"""
The widget's reducer, checked against orders of events that the server and the InfoView make rare:
output that arrives before the run is started, a result that reports its finish before its start, an
outcome that arrives twice, and a cancel after the run is done. Each check folds random sequences of
events through the reducer that the widget's module puts on the page, from a fixed seed, and checks
every state that the fold passes through.
"""

import random

import pytest

pytestmark = pytest.mark.errata_widget

# How many random sequences each check folds, and how long each is.
SEQUENCES = 200
LENGTH = 30

FOLD = """(events) => {
    const reducer = window.errataWidgetReducer;
    let st = reducer.idleState;
    const states = [];
    for (const ev of events) {
        st = reducer.step(st, ev);
        states.push(JSON.parse(JSON.stringify(st)));
    }
    return states;
}"""


@pytest.fixture
def fold(editor):
    """Folds a sequence of events through the widget's reducer, returning each state in turn."""
    editor.show("Passing", "bothStreams")
    editor.page.wait_for_function("window.errataWidgetReducer !== undefined")
    return lambda events: editor.page.evaluate(FOLD, events)


class Server:
    """
    A run as the server reports it: chunks `c0`, `c1`, … and named results that start and finish,
    with replies that begin at any earlier position, as a reconnecting widget's do.
    """

    def __init__(self, rng, run_id):
        self.rng = rng
        self.run_id = run_id
        self.chunks = []
        self.reports = []
        self.outcome = None

    def advance(self):
        """Adds a chunk or a report from a named result, which may finish before it starts."""
        if self.rng.random() < 0.6:
            self.chunks.append({"stream": "stdout", "text": f"c{len(self.chunks)}"})
        else:
            rid = self.rng.randint(1, 3)
            status = self.rng.choice([None, "pass", "fail"])
            report = {"id": rid, "parent": 0, "name": f"r{rid}"}
            if status:
                report["status"] = status
            self.reports.append(report)

    def reply(self, done=False):
        since = self.rng.randint(0, len(self.chunks))
        since_results = self.rng.randint(0, len(self.reports))
        res = {
            "runId": self.run_id,
            "startTime": 1000,
            "elapsedMs": 5,
            "phase": "done" if done else "running",
            "chunks": self.chunks[since:],
            "nextSince": len(self.chunks),
            "results": self.reports[since_results:],
            "nextSinceResults": len(self.reports),
            "done": done,
        }
        if done:
            self.outcome = self.outcome or {"status": "pass", "ran": True, "settings": []}
            res["outcome"] = self.outcome
        return {"type": "server", "res": res, "now": 2000}


def random_events(rng):
    """A random sequence of the reducer's events about two runs of one test."""
    servers = [Server(rng, "A"), Server(rng, "B")]
    events = []
    for _ in range(LENGTH):
        server = rng.choice(servers)
        kind = rng.random()
        if kind < 0.1:
            events.append({"type": "start", "now": 1000, "runId": server.run_id})
        elif kind < 0.15:
            events.append({"type": "started"})
        elif kind < 0.25:
            events.append({"type": "cancel"})
        elif kind < 0.3:
            events.append({"type": "fail", "error": "refused"})
        elif kind < 0.4:
            events.append(server.reply(done=True))
        else:
            server.advance()
            events.append(server.reply())
    return events


def settled(state):
    return state["tag"] in ("done", "cancelled", "failed")


def sequences():
    rng = random.Random(20260925)
    return [random_events(rng) for _ in range(SEQUENCES)]


def test_output_is_placed_once_and_in_order_whatever_the_replies_replay(fold):
    for events in sequences():
        for state in fold(events):
            if state["tag"] == "idle":
                continue
            texts = [c["text"] for c in state["chunks"]]
            assert texts == [f"c{i}" for i in range(len(texts))], texts


def test_output_before_a_start_is_dropped_by_the_start(fold):
    for events in sequences():
        states = fold(events)
        for ev, state in zip(events, states):
            if ev["type"] == "start":
                assert state["tag"] == "running", state
                assert state["chunks"] == [] and state["results"] == [], state
                assert state["runId"] == ev["runId"], state


def test_a_finished_result_keeps_its_status_when_its_start_arrives_later(fold):
    rng = random.Random(7)
    for _ in range(SEQUENCES):
        finish = {"id": 1, "parent": 0, "name": "r", "status": rng.choice(["pass", "fail"])}
        start = {"id": 1, "parent": 0, "name": "r"}
        order = [finish, start] if rng.random() < 0.5 else [start, finish]
        events = [
            {
                "type": "server",
                "now": 2000,
                "res": {
                    "runId": "A",
                    "startTime": 1000,
                    "results": [report],
                    "nextSinceResults": i + 1,
                    "done": False,
                },
            }
            for i, report in enumerate(order)
        ]
        last = fold(events)[-1]
        assert last["results"][1]["status"] == finish["status"], last


def test_a_settled_run_stays_settled_until_another_run_is_reported(fold):
    for events in sequences():
        states = fold(events)
        for before, ev, after in zip(states, events[1:], states[1:]):
            if not settled(before):
                continue
            if ev["type"] == "cancel":
                assert after == before, (before, ev, after)
            if ev["type"] == "server" and ev["res"]["runId"] == before["runId"]:
                if not ev["res"]["done"]:
                    assert after == before, (before, ev, after)
                else:
                    assert settled(after), (before, ev, after)


def test_an_outcome_that_arrives_twice_leaves_the_run_done(fold):
    server = Server(random.Random(3), "A")
    server.advance()
    states = fold([server.reply(), server.reply(done=True), server.reply(done=True)])
    assert [s["tag"] for s in states] == ["running", "done", "done"], states
    assert states[1]["outcome"] == states[2]["outcome"]


def test_a_cancel_after_the_run_is_done_keeps_its_outcome(fold):
    server = Server(random.Random(4), "A")
    server.advance()
    states = fold([server.reply(done=True), {"type": "cancel"}])
    assert states[0]["tag"] == "done" and states[1] == states[0], states
