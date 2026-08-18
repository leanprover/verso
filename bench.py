#!/usr/bin/env python
# This script is invoked by Radar infrastructure
# to measure the build time of projects downstream of Verso.

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

output_path: Path
root: str
cmdargs: list[str]

VERSO_LEAN_TOOLCHAIN_MAGIC = "VERSO_LEAN_TOOLCHAIN"

INTERACTIVE_BENCH_PATH = Path(__file__).resolve().parent / "InteractiveBench.lean"
HEADER_END_PATH = Path(__file__).resolve().parent / "HeaderEnd.lean"

# Command inserted to trigger re-elaboration
DUMMY_COMMAND = '#check "radar_interactive_edit"'

def append_result(
    metric: str,
    submetric: str,
    value: str | float | int,
    unit=None,
    more_is_better: bool = False,
) -> None:
    global output_path
    global root
    val = str(value)

    # Infer units a little bit
    if unit is None:
        match_val = re.match(r"([0-9.]+)ms", val)
        if match_val:
            val = str(float(match_val[1]) / 1000)
            unit = "s"

    if unit is None:
        # Supported: s for sec, B for bytes
        match_val = re.match(r"([0-9.]+)([%a-zA-Z]+)", val)
        if match_val:
            val = match_val[1]
            unit = match_val[2]

    print(f"{metric} // {submetric} -> {val}{f'({unit})' if unit else ''}")
    with open(output_path, "a") as f:
        f.write(
            json.dumps(
                {
                    "metric": f"{root}/{metric}//{submetric}",
                    "value": val,
                    "unit": unit,
                    "direction": 1 if more_is_better else -1,
                }
            )
            + "\n"
        )


def walk_ir_dir(project_directory: Path):
    total_c = 0
    ir_dir = Path.cwd() / project_directory / ".lake" / "build" / "ir"
    for dir_, _, files in os.walk(ir_dir):
        module_base = list(Path(dir_).relative_to(ir_dir).parts)
        for file in files:
            if file.endswith(".c"):
                module = ".".join(module_base + [file[:-2]])
                size = os.path.getsize(Path(dir_) / file)
                total_c += size
                append_result(f"build/{module}", "generated C", size, "B")
    append_result("build/.total", "generated C", total_c, "B")


def walk_lib_dir(project_directory: Path):
    total_olean = 0
    lib_dir = Path.cwd() / project_directory / ".lake" / "build" / "lib" / "lean"
    for dir_, _, files in os.walk(lib_dir):
        module_base = list(Path(dir_).relative_to(lib_dir).parts)
        for file in files:
            if file.endswith(".olean"):
                module = ".".join(module_base + [file[:-6]])
                size = os.path.getsize(Path(dir_) / file)
                total_olean += size
                append_result(f"build/{module}", "generated olean", size, "B")
    append_result("build/.total", "generated olean", total_olean, "B")

def repo_has_rev(repo_url: str, rev: str) -> bool:
    proc = subprocess.run(
        ["git", "ls-remote", "--exit-code", repo_url, f"refs/tags/{rev}", f"refs/heads/{rev}"],
        capture_output=True,
        text=True,
        timeout=30,
        # Fail instead of asking for credentials
        env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
    )
    if proc.returncode == 0:
        return True
    if proc.returncode == 2:
        return False
    raise RuntimeError(
        f"git ls-remote failed (code {proc.returncode}): {proc.stderr.strip()}"
    )

def checkout_project(
    verso_directory: Path,
    gitUrl: str,
    project_directory: Path,
    useO0: bool,
    branch: str,
) -> tuple[bool, bool]:
    """
    Checkout a suitably structured Verso project in an indicated directory.
    The project is rewritten to use the toolchain (& corresponding packages)
    for the Verso version being benchmarked.
    """

    try:
        with open(verso_directory / "lean-toolchain") as f:
            versos_lean_toolchain = f.read().strip()
            if not versos_lean_toolchain.startswith("leanprover/lean4:"):
                raise Exception(
                    f"lean toolchain for verso isn't a lean4 version: {versos_lean_toolchain}"
                )
            verso_lean_version = versos_lean_toolchain[17:]

        if branch == VERSO_LEAN_TOOLCHAIN_MAGIC:
            branch = verso_lean_version
        subprocess.run(
            [
                "git",
                "clone",
                "--depth=1",
                gitUrl,
                f"--branch={branch}",
                project_directory,
            ],
            capture_output=True,
            check=True,
        )

        # Before we replace the project's lean toolchain, read it so
        # we can use it to rewrite the lakefile
        with open(Path.cwd() / project_directory / "lean-toolchain") as f:
            project_lean_toolchain = f.read().strip()
            if not project_lean_toolchain.startswith("leanprover/lean4:"):
                raise Exception(
                    f"lean toolchain for project isn't a lean4 version: {project_lean_toolchain}"
                )
            project_lean_version = project_lean_toolchain[17:]
        with open(Path.cwd() / project_directory / "lean-toolchain", "w") as f:
            f.write(versos_lean_toolchain)

        lakefile: Path = Path.cwd() / project_directory / "lakefile.lean"
        needs_mathlib_cache_get = False
        with open(lakefile) as f:
            lines = f.readlines()
            required_verso = False
            for index, line in enumerate(lines):
                if re.match(r"^require verso from ", line):
                    lines[index] = f'require verso from "{verso_directory}"\n'
                    required_verso = True
                elif re.match(r"^require mathlib from ", line) and "nightly" in verso_lean_version:
                    # Mathlib nightly-testing-* tags live in a different repository - switch to that one.
                    # Remark: Verso and mathlib/nightly-testing-* must be on the same toolchain
                    # for mathlib's cache to successfully download.
                    nightly_repo = "https://github.com/leanprover-community/mathlib4-nightly-testing.git"
                    nightly_tag = verso_lean_version.replace("nightly", "nightly-testing")
                    if repo_has_rev(nightly_repo, nightly_tag):
                        lines[index] = f'require mathlib from git "{nightly_repo}" @ "{nightly_tag}"\n'
                    else:
                        # Use the general tag on a best-effort basis
                        print(f"WARNING: Using mathlib @ nightly-testing instead of mathlib @ {nightly_tag}", file=sys.stderr)
                        lines[index] = f'require mathlib from git "{nightly_repo}" @ "nightly-testing"\n'
                elif re.match(r"^require VersoBlueprint from ", line):
                    # VersoBlueprint only publishes v4.N.0 branches.
                    verso_lean_trunc = re.sub(r'\d+(-rc\d+)?$', '0', verso_lean_version)
                    vbp_repo = "https://github.com/leanprover/verso-blueprint.git"
                    if repo_has_rev(vbp_repo, verso_lean_trunc):
                        lines[index] = f'require VersoBlueprint from git "{vbp_repo}" @ "{verso_lean_trunc}"\n'
                    else:
                        print(f"WARNING: Using '{line.strip()}' instead of VersoBlueprint @ {verso_lean_trunc}", file=sys.stderr)
                elif re.match(r"^package", line) and useO0:
                    lines[index] = line + '  moreLeancArgs := #["-O0"]\n'
                else:
                    lines[index] = line.replace(
                        f'"{project_lean_version}"', f'"{verso_lean_version}"'
                    )
                if re.match(r"^require mathlib from ", line):
                    # `lake update` sometimes doesn't fetch mathlib cache (e.g. on nightly branches)
                    needs_mathlib_cache_get = True
            if not required_verso:
                raise Exception("lakefile.lean has no 'require verso', cannot point at benchmark commit")
        with open(lakefile, "w") as f:
            f.write("".join(lines))
        append_result("checkout", "success", 1, more_is_better=True)
        return (True, needs_mathlib_cache_get)
    except Exception as e:
        print(e, file=sys.stderr)
        append_result("checkout", "success", 0, more_is_better=True)
        return (False, False)


def project_install_deps(project_directory: Path, needs_mathlib_cache_get: bool) -> bool:
    try:
        subprocess.run(
            ["lake", "update", "--no-ansi", "--keep-toolchain"],
            cwd=project_directory,
            check=True,
        )
        if needs_mathlib_cache_get:
            subprocess.run(
                ["lake", "exe", "cache", "get"],
                cwd=project_directory,
                check=True,
            )
        return True
    except Exception as e:
        print(e, file=sys.stderr)
        return False

def project_build_targets(project_directory: Path, targets: list[str] = []) -> tuple[float, bytes] | None:
    try:
        start: float = time.time()
        result = subprocess.run(
            ["lake", "build", "--no-ansi", "--keep-toolchain"] + targets,
            cwd=project_directory,
            capture_output=True,
        )
        end: float = time.time()
        print(result.stderr.decode("utf-8"), file=sys.stderr)
        if result.returncode:
            # check_returncode will raise and return None,
            # so print stdout now.
            print(result.stdout.decode("utf-8"))
        result.check_returncode()
        return (end - start, result.stdout)
    except Exception as e:
        print(e, file=sys.stderr)
        return None


def project_measure_exe(project_directory: Path, main_module: str) -> tuple[float, int] | None:
    try:
        start: float = time.time()
        subprocess.run(
            ["lake", "lean", f"{main_module}.lean", "--", "--run", f"{main_module}.lean"] + cmdargs,
            cwd=project_directory,
            check=True,
        )
        end: float = time.time()
        return (end - start, 0)
    except Exception as e:
        print(e, file=sys.stderr)
        return None


def project_measure_reelab(project_directory: Path, file_name: Path, edit_pos: tuple[int, int]) -> float | None:
    try:
        result = subprocess.run(
            ["lean", "--run", str(INTERACTIVE_BENCH_PATH), str(file_name), DUMMY_COMMAND, str(edit_pos[0]), str(edit_pos[1])],
            # Use the project's Lean toolchain
            cwd=project_directory,
            stdout=subprocess.PIPE,
            text=True,
            check=True,
        )
        timings = dict(re.findall(
            r"^([a-z- ]+)=([0-9]+)$",
            result.stdout,
            re.MULTILINE,
        ))
        return int(timings["re-elab time"]) / 1000
    except Exception as e:
        print(e, file=sys.stderr)
        return None


def header_end_pos(project_directory: Path, file: Path) -> tuple[int, int]:
    """Position (0-based) of the first token after the header of `file`."""
    result = subprocess.run(
        ["lean", "--run", str(HEADER_END_PATH), str(file)],
        # Use the project's Lean toolchain
        cwd=project_directory,
        stdout=subprocess.PIPE,
        text=True,
        check=True,
    )
    [line, col] = result.stdout.strip().split(':')
    return (int(line) - 1, int(col))


def parse_time(time: str):
    time = time.strip()
    match_val = re.match(r"([0-9.]+)ms$", time)
    if match_val:
        return float(match_val[1]) / 1000
    match_val = re.match(r"([0-9.]+)s$", time)
    if match_val:
        return float(match_val[1])
    raise Exception(f"Cannot parse time: {time}")


total_key_time: dict[str, float] = {}
subtotals_key_time: dict[str, dict[str, float]] = {}


def process_output(prefix: str, output: str):
    global total_key_time
    global subtotals_key_time

    totals: dict[str, float] = {}

    for line in output.split("\n"):
        match_val_eval_metric = re.match(
            r"^. \[([0-9]+)/([0-9]+)\] Built ([A-Za-z0-9.\-/_«»]+) \(([A-Za-z0-9.]+)\)$",
            line,
        )
        match_val_other_metric = re.match(
            r"^. \[([0-9]+)/([0-9]+)\] Built ([A-Za-z0-9.\-/_«»]+):([A-Za-z0-9.\-/_«»]+) \(([A-Za-z0-9.]+)\)$",
            line,
        )

        if match_val_eval_metric:
            metric: str = "eval"
            time_data: float = parse_time(match_val_eval_metric[4])
            module_name = match_val_eval_metric[3]
            top_level_module: str = match_val_eval_metric[3].split(".")[0]
        elif match_val_other_metric:
            metric = match_val_other_metric[4]
            time_data = parse_time(match_val_other_metric[5])
            module_name = match_val_other_metric[3]
            top_level_module = match_val_other_metric[3].split(".")[0]
        elif re.match(r"[^]]*\]\s*Built", line):
            print(f"MISSED?: {line}", file=sys.stderr)
            continue
        else:
            print(line)
            continue

        append_result(f"{prefix}/{module_name}", f"{metric} time", time_data, "s")
        print(line)

        # Update total
        prev_total = totals.get(metric, 0.0)
        totals[metric] = prev_total + time_data

        # Update per-package subtotal
        if top_level_module not in subtotals_key_time:
            subtotals_key_time[top_level_module] = {}
        prev_subtotal = subtotals_key_time[top_level_module].get(metric, 0.0)
        subtotals_key_time[top_level_module][metric] = prev_subtotal + time_data

    for key, total in totals.items():
        if key not in total_key_time:
            total_key_time[key] = 0
        total_key_time[key] += total
        append_result(f"{prefix}/.total", f"{key} time", total, "s")


def main() -> None:
    global output_path
    global root
    global total_key_time
    global subtotals_key_time
    global cmdargs

    parser = argparse.ArgumentParser(
        description="Collect timing and output size data from building a Verso project and generating its artifacts. "
          "Output in Radar format.",
        allow_abbrev=False,
    )

    parser.add_argument(
        "output_path",
        type=Path,
        help="file the measurements should be appended to (created if missing)",
    )
    parser.add_argument("-r", "--metrics-root", type=str, help="first component of reported Radar metric names", required=True)
    parser.add_argument("-e", "--exe-name", type=str, help="name of the Verso doc generator lean_exe", required=True)
    # parser.add_argument("-f", "--edit-file", type=Path, help="measure CLI re-build and LSP re-elab times after editing this file", required=True)
    parser.add_argument("--exe-arg", action="append", help="additional argument to pass to the doc generator (use --exe-arg=--foo syntax)", default=[])
    parser.add_argument("--opt", type=str, help="optimization level for native compilation (must be o0 if provided)")
    parser.add_argument("--project-url", type=str, help="Git URL of the project to benchmark")
    parser.add_argument("--project-branch", type=str, help=f"branch/tag of the project to clone; the special value {VERSO_LEAN_TOOLCHAIN_MAGIC} uses Verso's toolchain (e.g. v4.33.0) as the tag")
    parser.add_argument("--project-dir", type=Path, help="directory to clone the project into (or to read the project from with --skip-checkout)", default="project")
    parser.add_argument("--skip-checkout", action="store_true", help="do not clone the project, assuming it is already in --project-dir")
    parser.add_argument("--verso-dir", type=Path, help="Verso checkout directory")
    parser.add_argument("--pre-build-cmd", type=str, help="additional command to run in the project directory after `lake update`, before `lake build`; its time is not measured")

    args, unknown_args = parser.parse_known_args()
    if unknown_args:
        print(f"warning: ignoring unrecognized arguments: {unknown_args}", file=sys.stderr)

    output_path = args.output_path
    # (Only non-globals can be type-annotated here)
    directory: Path = args.project_dir.resolve()
    root = args.metrics_root
    #binary: str = args.exe_name
    cmdargs = args.exe_arg
    if args.verso_dir is not None:
        verso_directory: Path = args.verso_dir
    else:
        verso_directory: Path = Path(__file__).resolve().parent

    if args.opt == "o0":
        use_o0_optimization = True
    elif args.opt is not None:
        print(f"unexpected opt level {args.opt}", file=sys.stderr)
        sys.exit(1)
    else:
        use_o0_optimization = False

    # if not str(args.edit_file).endswith('.lean'):
    #     print(f"--edit-file must end with .lean (got '{args.edit_file}')", file=sys.stderr)
    #     sys.exit(1)
    # else:
    #     # Hack: compute Lean module name assuming project_directory is the Lake srcDir
    #     mod_name = str(args.edit_file[:-5].replace('/', '.'))
    #     # Relativize to project directory
    #     args.edit_file = directory / args.edit_file

    if str(args.project_dir) == "lean4-cs1":
        main_module = "Main"
        targets = []
        edit_file = Path("FPCourse/Unit1/Week00_AlgebraicTypes.lean")
    elif str(args.project_dir) == "sherlock":
        main_module = "SherlockMain"
        targets = []
        edit_file = Path("Sherlock/Study001.lean")
    elif str(args.project_dir) == "refman":
        main_module = "Main"
        # The default targets *except* doc-generating `lean_exe`s (generate-manual and generate-tutorials)
        targets = ["IndexMap", "IndexMapGrind", "Manual", "@/subversoExtractMod", "@/extract-lakefile", "Main", "Tutorial", "TutorialMain"]
        edit_file = Path("Manual/Tactics.lean")
    elif str(args.project_dir) == "verso-natson":
        main_module = "BlueprintMain"
        targets = []
        edit_file = Path("CarlesonBlueprint/Chapters/Main.lean")
    else:
        # # Hack: compute Lean module name assuming project_directory is the Lake srcDir
        # mod_name = str(args.edit_file)[:-5].replace('/', '.')
        # # Relativize to project directory
        # args.edit_file = directory / args.edit_file
        raise Exception("unknown package")

    mod_name = str(edit_file)[:-5].replace('/', '.')
    edit_file = directory / edit_file

    if not args.skip_checkout:
        if args.project_url is None:
            print(f"--project-url must be provided when not using --skip-checkout", file=sys.stderr)
            sys.exit(1)
        if args.project_branch is None:
            print(f"--project-branch must be provided when not using --skip-checkout", file=sys.stderr)
            sys.exit(1)

        [did_checkout, needs_mathlib_cache_get] = checkout_project(
            verso_directory=verso_directory,
            gitUrl=args.project_url,
            branch=args.project_branch,
            useO0=use_o0_optimization,
            project_directory=directory,
        )
    else:
        did_checkout = True
        needs_mathlib_cache_get = False

    if not did_checkout:
        print("checkout did not succeed")
        sys.exit(1)

    # Clean in case the script had already run on a different downstream project
    # and constructed `.lake` in the Verso directory.
    subprocess.run(
        ["lake", "clean", "--no-ansi", "--keep-toolchain"],
        cwd=verso_directory,
        check=True,
    )

    did_install = project_install_deps(directory, needs_mathlib_cache_get)
    if not did_install:
        print("installing dependencies did not succeed")
        sys.exit(1)

    if not args.pre_build_cmd is None:
        subprocess.run([args.pre_build_cmd], cwd=directory, check=True)

    default_res = project_build_targets(directory, targets)
    if default_res is None:
        print("default build step did not succeed")
        append_result("build/default", "success", 0, more_is_better=True)
        sys.exit(1)
    else:
        (dt, stdout) = default_res
        append_result("build/default/.total", "wall clock time", dt, "s")
        process_output("build/default", stdout.decode("utf-8"))
        append_result("build/default", "success", 1, more_is_better=True)

    # Retained for continuity with old metrics
    append_result("build/exe/.total", "wall clock time", 0, "s")
    append_result("build/exe", "generated exe", 0, "B")
    append_result("build/exe", "success", 1, more_is_better=True)

    walk_ir_dir(directory)
    walk_lib_dir(directory)

    for key, total in total_key_time.items():
        append_result("build/.total", f"{key} time", total, "s")
    for top_level_package, kv in subtotals_key_time.items():
        for key, total in kv.items():
            append_result(
                f"build/{top_level_package}/.total", f"{key} time", total, "s"
            )

    run_res = project_measure_exe(directory, main_module)
    if run_res is None:
        print("exe measure step did not succeed")
        append_result("build/html", "success", 0, more_is_better=True)
        sys.exit(1)
    else:
        (dt, _) = run_res
        append_result("build/html/.total", "wall clock time", dt, "s")
        append_result("build/html", "success", 1, more_is_better=True)
        append_result("build/.total", "wall clock time", default_res[0] + dt, "s")

    (line, col) = header_end_pos(directory, edit_file)

    with open(edit_file, 'r', encoding="utf-8") as f:
        lines = f.read().split("\n")
    if col == 0:
        lines.insert(line, DUMMY_COMMAND)
    else:
        # When header ends in the middle of a line,
        # split the remainder out into its own line
        l = lines[line]
        lines[line] = l[:col]
        lines.insert(line+1, l[col:])
        lines.insert(line+1, DUMMY_COMMAND)

    with open(edit_file, 'w', encoding="utf-8") as f:
        f.write('\n'.join(lines))

    append_result("rebuild/exe/.total", "wall clock time", 0, "s")
    append_result("rebuild/exe", "success", 1, more_is_better=True)

    run_res = project_measure_exe(directory, main_module)
    if run_res is None:
        print("rebuilt exe measure step did not succeed")
        append_result("rebuild/html", "success", 0, more_is_better=True)
        sys.exit(1)
    else:
        (dt, _) = run_res
        append_result("rebuild/html/.total", "wall clock time", dt, "s")
        append_result("rebuild/html", "success", 1, more_is_better=True)
        append_result("rebuild/.total", "wall clock time", dt, "s")

    reelab_dt = project_measure_reelab(directory, edit_file, (line, col))
    if reelab_dt is None:
        print("LSP re-elaboration step did not succeed")
        append_result(f"lsp-elab/{mod_name}", "success", 0, more_is_better=True)
        sys.exit(1)
    else:
        append_result(f"lsp-elab/{mod_name}", "wall clock time", reelab_dt, "s")
        append_result(f"lsp-elab/{mod_name}", "success", 1, more_is_better=True)

if __name__ == "__main__":
    main()
