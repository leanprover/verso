# Project Notes

- See worktree layout section for more information
- When asked to do a task, assume it is a new branch and worktree from main, unless instructed otherwise
- Main validation command: `lake build` and `lake test`

## Worktree Layout (Parallel Features + Sub-Agents)

- Keep the main checkout at:
  - `/home/egallego/lean/verso` (branch `main`)
- Put feature worktrees under:
  - `/home/egallego/lean/verso/.worktrees/<feature>`
- This keeps all worktrees under the same writable root, so Codex sub-agents can edit without sandbox path issues.

## VS Code + Path References

- Open VS Code in the worktree you are actively editing (for example `/home/egallego/lean/verso/.worktrees/doc-html-preview`), not only in the main checkout.
- Treat the active worktree directory as the project root for commands, searches, and file links.
- When an agent is running from the main checkout but referring to a feature worktree file, include the worktree prefix in paths (for example `.worktrees/doc-html-preview/src/tests/Tests/DocPreview/Log.lean`).
- When an agent is already running inside a feature worktree, use paths relative to that worktree root (for example `src/tests/Tests/DocPreview/Log.lean`).
- In agent/user messages, prefer explicit paths that include `.worktrees/<feature>/...` whenever there is any ambiguity.

### Create feature worktrees

- Example commands:
  - `git worktree add .worktrees/feature-search -b feat/feature-search origin/main`
  - `git worktree add .worktrees/feature-graph -b feat/feature-graph origin/main`

### Sub-agent rule

- Run each sub-agent from the feature worktree it owns (its CWD must be that worktree path).
- Do not run multiple sub-agents in the same worktree simultaneously.
- Keep shared fixes in a separate worktree/branch and merge/cherry-pick as needed.
