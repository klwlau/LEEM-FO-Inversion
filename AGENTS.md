# AGENTS.md

## Cursor Cloud specific instructions

This is a **Lean 4 + Mathlib formalization project** (see `README.md`). There is no
runtime app or server: the "application" is the machine-checked proof library, so
`lake build` acts as both the build and the test — it type-checks every proof in
`LeemFO/`. A successful build means all theorems are verified.

Non-obvious caveats for future agents:

- The Lean toolchain (`elan`, `lake`, `lean`) is installed via the environment and
  symlinked into `/usr/local/bin`, so it is on `PATH` in every shell. The version is
  pinned by `lean-toolchain` (currently `leanprover/lean4:v4.33.1`) and auto-selected
  by `lake`.
- Run `lake exe cache get` before `lake build` on a fresh checkout. This downloads
  prebuilt Mathlib oleans. Without it, `lake build` would compile all of Mathlib from
  source, which is prohibitively slow. This command is already the environment update
  script, so it normally runs automatically on startup.
- Build/verify all proofs: `lake build` (fast, ~20s, since Mathlib is cached).
- **Linting** runs automatically during `lake build` via the Mathlib standard linter
  set (`weak.linter.mathlibStandardSet = true` in `lakefile.toml`); there is no
  separate lint command.
- There is **no test driver**: `lake test` intentionally reports
  `no test driver configured`. Proof checking via `lake build` is the test suite.
- To confirm a specific theorem is genuinely proven (no hidden `sorry`), run a scratch
  file with `lake env lean <file>` using `#print axioms <thm>`; a complete proof lists
  only `[propext, Classical.choice, Quot.sound]` and never `sorryAx`.
- Markdown math: inline `$...$`; display as a fenced `math` code block (GitHub GFM).
  Do not use TeX delimiters `\(...\)` / `\[...\]` — those render as literal text.
