# AGENTS.md

## Cursor Cloud specific instructions

This repository is a **Lean 4 + Mathlib formalization** (Fourier optics of LEEM image
formation and its inverse). There is no runtime application, server, or service to
start: the "application" is the proof checker, and success means `lake build`
machine-checks every proof.

### Toolchain
- Lean/Lake are managed by `elan`, installed under `~/.elan` (on `PATH` via `~/.profile`).
- The Lean version is pinned by `lean-toolchain` (`leanprover/lean4:v4.33.1`); `elan`
  installs it automatically the first time `lake` runs in the repo.
- If `lake` is not found in a non-login shell, use the full path `~/.elan/bin/lake`
  (only `~/.profile`, not `~/.bashrc`, has the `PATH` entry).

### Build / lint / test (all are the same step here)
- `lake exe cache get` — download prebuilt Mathlib `.olean`s. The startup update script
  already runs this. **Always run it before building**; skipping it forces a from-source
  Mathlib compile that takes hours instead of seconds.
- `lake build` — machine-checks the `LeemFO/Forward/*` and `LeemFO/Inverse/*` modules (~20s with a warm cache). This
  is simultaneously the build, the test, and the lint (Mathlib linters run via
  `weak.linter.mathlibStandardSet` in `lakefile.toml`).
- There is no separate unit-test suite. To confirm proofs are genuine, scan for
  `sorry`/`admit` and inspect axioms of key theorems, e.g.:
  `lake env lean` on a file with `#print axioms tikhonov_unique` — sound proofs depend
  only on `[propext, Classical.choice, Quot.sound]`.

### Docs / PDFs
- Rebuilding the PDFs in `docs/proofs/` needs TeX Live with `latexmk` (not installed by
  default and not required for proof checking). See `README.md` for those commands.
- GitHub Markdown math: inline formulas use dollar-backtick delimiters so `_`
  is not parsed as emphasis, e.g. `` $`E_{C,\mathrm{tot}}`$ ``. Display formulas
  use fenced `math` blocks. Do not wrap LaTeX in ordinary backticks (that shows
  the source). Keep Lean identifiers in backticks. In math, write absolute values
  as `\lvert...\rvert` so GFM tables do not split on `|`.
