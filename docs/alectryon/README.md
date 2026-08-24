# Alectryon proofs PDF

Literate Lean 4 note that typesets the machine-checked FO envelope
proofs with [Alectryon](https://github.com/cpitclaudel/alectryon).

| Artifact | Role |
|---|---|
| [`LeemFOProofs.lean`](LeemFOProofs.lean) | Source: Lean code + reST prose in `/-|` … `|-/` |
| [`leemfo_alectryon.pdf`](leemfo_alectryon.pdf) | Generated PDF (tracked) |
| [`docutils.conf`](docutils.conf) | Geometry, fonts, PDF metadata |
| [`pyproject.toml`](pyproject.toml) / [`requirements.txt`](requirements.txt) | `alectryon` pin for `uv` |

This is complementary to the handwritten analytic note
[`docs/proofs/leemfo_proofs.pdf`](../proofs/leemfo_proofs.pdf): that
document is traditional mathematics; this one is the Lean scripts.

## Rebuild

Needs [uv](https://docs.astral.sh/uv/), Python ≥ 3.10, and TeX Live
with LuaLaTeX (`texlive-luatex`, `texlive-latex-extra`, `tcolorbox`).

```bash
make -C docs/alectryon pdf
```

That creates `.venv` at the repository root, runs Alectryon
(`lean4+rst` → LuaLaTeX), and compiles `leemfo_alectryon.pdf`.

To typecheck the literate file against the library:

```bash
lake build LeemFOProofs
```

## LeanInk (optional)

Alectryon’s Lean 4 driver is [LeanInk](https://github.com/leanprover/LeanInk).
Upstream LeanInk is archived on Lean **4.6** and does not build against
this project’s **4.33.1** toolchain, so the Makefile defaults to
`--lean4-driver noop` (syntax-highlighted scripts, no Infoview goals).

If you have a LeanInk binary matching 4.33:

```bash
make -C docs/alectryon DRIVER=leanInk pdf
```
