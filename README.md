# Through-focal inversion of LEEM Fourier optics

We invert a through-focal LEEM intensity series for the object exit
wave $`\psi_0=\sigma\mathrm{e}^{\mathrm{i}\phi}`$ using the Fourier-optics
(FO) kernel of

> K. M. Yu, K. L. W. Lau, M. S. Altman,
> *Fourier optics of image formation in aberration-corrected LEEM*,
> Ultramicroscopy **200** (2019) 160–168.

The forward kernel is first encoded in Lean 4 and its appendix
identities are proved; the discrete inverse is then stated and
machine-checked against that same kernel. The project does **not**
prove experimental claims or simulation runtimes.

## 1. Forward model

We encode the wave aberration $`\chi`$ (in waves,
$`W=\mathrm{e}^{2\pi\mathrm{i}\chi}`$), the coherent kernel $`R_0`$, the
spatial and chromatic envelopes $`E_S`$ and $`E_{C,\mathrm{tot}}`$, the
identity that the contrast-transfer function is the slice
$`R_{\mathrm{FO}}(\mathbf{q},0)=R_{\mathrm{CTF}}`$, and the Jacobi–Anger
expansion of a sinusoidal phase object.

Equation-by-equation mapping:
[docs/FORMALIZATION.md](docs/FORMALIZATION.md).

Closed-form envelopes of the FO kernel (journal-style note):
[docs/proofs/leemfo_proofs.pdf](docs/proofs/leemfo_proofs.pdf)
([source](docs/proofs/leemfo_proofs.tex)).

## 2. Inverse

Given a 2D through-focal stack we recover $`\psi_0`$ in two stages:
regularized multi-defocus inversion on the CTF slice (Schiske/Wiener),
which fills CTF zeros; optional Gauss–Newton iteration on the full
bilinear FO residual for strong-phase objects; Jacobi–Anger fitting
for the 1D sinusoid of Yu *et al.* The bilinear inverse is encoded
analytically as a Gram lift plus vacuum-gauge factor: each
difference-frequency slice is linear in $`X(q,q-\xi)`$, the vacuum
$`2\times 2`$ inverts the DC column once the off-axis remainder is known
or vanishes (1–3 Fourier modes, two-axis 3-wave objects), an equally
spaced pure-defocus series inverts iso-$`\omega`$ fiber masses by a
Vandermonde system, and a radial pure-defocus 2D kernel cannot
separate frequencies with the same projection onto $`\xi`$.
Selected algebraic claims (unique Tikhonov minimizer, remainder-corrected
Cramer formula, small-mode identities, fiber masses, 2D degeneracy) are machine-checked
in Lean 4. This is **not** an unconditional inverse of the Yu kernel on
an unrestricted 2D lattice.

Inverse note:
[docs/proofs/leemfo_inverse.pdf](docs/proofs/leemfo_inverse.pdf)
([source](docs/proofs/leemfo_inverse.tex)).

Analytic bilinear inverse (Gram lift, small-mode and two-axis
objects, Vandermonde fiber masses), as a sequence of identities:
[docs/proofs/leemfo_analytic_inverse.pdf](docs/proofs/leemfo_analytic_inverse.pdf)
([source](docs/proofs/leemfo_analytic_inverse.tex)).

Theorem list:
[docs/LINEAR_INVERSE.md](docs/LINEAR_INVERSE.md).

## Build

Lean development requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get   # download Mathlib oleans
lake build
```

To rebuild the PDFs (TeX Live with `latexmk`):

```bash
cd docs/proofs
latexmk -pdf leemfo_proofs.tex
latexmk -pdf leemfo_inverse.tex
latexmk -pdf leemfo_analytic_inverse.tex
```

## Layout

Forward proofs live in `LeemFO/Forward/`; inverse proofs live in `LeemFO/Inverse/`.
`LeemFO/Forward.lean` and `LeemFO/Inverse.lean` re-export each directory.

### Forward

| File | Content |
|---|---|
| `LeemFO/Forward/Basic.lean` | $`\chi_S,\chi_C,M,W_S,W_C,R_0`$, nac/ac (`lam` is paper $`\lambda`$) |
| `LeemFO/Forward/Gaussian.lean` | FWHM and Gaussian characteristic functions |
| `LeemFO/Forward/Aberration.lean` | $`\nabla\chi_S`$ and first-order Taylor in tilt $`k`$ |
| `LeemFO/Forward/EnvelopeSpatial.lean` | Appendix A1: $`E_S`$ |
| `LeemFO/Forward/EnvelopeChromatic.lean` | Appendix A1: $`E_{C,\mathrm{tot}}`$ and polar form |
| `LeemFO/Forward/CTF.lean` | $`q'=0`$ recovery and hermiticity |
| `LeemFO/Forward/Kernel2.lean` | 2D working kernel $`R_{\mathrm{FO2}}`$: disk aperture, $`\mathbf{q}\cdot\mathbf{q}'`$ in $`E_S`$, pure-defocus cisoid |
| `LeemFO/Forward/Ratios.lean` | $`\Gamma_C,\Gamma_S`$ |
| `LeemFO/Forward/PhaseObject.lean` | Jacobi–Anger for $`\mathrm{e}^{\mathrm{i}\varphi\sin\theta}`$ |

### Inverse

| File | Content |
|---|---|
| `LeemFO/Inverse/Modes.lean` | Aperture mode count $`M=2\lfloor q_{\mathrm{ap}}\Lambda\rfloor+1`$, `rFO` sampling, `sinusoidJ` |
| `LeemFO/Inverse/Tikhonov.lean` | Fourier-bin Tikhonov: unique min, bias–noise identity, $`2\times 2`$ closed form, $`O(KN\log N)`$ cost model |
| `LeemFO/Inverse/LinearInverse.lean` | Aperture support of $`R_{\mathrm{FO}}(\cdot,0)`$, gauge, vacuum Jacobian remainder, $`K\ge 2`$ |
| `LeemFO/Inverse/Pipeline.lean` | Stage-1 map `stage1Scalar`/`stage1Pair`, vacuum GN glue, algebraic `stage2Skip` |
| `LeemFO/Inverse/Gram.lean` | Rank-1 Gram lift of bilinear FO, vacuum-gauge factor, remainder-corrected 2×2 |
| `LeemFO/Inverse/SmallMode.lean` | Closed-form inverse on 1/2/3 Fourier modes and two-axis 3-wave objects |
| `LeemFO/Inverse/Degeneracy.lean` | Householder reflection; pure-defocus 2D kernel depends on $`\mathbf{q}`$ only through $`\mathbf{q}\cdot\boldsymbol{\xi}`$ |
| `LeemFO/Inverse/Analytic.lean` | Analytic reconstruction map, uniqueness, sampled 2D Yu kernel on a finite group |
| `LeemFO/Inverse/Fiber.lean` | Vandermonde inverse of iso-$`\omega`$ fiber masses; Gram recovery on transversal support (Householder partners stay glued) |
