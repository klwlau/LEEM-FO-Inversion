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
which fills CTF zeros; then, for strong-phase objects, a mixed Born
homotopy that applies the bilinear remainder with a rank-`M` TCC /
coherent rank-1 autocorrelation (optionally LR+D) and solves the same
Fourier-diagonal $`2\times 2`$ system on the corrected residual, with
per-bin remainder skip and algebraic Armijo on the exact quartic line
energy. Rank policy: $`M=1`$ if perfectly coherent or if using the
line search, else $`M\le 8`$ at $`N=128`$. That mix is FO-faithful
(bilinear FO is exactly quadratic) and cheaper than a dense pair apply
at those ranks. The 1D sinusoid of Yu *et al.* remains Jacobi–Anger
fitting. Selected algebraic claims are machine-checked in Lean 4.

Inverse note:
[docs/proofs/leemfo_inverse.pdf](docs/proofs/leemfo_inverse.pdf)
([source](docs/proofs/leemfo_inverse.tex)).

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
| `LeemFO/Forward/Ratios.lean` | $`\Gamma_C,\Gamma_S`$ |
| `LeemFO/Forward/Kernel2.lean` | 2D kernel $`R_{\mathrm{FO}2}`$, disk aperture, $`\mathbf{q}\cdot\mathbf{q}'`$ in $`E_S`$ |
| `LeemFO/Forward/PhaseObject.lean` | Jacobi–Anger for $`\mathrm{e}^{\mathrm{i}\varphi\sin\theta}`$ |

### Inverse

| File | Content |
|---|---|
| `LeemFO/Inverse/Modes.lean` | Aperture mode count $`M=2\lfloor q_{\mathrm{ap}}\Lambda\rfloor+1`$, `rFO` sampling, `sinusoidJ` |
| `LeemFO/Inverse/Tikhonov.lean` | Fourier-bin Tikhonov: unique min, bias–noise identity, $`2\times 2`$ closed form, Kaczmarz reject, $`O(KN\log N)`$ cost model |
| `LeemFO/Inverse/LinearInverse.lean` | Aperture support of $`R_{\mathrm{FO}}(\cdot,0)`$, gauge, vacuum Jacobian remainder, $`K\ge 2`$ |
| `LeemFO/Inverse/Pipeline.lean` | Stage-1 map `stage1Scalar`/`stage1Pair`, vacuum GN glue, algebraic `stage2Skip` |
| `LeemFO/Inverse/LowRank.lean` | Rank-1 / TCC / LR+D apply, `recommendTccRank`, hybrid cost vs dense $`KN^2`$ |
| `LeemFO/Inverse/Homotopy.lean` | Exact quadratic homotopy, Born remainder correction, mixed spectrum iterate |
| `LeemFO/Inverse/LineSearch.lean` | Exact quartic line energy, algebraic Armijo, `nlsJ_line`, GN Hessian ≠ Newton |
| `LeemFO/Inverse/Plane2.lean` | 2D stage-1 map `stage1Pair2` on $`R_{\mathrm{FO}2}`$ |
| `LeemFO/Inverse/Mix.lean` | Mixed TCC–Born `mixed2DMix`; TIE / HIO / Rytov / Wiener / radial-1D / Kaczmarz witnesses |
