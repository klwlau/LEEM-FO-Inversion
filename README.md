# Lean proofs of ac-LEEM Fourier optics

Formalization of the extended Fourier Optics (FO) model in

> K. M. Yu, K. L. W. Lau, M. S. Altman,
> *Fourier optics of image formation in aberration-corrected LEEM*,
> Ultramicroscopy **200** (2019) 160–168.

This project encodes the proposed functions and proves the appendix
derivations (Gaussian integrals → envelopes, CTF as the \(q'=0\) slice,
perfect-coherence identities, Jacobi–Anger for the sinusoidal object).
It does **not** prove experimental claims or simulation runtimes.

Equation-by-equation mapping: [docs/FORMALIZATION.md](docs/FORMALIZATION.md).

Written proofs of the appendix identities (Gaussian envelopes, polar form,
FO/CTF ratios, Jacobi–Anger), compiled from LaTeX:
[docs/proofs/leemfo_proofs.pdf](docs/proofs/leemfo_proofs.pdf)
([source](docs/proofs/leemfo_proofs.tex)).

## Build

Lean development requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get   # download Mathlib oleans
lake build
```

To rebuild the proofs PDF (TeX Live with `latexmk`):

```bash
cd docs/proofs
latexmk -pdf leemfo_proofs.tex
```

## Layout

| File | Content |
|---|---|
| `LeemFO/Basic.lean` | \(\chi_S,\chi_C,M,W_S,W_C,R_0\), nac/ac (`lam` is paper \(\lambda\)) |
| `LeemFO/Gaussian.lean` | FWHM and Gaussian characteristic functions |
| `LeemFO/Aberration.lean` | \(\nabla\chi_S\) and first-order Taylor in tilt \(k\) |
| `LeemFO/EnvelopeSpatial.lean` | Appendix A1: \(E_S\) |
| `LeemFO/EnvelopeChromatic.lean` | Appendix A1: \(E_{C,\mathrm{tot}}\) and polar form |
| `LeemFO/CTF.lean` | \(q'=0\) recovery and hermiticity |
| `LeemFO/Ratios.lean` | \(\Gamma_C,\Gamma_S\) |
| `LeemFO/PhaseObject.lean` | Jacobi–Anger for \(\mathrm{e}^{\mathrm{i}\varphi\sin\theta}\) |
