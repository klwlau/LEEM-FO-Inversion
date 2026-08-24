/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO

/-|
================================================================
 Machine-checked proofs of ac-LEEM Fourier-optics identities
================================================================

:Author: Wilson Lau
:Date: 24 August 2026

.. contents::
   :depth: 2

Abstract
========

This note is a literate Lean 4 rendering of the formal proofs in the
``LeemFO`` library: the appendix identities of Yu, Lau and Altman,
*Ultramicroscopy* **200** (2019) 160–168, for Fourier-optics (FO) image
formation in aberration-corrected LEEM.  Each section states the
analytic claim, points at the Lean name, and replays the proof script
that the library uses.

The PDF is produced by `Alectryon <https://github.com/cpitclaudel/alectryon>`_
from this file (``docs/alectryon/LeemFOProofs.lean``).  Alectryon
extracts the reStructuredText prose delimited by ``/-|`` … ``|-/`` and
typesets the surrounding Lean.  The companion handwritten analytic
note is ``docs/proofs/leemfo_proofs.pdf``; equation numbers and the
modelling hypotheses live in ``docs/FORMALIZATION.md``.

Conventions
===========

- :math:`\chi` is in **waves**, with :math:`W = e^{2\pi i \chi}`.
- Lean cannot use ``λ`` as an identifier, so the wavelength is ``lam``.
- The 1D theory uses signed scalars :math:`q,q'` (products, not
  magnitudes).
- Truncations used by the paper (frozen aperture, first-order tilt,
  dropped mixed :math:`k\varepsilon`) are modelling hypotheses, not
  Lean theorems.

.. default-role:: lean4
|-/

open Complex Real Filter Asymptotics Topology
open scoped ComplexConjugate Topology

open LEEM

namespace LeemFOProofs

/-|
Instrument model
================

The structure `LEEM` packages one imaging condition.  Spatial and
chromatic paths are the spatial-frequency forms of the paper, with
powers of ``lam`` restored so that :math:`q` is a spatial frequency:

.. math::

   \chi_S(q,\Delta z)
     = \tfrac{1}{4} C_3\lambda^3 q^4
     + \tfrac{1}{6} C_5\lambda^5 q^6
     + \tfrac{1}{2} \Delta z\,\lambda\, q^2,

   \chi_C(q,\varepsilon)
     = \tfrac{1}{2} C_C\lambda (\varepsilon/E) q^2
     + \tfrac{1}{2} C_{CC}\lambda (\varepsilon/E)^2 q^2
     + \tfrac{1}{4} C_{3C}\lambda^3 (\varepsilon/E) q^4.

The coherent kernel :math:`R_0` (paper Eq. (2)) is the product of
apertures and transfer factors.  After the paper's first-order /
no-mixed-term approximation, the working FO kernel is
:math:`R_{\mathrm{FO}} = R_0(q,q',\Delta z,0)\, E_S\, E_{C,\mathrm{tot}}`.
|-/

#check LEEM
#check LEEM.chiS
#check LEEM.chiC
#check LEEM.R0
#check LEEM.aS
#check LEEM.b1
#check LEEM.b2

/-|
The phase identity :math:`W_S(q) W_S(q')^* = \exp\bigl(2\pi i
(\chi_S(q)-\chi_S(q'))\bigr)` is `LEEM.waveS_mul_conj`.  It is
``cexp``-algebra: conjugating flips the sign of :math:`2\pi i \chi`.
|-/

example (p : LEEM) (q q' Δz : ℝ) :
    p.waveS q Δz * conj (p.waveS q' Δz)
      = cexp (2 * π * I * ((p.chiS q Δz - p.chiS q' Δz : ℝ) : ℂ)) :=
  p.waveS_mul_conj q q' Δz

/-|
Gaussian calculus
=================

The paper's Gaussians are specified by FWHM.  With
:math:`\Delta = 2\sqrt{2\ln 2}\,\sigma` one has :math:`f(\Delta/2) =
f(0)/2`, and inverting gives :math:`\sigma^2 = \Delta^2/(8\ln 2)`.
The FWHM packaging of the spatial envelope uses
:math:`\kappa = \pi^2 q_{\mathrm{ill}}^2 / (4\ln 2)`, which is
exactly :math:`2\pi^2\sigma_{\mathrm{ill}}^2`.
|-/

example {σ : ℝ} (hσ : 0 < σ) :
    rexp (-((fwhmFactor * σ) / 2) ^ 2 / (2 * σ ^ 2)) = 1 / 2 := by
  have hhalf : (fwhmFactor * σ) / 2 = Real.sqrt (2 * Real.log 2) * σ := by
    unfold fwhmFactor; ring
  have hsq : ((fwhmFactor * σ) / 2) ^ 2 / (2 * σ ^ 2) = Real.log 2 := by
    rw [hhalf, mul_pow, Real.sq_sqrt (mul_nonneg two_pos.le log_two_pos.le)]
    field_simp [ne_of_gt hσ]
  have hneg : -((fwhmFactor * σ) / 2) ^ 2 / (2 * σ ^ 2) = -Real.log 2 := by
    rw [neg_div, hsq]
  rw [hneg, Real.exp_neg, Real.exp_log two_pos]
  ring

example {σ Δ : ℝ} (hσ : 0 < σ) (hΔ : Δ = fwhmFactor * σ) :
    σ ^ 2 = Δ ^ 2 / (8 * Real.log 2) :=
  variance_from_fwhm hσ hΔ

example {σ qIll : ℝ} (hσ : 0 < σ) (h : qIll = fwhmFactor * σ) :
    2 * π ^ 2 * σ ^ 2 = kappaIll qIll :=
  kappaIll_eq_sigma hσ h

/-|
Characteristic function
-----------------------

Appendix A1 is the Fourier transform of a centred Gaussian.  Lean
proves

.. math::

   \int_{\mathbb{R}} s(k)\, e^{2\pi i a k}\, dk
     = e^{-2\pi^2 \sigma^2 a^2}

as `charFun_source1D`.  The proof rewrites the integrand as a
quadratic exponential, applies Mathlib's `integral_cexp_quadratic`,
cancels the normalisation against :math:`\sqrt{\pi/|B|}`, and uses
:math:`i^2 = -1` in the completed-square exponent.
|-/

example {σ a : ℝ} (hσ : 0 < σ) :
    ∫ k : ℝ, (gaussian1D σ k : ℂ) * cexp ((2 * π * I) * a * k)
      = cexp (-(2 : ℂ) * π ^ 2 * σ ^ 2 * a ^ 2) :=
  charFun_source1D hσ

/-|
The 2D isotropic source is a product of 1D Gaussians, so the 2D
characteristic function is the 1D result iterated (`charFun_source2D`).
The exponent becomes :math:`-2\pi^2\sigma^2(a_x^2+a_y^2)`.

Aberration identities
=====================

`LEEM.hasDerivAt_chiS` differentiates the polynomial :math:`\chi_S`.
The illumination-tilt factor is then exactly the difference of
derivatives, `LEEM.aS_eq_deriv_sub`.  Paper Eq. (3) is the little-o
form of that derivative (`LEEM.chiS_taylor`).
|-/

example (p : LEEM) (q q' Δz : ℝ) :
    p.aS q q' Δz = deriv (p.chiS · Δz) q - deriv (p.chiS · Δz) q' := by
  simp [LEEM.aS, p.deriv_chiS]
  ring

example (p : LEEM) (Δz q : ℝ) :
    (fun k : ℝ => p.chiS (q + k) Δz - p.chiS q Δz
      - k * (p.C3 * p.lam ^ 3 * q ^ 3 + p.C5 * p.lam ^ 5 * q ^ 5
        + Δz * p.lam * q))
      =o[nhds 0] id :=
  p.chiS_taylor Δz q

/-|
The chromatic path difference is not an approximation: it factors
exactly as :math:`b_1\varepsilon + b_2\varepsilon^2` once
:math:`E \neq 0` (`LEEM.chiC_sub`).  On the diagonal
:math:`q=q'` one has :math:`a = b_1 = b_2 = 0`.
|-/

example (p : LEEM) (hp : p.IsPhysical) (q q' ε : ℝ) :
    p.chiC q ε - p.chiC q' ε = p.b1 q q' * ε + p.b2 q q' * ε ^ 2 := by
  unfold LEEM.chiC LEEM.b1 LEEM.b2 LEEM.IsPhysical at *
  have hE : p.E ≠ 0 := ne_of_gt hp.2
  field_simp [hE]
  ring

example (p : LEEM) (q Δz : ℝ) :
    p.aS q q Δz = 0 ∧ p.b1 q q = 0 ∧ p.b2 q q = 0 :=
  ⟨p.aS_zero_diag q Δz, p.b1_zero_diag q, p.b2_zero_diag q⟩

/-|
Spatial envelope (paper Eq. (5))
================================

The spatial envelope is the source characteristic function evaluated
at :math:`a = \partial_q\chi_S(q) - \partial_q\chi_S(q')`:

.. math::

   E_S(q,q',\Delta z)
     = \int s(k)\, e^{2\pi i a k}\, dk
     = e^{-2\pi^2 \sigma_{\mathrm{ill}}^2 a^2}
     = e^{-\kappa a^2}.

``spatialEnvelopeIntegral_eq_closed`` is the first equality
(instantiate ``charFun_source1D``);
``spatialEnvelopeClosed_eq_fwhm`` rewrites
:math:`2\pi^2\sigma^2` as :math:`\kappa`; chaining them is
``spatialEnvelope_eq_fwhm``.
|-/

example (p : LEEM) (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.spatialEnvelopeIntegral q q' Δz = p.spatialEnvelopeClosed q q' Δz := by
  unfold LEEM.spatialEnvelopeIntegral LEEM.spatialEnvelopeClosed
  rw [charFun_source1D (p.sigmaIll_pos h)]
  congr 1
  push_cast
  ring

example (p : LEEM) (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.spatialEnvelopeClosed q q' Δz = p.spatialEnvelopeFWHM q q' Δz := by
  unfold LEEM.spatialEnvelopeClosed LEEM.spatialEnvelopeFWHM
  have hk := kappaIll_eq_sigma (p.sigmaIll_pos h) (p.sigmaIll_eq h)
  congr 1
  simp [← hk]

example (p : LEEM) (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.spatialEnvelopeIntegral q q' Δz = p.spatialEnvelopeFWHM q q' Δz :=
  p.spatialEnvelope_eq_fwhm h q q' Δz

/-|
The closed form is real (`LEEM.spatialEnvelopeClosed_real`) and
symmetric in :math:`(q,q')` because :math:`a(q,q') = -a(q',q)`.
On the diagonal :math:`a=0` so :math:`E_S=1`.

Chromatic envelope (paper Eqs. (6a)–(6b))
=========================================

Energy spread contributes both a linear phase :math:`b_1\varepsilon`
and a quadratic phase :math:`b_2\varepsilon^2`.  Completing the square
in the complex Gaussian integral produces

.. math::

   E_{CC} = (1 - 4\pi i b_2 \sigma_E^2)^{-1/2},
   \qquad
   E_{C,\mathrm{tot}}
     = E_{CC}\,
       \exp\bigl(-2\pi^2\sigma_E^2 b_1^2 E_{CC}^2\bigr).

Lean names: ``ecc`` and ``chromaticEnvelopeClosed``.
The identity ``chromaticEnvelopeIntegral_eq_closed`` matches the
integral to that closed form: rewrite as a quadratic exponential
(``chromatic_integral_eq_quadratic``, using Mathlib
``integral_cexp_quadratic``) and identify the prefactor with ``ecc``.
If :math:`b_2=0` (nac), ``ecc = 1`` and
the formula collapses to the ordinary characteristic function.
|-/

#check ecc
#check chromaticEnvelopeClosed

example {σ b1 : ℝ} :
    chromaticEnvelopeClosed σ b1 0
      = cexp (-(2 : ℂ) * π ^ 2 * σ ^ 2 * b1 ^ 2) :=
  chromaticEnvelopeClosed_nac

example (p : LEEM) (h : 0 < p.ΔE) (q q' : ℝ) :
    p.chromaticEnvelopeIntegral q q'
      = chromaticEnvelopeClosed p.sigmaE (p.b1 q q') (p.b2 q q') :=
  p.chromaticEnvelopeIntegral_eq_closed h q q'

/-|
Polar form of :math:`E_{CC}`
----------------------------

Write :math:`1 - 4\pi i b_2\sigma_E^2 = 1 - i y` with
:math:`y = 4\pi b_2\sigma_E^2`.  Then
:math:`\arg(1-iy) = -\arctan y` (real part is positive) and

.. math::

   (1-iy)^{-1/2}
     = (1+y^2)^{-1/4}\,
       e^{i (\arctan y)/2}.

That is `ecc_eq_polar`, using `arg_one_sub_I` and `ecc_polar`.
|-/

example (σ b2 : ℝ) :
    ecc σ b2
      = Complex.ofReal
          ((1 + (4 * Real.pi * b2 * σ ^ 2) ^ 2) ^ (-(1 / 4 : ℝ)))
        * cexp (I * (1 / 2) * arctan (4 * Real.pi * b2 * σ ^ 2)) :=
  ecc_eq_polar σ b2

/-|
CTF as the :math:`q'=0` slice
=============================

`R_FO` is the working bilinear kernel; `R_CTF` is the separable
product of one-argument envelopes (printed Eqs. (7a)–(7b), **no**
extra conjugate on the chromatic factors).  Hermiticity of :math:`R_0`
is `LEEM.R0_hermitian`: conjugating swaps :math:`(q,q')` because
apertures are real.

On :math:`q'=0` the joint envelopes reduce to the CTF product
(`LEEM.R_FO_eq_R_CTF_axis`): the spatial diagonal is 1, and
:math:`b_1(q,0)`, :math:`b_2(q,0)` together with the nac collapse of
the primed chromatic factor match `spatialCTF` and `chromaticCTF`.
|-/

#check LEEM.R_FO
#check LEEM.R_CTF

example (p : LEEM) (q q' Δz ε : ℝ) :
    conj (p.R0 q q' Δz ε) = p.R0 q' q Δz ε := by
  simp only [LEEM.R0, map_mul, conj_ofReal, conj_conj]
  ac_rfl

example (p : LEEM) (q Δz : ℝ) :
    p.R_FO q 0 Δz = p.R_CTF q 0 Δz := by
  unfold LEEM.R_FO LEEM.R_CTF LEEM.spatialCTF LEEM.chromaticCTF
  rw [p.spatialEnvelopeClosed_diag 0 Δz, p.b1_zero_diag, p.b2_zero_diag,
    chromaticEnvelopeClosed_nac]
  simp

/-|
Envelope ratios
===============

The comparison factors are the ratios of axis envelopes to joint
envelopes:

.. math::

   \Gamma_S
     = \frac{E_S(q,0)\, E_S(q',0)}{E_S(q,q')},
   \qquad
   \Gamma_C
     = \frac{E_C(q,0)\, E_C(q',0)}{E_C(q,q')}.

Gaussian algebra gives :math:`\Gamma_S = \exp(-4\pi^2\sigma_{\mathrm{ill}}^2 u v)`
with :math:`u=\chi'(q)`, :math:`v=\chi'(q')` (`LEEM.gammaS_eq_dot`),
or equivalently :math:`\exp(-2\kappa u v)` (`LEEM.gammaS_eq_kappa`).
Under AC (:math:`C_3=0`) the derivatives keep only :math:`C_5` and
defocus (`LEEM.gammaS_ac`).
|-/

example (p : LEEM) (q q' Δz : ℝ) :
    p.gammaS q q' Δz
      = cexp (-(4 : ℂ) * π ^ 2 * p.sigmaIll ^ 2
          * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q') :=
  p.gammaS_eq_dot q q' Δz

example (p : LEEM) (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.gammaS q q' Δz
      = cexp (-(2 : ℂ) * kappaIll p.qIll
          * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q') :=
  p.gammaS_eq_kappa h q q' Δz

example (p : LEEM) (hAC : p.IsAC) (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.gammaS q q' Δz
      = cexp (-(2 : ℂ) * kappaIll p.qIll
          * (p.C5 * p.lam ^ 5 * q ^ 5 + Δz * p.lam * q)
          * (p.C5 * p.lam ^ 5 * q' ^ 5 + Δz * p.lam * q')) :=
  p.gammaS_ac hAC h q q' Δz

/-|
Multiplying FO by the two ratios rebuilds CTF, because :math:`E_S` is
real (so the spatial conjugate is redundant):
`LEEM.R_CTF_eq_R_FO_mul_gamma`.  Perfect coherence
(:math:`q_{\mathrm{ill}}=\Delta E=0`) forces both ratios to 1, hence
:math:`R_{\mathrm{CTF}}=R_{\mathrm{FO}}`.
|-/

example (p : LEEM) (q q' Δz : ℝ) :
    p.R_CTF q q' Δz = p.R_FO q q' Δz * p.gammaC q q' * p.gammaS q q' Δz := by
  have hEs : p.spatialEnvelopeClosed q q' Δz ≠ 0 := Complex.exp_ne_zero _
  have hEc := chromaticEnvelopeClosed_ne_zero p.sigmaE (p.b1 q q') (p.b2 q q')
  unfold LEEM.R_CTF LEEM.R_FO LEEM.gammaC LEEM.gammaS
  rw [p.spatialCTF_conj q' Δz]
  unfold LEEM.spatialCTF LEEM.chromaticCTF
  field_simp [hEs, hEc]

example (p : LEEM) (h : p.PerfectCoherence) (q q' Δz : ℝ) :
    p.gammaC q q' * p.gammaS q q' Δz = 1 :=
  p.gamma_product_perfect h q q' Δz

/-|
Jacobi–Anger
============

A strong phase object :math:`e^{i\varphi\sin\theta}` has Fourier
coefficients equal to Bessel functions.  Lean defines ``besselJ n φ``
as that coefficient on :math:`(0,2\pi]`, proves :math:`O(1/n^2)`
decay by two integrations by parts (``besselJ_bound``), hence
summability, and applies Mathlib's pointwise Fourier inversion on
the circle (`jacobi_anger_on_Ioc`).  The identity for every real
angle reduces modulo :math:`2\pi` (`jacobi_anger`).
|-/

#check besselJ
#check jacobi_anger_on_Ioc
#check jacobi_anger

example (φ θ : ℝ) :
    HasSum (fun n : ℤ => besselJ n φ * cexp (I * n * θ)) (phaseFun φ θ) :=
  jacobi_anger φ θ

/-|
Lean name map
=============

- Paper :math:`\lambda` → `LEEM.lam`
- :math:`\chi_S,\chi_C` → `LEEM.chiS`, `LEEM.chiC`
- :math:`R_0` → `LEEM.R0`
- :math:`a,b_1,b_2` → `LEEM.aS`, `LEEM.b1`, `LEEM.b2`
- FWHM / :math:`\kappa` → `fwhmFactor`, `kappaIll`
- :math:`\int s\,e^{2\pi i a k}` → `charFun_source1D`
- Eq. (5) :math:`E_S` → `LEEM.spatialEnvelope_eq_fwhm`
- Eqs. (6a)–(6b) → `LEEM.chromaticEnvelopeIntegral_eq_closed`
- Polar :math:`E_{CC}` → `ecc_eq_polar`
- :math:`R_{\mathrm{FO}}` → `LEEM.R_FO`
- :math:`R_{\mathrm{CTF}}` → `LEEM.R_CTF`
- CTF from FO on :math:`q'=0` → `LEEM.R_FO_eq_R_CTF_axis`
- :math:`\Gamma_S = e^{-2\kappa u v}` → `LEEM.gammaS_eq_kappa`
- :math:`R_{\mathrm{CTF}} = R_{\mathrm{FO}} \Gamma_C \Gamma_S`
  → `LEEM.R_CTF_eq_R_FO_mul_gamma`
- Jacobi–Anger → `jacobi_anger`

Rebuild
=======

From the repository root, with ``uv`` and TeX Live (LuaLaTeX)::

   make -C docs/alectryon pdf

The literate source is this file; the typeset PDF is
``docs/alectryon/leemfo_alectryon.pdf``.
|-/

end LeemFOProofs
