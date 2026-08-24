/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Basic
import LeemFO.Gaussian
import LeemFO.Aberration

/-!
# Appendix A1: spatial coherence envelope `E_S`
-/

open Complex Real MeasureTheory

namespace LEEM

variable (p : LEEM)

/-- Illumination Gaussian width from the paper’s FWHM `q_ill`. -/
noncomputable def sigmaIll : ℝ := p.qIll / fwhmFactor

lemma sigmaIll_eq (h : 0 < p.qIll) : p.qIll = fwhmFactor * p.sigmaIll := by
  unfold sigmaIll
  field_simp [ne_of_gt fwhmFactor_pos]

lemma sigmaIll_pos (h : 0 < p.qIll) : 0 < p.sigmaIll :=
  div_pos h fwhmFactor_pos

/-- Spatial envelope as the Appendix A1 integral (1D). -/
noncomputable def spatialEnvelopeIntegral (q q' Δz : ℝ) : ℂ :=
  ∫ k : ℝ, (gaussian1D p.sigmaIll k : ℂ) * cexp ((2 * π * I) * p.aS q q' Δz * k)

/-- Closed form `exp(-2π² σ_ill² a²)`. -/
noncomputable def spatialEnvelopeClosed (q q' Δz : ℝ) : ℂ :=
  cexp (Complex.ofReal (-(2 : ℝ) * π ^ 2 * p.sigmaIll ^ 2 * p.aS q q' Δz ^ 2))

/-- FWHM form of Eq. (5): `exp(-κ |a|²)` with `κ = π² q_ill² / (4 ln 2)`. -/
noncomputable def spatialEnvelopeFWHM (q q' Δz : ℝ) : ℂ :=
  cexp (Complex.ofReal (-kappaIll p.qIll * p.aS q q' Δz ^ 2))

theorem spatialEnvelopeIntegral_eq_closed (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.spatialEnvelopeIntegral q q' Δz = p.spatialEnvelopeClosed q q' Δz := by
  unfold spatialEnvelopeIntegral spatialEnvelopeClosed
  rw [charFun_source1D (p.sigmaIll_pos h)]
  congr 1
  push_cast
  ring

theorem spatialEnvelopeClosed_eq_fwhm (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.spatialEnvelopeClosed q q' Δz = p.spatialEnvelopeFWHM q q' Δz := by
  unfold spatialEnvelopeClosed spatialEnvelopeFWHM
  have hk := kappaIll_eq_sigma (p.sigmaIll_pos h) (p.sigmaIll_eq h)
  congr 1
  simp [← hk]

/-- Combined integral = FWHM closed form (canonical Eq. (5)). -/
theorem spatialEnvelope_eq_fwhm (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.spatialEnvelopeIntegral q q' Δz = p.spatialEnvelopeFWHM q q' Δz := by
  rw [p.spatialEnvelopeIntegral_eq_closed h, p.spatialEnvelopeClosed_eq_fwhm h]

theorem spatialEnvelopeClosed_real (q q' Δz : ℝ) :
    (p.spatialEnvelopeClosed q q' Δz).im = 0 :=
  Complex.exp_ofReal_im _

theorem spatialEnvelopeClosed_symm (q q' Δz : ℝ) :
    p.spatialEnvelopeClosed q q' Δz = p.spatialEnvelopeClosed q' q Δz := by
  unfold spatialEnvelopeClosed
  have h : p.aS q q' Δz = -p.aS q' q Δz := by
    simp [aS]
    ring
  simp [h]

/-- 2D spatial envelope as an iterated integral. -/
noncomputable def spatialEnvelopeIntegral2 (ax ay : ℝ) : ℂ :=
  ∫ kx : ℝ, ∫ ky : ℝ,
    (gaussian2D p.sigmaIll (kx, ky) : ℂ) *
      cexp ((2 * π * I) * (ax * kx + ay * ky))

theorem spatialEnvelopeIntegral2_eq (h : 0 < p.qIll) (ax ay : ℝ) :
    p.spatialEnvelopeIntegral2 ax ay
      = cexp (-(2 : ℂ) * π ^ 2 * p.sigmaIll ^ 2 * (ax ^ 2 + ay ^ 2 : ℂ)) :=
  charFun_source2D (p.sigmaIll_pos h)

end LEEM
