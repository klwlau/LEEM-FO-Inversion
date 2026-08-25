/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Forward.Basic
import LeemFO.Forward.Gaussian
import LeemFO.Forward.Aberration
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Appendix A1–A2: chromatic envelope `E_{C,tot}` and polar form of `E_CC`
-/

open Complex hiding log exp
open Real hiding log exp
open MeasureTheory
open scoped ComplexConjugate

namespace LEEM

variable (p : LEEM)

/-- Energy-spread Gaussian width from the paper’s FWHM `ΔE`. -/
noncomputable def sigmaE : ℝ := p.ΔE / fwhmFactor

lemma sigmaE_eq (h : 0 < p.ΔE) : p.ΔE = fwhmFactor * p.sigmaE := by
  unfold sigmaE
  field_simp [ne_of_gt fwhmFactor_pos]

lemma sigmaE_pos (h : 0 < p.ΔE) : 0 < p.sigmaE :=
  div_pos h fwhmFactor_pos

/-- Chromatic envelope as the Appendix A1 integral. -/
noncomputable def chromaticEnvelopeIntegral (q q' : ℝ) : ℂ :=
  ∫ ε : ℝ, (gaussian1D p.sigmaE ε : ℂ) *
    cexp ((2 * π * I) * (p.b1 q q' * ε + p.b2 q q' * ε ^ 2))

/-- Quadratic coefficient `B` of the Gaussian exponent. -/
noncomputable def chromaticB (σ b2 : ℝ) : ℂ :=
  { re := -(1 / (2 * σ ^ 2)), im := 2 * Real.pi * b2 }

lemma chromaticB_re {σ b2 : ℝ} (hσ : 0 < σ) : (chromaticB σ b2).re < 0 := by
  change -(1 / (2 * σ ^ 2)) < 0
  have : 0 < 1 / (2 * σ ^ 2) := by positivity
  linarith

/-- Denominator `1 - 4π i b₂ σ²`. -/
noncomputable def eccDenom (σ b2 : ℝ) : ℂ :=
  { re := 1, im := -(4 * Real.pi * b2 * σ ^ 2) }

/-- Prefactor `E_CC = (1 - 4π i b₂ σ_E²)^{-1/2}` (Eq. (6b)). -/
noncomputable def ecc (σ b2 : ℝ) : ℂ :=
  eccDenom σ b2 ^ (-(1 / 2 : ℂ))

lemma eccDenom_ne_zero (σ b2 : ℝ) : eccDenom σ b2 ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [eccDenom, zero_re] at hr
  exact one_ne_zero hr

lemma ecc_sq (σ b2 : ℝ) :
    (ecc σ b2) ^ 2 = (eccDenom σ b2)⁻¹ := by
  have h := eccDenom_ne_zero σ b2
  unfold ecc
  have hsum : (-(1 / 2 : ℂ)) + (-(1 / 2 : ℂ)) = -1 := by ring
  rw [sq, ← cpow_add _ _ h, hsum, cpow_neg_one]

lemma ecc_at_b2_zero (σ : ℝ) : ecc σ 0 = 1 := by
  have h : eccDenom σ 0 = 1 := by
    apply Complex.ext
    · simp only [eccDenom, one_re]
    · simp only [eccDenom, mul_zero, zero_mul, neg_zero, one_im]
  simp [ecc, h]

/-- Closed form packaged as Eq. (6a). -/
noncomputable def chromaticEnvelopeClosed (σ b1 b2 : ℝ) : ℂ :=
  ecc σ b2 * cexp (-(2 : ℂ) * π ^ 2 * σ ^ 2 * b1 ^ 2 * (ecc σ b2) ^ 2)

lemma quadratic_exponent_eq (σ b1 b2 ε : ℝ) :
    -((1 / (2 * σ ^ 2) : ℝ) : ℂ) * (ε : ℂ) ^ 2
        + (2 * π * I) * (b1 * ε + b2 * ε ^ 2)
      = chromaticB σ b2 * (ε : ℂ) ^ 2 + (2 * π * I * b1) * ε + 0 := by
  apply Complex.ext
  · simp only [chromaticB, add_zero]
    simp [add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, neg_re, pow_two]
  · simp only [chromaticB, add_zero]
    simp [add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, neg_im, pow_two]
    ring

lemma gaussian1D_quadratic_phase (σ b1 b2 ε : ℝ) :
    (gaussian1D σ ε : ℂ) * cexp ((2 * π * I) * (b1 * ε + b2 * ε ^ 2))
      = (1 / (σ * sqrt (2 * π)) : ℂ) *
          cexp (chromaticB σ b2 * (ε : ℂ) ^ 2 + (2 * π * I * b1) * ε + 0) := by
  rw [gaussian1D_cexp, mul_assoc, ← Complex.exp_add, quadratic_exponent_eq]

/-- Quadratic-phase Gaussian integral, matching Appendix A1. -/
theorem chromatic_integral_eq_quadratic {σ b1 b2 : ℝ} (hσ : 0 < σ) :
    ∫ ε : ℝ, (gaussian1D σ ε : ℂ) *
        cexp ((2 * π * I) * (b1 * ε + b2 * ε ^ 2))
      = (1 / (σ * sqrt (2 * π)) : ℂ) *
          (π / -chromaticB σ b2) ^ (1 / 2 : ℂ) *
            cexp (-(2 * π * I * b1) ^ 2 / (4 * chromaticB σ b2)) := by
  have hb := chromaticB_re (b2 := b2) hσ
  have hinter :
      (fun ε : ℝ =>
          (gaussian1D σ ε : ℂ) * cexp ((2 * π * I) * (b1 * ε + b2 * ε ^ 2)))
        = fun ε : ℝ =>
          (1 / (σ * sqrt (2 * π)) : ℂ) *
            cexp (chromaticB σ b2 * (ε : ℂ) ^ 2 + (2 * π * I * b1) * ε + 0) := by
    funext ε
    exact gaussian1D_quadratic_phase σ b1 b2 ε
  rw [hinter, integral_const_mul, integral_cexp_quadratic hb, zero_sub, neg_div]
  exact (mul_assoc _ _ _).symm

theorem chromaticEnvelopeClosed_nac {σ b1 : ℝ} :
    chromaticEnvelopeClosed σ b1 0 = cexp (-(2 : ℂ) * π ^ 2 * σ ^ 2 * b1 ^ 2) := by
  simp [chromaticEnvelopeClosed, ecc_at_b2_zero]

theorem chromaticEnvelopeIntegral_eq_closed_of_b2_zero {σ b1 : ℝ} (hσ : 0 < σ) :
    ∫ ε : ℝ, (gaussian1D σ ε : ℂ) *
        cexp ((2 * π * I) * (b1 * ε + (0 : ℝ) * ε ^ 2))
      = chromaticEnvelopeClosed σ b1 0 := by
  have hfun :
      (fun ε : ℝ => (gaussian1D σ ε : ℂ) *
          cexp ((2 * π * I) * (b1 * ε + (0 : ℝ) * ε ^ 2)))
        = fun ε : ℝ => (gaussian1D σ ε : ℂ) * cexp ((2 * π * I) * b1 * ε) := by
    funext ε
    simp [mul_assoc]
  rw [hfun, charFun_source1D hσ, chromaticEnvelopeClosed_nac]

lemma eccDenom_arg_ne_pi (σ b2 : ℝ) : (eccDenom σ b2).arg ≠ π := by
  have hre : 0 ≤ (eccDenom σ b2).re := by
    change 0 ≤ (1 : ℝ)
    exact zero_le_one
  have hbound := abs_arg_le_pi_div_two_iff.2 hre
  intro hπ
  rw [hπ] at hbound
  have : (π : ℝ) ≤ π / 2 := by
    simpa [abs_of_pos Real.pi_pos] using hbound
  linarith [Real.pi_pos]

lemma chromaticB_eq_div {σ b2 : ℝ} (hσ : 0 < σ) :
    chromaticB σ b2 = -eccDenom σ b2 * Complex.ofReal (2 * σ ^ 2)⁻¹ := by
  have hσ0 : (2 * σ ^ 2 : ℝ) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [chromaticB, eccDenom, mul_re, neg_re, neg_im, ofReal_re, ofReal_im]
    field_simp [hσ0]
    ring
  · simp only [chromaticB, eccDenom, mul_im, neg_re, neg_im, ofReal_re, ofReal_im]
    field_simp [hσ0]
    ring

lemma two_pi_I_mul_sq (b1 : ℝ) :
    (2 * π * I * b1) ^ 2 = -((4 : ℂ) * π ^ 2 * b1 ^ 2) := by
  have hI : I ^ 2 = (-1 : ℂ) := I_sq
  calc
    (2 * π * I * (b1 : ℂ)) ^ 2
        = (2 * π * (b1 : ℂ)) ^ 2 * I ^ 2 := by ring
      _ = (2 * π * (b1 : ℂ)) ^ 2 * (-1) := by rw [hI]
      _ = -((4 : ℂ) * π ^ 2 * b1 ^ 2) := by ring

lemma chromatic_exponent {σ b1 b2 : ℝ} (hσ : 0 < σ) :
    -(2 * π * I * b1) ^ 2 / (4 * chromaticB σ b2)
      = -(2 : ℂ) * π ^ 2 * σ ^ 2 * b1 ^ 2 * (ecc σ b2) ^ 2 := by
  have hden := eccDenom_ne_zero σ b2
  have hσ0 : (2 * σ ^ 2 : ℝ) ≠ 0 := by positivity
  have hB := chromaticB_eq_div (b2 := b2) hσ
  have hecc := ecc_sq σ b2
  have hinv : Complex.ofReal (2 * σ ^ 2)⁻¹ = (Complex.ofReal (2 * σ ^ 2))⁻¹ := by
    simp [ofReal_inv]
  rw [two_pi_I_mul_sq, hB, hinv, hecc]
  field_simp [hden, ofReal_ne_zero.mpr hσ0]
  push_cast
  ring

lemma cpow_div_ofReal_half {A : ℝ} {D : ℂ} (hA : 0 < A) (hD : D ≠ 0)
    (harg : D.arg ≠ π) :
    ((A : ℂ) / D) ^ (1 / 2 : ℂ)
      = (A : ℂ) ^ (1 / 2 : ℂ) * D ^ (-(1 / 2 : ℂ)) := by
  have hA0 : (A : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA.ne'
  rw [div_eq_mul_inv]
  rw [cpow_def_of_ne_zero (mul_ne_zero hA0 (inv_ne_zero hD))]
  rw [Complex.log_ofReal_mul hA (inv_ne_zero hD), Complex.log_inv D harg]
  rw [cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hD]
  rw [add_mul, Complex.exp_add, Complex.ofReal_log hA.le]
  congr 1
  simp [neg_mul, mul_neg]

lemma chromatic_prefactor_real {σ : ℝ} (hσ : 0 < σ) :
    (1 / (σ * sqrt (2 * π)) : ℂ) *
        Complex.ofReal ((2 * π * σ ^ 2) ^ (1 / 2 : ℝ)) = 1 := by
  have hs : (2 * π * σ ^ 2) ^ (1 / 2 : ℝ) = σ * sqrt (2 * π) := by
    have hπ : 0 ≤ (2 * π : ℝ) := by positivity
    rw [show (2 * π * σ ^ 2) = σ ^ 2 * (2 * π) by ring,
      Real.mul_rpow (sq_nonneg σ) hπ, ← Real.sqrt_eq_rpow, sqrt_sq hσ.le]
    rw [Real.sqrt_eq_rpow]
  rw [hs, ofReal_mul]
  field_simp [ofReal_ne_zero.mpr (ne_of_gt hσ),
    ofReal_ne_zero.mpr (ne_of_gt (sqrt_pos.mpr (by positivity)))]

lemma chromatic_prefactor {σ b2 : ℝ} (hσ : 0 < σ) :
    (1 / (σ * sqrt (2 * π)) : ℂ) *
        (π / -chromaticB σ b2) ^ (1 / 2 : ℂ) = ecc σ b2 := by
  have hden := eccDenom_ne_zero σ b2
  have hB := chromaticB_eq_div (b2 := b2) hσ
  have hσ0 : (2 * σ ^ 2 : ℝ) ≠ 0 := by positivity
  have hneg : -chromaticB σ b2 = eccDenom σ b2 * Complex.ofReal (2 * σ ^ 2)⁻¹ := by
    rw [hB]; ring
  have hquot : (π : ℂ) / -chromaticB σ b2
      = Complex.ofReal (2 * π * σ ^ 2) / eccDenom σ b2 := by
    rw [hneg]
    have hinv : Complex.ofReal (2 * σ ^ 2)⁻¹ = (Complex.ofReal (2 * σ ^ 2))⁻¹ := by
      simp [ofReal_inv]
    rw [hinv]
    field_simp [hden, ofReal_ne_zero.mpr hσ0]
    push_cast
    ring
  have hA : 0 < (2 * π * σ ^ 2 : ℝ) := by positivity
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hquot, cpow_div_ofReal_half hA hden (eccDenom_arg_ne_pi σ b2), h12,
    ← ofReal_cpow hA.le, ← mul_assoc, chromatic_prefactor_real hσ, one_mul]
  simp [ecc, h12]

theorem chromatic_quadratic_eq_closed {σ b1 b2 : ℝ} (hσ : 0 < σ) :
    (1 / (σ * sqrt (2 * π)) : ℂ) *
        (π / -chromaticB σ b2) ^ (1 / 2 : ℂ) *
          cexp (-(2 * π * I * b1) ^ 2 / (4 * chromaticB σ b2))
      = chromaticEnvelopeClosed σ b1 b2 := by
  rw [chromatic_prefactor hσ, chromatic_exponent hσ]
  rfl

theorem chromaticEnvelopeIntegral_eq_closed (h : 0 < p.ΔE) (q q' : ℝ) :
    p.chromaticEnvelopeIntegral q q'
      = chromaticEnvelopeClosed p.sigmaE (p.b1 q q') (p.b2 q q') := by
  unfold chromaticEnvelopeIntegral
  rw [chromatic_integral_eq_quadratic (p.sigmaE_pos h)]
  exact chromatic_quadratic_eq_closed (p.sigmaE_pos h)

lemma gaussian1D_quadratic_conj (σ b1 b2 ε : ℝ) :
    conj ((gaussian1D σ ε : ℂ) * cexp ((2 * π * I) * (b1 * ε + b2 * ε ^ 2)))
      = (gaussian1D σ ε : ℂ) *
          cexp ((2 * π * I) * ((-b1) * ε + (-b2) * ε ^ 2)) := by
  rw [map_mul, conj_ofReal, ← exp_conj]
  congr 2
  simp [map_add, map_mul, conj_I, conj_ofReal, conj_ofNat]
  ring

lemma chromatic_integral_eq_closed' {σ b1 b2 : ℝ} (hσ : 0 < σ) :
    ∫ ε : ℝ, (gaussian1D σ ε : ℂ) *
        cexp ((2 * π * I) * (b1 * ε + b2 * ε ^ 2))
      = chromaticEnvelopeClosed σ b1 b2 := by
  rw [chromatic_integral_eq_quadratic hσ, chromatic_quadratic_eq_closed hσ]

theorem chromaticEnvelopeClosed_neg {σ b1 b2 : ℝ} (hσ : 0 < σ) :
    chromaticEnvelopeClosed σ (-b1) (-b2)
      = conj (chromaticEnvelopeClosed σ b1 b2) := by
  rw [← chromatic_integral_eq_closed' (b1 := -b1) (b2 := -b2) hσ,
    ← chromatic_integral_eq_closed' (b1 := b1) (b2 := b2) hσ, ← integral_conj]
  congr 1
  funext ε
  simpa [neg_mul] using (gaussian1D_quadratic_conj σ b1 b2 ε).symm

lemma norm_one_sub_I (y : ℝ) : ‖(1 - I * y : ℂ)‖ = sqrt (1 + y ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp

lemma arg_one_sub_I (y : ℝ) : arg (1 - I * y) = -arctan y := by
  have hre : 0 ≤ (1 - I * y : ℂ).re := by simp
  have him : (1 - I * y : ℂ).im = -y := by simp
  rw [arg_of_re_nonneg hre, him, norm_one_sub_I, neg_div, Real.arcsin_neg, arctan_eq_arcsin]

theorem ecc_norm (y : ℝ) :
    ‖(1 - I * y : ℂ) ^ (-(1 / 2 : ℂ))‖ = (1 + y ^ 2) ^ (-(1 / 4 : ℝ)) := by
  have h12 : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by norm_num
  rw [h12, norm_cpow_real, norm_one_sub_I, sqrt_eq_rpow]
  have hpos : 0 < 1 + y ^ 2 := by positivity
  rw [← Real.rpow_mul hpos.le]
  ring_nf

theorem ecc_polar (y : ℝ) :
    (1 - I * y : ℂ) ^ (-(1 / 2 : ℂ))
      = Complex.ofReal ((1 + y ^ 2) ^ (-(1 / 4 : ℝ)))
        * cexp (I * (1 / 2) * arctan y) := by
  have h12 : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by norm_num
  rw [h12, cpow_ofReal, arg_one_sub_I]
  have hnn : 0 ≤ 1 + y ^ 2 := by positivity
  have hpow : ‖(1 - I * y : ℂ)‖ ^ (-(1 / 2 : ℝ))
      = (1 + y ^ 2) ^ (-(1 / 4 : ℝ)) := by
    rw [norm_one_sub_I, sqrt_eq_rpow, ← Real.rpow_mul hnn]
    ring_nf
  rw [hpow]
  have hθ : (-arctan y) * (-(1 / 2 : ℝ)) = (1 / 2) * arctan y := by ring
  rw [hθ]
  have hcis :
      (Real.cos ((1 / 2) * arctan y) : ℂ)
          + (Real.sin ((1 / 2) * arctan y) : ℂ) * I
        = cexp (((1 / 2 : ℝ) * arctan y : ℝ) * I) := by
    simpa [ofReal_cos, ofReal_sin] using
      (Complex.exp_mul_I (↑((1 / 2 : ℝ) * arctan y))).symm
  rw [hcis]
  simp [mul_comm, mul_assoc]

lemma eccDenom_eq_one_sub_I (σ b2 : ℝ) :
    eccDenom σ b2 = 1 - I * (4 * Real.pi * b2 * σ ^ 2 : ℝ) := by
  apply Complex.ext
  · simp only [eccDenom, sub_re, one_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
      zero_mul, mul_zero, sub_zero]
  · simp only [eccDenom, sub_im, one_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
      zero_mul, one_mul, zero_sub, zero_add]

/-- Polar form of `E_CC` with the paper’s \(y = 4\pi b_2\sigma_E^2\). -/
theorem ecc_eq_polar (σ b2 : ℝ) :
    ecc σ b2
      = Complex.ofReal
          ((1 + (4 * Real.pi * b2 * σ ^ 2) ^ 2) ^ (-(1 / 4 : ℝ)))
        * cexp (I * (1 / 2) * arctan (4 * Real.pi * b2 * σ ^ 2)) := by
  unfold ecc
  rw [eccDenom_eq_one_sub_I]
  exact ecc_polar _

end LEEM
