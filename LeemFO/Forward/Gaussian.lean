/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian FWHM and Fourier transforms used in Appendix A1
-/

open Complex hiding log exp
open Real hiding log exp
open MeasureTheory

/-- FWHM factor `2 √(2 ln 2)` relating `σ` to the paper’s `ΔE` / `q_ill`. -/
noncomputable def fwhmFactor : ℝ := 2 * sqrt (2 * Real.log 2)

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

lemma fwhmFactor_pos : 0 < fwhmFactor := by
  unfold fwhmFactor
  positivity

/-- If `f(x) = exp(-x²/(2σ²))`, then `f(Δ/2) = f(0)/2` for `Δ = 2√(2 ln 2) σ`. -/
lemma gaussian_fwhm {σ : ℝ} (hσ : 0 < σ) :
    rexp (-((fwhmFactor * σ) / 2) ^ 2 / (2 * σ ^ 2)) = 1 / 2 := by
  have hhalf : (fwhmFactor * σ) / 2 = sqrt (2 * Real.log 2) * σ := by
    unfold fwhmFactor; ring
  have hsq : ((fwhmFactor * σ) / 2) ^ 2 / (2 * σ ^ 2) = Real.log 2 := by
    rw [hhalf, mul_pow, sq_sqrt (mul_nonneg two_pos.le log_two_pos.le)]
    field_simp [ne_of_gt hσ]
  have hneg : -((fwhmFactor * σ) / 2) ^ 2 / (2 * σ ^ 2) = -Real.log 2 := by
    rw [neg_div, hsq]
  rw [hneg, Real.exp_neg, Real.exp_log two_pos]
  ring

/-- Inverse FWHM relation `σ² = Δ² / (8 ln 2)`. -/
lemma variance_from_fwhm {σ Δ : ℝ} (hσ : 0 < σ) (hΔ : Δ = fwhmFactor * σ) :
    σ ^ 2 = Δ ^ 2 / (8 * Real.log 2) := by
  subst hΔ
  have h8 : (8 : ℝ) * Real.log 2 ≠ 0 := by positivity
  unfold fwhmFactor
  have : (2 * sqrt (2 * Real.log 2) * σ) ^ 2 = 8 * Real.log 2 * σ ^ 2 := by
    rw [mul_pow, mul_pow, sq_sqrt (mul_nonneg two_pos.le log_two_pos.le)]
    ring
  rw [this]
  field_simp [h8]

/-- Prefactor `κ = π² q_ill² / (4 ln 2)` in the FWHM form of `E_S`. -/
noncomputable def kappaIll (qIll : ℝ) : ℝ :=
  π ^ 2 * qIll ^ 2 / (4 * Real.log 2)

lemma kappaIll_eq_sigma {σ qIll : ℝ} (hσ : 0 < σ) (h : qIll = fwhmFactor * σ) :
    2 * π ^ 2 * σ ^ 2 = kappaIll qIll := by
  have hσ2 := variance_from_fwhm hσ h
  unfold kappaIll
  rw [hσ2]
  have : (4 : ℝ) * Real.log 2 ≠ 0 := by positivity
  field_simp [this]
  ring

/-- Normalised 1D Gaussian density (source or energy). -/
noncomputable def gaussian1D (σ k : ℝ) : ℝ :=
  (1 / (σ * sqrt (2 * π))) * rexp (-k ^ 2 / (2 * σ ^ 2))

/-- 2D isotropic source density as a product of 1D Gaussians. -/
noncomputable def gaussian2D (σ : ℝ) (k : ℝ × ℝ) : ℝ :=
  gaussian1D σ k.1 * gaussian1D σ k.2

lemma gaussian2D_closed {σ kx ky : ℝ} (_hσ : 0 < σ) :
    gaussian2D σ (kx, ky)
      = (1 / (2 * π * σ ^ 2)) * rexp (-(kx ^ 2 + ky ^ 2) / (2 * σ ^ 2)) := by
  simp only [gaussian2D, gaussian1D]
  have hs : sqrt (2 * π) * sqrt (2 * π) = 2 * π := by
    rw [← pow_two, sq_sqrt (by positivity)]
  have hexp :
      rexp (-kx ^ 2 / (2 * σ ^ 2)) * rexp (-ky ^ 2 / (2 * σ ^ 2))
        = rexp (-(kx ^ 2 + ky ^ 2) / (2 * σ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc
    (1 / (σ * sqrt (2 * π))) * rexp (-kx ^ 2 / (2 * σ ^ 2)) *
        ((1 / (σ * sqrt (2 * π))) * rexp (-ky ^ 2 / (2 * σ ^ 2)))
      = (1 / (σ ^ 2 * (sqrt (2 * π) * sqrt (2 * π)))) *
          (rexp (-kx ^ 2 / (2 * σ ^ 2)) * rexp (-ky ^ 2 / (2 * σ ^ 2))) := by
        ring
    _ = (1 / (σ ^ 2 * (2 * π))) * rexp (-(kx ^ 2 + ky ^ 2) / (2 * σ ^ 2)) := by
        rw [hs, hexp]
    _ = (1 / (2 * π * σ ^ 2)) * rexp (-(kx ^ 2 + ky ^ 2) / (2 * σ ^ 2)) := by
        ring

lemma gaussian1D_cexp (σ k : ℝ) :
    (gaussian1D σ k : ℂ)
      = (1 / (σ * sqrt (2 * π)) : ℂ) *
          cexp (-((1 / (2 * σ ^ 2) : ℝ) : ℂ) * (k : ℂ) ^ 2) := by
  unfold gaussian1D
  rw [ofReal_mul, ofReal_div, ofReal_exp]
  congr 1
  · simp
  · congr 1
    have : (-k ^ 2 / (2 * σ ^ 2) : ℝ) = -((1 / (2 * σ ^ 2)) * k ^ 2) := by ring
    rw [this, ofReal_neg, ofReal_mul, ofReal_div, ofReal_pow, neg_mul]

lemma gaussian1D_char_eq (σ a k : ℝ) :
    (gaussian1D σ k : ℂ) * cexp ((2 * π * I) * a * k)
      = (1 / (σ * sqrt (2 * π)) : ℂ) *
          cexp (-((1 / (2 * σ ^ 2) : ℝ) : ℂ) * (k : ℂ) ^ 2 + (2 * π * I * a) * k + 0) := by
  rw [gaussian1D_cexp, mul_assoc, ← Complex.exp_add]
  simp [add_zero]

lemma integrable_gaussian1D_char {σ a : ℝ} (hσ : 0 < σ) :
    Integrable fun k : ℝ =>
      (gaussian1D σ k : ℂ) * cexp ((2 * π * I) * a * k) := by
  have hb : 0 < ((1 / (2 * σ ^ 2) : ℝ) : ℂ).re := by
    simp only [ofReal_re]; positivity
  have hI := integrable_cexp_quadratic hb (c := 2 * π * I * a) (d := 0)
  have hconst := hI.const_mul (1 / (σ * sqrt (2 * π)) : ℂ)
  refine hconst.congr (ae_of_all _ fun k => ?_)
  exact (gaussian1D_char_eq σ a k).symm

/-- Characteristic function of a centred 1D Gaussian
`∫ s(k) exp(2π i a k) dk = exp(-2π² σ² a²)`. -/
theorem charFun_source1D {σ a : ℝ} (hσ : 0 < σ) :
    ∫ k : ℝ, (gaussian1D σ k : ℂ) * cexp ((2 * π * I) * a * k)
      = cexp (-(2 : ℂ) * π ^ 2 * σ ^ 2 * a ^ 2) := by
  have hb : (-((1 / (2 * σ ^ 2) : ℝ) : ℂ)).re < 0 := by
    simp only [neg_re, ofReal_re]
    exact neg_lt_zero.mpr (by positivity)
  have hinter :
      (fun k : ℝ => (gaussian1D σ k : ℂ) * cexp ((2 * π * I) * a * k))
        = fun k : ℝ =>
          (1 / (σ * sqrt (2 * π)) : ℂ) *
            cexp (-((1 / (2 * σ ^ 2) : ℝ) : ℂ) * (k : ℂ) ^ 2 + (2 * π * I * a) * k + 0) := by
    funext k
    exact gaussian1D_char_eq σ a k
  rw [hinter, integral_const_mul, integral_cexp_quadratic hb]
  have hdiv : π / (1 / (2 * σ ^ 2)) = 2 * π * σ ^ 2 := by field_simp
  have hsqrt : sqrt (2 * π * σ ^ 2) = σ * sqrt (2 * π) := by
    rw [show (2 * π * σ ^ 2) = σ ^ 2 * (2 * π) by ring,
      sqrt_mul (sq_nonneg σ), sqrt_sq hσ.le]
  have hpos : 0 ≤ π / (1 / (2 * σ ^ 2)) := by positivity
  have hnegB : -(-((1 / (2 * σ ^ 2) : ℝ) : ℂ)) = ((1 / (2 * σ ^ 2) : ℝ) : ℂ) := by
    simp
  have hpref :
      (1 / (σ * sqrt (2 * π)) : ℂ) *
          (((π / (1 / (2 * σ ^ 2)) : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) = 1 := by
    rw [← ofReal_cpow hpos, ← sqrt_eq_rpow, hdiv, hsqrt, ofReal_mul]
    field_simp [ofReal_ne_zero.mpr (ne_of_gt hσ),
      ofReal_ne_zero.mpr (sqrt_pos.mpr (by positivity)).ne']
  have hpow :
      (π / ((1 / (2 * σ ^ 2) : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
        = ((π / (1 / (2 * σ ^ 2)) : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [← ofReal_div, h12]
  have hexp :
      cexp (0 - (2 * π * I * a) ^ 2 / (4 * (-((1 / (2 * σ ^ 2) : ℝ) : ℂ))))
        = cexp (-(2 : ℂ) * π ^ 2 * σ ^ 2 * a ^ 2) := by
    congr 1
    have hb0 : ((1 / (2 * σ ^ 2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    ring_nf
    simp [I_sq]
    field_simp [hb0]
  rw [hnegB, hpow]
  rw [← mul_assoc, hpref, one_mul]
  convert hexp using 2

/-- 2D isotropic characteristic function, by iterating the 1D result. -/
theorem charFun_source2D {σ ax ay : ℝ} (hσ : 0 < σ) :
    ∫ kx : ℝ, ∫ ky : ℝ,
        (gaussian2D σ (kx, ky) : ℂ) *
          cexp ((2 * π * I) * (ax * kx + ay * ky))
      = cexp (-(2 : ℂ) * π ^ 2 * σ ^ 2 * (ax ^ 2 + ay ^ 2)) := by
  have hsplit : ∀ kx ky : ℝ,
      cexp ((2 * π * I) * (ax * kx + ay * ky))
        = cexp ((2 * π * I) * ax * kx) * cexp ((2 * π * I) * ay * ky) := by
    intro kx ky
    rw [← Complex.exp_add]
    congr 1
    ring
  have hpoint : ∀ kx ky,
      (gaussian2D σ (kx, ky) : ℂ) * cexp ((2 * π * I) * (ax * kx + ay * ky))
        = ((gaussian1D σ kx : ℂ) * cexp ((2 * π * I) * ax * kx)) *
          ((gaussian1D σ ky : ℂ) * cexp ((2 * π * I) * ay * ky)) := by
    intro kx ky
    simp only [gaussian2D]
    rw [ofReal_mul, hsplit kx ky]
    ring
  simp_rw [hpoint]
  have hinner : ∀ kx,
      (∫ ky : ℝ,
          ((gaussian1D σ kx : ℂ) * cexp ((2 * π * I) * ax * kx)) *
            ((gaussian1D σ ky : ℂ) * cexp ((2 * π * I) * ay * ky)))
        = ((gaussian1D σ kx : ℂ) * cexp ((2 * π * I) * ax * kx)) *
            ∫ ky : ℝ, (gaussian1D σ ky : ℂ) * cexp ((2 * π * I) * ay * ky) := by
    intro kx
    exact integral_const_mul _ _
  simp_rw [hinner, integral_mul_const, charFun_source1D hσ]
  rw [← Complex.exp_add]
  congr 1
  ring
