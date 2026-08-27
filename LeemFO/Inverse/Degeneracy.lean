/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Forward.Kernel2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# 2D kernel degeneracy of a through-focal series

Pure defocus with a radial kernel depends on `q` only through `q · ξ`.
Reflection across the `ξ`-axis is therefore invisible. The 2D inner
product in `E_S` is the term that has no 1D analogue.
-/

open Complex Real
open scoped ComplexConjugate RealInnerProductSpace

lemma norm_eq_of_sq_eq {E : Type*} [SeminormedAddCommGroup E] {x y : E}
    (h : ‖x‖ ^ 2 = ‖y‖ ^ 2) : ‖x‖ = ‖y‖ := by
  have hx := congrArg Real.sqrt h
  simpa [Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (norm_nonneg y)] using hx

namespace LEEM

/-- Householder reflection of `q` across the line `ℝ • ξ`. -/
noncomputable def reflectLine (ξ q : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (2 * ⟪q, ξ⟫ / ‖ξ‖ ^ 2) • ξ - q

lemma reflectLine_inner {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0)
    (q : EuclideanSpace ℝ (Fin 2)) :
    ⟪reflectLine ξ q, ξ⟫ = ⟪q, ξ⟫ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ)
  unfold reflectLine
  simp [inner_sub_left, real_inner_smul_left]
  field_simp [hn]
  ring

lemma reflectLine_norm {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0)
    (q : EuclideanSpace ℝ (Fin 2)) :
    ‖reflectLine ξ q‖ = ‖q‖ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ)
  refine norm_eq_of_sq_eq ?_
  unfold reflectLine
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left]
  rw [real_inner_comm q ξ]
  field_simp [hn]
  ring

lemma reflectLine_self {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0) :
    reflectLine ξ ξ = ξ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ)
  unfold reflectLine
  rw [real_inner_self_eq_norm_sq, mul_div_cancel_right₀ (2 : ℝ) hn, two_smul]
  abel

lemma reflectLine_sub {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0)
    (q : EuclideanSpace ℝ (Fin 2)) :
    reflectLine ξ (q - ξ) = reflectLine ξ q - ξ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ)
  unfold reflectLine
  have hinter : ⟪q - ξ, ξ⟫ = ⟪q, ξ⟫ - ‖ξ‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  rw [hinter]
  have hcoeff :
      2 * (⟪q, ξ⟫ - ‖ξ‖ ^ 2) / ‖ξ‖ ^ 2 = 2 * ⟪q, ξ⟫ / ‖ξ‖ ^ 2 - 2 := by
    field_simp [hn]
  rw [hcoeff, sub_smul, two_smul]
  abel

lemma reflectLine_inner_pair {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0)
    (q q' : EuclideanSpace ℝ (Fin 2)) :
    ⟪reflectLine ξ q, reflectLine ξ q'⟫ = ⟪q, q'⟫ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ)
  let c : ℝ := 2 * ⟪q, ξ⟫ / ‖ξ‖ ^ 2
  let c' : ℝ := 2 * ⟪q', ξ⟫ / ‖ξ‖ ^ 2
  have hform : reflectLine ξ q = c • ξ - q := rfl
  have hform' : reflectLine ξ q' = c' • ξ - q' := rfl
  rw [hform, hform', inner_sub_left, inner_sub_right, inner_sub_right]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  change
    c * (c' * ‖ξ‖ ^ 2) - c * ⟪ξ, q'⟫ - (c' * ⟪q, ξ⟫ - ⟪q, q'⟫) = ⟪q, q'⟫
  rw [real_inner_comm q' ξ]
  unfold c c'
  field_simp [hn]
  ring

variable (p : LEEM)

lemma reflectLine_uS {ξ q : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0) (Δz : ℝ) :
    p.uS (reflectLine ξ q) Δz = p.uS q Δz := by
  simp [uS, uS0, reflectLine_norm hξ]

/-- Reflection preserves the tilt vector up to an isometry, hence `|a|`. -/
lemma aS2_reflect {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0)
    (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    ‖p.aS2 (reflectLine ξ q) (reflectLine ξ q') Δz‖
      = ‖p.aS2 q q' Δz‖ := by
  have hq : ‖reflectLine ξ q‖ = ‖q‖ := reflectLine_norm hξ q
  have hq' : ‖reflectLine ξ q'‖ = ‖q'‖ := reflectLine_norm hξ q'
  have hu : p.uS (reflectLine ξ q) Δz = p.uS q Δz := p.reflectLine_uS hξ Δz
  have hu' : p.uS (reflectLine ξ q') Δz = p.uS q' Δz := p.reflectLine_uS hξ Δz
  have hinter := reflectLine_inner_pair hξ q q'
  have hL := p.aS2_normSq (reflectLine ξ q) (reflectLine ξ q') Δz
  have hR := p.aS2_normSq q q' Δz
  have hsq :
      ‖p.aS2 (reflectLine ξ q) (reflectLine ξ q') Δz‖ ^ 2
        = ‖p.aS2 q q' Δz‖ ^ 2 := by
    rw [hL, hR, hq, hq', hu, hu', hinter]
  exact norm_eq_of_sq_eq hsq

/-- Pure-defocus `ω` is invariant under reflection across `ξ`. -/
theorem defocusOmega_reflect {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0)
    (q : EuclideanSpace ℝ (Fin 2)) :
    p.defocusOmega (reflectLine ξ q) (reflectLine ξ q - ξ)
      = p.defocusOmega q (q - ξ) := by
  unfold defocusOmega
  rw [← reflectLine_sub hξ q, reflectLine_norm hξ q, reflectLine_norm hξ (q - ξ)]

/-- Spatial envelope is reflection-invariant. -/
theorem spatialEnvelopeClosed2_reflect {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : ξ ≠ 0) (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.spatialEnvelopeClosed2 (reflectLine ξ q) (reflectLine ξ q') Δz
      = p.spatialEnvelopeClosed2 q q' Δz := by
  unfold spatialEnvelopeClosed2
  rw [p.aS2_reflect hξ]

/-- Two frequencies with the same projection onto `ξ` share the pure-defocus phase. -/
theorem defocusOmega_depends_inner (q₁ q₂ ξ : EuclideanSpace ℝ (Fin 2))
    (h : ⟪q₁, ξ⟫ = ⟪q₂, ξ⟫) :
    p.defocusOmega q₁ (q₁ - ξ) = p.defocusOmega q₂ (q₂ - ξ) := by
  unfold defocusOmega
  have h1 : ‖q₁‖ ^ 2 - ‖q₁ - ξ‖ ^ 2 = 2 * ⟪q₁, ξ⟫ - ‖ξ‖ ^ 2 := by
    rw [norm_sub_sq_real]
    ring
  have h2 : ‖q₂‖ ^ 2 - ‖q₂ - ξ‖ ^ 2 = 2 * ⟪q₂, ξ⟫ - ‖ξ‖ ^ 2 := by
    rw [norm_sub_sq_real]
    ring
  rw [h1, h2, h]

/-- Pure defocus + perfect coherence cannot separate a perpendicular pair. -/
theorem R_FO2_pureDefocus_perp (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (q₁ q₂ ξ : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ)
    (hproj : ⟪q₁, ξ⟫ = ⟪q₂, ξ⟫)
    (hap : p.aperture2 q₁ = p.aperture2 q₂)
    (hap' : p.aperture2 (q₁ - ξ) = p.aperture2 (q₂ - ξ)) :
    p.R_FO2 q₁ (q₁ - ξ) Δz = p.R_FO2 q₂ (q₂ - ξ) Δz := by
  rw [p.R_FO2_pureDefocus_perfect h hC3 hC5,
    p.R_FO2_pureDefocus_perfect h hC3 hC5, hap, hap',
    p.defocusOmega_depends_inner q₁ q₂ ξ hproj]

end LEEM
