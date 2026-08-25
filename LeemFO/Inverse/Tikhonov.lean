/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel

/-!
# Fourier-diagonal Tikhonov (scalar and 2×2 Gram)

Finite-dimensional algebra for one spatial-frequency bin of the linearized
multi-defocus FO/CTF slice. No DFT is constructed.
-/

open Complex
open scoped BigOperators ComplexConjugate

variable {κ : Type*} [Fintype κ]

noncomputable section

/-- Tikhonov energy of a scalar Fourier unknown `x`. -/
def tikhonovJ (α : ℝ) (h y : κ → ℂ) (x : ℂ) : ℝ :=
  (∑ k, ‖h k * x - y k‖ ^ 2) + α * ‖x‖ ^ 2

/-- Gram denominator `α + ∑ |h_k|²`. -/
def tikhonovDenom (α : ℝ) (h : κ → ℂ) : ℝ :=
  α + ∑ k, ‖h k‖ ^ 2

/-- Closed-form scalar Tikhonov estimator. -/
def tikhonovXhat (α : ℝ) (h y : κ → ℂ) : ℂ :=
  (∑ k, conj (h k) * y k) / (tikhonovDenom α h : ℂ)

lemma tikhonovDenom_nonneg {α : ℝ} (hα : 0 ≤ α) (h : κ → ℂ) :
    0 ≤ tikhonovDenom α h :=
  add_nonneg hα (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma tikhonovDenom_pos {α : ℝ} (hα : 0 < α) (h : κ → ℂ) :
    0 < tikhonovDenom α h :=
  add_pos_of_pos_of_nonneg hα (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma tikhonovDenom_pos_of_energy {α : ℝ} (hα : 0 ≤ α) (h : κ → ℂ)
    (hE : 0 < ∑ k, ‖h k‖ ^ 2) : 0 < tikhonovDenom α h :=
  add_pos_of_nonneg_of_pos hα hE

lemma re_mul_conj (z w : ℂ) : (z * conj w).re = (conj z * w).re := by
  simp [mul_re, conj_re, conj_im]

lemma norm_sq_add (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (conj z * w).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, normSq_add]
  simp

lemma conj_mul_self (z : ℂ) : conj z * z = (‖z‖ ^ 2 : ℂ) := by
  rw [mul_comm, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]

/-- Polarization of the scalar energy. -/
lemma tikhonovJ_add (α : ℝ) (h y : κ → ℂ) (x d : ℂ) :
    tikhonovJ α h y (x + d)
      = tikhonovJ α h y x
        + (∑ k, ‖h k * d‖ ^ 2) + α * ‖d‖ ^ 2
        + 2 * ((∑ k, conj (h k * x - y k) * (h k * d))
            + (α : ℂ) * (conj x * d)).re := by
  have hterm (k : κ) :
      ‖h k * (x + d) - y k‖ ^ 2
        = ‖h k * x - y k‖ ^ 2 + ‖h k * d‖ ^ 2
          + 2 * (conj (h k * x - y k) * (h k * d)).re := by
    have : h k * (x + d) - y k = (h k * x - y k) + h k * d := by ring
    rw [this, norm_sq_add]
  have hx : ‖x + d‖ ^ 2 = ‖x‖ ^ 2 + ‖d‖ ^ 2 + 2 * (conj x * d).re :=
    norm_sq_add x d
  have h2sum :
      (∑ k, 2 * (conj (h k * x - y k) * (h k * d)).re)
        = 2 * ∑ k, (conj (h k * x - y k) * (h k * d)).re := by
    rw [← Finset.mul_sum]
  have hre :
      ((∑ k, conj (h k * x - y k) * (h k * d)) + (α : ℂ) * (conj x * d)).re
        = (∑ k, (conj (h k * x - y k) * (h k * d)).re)
          + α * (conj x * d).re := by
    rw [add_re, ← Complex.re_sum, re_ofReal_mul]
  unfold tikhonovJ
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hx, h2sum, hre]
  ring

lemma tikhonovJ_cross_eq_re_normal (α : ℝ) (h y : κ → ℂ) (x d : ℂ) :
    (∑ k, conj (h k * x - y k) * (h k * d)) + (α : ℂ) * (conj x * d)
      = conj ((∑ k, conj (h k) * (h k * x - y k)) + (α : ℂ) * x) * d := by
  have hk (k : κ) :
      conj (h k * x - y k) * (h k * d)
        = conj (conj (h k) * (h k * x - y k)) * d := by
    simp [map_mul, map_sub, mul_assoc, mul_comm]
  have h1 :
      ∑ k, conj (h k * x - y k) * (h k * d)
        = conj (∑ k, conj (h k) * (h k * x - y k)) * d := by
    simp_rw [hk]
    rw [← Finset.sum_mul, ← map_sum]
  have h2 : (α : ℂ) * (conj x * d) = conj ((α : ℂ) * x) * d := by
    simp [map_mul, mul_left_comm, mul_comm]
  rw [h1, h2, ← add_mul, map_add]

lemma tikhonov_normal_eq {α : ℝ} (h y : κ → ℂ)
    (hD : tikhonovDenom α h ≠ 0) :
    (∑ k, conj (h k) * (h k * tikhonovXhat α h y - y k))
      + (α : ℂ) * tikhonovXhat α h y = 0 := by
  set D := tikhonovDenom α h
  set β := ∑ k, conj (h k) * y k
  have hx : tikhonovXhat α h y = β / (D : ℂ) := rfl
  have hD0 : (D : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD
  have hsumh :
      ∑ k, conj (h k) * h k = (∑ k, ‖h k‖ ^ 2 : ℝ) := by
    simp_rw [conj_mul_self]
    simp [ofReal_sum]
  rw [hx]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have h1 :
      ∑ k, conj (h k) * (h k * (β / (D : ℂ)))
        = (∑ k, conj (h k) * h k) * (β / (D : ℂ)) := by
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul]
  rw [h1, hsumh]
  have hDℂ : (D : ℂ) = (α : ℂ) + (∑ k, ‖h k‖ ^ 2 : ℝ) := by
    unfold D tikhonovDenom
    push_cast
    ring
  have hDen : (α : ℂ) + (∑ k, ‖h k‖ ^ 2 : ℝ) ≠ 0 := by
    rwa [← hDℂ]
  rw [hDℂ]
  field_simp [hDen]
  simp only [β]
  ring

lemma tikhonov_quad (α : ℝ) (h : κ → ℂ) (d : ℂ) :
    (∑ k, ‖h k * d‖ ^ 2) + α * ‖d‖ ^ 2 = tikhonovDenom α h * ‖d‖ ^ 2 := by
  have hk (k : κ) : ‖h k * d‖ ^ 2 = ‖h k‖ ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_mul, mul_pow]
  simp_rw [hk]
  rw [← Finset.sum_mul]
  unfold tikhonovDenom
  ring

/-- Completing the square: `J(x) = J(x̂) + D ‖x - x̂‖²`. -/
theorem tikhonovJ_eq_shift {α : ℝ} (h y : κ → ℂ) (x : ℂ)
    (hD : tikhonovDenom α h ≠ 0) :
    tikhonovJ α h y x
      = tikhonovJ α h y (tikhonovXhat α h y)
        + tikhonovDenom α h * ‖x - tikhonovXhat α h y‖ ^ 2 := by
  set xhat := tikhonovXhat α h y
  set d := x - xhat
  have hx : x = xhat + d := by ring
  have hN := tikhonov_normal_eq (α := α) h y hD
  have hcross := tikhonovJ_cross_eq_re_normal α h y xhat d
  rw [hx, tikhonovJ_add, hcross, hN, map_zero, zero_mul, zero_re, mul_zero,
    add_zero, add_assoc, tikhonov_quad]

theorem tikhonovJ_min {α : ℝ} (hα : 0 < α) (h y : κ → ℂ) (x : ℂ) :
    tikhonovJ α h y (tikhonovXhat α h y) ≤ tikhonovJ α h y x := by
  have hD := tikhonovDenom_pos hα h
  rw [tikhonovJ_eq_shift (α := α) h y x hD.ne']
  nlinarith [sq_nonneg (‖x - tikhonovXhat α h y‖ : ℝ)]

theorem tikhonov_unique {α : ℝ} (hα : 0 < α) (h y : κ → ℂ) {x : ℂ}
    (hx : ∀ z, tikhonovJ α h y x ≤ tikhonovJ α h y z) :
    x = tikhonovXhat α h y := by
  have hD := tikhonovDenom_pos hα h
  have heq : tikhonovJ α h y x = tikhonovJ α h y (tikhonovXhat α h y) :=
    le_antisymm (hx _) (tikhonovJ_min hα h y x)
  have hsq : tikhonovDenom α h * ‖x - tikhonovXhat α h y‖ ^ 2 = 0 := by
    have hshift := tikhonovJ_eq_shift (α := α) h y x hD.ne'
    linarith
  have : ‖x - tikhonovXhat α h y‖ = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hsq).resolve_left hD.ne')
  exact eq_of_sub_eq_zero (norm_eq_zero.mp this)

/-- Completing-the-square form used in the theorem list (T1). -/
theorem tikhonovJ_eq_completed {α : ℝ} (h y : κ → ℂ) (x : ℂ)
    (hD : tikhonovDenom α h ≠ 0) :
    tikhonovJ α h y x
      = tikhonovJ α h y (tikhonovXhat α h y)
        + tikhonovDenom α h * ‖x - tikhonovXhat α h y‖ ^ 2 :=
  tikhonovJ_eq_shift (α := α) h y x hD

theorem tikhonov_error {α : ℝ} (h : κ → ℂ) (xstar : ℂ) (n : κ → ℂ)
    (hD : tikhonovDenom α h ≠ 0) :
    tikhonovXhat α h (fun k => h k * xstar + n k) - xstar
      = (∑ k, conj (h k) * n k - (α : ℂ) * xstar)
        / (tikhonovDenom α h : ℂ) := by
  set D := tikhonovDenom α h
  set y := fun k : κ => h k * xstar + n k
  set β := ∑ k, conj (h k) * y k
  have hxhat : tikhonovXhat α h y = β / (D : ℂ) := rfl
  have hβ :
      β = (∑ k, (‖h k‖ ^ 2 : ℂ)) * xstar + ∑ k, conj (h k) * n k := by
    unfold β y
    simp_rw [mul_add, ← mul_assoc, conj_mul_self]
    rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hDsplit : (D : ℂ) * xstar
      = (α : ℂ) * xstar + (∑ k, (‖h k‖ ^ 2 : ℂ)) * xstar := by
    unfold D tikhonovDenom
    push_cast
    ring
  have hD0 : (D : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD
  have hdiv : β / (D : ℂ) - xstar = (β - (D : ℂ) * xstar) / (D : ℂ) := by
    field_simp [hD0]
  rw [hxhat, hdiv, hβ, hDsplit]
  ring

theorem tikhonov_error_bound {α : ℝ} (hα : 0 ≤ α) (h : κ → ℂ) (xstar : ℂ)
    (n : κ → ℂ) (hD : 0 < tikhonovDenom α h) :
    ‖tikhonovXhat α h (fun k => h k * xstar + n k) - xstar‖
      ≤ (∑ k, ‖h k‖ * ‖n k‖ + α * ‖xstar‖) / tikhonovDenom α h := by
  have hD0 : tikhonovDenom α h ≠ 0 := hD.ne'
  rw [tikhonov_error (hD := hD0), norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hD]
  refine div_le_div_of_nonneg_right ?_ hD.le
  have hsum :
      ‖∑ k, conj (h k) * n k‖ ≤ ∑ k, ‖h k‖ * ‖n k‖ := by
    calc
      ‖∑ k, conj (h k) * n k‖ ≤ ∑ k, ‖conj (h k) * n k‖ :=
        norm_sum_le _ _
      _ = ∑ k, ‖h k‖ * ‖n k‖ := by simp
  have hαn : ‖(α : ℂ) * xstar‖ = α * ‖xstar‖ := by
    simp [Complex.norm_real, abs_of_nonneg hα]
  calc
    ‖∑ k, conj (h k) * n k - (α : ℂ) * xstar‖
        ≤ ‖∑ k, conj (h k) * n k‖ + ‖(α : ℂ) * xstar‖ :=
          norm_sub_le _ _
    _ ≤ ∑ k, ‖h k‖ * ‖n k‖ + α * ‖xstar‖ := by
          rw [hαn]; exact add_le_add hsum le_rfl

/-- Triangle bound is attained: one measurement, `h = 1`, `n = 1`, `x⋆ = -1`, `α = 1`. -/
theorem tikhonov_error_bound_sharp :
    let h : Fin 1 → ℂ := fun _ => 1
    let n : Fin 1 → ℂ := fun _ => 1
    let xstar : ℂ := -1
    let α : ℝ := 1
    ‖tikhonovXhat α h (fun k => h k * xstar + n k) - xstar‖
      = (∑ k, ‖h k‖ * ‖n k‖ + α * ‖xstar‖) / tikhonovDenom α h := by
  simp [tikhonovXhat, tikhonovDenom]

lemma tikhonovXhat_eq_zero_of_h_zero {α : ℝ}
    (h y : κ → ℂ) (hh : ∀ k, h k = 0) :
    tikhonovXhat α h y = 0 := by
  simp [tikhonovXhat, tikhonovDenom, hh]

lemma tikhonovJ_of_h_zero {α : ℝ} (h y : κ → ℂ) (x : ℂ)
    (hh : ∀ k, h k = 0) :
    tikhonovJ α h y x = (∑ k, ‖y k‖ ^ 2) + α * ‖x‖ ^ 2 := by
  simp [tikhonovJ, hh]

/-- One complex linear measurement of two complex unknowns has a kernel. -/
theorem one_measurement_not_injective (h g : ℂ) :
    ∃ u v : ℂ, (u ≠ 0 ∨ v ≠ 0) ∧ h * u + g * v = 0 := by
  by_cases hh : h = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hh]⟩
  · exact ⟨g, -h, Or.inr (neg_ne_zero.mpr hh), by ring⟩

/-! ## 2×2 Gram of the vacuum Jacobian -/

def tikhonovJ2 (α : ℝ) (h g y : κ → ℂ) (u v : ℂ) : ℝ :=
  (∑ k, ‖h k * u + g k * v - y k‖ ^ 2) + α * (‖u‖ ^ 2 + ‖v‖ ^ 2)

def gramA (α : ℝ) (h : κ → ℂ) : ℝ := α + ∑ k, ‖h k‖ ^ 2

def gramB (h g : κ → ℂ) : ℂ := ∑ k, conj (h k) * g k

def gramDet (α : ℝ) (h g : κ → ℂ) : ℝ :=
  gramA α h * gramA α g - ‖gramB h g‖ ^ 2

lemma abs_sum_conj_mul_le (h g : κ → ℂ) :
    ‖∑ k, conj (h k) * g k‖ ≤ ∑ k, ‖h k‖ * ‖g k‖ := by
  calc
    ‖∑ k, conj (h k) * g k‖ ≤ ∑ k, ‖conj (h k) * g k‖ :=
      norm_sum_le _ _
    _ = ∑ k, ‖h k‖ * ‖g k‖ := by simp

lemma gramB_norm_sq_le (h g : κ → ℂ) :
    ‖gramB h g‖ ^ 2 ≤ (∑ k, ‖h k‖ ^ 2) * (∑ k, ‖g k‖ ^ 2) := by
  unfold gramB
  have h1 := abs_sum_conj_mul_le h g
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ)
    (fun k => ‖h k‖) (fun k => ‖g k‖)
  have hineq :
      ‖∑ k, conj (h k) * g k‖ ^ 2 ≤ (∑ k, ‖h k‖ * ‖g k‖) ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg _) h1
    simpa [pow_two] using this
  exact hineq.trans h2

theorem gramDet_pos {α : ℝ} (hα : 0 < α) (h g : κ → ℂ) :
    0 < gramDet α h g := by
  have hCS := gramB_norm_sq_le h g
  have hEh : 0 ≤ ∑ k, ‖h k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEg : 0 ≤ ∑ k, ‖g k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp :
      (α + ∑ k, ‖h k‖ ^ 2) * (α + ∑ k, ‖g k‖ ^ 2)
          - (∑ k, ‖h k‖ ^ 2) * (∑ k, ‖g k‖ ^ 2)
        = α * α + α * (∑ k, ‖h k‖ ^ 2) + α * (∑ k, ‖g k‖ ^ 2) := by
    ring
  have hα2 : 0 < α * α := mul_pos hα hα
  have hαh : 0 ≤ α * ∑ k, ‖h k‖ ^ 2 := mul_nonneg hα.le hEh
  have hαg : 0 ≤ α * ∑ k, ‖g k‖ ^ 2 := mul_nonneg hα.le hEg
  unfold gramDet gramA
  linarith

lemma gramA_eq_tikhonovDenom (α : ℝ) (h : κ → ℂ) :
    gramA α h = tikhonovDenom α h := rfl

lemma gramA_pos {α : ℝ} (hα : 0 < α) (h : κ → ℂ) : 0 < gramA α h :=
  tikhonovDenom_pos hα h

lemma gramDet_ne_zero {α : ℝ} (hα : 0 < α) (h g : κ → ℂ) :
    gramDet α h g ≠ 0 :=
  (gramDet_pos hα h g).ne'

/-- Right-hand side of the vacuum 2×2 normal equations. -/
def tikhonov2Rhs (h y : κ → ℂ) : ℂ :=
  ∑ k, conj (h k) * y k

/-- Cramer solution of the regularized 2×2 Gram system. -/
def tikhonov2FromRhs (α : ℝ) (h g : κ → ℂ) (ru rv : ℂ) : ℂ × ℂ :=
  (((gramA α g : ℂ) * ru - gramB h g * rv) / (gramDet α h g : ℂ),
    ((gramA α h : ℂ) * rv - conj (gramB h g) * ru) / (gramDet α h g : ℂ))

/-- Closed-form 2×2 Tikhonov estimator `(û, v̂)` of `(X(q), conj X(-q))`. -/
def tikhonovXhat2 (α : ℝ) (h g y : κ → ℂ) : ℂ × ℂ :=
  tikhonov2FromRhs α h g (tikhonov2Rhs h y) (tikhonov2Rhs g y)

lemma tikhonov2FromRhs_u (α : ℝ) (h g : κ → ℂ) (ru rv : ℂ) :
    (tikhonov2FromRhs α h g ru rv).1
      = ((gramA α g : ℂ) * ru - gramB h g * rv) / (gramDet α h g : ℂ) :=
  rfl

lemma tikhonov2FromRhs_v (α : ℝ) (h g : κ → ℂ) (ru rv : ℂ) :
    (tikhonov2FromRhs α h g ru rv).2
      = ((gramA α h : ℂ) * rv - conj (gramB h g) * ru) / (gramDet α h g : ℂ) :=
  rfl

lemma gramB_mul_conj (h g : κ → ℂ) :
    gramB h g * conj (gramB h g) = (‖gramB h g‖ ^ 2 : ℂ) := by
  rw [mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]

lemma conj_gramB_mul (h g : κ → ℂ) :
    conj (gramB h g) * gramB h g = (‖gramB h g‖ ^ 2 : ℂ) := by
  rw [mul_comm, gramB_mul_conj]

lemma gramDet_coe (α : ℝ) (h g : κ → ℂ) :
    (gramDet α h g : ℂ)
      = (gramA α h : ℂ) * (gramA α g : ℂ) - (‖gramB h g‖ ^ 2 : ℂ) := by
  unfold gramDet
  push_cast
  ring

/-- The Cramer formula solves the regularized Gram system. -/
theorem tikhonov2_solves {α : ℝ} (h g : κ → ℂ) (ru rv : ℂ)
    (hD : gramDet α h g ≠ 0) :
    (gramA α h : ℂ) * (tikhonov2FromRhs α h g ru rv).1
        + gramB h g * (tikhonov2FromRhs α h g ru rv).2 = ru
      ∧ conj (gramB h g) * (tikhonov2FromRhs α h g ru rv).1
        + (gramA α g : ℂ) * (tikhonov2FromRhs α h g ru rv).2 = rv := by
  have hD0 : (gramDet α h g : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD
  constructor
  · rw [tikhonov2FromRhs_u, tikhonov2FromRhs_v]
    field_simp [hD0]
    rw [gramDet_coe, ← gramB_mul_conj]
    ring
  · rw [tikhonov2FromRhs_u, tikhonov2FromRhs_v]
    field_simp [hD0]
    rw [gramDet_coe, ← conj_gramB_mul]
    ring

lemma tikhonov2NormalU_eq (α : ℝ) (h g y : κ → ℂ) (u v : ℂ) :
    (∑ k, conj (h k) * (h k * u + g k * v - y k)) + (α : ℂ) * u
      = (gramA α h : ℂ) * u + gramB h g * v - tikhonov2Rhs h y := by
  have hsumh :
      ∑ k, conj (h k) * h k = (∑ k, ‖h k‖ ^ 2 : ℝ) := by
    simp_rw [conj_mul_self]
    simp [ofReal_sum]
  unfold gramA gramB tikhonov2Rhs
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 :
      ∑ k, conj (h k) * (h k * u) = (∑ k, conj (h k) * h k) * u := by
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul]
  have h2 :
      ∑ k, conj (h k) * (g k * v) = (∑ k, conj (h k) * g k) * v := by
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul]
  rw [h1, h2, hsumh]
  push_cast
  ring

lemma tikhonov2NormalV_eq (α : ℝ) (h g y : κ → ℂ) (u v : ℂ) :
    (∑ k, conj (g k) * (h k * u + g k * v - y k)) + (α : ℂ) * v
      = conj (gramB h g) * u + (gramA α g : ℂ) * v - tikhonov2Rhs g y := by
  have hsumg :
      ∑ k, conj (g k) * g k = (∑ k, ‖g k‖ ^ 2 : ℝ) := by
    simp_rw [conj_mul_self]
    simp [ofReal_sum]
  have hBg : ∑ k, conj (g k) * h k = conj (gramB h g) := by
    unfold gramB
    simp [map_sum, map_mul, mul_comm]
  unfold gramA tikhonov2Rhs
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 :
      ∑ k, conj (g k) * (h k * u) = (∑ k, conj (g k) * h k) * u := by
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul]
  have h2 :
      ∑ k, conj (g k) * (g k * v) = (∑ k, conj (g k) * g k) * v := by
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul]
  rw [h1, h2, hsumg, hBg]
  push_cast
  ring

theorem tikhonov2_normal_eq {α : ℝ} (h g y : κ → ℂ)
    (hD : gramDet α h g ≠ 0) :
    (∑ k, conj (h k) * (h k * (tikhonovXhat2 α h g y).1
        + g k * (tikhonovXhat2 α h g y).2 - y k))
        + (α : ℂ) * (tikhonovXhat2 α h g y).1 = 0
      ∧ (∑ k, conj (g k) * (h k * (tikhonovXhat2 α h g y).1
        + g k * (tikhonovXhat2 α h g y).2 - y k))
        + (α : ℂ) * (tikhonovXhat2 α h g y).2 = 0 := by
  have hsol := tikhonov2_solves h g (tikhonov2Rhs h y) (tikhonov2Rhs g y) hD
  constructor
  · rw [tikhonov2NormalU_eq, tikhonovXhat2, hsol.1]
    ring
  · rw [tikhonov2NormalV_eq, tikhonovXhat2, hsol.2]
    ring

lemma tikhonovJ2_add (α : ℝ) (h g y : κ → ℂ) (u v du dv : ℂ) :
    tikhonovJ2 α h g y (u + du) (v + dv)
      = tikhonovJ2 α h g y u v
        + (∑ k, ‖h k * du + g k * dv‖ ^ 2) + α * (‖du‖ ^ 2 + ‖dv‖ ^ 2)
        + 2 * ((∑ k, conj (h k * u + g k * v - y k) * (h k * du + g k * dv))
            + (α : ℂ) * (conj u * du + conj v * dv)).re := by
  have hterm (k : κ) :
      ‖h k * (u + du) + g k * (v + dv) - y k‖ ^ 2
        = ‖h k * u + g k * v - y k‖ ^ 2 + ‖h k * du + g k * dv‖ ^ 2
          + 2 * (conj (h k * u + g k * v - y k) * (h k * du + g k * dv)).re := by
    have : h k * (u + du) + g k * (v + dv) - y k
        = (h k * u + g k * v - y k) + (h k * du + g k * dv) := by ring
    rw [this, norm_sq_add]
  have hu : ‖u + du‖ ^ 2 = ‖u‖ ^ 2 + ‖du‖ ^ 2 + 2 * (conj u * du).re :=
    norm_sq_add u du
  have hv : ‖v + dv‖ ^ 2 = ‖v‖ ^ 2 + ‖dv‖ ^ 2 + 2 * (conj v * dv).re :=
    norm_sq_add v dv
  have h2sum :
      (∑ k, 2 * (conj (h k * u + g k * v - y k) * (h k * du + g k * dv)).re)
        = 2 * ∑ k, (conj (h k * u + g k * v - y k) * (h k * du + g k * dv)).re := by
    rw [← Finset.mul_sum]
  have hre :
      ((∑ k, conj (h k * u + g k * v - y k) * (h k * du + g k * dv))
          + (α : ℂ) * (conj u * du + conj v * dv)).re
        = (∑ k, (conj (h k * u + g k * v - y k) * (h k * du + g k * dv)).re)
          + α * (conj u * du + conj v * dv).re := by
    rw [add_re, ← Complex.re_sum, re_ofReal_mul]
  unfold tikhonovJ2
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hu, hv, h2sum, hre]
  have hre2 :
      (conj u * du + conj v * dv).re = (conj u * du).re + (conj v * dv).re :=
    add_re _ _
  rw [hre2]
  ring

lemma tikhonovJ2_cross_eq_re_normal (α : ℝ) (h g y : κ → ℂ) (u v du dv : ℂ) :
    (∑ k, conj (h k * u + g k * v - y k) * (h k * du + g k * dv))
      + (α : ℂ) * (conj u * du + conj v * dv)
      = conj ((∑ k, conj (h k) * (h k * u + g k * v - y k)) + (α : ℂ) * u) * du
        + conj ((∑ k, conj (g k) * (h k * u + g k * v - y k)) + (α : ℂ) * v)
          * dv := by
  have hkU (k : κ) :
      conj (h k * u + g k * v - y k) * (h k * du)
        = conj (conj (h k) * (h k * u + g k * v - y k)) * du := by
    simp [map_mul, map_add, map_sub, mul_assoc]
    ring
  have hkV (k : κ) :
      conj (h k * u + g k * v - y k) * (g k * dv)
        = conj (conj (g k) * (h k * u + g k * v - y k)) * dv := by
    simp [map_mul, map_add, map_sub, mul_assoc]
    ring
  have h1 :
      ∑ k, conj (h k * u + g k * v - y k) * (h k * du + g k * dv)
        = conj (∑ k, conj (h k) * (h k * u + g k * v - y k)) * du
          + conj (∑ k, conj (g k) * (h k * u + g k * v - y k)) * dv := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp_rw [hkU, hkV]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← map_sum, ← map_sum]
  have h2 :
      (α : ℂ) * (conj u * du + conj v * dv)
        = conj ((α : ℂ) * u) * du + conj ((α : ℂ) * v) * dv := by
    simp [map_mul, mul_add, mul_left_comm, mul_comm]
  rw [h1, h2]
  simp [map_add, add_mul]
  ac_rfl

theorem tikhonovJ2_eq_shift {α : ℝ} (h g y : κ → ℂ) (u v : ℂ)
    (hD : gramDet α h g ≠ 0) :
    tikhonovJ2 α h g y u v
      = tikhonovJ2 α h g y (tikhonovXhat2 α h g y).1 (tikhonovXhat2 α h g y).2
        + (∑ k, ‖h k * (u - (tikhonovXhat2 α h g y).1)
            + g k * (v - (tikhonovXhat2 α h g y).2)‖ ^ 2)
        + α * (‖u - (tikhonovXhat2 α h g y).1‖ ^ 2
            + ‖v - (tikhonovXhat2 α h g y).2‖ ^ 2) := by
  set uv := tikhonovXhat2 α h g y
  set du := u - uv.1
  set dv := v - uv.2
  have hu : u = uv.1 + du := by ring
  have hv : v = uv.2 + dv := by ring
  have hN := tikhonov2_normal_eq (α := α) h g y hD
  have hcross := tikhonovJ2_cross_eq_re_normal α h g y uv.1 uv.2 du dv
  rw [hu, hv, tikhonovJ2_add, hcross, hN.1, hN.2, map_zero, zero_mul, zero_mul,
    zero_add, zero_re, mul_zero, add_zero]

theorem tikhonovJ2_min {α : ℝ} (hα : 0 < α) (h g y : κ → ℂ) (u v : ℂ) :
    tikhonovJ2 α h g y (tikhonovXhat2 α h g y).1 (tikhonovXhat2 α h g y).2
      ≤ tikhonovJ2 α h g y u v := by
  have hD := gramDet_ne_zero hα h g
  rw [tikhonovJ2_eq_shift (α := α) h g y u v hD]
  have h1 : 0 ≤ ∑ k, ‖h k * (u - (tikhonovXhat2 α h g y).1)
      + g k * (v - (tikhonovXhat2 α h g y).2)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ α * (‖u - (tikhonovXhat2 α h g y).1‖ ^ 2
      + ‖v - (tikhonovXhat2 α h g y).2‖ ^ 2) :=
    mul_nonneg hα.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith

theorem tikhonov2_unique {α : ℝ} (hα : 0 < α) (h g y : κ → ℂ) {u v : ℂ}
    (hx : ∀ u' v', tikhonovJ2 α h g y u v ≤ tikhonovJ2 α h g y u' v') :
    (u, v) = tikhonovXhat2 α h g y := by
  have hD := gramDet_ne_zero hα h g
  have hmin := tikhonovJ2_min hα h g y u v
  have heq :
      tikhonovJ2 α h g y u v
        = tikhonovJ2 α h g y (tikhonovXhat2 α h g y).1
            (tikhonovXhat2 α h g y).2 :=
    le_antisymm (hx _ _) hmin
  have hshift := tikhonovJ2_eq_shift (α := α) h g y u v hD
  have hαrem :
      α * (‖u - (tikhonovXhat2 α h g y).1‖ ^ 2
          + ‖v - (tikhonovXhat2 α h g y).2‖ ^ 2) = 0 := by
    have hsum : 0 ≤ ∑ k, ‖h k * (u - (tikhonovXhat2 α h g y).1)
        + g k * (v - (tikhonovXhat2 α h g y).2)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hquad : 0 ≤ α * (‖u - (tikhonovXhat2 α h g y).1‖ ^ 2
        + ‖v - (tikhonovXhat2 α h g y).2‖ ^ 2) :=
      mul_nonneg hα.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
    linarith
  have hnorm : ‖u - (tikhonovXhat2 α h g y).1‖ ^ 2
      + ‖v - (tikhonovXhat2 α h g y).2‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hαrem).resolve_left hα.ne'
  have hu : ‖u - (tikhonovXhat2 α h g y).1‖ = 0 := by
    nlinarith [sq_nonneg (‖v - (tikhonovXhat2 α h g y).2‖ : ℝ)]
  have hv : ‖v - (tikhonovXhat2 α h g y).2‖ = 0 := by
    nlinarith [sq_nonneg (‖u - (tikhonovXhat2 α h g y).1‖ : ℝ)]
  apply Prod.ext
  · exact eq_of_sub_eq_zero (norm_eq_zero.mp hu)
  · exact eq_of_sub_eq_zero (norm_eq_zero.mp hv)

theorem tikhonov2_error {α : ℝ} (h g : κ → ℂ) (ustar vstar : ℂ) (n : κ → ℂ)
    (hD : gramDet α h g ≠ 0) :
    tikhonovXhat2 α h g (fun k => h k * ustar + g k * vstar + n k)
      = ( (tikhonov2FromRhs α h g
            (tikhonov2Rhs h n - (α : ℂ) * ustar)
            (tikhonov2Rhs g n - (α : ℂ) * vstar)).1 + ustar
        , (tikhonov2FromRhs α h g
            (tikhonov2Rhs h n - (α : ℂ) * ustar)
            (tikhonov2Rhs g n - (α : ℂ) * vstar)).2 + vstar ) := by
  set y := fun k : κ => h k * ustar + g k * vstar + n k
  set uv := tikhonovXhat2 α h g y
  set err :=
    tikhonov2FromRhs α h g (tikhonov2Rhs h n - (α : ℂ) * ustar)
      (tikhonov2Rhs g n - (α : ℂ) * vstar)
  have hsol := tikhonov2_solves h g (tikhonov2Rhs h y) (tikhonov2Rhs g y) hD
  have herr :=
    tikhonov2_solves h g (tikhonov2Rhs h n - (α : ℂ) * ustar)
      (tikhonov2Rhs g n - (α : ℂ) * vstar) hD
  have hru :
      tikhonov2Rhs h y
        = (gramA α h : ℂ) * ustar + gramB h g * vstar
            - (α : ℂ) * ustar + tikhonov2Rhs h n := by
    unfold y tikhonov2Rhs gramA gramB
    simp_rw [mul_add, ← mul_assoc, conj_mul_self]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_mul]
    have hsumh : ∑ k, (‖h k‖ ^ 2 : ℂ) * ustar = (∑ k, ‖h k‖ ^ 2 : ℝ) * ustar := by
      simp [ofReal_sum, Finset.sum_mul]
    rw [hsumh]
    push_cast
    ring
  have hrv :
      tikhonov2Rhs g y
        = conj (gramB h g) * ustar + (gramA α g : ℂ) * vstar
            - (α : ℂ) * vstar + tikhonov2Rhs g n := by
    unfold y tikhonov2Rhs gramA
    have hBg : ∑ k, conj (g k) * h k = conj (gramB h g) := by
      unfold gramB
      simp [map_sum, map_mul, mul_comm]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : ∑ k, conj (g k) * (h k * ustar) = conj (gramB h g) * ustar := by
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, hBg]
    have h2 : ∑ k, conj (g k) * (g k * vstar) = (∑ k, ‖g k‖ ^ 2 : ℝ) * vstar := by
      simp_rw [← mul_assoc, conj_mul_self]
      simp [ofReal_sum, Finset.sum_mul]
    rw [h1, h2]
    push_cast
    ring
  have hlinu :
      (gramA α h : ℂ) * (err.1 + ustar) + gramB h g * (err.2 + vstar)
        = tikhonov2Rhs h y := by
    calc
      (gramA α h : ℂ) * (err.1 + ustar) + gramB h g * (err.2 + vstar)
          = ((gramA α h : ℂ) * err.1 + gramB h g * err.2)
              + ((gramA α h : ℂ) * ustar + gramB h g * vstar) := by ring
      _ = (tikhonov2Rhs h n - (α : ℂ) * ustar)
            + ((gramA α h : ℂ) * ustar + gramB h g * vstar) := by
            rw [herr.1]
      _ = tikhonov2Rhs h y := by
            rw [hru]
            ring
  have hlinv :
      conj (gramB h g) * (err.1 + ustar) + (gramA α g : ℂ) * (err.2 + vstar)
        = tikhonov2Rhs g y := by
    calc
      conj (gramB h g) * (err.1 + ustar) + (gramA α g : ℂ) * (err.2 + vstar)
          = (conj (gramB h g) * err.1 + (gramA α g : ℂ) * err.2)
              + (conj (gramB h g) * ustar + (gramA α g : ℂ) * vstar) := by
            ring
      _ = (tikhonov2Rhs g n - (α : ℂ) * vstar)
            + (conj (gramB h g) * ustar + (gramA α g : ℂ) * vstar) := by
            rw [herr.2]
      _ = tikhonov2Rhs g y := by
            rw [hrv]
            ring
  have hD0 : (gramDet α h g : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD
  have hu' : (gramA α h : ℂ) * uv.1 + gramB h g * uv.2 = tikhonov2Rhs h y := by
    simpa [uv, tikhonovXhat2] using hsol.1
  have hv' : conj (gramB h g) * uv.1 + (gramA α g : ℂ) * uv.2 = tikhonov2Rhs g y := by
    simpa [uv, tikhonovXhat2] using hsol.2
  have hkeru :
      (gramA α h : ℂ) * (err.1 + ustar - uv.1) + gramB h g * (err.2 + vstar - uv.2)
        = 0 := by
    linear_combination hlinu - hu'
  have hkerv :
      conj (gramB h g) * (err.1 + ustar - uv.1)
        + (gramA α g : ℂ) * (err.2 + vstar - uv.2) = 0 := by
    linear_combination hlinv - hv'
  have hdu :
      (gramDet α h g : ℂ) * (err.1 + ustar - uv.1) = 0 := by
    have hexpand :
        (gramDet α h g : ℂ) * (err.1 + ustar - uv.1)
          = (gramA α g : ℂ) * ((gramA α h : ℂ) * (err.1 + ustar - uv.1)
              + gramB h g * (err.2 + vstar - uv.2))
            - gramB h g * (conj (gramB h g) * (err.1 + ustar - uv.1)
              + (gramA α g : ℂ) * (err.2 + vstar - uv.2)) := by
      rw [gramDet_coe, ← gramB_mul_conj]
      ring
    rw [hexpand, hkeru, hkerv]
    ring
  have hdv :
      (gramDet α h g : ℂ) * (err.2 + vstar - uv.2) = 0 := by
    have hexpand :
        (gramDet α h g : ℂ) * (err.2 + vstar - uv.2)
          = (gramA α h : ℂ) * (conj (gramB h g) * (err.1 + ustar - uv.1)
              + (gramA α g : ℂ) * (err.2 + vstar - uv.2))
            - conj (gramB h g) * ((gramA α h : ℂ) * (err.1 + ustar - uv.1)
              + gramB h g * (err.2 + vstar - uv.2)) := by
      rw [gramDet_coe, ← conj_gramB_mul]
      ring
    rw [hexpand, hkeru, hkerv]
    ring
  have hu0 : err.1 + ustar - uv.1 = 0 :=
    (mul_eq_zero.mp hdu).resolve_left hD0
  have hv0 : err.2 + vstar - uv.2 = 0 :=
    (mul_eq_zero.mp hdv).resolve_left hD0
  apply Prod.ext
  · exact (eq_of_sub_eq_zero hu0).symm
  · exact (eq_of_sub_eq_zero hv0).symm

/-! ## Arithmetic cost model (no FFT existence theorem) -/

def dftCost (N : ℕ) : ℕ := N * Nat.log2 N

def binSolveCost (K : ℕ) : ℕ := 8 * K + 4

def reconstructCost (K N : ℕ) : ℕ :=
  K * dftCost N + N * binSolveCost K + dftCost N

def denseApplyCost (K N : ℕ) : ℕ := K * N * N

lemma reconstructCost_formula (K N : ℕ) :
    reconstructCost K N = (K + 1) * N * N.log2 + N * (8 * K + 4) := by
  simp [reconstructCost, dftCost, binSolveCost]
  ring

lemma one_le_log2 {N : ℕ} (hN : 2 ≤ N) : 1 ≤ N.log2 :=
  (Nat.le_log2 (by omega)).mpr hN

/-- Modelled cost is `O(K N log N)`; the constant `14` is tight at `K = 1`, `N = 2`. -/
theorem reconstructCost_le {K N : ℕ} (hK : 1 ≤ K) (hN : 2 ≤ N) :
    reconstructCost K N ≤ 14 * K * N * N.log2 := by
  rw [reconstructCost_formula]
  have hL : 1 ≤ N.log2 := one_le_log2 hN
  have hKL : 1 ≤ K * N.log2 := Nat.mul_le_mul hK hL
  have hlead : (K + 1) * N * N.log2 ≤ 2 * K * N * N.log2 := by
    have : K + 1 ≤ 2 * K := by omega
    have := Nat.mul_le_mul_right (N * N.log2) this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hbin : N * (8 * K + 4) ≤ 12 * K * N * N.log2 := by
    have h8 : 8 * K ≤ 8 * K * N.log2 := Nat.le_mul_of_pos_right (8 * K) hL
    have h4 : 4 ≤ 4 * K * N.log2 := by
      calc
        4 ≤ 4 * (K * N.log2) := Nat.le_mul_of_pos_right 4 hKL
        _ = 4 * K * N.log2 := by ring
    have hsum : 8 * K + 4 ≤ 12 * K * N.log2 := by
      have : 8 * K * N.log2 + 4 * K * N.log2 = 12 * K * N.log2 := by ring
      linarith
    have := Nat.mul_le_mul_left N hsum
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  calc
    (K + 1) * N * N.log2 + N * (8 * K + 4)
        ≤ 2 * K * N * N.log2 + 12 * K * N * N.log2 :=
          Nat.add_le_add hlead hbin
    _ = 14 * K * N * N.log2 := by ring

lemma log2_128 : Nat.log2 128 = 7 := by
  rw [Nat.log2_def, if_pos (by decide : 2 ≤ 128)]
  rw [Nat.log2_def, if_pos (by decide : 2 ≤ 64)]
  rw [Nat.log2_def, if_pos (by decide : 2 ≤ 32)]
  rw [Nat.log2_def, if_pos (by decide : 2 ≤ 16)]
  rw [Nat.log2_def, if_pos (by decide : 2 ≤ 8)]
  rw [Nat.log2_def, if_pos (by decide : 2 ≤ 4)]
  rw [Nat.log2_def, if_pos (by decide : 2 ≤ 2)]
  rw [Nat.log2_def, if_neg (by decide : ¬2 ≤ 1)]

lemma reconstructCost_128 (K : ℕ) :
    reconstructCost K 128 = 1920 * K + 1408 := by
  rw [reconstructCost_formula, log2_128]
  ring

theorem reconstructCost_lt_dense_128 {K : ℕ} (hK : 1 ≤ K) :
    reconstructCost K 128 < denseApplyCost K 128 := by
  rw [reconstructCost_128, denseApplyCost]
  have hpow : K * 128 * 128 = 16384 * K := by ring
  rw [hpow]
  have : 1408 < 14464 * K :=
    lt_of_lt_of_le (by decide : 1408 < 14464)
      (Nat.le_mul_of_pos_right 14464 hK)
  omega

theorem exists_grid_diagonal_cheaper {K : ℕ} (hK : 1 ≤ K) :
    ∃ N, 128 ≤ N ∧ reconstructCost K N < denseApplyCost K N :=
  ⟨128, le_rfl, reconstructCost_lt_dense_128 hK⟩

end
