/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Forward.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Gradient of `χ_S` and first-order Taylor expansion in illumination tilt `k`
-/

open Complex Real InnerProductSpace
open scoped InnerProductSpace Topology

namespace LEEM

variable (p : LEEM)

/-- `∂_q χ_S = C₃ λ³ q³ + C₅ λ⁵ q⁵ + Δz λ q`. -/
theorem hasDerivAt_chiS (Δz q : ℝ) :
    HasDerivAt (p.chiS · Δz)
      (p.C3 * p.lam ^ 3 * q ^ 3 + p.C5 * p.lam ^ 5 * q ^ 5 + Δz * p.lam * q) q := by
  have hf :
      (p.chiS · Δz)
        = (fun y => (1 / 4 : ℝ) * p.C3 * p.lam ^ 3 * y ^ 4)
          + (fun y => (1 / 6 : ℝ) * p.C5 * p.lam ^ 5 * y ^ 6)
          + (fun y => (1 / 2 : ℝ) * Δz * p.lam * y ^ 2) := by
    funext x
    simp [chiS, Pi.add_apply]
  rw [hf]
  refine
    ((((hasDerivAt_pow (n := 4) q).const_mul ((1 / 4 : ℝ) * p.C3 * p.lam ^ 3)).add
          ((hasDerivAt_pow (n := 6) q).const_mul ((1 / 6 : ℝ) * p.C5 * p.lam ^ 5))).add
        ((hasDerivAt_pow (n := 2) q).const_mul ((1 / 2 : ℝ) * Δz * p.lam))).congr_deriv
      ?_
  ring

theorem deriv_chiS (Δz q : ℝ) :
    deriv (p.chiS · Δz) q
      = p.C3 * p.lam ^ 3 * q ^ 3 + p.C5 * p.lam ^ 5 * q ^ 5 + Δz * p.lam * q :=
  (p.hasDerivAt_chiS Δz q).deriv

theorem aS_eq_deriv_sub (q q' Δz : ℝ) :
    p.aS q q' Δz = deriv (p.chiS · Δz) q - deriv (p.chiS · Δz) q' := by
  simp [aS, p.deriv_chiS]
  ring

/-- First-order Taylor remainder in illumination tilt: paper Eq. (3). -/
theorem chiS_taylor (Δz q : ℝ) :
    (fun k : ℝ => p.chiS (q + k) Δz - p.chiS q Δz
      - k * (p.C3 * p.lam ^ 3 * q ^ 3 + p.C5 * p.lam ^ 5 * q ^ 5 + Δz * p.lam * q))
      =o[𝓝 0] id :=
  (hasDerivAt_iff_isLittleO_nhds_zero.mp (p.hasDerivAt_chiS Δz q))

/-- Exact splitting `χ_C(q,ε) - χ_C(q',ε) = b₁ ε + b₂ ε²`. -/
theorem chiC_sub (hp : p.IsPhysical) (q q' ε : ℝ) :
    p.chiC q ε - p.chiC q' ε = p.b1 q q' * ε + p.b2 q q' * ε ^ 2 := by
  unfold chiC b1 b2 IsPhysical at *
  have hE : p.E ≠ 0 := ne_of_gt hp.2
  field_simp [hE]
  ring

theorem b1_zero_diag (q : ℝ) : p.b1 q q = 0 := by simp [b1]
theorem b2_zero_diag (q : ℝ) : p.b2 q q = 0 := by simp [b2]
theorem aS_zero_diag (q Δz : ℝ) : p.aS q q Δz = 0 := by simp [aS]

/-- AC specialisation of `b₁`. -/
theorem b1_ac (h : p.IsAC) (q q' : ℝ) :
    p.b1 q q' = p.C3C * p.lam ^ 3 / (4 * p.E) * (q ^ 4 - q' ^ 4) := by
  unfold IsAC at h
  simp [b1, h.2]

/-- NAC specialisation: `b₂ = 0`. -/
theorem b2_nac (h : p.IsNAC) (q q' : ℝ) : p.b2 q q' = 0 := by
  unfold IsNAC at h
  simp [b2, h.2.1]

section chiS2

open scoped RealInnerProductSpace

/-- Gradient of `‖q‖²` on Euclidean 2-space. -/
theorem hasGradientAt_normSq (q : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2) (2 • q) q := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hasStrictFDerivAt_norm_sq (F := EuclideanSpace ℝ (Fin 2)) q).hasFDerivAt.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro y
  simp [toDual_apply_apply, two_smul]

/-- `∇χ_S = (C₃ λ³ ‖q‖² + C₅ λ⁵ ‖q‖⁴ + Δz λ) • q`. -/
theorem hasGradientAt_chiS2 (Δz : ℝ) (q : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (p.chiS2 · Δz)
      ((p.C3 * p.lam ^ 3 * ‖q‖ ^ 2 + p.C5 * p.lam ^ 5 * ‖q‖ ^ 4 + Δz * p.lam) • q) q := by
  have hsq : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2)
      (2 • innerSL ℝ q) q :=
    (hasStrictFDerivAt_norm_sq (F := EuclideanSpace ℝ (Fin 2)) q).hasFDerivAt
  have h4 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 4)
      ((2 * ‖q‖ ^ 2) • (2 • innerSL ℝ q)) q := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * ‖q‖ ^ 2) (‖q‖ ^ 2) := by
      simpa using hasDerivAt_pow (n := 2) (‖q‖ ^ 2)
    have hf : (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 4)
        = (fun t : ℝ => t ^ 2) ∘ fun x => ‖x‖ ^ 2 := by
      funext x
      simp [Function.comp_apply]
      ring
    rw [hf]
    exact hpow.comp_hasFDerivAt q hsq
  have h6 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 6)
      ((3 * (‖q‖ ^ 2) ^ 2) • (2 • innerSL ℝ q)) q := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 3) (3 * (‖q‖ ^ 2) ^ 2) (‖q‖ ^ 2) := by
      simpa using hasDerivAt_pow (n := 3) (‖q‖ ^ 2)
    have hf : (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 6)
        = (fun t : ℝ => t ^ 3) ∘ fun x => ‖x‖ ^ 2 := by
      funext x
      simp [Function.comp_apply]
      ring
    rw [hf]
    exact hpow.comp_hasFDerivAt q hsq
  have hf :
      (fun x : EuclideanSpace ℝ (Fin 2) => p.chiS2 x Δz)
        = ((1 / 4 : ℝ) * p.C3 * p.lam ^ 3) • (fun x => ‖x‖ ^ 4)
          + ((1 / 6 : ℝ) * p.C5 * p.lam ^ 5) • (fun x => ‖x‖ ^ 6)
          + ((1 / 2 : ℝ) * Δz * p.lam) • (fun x => ‖x‖ ^ 2) := by
    funext x
    simp [chiS2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf, hasGradientAt_iff_hasFDerivAt]
  refine
    (((h4.const_smul ((1 / 4 : ℝ) * p.C3 * p.lam ^ 3)).add
          (h6.const_smul ((1 / 6 : ℝ) * p.C5 * p.lam ^ 5))).add
        (hsq.const_smul ((1 / 2 : ℝ) * Δz * p.lam))).congr_fderiv
      ?_
  apply ContinuousLinearMap.ext
  intro y
  simp [toDual_apply_apply, smul_smul, two_smul, pow_two]
  ring

end chiS2

end LEEM
