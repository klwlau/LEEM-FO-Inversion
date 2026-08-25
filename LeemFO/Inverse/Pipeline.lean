/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.LinearInverse
import LeemFO.Inverse.Modes
import Mathlib.Tactic.Linarith

/-!
# Fourier-domain inverse pipeline

Stage 1 is per-bin Tikhonov on the CTF slice `R_FO(q,0,Δz)` (scalar or the
vacuum 2×2). Stage 2 is optional: skip when the bilinear remainder of the
linear reconstruction is at a prescribed noise floor. The 1D sinusoid
special case is Jacobi–Anger least squares on `modeSet` (`sinusoidJ`).

No DFT is constructed; inputs are already Fourier bins. Iterative
Gauss–Newton is not encoded.
-/

open Complex Real
open scoped BigOperators ComplexConjugate

variable {κ : Type*}

noncomputable section

namespace LEEM

variable (p : LEEM)

/-- CTF-slice multipliers `h_k(q) = R_FO(q, 0, Δz_k)`. -/
def sliceH (Δz : κ → ℝ) (q : ℝ) : κ → ℂ :=
  fun k => p.R_FO q 0 (Δz k)

/-- Conjugate-branch multipliers `g_k(q) = R_FO(0, -q, Δz_k)`. -/
def sliceG (Δz : κ → ℝ) (q : ℝ) : κ → ℂ :=
  fun k => p.R_FO 0 (-q) (Δz k)

theorem sliceH_eq_zero_of_outside (Δz : κ → ℝ) {q : ℝ} (h : p.qAp < |q|)
    (k : κ) : p.sliceH Δz q k = 0 :=
  p.R_FO_axis_eq_zero_of_outside h

theorem sliceG_eq_zero_of_outside (Δz : κ → ℝ) {q : ℝ} (h : p.qAp < |q|)
    (k : κ) : p.sliceG Δz q k = 0 :=
  p.R_FO_eq_zero_of_outside (Or.inr (by simpa using h))

theorem sliceH_dc (h0 : 0 ≤ p.qAp) (Δz : κ → ℝ) (k : κ) :
    p.sliceH Δz 0 k = 1 :=
  p.R_FO_dc h0

theorem sliceG_dc (h0 : 0 ≤ p.qAp) (Δz : κ → ℝ) (k : κ) :
    p.sliceG Δz 0 k = 1 := by
  simp [sliceG, p.R_FO_dc h0]

/-- Conjugate branch is the Hermitian partner of the CTF slice. -/
theorem sliceG_eq_conj_sliceH (hσ : 0 ≤ p.sigmaE) (Δz : κ → ℝ)
    (q : ℝ) (k : κ) :
    p.sliceG Δz q k = conj (p.sliceH Δz (-q) k) := by
  simpa [sliceG, sliceH] using (p.R_FO_hermitian (q := -q) (q' := 0) hσ).symm

/-- 1D stage-2 cost: Jacobi–Anger least squares on the sampled kernel `rFO`. -/
def stage2Sinusoid (Λ Δz : ℝ) (I : ℝ → ℂ) (xs : Finset ℝ) (φ : ℝ) : ℝ :=
  sinusoidJ (rFO p Λ Δz) p.qAp Λ I xs φ

variable [Fintype κ]

/-- Stage 1, scalar branch: aperture-truncated Tikhonov of one Fourier bin. -/
def stage1Scalar (α : ℝ) (Δz : κ → ℝ) (y : κ → ℝ → ℂ) (q : ℝ) : ℂ :=
  if p.qAp < |q| then 0
  else tikhonovXhat α (p.sliceH Δz q) (fun k => y k q)

/-- Stage 1, vacuum 2×2 branch: pair `(X(q), conj X(-q))`. -/
def stage1Pair (α : ℝ) (Δz : κ → ℝ) (y : κ → ℝ → ℂ) (q : ℝ) : ℂ × ℂ :=
  if p.qAp < |q| then (0, 0)
  else tikhonovXhat2 α (p.sliceH Δz q) (p.sliceG Δz q) (fun k => y k q)

theorem stage1Scalar_eq_tikhonovXhat (α : ℝ) (Δz : κ → ℝ) (y : κ → ℝ → ℂ)
    (q : ℝ) :
    p.stage1Scalar α Δz y q
      = tikhonovXhat α (p.sliceH Δz q) (fun k => y k q) := by
  unfold stage1Scalar
  by_cases h : p.qAp < |q|
  · rw [if_pos h]
    exact (tikhonovXhat_eq_zero_of_h_zero (p.sliceH Δz q) (fun k => y k q)
      fun k => p.sliceH_eq_zero_of_outside Δz h k).symm
  · rw [if_neg h]

theorem stage1Pair_eq_tikhonovXhat2 (α : ℝ) (Δz : κ → ℝ) (y : κ → ℝ → ℂ)
    (q : ℝ) :
    p.stage1Pair α Δz y q
      = tikhonovXhat2 α (p.sliceH Δz q) (p.sliceG Δz q) (fun k => y k q) := by
  unfold stage1Pair
  by_cases h : p.qAp < |q|
  · rw [if_pos h]
    have hh : ∀ k, p.sliceH Δz q k = 0 := fun k =>
      p.sliceH_eq_zero_of_outside Δz h k
    have hg : ∀ k, p.sliceG Δz q k = 0 := fun k =>
      p.sliceG_eq_zero_of_outside Δz h k
    have hru : tikhonov2Rhs (p.sliceH Δz q) (fun k => y k q) = 0 := by
      simp [tikhonov2Rhs, hh]
    have hrv : tikhonov2Rhs (p.sliceG Δz q) (fun k => y k q) = 0 := by
      simp [tikhonov2Rhs, hg]
    simp [tikhonovXhat2, tikhonov2FromRhs, hru, hrv]
  · rw [if_neg h]

theorem stage1Scalar_outside {α : ℝ} (Δz : κ → ℝ) (y : κ → ℝ → ℂ) {q : ℝ}
    (h : p.qAp < |q|) : p.stage1Scalar α Δz y q = 0 := by
  simp [stage1Scalar, h]

/-- Unique minimizer of the scalar bin energy is `stage1Scalar`. -/
theorem stage1Scalar_unique {α : ℝ} (hα : 0 < α) (Δz : κ → ℝ)
    (y : κ → ℝ → ℂ) (q : ℝ) {x : ℂ}
    (hx : ∀ z, tikhonovJ α (p.sliceH Δz q) (fun k => y k q) x
      ≤ tikhonovJ α (p.sliceH Δz q) (fun k => y k q) z) :
    x = p.stage1Scalar α Δz y q := by
  rw [p.stage1Scalar_eq_tikhonovXhat]
  exact tikhonov_unique hα (p.sliceH Δz q) (fun k => y k q) hx

/-- Unique minimizer of the vacuum 2×2 energy is `stage1Pair`. -/
theorem stage1Pair_unique {α : ℝ} (hα : 0 < α) (Δz : κ → ℝ)
    (y : κ → ℝ → ℂ) (q : ℝ) {u v : ℂ}
    (hmin : ∀ u' v', tikhonovJ2 α (p.sliceH Δz q) (p.sliceG Δz q)
        (fun k => y k q) u v
      ≤ tikhonovJ2 α (p.sliceH Δz q) (p.sliceG Δz q) (fun k => y k q) u' v') :
    (u, v) = p.stage1Pair α Δz y q := by
  rw [p.stage1Pair_eq_tikhonovXhat2]
  exact tikhonov2_unique hα (p.sliceH Δz q) (p.sliceG Δz q)
    (fun k => y k q) hmin

theorem stage1Scalar_error_bound {α : ℝ} (hα : 0 ≤ α) (Δz : κ → ℝ)
    {q : ℝ} (xstar : ℂ) (n : κ → ℂ)
    (hD : 0 < tikhonovDenom α (p.sliceH Δz q)) :
    ‖p.stage1Scalar α Δz (fun k _ => p.sliceH Δz q k * xstar + n k) q
        - xstar‖
      ≤ (∑ k, ‖p.sliceH Δz q k‖ * ‖n k‖ + α * ‖xstar‖)
          / tikhonovDenom α (p.sliceH Δz q) := by
  rw [p.stage1Scalar_eq_tikhonovXhat]
  exact tikhonov_error_bound hα (p.sliceH Δz q) xstar n hD

theorem stage1Pair_error {α : ℝ} (Δz : κ → ℝ) {q : ℝ}
    (ustar vstar : ℂ) (n : κ → ℂ)
    (hD : gramDet α (p.sliceH Δz q) (p.sliceG Δz q) ≠ 0) :
    p.stage1Pair α Δz
        (fun k _ =>
          p.sliceH Δz q k * ustar + p.sliceG Δz q k * vstar + n k) q
      = ((tikhonov2FromRhs α (p.sliceH Δz q) (p.sliceG Δz q)
            (tikhonov2Rhs (p.sliceH Δz q) n - (α : ℂ) * ustar)
            (tikhonov2Rhs (p.sliceG Δz q) n - (α : ℂ) * vstar)).1 + ustar,
        (tikhonov2FromRhs α (p.sliceH Δz q) (p.sliceG Δz q)
            (tikhonov2Rhs (p.sliceH Δz q) n - (α : ℂ) * ustar)
            (tikhonov2Rhs (p.sliceG Δz q) n - (α : ℂ) * vstar)).2 + vstar) := by
  rw [p.stage1Pair_eq_tikhonovXhat2]
  exact tikhonov2_error (p.sliceH Δz q) (p.sliceG Δz q) ustar vstar n hD

end LEEM

end

noncomputable section

/-- Odd frequency embedding: `qmap (-ξ) = -qmap ξ`, hence `qmap 0 = 0`. -/
lemma qmap_zero {G : Type*} [AddGroup G] (qmap : G → ℝ)
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) : qmap 0 = 0 := by
  have h := hq 0
  simp at h
  linarith

theorem ihatJac_vacuum_slice {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] {κ : Type*} (p : LEEM) (qmap : G → ℝ)
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : κ → ℝ) (δ : G → ℂ) (ξ : G)
    (k : κ) :
    ihatJac (fun a b => p.R_FO (qmap a) (qmap b) (Δz k)) vacuum δ ξ
      = p.sliceH Δz (qmap ξ) k * δ ξ
        + p.sliceG Δz (qmap ξ) k * conj (δ (-ξ)) := by
  rw [ihatJac_vacuum]
  simp [LEEM.sliceH, LEEM.sliceG, qmap_zero qmap hq, hq]

/-- One vacuum Gauss–Newton residual is the 2×2 CTF-slice model, so the
closed-form step is `stage1Pair`. -/
theorem vacuumGN_eq_stage1Pair {κ : Type*} [Fintype κ]
    {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (p : LEEM) (α : ℝ) (qmap : G → ℝ)
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : κ → ℝ) (y : κ → ℝ → ℂ)
    (δ : G → ℂ) (ξ : G)
    (hy : ∀ k, y k (qmap ξ)
      = ihatJac (fun a b => p.R_FO (qmap a) (qmap b) (Δz k)) vacuum δ ξ) :
    p.stage1Pair α Δz y (qmap ξ)
      = tikhonovXhat2 α (p.sliceH Δz (qmap ξ)) (p.sliceG Δz (qmap ξ))
          (fun k => p.sliceH Δz (qmap ξ) k * δ ξ
            + p.sliceG Δz (qmap ξ) k * conj (δ (-ξ))) := by
  rw [p.stage1Pair_eq_tikhonovXhat2]
  congr 1
  funext k
  rw [hy, ihatJac_vacuum_slice p qmap hq]

theorem ihatJac_vacuum_dc {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] (R : G → G → ℂ) (δ : G → ℂ) :
    ihatJac R vacuum δ 0 = R 0 0 * (δ 0 + conj (δ 0)) := by
  rw [ihatJac_vacuum]
  simp
  ring

theorem ihatJac_vacuum_dc_real {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] {R : G → G → ℂ} (hR : R 0 0 = 1) (δ : G → ℂ) :
    ihatJac R vacuum δ 0 = 2 * (δ 0).re := by
  rw [ihatJac_vacuum_dc, hR, one_mul, Complex.add_conj]
  norm_cast

/-- DC bin of the FO Jacobian is twice the real part (gauge / real DC). -/
theorem ihatJac_vacuum_R_FO_dc {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] (p : LEEM) (h0 : 0 ≤ p.qAp) (qmap : G → ℝ)
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : ℝ) (δ : G → ℂ) :
    ihatJac (fun a b => p.R_FO (qmap a) (qmap b) Δz) vacuum δ 0
      = 2 * (δ 0).re := by
  refine ihatJac_vacuum_dc_real ?_ δ
  rw [qmap_zero qmap hq, p.R_FO_dc h0]

/-- Quadratic remainder dropped by one vacuum Gauss–Newton step. -/
def stage1Remainder {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (R : G → G → ℂ) (δ : G → ℂ) (ξ : G) : ℂ :=
  ihat R δ ξ

/-- Algebraic skip: bilinear remainder is at or below a noise floor `η`. -/
def stage2Skip {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (R : G → G → ℂ) (δ : G → ℂ) (η : ℝ) : Prop :=
  ∀ ξ : G, ‖ihat R δ ξ‖ ≤ η

theorem stage1Remainder_eq_quadratic {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] (R : G → G → ℂ) (δ : G → ℂ) (ξ : G) :
    ihat R (vacuum + δ) ξ - ihat R vacuum ξ - ihatJac R vacuum δ ξ
      = stage1Remainder R δ ξ :=
  ihat_quadratic_remainder R δ ξ

theorem stage2Skip_of_bound {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] (R : G → G → ℂ) (δ : G → ℂ) {η : ℝ}
    (hη : (∑ q : G, ∑ q' : G, ‖R q q'‖) * (∑ q : G, ‖δ q‖) ^ 2 ≤ η) :
    stage2Skip R δ η :=
  fun ξ => (ihat_bound R δ ξ).trans hη

end
