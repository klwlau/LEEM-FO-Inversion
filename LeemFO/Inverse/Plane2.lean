/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Forward.Kernel2
import LeemFO.Inverse.Homotopy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-!
# Two-dimensional stage-1 map

Odd vector embeddings `qmap2 : G → ℝ²`, disk truncation on `‖q‖`, and the
vacuum Gauss–Newton glue for `R_FO2`. Stage 1 remains Fourier-diagonal
Tikhonov on the radial CTF slice; stage 2 is the mixed Born homotopy of
`Homotopy.lean` applied to the 2D bilinear kernel.
-/

open Complex Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

variable {κ : Type*}

noncomputable section

namespace LEEM

variable (p : LEEM)

/-- 2D CTF-slice multipliers `h_k(q) = R_FO2(q, 0, Δz_k)`. -/
def sliceH2 (Δz : κ → ℝ) (q : EuclideanSpace ℝ (Fin 2)) : κ → ℂ :=
  fun k => p.R_FO2 q 0 (Δz k)

/-- Conjugate-branch multipliers `g_k(q) = R_FO2(0, -q, Δz_k)`. -/
def sliceG2 (Δz : κ → ℝ) (q : EuclideanSpace ℝ (Fin 2)) : κ → ℂ :=
  fun k => p.R_FO2 0 (-q) (Δz k)

theorem sliceH2_eq_sliceH (Δz : κ → ℝ) (q : EuclideanSpace ℝ (Fin 2)) :
    p.sliceH2 Δz q = p.sliceH Δz ‖q‖ := by
  funext k
  exact p.R_FO2_eq_R_FO_axis q (Δz k)

theorem sliceG2_eq_sliceG (Δz : κ → ℝ) (q : EuclideanSpace ℝ (Fin 2)) :
    p.sliceG2 Δz q = p.sliceG Δz ‖q‖ := by
  funext k
  rw [sliceG2, sliceG, p.R_FO2_eq_R_FO_conj_axis]

/-- Conjugate branch is the Hermitian partner of the 2D CTF slice. -/
theorem sliceG2_eq_conj_sliceH2 (hσ : 0 ≤ p.sigmaE) (Δz : κ → ℝ)
    (q : EuclideanSpace ℝ (Fin 2)) (k : κ) :
    p.sliceG2 Δz q k = conj (p.sliceH2 Δz (-q) k) := by
  simpa [sliceG2, sliceH2] using
    (p.R_FO2_hermitian (q := -q) (q' := 0) (Δz := Δz k) hσ).symm

variable [Fintype κ]

/-- Stage 1 on a 2D frequency: disk truncation, then the vacuum `2×2` solve. -/
def stage1Pair2 (α : ℝ) (Δz : κ → ℝ)
    (y : κ → EuclideanSpace ℝ (Fin 2) → ℂ)
    (q : EuclideanSpace ℝ (Fin 2)) : ℂ × ℂ :=
  if p.qAp < ‖q‖ then (0, 0)
  else tikhonovXhat2 α (p.sliceH2 Δz q) (p.sliceG2 Δz q) (fun k => y k q)

theorem stage1Pair2_eq_tikhonovXhat2 (α : ℝ) (Δz : κ → ℝ)
    (y : κ → EuclideanSpace ℝ (Fin 2) → ℂ)
    (q : EuclideanSpace ℝ (Fin 2)) :
    p.stage1Pair2 α Δz y q
      = tikhonovXhat2 α (p.sliceH2 Δz q) (p.sliceG2 Δz q)
          (fun k => y k q) := by
  unfold stage1Pair2
  by_cases h : p.qAp < ‖q‖
  · rw [if_pos h]
    have hh : ∀ k, p.sliceH2 Δz q k = 0 := fun k =>
      p.R_FO2_eq_zero_of_outside (Or.inl h)
    have hg : ∀ k, p.sliceG2 Δz q k = 0 := fun k =>
      p.R_FO2_eq_zero_of_outside (Or.inr (by simpa using h))
    have hru : tikhonov2Rhs (p.sliceH2 Δz q) (fun k => y k q) = 0 := by
      simp [tikhonov2Rhs, hh]
    have hrv : tikhonov2Rhs (p.sliceG2 Δz q) (fun k => y k q) = 0 := by
      simp [tikhonov2Rhs, hg]
    simp [tikhonovXhat2, tikhonov2FromRhs, hru, hrv]
  · rw [if_neg h]

theorem stage1Pair2_outside {α : ℝ} (Δz : κ → ℝ)
    (y : κ → EuclideanSpace ℝ (Fin 2) → ℂ)
    {q : EuclideanSpace ℝ (Fin 2)} (h : p.qAp < ‖q‖) :
    p.stage1Pair2 α Δz y q = (0, 0) := by
  simp [stage1Pair2, h]

theorem stage1Pair2_unique {α : ℝ} (hα : 0 < α) (Δz : κ → ℝ)
    (y : κ → EuclideanSpace ℝ (Fin 2) → ℂ)
    (q : EuclideanSpace ℝ (Fin 2)) {u v : ℂ}
    (hmin : ∀ u' v',
      tikhonovJ2 α (p.sliceH2 Δz q) (p.sliceG2 Δz q) (fun k => y k q) u v
        ≤ tikhonovJ2 α (p.sliceH2 Δz q) (p.sliceG2 Δz q)
            (fun k => y k q) u' v') :
    (u, v) = p.stage1Pair2 α Δz y q := by
  rw [p.stage1Pair2_eq_tikhonovXhat2]
  exact tikhonov2_unique hα (p.sliceH2 Δz q) (p.sliceG2 Δz q)
    (fun k => y k q) hmin

end LEEM

end

noncomputable section

open scoped RealInnerProductSpace

/-- Odd 2D frequency embedding: `qmap2(-ξ) = -qmap2 ξ`, hence `qmap2 0 = 0`. -/
lemma qmap2_zero {G : Type*} [AddGroup G]
    (qmap : G → EuclideanSpace ℝ (Fin 2))
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) : qmap 0 = 0 := by
  have h : qmap 0 = -qmap 0 := by simpa using hq 0
  have hadd : qmap 0 + qmap 0 = 0 := by
    nth_rw 1 [h]
    exact neg_add_cancel (qmap 0)
  have h2 : (2 : ℝ) • qmap 0 = 0 := by
    simpa [two_smul] using hadd
  rcases (smul_eq_zero.mp h2) with h20 | h0
  · exact (two_ne_zero h20).elim
  · exact h0

theorem ihatJac_vacuum_slice2 {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] {κ : Type*} (p : LEEM) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : κ → ℝ) (δ : G → ℂ) (ξ : G)
    (k : κ) :
    ihatJac (fun a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) vacuum δ ξ
      = p.sliceH2 Δz (qmap ξ) k * δ ξ
        + p.sliceG2 Δz (qmap ξ) k * conj (δ (-ξ)) := by
  rw [ihatJac_vacuum]
  simp [LEEM.sliceH2, LEEM.sliceG2, qmap2_zero qmap hq, hq]

theorem vacuumGN_eq_stage1Pair2 {κ : Type*} [Fintype κ]
    {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (p : LEEM) (α : ℝ) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : κ → ℝ)
    (y : κ → EuclideanSpace ℝ (Fin 2) → ℂ) (δ : G → ℂ) (ξ : G)
    (hy : ∀ k, y k (qmap ξ)
      = ihatJac (fun a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) vacuum δ ξ) :
    p.stage1Pair2 α Δz y (qmap ξ)
      = tikhonovXhat2 α (p.sliceH2 Δz (qmap ξ)) (p.sliceG2 Δz (qmap ξ))
          (fun k => p.sliceH2 Δz (qmap ξ) k * δ ξ
            + p.sliceG2 Δz (qmap ξ) k * conj (δ (-ξ))) := by
  rw [p.stage1Pair2_eq_tikhonovXhat2]
  congr 1
  funext k
  rw [hy, ihatJac_vacuum_slice2 p qmap hq]

theorem ihatJac_vacuum_R_FO2_dc {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] (p : LEEM) (h0 : 0 ≤ p.qAp)
    (qmap : G → EuclideanSpace ℝ (Fin 2))
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : ℝ) (δ : G → ℂ) :
    ihatJac (fun a b => p.R_FO2 (qmap a) (qmap b) Δz) vacuum δ 0
      = 2 * (δ 0).re := by
  refine ihatJac_vacuum_dc_real ?_ δ
  rw [qmap2_zero qmap hq, p.R_FO2_dc h0]

end
