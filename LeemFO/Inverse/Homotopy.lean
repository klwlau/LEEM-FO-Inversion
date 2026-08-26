/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.Pipeline
import LeemFO.Inverse.LowRank
import Mathlib.Tactic.Abel

/-!
# Homotopy / Born inverse for large-phase bilinear FO

Bilinear FO is exactly quadratic: there is no cubic remainder. The real
ray `vac + t • δ` interpolates the vacuum image (`t = 0`) and the full
FO image (`t = 1`). The remainder-weighted Born model interpolates the
vacuum linearization (`bornModel` at `t = 0`, stage 1) and full FO
(`t = 1`). Picard / Born iteration applies the Fourier-diagonal `2×2`
solve to a remainder-corrected residual; a damped mix with schedules
`t, damp` is the large-`φ` 2D estimator.

Iterative numerical convergence is not encoded. Uniqueness of the
nonlinear inverse is false (`ihat_gauge`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Complex Real
open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

noncomputable section

lemma ihat_smul (R : G → G → ℂ) (t : ℂ) (Ψ : G → ℂ) (ξ : G) :
    ihat R (fun q => t * Ψ q) ξ = t * conj t * ihat R Ψ ξ := by
  unfold ihat
  calc (∑ q : G, (t * Ψ q) * R q (q - ξ) * conj (t * Ψ (q - ξ)))
      = ∑ q : G, (t * Ψ q) * R q (q - ξ) * (conj t * conj (Ψ (q - ξ))) := by
        simp [map_mul]
    _ = ∑ q : G, (t * conj t) * (Ψ q * R q (q - ξ) * conj (Ψ (q - ξ))) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = t * conj t * ∑ q : G, Ψ q * R q (q - ξ) * conj (Ψ (q - ξ)) := by
        simp [← Finset.mul_sum]

lemma ihatJac_smul_real (R : G → G → ℂ) (t : ℝ) (x0 δ : G → ℂ) (ξ : G) :
    ihatJac R x0 (fun q => (t : ℂ) * δ q) ξ
      = (t : ℂ) * ihatJac R x0 δ ξ := by
  unfold ihatJac
  have h1 (q : G) :
      x0 q * R q (q - ξ) * conj ((t : ℂ) * δ (q - ξ))
        = (t : ℂ) * (x0 q * R q (q - ξ) * conj (δ (q - ξ))) := by
    simp [map_mul, conj_ofReal]
    ring
  have h2 (q : G) :
      ((t : ℂ) * δ q) * R q (q - ξ) * conj (x0 (q - ξ))
        = (t : ℂ) * (δ q * R q (q - ξ) * conj (x0 (q - ξ))) := by ring
  simp_rw [h1, h2]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add]

lemma ihatJac_comm (R : G → G → ℂ) (x0 δ : G → ℂ) (ξ : G) :
    ihatJac R x0 δ ξ = ihatJac R δ x0 ξ := by
  unfold ihatJac
  ac_rfl

lemma ihatJac_self (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) :
    ihatJac R Ψ Ψ ξ = 2 * ihat R Ψ ξ := by
  unfold ihatJac ihat
  simp [two_mul]

lemma ihatJac_add_left (R : G → G → ℂ) (x0 x1 δ : G → ℂ) (ξ : G) :
    ihatJac R (x0 + x1) δ ξ = ihatJac R x0 δ ξ + ihatJac R x1 δ ξ := by
  unfold ihatJac
  simp [add_mul, mul_add, map_add, Finset.sum_add_distrib]
  ac_rfl

lemma ihatJac_sub_right (R : G → G → ℂ) (x0 δ1 δ2 : G → ℂ) (ξ : G) :
    ihatJac R x0 (δ1 - δ2) ξ = ihatJac R x0 δ1 ξ - ihatJac R x0 δ2 ξ := by
  unfold ihatJac
  simp [Pi.sub_apply, sub_mul, mul_sub, map_sub, Finset.sum_sub_distrib]
  abel

/-- Real homotopy of bilinear FO: `t = 0` vacuum, `t = 1` full object. -/
theorem ihat_homotopy (R : G → G → ℂ) (δ : G → ℂ) (ξ : G) (t : ℝ) :
    ihat R (vacuum + fun q => (t : ℂ) * δ q) ξ
      = ihat R vacuum ξ
        + t * ihatJac R vacuum δ ξ
        + t ^ 2 * ihat R δ ξ := by
  rw [ihat_add, ihatJac_smul_real, ihat_smul]
  simp only [conj_ofReal]
  have ht : (t : ℂ) * (t : ℂ) = (t ^ 2 : ℂ) := by simp [sq]
  rw [ht]

theorem ihat_homotopy_at (R : G → G → ℂ) (x0 δ : G → ℂ) (ξ : G) (t : ℝ) :
    ihat R (x0 + fun q => (t : ℂ) * δ q) ξ
      = ihat R x0 ξ + t * ihatJac R x0 δ ξ + t ^ 2 * ihat R δ ξ := by
  rw [ihat_add, ihatJac_smul_real, ihat_smul]
  simp only [conj_ofReal]
  have ht : (t : ℂ) * (t : ℂ) = (t ^ 2 : ℂ) := by simp [sq]
  rw [ht]

theorem ihat_sub (R : G → G → ℂ) (Ψ1 Ψ2 : G → ℂ) (ξ : G) :
    ihat R Ψ1 ξ
      = ihat R Ψ2 ξ + ihatJac R Ψ2 (Ψ1 - Ψ2) ξ + ihat R (Ψ1 - Ψ2) ξ := by
  simpa [add_sub_cancel] using ihat_add R Ψ2 (Ψ1 - Ψ2) ξ

/-- Polarization: `I(Ψ₁) - I(Ψ₂)` is the Jacobian at the midpoint sum. -/
theorem ihat_polarization (R : G → G → ℂ) (Ψ1 Ψ2 : G → ℂ) (ξ : G) :
    ihatJac R (Ψ1 + Ψ2) (Ψ1 - Ψ2) ξ
      = 2 * (ihat R Ψ1 ξ - ihat R Ψ2 ξ) := by
  rw [ihatJac_add_left, ihatJac_sub_right, ihatJac_sub_right, ihatJac_self,
    ihatJac_self, ihatJac_comm (x0 := Ψ2) (δ := Ψ1)]
  ring

/-- Remainder-weighted forward model of a fixed increment `δ`. -/
def bornModel (R : G → G → ℂ) (t : ℝ) (δ : G → ℂ) (ξ : G) : ℂ :=
  ihat R vacuum ξ + ihatJac R vacuum δ ξ + t * ihat R δ ξ

theorem bornModel_t0 (R : G → G → ℂ) (δ : G → ℂ) (ξ : G) :
    bornModel R 0 δ ξ = ihat R vacuum ξ + ihatJac R vacuum δ ξ := by
  simp [bornModel]

theorem bornModel_t1 (R : G → G → ℂ) (δ : G → ℂ) (ξ : G) :
    bornModel R 1 δ ξ = ihat R (vacuum + δ) ξ := by
  simp [bornModel, ihat_add]

theorem bornModel_convex (R : G → G → ℂ) (t : ℝ) (δ : G → ℂ) (ξ : G) :
    bornModel R t δ ξ
      = (1 - t) * (ihat R vacuum ξ + ihatJac R vacuum δ ξ)
        + t * ihat R (vacuum + δ) ξ := by
  unfold bornModel
  rw [ihat_add]
  ring

/-- Distinct homotopy weights disagree by exactly the bilinear remainder. -/
theorem bornModel_sub (R : G → G → ℂ) (t₁ t₂ : ℝ) (δ : G → ℂ) (ξ : G) :
    bornModel R t₁ δ ξ - bornModel R t₂ δ ξ
      = ((t₁ - t₂ : ℝ) : ℂ) * ihat R δ ξ := by
  simp [bornModel]
  ring

/-- Quiet-bin bias: occupied remainder makes `t = 1` disagree with stage-1. -/
theorem bornModel_t1_ne_t0 {R : G → G → ℂ} {δ : G → ℂ} {ξ : G}
    (h : ihat R δ ξ ≠ 0) :
    bornModel R 1 δ ξ ≠ bornModel R 0 δ ξ := by
  intro heq
  have hdiff := bornModel_sub R 1 0 δ ξ
  simp only [sub_zero, ofReal_one, one_mul] at hdiff
  have hzero : bornModel R 1 δ ξ - bornModel R 0 δ ξ = 0 := by
    rw [heq, sub_self]
  exact h (hdiff ▸ hzero)

/-- Loud / occupied remainder: `t = 0` ignores the exact FO image. -/
theorem bornModel_t0_ne_full {R : G → G → ℂ} {δ : G → ℂ} {ξ : G}
    (h : ihat R δ ξ ≠ 0) :
    bornModel R 0 δ ξ ≠ ihat R (vacuum + δ) ξ := by
  simpa [bornModel_t1] using (bornModel_t1_ne_t0 h).symm

/-- Exact line residual: bilinear FO along `x0 + s • d` is quadratic in `s`. -/
def lineResidual (R : G → G → ℂ) (y : G → ℂ) (x0 d : G → ℂ) (s : ℝ)
    (ξ : G) : ℂ :=
  y ξ - ihat R x0 ξ - (s : ℂ) * ihatJac R x0 d ξ
    - (s : ℂ) ^ 2 * ihat R d ξ

theorem lineResidual_eq (R : G → G → ℂ) (y x0 d : G → ℂ) (s : ℝ) (ξ : G) :
    y ξ - ihat R (x0 + fun q => (s : ℂ) * d q) ξ
      = lineResidual R y x0 d s ξ := by
  rw [ihat_homotopy_at]
  simp [lineResidual]
  ring

/-- TIE / Fresnel multiplier (not the FO vacuum Jacobian). -/
def tieMultiplier (lam Δz q : ℝ) : ℂ :=
  2 * π * I * Δz * lam * q ^ 2

theorem tieMultiplier_ne_zero {lam Δz q : ℝ}
    (hlam : lam ≠ 0) (hΔz : Δz ≠ 0) (hq : q ≠ 0) :
    tieMultiplier lam Δz q ≠ 0 := by
  unfold tieMultiplier
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΔ : (Δz : ℂ) ≠ 0 := ofReal_ne_zero.mpr hΔz
  have hlamC : (lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlam
  have hq2 : ((q : ℂ) ^ 2) ≠ 0 := by
    rw [← ofReal_pow]
    exact ofReal_ne_zero.mpr (pow_ne_zero 2 hq)
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero) hΔ) hlamC)
    hq2

/-- Outside the aperture FO is blind while a TIE multiplier is not. -/
theorem R_FO_ne_tie_outside (p : LEEM) {q Δz : ℝ}
    (h : p.qAp < |q|) (hlam : p.lam ≠ 0) (hΔz : Δz ≠ 0) (hq : q ≠ 0) :
    p.R_FO q 0 Δz = 0 ∧ tieMultiplier p.lam Δz q ≠ 0 :=
  ⟨p.R_FO_axis_eq_zero_of_outside h, tieMultiplier_ne_zero hlam hΔz hq⟩

end

variable {κ : Type*} [Fintype κ]

noncomputable section

/-- Linear contrast: measured bin minus the vacuum image. -/
def yLin (R : κ → G → G → ℂ) (y : κ → G → ℂ) (ξ : G) : κ → ℂ :=
  fun k => y k ξ - ihat (R k) vacuum ξ

/-- Born right-hand side: linear contrast minus homotopy-weighted remainder. -/
def bornRhs (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t : ℝ) (δ : G → ℂ)
    (ξ : G) : κ → ℂ :=
  fun k => yLin R y ξ k - (t : ℂ) * ihat (R k) δ ξ

/-- `t = 0` recovers the stage-1 linear contrast (ignores bilinear remainder). -/
theorem bornRhs_t0 (R : κ → G → G → ℂ) (y : κ → G → ℂ) (δ : G → ℂ) (ξ : G) :
    bornRhs R y 0 δ ξ = yLin R y ξ := by
  funext k
  simp [bornRhs]

/-- Distinct weights shift the Born RHS by exactly the weighted remainder. -/
theorem bornRhs_sub (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t₁ t₂ : ℝ)
    (δ : G → ℂ) (ξ : G) (k : κ) :
    bornRhs R y t₁ δ ξ k - bornRhs R y t₂ δ ξ k
      = ((t₂ - t₁ : ℝ) : ℂ) * ihat (R k) δ ξ := by
  simp [bornRhs]
  ring

/-- Quiet-bin bias: forcing `t = 1` changes the RHS whenever any defocus
remainder is occupied (even below a noise floor `η`). -/
theorem bornRhs_t1_ne_t0 {R : κ → G → G → ℂ} {y : κ → G → ℂ} {δ : G → ℂ}
    {ξ : G} {k : κ} (h : ihat (R k) δ ξ ≠ 0) :
    bornRhs R y 1 δ ξ ≠ bornRhs R y 0 δ ξ := by
  intro heq
  have : yLin R y ξ k - ihat (R k) δ ξ = yLin R y ξ k := by
    have hpt := congrArg (fun f : κ → ℂ => f k) heq
    simpa [bornRhs] using hpt
  exact h (sub_eq_self.mp this)

/-- Loud bin: stage-1 (`t = 0`) drops a remainder larger than `η`. -/
theorem bornRhs_t0_ignores_loud {R : κ → G → G → ℂ} {y : κ → G → ℂ}
    {δ : G → ℂ} {ξ : G} {k : κ} {η : ℝ}
    (hloud : η < ‖ihat (R k) δ ξ‖) :
    bornRhs R y 0 δ ξ k = yLin R y ξ k ∧
      bornRhs R y 1 δ ξ k = yLin R y ξ k - ihat (R k) δ ξ ∧
      η < ‖bornRhs R y 0 δ ξ k - bornRhs R y 1 δ ξ k‖ := by
  refine ⟨by simp [bornRhs], by simp [bornRhs], ?_⟩
  have hdiff := bornRhs_sub R y 0 1 δ ξ k
  simpa [hdiff, sub_zero, ofReal_one, one_mul] using hloud

def bornHomotopyPair (α : ℝ) (h g : κ → ℂ) (R : κ → G → G → ℂ)
    (y : κ → G → ℂ) (t : ℝ) (δ : G → ℂ) (ξ : G) : ℂ × ℂ :=
  tikhonovXhat2 α h g (bornRhs R y t δ ξ)

theorem bornHomotopyPair_t0 (α : ℝ) (h g : κ → ℂ) (R : κ → G → G → ℂ)
    (y : κ → G → ℂ) (δ : G → ℂ) (ξ : G) :
    bornHomotopyPair α h g R y 0 δ ξ
      = tikhonovXhat2 α h g (yLin R y ξ) := by
  simp [bornHomotopyPair, bornRhs_t0]

lemma tikhonov2Rhs_sub (h y₁ y₂ : κ → ℂ) :
    tikhonov2Rhs h (y₁ - y₂) = tikhonov2Rhs h y₁ - tikhonov2Rhs h y₂ := by
  simp [tikhonov2Rhs, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma tikhonov2FromRhs_sub (α : ℝ) (h g : κ → ℂ) (ru₁ rv₁ ru₂ rv₂ : ℂ) :
    tikhonov2FromRhs α h g (ru₁ - ru₂) (rv₁ - rv₂)
      = ((tikhonov2FromRhs α h g ru₁ rv₁).1
          - (tikhonov2FromRhs α h g ru₂ rv₂).1,
        (tikhonov2FromRhs α h g ru₁ rv₁).2
          - (tikhonov2FromRhs α h g ru₂ rv₂).2) := by
  apply Prod.ext
  · simp [tikhonov2FromRhs, sub_div]
    ring
  · simp [tikhonov2FromRhs, sub_div]
    ring

lemma tikhonovXhat2_sub (α : ℝ) (h g : κ → ℂ) (y₁ y₂ : κ → ℂ) :
    tikhonovXhat2 α h g (y₁ - y₂)
      = ((tikhonovXhat2 α h g y₁).1 - (tikhonovXhat2 α h g y₂).1,
        (tikhonovXhat2 α h g y₁).2 - (tikhonovXhat2 α h g y₂).2) := by
  simp [tikhonovXhat2, tikhonov2FromRhs_sub, tikhonov2Rhs_sub]

/-- At a Born fixed point the vacuum-Jacobian normal equations hold for the
nonlinear residual (FO-faithful up to the `2×2` projection and `α`-bias). -/
theorem born_fixed_point_normal {α : ℝ} (h g : κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (δ : G → ℂ) (ξ : G)
    (hD : gramDet α h g ≠ 0)
    (hh : ∀ k, h k = R k ξ 0) (hg : ∀ k, g k = R k 0 (-ξ))
    (hfix : (δ ξ, conj (δ (-ξ)))
      = tikhonovXhat2 α h g (bornRhs R y 1 δ ξ)) :
    (∑ k, conj (h k) *
        (ihat (R k) (vacuum + δ) ξ - y k ξ)) + (α : ℂ) * δ ξ = 0 ∧
      (∑ k, conj (g k) *
        (ihat (R k) (vacuum + δ) ξ - y k ξ))
        + (α : ℂ) * conj (δ (-ξ)) = 0 := by
  have hN := tikhonov2_normal_eq (α := α) h g (bornRhs R y 1 δ ξ) hD
  have hu :
      (tikhonovXhat2 α h g (bornRhs R y 1 δ ξ)).1 = δ ξ :=
    (congrArg Prod.fst hfix).symm
  have hv :
      (tikhonovXhat2 α h g (bornRhs R y 1 δ ξ)).2 = conj (δ (-ξ)) :=
    (congrArg Prod.snd hfix).symm
  rw [hu, hv] at hN
  have hjac (k : κ) :
      h k * δ ξ + g k * conj (δ (-ξ)) = ihatJac (R k) vacuum δ ξ := by
    rw [ihatJac_vacuum, hh k, hg k]
  have hterm (k : κ) :
      h k * δ ξ + g k * conj (δ (-ξ)) - bornRhs R y 1 δ ξ k
        = ihat (R k) (vacuum + δ) ξ - y k ξ := by
    unfold bornRhs yLin
    rw [hjac]
    simp [ihat_add]
    ring
  simp_rw [hterm] at hN
  exact hN

/-- Nonlinear least-squares energy of a through-focal stack. -/
def nlsJ (α : ℝ) (R : κ → G → G → ℂ) (y : κ → G → ℂ) (Ψ : G → ℂ) : ℝ :=
  (∑ k, ∑ ξ, ‖ihat (R k) Ψ ξ - y k ξ‖ ^ 2) + α * ∑ q, ‖Ψ q‖ ^ 2

theorem nlsJ_vacuum_expand (α : ℝ) (R : κ → G → G → ℂ) (y : κ → G → ℂ)
    (δ : G → ℂ) :
    nlsJ α R y (vacuum + δ)
      = (∑ k, ∑ ξ,
          ‖ihat (R k) vacuum ξ + ihatJac (R k) vacuum δ ξ
            + ihat (R k) δ ξ - y k ξ‖ ^ 2)
        + α * ∑ q, ‖vacuum q + δ q‖ ^ 2 := by
  simp [nlsJ, ihat_add]

theorem nlsJfid_line (R : κ → G → G → ℂ) (y : κ → G → ℂ)
    (x0 d : G → ℂ) (s : ℝ) :
    (∑ k, ∑ ξ,
        ‖ihat (R k) (x0 + fun q => (s : ℂ) * d q) ξ - y k ξ‖ ^ 2)
      = ∑ k, ∑ ξ, ‖lineResidual (R k) (y k) x0 d s ξ‖ ^ 2 := by
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ξ _ => ?_
  have h := lineResidual_eq (R k) (y k) x0 d s ξ
  have : ihat (R k) (x0 + fun q => (s : ℂ) * d q) ξ - y k ξ
      = -lineResidual (R k) (y k) x0 d s ξ := by
    rw [← neg_sub, h]
  rw [this, norm_neg]

/-- One damped homotopy-Born update of a vacuum `2×2` pair. -/
def mixedBinStep (α : ℝ) (h g : κ → ℂ) (rhsLin quad : κ → ℂ)
    (t damp : ℝ) (uv : ℂ × ℂ) : ℂ × ℂ :=
  let tgt := tikhonovXhat2 α h g (fun k => rhsLin k - (t : ℂ) * quad k)
  (uv.1 + (damp : ℂ) * (tgt.1 - uv.1), uv.2 + (damp : ℂ) * (tgt.2 - uv.2))

theorem mixedBinStep_init (α : ℝ) (h g rhsLin quad : κ → ℂ) (uv : ℂ × ℂ) :
    mixedBinStep α h g rhsLin quad 0 1 uv = tikhonovXhat2 α h g rhsLin := by
  simp [mixedBinStep]

theorem mixedBinStep_damp1 (α : ℝ) (h g rhsLin quad : κ → ℂ) (t : ℝ)
    (uv : ℂ × ℂ) :
    mixedBinStep α h g rhsLin quad t 1 uv
      = tikhonovXhat2 α h g (fun k => rhsLin k - (t : ℂ) * quad k) := by
  simp [mixedBinStep]

theorem bornRhs_tcc {ι : Type*} (w : κ → ι → ℂ) (pupil : κ → ι → G → ℂ)
    (src : Finset ι) (y : κ → G → ℂ) (t : ℝ) (δ : G → ℂ) (ξ : G) :
    bornRhs (fun k => tccKernel (w k) (pupil k) src) y t δ ξ
      = fun k =>
          yLin (fun k => tccKernel (w k) (pupil k) src) y ξ k
            - (t : ℂ) *
              ∑ m ∈ src, w k m * autocorr (hadamard (pupil k m) δ) ξ := by
  funext k
  simp [bornRhs, ihat_tcc]

theorem ihat_homotopy_cubic_zero (R : G → G → ℂ) (x0 δ : G → ℂ) (ξ : G)
    (t : ℝ) :
    ihat R (x0 + fun q => (t : ℂ) * δ q) ξ
      - ihat R x0 ξ - t * ihatJac R x0 δ ξ - t ^ 2 * ihat R δ ξ = 0 := by
  rw [ihat_homotopy_at]
  ring

theorem mixedBinStep_t0_unique {α : ℝ} (hα : 0 < α) (h g rhsLin quad : κ → ℂ)
    {u v : ℂ}
    (hmin : ∀ u' v',
      tikhonovJ2 α h g rhsLin u v ≤ tikhonovJ2 α h g rhsLin u' v') :
    mixedBinStep α h g rhsLin quad 0 1 (u, v) = (u, v) ∧
      (u, v) = tikhonovXhat2 α h g rhsLin := by
  have huv : (u, v) = tikhonovXhat2 α h g rhsLin :=
    tikhonov2_unique hα h g rhsLin hmin
  refine ⟨?_, huv⟩
  rw [mixedBinStep_init, ← huv]

/-- Skip nonlinear refinement on every defocus when the bilinear remainder
is at a noise floor `η`. -/
def mixedSkip (R : κ → G → G → ℂ) (δ : G → ℂ) (η : ℝ) : Prop :=
  ∀ k, stage2Skip (R k) δ η

theorem mixedSkip_of_bound (R : κ → G → G → ℂ) (δ : G → ℂ) {η : ℝ}
    (h : ∀ k, (∑ q : G, ∑ q' : G, ‖R k q q'‖) * (∑ q : G, ‖δ q‖) ^ 2 ≤ η) :
    mixedSkip R δ η :=
  fun k => stage2Skip_of_bound (R k) δ (h k)

/-- Per-bin remainder weight: `t = 0` (stage-1 residual) when every defocus
remainder at this bin is at most `η`; otherwise `t = 1` (full Born). -/
noncomputable def remainderWeight (quad : κ → ℂ) (η : ℝ) : ℝ :=
  haveI : Decidable (∀ k, ‖quad k‖ ≤ η) := Classical.dec _
  if ∀ k, ‖quad k‖ ≤ η then 0 else 1

theorem remainderWeight_zero {quad : κ → ℂ} {η : ℝ}
    (h : ∀ k, ‖quad k‖ ≤ η) : remainderWeight quad η = 0 := by
  simp [remainderWeight, h]

theorem remainderWeight_one {quad : κ → ℂ} {η : ℝ} {k : κ}
    (h : η < ‖quad k‖) : remainderWeight quad η = 1 := by
  have : ¬ ∀ k', ‖quad k'‖ ≤ η := fun hall => (not_le_of_gt h) (hall k)
  simp [remainderWeight, this]

theorem remainderWeight_of_mixedSkip (R : κ → G → G → ℂ) (δ : G → ℂ)
    {η : ℝ} (h : mixedSkip R δ η) (ξ : G) :
    remainderWeight (fun k => ihat (R k) δ ξ) η = 0 :=
  remainderWeight_zero fun k => h k ξ

lemma yLin_hermitian (R : κ → G → G → ℂ) (y : κ → G → ℂ) (ξ : G)
    (hR : ∀ k a b, conj (R k a b) = R k b a)
    (hy : ∀ k, y k (-ξ) = conj (y k ξ)) :
    yLin R y (-ξ) = fun k => conj (yLin R y ξ k) := by
  funext k
  simp [yLin, hy k, map_sub, ihat_hermitian (R k) vacuum ξ (hR k)]

lemma mixedBinStep_conj_swap (α : ℝ) (h g rhsLin quad : κ → ℂ)
    (t damp : ℝ) (uv : ℂ × ℂ) :
    mixedBinStep α (fun k => conj (g k)) (fun k => conj (h k))
        (fun k => conj (rhsLin k)) (fun k => conj (quad k)) t damp
        (conj uv.2, conj uv.1)
      = (conj (mixedBinStep α h g rhsLin quad t damp uv).2,
        conj (mixedBinStep α h g rhsLin quad t damp uv).1) := by
  have hy :
      (fun k => conj (rhsLin k) - (t : ℂ) * conj (quad k))
        = fun k => conj (rhsLin k - (t : ℂ) * quad k) := by
    funext k
    simp [map_sub, map_mul, conj_ofReal]
  simp [mixedBinStep, hy, tikhonovXhat2_conj_swap, map_sub, map_mul, conj_ofReal]

/-- Spectrum iterate: stage-1 init, then damped Born with schedules `t, damp`.
Only the first `2×2` coordinate is stored as a spectrum (`δ ξ`). The partner
`v ≈ conj(δ (-ξ))` is carried by `mixedSpectrumPair`. -/
def mixedSpectrum (α : ℝ) (h g : G → κ → ℂ) (R : κ → G → G → ℂ)
    (y : κ → G → ℂ) (t damp : ℕ → ℝ) : ℕ → G → ℂ
  | 0 => fun ξ => (tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ)).1
  | n + 1 =>
    let δ := mixedSpectrum α h g R y t damp n
    fun ξ =>
      let tgt := (tikhonovXhat2 α (h ξ) (g ξ) (bornRhs R y (t n) δ ξ)).1
      ((1 : ℂ) - (damp n : ℂ)) * δ ξ + (damp n : ℂ) * tgt

/-- Both vacuum-Jacobian coordinates of the mixed iterate.
`mixedBinStep` updates `(u,v)`; the stored object spectrum is the first
component (`mixedSpectrum_eq_pair_fst`). Identifying `δ(-ξ)` with
`conj v(ξ)` is a post-processing step on an odd frequency embedding, not
an automatic property of a general finite group. -/
def mixedSpectrumPair (α : ℝ) (h g : G → κ → ℂ) (R : κ → G → G → ℂ)
    (y : κ → G → ℂ) (t damp : ℕ → ℝ) : ℕ → G → ℂ × ℂ
  | 0 => fun ξ => tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ)
  | n + 1 =>
    let uv := mixedSpectrumPair α h g R y t damp n
    let δ : G → ℂ := fun ξ => (uv ξ).1
    fun ξ =>
      mixedBinStep α (h ξ) (g ξ) (yLin R y ξ) (fun k => ihat (R k) δ ξ)
        (t n) (damp n) (uv ξ)

theorem mixedSpectrum_zero (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) :
    mixedSpectrum α h g R y t damp 0
      = fun ξ => (tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ)).1 :=
  rfl

/-- If the first remainder weight is `t=0` and the step is `damp=1`, the first
Born update is already the unique stage-1 estimator. -/
theorem mixedSpectrum_t0_step (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t damp : ℕ → ℝ)
    (ht : t 0 = 0) (hdamp : damp 0 = 1) :
    mixedSpectrum α h g R y t damp 1 = mixedSpectrum α h g R y t damp 0 := by
  funext ξ
  have hrhs :
      bornRhs R y 0 (mixedSpectrum α h g R y t damp 0) ξ = yLin R y ξ := by
    funext k
    simp [bornRhs]
  calc mixedSpectrum α h g R y t damp 1 ξ
      = ((1 : ℂ) - (damp 0 : ℂ)) * mixedSpectrum α h g R y t damp 0 ξ
          + (damp 0 : ℂ) *
            (tikhonovXhat2 α (h ξ) (g ξ)
              (bornRhs R y (t 0) (mixedSpectrum α h g R y t damp 0) ξ)).1 :=
        rfl
    _ = (tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ)).1 := by
        rw [hdamp, ht, hrhs]
        simp
    _ = mixedSpectrum α h g R y t damp 0 ξ := rfl

theorem mixedSpectrumPair_zero (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) :
    mixedSpectrumPair α h g R y t damp 0
      = fun ξ => tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ) :=
  rfl

set_option linter.flexible false in
theorem mixedSpectrum_eq_pair_fst (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) :
    ∀ n, mixedSpectrum α h g R y t damp n
      = fun ξ => (mixedSpectrumPair α h g R y t damp n ξ).1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ξ
    simp [mixedSpectrum, mixedSpectrumPair, mixedBinStep, ih]
    have hrhs :
        bornRhs R y (t n)
            (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) ξ
          = fun k => yLin R y ξ k - (t n : ℂ) *
              ihat (R k)
                (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) ξ :=
      rfl
    rw [hrhs]
    ring

theorem mixedSpectrumPair_t0_step (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t damp : ℕ → ℝ)
    (ht : t 0 = 0) (hdamp : damp 0 = 1) :
    mixedSpectrumPair α h g R y t damp 1
      = mixedSpectrumPair α h g R y t damp 0 := by
  funext ξ
  have hstep :
      mixedSpectrumPair α h g R y t damp 1 ξ
        = mixedBinStep α (h ξ) (g ξ) (yLin R y ξ)
            (fun k => ihat (R k)
              (fun ζ => (mixedSpectrumPair α h g R y t damp 0 ζ).1) ξ)
            (t 0) (damp 0)
            (mixedSpectrumPair α h g R y t damp 0 ξ) :=
    rfl
  rw [hstep, ht, hdamp, mixedBinStep_init]
  rfl

/-- Mix of stage-1 skip and Born: per-bin remainder weight, then a damped
`2×2` update. Init is the vacuum Tikhonov estimator. -/
def mixedSpectrumMix (α : ℝ) (h g : G → κ → ℂ) (R : κ → G → G → ℂ)
    (y : κ → G → ℂ) (η : ℝ) (damp : ℕ → ℝ) : ℕ → G → ℂ
  | 0 => fun ξ => (tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ)).1
  | n + 1 =>
    let δ := mixedSpectrumMix α h g R y η damp n
    fun ξ =>
      let tξ := remainderWeight (fun k => ihat (R k) δ ξ) η
      let tgt := (tikhonovXhat2 α (h ξ) (g ξ) (bornRhs R y tξ δ ξ)).1
      ((1 : ℂ) - (damp n : ℂ)) * δ ξ + (damp n : ℂ) * tgt

theorem mixedSpectrumMix_zero (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (η : ℝ) (damp : ℕ → ℝ) :
    mixedSpectrumMix α h g R y η damp 0
      = fun ξ => (tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ)).1 :=
  rfl

/-- Global skip: if the bilinear remainder is at the noise floor, one
`damp = 1` step is already the stage-1 estimator. -/
theorem mixedSpectrumMix_skip_step (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (η : ℝ) (damp : ℕ → ℝ)
    (hskip : mixedSkip R (mixedSpectrumMix α h g R y η damp 0) η)
    (hdamp : damp 0 = 1) :
    mixedSpectrumMix α h g R y η damp 1
      = mixedSpectrumMix α h g R y η damp 0 := by
  funext ξ
  have ht := remainderWeight_of_mixedSkip R
    (mixedSpectrumMix α h g R y η damp 0) hskip ξ
  have hrhs :
      bornRhs R y 0 (mixedSpectrumMix α h g R y η damp 0) ξ
        = yLin R y ξ := by
    funext k
    simp [bornRhs]
  calc mixedSpectrumMix α h g R y η damp 1 ξ
      = ((1 : ℂ) - (damp 0 : ℂ)) * mixedSpectrumMix α h g R y η damp 0 ξ
          + (damp 0 : ℂ) *
            (tikhonovXhat2 α (h ξ) (g ξ)
              (bornRhs R y
                (remainderWeight
                  (fun k => ihat (R k)
                    (mixedSpectrumMix α h g R y η damp 0) ξ) η)
                (mixedSpectrumMix α h g R y η damp 0) ξ)).1 :=
        rfl
    _ = (tikhonovXhat2 α (h ξ) (g ξ) (yLin R y ξ)).1 := by
        rw [hdamp, ht, hrhs]
        simp
    _ = mixedSpectrumMix α h g R y η damp 0 ξ := rfl

/-- A loud bin (`‖ihat δ‖ > η` in some defocus) takes a full Born step. -/
theorem mixedSpectrumMix_born_bin (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (η : ℝ) (damp : ℕ → ℝ)
    {ξ : G} {k : κ}
    (hbig : η < ‖ihat (R k) (mixedSpectrumMix α h g R y η damp 0) ξ‖)
    (hdamp : damp 0 = 1) :
    mixedSpectrumMix α h g R y η damp 1 ξ
      = (tikhonovXhat2 α (h ξ) (g ξ)
          (bornRhs R y 1 (mixedSpectrumMix α h g R y η damp 0) ξ)).1 := by
  have ht :
      remainderWeight
        (fun k' => ihat (R k') (mixedSpectrumMix α h g R y η damp 0) ξ) η
        = 1 :=
    remainderWeight_one (k := k) hbig
  calc mixedSpectrumMix α h g R y η damp 1 ξ
      = ((1 : ℂ) - (damp 0 : ℂ)) * mixedSpectrumMix α h g R y η damp 0 ξ
          + (damp 0 : ℂ) *
            (tikhonovXhat2 α (h ξ) (g ξ)
              (bornRhs R y
                (remainderWeight
                  (fun k' => ihat (R k')
                    (mixedSpectrumMix α h g R y η damp 0) ξ) η)
                (mixedSpectrumMix α h g R y η damp 0) ξ)).1 :=
        rfl
    _ = (tikhonovXhat2 α (h ξ) (g ξ)
          (bornRhs R y 1 (mixedSpectrumMix α h g R y η damp 0) ξ)).1 := by
        rw [hdamp, ht]
        simp

/-- Hermitian partner of the dropped `2×2` coordinate is `conj pair.snd`
at `ξ`, under slice conjugacy (odd `qmap`, not odd `|G|`). -/
theorem mixedSpectrumPair_conj_partner (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) (ξ : G)
    (hh : h (-ξ) = fun k => conj (g ξ k))
    (hg : g (-ξ) = fun k => conj (h ξ k))
    (hR : ∀ k a b, conj (R k a b) = R k b a)
    (hy : yLin R y (-ξ) = fun k => conj (yLin R y ξ k))
    (n : ℕ) :
    mixedSpectrumPair α h g R y t damp n (-ξ)
      = (conj (mixedSpectrumPair α h g R y t damp n ξ).2,
        conj (mixedSpectrumPair α h g R y t damp n ξ).1) := by
  induction n with
  | zero =>
    simp only [mixedSpectrumPair]
    rw [hh, hg, hy, tikhonovXhat2_conj_swap]
  | succ n ih =>
    have hL :
        mixedSpectrumPair α h g R y t damp (n + 1) (-ξ)
          = mixedBinStep α (h (-ξ)) (g (-ξ)) (yLin R y (-ξ))
              (fun k => ihat (R k)
                (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) (-ξ))
              (t n) (damp n)
              (mixedSpectrumPair α h g R y t damp n (-ξ)) :=
      rfl
    have hRstep :
        mixedSpectrumPair α h g R y t damp (n + 1) ξ
          = mixedBinStep α (h ξ) (g ξ) (yLin R y ξ)
              (fun k => ihat (R k)
                (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) ξ)
              (t n) (damp n)
              (mixedSpectrumPair α h g R y t damp n ξ) :=
      rfl
    have hquad :
        (fun k => ihat (R k)
            (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) (-ξ))
          = fun k => conj (ihat (R k)
              (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) ξ) := by
      funext k
      exact ihat_hermitian (R k)
        (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) ξ (hR k)
    rw [hL, hRstep, hh, hg, hy, hquad, ih]
    exact mixedBinStep_conj_swap α (h ξ) (g ξ) (yLin R y ξ)
      (fun k => ihat (R k)
        (fun ζ => (mixedSpectrumPair α h g R y t damp n ζ).1) ξ)
      (t n) (damp n) (mixedSpectrumPair α h g R y t damp n ξ)

/-- The dropped partner of `mixedSpectrum` is `conj` of `pair.snd` at `ξ`. -/
theorem mixedSpectrum_eq_conj_pair_snd (α : ℝ) (h g : G → κ → ℂ)
    (R : κ → G → G → ℂ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) (ξ : G)
    (hh : h (-ξ) = fun k => conj (g ξ k))
    (hg : g (-ξ) = fun k => conj (h ξ k))
    (hR : ∀ k a b, conj (R k a b) = R k b a)
    (hy : yLin R y (-ξ) = fun k => conj (yLin R y ξ k))
    (n : ℕ) :
    mixedSpectrum α h g R y t damp n (-ξ)
      = conj (mixedSpectrumPair α h g R y t damp n ξ).2 := by
  rw [mixedSpectrum_eq_pair_fst]
  have hpair := mixedSpectrumPair_conj_partner α h g R y t damp ξ hh hg hR hy n
  simpa using congrArg Prod.fst hpair

/-- Algebraic contraction implication (no existence / Banach FPT). -/
lemma l1_eq_zero_of_lip {s s' : G → ℂ} {L : ℝ}
    (hL : L < 1)
    (hineq : (∑ q : G, (‖s q - s' q‖ : ℝ))
      ≤ L * (∑ q : G, (‖s q - s' q‖ : ℝ))) :
    s = s' := by
  have hnn : (0 : ℝ) ≤ ∑ q : G, (‖s q - s' q‖ : ℝ) :=
    Finset.sum_nonneg fun q _ => norm_nonneg (s q - s' q)
  have hmul : (1 - L) * (∑ q : G, (‖s q - s' q‖ : ℝ)) ≤ 0 := by nlinarith
  have hz : ∑ q : G, (‖s q - s' q‖ : ℝ) = 0 := by
    have hpos : 0 ≤ 1 - L := by linarith
    nlinarith
  funext q
  have hterm :
      (‖s q - s' q‖ : ℝ)
        ≤ ∑ q : G, (‖s q - s' q‖ : ℝ) :=
    Finset.single_le_sum (f := fun q : G => (‖s q - s' q‖ : ℝ))
      (fun q _ => norm_nonneg (s q - s' q)) (Finset.mem_univ q)
  have : ‖s q - s' q‖ ≤ 0 := by
    simpa [hz] using hterm
  have hq : ‖s q - s' q‖ = 0 := le_antisymm this (norm_nonneg (s q - s' q))
  exact eq_of_sub_eq_zero (norm_eq_zero.mp hq)

theorem picard_unique_of_lip (Φ : (G → ℂ) → (G → ℂ)) (δ δ' : G → ℂ) {L : ℝ}
    (hfix : Φ δ = δ ∧ Φ δ' = δ')
    (hLip : (∑ q : G, (‖Φ δ q - Φ δ' q‖ : ℝ))
      ≤ L * (∑ q : G, (‖δ q - δ' q‖ : ℝ)))
    (hL : L < 1) : δ = δ' :=
  l1_eq_zero_of_lip hL (by simpa [hfix.1, hfix.2] using hLip)

end
