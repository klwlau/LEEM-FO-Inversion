/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.CTF
import LeemFO.Ratios
import LeemFO.Tikhonov
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Linearized multi-defocus FO/CTF inverse: identifiability

Connects the scalar Tikhonov algebra to the FO kernel `R_FO` on the CTF
slice `q' = 0`. Informal ingredients (DFT existence, statistical noise)
are not used.
-/

open Complex Real
open scoped BigOperators ComplexConjugate

namespace LEEM

variable (p : LEEM)

lemma waveS_ne_zero (q Δz : ℝ) : p.waveS q Δz ≠ 0 :=
  Complex.exp_ne_zero _

lemma spatialEnvelopeClosed_ne_zero (q q' Δz : ℝ) :
    p.spatialEnvelopeClosed q q' Δz ≠ 0 :=
  Complex.exp_ne_zero _

/-- Outside the contrast aperture the CTF-slice multiplier vanishes. -/
theorem R_FO_axis_eq_zero_of_outside {q Δz : ℝ} (h : p.qAp < |q|) :
    p.R_FO q 0 Δz = 0 := by
  have : p.aperture q = 0 := p.aperture_of_gt h
  simp [R_FO, R0, this]

lemma aperture_zero_of_neg_cutoff (h : p.qAp < 0) (q : ℝ) : p.aperture q = 0 :=
  p.aperture_of_gt (lt_of_lt_of_le h (abs_nonneg q))

/-- Inside a nonnegative aperture the CTF-slice multiplier is nonzero. -/
theorem R_FO_axis_ne_zero_of_inside {q Δz : ℝ} (h0 : 0 ≤ p.qAp)
    (h : |q| ≤ p.qAp) : p.R_FO q 0 Δz ≠ 0 := by
  have hAp0 : |0| ≤ p.qAp := by simpa using h0
  have hap : p.aperture q = 1 := p.aperture_of_le h
  have hap0 : p.aperture 0 = 1 := p.aperture_of_le hAp0
  have heq :
      p.R_FO q 0 Δz
        = p.waveS q Δz * conj (p.waveS 0 Δz) * p.spatialEnvelopeClosed q 0 Δz *
          chromaticEnvelopeClosed p.sigmaE (p.b1 q 0) (p.b2 q 0) := by
    unfold R_FO
    rw [p.R0_at_zero_energy, hap, hap0]
    simp
    try ring
  rw [heq]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact p.waveS_ne_zero q Δz
  · exact (map_ne_zero (starRingEnd ℂ)).mpr (p.waveS_ne_zero 0 Δz)
  · exact p.spatialEnvelopeClosed_ne_zero q 0 Δz
  · exact chromaticEnvelopeClosed_ne_zero p.sigmaE (p.b1 q 0) (p.b2 q 0)

/-- Characterization: on a physical aperture the slice vanishes iff `q` is
outside the disk. -/
theorem R_FO_axis_eq_zero_iff {q Δz : ℝ} (h0 : 0 ≤ p.qAp) :
    p.R_FO q 0 Δz = 0 ↔ p.qAp < |q| := by
  constructor
  · intro hR
    by_contra hle
    exact p.R_FO_axis_ne_zero_of_inside h0 (le_of_not_gt hle) hR
  · exact p.R_FO_axis_eq_zero_of_outside

/-- Modes outside the aperture are invisible to every defocus: the Tikhonov
estimator of that bin is `0` independently of the data. -/
theorem tikhonovXhat_outside_aperture {κ : Type*} [Fintype κ]
    {α : ℝ} (_hα : α ≠ 0) (Δz : κ → ℝ) {q : ℝ} (h : p.qAp < |q|)
    (y : κ → ℂ) :
    tikhonovXhat α (fun k => p.R_FO q 0 (Δz k)) y = 0 :=
  tikhonovXhat_eq_zero_of_h_zero (fun k => p.R_FO q 0 (Δz k)) y
    fun k => p.R_FO_axis_eq_zero_of_outside (Δz := Δz k) h

lemma chiS_zero (Δz : ℝ) : p.chiS 0 Δz = 0 := by
  simp [chiS]

/-- Weak-phase CTF factor `sin(2π χ_S)` vanishes on half-integer aberration. -/
theorem weakPhase_sin_eq_zero {q Δz : ℝ} {n : ℤ}
    (h : 2 * p.chiS q Δz = n) :
    Real.sin (2 * π * p.chiS q Δz) = 0 := by
  have : 2 * π * p.chiS q Δz = n * π := by
    calc
      2 * π * p.chiS q Δz = (2 * p.chiS q Δz) * π := by ring
      _ = (n : ℝ) * π := by rw [h]
  rw [this, Real.sin_int_mul_pi]

/-- For a pure-defocus NAC column, a large enough aperture contains a
nonzero weak-phase CTF zero. -/
theorem exists_interior_weakPhase_zero
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0) (hlam : 0 < p.lam)
    (hAp : 0 ≤ p.qAp) {Δz : ℝ} (hΔz : Δz ≠ 0)
    (hcut : 1 ≤ |Δz| * p.lam * p.qAp ^ 2) :
    ∃ q : ℝ, 0 < |q| ∧ |q| ≤ p.qAp ∧ Real.sin (2 * π * p.chiS q Δz) = 0 := by
  have hden : 0 < |Δz| * p.lam := mul_pos (abs_pos.mpr hΔz) hlam
  let q : ℝ := Real.sqrt (1 / (|Δz| * p.lam))
  have hq2 : q ^ 2 = 1 / (|Δz| * p.lam) :=
    Real.sq_sqrt (div_nonneg zero_le_one hden.le)
  have hqpos : 0 < q := Real.sqrt_pos.2 (div_pos zero_lt_one hden)
  have hqabs : |q| = q := abs_of_pos hqpos
  have hχ : p.chiS q Δz = (1 / 2) * (Δz / |Δz|) := by
    simp [chiS, hC3, hC5, hq2]
    field_simp [hden.ne']
    try ring
  have hqle : |q| ≤ p.qAp := by
    rw [hqabs, Real.sqrt_le_iff]
    refine ⟨hAp, ?_⟩
    have : 1 / (|Δz| * p.lam) ≤ p.qAp ^ 2 :=
      (div_le_iff₀ hden).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcut)
    simpa [hq2] using this
  refine ⟨q, by rwa [hqabs], hqle, ?_⟩
  have h2 : 2 * p.chiS q Δz = Δz / |Δz| := by
    rw [hχ]; ring
  by_cases hpos : 0 < Δz
  · have hn : 2 * p.chiS q Δz = (1 : ℤ) := by
      rw [h2, abs_of_pos hpos, div_self (ne_of_gt hpos)]
      norm_cast
    exact p.weakPhase_sin_eq_zero hn
  · have hneg : Δz < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hΔz
    have hn : 2 * p.chiS q Δz = (-1 : ℤ) := by
      rw [h2, abs_of_neg hneg]
      field_simp [ne_of_lt hneg]
      ring
    exact p.weakPhase_sin_eq_zero hn

/-- Object-wave global phase (real-space gauge). -/
theorem objectWave_phase_shift (σ φ : ℝ → ℝ) (θ r : ℝ) :
    objectWave σ (fun x => φ x + θ) r
      = cexp (I * θ) * objectWave σ φ r := by
  unfold objectWave
  have : ((φ r + θ : ℝ) : ℂ) = (φ r : ℂ) + (θ : ℂ) := by simp
  rw [this, mul_add, Complex.exp_add]
  ring

end LEEM

/-! ## Discrete bilinear intensity: gauge and quadratic remainder -/

section Bilinear

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Vacuum spectrum: DC coefficient `1`, all other modes `0`. -/
def vacuum : G → ℂ := fun q => if q = 0 then 1 else 0

/-- Discrete bilinear intensity Fourier coefficient at difference frequency `ξ`. -/
def ihat (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) : ℂ :=
  ∑ q : G, Ψ q * R q (q - ξ) * conj (Ψ (q - ξ))

/-- Global phase of the object spectrum does not change `ihat`. -/
lemma cexp_I_mul_conj (θ : ℝ) : cexp (I * θ) * conj (cexp (I * θ)) = 1 := by
  rw [mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp [mul_re]

theorem ihat_gauge (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) (θ : ℝ) :
    ihat R (fun q => cexp (I * θ) * Ψ q) ξ = ihat R Ψ ξ := by
  unfold ihat
  refine Finset.sum_congr rfl fun q _ => ?_
  have hφ := cexp_I_mul_conj θ
  calc
    cexp (I * θ) * Ψ q * R q (q - ξ) * conj (cexp (I * θ) * Ψ (q - ξ))
        = cexp (I * θ) * Ψ q * R q (q - ξ)
            * (conj (cexp (I * θ)) * conj (Ψ (q - ξ))) := by
          simp [map_mul]
    _ = (cexp (I * θ) * conj (cexp (I * θ)))
            * (Ψ q * R q (q - ξ) * conj (Ψ (q - ξ))) := by
          ring
    _ = Ψ q * R q (q - ξ) * conj (Ψ (q - ξ)) := by
          rw [hφ, one_mul]

theorem ihat_vacuum (R : G → G → ℂ) (ξ : G) :
    ihat R vacuum ξ = if ξ = 0 then R 0 0 else 0 := by
  unfold ihat vacuum
  rw [Fintype.sum_eq_single (0 : G)]
  · simp
    by_cases hξ : ξ = 0
    · simp [hξ]
    · simp [hξ]
  · intro q hq
    simp [hq]

/-- Jacobian of `ihat` at a background `x0`. -/
def ihatJac (R : G → G → ℂ) (x0 δ : G → ℂ) (ξ : G) : ℂ :=
  ∑ q : G, x0 q * R q (q - ξ) * conj (δ (q - ξ))
    + ∑ q : G, δ q * R q (q - ξ) * conj (x0 (q - ξ))

/-- Exact quadratic expansion: one Gauss–Newton step drops `ihat R δ ξ`. -/
theorem ihat_add (R : G → G → ℂ) (x0 δ : G → ℂ) (ξ : G) :
    ihat R (x0 + δ) ξ = ihat R x0 ξ + ihatJac R x0 δ ξ + ihat R δ ξ := by
  unfold ihat ihatJac
  simp [add_mul, mul_add, map_add, Finset.sum_add_distrib]
  ac_rfl

theorem ihatJac_vacuum (R : G → G → ℂ) (δ : G → ℂ) (ξ : G) :
    ihatJac R vacuum δ ξ = R ξ 0 * δ ξ + R 0 (-ξ) * conj (δ (-ξ)) := by
  unfold ihatJac vacuum
  have h1 :
      ∑ q : G, (if q = 0 then (1 : ℂ) else 0) * R q (q - ξ) * conj (δ (q - ξ))
        = R 0 (-ξ) * conj (δ (-ξ)) := by
    rw [Fintype.sum_eq_single (0 : G)]
    · simp
    · intro q hq
      simp [hq]
  have h2 :
      ∑ q : G, δ q * R q (q - ξ) * conj (if q - ξ = 0 then (1 : ℂ) else 0)
        = δ ξ * R ξ 0 := by
    rw [Fintype.sum_eq_single ξ]
    · simp
    · intro q hq
      have : q - ξ ≠ 0 := fun h => hq (eq_of_sub_eq_zero h)
      simp [this]
  rw [h1, h2]
  ring

/-- Quadratic remainder of bilinear FO versus vacuum linearization. -/
theorem ihat_quadratic_remainder (R : G → G → ℂ) (δ : G → ℂ) (ξ : G) :
    ihat R (vacuum + δ) ξ - ihat R vacuum ξ - ihatJac R vacuum δ ξ
      = ihat R δ ξ := by
  rw [ihat_add]
  ring

/-- Crude but fully elementary remainder bound (order `‖δ‖²`). -/
theorem ihat_bound (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) :
    ‖ihat R Ψ ξ‖
      ≤ (∑ q : G, ∑ q' : G, ‖R q q'‖) * (∑ q : G, ‖Ψ q‖) ^ 2 := by
  unfold ihat
  have hsum :
      ‖∑ q : G, Ψ q * R q (q - ξ) * conj (Ψ (q - ξ))‖
        ≤ ∑ q : G, ‖Ψ q‖ * ‖R q (q - ξ)‖ * ‖Ψ (q - ξ)‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun q _ => ?_
    simp [mul_assoc]
  refine hsum.trans ?_
  have hS : 0 ≤ ∑ t : G, ‖Ψ t‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpt (q : G) :
      ‖Ψ q‖ * ‖R q (q - ξ)‖ * ‖Ψ (q - ξ)‖
        ≤ ‖R q (q - ξ)‖ * (∑ t : G, ‖Ψ t‖) ^ 2 := by
    have hq : ‖Ψ q‖ ≤ ∑ t : G, ‖Ψ t‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ q)
    have hq' : ‖Ψ (q - ξ)‖ ≤ ∑ t : G, ‖Ψ t‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    have hΨ : ‖Ψ q‖ * ‖Ψ (q - ξ)‖ ≤ (∑ t : G, ‖Ψ t‖) * (∑ t : G, ‖Ψ t‖) :=
      mul_le_mul hq hq' (norm_nonneg _) hS
    have hR : 0 ≤ ‖R q (q - ξ)‖ := norm_nonneg _
    calc
      ‖Ψ q‖ * ‖R q (q - ξ)‖ * ‖Ψ (q - ξ)‖
          = ‖R q (q - ξ)‖ * (‖Ψ q‖ * ‖Ψ (q - ξ)‖) := by ring
      _ ≤ ‖R q (q - ξ)‖ * ((∑ t : G, ‖Ψ t‖) * (∑ t : G, ‖Ψ t‖)) :=
            mul_le_mul_of_nonneg_left hΨ hR
      _ = ‖R q (q - ξ)‖ * (∑ t : G, ‖Ψ t‖) ^ 2 := by rw [pow_two]
  have hmid :
      ∑ q : G, ‖Ψ q‖ * ‖R q (q - ξ)‖ * ‖Ψ (q - ξ)‖
        ≤ (∑ q : G, ‖R q (q - ξ)‖) * (∑ t : G, ‖Ψ t‖) ^ 2 := by
    calc
      ∑ q : G, ‖Ψ q‖ * ‖R q (q - ξ)‖ * ‖Ψ (q - ξ)‖
          ≤ ∑ q : G, ‖R q (q - ξ)‖ * (∑ t : G, ‖Ψ t‖) ^ 2 := by
            exact Finset.sum_le_sum fun q _ => hpt q
      _ = (∑ q : G, ‖R q (q - ξ)‖) * (∑ t : G, ‖Ψ t‖) ^ 2 := by
            rw [← Finset.sum_mul]
  refine hmid.trans ?_
  have hR : ∑ q : G, ‖R q (q - ξ)‖ ≤ ∑ q : G, ∑ q' : G, ‖R q q'‖ :=
    Finset.sum_le_sum fun q _ =>
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ (q - ξ))
  exact mul_le_mul_of_nonneg_right hR (sq_nonneg _)

end Bilinear
