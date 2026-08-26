/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.Gram
import Mathlib.Tactic.Linarith

/-!
# Exact inverses on one, two, three Fourier modes and two-axis 3-wave objects

Finite-support specialisations of the Gram inverse. On two modes the intensities
$`I(0)`$ and $`I(\xi)`$ determine a quadratic for the pair of amplitudes; the
specular root is the one with larger DC. A non-collinear 3-wave object
`{0, u, v}` inverts by a scalar CTF slice at each diffracted frequency.
-/

open Complex Real
open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

/-- One mode: a DC-only object produces intensity only at `ξ = 0`. -/
theorem ihat_of_dc_support (R : G → G → ℂ) (Ψ : G → ℂ)
    (hΨ : ∀ q, q ≠ 0 → Ψ q = 0) (ξ : G) :
    ihat R Ψ ξ = if ξ = 0 then R 0 0 * gram Ψ 0 0 else 0 := by
  rw [ihat_eq_gram]
  rw [Fintype.sum_eq_single (0 : G)]
  · by_cases hξ : ξ = 0
    · subst hξ
      simp [gram]
    · have hnz : Ψ (-ξ) = 0 := hΨ (-ξ) (neg_ne_zero.mpr hξ)
      simp [hξ, gram, zero_sub, hnz]
  · intro q hq
    simp [gram, hΨ q hq]

/-- Plus root of the two-mode quadratic `s(T - s) = |Z|²`. -/
noncomputable def twoModePlus (T : ℝ) (Z : ℂ) : ℝ :=
  (T + Real.sqrt (T ^ 2 - 4 * ‖Z‖ ^ 2)) / 2

/-- Minus root of the same quadratic. -/
noncomputable def twoModeMinus (T : ℝ) (Z : ℂ) : ℝ :=
  (T - Real.sqrt (T ^ 2 - 4 * ‖Z‖ ^ 2)) / 2

lemma twoMode_disc (a b T : ℝ) (Z : ℂ) (hT : a + b = T) (hZ : a * b = ‖Z‖ ^ 2) :
    T ^ 2 - 4 * ‖Z‖ ^ 2 = (a - b) ^ 2 := by
  rw [← hT, ← hZ]
  ring

/-- `a` is one of the two quadratic roots of `s² - T s + |Z|² = 0`. -/
theorem twoMode_roots (a b T : ℝ) (Z : ℂ)
    (hT : a + b = T) (hZ : a * b = ‖Z‖ ^ 2) :
    a = twoModePlus T Z ∨ a = twoModeMinus T Z := by
  have hdisc := twoMode_disc a b T Z hT hZ
  have hsqrt : Real.sqrt (T ^ 2 - 4 * ‖Z‖ ^ 2) = |a - b| := by
    rw [hdisc, Real.sqrt_sq_eq_abs]
  unfold twoModePlus twoModeMinus
  rw [hsqrt]
  rcases le_total b a with hba | hab
  · have : |a - b| = a - b := abs_of_nonneg (sub_nonneg.2 hba)
    refine Or.inl ?_
    rw [this, ← hT]
    ring
  · have : |a - b| = b - a := by
      rw [abs_of_nonpos (sub_nonpos.2 hab), neg_sub]
    refine Or.inr ?_
    rw [this, ← hT]
    ring

lemma twoMode_plus_add_minus (T : ℝ) (Z : ℂ) :
    twoModePlus T Z + twoModeMinus T Z = T := by
  unfold twoModePlus twoModeMinus
  ring

/-- The unordered pair of quadratic roots is `{a, b}`. -/
theorem twoMode_roots_pair (a b T : ℝ) (Z : ℂ)
    (hT : a + b = T) (hZ : a * b = ‖Z‖ ^ 2) :
    (a = twoModePlus T Z ∧ b = twoModeMinus T Z)
      ∨ (a = twoModeMinus T Z ∧ b = twoModePlus T Z) := by
  have hsum := twoMode_plus_add_minus T Z
  rcases twoMode_roots a b T Z hT hZ with ha | ha
  · refine Or.inl ⟨ha, ?_⟩
    linarith
  · refine Or.inr ⟨ha, ?_⟩
    linarith

/-- Specular selection: the larger amplitude is the plus root. -/
theorem twoMode_specular (a b T : ℝ) (Z : ℂ)
    (hT : a + b = T) (hZ : a * b = ‖Z‖ ^ 2) (hle : b ≤ a) :
    a = twoModePlus T Z := by
  have hdisc := twoMode_disc a b T Z hT hZ
  have hsqrt : Real.sqrt (T ^ 2 - 4 * ‖Z‖ ^ 2) = a - b := by
    rw [hdisc, Real.sqrt_sq_eq_abs, abs_of_nonneg (sub_nonneg.2 hle)]
  unfold twoModePlus
  rw [hsqrt, ← hT]
  ring

/-- Two-mode remainder at `ξ` vanishes: every leftover index has `Ψ q = 0`. -/
theorem bilinearRemainder_twoMode (R : G → G → ℂ) (Ψ : G → ℂ) {ξ : G}
    (hΨ : ∀ q, q ≠ 0 → q ≠ ξ → Ψ q = 0) :
    bilinearRemainder R Ψ ξ = 0 := by
  unfold bilinearRemainder
  refine Finset.sum_eq_zero fun q _ => ?_
  split_ifs with hq
  · rfl
  · have hq0 : q ≠ 0 := fun h => hq (Or.inl h)
    have hqξ : q ≠ ξ := fun h => hq (Or.inr h)
    simp [gram, hΨ q hq0 hqξ]

/-- Two-mode object `{0, ξ}`: conjugate branch drops when `-ξ` is not a mode. -/
theorem ihat_twoMode (R : G → G → ℂ) (Ψ : G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0) (h2 : ξ + ξ ≠ 0)
    (hΨ : ∀ q, q ≠ 0 → q ≠ ξ → Ψ q = 0) :
    ihat R Ψ ξ = R ξ 0 * gram Ψ ξ 0 := by
  have hconj : gram Ψ 0 (-ξ) = 0 := by
    have hn0 : -ξ ≠ 0 := neg_ne_zero.mpr hξ
    have hnξ : -ξ ≠ ξ := by
      intro hz
      exact h2 (neg_eq_iff_add_eq_zero.mp hz)
    simp [gram, hΨ (-ξ) hn0 hnξ]
  rw [ihat_dc_split (hξ := hξ), bilinearRemainder_twoMode R Ψ hΨ, hconj]
  simp

theorem ihat_twoMode_dc (R : G → G → ℂ) (Ψ : G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0)
    (hΨ : ∀ q, q ≠ 0 → q ≠ ξ → Ψ q = 0) :
    ihat R Ψ 0
      = R 0 0 * gram Ψ 0 0 + R ξ ξ * gram Ψ ξ ξ := by
  rw [ihat_eq_gram]
  simp only [sub_zero]
  rw [← Finset.sum_add_sum_compl ({0, ξ} : Finset G)]
  have hpair : ∑ q ∈ ({0, ξ} : Finset G), R q q * gram Ψ q q
      = R 0 0 * gram Ψ 0 0 + R ξ ξ * gram Ψ ξ ξ := by
    rw [Finset.sum_pair hξ.symm]
  have hrest : ∑ q ∈ ({0, ξ} : Finset G)ᶜ, R q q * gram Ψ q q = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have : q ≠ 0 ∧ q ≠ ξ := by
      simpa [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] using hq
    simp [gram, hΨ q this.1 this.2]
  rw [hpair, hrest, add_zero]

/-- Three-mode remainder at `ξ` vanishes: leftover indices hit a missing mode. -/
theorem bilinearRemainder_threeMode (R : G → G → ℂ) (Ψ : G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0) (h2 : ξ + ξ ≠ 0) (h3 : ξ + ξ ≠ -ξ)
    (hΨ : ∀ q, q ≠ 0 → q ≠ ξ → q ≠ -ξ → Ψ q = 0) :
    bilinearRemainder R Ψ ξ = 0 := by
  unfold bilinearRemainder
  refine Finset.sum_eq_zero fun q _ => ?_
  split_ifs with hq
  · rfl
  · have hq0 : q ≠ 0 := fun h => hq (Or.inl h)
    have hqξ : q ≠ ξ := fun h => hq (Or.inr h)
    by_cases hm : q = -ξ
    · subst hm
      have hmiss : Ψ (-ξ - ξ) = 0 := by
        have h0' : -ξ - ξ ≠ 0 := by
          intro hz
          exact h2 (neg_eq_iff_add_eq_zero.mp (eq_of_sub_eq_zero hz))
        have hξ' : -ξ - ξ ≠ ξ := by
          intro hz
          have : -(ξ + ξ) = ξ := by
            simpa [neg_add, sub_eq_add_neg] using hz
          exact h3 (neg_eq_iff_eq_neg.mp this)
        have hm' : -ξ - ξ ≠ -ξ := by
          intro hz
          exact hξ (sub_eq_self.mp hz)
        exact hΨ _ h0' hξ' hm'
      simp [gram, hmiss]
    · simp [gram, hΨ q hq0 hqξ hm]

/-- Three-mode object `{-ξ, 0, ξ}`: frequency `ξ` is exactly the vacuum 2×2. -/
theorem ihat_threeMode_axis (R : G → G → ℂ) (Ψ : G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0) (h2 : ξ + ξ ≠ 0) (h3 : ξ + ξ ≠ -ξ)
    (hΨ : ∀ q, q ≠ 0 → q ≠ ξ → q ≠ -ξ → Ψ q = 0) :
    ihat R Ψ ξ
      = R ξ 0 * gram Ψ ξ 0 + R 0 (-ξ) * gram Ψ 0 (-ξ) := by
  rw [ihat_dc_split (hξ := hξ), bilinearRemainder_threeMode R Ψ hξ h2 h3 hΨ]
  ring

/-- Two non-collinear diffracted beams: leftover index `v` misses `v - u`. -/
theorem bilinearRemainder_twoAxis (R : G → G → ℂ) (Ψ : G → ℂ) {u v : G}
    (hu : u ≠ 0) (_hv : v ≠ 0) (huv : u ≠ v) (h2 : u + u ≠ v)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0) :
    bilinearRemainder R Ψ u = 0 := by
  unfold bilinearRemainder
  refine Finset.sum_eq_zero fun q _ => ?_
  split_ifs with hq
  · rfl
  · have hq0 : q ≠ 0 := fun h => hq (Or.inl h)
    have hqu : q ≠ u := fun h => hq (Or.inr h)
    by_cases hqv : q = v
    · rw [hqv]
      have hmiss : Ψ (v - u) = 0 := by
        have h0' : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
        have hu' : v - u ≠ u := fun hz => h2 (sub_eq_iff_eq_add.mp hz).symm
        have hv' : v - u ≠ v := fun hz => hu (sub_eq_self.mp hz)
        exact hΨ _ h0' hu' hv'
      simp [gram, hmiss]
    · simp [gram, hΨ q hq0 hqu hqv]

/-- 2D three-wave object `{0, u, v}` at frequency `u`: conjugate branch and remainder drop. -/
theorem ihat_twoAxis (R : G → G → ℂ) (Ψ : G → ℂ) {u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (h2u : u + u ≠ 0) (h2 : u + u ≠ v)
    (hneg : v ≠ -u)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0) :
    ihat R Ψ u = R u 0 * gram Ψ u 0 := by
  have hconj : gram Ψ 0 (-u) = 0 := by
    have hn0 : -u ≠ 0 := neg_ne_zero.mpr hu
    have hnu : -u ≠ u := fun hz => h2u (neg_eq_iff_add_eq_zero.mp hz)
    have hnv : -u ≠ v := fun hz => hneg hz.symm
    simp [gram, hΨ (-u) hn0 hnu hnv]
  rw [ihat_dc_split (hξ := hu), bilinearRemainder_twoAxis R Ψ hu hv huv h2 hΨ, hconj]
  simp only [mul_zero, add_zero]

/-- Same 3-wave object at the second diffracted frequency `v`. -/
theorem ihat_twoAxis_v (R : G → G → ℂ) (Ψ : G → ℂ) {u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (h2v : v + v ≠ 0) (h2vu : v + v ≠ u)
    (hneg : u ≠ -v)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0) :
    ihat R Ψ v = R v 0 * gram Ψ v 0 := by
  refine ihat_twoAxis R Ψ hv hu huv.symm h2v h2vu hneg ?_
  intro q hq0 hqv hqu
  exact hΨ q hq0 hqu hqv

/-- DC intensity of a 3-wave object is the sum of the three diagonal Gram entries. -/
theorem ihat_twoAxis_dc (R : G → G → ℂ) (Ψ : G → ℂ) {u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0) :
    ihat R Ψ 0
      = R 0 0 * gram Ψ 0 0 + R u u * gram Ψ u u + R v v * gram Ψ v v := by
  rw [ihat_eq_gram]
  simp only [sub_zero]
  rw [← Finset.sum_add_sum_compl (insert v ({0, u} : Finset G))]
  have hmemv : v ∉ ({0, u} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hv, huv.symm⟩
  have htrip :
      ∑ q ∈ insert v ({0, u} : Finset G), R q q * gram Ψ q q
        = R v v * gram Ψ v v
          + (R 0 0 * gram Ψ 0 0 + R u u * gram Ψ u u) := by
    rw [Finset.sum_insert hmemv, Finset.sum_pair hu.symm]
  have hrest :
      ∑ q ∈ (insert v ({0, u} : Finset G))ᶜ, R q q * gram Ψ q q = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' : q ≠ v ∧ q ≠ 0 ∧ q ≠ u := by
      simpa [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] using hq
    simp [gram, hΨ q hq'.2.1 hq'.2.2 hq'.1]
  rw [htrip, hrest, add_zero]
  ring

end
