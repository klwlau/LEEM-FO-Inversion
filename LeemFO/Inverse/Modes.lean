/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeemFO.Forward.CTF
import LeemFO.Forward.PhaseObject

/-!
# Aperture-truncated Jacobi–Anger modes

For a 1D sinusoidal phase object the Fourier support is the Bessel ladder
`q_n = n / Λ`. A hard contrast aperture of radius `qap` keeps only
`|n| ≤ ⌊qap * Λ⌋`, so `M = 2 * nAperture qap Λ + 1` modes enter the bilinear
FO image (a double sum of `M²` terms). Discrete-mode fitting is Gauss–Newton
restricted to that `M`-dimensional manifold — the fastest still-correct inverse
for Yu's sinusoid.

This file proves the mode count and the aperture bound. It does not encode an
iterative solver.
-/

open Complex hiding log exp sin cos tan
open Real hiding log exp
open Finset

noncomputable section

/-- `(n.natAbs : ℤ) = |n|`. -/
lemma coe_natAbs (n : ℤ) : (n.natAbs : ℤ) = |n| := by
  cases n with
  | ofNat m =>
    have hm : 0 ≤ (m : ℤ) := Int.natCast_nonneg m
    -- `Int.ofNat m` is `↑m`; `natAbs` on a nonnegative integer is itself.
    change ((m : ℕ) : ℤ) = |(m : ℤ)|
    rw [abs_of_nonneg hm]
  | negSucc m =>
    have hn : Int.negSucc m < 0 := Int.negSucc_lt_zero m
    rw [abs_of_neg hn, Int.natAbs_negSucc]
    simp [Int.negSucc_eq]

/-- Highest harmonic index transmitted by a hard aperture of radius `qap`
for a grating of wavelength `Λ`. Equals `0` if `qap * Λ < 1`. -/
def nAperture (qap Λ : ℝ) : ℕ := Nat.floor (qap * Λ)

/-- Integer modes with `|n| ≤ nAperture qap Λ`. -/
def modeSet (qap Λ : ℝ) : Finset ℤ :=
  Icc (-(nAperture qap Λ : ℤ)) (nAperture qap Λ)

lemma card_modeSet (qap Λ : ℝ) :
    (modeSet qap Λ).card = 2 * nAperture qap Λ + 1 := by
  unfold modeSet
  rw [Int.card_Icc]
  set N := nAperture qap Λ
  have h : (N : ℤ) + 1 - -N = (2 * N + 1 : ℕ) := by
    omega
  rw [h, Int.toNat_natCast]

lemma card_modePairs (qap Λ : ℝ) :
    (modeSet qap Λ ×ˢ modeSet qap Λ).card = (2 * nAperture qap Λ + 1) ^ 2 := by
  rw [card_product, card_modeSet, sq]

lemma mem_modeSet_iff {qap Λ : ℝ} {n : ℤ} :
    n ∈ modeSet qap Λ ↔ n.natAbs ≤ nAperture qap Λ := by
  rw [modeSet, mem_Icc]
  calc
    (-(nAperture qap Λ : ℤ) ≤ n ∧ n ≤ nAperture qap Λ) ↔
        |n| ≤ (nAperture qap Λ : ℤ) := abs_le.symm
    _ ↔ (n.natAbs : ℤ) ≤ nAperture qap Λ := by rw [← coe_natAbs]
    _ ↔ n.natAbs ≤ nAperture qap Λ := Nat.cast_le

/-- Every retained mode lies inside the contrast aperture: `|n|/Λ ≤ qap`. -/
lemma mode_in_aperture {qap Λ : ℝ} (hq : 0 ≤ qap) (hΛ : 0 < Λ) {n : ℤ}
    (hn : n ∈ modeSet qap Λ) : |(n : ℝ)| / Λ ≤ qap := by
  have hN : (n.natAbs : ℝ) ≤ nAperture qap Λ :=
    Nat.cast_le.mpr (mem_modeSet_iff.mp hn)
  have hfloor : (nAperture qap Λ : ℝ) ≤ qap * Λ :=
    Nat.floor_le (mul_nonneg hq hΛ.le)
  have hprod : (n.natAbs : ℝ) ≤ qap * Λ := hN.trans hfloor
  have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← coe_natAbs n]
    rfl
  rw [habs, div_le_iff₀ hΛ]
  linarith

lemma nAperture_lt_of_not_mem {qap Λ : ℝ} {n : ℤ} (hn : n ∉ modeSet qap Λ) :
    nAperture qap Λ < n.natAbs :=
  Nat.lt_of_not_ge (mt mem_modeSet_iff.mpr hn)

/-- Modes dropped by the aperture obey the `O(1/n²)` Bessel bound. -/
lemma besselJ_outside_modeSet (φ : ℝ) {qap Λ : ℝ} {n : ℤ}
    (hn : n ∉ modeSet qap Λ) :
    ‖besselJ n φ‖ ≤ (|φ| + φ ^ 2) / (n : ℝ) ^ 2 := by
  have h0 : n ≠ 0 := by
    intro h
    subst h
    have : (0 : ℤ) ∈ modeSet qap Λ := by
      rw [mem_modeSet_iff]
      exact Nat.zero_le _
    exact hn this
  exact besselJ_bound h0 φ

lemma norm_jacobi_term (n : ℤ) (φ θ : ℝ) :
    ‖besselJ n φ * cexp (I * n * θ)‖ = ‖besselJ n φ‖ := by
  rw [norm_mul]
  have h : I * (n : ℂ) * (θ : ℂ) = (n * θ : ℝ) * I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- FO image of a finite-mode object. `R n m` is the TCC sample at
`(n/Λ, m/Λ)`. One evaluation is a double sum of `modes.card²` terms. -/
def discreteFOImage (R : ℤ → ℤ → ℂ) (c : ℤ → ℂ) (modes : Finset ℤ)
    (Λ x : ℝ) : ℂ :=
  ∑ n ∈ modes, ∑ m ∈ modes,
    c n * star (c m) * R n m *
      cexp (2 * π * I * ((n : ℝ) - (m : ℝ)) * x / Λ)

/-- Sinusoidal object: coefficients are Bessel functions of a single `φ`. -/
def besselCoeffs (φ : ℝ) : ℤ → ℂ := fun n => besselJ n φ

/-- Forward model of Jacobi–Anger fitting: bilinear FO on the aperture
section of the Bessel ladder. -/
def sinusoidalFOImage (R : ℤ → ℤ → ℂ) (qap Λ φ x : ℝ) : ℂ :=
  discreteFOImage R (besselCoeffs φ) (modeSet qap Λ) Λ x

/-- Modes dropped by the aperture lie strictly outside the disk. -/
lemma mode_outside_aperture {qap Λ : ℝ} (hΛ : 0 < Λ) {n : ℤ}
    (hn : n ∉ modeSet qap Λ) : qap < |(n : ℝ)| / Λ := by
  have hne : n ≠ 0 := by
    intro h
    subst h
    exact hn (mem_modeSet_iff.mpr (Nat.zero_le _))
  have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← coe_natAbs n]
    rfl
  rw [habs, lt_div_iff₀ hΛ]
  have hlt := nAperture_lt_of_not_mem hn
  by_cases hmul : 0 ≤ qap * Λ
  · exact (Nat.floor_lt hmul).mp hlt
  · exact lt_trans (lt_of_not_ge hmul)
      (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hne))

lemma discreteFOImage_cexp_norm (n m : ℤ) (Λ x : ℝ) :
    ‖cexp (2 * π * I * ((n : ℝ) - (m : ℝ)) * x / Λ)‖ = 1 := by
  have h : (2 * π * I * ((n : ℝ) - (m : ℝ)) * x / Λ : ℂ)
      = ((2 * π * ((n : ℝ) - (m : ℝ)) * x / Λ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma discreteFOImage_term_norm (R : ℤ → ℤ → ℂ) (c : ℤ → ℂ) (n m : ℤ) (Λ x : ℝ) :
    ‖c n * star (c m) * R n m *
        cexp (2 * π * I * ((n : ℝ) - (m : ℝ)) * x / Λ)‖
      = ‖c n‖ * ‖c m‖ * ‖R n m‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_star, discreteFOImage_cexp_norm]
  ring

/-- Fourier coefficient of a finite-mode bilinear image at difference `ξ`.
This is the `ihat` pairing on a finite support (ℤ is not a `Fintype`). -/
def ihatModes (R : ℤ → ℤ → ℂ) (c : ℤ → ℂ) (modes : Finset ℤ) (ξ : ℤ) : ℂ :=
  ∑ n ∈ modes,
    if n - ξ ∈ modes then c n * star (c (n - ξ)) * R n (n - ξ) else 0

lemma ihatModes_eq_pairs (R : ℤ → ℤ → ℂ) (c : ℤ → ℂ) (modes : Finset ℤ) (ξ : ℤ) :
    ihatModes R c modes ξ
      = ∑ n ∈ modes, ∑ m ∈ modes,
          if n - m = ξ then c n * star (c m) * R n m else 0 := by
  unfold ihatModes
  refine Finset.sum_congr rfl fun n _ => ?_
  have hiff (m : ℤ) : n - m = ξ ↔ m = n - ξ := by
    constructor <;> intro h <;> linarith
  have hterm (m : ℤ) :
      (if n - m = ξ then c n * star (c m) * R n m else 0)
        = if m = n - ξ then c n * star (c m) * R n m else 0 := by
    simp [hiff m]
  simp_rw [hterm]
  rw [sum_ite_eq']

/-- Spatial FO image is the inverse Fourier sum of `ihatModes` (reindex `ξ = n-m`). -/
theorem discreteFOImage_eq_ihatModes (R : ℤ → ℤ → ℂ) (c : ℤ → ℂ)
    (modes : Finset ℤ) (Λ x : ℝ) {Ξ : Finset ℤ}
    (hΞ : ∀ n ∈ modes, ∀ m ∈ modes, n - m ∈ Ξ) :
    discreteFOImage R c modes Λ x
      = ∑ ξ ∈ Ξ, ihatModes R c modes ξ *
          cexp (2 * π * I * (ξ : ℝ) * x / Λ) := by
  set e : ℤ → ℂ := fun ξ => cexp (2 * π * I * (ξ : ℝ) * x / Λ)
  set f : ℤ → ℤ → ℂ := fun n m => c n * star (c m) * R n m
  have hphase (n m : ℤ) :
      cexp (2 * π * I * ((n : ℝ) - (m : ℝ)) * x / Λ) = e (n - m) := by
    unfold e
    congr 1
    simp [Int.cast_sub]
  have hL : discreteFOImage R c modes Λ x
      = ∑ n ∈ modes, ∑ m ∈ modes, f n m * e (n - m) := by
    unfold discreteFOImage f
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1
    exact hphase n m
  have hite (n m : ℤ) (hn : n ∈ modes) (hm : m ∈ modes) :
      f n m * e (n - m)
        = ∑ ξ ∈ Ξ, if n - m = ξ then f n m * e ξ else 0 := by
    have hξ : n - m ∈ Ξ := hΞ n hn m hm
    rw [sum_ite_eq, if_pos hξ]
  have hswap :
      ∑ n ∈ modes, ∑ m ∈ modes, ∑ ξ ∈ Ξ,
          (if n - m = ξ then f n m * e ξ else 0)
        = ∑ ξ ∈ Ξ, ∑ n ∈ modes, ∑ m ∈ modes,
            (if n - m = ξ then f n m else 0) * e ξ := by
    have h1 :
        ∑ n ∈ modes, ∑ m ∈ modes, ∑ ξ ∈ Ξ,
            (if n - m = ξ then f n m * e ξ else 0)
          = ∑ n ∈ modes, ∑ ξ ∈ Ξ, ∑ m ∈ modes,
              (if n - m = ξ then f n m * e ξ else 0) :=
      Finset.sum_congr rfl fun _ _ => sum_comm
    have h2 :
        ∑ n ∈ modes, ∑ ξ ∈ Ξ, ∑ m ∈ modes,
            (if n - m = ξ then f n m * e ξ else 0)
          = ∑ ξ ∈ Ξ, ∑ n ∈ modes, ∑ m ∈ modes,
              (if n - m = ξ then f n m * e ξ else 0) :=
      sum_comm
    rw [h1, h2]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun n _ =>
      Finset.sum_congr rfl fun m _ => ?_
    by_cases h : n - m = ξ <;> simp [h]
  have hrhs :
      ∑ ξ ∈ Ξ, ihatModes R c modes ξ * e ξ
        = ∑ n ∈ modes, ∑ m ∈ modes, f n m * e (n - m) := by
    have h1 :
        ∑ ξ ∈ Ξ, ihatModes R c modes ξ * e ξ
          = ∑ ξ ∈ Ξ, ∑ n ∈ modes, ∑ m ∈ modes,
              (if n - m = ξ then f n m else 0) * e ξ := by
      simp_rw [ihatModes_eq_pairs, Finset.sum_mul]
      simp [f]
    rw [h1, ← hswap]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    exact (hite n m hn hm).symm
  rw [hL, hrhs]

/-- FO kernel sampled on the Bessel ladder `n/Λ`. -/
def rFO (p : LEEM) (Λ Δz : ℝ) : ℤ → ℤ → ℂ :=
  fun n m => p.R_FO ((n : ℝ) / Λ) ((m : ℝ) / Λ) Δz

lemma rFO_eq_zero_of_not_mem (p : LEEM) {Λ Δz : ℝ} (hΛ : 0 < Λ)
    {n : ℤ} (hn : n ∉ modeSet p.qAp Λ) (m : ℤ) :
    rFO p Λ Δz n m = 0 ∧ rFO p Λ Δz m n = 0 := by
  have hq : p.qAp < |((n : ℝ) / Λ)| := by
    have := mode_outside_aperture hΛ hn
    rwa [abs_div, abs_of_pos hΛ]
  exact ⟨p.R_FO_eq_zero_of_outside (Or.inl hq),
    p.R_FO_eq_zero_of_outside (Or.inr hq)⟩

/-- Extra harmonics outside `modeSet` do not enter the FO image of `rFO`. -/
theorem discreteFOImage_rFO_restrict (p : LEEM) {Λ Δz : ℝ} (hΛ : 0 < Λ)
    (c : ℤ → ℂ) {S : Finset ℤ} (hS : modeSet p.qAp Λ ⊆ S) (x : ℝ) :
    discreteFOImage (rFO p Λ Δz) c S Λ x
      = discreteFOImage (rFO p Λ Δz) c (modeSet p.qAp Λ) Λ x := by
  set M := modeSet p.qAp Λ
  set f := fun n m : ℤ =>
    c n * star (c m) * rFO p Λ Δz n m *
      cexp (2 * π * I * ((n : ℝ) - (m : ℝ)) * x / Λ)
  have hzero n m (hn : n ∉ M) : f n m = 0 := by
    have hz := (rFO_eq_zero_of_not_mem (Δz := Δz) p hΛ hn m).1
    dsimp [f]
    rw [hz]
    simp
  have hzero' n m (hm : m ∉ M) : f n m = 0 := by
    have hz := (rFO_eq_zero_of_not_mem (Δz := Δz) p hΛ hm n).2
    dsimp [f]
    rw [hz]
    simp
  have houter :
      ∑ n ∈ S, ∑ m ∈ S, f n m = ∑ n ∈ M, ∑ m ∈ S, f n m :=
    (sum_subset hS fun n _ hnM => sum_eq_zero fun m _ => hzero n m hnM).symm
  have hinner :
      ∑ n ∈ M, ∑ m ∈ S, f n m = ∑ n ∈ M, ∑ m ∈ M, f n m :=
    Finset.sum_congr rfl fun n _ =>
      (sum_subset hS fun m _ hmM => hzero' n m hmM).symm
  simpa [discreteFOImage, f] using (houter.trans hinner)

/-- Triangle bound on harmonics omitted by the aperture truncation. -/
theorem discreteFOImage_sub_sinusoidal_le (R : ℤ → ℤ → ℂ)
    (qap Λ φ x : ℝ) {S : Finset ℤ} (hS : modeSet qap Λ ⊆ S) :
    ‖discreteFOImage R (besselCoeffs φ) S Λ x
        - sinusoidalFOImage R qap Λ φ x‖
      ≤ ∑ n ∈ S, ∑ m ∈ S,
          if n ∈ modeSet qap Λ ∧ m ∈ modeSet qap Λ then (0 : ℝ)
          else ‖besselJ n φ‖ * ‖besselJ m φ‖ * ‖R n m‖ := by
  set M := modeSet qap Λ
  set c := besselCoeffs φ
  set a := fun n m : ℤ =>
    c n * star (c m) * R n m *
      cexp (2 * π * I * ((n : ℝ) - (m : ℝ)) * x / Λ)
  have hterm n m : ‖a n m‖ = ‖c n‖ * ‖c m‖ * ‖R n m‖ :=
    discreteFOImage_term_norm R c n m Λ x
  have hdecomp n m :
      a n m
        = (if n ∈ M ∧ m ∈ M then a n m else 0)
          + (if n ∈ M ∧ m ∈ M then 0 else a n m) := by
    by_cases h : n ∈ M ∧ m ∈ M <;> simp [h]
  have hsum :
      ∑ n ∈ S, ∑ m ∈ S, a n m
        = (∑ n ∈ S, ∑ m ∈ S, if n ∈ M ∧ m ∈ M then a n m else 0)
          + (∑ n ∈ S, ∑ m ∈ S, if n ∈ M ∧ m ∈ M then 0 else a n m) := by
    have hinner (n : ℤ) :
        ∑ m ∈ S, a n m
          = (∑ m ∈ S, if n ∈ M ∧ m ∈ M then a n m else 0)
            + (∑ m ∈ S, if n ∈ M ∧ m ∈ M then 0 else a n m) := by
      rw [← sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => hdecomp n m
    rw [← sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => hinner n
  have hM :
      ∑ n ∈ S, ∑ m ∈ S, (if n ∈ M ∧ m ∈ M then a n m else 0)
        = ∑ n ∈ M, ∑ m ∈ M, a n m := by
    trans ∑ n ∈ M, ∑ m ∈ S, (if n ∈ M ∧ m ∈ M then a n m else 0)
    · refine (sum_subset hS ?_).symm
      intro n _ hnM
      exact sum_eq_zero fun m _ => by simp [hnM]
    · refine Finset.sum_congr rfl fun n hn => ?_
      trans ∑ m ∈ M, (if n ∈ M ∧ m ∈ M then a n m else 0)
      · refine (sum_subset hS ?_).symm
        intro m _ hmM
        simp [hn, hmM]
      · exact Finset.sum_congr rfl fun m hm => by simp [hn, hm]
  have haS : discreteFOImage R c S Λ x = ∑ n ∈ S, ∑ m ∈ S, a n m := by
    simp [discreteFOImage, a]
  have haM : sinusoidalFOImage R qap Λ φ x = ∑ n ∈ M, ∑ m ∈ M, a n m := by
    simp [discreteFOImage, sinusoidalFOImage, a, c, M]
  have hdiff :
      discreteFOImage R c S Λ x - sinusoidalFOImage R qap Λ φ x
        = ∑ n ∈ S, ∑ m ∈ S, (if n ∈ M ∧ m ∈ M then 0 else a n m) := by
    rw [haS, haM, hsum, hM, add_sub_cancel_left]
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun m _ => ?_
  by_cases h : n ∈ M ∧ m ∈ M
  · simp [h]
  · simp only [h, ite_false]
    rw [hterm]
    simp [c, besselCoeffs]

/-- Difference frequencies of `modeSet`: `|ξ| ≤ 2 nAperture`. -/
def modeDiffSet (qap Λ : ℝ) : Finset ℤ :=
  Icc (-(2 * nAperture qap Λ : ℤ)) (2 * nAperture qap Λ)

lemma mem_modeDiffSet {qap Λ : ℝ} {n m : ℤ}
    (hn : n ∈ modeSet qap Λ) (hm : m ∈ modeSet qap Λ) :
    n - m ∈ modeDiffSet qap Λ := by
  rw [modeSet, mem_Icc] at hn hm
  rw [modeDiffSet, mem_Icc]
  constructor <;> linarith

/-- Spatial FO image on `modeSet` is the inverse Fourier sum of `ihatModes`. -/
theorem discreteFOImage_eq_ihatModes_modeSet (R : ℤ → ℤ → ℂ)
    (qap Λ : ℝ) (c : ℤ → ℂ) (x : ℝ) :
    discreteFOImage R c (modeSet qap Λ) Λ x
      = ∑ ξ ∈ modeDiffSet qap Λ, ihatModes R c (modeSet qap Λ) ξ *
          cexp (2 * π * I * (ξ : ℝ) * x / Λ) :=
  discreteFOImage_eq_ihatModes R c (modeSet qap Λ) Λ x fun _ hn _ hm =>
    mem_modeDiffSet hn hm

theorem sinusoidalFOImage_eq_ihatModes (R : ℤ → ℤ → ℂ)
    (qap Λ φ x : ℝ) :
    sinusoidalFOImage R qap Λ φ x
      = ∑ ξ ∈ modeDiffSet qap Λ,
          ihatModes R (besselCoeffs φ) (modeSet qap Λ) ξ *
            cexp (2 * π * I * (ξ : ℝ) * x / Λ) :=
  discreteFOImage_eq_ihatModes_modeSet R qap Λ (besselCoeffs φ) x

/-- Least-squares cost of the 1D Jacobi–Anger estimator (no iterative solver). -/
def sinusoidJ (R : ℤ → ℤ → ℂ) (qap Λ : ℝ) (I : ℝ → ℂ) (xs : Finset ℝ)
    (φ : ℝ) : ℝ :=
  ∑ x ∈ xs, ‖sinusoidalFOImage R qap Λ φ x - I x‖ ^ 2

end
