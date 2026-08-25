/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Int.Interval
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

end
