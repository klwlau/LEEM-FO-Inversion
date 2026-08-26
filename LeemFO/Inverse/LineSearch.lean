/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.Homotopy

/-!
# Exact quartic line energy of bilinear FO

Along a real ray `x0 + s • d` the FO residual is quadratic in `s`
(`lineResidual`). The stack fidelity is therefore a real quartic.
Stationarity is the cubic `lineCubic`; a unit Gauss–Newton step is not
automatically a root. Roots of that cubic are not constructed (no Cardano).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Complex Real
open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

noncomputable section

/-- Exact quadratic polynomial along a real step. Coercions match `lineResidual`. -/
def quadPoly (A B C : ℂ) (s : ℝ) : ℂ :=
  A + (s : ℂ) * B + (s : ℂ) ^ 2 * C

lemma norm_sq_ofReal_mul (s : ℝ) (z : ℂ) :
    ‖(s : ℂ) * z‖ ^ 2 = s ^ 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

lemma re_conj_mul_ofReal (z w : ℂ) (s : ℝ) :
    (conj z * ((s : ℂ) * w)).re = s * (conj z * w).re := by
  have : conj z * ((s : ℂ) * w) = (s : ℂ) * (conj z * w) := by ring
  rw [this, re_ofReal_mul]

lemma re_pow_mul (s : ℝ) (n : ℕ) (z : ℂ) :
    ((s : ℂ) ^ n * z).re = s ^ n * z.re := by
  rw [← ofReal_pow, re_ofReal_mul]

def quadA0 (A : ℂ) : ℝ := ‖A‖ ^ 2

def quadA1 (A B : ℂ) : ℝ := 2 * (conj A * B).re

def quadA2 (A B C : ℂ) : ℝ := ‖B‖ ^ 2 + 2 * (conj A * C).re

def quadA3 (B C : ℂ) : ℝ := 2 * (conj B * C).re

def quadA4 (C : ℂ) : ℝ := ‖C‖ ^ 2

def quadEnergy (A0 A1 A2 A3 A4 : ℝ) (s : ℝ) : ℝ :=
  A0 + A1 * s + A2 * s ^ 2 + A3 * s ^ 3 + A4 * s ^ 4

/-- Formal derivative of `quadEnergy` in `s` (no analytic `deriv`). -/
def lineCubic (A1 A2 A3 A4 : ℝ) (s : ℝ) : ℝ :=
  A1 + 2 * A2 * s + 3 * A3 * s ^ 2 + 4 * A4 * s ^ 3

theorem lineCubic_zero (A1 A2 A3 A4 : ℝ) :
    lineCubic A1 A2 A3 A4 0 = A1 := by
  simp [lineCubic]

theorem quadEnergy_shift (A0 A1 A2 A3 A4 : ℝ) (s h : ℝ) :
    quadEnergy A0 A1 A2 A3 A4 (s + h)
      = quadEnergy A0 A1 A2 A3 A4 s
        + h * lineCubic A1 A2 A3 A4 s
        + h ^ 2 * (A2 + 3 * A3 * s + 6 * A4 * s ^ 2)
        + h ^ 3 * (A3 + 4 * A4 * s)
        + h ^ 4 * A4 := by
  simp [quadEnergy, lineCubic]
  ring

/-- A unit Gauss–Newton step is not automatically a critical point of a
generic quartic. -/
theorem lineCubic_one_not_identically_zero :
    ¬∀ A1 A2 A3 A4 : ℝ, lineCubic A1 A2 A3 A4 1 = 0 := by
  intro h
  have := h 1 0 0 0
  simp [lineCubic] at this

theorem norm_sq_quadPoly (A B C : ℂ) (s : ℝ) :
    ‖quadPoly A B C s‖ ^ 2
      = quadEnergy (quadA0 A) (quadA1 A B) (quadA2 A B C)
          (quadA3 B C) (quadA4 C) s := by
  unfold quadPoly quadEnergy quadA0 quadA1 quadA2 quadA3 quadA4
  rw [norm_sq_add (A + (s : ℂ) * B) ((s : ℂ) ^ 2 * C)]
  rw [norm_sq_add A ((s : ℂ) * B)]
  have hB : ‖(s : ℂ) * B‖ ^ 2 = s ^ 2 * ‖B‖ ^ 2 :=
    norm_sq_ofReal_mul s B
  have hC : ‖(s : ℂ) ^ 2 * C‖ ^ 2 = s ^ 4 * ‖C‖ ^ 2 := by
    rw [← ofReal_pow s 2, norm_sq_ofReal_mul]
    ring
  have hAB : (conj A * ((s : ℂ) * B)).re = s * (conj A * B).re :=
    re_conj_mul_ofReal A B s
  have hAC : (conj A * ((s : ℂ) ^ 2 * C)).re = s ^ 2 * (conj A * C).re := by
    have : conj A * ((s : ℂ) ^ 2 * C) = (s : ℂ) ^ 2 * (conj A * C) := by ring
    rw [this, re_pow_mul]
  have hBC : (conj ((s : ℂ) * B) * ((s : ℂ) ^ 2 * C)).re
      = s ^ 3 * (conj B * C).re := by
    have :
        conj ((s : ℂ) * B) * ((s : ℂ) ^ 2 * C)
          = (s : ℂ) ^ 3 * (conj B * C) := by
      simp only [map_mul, conj_ofReal]
      ring
    rw [this, re_pow_mul]
  have hmid :
      (conj (A + (s : ℂ) * B) * ((s : ℂ) ^ 2 * C)).re
        = (conj A * ((s : ℂ) ^ 2 * C)).re
          + (conj ((s : ℂ) * B) * ((s : ℂ) ^ 2 * C)).re := by
    simp [map_add, add_mul, add_re]
  rw [hB, hC, hmid, hAB, hAC, hBC]
  ring

theorem quadEnergy_sum {ι : Type*} (A0 A1 A2 A3 A4 : ι → ℝ)
    (src : Finset ι) (s : ℝ) :
    ∑ i ∈ src, quadEnergy (A0 i) (A1 i) (A2 i) (A3 i) (A4 i) s
      = quadEnergy (∑ i ∈ src, A0 i) (∑ i ∈ src, A1 i)
          (∑ i ∈ src, A2 i) (∑ i ∈ src, A3 i) (∑ i ∈ src, A4 i) s := by
  simp [quadEnergy, Finset.sum_add_distrib, Finset.sum_mul]

def lineQuadA (R : G → G → ℂ) (y x0 : G → ℂ) (ξ : G) : ℂ :=
  y ξ - ihat R x0 ξ

def lineQuadB (R : G → G → ℂ) (x0 d : G → ℂ) (ξ : G) : ℂ :=
  -ihatJac R x0 d ξ

def lineQuadC (R : G → G → ℂ) (d : G → ℂ) (ξ : G) : ℂ :=
  -ihat R d ξ

theorem lineResidual_quadPoly (R : G → G → ℂ) (y x0 d : G → ℂ)
    (s : ℝ) (ξ : G) :
    lineResidual R y x0 d s ξ
      = quadPoly (lineQuadA R y x0 ξ) (lineQuadB R x0 d ξ)
          (lineQuadC R d ξ) s := by
  simp [lineResidual, quadPoly, lineQuadA, lineQuadB, lineQuadC]
  ring

/-- Linearized residual vanishes at `s = 1` (`B = -A`). The exact cubic at
that step is `4‖C‖² - 2 Re(conj A * C)`, not identically zero. -/
theorem lineCubic_exactGN (A C : ℂ) :
    lineCubic (quadA1 A (-A)) (quadA2 A (-A) C) (quadA3 (-A) C) (quadA4 C) 1
      = 4 * ‖C‖ ^ 2 - 2 * (conj A * C).re := by
  have h1 : quadA1 A (-A) = -2 * ‖A‖ ^ 2 := by
    unfold quadA1
    have hre : (conj A * A).re = ‖A‖ ^ 2 := by
      rw [mul_comm, mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]
    rw [mul_neg, neg_re, hre]
    ring
  have h2 : quadA2 A (-A) C = ‖A‖ ^ 2 + 2 * (conj A * C).re := by
    unfold quadA2
    simp [norm_neg]
  have h3 : quadA3 (-A) C = -2 * (conj A * C).re := by
    unfold quadA3
    have : conj (-A) * C = -(conj A * C) := by
      simp [map_neg]
    rw [this, neg_re]
    ring
  have h4 : quadA4 C = ‖C‖ ^ 2 := rfl
  rw [h1, h2, h3, h4]
  simp [lineCubic]
  ring

theorem lineCubic_exactGN_one_not_identically_zero :
    ¬∀ (A C : ℂ), C ≠ 0 →
      lineCubic (quadA1 A (-A)) (quadA2 A (-A) C)
        (quadA3 (-A) C) (quadA4 C) 1 = 0 := by
  intro h
  have hf := h 0 1 one_ne_zero
  have hval := lineCubic_exactGN (0 : ℂ) (1 : ℂ)
  rw [hval] at hf
  simp at hf

end

variable {κ : Type*} [Fintype κ]

noncomputable section

/-- Stack fidelity along the real ray (no Tikhonov penalty). -/
def lineFid (R : κ → G → G → ℂ) (y : κ → G → ℂ) (x0 d : G → ℂ) (s : ℝ) : ℝ :=
  ∑ k, ∑ ξ, ‖lineResidual (R k) (y k) x0 d s ξ‖ ^ 2

theorem lineFid_eq_nlsJfid (R : κ → G → G → ℂ) (y : κ → G → ℂ)
    (x0 d : G → ℂ) (s : ℝ) :
    lineFid R y x0 d s
      = ∑ k, ∑ ξ,
          ‖ihat (R k) (x0 + fun q => (s : ℂ) * d q) ξ - y k ξ‖ ^ 2 :=
  (nlsJfid_line R y x0 d s).symm

def stackA0 (R : κ → G → G → ℂ) (y : κ → G → ℂ) (x0 : G → ℂ) : ℝ :=
  ∑ k, ∑ ξ, quadA0 (lineQuadA (R k) (y k) x0 ξ)

def stackA1 (R : κ → G → G → ℂ) (y : κ → G → ℂ) (x0 d : G → ℂ) : ℝ :=
  ∑ k, ∑ ξ, quadA1 (lineQuadA (R k) (y k) x0 ξ) (lineQuadB (R k) x0 d ξ)

def stackA2 (R : κ → G → G → ℂ) (y : κ → G → ℂ) (x0 d : G → ℂ) : ℝ :=
  ∑ k, ∑ ξ, quadA2 (lineQuadA (R k) (y k) x0 ξ)
    (lineQuadB (R k) x0 d ξ) (lineQuadC (R k) d ξ)

def stackA3 (R : κ → G → G → ℂ) (x0 d : G → ℂ) : ℝ :=
  ∑ k, ∑ ξ, quadA3 (lineQuadB (R k) x0 d ξ) (lineQuadC (R k) d ξ)

def stackA4 (R : κ → G → G → ℂ) (d : G → ℂ) : ℝ :=
  ∑ k, ∑ ξ, quadA4 (lineQuadC (R k) d ξ)

theorem lineFid_quadEnergy (R : κ → G → G → ℂ) (y : κ → G → ℂ)
    (x0 d : G → ℂ) (s : ℝ) :
    lineFid R y x0 d s
      = quadEnergy (stackA0 R y x0) (stackA1 R y x0 d) (stackA2 R y x0 d)
          (stackA3 R x0 d) (stackA4 R d) s := by
  unfold lineFid stackA0 stackA1 stackA2 stackA3 stackA4
  have hξ (k : κ) :
      ∑ ξ, ‖lineResidual (R k) (y k) x0 d s ξ‖ ^ 2
        = quadEnergy
            (∑ ξ, quadA0 (lineQuadA (R k) (y k) x0 ξ))
            (∑ ξ, quadA1 (lineQuadA (R k) (y k) x0 ξ) (lineQuadB (R k) x0 d ξ))
            (∑ ξ, quadA2 (lineQuadA (R k) (y k) x0 ξ)
              (lineQuadB (R k) x0 d ξ) (lineQuadC (R k) d ξ))
            (∑ ξ, quadA3 (lineQuadB (R k) x0 d ξ) (lineQuadC (R k) d ξ))
            (∑ ξ, quadA4 (lineQuadC (R k) d ξ)) s := by
    simp_rw [lineResidual_quadPoly, norm_sq_quadPoly]
    exact quadEnergy_sum _ _ _ _ _ _ s
  simp_rw [hξ]
  exact quadEnergy_sum _ _ _ _ _ _ s

/-- Stationarity cubic of the FO line energy (no Cardano root). -/
def stackLineCubic (R : κ → G → G → ℂ) (y : κ → G → ℂ)
    (x0 d : G → ℂ) (s : ℝ) : ℝ :=
  lineCubic (stackA1 R y x0 d) (stackA2 R y x0 d) (stackA3 R x0 d)
    (stackA4 R d) s

theorem lineFid_shift (R : κ → G → G → ℂ) (y : κ → G → ℂ)
    (x0 d : G → ℂ) (s h : ℝ) :
    lineFid R y x0 d (s + h)
      = lineFid R y x0 d s
        + h * stackLineCubic R y x0 d s
        + h ^ 2 * (stackA2 R y x0 d + 3 * stackA3 R x0 d * s
            + 6 * stackA4 R d * s ^ 2)
        + h ^ 3 * (stackA3 R x0 d + 4 * stackA4 R d * s)
        + h ^ 4 * stackA4 R d := by
  simp [lineFid_quadEnergy, stackLineCubic, quadEnergy_shift]

end
