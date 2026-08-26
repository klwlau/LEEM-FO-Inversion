/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Instrument parameters and the proposed FO functions

Spatial-frequency form with `χ` in **waves** and `W = exp(2π i χ)`.
See `docs/FORMALIZATION.md`.

The field `LEEM.lam` is the electron wavelength after acceleration (paper `λ`).
Lean reserves `λ` for function abstraction, so the identifier is `lam`.
-/

open Complex Real
open scoped ComplexConjugate RealInnerProductSpace

/-- Column and aberration parameters for one LEEM imaging condition. -/
structure LEEM where
  /-- Wavelength after acceleration (paper `λ`). -/
  lam : ℝ
  /-- Nominal column energy. -/
  E : ℝ
  /-- Third-order spherical aberration. -/
  C3 : ℝ
  /-- Fifth-order spherical aberration. -/
  C5 : ℝ
  /-- First-order chromatic aberration `C_C`. -/
  CC : ℝ
  /-- Second-degree chromatic aberration `C_CC`. -/
  CCC : ℝ
  /-- Mixed `C_{3C}`. -/
  C3C : ℝ
  /-- Contrast-aperture cutoff frequency `q_ap = α_ap / λ`. -/
  qAp : ℝ
  /-- FWHM of the source density in spatial-frequency units. -/
  qIll : ℝ
  /-- FWHM of the energy spread. -/
  ΔE : ℝ

namespace LEEM

variable (p : LEEM)

/-- Wavelength and column energy are positive. -/
def IsPhysical : Prop := 0 < p.lam ∧ 0 < p.E

/-- Aberration-corrected specialisation: `C₃ = C_C = 0`. -/
def IsAC : Prop := p.C3 = 0 ∧ p.CC = 0

/-- Non-corrected specialisation: drop fifth-order and higher-rank chromatic terms. -/
def IsNAC : Prop := p.C5 = 0 ∧ p.CCC = 0 ∧ p.C3C = 0

/-- Object wave `ψ₀(r) = σ(r) exp(i φ(r))` with `φ` in radians. -/
noncomputable def objectWave (σ φ : ℝ → ℝ) (r : ℝ) : ℂ :=
  (σ r : ℂ) * cexp (I * (φ r : ℂ))

/-- Circular contrast aperture `M(q)`. -/
noncomputable def aperture (q : ℝ) : ℝ :=
  if |q| ≤ p.qAp then 1 else 0

/-- Two-dimensional circular aperture on Euclidean 2-space. -/
noncomputable def aperture2 (q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if ‖q‖ ≤ p.qAp then 1 else 0

/-- Wave aberration `χ_S(q, Δz)` in waves (1D signed spatial frequency). -/
noncomputable def chiS (q Δz : ℝ) : ℝ :=
  (1 / 4 : ℝ) * p.C3 * p.lam ^ 3 * q ^ 4
    + (1 / 6 : ℝ) * p.C5 * p.lam ^ 5 * q ^ 6
    + (1 / 2 : ℝ) * Δz * p.lam * q ^ 2

/-- Radial `χ_S` on Euclidean 2-space. -/
noncomputable def chiS2 (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) : ℝ :=
  (1 / 4 : ℝ) * p.C3 * p.lam ^ 3 * ‖q‖ ^ 4
    + (1 / 6 : ℝ) * p.C5 * p.lam ^ 5 * ‖q‖ ^ 6
    + (1 / 2 : ℝ) * Δz * p.lam * ‖q‖ ^ 2

/-- Transfer factor `W_S = exp(2π i χ_S)`. -/
noncomputable def waveS (q Δz : ℝ) : ℂ :=
  cexp (2 * π * I * (p.chiS q Δz : ℂ))

/-- Chromatic path `χ_C(q, ε)` in waves. -/
noncomputable def chiC (q ε : ℝ) : ℝ :=
  (1 / 2 : ℝ) * p.CC * p.lam * (ε / p.E) * q ^ 2
    + (1 / 2 : ℝ) * p.CCC * p.lam * (ε / p.E) ^ 2 * q ^ 2
    + (1 / 4 : ℝ) * p.C3C * p.lam ^ 3 * (ε / p.E) * q ^ 4

/-- Transfer factor `W_C = exp(2π i χ_C)`. -/
noncomputable def waveC (q ε : ℝ) : ℂ :=
  cexp (2 * π * I * (p.chiC q ε : ℂ))

/-- Coherent bilinear kernel `R₀` (paper Eq. (2)). -/
noncomputable def R0 (q q' Δz ε : ℝ) : ℂ :=
  (p.aperture q : ℂ) * (p.aperture q' : ℂ)
    * p.waveS q Δz * conj (p.waveS q' Δz)
    * p.waveC q ε * conj (p.waveC q' ε)

/-- Linear coefficient `b₁` in `χ_C(q,ε) - χ_C(q',ε) = b₁ ε + b₂ ε²`. -/
noncomputable def b1 (q q' : ℝ) : ℝ :=
  p.CC * p.lam / (2 * p.E) * (q ^ 2 - q' ^ 2)
    + p.C3C * p.lam ^ 3 / (4 * p.E) * (q ^ 4 - q' ^ 4)

/-- Quadratic coefficient `b₂`. -/
noncomputable def b2 (q q' : ℝ) : ℝ :=
  p.CCC * p.lam / (2 * p.E ^ 2) * (q ^ 2 - q' ^ 2)

/-- 1D illumination-tilt factor `a = ∂_q χ_S(q) - ∂_q χ_S(q')`. -/
noncomputable def aS (q q' Δz : ℝ) : ℝ :=
  p.C3 * p.lam ^ 3 * (q ^ 3 - q' ^ 3)
    + p.C5 * p.lam ^ 5 * (q ^ 5 - q' ^ 5)
    + Δz * p.lam * (q - q')

@[simp] lemma aperture_of_le {q : ℝ} (h : |q| ≤ p.qAp) :
    p.aperture q = 1 := if_pos h

@[simp] lemma aperture_of_gt {q : ℝ} (h : p.qAp < |q|) :
    p.aperture q = 0 := if_neg (not_le.mpr h)

lemma aperture_eq_zero_or_one (q : ℝ) :
    p.aperture q = 0 ∨ p.aperture q = 1 := by
  by_cases h : |q| ≤ p.qAp
  · exact Or.inr (p.aperture_of_le h)
  · exact Or.inl (p.aperture_of_gt (lt_of_not_ge h))

lemma aperture_nonneg (q : ℝ) : 0 ≤ p.aperture q := by
  rcases p.aperture_eq_zero_or_one q with h | h <;> simp [h]

lemma aperture2_eq_zero_or_one (q : EuclideanSpace ℝ (Fin 2)) :
    p.aperture2 q = 0 ∨ p.aperture2 q = 1 := by
  by_cases h : ‖q‖ ≤ p.qAp
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

@[simp] lemma aperture2_of_le {q : EuclideanSpace ℝ (Fin 2)} (h : ‖q‖ ≤ p.qAp) :
    p.aperture2 q = 1 := if_pos h

@[simp] lemma aperture2_of_gt {q : EuclideanSpace ℝ (Fin 2)} (h : p.qAp < ‖q‖) :
    p.aperture2 q = 0 := if_neg (not_le.mpr h)

lemma aperture2_eq_aperture (q : EuclideanSpace ℝ (Fin 2)) :
    p.aperture2 q = p.aperture ‖q‖ := by
  simp [aperture2, aperture, abs_of_nonneg (norm_nonneg q)]

/-- Radial `χ_S` agrees with the 1D formula on the Euclidean radius. -/
lemma chiS2_eq_chiS (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.chiS2 q Δz = p.chiS ‖q‖ Δz := rfl

/-- Transfer factor `W_S` on Euclidean 2-space. -/
noncomputable def waveS2 (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) : ℂ :=
  cexp (2 * π * I * (p.chiS2 q Δz : ℂ))

lemma waveS2_eq_waveS (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.waveS2 q Δz = p.waveS ‖q‖ Δz := rfl

/-- Radial prefactor of `∇χ_S`: `∇χ_S(q) = u_S(q) • q`. -/
noncomputable def uS (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) : ℝ :=
  p.C3 * p.lam ^ 3 * ‖q‖ ^ 2 + p.C5 * p.lam ^ 5 * ‖q‖ ^ 4 + Δz * p.lam

/-- Two-dimensional illumination-tilt vector `a = ∇χ_S(q) - ∇χ_S(q')`. -/
noncomputable def aS2 (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  p.uS q Δz • q - p.uS q' Δz • q'

lemma aS2_neg (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.aS2 q q' Δz = -p.aS2 q' q Δz := by
  simp [aS2, neg_sub]

lemma aS2_axis (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.aS2 q 0 Δz = p.uS q Δz • q := by
  simp [aS2]

lemma uS_mul_norm (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.uS q Δz * ‖q‖ = p.aS ‖q‖ 0 Δz := by
  simp [uS, aS]
  ring

/-- Coherent pupil `M(q) W_S(q) W_C(q)`: `R₀` is rank-1 in this factor. -/
noncomputable def coherentPupil (Δz ε q : ℝ) : ℂ :=
  (p.aperture q : ℂ) * p.waveS q Δz * p.waveC q ε

/-- Coherent kernel is exactly rank-1: `R₀(q,q') = P(q) conj(P(q'))`. -/
theorem R0_eq_rank1 (q q' Δz ε : ℝ) :
    p.R0 q q' Δz ε
      = p.coherentPupil Δz ε q * conj (p.coherentPupil Δz ε q') := by
  unfold R0 coherentPupil
  simp [map_mul, conj_ofReal]
  ac_rfl

lemma coherentPupil_zero_energy (Δz q : ℝ) :
    p.coherentPupil Δz 0 q = (p.aperture q : ℂ) * p.waveS q Δz := by
  simp [coherentPupil, waveC, chiC]

/-- Two-dimensional coherent kernel on Euclidean frequencies. -/
noncomputable def R0_2 (q q' : EuclideanSpace ℝ (Fin 2)) (Δz ε : ℝ) : ℂ :=
  (p.aperture2 q : ℂ) * (p.aperture2 q' : ℂ)
    * p.waveS2 q Δz * conj (p.waveS2 q' Δz)
    * p.waveC ‖q‖ ε * conj (p.waveC ‖q'‖ ε)

theorem R0_2_eq_R0 (q q' : EuclideanSpace ℝ (Fin 2)) (Δz ε : ℝ) :
    p.R0_2 q q' Δz ε = p.R0 ‖q‖ ‖q'‖ Δz ε := by
  unfold R0_2 R0
  rw [p.aperture2_eq_aperture, p.aperture2_eq_aperture,
    p.waveS2_eq_waveS, p.waveS2_eq_waveS]

theorem R0_2_hermitian (q q' : EuclideanSpace ℝ (Fin 2)) (Δz ε : ℝ) :
    conj (p.R0_2 q q' Δz ε) = p.R0_2 q' q Δz ε := by
  simp only [R0_2, map_mul, conj_ofReal, conj_conj]
  ac_rfl

/-- Two-dimensional coherent pupil `M(q) W_S(q) W_C(q)`. -/
noncomputable def coherentPupil2 (Δz ε : ℝ) (q : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (p.aperture2 q : ℂ) * p.waveS2 q Δz * p.waveC ‖q‖ ε

lemma coherentPupil2_eq_coherentPupil (Δz ε : ℝ) (q : EuclideanSpace ℝ (Fin 2)) :
    p.coherentPupil2 Δz ε q = p.coherentPupil Δz ε ‖q‖ := by
  simp [coherentPupil2, coherentPupil, aperture2_eq_aperture, waveS2_eq_waveS]

theorem R0_2_eq_rank1 (q q' : EuclideanSpace ℝ (Fin 2)) (Δz ε : ℝ) :
    p.R0_2 q q' Δz ε
      = p.coherentPupil2 Δz ε q * conj (p.coherentPupil2 Δz ε q') := by
  rw [p.R0_2_eq_R0, p.R0_eq_rank1, p.coherentPupil2_eq_coherentPupil,
    p.coherentPupil2_eq_coherentPupil]

private lemma conj_two_pi_I_ofReal (x : ℝ) :
    conj (2 * π * I * (x : ℂ)) = -(2 * π * I * (x : ℂ)) := by
  rw [map_mul, map_mul, map_mul, conj_ofNat, conj_ofReal, conj_I, conj_ofReal]
  ring

/-- `conj (W_S(q')) = exp(-2π i χ_S(q'))`. -/
lemma conj_waveS (q Δz : ℝ) :
    conj (p.waveS q Δz) = cexp (-(2 * π * I * (p.chiS q Δz : ℂ))) := by
  unfold waveS
  rw [← exp_conj, conj_two_pi_I_ofReal]

/-- `W_S(q) W_S(q')*` is the pure phase `exp(2π i (χ_S(q)-χ_S(q')))`. -/
lemma waveS_mul_conj (q q' Δz : ℝ) :
    p.waveS q Δz * conj (p.waveS q' Δz)
      = cexp (2 * π * I * ((p.chiS q Δz - p.chiS q' Δz : ℝ) : ℂ)) := by
  rw [p.conj_waveS q' Δz, waveS, ← Complex.exp_add]
  congr 1
  simp [ofReal_sub]
  ring

lemma conj_waveC (q ε : ℝ) :
    conj (p.waveC q ε) = cexp (-(2 * π * I * (p.chiC q ε : ℂ))) := by
  unfold waveC
  rw [← exp_conj, conj_two_pi_I_ofReal]

lemma waveC_mul_conj (q q' ε : ℝ) :
    p.waveC q ε * conj (p.waveC q' ε)
      = cexp (2 * π * I * ((p.chiC q ε - p.chiC q' ε : ℝ) : ℂ)) := by
  rw [p.conj_waveC q' ε, waveC, ← Complex.exp_add]
  congr 1
  simp [ofReal_sub]
  ring

lemma waveC_at_zero (q : ℝ) : p.waveC q 0 = 1 := by
  simp [waveC, chiC]

lemma R0_at_zero_energy (q q' Δz : ℝ) :
    p.R0 q q' Δz 0
      = (p.aperture q : ℂ) * (p.aperture q' : ℂ)
        * p.waveS q Δz * conj (p.waveS q' Δz) := by
  simp [R0, p.waveC_at_zero]

end LEEM
