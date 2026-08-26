/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Forward.CTF
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

/-!
# Two-dimensional working FO kernel

The 1D kernel `R_FO` takes signed scalar frequencies. The 2D kernel uses the
disk aperture `aperture2`, radial `χ_S2`, and the vector tilt
`a = ∇χ_S(q) - ∇χ_S(q')`, so the spatial envelope sees `q · q'`.
On the CTF slice `q' = 0` this agrees with `R_FO ‖q‖ 0`. Off axis,
`R_FO2(q,q')` is *not* `R_FO(‖q‖,‖q'‖)`.
-/

open Complex Real
open scoped ComplexConjugate RealInnerProductSpace

namespace LEEM

variable (p : LEEM)

/-- Closed-form 2D spatial envelope `exp(-2π² σ_ill² ‖a‖²)`. -/
noncomputable def spatialEnvelopeClosed2
    (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) : ℂ :=
  cexp (Complex.ofReal
    (-(2 : ℝ) * π ^ 2 * p.sigmaIll ^ 2 * ‖p.aS2 q q' Δz‖ ^ 2))

lemma spatialEnvelopeClosed2_real (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    (p.spatialEnvelopeClosed2 q q' Δz).im = 0 :=
  Complex.exp_ofReal_im _

lemma spatialEnvelopeClosed2_symm (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.spatialEnvelopeClosed2 q q' Δz = p.spatialEnvelopeClosed2 q' q Δz := by
  unfold spatialEnvelopeClosed2
  rw [p.aS2_neg q q' Δz, norm_neg]

lemma aS2_axis_normSq (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    ‖p.aS2 q 0 Δz‖ ^ 2 = p.aS ‖q‖ 0 Δz ^ 2 := by
  rw [p.aS2_axis, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← p.uS_mul_norm]
  ring

lemma spatialEnvelopeClosed2_axis (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.spatialEnvelopeClosed2 q 0 Δz = p.spatialEnvelopeClosed ‖q‖ 0 Δz := by
  unfold spatialEnvelopeClosed2 spatialEnvelopeClosed
  rw [p.aS2_axis_normSq]

lemma chiS_even (q Δz : ℝ) : p.chiS (-q) Δz = p.chiS q Δz := by
  simp [chiS]
  ring

lemma waveS_even (q Δz : ℝ) : p.waveS (-q) Δz = p.waveS q Δz := by
  simp [waveS, p.chiS_even]

lemma chiC_even (q ε : ℝ) : p.chiC (-q) ε = p.chiC q ε := by
  unfold chiC
  have h2 : (-q) ^ 2 = q ^ 2 := by ring
  have h4 : (-q) ^ 4 = q ^ 4 := by ring
  rw [h2, h4]

lemma waveC_even (q ε : ℝ) : p.waveC (-q) ε = p.waveC q ε := by
  simp [waveC, p.chiC_even]

lemma aperture_neg (q : ℝ) : p.aperture (-q) = p.aperture q := by
  simp [aperture, abs_neg]

lemma aS_zero_right (r Δz : ℝ) : p.aS 0 r Δz = -p.aS r 0 Δz := by
  simp [aS]
  ring

lemma aS_zero_neg (r Δz : ℝ) : p.aS 0 (-r) Δz = p.aS r 0 Δz := by
  simp [aS]
  ring

lemma uS_neg (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.uS (-q) Δz = p.uS q Δz := by
  simp [uS]

lemma aS2_zero_neg (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.aS2 0 (-q) Δz = p.uS q Δz • q := by
  simp [aS2, p.uS_neg]

lemma aS2_zero_neg_normSq (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    ‖p.aS2 0 (-q) Δz‖ ^ 2 = p.aS ‖q‖ 0 Δz ^ 2 := by
  rw [p.aS2_zero_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ← p.uS_mul_norm]
  ring

lemma spatialEnvelopeClosed2_conj_axis (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.spatialEnvelopeClosed2 0 (-q) Δz
      = p.spatialEnvelopeClosed 0 (-‖q‖) Δz := by
  unfold spatialEnvelopeClosed2 spatialEnvelopeClosed
  rw [p.aS2_zero_neg_normSq, p.aS_zero_neg]

/-- Working 2D FO kernel: coherent rank-1 factor times 2D `E_S` times `E_C`. -/
noncomputable def R_FO2 (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) : ℂ :=
  p.R0_2 q q' Δz 0 * p.spatialEnvelopeClosed2 q q' Δz *
    chromaticEnvelopeClosed p.sigmaE (p.b1 ‖q‖ ‖q'‖) (p.b2 ‖q‖ ‖q'‖)

theorem R_FO2_eq_zero_of_outside {q q' : EuclideanSpace ℝ (Fin 2)} {Δz : ℝ}
    (h : p.qAp < ‖q‖ ∨ p.qAp < ‖q'‖) : p.R_FO2 q q' Δz = 0 := by
  unfold R_FO2
  rcases h with hq | hq'
  · simp [R0_2, p.aperture2_of_gt hq]
  · simp [R0_2, p.aperture2_of_gt hq']

/-- On the CTF slice the 2D kernel is the radial 1D slice. -/
theorem R_FO2_eq_R_FO_axis (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.R_FO2 q 0 Δz = p.R_FO ‖q‖ 0 Δz := by
  unfold R_FO2 R_FO
  rw [p.R0_2_eq_R0, p.spatialEnvelopeClosed2_axis]
  simp [norm_zero]

lemma b1_zero_even (r : ℝ) : p.b1 0 (-r) = p.b1 0 r := by
  unfold b1
  ring

lemma b2_zero_even (r : ℝ) : p.b2 0 (-r) = p.b2 0 r := by
  unfold b2
  ring

lemma spatialEnvelopeClosed_zero_even (r Δz : ℝ) :
    p.spatialEnvelopeClosed 0 (-r) Δz = p.spatialEnvelopeClosed 0 r Δz := by
  unfold spatialEnvelopeClosed
  rw [p.aS_zero_neg, p.aS_zero_right, neg_sq]

lemma R0_zero_even (r Δz ε : ℝ) : p.R0 0 (-r) Δz ε = p.R0 0 r Δz ε := by
  unfold R0
  rw [p.aperture_neg, p.waveS_even, p.waveC_even]

theorem R_FO_zero_even (r Δz : ℝ) : p.R_FO 0 (-r) Δz = p.R_FO 0 r Δz := by
  unfold R_FO
  rw [p.R0_zero_even, p.spatialEnvelopeClosed_zero_even, p.b1_zero_even,
    p.b2_zero_even]

/-- Conjugate vacuum branch: `R_FO2(0,-q) = R_FO(0,-‖q‖)`. -/
theorem R_FO2_eq_R_FO_conj_axis (q : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.R_FO2 0 (-q) Δz = p.R_FO 0 (-‖q‖) Δz := by
  unfold R_FO2 R_FO
  rw [p.R0_2_eq_R0, p.spatialEnvelopeClosed2_conj_axis, norm_zero, norm_neg,
    p.R0_zero_even, p.b1_zero_even, p.b2_zero_even]

theorem R_FO2_hermitian {q q' : EuclideanSpace ℝ (Fin 2)} {Δz : ℝ}
    (hσ : 0 ≤ p.sigmaE) :
    conj (p.R_FO2 q q' Δz) = p.R_FO2 q' q Δz := by
  unfold R_FO2
  rw [map_mul, map_mul, p.R0_2_hermitian,
    Complex.conj_eq_iff_im.mpr (p.spatialEnvelopeClosed2_real q q' Δz),
    p.spatialEnvelopeClosed2_symm, chromaticEnvelopeClosed_conj hσ,
    p.b1_swap, p.b2_swap]
  simp

lemma waveS2_zero (Δz : ℝ) : p.waveS2 0 Δz = 1 := by
  simp [waveS2, chiS2]

/-- DC bin of the 2D kernel is `1` on a physical aperture. -/
theorem R_FO2_dc {Δz : ℝ} (h0 : 0 ≤ p.qAp) :
    p.R_FO2 0 0 Δz = 1 := by
  have hap : p.aperture2 0 = 1 :=
    p.aperture2_of_le (by simpa using h0)
  have hχ : p.spatialEnvelopeClosed2 0 0 Δz = 1 := by
    unfold spatialEnvelopeClosed2
    simp [aS2]
  have hC : chromaticEnvelopeClosed p.sigmaE (p.b1 0 0) (p.b2 0 0) = 1 := by
    rw [p.b1_zero_diag, p.b2_zero_diag, chromaticEnvelopeClosed_nac]
    simp
  unfold R_FO2 R0_2
  have hnorm : ‖(0 : EuclideanSpace ℝ (Fin 2))‖ = 0 := norm_zero
  rw [p.waveC_at_zero, hap, hχ, p.waveS2_zero, hnorm, hC]
  simp

theorem spatialEnvelopeClosed2_of_sigma_zero
    (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) (h : p.sigmaIll = 0) :
    p.spatialEnvelopeClosed2 q q' Δz = 1 := by
  simp [spatialEnvelopeClosed2, h]

theorem R_FO2_eq_R0_2_of_perfect (h : p.PerfectCoherence)
    (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.R_FO2 q q' Δz = p.R0_2 q q' Δz 0 := by
  unfold R_FO2
  rw [p.spatialEnvelopeClosed2_of_sigma_zero q q' Δz (p.sigmaIll_of_qIll_zero h.1),
    p.chromaticEnvelope_of_perfect h ‖q‖ ‖q'‖]
  simp

theorem R_FO2_eq_rank1_of_perfect (h : p.PerfectCoherence)
    (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    p.R_FO2 q q' Δz
      = p.coherentPupil2 Δz 0 q * conj (p.coherentPupil2 Δz 0 q') := by
  rw [p.R_FO2_eq_R0_2_of_perfect h, p.R0_2_eq_rank1]

lemma aS2_normSq (q q' : EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    ‖p.aS2 q q' Δz‖ ^ 2
      = p.uS q Δz ^ 2 * ‖q‖ ^ 2 + p.uS q' Δz ^ 2 * ‖q'‖ ^ 2
        - 2 * p.uS q Δz * p.uS q' Δz * ⟪q, q'⟫ := by
  unfold aS2
  rw [norm_sub_sq_real]
  simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right]
  ring

end LEEM
