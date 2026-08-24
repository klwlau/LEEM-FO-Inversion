/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.CTF

/-!
# Envelope ratios `Γ_C`, `Γ_S` (paper Eqs. (7a)–(7b) and Appendix A2)
-/

open Complex Real
open scoped ComplexConjugate

namespace LEEM

variable (p : LEEM)

/-- Spatial ratio `Γ_S` (Eq. (7b)). -/
noncomputable def gammaS (q q' Δz : ℝ) : ℂ :=
  p.spatialEnvelopeClosed q 0 Δz * p.spatialEnvelopeClosed q' 0 Δz
    / p.spatialEnvelopeClosed q q' Δz

/-- Chromatic ratio `Γ_C` as printed in Eq. (7a) (no extra conjugate). -/
noncomputable def gammaC (q q' : ℝ) : ℂ :=
  chromaticEnvelopeClosed p.sigmaE (p.b1 q 0) (p.b2 q 0)
    * chromaticEnvelopeClosed p.sigmaE (p.b1 q' 0) (p.b2 q' 0)
    / chromaticEnvelopeClosed p.sigmaE (p.b1 q q') (p.b2 q q')

/-- Amplitude plotted in the paper’s Fig. 1. -/
noncomputable def gammaC_abs (q q' : ℝ) : ℝ := ‖p.gammaC q q'‖

private lemma deriv_chiS_zero (Δz : ℝ) : deriv (p.chiS · Δz) 0 = 0 := by
  rw [p.deriv_chiS]; ring

private lemma aS_axis' (q Δz : ℝ) :
    p.aS q 0 Δz = deriv (p.chiS · Δz) q := by
  rw [p.aS_eq_deriv_sub, p.deriv_chiS_zero, sub_zero]

/-- Algebra of Gaussians: `Γ_S = exp(-4π² σ_ill² u v)` with `u = χ'(q)`, `v = χ'(q')`. -/
theorem gammaS_eq_dot (q q' Δz : ℝ) :
    p.gammaS q q' Δz
      = cexp (-(4 : ℂ) * π ^ 2 * p.sigmaIll ^ 2
          * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q') := by
  unfold gammaS spatialEnvelopeClosed
  rw [p.aS_axis' q Δz, p.aS_axis' q' Δz, p.aS_eq_deriv_sub]
  simp [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-- Equivalent packaging with `κ = π² q_ill² / (4 ln 2)`.
Then `2κ` matches the end of A2. -/
theorem gammaS_eq_kappa (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.gammaS q q' Δz
      = cexp (-(2 : ℂ) * kappaIll p.qIll
          * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q') := by
  have hk := (kappaIll_eq_sigma (p.sigmaIll_pos h) (p.sigmaIll_eq h)).symm
  rw [p.gammaS_eq_dot]
  apply congrArg Complex.exp
  have hL :
      (-(4 : ℂ) * π ^ 2 * p.sigmaIll ^ 2
          * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q')
        = Complex.ofReal
            (-(4 : ℝ) * π ^ 2 * p.sigmaIll ^ 2
              * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q') := by
    push_cast
    ring
  have hR :
      (-(2 : ℂ) * kappaIll p.qIll
          * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q')
        = Complex.ofReal
            (-(2 : ℝ) * kappaIll p.qIll
              * deriv (p.chiS · Δz) q * deriv (p.chiS · Δz) q') := by
    push_cast
    ring
  rw [hL, hR, ofReal_inj, hk]
  ring

/-- 1D ac formula at the end of A2. -/
theorem gammaS_ac (hAC : p.IsAC) (h : 0 < p.qIll) (q q' Δz : ℝ) :
    p.gammaS q q' Δz
      = cexp (-(2 : ℂ) * kappaIll p.qIll
          * (p.C5 * p.lam ^ 5 * q ^ 5 + Δz * p.lam * q)
          * (p.C5 * p.lam ^ 5 * q' ^ 5 + Δz * p.lam * q')) := by
  rw [p.gammaS_eq_kappa h, p.deriv_chiS, p.deriv_chiS]
  unfold IsAC at hAC
  rcases hAC with ⟨hC3, _⟩
  simp [hC3]

/-- Axes: `q' = 0` implies `Γ_S = 1`. -/
theorem gammaS_axis (q Δz : ℝ) : p.gammaS q 0 Δz = 1 := by
  unfold gammaS
  rw [p.spatialEnvelopeClosed_diag 0 Δz, mul_one, div_self]
  exact Complex.exp_ne_zero _

/-- Perfect spatial coherence (`σ_ill = 0`) implies `Γ_S = 1`. -/
theorem gammaS_perfect (hσ : p.sigmaIll = 0) (q q' Δz : ℝ) :
    p.gammaS q q' Δz = 1 := by
  unfold gammaS
  simp [p.spatialEnvelopeClosed_of_sigma_zero, hσ]

/-- Perfect chromatic coherence (`σ_E = 0`) implies `Γ_C = 1`. -/
theorem gammaC_perfect (hσ : p.sigmaE = 0) (q q' : ℝ) :
    p.gammaC q q' = 1 := by
  unfold gammaC
  simp [hσ, chromaticEnvelopeClosed_of_sigma_zero]

lemma chromaticEnvelopeClosed_ne_zero (σ b1 b2 : ℝ) :
    chromaticEnvelopeClosed σ b1 b2 ≠ 0 := by
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  unfold ecc
  rw [cpow_ne_zero_iff]
  exact Or.inl (eccDenom_ne_zero _ _)

/-- Axes: `q' = 0` implies `Γ_C = 1`. -/
theorem gammaC_axis (q : ℝ) : p.gammaC q 0 = 1 := by
  unfold gammaC
  rw [p.b1_zero_diag, p.b2_zero_diag]
  have h00 : chromaticEnvelopeClosed p.sigmaE 0 0 = 1 := by
    rw [chromaticEnvelopeClosed_nac]
    simp
  rw [h00, mul_one, div_self]
  exact chromaticEnvelopeClosed_ne_zero _ _ _

/-- Axes: `q = 0` implies `Γ_S = 1`. -/
theorem gammaS_axis_q (q' Δz : ℝ) : p.gammaS 0 q' Δz = 1 := by
  unfold gammaS
  rw [p.spatialEnvelopeClosed_diag 0 Δz, p.spatialEnvelopeClosed_symm 0 q' Δz,
    one_mul, div_self]
  exact Complex.exp_ne_zero _

/-- Axes: `q = 0` implies `Γ_C` has modulus 1 after swapping
`b₁,b₂` signs; the printed product equals 1 on `q' = 0` (`gammaC_axis`). -/
lemma b1_swap (q q' : ℝ) : p.b1 q q' = -p.b1 q' q := by
  simp [b1]
  ring

lemma b2_swap (q q' : ℝ) : p.b2 q q' = -p.b2 q' q := by
  simp [b2]
  ring

/-- Axes: `q = 0` implies `|Γ_C| = 1`. -/
theorem gammaC_norm_axis_q (h : 0 < p.ΔE) (q' : ℝ) :
    ‖p.gammaC 0 q'‖ = 1 := by
  unfold gammaC
  set E := chromaticEnvelopeClosed p.sigmaE (p.b1 q' 0) (p.b2 q' 0)
  set F := chromaticEnvelopeClosed p.sigmaE (p.b1 0 q') (p.b2 0 q')
  have h00 : chromaticEnvelopeClosed p.sigmaE (p.b1 0 0) (p.b2 0 0) = 1 := by
    rw [p.b1_zero_diag, p.b2_zero_diag, chromaticEnvelopeClosed_nac]
    simp
  have hF : F = conj E := by
    dsimp [E, F]
    rw [p.b1_swap 0 q', p.b2_swap 0 q']
    exact chromaticEnvelopeClosed_neg (p.sigmaE_pos h)
  have hz : E ≠ 0 := chromaticEnvelopeClosed_ne_zero _ _ _
  simp [h00, hF, hz]

/-- Product of ratios is 1 under perfect coherence (`q_ill = ΔE = 0`). -/
theorem gamma_product_perfect (h : p.PerfectCoherence) (q q' Δz : ℝ) :
    p.gammaC q q' * p.gammaS q q' Δz = 1 := by
  rw [p.gammaC_perfect (p.sigmaE_of_ΔE_zero h.2),
    p.gammaS_perfect (p.sigmaIll_of_qIll_zero h.1), one_mul]

/-- The printed CTF/FO comparison: `R_CTF = R_FO Γ_C Γ_S`
(using that `E_S` is real, so the spatial conjugate is redundant). -/
theorem R_CTF_eq_R_FO_mul_gamma (q q' Δz : ℝ) :
    p.R_CTF q q' Δz = p.R_FO q q' Δz * p.gammaC q q' * p.gammaS q q' Δz := by
  have hEs : p.spatialEnvelopeClosed q q' Δz ≠ 0 := Complex.exp_ne_zero _
  have hEc := chromaticEnvelopeClosed_ne_zero p.sigmaE (p.b1 q q') (p.b2 q q')
  unfold R_CTF R_FO gammaC gammaS
  rw [p.spatialCTF_conj q' Δz]
  unfold spatialCTF chromaticCTF
  field_simp [hEs, hEc]

end LEEM
