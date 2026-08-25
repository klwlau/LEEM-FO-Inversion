/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Filter.Cofinite

/-!
# Jacobi–Anger expansion of the sinusoidal phase object

Integer-order Bessel functions are realised as Fourier coefficients of
`θ ↦ exp(i φ sin θ)` on `(0, 2π]`. Summability of those coefficients (from two
integrations by parts) yields the pointwise expansion

\[
  \exp(i \varphi \sin \theta) = \sum_{n \in \mathbb{Z}} J_n(\varphi)\, e^{i n \theta}.
\]
-/

open Complex hiding log exp sin cos tan
open Real hiding log exp
open Filter Function MeasureTheory Set
open scoped Complex Interval

noncomputable section

/-- The circle of length `2π` is an `AddCircle`. -/
instance two_pi_pos_fact : Fact (0 < (2 * π : ℝ)) := ⟨Real.two_pi_pos⟩

/-- Object wave factor `exp(i φ sin θ)`. -/
def phaseFun (φ θ : ℝ) : ℂ :=
  cexp (I * φ * sin θ)

lemma phaseFun_periodic (φ : ℝ) : Periodic (phaseFun φ) (2 * π) :=
  sin_periodic.comp fun s => cexp (I * φ * s)

lemma phaseFun_period_eq (φ : ℝ) : phaseFun φ 0 = phaseFun φ (2 * π) :=
  (phaseFun_periodic φ).eq.symm

lemma phaseFun_norm (φ θ : ℝ) : ‖phaseFun φ θ‖ = 1 := by
  unfold phaseFun
  have h : I * (φ : ℂ) * (sin θ : ℂ) = I * (φ * sin θ : ℝ) := by
    push_cast
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

@[fun_prop]
lemma continuous_phaseFun (φ : ℝ) : Continuous (phaseFun φ) := by
  have h : phaseFun φ = fun θ => cexp (I * φ * (sin θ : ℂ)) := rfl
  rw [h]
  exact Complex.continuous_exp.comp (by fun_prop)

lemma hasDerivAt_phaseFun (φ θ : ℝ) :
    HasDerivAt (phaseFun φ) (I * φ * cos θ * phaseFun φ θ) θ := by
  have hs : HasDerivAt (fun t : ℝ => (sin t : ℂ)) (cos θ : ℂ) θ :=
    (Real.hasDerivAt_sin θ).ofReal_comp
  have hmul := HasDerivAt.const_mul (I * (φ : ℂ)) hs
  have hexp := hmul.cexp
  convert hexp using 1
  · rfl
  · simp [phaseFun, mul_comm, mul_left_comm, mul_assoc]

/-- First derivative of the phase factor. -/
def phaseFunDeriv (φ θ : ℝ) : ℂ :=
  I * φ * cos θ * phaseFun φ θ

lemma hasDerivAt_phaseFun_deriv (φ θ : ℝ) :
    HasDerivAt (phaseFun φ) (phaseFunDeriv φ θ) θ :=
  hasDerivAt_phaseFun φ θ

@[fun_prop]
lemma continuous_phaseFunDeriv (φ : ℝ) : Continuous (phaseFunDeriv φ) := by
  unfold phaseFunDeriv
  fun_prop

lemma phaseFunDeriv_period_eq (φ : ℝ) :
    phaseFunDeriv φ 0 = phaseFunDeriv φ (2 * π) := by
  simp [phaseFunDeriv, phaseFun_period_eq, Real.cos_two_pi, Real.cos_zero]

/-- Second derivative, used for an `O(1/n²)` Fourier-coefficient bound. -/
def phaseFunDeriv2 (φ θ : ℝ) : ℂ :=
  I * φ * (-sin θ) * phaseFun φ θ + (I * φ * cos θ) * phaseFunDeriv φ θ

lemma hasDerivAt_phaseFunDeriv (φ θ : ℝ) :
    HasDerivAt (phaseFunDeriv φ) (phaseFunDeriv2 φ θ) θ := by
  have hc : HasDerivAt (fun t : ℝ => (cos t : ℂ)) ((-sin θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_cos θ).ofReal_comp
  have hleft := HasDerivAt.const_mul (I * (φ : ℂ)) hc
  have hright := hasDerivAt_phaseFun φ θ
  have hprod := hleft.mul hright
  have hf : phaseFunDeriv φ = (fun y => I * (φ : ℂ) * (cos y : ℂ)) * phaseFun φ := rfl
  have hf' : phaseFunDeriv2 φ θ
      = I * (φ : ℂ) * ↑(-sin θ) * phaseFun φ θ
        + I * (φ : ℂ) * ↑(cos θ) * (I * (φ : ℂ) * ↑(cos θ) * phaseFun φ θ) := by
    unfold phaseFunDeriv2 phaseFunDeriv
    simp [ofReal_neg]
  rw [hf, hf']
  exact hprod

@[fun_prop]
lemma continuous_phaseFunDeriv2 (φ : ℝ) : Continuous (phaseFunDeriv2 φ) := by
  unfold phaseFunDeriv2 phaseFunDeriv
  fun_prop

lemma phaseFunDeriv2_norm_le (φ θ : ℝ) :
    ‖phaseFunDeriv2 φ θ‖ ≤ |φ| + φ ^ 2 := by
  unfold phaseFunDeriv2 phaseFunDeriv
  set a := I * (φ : ℂ) * (-(sin θ : ℂ)) * phaseFun φ θ
  set b := (I * (φ : ℂ) * (cos θ : ℂ)) *
      (I * (φ : ℂ) * (cos θ : ℂ) * phaseFun φ θ)
  have ha : ‖a‖ = |φ| * |sin θ| := by
    simp only [a, norm_mul, Complex.norm_I, phaseFun_norm, one_mul, mul_one, norm_neg]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hb : ‖b‖ = φ ^ 2 * |cos θ| ^ 2 := by
    simp only [b, norm_mul, Complex.norm_I, phaseFun_norm, one_mul, mul_one]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [mul_mul_mul_comm, ← sq, ← sq, sq_abs]
  calc
    ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ = |φ| * |sin θ| + φ ^ 2 * |cos θ| ^ 2 := by rw [ha, hb]
    _ ≤ |φ| * 1 + φ ^ 2 * 1 := by
      gcongr
      · exact abs_sin_le_one θ
      · exact pow_le_one₀ (abs_nonneg _) (abs_cos_le_one θ)
    _ = |φ| + φ ^ 2 := by ring

/-- Integer Bessel function as a Fourier coefficient on `[0, 2π]`. -/
def besselJ (n : ℤ) (φ : ℝ) : ℂ :=
  fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) (phaseFun φ) n

lemma fourier_two_pi (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * π)) = cexp (I * n * θ) := by
  rw [fourier_coe_apply]
  refine congrArg cexp ?_
  have hT : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Real.two_pi_pos)
  field_simp [hT]
  norm_cast
  ring

/-- Integration by parts: periodic endpoints cancel, leaving a factor `1/(I n)`. -/
lemma fourierCoeffOn_periodic_hasDeriv {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hper : f 0 = f (2 * π))
    (hf' : IntervalIntegrable f' volume 0 (2 * π)) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) f n
      = fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) f' n / (I * n) := by
  have hab : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have h := fourierCoeffOn_of_hasDerivAt hab hn (fun x _ => hf x) hf'
  have hgoal : fourierCoeffOn hab f n = fourierCoeffOn hab f' n / (I * n) := by
    rw [h, hper, sub_self, mul_zero, zero_sub]
    simp only [ofReal_zero, sub_zero]
    have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    set c := fourierCoeffOn hab f' n
    have hconst : (1 : ℂ) / (-2 * π * I * n) * -((2 * π : ℝ) : ℂ) = 1 / (I * n) := by
      simp only [ofReal_mul, ofReal_ofNat]
      field_simp [I_ne_zero, hnC, hπ]
    calc
      (1 : ℂ) / (-2 * π * I * n) * -(↑(2 * π) * c)
          = (1 / (-2 * π * I * n) * -↑(2 * π)) * c := by ring
      _ = (1 / (I * n)) * c := by rw [hconst]
      _ = c / (I * n) := by rw [one_div, mul_comm, div_eq_mul_inv]
  exact hgoal

lemma besselJ_eq_deriv_div {n : ℤ} (hn : n ≠ 0) (φ : ℝ) :
    besselJ n φ
      = fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) (phaseFunDeriv φ) n
          / (I * n) := by
  unfold besselJ
  exact fourierCoeffOn_periodic_hasDeriv hn (hasDerivAt_phaseFun_deriv φ)
    (phaseFun_period_eq φ) ((continuous_phaseFunDeriv φ).intervalIntegrable _ _)

lemma besselJ_eq_deriv2_div {n : ℤ} (hn : n ≠ 0) (φ : ℝ) :
    besselJ n φ
      = fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) (phaseFunDeriv2 φ) n
          / (I * n) ^ 2 := by
  rw [besselJ_eq_deriv_div hn]
  have h := fourierCoeffOn_periodic_hasDeriv (f := phaseFunDeriv φ) hn
    (hasDerivAt_phaseFunDeriv φ) (phaseFunDeriv_period_eq φ)
    ((continuous_phaseFunDeriv2 φ).intervalIntegrable _ _)
  rw [h, div_div, pow_two]

lemma fourierCoeffOn_norm_le {f : ℝ → ℂ} {n : ℤ} {M : ℝ}
    (hM : ∀ θ, ‖f θ‖ ≤ M) :
    ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) f n‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral]
  have hinter :
      ‖∫ x in (0 : ℝ)..(2 * π),
          fourier (-n) (x : AddCircle (2 * π - 0)) • f x‖
        ≤ M * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
    have hfou : ‖fourier (-n) (x : AddCircle (2 * π - 0))‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    rw [norm_smul, hfou, one_mul]
    exact hM x
  have hsc : ‖(1 / (2 * π - 0 : ℝ))‖ = (2 * π)⁻¹ := by
    simp only [sub_zero, one_div, Real.norm_eq_abs, abs_inv]
    rw [abs_of_pos Real.two_pi_pos]
  rw [norm_smul, hsc]
  have hsimp : (2 * π)⁻¹ * (M * |2 * π - 0|) = M := by
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    simp [abs_of_pos Real.two_pi_pos]
    field_simp [hπ]
  calc
    _ ≤ (2 * π)⁻¹ * (M * |2 * π - 0|) :=
      mul_le_mul_of_nonneg_left hinter (inv_nonneg.2 Real.two_pi_pos.le)
    _ = M := hsimp

lemma besselJ_bound {n : ℤ} (hn : n ≠ 0) (φ : ℝ) :
    ‖besselJ n φ‖ ≤ (|φ| + φ ^ 2) / (n : ℝ) ^ 2 := by
  have hcoeff := fourierCoeffOn_norm_le (n := n) (fun θ => phaseFunDeriv2_norm_le φ θ)
  have hdiv := besselJ_eq_deriv2_div hn φ
  have hn2 : ‖((I * n : ℂ) ^ 2)‖ = (n : ℝ) ^ 2 := by
    rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, sq_abs]
  have hnn : 0 < (n : ℝ) ^ 2 := sq_pos_iff.mpr (Int.cast_ne_zero.mpr hn)
  rw [hdiv, norm_div, hn2]
  exact div_le_div_of_nonneg_right hcoeff hnn.le

lemma summable_inv_sq : Summable fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2 :=
  (Real.summable_one_div_int_pow (p := 2)).mpr (by decide)

lemma summable_besselJ (φ : ℝ) : Summable fun n : ℤ => besselJ n φ := by
  have hg : Summable fun n : ℤ => (|φ| + φ ^ 2) / (n : ℝ) ^ 2 := by
    simpa [div_eq_mul_inv] using (summable_inv_sq.mul_left (|φ| + φ ^ 2))
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  exact besselJ_bound hn φ

/-- Continuous lift of the phase function to the circle of length `2π`. -/
def phaseOnCircle (φ : ℝ) : C(AddCircle (2 * π), ℂ) where
  toFun := AddCircle.liftIoc (2 * π) 0 (phaseFun φ)
  continuous_toFun :=
    AddCircle.liftIoc_zero_continuous (phaseFun_period_eq φ)
      (continuous_phaseFun φ).continuousOn

lemma phaseOnCircle_eq_of_mem (φ : ℝ) {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * π)) :
    phaseOnCircle φ (θ : AddCircle (2 * π)) = phaseFun φ θ := by
  change AddCircle.liftIoc (2 * π) 0 (phaseFun φ) ↑θ = phaseFun φ θ
  exact AddCircle.liftIoc_zero_coe_apply hθ

lemma fourierCoeff_phaseOnCircle (φ : ℝ) (n : ℤ) :
    fourierCoeff (phaseOnCircle φ) n = besselJ n φ := by
  simpa [phaseOnCircle, besselJ, zero_add, sub_zero] using
    (fourierCoeff_liftIoc_eq (T := 2 * π) (a := (0 : ℝ)) (phaseFun φ) n)

lemma exp_I_int_int_two_pi (n k : ℤ) :
    cexp (I * n * (k * (2 * π) : ℝ)) = 1 := by
  have h : I * (n : ℂ) * (k * (2 * π) : ℝ) = (n * k : ℤ) * (2 * π * I) := by
    push_cast
    ring
  rw [h, exp_int_mul_two_pi_mul_I]

lemma exp_I_n_sub_int_two_pi (n k : ℤ) (θ : ℝ) :
    cexp (I * n * (θ - k * (2 * π))) = cexp (I * n * θ) := by
  have h : I * (n : ℂ) * ((θ : ℂ) - (k : ℂ) * (2 * π : ℂ))
      = I * n * θ - I * n * (k * (2 * π) : ℝ) := by
    push_cast
    ring
  rw [h, Complex.exp_sub, exp_I_int_int_two_pi, div_one]

/-- Jacobi–Anger on one period: `exp(i φ sin θ) = ∑ J_n(φ) exp(i n θ)`
for `θ ∈ (0, 2π]`. -/
theorem jacobi_anger_on_Ioc (φ : ℝ) {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * π)) :
    HasSum (fun n : ℤ => besselJ n φ * cexp (I * n * θ)) (phaseFun φ θ) := by
  have hsum : Summable (fourierCoeff (phaseOnCircle φ)) :=
    (summable_besselJ φ).congr fun n => (fourierCoeff_phaseOnCircle φ n).symm
  have hx := has_pointwise_sum_fourier_series_of_summable (f := phaseOnCircle φ) hsum
    (θ : AddCircle (2 * π))
  have hfun :
      (fun n : ℤ => fourierCoeff (phaseOnCircle φ) n • fourier n (θ : AddCircle (2 * π)))
        = fun n => besselJ n φ * cexp (I * n * θ) := by
    funext n
    rw [fourierCoeff_phaseOnCircle, smul_eq_mul, fourier_two_pi]
  rw [hfun] at hx
  rwa [phaseOnCircle_eq_of_mem φ hθ] at hx

/-- Jacobi–Anger for every real angle, by reducing modulo `2π`. -/
theorem jacobi_anger (φ θ : ℝ) :
    HasSum (fun n : ℤ => besselJ n φ * cexp (I * n * θ)) (phaseFun φ θ) := by
  have hp : 0 < (2 * π : ℝ) := Real.two_pi_pos
  set θ0 := toIocMod hp 0 θ
  have hmem : θ0 ∈ Ioc 0 (2 * π) := by
    simpa using toIocMod_mem_Ioc hp (0 : ℝ) θ
  have hθ0 : θ0 = θ - toIocDiv hp 0 θ * (2 * π) := by
    linarith [toIocMod_add_toIocDiv_mul hp (0 : ℝ) θ]
  have hphase : phaseFun φ θ0 = phaseFun φ θ := by
    rw [hθ0]
    exact (phaseFun_periodic φ).sub_int_mul_eq (toIocDiv hp 0 θ)
  have hfun :
      (fun n : ℤ => besselJ n φ * cexp (I * n * θ0))
        = fun n => besselJ n φ * cexp (I * n * θ) := by
    funext n
    rw [hθ0]
    push_cast
    rw [exp_I_n_sub_int_two_pi]
  rw [← hphase, ← hfun]
  exact jacobi_anger_on_Ioc φ hmem

end
