/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.LinearInverse
import LeemFO.Inverse.Tikhonov
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gram lifting of bilinear FO

The discrete intensity Fourier coefficient is the contraction of the rank-1
Gram `X(q,q') = Ψ(q) conj(Ψ(q'))` against the FO kernel. Recovering `X` is a
*linear* inverse on each difference-frequency slice; the object is then the
vacuum-gauge factor `Ψ(q) = X(q,0) / √‖X(0,0)‖`.
-/

open Complex Real
open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {κ : Type*} [Fintype κ]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

/-- Rank-1 Gram of an object spectrum. -/
def gram (Ψ : G → ℂ) (q q' : G) : ℂ :=
  Ψ q * conj (Ψ q')

lemma gram_hermitian (Ψ : G → ℂ) (q q' : G) :
    conj (gram Ψ q q') = gram Ψ q' q := by
  simp only [gram, map_mul, mul_comm, conj_conj]

lemma gram_diag (Ψ : G → ℂ) (q : G) :
    gram Ψ q q = (‖Ψ q‖ ^ 2 : ℂ) := by
  unfold gram
  rw [mul_comm, conj_mul_self]

lemma gram_diag_norm (Ψ : G → ℂ) (q : G) :
    ‖gram Ψ q q‖ = ‖Ψ q‖ ^ 2 := by
  rw [gram_diag]
  simp [norm_pow, Complex.norm_real]

lemma gram_rank1 (Ψ : G → ℂ) (q q' : G) :
    gram Ψ q q' * gram Ψ 0 0 = gram Ψ q 0 * gram Ψ 0 q' := by
  simp only [gram]
  ring

lemma gram_eq_of_phase (Ψ : G → ℂ) (θ : ℝ) :
    gram (fun q => cexp (I * θ) * Ψ q) = gram Ψ := by
  funext q q'
  unfold gram
  simp only [map_mul]
  have hφ := cexp_I_mul_conj θ
  calc
    cexp (I * θ) * Ψ q * (conj (cexp (I * θ)) * conj (Ψ q'))
        = (cexp (I * θ) * conj (cexp (I * θ))) * (Ψ q * conj (Ψ q')) := by
          ring
    _ = Ψ q * conj (Ψ q') := by
          rw [hφ, one_mul]

/-- Bilinear intensity is the Gram contracted against the kernel. -/
theorem ihat_eq_gram (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) :
    ihat R Ψ ξ = ∑ q : G, R q (q - ξ) * gram Ψ q (q - ξ) := by
  unfold ihat gram
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- Vacuum-gauge factor of a Gram: `Ψ(q) = X(q,0) / √‖X(0,0)‖`. -/
noncomputable def vacuumGaugePsi (X : G → G → ℂ) : G → ℂ :=
  fun q => X q 0 / (Real.sqrt ‖X 0 0‖ : ℂ)

theorem vacuumGaugePsi_gram (Ψ : G → ℂ) :
    vacuumGaugePsi (gram Ψ) = fun q => (conj (Ψ 0) / ‖Ψ 0‖) * Ψ q := by
  have hsqrt : Real.sqrt ‖gram Ψ 0 0‖ = ‖Ψ 0‖ := by
    rw [gram_diag_norm, Real.sqrt_sq (norm_nonneg _)]
  funext q
  change gram Ψ q 0 / (Real.sqrt ‖gram Ψ 0 0‖ : ℂ)
      = (conj (Ψ 0) / ‖Ψ 0‖) * Ψ q
  rw [hsqrt]
  unfold gram
  ring

lemma complex_eq_norm_of_im_zero_re_nonneg {z : ℂ} (him : z.im = 0)
    (hre : 0 ≤ z.re) : z = ‖z‖ := by
  apply Complex.ext
  · have hn : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      have hsqrt : ‖z‖ = Real.sqrt (‖z‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg z)).symm
      rw [hsqrt, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [pow_two]
    rw [hn, him]
    simp [Real.sqrt_sq hre]
  · simp [him]

/-- If the DC coefficient is real and nonnegative, vacuum gauge is the identity. -/
theorem vacuumGaugePsi_recovers (Ψ : G → ℂ) (h0 : Ψ 0 ≠ 0)
    (him : (Ψ 0).im = 0) (hre : 0 ≤ (Ψ 0).re) :
    vacuumGaugePsi (gram Ψ) = Ψ := by
  rw [vacuumGaugePsi_gram Ψ]
  have hz : Ψ 0 = ‖Ψ 0‖ := complex_eq_norm_of_im_zero_re_nonneg him hre
  have hconj : conj (Ψ 0) = Ψ 0 := (Complex.conj_eq_iff_im).2 him
  have hμ : conj (Ψ 0) = (‖Ψ 0‖ : ℂ) := by
    calc
      conj (Ψ 0) = Ψ 0 := hconj
      _ = ‖Ψ 0‖ := hz
  have hne : (‖Ψ 0‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
  funext q
  rw [hμ, div_self hne, one_mul]

/-- Slice map of a lifted Gram unknown. -/
def sliceApply (A : κ → G → ℂ) (x : G → ℂ) (k : κ) : ℂ :=
  ∑ q : G, A k q * x q

/-- The slice is injective: vanishing measurements imply a vanishing unknown. -/
def sliceInjective (A : κ → G → ℂ) : Prop :=
  ∀ x : G → ℂ, (∀ k, sliceApply A x k = 0) → x = 0

theorem slice_unique {A : κ → G → ℂ} (h : sliceInjective A) (x y : G → ℂ)
    (heq : ∀ k, sliceApply A x k = sliceApply A y k) : x = y := by
  have hxy : x - y = 0 := by
    refine h (x - y) ?_
    intro k
    have : sliceApply A (fun q => x q - y q) k
        = sliceApply A x k - sliceApply A y k := by
      simp only [sliceApply, mul_sub, Finset.sum_sub_distrib]
    have hx : (x - y) = fun q => x q - y q := rfl
    rw [hx, this, heq k, sub_self]
  exact sub_eq_zero.mp hxy

/-- Through-focal contraction of a general (not necessarily rank-1) lift. -/
def liftedApply (R : κ → G → G → ℂ) (X : G → G → ℂ) (ξ : G) (k : κ) : ℂ :=
  ∑ q : G, R k q (q - ξ) * X q (q - ξ)

theorem liftedApply_gram (R : κ → G → G → ℂ) (Ψ : G → ℂ) (ξ : G) (k : κ) :
    liftedApply R (gram Ψ) ξ k = ihat (R k) Ψ ξ := by
  rw [liftedApply, ihat_eq_gram]

/-- Off-axis bilinear remainder after peeling the vacuum 2×2 columns. -/
def bilinearRemainder (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) : ℂ :=
  ∑ q : G, if q = 0 ∨ q = ξ then 0 else R q (q - ξ) * gram Ψ q (q - ξ)

private lemma sum_ite_pair (f : G → ℂ) {ξ : G} (hξ : ξ ≠ 0) :
    ∑ q : G, (if q = 0 ∨ q = ξ then f q else 0) = f 0 + f ξ := by
  have hset : Finset.univ.filter (fun q : G => q = 0 ∨ q = ξ) = {0, ξ} := by
    ext q
    simp [or_comm]
  rw [← Finset.sum_filter, hset, Finset.sum_pair hξ.symm]

/-- Exact DC-column split of bilinear FO at a nonzero difference frequency. -/
theorem ihat_dc_split (R : G → G → ℂ) (Ψ : G → ℂ) {ξ : G} (hξ : ξ ≠ 0) :
    ihat R Ψ ξ
      = R ξ 0 * gram Ψ ξ 0
        + R 0 (-ξ) * gram Ψ 0 (-ξ)
        + bilinearRemainder R Ψ ξ := by
  rw [ihat_eq_gram]
  unfold bilinearRemainder
  have hterm (q : G) :
      R q (q - ξ) * gram Ψ q (q - ξ)
        = (if q = 0 ∨ q = ξ then R q (q - ξ) * gram Ψ q (q - ξ) else 0)
          + (if q = 0 ∨ q = ξ then 0 else
            R q (q - ξ) * gram Ψ q (q - ξ)) := by
    split_ifs <;> ring
  refine (Finset.sum_congr rfl fun q _ => hterm q).trans ?_
  rw [Finset.sum_add_distrib,
    sum_ite_pair (fun q => R q (q - ξ) * gram Ψ q (q - ξ)) hξ]
  have hf0 : R 0 (0 - ξ) * gram Ψ 0 (0 - ξ) = R 0 (-ξ) * gram Ψ 0 (-ξ) := by
    simp [sub_eq_add_neg]
  have hfξ : R ξ (ξ - ξ) * gram Ψ ξ (ξ - ξ) = R ξ 0 * gram Ψ ξ 0 := by
    simp
  rw [hf0, hfξ]
  ac_rfl

/-- Subtracting a known remainder reduces bilinear FO to the vacuum 2×2. -/
theorem ihat_sub_remainder (R : G → G → ℂ) (Ψ : G → ℂ) {ξ : G} (hξ : ξ ≠ 0) :
    ihat R Ψ ξ - bilinearRemainder R Ψ ξ
      = R ξ 0 * gram Ψ ξ 0 + R 0 (-ξ) * gram Ψ 0 (-ξ) := by
  rw [ihat_dc_split (hξ := hξ)]
  ring

theorem twoColumn_recovers (h g : κ → ℂ) (U V : ℂ)
    (hD : gramDet (0 : ℝ) h g ≠ 0) :
    tikhonovXhat2 0 h g (fun k => h k * U + g k * V) = (U, V) := by
  have herr :=
    tikhonov2_error (α := (0 : ℝ)) h g U V (fun _ => 0) hD
  have hz : tikhonov2FromRhs (0 : ℝ) h g 0 0 = (0, 0) := by
    simp [tikhonov2FromRhs]
  have h0u : tikhonov2Rhs h (fun _ : κ => (0 : ℂ)) = 0 := by
    simp [tikhonov2Rhs]
  have h0v : tikhonov2Rhs g (fun _ : κ => (0 : ℂ)) = 0 := by
    simp [tikhonov2Rhs]
  simpa [h0u, h0v, hz] using herr

/-- Recover `|Ψ(0)|²` from the DC column and the total intensity. -/
noncomputable def recoveredDC (Xcol : G → ℂ) (I0 : ℂ) : ℂ :=
  (∑ q : G, (‖Xcol q‖ ^ 2 : ℂ)) / I0

theorem recoveredDC_gram (R : G → G → ℂ) (Ψ : G → ℂ)
    (hR : ∀ q, R q q = 1) (hI : ihat R Ψ 0 ≠ 0) :
    recoveredDC (fun q => gram Ψ q 0) (ihat R Ψ 0) = gram Ψ 0 0 := by
  have hi : ihat R Ψ 0 = ∑ q : G, (‖Ψ q‖ ^ 2 : ℂ) := by
    unfold ihat
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [sub_zero, hR, mul_one, mul_comm, conj_mul_self]
  have hterm (q : G) :
      (‖gram Ψ q 0‖ ^ 2 : ℂ) = (‖Ψ 0‖ ^ 2 : ℂ) * (‖Ψ q‖ ^ 2 : ℂ) := by
    have hreal : ‖gram Ψ q 0‖ ^ 2 = ‖Ψ 0‖ ^ 2 * ‖Ψ q‖ ^ 2 := by
      unfold gram
      rw [norm_mul, norm_conj, mul_pow, mul_comm]
    exact_mod_cast hreal
  have hcol :
      ∑ q : G, (‖gram Ψ q 0‖ ^ 2 : ℂ)
        = (‖Ψ 0‖ ^ 2 : ℂ) * ∑ q : G, (‖Ψ q‖ ^ 2 : ℂ) := by
    simp_rw [hterm]
    rw [← Finset.mul_sum]
  unfold recoveredDC
  rw [hcol, hi, gram_diag, mul_div_cancel_right₀ _ (by simpa [hi] using hI)]

/-- The DC slice of a unimodular diagonal kernel has rank one. -/
theorem dcSlice_not_injective [Nontrivial G] (A : κ → G → ℂ)
    (hA : ∀ k q, A k q = 1) : ¬ sliceInjective A := by
  intro hker
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : G)
  let x : G → ℂ := fun q => if q = 0 then 1 else if q = ξ then -1 else 0
  have hsum : ∀ k, sliceApply A x k = 0 := by
    intro k
    unfold sliceApply
    simp only [hA, one_mul]
    rw [← Finset.sum_add_sum_compl ({0, ξ} : Finset G)]
    have hpair : ∑ q ∈ ({0, ξ} : Finset G), x q = 0 := by
      rw [Finset.sum_pair hξ.symm]
      simp [x, hξ]
    have hrest : ∑ q ∈ ({0, ξ} : Finset G)ᶜ, x q = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      have hq' : q ≠ 0 ∧ q ≠ ξ := by
        simpa [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] using hq
      simp [x, hq'.1, hq'.2]
    rw [hpair, hrest, zero_add]
  have hx := hker x hsum
  have hx0 : x 0 = 1 := if_pos rfl
  rw [hx] at hx0
  exact one_ne_zero hx0.symm

/-- Hermitian kernels yield Hermitian intensity: $`I(-\xi)=\overline{I(\xi)}`$. -/
theorem ihat_hermitian (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G)
    (hR : ∀ q q', conj (R q q') = R q' q) :
    conj (ihat R Ψ ξ) = ihat R Ψ (-ξ) := by
  unfold ihat
  simp only [map_sum, map_mul, conj_conj]
  let f : G → ℂ := fun q => conj (Ψ q) * conj (R q (q - ξ)) * Ψ (q - ξ)
  let g : G → ℂ :=
    fun q' => conj (Ψ (q' + ξ)) * conj (R (q' + ξ) q') * Ψ q'
  have hg : ∀ q', g q' = f (q' + ξ) := by
    intro q'
    simp [f, g]
  have hreindex : ∑ q, f q = ∑ q', g q' :=
    (Fintype.sum_equiv (Equiv.addRight ξ) g f hg).symm
  change ∑ q, f q = ∑ q', Ψ q' * R q' (q' - -ξ) * conj (Ψ (q' - -ξ))
  rw [hreindex]
  refine Finset.sum_congr rfl fun q' _ => ?_
  simp only [g, sub_neg_eq_add]
  rw [hR (q' + ξ) q']
  ac_rfl

/-- Rank-1 coherent kernel: intensity is the Gram autocorrelation of `Ψ P`. -/
theorem ihat_of_rank1 (P Ψ : G → ℂ) (ξ : G) :
    ihat (fun q q' => P q * conj (P q')) Ψ ξ
      = ∑ q : G, gram (fun t => Ψ t * P t) q (q - ξ) := by
  simp only [ihat, gram, map_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- Lag diagonals determine a bilinear form on an abelian frequency group. -/
theorem gram_eq_of_lags {Ψ Φ : G → ℂ}
    (h : ∀ ξ q, gram Ψ q (q - ξ) = gram Φ q (q - ξ)) : gram Ψ = gram Φ := by
  funext q q'
  have := h (q - q') q
  simpa [sub_sub_cancel] using this

/-- Through-focal slice injectivity recovers one lag diagonal of a lift. -/
theorem lifted_unique_of_sliceInjective (R : κ → G → G → ℂ)
    (X Y : G → G → ℂ) (ξ : G)
    (h : sliceInjective (fun k q => R k q (q - ξ)))
    (heq : ∀ k, liftedApply R X ξ k = liftedApply R Y ξ k) :
    ∀ q, X q (q - ξ) = Y q (q - ξ) := by
  have hx : (fun q => X q (q - ξ)) = fun q => Y q (q - ξ) := by
    refine slice_unique h _ _ ?_
    intro k
    simpa [sliceApply, liftedApply] using heq k
  exact fun q => congrFun hx q

/-- The vacuum 2×2 is injective when the Gram determinant is nonzero. -/
theorem twoColumn_injective (h g : κ → ℂ)
    (hD : gramDet (0 : ℝ) h g ≠ 0) {U V : ℂ}
    (hz : ∀ k, h k * U + g k * V = 0) : U = 0 ∧ V = 0 := by
  have hUV := twoColumn_recovers h g U V hD
  have h00 := twoColumn_recovers h g 0 0 hD
  have hy : (fun k => h k * U + g k * V) = fun k => h k * 0 + g k * 0 := by
    funext k
    simp [hz k]
  have hpair : (U, V) = (0, 0) := by
    rw [← hUV, hy, h00]
  exact Prod.mk.inj hpair

end
