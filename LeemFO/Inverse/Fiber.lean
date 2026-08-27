/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.Analytic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Projection fibers and Vandermonde inversion of a through-focal series

Under pure defocus and perfect coherence the 2D kernel is a cisoid in `Δz`
whose frequency depends on `q` only through `q · ξ`. Grouping by that
frequency, a length-`n` equally spaced defocus series is a Vandermonde
system for the *fiber masses*. Distinct cisoid nodes recover the masses
exactly. If each fiber carries at most one object pair (transversal
support), the masses are the Gram entries. A full DC column plus vacuum
gauge recovers `Ψ`; a single fiber does not.

Householder partners share a node, so they remain glued: this is the
analytic 2D inverse, not an unrestricted lattice inverse.
-/

open Complex Real
open Matrix hiding gram
open scoped BigOperators ComplexConjugate Matrix

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {n : ℕ}

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

lemma sum_eq_sum_indexed {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (idx : α → ι) (f : ι → ℂ) (g : α → ℂ) :
    ∑ a : α, f (idx a) * g a
      = ∑ i : ι, f i * ∑ a : α, (if idx a = i then g a else 0) := by
  have h1 (a : α) :
      f (idx a) * g a = ∑ i : ι, if idx a = i then f i * g a else 0 := by
    rw [Fintype.sum_eq_single (idx a)]
    · rw [if_pos rfl]
    · intro i hi
      rw [if_neg (Ne.symm hi)]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    ∑ a : α, (if idx a = i then f i * g a else 0)
        = ∑ a : α, f i * (if idx a = i then g a else 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs <;> ring
    _ = f i * ∑ a : α, (if idx a = i then g a else 0) :=
      (Finset.mul_sum _ _ _).symm

/-- Aperture-weighted Gram on a difference-frequency pair. -/
def apertureGram (p : LEEM) (ι : G → EuclideanSpace ℝ (Fin 2))
    (Ψ : G → ℂ) (ξ q : G) : ℂ :=
  (p.aperture2 (ι q) : ℂ) * (p.aperture2 (ι (q - ξ)) : ℂ) * gram Ψ q (q - ξ)

/-- Fiber mass: sum of aperture-weighted Gram entries with a given cisoid index. -/
def cisoidMass (p : LEEM) (ι : G → EuclideanSpace ℝ (Fin 2))
    (Ψ : G → ℂ) (ξ : G) (idx : G → Fin n) (j : Fin n) : ℂ :=
  ∑ q : G, if idx q = j then apertureGram p ι Ψ ξ q else 0

/-- Cisoid nodes `exp(i ω_j δ)` of an equally spaced through-focal series. -/
def cisoidNode (ω : Fin n → ℝ) (δ : ℝ) (j : Fin n) : ℂ :=
  cexp (I * (ω j * δ : ℂ))

/-- Closed-form fiber masses: right-multiply samples by the inverse Vandermonde. -/
def recoveredMasses (ω : Fin n → ℝ) (δ : ℝ) (y : Fin n → ℂ) : Fin n → ℂ :=
  y ᵥ* (vandermonde (cisoidNode ω δ))⁻¹

lemma vandermonde_cisoid_det_ne_zero {ω : Fin n → ℝ} {δ : ℝ}
    (hinj : Function.Injective (cisoidNode ω δ)) :
    (vandermonde (cisoidNode ω δ)).det ≠ 0 :=
  (det_vandermonde_ne_zero_iff (R := ℂ)).mpr hinj

/-- Vandermonde uniqueness: distinct nodes determine fiber masses. -/
theorem cisoidMasses_unique (ω : Fin n → ℝ) (M N : Fin n → ℂ) (δ : ℝ)
    (hinj : Function.Injective (cisoidNode ω δ))
    (heq : ∀ k : Fin n,
      ∑ j : Fin n, M j * cisoidNode ω δ j ^ (k : ℕ)
        = ∑ j : Fin n, N j * cisoidNode ω δ j ^ (k : ℕ)) :
    M = N := by
  have hdiff : ∀ k : Fin n,
      ∑ j : Fin n, (M j - N j) * cisoidNode ω δ j ^ (k : ℕ) = 0 := by
    intro k
    have hsplit :
        ∑ j : Fin n, (M j - N j) * cisoidNode ω δ j ^ (k : ℕ)
          = ∑ j : Fin n, M j * cisoidNode ω δ j ^ (k : ℕ)
            - ∑ j : Fin n, N j * cisoidNode ω δ j ^ (k : ℕ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact sub_mul _ _ _
    rw [hsplit, heq k, sub_self]
  have h0 :=
    eq_zero_of_forall_pow_sum_mul_pow_eq_zero (R := ℂ) hinj hdiff
  ext j
  exact sub_eq_zero.mp (congrFun h0 j)

/-- The inverse Vandermonde recovers the masses from `n` defocus samples. -/
theorem recoveredMasses_eq (ω : Fin n → ℝ) (M : Fin n → ℂ) (δ : ℝ)
    (hinj : Function.Injective (cisoidNode ω δ))
    (y : Fin n → ℂ)
    (hy : ∀ k : Fin n, y k = ∑ j : Fin n, M j * cisoidNode ω δ j ^ (k : ℕ)) :
    recoveredMasses ω δ y = M := by
  have hdet := vandermonde_cisoid_det_ne_zero hinj
  have hV : IsUnit (vandermonde (cisoidNode ω δ)).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hy' : y = M ᵥ* vandermonde (cisoidNode ω δ) := by
    funext k
    rw [hy, vecMul_apply_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vandermonde_apply]
  unfold recoveredMasses
  rw [hy', vecMul_vecMul, mul_nonsing_inv _ hV, vecMul_one]

namespace LEEM

variable (p : LEEM)

/-- Pure-defocus sampled FO is a cisoid mixture indexed by `idx`. -/
theorem ihat_eq_cisoidMass (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (ι : G → EuclideanSpace ℝ (Fin 2)) (Ψ : G → ℂ) {ξ : G}
    (idx : G → Fin n) (ω : Fin n → ℝ)
    (hω : ∀ q, p.defocusOmega (ι q) (ι (q - ξ)) = ω (idx q))
    (Δz : ℝ) :
    ihat (p.sampledR ι Δz) Ψ ξ
      = ∑ j : Fin n, cisoidMass p ι Ψ ξ idx j
          * cexp (I * (ω j * Δz : ℂ)) := by
  have hterm (q : G) :
      p.sampledR ι Δz q (q - ξ) * gram Ψ q (q - ξ)
        = cexp (I * (ω (idx q) * Δz : ℂ)) * apertureGram p ι Ψ ξ q := by
    unfold sampledR apertureGram
    rw [p.R_FO2_pureDefocus_perfect h hC3 hC5, hω]
    ring
  rw [ihat_eq_gram]
  simp_rw [hterm]
  have hidx :=
    sum_eq_sum_indexed (ι := Fin n) idx
      (fun j => cexp (I * (ω j * Δz : ℂ)))
      (fun q => apertureGram p ι Ψ ξ q)
  rw [hidx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cisoidMass, mul_comm]

/-- Equally spaced defocus samples are the Vandermonde rows for the fiber masses. -/
theorem ihat_eq_vandermondeRow (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (ι : G → EuclideanSpace ℝ (Fin 2)) (Ψ : G → ℂ) {ξ : G}
    (idx : G → Fin n) (ω : Fin n → ℝ)
    (hω : ∀ q, p.defocusOmega (ι q) (ι (q - ξ)) = ω (idx q))
    (δ : ℝ) (k : Fin n) :
    ihat (p.sampledR ι (δ * (k : ℝ))) Ψ ξ
      = ∑ j : Fin n, cisoidMass p ι Ψ ξ idx j * cisoidNode ω δ j ^ (k : ℕ) := by
  rw [p.ihat_eq_cisoidMass h hC3 hC5 ι Ψ idx ω hω]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold cisoidNode
  simp only [ofReal_mul, ofReal_natCast]
  have hmul :
      I * ((ω j : ℂ) * ((δ : ℂ) * (k : ℂ)))
        = (k : ℂ) * (I * ((ω j : ℂ) * (δ : ℂ))) := by
    ring
  rw [hmul, Complex.exp_nat_mul]

/-- Distinct cisoid nodes: fiber masses are uniquely determined by `n` samples. -/
theorem cisoidMass_unique_of_ihat (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (ι : G → EuclideanSpace ℝ (Fin 2)) {Ψ Φ : G → ℂ} {ξ : G}
    (idx : G → Fin n) (ω : Fin n → ℝ)
    (hω : ∀ q, p.defocusOmega (ι q) (ι (q - ξ)) = ω (idx q))
    (δ : ℝ) (hinj : Function.Injective (cisoidNode ω δ))
    (heq : ∀ k : Fin n,
      ihat (p.sampledR ι (δ * (k : ℝ))) Ψ ξ
        = ihat (p.sampledR ι (δ * (k : ℝ))) Φ ξ) :
    cisoidMass p ι Ψ ξ idx = cisoidMass p ι Φ ξ idx := by
  refine cisoidMasses_unique ω _ _ δ hinj ?_
  intro k
  have hΨ := p.ihat_eq_vandermondeRow h hC3 hC5 ι Ψ idx ω hω δ k
  have hΦ := p.ihat_eq_vandermondeRow h hC3 hC5 ι Φ idx ω hω δ k
  rw [← hΨ, ← hΦ, heq k]

/-- Closed-form fiber masses from the through-focal series. -/
theorem recoveredMasses_eq_cisoidMass (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (ι : G → EuclideanSpace ℝ (Fin 2)) (Ψ : G → ℂ) {ξ : G}
    (idx : G → Fin n) (ω : Fin n → ℝ)
    (hω : ∀ q, p.defocusOmega (ι q) (ι (q - ξ)) = ω (idx q))
    (δ : ℝ) (hinj : Function.Injective (cisoidNode ω δ)) :
    recoveredMasses ω δ (fun k => ihat (p.sampledR ι (δ * (k : ℝ))) Ψ ξ)
      = cisoidMass p ι Ψ ξ idx := by
  refine recoveredMasses_eq ω _ δ hinj _ ?_
  intro k
  exact p.ihat_eq_vandermondeRow h hC3 hC5 ι Ψ idx ω hω δ k

/-- Transversal support: at most one occupied pair per cisoid fiber. -/
def transversalSupport (Ψ : G → ℂ) (ξ : G) (idx : G → Fin n) : Prop :=
  ∀ q q', idx q = idx q' →
    Ψ q ≠ 0 → Ψ (q - ξ) ≠ 0 → Ψ q' ≠ 0 → Ψ (q' - ξ) ≠ 0 → q = q'

/-- On transversal support inside the aperture, a fiber mass is a single Gram entry. -/
theorem cisoidMass_eq_gram_of_transversal
    (ι : G → EuclideanSpace ℝ (Fin 2)) (Ψ : G → ℂ) {ξ : G}
    (idx : G → Fin n)
    (hT : transversalSupport Ψ ξ idx)
    (hap : ∀ q, Ψ q ≠ 0 → p.aperture2 (ι q) = 1)
    {q : G} (hq : Ψ q ≠ 0) (hqξ : Ψ (q - ξ) ≠ 0) :
    cisoidMass p ι Ψ ξ idx (idx q) = gram Ψ q (q - ξ) := by
  have hapq : p.aperture2 (ι q) = 1 := hap q hq
  have hapξ : p.aperture2 (ι (q - ξ)) = 1 := hap (q - ξ) hqξ
  unfold cisoidMass apertureGram
  rw [Fintype.sum_eq_single q]
  · rw [if_pos rfl, hapq, hapξ]
    simp only [ofReal_one, one_mul]
  · intro q' hq'
    split_ifs with hidx
    · by_cases hΨq' : Ψ q' = 0
      · simp [gram, hΨq']
      · by_cases hΨξ' : Ψ (q' - ξ) = 0
        · simp [gram, hΨξ']
        · exact (hq' (hT q' q hidx hΨq' hΨξ' hq hqξ)).elim
    · rfl

/-- Analytic 2D inverse on transversal support: recovered fiber mass is the Gram. -/
theorem recoveredMasses_eq_gram_of_transversal (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (ι : G → EuclideanSpace ℝ (Fin 2)) (Ψ : G → ℂ) {ξ : G}
    (idx : G → Fin n) (ω : Fin n → ℝ)
    (hω : ∀ q, p.defocusOmega (ι q) (ι (q - ξ)) = ω (idx q))
    (δ : ℝ) (hinj : Function.Injective (cisoidNode ω δ))
    (hT : transversalSupport Ψ ξ idx)
    (hap : ∀ q, Ψ q ≠ 0 → p.aperture2 (ι q) = 1)
    {q : G} (hq : Ψ q ≠ 0) (hqξ : Ψ (q - ξ) ≠ 0) :
    recoveredMasses ω δ (fun k => ihat (p.sampledR ι (δ * (k : ℝ))) Ψ ξ) (idx q)
      = gram Ψ q (q - ξ) := by
  rw [p.recoveredMasses_eq_cisoidMass h hC3 hC5 ι Ψ idx ω hω δ hinj]
  exact p.cisoidMass_eq_gram_of_transversal ι Ψ idx hT hap hq hqξ

/-- Vacuum column: the pair `(ξ, 0)` is recovered from the fiber of lag `ξ`. -/
theorem recoveredMasses_eq_gram_vacuum (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (ι : G → EuclideanSpace ℝ (Fin 2)) (Ψ : G → ℂ) {ξ : G}
    (idx : G → Fin n) (ω : Fin n → ℝ)
    (hω : ∀ q, p.defocusOmega (ι q) (ι (q - ξ)) = ω (idx q))
    (δ : ℝ) (hinj : Function.Injective (cisoidNode ω δ))
    (hT : transversalSupport Ψ ξ idx)
    (hap : ∀ q, Ψ q ≠ 0 → p.aperture2 (ι q) = 1)
    (hξ : Ψ ξ ≠ 0) (h0 : Ψ 0 ≠ 0) :
    recoveredMasses ω δ (fun k => ihat (p.sampledR ι (δ * (k : ℝ))) Ψ ξ) (idx ξ)
      = gram Ψ ξ 0 := by
  have hqξ : Ψ (ξ - ξ) ≠ 0 := by simpa [sub_self] using h0
  have hgram :=
    p.recoveredMasses_eq_gram_of_transversal h hC3 hC5 ι Ψ idx ω hω δ hinj
      hT hap hξ hqξ
  simpa [sub_self] using hgram

/-- Known occupied pairs: equal through-focal data recover the same Gram entry. -/
theorem gram_eq_of_transversal_ihat (h : p.PerfectCoherence)
    (hC3 : p.C3 = 0) (hC5 : p.C5 = 0)
    (ι : G → EuclideanSpace ℝ (Fin 2)) {Ψ Φ : G → ℂ} {ξ : G}
    (idx : G → Fin n) (ω : Fin n → ℝ)
    (hω : ∀ q, p.defocusOmega (ι q) (ι (q - ξ)) = ω (idx q))
    (δ : ℝ) (hinj : Function.Injective (cisoidNode ω δ))
    (hTΨ : transversalSupport Ψ ξ idx) (hTΦ : transversalSupport Φ ξ idx)
    (hapΨ : ∀ q, Ψ q ≠ 0 → p.aperture2 (ι q) = 1)
    (hapΦ : ∀ q, Φ q ≠ 0 → p.aperture2 (ι q) = 1)
    (heq : ∀ k : Fin n,
      ihat (p.sampledR ι (δ * (k : ℝ))) Ψ ξ
        = ihat (p.sampledR ι (δ * (k : ℝ))) Φ ξ)
    {q : G} (hqΨ : Ψ q ≠ 0) (hqξΨ : Ψ (q - ξ) ≠ 0)
    (hqΦ : Φ q ≠ 0) (hqξΦ : Φ (q - ξ) ≠ 0) :
    gram Ψ q (q - ξ) = gram Φ q (q - ξ) := by
  have hΨ :=
    p.recoveredMasses_eq_gram_of_transversal h hC3 hC5 ι Ψ idx ω hω δ hinj
      hTΨ hapΨ hqΨ hqξΨ
  have hΦ :=
    p.recoveredMasses_eq_gram_of_transversal h hC3 hC5 ι Φ idx ω hω δ hinj
      hTΦ hapΦ hqΦ hqξΦ
  rw [← hΨ, ← hΦ]
  congr 1
  funext k
  exact heq k

end LEEM

end
