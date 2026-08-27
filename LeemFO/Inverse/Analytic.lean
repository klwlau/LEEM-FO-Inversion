/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.Gram
import LeemFO.Inverse.SmallMode
import LeemFO.Inverse.Degeneracy
import LeemFO.Inverse.Pipeline

/-!
# Analytic 2D FO inverse

The reconstruction map is the vacuum-gauge factor of the Gram of the object.
Each difference-frequency slice of a through-focal series is a linear image
of that Gram; the vacuum 2×2 is the exact remainder-corrected inverse of the
DC column. Small-mode and two-axis 3-wave objects invert in closed form. A
radial pure-defocus kernel cannot separate perpendicular frequencies. The DC
slice itself is not injective (`dcSlice_not_injective`).

Stage-1 Tikhonov (`stage1Pair`) is this map linearised at vacuum (remainder
dropped). The identities below keep the remainder and invert it when it is
known, or when support makes it vanish.
-/

open Complex Real
open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {κ : Type*} [Fintype κ]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

/-- Analytic reconstruction: DC-column factor of a Gram. -/
noncomputable def analyticPsi (X : G → G → ℂ) : G → ℂ :=
  vacuumGaugePsi X

theorem analyticPsi_eq_vacuumGauge (X : G → G → ℂ) :
    analyticPsi X = vacuumGaugePsi X :=
  rfl

/-- Noiseless reconstruction of a vacuum-gauged object from its Gram. -/
theorem analyticPsi_recovers (Ψ : G → ℂ) (h0 : Ψ 0 ≠ 0)
    (him : (Ψ 0).im = 0) (hre : 0 ≤ (Ψ 0).re) :
    analyticPsi (gram Ψ) = Ψ :=
  vacuumGaugePsi_recovers Ψ h0 him hre

/-- Unique Gram factor up to the global phase already quotiented by intensity. -/
theorem analyticPsi_unique {Ψ Φ : G → ℂ} (h0 : Ψ 0 ≠ 0)
    (h : gram Ψ = gram Φ)
    (himΨ : (Ψ 0).im = 0) (hreΨ : 0 ≤ (Ψ 0).re)
    (himΦ : (Φ 0).im = 0) (hreΦ : 0 ≤ (Φ 0).re)
    (hΦ0 : Φ 0 ≠ 0) :
    Ψ = Φ := by
  have hΨ := analyticPsi_recovers Ψ h0 himΨ hreΨ
  have hΦ := analyticPsi_recovers Φ hΦ0 himΦ hreΦ
  rw [← hΨ, ← hΦ, h]

/-- Vacuum gauge uses only the DC column, so matching columns recover the object. -/
theorem analyticPsi_unique_of_dc_column {Ψ Φ : G → ℂ} (h0 : Ψ 0 ≠ 0)
    (himΨ : (Ψ 0).im = 0) (hreΨ : 0 ≤ (Ψ 0).re)
    (hΦ0 : Φ 0 ≠ 0) (himΦ : (Φ 0).im = 0) (hreΦ : 0 ≤ (Φ 0).re)
    (hcol : ∀ q, gram Ψ q 0 = gram Φ q 0) :
    Ψ = Φ := by
  have hΨ := analyticPsi_recovers Ψ h0 himΨ hreΨ
  have hΦ := analyticPsi_recovers Φ hΦ0 himΦ hreΦ
  have hmap : analyticPsi (gram Ψ) = analyticPsi (gram Φ) := by
    unfold analyticPsi vacuumGaugePsi
    funext q
    simp only [hcol]
  rw [← hΨ, ← hΦ, hmap]

/-- Remainder-corrected measurements equal the vacuum 2×2 model. -/
theorem remainderCorrected_eq_twoColumn (R : κ → G → G → ℂ) (Ψ : G → ℂ)
    {ξ : G} (hξ : ξ ≠ 0) (k : κ) :
    ihat (R k) Ψ ξ - bilinearRemainder (R k) Ψ ξ
      = R k ξ 0 * gram Ψ ξ 0 + R k 0 (-ξ) * gram Ψ 0 (-ξ) :=
  ihat_sub_remainder (R k) Ψ hξ

/-- Closed-form vacuum pair from remainder-corrected through-focal data. -/
theorem analyticPair_of_remainder (R : κ → G → G → ℂ) (Ψ : G → ℂ)
    {ξ : G} (hξ : ξ ≠ 0)
    (hD : gramDet (0 : ℝ) (fun k => R k ξ 0) (fun k => R k 0 (-ξ)) ≠ 0) :
    tikhonovXhat2 0 (fun k => R k ξ 0) (fun k => R k 0 (-ξ))
        (fun k => ihat (R k) Ψ ξ - bilinearRemainder (R k) Ψ ξ)
      = (gram Ψ ξ 0, gram Ψ 0 (-ξ)) := by
  have hmodel := remainderCorrected_eq_twoColumn R Ψ hξ
  have : (fun k : κ => ihat (R k) Ψ ξ - bilinearRemainder (R k) Ψ ξ)
      = fun k => R k ξ 0 * gram Ψ ξ 0 + R k 0 (-ξ) * gram Ψ 0 (-ξ) := by
    funext k
    exact hmodel k
  rw [this]
  exact twoColumn_recovers _ _ _ _ hD

/-- On a two-mode object the remainder vanishes, so the scalar CTF slice inverts
the DC column exactly (`α = 0`, energy positive). -/
theorem analyticPair_twoMode (R : κ → G → G → ℂ) (Ψ : G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0) (h2 : ξ + ξ ≠ 0)
    (hΨ : ∀ q, q ≠ 0 → q ≠ ξ → Ψ q = 0)
    (hD : tikhonovDenom (0 : ℝ) (fun k => R k ξ 0) ≠ 0) :
    tikhonovXhat 0 (fun k => R k ξ 0)
        (fun k => ihat (R k) Ψ ξ)
      = gram Ψ ξ 0 := by
  have hy : (fun k : κ => ihat (R k) Ψ ξ)
      = fun k => R k ξ 0 * gram Ψ ξ 0 := by
    funext k
    exact ihat_twoMode (R k) Ψ hξ h2 hΨ
  rw [hy]
  have hy0 : (fun k : κ => R k ξ 0 * gram Ψ ξ 0)
      = fun k => R k ξ 0 * gram Ψ ξ 0 + (0 : ℂ) := by
    funext k
    rw [add_zero]
  rw [hy0]
  have herr :=
    tikhonov_error (α := (0 : ℝ)) (fun k => R k ξ 0) (gram Ψ ξ 0)
      (fun _ => (0 : ℂ)) hD
  apply eq_of_sub_eq_zero
  rw [herr]
  simp [ofReal_zero]

/-- Two-axis 3-wave object `{0, u, v}`: scalar CTF slice inverts the vacuum column at `u`. -/
theorem analyticPair_twoAxis (R : κ → G → G → ℂ) (Ψ : G → ℂ) {u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h2u : u + u ≠ 0) (h2 : u + u ≠ v) (hneg : v ≠ -u)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0)
    (hD : tikhonovDenom (0 : ℝ) (fun k => R k u 0) ≠ 0) :
    tikhonovXhat 0 (fun k => R k u 0)
        (fun k => ihat (R k) Ψ u)
      = gram Ψ u 0 := by
  have hy : (fun k : κ => ihat (R k) Ψ u)
      = fun k => R k u 0 * gram Ψ u 0 := by
    funext k
    exact ihat_twoAxis (R k) Ψ hu hv huv h2u h2 hneg hΨ
  rw [hy]
  have hy0 : (fun k : κ => R k u 0 * gram Ψ u 0)
      = fun k => R k u 0 * gram Ψ u 0 + (0 : ℂ) := by
    funext k
    rw [add_zero]
  rw [hy0]
  have herr :=
    tikhonov_error (α := (0 : ℝ)) (fun k => R k u 0) (gram Ψ u 0)
      (fun _ => (0 : ℂ)) hD
  apply eq_of_sub_eq_zero
  rw [herr]
  simp [ofReal_zero]

/-- Same 3-wave object: scalar CTF slice at the second diffracted frequency `v`. -/
theorem analyticPair_twoAxis_v (R : κ → G → G → ℂ) (Ψ : G → ℂ) {u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h2v : v + v ≠ 0) (h2vu : v + v ≠ u) (hneg : u ≠ -v)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0)
    (hD : tikhonovDenom (0 : ℝ) (fun k => R k v 0) ≠ 0) :
    tikhonovXhat 0 (fun k => R k v 0)
        (fun k => ihat (R k) Ψ v)
      = gram Ψ v 0 := by
  have hy : (fun k : κ => ihat (R k) Ψ v)
      = fun k => R k v 0 * gram Ψ v 0 := by
    funext k
    exact ihat_twoAxis_v (R k) Ψ hu hv huv h2v h2vu hneg hΨ
  rw [hy]
  have hy0 : (fun k : κ => R k v 0 * gram Ψ v 0)
      = fun k => R k v 0 * gram Ψ v 0 + (0 : ℂ) := by
    funext k
    rw [add_zero]
  rw [hy0]
  have herr :=
    tikhonov_error (α := (0 : ℝ)) (fun k => R k v 0) (gram Ψ v 0)
      (fun _ => (0 : ℂ)) hD
  apply eq_of_sub_eq_zero
  rw [herr]
  simp [ofReal_zero]

/-- Equal through-focal data at `u` recover the vacuum Gram entry of a 3-wave object. -/
theorem twoAxis_dcCol_unique (R : κ → G → G → ℂ) {Ψ Φ : G → ℂ} {u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h2u : u + u ≠ 0) (h2 : u + u ≠ v) (hneg : v ≠ -u)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0)
    (hΦ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Φ q = 0)
    (hD : tikhonovDenom (0 : ℝ) (fun k => R k u 0) ≠ 0)
    (heq : ∀ k, ihat (R k) Ψ u = ihat (R k) Φ u) :
    gram Ψ u 0 = gram Φ u 0 := by
  have hΨ' := analyticPair_twoAxis R Ψ hu hv huv h2u h2 hneg hΨ hD
  have hΦ' := analyticPair_twoAxis R Φ hu hv huv h2u h2 hneg hΦ hD
  have hy : (fun k : κ => ihat (R k) Ψ u) = fun k => ihat (R k) Φ u :=
    funext heq
  rw [← hΨ', ← hΦ', hy]

/-- Equal through-focal data at `v` recover the other vacuum Gram entry. -/
theorem twoAxis_dcCol_unique_v (R : κ → G → G → ℂ) {Ψ Φ : G → ℂ} {u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h2v : v + v ≠ 0) (h2vu : v + v ≠ u) (hneg : u ≠ -v)
    (hΨ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Ψ q = 0)
    (hΦ : ∀ q, q ≠ 0 → q ≠ u → q ≠ v → Φ q = 0)
    (hD : tikhonovDenom (0 : ℝ) (fun k => R k v 0) ≠ 0)
    (heq : ∀ k, ihat (R k) Ψ v = ihat (R k) Φ v) :
    gram Ψ v 0 = gram Φ v 0 := by
  have hΨ' := analyticPair_twoAxis_v R Ψ hu hv huv h2v h2vu hneg hΨ hD
  have hΦ' := analyticPair_twoAxis_v R Φ hu hv huv h2v h2vu hneg hΦ hD
  have hy : (fun k : κ => ihat (R k) Ψ v) = fun k => ihat (R k) Φ v :=
    funext heq
  rw [← hΨ', ← hΦ', hy]

/-- Three-mode objects invert by the vacuum 2×2 (no remainder). -/
theorem analyticPair_threeMode (R : κ → G → G → ℂ) (Ψ : G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0) (h2 : ξ + ξ ≠ 0) (h3 : ξ + ξ ≠ -ξ)
    (hΨ : ∀ q, q ≠ 0 → q ≠ ξ → q ≠ -ξ → Ψ q = 0)
    (hD : gramDet (0 : ℝ) (fun k => R k ξ 0) (fun k => R k 0 (-ξ)) ≠ 0) :
    tikhonovXhat2 0 (fun k => R k ξ 0) (fun k => R k 0 (-ξ))
        (fun k => ihat (R k) Ψ ξ)
      = (gram Ψ ξ 0, gram Ψ 0 (-ξ)) := by
  have hy : (fun k : κ => ihat (R k) Ψ ξ)
      = fun k => R k ξ 0 * gram Ψ ξ 0 + R k 0 (-ξ) * gram Ψ 0 (-ξ) := by
    funext k
    exact ihat_threeMode_axis (R k) Ψ hξ h2 h3 hΨ
  rw [hy]
  exact twoColumn_recovers _ _ _ _ hD

/-- Remainder-corrected through-focal data determine the vacuum pair uniquely. -/
theorem dcPair_unique_of_remainder (R : κ → G → G → ℂ) (Ψ Φ : G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0)
    (hD : gramDet (0 : ℝ) (fun k => R k ξ 0) (fun k => R k 0 (-ξ)) ≠ 0)
    (heq : ∀ k, ihat (R k) Ψ ξ - bilinearRemainder (R k) Ψ ξ
              = ihat (R k) Φ ξ - bilinearRemainder (R k) Φ ξ) :
    (gram Ψ ξ 0, gram Ψ 0 (-ξ)) = (gram Φ ξ 0, gram Φ 0 (-ξ)) := by
  have hΨ := analyticPair_of_remainder R Ψ hξ hD
  have hΦ := analyticPair_of_remainder R Φ hξ hD
  have hy : (fun k : κ => ihat (R k) Ψ ξ - bilinearRemainder (R k) Ψ ξ)
      = fun k => ihat (R k) Φ ξ - bilinearRemainder (R k) Φ ξ :=
    funext heq
  rw [← hΨ, ← hΦ, hy]

/-- Off-DC injective slices recover every lag diagonal with `ξ ≠ 0`.
The DC slice `ξ = 0` is not injective for unimodular diagonal kernels
(`dcSlice_not_injective`), so this does not by itself yield `gram Ψ = gram Φ`.
Vacuum-gauged uniqueness is `analyticPsi_unique` (from a full Gram) or
`dcPair_unique_of_remainder` (from remainder-corrected vacuum 2×2 data). -/
theorem offDiagGram_eq_of_sliceInjective
    (R : κ → G → G → ℂ) {Ψ Φ : G → ℂ}
    (hInj : ∀ ξ, ξ ≠ 0 → sliceInjective (fun k q => R k q (q - ξ)))
    (hI : ∀ ξ, ξ ≠ 0 → ∀ k, ihat (R k) Ψ ξ = ihat (R k) Φ ξ)
    {ξ : G} (hξ : ξ ≠ 0) (q : G) :
    gram Ψ q (q - ξ) = gram Φ q (q - ξ) := by
  have hdiag :=
    lifted_unique_of_sliceInjective R (gram Ψ) (gram Φ) ξ (hInj ξ hξ)
      (fun k => by
        simp only [liftedApply_gram, hI ξ hξ k])
  exact hdiag q

/-- Stage-1 `stage1Pair` is the vacuum 2×2 Tikhonov solve on the CTF slice.
That is the remainder-dropped model: the same Cramer formula as
`analyticPair_of_remainder`, with `bilinearRemainder` replaced by `0`. -/
theorem stage1Pair_eq_analyticPair_linearized {p : LEEM} (α : ℝ)
    (Δz : κ → ℝ) (y : κ → ℝ → ℂ) (q : ℝ) :
    p.stage1Pair α Δz y q
      = tikhonovXhat2 α (p.sliceH Δz q) (p.sliceG Δz q) (fun k => y k q) :=
  p.stage1Pair_eq_tikhonovXhat2 α Δz y q

namespace LEEM

variable (p : LEEM)

/-- Yu 2D kernel sampled on a finite frequency group via `ι`. -/
noncomputable def sampledR (ι : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) :
    G → G → ℂ :=
  fun q q' => p.R_FO2 (ι q) (ι q') Δz

theorem sampledR_hermitian (ι : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ)
    (hσ : 0 ≤ p.sigmaE) (q q' : G) :
    conj (p.sampledR ι Δz q q') = p.sampledR ι Δz q' q :=
  p.R_FO2_hermitian hσ

theorem sampledR_dc (ι : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ)
    (hι : ι 0 = 0) (hap : 0 ≤ p.qAp) :
    p.sampledR ι Δz 0 0 = 1 := by
  simp [sampledR, hι, p.R_FO2_dc hap]

theorem sampledR_axis (ι : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) (q : G)
    (hι : ι 0 = 0) :
    p.sampledR ι Δz q 0 = p.R_FO ‖ι q‖ 0 Δz := by
  simp [sampledR, hι, p.R_FO2_eq_R_FO_axis]

theorem sampledR_conj_axis (ι : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ)
    (q : G) (hι : ι 0 = 0) (hneg : ι (-q) = -ι q) :
    p.sampledR ι Δz 0 (-q) = p.R_FO 0 (-‖ι q‖) Δz := by
  simp [sampledR, hι, hneg, p.R_FO2_eq_R_FO_conj_axis]

theorem ihat_sampledR (ι : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ)
    (Ψ : G → ℂ) (ξ : G) :
    ihat (p.sampledR ι Δz) Ψ ξ
      = ∑ q : G, p.sampledR ι Δz q (q - ξ) * gram Ψ q (q - ξ) :=
  ihat_eq_gram _ _ _

/-- Perfect-coherence sampling: bilinear FO is the pupil-modulated autocorrelation. -/
theorem ihat_sampledR_perfect (h : p.PerfectCoherence)
    (ι : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) (Ψ : G → ℂ) (ξ : G) :
    ihat (p.sampledR ι Δz) Ψ ξ
      = ∑ q : G,
          gram (fun t => Ψ t * p.coherentPupil2 Δz 0 (ι t)) q (q - ξ) := by
  have hR : p.sampledR ι Δz
      = fun q q' => p.coherentPupil2 Δz 0 (ι q)
          * conj (p.coherentPupil2 Δz 0 (ι q')) := by
    funext q q'
    simp [sampledR, p.R_FO2_eq_rank1_of_perfect h]
  rw [hR, ihat_of_rank1]

end LEEM

end
