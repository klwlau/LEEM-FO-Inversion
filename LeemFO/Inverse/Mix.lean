/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.Homotopy
import LeemFO.Inverse.Plane2
import LeemFO.Inverse.Modes
import LeemFO.Forward.Kernel2
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Mixed 2D inverse: TCC apply + Born homotopy, with rejects

Recommended large-`φ` 2D estimator: vacuum `2×2` Tikhonov (`stage1Pair2`),
then remainder-corrected Born steps (`mixed2D` / `mixedSpectrum2`) whose
apply is rank-`M` TCC (`ihat_tcc`) or exact rank-1 autocorrelation under
`PerfectCoherence`. Per-bin remainder weight (`remainderWeight`) skips Born
on quiet bins (`t = 0`) and takes the full remainder (`t = 1`) otherwise.
Bilinear FO is exactly quadratic, so the homotopy in `t` has no cubic
term. Competing maps (TIE, coherent GS, linearized CTF, radial 1D kernel,
1D Jacobi–Anger as a 2D inverse) fail as identities on concrete columns.

Hermitian kernel plus Hermitian data on an odd embedding recovers the
dropped partner: `δ(-ξ) = conj v(ξ)` (`mixed2D_conj_partner`).

Iterative convergence, Banach fixed-point existence, Cardano line search,
and uniqueness of the nonlinear inverse are not encoded (`ihat_gauge`;
`picard_unique_of_lip` is only an algebraic contraction implication).
FFT existence is not encoded (`dftCost` is a cost model).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Complex Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

open LEEM

noncomputable section

/-- NAC unit column with partial spatial coherence. -/
def nacPC : LEEM :=
  { lam := 1, E := 1, C3 := 0, C5 := 0, CC := 0, CCC := 0, C3C := 0,
    qAp := 1, qIll := 1, ΔE := 0 }

/-- Same column, perfect coherence. -/
def nacCoh : LEEM :=
  { lam := 1, E := 1, C3 := 0, C5 := 0, CC := 0, CCC := 0, C3C := 0,
    qAp := 1, qIll := 0, ΔE := 0 }

lemma nacPC_sigmaIll_ne_zero : nacPC.sigmaIll ≠ 0 := by
  unfold nacPC LEEM.sigmaIll
  exact div_ne_zero one_ne_zero (ne_of_gt fwhmFactor_pos)

lemma nacCoh_perfect : nacCoh.PerfectCoherence := ⟨rfl, rfl⟩

lemma nacCoh_chiS_half : nacCoh.chiS 1 1 = 1 / 2 := by
  simp [LEEM.chiS, nacCoh]

lemma nacCoh_waveS_neg : nacCoh.waveS 1 1 = -1 := by
  unfold LEEM.waveS
  rw [nacCoh_chiS_half]
  have : (2 : ℂ) * π * I * (1 / 2 : ℝ) = π * I := by
    simp
    ring
  rw [this, Complex.exp_pi_mul_I]

set_option linter.flexible false in
/-- Interior TIE multiplier is not the FO CTF slice. -/
theorem exists_interior_R_FO_ne_tie :
    ∃ p : LEEM, ∃ q Δz : ℝ,
      |q| ≤ p.qAp ∧ p.R_FO q 0 Δz ≠ tieMultiplier p.lam Δz q := by
  refine ⟨nacCoh, 1, 1, ?_, ?_⟩
  · simp [nacCoh]
  · have hR : nacCoh.R_FO 1 0 1 = nacCoh.R0 1 0 1 0 :=
      nacCoh.R_FO_eq_R0_of_perfect nacCoh_perfect 1 0 1
    have hR0 : nacCoh.R0 1 0 1 0 = -1 := by
      unfold LEEM.R0
      simp [nacCoh, LEEM.waveS_zero, LEEM.waveC_at_zero]
      exact nacCoh_waveS_neg
    have hT : tieMultiplier nacCoh.lam 1 1 = 2 * π * I := by
      simp [tieMultiplier, nacCoh]
    rw [hR, hR0, hT]
    intro h
    have : (-1 : ℂ).re = (2 * π * I).re := congrArg Complex.re h
    simp at this

set_option linter.flexible false in
/-- Partial spatial coherence: FO kernel is not the coherent projector. -/
theorem exists_R_FO_ne_R0 :
    ∃ p : LEEM, ∃ q q' Δz : ℝ,
      p.sigmaIll ≠ 0 ∧ p.R0 q q' Δz 0 ≠ 0 ∧
      p.R_FO q q' Δz ≠ p.R0 q q' Δz 0 := by
  refine ⟨nacPC, 1, 0, 1, nacPC_sigmaIll_ne_zero, ?_, ?_⟩
  · simp [LEEM.R0, nacPC, LEEM.waveS_zero, LEEM.waveC_at_zero]
    exact Complex.exp_ne_zero _
  · have hC : chromaticEnvelopeClosed nacPC.sigmaE (nacPC.b1 1 0) (nacPC.b2 1 0) = 1 := by
      have hσ : nacPC.sigmaE = 0 := by simp [nacPC, LEEM.sigmaE]
      rw [hσ]
      exact chromaticEnvelopeClosed_of_sigma_zero _ _
    have ha : nacPC.aS 1 0 1 = 1 := by simp [LEEM.aS, nacPC]
    have hE :
        nacPC.spatialEnvelopeClosed 1 0 1 ≠ 1 := by
      unfold LEEM.spatialEnvelopeClosed
      rw [ha]
      intro h
      have hx : (-(2 : ℝ) * π ^ 2 * nacPC.sigmaIll ^ 2 * (1 : ℝ) ^ 2) = 0 :=
        (LEEM.cexp_ofReal_eq_one).mp (by simpa using h)
      have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have hσ := nacPC_sigmaIll_ne_zero
      have : (2 : ℝ) * π ^ 2 * nacPC.sigmaIll ^ 2 = 0 := by
        nlinarith
      rcases mul_eq_zero.mp this with hL | hσ2
      · rcases mul_eq_zero.mp hL with h2 | hπ2
        · exact (by norm_num : (2 : ℝ) ≠ 0) h2
        · exact hπ (sq_eq_zero_iff.mp hπ2)
      · exact hσ (sq_eq_zero_iff.mp hσ2)
    unfold LEEM.R_FO
    rw [hC, mul_one]
    intro h
    have hR0 : nacPC.R0 1 0 1 0 ≠ 0 := by
      simp [LEEM.R0, nacPC, LEEM.waveS_zero, LEEM.waveC_at_zero]
      exact Complex.exp_ne_zero _
    have heq :
        nacPC.R0 1 0 1 0 * nacPC.spatialEnvelopeClosed 1 0 1
          = nacPC.R0 1 0 1 0 * 1 := by
      simpa using h
    exact hE (mul_left_cancel₀ hR0 heq)

/-- Rank-1 remainder of vacuum linearization is the whole DC image of a
single occupied sideband. -/
theorem ihat_single_mode {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (R : G → G → ℂ) (q0 : G) :
    ihat R (fun q => if q = q0 then (1 : ℂ) else 0) 0 = R q0 q0 := by
  unfold ihat
  rw [Fintype.sum_eq_single q0]
  · simp
  · intro q hq
    simp [hq]

theorem exists_rank1_remainder_ne_zero :
    ∃ p : LEEM, ∃ qmap : ZMod 2 → ℝ, ∃ δ : ZMod 2 → ℂ, ∃ Δz : ℝ,
      ihat (fun a b => p.R_FO (qmap a) (qmap b) Δz) δ 0 ≠ 0 := by
  let qmap : ZMod 2 → ℝ := fun q => if q = 1 then 1 else 0
  let δ : ZMod 2 → ℂ := fun q => if q = 1 then 1 else 0
  refine ⟨nacCoh, qmap, δ, 1, ?_⟩
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  have hq : qmap 1 = 1 := if_pos rfl
  have hih :
      ihat (fun a b => nacCoh.R_FO (qmap a) (qmap b) 1) δ 0
        = nacCoh.R_FO (qmap 1) (qmap 1) 1 := by
    simpa [δ] using
      ihat_single_mode (fun a b => nacCoh.R_FO (qmap a) (qmap b) 1) (1 : ZMod 2)
  rw [hih, hq]
  have hdiag : nacCoh.R_FO 1 1 1 = 1 :=
    nacCoh.R_FO_diag (by simp [nacCoh])
  simp [hdiag]

/-- Off-axis 2D spatial envelope is not the 1D radial formula. -/
theorem exists_aS2_ne_radial_aS :
    ∃ p : LEEM, ∃ q q' : EuclideanSpace ℝ (Fin 2), ∃ Δz : ℝ,
      ‖q‖ = ‖q'‖ ∧
      ‖p.aS2 q q' Δz‖ ^ 2 ≠ p.aS ‖q‖ ‖q'‖ Δz ^ 2 := by
  let q := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  let q' := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  refine ⟨nacPC, q, q', 1, ?_, ?_⟩
  · simp [q, q']
  · have hq : ‖q‖ = 1 := by simp [q]
    have hq' : ‖q'‖ = 1 := by simp [q']
    have hin : ⟪q, q'⟫ = 0 := by
      simp [q, q', EuclideanSpace.inner_single_left]
    have hu : nacPC.uS q 1 = 1 := by simp [LEEM.uS, nacPC, q]
    have hu' : nacPC.uS q' 1 = 1 := by simp [LEEM.uS, nacPC, q']
    have hL : ‖nacPC.aS2 q q' 1‖ ^ 2 = 2 := by
      rw [nacPC.aS2_normSq, hu, hu', hq, hq', hin]
      norm_num
    have hR : nacPC.aS ‖q‖ ‖q'‖ 1 = 0 := by
      rw [hq, hq']
      simp [LEEM.aS, nacPC]
    rw [hL, hR]
    norm_num

set_option linter.flexible false in
theorem exists_R_FO2_ne_R_FO_of_norms :
    ∃ p : LEEM, ∃ q q' : EuclideanSpace ℝ (Fin 2), ∃ Δz : ℝ,
      p.sigmaIll ≠ 0 ∧
      p.R_FO2 q q' Δz ≠ p.R_FO ‖q‖ ‖q'‖ Δz := by
  let q := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  let q' := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  refine ⟨nacPC, q, q', 1, nacPC_sigmaIll_ne_zero, ?_⟩
  have hq : ‖q‖ = 1 := by simp [q]
  have hq' : ‖q'‖ = 1 := by simp [q']
  have hdiag : nacPC.R_FO 1 1 1 = 1 := nacPC.R_FO_diag (by simp [nacPC])
  have hR1 : nacPC.R_FO ‖q‖ ‖q'‖ 1 = 1 := by
    simpa [hq, hq'] using hdiag
  have hin : ⟪q, q'⟫ = 0 := by
    simp [q, q', EuclideanSpace.inner_single_left]
  have hu : nacPC.uS q 1 = 1 := by simp [LEEM.uS, nacPC, q]
  have hu' : nacPC.uS q' 1 = 1 := by simp [LEEM.uS, nacPC, q']
  have ha2 : ‖nacPC.aS2 q q' 1‖ ^ 2 = 2 := by
    rw [nacPC.aS2_normSq, hu, hu', hq, hq', hin]
    norm_num
  have hC :
      chromaticEnvelopeClosed nacPC.sigmaE (nacPC.b1 1 1) (nacPC.b2 1 1) = 1 := by
    rw [nacPC.b1_zero_diag, nacPC.b2_zero_diag, chromaticEnvelopeClosed_nac]
    simp
  have hR0 : nacPC.R0_2 q q' 1 0 = 1 := by
    rw [nacPC.R0_2_eq_R0, hq, hq']
    have hw : nacPC.waveS 1 1 * conj (nacPC.waveS 1 1) = 1 := by
      rw [nacPC.waveS_mul_conj, sub_self]
      simp
    unfold LEEM.R0
    simp [nacPC, LEEM.waveC_at_zero]
    exact hw
  have hE :
      nacPC.spatialEnvelopeClosed2 q q' 1 ≠ 1 := by
    unfold LEEM.spatialEnvelopeClosed2
    rw [ha2]
    intro h
    have hx :
        (-(2 : ℝ) * π ^ 2 * nacPC.sigmaIll ^ 2 * (2 : ℝ)) = 0 :=
      (LEEM.cexp_ofReal_eq_one).mp (by simpa using h)
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hσ := nacPC_sigmaIll_ne_zero
    have : (2 : ℝ) * π ^ 2 * nacPC.sigmaIll ^ 2 * 2 = 0 := by
      nlinarith
    rcases mul_eq_zero.mp this with hL | h2
    · rcases mul_eq_zero.mp hL with hL' | hσ2
      · rcases mul_eq_zero.mp hL' with h2' | hπ2
        · exact (by norm_num : (2 : ℝ) ≠ 0) h2'
        · exact hπ (sq_eq_zero_iff.mp hπ2)
      · exact hσ (sq_eq_zero_iff.mp hσ2)
    · exact (by norm_num : (2 : ℝ) ≠ 0) h2
  unfold LEEM.R_FO2
  rw [hR0, hq, hq', hC, mul_one]
  intro h
  have hES : nacPC.spatialEnvelopeClosed2 q q' 1 = 1 := by
    have h' := h.trans hdiag
    simpa using h'
  exact hE hES

/-! ## Rank-1 2D apply and exact line quartic -/

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

theorem ihat_R0_2 (p : LEEM) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (Δz ε : ℝ) (Ψ : G → ℂ) (ξ : G) :
    ihat (fun a b => p.R0_2 (qmap a) (qmap b) Δz ε) Ψ ξ
      = autocorr (hadamard (fun a => p.coherentPupil2 Δz ε (qmap a)) Ψ) ξ := by
  have hR :
      (fun a b => p.R0_2 (qmap a) (qmap b) Δz ε)
        = rank1Kernel (fun a => p.coherentPupil2 Δz ε (qmap a)) := by
    funext a b
    exact p.R0_2_eq_rank1 (qmap a) (qmap b) Δz ε
  rw [hR, ihat_rank1]

theorem ihat_R_FO2_of_perfect (p : LEEM) (hpc : p.PerfectCoherence)
    (qmap : G → EuclideanSpace ℝ (Fin 2)) (Δz : ℝ) (Ψ : G → ℂ) (ξ : G) :
    ihat (fun a b => p.R_FO2 (qmap a) (qmap b) Δz) Ψ ξ
      = autocorr (hadamard (fun a => p.coherentPupil2 Δz 0 (qmap a)) Ψ) ξ := by
  have hR :
      (fun a b => p.R_FO2 (qmap a) (qmap b) Δz)
        = fun a b => p.R0_2 (qmap a) (qmap b) Δz 0 := by
    funext a b
    exact p.R_FO2_eq_R0_2_of_perfect hpc (qmap a) (qmap b) Δz
  rw [hR, ihat_R0_2]

theorem bornRhs_of_perfect {κ : Type*} [Fintype κ] (p : LEEM)
    (hpc : p.PerfectCoherence) (qmap : G → ℝ) (Δz : κ → ℝ)
    (y : κ → G → ℂ) (t : ℝ) (δ : G → ℂ) (ξ : G) :
    bornRhs (fun k a b => p.R_FO (qmap a) (qmap b) (Δz k)) y t δ ξ
      = fun k =>
          yLin (fun k a b => p.R_FO (qmap a) (qmap b) (Δz k)) y ξ k
            - (t : ℂ) * autocorr
                (hadamard (fun a => p.coherentPupil (Δz k) 0 (qmap a)) δ) ξ := by
  funext k
  simp [bornRhs, ihat_R_FO_of_perfect p hpc]

theorem bornRhs_of_perfect2 {κ : Type*} [Fintype κ] (p : LEEM)
    (hpc : p.PerfectCoherence) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (Δz : κ → ℝ) (y : κ → G → ℂ) (t : ℝ) (δ : G → ℂ) (ξ : G) :
    bornRhs (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y t δ ξ
      = fun k =>
          yLin (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y ξ k
            - (t : ℂ) * autocorr
                (hadamard (fun a => p.coherentPupil2 (Δz k) 0 (qmap a)) δ)
                  ξ := by
  funext k
  simp [bornRhs, ihat_R_FO2_of_perfect p hpc]

/-- Stationarity cubic of a real quartic (exact line energy of bilinear FO). -/
def lineCubic (A1 A2 A3 A4 : ℝ) (s : ℝ) : ℝ :=
  A1 + 2 * A2 * s + 3 * A3 * s ^ 2 + 4 * A4 * s ^ 3

theorem lineCubic_zero (A1 A2 A3 A4 : ℝ) : lineCubic A1 A2 A3 A4 0 = A1 := by
  simp [lineCubic]

/-- A unit Gauss–Newton step is not automatically a critical point of the
exact quartic line energy. -/
theorem lineCubic_one_not_identically_zero :
    ¬∀ A1 A2 A3 A4 : ℝ, lineCubic A1 A2 A3 A4 1 = 0 := by
  intro h
  have := h 1 0 0 0
  simp [lineCubic] at this

variable {κ : Type*} [Fintype κ]

theorem yLin_of_ne_zero (R : κ → G → G → ℂ) (y : κ → G → ℂ) {ξ : G}
    (hξ : ξ ≠ 0) :
    yLin R y ξ = fun k => y k ξ := by
  funext k
  simp [yLin, ihat_vacuum, hξ]

theorem mixedSpectrum_zero_eq_stage1Pair {p : LEEM} (α : ℝ)
    (qmap : G → ℝ) (Δz : κ → ℝ) (y : κ → G → ℂ) (t damp : ℕ → ℝ)
    {ξ : G} (hξ : ξ ≠ 0) :
    mixedSpectrum α
        (fun ξ k => p.sliceH Δz (qmap ξ) k)
        (fun ξ k => p.sliceG Δz (qmap ξ) k)
        (fun k a b => p.R_FO (qmap a) (qmap b) (Δz k)) y t damp 0 ξ
      = (tikhonovXhat2 α (p.sliceH Δz (qmap ξ)) (p.sliceG Δz (qmap ξ))
          (fun k => y k ξ)).1 := by
  simp [mixedSpectrum, yLin_of_ne_zero _ y hξ]

/-! ## End-to-end 2D mixed inverse on `R_FO2` -/

/-- 2D mixed spectrum iterate: CTF slices of `R_FO2` on embedding `qmap`. -/
def mixedSpectrum2 (p : LEEM) (α : ℝ) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (Δz : κ → ℝ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) : ℕ → G → ℂ :=
  mixedSpectrum α
    (fun ξ => p.sliceH2 Δz (qmap ξ))
    (fun ξ => p.sliceG2 Δz (qmap ξ))
    (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y t damp

/-- Pair-valued 2D mixed iterate (`mixedBinStep` on each bin). -/
def mixedSpectrumPair2 (p : LEEM) (α : ℝ) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (Δz : κ → ℝ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) : ℕ → G → ℂ × ℂ :=
  mixedSpectrumPair α
    (fun ξ => p.sliceH2 Δz (qmap ξ))
    (fun ξ => p.sliceG2 Δz (qmap ξ))
    (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y t damp

/-- End-to-end 2D mixed inverse: vacuum `2×2` at `t = 0`, then Born homotopy. -/
def mixed2D (p : LEEM) (α : ℝ) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (Δz : κ → ℝ) (y : κ → G → ℂ) (t damp : ℕ → ℝ) : ℕ → G → ℂ × ℂ :=
  mixedSpectrumPair2 p α qmap Δz y t damp

/-- Per-bin skip/Born mix on the 2D kernel. -/
def mixed2DMix (p : LEEM) (α : ℝ) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (Δz : κ → ℝ) (y : κ → G → ℂ) (η : ℝ) (damp : ℕ → ℝ) : ℕ → G → ℂ :=
  mixedSpectrumMix α
    (fun ξ => p.sliceH2 Δz (qmap ξ))
    (fun ξ => p.sliceG2 Δz (qmap ξ))
    (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y η damp

theorem mixedSpectrum2_eq_pair_fst (p : LEEM) (α : ℝ)
    (qmap : G → EuclideanSpace ℝ (Fin 2)) (Δz : κ → ℝ)
    (y : κ → G → ℂ) (t damp : ℕ → ℝ) :
    ∀ n, mixedSpectrum2 p α qmap Δz y t damp n
      = fun ξ => (mixed2D p α qmap Δz y t damp n ξ).1 :=
  mixedSpectrum_eq_pair_fst α
    (fun ξ => p.sliceH2 Δz (qmap ξ))
    (fun ξ => p.sliceG2 Δz (qmap ξ))
    (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y t damp

theorem mixedSpectrum2_zero_eq_tikhonovXhat2 (p : LEEM) (α : ℝ)
    (qmap : G → EuclideanSpace ℝ (Fin 2)) (Δz : κ → ℝ)
    (y : κ → G → ℂ) (t damp : ℕ → ℝ) {ξ : G} (hξ : ξ ≠ 0) :
    mixedSpectrum2 p α qmap Δz y t damp 0 ξ
      = (tikhonovXhat2 α (p.sliceH2 Δz (qmap ξ)) (p.sliceG2 Δz (qmap ξ))
          (fun k => y k ξ)).1 := by
  simp [mixedSpectrum2, mixedSpectrum, yLin_of_ne_zero _ y hξ]

/-- Init equals `stage1Pair2` for `ξ ≠ 0` (inside or outside the disk). -/
theorem mixedSpectrum2_zero_eq_stage1Pair2 (p : LEEM) (α : ℝ)
    (qmap : G → EuclideanSpace ℝ (Fin 2)) (Δz : κ → ℝ)
    (y : κ → G → ℂ) (t damp : ℕ → ℝ) {ξ : G} (hξ : ξ ≠ 0) :
    mixedSpectrum2 p α qmap Δz y t damp 0 ξ
      = (p.stage1Pair2 α Δz (fun k _ => y k ξ) (qmap ξ)).1 := by
  rw [mixedSpectrum2_zero_eq_tikhonovXhat2 p α qmap Δz y t damp hξ,
    p.stage1Pair2_eq_tikhonovXhat2]

theorem mixed2D_zero_eq_tikhonovXhat2 (p : LEEM) (α : ℝ)
    (qmap : G → EuclideanSpace ℝ (Fin 2)) (Δz : κ → ℝ)
    (y : κ → G → ℂ) (t damp : ℕ → ℝ) {ξ : G} (hξ : ξ ≠ 0) :
    mixed2D p α qmap Δz y t damp 0 ξ
      = tikhonovXhat2 α (p.sliceH2 Δz (qmap ξ)) (p.sliceG2 Δz (qmap ξ))
          (fun k => y k ξ) := by
  simp [mixed2D, mixedSpectrumPair2, mixedSpectrumPair,
    yLin_of_ne_zero _ y hξ]

theorem mixed2D_zero_eq_stage1Pair2 (p : LEEM) (α : ℝ)
    (qmap : G → EuclideanSpace ℝ (Fin 2)) (Δz : κ → ℝ)
    (y : κ → G → ℂ) (t damp : ℕ → ℝ) {ξ : G} (hξ : ξ ≠ 0) :
    mixed2D p α qmap Δz y t damp 0 ξ
      = p.stage1Pair2 α Δz (fun k _ => y k ξ) (qmap ξ) := by
  rw [mixed2D_zero_eq_tikhonovXhat2 p α qmap Δz y t damp hξ,
    p.stage1Pair2_eq_tikhonovXhat2]

/-- Hermitian kernel + Hermitian data on an odd embedding: the dropped
partner is `conj` of `mixed2D n ξ`.snd. -/
theorem mixed2D_conj_partner (p : LEEM) (hσ : 0 ≤ p.sigmaE) (α : ℝ)
    (qmap : G → EuclideanSpace ℝ (Fin 2))
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : κ → ℝ) (y : κ → G → ℂ)
    (hy : ∀ k ξ, y k (-ξ) = conj (y k ξ))
    (t damp : ℕ → ℝ) (n : ℕ) (ξ : G) :
    mixed2D p α qmap Δz y t damp n (-ξ)
      = (conj (mixed2D p α qmap Δz y t damp n ξ).2,
        conj (mixed2D p α qmap Δz y t damp n ξ).1) := by
  refine mixedSpectrumPair_conj_partner α
    (fun ζ => p.sliceH2 Δz (qmap ζ))
    (fun ζ => p.sliceG2 Δz (qmap ζ))
    (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y t damp ξ ?hh ?hg ?hR
      ?hyLin n
  · funext k
    rw [hq ξ]
    have hsg := p.sliceG2_eq_conj_sliceH2 hσ Δz (qmap ξ) k
    simpa using (congrArg conj hsg).symm
  · funext k
    rw [hq ξ]
    simpa [neg_neg] using p.sliceG2_eq_conj_sliceH2 hσ Δz (-qmap ξ) k
  · intro k a b
    exact p.R_FO2_hermitian (q := qmap a) (q' := qmap b) (Δz := Δz k) hσ
  · refine yLin_hermitian
        (fun k a b => p.R_FO2 (qmap a) (qmap b) (Δz k)) y ξ ?_ fun k => hy k ξ
    intro k a b
    exact p.R_FO2_hermitian (q := qmap a) (q' := qmap b) (Δz := Δz k) hσ

theorem mixedSpectrum2_eq_conj_pair_snd (p : LEEM) (hσ : 0 ≤ p.sigmaE)
    (α : ℝ) (qmap : G → EuclideanSpace ℝ (Fin 2))
    (hq : ∀ ξ, qmap (-ξ) = -qmap ξ) (Δz : κ → ℝ) (y : κ → G → ℂ)
    (hy : ∀ k ξ, y k (-ξ) = conj (y k ξ))
    (t damp : ℕ → ℝ) (n : ℕ) (ξ : G) :
    mixedSpectrum2 p α qmap Δz y t damp n (-ξ)
      = conj (mixed2D p α qmap Δz y t damp n ξ).2 := by
  rw [mixedSpectrum2_eq_pair_fst]
  have hpair := mixed2D_conj_partner p hσ α qmap hq Δz y hy t damp n ξ
  simpa [mixed2D] using congrArg Prod.fst hpair

theorem mixed2DMix_zero_eq_stage1Pair2 (p : LEEM) (α : ℝ)
    (qmap : G → EuclideanSpace ℝ (Fin 2)) (Δz : κ → ℝ)
    (y : κ → G → ℂ) (η : ℝ) (damp : ℕ → ℝ) {ξ : G} (hξ : ξ ≠ 0) :
    mixed2DMix p α qmap Δz y η damp 0 ξ
      = (p.stage1Pair2 α Δz (fun k _ => y k ξ) (qmap ξ)).1 := by
  simp [mixed2DMix, mixedSpectrumMix, yLin_of_ne_zero _ y hξ,
    p.stage1Pair2_eq_tikhonovXhat2]

end
