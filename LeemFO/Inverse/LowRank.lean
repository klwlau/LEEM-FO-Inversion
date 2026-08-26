/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Inverse.LinearInverse
import LeemFO.Forward.CTF

/-!
# Rank-1 / finite TCC apply of bilinear FO

When `R(q,q') = h(q) conj(h(q'))` the discrete intensity `ihat` is the
cyclic autocorrelation of `h ⊙ Ψ`. A finite Hopkins sum of such terms
is the algebraic TCC / coherent-mode expansion. Cost is modelled as
`K M` pairs of DFTs versus a dense `K N²` pair sum (same discipline as
`dftCost`: no FFT existence theorem). Rank-adaptive `M` is chosen by
`recommendTccRank` from the `ihat_tcc_trunc_bound` proxy versus the
cost-safe caps `M=1` (perfect coherence / line search) and `M≤8`
(Born/hybrid at `N=128`); zero-weight padding is free
(`tccKernel_insert_weight_zero`).
-/

open Complex
open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-- Pointwise (Hadamard) product `h ⊙ Ψ`. -/
def hadamard (h Ψ : G → ℂ) : G → ℂ := fun q => h q * Ψ q

/-- Cyclic autocorrelation of a spectrum (no `1/|G|` factor, matching `ihat`). -/
def autocorr (Φ : G → ℂ) (ξ : G) : ℂ :=
  ∑ q : G, Φ q * conj (Φ (q - ξ))

/-- Fréchet derivative of `autocorr` at `Φ0` along `Δ`. -/
def autocorrJac (Φ0 Δ : G → ℂ) (ξ : G) : ℂ :=
  ∑ q : G, Φ0 q * conj (Δ (q - ξ)) + ∑ q : G, Δ q * conj (Φ0 (q - ξ))

/-- Rank-1 coherent kernel `R(q,q') = h(q) conj(h(q'))`. -/
def rank1Kernel (h : G → ℂ) : G → G → ℂ :=
  fun q q' => h q * conj (h q')

/-- Finite Hopkins / TCC kernel on a source list `src`. -/
def tccKernel {ι : Type*} (w : ι → ℂ) (h : ι → G → ℂ) (src : Finset ι) :
    G → G → ℂ :=
  fun q q' => ∑ m ∈ src, w m * h m q * conj (h m q')

@[simp] lemma hadamard_apply (h Ψ : G → ℂ) (q : G) :
    hadamard h Ψ q = h q * Ψ q := rfl

lemma rank1Kernel_hermitian (h : G → ℂ) (q q' : G) :
    conj (rank1Kernel h q q') = rank1Kernel h q' q := by
  simp [rank1Kernel, map_mul]
  ring

/-- Rank-1 bilinear intensity is the autocorrelation of the pupil-filtered spectrum. -/
theorem ihat_rank1 (h Ψ : G → ℂ) (ξ : G) :
    ihat (rank1Kernel h) Ψ ξ = autocorr (hadamard h Ψ) ξ := by
  unfold ihat rank1Kernel autocorr hadamard
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [map_mul]
  ring

theorem ihat_sum {ι : Type*} (R : ι → G → G → ℂ) (src : Finset ι)
    (Ψ : G → ℂ) (ξ : G) :
    ihat (fun q q' => ∑ m ∈ src, R m q q') Ψ ξ
      = ∑ m ∈ src, ihat (R m) Ψ ξ := by
  unfold ihat
  have hterm (q : G) :
      Ψ q * (∑ m ∈ src, R m q (q - ξ)) * conj (Ψ (q - ξ))
        = ∑ m ∈ src, Ψ q * R m q (q - ξ) * conj (Ψ (q - ξ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun q _ => hterm q).trans ?_
  exact Finset.sum_comm

theorem ihat_smul_kernel (c : ℂ) (R : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) :
    ihat (fun q q' => c * R q q') Ψ ξ = c * ihat R Ψ ξ := by
  unfold ihat
  have hterm (q : G) :
      Ψ q * (c * R q (q - ξ)) * conj (Ψ (q - ξ))
        = c * (Ψ q * R q (q - ξ) * conj (Ψ (q - ξ))) := by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]

/-- Finite TCC apply: `ihat` is a weighted sum of rank-1 autocorrelations. -/
theorem ihat_tcc {ι : Type*} (w : ι → ℂ) (h : ι → G → ℂ) (src : Finset ι)
    (Ψ : G → ℂ) (ξ : G) :
    ihat (tccKernel w h src) Ψ ξ
      = ∑ m ∈ src, w m * autocorr (hadamard (h m) Ψ) ξ := by
  unfold tccKernel
  have hR :
      (fun q q' => ∑ m ∈ src, w m * h m q * conj (h m q'))
        = fun q q' => ∑ m ∈ src, w m * rank1Kernel (h m) q q' := by
    funext q q'
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [rank1Kernel]
    ring
  rw [hR, ihat_sum (R := fun m => fun q q' => w m * rank1Kernel (h m) q q')]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ihat_smul_kernel, ihat_rank1]

theorem ihatJac_rank1 (h x0 δ : G → ℂ) (ξ : G) :
    ihatJac (rank1Kernel h) x0 δ ξ
      = autocorrJac (hadamard h x0) (hadamard h δ) ξ := by
  unfold ihatJac rank1Kernel autocorrJac hadamard
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp [map_mul]
    ring
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp [map_mul]
    ring

theorem autocorr_add (Φ0 Δ : G → ℂ) (ξ : G) :
    autocorr (Φ0 + Δ) ξ
      = autocorr Φ0 ξ + autocorrJac Φ0 Δ ξ + autocorr Δ ξ := by
  simpa [autocorr, autocorrJac, ihat, ihatJac] using
    ihat_add (fun _ _ => (1 : ℂ)) Φ0 Δ ξ

theorem ihatJac_sum {ι : Type*} (R : ι → G → G → ℂ) (src : Finset ι)
    (x0 δ : G → ℂ) (ξ : G) :
    ihatJac (fun q q' => ∑ m ∈ src, R m q q') x0 δ ξ
      = ∑ m ∈ src, ihatJac (R m) x0 δ ξ := by
  unfold ihatJac
  have h1 :
      ∑ q : G, x0 q * (∑ m ∈ src, R m q (q - ξ)) * conj (δ (q - ξ))
        = ∑ m ∈ src, ∑ q : G, x0 q * R m q (q - ξ) * conj (δ (q - ξ)) := by
    have hterm (q : G) :
        x0 q * (∑ m ∈ src, R m q (q - ξ)) * conj (δ (q - ξ))
          = ∑ m ∈ src, x0 q * R m q (q - ξ) * conj (δ (q - ξ)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_congr rfl fun q _ => hterm q).trans Finset.sum_comm
  have h2 :
      ∑ q : G, δ q * (∑ m ∈ src, R m q (q - ξ)) * conj (x0 (q - ξ))
        = ∑ m ∈ src, ∑ q : G, δ q * R m q (q - ξ) * conj (x0 (q - ξ)) := by
    have hterm (q : G) :
        δ q * (∑ m ∈ src, R m q (q - ξ)) * conj (x0 (q - ξ))
          = ∑ m ∈ src, δ q * R m q (q - ξ) * conj (x0 (q - ξ)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_congr rfl fun q _ => hterm q).trans Finset.sum_comm
  rw [h1, h2, ← Finset.sum_add_distrib]

theorem ihatJac_smul_kernel (c : ℂ) (R : G → G → ℂ) (x0 δ : G → ℂ) (ξ : G) :
    ihatJac (fun q q' => c * R q q') x0 δ ξ = c * ihatJac R x0 δ ξ := by
  unfold ihatJac
  have h1 (q : G) :
      x0 q * (c * R q (q - ξ)) * conj (δ (q - ξ))
        = c * (x0 q * R q (q - ξ) * conj (δ (q - ξ))) := by ring
  have h2 (q : G) :
      δ q * (c * R q (q - ξ)) * conj (x0 (q - ξ))
        = c * (δ q * R q (q - ξ) * conj (x0 (q - ξ))) := by ring
  simp_rw [h1, h2]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add]

theorem ihatJac_tcc {ι : Type*} (w : ι → ℂ) (h : ι → G → ℂ) (src : Finset ι)
    (x0 δ : G → ℂ) (ξ : G) :
    ihatJac (tccKernel w h src) x0 δ ξ
      = ∑ m ∈ src, w m *
          autocorrJac (hadamard (h m) x0) (hadamard (h m) δ) ξ := by
  unfold tccKernel
  have hR :
      (fun q q' => ∑ m ∈ src, w m * h m q * conj (h m q'))
        = fun q q' => ∑ m ∈ src, w m * rank1Kernel (h m) q q' := by
    funext q q'
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [rank1Kernel]
    ring
  rw [hR, ihatJac_sum (R := fun m => fun q q' => w m * rank1Kernel (h m) q q')]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ihatJac_smul_kernel, ihatJac_rank1]

/-- Sampled coherent kernel is rank-1, so `ihat` is an autocorrelation. -/
theorem ihat_R0 (p : LEEM) (qmap : G → ℝ) (Δz ε : ℝ) (Ψ : G → ℂ) (ξ : G) :
    ihat (fun a b => p.R0 (qmap a) (qmap b) Δz ε) Ψ ξ
      = autocorr (hadamard (fun a => p.coherentPupil Δz ε (qmap a)) Ψ) ξ := by
  have hR :
      (fun a b => p.R0 (qmap a) (qmap b) Δz ε)
        = rank1Kernel (fun a => p.coherentPupil Δz ε (qmap a)) := by
    funext a b
    exact p.R0_eq_rank1 (qmap a) (qmap b) Δz ε
  rw [hR, ihat_rank1]

theorem ihat_R_FO_of_perfect (p : LEEM) (hpc : p.PerfectCoherence)
    (qmap : G → ℝ) (Δz : ℝ) (Ψ : G → ℂ) (ξ : G) :
    ihat (fun a b => p.R_FO (qmap a) (qmap b) Δz) Ψ ξ
      = autocorr (hadamard (fun a => p.coherentPupil Δz 0 (qmap a)) Ψ) ξ := by
  have hR :
      (fun a b => p.R_FO (qmap a) (qmap b) Δz)
        = fun a b => p.R0 (qmap a) (qmap b) Δz 0 := by
    funext a b
    exact p.R_FO_eq_R0_of_perfect hpc (qmap a) (qmap b) Δz
  rw [hR, ihat_R0]

/-! ## Modelled rank-`M` apply cost (no FFT existence theorem) -/

/-- Rank-`M` Hopkins apply: `K` defoci × `M` modes × two modelled DFTs
(IFFT of `h⊙Ψ`, FFT of `|φ|²`). The Hadamard product is `O(N)`, not a third DFT. -/
def tccApplyCost (K M N : ℕ) : ℕ :=
  K * M * 2 * dftCost N

lemma tccApplyCost_formula (K M N : ℕ) :
    tccApplyCost K M N = K * M * 2 * N * N.log2 := by
  simp [tccApplyCost, dftCost]
  ring

lemma tccApplyCost_8_128 (K : ℕ) :
    tccApplyCost K 8 128 = 14336 * K := by
  rw [tccApplyCost_formula, log2_128]
  ring

/-- At `N = 128` a rank-`M≤8` apply is strictly cheaper than a dense `K N²` pair sum. -/
theorem tccApplyCost_lt_dense_128 {K M : ℕ} (hK : 1 ≤ K) (hM : M ≤ 8) :
    tccApplyCost K M 128 < denseApplyCost K 128 := by
  unfold tccApplyCost denseApplyCost dftCost
  rw [log2_128]
  have hcore : 2 * 7 * M < 128 :=
    lt_of_le_of_lt (Nat.mul_le_mul_left (2 * 7) hM)
      (by decide : 2 * 7 * 8 < 128)
  have hKN : 0 < K * 128 := Nat.mul_pos hK (by decide : 0 < 128)
  have hL : K * M * 2 * (128 * 7) = K * 128 * (2 * 7 * M) := by ring
  rw [hL]
  exact Nat.mul_lt_mul_of_pos_left hcore hKN

theorem exists_grid_tcc_cheaper {K M : ℕ} (hK : 1 ≤ K) (hM : M ≤ 8) :
    ∃ N, 128 ≤ N ∧ tccApplyCost K M N < denseApplyCost K N :=
  ⟨128, le_rfl, tccApplyCost_lt_dense_128 hK hM⟩

/-- One Born step: rank-`M` apply of `ihat(δ)` plus `N` of the `2×2` bin solves. -/
def bornStepCost (K M N : ℕ) : ℕ :=
  tccApplyCost K M N + N * binSolveCost K

def mixedCost (T K M N : ℕ) : ℕ :=
  T * bornStepCost K M N

lemma bornStepCost_8_128 (K : ℕ) :
    bornStepCost K 8 128 = 15360 * K + 512 := by
  simp [bornStepCost, tccApplyCost, dftCost, binSolveCost, log2_128]
  ring

/-- One mixed step (TCC apply + diagonal solve) stays cheaper than one dense apply. -/
theorem bornStepCost_lt_dense_128 {K M : ℕ} (hK : 1 ≤ K) (hM : M ≤ 8) :
    bornStepCost K M 128 < denseApplyCost K 128 := by
  unfold bornStepCost denseApplyCost
  have happly : tccApplyCost K M 128 ≤ tccApplyCost K 8 128 := by
    unfold tccApplyCost dftCost
    rw [log2_128]
    have hmul : K * M * 2 * 128 * 7 ≤ K * 8 * 2 * 128 * 7 := by
      have := Nat.mul_le_mul_left K (Nat.mul_le_mul_right (2 * 128 * 7) hM)
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hnum : tccApplyCost K 8 128 + 128 * binSolveCost K
      < denseApplyCost K 128 := by
    rw [tccApplyCost_8_128, denseApplyCost, binSolveCost]
    have hpow : K * 128 * 128 = 16384 * K := by ring
    rw [hpow]
    have hbin : 128 * (8 * K + 4) = 1024 * K + 512 := by ring
    rw [hbin]
    have : 15360 * K + 512 < 16384 * K := by
      have h512 : 512 < 1024 * K :=
        lt_of_lt_of_le (by decide : 512 < 1024)
          (Nat.le_mul_of_pos_right 1024 hK)
      omega
    calc
      14336 * K + (1024 * K + 512) = 15360 * K + 512 := by ring
      _ < 16384 * K := this
  exact lt_of_le_of_lt (Nat.add_le_add_right happly _) hnum

theorem mixedCost_lt_dense_T {T K M : ℕ} (hT : 1 ≤ T) (hK : 1 ≤ K) (hM : M ≤ 8) :
    mixedCost T K M 128 < T * denseApplyCost K 128 := by
  unfold mixedCost
  have hstep := bornStepCost_lt_dense_128 (K := K) (M := M) hK hM
  exact Nat.mul_lt_mul_of_pos_left hstep hT

theorem ihat_add_kernel (R₁ R₂ : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) :
    ihat (fun q q' => R₁ q q' + R₂ q q') Ψ ξ
      = ihat R₁ Ψ ξ + ihat R₂ Ψ ξ := by
  unfold ihat
  simp [add_mul, mul_add, Finset.sum_add_distrib]

/-- Algebraic two-source Hopkins kernel: finite TCC on `Fin 2`. -/
lemma tccKernel_fin2 (w : Fin 2 → ℂ) (pupil : Fin 2 → G → ℂ) :
    tccKernel w pupil Finset.univ
      = fun q q' =>
          w 0 * rank1Kernel (pupil 0) q q'
            + w 1 * rank1Kernel (pupil 1) q q' := by
  funext q q'
  simp [tccKernel, rank1Kernel, Fin.sum_univ_two]
  ring

/-- Two rank-1 pupils: `ihat` is the corresponding sum of autocorrelations. -/
theorem ihat_twoSource (w₁ w₂ : ℂ) (h₁ h₂ Ψ : G → ℂ) (ξ : G) :
    ihat (fun q q' => w₁ * rank1Kernel h₁ q q' + w₂ * rank1Kernel h₂ q q') Ψ ξ
      = w₁ * autocorr (hadamard h₁ Ψ) ξ
        + w₂ * autocorr (hadamard h₂ Ψ) ξ := by
  rw [ihat_add_kernel, ihat_smul_kernel, ihat_smul_kernel, ihat_rank1,
    ihat_rank1]

theorem ihat_sub_kernel (R₁ R₂ : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) :
    ihat (fun q q' => R₁ q q' - R₂ q q') Ψ ξ
      = ihat R₁ Ψ ξ - ihat R₂ Ψ ξ := by
  unfold ihat
  simp [sub_mul, mul_sub, Finset.sum_sub_distrib]

/-- Truncating the bilinear kernel controls the apply error by the `ℓ¹` mass. -/
theorem ihat_approx_bound (R Rapprox : G → G → ℂ) (Ψ : G → ℂ) (ξ : G) :
    ‖ihat R Ψ ξ - ihat Rapprox Ψ ξ‖
      ≤ (∑ q : G, ∑ q' : G, ‖R q q' - Rapprox q q'‖) * (∑ q : G, ‖Ψ q‖) ^ 2 := by
  rw [← ihat_sub_kernel]
  exact ihat_bound (fun q q' => R q q' - Rapprox q q') Ψ ξ

def tccRemainder {ι : Type*} (R : G → G → ℂ) (w : ι → ℂ) (h : ι → G → ℂ)
    (src : Finset ι) : G → G → ℂ :=
  fun q q' => R q q' - tccKernel w h src q q'

theorem ihat_tcc_trunc_bound {ι : Type*} (R : G → G → ℂ)
    (w : ι → ℂ) (h : ι → G → ℂ) (src : Finset ι) (Ψ : G → ℂ) (ξ : G) :
    ‖ihat R Ψ ξ - ihat (tccKernel w h src) Ψ ξ‖
      ≤ (∑ q : G, ∑ q' : G, ‖tccRemainder R w h src q q'‖) *
        (∑ q : G, ‖Ψ q‖) ^ 2 :=
  ihat_approx_bound R (tccKernel w h src) Ψ ξ

/-- Stage-1 reconstruct plus `T` mixed Born steps. -/
def hybridCost (T K M N : ℕ) : ℕ :=
  reconstructCost K N + mixedCost T K M N

theorem hybridCost_lt_dense_succ {T K M : ℕ} (hK : 1 ≤ K) (hM : M ≤ 8) :
    hybridCost T K M 128 < (T + 1) * denseApplyCost K 128 := by
  unfold hybridCost mixedCost
  have h1 := reconstructCost_lt_dense_128 (K := K) hK
  have h2 := bornStepCost_lt_dense_128 (K := K) (M := M) hK hM
  have hT : T * bornStepCost K M 128 ≤ T * denseApplyCost K 128 :=
    Nat.mul_le_mul_left T (Nat.le_of_lt h2)
  have hle :
      reconstructCost K 128 + T * bornStepCost K M 128
        ≤ reconstructCost K 128 + T * denseApplyCost K 128 :=
    Nat.add_le_add_left hT (reconstructCost K 128)
  have hlt :
      reconstructCost K 128 + T * denseApplyCost K 128
        < denseApplyCost K 128 + T * denseApplyCost K 128 :=
    Nat.add_lt_add_right h1 (T * denseApplyCost K 128)
  have hsum :
      denseApplyCost K 128 + T * denseApplyCost K 128
        = (T + 1) * denseApplyCost K 128 := by ring
  exact lt_of_le_of_lt hle (hsum ▸ hlt)

/-- Assembly of the five real quartic coefficients along a line, `O(KN)`. -/
def quarticCoeffCost (K N : ℕ) : ℕ := 5 * K * N

theorem quarticCoeffCost_lt_dense_128 {K : ℕ} (hK : 1 ≤ K) :
    quarticCoeffCost K 128 < denseApplyCost K 128 := by
  have : 640 * K < 16384 * K :=
    Nat.mul_lt_mul_of_pos_right (by decide : 640 < 16384) hK
  simpa [quarticCoeffCost, denseApplyCost, mul_assoc, mul_left_comm, mul_comm]
    using this

/-- Three TCC applies (forward, Jacobian, remainder) plus quartic assembly. -/
def lineSearchCost (K M N : ℕ) : ℕ :=
  3 * tccApplyCost K M N + quarticCoeffCost K N

lemma lineSearchCost_formula (K M N : ℕ) :
    lineSearchCost K M N = 3 * tccApplyCost K M N + 5 * K * N := by
  simp [lineSearchCost, quarticCoeffCost]

/-- Coherent rank-1 exact line search stays cheaper than a dense pair apply
at `N = 128`. Rank-`M = 8` does not: three applies exceed `K N²`. -/
theorem lineSearchCost_lt_dense_128_rank1 {K : ℕ} (hK : 1 ≤ K) :
    lineSearchCost K 1 128 < denseApplyCost K 128 := by
  unfold lineSearchCost denseApplyCost quarticCoeffCost
  rw [tccApplyCost_formula, log2_128]
  have : 3 * (K * 1 * 2 * 128 * 7) + 5 * K * 128 < K * 128 * 128 := by
    have hL : 3 * (K * 1 * 2 * 128 * 7) + 5 * K * 128 = 6016 * K := by ring
    have hR : K * 128 * 128 = 16384 * K := by ring
    rw [hL, hR]
    exact Nat.mul_lt_mul_of_pos_right (by decide : 6016 < 16384) hK
  exact this

theorem reconstructCost_lt_bornStep_8_128 {K : ℕ} (hK : 1 ≤ K) :
    reconstructCost K 128 < bornStepCost K 8 128 := by
  rw [reconstructCost_128, bornStepCost_8_128]
  have : 1920 * K + 1408 < 15360 * K + 512 := by
    have hgap : 896 < 13440 * K :=
      lt_of_lt_of_le (by decide : 896 < 13440)
        (Nat.le_mul_of_pos_right 13440 hK)
    omega
  exact this


/-! ## Zero-weight padding and rank-adaptive `M` -/

/-- An unused Hopkins mode with weight `0` does not change the TCC kernel
(padding the source list is free algebraically). -/
theorem tccKernel_insert_weight_zero {ι : Type*} [DecidableEq ι]
    (w : ι → ℂ) (h : ι → G → ℂ) (src : Finset ι) (m : ι) (hw : w m = 0) :
    tccKernel w h (insert m src) = tccKernel w h src := by
  funext q q'
  by_cases hm : m ∈ src
  · simp [tccKernel, Finset.insert_eq_of_mem hm]
  · simp [tccKernel, Finset.sum_insert hm, hw]

/-- Consequently `ihat` is unchanged by zero-weight padding. -/
theorem ihat_tcc_insert_weight_zero {ι : Type*} [DecidableEq ι]
    (w : ι → ℂ) (h : ι → G → ℂ) (src : Finset ι) (m : ι) (hw : w m = 0)
    (Ψ : G → ℂ) (ξ : G) :
    ihat (tccKernel w h (insert m src)) Ψ ξ
      = ihat (tccKernel w h src) Ψ ξ := by
  rw [tccKernel_insert_weight_zero w h src m hw]

/-- Dropping modes with weight `0` leaves the TCC kernel unchanged. -/
theorem tccKernel_filter_ne_zero {ι : Type*} [DecidableEq ι]
    (w : ι → ℂ) (h : ι → G → ℂ) (src : Finset ι) :
    tccKernel w h (src.filter fun m => w m ≠ 0) = tccKernel w h src := by
  funext q q'
  refine (Finset.sum_filter_of_ne (s := src)
    (f := fun m => w m * h m q * conj (h m q')) ?_).symm
  intro m _ hterm
  exact fun hw => hterm (by simp [hw])

lemma tccApplyCost_mono {K M₁ M₂ N : ℕ} (hM : M₁ ≤ M₂) :
    tccApplyCost K M₁ N ≤ tccApplyCost K M₂ N := by
  simp only [tccApplyCost, dftCost]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    Nat.mul_le_mul_right (2 * N * N.log2) (Nat.mul_le_mul_left K hM)

/-- At `N = 128`, once `M ≥ 10` the modelled TCC apply meets or exceeds dense
`K N²` (large rank approaches the dense pair-sum cost). -/
theorem denseApplyCost_le_tccApplyCost_128 {K M : ℕ} (hM : 10 ≤ M) :
    denseApplyCost K 128 ≤ tccApplyCost K M 128 := by
  unfold tccApplyCost denseApplyCost dftCost
  rw [log2_128]
  have hcore : 128 ≤ 2 * 7 * M :=
    le_trans (by decide : 128 ≤ 2 * 7 * 10) (Nat.mul_le_mul_left (2 * 7) hM)
  have hL : K * M * 2 * (128 * 7) = K * 128 * (2 * 7 * M) := by ring
  rw [hL]
  exact Nat.mul_le_mul_left (K * 128) hcore

/-- Exact line search at rank `M = 8` is not cheaper than a dense apply at
`N = 128` (three TCC applies already exceed `K N²`). -/
theorem denseApplyCost_le_lineSearchCost_128_rank8 {K : ℕ} :
    denseApplyCost K 128 ≤ lineSearchCost K 8 128 := by
  unfold lineSearchCost denseApplyCost quarticCoeffCost
  rw [tccApplyCost_formula, log2_128]
  have hL : 3 * (K * 8 * 2 * 128 * 7) + 5 * K * 128 = 43648 * K := by ring
  have hR : K * 128 * 128 = 16384 * K := by ring
  rw [hL, hR]
  exact Nat.mul_le_mul_right K (by decide : 16384 ≤ 43648)

/-- Cost-safe Hopkins-rank cap at the `N = 128` design point:
* perfect coherence → exact `M = 1` (`ihat_R_FO_of_perfect`);
* exact line search → `M = 1` (`lineSearchCost_lt_dense_128_rank1`;
  rank 8 is not cheaper: `denseApplyCost_le_lineSearchCost_128_rank8`);
* Born / hybrid apply → `M ≤ 8` (`tccApplyCost_lt_dense_128`). -/
def recommendTccCap (perfectCoherence lineSearch : Bool) : ℕ :=
  if perfectCoherence then 1
  else if lineSearch then 1
  else 8

/-- Smallest `M ∈ {1,…,Mcap}` with `truncOk M`, else `Mcap`.
Interpret `truncOk M` as the `ihat_tcc_trunc_bound` proxy meeting the
tolerance: `(∑∑‖R - tcc_M‖) * (∑‖Ψ‖)² ≤ ε`. -/
def chooseTccRank (Mcap : ℕ) (truncOk : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 Mcap).filter truncOk).min.getD Mcap

/-- Rank-adaptive policy: cost-safe cap, then minimal truncation that meets
the error budget. Zero-weight padding of unused slots is free
(`tccKernel_insert_weight_zero`). -/
def recommendTccRank (perfectCoherence lineSearch : Bool)
    (truncOk : ℕ → Bool) : ℕ :=
  chooseTccRank (recommendTccCap perfectCoherence lineSearch) truncOk

lemma recommendTccCap_perfect (lineSearch : Bool) :
    recommendTccCap true lineSearch = 1 := by
  simp [recommendTccCap]

lemma recommendTccCap_lineSearch :
    recommendTccCap false true = 1 := by
  simp [recommendTccCap]

lemma recommendTccCap_born :
    recommendTccCap false false = 8 := by
  simp [recommendTccCap]

lemma chooseTccRank_le (Mcap : ℕ) (truncOk : ℕ → Bool) :
    chooseTccRank Mcap truncOk ≤ Mcap := by
  simp only [chooseTccRank]
  cases hmin : ((Finset.Icc 1 Mcap).filter truncOk).min with
  | none => simp [hmin, Option.getD]
  | some M =>
    have hmem : M ∈ (Finset.Icc 1 Mcap).filter truncOk :=
      Finset.mem_of_min hmin
    have hIcc : M ∈ Finset.Icc 1 Mcap := Finset.mem_of_mem_filter hmem
    exact (Finset.mem_Icc.mp hIcc).2

lemma recommendTccRank_le_cap (perfectCoherence lineSearch : Bool)
    (truncOk : ℕ → Bool) :
    recommendTccRank perfectCoherence lineSearch truncOk
      ≤ recommendTccCap perfectCoherence lineSearch :=
  chooseTccRank_le _ _

/-- Born/hybrid policy stays strictly cheaper than dense apply at `N = 128`. -/
theorem tccApplyCost_recommend_lt_dense_born {K : ℕ} (hK : 1 ≤ K)
    (truncOk : ℕ → Bool) :
    tccApplyCost K (recommendTccRank false false truncOk) 128
      < denseApplyCost K 128 := by
  have hM : recommendTccRank false false truncOk ≤ 8 := by
    simpa [recommendTccCap_born] using
      recommendTccRank_le_cap false false truncOk
  exact tccApplyCost_lt_dense_128 hK hM

/-- Perfect-coherence or line-search policy uses at most `M = 1`, so exact
line search stays under dense at `N = 128`. -/
theorem lineSearchCost_recommend_lt_dense {K : ℕ} (hK : 1 ≤ K)
    (perfectCoherence : Bool) (truncOk : ℕ → Bool) :
    lineSearchCost K (recommendTccRank perfectCoherence true truncOk) 128
      < denseApplyCost K 128 := by
  have hcap : recommendTccCap perfectCoherence true = 1 := by
    cases perfectCoherence <;> simp [recommendTccCap]
  have hle : recommendTccRank perfectCoherence true truncOk ≤ 1 := by
    simpa [hcap] using recommendTccRank_le_cap perfectCoherence true truncOk
  have hcost :
      lineSearchCost K (recommendTccRank perfectCoherence true truncOk) 128
        ≤ lineSearchCost K 1 128 := by
    simp only [lineSearchCost]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 3 (tccApplyCost_mono (K := K) (N := 128) hle)) _
  exact lt_of_le_of_lt hcost (lineSearchCost_lt_dense_128_rank1 hK)


end
