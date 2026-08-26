# Linearized multi-defocus FO/CTF inverse: theorem list

This is stage 2 of the project: after the Yu 2019 FO kernel is encoded,
the discrete inverse is stated against that kernel.
The inverse note is [proofs/leemfo_inverse.pdf](proofs/leemfo_inverse.pdf).

This is the Lean-ready statement list for the **Fourier-diagonal Tikhonov
estimator** of the linearized FO/CTF slice and the **mixed large-phase
2D inverse** (TCC apply + Born homotopy + exact quartic line search).
Encoding: `LeemFO/Inverse/Tikhonov.lean`,
`LeemFO/Inverse/LinearInverse.lean`, `LeemFO/Inverse/Pipeline.lean`,
`LeemFO/Inverse/Modes.lean`, `LeemFO/Inverse/LowRank.lean`,
`LeemFO/Inverse/Homotopy.lean`, `LeemFO/Inverse/LineSearch.lean`,
`LeemFO/Inverse/Plane2.lean`, `LeemFO/Inverse/Mix.lean`.
The 2D working kernel is `LeemFO/Forward/Kernel2.lean`.

The object is finite-dimensional throughout. After a formal discrete Fourier
transform, each spatial-frequency bin is a map $`\kappa \to \mathbb{C}`$ of defocus
measurements ($`\kappa`$ is `Fin K` in applications). No analysis of FFT
correctness is used.

---

## Standing discrete model

Let $`\kappa`$ be a finite index of defoci and $`G`$ a finite abelian group of
sampled frequencies (in Lean: any `AddGroup` with `Fintype`).

| Symbol | Meaning |
|---|---|
| $`h : \kappa \to \mathbb{C}`$ | CTF-slice multipliers $`h_k = R_{\mathrm{FO}}(q, 0, \Delta z_k)`$ |
| $`g : \kappa \to \mathbb{C}`$ | conjugate-branch multipliers $`g_k = R_{\mathrm{FO}}(0, -q, \Delta z_k)`$ |
| $`y : \kappa \to \mathbb{C}`$ | measured Fourier coefficients of intensity (one bin) |
| $`x : \mathbb{C}`$ | unknown complex amplitude of that bin (weak-object / one branch) |
| $`(u, v) : \mathbb{C} \times \mathbb{C}`$ | pair $`(X(q), \overline{X(-q)})`$ in the vacuum $`2\times 2`$ Jacobian |
| $`\alpha > 0`$ | Tikhonov parameter |
| $`n : \kappa \to \mathbb{C}`$ | additive discrepancy $`y = h \cdot x^\star + n`$ (deterministic; not a probability space) |

The working kernel is the already-encoded $`R_{\mathrm{FO}}`$ (CTF-slice identity
`R_FO_eq_R_CTF_axis`).

---

## Lean theorems (encode these)

### T1. Unique minimizer ($`\alpha > 0`$)

**Statement.** For $`\alpha > 0`$ the energy

```math
J(x)=\sum_{k\in\kappa}\lVert h_k x-y_k\rVert^2+\alpha\lVert x\rVert^2
```

has a unique global minimizer

```math
\hat{x}=\frac{\sum_k \overline{h_k}\,y_k}{\alpha+\sum_k\lvert h_k\rvert^2}.
```

**Lean.** `tikhonovJ_min`, `tikhonov_unique`, closed form `tikhonovXhat`.
Proof: completing the square (`tikhonovJ_eq_completed` / `tikhonovJ_eq_shift`). The same identity
gives uniqueness at $`\alpha = 0`$ whenever $`\sum \lvert h_k\rvert^2 > 0`$
(`tikhonovDenom_pos_of_energy`).

**Tightness.** The Hessian is the positive real $`2(\alpha+\sum\lvert h\rvert^2)`$; no smaller
regularization yields a uniform unique-minimizer theorem for arbitrary $`h`$.

### T2. Bias–noise identity

**Statement.** If $`y_k = h_k x^\star + n_k`$ and $`D := \alpha+\sum\lvert h_k\rvert^2 \neq 0`$, then

```math
\hat{x}-x^\star
=\frac{\sum_k \overline{h_k}\,n_k-\alpha x^\star}{D}.
```

**Lean.** `tikhonov_error`.

This is an algebraic identity. It is **not** a statistical noise theorem:
$`n`$ is an arbitrary discrepancy (linearization remainder + instrument noise
+ discretization). Taking $`\mathbb{E}[n]=0`$ and $`\mathbb{E}[\lvert n_k\rvert^2]=\sigma^2`$ is informal (needs a
probability space, not used here).

### T3. Triangle bound

**Statement.** If $`\alpha \ge 0`$ and $`D > 0`$, then

```math
\lvert\hat{x}-x^\star\rvert
\le
\frac{\sum_k \lvert h_k\rvert\,\lvert n_k\rvert+\alpha\,\lvert x^\star\rvert}{D}.
```

**Lean.** `tikhonov_error_bound`.

**Tightness.** Equality is attained (`tikhonov_error_bound_sharp`): one
measurement, $`h=1`$, $`n=1`$, $`x^\star=-1`$, $`\alpha=1`$ gives both sides $`1`$.
The constant $`1`$ cannot be improved uniformly.

### T4. Aperture: modes with $`\lvert q\rvert>q_{\mathrm{ap}}`$ are invisible

**Statement.** If $`\lvert q\rvert>q_{\mathrm{ap}}`$ then $`R_{\mathrm{FO}}(q,0,\Delta z)=0`$ for every
defocus. Consequently the Tikhonov estimator of that bin is identically $`0`$
(for $`\alpha \neq 0`$), independently of the data.

If $`0 \le q_{\mathrm{ap}}`$, then $`R_{\mathrm{FO}}(q,0,\Delta z)=0`$ **iff** $`\lvert q\rvert>q_{\mathrm{ap}}`$
(waves and envelopes never vanish).

**Lean.** `R_FO_axis_eq_zero_of_outside`, `R_FO_axis_ne_zero_of_inside`,
`R_FO_axis_eq_zero_iff`, `tikhonovXhat_outside_aperture`.

This is the sharp support statement: the linearized slice cannot recover
aperture-blocked modes. It is **not** the same as a CTF zero of
$`\sin(2\pi\chi_S)`$ inside the disk (T8).

### T5. Gauge: $`I(\mathrm{e}^{i\theta}\psi)=I(\psi)`$

**Statement (spectrum).** For any bilinear kernel $`R`$ and any real $`\theta`$,

```math
\hat{I}\bigl(\mathrm{e}^{i\theta}\Psi\bigr)=\hat{I}(\Psi).
```

**Statement (real space).** $`\texttt{objectWave}\,\sigma\,(\varphi+\theta) = \mathrm{e}^{i\theta}\,\texttt{objectWave}\,\sigma\,\varphi`$.

**Lean.** `ihat_gauge`, `cexp_I_mul_conj`, `objectWave_phase_shift`.

The linearized inverse around a **fixed** vacuum therefore selects a gauge
(the vacuum phase). A second Gauss–Newton step about a non-vacuum
background does **not** restore global-phase invariance of the unknown.

### T6. Quadratic remainder of bilinear FO vs vacuum linearization

**Statement.** With vacuum spectrum $`\mathrm{vacuum} = 1_{q=0}`$ and increment $`\delta`$,

```math
\hat{I}(\mathrm{vac}+\delta)
=
\hat{I}(\mathrm{vac})
+ DI_{\mathrm{vac}}[\delta]
+ \hat{I}(\delta),
```

where

```math
DI_{\mathrm{vac}}[\delta](\xi)
= R(\xi,0)\,\delta(\xi)+R(0,-\xi)\,\overline{\delta(-\xi)}.
```

The dropped term is exactly bilinear in $`\delta`$. In particular

```math
\bigl\lvert\hat{I}(\delta)(\xi)\bigr\rvert
\le
\Bigl(\sum_{q,q'}\lvert R(q,q')\rvert\Bigr)\Bigl(\sum_q\lvert\delta(q)\rvert\Bigr)^2.
```

**Lean.** `ihat_add`, `ihatJac_vacuum`, `ihat_quadratic_remainder`,
`ihat_bound`.

**Tightness.** The remainder is homogeneous of degree 2 (not $`o(\lVert\delta\rVert^2)`$ in
general). The displayed constant is the elementary $`\ell^1`$ bound; the sharp
constant is the operator norm of $`R`$ on $`\ell^2`$, equivalently the Frobenius
bound $`\lVert R\rVert_F \lVert\delta\rVert_2^2`$. One Gauss–Newton step from vacuum **is**
Fourier-diagonal Tikhonov on $`DI_{\mathrm{vac}}`$. A further GN step at a
generic $`x_0`$ uses `ihatJac R x0`, which is **not** Fourier-diagonal.

### T7. Cost model: $`O(K N \log N)`$

**Statement (definition, not an FFT existence theorem).** Set
`dftCost N := N log₂ N` (modelled Cooley–Tukey cost) and
`binSolveCost K := 8K+4` (Gram/right-hand side for a scalar or $`2\times 2`$ solve).
Then

```math
\texttt{reconstructCost}(K,N)=(K+1)\,N\log_2 N+N(8K+4).
```

For $`K\ge 1`$, $`N\ge 2`$,

```math
\texttt{reconstructCost}(K,N)\le 14\,K\,N\log_2 N.
```

At $`N=128`$ this is already strictly cheaper than a dense bilinear apply
$`K N^2`$, for every $`K\ge 1`$.

**Lean.** `dftCost`, `reconstructCost`, `reconstructCost_le`,
`reconstructCost_lt_dense_128`, `exists_grid_diagonal_cheaper`.

**Informal.** Existence of an FFT achieving $`O(N \log N)`$ is **not** proved.
Neither is cache/architecture cost, nor that a DFT of the physical
continuous Fourier transform equals the array DFT.

### T8. Why this is asymptotically the cheapest CTF-zero-filling method
($`K \ge 2`$)

Two independent Lean facts, then an informal comparison.

**T8a. Complex object, vacuum Jacobian (any optics).** One complex
measurement of two complex unknowns $`(X(q), \overline{X(-q)})`$ always has a kernel.

**Lean.** `one_measurement_not_injective`. Hence $`K = 1`$ cannot identify a
general complex object even when $`R_{\mathrm{FO}}(q,0,\Delta z) \neq 0`$. Need $`K \ge 2`$ and
linearly independent columns $`(h,g)`$ for that bin.

**T8b. Weak-phase CTF zeros.** $`\sin(2\pi \chi_S(q,\Delta z))=0`$ whenever $`2\chi_S \in \mathbb{Z}`$.
For a pure-defocus NAC column ($`C_3=C_5=0`$, $`\Delta z \neq 0`$) a large enough
aperture contains a nonzero such $`q`$.

**Lean.** `weakPhase_sin_eq_zero`, `exists_interior_weakPhase_zero`.
Filling those zeros is exactly “$`\sum_k \sin^2(2\pi \chi_S(q,\Delta z_k)) > 0`$ on the
punctured aperture”, which a single defocus generically fails and two
defoci with incommensurate $`\Delta z`$ typically achieve. (Common zeros can
remain if $`\Delta z_2/\Delta z_1 \in \mathbb{Q}`$; $`K\ge 2`$ is necessary but not automatically
sufficient.)

**T8c. Cost among methods that fill zeros.** After $`K`$ modelled DFTs, any
algorithm that uses all $`KN`$ Fourier samples costs $`\Omega(KN)`$ arithmetic
(input-size lower bound). The diagonal Tikhonov solve is $`\Theta(KN)`$ plus the
modelled DFTs, matching T7. A dense bilinear apply is $`\Theta(KN^2)`$
(`denseApplyCost`), strictly larger at $`N=128`$ (T7).

**Informal (do not encode as a theorem).**
- Iterative bilinear / Gerchberg–Saxton / MAL: $`T`$ applications with $`T\ge 2`$
  cost at least twice the DFT leading term.
- Full FO Gauss–Newton about a generic background is not Fourier-diagonal
  (T6), so it is not $`O(KN \log N)`$ without a further Jacobian
  approximation.
- Statistical MSE rates, continuous Shannon sampling, and “fastest among
  *all* algorithms including unspecified real-space tricks” are outside
  the Lean fragment.

---

### T9. Fourier-domain pipeline map

Stage 1 is a reconstruction map on Fourier bins $`y_k(q)`$, not a
per-bin lemma in isolation.

**Scalar / 2×2 estimators.** `stage1Scalar` and `stage1Pair` apply T1 and
the vacuum $`2\times 2`$ closed form to the slices
$`h_k=R_{\mathrm{FO}}(q,0,\Delta z_k)`$ and
$`g_k=R_{\mathrm{FO}}(0,-q,\Delta z_k)`$. Modes with
$`\lvert q\rvert>q_{\mathrm{ap}}`$ map to $`0`$. The unknown pair is
$`(X(q),\overline{X(-q)})`$.

**Lean.** `sliceH`, `sliceG`, `stage1Scalar`, `stage1Pair`,
`stage1Scalar_unique`, `stage1Pair_unique`, `stage1Scalar_outside`,
`tikhonovXhat_outside_aperture`.

**Vacuum Gauss–Newton glue.** On an odd frequency embedding
$`q(-\xi)=-q(\xi)`$, the vacuum Jacobian residual is the $`2\times 2`$
model. One closed-form GN step from vacuum is therefore `stage1Pair`.

**Lean.** `ihatJac_vacuum_slice`, `vacuumGN_eq_stage1Pair`.

**DC / gauge.** If $`0\le q_{\mathrm{ap}}`$ then $`R_{\mathrm{FO}}(0,0,\Delta z)=1`$,
and the DC Jacobian sees $`\delta_0+\overline{\delta_0}=2\operatorname{Re}(\delta_0)`$.
The kernel is Hermitian for $`\sigma_E\ge 0`$, so
$`g_k(q)=\overline{h_k(-q)}`$.

**Lean.** `R_FO_dc`, `R_FO_hermitian`, `sliceH_dc`, `sliceG_dc`,
`sliceG_eq_conj_sliceH`, `ihatJac_vacuum_dc`, `ihatJac_vacuum_R_FO_dc`.

**Stage 2 skip (algebraic).** Skip nonlinear refinement when the bilinear
remainder is at a prescribed noise floor $`\eta`$:
$`\forall\xi,\;\lVert\hat I(R,\delta)(\xi)\rVert\le\eta`$. This is **not**
the numerical criterion $`\max\lvert\varphi\rvert\lesssim 0.3`$.

**Lean.** `stage1Remainder`, `stage2Skip`, `stage2Skip_of_bound`.

**1D sinusoid branch.** Sample $`R_{\mathrm{FO}}(n/\Lambda,m/\Lambda,\Delta z)`$
as `rFO`. The spatial image is the inverse Fourier sum of `ihatModes`
over difference frequencies in `modeDiffSet`. Harmonics outside
`modeSet` do not enter. The estimator is the least-squares cost
`sinusoidJ` / `stage2Sinusoid` (no GN iterator, no uniqueness of $`\varphi`$).

**Lean.** `rFO`, `discreteFOImage_eq_ihatModes`,
`discreteFOImage_eq_ihatModes_modeSet`, `sinusoidalFOImage_eq_ihatModes`,
`discreteFOImage_rFO_restrict`, `discreteFOImage_sub_sinusoidal_le`,
`sinusoidJ`, `stage2Sinusoid`.

**$`2\times 2`$ closed form.** Cramer solution of the regularized Gram
system; unique minimizer for $`\alpha>0`$; bias–noise identity.

**Lean.** `tikhonovXhat2`, `tikhonov2_solves`, `tikhonovJ2_eq_shift`,
`tikhonovJ2_min`, `tikhonov2_unique`, `tikhonov2_error`,
`stage1Pair_error`.

---

### T10. Two-dimensional kernel and stage-1 map

The 1D kernel $`R_{\mathrm{FO}}(q,q')`$ takes signed scalars. The 2D
working kernel $`R_{\mathrm{FO}2}(\mathbf{q},\mathbf{q}')`$ uses the disk
aperture, radial $`\chi_{S2}`$, and $`\mathbf{q}\cdot\mathbf{q}'`$ in
$`E_S`$. On the CTF slice $`\mathbf{q}'=0`$ it agrees with
$`R_{\mathrm{FO}}(\lVert\mathbf{q}\rVert,0)`$. Off axis it is **not**
$`R_{\mathrm{FO}}(\lVert\mathbf{q}\rVert,\lVert\mathbf{q}'\rVert)`$.

**Lean.** `R_FO2`, `R_FO2_eq_R_FO_axis`, `R_FO2_eq_R_FO_conj_axis`,
`R_FO2_hermitian`, `R_FO2_dc`, `exists_R_FO2_ne_R_FO_of_norms`,
`exists_aS2_ne_radial_aS`.

Odd embeddings $`\mathrm{qmap2}(-\xi)=-\mathrm{qmap2}\,\xi`$ force
$`\mathrm{qmap2}\,0=0`$ (`qmap2_zero`). Stage 1 on the disk is the
vacuum $`2\times 2`$ solve of the 2D slices
$`h_k=R_{\mathrm{FO}2}(\mathbf{q},0,\Delta z_k)`$,
$`g_k=R_{\mathrm{FO}2}(0,-\mathbf{q},\Delta z_k)`$.

**Lean.** `sliceH2`, `sliceG2`, `stage1Pair2`, `stage1Pair2_unique`,
`vacuumGN_eq_stage1Pair2`, `ihatJac_vacuum_R_FO2_dc`.

---

### T11. Rank-1 / finite TCC apply

If $`R(q,q')=h(q)\overline{h(q')}`$ then
$`\hat I(R,\Psi)=\mathrm{autocorr}(h\odot\Psi)`$ (no $`1/\lvert G\rvert`$
factor, matching `ihat`). A finite Hopkins sum is a weighted sum of
those autocorrelations. Under `PerfectCoherence` the sampled coherent
kernel (1D or 2D) is exactly rank-1. A truncated TCC is controlled by
the $`\ell^1`$ mass of the remainder.

LR+D keeps those TCC modes plus the matrix diagonal of the remainder
(`lrPlusDiag`); the discarded error is only off-diagonal mass, and the
leftover costs $`O(KN)`$ (`lrPlusDiagApplyCost_lt_dense_128`).

**Lean.** `rank1Kernel`, `tccKernel`, `ihat_rank1`, `ihat_tcc`,
`ihatJac_tcc`, `ihat_R0`, `ihat_R_FO_of_perfect`, `ihat_R0_2`,
`ihat_R_FO2_of_perfect`, `ihat_twoSource`, `ihat_tcc_trunc_bound`,
`lrPlusDiag`, `ihat_lrPlusDiag_trunc_bound`.

---

### T12. Exact quadratic homotopy (no cubic remainder)

For real $`t`$,

```math
\hat I(\mathrm{vac}+t\cdot\delta)
=
\hat I(\mathrm{vac})
+ t\,DI_{\mathrm{vac}}[\delta]
+ t^2\,\hat I(\delta).
```

There is no cubic term (`ihat_homotopy_cubic_zero`). The Born model
$`\hat I(\mathrm{vac})+DI_{\mathrm{vac}}[\delta]+t\,\hat I(\delta)`$
interpolates the vacuum linearization ($`t=0`$) and full FO ($`t=1`$).
At a Born fixed point the vacuum-Jacobian normal equations hold for the
nonlinear residual (`born_fixed_point_normal`).

**Lean.** `ihat_homotopy`, `ihat_homotopy_at`, `bornModel`,
`bornModel_sub`, `bornModel_t1_ne_t0`, `bornModel_t0_ne_full`,
`bornRhs_t0`, `bornRhs_sub`, `bornRhs_t1_ne_t0`,
`bornRhs_t0_ignores_loud`, `bornHomotopyPair_t0`,
`born_fixed_point_normal`, `exists_bornModel_t_disagree` (global
$`t`$ is not interchangeable across occupied bins). Quiet $`t=1`$
biases the stage-1 RHS; loud $`t=0`$ ignores the exact remainder.
Per-bin $`0/1`$ `remainderWeight` is the recommended large-$`\varphi`$
mix (not global $`t`$ and not fractional $`\min(1,\|\hat I(\delta)\|/\eta)`$).

---

### T13. Mixed 2D estimator

Init is vacuum $`2\times 2`$ Tikhonov. Each later step applies a damped
Born update of the pair $`(u,v)`$ (`mixedBinStep`) with schedules
$`t,\mathrm{damp}`$. `mixedSpectrum` stores only $`u=\delta(\xi)`$;
`mixedSpectrumPair` / `mixed2D` carry both coordinates. Per-bin
remainder weight uses $`t=0`$ on quiet bins and $`t=1`$ on loud bins
(`remainderWeight`, `mixedSpectrumMix`, `mixed2DMix`).

On $`R_{\mathrm{FO}2}`$, for $`\xi\neq 0`$, the $`n=0`$ iterate is
`stage1Pair2`.

**Lean.** `mixedBinStep`, `mixedSpectrum`, `mixedSpectrumPair`,
`mixedSpectrum_eq_pair_fst`, `mixed2D`, `mixedSpectrum2_zero_eq_stage1Pair2`,
`mixedSpectrumMix_skip_step`, `mixedSpectrumMix_born_bin`.

Nonlinear uniqueness is false (`ihat_gauge`). Iterative convergence is
not encoded (`picard_unique_of_lip` is only an algebraic contraction
implication).

---

### T14. Hermitian partner recovery

If $`h'=\overline{g}`$, $`g'=\overline{h}`$, $`y'=\overline{y}`$, then

```math
(\hat u',\hat v')=\bigl(\overline{\hat v},\,\overline{\hat u}\bigr).
```

Hermitian kernels give Hermitian intensities (`ihat_hermitian`). On an
odd embedding with Hermitian data,
$`\delta(-\xi)=\overline{v(\xi)}`$ is recovered from
`mixed2D n ξ`.snd (`mixed2D_conj_partner`). This is **not** automatic
on a general finite group.

**Lean.** `tikhonovXhat2_conj_swap`, `ihat_hermitian`,
`sliceG2_eq_conj_sliceH2`, `mixed2D_conj_partner`,
`mixedSpectrum_eq_conj_pair_snd`.

---

### T15. Exact quartic line search

Along $`x_0+s\cdot d`$ the residual is `quadPoly` of degree 2, so the
stack fidelity `lineFid` is a real quartic (`lineFid_quadEnergy`). The
formal $`s`$-derivative is `lineCubic`. A unit Gauss–Newton step
($`B=-A`$) has cubic value $`4\lVert C\rVert^2-2\operatorname{Re}(\overline A C)`$,
not identically zero (`lineCubic_exactGN`). The Gauss–Newton Hessian
coefficient $`\lVert B\rVert^2`$ drops the remainder coupling
$`2\operatorname{Re}(\overline A C)`$ (`exists_quadA2_ne_gn`). Roots of
the cubic are not constructed (no Cardano).

When $`A_1=\texttt{lineCubic}(\cdot)(0)<0`$, the algebraic Armijo step
`descentStep` (built from $`\lvert A_2\rvert+\lvert A_3\rvert+\lvert A_4\rvert`$)
gives $`\texttt{quadEnergy}(s)<\texttt{quadEnergy}(0)`$
(`quadEnergy_descent`); a unit step need not decrease energy
(`exists_unit_step_energy_increase`). After a Born / `mixedBinStep`
direction the FO-faithful 1D mix is `lineDescentStep` /
`lineFid_descent`. Full NLS energy on the ray is
`nlsJ_line`: $`\texttt{nlsJ}=\texttt{lineFid}+\alpha\sum\lVert x_0+s d\rVert^2`$.
Do not replace that 1D mix by a Tikhonov line: bins already use $`\alpha`$
in `mixedBinStep`. Fidelity-only `lineFid` can be flat while
$`\lVert x_0+s d\rVert`$ is unbounded (`exists_lineFid_flat_unbounded`).

**Lean.** `quadPoly`, `norm_sq_quadPoly`, `lineResidual_quadPoly`,
`lineFid_quadEnergy`, `quadEnergy_shift`, `lineCubic_exactGN`,
`lineCubic_exactGN_one_not_identically_zero`, `descentStep`,
`quadEnergy_armijo`, `quadEnergy_descent`,
`exists_unit_step_energy_increase`, `lineDescentStep`, `lineFid_descent`,
`nlsJ_line`, `lineFid_eq_nlsJ_zero`, `exists_lineFid_flat_unbounded`.

---

### T16. Cost: TCC / hybrid / rank-1 line search versus dense $`KN^2`$

Same discipline as T7 (`dftCost` is a definition, not an FFT theorem).

- Rank-$`M`$ apply: `tccApplyCost` $`=KM\cdot 2\cdot N\log_2 N`$. For
  $`M\le 8`$, $`N=128`$ this is strictly cheaper than dense
  $`KN^2`$ (`tccApplyCost_lt_dense_128`).
- One Born step = that apply plus $`N`$ of the $`2\times 2`$ solves
  (`bornStepCost_lt_dense_128`).
- Stage 1 plus $`T`$ Born steps: `hybridCost_lt_dense_succ`.
- Exact line search costs three TCC applies plus $`O(KN)`$ coefficient
  assembly. Under coherent rank-1 ($`M=1`$) that is still cheaper than
  dense at $`N=128`$ (`lineSearchCost_lt_dense_128_rank1`). Rank
  $`M=8`$ line search is **not** cheaper than dense (three applies
  exceed $`KN^2`$; `denseApplyCost_le_lineSearchCost_128_rank8`).
- Large rank: $`M=9`$ at $`N=128`$ is still strictly cheaper
  (`tccApplyCost_lt_dense_128_nine`, `lrPlusDiagApplyCost_lt_dense_128_nine`);
  for $`M\ge 10`$ the modelled TCC apply meets or exceeds dense
  (`denseApplyCost_le_tccApplyCost_128`). The Born cap stays $`M\le 8`$.
- Rank-adaptive policy `recommendTccRank`: cost-safe cap
  (`recommendTccCap`: $`M=1`$ under perfect coherence or line search,
  else $`M\le 8`$), then the smallest $`M`$ whose
  `ihat_tcc_trunc_bound` proxy meets the tolerance. Zero-weight padding
  of unused modes does not change `ihat`
  (`tccKernel_insert_weight_zero`, `ihat_tcc_insert_weight_zero`).
- LR+D with the same Born cap stays cheaper than dense
  (`lrPlusDiagApplyCost_recommend_lt_dense`).
- Batch `2\times 2` Cramer (`binSolveCost`) is strictly cheaper than one
  forgetful Kaczmarz sweep for $`K\ge 2`$
  (`binSolveCost_lt_kaczmarzCost_one_sweep`).

**Lean.** `tccApplyCost`, `bornStepCost`, `mixedCost`, `hybridCost`,
`lineSearchCost`, `quarticCoeffCost`, `recommendTccRank`,
`tccKernel_insert_weight_zero`, `lrPlusDiagApplyCost`, `kaczmarzCost`.

---

### T17. Rejected maps (concrete witnesses)

Competing numerical methods fail as identities on named NAC columns
`nacPC` / `nacCoh`.

| Map | Why it is not FO-faithful | Lean |
|---|---|---|
| TIE / Fresnel multiplier | wrong PDE; nonzero outside the aperture where FO is blind | `exists_interior_R_FO_ne_tie`, `exists_interior_R_FO2_ne_tie`, `R_FO_ne_tie_outside` |
| Coherent GS / HIO / ER | $`R_{\mathrm{CTF}}=R_{\mathrm{FO}}\Gamma_C\Gamma_S`$ and $`\Gamma_S\neq 1`$ off axis | `exists_R_CTF_ne_R_FO`, `exists_hio_kernel_ne_R_FO` |
| Partial-coherence $`R_0`$ | spatial envelope is not 1 | `exists_R_FO_ne_R0` |
| Single-defocus Wiener | vacuum $`2\times 2`$ always has a kernel | `exists_one_defocus_pair_kernel` |
| Weak-phase CTF $`\sin(2\pi\chi_S)`$ | can vanish while the FO slice does not | `exists_weakPhase_sin_zero_R_FO_ne_zero` |
| Radial 1D kernel as 2D | $`\mathbf{q}\cdot\mathbf{q}'`$ in $`E_S`$ | `exists_R_FO2_ne_R_FO_of_norms` |
| Jacobi–Anger as a 2D inverse | Bessel ladder $`M`$ vs bilinear $`M^2`$ pairs | `exists_modeSet_lt_modePairs` |
| Unit GN as exact line critical point | quartic cubic is not identically 0 at $`s=1`$ | `lineCubic_exactGN_one_not_identically_zero` |
| Gauss–Newton Hessian | drops remainder coupling $`2\operatorname{Re}(\overline A C)`$ | `exists_quadA2_ne_gn`, `exists_lineHess0_gn_ne_newton` |
| Quadratic Newton candidate $`-A_1/(2A_2)`$ | ignores $`A_3,A_4`$; not a cubic root; can raise energy | `exists_newtonCandidate_not_critical`, `exists_newtonCandidate_energy_increase` |
| Forgetful Kaczmarz sweep | last-row only; not `tikhonovJ2` minimizer for $`K\ge 2`$ | `exists_kaczmarzSweep_ne_tikhonovXhat2`, `exists_kaczmarzSweep_not_minimizer` |
| First-order Rytov increment | $`i\varphi`$ is not $`e^{i\varphi}-1`$ on FO | `exists_rytov_inc_ne_fo_phase` |

Dense Gauss–Newton about a generic background is FO-faithful but is
**not** Fourier-diagonal (T6) and is not $`O(KN\log N)`$ without a
further Jacobian approximation.

---

## Mixed large-phase 2D inverse (recommended)

From vacuum, one GN step **equals** T1 / the $`2\times 2`$ solve (T6, T9:
`vacuumGN_eq_stage1Pair` / T10 `vacuumGN_eq_stage1Pair2`). For large
$`\varphi`$ the recommended 2D estimator is that stage-1 init, then
remainder-corrected Born steps whose apply is rank-$`M`$ TCC
(`recommendTccRank`: $`M=1`$ if perfectly coherent or if using the
quartic line search, else $`M\le 8`$) or coherent rank-1
autocorrelation, optionally LR+D, mixed with per-bin skip
(`remainderWeight`) and algebraic Armijo on the exact quartic
(`lineDescentStep`). The mix is FO-faithful because bilinear FO is
exactly quadratic, and cheaper than a dense pair apply at $`N=128`$,
$`M\le 8`$ for the Born loop (T16). From a general $`x_0`$, one GN
step uses `ihatJac R x0`, which is **not** Fourier-diagonal. Do not
replace the batch $`2\times 2`$ by Kaczmarz; do not use the GN Hessian
in place of the exact quartic.

Do not encode local quadratic convergence of GN / Born (needs a
Lipschitz Hessian estimate in a Banach space of images). Do not encode
Cardano roots of the line cubic.

---

## Explicitly informal (do not encode)

| Item | Why |
|---|---|
| FFT algorithm exists / runs in $`O(N \log N)`$ wall-clock | complexity model only (`dftCost` is a definition) |
| Array DFT = continuum FT of the paper | sampling theory |
| Gaussian / Poisson noise, MSE, Cramér–Rao | no probability space |
| Frozen-aperture and first-order tilt truncations | already flagged `Approx.` in the forward model |
| “Fastest among all conceivable inverses” | only DFT-based / dense-bilinear / TCC comparisons are proved |
| Global convergence of nonlinear GN / GS / Born | not an identity (`picard_unique_of_lip` is only a contraction implication) |
| Cardano roots of `lineCubic` | algebraic stationarity only |
| Banach fixed-point existence for Picard | uniqueness under a Lipschitz hypothesis only |
| Nesterov / Polyak / Heavy-ball / FISTA rates | not an FO identity; same bucket as GN/Born convergence |
| Complex-step line search as the 1D quartic | sesquilinear in $`(\sigma,\overline{\sigma})`$, not `quadPoly` |
| Trust-region / dogleg / cubic regularization | quadratic model is not the FO quartic; cubic min is Cardano |
| Wirtinger / ADMM / PhaseLift convergence | not an FO identity; PC kernel mismatch is `exists_R_FO_ne_R0` |
| Replace `lineFid` by Tikhonov line energy | bins already use $`\alpha`$; companion is `nlsJ_line` |

---

## Encoding map

| ID | Lean names |
|---|---|
| T1 | `tikhonovJ`, `tikhonovXhat`, `tikhonovJ_eq_shift`, `tikhonovJ_eq_completed`, `tikhonovJ_min`, `tikhonov_unique` |
| T2 | `tikhonov_error` |
| T3 | `tikhonov_error_bound`, `tikhonov_error_bound_sharp` |
| T4 | `R_FO_axis_eq_zero_of_outside`, `R_FO_axis_eq_zero_iff`, `tikhonovXhat_outside_aperture` |
| T5 | `ihat_gauge`, `objectWave_phase_shift` |
| T6 | `ihat_add`, `ihatJac_vacuum`, `ihat_quadratic_remainder`, `ihat_bound` |
| T7 | `dftCost`, `reconstructCost`, `reconstructCost_le`, `reconstructCost_lt_dense_128` |
| T8 | `one_measurement_not_injective`, `weakPhase_sin_eq_zero`, `exists_interior_weakPhase_zero` |
| $`2\times 2`$ Gram | `tikhonovJ2`, `tikhonovXhat2`, `gramDet_pos`, `tikhonovJ2_eq_shift`, `tikhonovJ2_min`, `tikhonov2_unique`, `tikhonov2_error` |
| T9 | `stage1Scalar`, `stage1Pair`, `stage1Scalar_unique`, `stage1Pair_unique`, `vacuumGN_eq_stage1Pair`, `ihatJac_vacuum_slice`, `ihatJac_vacuum_R_FO_dc`, `stage2Skip`, `rFO`, `sinusoidJ`, `R_FO_hermitian`, `R_FO_dc` |
| T10 | `R_FO2`, `stage1Pair2`, `qmap2_zero`, `vacuumGN_eq_stage1Pair2`, `exists_R_FO2_ne_R_FO_of_norms` |
| T11 | `ihat_rank1`, `ihat_tcc`, `ihat_R0`, `ihat_R_FO_of_perfect`, `ihat_R_FO2_of_perfect`, `ihat_tcc_trunc_bound`, `ihat_twoSource`, `lrPlusDiag` |
| T12 | `ihat_homotopy`, `ihat_homotopy_cubic_zero`, `bornModel`, `bornModel_sub`, `bornModel_t1_ne_t0`, `bornModel_t0_ne_full`, `bornRhs_t0`, `bornRhs_sub`, `bornRhs_t1_ne_t0`, `bornRhs_t0_ignores_loud`, `born_fixed_point_normal` |
| T13 | `mixedBinStep`, `mixedSpectrum`, `mixedSpectrumPair`, `mixed2D`, `mixedSpectrumMix`, `remainderWeight` |
| T14 | `tikhonovXhat2_conj_swap`, `ihat_hermitian`, `mixed2D_conj_partner` |
| T15 | `quadPoly`, `norm_sq_quadPoly`, `lineFid_quadEnergy`, `descentStep`, `nlsJ_line`, `lineFid_eq_nlsJ_zero`, `exists_lineFid_flat_unbounded`, `exists_newtonCandidate_not_critical` |
| T16 | `tccApplyCost_lt_dense_128`, `tccApplyCost_lt_dense_128_nine`, `hybridCost_lt_dense_succ`, `lineSearchCost_lt_dense_128_rank1`, `recommendTccRank`, `tccKernel_insert_weight_zero`, `denseApplyCost_le_tccApplyCost_128`, `kaczmarzCost` |
| T17 | `exists_interior_R_FO_ne_tie`, `exists_interior_R_FO2_ne_tie`, `exists_R_CTF_ne_R_FO`, `exists_hio_kernel_ne_R_FO`, `exists_rytov_inc_ne_fo_phase`, `exists_kaczmarzSweep_ne_tikhonovXhat2` |
