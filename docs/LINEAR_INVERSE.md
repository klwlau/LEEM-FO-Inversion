# Linearized multi-defocus FO/CTF inverse: theorem list

This is stage 2 of the project: after the Yu 2019 FO kernel is encoded,
the discrete inverse is stated against that kernel.
The inverse note is [proofs/leemfo_inverse.pdf](proofs/leemfo_inverse.pdf).

This is the Lean-ready statement list for the **Fourier-diagonal Tikhonov
estimator** of the linearized FO/CTF slice (optionally one Gauss–Newton
step). Encoding: `LeemFO/Inverse/Tikhonov.lean`,
`LeemFO/Inverse/LinearInverse.lean`, `LeemFO/Inverse/Pipeline.lean`,
`LeemFO/Inverse/Modes.lean`. The analytic bilinear inverse (Gram lift,
small-mode closed forms, 2D kernel degeneracy) is
`LeemFO/Inverse/Gram.lean`, `SmallMode.lean`, `Degeneracy.lean`,
`Analytic.lean`, `Fiber.lean`, with 2D kernel `LeemFO/Forward/Kernel2.lean`.

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

## Analytic bilinear inverse (Gram lift)

The full FO map is bilinear, not the CTF slice. On a finite abelian frequency
group $`G`$,

```math
\hat I(\xi)=\sum_{q\in G}\Psi(q)\,R(q,q-\xi)\,\overline{\Psi(q-\xi)}
=\sum_{q\in G}R(q,q-\xi)\,X(q,q-\xi),
```

where $`X(q,q')=\Psi(q)\overline{\Psi(q')}`$ is rank-1. Each through-focal
slice is a **linear** map in the lag diagonal $`q\mapsto X(q,q-\xi)`$. The
object is recovered from a Gram by the vacuum-gauge factor
$`\Psi(q)=X(q,0)/\sqrt{\lVert X(0,0)\rVert}`$ when $`\Psi(0)`$ is real and
nonnegative.

### T10. Vacuum-gauge factor

**Statement.** If $`\Psi(0)\neq 0`$ has vanishing imaginary part and nonnegative
real part, then `vacuumGaugePsi (gram Ψ) = Ψ`. Global phase is quotiented:
`gram (e^{iθ} Ψ) = gram Ψ` and `ihat` is gauge-invariant (`ihat_gauge`,
`gram_eq_of_phase`).

**Lean.** `vacuumGaugePsi`, `vacuumGaugePsi_recovers`, `analyticPsi_recovers`,
`analyticPsi_unique`, `analyticPsi_unique_of_dc_column`.

### T11. DC-column split

**Statement.** For $`\xi\neq 0`$,

```math
\hat I(\xi)=R(\xi,0)X(\xi,0)+R(0,-\xi)X(0,-\xi)
+\sum_{q\notin\{0,\xi\}}R(q,q-\xi)X(q,q-\xi).
```

Subtracting a known remainder reduces bilinear FO to the vacuum $`2\times 2`$.
If `gramDet 0 h g ≠ 0` with $`h_k=R_k(\xi,0)`$, $`g_k=R_k(0,-\xi)`$, Cramer's
rule at $`\alpha=0`$ recovers $`(X(\xi,0),X(0,-\xi))`$ exactly.

**Lean.** `ihat_dc_split`, `ihat_sub_remainder`, `twoColumn_recovers`,
`analyticPair_of_remainder`, `dcPair_unique_of_remainder`,
`twoColumn_injective`.

### T12. One, two, and three modes

**Statement.** Support at $`\{0\}`$: intensity only at DC. Support at
$`\{0,\xi\}`$ with $`2\xi\neq 0`$: the conjugate branch drops and
$`\hat I(\xi)=R(\xi,0)X(\xi,0)`$ (scalar Tikhonov at $`\alpha=0`$ inverts it).
Support at $`\{-\xi,0,\xi\}`$ with $`2\xi\neq 0`$ and $`3\xi\neq 0`$: the
remainder vanishes, so the vacuum $`2\times 2`$ is exact. A non-collinear
3-wave object $`\{0,u,v\}`$ (with $`2u\neq 0`$, $`2u\neq v`$, $`v\neq -u`$)
likewise has vanishing remainder and conjugate branch at frequency $`u`$,
so $`\hat I(u)=R(u,0)X(u,0)`$; the same holds at $`v`$ under the swapped
hypotheses. The two-mode amplitude quadratic $`s(T-s)=\lvert Z\rvert^2`$ has roots
`twoModePlus`/`twoModeMinus`; the larger (specular) root is `twoModePlus`.

**Lean.** `ihat_of_dc_support`, `bilinearRemainder_twoMode`, `ihat_twoMode`,
`analyticPair_twoMode`, `bilinearRemainder_threeMode`, `ihat_threeMode_axis`,
`analyticPair_threeMode`, `bilinearRemainder_twoAxis`, `ihat_twoAxis`,
`ihat_twoAxis_v`, `ihat_twoAxis_dc`, `analyticPair_twoAxis`,
`analyticPair_twoAxis_v`, `twoAxis_dcCol_unique`, `twoAxis_dcCol_unique_v`,
`twoMode_roots_pair`, `twoMode_specular`.

### T13. Hermitian intensity and rank-1 pupil

**Statement.** If $`\overline{R(q,q')}=R(q',q)`$ then
$`\overline{\hat I(\xi)}=\hat I(-\xi)`$. If $`R(q,q')=P(q)\overline{P(q')}`$
(perfect coherence), then $`\hat I`$ is the Gram autocorrelation of $`\Psi P`$.
A unimodular diagonal kernel has a rank-1 DC slice (not injective).

**Lean.** `ihat_hermitian`, `ihat_of_rank1`, `dcSlice_not_injective`. Off-DC
slice injectivity recovers those lag diagonals
(`offDiagGram_eq_of_sliceInjective`, `lifted_unique_of_sliceInjective`,
`gram_eq_of_lags`). It does **not** invert the DC slice.

### T14. 2D kernel and pure-defocus degeneracy

**Statement.** The working 2D kernel `R_FO2` uses the disk aperture, radial
$`\chi_{S2}`$, and vector tilt $`\mathbf{a}=\nabla\chi_S(\mathbf{q})-\nabla\chi_S(\mathbf{q}')`$,
so $`E_S`$ sees $`\mathbf{q}\cdot\mathbf{q}'`$. On the CTF slice
$`R_{\mathrm{FO2}}(\mathbf{q},0)=R_{\mathrm{FO}}(\lVert\mathbf{q}\rVert,0)`$;
off axis it is **not** $`R_{\mathrm{FO}}(\lVert\mathbf{q}\rVert,\lVert\mathbf{q}'\rVert)`$.
Pure defocus plus perfect coherence is a cisoid of frequency
$`\omega=\pi\lambda(\lVert\mathbf{q}\rVert^2-\lVert\mathbf{q}'\rVert^2)`$,
which depends on $`\mathbf{q}`$ only through $`\mathbf{q}\cdot\boldsymbol{\xi}`$.
Householder reflection across $`\boldsymbol{\xi}`$ preserves $`\omega`$ and
$`\lVert\mathbf{a}\rVert`$. Frequencies with the same projection onto
$`\boldsymbol{\xi}`$ (and matching aperture) are indistinguishable.

Sampling `R_FO2` on a finite group via $`\iota:G\to\mathbb{R}^2`$ yields
`sampledR`; bilinear FO on that group is `ihat (sampledR ι Δz)`.

**Lean.** `R_FO2`, `R_FO2_eq_R_FO_axis`, `R_FO2_pureDefocus_perfect`,
`defocusOmega_eq_inner`, `defocusOmega_depends_inner`,
`R_FO2_pureDefocus_perp`, `reflectLine_*`, `sampledR`,
`ihat_sampledR_perfect`.

**Tightness.** This is a closed-form inverse of bilinear FO **under**
remainder knowledge, small-mode support, or injective off-DC slices plus a
full Gram/vacuum gauge. It is **not** an inverse of unrestricted 2D Yu
`R_FO2` on a general lattice: pure defocus is degenerate in the
perpendicular directions, and the DC slice has rank one.

### T15. Vandermonde fiber masses

**Statement.** Under perfect coherence and pure defocus ($`C_3=C_5=0`$),
sampled bilinear FO at lag $`\xi`$ is a mixture of cisoids whose frequencies
are $`\omega(q,q-\xi)=\pi\lambda(\lVert\mathbf{q}\rVert^2-\lVert\mathbf{q}-\boldsymbol{\xi}\rVert^2)`$.
Grouping $`q`$ by a fiber index, $`n`$ equally spaced defoci
$`\Delta z_k=\delta k`$ yield the Vandermonde system

```math
\hat I(\xi,\delta k)=\sum_{j} M_j\,z_j^k,\qquad
z_j=\mathrm{e}^{\mathrm{i}\omega_j\delta},
```

for the fiber masses $`M_j`$. Distinct nodes ($`z_j`$ injective) recover
$`M`$ uniquely by right-multiplication with the inverse Vandermonde. If
each fiber carries at most one occupied pair (transversal support) and
those frequencies lie inside the aperture, then $`M_{\mathrm{idx}(q)}=X(q,q-\xi)`$.
In particular the vacuum-column entry $`X(\xi,0)`$ is the mass of the
fiber containing $`(\xi,0)`$ (`recoveredMasses_eq_gram_vacuum`). Collecting
every DC-column entry together with $`X(0,0)`$ determines a vacuum-gauged
$`\Psi`$ (`analyticPsi_unique_of_dc_column`); $`X(0,0)`$ itself is not an
off-DC fiber mass.

Householder partners across $`\boldsymbol{\xi}`$ share a cisoid node
(`defocusOmega_reflect`), so they remain a single mass: the inverse
recovers fibers, not individual lattice points on an iso-$`\omega`$ line.

**Lean.** `cisoidMass`, `cisoidNode`, `recoveredMasses`,
`cisoidMasses_unique`, `recoveredMasses_eq`, `ihat_eq_cisoidMass`,
`ihat_eq_vandermondeRow`, `cisoidMass_unique_of_ihat`,
`recoveredMasses_eq_cisoidMass`, `transversalSupport`,
`cisoidMass_eq_gram_of_transversal`,
`recoveredMasses_eq_gram_of_transversal`,
`recoveredMasses_eq_gram_vacuum`, `gram_eq_of_transversal_ihat`.

**Tightness.** This is the analytic 2D inverse on **transversal** support
with distinct cisoid nodes. It is **not** an inverse of unrestricted Yu
$`R_{\mathrm{FO2}}`$ on a general 2D lattice.

---

## Optional Gauss–Newton step

From vacuum, one GN step **equals** T1 / the $`2\times 2`$ solve (T6, T9:
`vacuumGN_eq_stage1Pair`). From a general $`x_0`$, one GN
step is Tikhonov for the Jacobian `ihatJac R x0`; the ignored term is
exactly `ihat R δ`. That Jacobian is Fourier-diagonal iff $`x_0`$ is
supported at DC (vacuum). Encode the expansion (`ihat_add`); do not
encode local quadratic convergence of GN (needs a Lipschitz Hessian
estimate in a Banach space of images).

---

## Explicitly informal (do not encode)

| Item | Why |
|---|---|
| FFT algorithm exists / runs in $`O(N \log N)`$ wall-clock | complexity model only (`dftCost` is a definition) |
| Array DFT = continuum FT of the paper | sampling theory |
| Gaussian / Poisson noise, MSE, Cramér–Rao | no probability space |
| Frozen-aperture and first-order tilt truncations | already flagged `Approx.` in the forward model |
| “Fastest among all conceivable inverses” | only DFT-based / dense-bilinear comparisons are proved |
| Global convergence of nonlinear GN / GS | not an identity |

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
| T10 | `gram`, `vacuumGaugePsi_recovers`, `analyticPsi_recovers`, `analyticPsi_unique`, `analyticPsi_unique_of_dc_column`, `gram_eq_of_phase` |
| T11 | `ihat_eq_gram`, `ihat_dc_split`, `twoColumn_recovers`, `analyticPair_of_remainder`, `dcPair_unique_of_remainder` |
| T12 | `ihat_twoMode`, `analyticPair_twoMode`, `ihat_threeMode_axis`, `analyticPair_threeMode`, `ihat_twoAxis`, `ihat_twoAxis_v`, `ihat_twoAxis_dc`, `analyticPair_twoAxis`, `analyticPair_twoAxis_v`, `twoAxis_dcCol_unique`, `twoAxis_dcCol_unique_v`, `twoMode_specular` |
| T13 | `ihat_hermitian`, `ihat_of_rank1`, `dcSlice_not_injective`, `offDiagGram_eq_of_sliceInjective` |
| T14 | `R_FO2`, `R_FO2_pureDefocus_perp`, `reflectLine`, `sampledR`, `ihat_sampledR_perfect` |
| T15 | `cisoidMass`, `recoveredMasses`, `cisoidMasses_unique`, `recoveredMasses_eq_gram_of_transversal`, `recoveredMasses_eq_gram_vacuum`, `gram_eq_of_transversal_ihat` |
