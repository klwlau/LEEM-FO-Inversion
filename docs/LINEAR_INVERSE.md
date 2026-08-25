# Linearized multi-defocus FO/CTF inverse: theorem list

This is stage 2 of the project: after the Yu 2019 FO kernel is encoded,
the discrete inverse is stated against that kernel.
The inverse note is [proofs/leemfo_inverse.pdf](proofs/leemfo_inverse.pdf).

This is the Lean-ready statement list for the **Fourier-diagonal Tikhonov
estimator** of the linearized FO/CTF slice (optionally one Gauss–Newton
step). Encoding: `LeemFO/Tikhonov.lean`, `LeemFO/LinearInverse.lean`.

The object is finite-dimensional throughout. After a formal discrete Fourier
transform, each spatial-frequency bin is a map `κ → ℂ` of defocus
measurements (`κ` is `Fin K` in applications). No analysis of FFT
correctness is used.

---

## Standing discrete model

Let `κ` be a finite index of defoci and `G` a finite abelian group of
sampled frequencies (in Lean: any `AddGroup` with `Fintype`).

| Symbol | Meaning |
|---|---|
| `h : κ → ℂ` | CTF-slice multipliers `h_k = R_FO(q, 0, Δz_k)` |
| `g : κ → ℂ` | conjugate-branch multipliers `g_k = R_FO(0, -q, Δz_k)` |
| `y : κ → ℂ` | measured Fourier coefficients of intensity (one bin) |
| `x : ℂ` | unknown complex amplitude of that bin (weak-object / one branch) |
| `(u, v) : ℂ × ℂ` | pair `(X(q), X(-q))` in the vacuum 2×2 Jacobian |
| `α > 0` | Tikhonov parameter |
| `n : κ → ℂ` | additive discrepancy `y = h • x⋆ + n` (deterministic; not a probability space) |

The working kernel is the already-encoded `R_FO` (CTF-slice identity
`R_FO_eq_R_CTF_axis`).

---

## Lean theorems (encode these)

### T1. Unique minimizer (`α > 0`)

**Statement.** For `α > 0` the energy
$$
J(x)=\sum_{k\in\kappa}\|h_k x-y_k\|^2+\alpha\|x\|^2
$$
has a unique global minimizer
$$
\hat x=\frac{\sum_k \overline{h_k}\,y_k}{\alpha+\sum_k|h_k|^2}.
$$
**Lean.** `tikhonovJ_min`, `tikhonov_unique`, closed form `tikhonovXhat`.
Proof: completing the square (`tikhonovJ_eq_completed` / `tikhonovJ_eq_shift`). The same identity
gives uniqueness at `α = 0` whenever `∑ |h_k|² > 0`
(`tikhonovDenom_pos_of_energy`).

**Tightness.** The Hessian is the positive real `2(α+∑|h|²)`; no smaller
regularization yields a uniform unique-minimizer theorem for arbitrary `h`.

### T2. Bias–noise identity

**Statement.** If $y_k = h_k x^\star + n_k$ and $D := \alpha+\sum|h_k|^2 \neq 0$, then
$$
\hat x-x^\star
=\frac{\sum_k \overline{h_k}\,n_k-\alpha x^\star}{D}.
$$
**Lean.** `tikhonov_error`.

This is an algebraic identity. It is **not** a statistical noise theorem:
`n` is an arbitrary discrepancy (linearization remainder + instrument noise
+ discretization). Taking `𝔼[n]=0` and `𝔼[|n_k|²]=σ²` is informal (needs a
probability space, not used here).

### T3. Triangle bound

**Statement.** If `α ≥ 0` and `D > 0`, then
$$
|\hat x-x^\star|
\le
\frac{\sum_k |h_k|\,|n_k|+\alpha\,|x^\star|}{D}.
$$
**Lean.** `tikhonov_error_bound`.

**Tightness.** Equality is attained (`tikhonov_error_bound_sharp`): one
measurement, $h=1$, $n=1$, $x^\star=-1$, $\alpha=1$ gives both sides $1$.
The constant `1` cannot be improved uniformly.

### T4. Aperture: modes with $|q|>q_{\mathrm{ap}}$ are invisible

**Statement.** If $|q|>q_{\mathrm{ap}}$ then $R_{\mathrm{FO}}(q,0,\Delta z)=0$ for every
defocus. Consequently the Tikhonov estimator of that bin is identically `0`
(for `α ≠ 0`), independently of the data.

If $0 \le q_{\mathrm{ap}}$, then $R_{\mathrm{FO}}(q,0,\Delta z)=0$ **iff** $|q|>q_{\mathrm{ap}}$
(waves and envelopes never vanish).

**Lean.** `R_FO_axis_eq_zero_of_outside`, `R_FO_axis_ne_zero_of_inside`,
`R_FO_axis_eq_zero_iff`, `tikhonovXhat_outside_aperture`.

This is the sharp support statement: the linearized slice cannot recover
aperture-blocked modes. It is **not** the same as a CTF *zero of
`sin(2πχ_S)`* inside the disk (T8).

### T5. Gauge: $I(e^{i\theta}\psi)=I(\psi)$

**Statement (spectrum).** For any bilinear kernel `R` and any real `θ`,
$$
\hat I\bigl(e^{iθ}Ψ\bigr)=\hat I(Ψ).
$$
**Statement (real space).** `objectWave σ (φ+θ) = e^{iθ} objectWave σ φ`.

**Lean.** `ihat_gauge`, `cexp_I_mul_conj`, `objectWave_phase_shift`.

The linearized inverse around a **fixed** vacuum therefore selects a gauge
(the vacuum phase). A second Gauss–Newton step about a non-vacuum
background does **not** restore global-phase invariance of the unknown.

### T6. Quadratic remainder of bilinear FO vs vacuum linearization

**Statement.** With vacuum spectrum `vacuum = 1_{q=0}` and increment `δ`,
$$
\hat I(\mathrm{vac}+δ)
=
\hat I(\mathrm{vac})
+ DI_{\mathrm{vac}}[δ]
+ \hat I(δ),
$$
where
$$
DI_{\mathrm{vac}}[δ](ξ)
= R(ξ,0)\,δ(ξ)+R(0,-ξ)\,\overline{δ(-ξ)}.
$$
The dropped term is exactly bilinear in `δ`. In particular
$$
\bigl|\hat I(δ)(ξ)\bigr|
\le
\Bigl(\sum_{q,q'}|R(q,q')|\Bigr)\Bigl(\sum_q|δ(q)|\Bigr)^2.
$$
**Lean.** `ihat_add`, `ihatJac_vacuum`, `ihat_quadratic_remainder`,
`ihat_bound`.

**Tightness.** The remainder is homogeneous of degree 2 (not `o(‖δ‖²)` in
general). The displayed constant is the elementary `ℓ¹` bound; the sharp
constant is the operator norm of `R` on `ℓ²`, equivalently the Frobenius
bound `‖R‖_F ‖δ‖_2²`. One Gauss–Newton step from vacuum **is**
Fourier-diagonal Tikhonov on $DI_{\mathrm{vac}}$. A further GN step at a
generic `x_0` uses `ihatJac R x0`, which is **not** Fourier-diagonal.

### T7. Cost model: `O(K N log N)`

**Statement (definition, not an FFT existence theorem).** Set
`dftCost N := N log₂ N` (modelled Cooley–Tukey cost) and
`binSolveCost K := 8K+4` (Gram/right-hand side for a scalar or 2×2 solve).
Then
$$
\texttt{reconstructCost}(K,N)=(K+1)\,N\log_2 N+N(8K+4).
$$
For `K≥1`, `N≥2`,
$$
\texttt{reconstructCost}(K,N)\le 14\,K\,N\log_2 N.
$$
At `N=128` this is already strictly cheaper than a dense bilinear apply
`K N²`, for every `K≥1`.

**Lean.** `dftCost`, `reconstructCost`, `reconstructCost_le`,
`reconstructCost_lt_dense_128`, `exists_grid_diagonal_cheaper`.

**Informal.** Existence of an FFT achieving `O(N log N)` is **not** proved.
Neither is cache/architecture cost, nor that a DFT of the physical
continuous Fourier transform equals the array DFT.

### T8. Why this is asymptotically the cheapest CTF-zero-filling method
(`K ≥ 2`)

Two independent Lean facts, then an informal comparison.

**T8a. Complex object, vacuum Jacobian (any optics).** One complex
measurement of two complex unknowns `(X(q), X(-q))` always has a kernel.

**Lean.** `one_measurement_not_injective`. Hence `K = 1` cannot identify a
general complex object even when `R_FO(q,0,Δz) ≠ 0`. Need `K ≥ 2` and
linearly independent columns `(h,g)` for that bin.

**T8b. Weak-phase CTF zeros.** `sin(2π χ_S(q,Δz))=0` whenever `2χ_S ∈ ℤ`.
For a pure-defocus NAC column (`C_3=C_5=0`, `Δz ≠ 0`) a large enough
aperture contains a nonzero such `q`.

**Lean.** `weakPhase_sin_eq_zero`, `exists_interior_weakPhase_zero`.
Filling those zeros is exactly “`∑_k sin²(2π χ_S(q,Δz_k)) > 0` on the
punctured aperture”, which a single defocus generically fails and two
defoci with incommensurate `Δz` typically achieve. (Common zeros can
remain if `Δz_2/Δz_1 ∈ ℚ`; `K≥2` is necessary but not automatically
sufficient.)

**T8c. Cost among methods that fill zeros.** After `K` modelled DFTs, any
algorithm that uses all `KN` Fourier samples costs `Ω(KN)` arithmetic
(input-size lower bound). The diagonal Tikhonov solve is `Θ(KN)` plus the
modelled DFTs, matching T7. A dense bilinear apply is `Θ(KN²)`
(`denseApplyCost`), strictly larger at `N=128` (T7).

**Informal (do not encode as a theorem).**
- Iterative bilinear / Gerchberg–Saxton / MAL: `T` applications with `T≥2`
  cost at least twice the DFT leading term.
- Full FO Gauss–Newton about a generic background is not Fourier-diagonal
  (T6), so it is not `O(KN log N)` without a further Jacobian
  approximation.
- Statistical MSE rates, continuous Shannon sampling, and “fastest among
  *all* algorithms including unspecified real-space tricks” are outside
  the Lean fragment.

---

## Optional Gauss–Newton step

From vacuum, one GN step **equals** T1 (T6). From a general `x_0`, one GN
step is Tikhonov for the Jacobian `ihatJac R x0`; the ignored term is
exactly `ihat R δ`. That Jacobian is Fourier-diagonal iff `x_0` is
supported at DC (vacuum). Encode the expansion (`ihat_add`); do not
encode local quadratic convergence of GN (needs a Lipschitz Hessian
estimate in a Banach space of images).

---

## Explicitly informal (do not encode)

| Item | Why |
|---|---|
| FFT algorithm exists / runs in `O(N log N)` wall-clock | complexity model only (`dftCost` is a definition) |
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
| 2×2 Gram | `tikhonovJ2`, `gramDet`, `gramDet_pos` (invertible for `α>0`; uniqueness of the 2×2 minimizer is the same square-completion argument as T1) |
