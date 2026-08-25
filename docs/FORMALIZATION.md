# Formalization source: Yu, Lau, Altman, Ultramicroscopy 200 (2019) 160–168

Typeset proofs of the identities below:
[proofs/leemfo_proofs.pdf](proofs/leemfo_proofs.pdf)
([TeX source](proofs/leemfo_proofs.tex)).

Source of truth for a Lean formalization of Fourier-optics (FO) image formation in aberration-corrected LEEM. Reconstructed from §2.2 and Appendix A1–A2 of Yu *et al.* (2019). The PDF’s two-column OCR is unreliable; every displayed formula below is restored from (i) surrounding prose, (ii) the appendix integrals, and (iii) the same group’s FO/CTF formulae (Pang *et al.* 2009; Schramm *et al.*, Ultramicroscopy 115 (2012) 88; Yu *et al.*, Ultramicroscopy 183 (2017) 109; Tromp & Schramm, Ultramicroscopy 2012, χ-convention).

**How to read this document**

- **Def.** = modelling choice or notation, not a theorem.
- **Thm.** = identity that follows from a named analysis theorem (Gaussian Fourier transform, polar form of a complex number, Jacobi–Anger, FWHM of a Gaussian).
- **Approx.** = truncation or modelling hypothesis used in the paper, not an identity.
- Vectors are bold (`\mathbf{q}`); scalars (including 1D signed spatial frequency) are italic (`q`). Magnitudes: \(q=|\mathbf{q}|\).
- The paper’s Fourier kernel is always the **unitary \(2\pi\)-in-the-exponent, ordinary Lebesgue-measure** convention
  \[
  \mathrm{e}^{2\pi\mathrm{i}\,\mathbf{q}\cdot\mathbf{r}},\qquad
  \mathrm{d}^2q=\mathrm{d}q_x\,\mathrm{d}q_y.
  \]
  The wave-aberration factor is \(W=\mathrm{e}^{2\pi\mathrm{i}\chi}\) with **\(\chi\) in waves** (optical path in units of \(\lambda\)). That is the only \(2\pi\) convention used here. Do **not** mix in a radian-valued \(\chi_{\mathrm{rad}}=2\pi\chi\) unless it is written explicitly.

---

## 0. Notation, types, and the \(\lambda\) restoration

### 0.1 Physical quantities

| Symbol | Type | Meaning |
|---|---|---|
| \(\mathbf{r}\) | \(\mathbb{R}^2\) | lateral position in an \(M=1\) image plane |
| \(\psi_0(\mathbf{r})\) | \(\mathbb{C}\) | object (exit) wave |
| \(\sigma(\mathbf{r}),\ \phi(\mathbf{r})\) | \(\mathbb{R}\) | amplitude and phase of \(\psi_0\) |
| \(\alpha\) | rad | emission angle from the virtual object |
| \(\lambda\) | length | electron wavelength **after acceleration** (column energy \(E\)) |
| \(\lambda_0\) | length | wavelength at the sample (\(E_0\)) |
| \(\mathbf{q}\) | \(\mathbb{R}^2\), length\(^{-1}\) | spatial frequency |
| \(\boldsymbol{\Psi}(\mathbf{q})\) | \(\mathbb{C}\) | Fourier transform of \(\psi_0\) |
| \(\Delta z\) (also \(C_1\)) | length | defocus, referenced to the \(M=1\) image plane |
| \(\varepsilon\) | energy | deviation from nominal column energy \(E\) |
| \(\mathbf{k}\) | \(\mathbb{R}^2\), length\(^{-1}\) | spatial-frequency shift from source tilt \(\kappa/\lambda\) |
| \(C_3,C_5\) | length | spherical aberration coefficients (3rd, 5th order) |
| \(C_C,C_{CC},C_{3C}\) | length | chromatic coefficients (2nd / 3rd / 4th rank) |
| \(q_{\mathrm{ap}}=\alpha_{\mathrm{ap}}/\lambda\) | length\(^{-1}\) | aperture cut-off |
| \(q_{\mathrm{ill}}=\alpha_{\mathrm{ill}}/\lambda\) | length\(^{-1}\) | FWHM of the source density \(s(\mathbf{k})\) |
| \(\Delta E\) | energy | FWHM of \(c(\varepsilon)\) |

Table 1 of the paper (IBM LEEM, \(E_0=10\,\mathrm{eV}\), \(E=15.010\,\mathrm{kV}\), \(\Delta E=0.25\,\mathrm{eV}\), \(\alpha_{\mathrm{ill}}=0.1\,\mathrm{mrad}\)) reports \(C_x\) **in metres** and \(q_{\mathrm{ap}}\) **in \(\mathrm{nm}^{-1}\)**. Those units are consistent only if the powers of \(\lambda\) in §0.2 are present.

### 0.2 Spatial-frequency vs angular form of \(\chi\) (equivalent)

The paper **defines** \(\mathbf{q}=\boldsymbol{\alpha}/\lambda\) (vector of direction cosines over wavelength) and then typesets \(\chi_S=\tfrac14 C_3 q^4+\cdots\) in the Rose/Schmidt angular style, omitting \(\lambda\). That typesetting is dimensionally incomplete if \(q\) is the spatial frequency of the sentence immediately above it.

Two equivalent, dimensionally consistent writings:

**Spatial-frequency form (canonical for Lean; Tromp–Schramm 2012, Schramm 2012):**
\(\chi\) is in **waves**, \(W=\mathrm{e}^{2\pi\mathrm{i}\chi}\),
\[
\chi_S(\mathbf{q},\Delta z)
=\frac14 C_3\lambda^3 q^4+\frac16 C_5\lambda^5 q^6+\frac12\Delta z\,\lambda\, q^2.
\]

**Angular / path-length form (Rose 1992, Schmidt 2002, citations [9,10] of the paper):**
\(\chi_{\mathrm{path}}\) is an optical path (length), \(\alpha=q\lambda\),
\[
\chi_{\mathrm{path}}(\alpha,\Delta z)
=\frac14 C_3\alpha^4+\frac16 C_5\alpha^6+\frac12\Delta z\,\alpha^2,
\qquad
\chi=\chi_{\mathrm{path}}/\lambda,
\qquad
W=\mathrm{e}^{2\pi\mathrm{i}\chi_{\mathrm{path}}/\lambda}.
\]

These are identical after \(\alpha=\lambda q\). **Lean should use the spatial-frequency form**, with \(\lambda\) explicit, \(q=|\mathbf{q}|\), and \(W:=\exp(2\pi\mathrm{i}\chi)\) as a definition.

### 0.3 One-dimensional reduction

For a 1D object \(\psi_0(x)\) the paper replaces 2D vectors by **signed scalars** \(q,q',k\in\mathbb{R}\). Then \(\mathbf{q}\cdot\mathbf{q}'\mapsto qq'\) (product of signed reals, not \(|q||q'|\)). Odd powers \(q^3,q^5\) keep the sign. The 2D theory is **not** the 1D theory with \(q_y\equiv 0\) unless the source integral is also reduced to 1D; the paper’s 1D envelopes use a 1D source density along the object axis. Both 1D and 2D Gaussian Fourier transforms produce the **same** exponent \(-2\pi^2\sigma^2|a|^2\) (see A1).

---

## 1. Object wave \(\psi_0(\mathbf{r})\)

**Paper eq.:** unnumbered, §2.2 opening sentence.

**Def.**
\[
\psi_0(\mathbf{r})=\sigma(\mathbf{r})\,\mathrm{e}^{\mathrm{i}\phi(\mathbf{r})}.
\]

- \(\mathbf{r}\): lateral position.
- \(\sigma\): amplitude of the emitted wave (LEEM reflectivity / structure-factor contrast).
- \(\phi\): phase of the emitted wave (topographic / inner-potential contrast).

No \(2\pi\) in the object-wave phase: \(\phi\) is in **radians**. This \(\mathrm{e}^{\mathrm{i}\phi}\) is independent of the \(\mathrm{e}^{2\pi\mathrm{i}\chi}\) convention used later for lens aberrations.

**Related object models used in §3.2 (not numbered in §2.2):**

- Atomic step, height \(a_0\):
  \[
  \Delta\phi=\frac{4\pi a_0}{\lambda_0},\qquad
  \lambda_0\sim\frac{h}{\sqrt{2m E_0}}.
  \]
  **Def.** of the kinematic LEEM phase shift on reflection (path \(2a_0\)).
- Sinusoidal ripple of physical amplitude \(A\) and wavelength \(\Lambda\):
  \[
  \psi_0(x)\propto\exp\bigl(\mathrm{i}\,\varphi\sin(kx)\bigr),
  \qquad
  \varphi=\frac{4\pi A}{\lambda_0},\qquad
  k=\frac{2\pi}{\Lambda}.
  \]
  Here \(k\) is a **real-space wave number**, not the source-tilt variable of §7. See §17 for Jacobi–Anger.

---

## 2. Spatial frequency \(\mathbf{q}=\boldsymbol{\alpha}/\lambda\)

**Paper eq.:** unnumbered, §2.2.

**Def.**
\[
\mathbf{q}=\frac{\boldsymbol{\alpha}}{\lambda},
\qquad
q=|\mathbf{q}|.
\]

- \(\boldsymbol{\alpha}\): emission-angle vector from the virtual object (paraxial; \(|\boldsymbol{\alpha}|\ll 1\)).
- \(\lambda\): wavelength **after acceleration**, not \(\lambda_0\).

The object-wave Fourier transform (same \(2\pi\) convention as the image synthesis) is the **Def.**
\[
\boldsymbol{\Psi}(\mathbf{q})
=\int_{\mathbb{R}^2}\psi_0(\mathbf{r})\,\mathrm{e}^{-2\pi\mathrm{i}\,\mathbf{q}\cdot\mathbf{r}}\,\mathrm{d}^2r.
\]
(The overall sign in the object FT is a Fourier-pair convention; it must be opposite to the image inverse FT of §8. The paper writes the image kernel as \(\mathrm{e}^{2\pi\mathrm{i}(\mathbf{q}-\mathbf{q}')\cdot\mathbf{r}}\), which **fixes** the inverse-FT sign.)

Instrumental modifications are applied in Fourier space. A single multiplicative \(H(\mathbf{q})\) (CTF style) is **not** how FO computes intensity under partial coherence; FO uses the bilinear kernel \(R(\mathbf{q},\mathbf{q}',\Delta z)\) of §8–§9. The paper’s informal
\[
\widetilde{\boldsymbol{\Psi}}(\mathbf{q})=\boldsymbol{\Psi}(\mathbf{q})\,H(\mathbf{q})
\]
is the CTF picture, recovered from FO when envelopes factor (perfect coherence, or the weak-phase / \(q'=0\) slice).

---

## 3. Aperture \(M(\mathbf{q})\)

**Paper eq.:** unnumbered, §2.2.

**Def.** For a circular contrast aperture of angular radius \(\alpha_{\mathrm{ap}}\),
\[
M(\mathbf{q})
=
\begin{cases}
1 & \text{if }|\mathbf{q}|\le q_{\mathrm{ap}},\\
0 & \text{if }|\mathbf{q}|> q_{\mathrm{ap}},
\end{cases}
\qquad
q_{\mathrm{ap}}=\frac{\alpha_{\mathrm{ap}}}{\lambda}.
\]
\(M\) is real, so \(M^*(\mathbf{q}')=M(\mathbf{q}')\).

**Approx.** (used from Eq. (4) onward). For a circularly symmetric aperture and small source,
\[
M(\mathbf{q}+\mathbf{k})\approx M(\mathbf{q}),
\]
i.e. the aperture is evaluated at the untilted spatial frequency, not at the true tilted ray \(\mathbf{q}+\mathbf{k}\).

---

## 4. Wave aberration \(\chi_S(\mathbf{q},\Delta z)\) and \(W_S=\mathrm{e}^{2\pi\mathrm{i}\chi_S}\)

**Paper eq.:** unnumbered, §2.2. Citations [9,10] (Rose; Schmidt).

### 4.1 Definition of \(W_S\)

**Def.**
\[
W_S(\mathbf{q},\Delta z)
:=\exp\bigl(2\pi\mathrm{i}\,\chi_S(\mathbf{q},\Delta z)\bigr).
\]

\(\chi_S\) is the **q-dependent optical path-length difference, in waves**, of the actual wavefront relative to the ideal reference sphere. The factor \(2\pi\) converts waves to radians. This is a definition of the transfer factor, not a theorem about a particular \(\mathrm{e}^{\pm\mathrm{i}\omega t}\) time convention.

### 4.2 Spherical aberration and defocus

**Def.** (spatial-frequency form; rotationally symmetric)
\[
\chi_S(\mathbf{q},\Delta z)
=\frac14 C_3\lambda^3\,|\mathbf{q}|^4
+\frac16 C_5\lambda^5\,|\mathbf{q}|^6
+\frac12\Delta z\,\lambda\,|\mathbf{q}|^2.
\]

- **nac LEEM:** \(C_3\) dominates; \(C_5\) is dropped.
- **ac LEEM:** \(C_3=0\); \(C_5\) is kept.

**1D signed-scalar form:** replace \(|\mathbf{q}|^{2n}\) by \(q^{2n}\) (even).

### 4.3 Defocus sign (path-length convention)

The paper: spherical aberration and defocus \(\Delta z\) “cause deviations of the wave path for off-axis waves (\(q>0\)) from the ideal reference wave. This introduces a \(q\)-dependent **optical path length difference**” written as \(\chi_S\), with a **positive** \(\tfrac12\Delta z\,q^2\) (angular) / \(\tfrac12\Delta z\,\lambda\,q^2\) (spatial-frequency) term.

**Def. of the sign of \(\Delta z\) in this paper (and in Tromp–Schramm):**

- \(\Delta z>0\) adds **positive** optical path for off-axis rays, i.e. positive \(C_1\) in the Rose expansion \(\chi_{\mathrm{path}}=\tfrac12 C_1\alpha^2+\cdots\).
- Combined with \(W_S=\mathrm{e}^{+2\pi\mathrm{i}\chi_S}\), the defocus phase in radians is
  \[
  2\pi\chi_S\big|_{\text{defocus}}
  =\pi\,\Delta z\,\lambda\,q^2
  =\pi\,\Delta z\,\alpha^2/\lambda.
  \]
- This is the **same** sign as Schramm *et al.* 2012 and Tromp & Schramm 2012:
  \(\chi=\tfrac12 C_1\lambda q^2+\cdots\), \(W=\mathrm{e}^{\mathrm{i}2\pi\chi}\).
- Scherzer compensation of **positive** \(C_3\) uses **negative** \(\Delta z\) (underfocus) in this convention, as in TEM.

Do not flip this sign in Lean. The path-length wording and the \(+\tfrac12\Delta z\) typesetting agree.

### 4.4 Gradient (needed for \(E_S\))

**Thm.** (chain rule on a radial function \(\chi_S=\chi_S(q)\), \(q=|\mathbf{q}|\))
\[
\nabla_{\mathbf{q}}\chi_S(\mathbf{q},\Delta z)
=\bigl(C_3\lambda^3\,q^2+C_5\lambda^5\,q^4+\Delta z\,\lambda\bigr)\,\mathbf{q}.
\]

**1D:**
\[
\partial_q\chi_S(q,\Delta z)
=C_3\lambda^3 q^3+C_5\lambda^5 q^5+\Delta z\,\lambda\, q.
\]

---

## 5. Chromatic aberration \(\chi_C(\mathbf{q},\varepsilon)\)

**Paper eq.:** unnumbered, §2.2. Analogous wave factor
\[
W_C(\mathbf{q},\varepsilon)
:=\exp\bigl(2\pi\mathrm{i}\,\chi_C(\mathbf{q},\varepsilon)\bigr)
\quad\text{(Def.)}.
\]

**Def.** (spatial-frequency form)
\[
\chi_C(\mathbf{q},\varepsilon)
=
\frac12 C_C\lambda\Bigl(\frac{\varepsilon}{E}\Bigr)q^2
+
\frac12 C_{CC}\lambda\Bigl(\frac{\varepsilon}{E}\Bigr)^2 q^2
+
\frac14 C_{3C}\lambda^3\Bigl(\frac{\varepsilon}{E}\Bigr)q^4.
\]

Ranks, as stated in the paper:

| Coefficient | Rank | (order in angle, degree in \(\varepsilon/E\)) | nac | ac |
|---|---|---|---|---|
| \(C_C\) | 2nd | (1st, 1st) | kept | \(=0\) |
| \(C_{CC}\) | 3rd | (1st, 2nd) | dropped | kept |
| \(C_{3C}\) | 4th | (3rd, 1st) | dropped | kept |

\(\varepsilon\): energy deviation from the nominal column energy \(E\). Lens-current / high-voltage instabilities are argued to be negligible versus \(\Delta E\) and are **dropped** (not an identity).

\(\chi_C\) is radial: it depends on \(q=|\mathbf{q}|\) only, not on \(\arg\mathbf{q}\). Consequently \(E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{q}')\) depends on \((|\mathbf{q}|,|\mathbf{q}'|)\) only. The **dot product** \(\mathbf{q}\cdot\mathbf{q}'\) appears only in \(E_S\).

---

## 6. Energy distribution \(c(\varepsilon)\) (Gaussian)

**Paper eq.:** unnumbered in §2.2; explicit in A1. Citation [17] (Hanßen & Trepte).

**Def.** (normalized 1D Gaussian)
\[
c(\varepsilon)
=\frac{1}{\sigma_E\sqrt{2\pi}}
\exp\Bigl(-\frac{\varepsilon^2}{2\sigma_E^2}\Bigr),
\qquad
\int_{-\infty}^{\infty}c(\varepsilon)\,\mathrm{d}\varepsilon=1.
\]

**Thm.** (FWHM of a 1D Gaussian). If \(c(\pm\Delta E/2)=\tfrac12 c(0)\), then
\[
\Delta E=2\sqrt{2\ln 2}\;\sigma_E,
\qquad
\sigma_E^2=\frac{\Delta E^2}{8\ln 2}.
\]
The paper identifies this FWHM with the source energy spread \(\Delta E\).

Equivalent writing used in A2-style algebra:
\[
c(\varepsilon)=\sqrt{\frac{\gamma_E}{\pi}}\,\mathrm{e}^{-\gamma_E\varepsilon^2},
\qquad
\gamma_E=\frac{4\ln 2}{\Delta E^2}.
\]

---

## 7. Source density \(s(\mathbf{k})\) (2D Gaussian)

**Paper eq.:** unnumbered in §2.2; explicit in A1. Citations [18,19] (Frank; Wade & Frank).

Source point off-axis by tilt \(\boldsymbol{\kappa}\) shifts spatial frequency
\[
\mathbf{q}\mapsto\mathbf{q}+\mathbf{k},
\qquad
\mathbf{k}=\frac{\boldsymbol{\kappa}}{\lambda}
\quad\text{(Def.)}.
\]

**Def.** Circularly symmetric, normalized 2D Gaussian of isotropic variance \(\sigma_{\mathrm{ill}}^2\) on each Cartesian component:
\[
s(\mathbf{k})
=\frac{1}{2\pi\sigma_{\mathrm{ill}}^2}
\exp\Bigl(-\frac{|\mathbf{k}|^2}{2\sigma_{\mathrm{ill}}^2}\Bigr),
\qquad
\int_{\mathbb{R}^2}s(\mathbf{k})\,\mathrm{d}^2k=1.
\]

**Thm.** Product structure in rectangular coordinates:
\[
s(\mathbf{k})=s_{1\mathrm{D}}(k_x)\,s_{1\mathrm{D}}(k_y),
\qquad
s_{1\mathrm{D}}(k)=\frac{1}{\sigma_{\mathrm{ill}}\sqrt{2\pi}}
\exp\Bigl(-\frac{k^2}{2\sigma_{\mathrm{ill}}^2}\Bigr),
\]
because \(|\mathbf{k}|^2=k_x^2+k_y^2\).

**Thm.** (FWHM of a 1D slice / 1D marginal). The isotropic FWHM in spatial-frequency units is
\[
q_{\mathrm{ill}}
=2\sqrt{2\ln 2}\;\sigma_{\mathrm{ill}}
=\frac{\alpha_{\mathrm{ill}}}{\lambda},
\qquad
\sigma_{\mathrm{ill}}^2=\frac{q_{\mathrm{ill}}^2}{8\ln 2}.
\]
\(\alpha_{\mathrm{ill}}\): angular spread produced by source extension.

Equivalent writing:
\[
s(\mathbf{k})=\frac{\beta}{\pi}\,\mathrm{e}^{-\beta|\mathbf{k}|^2},
\qquad
\beta=\frac{4\ln 2}{q_{\mathrm{ill}}^2}.
\]

In 1D modelling, replace \(s(\mathbf{k})\,\mathrm{d}^2k\) by \(s_{1\mathrm{D}}(k)\,\mathrm{d}k\).

---

## 8. Image intensity \(I(\mathbf{r})\): double inverse Fourier transform

**Paper eq.:** unnumbered, §2.2, \(M=1\) image plane.

**Def.**
\[
I(\mathbf{r})
=\iint_{\mathbb{R}^2\times\mathbb{R}^2}
\boldsymbol{\Psi}(\mathbf{q})\,\boldsymbol{\Psi}^*(\mathbf{q}')
\,R(\mathbf{q},\mathbf{q}',\Delta z)
\,\exp\bigl(2\pi\mathrm{i}\,(\mathbf{q}-\mathbf{q}')\cdot\mathbf{r}\bigr)
\,\mathrm{d}^2q\,\mathrm{d}^2q'.
\]

This is \(\psi_i\psi_i^*\) with
\[
\psi_i(\mathbf{r})
=\int\widetilde{\boldsymbol{\Psi}}(\mathbf{q})\,
\mathrm{e}^{2\pi\mathrm{i}\,\mathbf{q}\cdot\mathbf{r}}\,\mathrm{d}^2q
\]
**before** ensemble-averaging over \((\mathbf{k},\varepsilon)\); after averaging, the bilinear kernel is \(R\), not a product \(H(\mathbf{q})H^*(\mathbf{q}')\).

**FO vs CTF (prose, not an equation number):**

- **CTF:** inverse FTs of \(\boldsymbol{\Psi}H\) and of \(\boldsymbol{\Psi}^*H^*\) are taken **separately**, then multiplied. Valid for perfect coherence, and for partial coherence in the weak-phase approximation. Separable envelopes \(E(\mathbf{q})E^*(\mathbf{q}')\).
- **FO:** the two inverse transforms are evaluated **together**. Mode mixing from partial coherence is kept. Valid beyond the weak-phase approximation. Envelopes are **inseparable** functions of \((\mathbf{q},\mathbf{q}')\).

---

## 9. Eqs. (1)–(2): \(R\) as an integral of \(R_0\)

### 9.1 Equation (1) — ensemble average

**Def.**
\[
R(\mathbf{q},\mathbf{q}',\Delta z)
=
\int_{\mathbb{R}^2}\mathrm{d}^2k\int_{-\infty}^{\infty}\mathrm{d}\varepsilon\;
s(\mathbf{k})\,c(\varepsilon)\,
R_0(\mathbf{q}+\mathbf{k},\,\mathbf{q}'+\mathbf{k},\,\Delta z,\,\varepsilon).
\]

The **same** tilt \(\mathbf{k}\) appears in both arguments (common illumination). Energy \(\varepsilon\) is likewise common.

### 9.2 Equation (2) — coherent kernel

**Def.**
\[
\begin{aligned}
R_0(\mathbf{q},\mathbf{q}',\Delta z,\varepsilon)
&=
M(\mathbf{q})\,M^*(\mathbf{q}')
\,W_S(\mathbf{q},\Delta z)\,W_S^*(\mathbf{q}',\Delta z)
\,W_C(\mathbf{q},\varepsilon)\,W_C^*(\mathbf{q}',\varepsilon).
\end{aligned}
\]

Because \(W=\mathrm{e}^{2\pi\mathrm{i}\chi}\) with real \(\chi\),
\[
W_S(\mathbf{q})W_S^*(\mathbf{q}')
=\exp\bigl(2\pi\mathrm{i}\bigl[\chi_S(\mathbf{q},\Delta z)-\chi_S(\mathbf{q}',\Delta z)\bigr]\bigr),
\]
and likewise for \(W_C\). This is an identity from \(W^{-1}=W^*\) on the unit circle, not a new physical assumption.

At \(\varepsilon=0\), \(\chi_C(\cdot,0)=0\), so \(W_C(\mathbf{q},0)=1\) and
\[
R_0(\mathbf{q},\mathbf{q}',\Delta z,0)
=M(\mathbf{q})M^*(\mathbf{q}')
W_S(\mathbf{q},\Delta z)W_S^*(\mathbf{q}',\Delta z).
\]

---

## 10. Taylor expansion, Eqs. (3)–(4)

### 10.1 Equation (3)

**Approx.** Expand the path functions in \(\mathbf{k}\) about \(\mathbf{k}=\mathbf{0}\) to **first order**, and **drop mixed \(\mathbf{k}\varepsilon\) terms**:
\[
\begin{aligned}
\chi_S(\mathbf{q}+\mathbf{k},\Delta z)+\chi_C(\mathbf{q}+\mathbf{k},\varepsilon)
&\approx
\chi_S(\mathbf{q},\Delta z)
+\mathbf{k}\cdot\nabla_{\mathbf{q}}\chi_S(\mathbf{q},\Delta z)
+\chi_C(\mathbf{q},\varepsilon).
\end{aligned}
\]
The same expansion at \(\mathbf{q}'\) is subtracted. The difference that enters \(R_0\) is
\[
\begin{aligned}
&\bigl[\chi_S(\mathbf{q}+\mathbf{k})+\chi_C(\mathbf{q}+\mathbf{k},\varepsilon)\bigr]
-
\bigl[\chi_S(\mathbf{q}'+\mathbf{k})+\chi_C(\mathbf{q}'+\mathbf{k},\varepsilon)\bigr] \\
&\approx
\bigl[\chi_S(\mathbf{q})-\chi_S(\mathbf{q}')\bigr]
+\mathbf{k}\cdot\mathbf{a}
+\bigl[\chi_C(\mathbf{q},\varepsilon)-\chi_C(\mathbf{q}',\varepsilon)\bigr],
\end{aligned}
\]
with \(\mathbf{a}\) defined in §11.

### 10.2 Equation (4)

**Approx.** (Eq. (3) + \(M(\mathbf{q}+\mathbf{k})\approx M(\mathbf{q})\))
\[
\begin{aligned}
R_0(\mathbf{q}+\mathbf{k},\,\mathbf{q}'+\mathbf{k},\,\Delta z,\,\varepsilon)
&\approx
R_0(\mathbf{q},\mathbf{q}',\Delta z,0)
\exp\bigl(2\pi\mathrm{i}\,\mathbf{a}\cdot\mathbf{k}\bigr)
\exp\bigl(2\pi\mathrm{i}\,(b_1\varepsilon+b_2\varepsilon^2)\bigr),
\end{aligned}
\]
where \(b_1,b_2\) are defined in §13. The two exponentials separate because mixed \(\mathbf{k}\varepsilon\) terms were dropped, so the \((\mathbf{k},\varepsilon)\) integral **factors** into \(E_S\,E_{C,\mathrm{tot}}\).

---

## 11. Envelope \(E_S\), Eq. (5), from A1

### 11.1 Vector \(\mathbf{a}\)

**Def.**
\[
\mathbf{a}(\mathbf{q},\mathbf{q}',\Delta z)
:=
\nabla_{\mathbf{q}}\chi_S(\mathbf{q},\Delta z)
-
\nabla_{\mathbf{q}'}\chi_S(\mathbf{q}',\Delta z).
\]

Using §4.4,
\[
\mathbf{a}
=
\bigl(C_3\lambda^3 q^2+C_5\lambda^5 q^4+\Delta z\,\lambda\bigr)\mathbf{q}
-
\bigl(C_3\lambda^3 {q'}^2+C_5\lambda^5 {q'}^4+\Delta z\,\lambda\bigr)\mathbf{q}'.
\]

**1D:**
\[
a
=C_3\lambda^3(q^3-{q'}^3)
+C_5\lambda^5(q^5-{q'}^5)
+\Delta z\,\lambda\,(q-q').
\]

### 11.2 Gaussian Fourier transform (A1)

**Def.** of the spatial envelope (the \(\mathbf{k}\)-integral in Eq. (1) after Eq. (4)):
\[
E_S(\mathbf{q},\mathbf{q}',\Delta z)
:=
\int_{\mathbb{R}^2}
s(\mathbf{k})\,\exp\bigl(2\pi\mathrm{i}\,\mathbf{a}\cdot\mathbf{k}\bigr)\,\mathrm{d}^2k.
\]

**Thm.** (characteristic function of a centred isotropic Gaussian; 2D). With \(s\) as in §7 and the kernel \(\mathrm{e}^{2\pi\mathrm{i}\,\mathbf{a}\cdot\mathbf{k}}\),
\[
E_S(\mathbf{q},\mathbf{q}',\Delta z)
=\exp\bigl(-2\pi^2\sigma_{\mathrm{ill}}^2\,|\mathbf{a}|^2\bigr).
\]
The 1D theorem is the same with \(|\mathbf{a}|^2\to a^2\). Proof: \(\mathbb{E}[\mathrm{e}^{\mathrm{i}\mathbf{t}\cdot\mathbf{k}}]=\mathrm{e}^{-\frac12\sigma_{\mathrm{ill}}^2|\mathbf{t}|^2}\) at \(\mathbf{t}=2\pi\mathbf{a}\); equivalently, complete the square in rectangular coordinates using \(s=s(k_x)s(k_y)\).

**Thm.** (rewrite in FWHM \(q_{\mathrm{ill}}\)). Substitute \(\sigma_{\mathrm{ill}}^2=q_{\mathrm{ill}}^2/(8\ln 2)\):
\[
\boxed{
E_S(\mathbf{q},\mathbf{q}',\Delta z)
=\exp\Biggl(
-\frac{\pi^2 q_{\mathrm{ill}}^2}{4\ln 2}\,
\bigl|\mathbf{a}(\mathbf{q},\mathbf{q}',\Delta z)\bigr|^2
\Biggr).
}
\]
This is the canonical Eq. (5). It is real and even in \((\mathbf{q},\mathbf{q}')\leftrightarrow(\mathbf{q}',\mathbf{q})\).

**Eq. (5) expanded (2D), showing the new \(\mathbf{q}\cdot\mathbf{q}'\) term.** Let
\[
u(\mathbf{q}):=C_3\lambda^3 q^2+C_5\lambda^5 q^4+\Delta z\,\lambda,
\]
so \(\nabla\chi_S=u(\mathbf{q})\,\mathbf{q}\) and \(\mathbf{a}=u(\mathbf{q})\mathbf{q}-u(\mathbf{q}')\mathbf{q}'\). Then
\[
|\mathbf{a}|^2
=
u(\mathbf{q})^2\,q^2
+u(\mathbf{q}')^2\,{q'}^2
-2\,u(\mathbf{q})u(\mathbf{q}')\,(\mathbf{q}\cdot\mathbf{q}').
\]
The last term is absent from any treatment that replaces \(\mathbf{q}\cdot\mathbf{q}'\) by the product of magnitudes; the paper flags it as new in the 2D FO generalisation.

**1D expanded polynomial** (structure of the typeset Eq. (5)):
\[
E_S(q,q',\Delta z)
=\exp\Biggl(
-\frac{\pi^2 q_{\mathrm{ill}}^2}{4\ln 2}
\Bigl[
C_3\lambda^3(q^3-{q'}^3)
+C_5\lambda^5(q^5-{q'}^5)
+\Delta z\,\lambda\,(q-q')
\Bigr]^2
\Biggr).
\]
Using \(q^3-{q'}^3=(q-q')(q^2+qq'+{q'}^2)\) one may factor \((q-q')^2\) times a symmetric cubic/quintic polynomial. For **ac** (\(C_3=0\)) only \(C_5\) and \(\Delta z\) remain.

**CTF slice (prose after Eq. (6)).** Setting \(\mathbf{q}'=\mathbf{0}\) (so \(\mathbf{a}=\nabla\chi_S(\mathbf{q})\)) recovers the separable CTF envelope \(E_S(\mathbf{q},\Delta z)\). Cross terms in \(q,q'\) and the dot product are then absent.

**Lean note.** The main-text OCR of Eq. (5) is unusable. Encode A1’s integral as the **definition** of \(E_S\) and the Gaussian-FT closed form as a **theorem**. The polynomial form is a corollary of the gradient formula.

---

## 12. Envelope \(E_{C,\mathrm{tot}}\), Eqs. (6a)–(6b), from A1

### 12.1 Integral

**Def.**
\[
E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{q}')
:=
\int_{-\infty}^{\infty}
c(\varepsilon)\,
\exp\bigl(2\pi\mathrm{i}\,(b_1\varepsilon+b_2\varepsilon^2)\bigr)
\,\mathrm{d}\varepsilon,
\]
with \(b_1(\mathbf{q},\mathbf{q}'),\,b_2(\mathbf{q},\mathbf{q}')\) from §13. This is the \(\varepsilon\)-integral in Eq. (1) after Eq. (4).

### 12.2 Closed form (theorem)

**Thm.** (Gaussian integral with linear + quadratic phase). Completing the square in
\[
-\frac{\varepsilon^2}{2\sigma_E^2}+2\pi\mathrm{i} b_1\varepsilon+2\pi\mathrm{i} b_2\varepsilon^2
\]
yields
\[
\boxed{
E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{q}')
=
\bigl(1-4\pi\mathrm{i}\,b_2\sigma_E^2\bigr)^{-1/2}
\exp\Biggl(
-\frac{2\pi^2\sigma_E^2\,b_1^2}{1-4\pi\mathrm{i}\,b_2\sigma_E^2}
\Biggr),
}
\]
principal branch of \(z^{-1/2}\) with \(z=1\) at \(b_2=0\).

**Thm.** (FWHM form). With \(\sigma_E^2=\Delta E^2/(8\ln 2)\),
\[
1-4\pi\mathrm{i}\,b_2\sigma_E^2
=1-\mathrm{i}\,\frac{\pi\,b_2\Delta E^2}{2\ln 2},
\qquad
2\pi^2\sigma_E^2
=\frac{\pi^2\Delta E^2}{4\ln 2}.
\]

### 12.3 Equations (6b) and (6a) as printed

**Def. / rewrite of the prefactor** — Eq. (6b):
\[
E_{CC}(\mathbf{q},\mathbf{q}')
:=
\bigl(1-4\pi\mathrm{i}\,b_2\sigma_E^2\bigr)^{-1/2}.
\]
Then \(E_{CC}^2=(1-4\pi\mathrm{i}\,b_2\sigma_E^2)^{-1}\) and Eq. (6a) is
\[
\boxed{
E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{q}')
=
E_{CC}(\mathbf{q},\mathbf{q}')
\exp\Bigl(
-2\pi^2\sigma_E^2\,b_1^2\,
E_{CC}(\mathbf{q},\mathbf{q}')^2
\Bigr).
}
\]
The typeset Eq. (6a) writes the exponent with the characteristic **\(16\ln 2\)** of Hanßen–Trepte: because
\[
2\pi^2\sigma_E^2 b_1^2
=\frac{(\Delta E)^2}{16\ln 2}\,(2\pi b_1)^2,
\]
and \(2\pi b_1\) is the coefficient of \(\varepsilon\) in the **radian** phase \(2\pi(\chi_C(\mathbf{q})-\chi_C(\mathbf{q}'))\). Both \(\pi\) (from \(W=\mathrm{e}^{2\pi\mathrm{i}\chi}\)) and \(16\ln 2\) (from FWHM) must appear.

**Consistency check (nac CTF, Schramm 2012).** Set \(\mathbf{q}'=\mathbf{0}\), \(C_{CC}=C_{3C}=0\): \(b_2=0\), \(b_1=C_C\lambda q^2/(2E)\),
\[
E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{0})
=\exp\Biggl(
-\frac{\bigl(\pi C_C\lambda\Delta E\,q^2\bigr)^2}{16\ln 2\,E^2}
\Biggr),
\]
which is the standard chromatic envelope \(E_C(q)\) of Schramm *et al.* 2012 / Tromp & Schramm.

**CTF slice.** \(E_{C,\mathrm{tot}}(\mathbf{q})\) of Schramm 2012 is \(E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{0})\). Cross terms of the form \(q^2{q'}^2\), \(q^4{q'}^4\) in \(b_1^2\) and \(b_2\) are the FO/CTF difference for chromatic envelopes (already noted for nac in Yu 2017).

A1’s parenthetical “\(E_S\) (Eq. (6b))” is a **typo**: \(E_S\) is Eq. (5); Eq. (6b) is \(E_{CC}\).

---

## 13. Explicit \(b_1\), \(b_2\)

**Def.** Linear/quadratic splitting of the chromatic path difference:
\[
\chi_C(\mathbf{q},\varepsilon)-\chi_C(\mathbf{q}',\varepsilon)
=b_1\varepsilon+b_2\varepsilon^2.
\]

**Thm.** (collect powers of \(\varepsilon\) in §5; use \(q=|\mathbf{q}|\), \(q'=|\mathbf{q}'|\))
\[
\begin{aligned}
b_1(\mathbf{q},\mathbf{q}')
&=
\frac{C_C\lambda}{2E}\bigl(q^2-{q'}^2\bigr)
+
\frac{C_{3C}\lambda^3}{4E}\bigl(q^4-{q'}^4\bigr),
\\[0.4em]
b_2(\mathbf{q},\mathbf{q}')
&=
\frac{C_{CC}\lambda}{2E^2}\bigl(q^2-{q'}^2\bigr).
\end{aligned}
\]

**1D:** \(q^2-{q'}^2\) and \(q^4-{q'}^4\) are differences of even powers of **signed** scalars.

**ac** (\(C_C=0\)):
\[
b_1=\frac{C_{3C}\lambda^3}{4E}(q^4-{q'}^4),\qquad
b_2=\frac{C_{CC}\lambda}{2E^2}(q^2-{q'}^2).
\]

**nac** (\(C_{CC}=C_{3C}=0\)):
\[
b_1=\frac{C_C\lambda}{2E}(q^2-{q'}^2),\qquad
b_2=0
\quad\Rightarrow\quad
E_{CC}=1,\quad
E_{C,\mathrm{tot}}=\mathrm{e}^{-2\pi^2\sigma_E^2 b_1^2}.
\]

Units: \(b_1\) is waves/energy, \(b_2\) is waves/energy\(^2\), so that \(b_1\varepsilon+b_2\varepsilon^2\) is in waves and \(2\pi(b_1\varepsilon+b_2\varepsilon^2)\) is in radians.

---

## 14. Ratios \(\Gamma_C\), \(\Gamma_S\), Eqs. (7)

**Def.** Compare separable CTF envelopes (arguments \((\mathbf{q})\) and \((\mathbf{q}')\), i.e. the \(q'=0\) slices) to the inseparable FO envelopes:
\[
\begin{aligned}
\Gamma_C(\mathbf{q},\mathbf{q}')
&=
\frac{
E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{0})\,
E_{C,\mathrm{tot}}(\mathbf{q}',\mathbf{0})
}{
E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{q}')
}
\tag{7a}
\\[0.6em]
\Gamma_S(\mathbf{q},\mathbf{q}',\Delta z)
&=
\frac{
E_S(\mathbf{q},\mathbf{0},\Delta z)\,
E_S(\mathbf{q}',\mathbf{0},\Delta z)
}{
E_S(\mathbf{q},\mathbf{q}',\Delta z)
}.
\tag{7b}
\end{aligned}
\]
The paper writes \(E_{C,\mathrm{tot}}(q)\) for the CTF slice \(E_{C,\mathrm{tot}}(q,0)\).

**Thm.** \(\Gamma_C\Gamma_S=1\) for all \((\mathbf{q},\mathbf{q}',\Delta z)\) if \(\alpha_{\mathrm{ill}}=\Delta E=0\) (perfect coherence: all envelopes \(=1\)).

**Thm.** \(\Gamma_C\Gamma_S=1\) on the axes \(\mathbf{q}=\mathbf{0}\) or \(\mathbf{q}'=\mathbf{0}\) even with partial coherence, because FO and CTF envelopes then coincide.

**Remark (conjugate).** The CTF intensity \(|\mathrm{FT}^{-1}(\boldsymbol{\Psi}H)|^2\) produces the bilinear factor \(E_{C,\mathrm{tot}}(\mathbf{q},0)\,E_{C,\mathrm{tot}}(\mathbf{q}',0)^*\). Equation (7a) as printed uses the **non-conjugated** product \(E(q)E(q')\). For ac, \(E_{C,\mathrm{tot}}\) is complex; the paper states that \(\Gamma_C\) is complex and that **it suffices to plot \(|\Gamma_C|\)** because \(\mathrm{Im}\,E_{C,\mathrm{tot}}\) is numerically small inside the aperture (Schramm 2012 parameters, Table 1). Lean should:

1. define \(\Gamma_C\) exactly as (7a);
2. separately record \(|\Gamma_C|\) as the quantity plotted in Fig. 1;
3. not silently insert a conjugate.

FO is treated as the rigorous benchmark: \(\Gamma_C\Gamma_S\neq 1\) warns that CTF may be inaccurate.

**1D analysis in §3.1 and A2:** vector dependence reverts to signed scalars. Explicit ac formulae are in §15–§16.

---

## 15. Appendix A2: polar form of \(E_{CC}\), \(A(\mathbf{q},\mathbf{q}')\), \(\theta(\mathbf{q},\mathbf{q}')\)

A2 is written for **1D** ac-LEEM (\(C_C=0\); \(C_{CC},C_{3C}\) kept). All \(q,q'\) below are signed scalars. The 2D polar form is identical after \(q^2\mapsto|\mathbf{q}|^2\), \(q^4\mapsto|\mathbf{q}|^4\).

### 15.1 Polar decomposition of \(E_{C,\mathrm{tot}}\)

**Def.**
\[
E_{C,\mathrm{tot}}(q,q')=A(q,q')\,\mathrm{e}^{\mathrm{i}\theta(q,q')},
\qquad
A\ge 0,\ \theta\in\mathbb{R}.
\]
CTF slice: \(E_{C,\mathrm{tot}}(q)=A(q,0)\,\mathrm{e}^{\mathrm{i}\theta(q,0)}\).

### 15.2 Polar form of \(E_{CC}\)

Write
\[
E_{CC}(q,q')=\bigl(1-\mathrm{i}\,y\bigr)^{-1/2},
\qquad
y:=\frac{\pi b_2\Delta E^2}{2\ln 2}.
\]
With ac \(b_2\) from §13,
\[
y=\gamma\,(q^2-{q'}^2),
\qquad
\gamma
:=\frac{\pi C_{CC}\lambda\Delta E^2}{4\ln 2\,E^2}.
\]
(The typeset A2 writes a symbol equal to “\(4\ln 2\cdot C_{CC}/E^2\)” times \(\Delta E\) powers; restore \(\pi\) and \(\lambda\) so that \(y\) is dimensionless and matches §12.)

**Thm.** (polar form of \((1-\mathrm{i}y)^{-1/2}\), principal branch)
\[
\begin{aligned}
E_{CC}(q,q')
&=
\bigl(1+y^2\bigr)^{-1/4}
\exp\Bigl(\frac{\mathrm{i}}{2}\arctan y\Bigr)
\\
&=
\bigl[1+\gamma^2(q^2-{q'}^2)^2\bigr]^{-1/4}
\exp\Bigl(\frac{\mathrm{i}}{2}\arctan\bigl(\gamma(q^2-{q'}^2)\bigr)\Bigr).
\end{aligned}
\]
Proof: \(|1-\mathrm{i}y|=\sqrt{1+y^2}\), \(\arg(1-\mathrm{i}y)=-\arctan y\), so
\(\arg\bigl((1-\mathrm{i}y)^{-1/2}\bigr)=\tfrac12\arctan y\).

### 15.3 Polar form of the remaining exponential (ac)

For ac, \(b_1\propto(q^4-{q'}^4)\). Let
\[
\eta
:=\frac{\pi^2\Delta E^2}{4\ln 2}
\left(\frac{C_{3C}\lambda^3}{4E}\right)^2
=\frac{(\pi C_{3C}\lambda^3\Delta E)^2}{64\ln 2\,E^2}.
\]
Then \(2\pi^2\sigma_E^2 b_1^2=\eta\,(q^4-{q'}^4)^2\), and
\[
\frac{1}{1-\mathrm{i}y}
=\frac{1+\mathrm{i}y}{1+y^2}.
\]

**Thm.**
\[
\exp\Bigl(-2\pi^2\sigma_E^2 b_1^2 E_{CC}^2\Bigr)
=
\exp\Biggl(
-\frac{\eta(q^4-{q'}^4)^2}{1+\gamma^2(q^2-{q'}^2)^2}
\Biggr)
\exp\Biggl(
-\mathrm{i}\,
\frac{\eta\gamma(q^2-{q'}^2)(q^4-{q'}^4)^2}{1+\gamma^2(q^2-{q'}^2)^2}
\Biggr).
\]
(The paper’s typeset A2 writes this exponential in polar form with a coefficient “\(16\ln 2\cdot(\tfrac12 C_{3C}\Delta E/E)^2\)”; that is the Hanßen–Trepte packaging of \(\eta\) **without** \(\lambda,\pi\) restored. Use \(\eta\) as above.)

### 15.4 Combined \(A\) and \(\theta\) (A2, ac)

**Thm.** (product of §15.2 and §15.3)
\[
\begin{aligned}
A(q,q')
&=
\bigl[1+\gamma^2(q^2-{q'}^2)^2\bigr]^{-1/4}
\exp\Biggl(
-\frac{\eta(q^4-{q'}^4)^2}{1+\gamma^2(q^2-{q'}^2)^2}
\Biggr),
\\[0.6em]
\theta(q,q')
&=
\frac12\arctan\bigl(\gamma(q^2-{q'}^2)\bigr)
-
\frac{\eta\gamma(q^2-{q'}^2)(q^4-{q'}^4)^2}{1+\gamma^2(q^2-{q'}^2)^2}.
\end{aligned}
\]

**Parity.** \(A(q,q')=A(q',q)=A(|q|,|q'|)\). \(\theta(q,q')=-\theta(q',q)\), and \(\theta\) changes sign with \((q^2-{q'}^2)\).

### 15.5 \(\Gamma_C\) in polar form (A2)

**Thm.** From (7a) and the polar decomposition,
\[
\Gamma_C(q,q')
=
\frac{A(q,0)\,A(q',0)}{A(q,q')}
\exp\Bigl(
\mathrm{i}\bigl[\theta(q,0)+\theta(q',0)-\theta(q,q')\bigr]
\Bigr).
\]
The **amplitude** used in the paper’s discussion is \(A(q,0)A(q',0)/A(q,q')\).

---

## 16. 1D \(\Gamma_S\), end of A2

\(E_S\) is real. From (7b) and \(E_S=\exp(-\kappa|a|^2)\) with
\[
\kappa=\frac{\pi^2 q_{\mathrm{ill}}^2}{4\ln 2}:
\]

**Thm.** (algebra of Gaussians). Let \(\mathbf{u}=\nabla\chi_S(\mathbf{q})\), \(\mathbf{v}=\nabla\chi_S(\mathbf{q}')\). Then
\[
\Gamma_S
=\exp\bigl(-\kappa|\mathbf{u}|^2-\kappa|\mathbf{v}|^2+\kappa|\mathbf{u}-\mathbf{v}|^2\bigr)
=\exp\bigl(-2\kappa\,\mathbf{u}\cdot\mathbf{v}\bigr).
\]

**1D, general (nac+ac):**
\[
\Gamma_S(q,q',\Delta z)
=\exp\Bigl(
-2\kappa\,
\partial_q\chi_S(q,\Delta z)\,
\partial_q\chi_S(q',\Delta z)
\Bigr).
\]

**1D, ac** (\(C_3=0\)), as at the end of A2:
\[
\partial_q\chi_S(q,\Delta z)
=\bigl(C_5\lambda^5 q^4+\Delta z\,\lambda\bigr)q
=C_5\lambda^5 q^5+\Delta z\,\lambda\, q,
\]
\[
\boxed{
\Gamma_S(q,q',\Delta z)
=\exp\Biggl[
-\frac{\pi^2 q_{\mathrm{ill}}^2}{2\ln 2}
\bigl(C_5\lambda^5 q^5+\Delta z\,\lambda\, q\bigr)
\bigl(C_5\lambda^5 {q'}^5+\Delta z\,\lambda\, q'\bigr)
\Biggr].
}
\]
The typeset A2 shows the same **polynomial** \((C_5 q^5+\Delta z\,q)(C_5{q'}^5+\Delta z\,q')\) (without \(\lambda\)) multiplied by a factor OCR’d as “\(2\ln 2\,q_{\mathrm{ill}}^2\)”. The prefactor above is the one implied by A1’s Gaussian FT together with \(\Gamma_S=\mathrm{e}^{-2\kappa uv}\). Encode that chain in Lean, not the OCR’d coefficient.

For **2D**, replace the product of scalars by the dot product
\[
\Gamma_S(\mathbf{q},\mathbf{q}',\Delta z)
=\exp\bigl(-2\kappa\,\nabla\chi_S(\mathbf{q})\cdot\nabla\chi_S(\mathbf{q}')\bigr).
\]

---

## 17. Jacobi–Anger for the sinusoidal object

**Paper:** §3.2, unnumbered. Object
\[
\psi_0(x)\propto\exp\bigl(\mathrm{i}\,\varphi\sin(kx)\bigr),
\qquad
k=\frac{2\pi}{\Lambda}.
\]

**Thm.** (Jacobi–Anger / Bessel generating function)
\[
\exp\bigl(\mathrm{i}\,\varphi\sin\theta\bigr)
=\sum_{n\in\mathbb{Z}}J_n(\varphi)\,\mathrm{e}^{\mathrm{i}n\theta},
\]
hence
\[
\exp\bigl(\mathrm{i}\,\varphi\sin(kx)\bigr)
=\sum_{n\in\mathbb{Z}}J_n(\varphi)\,\mathrm{e}^{\mathrm{i}nkx}.
\]

**Lean** (`LeemFO/PhaseObject.lean`, does not import `LeemFO.Basic`): `phaseFun`, `phaseFun_periodic`, `besselJ` (Fourier coefficient of `phaseFun` on `(0,2\pi]`), `besselJ_bound`, `summable_besselJ`, `jacobi_anger_on_Ioc` (`HasSum` for \(\theta\in(0,2\pi]\)), `jacobi_anger` (all real \(\theta\), via `toIocMod`).

**Corollary** (Fourier representation, this paper’s \(2\pi\) convention).  
\(\mathrm{e}^{\mathrm{i}n k x}=\mathrm{e}^{2\pi\mathrm{i}\,(nk/(2\pi))\,x}\), so the object is a discrete spectrum at spatial frequencies
\[
q_n=\frac{nk}{2\pi}=\frac{n}{\Lambda},
\qquad
\boldsymbol{\Psi}(q)\propto\sum_{n\in\mathbb{Z}}J_n(\varphi)\,\delta(q-q_n)
\]
(tempered distributions on \(\mathbb{R}\); on a large finite window the \(\delta\) become sinc peaks). Larger \(\varphi\) populates larger \(|n|\), which is why CTF fails for strongly corrugated graphene: the object samples \((q,q')\) away from the axes where \(\Gamma_C\Gamma_S\approx 1\).

\(J_{-n}(\varphi)=(-1)^n J_n(\varphi)\) for real \(\varphi\) (**Thm.**, Bessel). The phase amplitude \(\varphi=4\pi A/\lambda_0\) is a **Def.** (kinematic reflection), not a theorem of FO.

---

## 18. Assembled FO intensity (working formula)

After Eqs. (1)–(6), the paper’s computational kernel is

**Thm.** (assembly of (1)–(4) with A1)
\[
R(\mathbf{q},\mathbf{q}',\Delta z)
=
R_0(\mathbf{q},\mathbf{q}',\Delta z,0)
\,E_S(\mathbf{q},\mathbf{q}',\Delta z)
\,E_{C,\mathrm{tot}}(\mathbf{q},\mathbf{q}'),
\]
with \(R_0(\cdot,\cdot,\Delta z,0)=M(\mathbf{q})M(\mathbf{q}')W_S(\mathbf{q},\Delta z)W_S^*(\mathbf{q}',\Delta z)\), \(E_S\) from §11, \(E_{C,\mathrm{tot}}\) from §12.

Then \(I(\mathbf{r})\) is §8. All subsequent nac/ac specialisation is substitution of coefficients (\(C_3=0\) or \(C_5=0\), etc.), not a change of theorem.

---

## 19. Lean encoding checklist

Wavelength is `LEEM.lam` (Lean reserves `λ`). No `sorry`. Build with `lake build` after `elan`.

| Item | Status | Lean name |
|---|---|---|
| \(\psi_0=\sigma\mathrm{e}^{\mathrm{i}\phi}\) | Def. | `LEEM.objectWave` |
| \(\mathbf{q}=\boldsymbol{\alpha}/\lambda\) | Def. | comments in `LeemFO/Basic.lean` |
| FT pair with \(\mathrm{e}^{\pm 2\pi\mathrm{i}\mathbf{q}\cdot\mathbf{r}}\) | Def. | image kernel convention only |
| \(M\) disk | Def. | `aperture`, `aperture_eq_zero_or_one` |
| \(M(\mathbf{q}+\mathbf{k})\approx M(\mathbf{q})\) | Approx. | not a theorem |
| \(W_S=\mathrm{e}^{2\pi\mathrm{i}\chi_S}\), \(\chi_S\) §4.2 | Def. | `chiS`, `waveS`; 2D `chiS2` |
| Sign of \(\Delta z\) | Def. | `+\tfrac12\Delta z\,\mathtt{lam}\,q^2` in `chiS` |
| \(\nabla\chi_S\) / \(\partial_q\chi_S\) | Thm. | `hasDerivAt_chiS`, `deriv_chiS`, `hasGradientAt_chiS2` |
| Taylor in tilt \(k\) | Thm. | `chiS_taylor` (`IsLittleO` remainder) |
| \(W_C=\mathrm{e}^{2\pi\mathrm{i}\chi_C}\) | Def. | `chiC`, `waveC` |
| \(c(\varepsilon)\), \(s(\mathbf{k})\) Gaussians | Def. | `gaussian1D`, `gaussian2D` |
| \(\Delta E=2\sqrt{2\ln 2}\,\sigma_E\) | Thm. | `fwhmFactor`, `gaussian_fwhm`, `sigmaE` |
| \(q_{\mathrm{ill}}=2\sqrt{2\ln 2}\,\sigma_{\mathrm{ill}}\) | Thm. | `sigmaIll`, `variance_from_fwhm` |
| \(s(\mathbf{k})=s(k_x)s(k_y)\) | Thm. | `gaussian2D_closed` |
| \(I(\mathbf{r})\) bilinear inverse FT | Def. | not simulated; kernel `R0`, `R_FO` |
| (1)(2) \(R=\int s\,c\,R_0\) | Def. | envelopes defined as those integrals |
| (3)(4) Taylor + no mixed \(\mathbf{k}\varepsilon\) | Approx. | `chiS_taylor`; mixed \(k\varepsilon\) dropped by definition of `R_FO` |
| \(\mathbf{a}=\nabla\chi_S(\mathbf{q})-\nabla\chi_S(\mathbf{q}')\) | Def. | 1D `aS`; `aS_eq_deriv_sub` |
| \(E_S=\int s\,\mathrm{e}^{2\pi\mathrm{i}a k}\) | Def. | `spatialEnvelopeIntegral` |
| \(E_S=\mathrm{e}^{-2\pi^2\sigma_{\mathrm{ill}}^2 a^2}\) | Thm. | `spatialEnvelopeIntegral_eq_closed`, `charFun_source1D` |
| \(E_S\) in \(q_{\mathrm{ill}}\) | Thm. | `spatialEnvelope_eq_fwhm`, `kappaIll` |
| 2D Gaussian FT | Thm. | `charFun_source2D`, `spatialEnvelopeIntegral2_eq` |
| \(b_1\varepsilon+b_2\varepsilon^2=\Delta\chi_C\) | Thm. | `chiC_sub`, `b1`, `b2` |
| \(E_{C,\mathrm{tot}}=\int c\,\mathrm{e}^{2\pi\mathrm{i}(b_1\varepsilon+b_2\varepsilon^2)}\) | Def. | `chromaticEnvelopeIntegral` |
| closed form (6a)(6b) | Thm. | `chromaticEnvelopeIntegral_eq_closed`, `ecc`, `chromaticEnvelopeClosed` |
| NAC \(b_2=0\) | Thm. | `b2_nac`, `chromaticEnvelopeClosed_nac` |
| AC \(C_3=C_C=0\) in \(b_1\) | Thm. | `b1_ac` |
| hermiticity \(R_0(q',q)=\overline{R_0(q,q')}\) | Thm. | `R0_hermitian` |
| CTF as \(q'=0\) | Thm. | `spatialCTF`, `chromaticCTF`, `R_FO_eq_R_CTF_axis`; `R_CTF` matches printed (7a) (no chromatic conjugate); `R_CTF_eq_R_FO_mul_gamma` |
| (7) \(\Gamma_C,\Gamma_S\) | Def. | `gammaC`, `gammaS`; plotted amplitude `gammaC_abs` |
| \(\Gamma_S=\mathrm{e}^{-2\kappa uv}\) | Thm. | `gammaS_eq_dot`, `gammaS_eq_kappa`, `gammaS_ac` |
| \(\Gamma=1\) perfect coherence | Thm. | `PerfectCoherence`, `spatialEnvelope_of_perfect`, `chromaticEnvelope_of_perfect`, `gammaS_perfect`, `gammaC_perfect`, `gamma_product_perfect` |
| axes \(\Gamma_S=1\) | Thm. | `gammaS_axis`, `gammaS_axis_q` |
| axes \(\Gamma_C=1\) or \(\lvert\Gamma_C\rvert=1\) | Thm. | `gammaC_axis`; `gammaC_norm_axis_q` (`q=0`, needs \(0<\Delta E\)) |
| polar \(E_{CC}\) (Eq. (6b)) | Thm. | `ecc_polar`, `ecc_eq_polar` (\(y=4\pi b_2\sigma_E^2\)), `ecc_norm`, `arg_one_sub_I`. Combined A2 amplitude/phase \(A,\theta\) of \(E_{C,\mathrm{tot}}\) is not a separate definition. |
| Jacobi–Anger | Thm. | `jacobi_anger`, `jacobi_anger_on_Ioc`, `besselJ` |
| \(\varphi=4\pi A/\lambda_0\) | Def. | kinematics, outside FO |
| Aperture modes \(M=2\lfloor q_{\mathrm{ap}}\Lambda\rfloor+1\) | Thm. | `nAperture`, `modeSet`, `card_modeSet`, `card_modePairs`, `mode_in_aperture` |
| Discrete bilinear FO image | Def. | `discreteFOImage`, `besselCoeffs`, `sinusoidalFOImage` |

### 19.1 Module map

| File | Role |
|---|---|
| `LeemFO/Basic.lean` | `LEEM`, `chiS`/`chiC`, `aperture`, `waveS`/`waveC`, `R0`, `b1`/`b2`/`aS`, nac/ac |
| `LeemFO/Gaussian.lean` | FWHM, `charFun_source1D`, `charFun_source2D` |
| `LeemFO/Aberration.lean` | `hasDerivAt_chiS`, `chiS_taylor`, `chiC_sub`, `hasGradientAt_chiS2` |
| `LeemFO/EnvelopeSpatial.lean` | `spatialEnvelopeIntegral` = closed = FWHM |
| `LeemFO/EnvelopeChromatic.lean` | quadratic-phase integral, `ecc`, polar form, `chromaticEnvelopeClosed_neg` |
| `LeemFO/CTF.lean` | `q'=0` slice, `R0_hermitian`, `R_FO` vs `R_CTF` |
| `LeemFO/Ratios.lean` | \(\Gamma_C,\Gamma_S\) identities |
| `LeemFO/PhaseObject.lean` | Jacobi–Anger (no `LeemFO.Basic` import) |
| `LeemFO/Inverse.lean` | Aperture-truncated Bessel modes for the discrete inverse (`nAperture`, `modeSet`, `sinusoidalFOImage`) |
| `LeemFO/Tikhonov.lean` | Scalar/2×2 Fourier-bin Tikhonov (`tikhonovJ`, `tikhonov_error`, `reconstructCost`) |
| `LeemFO/LinearInverse.lean` | Linearized slice identifiability (`R_FO_axis_eq_zero_iff`, `ihat_gauge`, `ihatJac_vacuum`) |

**Linearized Fourier-diagonal inverse (see [LINEAR_INVERSE.md](LINEAR_INVERSE.md)).** Multi-defocus Tikhonov on the CTF slice \(R_{\mathrm{FO}}(q,0,\Delta z)\) has a unique minimizer for \(\alpha>0\), the exact bias–noise identity \(\hat x-x^\star=(\sum \overline h n-\alpha x^\star)/D\), and the sharp triangle bound. Modes with \(|q|>q_{\mathrm{ap}}\) are identically invisible. Bilinear FO is phase-gauge invariant; its vacuum linearization has an exact quadratic remainder (one Gauss–Newton step from vacuum *is* the diagonal Tikhonov solve). Cost is modelled as \(O(KN\log N)\) DFTs plus \(O(KN)\) bin solves, without proving FFT existence. \(K=1\) cannot identify a general complex \((X(q),X(-q))\) pair; weak-phase CTF zeros of \(\sin(2\pi\chi_S)\) sit inside a large enough aperture. Statistical noise models remain informal.

**Inverse (journal-style note: [proofs/leemfo_inverse.pdf](proofs/leemfo_inverse.pdf)).** Lean details stay in [LINEAR_INVERSE.md](LINEAR_INVERSE.md). Scientific verdict: for a 2D experimental through-focal stack the fastest inverse that still fills CTF zeros is Fourier-diagonal multi-defocus Tikhonov on the slice \(R_{\mathrm{FO}}(q,0,\Delta z)\) (Schiske/Wiener), cost \(O(KN\log N)\). That map is the Fréchet derivative of bilinear FO at vacuum and is biased for \(\varphi=4\pi A/\lambda_0\not\ll 1\). Optional stage 2 is Gauss--Newton on bilinear FO, skipped when the stage-1 FO residual is at the noise floor (\(\max|\varphi|\lesssim 0.3\)). For the paper's 1D sinusoid, stage 2 collapses to Jacobi--Anger least squares on \(\{J_n(\varphi)\}_{|n|\le\lfloor q_{\mathrm{ap}}\Lambda\rfloor}\), cost \(O(M^2)\) with \(M=2\lfloor q_{\mathrm{ap}}\Lambda\rfloor+1\). Gerchberg--Saxton is either misspecified under partial coherence or a slower rewrite of Gauss--Newton. MAL/phase diversity is Gauss--Newton stacked over extra defoci, needed only when aberrations are unknown. Uniqueness of the regularized Fourier-diagonal estimator and its bias–noise identity are machine-checked in Lean 4.

**Do not encode from OCR of the two-column PDF.** Encode from the boxed formulae and from A1 integrals.

**2D vs 1D (easy to get wrong):**

- \(\chi_S,\chi_C,M,c\) depend on magnitudes / scalars as written.
- \(\mathbf{a}\), \(E_S\), \(\Gamma_S\) use **vectors** and \(\mathbf{q}\cdot\mathbf{q}'\) in 2D; **signed** \(q,q'\) in 1D.
- \(E_{C,\mathrm{tot}},b_1,b_2,\Gamma_C\) depend only on \((q^2,{q'}^2,q^4,{q'}^4)\), hence only on magnitudes in 2D.

---

## 20. References used in the reconstruction

1. K.M. Yu, K.L.W. Lau, M.S. Altman, *Ultramicroscopy* **200** (2019) 160–168. (§2.2, A1, A2; equation numbers (1)–(7).)
2. A.B. Pang, Th. Müller, M.S. Altman, E. Bauer, *J. Phys.: Condens. Matter* **21** (2009) 314006. (FO for nac LEEM.)
3. S.M. Schramm, A.B. Pang, M.S. Altman, R.M. Tromp, *Ultramicroscopy* **115** (2012) 88–108. (CTF envelopes for ac; Table 1 source; \(E_{C,\mathrm{tot}}(q)\) is the \(q'=0\) slice.)
4. K.M. Yu, A. Locatelli, M.S. Altman, *Ultramicroscopy* **183** (2017) 109–116. (FO vs CTF for nac; inseparable \(qq'\) cross terms.)
5. R.M. Tromp, S.M. Schramm, *Ultramicroscopy* (2012), optimization of the CTF:
   \(\chi=\tfrac12 C_1 q^2\lambda+\tfrac14 C_3 q^4\lambda^3+\tfrac16 C_5 q^6\lambda^5\), \(W=\mathrm{e}^{\mathrm{i}2\pi\chi}\).
6. H. Rose, D. Preikszas, *Optik* **92** (1992) 31; Th. Schmidt *et al.*, *Surf. Rev. Lett.* **9** (2002) 223. (Angular aberration expansion.)
7. K.J. Hanßen, L. Trepte, *Optik* **32** (1971) 519; J. Frank, *Optik* **38** (1973) 519; R.H. Wade, J. Frank, *Optik* **49** (1977) 81. (Gaussian energy/source envelopes.)
