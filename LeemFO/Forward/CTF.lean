/-
Copyright (c) 2026 The leem-fo-proof authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wilson
-/
import LeemFO.Forward.Basic
import LeemFO.Forward.Gaussian
import LeemFO.Forward.Aberration
import LeemFO.Forward.EnvelopeSpatial
import LeemFO.Forward.EnvelopeChromatic

/-!
# CTF as the FO envelopes at `q' = 0`, and hermiticity of `R₀`
-/

open Complex Real
open scoped ComplexConjugate

namespace LEEM

variable (p : LEEM)

/-- CTF spatial envelope: the FO envelope on the slice `q' = 0`. -/
noncomputable def spatialCTF (q Δz : ℝ) : ℂ :=
  p.spatialEnvelopeClosed q 0 Δz

/-- CTF chromatic envelope: the FO envelope on the slice `q' = 0`. -/
noncomputable def chromaticCTF (q : ℝ) : ℂ :=
  chromaticEnvelopeClosed p.sigmaE (p.b1 q 0) (p.b2 q 0)

theorem spatialCTF_eq (q Δz : ℝ) :
    p.spatialCTF q Δz = p.spatialEnvelopeClosed q 0 Δz := rfl

theorem chromaticCTF_eq (q : ℝ) :
    p.chromaticCTF q = chromaticEnvelopeClosed p.sigmaE (p.b1 q 0) (p.b2 q 0) := rfl

/-- On the diagonal `q' = q`, `a = 0` so `E_S = 1`. -/
theorem spatialEnvelopeClosed_diag (q Δz : ℝ) :
    p.spatialEnvelopeClosed q q Δz = 1 := by
  simp [spatialEnvelopeClosed, p.aS_zero_diag]

/-- On the axis `q' = 0`, `a = ∂χ_S(q)`. -/
theorem aS_axis (q Δz : ℝ) :
    p.aS q 0 Δz = p.C3 * p.lam ^ 3 * q ^ 3 + p.C5 * p.lam ^ 5 * q ^ 5 + Δz * p.lam * q := by
  simp [aS]

/-- Hermiticity of the coherent kernel: `R₀(q',q) = R₀(q,q')*`. -/
theorem R0_hermitian (q q' Δz ε : ℝ) :
    conj (p.R0 q q' Δz ε) = p.R0 q' q Δz ε := by
  simp only [R0, map_mul, conj_ofReal, conj_conj]
  ac_rfl

/-- After the paper’s first-order / no-mixed-term approximation, FO factors as
`R₀(q,q',Δz,0) E_S E_{C,tot}`. This is the working formula of §18. -/
noncomputable def R_FO (q q' Δz : ℝ) : ℂ :=
  p.R0 q q' Δz 0 * p.spatialEnvelopeClosed q q' Δz *
    chromaticEnvelopeClosed p.sigmaE (p.b1 q q') (p.b2 q q')

/-- Spatial CTF envelopes are real (Gaussian characteristic functions). -/
theorem spatialCTF_conj (q Δz : ℝ) :
    conj (p.spatialCTF q Δz) = p.spatialCTF q Δz :=
  Complex.conj_eq_iff_im.mpr (p.spatialEnvelopeClosed_real q 0 Δz)

/-- CTF product of one-argument envelopes, matching printed Eqs. (7a)–(7b)
(no extra conjugate on chromatic envelopes). Spatial envelopes are real, so
`conj (spatialCTF q')` is the same as `spatialCTF q'`. The bilinear intensity
`|FT⁻¹(Ψ H)|²` would instead use `conj (chromaticCTF q')`; see
`docs/FORMALIZATION.md` §14. -/
noncomputable def R_CTF (q q' Δz : ℝ) : ℂ :=
  p.R0 q q' Δz 0 * p.spatialCTF q Δz * conj (p.spatialCTF q' Δz) *
    p.chromaticCTF q * p.chromaticCTF q'

/-- Perfect coherence: vanishing energy and illumination spread. -/
def PerfectCoherence : Prop := p.qIll = 0 ∧ p.ΔE = 0

theorem spatialEnvelopeClosed_of_sigma_zero (q q' Δz : ℝ) (h : p.sigmaIll = 0) :
    p.spatialEnvelopeClosed q q' Δz = 1 := by
  simp [spatialEnvelopeClosed, h]

theorem chromaticEnvelopeClosed_of_sigma_zero (b1 b2 : ℝ) :
    chromaticEnvelopeClosed 0 b1 b2 = 1 := by
  have hd : eccDenom 0 b2 = 1 := by
    apply Complex.ext
    · simp [eccDenom]
    · simp [eccDenom]
  have he : ecc 0 b2 = 1 := by
    simp [ecc, hd, one_cpow]
  simp [chromaticEnvelopeClosed, he]

lemma sigmaIll_of_qIll_zero (h : p.qIll = 0) : p.sigmaIll = 0 := by
  simp [sigmaIll, h]

lemma sigmaE_of_ΔE_zero (h : p.ΔE = 0) : p.sigmaE = 0 := by
  simp [sigmaE, h]

theorem spatialEnvelope_of_perfect (h : p.PerfectCoherence) (q q' Δz : ℝ) :
    p.spatialEnvelopeClosed q q' Δz = 1 :=
  p.spatialEnvelopeClosed_of_sigma_zero q q' Δz (p.sigmaIll_of_qIll_zero h.1)

theorem chromaticEnvelope_of_perfect (h : p.PerfectCoherence) (q q' : ℝ) :
    chromaticEnvelopeClosed p.sigmaE (p.b1 q q') (p.b2 q q') = 1 := by
  rw [p.sigmaE_of_ΔE_zero h.2]
  exact chromaticEnvelopeClosed_of_sigma_zero _ _

/-- On the axis `q' = 0`, FO envelopes reduce to the CTF product
(the paper’s recovery of CTF from FO). -/
theorem R_FO_eq_R_CTF_axis (q Δz : ℝ) :
    p.R_FO q 0 Δz = p.R_CTF q 0 Δz := by
  unfold R_FO R_CTF spatialCTF chromaticCTF
  rw [p.spatialEnvelopeClosed_diag 0 Δz, p.b1_zero_diag, p.b2_zero_diag,
    chromaticEnvelopeClosed_nac]
  simp

theorem spatialCTF_at_zero (Δz : ℝ) : p.spatialCTF 0 Δz = 1 :=
  p.spatialEnvelopeClosed_diag 0 Δz

theorem chromaticCTF_at_zero :
    p.chromaticCTF 0 = chromaticEnvelopeClosed p.sigmaE 0 0 := by
  simp [chromaticCTF, p.b1_zero_diag, p.b2_zero_diag]

end LEEM
