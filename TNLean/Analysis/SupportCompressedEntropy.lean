/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.Entropy
import TNLean.Analysis.IsometricCompression
import TNLean.Analysis.SandwichedRenyiTwo
import TNLean.Channel.Spectral.Support

/-!
# Entropy functionals compressed to the reference support

Let $\rho,\omega\geq0$ and assume $\ker\omega\subseteq\ker\rho$.
If the columns of $V$ form an orthonormal basis of the support of $\omega$,
then both matrices are isometric expansions of their compressions by $V$.
The totalized logarithm and negative real powers vanish at zero, so the
nonunital functional calculus shows that quantum relative entropy and the
order-two sandwiched trace functional are unchanged by this compression.

## Main declarations

* `Matrix.PosSemidef.eq_isometry_expansion_compression_of_kernel_le` — support
  inclusion reconstructs a matrix from its support compression.
* `TNLean.quantumRelativeEntropy_support_compression` — relative entropy is
  invariant under compression to the reference support.
* `TNLean.sandwichedRenyiTwoTrace_support_compression` — the order-two
  sandwiched trace functional is invariant under the same compression.
* `TNLean.quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_of_faithful` —
  a faithful-reference density-operator inequality implies the
  support-restricted density-operator inequality.

The last theorem preserves both trace-one normalizations under support
compression.  It is only a reduction and does not assert the missing
faithful-reference inequality.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

variable {D k : ℕ}

/-- If $\ker\omega\subseteq\ker\rho$, an isometry whose range projection is the
support of $\omega$ reconstructs $\rho$ exactly from its compression. -/
theorem PosSemidef.eq_isometry_expansion_compression_of_kernel_le
    {ρ ω : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hker : ∀ v : Fin D → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (V : Matrix (Fin D) (Fin k) ℂ)
    (hRange : V * Vᴴ = hω.supportProj) :
    V * (Vᴴ * ρ * V) * Vᴴ = ρ := by
  have hright : ρ * hω.supportProj = ρ :=
    hω.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  have hleft : hω.supportProj * ρ = ρ := by
    have hadj := congrArg Matrix.conjTranspose hright
    simpa only [Matrix.conjTranspose_mul, hω.supportProj_isHermitian.eq,
      hρ.isHermitian.eq] using hadj
  calc
    V * (Vᴴ * ρ * V) * Vᴴ = (V * Vᴴ) * ρ * (V * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = hω.supportProj * ρ * hω.supportProj := by rw [hRange]
    _ = ρ := by rw [hleft, hright]

end Matrix

namespace TNLean

noncomputable section

variable {D k : ℕ}

private theorem supportCompression_log
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef)
    (V : Matrix (Fin D) (Fin k) ℂ) (hV : Vᴴ * V = 1)
    (hexpand : V * (Vᴴ * A * V) * Vᴴ = A) :
    CFC.log A = V * CFC.log (Vᴴ * A * V) * Vᴴ := by
  let Ac := Vᴴ * A * V
  have hAc : Ac.PosSemidef := by
    simpa only [Ac, Matrix.conjTranspose_conjTranspose] using
      hA.mul_mul_conjTranspose_same Vᴴ
  calc
    CFC.log A = CFC.log (V * Ac * Vᴴ) := congrArg CFC.log hexpand.symm
    _ = V * CFC.log Ac * Vᴴ := by
      rw [CFC.log, CFC.log]
      exact Matrix.cfc_conj_isometry_of_zero hAc.isHermitian
        Real.log Real.log_zero V hV

private theorem supportCompression_rpow
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef)
    (s : ℝ) (hs : s ≠ 0) (V : Matrix (Fin D) (Fin k) ℂ)
    (hV : Vᴴ * V = 1) (hexpand : V * (Vᴴ * A * V) * Vᴴ = A) :
    A ^ s = V * (Vᴴ * A * V) ^ s * Vᴴ := by
  have hAc : (Vᴴ * A * V).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hA.mul_mul_conjTranspose_same Vᴴ
  calc
    A ^ s = (V * (Vᴴ * A * V) * Vᴴ) ^ s := congrArg (fun X => X ^ s) hexpand.symm
    _ = cfc (fun x : ℝ => x ^ s) (V * (Vᴴ * A * V) * Vᴴ) := by
      rw [CFC.rpow_eq_cfc_real]
    _ = V * cfc (fun x : ℝ => x ^ s) (Vᴴ * A * V) * Vᴴ :=
      Matrix.cfc_conj_isometry_of_zero hAc.isHermitian
        (fun x : ℝ => x ^ s) (Real.zero_rpow hs) V hV
    _ = V * (Vᴴ * A * V) ^ s * Vᴴ := by
      rw [CFC.rpow_eq_cfc_real hAc.nonneg]

/-- Quantum relative entropy is unchanged by compression to the support of its
positive-semidefinite reference.  The kernel inclusion is exactly the finite
relative-entropy support condition; no faithfulness assumption is made on the
ambient reference. -/
theorem quantumRelativeEntropy_support_compression
    {ρ ω : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hker : ∀ v : Fin D → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (V : Matrix (Fin D) (Fin k) ℂ) (hV : Vᴴ * V = 1)
    (hRange : V * Vᴴ = hω.supportProj) :
    quantumRelativeEntropy ρ ω =
      quantumRelativeEntropy (Vᴴ * ρ * V) (Vᴴ * ω * V) := by
  let ρc := Vᴴ * ρ * V
  let ωc := Vᴴ * ω * V
  have hρexpand : V * ρc * Vᴴ = ρ := by
    simpa only [ρc] using
      hρ.eq_isometry_expansion_compression_of_kernel_le hω hker V hRange
  have hωexpand : V * ωc * Vᴴ = ω := by
    simpa only [ωc] using
      hω.eq_isometry_expansion_compression_of_kernel_le hω
        (fun _ hv => hv) V hRange
  have hlogρ : CFC.log ρ = V * CFC.log ρc * Vᴴ :=
    supportCompression_log hρ V hV hρexpand
  have hlogω : CFC.log ω = V * CFC.log ωc * Vᴴ :=
    supportCompression_log hω V hV hωexpand
  change quantumRelativeEntropy ρ ω = quantumRelativeEntropy ρc ωc
  rw [quantumRelativeEntropy, quantumRelativeEntropy]
  rw [hlogρ, hlogω, ← hρexpand]
  have hmatrix :
      (V * ρc * Vᴴ) *
          (V * CFC.log ρc * Vᴴ - V * CFC.log ωc * Vᴴ) =
        V * (ρc * (CFC.log ρc - CFC.log ωc)) * Vᴴ := by
    let φ := Matrix.isometryConjNonUnitalStarAlgHom V hV
    change φ ρc * (φ (CFC.log ρc) - φ (CFC.log ωc)) =
      φ (ρc * (CFC.log ρc - CFC.log ωc))
    rw [← map_sub, ← map_mul]
  rw [hmatrix, Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV]

/-- The order-two sandwiched trace functional is unchanged by compression to
the support of its positive-semidefinite reference under the support inclusion
$\ker\omega\subseteq\ker\rho$.  Negative quarter-powers use the zero-on-kernel
convention on both sides. -/
theorem sandwichedRenyiTwoTrace_support_compression
    {ρ ω : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hker : ∀ v : Fin D → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (V : Matrix (Fin D) (Fin k) ℂ) (hV : Vᴴ * V = 1)
    (hRange : V * Vᴴ = hω.supportProj) :
    sandwichedRenyiTwoTrace ρ ω =
      sandwichedRenyiTwoTrace (Vᴴ * ρ * V) (Vᴴ * ω * V) := by
  let ρc := Vᴴ * ρ * V
  let ωc := Vᴴ * ω * V
  have hρexpand : V * ρc * Vᴴ = ρ := by
    simpa only [ρc] using
      hρ.eq_isometry_expansion_compression_of_kernel_le hω hker V hRange
  have hωexpand : V * ωc * Vᴴ = ω := by
    simpa only [ωc] using
      hω.eq_isometry_expansion_compression_of_kernel_le hω
        (fun _ hv => hv) V hRange
  have hq : ω ^ (-(1 / 4 : ℝ)) = V * ωc ^ (-(1 / 4 : ℝ)) * Vᴴ :=
    supportCompression_rpow hω (-(1 / 4 : ℝ)) (by norm_num) V hV hωexpand
  change sandwichedRenyiTwoTrace ρ ω = sandwichedRenyiTwoTrace ρc ωc
  rw [sandwichedRenyiTwoTrace, sandwichedRenyiTwoTrace]
  change (Matrix.trace
      ((ω ^ (-(1 / 4 : ℝ)) * ρ * ω ^ (-(1 / 4 : ℝ))) *
        (ω ^ (-(1 / 4 : ℝ)) * ρ * ω ^ (-(1 / 4 : ℝ))))).re =
    (Matrix.trace
      ((ωc ^ (-(1 / 4 : ℝ)) * ρc * ωc ^ (-(1 / 4 : ℝ))) *
        (ωc ^ (-(1 / 4 : ℝ)) * ρc * ωc ^ (-(1 / 4 : ℝ))))).re
  rw [← hρexpand, hq]
  let q := ωc ^ (-(1 / 4 : ℝ))
  let φ := Matrix.isometryConjNonUnitalStarAlgHom V hV
  have hsandwich :
      (V * q * Vᴴ) * (V * ρc * Vᴴ) * (V * q * Vᴴ) =
        V * (q * ρc * q) * Vᴴ := by
    change φ q * φ ρc * φ q = φ (q * ρc * q)
    rw [← map_mul, ← map_mul]
  rw [hsandwich]
  have hsquare :
      (V * (q * ρc * q) * Vᴴ) * (V * (q * ρc * q) * Vᴴ) =
        V * ((q * ρc * q) * (q * ρc * q)) * Vᴴ := by
    change φ (q * ρc * q) * φ (q * ρc * q) =
      φ ((q * ρc * q) * (q * ρc * q))
    rw [← map_mul]
  rw [hsquare, Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV]

/-- A faithful-reference density-operator proof of
$D(\rho\Vert\omega)\leq\log Q_2(\rho,\omega)$ reduces the support-restricted
case to the support compression.  Both ambient matrices have trace one, and
isometric trace preservation supplies the corresponding normalizations for
the compressed matrices.  The faithful inequality is an explicit hypothesis
and is not proved here. -/
theorem quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_of_faithful
    {ρ ω : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hρtr : ρ.trace = 1) (hωtr : ω.trace = 1)
    (hker : ∀ v : Fin D → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (hfaithful : ∀ {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ),
      A.PosSemidef → B.PosDef → A.trace = 1 → B.trace = 1 →
        quantumRelativeEntropy A B ≤ Real.log (sandwichedRenyiTwoTrace A B)) :
    quantumRelativeEntropy ρ ω ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) := by
  obtain ⟨k, V, hV, hRange⟩ := hω.isOrthogonalProjection_supportProj.exists_range_isometry
  let ρc := Vᴴ * ρ * V
  let ωc := Vᴴ * ω * V
  have hρc : ρc.PosSemidef := by
    simpa only [ρc, Matrix.conjTranspose_conjTranspose] using
      hρ.mul_mul_conjTranspose_same Vᴴ
  have hωc : ωc.PosDef := by
    simpa only [ωc, Matrix.conjTranspose_conjTranspose] using
      hω.compression_on_support_posDef (V := Vᴴ) (by
        simpa only [Matrix.conjTranspose_conjTranspose] using hV) (by
        simpa only [Matrix.conjTranspose_conjTranspose] using hRange)
  have hρexpand : V * ρc * Vᴴ = ρ := by
    simpa only [ρc] using
      hρ.eq_isometry_expansion_compression_of_kernel_le hω hker V hRange
  have hωexpand : V * ωc * Vᴴ = ω := by
    simpa only [ωc] using
      hω.eq_isometry_expansion_compression_of_kernel_le hω
        (fun _ hv => hv) V hRange
  have hρctr : ρc.trace = 1 := by
    calc
      ρc.trace = (V * ρc * Vᴴ).trace :=
        (Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV ρc).symm
      _ = ρ.trace := congrArg Matrix.trace hρexpand
      _ = 1 := hρtr
  have hωctr : ωc.trace = 1 := by
    calc
      ωc.trace = (V * ωc * Vᴴ).trace :=
        (Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV ωc).symm
      _ = ω.trace := congrArg Matrix.trace hωexpand
      _ = 1 := hωtr
  have hcompressed := hfaithful ρc ωc hρc hωc hρctr hωctr
  calc
    quantumRelativeEntropy ρ ω = quantumRelativeEntropy ρc ωc :=
      quantumRelativeEntropy_support_compression hρ hω hker V hV hRange
    _ ≤ Real.log (sandwichedRenyiTwoTrace ρc ωc) := hcompressed
    _ = Real.log (sandwichedRenyiTwoTrace ρ ω) := congrArg Real.log
      (sandwichedRenyiTwoTrace_support_compression hρ hω hker V hV hRange).symm

end

end TNLean
