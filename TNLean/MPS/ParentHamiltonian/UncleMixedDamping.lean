/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleBoundaryWords
import QICLean.Channel.Schwarz.Basic
import QICLean.Channel.Peripheral.UnitalKraus
import QICLean.Kraus.MixedMap.SpectralRadius
import QICLean.Analysis.OperatorMean.BlockDiagonal
import QICLean.Analysis.SpectralRadiusPowerDecay

/-!
# Mixed damping from full source perturbation span

The full perturbation span separates the two diagonal blocks. A peripheral
mixed eigenvector would intertwine their adjoint letters, by equality in
the weighted Schwarz inequality for the block-diagonal channel. Contracting
that identity with coefficients isolating one block forces the vector to
vanish. Thus strict mixed damping follows from the source span and canonical
normalization; it is not an additional spectral assumption. The
conclusion is \(r(\mathcal E_{AB})<1\) for the mixed transfer map
\(\mathcal E_{AB}(X)=\sum_iA_iXB_i^\dagger\), and likewise
\(r(\mathcal E_{BA})<1\).

This is not a formalization of the source's Lemma offdiagonal-damping
(lines 1175–1177), which derives the same bound from block injectivity of the
unperturbed diagonal blocks alone. The hypothesis here is full span of the
perturbed letters, which suffices for the two-wall trial argument.

Source: arXiv:1210.6613, Lemma exptransferoperator and the normalized
two-block setting of Lemma lowenergystates, lines 1165–1265.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace ENNReal

namespace MPSTensor

variable {d a b : ℕ}

private theorem uncleBoundary_separating_coefficients
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) :
    ∃ c : Fin d → ℂ, (∑ i, c i • (A i)ᴴ) = 0 ∧ (∑ i, c i • (B i)ᴴ) = 1 := by
  classical
  have hmem : uncleBlockMatrix (a := a) (b := b) 0 0 0 1 ∈
      Submodule.span ℂ (Set.range (uncleBoundaryLetter A B R L)) := by
    rw [hPert.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  have hA : ∑ i, c i • A i = 0 := by
    ext j k
    have h := congrArg (fun M ↦ M (e (Sum.inl j)) (e (Sum.inl k))) hc
    simpa [e, Matrix.sum_apply, uncleBoundaryLetter, uncleBlockMatrix,
      Matrix.reindex_apply] using h
  have hB : ∑ i, c i • B i = 1 := by
    ext j k
    have h := congrArg (fun M ↦ M (e (Sum.inr j)) (e (Sum.inr k))) hc
    simpa [e, Matrix.sum_apply, uncleBoundaryLetter, uncleBlockMatrix,
      Matrix.reindex_apply] using h
  refine ⟨fun i ↦ star (c i), ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hA
  · simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose hB

/-- The full perturbation span and unital canonical blocks imply
strict mixed-transfer damping. Faithful stationary dual densities suffice;
their trace normalization is not needed for this implication.
Source: arXiv:1210.6613, Lemma exptransferoperator. -/
theorem uncleBoundaryLetter_mixedMapSpectralRadius_lt_one [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L))
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB) :
    Kraus.mixedMapSpectralRadius A B < 1 := by
  classical
  let K : Fin d → Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ :=
    fun i ↦ Matrix.fromBlocks (A i) 0 0 (B i)
  let ρ : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ :=
    Matrix.fromBlocks ρA 0 0 ρB
  have hKA : ∑ i, A i * (A i)ᴴ = 1 := by
    simpa only [Kraus.mapLM_apply, Kraus.map_apply, Matrix.mul_one] using hUA
  have hKB : ∑ i, B i * (B i)ᴴ = 1 := by
    simpa only [Kraus.mapLM_apply, Kraus.map_apply, Matrix.mul_one] using hUB
  have hKU : Kraus.IsUnital K := by
    change (∑ i, K i * (K i)ᴴ) = 1
    have hsum : (∑ i, K i * (K i)ᴴ) = Matrix.fromBlocks
        (∑ i, A i * (A i)ᴴ) 0 0 (∑ i, B i * (B i)ᴴ) := by
      ext (i | i) (j | j) <;>
        simp [K, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    rw [hsum, hKA, hKB, Matrix.fromBlocks_one]
  have hρ : ρ.PosDef := hρA.fromBlocks_diag hρB
  have hF : Kraus.adjointMap K ρ = ρ := by
    have hsum : Kraus.adjointMap K ρ = Matrix.fromBlocks
        (Kraus.adjointMap A ρA) 0 0 (Kraus.adjointMap B ρB) := by
      ext (i | i) (j | j) <;>
        simp [Kraus.adjointMap, K, ρ, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    rw [hsum, hFA, hFB]
  have hCP := Matrix.rectangularKrausMap_isKrausCP K
  have hOne : Matrix.rectangularKrausMap K 1 = 1 := by
    change (∑ i, K i * 1 * (K i)ᴴ) = 1
    simpa only [Kraus.IsUnital, Matrix.mul_one] using hKU
  unfold Kraus.mixedMapSpectralRadius
  apply spectralRadius_lt_one_of_eigenvalues_lt_one
  intro μ hμ
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hEX : Kraus.mixedMapLM A B X = μ • X :=
    Module.End.mem_eigenspace_iff.mp hX.1
  let M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := Matrix.fromBlocks 0 X 0 0
  have hEM : Kraus.map K M = μ • M := by
    have hsum : Kraus.map K M = Matrix.fromBlocks 0 (Kraus.mixedMapLM A B X) 0 0 := by
      ext (i | i) (j | j) <;>
        simp [Kraus.map, Kraus.mixedMapLM_apply, K, M, Matrix.sum_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    rw [hsum, hEX]
    ext (i | i) (j | j) <;> simp [M]
  have hMne : M ≠ 0 := by
    intro hM
    apply hX.2
    ext i j
    exact congrArg (fun T ↦ T (Sum.inl i) (Sum.inr j)) hM
  have hEK : Module.End.HasEigenvalue (Matrix.rectangularKrausMap K) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hEM, hMne⟩
  have hle := hCP.eigenvalue_norm_le_one_of_map_one_eq_one hOne μ hEK
  by_contra hn
  have hnorm : ‖μ‖ = 1 := le_antisymm hle (le_of_not_gt hn)
  have hKS := Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
    K hKU hρ hF M μ hEM hnorm
  have hComm := Kraus.kraus_commute_of_ks_equality K hKU M hKS
  have hInter (i : Fin d) : X * (B i)ᴴ = μ • ((A i)ᴴ * X) := by
    ext j k
    have h := congrArg (fun T ↦ T (Sum.inl j) (Sum.inr k)) (hComm i)
    rw [hEM] at h
    simpa [K, M, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] using h
  obtain ⟨c, hcA, hcB⟩ := uncleBoundary_separating_coefficients A B R L hPert
  have hzero : X = 0 := by
    calc
      X = X * (∑ i, c i • (B i)ᴴ) := by rw [hcB, Matrix.mul_one]
      _ = ∑ i, c i • (X * (B i)ᴴ) := by
        rw [Matrix.mul_sum]
        simp_rw [Matrix.mul_smul]
      _ = ∑ i, c i • (μ • ((A i)ᴴ * X)) := by simp_rw [hInter]
      _ = μ • ((∑ i, c i • (A i)ᴴ) * X) := by
        rw [Matrix.sum_mul, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.smul_mul]
        exact smul_comm (c i) μ ((A i)ᴴ * X)
      _ = 0 := by rw [hcA, Matrix.zero_mul, smul_zero]
  exact hX.2 hzero

/-- Full source perturbation span also gives strict mixed damping in the
reverse orientation. The conjugate-transpose mixed eigenvector reduces
this to the preceding block-separation argument.
Source: arXiv:1210.6613, Lemma exptransferoperator. -/
theorem uncleBoundaryLetter_mixedMapSpectralRadius_reverse_lt_one [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L))
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB) :
    Kraus.mixedMapSpectralRadius B A < 1 := by
  have hgap := uncleBoundaryLetter_mixedMapSpectralRadius_lt_one
    A B R L hPert hUA hUB ρA hρA ρB hρB hFA hFB
  unfold Kraus.mixedMapSpectralRadius
  apply spectralRadius_lt_one_of_eigenvalues_lt_one
  intro μ hμ
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hEX : Kraus.mixedMapLM B A X = μ • X :=
    Module.End.mem_eigenspace_iff.mp hX.1
  have hEXstar : Kraus.mixedMapLM A B Xᴴ = star μ • Xᴴ := by
    have h := congrArg Matrix.conjTranspose hEX
    simpa only [Kraus.mixedMapLM_apply, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.mul_assoc] using h
  have hne : Xᴴ ≠ 0 := by
    intro h
    exact hX.2 (by simpa only [Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose h)
  have hEig : Module.End.HasEigenvalue (Kraus.mixedMapLM A B) (star μ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hEXstar, hne⟩
  have hSpec : star μ ∈ spectrum ℂ (Kraus.mixedMapLM A B) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp hEig
  have hQspec : star μ ∈ quasispectrum ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin a) (Fin b) ℂ))
        (Kraus.mixedMapLM A B)) := by
    apply spectrum_subset_quasispectrum ℂ _
    rw [AlgEquiv.spectrum_eq (R := ℂ)]
    exact hSpec
  have hbound : (‖star μ‖₊ : ℝ≥0∞) ≤ Kraus.mixedMapSpectralRadius A B := by
    unfold Kraus.mixedMapSpectralRadius spectralRadius
    exact le_iSup_of_le (star μ) (le_iSup_of_le hQspec le_rfl)
  have hlt := hbound.trans_lt hgap
  simpa only [norm_star] using (show ‖star μ‖ < 1 by exact_mod_cast hlt)

end MPSTensor
