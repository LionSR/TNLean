/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.FromSpectral
import QICLean.Channel.Peripheral.GroupStructure
import QICLean.Channel.Peripheral.JordanBlocks
import QICLean.Channel.Peripheral.SpectralRadius
import TNLean.MPS.Defs
import QICLean.Kraus.Transfer

/-!
# Peripheral spectrum of a one-block unital canonical tensor

The three conditions of the TI canonical form imply irreducibility: the
transfer map is unital, has a faithful adjoint fixed point, and its fixed
matrices are scalar multiples of the identity. Its peripheral spectrum is
therefore cyclic. The number of peripheral eigenvalues determines the period;
the peripheral generalized eigenspaces are one-dimensional, so this count
does not discard algebraic multiplicities.

The positive adjoint fixed point need not be diagonal for these conclusions.
The diagonal representative in the source is a specialization.

## References

PGVWC07, arXiv:quant-ph/0608197, Theorems 4 and 5, `Th:TIcanonical` and
`Th:periodic`, source lines 740–766 and 849–880.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-- The printed one-block unital canonical hypotheses imply irreducibility of
the actual transfer map; irreducibility is not an extra source hypothesis.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 4 and the proof of
Theorem 5, source lines 740–766 and 860–868. -/
theorem isIrreducible_transferMap_of_unital_canonical
    (A : MPSTensor d D) (hU : ∑ i, A i * (A i)ᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hUnique : ∀ X, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1) :
    IsIrreducibleMap (Kraus.transferMap A) := by
  have hOne : Kraus.transferMap A 1 = 1 := by
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hU
  apply isIrreducibleMap_of_hasSpectralProperties
  refine ⟨{
    n := d
    K := A
    map_eq := rfl
    ρ := 1
    σ := Λ
    r := 1
    ρ_posDef := Matrix.PosDef.one
    σ_posDef := hΛ
    hr_pos := zero_lt_one
    right_eig := ?_
    left_eig := ?_
    unique_psd_eigenvector := ?_
    spectralRadius_eq := ?_ }⟩
  · simpa only [Complex.ofReal_one, one_smul] using hOne
  · simpa only [Complex.ofReal_one, one_smul] using hΛfix
  · intro X _ hX
    exact hUnique X (by simpa only [Complex.ofReal_one, one_smul] using hX)
  · simpa only [ENNReal.ofReal_one] using
      (Kraus.isPositiveMap_mapLM A).spectralRadius_eq_one_of_map_one_eq_one hOne

/-- The peripheral eigenvalue count in PGVWC07 Theorem 5 supplies a positive
period and a primitive generator of the actual unital transfer spectrum.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 5, lines 849–868. -/
theorem exists_peripheral_generator_of_unital_canonical
    (A : MPSTensor d D) (hU : ∑ i, A i * (A i)ᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hUnique : ∀ X, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1)
    (p : ℕ) (hp : (peripheralEigenvalues (Kraus.transferMap A)).ncard = p) :
    0 < p ∧ ∃ γ : ℂ, IsPrimitiveRoot γ p ∧
      peripheralEigenvalues (Kraus.transferMap A) =
        Set.range (fun k : Fin p => γ ^ k.val) := by
  have hIrr := isIrreducible_transferMap_of_unital_canonical A hU Λ hΛ hΛfix hUnique
  obtain ⟨m, γ, hm, hγ, hper⟩ :=
    PeripheralSpectrum.peripheral_eigenvalues_cyclic_structure A hU Λ hΛ
      (by simpa only [Kraus.adjointMap_apply, Kraus.transferMap_apply,
        Matrix.conjTranspose_conjTranspose] using hΛfix) hIrr
  have hper' : peripheralEigenvalues (Kraus.transferMap A) =
      Set.range (fun k : Fin m => γ ^ k.val) := by
    rw [hper]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_range, eq_comm]
  have hinj : Function.Injective (fun k : Fin m => γ ^ k.val) := by
    intro i j hij
    exact Fin.ext (hγ.pow_inj i.isLt j.isLt hij)
  have hmp : m = p := by
    rw [hper', Set.ncard_range_of_injective hinj, Nat.card_fin] at hp
    exact hp
  subst m
  exact ⟨hm, γ, hγ, hper'⟩

/-- Every peripheral eigenvalue of a one-block unital canonical tensor has
algebraic multiplicity one: its maximal generalized eigenspace is a line.

Source: the peripheral spectral structure invoked in PGVWC07,
arXiv:quant-ph/0608197, proof of Theorem 5, lines 860–868. -/
theorem peripheral_genEigenspace_finrank_eq_one_of_unital_canonical
    (A : MPSTensor d D) (hU : ∑ i, A i * (A i)ᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hUnique : ∀ X, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1)
    {μ : ℂ} (hμ : μ ∈ peripheralEigenvalues (Kraus.transferMap A)) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (Kraus.transferMap A) μ) = 1 := by
  have hOne : Kraus.transferMap A 1 = 1 := by
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hU
  have hSpace : Module.End.maxGenEigenspace (Kraus.transferMap A) μ =
      Module.End.eigenspace (Kraus.transferMap A) μ := by
    apply le_antisymm
    · intro X hX
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hX
      have h := IsPositiveMap.peripheral_Jordan_trivial_of_unital
        (Kraus.isPositiveMap_mapLM A) hOne μ hμ.2 k X hk
      exact Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp (by simpa using h))
    · exact Module.End.eigenspace_le_maxGenEigenspace
  rw [hSpace]
  exact PeripheralSpectrum.peripheral_eigenvalue_multiplicity_one A hU Λ hΛ
    (by simpa only [Kraus.adjointMap_apply, Kraus.transferMap_apply,
      Matrix.conjTranspose_conjTranspose] using hΛfix)
    (isIrreducible_transferMap_of_unital_canonical A hU Λ hΛ hΛfix hUnique) hμ

end MPSTensor
