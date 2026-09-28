/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DiagonalPolar
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.Overlap.PeripheralToTransferMapGap

/-!
# One-dimensional normal blocks in a canonical form

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") write a tensor as `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ`
(eq. (S2)), where "the normal `A_j` are in canonical form II and produce orthogonal vectors in
the thermodynamic limit", with `|μ_{j,k}| ≤ 1` and at least one `|μ_{j,k}| = 1`. This file
collects the facts needed to check these hypotheses for a canonical form whose blocks have bond
dimension one, as in the two counterexamples to Lemma 1'(ii)
(`TNLean.MPS.Preparation.RepeatedBlockCounterexample`,
`TNLean.MPS.Preparation.OverlappingBlockCounterexample`).

A one-dimensional block `(a_i)` in the gauge `∑ᵢ |aᵢ|² = 1` of eq. `eq:Ek_decomp` has the identity
as transfer map. It is therefore a normal tensor (`isNormalTensor_of_dim_one`), left-canonical
(`isLeftCanonical_of_dim_one`), has the identity as a diagonal positive-definite fixed point, so it
is in canonical form II, and its normalized self-overlap tends to one
(`tendsto_mpvOverlap_self_of_dim_one`).

For the assembled tensor of a sector decomposition, the entries between the coordinates of two
distinct copies vanish (`SectorDecomposition.toTensor_copyCoord_of_ne`), and coordinates of
distinct copies are distinct (`SectorDecomposition.sigma_eq_of_copyCoord_eq`). These identify the
assembled tensor with a displayed tensor, coordinate by coordinate.

## Main declarations

* `MPSTensor.isNormalTensor_of_dim_one`, `MPSTensor.isLeftCanonical_of_dim_one`,
  `MPSTensor.posDef_isDiag_transferMap_one_of_dim_one`,
  `MPSTensor.tendsto_mpvOverlap_self_of_dim_one` — the clauses of eq. (S2) for a normalized
  one-dimensional block, whose transfer map is the identity
  (`MPSTensor.transferMap_eq_id_of_dim_one`).
* `MPSTensor.mpv_of_dim_one` — its coefficients are products of its entries.
* `MPSTensor.not_gaugePhaseEquiv_of_dim_one` — two such blocks with different zero patterns are
  distinct blocks of a basis of normal tensors.
* `MPSTensor.SectorDecomposition.toTensor_copyCoord_of_ne` — the assembled tensor is block
  diagonal in the coordinates of the copies.
* `MPSTensor.SectorDecomposition.sigma_eq_of_copyCoord_eq` — distinct copies occupy distinct
  bond coordinates.
* `MPSTensor.embedPair_symm_comp` — relabelling the bond coordinates of an embedded pair.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2) and `eq:Ek_decomp`.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ## One-dimensional blocks -/

/-- A one-dimensional tensor in the gauge `∑ᵢ |aᵢ|² = 1` is a normal tensor: the blocks `A_j`
of arXiv:2307.01696, eq. (S2), may be taken one-dimensional. -/
theorem isNormalTensor_of_dim_one (A : MPSTensor d 1)
    (hA : ∑ i, star (A i 0 0) * A i 0 0 = 1) : IsNormalTensor A :=
  isNormalTensor_of_bondDim_one_of_transferMap_eq_id A (transferMap_eq_id_of_dim_one A hA)

/-- A one-dimensional tensor in the gauge `∑ᵢ |aᵢ|² = 1` is left-canonical,
`∑ᵢ (Aⁱ)ᴴ Aⁱ = 1`, the first condition of canonical form II invoked in arXiv:2307.01696,
eq. (S2). -/
theorem isLeftCanonical_of_dim_one (A : MPSTensor d 1)
    (hA : ∑ i, star (A i 0 0) * A i 0 0 = 1) : IsLeftCanonical A := by
  change ∑ i, (A i)ᴴ * A i = 1
  ext a c
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : c = 0 := Subsingleton.elim _ _
  rw [Matrix.sum_apply]
  simpa [Matrix.mul_apply, conjTranspose_apply] using hA

/-- The identity is a diagonal positive-definite fixed point of the transfer map of a
one-dimensional tensor in the gauge `∑ᵢ |aᵢ|² = 1`: the second condition of canonical form II
invoked in arXiv:2307.01696, eq. (S2). -/
theorem posDef_isDiag_transferMap_one_of_dim_one (A : MPSTensor d 1)
    (hA : ∑ i, star (A i 0 0) * A i 0 0 = 1) :
    (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef ∧ (1 : Matrix (Fin 1) (Fin 1) ℂ).IsDiag ∧
      Kraus.transferMap A 1 = 1 :=
  ⟨PosDef.one, isDiag_one, by rw [transferMap_eq_id_of_dim_one A hA, LinearMap.id_apply]⟩

/-- The normalized self-overlap of a one-dimensional tensor in the gauge `∑ᵢ |aᵢ|² = 1` tends to
one, the normalization of the blocks of arXiv:2307.01696, eq. (S2). -/
theorem tendsto_mpvOverlap_self_of_dim_one (A : MPSTensor d 1)
    (hA : ∑ i, star (A i 0 0) * A i 0 0 = 1) :
    Tendsto (fun N : ℕ => mpvOverlap (d := d) A A N) atTop (𝓝 1) :=
  overlap_tendsto_one_of_peripheralPrimitive_of_irreducible A
    (isIrreducibleTensor_of_bondDim_one A) (isLeftCanonical_of_dim_one A hA)
    (isNormalTensor_of_dim_one A hA).primitive_transfer

/-- The coefficients of a one-dimensional tensor are the products of its entries along the
configuration: `⟨i₁⋯i_N|v⟩ = a_{i₁} ⋯ a_{i_N}` (arXiv:2307.01696, eq. `eq:TI-MPS2` for `D = 1`). -/
theorem mpv_of_dim_one (A : MPSTensor d 1) {N : ℕ} (σ : Fin N → Fin d) :
    mpv A σ = ∏ k, A (σ k) 0 0 := by
  have hA : A = fun i => diagonal (fun _ : Fin 1 => A i 0 0) := by
    funext i
    ext a c
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : c = 0 := Subsingleton.elim _ _
    simp
  rw [mpv_eq, coeff_eq, hA, evalWord_diagonal, trace_diagonal, Fin.sum_univ_one,
    List.map_ofFn, List.prod_ofFn]
  rfl

/-- Two one-dimensional tensors whose entries at some letter `i` are not both zero or both
nonzero are not related by a gauge transformation and a nonzero phase: for bond dimension one,
`Bⁱ = ζ X Aⁱ X⁻¹` reads `bᵢ = ζ aᵢ`. This separates distinct blocks `A_j` of the basis of
normal tensors in arXiv:2307.01696, eq. (S2). -/
theorem not_gaugePhaseEquiv_of_dim_one {A B : MPSTensor d 1} (i : Fin d)
    (h : ¬(A i 0 0 = 0 ↔ B i 0 0 = 0)) : ¬GaugePhaseEquiv A B := by
  rintro ⟨X, ζ, hζ, hX⟩
  have hinv : (X : Matrix (Fin 1) (Fin 1) ℂ) 0 0 *
      ((X⁻¹ : GL (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1 := by
    have := congrArg (fun U : GL (Fin 1) ℂ => (U : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
      (mul_inv_cancel X)
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one] at this
    simpa using this
  have hB : B i 0 0 = ζ * A i 0 0 := by
    rw [hX i, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply,
      Fin.sum_univ_one, smul_eq_mul]
    linear_combination ζ * A i 0 0 * hinv
  exact h ⟨fun hA => by rw [hB, hA, mul_zero], fun hB0 => by
    rw [hB] at hB0; exact (mul_eq_zero.1 hB0).resolve_left hζ⟩

/-! ## The coordinates of the copies in a sector decomposition -/

namespace SectorDecomposition

/-- Coordinates of the assembled tensor coming from two copies coincide only when the copies
coincide: the copies `μ_{j,k} A_j` of arXiv:2307.01696, eq. (S2), occupy disjoint bond
coordinates. -/
theorem sigma_eq_of_copyCoord_eq (P : SectorDecomposition d) {j j' : Fin P.basisCount}
    {k : Fin (P.copies j)} {k' : Fin (P.copies j')} {a : Fin (P.basisDim j)}
    {a' : Fin (P.basisDim j')} (h : P.copyCoord j k a = P.copyCoord j' k' a') :
    (⟨j, k⟩ : (j : Fin P.basisCount) × Fin (P.copies j)) = ⟨j', k'⟩ :=
  P.flatIndexEquiv.injective (Sigma.mk.inj_iff.1 (finSigmaFinEquiv.injective h)).1

/-- The assembled tensor vanishes between the coordinates of two distinct copies: it is the
direct sum `⊕_{(j,k)} μ_{j,k} A_j` of arXiv:2307.01696, eq. (S2). -/
theorem toTensor_copyCoord_of_ne (P : SectorDecomposition d) (i : Fin d)
    {j j' : Fin P.basisCount} {k : Fin (P.copies j)} {k' : Fin (P.copies j')}
    (h : (⟨j, k⟩ : (j : Fin P.basisCount) × Fin (P.copies j)) ≠ ⟨j', k'⟩)
    (a : Fin (P.basisDim j)) (a' : Fin (P.basisDim j')) :
    P.toTensor i (P.copyCoord j k a) (P.copyCoord j' k' a') = 0 := by
  simp only [toTensor, toTensorFromBlocks, copyCoord, reindex_apply, submatrix_apply,
    Equiv.symm_apply_apply]
  exact blockDiagonal'_apply_ne _ _ _ fun h' => h (P.flatIndexEquiv.injective h')

end SectorDecomposition

/-- Relabelling the bond coordinates by an equivalence `e` relabels an embedded pair:
`(e⁻¹ ∘ ι)_* ω` at `p` is `ι_* ω` at `(e p₁, e p₂)`. -/
theorem embedPair_symm_comp {D D' n : ℕ} (e : Fin D ≃ Fin D') (ι : Fin n → Fin D')
    (ω : Fin n × Fin n → ℂ) (p : Fin D × Fin D) :
    embedPair (fun a => e.symm (ι a)) ω p = embedPair ι ω (e p.1, e p.2) := by
  simp only [embedPair, Prod.ext_iff, Equiv.symm_apply_eq]

end MPSTensor
