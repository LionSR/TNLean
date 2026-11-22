/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceGateDensity
import QICLean.Analysis.Norm.KroneckerOperatorNorm

/-!
# Operator norms of prepared branches

Preparing normalized pair sources and then applying an allowed word is a
contraction. Its matrix in orthonormal input and output bases therefore has
Euclidean operator norm at most one. In particular, this holds for the operators
obtained by assigning a unit vector to every source half, including vectors
from an orthonormal family that spans only a proper subspace.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, source-gate expansion and source-entry separation,
lines 233–267 and 409–427.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.

## Density coefficients of an actual source-only gate

Starting from a finite family of allowed words, construct its common finite
source spaces and the remaining local operations. The density of the original
weighted gate is then the explicit sum of the source-coordinate coefficients
and the matrices obtained by preparing endpoint basis vectors. These prepared
matrices are contractions. The factorization and the coefficient operators are
constructed from the words.

This is the exact density identity preceding Gaussian source replacement. It
does not give the corrected-position error estimate, which must retain the
exterior aggregate gates as contractions.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, `eq:compression-source-gate` and the density-source
expansion, lines 233–355.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

section

noncomputable section

open scoped InnerProductSpace TensorProduct Matrix.Norms.L2Operator
open ContinuousLinearMap

namespace TNLean.Lattice.PartyCircuit.Word

/-- Normalized source preparation followed by allowed operations has matrix
operator norm at most one in any orthonormal input and output bases.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 409–427. -/
theorem norm_preparedMatrix_le_one {P m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) (hη : ∀ i, ‖η i‖ = 1) (ℓ : Layout P) {ℓ' : Layout P}
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ') (hv : v.IsAllowed)
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    ‖v.preparedMatrix R U V η ℓ bIn bOut‖ ≤ 1 := by
  classical
  let : DecidableEq n := Classical.decEq n
  have hp : (SourceInventory.prepareSlots R U V η ℓ).IsAllowed :=
    (isAllowed_castLayouts ((SourceInventory.ofSlots R U V η).prepare ℓ) rfl _).mpr
      ((SourceInventory.isAllowed_prepare_iff _ _).mpr
        (SourceInventory.isNormalized_ofSlots R U V η hη))
  change ‖LinearMap.toMatrix bIn.toBasis bOut.toBasis
    (v.eval.comp (SourceInventory.prepareSlots R U V η ℓ).eval).toLinearMap‖ ≤ 1
  exact (ContinuousLinearMap.norm_toMatrix_orthonormal
    (v.eval.comp (SourceInventory.prepareSlots R U V η ℓ).eval) bIn bOut).le.trans
      (norm_comp_le_one (v.norm_eval_le_one hv)
        ((SourceInventory.prepareSlots R U V η ℓ).norm_eval_le_one hp))

/-- Assigning a unit vector to each source half gives a contraction. This applies
both to orthonormal bases and to orthonormal families spanning proper subspaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_preparedMatrix_tmul_le_one {P m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type}
    (u : ∀ i, A i → U i) (v : ∀ i, B i → V i)
    (hu : ∀ i a, ‖u i a‖ = 1) (hv : ∀ i b, ‖v i b‖ = 1)
    (ℓ : Layout P) {ℓ' : Layout P}
    (w : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ') (hw : w.IsAllowed)
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (a : ∀ i, A i × B i) :
    ‖w.preparedMatrix R U V (fun i ↦ u i (a i).1 ⊗ₜ[ℂ] v i (a i).2)
      ℓ bIn bOut‖ ≤ 1 := by
  apply norm_preparedMatrix_le_one R U V _ _ ℓ w hw bIn bOut
  exact fun i ↦ (TensorProduct.norm_tmul _ _).trans (by rw [hu, hv, one_mul])

end TNLean.Lattice.PartyCircuit.Word
end

end

section

noncomputable section

open scoped ComplexConjugate TensorProduct Matrix Matrix.Norms.L2Operator

namespace TNLean
open TNLean.Lattice.PartyCircuit

namespace Lattice.PartyCircuit
/-- Construct the finite source coordinates and the exact density coefficients of
the original weighted gate. The elementary preparation operators are contractions,
and the ket and bra retain the coefficients `c ξ` and `conj (c ζ)`, respectively.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–355. -/
theorem Word.exists_finite_density_expansion {P ι m n : Type}
    [Finite P] [Fintype ι] [Fintype m] [Fintype n] [DecidableEq n]
    {ℓ ℓ' : Layout P} (w : ι → Word ℓ ℓ') (hw : ∀ ξ, (w ξ).IsAllowed)
    (c : ι → ℂ) (bIn : OrthonormalBasis n ℂ (Mem ℓ))
    (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    let M := fun ξ ↦ LinearMap.toMatrix bIn.toBasis bOut.toBasis (w ξ).eval.toLinearMap
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ a b : Fin R.length → ℕ,
        let U := fun i ↦ euc (Fin (a i))
        let V := fun i ↦ euc (Fin (b i))
        let bU := fun i ↦ EuclideanSpace.basisFun (Fin (a i)) ℂ
        let bV := fun i ↦ EuclideanSpace.basisFun (Fin (b i)) ℂ
        ∃ η : ι → ∀ i, U i ⊗[ℂ] V i, (∀ ξ i, ‖η ξ i‖ = 1) ∧
          ∃ v : ι → Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ',
            (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
            (∀ ξ, (w ξ).eval = (v ξ).eval ∘L
              (SourceInventory.prepareSlots R U V (η ξ) ℓ).eval) ∧
            (∀ ξ (x : ∀ i, Fin (a i) × Fin (b i)),
              ‖(v ξ).preparedMatrix R U V
                (fun i ↦ bU i (x i).1 ⊗ₜ[ℂ] bV i (x i).2) ℓ bIn bOut‖ ≤ 1) ∧
            ∀ ρ : Matrix n n ℂ,
              (∑ ξ, c ξ • M ξ) * ρ * (∑ ξ, c ξ • M ξ)ᴴ =
                ∑ ξ, ∑ ζ, (c ξ * conj (c ζ)) •
                  ∑ x : ∀ i, Fin (a i) × Fin (b i),
                    ∑ y : ∀ i, Fin (a i) × Fin (b i),
                      (∏ i, ((bU i).tensorProduct (bV i)).repr (η ξ i) (x i) *
                        conj (((bU i).tensorProduct (bV i)).repr (η ζ i) (y i))) •
                        (v ξ).preparedDensityCoefficient R U V
                          (fun i ↦ bU i) (fun i ↦ bV i)
                          (fun i ↦ bU i) (fun i ↦ bV i)
                          ℓ (v ζ) bIn bOut ρ x y := by
  classical
  dsimp only
  obtain ⟨R, hR, hRK, a, b, η, hη, v, hv, hvs, he⟩ :=
    Word.exists_finite_source_preparation w hw
  refine ⟨R, hR, hRK, a, b, η, hη, v, hv, hvs, he, ?_, ?_⟩
  · intro ξ x
    exact (v ξ).norm_preparedMatrix_tmul_le_one R
      (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i)))
      (fun i ↦ EuclideanSpace.basisFun (Fin (a i)) ℂ)
      (fun i ↦ EuclideanSpace.basisFun (Fin (b i)) ℂ)
      (fun i ↦ (EuclideanSpace.basisFun (Fin (a i)) ℂ).norm_eq_one)
      (fun i ↦ (EuclideanSpace.basisFun (Fin (b i)) ℂ).norm_eq_one)
      ℓ (hv ξ) bIn bOut x
  · intro ρ
    have hM ξ : LinearMap.toMatrix bIn.toBasis bOut.toBasis (w ξ).eval.toLinearMap =
        (v ξ).preparedMatrix R (fun i ↦ euc (Fin (a i)))
          (fun i ↦ euc (Fin (b i))) (η ξ) ℓ bIn bOut := by
      ext i j
      simp only [Word.preparedMatrix, LinearMap.toMatrix_apply, he ξ]
    simp only [hM]
    exact Word.preparedMatrix_gate_density_eq_sum_basis R
      (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i)))
      (fun _ i ↦ EuclideanSpace.basisFun (Fin (a i)) ℂ)
      (fun _ i ↦ EuclideanSpace.basisFun (Fin (b i)) ℂ)
      c η ℓ v bIn bOut ρ

end Lattice.PartyCircuit
end TNLean
end

end
