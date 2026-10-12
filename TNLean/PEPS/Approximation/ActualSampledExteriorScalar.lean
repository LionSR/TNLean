/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NoneSourceWordScalar
import TNLean.PEPS.Approximation.SampledEndpointExteriorIdentity
import TNLean.PEPS.Approximation.SelectedFamilyPhysicalBasis
import TNLean.PEPS.Approximation.BasisMatrixOperator
import QICLean.Channel.PartialTrace

/-!
# The actual exterior scalar in a sampled local trace

The exterior restriction of the prepared source word is multiplication by the
original empty-gate scalar. The sampled endpoint word is the identity on this
empty memory. Arbitrary orthonormal input and output coordinates therefore
give the same reduced exterior matrix, equal to the squared modulus of that
scalar times the identity on the singleton physical coordinate. No scalar is
cancelled, and no additional physical register is introduced.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect

private theorem empty_memory_mixed_partialTrace
    {Q I J : Type} [Fintype I] [Fintype J] {a b : Layout Q}
    (ha : a = []) (hb : b = [])
    (B : OrthonormalBasis I ℂ (Mem a))
    (C : OrthonormalBasis (PUnit × J) ℂ (Mem b))
    (A T : Mem a →L[ℂ] Mem b) (U : Mem a →L[ℂ] Mem a) (α β : ℂ)
    (hA : HEq A (α • ContinuousLinearMap.id ℂ ℂ))
    (hT : HEq T (β • ContinuousLinearMap.id ℂ ℂ))
    (hU : HEq U (ContinuousLinearMap.id ℂ ℂ)) :
    Matrix.partialTraceRight
        (Matrix.of (fun row col ↦ C.repr (A (B col)) row) *
          Matrix.of (fun row col ↦ B.repr (U (B col)) row) *
          (Matrix.of (fun row col ↦ C.repr (T (B col)) row))ᴴ) =
      (α * conj β) • (1 : Matrix PUnit PUnit ℂ) := by
  classical
  cases ha
  cases hb
  rw [eq_of_heq hA, eq_of_heq hT, eq_of_heq hU]
  let V := C.toBasis.toMatrix B
  have hScalar (γ : ℂ) :
      Matrix.of (fun row col ↦ C.repr ((γ • ContinuousLinearMap.id ℂ ℂ) (B col)) row) =
        γ • V := by
    rw [matrix_repr_eval_eq_toMatrix]
    change LinearMap.toMatrix B.toBasis C.toBasis (γ • LinearMap.id) = γ • V
    simp only [map_smul, LinearMap.toMatrix_id_eq_basis_toMatrix,
      OrthonormalBasis.coe_toBasis, V]
  have hIdentity : Matrix.of (fun row col ↦
      B.repr ((ContinuousLinearMap.id ℂ ℂ) (B col)) row) = (1 : Matrix I I ℂ) := by
    rw [matrix_repr_eval_eq_toMatrix]
    exact LinearMap.toMatrix_id B.toBasis
  have hV : V * Vᴴ = 1 := C.toMatrix_orthonormalBasis_self_mul_conjTranspose B
  have hJ : Fintype.card J = 1 := by
    simpa only [Module.finrank_self, Fintype.card_prod, Fintype.card_punit, one_mul] using
      (Module.finrank_eq_card_basis C.toBasis).symm
  rw [hScalar, hScalar, hIdentity, Matrix.mul_one, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, hV, smul_smul,
    Matrix.partialTraceRight_smul, Matrix.partialTraceRight_one, hJ]
  simp only [Nat.cast_one, one_smul, Complex.star_def]

namespace SourceCircuit
variable {P : Type} {a b : Layout P}

/-- The actual exterior sampled mixed trace is the original empty-gate scalar
times its complex conjugate, in the canonical singleton physical coordinate.
The input and output orthonormal bases, ket and bra choices, and original joint
sample are arbitrary. No normalization or nonvanishing is required.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267 and 565–588. -/
theorem partialSourceWord_sampled_none_partialTrace_eq_scalar
    (w : SourceCircuit a b) (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k)
    {I J : Type} [Fintype I] [Fintype J]
    (B : OrthonormalBasis I ℂ
      (Mem (Layout.atParty none (w.allResidualSourceLayout ++ []))))
    (C : OrthonormalBasis (PUnit × J) ℂ
      (Mem (Layout.atParty none (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)))) :
    Matrix.partialTraceRight
        (Matrix.of (fun row col ↦ C.repr
          (((w.partialSourceWord ψ ξ).restrict (partySelector none)
            (sources_partialSourceWord w ψ ξ)).eval (B col)) row) *
          Matrix.of (fun row col ↦ B.repr
            (((sampledEndpointInputWord w k lam L R ξ ζ j ω).restrict (partySelector none)
              (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).eval (B col)) row) *
          (Matrix.of (fun row col ↦ C.repr
            (((w.partialSourceWord ψ ζ).restrict (partySelector none)
              (sources_partialSourceWord w ψ ζ)).eval (B col)) row))ᴴ) =
      (w.emptyGateScalar * conj w.emptyGateScalar) • (1 : Matrix PUnit PUnit ℂ) := by
  classical
  have ha : Layout.atParty none (w.allResidualSourceLayout ++ []) = [] := by
    change Layout.restrict (partySelector none) (w.allResidualSourceLayout ++ []) = []
    rw [partySelector_none, Layout.restrict_append, restrict_allResidualSourceLayout_isNone,
      Layout.restrict_nil, List.nil_append]
  have hξ : HEq (((w.partialSourceWord ψ ξ).restrict (partySelector none)
      (sources_partialSourceWord w ψ ξ)).eval)
      (w.emptyGateScalar • ContinuousLinearMap.id ℂ ℂ) := by
    simpa only [partySelector_none] using
      restrict_partialSourceWord_all_eval_heq_emptyGateScalar w ψ ξ
  have hζ : HEq (((w.partialSourceWord ψ ζ).restrict (partySelector none)
      (sources_partialSourceWord w ψ ζ)).eval)
      (w.emptyGateScalar • ContinuousLinearMap.id ℂ ℂ) := by
    simpa only [partySelector_none] using
      restrict_partialSourceWord_all_eval_heq_emptyGateScalar w ψ ζ
  have hU : HEq ((sampledEndpointInputWord w k lam L R ξ ζ j ω).restrict (partySelector none)
      (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).eval
      (ContinuousLinearMap.id ℂ ℂ) := by
    simpa only [partySelector_none] using
      sampledEndpointInputWord_none_eval_heq_id w k lam L R ξ ζ j ω
  exact empty_memory_mixed_partialTrace ha (Layout.atParty_none_mapOwner_all b) B C
    ((w.partialSourceWord ψ ξ).restrict (partySelector none)
      (sources_partialSourceWord w ψ ξ)).eval
    ((w.partialSourceWord ψ ζ).restrict (partySelector none)
      (sources_partialSourceWord w ψ ζ)).eval
    ((sampledEndpointInputWord w k lam L R ξ ζ j ω).restrict (partySelector none)
      (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).eval
    w.emptyGateScalar w.emptyGateScalar hξ hζ hU

end SourceCircuit
end TNLean.PEPS.PairEffect
