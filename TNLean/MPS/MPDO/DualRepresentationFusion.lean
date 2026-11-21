/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PreBialgebra
import TNLean.MPS.MPDO.WeakHopfRepresentation
import TNLean.MPS.MPDO.BoundaryBlockFusion
import TNLean.MPS.MPDO.BoundaryZipper
import TNLean.MPS.MPDO.BiCFDerivation.Core
import TNLean.MPS.MPDO.CompleteZipperFusionCoassoc
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Complete zipper fusion from a cosemisimple pre-bialgebra

A faithful unital physical representation and a matrix-block decomposition of
the convolution dual give a complete zipper fusion family at the original
physical alphabet. Multiplicativity of the represented iterated coproduct
implies arbitrary-boundary closedness. The existing representation theorem
then constructs exact biorthogonal fusion tensors. Faithfulness supplies the
simultaneous one-letter inverse, without physical blocking.

Cosemisimplicity is essential here: the source assumes it in Section 4.1.
The final existence theorem obtains the matrix-block decomposition from
Mathlib's Wedderburn--Artin theorem. No fusion tensors, left inverses, or
counit witnesses are hypotheses.

## References

* Molnár et al., arXiv:2204.05940, Section 4.1, lines 1640--1658,
  equations `eq:irrep_product_decomposition` and `eq:splitting_algebraic`.
-/

open scoped Matrix BigOperators
open WithConv

noncomputable section

namespace MPOTensor

variable {H : Type*} [Ring H] [Algebra ℂ H] [PreBialgebra ℂ H]
  [FiniteDimensional ℂ H] {p D r : ℕ}

/-- A faithful dual representation of a pre-bialgebra is closed under products
with one output boundary for all positive lengths. Source: arXiv:2204.05940,
Section 4. No semisimplicity or physical faithfulness is needed here. -/
theorem isBoundaryClosed_ofDualRepresentation
    (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) : IsBoundaryClosed (ofDualRepresentation φ.toLinearMap ψ) := by
  intro X Y
  obtain ⟨x, hx⟩ := exists_weakHopfRep_eq_mpoWithBoundary φ.toLinearMap ψ X
  obtain ⟨y, hy⟩ := exists_weakHopfRep_eq_mpoWithBoundary φ.toLinearMap ψ Y
  obtain ⟨Z, hZ⟩ := exists_mpoWithBoundary_eq_weakHopfRep φ.toLinearMap ψ hψ (x * y)
  exact ⟨Z, fun n hn ↦ by rw [hx, hy, hZ, weakHopfRep_mul PreBialgebra.comul_mul φ hn]⟩

namespace DualRepresentationFusion

variable {δ : Fin r → ℕ}

/-- The direct sum of the simple dual representations, in flattened bond
coordinates. Source: arXiv:2204.05940, Section 3.1 and Section 4.1. -/
def totalRepresentation
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ) :
    WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ]
      Matrix (Fin (∑ c, δ c)) (Fin (∑ c, δ c)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ finSigmaFinEquiv).toAlgHom.comp
    ({ toRingHom := (Matrix.blockDiagonal'RingHom (fun c ↦ Fin (δ c)) ℂ).comp
        ψ.toAlgHom.toRingHom
       commutes' := by
         intro z
         change Matrix.blockDiagonal' (ψ (algebraMap ℂ _ z)) = _
         simp [Algebra.algebraMap_eq_smul_one, Matrix.blockDiagonal'_smul] } :
      WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ]
        Matrix ((c : Fin r) × Fin (δ c)) ((c : Fin r) × Fin (δ c)) ℂ)

omit [FiniteDimensional ℂ H] in
/-- The direct sum contains every simple dual block and is faithful. -/
theorem totalRepresentation_injective
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ) :
    Function.Injective (totalRepresentation ψ) :=
  (Matrix.reindexAlgEquiv ℂ ℂ finSigmaFinEquiv).injective.comp
    (Matrix.blockDiagonal'_injective.comp ψ.injective)

/-- The one-site block letters obtained by evaluating physical coefficients
in each simple dual representation. Source: arXiv:2204.05940, Sections 3.1, 4.1. -/
def tensor (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ)
    (c : Fin r) : MPOTensor p (δ c) :=
  fun i k ↦ ψ (dualCoefficient φ.toLinearMap i k) c

/-- Faithfulness of the physical representation gives simultaneous spanning
at length one, not merely individual block injectivity. Source:
arXiv:2204.05940, Section 3.1, lines 1180--1184. -/
theorem wordTupleSpanTop_tensor
    (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ) (hφ : Function.Injective φ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ) :
    MPSTensor.WordTupleSpanTop (fun c ↦ (tensor φ ψ c).toMPSTensor) 1 := by
  let f : (Fin p × Fin p) → Module.Dual ℂ H :=
    fun q ↦ (dualCoefficient φ.toLinearMap q.1 q.2).ofConv
  have hs : Submodule.span ℂ (Set.range f) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro x hx
    by_contra! h
    apply hx
    apply hφ
    ext i k
    exact (h (f (i, k)) ⟨(i, k), rfl⟩).trans (by simp)
  apply top_unique
  intro M _
  obtain ⟨g, rfl⟩ := ψ.surjective M
  have hg : g.ofConv ∈ Submodule.span ℂ (Set.range f) := by rw [hs]; trivial
  change ψ (toConv g.ofConv) ∈ _
  generalize g.ofConv = f' at hg ⊢
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, k⟩, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun _ ↦ finProdFinEquiv (i, k), ?_⟩
    funext c
    simp [MPSTensor.wordTuple, List.ofFn_succ, tensor, toMPSTensor, f]
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul z x _ hx => simpa using Submodule.smul_mem _ z hx

omit [FiniteDimensional ℂ H] in
/-- The faithful total dual representation assembles exactly the chosen
simple blocks, with multiplicity one. -/
theorem totalRepresentation_tensor
    (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ) :
    (ofDualRepresentation φ.toLinearMap (totalRepresentation ψ)).toMPSTensor =
      MPSTensor.toTensorFromBlocks (fun _ ↦ 1) (fun c ↦ (tensor φ ψ c).toMPSTensor) := by
  funext i
  simp [MPSTensor.toTensorFromBlocks, toMPSTensor, ofDualRepresentation,
    totalRepresentation, tensor, Matrix.reindexAlgEquiv]

/-- Construct the full zipper family from the abstract algebra data. All
multiplicities, fusion tensors and their independent left inverses are chosen
from the proved representation decomposition; the simultaneous letter inverse
is derived from physical faithfulness. Source: arXiv:2204.05940, Section 4.1,
`eq:splitting_algebraic`. -/
def family
    (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ) (hφ : Function.Injective φ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ)
    (hδ : ∀ c, 0 < δ c) : CompleteZipperFusionFamily (Fin r) p := by
  let hs := wordTupleSpanTop_tensor φ hφ ψ
  have hc := isBoundaryClosed_ofDualRepresentation φ (totalRepresentation ψ)
    (totalRepresentation_injective ψ)
  choose N V W hVW using fun a b ↦ hc.exists_blockFusionDecomposition
    (tensor φ ψ) (totalRepresentation_tensor φ ψ) (by decide : 0 < 1) hs a b
  let K := hs.exists_mpo_block_left_inverse.choose
  have hK := hs.exists_mpo_block_left_inverse.choose_spec
  exact CompleteZipperFusionFamily.ofBiorthogonal hδ hs.isInjective_one V W hVW K hK

/-- The construction retains the original physical coefficient letters. -/
theorem family_tensor
    (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ) (hφ : Function.Injective φ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ)
    (hδ : ∀ c, 0 < δ c) (c : Fin r) :
    (family φ hφ ψ hδ).tensor c = tensor φ ψ c := rfl

/-- The constructed family's boundary pre-bialgebra uses the counit already
constructed from the unital physical representation. Source:
arXiv:2204.05940, Section 4, lines 1419--1421. -/
@[instance_reducible]
def toPreBialgebra
    (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ) (hφ : Function.Injective φ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) ℂ)
    (hδ : ∀ c, 0 < δ c) : PreBialgebra ℂ (family φ hφ ψ hδ).BoundarySpace :=
  (family φ hφ ψ hδ).toPreBialgebraOfDualRepresentation φ
    ((WithConv.linearEquiv ℂ (H →ₗ[ℂ] ℂ)).symm.trans ψ.toLinearEquiv).toLinearMap
    (ψ.injective.comp (WithConv.linearEquiv ℂ (H →ₗ[ℂ] ℂ)).symm.injective)
    (fun _ _ ↦ rfl)

end DualRepresentationFusion

/-- A finite-dimensional cosemisimple pre-bialgebra with a faithful unital
physical representation gives a complete zipper fusion family with exactly
its physical coefficient letters. Cosemisimplicity is the source's explicit
hypothesis in arXiv:2204.05940, Section 4.1, lines 1642--1658. The matrix
blocks are derived by Wedderburn--Artin; fusion maps and simultaneous letter
inverses are derived by `DualRepresentationFusion.family`. -/
theorem exists_completeZipperFusionFamily_of_cosemisimple
    [IsSemisimpleRing (WithConv (H →ₗ[ℂ] ℂ))]
    (φ : H →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ) (hφ : Function.Injective φ) :
    ∃ (r : ℕ) (F : CompleteZipperFusionFamily (Fin r) p)
      (ψ : WithConv (H →ₗ[ℂ] ℂ) ≃ₐ[ℂ] F.BoundarySpace),
      ∀ i k, ψ (dualCoefficient φ.toLinearMap i k) = F.letter i k := by
  let : FiniteDimensional ℂ (WithConv (H →ₗ[ℂ] ℂ)) :=
    Module.Finite.equiv (WithConv.linearEquiv ℂ (H →ₗ[ℂ] ℂ)).symm
  obtain ⟨r, δ, hδ, ⟨ψ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (WithConv (H →ₗ[ℂ] ℂ))
  exact ⟨r, DualRepresentationFusion.family φ hφ ψ
    (fun c ↦ Nat.pos_of_ne_zero (hδ c).out), ψ, fun _ _ ↦ rfl⟩

end MPOTensor
