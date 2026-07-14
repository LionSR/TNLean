/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BlockedBNTFusionIsometries
import TNLean.MPS.MPDO.BNTTripleFusionSeparation
import TNLean.MPS.MPDO.CompleteZipperFusionPentagon

/-!
# Complete zipper data from blocked BNT fusion isometries

After one common positive blocking, the length-independent fusion map
`U_{α,β}` is a unitary coordinate map between the product bond space and the
direct sum of the fusion sectors.  Reindexing the product bond space as a pair,
its adjoint is the synthesis map and the map itself is the analysis map of the
complete zipper family.  The blocked zipper identities, reconstruction,
injectivity, and simultaneous block-letter inverse have already been derived
from the source BNT assumptions.

The empty chain is not used: the common block length is strictly positive.

## References

* arXiv:1606.00608, BNT separation at lines 317--345, equation `Ualphabeta`
  at lines 986--993, and length independence at lines 995--1010.
* arXiv:1511.08090, fusion tensors and zipper equations at lines 161--200,
  simultaneous inverse at lines 269--277, and common blocking at lines
  427--431.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

variable {p : ℕ}

/-- The blocked complete-zipper synthesis map, namely the adjoint of the
source fusion map with the product bond index written as a pair.

Source: arXiv:1511.08090, fusion tensor orientation at lines 161--163 and
zipper equations at lines 193--200. -/
noncomputable def blockedFusionSynthesis
    {g : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    (α β : Fin g) :
    Matrix (Fin (Fam.bondDim α) × Fin (Fam.bondDim β))
      ((γ : Fin g) ×
        (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) ℂ :=
  fun xy z ↦ (Fam.fusionIsometry α β)ᴴ (finProdFinEquiv xy) z

/-- The blocked complete-zipper analysis map, namely the source fusion map
with the product bond index written as a pair.

Source: arXiv:1511.08090, left inverses at line 161 and the second zipper
equation at lines 198--200. -/
noncomputable def blockedFusionAnalysis
    {g : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    (α β : Fin g) :
    Matrix ((γ : Fin g) ×
        (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ)))
      (Fin (Fam.bondDim α) × Fin (Fam.bondDim β)) ℂ :=
  fun z xy ↦ Fam.fusionIsometry α β z (finProdFinEquiv xy)

/-- Pair coisometry gives biorthogonality of the blocked analysis and
synthesis maps.

Source: arXiv:1511.08090, the fusion-tensor left-inverse relation at line
161. -/
theorem blockedFusionAnalysis_mul_blockedFusionSynthesis
    {g : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    (hcoisometry : ∀ α β : Fin g,
      Fam.fusionIsometry α β * (Fam.fusionIsometry α β)ᴴ = 1)
    (α β : Fin g) :
    Fam.blockedFusionAnalysis α β * Fam.blockedFusionSynthesis α β = 1 := by
  ext x y
  simp only [blockedFusionAnalysis, blockedFusionSynthesis, Matrix.mul_apply,
    Matrix.one_apply]
  have h := congrArg (fun M ↦ M x y) (hcoisometry α β)
  calc
    (∑ xy : Fin (Fam.bondDim α) × Fin (Fam.bondDim β),
      Fam.fusionIsometry α β x (finProdFinEquiv xy) *
        (Fam.fusionIsometry α β)ᴴ (finProdFinEquiv xy) y) =
        ∑ q : Fin (Fam.bondDim α * Fam.bondDim β),
          Fam.fusionIsometry α β x q *
            (Fam.fusionIsometry α β)ᴴ q y :=
      Equiv.sum_comp
        (finProdFinEquiv :
          (Fin (Fam.bondDim α) × Fin (Fam.bondDim β)) ≃
            Fin (Fam.bondDim α * Fam.bondDim β))
        (fun q ↦ Fam.fusionIsometry α β x q *
          (Fam.fusionIsometry α β)ᴴ q y)
    _ = if x = y then 1 else 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- The blocked second zipper identity in the paired product-bond
coordinates of the complete zipper family.

Source: arXiv:1511.08090, equation `zippercondition` at lines 198--200. -/
theorem blockedFusionAnalysis_mul_pairLetter
    {g L : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    (α β : Fin g) (I J : Fin (MPSTensor.blockPhysDim p L))
    (hzipper : Fam.fusionIsometry α β *
          mulTensor (blockTensor (Fam.tensor α) L)
            (blockTensor (Fam.tensor β) L) I J =
        Fam.blockedUnweightedDirectSumLetter L α β I J *
          Fam.fusionIsometry α β) :
    Fam.blockedFusionAnalysis α β *
        (∑ K : Fin (MPSTensor.blockPhysDim p L),
          blockTensor (Fam.tensor α) L I K ⊗ₖ
            blockTensor (Fam.tensor β) L K J) =
      Fam.blockedUnweightedDirectSumLetter L α β I J *
        Fam.blockedFusionAnalysis α β := by
  ext x y
  have h := congrArg (fun M ↦ M x (finProdFinEquiv y)) hzipper
  simp only [blockedFusionAnalysis, Matrix.mul_apply]
  calc
    (∑ xy : Fin (Fam.bondDim α) × Fin (Fam.bondDim β),
      Fam.fusionIsometry α β x (finProdFinEquiv xy) *
        (∑ K : Fin (MPSTensor.blockPhysDim p L),
          blockTensor (Fam.tensor α) L I K ⊗ₖ
            blockTensor (Fam.tensor β) L K J) xy y) =
        ∑ q : Fin (Fam.bondDim α * Fam.bondDim β),
          Fam.fusionIsometry α β x q *
            mulTensor (blockTensor (Fam.tensor α) L)
              (blockTensor (Fam.tensor β) L) I J q
                (finProdFinEquiv y) := by
      simpa [mulTensor_apply] using
        Equiv.sum_comp
          (finProdFinEquiv :
            (Fin (Fam.bondDim α) × Fin (Fam.bondDim β)) ≃
              Fin (Fam.bondDim α * Fam.bondDim β))
          (fun q ↦ Fam.fusionIsometry α β x q *
            mulTensor (blockTensor (Fam.tensor α) L)
              (blockTensor (Fam.tensor β) L) I J q
                (finProdFinEquiv y))
    _ = ∑ z, Fam.blockedUnweightedDirectSumLetter L α β I J x z *
          Fam.fusionIsometry α β z (finProdFinEquiv y) := by
      simpa [Matrix.mul_apply] using h

/-- The blocked first zipper identity in the paired product-bond coordinates
of the complete zipper family.

Source: arXiv:1511.08090, equation `zippercondition` at lines 193--196. -/
theorem pairLetter_mul_blockedFusionSynthesis
    {g L : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    (α β : Fin g) (I J : Fin (MPSTensor.blockPhysDim p L))
    (hzipper : mulTensor (blockTensor (Fam.tensor α) L)
          (blockTensor (Fam.tensor β) L) I J *
        (Fam.fusionIsometry α β)ᴴ =
      (Fam.fusionIsometry α β)ᴴ *
        Fam.blockedUnweightedDirectSumLetter L α β I J) :
    (∑ K : Fin (MPSTensor.blockPhysDim p L),
        blockTensor (Fam.tensor α) L I K ⊗ₖ
          blockTensor (Fam.tensor β) L K J) *
        Fam.blockedFusionSynthesis α β =
      Fam.blockedFusionSynthesis α β *
        Fam.blockedUnweightedDirectSumLetter L α β I J := by
  ext x y
  have h := congrArg (fun M ↦ M (finProdFinEquiv x) y) hzipper
  simp only [blockedFusionSynthesis, Matrix.mul_apply]
  calc
    (∑ xy : Fin (Fam.bondDim α) × Fin (Fam.bondDim β),
      (∑ K : Fin (MPSTensor.blockPhysDim p L),
        blockTensor (Fam.tensor α) L I K ⊗ₖ
          blockTensor (Fam.tensor β) L K J) x xy *
        (Fam.fusionIsometry α β)ᴴ (finProdFinEquiv xy) y) =
      ∑ q : Fin (Fam.bondDim α * Fam.bondDim β),
        mulTensor (blockTensor (Fam.tensor α) L)
            (blockTensor (Fam.tensor β) L) I J
              (finProdFinEquiv x) q *
          (Fam.fusionIsometry α β)ᴴ q y := by
      simpa [mulTensor_apply] using
        Equiv.sum_comp
          (finProdFinEquiv :
            (Fin (Fam.bondDim α) × Fin (Fam.bondDim β)) ≃
              Fin (Fam.bondDim α * Fam.bondDim β))
          (fun q ↦ mulTensor (blockTensor (Fam.tensor α) L)
              (blockTensor (Fam.tensor β) L) I J
                (finProdFinEquiv x) q *
            (Fam.fusionIsometry α β)ᴴ q y)
    _ = ∑ z, (Fam.fusionIsometry α β)ᴴ (finProdFinEquiv x) z *
          Fam.blockedUnweightedDirectSumLetter L α β I J z y := by
      simpa [Matrix.mul_apply] using h

/-- The blocked product letter is reconstructed through the fusion support in
the paired product-bond coordinates.

Source: arXiv:1511.08090, equation `inversegaugeone` at lines 181--191. -/
theorem pairLetter_eq_blockedFusionSynthesis_mul_directSum_mul_analysis
    {g L : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    (α β : Fin g) (I J : Fin (MPSTensor.blockPhysDim p L))
    (hreconstruct : mulTensor (blockTensor (Fam.tensor α) L)
          (blockTensor (Fam.tensor β) L) I J =
        (Fam.fusionIsometry α β)ᴴ *
          Fam.blockedUnweightedDirectSumLetter L α β I J *
            Fam.fusionIsometry α β) :
    (∑ K : Fin (MPSTensor.blockPhysDim p L),
      blockTensor (Fam.tensor α) L I K ⊗ₖ
        blockTensor (Fam.tensor β) L K J) =
      Fam.blockedFusionSynthesis α β *
        Fam.blockedUnweightedDirectSumLetter L α β I J *
          Fam.blockedFusionAnalysis α β := by
  ext x y
  have h := congrArg
    (fun M ↦ M (finProdFinEquiv x) (finProdFinEquiv y)) hreconstruct
  simpa [blockedFusionSynthesis, blockedFusionAnalysis, mulTensor_apply,
    Matrix.mul_apply] using h

/-- Length-independent source BNT fusion isometries determine complete zipper
fusion data after one common positive blocking.

The synthesis matrix is the reindexed adjoint of `U_{α,β}`, the analysis
matrix is the reindexed `U_{α,β}`, and the fusion multiplicity is the
dimension of the corresponding chi space.  Injectivity, the simultaneous
block-letter inverse, and pair coisometry are derived from the BNT witness;
none is an additional hypothesis.

Source: arXiv:1606.00608, BNT separation at lines 317--345, equation
`Ualphabeta` at lines 986--993, and length independence at lines 995--1010;
arXiv:1511.08090, complete zipper data at lines 161--200 and simultaneous
inverse at lines 269--277. -/
theorem exists_blocked_completeZipperFusionFamily
    {g D : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    {A : MPSTensor (p * p) D}
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors A
      (fun γ : Fin g ↦
        ⟨Fam.bondDim γ, (Fam.tensor γ).toMPSTensor⟩))
    (c : BNTLabelCoefficientFamily (Fin g))
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) :
    ∃ L : ℕ, 0 < L ∧
      ∃ Fus : CompleteZipperFusionFamily
          (Fin g) (MPSTensor.blockPhysDim p L),
        Fus.bondDim = Fam.bondDim ∧
        Fus.fusionMultiplicity = Fam.chi.dim ∧
        (∀ γ, HEq (Fus.tensor γ) (blockTensor (Fam.tensor γ) L)) ∧
        (∀ α β, HEq (Fus.fusionSynthesis α β)
          (Fam.blockedFusionSynthesis α β)) ∧
        ∀ α β, HEq (Fus.fusionAnalysis α β)
          (Fam.blockedFusionAnalysis α β) := by
  classical
  obtain ⟨L, hL, hSpan, hInjective, hFusion⟩ :=
    Fam.exists_positive_block_with_injective_fusion hBNT c hχ hLI
  obtain ⟨C, hC⟩ := hSpan.exists_mpo_block_left_inverse
  have hCoisometry : ∀ α β : Fin g,
      Fam.fusionIsometry α β * (Fam.fusionIsometry α β)ᴴ = 1 :=
    fun α β ↦
      Fam.fusionIsometry_mul_conjTranspose_eq_one_of_bnt_of_lengthIndependent
        hBNT c hχ hLI α β
  let Fus : CompleteZipperFusionFamily
      (Fin g) (MPSTensor.blockPhysDim p L) :=
    { bondDim := Fam.bondDim
      bondDim_pos := hBNT.blocks_dim_pos
      tensor := fun γ ↦ blockTensor (Fam.tensor γ) L
      tensor_injective := hInjective
      fusionMultiplicity := Fam.chi.dim
      fusionSynthesis := Fam.blockedFusionSynthesis
      fusionAnalysis := Fam.blockedFusionAnalysis
      analysis_mul_synthesis :=
        Fam.blockedFusionAnalysis_mul_blockedFusionSynthesis hCoisometry
      pairLetter_mul_synthesis := fun α β I J ↦ by
        simpa [blockedUnweightedDirectSumLetter] using
          Fam.pairLetter_mul_blockedFusionSynthesis α β I J
            (hFusion α β I J).2.2.1
      analysis_mul_pairLetter := fun α β I J ↦ by
        simpa [blockedUnweightedDirectSumLetter] using
          Fam.blockedFusionAnalysis_mul_pairLetter α β I J
            (hFusion α β I J).2.1
      pairLetter_eq_synthesis_mul_directSum_mul_analysis :=
        fun α β I J ↦ by
          simpa [blockedUnweightedDirectSumLetter] using
            Fam.pairLetter_eq_blockedFusionSynthesis_mul_directSum_mul_analysis
              α β I J (hFusion α β I J).2.2.2
      blockLeftInverse := C
      blockLeftInverse_apply := hC }
  refine ⟨L, hL, Fus, rfl, rfl, ?_, ?_, ?_⟩
  · intro γ
    change HEq (blockTensor (Fam.tensor γ) L)
      (blockTensor (Fam.tensor γ) L)
    rfl
  · intro α β
    change HEq (Fam.blockedFusionSynthesis α β)
      (Fam.blockedFusionSynthesis α β)
    rfl
  · intro α β
    change HEq (Fam.blockedFusionAnalysis α β)
      (Fam.blockedFusionAnalysis α β)
    rfl

end MPOTensor.BNTFusionIsometryFamily
