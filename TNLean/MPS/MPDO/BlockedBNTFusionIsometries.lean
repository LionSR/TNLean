/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTFusionIsometries
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.SourceBNTBlocking

/-!
# Blocking the length-independent BNT fusion isometries

The basis of normal tensors admits one common positive physical blocking for
which the labelled tensors are simultaneously injective.  At that same block
length, the fusion isometries of Theorem IV.13 satisfy the unweighted fusion
identity and both zipper orientations.

The exclusion of the empty block is essential.  At block length zero the
conjugated fusion identity would assert that the fusion isometry is also a
coisometry, which is not an assumption of Theorem IV.13.

## References

* arXiv:1606.00608, BNT definition and blocking, lines 271--274 and 317--345.
* arXiv:1606.00608, equation `Ualphabeta`, lines 986--993.
* arXiv:1606.00608, length independence, lines 995--1010.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : MPOTensor.BNTFusionIsometryFamily Λ p)

/-- The unweighted direct-sum letter obtained after blocking a positive
number of physical sites.  Its multiplicity space for the label `γ` is the
chi space of `χ_{α,β,γ}`.

Source: arXiv:1606.00608, equation `Ualphabeta`, lines 986--993, specialized
by the length-independence observation at lines 995--1010. -/
noncomputable def blockedUnweightedDirectSumLetter
    (L : ℕ) (α β : Λ) (I J : Fin (MPSTensor.blockPhysDim p L)) :
    Matrix ((γ : Λ) × (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ)))
      ((γ : Λ) × (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) ℂ :=
  Matrix.blockDiagonal' fun γ =>
    (1 : Matrix (Fin (Fam.chi.dim α β γ))
      (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
        blockTensor (Fam.tensor γ) L I J

/-- The fusion identity transported through a positive physical block.  The
same fusion map conjugates a blocked product letter onto the unweighted direct
sum of the blocked labelled letters.

Source: arXiv:1606.00608, equation `Ualphabeta`, lines 986--993, and length
independence at lines 995--1010. -/
theorem blocked_fusion_of_lengthIndependent
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {L : ℕ} (hL : 0 < L)
    (α β : Λ) (I J : Fin (MPSTensor.blockPhysDim p L)) :
    Fam.fusionIsometry α β *
          mulTensor (blockTensor (Fam.tensor α) L)
            (blockTensor (Fam.tensor β) L) I J *
        (Fam.fusionIsometry α β)ᴴ =
      Fam.blockedUnweightedDirectSumLetter L α β I J := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 :=
    ⟨L - 1, (Nat.succ_pred_eq_of_pos hL).symm⟩
  rw [← blockTensor_mulTensor (Fam.tensor α) (Fam.tensor β)]
  simp only [blockTensor_apply, MPSTensor.wordOfBlock, evalWord_ofFn]
  let F : Fin (n + 1) →
      Matrix (Fin (Fam.bondDim α * Fam.bondDim β))
        (Fin (Fam.bondDim α * Fam.bondDim β)) ℂ :=
    fun l ↦ mulTensor (Fam.tensor α) (Fam.tensor β)
      (MPSTensor.decodeBlock p (n + 1) I l)
      (MPSTensor.decodeBlock p (n + 1) J l)
  let G : ∀ γ : Λ, Fin (n + 1) →
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ :=
    fun γ l ↦ Fam.tensor γ
      (MPSTensor.decodeBlock p (n + 1) I l)
      (MPSTensor.decodeBlock p (n + 1) J l)
  unfold blockedUnweightedDirectSumLetter
  simp only [blockTensor_apply, MPSTensor.wordOfBlock, evalWord_ofFn]
  change Fam.fusionIsometry α β * (List.ofFn F).prod *
      (Fam.fusionIsometry α β)ᴴ =
    Matrix.blockDiagonal' fun γ ↦
      (1 : Matrix (Fin (Fam.chi.dim α β γ))
        (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ (List.ofFn (G γ)).prod
  calc
    _ = (List.ofFn fun l ↦ Fam.fusionIsometry α β * F l *
        (Fam.fusionIsometry α β)ᴴ).prod :=
      (listProd_conj_of_conjTranspose_mul_self
        (Fam.fusionIsometry α β) (Fam.isometry α β) F).symm
    _ = (List.ofFn fun l ↦ Matrix.blockDiagonal' fun γ ↦
        Fam.chi.matrix α β γ ⊗ₖ G γ l).prod := by
      congr 1
      rw [List.ofFn_inj]
      funext l
      exact Fam.fusion α β
        (MPSTensor.decodeBlock p (n + 1) I l)
        (MPSTensor.decodeBlock p (n + 1) J l)
    _ = Matrix.blockDiagonal' (fun γ ↦
        ((Fam.chi.matrix α β γ) ^ (n + 1)) ⊗ₖ
          (List.ofFn (G γ)).prod) := by
      rw [listProd_blockDiagonal'_kronecker]
    _ = Matrix.blockDiagonal' (fun γ ↦
        (1 : Matrix (Fin (Fam.chi.dim α β γ))
          (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
            (List.ofFn (G γ)).prod) := by
      simp_rw [Fam.chi_matrix_eq_one_of_lengthIndependent c hχ hLI]
      simp

/-- The left zipper identity for the same positive physical blocking.

Source: arXiv:1606.00608, lines 986--1010; arXiv:1511.08090, equation
`zippercondition2`, lines 193--196. -/
theorem fusionIsometry_mul_blocked_mulTensor_of_lengthIndependent
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {L : ℕ} (hL : 0 < L)
    (α β : Λ) (I J : Fin (MPSTensor.blockPhysDim p L)) :
    Fam.fusionIsometry α β *
        mulTensor (blockTensor (Fam.tensor α) L)
          (blockTensor (Fam.tensor β) L) I J =
      Fam.blockedUnweightedDirectSumLetter L α β I J *
        Fam.fusionIsometry α β := by
  calc
    _ = (Fam.fusionIsometry α β *
          mulTensor (blockTensor (Fam.tensor α) L)
            (blockTensor (Fam.tensor β) L) I J *
          (Fam.fusionIsometry α β)ᴴ) *
        Fam.fusionIsometry α β := by
      rw [Matrix.mul_assoc, Fam.isometry, Matrix.mul_one]
    _ = _ := by
      rw [Fam.blocked_fusion_of_lengthIndependent c hχ hLI hL]

/-- The right zipper identity for the same positive physical blocking.

Source: arXiv:1606.00608, lines 986--1010; arXiv:1511.08090, equation
`zippercondition2`, lines 198--200. -/
theorem blocked_mulTensor_mul_fusionIsometry_conjTranspose_of_lengthIndependent
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {L : ℕ} (hL : 0 < L)
    (α β : Λ) (I J : Fin (MPSTensor.blockPhysDim p L)) :
    mulTensor (blockTensor (Fam.tensor α) L)
          (blockTensor (Fam.tensor β) L) I J *
        (Fam.fusionIsometry α β)ᴴ =
      (Fam.fusionIsometry α β)ᴴ *
        Fam.blockedUnweightedDirectSumLetter L α β I J := by
  calc
    _ = (Fam.fusionIsometry α β)ᴴ *
        (Fam.fusionIsometry α β *
          mulTensor (blockTensor (Fam.tensor α) L)
            (blockTensor (Fam.tensor β) L) I J *
          (Fam.fusionIsometry α β)ᴴ) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Fam.isometry,
        Matrix.one_mul]
    _ = _ := by
      rw [Fam.blocked_fusion_of_lengthIndependent c hχ hLI hL]

/-- Literal reconstruction of a blocked product letter through the fusion
isometry and the unweighted blocked direct sum.

Source: arXiv:1606.00608, lines 986--1010; arXiv:1511.08090, equation
`inversegaugeone`, lines 181--191. -/
theorem blocked_mulTensor_eq_conjTranspose_mul_unweightedDirectSum_mul
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {L : ℕ} (hL : 0 < L)
    (α β : Λ) (I J : Fin (MPSTensor.blockPhysDim p L)) :
    mulTensor (blockTensor (Fam.tensor α) L)
        (blockTensor (Fam.tensor β) L) I J =
      (Fam.fusionIsometry α β)ᴴ *
        Fam.blockedUnweightedDirectSumLetter L α β I J *
        Fam.fusionIsometry α β := by
  calc
    _ = ((Fam.fusionIsometry α β)ᴴ * Fam.fusionIsometry α β) *
          mulTensor (blockTensor (Fam.tensor α) L)
            (blockTensor (Fam.tensor β) L) I J *
          ((Fam.fusionIsometry α β)ᴴ * Fam.fusionIsometry α β) := by
      rw [Fam.isometry, Matrix.one_mul, Matrix.mul_one]
    _ = (Fam.fusionIsometry α β)ᴴ *
        (Fam.fusionIsometry α β *
          mulTensor (blockTensor (Fam.tensor α) L)
            (blockTensor (Fam.tensor β) L) I J *
          (Fam.fusionIsometry α β)ᴴ) *
        Fam.fusionIsometry α β := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Fam.blocked_fusion_of_lengthIndependent c hχ hLI hL]

/-- A basis of normal tensors and its length-independent fusion isometries have
one common positive block length at which all labelled MPO tensors are
injective and all four unweighted fusion identities hold.

The block length is obtained from the BNT property; it is not an additional
hypothesis.  After the length-independent specialization, the multiplicity
for the label `γ` is `Fam.chi.dim α β γ`, the dimension of the chi space.

Source: arXiv:1606.00608, BNT blocking at lines 317--345, equation
`Ualphabeta` at lines 986--993, and length independence at lines 995--1010. -/
theorem exists_positive_block_with_injective_fusion
    {g D : ℕ} (Fam : MPOTensor.BNTFusionIsometryFamily (Fin g) p)
    {A : MPSTensor (p * p) D}
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors A
      (fun γ : Fin g ↦
        ⟨Fam.bondDim γ, (Fam.tensor γ).toMPSTensor⟩))
    (c : BNTLabelCoefficientFamily (Fin g))
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) :
    ∃ L : ℕ, 0 < L ∧
      MPSTensor.WordTupleSpanTop
        (fun γ ↦ (blockTensor (Fam.tensor γ) L).toMPSTensor) 1 ∧
      (∀ γ, MPSTensor.IsInjective
        (blockTensor (Fam.tensor γ) L).toMPSTensor) ∧
      ∀ (α β : Fin g) (I J : Fin (MPSTensor.blockPhysDim p L)),
        (Fam.fusionIsometry α β *
              mulTensor (blockTensor (Fam.tensor α) L)
                (blockTensor (Fam.tensor β) L) I J *
            (Fam.fusionIsometry α β)ᴴ =
          Fam.blockedUnweightedDirectSumLetter L α β I J) ∧
        (Fam.fusionIsometry α β *
              mulTensor (blockTensor (Fam.tensor α) L)
                (blockTensor (Fam.tensor β) L) I J =
          Fam.blockedUnweightedDirectSumLetter L α β I J *
            Fam.fusionIsometry α β) ∧
        (mulTensor (blockTensor (Fam.tensor α) L)
              (blockTensor (Fam.tensor β) L) I J *
            (Fam.fusionIsometry α β)ᴴ =
          (Fam.fusionIsometry α β)ᴴ *
            Fam.blockedUnweightedDirectSumLetter L α β I J) ∧
        (mulTensor (blockTensor (Fam.tensor α) L)
              (blockTensor (Fam.tensor β) L) I J =
          (Fam.fusionIsometry α β)ᴴ *
            Fam.blockedUnweightedDirectSumLetter L α β I J *
            Fam.fusionIsometry α β) := by
  obtain ⟨L, hL, hSpan⟩ := hBNT.exists_blocked_wordTupleSpanTop_one
  have hReindexed :=
    (MPSTensor.wordTupleSpanTop_reindexPhysical_equiv
      (blockedDoubledIndexEquiv p L)
      (fun γ ↦ MPSTensor.blockTensor (Fam.tensor γ).toMPSTensor L) 1).2 hSpan
  have hFamily :
      (fun γ ↦ (blockTensor (Fam.tensor γ) L).toMPSTensor) =
        fun γ ↦ MPSTensor.reindexPhysical (blockedDoubledIndexEquiv p L)
          (MPSTensor.blockTensor (Fam.tensor γ).toMPSTensor L) := by
    funext γ
    exact toMPSTensor_blockTensor (Fam.tensor γ)
  have hSpanBlocked : MPSTensor.WordTupleSpanTop
      (fun γ ↦ (blockTensor (Fam.tensor γ) L).toMPSTensor) 1 := by
    rw [hFamily]
    exact hReindexed
  refine ⟨L, hL, hSpanBlocked, fun γ ↦ hSpanBlocked.isInjective_one γ, ?_⟩
  intro α β I J
  exact ⟨Fam.blocked_fusion_of_lengthIndependent c hχ hLI hL α β I J,
    Fam.fusionIsometry_mul_blocked_mulTensor_of_lengthIndependent c hχ hLI hL α β I J,
    Fam.blocked_mulTensor_mul_fusionIsometry_conjTranspose_of_lengthIndependent
      c hχ hLI hL α β I J,
    Fam.blocked_mulTensor_eq_conjTranspose_mul_unweightedDirectSum_mul
      c hχ hLI hL α β I J⟩

end MPOTensor.BNTFusionIsometryFamily
