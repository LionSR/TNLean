/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OwnershipMonomials
import TNLean.Lattice.PartyCircuit.SiteRegisters

/-!
# Tag registers of holes

The source has one tag register for every hole of an encoded frame, held by the tag owner of
the hole (`05-frames.tex`, Definition 6.1). This file lists those registers on a party layout.
It is separate from `TNLean.PEPS.Approximation.SiteRegisters` because holes are square patches
of the plane, while the site registers make sense on any finite set of sites.

* `tagRegs l` lists one register `ℂ^{Tag}` for each hole of `l`, held by its tag owner, with
  basis vectors `tagVec` and the identification `tagIso` with `ℂ^{TagSpace l}`.

## Main definitions

* `EncodedFrame.tagRegs`, `EncodedFrame.tagVec`, `EncodedFrame.tagIso`.

## Main results

* `EncodedFrame.tagIso_tagVec`: the identification on basis vectors.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Definition 6.1 `def:frame`,
  `05-frames.tex`, lines 71–82.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.EncodedFrame

open TNLean.Lattice.PartyCircuit ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### Tag registers -/

section Tags

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

/-- The tag registers of a list of holes, in the order of the list, the tag of a hole held by
its tag owner. -/
def tagRegs : List (Hole pos q Party) → Layout Party
  | [] => []
  | h :: l => ⟨h.tagOwner, euc h.patch.Tag⟩ :: tagRegs l

/-- The basis vector `⊗_a |τ_a⟩` of the tag registers. -/
def tagVec : (l : List (Hole pos q Party)) → TagSpace l → Mem (tagRegs l)
  | [], _ => (1 : ℂ)
  | h :: l, τ => (EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) ⊗ₜ
      tagVec l τ.2

/-- The tag registers identified with `ℂ^{TagSpace l}`. -/
def tagIso : (l : List (Hole pos q Party)) → Mem (tagRegs l) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (TagSpace l)
  | [] => (OrthonormalBasis.singleton Unit ℂ).repr
  | h :: l => ((tagIso l).lTensor (EuclideanSpace ℂ h.patch.Tag)).trans
      (pairIso h.patch.Tag (TagSpace l))

/-- The tag registers on basis vectors: `⊗_a |τ_a⟩ ↦ |τ⟩`. -/
theorem tagIso_tagVec : (l : List (Hole pos q Party)) → (τ : TagSpace l) →
    tagIso l (tagVec l τ) = EuclideanSpace.single τ (1 : ℂ)
  | [], τ => by
      change (OrthonormalBasis.singleton Unit ℂ).repr (1 : ℂ) = _
      ext u
      rw [OrthonormalBasis.singleton_repr]
      erw [PiLp.single_apply]
      split_ifs with hu
      · rfl
      · exact absurd rfl hu
  | h :: l, τ => by
      change pairIso h.patch.Tag (TagSpace l) ((tagIso l).lTensor (EuclideanSpace ℂ h.patch.Tag)
        ((EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) ⊗ₜ
          tagVec l τ.2)) = _
      ext i
      rw [LinearIsometryEquiv.lTensor_tmul, tagIso_tagVec l τ.2, pairIso_tmul_apply]
      change (EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) i.1 *
          (EuclideanSpace.single τ.2 (1 : ℂ) : EuclideanSpace ℂ (TagSpace l)) i.2 =
        (EuclideanSpace.single (τ : h.patch.Tag × TagSpace l) (1 : ℂ) :
          EuclideanSpace ℂ (h.patch.Tag × TagSpace l)) i
      simp only [PiLp.single_apply, ite_zero_mul_ite_zero, one_mul]
      erw [PiLp.single_apply]
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (Prod.ext h₁.1 h₁.2) h₂
      · exact absurd ⟨congrArg Prod.fst h₂, congrArg Prod.snd h₂⟩ h₁
      · rfl

end Tags

end TNLean.PEPS.EncodedFrame
