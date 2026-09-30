/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.CanonicalRefinementWitness
import TNLean.MPS.Periodic.Symmetry.Theorem41Forward

/-!
# Canonical refinement witnesses from the literal equal-case theorem

The refinement isometry first produces the blocked tensor (C). Its
irreducible-form presentation is inherited from the given tensor. The
equal-case theorem then removes any zero composition factor of the arbitrary
refinement root and yields a same-bond irreducible-form root.

Source: arXiv:1708.00029, Theorem 4.1, lines 735--810.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- A same-bond refinement of an irreducible-form tensor has a same-bond
irreducible-form root whose blocked vectors agree with the literal isometric
target at every length. The target also retains the original transfer map.
Source: arXiv:1708.00029, Theorem 4.1, lines 735--810. -/
theorem pRefinementCanonicalization_literal_root
    {d D : ℕ} (B : MPSTensor d D)
    (hB : IsIrreducibleForm B) (p : ℕ) (hp : 0 < p)
    (hRefine : IsPRefinable B p) :
    ∃ (A' : MPSTensor d D) (_hA' : IsIrreducibleForm A')
      (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ)
      (_hC : IsIrreducibleForm
        (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ)),
      Wᴴ * W = 1 ∧
      Kraus.transferMap
        (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ) =
        Kraus.transferMap B ∧
      SameMPV₂ (blockTensor A' p)
        (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ) := by
  classical
  obtain ⟨A, W, hC, hW, hTransfer, hSame⟩ :=
    pRefinementCanonicalization_pullback_of_irreducibleForm B hB p hRefine
  let C : MPSTensor (blockPhysDim d p) D :=
    fun τ => ∑ σ : Fin d, W τ σ • B σ
  have hSamePos : SameMPV₂Pos (blockTensor A p) C :=
    fun N hN σ => (hSame N σ).symm
  obtain ⟨A', hA', _, hBlock⟩ :=
    exists_irreducibleForm_refinement_root_tensor A C hC hp hSamePos
  exact ⟨A', hA', W, hC, hW, hTransfer, hBlock⟩

end MPSTensor
