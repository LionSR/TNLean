/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitPeriod
import TNLean.MPS.Core.NestedBlockMPVFlatten

/-!
# Irreducible form under positive blocking

Each periodic block of an irreducible-form tensor splits, after positive
blocking, into its shift-orbit tensors. Flattening the resulting family
gives an irreducible-form presentation of the blocked tensor. The weight
of an orbit tensor is the original block weight raised to the blocking
length.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

/-- Positive blocking preserves the MPV-level irreducible-form structure,
with every periodic block split into its shift orbits. Source:
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
noncomputable def IsIrreducibleForm.blockTensor_isIrreducibleForm
    {d D : ℕ} {A : MPSTensor d D}
    (hA : IsIrreducibleForm A) {p : ℕ} (hp : 0 < p) :
    IsIrreducibleForm (blockTensor A p) := by
  classical
  let sectorCount : Fin hA.r → ℕ :=
    fun j => Nat.gcd (hA.period j) p
  have hExists (j : Fin hA.r) :
      ∃ (dim : Fin (sectorCount j) → ℕ)
        (C : (s : Fin (sectorCount j)) →
          MPSTensor (blockPhysDim d p) (dim s)),
        (∀ s, dim s ≠ 0) ∧
        (∀ s, IsPeriodic ((hA.period j) / sectorCount j) (C s)) ∧
        SameMPV₂ (blockTensor (hA.blocks j) p)
          (toTensorFromBlocks (μ := fun _ => 1) C) := by
    let : NeZero (hA.period j) := ⟨(hA.periodic j).period_pos.ne'⟩
    exact (hA.periodic j).exists_blockTensor_periodic_orbit_compression
      (hA.blocks j) hp
  let sectorDim : (j : Fin hA.r) → Fin (sectorCount j) → ℕ :=
    fun j => Classical.choose (hExists j)
  let C : (j : Fin hA.r) → (s : Fin (sectorCount j)) →
      MPSTensor (blockPhysDim d p) (sectorDim j s) :=
    fun j => Classical.choose (Classical.choose_spec (hExists j))
  have hOrbit (j : Fin hA.r) :
      (∀ s, IsPeriodic ((hA.period j) / sectorCount j) (C j s)) ∧
      SameMPV₂ (blockTensor (hA.blocks j) p)
        (toTensorFromBlocks (μ := fun _ => 1) (C j)) := by
    exact (Classical.choose_spec (Classical.choose_spec (hExists j))).2
  let weight : Fin hA.r → ℂ := fun j => (hA.μ j) ^ p
  let flatWeight : Fin (∑ j : Fin hA.r, sectorCount j) → ℂ :=
    fun x => weight (finSigmaFinEquiv.symm x).1
  let flatPeriod : Fin (∑ j : Fin hA.r, sectorCount j) → ℕ :=
    fun x => (hA.period (finSigmaFinEquiv.symm x).1) /
      sectorCount (finSigmaFinEquiv.symm x).1
  have hSameOuter : SameMPV₂ (blockTensor A p)
      (toTensorFromBlocks weight
        (fun j => blockTensor (hA.blocks j) p)) :=
    sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
      A hA.μ hA.blocks hA.sameMPV p
  have hSameFlat : SameMPV₂
      (toTensorFromBlocks weight
        (fun j => blockTensor (hA.blocks j) p))
      (toTensorFromBlocks flatWeight
        (nestedBlockFlatTensor sectorCount sectorDim C)) :=
    sameMPV₂_weighted_nested_blocks_flatten weight
      (fun j => blockTensor (hA.blocks j) p)
      sectorCount sectorDim C (fun j => (hOrbit j).2)
  refine
    { r := ∑ j : Fin hA.r, sectorCount j
      dim := nestedBlockFlatDim sectorCount sectorDim
      blocks := nestedBlockFlatTensor sectorCount sectorDim C
      μ := flatWeight
      period := flatPeriod
      periodic := ?_
      weight_pos := ?_
      sameMPV := ?_ }
  · intro x
    exact (hOrbit (finSigmaFinEquiv.symm x).1).1
      (finSigmaFinEquiv.symm x).2
  · intro x
    exact positiveRealWeight_pow (hA.μ (finSigmaFinEquiv.symm x).1)
      (hA.weight_pos (finSigmaFinEquiv.symm x).1) p
  · intro N σ
    exact (hSameOuter N σ).trans (hSameFlat N σ)

end MPSTensor
