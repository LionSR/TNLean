/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Periodic.PrescribedBlocking

/-!
# Positive blocking of an irreducible-form presentation

Apply the prescribed periodic decomposition to every original block, retaining
its label and raising its weight to the blocking power. Flattening these labels
gives an irreducible-form presentation of the blocked tensor, as used in
arXiv:1708.00029, Theorem 4.1, lines 750–756.

The supplied presentation carries all-length MPV equality, not a literal bond
similarity. The explicit orbit isometries remain available from
`IsPeriodic.exists_stepOrbit_blockDecomposition`; the global similarity
needed for the corrected forward theorem is a separate construction.
-/

open scoped BigOperators Matrix

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Refining each summand by a unit-weight block presentation commutes with taking
a weighted block sum. Each refined block inherits its original summand's weight.
Source: arXiv:1708.00029, `eq:irreducible-form` and `lem:blocking-arbitrary`,
lines 252–261 and 432–456. -/
theorem sameMPV₂_toTensorFromBlocks_refinement
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (n : Fin r → ℕ) (sd : (k : Fin r) → Fin (n k) → ℕ)
    (B : (k : Fin r) → (a : Fin (n k)) → MPSTensor d (sd k a))
    (hB : ∀ k, SameMPV₂ (A k) (toTensorFromBlocks (fun _ ↦ 1) (B k))) :
    let e := (finSigmaFinEquiv (n := n)).symm
    SameMPV₂ (toTensorFromBlocks μ A)
      (toTensorFromBlocks (fun j ↦ μ (e j).1) (fun j ↦ B (e j).1 (e j).2)) := by
  dsimp only
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  simp_rw [hB _ N σ, mpv_toTensorFromBlocks_eq_sum, one_pow, one_smul, Finset.smul_sum]
  exact (Fintype.sum_sigma' fun k a ↦ μ k ^ N • mpv (B k a) σ).symm.trans
    (Equiv.sum_comp finSigmaFinEquiv.symm _).symm

/-- Positive blocking preserves a supplied irreducible-form presentation.
The new index enumerates `(original block, step orbit)`; its weight is the
original weight to the power `p`, and its period is the original period divided
by its greatest common divisor with `p`.

Source: arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432–456, applied to
each block as in the proof of Theorem 4.1, lines 750–756. This construction
preserves the presentation's MPVs; it does not supply a global bond similarity
between the original tensor and its presentation. -/
noncomputable def IsIrreducibleForm.block {D : ℕ} {A : MPSTensor d D}
    (h : IsIrreducibleForm A) {p : ℕ} (hp : 0 < p) :
    IsIrreducibleForm (blockTensor A p) := by
  classical
  let n : Fin h.r → ℕ := fun k ↦ (h.period k).gcd p
  have hex (k : Fin h.r) :
      ∃ (sd : Fin (n k) → ℕ)
        (B : (a : Fin (n k)) → MPSTensor (blockPhysDim d p) (sd a)),
        (∀ a, IsPeriodic (h.period k / n k) (B a)) ∧
        SameMPV₂ (blockTensor (h.blocks k) p) (toTensorFromBlocks (fun _ ↦ 1) B) := by
    obtain ⟨_, sd, B, _, _, _, _, _, _, _, _, hSame, _, _, _, hper⟩ :=
      (h.periodic k).exists_stepOrbit_blockDecomposition p
    exact ⟨sd, B, hper hp, hSame⟩
  choose sd B hper hSame using hex
  let e := (finSigmaFinEquiv (n := n)).symm
  refine {
    r := ∑ k, n k
    dim := fun j ↦ sd (e j).1 (e j).2
    blocks := fun j ↦ B (e j).1 (e j).2
    μ := fun j ↦ h.μ (e j).1 ^ p
    period := fun j ↦ h.period (e j).1 / n (e j).1
    periodic := fun j ↦ hper (e j).1 (e j).2
    weight_pos := ?_
    sameMPV := ?_ }
  · intro j
    have he : h.μ (e j).1 = ((h.μ (e j).1).re : ℂ) := by
      apply Complex.ext <;> simp [(h.weight_pos (e j).1).2]
    rw [he, ← Complex.ofReal_pow]
    exact ⟨pow_pos (h.weight_pos (e j).1).1 p, rfl⟩
  · have hbase := sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
      A h.μ h.blocks h.sameMPV p
    have hflat := sameMPV₂_toTensorFromBlocks_refinement (fun k ↦ h.μ k ^ p)
      (fun k ↦ blockTensor (h.blocks k) p) n sd B hSame
    intro N σ
    exact (hbase N σ).trans (hflat N σ)

/-- The all-length MPV equality in an irreducible-form presentation forces equality
of total bond dimensions by evaluation on the empty word. -/
theorem IsIrreducibleForm.sum_dim_eq {D : ℕ} {A : MPSTensor d D} (h : IsIrreducibleForm A) :
    (∑ k, h.dim k) = D := by
  have he := h.sameMPV 0 Fin.elim0
  simp only [mpv_zero_length] at he
  exact_mod_cast he.symm

end MPSTensor
