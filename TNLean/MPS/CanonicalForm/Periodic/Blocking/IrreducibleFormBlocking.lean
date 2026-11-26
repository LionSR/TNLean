/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Irreducible.BlockingInfrastructure
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.StateVectorDecomposition
import TNLean.MPS.CanonicalForm.Periodic.Blocking.Spectrum
import TNLean.MPS.CanonicalForm.Periodic.Blocking.FixedSpace
import TNLean.MPS.CanonicalForm.Periodic.Blocking.StepOrbitSectors

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

**Scope restriction (length, representation, and normalization):** the
presentations here are values of `IsIrreducibleForm`, a normalized MPV-level
representation of the source irreducible form that also imposes empty-word
equality. Documented in `docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex`.

It also contains the following results.

* `MPSTensor.IsPeriodic.exists_stepOrbit_blockDecomposition`: prescribed blocking of a periodic
  tensor.
-/

section PrescribedBlocking

/-!
## Prescribed blocking of a periodic tensor

The algebraic decomposition in arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
has gcd(m,p) nonzero blocks. This file obtains the projectors from periodicity,
rather than assuming a supplied cyclic decomposition. For positive blocking,
each compressed block is periodic of period m/gcd(m,p).

**Local fix (powered roots):** The root set uses order m/gcd(m,p); see
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex` for the paper's omitted exponent.

### Main results

* `IsPeriodic.exists_stepOrbit_blockDecomposition`: nonzero left-canonical
  compressed blocks, their support isometries, equality of all MPVs, and their
  periodicity at positive blocking lengths.

### References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`.
-/

open scoped Matrix BigOperators
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

/-- Prescribed blocking of a periodic tensor into periodic blocks.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`. -/
theorem IsPeriodic.exists_stepOrbit_blockDecomposition {d D m : ℕ}
    {A : MPSTensor d D} (hA : IsPeriodic m A) (p : ℕ) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (dim : Fin (m.gcd p) → ℕ)
      (blocks : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
      (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ),
      (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u) = 1 ∧
      (∀ u, P u ≠ 0) ∧ (∀ u i, P u * A i = A i * P (u + 1)) ∧
      (∀ a, 0 < dim a) ∧ (∑ a, dim a) = D ∧
      (∀ a, IsLeftCanonical (blocks a)) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      (∀ a, (V a)ᴴ * V a = 1) ∧
      (∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a) ∧
      (∀ a i, blocks a i = (V a)ᴴ * blockTensor A p i * V a) ∧
      (0 < p → ∀ a, IsPeriodic (m / m.gcd p) (blocks a)) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, hproj, hsum, hne, hshift⟩ := exists_paper_cyclic_projectors_of_isPeriodic A hA
  obtain ⟨dim, blocks, V, hdim, htotal, hcan, hmpv, hiso, hV, hC⟩ :=
    MPSTensor.exists_stepOrbit_blockDecomposition P hproj hsum hne A hA.leftCanonical hshift p
  refine ⟨P, dim, blocks, V, hproj, hsum, hne, hshift, hdim, htotal, hcan,
    hmpv, hiso, hV, hC, ?_⟩
  intro hp a
  exact ⟨hA.isIrreducibleFamily_compressed_stepOrbit P hproj hsum hshift hp a
      (blocks a) (V a) (hiso a) (hV a) (hC a), hcan a,
    Nat.div_gcd_pos_of_pos_left p hA.period_pos,
    hA.peripheral_compressed_stepOrbit_eq P hproj hsum hne hshift hp a
      (blocks a) (V a) (hiso a) (hV a) (hC a)⟩

end MPSTensor

end PrescribedBlocking

section IrreducibleFormBlocking

open scoped BigOperators Matrix
open Kraus (blockPhysDim blockTensor)

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

end IrreducibleFormBlocking
