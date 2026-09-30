/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.PhaseTwistedTensor
import TNLean.MPS.Periodic.Overlap.SelfOverlapSetup
import TNLean.MPS.Periodic.SectorIrreducibility.ProjectionOrtho

/-!
# Orbit corners of a blocked periodic tensor

For a periodic tensor, its cyclic projections give a grading of every letter.
After blocking by `p` sites, a matrix corner can connect only sectors in the
same orbit of the shift by `p`. This is the algebraic part of the blocked
decomposition in arXiv:1708.00029, Section 4.1, lines 765--806. The
normality and irreducibility of the resulting orbit blocks require separate
arguments.
-/

open scoped Matrix BigOperators
namespace MPSTensor

/-- The cyclic projections of a periodic tensor give an orbitwise block
decomposition of each `p`-blocked letter. The orbit length is the additive
order of `p` in `ZMod m`, hence `m / gcd(m,p)`.

Source: arXiv:1708.00029, Lemma `lem:unique-dec` and Section 4.1,
lines 446--450 and 765--806. -/
theorem exists_blockTensor_offOrbit_corners {d D m : ℕ} [NeZero m]
    (A : MPSTensor d D) (hA : IsPeriodic m A) (p : ℕ) :
    ∃ (ι : Type) (α : Fin m → ι)
      (k : Fin m → ZMod (addOrderOf (p : ZMod m)))
      (P : Fin m → MatrixAlg D),
      (∀ u, IsOrthogonalProjection (P u)) ∧
      (∀ u, P u ≠ 0) ∧
      (∑ u : Fin m, P u = 1) ∧
      (∀ u v, u ≠ v → P u * P v = 0) ∧
      (∀ u (i : Fin d), P u * A i = A i * P (u + 1)) ∧
      (∀ u, α (u + p • (1 : Fin m)) = α u) ∧
      (∀ u, k (u + p • (1 : Fin m)) = k u + 1) ∧
      Function.Surjective α ∧
      (∀ u v, α u = α v ↔
        (ZMod.finEquiv m) u - (ZMod.finEquiv m) v ∈
          AddSubgroup.zmultiples (p : ZMod m)) ∧
      Nat.card ι = Nat.gcd m p ∧
      (∀ u v, α u ≠ α v →
        ∀ I : Fin (blockPhysDim d p),
          P u * blockTensor A p I * P v = 0) := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨dim, blocks, _hLC, _hMPV, ⟨P₀, φ, hproj, hsum, hcyc,
    _hcomm, _htrace, _hint, _hmul, _hstar⟩, _hnonzero⟩ :=
    exists_cyclic_sector_decomp_after_blocking_of_isPeriodic A hA
  let P : Fin m → MatrixAlg D := fun u => P₀ (-u)
  have hproj' : ∀ u, IsOrthogonalProjection (P u) := fun u => hproj (-u)
  have hnonzero₀ : ∀ u, P₀ u ≠ 0 :=
    cyclic_projection_ne_zero_of_sum_one
      (T := Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) hsum hcyc
  have hnonzero : ∀ u, P u ≠ 0 := fun u => hnonzero₀ (-u)
  have hsum' : ∑ u : Fin m, P u = 1 := by
    have h := Fintype.sum_equiv (Equiv.neg (Fin m))
      (fun u : Fin m => P₀ (-u)) P₀ (fun _ => rfl)
    exact h.trans hsum
  have horth : ∀ u v, u ≠ v → P u * P v = 0 := by
    intro u v huv
    exact pairwise_mul_zero_of_orthogonalProjection_sum_one P₀ hproj hsum
      (by intro h; exact huv (neg_injective h))
  have hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1) := by
    intro u i
    exact negReindex_paper_shift A hA.leftCanonical hproj hcyc u i
  obtain ⟨ι, α₀, k₀, hα₀, hk₀, hsurj₀, horbit₀, hcard⟩ :=
    exists_phase_residue_coordinates (m := m) (p := p)
  let e : Fin m ≃+* ZMod m := ZMod.finEquiv m
  let α : Fin m → ι := fun u => α₀ (e u)
  let k : Fin m → ZMod (addOrderOf (p : ZMod m)) := fun u => k₀ (e u)
  have hα : ∀ u, α (u + p • (1 : Fin m)) = α u := by
    intro u
    simpa [α, map_add, map_nsmul] using hα₀ (e u)
  have hk : ∀ u, k (u + p • (1 : Fin m)) = k u + 1 := by
    intro u
    simpa [k, map_add, map_nsmul] using hk₀ (e u)
  have hsurj : Function.Surjective α := by
    intro a
    obtain ⟨z, hz⟩ := hsurj₀ a
    exact ⟨e.symm z, by simpa [α] using hz⟩
  have horbit : ∀ u v, α u = α v ↔
      e u - e v ∈ AddSubgroup.zmultiples (p : ZMod m) := by
    intro u v
    exact horbit₀ (e u) (e v)
  refine ⟨ι, α, k, P, hproj', hnonzero, hsum', horth, hshift,
    hα, hk, hsurj, horbit, hcard, ?_⟩
  intro u v huv I
  exact cyclic_projection_blockTensor_offOrbit_zero p α hα P A horth hshift u v huv I

end MPSTensor
