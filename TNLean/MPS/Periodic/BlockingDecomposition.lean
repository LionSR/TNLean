/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockingFixedSpace
import TNLean.MPS.Periodic.BlockingEigenvalues
import TNLean.MPS.Periodic.Overlap.SelfOverlapSetup

/-!
# The prescribed blocking decomposition of a periodic tensor

Assemble the orbit compression, irreducibility, and peripheral-spectrum results
into Lemma 6 of arXiv:1708.00029. Cyclic projections are obtained from periodicity,
not supplied as additional mathematical hypotheses.

**Local fix (powered roots):** The period is `m / gcd(m,p)`; the source's displayed
peripheral root set omits the exponent `p`. See
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.
-/

open scoped BigOperators Matrix
open Fin.NatCast

namespace MPSTensor

variable {d D m : ℕ}

/-- A periodic tensor admits nonzero cyclic projections in the paper's forward-shift
convention. Source: arXiv:1708.00029, `eq:Aoffdiag`, and the cyclic construction
used in `lem:blocking-arbitrary`. -/
theorem IsPeriodic.exists_paper_cyclic_projections
    [NeZero m] (A : MPSTensor d D) (hA : IsPeriodic m A) :
    ∃ P : Fin m → Matrix (Fin D) (Fin D) ℂ,
      (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u = 1) ∧
      (∀ u, P u ≠ 0) ∧ (∀ u i, P u * A i = A i * P (u + 1)) := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨dim, blocks, P, φ, V, _, _, hproj, hsum, hshift, _, _, _, _, _, hdim,
    _, hiso, hrange, _⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hA
  have hne (u) : P u ≠ 0 := by
    intro hz
    have hh := congrArg (fun X ↦ (V u)ᴴ * X * V u) ((hrange u).trans hz)
    simp only [Matrix.mul_assoc, hiso, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul] at hh
    have : NeZero (dim u) := ⟨hdim u⟩
    have he := congrFun (congrFun hh 0) 0
    simp at he
  refine ⟨fun u ↦ P (-u), fun u ↦ hproj (-u), ?_, fun u ↦ hne (-u), ?_⟩
  · simpa only [Equiv.neg_apply] using Equiv.sum_comp (Equiv.neg (Fin m)) P |>.trans hsum
  · apply negReindex_paper_shift A hA.leftCanonical hproj
    intro k
    have he : cyclicNextOfPos hA.period_pos k = k + 1 := by
      apply Fin.ext
      simp [cyclicNextOfPos, Fin.val_add, Nat.add_mod_mod]
    simpa only [he] using hshift k

/-- Blocking a period-`m` tensor by `p > 0` gives `gcd(m,p)` nonzero periodic
blocks, each of period `m / gcd(m,p)`, with explicit orbit-support isometries.
The total bond dimension and all matrix product vectors are preserved.
Source: arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432–456. -/
theorem IsPeriodic.exists_periodic_stepOrbit_decomposition
    [NeZero m] (A : MPSTensor d D) (hA : IsPeriodic m A)
    {p : ℕ} (hp : 0 < p) :
    ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (dim : Fin (m.gcd p) → ℕ)
      (blocks : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
      (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ),
      (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u = 1) ∧
      (∀ u, P u ≠ 0) ∧ (∀ u i, P u * A i = A i * P (u + 1)) ∧
      (∀ a, 0 < dim a) ∧ (∑ a, dim a) = D ∧
      (∀ a, IsPeriodic (m / m.gcd p) (blocks a)) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ ↦ 1) blocks) ∧
      (∀ a, (V a)ᴴ * V a = 1) ∧
      (∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a) ∧
      (∀ a i, blocks a i = (V a)ᴴ * blockTensor A p i * V a) := by
  obtain ⟨P, hproj, hsum, hne, hshift⟩ := IsPeriodic.exists_paper_cyclic_projections A hA
  obtain ⟨dim, blocks, V, hdim, htotal, hTP, hSame, hiso, hrange, hletter⟩ :=
    exists_stepOrbit_blockDecomposition P hproj hsum hne A hA.leftCanonical hshift p
  refine ⟨P, dim, blocks, V, hproj, hsum, hne, hshift, hdim, htotal, ?_,
    hSame, hiso, hrange, hletter⟩
  intro a
  exact ⟨hA.isIrreducibleFamily_compressed_stepOrbit P hproj hsum hshift hp a
      (blocks a) (V a) (hiso a) (hrange a) (hletter a),
    hTP a, Nat.div_gcd_pos_of_pos_left p hA.period_pos,
    hA.peripheral_compressed_stepOrbit_eq P hproj hsum hne hshift hp a
      (blocks a) (V a) (hiso a) (hrange a) (hletter a)⟩
end MPSTensor
