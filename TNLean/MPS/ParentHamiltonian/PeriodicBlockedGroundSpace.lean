/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.PrescribedBlocking
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces

/-!
# Open MPS spaces under periodic blocking

For a periodic tensor, the step-orbit projections commute with every blocked
letter. Compression through their support isometries therefore intertwines all
words. Resolving the virtual identity and taking traces identifies the open
MPS space with the sum of the compressed block spaces at every length.

The proof retains the rectangular support isometries and uses literal word
contractions. It does not infer open-space equality from equality of periodic
matrix product vectors. The theorem permits arbitrary positive blocking;
blocking by a multiple of the period gives period-one compressed sectors.

Source: De las Cuevas--Cirac--Schuch--Perez-Garcia, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451. The finite support spaces are
those used in Nachtergaele, arXiv:cond-mat/9410110, Section 3, lines 1504--1538.

**Local fix (powered roots):** The period after blocking is `m / gcd(m,p)`.
The peripheral-root correction used in the period proof is documented in
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {ι : Type*} [Fintype ι] {dim : ι → ℕ}

/-- An isometric resolution of the virtual identity identifies the ambient
open MPS space with the sum of the sector spaces at every length, including zero.
The hypotheses express the letterwise sector decomposition in DCCSP17,
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451. This is a
trace-cyclicity consequence, rather than a consequence of equality of MPVs. -/
theorem groundSpace_eq_iSup_of_isometric_sector_resolution
    (C : MPSTensor d D) (B : (j : ι) → MPSTensor d (dim j))
    (V : (j : ι) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, C i * V j = V j * B j i) (N : ℕ) :
    groundSpace C N = ⨆ j, groundSpace (B j) N := by
  classical
  have hEmbed (j : ι) (Y : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
      groundSpaceMap C N (V j * Y * (V j)ᴴ) = groundSpaceMap (B j) N Y := by
    ext σ
    simp only [groundSpaceMap_apply, ← Matrix.mul_assoc,
      Kraus.evalWord_intertwine C (B j) (V j) (hInt j)]
    simpa only [Matrix.mul_assoc, hV j, Matrix.mul_one] using
      Matrix.trace_mul_comm (V j) (Kraus.evalWord (B j) (List.ofFn σ) * Y * (V j)ᴴ)
  have hSplit (X : Matrix (Fin D) (Fin D) ℂ) :
      groundSpaceMap C N X = ∑ j, groundSpaceMap (B j) N ((V j)ᴴ * X * V j) := by
    ext σ
    simp only [Finset.sum_apply, groundSpaceMap_apply]
    calc
      _ = (Kraus.evalWord C (List.ofFn σ) * (∑ j, V j * (V j)ᴴ) * X).trace := by
        rw [hSum, Matrix.mul_one]
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum,
          ← Matrix.mul_assoc]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Kraus.evalWord_intertwine C (B j) (V j) (hInt j)]
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (V j) (Kraus.evalWord (B j) (List.ofFn σ) * (V j)ᴴ * X)
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [hSplit]
    exact Submodule.sum_mem _ fun j _ =>
      (le_iSup (fun j => groundSpace (B j) N) j) ⟨(V j)ᴴ * X * V j, rfl⟩
  · refine iSup_le fun j => ?_
    rintro _ ⟨Y, rfl⟩
    exact ⟨V j * Y * (V j)ᴴ, hEmbed j Y⟩

/-- The isometric sector resolution gives the same exact decomposition in the
physical Euclidean Hilbert space. Source context: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, lines 1504--1538. -/
theorem groundSpaceES_eq_iSup_of_isometric_sector_resolution
    (C : MPSTensor d D) (B : (j : ι) → MPSTensor d (dim j))
    (V : (j : ι) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, C i * V j = V j * B j i) (N : ℕ) :
    groundSpaceES C N = ⨆ j, groundSpaceES (B j) N := by
  simp only [groundSpaceES,
    groundSpace_eq_iSup_of_isometric_sector_resolution C B V hV hSum hInt N,
    Submodule.map_iSup]

/-- Prescribed positive blocking of a periodic tensor retains its support
isometries and identifies all open MPS spaces with those of the compressed
step-orbit block family. The compressed letters intertwine with the original
blocked letters. No separation of the compressed sectors is asserted.

Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451;
the open-space conclusion is the supported word contraction underlying the
local support spaces of Nachtergaele, arXiv:cond-mat/9410110, Section 3. -/
theorem IsPeriodic.exists_stepOrbit_groundSpaceDecomposition {m : ℕ}
    {A : MPSTensor d D} (hA : IsPeriodic m A) (p : ℕ) (hp : 0 < p) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (dim : Fin (m.gcd p) → ℕ)
      (blocks : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
      (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ),
      (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u) = 1 ∧
      (∀ u, P u ≠ 0) ∧ (∀ u i, P u * A i = A i * P (u + 1)) ∧
      (∀ a, 0 < dim a) ∧ (∑ a, dim a) = D ∧
      (∀ a, IsLeftCanonical (blocks a)) ∧
      (∀ a, (V a)ᴴ * V a = 1) ∧
      (∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a) ∧
      (∀ a i, blocks a i = (V a)ᴴ * blockTensor A p i * V a) ∧
      (∀ a i, blockTensor A p i * V a = V a * blocks a i) ∧
      (∀ N, groundSpaceES (blockTensor A p) N =
        groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) blocks) N) ∧
      (∀ a, IsPeriodic (m / m.gcd p) (blocks a)) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, dim, blocks, V, hproj, hsum, hne, hshift, hdim, htotal, hcan,
    _hMPV, hiso, hV, hC, hperiod⟩ := hA.exists_stepOrbit_blockDecomposition p
  have hInt (a : Fin (m.gcd p)) (i : Fin (blockPhysDim d p)) :
      blockTensor A p i * V a = V a * blocks a i := by
    simp only [hC, ← Matrix.mul_assoc, hV]
    rw [stepOrbitProjection_mul_blockTensor P A hshift,
      ← hV, Matrix.mul_assoc, Matrix.mul_assoc, hiso, Matrix.mul_one]
  refine ⟨P, dim, blocks, V, hproj, hsum, hne, hshift, hdim, htotal, hcan,
    hiso, hV, hC, hInt, ?_, hperiod hp⟩
  intro N
  rw [groundSpaceES_toTensorFromBlocks_eq_iSup _ blocks (fun _ => one_ne_zero)]
  refine groundSpaceES_eq_iSup_of_isometric_sector_resolution
    (blockTensor A p) blocks V hiso ?_ hInt N
  simp only [hV, sum_stepOrbitProjection, hsum]

end MPSTensor
