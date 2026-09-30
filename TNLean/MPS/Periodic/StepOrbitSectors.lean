/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinStepOrbit
import TNLean.Algebra.OrthogonalResolution
import TNLean.MPS.CanonicalForm.CyclicSectors.CommutingProj
import TNLean.MPS.Core.CanonicalNormalization
import TNLean.MPS.Periodic.SectorLift

/-!
# Cyclic sectors grouped for a prescribed blocking length

For a period m and blocking length p, arXiv:1708.00029, Lemma
`lem:blocking-arbitrary`, groups the cyclic projections into gcd(m,p) step orbits.
This file establishes the resulting orthogonal resolution and its commutation
with the blocked letters. The spectral and irreducibility claims about the
compressed blocks are separate from these algebraic identities.

## Main results

* `stepOrbitProjection_mul_blockTensor`: orbit sums commute with blocked letters.
* `exists_stepOrbit_blockDecomposition`: compression gives nonzero left-canonical
  blocks of total dimension D and preserves the MPVs, including the empty word.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`.
-/

open scoped Matrix BigOperators
open Fin.NatCast

namespace MPSTensor

variable {d D m : ℕ} [NeZero m]

/-- Sum the cyclic projections along one step-p orbit.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, definition of tilde P. -/
noncomputable def stepOrbitProjection (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (p : ℕ) (a : Fin (m.gcd p)) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ k : Fin (m / m.gcd p),
    P (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m)) (a, k))

/-- Grouping by the step coordinates preserves the sum of all cyclic projections.
Source: arXiv:1708.00029, paragraph following `lem:unique-dec`. -/
theorem sum_stepOrbitProjection (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (p : ℕ) :
    ∑ a, stepOrbitProjection P p a = ∑ u, P u := by
  unfold stepOrbitProjection
  simpa only [Fintype.sum_prod_type] using
    (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).sum_comp P

/-- Each step-orbit sum is an orthogonal projection.
Source: arXiv:1708.00029, paragraph following `lem:unique-dec`. -/
theorem stepOrbitProjection_isOrthogonalProjection
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (p : ℕ) (a : Fin (m.gcd p)) : IsOrthogonalProjection (stepOrbitProjection P p a) := by
  unfold stepOrbitProjection
  apply isOrthogonalProjection_sum_of_pairwise_mul_eq_zero
  · exact fun k => hproj _
  · intro i j hij
    apply orthogonalProjection_mul_eq_zero_of_sum_eq_one P hproj hsum
    intro he
    exact hij (congrArg Prod.snd
      ((Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).injective he))

/-- An orbit projection retains exactly the original projections in that orbit.
Source: arXiv:1708.00029, orthogonality calculation after `lem:unique-dec`. -/
theorem stepOrbitProjection_mul_original
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (p : ℕ) (a b : Fin (m.gcd p)) (k : Fin (m / m.gcd p)) :
    stepOrbitProjection P p a *
        P (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m)) (b, k)) =
      if a = b then P (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m)) (b, k))
      else 0 := by
  have hmul := orthogonalProjection_mul_eq_ite_of_sum_eq_one P hproj hsum
  by_cases hab : a = b
  · subst b
    simp [stepOrbitProjection, Finset.sum_mul, hmul]
  · simp [stepOrbitProjection, Finset.sum_mul, hmul, hab]

/-- Distinct step orbits give orthogonal projections.
Source: arXiv:1708.00029, paragraph following `lem:unique-dec`. -/
theorem stepOrbitProjection_mul_eq_zero
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (p : ℕ) {a b : Fin (m.gcd p)} (hab : a ≠ b) :
    stepOrbitProjection P p a * stepOrbitProjection P p b = 0 :=
  orthogonalProjection_mul_eq_zero_of_sum_eq_one _
    (stepOrbitProjection_isOrthogonalProjection P hproj hsum p)
    ((sum_stepOrbitProjection P p).trans hsum) hab

/-- A step-orbit sum containing a nonzero cyclic projection is nonzero.
Source: arXiv:1708.00029, the blocks in `lem:blocking-arbitrary`. -/
theorem stepOrbitProjection_ne_zero
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hne : ∀ u, P u ≠ 0) (p : ℕ) (a : Fin (m.gcd p)) :
    stepOrbitProjection P p a ≠ 0 := by
  let : NeZero (m / m.gcd p) :=
    ⟨Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_left p (Nat.pos_of_ne_zero (NeZero.ne m)))⟩
  intro hzero
  have h := stepOrbitProjection_mul_original P hproj hsum p a a 0
  simp only [hzero, Matrix.zero_mul, ite_true] at h
  exact hne _ h.symm

/-- Step-p orbit projections commute with words of length p.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, paragraph after `lem:unique-dec`. -/
theorem stepOrbitProjection_mul_evalWord (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (A : MPSTensor d D) (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (p : ℕ) (a : Fin (m.gcd p)) (w : List (Fin d)) (hw : w.length = p) :
    stepOrbitProjection P p a * Kraus.evalWord A w =
      Kraus.evalWord A w * stepOrbitProjection P p a := by
  let : NeZero (m / m.gcd p) :=
    ⟨Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_left p (Nat.pos_of_ne_zero (NeZero.ne m)))⟩
  simp only [stepOrbitProjection, Finset.sum_mul,
    projector_mul_evalWord_eq_evalWord_mul_projector P A hshift, hw, nsmul_one]
  simp_rw [← Fin.stepOrbitEquiv_add_one m p (Nat.pos_of_ne_zero (NeZero.ne m)) a]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (m / m.gcd p)))
    (fun k => P (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m)) (a, k)))

/-- The grouped cyclic projections commute with every p-blocked letter.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`. -/
theorem stepOrbitProjection_mul_blockTensor (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (A : MPSTensor d D) (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (p : ℕ) (a : Fin (m.gcd p)) (i : Fin (blockPhysDim d p)) :
    stepOrbitProjection P p a * blockTensor A p i =
      blockTensor A p i * stepOrbitProjection P p a :=
  stepOrbitProjection_mul_evalWord P A hshift p a (wordOfBlock d p i) (length_wordOfBlock d p i)

/-- The blocked adjoint transfer map advances the original projectors by p steps.
Source: arXiv:1708.00029, final display in the proof of `lem:blocking-arbitrary`. -/
theorem adjoint_blockTensor_projection (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1)) (p : ℕ) (u : Fin m) :
    Kraus.transferMap (fun i => (blockTensor A p i)ᴴ) (P u) = P (u + (p : Fin m)) := by
  have hword (i : Fin (blockPhysDim d p)) :
      P u * blockTensor A p i = blockTensor A p i * P (u + (p : Fin m)) := by
    simpa only [blockTensor, Kraus.blockTensor, length_wordOfBlock, nsmul_one] using
      projector_mul_evalWord_eq_evalWord_mul_projector P A hshift u (wordOfBlock d p i)
  simp only [Kraus.transferMap_apply, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, hword]
  simp only [← Matrix.mul_assoc, ← Finset.sum_mul,
    leftCanonical_blockTensor A p hA, Matrix.one_mul]

/-- A p-blocked letter is the sum of its diagonal step-orbit corners.
Source: arXiv:1708.00029, paragraph following `lem:unique-dec`. -/
theorem blockTensor_eq_sum_stepOrbit_corners (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (A : MPSTensor d D) (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (p : ℕ) (i : Fin (blockPhysDim d p)) :
    blockTensor A p i = ∑ a, stepOrbitProjection P p a * blockTensor A p i *
      stepOrbitProjection P p a := by
  have hcorner (a : Fin (m.gcd p)) :
      stepOrbitProjection P p a * blockTensor A p i * stepOrbitProjection P p a =
        stepOrbitProjection P p a * blockTensor A p i := by
    rw [Matrix.mul_assoc, ← stepOrbitProjection_mul_blockTensor P A hshift,
      ← Matrix.mul_assoc, (stepOrbitProjection_isOrthogonalProjection P hproj hsum p a).2]
  simp only [hcorner, ← Finset.sum_mul, sum_stepOrbitProjection, hsum, Matrix.one_mul]

/-- Compress the step-orbit corners to nonzero left-canonical blocks without changing any MPV.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, the block construction before
its final peripheral-spectrum argument. No irreducibility or period conclusion is asserted here. -/
theorem exists_stepOrbit_blockDecomposition
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hne : ∀ u, P u ≠ 0) (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1)) (p : ℕ) :
    ∃ (dim : Fin (m.gcd p) → ℕ)
      (blocks : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
      (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ),
      (∀ a, 0 < dim a) ∧ (∑ a, dim a) = D ∧
      (∀ a, IsLeftCanonical (blocks a)) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      (∀ a, (V a)ᴴ * V a = 1) ∧
      (∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a) ∧
      (∀ a i, blocks a i = (V a)ᴴ * blockTensor A p i * V a) := by
  obtain ⟨dim, blocks, φ, V, hTP, hSame, hTrace, hIntertwine, hMul, hStar,
    hLetter, hViso, hVrange, hEmbed⟩ :=
    exists_blockDecomp_of_commuting_projections_with_letter_and_isometry
      (blockTensor A p) (stepOrbitProjection P p)
      (stepOrbitProjection_isOrthogonalProjection P hproj hsum p)
      ((sum_stepOrbitProjection P p).trans hsum) (leftCanonical_blockTensor A p hA)
      (stepOrbitProjection_mul_blockTensor P A hshift p)
  have hentries (a : Fin (m.gcd p)) (i : Fin (blockPhysDim d p)) :
      blocks a i = (V a)ᴴ * blockTensor A p i * V a := by
    have h := congrArg (fun X => (V a)ᴴ * X * V a)
      ((hEmbed a (blocks a i)).symm.trans (hLetter a i))
    simp only [← hVrange, Matrix.mul_assoc, hViso, Matrix.mul_one] at h
    simpa only [← Matrix.mul_assoc, hViso, Matrix.one_mul] using h
  refine ⟨dim, blocks, V, ?_, ?_, hTP, hSame, hViso, hVrange, hentries⟩
  · intro a
    apply Nat.pos_of_ne_zero
    intro ha
    apply stepOrbitProjection_ne_zero P hproj hsum hne p a
    rw [← hVrange]
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk := k.isLt
    omega
  · have hdim (a : Fin (m.gcd p)) : (dim a : ℂ) = (stepOrbitProjection P p a).trace := by
      simpa [mpv, coeff] using hTrace a 0 Fin.elim0
    have htotal : (∑ a, (dim a : ℂ)) = (D : ℂ) := by
      rw [Finset.sum_congr rfl (fun a _ => hdim a), ← Matrix.trace_sum,
        sum_stepOrbitProjection, hsum, Matrix.trace_one]
      simp
    exact_mod_cast htotal

end MPSTensor
