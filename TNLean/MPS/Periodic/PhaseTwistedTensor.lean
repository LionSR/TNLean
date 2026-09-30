/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.SectorLift
import TNLean.MPS.Periodic.PhaseDistribution
import TNLean.Algebra.UnitaryCongruence
import TNLean.MPS.CanonicalForm.SectorComparison.CyclicSectorRelation
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Complex.Circle

/-!
# Cyclic phase twisting of periodic matrix-product tensors

The phase redistribution in arXiv:1708.00029, Section 4.1, lines 765--806,
changes each letter by a scalar on its outgoing cyclic sector. The theorems
below evaluate the resulting tensor on arbitrary words. The phases multiply
along the sector path, which is the matrix part of equation
`eq:Aprime-is-cPA`.
-/

open scoped Matrix BigOperators
namespace MPSTensor
variable {d D m : ℕ}

/-- Twisting outgoing cyclic sectors by unit-modulus phases preserves trace
    preservation. This is the unitary part of the construction in
    arXiv:1708.00029, Section 4.1, lines 788--806. -/
theorem phaseTwisted_tracePreserving
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hsum : ∑ u : Fin m, P u = 1)
    (hζ : ∀ u, ‖ζ u‖ = 1)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∑ i : Fin d,
      (∑ u : Fin m, ζ u • (P u * A i))ᴴ *
        (∑ u : Fin m, ζ u • (P u * A i)) = 1 := by
  let U : MatrixAlg D := ∑ u : Fin m, ζ u • P u
  have hPmul : ∀ u v : Fin m, P u * P v = if u = v then P u else 0 := by
    intro u v
    split_ifs with huv
    · subst v; exact (hP u).2
    · exact horth u v huv
  have hU : Uᴴ * U = 1 := by
    exact (Matrix.mem_unitaryGroup_iff').mp
      (Matrix.weighted_sum_mem_unitaryGroup P (fun u => (hP u).1)
        hPmul hsum ζ hζ)
  have hletter (i : Fin d) : ∑ u : Fin m, ζ u • (P u * A i) = U * A i := by
    simp [U, Finset.sum_mul]
  simp_rw [hletter, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U,
    hU, one_mul]
  exact hTP

variable [NeZero m]

/-- The adjoint transfer map advances a cyclic projection by one sector
under the paper's outgoing-sector convention.
Source: arXiv:1708.00029, equation `eq:peripheral` and the proof of
Lemma `lem:blocking-arbitrary`, lines 451--459. -/
theorem adjointTransferMap_cyclic_projection_shift
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (u : Fin m) :
    Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P u) = P (u + 1) := by
  rw [Kraus.transferMap_apply]
  calc
    (∑ i : Fin d, (A i)ᴴ * P u * ((A i)ᴴ)ᴴ) =
        ∑ i : Fin d, (A i)ᴴ * A i * P (u + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
            hshift u i, ← Matrix.mul_assoc]
    _ = (∑ i : Fin d, (A i)ᴴ * A i) * P (u + 1) := by rw [Finset.sum_mul]
    _ = P (u + 1) := by rw [hTP, Matrix.one_mul]

/-- After `p` sites the adjoint transfer map advances the cyclic sector
by `p`. Source: arXiv:1708.00029, proof of Lemma
`lem:blocking-arbitrary`, lines 451--459. -/
theorem adjointTransferMap_pow_cyclic_projection_shift
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (p : ℕ) (u : Fin m) :
    ((Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ p) (P u) =
      P (u + p • (1 : Fin m)) := by
  induction p generalizing u with
  | zero => simp
  | succ p ih =>
      rw [pow_succ', Module.End.mul_apply, ih u,
        adjointTransferMap_cyclic_projection_shift P A hTP hshift (u + p • (1 : Fin m))]
      congr 1
      simp only [add_smul, one_smul]
      abel_nf

/-- The adjoint transfer map of the blocked tensor advances the original
cyclic projections by `p` sectors. Source: arXiv:1708.00029,
proof of Lemma `lem:blocking-arbitrary`, lines 451--459. -/
theorem adjointTransferMap_blockTensor_cyclic_projection_shift
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (p : ℕ) (u : Fin m) :
    Kraus.transferMap (d := blockPhysDim d p) (D := D)
      (fun I => (blockTensor A p I)ᴴ) (P u) =
        P (u + p • (1 : Fin m)) := by
  rw [transferMap_adjoint_blocked_eq_pow]
  exact adjointTransferMap_pow_cyclic_projection_shift P A hTP hshift p u

/-- A word carries its starting cyclic sector forward by its length.
Source: arXiv:1708.00029, equation `eq:Aoffdiag`, lines 335--341. -/
theorem cyclic_projection_evalWord_shift
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (u : Fin m) (w : List (Fin d)) :
    P u * Kraus.evalWord A w =
      Kraus.evalWord A w * P (u + w.length • (1 : Fin m)) := by
  induction w generalizing u with
  | nil => simp [Kraus.evalWord]
  | cons i w ih =>
      rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, hshift u i,
        Matrix.mul_assoc, ih (u + 1), ← Matrix.mul_assoc]
      congr 1
      simp only [List.length_cons, add_smul, one_smul]
      abel_nf

/-- A blocked letter advances the cyclic sector by `p`.
Source: arXiv:1708.00029, Section 4.1, lines 765--806. -/
theorem cyclic_projection_blockTensor_shift
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (p : ℕ) (u : Fin m) (I : Fin (blockPhysDim d p)) :
    P u * blockTensor A p I =
      blockTensor A p I * P (u + p • (1 : Fin m)) := by
  simpa only [blockTensor, Kraus.blockTensor, length_wordOfBlock] using
    cyclic_projection_evalWord_shift P A hshift u (wordOfBlock d p I)

/-- A blocked letter has no matrix corner except the one advancing the
starting sector by `p`. Source: arXiv:1708.00029, Section 4.1,
lines 765--806. -/
theorem cyclic_projection_blockTensor_corner_zero
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (p : ℕ) (u v : Fin m) (huv : u + p • (1 : Fin m) ≠ v)
    (I : Fin (blockPhysDim d p)) :
    P u * blockTensor A p I * P v = 0 := by
  rw [cyclic_projection_blockTensor_shift P A hshift p u I,
    Matrix.mul_assoc, horth _ _ huv, Matrix.mul_zero]

/-- Distinct orbits of the blocked shift have no matrix corners between
them. Source: arXiv:1708.00029, Section 4.1, lines 765--806. -/
theorem cyclic_projection_blockTensor_offOrbit_zero
    {ι : Type*} (p : ℕ) (α : Fin m → ι)
    (hα : ∀ u, α (u + p • (1 : Fin m)) = α u)
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (u v : Fin m) (huv : α u ≠ α v)
    (I : Fin (blockPhysDim d p)) :
    P u * blockTensor A p I * P v = 0 := by
  apply cyclic_projection_blockTensor_corner_zero P A horth hshift p u v _ I
  intro h
  apply huv
  rw [← hα u, h]

/-- The phase-weighted corner product along a word. Source: arXiv:1708.00029,
    equation `eq:Aprime-is-cPA`, lines 788--806. -/
def weightedCornerProd (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (ζ : Fin m → ℂ) : Fin m → List (Fin d) → MatrixAlg D
  | u, [] => P u
  | u, i :: w => ζ u • (P u * A i * weightedCornerProd P A ζ (u + 1) w)

private theorem weightedCornerProd_left
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (u v : Fin m) (w : List (Fin d)) :
    P v * weightedCornerProd P A ζ u w =
      if v = u then weightedCornerProd P A ζ u w else 0 := by
  cases w with
  | nil =>
      simp only [weightedCornerProd]
      split_ifs with h
      · subst v; exact (hP u).2
      · exact horth v u h
  | cons i w =>
      simp only [weightedCornerProd]
      split_ifs with h
      · subst v
        simp only [Matrix.mul_smul, ← Matrix.mul_assoc, (hP u).2]
      · calc
          P v * (ζ u • (P u * A i * weightedCornerProd P A ζ (u + 1) w)) =
              ζ u • ((P v * P u) * A i * weightedCornerProd P A ζ (u + 1) w) := by
                simp [Matrix.mul_assoc]
          _ = 0 := by rw [horth v u h]; simp

private theorem weightedCornerProd_sum_left
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (v : Fin m) (w : List (Fin d)) :
    P v * (∑ u : Fin m, weightedCornerProd P A ζ u w) =
      weightedCornerProd P A ζ v w := by
  rw [Finset.mul_sum]
  simp [weightedCornerProd_left P A ζ hP horth]

/-- Evaluation of the sector-phase-twisted tensor is the sum of its
    phase-weighted corner products. Source: arXiv:1708.00029,
    equation `eq:Aprime-is-cPA`, lines 788--806. -/
theorem evalWord_weightedCornerProd
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hsum : ∑ u : Fin m, P u = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (w : List (Fin d)) :
    Kraus.evalWord (fun i : Fin d => ∑ u : Fin m, ζ u • (P u * A i)) w =
      ∑ u : Fin m, weightedCornerProd P A ζ u w := by
  induction w with
  | nil => simpa [weightedCornerProd, Kraus.evalWord] using hsum.symm
  | cons i w ih =>
      rw [Kraus.evalWord_cons, ih]
      simp only [weightedCornerProd]
      calc
        (∑ v : Fin m, ζ v • (P v * A i)) *
            ∑ u : Fin m, weightedCornerProd P A ζ u w =
          ∑ v : Fin m, ζ v • ((P v * A i) *
            ∑ u : Fin m, weightedCornerProd P A ζ u w) := by
              simp [Finset.sum_mul]
        _ = ∑ v : Fin m, ζ v • (P v * A i *
            weightedCornerProd P A ζ (v + 1) w) := by
              apply Finset.sum_congr rfl
              intro v _
              congr 1
              calc
                (P v * A i) * (∑ u : Fin m, weightedCornerProd P A ζ u w) =
                    A i * (P (v + 1) *
                      ∑ u : Fin m, weightedCornerProd P A ζ u w) := by
                        rw [hshift, ← Matrix.mul_assoc]
                _ = A i * weightedCornerProd P A ζ (v + 1) w := by
                      rw [weightedCornerProd_sum_left P A ζ hP horth]
                _ = (P v * A i) * weightedCornerProd P A ζ (v + 1) w := by
                      rw [hshift, Matrix.mul_assoc]
                      have hrest := weightedCornerProd_left P A ζ hP horth
                        (v + 1) (v + 1) w
                      simpa using congrArg (fun X => A i * X) hrest.symm
        _ = ∑ v : Fin m, weightedCornerProd P A ζ v (i :: w) := by
              simp only [weightedCornerProd]

/-- Product of the site phases along a cyclic path. Source: arXiv:1708.00029,
    equation `eq:Aprime-is-cPA`, lines 788--806. -/
def phaseFactor (ζ : Fin m → ℂ) : Fin m → ℕ → ℂ
  | _, 0 => 1
  | u, n + 1 => ζ u * phaseFactor ζ (u + 1) n

/-- The recursive path phase is the finite product over its sites. Source:
    arXiv:1708.00029, equation `eq:Aprime-is-cPA`, lines 788--806. -/
theorem phaseFactor_eq_prod_range (ζ : Fin m → ℂ) (u : Fin m) (n : ℕ) :
    phaseFactor ζ u n = ∏ j ∈ Finset.range n, ζ (u + j • (1 : Fin m)) := by
  induction n generalizing u with
  | zero => simp [phaseFactor]
  | succ n ih =>
      rw [phaseFactor, Finset.prod_range_succ']
      rw [ih (u + 1)]
      simp only [add_nsmul, one_nsmul, add_assoc, zero_smul, add_zero]
      rw [mul_comm (ζ u)]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      abel_nf

/-- The weighted corner product is the ordinary corner product times its
    accumulated phase. Source: arXiv:1708.00029, equation
    `eq:Aprime-is-cPA`, lines 788--806. -/
theorem weightedCornerProd_eq_phaseFactor_cornerProd
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (u : Fin m) (w : List (Fin d)) :
    weightedCornerProd P A ζ u w =
      phaseFactor ζ u w.length • cornerProd P A u w := by
  induction w generalizing u with
  | nil => simp [weightedCornerProd, phaseFactor, cornerProd]
  | cons i w ih =>
      simp only [weightedCornerProd, phaseFactor, List.length_cons, cornerProd_cons]
      rw [ih (u + 1)]
      simp [smul_smul]

/-- Twisting each letter of a periodic tensor by sector phases distributes the
phase across every word. The sector starting at `u` acquires the product of
the phases at `u, u+1, ..., u+length(w)-1`.

Source: arXiv:1708.00029, equation `eq:Aprime-is-cPA`, lines 788--806. -/
theorem evalWord_phaseTwisted_sum
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hsum : ∑ u : Fin m, P u = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (w : List (Fin d)) :
    Kraus.evalWord (fun i : Fin d => ∑ u : Fin m, ζ u • (P u * A i)) w =
      ∑ u : Fin m,
        (∏ j ∈ Finset.range w.length, ζ (u + j • (1 : Fin m))) •
          cornerProd P A u w := by
  rw [evalWord_weightedCornerProd P A ζ hP horth hsum hshift]
  apply Finset.sum_congr rfl
  intro u _
  rw [weightedCornerProd_eq_phaseFactor_cornerProd,
    phaseFactor_eq_prod_range]

/-- At a blocked physical letter, the phase-twisted tensor is the sum of
cyclic corner blocks with the product of `p` consecutive one-site phases.
This is the matrix identity preceding the phase choice in
arXiv:1708.00029, equation `eq:Aprime-is-cPA`, lines 788--806. -/
theorem blockTensor_phaseTwisted_apply
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hsum : ∑ u : Fin m, P u = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (p : ℕ) (I : Fin (blockPhysDim d p)) :
    blockTensor (fun i : Fin d => ∑ u : Fin m, ζ u • (P u * A i)) p I =
      ∑ u : Fin m,
        (∏ j ∈ Finset.range p, ζ (u + j • (1 : Fin m))) •
          cornerProd P A u (wordOfBlock d p I) := by
  simpa only [blockTensor, Kraus.blockTensor, length_wordOfBlock] using
    evalWord_phaseTwisted_sum P A ζ hP horth hsum hshift (wordOfBlock d p I)

/-- The blocked-word phase formula with the sector projections visible.
This is the matrix identity in arXiv:1708.00029, equation
`eq:Aprime-is-cPA`, lines 788--806. -/
theorem blockTensor_phaseTwisted_apply_projection
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (ζ : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hsum : ∑ u : Fin m, P u = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (p : ℕ) (I : Fin (blockPhysDim d p)) :
    blockTensor (fun i : Fin d => ∑ u : Fin m, ζ u • (P u * A i)) p I =
      ∑ u : Fin m,
        (∏ j ∈ Finset.range p, ζ (u + j • (1 : Fin m))) •
          (P u * blockTensor A p I * P (u + p • (1 : Fin m))) := by
  rw [blockTensor_phaseTwisted_apply P A ζ hP horth hsum hshift p I]
  apply Finset.sum_congr rfl
  intro u _
  rw [cornerProd_eq_conj_evalWord P A hP hshift]
  simp only [length_wordOfBlock]
  rfl

/-- A cyclic family of root-of-unity phases on the blocked sectors can be
absorbed into the one-site letters. For a phase family `c` constant under the
blocked shift, this constructs `A'` with
`A'^[p]_w = Σ_u c_u P_u A^w P_{u+p}`.

This is the phase-distribution step in arXiv:1708.00029, equations
`eq:ZPA-is-cPA` and `eq:Aprime-is-cPA`, lines 765--806. The remaining
application to Theorem 4.1 must obtain the cyclic projectors and the phase
family from the equal-case gauge. -/
theorem exists_phaseTwistedTensor_blockTensor (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hsum : ∑ u : Fin m, P u = 1)
    (hshift : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (p : ℕ) (c : Fin m → Circle)
    (hcshift : ∀ u, c (u + p • (1 : Fin m)) = c u)
    (hcroot : ∀ u, c u ^ addOrderOf (p : ZMod m) = 1) :
    ∃ A' : MPSTensor d D,
      (∀ I : Fin (blockPhysDim d p),
        blockTensor A' p I = ∑ u : Fin m,
          (c u : ℂ) • (P u * blockTensor A p I * P (u + p • (1 : Fin m)))) ∧
      ((∑ i : Fin d, (A i)ᴴ * A i = 1) →
        ∑ i : Fin d, (A' i)ᴴ * A' i = 1) := by
  obtain ⟨δ, hδ⟩ := exists_phaseDistribution_fin c hcshift hcroot
  let ζ : Fin m → ℂ := fun u => (δ u : ℂ)
  let A' : MPSTensor d D := fun i => ∑ u : Fin m, ζ u • (P u * A i)
  refine ⟨A', ?_, ?_⟩
  · intro I
    change blockTensor (fun i : Fin d => ∑ u : Fin m, ζ u • (P u * A i)) p I = _
    rw [blockTensor_phaseTwisted_apply_projection P A ζ hP horth hsum hshift]
    apply Finset.sum_congr rfl
    intro u _
    have hζ : (∏ j ∈ Finset.range p, ζ (u + j • (1 : Fin m))) = (c u : ℂ) := by
      have hmap : ((∏ j ∈ Finset.range p, δ (u + j • (1 : Fin m)) : Circle) : ℂ) =
          ∏ j ∈ Finset.range p, ((δ (u + j • (1 : Fin m))) : ℂ) := by
        exact map_prod Circle.coeHom _ _
      calc
        (∏ j ∈ Finset.range p, ζ (u + j • (1 : Fin m))) =
            ((∏ j ∈ Finset.range p, δ (u + j • (1 : Fin m)) : Circle) : ℂ) := by
              simpa [ζ] using hmap.symm
        _ = (c u : ℂ) := congrArg (fun z : Circle => (z : ℂ)) (hδ u)
    rw [hζ]
  · intro hTP
    exact phaseTwisted_tracePreserving P A ζ hP horth hsum
      (fun u => Circle.norm_coe (δ u)) hTP
end MPSTensor
