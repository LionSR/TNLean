/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Overlap
import QICLean.Analysis.Topology.GramMatrixLI

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Star
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import QICLean.Analysis.Subspace.FamilyImage

/-!
# Basis of normal tensors (BNT) and matching theory

This module combines two natural units:

## Part 1: Eventual linear independence of basis tensors

The **basis of normal tensors** (BNT) of a tensor, Definition 4.2 of arXiv:2011.12127,
lines 1846–1850, and arXiv:1606.00608, lines 271–274, is
`MPSTensor.IsCPSVBasisOfNormalTensors` in `TNLean.MPS.CanonicalForm.Definitions`. Its last
clause asks that the matrix product vectors of the basis tensors be eventually linearly
independent.

This part provides a criterion for that clause: if pairwise overlaps of a finite family of
MPV states converge to the Kronecker delta (i.e. the Gram matrix tends to the identity), then
the states are eventually linearly independent.
The finite-index and two-family forms of this criterion are the linear-independence
conditions used in the CPSV proof of arXiv:1606.00608, Theorem 2.10.

## Part 2: BNT matching theory (from `BNTMatching`)

Provides the **permutation-matching** linear-algebra results for the proof of
Theorem 4.4 of arXiv:2011.12127 (Cirac–Pérez-García–Schuch–Verstraete, RMP 2021).

### Pure linear algebra

* `exists_invertible_changeBasis`: If two finite families of vectors `v, w : Fin g → V` in a
  complex vector space are both linearly independent and span the same subspace, then there is an
  invertible `g × g` coefficient matrix `U` expressing each `w j` as a linear combination
  `w j = ∑ i, U i j • v i`.

### MPS application

* `MPSTensor.eventually_exists_invertible_changeBasis`: If two BNT-like families produce MPV
  states that are eventually linearly independent and eventually span the same subspace, then
  for all sufficiently large system sizes there is an invertible coefficient matrix `U_N`
  expressing one family in terms of the other.

## Intended use in Theorem 4.4

1. **Block separation** produces two BNT families `A_bnt` and `B_bnt` from tensors `A_total` and
   `B_total` that generate the same MPV family.
2. This module supplies the invertible `U_N` relating the two BNT families at each large `N`.
3. The permutation-rigidity argument identifies the limiting coefficient matrix as a
   permutation times diagonal phases, using the overlap orthonormality conditions.
-/

open MPTensor

open scoped BigOperators InnerProductSpace Matrix
open Filter Finset

namespace MPSTensor

/--
If the MPV overlaps of a finite index family `A j` converge to an orthonormal
Gram matrix, then the MPV states `mpvState (A j) N` are eventually linearly
independent.

This is the finite-index formulation of
`Matrix.eventually_linearIndependent_of_gram_tendsto_id`.
-/
lemma eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal
    {d : ℕ} {ι : Type*} [Finite ι] {dim : ι → ℕ}
    (A : (j : ι) → MPSTensor d (dim j))
    (h_self : ∀ j,
      Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (h_cross : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (α := Fin d) (A i) (A j) N) atTop (nhds (0 : ℂ))) :
    ∀ᶠ N in atTop,
      LinearIndependent ℂ (fun j : ι => mpvState (α := Fin d) (A j) N) := by
  classical
  -- Work in a fixed Hilbert space containing all `MPVSpace (Fin d) N` as orthogonal summands.
  let V := lp (fun N : ℕ => MPVSpace (Fin d) N) 2
  -- Embed each `mpvState (A j) N : MPVSpace (Fin d) N` into the `N`-th summand of `V`.
  let v : ι → ℕ → V := fun j N => lp.single 2 N (mpvState (α := Fin d) (A j) N)
  -- First show convergence of the inner products `⟪mpvState (A i) N, mpvState (A j) N⟫`.
  have hInnerState : ∀ i j : ι,
      Tendsto (fun N =>
        ⟪mpvState (α := Fin d) (A i) N, mpvState (α := Fin d) (A j) N⟫_ℂ)
        atTop (nhds (if i = j then (1 : ℂ) else 0)) := by
    intro i j
    by_cases h : i = j
    · subst h
      -- `mpvOverlap = star mpvInner`, so `.star` converts the limit.
      have h1 : Tendsto (fun N => star (mpvInner (α := Fin d) (A i) (A i) N)) atTop (nhds 1) :=
        (h_self i).congr fun N =>
          mpvOverlap_eq_star_mpvInner (A := A i) (B := A i) N
      simpa [mpvInner] using h1.star
    · have h1 : Tendsto (fun N => star (mpvInner (α := Fin d) (A i) (A j) N)) atTop (nhds 0) :=
        (h_cross i j h).congr fun N =>
          mpvOverlap_eq_star_mpvInner (A := A i) (B := A j) N
      simpa [mpvInner, ite_eq_right h] using h1.star
  -- Translate the Gram convergence to the embedded vectors `v` in the fixed space `V`.
  have hGram : ∀ i j : ι,
      Tendsto (fun N => ⟪v i N, v j N⟫_ℂ)
        atTop (nhds (if i = j then (1 : ℂ) else 0)) := fun i j =>
    -- `⟪v i N, v j N⟫ = ⟪lp.single 2 N (mpvState A i N), ...⟫ = ⟪mpvState A i N, ...⟫`
    -- by `lp.inner_single_left` and `lp.single_apply_self`.
    (hInnerState i j).congr fun N => by
      simp only [v]
      rw [lp.inner_single_left, lp.single_apply_self]
  -- Apply the Gram-matrix criterion in the fixed inner product space `V`.
  have hLI_emb : ∀ᶠ N in atTop, LinearIndependent ℂ (fun j : ι => v j N) :=
    Matrix.eventually_linearIndependent_of_gram_tendsto_id (v := v) hGram
  -- Pull back linear independence along the linear map `lp.lsingle 2 N`.
  refine hLI_emb.mono ?_
  intro N hN
  -- `lp.lsingle 2 N` is the linear map `MPVSpace (Fin d) N →ₗ[ℂ] V` sending `x` to
  -- `lp.single 2 N x`.
  let fN : MPVSpace (Fin d) N →ₗ[ℂ] V :=
    lp.lsingle (𝕜 := ℂ) (E := fun N : ℕ => MPVSpace (Fin d) N) 2 N
  -- Rewrite the embedded family as `fN ∘ mpvState` and apply `LinearIndependent.of_comp`.
  have hN' : LinearIndependent ℂ (fun j : ι => fN (mpvState (α := Fin d) (A j) N)) := by
    convert hN using 1
    ext j L i
    rfl
  exact LinearIndependent.of_comp fN hN'

/-- **Eventual coefficient extraction from eventual linear independence.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182 invokes Lemma
`Lem1` to rule out a vanishing-overlap alternative. Once Lemma `Lem1` gives
linear independence for all sufficiently large lengths, equality of two finite
linear combinations forces equality of the corresponding coefficients for all
sufficiently large lengths. -/
lemma coefficient_eventually_eq_of_eventually_linearIndependent
    {ι : Type*} [Fintype ι]
    {E : ℕ → Type*} [∀ N, AddCommGroup (E N)] [∀ N, Module ℂ (E N)]
    (v : (N : ℕ) → ι → E N) (a b : ℕ → ι → ℂ)
    (hLI : ∀ᶠ N in atTop, LinearIndependent ℂ (v N))
    (hEq : ∀ᶠ N in atTop, ∑ i : ι, a N i • v N i = ∑ i : ι, b N i • v N i) :
    ∀ᶠ N in atTop, ∀ i : ι, a N i = b N i := by
  refine (hLI.and hEq).mono ?_
  intro N hN i
  rcases hN with ⟨hLIN, hEqN⟩
  have hdiff : ∑ j : ι, (a N j - b N j) • v N j = 0 := by
    simpa [Finset.sum_sub_distrib, sub_smul] using sub_eq_zero.mpr hEqN
  have hzero := Fintype.linearIndependent_iff.mp hLIN
    (fun j : ι => a N j - b N j) hdiff
  exact sub_eq_zero.mp (hzero i)

/-- Eventual linear independence for the union of two asymptotically orthonormal
MPV families whose mixed overlaps vanish.

Source context: arXiv:1606.00608, Lemma `Lem1`, lines 1131--1133, and the
application in Theorem `thm1`, proof line 1182, where the
linear-independence corollary is applied after adjoining one block from one BNT
family to the other family.  This auxiliary lemma records the symmetric
two-family strengthening of that Gram-matrix input; it is not the equal-MPV
coefficient comparison of lines 1184--1192. -/
lemma eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal
    {d : ℕ} {gA gB : ℕ} {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (α := Fin d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (α := Fin d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (α := Fin d) (B k₁) (B k₂) N) atTop (nhds 0))
    (hAB : ∀ j k,
      Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (B k) N) atTop (nhds 0)) :
    ∀ᶠ N in atTop,
      LinearIndependent ℂ
        (Sum.elim
          (fun j : Fin gA => mpvState (α := Fin d) (A j) N)
          (fun k : Fin gB => mpvState (α := Fin d) (B k) N)) := by
  classical
  let C : (x : Sum (Fin gA) (Fin gB)) → MPSTensor d (Sum.elim dimA dimB x) :=
    Sum.rec (motive := fun x => MPSTensor d (Sum.elim dimA dimB x)) A B
  have h_self : ∀ x,
      Tendsto (fun N => mpvOverlap (α := Fin d) (C x) (C x) N) atTop
        (nhds (1 : ℂ)) := by
    intro x
    cases x with
    | inl j => simpa [C] using hA_self j
    | inr k => simpa [C] using hB_self k
  have h_cross : ∀ x y, x ≠ y →
      Tendsto (fun N => mpvOverlap (α := Fin d) (C x) (C y) N) atTop
        (nhds (0 : ℂ)) := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            have hij : i ≠ j := by
              intro hij
              apply hxy
              simp [hij]
            simpa [C] using hA_off i j hij
        | inr k =>
            simpa [C] using hAB i k
    | inr k =>
        cases y with
        | inl i =>
            simpa [C] using tendsto_mpvOverlap_zero_swap (A i) (B k) (hAB i k)
        | inr l =>
            have hkl : k ≠ l := by
              intro hkl
              apply hxy
              simp [hkl]
            simpa [C] using hB_off k l hkl
  have hLI :=
    MPSTensor.eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal C
      h_self h_cross
  refine hLI.mono ?_
  intro N hN
  have key :
      (fun x : Sum (Fin gA) (Fin gB) => mpvState (α := Fin d) (C x) N) =
        Sum.elim
          (fun j : Fin gA => mpvState (α := Fin d) (A j) N)
          (fun k : Fin gB => mpvState (α := Fin d) (B k) N) := by
    funext x
    cases x <;> rfl
  rw [← key]
  exact hN

end MPSTensor

/-! ## Pure linear algebra: invertible change of basis -/

/-! ## MPS application -/

namespace MPSTensor

open MPSTensor

/--
**Eventually invertible change-of-basis matrix from equal spans.**

Given two BNT-like families of MPS tensors whose pairwise overlaps converge to orthonormality
(so both are eventually linearly independent), and whose MPV state spans eventually agree,
there is—for all large enough `N`—an invertible `g × g` coefficient matrix `U_N`
satisfying

`mpvState (B j) N = ∑ i, U_N i j • mpvState (A i) N`.

This converts the equal-MPV-subspace condition into a matrix equation whose
asymptotics can then be analysed in the permutation-matching step of Theorem 4.4.

**Local fix (eventual span equality):** The source comparison holds only on a
finite tail.  Accordingly, this result assumes eventual span equality rather
than equality at every length.  See
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source context: CPSV16, arXiv:1606.00608, lines 522--525 and 1305--1307.
-/
lemma eventually_exists_invertible_changeBasis
    {d g : ℕ} {dimA dimB : Fin g → ℕ}
    (A : (j : Fin g) → MPSTensor d (dimA j))
    (B : (j : Fin g) → MPSTensor d (dimB j))
    (hA_diag : ∀ j,
      Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (α := Fin d) (A i) (A j) N) atTop (nhds (0 : ℂ)))
    (hB_diag : ∀ j,
      Tendsto (fun N => mpvOverlap (α := Fin d) (B j) (B j) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (α := Fin d) (B i) (B j) N) atTop (nhds (0 : ℂ)))
    (hspan : ∀ᶠ N : ℕ in atTop,
      Submodule.span ℂ (Set.range (fun j : Fin g => mpvState (α := Fin d) (A j) N)) =
      Submodule.span ℂ (Set.range (fun j : Fin g => mpvState (α := Fin d) (B j) N))) :
    ∀ᶠ N in atTop, ∃ U : Matrix (Fin g) (Fin g) ℂ,
      U.det ≠ 0 ∧
      ∀ j : Fin g,
        mpvState (α := Fin d) (B j) N =
          ∑ i : Fin g, U i j • mpvState (α := Fin d) (A i) N := by
  -- Both families are eventually LI.
  have hA_li := eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal A hA_diag hA_off
  have hB_li := eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal B hB_diag hB_off
  -- Intersect the three eventual conditions.
  filter_upwards [hA_li, hB_li, hspan] with N hA_N hB_N hspanN
  -- Apply the pure linear-algebra change-of-basis lemma.
  exact exists_invertible_changeBasis
    (fun j => mpvState (α := Fin d) (A j) N)
    (fun j => mpvState (α := Fin d) (B j) N)
    hA_N hB_N hspanN

end MPSTensor
