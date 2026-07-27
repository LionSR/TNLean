/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVRepresentativeGroupedLemmaL
import TNLean.MPS.MPDO.LinearMarkedTensor

/-!
# Lemma L in the original bond coordinates of a literal CPSV canonical form

A literal CPSV canonical-form tensor is reconstructed from its retained grouped tensor by a
block-diagonal similarity and a rectangular coisometry.  This file proves that closed chains with
one marked physical letter pass across the rectangular reconstruction, identifies physical linear
marks with the full grouped marked tensor, and obtains Lemma L on the original bond space.

Inactive listed coordinates remain in every full grouped tensor.  Their marked blocks vanish from
the zero raw weight; no statement is made about the corresponding unweighted blocks.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.3, Lemma L, lines 1835--1858, and Proposition 4.13,
  lines 1873--1887.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d e D n : ℕ}

/-- A closed chain with an arbitrary marked first matrix is unchanged by a rectangular
coisometric reconstruction.

If every ordinary letter satisfies `A i = Vᴴ * B i * V`, the marked matrices satisfy the same
relation, and `V * Vᴴ = 1`, then the trace with any tail word agrees.  The tail may be empty: the
marked first matrix still makes the chain nonempty, so the false unmarked length-zero assertion is
not used.

Source: arXiv:1606.00608, Appendix C.3, lines 1848--1858. -/
theorem trace_marked_mul_evalWord_of_coisometry_reconstruction
    (A : MPSTensor d D) (B : MPSTensor d n)
    (V : Matrix (Fin n) (Fin D) ℂ) (hV : V * Vᴴ = 1)
    (hReconstruct : ∀ i, A i = Vᴴ * B i * V)
    (C : Matrix (Fin D) (Fin D) ℂ) (E : Matrix (Fin n) (Fin n) ℂ)
    (hMarked : C = Vᴴ * E * V) (w : List (Fin d)) :
    Matrix.trace (C * evalWord A w) = Matrix.trace (E * evalWord B w) := by
  have hChain : ∀ (w : List (Fin d))
      (C : Matrix (Fin D) (Fin D) ℂ) (E : Matrix (Fin n) (Fin n) ℂ),
      C = Vᴴ * E * V →
      C * evalWord A w = Vᴴ * (E * evalWord B w) * V := by
    intro w
    induction w with
    | nil =>
        intro C E hCE
        simp [hCE]
    | cons i w ih =>
        intro C E hCE
        simp only [evalWord_cons]
        have hNext : C * A i = Vᴴ * (E * B i) * V := by
          rw [hCE, hReconstruct i]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc V Vᴴ, hV, Matrix.one_mul]
        simpa only [Matrix.mul_assoc] using ih (C * A i) (E * B i) hNext
  rw [hChain w C E hMarked]
  exact Matrix.trace_conjTranspose_mul_mul_of_mul_conjTranspose_eq_one V hV _

/-- Linear physical marking commutes with a rectangular coisometric reconstruction. -/
theorem linearMarkedTensor_coisometry_reconstruction
    (f : Fin e → Fin d → ℂ) (A : MPSTensor d D) (B : MPSTensor d n)
    (V : Matrix (Fin n) (Fin D) ℂ)
    (hReconstruct : ∀ i, A i = Vᴴ * B i * V) (u : Fin e) :
    linearMarkedTensor f A u = Vᴴ * linearMarkedTensor f B u * V := by
  classical
  simp only [linearMarkedTensor]
  simp_rw [hReconstruct]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- A closed chain with one linear physical mark is unchanged by a rectangular coisometric
reconstruction, including when its tail word is empty. -/
theorem trace_linearMarkedTensor_mul_evalWord_of_coisometry_reconstruction
    (f : Fin e → Fin d → ℂ) (A : MPSTensor d D) (B : MPSTensor d n)
    (V : Matrix (Fin n) (Fin D) ℂ) (hV : V * Vᴴ = 1)
    (hReconstruct : ∀ i, A i = Vᴴ * B i * V)
    (u : Fin e) (w : List (Fin d)) :
    Matrix.trace (linearMarkedTensor f A u * evalWord A w) =
      Matrix.trace (linearMarkedTensor f B u * evalWord B w) :=
  trace_marked_mul_evalWord_of_coisometry_reconstruction A B V hV hReconstruct
    _ _ (linearMarkedTensor_coisometry_reconstruction f A B V hReconstruct u) w

private theorem cast_linearMarkedTensor
    {m n : ℕ} (h : m = n) (f : Fin e → Fin d → ℂ) (A : MPSTensor d m) :
    cast (congr_arg (MPSTensor e) h) (linearMarkedTensor f A) =
      linearMarkedTensor f (cast (congr_arg (MPSTensor d) h) A) := by
  subst n
  rfl

namespace CPSVCanonicalFormData.ActiveBNTRefinement

variable {A : MPSTensor d D} {data : CPSVCanonicalFormData A}

/-- Linear marking of the full grouped tensor is exactly the full grouped marked tensor formed
from the representative linear marks.

Active copies carry their raw weight and phase.  Every inactive listed coordinate remains present,
but its marked block is zero because its raw weight is zero.

Source: arXiv:1606.00608, Appendix C.3, lines 1848--1858. -/
theorem linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor
    (ref : data.ActiveBNTRefinement) (f : Fin e → Fin d → ℂ) :
    linearMarkedTensor f ref.groupedTensor =
      ref.groupedMarkedTensor
        (fun j => linearMarkedTensor f (data.blocks (data.activeRepresentativeIndex j))) := by
  classical
  rw [← funext ref.regroupedTensor_eq_groupedTensor,
    linearMarkedTensor_toTensorFromBlocks]
  rw [groupedMarkedTensor]
  have hBlocks : ∀ k,
      data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) =
        ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f
            (data.blocks (data.activeRepresentativeIndex j))) k := by
    intro k
    funext u
    by_cases hk : data.weights k ≠ 0
    · let ka : data.Active := ⟨k, hk⟩
      change data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) u =
        ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f (data.blocks (data.activeRepresentativeIndex j))) k u
      rw [ref.groupedMarkedBlocks_active _ ka, ref.regroupedBlocksActive ka]
      rw [cast_linearMarkedTensor (ref.copyDimEq ka)]
      simp only [linearMarkedTensor, Pi.smul_apply, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      ring
    · change data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) u =
        ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f (data.blocks (data.activeRepresentativeIndex j))) k u
      have hzero : data.weights k = 0 := not_ne_iff.mp hk
      rw [hzero]
      simp [groupedMarkedBlocks, hk]
  unfold toTensorFromBlocks
  funext u
  change (Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv)
      (Matrix.blockDiagonal' fun k =>
        data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) u) =
    (Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv)
      (Matrix.blockDiagonal' fun k =>
        (1 : ℂ) • ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f
            (data.blocks (data.activeRepresentativeIndex j))) k u)
  have hBlockDiagonal :
      (Matrix.blockDiagonal' fun k =>
        data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) u) =
      (Matrix.blockDiagonal' fun k =>
        (1 : ℂ) • ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f
            (data.blocks (data.activeRepresentativeIndex j))) k u) := by
    congr 1
    funext k
    simpa using congrFun (hBlocks k) u
  rw [hBlockDiagonal]

/-- **Lemma L in the original bond coordinates of a literal CPSV canonical form.**

Equality of every closed chain with one marked physical letter implies equality of the two linear
marked tensors on the original bond space.  The proof uses the original ambient coisometry in the
orientation `U * Uᴴ = 1`, the listed block gauge, and the full grouped tensor including inactive
zero-weight coordinates.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858. -/
theorem linearMarkedTensor_eq_of_trace_agree
    (ref : data.ActiveBNTRefinement) (f g : Fin e → Fin d → ℂ)
    (hTrace : ∀ (L : ℕ) (u : Fin e) (w : Fin L → Fin d),
      Matrix.trace (linearMarkedTensor f A u * evalWord A (List.ofFn w)) =
        Matrix.trace (linearMarkedTensor g A u * evalWord A (List.ofFn w))) :
    linearMarkedTensor f A = linearMarkedTensor g A := by
  classical
  let X := globalGaugeOfBlocks ref.listedGauge
  let B : MPSTensor d (∑ k : Fin data.r, data.dim k) := fun i =>
    (X : Matrix _ _ ℂ) * ref.groupedTensor i *
      (↑(X⁻¹) : Matrix _ _ ℂ)
  have hReconstruct : ∀ i, A i = ref.ambientCoisometryᴴ * B i * ref.ambientCoisometry := by
    intro i
    exact ref.reconstructGrouped i
  have hGauge : ∀ i, B i =
      (X : Matrix _ _ ℂ) * ref.groupedTensor i *
        (↑(X⁻¹) : Matrix _ _ ℂ) := fun _ => rfl
  let Cf := fun j : Fin data.activePhaseClasses.g =>
    linearMarkedTensor f (data.blocks (data.activeRepresentativeIndex j))
  let Cg := fun j : Fin data.activePhaseClasses.g =>
    linearMarkedTensor g (data.blocks (data.activeRepresentativeIndex j))
  have hGroupedTrace : ∀ (L : ℕ) (u : Fin e) (w : Fin L → Fin d),
      Matrix.trace (ref.groupedMarkedTensor Cf u * evalWord ref.groupedTensor (List.ofFn w)) =
        Matrix.trace (ref.groupedMarkedTensor Cg u * evalWord ref.groupedTensor (List.ofFn w)) := by
    intro L u w
    rw [← ref.linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor f,
      ← ref.linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor g]
    have hf := trace_linearMarkedTensor_mul_evalWord_of_coisometry_reconstruction
      f A B ref.ambientCoisometry ref.ambientCoisometric hReconstruct u (List.ofFn w)
    have hg := trace_linearMarkedTensor_mul_evalWord_of_coisometry_reconstruction
      g A B ref.ambientCoisometry ref.ambientCoisometric hReconstruct u (List.ofFn w)
    have hfg := hTrace L u w
    have hGaugeF := trace_linearMarkedTensor_mul_evalWord_gauge
      f X hGauge u (List.ofFn w)
    have hGaugeG := trace_linearMarkedTensor_mul_evalWord_gauge
      g X hGauge u (List.ofFn w)
    exact hGaugeF.symm.trans (hf.symm.trans (hfg.trans (hg.trans hGaugeG)))
  have hRepresentative : ∀ j, Cf j = Cg j :=
    ref.groupedMarkedTensor_basis_eq_of_trace_agree Cf Cg hGroupedTrace
  have hGrouped : linearMarkedTensor f ref.groupedTensor =
      linearMarkedTensor g ref.groupedTensor := by
    rw [ref.linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor f,
      ref.linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor g]
    congr 1
    funext j
    exact hRepresentative j
  funext u
  rw [linearMarkedTensor_coisometry_reconstruction f A B ref.ambientCoisometry
      hReconstruct u,
    linearMarkedTensor_coisometry_reconstruction g A B ref.ambientCoisometry
      hReconstruct u,
    linearMarkedTensor_gauge f X hGauge u,
    linearMarkedTensor_gauge g X hGauge u,
    hGrouped]

/-- Physical first-site Lemma L in the original bond coordinates of a literal CPSV canonical
form. -/
theorem insertedTensor_eq_of_firstSiteActionAgree
    (ref : data.ActiveBNTRefinement) {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree A Y Z) :
    insertedTensor Y A = insertedTensor Z A := by
  apply ref.linearMarkedTensor_eq_of_trace_agree Y Z
  intro L u w
  simpa [linearMarkedTensor, insertedTensor] using
    hAct.trace_evalWord u (List.ofFn w)

end CPSVCanonicalFormData.ActiveBNTRefinement

namespace IsCPSVCanonicalForm

/-- Predicate-level form of Lemma L in the original bond coordinates of a literal CPSV canonical
form. -/
theorem linearMarkedTensor_eq_of_trace_agree
    (A : MPSTensor d D) (hCanonical : IsCPSVCanonicalForm A)
    (f g : Fin e → Fin d → ℂ)
    (hTrace : ∀ (L : ℕ) (u : Fin e) (w : Fin L → Fin d),
      Matrix.trace (linearMarkedTensor f A u * evalWord A (List.ofFn w)) =
        Matrix.trace (linearMarkedTensor g A u * evalWord A (List.ofFn w))) :
    linearMarkedTensor f A = linearMarkedTensor g A := by
  let data := Classical.choice hCanonical
  let ref := data.activeBNTRefinement
  exact ref.linearMarkedTensor_eq_of_trace_agree f g hTrace

/-- Predicate-level physical first-site Lemma L in the original bond coordinates of a literal
CPSV canonical form. -/
theorem insertedTensor_eq_of_firstSiteActionAgree
    (A : MPSTensor d D) (hCanonical : IsCPSVCanonicalForm A)
    {Y Z : Matrix (Fin d) (Fin d) ℂ} (hAct : FirstSiteActionAgree A Y Z) :
    insertedTensor Y A = insertedTensor Z A := by
  let data := Classical.choice hCanonical
  let ref := data.activeBNTRefinement
  exact ref.insertedTensor_eq_of_firstSiteActionAgree hAct

end IsCPSVCanonicalForm

end MPSTensor
