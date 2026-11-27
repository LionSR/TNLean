/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Vertical.CPSVRepresentativeGroupedLemmaL
import TNLean.MPS.MPDO.Vertical.LinearMarkedTensor
import QICLean.Kraus.NormalCommutant
import TNLean.MPS.MPDO.Vertical.FigureEightPairwise
import TNLean.MPS.CanonicalForm.PhysicalReindex

/-!
# Lemma L in the original bond coordinates of a literal CPSV canonical form

A literal CPSV canonical-form tensor is reconstructed from its retained grouped tensor by a
block-diagonal similarity and a rectangular coisometry.  This file proves that closed chains with
one marked physical letter pass across the rectangular reconstruction, identifies physical linear
marks with the full grouped marked tensor, and obtains Lemma L on the original bond space.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.3, Lemma L, lines 1835--1858, and Proposition 4.13,
  lines 1873--1887.

## Figure 8 for literal CPSV canonical form

The reflected marked-chain identity identifies the Gram-dressed chains of two supplied vertical
corners of one representative.  Lemma L for literal CPSV canonical form then gives equality of the
two Gram-dressed tensors on the original horizontal bond space.  When the representative is normal,
commutant rigidity makes the two Gram matrices positive real scalar multiples of one another.

Inactive listed horizontal coordinates remain present throughout Lemma L; their contributions
vanish only through their zero raw weights.

### Main results

* `MPTensor.IsCPSVCanonicalForm.gramDressing_eq_of_two_grouped_corners`: the pairwise Figure 8
  identity under literal CPSV canonical form.
* `MPTensor.IsCPSVCanonicalForm.gram_eq_pos_smul_gram_of_two_grouped_corners`: the positive
  relative Gram scalar for a normal representative.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, proof of Proposition 4.13,
  Figures 7--8 and lines 1909--1921.
-/

open MPTensor

section

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
    Matrix.trace (C * Kraus.evalWord A w) = Matrix.trace (E * Kraus.evalWord B w) := by
  have hChain : ∀ (w : List (Fin d))
      (C : Matrix (Fin D) (Fin D) ℂ) (E : Matrix (Fin n) (Fin n) ℂ),
      C = Vᴴ * E * V →
      C * Kraus.evalWord A w = Vᴴ * (E * Kraus.evalWord B w) * V := by
    intro w
    induction w with
    | nil =>
        intro C E hCE
        simp [hCE]
    | cons i w ih =>
        intro C E hCE
        simp only [Kraus.evalWord_cons]
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
    Matrix.trace (linearMarkedTensor f A u * Kraus.evalWord A w) =
      Matrix.trace (linearMarkedTensor f B u * Kraus.evalWord B w) :=
  trace_marked_mul_evalWord_of_coisometry_reconstruction A B V hV hReconstruct
    _ _ (linearMarkedTensor_coisometry_reconstruction f A B V hReconstruct u) w

private theorem cast_linearMarkedTensor
    {m n : ℕ} (h : m = n) (f : Fin e → Fin d → ℂ) (A : MPSTensor d m) :
    cast (congr_arg (MPSTensor e) h) (linearMarkedTensor f A) =
      linearMarkedTensor f (cast (congr_arg (MPSTensor d) h) A) := by
  subst n
  rfl

section CPSVCanonicalFormData.BNTRefinement

open MPTensor.CPSVCanonicalFormData.BNTRefinement

variable {A : MPSTensor d D} {data : CPSVCanonicalFormData A}

set_option linter.style.longLine false in
/-- Linear marking of the full grouped tensor is exactly the full grouped marked tensor formed
from the representative linear marks.

Every copy carries its raw weight and phase.

Source: arXiv:1606.00608, Appendix C.3, lines 1848--1858. -/
theorem
    _root_.MPTensor.CPSVCanonicalFormData.BNTRefinement.linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor
    (ref : data.BNTRefinement) (f : Fin e → Fin d → ℂ) :
    linearMarkedTensor f ref.groupedTensor =
      ref.groupedMarkedTensor
        (fun j => linearMarkedTensor f (data.blocks (data.representativeIndex j))) := by
  classical
  rw [← funext ref.regroupedTensor_eq_groupedTensor,
    linearMarkedTensor_toTensorFromBlocks]
  rw [groupedMarkedTensor]
  have hBlocks : ∀ k,
      data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) =
        ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f
            (data.blocks (data.representativeIndex j))) k := by
    intro k
    funext u
    change data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) u =
      ref.groupedMarkedBlocks
        (fun j => linearMarkedTensor f (data.blocks (data.representativeIndex j))) k u
    rw [groupedMarkedBlocks, ref.regroupedBlocksEq k]
    rw [cast_linearMarkedTensor (ref.copyDimEq k)]
    simp only [linearMarkedTensor, Pi.smul_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    ring
  unfold toTensorFromBlocks
  funext u
  change (Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv)
      (Matrix.blockDiagonal' fun k =>
        data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) u) =
    (Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv)
      (Matrix.blockDiagonal' fun k =>
        (1 : ℂ) • ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f
            (data.blocks (data.representativeIndex j))) k u)
  have hBlockDiagonal :
      (Matrix.blockDiagonal' fun k =>
        data.weights k • linearMarkedTensor f (ref.regroupedBlocks k) u) =
      (Matrix.blockDiagonal' fun k =>
        (1 : ℂ) • ref.groupedMarkedBlocks
          (fun j => linearMarkedTensor f
            (data.blocks (data.representativeIndex j))) k u) := by
    congr 1
    funext k
    simpa using congrFun (hBlocks k) u
  rw [hBlockDiagonal]

/-- **Lemma L in the original bond coordinates of a literal CPSV canonical form.**

Equality of every positive-tail closed chain with one marked physical letter implies equality of
the two linear marked tensors on the original bond space.  The proof uses the original ambient
coisometry in the orientation `U * Uᴴ = 1`, the listed block gauge, and the full
grouped tensor.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858. -/
theorem _root_.MPTensor.CPSVCanonicalFormData.BNTRefinement.linearMarkedTensor_eq_of_trace_agree
    (ref : data.BNTRefinement) (f g : Fin e → Fin d → ℂ)
    (hTrace : ∀ (L : ℕ), 0 < L → ∀ (u : Fin e) (w : Fin L → Fin d),
      Matrix.trace (linearMarkedTensor f A u * Kraus.evalWord A (List.ofFn w)) =
        Matrix.trace (linearMarkedTensor g A u * Kraus.evalWord A (List.ofFn w))) :
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
  let Cf := fun j : Fin data.phaseClasses.g =>
    linearMarkedTensor f (data.blocks (data.representativeIndex j))
  let Cg := fun j : Fin data.phaseClasses.g =>
    linearMarkedTensor g (data.blocks (data.representativeIndex j))
  have hGroupedTrace : ∀ (L : ℕ), 0 < L → ∀ (u : Fin e) (w : Fin L → Fin d),
      Matrix.trace (ref.groupedMarkedTensor Cf u * Kraus.evalWord ref.groupedTensor (List.ofFn w)) =
        Matrix.trace (ref.groupedMarkedTensor Cg u *
          Kraus.evalWord ref.groupedTensor (List.ofFn w)) := by
    intro L hL u w
    rw [← ref.linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor f,
      ← ref.linearMarkedTensor_groupedTensor_eq_groupedMarkedTensor g]
    have hf := trace_linearMarkedTensor_mul_evalWord_of_coisometry_reconstruction
      f A B ref.ambientCoisometry ref.ambientCoisometric hReconstruct u (List.ofFn w)
    have hg := trace_linearMarkedTensor_mul_evalWord_of_coisometry_reconstruction
      g A B ref.ambientCoisometry ref.ambientCoisometric hReconstruct u (List.ofFn w)
    have hfg := hTrace L hL u w
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
theorem
    _root_.MPTensor.CPSVCanonicalFormData.BNTRefinement.insertedTensor_eq_of_firstSiteActionAgree
    (ref : data.BNTRefinement) {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree A Y Z) :
    insertedTensor Y A = insertedTensor Z A := by
  apply ref.linearMarkedTensor_eq_of_trace_agree Y Z
  intro L _hL u w
  simpa [linearMarkedTensor, insertedTensor] using
    hAct.trace_evalWord u (List.ofFn w)

end CPSVCanonicalFormData.BNTRefinement

section IsCPSVCanonicalForm

open MPTensor.IsCPSVCanonicalForm

/-- Predicate-level form of Lemma L in the original bond coordinates of a literal CPSV canonical
form, on any finite physical alphabet. -/
theorem _root_.MPTensor.IsCPSVCanonicalForm.linearMarkedTensor_eq_of_trace_agree
    {α : Type*} [Fintype α] (A : MPTensor α (Fin D)) (hCanonical : IsCPSVCanonicalForm A)
    (f g : Fin e → α → ℂ)
    (hTrace : ∀ (L : ℕ), 0 < L → ∀ (u : Fin e) (w : Fin L → α),
      Matrix.trace (linearMarkedTensor f A u * Kraus.evalWord A (List.ofFn w)) =
        Matrix.trace (linearMarkedTensor g A u * Kraus.evalWord A (List.ofFn w))) :
    linearMarkedTensor f A = linearMarkedTensor g A := by
  classical
  let eα := Fintype.equivFin α
  have hMark : ∀ h : Fin e → α → ℂ, linearMarkedTensor h A =
      linearMarkedTensor (fun u (z : Fin (Fintype.card α)) ↦ h u (eα.symm z))
        (Kraus.reindexPhysical eα.symm A) := by
    intro h
    rw [linearMarkedTensor_reindexPhysical]
    simp
  rw [hMark f, hMark g]
  let data := Classical.choice (hCanonical.reindexPhysical eα.symm)
  refine data.bntRefinement.linearMarkedTensor_eq_of_trace_agree _ _ fun L hL u w ↦ ?_
  rw [← hMark f, ← hMark g, Kraus.evalWord_reindexPhysical, List.map_ofFn]
  exact hTrace L hL u _

/-- Predicate-level physical first-site Lemma L in the original bond coordinates of a literal
CPSV canonical form. -/
theorem _root_.MPTensor.IsCPSVCanonicalForm.insertedTensor_eq_of_firstSiteActionAgree
    (A : MPSTensor d D) (hCanonical : IsCPSVCanonicalForm A)
    {Y Z : Matrix (Fin d) (Fin d) ℂ} (hAct : FirstSiteActionAgree A Y Z) :
    insertedTensor Y A = insertedTensor Z A := by
  let data := Classical.choice hCanonical
  let ref := data.bntRefinement
  exact ref.insertedTensor_eq_of_firstSiteActionAgree hAct

end IsCPSVCanonicalForm

end MPSTensor

end

section

open scoped Matrix ComplexOrder
open MPOTensor

namespace MPTensor.IsCPSVCanonicalForm

open MPSTensor

variable {d D n : ℕ}

/-- **The pairwise Gram identity of Figure 8 under literal CPSV canonical form.**

Suppose two vertical corners of the same representative tensor are positive scalar multiples of
similarities by `X` and `Y`.  The reflected marked-chain identity makes their Gram-dressed marked
chains equal.  Lemma L for the literal CPSV canonical form separates the corresponding physical
linear marks, giving
$X^\dagger X A^v (X^\dagger X)^{-1}=Y^\dagger Y A^v (Y^\dagger Y)^{-1}$.

**Scope restriction (conditional corners):** The theorem assumes the two positive corner
similarity equations; it does not construct the representative group or its corners.  See
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines 1909--1919. -/
theorem gramDressing_eq_of_two_grouped_corners
    (M : MPOTensor d D) (hCanonical : IsCPSVCanonicalForm M) (hM : IsMPDO M)
    (A : MPSTensor (D * D) n)
    (VX VY : Matrix (Fin d) (Fin n) ℂ) (X Y : GL (Fin n) ℂ)
    (cX cY : ℂ) (hcX : (0 : ℂ) < cX) (hcY : (0 : ℂ) < cY)
    (hcornerX : ∀ v,
      VXᴴ * verticalTensor M v * VX =
        cX • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (hcornerY : ∀ v,
      VYᴴ * verticalTensor M v * VY =
        cY • ((Y : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((Y)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))) :
    gramDressing X A = gramDressing Y A := by
  let fX := cornerGramCoefficients VX X cX
  let fY := cornerGramCoefficients VY Y cY
  have hTrace : ∀ (L : ℕ), 0 < L → ∀ (u : Fin (n * n))
      (w : Fin L → Fin d × Fin d),
      Matrix.trace (linearMarkedTensor fX M u * Kraus.evalWord M (List.ofFn w)) =
        Matrix.trace (linearMarkedTensor fY M u * Kraus.evalWord M (List.ofFn w)) := by
    intro L _hL u w
    rw [show linearMarkedTensor fX M u =
        horizontalSlice (gramDressing X A) u.divNat u.modNat by
      exact linearMarkedTensor_cornerGramCoefficients
        A VX X cX hcX hcornerX u]
    rw [show linearMarkedTensor fY M u =
        horizontalSlice (gramDressing Y A) u.divNat u.modNat by
      exact linearMarkedTensor_cornerGramCoefficients
        A VY Y cY hcY hcornerY u]
    rw [kraus_evalWord_ofFn]
    exact hM.markedChainCoefficient_gramDressing_eq_of_two_corners
      A VX VY X Y cX cY hcX hcY hcornerX hcornerY L
        u.divNat u.modNat (fun k ↦ (w k).1) (fun k ↦ (w k).2)
  have hMarks : linearMarkedTensor fX M = linearMarkedTensor fY M :=
    hCanonical.linearMarkedTensor_eq_of_trace_agree M fX fY hTrace
  funext v
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective v
  ext r s
  have hSlice := congrFun hMarks (finProdFinEquiv (r, s))
  rw [linearMarkedTensor_cornerGramCoefficients
      A VX X cX hcX hcornerX,
    linearMarkedTensor_cornerGramCoefficients
      A VY Y cY hcY hcornerY] at hSlice
  simpa only [horizontalSlice, finProdFinEquiv_divNat,
    finProdFinEquiv_modNat] using congrFun (congrFun hSlice a) b

/-- **The positive relative Gram scalar of Figure 8.**

If the common representative is normal, equality of the two Gram conjugations implies
$X^\dagger X=\omega\,Y^\dagger Y$ for a real number $\omega>0$.

**Scope restriction (conditional corners):** The theorem assumes the two positive corner
similarity equations; it does not construct the representative group or its corners.  See
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, equation `eq3:proof.IV.12` and lines
1909--1921. -/
theorem gram_eq_pos_smul_gram_of_two_grouped_corners
    (M : MPOTensor d D) (hCanonical : IsCPSVCanonicalForm M) (hM : IsMPDO M)
    (A : MPSTensor (D * D) n) (hA : Kraus.IsNormal A)
    (VX VY : Matrix (Fin d) (Fin n) ℂ) (X Y : GL (Fin n) ℂ)
    (cX cY : ℂ) (hcX : (0 : ℂ) < cX) (hcY : (0 : ℂ) < cY)
    (hcornerX : ∀ v,
      VXᴴ * verticalTensor M v * VX =
        cX • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (hcornerY : ∀ v,
      VYᴴ * verticalTensor M v * VY =
        cY • ((Y : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((Y)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))) :
    ∃ ω : ℝ, 0 < ω ∧
      (X : Matrix (Fin n) (Fin n) ℂ)ᴴ * X =
        (ω : ℂ) • ((Y : Matrix (Fin n) (Fin n) ℂ)ᴴ * Y) := by
  have hDress := hCanonical.gramDressing_eq_of_two_grouped_corners
    M hM A VX VY X Y cX cY hcX hcY hcornerX hcornerY
  apply hA.gram_eq_pos_smul_gram_of_gram_conj_eq
      (Matrix.isUnits_det_units X) (Matrix.isUnits_det_units Y)
  intro v
  simpa only [gramDressing] using congrFun hDress v

end MPTensor.IsCPSVCanonicalForm

end
