/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.SquareLattice.Basic
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Sites.ReplicaSwap
import QICLean.ManyBody.Sites.PairSwapPermutation
import QICLean.ManyBody.Sites.SitewiseProduct
import TNLean.PEPS.Tensor.Region.RegionBlock
import TNLean.Lattice.Sheet.SwapCorrection
import QICLean.Spectral.Gap.DoubledSystemGap
import TNLean.PEPS.Graph.Region.SquareLatticeEdgeCount
import QICLean.Analysis.Norm.L2OpNormReindex
import TNLean.PEPS.AreaLaw.Operators.Interactions.RectangleInteraction
import TNLean.PEPS.Tensor.SquareLattice.SquareGridContraction
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.ManyBody.Sites.ConfigurationMap

/-!
# The crossing-edge expansion of a swapped Hamiltonian

The difference between a doubled square Hamiltonian and its conjugate by the
regional sheet swap is the sum of the corresponding differences for the
original crossing-edge interactions. All site interactions and all remaining
edge interactions cancel.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The norm of a swapped doubled interaction

The change of one doubled interaction under the actual regional sheet swap has
norm at most four times the norm of the original interaction. This estimate is
independent of its support and applies to arbitrary finite coordinate spaces.

### References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 416–424 and 513–524, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The boundary perturbation of a doubled square Hamiltonian

The partial swap changes only the original interactions crossing the chosen
region. In paired-site coordinates, the resulting perturbation is supported
on their endpoints and has norm at most eight times the interaction bound
times the number of sites.

The original individual interactions need not be Hermitian. No sign assumption
on the interaction bound is added: on a nonempty grid it follows from any
original site bound, whereas an empty grid has zero Hamiltonian.

### References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 416–424 and 513–524,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The local interactions of the partially swapped doubled Hamiltonian

Take the Hermitian part of each original site and edge interaction, double
it, pair the two coordinates at every site, and conjugate by the actual
partial swap. Each resulting term acts on its original designated support
and has norm at most twice the original bound. The sum is exactly the
partially swapped doubled Hamiltonian, since the original total is Hermitian.

### References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `00-introduction.tex`, `eq:model`, and
`02-information.tex`, lines 416–424 and 498–524, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

open scoped Matrix.Norms.L2Operator

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareInteraction)

open Matrix
open scoped BigOperators

namespace TNLean.PEPS.Approximation

/-- Only the original crossing-edge interactions contribute to the partial-swap
perturbation. The individual interactions need not be Hermitian, and zero local
dimension and empty square grids are included.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem _root_.ManyBody.SquareInteraction.pairSwapOp_conj_doubled_operator_sub_eq_sum_crossing
    {L q : ℕ} (h : SquareInteraction L q) (R : Finset (SquareLatticeVertex L L)) :
    let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let F := reindex pr pr (ManyBody.pairSwapOp R)
    F * doubledHamiltonian h.hamiltonian * Fᴴ - doubledHamiltonian h.hamiltonian =
      ∑ e ∈ Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R),
        (F * doubledHamiltonian (h.term (.inr e)) * Fᴴ -
          doubledHamiltonian (h.term (.inr e))) := by
  classical
  intro pr F
  let δ : Matrix (Configuration L q) (Configuration L q) ℂ →ₗ[ℂ]
      Matrix (Configuration L q × Configuration L q)
        (Configuration L q × Configuration L q) ℂ :=
    (LinearMap.mulLeftRight ℂ (F, Fᴴ) - LinearMap.id).comp
      ((Matrix.kroneckerBilinear (R := ℂ)).flip
          (1 : Matrix (Configuration L q) (Configuration L q) ℂ) +
        Matrix.kroneckerBilinear (R := ℂ)
          (1 : Matrix (Configuration L q) (Configuration L q) ℂ))
  change δ h.hamiltonian = ∑ e ∈ Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R), δ (h.term (.inr e))
  simp only [ManyBody.Interaction.hamiltonian, Fintype.sum_sum_type, map_add, map_sum]
  have hcancel {S : Finset (SquareLatticeVertex L L)}
      {A : Matrix (Configuration L q) (Configuration L q) ℂ}
      (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
      (hS : S ⊆ R ∨ Disjoint S R) :
      δ A = 0 := by
    -- on paired sites the exchange on `R` fixes a doubled operator supported inside or
    -- outside `R`
    have hfix : ManyBody.pairSwapOp R * reindex pr.symm pr.symm (doubledHamiltonian A) *
        (ManyBody.pairSwapOp R)ᴴ = reindex pr.symm pr.symm (doubledHamiltonian A) :=
      hS.elim (fun hs ↦ ManyBody.pairSwapOp_conj_doubled_of_subset hs hA)
        (fun hs ↦ ManyBody.pairSwapOp_mul_mul_conjTranspose_of_disjoint hs
          (ManyBody.reindex_doubledHamiltonian_mem_supportedOperators hA))
    have hY : doubledHamiltonian A =
        reindex pr pr (reindex pr.symm pr.symm (doubledHamiltonian A)) := by
      rw [← reindex_symm, Equiv.apply_symm_apply]
    change F * doubledHamiltonian A * Fᴴ - doubledHamiltonian A = 0
    rw [sub_eq_zero, hY]
    conv_rhs => rw [← hfix]
    simp only [F, reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have hedge (e : Edge (squareLatticeGraph L L)) (he : ¬ ManyBody.IsRegionBoundaryEdge R e) :
      δ (h.term (.inr e)) = 0 := by
    apply hcancel (h.mem (.inr e))
    simp only [ManyBody.squareLatticeSiteOrEdgeSupport, ManyBody.IsRegionBoundaryEdge,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.disjoint_insert_left,
      Finset.disjoint_singleton_left] at he ⊢
    tauto
  have hsite (v : SquareLatticeVertex L L) : δ (h.term (.inl v)) = 0 :=
    hcancel (h.mem (.inl v)) (by
      simp only [ManyBody.squareLatticeSiteOrEdgeSupport, Finset.singleton_subset_iff,
        Finset.disjoint_singleton_left]
      exact em _)
  rw [Finset.sum_eq_zero fun v _ => hsite v, zero_add]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro e _ hne
  exact hedge e fun hb => hne (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hb⟩)

end TNLean.PEPS.Approximation

end

section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

/-- Swapping a doubled interaction changes it by at most four times its original
norm. This is the single-interaction estimate used for the boundary perturbation
in `02-information.tex`, lines 416–424 and 513–524. -/
theorem norm_pairSwapOp_conj_doubledHamiltonian_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (R : Finset ι) (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    ‖reindex (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
          (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q) (ManyBody.pairSwapOp R) *
        doubledHamiltonian A *
        (reindex (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
          (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
          (ManyBody.pairSwapOp R))ᴴ - doubledHamiltonian A‖ ≤ 4 * ‖A‖ := by
  set F := reindex (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
    (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
    (ManyBody.pairSwapOp (X := fun _ : ι ↦ Fin q) R)
  have hF : ‖F‖ ≤ 1 :=
    (Matrix.l2_opNorm_reindex_equiv _ _).trans_le (ManyBody.norm_pairSwapOp_le_one R)
  have hdouble : ‖doubledHamiltonian A‖ ≤ ‖A‖ + ‖A‖ := by
    unfold doubledHamiltonian
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact l2_opNorm_kronecker_one_le A
    · exact l2_opNorm_one_kronecker_le A
  have hconj : ‖F * doubledHamiltonian A * Fᴴ‖ ≤ ‖A‖ + ‖A‖ :=
    (norm_mul_le_of_le (norm_mul_le_of_le hF hdouble)
      ((l2_opNorm_conjTranspose F).trans_le hF)).trans (le_of_eq (by ring))
  calc ‖F * doubledHamiltonian A * Fᴴ - doubledHamiltonian A‖
      ≤ ‖F * doubledHamiltonian A * Fᴴ‖ + ‖doubledHamiltonian A‖ := norm_sub_le _ _
    _ ≤ (‖A‖ + ‖A‖) + (‖A‖ + ‖A‖) := add_le_add hconj hdouble
    _ = 4 * ‖A‖ := by ring

end TNLean.PEPS.EncodedFrame

end

section

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareInteraction)

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

/-- The actual partial-swap perturbation is supported on the endpoints of
the original crossing edges and has norm at most `8 J L²`. Empty grids and
zero local dimension are included, and the original individual interactions
need not be Hermitian.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem _root_.ManyBody.SquareInteraction.swapped_doubled_boundary_bound
    {L q : ℕ} {J : ℝ} (h : SquareInteraction L q) (hhJ : ∀ i, ‖h.term i‖ ≤ J)
    (R : Finset (SquareLatticeVertex L L)) :
    let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let p := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
    let K := Matrix.reindex p p (Matrix.doubledHamiltonian h.hamiltonian)
    let F := Matrix.reindex p p (Matrix.reindex pr pr (ManyBody.pairSwapOp R))
    let boundary : Finset (Edge (squareLatticeGraph L L)) :=
      Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
    let Z := boundary.biUnion fun e ↦ ({e.1.1, e.1.2} : Finset (SquareLatticeVertex L L))
    F * K * Fᴴ - K ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Z ∧
      ‖F * K * Fᴴ - K‖ ≤ 8 * J * (L : ℝ) ^ 2 := by
  classical
  intro pr p K F boundary Z
  let g := ManyBody.siteConfigurationEquiv (X' := fun _ : SquareLatticeVertex L L ↦ Fin (q * q))
    (Equiv.refl (SquareLatticeVertex L L)) fun _ ↦ finProdFinEquiv
  have hsum := congrArg (Matrix.reindex p p)
    (h.pairSwapOp_conj_doubled_operator_sub_eq_sum_crossing R)
  simp only [← Matrix.coe_reindexRingEquiv, map_sum, map_sub, map_mul] at hsum
  change F * K * Fᴴ - K = ∑ e ∈ boundary,
    (F * Matrix.reindex p p (doubledHamiltonian (h.term (.inr e))) * Fᴴ -
      Matrix.reindex p p (doubledHamiltonian (h.term (.inr e)))) at hsum
  have hnorm (A : Matrix (Configuration L q) (Configuration L q) ℂ) :
      ‖F * Matrix.reindex p p (doubledHamiltonian A) * Fᴴ -
        Matrix.reindex p p (doubledHamiltonian A)‖ ≤ 4 * ‖A‖ := by
    simpa only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
      ← Matrix.submatrix_mul_equiv (e₂ := p.symm), ← Matrix.conjTranspose_submatrix] using!
      (Matrix.l2_opNorm_reindex_equiv p
        (Matrix.reindex pr pr (ManyBody.pairSwapOp R) * doubledHamiltonian A *
          (Matrix.reindex pr pr (ManyBody.pairSwapOp R))ᴴ - doubledHamiltonian A)).trans_le
        (EncodedFrame.norm_pairSwapOp_conj_doubledHamiltonian_sub_le R A)
  have hplain (S : Finset (SquareLatticeVertex L L))
      {A : Matrix (Configuration L q) (Configuration L q) ℂ}
      (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
      Matrix.reindex p p (doubledHamiltonian A) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl _)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      (ManyBody.reindex_doubledHamiltonian_mem_supportedOperators hA)
    convert hs using 1
    ext x y
    rfl
  have hlocal (S : Finset (SquareLatticeVertex L L))
      {A : Matrix (Configuration L q) (Configuration L q) ℂ}
      (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
      F * Matrix.reindex p p (doubledHamiltonian A) * Fᴴ -
          Matrix.reindex p p (doubledHamiltonian A) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
    refine sub_mem ?_ (hplain S hA)
    -- in the paired coordinates `F` is the exchange on `R`, which keeps supports
    have h := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl _)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      (ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators R
        (ManyBody.reindex_doubledHamiltonian_mem_supportedOperators hA))
    convert h using 1
    have hF : F = Matrix.reindex g g (ManyBody.pairSwapOp R) := rfl
    have hY : Matrix.reindex p p (doubledHamiltonian A) =
        Matrix.reindex g g (Matrix.reindex pr.symm pr.symm (doubledHamiltonian A)) := by
      ext x y
      rfl
    rw [hF, hY]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    ext x y
    rfl
  have hsupport : F * K * Fᴴ - K ∈
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Z :=
    hsum.symm ▸ sum_mem
      (fun e he ↦ ManyBody.supportedOperators_mono
        (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem
          (fun e : Edge (squareLatticeGraph L L) ↦
            ({e.1.1, e.1.2} : Finset (SquareLatticeVertex L L))) he))
        (hlocal {e.1.1, e.1.2}
          (h.mem (.inr e))))
  have hbound : ‖F * K * Fᴴ - K‖ ≤ (boundary.card : ℝ) * (4 * J) := by
    simpa only [hsum, nsmul_eq_mul] using
      (norm_sum_le boundary (fun e ↦
        F * Matrix.reindex p p (doubledHamiltonian (h.term (.inr e))) * Fᴴ -
          Matrix.reindex p p (doubledHamiltonian (h.term (.inr e))))).trans
        (Finset.sum_le_card_nsmul boundary _ (4 * J) (fun e _ ↦
          (hnorm (h.term (.inr e))).trans
            (mul_le_mul_of_nonneg_left (hhJ (.inr e)) (by norm_num))))
  have hbcard : boundary.card ≤ 2 * L ^ 2 :=
    (Finset.card_le_univ boundary).trans (TNLean.PEPS.card_squareLatticeEdges_le L)
  have hJ (hL : L ≠ 0) : 0 ≤ J :=
    (norm_nonneg (h.term
      (.inl (⟨0, Nat.pos_of_ne_zero hL⟩, ⟨0, Nat.pos_of_ne_zero hL⟩)))).trans
      (hhJ (.inl _))
  exact ⟨hsupport, if hL : L = 0 then
    hbound.trans_eq (by
      simp [hL, Nat.eq_zero_of_le_zero (n := boundary.card) (by simpa [hL] using hbcard)])
    else hbound.trans (calc
      (boundary.card : ℝ) * (4 * J) ≤ (2 * (L : ℝ) ^ 2) * (4 * J) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hbcard)
          (mul_nonneg (by norm_num) (hJ hL))
      _ = 8 * J * (L : ℝ) ^ 2 := by ring)⟩

end TNLean.PEPS.Approximation

end

section

open ManyBody (SquareLatticeVertex SquareLatticeSiteOrEdge squareLatticeSiteOrEdgeSupport
  SquareInteraction)

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

/-- The actual local interaction family of the swapped doubled Hamiltonian.
Its term at each original support is the conjugated doubled Hermitian part;
unused admissible supports carry zero. Only the original total is required
to be Hermitian. No ground-state or gap hypothesis is needed.

Source: polynomial-PEPS `eq:model` and `02-information.tex`, lines 416–424,
where pairing the two replicas at each site preserves range one. -/
theorem _root_.ManyBody.SquareInteraction.exists_swapped_doubled_planeInteraction
    {L q : ℕ} {J : ℝ} (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian)
        (hhJ : ∀ i, ‖h.term i‖ ≤ J) (hJ : 0 ≤ J)
    (R : Finset (SquareLatticeVertex L L)) :
    let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let p := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
    let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
    let F := Matrix.reindex p p (Matrix.reindex pr pr (ManyBody.pairSwapOp R))
    let K := Matrix.reindex p p (Matrix.doubledHamiltonian h.hamiltonian)
    ∃ g : ManyBody.PlaneInteraction (ManyBody.rectangularDomain L L) (q * q) 1,
      (∀ X, (g.term X).IsHermitian) ∧ (∀ X, ‖g.term X‖ ≤ 2 * J) ∧ g.term =
          Function.extend (ManyBody.rectangleSupport (width := L) (height := L))
        (fun i : SquareLatticeSiteOrEdge L L =>
          Matrix.reindex e e
            (F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i)) * Fᴴ)) 0 ∧
      g.hamiltonian = Matrix.reindex e e (F * K * Fᴴ) := by
  classical
  intro pr p e F K
  let g := ManyBody.siteConfigurationEquiv (X' := fun _ : SquareLatticeVertex L L ↦ Fin (q * q))
    (Equiv.refl (SquareLatticeVertex L L)) fun _ ↦ finProdFinEquiv
  let B (i : SquareLatticeSiteOrEdge L L) :=
    F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i)) * Fᴴ
  have hBsupport (i : SquareLatticeSiteOrEdge L L) : B i ∈
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q))
          (squareLatticeSiteOrEdgeSupport i : Finset (Vertex L)) := by
    -- in the paired coordinates `F` is the exchange on `R`, which keeps supports
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl _)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      (ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators R
        (ManyBody.reindex_doubledHamiltonian_mem_supportedOperators (h.hermitianPart.mem i)))
    convert hs using 1
    have hF : F = Matrix.reindex g g (ManyBody.pairSwapOp R) := rfl
    have hY : Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i)) =
        Matrix.reindex g g (Matrix.reindex pr.symm pr.symm
          (Matrix.doubledHamiltonian (h.hermitianPart.term i))) := by
      ext x y
      rfl
    simp only [B]
    rw [hF, hY]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    ext x y
    rfl
  have hFn : ‖F‖ ≤ 1 :=
    (Matrix.l2_opNorm_reindex_equiv p _).le.trans ((Matrix.l2_opNorm_reindex_equiv pr _).le.trans
      (ManyBody.norm_pairSwapOp_le_one R))
  have hDn (i : SquareLatticeSiteOrEdge L L) : ‖Matrix.doubledHamiltonian
      (h.hermitianPart.term i)‖ ≤
      J + J :=
    (norm_add_le _ _).trans (add_le_add
      ((Matrix.l2_opNorm_kronecker_one_le _).trans
          ((h.norm_hermitianPart_term_le i).trans (hhJ i)))
      ((Matrix.l2_opNorm_one_kronecker_le _).trans
          ((h.norm_hermitianPart_term_le i).trans (hhJ i))))
  have hBn (i : SquareLatticeSiteOrEdge L L) : ‖B i‖ ≤ 2 * J := by
    simpa only [B, one_mul, mul_one, two_mul] using
      norm_mul_le_of_le
        (norm_mul_le_of_le hFn ((Matrix.l2_opNorm_reindex_equiv p _).le.trans (hDn i)))
        ((Matrix.l2_opNorm_conjTranspose F).trans_le hFn)
  have hDH (i : SquareLatticeSiteOrEdge L L) :
      (Matrix.doubledHamiltonian (h.hermitianPart.term i)).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.doubledHamiltonian, Matrix.conjTranspose_add,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (h.isHermitian_hermitianPart_term i).eq]
  have hBH (i : SquareLatticeSiteOrEdge L L) : (B i).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose F ((hDH i).reindex p)
  -- The doubled map is additive in its argument, so summing the doubled Hermitian
  -- parts recovers the doubled total.
  let D : Matrix (Configuration L q) (Configuration L q) ℂ →ₗ[ℂ]
      Matrix (Configuration L q × Configuration L q)
        (Configuration L q × Configuration L q) ℂ :=
    (Matrix.kroneckerBilinear (R := ℂ)).flip
        (1 : Matrix (Configuration L q) (Configuration L q) ℂ) +
      Matrix.kroneckerBilinear (R := ℂ)
        (1 : Matrix (Configuration L q) (Configuration L q) ℂ)
  have hDsum : (∑ i : SquareLatticeSiteOrEdge L L,
      Matrix.doubledHamiltonian (h.hermitianPart.term i)) =
      Matrix.doubledHamiltonian h.hamiltonian := by
    change (∑ i : SquareLatticeSiteOrEdge L L, D (h.hermitianPart.term i)) = D h.hamiltonian
    rw [← map_sum D, ← h.hamiltonian_hermitianPart hh]; rfl
  -- The actual interaction family sums exactly to the swapped doubled total, since
  -- the conjugation and the bond reindexing are additive.
  have key : (∑ i : SquareLatticeSiteOrEdge L L, B i) = F * K * Fᴴ := by
    have hreindex : (∑ i : SquareLatticeSiteOrEdge L L,
        Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i))) = K := by
      change (∑ i : SquareLatticeSiteOrEdge L L,
        (Matrix.reindexAlgEquiv ℂ ℂ p) (Matrix.doubledHamiltonian (h.hermitianPart.term i))) = K
      rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ p), hDsum]
      rfl
    calc (∑ i : SquareLatticeSiteOrEdge L L, B i)
        = F * (∑ i : SquareLatticeSiteOrEdge L L,
            Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i))) * Fᴴ := by
          simp only [B, Finset.mul_sum, Finset.sum_mul]
      _ = F * K * Fᴴ := by rw [hreindex]
  refine ⟨{ term := Function.extend (ManyBody.rectangleSupport (width := L) (height := L))
              (fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (B i)) 0
            mem := ?_ }, ?_, ?_, rfl, ?_⟩
  · intro X
    by_cases hx : ∃ i, ManyBody.rectangleSupport i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(ManyBody.rectangleSupport_injective L L).extend_apply]
      have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators
        (X := fun _ : SquareLatticeVertex L L ↦ Fin (q * q))
        (X' := fun _ : ↥(ManyBody.rectangularDomain L L) ↦ Fin (q * q))
        (ManyBody.rectangleSiteEquiv L L) (fun _ ↦ Equiv.refl (Fin (q * q)))
        (D' := (ManyBody.rectangleSupport i).val)
        (fun v ↦ (ManyBody.mem_rectangleSupport_iff i v).symm) (hBsupport i)
      rw [AreaLaw.siteConfigurationEquiv_rectangleSiteEquiv] at hs
      exact hs
    · rw [Function.extend_apply' _ _ _ hx]
      exact zero_mem _
  · intro X
    dsimp only
    by_cases hx : ∃ i, ManyBody.rectangleSupport i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(ManyBody.rectangleSupport_injective L L).extend_apply]
      exact (hBH i).submatrix e.symm
    · rw [Function.extend_apply' _ _ _ hx]
      exact Matrix.isHermitian_zero
  · intro X
    dsimp only
    by_cases hx : ∃ i, ManyBody.rectangleSupport i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(ManyBody.rectangleSupport_injective L L).extend_apply]
      exact (Matrix.l2_opNorm_reindex_equiv e (B i)).le.trans (hBn i)
    · rw [Function.extend_apply' _ _ _ hx]
      simpa only [Pi.zero_apply, norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hJ
  · let T := fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (B i)
    have hsum : (∑ i : SquareLatticeSiteOrEdge L L, T i) =
        ∑ X : ManyBody.AdmissibleSupport (ManyBody.rectangularDomain L L) 1,
          Function.extend (ManyBody.rectangleSupport (width := L) (height := L)) T 0 X := by
      apply Finset.sum_of_injOn (ManyBody.rectangleSupport (width := L) (height := L))
        (ManyBody.rectangleSupport_injective L L).injOn (fun _ _ => Finset.mem_univ _)
      · intro X _ hX
        exact Function.extend_apply' _ _ _ (by simpa using hX)
      · intro i _
        exact ((ManyBody.rectangleSupport_injective L L).extend_apply T 0 i).symm
    change (∑ X, Function.extend (ManyBody.rectangleSupport (width := L) (height := L)) T 0 X) = _
    rw [← hsum]
    change (∑ i : SquareLatticeSiteOrEdge L L, (Matrix.reindexAlgEquiv ℂ ℂ e) (B i)) = _
    rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e), key]
    rfl

end TNLean.PEPS.Approximation
end

end
