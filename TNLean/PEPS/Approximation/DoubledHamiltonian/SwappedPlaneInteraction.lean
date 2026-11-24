/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionalReset
import QICLean.ManyBody.Sites.ReplicaSwap
import QICLean.ManyBody.Dynamics.SwappedDoubledInteraction
import QICLean.ManyBody.Sites.Lattice.IntegerRectangle
import TNLean.PEPS.Approximation.DoubledHamiltonian.SwappedSquareHamiltonian
import TNLean.PEPS.AreaLaw.Operators.Interactions.SupportedGaussianIntegral
import QICLean.ManyBody.Sites.Lattice.Plane
import TNLean.PEPS.AreaLaw.Polygons.SafeRectangles.TailParameter
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.ManyBody.Sites.ConfigurationMap

/-!
# The partially swapped doubled Hamiltonian at interaction range `R`

Let `h` be a Hamiltonian of interaction range `R` and term bound `J` on a finite domain `Λ`,
and let `A` be a set of sites. Double `h` on two replicas, pair the two coordinates at every
site, and conjugate by the swap `F_A` of the replicas on `A`. This file shows:

* the result is again a Hamiltonian of range `R` on `Λ`, now with local dimension `q²` and term
  bound `2J`, with the same supports: the doubled interaction `ManyBody.Interaction.doubled`
  conjugated by the exchange `ManyBody.pairSwapOp A` (`ManyBody.Interaction.conj`), relabelled
  to `Fin (q * q)`, whose Hamiltonian is `F_A K F_Aᴴ`
  (`ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled`);
* it differs from the doubled Hamiltonian only through the terms whose support crosses `A`
  (`ManyBody.PlaneInteraction.pairSwapOp_conj_doubled_hamiltonian_sub_eq_sum_crossing`), the
  crossing
  terms `ManyBody.crossingTerms` of the supports at the cut `A`, so the difference is supported
  on the sites `ManyBody.crossingSites` of these supports and has norm at most `4 μ_R J |Λ|`,
  with `μ_R = 2^(v_R - 1)` and `v_R = 1 + 2R(R + 1)`
  (`ManyBody.PlaneInteraction.swapped_doubled_boundary_bound`);
* the supported Gaussian approximation of the physical buffer holds at range `R` with the
  graph-ball localization constants at range `R` and term bound `2J`
  (`ManyBody.PlaneInteraction.supported_buffer_gaussian_integral`).

The sites of the crossing supports and their walks to both sides of `A` are in
`TNLean.Lattice.CrossingSupports`.

The polynomial-PEPS manuscript treats only site and nearest-neighbour terms on the open square,
which is range one; this file extends its boundary estimate to range `R`. The range-one
statements on the open square, with the constant `8 J L²`, are
`ManyBody.SquareInteraction.swapped_doubled_boundary_bound` and
`ManyBody.SquareInteraction.supported_buffer_gaussian_integral`, and are unchanged.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `02-information.tex`, lines 416–424 and 498–564, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `01-preliminaries.tex`, lines 82–103 (the count of supports through a site).

Independently formalized from the manuscripts; no upstream Lean proof text is reused.

## The edge-boundary norm of a partially swapped doubled Hamiltonian

For a finite-domain Hamiltonian of interaction range `R` and term bound `J ≥ 0`,
the partial swap changes its doubled Hamiltonian by an operator of norm at most
`4 μ_R v_R J` times the number of boundary edges of the swapped region, where
`v_R = 1 + 2 R (R + 1)` and `μ_R = 2^(v_R - 1)`.

This is a finite-range extension of the polynomial-PEPS manuscript,
`02-information.tex`, lines 416–424 and 513–524. The crossing-support count is
from the area-law manuscript, `02-initial.tex`, lines 202–206.
The whole-domain estimate in `SwappedPlaneInteraction` remains available.
-/

open ManyBody (reindex_physicalBuffer_eq_place)

section

open Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator NNReal

noncomputable section

open ManyBody (AdmissibleSupport PlaneInteraction)

namespace TNLean.Lattice

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- There are at most `μ_R |Λ|` supports of range `R`, with `μ_R = 2^(v_R - 1)`: every support
is nonempty, and at most `μ_R` supports contain a given site.
Source: area-law `01-preliminaries.tex`, lines 95–102. -/
theorem card_admissibleSupport_le (Λ : Finset (ℤ × ℤ)) (R : ℕ) :
    Fintype.card (AdmissibleSupport Λ R) ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) * Λ.card := by
  classical
  have h := ManyBody.card_le_card_mul_of_forall_exists_mem (R := R)
    (N := (Finset.univ : Finset ↥Λ)) (S := Finset.univ) fun X _ ↦ by
      obtain ⟨v, hv⟩ := X.2.1
      exact ⟨v, Finset.mem_univ v, hv⟩
  rwa [Finset.card_univ, Finset.card_univ, Fintype.card_coe, mul_comm] at h

/-- The coefficient `4 μ_R` of the norm bound `4 μ_R J |Λ|` of the partial-swap perturbation at
range `R`, with `μ_R = 2^(v_R - 1)` supports through a site and `v_R = 1 + 2R(R + 1)`. -/
def swapBoundaryCoefficient (R : ℕ) : ℝ := 4 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)

theorem swapBoundaryCoefficient_nonneg (R : ℕ) : 0 ≤ swapBoundaryCoefficient R := by
  unfold swapBoundaryCoefficient
  positivity

end TNLean.Lattice

namespace ManyBody.PlaneInteraction

open TNLean.Lattice

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

theorem doubledHamiltonian_isHermitian {n : Type*} [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (doubledHamiltonian A).IsHermitian := by
  simp only [Matrix.IsHermitian, doubledHamiltonian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hA.eq]

/-- The doubling map is additive. -/
private theorem doubledHamiltonian_sum {n ι : Type*} [DecidableEq n]
    (s : Finset ι) (f : ι → Matrix n n ℂ) :
    doubledHamiltonian (∑ i ∈ s, f i) = ∑ i ∈ s, doubledHamiltonian (f i) := by
  let D : Matrix n n ℂ →ₗ[ℂ] Matrix (n × n) (n × n) ℂ :=
    (Matrix.kroneckerBilinear (R := ℂ)).flip (1 : Matrix n n ℂ) +
      Matrix.kroneckerBilinear (R := ℂ) (1 : Matrix n n ℂ)
  change D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i)
  exact map_sum D f s

/-- **Only the crossing supports contribute to the partial-swap perturbation.** The difference
between the doubled Hamiltonian and its conjugate by the swap on `A` is the sum of the
corresponding differences for the terms whose support crosses `A`.
Source: polynomial-PEPS `02-information.tex`, lines 416–424 and 513–524, at range `R`. -/
theorem pairSwapOp_conj_doubled_hamiltonian_sub_eq_sum_crossing (h : PlaneInteraction Λ q R)
    (A : Finset ↥Λ) :
    let pr := Equiv.arrowProdEquivProdArrow ↥Λ (fun _ ↦ Fin q) fun _ ↦ Fin q
    let F := reindex pr pr (ManyBody.pairSwapOp A)
    F * doubledHamiltonian h.hamiltonian * Fᴴ - doubledHamiltonian h.hamiltonian =
      ∑ X ∈ ManyBody.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A,
        (F * doubledHamiltonian (h.term X) * Fᴴ - doubledHamiltonian (h.term X)) := by
  classical
  intro pr F
  have hcancel (X : AdmissibleSupport Λ R)
      (hX : X ∉ ManyBody.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A) :
      F * doubledHamiltonian (h.term X) * Fᴴ - doubledHamiltonian (h.term X) = 0 := by
    have hX : X.1 ⊆ A ∨ Disjoint X.1 A := by
      simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
        not_exists, not_not] at hX
      by_cases hXA : ∃ v ∈ X.1, v ∈ A
      · exact Or.inl fun v hv ↦ hX hXA v hv
      · push Not at hXA
        exact Or.inr (Finset.disjoint_left.mpr hXA)
    -- on paired sites the exchange on `A` fixes a doubled term supported inside or outside `A`
    have hfix : ManyBody.pairSwapOp A * reindex pr.symm pr.symm (doubledHamiltonian (h.term X)) *
        (ManyBody.pairSwapOp A)ᴴ = reindex pr.symm pr.symm (doubledHamiltonian (h.term X)) :=
      hX.elim (fun hs ↦ ManyBody.pairSwapOp_conj_doubled_of_subset hs (h.mem X))
        (fun hs ↦ ManyBody.pairSwapOp_mul_mul_conjTranspose_of_disjoint hs
          (ManyBody.reindex_doubledHamiltonian_mem_supportedOperators (h.mem X)))
    have hY : doubledHamiltonian (h.term X) =
        reindex pr pr (reindex pr.symm pr.symm (doubledHamiltonian (h.term X))) := by
      rw [← reindex_symm, Equiv.apply_symm_apply]
    rw [sub_eq_zero, hY]
    conv_rhs => rw [← hfix]
    simp only [F, reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have hsum : F * doubledHamiltonian h.hamiltonian * Fᴴ - doubledHamiltonian h.hamiltonian =
      ∑ X, (F * doubledHamiltonian (h.term X) * Fᴴ - doubledHamiltonian (h.term X)) := by
    rw [ManyBody.Interaction.hamiltonian, doubledHamiltonian_sum, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
  rw [hsum]
  exact (Finset.sum_subset (Finset.subset_univ _) fun X _ hX ↦ hcancel X hX).symm

/-- **The partial-swap perturbation at range `R`.** In paired-site coordinates, `F K Fᴴ - K` is
supported on the sites of the supports crossing `A`, and has norm at most `4 μ_R J |Λ|`
(`swapBoundaryCoefficient R * J * |Λ|`). The individual terms are Hermitian, as the model
requires; the bound uses only their norms.
Source: polynomial-PEPS `02-information.tex`, lines 416–424 and 513–524, at range `R`, with the
count of supports through a site of area-law `01-preliminaries.tex`, lines 95–102. -/
theorem swapped_doubled_boundary_bound (h : PlaneInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (hJ : 0 ≤ J)
    (A : Finset ↥Λ) :
    let pr := Equiv.arrowProdEquivProdArrow ↥Λ (fun _ ↦ Fin q) fun _ ↦ Fin q
    let p := pr.symm.trans (Equiv.arrowCongr (Equiv.refl ↥Λ) finProdFinEquiv)
    let K := Matrix.reindex p p (doubledHamiltonian h.hamiltonian)
    let F := Matrix.reindex p p (Matrix.reindex pr pr (ManyBody.pairSwapOp A))
    F * K * Fᴴ - K ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q))
        (ManyBody.crossingSites Λ R A : Finset ↥Λ) ∧
      ‖F * K * Fᴴ - K‖ ≤ swapBoundaryCoefficient R * J * (Λ.card : ℝ) := by
  classical
  intro pr p K F
  let g := ManyBody.siteConfigurationEquiv (X' := fun _ : ↥Λ ↦ Fin (q * q)) (Equiv.refl ↥Λ)
    fun _ ↦ finProdFinEquiv
  set T := ManyBody.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A
  have hsum := congrArg (Matrix.reindex p p)
    (h.pairSwapOp_conj_doubled_hamiltonian_sub_eq_sum_crossing A)
  simp only [← Matrix.coe_reindexRingEquiv, map_sum, map_sub, map_mul] at hsum
  change F * K * Fᴴ - K = ∑ X ∈ T,
    (F * Matrix.reindex p p (doubledHamiltonian (h.term X)) * Fᴴ -
      Matrix.reindex p p (doubledHamiltonian (h.term X))) at hsum
  have hnorm (M : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) :
      ‖F * Matrix.reindex p p (doubledHamiltonian M) * Fᴴ -
        Matrix.reindex p p (doubledHamiltonian M)‖ ≤ 4 * ‖M‖ := by
    simpa only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
      ← Matrix.submatrix_mul_equiv (e₂ := p.symm), ← Matrix.conjTranspose_submatrix] using!
      (Matrix.l2_opNorm_reindex_equiv p
        (Matrix.reindex pr pr (ManyBody.pairSwapOp A) * doubledHamiltonian M *
          (Matrix.reindex pr pr (ManyBody.pairSwapOp A))ᴴ - doubledHamiltonian M)).trans_le
        (TNLean.PEPS.EncodedFrame.norm_pairSwapOp_conj_doubledHamiltonian_sub_le A M)
  have hplain (S : Finset ↥Λ)
      {M : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ}
      (hM : M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
      Matrix.reindex p p (doubledHamiltonian M) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl _)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      (ManyBody.reindex_doubledHamiltonian_mem_supportedOperators hM)
    convert hs using 1
    ext x y
    rfl
  -- in the paired coordinates `F` is the exchange on `A`, which keeps supports
  have hswap (S : Finset ↥Λ)
      {M : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ}
      (hM : M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
      F * Matrix.reindex p p (doubledHamiltonian M) * Fᴴ ∈
        ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl _)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      (ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators A
        (ManyBody.reindex_doubledHamiltonian_mem_supportedOperators hM))
    convert hs using 1
    have hF : F = Matrix.reindex g g (ManyBody.pairSwapOp A) := rfl
    have hY : Matrix.reindex p p (doubledHamiltonian M) =
        Matrix.reindex g g (Matrix.reindex pr.symm pr.symm (doubledHamiltonian M)) := by
      ext x y
      rfl
    rw [hF, hY]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    ext x y
    rfl
  have hsupport : F * K * Fᴴ - K ∈
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q))
        (ManyBody.crossingSites Λ R A : Finset ↥Λ) :=
    hsum.symm ▸ sum_mem
      fun X hX ↦ ManyBody.supportedOperators_mono
        (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem
          (fun X : AdmissibleSupport Λ R ↦ X.1) hX))
        (sub_mem (hswap X.1 (h.mem X)) (hplain X.1 (h.mem X)))
  have hbound : ‖F * K * Fᴴ - K‖ ≤ (T.card : ℝ) * (4 * J) := by
    simpa only [hsum, nsmul_eq_mul] using
      (norm_sum_le T fun X ↦
        F * Matrix.reindex p p (doubledHamiltonian (h.term X)) * Fᴴ -
          Matrix.reindex p p (doubledHamiltonian (h.term X))).trans
        (Finset.sum_le_card_nsmul T _ (4 * J) fun X _ ↦
          (hnorm (h.term X)).trans
            (mul_le_mul_of_nonneg_left (hhJ X) (by norm_num)))
  have hcard : (T.card : ℝ) ≤
      ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * Λ.card := by
    exact_mod_cast ((Finset.card_le_univ _).trans (card_admissibleSupport_le Λ R))
  refine ⟨hsupport, hbound.trans ?_⟩
  calc (T.card : ℝ) * (4 * J)
      ≤ (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * Λ.card) * (4 * J) :=
        mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = swapBoundaryCoefficient R * J * (Λ.card : ℝ) := by
        unfold swapBoundaryCoefficient
        ring

/-- **The supported Gaussian approximation of the physical buffer at range `R`, with explicit
constants.** Let `h` be a Hamiltonian of range `R` and term bound `J ≥ 0` on a finite domain
`Λ`, let `A, C` be disjoint sets of sites with buffer `Q = (A ∪ C)ᶜ`, let `K` be the doubled
Hamiltonian in paired-site coordinates and `K' = F_A K F_Aᴴ` its partial swap, and let `Z` be
the sites of the supports crossing `A`. For a buffer operator `W` and a radius `l` there is a
unitary path on the graph neighbourhood `B` of radius `l` of `Q ∪ Z` such that, for every
variance and cutoff `T ≥ 0`, the supported integral `M` approximates the truncated Gaussian
intertwiner with error at most
`‖W‖ 2 C₀(R) |Λ| (1 + 4 μ_R J |Λ| T) e^{v(R, 2J) T - l/2}`.

The polynomial-PEPS manuscript treats range one only; this is the extension to range `R`. The
range-one statement on the open square, with `C = squareLocalizationPrefactor`,
`v = squareLocalizationVelocity J` and the factor `1 + 8 J L² T`, is
`ManyBody.SquareInteraction.supported_buffer_gaussian_integral`.
Source: polynomial-PEPS, Section 2, `eq:info-local-two-sided`, lines 513–562, with the
constants of `eq:info-lr` (lines 486–496). -/
theorem supported_buffer_gaussian_integral (hq : 1 ≤ q) (hJ : 0 ≤ J)
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (A C : Finset ↥Λ) (hAC : Disjoint A C) :
    let Q := (A ∪ C)ᶜ
    let P := Fin (Fintype.card (A → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := ManyBody.splitTwoRegionsEquiv (fun _ : ↥Λ ↦ Fin q) A C hAC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P ({v // v ∉ A ∪ C} → Fin q))
    let pr := Equiv.arrowProdEquivProdArrow ↥Λ (fun _ ↦ Fin q) fun _ ↦ Fin q
    let p := pr.symm.trans (Equiv.arrowCongr (Equiv.refl ↥Λ) finProdFinEquiv)
    let K := reindex p p (doubledHamiltonian h.hamiltonian)
    let F := reindex p p (reindex pr pr (ManyBody.pairSwapOp A))
    let K' := F * K * Fᴴ
    let Z := ManyBody.crossingSites Λ R A
    ∀ W : Matrix (({v // v ∉ A ∪ C} → Fin q) × ({v // v ∉ A ∪ C} → Fin q))
        (({v // v ∉ A ∪ C} → Fin q) × ({v // v ∉ A ∪ C} → Fin q)) ℂ,
      let V := reindex (g.symm.trans p) (g.symm.trans p)
        ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W)
      ∀ l : ℕ,
        let B := ManyBody.graphNeighborhood (ManyBody.planeDomainGraph Λ) (Q ∪ Z) l
        ∃ U : ℝ → Matrix (↥Λ → Fin (q * q)) (↥Λ → Fin (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • ManyBody.regionExpectation B
              (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ unitaryGroup (↥Λ → Fin (q * q)) ℂ) ∧
          (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B) ∧
          ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
            let M := ∫ t : ℝ in Set.Icc (-T) T,
              ManyBody.regionExpectation B (ManyBody.heisenbergEvolution K' t V) * U t
                ∂gaussianReal 0 η
            M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
            ‖M‖ ≤ ‖W‖ ∧
            ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K V‖ ≤
              ‖W‖ * (2 * TNLean.PEPS.AreaLaw.graphBallLocalizationPrefactor R) * (Λ.card : ℝ) *
                (1 + swapBoundaryCoefficient R * J * (Λ.card : ℝ) * T) *
                Real.exp
                  (TNLean.PEPS.AreaLaw.graphBallLocalizationVelocity R (2 * J) * T -
                      1 / 2 * l) := by
  classical
  intro Q P s g pr p K F K' Z W V l B
  have hC : 0 < 2 * TNLean.PEPS.AreaLaw.graphBallLocalizationPrefactor R :=
    mul_pos two_pos (TNLean.PEPS.AreaLaw.graphBallLocalizationPrefactor_pos R)
  let gH : PlaneInteraction Λ (q * q) R :=
    (h.doubled.conj (ManyBody.pairSwapOp (X := fun _ ↦ Fin q) A) fun X ↦
        ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators A
          (h.doubled.mem X)).relabel (X' := fun _ ↦ Fin (q * q)) (Equiv.refl _)
      (fun _ ↦ finProdFinEquiv) (fun X : AdmissibleSupport Λ R ↦ X.1) fun _ _ ↦ Iff.rfl
  have hK' : gH.hamiltonian = K' :=
    ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled (X' := fun _ ↦ Fin (q * q))
      h A _ (Equiv.refl _) (fun _ ↦ finProdFinEquiv) _ fun _ _ ↦ Iff.rfl
  have hgHh : ∀ X, (gH.term X).IsHermitian := fun X ↦
    ManyBody.Interaction.isHermitian_relabel_term _ _ _ _
      (ManyBody.Interaction.isHermitian_conj_term _ _
        (ManyBody.Interaction.isHermitian_doubled_term (hh X)))
  have hgHn : ∀ X, ‖gH.term X‖ ≤ 2 * J := fun X ↦
    ((ManyBody.Interaction.norm_relabel_term _ _ _ _ _ X).trans
      (ManyBody.Interaction.norm_conj_term _ (ManyBody.pairSwapOp_mem_unitaryGroup A) _
        X)).trans_le ((ManyBody.Interaction.norm_doubled_term_le h X).trans
          (by linarith [hhJ X]))
  have hDK : K.IsHermitian :=
    (doubledHamiltonian_isHermitian (ManyBody.Interaction.isHermitian_hamiltonian hh)).reindex p
  have hV : V ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q := by
    obtain ⟨M, hM⟩ : ∃ M, V = ManyBody.place (X := fun _ ↦ Fin (q * q)) Q M :=
      ⟨_, reindex_physicalBuffer_eq_place q A C hAC W⟩
    rw [hM]
    exact ManyBody.place_mem_supportedOperators M
  obtain ⟨hDs, hDn⟩ := h.swapped_doubled_boundary_bound hhJ hJ A
  have hD : gH.hamiltonian - K ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Z := by
    rw [hK']; exact hDs
  have hVn : ‖V‖ ≤ ‖W‖ :=
    (Matrix.l2_opNorm_reindex_equiv (g.symm.trans p) _).trans_le
      (Matrix.l2_opNorm_one_kronecker_le W)
  obtain ⟨U, hU0, hU, hunit, hsupport, hM⟩ :=
    TNLean.PEPS.AreaLaw.supported_gaussian_integral (q * q) (Nat.mul_le_mul hq hq) R
      (by linarith : (0 : ℝ) ≤ 2 * J) Λ gH hgHh hgHn K V hDK Q Z hV hD l
  rw [hK'] at hU hM
  refine ⟨U, hU0, hU, hunit, hsupport, fun η T hT ↦ ?_⟩
  obtain ⟨hMs, hMn, hMe⟩ := hM η T hT
  refine ⟨hMs, hMn.trans hVn, hMe.trans ?_⟩
  have hcard : (0 : ℝ) ≤ Λ.card := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hVn hC.le) hcard)
      (add_le_add_right (mul_le_mul_of_nonneg_right hDn hT) 1)
      (add_nonneg zero_le_one (mul_nonneg (norm_nonneg (K' - K)) hT))
      (mul_nonneg (mul_nonneg (norm_nonneg W) hC.le) hcard))
    (Real.exp_pos _).le

end ManyBody.PlaneInteraction
end

end

section

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

open ManyBody (AdmissibleSupport PlaneInteraction)

namespace ManyBody.PlaneInteraction

open TNLean.Lattice

/-- The edge-boundary norm estimate for the actual swapped doubled Hamiltonian.
This finite-range extension combines polynomial-PEPS `02-information.tex`,
lines 416–424 and 513–524, with the area-law crossing-support count in
`02-initial.tex`, lines 202–206. The coefficient retains the diamond count
`v_R = 1 + 2 R (R + 1)`. -/
theorem swapped_doubled_boundary_bound_edgeBoundary
    {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
    (h : PlaneInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J) (hJ : 0 ≤ J)
    (A : Finset ↥Λ) :
    let pr := Equiv.arrowProdEquivProdArrow ↥Λ (fun _ ↦ Fin q) fun _ ↦ Fin q
    let p := pr.symm.trans (Equiv.arrowCongr (Equiv.refl ↥Λ) finProdFinEquiv)
    let K := Matrix.reindex p p (doubledHamiltonian h.hamiltonian)
    let F := Matrix.reindex p p (Matrix.reindex pr pr (ManyBody.pairSwapOp A))
    ‖F * K * Fᴴ - K‖ ≤
      swapBoundaryCoefficient R * ((1 + 2 * R * (R + 1) : ℕ) : ℝ) *
        J * ((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) := by
  intro pr p K F
  classical
  have hsum := h.pairSwapOp_conj_doubled_hamiltonian_sub_eq_sum_crossing A
  have hpaired : ‖F * K * Fᴴ - K‖ =
      ‖Matrix.reindex pr pr (ManyBody.pairSwapOp A) * doubledHamiltonian h.hamiltonian *
          (Matrix.reindex pr pr (ManyBody.pairSwapOp A))ᴴ -
        doubledHamiltonian h.hamiltonian‖ := by
    simpa only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
      ← Matrix.submatrix_mul_equiv (e₂ := p.symm), ← Matrix.conjTranspose_submatrix] using!
      Matrix.l2_opNorm_reindex_equiv p
        (Matrix.reindex pr pr (ManyBody.pairSwapOp A) * doubledHamiltonian h.hamiltonian *
          (Matrix.reindex pr pr (ManyBody.pairSwapOp A))ᴴ - doubledHamiltonian h.hamiltonian)
  rw [hpaired, hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm (X : AdmissibleSupport Λ R) :
      ‖Matrix.reindex pr pr (ManyBody.pairSwapOp A) * doubledHamiltonian (h.term X) *
          (Matrix.reindex pr pr (ManyBody.pairSwapOp A))ᴴ - doubledHamiltonian (h.term X)‖ ≤
        4 * J :=
    (TNLean.PEPS.EncodedFrame.norm_pairSwapOp_conj_doubledHamiltonian_sub_le A (h.term X)).trans
      (mul_le_mul_of_nonneg_left (hhJ X) (by norm_num))
  refine (Finset.sum_le_card_nsmul _ _ (4 * J) (fun X _ ↦ hterm X)).trans ?_
  have hcard : ((ManyBody.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).card : ℝ) ≤
      ((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) *
        (((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) := by
    exact_mod_cast TNLean.PEPS.AreaLaw.card_crossingTerms_le_edgeBoundary Λ R A
  calc
    _ = ((ManyBody.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).card : ℝ) * (4 * J) :=
      nsmul_eq_mul _ _
    _ ≤ (((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) *
        (((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)) * (4 * J) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      simp only [swapBoundaryCoefficient, Nat.cast_mul]
      ring

end ManyBody.PlaneInteraction

end
