/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.CrossingSupports
import TNLean.Lattice.PhysicalBufferCoordinates
import TNLean.Lattice.RegionalSwapSupport
import TNLean.PEPS.Approximation.SheetSwapDoubledTermNorm
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.SupportedGaussianIntegral

/-!
# The partially swapped doubled Hamiltonian at interaction range `R`

Let `h` be a Hamiltonian of interaction range `R` and term bound `J` on a finite domain `Λ`,
and let `A` be a set of sites. Double `h` on two replicas, pair the two coordinates at every
site, and conjugate by the swap `F_A` of the replicas on `A`. This file shows:

* the result is again a Hamiltonian of range `R` on `Λ`, now with local dimension `q²` and term
  bound `2J`, with the same supports (`LocalHamiltonian.swappedDoubled`);
* it differs from the doubled Hamiltonian only through the terms whose support crosses `A`
  (`LocalHamiltonian.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing`), the crossing
  terms `Entropy.crossingTerms` of the supports at the cut `A`, so the difference is supported
  on the sites `crossingSites` of these supports and has norm at most `4 μ_R J |Λ|`,
  with `μ_R = 2^(v_R - 1)` and `v_R = 1 + 2R(R + 1)`
  (`LocalHamiltonian.swapped_doubled_boundary_bound`);
* the supported Gaussian approximation of the physical buffer holds at range `R` with the
  graph-ball localization constants at range `R` and term bound `2J`
  (`LocalHamiltonian.supported_buffer_gaussian_integral`).

The sites of the crossing supports and their walks to both sides of `A` are in
`TNLean.Lattice.CrossingSupports`.

The polynomial-PEPS manuscript treats only site and nearest-neighbour terms on the open square,
which is range one; this file extends its boundary estimate to range `R`. The range-one
statements on the open square, with the constant `8 J L²`, are
`SquareHamiltonian.swapped_doubled_boundary_bound` and
`SquareHamiltonian.supported_buffer_gaussian_integral`, and are unchanged.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `02-information.tex`, lines 416–424 and 498–564, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `01-preliminaries.tex`, lines 82–103 (the count of supports through a site).

Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator NNReal

noncomputable section

namespace TNLean.Lattice

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- There are at most `μ_R |Λ|` supports of range `R`, with `μ_R = 2^(v_R - 1)`: every support
is nonempty, and at most `μ_R` supports contain a given site.
Source: area-law `01-preliminaries.tex`, lines 95–102. -/
theorem card_admissibleSupport_le (Λ : Finset (ℤ × ℤ)) (R : ℕ) :
    Fintype.card (AdmissibleSupport Λ R) ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) * Λ.card := by
  classical
  have hcover : (Finset.univ : Finset (AdmissibleSupport Λ R)) ⊆
      (Finset.univ : Finset (Site Λ)).biUnion
        fun v ↦ Finset.univ.filter fun X : AdmissibleSupport Λ R ↦ v ∈ X.1 := by
    intro X _
    obtain ⟨v, hv⟩ := X.2.1
    exact Finset.mem_biUnion.mpr
      ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr ⟨Finset.mem_univ X, hv⟩⟩
  calc Fintype.card (AdmissibleSupport Λ R)
      = (Finset.univ : Finset (AdmissibleSupport Λ R)).card := Finset.card_univ.symm
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ v : Site Λ, (Finset.univ.filter fun X : AdmissibleSupport Λ R ↦ v ∈ X.1).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _v : Site Λ, 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
        Finset.sum_le_sum fun v _ ↦ PEPS.AreaLaw.card_admissibleSupport_containing_le v
    _ = 2 ^ ((1 + 2 * R * (R + 1)) - 1) * Λ.card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm]

/-- The coefficient `4 μ_R` of the norm bound `4 μ_R J |Λ|` of the partial-swap perturbation at
range `R`, with `μ_R = 2^(v_R - 1)` supports through a site and `v_R = 1 + 2R(R + 1)`. -/
def swapBoundaryCoefficient (R : ℕ) : ℝ := 4 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)

theorem swapBoundaryCoefficient_nonneg (R : ℕ) : 0 ≤ swapBoundaryCoefficient R := by
  unfold swapBoundaryCoefficient
  positivity

namespace LocalHamiltonian

theorem doubledHamiltonian_isHermitian {n : Type*} [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (doubledHamiltonian A).IsHermitian := by
  simp only [Matrix.IsHermitian, doubledHamiltonian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hA.eq]

/-- **The partially swapped doubled Hamiltonian at range `R`.** Its term at a support `X` is the
doubled term of `h` at `X`, in paired-site coordinates, conjugated by the swap of the two
replicas on `A`. It is a Hamiltonian of range `R` with local dimension `q²` and term bound `2J`.
Source: polynomial-PEPS `02-information.tex`, lines 416–424, at range `R`. -/
def swappedDoubled (h : LocalHamiltonian Λ q R J) (A : Finset (Site Λ)) :
    LocalHamiltonian Λ (q * q) R (2 * J) where
  term X :=
    Matrix.reindex (sitePairConfigurationEquiv (Site Λ) q q)
        (sitePairConfigurationEquiv (Site Λ) q q) (sheetSwapOp q A) *
      Matrix.reindex (sitePairConfigurationEquiv (Site Λ) q q)
        (sitePairConfigurationEquiv (Site Λ) q q) (doubledHamiltonian (h.term X)) *
      (Matrix.reindex (sitePairConfigurationEquiv (Site Λ) q q)
        (sitePairConfigurationEquiv (Site Λ) q q) (sheetSwapOp q A))ᴴ
  supported X :=
    reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators A X.1 (h.supported X)
  hermitian X :=
    Matrix.isHermitian_mul_mul_conjTranspose _
      ((doubledHamiltonian_isHermitian (h.hermitian X)).reindex _)
  norm_le X := by
    set p := sitePairConfigurationEquiv (Site Λ) q q
    set F := Matrix.reindex p p (sheetSwapOp q A)
    have hFn : ‖F‖ ≤ 1 :=
      (Matrix.l2_opNorm_reindex_equiv p (sheetSwapOp q A)).le.trans
        (norm_sheetSwapOp_le_one A)
    have hDn : ‖doubledHamiltonian (h.term X)‖ ≤ J + J :=
      (norm_add_le _ _).trans (add_le_add
        ((Matrix.l2_opNorm_kronecker_one_le _).trans (h.norm_le X))
        ((Matrix.l2_opNorm_one_kronecker_rect_le _).trans (h.norm_le X)))
    simpa only [one_mul, mul_one, two_mul] using
      norm_mul_le_of_le
        (norm_mul_le_of_le hFn ((Matrix.l2_opNorm_reindex_equiv p _).le.trans hDn))
        ((Matrix.l2_opNorm_conjTranspose F).trans_le hFn)

/-- The doubling map is additive. -/
private theorem doubledHamiltonian_sum {n ι : Type*} [DecidableEq n]
    (s : Finset ι) (f : ι → Matrix n n ℂ) :
    doubledHamiltonian (∑ i ∈ s, f i) = ∑ i ∈ s, doubledHamiltonian (f i) := by
  let D : Matrix n n ℂ →ₗ[ℂ] Matrix (n × n) (n × n) ℂ :=
    (Matrix.kroneckerBilinear (R := ℂ)).flip (1 : Matrix n n ℂ) +
      Matrix.kroneckerBilinear (R := ℂ) (1 : Matrix n n ℂ)
  change D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i)
  exact map_sum D f s

/-- The partially swapped doubled Hamiltonian is the conjugate `F K Fᴴ` of the doubled
Hamiltonian `K` in paired-site coordinates. -/
theorem swappedDoubled_operator (h : LocalHamiltonian Λ q R J) (A : Finset (Site Λ)) :
    let p := sitePairConfigurationEquiv (Site Λ) q q
    let F := Matrix.reindex p p (sheetSwapOp q A)
    (h.swappedDoubled A).operator =
      F * Matrix.reindex p p (doubledHamiltonian h.operator) * Fᴴ := by
  intro p F
  have hre : Matrix.reindex p p (doubledHamiltonian h.operator) =
      ∑ X, Matrix.reindex p p (doubledHamiltonian (h.term X)) := by
    change (Matrix.reindexAlgEquiv ℂ ℂ p) (doubledHamiltonian (∑ X, h.term X)) = _
    rw [doubledHamiltonian_sum, map_sum]
    rfl
  rw [hre, Finset.mul_sum, Finset.sum_mul]
  rfl

/-- **Only the crossing supports contribute to the partial-swap perturbation.** The difference
between the doubled Hamiltonian and its conjugate by the swap on `A` is the sum of the
corresponding differences for the terms whose support crosses `A`.
Source: polynomial-PEPS `02-information.tex`, lines 416–424 and 513–524, at range `R`. -/
theorem sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing (h : LocalHamiltonian Λ q R J)
    (A : Finset (Site Λ)) :
    let F := sheetSwapOp q A
    F * doubledHamiltonian h.operator * Fᴴ - doubledHamiltonian h.operator =
      ∑ X ∈ Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A,
        (F * doubledHamiltonian (h.term X) * Fᴴ - doubledHamiltonian (h.term X)) := by
  classical
  intro F
  have hcancel (X : AdmissibleSupport Λ R)
      (hX : X ∉ Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A) :
      F * doubledHamiltonian (h.term X) * Fᴴ - doubledHamiltonian (h.term X) = 0 := by
    have hX : X.1 ⊆ A ∨ Disjoint X.1 A := by
      simp only [Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
        not_exists, not_not] at hX
      by_cases hXA : ∃ v ∈ X.1, v ∈ A
      · exact Or.inl fun v hv ↦ hX hXA v hv
      · push Not at hXA
        exact Or.inr (Finset.disjoint_left.mpr hXA)
    refine sub_eq_zero.mpr
      (sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators (h.supported X) ?_)
    rcases hX with hX | hX
    · exact Or.inl (Finset.coe_subset.mpr hX)
    · exact Or.inr (Finset.disjoint_coe.mpr hX)
  have hsum : F * doubledHamiltonian h.operator * Fᴴ - doubledHamiltonian h.operator =
      ∑ X, (F * doubledHamiltonian (h.term X) * Fᴴ - doubledHamiltonian (h.term X)) := by
    rw [LocalHamiltonian.operator, doubledHamiltonian_sum, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
  rw [hsum]
  exact (Finset.sum_subset (Finset.subset_univ _) fun X _ hX ↦ hcancel X hX).symm

/-- **The partial-swap perturbation at range `R`.** In paired-site coordinates, `F K Fᴴ - K` is
supported on the sites of the supports crossing `A`, and has norm at most `4 μ_R J |Λ|`
(`swapBoundaryCoefficient R * J * |Λ|`). The individual terms are Hermitian, as the model
requires; the bound uses only their norms.
Source: polynomial-PEPS `02-information.tex`, lines 416–424 and 513–524, at range `R`, with the
count of supports through a site of area-law `01-preliminaries.tex`, lines 95–102. -/
theorem swapped_doubled_boundary_bound (h : LocalHamiltonian Λ q R J) (hJ : 0 ≤ J)
    (A : Finset (Site Λ)) :
    let p := sitePairConfigurationEquiv (Site Λ) q q
    let K := Matrix.reindex p p (doubledHamiltonian h.operator)
    let F := Matrix.reindex p p (sheetSwapOp q A)
    F * K * Fᴴ - K ∈ supportedOperators (q * q) (crossingSites Λ R A : Set (Site Λ)) ∧
      ‖F * K * Fᴴ - K‖ ≤ swapBoundaryCoefficient R * J * (Λ.card : ℝ) := by
  classical
  intro p K F
  set T := Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A
  have hsum := congrArg (Matrix.reindex p p)
    (h.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing A)
  simp only [← Matrix.coe_reindexRingEquiv, map_sum, map_sub, map_mul] at hsum
  change F * K * Fᴴ - K = ∑ X ∈ T,
    (F * Matrix.reindex p p (doubledHamiltonian (h.term X)) * Fᴴ -
      Matrix.reindex p p (doubledHamiltonian (h.term X))) at hsum
  have hnorm (M : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
      ‖F * Matrix.reindex p p (doubledHamiltonian M) * Fᴴ -
        Matrix.reindex p p (doubledHamiltonian M)‖ ≤ 4 * ‖M‖ := by
    simpa only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
      ← Matrix.submatrix_mul_equiv (e₂ := p.symm), ← Matrix.conjTranspose_submatrix] using!
      (Matrix.l2_opNorm_reindex_equiv p
        (sheetSwapOp q A * doubledHamiltonian M * (sheetSwapOp q A)ᴴ -
          doubledHamiltonian M)).trans_le
        (PEPS.EncodedFrame.norm_sheetSwapOp_conj_doubledHamiltonian_sub_le A M)
  have hplain (S : Finset (Site Λ))
      {M : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
      (hM : M ∈ supportedOperators q (S : Set (Site Λ))) :
      Matrix.reindex p p (doubledHamiltonian M) ∈
        supportedOperators (q * q) (S : Set (Site Λ)) := by
    simpa only [Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv,
      sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
        (R := ∅) hM (Or.inr (by simp))] using!
      reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators ∅ S hM
  have hsupport : F * K * Fᴴ - K ∈
      supportedOperators (q * q) (crossingSites Λ R A : Set (Site Λ)) :=
    hsum.symm ▸ (supportedOperators (q * q) (crossingSites Λ R A : Set (Site Λ))).sum_mem
      fun X hX ↦ supportedOperators_mono
        (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem
          (fun X : AdmissibleSupport Λ R ↦ X.1) hX))
        ((supportedOperators (q * q) (X.1 : Set (Site Λ))).sub_mem
          (reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators A X.1
            (h.supported X))
          (hplain X.1 (h.supported X)))
  have hbound : ‖F * K * Fᴴ - K‖ ≤ (T.card : ℝ) * (4 * J) := by
    simpa only [hsum, nsmul_eq_mul] using
      (norm_sum_le T fun X ↦
        F * Matrix.reindex p p (doubledHamiltonian (h.term X)) * Fᴴ -
          Matrix.reindex p p (doubledHamiltonian (h.term X))).trans
        (Finset.sum_le_card_nsmul T _ (4 * J) fun X _ ↦
          (hnorm (h.term X)).trans
            (mul_le_mul_of_nonneg_left (h.norm_le X) (by norm_num)))
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
`SquareHamiltonian.supported_buffer_gaussian_integral`.
Source: polynomial-PEPS, Section 2, `eq:info-local-two-sided`, lines 513–562, with the
constants of `eq:info-lr` (lines 486–496). -/
theorem supported_buffer_gaussian_integral (hq : 1 ≤ q) (hJ : 0 ≤ J)
    (h : LocalHamiltonian Λ q R J) (A C : Finset (Site Λ)) (hAC : Disjoint A C) :
    let Q := (A ∪ C)ᶜ
    let P := Fin (Fintype.card (A → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : Site Λ ↦ Fin q) A C hAC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (Q → Fin q))
    let p := sitePairConfigurationEquiv (Site Λ) q q
    let K := reindex p p (doubledHamiltonian h.operator)
    let F := reindex p p (sheetSwapOp q A)
    let K' := F * K * Fᴴ
    let Z := crossingSites Λ R A
    ∀ W : Matrix ((Q → Fin q) × (Q → Fin q)) ((Q → Fin q) × (Q → Fin q)) ℂ,
      let V := reindex (g.symm.trans p) (g.symm.trans p)
        ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W)
      ∀ l : ℕ,
        let B := graphNeighborhood Λ l (Q ∪ Z)
        ∃ U : ℝ → Matrix (Configuration Λ (q * q)) (Configuration Λ (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • siteExpectation (q * q) B
              (heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ unitaryGroup (Configuration Λ (q * q)) ℂ) ∧
          (∀ t, U t ∈ supportedOperators (q * q) (B : Set (Site Λ))) ∧
          ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
            let M := ∫ t : ℝ in Set.Icc (-T) T,
              siteExpectation (q * q) B (heisenbergEvolution K' t V) * U t
                ∂gaussianReal 0 η
            M ∈ supportedOperators (q * q) (B : Set (Site Λ)) ∧
            ‖M‖ ≤ ‖W‖ ∧
            ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K V‖ ≤
              ‖W‖ * (2 * PEPS.AreaLaw.graphBallLocalizationPrefactor R) * (Λ.card : ℝ) *
                (1 + swapBoundaryCoefficient R * J * (Λ.card : ℝ) * T) *
                Real.exp
                  (PEPS.AreaLaw.graphBallLocalizationVelocity R (2 * J) * T - 1 / 2 * l) := by
  classical
  intro Q P s g p K F K' Z W V l B
  have hC : 0 < 2 * PEPS.AreaLaw.graphBallLocalizationPrefactor R :=
    mul_pos two_pos (PEPS.AreaLaw.graphBallLocalizationPrefactor_pos R)
  set gH := h.swappedDoubled A
  have hK' : gH.operator = K' := h.swappedDoubled_operator A
  have hDK : K.IsHermitian :=
    (doubledHamiltonian_isHermitian h.operator_isHermitian).reindex p
  have hV : V ∈ supportedOperators (q * q) (Q : Set (Site Λ)) := by
    have hlift := siteLift_mem_supportedOperators Q
      (reindex (sitePairConfigurationEquiv Q q q) (sitePairConfigurationEquiv Q q q) W)
    rw [← reindex_physicalBuffer_eq_siteLift q A C hAC W] at hlift
    exact hlift
  obtain ⟨hDs, hDn⟩ := h.swapped_doubled_boundary_bound hJ A
  have hD : gH.operator - K ∈ supportedOperators (q * q) (Z : Set (Site Λ)) := by
    rw [hK']; exact hDs
  have hVn : ‖V‖ ≤ ‖W‖ :=
    (Matrix.l2_opNorm_reindex_equiv (g.symm.trans p) _).trans_le
      (Matrix.l2_opNorm_one_kronecker_rect_le W)
  obtain ⟨U, hU0, hU, hunit, hsupport, hM⟩ :=
    PEPS.AreaLaw.supported_gaussian_integral (q * q) (Nat.mul_le_mul hq hq) R
      (by linarith : (0 : ℝ) ≤ 2 * J) Λ gH K V hDK Q Z hV hD l
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

end LocalHamiltonian

end TNLean.Lattice
