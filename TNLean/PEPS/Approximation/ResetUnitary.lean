/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.PhysicalBufferUniform
import QICLean.Analysis.GaussianFilter.LocalizationParameters
import QICLean.Analysis.GaussianFilter.Reindex
import QICLean.Entropy.FiniteProductSplitting
import QICLean.Entropy.ProductMarginals
import TNLean.PEPS.Approximation.SupportedPhysicalBufferGaussian
import TNLean.PEPS.Approximation.SupportedPolarUnitary

/-!
# The supported unitary of the information reset

Let `Ω` be a gapped ground state of an open square Hamiltonian, and let `R, C` be disjoint
physical regions with `I_Ω(R : C) ≤ b`. On two replicas put `Ψ = Ω ⊗ Ω` and `Φ = F_R Ψ`,
where `F_R` exchanges the replicas on `R`. With `B = 1 + b + log L`, this module constructs a
unitary `U` on the doubled system with

* `U` acting on the graph neighborhood of radius `ℓ = ⌈K B⌉` of the buffer `Q = (R ∪ C)ᶜ` and
  of the endpoints of the edges crossing `R`;
* `‖U Ψ - Φ‖ ≤ C L^(-r)`.

The constants `C, K` depend only on `q, J, Δ` and the exponent `r`, and are named:
`K = resetRadius J Δ r` and `C = resetUnitaryPrefactor J Δ r`, built from the Gaussian
variance and cutoff coefficients `resetVariance Δ r` and `resetCutoff Δ r` and from the
localization prefactor and velocity of the doubled square Hamiltonian. No gap of a restricted
Hamiltonian, rank bound or bound on purifying dimensions is assumed.

The proof composes the physical-buffer Gaussian filter, its dimension-uniform parameter
choice, the localization of the truncated Gaussian integral on the square, and the polar
correction on the same support. It first identifies the regional mutual information with the
relative entropy of the joint regional state from the product of its marginals, and the
regional sheet swap with the partial swap of the retained regional registers.

## Main statements

* `TNLean.PEPS.Approximation.splitTwoRegions_sheetSwap`,
  `TNLean.PEPS.Approximation.submatrix_partialSwap_kronecker_one_eq_sheetSwapOp`: the
  regional sheet swap in the coordinates of the two regions and the buffer.
* `TNLean.PEPS.Approximation.quantumRelativeEntropy_splitTwoRegionsState_eq_mutualInformation`.
* `TNLean.PEPS.Approximation.resetVariance`, `TNLean.PEPS.Approximation.resetCutoff`,
  `TNLean.PEPS.Approximation.resetRadius`, `TNLean.PEPS.Approximation.resetFilterPrefactor`,
  `TNLean.PEPS.Approximation.resetUnitaryPrefactor`: the constants of the reset.
* `TNLean.PEPS.Approximation.regional_physicalBuffer_filter`,
  `TNLean.PEPS.Approximation.SquareHamiltonian.reset_localized_filter`,
  `TNLean.PEPS.Approximation.SquareHamiltonian.reset_unitary`: the statements below with
  these constants.
* `TNLean.PEPS.Approximation.exists_regional_physicalBuffer_filter`: the two-sided Gaussian
  filter of `eq:info-gaussian-two-sided` in arbitrary coordinates of the two replicas.
* `TNLean.PEPS.Approximation.exists_supported_unitary_of_two_sided`: the polar step of
  `eq:info-reset-polar-errors` and `eq:info-reset-unitary`.
* `TNLean.PEPS.Approximation.SquareHamiltonian.exists_reset_localized_filter`: the localized
  two-sided filter of `eq:info-local-two-sided`.
* `TNLean.PEPS.Approximation.SquareHamiltonian.exists_reset_unitary`: the unitary of
  `eq:info-reset-unitary`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`,
  lines 355–599, equations `eq:info-reset-overlap`, `eq:info-gaussian-two-sided`,
  `eq:info-local-two-sided`, `eq:info-reset-polar-errors` and `eq:info-reset-unitary`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator NNReal ComplexOrder
open TNLean.Lattice

namespace TNLean.PEPS.Approximation

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In the coordinates of two disjoint regions `R, C` and their complement, swapping the two
replicas on `R` exchanges the two retained `R` registers and fixes everything else.
Source: `02-information.tex`, lines 362–365 and 398–410. -/
theorem splitTwoRegions_sheetSwap (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C)
    (x : (ι → Fin q) × (ι → Fin q)) :
    let Q := (R ∪ C)ᶜ
    let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (Q → Fin q))
    g (EncodedFrame.sheetSwap q R x) =
      (Equiv.partialSwap (Fin (Fintype.card (R → Fin q))) (Fin (Fintype.card (C → Fin q)))
        (g x).1, (g x).2) := by
  intro Q P s g
  have hC : ∀ v : C, (v : ι) ∉ R := fun v hv ↦ Finset.disjoint_left.mp hRC hv v.2
  have hQ : ∀ v : Q, (v : ι) ∉ R := fun v hv ↦
    Finset.mem_compl.mp v.2 (Finset.mem_union_left C hv)
  simp only [g, s, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.doubledRegroup, Equiv.bipartiteRegroup, Equiv.coe_fn_mk,
    FiniteProduct.splitTwoRegionsEquiv, FiniteProduct.unionEquiv, Equiv.refl_apply,
    Equiv.partialSwap_apply, EncodedFrame.sheetSwap]
  refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) (Prod.ext ?_ ?_) <;>
    dsimp only
  · congr 1; funext v; simp [v.2]
  · congr 1; funext v; simp [hC v]
  · congr 1; funext v; simp [v.2]
  · congr 1; funext v; simp [hC v]
  · funext v; simp [hQ v]
  · funext v; simp [hQ v]

/-- The regional sheet swap is the partial swap of the retained `R` registers, tensored with
the identity on the two copies of the buffer.
Source: `02-information.tex`, lines 362–365 and 398–410. -/
theorem submatrix_partialSwap_kronecker_one_eq_sheetSwapOp (q : ℕ) (R C : Finset ι)
    (hRC : Disjoint R C) :
    let Q := (R ∪ C)ᶜ
    let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (Q → Fin q))
    (partialSwap (Fin (Fintype.card (R → Fin q))) (Fin (Fintype.card (C → Fin q))) ⊗ₖ
        (1 : Matrix ((Q → Fin q) × (Q → Fin q)) ((Q → Fin q) × (Q → Fin q)) ℂ)).submatrix
        g g = EncodedFrame.sheetSwapOp q R := by
  intro Q P s g
  ext x y
  have hiff : (g y).1 = Equiv.partialSwap _ _ (g x).1 ∧ (g x).2 = (g y).2 ↔
      EncodedFrame.sheetSwap q R x = y := by
    rw [← g.apply_eq_iff_eq, splitTwoRegions_sheetSwap q R C hRC x]
    exact ⟨fun h ↦ Prod.ext h.1.symm h.2,
      fun h ↦ ⟨(Prod.ext_iff.mp h).1.symm, (Prod.ext_iff.mp h).2⟩⟩
  simp only [submatrix_apply, kroneckerMap_apply, partialSwap_apply, one_apply,
    EncodedFrame.sheetSwapOp, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, ← hiff, ite_zero_mul_ite_zero, mul_one]

/-- Doubling commutes with a coordinate change applied to both replicas. -/
theorem reindex_prodCongr_doubledHamiltonian {m n : Type*} [DecidableEq m]
    [DecidableEq n] (e : m ≃ n) (H : Matrix m m ℂ) :
    reindex (e.prodCongr e) (e.prodCongr e) (doubledHamiltonian H) =
      doubledHamiltonian (reindex e e H) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [doubledHamiltonian, kroneckerMap_apply, one_apply, e.symm.injective.eq_iff]

/-- The relative entropy of the joint state of two disjoint regions from the product of its
marginals is their regional mutual information.
Source: `02-information.tex`, lines 368–375. -/
theorem quantumRelativeEntropy_splitTwoRegionsState_eq_mutualInformation (q : ℕ)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (R C : Finset ι) (hRC : Disjoint R C) :
    let ψ := FiniteProduct.splitTwoRegionsState (fun _ : ι ↦ Fin q) Ω R C hRC
    quantumRelativeEntropy (partialTraceRight (vecMulVec ψ (star ψ)))
        (partialTraceRight (partialTraceRight (vecMulVec ψ (star ψ))) ⊗ₖ
          partialTraceLeft (partialTraceRight (vecMulVec ψ (star ψ)))) =
      FiniteProduct.mutualInformation (fun _ : ι ↦ Fin q) Ω R C := by
  intro ψ
  rw [FiniteProduct.partialTraceRight_splitTwoRegionsState,
    quantumRelativeEntropy_product_marginals
      (FiniteProduct.jointMatrix_posSemidef (fun _ : ι ↦ Fin q) Ω R C hRC),
    FiniteProduct.mutualInformation_eq_matrix (fun _ : ι ↦ Fin q) Ω R C hRC]
  rfl

end Coordinates

section Transport

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Distances of images of vectors are unchanged by a simultaneous change of coordinates. -/
theorem norm_reindex_mulVec_sub (E : n ≃ m) (M : Matrix n n ℂ) (x y : n → ℂ) :
    ‖WithLp.toLp 2 (reindex E E M *ᵥ (x ∘ E.symm)) - WithLp.toLp 2 (y ∘ E.symm)‖ =
      ‖WithLp.toLp 2 (M *ᵥ x) - WithLp.toLp 2 y‖ := by
  rw [Matrix.reindex_mulVec, ← WithLp.toLp_sub, ← WithLp.toLp_sub]
  exact EuclideanSpace.norm_toLp_comp_equiv E.symm (M *ᵥ x - y)

/-- An operator close in norm to one with two small residuals has two small residuals. -/
theorem norm_two_sided_le_of_norm_sub_le [DecidableEq n] {M M' : Matrix n n ℂ} {ψ φ : n → ℂ}
    {z : ℂ} {δ ε : ℝ} (hψ : ‖WithLp.toLp 2 ψ‖ = 1) (hφ : ‖WithLp.toLp 2 φ‖ = 1)
    (hM : ‖M - M'‖ ≤ δ) (hfwd : ‖WithLp.toLp 2 (M' *ᵥ ψ) - z • WithLp.toLp 2 φ‖ ≤ ε)
    (hrev : ‖WithLp.toLp 2 (M'ᴴ *ᵥ φ) - z • WithLp.toLp 2 ψ‖ ≤ ε) :
    ‖WithLp.toLp 2 (M *ᵥ ψ) - z • WithLp.toLp 2 φ‖ ≤ δ + ε ∧
      ‖WithLp.toLp 2 (Mᴴ *ᵥ φ) - z • WithLp.toLp 2 ψ‖ ≤ δ + ε := by
  have hop (A : Matrix n n ℂ) (x : n → ℂ) :
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖ := by
    simpa only [toEuclideanCLM_toLp, l2_opNorm_toEuclideanCLM] using
      (toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 x)
  have hsplit (A A' : Matrix n n ℂ) (x : n → ℂ) (w : EuclideanSpace ℂ n) :
      ‖WithLp.toLp 2 (A *ᵥ x) - w‖ ≤
        ‖WithLp.toLp 2 ((A - A') *ᵥ x)‖ + ‖WithLp.toLp 2 (A' *ᵥ x) - w‖ := by
    rw [sub_mulVec, WithLp.toLp_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  constructor
  · refine (hsplit M M' ψ _).trans (add_le_add ((hop _ ψ).trans ?_) hfwd)
    rw [hψ, mul_one]
    exact hM
  · refine (hsplit Mᴴ M'ᴴ φ _).trans (add_le_add ((hop _ φ).trans ?_) hrev)
    rw [hφ, mul_one, ← conjTranspose_sub, l2_opNorm_conjTranspose]
    exact hM

end Transport


section RegionalCoordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Type*}

/-- The doubled Hamiltonian in regional coordinates is the doubled Hamiltonian in any other
coordinates of the two replicas.
Source: `02-information.tex`, lines 416–424. -/
theorem reindex_regional_doubledHamiltonian (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C)
    (t : (ι → Fin q) × (ι → Fin q) ≃ N) (H : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q))
    reindex (g.symm.trans t) (g.symm.trans t)
        (reindex (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q))
          (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q)) (doubledHamiltonian (reindex s s H))) =
      reindex t t (doubledHamiltonian H) := by
  intro P s g
  rw [← reindex_prodCongr_doubledHamiltonian]
  ext x y
  simp [g, Prod.map]

/-- The partial swap of the retained `R` registers is the regional sheet swap in any
coordinates of the two replicas.
Source: `02-information.tex`, lines 362–365 and 398–410. -/
theorem reindex_regional_partialSwap (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C)
    (t : (ι → Fin q) × (ι → Fin q) ≃ N) :
    let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q))
    reindex (g.symm.trans t) (g.symm.trans t)
        (partialSwap (Fin (Fintype.card (R → Fin q))) (Fin (Fintype.card (C → Fin q))) ⊗ₖ
          (1 : Matrix ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q))
            ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q)) ℂ)) =
      reindex t t (EncodedFrame.sheetSwapOp q R) := by
  intro P s g
  rw [← submatrix_partialSwap_kronecker_one_eq_sheetSwapOp q R C hRC]
  ext x y
  rfl

/-- Two regional copies of a vector form the doubled vector in any coordinates of the two
replicas. -/
theorem doubledRegroup_splitTwoRegionsState_comp (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C)
    (t : (ι → Fin q) × (ι → Fin q) ≃ N) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q))
    doubledRegroup (FiniteProduct.splitTwoRegionsState (fun _ : ι ↦ Fin q) Ω R C hRC) ∘
        (g.symm.trans t).symm =
      fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2 := by
  intro P s g
  funext c
  simp [g, s, doubledRegroup, Equiv.doubledRegroup, Equiv.bipartiteRegroup,
    FiniteProduct.splitTwoRegionsState]

end RegionalCoordinates

universe u v w

/-! ### The constants of the information reset -/

/-- The variance coefficient `A = 2 (30 + r) / Δ²` of the Gaussian filter of the information
reset: the variance at size `L` and information bound `b` is `A (1 + b + log L)`. It meets
the requirement `A Δ² / 2 ≥ 30 + r` with equality.
Source: `02-information.tex`, lines 426–427 and 443–444 (`h = A B_*` with
`A Δ²/2 ≥ 10 + r_* + 20`). -/
noncomputable def resetVariance (Δ r : ℝ) : ℝ := 2 * (30 + r) / Δ ^ 2

/-- The cutoff coefficient `T₀ = 2 (30 + r) / Δ` of the Gaussian filter of the information
reset: the time integral is truncated at `T₀ (1 + b + log L)`. It meets the requirement
`T₀² / (2 A) ≥ 30 + r` with equality for `A = resetVariance Δ r`.
Source: `02-information.tex`, lines 446–450 (`T_0^2/(2A) ≥ 10 + r_* + 20`). -/
noncomputable def resetCutoff (Δ r : ℝ) : ℝ := 2 * (30 + r) / Δ

/-- The localization radius coefficient `K = (v T₀ + 15 + r) / μ` of the information reset,
with the velocity `v = squareLocalizationVelocity J`, the decay rate `μ = 1/2` and the
cutoff `T₀ = resetCutoff Δ r`; the support radius at size `L` is `⌈K (1 + b + log L)⌉`.
Source: `K_loc` of `02-information.tex`, lines 551–554, chosen after `T₀`. -/
noncomputable def resetRadius (J Δ r : ℝ) : ℝ :=
  (squareLocalizationVelocity J * resetCutoff Δ r + 15 + r) / (1 / 2)

/-- The prefactor `C' (1 + 8J) (1 + T₀) + 3` of the two residuals of the localized filter of
the information reset, with `C' = squareLocalizationPrefactor`, `T₀ = resetCutoff Δ r`. The
summand `3` bounds the Gaussian and truncation errors, the rest the localization error.
Source: `02-information.tex`, lines 551–562, equation `eq:info-local-two-sided`. -/
noncomputable def resetFilterPrefactor (J Δ r : ℝ) : ℝ :=
  squareLocalizationPrefactor * (1 + 8 * J) * (1 + resetCutoff Δ r) + 3

/-- The prefactor `2 C` of the error `‖U Ψ - Φ‖ ≤ 2 C L^(-r)` of the unitary of the
information reset, with `C = resetFilterPrefactor J Δ r`.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
noncomputable def resetUnitaryPrefactor (J Δ r : ℝ) : ℝ := 2 * resetFilterPrefactor J Δ r

theorem resetVariance_pos {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) : 0 < resetVariance Δ r := by
  unfold resetVariance; positivity

theorem resetCutoff_pos {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) : 0 < resetCutoff Δ r := by
  unfold resetCutoff; positivity

theorem resetVariance_mul_sq_div_two {Δ r : ℝ} (hΔ : Δ ≠ 0) :
    resetVariance Δ r * Δ ^ 2 / 2 = 30 + r := by
  unfold resetVariance; field_simp

theorem resetCutoff_sq_div {Δ r : ℝ} (hΔ : Δ ≠ 0) (hr : 30 + r ≠ 0) :
    resetCutoff Δ r ^ 2 / (2 * resetVariance Δ r) = 30 + r := by
  unfold resetCutoff resetVariance; field_simp

theorem resetRadius_pos {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 < resetRadius J Δ r := by
  have := squareLocalizationVelocity_nonneg hJ
  have := resetCutoff_pos hΔ hr
  unfold resetRadius; positivity

theorem resetFilterPrefactor_pos {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 < resetFilterPrefactor J Δ r := by
  have := squareLocalizationPrefactor_pos
  have := resetCutoff_pos hΔ hr
  unfold resetFilterPrefactor; positivity

theorem resetUnitaryPrefactor_pos {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 < resetUnitaryPrefactor J Δ r :=
  mul_pos two_pos (resetFilterPrefactor_pos hJ hΔ hr)

/-- The closed form `K = 1280 e² (J/Δ)(30 + r) + 2 r + 30` of the localization radius
coefficient of the information reset. -/
theorem resetRadius_eq (J Δ r : ℝ) :
    resetRadius J Δ r = 1280 * Real.exp 2 * (J / Δ) * (30 + r) + 2 * r + 30 := by
  rw [resetRadius, squareLocalizationVelocity_eq, resetCutoff]
  ring

/-- The closed form of the unitary prefactor of the information reset,
`2 (64 e^{3/2} / (1 - e^{-1/2}) (1 + 8J) (1 + 2 (30 + r) / Δ) + 3)`. -/
theorem resetUnitaryPrefactor_eq (J Δ r : ℝ) :
    resetUnitaryPrefactor J Δ r =
      2 * (64 * Real.exp (3 / 2) / (1 - Real.exp (-(1 / 2))) * (1 + 8 * J) *
        (1 + 2 * (30 + r) / Δ) + 3) := by
  rw [resetUnitaryPrefactor, resetFilterPrefactor, squareLocalizationPrefactor_eq, resetCutoff]

/-- Any Gaussian constants `A, T₀` meeting the two numerical conditions of the manuscript
give the dimension-uniform physical-buffer filter. This is the argument of
`GaussianFilter.exists_uniform_physicalBuffer_filter` with the constants kept visible.
Source: `02-information.tex`, lines 395–452. -/
private theorem uniform_physicalBuffer_filter_of_parameters {Δ r A T₀ : ℝ} (hΔ : 0 < Δ)
    (hr : 0 ≤ r) (hA : 0 < A) (hT₀ : 0 ≤ T₀) (hgap : 30 + r ≤ A * Δ ^ 2 / 2)
    (htail : 30 + r ≤ T₀ ^ 2 / (2 * A)) :
    ∀ (R : Type u) (C : Type v) (Q : Type w)
      [Fintype R] [Fintype C] [Fintype Q]
      [DecidableEq R] [DecidableEq C] [DecidableEq Q]
      (H : Matrix ((R × C) × Q) ((R × C) × Q) ℂ)
      (Ω : (R × C) × Q → ℂ) (E₀ b : ℝ),
      star Ω ⬝ᵥ Ω = 1 → H *ᵥ Ω = (E₀ : ℂ) • Ω →
      (H - (E₀ : ℂ) • 1 -
        (Δ : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef → 0 ≤ b →
      quantumRelativeEntropy
        (partialTraceRight (vecMulVec Ω (star Ω)))
        (partialTraceRight (partialTraceRight (vecMulVec Ω (star Ω))) ⊗ₖ
          partialTraceLeft (partialTraceRight (vecMulVec Ω (star Ω)))) ≤ b →
      let e := Equiv.doubledRegroup (R × C) Q
      let ψ := doubledRegroup Ω
      let φ := physicalLeftSwap ψ
      let S := partialSwap R C ⊗ₖ (1 : Matrix (Q × Q) (Q × Q) ℂ)
      let K := reindex e e (doubledHamiltonian H)
      let K' := S * K * Sᴴ
      let Ψ : EuclideanSpace ℂ _ := WithLp.toLp 2 ψ
      let Φ : EuclideanSpace ℂ _ := WithLp.toLp 2 φ
      ∃ (W : Matrix (Q × Q) (Q × Q) ℂ) (z : ℝ),
        let V := (1 : Matrix ((R × C) × (R × C)) ((R × C) × (R × C)) ℂ) ⊗ₖ W
        W.IsHermitian ∧ ‖W‖ ≤ 1 ∧ Real.exp (-2 * b) ≤ z ∧
        star φ ⬝ᵥ (V *ᵥ ψ) = (z : ℂ) ∧
        ∀ L : ℝ, 1 ≤ L →
          let B := 1 + b + Real.log L
          let h := Real.toNNReal (A * B)
          let T := T₀ * B
          let M := GaussianFilter.gaussianIntertwinerTruncated h T K' K V
          (h : ℝ) = A * B ∧ 0 < (h : ℝ) ∧ 0 ≤ T ∧ ‖M‖ ≤ 1 ∧
            ‖toEuclideanLin M Ψ - (z : ℂ) • Φ‖ ≤
              3 * Real.exp (-10 * b) * L ^ (-r) ∧
            ‖toEuclideanLin Mᴴ Φ - (z : ℂ) • Ψ‖ ≤
              3 * Real.exp (-10 * b) * L ^ (-r) := by
  intro R C Q _ _ _ _ _ _ H Ω E₀ b hΩ heigen hgap' hb hbound
  obtain ⟨W, z, hWherm, hW, hz, hoverlap, hfilter⟩ :=
    GaussianFilter.exists_physicalBuffer_gaussian_filter H Ω hΩ heigen hgap' hΔ hb hbound
  refine ⟨W, z, hWherm, hW, hz, hoverlap, ?_⟩
  intro L hL
  let B := 1 + b + Real.log L
  let h := Real.toNNReal (A * B)
  let T := T₀ * B
  have hs := GaussianFilter.gaussian_error_bounds_of_parameter_constants hA hT₀ hr hgap htail
    hb hL
  have hh : (h : ℝ) = A * B := Real.coe_toNNReal _ hs.1.le
  obtain ⟨hM, hforward, hreverse⟩ := (hfilter h).2.2.2 T hs.2.1
  have hsum : Real.exp (-(h : ℝ) * Δ ^ 2 / 2) +
      2 * Real.exp (-T ^ 2 / (2 * (h : ℝ))) ≤
        3 * Real.exp (-10 * b) * L ^ (-r) := by
    rw [hh]
    nlinarith only [hs.2.2.1, hs.2.2.2]
  refine ⟨hh, ?_, hs.2.1, hM, hforward.trans hsum, hreverse.trans hsum⟩
  rw [hh]
  exact hs.1

/-- **The two-sided Gaussian filter in arbitrary coordinates of the two replicas, with
explicit constants.** The statement of `exists_regional_physicalBuffer_filter` holds with
the variance coefficient `A = resetVariance Δ r = 2 (30 + r) / Δ²` and the cutoff coefficient
`T₀ = resetCutoff Δ r = 2 (30 + r) / Δ`.
Source: `02-information.tex`, lines 355–452, with `A, T₀` at lines 443–450. -/
theorem regional_physicalBuffer_filter {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {N : Type v} [Fintype N] [DecidableEq N]
      (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C) (t : (ι → Fin q) × (ι → Fin q) ≃ N)
      (H : Matrix (ι → Fin q) (ι → Fin q) ℂ) (E₀ : ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q))
      (b : ℝ), Matrix.IsGappedGroundState H E₀ Ω Δ → 0 ≤ b →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
      let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
      let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
      let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q))
      let K := reindex t t (doubledHamiltonian H)
      let F := reindex t t (EncodedFrame.sheetSwapOp q R)
      let ψ : N → ℂ := fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ (W : Matrix ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q))
          ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q)) ℂ) (z : ℝ),
        ‖W‖ ≤ 1 ∧ Real.exp (-2 * b) ≤ z ∧
        ∀ L : ℝ, 1 ≤ L →
          let B := 1 + b + Real.log L
          let V := reindex (g.symm.trans t) (g.symm.trans t)
            ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W)
          let M := GaussianFilter.gaussianIntertwinerTruncated
            (Real.toNNReal (resetVariance Δ r * B)) (resetCutoff Δ r * B) (F * K * Fᴴ) K V
          0 ≤ resetCutoff Δ r * B ∧
          ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            3 * Real.exp (-10 * b) * L ^ (-r) ∧
          ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
            3 * Real.exp (-10 * b) * L ^ (-r) := by
  have hfilter := uniform_physicalBuffer_filter_of_parameters.{0, 0, u} hΔ hr
    (resetVariance_pos hΔ hr) (resetCutoff_pos hΔ hr).le
    (resetVariance_mul_sq_div_two hΔ.ne').ge
    (resetCutoff_sq_div hΔ.ne' (by linarith)).ge
  intro ι _ _ N _ _ q R C hRC t H E₀ Ω b hgs hb hI P s g K F ψ
  obtain ⟨hΩ, heigen, hgap⟩ := Matrix.isGappedGroundState_iff.mp hgs
  let Ωs := FiniteProduct.splitTwoRegionsState (fun _ : ι ↦ Fin q) Ω R C hRC
  have hΩsv : Ωs = WithLp.ofLp Ω ∘ s.symm := rfl
  have hunit : star Ωs ⬝ᵥ Ωs = 1 := FiniteProduct.splitTwoRegionsState_unit _ Ω hΩ R C hRC
  have heigs : reindex s s H *ᵥ Ωs = (E₀ : ℂ) • Ωs := by
    rw [hΩsv, Matrix.reindex_mulVec, heigen]
    rfl
  have hgaps : (reindex s s H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec Ωs (star Ωs))).PosSemidef := by
    convert hgap.submatrix s.symm using 1
    ext x y
    simp [hΩsv, vecMulVec_apply, one_apply, s.symm.injective.eq_iff]
  have hbound := (quantumRelativeEntropy_splitTwoRegionsState_eq_mutualInformation q Ω R C
    hRC).trans_le hI
  obtain ⟨-, -, hψ1, hφ1, -⟩ := physicalBuffer_ground_pair hunit heigs hgaps hΔ.le
  have hK : reindex (g.symm.trans t) (g.symm.trans t)
      (reindex (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q))
        (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q)) (doubledHamiltonian (reindex s s H))) = K :=
    reindex_regional_doubledHamiltonian q R C hRC t H
  have hS : reindex (g.symm.trans t) (g.symm.trans t)
      (partialSwap (Fin (Fintype.card (R → Fin q))) (Fin (Fintype.card (C → Fin q))) ⊗ₖ
        (1 : Matrix ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q))
          ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q)) ℂ)) = F :=
    reindex_regional_partialSwap q R C hRC t
  have hψ : doubledRegroup Ωs ∘ (g.symm.trans t).symm = ψ :=
    doubledRegroup_splitTwoRegionsState_comp q R C hRC t Ω
  have hφ : physicalLeftSwap (doubledRegroup Ωs) ∘ (g.symm.trans t).symm = F *ᵥ ψ := by
    rw [physicalLeftSwap_eq_mulVec, ← Matrix.reindex_mulVec, hS, hψ]
  have hnorm (v : _ → ℂ) : ‖WithLp.toLp 2 (v ∘ (g.symm.trans t).symm)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv _ v
  refine ⟨by rw [← hψ, hnorm]; exact hψ1, by rw [← hφ, hnorm]; exact hφ1, ?_⟩
  obtain ⟨W, z, -, hW, hz, -, hfil⟩ :=
    hfilter (Fin (Fintype.card (R → Fin q))) (Fin (Fintype.card (C → Fin q)))
      (↥(R ∪ C)ᶜ → Fin q) (reindex s s H) Ωs E₀ b hunit heigs hgaps hb hbound
  refine ⟨W, z, hW, hz, fun L hL ↦ ?_⟩
  obtain ⟨-, -, hT, -, hfwd, hrev⟩ := hfil L hL
  have hmul (X Y : Matrix ((P × P) × ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q)))
      ((P × P) × ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q))) ℂ) :
      reindex (g.symm.trans t) (g.symm.trans t) (X * Y) =
        reindex (g.symm.trans t) (g.symm.trans t) X *
          reindex (g.symm.trans t) (g.symm.trans t) Y := by
    simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℂ ℂ (g.symm.trans t)) X Y
  have hsc (y : _ → ℂ) : (z : ℂ) • (y ∘ (g.symm.trans t).symm) =
      ((z : ℂ) • y) ∘ (g.symm.trans t).symm := rfl
  refine ⟨hT, ?_, ?_⟩
  · rw [← hφ, ← hψ, ← WithLp.toLp_smul, hsc, ← hS, ← hK, conjTranspose_reindex, ← hmul, ← hmul,
      ← GaussianFilter.reindex_gaussianIntertwinerTruncated, norm_reindex_mulVec_sub,
      WithLp.toLp_smul]
    exact hfwd
  · rw [← hφ, ← hψ, ← WithLp.toLp_smul, hsc, ← hS, ← hK, conjTranspose_reindex, ← hmul, ← hmul,
      ← GaussianFilter.reindex_gaussianIntertwinerTruncated, conjTranspose_reindex,
      norm_reindex_mulVec_sub, WithLp.toLp_smul]
    exact hrev


/-- **The two-sided Gaussian filter in arbitrary coordinates of the two replicas.** For a gap
`Δ > 0` and an exponent `r ≥ 0` there are constants `A, T₀` with the following property. Let
`Ω` be a gapped ground state of `H`, and let `R, C` be disjoint regions with `I_Ω(R : C) ≤ b`.
On two replicas put `Ψ = Ω ⊗ Ω` and `Φ = F_R Ψ`. Then a contraction `W` on the two copies of
the buffer `(R ∪ C)ᶜ` and a real `z ≥ exp (-2 b)` are chosen once, and for every `L ≥ 1` the
Gaussian integral `M` of variance `A B` truncated at `T₀ B`, with `B = 1 + b + log L`, has both
residuals `‖M Ψ - z Φ‖` and `‖Mᴴ Φ - z Ψ‖` at most `3 exp (-10 b) L^(-r)`. No restricted gap
and no bound on any purifying dimension is assumed.
Source: `02-information.tex`, lines 355–452, equations `eq:info-split-overlap`,
`eq:info-reset-overlap` and `eq:info-gaussian-two-sided`. -/
theorem exists_regional_physicalBuffer_filter {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {N : Type v} [Fintype N] [DecidableEq N]
        (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C) (t : (ι → Fin q) × (ι → Fin q) ≃ N)
        (H : Matrix (ι → Fin q) (ι → Fin q) ℂ) (E₀ : ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q))
        (b : ℝ), Matrix.IsGappedGroundState H E₀ Ω Δ → 0 ≤ b →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
        let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
        let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
        let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (↥(R ∪ C)ᶜ → Fin q))
        let K := reindex t t (doubledHamiltonian H)
        let F := reindex t t (EncodedFrame.sheetSwapOp q R)
        let ψ : N → ℂ := fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ (W : Matrix ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q))
            ((↥(R ∪ C)ᶜ → Fin q) × (↥(R ∪ C)ᶜ → Fin q)) ℂ) (z : ℝ),
          ‖W‖ ≤ 1 ∧ Real.exp (-2 * b) ≤ z ∧
          ∀ L : ℝ, 1 ≤ L →
            let B := 1 + b + Real.log L
            let V := reindex (g.symm.trans t) (g.symm.trans t)
              ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W)
            let M := GaussianFilter.gaussianIntertwinerTruncated (Real.toNNReal (A * B))
              (T₀ * B) (F * K * Fᴴ) K V
            0 ≤ T₀ * B ∧
            ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
              3 * Real.exp (-10 * b) * L ^ (-r) ∧
            ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
              3 * Real.exp (-10 * b) * L ^ (-r) :=
  ⟨resetVariance Δ r, resetCutoff Δ r, resetVariance_pos hΔ hr, resetCutoff_pos hΔ hr,
    regional_physicalBuffer_filter hΔ hr⟩


section PolarStep

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- **The polar step of the information reset.** Let `M` act on `S`, and let a real
`z ≥ exp (-2 b)` satisfy `‖M ψ - z φ‖, ‖Mᴴ φ - z ψ‖ ≤ C exp (-10 b) ε`. Then a unitary `U`
acting on `S` satisfies `‖U ψ - φ‖ ≤ 2 C ε`. It is the polar factor of `D = M / z`, whose
residuals are at most `C exp (-8 b) ε` because `z⁻¹ ≤ exp (2 b)`.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
theorem exists_supported_unitary_of_two_sided (S : Finset ι)
    {M : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hMsupp : M ∈ supportedOperators q (S : Set ι))
    {ψ φ : (ι → Fin q) → ℂ} {z b C ε : ℝ} (hb : 0 ≤ b) (hz : Real.exp (-2 * b) ≤ z)
    (hfwd : ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 φ‖ ≤ C * Real.exp (-10 * b) * ε)
    (hrev : ‖WithLp.toLp 2 (Mᴴ *ᵥ φ) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
      C * Real.exp (-10 * b) * ε)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    ∃ U : Matrix (ι → Fin q) (ι → Fin q) ℂ,
      U ∈ unitaryGroup (ι → Fin q) ℂ ∧ U ∈ supportedOperators q (S : Set ι) ∧
      ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 φ‖ ≤ 2 * C * ε := by
  have hz0 : 0 < z := (Real.exp_pos _).trans_le hz
  obtain ⟨U, hU, hUsupp, hcorr⟩ := exists_supported_unitary_polar_correction S
    (Submodule.smul_mem _ ((z : ℂ)⁻¹) hMsupp)
  refine ⟨U, hU, hUsupp, (hcorr ψ φ).trans ?_⟩
  have hzinv : (z : ℂ)⁻¹ = ((z⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hstar : star ((z : ℂ)⁻¹) = (z : ℂ)⁻¹ := by
    rw [hzinv, Complex.star_def, Complex.conj_ofReal]
  have hscale (x y : (ι → Fin q) → ℂ) :
      ‖WithLp.toLp 2 ((z : ℂ)⁻¹ • x) - WithLp.toLp 2 y‖ =
        z⁻¹ * ‖WithLp.toLp 2 x - (z : ℂ) • WithLp.toLp 2 y‖ := by
    rw [← Real.norm_of_nonneg (inv_nonneg.mpr hz0.le), ← Complex.norm_real, ← hzinv,
      ← norm_smul, smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hz0.ne'),
      one_smul, WithLp.toLp_smul]
  rw [conjTranspose_smul, hstar, smul_mulVec, smul_mulVec, hscale, hscale]
  have hzb : z⁻¹ ≤ Real.exp (2 * b) := by
    have h₁ := inv_anti₀ (Real.exp_pos (-2 * b)) hz
    rwa [← Real.exp_neg, show -(-2 * b) = 2 * b by ring] at h₁
  have hdecay : Real.exp (2 * b) * Real.exp (-10 * b) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hX : 0 ≤ C * Real.exp (-10 * b) * ε := by positivity
  calc z⁻¹ * ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 φ‖ +
        z⁻¹ * ‖WithLp.toLp 2 (Mᴴ *ᵥ φ) - (z : ℂ) • WithLp.toLp 2 ψ‖
      ≤ Real.exp (2 * b) * (C * Real.exp (-10 * b) * ε) +
        Real.exp (2 * b) * (C * Real.exp (-10 * b) * ε) := by
        gcongr
    _ = 2 * C * ε * (Real.exp (2 * b) * Real.exp (-10 * b)) := by ring
    _ ≤ 2 * C * ε * 1 := by gcongr
    _ = 2 * C * ε := mul_one _

end PolarStep

/-- **The localized two-sided filter of the information reset, with explicit constants.**
The statement of `SquareHamiltonian.exists_reset_localized_filter` holds with the radius
coefficient `K = resetRadius J Δ r` and the residual prefactor
`C = resetFilterPrefactor J Δ r`. They are built from the localization prefactor and
velocity of the doubled square Hamiltonian, the decay rate `1/2`, and the Gaussian cutoff
`T₀ = resetCutoff Δ r`.
Source: `02-information.tex`, lines 355–562, with `K_loc` at lines 551–554. -/
theorem SquareHamiltonian.reset_localized_filter (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
      h.IsGappedGroundState E₀ Ω Δ →
      ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
      let Q := (R ∪ C₀)ᶜ
      let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
      let Λ := AreaLaw.rectangularDomain L L
      let a := AreaLaw.rectangleSiteEquiv L L
      let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
      let F := reindex (p.trans e) (p.trans e) (EncodedFrame.sheetSwapOp q R)
      let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
        Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
      let boundary : Finset (Edge (squareLatticeGraph L L)) :=
        Finset.univ.filter (IsRegionBoundaryEdge R)
      let Z := boundary.biUnion fun x ↦
        ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
      let B := Lattice.graphNeighborhood Λ ⌈resetRadius J Δ r * (1 + b + Real.log L)⌉₊
        (Q.image a ∪ Z.image a)
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ (z : ℝ) (M : Matrix (Lattice.Configuration Λ (q * q))
          (Lattice.Configuration Λ (q * q)) ℂ),
        Real.exp (-2 * b) ≤ z ∧
        M ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧ ‖M‖ ≤ 1 ∧
        ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
          resetFilterPrefactor J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
        ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
          resetFilterPrefactor J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
  intro L hL h E₀ Ω hgs R C₀ hRC b hb hI Q p Λ a e F ψ boundary Z B
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hcoef : squareLocalizationVelocity J * resetCutoff Δ r + 15 + r ≤
      1 / 2 * resetRadius J Δ r := by
    rw [resetRadius]; apply le_of_eq; ring
  set Cg := squareLocalizationPrefactor with hCgdef
  set v := squareLocalizationVelocity J with hvdef
  set T₀ := resetCutoff Δ r with hT₀def
  set K := resetRadius J Δ r with hKdef
  have hCg : 0 < Cg := squareLocalizationPrefactor_pos
  have hT₀ : 0 < T₀ := resetCutoff_pos hΔ hr
  obtain ⟨hψn, hφn, W, z, hW, hz, hfil⟩ :=
    regional_physicalBuffer_filter.{0, 0} hΔ hr q R C₀ hRC (p.trans e) h.operator E₀ Ω b hgs
      hb hI
  obtain ⟨hT, hfwd, hrev⟩ := hfil L hL1
  obtain ⟨U, -, -, -, -, hM⟩ := SquareHamiltonian.supported_buffer_gaussian_integral q hq J hJ
    L h R C₀ hRC W ⌈K * (1 + b + Real.log L)⌉₊
  obtain ⟨hMsupp, hMnorm, hMerr⟩ := hM (Real.toNNReal (resetVariance Δ r * (1 + b + Real.log L)))
    (T₀ * (1 + b + Real.log L)) hT
  have hlocb := GaussianFilter.localization_error_bound_of_parameter_constant (L := (L : ℝ))
    (C := Cg * (1 + 8 * J)) hT₀.le (by norm_num : (0 : ℝ) ≤ 1 / 2) hr hcoef hb hL1
    (by positivity)
  have hT₀B : 0 ≤ 1 + b + Real.log L := by
    have := Real.log_nonneg hL1
    linarith
  have hδ : ‖W‖ * Cg * (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L))) *
      Real.exp (v * (T₀ * (1 + b + Real.log L)) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) ≤
      Cg * (1 + 8 * J) * (1 + T₀) * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
    refine le_trans ?_ hlocb
    have hTB : 0 ≤ T₀ * (1 + b + Real.log L) := mul_nonneg hT₀.le hT₀B
    have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    have hpoly : (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L))) ≤
        (1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L)) := by
      set T' := T₀ * (1 + b + Real.log L)
      have hL4 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 * (1 + T') := by
        have h₁ : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 := by
          rw [show (L : ℝ) ^ 4 = (L : ℝ) ^ 2 * (L : ℝ) ^ 2 by ring]
          exact le_mul_of_one_le_right (by positivity) hL2
        exact h₁.trans (le_mul_of_one_le_right (by positivity) (by linarith))
      have h8 : 8 * J * (L : ℝ) ^ 4 * T' ≤ 8 * J * (L : ℝ) ^ 4 * (1 + T') :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * T')
          = (L : ℝ) ^ 2 + 8 * J * (L : ℝ) ^ 4 * T' := by ring
        _ ≤ (L : ℝ) ^ 4 * (1 + T') + 8 * J * (L : ℝ) ^ 4 * (1 + T') := add_le_add hL4 h8
        _ = (1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T') := by ring
    rw [show v * (T₀ * (1 + b + Real.log L)) = v * T₀ * (1 + b + Real.log L) by ring]
    calc ‖W‖ * Cg * (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊)
        = ‖W‖ * Cg * ((L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L)))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by ring
      _ ≤ 1 * Cg * ((1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by
          gcongr
      _ = Cg * (1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L)) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by
          ring
  obtain ⟨h₁, h₂⟩ := norm_two_sided_le_of_norm_sub_le hψn hφn (hMerr.trans hδ) hfwd hrev
  refine ⟨hψn, hφn, z, _, hz, hMsupp, hMnorm.trans hW, h₁.trans_eq ?_, h₂.trans_eq ?_⟩ <;>
    rw [resetFilterPrefactor, ← hCgdef, ← hT₀def] <;> ring


/-- **The localized two-sided filter of the information reset.** For a gap `Δ > 0` and an
exponent `r ≥ 0` there are constants `C, K` with the following property. Let `Ω` be a gapped
ground state of an open square Hamiltonian, `R, C₀` disjoint regions with
`I_Ω(R : C₀) ≤ b`, and `B = 1 + b + log L`. On the paired sites put `Ψ = Ω ⊗ Ω` and
`Φ = F_R Ψ`. Then there are a real `z ≥ exp (-2 b)` and a contraction `M` acting on the
graph neighborhood of radius `⌈K B⌉` of the buffer and of the endpoints of the edges crossing
`R`, with `‖M Ψ - z Φ‖` and `‖Mᴴ Φ - z Ψ‖` at most `C exp (-10 b) L^(-r)`.
Source: `02-information.tex`, lines 355–562, equations `eq:info-reset-overlap` and
`eq:info-local-two-sided`. -/
theorem SquareHamiltonian.exists_reset_localized_filter (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
        let Q := (R ∪ C₀)ᶜ
        let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
        let Λ := AreaLaw.rectangularDomain L L
        let a := AreaLaw.rectangleSiteEquiv L L
        let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
        let F := reindex (p.trans e) (p.trans e) (EncodedFrame.sheetSwapOp q R)
        let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := Lattice.graphNeighborhood Λ ⌈K * (1 + b + Real.log L)⌉₊
          (Q.image a ∪ Z.image a)
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ (z : ℝ) (M : Matrix (Lattice.Configuration Λ (q * q))
            (Lattice.Configuration Λ (q * q)) ℂ),
          Real.exp (-2 * b) ≤ z ∧
          M ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧ ‖M‖ ≤ 1 ∧
          ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
          ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) :=
  ⟨resetFilterPrefactor J Δ r, resetRadius J Δ r, resetFilterPrefactor_pos hJ hΔ hr,
    resetRadius_pos hJ hΔ hr, SquareHamiltonian.reset_localized_filter q hq J hJ hΔ hr⟩

/-- **The unitary of the information reset, with explicit constants.** The statement of
`SquareHamiltonian.exists_reset_unitary` holds with the radius coefficient
`K = resetRadius J Δ r` and the error prefactor `C = resetUnitaryPrefactor J Δ r`, twice the
residual prefactor of the localized filter.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
theorem SquareHamiltonian.reset_unitary (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
      h.IsGappedGroundState E₀ Ω Δ →
      ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
      let Q := (R ∪ C₀)ᶜ
      let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
      let Λ := AreaLaw.rectangularDomain L L
      let a := AreaLaw.rectangleSiteEquiv L L
      let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
      let F := reindex (p.trans e) (p.trans e) (EncodedFrame.sheetSwapOp q R)
      let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
        Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
      let boundary : Finset (Edge (squareLatticeGraph L L)) :=
        Finset.univ.filter (IsRegionBoundaryEdge R)
      let Z := boundary.biUnion fun x ↦
        ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
      let B := Lattice.graphNeighborhood Λ ⌈resetRadius J Δ r * (1 + b + Real.log L)⌉₊
        (Q.image a ∪ Z.image a)
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ U : Matrix (Lattice.Configuration Λ (q * q)) (Lattice.Configuration Λ (q * q)) ℂ,
        U ∈ unitaryGroup (Lattice.Configuration Λ (q * q)) ℂ ∧
        U ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧
        ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            resetUnitaryPrefactor J Δ r * (L : ℝ) ^ (-r) := by
  intro L hL h E₀ Ω hgs R C₀ hRC b hb hI Q p Λ a e F ψ boundary Z B
  obtain ⟨hψn, hφn, z, M, hz, hMsupp, -, hfwd, hrev⟩ :=
    SquareHamiltonian.reset_localized_filter q hq J hJ hΔ hr L hL h E₀ Ω hgs R C₀ hRC b hb hI
  obtain ⟨U, hU, hUsupp, hUerr⟩ := exists_supported_unitary_of_two_sided B hMsupp hb hz hfwd hrev
    (resetFilterPrefactor_pos hJ hΔ hr).le (by positivity)
  exact ⟨hψn, hφn, U, hU, hUsupp, hUerr⟩

/-- **The unitary of the information reset.** For a gap `Δ > 0` and an exponent `r ≥ 0` there
are constants `C, K` with the following property. Let `Ω` be a gapped ground state of an open
square Hamiltonian, `R, C₀` disjoint regions with `I_Ω(R : C₀) ≤ b`, and
`B = 1 + b + log L`. On the paired sites put `Ψ = Ω ⊗ Ω` and `Φ = F_R Ψ`. Then a unitary
acting on the graph neighborhood of radius `⌈K B⌉` of the buffer and of the endpoints of the
edges crossing `R` satisfies `‖U Ψ - Φ‖ ≤ C L^(-r)`. It is the polar factor of
`M / z` on the same support; the norm `‖M / z‖ ≤ exp (2 b)` is paid by the factor
`exp (-10 b)` of the two-sided errors, and no unitary dilation is used.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
theorem SquareHamiltonian.exists_reset_unitary (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
        let Q := (R ∪ C₀)ᶜ
        let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
        let Λ := AreaLaw.rectangularDomain L L
        let a := AreaLaw.rectangleSiteEquiv L L
        let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
        let F := reindex (p.trans e) (p.trans e) (EncodedFrame.sheetSwapOp q R)
        let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := Lattice.graphNeighborhood Λ ⌈K * (1 + b + Real.log L)⌉₊
          (Q.image a ∪ Z.image a)
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ U : Matrix (Lattice.Configuration Λ (q * q)) (Lattice.Configuration Λ (q * q)) ℂ,
          U ∈ unitaryGroup (Lattice.Configuration Λ (q * q)) ℂ ∧
          U ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧
          ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ C * (L : ℝ) ^ (-r) :=
  ⟨resetUnitaryPrefactor J Δ r, resetRadius J Δ r, resetUnitaryPrefactor_pos hJ hΔ hr,
    resetRadius_pos hJ hΔ hr, SquareHamiltonian.reset_unitary q hq J hJ hΔ hr⟩

end TNLean.PEPS.Approximation
