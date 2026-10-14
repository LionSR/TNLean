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

The constants `C, K` depend only on `q, J, Δ` and the exponent `r`. No gap of a restricted
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
theorem reindex_prodCongr_doubledHamiltonian {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (H : Matrix m m ℂ) :
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

universe u v

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
              3 * Real.exp (-10 * b) * L ^ (-r) := by
  obtain ⟨A, T₀, hA, hT₀, hfilter⟩ := GaussianFilter.exists_uniform_physicalBuffer_filter hΔ hr
  refine ⟨A, T₀, hA, hT₀, ?_⟩
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


section PolarStep

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- **The polar step of the information reset.** Let `M` act on `S`, and let a real
`z ≥ exp (-2 b)` satisfy `‖M ψ - z φ‖, ‖Mᴴ φ - z ψ‖ ≤ C exp (-10 b) ε`. Then a unitary `U`
acting on `S` satisfies `‖U ψ - φ‖ ≤ 2 C ε`. It is the polar factor of `D = M / z`; the norm
`‖D‖ ≤ exp (2 b)` is paid by the factor `exp (-10 b)`.
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
        let ψ : AreaLaw.Configuration Λ (q * q) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := AreaLaw.graphNeighborhood Λ ⌈K * (1 + b + Real.log L)⌉₊
          (Q.image a ∪ Z.image a)
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ (z : ℝ) (M : Matrix (AreaLaw.Configuration Λ (q * q))
            (AreaLaw.Configuration Λ (q * q)) ℂ),
          Real.exp (-2 * b) ≤ z ∧
          M ∈ supportedOperators (q * q) (B : Set (AreaLaw.Site Λ)) ∧ ‖M‖ ≤ 1 ∧
          ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
          ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
  obtain ⟨Cg, v, c, hCg, hv, hc, hgauss⟩ :=
    SquareHamiltonian.exists_supported_buffer_gaussian_integral q hq J hJ
  obtain ⟨A, T₀, hA, hT₀, hreg⟩ :=
    exists_regional_physicalBuffer_filter.{0, 0} hΔ hr
  refine ⟨Cg * (1 + 8 * J) * (1 + T₀) + 3, ?_⟩
  obtain ⟨K, hK, -, hloc⟩ := GaussianFilter.exists_localization_parameters hT₀ hv.le hc hr
  refine ⟨K, by positivity, hK, ?_⟩
  intro L hL h E₀ Ω hgs R C₀ hRC b hb hI Q p Λ a e F ψ boundary Z B
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hψn, hφn, W, z, hW, hz, hfil⟩ :=
    hreg q R C₀ hRC (p.trans e) h.operator E₀ Ω b hgs hb hI
  obtain ⟨hT, hfwd, hrev⟩ := hfil L hL1
  obtain ⟨U, -, -, -, -, hM⟩ := hgauss L h R C₀ hRC W ⌈K * (1 + b + Real.log L)⌉₊
  obtain ⟨hMsupp, hMnorm, hMerr⟩ := hM (Real.toNNReal (A * (1 + b + Real.log L)))
    (T₀ * (1 + b + Real.log L)) hT
  obtain ⟨-, -, -, hlocb⟩ := hloc b L (Cg * (1 + 8 * J)) hb hL1 (by positivity)
  have hT₀B : 0 ≤ 1 + b + Real.log L := by
    have := Real.log_nonneg hL1
    linarith
  have hδ : ‖W‖ * Cg * (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L))) *
      Real.exp (v * (T₀ * (1 + b + Real.log L)) - c * ⌈K * (1 + b + Real.log L)⌉₊) ≤
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
          Real.exp (v * T₀ * (1 + b + Real.log L) - c * ⌈K * (1 + b + Real.log L)⌉₊)
        = ‖W‖ * Cg * ((L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L)))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - c * ⌈K * (1 + b + Real.log L)⌉₊) := by ring
      _ ≤ 1 * Cg * ((1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - c * ⌈K * (1 + b + Real.log L)⌉₊) := by
          gcongr
      _ = Cg * (1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L)) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - c * ⌈K * (1 + b + Real.log L)⌉₊) := by
          ring
  obtain ⟨h₁, h₂⟩ := norm_two_sided_le_of_norm_sub_le hψn hφn (hMerr.trans hδ) hfwd hrev
  refine ⟨hψn, hφn, z, _, hz, hMsupp, hMnorm.trans hW, h₁.trans_eq (by ring), h₂.trans_eq (by ring)⟩

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
        let ψ : AreaLaw.Configuration Λ (q * q) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := AreaLaw.graphNeighborhood Λ ⌈K * (1 + b + Real.log L)⌉₊
          (Q.image a ∪ Z.image a)
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ U : Matrix (AreaLaw.Configuration Λ (q * q)) (AreaLaw.Configuration Λ (q * q)) ℂ,
          U ∈ unitaryGroup (AreaLaw.Configuration Λ (q * q)) ℂ ∧
          U ∈ supportedOperators (q * q) (B : Set (AreaLaw.Site Λ)) ∧
          ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ C * (L : ℝ) ^ (-r) := by
  obtain ⟨C, K, hC, hK, hfilter⟩ :=
    SquareHamiltonian.exists_reset_localized_filter q hq J hJ hΔ hr
  refine ⟨2 * C, K, by positivity, hK, ?_⟩
  intro L hL h E₀ Ω hgs R C₀ hRC b hb hI Q p Λ a e F ψ boundary Z B
  obtain ⟨hψn, hφn, z, M, hz, hMsupp, -, hfwd, hrev⟩ :=
    hfilter L hL h E₀ Ω hgs R C₀ hRC b hb hI
  obtain ⟨U, hU, hUsupp, hUerr⟩ := exists_supported_unitary_of_two_sided B hMsupp hb hz hfwd hrev
    hC.le (by positivity)
  exact ⟨hψn, hφn, U, hU, hUsupp, hUerr⟩

end TNLean.PEPS.Approximation
