/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionalReset
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# The physical-buffer filter on two sheets

QICLean's two-sided Gaussian filter of the information reset,
`GaussianFilter.regional_physicalBuffer_filter`, lives on the sites `ι ⊕ ι` of two replicas.
The square-lattice reset reads it on the two sheets `(ι → Fin q) × (ι → Fin q)`, relabelled by
an arbitrary bijection `t` of the configurations, with the buffer operator written as
`1 ⊗ W` in the coordinates that split each sheet into the two regions and the buffer. This file
carries the filter to these coordinates: the doubled Hamiltonian, the exchange of the sheets on
`R` and the doubled ground vector are the transports of their replica forms along the splitting
`ι ⊕ ι → Fin q ≃ (ι → Fin q) × (ι → Fin q)` followed by `t`, and the placement of the buffer
operator on the two replicas of the buffer is `1 ⊗ W` for an operator `W` of the same norm.

## Main results

* `TNLean.PEPS.Approximation.regional_physicalBuffer_filter_twoSheet`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, `02-information.tex`, lines 355–452, equations `eq:info-split-overlap`,
  `eq:info-reset-overlap` and `eq:info-gaussian-two-sided`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace)

open GaussianFilter (resetCutoff resetVariance)

universe u v

namespace TNLean.PEPS.Approximation

/-- **The two-sided Gaussian filter of the information reset on two sheets.** Let `H` be
Hermitian and gapped at `E₀` with gap `Δ > 0`, with ground space the line through the unit
vector `Ω`, let `r ≥ 0`, and let `R, C` be disjoint regions with `I_Ω(R : C) ≤ b`. Read the two
sheets through a bijection `t`, and let `ψ`, `F` and `K` be the doubled vector `Ω ⊗ Ω`, the
exchange of the two sheets on `R` and the doubled Hamiltonian in these coordinates. Then an
operator `W` of norm at most one on the two copies of the buffer `(R ∪ C)ᶜ` and a real
`z ≥ exp (-2 b)` are chosen once, and for every `L ≥ 1`, with `B = 1 + b + log L`, the Gaussian
integral of variance `resetVariance Δ r * B` truncated at `resetCutoff Δ r * B`, between the
generators `F K F*` and `K` applied to `1 ⊗ W`, has both residuals at most
`3 exp (-10 b) L^(-r)`. Polynomial PEPS approximation, `02-information.tex`, lines 355–452. -/
theorem regional_physicalBuffer_filter_twoSheet {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {N : Type v} [Fintype N] [DecidableEq N]
      (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C) (t : (ι → Fin q) × (ι → Fin q) ≃ N)
      (H : Matrix (ι → Fin q) (ι → Fin q) ℂ) (E₀ : ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q))
      (b : ℝ), H.IsHermitian → ‖Ω‖ = 1 → IsGapped H E₀ Δ →
      groundSpace H E₀ = Submodule.span ℂ {Ω} → 0 ≤ b →
      ManyBody.regionMutualInformation Ω R C ≤ b →
      let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
      let s := ManyBody.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
      let g := (s.prodCongr s).trans (Equiv.doubledRegroup P ({v // v ∉ R ∪ C} → Fin q))
      let pr := Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q
      let K := reindex t t (doubledHamiltonian H)
      let F := reindex t t (reindex pr pr (ManyBody.pairSwapOp R))
      let ψ : N → ℂ := fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ (W : Matrix (({v // v ∉ R ∪ C} → Fin q) × ({v // v ∉ R ∪ C} → Fin q))
          (({v // v ∉ R ∪ C} → Fin q) × ({v // v ∉ R ∪ C} → Fin q)) ℂ) (z : ℝ),
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
  intro ι _ _ N _ _ q R C hRC t H E₀ Ω b hH hΩ hgap hspan hb hI P s g pr K F ψ
  let Q := (R ∪ C)ᶜ
  -- the two replicas `ι ⊕ ι`, read on the two sheets and then through `t`
  let φ := (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).trans t
  let KV := reindex (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).symm
    (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).symm (doubledHamiltonian H)
  let FV := ManyBody.replicaSwapOp (Fin q) R
  let Ψ := ManyBody.sumSitesProduct (X := fun _ : ι ⊕ ι ↦ Fin q) Ω Ω
  have hK : reindex φ φ KV = K := by
    ext x y
    rfl
  have hF : reindex φ φ FV = F := by
    ext x y
    rfl
  have hψ : ψ = WithLp.ofLp Ψ ∘ φ.symm := rfl
  have hconj (A B : Matrix (ManyBody.Config fun _ : ι ⊕ ι ↦ Fin q)
      (ManyBody.Config fun _ : ι ⊕ ι ↦ Fin q) ℂ) :
      reindex φ φ (A * B * Aᴴ) = reindex φ φ A * reindex φ φ B * (reindex φ φ A)ᴴ := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  -- transporting a vector equation along `φ` keeps its norm
  have hvec (A : Matrix (ManyBody.Config fun _ : ι ⊕ ι ↦ Fin q)
      (ManyBody.Config fun _ : ι ⊕ ι ↦ Fin q) ℂ)
      (u : EuclideanSpace ℂ (ManyBody.Config fun _ : ι ⊕ ι ↦ Fin q)) :
      reindex φ φ A *ᵥ (WithLp.ofLp u ∘ φ.symm) =
        WithLp.ofLp (toEuclideanLin A u) ∘ φ.symm := by
    rw [reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id]
    rfl
  have hnorm (u : EuclideanSpace ℂ (ManyBody.Config fun _ : ι ⊕ ι ↦ Fin q)) :
      ‖(WithLp.toLp 2 (WithLp.ofLp u ∘ φ.symm) : EuclideanSpace ℂ N)‖ = ‖u‖ :=
    EuclideanSpace.norm_toLp_comp_equiv φ.symm (WithLp.ofLp u)
  have hnorm' (f : ManyBody.Config (fun _ : ι ⊕ ι ↦ Fin q) → ℂ) :
      ‖(WithLp.toLp 2 (f ∘ φ.symm) : EuclideanSpace ℂ N)‖ =
        ‖(WithLp.toLp 2 f : EuclideanSpace ℂ _)‖ :=
    EuclideanSpace.norm_toLp_comp_equiv φ.symm f
  have hΨ : ‖Ψ‖ = 1 := by
    rw [ManyBody.norm_sumSitesProduct, hΩ, mul_one]
  have hFΨ : ‖toEuclideanLin FV Ψ‖ = 1 := by
    have h := ManyBody.sitePermOp_mulVec_eq_relabelVector (α := Fin q) (ManyBody.replicaSwap R) Ψ
    rw [ManyBody.sitePermOp_replicaSwap] at h
    change ‖WithLp.toLp 2 (FV *ᵥ WithLp.ofLp Ψ)‖ = 1
    rw [h, ManyBody.norm_relabelVector, hΨ]
  obtain ⟨W', z, -, hW', hz, hfilter⟩ :=
    GaussianFilter.regional_physicalBuffer_filter hΔ hr hH hΩ hgap hspan hRC hI
  -- the placement of `W'` on the two replicas of the buffer, in paired coordinates, is a
  -- placement on the buffer; written in the splitting coordinates it is `1 ⊗ W`
  let p := pr.symm.trans (Equiv.arrowCongr (Equiv.refl ι) finProdFinEquiv)
  let φp := (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).trans p
  have hVp : reindex φp φp (ManyBody.place (Q.disjSum Q) W') ∈
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl ι)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      ((ManyBody.reindex_replicaPairEquiv_mem_supportedOperators_iff (S := Q)).mpr
        (ManyBody.place_mem_supportedOperators W'))
    convert hs using 1
    ext x y
    rfl
  obtain ⟨K₀, hK₀⟩ := ManyBody.exists_eq_place_of_mem_supportedOperators hVp
  let pQ := ((Equiv.arrowProdEquivProdArrow {v // v ∉ R ∪ C} (fun _ ↦ Fin q)
      (fun _ ↦ Fin q)).symm.trans
      (Equiv.arrowCongr (Equiv.refl {v // v ∉ R ∪ C}) finProdFinEquiv)).trans
    (ManyBody.complementEquiv (fun _ : ι ↦ Fin (q * q)) (R ∪ C))
  let W := reindex pQ.symm pQ.symm K₀
  have hWK : reindex (g.symm.trans p) (g.symm.trans p) ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W) =
      reindex φp φp (ManyBody.place (Q.disjSum Q) W') := by
    rw [ManyBody.reindex_physicalBuffer_eq_place q R C hRC W, hK₀]
    congr 1
    exact (reindex pQ pQ).apply_symm_apply K₀
  -- the configurations are nonempty, since `Ω` is a unit vector
  have hc : Nonempty (ι → Fin q) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [EuclideanSpace.norm_eq, Finset.univ_eq_empty] at hΩ
  have hWn : ‖W‖ ≤ 1 := by
    change ‖reindex pQ.symm pQ.symm K₀‖ ≤ 1
    have hn : ‖ManyBody.place Q K₀‖ = ‖K₀‖ := by
      refine @ManyBody.norm_place _ _ _ (fun _ : ι ↦ Fin (q * q)) _ Q _ (fun v ↦ ?_) K₀
      exact ⟨finProdFinEquiv (hc.some v, hc.some v)⟩
    rw [l2_opNorm_reindex_equiv, ← hn, ← hK₀, l2_opNorm_reindex_equiv]
    exact (ManyBody.norm_place_le W').trans hW'
  have hV (L : ℝ) : reindex (g.symm.trans t) (g.symm.trans t)
      ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W) =
        reindex φ φ (ManyBody.place (Q.disjSum Q) W') := by
    have h := congrArg (reindex (p.symm.trans t) (p.symm.trans t)) hWK
    simp only [← Matrix.reindex_trans, Equiv.trans_apply] at h
    convert h using 2 <;> ext x <;> simp [φ, φp]
  refine ⟨by rw [hψ, hnorm, hΨ], ?_, W, z, hWn, hz, fun L hL ↦ ?_⟩
  · rw [← hF, hψ, hvec, hnorm, hFΨ]
  intro B V M
  obtain ⟨-, hfwd, hrev⟩ := hfilter L hL
  have hM : M = reindex φ φ (GaussianFilter.gaussianIntertwinerTruncated
      (Real.toNNReal (resetVariance Δ r * B)) (resetCutoff Δ r * B) (FV * KV * FVᴴ) KV
      (ManyBody.place (Q.disjSum Q) W')) := by
    rw [GaussianFilter.reindex_gaussianIntertwinerTruncated, hconj, hF, hK, ← hV L]
  refine ⟨mul_nonneg (GaussianFilter.resetCutoff_pos hΔ hr).le
    (by linarith [Real.log_nonneg hL]), ?_, ?_⟩
  · rw [hM, ← hF, hψ, hvec, hvec, ← WithLp.toLp_smul, ← WithLp.toLp_sub, ← Pi.smul_comp,
      ← Pi.sub_comp, hnorm', WithLp.toLp_sub, WithLp.toLp_smul, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
    exact hfwd
  · rw [hM, ← hF, hψ, conjTranspose_reindex, hvec, hvec, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
      ← Pi.smul_comp, ← Pi.sub_comp, hnorm', WithLp.toLp_sub, WithLp.toLp_smul, WithLp.toLp_ofLp,
      WithLp.toLp_ofLp]
    exact hrev

end TNLean.PEPS.Approximation
