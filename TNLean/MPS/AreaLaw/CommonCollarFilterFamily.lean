/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CommonCollarMPOFamily
import QICLean.Analysis.InvariantTensorWordPower

/-!
# The same global improving operator after adding interval collars

One enlarged family precedes every later filter and target. A filter
supplied in the original canonical split is represented by its actual
whole-chain matrix, then expressed through that same enlarged family.
Only the global operator bounds are transported unitarily; viability
for the new interval follows from the derived tensor decomposition.
Supporting ALVV, arXiv:1602.08828v2, Lemma l:er and Proposition 5.7,
lines 597–622 and 1332–1333. No new spectral filter is selected.
-/

open Matrix
open scoped BigOperators Kronecker TensorProduct

noncomputable section
namespace TNLean.MPS.AreaLaw

/-- The same actual global filter has a common collar family and all
ordered-word improvement bounds on the larger interval. The original
filter decomposition and its operator bounds are genuine intermediate
inputs; the enlarged decomposition and its viable-family estimates
are derived. Supporting ALVV, arXiv:1602.08828v2, Lemma l:er and
Proposition 5.7, lines 597–622 and 1332–1333. -/
theorem exists_common_collar_filter_family
    {L q c d p r n0 B : ℕ} (hq : 0 < q)
    (hpc : p ≤ c) (hcd : c ≤ d) (hdr : d ≤ r) (hrL : r ≤ L)
    (W0 : Fin n0 → Matrix (interval L c d → Fin q) (interval L c d → Fin q) ℂ)
    (hW0 : ∀ j, let e0 := intervalShiftOrderIso hcd (hdr.trans hrL)
      IsOpenMPS (d - c) (q * q) B (fun x ↦ W0 j
        (fun z ↦ (finProdFinEquiv.symm (x (e0.symm z))).1)
        (fun z ↦ (finProdFinEquiv.symm (x (e0.symm z))).2))) :
    let E := interval L c d
    let J := interval L p r
    let ep := intervalShiftOrderIso (hpc.trans (hcd.trans hdr)) hrL
    let HM := EuclideanSpace ℂ (J → Fin q)
    let HE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
    let tau := (FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (↥(Jᶜ) → Fin q) ℂ).tensorProduct
      (EuclideanSpace.basisFun (J → Fin q) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ HE HM)
    ∃ (n : ℕ) (W : Fin n → Matrix (J → Fin q) (J → Fin q) ℂ),
      n = n0 * q ^ (2 * (J \ E).card) ∧
      (∀ j, IsOpenMPS (r - p) (q * q) (max 1 B) (fun x ↦ W j
        (fun z ↦ (finProdFinEquiv.symm (x (ep.symm z))).1)
        (fun z ↦ (finProdFinEquiv.symm (x (ep.symm z))).2))) ∧
      ∀ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ)
        (Kwhole : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
          EuclideanSpace ℂ (Fin L → Fin q)),
        let Z := (Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)).symm Kwhole
        0 ≤ Delta →
        (∃ M0 : Fin n0 → Matrix (↥(Eᶜ) → Fin q) (↥(Eᶜ) → Fin q) ℂ,
          Z = (∑ i, M0 i ⊗ₖ W0 i).submatrix
            ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) E).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) E).trans (Equiv.prodComm _ _))) →
        (∀ t ∈ T, Kwhole t ∈ T) → (∀ z ∈ Tᗮ, Kwhole z ∈ Tᗮ) →
        (∀ t ∈ T, ‖t‖ ≤ ‖Kwhole t‖) →
        (∀ z ∈ Tᗮ, ‖Kwhole z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) →
        let K := Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv Kwhole
        let Tc := T.map Tm.toLinearEquiv.toLinearMap
        ∃ M : Fin n → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
          Z = (∑ i, M i ⊗ₖ W i).submatrix tau tau ∧
          K = ∑ i, TensorProduct.mapL
            (Matrix.toEuclideanCLM (n := J → Fin q) (𝕜 := ℂ) (W i))
            (Matrix.toEuclideanCLM (n := ↥(Jᶜ) → Fin q) (𝕜 := ℂ) (M i)) ∧
          (∀ t ∈ Tc, K t ∈ Tc) ∧ (∀ z ∈ Tcᗮ, K z ∈ Tcᗮ) ∧
          (∀ t ∈ Tc, ‖t‖ ≤ ‖K t‖) ∧
          (∀ z ∈ Tcᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) ∧
          ∀ (a : ℕ) (S : Submodule ℂ HM) (delta : ℝ),
            Submodule.IsViable delta S Tc → delta < 1 →
            let grow := ⨆ w : Fin a → Fin n,
              S.map ((List.ofFn (fun j ↦ Matrix.toEuclideanCLM (n := J → Fin q) (𝕜 := ℂ)
                (W (w j)))).prod : HM →ₗ[ℂ] HM)
            Module.finrank ℂ grow ≤ n ^ a * Module.finrank ℂ S ∧
              Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2) grow Tc := by
  classical
  intro E J ep HM HE tau U Phi Tm
  have hbase := exists_common_collar_mpo_tensor_family
    (L := L) (q := q) (c := c) (d := d) (p := p) (r := r) (n := n0) (B := B)
    hq hpc hcd hdr hrL W0 hW0
  obtain ⟨n, W, hn, hW, hTransfer⟩ := hbase
  refine ⟨n, W, hn, hW, ?_⟩
  intro T Delta Kwhole Z hDelta hdecomp hKT hKTo hlow hhigh K Tc
  obtain ⟨M, hmatrix, hconj⟩ := hTransfer Z hdecomp
  have hwhole : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) Z = Kwhole :=
    (Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)).apply_symm_apply Kwhole
  have hdec : K = ∑ i, TensorProduct.mapL
      (Matrix.toEuclideanCLM (n := J → Fin q) (𝕜 := ℂ) (W i))
      (Matrix.toEuclideanCLM (n := ↥(Jᶜ) → Fin q) (𝕜 := ℂ) (M i)) := by
    exact (congrArg (fun A : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
        EuclideanSpace ℂ (Fin L → Fin q) ↦
      Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap) hwhole).symm.trans hconj
  obtain ⟨hKT', hKTo', hlow', hhigh'⟩ :=
    ContinuousLinearMap.invariant_subspace_bounds_conj
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin L → Fin q)) (F := HM ⊗[ℂ] HE)
      Tm Kwhole T Delta hKT hKTo hlow hhigh
  refine ⟨M, hmatrix, hdec, hKT', hKTo', hlow', hhigh', ?_⟩
  intro a S delta hS hdelta grow
  simpa only [Fintype.card_fin] using
    Submodule.IsViable.word_power_of_tensor_decomposition K
      (fun i ↦ Matrix.toEuclideanCLM (n := J → Fin q) (𝕜 := ℂ) (W i))
      (fun i ↦ Matrix.toEuclideanCLM (n := ↥(Jᶜ) → Fin q) (𝕜 := ℂ) (M i))
      hdec hDelta hKT' hKTo' hlow' hhigh' a S delta hS hdelta

end TNLean.MPS.AreaLaw
