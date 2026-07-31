/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SectorMatch.CyclicTrace
import TNLean.MPS.Periodic.Overlap.SectorMatch.CyclicTransport
import TNLean.Algebra.FiniteCycleCoboundary
import TNLean.Algebra.PiTensorProductPhase
import TNLean.MPS.Periodic.GlobalGauge
import TNLean.MPS.Periodic.SectorContraction

/-!
# Full-cycle sector-match contraction

This module contracts a cycle of matched normal sectors into a single
repeated-block gauge relation.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module

namespace MPSTensor

variable {d D : ℕ}

/-- Full-cycle contraction step for periodic-overlap Case 3.

At this point the sector transport has already been abstracted into
`hBlockMatch`, so this contraction step is no longer the per-step
eq:blockedABprop staircase identification (lines 985--1002). What is still
needed is the contraction argument around the whole cycle, arXiv:1708.00029,
Appendix A lines 1023--1117:

* For each sector `u`, Lemma bdcf normality gives a repetition length `N₀` after
  which the blocked product F_u (eq:Fu, lines 1026--1030) is injective, with a
  right inverse Ω_u (eq:Omegauprop, lines 1035--1040).
* Concatenating and applying the Ω_u inverses contracts the repeated products to
  per-site proportionality A_u^i = κ_v · e^{iη/m} · B_v^i (eq:resultprop/
  eq:thetaACprop, lines 1063--1076).
* The phase bookkeeping is load-bearing: ∏_v κ_v = 1 (eq:prodkappaprop, line
  1079) and |κ_v| = 1 from ‖Σ_i A_u^{i†} A_u^i‖ = 1 (lines 1082--1084), so
  κ_v = e^{iθ_v} with Σ_v θ_v = 0; choosing φ_v with θ_v = φ_v − φ_{v+1}
  (lines 1093--1102) telescopes the per-sector phases into a single global phase
  ξ = η/m and a single global unitary U = Σ_u e^{iφ_{u+q}} P_u U_{u+q} Q_{u+q}
  (eq:result and lines 1110--1117), giving A^i = e^{iξ} U B^i U†.

The cyclic offset `q` records the fixed displacement between matched sector orbits:
`hBlockMatch` pairs sector `u` of `A` with sector `u + q` of `B`. The hypothesis
`hNondeg` rules out zero-dimensional sectors, for which the sector match and its
contraction data would be vacuous. Finally, `hA_lc` and `hB_lc` normalize the original
tensors; comparing the resulting norm identities is what forces the gauge phases
produced by the contraction to have unit modulus.

The available chain inputs are `blockDecompositionMap` /
`IsNBlkInjective.exists_rightInverse` in `MPS/Chain/OneSidedInverse.lean`
(realizing Ω_u for a chosen injective word length) and the two-site
proportionality theorem `tensor_proportional` in `MPS/Chain/TensorEquality.lean`.
The finite-cycle phase choice in lines 1093--1102 is now isolated as
`TNLean.Algebra.exists_fin_complex_unit_cyclic_coboundary_of_prod_eq_one`; the
offset-indexed form needed for the sector match `(u, u + q)` is
`TNLean.Algebra.exists_fin_complex_unit_cyclic_coboundary_shift_of_prod_eq_one`.
The product-one scalar extraction in lines 1072--1080 is isolated as
`PiTensorProductPhase.exists_kappa_product_one_of_piTensorProduct_eq_root_smul`.
The `m`-factor cyclic contraction below produces the uniform product-tensor
identity and the unit-modulus
normalization of the resulting sector phases; after that, the algebraic scalar
extraction and the phase-coboundary lemma perform the κ/θ/φ telescoping. See
docs/paper-gaps/1708_periodic_overlap_route_alignment.tex. -/
lemma sectorTensor_proportional_of_blockedMatch
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    {PA PB : Fin m → MatrixAlg D}
    {φA : (k : Fin m) →
      Matrix (Fin (dimA k)) (Fin (dimA k)) ℂ ≃ₗ[ℂ] cornerSubmodule (PA k)}
    {φB : (k : Fin m) →
      Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ ≃ₗ[ℂ] cornerSubmodule (PB k)}
    (hA_cyclic : IsCyclicSectorDecompWith A blocksA PA φA)
    (hB_cyclic : IsCyclicSectorDecompWith B blocksB PB φB)
    (hA_letter : ∀ k (i : Fin (blockPhysDim d m)),
      (φA k (blocksA k i)).1 = PA k * (blockTensor A m) i * PA k)
    (hB_letter : ∀ k (i : Fin (blockPhysDim d m)),
      (φB k (blocksB k i)).1 = PB k * (blockTensor B m) i * PB k)
    (q : Fin m)
    (hBlockMatch : ∀ u : Fin m,
      ∃ (hdim : dimA u = dimB (u + q)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA u))
          (blocksB (u + q)))
    (hNondeg : ∀ u, dimA u ≠ 0)
    (hNormal : ∀ u, IsNormal (blocksA u)) :
    ∃ (ξ : ℂ) (Uglob : MatrixAlg D),
      ‖ξ‖ = 1 ∧
      Uglob * Uglobᴴ = 1 ∧
      Uglobᴴ * Uglob = 1 ∧
      ∀ i, A i = ξ • (Uglob * B i * Uglobᴴ) := by
  clear hA_mpv hB_mpv
  obtain ⟨L, hL_pos, Ω, hΩ⟩ :=
    exists_common_sectorDecompositionMaps_of_isNormal_leftCanonical
      blocksA hA_blocks_lc hNondeg hNormal
  rcases hA_cyclic with
    ⟨hPA_proj, hPA_sum, hPA_shift, hPA_comm, hPA_trace, hPA_intertwine,
      hφA_mul, hφA_star⟩
  rcases hB_cyclic with
    ⟨hPB_proj, hPB_sum, hPB_shift, hPB_comm, hPB_trace, hPB_intertwine,
      hφB_mul, hφB_star⟩
  have hCornerData : ∀ u : Fin m,
      ∃ (U : MatrixAlg D) (c : ℂ),
        U = PA u * U * PB (u + q) ∧
        Uᴴ * U = PB (u + q) ∧
        U * Uᴴ = PA u ∧
        ‖c‖ = 1 ∧
        ∀ i : Fin (blockPhysDim d m), (φA u (blocksA u i)).1 =
          c • (U * (φB (u + q) (blocksB (u + q) i)).1 * Uᴴ) := by
    intro u
    obtain ⟨hdim, hMatch⟩ := hBlockMatch u
    haveI : NeZero (dimA u) := ⟨hNondeg u⟩
    exact exists_ambient_corner_gauge_of_gaugePhase
      (blocksA u) (blocksB (u + q)) hdim (PA u) (PB (u + q))
      (φA u) (φB (u + q)) (hPA_proj u) (hPB_proj (u + q))
      (hφA_mul u) (hφB_mul (u + q)) (hφA_star u) (hφB_star (u + q))
      (hA_blocks_lc u) (hB_blocks_lc (u + q)) (hNormal u) hMatch
  let U : Fin m → MatrixAlg D := fun u => (hCornerData u).choose
  let c : Fin m → ℂ := fun u => (hCornerData u).choose_spec.choose
  have hU_corner : ∀ u, U u = PA u * U u * PB (u + q) :=
    fun u => (hCornerData u).choose_spec.choose_spec.1
  have hU_star_U : ∀ u, (U u)ᴴ * U u = PB (u + q) :=
    fun u => (hCornerData u).choose_spec.choose_spec.2.1
  have hU_U_star : ∀ u, U u * (U u)ᴴ = PA u :=
    fun u => (hCornerData u).choose_spec.choose_spec.2.2.1
  have hc_norm : ∀ u, ‖c u‖ = 1 :=
    fun u => (hCornerData u).choose_spec.choose_spec.2.2.2.1
  have hBlockAmbient : ∀ (u : Fin m) (i : Fin (blockPhysDim d m)),
      PA u * (blockTensor A m) i * PA u =
        c u • (U u * (PB (u + q) * (blockTensor B m) i * PB (u + q)) *
          (U u)ᴴ) := by
    intro u i
    rw [← hA_letter u i, ← hB_letter (u + q) i]
    exact (hCornerData u).choose_spec.choose_spec.2.2.2.2 i
  let P : Fin m → MatrixAlg D := fun u => PA (-u)
  let Q : Fin m → MatrixAlg D := fun v => PB (-v)
  let q' : Fin m := -q
  let U' : Fin m → MatrixAlg D := fun u => U (-u)
  let c' : Fin m → ℂ := fun u => c (-u)
  let dimA' : Fin m → ℕ := fun u => dimA (-u)
  let blocksA' : (u : Fin m) → MPSTensor (blockPhysDim d m) (dimA' u) :=
    fun u => blocksA (-u)
  let φA' : (u : Fin m) →
      MatrixAlg (dimA' u) ≃ₗ[ℂ] cornerSubmodule (P u) :=
    fun u => φA (-u)
  have hP_proj : ∀ u, IsOrthogonalProjection (P u) := fun u => hPA_proj (-u)
  have hQ_proj : ∀ v, IsOrthogonalProjection (Q v) := fun v => hPB_proj (-v)
  have hA_offDiag :
      ∀ (k : Fin m) (i : Fin d), PA (k + 1) * A i = A i * PA k :=
    offDiag_shift_of_adjoint_cyclic_shift A hA_lc hPA_proj hPA_shift
  have hB_offDiag :
      ∀ (k : Fin m) (i : Fin d), PB (k + 1) * B i = B i * PB k :=
    offDiag_shift_of_adjoint_cyclic_shift B hB_lc hPB_proj hPB_shift
  have hP_shift : ∀ (u : Fin m) (i : Fin d), P u * A i = A i * P (u + 1) := by
    intro u i
    have h := hA_offDiag (-(u + 1)) i
    have hindex : -(u + 1) + 1 = -u := by abel
    rw [hindex] at h
    exact h
  have hQ_shift : ∀ (v : Fin m) (i : Fin d), Q v * B i = B i * Q (v + 1) := by
    intro v i
    have h := hB_offDiag (-(v + 1)) i
    have hindex : -(v + 1) + 1 = -v := by abel
    rw [hindex] at h
    exact h
  have hU'_corner : ∀ u, U' u = P u * U' u * Q (u + q') := by
    intro u
    have h := hU_corner (-u)
    have hindex : -(u + q') = -u + q := by simp only [q']; abel
    change U (-u) = PA (-u) * U (-u) * PB (-(u + q'))
    rw [hindex]
    exact h
  have hU'_star_U : ∀ u, (U' u)ᴴ * U' u = Q (u + q') := by
    intro u
    have h := hU_star_U (-u)
    have hindex : -(u + q') = -u + q := by simp only [q']; abel
    change (U (-u))ᴴ * U (-u) = PB (-(u + q'))
    rw [hindex]
    exact h
  have hU'_U_star : ∀ u, U' u * (U' u)ᴴ = P u := by
    intro u
    exact hU_U_star (-u)
  have hc'_norm : ∀ u, ‖c' u‖ = 1 := fun u => hc_norm (-u)
  have hBlockAmbient' : ∀ (u : Fin m) (i : Fin (blockPhysDim d m)),
      P u * (blockTensor A m) i * P u =
        c' u • (U' u * (Q (u + q') * (blockTensor B m) i * Q (u + q')) *
          (U' u)ᴴ) := by
    intro u i
    have h := hBlockAmbient (-u) i
    have hindex : -(u + q') = -u + q := by simp only [q']; abel
    change PA (-u) * (blockTensor A m) i * PA (-u) =
      c (-u) • (U (-u) *
        (PB (-(u + q')) * (blockTensor B m) i * PB (-(u + q'))) *
          (U (-u))ᴴ)
    rw [hindex]
    exact h
  have hBC : ∀ (u : Fin m) (w : List (Fin d)), w.length = m →
      cornerProd P A u w =
        c' u • (U' u * cornerProd Q B (u + q') w * (U' u)ᴴ) := by
    intro u w hw
    induction w using List.ofFnRec with
    | _ n σ =>
        simp only [List.length_ofFn] at hw
        subst n
        let i : Fin (blockPhysDim d m) := (decodeBlockEquiv d m).symm σ
        have hword : wordOfBlock d m i = List.ofFn σ := by
          simp [wordOfBlock, i]
        rw [← hword,
          cornerProd_eq_blockDiagCorner P A hP_proj hP_shift,
          cornerProd_eq_blockDiagCorner Q B hQ_proj hQ_shift]
        exact hBlockAmbient' u i
  let segments
      (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d))
      (k : Fin m) : List (Fin d) :=
    σ k :: List.ofFn (ρ k)
  let combinedWord
      (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)) :
      List (Fin d) :=
    (cyclicList (segments σ ρ) 0 m).flatten
  have hsegments :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d))
        (k : Fin m),
        (segments σ ρ k).length • (1 : Fin m) = 1 := by
    intro σ ρ k
    simp only [segments, List.length_cons, List.length_ofFn, add_nsmul, one_nsmul,
      mul_nsmul, nsmul_card_one_fin, nsmul_zero, zero_add]
  have hcombinedWord_length :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)),
        (combinedWord σ ρ).length = (m * L + 1) * m := by
    intro σ ρ
    simp only [combinedWord, cyclicList_zero_card_eq_ofFn, List.length_flatten,
      List.map_ofFn, List.sum_ofFn, segments]
    simp only [Function.comp_apply, List.length_cons, List.length_ofFn]
    simp
    exact Nat.mul_comm m (m * L + 1)
  have hcombinedWord_corner :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)),
        cornerProd P A 0 (combinedWord σ ρ) =
          (List.ofFn (fun k => cornerLetter P A k (σ k) *
            cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod := by
    intro σ ρ
    have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
    have hconcat :=
      cornerProd_cyclicList_flatten_succ P A hP_proj (segments σ ρ)
        (hsegments σ ρ) 0 m.pred
    rw [hm, cyclicList_zero_card_eq_ofFn] at hconcat
    rw [cyclicList_zero_card_eq_ofFn] at hconcat
    change cornerProd P A 0 (cyclicList (segments σ ρ) 0 m).flatten = _
    rw [cyclicList_zero_card_eq_ofFn, hconcat]
    apply congrArg List.prod
    apply List.ofFn_inj.mpr
    funext k
    simp only [segments, cornerProd_cons, cornerLetter, Matrix.mul_assoc,
      corner_mul_cornerProd P A (k + 1) (List.ofFn (ρ k)) (hP_proj (k + 1))]
  have hcombinedMatch :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)),
        (List.ofFn (fun k => cornerLetter P A k (σ k) *
          cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod =
            (c' 0) ^ (m * L + 1) •
              (U' 0 * cornerProd Q B q' (combinedWord σ ρ) * (U' 0)ᴴ) := by
    intro σ ρ
    rw [← hcombinedWord_corner σ ρ]
    simpa only [zero_add] using
      cornerProd_blockMatch_partial_isometry_pow P Q A B q' U' c'
        hP_proj hQ_proj hQ_shift hU'_star_U hBC 0 (m * L)
        (combinedWord σ ρ) (hcombinedWord_length σ ρ)
  let Ω' : (u : Fin m) →
      MatrixAlg (dimA' u) →ₗ[ℂ]
        ((Fin L → Fin (blockPhysDim d m)) → ℂ) :=
    fun u => Ω (-u)
  have hΩ' : ∀ (u : Fin m) (X : MatrixAlg (dimA' u)),
      ∑ σ : Fin L → Fin (blockPhysDim d m),
        Ω' u X σ • evalWord (blocksA' u) (List.ofFn σ) = X :=
    fun u X => hΩ (-u) X
  have hφA'_mul : ∀ (u : Fin m) (X Y : MatrixAlg (dimA' u)),
      (φA' u (X * Y)).1 = (φA' u X).1 * (φA' u Y).1 :=
    fun u X Y => hφA_mul (-u) X Y
  have hA'_letter : ∀ (u : Fin m) (i : Fin (blockPhysDim d m)),
      (φA' u (blocksA' u i)).1 =
        P u * (blockTensor A m) i * P u :=
    fun u i => hA_letter (-u) i
  obtain ⟨Ωhat, hΩhat⟩ :=
    exists_ambientCornerRightInverse_of_sectorRightInverse
      P A blocksA' φA' hP_proj hP_shift hφA'_mul hA'_letter
      L hL_pos Ω' hΩ'
  let T : Fin m → Fin d → MatrixAlg D :=
    fun k i => U' k * cornerLetter Q B (k + q') i * (U' (k + 1))ᴴ
  let G : Fin m → (Fin (m * L) → Fin d) → MatrixAlg D :=
    fun k ρ =>
      U' k * cornerProd Q B (k + q') (List.ofFn ρ) * (U' k)ᴴ
  have hBcombined :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)),
        U' 0 * cornerProd Q B q' (combinedWord σ ρ) * (U' 0)ᴴ =
          (List.ofFn (fun k => T k (σ k) * G (k + 1) (ρ k))).prod := by
    intro σ ρ
    have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
    have hchain :=
      cyclic_transport_cornerProd_segments Q B q' U' hQ_proj hQ_shift
        hU'_star_U (segments σ ρ) (hsegments σ ρ) 0 m.pred
    rw [hm, nsmul_card_one_fin, zero_add] at hchain
    have hchain' :
        U' 0 * cornerProd Q B q' (combinedWord σ ρ) * (U' 0)ᴴ =
          (cyclicList
            (fun k => U' k * cornerProd Q B (k + q') (segments σ ρ k) *
              (U' (k + 1))ᴴ) 0 m).prod := by
      simpa only [combinedWord, zero_add] using hchain.symm
    rw [hchain']
    rw [cyclicList_zero_card_eq_ofFn]
    apply congrArg List.prod
    apply List.ofFn_inj.mpr
    funext k
    change U' k * cornerProd Q B (k + q') (σ k :: List.ofFn (ρ k)) *
        (U' (k + 1))ᴴ =
      (U' k * cornerLetter Q B (k + q') (σ k) * (U' (k + 1))ᴴ) *
        (U' (k + 1) * cornerProd Q B (k + 1 + q') (List.ofFn (ρ k)) *
          (U' (k + 1))ᴴ)
    exact transported_cornerProd_cons Q B q' U' hQ_proj hU'_star_U k
      (σ k) (List.ofFn (ρ k))
  have hGapMatch :
      ∀ (k : Fin m) (ρ : Fin (m * L) → Fin d),
        cornerProd P A k (List.ofFn ρ) = (c' k) ^ L • G k ρ := by
    intro k ρ
    have hL : L.pred + 1 = L := Nat.succ_pred_eq_of_pos hL_pos
    have hword : (List.ofFn ρ).length = (L.pred + 1) * m := by
      rw [List.length_ofFn, hL, Nat.mul_comm]
    simpa only [G, hL] using
      cornerProd_blockMatch_partial_isometry_pow P Q A B q' U' c'
        hP_proj hQ_proj hQ_shift hU'_star_U hBC k L.pred
        (List.ofFn ρ) hword
  have hc'_pow_ne : ∀ k : Fin m, (c' k) ^ L ≠ 0 := by
    intro k
    exact pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [hc'_norm k]; exact one_ne_zero))
  have hG_contraction :
      ∀ (k : Fin m) (X : MatrixAlg D), P k * X * P k = X →
        ∑ ρ, Ωhat k X ρ • G k ρ = ((c' k) ^ L)⁻¹ • X := by
    intro k X hX
    have hsolve : ∀ ρ, G k ρ =
        ((c' k) ^ L)⁻¹ • cornerProd P A k (List.ofFn ρ) := by
      intro ρ
      calc
        G k ρ = 1 • G k ρ := (one_smul ℂ _).symm
        _ = (((c' k) ^ L)⁻¹ * (c' k) ^ L) • G k ρ := by
          rw [inv_mul_cancel₀ (hc'_pow_ne k)]
        _ = ((c' k) ^ L)⁻¹ • ((c' k) ^ L • G k ρ) := by
          rw [smul_smul]
        _ = ((c' k) ^ L)⁻¹ • cornerProd P A k (List.ofFn ρ) := by
          rw [hGapMatch k ρ]
    simp_rw [hsolve, smul_smul]
    calc
      ∑ ρ, (Ωhat k X ρ * ((c' k) ^ L)⁻¹) •
          cornerProd P A k (List.ofFn ρ) =
          ((c' k) ^ L)⁻¹ •
            ∑ ρ, Ωhat k X ρ • cornerProd P A k (List.ofFn ρ) := by
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro ρ _
              rw [smul_smul]
              congr 1
              ring
      _ = ((c' k) ^ L)⁻¹ • X := by rw [hΩhat k X hX]
  let a : Fin m → ℂ := fun k => ((c' (k + 1)) ^ L)⁻¹
  let z : ℂ := (c' 0) ^ (m * L + 1) * ∏ k, a k
  have hInsertedProduct :
      ∀ (σ : Fin m → Fin d) (X : Fin m → MatrixAlg D),
        (∀ k, P (k + 1) * X k * P (k + 1) = X k) →
        (List.ofFn (fun k => cornerLetter P A k (σ k) * X k)).prod =
          z • (List.ofFn (fun k => T k (σ k) * X k)).prod := by
    intro σ X hX
    let weight : (Fin m → (Fin (m * L) → Fin d)) → ℂ :=
      fun ρ => ∏ k, Ωhat (k + 1) (X k) (ρ k)
    have hweighted :
        ∑ ρ, weight ρ •
            (List.ofFn (fun k => cornerLetter P A k (σ k) *
              cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod =
          (c' 0) ^ (m * L + 1) •
            ∑ ρ, weight ρ •
              (List.ofFn (fun k => T k (σ k) * G (k + 1) (ρ k))).prod := by
      calc
        ∑ ρ, weight ρ •
            (List.ofFn (fun k => cornerLetter P A k (σ k) *
              cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod =
            ∑ ρ, weight ρ •
              ((c' 0) ^ (m * L + 1) •
                (List.ofFn (fun k => T k (σ k) * G (k + 1) (ρ k))).prod) := by
                  apply Finset.sum_congr rfl
                  intro ρ _
                  rw [hcombinedMatch σ ρ, hBcombined σ ρ]
        _ = (c' 0) ^ (m * L + 1) •
            ∑ ρ, weight ρ •
              (List.ofFn (fun k => T k (σ k) * G (k + 1) (ρ k))).prod := by
                rw [Finset.smul_sum]
                apply Finset.sum_congr rfl
                intro ρ _
                exact smul_comm (weight ρ) ((c' 0) ^ (m * L + 1))
                  (List.ofFn
                    (fun k => T k (σ k) * G (k + 1) (ρ k))).prod
    have hleft :=
      cornerProd_contraction P A (m * L) Ωhat σ X
        (fun k => hΩhat (k + 1) (X k) (hX k))
    have hright :=
      ofFn_contraction
        (fun k => T k (σ k))
        (fun k => a k • X k)
        (fun k ρ => G (k + 1) ρ)
        (fun k _ ρ => Ωhat (k + 1) (X k) ρ)
        (fun k => by
          change ∑ ρ, Ωhat (k + 1) (X k) ρ • G (k + 1) ρ = a k • X k
          exact hG_contraction (k + 1) (X k) (hX k))
    change
      ∑ ρ, weight ρ •
          (List.ofFn (fun k => cornerLetter P A k (σ k) *
            cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod =
        (List.ofFn (fun k => cornerLetter P A k (σ k) * X k)).prod at hleft
    change
      ∑ ρ, weight ρ •
          (List.ofFn (fun k => T k (σ k) * G (k + 1) (ρ k))).prod =
        (List.ofFn (fun k => T k (σ k) * (a k • X k))).prod at hright
    rw [hleft, hright] at hweighted
    have hfactor :
        (List.ofFn (fun k => T k (σ k) * (a k • X k))).prod =
          (∏ k, a k) • (List.ofFn (fun k => T k (σ k) * X k)).prod := by
      simpa only [mul_smul_comm] using
        List.prod_ofFn_smul a (fun k => T k (σ k) * X k)
    rw [hfactor] at hweighted
    simpa only [z, smul_smul] using hweighted
  have hP_U : ∀ k, P k * U' k = U' k := by
    intro k
    calc
      P k * U' k = P k * (P k * U' k * Q (k + q')) := by
        rw [← hU'_corner k]
      _ = P k * U' k * Q (k + q') := by
        rw [← Matrix.mul_assoc (P k) (P k * U' k) (Q (k + q')),
          ← Matrix.mul_assoc (P k) (P k) (U' k), (hP_proj k).2]
      _ = U' k := (hU'_corner k).symm
  have hUstar_P : ∀ k, (U' k)ᴴ * P k = (U' k)ᴴ := by
    intro k
    have h := congrArg (fun M : MatrixAlg D => Mᴴ) (hP_U k)
    simpa only [Matrix.conjTranspose_mul, (hP_proj k).1.eq] using h
  have hAcorner_left : ∀ k i,
      P k * cornerLetter P A k i = cornerLetter P A k i := by
    intro k i
    simp only [cornerLetter, ← Matrix.mul_assoc, (hP_proj k).2]
  have hAcorner_right : ∀ k i,
      cornerLetter P A k i * P (k + 1) = cornerLetter P A k i := by
    intro k i
    simp only [cornerLetter, Matrix.mul_assoc, (hP_proj (k + 1)).2]
  have hT_left : ∀ k i, P k * T k i = T k i := by
    intro k i
    simp only [T, ← Matrix.mul_assoc, hP_U]
  have hT_right : ∀ k i, T k i * P (k + 1) = T k i := by
    intro k i
    simp only [T, Matrix.mul_assoc, hUstar_P]
  have hresult :
      ∀ σ : Fin m → Fin d,
        (⨂ₜ[ℂ] k : Fin m, cornerLetter P A k (σ k)) =
          z • (⨂ₜ[ℂ] k : Fin m, T k (σ k)) := by
    intro σ
    exact piTensorProduct_eq_smul_of_corner_cyclic_products
      P (fun k => cornerLetter P A k (σ k)) (fun k => T k (σ k)) z
      hP_proj
      (fun k => hAcorner_left k (σ k))
      (fun k => hAcorner_right k (σ k))
      (fun k => hT_left k (σ k))
      (fun k => hT_right k (σ k))
      (fun X hX => hInsertedProduct σ X hX)
  have hP_transfer : ∀ k, ∑ i, (A i)ᴴ * P k * A i = P (k + 1) := by
    intro k
    have h := hPA_shift (-(k + 1))
    have hsource : -(k + 1) + 1 = -k := by abel
    change
      transferMap (fun i => (A i)ᴴ) (PA (-(k + 1) + 1)) = PA (-(k + 1)) at h
    rw [hsource] at h
    simpa only [transferMap_apply, Matrix.conjTranspose_conjTranspose, P] using h
  have hQ_transfer : ∀ k, ∑ i, (B i)ᴴ * Q k * B i = Q (k + 1) := by
    intro k
    have h := hPB_shift (-(k + 1))
    have hsource : -(k + 1) + 1 = -k := by abel
    change
      transferMap (fun i => (B i)ᴴ) (PB (-(k + 1) + 1)) = PB (-(k + 1)) at h
    rw [hsource] at h
    simpa only [transferMap_apply, Matrix.conjTranspose_conjTranspose, Q] using h
  have hAcorner_norm : ∀ k,
      ∑ i, (cornerLetter P A k i)ᴴ * cornerLetter P A k i = P (k + 1) :=
    fun k => sum_cornerLetter_star_mul P A hP_proj hP_transfer k
  have hQcorner_norm : ∀ k,
      ∑ i, (cornerLetter Q B k i)ᴴ * cornerLetter Q B k i = Q (k + 1) :=
    fun k => sum_cornerLetter_star_mul Q B hQ_proj hQ_transfer k
  have hU_Q : ∀ k, U' k * Q (k + q') = U' k := by
    intro k
    calc
      U' k * Q (k + q') =
          (P k * U' k * Q (k + q')) * Q (k + q') := by
            rw [← hU'_corner k]
      _ = P k * U' k * Q (k + q') := by
        rw [Matrix.mul_assoc, (hQ_proj (k + q')).2]
      _ = U' k := (hU'_corner k).symm
  have hQcorner_left : ∀ k i,
      Q k * cornerLetter Q B k i = cornerLetter Q B k i := by
    intro k i
    simp only [cornerLetter, ← Matrix.mul_assoc, (hQ_proj k).2]
  have hT_norm : ∀ k, ∑ i, (T k i)ᴴ * T k i = P (k + 1) := by
    intro k
    calc
      ∑ i, (T k i)ᴴ * T k i =
          ∑ i, U' (k + 1) *
            ((cornerLetter Q B (k + q') i)ᴴ *
              cornerLetter Q B (k + q') i) * (U' (k + 1))ᴴ := by
                apply Finset.sum_congr rfl
                intro i _
                simp only [T, Matrix.conjTranspose_mul,
                  Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
                rw [← Matrix.mul_assoc (U' k)ᴴ (U' k),
                  hU'_star_U k]
                rw [← Matrix.mul_assoc (Q (k + q'))
                  (cornerLetter Q B (k + q') i) (U' (k + 1))ᴴ,
                  hQcorner_left (k + q') i]
      _ = U' (k + 1) *
          (∑ i, (cornerLetter Q B (k + q') i)ᴴ *
            cornerLetter Q B (k + q') i) * (U' (k + 1))ᴴ := by
              rw [Finset.mul_sum, Finset.sum_mul]
      _ = U' (k + 1) * Q (k + 1 + q') * (U' (k + 1))ᴴ := by
        rw [hQcorner_norm]
        congr 2
        abel
      _ = P (k + 1) := by
        rw [hU_Q (k + 1), hU'_U_star]
  have hc'_ne : ∀ k, c' k ≠ 0 :=
    fun k => norm_ne_zero_iff.mp (by rw [hc'_norm k]; exact one_ne_zero)
  have ha_ne : ∀ k, a k ≠ 0 := by
    intro k
    exact inv_ne_zero (pow_ne_zero _ (hc'_ne (k + 1)))
  have hz : z ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (hc'_ne 0)
    · exact Finset.prod_ne_zero_iff.mpr (fun k _ => ha_ne k)
  obtain ⟨ξ, hξ_pow⟩ :=
    IsAlgClosed.exists_pow_nat_eq (k := ℂ) z (NeZero.pos m)
  have hP_ne : ∀ k, P k ≠ 0 := by
    intro k hPk
    haveI : NeZero (dimA' k) := ⟨hNondeg (-k)⟩
    have hsupp := (φA' k (1 : MatrixAlg (dimA' k))).2
    have hval : (φA' k (1 : MatrixAlg (dimA' k))).1 = 0 := by
      simpa only [hPk, zero_mul, mul_zero] using hsupp.symm
    have hφ :
        φA' k (1 : MatrixAlg (dimA' k)) = 0 := Subtype.ext hval
    have hφ' :
        φA' k (1 : MatrixAlg (dimA' k)) =
          φA' k (0 : MatrixAlg (dimA' k)) := by
      simpa only [map_zero] using hφ
    have hone : (1 : MatrixAlg (dimA' k)) = 0 := (φA' k).injective hφ'
    exact one_ne_zero hone
  have hT_nonzero : ∀ k, ∃ i, T k i ≠ 0 := by
    intro k
    by_contra h
    have hzeroT : ∀ i, T k i = 0 :=
      fun i => not_ne_iff.mp ((not_exists.mp h) i)
    have hzero : P (k + 1) = 0 := by
      symm
      simpa [hzeroT] using hT_norm k
    exact hP_ne (k + 1) hzero
  let ref : Fin m → Fin d := fun k => (hT_nonzero k).choose
  have href_ne : ∀ k, T k (ref k) ≠ 0 :=
    fun k => (hT_nonzero k).choose_spec
  have hentry : ∀ k, ∃ r c : Fin D, T k (ref k) r c ≠ 0 := by
    intro k
    by_contra h
    have hzeroEntry : ∀ r c, T k (ref k) r c = 0 :=
      fun r c => not_ne_iff.mp ((not_exists.mp (not_exists.mp h r)) c)
    exact href_ne k (Matrix.ext fun r c => hzeroEntry r c)
  let r : Fin m → Fin D := fun k => (hentry k).choose
  let s : Fin m → Fin D := fun k => (hentry k).choose_spec.choose
  have href_entry : ∀ k, T k (ref k) (r k) (s k) ≠ 0 :=
    fun k => (hentry k).choose_spec.choose_spec
  obtain ⟨κ, hκ_prod, hκ⟩ :=
    TNLean.Algebra.PiTensorProductPhase.exists_kappa_product_one_of_piTensorProduct_eq_root_smul
        (fun k i => cornerLetter P A k i) T z ξ hz hξ_pow
        ref r s href_entry hresult
  let γ : Fin m → ℂ := fun k => κ k * ξ
  have hnorm_matrix : ∀ k, P (k + 1) =
      (star (γ k) * γ k) • P (k + 1) := by
    intro k
    calc
      P (k + 1) =
          ∑ i, (cornerLetter P A k i)ᴴ * cornerLetter P A k i :=
        (hAcorner_norm k).symm
      _ = ∑ i, (γ k • T k i)ᴴ * (γ k • T k i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hκ k i]
      _ = (star (γ k) * γ k) • ∑ i, (T k i)ᴴ * T k i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.conjTranspose_smul, smul_mul_smul_comm]
      _ = (star (γ k) * γ k) • P (k + 1) := by rw [hT_norm]
  have hP_entry : ∀ k, ∃ r c : Fin D, P k r c ≠ 0 := by
    intro k
    by_contra h
    have hzeroEntry : ∀ r c, P k r c = 0 :=
      fun r c => not_ne_iff.mp ((not_exists.mp (not_exists.mp h r)) c)
    exact hP_ne k (Matrix.ext fun r c => hzeroEntry r c)
  have hγ_star_mul : ∀ k, star (γ k) * γ k = 1 := by
    intro k
    obtain ⟨rk, ck, hPk⟩ := hP_entry (k + 1)
    have heq := congrArg (fun M : MatrixAlg D => M rk ck) (hnorm_matrix k)
    simp only [Matrix.smul_apply, smul_eq_mul] at heq
    apply mul_right_cancel₀ hPk
    simpa only [one_mul] using heq.symm
  have hγ_norm : ∀ k, ‖γ k‖ = 1 := by
    intro k
    have hnorm := congrArg norm (hγ_star_mul k)
    simp only [norm_mul, norm_star, norm_one] at hnorm
    nlinarith [norm_nonneg (γ k)]
  have ha_norm : ∀ k, ‖a k‖ = 1 := by
    intro k
    simp only [a, norm_inv, norm_pow, hc'_norm, one_pow, inv_one]
  have hz_norm : ‖z‖ = 1 := by
    change ‖(c' 0) ^ (m * L + 1) * ∏ k, a k‖ = 1
    rw [norm_mul, norm_pow, hc'_norm, one_pow, one_mul]
    have hprod : ∀ t : Finset (Fin m), ‖∏ k ∈ t, a k‖ = 1 := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | @insert k t hk ih =>
        rw [Finset.prod_insert hk, norm_mul, ha_norm k, one_mul]
        exact ih
    simpa using hprod Finset.univ
  have hξ_norm : ‖ξ‖ = 1 := by
    have hpow_norm := congrArg norm hξ_pow
    rw [norm_pow, hz_norm] at hpow_norm
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ξ) (NeZero.ne m)).mp hpow_norm
  have hκ_norm : ∀ k, ‖κ k‖ = 1 := by
    intro k
    have h := hγ_norm k
    simpa only [γ, norm_mul, hξ_norm, mul_one] using h
  have hP_sum : ∑ k, P k = 1 := by
    change (∑ k, PA (-k)) = 1
    convert (Equiv.sum_comp (Equiv.neg (Fin m)) PA).trans hPA_sum using 1 <;>
      rfl
  have hQ_sum : ∑ k, Q k = 1 := by
    change (∑ k, PB (-k)) = 1
    convert (Equiv.sum_comp (Equiv.neg (Fin m)) PB).trans hPB_sum using 1 <;>
      rfl
  have hA_cyclic : ∀ i, A i = ∑ k, P k * A i * P (k + 1) := by
    intro i
    calc
      A i = (∑ k, P k) * A i := by rw [hP_sum, Matrix.one_mul]
      _ = ∑ k, P k * A i := by rw [Finset.sum_mul]
      _ = ∑ k, P k * A i * P (k + 1) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hP_shift k i, Matrix.mul_assoc, (hP_proj (k + 1)).2]
  have hB_cyclic : ∀ i, B i = ∑ k, Q k * B i * Q (k + 1) := by
    intro i
    calc
      B i = (∑ k, Q k) * B i := by rw [hQ_sum, Matrix.one_mul]
      _ = ∑ k, Q k * B i := by rw [Finset.sum_mul]
      _ = ∑ k, Q k * B i * Q (k + 1) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hQ_shift k i, Matrix.mul_assoc, (hQ_proj (k + 1)).2]
  let κB : Fin m → ℂ := fun v => κ (v - q')
  have hκB_norm : ∀ v, ‖κB v‖ = 1 := fun v => hκ_norm (v - q')
  have hκB_prod : ∏ v, κB v = 1 := by
    change (∏ v, κ (v - q')) = 1
    convert (Equiv.prod_comp (Equiv.subRight q') κ).trans hκ_prod using 1 <;>
      rfl
  obtain ⟨φ, hφ_norm, hφ⟩ :=
    TNLean.Algebra.exists_fin_complex_unit_cyclic_coboundary_shift_of_prod_eq_one
      κB hκB_norm hκB_prod q'
  have hφ_ne : ∀ v, φ v ≠ 0 := by
    intro v
    exact norm_ne_zero_iff.mp (by rw [hφ_norm v]; exact one_ne_zero)
  have hφ_star : ∀ v, star (φ v) = (φ v)⁻¹ := by
    intro v
    apply mul_right_cancel₀ (hφ_ne v)
    rw [inv_mul_cancel₀ (hφ_ne v)]
    have hnormSq := Complex.normSq_eq_conj_mul_self (z := φ v)
    rw [Complex.normSq_eq_norm_sq, hφ_norm v, one_pow] at hnormSq
    convert hnormSq.symm using 1 <;> norm_num [Complex.star_def]
  let V : Fin m → MatrixAlg D := fun v => φ v • U' (v - q')
  have hV_corner : ∀ v, V v = P (v - q') * V v * Q v := by
    intro v
    have hindex : v - q' + q' = v := by abel
    simp only [V, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc
      U' (v - q') = P (v - q') * U' (v - q') * Q (v - q' + q') :=
        hU'_corner (v - q')
      _ = P (v - q') * U' (v - q') * Q v := by rw [hindex]
  have hV_star_V : ∀ v, (V v)ᴴ * V v = Q v := by
    intro v
    have hindex : v - q' + q' = v := by abel
    simp only [V, Matrix.conjTranspose_smul, smul_mul_smul_comm,
      hφ_star, inv_mul_cancel₀ (hφ_ne v), one_smul]
    rw [hU'_star_U, hindex]
  have hV_V_star : ∀ v, V v * (V v)ᴴ = P (v - q') := by
    intro v
    simp only [V, Matrix.conjTranspose_smul, smul_mul_smul_comm]
    have hunit : φ v * star (φ v) = 1 := by
      rw [hφ_star, mul_inv_cancel₀ (hφ_ne v)]
    rw [hunit, one_smul, hU'_U_star]
  have hphase : ∀ u,
      φ (u + q') * star (φ (u + q' + 1)) = κ u := by
    intro u
    rw [hφ_star]
    have hcob := hφ u
    change κ (u + q' - q') =
      φ (u + q') * (φ (u + q' + 1))⁻¹ at hcob
    convert hcob.symm using 1 <;> abel
  have hVprod : ∀ (u : Fin m) (i : Fin d),
      V (u + q') * cornerLetter Q B (u + q') i * (V (u + q' + 1))ᴴ =
        κ u • T u i := by
    intro u i
    have hindex₀ : u + q' - q' = u := by abel
    have hindex₁ : u + q' + 1 - q' = u + 1 := by abel
    simp only [V, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hindex₀, hindex₁, T]
    rw [mul_comm (star (φ (u + q' + 1))) (φ (u + q')), hphase]
  have hprop : ∀ (u : Fin m) (i : Fin d),
      P u * A i * P (u + 1) =
        ξ • (V (u + q') * (Q (u + q') * B i * Q (u + q' + 1)) *
          (V (u + q' + 1))ᴴ) := by
    intro u i
    change cornerLetter P A u i =
      ξ • (V (u + q') * cornerLetter Q B (u + q') i * (V (u + q' + 1))ᴴ)
    rw [hκ u i, hVprod, smul_smul]
    congr 1
    ring
  refine ⟨ξ, ?_⟩
  exact exists_unitary_globalGauge hP_proj hP_sum hQ_proj hQ_sum
    hV_corner hV_star_V hV_V_star hA_cyclic hB_cyclic hprop hξ_norm

end MPSTensor
