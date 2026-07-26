/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.FundamentalTheorem.SectorWeightComparison
import TNLean.MPS.Overlap.NormalTensorDichotomy

/-!
# Characterization of a basis of normal tensors

This module proves the characterization of a basis of normal tensors from
arXiv:1606.00608, Proposition 2.7 (`prop:char-BNT`, lines 271--280 and
1135--1146). For a tensor in canonical form, a finite candidate family is a
basis of normal tensors if and only if every candidate is normal, every active
canonical-form summand is gauge-phase equivalent to one member of the family,
and distinct members are not gauge-phase equivalent.

The canonical-form hypotheses below record the context of the source
proposition: the displayed summands are normal and their weighted direct sum
generates the same positive-length matrix product vectors as the original
tensor. Coverage is restricted to nonzero-weight summands, as explained in
`docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`. Positive bond
dimensions are implicit in the source's matrix algebras and are made explicit
through typeclass assumptions.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d D : ℕ}

/-- Normal tensors which are not MPV-phase equivalent have asymptotically
vanishing overlap.

This is the contrapositive form of arXiv:1606.00608, Corollary `eqV`, lines
1121--1128. -/
private lemma overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNormalTensor A) (hB : IsNormalTensor B)
    (hNot : ¬ MPVBlockPhaseEquiv A B) :
    Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (𝓝 0) := by
  rcases hA.mpv_phase_alternative hB with hZero | ⟨ζ, hζ, hState⟩
  · exact hZero
  · exfalso
    apply hNot
    refine ⟨ζ, ?_, ?_⟩
    · exact norm_ne_zero_iff.mp (by rw [hζ]; exact one_ne_zero)
    · intro N _hN σ
      have hEq := congrArg (fun v : MPVSpace d N => v σ) (hState N)
      simpa [mpvState_apply, PiLp.smul_apply, smul_eq_mul] using hEq

/-- Every sector of a full-support sector decomposition is represented in any
basis of normal tensors for the same matrix product vectors.

The nonzero copy weights make each sector coefficient nonzero infinitely
often, excluding the unused-candidate counterexample to unrestricted BNT
uniqueness.  This is the full-support direction used in the sector matching
argument of CPSV16, Appendix A, lines 1135--1148 and 1182.

Source: arXiv:1606.00608, Proposition 2.7 and Appendix A, lines 1135--1148
and 1182 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem SectorDecomposition.exists_phase_match_of_isCPSVBasisOfNormalTensors
    {g : ℕ} {dimB : Fin g → ℕ} [∀ j, NeZero (dimB j)]
    {P : SectorDecomposition d} [∀ j, NeZero (P.basisDim j)]
    (B : (j : Fin g) → MPSTensor d (dimB j))
    (hPNormal : ∀ j, IsNormalTensor (P.basis j))
    (hPDistinct : BlocksNotGaugePhaseEquiv (d := d) P.basis)
    (hBNormal : ∀ j, IsNormalTensor (B j))
    (hBNT : IsCPSVBasisOfNormalTensors P.toTensor (fun j => ⟨dimB j, B j⟩))
    (j₀ : Fin P.basisCount) :
    ∃ k : Fin g, MPVBlockPhaseEquiv (P.basis j₀) (B k) := by
  classical
  have hBDistinct : BlocksNotGaugePhaseEquiv (d := d) B :=
    hBNT.blocks_not_gaugePhaseEquiv
  have hPPhaseDistinct : ∀ i j : Fin P.basisCount, i ≠ j →
      ¬ MPVBlockPhaseEquiv (P.basis i) (P.basis j) := by
    intro i j hij hPhase
    obtain ⟨hdim, hGPE⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (hPNormal i) (hPNormal j)
    exact hPDistinct i j hij hdim hGPE
  have hBPhaseDistinct : ∀ i j : Fin g, i ≠ j →
      ¬ MPVBlockPhaseEquiv (B i) (B j) := by
    intro i j hij hPhase
    obtain ⟨hdim, hGPE⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (hBNormal i) (hBNormal j)
    exact hBDistinct i j hij hdim hGPE
  by_contra hNo
  push Not at hNo
  let T : Finset (Fin P.basisCount) :=
    Finset.univ.filter fun j : Fin P.basisCount =>
      ∀ k : Fin g, ¬ MPVBlockPhaseEquiv (P.basis j) (B k)
  have hj₀T : j₀ ∈ T := by
    simp [T, hNo]
  have hTNotPhase : ∀ (j : Fin P.basisCount), j ∈ T → ∀ k : Fin g,
      ¬ MPVBlockPhaseEquiv (P.basis j) (B k) := by
    intro j hj k
    exact (Finset.mem_filter.mp hj).2 k
  have hNotTPhase : ∀ j : Fin P.basisCount, j ∉ T →
      ∃ k : Fin g, MPVBlockPhaseEquiv (P.basis j) (B k) := by
    intro j hj
    have hnot : ¬ (∀ k : Fin g, ¬ MPVBlockPhaseEquiv (P.basis j) (B k)) := by
      intro hall
      exact hj (by simp [T, hall])
    push Not at hnot
    exact hnot
  have hScalar : ∀ c : {j : Fin P.basisCount // j ∉ T},
      ∃ k : Fin g, ∃ α : ℕ → ℂ, ∀ N : ℕ, 0 < N →
        mpvState (d := d) (P.basis c.1) N =
          α N • mpvState (d := d) (B k) N := by
    intro c
    obtain ⟨k, ζ, hζ, hmpv⟩ := hNotTPhase c.1 c.2
    refine ⟨k, fun N => (ζ ^ N)⁻¹, ?_⟩
    intro N hN
    apply PiLp.ext
    intro σ
    have hB_mpv : mpv (B k) σ = ζ ^ N * mpv (P.basis c.1) σ :=
      hmpv N hN σ
    have hζN : ζ ^ N ≠ 0 := pow_ne_zero N hζ
    simp only [mpvState_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      mpv (P.basis c.1) σ = (ζ ^ N)⁻¹ * (ζ ^ N * mpv (P.basis c.1) σ) := by
        rw [inv_mul_cancel_left₀ hζN]
      _ = (ζ ^ N)⁻¹ * mpv (B k) σ := by rw [← hB_mpv]
  choose kOf αOf hStateOf using hScalar
  letI : Fintype {j : Fin P.basisCount // j ∈ T} := Subtype.fintype (fun j => j ∈ T)
  letI : Fintype {j : Fin P.basisCount // j ∉ T} := Subtype.fintype (fun j => j ∉ T)
  let C :
      (x : Sum {j : Fin P.basisCount // j ∈ T} (Fin g)) →
        MPSTensor d
          (Sum.elim
            (fun j : {j : Fin P.basisCount // j ∈ T} => P.basisDim j.1)
            dimB x) :=
    Sum.rec
      (motive := fun x => MPSTensor d
        (Sum.elim
          (fun j : {j : Fin P.basisCount // j ∈ T} => P.basisDim j.1)
          dimB x))
      (fun j => P.basis j.1) B
  have hSelf : ∀ x,
      Tendsto (fun N => mpvOverlap (d := d) (C x) (C x) N) atTop
        (𝓝 (1 : ℂ)) := by
    intro x
    cases x with
    | inl j => simpa [C] using (hPNormal j.1).selfOverlap_tendsto_one
    | inr k => simpa [C] using (hBNormal k).selfOverlap_tendsto_one
  have hCross : ∀ x y, x ≠ y →
      Tendsto (fun N => mpvOverlap (d := d) (C x) (C y) N) atTop
        (𝓝 (0 : ℂ)) := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            have hij : i.1 ≠ j.1 := by
              intro h
              exact hxy (congrArg Sum.inl (Subtype.ext h))
            simpa [C] using
              overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv
                (hPNormal i.1) (hPNormal j.1) (hPPhaseDistinct i.1 j.1 hij)
        | inr k =>
            simpa [C] using
              overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv
                (hPNormal i.1) (hBNormal k) (hTNotPhase i.1 i.2 k)
    | inr k =>
        cases y with
        | inl i =>
            simpa [C] using tendsto_mpvOverlap_zero_swap
              (P.basis i.1) (B k)
              (overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv
                (hPNormal i.1) (hBNormal k) (hTNotPhase i.1 i.2 k))
        | inr l =>
            have hkl : k ≠ l := by
              intro h
              exact hxy (congrArg Sum.inr h)
            simpa [C] using
              overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv
                (hBNormal k) (hBNormal l) (hBPhaseDistinct k l hkl)
  have hLI : ∀ᶠ N in atTop,
      LinearIndependent ℂ
        (Sum.elim
          (fun j : {j : Fin P.basisCount // j ∈ T} =>
            mpvState (d := d) (P.basis j.1) N)
          (fun k : Fin g => mpvState (d := d) (B k) N)) :=
    (eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal
      C hSelf hCross).mono (fun N hN => by
        have key :
            (fun x : Sum {j : Fin P.basisCount // j ∈ T} (Fin g) =>
              mpvState (d := d) (C x) N) =
              Sum.elim
                (fun j : {j : Fin P.basisCount // j ∈ T} =>
                  mpvState (d := d) (P.basis j.1) N)
                (fun k : Fin g => mpvState (d := d) (B k) N) := by
          funext x
          cases x <;> rfl
        rw [← key]
        exact hN)
  have hCoeffEventuallyZero : ∀ᶠ N : ℕ in atTop, P.coeff N j₀ = 0 := by
    refine (hLI.and (Filter.eventually_atTop.mpr ⟨1, fun N hN => hN⟩)).mono ?_
    intro N hN
    rcases hN with ⟨hLIN, hNpos⟩
    obtain ⟨cB, hcB⟩ := hBNT.spans_mpv N hNpos
    have hPstate :
        mpvState (d := d) P.toTensor N =
          ∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N := by
      refine mpvState_eq_sum_of_decomp (d := d) P.toTensor P.basis
        (N := N) (fun j => P.coeff N j) ?_
      intro σ
      simpa [smul_eq_mul] using P.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hBstate :
        mpvState (d := d) P.toTensor N =
          ∑ k : Fin g, cB k • mpvState (d := d) (B k) N :=
      mpvState_eq_sum_of_decomp (d := d) P.toTensor B cB (hcB)
    have hPBsum :
        (∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N) =
          ∑ k : Fin g, cB k • mpvState (d := d) (B k) N :=
      hPstate.symm.trans hBstate
    let sumT : MPVSpace d N :=
      ∑ t : {j : Fin P.basisCount // j ∈ T}, P.coeff N t.1 •
        mpvState (d := d) (P.basis t.1) N
    let sumC : MPVSpace d N :=
      ∑ c : {j : Fin P.basisCount // j ∉ T}, P.coeff N c.1 •
        mpvState (d := d) (P.basis c.1) N
    let sumB : MPVSpace d N :=
      ∑ k : Fin g, cB k • mpvState (d := d) (B k) N
    let agg : Fin g → ℂ := fun k =>
      ∑ c : {j : Fin P.basisCount // j ∉ T},
        if kOf c = k then P.coeff N c.1 * αOf c N else 0
    let sumAgg : MPVSpace d N :=
      ∑ k : Fin g, agg k • mpvState (d := d) (B k) N
    have hSplitP : sumT + sumC = sumB := by
      have hsplit :=
        Fintype.sum_subtype_add_sum_subtype
          (p := fun j : Fin P.basisCount => j ∈ T)
          (f := fun j : Fin P.basisCount =>
            P.coeff N j • mpvState (d := d) (P.basis j) N)
      exact hsplit.trans hPBsum
    have hCSubst :
        sumC = ∑ c : {j : Fin P.basisCount // j ∉ T},
          (P.coeff N c.1 * αOf c N) •
            mpvState (d := d) (B (kOf c)) N := by
      refine Finset.sum_congr rfl ?_
      intro c _
      calc
        P.coeff N c.1 • mpvState (d := d) (P.basis c.1) N =
            P.coeff N c.1 •
              (αOf c N • mpvState (d := d) (B (kOf c)) N) := by
                rw [hStateOf c N hNpos]
        _ = (P.coeff N c.1 * αOf c N) •
              mpvState (d := d) (B (kOf c)) N := by
                rw [smul_smul]
    have hCGroup :
        (∑ c : {j : Fin P.basisCount // j ∉ T},
          (P.coeff N c.1 * αOf c N) •
            mpvState (d := d) (B (kOf c)) N) = sumAgg := by
      simpa [sumAgg, agg] using
        (sum_fiber_smul (φ := kOf)
          (a := fun c : {j : Fin P.basisCount // j ∉ T} =>
            P.coeff N c.1 * αOf c N)
          (v := fun k : Fin g => mpvState (d := d) (B k) N))
    have hMain : sumT + sumAgg = sumB := by
      calc
        sumT + sumAgg = sumT + sumC := by rw [← hCGroup, ← hCSubst]
        _ = sumB := hSplitP
    let coeff : Sum {j : Fin P.basisCount // j ∈ T} (Fin g) → ℂ :=
      Sum.elim (fun t => P.coeff N t.1) (fun k => agg k - cB k)
    have hZeroCombined :
        ∑ x : Sum {j : Fin P.basisCount // j ∈ T} (Fin g),
          coeff x •
            Sum.elim
              (fun t : {j : Fin P.basisCount // j ∈ T} =>
                mpvState (d := d) (P.basis t.1) N)
              (fun k : Fin g => mpvState (d := d) (B k) N) x = 0 := by
      have hBsub :
          (∑ k : Fin g, (agg k - cB k) • mpvState (d := d) (B k) N) =
            sumAgg - sumB := by
        simp [sumAgg, sumB, sub_smul, Finset.sum_sub_distrib]
      have hZero :
          sumT +
            (∑ k : Fin g, (agg k - cB k) • mpvState (d := d) (B k) N) = 0 := by
        calc
          sumT +
              (∑ k : Fin g, (agg k - cB k) • mpvState (d := d) (B k) N) =
              sumT + (sumAgg - sumB) := by rw [hBsub]
          _ = (sumT + sumAgg) - sumB := by abel
          _ = 0 := sub_eq_zero.mpr hMain
      simpa [coeff, sumT] using hZero
    have hcoeff :=
      Fintype.linearIndependent_iff.mp hLIN coeff hZeroCombined
        (Sum.inl ⟨j₀, hj₀T⟩)
    simpa [coeff] using hcoeff
  exact (P.coeff_not_eventually_zero j₀) hCoeffEventuallyZero

/-- The all-active-block form of the CPSV16 basis characterization. -/
private theorem isCPSVBasisOfNormalTensors_iff_active_blocks_covered_and_minimal
    {r g : ℕ} {dimCF : Fin r → ℕ} {dimB : Fin g → ℕ}
    [∀ k, NeZero (dimCF k)] [∀ j, NeZero (dimB j)]
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dimCF k))
    (basis : (j : Fin g) → MPSTensor d (dimB j))
    (hBlocksNormal : ∀ k, IsNormalTensor (blocks k))
    (hμne : ∀ k, μ k ≠ 0)
    (hCF : SameMPV₂Pos A (toTensorFromBlocks (d := d) μ blocks)) :
    IsCPSVBasisOfNormalTensors A (fun j => ⟨dimB j, basis j⟩) ↔
      (∀ j, IsNormalTensor (basis j)) ∧
      (∀ k : Fin r, ∃ j : Fin g, ∃ hdim : dimB j = dimCF k,
        ∃ X : GL (Fin (dimCF k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, blocks k i = ζ •
            ((X : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis j)) i *
              (↑(X⁻¹) : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ))) ∧
      (∀ j k : Fin g, j ≠ k → ∀ hdim : dimB j = dimB k,
        ¬ ∃ X : GL (Fin (dimB k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, basis k i = ζ •
            ((X : Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis j)) i *
              (↑(X⁻¹) : Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ))) := by
  classical
  constructor
  · intro hBNT
    have hBasisNormal := hBNT.blocks_normal
    have hBasisDistinct := hBNT.blocks_not_gaugePhaseEquiv
    refine ⟨hBasisNormal, ?_, ?_⟩
    · let classes := mpvPhaseClassData blocks
      let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
      have hPBasis : ∀ j : Fin P.basisCount,
          P.basis j = blocks (classes.repr j) := by
        intro j
        rfl
      have hPBasisDim : ∀ j : Fin P.basisCount,
          P.basisDim j = dimCF (classes.repr j) := by
        intro j
        rfl
      letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) := fun j => by
        rw [hPBasisDim j]
        infer_instance
      have hPNormal : ∀ j : Fin P.basisCount, IsNormalTensor (P.basis j) := by
        intro j
        rw [hPBasis j]
        exact hBlocksNormal (classes.repr j)
      have hPDistinct : BlocksNotGaugePhaseEquiv (d := d) P.basis := by
        simpa [P, classes, collapsedBntSectorDecomp] using classes.blocks_not_equiv
      have hPA : SameMPV₂Pos P.toTensor A :=
        (collapsedBntSectorDecomp_sameMPV₂Pos (d := d) μ blocks hμne).trans hCF.symm
      have hPBNT :
          IsCPSVBasisOfNormalTensors P.toTensor
            (fun j => ⟨dimB j, basis j⟩) := by
        refine {
          blocks_normal := hBNT.blocks_normal
          spans_mpv := ?_
          eventually_li := hBNT.eventually_li
        }
        · intro N hN
          obtain ⟨c, hc⟩ := hBNT.spans_mpv N hN
          refine ⟨c, fun σ => ?_⟩
          rw [hPA N hN σ]
          exact hc σ
      intro k
      obtain ⟨jClass, q, hEnum⟩ := classes.exists_enum_eq k
      obtain ⟨jBasis, hRepBasis⟩ :=
        P.exists_phase_match_of_isCPSVBasisOfNormalTensors basis
          hPNormal hPDistinct hBasisNormal hPBNT jClass
      have hBasisRep : MPVBlockPhaseEquiv (basis jBasis) (blocks (classes.repr jClass)) := by
        rw [← hPBasis jClass]
        exact hRepBasis.symm
      have hRepBlock : MPVBlockPhaseEquiv (blocks (classes.repr jClass)) (blocks k) := by
        rw [← hEnum]
        exact classes.enum_phase jClass q
      have hBasisBlock : MPVBlockPhaseEquiv (basis jBasis) (blocks k) :=
        hBasisRep.trans hRepBlock
      obtain ⟨hdim, hGPE⟩ :=
        hBasisBlock.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
          (hBasisNormal jBasis) (hBlocksNormal k)
      obtain ⟨X, ζ, hζ, hrel⟩ := hGPE
      have hζnorm : ‖ζ‖ = 1 :=
        norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
          (hBasisNormal jBasis) (hBlocksNormal k) hdim hrel
      exact ⟨jBasis, hdim, X, ζ, hζnorm, hrel⟩
    · intro j k hjk hdim hUnit
      obtain ⟨X, ζ, hζnorm, hrel⟩ := hUnit
      exact hBasisDistinct j k hjk hdim
        ⟨X, ζ, norm_ne_zero_iff.mp (by rw [hζnorm]; exact one_ne_zero), hrel⟩
  · rintro ⟨hBasisNormal, hCover, hUnitDistinct⟩
    have hDistinct : BlocksNotGaugePhaseEquiv (d := d) basis := by
      intro j k hjk hdim hGPE
      obtain ⟨X, ζ, _hζ, hrel⟩ := hGPE
      apply hUnitDistinct j k hjk hdim
      exact ⟨X, ζ,
        norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
          (hBasisNormal j) (hBasisNormal k) hdim hrel,
        hrel⟩
    choose jOf hdimOf XOf ζOf hζnormOf hrelOf using hCover
    have hGPE : ∀ k : Fin r,
        GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) (hdimOf k)) (basis (jOf k)))
          (blocks k) := fun k =>
      ⟨XOf k, ζOf k,
        norm_ne_zero_iff.mp (by rw [hζnormOf k]; exact one_ne_zero), hrelOf k⟩
    have hPhase : ∀ k : Fin r,
        MPVBlockPhaseEquiv (basis (jOf k)) (blocks k) := fun k =>
      MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast
        (basis (jOf k)) (blocks k) (hdimOf k) (hGPE k)
    choose ζ hζ hmpv using hPhase
    refine {
      blocks_normal := hBasisNormal
      spans_mpv := ?_
      eventually_li :=
        exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
          basis hBasisNormal hDistinct
    }
    intro N hN
    let c : Fin g → ℂ := fun j =>
      ∑ k : Fin r, if jOf k = j then (μ k * ζ k) ^ N else 0
    refine ⟨c, ?_⟩
    intro σ
    calc
      mpv A σ = mpv (toTensorFromBlocks (d := d) μ blocks) σ := hCF N hN σ
      _ = ∑ k : Fin r, (μ k) ^ N * mpv (blocks k) σ := by
        simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ
      _ = ∑ k : Fin r, (μ k * ζ k) ^ N * mpv (basis (jOf k)) σ := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [hmpv k N hN σ, mul_pow]
        ring
      _ = ∑ j : Fin g, c j * mpv (basis j) σ := by
        have hGroup :=
          sum_fiber_smul (φ := jOf)
            (a := fun k : Fin r => (μ k * ζ k) ^ N)
            (v := fun j : Fin g => mpvState (d := d) (basis j) N)
        have hComponent := congrArg (fun v : MPVSpace d N => v σ) hGroup
        simpa [c, mpvState_apply, PiLp.smul_apply, smul_eq_mul] using hComponent

/-- Characterization of a basis of normal tensors by coverage of the active
normal canonical-form summands and minimality under gauge-phase equivalence.

This is arXiv:1606.00608, Proposition 2.7 (`prop:char-BNT`, lines 271--280
and 1135--1146).

**Local fix (active CF blocks and candidate normality):** Definition
`eq:II_CF1` at lines 238--244 permits zero weights syntactically, although the
construction at lines 214--225 lists the nonzero blocks and normalizes their
completely positive maps. Accordingly, coverage is required precisely when
the displayed weight is nonzero. Candidate normality, which is part of the BNT
definition at lines 271--274, is stated on the characterized side of the iff.
See `docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`. -/
theorem isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal
    {r g : ℕ} {dimCF : Fin r → ℕ} {dimB : Fin g → ℕ}
    [∀ k, NeZero (dimCF k)] [∀ j, NeZero (dimB j)]
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dimCF k))
    (basis : (j : Fin g) → MPSTensor d (dimB j))
    (hBlocksNormal : ∀ k, IsNormalTensor (blocks k))
    (hCF : SameMPV₂Pos A (toTensorFromBlocks (d := d) μ blocks)) :
    IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dimB j, basis j⟩) ↔
      (∀ j, IsNormalTensor (basis j)) ∧
      (∀ k : Fin r, μ k ≠ 0 →
        ∃ j : Fin g, ∃ hdim : dimB j = dimCF k,
        ∃ X : GL (Fin (dimCF k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, blocks k i = ζ •
            ((X : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis j)) i *
              (↑(X⁻¹) : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ))) ∧
      (∀ j k : Fin g, j ≠ k → ∀ hdim : dimB j = dimB k,
        ¬ ∃ X : GL (Fin (dimB k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, basis k i = ζ •
            ((X : Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis j)) i *
              (↑(X⁻¹) : Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ))) := by
  classical
  let Active := {k : Fin r // μ k ≠ 0}
  let activeEquiv : Fin (Fintype.card Active) ≃ Active :=
    (Fintype.equivFin Active).symm
  let dimActive : Fin (Fintype.card Active) → ℕ :=
    fun k ↦ dimCF (activeEquiv k)
  let μActive : Fin (Fintype.card Active) → ℂ :=
    fun k ↦ μ (activeEquiv k)
  let blocksActive : (k : Fin (Fintype.card Active)) → MPSTensor d (dimActive k) :=
    fun k ↦ blocks (activeEquiv k)
  letI : ∀ k, NeZero (dimActive k) := fun k ↦ by
    simp only [dimActive]
    infer_instance
  have hActiveNormal : ∀ k, IsNormalTensor (blocksActive k) := by
    intro k
    exact hBlocksNormal (activeEquiv k)
  have hμActive : ∀ k, μActive k ≠ 0 := by
    intro k
    exact (activeEquiv k).property
  have hActiveCF :
      SameMPV₂Pos A (toTensorFromBlocks (d := d) μActive blocksActive) := by
    intro N hN σ
    rw [hCF N hN σ]
    rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
    simp only [smul_eq_mul]
    let f : Fin r → ℂ := fun k ↦ μ k ^ N * mpv (blocks k) σ
    have hInactive : ∑ k : {k : Fin r // ¬ μ k ≠ 0}, f k = 0 := by
      apply Fintype.sum_eq_zero
      intro k
      simp [f, not_ne_iff.mp k.property, Nat.ne_of_gt hN]
    have hSplit :=
      Fintype.sum_subtype_add_sum_subtype (fun k : Fin r ↦ μ k ≠ 0) f
    have hActiveSum : (∑ k : Fin r, f k) = ∑ k : Active, f k := by
      rw [hInactive, add_zero] at hSplit
      exact hSplit.symm
    change (∑ k : Fin r, f k) =
      ∑ k : Fin (Fintype.card Active), f (activeEquiv k)
    rw [hActiveSum]
    exact (activeEquiv.sum_comp (fun k : Active ↦ f k)).symm
  have hCharacterization :=
    isCPSVBasisOfNormalTensors_iff_active_blocks_covered_and_minimal
      A μActive blocksActive basis hActiveNormal hμActive hActiveCF
  constructor
  · intro hBNT
    obtain ⟨hBasisNormal, hCover, hDistinct⟩ := hCharacterization.mp hBNT
    refine ⟨hBasisNormal, ?_, hDistinct⟩
    intro k hk
    let kActive : Active := ⟨k, hk⟩
    let l : Fin (Fintype.card Active) := activeEquiv.symm kActive
    have hkIndex : k = (activeEquiv l : Fin r) := by
      change k = (activeEquiv (activeEquiv.symm kActive) : Fin r)
      exact (congrArg Subtype.val (activeEquiv.apply_symm_apply kActive)).symm
    rw [hkIndex]
    simpa only [dimActive, blocksActive] using hCover l
  · rintro ⟨hBasisNormal, hCover, hDistinct⟩
    apply hCharacterization.mpr
    refine ⟨hBasisNormal, ?_, hDistinct⟩
    intro k
    simpa [dimActive, blocksActive] using
      hCover (activeEquiv k) (activeEquiv k).property

/-- Characterization of a basis of normal tensors for literal CPSV canonical-form data.

This specializes arXiv:1606.00608, Proposition 2.7 (`prop:char-BNT`, lines
271--301 and 1137--1148), to the data of eq. `II_CF1`.

**Local fix (active blocks):** Only blocks with nonzero weight are covered: a
syntactically listed zero-weight block contributes nothing to any positive-length
matrix product vector. See
`docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`. -/
theorem CPSVCanonicalFormData.isCPSVBasisOfNormalTensors_iff_covered_and_minimal
    {g : ℕ} {dimB : Fin g → ℕ} [∀ j, NeZero (dimB j)]
    (data : CPSVCanonicalFormData A)
    (basis : (j : Fin g) → MPSTensor d (dimB j)) :
    IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dimB j, basis j⟩) ↔
      (∀ j, IsNormalTensor (basis j)) ∧
      (∀ k : Fin data.r, data.weights k ≠ 0 →
        ∃ j : Fin g, ∃ hdim : dimB j = data.dim k,
        ∃ X : GL (Fin (data.dim k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, data.blocks k i = ζ •
            ((X : Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis j)) i *
              (↑(X⁻¹) : Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ))) ∧
      (∀ j k : Fin g, j ≠ k → ∀ hdim : dimB j = dimB k,
        ¬ ∃ X : GL (Fin (dimB k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, basis k i = ζ •
            ((X : Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis j)) i *
              (↑(X⁻¹) : Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ))) := by
  letI : ∀ k, NeZero (data.dim k) := fun k ↦ ⟨Nat.ne_of_gt (data.dim_pos k)⟩
  exact isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal
    A data.weights data.blocks basis data.blocks_normal
      data.sameMPV₂Pos_toTensorFromBlocks

end MPSTensor
