/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.ValidOracle
import TNLean.MPS.AreaLaw.Algorithm.SampledProgram

/-!
# The sampled route under every valid oracle

The sampled ground-state program is correct for every valid oracle: on good words its sweep
is viable at every cut with the size and bond budgets of the honest sweep, and its output
has the same overlap guarantee; hence the success probability of Theorem 1 holds for every
solver returning optimal solutions of the convex programs and cut decompositions of the
sampled projector. The honest oracle is one such solver.

**Local fix (trimming radius):** bond trimming uses the corrected quadratic radius
`bondTrimmingRadius` recorded at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.

**Local fix (error-reduction normalization):** the error-reduction step uses the corrected
direct estimate against the ground projection recorded in
`docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.

**Scope restriction (quantitative constants):** the size and bond budgets use the library
constant-cut bond `constantCutBond` and the corrected net exponent, not the printed quantitative
bounds; see `docs/paper-gaps/lvv13_constant_bond.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 213--216 and 652--678.
-/

open Matrix Cslib MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {o : {ι : Type} → LinearAlgebraQuery q ι → ι}

open LinearAlgebraQuery

/-- **The sampled error-reduction step with any admissible factors.** For a family `F` of
left factors containing a cut decomposition of the sampled projector, with at most `ℓ D`
members of rank at most `D` at the internal cuts, a half-viable family is taken to a
`4 η`-viable family when the sampled projector is within `η < 1/2` of the ground projection.
LVV13, `algo53.tex`, Claim `c:errorreduction`, lines 584--592. -/
theorem isViableMPS_errorReductionSet_of_admissible_sampled {i : ℕ} (hi : i ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) {D : ℕ} {F : Finset (LeftBlockMatrix L q i)}
    (hdec : ∃ (ι : Type) (J : Finset ι) (A : ι → LeftBlockMatrix L q i)
      (B : ι → RightBlockMatrix L q i),
      Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) (sampledProjector h E₀ I) =
          ∑ t ∈ J, A t ⊗ₖ B t ∧ ∀ t ∈ J, A t ∈ F)
    (hcard : F.card ≤ ℓ * D)
    (hrank : ∀ A ∈ F, ∀ k, k < i → operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ D)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1) {s b : ℕ}
    {S : Finset (LeftBlockVector L q i)} (hS : IsViableMPS Γ s b (1 / 2) S) {η : ℝ}
    (hKP : ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤ η)
    (hη : η < 1 / 2) :
    IsViableMPS Γ (ℓ * D * s) (D * max 1 b) (4 * η) (errorReductionSet F id S) := by
  classical
  obtain ⟨ι, J, A, B, hdecomp, hAF⟩ := hdec
  have hout := hS.errorReduction_of_norm_sub_groundProjection_le hi hΓ hdecomp
    (fun t ht k _ hki ↦ hrank (A t) (hAF t ht) k hki) hKP hη
  refine ⟨?_, ?_, ?_⟩
  · exact (card_errorReductionSet_le F id S).trans (Nat.mul_le_mul hcard hS.1)
  · exact fun v hv ↦ isLeftOpenMPS_of_mem_errorReductionSet hi
      (fun _ hA k _ hki ↦ hrank _ hA k hki) (fun _ hu ↦ hS.2.1 _ hu) hv
  · obtain ⟨v, hv1, hvΓ, hvS⟩ := hout.2.2
    refine ⟨v, hv1, hvΓ, ?_⟩
    have hsubset : (errorReductionSet J A S : Set (LeftBlockVector L q i)) ⊆
        errorReductionSet F id S := by
      intro w hw
      obtain ⟨k, hk, t, ht, rfl⟩ := Finset.mem_image₂.mp hw
      exact Finset.mem_image₂.mpr ⟨_, hAF k hk, t, ht, rfl⟩
    intro z
    exact Submodule.span_mono hsubset (hvS z)

/-- Under a valid oracle, one sampled step is the step with the oracle's sampled factors
applied to the selection of the oracle's nets and solver. -/
theorem eval_sampledSweepStepProgram_of_valid (hv : IsValidOracle o) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (b D : ℕ) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) :
    FreeM.eval o (sampledSweepStepProgram hq h hs h0 h1 E₀ Δ I b D hi S) =
      haveI : NeZero q := ⟨by omega⟩
      successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
        (o (LinearAlgebraQuery.sampledFactors L (i + 1) h E₀ ℓ m D I)) id
        ((ChainHamiltonian.ofBonds h hs h0 h1).sizeTrimmingSelectionWith hq Δ
          (AreaLaw.extend (i + 1) S) (oracleNets o L (i + 1) ((Δ / 169) ^ 2 / (2 * L)))
          (oracleSolver o L (i + 1) b (AreaLaw.extend (i + 1) S)
            (leftCutOperator (i + 1) ((ChainHamiltonian.ofBonds h hs h0 h1).cutLeftPart (i + 1)))
            ((Δ / 169) ^ 2 / (2 * L)))) := by
  simp only [sampledSweepStepProgram, FreeM.eval_bind, FreeM.eval_lift,
    eval_extensionProgram_of_valid hv, eval_sizeTrimmingProgram_of_valid hv,
    eval_bondTrimmingProgram_of_valid hv, eval_errorReductionProgram_of_valid hv, successiveStep]

/-- **One sampled step preserves viability on good words under every valid oracle**, with
the explicit size and bond bounds of the honest step. -/
theorem sampledSweepStepProgram_spec_of_valid (hv : IsValidOracle o) (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : GoodWords h E₀ m (δ / 8) κ I) (b : ℕ) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) (hS : IsViable Γ δ (S : Set (LeftBlockVector L q i))) :
    IsViableMPS Γ (ℓ * q ^ (2 * κ) *
        (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ))
      (q ^ (2 * κ) * max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))) δ
      (FreeM.eval o (sampledSweepStepProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) hi S)) := by
  classical
  let : NeZero q := ⟨by omega⟩
  rw [eval_sampledSweepStepProgram_of_valid hv hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) hi S]
  let chain := ChainHamiltonian.ofBonds h hs h0 h1
  have hgs' : IsGappedGroundState chain.operator E₀ Γ Δ := by
    simpa only [chain, ChainHamiltonian.ofBonds_operator] using hgs
  have hext : IsViable Γ ((Δ / 169) ^ 2 / L)
      (AreaLaw.extend (i + 1) S : Set (LeftBlockVector L q (i + 1))) :=
    (hS.extend (by omega) hi).mono hδc
  set m' := bondTrimmingRadius L (lvvReferenceBond q Δ L) with hm'
  set T₀ := chain.sizeTrimmingSelectionWith hq Δ (AreaLaw.extend (i + 1) S)
    (oracleNets o L (i + 1) ((Δ / 169) ^ 2 / (2 * L)))
    (oracleSolver o L (i + 1) b (AreaLaw.extend (i + 1) S)
      (leftCutOperator (i + 1) (chain.cutLeftPart (i + 1))) ((Δ / 169) ^ 2 / (2 * L))) with hT₀
  have hnet := isAdmissibleNet_oracleNets hv (k := i + 1) hL chain hΔ
  have hsol := isAdmissibleSolver_oracleSolver hv chain hq Δ b (AreaLaw.extend (i + 1) S)
  have hT : IsViableMPS Γ (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ) m'
      (1 / 2) (bondTrimSet hi m' T₀) :=
    ⟨(card_bondTrimSet_le hi m' T₀).trans
      (chain.card_sizeTrimmingSelectionWith_le_polynomial hL hq hΔ _ _
        (card_oracleNets_le hv hL hq hΔ)),
      fun v hv' ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m' T₀ hv',
      chain.isViable_bondTrimSet_sizeTrimmingSelectionWith
        (ChainHamiltonian.posSemidef_ofBonds_term h hs h0 h1) hL hq hi hΔ
        (AreaLaw.extend (i + 1) S) hnet hsol E₀ Γ hgs' hext⟩
  have hrank : ∀ t k, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) (bondComplementWord h (I t))) ≤ q ^ (2 * κ) := fun t k ↦
    operatorSchmidtRank_cutOperator_bondComplementWord_le_all (by omega) h hs (I t)
      (hgood.2 t) k
  obtain ⟨hdec, hcardF, hrankF⟩ := hv.sampledFactors L (i + 1) h E₀ ℓ m (q ^ (2 * κ)) I hrank
  have hKP : ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
      δ / 4 := by
    calc
      _ ≤ ‖sampledProjector h E₀ I - powerProjector (∑ j, h j) L E₀ m‖ +
          ‖powerProjector (∑ j, h j) L E₀ m -
            vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ / 8 + δ / 8 := add_le_add hgood.1.le
          (norm_powerProjector_sub_le hL h h0 h1 hgs hΔ (by positivity) m hm)
      _ = δ / 4 := by ring
  have hout := isViableMPS_errorReductionSet_of_admissible_sampled hi h E₀ I hdec hcardF
    (hrankF hi) hgs.1 hT hKP (by linarith)
  have hδeq : 4 * (δ / 4) = δ := by ring
  rw [hδeq] at hout
  exact hout

/-- **The sampled sweep program on good words under every valid oracle** is viable at every
cut, with the uniform size and bond bounds at every positive cut. -/
theorem sampledSweepProgram_spec_of_valid (hv : IsValidOracle o) (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (b : ℕ) (i : ℕ) (hi : i ≤ L) :
    let S := FreeM.eval o (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) i)
    S.card ≤ (if i = 0 then 1 else ℓ * q ^ (2 * κ) *
        (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) ∧
      (∀ v ∈ S, IsLeftOpenMPS
        (if i = 0 then 1 else q ^ (2 * κ) * max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L)))
        v) ∧
      IsViable Γ δ (S : Set (LeftBlockVector L q i)) := by
  intro S
  induction i with
  | zero =>
    obtain ⟨hcard, hmps, hviable⟩ := isViableMPS_emptyLeftVector (L := L) (q := q) hgs.1
    exact ⟨by simp [S, sampledSweepProgram], by simpa [S, sampledSweepProgram] using hmps,
      by simpa [S, sampledSweepProgram] using hviable.mono hδ0.le⟩
  | succ i ih =>
    obtain ⟨-, -, hviable⟩ := ih (by omega)
    simp only [S, sampledSweepProgram, hi, ↓reduceDIte, FreeM.eval_bind, Nat.succ_ne_zero,
      ↓reduceIte]
    exact sampledSweepStepProgram_spec_of_valid hv hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc _ hm
      (hgood ⟨i, by omega⟩) b hi _ hviable

/-- **On good words the sampled program finds the ground state under every valid oracle.** -/
theorem sampledGroundStateProgram_spec_of_valid (hv : IsValidOracle o) (hL : 0 < L)
    (hq : 2 ≤ q) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (b : ℕ) :
    let ψ := FreeM.eval o (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)))
    ‖ψ‖ = 1 ∧ 1 - 8 * L * δ / Δ ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧
      IsOpenMPS L q ((ℓ * q ^ (2 * κ) *
          (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) *
        max 1 (q ^ (2 * κ) * max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))))
        (fun x ↦ ψ x) := by
  classical
  intro ψ
  set e := fullLeftEquiv L q with he
  set S := FreeM.eval o (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) L) with hSdef
  have hψ : ψ = o (LinearAlgebraQuery.energyMinimizer L b (∑ j, h j)
      (S.image fun w ↦ e.symm w)) := by
    simp only [ψ, sampledGroundStateProgram, FreeM.eval_bind, FreeM.eval_lift]
    rfl
  obtain ⟨hcard, hmps, hviable⟩ :=
    sampledSweepProgram_spec_of_valid hv hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I hm hgood b L le_rfl
  simp only [show L ≠ 0 by omega, ↓reduceIte] at hcard hmps
  obtain ⟨v, hv', hvnorm, hover⟩ := hviable.exists_fullLeftVector
  set U := Submodule.span ℂ ((S.image fun w ↦ e.symm w : Finset _) :
    Set (EuclideanSpace ℂ (Fin L → Fin q))) with hUdef
  have hUmap : U = (Submodule.span ℂ (S : Set (LeftBlockVector L q L))).map
      e.symm.toLinearEquiv.toLinearMap := by
    rw [hUdef, Finset.coe_image, Submodule.map_span]
    rfl
  have hw'U : e.symm v ∈ U := by
    rw [hUmap]
    exact Submodule.mem_map_of_mem hv'
  have hw'norm : ‖e.symm v‖ = 1 := by rw [e.symm.norm_map, hvnorm]
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : e.symm v = 0 := by simpa only [hbot, Submodule.mem_bot] using hw'U
    rw [this, norm_zero] at hw'norm
    exact zero_ne_one hw'norm
  obtain ⟨hψU, hψnorm, hψmin⟩ :=
    hv.energyMinimizer L b (∑ j, h j) (S.image fun w ↦ e.symm w) hUne
  rw [← hψ] at hψU hψnorm hψmin
  refine ⟨hψnorm, ?_, ?_⟩
  · obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
    have hover' : 1 - δ ≤ ‖⟪Γ, e.symm v⟫_ℂ‖ := by
      have : ⟪e.symm v, Γ⟫_ℂ = ⟪v, e Γ⟫_ℂ := by
        rw [← e.inner_map_map, e.apply_symm_apply]
      rw [← norm_inner_symm, this]
      exact hover
    let chain := ChainHamiltonian.ofBonds h hs h0 h1
    have hchain : chain.operator = ∑ j, h j := ChainHamiltonian.ofBonds_operator h hs h0 h1
    have hgsChain : IsGappedGroundState chain.operator E₀ Γ Δ := by rwa [hchain]
    have henergy := chain.re_inner_sub_le_of_overlap_of_range_one hgsChain hw'norm hover'
    rw [hchain] at henergy
    have hψenergy : (⟪ψ, toEuclideanLin (∑ j, h j) ψ⟫_ℂ).re - E₀ ≤ 8 * L * δ :=
      (sub_le_sub_right (hψmin _ hw'U hw'norm) E₀).trans henergy
    exact Entropy.norm_inner_ge_of_gap hΔ hgap hΓ hψnorm hψenergy
  · have hψU' : ψ ∈ U := hψU
    rw [hUmap] at hψU'
    obtain ⟨v', hv'', hvψ⟩ := Submodule.mem_map.mp hψU'
    have hvmps := isOpenMPS_leftChain_of_mem_span S hmps hv''
    have hcoord : (fun x ↦ ψ x) = fun x ↦ v' (leftConfigOfFin x) := by
      rw [← hvψ]
      rfl
    rw [hcoord]
    exact hvmps.mono (Nat.mul_le_mul_right _ hcard)

/-- **The sampled program succeeds with probability at least `1 - 1/(2 n²)` under every
valid oracle.** -/
theorem measureReal_sampledGroundStateProgram_success_of_valid [NeZero L]
    (hv : IsValidOracle o) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) (b : ℕ) :
    1 - 1 / (2 * (L : ℝ) ^ 2) ≤
      (stepWordsMeasure L (sampledWordCount q L E₀ Δ δ) (sampledPower L E₀ Δ δ)).real
        {I | let ψ := FreeM.eval o (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b
            (sampledRankBound q L E₀ Δ δ))
          ‖ψ‖ = 1 ∧ 1 - 8 * L * δ / Δ ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧
            IsOpenMPS L q ((sampledWordCount q L E₀ Δ δ * sampledRankBound q L E₀ Δ δ *
                (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) *
              max 1 (sampledRankBound q L E₀ Δ δ *
                max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))))
              (fun x ↦ ψ x)} := by
  refine (measureReal_forall_goodWords_ge h h0 h1 hgs hΔ hδ0).trans (measureReal_mono ?_)
  intro I hI
  exact sampledGroundStateProgram_spec_of_valid hv (Nat.pos_of_neZero L) hq h hs h0 h1 hΔ hgs
    hδ0 hδ1 hδc I (Nat.le_ceil _) hI b

end TNLean.MPS.AreaLaw
