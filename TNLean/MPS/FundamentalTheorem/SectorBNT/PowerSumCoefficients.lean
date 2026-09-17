/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.CanonicalForm.SectorComparison.PrimitiveBlocks
import TNLean.MPS.Core.PhysicalReindexTransport
import TNLean.MPS.FundamentalTheorem.SectorBNT.MatchAux
import TNLean.MPS.FundamentalTheorem.SectorBNT.SupplierNormalized
import TNLean.MPS.ParentHamiltonian.PrimitiveGaugeExistence
import TNLean.MPS.Periodic.Overlap.SelfOverlapSetup

/-!
# Power-sum structure of length-dependent coefficients

In a matrix product operator algebra closed at the level of the trace, the
structure constants attached to a chain of length `L` need not be independent of
`L`.  Cirac, Perez-Garcia, Schuch and Verstraete ask in arXiv:1606.00608,
Section 4.5, lines 995--1010, whether renormalization fixed points with genuinely
length-dependent structure constants exist, and record that constants which do
not depend on the length are forced to be nonnegative integers.  The project
open-problem note P6
(`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex`)
builds fixed points whose constants are sums of powers of finitely many complex
weights.

The theorem proved here says that this is the only possible shape.  Whenever the
periodic vectors of a tensor `B` lie, at every positive length, inside the span
of the periodic vectors of a family of pairwise inequivalent normal tensors, the
coefficients of that expansion are, along the lengths of one fixed blocking,
uniquely determined and equal to the power sums of finite multisets of nonzero
complex weights.  The blocking is the one the source itself performs before
reading off a basis of normal tensors, so the statement is the blocked stage of
the question; passing from blocked lengths to all lengths is left open here.

## Main results

* `MPSTensor.exists_blocked_representatives_of_isNormal_distinct` — a family of
  algebraically normal tensors that are pairwise not gauge-phase equivalent has
  left-canonical irreducible representatives after blocking, with nonzero
  scalars recording the rescaling, and blocking does not merge two members.
* `MPSTensor.exists_matching_data_of_isBNTCanonicalForm` — every basis block of a
  basis-of-normal-tensors canonical form either has decaying overlap with a
  separated family or is gauge-phase equivalent to one of its members, and past a
  threshold length the matching determines the coefficients of any common
  expansion.
* `MPSTensor.exists_blocking_powerSum_weights` — the rigidity half: along the
  blocked lengths, any expansion has the power-sum coefficients.
* `MPSTensor.exists_blocking_powerSum_coeff` — the full statement, rigidity
  together with the expansion supplied by the spanning hypothesis.

## Source anchors

* arXiv:1606.00608, `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 995--1010 —
  the open question on length-dependent structure constants and the
  length-independent case.
* arXiv:1606.00608, lines 237--246 and 271--301 — the canonical form after
  blocking, its weight normalization, and the two-layer basis-of-normal-tensors
  expansion whose coefficients are the power sums appearing below.
* Project open-problem note P5,
  `Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.7 —
  the compression setting in which these coefficients arise.
* Project open-problem note P6,
  `Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex` —
  the constructions whose coefficients are power sums of channel weights.

## Tags

matrix product states, renormalization fixed point, structure constants, basis of
normal tensors, power sums
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **Left-canonical normalized representative of an algebraically normal tensor.**

An algebraically normal tensor is, after a gauge and a nonzero rescaling,
left-canonical with primitive irreducible transfer map and spectral radius one.
This is the normalization taken without loss of generality at
arXiv:quant-ph/0608197, proof of Theorem 4, lines 765--770.  The scalar `ζ`
records the rescaling in the periodic vectors. -/
theorem exists_leftCanonical_normalTensor_scale_of_isNormal
    {D : ℕ} [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsNormal A) :
    ∃ (B : MPSTensor d D) (ζ : ℂ), ζ ≠ 0 ∧ GaugeEquiv (ζ • A) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) ∧
      IsLeftCanonical B ∧ IsNormalTensor B := by
  obtain ⟨B, ζ, ρ, hζ, hGauge, hMpv, hPrim, _hρ, _, _, _⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal hA
  have hLC : IsLeftCanonical B := hPrim.norm
  have hNormalB : Kraus.IsNormal B :=
    isNormal_of_gaugeEquiv ((isNormal_smul_iff hζ A).2 hA) hGauge
  exact ⟨B, ζ, hζ, hGauge, hMpv, hLC,
    isNormalTensor_of_isNormal_leftCanonical B hNormalB hLC⟩

/-- Nonzero rescalings on either side do not affect gauge-phase equivalence. -/
theorem gaugePhaseEquiv_of_smul_smul_cast
    {D₁ D₂ : ℕ} (hdim : D₁ = D₂) {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {c e : ℂ} (hc : c ≠ 0) (he : e ≠ 0)
    (h : GaugePhaseEquiv
      (cast (congr_arg (MPSTensor d) hdim) (c • A)) (e • B)) :
    GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) A) B := by
  subst hdim
  simp only [cast_eq] at h ⊢
  obtain ⟨X, ζ, hζ, hrel⟩ := h
  refine ⟨X, e⁻¹ * (ζ * c), by simp [hζ, hc, he], fun i => ?_⟩
  have hi := hrel i
  simp only [Pi.smul_apply] at hi
  have hB : B i = e⁻¹ • (e • B i) := (inv_smul_smul₀ he (B i)).symm
  rw [hB, hi]
  simp [smul_smul]

/-- Eventual linear independence of the matrix product vectors of a finite family of
normalized normal tensors that are pairwise not gauge-phase equivalent.

This is the arbitrary finite index set version of
`exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv`. -/
theorem exists_eventually_linearIndependent_of_normalTensor_distinct
    {ι : Type*} [Finite ι] {dim : ι → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : ι) → MPSTensor d (dim k))
    (hNormal : ∀ k, IsNormalTensor (A k))
    (hDistinct : ∀ j k : ι, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)) :
    ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ (fun k : ι => mpvState (d := d) (A k) N) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  set e := Fintype.equivFin ι with he
  obtain ⟨N₀, hLI⟩ :=
    exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
      (d := d) (dim := fun k => dim (e.symm k)) (fun k => A (e.symm k))
      (fun k => hNormal (e.symm k))
      (fun j k hjk h => hDistinct (e.symm j) (e.symm k)
        (fun hEq => hjk (by simpa using congrArg e hEq)) h)
  refine ⟨N₀, fun N hN => ?_⟩
  have hfun : ((fun k : Fin (Fintype.card ι) => mpvState (d := d) (A (e.symm k)) N) ∘ e)
      = fun k : ι => mpvState (d := d) (A k) N := by
    funext k
    exact congrArg (fun y : ι => mpvState (d := d) (A y) N) (e.symm_apply_apply k)
  rw [← hfun]
  exact (hLI N hN).comp e e.injective

/-- Eventual linear independence of the blocked matrix product vectors of a finite
family of normalized normal tensors that are pairwise not gauge-phase equivalent. -/
theorem exists_eventually_linearIndependent_blockTensor_of_normalTensor_distinct
    {ι : Type*} [Finite ι] {dim : ι → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : ι) → MPSTensor d (dim k)) {p : ℕ} (hp : 0 < p)
    (hNormal : ∀ k, IsNormalTensor (A k))
    (hDistinct : ∀ j k : ι, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)) :
    ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ
        (fun k : ι => mpvState (d := blockPhysDim d p) (blockTensor (A k) p) N) := by
  obtain ⟨N₀, hLI⟩ :=
    exists_eventually_linearIndependent_of_normalTensor_distinct A hNormal hDistinct
  refine ⟨N₀, fun N hN => ?_⟩
  refine linearIndependent_mpvState_of_configEquiv (blockedConfigEquiv d N p)
    (fun k => blockTensor (A k) p) A ?_ ?_
  · intro k σ
    change mpv (blockTensor (A k) p) ((blockedConfigEquiv d N p).symm σ) = mpv (A k) σ
    simp only [mpv, MPSTensor.coeff, evalWord_blockTensor]
    rw [← ofFn_blockedConfigEquiv d N p ((blockedConfigEquiv d N p).symm σ)]
    simp
  · exact hLI (N * p) (lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hp))

/-- Eventual linear independence of matrix product vectors rules out gauge-phase
equivalence between two distinct members of the family. -/
theorem not_gaugePhaseEquiv_of_exists_eventually_linearIndependent
    {ι : Type*} {dim : ι → ℕ} (A : (k : ι) → MPSTensor d (dim k))
    (hLI : ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ (fun k : ι => mpvState (d := d) (A k) N))
    {j k : ι} (hjk : j ≠ k) (hdim : dim j = dim k) :
    ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k) := by
  rintro ⟨X, ζ, -, hX⟩
  obtain ⟨N₀, hLI⟩ := hLI
  have hState : mpvState (d := d) (A k) (N₀ + 1) =
      (ζ ^ (N₀ + 1)) • mpvState (d := d) (A j) (N₀ + 1) := by
    ext σ
    change mpv (A k) σ = ζ ^ (N₀ + 1) * mpv (A j) σ
    rw [mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX (N₀ + 1) σ,
      mpv_cast_dim hdim (A j) (N₀ + 1) σ]
  have hEq : (1 : ℂ) • mpvState (d := d) (A k) (N₀ + 1) =
      (ζ ^ (N₀ + 1)) • mpvState (d := d) (A j) (N₀ + 1) := by simpa using hState
  exact hjk (((hLI (N₀ + 1) (by omega)).eq_of_smul_apply_eq_smul_apply
    1 (ζ ^ (N₀ + 1)) k j one_ne_zero hEq).symm)

/-- **Blocked canonical representatives of a separated family of normal tensors.**

Every algebraically normal tensor becomes left-canonical after a gauge and a
nonzero rescaling, and these properties survive physical blocking.  The scalar
`ξ γ` records the rescaling at the blocked length, and blocking never merges two
members that were not gauge-phase equivalent. -/
theorem exists_blocked_representatives_of_isNormal_distinct
    {Γ : Type*} [Finite Γ] {DM : Γ → ℕ} (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    {p : ℕ} (hp : 0 < p) :
    ∃ (C : ∀ γ, MPSTensor (blockPhysDim d p) (DM γ)) (ξ : Γ → ℂ),
      (∀ γ, ξ γ ≠ 0) ∧
      (∀ (γ : Γ) (N : ℕ) (τ : Fin N → Fin (blockPhysDim d p)),
        mpv (C γ) τ = (ξ γ) ^ N * mpv (blockTensor (M γ) p) τ) ∧
      (∀ γ, IsLeftCanonical (C γ)) ∧
      (∀ γ, Kraus.IsIrreducibleFamily (C γ)) ∧
      (∀ γ, Tendsto (fun N : ℕ => mpvOverlap (d := blockPhysDim d p) (C γ) (C γ) N)
        atTop (𝓝 (1 : ℂ))) ∧
      (∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
        ¬ GaugePhaseEquiv
          (cast (congr_arg (MPSTensor (blockPhysDim d p)) h) (C γ)) (C δ)) := by
  classical
  have hNe : ∀ γ, NeZero (DM γ) := fun γ => ⟨(hD γ).ne'⟩
  choose Mc ζ hζ hGauge hMpv hLC hNT using
    fun γ => exists_leftCanonical_normalTensor_scale_of_isNormal (hM γ)
  have hMcDistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (Mc γ)) (Mc δ) := by
    intro γ δ hne h hGPE
    exact hdistinct γ δ hne h
      (gaugePhaseEquiv_of_smul_smul_cast h (hζ γ) (hζ δ)
        (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGauge γ) hGPE (hGauge δ)))
  refine ⟨fun γ => blockTensor (Mc γ) p, fun γ => (ζ γ) ^ p, fun γ => pow_ne_zero p (hζ γ),
    ?_, fun γ => leftCanonical_blockTensor (Mc γ) p (hLC γ), ?_, ?_, ?_⟩
  · intro γ N τ
    rw [mpv_blockTensor_eq_mpv_blockedFlatConfig, mpv_blockTensor_eq_mpv_blockedFlatConfig,
      hMpv γ (N * p) (blockedFlatConfig (d := d) p τ)]
    congr 1
    rw [← pow_mul, Nat.mul_comm]
  · intro γ
    exact isIrreducibleTensor_blockTensor_of_tp_primitive_irr (Mc γ) (hLC γ)
      (hNT γ).primitive_transfer (hNT γ).no_invariant_proj hp
  · intro γ
    have hMul : Tendsto (fun N : ℕ => N * p) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop b] with a ha
      exact ha.trans (Nat.le_mul_of_pos_right a hp)
    refine (((hNT γ).selfOverlap_tendsto_one).comp hMul).congr' ?_
    filter_upwards with N
    exact (mpvOverlap_blockTensor_self_eq (Mc γ) p N).symm
  · intro γ δ hne h
    exact not_gaugePhaseEquiv_of_exists_eventually_linearIndependent
      (d := blockPhysDim d p) (fun γ => blockTensor (Mc γ) p)
      (exists_eventually_linearIndependent_blockTensor_of_normalTensor_distinct
        Mc hp hNT hMcDistinct) hne h

/-- **Matching data and eventual coefficient rigidity.**

For a basis-of-normal-tensors canonical form `P` and a separated family `C` of
left-canonical irreducible tensors with normalized self-overlaps, every basis
block of `P` either has decaying overlap with the whole family `C` or is
gauge-phase equivalent to one of its members.  Past a threshold length the
matching determines the `C`-side coefficients of any common expansion. -/
theorem exists_matching_data_of_isBNTCanonicalForm
    {a : ℕ} {P : SectorDecomposition a} (hCF : IsBNTCanonicalForm P)
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {DM : Γ → ℕ}
    (C : ∀ γ, MPSTensor a (DM γ)) (hDpos : ∀ γ, 0 < DM γ)
    (hCLC : ∀ γ, IsLeftCanonical (C γ))
    (hCirr : ∀ γ, Kraus.IsIrreducibleFamily (C γ))
    (hCself : ∀ γ, Tendsto (fun N : ℕ => mpvOverlap (d := a) (C γ) (C γ) N)
      atTop (𝓝 (1 : ℂ)))
    (hCdist : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor a) h) (C γ)) (C δ)) :
    ∃ (lab : Fin P.basisCount → Option Γ) (sc : Fin P.basisCount → ℂ) (N₁ : ℕ),
      (∀ j, sc j ≠ 0) ∧
      (∀ (j : Fin P.basisCount) (γ : Γ), lab j = some γ →
        ∀ (N : ℕ) (τ : Fin N → Fin a), mpv (C γ) τ = (sc j) ^ N * mpv (P.basis j) τ) ∧
      ∀ m : ℕ, N₁ ≤ m → ∀ (α : Fin P.basisCount → ℂ) (β : Γ → ℂ),
        (∀ τ : Fin m → Fin a,
          ∑ j, α j * mpv (P.basis j) τ = ∑ γ, β γ * mpv (C γ) τ) →
        ∀ γ, β γ = ∑ j, (if lab j = some γ then α j * ((sc j) ^ m)⁻¹ else 0) := by
  classical
  have hmix : ∀ (j : Fin P.basisCount) (γ : Γ),
      ¬ Tendsto (fun N : ℕ => mpvOverlap (d := a) (P.basis j) (C γ) N) atTop (𝓝 0) →
      ∃ η : ℂ, η ≠ 0 ∧ ∀ (N : ℕ) (τ : Fin N → Fin a),
        mpv (C γ) τ = η ^ N * mpv (P.basis j) τ := by
    intro j γ hnd
    have _hj : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
    have _hγ : NeZero (DM γ) := ⟨(hDpos γ).ne'⟩
    have hdim : P.basisDim j = DM γ := by
      by_contra hne
      exact hnd (mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP (P.basis j) (C γ)
        (hCF.basis_irreducible j) (hCirr γ) (hCF.basis_left_canonical j) (hCLC γ) hne)
    have hGPE : GaugePhaseEquiv (cast (congr_arg (MPSTensor a) hdim) (P.basis j)) (C γ) := by
      by_contra hNot
      exact hnd (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
        (hdim := hdim) (A := P.basis j) (B := C γ)
        (hA_irr := hCF.basis_irreducible j) (hB_irr := hCirr γ)
        (hA_norm := hCF.basis_left_canonical j) (hB_norm := hCLC γ) (hNot := hNot))
    obtain ⟨X, η, hη, hrel⟩ := hGPE
    exact ⟨η, hη, fun N τ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X η hrel N τ, mpv_cast_dim hdim (P.basis j) N τ]⟩
  have hclass : ∀ j : Fin P.basisCount, ∃ (o : Option Γ) (η : ℂ), η ≠ 0 ∧
      (∀ γ : Γ, o = some γ → ∀ (N : ℕ) (τ : Fin N → Fin a),
        mpv (C γ) τ = η ^ N * mpv (P.basis j) τ) ∧
      (o = none → ∀ γ : Γ,
        Tendsto (fun N : ℕ => mpvOverlap (d := a) (P.basis j) (C γ) N) atTop (𝓝 0)) := by
    intro j
    by_cases h : ∃ γ : Γ,
        ¬ Tendsto (fun N : ℕ => mpvOverlap (d := a) (P.basis j) (C γ) N) atTop (𝓝 0)
    · obtain ⟨γ₀, hγ₀⟩ := h
      obtain ⟨η, hη, hmpv⟩ := hmix j γ₀ hγ₀
      refine ⟨some γ₀, η, hη, ?_, by simp⟩
      rintro γ hγ
      rw [Option.some_inj] at hγ
      subst hγ
      exact hmpv
    · push Not at h
      exact ⟨none, 1, one_ne_zero, by simp, fun _ => h⟩
  choose lab sc hsc hsome hnone using hclass
  have hCcross : ∀ γ δ : Γ, γ ≠ δ →
      Tendsto (fun N : ℕ => mpvOverlap (d := a) (C γ) (C δ) N) atTop (𝓝 0) := by
    intro γ δ hne
    have _hγ : NeZero (DM γ) := ⟨(hDpos γ).ne'⟩
    have _hδ : NeZero (DM δ) := ⟨(hDpos δ).ne'⟩
    by_cases hdim : DM γ = DM δ
    · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
        (hdim := hdim) (A := C γ) (B := C δ) (hA_irr := hCirr γ) (hB_irr := hCirr δ)
        (hA_norm := hCLC γ) (hB_norm := hCLC δ) (hNot := hCdist γ δ hne hdim)
    · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP (C γ) (C δ)
        (hCirr γ) (hCirr δ) (hCLC γ) (hCLC δ) hdim
  let dimF : ({j : Fin P.basisCount // lab j = none}) ⊕ Γ → ℕ :=
    Sum.elim (fun j => P.basisDim j.1) DM
  let F : (x : ({j : Fin P.basisCount // lab j = none}) ⊕ Γ) → MPSTensor a (dimF x) :=
    Sum.rec (motive := fun x => MPSTensor a (dimF x)) (fun j => P.basis j.1) C
  have hself : ∀ x, Tendsto (fun N : ℕ => mpvOverlap (d := a) (F x) (F x) N)
      atTop (𝓝 (1 : ℂ)) := by
    rintro (j | γ)
    · exact hCF.basis_normalized_self_overlap j.1
    · exact hCself γ
  have hcross : ∀ x y, x ≠ y →
      Tendsto (fun N : ℕ => mpvOverlap (d := a) (F x) (F y) N) atTop (𝓝 (0 : ℂ)) := by
    rintro (i | γ) (j | δ) hxy
    · exact hCF.cross_overlap_basis_tendsto_zero
        (fun hval => hxy (congrArg Sum.inl (Subtype.ext hval)))
    · exact hnone i.1 i.2 δ
    · exact tendsto_mpvOverlap_zero_swap (d := a) (A := P.basis j.1) (B := C γ)
        (N := id) (hnone j.1 j.2 γ)
    · exact hCcross γ δ (fun h => hxy (by rw [h]))
  obtain ⟨N₁, hLI⟩ := Filter.eventually_atTop.1
    (eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal F hself hcross)
  refine ⟨lab, sc, N₁, hsc, hsome, ?_⟩
  intro m hm α β hEq γ
  set b : Fin P.basisCount → Γ → ℂ :=
    fun j δ => if lab j = some δ then α j * ((sc j) ^ m)⁻¹ else 0 with hb
  have hper : ∀ (j : Fin P.basisCount) (τ : Fin m → Fin a),
      ∑ δ, b j δ * mpv (C δ) τ
        = if lab j = none then 0 else α j * mpv (P.basis j) τ := by
    intro j τ
    rcases hlab : lab j with _ | γ₀
    · simp [hb, hlab]
    · have hgoal : (if (some γ₀ : Option Γ) = none then (0 : ℂ)
          else α j * mpv (P.basis j) τ) = α j * mpv (P.basis j) τ := by simp
      rw [hgoal, Finset.sum_eq_single γ₀]
      · have hbj : b j γ₀ = α j * ((sc j) ^ m)⁻¹ := by simp [hb, hlab]
        have hne : (sc j) ^ m ≠ 0 := pow_ne_zero m (hsc j)
        rw [hbj, hsome j γ₀ hlab m τ]
        field_simp
      · intro δ _ hδ
        have hzeroδ : b j δ = 0 := by
          have : ¬ (lab j = some δ) := by rw [hlab]; simpa using fun h => hδ h.symm
          simp [hb, this]
        rw [hzeroδ, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ γ₀) h
  have hsplit : ∀ τ : Fin m → Fin a,
      (∑ j ∈ Finset.univ.filter (fun j => lab j = none), α j * mpv (P.basis j) τ)
        + ∑ δ, ((∑ j, b j δ) - β δ) * mpv (C δ) τ = 0 := by
    intro τ
    have h1 : ∑ δ, (∑ j, b j δ) * mpv (C δ) τ = ∑ j, ∑ δ, b j δ * mpv (C δ) τ := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    have h2 : ∑ j, ∑ δ, b j δ * mpv (C δ) τ
        = ∑ j ∈ Finset.univ.filter (fun j => ¬ lab j = none),
            α j * mpv (P.basis j) τ := by
      calc ∑ j, ∑ δ, b j δ * mpv (C δ) τ
          = ∑ j, (if lab j = none then 0 else α j * mpv (P.basis j) τ) :=
            Finset.sum_congr rfl fun j _ => hper j τ
        _ = ∑ j, (if ¬ (lab j = none) then α j * mpv (P.basis j) τ else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases h : lab j = none <;> simp [h]
        _ = ∑ j ∈ Finset.univ.filter (fun j => ¬ lab j = none),
              α j * mpv (P.basis j) τ := (Finset.sum_filter _ _).symm
    have h3 : (∑ j ∈ Finset.univ.filter (fun j => lab j = none), α j * mpv (P.basis j) τ)
        + (∑ j ∈ Finset.univ.filter (fun j => ¬ lab j = none), α j * mpv (P.basis j) τ)
        = ∑ j, α j * mpv (P.basis j) τ :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hgoal : ∑ δ, ((∑ j, b j δ) - β δ) * mpv (C δ) τ
        = (∑ δ, (∑ j, b j δ) * mpv (C δ) τ) - ∑ δ, β δ * mpv (C δ) τ := by
      simp [sub_mul, Finset.sum_sub_distrib]
    rw [hgoal, h1, h2, ← hEq τ, ← h3]
    ring
  set g : ({j : Fin P.basisCount // lab j = none}) ⊕ Γ → ℂ :=
    Sum.elim (fun j => α j.1) (fun δ => (∑ j, b j δ) - β δ) with hg
  have hzero : ∑ x, g x • mpvState (d := a) (F x) m = 0 := by
    apply PiLp.ext
    intro τ
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mpvState_apply, WithLp.ofLp_zero, Pi.zero_apply]
    have key : ∀ x, g x * mpv (F x) τ =
        Sum.elim (fun j : {j : Fin P.basisCount // lab j = none} =>
            α j.1 * mpv (P.basis j.1) τ)
          (fun δ : Γ => ((∑ j, b j δ) - β δ) * mpv (C δ) τ) x := by
      rintro (j | δ) <;> rfl
    rw [Finset.sum_congr rfl fun x _ => key x, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun j => lab j = none))
      (fun x => by simp) (fun j => α j * mpv (P.basis j) τ)]
    exact hsplit τ
  have hcoef := Fintype.linearIndependent_iff.1 (hLI m hm) g hzero (Sum.inr γ)
  simp only [hg, Sum.elim_inr, sub_eq_zero] at hcoef
  exact hcoef.symm

/-- A spanning identity at one length transports to any equal length. -/
theorem mpv_span_congr_length {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ]
    {DM : Γ → ℕ} {M : ∀ γ, MPSTensor d (DM γ)} {c : Γ → ℂ} {N N' : ℕ} (h : N = N')
    (hc : ∀ σ : Fin N → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) :
    ∀ σ : Fin N' → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ := by
  subst h; exact hc

/-- A vanishing pointwise combination of matrix product vectors is a vanishing
combination of the corresponding states. -/
theorem sum_smul_mpvState_eq_zero
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} (A : (k : ι) → MPSTensor d (dim k))
    (g : ι → ℂ) {N : ℕ}
    (h : ∀ σ : Fin N → Fin d, ∑ k, g k * mpv (A k) σ = 0) :
    ∑ k, g k • mpvState (d := d) (A k) N = 0 := by
  apply PiLp.ext
  intro σ
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mpvState_apply, WithLp.ofLp_zero, Pi.zero_apply]
  exact h σ

/-- A finite family of nonzero complex weights is reindexed by an initial segment of the
natural numbers without changing its power sums. -/
theorem exists_fin_weights_of_sum_pow
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : ∀ i, w i ≠ 0) :
    ∃ (n : ℕ) (μ : Fin n → ℂ), (∀ k, μ k ≠ 0) ∧
      ∀ m : ℕ, ∑ k, (μ k) ^ m = ∑ i, (w i) ^ m := by
  classical
  refine ⟨Fintype.card ι, fun k => w ((Fintype.equivFin ι).symm k), fun k => hw _, fun m => ?_⟩
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (w i) ^ m)

/-- **Rigidity half of T1 in blocked form.**

For a family of pairwise inequivalent normal tensors `M γ` there are one positive
blocking length `p`, a threshold, and finite multisets of nonzero weights such
that at every blocked length `p * m` past the threshold, any expansion of the
periodic vectors of `B` in the periodic vectors of the family has coefficients
equal to the power sums of those weights.  No spanning hypothesis enters: the
statement is about every expansion that happens to exist. -/
theorem exists_blocking_powerSum_weights
    {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ)) :
    ∃ (p : ℕ) (_ : 0 < p) (N₀ : ℕ) (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      ∀ m : ℕ, N₀ ≤ m → ∀ c : Γ → ℂ,
        (∀ σ : Fin (p * m) → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ m := by
  classical
  have hNe : ∀ γ, NeZero (DM γ) := fun γ => ⟨(hD γ).ne'⟩
  by_cases hNZ : ∃ N : ℕ, 0 < N ∧ ∃ σ : Fin N → Fin d, mpv B σ ≠ 0
  · obtain ⟨p, hp, sB, hsB, P, hCF, hBeq⟩ :=
      exists_isBNTCanonicalForm_afterBlocking_pos_normalized B hNZ
    obtain ⟨C, ξ, hξ, hCmpv, hCLC, hCirr, hCself, hCdist⟩ :=
      exists_blocked_representatives_of_isNormal_distinct M hM hD hdistinct hp
    obtain ⟨lab, sc, N₁, hsc, hsome, hmatch⟩ :=
      exists_matching_data_of_isBNTCanonicalForm hCF C hD hCLC hCirr hCself hCdist
    have hsBC : ((sB : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsB.ne'
    have hpack : ∀ γ : Γ, ∃ (n : ℕ) (μ : Fin n → ℂ), (∀ k, μ k ≠ 0) ∧
        ∀ m : ℕ, ∑ k, (μ k) ^ m
          = ∑ j : Fin P.basisCount, (if lab j = some γ then
              ∑ q : Fin (P.copies j),
                (((sB : ℝ) : ℂ) * P.weight j q * (sc j)⁻¹ * ξ γ) ^ m else 0) := by
      intro γ
      obtain ⟨n, μ, hne, hsum⟩ := exists_fin_weights_of_sum_pow
        (ι := {x : (Σ j : Fin P.basisCount, Fin (P.copies j)) // lab x.1 = some γ})
        (fun x => ((sB : ℝ) : ℂ) * P.weight x.1.1 x.1.2 * (sc x.1.1)⁻¹ * ξ γ)
        (fun x => by
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero hsBC (P.weight_ne_zero _ _)) ?_) (hξ γ)
          exact inv_ne_zero (hsc _))
      refine ⟨n, μ, hne, fun m => ?_⟩
      rw [hsum m]
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun x : (Σ j : Fin P.basisCount, Fin (P.copies j)) =>
          lab x.1 = some γ)) (fun x => by simp)
        (fun x => (((sB : ℝ) : ℂ) * P.weight x.1 x.2 * (sc x.1)⁻¹ * ξ γ) ^ m)]
      rw [Finset.sum_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hlab : lab j = some γ
      · simp [hlab]
      · simp [hlab]
    choose n μ hμne hμsum using hpack
    refine ⟨p, hp, max N₁ 1, n, μ, hμne, ?_⟩
    intro m hm c hc γ
    have hm1 : 0 < m := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N₁ 1) hm)
    have hmN₁ : N₁ ≤ m := le_trans (le_max_left N₁ 1) hm
    have hcflat := mpv_span_congr_length B (Nat.mul_comm p m) hc
    have hblocked : ∀ τ : Fin m → Fin (blockPhysDim d p),
        mpv (blockTensor B p) τ = ∑ δ, c δ * mpv (blockTensor (M δ) p) τ := by
      intro τ
      rw [mpv_blockTensor_eq_mpv_blockedFlatConfig,
        hcflat (blockedFlatConfig (d := d) p τ)]
      exact Finset.sum_congr rfl fun δ _ => by
        rw [mpv_blockTensor_eq_mpv_blockedFlatConfig]
    have hEq : ∀ τ : Fin m → Fin (blockPhysDim d p),
        ∑ j, (((sB : ℝ) : ℂ) ^ m * P.coeff m j) * mpv (P.basis j) τ
          = ∑ δ, (c δ * ((ξ δ) ^ m)⁻¹) * mpv (C δ) τ := by
      intro τ
      have hL : ∑ j, (((sB : ℝ) : ℂ) ^ m * P.coeff m j) * mpv (P.basis j) τ
          = ((sB : ℝ) : ℂ) ^ m * mpv P.toTensor τ := by
        rw [P.mpv_toTensor_eq_sum_coeff τ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hR : ∀ δ : Γ,
          (c δ * ((ξ δ) ^ m)⁻¹) * mpv (C δ) τ = c δ * mpv (blockTensor (M δ) p) τ := by
        intro δ
        have hne : (ξ δ) ^ m ≠ 0 := pow_ne_zero m (hξ δ)
        rw [hCmpv δ m τ]
        field_simp
      calc ∑ j, (((sB : ℝ) : ℂ) ^ m * P.coeff m j) * mpv (P.basis j) τ
          = ((sB : ℝ) : ℂ) ^ m * mpv P.toTensor τ := hL
        _ = mpv (blockTensor B p) τ := (hBeq m hm1 τ).symm
        _ = ∑ δ, c δ * mpv (blockTensor (M δ) p) τ := hblocked τ
        _ = ∑ δ, (c δ * ((ξ δ) ^ m)⁻¹) * mpv (C δ) τ :=
            (Finset.sum_congr rfl fun δ _ => hR δ).symm
    have hcoef := hmatch m hmN₁ (fun j => ((sB : ℝ) : ℂ) ^ m * P.coeff m j)
      (fun δ => c δ * ((ξ δ) ^ m)⁻¹) hEq γ
    have hξm : (ξ γ) ^ m ≠ 0 := pow_ne_zero m (hξ γ)
    have hc_eq : c γ = ((ξ γ) ^ m) * ∑ j, (if lab j = some γ then
        (((sB : ℝ) : ℂ) ^ m * P.coeff m j) * ((sc j) ^ m)⁻¹ else 0) := by
      rw [← hcoef]
      field_simp
    rw [hμsum γ m, hc_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hlab : lab j = some γ
    · simp only [hlab, reduceIte]
      rw [P.coeff_eq_sum_weight_pow m j]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_pow, mul_pow, mul_pow, inv_pow]
      ring
    · simp [hlab]
  · push Not at hNZ
    choose Mc ζ hζ hGauge hMpv hLC hNT using
      fun γ => exists_leftCanonical_normalTensor_scale_of_isNormal (hM γ)
    have hMcDistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (Mc γ)) (Mc δ) := by
      intro γ δ hne h hGPE
      exact hdistinct γ δ hne h
        (gaugePhaseEquiv_of_smul_smul_cast h (hζ γ) (hζ δ)
          (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGauge γ) hGPE (hGauge δ)))
    obtain ⟨N₀, hLI⟩ :=
      exists_eventually_linearIndependent_of_normalTensor_distinct Mc hNT hMcDistinct
    refine ⟨1, Nat.one_pos, N₀ + 1, fun _ => 0, fun _ => Fin.elim0,
      fun γ k => k.elim0, ?_⟩
    intro m hm c hc γ
    have hm1 : 0 < m := by omega
    have hc1 := mpv_span_congr_length B (one_mul m) hc
    have hzero : ∀ τ : Fin m → Fin d,
        ∑ δ, (c δ * ((ζ δ) ^ m)⁻¹) * mpv (Mc δ) τ = 0 := by
      intro τ
      have hB0 : (0 : ℂ) = ∑ δ, c δ * mpv (M δ) τ := by
        rw [← hc1 τ, hNZ m hm1 τ]
      rw [← hB0.symm]
      refine Finset.sum_congr rfl fun δ _ => ?_
      have hne : (ζ δ) ^ m ≠ 0 := pow_ne_zero m (hζ δ)
      rw [hMpv δ m τ]
      field_simp
    have hcoef := Fintype.linearIndependent_iff.1 (hLI m (by omega))
      (fun δ => c δ * ((ζ δ) ^ m)⁻¹)
      (sum_smul_mpvState_eq_zero Mc (fun δ => c δ * ((ζ δ) ^ m)⁻¹) hzero) γ
    have hζm : (ζ γ) ^ m ≠ 0 := pow_ne_zero m (hζ γ)
    have : c γ = 0 := by
      field_simp at hcoef
      simpa using hcoef
    simp [this]

/-- **T1, blocked form: length-dependent coefficients are power sums.**

If the periodic vectors of `B` lie, at every positive length, in the span of the
periodic vectors of a family of pairwise inequivalent normal tensors `M γ`, then
along the lengths `p * m` of one fixed blocking the coefficients are uniquely
determined and equal the power sums of finite multisets of nonzero weights.

The first conclusion is rigidity: any expansion at a blocked length past the
threshold has exactly these coefficients.  The second is the matching expansion
itself, which the spanning hypothesis supplies. -/
theorem exists_blocking_powerSum_coeff
    {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ) :
    ∃ (p : ℕ) (_ : 0 < p) (N₀ : ℕ) (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      (∀ m : ℕ, N₀ ≤ m → ∀ c : Γ → ℂ,
        (∀ σ : Fin (p * m) → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ m) ∧
      (∀ m : ℕ, N₀ ≤ m → ∀ σ : Fin (p * m) → Fin d,
        mpv B σ = ∑ γ, (∑ k, (μ γ k) ^ m) * mpv (M γ) σ) := by
  obtain ⟨p, hp, N₀, n, μ, hμne, huniq⟩ :=
    exists_blocking_powerSum_weights B M hM hD hdistinct
  refine ⟨p, hp, max N₀ 1, n, μ, hμne, fun m hm c hc γ =>
    huniq m (le_trans (le_max_left _ _) hm) c hc γ, ?_⟩
  intro m hm σ
  have hpos : 0 < p * m :=
    Nat.mul_pos hp (lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N₀ 1) hm))
  obtain ⟨c, hc⟩ := hspan (p * m) hpos
  rw [hc σ]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [huniq m (le_trans (le_max_left N₀ 1) hm) c hc γ]

end MPSTensor
