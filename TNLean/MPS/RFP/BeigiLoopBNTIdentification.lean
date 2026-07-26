/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.BNT.Basic
import TNLean.MPS.Overlap.NormalTensorDichotomy
import TNLean.MPS.RFP.BeigiLoopFixedPoint
import TNLean.MPS.RFP.BeigiSectorGraphConstruction
import TNLean.MPS.RFP.StructuralForm
import TNLean.Wielandt.Primitivity.Equivalence

/-!
# Identification of Beigi loop sectors with normal tensors

This file develops the normal-tensor comparison needed to identify the loop-product ground
states in Beigi's classification with the basis of normal tensors of a matrix product state.

The conversion lemma below relates the project's algebraic normality predicate to the spectral
normal-tensor predicate of Cirac--Pérez-García--Schuch--Verstraete. It is an input to the
identification asserted in arXiv:1606.00608, line 1307. Its primitive-transfer ingredient is
the equivalence between eventual full Kraus rank and strong irreducibility in
arXiv:0909.5347, Proposition 3, together with the Perron--Frobenius theorem for irreducible
completely positive maps (Wolf, Theorem 6.3). The companion conversion from an algebraically
normal left-canonical tensor is `isNormalTensor_of_isNormal_leftCanonical` in
`TNLean/MPS/CanonicalForm/NormalTensorGauge.lean`.
-/

open scoped Matrix BigOperators ComplexOrder
open FiniteWeightedDigraph

namespace MPSTensor

variable {d D : ℕ}

/-- A transfer-idempotent algebraically normal tensor is a spectrally normalized normal tensor.

Algebraic normality gives irreducibility by arXiv:0909.5347, Proposition 3. Wolf's
Perron--Frobenius theorem (Theorem 6.3) supplies a positive-definite eigenvector with positive
eigenvalue. Transfer idempotence forces that eigenvalue, and every nonzero eigenvalue, to be
one. The spectral normalization of arXiv:1606.00608, lines 224--235, is therefore trivial.
This conversion applies in particular to the loop tensors used in the BNT identification at
arXiv:1606.00608, line 1307.
-/
theorem isNormalTensor_of_isNormal_isTransferIdempotent [NeZero D]
    (A : MPSTensor d D) (hNormal : IsNormal A)
    (hRFP : IsTransferIdempotent A) : IsNormalTensor A := by
  have hInjective : IsInjective A := rfp_nt_structural A hNormal hRFP
  have hIrr : IsIrreducibleTensor A :=
    isIrreducibleTensor_of_isPrimitivePaper A (isPrimitivePaper_of_isNormal A hNormal)
  have hApply : ∃ i, A i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hOne : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
        Submodule.span ℂ (Set.range A) := by
      rw [hInjective]
      exact Submodule.mem_top
    have hle : Submodule.span ℂ (Set.range A) ≤ ⊥ :=
      Submodule.span_le.mpr fun X hX => by
        obtain ⟨i, rfl⟩ := hX
        simp [hzero i]
    have hOneZero : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      simpa using hle hOne
    have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
    let i : Fin D := ⟨0, hD⟩
    have := congrFun (congrFun hOneZero i) i
    simp [i] at this
  obtain ⟨ρ, r, hρ, hr, hρeig⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible A hIrr hApply
  have hρne : ρ ≠ 0 := (Matrix.PosDef.isUnit hρ).ne_zero
  have hIdemρ : transferMap A (transferMap A ρ) = transferMap A ρ := by
    exact DFunLike.congr_fun hRFP ρ
  have hrIdem : (r : ℂ) * (r : ℂ) = (r : ℂ) := by
    have hzero : (((r : ℂ) * (r : ℂ) - (r : ℂ)) • ρ) = 0 := by
      calc
        (((r : ℂ) * (r : ℂ) - (r : ℂ)) • ρ) =
            ((r : ℂ) * (r : ℂ)) • ρ - (r : ℂ) • ρ := by
              rw [sub_smul]
        _ = transferMap A (transferMap A ρ) - transferMap A ρ := by
              rw [hρeig, map_smul, hρeig, smul_smul]
        _ = 0 := sub_eq_zero.mpr hIdemρ
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hρne)
  have hrOneComplex : (r : ℂ) = 1 := by
    have hrne : (r : ℂ) ≠ 0 := by
      exact_mod_cast hr.ne'
    apply mul_left_cancel₀ hrne
    simpa only [mul_one] using hrIdem
  have hrOne : r = 1 := by
    exact_mod_cast hrOneComplex
  subst r
  have huniq : ∀ μ : ℂ, Module.End.HasEigenvalue (transferMap A) μ →
      ‖μ‖ = (1 : ℝ) → μ = (1 : ℂ) := by
    intro μ hμ hμnorm
    obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
    have hXeq : transferMap A X = μ • X :=
      Module.End.mem_eigenspace_iff.mp (Module.End.hasEigenvector_iff.mp hX).1
    have hXne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
    have hIdemX : transferMap A (transferMap A X) = transferMap A X := by
      exact DFunLike.congr_fun hRFP X
    have hμIdem : μ * μ = μ := by
      have hzero : ((μ * μ - μ) • X) = 0 := by
        calc
          ((μ * μ - μ) • X) = (μ * μ) • X - μ • X := by rw [sub_smul]
          _ = transferMap A (transferMap A X) - transferMap A X := by
                rw [hXeq, map_smul, hXeq, smul_smul]
          _ = 0 := sub_eq_zero.mpr hIdemX
      exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hXne)
    have hμne : μ ≠ 0 := by
      intro hzero
      subst μ
      norm_num at hμnorm
    apply mul_left_cancel₀ hμne
    simpa only [mul_one] using hμIdem
  have hScaled : IsNormalTensor (fun i =>
      (((Real.sqrt (1 : ℝ) : ℝ) : ℂ))⁻¹ • A i) :=
    isNormalTensor_invSqrt_smul_of_unique_peripheral A hIrr ρ 1 hρ (by norm_num)
      (by simpa using hρeig) huniq
  simpa using hScaled

/-- Two normal tensors which are not MPV-phase equivalent have asymptotically vanishing
overlap. -/
private lemma overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNormalTensor A) (hB : IsNormalTensor B)
    (hNot : ¬ MPVBlockPhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  rcases hA.mpv_phase_alternative hB with hZero | ⟨ζ, hζ, hState⟩
  · exact hZero
  · exfalso
    apply hNot
    refine ⟨ζ, Complex.ne_zero_of_norm_eq_one hζ, ?_⟩
    intro N _hN σ
    have hEq := congrArg (fun v : MPVSpace d N => v σ) (hState N)
    simpa [mpvState_apply, PiLp.smul_apply, smul_eq_mul] using hEq

/-- Eventual containment in a finite asymptotically orthonormal family of normal MPV states
forces phase equivalence with one member of the family.

The normal-tensor hypotheses are those of arXiv:1606.00608, lines 231--235. If no member were
MPV-phase equivalent to `A`, Corollary `eqV` (lines 1121--1128) would make every mixed overlap
with `A` tend to zero. Adjoining `A` to the given asymptotically orthonormal family would then
produce an eventually linearly independent family, contradicting the assumed span containment.
This is the finite-family argument underlying the BNT identification used at
arXiv:1606.00608, line 1307; algebraic normal tensors enter that application through quantum
Wielandt Proposition 3 (arXiv:0909.5347) and Wolf, Theorem 6.3.
-/
theorem exists_mpvBlockPhaseEquiv_of_mem_span_eventually
    {D₀ : ℕ} [NeZero D₀]
    {A : MPSTensor d D₀} (hA : IsNormalTensor A)
    {ι : Type*} [Finite ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (B : (j : ι) → MPSTensor d (dim j))
    (hB : ∀ j, IsNormalTensor (B j))
    (hBCross : ∀ i j, i ≠ j →
      Filter.Tendsto (fun N => mpvOverlap (d := d) (B i) (B j) N)
        Filter.atTop (nhds 0))
    (hMem : ∀ᶠ N in Filter.atTop,
      mpvState (d := d) A N ∈
        Submodule.span ℂ (Set.range fun j : ι => mpvState (d := d) (B j) N)) :
    ∃ j, MPVBlockPhaseEquiv A (B j) := by
  classical
  by_contra hNo
  push Not at hNo
  let C :
      (x : Option ι) → MPSTensor d (Option.rec D₀ dim x) :=
    fun x => Option.rec A B x
  have hSelf : ∀ x,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (C x) (C x) N)
        Filter.atTop (nhds (1 : ℂ)) := by
    intro x
    cases x with
    | none => simpa [C] using hA.selfOverlap_tendsto_one
    | some j => simpa [C] using (hB j).selfOverlap_tendsto_one
  have hCross : ∀ x y, x ≠ y →
      Filter.Tendsto (fun N => mpvOverlap (d := d) (C x) (C y) N)
        Filter.atTop (nhds (0 : ℂ)) := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => exact (hxy rfl).elim
        | some j =>
            simpa [C] using
              overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv hA (hB j) (hNo j)
    | some i =>
        cases y with
        | none =>
            simpa [C] using
              tendsto_mpvOverlap_zero_swap A (B i)
                (overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv hA (hB i) (hNo i))
        | some j =>
            have hij : i ≠ j := by
              intro hij
              exact hxy (congrArg some hij)
            simpa [C] using hBCross i j hij
  have hLI : ∀ᶠ N in Filter.atTop,
      LinearIndependent ℂ (fun x : Option ι => mpvState (d := d) (C x) N) :=
    eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal C hSelf hCross
  obtain ⟨NLI, hNLI⟩ := Filter.eventually_atTop.1 hLI
  obtain ⟨NMem, hNMem⟩ := Filter.eventually_atTop.1 hMem
  let N := max NLI NMem
  have hLIN := hNLI N (Nat.le_max_left NLI NMem)
  have hNmem := hNMem N (Nat.le_max_right NLI NMem)
  have hNotMem : mpvState (d := d) A N ∉
      Submodule.span ℂ (Set.range fun j : ι => mpvState (d := d) (B j) N) := by
    simpa [C, Function.comp_def] using (linearIndependent_option.mp hLIN).2
  exact hNotMem hNmem

/-- Multiplication of every tensor letter by a unit phase leaves the transfer map unchanged.

The transfer map scales by `ζ * star ζ`, which is one when `‖ζ‖ = 1`. This is the
normalization-sensitive scalar step in the BNT identification at arXiv:1606.00608, line 1307;
the spectral normalization is that of lines 224--235, obtained from quantum Wielandt
Proposition 3 (arXiv:0909.5347) and Wolf, Theorem 6.3.
-/
theorem transferMap_smul_eq_of_norm_eq_one
    (A : MPSTensor d D) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    transferMap (fun i => ζ • A i) = transferMap A := by
  have hstar : starRingEnd ℂ ζ * ζ = 1 := by
    simpa [Complex.normSq_eq_norm_sq, hζ] using
      (Complex.normSq_eq_conj_mul_self (z := ζ)).symm
  have hphase : ζ * starRingEnd ℂ ζ = 1 := by
    rw [mul_comm, hstar]
  apply LinearMap.ext
  intro X
  rw [transferMap_smul, hphase, one_smul]

/-- An explicit unit-phase gauge relation transports transfer idempotence.

Virtual conjugation preserves the physical blocking relation, hence transfer idempotence, and
unit-phase multiplication leaves the transfer map unchanged. This is the covariance needed for
the BNT identification at arXiv:1606.00608, line 1307. The unit normalization is the normal-tensor
normalization of lines 224--235, related to algebraic normality by quantum Wielandt Proposition 3
(arXiv:0909.5347) and Wolf, Theorem 6.3.
-/
theorem isTransferIdempotent_of_unit_gaugePhase
    (A B : MPSTensor d D) (X : GL (Fin D) ℂ) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hrel : ∀ i, B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
      (↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ)))
    (hRFP : IsTransferIdempotent A) : IsTransferIdempotent B := by
  let C : MPSTensor d D := fun i =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      (↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ)
  have hGauge : GaugeEquiv A C := ⟨X, fun _ => rfl⟩
  have hCRFP : IsTransferIdempotent C := hGauge.isTransferIdempotent_iff.mp hRFP
  have hTensor : B = fun i => ζ • C i := by
    funext i
    simpa [C] using hrel i
  have hMap : transferMap B = transferMap C := by
    rw [hTensor]
    exact transferMap_smul_eq_of_norm_eq_one C ζ hζ
  rw [IsTransferIdempotent, hMap]
  exact hCRFP

/-- Transport across an equality of bond dimensions preserves transfer idempotence.

This isolates the dependent cast used in the BNT identification at arXiv:1606.00608,
line 1307. The surrounding normal-tensor normalization is that of lines 224--235 and is
related to algebraic normality by quantum Wielandt Proposition 3 (arXiv:0909.5347) and
Wolf, Theorem 6.3.
-/
theorem isTransferIdempotent_cast_iff
    {D₁ D₂ : ℕ} (hdim : D₁ = D₂) (A : MPSTensor d D₁) :
    IsTransferIdempotent (cast (congr_arg (MPSTensor d) hdim) A) ↔
      IsTransferIdempotent A := by
  subst D₂
  rfl

/-- Gauge-phase equivalence between normal tensors transports transfer idempotence.

For spectrally normalized normal tensors, the scalar in a gauge-phase relation has unit norm by
the self-overlap normalization of arXiv:1606.00608, Lemma `equalMPS`, lines 1080--1097. The
preceding unit-phase covariance therefore applies. This is the form needed in the BNT
identification at arXiv:1606.00608, line 1307. Algebraic normality reaches these hypotheses by
quantum Wielandt Proposition 3 (arXiv:0909.5347), Wolf, Theorem 6.3, and the spectral
normalization of arXiv:1606.00608, lines 224--235.
-/
theorem GaugePhaseEquiv.isTransferIdempotent [NeZero D]
    {A B : MPSTensor d D} (h : GaugePhaseEquiv A B)
    (hA : IsNormalTensor A) (hB : IsNormalTensor B)
    (hRFP : IsTransferIdempotent A) : IsTransferIdempotent B := by
  obtain ⟨X, ζ, _hζ, hrel⟩ := h
  have hζnorm : ‖ζ‖ = 1 :=
    norm_eq_one_of_gaugePhase_cast_of_isNormalTensor hA hB rfl (by simpa using hrel)
  exact isTransferIdempotent_of_unit_gaugePhase A B X ζ hζnorm hrel hRFP

/-- Eventual constancy of the Euclidean parent-ground-space dimension under the algebraic BNT
and all-chain NNCPH hypotheses. -/
private theorem eventually_parentHamiltonianGroundSpaceES_finrank_eq_of_isBNT
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {B : MPSTensor d D} (hBNT : IsBNT B r dim A)
    (hNNCPH : HasNNCPHGroundSpaces B A) :
    ∃ c N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      Module.finrank ℂ (parentHamiltonianGroundSpaceES B 2 N) = c := by
  obtain ⟨N₀, hLI⟩ := hBNT.eventually_li
  refine ⟨r, max N₀ 2, ?_⟩
  intro N hN
  have hN₀ : N₀ < N := lt_of_le_of_lt (Nat.le_max_left N₀ 2) hN
  have hTwo : 2 < N := lt_of_le_of_lt (Nat.le_max_right N₀ 2) hN
  have hImage : LinearIndependent ℂ
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap ∘
        fun j : Fin r => (mpv (A j) : NSiteSpace d N)) := by
    convert hLI N hN₀ using 1
    funext j
    ext σ
    simp [Function.comp_apply, mpvState_apply]
  have hCoefficients : LinearIndependent ℂ
      (fun j : Fin r => (mpv (A j) : NSiteSpace d N)) :=
    LinearIndependent.of_comp
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap hImage
  rw [BeigiSectorGraphData.parentHamiltonianGroundSpaceES_finrank_eq_ker,
    (hNNCPH N hTwo).groundSpaceSpanning, bntMPSVectorSpan]
  simpa using finrank_span_eq_card hCoefficients

/-- The normalized minimal loop MPV state is the corresponding Euclidean loop-product state
times the inverse bond norm at every site. -/
private theorem BeigiSectorGraphData.mpvState_normalizedMinimalLoopTensor
    {A : MPSTensor d D} (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} [NeZero N] :
    mpvState (d := d) (F.normalizedMinimalLoopTensor l) N =
      (((F.loopBondNorm l : ℂ)⁻¹) ^ N) • F.loopProductStateES l := by
  apply PiLp.ext
  intro s
  change mpv (F.normalizedMinimalLoopTensor l) s =
    ((F.loopBondNorm l : ℂ)⁻¹) ^ N * F.loopProductState l s
  exact F.mpv_normalizedMinimalLoopTensor l s

/-- Distinct normalized minimal loop tensors have vanishing overlap at every positive length,
and hence asymptotically. -/
private theorem BeigiSectorGraphData.normalizedMinimalLoopTensor_overlap_tendsto_zero
    {A : MPSTensor d D} (F : BeigiSectorGraphData A) {l m : Loop F.edgeWeight}
    (hlm : l ≠ m) :
    Filter.Tendsto
      (fun N => mpvOverlap (d := d) (F.normalizedMinimalLoopTensor l)
        (F.normalizedMinimalLoopTensor m) N)
      Filter.atTop (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  refine (Filter.eventually_gt_atTop 0).mono ?_
  intro N hN
  letI : NeZero N := ⟨hN.ne'⟩
  symm
  change mpvOverlap (d := d) (F.normalizedMinimalLoopTensor l)
    (F.normalizedMinimalLoopTensor m) N = 0
  rw [mpvOverlap_eq_star_mpvInner, mpvInner,
    F.mpvState_normalizedMinimalLoopTensor l,
    F.mpvState_normalizedMinimalLoopTensor m]
  simp [F.loopProductStateES_inner_eq_zero_of_ne hlm]

/-- The periodic MPV state of the NNCPH tensor eventually belongs to the span of the normalized
minimal loop MPV states. -/
private theorem BeigiSectorGraphData.eventually_mpvState_mem_span_normalizedMinimalLoopTensor
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {B : MPSTensor d D} (F : BeigiSectorGraphData B)
    (hparent : ∃ c N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      Module.finrank ℂ (parentHamiltonianGroundSpaceES B 2 N) = c)
    (hNNCPH : HasNNCPHGroundSpaces B A) :
    ∀ᶠ N in Filter.atTop,
      mpvState (d := d) B N ∈
        Submodule.span ℂ (Set.range fun l : Loop F.edgeWeight =>
          mpvState (d := d) (F.normalizedMinimalLoopTensor l) N) := by
  refine Filter.eventually_atTop.mpr ⟨3, ?_⟩
  intro N hN
  have hTwo : 2 < N := by omega
  letI : NeZero N := ⟨by omega⟩
  have hGround : mpvState (d := d) B N ∈ parentHamiltonianGroundSpaceES B 2 N := by
    rw [parentHamiltonianGroundSpaceES, Submodule.mem_map]
    refine ⟨(mpv B : NSiteSpace d N), ?_, rfl⟩
    rw [LinearMap.mem_ker, parentHamiltonian]
    rw [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _hi
    exact (hNNCPH N hTwo).isFrustrationFree i
  have hLoopSpan := F.span_loopProductStateES_eq_parentHamiltonianGroundSpaceES hparent hTwo
  have hInLoopSpan : mpvState (d := d) B N ∈
      Submodule.span ℂ
        (Set.range fun l : Loop F.edgeWeight => F.loopProductStateES l) := by
    rw [hLoopSpan]
    exact hGround
  apply (Submodule.span_le.mpr ?_) hInLoopSpan
  rintro _ ⟨l, rfl⟩
  let c : ℂ := ((F.loopBondNorm l : ℂ)⁻¹) ^ N
  have hc : c ≠ 0 := by
    exact pow_ne_zero N (inv_ne_zero (Complex.ofReal_ne_zero.mpr (F.loopBondNorm_ne_zero l)))
  have hNormalized : mpvState (d := d) (F.normalizedMinimalLoopTensor l) N ∈
      Submodule.span ℂ (Set.range fun k : Loop F.edgeWeight =>
        mpvState (d := d) (F.normalizedMinimalLoopTensor k) N) :=
    Submodule.subset_span ⟨l, rfl⟩
  have hScaled := Submodule.smul_mem
    (Submodule.span ℂ (Set.range fun k : Loop F.edgeWeight =>
      mpvState (d := d) (F.normalizedMinimalLoopTensor k) N)) c⁻¹ hNormalized
  have hEq : F.loopProductStateES l =
      c⁻¹ • mpvState (d := d) (F.normalizedMinimalLoopTensor l) N := by
    rw [F.mpvState_normalizedMinimalLoopTensor l, smul_smul, inv_mul_cancel₀ hc, one_smul]
  change F.loopProductStateES l ∈
    Submodule.span ℂ (Set.range fun k : Loop F.edgeWeight =>
      mpvState (d := d) (F.normalizedMinimalLoopTensor k) N)
  rw [hEq]
  exact hScaled

/-- All-chain nearest-neighbor commuting parent-Hamiltonian ground spaces imply transfer
idempotence for a normal left-canonical representative.

The all-chain NNCPH hypotheses give Beigi's finite sector graph, whose positive loops span the
parent ground space. The normalized minimal loop tensors are normal fixed points. The finite
normal-family span argument therefore matches the original tensor to one loop tensor by a unit
phase and an invertible virtual gauge, which transports transfer idempotence.

Source: CPSV16, proof of Theorem 3.10 at line 1307; Beigi,
arXiv:1105.1019v2, Sections III--IV; algebraic-to-spectral normality uses quantum Wielandt
Proposition 3 (arXiv:0909.5347) and Wolf, Theorem 6.3.

**Scope restriction (normal representative):** CPSV16, Theorem 3.10 is stated for a tensor in
canonical form. This theorem proves its reverse implication for one explicitly normal and
left-canonical representative, together with an explicit BNT relation and the all-chain
ground-space condition. It does not assert the unrestricted canonical-form theorem. This
restriction is documented in `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.
-/
theorem nncph_implies_rfp
    (B : MPSTensor d D) [NeZero D]
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j))
    (hBNT : IsBNT B r dim A)
    (hNNCPH : HasNNCPHGroundSpaces B A)
    (hNT : IsNormal B) (hLeft : IsLeftCanonical B) :
    IsTransferIdempotent B := by
  classical
  have hNNCPH3 : IsNNCPH B 3 := (hNNCPH 3 (by omega)).isNNCPH
  let F : BeigiSectorGraphData B := hNNCPH3.beigiSectorGraphData
  letI : ∀ l : Loop F.edgeWeight, NeZero (F.loopSchmidtRank l) :=
    fun l => ⟨(F.loopSchmidtRank_pos l).ne'⟩
  have hBNormal : IsNormalTensor B :=
    isNormalTensor_of_isNormal_leftCanonical B hNT hLeft
  have hLoopNormal : ∀ l : Loop F.edgeWeight,
      IsNormalTensor (F.normalizedMinimalLoopTensor l) := by
    intro l
    exact isNormalTensor_of_isNormal_isTransferIdempotent
      (F.normalizedMinimalLoopTensor l)
      (F.normalizedMinimalLoopTensor_isNormal l)
      (F.normalizedMinimalLoopTensor_isTransferIdempotent l)
  have hparent :=
    eventually_parentHamiltonianGroundSpaceES_finrank_eq_of_isBNT hBNT hNNCPH
  have hMem := F.eventually_mpvState_mem_span_normalizedMinimalLoopTensor hparent hNNCPH
  have hCross : ∀ l m : Loop F.edgeWeight, l ≠ m →
      Filter.Tendsto
        (fun N => mpvOverlap (d := d) (F.normalizedMinimalLoopTensor l)
          (F.normalizedMinimalLoopTensor m) N)
        Filter.atTop (nhds 0) := by
    intro l m hlm
    exact F.normalizedMinimalLoopTensor_overlap_tendsto_zero hlm
  obtain ⟨l, hPhase⟩ :=
    exists_mpvBlockPhaseEquiv_of_mem_span_eventually hBNormal
      F.normalizedMinimalLoopTensor hLoopNormal hCross hMem
  obtain ⟨hdim, hGaugePhase⟩ :=
    hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor hBNormal (hLoopNormal l)
  have hBCastNormal :
      IsNormalTensor (cast (congr_arg (MPSTensor d) hdim) B) :=
    (isNormalTensor_cast_iff hdim B).2 hBNormal
  have hBCastRFP :
      IsTransferIdempotent (cast (congr_arg (MPSTensor d) hdim) B) :=
    (gaugePhaseEquiv_symm_same_dim hGaugePhase).isTransferIdempotent
      (hLoopNormal l) hBCastNormal
      (F.normalizedMinimalLoopTensor_isTransferIdempotent l)
  exact (isTransferIdempotent_cast_iff hdim B).1 hBCastRFP

end MPSTensor
