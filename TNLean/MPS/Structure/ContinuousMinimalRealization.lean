/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ContinuousIdempotentFrames
import TNLean.MPS.Structure.ContinuousTraceQuotientPrimitive
import TNLean.MPS.Structure.ContinuousFramedLeftIdealAction
import TNLean.MPS.Structure.ContinuousTraceQuotientLetters
import TNLean.MPS.Structure.NormalizedTraceQuotientLetters
import TNLean.MPS.Symmetry.PositiveRayFiniteTraceData
import TNLean.MPS.Symmetry.ExactMPSPhaseGaugeInvariance

/-!
# Continuous realization of finite-ring trace quotients

A local continuous primitive idempotent supplies a principal left ideal of the
minimal bond dimension. Continuous frames and their Gram left inverses represent
the recovered quotient letters by continuous matrices. Pointwise matrix-algebra
identifications show that these matrices are gauge equivalent to the normalized
minimal tensor. The pointwise tensor and the identifying gauges need not be
continuous.

**Scope restriction (constant minimal dimension):** This is an auxiliary
construction at constant positive minimal dimension for arXiv:1010.3732,
Section II.F.2, lines 953–993. The remaining change-of-dimension problem is
recorded in `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
Proportionality of two-site and
three-site vectors alone does not identify all positive-length MPS rays of a raw
tensor. Such a conclusion requires full positive-ray equality separately.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder BigOperators Topology

namespace MPSTensor

private theorem exists_local_continuous_leftIdealLetters
    {T : Type*} [TopologicalSpace T] {d r D : ℕ} [NeZero D]
    (μ : T → (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (M : T → Matrix (Fin r) (Fin r × Fin r) ℂ) (hM : Continuous M)
    (hμ : ∀ t x y, μ t x y = M t *ᵥ (fun ab => x ab.1 * y ab.2))
    (p : T → Fin r → ℂ)
    (R : T → Matrix (Fin r) (Fin r) ℂ) (hR : Continuous R)
    (hRdef : ∀ t, R t = LinearMap.toMatrix' ((μ t).flip (p t)))
    (hIdem : ∀ t, IsIdempotentElem (R t))
    (q : T → Fin d → Fin r → ℂ) (hq : Continuous q)
    (A : T → MPSTensor d D) (hA : ∀ t, Kraus.IsInjective (A t))
    (κ : T → ℂ) (hκ : ∀ t, κ t ≠ 0)
    (E : T → (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ t x y, E t (μ t x y) = E t x * E t y)
    (hLetters : ∀ t i, E t (q t i) = κ t • A t i)
    (t₀ : T) (hRank : (R t₀).rank = D) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ∃ C : T → MPSTensor d D,
      ContinuousOn C S ∧ ∀ t ∈ S, GaugeEquiv (κ t • A t) (C t) ∧ Kraus.IsInjective (C t) := by
  classical
  obtain ⟨S, hS, ht₀, F, J, H, hJ, hH, hFrame⟩ :=
    Matrix.exists_local_continuous_rangeFrame_of_idempotent R hR hIdem t₀ hRank
  let L : S → MPSTensor d D := fun t i =>
    Matrix.leftIdealFrameAction (μ t) (J t).mulVecLin (H t).mulVecLin (q t i)
  have hL : Continuous L := continuous_pi fun i => continuousOn_univ.mp
    (Matrix.continuousOn_leftIdealFrameAction Set.univ
      (fun t : S => μ t) (fun t : S => M t)
      (hM.comp continuous_subtype_val).continuousOn (fun t x y => hμ t x y)
      J hJ.continuousOn H hH.continuousOn (fun t : S => q t i)
      (((continuous_apply i).comp (hq.comp continuous_subtype_val)).continuousOn))
  have hHJ : ∀ t : S, (H t).mulVecLin.comp (J t).mulVecLin = LinearMap.id := by
    intro t
    rw [← Matrix.mulVecLin_mul, (hFrame t).2.2.2.2.1, Matrix.mulVecLin_one]
  have hRange : ∀ t : S, LinearMap.range (J t).mulVecLin =
      LinearMap.range ((μ t).flip (p t)) := by
    intro t
    rw [(hFrame t).2.2.2.1, hRdef, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hGauge : ∀ t : S, GaugeEquiv (κ t • A t) (L t) := by
    intro t
    have hCompare : (fun i => E t (q t i)) = κ t • A t := by
      funext i
      exact hLetters t i
    exact hCompare ▸ gaugeEquiv_leftIdealFrameAction
      (μ t) (E t) (hE t) (p t) (J t).mulVecLin (H t).mulVecLin
      (hHJ t) (hRange t) (q t)
  let C : T → MPSTensor d D := fun t => if ht : t ∈ S then L ⟨t, ht⟩ else 0
  have hC : ContinuousOn C S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hL.congr (fun t => by simp only [Set.domRestrict_apply, C, dite_eq_left t.property])
  refine ⟨S, hS, ht₀, C, hC, ?_⟩
  intro t ht
  simpa only [C, dite_eq_left ht] using
    (show GaugeEquiv (κ t • A t) (L ⟨t, ht⟩) ∧ Kraus.IsInjective (L ⟨t, ht⟩) from
      ⟨hGauge ⟨t, ht⟩, isInjective_of_gaugeEquiv ((hA t).smul (hκ t)) (hGauge ⟨t, ht⟩)⟩)

/-- Continuous raw tensors with injective pointwise realizations of a fixed positive
bond dimension admit a local continuous injective realization. The constructed tensor
is gauge equivalent pointwise to the scalar α₃/α₂ times the supplied minimal tensor.
Neither that tensor nor its scalar normalization is assumed continuous. This conclusion
does not identify the longer rays of the raw tensor from its two- and three-site data.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem exists_local_continuous_minimalTensor_of_two_three_trace_eq
    {T : Type*} [TopologicalSpace T] {d D K : ℕ} [NeZero D]
    (B : T → MPSTensor d K) (hB : Continuous B)
    (A : T → MPSTensor d D) (hA : ∀ t, Kraus.IsInjective (A t))
    (α₂ α₃ : T → ℂ) (hα₂ : ∀ t, α₂ t ≠ 0) (hα₃ : ∀ t, α₃ t ≠ 0)
    (hPair : ∀ t i j, Matrix.trace (B t i * B t j) =
      α₂ t * Matrix.trace (A t i * A t j))
    (hTriple : ∀ t i k j, Matrix.trace (B t i * B t k * B t j) =
      α₃ t * Matrix.trace (A t i * A t k * A t j)) (t₀ : T) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ∃ C : T → MPSTensor d D,
      ContinuousOn C S ∧ ∀ t ∈ S,
        GaugeEquiv ((α₃ t / α₂ t) • A t) (C t) ∧ Kraus.IsInjective (C t) := by
  classical
  let G : T → Matrix (Fin d) (Fin d) ℂ :=
    fun t j i => Matrix.trace (B t i * B t j)
  obtain ⟨F, S₀, u, p, hS₀, ht₀, hM, hu, hp, hR, hPrimitive⟩ :=
    Matrix.exists_local_continuous_traceQuotientPrimitive B hB G (fun _ _ _ => rfl)
      (fun _ => D) (fun _ => rfl) A hA α₂ α₃ hα₂ hα₃ hPair hTriple t₀ (NeZero.pos D)
  let M : T → Matrix (Fin (D * D)) (Fin (D * D) × Fin (D * D)) ℂ :=
    fun t => Matrix.traceQuotientProductCoordinates (G t) F
      (Matrix.traceQuotientTripleColumns (B t) F)
  let μ : T → (Fin (D * D) → ℂ) →ₗ[ℂ]
      (Fin (D * D) → ℂ) →ₗ[ℂ] (Fin (D * D) → ℂ) :=
    fun t => Matrix.toLinearMap₂' ℂ (Matrix.of fun a b i => M t i (a, b))
  replace hPrimitive : ∀ t : S₀,
      μ t (p t) (p t) = p t ∧
      (LinearMap.toMatrix' ((μ t).flip (p t))).rank = D ∧
      ∃ E : (Fin (D * D) → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
        (∀ x, E x = (α₃ t / α₂ t) • Fintype.linearCombination ℂ (A t) (F *ᵥ x)) ∧
        (∀ x y, E (μ t x y) = E x * E y) ∧
        (∀ x y z, μ t (μ t x y) z = μ t x (μ t y z)) :=
    fun t => (hPrimitive t t.property).2
  let E : S₀ → (Fin (D * D) → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    fun t => Classical.choose (hPrimitive t).2.2
  have hLetters : ∀ t : S₀,
      Function.Injective (G t * F).mulVec ∧
      ∀ i, E t (Matrix.traceQuotientLetterCoordinates (G t) F *ᵥ Pi.single i 1) =
        (α₃ t / α₂ t) • A t i :=
    fun t => Matrix.traceQuotientLetters_of_normalized_linearEquiv
      (A t) (hA t) (E t) (G t) F (α₂ t) (α₃ t / α₂ t)
      (hα₂ t) (div_ne_zero (hα₃ t) (hα₂ t))
      (fun j i => hPair t i j) (Classical.choose_spec (hPrimitive t).2.2).1
  have hGC : Continuous G := continuous_pi fun j => continuous_pi fun i =>
    (((continuous_apply i).comp hB).matrix_mul
      ((continuous_apply j).comp hB)).matrix_trace
  have hqM : ContinuousOn (fun t => Matrix.traceQuotientLetterCoordinates (G t) F) S₀ :=
    Matrix.continuousOn_traceQuotientLetterCoordinates S₀ G hGC.continuousOn F
      (fun t ht => (hLetters ⟨t, ht⟩).1)
  let q : S₀ → Fin d → Fin (D * D) → ℂ := fun t i =>
    Matrix.traceQuotientLetterCoordinates (G t) F *ᵥ Pi.single i 1
  have hq : Continuous q := continuous_pi fun i =>
    (continuousOn_iff_continuous_domRestrict.mp hqM).matrix_mulVec continuous_const
  let R : T → Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
    fun t => LinearMap.toMatrix' ((μ t).flip (p t))
  have hIdem : ∀ t : S₀, IsIdempotentElem (R t) := by
    intro t
    have hf : IsIdempotentElem ((μ t).flip (p t)) := by
      change ((μ t).flip (p t)).comp ((μ t).flip (p t)) = (μ t).flip (p t)
      apply LinearMap.ext
      intro x
      exact ((Classical.choose_spec (hPrimitive t).2.2).2.2 x (p t) (p t)).trans
        (congrArg (μ t x) (hPrimitive t).1)
    exact hf.map LinearMap.toMatrixAlgEquiv'
  obtain ⟨W, hW, hbase, C, hC, hData⟩ :=
    exists_local_continuous_leftIdealLetters
      (fun t : S₀ => μ t) (fun t : S₀ => M t)
      (continuousOn_iff_continuous_domRestrict.mp hM)
      (fun t x y => Matrix.toLinearMap₂'_apply_mulVec_prod (M t) x y)
      (fun t : S₀ => p t) (fun t : S₀ => R t)
      (continuousOn_iff_continuous_domRestrict.mp hR) (fun _ => rfl) hIdem q hq
      (fun t : S₀ => A t) (fun t => hA t)
      (fun t : S₀ => α₃ t / α₂ t) (fun t => div_ne_zero (hα₃ t) (hα₂ t))
      E (fun t => (Classical.choose_spec (hPrimitive t).2.2).2.1)
      (fun t => (hLetters t).2) ⟨t₀, ht₀⟩ (hPrimitive ⟨t₀, ht₀⟩).2.1
  let C' : T → MPSTensor d D := fun t => if ht : t ∈ S₀ then C ⟨t, ht⟩ else 0
  have hC' : ContinuousOn C' (Subtype.val '' W) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr
    simpa [C', Function.comp_def] using hC
  refine ⟨Subtype.val '' W, hS₀.isOpenMap_subtype_val W hW,
    ⟨⟨t₀, ht₀⟩, hbase, rfl⟩, C', hC', ?_⟩
  rintro t ⟨s, hs, rfl⟩
  simpa only [C', dite_eq_left s.property] using hData s hs

/-- A continuous family of raw tensors whose positive-length periodic rays admit
injective realizations of a fixed positive bond dimension has local continuous
injective realizations of those same rays. The pointwise minimal tensors and
normalizations need not be continuous. Auxiliary context: arXiv:1010.3732,
Section II.F.2, lines 953–993. -/
theorem exists_local_continuous_minimalTensor_of_samePositiveMpvRay
    {T : Type*} [TopologicalSpace T] {d D K : ℕ} [NeZero D]
    (B : T → MPSTensor d K) (hB : Continuous B)
    (A : T → MPSTensor d D) (hA : ∀ t, Kraus.IsInjective (A t))
    (hRay : ∀ t, SamePositiveMpvRay (B t) (A t)) (t₀ : T) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ∃ C : T → MPSTensor d D,
      ContinuousOn C S ∧ ∀ t ∈ S,
        SamePositiveMpvRay (B t) (C t) ∧ Kraus.IsInjective (C t) := by
  classical
  choose α₂ α₃ hα₂ hα₃ hPair hTriple using fun t =>
    exists_nonzero_two_three_trace_scalars_of_samePositiveMpvRay (hA t) (hRay t)
  obtain ⟨S, hS, ht₀, C, hC, hData⟩ :=
    exists_local_continuous_minimalTensor_of_two_three_trace_eq
      B hB A hA α₂ α₃ hα₂ hα₃ hPair hTriple t₀
  exact ⟨S, hS, ht₀, C, hC, fun t ht =>
    ⟨(hRay t).trans (samePositiveMpvRay_of_smul_gaugeEquiv (α₃ t / α₂ t)
      (div_ne_zero (hα₃ t) (hα₂ t)) (hData t ht).1), (hData t ht).2⟩⟩

end MPSTensor
