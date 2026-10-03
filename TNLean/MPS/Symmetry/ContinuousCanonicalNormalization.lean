/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Maps.Proper.Basic
import QICLean.Channel.Irreducible.CollatzWielandt
import QICLean.Kraus.CPPrimitive
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Symmetry.LocalInvariantCompression
import TNLean.MPS.Symmetry.ContinuousStationaryDensity

/-!
# Local continuous Perron normalizations of injective tensor families

Let A(t) be continuous in a fixed positive bond dimension and one-site injective
at t₀. On an open neighborhood of t₀ its right Perron matrix ρ(t) can be chosen
continuously, with ρ(t) positive definite and of trace one. Its positive Perron
value r(t) is continuous and satisfies E_A(t)(ρ(t)) = r(t)ρ(t). The unital tensor
Bⁱ(t) = r(t)^(-1/2) ρ(t)^(-1/2) Aⁱ(t) ρ(t)^(1/2) is continuous there and is
gauge-equivalent to r(t)^(-1/2) A(t).

After this normalization, the unique trace-one adjoint stationary density
can also be chosen continuously. Its one-dimensional fixed space follows
from injectivity and unitality; it is not an additional hypothesis.

The proof uses compactness of the density matrices and uniqueness of the
normalized positive Perron eigenvector (Wolf, Theorem 6.3). Generic
positive-map arguments remain private.

**Scope restriction (supplied continuous tensor family):** SPC11,
arXiv:1010.3732, Section II.F.2, interpolates along a gapped path of physical
states. Every declaration here instead takes a continuous fixed-dimensional
tensor family as a hypothesis and proves only its local continuous Perron and
canonical normalization; reconstruction of such a family from finite-ring
ground states or a uniform physical gap is not asserted. Documented in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix MatrixOrder ComplexOrder Topology
open Matrix

private theorem exists_nonzero_letter {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) : ∃ i, A i ≠ 0 := by
  by_contra! h
  exact (Kraus.not_isInjective_of_linearMap (Matrix.traceLinearMap (Fin D) ℂ ℂ)
    (fun i => by simp [h i]) 1 (by simpa using (show (D : ℂ) ≠ 0 by
      exact_mod_cast NeZero.ne D))) hA

private theorem densityEigenvector_unique {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T) (hTne : T ≠ 0)
    (X Y : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ∈ densityMatrices D) (hY : Y ∈ densityMatrices D)
    (hXeig : T X = trace (T X) • X) (hYeig : T Y = trace (T Y) • Y) :
    X = Y := by
  obtain ⟨R, r, hR, hr, hRpd, hReig, _⟩ :=
    exists_posDef_eigenvector_of_irreducible_positive_of_ne_zero T hT hIrr hTne
  obtain ⟨L, hL, hLeig⟩ :=
    exists_posDef_traceAdjointMap_eigenvector_at_perron T hT hIrr hr hRpd hReig
  have hnormalized : ∀ Z ∈ densityMatrices D,
      T Z = trace (T Z) • Z → Z = R := by
    intro Z hZ hZeig
    have hZne : Z ≠ 0 := fun h ↦ by simpa [h] using hZ.2
    have hpairne : trace (L * Z) ≠ 0 :=
      ne_of_gt (hL.trace_mul_pos_of_posSemidef_of_ne_zero hZ.1 hZne)
    have hvalue : trace (T Z) = (r : ℂ) := by
      apply mul_right_cancel₀ hpairne
      have hpair := (Matrix.trace_traceAdjointMap_mul T L Z).symm
      rw [hLeig, hZeig] at hpair
      simpa only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        using hpair
    obtain ⟨c, hc⟩ := eigenvector_eq_smul_of_irreducible_positive
      T hT hIrr hr.le hRpd hReig (hvalue ▸ hZeig)
    have hc1 : c = 1 := by
      simpa [Matrix.trace_smul, hZ.2, hR.2] using (congrArg trace hc).symm
    simpa [hc1] using hc
  exact (hnormalized X hX hXeig).trans (hnormalized Y hY hYeig).symm

private theorem continuous_densityEigenvectorChoice {S : Type*} [TopologicalSpace S]
    {D : ℕ} [NeZero D]
    (T : S → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hcont : Continuous (fun p : S × Matrix (Fin D) (Fin D) ℂ => T p.1 p.2))
    (hT : ∀ t, IsPositiveMap (T t)) (hIrr : ∀ t, IsIrreducibleMap (T t))
    (hTne : ∀ t, T t ≠ 0)
    (ρ : S → Matrix (Fin D) (Fin D) ℂ)
    (hρ : ∀ t, ρ t ∈ densityMatrices D)
    (heig : ∀ t, T t (ρ t) = trace (T t (ρ t)) • ρ t) :
    Continuous ρ := by
  let ρ' : S → densityMatrices D := fun t => ⟨ρ t, hρ t⟩
  have : CompactSpace (densityMatrices D) :=
    isCompact_iff_compactSpace.mp densityMatrices_isCompact
  suffices h : Continuous ρ' from continuous_subtype_val.comp h
  apply continuous_of_isClosed_graph
  have hgraph : Function.graph ρ' =
      {p : S × densityMatrices D | T p.1 p.2.val =
        trace (T p.1 p.2.val) • p.2.val} := by
    ext p
    change ρ' p.1 = p.2 ↔ _
    constructor
    · intro h
      simpa only [Set.mem_ofPred_eq, ← h, ρ'] using heig p.1
    · intro h
      exact Subtype.ext (densityEigenvector_unique (T p.1) (hT p.1) (hIrr p.1)
        (hTne p.1) (ρ p.1) p.2.val (hρ p.1) p.2.property (heig p.1) h)
  rw [hgraph]
  have hc : Continuous (fun p : S × densityMatrices D => T p.1 p.2.val) :=
    hcont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact isClosed_eq hc
    (hc.matrix_trace.smul (continuous_subtype_val.comp continuous_snd))


/-- In a fixed positive bond dimension, any pointwise choice of normalized
right Perron matrices is continuous for a continuous injective tensor family.
Auxiliary source context: Wolf Theorem 6.3; SPC11, Section II.F.2. -/
theorem MPSTensor.continuous_rightPerronDensity_of_isInjective
    {S : Type*} [TopologicalSpace S] {d D : ℕ} [NeZero D]
    (A : S → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ t, Kraus.IsInjective (A t))
    (ρ : S → Matrix (Fin D) (Fin D) ℂ)
    (hρ : ∀ t, ρ t ∈ densityMatrices D)
    (heig : ∀ t, Kraus.transferMap (A t) (ρ t) =
      trace (Kraus.transferMap (A t) (ρ t)) • ρ t) : Continuous ρ := by
  apply continuous_densityEigenvectorChoice (fun t => Kraus.mapLM (A t)) ?_
    (hT := fun t => Kraus.isPositiveMap_mapLM (A t))
    (hIrr := fun t => Kraus.injective_implies_irreducibleCP (A t) (hInj t))
    (hTne := fun t => Kraus.mapLM_ne_zero_of_exists_ne_zero (A t)
      (exists_nonzero_letter (A t) (hInj t))) ρ hρ heig
  change Continuous (fun p : S × Matrix (Fin D) (Fin D) ℂ =>
    ∑ i : Fin d, A p.1 i * p.2 * (A p.1 i)ᴴ)
  fun_prop

/-- Trace-normalized right Perron data of an injective continuous tensor family
can be chosen continuously. Source context: Wolf Theorem 6.3 and SPC11,
Section II.F.2. -/
theorem MPSTensor.exists_continuous_rightPerronPair_of_isInjective
    {S : Type*} [TopologicalSpace S] {d D : ℕ} [NeZero D]
    (A : S → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ t, Kraus.IsInjective (A t)) :
    ∃ (ρ : S → Matrix (Fin D) (Fin D) ℂ) (r : S → ℝ),
      Continuous ρ ∧ Continuous r ∧ ∀ t,
        (ρ t).PosDef ∧ trace (ρ t) = 1 ∧ 0 < r t ∧
          Kraus.transferMap (A t) (ρ t) = (r t : ℂ) • ρ t := by
  choose ρ r hρ hr hρpd heig hmax using fun t =>
    exists_posDef_eigenvector_of_irreducible_positive_of_ne_zero
      (Kraus.mapLM (A t)) (Kraus.isPositiveMap_mapLM (A t))
      (Kraus.injective_implies_irreducibleCP (A t) (hInj t))
      (Kraus.mapLM_ne_zero_of_exists_ne_zero (A t)
        (exists_nonzero_letter (A t) (hInj t)))
  have htrace : ∀ t, trace (Kraus.mapLM (A t) (ρ t)) = (r t : ℂ) :=
    fun t => by simp [heig t, Matrix.trace_smul, (hρ t).2]
  have hρcont := MPSTensor.continuous_rightPerronDensity_of_isInjective
    A hA hInj ρ hρ (fun t => by simpa only [htrace t] using heig t)
  refine ⟨ρ, r, hρcont, ?_, fun t => ⟨hρpd t, (hρ t).2, hr t, heig t⟩⟩
  have hEρ : Continuous fun t => Kraus.mapLM (A t) (ρ t) := by
    change Continuous (fun t => ∑ i : Fin d, A t i * ρ t * (A t i)ᴴ)
    fun_prop
  simpa only [Function.comp_def, htrace, Complex.ofReal_re] using
    (Complex.continuous_re.comp hEρ.matrix_trace)


private theorem continuous_spectralUnitalGauge {S : Type*} [TopologicalSpace S]
    {d D : ℕ} (A : S → MPSTensor d D) (hA : Continuous A)
    (ρ : S → Matrix (Fin D) (Fin D) ℂ) (hρ : Continuous ρ)
    (hρpd : ∀ t, (ρ t).PosDef) (r : S → ℝ) (hr : Continuous r)
    (hrpos : ∀ t, 0 < r t) :
    Continuous fun t => Kraus.spectralUnitalGauge (A t) (r t) (ρ t) := by
  have hsqrt : Continuous fun t => CFC.sqrt (ρ t) := by
    open scoped Matrix.Norms.L2Operator in
      exact CFC.continuousOn_sqrt.comp_continuous hρ (fun t => (hρpd t).posSemidef.nonneg)
  have hinv : Continuous fun t => (CFC.sqrt (ρ t))⁻¹ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_matrix_inv _ (by
      simpa only [Ring.inverse_eq_inv'] using
        continuousAt_inv₀ (hρpd t).isUnit_det_cfc_sqrt.ne_zero)).comp hsqrt.continuousAt
  have hscale : Continuous fun t => (↑((Real.sqrt (r t))⁻¹) : ℂ) :=
    Complex.continuous_ofReal.comp ((Real.continuous_sqrt.comp hr).inv₀
      (fun t => Real.sqrt_ne_zero'.mpr (hrpos t)))
  exact continuous_pi (fun i => hscale.smul
    ((hinv.matrix_mul ((continuous_apply i).comp hA)).matrix_mul hsqrt))

private theorem exists_continuous_unitalNormalization
    {S : Type*} [TopologicalSpace S] {d D : ℕ} [NeZero D]
    (A : S → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ t, Kraus.IsInjective (A t)) :
    ∃ (B : S → MPSTensor d D) (ρ : S → Matrix (Fin D) (Fin D) ℂ) (r : S → ℝ),
      Continuous B ∧ Continuous ρ ∧ Continuous r ∧ ∀ t,
        (ρ t).PosDef ∧ trace (ρ t) = 1 ∧ 0 < r t ∧
        Kraus.transferMap (A t) (ρ t) = (r t : ℂ) • ρ t ∧
        B t = Kraus.spectralUnitalGauge (A t) (r t) (ρ t) ∧
        Kraus.IsUnital (B t) ∧
        MPSTensor.GaugeEquiv ((↑((Real.sqrt (r t))⁻¹) : ℂ) • A t) (B t) := by
  obtain ⟨ρ, r, hρcont, hrcont, hdata⟩ :=
    MPSTensor.exists_continuous_rightPerronPair_of_isInjective A hA hInj
  refine ⟨fun t => Kraus.spectralUnitalGauge (A t) (r t) (ρ t), ρ, r,
    continuous_spectralUnitalGauge A hA ρ hρcont (fun t => (hdata t).1)
      r hrcont (fun t => (hdata t).2.2.1), hρcont, hrcont, ?_⟩
  refine fun t => ⟨(hdata t).1, (hdata t).2.1, (hdata t).2.2.1,
    (hdata t).2.2.2, rfl, Kraus.spectralUnitalGauge_isUnital_of_map_eigenvector
      (A t) (ρ t) (r t) (hdata t).1 (hdata t).2.2.1 (hdata t).2.2.2, ?_⟩
  convert MPSTensor.gaugeEquiv_unitalGauge
    ((↑((Real.sqrt (r t))⁻¹) : ℂ) • A t) (ρ t) (hdata t).1 using 1
  ext i
  simp [Kraus.spectralUnitalGauge, Kraus.unitalGauge]


/-- A continuous tensor family with fixed positive bond dimension has local
continuous Perron data and an explicit continuous unital normalization near
an injective base tensor. The result is conditional on the supplied tensor
family; it does not reconstruct that family from physical ground-state data.
Source context: Wolf Theorem 6.3; SPC11, Section II.F.2. -/
theorem MPSTensor.exists_local_continuous_unitalNormalization_of_isInjective
    {S : Type*} [TopologicalSpace S] {d D : ℕ} [NeZero D]
    (A : S → MPSTensor d D) (hA : Continuous A) (t₀ : S)
    (hInj : Kraus.IsInjective (A t₀)) :
    ∃ s : Set S, IsOpen s ∧ t₀ ∈ s ∧
      ∃ (B : s → MPSTensor d D) (ρ : s → Matrix (Fin D) (Fin D) ℂ) (r : s → ℝ),
        Continuous B ∧ Continuous ρ ∧ Continuous r ∧ ∀ t,
          (ρ t).PosDef ∧ trace (ρ t) = 1 ∧ 0 < r t ∧
          Kraus.transferMap (A t) (ρ t) = (r t : ℂ) • ρ t ∧
          B t = Kraus.spectralUnitalGauge (A t) (r t) (ρ t) ∧
          Kraus.IsUnital (B t) ∧
          GaugeEquiv ((↑((Real.sqrt (r t))⁻¹) : ℂ) • A t) (B t) := by
  obtain ⟨s, hs, hsopen, ht₀⟩ := mem_nhds_iff.mp
    (MPSTensor.eventually_isInjective_of_continuousAt A t₀ hA.continuousAt hInj)
  exact ⟨s, hsopen, ht₀, exists_continuous_unitalNormalization
    (fun t : s => A t) (hA.comp continuous_subtype_val) (fun t => hs t.property)⟩


private theorem adjointFixedSpace_finrank_eq_one_of_unital_injective
    {d D : ℕ} [NeZero D] (B : MPSTensor d D)
    (hB : Kraus.IsInjective B) (hUnital : Kraus.IsUnital B) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM B)) = 1 := by
  let E := Kraus.mapLM (fun i => (B i)ᴴ)
  have hIrr : IsIrreducibleMap E :=
    Kraus.isIrreducibleMap_mapLM_conjTranspose B
      (Kraus.injective_implies_irreducibleCP B hB)
  have hTP : Kraus.IsTP (fun i => (B i)ᴴ) := by
    simpa [Kraus.IsTP, Kraus.IsUnital] using hUnital
  obtain ⟨σ, hσ, hσfix⟩ := IsStationaryMap.exists_stationaryState_of_linear E
    (Kraus.isPositiveMap_mapLM (fun i => (B i)ᴴ))
    (Kraus.isTracePreservingMap_mapLM_of_isTP (fun i => (B i)ᴴ) hTP)
  have hσpd : σ.PosDef := posDef_of_posSemidef_eigenvector_irreducible E
    (Kraus.isPositiveMap_mapLM (fun i => (B i)ᴴ)) hIrr σ 1 hσ.1
    (fun h => by simpa [h] using hσ.2) (by simpa using hσfix)
  have hdim := finrank_eigenspace_eq_one_of_irreducible_positive E
    (Kraus.isPositiveMap_mapLM (fun i => (B i)ᴴ)) hIrr
    (r := 1) (by norm_num) hσpd (by simpa using hσfix)
  have hE : Kraus.adjointMapLM B = E := by
    ext X i j
    simp [E, Kraus.adjointMapLM_apply, Kraus.adjointMap, Kraus.mapLM_apply, Kraus.map]
  rw [hE, ← LinearMap.ker_neg, neg_sub]
  rw [Module.End.eigenspace_def] at hdim
  rw [Complex.ofReal_one, one_smul] at hdim
  exact hdim

/-- Local continuous canonical data for a supplied continuous fixed-dimensional
injective tensor family. The right Perron matrix gives the explicit unital
gauge; the normalized adjoint stationary density is continuous and unique
among all trace-one fixed matrices. No fixed-space dimension hypothesis is
supplied: it follows from injectivity and unitality.
Source context: Wolf, Theorems 6.3 and 6.11; SPC11, Section II.F.2. -/
theorem MPSTensor.exists_local_continuous_canonicalNormalization_of_isInjective
    {S : Type*} [TopologicalSpace S] {d D : ℕ} [NeZero D]
    (A : S → MPSTensor d D) (hA : Continuous A) (t₀ : S)
    (hInj : Kraus.IsInjective (A t₀)) :
    ∃ s : Set S, IsOpen s ∧ t₀ ∈ s ∧
      ∃ (B : s → MPSTensor d D) (ρ : s → Matrix (Fin D) (Fin D) ℂ)
        (r : s → ℝ) (σ : s → Matrix (Fin D) (Fin D) ℂ),
        Continuous B ∧ Continuous ρ ∧ Continuous r ∧ Continuous σ ∧ ∀ t,
          ((ρ t).PosDef ∧ trace (ρ t) = 1 ∧ 0 < r t ∧
            Kraus.transferMap (A t) (ρ t) = (r t : ℂ) • ρ t ∧
            B t = Kraus.spectralUnitalGauge (A t) (r t) (ρ t) ∧
            Kraus.IsUnital (B t) ∧
            GaugeEquiv ((↑((Real.sqrt (r t))⁻¹) : ℂ) • A t) (B t)) ∧
          (σ t).PosSemidef ∧ trace (σ t) = 1 ∧
            Kraus.adjointMap (B t) (σ t) = σ t ∧
              ∀ X : Matrix (Fin D) (Fin D) ℂ,
                Kraus.adjointMap (B t) X = X → trace X = 1 → X = σ t := by
  obtain ⟨s, hsopen, ht₀, B, ρ, r, hB, hρ, hr, hdata⟩ :=
    exists_local_continuous_unitalNormalization_of_isInjective A hA t₀ hInj
  let p₀ : s := ⟨t₀, ht₀⟩
  have hB₀ : Kraus.IsInjective (B p₀) := isInjective_of_gaugeEquiv
    (hInj.smul (show (↑((Real.sqrt (r p₀))⁻¹) : ℂ) ≠ 0 from by
      exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (hdata p₀).2.2.1)))
    (hdata p₀).2.2.2.2.2.2
  obtain ⟨q, hqopen, hp₀, σ, hσcont, hσdata⟩ :=
    exists_local_continuous_adjointStationaryDensity_of_unital B hB
      (fun t => (hdata t).2.2.2.2.2.1) p₀
      (adjointFixedSpace_finrank_eq_one_of_unital_injective
        (B p₀) hB₀ (hdata p₀).2.2.2.2.2.1)
  obtain ⟨u, huopen, hu⟩ := isOpen_induced_iff.mp hqopen
  have ht₀u : t₀ ∈ u := by simpa only [← hu, Set.mem_preimage, p₀] using hp₀
  let j : ↥(s ∩ u) → s := fun t => ⟨t.val, t.property.1⟩
  have hjq : ∀ t, j t ∈ q := fun t => by
    simpa only [← hu, Set.mem_preimage, j] using t.property.2
  let k : ↥(s ∩ u) → q := fun t => ⟨j t, hjq t⟩
  have hjcont : Continuous j :=
    continuous_subtype_val.subtype_mk (fun t => t.property.1)
  have hkcont : Continuous k := hjcont.subtype_mk hjq
  refine ⟨s ∩ u, hsopen.inter huopen, ⟨ht₀, ht₀u⟩,
    B ∘ j, ρ ∘ j, r ∘ j, σ ∘ k,
    hB.comp hjcont, hρ.comp hjcont, hr.comp hjcont, hσcont.comp hkcont, ?_⟩
  exact fun t => ⟨hdata (j t), hσdata (k t)⟩
