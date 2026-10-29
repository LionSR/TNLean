/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.PeriodicKernel
import TNLean.MPS.Examples.PVBSPureWindowMatchingVolume
import TNLean.MPS.ParentHamiltonian.PhysicalSectorKernelDecomposition
import Mathlib.RingTheory.RootsOfUnity.Complex
import TNLean.MPS.Preparation.PeriodicFiniteRepresentation
import TNLean.MPS.Core.PhysicalEmbedding

/-!
# A fixed interaction with an exceptional short-volume ground line

The physical alphabet has three Weyl letters and two particle letters. The
local kernel is the sum of the embedded seven-site Weyl boundary space and
the embedded pure particle line. Its complementary projection is a single
positive interaction of range seven. For a primitive fifth-root Weyl parameter
and a matching seventh-root particle weight, its actual periodic kernel is the
particle line at seven sites and the Weyl trace line at every larger volume.

All volume assertions explicitly concern the permitted domain of at least
seven sites. This is not a statement about shorter chains under a different
interaction convention, nor a counterexample to an eventual fixed-tensor
conclusion or to general site-dependent matrix product representations.
Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 790--793,
850--880; PGVWC07, MPSarchive.tex lines 663--671 and 2244--2265.
-/

namespace MPSTensor.ShortMomentum

/-- A fixed positive interaction on five physical letters, with seven-site
local kernel equal to the actual Weyl boundary sector plus the actual pure
particle sector. Source context: SPWC10, Theorem 5, lines 850--880, with the
permitted-volume and translation-phase distinctions explicit in this module. -/
noncomputable def sevenSectorInteraction (ζ q : ℂ) : MPVSpace 5 7 →ₗ[ℂ] MPVSpace 5 7 :=
  ((groundSpaceES (threeLetterTensor ζ) 7).map
      (Function.Embedding.piCongrRight
        (fun _ : Fin 7 ↦ (Fin.castAddEmb 2 : Fin 3 ↪ Fin 5)))
        .euclideanExtendByZero.toLinearMap ⊔
    (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q 7)}).map
      (Function.Embedding.piCongrRight
        (fun _ : Fin 7 ↦ (Fin.natAddEmb 3 : Fin 2 ↪ Fin 5)))
        .euclideanExtendByZero.toLinearMap)ᗮ.starProjection.toLinearMap

/-- The fixed seven-site interaction is positive, independently of the chosen
complex parameters. Source: its actual complementary orthogonal projection. -/
theorem sevenSectorInteraction_isPositive (ζ q : ℂ) :
    (sevenSectorInteraction ζ q).IsPositive :=
  (Submodule.isSymmetricProjection_starProjection _).isPositive

/-- At every permitted volume greater than seven, the actual periodic kernel
is exactly the embedded nonzero Weyl trace line. No component or mixed-sector
kernel identity is assumed. Source context: SPWC10, Theorem 5, lines 850--880. -/
theorem ker_sevenSectorHamiltonian_of_eight_le {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (hq : q ≠ 0) (M : ℕ) (hM : 8 ≤ M) :
    LinearMap.ker (periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) M) =
      Submodule.span ℂ {(Function.Embedding.piCongrRight
        (fun _ : Fin M ↦ (Fin.castAddEmb 2 : Fin 3 ↪ Fin 5)))
          .euclideanExtendByZero (mpvState (threeLetterTensor ζ) M)} := by
  have hmain : LinearMap.ker (periodicInteractionHamiltonianES
      (groundSpaceES (threeLetterTensor ζ) 7)ᗮ.starProjection.toLinearMap M) =
      Submodule.span ℂ {mpvState (threeLetterTensor ζ) M} := by
    change LinearMap.ker (periodicInteractionHamiltonianES
      (parentInteractionES (threeLetterTensor ζ) 7) M) = _
    rw [periodicInteractionHamiltonianES_parentInteractionES _ (by decide)]
    exact ker_parentHamiltonianES_threeLetterTensor_eq_span hζ M hM
  have hparticle : LinearMap.ker (periodicInteractionHamiltonianES
      (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q 7)})ᗮ.starProjection.toLinearMap M) = ⊥ :=
    ker_pvbsPureWindowHamiltonian_eq_bot q hq 5 hM
  rw [sevenSectorInteraction, ker_physical_sum_projectorHamiltonian _ _ (by decide) (by omega),
    hmain, hparticle, Submodule.map_bot, sup_bot_eq, Submodule.map_span, Set.image_singleton]

/-- One actual site-independent tensor of bond dimension five represents the
nonzero ground line at every length at least eight. The tensor is the physical
extension of the existing Weyl tensor, not a supplied state family.
This is an eventual statement, consistent with SPWC10's future-length proof
at lines 877--879. -/
theorem exists_bond_five_eventual_ground_family_sevenSector {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (hq : q ≠ 0) :
    ∃ A : MPSTensor 5 5, ∀ M : ℕ, 8 ≤ M →
      mpvState A M ≠ 0 ∧
      LinearMap.ker (periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) M) =
        Submodule.span ℂ {mpvState A M} := by
  let e : Fin 3 ↪ Fin 5 := Fin.castAddEmb 2
  refine ⟨Function.extend e (threeLetterTensor ζ) 0, fun M hM ↦ ?_⟩
  have hstate := mpvState_extend_physical e (threeLetterTensor ζ) M
  constructor
  · rw [hstate]
    intro hzero
    have hz := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e))
      .euclideanExtendByZero.injective
      (hzero.trans ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e))
        .euclideanExtendByZero.map_zero).symm)
    exact mpvState_threeLetterTensor_ne_zero hζ M hM hz
  · rw [hstate]
    exact ker_sevenSectorHamiltonian_of_eight_le hζ hq M hM

/-- At the matching volume seven, the actual periodic kernel is exactly the
embedded geometric particle line, with its root-of-unity phase retained.
Source context: the finite-prefix distinction in SPWC10, Theorem 5, lines 850--880. -/
theorem ker_sevenSectorHamiltonian_seven {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (hq : q ^ 7 = 1) :
    LinearMap.ker (periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) 7) =
      Submodule.span ℂ {(Function.Embedding.piCongrRight
        (fun _ : Fin 7 ↦ (Fin.natAddEmb 3 : Fin 2 ↪ Fin 5)))
          .euclideanExtendByZero (WithLp.toLp 2 (pvbsEdge q 7))} := by
  have hmain : LinearMap.ker (periodicInteractionHamiltonianES
      (groundSpaceES (threeLetterTensor ζ) 7)ᗮ.starProjection.toLinearMap 7) = ⊥ := by
    change LinearMap.ker (periodicInteractionHamiltonianES
      (parentInteractionES (threeLetterTensor ζ) 7) 7) = _
    rw [periodicInteractionHamiltonianES_parentInteractionES _ (by decide)]
    exact ker_parentHamiltonianES_threeLetterTensor_seven_eq_bot hζ
  have hparticle : LinearMap.ker (periodicInteractionHamiltonianES
      (Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q 7)})ᗮ.starProjection.toLinearMap 7) =
      Submodule.span ℂ {WithLp.toLp 2 (pvbsEdge q 7)} :=
    ker_pvbsPureWindowHamiltonian_matching_volume q (by decide) hq
  rw [sevenSectorInteraction, ker_physical_sum_projectorHamiltonian _ _ (by decide) le_rfl,
    hmain, hparticle, Submodule.map_bot, bot_sup_eq, Submodule.map_span, Set.image_singleton]

/-- Every permitted volume has an actual nonzero spanning ground vector for
this one fixed interaction. This proves frustration-free nonvanishing as well
as the one-dimensional kernel, rather than assuming ground-state suppliers.
Source context: SPWC10's fixed-interaction condition, Theorem 5, lines 850--857;
the volume domain here is explicitly \(M\ge7\). -/
theorem exists_nonzero_ground_line_sevenSectorHamiltonian {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (hq : q ^ 7 = 1) (M : ℕ) (hM : 7 ≤ M) :
    ∃ v : MPVSpace 5 M, v ≠ 0 ∧
      periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) M v = 0 ∧
      LinearMap.ker (periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) M) =
        Submodule.span ℂ {v} := by
  have hqzero : q ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact zero_ne_one hq
  by_cases hseven : M = 7
  · subst M
    let E := (Function.Embedding.piCongrRight
      (fun _ : Fin 7 ↦ (Fin.natAddEmb 3 : Fin 2 ↪ Fin 5))).euclideanExtendByZero
    let v := E (WithLp.toLp 2 (pvbsEdge q 7))
    have hv : v ≠ 0 := by
      intro hv
      have hz := E.injective (hv.trans E.map_zero.symm)
      exact (pvbsPureWindowHamiltonian_matching_volume_nonzero_ground q (by decide) hq).1 hz
    have hker : LinearMap.ker
        (periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) 7) =
        Submodule.span ℂ {v} := ker_sevenSectorHamiltonian_seven hζ hq
    refine ⟨v, hv, ?_, hker⟩
    exact hker.symm ▸ Submodule.mem_span_singleton_self v
  · have hlarge : 8 ≤ M := by omega
    let E := (Function.Embedding.piCongrRight
      (fun _ : Fin M ↦ (Fin.castAddEmb 2 : Fin 3 ↪ Fin 5))).euclideanExtendByZero
    let v := E (mpvState (threeLetterTensor ζ) M)
    have hv : v ≠ 0 := by
      intro hv
      exact mpvState_threeLetterTensor_ne_zero hζ M hlarge
        (E.injective (hv.trans E.map_zero.symm))
    have hker : LinearMap.ker
        (periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) M) =
        Submodule.span ℂ {v} := ker_sevenSectorHamiltonian_of_eight_le hζ hqzero M hlarge
    refine ⟨v, hv, ?_, hker⟩
    exact hker.symm ▸ Submodule.mem_span_singleton_self v

/-- The fixed interaction has a one-dimensional actual ground kernel at every
permitted volume. Its nonzero spanning vector is derived in the preceding
existence theorem. Source context: SPWC10, Theorem 5, lines 850--857. -/
theorem finrank_ker_sevenSectorHamiltonian {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (hq : q ^ 7 = 1) (M : ℕ) (hM : 7 ≤ M) :
    Module.finrank ℂ
      (LinearMap.ker (periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) M)) = 1 := by
  obtain ⟨v, hv, _, hker⟩ := exists_nonzero_ground_line_sevenSectorHamiltonian hζ hq M hM
  rw [hker]
  exact finrank_span_singleton hv

/-- A nontrivial particle phase leaves no nonzero translation-invariant
coefficient vector in the actual seven-site ground kernel. Translation acts on
the full physical alphabet; the particle coefficient restriction is derived.
Source context: SPWC10, Theorem 5, lines 850--880, and the ordinary periodic
trace convention at lines 790--793. -/
theorem eq_zero_of_sevenSectorHamiltonian_fixed {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (hq : q ^ 7 = 1) (hqone : q ≠ 1) (ψ : MPVSpace 5 7)
    (hzero : periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) 7 ψ = 0)
    (hfixed : ∀ s : Fin 7, cyclicTranslateState s ψ.ofLp = ψ.ofLp) : ψ = 0 := by
  have hmem : ψ ∈ Submodule.span ℂ {(Function.Embedding.piCongrRight
      (fun _ : Fin 7 ↦ (Fin.natAddEmb 3 : Fin 2 ↪ Fin 5)))
        .euclideanExtendByZero (WithLp.toLp 2 (pvbsEdge q 7))} := by
    rw [← ker_sevenSectorHamiltonian_seven hζ hq]
    exact hzero
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  let E := (Function.Embedding.piCongrRight
    (fun _ : Fin 7 ↦ (Fin.natAddEmb 3 : Fin 2 ↪ Fin 5))).euclideanExtendByZero
  let y : MPVSpace 2 7 := c • WithLp.toLp 2 (pvbsEdge q 7)
  have hEy : E y = ψ := by
    rw [y, map_smul]
    exact hc
  have hyzero : periodicInteractionHamiltonianES (pvbsPureWindowInteraction q 7) 7 y = 0 := by
    rw [y, map_smul, pvbsPureWindowHamiltonian_apply_pvbsEdge q (by decide) hq, smul_zero]
  have hyfixed (s : Fin 7) : cyclicTranslateState s y.ofLp = y.ofLp := by
    funext σ
    have h := congrFun (hfixed s) (fun i ↦ Fin.natAdd 3 (σ i))
    rw [← hEy] at h
    change E y ((Function.Embedding.piCongrRight
      (fun _ : Fin 7 ↦ (Fin.natAddEmb 3 : Fin 2 ↪ Fin 5))) (cyclicTranslateCfg s σ)) =
      E y ((Function.Embedding.piCongrRight
        (fun _ : Fin 7 ↦ (Fin.natAddEmb 3 : Fin 2 ↪ Fin 5))) σ) at h
    simpa only [E, Function.Embedding.euclideanExtendByZero_apply_image] using h
  have hy := eq_zero_of_pvbsPureWindow_matching_volume_fixed q (by decide) hq hqone y hyzero hyfixed
  rw [← hEy, hy, map_zero]

/-- At the exceptional volume there is no nonzero ordinary periodic trace-MPS
ground vector at any bond dimension. This follows from actual vector-level
cyclic invariance of every such trace expression, not from an assumed lower
bound on its bond dimension. Source: the ordinary trace convention in SPWC10,
lines 790--793, and its finite-prefix distinction at lines 877--879. -/
theorem mpvState_eq_zero_of_sevenSectorHamiltonian_eq_zero {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (hq : q ^ 7 = 1) (hqone : q ≠ 1)
    {D : ℕ} (A : MPSTensor 5 D)
    (hzero : periodicInteractionHamiltonianES (sevenSectorInteraction ζ q) 7
      (mpvState A 7) = 0) : mpvState A 7 = 0 := by
  apply eq_zero_of_sevenSectorHamiltonian_fixed hζ hq hqone (mpvState A 7) hzero
  intro s
  funext σ
  exact mpvState_cyclic_invariant A s σ

/-- There exists one fixed positive seven-site interaction with a nonzero common
local ground vector and a one-dimensional actual periodic kernel at every
permitted volume, but no nonzero translation-invariant ground vector at seven
sites. The volume domain and vector-level invariance are part of the statement.
This tests the all-volume ordinary trace-MPS strengthening, not the eventual
fixed-tensor conclusion in SPWC10, Theorem 5, proof lines 877--879. -/
theorem exists_seven_site_interaction_without_short_fixed_ground :
    ∃ h : MPVSpace 5 7 →ₗ[ℂ] MPVSpace 5 7, h.IsPositive ∧
      (∀ M : ℕ, 7 ≤ M →
        Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1 ∧
        ∃ v : MPVSpace 5 M, v ≠ 0 ∧
          ∀ i : Fin M, periodicLocalInteractionES h i v = 0) ∧
      (∃ A : MPSTensor 5 5, ∀ M : ℕ, 8 ≤ M → mpvState A M ≠ 0 ∧
        LinearMap.ker (periodicInteractionHamiltonianES h M) =
          Submodule.span ℂ {mpvState A M}) ∧
      (∀ ψ : MPVSpace 5 7, periodicInteractionHamiltonianES h 7 ψ = 0 →
        (∀ s : Fin 7, cyclicTranslateState s ψ.ofLp = ψ.ofLp) → ψ = 0) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  let q : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)
  have hζ : IsPrimitiveRoot ζ 5 := Complex.isPrimitiveRoot_exp 5 (by decide)
  have hq : IsPrimitiveRoot q 7 := Complex.isPrimitiveRoot_exp 7 (by decide)
  refine ⟨sevenSectorInteraction ζ q, sevenSectorInteraction_isPositive ζ q, ?_, ?_, ?_⟩
  · intro M hM
    refine ⟨finrank_ker_sevenSectorHamiltonian hζ hq.pow_eq_one M hM, ?_⟩
    obtain ⟨v, hv, hzero, _⟩ :=
      exists_nonzero_ground_line_sevenSectorHamiltonian hζ hq.pow_eq_one M hM
    refine ⟨v, hv, ?_⟩
    exact (WeightedPositiveKernel.apply_sum_eq_zero_iff
      (fun i : Fin M ↦ periodicLocalInteractionES_isPositive
        (sevenSectorInteraction_isPositive ζ q) i) v).mp hzero
  · exact exists_bond_five_eventual_ground_family_sevenSector hζ (hq.ne_zero (by decide))
  · intro ψ hzero hfixed
    exact eq_zero_of_sevenSectorHamiltonian_fixed hζ hq.pow_eq_one
      (hq.ne_one (by decide)) ψ hzero hfixed

end MPSTensor.ShortMomentum
