/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.QuasiLocalBlocking
import TNLean.QCA.StateSpace
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# State and purity transport under site grouping

A star-algebra equivalence of quasi-local observable algebras induces a
continuous linear equivalence of their functional spaces by inverse
precomposition. This equivalence preserves the functional norm and maps the
entire normalized positive state space onto the entire state space. Hence it
preserves pure states, understood as extreme points among all states.

Applying this construction to the existing site-blocking equivalence transports
states from the blocked lattice to the original lattice. No translation
invariance is assumed. These are consequences of the observable-algebra
identification; they do not identify a particular periodic GVBS presentation
or its finite-interval support spaces.

Source: the regrouping of sites in Nachtergaele, arXiv:cond-mat/9410110,
lines 825--836, and the state/purity convention at lines 1469--1482;
arXiv:1703.09188, Appendix, lines 2308 and 2313--2320, for site grouping.
-/

open scoped ComplexOrder

namespace SpinChain

variable {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]

/-- A star-algebra equivalence transports continuous state functionals by
inverse precomposition. This is the abstract state transport for the grouping
of sites in Nachtergaele, arXiv:cond-mat/9410110, lines 825--836. -/
noncomputable def quasiLocalFunctionalCongr
    (e : QuasiLocalAlgebra d₁ ≃⋆ₐ[ℂ] QuasiLocalAlgebra d₂) :
    (QuasiLocalAlgebra d₁ →L[ℂ] ℂ) ≃L[ℂ] (QuasiLocalAlgebra d₂ →L[ℂ] ℂ) :=
  let E : QuasiLocalAlgebra d₁ ≃L[ℂ] QuasiLocalAlgebra d₂ :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := map_add e
      map_smul' := map_smul e
      continuous_toFun := (StarAlgEquiv.isometry e).continuous
      continuous_invFun := (StarAlgEquiv.isometry e.symm).continuous }
  ContinuousLinearEquiv.arrowCongr E (ContinuousLinearEquiv.refl ℂ ℂ)

/-- Evaluation of inverse precomposition. -/
@[simp] theorem quasiLocalFunctionalCongr_apply
    (e : QuasiLocalAlgebra d₁ ≃⋆ₐ[ℂ] QuasiLocalAlgebra d₂)
    (ω : QuasiLocalAlgebra d₁ →L[ℂ] ℂ) (X : QuasiLocalAlgebra d₂) :
    quasiLocalFunctionalCongr e ω X = ω (e.symm X) := rfl

/-- Inverse precomposition by a star-algebra equivalence preserves the
functional norm. -/
theorem norm_quasiLocalFunctionalCongr
    (e : QuasiLocalAlgebra d₁ ≃⋆ₐ[ℂ] QuasiLocalAlgebra d₂)
    (ω : QuasiLocalAlgebra d₁ →L[ℂ] ℂ) :
    ‖quasiLocalFunctionalCongr e ω‖ = ‖ω‖ := by
  apply le_antisymm
  · exact (quasiLocalFunctionalCongr e ω).opNorm_le_bound (norm_nonneg ω)
      (fun X => by simpa only [quasiLocalFunctionalCongr_apply, StarAlgEquiv.norm_map]
        using ω.le_opNorm (e.symm X))
  · refine ω.opNorm_le_bound (norm_nonneg (quasiLocalFunctionalCongr e ω)) ?_
    intro X
    simpa only [quasiLocalFunctionalCongr_apply, StarAlgEquiv.symm_apply_apply,
      StarAlgEquiv.norm_map] using (quasiLocalFunctionalCongr e ω).le_opNorm (e X)

/-- A star-algebra equivalence preserves normalization and positivity of states. -/
@[simp] theorem quasiLocalFunctionalCongr_mem_stateSpace_iff
    (e : QuasiLocalAlgebra d₁ ≃⋆ₐ[ℂ] QuasiLocalAlgebra d₂)
    (ω : QuasiLocalAlgebra d₁ →L[ℂ] ℂ) :
    quasiLocalFunctionalCongr e ω ∈ quasiLocalStateSpace d₂ ↔
      ω ∈ quasiLocalStateSpace d₁ := by
  simp only [quasiLocalStateSpace, Set.mem_ofPred_eq, norm_quasiLocalFunctionalCongr,
    quasiLocalFunctionalCongr_apply, map_one, map_mul, map_star]
  rw [(EquivLike.surjective e.symm).forall]

/-- The induced functional equivalence maps the entire state space onto
the entire state space. -/
theorem quasiLocalFunctionalCongr_image_stateSpace
    (e : QuasiLocalAlgebra d₁ ≃⋆ₐ[ℂ] QuasiLocalAlgebra d₂) :
    quasiLocalFunctionalCongr e '' quasiLocalStateSpace d₁ = quasiLocalStateSpace d₂ := by
  ext ω
  obtain ⟨ω, rfl⟩ := EquivLike.surjective (quasiLocalFunctionalCongr e) ω
  simp only [(EquivLike.injective (quasiLocalFunctionalCongr e)).mem_set_image,
    quasiLocalFunctionalCongr_mem_stateSpace_iff]

/-- Purity, defined by extremality among all states, is invariant under
star-algebra equivalence. No translation invariance is assumed. -/
@[simp] theorem isPureQuasiLocalState_quasiLocalFunctionalCongr_iff
    (e : QuasiLocalAlgebra d₁ ≃⋆ₐ[ℂ] QuasiLocalAlgebra d₂)
    (ω : QuasiLocalAlgebra d₁ →L[ℂ] ℂ) :
    IsPureQuasiLocalState d₂ (quasiLocalFunctionalCongr e ω) ↔
      IsPureQuasiLocalState d₁ ω := by
  have hImage := image_extremePoints
    ((quasiLocalFunctionalCongr e).toLinearEquiv.restrictScalars ℝ)
    (quasiLocalStateSpace d₁)
  change quasiLocalFunctionalCongr e '' (quasiLocalStateSpace d₁).extremePoints ℝ =
    (quasiLocalFunctionalCongr e '' quasiLocalStateSpace d₁).extremePoints ℝ at hImage
  simpa only [IsPureQuasiLocalState, quasiLocalFunctionalCongr_image_stateSpace,
    (EquivLike.injective (quasiLocalFunctionalCongr e)).mem_set_image] using
    (Iff.of_eq (congrArg (fun S => quasiLocalFunctionalCongr e ω ∈ S) hImage)).symm

/-- A functional on the blocked chain becomes a functional on the original
chain by inverse blocking of observables. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836; the completed observable identification
is the one in arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
noncomputable def quasiLocalBlockingFunctional (d L : ℕ) [NeZero d] [NeZero L] :
    (QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) →L[ℂ] ℂ) ≃L[ℂ]
      (QuasiLocalAlgebra d →L[ℂ] ℂ) :=
  quasiLocalFunctionalCongr (quasiLocalBlocking d L)

/-- Evaluation of the transported functional on an original observable. -/
@[simp] theorem quasiLocalBlockingFunctional_apply (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) →L[ℂ] ℂ)
    (X : QuasiLocalAlgebra d) :
    quasiLocalBlockingFunctional d L ω X = ω ((quasiLocalBlocking d L).symm X) := rfl

/-- Site grouping preserves the norm of a continuous functional. -/
theorem norm_quasiLocalBlockingFunctional (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) →L[ℂ] ℂ) :
    ‖quasiLocalBlockingFunctional d L ω‖ = ‖ω‖ :=
  norm_quasiLocalFunctionalCongr (quasiLocalBlocking d L) ω

/-- States on the blocked chain correspond to states on the original chain. -/
@[simp] theorem quasiLocalBlockingFunctional_mem_stateSpace_iff
    (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) →L[ℂ] ℂ) :
    quasiLocalBlockingFunctional d L ω ∈ quasiLocalStateSpace d ↔
      ω ∈ quasiLocalStateSpace (MPSTensor.blockPhysDim d L) :=
  quasiLocalFunctionalCongr_mem_stateSpace_iff (quasiLocalBlocking d L) ω

/-- A pure state on the blocked chain is pure on the original lattice, and
conversely. Purity is tested against all state decompositions. Source:
Nachtergaele, arXiv:cond-mat/9410110, lines 825--836 and 1469--1482. -/
@[simp] theorem isPureQuasiLocalState_quasiLocalBlockingFunctional_iff
    (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) →L[ℂ] ℂ) :
    IsPureQuasiLocalState d (quasiLocalBlockingFunctional d L ω) ↔
      IsPureQuasiLocalState (MPSTensor.blockPhysDim d L) ω :=
  isPureQuasiLocalState_quasiLocalFunctionalCongr_iff (quasiLocalBlocking d L) ω

end SpinChain
