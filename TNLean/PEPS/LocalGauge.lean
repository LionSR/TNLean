import TNLean.PEPS.VirtualInsertion

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Local gauge candidates for injective PEPS

For a vertex-injective PEPS tensor `A`, the chosen local left inverse lets us pull
any local physical vector back to a coefficient function on the virtual star at a
vertex `v`. When `A` and `B` have the same bond dimensions, this yields a
canonical candidate endomorphism on the local virtual coefficient space of `A`.

The remaining PEPS Fundamental-Theorem blocker is that this candidate must still
be shown to

1. reconstruct the local tensors of `B`, equivalently that the local image of
   `B` lies in the image of `localTensorMap A v`, and
2. factor into independent edge gauges.

We package those two requirements as `HasLocalGaugeLift`. This isolates the exact
output still needed from the blocked-middle / three-site-MPS reduction in
arXiv:1804.04964 §3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Transport a local virtual configuration across a bond-dimension equality. -/
noncomputable def castLocalVirtualConfig (A B : Tensor G d)
    (hDim : A.bondDim = B.bondDim) (v : V) :
    LocalVirtualConfig A v ≃ LocalVirtualConfig B v :=
  Equiv.piCongrRight (fun ie : IncidentEdge G v => finCongr (congr_fun hDim ie.1))

omit [Fintype V] in
@[simp] theorem castLocalVirtualConfig_apply (A B : Tensor G d)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (η : LocalVirtualConfig A v) (ie : IncidentEdge G v) :
    castLocalVirtualConfig A B hDim v η ie =
      Fin.cast (congr_fun hDim ie.1) (η ie) := by
  simp [castLocalVirtualConfig, finCongr_apply]

omit [Fintype V] in
@[simp] theorem castLocalVirtualConfig_symm_apply (A B : Tensor G d)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (η : LocalVirtualConfig B v) (ie : IncidentEdge G v) :
    (castLocalVirtualConfig A B hDim v).symm η ie =
      Fin.cast (congr_fun hDim.symm ie.1) (η ie) := by
  simp [castLocalVirtualConfig]

/-- Reindex coefficient functions on local virtual configurations along
`castLocalVirtualConfig`. -/
noncomputable def castLocalCoeffMap (A B : Tensor G d)
    (hDim : A.bondDim = B.bondDim) (v : V) :
    (LocalVirtualConfig A v → ℂ) →ₗ[ℂ] (LocalVirtualConfig B v → ℂ) where
  toFun c := fun η => c ((castLocalVirtualConfig A B hDim v).symm η)
  map_add' c c' := by
    ext η
    simp
  map_smul' z c := by
    ext η
    simp

omit [Fintype V] in
@[simp] theorem castLocalCoeffMap_apply (A B : Tensor G d)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (c : LocalVirtualConfig A v → ℂ) (η : LocalVirtualConfig B v) :
    castLocalCoeffMap A B hDim v c η =
      c ((castLocalVirtualConfig A B hDim v).symm η) :=
  rfl

@[simp] theorem castLocalCoeffMap_single (A B : Tensor G d)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (η : LocalVirtualConfig A v) :
    castLocalCoeffMap A B hDim v (Pi.single η (1 : ℂ)) =
      Pi.single (castLocalVirtualConfig A B hDim v η) (1 : ℂ) := by
  ext ξ
  by_cases hξ : ξ = castLocalVirtualConfig A B hDim v η
  · subst ξ
    simp only [castLocalCoeffMap_apply]
    rw [(castLocalVirtualConfig A B hDim v).symm_apply_apply η]
    simp
  · have hs : (castLocalVirtualConfig A B hDim v).symm ξ ≠ η := by
      intro hs
      apply hξ
      simpa using congrArg (castLocalVirtualConfig A B hDim v) hs
    simp [castLocalCoeffMap_apply, hξ, hs]

/-- The canonical local coefficient-space candidate obtained by pulling the local
`B`-tensor back through the chosen left inverse of `A`. -/
noncomputable def localGaugeCandidate (A B : Tensor G d)
    (hA : IsVertexInjective A) (hDim : A.bondDim = B.bondDim) (v : V) :
    LocalVirtualOp A v :=
  (localLeftInverse A hA v).comp <|
    (localTensorMap B v).comp (castLocalCoeffMap A B hDim v)

/-- Reindexing a basis vector of the local coefficient space transports the
corresponding `B`-component across `hDim`. -/
theorem localTensorMap_castLocalCoeffMap_single (A B : Tensor G d)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (η : LocalVirtualConfig A v) :
    localTensorMap B v (castLocalCoeffMap A B hDim v (Pi.single η (1 : ℂ))) =
      B.component v (castLocalVirtualConfig A B hDim v η) := by
  rw [castLocalCoeffMap_single, localTensorMap_apply_single]

/-- The canonical local gauge candidate reconstructs the projection of `B`'s
local tensor into the image of `localTensorMap A v`. -/
theorem localGaugeCandidate_apply_single (A B : Tensor G d)
    (hA : IsVertexInjective A) (hDim : A.bondDim = B.bondDim) (v : V)
    (η : LocalVirtualConfig A v) :
    localTensorMap A v (localGaugeCandidate A B hA hDim v (Pi.single η (1 : ℂ))) =
      localProjector A hA v (B.component v (castLocalVirtualConfig A B hDim v η)) := by
  rw [localGaugeCandidate, LinearMap.comp_apply, LinearMap.comp_apply,
    localTensorMap_castLocalCoeffMap_single]
  simp [localProjector, physRealizeLocalOp]

/-- Sharper local hypothesis for PEPS gauge extraction.

This packages exactly the two local outputs still needed from the blocked-middle
reduction in arXiv:1804.04964 §3:

1. the local components of `B` lie in the image of `localTensorMap A v`, and
2. the canonical candidate `localGaugeCandidate` factorizes into one invertible
   matrix on each incident edge. -/
structure HasLocalGaugeLift (A B : Tensor G d) (hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim) (v : V) : Prop where
  projector_fixes :
    ∀ η : LocalVirtualConfig A v,
      localProjector A hA v (B.component v (castLocalVirtualConfig A B hDim v η)) =
        B.component v (castLocalVirtualConfig A B hDim v η)
  factorized_candidate :
    ∃ Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
      ∀ η η' : LocalVirtualConfig A v,
        localGaugeCandidate A B hA hDim v (Pi.single η (1 : ℂ)) η' =
          ∏ ie : IncidentEdge G v,
            (↑(Xv ie.1) : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
              (η ie) (η' ie)

/-- Under `HasLocalGaugeLift`, one obtains the factorized local-gauge formula at
vertex `v`.

This is the honest local endpoint currently available in Lean: the remaining PEPS
Fundamental-Theorem gap is to derive `HasLocalGaugeLift` from `SameState` via the
blocked-middle / three-site-MPS reduction. -/
theorem localGauge_exists_of_liftData (A B : Tensor G d)
    (hA : IsVertexInjective A) (hDim : A.bondDim = B.bondDim) (v : V)
    (hLift : HasLocalGaugeLift A B hA hDim v) :
    ∃ (Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
            (∏ ie : IncidentEdge G v,
              (↑(Xv ie.1) : Matrix _ _ ℂ) (η ie) (η' ie)) *
              A.component v η' σ := by
  rcases hLift.factorized_candidate with ⟨Xv, hXv⟩
  refine ⟨Xv, ?_⟩
  intro η σ
  have hproj := congrArg (fun f : Fin d → ℂ => f σ) (hLift.projector_fixes η)
  have hspec := congrArg (fun f : Fin d → ℂ => f σ)
    (localGaugeCandidate_apply_single A B hA hDim v η)
  calc
    B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        (localProjector A hA v
          (B.component v (castLocalVirtualConfig A B hDim v η))) σ := by
          simpa [castLocalVirtualConfig_apply] using hproj.symm
    _ = (localTensorMap A v
          (localGaugeCandidate A B hA hDim v (Pi.single η (1 : ℂ)))) σ := by
          simpa using hspec.symm
    _ = ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          localGaugeCandidate A B hA hDim v (Pi.single η (1 : ℂ)) η' *
            A.component v η' σ := by
          simp [localTensorMap, Fintype.linearCombination_apply]
    _ = ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          (∏ ie : IncidentEdge G v,
            (↑(Xv ie.1) : Matrix _ _ ℂ) (η ie) (η' ie)) *
              A.component v η' σ := by
          refine Finset.sum_congr rfl ?_
          intro η' _
          rw [hXv η η']

end PEPS
end TNLean
