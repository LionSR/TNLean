import TNLean.PEPS.VirtualInsertion

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Local gauge maps for injective PEPS

For a vertex-injective PEPS tensor `A`, the chosen local left inverse lets us pull
any local physical vector back to a coefficient function on the virtual star at a
vertex `v`. When `A` and `B` have the same bond dimensions, this yields a
canonical endomorphism on the local virtual coefficient space of `A`.

To complete the PEPS Fundamental-Theorem argument, this endomorphism must still
be shown to

1. reconstruct the local tensors of `B`, equivalently that the local image of
   `B` lies in the image of `localTensorMap A v`, and
2. factor into independent edge gauges.

We capture those two requirements as `HasFactorizedLocalGauge`. This isolates
the exact output of the blocked-middle / three-site-MPS reduction in
arXiv:1804.04964 Section 3, and `hasFactorizedLocalGauge_of_localGaugeFormula`
is the final conversion that turns an explicit local gauge formula into that
sharper datum.
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

/-- The canonical local coefficient-space map obtained by pulling the local
`B`-tensor back through the chosen left inverse of `A`. -/
noncomputable def localGaugeMap (A B : Tensor G d)
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

/-- The canonical local gauge map reconstructs the projection of `B`'s
local tensor into the image of `localTensorMap A v`. -/
theorem localGaugeMap_apply_single (A B : Tensor G d)
    (hA : IsVertexInjective A) (hDim : A.bondDim = B.bondDim) (v : V)
    (η : LocalVirtualConfig A v) :
    localTensorMap A v (localGaugeMap A B hA hDim v (Pi.single η (1 : ℂ))) =
      localProjector A hA v (B.component v (castLocalVirtualConfig A B hDim v η)) := by
  rw [localGaugeMap, LinearMap.comp_apply, LinearMap.comp_apply,
    localTensorMap_castLocalCoeffMap_single]
  simp [localProjector, physRealizeLocalOp]

/-- Sharper local hypothesis for PEPS gauge extraction.

This states exactly the two local conclusions still needed from the blocked-middle
reduction in arXiv:1804.04964 Section 3:

1. the local components of `B` lie in the image of `localTensorMap A v`, and
2. the canonical map `localGaugeMap` factorizes into one invertible
   matrix on each incident edge. -/
structure HasFactorizedLocalGauge (A B : Tensor G d) (hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim) (v : V) : Prop where
  projector_fixes :
    ∀ η : LocalVirtualConfig A v,
      localProjector A hA v (B.component v (castLocalVirtualConfig A B hDim v η)) =
        B.component v (castLocalVirtualConfig A B hDim v η)
  factorized_localGaugeMap :
    ∃ Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
      ∀ η η' : LocalVirtualConfig A v,
        localGaugeMap A B hA hDim v (Pi.single η (1 : ℂ)) η' =
          ∏ ie : IncidentEdge G v,
            (↑(Xv ie.1) : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
              (η ie) (η' ie)

/-- Any explicit edgewise local gauge formula at `v` yields the sharper datum
`HasFactorizedLocalGauge`.

This is the final algebraic conversion after the blocked-middle / three-site-MPS
reduction: once that reduction produces invertible incident-edge gauges
realizing the local tensors of `B`, the canonical map pulled back through
`localLeftInverse` is forced to be the same factorized operator. -/
theorem hasFactorizedLocalGauge_of_localGaugeFormula (A B : Tensor G d)
    (hA : IsVertexInjective A) (hDim : A.bondDim = B.bondDim) (v : V)
    (hLocal :
      ∃ Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
        ∀ (η : LocalVirtualConfig A v) (σ : Fin d),
          B.component v (castLocalVirtualConfig A B hDim v η) σ =
            ∑ η' : LocalVirtualConfig A v,
              (∏ ie : IncidentEdge G v,
                (↑(Xv ie.1) : Matrix (Fin (A.bondDim ie.1))
                    (Fin (A.bondDim ie.1)) ℂ) (η ie) (η' ie)) *
                A.component v η' σ) :
    HasFactorizedLocalGauge A B hA hDim v := by
  rcases hLocal with ⟨Xv, hXv⟩
  refine ⟨?_, ⟨Xv, ?_⟩⟩
  · intro η
    let c : LocalVirtualConfig A v → ℂ := fun η' =>
      ∏ ie : IncidentEdge G v,
        (↑(Xv ie.1) : Matrix (Fin (A.bondDim ie.1))
            (Fin (A.bondDim ie.1)) ℂ) (η ie) (η' ie)
    have hcomp :
        B.component v (castLocalVirtualConfig A B hDim v η) =
          localTensorMap A v c := by
      ext σ
      simpa [c, localTensorMap, Fintype.linearCombination_apply] using hXv η σ
    calc
      localProjector A hA v (B.component v (castLocalVirtualConfig A B hDim v η)) =
          localProjector A hA v (localTensorMap A v c) := by rw [hcomp]
      _ = localTensorMap A v c := by simp
      _ = B.component v (castLocalVirtualConfig A B hDim v η) := by rw [hcomp]
  · intro η η'
    let c : LocalVirtualConfig A v → ℂ := fun ξ =>
      ∏ ie : IncidentEdge G v,
        (↑(Xv ie.1) : Matrix (Fin (A.bondDim ie.1))
            (Fin (A.bondDim ie.1)) ℂ) (η ie) (ξ ie)
    have hcomp :
        B.component v (castLocalVirtualConfig A B hDim v η) =
          localTensorMap A v c := by
      ext σ
      simpa [c, localTensorMap, Fintype.linearCombination_apply] using hXv η σ
    have hcand :
        localGaugeMap A B hA hDim v (Pi.single η (1 : ℂ)) = c := by
      ext ξ
      calc
        localGaugeMap A B hA hDim v (Pi.single η (1 : ℂ)) ξ =
            localLeftInverse A hA v
              (B.component v (castLocalVirtualConfig A B hDim v η)) ξ := by
              rw [localGaugeMap, LinearMap.comp_apply, LinearMap.comp_apply,
                localTensorMap_castLocalCoeffMap_single]
        _ = localLeftInverse A hA v (localTensorMap A v c) ξ := by rw [hcomp]
        _ = c ξ := by simp
    simpa [c] using congrArg (fun f : LocalVirtualConfig A v → ℂ => f η') hcand

/-- Abbreviated proposition for the output expected from the edge-centered
blocked-middle / three-site-MPS reduction at a vertex.

The PEPS fundamental theorem requires deriving this proposition from `SameState`:
an incident-edge family of invertible matrices whose local gauge formula already
reconstructs the local tensors of `B` from those of `A`. The next theorem then
turns this explicit local formula into `HasFactorizedLocalGauge`. -/
abbrev BlockedMiddleGaugeFormula (A B : Tensor G d) (_hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim) (v : V) : Prop :=
  ∃ Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
    ∀ (η : LocalVirtualConfig A v) (σ : Fin d),
      B.component v (castLocalVirtualConfig A B hDim v η) σ =
        ∑ η' : LocalVirtualConfig A v,
          (∏ ie : IncidentEdge G v,
            (↑(Xv ie.1) : Matrix (Fin (A.bondDim ie.1))
                (Fin (A.bondDim ie.1)) ℂ) (η ie) (η' ie)) *
            A.component v η' σ

/-- The blocked-middle / three-site-MPS output immediately yields
`HasFactorizedLocalGauge`. -/
theorem hasFactorizedLocalGauge_of_blockedMiddleGaugeFormula (A B : Tensor G d)
    (hA : IsVertexInjective A) (hDim : A.bondDim = B.bondDim) (v : V)
    (hBlocked : BlockedMiddleGaugeFormula A B hA hDim v) :
    HasFactorizedLocalGauge A B hA hDim v :=
  hasFactorizedLocalGauge_of_localGaugeFormula A B hA hDim v hBlocked

/-- Under `HasFactorizedLocalGauge`, one obtains the factorized local-gauge formula at
vertex `v`.

This theorem gives the local factorized gauge relation under `HasFactorizedLocalGauge`.
Deriving that hypothesis from `SameState` remains the blocked-middle /
three-site-MPS reduction, followed by
`hasFactorizedLocalGauge_of_blockedMiddleGaugeFormula`. -/
theorem localGauge_exists_of_factorizedLocalGauge (A B : Tensor G d)
    (hA : IsVertexInjective A) (hDim : A.bondDim = B.bondDim) (v : V)
    (hFactorized : HasFactorizedLocalGauge A B hA hDim v) :
    ∃ (Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
            (∏ ie : IncidentEdge G v,
              (↑(Xv ie.1) : Matrix _ _ ℂ) (η ie) (η' ie)) *
              A.component v η' σ := by
  rcases hFactorized.factorized_localGaugeMap with ⟨Xv, hXv⟩
  refine ⟨Xv, ?_⟩
  intro η σ
  have hproj := congrArg (fun f : Fin d → ℂ => f σ) (hFactorized.projector_fixes η)
  have hspec := congrArg (fun f : Fin d → ℂ => f σ)
    (localGaugeMap_apply_single A B hA hDim v η)
  calc
    B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        (localProjector A hA v
          (B.component v (castLocalVirtualConfig A B hDim v η))) σ := by
          simpa [castLocalVirtualConfig_apply] using hproj.symm
    _ = (localTensorMap A v
          (localGaugeMap A B hA hDim v (Pi.single η (1 : ℂ)))) σ := by
          simpa using hspec.symm
    _ = ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          localGaugeMap A B hA hDim v (Pi.single η (1 : ℂ)) η' *
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
