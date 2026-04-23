import TNLean.PEPS.Defs

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Local virtual operations for injective PEPS tensors

For a PEPS tensor `A` and a vertex `v`, the family
`η ↦ A.component v η` defines a linear map from coefficient functions on local
virtual configurations into the physical space `Fin d → ℂ`. Under
`IsVertexInjective A`, this map is injective, hence admits a left inverse.

This file packages that left inverse and the induced realization of virtual
endomorphisms as physical linear maps on the local physical space.

## Main results

- `LocalVirtualConfig`: local virtual configurations at a vertex.
- `localTensorMap`: the linear map from virtual coefficient data to the local
  physical vector.
- `localLeftInverse`: a chosen left inverse under vertex injectivity.
- `physRealizeLocalOp`: realization of a virtual endomorphism as a physical
  linear map.
- `physRealizeLocalOp_spec`: the realized physical map agrees with the virtual
  operator on the image of `localTensorMap`.

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, §3](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Local virtual configurations at a vertex. -/
abbrev LocalVirtualConfig (A : Tensor G d) (v : V) : Type _ :=
  (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)

instance instFintypeLocalVirtualConfig (A : Tensor G d) (v : V) :
    Fintype (LocalVirtualConfig A v) :=
  inferInstance

/-- The local tensor map sending a coefficient function on virtual
configurations to the corresponding physical vector. -/
abbrev localTensorMap (A : Tensor G d) (v : V) :
    (LocalVirtualConfig A v → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  Fintype.linearCombination ℂ (A.component v)

@[simp] theorem localTensorMap_apply_single (A : Tensor G d) (v : V)
    (η : LocalVirtualConfig A v) :
    localTensorMap A v (Pi.single η (1 : ℂ)) = A.component v η := by
  simp [localTensorMap, Fintype.linearCombination_apply_single]

/-- Vertex injectivity makes the local tensor map injective. -/
theorem IsVertexInjective.localTensorMap_injective {A : Tensor G d}
    (hA : IsVertexInjective A) (v : V) :
    Function.Injective (localTensorMap A v) :=
  (hA v).fintypeLinearCombination_injective

/-- Kernel form of `IsVertexInjective.localTensorMap_injective`. -/
theorem IsVertexInjective.localTensorMap_ker_eq_bot {A : Tensor G d}
    (hA : IsVertexInjective A) (v : V) :
    LinearMap.ker (localTensorMap A v) = ⊥ :=
  LinearMap.ker_eq_bot.mpr <| hA.localTensorMap_injective v

/-- A chosen left inverse of the local tensor map under vertex injectivity. -/
noncomputable def localLeftInverse (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) : (Fin d → ℂ) →ₗ[ℂ] (LocalVirtualConfig A v → ℂ) :=
  ((localTensorMap A v).exists_leftInverse_of_injective
    (hA.localTensorMap_ker_eq_bot v)).choose

@[simp] theorem localLeftInverse_comp_localTensorMap (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) :
    (localLeftInverse A hA v).comp (localTensorMap A v) = LinearMap.id :=
  ((localTensorMap A v).exists_leftInverse_of_injective
    (hA.localTensorMap_ker_eq_bot v)).choose_spec

@[simp] theorem localLeftInverse_apply_localTensorMap (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (c : LocalVirtualConfig A v → ℂ) :
    localLeftInverse A hA v (localTensorMap A v c) = c := by
  change ((localLeftInverse A hA v).comp (localTensorMap A v)) c = c
  rw [localLeftInverse_comp_localTensorMap]
  rfl

/-- Endomorphisms of the local virtual coefficient space at a vertex. -/
abbrev LocalVirtualOp (A : Tensor G d) (v : V) : Type _ :=
  (LocalVirtualConfig A v → ℂ) →ₗ[ℂ] (LocalVirtualConfig A v → ℂ)

/-- Physical realization of a local virtual endomorphism.

Since the local tensor map is injective, a virtual operator on the coefficient
space extends to a physical linear map after choosing a left inverse. -/
noncomputable def physRealizeLocalOp (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (T : LocalVirtualOp A v) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  (localTensorMap A v).comp <| T.comp (localLeftInverse A hA v)

/-- The physical realization agrees with the virtual operator on the image of
`localTensorMap`. -/
theorem physRealizeLocalOp_spec (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (T : LocalVirtualOp A v) (c : LocalVirtualConfig A v → ℂ) :
    physRealizeLocalOp A hA v T (localTensorMap A v c) =
      localTensorMap A v (T c) := by
  simp [physRealizeLocalOp]

/-- Realization is compatible with composition of virtual operators. -/
theorem physRealizeLocalOp_comp (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (S T : LocalVirtualOp A v) :
    physRealizeLocalOp A hA v (S.comp T) =
      (physRealizeLocalOp A hA v S).comp (physRealizeLocalOp A hA v T) := by
  ext x
  simp [physRealizeLocalOp, LinearMap.comp_assoc]

/-- Virtual operators are determined by their physical realizations. -/
theorem physRealizeLocalOp_injective (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) :
    Function.Injective (physRealizeLocalOp A hA v) := by
  intro S T hST
  apply LinearMap.ext
  intro c
  apply funext
  intro η
  have hApply := congrArg (fun F : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) =>
    F (localTensorMap A v c)) hST
  have hVirtual : localTensorMap A v (S c) = localTensorMap A v (T c) := by
    simpa [physRealizeLocalOp_spec] using hApply
  exact congrArg (fun f : LocalVirtualConfig A v → ℂ => f η)
    (hA.localTensorMap_injective v hVirtual)

/-- The virtual identity realizes a projection onto the image of the local
 tensor map. -/
noncomputable def localProjector (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  physRealizeLocalOp A hA v LinearMap.id

@[simp] theorem localProjector_apply_localTensorMap (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (c : LocalVirtualConfig A v → ℂ) :
    localProjector A hA v (localTensorMap A v c) = localTensorMap A v c := by
  simpa [localProjector] using
    (physRealizeLocalOp_spec A hA v LinearMap.id c)

@[simp] theorem localProjector_apply_component (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (η : LocalVirtualConfig A v) :
    localProjector A hA v (A.component v η) = A.component v η := by
  simpa [localTensorMap_apply_single] using
    (localProjector_apply_localTensorMap A hA v (Pi.single η (1 : ℂ)))

theorem localProjector_idempotent (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) :
    (localProjector A hA v).comp (localProjector A hA v) =
      localProjector A hA v := by
  simpa [localProjector] using
    (physRealizeLocalOp_comp A hA v LinearMap.id LinearMap.id).symm

end PEPS
end TNLean
