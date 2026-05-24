import TNLean.PEPS.Defs

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Logic.Equiv.Prod

/-!
# Local virtual operations for injective PEPS tensors

For a PEPS tensor `A` and a vertex `v`, the family
`η ↦ A.component v η` defines a linear map from coefficient functions on local
virtual configurations into the physical space `Fin d → ℂ`. Under
`IsVertexInjective A`, this map is injective, hence admits a left inverse.

This file constructs that left inverse and the induced realization of virtual
endomorphisms as physical linear maps on the local physical space.

## Main results

- `LocalVirtualConfig`: local virtual configurations at a vertex.
- `localVirtualConfigSplitAt`: split off one incident-edge coordinate.
- `localTensorMap`: the linear map from virtual coefficient data to the local
  physical vector.
- `localLeftInverse`: a chosen left inverse under vertex injectivity.
- `localIncidentMatrixOp`: the virtual operation obtained by applying a matrix
  on one incident edge.
- `physRealizeLocalOp`: realization of a virtual endomorphism as a physical
  linear map.
- `physRealizeLocalOp_spec`: the realized physical map agrees with the virtual
  operator on the image of `localTensorMap`.

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3](https://arxiv.org/abs/1804.04964)
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

/-- The incident edges at `v` other than a chosen distinguished edge. -/
abbrev OtherIncidentEdge (v : V) (ie : IncidentEdge G v) : Type _ :=
  { je : IncidentEdge G v // je ≠ ie }

/-- The residual local virtual data after removing one distinguished incident
edge. -/
abbrev ResidualLocalConfig (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) : Type _ :=
  (je : OtherIncidentEdge (G := G) v ie) → Fin (A.bondDim je.1.1)

instance instFintypeOtherIncidentEdge (v : V) (ie : IncidentEdge G v) :
    Fintype (OtherIncidentEdge (G := G) v ie) :=
  inferInstance

instance instFintypeResidualLocalConfig (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) : Fintype (ResidualLocalConfig (G := G) A ie) :=
  inferInstance

/-- Split a local virtual configuration into the coordinate on one distinguished
incident edge and the coordinates on all remaining incident edges. -/
noncomputable def localVirtualConfigSplitAt (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) :
    LocalVirtualConfig A v ≃ Fin (A.bondDim ie.1) × ResidualLocalConfig (G := G) A ie := by
  classical
  simpa [LocalVirtualConfig, ResidualLocalConfig, OtherIncidentEdge] using
    (Equiv.piSplitAt ie fun je : IncidentEdge G v => Fin (A.bondDim je.1))

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_apply_fst (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) (η : LocalVirtualConfig A v) :
    (localVirtualConfigSplitAt (G := G) A ie η).1 = η ie := by
  classical
  simp [localVirtualConfigSplitAt]

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_apply_snd (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) (η : LocalVirtualConfig A v)
    (je : OtherIncidentEdge (G := G) v ie) :
    (localVirtualConfigSplitAt (G := G) A ie η).2 je = η je.1 := by
  classical
  simp [localVirtualConfigSplitAt]

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_symm_apply_fst (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (x : Fin (A.bondDim ie.1) × ResidualLocalConfig (G := G) A ie) :
    (localVirtualConfigSplitAt (G := G) A ie).symm x ie = x.1 := by
  classical
  simp [localVirtualConfigSplitAt]

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_symm_apply_snd (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (x : Fin (A.bondDim ie.1) × ResidualLocalConfig (G := G) A ie)
    (je : OtherIncidentEdge (G := G) v ie) :
    (localVirtualConfigSplitAt (G := G) A ie).symm x je.1 = x.2 je := by
  classical
  simp [localVirtualConfigSplitAt, je.2]

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

/-- The local virtual operation induced by a matrix on one incident edge.

For an incident edge `ie` at `v`, the matrix `M` acts on the `ie` coordinate
and leaves the remaining virtual coordinates fixed. This is the local
linear-algebra operation used in the \(X \mapsto O_1,O_2\) step of
arXiv:1804.04964, Section 3. -/
noncomputable def localIncidentMatrixOp (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    LocalVirtualOp A v where
  toFun c := fun η' =>
    ∑ x : Fin (A.bondDim ie.1),
      M x (η' ie) *
        c ((localVirtualConfigSplitAt (G := G) A ie).symm
          (x, (localVirtualConfigSplitAt (G := G) A ie η').2))
  map_add' c c' := by
    ext η'
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' z c := by
    ext η'
    change
      (∑ x : Fin (A.bondDim ie.1),
        M x (η' ie) *
          (z * c ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2)))) =
      z * ∑ x : Fin (A.bondDim ie.1),
        M x (η' ie) *
          c ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    calc
      M x (η' ie) *
          (z * c ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2))) =
        (M x (η' ie) * z) *
          c ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2)) := by
        rw [← mul_assoc]
      _ = (z * M x (η' ie)) *
          c ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2)) := by
        rw [mul_comm (M x (η' ie)) z]
      _ = z * (M x (η' ie) *
          c ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2))) := by
        rw [mul_assoc]

omit [Fintype V] in
@[simp] theorem localIncidentMatrixOp_apply (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (c : LocalVirtualConfig A v → ℂ) (η' : LocalVirtualConfig A v) :
    localIncidentMatrixOp A ie M c η' =
      ∑ x : Fin (A.bondDim ie.1),
        M x (η' ie) *
          c ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2)) :=
  rfl

/-- Acting on one distinguished-edge basis configuration only changes the
distinguished index and keeps the residual local boundary fixed. -/
theorem localIncidentMatrixOp_single (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (x : Fin (A.bondDim ie.1)) (r : ResidualLocalConfig (G := G) A ie) :
    localIncidentMatrixOp A ie M
      (Pi.single ((localVirtualConfigSplitAt (G := G) A ie).symm (x, r)) (1 : ℂ)) =
      ∑ y : Fin (A.bondDim ie.1),
        Pi.single ((localVirtualConfigSplitAt (G := G) A ie).symm (y, r)) (M x y) := by
  classical
  ext η
  simp only [localIncidentMatrixOp_apply, Finset.sum_apply]
  let φ := localVirtualConfigSplitAt (G := G) A ie
  have hfst : (φ η).1 = η ie := by simp [φ]
  by_cases hres : (φ η).2 = r
  · have hη : φ.symm (η ie, r) = η := by
      have hp : (η ie, r) = φ η := by
        ext <;> simp [hfst, hres]
      rw [hp]
      exact Equiv.symm_apply_apply φ η
    rw [Fintype.sum_eq_single x]
    · rw [Fintype.sum_eq_single (η ie)]
      · have hcfg : φ.symm (x, (φ η).2) = φ.symm (x, r) := by simp [hres]
        rw [hcfg, Pi.single_eq_same, mul_one, hη, Pi.single_eq_same]
      · intro y hy
        have hcfg : φ.symm (y, r) ≠ η := by
          intro h
          apply hy
          have hp := congrArg φ h
          simpa [φ, hfst, hres] using congrArg Prod.fst hp
        rw [Pi.single_eq_of_ne (Ne.symm hcfg)]
    · intro y hy
      have hcfg : φ.symm (y, (φ η).2) ≠ φ.symm (x, r) := by
        intro h
        apply hy
        have hp := congrArg φ h
        simpa using congrArg Prod.fst hp
      rw [Pi.single_eq_of_ne hcfg, mul_zero]
  · rw [Fintype.sum_eq_single x]
    · rw [Fintype.sum_eq_single (η ie)]
      · have hcfg₁ : φ.symm (x, (φ η).2) ≠ φ.symm (x, r) := by
          intro h
          apply hres
          have hp := congrArg φ h
          simpa using congrArg Prod.snd hp
        have hcfg₂ : φ.symm (η ie, r) ≠ η := by
          intro h
          apply hres
          have hp := congrArg φ h
          simpa [φ, hfst] using (congrArg Prod.snd hp).symm
        rw [Pi.single_eq_of_ne hcfg₁, mul_zero, Pi.single_eq_of_ne (Ne.symm hcfg₂)]
      · intro y hy
        have hcfg : φ.symm (y, r) ≠ η := by
          intro h
          apply hy
          have hp := congrArg φ h
          simpa [φ, hfst] using congrArg Prod.fst hp
        rw [Pi.single_eq_of_ne (Ne.symm hcfg)]
    · intro y hy
      have hcfg : φ.symm (y, (φ η).2) ≠ φ.symm (x, r) := by
        intro h
        apply hy
        have hp := congrArg φ h
        simpa using congrArg Prod.fst hp
      rw [Pi.single_eq_of_ne hcfg, mul_zero]

/-- The local tensor map after a one-edge matrix action on a basis virtual
configuration. -/
theorem localTensorMap_localIncidentMatrixOp_single (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (x : Fin (A.bondDim ie.1)) (r : ResidualLocalConfig (G := G) A ie) :
    localTensorMap A v (localIncidentMatrixOp A ie M
      (Pi.single ((localVirtualConfigSplitAt (G := G) A ie).symm (x, r)) (1 : ℂ))) =
      ∑ y : Fin (A.bondDim ie.1),
        M x y • A.component v ((localVirtualConfigSplitAt (G := G) A ie).symm (y, r)) := by
  rw [localIncidentMatrixOp_single]
  simp [map_sum]

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

/-- A matrix acting on one incident virtual edge is realized by a physical
operator on the vertex tensor, under vertex injectivity. -/
theorem localIncidentMatrixOp_physicalRealization (A : Tensor G d)
    (hA : IsVertexInjective A) {v : V} (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    ∃ O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ),
      ∀ c : LocalVirtualConfig A v → ℂ,
        O (localTensorMap A v c) =
          localTensorMap A v (localIncidentMatrixOp A ie M c) :=
  ⟨physRealizeLocalOp A hA v (localIncidentMatrixOp A ie M),
    fun c => physRealizeLocalOp_spec A hA v (localIncidentMatrixOp A ie M) c⟩

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

/-- Pull a local physical operator back to the virtual coefficient space.

This is the local injectivity step used in the \(O_1,O_2 \mapsto W\) part of
arXiv:1804.04964, Section 3: the chosen left inverse identifies the action of a
physical operator on the image of the local tensor map with a virtual operation
on local boundary coefficients. -/
noncomputable def localVirtualOpOfPhysicalOp (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    LocalVirtualOp A v :=
  (localLeftInverse A hA v).comp (O.comp (localTensorMap A v))

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

/-- The virtual pullback realizes the projected physical action on the image of
the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_spec (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (c : LocalVirtualConfig A v → ℂ) :
    localTensorMap A v (localVirtualOpOfPhysicalOp A hA v O c) =
      localProjector A hA v (O (localTensorMap A v c)) := by
  simp [localVirtualOpOfPhysicalOp, localProjector, physRealizeLocalOp]

/-- If a local physical operator preserves the image of the local tensor map,
then its virtual pullback gives exactly the same action on that image. -/
theorem localVirtualOpOfPhysicalOp_realizes_of_projector (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hO : ∀ c : LocalVirtualConfig A v → ℂ,
      localProjector A hA v (O (localTensorMap A v c)) = O (localTensorMap A v c))
    (c : LocalVirtualConfig A v → ℂ) :
    localTensorMap A v (localVirtualOpOfPhysicalOp A hA v O c) =
      O (localTensorMap A v c) := by
  rw [localVirtualOpOfPhysicalOp_spec, hO]

/-- A virtual operator is recovered by pulling back any physical operator that
realizes it on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_eq_of_realizes (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (T : LocalVirtualOp A v)
    (hO : ∀ c : LocalVirtualConfig A v → ℂ,
      O (localTensorMap A v c) = localTensorMap A v (T c)) :
    localVirtualOpOfPhysicalOp A hA v O = T := by
  apply LinearMap.ext
  intro c
  apply hA.localTensorMap_injective v
  calc
    localTensorMap A v (localVirtualOpOfPhysicalOp A hA v O c) =
        localProjector A hA v (O (localTensorMap A v c)) := by
      rw [localVirtualOpOfPhysicalOp_spec]
    _ = localTensorMap A v (T c) := by
      rw [hO c]
      simp

/-- Two physical endpoint operations have the same virtual pullback if their
projected actions agree on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_eq_of_projected_action_eq (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O O' : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hOO' : ∀ c : LocalVirtualConfig A v → ℂ,
      localProjector A hA v (O (localTensorMap A v c)) =
        localProjector A hA v (O' (localTensorMap A v c))) :
    localVirtualOpOfPhysicalOp A hA v O =
      localVirtualOpOfPhysicalOp A hA v O' := by
  apply LinearMap.ext
  intro c
  apply hA.localTensorMap_injective v
  rw [localVirtualOpOfPhysicalOp_spec, localVirtualOpOfPhysicalOp_spec, hOO']

/-- Equality of virtual pullbacks is equivalent to equality of the projected
physical actions on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_eq_iff_projected_action_eq (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O O' : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    localVirtualOpOfPhysicalOp A hA v O =
        localVirtualOpOfPhysicalOp A hA v O' ↔
      ∀ c : LocalVirtualConfig A v → ℂ,
        localProjector A hA v (O (localTensorMap A v c)) =
          localProjector A hA v (O' (localTensorMap A v c)) := by
  constructor
  · intro h c
    rw [← localVirtualOpOfPhysicalOp_spec A hA v O c,
      ← localVirtualOpOfPhysicalOp_spec A hA v O' c, h]
  · exact localVirtualOpOfPhysicalOp_eq_of_projected_action_eq A hA v O O'

/-- Pulling back the canonical physical realization of a virtual operation
recovers the original virtual operation. -/
theorem localVirtualOpOfPhysicalOp_physRealizeLocalOp (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (T : LocalVirtualOp A v) :
    localVirtualOpOfPhysicalOp A hA v (physRealizeLocalOp A hA v T) = T :=
  localVirtualOpOfPhysicalOp_eq_of_realizes A hA v
    (physRealizeLocalOp A hA v T) T
    (physRealizeLocalOp_spec A hA v T)

/-- The physical realization of the virtual pullback of \(O\) is
\(P \circ O \circ P\), where \(P\) is the local projector onto the image of the
local tensor map. -/
theorem physRealizeLocalOp_localVirtualOpOfPhysicalOp (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    physRealizeLocalOp A hA v (localVirtualOpOfPhysicalOp A hA v O) =
      (localProjector A hA v).comp (O.comp (localProjector A hA v)) := by
  ext x
  simp [physRealizeLocalOp, localVirtualOpOfPhysicalOp, localProjector,
    LinearMap.comp_assoc]

end PEPS
end TNLean
