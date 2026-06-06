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

/-- Linear independence of the vertex tensor family makes the local tensor map
at that vertex injective. This is the per-vertex form: it depends only on the
single vertex `v`, not on the global `IsVertexInjective` hypothesis. -/
theorem localTensorMap_injective_of_linearIndependent {A : Tensor G d} {v : V}
    (hv : LinearIndependent ℂ (A.component v)) :
    Function.Injective (localTensorMap A v) :=
  hv.fintypeLinearCombination_injective

/-- Kernel form of `localTensorMap_injective_of_linearIndependent`. -/
theorem localTensorMap_ker_eq_bot_of_linearIndependent {A : Tensor G d} {v : V}
    (hv : LinearIndependent ℂ (A.component v)) :
    LinearMap.ker (localTensorMap A v) = ⊥ :=
  LinearMap.ker_eq_bot.mpr <| localTensorMap_injective_of_linearIndependent hv

/-- Vertex injectivity makes the local tensor map injective. -/
theorem IsVertexInjective.localTensorMap_injective {A : Tensor G d}
    (hA : IsVertexInjective A) (v : V) :
    Function.Injective (localTensorMap A v) :=
  localTensorMap_injective_of_linearIndependent (hA v)

/-- Kernel form of `IsVertexInjective.localTensorMap_injective`. -/
theorem IsVertexInjective.localTensorMap_ker_eq_bot {A : Tensor G d}
    (hA : IsVertexInjective A) (v : V) :
    LinearMap.ker (localTensorMap A v) = ⊥ :=
  localTensorMap_ker_eq_bot_of_linearIndependent (hA v)

/-- A chosen left inverse of the local tensor map under per-vertex linear
independence of the tensor family at `v`. -/
noncomputable def localLeftInverseAt (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) :
    (Fin d → ℂ) →ₗ[ℂ] (LocalVirtualConfig A v → ℂ) :=
  ((localTensorMap A v).exists_leftInverse_of_injective
    (localTensorMap_ker_eq_bot_of_linearIndependent hv)).choose

@[simp] theorem localLeftInverseAt_comp_localTensorMap (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) :
    (localLeftInverseAt A hv).comp (localTensorMap A v) = LinearMap.id :=
  ((localTensorMap A v).exists_leftInverse_of_injective
    (localTensorMap_ker_eq_bot_of_linearIndependent hv)).choose_spec

@[simp] theorem localLeftInverseAt_apply_localTensorMap (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (c : LocalVirtualConfig A v → ℂ) :
    localLeftInverseAt A hv (localTensorMap A v c) = c := by
  change ((localLeftInverseAt A hv).comp (localTensorMap A v)) c = c
  rw [localLeftInverseAt_comp_localTensorMap]
  rfl

/-- A chosen left inverse of the local tensor map under vertex injectivity. -/
noncomputable def localLeftInverse (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) : (Fin d → ℂ) →ₗ[ℂ] (LocalVirtualConfig A v → ℂ) :=
  localLeftInverseAt A (hA v)

@[simp] theorem localLeftInverse_comp_localTensorMap (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) :
    (localLeftInverse A hA v).comp (localTensorMap A v) = LinearMap.id :=
  localLeftInverseAt_comp_localTensorMap A (hA v)

@[simp] theorem localLeftInverse_apply_localTensorMap (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (c : LocalVirtualConfig A v → ℂ) :
    localLeftInverse A hA v (localTensorMap A v c) = c :=
  localLeftInverseAt_apply_localTensorMap A (hA v) c

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

omit [Fintype V] in
/-- The identity matrix on one incident edge induces the identity virtual
operation. -/
@[simp] theorem localIncidentMatrixOp_one (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) :
    localIncidentMatrixOp A ie (1 : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) =
      LinearMap.id := by
  classical
  ext c η'
  rw [localIncidentMatrixOp_apply, LinearMap.id_apply]
  rw [Fintype.sum_eq_single (η' ie)]
  · have hcfg :
        (localVirtualConfigSplitAt (G := G) A ie).symm
          (η' ie, (localVirtualConfigSplitAt (G := G) A ie η').2) = η' := by
      have hp :
          (η' ie, (localVirtualConfigSplitAt (G := G) A ie η').2) =
            localVirtualConfigSplitAt (G := G) A ie η' := by
        ext
        · simp
        · rfl
      rw [hp, Equiv.symm_apply_apply]
    rw [Matrix.one_apply_eq, one_mul, hcfg]
  · intro y hy
    rw [Matrix.one_apply_ne hy, zero_mul]

omit [Fintype V] in
/-- The incident-edge matrix operation is additive in the inserted matrix. -/
theorem localIncidentMatrixOp_add (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (M N : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    localIncidentMatrixOp A ie (M + N) =
      localIncidentMatrixOp A ie M + localIncidentMatrixOp A ie N := by
  refine LinearMap.ext fun c => ?_
  funext η'
  rw [LinearMap.add_apply, Pi.add_apply, localIncidentMatrixOp_apply,
    localIncidentMatrixOp_apply, localIncidentMatrixOp_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Matrix.add_apply, add_mul]

omit [Fintype V] in
/-- The incident-edge matrix operation is homogeneous in the inserted matrix. -/
theorem localIncidentMatrixOp_smul (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) (z : ℂ)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    localIncidentMatrixOp A ie (z • M) = z • localIncidentMatrixOp A ie M := by
  refine LinearMap.ext fun c => ?_
  funext η'
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, localIncidentMatrixOp_apply,
    localIncidentMatrixOp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] in
/-- Composing the virtual operations of two matrices on one incident edge gives
the virtual operation of the reversed product: the action on the distinguished
coordinate is matrix multiplication, so the induced operation is an
anti-homomorphism in the matrix. -/
theorem localIncidentMatrixOp_comp (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (M N : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    (localIncidentMatrixOp A ie M).comp (localIncidentMatrixOp A ie N) =
      localIncidentMatrixOp A ie (N * M) := by
  classical
  ext c η'
  rw [LinearMap.comp_apply, localIncidentMatrixOp_apply, localIncidentMatrixOp_apply]
  -- Expand the inner sum, evaluated at the configuration with `ie`-index `x`.
  have hinner : ∀ x : Fin (A.bondDim ie.1),
      localIncidentMatrixOp A ie N c
          ((localVirtualConfigSplitAt (G := G) A ie).symm
            (x, (localVirtualConfigSplitAt (G := G) A ie η').2)) =
        ∑ y : Fin (A.bondDim ie.1),
          N y x *
            c ((localVirtualConfigSplitAt (G := G) A ie).symm
              (y, (localVirtualConfigSplitAt (G := G) A ie η').2)) := by
    intro x
    rw [localIncidentMatrixOp_apply]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [localVirtualConfigSplitAt_symm_apply_fst]
    congr 2
    apply (localVirtualConfigSplitAt (G := G) A ie).injective
    ext
    · simp
    · simp
  simp only [hinner, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

/-- Read off the matrix on one incident edge from a local virtual operation,
using a fixed residual local configuration as a reference frame.

This is the inverse of `localIncidentMatrixOp` on operations of incident-matrix
form: `incidentMatrixOfLocalOp ie r (localIncidentMatrixOp ie M) = M`. -/
noncomputable def incidentMatrixOfLocalOp (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) (r : ResidualLocalConfig (G := G) A ie)
    (T : LocalVirtualOp A v) :
    Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ :=
  fun x y =>
    T (Pi.single ((localVirtualConfigSplitAt (G := G) A ie).symm (x, r)) (1 : ℂ))
      ((localVirtualConfigSplitAt (G := G) A ie).symm (y, r))

/-- Reading off the matrix of an incident-matrix operation recovers the matrix. -/
@[simp] theorem incidentMatrixOfLocalOp_localIncidentMatrixOp (A : Tensor G d)
    {v : V} (ie : IncidentEdge G v) (r : ResidualLocalConfig (G := G) A ie)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    incidentMatrixOfLocalOp A ie r (localIncidentMatrixOp A ie M) = M := by
  classical
  ext x y
  rw [incidentMatrixOfLocalOp, localIncidentMatrixOp_single, Finset.sum_apply]
  rw [Fintype.sum_eq_single y]
  · rw [Pi.single_eq_same]
  · intro z hz
    have hne : (localVirtualConfigSplitAt (G := G) A ie).symm (z, r) ≠
        (localVirtualConfigSplitAt (G := G) A ie).symm (y, r) := by
      intro h
      apply hz
      have hp := congrArg (localVirtualConfigSplitAt (G := G) A ie) h
      simpa using congrArg Prod.fst hp
    rw [Pi.single_eq_of_ne hne.symm]

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

/-- Physical realization of a local virtual endomorphism, under per-vertex
linear independence of the tensor family at `v`.

Since the local tensor map is injective, a virtual operator on the coefficient
space extends to a physical linear map after choosing a left inverse. -/
noncomputable def physRealizeLocalOpAt (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (T : LocalVirtualOp A v) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  (localTensorMap A v).comp <| T.comp (localLeftInverseAt A hv)

/-- The physical realization agrees with the virtual operator on the image of
`localTensorMap`. -/
theorem physRealizeLocalOpAt_spec (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (T : LocalVirtualOp A v)
    (c : LocalVirtualConfig A v → ℂ) :
    physRealizeLocalOpAt A hv T (localTensorMap A v c) =
      localTensorMap A v (T c) := by
  simp [physRealizeLocalOpAt]

/-- Physical realization of a local virtual endomorphism.

Since the local tensor map is injective, a virtual operator on the coefficient
space extends to a physical linear map after choosing a left inverse. -/
noncomputable def physRealizeLocalOp (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (T : LocalVirtualOp A v) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  physRealizeLocalOpAt A (hA v) T

/-- The physical realization agrees with the virtual operator on the image of
`localTensorMap`. -/
theorem physRealizeLocalOp_spec (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (T : LocalVirtualOp A v) (c : LocalVirtualConfig A v → ℂ) :
    physRealizeLocalOp A hA v T (localTensorMap A v c) =
      localTensorMap A v (T c) :=
  physRealizeLocalOpAt_spec A (hA v) T c

/-- A matrix acting on one incident virtual edge is realized by a physical
operator on the vertex tensor, under per-vertex linear independence of the
tensor family at `v`. -/
theorem localIncidentMatrixOp_physicalRealizationAt (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    ∃ O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ),
      ∀ c : LocalVirtualConfig A v → ℂ,
        O (localTensorMap A v c) =
          localTensorMap A v (localIncidentMatrixOp A ie M c) :=
  ⟨physRealizeLocalOpAt A hv (localIncidentMatrixOp A ie M),
    fun c => physRealizeLocalOpAt_spec A hv (localIncidentMatrixOp A ie M) c⟩

/-- A matrix acting on one incident virtual edge is realized by a physical
operator on the vertex tensor, under vertex injectivity. -/
theorem localIncidentMatrixOp_physicalRealization (A : Tensor G d)
    (hA : IsVertexInjective A) {v : V} (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    ∃ O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ),
      ∀ c : LocalVirtualConfig A v → ℂ,
        O (localTensorMap A v c) =
          localTensorMap A v (localIncidentMatrixOp A ie M c) :=
  localIncidentMatrixOp_physicalRealizationAt A (hA v) ie M

/-- Realization is compatible with composition of virtual operators. -/
theorem physRealizeLocalOpAt_comp (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (S T : LocalVirtualOp A v) :
    physRealizeLocalOpAt A hv (S.comp T) =
      (physRealizeLocalOpAt A hv S).comp (physRealizeLocalOpAt A hv T) := by
  ext x
  simp [physRealizeLocalOpAt, LinearMap.comp_assoc]

/-- Realization is additive in the virtual operator. -/
theorem physRealizeLocalOpAt_add (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (S T : LocalVirtualOp A v) :
    physRealizeLocalOpAt A hv (S + T) =
      physRealizeLocalOpAt A hv S + physRealizeLocalOpAt A hv T := by
  ext x
  simp [physRealizeLocalOpAt]

/-- Realization is homogeneous in the virtual operator. -/
theorem physRealizeLocalOpAt_smul (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (z : ℂ) (T : LocalVirtualOp A v) :
    physRealizeLocalOpAt A hv (z • T) = z • physRealizeLocalOpAt A hv T := by
  ext x
  simp [physRealizeLocalOpAt]

/-- Realization is compatible with composition of virtual operators. -/
theorem physRealizeLocalOp_comp (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (S T : LocalVirtualOp A v) :
    physRealizeLocalOp A hA v (S.comp T) =
      (physRealizeLocalOp A hA v S).comp (physRealizeLocalOp A hA v T) :=
  physRealizeLocalOpAt_comp A (hA v) S T

/-- Virtual operators are determined by their physical realizations. -/
theorem physRealizeLocalOpAt_injective (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) :
    Function.Injective (physRealizeLocalOpAt A hv) := by
  intro S T hST
  apply LinearMap.ext
  intro c
  apply funext
  intro η
  have hApply := congrArg (fun F : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) =>
    F (localTensorMap A v c)) hST
  have hVirtual : localTensorMap A v (S c) = localTensorMap A v (T c) := by
    simpa [physRealizeLocalOpAt_spec] using hApply
  exact congrArg (fun f : LocalVirtualConfig A v → ℂ => f η)
    (localTensorMap_injective_of_linearIndependent hv hVirtual)

/-- Virtual operators are determined by their physical realizations. -/
theorem physRealizeLocalOp_injective (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) :
    Function.Injective (physRealizeLocalOp A hA v) :=
  physRealizeLocalOpAt_injective A (hA v)

/-- The virtual identity realizes a projection onto the image of the local
tensor map, under per-vertex linear independence of the tensor family at `v`. -/
noncomputable def localProjectorAt (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  physRealizeLocalOpAt A hv LinearMap.id

/-- The virtual identity realizes a projection onto the image of the local
 tensor map. -/
noncomputable def localProjector (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  localProjectorAt A (hA v)

/-- Pull a local physical operator back to the virtual coefficient space,
under per-vertex linear independence of the tensor family at `v`.

This is the local injectivity step used in the \(O_1,O_2 \mapsto W\) part of
arXiv:1804.04964, Section 3: the chosen left inverse identifies the action of a
physical operator on the image of the local tensor map with a virtual operation
on local boundary coefficients. -/
noncomputable def localVirtualOpOfPhysicalOpAt (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v))
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    LocalVirtualOp A v :=
  (localLeftInverseAt A hv).comp (O.comp (localTensorMap A v))

/-- Pull a local physical operator back to the virtual coefficient space.

This is the local injectivity step used in the \(O_1,O_2 \mapsto W\) part of
arXiv:1804.04964, Section 3: the chosen left inverse identifies the action of a
physical operator on the image of the local tensor map with a virtual operation
on local boundary coefficients. -/
noncomputable def localVirtualOpOfPhysicalOp (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    LocalVirtualOp A v :=
  localVirtualOpOfPhysicalOpAt A (hA v) O

@[simp] theorem localProjectorAt_apply_localTensorMap (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (c : LocalVirtualConfig A v → ℂ) :
    localProjectorAt A hv (localTensorMap A v c) = localTensorMap A v c := by
  simpa [localProjectorAt] using
    (physRealizeLocalOpAt_spec A hv LinearMap.id c)

@[simp] theorem localProjector_apply_localTensorMap (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (c : LocalVirtualConfig A v → ℂ) :
    localProjector A hA v (localTensorMap A v c) = localTensorMap A v c :=
  localProjectorAt_apply_localTensorMap A (hA v) c

@[simp] theorem localProjectorAt_apply_component (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (η : LocalVirtualConfig A v) :
    localProjectorAt A hv (A.component v η) = A.component v η := by
  simpa [localTensorMap_apply_single] using
    (localProjectorAt_apply_localTensorMap A hv (Pi.single η (1 : ℂ)))

@[simp] theorem localProjector_apply_component (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (η : LocalVirtualConfig A v) :
    localProjector A hA v (A.component v η) = A.component v η :=
  localProjectorAt_apply_component A (hA v) η

theorem localProjectorAt_idempotent (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) :
    (localProjectorAt A hv).comp (localProjectorAt A hv) =
      localProjectorAt A hv := by
  simpa [localProjectorAt] using
    (physRealizeLocalOpAt_comp A hv LinearMap.id LinearMap.id).symm

theorem localProjector_idempotent (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) :
    (localProjector A hA v).comp (localProjector A hA v) =
      localProjector A hA v :=
  localProjectorAt_idempotent A (hA v)

/-- The virtual pullback realizes the projected physical action on the image of
the local tensor map. -/
theorem localVirtualOpOfPhysicalOpAt_spec (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v))
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (c : LocalVirtualConfig A v → ℂ) :
    localTensorMap A v (localVirtualOpOfPhysicalOpAt A hv O c) =
      localProjectorAt A hv (O (localTensorMap A v c)) := by
  simp [localVirtualOpOfPhysicalOpAt, localProjectorAt, physRealizeLocalOpAt]

/-- The virtual pullback realizes the projected physical action on the image of
the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_spec (A : Tensor G d) (hA : IsVertexInjective A)
    (v : V) (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (c : LocalVirtualConfig A v → ℂ) :
    localTensorMap A v (localVirtualOpOfPhysicalOp A hA v O c) =
      localProjector A hA v (O (localTensorMap A v c)) :=
  localVirtualOpOfPhysicalOpAt_spec A (hA v) O c

/-- If a local physical operator preserves the image of the local tensor map,
then its virtual pullback gives exactly the same action on that image. -/
theorem localVirtualOpOfPhysicalOpAt_realizes_of_projector (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v))
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hO : ∀ c : LocalVirtualConfig A v → ℂ,
      localProjectorAt A hv (O (localTensorMap A v c)) = O (localTensorMap A v c))
    (c : LocalVirtualConfig A v → ℂ) :
    localTensorMap A v (localVirtualOpOfPhysicalOpAt A hv O c) =
      O (localTensorMap A v c) := by
  rw [localVirtualOpOfPhysicalOpAt_spec, hO]

/-- If a local physical operator preserves the image of the local tensor map,
then its virtual pullback gives exactly the same action on that image. -/
theorem localVirtualOpOfPhysicalOp_realizes_of_projector (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hO : ∀ c : LocalVirtualConfig A v → ℂ,
      localProjector A hA v (O (localTensorMap A v c)) = O (localTensorMap A v c))
    (c : LocalVirtualConfig A v → ℂ) :
    localTensorMap A v (localVirtualOpOfPhysicalOp A hA v O c) =
      O (localTensorMap A v c) :=
  localVirtualOpOfPhysicalOpAt_realizes_of_projector A (hA v) O hO c

/-- A virtual operator is recovered by pulling back any physical operator that
realizes it on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOpAt_eq_of_realizes (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v))
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (T : LocalVirtualOp A v)
    (hO : ∀ c : LocalVirtualConfig A v → ℂ,
      O (localTensorMap A v c) = localTensorMap A v (T c)) :
    localVirtualOpOfPhysicalOpAt A hv O = T := by
  apply LinearMap.ext
  intro c
  apply localTensorMap_injective_of_linearIndependent hv
  calc
    localTensorMap A v (localVirtualOpOfPhysicalOpAt A hv O c) =
        localProjectorAt A hv (O (localTensorMap A v c)) := by
      rw [localVirtualOpOfPhysicalOpAt_spec]
    _ = localTensorMap A v (T c) := by
      rw [hO c]
      simp

/-- A virtual operator is recovered by pulling back any physical operator that
realizes it on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_eq_of_realizes (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (T : LocalVirtualOp A v)
    (hO : ∀ c : LocalVirtualConfig A v → ℂ,
      O (localTensorMap A v c) = localTensorMap A v (T c)) :
    localVirtualOpOfPhysicalOp A hA v O = T :=
  localVirtualOpOfPhysicalOpAt_eq_of_realizes A (hA v) O T hO

/-- Two physical endpoint operations have the same virtual pullback if their
projected actions agree on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOpAt_eq_of_projected_action_eq (A : Tensor G d)
    {v : V} (hv : LinearIndependent ℂ (A.component v))
    (O O' : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hOO' : ∀ c : LocalVirtualConfig A v → ℂ,
      localProjectorAt A hv (O (localTensorMap A v c)) =
        localProjectorAt A hv (O' (localTensorMap A v c))) :
    localVirtualOpOfPhysicalOpAt A hv O =
      localVirtualOpOfPhysicalOpAt A hv O' := by
  apply LinearMap.ext
  intro c
  apply localTensorMap_injective_of_linearIndependent hv
  rw [localVirtualOpOfPhysicalOpAt_spec, localVirtualOpOfPhysicalOpAt_spec, hOO']

/-- Two physical endpoint operations have the same virtual pullback if their
projected actions agree on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_eq_of_projected_action_eq (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O O' : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hOO' : ∀ c : LocalVirtualConfig A v → ℂ,
      localProjector A hA v (O (localTensorMap A v c)) =
        localProjector A hA v (O' (localTensorMap A v c))) :
    localVirtualOpOfPhysicalOp A hA v O =
      localVirtualOpOfPhysicalOp A hA v O' :=
  localVirtualOpOfPhysicalOpAt_eq_of_projected_action_eq A (hA v) O O' hOO'

/-- Equality of virtual pullbacks is equivalent to equality of the projected
physical actions on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOpAt_eq_iff_projected_action_eq (A : Tensor G d)
    {v : V} (hv : LinearIndependent ℂ (A.component v))
    (O O' : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    localVirtualOpOfPhysicalOpAt A hv O =
        localVirtualOpOfPhysicalOpAt A hv O' ↔
      ∀ c : LocalVirtualConfig A v → ℂ,
        localProjectorAt A hv (O (localTensorMap A v c)) =
          localProjectorAt A hv (O' (localTensorMap A v c)) := by
  constructor
  · intro h c
    rw [← localVirtualOpOfPhysicalOpAt_spec A hv O c,
      ← localVirtualOpOfPhysicalOpAt_spec A hv O' c, h]
  · exact localVirtualOpOfPhysicalOpAt_eq_of_projected_action_eq A hv O O'

/-- Equality of virtual pullbacks is equivalent to equality of the projected
physical actions on the image of the local tensor map. -/
theorem localVirtualOpOfPhysicalOp_eq_iff_projected_action_eq (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O O' : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    localVirtualOpOfPhysicalOp A hA v O =
        localVirtualOpOfPhysicalOp A hA v O' ↔
      ∀ c : LocalVirtualConfig A v → ℂ,
        localProjector A hA v (O (localTensorMap A v c)) =
          localProjector A hA v (O' (localTensorMap A v c)) :=
  localVirtualOpOfPhysicalOpAt_eq_iff_projected_action_eq A (hA v) O O'

/-- Pulling back the canonical physical realization of a virtual operation
recovers the original virtual operation. -/
theorem localVirtualOpOfPhysicalOpAt_physRealizeLocalOpAt (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v)) (T : LocalVirtualOp A v) :
    localVirtualOpOfPhysicalOpAt A hv (physRealizeLocalOpAt A hv T) = T :=
  localVirtualOpOfPhysicalOpAt_eq_of_realizes A hv
    (physRealizeLocalOpAt A hv T) T
    (physRealizeLocalOpAt_spec A hv T)

/-- Pulling back the canonical physical realization of a virtual operation
recovers the original virtual operation. -/
theorem localVirtualOpOfPhysicalOp_physRealizeLocalOp (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) (T : LocalVirtualOp A v) :
    localVirtualOpOfPhysicalOp A hA v (physRealizeLocalOp A hA v T) = T :=
  localVirtualOpOfPhysicalOpAt_physRealizeLocalOpAt A (hA v) T

/-- The physical realization of the virtual pullback of \(O\) is
\(P \circ O \circ P\), where \(P\) is the local projector onto the image of the
local tensor map. -/
theorem physRealizeLocalOpAt_localVirtualOpOfPhysicalOpAt (A : Tensor G d) {v : V}
    (hv : LinearIndependent ℂ (A.component v))
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    physRealizeLocalOpAt A hv (localVirtualOpOfPhysicalOpAt A hv O) =
      (localProjectorAt A hv).comp (O.comp (localProjectorAt A hv)) := by
  ext x
  simp [physRealizeLocalOpAt, localVirtualOpOfPhysicalOpAt, localProjectorAt,
    LinearMap.comp_assoc]

/-- The physical realization of the virtual pullback of \(O\) is
\(P \circ O \circ P\), where \(P\) is the local projector onto the image of the
local tensor map. -/
theorem physRealizeLocalOp_localVirtualOpOfPhysicalOp (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    physRealizeLocalOp A hA v (localVirtualOpOfPhysicalOp A hA v O) =
      (localProjector A hA v).comp (O.comp (localProjector A hA v)) :=
  physRealizeLocalOpAt_localVirtualOpOfPhysicalOpAt A (hA v) O

/-- If the projected physical action of \(O\) is the canonical physical
realization of a virtual operation \(T\), then pulling back \(O\) recovers
\(T\). -/
theorem localVirtualOpOfPhysicalOpAt_eq_of_projected_realization_eq
    (A : Tensor G d) {v : V} (hv : LinearIndependent ℂ (A.component v))
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (T : LocalVirtualOp A v)
    (hO : (localProjectorAt A hv).comp (O.comp (localProjectorAt A hv)) =
      physRealizeLocalOpAt A hv T) :
    localVirtualOpOfPhysicalOpAt A hv O = T := by
  apply physRealizeLocalOpAt_injective A hv
  rw [physRealizeLocalOpAt_localVirtualOpOfPhysicalOpAt, hO]

/-- If the projected physical action of \(O\) is the canonical physical
realization of a virtual operation \(T\), then pulling back \(O\) recovers
\(T\). -/
theorem localVirtualOpOfPhysicalOp_eq_of_projected_realization_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (T : LocalVirtualOp A v)
    (hO : (localProjector A hA v).comp (O.comp (localProjector A hA v)) =
      physRealizeLocalOp A hA v T) :
    localVirtualOpOfPhysicalOp A hA v O = T :=
  localVirtualOpOfPhysicalOpAt_eq_of_projected_realization_eq A (hA v) O T hO

/-- The compressed physical action of \(O\) is the canonical physical
realization of \(T\) exactly when the virtual pullback of \(O\) is \(T\). -/
theorem localVirtualOpOfPhysicalOpAt_eq_iff_projected_realization_eq
    (A : Tensor G d) {v : V} (hv : LinearIndependent ℂ (A.component v))
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (T : LocalVirtualOp A v) :
    localVirtualOpOfPhysicalOpAt A hv O = T ↔
      (localProjectorAt A hv).comp (O.comp (localProjectorAt A hv)) =
        physRealizeLocalOpAt A hv T := by
  constructor
  · intro h
    rw [← h, physRealizeLocalOpAt_localVirtualOpOfPhysicalOpAt]
  · exact localVirtualOpOfPhysicalOpAt_eq_of_projected_realization_eq A hv O T

/-- The compressed physical action of \(O\) is the canonical physical
realization of \(T\) exactly when the virtual pullback of \(O\) is \(T\). -/
theorem localVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (v : V)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (T : LocalVirtualOp A v) :
    localVirtualOpOfPhysicalOp A hA v O = T ↔
      (localProjector A hA v).comp (O.comp (localProjector A hA v)) =
        physRealizeLocalOp A hA v T :=
  localVirtualOpOfPhysicalOpAt_eq_iff_projected_realization_eq A (hA v) O T

end PEPS
end TNLean
