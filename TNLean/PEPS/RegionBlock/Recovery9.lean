import TNLean.PEPS.RegionBlock.Recovery8

/-!
# Region physical-to-virtual recovery: the region resonate reconcile

This file proves the region resonate reconcile `RegionResonateReconcile`
(`TNLean.PEPS.RegionBlock.Recovery8`), the single remaining mathematical content of
remaining obligation 4 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`: for
every inserted matrix `M`, the virtual pullback
`W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`
of the transferred in-region endpoint operator is of incident-matrix form on the
boundary leg `f`.

## Strategy

The region port of `physical_to_virtual_insertion`
(`TNLean.PEPS.InsertionRealization`). The two "endpoints" are the blocked regions
`R` and `univ \ R`, joined by the single boundary edge `f`; there is no middle
block (the region/complement split has empty interior). The inversion tool is the
blocked-region left inverse `regionBlockedLeftInverse` (`Recovery5`) applied to
each block, not the per-vertex split of the edge proof.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The leg-wise pin of the in-region endpoint operator

The non-circular endpoint pin `regionInsertionOp_regionStateVec_pin` evaluates the
in-region endpoint operator of the first tensor, applied to the second tensor's
closed state vector, only at the endpoint physical leg `σ v`. Updating the
in-region physical configuration at the endpoint vertex `v` to an arbitrary value
`a` leaves the closed state vector unchanged (`regionStateVec_update_vmem`) while
moving the evaluation leg to `a`, so the pin extends to every leg. This reads the
*whole output vector* of the in-region endpoint operator on the second tensor's
state vector as the region-inserted coefficient of the first tensor, scanned over
the endpoint physical configuration. -/

/-- **The leg-wise pin of the in-region endpoint operator.** The in-region endpoint
operator of the first tensor from `M.transpose`, applied to the second tensor's
closed state vector and evaluated at an arbitrary physical leg `a`, recovers the
first tensor's region-inserted coefficient of `M` at the endpoint physical
configuration updated to `a`, up to the interior bond product.

This is the non-circular endpoint pin `regionInsertionOp_regionStateVec_pin`
applied to `σ` updated at the endpoint vertex `v` to the value `a`: the state
vector is unchanged by that update (`regionStateVec_update_vmem`), and the updated
endpoint leg reads `a`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertionOp_regionStateVec_pin_leg (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) (a : Fin d) :
    regionInteriorBondProd (G := G) A R •
        (regionInsertionOp (G := G) A R f hvA M.transpose
          (regionStateVec (G := G) B R f σ τ)) a =
      regionInsertedCoeff (G := G) A R f M
        (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) τ := by
  have hpin := regionInsertionOp_regionStateVec_pin A B R f hvA hAB M
    (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
      regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) τ
  rw [regionStateVec_update_vmem B R f σ τ a] at hpin
  rw [← hpin]
  congr 2
  rw [Function.update_self]

/-! ### Extending a realization from the state vectors to all coefficients

The closed state-vector coefficients `stateOpenCoeff B σ τ` span the full local
virtual coefficient space at the in-region endpoint `v`
(`span_stateOpenCoeff_eq_top`). The two sides of the region physical-to-virtual
realization equation are linear in the coefficient, so the realization on the
state vectors alone forces the realization on every coefficient. This is the
region analogue of the basis-expansion step that closes
`physical_to_virtual_insertion` once the resonate inversion has pinned the action
on the tensor vectors. -/

/-- **Extending the realization from the state vectors.** If the in-region endpoint
operator of the first tensor from `M.transpose` agrees, on the second tensor's
closed state vectors, with the matrix insertion of `N.transpose` on the boundary
edge `f`, then it agrees on every local tensor image of the second tensor at `v`.

Both sides are linear in the coefficient, and the closed state-vector coefficients
span the full local virtual coefficient space (`span_stateOpenCoeff_eq_top`), so
equality on the spanning set extends to all coefficients.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertionOp_realizes_of_realizes_on_stateVec (A B : Tensor G d)
    (R : Finset V) (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hB : IsVertexInjective B) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hstate : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertionOp (G := G) A R f hvA M.transpose
          (regionStateVec (G := G) B R f σ τ) =
        localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
          (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose
            (stateOpenCoeff (G := G) B R f σ τ)))
    (c : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) → ℂ) :
    regionInsertionOp (G := G) A R f hvA M.transpose
        (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) =
      localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
        (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose c) := by
  have hspan : Submodule.span ℂ
      (Set.range (fun p : RegionPhysicalConfig (V := V) (d := d) R ×
          RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        stateOpenCoeff (G := G) B R f p.1 p.2)) = ⊤ :=
    span_stateOpenCoeff_eq_top B R f hB hposB
  have hEq :
      (regionInsertionOp (G := G) A R f hvA M.transpose).comp
          (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)) =
        (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)).comp
          (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose) := by
    refine LinearMap.ext_on_range hspan (fun p => ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      ← regionStateVec_eq_localTensorMap B R f p.1 p.2]
    exact hstate p.1 p.2
  exact LinearMap.congr_fun hEq c

/-! ### The interior bond product is positive

The bond-dimension product over the non-boundary edges is a product of positive
bond dimensions, so it is positive. This lets the leg-wise pin cancel the bond
product when comparing the two endpoint operators on the closed state vectors. -/

/-- The interior bond product is positive when every bond dimension is positive. -/
theorem regionInteriorBondProd_pos (A : Tensor G d) (R : Finset V)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) :
    0 < regionInteriorBondProd (G := G) A R := by
  rw [regionInteriorBondProd]
  exact Finset.prod_pos (fun e _ => hposA e)

/-! ### The state-vector realization from the coefficient transfer

If a matrix `N` on the second tensor matches the region-inserted coefficients of
the two tensors, then on the second tensor's closed state vectors the in-region
endpoint operator of the first tensor (from `M.transpose`) agrees with the matrix
insertion of `N.transpose` on the boundary edge. The leg-wise pin reads both sides,
leg by leg, as the matched coefficients scaled by the interior bond product, which
is positive and so cancels. -/

/-- **The state-vector realization from the coefficient transfer.** If `N` matches
the region-inserted coefficients of the two tensors, the in-region endpoint operator
of the first tensor from `M.transpose`, applied to the second tensor's closed state
vector, equals the matrix insertion of `N.transpose` on the boundary edge applied to
the same state vector.

Both sides are vectors in the endpoint physical leg. The leg-wise pin reads the left
side as the first tensor's region-inserted coefficient and the right side (through
the realization of `regionInsertionOp B`) as the second tensor's, each scaled by the
interior bond product; matched coefficients and matched bond products (positive, so
cancellable) give the vector equality.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertionOp_regionStateVec_eq_of_coeff_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hcoeff : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f N σ τ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertionOp (G := G) A R f hvA M.transpose
        (regionStateVec (G := G) B R f σ τ) =
      localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
        (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose
          (stateOpenCoeff (G := G) B R f σ τ)) := by
  -- Rewrite the right side as `regionInsertionOp B … N.transpose` on `B`'s state vector.
  rw [← regionInsertionOp_realizes B R f hvB N.transpose (stateOpenCoeff (G := G) B R f σ τ),
    ← regionStateVec_eq_localTensorMap B R f σ τ]
  -- Compare the two vectors leg by leg.
  funext a
  have hbond : regionInteriorBondProd (G := G) A R = regionInteriorBondProd (G := G) B R :=
    regionInteriorBondProd_congr A B R hDim
  have hpos : 0 < regionInteriorBondProd (G := G) B R :=
    regionInteriorBondProd_pos B R hposB
  -- The leg-wise pins read both sides as the matched coefficients.
  have hL := regionInsertionOp_regionStateVec_pin_leg A B R f hvA hAB M σ τ a
  have hR := regionInsertionOp_regionStateVec_pin_leg B B R f hvB (fun _ => rfl) N σ τ a
  -- The matched coefficients with matched (positive) bond products force the legs equal.
  rw [hbond, hcoeff, ← hR, nsmul_eq_mul, nsmul_eq_mul] at hL
  have hne : (regionInteriorBondProd (G := G) B R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  exact mul_left_cancel₀ hne hL

/-! ### The region resonate reconcile from the coefficient transfer

The region resonate reconcile reduces to the existence of a single matrix `N` on
the second tensor whose region-inserted coefficient matches the first tensor's for
every physical configuration. Given such an `N`, the state-vector realization
(`regionInsertionOp_regionStateVec_eq_of_coeff_eq`) holds, the spanning extension
(`regionInsertionOp_realizes_of_realizes_on_stateVec`) lifts it to every
coefficient, and `localVirtualOpOfPhysicalOpAt_eq_of_realizes` reads off the
incident-matrix form with `P = N.transpose`. This is the assembly of the region
resonate reconcile from the coefficient transfer. -/

/-- **The region resonate reconcile from the coefficient transfer.** If, for the
inserted matrix `M`, there is a matrix `N` on the second tensor matching the
region-inserted coefficients of the two tensors at every physical configuration,
then the virtual pullback of the transferred in-region endpoint operator is of
incident-matrix form on the boundary leg `f`, with read-off matrix `N.transpose`.

The state-vector realization `regionInsertionOp_regionStateVec_eq_of_coeff_eq`,
extended to all coefficients by `regionInsertionOp_realizes_of_realizes_on_stateVec`,
is exactly the hypothesis of `localVirtualOpOfPhysicalOpAt_eq_of_realizes`, which
reads off the incident-matrix form.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isIncidentMatrixForm_of_coeff_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hB : IsVertexInjective B)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hcoeff : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f N σ τ) :
    localVirtualOpOfPhysicalOpAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose := by
  -- The realization on all coefficients, from the realization on the state vectors.
  have hreal : ∀ c : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) → ℂ,
      regionInsertionOp (G := G) A R f hvA M.transpose
          (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) =
        localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
          (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose c) :=
    regionInsertionOp_realizes_of_realizes_on_stateVec A B R f hvA hB hposB M N
      (regionInsertionOp_regionStateVec_eq_of_coeff_eq A B R f hvA hvB hAB hposB hDim M N hcoeff)
  -- Read off the incident-matrix form of the virtual pullback.
  exact localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB
    (regionInsertionOp (G := G) A R f hvA M.transpose)
    (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose) hreal

/-- **The region resonate reconcile from the coefficient transfer.** If, for every
inserted matrix `M`, there is a matrix `N` on the second tensor matching the
region-inserted coefficients of the two tensors at every physical configuration,
then the region resonate reconcile `RegionResonateReconcile` holds.

Each per-matrix incident-matrix form is `isIncidentMatrixForm_of_coeff_eq`, with the
witness `P = N.transpose`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionResonateReconcile_of_coeff_transfer (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hB : IsVertexInjective B)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (htransfer : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ) :
    RegionResonateReconcile (G := G) A B R f hvA hvB := by
  intro M
  obtain ⟨N, hN⟩ := htransfer M
  exact ⟨N.transpose,
    isIncidentMatrixForm_of_coeff_eq A B R f hvA hvB hAB hB hposB hDim M N hN⟩

/-! ### The closed state vector factors through the region and complement blocks

The closed state vector at the in-region endpoint, scaled by the interior bond
product, is the identity-inserted region coefficient at the endpoint physical
configuration updated to the chosen leg. Reading off that identity insertion as a
single boundary-configuration sum (`regionInsertedCoeff_identity`) exhibits the
state vector at each leg as the diagonal contraction of the region block against
the complement block. As a function of the complement physical configuration it
factors through the complement blocked tensor map; as a function of the region
physical configuration it factors through the region blocked tensor map. -/

/-- **The closed state vector as a region/complement contraction.** The interior
bond product times the closed state vector at the in-region endpoint, evaluated at
the leg `a`, equals the single boundary-configuration sum of the region blocked
weight (at `σ` updated to `a` at the endpoint vertex) times the complement blocked
weight.

This is the identity-insertion reading `regionInsertedCoeff_one_eq_stateCoeff`
followed by `regionInsertedCoeff_identity`, with the endpoint physical leg supplied
by the update at the endpoint vertex (`regionStateVec` reads the leg through that
update).

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_regionStateVec (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) (a : Fin d) :
    regionInteriorBondProd (G := G) A R • regionStateVec (G := G) A R f σ τ a =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        regionBlockedWeight (G := G) A R μ
            (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
              regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) *
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R μ) τ := by
  set vmem : {w : V // w ∈ R} :=
    ⟨regionBoundaryEdgeInVertex (G := G) R f, regionBoundaryEdgeInVertex_mem (G := G) R f⟩
    with hvmem
  have hstate : regionStateVec (G := G) A R f σ τ a =
      stateCoeff A (assembleRegionσ (V := V) (d := d) R (Function.update σ vmem a) τ) := rfl
  rw [hstate,
    ← regionInsertedCoeff_one_eq_stateCoeff (G := G) A R f (Function.update σ vmem a) τ,
    regionInsertedCoeff_identity (G := G) A R f (Function.update σ vmem a) τ]

/-! ### The v-side inversion: factoring the first tensor's coefficient through the
second tensor's complement block

The first tensor's region-inserted coefficient, transferred across
`SameState` onto the second tensor's closed state vector by the leg-wise pin and
the state-vector factorization, is — as a function of the complement physical
configuration — in the image of the *second* tensor's complement blocked tensor
map. This is the non-circular complement-block inversion: the complement
dependence runs entirely through the second tensor's complement block (the state
vector is built from the second tensor), so its left inverse reads off a row
function without any membership of the first tensor's coefficient in the second
tensor's region image. -/

/-- The blocked region weight, read off the physical leg by updating the in-region
physical configuration at the endpoint vertex, is the region weight vector. The
open region coefficient is independent of the endpoint physical value
(`regionOpenCoeff_update_vmem`), so the local-tensor factorization of the blocked
region weight (`regionBlockedWeight_eq_localTensorMap`) reads the leg directly. -/
theorem regionBlockedWeight_update_eq_regionWeightVec (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) (a : Fin d) :
    regionBlockedWeight (G := G) A R μ
        (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) =
      regionWeightVec (G := G) A R f μ σ a := by
  rw [regionBlockedWeight_eq_localTensorMap A R f μ
      (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
        regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a),
    regionOpenCoeff_update_vmem A R f μ σ a, Function.update_self, regionWeightVec]

/-- **The second tensor's state vector as a complement-block combination.** The
interior bond product times the second tensor's closed state vector is the
boundary-configuration sum of the complement blocked weights against the region
weight vectors. This rewrites the region/complement contraction
`regionInteriorBondProd_smul_regionStateVec` as a single vector identity in the
endpoint leg. -/
theorem regionInteriorBondProd_smul_regionStateVec_eq_sum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInteriorBondProd (G := G) A R • regionStateVec (G := G) A R f σ τ =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R μ) τ •
          regionWeightVec (G := G) A R f μ σ := by
  funext a
  rw [Pi.smul_apply, regionInteriorBondProd_smul_regionStateVec A R f σ τ a, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, regionBlockedWeight_update_eq_regionWeightVec A R f μ σ a,
    mul_comm]

/-- **The v-side inversion (factoring through the complement block).** The first
tensor's region-inserted coefficient of `M`, as a function of the complement
physical configuration `τ`, is the second tensor's complement blocked tensor map
applied to the row function reading the first tensor's in-region endpoint operator
against the second tensor's region weight vectors at the endpoint leg.

The leg-wise pin reads the coefficient as the first tensor's in-region endpoint
operator on the second tensor's closed state vector at the endpoint leg; the
state-vector factorization
(`regionInteriorBondProd_smul_regionStateVec_eq_sum`) expands the state vector as a
complement-block combination; linearity of the operator and the leg evaluation
moves the operator inside; and reindexing the boundary configurations by the
complement boundary-configuration equivalence presents the result as the complement
blocked tensor map.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_complement_blockedMap_B (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionInsertedCoeff (G := G) A R f M σ τ) =
      regionBlockedTensorMap (G := G) B (Finset.univ \ R)
        (fun ν : RegionBoundaryConfig (G := G) B (Finset.univ \ R) =>
          (regionInsertionOp (G := G) A R f hvA M.transpose
              (regionWeightVec (G := G) B R f
                ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν) σ))
            (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
              regionBoundaryEdgeInVertex_mem (G := G) R f⟩)) := by
  classical
  funext τ
  set v := regionBoundaryEdgeInVertex (G := G) R f with hv
  set vm : {w : V // w ∈ R} := ⟨v, regionBoundaryEdgeInVertex_mem (G := G) R f⟩ with hvm
  set O := regionInsertionOp (G := G) A R f hvA M.transpose with hO
  set E := regionComplementBoundaryConfigEquiv (G := G) B R with hE
  -- The pin reads the coefficient off the operator on `B`'s state vector.
  have hpin := regionInsertionOp_regionStateVec_pin A B R f hvA hAB M σ τ
  rw [← hpin]
  -- Pull the interior bond product (matched across the two tensors) inside the operator.
  have hbond : regionInteriorBondProd (G := G) A R = regionInteriorBondProd (G := G) B R :=
    regionInteriorBondProd_congr A B R hDim
  rw [hbond, ← Pi.smul_apply (regionInteriorBondProd (G := G) B R), ← map_nsmul,
    regionInteriorBondProd_smul_regionStateVec_eq_sum B R f σ τ]
  -- Distribute the operator and the leg evaluation over the boundary-configuration sum.
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  -- Present the sum as the complement blocked tensor map, reindexing by `E`.
  rw [regionBlockedTensorMap_apply]
  rw [← Equiv.sum_comp E
    (fun ν : RegionBoundaryConfig (G := G) B (Finset.univ \ R) =>
      (O (regionWeightVec (G := G) B R f (E.symm ν) σ)) (σ vm) •
        regionBlockedWeight (G := G) B (Finset.univ \ R) ν τ)]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [hE, Equiv.symm_apply_apply, regionComplementBoundaryConfigEquiv_apply,
    smul_eq_mul, mul_comm]

/-- **The complement read-off of the first tensor's coefficient.** The second
tensor's complement blocked left inverse, applied to the first tensor's
region-inserted coefficient viewed as a function of the complement physical
configuration, recovers the row function reading the first tensor's in-region
endpoint operator against the second tensor's region weight vectors at the endpoint
leg.

This is the v-side inversion `regionInsertedCoeff_eq_complement_blockedMap_B`
composed with the left inverse of the complement blocked tensor map
(`regionBlockedLeftInverse_apply_regionBlockedTensorMap`). It is non-circular: the
complement dependence runs through the second tensor's block, so the left inverse
reads the row off without any membership of the first tensor's coefficient in the
second tensor's region image.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedLeftInverse_complement_regionInsertedCoeff_B (A B : Tensor G d)
    (R : Finset V) (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedLeftInverse (G := G) B (Finset.univ \ R) hCB
        (fun τ => regionInsertedCoeff (G := G) A R f M σ τ) =
      (fun ν : RegionBoundaryConfig (G := G) B (Finset.univ \ R) =>
        (regionInsertionOp (G := G) A R f hvA M.transpose
            (regionWeightVec (G := G) B R f
              ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν) σ))
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩)) := by
  rw [regionInsertedCoeff_eq_complement_blockedMap_B A B R f hvA hAB hDim M σ,
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

end PEPS
end TNLean
