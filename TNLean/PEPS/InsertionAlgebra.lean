import TNLean.PEPS.EdgeMiddlePhysical
import TNLean.PEPS.IdentityInsertion
import TNLean.PEPS.InsertionCoefficientRealization
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Edge-blocked insertion algebra for PEPS

This file records the matrix-algebra correspondence obtained from applying the
three-site injective-chain argument to a PEPS blocked around one edge.

The statement follows the proof of Lemma inj_isomorph in
Molnar--Schuch--Verstraete--Cirac, arXiv:1804.04964, Section 3, lines
254--582 of Papers/1804.04964/paper_normal.tex: physical realization of
virtual insertions and the converse physical-to-virtual recovery produce an
algebra isomorphism between the matrix algebras on the chosen bond.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### State and endpoint-operator comparison

The realization sums appearing in `edgeInsertedCoeff_eq_sum_left_physicalRealization`
and `edgeInsertedCoeff_eq_sum_right_physicalRealization` are rewritten as weighted
sums of the edge-blocked PEPS coefficient, with the inserted operator acting on the
endpoint physical leg over the standard basis. Because the open middle weight only
reads the physical configuration on the middle region, updating the configuration at
an endpoint leaves it fixed; this is what lets equality of PEPS states (recorded by
`SameState.edgeBlockedCoeff_eq`) transfer the realization sums from one tensor family
to the other.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/

/-- The open middle weight is unchanged when the physical configuration is updated at
the left endpoint, since the endpoint lies outside the middle region. -/
theorem edgeOpenMiddleWeight_update_left (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (τ : Fin d)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    edgeOpenMiddleWeight (G := G) A e (Function.update σ e.1.1 τ) leftResidual rightResidual =
      edgeOpenMiddleWeight (G := G) A e σ leftResidual rightResidual := by
  classical
  unfold edgeOpenMiddleWeight
  refine Finset.sum_congr rfl ?_
  intro ζ _
  refine Finset.prod_congr rfl ?_
  intro v _
  have hv : v.1 ≠ e.1.1 := (mem_edgeMiddleVertices_iff (G := G) e v.1 |>.mp v.2).1
  rw [Function.update_of_ne hv]

/-- The open middle weight is unchanged when the physical configuration is updated at
the right endpoint, since the endpoint lies outside the middle region. -/
theorem edgeOpenMiddleWeight_update_right (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (τ : Fin d)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    edgeOpenMiddleWeight (G := G) A e (Function.update σ e.1.2 τ) leftResidual rightResidual =
      edgeOpenMiddleWeight (G := G) A e σ leftResidual rightResidual := by
  classical
  unfold edgeOpenMiddleWeight
  refine Finset.sum_congr rfl ?_
  intro ζ _
  refine Finset.prod_congr rfl ?_
  intro v _
  have hv : v.1 ≠ e.1.2 := (mem_edgeMiddleVertices_iff (G := G) e v.1 |>.mp v.2).2
  rw [Function.update_of_ne hv]

/-- The left realization sum equals a weighted sum of the edge-blocked PEPS
coefficient: expanding the inserted operator over the standard basis at the left
endpoint moves the inserted physical action onto the physical configuration, leaving
the contraction of the three-block coefficient.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeRealizationSum_left_eq_sum_edgeBlockedCoeff (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    (∑ β : EdgeBoundaryConfig (G := G) A e,
      O (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
        edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
        A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) =
      ∑ τ : Fin d,
        O (Pi.single τ (1 : ℂ)) (σ e.1.1) *
          edgeBlockedCoeff (G := G) A e (Function.update σ e.1.1 τ) := by
  classical
  have hexpand : ∀ β : EdgeBoundaryConfig (G := G) A e,
      O (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) =
        ∑ τ : Fin d,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) τ *
            O (Pi.single τ (1 : ℂ)) (σ e.1.1) := by
    intro β
    have hsingle : ∀ τ : Fin d,
        (fun j => if τ = j then (1 : ℂ) else 0) = Pi.single τ (1 : ℂ) := by
      intro τ
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [LinearMap.pi_apply_eq_sum_univ O (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β))]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro τ _
    rw [Pi.smul_apply, smul_eq_mul, hsingle τ]
  calc
    (∑ β : EdgeBoundaryConfig (G := G) A e,
        O (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2))
        = ∑ β : EdgeBoundaryConfig (G := G) A e, ∑ τ : Fin d,
            O (Pi.single τ (1 : ℂ)) (σ e.1.1) *
              (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) τ *
                edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
                A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) := by
          refine Finset.sum_congr rfl ?_
          intro β _
          rw [hexpand β, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro τ _
          ring
    _ = ∑ τ : Fin d, ∑ β : EdgeBoundaryConfig (G := G) A e,
            O (Pi.single τ (1 : ℂ)) (σ e.1.1) *
              (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) τ *
                edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
                A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) := by
          rw [Finset.sum_comm]
    _ = ∑ τ : Fin d,
            O (Pi.single τ (1 : ℂ)) (σ e.1.1) *
              edgeBlockedCoeff (G := G) A e (Function.update σ e.1.1 τ) := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [edgeBlockedCoeff, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro β _
          rw [edgeMiddleWeight_eq_edgeOpenMiddleWeight, edgeOpenMiddleWeight_update_left,
            Function.update_self, Function.update_of_ne (edgeLeft_ne_edgeRight e).symm]

/-- The right realization sum equals a weighted sum of the edge-blocked PEPS
coefficient, the right-endpoint mirror of
`edgeRealizationSum_left_eq_sum_edgeBlockedCoeff`.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeRealizationSum_right_eq_sum_edgeBlockedCoeff (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    (∑ β : EdgeBoundaryConfig (G := G) A e,
      A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
        edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
        O (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2)) =
      ∑ τ : Fin d,
        O (Pi.single τ (1 : ℂ)) (σ e.1.2) *
          edgeBlockedCoeff (G := G) A e (Function.update σ e.1.2 τ) := by
  classical
  have hexpand : ∀ β : EdgeBoundaryConfig (G := G) A e,
      O (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2) =
        ∑ τ : Fin d,
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) τ *
            O (Pi.single τ (1 : ℂ)) (σ e.1.2) := by
    intro β
    have hsingle : ∀ τ : Fin d,
        (fun j => if τ = j then (1 : ℂ) else 0) = Pi.single τ (1 : ℂ) := by
      intro τ
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [LinearMap.pi_apply_eq_sum_univ O (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β))]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro τ _
    rw [Pi.smul_apply, smul_eq_mul, hsingle τ]
  calc
    (∑ β : EdgeBoundaryConfig (G := G) A e,
        A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          O (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2))
        = ∑ β : EdgeBoundaryConfig (G := G) A e, ∑ τ : Fin d,
            O (Pi.single τ (1 : ℂ)) (σ e.1.2) *
              (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
                edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
                A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) τ) := by
          refine Finset.sum_congr rfl ?_
          intro β _
          rw [hexpand β, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro τ _
          ring
    _ = ∑ τ : Fin d, ∑ β : EdgeBoundaryConfig (G := G) A e,
            O (Pi.single τ (1 : ℂ)) (σ e.1.2) *
              (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
                edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
                A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) τ) := by
          rw [Finset.sum_comm]
    _ = ∑ τ : Fin d,
            O (Pi.single τ (1 : ℂ)) (σ e.1.2) *
              edgeBlockedCoeff (G := G) A e (Function.update σ e.1.2 τ) := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [edgeBlockedCoeff, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro β _
          rw [edgeMiddleWeight_eq_edgeOpenMiddleWeight, edgeOpenMiddleWeight_update_right,
            Function.update_self, Function.update_of_ne (edgeLeft_ne_edgeRight e)]

/-- Equality of PEPS states transfers the left realization sum between the two tensor
families. Both sides are weighted sums of the edge-blocked coefficient, and
`SameState.edgeBlockedCoeff_eq` matches them termwise.

Source: arXiv:1804.04964, Section 3, lines 1010--1036 of
`Papers/1804.04964/paper_normal.tex` (the two PEPS represent the same state before
blocking). -/
theorem edgeRealizationSum_left_sameState {A B : Tensor G d} (hAB : SameState A B)
    (e : Edge G) (σ : V → Fin d) (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    (∑ β : EdgeBoundaryConfig (G := G) A e,
      O (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
        edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
        A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) =
      ∑ β : EdgeBoundaryConfig (G := G) B e,
        O (B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
          B.component e.1.2 (edgeRightLocalConfig (G := G) B e β) (σ e.1.2) := by
  rw [edgeRealizationSum_left_eq_sum_edgeBlockedCoeff,
    edgeRealizationSum_left_eq_sum_edgeBlockedCoeff]
  refine Finset.sum_congr rfl ?_
  intro τ _
  rw [hAB.edgeBlockedCoeff_eq]

/-- Equality of PEPS states transfers the right realization sum between the two tensor
families, the right-endpoint mirror of `edgeRealizationSum_left_sameState`.

Source: arXiv:1804.04964, Section 3, lines 1010--1036 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeRealizationSum_right_sameState {A B : Tensor G d} (hAB : SameState A B)
    (e : Edge G) (σ : V → Fin d) (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    (∑ β : EdgeBoundaryConfig (G := G) A e,
      A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
        edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
        O (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2)) =
      ∑ β : EdgeBoundaryConfig (G := G) B e,
        B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
          O (B.component e.1.2 (edgeRightLocalConfig (G := G) B e β)) (σ e.1.2) := by
  rw [edgeRealizationSum_right_eq_sum_edgeBlockedCoeff,
    edgeRealizationSum_right_eq_sum_edgeBlockedCoeff]
  refine Finset.sum_congr rfl ?_
  intro τ _
  rw [hAB.edgeBlockedCoeff_eq]

/-! ### The explicit transfer map and its algebra structure

The inserted-matrix correspondence $X \mapsto Y$ is realized as an explicit
composition of three algebra maps on the chosen edge:

* insert $X$ on the right endpoint of the first family and physically realize the
  resulting virtual operation (`edgeRightInsertionOp`), an algebra
  anti-homomorphism in $X$ by `localIncidentMatrixOp_comp` and
  `physRealizeLocalOpAt_comp`;
* transfer this physical operator to the second family across `SameState`, where
  `physical_to_virtual_insertion` shows it is realized by a matrix insertion on
  the second family's right endpoint;
* read off that matrix (`incidentMatrixOfLocalOp` after the virtual pullback
  `localVirtualOpOfPhysicalOpAt`).

Because each step preserves composition, the composite $X \mapsto Y$ is an algebra
homomorphism, supplying the multiplicativity invisible from the coefficient
identity alone.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/

/-- The physical operator on the right-endpoint tensor obtained by inserting the
matrix `X` on the chosen bond and realizing it through the endpoint tensor.

This is the right half of the local $X \mapsto O_1, O_2$ realization, taken in the
canonical (left-inverse) form so that its dependence on `X` is functorial. -/
noncomputable def edgeRightInsertionOp (A : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.2))
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  physRealizeLocalOpAt A hvA (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X)

/-- The right-endpoint insertion operator realizes the inserted matrix on the
image of the local tensor map. -/
theorem edgeRightInsertionOp_realizes (A : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.2))
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (c : LocalVirtualConfig A e.1.2 → ℂ) :
    edgeRightInsertionOp A e hvA X (localTensorMap A e.1.2 c) =
      localTensorMap A e.1.2
        (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X c) :=
  physRealizeLocalOpAt_spec A hvA
    (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X) c

/-- The right-endpoint insertion operator is an algebra anti-homomorphism in the
inserted matrix: inserting a product realizes the composite in reverse order. -/
theorem edgeRightInsertionOp_mul (A : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.2))
    (X X' : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeRightInsertionOp A e hvA (X * X') =
      (edgeRightInsertionOp A e hvA X').comp (edgeRightInsertionOp A e hvA X) := by
  have hop : localIncidentMatrixOp A (edgeRightIncident (G := G) e) (X * X') =
      (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X').comp
        (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X) :=
    (localIncidentMatrixOp_comp A (edgeRightIncident (G := G) e) X' X).symm
  rw [edgeRightInsertionOp, edgeRightInsertionOp, edgeRightInsertionOp, hop,
    physRealizeLocalOpAt_comp]

/-- The right-endpoint insertion operator is additive in the inserted matrix. -/
theorem edgeRightInsertionOp_add (A : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.2))
    (X X' : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeRightInsertionOp A e hvA (X + X') =
      edgeRightInsertionOp A e hvA X + edgeRightInsertionOp A e hvA X' := by
  have hop : localIncidentMatrixOp A (edgeRightIncident (G := G) e) (X + X') =
      localIncidentMatrixOp A (edgeRightIncident (G := G) e) X +
        localIncidentMatrixOp A (edgeRightIncident (G := G) e) X' :=
    localIncidentMatrixOp_add A (edgeRightIncident (G := G) e) X X'
  rw [edgeRightInsertionOp, edgeRightInsertionOp, edgeRightInsertionOp, hop,
    physRealizeLocalOpAt_add]

/-- The right-endpoint insertion operator is homogeneous in the inserted matrix. -/
theorem edgeRightInsertionOp_smul (A : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.2)) (z : ℂ)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeRightInsertionOp A e hvA (z • X) = z • edgeRightInsertionOp A e hvA X := by
  have hop : localIncidentMatrixOp A (edgeRightIncident (G := G) e) (z • X) =
      z • localIncidentMatrixOp A (edgeRightIncident (G := G) e) X :=
    localIncidentMatrixOp_smul A (edgeRightIncident (G := G) e) z X
  rw [edgeRightInsertionOp, edgeRightInsertionOp, hop, physRealizeLocalOpAt_smul]

/-- A reference residual configuration on an arbitrary incident edge, available
when every bond dimension is positive. -/
noncomputable def edgeIncidentReferenceResidual (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) (hposA : ∀ f : Edge G, 0 < A.bondDim f) :
    ResidualLocalConfig (G := G) A ie :=
  fun je => ⟨0, hposA je.1.1⟩

/-- A matrix insertion on an incident edge is determined by the physical operator
it realizes on the image of the local tensor map. This applies at either
endpoint of the chosen edge. -/
theorem edge_matrix_unique_of_realizes (B : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (hvB : LinearIndependent ℂ (B.component v))
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M M' : Matrix (Fin (B.bondDim ie.1)) (Fin (B.bondDim ie.1)) ℂ)
    (hM : ∀ c : LocalVirtualConfig B v → ℂ,
      O (localTensorMap B v c) =
        localTensorMap B v (localIncidentMatrixOp B ie M c))
    (hM' : ∀ c : LocalVirtualConfig B v → ℂ,
      O (localTensorMap B v c) =
        localTensorMap B v (localIncidentMatrixOp B ie M' c)) :
    M = M' := by
  have h1 : localIncidentMatrixOp B ie M = localVirtualOpOfPhysicalOpAt B hvB O :=
    (localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB O _ hM).symm
  have h2 : localIncidentMatrixOp B ie M' = localVirtualOpOfPhysicalOpAt B hvB O :=
    (localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB O _ hM').symm
  have hops : localIncidentMatrixOp B ie M = localIncidentMatrixOp B ie M' :=
    h1.trans h2.symm
  have := congrArg
    (incidentMatrixOfLocalOp B ie (edgeIncidentReferenceResidual B ie hposB)) hops
  simpa [incidentMatrixOfLocalOp_localIncidentMatrixOp] using this

/-- The matrix on the second family's bond obtained by transferring the
right-endpoint insertion operator of the first family and reading it off through
the virtual pullback.

`edgeTransferMatrix A B e hvA hvB hposB X` is the explicit $X \mapsto Y$ map: it
realizes `edgeRightInsertionOp A hvA e X` as a matrix insertion on the second
family's right endpoint. -/
noncomputable def edgeTransferMatrix (A B : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.2))
    (hvB : LinearIndependent ℂ (B.component e.1.2))
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ :=
  incidentMatrixOfLocalOp B (edgeRightIncident (G := G) e)
    (edgeIncidentReferenceResidual B (edgeRightIncident (G := G) e) hposB)
    (localVirtualOpOfPhysicalOpAt B hvB (edgeRightInsertionOp A e hvA X))

/-- The right-endpoint insertion operator of the first family, transferred to the
second family across `SameState`, is realized by the matrix insertion
`edgeTransferMatrix … X` on the second family's right endpoint.

This is the load-bearing characterization of the transfer matrix: it says the
explicit composition behind `edgeTransferMatrix` agrees with the matrix
recovered by `physical_to_virtual_insertion`. -/
theorem edgeRightInsertionOp_realizes_edgeTransferMatrix
    (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    ∀ c : LocalVirtualConfig B e.1.2 → ℂ,
      edgeRightInsertionOp A e hA.endpoint_linearIndependent.2 X
          (localTensorMap B e.1.2 c) =
        localTensorMap B e.1.2
          (localIncidentMatrixOp B (edgeRightIncident (G := G) e)
            (edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
              hB.endpoint_linearIndependent.2 hposB X) c) := by
  classical
  obtain ⟨huA, hvA⟩ := hA.endpoint_linearIndependent
  obtain ⟨huB, hvB⟩ := hB.endpoint_linearIndependent
  set O₁ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
    physRealizeLocalOpAt A huA
      (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) X.transpose) with hO₁def
  set O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := edgeRightInsertionOp A e hvA X with hO₂def
  have hO₁ : ∀ c : LocalVirtualConfig A e.1.1 → ℂ,
      O₁ (localTensorMap A e.1.1 c) =
        localTensorMap A e.1.1
          (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) X.transpose c) :=
    fun c => physRealizeLocalOpAt_spec A huA
      (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) X.transpose) c
  have hO₂ : ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
      O₂ (localTensorMap A e.1.2 c) =
        localTensorMap A e.1.2
          (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X c) :=
    fun c => physRealizeLocalOpAt_spec A hvA
      (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X) c
  have hAleft : ∀ σ : V → Fin d,
      edgeInsertedCoeff (G := G) A e σ X =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2) := fun σ =>
    edgeInsertedCoeff_eq_sum_left_physicalRealization (G := G) A e σ X O₁ hO₁
  have hAright : ∀ σ : V → Fin d,
      edgeInsertedCoeff (G := G) A e σ X =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2) := fun σ =>
    edgeInsertedCoeff_eq_sum_right_physicalRealization (G := G) A e σ X O₂ hO₂
  have hEqB : ∀ σ : V → Fin d,
      (∑ β : EdgeBoundaryConfig (G := G) B e,
        O₁ (B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
          B.component e.1.2 (edgeRightLocalConfig (G := G) B e β) (σ e.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G) B e,
          B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
            O₂ (B.component e.1.2 (edgeRightLocalConfig (G := G) B e β)) (σ e.1.2) := by
    intro σ
    rw [← edgeRealizationSum_left_sameState hAB e σ O₁,
      ← edgeRealizationSum_right_sameState hAB e σ O₂, ← hAleft σ, ← hAright σ]
  obtain ⟨Y, _hYleft, hYright⟩ :=
    physical_to_virtual_insertion (G := G) B e hB hposB O₁ O₂ hEqB
  -- The recovered matrix `Y` equals the read-off `edgeTransferMatrix`.
  have hpull : localVirtualOpOfPhysicalOpAt B hvB O₂ =
      localIncidentMatrixOp B (edgeRightIncident (G := G) e) Y :=
    localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB O₂
      (localIncidentMatrixOp B (edgeRightIncident (G := G) e) Y) hYright
  have hYeq : edgeTransferMatrix A B e hvA hvB hposB X = Y := by
    rw [edgeTransferMatrix, ← hO₂def, hpull, incidentMatrixOfLocalOp_localIncidentMatrixOp]
  rw [hYeq]
  exact hYright

/-- The transfer map sends a product of inserted matrices to the product of the
transferred matrices: the explicit composition behind `edgeTransferMatrix` is
multiplicative. -/
theorem edgeTransferMatrix_mul (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X X' : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
        hB.endpoint_linearIndependent.2 hposB (X * X') =
      edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
          hB.endpoint_linearIndependent.2 hposB X *
        edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
          hB.endpoint_linearIndependent.2 hposB X' := by
  obtain ⟨_huA, hvA⟩ := hA.endpoint_linearIndependent
  obtain ⟨_huB, hvB⟩ := hB.endpoint_linearIndependent
  set YX := edgeTransferMatrix A B e hvA hvB hposB X with hYX
  set YX' := edgeTransferMatrix A B e hvA hvB hposB X' with hYX'
  -- The transferred operator of the product realizes both `transfer (X*X')` and
  -- `transfer X * transfer X'`; uniqueness on `B` identifies them.
  refine edge_matrix_unique_of_realizes B (edgeRightIncident (G := G) e) hvB hposB
    (edgeRightInsertionOp A e hvA (X * X')) _ _
    (edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB (X * X')) ?_
  -- Realize via the anti-homomorphism of `edgeRightInsertionOp` and the
  -- composite-pullback structure.
  intro c
  rw [edgeRightInsertionOp_mul, LinearMap.comp_apply,
    edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB X,
    edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB X']
  congr 1
  rw [← hYX, ← hYX']
  exact congrFun (congrArg DFunLike.coe
    (localIncidentMatrixOp_comp B (edgeRightIncident (G := G) e) YX' YX)) _

/-- The transfer map is additive. -/
theorem edgeTransferMatrix_add (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X X' : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
        hB.endpoint_linearIndependent.2 hposB (X + X') =
      edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
          hB.endpoint_linearIndependent.2 hposB X +
        edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
          hB.endpoint_linearIndependent.2 hposB X' := by
  obtain ⟨_huA, hvA⟩ := hA.endpoint_linearIndependent
  obtain ⟨_huB, hvB⟩ := hB.endpoint_linearIndependent
  set YX := edgeTransferMatrix A B e hvA hvB hposB X with hYX
  set YX' := edgeTransferMatrix A B e hvA hvB hposB X' with hYX'
  refine edge_matrix_unique_of_realizes B (edgeRightIncident (G := G) e) hvB hposB
    (edgeRightInsertionOp A e hvA (X + X')) _ _
    (edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB (X + X')) ?_
  intro c
  rw [edgeRightInsertionOp_add, LinearMap.add_apply,
    edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB X,
    edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB X',
    ← map_add]
  congr 1
  rw [← hYX, ← hYX']
  exact (congrFun (congrArg DFunLike.coe
    (localIncidentMatrixOp_add B (edgeRightIncident (G := G) e) YX YX')) c).symm

/-- The transfer map is homogeneous. -/
theorem edgeTransferMatrix_smul (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (z : ℂ) (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
        hB.endpoint_linearIndependent.2 hposB (z • X) =
      z • edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
        hB.endpoint_linearIndependent.2 hposB X := by
  obtain ⟨_huA, hvA⟩ := hA.endpoint_linearIndependent
  obtain ⟨_huB, hvB⟩ := hB.endpoint_linearIndependent
  set YX := edgeTransferMatrix A B e hvA hvB hposB X with hYX
  refine edge_matrix_unique_of_realizes B (edgeRightIncident (G := G) e) hvB hposB
    (edgeRightInsertionOp A e hvA (z • X)) _ _
    (edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB (z • X)) ?_
  intro c
  rw [edgeRightInsertionOp_smul, LinearMap.smul_apply,
    edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB X,
    ← map_smul]
  congr 1
  rw [← hYX]
  exact (congrFun (congrArg DFunLike.coe
    (localIncidentMatrixOp_smul B (edgeRightIncident (G := G) e) z YX)) c).symm

/-- The edge-inserted coefficient is unchanged by the transfer map: inserting `X`
in the first family equals inserting `edgeTransferMatrix … X` in the second
family at every physical configuration.

This is the coefficient identity of `exists_edgeInsertedCoeff_eq`, made functional
with the explicit transfer matrix. -/
theorem edgeTransferMatrix_edgeInsertedCoeff (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) (σ : V → Fin d) :
    edgeInsertedCoeff (G := G) A e σ X =
      edgeInsertedCoeff (G := G) B e σ
        (edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
          hB.endpoint_linearIndependent.2 hposB X) := by
  obtain ⟨_huA, hvA⟩ := hA.endpoint_linearIndependent
  set O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := edgeRightInsertionOp A e hvA X with hO₂def
  have hO₂A : ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
      O₂ (localTensorMap A e.1.2 c) =
        localTensorMap A e.1.2
          (localIncidentMatrixOp A (edgeRightIncident (G := G) e) X c) :=
    fun c => edgeRightInsertionOp_realizes A e hvA X c
  have hO₂B : ∀ c : LocalVirtualConfig B e.1.2 → ℂ,
      O₂ (localTensorMap B e.1.2 c) =
        localTensorMap B e.1.2
          (localIncidentMatrixOp B (edgeRightIncident (G := G) e)
            (edgeTransferMatrix A B e hvA hB.endpoint_linearIndependent.2 hposB X) c) :=
    edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB X
  rw [edgeInsertedCoeff_eq_sum_right_physicalRealization (G := G) A e σ X O₂ hO₂A,
    edgeRealizationSum_right_sameState hAB e σ O₂,
    ← edgeInsertedCoeff_eq_sum_right_physicalRealization (G := G) B e σ _ O₂ hO₂B]

/-- For each matrix `X` inserted on the chosen bond of the first blocked PEPS,
there is a matrix `Y` on the corresponding bond of the second blocked PEPS
giving the same edge-inserted coefficient at every physical configuration.

This is the inserted-coefficient correspondence $X \mapsto Y$ of Lemma
inj_isomorph, without the algebra structure. The witness is the explicit
transfer matrix, and the coefficient identity is
`edgeTransferMatrix_edgeInsertedCoeff`.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`; the displayed correspondence
$X \mapsto Y$ is at lines 564--582. -/
theorem exists_edgeInsertedCoeff_eq
    (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    ∃ Y : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ,
      ∀ σ : V → Fin d,
        edgeInsertedCoeff (G := G) A e σ X = edgeInsertedCoeff (G := G) B e σ Y :=
  ⟨edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
      hB.endpoint_linearIndependent.2 hposB X,
    fun σ => edgeTransferMatrix_edgeInsertedCoeff A B e hA hB hAB hposB X σ⟩

/-! ### Injectivity of the edge-inserted coefficient and the algebra equivalence

The transfer map carries an algebra structure. To obtain an algebra
isomorphism, the inserted coefficient must determine the inserted matrix:
two matrices giving the same edge-inserted coefficient at every physical
configuration are equal (`edgeInsertedCoeff_injective`). This is the
inverse-direction content of the resonate inversion behind
`physical_to_virtual_insertion`. Together with the coefficient identity it
supplies `map_one` (`edgeTransferMatrix_one`), the algebra homomorphism
(`edgeTransferAlgHom`), the two-sided inverse from the symmetric construction
(`edgeTransferAlgHom_comp_self`), and the algebra equivalence
(`edgeTransferAlgEquiv`).

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/

/-- **Injectivity of the edge-inserted coefficient in the inserted matrix.**

If two matrices give the same edge-inserted coefficient at every physical
configuration, they are equal. Realizing the first matrix on the right endpoint
(`edgeRightInsertionOp`) and the transpose of the second on the left endpoint,
the equality of inserted coefficients is exactly the hypothesis of the resonate
inversion `physical_to_virtual_insertion`, which recovers a single matrix
realized on both endpoints. Endpoint uniqueness (`edge_matrix_unique_of_realizes`)
identifies that matrix with each of the two, forcing them equal. Positivity makes
the endpoint reference residuals available.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, the inverse direction of
the resonate inversion `eq:inj_O->X_argument`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeInsertedCoeff_injective (B : Tensor G d) (e : Edge G)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (M M' : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)
    (hMM' : ∀ σ : V → Fin d,
      edgeInsertedCoeff (G := G) B e σ M = edgeInsertedCoeff (G := G) B e σ M') :
    M = M' := by
  classical
  obtain ⟨huB, hvB⟩ := hB.endpoint_linearIndependent
  -- Realize `M` on the right endpoint and `M'.transpose` on the left endpoint.
  set O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := edgeRightInsertionOp B e hvB M with hO₂def
  have hO₂ : ∀ c : LocalVirtualConfig B e.1.2 → ℂ,
      O₂ (localTensorMap B e.1.2 c) =
        localTensorMap B e.1.2
          (localIncidentMatrixOp B (edgeRightIncident (G := G) e) M c) :=
    fun c => edgeRightInsertionOp_realizes B e hvB M c
  obtain ⟨O₁, hO₁⟩ := localIncidentMatrixOp_physicalRealizationAt
    (A := B) huB (edgeLeftIncident (G := G) e) M'.transpose
  -- The two physical realizations have equal contraction sums.
  have hEq : ∀ σ : V → Fin d,
      (∑ β : EdgeBoundaryConfig (G := G) B e,
        O₁ (B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
          B.component e.1.2 (edgeRightLocalConfig (G := G) B e β) (σ e.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G) B e,
          B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
            O₂ (B.component e.1.2 (edgeRightLocalConfig (G := G) B e β)) (σ e.1.2) := by
    intro σ
    rw [← edgeInsertedCoeff_eq_sum_left_physicalRealization (G := G) B e σ M' O₁ hO₁,
      ← edgeInsertedCoeff_eq_sum_right_physicalRealization (G := G) B e σ M O₂ hO₂]
    exact (hMM' σ).symm
  -- Recover a single matrix `N` realized on both endpoints.
  obtain ⟨N, hNleft, hNright⟩ :=
    physical_to_virtual_insertion (G := G) B e hB hposB O₁ O₂ hEq
  -- Right endpoint: `O₂` realizes both `M` and `N`, so `M = N`.
  have hMN : M = N :=
    edge_matrix_unique_of_realizes B (edgeRightIncident (G := G) e) hvB hposB O₂ M N hO₂ hNright
  -- Left endpoint: `O₁` realizes both `M'.transpose` and `N.transpose`, so `M' = N`.
  have hM'N : M'.transpose = N.transpose :=
    edge_matrix_unique_of_realizes B (edgeLeftIncident (G := G) e) huB hposB O₁
      M'.transpose N.transpose hO₁ hNleft
  have hM'eqN : M' = N := by
    have := congrArg Matrix.transpose hM'N
    simpa using this
  rw [hMN, hM'eqN]

/-- The transfer map packaged as a `ℂ`-linear map, using additivity and
homogeneity of `edgeTransferMatrix`. -/
noncomputable def edgeTransferLinearMap (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f) :
    Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →ₗ[ℂ]
      Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ where
  toFun X := edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
    hB.endpoint_linearIndependent.2 hposB X
  map_add' X X' := edgeTransferMatrix_add A B e hA hB hAB hposB X X'
  map_smul' z X := edgeTransferMatrix_smul A B e hA hB hAB hposB z X

/-- The transfer map sends the identity matrix to the identity matrix.

By the coefficient identity, inserting `edgeTransferMatrix … 1` in the second
family has the same coefficient as inserting `1` in the first family, which is
the original state coefficient; equality of states matches it to inserting `1`
in the second family, and injectivity of the inserted coefficient identifies the
two matrices. -/
theorem edgeTransferMatrix_one (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f) :
    edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
        hB.endpoint_linearIndependent.2 hposB 1 = 1 := by
  refine edgeInsertedCoeff_injective B e hB hposB _ 1 (fun σ => ?_)
  rw [← edgeTransferMatrix_edgeInsertedCoeff A B e hA hB hAB hposB 1 σ]
  exact hAB.edgeInsertedCoeff_identity_eq e σ

/-- The transfer map packaged as a `ℂ`-algebra homomorphism, using
multiplicativity and the identity-preservation of `edgeTransferMatrix`. -/
noncomputable def edgeTransferAlgHom (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f) :
    Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →ₐ[ℂ]
      Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ :=
  AlgHom.ofLinearMap (edgeTransferLinearMap A B e hA hB hAB hposB)
    (edgeTransferMatrix_one A B e hA hB hAB hposB)
    (fun X X' => edgeTransferMatrix_mul A B e hA hB hAB hposB X X')

theorem edgeTransferAlgHom_apply (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeTransferAlgHom A B e hA hB hAB hposB X =
      edgeTransferMatrix A B e hA.endpoint_linearIndependent.2
        hB.endpoint_linearIndependent.2 hposB X :=
  rfl

/-- The forward and backward transfer maps are mutually inverse: composing the
transfer from the second family back to the first with the transfer from the
first to the second leaves every inserted matrix unchanged, by the coefficient
identity in both directions and injectivity of the inserted coefficient. -/
theorem edgeTransferAlgHom_comp_self (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposA : ∀ f : Edge G, 0 < A.bondDim f) (hposB : ∀ f : Edge G, 0 < B.bondDim f) :
    (edgeTransferAlgHom B A e hB hA hAB.symm hposA).comp
        (edgeTransferAlgHom A B e hA hB hAB hposB) = AlgHom.id ℂ _ := by
  refine AlgHom.ext (fun X => ?_)
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  refine edgeInsertedCoeff_injective A e hA hposA _ X (fun σ => ?_)
  rw [edgeTransferAlgHom_apply, edgeTransferAlgHom_apply,
    ← edgeTransferMatrix_edgeInsertedCoeff B A e hB hA hAB.symm hposA _ σ,
    ← edgeTransferMatrix_edgeInsertedCoeff A B e hA hB hAB hposB X σ]

/-- The transfer map as a `ℂ`-algebra equivalence between the full matrix
algebras on the chosen bond, with the backward transfer as two-sided inverse. -/
noncomputable def edgeTransferAlgEquiv (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposA : ∀ f : Edge G, 0 < A.bondDim f) (hposB : ∀ f : Edge G, 0 < B.bondDim f) :
    Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ :=
  AlgEquiv.ofAlgHom (edgeTransferAlgHom A B e hA hB hAB hposB)
    (edgeTransferAlgHom B A e hB hA hAB.symm hposA)
    (edgeTransferAlgHom_comp_self B A e hB hA hAB.symm hposB hposA)
    (edgeTransferAlgHom_comp_self A B e hA hB hAB hposA hposB)

/-- The algebra-isomorphism property obtained by comparing matrix insertions on an
edge-blocked PEPS pair.

The existentially quantified algebra equivalence is the map $X \mapsto Y$
between the full matrix algebras on the chosen virtual bond. The coefficient
identity says that inserting $X$ in the first blocked PEPS has the same
coefficient as inserting the corresponding matrix in the second blocked PEPS.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, especially lines
279--282 and 571--582 of Papers/1804.04964/paper_normal.tex. -/
def IsEdgeBlockedInsertionAlgebraIsomorphism (A B : Tensor G d) (e : Edge G) : Prop :=
  ∃ Φ :
    Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ,
    ∀ (σ : V → Fin d) (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ X =
        edgeInsertedCoeff (G := G) B e σ (Φ X)

/-! ### Post-absorption inserted-edge comparison -/

/-- Post-absorption equality of all inserted-edge coefficients.

Source: arXiv:1804.04964, Section 3, `eq:inj_equal_edge`
(`Papers/1804.04964/paper_normal.tex:1037-1065`). After absorbing the edge
gauges into the modified second tensor family $\widetilde B$, for every edge
and every inserted matrix, the first PEPS and $\widetilde B$ give the same
edge-inserted coefficient. -/
structure PostAbsorptionEdgeInsertionEquality (A Btilde : Tensor G d) : Prop where
  /-- The absorbed tensor family has the same bond dimensions as the first PEPS. -/
  bondDim_eq : A.bondDim = Btilde.bondDim
  /-- The same inserted virtual matrix gives equal edge-inserted coefficients. -/
  edgeInsertedCoeff_eq :
    ∀ (e : Edge G) (σ : V → Fin d)
      (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ M =
        edgeInsertedCoeff (G := G) Btilde e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun bondDim_eq e)) M)

/-- **Edge-blocked insertion algebra isomorphism.**

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
Papers/1804.04964/paper_normal.tex.

After blocking a PEPS around an edge $e=(u,v)$, suppose both resulting
three-site chains are injective, every virtual bond of both tensors has positive
dimension, and the original PEPS states agree. Then matrix insertions on the
chosen bond of the first blocked chain correspond, by an algebra isomorphism, to
matrix insertions on the chosen bond of the second blocked chain, and the
corresponding inserted coefficients agree.

**Scope restriction (positive bond dimensions):** This is the positive-bond
version of the Section 3 insertion-algebra correspondence. The extra hypotheses
`hposA` and `hposB` are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`; the elimination plan is
to derive positive bond dimensions from injectivity before marking the
unrestricted source statement as formalized.

The inserted-matrix correspondence $X \mapsto Y$ is built explicitly as the
composition of algebra maps `edgeTransferMatrix`: insert $X$ on the right
endpoint of the first family and realize it (`edgeRightInsertionOp`), transfer
the resulting physical operator to the second family across `SameState`, and
read off the matrix it realizes there
(`edgeRightInsertionOp_realizes_edgeTransferMatrix`). Because each step preserves
composition, the explicit map is multiplicative, additive, and homogeneous
(`edgeTransferMatrix_mul`, `edgeTransferMatrix_add`, `edgeTransferMatrix_smul`)
and satisfies the coefficient identity (`edgeTransferMatrix_edgeInsertedCoeff`).
Injectivity of the edge-inserted coefficient in the inserted matrix
(`edgeInsertedCoeff_injective`) supplies identity-preservation
(`edgeTransferMatrix_one`); the symmetric construction with the two families
exchanged supplies the two-sided inverse (`edgeTransferAlgHom_comp_self`),
giving the algebra equivalence `edgeTransferAlgEquiv`. -/
theorem isEdgeBlockedInsertionAlgebraIsomorphism
    (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposA : ∀ f : Edge G, 0 < A.bondDim f) (hposB : ∀ f : Edge G, 0 < B.bondDim f) :
    IsEdgeBlockedInsertionAlgebraIsomorphism (G := G) A B e :=
  ⟨edgeTransferAlgEquiv A B e hA hB hAB hposA hposB,
    fun σ X => edgeTransferMatrix_edgeInsertedCoeff A B e hA hB hAB hposB X σ⟩

end PEPS
end TNLean
