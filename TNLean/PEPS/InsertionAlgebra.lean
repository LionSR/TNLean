import TNLean.PEPS.EdgeMiddlePhysical
import TNLean.PEPS.IdentityInsertion
import TNLean.PEPS.InsertionRealization
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

/-! ### The state-operator bridge

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
          rw [edgeMiddleWeight_eq_edgeOpenMiddleWeight]
          rw [edgeOpenMiddleWeight_update_left]
          rw [Function.update_self]
          rw [Function.update_of_ne (edgeLeft_ne_edgeRight e).symm]

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
          rw [edgeMiddleWeight_eq_edgeOpenMiddleWeight]
          rw [edgeOpenMiddleWeight_update_right]
          rw [Function.update_self]
          rw [Function.update_of_ne (edgeLeft_ne_edgeRight e)]

/-- Equality of PEPS states transfers the left realization sum between the two tensor
families. The bridge rewrites both sides as weighted sums of the edge-blocked
coefficient, and `SameState.edgeBlockedCoeff_eq` matches them termwise.

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

/-- For each matrix `X` inserted on the chosen bond of the first blocked PEPS, there is
a matrix `Y` on the corresponding bond of the second blocked PEPS giving the same
edge-inserted coefficient at every physical configuration.

This is the inserted-coefficient correspondence $X \mapsto Y$ of Lemma inj_isomorph,
without the algebra structure. The proof combines the virtual-to-physical realization
$X \mapsto O_1,O_2$ (`edgeInsertedCoeff_eq_sum_left_physicalRealization`,
`edgeInsertedCoeff_eq_sum_right_physicalRealization`) on the first family, transfers
the two endpoint realization sums to the second family across `SameState`
(`edgeRealizationSum_left_sameState`, `edgeRealizationSum_right_sameState`), and feeds
the resulting equality of physical actions into the physical-to-virtual recovery
`physical_to_virtual_insertion` on the second family.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`; the displayed correspondence $X \mapsto Y$ is at
lines 564--582. -/
theorem exists_edgeInsertedCoeff_eq
    (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    ∃ Y : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ,
      ∀ σ : V → Fin d,
        edgeInsertedCoeff (G := G) A e σ X = edgeInsertedCoeff (G := G) B e σ Y := by
  classical
  obtain ⟨huA, hvA⟩ := hA.endpoint_linearIndependent
  obtain ⟨O₁, hO₁⟩ := localIncidentMatrixOp_physicalRealizationAt
    (A := A) huA (edgeLeftIncident (G := G) e) X.transpose
  obtain ⟨O₂, hO₂⟩ := localIncidentMatrixOp_physicalRealizationAt
    (A := A) hvA (edgeRightIncident (G := G) e) X
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
  obtain ⟨Y, hYleft, _hYright⟩ :=
    physical_to_virtual_insertion (G := G) B e hB hposB O₁ O₂ hEqB
  refine ⟨Y, fun σ => ?_⟩
  rw [hAleft σ, edgeRealizationSum_left_sameState hAB e σ O₁]
  exact (edgeInsertedCoeff_eq_sum_left_physicalRealization (G := G) B e σ Y O₁ hYleft).symm

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
three-site chains are injective and the original PEPS states agree. Then
matrix insertions on the chosen bond of the first blocked chain correspond, by
an algebra isomorphism, to matrix insertions on the chosen bond of the second
blocked chain, and the corresponding inserted coefficients agree.

**Proof status:** The inserted-coefficient correspondence $X \mapsto Y$ is
formalized: `exists_edgeInsertedCoeff_eq` produces, for every inserted matrix
$X$, a matrix $Y$ with equal edge-inserted coefficients at every physical
configuration. This combines the virtual-to-physical realization
$X \mapsto O_1,O_2$, the state-operator bridge transferring the endpoint
realization sums across `SameState`, and the recovery
`physical_to_virtual_insertion` on the second family. What remains is the
algebra-equivalence packaging of $X \mapsto Y$: well-definedness and injectivity
(equal edge-inserted coefficients determine the inserted matrix, using endpoint
injectivity of the corresponding family), surjectivity by the symmetric
construction, and the algebra-homomorphism laws (additivity follows from the
characterization, but multiplicativity is not visible from the coefficient
identity and needs the construction-level fact that $X \mapsto O_1$ and
$O_1 \mapsto Y$ are algebra homomorphisms). The available components and
remaining implications are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem isEdgeBlockedInsertionAlgebraIsomorphism
    (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposA : ∀ f : Edge G, 0 < A.bondDim f) (hposB : ∀ f : Edge G, 0 < B.bondDim f) :
    IsEdgeBlockedInsertionAlgebraIsomorphism (G := G) A B e := by
  -- This is the algebra-isomorphism step in arXiv:1804.04964, Section 3,
  -- Lemma inj_isomorph, lines 254--582. The inserted-coefficient correspondence
  -- $X \mapsto Y$ is supplied by `exists_edgeInsertedCoeff_eq`, which combines
  -- the virtual-to-physical realization with the physical-to-virtual recovery
  -- `physical_to_virtual_insertion`. The remaining work is to package that
  -- correspondence as the algebra equivalence: uniqueness and injectivity from
  -- endpoint injectivity, surjectivity from the symmetric construction, and the
  -- algebra-homomorphism laws (the multiplicativity is not visible from the
  -- coefficient identity and needs the construction-level algebra-map property).
  sorry

end PEPS
end TNLean
