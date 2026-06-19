import TNLean.PEPS.Blocking
import TNLean.PEPS.InsertionAlgebra
import TNLean.PEPS.EdgeGaugeExtraction
import TNLean.PEPS.EdgeMiddlePhysical
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Per-edge gauge family for injective PEPS

This file records the per-edge content of the injective PEPS Fundamental
Theorem (arXiv:1804.04964, Section 3) into one global gauge family.

For each edge `e`, blocking a vertex-injective PEPS around `e` gives a three-site
injective chain. Comparing two PEPS that generate the same state then yields, via
`isEdgeBlockedInsertionAlgebraIsomorphism` (#1367), an algebra isomorphism `Φ_e`
between the two bond matrix algebras whose inserted edge coefficients agree.
Skolem--Noether (`edgeGaugeFromInsertionAlgebraIsomorphism`) realizes each `Φ_e`
as conjugation by an invertible bond matrix. Transporting these matrices back to
the first tensor's bonds across the bond-dimension equality gives a single
gauge family `X` and records, edgewise, both the inserted-coefficient identity
and the conjugation form of `Φ_e`.

This is the construction used in the gauge-consistency theorem; the remaining
cross-edge passage to the per-vertex gauge formula is recorded in
the fundamental-theorem module and in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Transport an invertible matrix across an equality of finite index sizes. -/
noncomputable def glReindex {m n : ℕ} (h : m = n) :
    GL (Fin m) ℂ ≃* GL (Fin n) ℂ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)).toRingEquiv.toMulEquiv

/-- The matrix of a transported invertible matrix is the reindexed matrix. -/
theorem glReindex_coe {m n : ℕ} (h : m = n) (Z : GL (Fin m) ℂ) :
    (↑(glReindex h Z) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) (↑Z : Matrix (Fin m) (Fin m) ℂ) :=
  rfl

/-- Reindexing back and forth across an index-size equality is the identity. -/
@[deprecated "Use a local proof by simplifying `Matrix.reindexAlgEquiv`."
  (since := "2026-06-19")]
theorem reindexAlgEquiv_finCongr_symm_round {m n : ℕ} (h h' : m = n)
    (N : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr h'.symm) N) = N := by
  subst h
  simp

/-- Transporting an invertible matrix across two successive index-size equalities is transporting
across their composite. -/
theorem glReindex_glReindex {m n k : ℕ} (h₁ : m = n) (h₂ : n = k) (Z : GL (Fin m) ℂ) :
    glReindex h₂ (glReindex h₁ Z) = glReindex (h₁.trans h₂) Z := by
  subst h₁
  subst h₂
  rfl

/-- The transpose of an invertible matrix, packaged as an invertible matrix. The
inverse is the transpose of the inverse, since transposition is an
anti-homomorphism. -/
def glTranspose {m : ℕ} (X : GL (Fin m) ℂ) : GL (Fin m) ℂ where
  val := (↑X : Matrix (Fin m) (Fin m) ℂ)ᵀ
  inv := (↑X⁻¹ : Matrix (Fin m) (Fin m) ℂ)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

/-- The matrix of `glTranspose X` is the transpose of the matrix of `X`. -/
theorem glTranspose_coe {m : ℕ} (X : GL (Fin m) ℂ) :
    (↑(glTranspose X) : Matrix (Fin m) (Fin m) ℂ) =
      (↑X : Matrix (Fin m) (Fin m) ℂ)ᵀ :=
  rfl

/-- The matrix of `(glTranspose X)⁻¹` is the transpose of the inverse of `X`. -/
theorem glTranspose_inv_coe {m : ℕ} (X : GL (Fin m) ℂ) :
    (↑(glTranspose X)⁻¹ : Matrix (Fin m) (Fin m) ℂ) =
      (↑X⁻¹ : Matrix (Fin m) (Fin m) ℂ)ᵀ := by
  rw [Matrix.GeneralLinearGroup.coe_inv, glTranspose_coe,
    ← Matrix.transpose_nonsing_inv, Matrix.GeneralLinearGroup.coe_inv]

/-- Reindexing commutes with transposition. -/
@[deprecated "Use `Matrix.transpose_reindex` directly." (since := "2026-06-19")]
theorem reindexAlgEquiv_transpose {m n : ℕ} (h : m = n)
    (N : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) Nᵀ =
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) N)ᵀ := by
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.transpose_submatrix]

/-- **Per-edge gauge family from the edge-blocked insertion algebra
isomorphisms.**

For each edge `e`, blocking `A` and `B` around `e` gives three-site injective
chains (`IsVertexInjective.edgeBlockedThreeSiteInjective`, using the positive
bond dimensions), and `isEdgeBlockedInsertionAlgebraIsomorphism` (#1367) supplies
an algebra isomorphism `Φ_e` between the bond matrix algebras whose inserted
coefficients match. The finite-dimensional algebra step
`edgeGaugeFromInsertionAlgebraIsomorphism` (Skolem--Noether) realizes each `Φ_e`
as conjugation by an invertible bond matrix on the `B`-side. Transporting those
matrices back to the \(A\)-side bonds across the bond-dimension equality gives
a single global gauge family, and records, edgewise, both the inserted-coefficient identity and
that `Φ_e` is conjugation by `X_e`.

This records the per-edge content of the source proof up to the point where the
edge gauges are produced. The remaining work in gauge consistency is the
cross-edge passage to the per-vertex formula \(B_v = X\cdot A_v\), which
the source obtains from the post-absorption insertion identity
(`eq:inj_equal_edge`) and the one-vertex-versus-complement comparison; both of
those steps are tracked separately (see
`docs/paper-gaps/peps_injective_ft_section3_route.tex`).

Source: arXiv:1804.04964, Section 3, lines 560--586. -/
theorem exists_edgeGaugeFamily (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
      ∀ e : Edge G,
        ∃ Φ :
          Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ ≃ₐ[ℂ]
            Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ,
          (∀ (σ : V → Fin d)
              (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
            edgeInsertedCoeff (G := G) A e σ M =
              edgeInsertedCoeff (G := G) B e σ (Φ M)) ∧
          ∀ M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
            Φ M =
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e))
                ((↑(X e) : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) * M *
                  (↑(X e)⁻¹ : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)) := by
  classical
  have hposB : ∀ e : Edge G, 0 < B.bondDim e := by
    intro e; rw [← congr_fun hDim e]; exact hpos e
  have hAblk : ∀ e : Edge G, EdgeBlockedThreeSiteInjective (G := G) A e :=
    fun e => hA.edgeBlockedThreeSiteInjective hpos e
  have hBblk : ∀ e : Edge G, EdgeBlockedThreeSiteInjective (G := G) B e :=
    fun e => hB.edgeBlockedThreeSiteInjective hposB e
  have hiso : ∀ e : Edge G, IsEdgeBlockedInsertionAlgebraIsomorphism (G := G) A B e :=
    fun e =>
      isEdgeBlockedInsertionAlgebraIsomorphism A B e (hAblk e) (hBblk e) hAB hpos hposB
  choose Φ hΦcoeff using fun e => (hiso e)
  -- Skolem--Noether: each edge algebra equivalence is conjugation by an
  -- invertible matrix on the second tensor's bond.
  choose hEdge Z hZ using
    fun e => edgeGaugeFromInsertionAlgebraIsomorphism A B e (Φ e)
  -- Transport each edge gauge back to the first tensor's bond.
  refine ⟨fun e => glReindex (hEdge e).symm (Z e), fun e => ⟨Φ e, hΦcoeff e, ?_⟩⟩
  intro M
  rw [hZ e]
  -- Both sides reindex the inserted matrix from the first bond to the second
  -- bond, conjugated by the edge gauge.
  have hXcoe :
      (↑(glReindex (hEdge e).symm (Z e)) :
          Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hEdge e).symm)
          (↑(Z e) : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :=
    glReindex_coe (hEdge e).symm (Z e)
  have hXinvcoe :
      (↑(glReindex (hEdge e).symm (Z e))⁻¹ :
          Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hEdge e).symm)
          (↑(Z e)⁻¹ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
    rw [← map_inv, glReindex_coe]
  rw [hXcoe, hXinvcoe]
  have hProofEq : congr_fun hDim e = hEdge e := Subsingleton.elim _ _
  rw [hProofEq]
  -- The reindexing equivalence is multiplicative; push it through products, and
  -- the inverse-index transport cancels against the outer reindex.
  have hRound {m n : ℕ} (h h' : m = n) (N : Matrix (Fin n) (Fin n) ℂ) :
      Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr h'.symm) N) = N := by
    subst h
    simp
  simp only [map_mul, hRound (hEdge e) (hEdge e)]

end PEPS
end TNLean
