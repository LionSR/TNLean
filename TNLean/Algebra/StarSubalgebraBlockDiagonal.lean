/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraIsotypicFactorization
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Global unitary block-diagonal form of a star-subalgebra of complex matrices

Continuing the structure theory of *Quantum Channels & Operations* (Wolf 2012), Chapter 6,
towards Theorem 6.14, this file assembles the adapted orthonormal bases of the isotypic
components into a single orthonormal basis of $\mathbb{C}^{D}$ and packages the change of basis
as a unitary matrix $U$. In the resulting coordinates every member of the subalgebra is block
diagonal, one block per isotypic component, and the block of the component with multiplicity
$m_k$ over an irreducible piece of dimension $d_k$ is the Kronecker product
$\mathbf{1}_{m_k} \otimes B_k$ of the identity with a $d_k \times d_k$ matrix. Up to reordering
the two tensor factors this is the representation
$$U \Bigl(\bigoplus_{k} M_{d_k} \otimes \mathbf{1}_{m_k}\Bigr) U^{\dagger}$$
of Theorem 6.14. A star-subalgebra contains the identity matrix, so no summand of the
decomposition acts as zero: this is the unital case of the representation, without the zero
block that Theorem 6.14 reserves for the complement of the support.

## Main results

* `StarSubalgebra.exists_adapted_orthonormalBasis` -- an orthonormal basis of the whole space,
  indexed by a component index $k$, a multiplicity index $i < m_k$, and an irreducible index
  $j < d_k$, on which every member of the subalgebra acts by one matrix on the irreducible
  index, identically across the multiplicity index, within each component.
* `StarSubalgebra.exists_unitary_conj_blockDiagonal` -- a unitary $U$ such that for every
  $A$ in the subalgebra, $U^{\dagger} A U$ is block diagonal with blocks
  $\mathbf{1}_{m_k} \otimes B_k$.

## Remaining step towards Wolf Thm 6.14

Both results state the containment direction only: every member of the subalgebra takes the
block-diagonal form in the adapted coordinates. The converse of Theorem 6.14, that every
choice of blocks $(B_k)_k$ arises from a member of the subalgebra, is not asserted here.
-/

open scoped InnerProductSpace Kronecker

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- **Adapted orthonormal basis of the whole space.** For a star-subalgebra $S$ of complex
matrices there are a number $K$ of isotypic components, positive dimensions
$d_0, \ldots, d_{K-1}$ and multiplicities $m_0, \ldots, m_{K-1}$, and an orthonormal basis
$(f_{k,i,j})_{k < K,\, i < m_k,\, j < d_k}$ of $\mathbb{C}^{D}$ such that for every $A \in S$
there are matrices $B_k \in M_{d_k}(\mathbb{C})$ with, for all $k$, $i < m_k$, and $j < d_k$,
$$A\,f_{k,i,j} \;=\; \sum_{j'} (B_k)_{j'j}\, f_{k,i,j'} :$$
the member $A$ acts on the $k$-th component as $\mathbf{1}_{m_k} \otimes B_k$. The basis is
the concatenation of the adapted orthonormal bases of the pairwise orthogonal isotypic
components, combining `StarSubalgebra.exists_orthogonal_isotypic_decomposition` with
`StarSubalgebra.exists_adapted_orthonormal_family_of_sameIsotype` on each component. This is the
adapted-basis form of the block decomposition behind *Quantum Channels & Operations*
(Wolf 2012), Theorem 6.14, in the unital case (no zero block). Only the containment direction
is stated: every member of $S$ takes this form. -/
theorem exists_adapted_orthonormalBasis :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ (EuclideanSpace ℂ n)),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        ∀ A ∈ S, ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
          ∀ (k : Fin K) (i : Fin (m k)) (j : Fin (d k)),
            Matrix.toEuclideanLin A (b ⟨k, (i, j)⟩) = ∑ j', B k j' j • b ⟨k, (i, j')⟩ := by
  classical
  obtain ⟨C, hCfin, hCpair, hCsup, hC⟩ := S.exists_orthogonal_isotypic_decomposition
  haveI : Fintype ↥C := hCfin.fintype
  -- Each component carries an adapted orthonormal family with positive dimensions.
  have key : ∀ c ∈ C, ∃ (d m : ℕ) (f : Fin m × Fin d → EuclideanSpace ℂ n),
      0 < d ∧ 0 < m ∧ Orthonormal ℂ f ∧ Submodule.span ℂ (Set.range f) = c ∧
        ∀ A ∈ S, ∃ B : Matrix (Fin d) (Fin d) ℂ, ∀ i j,
          Matrix.toEuclideanLin A (f (i, j)) = ∑ j', B j' j • f (i, j') := by
    intro c hc
    obtain ⟨Dc, hne, hfin, hirr, rfl, hortho, hsame⟩ := hC c hc
    obtain ⟨d, m, f, hmcard, hdim, hon, hspan, hact⟩ :=
      S.exists_adapted_orthonormal_family_of_sameIsotype hne hfin hirr hortho hsame
    obtain ⟨p₀, hp₀⟩ := hne
    refine ⟨d, m, f, ?_, ?_, hon, hspan, hact⟩
    · -- The common dimension is positive because an irreducible piece is nonzero.
      rw [← hdim p₀ hp₀]
      exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr (hirr p₀ hp₀).2.1)
    · -- The multiplicity is positive because the same-type class is nonempty.
      rw [hmcard]
      exact (Set.ncard_pos hfin).mpr ⟨p₀, hp₀⟩
  choose d m f hd hm hon hspan hact using fun c : ↥C => key c.1 c.2
  -- The concatenated family over the sigma type of all components.
  have hmem : ∀ (c : ↥C) (p : Fin (m c) × Fin (d c)),
      f c p ∈ (c : Submodule ℂ (EuclideanSpace ℂ n)) := fun c p =>
    hspan c ▸ Submodule.subset_span (Set.mem_range_self p)
  -- Orthonormality: within a component by the adapted family, across components by the
  -- orthogonality of the isotypic components.
  have hFon : Orthonormal ℂ fun x : (c : ↥C) × (Fin (m c) × Fin (d c)) => f x.1 x.2 := by
    rw [orthonormal_iff_ite]
    rintro ⟨c, p⟩ ⟨c', p'⟩
    rcases eq_or_ne c c' with rfl | hcc
    · simpa [Sigma.mk.inj_iff] using orthonormal_iff_ite.mp (hon c) p p'
    · have h0 := (hCpair c.2 c'.2 fun h => hcc (Subtype.ext h)).inner_eq
        (hmem c p) (hmem c' p')
      simpa [Sigma.mk.inj_iff, hcc] using h0
  -- The concatenated family spans: the components span their suprema, which sup to the top.
  have hFspan : ⊤ ≤ Submodule.span ℂ
      (Set.range fun x : (c : ↥C) × (Fin (m c) × Fin (d c)) => f x.1 x.2) := by
    rw [← hCsup]
    refine sSup_le fun c hc => le_trans (hspan ⟨c, hc⟩).symm.le (Submodule.span_mono ?_)
    rintro x ⟨p, rfl⟩
    exact ⟨⟨⟨c, hc⟩, p⟩, rfl⟩
  -- Enumerate the components and transport the basis to the enumerated index type.
  set σ : Fin (Fintype.card ↥C) ≃ ↥C := (Fintype.equivFin ↥C).symm with hσ
  refine ⟨Fintype.card ↥C, fun k => d (σ k), fun k => m (σ k),
    (OrthonormalBasis.mk hFon hFspan).reindex
      (Equiv.sigmaCongrLeft (β := fun c : ↥C => Fin (m c) × Fin (d c)) σ).symm,
    fun k => hd (σ k), fun k => hm (σ k), ?_⟩
  have hb : ∀ (k : Fin (Fintype.card ↥C)) (p : Fin (m (σ k)) × Fin (d (σ k))),
      (OrthonormalBasis.mk hFon hFspan).reindex
        (Equiv.sigmaCongrLeft (β := fun c : ↥C => Fin (m c) × Fin (d c)) σ).symm ⟨k, p⟩ =
      f (σ k) p := by
    intro k p
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm,
      show (Equiv.sigmaCongrLeft (β := fun c : ↥C => Fin (m c) × Fin (d c)) σ) ⟨k, p⟩ =
        ⟨σ k, p⟩ from rfl,
      OrthonormalBasis.coe_mk]
  intro A hA
  choose B hB using fun c : ↥C => hact c A hA
  refine ⟨fun k => B (σ k), fun k i j => ?_⟩
  rw [hb k (i, j), hB (σ k) i j]
  exact Finset.sum_congr rfl fun j' _ => by rw [hb k (i, j')]

/-- **Global unitary block-diagonal form.** For a star-subalgebra $S$ of complex matrices
there are a number $K$ of isotypic components, positive dimensions $d_k$ and multiplicities
$m_k$ with $\sum_k d_k m_k = D$, and a unitary $U \in M_{D}(\mathbb{C})$ such that every
$A \in S$ satisfies
$$U^{\dagger} A U \;=\; \bigoplus_{k} \mathbf{1}_{m_k} \otimes B_k$$
for matrices $B_k \in M_{d_k}(\mathbb{C})$ depending on $A$. The columns of $U$ are the
adapted orthonormal basis of `StarSubalgebra.exists_adapted_orthonormalBasis`; the index
identification realizing $\sum_k d_k m_k = D$ is part of the statement. Up to reordering the
two tensor factors this is the block representation of *Quantum Channels & Operations*
(Wolf 2012), Theorem 6.14, in the unital case: a star-subalgebra contains the identity, so
there is no zero block. Only the containment direction is stated: every member of $S$ is
carried by $U$ into the block algebra; that every choice of blocks is attained is not
asserted here. -/
theorem exists_unitary_conj_blockDiagonal :
    ∃ (K : ℕ) (d m : Fin K → ℕ) (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ n)
      (U : Matrix n n ℂ), U ∈ Matrix.unitaryGroup n ℂ ∧ (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        ∀ A ∈ S, ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
          star U * A * U = Matrix.reindex e e
            (Matrix.blockDiagonal' fun k => (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k) := by
  classical
  obtain ⟨K, d, m, b, hd, hm, hact⟩ := S.exists_adapted_orthonormalBasis
  set s : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := EuclideanSpace.basisFun n ℂ with hs
  set e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ n := b.toBasis.indexEquiv s.toBasis with he
  set b' : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b.reindex e with hb'
  refine ⟨K, d, m, e, s.toBasis.toMatrix ⇑b'.toBasis,
    s.toMatrix_orthonormalBasis_mem_unitary b', hd, hm, fun A hA => ?_⟩
  obtain ⟨B, hB⟩ := hact A hA
  refine ⟨B, ?_⟩
  -- The conjugate transpose of the change-of-basis matrix is the reverse change of basis.
  have hstar : star (s.toBasis.toMatrix ⇑b'.toBasis) = b'.toBasis.toMatrix ⇑s.toBasis := by
    have h1 : star (s.toBasis.toMatrix ⇑b'.toBasis) * s.toBasis.toMatrix ⇑b'.toBasis = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (s.toMatrix_orthonormalBasis_mem_unitary b')
    have h2 : s.toBasis.toMatrix ⇑b'.toBasis * b'.toBasis.toMatrix ⇑s.toBasis = 1 :=
      Module.Basis.toMatrix_mul_toMatrix_flip _ _
    calc star (s.toBasis.toMatrix ⇑b'.toBasis)
        = star (s.toBasis.toMatrix ⇑b'.toBasis) *
            (s.toBasis.toMatrix ⇑b'.toBasis * b'.toBasis.toMatrix ⇑s.toBasis) := by
          rw [h2, mul_one]
      _ = star (s.toBasis.toMatrix ⇑b'.toBasis) * s.toBasis.toMatrix ⇑b'.toBasis *
            b'.toBasis.toMatrix ⇑s.toBasis := by rw [mul_assoc]
      _ = b'.toBasis.toMatrix ⇑s.toBasis := by rw [h1, one_mul]
  -- A matrix is the matrix of its Euclidean operator in the standard orthonormal basis.
  have hA' : LinearMap.toMatrix s.toBasis s.toBasis (Matrix.toEuclideanLin A) = A := by
    rw [hs, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  -- Conjugation by the change-of-basis matrix computes the matrix in the adapted basis.
  have hchange : b'.toBasis.toMatrix ⇑s.toBasis * A * s.toBasis.toMatrix ⇑b'.toBasis =
      LinearMap.toMatrix b'.toBasis b'.toBasis (Matrix.toEuclideanLin A) := by
    conv_lhs => rw [← hA']
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      b'.toBasis s.toBasis b'.toBasis s.toBasis (Matrix.toEuclideanLin A)
  -- In the adapted basis the matrix of the operator is the block-diagonal Kronecker form.
  have hmatrix : LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A) =
      Matrix.blockDiagonal' fun k => (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k := by
    ext ⟨k', i', j'⟩ ⟨k, i, j⟩
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, hB k i j,
      inner_sum]
    simp only [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    rcases eq_or_ne k' k with rfl | hkk
    · rw [Matrix.blockDiagonal'_apply_eq]
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq,
        Prod.mk.injEq, true_and]
      rcases eq_or_ne i' i with rfl | hii
      · simp [Finset.sum_ite_eq]
      · simp [hii]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkk]
      simp [hkk]
  -- Reindexing the basis reindexes the matrix of the operator.
  have hreindex : LinearMap.toMatrix b'.toBasis b'.toBasis (Matrix.toEuclideanLin A) =
      Matrix.reindex e e (LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A)) := by
    ext x y
    simp [hb', Matrix.reindex_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis]
  calc star (s.toBasis.toMatrix ⇑b'.toBasis) * A * s.toBasis.toMatrix ⇑b'.toBasis
      = b'.toBasis.toMatrix ⇑s.toBasis * A * s.toBasis.toMatrix ⇑b'.toBasis := by rw [hstar]
    _ = LinearMap.toMatrix b'.toBasis b'.toBasis (Matrix.toEuclideanLin A) := hchange
    _ = Matrix.reindex e e
          (Matrix.blockDiagonal' fun k => (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k) := by
        rw [hreindex, hmatrix]

end StarSubalgebra
