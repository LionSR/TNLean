/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraBlockDiagonal
import TNLean.Algebra.StarSubalgebraSimpleModule
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The full block form of a star-subalgebra of complex matrices

This file completes the block representation of a star-subalgebra $S$ of complex matrices
asserted by *Quantum Channels & Operations* (Wolf 2012), Eq. (1.39), and invoked there by
Theorem 6.14: there is a unitary $U$ with
$$S \;=\; U \Bigl(\bigoplus_{k} \mathbf{1}_{m_k} \otimes M_{d_k}(\mathbb{C})\Bigr) U^{\dagger},$$
the unital case (no zero block), with the two Kronecker factors of each block written in the
order identity-times-matrix. The containment of $S$ in the conjugated block algebra is the
adapted-basis representation of `TNLean.Algebra.StarSubalgebraBlockDiagonal`; this file adds
the reverse inclusion: every choice of blocks $(B_k)_k$ is attained by a member of $S$.

The reverse inclusion is the finite-dimensional double-commutant argument. Every operator that
commutes with the commutant of $S$ already lies in $S$; this is the Jacobson density theorem
applied to $\mathbb{C}^{D}$ as a semisimple module over $S$. The commutant is computed in the
adapted orthonormal basis: an operator commuting with $S$ acts on each isotypic component by a
matrix on the multiplicity index, identically across the irreducible index — the block
$C_k \otimes \mathbf{1}_{d_k}$ opposite to the blocks of $S$. Every matrix that is
block-diagonal with blocks $\mathbf{1}_{m_k} \otimes B_k$ in the adapted basis commutes with
all such operators, hence lies in $S$.

## Main results

* `StarSubalgebra.mem_of_forall_comm` -- membership through the double commutant: a matrix
  whose operator commutes with every endomorphism commuting with the subalgebra is a member
  of the subalgebra.
* `StarSubalgebra.exists_unitary_conj_blockDiagonal_iff` -- the full block form: a unitary
  $U$ such that membership in $S$ is equivalent to $U^{\dagger} A U$ being block diagonal
  with blocks $\mathbf{1}_{m_k} \otimes B_k$.
-/

open scoped InnerProductSpace Kronecker

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- **Membership through the double commutant.** A matrix whose operator commutes with every
endomorphism of $\mathbb{C}^{D}$ that commutes with a star-subalgebra $S$ of complex matrices
is a member of $S$. This is the finite-dimensional case of the bicommutant characterization of
von Neumann algebras recalled in *Quantum Channels & Operations* (Wolf 2012), Chapter 1, used
there for the block representation Eq. (1.39) behind Theorem 6.14. The proof is the Jacobson
density theorem for $\mathbb{C}^{D}$ as a semisimple module over $S$: an endomorphism linear
over the commutant agrees with the action of a member of $S$ on any finite set of vectors, in
particular on a basis. -/
theorem mem_of_forall_comm {T : Matrix n n ℂ}
    (hT : ∀ g : Module.End ℂ (EuclideanSpace ℂ n),
      (∀ A ∈ S, ∀ x, g (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A (g x)) →
      ∀ x, g (Matrix.toEuclideanLin T x) = Matrix.toEuclideanLin T (g x)) :
    T ∈ S := by
  classical
  -- The operator of `T` commutes with every endomorphism over the subalgebra.
  have hcomm : ∀ (g : Module.End ↥S (EuclideanSpace ℂ n)) (v : EuclideanSpace ℂ n),
      Matrix.toEuclideanLin T (g v) = g (Matrix.toEuclideanLin T v) := by
    intro g v
    have hg : ∀ A ∈ S, ∀ x : EuclideanSpace ℂ n,
        (LinearMap.restrictScalars ℂ g) (Matrix.toEuclideanLin A x) =
          Matrix.toEuclideanLin A ((LinearMap.restrictScalars ℂ g) x) := by
      intro A hA x
      have h1 := map_smul g (⟨A, hA⟩ : ↥S) x
      simpa only [LinearMap.restrictScalars_apply, S.euclideanSpace_smul_def] using h1
    simpa only [LinearMap.restrictScalars_apply] using
      (hT (LinearMap.restrictScalars ℂ g) hg v).symm
  -- Package the operator as an endomorphism over the commutant and apply Jacobson density.
  haveI : IsSemisimpleModule ↥S (EuclideanSpace ℂ n) := S.isSemisimpleModule_euclideanSpace
  let f : Module.End (Module.End ↥S (EuclideanSpace ℂ n)) (EuclideanSpace ℂ n) :=
    { toFun := Matrix.toEuclideanLin T
      map_add' := map_add _
      map_smul' := fun g v => by
        simpa only [Module.End.smul_def, RingHom.id_apply] using hcomm g v }
  obtain ⟨r, hr⟩ := jacobson_density (R := ↥S) (M := EuclideanSpace ℂ n) f
    (Finset.image (EuclideanSpace.basisFun n ℂ) Finset.univ)
  -- The member `r` acts as `T` on the standard basis, hence everywhere.
  have heq : Matrix.toEuclideanLin T = Matrix.toEuclideanLin (r : Matrix n n ℂ) := by
    refine (EuclideanSpace.basisFun n ℂ).toBasis.ext fun i => ?_
    have hi := hr (EuclideanSpace.basisFun n ℂ i)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simpa only [OrthonormalBasis.coe_toBasis, LinearMap.coe_mk, AddHom.coe_mk,
      S.euclideanSpace_smul_def, f] using hi
  have hTr : T = (r : Matrix n n ℂ) := Matrix.toEuclideanLin.injective heq
  exact hTr ▸ r.2

section RowTransport

variable {K : ℕ} {d m : Fin K → ℕ}
variable (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ (EuclideanSpace ℂ n))

/-- Auxiliary operator between two rows of the adapted orthonormal basis: it reads off the
coefficients of a vector along the row $(k, i')$ and rebuilds them along the row $(k, i)$,
$$v \;\longmapsto\; \sum_{j} \langle f_{k,i',j}, v\rangle\, f_{k,i,j}.$$
Composites of these operators with an element of the commutant realize the intertwiners used
to compute the commutant of the subalgebra in the adapted basis, towards the block
representation Eq. (1.39) of *Quantum Channels & Operations* (Wolf 2012). -/
private noncomputable def rowTransport (k : Fin K) (i' i : Fin (m k)) :
    Module.End ℂ (EuclideanSpace ℂ n) where
  toFun v := ∑ j : Fin (d k), ⟪b ⟨k, (i', j)⟩, v⟫_ℂ • b ⟨k, (i, j)⟩
  map_add' x y := by
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [inner_smul_right, RingHom.id_apply, mul_smul, Finset.smul_sum]

omit [DecidableEq n] in
private theorem rowTransport_apply (k : Fin K) (i' i : Fin (m k)) (v : EuclideanSpace ℂ n) :
    rowTransport b k i' i v = ∑ j : Fin (d k), ⟪b ⟨k, (i', j)⟩, v⟫_ℂ • b ⟨k, (i, j)⟩ :=
  rfl

omit [DecidableEq n] in
/-- The row transport lands in the span of the target row. -/
private theorem rowTransport_apply_mem (k : Fin K) (i' i : Fin (m k))
    (v : EuclideanSpace ℂ n) :
    rowTransport b k i' i v ∈ Submodule.span ℂ (Set.range fun j => b ⟨k, (i, j)⟩) :=
  rowTransport_apply b k i' i v ▸ Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

omit [DecidableEq n] in
/-- On a basis vector of the same component, the row transport matches the source row to the
target row and annihilates the other rows. -/
private theorem rowTransport_apply_basis (k : Fin K) (i' i : Fin (m k))
    (i₀ : Fin (m k)) (j₀ : Fin (d k)) :
    rowTransport b k i' i (b ⟨k, (i₀, j₀)⟩) =
      if i₀ = i' then b ⟨k, (i, j₀)⟩ else 0 := by
  classical
  have horth := orthonormal_iff_ite.mp b.orthonormal
  rw [rowTransport_apply]
  rcases eq_or_ne i₀ i' with rfl | hi
  · simp [horth]
  · simp [horth, hi, Ne.symm hi]

omit [DecidableEq n] in
/-- On a basis vector of a different component, the row transport vanishes. -/
private theorem rowTransport_apply_basis_ne (k : Fin K) (i' i : Fin (m k)) {k₀ : Fin K}
    (hk : k₀ ≠ k) (i₀ : Fin (m k₀)) (j₀ : Fin (d k₀)) :
    rowTransport b k i' i (b ⟨k₀, (i₀, j₀)⟩) = 0 := by
  classical
  have horth := orthonormal_iff_ite.mp b.orthonormal
  rw [rowTransport_apply]
  simp [horth, Ne.symm hk]

/-- The row transport commutes with every matrix whose action on the adapted basis is by one
block per component, identically across the multiplicity index. -/
private theorem rowTransport_comm (k : Fin K) (i' i : Fin (m k)) {A : Matrix n n ℂ}
    {B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ}
    (hB : ∀ (k : Fin K) (i : Fin (m k)) (j : Fin (d k)),
      Matrix.toEuclideanLin A (b ⟨k, (i, j)⟩) = ∑ j', B k j' j • b ⟨k, (i, j')⟩)
    (v : EuclideanSpace ℂ n) :
    rowTransport b k i' i (Matrix.toEuclideanLin A v) =
      Matrix.toEuclideanLin A (rowTransport b k i' i v) := by
  have hext : rowTransport b k i' i ∘ₗ Matrix.toEuclideanLin A =
      Matrix.toEuclideanLin A ∘ₗ rowTransport b k i' i := by
    refine b.toBasis.ext fun l => ?_
    obtain ⟨k₀, i₀, j₀⟩ := l
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
    rcases eq_or_ne k₀ k with rfl | hk
    · rw [hB, map_sum]
      simp only [map_smul, rowTransport_apply_basis]
      rcases eq_or_ne i₀ i' with rfl | hi
      · simp [hB]
      · simp [hi]
    · rw [hB, map_sum]
      simp only [map_smul, rowTransport_apply_basis_ne b k i' i hk, smul_zero,
        Finset.sum_const_zero, map_zero]
  exact LinearMap.congr_fun hext v

variable {b}

/-- **The commutant in the adapted basis.** Let $(f_{k,i,j})$ be the adapted orthonormal
basis of `StarSubalgebra.exists_adapted_orthonormalBasis`: the rows span irreducible
subspaces, rows of distinct components are of different types, and the subalgebra acts by
one block per component. Then every endomorphism $g$ commuting with the subalgebra acts by
$$g\,f_{k,i,j} \;=\; \sum_{i'} \gamma^{(k)}_{i'i}\, f_{k,i',j}$$
for coefficients $\gamma^{(k)}$ depending only on the component and the multiplicity
indices: in the adapted basis the commutant consists of the block-diagonal matrices with
blocks $C_k \otimes \mathbf{1}_{d_k}$, as recalled after Eq. (1.39) of *Quantum Channels &
Operations* (Wolf 2012). Composites of `g` with the row transports are intertwiners between
the rows, so Schur's lemma makes them scalar within a component and zero across components. -/
private theorem exists_commutant_coeff
    (hirr : ∀ (k : Fin K) (i : Fin (m k)),
      S.IsIrreducibleSubspace (Submodule.span ℂ (Set.range fun j => b ⟨k, (i, j)⟩)))
    (hcross : ∀ k k' : Fin K, k ≠ k' → ∀ (i : Fin (m k)) (i' : Fin (m k')),
      ¬ S.SameIsotype (Submodule.span ℂ (Set.range fun j => b ⟨k, (i, j)⟩))
        (Submodule.span ℂ (Set.range fun j => b ⟨k', (i', j)⟩)))
    (hact : ∀ A ∈ S, ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
      ∀ (k : Fin K) (i : Fin (m k)) (j : Fin (d k)),
        Matrix.toEuclideanLin A (b ⟨k, (i, j)⟩) = ∑ j', B k j' j • b ⟨k, (i, j')⟩)
    {g : Module.End ℂ (EuclideanSpace ℂ n)}
    (hg : ∀ A ∈ S, ∀ x, g (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A (g x)) :
    ∃ γ : (k : Fin K) → Fin (m k) → Fin (m k) → ℂ,
      ∀ (k : Fin K) (i : Fin (m k)) (j : Fin (d k)),
        g (b ⟨k, (i, j)⟩) = ∑ i', γ k i' i • b ⟨k, (i', j)⟩ := by
  classical
  have horth := orthonormal_iff_ite.mp b.orthonormal
  -- The composite of a row transport with `g` commutes with the subalgebra.
  have hcomp : ∀ (k : Fin K) (i' i : Fin (m k)), ∀ A ∈ S, ∀ x,
      (rowTransport b k i' i ∘ₗ g) (Matrix.toEuclideanLin A x) =
        Matrix.toEuclideanLin A ((rowTransport b k i' i ∘ₗ g) x) := by
    intro k i' i A hA x
    obtain ⟨B, hB⟩ := hact A hA
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hg A hA x,
      rowTransport_comm b k i' i hB]
  -- Within one component the matrix of `g` between two rows is scalar, by Schur's lemma.
  have hwithin : ∀ (k : Fin K) (i i' : Fin (m k)), ∃ c : ℂ,
      ∀ (j : Fin (d k)) (j' : Fin (d k)),
        ⟪b ⟨k, (i', j')⟩, g (b ⟨k, (i, j)⟩)⟫_ℂ = if j' = j then c else 0 := by
    intro k i i'
    have hinv : Submodule.span ℂ (Set.range fun j => b ⟨k, (i, j)⟩) ∈
        Module.End.invtSubmodule (rowTransport b k i' i ∘ₗ g) :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := rowTransport b k i' i ∘ₗ g)).mpr fun x _ =>
          rowTransport_apply_mem b k i' i (g x)
    obtain ⟨c, hc⟩ := S.exists_eq_smul_of_commute_of_irreducible (hirr k i) hinv
      fun A hA x _ => hcomp k i' i A hA x
    refine ⟨c, fun j j' => ?_⟩
    have hx := hc (b ⟨k, (i, j)⟩) (Submodule.subset_span ⟨j, rfl⟩)
    rw [LinearMap.comp_apply, rowTransport_apply] at hx
    have hcoeff := congrArg (fun v => ⟪b ⟨k, (i, j')⟩, v⟫_ℂ) hx
    simpa only [inner_sum, inner_smul_right, horth, Sigma.mk.inj_iff, heq_eq_eq,
      Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] using hcoeff
  -- Across components the matrix of `g` vanishes: a nonzero entry would produce a nonzero
  -- intertwiner between rows of different types.
  have hacross : ∀ (k k' : Fin K), k ≠ k' → ∀ (i : Fin (m k)) (i' : Fin (m k'))
      (j : Fin (d k)) (j' : Fin (d k')),
      ⟪b ⟨k', (i', j')⟩, g (b ⟨k, (i, j)⟩)⟫_ℂ = 0 := by
    intro k k' hkk i i' j j'
    by_contra hne
    refine hcross k k' hkk i i' ⟨rowTransport b k' i' i' ∘ₗ g, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.map_le_iff_le_comap.mpr fun x _ =>
        rowTransport_apply_mem b k' i' i' (g x)
    · exact fun A hA x _ => hcomp k' i' i' A hA x
    · intro hzero
      have h0 := hzero (b ⟨k, (i, j)⟩) (Submodule.subset_span ⟨j, rfl⟩)
      rw [LinearMap.comp_apply, rowTransport_apply] at h0
      have hcoeff := congrArg (fun v => ⟪b ⟨k', (i', j')⟩, v⟫_ℂ) h0
      simp only [inner_sum, inner_smul_right, horth, Sigma.mk.inj_iff, heq_eq_eq,
        Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, inner_zero_right] at hcoeff
      exact hne hcoeff
  -- Expand `g` on the basis and collect the coefficients.
  choose γ hγ using hwithin
  refine ⟨fun k i' i => γ k i i', fun k i j => ?_⟩
  have houter : ∀ k' ∈ (Finset.univ : Finset (Fin K)), k' ≠ k →
      (∑ i' : Fin (m k'), ∑ j' : Fin (d k'),
        ⟪b ⟨k', (i', j')⟩, g (b ⟨k, (i, j)⟩)⟫_ℂ • b ⟨k', (i', j')⟩) = 0 := by
    intro k' _ hk'
    simp [hacross k k' (Ne.symm hk')]
  conv_lhs => rw [← b.sum_repr' (g (b ⟨k, (i, j)⟩))]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k) houter]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [hγ, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end RowTransport

/-- **The full block form (Wolf Eq. (1.39) / Thm 6.14).** For a star-subalgebra $S$ of
complex matrices there are a number $K$ of isotypic components, positive dimensions $d_k$
and multiplicities $m_k$ with $\sum_k d_k m_k = D$, and a unitary $U \in M_{D}(\mathbb{C})$
such that a matrix $A$ belongs to $S$ exactly when
$$U^{\dagger} A U \;=\; \bigoplus_{k} \mathbf{1}_{m_k} \otimes B_k$$
for some matrices $B_k \in M_{d_k}(\mathbb{C})$: up to reordering the two tensor factors of
each block,
$$S \;=\; U \Bigl(\bigoplus_{k} \mathbf{1}_{m_k} \otimes M_{d_k}(\mathbb{C})\Bigr)
U^{\dagger}.$$
This is the block representation of a finite-dimensional star-algebra of
*Quantum Channels & Operations* (Wolf 2012), Eq. (1.39), invoked by Theorem 6.14, in the
unital case: a star-subalgebra contains the identity, so there is no zero block. The
containment of $S$ in the block algebra is the adapted-basis representation of
`StarSubalgebra.exists_adapted_orthonormalBasis`; the reverse inclusion holds because a
matrix that is block diagonal in the adapted basis commutes with the commutant of $S$
(`StarSubalgebra.exists_commutant_coeff`) and therefore belongs to $S$ by the
double-commutant criterion (`StarSubalgebra.mem_of_forall_comm`). -/
theorem exists_unitary_conj_blockDiagonal_iff :
    ∃ (K : ℕ) (d m : Fin K → ℕ) (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ n)
      (U : Matrix n n ℂ), U ∈ Matrix.unitaryGroup n ℂ ∧ (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        ∀ A : Matrix n n ℂ,
          A ∈ S ↔ ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * A * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k =>
                (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k) := by
  classical
  obtain ⟨K, d, m, b, hd, hm, hirr, hcross, hact⟩ := S.exists_adapted_orthonormalBasis
  set s : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := EuclideanSpace.basisFun n ℂ with hs
  set e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ n := b.toBasis.indexEquiv s.toBasis with he
  set b' : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b.reindex e with hb'
  set U : Matrix n n ℂ := s.toBasis.toMatrix ⇑b'.toBasis with hU
  have hUmem : U ∈ Matrix.unitaryGroup n ℂ := s.toMatrix_orthonormalBasis_mem_unitary b'
  -- The conjugate transpose of the change-of-basis matrix is the reverse change of basis.
  have hstar : star U = b'.toBasis.toMatrix ⇑s.toBasis := by
    have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hUmem
    have h2 : U * b'.toBasis.toMatrix ⇑s.toBasis = 1 :=
      Module.Basis.toMatrix_mul_toMatrix_flip _ _
    calc star U = star U * (U * b'.toBasis.toMatrix ⇑s.toBasis) := by rw [h2, mul_one]
      _ = star U * U * b'.toBasis.toMatrix ⇑s.toBasis := by rw [mul_assoc]
      _ = b'.toBasis.toMatrix ⇑s.toBasis := by rw [h1, one_mul]
  -- The conjugation identity for any matrix with the adapted block action.
  have hconj : ∀ (A : Matrix n n ℂ) (B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ),
      (∀ (k : Fin K) (i : Fin (m k)) (j : Fin (d k)),
        Matrix.toEuclideanLin A (b ⟨k, (i, j)⟩) = ∑ j', B k j' j • b ⟨k, (i, j')⟩) →
      star U * A * U = Matrix.reindex e e
        (Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k) := by
    intro A B hB
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
        Matrix.reindex e e
          (LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A)) := by
      ext x y
      simp [hb', Matrix.reindex_apply, LinearMap.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis]
    calc star U * A * U
        = b'.toBasis.toMatrix ⇑s.toBasis * A * s.toBasis.toMatrix ⇑b'.toBasis := by
          rw [hstar, hU]
      _ = LinearMap.toMatrix b'.toBasis b'.toBasis (Matrix.toEuclideanLin A) := hchange
      _ = Matrix.reindex e e
            (Matrix.blockDiagonal' fun k =>
              (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k) := by
          rw [hreindex, hmatrix]
  refine ⟨K, d, m, e, U, hUmem, hd, hm, fun A => ⟨fun hA => ?_, fun h => ?_⟩⟩
  · -- Containment: the adapted action of a member gives the block-diagonal form.
    obtain ⟨B, hB⟩ := hact A hA
    exact ⟨B, hconj A B hB⟩
  · -- Reverse inclusion: a block-diagonal matrix in the adapted basis is a member.
    obtain ⟨B, hAB⟩ := h
    -- The candidate member acting by the blocks `B` on the adapted basis.
    set t : Module.End ℂ (EuclideanSpace ℂ n) :=
      b.toBasis.constr ℂ
        (fun l : (k : Fin K) × (Fin (m k) × Fin (d k)) =>
          ∑ j', B l.1 j' l.2.2 • b ⟨l.1, (l.2.1, j')⟩) with ht
    set T : Matrix n n ℂ := Matrix.toEuclideanLin.symm t with hT
    have hTact : ∀ (k : Fin K) (i : Fin (m k)) (j : Fin (d k)),
        Matrix.toEuclideanLin T (b ⟨k, (i, j)⟩) = ∑ j', B k j' j • b ⟨k, (i, j')⟩ := by
      intro k i j
      rw [hT, LinearEquiv.apply_symm_apply, ht]
      have hcb := b.toBasis.constr_basis ℂ
        (fun l : (k : Fin K) × (Fin (m k) × Fin (d k)) =>
          ∑ j', B l.1 j' l.2.2 • b ⟨l.1, (l.2.1, j')⟩) ⟨k, (i, j)⟩
      simpa only [OrthonormalBasis.coe_toBasis] using hcb
    -- `T` commutes with the commutant of `S`, hence lies in `S`.
    have hTmem : T ∈ S := by
      refine S.mem_of_forall_comm fun g hg => ?_
      obtain ⟨γ, hγ⟩ := exists_commutant_coeff S hirr hcross hact hg
      have hgt : g ∘ₗ Matrix.toEuclideanLin T = Matrix.toEuclideanLin T ∘ₗ g := by
        refine b.toBasis.ext fun l => ?_
        obtain ⟨k, i, j⟩ := l
        simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
        rw [hTact, hγ, map_sum, map_sum]
        simp only [map_smul, hγ, hTact, Finset.smul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i' _ =>
          Finset.sum_congr rfl fun j' _ => smul_comm _ _ _
      exact fun x => LinearMap.congr_fun hgt x
    -- The block-diagonal forms of `A` and of the member `T` agree, so `A = T`.
    have hTconj := hconj T B hTact
    have hU1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hUmem
    have hcancel : ∀ X : Matrix n n ℂ, U * (star U * X * U) * star U = X := by
      intro X
      rw [← mul_assoc U (star U * X) U, ← mul_assoc U (star U) X, hU1, one_mul,
        mul_assoc, hU1, mul_one]
    have hAT : A = T := by
      have h1 : U * (star U * A * U) * star U = U * (star U * T * U) * star U := by
        rw [hAB, hTconj]
      rwa [hcancel A, hcancel T] at h1
    exact hAT ▸ hTmem

end StarSubalgebra
