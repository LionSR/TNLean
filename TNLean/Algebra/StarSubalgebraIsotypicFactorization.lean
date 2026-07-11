/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraIsotypicDecomp
import TNLean.Algebra.StarSubalgebraUnitaryIntertwiner

/-!
# Tensor factorization of the isotypic components of a star-subalgebra

Continuing the structure theory of *Quantum Channels & Operations* (Wolf 2012), Chapter 6,
towards Theorem 6.14, this file factors each isotypic component spatially. An isotypic
component is spanned by finitely many pairwise orthogonal irreducible pieces of one type; the
pieces are unitarily identified copies of a single irreducible piece, so an orthonormal basis
of one copy spreads to an adapted orthonormal basis of the whole component, indexed by a
multiplicity index and an irreducible index. In this basis every member of the subalgebra acts
by one matrix on the irreducible index, identically across the multiplicity index. This is the
matrix-times-identity block structure of Theorem 6.14: on the component of multiplicity $m$
over an irreducible piece of dimension $d$, the subalgebra acts by matrices of the form
$\mathbf{1}_{m} \otimes B$ with $B$ a $d \times d$ matrix.

## Main results

* `StarSubalgebra.exists_adapted_orthonormal_family_of_sameIsotype` -- a finite nonempty family
  of pairwise orthogonal irreducible pieces of one type has an adapted orthonormal basis of its
  span, on which every member of the subalgebra acts by a matrix on the irreducible index,
  identically across the multiplicity index.
* `StarSubalgebra.exists_isotypic_tensor_factorization` -- the whole representation space is
  the supremum of a finite, pairwise orthogonal family of isotypic components, each carrying
  such an adapted orthonormal basis.

## Remaining step towards Wolf Thm 6.14

The adapted bases realize the action of the subalgebra on each isotypic component as
matrix-times-identity blocks. The global change of basis, which concatenates the adapted bases
of the components into a single unitary matrix conjugating every member of the subalgebra to
the block-diagonal form, is carried out in `TNLean.Algebra.StarSubalgebraBlockDiagonal`. The
converse direction of the theorem, that every choice of blocks is attained by a member of the
subalgebra, remains open.
-/

open scoped InnerProductSpace

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- **Adapted orthonormal basis of an isotypic component.** Let $\mathcal{D}$ be a finite,
nonempty family of pairwise orthogonal subspaces of $\mathbb{C}^{D}$, irreducible under a
star-subalgebra $S$ of complex matrices and pairwise of the same type. Write $m$ for the number
of pieces; all pieces share one dimension $d$. Then the span of the family has an orthonormal
basis $(f_{i,j})_{0 \le i < m,\, 0 \le j < d}$ such that for every $A \in S$ there is a matrix
$B \in M_{d}(\mathbb{C})$ with, for all $i < m$ and $j < d$,
$$A\,f_{i,j} \;=\; \sum_{j'} B_{j'j}\, f_{i,j'} :$$
in the adapted basis the member $A$ acts on the component as $\mathbf{1}_{m} \otimes B$, one
matrix on the irreducible index, identically across the multiplicity index.

An orthonormal basis $e_0, \ldots, e_{d-1}$ of one piece spreads to the others through the
inner-product-preserving intertwiners of
`StarSubalgebra.exists_isometry_intertwiner_of_sameIsotype`; the intertwining identity makes
the matrix of $A$ the same on every copy. See *Quantum Channels & Operations* (Wolf 2012),
Chapter 6, towards Theorem 6.14. -/
theorem exists_adapted_orthonormal_family_of_sameIsotype
    {Dc : Set (Submodule ℂ (EuclideanSpace ℂ n))} (hne : Dc.Nonempty) (hfin : Dc.Finite)
    (hirr : ∀ p ∈ Dc, S.IsIrreducibleSubspace p) (hortho : Dc.Pairwise (· ⟂ ·))
    (hsame : Dc.Pairwise fun p q => S.SameIsotype p q) :
    ∃ (d m : ℕ) (f : Fin m × Fin d → EuclideanSpace ℂ n),
      m = Dc.ncard ∧ (∀ p ∈ Dc, Module.finrank ℂ p = d) ∧
      Orthonormal ℂ f ∧ Submodule.span ℂ (Set.range f) = sSup Dc ∧
      ∀ A ∈ S, ∃ B : Matrix (Fin d) (Fin d) ℂ, ∀ (i : Fin m) (j : Fin d),
        Matrix.toEuclideanLin A (f (i, j)) = ∑ j', B j' j • f (i, j') := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  have hp₀irr : S.IsIrreducibleSubspace p₀ := hirr p₀ hp₀
  haveI : Fintype ↥Dc := hfin.fintype
  -- An orthonormal basis of the base piece and an enumeration of the family.
  set e : OrthonormalBasis (Fin (Module.finrank ℂ p₀)) ℂ ↥p₀ := stdOrthonormalBasis ℂ ↥p₀
  set σ : Fin (Fintype.card ↥Dc) ≃ ↥Dc := (Fintype.equivFin ↥Dc).symm
  -- Every piece receives an inner-product-preserving intertwiner from the base piece.
  have key : ∀ q : ↥Dc, ∃ u : Module.End ℂ (EuclideanSpace ℂ n),
      S.IsIntertwiner p₀ q.1 u ∧ Submodule.map u p₀ = q.1 ∧
        ∀ x ∈ p₀, ∀ y ∈ p₀, ⟪u x, u y⟫_ℂ = ⟪x, y⟫_ℂ := by
    rintro ⟨q, hq⟩
    rcases eq_or_ne p₀ q with rfl | hpq
    · exact S.exists_isometry_intertwiner_of_sameIsotype hp₀irr hp₀irr (S.sameIsotype_refl hp₀irr)
    · exact S.exists_isometry_intertwiner_of_sameIsotype hp₀irr (hirr q hq) (hsame hp₀ hq hpq)
  choose u hu_int hu_map hu_inner using key
  -- The adapted family: the basis of the base piece, spread to each copy.
  set f : Fin (Fintype.card ↥Dc) × Fin (Module.finrank ℂ p₀) → EuclideanSpace ℂ n :=
    fun ij => u (σ ij.1) (e ij.2 : EuclideanSpace ℂ n)
  have hmem : ∀ i j, f (i, j) ∈ (σ i : Submodule ℂ (EuclideanSpace ℂ n)) := fun i j =>
    hu_map (σ i) ▸ Submodule.mem_map_of_mem (e j).2
  -- Orthonormality: within a copy by the isometry, across copies by orthogonality.
  have hf_on : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, j⟩ ⟨i', j'⟩
    rcases eq_or_ne i i' with rfl | hii
    · have h1 : ⟪f (i, j), f (i, j')⟫_ℂ =
          ⟪(e j : EuclideanSpace ℂ n), (e j' : EuclideanSpace ℂ n)⟫_ℂ :=
        hu_inner (σ i) _ (e j).2 _ (e j').2
      rw [h1, ← Submodule.coe_inner, orthonormal_iff_ite.mp e.orthonormal j j']
      simp [Prod.ext_iff]
    · have hqq : (σ i : Submodule ℂ (EuclideanSpace ℂ n)) ≠ ↑(σ i') := fun h =>
        hii (σ.injective (Subtype.ext h))
      rw [(hortho (σ i).2 (σ i').2 hqq).inner_eq (hmem i j) (hmem i' j')]
      simp [Prod.ext_iff, hii]
  -- The base basis spans the base piece, so each spread copy spans its piece.
  have hspan₀ : Submodule.span ℂ (Set.range fun j => (e j : EuclideanSpace ℂ n)) = p₀ := by
    have h1 := congrArg (Submodule.map p₀.subtype) e.toBasis.span_eq
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
  have hspan_copy : ∀ i, Submodule.span ℂ (Set.range fun j => f (i, j)) =
      (σ i : Submodule ℂ (EuclideanSpace ℂ n)) := by
    intro i
    have h1 := congrArg (Submodule.map (u (σ i))) hspan₀
    rw [Submodule.map_span, ← Set.range_comp, hu_map (σ i)] at h1
    exact h1
  refine ⟨Module.finrank ℂ p₀, Fintype.card ↥Dc, f, ?_, ?_, hf_on, ?_, ?_⟩
  · -- The number of copies is the number of pieces of the family.
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  · -- Every piece has the dimension of the base piece: it is spanned by an orthonormal family
    -- of that many vectors.
    intro q hq
    have hsub : Orthonormal ℂ fun j => f (σ.symm ⟨q, hq⟩, j) :=
      hf_on.comp (fun j => (σ.symm ⟨q, hq⟩, j)) fun a b hab => (Prod.ext_iff.mp hab).2
    have hcopy := hspan_copy (σ.symm ⟨q, hq⟩)
    rw [Equiv.apply_symm_apply] at hcopy
    have h2 := finrank_span_eq_card hsub.linearIndependent
    rw [hcopy] at h2
    simpa using h2
  · -- The copies together span the whole component.
    refine le_antisymm ?_ (sSup_le fun q hq => ?_)
    · rw [Submodule.span_le]
      rintro x ⟨⟨i, j⟩, rfl⟩
      exact le_sSup (σ i).2 (hmem i j)
    · have hcopy := hspan_copy (σ.symm ⟨q, hq⟩)
      rw [Equiv.apply_symm_apply] at hcopy
      exact hcopy.symm.le.trans
        (Submodule.span_mono (Set.range_comp_subset_range (fun j => (σ.symm ⟨q, hq⟩, j)) f))
  · -- The action: one matrix on the irreducible index, identically across the copies.
    intro A hA
    refine ⟨Matrix.of fun j' j => ⟪(e j' : EuclideanSpace ℂ n),
      Matrix.toEuclideanLin A (e j : EuclideanSpace ℂ n)⟫_ℂ, fun i j => ?_⟩
    have hAe : Matrix.toEuclideanLin A (e j : EuclideanSpace ℂ n) ∈ p₀ :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Matrix.toEuclideanLin A)).mp (hp₀irr.1 A hA) _ (e j).2
    have hcomm := (hu_int (σ i)).2 A hA (e j : EuclideanSpace ℂ n) (e j).2
    -- Expand the image of the base basis vector in the base basis and spread by the
    -- intertwiner.
    have happ := congrArg ((u (σ i)).comp p₀.subtype)
      (e.sum_repr' (⟨Matrix.toEuclideanLin A (e j : EuclideanSpace ℂ n), hAe⟩ : ↥p₀))
    rw [map_sum] at happ
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_smul] at happ
    calc Matrix.toEuclideanLin A (f (i, j))
        = u (σ i) (Matrix.toEuclideanLin A (e j : EuclideanSpace ℂ n)) := hcomm.symm
      _ = ∑ j', ⟪e j', (⟨Matrix.toEuclideanLin A (e j : EuclideanSpace ℂ n), hAe⟩ : ↥p₀)⟫_ℂ •
            u (σ i) (e j' : EuclideanSpace ℂ n) := happ.symm
      _ = ∑ j', Matrix.of (fun j' j => ⟪(e j' : EuclideanSpace ℂ n),
            Matrix.toEuclideanLin A (e j : EuclideanSpace ℂ n)⟫_ℂ) j' j • f (i, j') := by
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [Submodule.coe_inner]
          rfl

/-- **Spatial tensor factorization of the isotypic components.** For a star-subalgebra $S$ of
complex matrices, $\mathbb{C}^{D}$ is the supremum of a finite family of pairwise orthogonal
isotypic components, and each component carries an orthonormal basis $(f_{i,j})$, indexed by a
multiplicity index $i < m$ and an irreducible index $j < d$, on which every $A \in S$ acts
by
$$A\,f_{i,j} = \sum_{j'} B_{j'j}\, f_{i,j'}$$
for a matrix $B \in M_{d}(\mathbb{C})$ depending only on $A$ and the component. In the adapted
basis the action
of $S$ on each component is by matrices of the form $\mathbf{1}_{m} \otimes B$; these are the
matrix-times-identity blocks of *Quantum Channels & Operations* (Wolf 2012), Theorem 6.14. -/
theorem exists_isotypic_tensor_factorization :
    ∃ C : Set (Submodule ℂ (EuclideanSpace ℂ n)), C.Finite ∧
      C.Pairwise (· ⟂ ·) ∧ sSup C = ⊤ ∧
      ∀ c ∈ C, ∃ (d m : ℕ) (f : Fin m × Fin d → EuclideanSpace ℂ n),
        Orthonormal ℂ f ∧ Submodule.span ℂ (Set.range f) = c ∧
        ∀ A ∈ S, ∃ B : Matrix (Fin d) (Fin d) ℂ, ∀ (i : Fin m) (j : Fin d),
          Matrix.toEuclideanLin A (f (i, j)) = ∑ j', B j' j • f (i, j') := by
  obtain ⟨C, hCfin, hCpair, hCsup, hC⟩ := S.exists_orthogonal_isotypic_decomposition
  refine ⟨C, hCfin, hCpair, hCsup, fun c hc => ?_⟩
  obtain ⟨Dc, hne, hfin, hirr, rfl, hortho, hsame⟩ := hC c hc
  obtain ⟨d, m, f, -, -, hon, hspan, hact⟩ :=
    S.exists_adapted_orthonormal_family_of_sameIsotype hne hfin hirr hortho hsame
  exact ⟨d, m, f, hon, hspan, hact⟩

end StarSubalgebra
