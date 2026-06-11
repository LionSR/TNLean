import TNLean.PEPS.RegionBlock.Basic

/-!
# Splitting the region vertex product across an inserted site

For a region `R` and a vertex `v ∉ R`, the inserted region `insert v R` carries
one extra physical site. This file isolates the single algebraic step that the
block-granularity one-site quotient of the normal PEPS Fundamental Theorem rests
on (arXiv:1804.04964, Section 3, proof of Theorem 3, the comparison of the
one-site-different regions `R` and `S`, lines 1407--1443 and 1544 of
`Papers/1804.04964/paper_normal.tex`): the product of the tensors over the
vertices of `insert v R` factors as the tensor at the inserted site `v` times the
product of the tensors over the vertices of `R`.

The blocked-region weight of `insert v R` is a constrained sum of this vertex
product over global virtual configurations. The split below is therefore the
vertex-product half of the one-site quotient: it isolates `A.component v` from the
remaining region product, the residual being exactly the vertex product of the
smaller region `R`. The full quotient still needs the boundary-configuration
bookkeeping relating the crossing edges of `insert v R` to those of `R` together
with the bonds incident to `v`; that bookkeeping is recorded as the remaining
obstruction of the per-vertex relation in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1544 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The equivalence between the vertices of `R` and the non-`v` vertices of
`insert v R`, for `v ∉ R`. -/
noncomputable def insertVertexComplEquiv (R : Finset V) {v : V} (hv : v ∉ R) :
    {w : V // w ∈ R} ≃
      {w : {x : V // x ∈ insert v R} //
        w ∈ ({⟨v, Finset.mem_insert_self v R⟩} : Finset {x : V // x ∈ insert v R})ᶜ} where
  toFun w := ⟨⟨w.1, Finset.mem_insert_of_mem w.2⟩, by
    simp only [Finset.mem_compl, Finset.mem_singleton]
    intro hc
    have : w.1 = v := congrArg Subtype.val hc
    exact hv (this ▸ w.2)⟩
  invFun w := ⟨w.1.1, by
    have hne : w.1.1 ≠ v := by
      intro hc
      have : w.1 = ⟨v, Finset.mem_insert_self v R⟩ := Subtype.ext hc
      exact (Finset.mem_compl.mp w.2) (Finset.mem_singleton.mpr this)
    rcases Finset.mem_insert.mp w.1.2 with h | h
    · exact absurd h hne
    · exact h⟩
  left_inv w := rfl
  right_inv w := by ext; rfl

/-- The physical configuration on a region `R`, obtained by restricting a physical
configuration on the inserted region `insert v R`. -/
noncomputable def restrictInsertPhysical (R : Finset V) {v : V}
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)) :
    RegionPhysicalConfig (V := V) (d := d) R :=
  fun w => σ ⟨w.1, Finset.mem_insert_of_mem w.2⟩

omit [Fintype V] in
/-- **The region vertex product splits across the inserted site.**

For a vertex `v ∉ R`, the product of the tensors `A.component w` over the
vertices of `insert v R`, at a fixed global virtual configuration `ζ` and a
physical configuration `σ` on `insert v R`, equals the tensor at the inserted site
`v` (read at `ζ`'s local configuration at `v` and the physical leg `σ` assigns to
`v`) times the product over the vertices of `R` of the same tensors, with the
physical legs restricted to `R`.

This is the vertex-product half of the block-granularity one-site quotient: the
inserted site `v` is isolated from the residual region product, which is exactly
the vertex product of `R`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem prod_region_insert_split (A : Tensor G d) (R : Finset V) {v : V} (hv : v ∉ R)
    (ζ : VirtualConfig A)
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)) :
    (∏ w : {w : V // w ∈ insert v R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) =
      A.component v (fun ie => ζ ie.1) (σ ⟨v, Finset.mem_insert_self v R⟩) *
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
          (restrictInsertPhysical (V := V) (d := d) R σ w) := by
  classical
  -- Factor the inserted site `v` out of the product over `insert v R`.
  rw [Fintype.prod_eq_mul_prod_compl
      (⟨v, Finset.mem_insert_self v R⟩ : {w : V // w ∈ insert v R})
      (fun w : {w : V // w ∈ insert v R} => A.component w.1 (fun ie => ζ ie.1) (σ w))]
  congr 1
  -- Read the residual product over the complement finset as a product over its coe-sort,
  -- then reindex it through the vertices of `R`.
  rw [← Finset.prod_coe_sort
      (({⟨v, Finset.mem_insert_self v R⟩} : Finset {x : V // x ∈ insert v R})ᶜ)
      (fun w : {x : V // x ∈ insert v R} => A.component w.1 (fun ie => ζ ie.1) (σ w))]
  rw [← Equiv.prod_comp (insertVertexComplEquiv (V := V) R hv)
      (fun w => A.component w.1.1 (fun ie => ζ ie.1) (σ w.1))]
  rfl

end PEPS
end TNLean
