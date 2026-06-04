import Mathlib.Data.Finset.Basic

/-!
# Finite kernel descent for PEPS blocking arguments

This file records a finite induction used to formalize the fact that
contracting a finite region of vertex-injective PEPS tensors yields an
injective tensor.

The source establishes that fact in one step. An injective tensor admits a
one-sided inverse, and the inverse of a contraction of two injective tensors
is the contraction of their inverses, up to the connecting bond dimension
(arXiv:1804.04964, Section 3; the inverse-of-a-contraction identity in
`Papers/1804.04964/paper_normal.tex`, lines 205--250). The finite induction
packaged here is the formalization route towards that fact, not a separate
step in the source: deleting one vertex of the region at a time, each step
uses a one-sided inverse, until the empty contraction is reached. The region
contracted is the middle block $V\setminus\{u,v\}$ of the edge blocking
`eq:block_to_mps`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, `eq:block_to_mps`](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 205--250 (a contraction of
  injective tensors is injective) and 981--1009 (`eq:block_to_mps`).
-/

namespace TNLean
namespace PEPS

/-- A finite family of kernel conditions stable under deleting one vertex.

In the edge-blocking proof, `kernelCondition S` is the assertion $K(S)$ that a
family of boundary coefficients, with the virtual indices exposed at that
stage, gives zero after the tensors in $S$ are contracted. The deletion
implication is the step $K(S)\Rightarrow K(S\setminus\{j\})$ obtained from the
one-sided inverse at $j$.

Source: the one-sided inverse of an injective tensor, arXiv:1804.04964,
Section 3, `Papers/1804.04964/paper_normal.tex`, lines 205--250; applied to the
middle block of `eq:block_to_mps`, lines 981--1009. -/
structure FiniteRegionKernelDescent (V : Type*) [DecidableEq V] where
  /-- The kernel condition attached to a finite vertex set. -/
  kernelCondition : Finset V → Prop
  /-- The local deletion step $K(S)\Rightarrow K(S\setminus\{j\})$. -/
  erase_vertex :
    ∀ {S : Finset V} {j : V}, j ∈ S → kernelCondition S → kernelCondition (S.erase j)

namespace FiniteRegionKernelDescent

variable {V : Type*}

/-- Iterating the one-vertex deletion implication gives $K(S)\Rightarrow
K(\varnothing)$.

This is the finite-induction part of the middle-block injectivity proof after
`eq:block_to_mps`: once every local left inverse gives
$K(S)\Rightarrow K(S\setminus\{j\})$, the kernel condition descends from the
whole blocked region to the empty contraction.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 979--1009. -/
lemma descend_to_empty [DecidableEq V] (c : FiniteRegionKernelDescent V) {S : Finset V} :
    c.kernelCondition S → c.kernelCondition ∅ := by
  induction S using Finset.induction with
  | empty =>
      intro h
      exact h
  | insert j S hj ih =>
      intro h
      have hErase : c.kernelCondition S := by
        simpa [Finset.erase_insert, hj] using
          c.erase_vertex (S := insert j S) (j := j) (by simp) h
      exact ih hErase

/-- A terminal consequence of $K(\varnothing)$ holds already at any finite
region satisfying $K(S)$.

In the PEPS blocking proof, the terminal consequence is that every boundary
coefficient is zero after the empty contraction has been reached.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 979--1009. -/
lemma descend [DecidableEq V] (c : FiniteRegionKernelDescent V) {S : Finset V} {Q : Prop}
    (hEmpty : c.kernelCondition ∅ → Q) :
    c.kernelCondition S → Q :=
  fun hS => hEmpty (c.descend_to_empty hS)

end FiniteRegionKernelDescent

end PEPS
end TNLean
