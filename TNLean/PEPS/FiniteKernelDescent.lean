import Mathlib.Data.Finset.Basic

/-!
# Finite kernel descent for PEPS blocking arguments

This file records the finite induction used in the proof that blocking a
finite region of vertex-injective PEPS tensors preserves injectivity. In the
source proof, after the edge blocking around $e=(u,v)$, the middle block is
handled by repeatedly applying local left inverses inside
$V\setminus\{u,v\}$.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, `eq:block_to_mps`](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 979--1009.
-/

namespace TNLean
namespace PEPS

/-- A finite family of kernel conditions stable under deleting one vertex.

In the edge-blocking proof, `kernelCondition S` is the assertion $K(S)$ that a
family of boundary coefficients, with the virtual indices exposed at that
stage, gives zero after the tensors in $S$ are contracted. The deletion
implication is the step $K(S)\Rightarrow K(S\setminus\{j\})$ obtained from the
local left inverse at $j$.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 979--1009. -/
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
