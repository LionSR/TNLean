/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalRotation
import TNLean.MPS.ParentHamiltonian.CompactBlockParentGap

/-!
# Simultaneous word spanning under physical transformations

Applying the same physical linear map to every block cannot enlarge the span
of their joint word evaluations at any prescribed length. An invertible map
preserves that span. In particular, the common one-site injectivity used after
initial blocking in arXiv:1010.3732 is preserved along the deformation
\(P_\gamma=Q_\gamma P_0\). This is a joint span statement; individual normality
of the blocks does not replace its hypothesis.

Source: arXiv:1010.3732, the isometric deformation and Appendix A.
-/

open scoped Matrix BigOperators Topology

namespace MPSTensor

variable {d e r : ℕ} {dim : Fin r → ℕ}

/-- A physical linear transformation cannot enlarge the joint word span.
Source: arXiv:1010.3732, Appendix A, the deformation of the block matrices. -/
theorem span_wordTuple_rotatePhysical_le
    (M : Matrix (Fin e) (Fin d) ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (L : ℕ) :
    Submodule.span ℂ (Set.range (wordTuple (fun j => rotatePhysical M (A j)) L)) ≤
      Submodule.span ℂ (Set.range (wordTuple A L)) := by
  apply Submodule.span_le.2
  rintro _ ⟨w, rfl⟩
  have hexp : wordTuple (fun j => rotatePhysical M (A j)) L w =
      ∑ t : Fin L → Fin d, (∏ n, M (w n) (t n)) • wordTuple A L t := by
    ext j a b
    simp [wordTuple, evalWord_rotatePhysical_ofFn, Finset.sum_apply]
  rw [hexp]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨t, rfl⟩)

/-- A physical map with a left inverse preserves the joint word span, including
rectangular embeddings. Source: arXiv:1010.3732, the isometric deformation. -/
theorem span_wordTuple_rotatePhysical_eq_of_leftInverse
    (M : Matrix (Fin e) (Fin d) ℂ) (N : Matrix (Fin d) (Fin e) ℂ)
    (hNM : N * M = 1) (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    Submodule.span ℂ (Set.range (wordTuple (fun j => rotatePhysical M (A j)) L)) =
      Submodule.span ℂ (Set.range (wordTuple A L)) := by
  apply le_antisymm (span_wordTuple_rotatePhysical_le M A L)
  simpa only [rotatePhysical_rotatePhysical, hNM, rotatePhysical_one] using
    span_wordTuple_rotatePhysical_le N (fun j => rotatePhysical M (A j)) L

/-- An invertible physical transformation preserves simultaneous spanning at
any fixed length. Source: arXiv:1010.3732, Appendix A. -/
theorem wordTupleSpanTop_rotatePhysical_iff
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : IsUnit M)
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    WordTupleSpanTop (fun j => rotatePhysical M (A j)) L ↔ WordTupleSpanTop A L := by
  unfold WordTupleSpanTop
  rw [span_wordTuple_rotatePhysical_eq_of_leftInverse M M⁻¹
    (Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).1 hM))]

/-- Physical transformations of a continuous tensor family are continuous.
Source: arXiv:1010.3732, the path defined following eq. (1d-iso:polardec). -/
theorem continuous_rotatePhysical_family
    {X : Type*} [TopologicalSpace X] {D : ℕ}
    (M : X → Matrix (Fin e) (Fin d) ℂ) (A : X → MPSTensor d D)
    (hM : Continuous M) (hA : Continuous A) :
    Continuous fun x => rotatePhysical (M x) (A x) := by
  exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
    (hM.matrix_elem i j).smul ((continuous_apply j).comp hA)

/-- A compact continuous family of invertible physical transformations of a
fixed simultaneously injective block tensor has a common periodic gap.
For a jointly one-site injective tensor, this applies directly at range two.
Source: arXiv:1010.3732, Appendix A, and the isometric path at lines 589--594. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_physicalAction
    {X : Type*} [TopologicalSpace X] [NeZero d] [∀ j, NeZero (dim j)]
    (A : (j : Fin r) → MPSTensor d (dim j)) {S R : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (M : X → Matrix (Fin d) (Fin d) ℂ) (hM : Continuous M)
    (hUnit : ∀ x, IsUnit (M x)) (μ : X → Fin r → ℂ) (hμ : ∀ x j, μ x j ≠ 0)
    {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x)
          (fun j => rotatePhysical (M x) (A j))) R N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ x)
            (fun j => rotatePhysical (M x) (A j))) R N v‖ := by
  exact exists_uniform_parentHamiltonianES_toTensorFromBlocks_gap_of_compact_all_lengths
    μ (fun x j => rotatePhysical (M x) (A j)) hμ
    (fun j => continuous_rotatePhysical_family M (fun _ => A j) hM continuous_const)
    hS (fun x => (wordTupleSpanTop_rotatePhysical_iff (M x) (hUnit x) A S).2 hSpan)
    hR hK

end MPSTensor
