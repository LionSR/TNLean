/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionBoundaryDecomposition
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace
import TNLean.MPS.MPDO.SourceBNTBlocking
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase

/-!
# Separation of simultaneously injective blocks

Simultaneous spanning of the product matrix algebra excludes gauge-phase
equivalence between distinct blocks. This supplies the separation condition
from the block-injectivity hypothesis of Cirac--Perez-Garcia--Schuch--Verstraete
2021, Section IV.C, arXiv:2011.12127, lines 2114--2129.
-/

namespace MPSTensor

/-- Distinct blocks whose word tuples span the product algebra cannot be
gauge-phase equivalent. Their periodic vectors belong to disjoint local ground
spaces and are nonzero because the boundary maps are injective.

Source: arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem not_gaugePhaseEquiv_of_wordTupleSpanTop
    {d r S : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A S)
    (i j : Fin r) (hij : i ≠ j) (h : dim j = dim i) :
    ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (A j)) (A i) := by
  rintro ⟨X, ζ, hζ, hX⟩
  have hvec : (mpv (A i) : NSiteSpace d S) = ζ ^ S • mpv (A j) := by
    ext σ
    simpa only [Pi.smul_apply, smul_eq_mul, mpv_cast_dim h (A j) S σ] using
      mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX S σ
  have hzero : (mpv (A i) : NSiteSpace d S) = 0 :=
    (Submodule.disjoint_def.mp
      ((groundSpace_iSupIndep_of_wordTupleSpanTop A hSpan).pairwiseDisjoint hij)) _
      (mpv_mem_groundSpace (A i) S)
      (hvec ▸ (groundSpace (A j) S).smul_mem (ζ ^ S)
        (mpv_mem_groundSpace (A j) S))
  exact one_ne_zero (groundSpaceMap_injective_of_isNBlkInjective
    (isNBlkInjective_of_wordTupleSpanTop A hSpan i)
    (by simpa only [← mpv_eq_groundSpaceMap_one, map_zero] using hzero))

end MPSTensor
