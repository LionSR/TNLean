/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLTStringOrder
import TNLean.MPS.Examples.Cluster
import TNLean.MPS.Symmetry.EntanglementSpectrum

/-!
# AKLT and cluster states: doubly degenerate entanglement spectrum

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
paragraph "Entanglement spectrum and edge modes",
`Papers/2011.12127/TN-Review-main.tex` lines 1171–1172: a non-trivial SPT phase has
an entanglement spectrum in which every eigenvalue is degenerate, because the
projective virtual representation has no one-dimensional invariant subspace.
Review: arXiv:2011.12127, Appendix A, "The AKLT state" and "The cluster state".

**Formalized here.** For the length-`2` blocked AKLT tensor and the length-`2`
blocked cluster tensor, both injective, every positive definite fixed point `Λ` of
the adjoint transfer map has only even-dimensional eigenspaces.  The anticommuting
virtual gauges of the two `Z₂` generators (`iσy`, `σz` for AKLT; `σz`, `σx` for
the cluster state) enter through
`MPSTensor.even_finrank_eigenspace_of_anticommuting_gauges`.

## Main results

* `MPSTensor.akltBlocked_even_finrank_eigenspace`
* `MPSTensor.clusterBlocked_even_finrank_eigenspace`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-- An intertwining relation `Tᵢ R = R Aᵢ` is the gauge relation `Tᵢ = 1 · R Aᵢ R⁻¹`. -/
private lemma eq_one_smul_conj_of_intertwine {T A : Matrix (Fin D) (Fin D) ℂ}
    (R : GL (Fin D) ℂ) (h : T * R = R * A) :
    T = (1 : ℂ) • ((R : Matrix (Fin D) (Fin D) ℂ) * A *
      ((R⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  rw [one_smul, ← h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- **Doubly degenerate entanglement spectrum of the AKLT state.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1172).  Every eigenspace of every positive definite fixed point of the
adjoint transfer map of the blocked AKLT tensor has even dimension. -/
theorem akltBlocked_even_finrank_eigenspace {Λ : Matrix (Fin 2) (Fin 2) ℂ}
    (hΛpos : Λ.PosDef) (hΛfix : Kraus.transferMap (fun i => (akltBlocked i)ᴴ) Λ = Λ)
    (μ : ℂ) : Even (Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' Λ) μ)) := by
  have hgauge (g : Multiplicative (ZMod 2 × ZMod 2)) (I : Fin (blockPhysDim 3 2)) :
      ∑ j, akltBlockedZ2Z2Action g I j • akltBlocked j =
        (1 : ℂ) • ((akltProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) * akltBlocked I *
          (((akltProjRep.X g)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [one_smul]
    exact twistedTensor_blockTensor_eq_gauge (fun i =>
      by simpa using eq_one_smul_conj_of_intertwine _ (akltTensor_twist_intertwine g i)) 2 I
  exact even_finrank_eigenspace_of_anticommuting_gauges akltBlocked_isInjective
    akltBlocked_transferMap_one hΛpos hΛfix (akltBlockedZ2Z2Action_unitary _)
    (akltBlockedZ2Z2Action_unitary _) one_ne_zero one_ne_zero
    (hgauge (Multiplicative.ofAdd (1, 0))) (hgauge (Multiplicative.ofAdd (0, 1)))
    akltProjRep_generators_anticomm μ

/-- **Doubly degenerate entanglement spectrum of the cluster state.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1172).  Every eigenspace of every positive definite fixed point of the
adjoint transfer map of the blocked cluster tensor has even dimension. -/
theorem clusterBlocked_even_finrank_eigenspace {Λ : Matrix (Fin 2) (Fin 2) ℂ}
    (hΛpos : Λ.PosDef) (hΛfix : Kraus.transferMap (fun i => (clusterBlocked i)ᴴ) Λ = Λ)
    (μ : ℂ) : Even (Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' Λ) μ)) := by
  have hgauge (g : Multiplicative (ZMod 2 × ZMod 2)) (I : Fin 4) :
      ∑ j, clusterZ2Z2Action g I j • clusterBlocked j =
        (1 : ℂ) • ((clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) * clusterBlocked I *
          (((clusterProjRep.X g)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :=
    eq_one_smul_conj_of_intertwine _ (clusterBlocked_twist_intertwine g I)
  exact even_finrank_eigenspace_of_anticommuting_gauges clusterBlocked_isInjective
    clusterBlocked_transferMap_one hΛpos hΛfix (clusterZ2Z2Action_unitary _)
    (clusterZ2Z2Action_unitary _) one_ne_zero one_ne_zero
    (hgauge (Multiplicative.ofAdd (1, 0))) (hgauge (Multiplicative.ofAdd (0, 1)))
    (by simpa [clusterProjRep, clusterRepX] using cluster_gauge_anticomm) μ

end MPSTensor
