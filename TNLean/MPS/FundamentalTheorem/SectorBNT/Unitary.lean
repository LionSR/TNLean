/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch
import TNLean.MPS.FundamentalTheorem.UnitaryGauge

/-!
# Unitary refinement of proportional BNT sector matching

The proportional Fundamental Theorem matches the basis normal tensors of two
canonical forms by gauge-phase equivalences. When the basis tensors satisfy the
BNT canonical form hypotheses of left-canonicity and irreducibility, the
matched gauges may be chosen unitary.

This is the proportional part of Canonical Form II in Cirac et al.,
arXiv:1606.00608, Corollary C.5, lines 1197–1199.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **Canonical Form II unitary refinement of proportional BNT matching.**

Let two BNT canonical forms generate eventually nonzero proportional MPV
families.  Their basis normal tensors can be matched bijectively so that each
matched pair has the same bond dimension and differs by a unit phase and a
unitary conjugation.

The BNT hypotheses already include left canonicity and irreducibility for each
basis tensor.  Thus no hypothesis beyond those of the proportional BNT theorem
is needed for this refinement.

Source: Cirac et al., arXiv:1606.00608, Corollary C.5, lines 1197–1199. -/
theorem ft_sector_bnt_proportional_unitary_sector_match_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (ζ : Fin Q.basisCount → ℂ)
      (U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      ∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
  classical
  obtain ⟨β, hDim, ζ₀, X, hζ₀, hConj, _hMpv⟩ :=
    ft_sector_bnt_proportional_sector_match_witnesses hP hQ hProp
  let hGPE : ∀ k : Fin Q.basisCount,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) (Q.basis k) :=
    fun k => ⟨X k, ζ₀ k, by
      intro hzero
      simpa [hzero] using hζ₀ k, hConj k⟩
  have hUnitary : ∀ k : Fin Q.basisCount,
      ∃ (U : Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧
        ∀ i, Q.basis k i = ζ •
          ((U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
    intro k
    letI : NeZero (Q.basisDim k) := ⟨ne_of_gt (hQ.basis_dim_pos k)⟩
    apply exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible (hGPE k)
    · exact (leftCanonical_cast_dim (hDim k) (P.basis (β k))).2
        (hP.basis_left_canonical (β k))
    · exact hQ.basis_left_canonical k
    · exact (isIrreducibleTensor_cast_dim (hDim k) (P.basis (β k))).2
        (hP.basis_irreducible (β k))
    · exact hQ.basis_irreducible k
  let U : (k : Fin Q.basisCount) →
      Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ :=
    fun k => (hUnitary k).choose
  let ζ : Fin Q.basisCount → ℂ :=
    fun k => (hUnitary k).choose_spec.choose
  refine ⟨β, hDim, ζ, U, ?_, ?_⟩
  · intro k
    exact (hUnitary k).choose_spec.choose_spec.1
  · intro k i
    exact (hUnitary k).choose_spec.choose_spec.2 i

end MPSTensor
