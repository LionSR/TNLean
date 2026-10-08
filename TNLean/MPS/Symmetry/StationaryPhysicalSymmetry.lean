/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.StationaryPhysicalOverlap
import TNLean.MPS.Symmetry.PureTwistedSpectrum
import TNLean.MPS.Symmetry.PhysicalStringEndpoints

/-!
# Local symmetry of the stationary physical density family

For a fixed on-site unitary u, invariance of every physical block density
under u⊗N is equivalent to spectral radius one of the u-twisted transfer
map. The tensor is in the pure canonical finitely correlated form: Λ is
faithful and trace one, the ordinary transfer map is unital, its adjoint
fixes Λ, and its only peripheral eigenmatrices are scalar multiples of the
identity at eigenvalue one. One-site injectivity is not assumed.

The forward spectral implication uses the peripheral unitary intertwiner
and its invariance of Λ. The converse compares the uniform D⁻² purity
bound with decay of a quadratic mixed-transfer contraction. The physical
symmetry is not replaced by an assumed virtual gauge relation.

The statement fixes u and includes scalar unitaries. It is separate from
existence of a nonscalar twist with string order.

## References

* Pérez-García, Wolf, Sanz, Verstraete and Cirac, arXiv:0802.0447,
  Theorem 2 and its proof, lines 297–323.
-/

open scoped Matrix BigOperators Kronecker ComplexOrder MatrixOrder TNOperatorSpace Topology
open Filter

namespace MPSTensor

variable {d D : ℕ}

/-- The rotated tensor's mixed transfer map is the physical twisted transfer
map. Source: arXiv:0802.0447, display EU, lines 166–181. -/
private theorem mixedMapLM_rotatePhysical_eq_twistedTransferMap
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ) :
    Kraus.mixedMapLM (rotatePhysical u A) A = twistedTransferMap A u := by
  ext X : 1
  rw [twistedTransferMap_eq_sum_rotatePhysical, Kraus.mixedMapLM_apply]

/-- For a canonical tensor with irreducible transfer map, spectral radius one
is equivalent to invariance of every stationary physical density. This
supporting statement makes the irreducibility requirement explicit; the
pure-FCS statement below derives it from the source hypotheses.
Source: arXiv:0802.0447, Theorem 2, lines 297–323. -/
private theorem stationaryBlockDensity_invariant_iff_spectralRadius_eq_one_of_irreducible
    (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef)
    (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1) :
    (∀ N, blockKron N u * stationaryBlockDensity A Λ N * (blockKron N u)ᴴ =
      stationaryBlockDensity A Λ N) ↔
      spectralRadius ℂ (Module.End.toContinuousLinearMap
        (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) = 1 := by
  have : NeZero D := ⟨by rintro rfl; simp at hΛtr⟩
  constructor
  · intro hsym
    by_contra hne
    have hlt := lt_of_le_of_ne
      (twistedTransfer_spectralRadius_le_one_of_irreducible A hIrr u hu hNorm) hne
    have hgap : Kraus.mixedMapSpectralRadius (rotatePhysical u A) A < 1 := by
      simpa only [Kraus.mixedMapSpectralRadius,
        mixedMapLM_rotatePhysical_eq_twistedTransferMap] using hlt
    have hdecay := stationaryBlockDensity_overlap_tendsto_zero A (rotatePhysical u A) Λ
      (Kraus.mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one _ _ hgap)
    have hsame N : stationaryBlockDensity (rotatePhysical u A) Λ N =
        stationaryBlockDensity A Λ N :=
      (stationaryBlockDensity_rotatePhysical A Λ u N).trans (hsym N)
    have hp : Tendsto (fun N => (stationaryBlockDensity A Λ N ^ 2).trace.re)
        atTop (𝓝 0) := by
      simpa only [hsame, ← pow_two, Complex.zero_re, Function.comp_def] using
        (Complex.continuous_re.tendsto 0).comp hdecay
    have hzero : (D : ℝ)⁻¹ ^ 2 ≤ 0 := ge_of_tendsto' hp
      (inv_sq_le_purity_stationaryBlockDensity A hΛpos.posSemidef hΛtr hNorm)
    exact (sq_pos_of_pos (inv_pos.mpr
      (Nat.cast_pos.mpr (NeZero.pos D)))).not_ge hzero
  · intro hrad
    obtain ⟨V, μ, hV, hμ, hInter⟩ :=
      (twistedTransfer_spectralRadius_eq_one_iff_intertwiner A hIrr u hu hNorm).mp hrad
    have hΛ := boundaryState_invariant_of_virtualUnitary_of_irreducible A hIrr u hu
      Λ hΛpos hΛtr hΛfix V μ hV (mul_eq_one_comm.mp hV) hμ hInter
    intro N
    rw [← stationaryBlockDensity_rotatePhysical]
    exact stationaryBlockDensity_eq_of_unitary_gaugePhase A (rotatePhysical u A)
      Λ V μ hV hμ hΛ hInter N

/-- PGWSVC08 Theorem 2 for the actual stationary physical density matrices:
for a fixed physical unitary u, every N-site density is invariant under
u⊗N exactly when the twisted transfer spectral radius is one. All canonical
pure-FCS assumptions are the source assumptions; one-site injectivity and
nonscalarity of u are not required.
Source: arXiv:0802.0447, Theorem 2, lines 297–323. -/
theorem stationaryBlockDensity_invariant_iff_spectralRadius_eq_one
    (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef)
    (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
        ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1) :
    (∀ N, blockKron N u * stationaryBlockDensity A Λ N * (blockKron N u)ᴴ =
      stationaryBlockDensity A Λ N) ↔
      spectralRadius ℂ (Module.End.toContinuousLinearMap
        (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) = 1 := by
  have hIrr := (pureCanonical_isIrreducibleMap_and_isPrimitive A Λ
    hΛpos hΛfix hNorm hPure).1
  exact stationaryBlockDensity_invariant_iff_spectralRadius_eq_one_of_irreducible
    A Λ hΛpos hΛtr hΛfix hNorm hIrr u hu

end MPSTensor
