/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs

/-!
# Rescaling invariance of block injectivity and normality

Multiplying every matrix of a matrix product state tensor by one nonzero complex scalar
multiplies every length-`N` word by the unit `ζ ^ N`.  The span of the length-`N` words is
therefore unchanged, and both block injectivity and normality are invariant under such a
rescaling.

## Main results

* `MPSTensor.wordSpan_smul_eq`: the span of the length-`N` words is invariant.
* `MPSTensor.isNBlkInjective_smul_iff`: block injectivity at every blocking length is invariant.
* `MPSTensor.isNormal_smul_iff`: normality is invariant.
* `MPSTensor.mpv_smul`: scaling a tensor by `c` multiplies the coefficients of length `N` by
  `c ^ N`.

## References

* D. Pérez-García, F. Verstraete, M. Wolf, J. I. Cirac, arXiv:quant-ph/0608197, Theorem 4,
  proof lines 765--767 (the scalar normalization taken without loss of generality).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Scaling a tensor by `c` scales MPVs by `c^N`. -/
theorem mpv_smul (c : ℂ) (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (fun i => c • A i) σ = c ^ N * mpv A σ := by
  simp only [mpv, coeff]
  rw [Kraus.evalWord_smul]
  simp [List.length_ofFn, Matrix.trace_smul]

/-- Rescaling every matrix of a tensor by a nonzero scalar preserves the span of
the length-\(N\) words.

Each length-\(N\) word acquires the common factor \(\zeta^N\), which is a unit,
and the span of a set is unchanged by a unit scalar. -/
theorem wordSpan_smul_eq {ζ : ℂ} (hζ : ζ ≠ 0) (A : MPSTensor d D) (N : ℕ) :
    Kraus.wordSpan (ζ • A) N = Kraus.wordSpan A N := by
  have hword : ∀ σ : Fin N → Fin d,
      Kraus.evalWord (ζ • A) (List.ofFn σ) =
        (ζ ^ N) • Kraus.evalWord A (List.ofFn σ) := fun σ => by
    have h := Kraus.evalWord_smul ζ A (List.ofFn σ)
    rw [List.length_ofFn] at h
    exact h
  simp only [Kraus.wordSpan]
  simp_rw [hword]
  rw [Set.range_smul]
  exact Submodule.span_smul_eq_of_isUnit _ _ (pow_ne_zero N hζ).isUnit

/-- Rescaling every matrix of a tensor by a nonzero scalar preserves block
injectivity at every blocking length. -/
theorem isNBlkInjective_smul_iff {ζ : ℂ} (hζ : ζ ≠ 0) (A : MPSTensor d D) (N : ℕ) :
    Kraus.IsNBlkInjective (ζ • A) N ↔ Kraus.IsNBlkInjective A N := by
  simp only [Kraus.IsNBlkInjective, wordSpan_smul_eq hζ A N]

/-- Rescaling every matrix of a tensor by a nonzero scalar preserves normality.

This is the scalar half of the normalization taken without loss of generality at
arXiv:quant-ph/0608197, proof lines 765--767. -/
theorem isNormal_smul_iff {ζ : ℂ} (hζ : ζ ≠ 0) (A : MPSTensor d D) :
    Kraus.IsNormal (ζ • A) ↔ Kraus.IsNormal A := by
  constructor
  · rintro ⟨N, hN, hInj⟩
    exact ⟨N, hN, (isNBlkInjective_smul_iff hζ A N).1 hInj⟩
  · rintro ⟨N, hN, hInj⟩
    exact ⟨N, hN, (isNBlkInjective_smul_iff hζ A N).2 hInj⟩

end MPSTensor
