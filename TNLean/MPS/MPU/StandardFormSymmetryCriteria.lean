/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Index
import TNLean.MPS.MPU.SimpleCanonicalRepresentative
import TNLean.MPS.MPU.SuppliedTimeReversalCriterion
import TNLean.MPS.MPU.SuppliedTranspositionCriterion

/-!
# Local criteria for time reversal and transposition in standard form

Definition `SF` of CPSV17 defines the standard form of the two-site block
`𝒱₂` of a simple tensor `𝒱`, written in the canonical form II assumed
throughout Section III of the source (lines 350--356). Its gates come from
the source cuts of `𝒱`, normalized at the canonical right fixed point `ρ`
(lines 482--543). The two-site block of such a tensor is again in canonical
form II, so the criteria for supplied standard forms of a canonical ambient
tensor apply to every standard form in the sense of the source. The statements
below are therefore the source propositions, for any choice of the factors in
the standard form of `𝒱₂`; the construction of such a standard form for every
simple MPU is `MPOTensor.IsMPUSimple.exists_reduced_twoSiteStandardFormData`.

**Local fix (standard form of the canonical representative):** a tensor in
standard form is read as the two-site block of a simple tensor in canonical
form II, following the source's standing convention (line 326) and its
explicit "not necessarily in CF" qualifiers elsewhere (lines 710--747, 871,
1349). See `docs/paper-gaps/mpu_standard_form_canonical_convention.tex`.

**Length convention.** From line 1209 on, the source places two spins on each
site of the standard-form chain. The symmetry hypotheses are therefore stated
for `mpo (blockTwo V) N` at even `N`, that is, at original chain lengths
divisible by four, exactly as in the source propositions. They say nothing
about original lengths `2 mod 4`. For example, the one-site tensor `e^{iπ/4}·1`
has gates `u = i·1`, `v = 1` satisfying `UUdaggertrick` with `σ = -1`, while its
original length-two operator `i·1` is not self-adjoint. For the reading of
standard-form lengths see `docs/paper-gaps/mpu_standard_form_parity_gap.tex`.
Both symmetries force the source ranks of `𝒱` to equal the physical dimension,
so the index vanishes.

## Main results

* `MPOTensor.IsMPUCanonicalFormII.standardForm_even_timeReversal_iff`:
  Proposition `PropChiral`.
* `MPOTensor.IsMPUCanonicalFormII.standardForm_even_transposition_iff`:
  Proposition `prop:local-char-transposition`.
* `MPOTensor.IsMPUCanonicalFormII.index_eq_zero_of_standardForm_even_mpo_eq_adjoint`
  and `MPOTensor.IsMPUCanonicalFormII.index_eq_zero_of_standardForm_even_mpo_eq_transpose`:
  the zero-index observations preceding the two propositions.

## References

* arXiv:1703.09188, Definition `SF`, lines 603--622; Proposition `PropChiral`,
  lines 1196--1252; Proposition `prop:local-char-transposition`, lines
  1256--1288.
-/

open scoped Matrix Kronecker

namespace MPOTensor

namespace IsMPUCanonicalFormII

variable {d D : ℕ} {V : MPOTensor d D}

/-- A simple tensor in canonical form II whose right source rank is the
physical dimension has index zero. Source: arXiv:1703.09188, Definition
`def:index` and the formulas following it, lines 681--688. -/
theorem index_eq_zero_of_rightRank_eq_phys (hV : IsMPUCanonicalFormII V)
    (hsimple : IsMPUSimple V) (hr : r[V] = d) : hV.index = 0 := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hV.neZero_phys.out
  have hS : IsMPUSimple (MPOTensor.blockTensor V 1) := by
    rw [blockTensor_one_eq_reindexPhysical]
    exact hsimple.reindexPhysical _
  rw [hV.index_eq_logb_rightRank_div Nat.one_pos hS, blockTensor_one_eq_reindexPhysical,
    rightRank_reindexPhysical, hr, pow_one, div_self hd, Real.logb_one]

/-- Time-reversal invariance of the standard form at every even length forces
the index of the simple canonical tensor to vanish. Source: arXiv:1703.09188,
the discussion preceding Proposition `PropChiral`, lines 1199--1207. -/
theorem index_eq_zero_of_standardForm_even_mpo_eq_adjoint
    (hV : IsMPUCanonicalFormII V) (hsimple : IsMPUSimple V)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᴴ) :
    hV.index = 0 :=
  hV.index_eq_zero_of_rightRank_eq_phys hsimple
    (hV.sourceRanks_eq_phys_of_standardForm_even_mpo_eq_adjoint hsimple hTR).1

/-- Transposition invariance of the standard form at every even length forces
the index of the simple canonical tensor to vanish. Source: arXiv:1703.09188,
the discussion preceding Proposition `prop:local-char-transposition`, lines
1258--1263. -/
theorem index_eq_zero_of_standardForm_even_mpo_eq_transpose
    (hV : IsMPUCanonicalFormII V) (hsimple : IsMPUSimple V)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᵀ) :
    hV.index = 0 :=
  hV.index_eq_zero_of_rightRank_eq_phys hsimple
    ((hV.twoSiteStandardFormData hsimple).intermediateRanks_eq_phys_of_even_mpo_eq_transpose
      hV.blockTwo hTR).1

/-- **Local characterization of time reversal.** Let `u, v` be the gates of a
standard form of the two-site block of a tensor in canonical form II. The
generated MPU satisfies `U⁽ᴺ⁾ = U⁽ᴺ⁾†` for every even `N` if and only if the
intermediate dimensions equal the physical dimension and, in these
coordinates, there are a unitary `x` and a sign `σ = ±1` with
`(1 ⊗ v₂₃ ⊗ 1)(u₁₂ ⊗ u₃₄) = σ (x₁₂ ⊗ x₃₄†)(1 ⊗ v₂₃† ⊗ 1)`.
The rank equalities are part of the conclusion of the forward direction.

Source: arXiv:1703.09188, Proposition `PropChiral`, equation `UUdaggertrick`,
lines 1214--1225, with proof at lines 1230--1252. -/
theorem standardForm_even_timeReversal_iff
    {ℓ r : ℕ} (hV : IsMPUCanonicalFormII V)
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (MPOTensor.blockTwo V) u v) :
    (∀ N : ℕ, 1 < N → Even N →
        mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᴴ) ↔
      ∃ (hr : r = d) (hl : ℓ = d) (σ : ℂ)
        (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
        let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
          (Equiv.refl _) u
        let v₀ := Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
        (σ = 1 ∨ σ = -1) ∧
        staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
          σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
              (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
            (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᴴ :=
  S.even_timeReversal_iff_exists_certificate hV.blockTwo

/-- **Local characterization of transposition.** Let `u, v` be the gates of a
standard form of the two-site block of a tensor in canonical form II. The
generated MPU satisfies `U⁽ᴺ⁾ = U⁽ᴺ⁾ᵀ` for every even `N` if and only if the
intermediate dimensions equal the physical dimension and, in these
coordinates, there are a unitary `x` and a real `φ` with
`(1 ⊗ v₂₃ ⊗ 1)(u₁₂ ⊗ u₃₄) = e^{iφ} (x₁₂ ⊗ x₃₄ᵀ)(1 ⊗ v₂₃ᵀ ⊗ 1)`.

Source: arXiv:1703.09188, Proposition `prop:local-char-transposition`,
equation `UUtransposetrick`, lines 1266--1276, with proof at lines
1278--1283. -/
theorem standardForm_even_transposition_iff
    {ℓ r : ℕ} (hV : IsMPUCanonicalFormII V)
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (MPOTensor.blockTwo V) u v) :
    (∀ N : ℕ, 1 < N → Even N →
        mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᵀ) ↔
      ∃ (hr : r = d) (hl : ℓ = d) (φ : ℝ)
        (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
        let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
          (Equiv.refl _) u
        let v₀ := Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
        staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
          Complex.exp ((φ : ℂ) * Complex.I) •
            ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
              (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) *
            (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᵀ := by
  refine ⟨S.exists_transposition_exponential_certificate hV.blockTwo, ?_⟩
  rintro ⟨hr, hl, φ, x, hlocal⟩
  refine (S.even_transposition_iff_exists_certificate hV.blockTwo).mpr
    ⟨hr, hl, Complex.exp ((φ : ℂ) * Complex.I), x, ?_, hlocal⟩
  rw [Complex.norm_exp_ofReal_mul_I]

end IsMPUCanonicalFormII

end MPOTensor
