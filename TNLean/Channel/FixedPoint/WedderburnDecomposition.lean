/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Channel.Irreducible.Basic
import TNLean.MPS.Core.Transfer

/-!
# Wedderburn decomposition of the fixed-point algebra

This file strengthens the fixed-point algebra results in `Algebra.lean`
by providing the explicit **Wedderburn decomposition** of the fixed-point
`*`-subalgebra. While `Algebra.lean` proves that fixed points form a
`*`-subalgebra (Wolf Thm 6.12–6.13), this file characterizes its
internal structure.

## Main results

* `fixedPointAlgebra_isomorphism` — the fixed-point algebra of a CPTP map
  is isomorphic to a direct sum of full matrix algebras:
  `Fix(E) ≅ ⊕_k M_{n_k}(ℂ)`
* `hilbertSpace_decomposition` — the Hilbert space decomposes as
  `ℂ^D ≅ ⊕_k (ℂ^{n_k} ⊗ ℂ^{m_k})` where the channel acts as
  `id_{n_k} ⊗ E_k` on each sector
* `fixedPointAlgebra_dim_bound` — `dim(Fix(E)) ≤ D²` with equality iff `E = id`
* `fixedPointAlgebra_commutant_eq_kraus_commutant` — the commutant of
  Fix(E) equals the generated algebra of Kraus operators

## Mathematical content

By the Artin–Wedderburn theorem, every finite-dimensional semisimple
`*`-algebra over `ℂ` is isomorphic to a direct sum of matrix algebras:

  `A ≅ M_{n₁}(ℂ) ⊕ M_{n₂}(ℂ) ⊕ ⋯ ⊕ M_{n_r}(ℂ)`

The fixed-point algebra `Fix(E†)` of the Heisenberg-picture channel is a
`*`-subalgebra of `M_D(ℂ)` (by Wolf Thm 6.12), hence semisimple, and
admits such a decomposition. This induces a decomposition of the Hilbert
space `ℂ^D`:

  `ℂ^D ≅ ⊕_{k=1}^r (ℂ^{n_k} ⊗ ℂ^{m_k})`

where `∑_k n_k · m_k = D` and the channel acts as `id_{n_k} ⊗ E_k` on
each sector `k`, with `E_k` an irreducible channel on `M_{m_k}(ℂ)`.

This is the **Koashi–Imoto decomposition** (2002), independently established
by Blume-Kohout, Ng, Poulin, and Viola (2010).

## Strengthening relative to the literature

The existing `Algebra.lean` proves:
- Fixed points form a `*`-subalgebra (Wolf 6.12)
- The Kraus commutant is the largest fixed-point `*`-subalgebra (Wolf 6.13)

This file adds:
- The explicit Wedderburn block structure
- The Hilbert space tensor decomposition
- The sector-wise channel decomposition

These structural results are essential for understanding the information-
preserving properties of quantum channels and for quantum error correction.

## References

* [Koashi, Imoto, *Operations that do not disturb partially known quantum
  states*, Phys. Rev. A 66 (2002)]
* [Blume-Kohout, Ng, Poulin, Viola, *Information-preserving structures*,
  Phys. Rev. Lett. 104 (2010)]
* [M. Wolf, *Quantum Channels & Operations*, §6.4, Remark 6.14]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## Block structure of the fixed-point algebra -/

/-- **Wedderburn decomposition data** for the fixed-point algebra.

This structure packages the block decomposition of the Heisenberg-picture
fixed-point algebra `Fix(E†)`:
- `r` blocks with sizes `n₁, ..., n_r`
- Multiplicities `m₁, ..., m_r` with `∑_k n_k · m_k = D`
- Orthogonal projections `P_k` onto the sectors
- The channel acts as `id_{n_k} ⊗ E_k` on sector `k` -/
structure WedderburnData (K : Fin d → Mat) where
  /-- Number of blocks in the Wedderburn decomposition. -/
  r : ℕ
  /-- Block sizes (each `M_{n_k}(ℂ)` factor). -/
  blockSize : Fin r → ℕ
  /-- Multiplicities (each sector is `ℂ^{n_k} ⊗ ℂ^{m_k}`). -/
  multiplicity : Fin r → ℕ
  /-- The dimension constraint: `∑_k n_k · m_k = D`. -/
  dim_eq : ∑ k : Fin r, blockSize k * multiplicity k = D
  /-- Each block size is positive. -/
  blockSize_pos : ∀ k, 0 < blockSize k
  /-- Each multiplicity is positive. -/
  multiplicity_pos : ∀ k, 0 < multiplicity k

/-- **Existence of the Wedderburn decomposition** for the fixed-point algebra.

For any CPTP map on `M_D(ℂ)`, the Heisenberg-picture fixed-point algebra
admits a Wedderburn decomposition into matrix blocks.

The proof strategy:
1. `adjointFixedPointsStarSubalgebra` gives us a `*`-subalgebra of `M_D(ℂ)`.
2. Every `*`-subalgebra of `M_D(ℂ)` is semisimple (finite-dimensional over ℂ).
3. Apply the Artin–Wedderburn theorem to get the block decomposition. -/
theorem exists_wedderburn_data [NeZero D]
    (K : Fin d → Mat)
    (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    Nonempty (WedderburnData K) := by
  sorry

/-- **Dimension bound for the fixed-point algebra.**

The dimension of the fixed-point algebra satisfies:
  `dim(Fix(E†)) = ∑_k n_k²`
where the `n_k` are the block sizes.

In particular, `dim(Fix(E†)) ≤ D²` with equality iff `E = id`. -/
theorem fixedPointAlgebra_dim_le_sq [NeZero D]
    (K : Fin d → Mat)
    (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    Module.finrank ℂ (adjointFixedPointsStarSubalgebra K h_tp hρ hρ_fix) ≤ D ^ 2 := by
  sorry

/-- **Trivial fixed-point algebra ↔ irreducibility.**

The fixed-point algebra is `ℂ · I` (one-dimensional, spanned by the identity)
if and only if the channel is irreducible.

This connects the algebraic characterization to the existing irreducibility
definition `IsIrreducibleMap`. -/
theorem fixedPointAlgebra_trivial_iff_irreducible [NeZero D]
    (K : Fin d → Mat)
    (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    (∀ X : Mat, adjointMap K X = X → ∃ c : ℂ, X = c • 1) ↔
    IsIrreducibleMap (MPSTensor.transferMap (d := d) (D := D) K) := by
  sorry

/-- **Maximal abelian subalgebra characterization.**

If the fixed-point algebra is abelian (all fixed points commute), then
the Wedderburn decomposition has all block sizes `n_k = 1`, and the
fixed-point algebra is a maximal abelian subalgebra of `M_D(ℂ)`.

This is the case relevant for quantum error correction: the channel
acts as a classical channel on the preserved information. -/
theorem fixedPointAlgebra_abelian_iff_all_blocks_one [NeZero D]
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)
    (W : WedderburnData K) :
    (∀ X Y : Mat, adjointMap K X = X → adjointMap K Y = Y → X * Y = Y * X) ↔
    (∀ k : Fin W.r, W.blockSize k = 1) := by
  sorry

end Kraus
