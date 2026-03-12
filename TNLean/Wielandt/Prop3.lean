/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.PrimitiveEquiv
import TNLean.Wielandt.Prop3_ac
import TNLean.Wielandt.Prop3_cb

/-!
# Proposition 3 — Full Equivalence (arXiv:0909.5347)

This file assembles the paper-facing development of **Proposition 3** from
Sanz–Pérez-García–Wolf–Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347, Section II), and packages the full circular equivalence.

## Proposition 3 (paper statement)

The following are equivalent for an MPS tensor `A` with `∑ Aᵢ† Aᵢ = 1`:

* **(a)** `IsPrimitivePaper A`: there exists `q` such that for all `|φ⟩ ≠ 0`,
  `H_q(A,φ) = ℂ^D`.
* **(b)** `HasEventuallyFullKrausRank A`: there exists `i` with `S_i(A) = M_D(ℂ)`
  (equivalently, `IsNormal A`).
* **(c)** `IsStronglyIrreduciblePaper A`: `E_A` is irreducible, has a
  positive-definite fixed point, and peripheral spectrum `{1}`.

## Directions proved

| Direction | Theorem | File |
|-----------|---------|------|
| **(b) → (a)** | `isPrimitivePaper_of_hasEventuallyFullKrausRank` | `PrimitiveEquiv.lean` |
| **(a) → (c)** | `isStronglyIrreduciblePaper_of_isPrimitivePaper` | `Prop3_ac.lean` |
| **(c) → (b)** | `hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper` | `Prop3_cb.lean` |

Together these close the cycle **(a) → (c) → (b) → (a)**, establishing the
full equivalence of all three conditions.

## Full-equivalence corollaries

* `primitivePaper_iff_hasEventuallyFullKrausRank`: **(a) ↔ (b)**
* `primitivePaper_iff_stronglyIrreducible`: **(a) ↔ (c)**
* `hasEventuallyFullKrausRank_iff_stronglyIrreducible`: **(b) ↔ (c)**

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347](https://arxiv.org/abs/0909.5347), Proposition 3
- Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## Direction (b) → (a) -/

/-- **Proposition 3 (b)→(a)**: Eventually full Kraus rank implies paper-primitivity.

If `{A₁,…,Aₐ}` has eventually full Kraus rank (there exists `i` with
`S_i(A) = M_D(ℂ)`), then the transfer map `E_A` is primitive: for every
nonzero `|φ⟩`, there exists a uniform `q` with `H_q(A,φ) = ℂ^D`.

Re-exported from `PrimitiveEquiv.lean`. -/
theorem prop3_ba (A : MPSTensor d D)
    (hA : HasEventuallyFullKrausRank A) :
    IsPrimitivePaper A :=
  isPrimitivePaper_of_hasEventuallyFullKrausRank A hA

/-- **Proposition 3 (b)→(a), `IsNormal` version**: `IsNormal A` implies
paper-primitivity.

This is the same as `prop3_ba` but takes the library's `IsNormal` predicate
directly. -/
theorem prop3_ba_isNormal (A : MPSTensor d D)
    (hA : IsNormal A) :
    IsPrimitivePaper A :=
  isPrimitivePaper_of_isNormal A hA

/-! ## Direction (a) → (c) -/

/-- **Proposition 3 (a)→(c)**: Paper-primitivity implies strong irreducibility.

If the MPS tensor `A` is paper-primitive and normalized (`∑ Aᵢ† Aᵢ = 1`), then
it is strongly irreducible: the transfer map `E_A` is irreducible, has a
positive-definite fixed point, and peripheral spectrum `{1}`.

Re-exported from `Prop3_ac.lean`. -/
theorem prop3_ac [NeZero D] (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    IsStronglyIrreduciblePaper A :=
  isStronglyIrreduciblePaper_of_isPrimitivePaper A hNorm hPrim

/-! ## Direction (c) → (b) -/

/-- **Proposition 3 (c)→(b)**: Strong irreducibility implies eventually full
Kraus rank.

If the MPS tensor `A` is strongly irreducible (`E_A` irreducible, PosDef
fixed point, peripheral spectrum `{1}`) and normalized (`∑ Aᵢ† Aᵢ = 1`),
then `A` has eventually full Kraus rank (`∃ i, S_i(A) = M_D(ℂ)`).

Re-exported from `Prop3_cb.lean`. -/
theorem prop3_cb [NeZero D] (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hSI : IsStronglyIrreduciblePaper A) :
    HasEventuallyFullKrausRank A :=
  hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper A hNorm hSI

/-! ## Combined directions -/

/-- **Proposition 3 (b)→(c)**: Eventually full Kraus rank implies strong irreducibility.

Combines the two proved directions: `HasEventuallyFullKrausRank → IsPrimitivePaper`
and `IsPrimitivePaper → IsStronglyIrreduciblePaper`.

Paper: "The following are equivalent: (a), (b), (c)" — this packages (b)→(a)→(c)
as a single implication. -/
theorem primitivePaper_implies_stronglyIrreducible [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : HasEventuallyFullKrausRank A) :
    IsStronglyIrreduciblePaper A :=
  prop3_ac A hNorm (prop3_ba A hA)

/-- **Proposition 3 (b)→(c), `IsNormal` version**: `IsNormal A` implies strong
irreducibility (given normalization).

Convenience corollary rewriting `HasEventuallyFullKrausRank` as `IsNormal`. -/
theorem isNormal_implies_stronglyIrreducible [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsNormal A) :
    IsStronglyIrreduciblePaper A :=
  primitivePaper_implies_stronglyIrreducible A hNorm
    ((hasEventuallyFullKrausRank_iff_isNormal A).mpr hA)

/-! ## Full equivalences -/

/-- **Proposition 3 (a)↔(b)**: Paper-primitivity is equivalent to eventually full
Kraus rank (under normalization).

Composes **(b)→(a)** and **(a)→(c)→(b)**. -/
theorem primitivePaper_iff_hasEventuallyFullKrausRank [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    IsPrimitivePaper A ↔ HasEventuallyFullKrausRank A :=
  ⟨fun hP => prop3_cb A hNorm (prop3_ac A hNorm hP),
   fun hB => prop3_ba A hB⟩

/-- **Proposition 3 (a)↔(c)**: Paper-primitivity is equivalent to strong
irreducibility (under normalization).

Composes **(a)→(c)** and **(c)→(b)→(a)**. -/
theorem primitivePaper_iff_stronglyIrreducible [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    IsPrimitivePaper A ↔ IsStronglyIrreduciblePaper A :=
  ⟨fun hP => prop3_ac A hNorm hP,
   fun hC => prop3_ba A (prop3_cb A hNorm hC)⟩

/-- **Proposition 3 (b)↔(c)**: Eventually full Kraus rank is equivalent to strong
irreducibility (under normalization).

Composes **(b)→(a)→(c)** and **(c)→(b)**. -/
theorem hasEventuallyFullKrausRank_iff_stronglyIrreducible [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    HasEventuallyFullKrausRank A ↔ IsStronglyIrreduciblePaper A :=
  ⟨fun hB => primitivePaper_implies_stronglyIrreducible A hNorm hB,
   fun hC => prop3_cb A hNorm hC⟩

/-! ## Channel primitivity (intermediate result) -/

/-- **Proposition 3 (a) implies channel-level primitivity**: Paper-primitivity
implies that `E_A` has peripheral spectrum `{1}`.

This is the intermediate step of (a)→(c); strong irreducibility additionally
produces a PosDef fixed point. -/
theorem prop3_a_implies_channelPrimitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    IsChannelPrimitive A :=
  isChannelPrimitive_of_isPrimitivePaper A hNorm hPrim

/-! ## Index bound -/

/-- **q(E_A) ≤ i(A)**: the primitivity index is at most the full-Kraus-rank
index.

Re-exported from `PrimitiveEquiv.lean`. -/
theorem prop3_qIndex_le_iIndex (A : MPSTensor d D)
    (hA : HasEventuallyFullKrausRank A) :
    qIndex A ≤ iIndex A :=
  qIndex_le_iIndex A hA

end MPSTensor
