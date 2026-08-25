/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.QPF.Assembly
import TNLean.Wielandt.Primitivity.Definitions
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank
import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.Inequality.Bounds

/-!
# Wolf Chapter 6 index: tensor-network side

This module is the tensor-network half of the navigational index for

> M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012), Chapter 6.

It records the sections of Wolf Chapter 6 whose formalization lives in the
tensor-network layer (`TNLean.Wielandt.*`, `TNLean.QPF.*`, `TNLean.MPS.*`,
`TNLean.Spectral.*`): the Kraus-span primitivity characterizations, the
quantum Wielandt inequality, the unique-fixed-point theorem for tensors with
eventually full Kraus rank, and the assembled quantum Perron–Frobenius
theorem.

The channel-level sections of the index are in
`TNLean.Channel.WolfChapter6Index`; that module contains the entries whose
formalization lives in the quantum-channel layer and does not directly import
the tensor-network layer. A residual transitive dependence remains through the
Perron--Frobenius modules while the decoupling of the channel layer is in
progress.

No new proofs are introduced here; this is a documentation-only index module.

---

## Section 6.2 Irreducible maps and Perron–Frobenius theory

### Wolf Theorem 6.3 (Spectral radius of irreducible maps) — TRANSFER-MAP SPECIALIZATIONS

The channel-level entries for Theorem 6.3 are in
`TNLean.Channel.WolfChapter6Index`.  The transfer-map specializations of the
fixed-point consequences of items 2–3 (strict positivity and PSD uniqueness):

* `posSemidef_fixedPoint_isPosDef` — `TNLean.QPF.PosDef`
* `posSemidef_fixedPoint_isPosDef_of_irreducible`
* `posSemidef_fixedPoint_unique` — `TNLean.QPF.Uniqueness`
* `posSemidef_fixedPoint_unique_of_irreducible`

---

## Section 6.3 Primitive maps

### Wolf Theorem 6.7 (Primitive maps, 4 equivalent conditions) — TRANSFER-OPERATOR GAP SIDE

Item 4 (trivial peripheral spectrum, PD eigenvector) is channel-level; see
`TNLean.Channel.WolfChapter6Index`.  The other items are PARTIALLY covered via
the transfer-operator gap formalization in `TNLean.Spectral.*`.

### Wolf Theorem 6.8 (CP primitive maps, Kraus span characterizations)

* `IsPrimitivePaper` — `TNLean.Wielandt.Primitivity.Definitions`
  (item 3: `Kₘ = M_d(ℂ)` for `m ≥ q`)
* Pairwise equivalences from Proposition 3:
  * `primitivePaper_iff_hasEventuallyFullKrausRank` / `primitivePaper_iff_stronglyIrreducible`
    (in `TNLean.Wielandt.Primitivity.Equivalence`)
  * `hasEventuallyFullKrausRank_iff_isNormal`
    (in `TNLean.Wielandt.Primitivity.Definitions`)
* Formulated Wolf-facing formulations:
  * `wolf_theorem_6_8_kraus_span`
  * `wolf_theorem_6_8_conjunction`
  (in `TNLean.Wielandt.Primitivity.Equivalence`)

### Wolf Theorem 6.9 (Quantum Wielandt inequality)

Current formal statements live in `TNLean.Wielandt.Inequality.Bounds`:
* `qIndex_le_iIndex_of_isPrimitivePaper`
* `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit` /
  `iIndex_le_of_isPrimitivePaper_of_isUnit`
* `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector` /
  `iIndex_le_sq_of_noninvertible_eigenvector`

The positive-definite primitive-to-normal theorem is
`MPSTensor.isNormal_of_isPrimitiveMPS_with_posDef` in
`TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank`; it is not the
Wielandt index bound itself.

---

## Section 6.4 Fixed points

### Wolf Theorem 6.15 (Unique fixed point from full Kraus-word span) — FORMALIZED

* `MPSTensor.wolf_theorem_6_15` (`TNLean.Wielandt.Primitivity.Equivalence`) —
  for a normalized MPS tensor `A` (`∑ᵢ Aᵢ† Aᵢ = 1`) with eventually full Kraus
  rank (homogeneous words of some fixed length in the Kraus operators span the
  full matrix algebra), there exists a unique positive definite density matrix
  `ρ` such that every fixed point of the transfer map `E_A` is a scalar
  multiple of `ρ`.

The proof routes through Proposition 3:
`MPSTensor.isStronglyIrreduciblePaper_of_hasEventuallyFullKrausRank` turns the
span hypothesis into strong irreducibility, then
`MPSTensor.isPrimitiveMPS_of_isStronglyIrreduciblePaper` supplies a
positive-definite fixed point together with peripheral primitivity and
irreducibility of `E_A`; the complementary transfer-map gap around that fixed
point (`Kraus.HasComplementaryFixedPointGap.fixedPoint_unique`) then forces every fixed
point to be a scalar multiple of it. This differs from the source's own `T^n`
/ Corollary 6.5 argument but reuses only already-formalized Wolf Chapter 6
machinery (Proposition 3).

---

## The quantum Perron–Frobenius theorem

* `quantum_perron_frobenius` — `TNLean.QPF.Assembly`
  Combines existence + positive definiteness + uniqueness (Wolf Theorem 6.3).

* `injective_transfer_unique_fixed_point'` — same, without `0 < D` hypothesis.
-/
