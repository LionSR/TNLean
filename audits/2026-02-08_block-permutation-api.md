---
title: "Block permutation API audit (Mathlib v4.27.0)"
date: 2026-02-08
author: AI research assistant (search agent)
purpose: >
  Audit of Mathlib's semisimple block decomposition and block permutation
  API.  Evaluates TwoSidedIdeal, simple ring infrastructure, and
  Equiv.Perm tooling needed to prove that automorphisms of ∏ M_{D_k}(ℂ)
  decompose as block permutations + per-block inner automorphisms.
---

# Audit: semisimple block decomposition / block permutation API (Mathlib v4.27.0)

_Date_: 2026-02-08  
_Project_: **MPSLean** (Fundamental Theorem of Matrix Product States, multi-block version)

## Goal

We need to formalize the following ring/algebra-theoretic step used in the multi-block Fundamental Theorem:

> Let
> \[
>   A := \bigoplus_k M_{D_k}(\mathbb C).
> \]
> (For **finite** index sets, this is (canonically) a finite product ring.)
> Show that an **algebra automorphism** (or ring equivalence)
> \[
>   T : A \to A
> \]
> must **permute the simple blocks**.
>
> Equivalently (Lean-friendly): for a finite type `ι` and simple rings `R i`, any
> `T : (Π i, R i) ≃+* (Π i, R i)` must permute the factors.

This audit checks what Mathlib v4.27.0 provides, and what glue lemmas we still need.

---

## 1. Central idempotents / orthogonal idempotents

### What exists

- `Mathlib/RingTheory/Idempotents.lean`
  - `OrthogonalIdempotents` / `CompleteOrthogonalIdempotents`.
  - `CompleteOrthogonalIdempotents.single`:
    canonical complete orthogonal family in a product ring,
    \(e_i := \texttt{Pi.single i 1}\).
  - `OrthogonalIdempotents.map` / `CompleteOrthogonalIdempotents.map`:
    push families through ring homs.
  - “corner” construction:
    - `IsIdempotentElem.Corner`
    - `CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral`:
      a complete orthogonal family of **central** idempotents yields a product decomposition into corners.

- `Mathlib/Algebra/Group/Center.lean`
  - `IsMulCentral` (multiplicatively central elements).
  - `Set.center_pi` identifies `Set.center (Π i, A i)` coordinatewise.

- `Mathlib/GroupTheory/Submonoid/Center.lean`
  - `MulEquivClass.apply_mem_center_iff`:
    multiplicative equivalences preserve membership in `Set.center`.

### What does *not* exist (as far as found)

- No dedicated `CentralIdempotent` structure.
- No “primitive central idempotent” API.
- No packaged theorem that “automorphisms of a finite product of simple rings permute the central primitive idempotents”.

---

## 2. Ring homomorphisms involving `Pi`

### Core API

- `Mathlib/Algebra/Ring/Pi.lean`
  - `Pi.evalRingHom` : evaluation `(Π i, R i) →+* R i`.
  - `Pi.ringHom` : build `γ →+* (Π i, R i)` from a family `γ →+* R i`.

- `Mathlib/Algebra/Ring/Equiv.lean`
  - `RingEquiv.piCongrRight`, `RingEquiv.piCongrLeft'`, `RingEquiv.piCongrLeft`.

- `Mathlib/Algebra/Algebra/Pi.lean`
  - `AlgEquiv.piCongrRight`, `AlgEquiv.piCongrLeft'`, `AlgEquiv.piCongrLeft`.

### Notes

- Proving “block permutation” is substantially easier if we upgrade the map to a `RingEquiv` / `AlgEquiv`.
- If you start with a bijective hom (e.g. `RingHom` or `AlgHom`), you can typically use `RingEquiv.ofBijective` / `AlgEquiv.ofBijective`.

---

## 3. `IsSemisimpleRing` and Wedderburn–Artin

### What exists

- `Mathlib/RingTheory/SimpleModule/Basic.lean`
  - `abbrev IsSemisimpleRing := IsSemisimpleModule R R`.
  - Explicit TODO: **"Artin-Wedderburn Theory (uniqueness)"**.

- `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`
  - existence/decomposition results, e.g.
    - `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`
    - `isSemisimpleRing_iff_pi_matrix_divisionRing`

- `Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean`
  - over an algebraically closed field:
    - `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`
    - `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`

### What is missing for our purpose

Mathlib does **not** appear to provide a ready-made uniqueness theorem saying that an automorphism of a semisimple ring must permute its simple factors.

However, for a *known explicit product decomposition* `A = Π i, R i`, we can prove the permutation property directly (see §6).

---

## 4. Two-sided ideals of product rings

This is the most useful part of the library for proving “blocks are permuted”.

### Ideals in a finite product

- `Mathlib/RingTheory/Ideal/Basic.lean`
  - `Ideal.pi` : from `I : Π i, Ideal (R i)` build an ideal of `Π i, R i`.
  - instance: if each `I i` is two-sided, then `(Ideal.pi I).IsTwoSided`.

- `Mathlib/RingTheory/Ideal/Maps.lean`
  - `Ideal.piOrderIso [Finite ι] : Ideal (Π i, R i) ≃o Π i, Ideal (R i)`.
    This classifies **all** ideals of a **finite** product ring.
  - important helper lemma: `Ideal.map_evalRingHom_pi`.
  - instance: if `f : R →+* S` is surjective and `I` is two-sided, then `I.map f` is two-sided:
    ```lean
    instance (priority := low) (f : R →+* S) [RingHomSurjective f]
        (I : Ideal R) [I.IsTwoSided] : (I.map f).IsTwoSided
    ```

### TwoSidedIdeal ↔ two-sided `Ideal`

- `Mathlib/RingTheory/TwoSidedIdeal/Operations.lean`
  - `TwoSidedIdeal.orderIsoIsTwoSided : TwoSidedIdeal R ≃o {I : Ideal R // I.IsTwoSided}`.
  - `RingEquiv.mapTwoSidedIdeal : TwoSidedIdeal R ≃o TwoSidedIdeal S`.

### Consequence

Using `Ideal.piOrderIso`, one can show:

- Any two-sided ideal of `Π i, R i` is determined by the family of projected ideals
  \(I_i := I.map(\mathrm{eval}_i)\).
- If each factor `R i` is simple, each `I_i` is `⊥` or `⊤`, so two-sided ideals correspond to subsets of indices.

This makes it possible to extract a permutation from an automorphism by observing it permutes **atoms**.

---

## 5. Simplicity of matrix rings

- `Mathlib/RingTheory/SimpleRing/Matrix.lean`
  - `IsSimpleRing.matrix` : if `A` is simple then `Matrix ι ι A` is simple (for finite nonempty `ι`).

So in particular, `IsSimpleRing (Matrix (Fin n) (Fin n) ℂ)` is available.

---

## 6. Can we prove block permutation in current Mathlib?

### Verdict

**Yes**, provided we work with a **ring/algebra equivalence** (or at least a bijective hom upgraded to an equivalence).

Mathlib does not have a one-line theorem, but it contains enough infrastructure to prove it with a moderate amount of glue.

### Strategy A (recommended): classify two-sided ideals, then use atoms

Let `A := Π i, R i` with `[Finite ι]` and each `R i` a simple ring.

1. Show two-sided ideals of `A` correspond to subsets of `ι`:
   - Start with `I : TwoSidedIdeal A`.
   - Convert to `I.asIdeal : Ideal A` (and keep track of `IsTwoSided`).
   - Use `Ideal.piOrderIso` to rewrite `I.asIdeal` as an `Ideal.pi` of the family
     `I.asIdeal.map (Pi.evalRingHom _ i)`.
   - Each component ideal is two-sided (surjective `evalRingHom` + `Ideal.map` preserves `IsTwoSided`).
   - Simplicity of each `R i` forces each component ideal to be `⊥` or `⊤`.

2. Identify “minimal nonzero two-sided ideals” with **atoms** in the lattice `TwoSidedIdeal A`.
   - Use `IsAtom` from `Mathlib/Order/Atoms.lean`.
   - Atoms correspond to singleton subsets (i.e. “the i-th block ideal”).

3. A ring equivalence `T : A ≃+* A` induces an order isomorphism on two-sided ideals:
   - `T.mapTwoSidedIdeal : TwoSidedIdeal A ≃o TwoSidedIdeal A`.
   - `OrderIso.isAtom_iff` gives that atoms map to atoms.

4. Therefore, `T` permutes singleton block ideals, producing a permutation `σ : ι ≃ ι`.

5. Restrict `T` to obtain componentwise maps
   \(R_i \to R_{σ(i)}\)
   (include via `Pi.single`, apply `T`, project via `Pi.evalRingHom`).
   Use simplicity / finite-dimensionality to upgrade to equivalences.

6. Apply Skolem–Noether on each matrix block.

**Work estimate:** ~150–400 LoC of “glue lemmas” in a local helper file (atoms, projections, restriction maps).

### Strategy B: central idempotents

An alternative is to track the images of the canonical central idempotents `Pi.single i 1` via
`CompleteOrthogonalIdempotents.single` and show they remain central/orthogonal/complete, then prove
“in a simple ring, a central idempotent is 0 or 1” and deduce each image has singleton support.

This works, but tends to require more bespoke lemmas about centrality and corners.

---

## 7. GitHub PR / issue scan (Artin–Wedderburn / semisimple)

I queried the GitHub search API briefly before hitting rate limits; relevant merged PRs included:

- `leanprover-community/mathlib4#23583` (Wedderburn–Artin theorem development)
- `leanprover-community/mathlib4#24119` (preliminaries for Wedderburn–Artin)
- `leanprover-community/mathlib4#24192` (semisimple Wedderburn–Artin existence)
- `leanprover-community/mathlib4#31672` (follow-up/cleanup on semisimple rings)

In Mathlib itself, `RingTheory/SimpleModule/Basic.lean` still lists “Artin–Wedderburn theory (uniqueness)” as TODO.

---

## Bottom line

- **We can prove now** (in Mathlib v4.27.0) that an *automorphism*
  `T : (Π i, Matrix (Fin (D i)) (Fin (D i)) ℂ) ≃ₐ[ℂ] (Π i, Matrix (Fin (D i)) (Fin (D i)) ℂ)`
  permutes the factors.
- The most Lean-friendly route is via:
  `Ideal.piOrderIso` + two-sidedness + simplicity ⇒ two-sided ideals are “subsets” ⇒ atoms are singletons ⇒ automorphisms permute atoms.
- What’s missing is only a packaged theorem; not core infrastructure.
