# Battery & Non-Mathlib Library Analysis for TNLean

## Current Dependency Landscape

TNLean already **transitively depends** on batteries, aesop, Qq, ProofWidgets4, and plausible
through Mathlib v4.28.0. Current usage:

| Library | Usage | Notes |
|---------|-------|-------|
| `omega` (Batteries) | 171 uses / 34 files | Heavily used for index arithmetic |
| `simp` (+ Batteries lemmas) | 2,696 uses / 146 files | Primary workhorse tactic |
| `aesop` | **0 uses** | Available but unused |
| `plausible`/`slim_check` | **0 uses** | Available but unused |
| `decide` | **0 uses** | Not relevant for continuous math |
| Direct Batteries imports | **0** | All access is via Mathlib |

The project is sorry-free (all 11 grep hits for "sorry" are in comments like "sorry-free").

---

## Recommendation Summary

### High Priority: Use `aesop` (already available, zero cost)

**Why:** Aesop is a rule-based best-first proof search tactic (like Isabelle's `auto`).
The project's 2,696 `simp` calls and extensive algebraic reasoning suggest many goals
that `aesop` could dispatch more cleanly, especially:

- **Channel theory proofs** with repetitive algebraic structure
- **Gauge equivalence** lemmas involving conjugation patterns
- **Transfer operator** properties that compose known facts

**How to adopt:**
1. Tag frequently-used lemmas with `@[aesop]` (as `norm`, `safe`, or `unsafe` rules)
2. Build domain-specific rule sets for MPS/channel reasoning
3. Use `aesop?` to generate deterministic proof scripts (avoids runtime search cost)

Mathlib already uses Aesop extensively for `measurability`, `continuity`, and category theory.

### Medium Priority: Use `plausible` for conjecture testing (already available)

**Why:** Before investing in formal proofs of new results (e.g., Wielandt bound variants,
spectral gap estimates), use `plausible` to hunt for counter-examples at small sizes.

**Best candidates in TNLean:**
- Testing conjectures about `wordSpan` growth rates
- Checking gauge equivalence properties on small matrix dimensions
- Validating spectral gap bounds before formalizing

### Low Priority: Consider `Lean-Auto + Duper` (new dependency)

**What:** An interface to external automated theorem provers (SMT solvers, superposition provers).
The combined LeanHammer system solves ~30% of Mathlib theorems automatically.

**Trade-off:** Adds a medium-weight dependency and may require external solver installation.
Worth investigating if you have many "should be obvious" algebraic lemmas that resist `simp`/`aesop`.

### Not Recommended for TNLean

| Library | Why Not |
|---------|---------|
| **LeanSAT / `bv_decide`** | Project is continuous math (ℂ-matrices, operator algebras), not Boolean/bitvector |
| **LeanCamCombi** | Graph theory / extremal combinatorics — different mathematical domain |
| **ProofWidgets** | Nice for visualization/teaching but doesn't help prove theorems |
| **Qq** | Only useful if writing custom tactics — TNLean is proof-focused |
| **Standalone Batteries** | Already getting everything via Mathlib; no benefit to importing directly |

---

## Detailed Library Catalog

### 1. Batteries (formerly Std4)
- **Provides:** `RBMap`, `HashMap`, `List`/`Array`/`Nat`/`Int` lemmas, `omega` tactic
- **Weight:** Lightweight (sits between Lean core and Mathlib)
- **TNLean status:** Already used transitively; `omega` is heavily used
- **Additional value:** More `Finset`/`Multiset` lemmas for Wielandt combinatorial arguments

### 2. Aesop
- **Provides:** Extensible best-first proof search with `@[aesop]` rule registration
- **Weight:** Lightweight (depends on Batteries, not Mathlib)
- **TNLean status:** Available but **completely unused** — biggest missed opportunity
- **Key feature:** `aesop?` generates deterministic scripts for CI performance

### 3. LeanSAT / bv_decide
- **Provides:** Verified SAT solving, bitvector reasoning
- **Weight:** Now in Lean core (zero extra deps)
- **TNLean status:** Not relevant (continuous, not discrete math)

### 4. Plausible / SlimCheck
- **Provides:** Randomized counter-example search (like QuickCheck)
- **Weight:** Very lightweight standalone; SlimCheck lives in Mathlib
- **TNLean status:** Available but unused; useful for conjecture exploration

### 5. ProofWidgets4
- **Provides:** Interactive visualizations in the Lean infoview (Penrose diagrams, etc.)
- **Weight:** Moderate (has JS build component)
- **TNLean status:** Available via Mathlib; presentation/debugging tool only

### 6. Qq (Quote4)
- **Provides:** Type-safe expression quotation for metaprogramming
- **Weight:** Very lightweight
- **TNLean status:** Only relevant if writing custom tactics

### 7. Lean-Auto + Duper
- **Provides:** Interface to external ATPs (Z3, CVC5, Zipperposition) + native HOL superposition
- **Weight:** Medium (Duper is substantial; external solvers need installation)
- **TNLean status:** Not currently a dependency; worth evaluating for hard algebraic goals

---

## Conclusion

**No new dependencies are needed.** The primary actionable improvement is adopting `aesop`,
which is already available and could meaningfully reduce proof verbosity across the codebase.
Secondary gains come from using `plausible` during development to test conjectures before
investing in formal proofs.

The project's mathematical domain (finite-dimensional C*-algebras, quantum channels,
matrix product states) is squarely Mathlib territory — no lightweight library replaces
what Mathlib provides. The gap is in **underusing available automation**, not in missing libraries.

*Analysis date: 2026-03-21*
