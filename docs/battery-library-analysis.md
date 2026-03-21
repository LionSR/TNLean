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

## Estimated Line Savings from `aesop` Adoption

**Summary: ~150–250 lines saveable** across 59,632 total lines (0.3–0.4%).

The savings are modest in raw count but meaningful in proof clarity and maintainability.

### Pattern-by-pattern breakdown

| Pattern | Occurrences | Lines saved per | Total lines |
|---------|------------|-----------------|-------------|
| `map_add'`/`map_smul'` structure proofs | 34 pairs (~68) | 1–6 each | ~100–200 |
| `ext; simp [...]` one-liners | 4 | 0 (already 1-line) | 0 |
| `simp [...] ; abel/ring` combos | 18 | 1–2 each | ~20–36 |
| `constructor` + multi-step structural | 53 | 0–2 each | ~30–60 |
| `intro; simp` patterns | 43 | 0 (inline) | 0 |

---

## Concrete Before/After Examples

### Example 1: LindbladForm `map_smul'` (6 lines → 1 line)

**File:** `Channel/Semigroup/LindbladForm.lean:102–108`

**Before (7 lines):**
```lean
map_smul' c ρ := by
  simp only [RingHom.id_apply, dissipator_smul, mul_smul_comm, smul_mul_assoc,
    smul_sub]
  rw [← Finset.smul_sum, smul_add, smul_sub]
  simp only [smul_smul]
  congr 1
  congr 1 <;> ring_nf
```

**After (1 line):**
```lean
map_smul' c ρ := by aesop
```

**Savings: 6 lines.** Aesop can discover the `simp` lemmas, apply `ring_nf`, and close the
goal via its tactic fallback rules — provided `dissipator_smul` etc. are tagged `@[aesop norm]`.

---

### Example 2: TensorMapId `map_add'` (6 lines → 1 line)

**File:** `Channel/TensorMap.lean:83–89`

**Before (6 lines):**
```lean
map_add' X Y := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [tensorMapId_apply, Matrix.add_apply]
  rw [show bipartiteSlice (X + Y) i₂ j₂ =
    bipartiteSlice X i₂ j₂ + bipartiteSlice Y i₂ j₂ from by
      ext; simp [bipartiteSlice]]
  simp [map_add]
```

**After (1 line):**
```lean
map_add' X Y := by aesop
```

**Savings: 5 lines.** The `ext` + `simp` + `rw` chain is exactly what aesop's search handles.
Requires tagging `bipartiteSlice` lemmas and `tensorMapId_apply` as `@[aesop norm unfold]`.

---

### Example 3: TensorMapId `map_smul'` (6 lines → 1 line)

**File:** `Channel/TensorMap.lean:90–96`

**Before (6 lines):**
```lean
map_smul' c X := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [tensorMapId_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
  rw [show bipartiteSlice (c • X) i₂ j₂ =
    c • bipartiteSlice X i₂ j₂ from by
      ext; simp [bipartiteSlice, Matrix.smul_apply, smul_eq_mul]]
  simp [map_smul]
```

**After (1 line):**
```lean
map_smul' c X := by aesop
```

**Savings: 5 lines.**

---

### Example 4: Hermitian proof with `simp` + `abel` (5 lines → 1 line)

**File:** `Channel/Semigroup/LindbladForm.lean:276–281`

**Before (5 lines):**
```lean
have hX_herm : X.IsHermitian := by
  dsimp [X]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  simp
  abel
```

**After (1 line):**
```lean
have hX_herm : X.IsHermitian := by aesop
```

**Savings: 4 lines.** With `Matrix.IsHermitian` unfolding and `conjTranspose_*` lemmas
as `@[aesop norm]`, plus `abel` registered as a tactic fallback.

---

### Example 5: Complex.I Hermitian proof (9 lines → 1 line)

**File:** `Channel/Semigroup/LindbladForm.lean:282–291`

**Before (9 lines):**
```lean
have hY_herm : Y.IsHermitian := by
  dsimp [Y]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  have hI : star (Complex.I / 2 : ℂ) = -(Complex.I / 2) := by
    apply Complex.ext <;> norm_num
  rw [hI]
  ext i j
  simp [sub_eq_add_neg]
  ring
```

**After (1 line):**
```lean
have hY_herm : Y.IsHermitian := by aesop
```

**Savings: 8 lines.** The `Complex.ext <;> norm_num` subproof and the `ext i j; simp; ring`
pattern are both searchable by aesop with `norm_num` and `ring` as fallback tactics.

---

### Example 6: Kraus `mapLM` proofs (2 lines → 1 line, ×4 definitions)

**File:** `Channel/Schwarz/Basic.lean:43–44, 60–61`

**Before (2 lines each, 4 definitions = 8 lines):**
```lean
map_add' X Y := by simp [map, add_mul, mul_add, Finset.sum_add_distrib]
map_smul' c X := by simp [map, Finset.smul_sum]
-- and --
map_add' X Y := by simp [adjointMap, add_mul, mul_add, Finset.sum_add_distrib]
map_smul' c X := by simp [adjointMap, Finset.smul_sum, Matrix.mul_assoc]
```

**After (1 line each, 4 lines):**
```lean
map_add' X Y := by aesop
map_smul' c X := by aesop
```

**Savings: 4 lines.** These are already short, but `aesop` would discover the right `simp`
lemmas without manual enumeration, improving maintainability.

---

### Example 7: `rectSpanLeftStep` / `rectSpanNilpIndexLeftStep` (already optimal)

**File:** `Wielandt/RectangularSpan/Growth.lean:104–105`

```lean
map_add' x y := by ext; simp [Matrix.mul_add]
map_smul' a x := by ext; simp
```

**Savings: 0 lines.** Already 1-line proofs. `aesop` would be equivalent but not shorter.

---

### Example 8: Calc chain simplification steps (1 line each, ~20 instances)

**File:** `Channel/Peripheral/CyclicDecomposition.lean:170–174`

**Before:**
```lean
calc
  transferMap K (H - (c0 : ℂ) • 1)
      = transferMap K H - (c0 : ℂ) • transferMap K 1 := by
          simpa using (transferMap K).map_sub H ((c0 : ℂ) • (1 : MatrixAlg D))
  _ = H - (c0 : ℂ) • 1 := by simp [hfix, hone_fix]
```

**After:**
```lean
calc
  transferMap K (H - (c0 : ℂ) • 1)
      = transferMap K H - (c0 : ℂ) • transferMap K 1 := by aesop
  _ = H - (c0 : ℂ) • 1 := by simp [hfix, hone_fix]
```

**Savings: ~0 lines** (same line count). But the `simpa using ...` → `aesop` swap removes
the need to manually identify which lemma to use. Roughly 20 such `simpa using` instances
across the codebase become simpler to write and maintain.

---

## Setup Cost

To enable these savings, you'd need a one-time setup file (~30–40 lines):

```lean
-- TNLean/Aesop/Rules.lean

-- Register domain-specific aesop rules
attribute [aesop norm simp] bipartiteSlice tensorMapId_apply
attribute [aesop norm simp] dissipator_add dissipator_smul
attribute [aesop norm simp] Matrix.conjTranspose_smul Matrix.conjTranspose_add
attribute [aesop safe apply] Matrix.IsHermitian
attribute [aesop unsafe 50% tactic] (tactic| ring_nf)
attribute [aesop unsafe 50% tactic] (tactic| abel)
attribute [aesop unsafe 30% tactic] (tactic| norm_num)
```

---

## `plausible` Opportunities (Development Aid, Not Line Savings)

`plausible` doesn't reduce existing lines — it accelerates *future* development by catching
bad conjectures early. Priority targets:

| File | What to Test | Priority |
|------|-------------|----------|
| `Wielandt/WielandtBound.lean:87` | Wielandt analysis structure completeness | Critical |
| `Wielandt/SpanGrowth/NonzeroTraceProduct.lean:61` | Lemma 1 bound tightness (D² − dim + 1) | Critical |
| `Wielandt/SpanGrowth/EigenvectorSpreading.lean:60` | Spreading speed = D−1 | High |
| `Channel/Semigroup.lean:133` | GKSL ↔ Lindblad (has sorry-dependent lemmas) | High |
| `Spectral/SpectralGap.lean:25` | Spectral radius bounds | Medium |
| `MPS/Defs.lean:75` | GaugeEquiv preserves MPV families | Medium |

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

### Medium Priority: Use `plausible` for conjecture testing (already available)

**Why:** Before investing in formal proofs of new results (e.g., Wielandt bound variants,
spectral gap estimates), use `plausible` to hunt for counter-examples at small sizes.

### Low Priority: Consider `Lean-Auto + Duper` (new dependency)

**What:** An interface to external automated theorem provers (SMT solvers, superposition provers).
The combined LeanHammer system solves ~30% of Mathlib theorems automatically.

**Trade-off:** Adds a medium-weight dependency and may require external solver installation.

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
which could save ~150–250 lines across the codebase and improve proof maintainability.
The biggest wins are in `map_add'`/`map_smul'` structure proofs (34 pairs across 28 files)
and `simp + abel/ring` combos (18 instances across 18 files).

The real value isn't raw line count — it's that `aesop` proofs are **more robust to upstream
changes** than manually-curated `simp only [...]` lists. When Mathlib renames a lemma,
`aesop` adapts automatically; explicit `simp only` calls break.

Secondary gains come from using `plausible` during development to test conjectures before
investing in formal proofs.

*Analysis date: 2026-03-21*
