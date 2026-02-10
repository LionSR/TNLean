---
title: "Community Lean 4 resources for the spectral gap"
date: 2026-02-09
author: AI research assistant (search agent)
purpose: >
  Survey of reusable Lean 4 libraries (HopfieldNet, Lean-QuantumInfo,
  Mathlib, Isabelle AFP) for closing the quantum Perron–Frobenius gap.
  Assesses version compatibility, importability, and gap coverage for
  each resource.  Includes the HopfieldNet addendum after the repo was
  found to use identical Lean+Mathlib versions.
---

# Community Lean 4 Resources for MPSLean's Spectral Gap
## Investigation of Available Formalizations for Quantum Perron-Frobenius Theory

**Date:** 2026-02-09  
**Scope:** Lean 4 community libraries, Mathlib v4.27.0, external proof assistant projects  
**Purpose:** Assess what existing community resources can help close MPSLean's remaining gap — the spectral theory of completely positive maps (quantum Perron-Frobenius) needed for block separation in the multi-block (r≥2) Fundamental Theorem of Matrix Product States.

---

## 1. Executive Summary

MPSLean's sole remaining gap is the **block separation lemma**: proving that a weighted-sum equality across blocks implies per-block equality, which requires spectral analysis of the transfer operator $E_A(X) = \sum_i A_i X A_i^\dagger$ as a completely positive map. We investigated four categories of community resources:

| Resource | Status | Gap Coverage | Importable? |
|----------|--------|-------------|-------------|
| **Cipollina et al.** — Classical PF in Lean 4 | Code not yet public | Classical PF only (stochastic matrices) | Not yet |
| **Lean-QuantumInfo** — Quantum information library | Active, v4.24.0 | CP maps, Choi matrix, no spectral theory | With effort |
| **Mathlib** — CP maps & irreducibility defs | In our dependencies | Definitions only, no PF eigenvalue theorem | Already imported |
| **Isabelle AFP** — Full classical PF | Complete formalization | Different proof assistant entirely | Not importable |

**Bottom line:** No existing Lean 4 resource provides quantum Perron-Frobenius theory. The closest resources are (1) a classical PF formalization that is not yet publicly available, and (2) a quantum information library with CP map definitions but no spectral analysis. Closing the gap will require original formalization work, though these resources can reduce the effort by 30–40%.

---

## 2. Detailed Resource Analysis

### 2.1 Cipollina, Karatarakis & Wiedijk — Classical Perron-Frobenius (arXiv:2512.07766)

**Paper:** "Formalized Hopfield Networks and Boltzmann Machines in Lean 4"  
**Authors:** Michele Cipollina, Ioannis Karatarakis, Freek Wiedijk (Radboud University)  
**Date:** December 2025  
**Size:** 15,342 lines of Lean 4 code

#### What they formalize

This is the most substantial formalization of Perron-Frobenius theory in Lean 4 to date. The PF results are a key ingredient in their proof that Boltzmann machines converge to thermal equilibrium. Specifically, they prove:

1. **Perron root existence:** For irreducible stochastic matrices, the spectral radius equals 1 and is an eigenvalue.
2. **Unique positive eigenvector:** The Perron eigenvector is positive and unique up to scaling, established via the Collatz-Wielandt characterization.
3. **Spectral dominance:** For aperiodic (primitive) irreducible matrices, the Perron root is the unique eigenvalue of maximum modulus.
4. **Ergodicity:** Powers of an irreducible aperiodic stochastic matrix converge to the rank-1 projector onto the stationary distribution.

These results are proved for **stochastic matrices** (nonneg entries, rows summing to 1) — not for general nonnegative matrices. This is sufficient for their Markov chain application but narrower than the full PF theorem.

#### Availability and integration status

- **GitHub repository:** The paper states the link will be provided after review; it was anonymized at submission. As of February 2026, **no public standalone repository** has been found.
- **Mathlib contributions:** The paper notes that "mathematical infrastructure has either been integrated into mathlib or is currently under review." In particular, the `Matrix.IsIrreducible` and `Matrix.IsPrimitive` definitions currently in Mathlib were contributed by Karatarakis as part of this project.
- **PhysLean:** The neural network formalization was submitted as a PR to HEPLean/PhysLean. The PF infrastructure may be included in that PR, but the specific PR has not been located.
- **Mathlib issue #6091:** The Perron-Frobenius theorem is listed among the "100 theorems" challenge and remains unproved in Mathlib proper.

#### Relevance to MPSLean

**Partial.** The classical PF theorem for stochastic matrices could serve as a foundation, but our transfer operator is a completely positive map on the space of matrices (not a stochastic matrix on a vector space). Bridging the gap would require:

1. **Choi-Jamiołkowski isomorphism:** Show that the transfer operator's spectral properties can be analyzed through its Choi matrix (a positive semidefinite matrix).
2. **Normalization:** Relate the trace-preserving property of the transfer operator to the stochastic property of a suitable matrix.
3. **Extension to general nonneg matrices:** The current formalization covers only stochastic matrices; we need the result for general nonnegative matrices (or at least doubly stochastic ones after suitable normalization).

**Estimated effort to adapt:** 2–3 months after the code becomes public, assuming the Choi isomorphism can be established as a bridge.

---

### 2.2 Lean-QuantumInfo (Timeroot/Lean-QuantumInfo)

**Repository:** https://github.com/Timeroot/Lean-QuantumInfo  
**Maintainer:** Alex Meiburg  
**License:** MIT  
**Stats:** 101 stars, 24 forks, 343 commits, 8 contributors  
**Size:** 1,059 theorems, 248 definitions, ~13,992 lines  
**Lean version:** v4.24.0 (from `lean-toolchain`)  
**Build status on Reservoir:** Last verified on v4.17.0-rc1 (April 2025); active development continues

#### What they formalize

This is the most comprehensive quantum information theory library in Lean 4. Its primary goal is a formalization of the Generalized Quantum Stein's Lemma (described as "quite close" to the first milestone as of October 2025). The library includes:

**Directly relevant to MPSLean:**
- **`CPTPMap dIn dOut`** — Completely positive trace-preserving maps as a structure over `Matrix (Fin dIn) (Fin dIn) ℂ →ₗ[ℂ] Matrix (Fin dOut) (Fin dOut) ℂ`, with bundled proofs of complete positivity and trace preservation.
- **`IsCompletelyPositive`** — Definition of complete positivity via Kronecker products with the identity: a map is CP if for all $n$, $(\phi \otimes \mathrm{id}_n)$ preserves positive semidefiniteness.
- **`MState d`** — Mixed quantum states (positive semidefinite matrices with trace 1).
- **`choi_MState_iff_CPTP`** — The Choi-Jamiołkowski isomorphism: a linear map is CPTP if and only if its (normalized) Choi matrix is a valid quantum state. This is a key structural result.
- **`CPTP_of_choi_PSD_Tr`** — Constructing a CPTP map from a PSD Choi matrix with the correct trace.
- **Channel composition, tensor products of channels and states.**

**Other content (less directly relevant):**
- POVM measurements
- Fidelity and trace distance
- Von Neumann entropy
- Quantum error correction basics
- Tensor product infrastructure for states and channels

#### What they don't have

- **No spectral analysis of CP maps** — no eigenvalues, spectral radius, or convergence results for quantum channels.
- **No quantum Perron-Frobenius theorem** — no fixed-point characterization for irreducible CP maps.
- **No transfer operator / transfer matrix** concept.
- **No Kraus representation theorem** (maps are defined structurally, not decomposed into Kraus operators).
- **No Stinespring dilation.**

#### Importability assessment

| Factor | Assessment |
|--------|-----------|
| **Version gap** | v4.24.0 → v4.27.0 needed. Lean 4 breaking changes between minor versions are common; expect 1–2 days of porting work. |
| **Build system** | Uses `lakefile.lean` (we use `lakefile.toml`). Minor compatibility issue, easily resolved. |
| **Mathlib dependency** | Both depend on Mathlib, reducing conflict risk. |
| **Matrix types** | Uses `Matrix (Fin d) (Fin d) ℂ` — compatible with MPSLean's concrete matrix types. |
| **License** | MIT — fully compatible with any use. |

**What we could import:**
- The `CPTPMap` / `IsCompletelyPositive` infrastructure could provide a cleaner foundation for our transfer operator.
- The Choi-Jamiołkowski isomorphism (`choi_MState_iff_CPTP`) is the key bridge between quantum channel spectral theory and classical matrix spectral theory.
- State definitions (`MState`) and channel composition could support future extensions.

**Estimated effort to import and adapt:** 1–2 weeks for selective import of Choi-related definitions and theorems. Would still require building all spectral theory on top.

---

### 2.3 Mathlib v4.27.0 — Current State

Mathlib is already a dependency of MPSLean. Here is the current state of relevant components:

#### Completely positive maps (`Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap`)

- **`CompletelyPositiveMap A₁ A₂`** — Structure extending `A₁ →ₗ[ℂ] A₂` with a proof of complete positivity.
- **`CompletelyPositiveMapClass`** — Morphism class for CP maps.
- **`A₁ →CP A₂`** notation.
- **`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`** — Star algebra homomorphisms are automatically CP.
- **`CompletelyPositiveMap.map_cstarMatrix_nonneg`** — CP maps preserve positivity of matrix blocks.

**Limitations:** This is an abstract C*-algebraic definition. There is no Choi matrix, no Kraus representation, no Stinespring dilation, and no connection to concrete `Matrix` types. The abstraction level is too high for our concrete spectral analysis needs.

#### Matrix irreducibility (`Mathlib.LinearAlgebra.Matrix.Irreducible`)

- **`Matrix.IsIrreducible`** — A matrix is irreducible iff the associated directed graph is strongly connected.
- **`Matrix.IsPrimitive`** — A matrix is primitive iff it is irreducible and aperiodic.

**Limitations:** These are *definitions only* — no eigenvalue theorems, no spectral radius characterization, no Perron eigenvector. The Perron-Frobenius theorem itself (Mathlib issue #6091) remains unproved in Mathlib.

#### Spectral theory infrastructure

Mathlib has mature general spectral theory:
- `spectrum`, `eigenvalues`, `IsEigenvalue`, `HasEigenvalue` for linear operators
- `spectralRadius` and the Gelfand formula for Banach algebras
- `Matrix.charpoly` — characteristic polynomials for matrices
- `Matrix.IsHermitian.eigenvalues` — eigenvalues of Hermitian matrices (real, ordered)
- `EigenvalueDecomposition` — for normal operators on finite-dimensional spaces

**Gap:** No connection between irreducibility/primitivity and eigenvalue structure. The "Perron-Frobenius bridge" — irreducible + nonneg ⟹ spectral radius is a simple eigenvalue with positive eigenvector — does not exist.

#### Positive semidefinite matrices

- `Matrix.PosSemidef` — well-developed, with Cholesky-like properties
- `Matrix.PosDef` — strict positivity
- `innerProductSpace` on matrices via Hilbert-Schmidt inner product

These are directly used by MPSLean already (the transfer operator `transferMap` is proved to preserve `PosSemidef` in `Transfer.lean`).

---

### 2.4 Other Resources Surveyed

#### PhysLean (HEPLean/PhysLean)

A Lean 4 physics library built on Mathlib, focused on high-energy physics (Standard Model, gauge fields, Feynman diagrams). The Cipollina et al. neural network formalization was submitted as a PR here. However:
- The PF-related code has not been identified in merged PRs.
- The library's focus is HEP, not quantum information or condensed matter.
- No directly useful infrastructure for our problem beyond what Mathlib already provides.

#### Isabelle AFP — Perron-Frobenius (Thiemann et al., 2016–2017)

The Archive of Formal Proofs contains:
- **Perron-Frobenius Theorem** (Thiemann, 2017): Full PF for irreducible nonneg matrices, including spectral radius = largest eigenvalue, positive eigenvector, spectral gap.
- **Jordan Normal Form** (Thiemann & Yamada, 2016): Full Jordan decomposition, needed for convergence results.

This is the most complete PF formalization in any proof assistant. However, it is in Isabelle/HOL and **cannot be imported into Lean 4**. It serves as a reference for proof strategy but not as reusable code.

#### CoqQ / MathComp-Analysis

The Coq ecosystem has some quantum information formalization (CoqQ by Li & Ying), but:
- No quantum PF theorem.
- No clear Lean 4 port pathway.
- Different type theory foundations make translation non-trivial.

#### Other Lean 4 projects

A systematic search of GitHub, Lean Reservoir, and Lean Zulip found no other Lean 4 projects with relevant spectral theory for CP maps or Perron-Frobenius results.

---

## 3. Gap Analysis: What's Missing Across All Resources

No existing Lean 4 formalization provides any of the following, all of which are needed for the quantum Perron-Frobenius approach to block separation:

| Component | Best Available | Status |
|-----------|---------------|--------|
| Classical PF eigenvalue theorem | Cipollina et al. (not public) | Formalized but unavailable |
| Classical PF for general nonneg matrices | Isabelle AFP (wrong language) | Not in Lean 4 |
| Choi-Jamiołkowski isomorphism | Lean-QuantumInfo | Formalized in Lean 4 ✓ |
| Kraus representation theorem | None | Not formalized in Lean 4 |
| Stinespring dilation | None | Not formalized in Lean 4 |
| Quantum PF (fixed point of irred. CP map) | None | Not formalized in any prover |
| Spectral gap for primitive CP maps | None | Not formalized in any prover |
| Transfer operator eigenvalue analysis | None | Not formalized |

The **quantum Perron-Frobenius theorem** — that an irreducible completely positive trace-preserving map has a unique full-rank fixed point, and the spectral radius of the map restricted to the traceless subspace is strictly less than 1 — has never been formally verified in any proof assistant.

---

## 4. Practical Importability Assessment

### 4.1 Lean-QuantumInfo: Most Immediately Useful

**What to import:** The Choi-Jamiołkowski definitions and the `CPTPMap` structure.

**How:**
1. Add as a Lake dependency (updating their `lean-toolchain` from v4.24.0 to v4.27.0).
2. Selectively import `QuantumInfo.Finite.CPTPMap` and related files.
3. Build a bridge between their concrete `CPTPMap` and our `transferMap`.

**Risk:** Version gap may cause build issues. Their library may have transitive dependencies that conflict.

**Alternative:** Cherry-pick the key definitions and theorems (MIT license allows this) into MPSLean directly, avoiding dependency management issues. This is the recommended approach — copy and adapt ~200 lines rather than adding a full library dependency.

### 4.2 Cipollina PF: Potentially Useful When Available

**Monitoring strategy:**
1. Watch Mathlib PRs for PF-related submissions (search for "Perron", "Frobenius", "Collatz", "Wielandt").
2. Watch PhysLean PRs for the Cipollina neural network submission.
3. Check arXiv:2512.07766 for updated versions with repository links.

**When available:** The classical PF infrastructure could be imported and extended. The key extension needed is from stochastic matrices to the Choi matrix of a CP map (which is PSD and has a specific trace constraint, making it analogous to a stochastic matrix after normalization).

### 4.3 Mathlib: Already Imported, Incremental Additions Expected

Mathlib contributions relevant to us may appear over the next 6–12 months:
- PF-related PRs from the Cipollina project
- Additional CP map infrastructure (Stinespring, Kraus)
- General matrix analysis results

These are unlikely to arrive fast enough to be useful for near-term closure of our gap.

---

## 5. Recommended Approach: Tiered Strategy

Given the landscape, we recommend a tiered approach:

### Tier 1: Axiomatic Interface (Current — 0 additional effort)

MPSLean already has a clean axiomatic interface via `blockSeparation_from_spectralTheory` that assumes the block separation result. The single-block case (r=1) is fully proved, and the multi-block case has an explicit, well-documented hypothesis. This is the **production interface** and should remain the default.

### Tier 2: Direct Finite-Dimensional Argument (1–2 months)

As recommended in the Spectral Gap Analysis report, pursue a direct algebraic proof that avoids the full generality of quantum PF:

1. **Vandermonde separation** of eigenvalue weights $\mu_k^N$ to isolate individual blocks (already established to work when eigenvalues are distinct).
2. **Transfer operator spectral analysis** for a single block: show that the identity component dominates as $N \to \infty$.
3. **Key insight:** For the specific transfer operator $E_A(X) = \sum_i A_i X A_i^\dagger$ arising from a canonical-form MPS, irreducibility of $E_A$ follows from the canonical form conditions (already in MPSLean).

**Community resource usage:**
- Cherry-pick Choi matrix definitions from Lean-QuantumInfo (~200 lines)
- Use Mathlib's existing spectral infrastructure (spectral radius, eigenvalues)
- Use Mathlib's `Matrix.IsIrreducible` as the starting point for irreducibility conditions

### Tier 3: Full Quantum PF (3–6 months, optional)

If/when the Cipollina PF code becomes public:

1. Import the classical PF infrastructure
2. Formalize the Choi-Jamiołkowski isomorphism (building on Lean-QuantumInfo)
3. Prove the quantum PF theorem by reduction to the classical case via the Choi matrix
4. Apply to the transfer operator

This would be a significant contribution to the Lean 4 ecosystem beyond MPSLean.

### Tier 4: Contribute to Mathlib (6–12 months, aspirational)

Package the quantum PF formalization for Mathlib contribution:
- Classical PF eigenvalue theorem (closing issue #6091)
- Choi-Jamiołkowski isomorphism for concrete matrices
- Quantum PF as a consequence
- Transfer operator theory for MPS applications

---

## 6. Effort Estimates with Community Resources

| Approach | Without Community Resources | With Community Resources | Savings |
|----------|---------------------------|--------------------------|---------|
| **Axiomatic (current)** | Done ✅ | Done ✅ | — |
| **Direct algebraic argument** | 1–2 months | 3–5 weeks | ~30% |
| **Classical PF + Choi bridge** | 3–4 months | 2–3 months | ~25% |
| **Full quantum PF** | 4–6 months | 3–4 months | ~30% |

The savings come primarily from:
- **Lean-QuantumInfo Choi isomorphism:** Saves ~2 weeks of formalization
- **Cipollina PF (when available):** Saves ~4–6 weeks on classical PF infrastructure
- **Mathlib spectral infrastructure:** Already available, saves ~2–3 weeks vs. building from scratch

---

## 7. Monitoring Checklist

To stay current with community developments:

- [ ] **Monthly:** Check Mathlib PRs for "Perron", "Frobenius", "spectral radius" keywords
- [ ] **Monthly:** Check PhysLean repo for merged neural network / PF PRs
- [ ] **Monthly:** Check arXiv:2512.07766 for camera-ready version with repo link
- [ ] **Quarterly:** Check Lean-QuantumInfo for spectral theory additions
- [ ] **Quarterly:** Check Lean Zulip `#mathlib4` for PF theorem discussions
- [ ] **Watch:** Mathlib issue #6091 (PF theorem in 100-theorems list)

---

## 8. Conclusion

The Lean 4 ecosystem is approaching but has not yet reached the point where quantum Perron-Frobenius theory can be assembled from existing components. The two most relevant resources — Cipollina's classical PF and Meiburg's quantum information library — together cover the two halves of the bridge (classical eigenvalue theory + quantum channel structure) but neither has been connected to the other, and one is not yet publicly available.

For MPSLean's practical needs, the recommended path is:
1. **Keep the current axiomatic interface** as the production version.
2. **Pursue the direct finite-dimensional algebraic argument** (Tier 2) as the next proof effort, cherry-picking Choi definitions from Lean-QuantumInfo.
3. **Monitor** the Cipollina PF availability for a potential faster path to a full proof.
4. **Consider contributing** a quantum PF formalization to Mathlib as a longer-term community contribution.

The single-block case remains **fully closed** with zero sorries. The multi-block case has a clear, well-documented path to closure that community resources can accelerate but not eliminate the need for original formalization work.

---

## ADDENDUM (2026-02-09, later): HopfieldNet Repository Now Public

### Major Update

The Cipollina/Karatarakis/Wiedijk code has been found at **https://github.com/mkaratarakis/HopfieldNet**. This dramatically changes the landscape:

| Factor | Previous Assessment | Updated Assessment |
|--------|--------------------|--------------------|
| **Availability** | Not public | **Public, MIT licensed** |
| **PF scope** | Stochastic matrices only | **General irreducible + primitive nonneg real matrices** |
| **Version compatibility** | Unknown | **Identical** (Lean v4.27.0-rc1, same Mathlib revision!) |
| **Import effort** | Unknown | **1 day** (add Lake dependency) |
| **Gap coverage** | Partial classical PF | **Full classical PF** (8,302 lines, 416 theorems) |

### Key Findings

1. **Full classical PF**: The code proves `pft_irreducible` (existence, uniqueness, spectral radius) and `spectral_dominance_of_primitive'` (strict spectral gap for primitive matrices) — these are the **complete** Perron-Frobenius theorem, not just the stochastic special case.

2. **Essentially sorry-free**: Only 1 sorry in the entire 8,302-line PF module (a minor quiver path lemma).

3. **Zero-friction import**: Same Lean version (v4.27.0-rc1 ≈ v4.27.0), **identical Mathlib revision** (`910dac3f6e7f4b2559dff67c9819543048995349`). Can be added as a Lake dependency with no version conflicts.

### Revised Effort Estimates

| Approach | Effort | Savings vs. from scratch |
|----------|--------|--------------------------|
| Import classical PF from HopfieldNet | 1 day | 2–3 months of PF formalization |
| Direct quantum PF + HopfieldNet as reference | 5–6 weeks | ~60% |
| Full vectorization bridge (classical → quantum) | 7–10 weeks | ~50% |

See `HOPFIELDNET_EFFORT_ANALYSIS.md` for the detailed analysis.
