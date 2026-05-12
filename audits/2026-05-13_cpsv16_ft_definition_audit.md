# CPSV16 Fundamental Theorem (proportional case): Definition Audit

**Date:** 2026-05-13
**Scope:** Read-only definitional cross-check of every Lean construct used by the
proportional Fundamental Theorem chain in `TNLean/MPS/FundamentalTheorem/Full/`,
against CPSV16 (arXiv:1606.00608v4, Annals of Physics 378 (2017)),
with secondary cross-references to CPSV21 (arXiv:2011.12127) and
PGVWC07 (quant-ph/0608197).
**Predecessors:**
- `blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md`
- `audits/2026-05-13_cpsv16_ft_paper_vs_code_structural_map.md`
- `audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md`
- `docs/paper-gaps/ft_one_copy_scope_restriction.tex`

The prior audits focused on **proofs** (the wrong-direction subgraph, the
combined-family LI workarounds, the discharge plan). This audit focuses on
**definitions**: are the math obstacles flagged in those audits true
paper-level gaps, or are they downstream symptoms of definitional restrictions
in our Lean encoding? Each section gives:
- (a) the Lean definition and its location;
- (b) the precise mathematical content;
- (c) the corresponding paper construct;
- (d) line-by-line comparison;
- (e) whether the discrepancy obstructs the paper's Step 1 per-block projection.

---

## 1. Canonical form

### 1.1 `IsCanonicalForm` (block-data version)

(a) **Lean:** `TNLean/PiAlgebra/CanonicalFormSepAux.lean:231–251`.

(b) **Content:** A `Prop`-valued structure on the *separated block data*
`(μ : Fin r → ℂ, A : (k : Fin r) → MPSTensor d (dim k))` with five fields:

```
block_injective       : ∀ k, IsInjective (A k)
leftCanonical         : ∀ k, ∑ i, (A k i)ᴴ * (A k i) = 1
mu_antitone           : Antitone (fun k => ‖μ k‖)
mu_ne_zero            : ∀ k, μ k ≠ 0
overlap_tendsto_one   : ∀ k, Tendsto (mpvOverlap (A k) (A k)) atTop (𝓝 1)
```

(c) **Paper:** CPSV16 §II "Canonical form" (the unnumbered definition on
p. 7 after eq. (II_CF1)):

> A tensor $A$ is in *canonical form* (CF) if $A^i = \bigoplus_{k=1}^r \mu_k A^i_k$
> and the tensors $A_k$ are NT.
> "We can always choose $|\mu_k| \le 1$ and at least one of them equals one,
> something which we will assume from now on" (p. 8, just after the definition).

Plus the unnumbered remark on p. 7 (eq. II_CF1 footnote): blocks $A_k$ are
**normal tensors** (CPSV16 §II, "normal tensor" definition on p. 7): "(i) there
exists no non-trivial projector $P$ such that $A^iP = PA^iP$; (ii) its
associated CPM has a unique eigenvalue of magnitude (and value) equal to its
spectral radius, which is equal to one."

CPSV16 separately introduces **CFII** (Definition in Appendix A on p. 30): a
tensor in CF such that each block CPM is **trace-preserving** with a
**full-rank diagonal fixed point**. CFII is what carries `∑ A^{i†} A^i = I` and
`Λ_k > 0`.

(d) **Comparison.**

- `block_injective` vs paper "blocks are NT": **Lean is strictly stronger.**
  The paper's CF requires each $A_k$ to be a normal tensor (NT), which means
  irreducibility + peripheral spectrum $= \{1\}$. Injectivity ($\{A^i\}$ span
  the full matrix algebra) is paper's **biCF** condition (Definition `defnbi`,
  p. 9 of CPSV16). By Wielandt's theorem (CPSV16 Proposition `propblockinj`,
  p. 9), every NT becomes injective after blocking at most $D^4$ times, so the
  two are *eventually* equivalent after blocking; but **as point-set
  definitions** Lean asks for biCF-level injectivity at the unblocked level,
  not CF.
- `leftCanonical` (`∑ A_k^{i†} A_k^i = I`) vs paper CF: **Lean is strictly
  stronger.** This is CFII's eq. (`TP`) (paper p. 30), *not* part of basic CF.
- `mu_antitone` (non-increasing modulus) vs paper: **matches** the paper's
  convention $|\mu_k| \le 1$ when combined with the dominant normalization.
- `mu_ne_zero` vs paper: matches the paper's convention (zero weights would
  correspond to redundant blocks excluded by CF).
- `overlap_tendsto_one` vs paper: **matches** the asymptotic conclusion of
  Lemma A.2 first part ($\langle V_\alpha | V_\alpha \rangle \to 1$); the paper
  treats this as a *consequence* of NT-ness plus the CFII normalization rather
  than as a separate field.

Net assessment: `IsCanonicalForm` is a *bundled CFII-plus-injectivity*
proposition. It is **substantially stronger** than the paper's basic CF (it
sits at the biCF-CFII intersection), and **strictly stronger** than CFII (which
does not by itself imply blockwise injectivity at the unblocked level).

The bundled form is consistent with the paper's "after blocking" working
assumption (CPSV16 §II discussion before Proposition `propblockinj`, p. 9: "we
will be mostly interested in MPVs obtained after a renormalization procedure
which will block large numbers of spins anyway"). So as a *working* definition
for theorems below the blocking horizon, it's fine. The deviation from the
basic CF is a stylistic shortcut, not a true narrowing of the FT setting.

(e) **Step 1 impact:** none. None of the narrowings above affect the per-block
projection of Step 1; if anything they help (injectivity is used downstream to
get the gauge matrix from the phase relation).

### 1.2 `IsCanonicalFormBNT` (the load-bearing structure)

(a) **Lean:** `TNLean/MPS/BNT/Construction.lean:99–110`.

(b) **Content:** Extends `IsCanonicalForm` with two extra fields:

```
mu_strict_anti        : StrictAnti (fun k : Fin r => ‖μ k‖)
blocks_not_equiv      : ∀ j k, j ≠ k → ∀ (h : dim j = dim k),
                          ¬ GaugePhaseEquiv (cast h (A j)) (A k)
```

i.e., **strictly** decreasing block-weight moduli plus pairwise BNT separation
(no two blocks are gauge-phase equivalent).

(c) **Paper:** The corresponding paper construct is the pair (CF, BNT), where
the BNT is **Definition 2.6** (CPSV16, p. 8):

> The tensors $A_j$ ($j = 1, \ldots, g$) form a *basis of normal tensors*
> (BNT) of a tensor $A$ if:
> (i) the $A_j$ are NT;
> (ii) for each $N$, $V^{(N)}(A)$ can be written as a linear combination of
>      $V^{(N)}(A_j)$;
> (iii) there exists some $N_0$ such that for all $N > N_0$, $V^{(N)}(A_j)$
>       are linearly independent.

The BNT minimality (Proposition `prop:char-BNT` (ii), CPSV16 p. 8): for any
element $A_j$, there is no other $j'$ with $A_j = e^{i\phi} X A_{j'} X^{-1}$
(no two BNT elements are phase-equivalent).

CPSV16 eq. (20a) gives the decomposition of $A$ in its BNT:

$$A^i = X \left[\bigoplus_{j=1}^{g} \left(M_j \otimes A^i_j\right)\right] X^{-1},
  \qquad M_j = \mathrm{diag}(\mu_{j,1}, \ldots, \mu_{j,r_j}),$$

and eq. (20b) restates this as

$$|V^{(N)}(A)\rangle = \sum_{j=1}^{g} \left(\sum_{q=1}^{r_j} \mu_{j,q}^N\right)
  |V^{(N)}(A_j)\rangle.$$

The key paper observation: **the BNT index $j$ does NOT come with a strict
modulus ordering.** Two distinct BNT elements $A_j$ and $A_{j'}$ are required
to be non-phase-equivalent (BNT minimality), but they may have *equal-modulus*
weights $|\mu_{j,1}| = |\mu_{j',1}| = 1$ (in fact, paper §II's
"$|\mu_k| \le 1$ with at least one equal to one" convention combined with the
CF→BNT normalization makes **every BNT element carry spectral radius
$|\mu_{j,q}| = 1$**, so they all sit at the same modulus class).

In particular, the paper's BNT allows **per-sector multiplicity** $r_j \ge 1$,
and the BNT expansion coefficient for block $j$ at length $N$ is
$\sum_{q=1}^{r_j} \mu_{j,q}^N$, a finite sum of unit-modulus complex numbers.

(d) **Comparison.** This is the headline narrowing already documented in
`docs/paper-gaps/ft_one_copy_scope_restriction.tex` and called out by both
prior audits. To make the discrepancy precise:

| Aspect | Lean `IsCanonicalFormBNT` | CPSV16 BNT (eqs. 20a–b) |
|---|---|---|
| Weight indexing | One weight `μ k` per Lean index `k : Fin r` | Multi-weight per BNT index: $\mu_{j,q}$ for $q = 1, \ldots, r_j$ |
| Multiplicity | Implicit $r_j = 1$ for every $j$ | $r_j \ge 1$ arbitrary |
| Modulus relation across indices | `StrictAnti` on `‖μ k‖` (every pair of blocks has strictly different modulus) | None — paper allows distinct BNT blocks at the same modulus class (in fact typically all at modulus 1) |
| Block-weight modulus value | `‖μ 0‖ = 1` only on the *dominant* index by `IsNormalCanonicalFormBNT.mu_dom_norm_one`; non-dominant `‖μ k‖ < 1` strictly | Every $\|\mu_{j,q}\| = 1$ (spectral radius 1 on every block) |
| BNT separation | `blocks_not_equiv` (no two distinct Lean blocks are gauge-phase equivalent) | Same — the BNT minimality of Proposition `prop:char-BNT` (ii) |
| Spans `V^(N)(A)` | Not asserted by `IsCanonicalFormBNT` itself; comes from the assembly `toTensorFromBlocks` | BNT condition (ii) |
| Eventual LI of `{V^(N)(A_j)}` | Not asserted by `IsCanonicalFormBNT`; comes from BNT separation via `eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal` (or `IsBNT.eventually_li`) | BNT condition (iii) |

**The two strictly stronger Lean conditions are `mu_strict_anti` and the
implicit `r_j = 1` collapse.** These pin two paper-degrees of freedom that the
paper proof crucially exploits:

1. The paper's CF eigenvalues all have modulus 1; non-dominant terms in the
   weighted sum do *not* decay geometrically. Lean's `mu_strict_anti` instead
   gives `‖μ k‖ < 1` for $k \ne 0$, producing geometric decay of every
   non-dominant block's contribution.
2. The paper's BNT coefficient $\sum_q \mu_{j,q}^N$ is a finite sum of
   unit-modulus complex numbers; it is bounded by $r_j$ and (by
   almost-periodicity / Vandermonde / CPSV16 Lem:app_simple) does not tend to
   0 with $N$. Lean's collapsed version is just $\mu_{j}^N$, which equals
   $\mu_0^N$ (modulus 1) on the dominant block and $\mu_j^N \to 0$
   geometrically off-dominant.

A multiplicity-aware structure for the same data exists in the codebase as
`SectorDecomposition` (`TNLean/MPS/SharedInfra/SectorDecomposition.lean:61`),
which carries the paper-faithful $(j, q)$ indexing, the multiset `weight j q`,
and the coefficient `coeff P N j = ∑_q (weight j q)^N`. But the proportional
FT chain is keyed on `IsCanonicalFormBNT`, not `SectorDecomposition`, so the
multiplicity surface is unreachable from the FT entry points.

(e) **Step 1 impact:** **Yes — `mu_strict_anti` is the proximate cause of the
non-leading-`k₀` obstruction.** Concretely:

- For *leading* `k₀ = b0`: the per-block projection works because
  `‖μA j / μA 0‖ ≤ 1` and `‖μB k / μB 0‖ ≤ 1` for all `j, k`, so the
  normalized sums in the projection are bounded. See
  `dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  in `ProportionalDominant.lean:850`, which closes the leading case.
- For *non-leading* `k₀ ≠ b0`: under `mu_strict_anti`, the BNT self-coefficient
  on the projected side is the single scalar $\mu_B(k_0)^N$ with
  $\|\mu_B(k_0)\| < 1$ strictly, so this *self*-term tends to **zero**
  geometrically. There is no $\sum_q \nu_{k_0,q}^N$ floor to keep the RHS
  bounded away from zero; the paper's per-block contradiction
  "LHS → 0, RHS → (non-decaying multiplier) · 1" collapses to
  "LHS → 0, RHS → 0" with no contradiction.

The discharge-plan audit (§5.2) flags exactly this:

> In the one-copy-per-sector surface, $\|\mu_B(k_0)\| < 1$ for $k_0 \neq 0$.
> The BNT expansion coefficient for block $B_{k_0}$ is the single scalar
> $\mu_B(k_0)^N$, which tends to zero geometrically. The self-term
> $\mu_B(k_0)^N \cdot \langle V(B_{k_0}) | V(B_{k_0}) \rangle \sim \mu_B(k_0)^N \to 0$
> no longer provides a non-vanishing contribution.

This is a definitional gap, not a paper gap. Section 9 below states the
yes/no answer.

### 1.3 `IsNormalCanonicalForm` and `IsNormalCanonicalFormBNT`

(a) **Lean:** `TNLean/PiAlgebra/CanonicalFormSepAux.lean:317–332` and
`TNLean/MPS/BNT/Construction.lean:187–198`.

(b) **Content:** `IsNormalCanonicalForm` has
`block_irreducible`, `leftCanonical`, `block_primitive`, `mu_antitone`,
`mu_ne_zero`, `dim_pos`. `IsNormalCanonicalFormBNT` extends it with
`mu_strict_anti`, `blocks_not_equiv`, and `mu_dom_norm_one`
(the dominant weight has unit modulus).

(c) **Paper:** Same as 1.1 plus the normal-tensor definition (CPSV16 §II,
p. 7). `IsNormalCanonicalForm` is the closest match to CPSV16's CF: it asks
for *normal tensors* (irreducible + peripheral primitive) per block, not
algebraic injectivity, which is what the paper's CF actually requires.

(d) **Comparison.** This is the "weaker" CF variant, faithful to CPSV16 §II's
CF/NT formulation. Its BNT-strict version (`IsNormalCanonicalFormBNT`) carries
exactly the same `mu_strict_anti` narrowing as §1.2.

(e) **Step 1 impact:** Same as 1.2. The FT proportional chain in
`TNLean/MPS/FundamentalTheorem/Full/` uses `IsCanonicalFormBNT` (not the
NCF-BNT variant), so the practical narrowing is via 1.2.

### 1.4 `IsLeftCanonicalBlockFamily`, `HasNormalizedSelfOverlap`,
`HasInjectiveBlocks`, `HasStrictOrderedNonzeroWeights`

(a) **Lean:** `TNLean/PiAlgebra/CanonicalFormSepAux.lean:69, 128, 165, 200`.

(b) **Content:** Field projections of `IsCanonicalForm` / `IsCanonicalFormBNT`
into single-condition wrappers (each carries one of the fields above with the
same body).

(c) **Paper:** No direct analogue; these are bookkeeping helpers for the
modular re-assembly of CF hypotheses (see `IsCanonicalForm.ofSeparatedData`).

(d) **Comparison.** Same content as the corresponding fields of `IsCanonicalForm`;
no extra narrowing.

(e) **Step 1 impact:** None directly; they propagate the §1.2 narrowing only
because `HasStrictOrderedNonzeroWeights` carries `mu_strict_anti`.

---

## 2. Basis of normal tensors

### 2.1 `IsBNT`

(a) **Lean:** `TNLean/MPS/BNT/Basic.lean:75–87`.

(b) **Content:**

```
structure IsBNT {d Dtot : ℕ} (A_total : MPSTensor d Dtot)
    (g : ℕ) (dim : Fin g → ℕ) (A_bnt : (j : Fin g) → MPSTensor d (dim j)) where
  normal       : ∀ j, IsNormal (A_bnt j)
  spans_mpv    : ∀ N : ℕ, ∃ c : Fin g → ℂ, ∀ σ : Fin N → Fin d,
                   mpv A_total σ = ∑ j, c j * mpv (A_bnt j) σ
  eventually_li : ∃ N0 : ℕ, ∀ N > N0,
                   LinearIndependent ℂ (fun j => mpvState (A_bnt j) N)
```

(c) **Paper:** CPSV16 Definition 2.6 (p. 8, cited verbatim in §1.2 above):

> (i) the $A_j$ are NT;
> (ii) for each $N$, $V^{(N)}(A)$ can be written as a linear combination of
>      $V^{(N)}(A_j)$;
> (iii) there exists some $N_0$ such that for all $N > N_0$, $V^{(N)}(A_j)$
>       are linearly independent.

(d) **Comparison.**

- `normal` ↔ "the $A_j$ are NT": matches in *spirit* but the Lean `IsNormal`
  is the **algebraic** notion (`∃ N, IsNBlkInjective A N`,
  `TNLean/MPS/Defs.lean:243–244`) — eventual block injectivity — whereas the
  paper's NT (CPSV16 §II p. 7) is the **spectral** notion: no nontrivial
  invariant projector and unique peripheral eigenvalue. By Wielandt's theorem
  these are equivalent up to blocking (paper §II just before
  `propblockinj`), but the equivalence is a theorem, not a definitional
  identity. For BNT this is the right surface to expose (it's what gets used
  downstream in MPV spanning arguments), so this is a sound stylistic choice.
- `spans_mpv` ↔ BNT (ii): **matches.**
- `eventually_li` ↔ BNT (iii): **matches.** Both use `∃ N0, ∀ N > N0`
  (strict `>`). One should record that the strict-inequality form is the
  paper's literal statement; downstream wrappers like
  `eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal` use
  `∀ᶠ N in atTop` which is interchangeable (Lean's Filter API converts
  between them).

(e) **Step 1 impact:** None. `IsBNT.eventually_li` is paper-faithful and is
exactly the LI input the paper's per-block projection needs (LI of one BNT
family, not combined-family LI).

### 2.2 `HasNormalizedSelfOverlap`, `HasInjectiveBlocks`

(a, b, c, d, e) Covered in §1.4. Both are paper-faithful single-field
projections.

---

## 3. Normal tensor

### 3.1 `IsNormal`

(a) **Lean:** `TNLean/MPS/Defs.lean:243–244`.

(b) **Content:**

```
def IsNBlkInjective (A : MPSTensor d D) (N : ℕ) : Prop :=
  Submodule.span ℂ (Set.range fun σ : Fin N → Fin d => evalWord A (List.ofFn σ))
    = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))
def IsNormal (A : MPSTensor d D) : Prop :=
  ∃ N : ℕ, IsNBlkInjective A N
```

(c) **Paper:** CPSV16 §II, "normal tensor" definition (p. 7):

> A tensor $A$ is a *normal tensor* (NT) if: (i) there exists no non-trivial
> projector $P$ such that $A^i P = P A^i P$; (ii) its associated CPM has a
> unique eigenvalue of magnitude (and value) equal to its spectral radius,
> which is equal to one.

Wolf 2012 §6 gives an extensive treatment of primitivity / irreducibility of
CP maps. The two paper conditions are: no invariant subspace (irreducibility)
+ peripheral spectrum $= \{1\}$ (primitivity).

(d) **Comparison.** Lean's `IsNormal` is **eventual block injectivity**, which
is the *consequence* of paper's NT after Wielandt blocking (CPSV16 §II
remarks p. 9: after $D^4$ blockings every NT becomes injective). It is **not**
the spectral definition; it captures only the post-blocking algebraic
consequence.

The codebase has a separate spectral-primitivity surface at
`TNLean/Channel/Peripheral/Spectrum.lean:181` (`IsPrimitive` on a channel,
`peripheralEigenvalues E = {1}`) and `IsIrreducibleTensor` at
`TNLean/MPS/CanonicalForm/Reduction.lean:54` (no invariant orthogonal
projection). These match the paper's two conditions. `IsNormalCanonicalForm`
(§1.3) carries both.

The choice of `IsNormal := eventually-block-injective` is broadening (any
tensor that becomes block-injective after enough blocking qualifies). For an
*arbitrary* `A`, paper's NT ⇒ Lean's `IsNormal` (by Wielandt), but the reverse
is generally only true under the additional peripheral-spectrum condition.

Also, there is a `IsPrimitivePaper` in
`TNLean/Wielandt/Primitivity/PaperDefinitions.lean:129` matching PGVWC07 /
arXiv:0909.5347's `H_q(A,φ) = ℂ^D` formulation; this is the paper-faithful
primitivity surface independent of `IsNormal`.

(e) **Step 1 impact:** None. The proportional FT uses BNT structure
(`IsBNT.normal`), but the actual *use* in the proof of Step 1 is the *spectral*
consequence (Lemma A.2's "0 or 1" dichotomy and Corollary `eqV`'s exact phase
relation), and these are extracted via separate lemmas
(`mpvOverlap_self_scale_of_mpv_eq_pow_mul`, `norm_eq_one_of_selfOverlap_scale`,
etc.) that work uniformly with the algebraic `IsNormal` plus CF-overlap data.
So this broadening doesn't bite the FT.

### 3.2 `IsIrreducibleTensor`, `IsPrimitive`

(a, b, c, d, e) These exactly match the paper's two NT conditions
(no-invariant-projector + peripheral-spectrum = {1}). See §1.3 above.

---

## 4. MPV / mpvState / MPVSpace / toTensorFromBlocks

### 4.1 `mpv` and `mpvState`

(a) **Lean:** `TNLean/MPS/Defs.lean:70` and `TNLean/MPS/Overlap/Basic.lean:40`.

(b) **Content:**

```
def mpv (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) : ℂ :=
  Matrix.trace (evalWord A (List.ofFn σ))
abbrev MPVSpace (d N : ℕ) := EuclideanSpace ℂ (Fin N → Fin d)
def mpvState (A : MPSTensor d D) (N : ℕ) : MPVSpace d N :=
  (EuclideanSpace.equiv (ι := Fin N → Fin d)).symm (fun σ => mpv A σ)
```

(c) **Paper:** CPSV16 eq. (4) (p. 6):

$$|V^{(N)}(A)\rangle = \sum_{i_1, \ldots, i_N}
  \mathrm{tr}(A^{i_1} A^{i_2} \cdots A^{i_N}) |i_1 \ldots i_N\rangle$$

(d) **Comparison.** Exact match. `mpv A σ` is the coefficient
$\mathrm{tr}(A^{σ_0} \cdots A^{σ_{N-1}})$, and `mpvState A N` assembles them
into the EuclideanSpace coefficient vector.

(e) **Step 1 impact:** None.

### 4.2 `toTensorFromBlocks`

(a) **Lean:** `TNLean/MPS/SharedInfra/BlockAssembly.lean:23–28`.

(b) **Content:**

```
noncomputable def toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) :
    MPSTensor d (∑ k : Fin r, dim k) := fun i =>
  (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
    (Matrix.blockDiagonal' fun k => (μ k) • (A k i))
```

with `mpv_toTensorFromBlocks_eq_sum` (line 53):
`mpv (toTensorFromBlocks μ A) σ = ∑ k, (μ k)^N · mpv (A k) σ`.

(c) **Paper:** CPSV16 eq. (20a):

$$A^i = X \left[\bigoplus_{j=1}^{g} \left(M_j \otimes A^i_j\right)\right] X^{-1},
  \qquad M_j = \mathrm{diag}(\mu_{j,1}, \ldots, \mu_{j,r_j}),$$

i.e., the assembled tensor is conjugated by an overall gauge `X` and contains
**a sum of $r_j$ weighted copies of $A^i_j$** for each BNT index `j`.

(d) **Comparison.** Two narrowings:

- **No overall gauge `X`.** Lean assembles only the block-diagonal piece; the
  outer conjugation by an invertible `X` is delegated to a downstream
  `GaugePhaseEquiv` / `GaugeEquiv` wrapper. This is fine and standard.
- **No internal multiplicity.** Lean's `toTensorFromBlocks` carries **one
  weight `μ k` per Lean block index `k`**. The paper's eq. (20a) has, *per
  BNT index $j$*, a *diagonal matrix* $M_j$ of size $r_j \times r_j$ with
  entries $\mu_{j,1}, \ldots, \mu_{j,r_j}$. So Lean's tensor is the special
  case $r_j = 1$ for all $j$.

The collapsed MPV expansion `mpv_toTensorFromBlocks_eq_sum` gives
$\sum_k \mu_k^N \cdot \mathrm{mpv}(A_k) σ$, which corresponds to CPSV16
eq. (20b)

$$|V^{(N)}(A)\rangle = \sum_j \left(\sum_q \mu_{j,q}^N\right) |V^{(N)}(A_j)\rangle$$

**only when $r_j = 1$ for every $j$**. The paper's full coefficient
$\sum_q \mu_{j,q}^N$ is the sum-of-unit-modulus-powers that does not decay in
$N$; Lean's $\mu_k^N$ collapses to a single complex number raised to the $N$th
power.

The codebase's `SectorDecomposition` (`SharedInfra/SectorDecomposition.lean:61`)
exposes the paper-faithful multiplicity surface
(`P.basis : Fin basisCount → MPSTensor ...` and
`P.weight : (j : Fin basisCount) → Fin (P.copies j) → ℂ`), and
`SectorWeightData.coeff S N j = ∑_q (S.weight j q)^N` matches the paper's
expansion coefficient exactly. The FT proportional chain does **not** use this
surface.

(e) **Step 1 impact:** **Yes — this is the same narrowing as §1.2**, viewed
from the assembled-tensor side. The collapsed expansion has *single-term*
coefficients $\mu_k^N$ which decay geometrically off-dominant, instead of the
paper's bounded non-decaying $\sum_q \mu_{j,q}^N$. The paper's per-block
projection of Step 1 hinges on $\sum_q \nu_{k_0,q}^N \not\to 0$, which is
unavailable here.

---

## 5. MPV overlap

### 5.1 `mpvOverlap` and `mpvInner`

(a) **Lean:** `TNLean/MPS/Overlap/Basic.lean:49–54`.

(b) **Content:**

```
def mpvInner (A B) (N) : ℂ :=
  ⟪mpvState A N, mpvState B N⟫_ℂ
def mpvOverlap (A B) (N) : ℂ :=
  ∑ σ : Cfg d N, mpv A σ * star (mpv B σ)
```

with the bridging lemma `mpvOverlap_eq_star_mpvInner` (line 60):
`mpvOverlap A B N = star (mpvInner A B N)`.

(c) **Paper:** CPSV16 §A uses the physics ket-bra notation
$\langle V_b | V_a \rangle$ throughout (Lemma A.2, p. 30). In physics
notation, $\langle V_b | V_a \rangle = \sum_\sigma \overline{V_b(\sigma)} V_a(\sigma)$
— the **bra** $V_b$ is complex-conjugated, the **ket** $V_a$ is not.

Lemma A.2's overlap is
$\langle V_b | V_a \rangle = \mathrm{tr}(\mathbb{E}_{ab}^N)$ with
$\mathbb{E}_{ab} = \sum_i A_a^i \otimes \overline{A_b^i}$.

(d) **Comparison.** Lean's two overlaps are related to the paper's
$\langle V_b | V_a \rangle$ as follows:

- `mpvInner A B N = ⟪mpvState A, mpvState B⟫_ℂ`. Lean's `⟪·,·⟫` is
  conjugate-linear in the **first** argument (Mathlib convention,
  `PiLp.inner_apply`), so
  $$\mathrm{mpvInner}(A, B, N) = \sum_\sigma \overline{\mathrm{mpv}\,A\,\sigma}\,
  \mathrm{mpv}\,B\,\sigma.$$
  Identifying $A \leftrightarrow$ bra and $B \leftrightarrow$ ket, this is
  **the physics $\langle V_A | V_B \rangle$**.
- `mpvOverlap A B N = ∑_σ mpv(A,σ) · star (mpv(B,σ))`. The conjugation is on
  $B$ (the *second* argument), so this is the *physics* $\langle V_B | V_A \rangle$
  with $A$ as ket and $B$ as bra. Equivalently,
  `mpvOverlap A B N = star (mpvInner A B N) = conj ⟨V_A | V_B⟩`.

So `mpvOverlap A B = ⟨V_B | V_A⟩` in physics notation. The paper's
$\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle$ corresponds to
`mpvOverlap (A j) (B k) N` in Lean (note the **swap**).

**Orientation check** against the proportional-FT scaffolding: lemmas like
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
hypothesize `∀ j, Tendsto (fun N => mpvOverlap (A j) (B k₀)) atTop (𝓝 0)`
— i.e., $\langle V(B_{k_0}) | V(A_j) \rangle \to 0$ in physics notation,
which is the paper Step 1's hypothesis-to-be-contradicted. **Sign/orientation
match: correct.**

(e) **Step 1 impact:** None. The orientation is consistent with the paper and
with the way `hAllDecay` enters Step 1.

---

## 6. Proportional MPV

### 6.1 `SameMPV₂`

(a) **Lean:** `TNLean/MPS/Defs.lean:90`.
(b) **Content:** `∀ N σ, mpv A σ = mpv B σ` (heterogeneous bond-dim version).
(c) **Paper:** Equal-MPV hypothesis of Corollary `II_cor2` (CPSV16 p. 9).
(d) **Comparison.** Exact match.
(e) **Step 1 impact:** None.

### 6.2 `ProportionalMPV₂`

(a) **Lean:** `TNLean/MPS/Defs.lean:108–109`.
(b) **Content:** `∀ N, ∃ c : ℂ, ∀ σ, mpv A σ = c * mpv B σ`.
(c) **Paper:** Theorem `thm1` (CPSV16 p. 9): "If for all $N$, $A$ and $B$
generate MPV that are proportional to each other..." The scalar in the
proportionality is not required nonzero in this reading.
(d) **Comparison.** Direct reading; allows degenerate `c = 0` at some `N`
(which would imply `V^(N)(A) = 0`).
(e) **Step 1 impact:** None directly; the proportional FT chain uses the
nonzero variant.

### 6.3 `NonzeroProportionalMPV₂`

(a) **Lean:** `TNLean/MPS/Defs.lean:122–124`.
(b) **Content:** `∀ N, ∃ c : ℂ, c ≠ 0 ∧ ∀ σ, mpv A σ = c * mpv B σ`.
(c) **Paper:** Theorem `thm1`, projective reading; see also
`docs/paper-gaps/cpsv16_nonzero_proportionality_reading.tex`.
(d) **Comparison.** Faithful projective reading of "proportional to each
other".
(e) **Step 1 impact:** None.

### 6.4 `EventuallyNonzeroProportionalMPV₂` (the actual FT hypothesis)

(a) **Lean:** `TNLean/MPS/Defs.lean:136–141`.

(b) **Content:**

```
def EventuallyNonzeroProportionalMPV₂ (A B) : Prop :=
  ∀ᶠ N in atTop, ∃ c : ℂ, c ≠ 0 ∧ ∀ σ, mpv A σ = c * mpv B σ
```

i.e., for sufficiently large `N`, there is a nonzero proportionality scalar.
**Crucially, the scalar `c` is chosen *independently* at each `N`** (it is the
existential witness inside `∃`, parametrized by `N`).

(c) **Paper:** Theorem `thm1` of CPSV16 (p. 9). The paper states the
hypothesis as "for all $N$, $A$ and $B$ generate MPV that are proportional to
each other". The hidden scalar $\lambda_N$ is implicit: $|V^{(N)}(B)\rangle = \lambda_N |V^{(N)}(A)\rangle$.

(d) **Comparison.** Three deviations from the paper:

1. **`∀ᶠ N` vs paper's `∀ N`.** Broadening: the paper requires proportionality
   at *every* $N$; Lean only requires it eventually. This is harmless when
   combined with the BNT eventual-LI condition (the proof uses
   $N \to \infty$ asymptotics anyway), but it is a strictly weaker hypothesis.
   This matches the analysis memo's reading (`Lem1` is itself an eventual
   statement).
2. **Per-`N` scalar `c`.** The Lean definition only insists that *some*
   nonzero `c` exists at each `N`; nothing pins down the function `N ↦ c_N`
   beyond pointwise nonvanishing. **No boundedness, no continuity, no
   convergence**. In particular, `c_N` is allowed to oscillate wildly with
   `N`.
3. **Paper's implicit boundedness of $\lambda_N$.** The analysis memo §4.2
   reads the paper's proof as silently using $\lambda_N$ bounded: both
   $\|V^{(N)}(A)\|$ and $\|V^{(N)}(B)\|$ tend to finite positive limits
   (because the BNT coefficients $\sum_q \mu_{j,q}^N$ are bounded by $r_j$,
   sums of unit-modulus complex numbers, and the BNT cross-overlaps tend to
   $\delta_{j,j'}$). So $\lambda_N$ has finite limit modulus and is
   eventually bounded. This is a *consequence* in the paper, derived from the
   CF + BNT spectral structure.

   In Lean, with the strict-modulus restriction, the analogous argument
   gives $\|V^{(N)}(A)\| \to |\mu_A(0)| = 1$ (only the dominant block
   survives), so $c_N \cdot \mu_B(0)^N / \mu_A(0)^N$ tends to a unit-modulus
   limit (this is the `exists_dominant_adjusted_scalar_tendsto_norm_one`
   lemma, `ProportionalDominant.lean:536`). But this is **norm convergence
   only**, not value convergence; and the adjusted-phase version
   (`exists_dominant_phase_adjusted_scalar_tendsto_one`, line 303) gives
   value convergence only **after** the dominant phase $\zeta$ is known. The
   downstream needs the **exact** identity `c_N · (μB 0 · ζ / μA 0)^N = 1`
   for large $N$, which the Lean definition by itself does not constrain.

(e) **Step 1 impact:** Indirect but real. Under the §1.2 narrowing, the
leading-block route is the only one available; that route needs to upgrade
the asymptotic adjusted-scalar limit to an exact eventual identity (the
"exactness lemma" of the discharge plan §4.3). The looseness of
`EventuallyNonzeroProportionalMPV₂` — `c_N` is free and unconstrained — does
not help: there is no built-in handle to upgrade a `Tendsto` into an
`Eventually =`. This is the discharge-plan §4.3 obstruction.

Note however: if the §1.2 narrowing were lifted, the paper-faithful Step 1
goes through with `c_N` only assumed bounded (which is *derivable* from the
multiplicity-aware BNT data and Lemma A.2 applied to each BNT block, *not* a
hypothesis on `c_N` itself). So `EventuallyNonzeroProportionalMPV₂`'s
looseness is not the cause of the obstruction.

### 6.5 `EventuallyProportionalMPV₂`

Does not exist in the codebase. Searched
`grep -rn EventuallyProportionalMPV TNLean/` — only the nonzero variant
exists. No discrepancy.

---

## 7. Gauge / phase equivalence

### 7.1 `GaugeEquiv`

(a) **Lean:** `TNLean/MPS/Defs.lean:78–79`.

(b) **Content:**

```
def GaugeEquiv (A B : MPSTensor d D) : Prop :=
  ∃ X : GL (Fin D) ℂ, ∀ i, B i = X * A i * X⁻¹
```

(c) **Paper:** CPSV16 §II eq. (II:A=XAX): $\tilde A^i = X A^i X^{-1}$ for some
invertible $X$. (Also CPSV21 Def. 4.3.)
(d) **Comparison.** Match (invertible $X$, no phase).
(e) **Step 1 impact:** None.

### 7.2 `GaugePhaseEquiv`

(a) **Lean:** `TNLean/MPS/Defs.lean:200–203`.

(b) **Content:**

```
def GaugePhaseEquiv (A B : MPSTensor d D) : Prop :=
  ∃ (X : GL (Fin D) ℂ) (ζ : ℂ), ζ ≠ 0 ∧ ∀ i, B i = ζ • (X * A i * X⁻¹)
```

(c) **Paper:** Two relevant paper constructs:

- **CPSV16 Lemma A.2 conclusion** (p. 30): "$D_a = D_b$ and there exists a
  non-singular matrix $X$, and a phase $\phi$ so that $A^i_b = e^{i\phi} X A^i_a X^{-1}$."
  And in the *proof*: "Thus, $D_a = D_b$, and $X$ is **unitary**."
  So Lemma A.2's literal conclusion at the CFII level is: $X$ **unitary** and
  the scalar is $e^{i\phi}$ (**unit modulus**).
- **CPSV16 Theorem `thm1` conclusion** (the FT, p. 9): "there exists a $j_k$,
  phases $\phi_k$, and non-singular matrices $X_k$ such that
  $B^i_k = e^{i\phi_k} X_k A^i_{j_k} X_k^{-1}$."
  At the FT level: $X_k$ **non-singular** (= invertible), scalar $e^{i\phi_k}$
  **unit modulus**.
- **CPSV16 Corollary `thm:Fundamental-CFII`** (p. 32): when the input tensors
  are in CFII, the $X_k$ are **unitary**.

(d) **Comparison.**

| Aspect | Lean `GaugePhaseEquiv` | CPSV16 FT conclusion | CPSV16 Lemma A.2 conclusion (CFII) |
|---|---|---|---|
| $X$ | invertible (`GL (Fin D) ℂ`) | non-singular | **unitary** |
| Scalar $\zeta$ | nonzero (`ζ ≠ 0`) | unit modulus ($e^{i\phi}$) | unit modulus ($e^{i\phi}$) |

So `GaugePhaseEquiv` is **broader than the paper's FT conclusion on the
scalar** (allows any nonzero $\zeta$, not just $|\zeta| = 1$), and **broader
than Lemma A.2's CFII-conclusion on $X$** (allows any invertible $X$, not just
unitary).

Two mitigations in the Lean codebase:

- Downstream lemmas like `norm_eq_one_of_selfOverlap_scale` derive
  $\|\zeta\| = 1$ from the self-overlap normalization. So in the
  `IsCanonicalFormBNT` context where `overlap_tendsto_one` holds for every
  block, the scalar in any `GaugePhaseEquiv` produced from a Lemma-A.2-style
  inner-product argument *will* have unit modulus. The structure
  `GaugePhaseEquiv` itself just doesn't *bundle* this.
- The unitarity of $X$ is not separately bundled. The `BlockPermutationGaugePhaseConclusion`
  (§8 below) inherits this: it asserts only the FT-level "non-singular $X$",
  not the CFII-level unitarity.

(e) **Step 1 impact:** None directly. The paper's FT theorem statement
(Theorem `thm1`) only requires non-singular $X_k$ and unit-modulus scalars;
the Lean conclusion is *broader on $\zeta$* but the proof routes that
produce a `GaugePhaseEquiv` (via `gaugePhaseEquiv_of_nondecaying_overlap_CFBNT`,
`NondecayingPartnerUnique.lean:63`) do, in fact, generate a unit-modulus
$\zeta$ — the `ζ ≠ 0` field is a *type-level looseness* that is always
tightened in practice. This costs us nothing at Step 1.

### 7.3 The "$X$ is an isometry / unitary" sub-step

The analysis memo §7(ii) flags that Lemma A.2's proof of $X^\dagger X = c \cdot \mathbb{1}$
elides a rescaling step. The Lean codebase carries the per-pair phase-extraction
machinery (`exists_phase_mpvState_eq_smul_of_nondecaying_overlap_CFBNT` at
`NondecayingPartnerUnique.lean:100`) and produces the gauge matrix via
`gaugePhaseEquiv_of_nondecaying_overlap_CFBNT` (line 63). The output is a
`GaugePhaseEquiv`, not bundled with unitarity. **No paper-level mismatch** —
this is a stylistic non-bundling.

---

## 8. Block decomposition / `BlockPermutationGaugePhaseConclusion`

### 8.1 `toTensorFromBlocks`

Covered in §4.2.

### 8.2 `BlockPermutationGaugePhaseConclusion`

(a) **Lean:** `TNLean/MPS/BNT/Construction.lean:549–559`.

(b) **Content:**

```
abbrev BlockPermutationGaugePhaseConclusion
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k)) : Prop :=
  ∃ _h : rA = rB,
    ∃ perm : Fin rA ≃ Fin rB,
      ∀ j : Fin rA,
        ∃ hdim : dimA j = dimB (perm j),
          GaugePhaseEquiv (d := d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B (perm j))
```

(c) **Paper:** CPSV16 Theorem `thm1` conclusion (p. 9):

> (i) $g_a = g_b =: g$;
> (ii) for all $k$ there exists a $j_k$, phases $\phi_k$, and non-singular
>      matrices $X_k$ such that $B^i_k = e^{i\phi_k} X_k A^i_{j_k} X_k^{-1}$.

(d) **Comparison.**

- `_h : rA = rB` ↔ paper (i): match.
- `perm : Fin rA ≃ Fin rB` is the inverse of the map $k \mapsto j_k$ in the
  paper. Same data.
- `∃ hdim : dimA j = dimB (perm j)` is implicit in the paper because the
  paper proves dimensions match as part of Lemma A.2. Lean keeps it as a
  per-pair existential, faithful.
- `GaugePhaseEquiv ...` ↔ paper "$e^{i\phi_k}$ phase + $X_k$ non-singular":
  match (subject to the §7.2 looseness on $\zeta$ which is harmless).

**Exact correspondence to eq. (20a):** No — eq. (20a) decomposes a *single*
tensor $A$ in its own BNT. `BlockPermutationGaugePhaseConclusion` is the
*comparison* between two tensors' BNTs (eq. (20a) for $A$ vs eq. (20a) for $B$,
combined with the FT conclusion that the BNTs match up to permutation +
phase + gauge per block). This is the right structure for the FT conclusion.

(e) **Step 1 impact:** None. This is the **output** of the FT, not an input
to Step 1.

---

## 9. Definitional gaps that may explain the proof gaps

In priority order:

### (i) `IsCanonicalFormBNT.mu_strict_anti` (§1.2): **THE** load-bearing narrowing

**Status:** Lean is strictly narrower than CPSV16's CF/BNT pair.

**What CPSV16 actually has:**
- All BNT blocks $A_j$ have *spectral radius 1* (every weight $\mu_{j,q}$ has
  $|\mu_{j,q}| = 1$).
- Per-BNT-block multiplicity $r_j \ge 1$; the BNT expansion coefficient at
  length $N$ is $\sum_{q=1}^{r_j} \mu_{j,q}^N$, a sum of unit-modulus complex
  numbers (bounded by $r_j$, does not tend to 0 by almost-periodicity /
  Lem:app_simple).
- BNT minimality (no two BNT blocks phase-equivalent), but BNT blocks at the
  *same modulus class* are allowed.

**What Lean has:**
- One BNT index $k : \mathrm{Fin}\ r$ per modulus class, with a single weight
  $\mu_k$.
- $\|\mu_0\| = 1$ dominant, $\|\mu_k\| < 1$ strictly for $k \ne 0$.
- Single-term expansion coefficient $\mu_k^N$, decaying geometrically
  off-dominant.

**Recommendation:** Restrict / restate. Two routes:

1. **Migrate the FT chain to use `SectorDecomposition`** (already in the
   codebase at `SharedInfra/SectorDecomposition.lean:61`) with full
   multiplicity. This is the paper-faithful surface; rename or wrap
   `IsCanonicalFormBNT` as `IsCollapsedCanonicalFormBNT` (the
   one-copy-per-sector special case) and use `SectorDecomposition` plus
   `HasBNTSectorData` for the FT statement.
2. **Relax `mu_strict_anti` to `mu_class_strict_anti`** — strict ordering on
   the *quotient* by phase-equivalence-modulus-class — and add a separate
   multiplicity field. This is more invasive.

Either route would surface the paper's $\sum_q \mu_{j,q}^N$ as the actual
expansion coefficient and unblock the per-block projection for arbitrary
$k_0$.

### (ii) `toTensorFromBlocks` / eq. (20a) (§4.2): a symptom of (i)

**Status:** Lean's assembled tensor has the $r_j = 1$ collapse.
**Recommendation:** Follows from (i); the paper-faithful assembler is the
flattened `SectorDecomposition.toTensor`-style construction.

### (iii) `EventuallyNonzeroProportionalMPV₂` (§6.4): mild broadening, not the obstruction

**Status:** Lean's `c_N` is a per-`N` free sequence. The paper's $\lambda_N$
is implicitly bounded by the BNT spectral structure.
**Recommendation:** Keep as-is; derive boundedness from the (relaxed) BNT
data as a separate lemma. Once (i) is fixed, this is not load-bearing.

### (iv) `GaugePhaseEquiv` scalar not pinned to $|\zeta| = 1$ (§7.2): mild

**Status:** Lean allows $\zeta$ any nonzero, paper has $e^{i\phi_k}$.
**Recommendation:** Optionally tighten to `∃ X ζ, ‖ζ‖ = 1 ∧ ...` to match
the FT theorem statement. Practically benign because every constructor in the
codebase produces unit-modulus $\zeta$.

### (v) `IsCanonicalForm` is at the biCF/CFII level (§1.1): paper-acceptable shortcut

**Status:** Bundled biCF + CFII fields rather than basic CF. Justified by
the "after blocking" working assumption of CPSV16.
**Recommendation:** Document but do not change.

### (vi) `IsNormal = eventually block injective` (§3.1): paper-equivalent

**Status:** Algebraic surrogate of paper's spectral NT; equivalent after
Wielandt blocking.
**Recommendation:** No change.

---

## 10. The bottom-line yes/no

> **Question:** If we replaced `IsCanonicalFormBNT` with the paper's CF
> (spectral radius 1, multiplicity inside sectors recovered via BNT
> eigenvalues), would the per-block projection of CPSV16 Step 1 go through
> for arbitrary $k_0$ without any combined-family LI?

### Answer: **YES.**

### Justification (the algebra)

Under the **paper-faithful CF/BNT** (every $\mu_{j,q}$ and $\nu_{k,q}$ has
$|·| = 1$; multiplicity $r_j, r_k \ge 1$; BNT minimality; per-BNT eventual LI),
fix any $k_0$ on the $B$ side and consider the hypothesis $\mathrm{hAllDecay}$:
$\langle V^{(N)}(B_{k_0}) | V^{(N)}(A_j) \rangle \to 0$ for **every** $j$.

From the proportionality $|V^{(N)}(A)\rangle = c_N |V^{(N)}(B)\rangle$, take
inner product with $|V^{(N)}(B_{k_0})\rangle$:

$$
\underbrace{\sum_j \left(\sum_q \mu_{j,q}^N\right)
  \langle V^{(N)}(B_{k_0}) | V^{(N)}(A_j) \rangle}_{=: \text{LHS}_N}
=
c_N \cdot
\underbrace{\sum_{k'} \left(\sum_q \nu_{k',q}^N\right)
  \langle V^{(N)}(B_{k_0}) | V^{(N)}(B_{k'}) \rangle}_{=: \text{RHS}_N / c_N}.
$$

**LHS asymptotic.**
- Each coefficient $\sum_q \mu_{j,q}^N$ is bounded by $r_j$ (sum of $r_j$
  unit-modulus complex numbers).
- Each inner product $\langle V^{(N)}(B_{k_0}) | V^{(N)}(A_j) \rangle \to 0$
  by hypothesis.
- Bounded × $\to 0$ $\Rightarrow 0$.
- Sum of finitely many ($g_a$) such terms tends to $0$.
- So $\mathrm{LHS}_N \to 0$.

**RHS asymptotic.**
- By Lemma A.2 (per-pair dichotomy) applied to BNT blocks of $B$ that are
  *not* phase-equivalent (BNT minimality, Proposition `prop:char-BNT`(ii)),
  $\langle V^{(N)}(B_{k_0}) | V^{(N)}(B_{k'}) \rangle \to 0$ for $k' \ne k_0$.
- For $k' = k_0$, $\langle V^{(N)}(B_{k_0}) | V^{(N)}(B_{k_0}) \rangle \to 1$
  by CF normalization (`overlap_tendsto_one`).
- So the only RHS term not vanishing in the limit is the $k' = k_0$ term:
  $\left(\sum_q \nu_{k_0,q}^N\right) \cdot \langle V^{(N)}(B_{k_0}) | V^{(N)}(B_{k_0}) \rangle$.
- For $k' \ne k_0$, the term is (bounded by $r_{k'}$) × ($\to 0$) = $\to 0$.

So $\mathrm{RHS}_N / c_N = \sum_q \nu_{k_0,q}^N + o(1)$ as $N \to \infty$.

**Closing the contradiction.**

- Boundedness of $c_N$: Take inner product of the proportionality with
  $|V^{(N)}(A)\rangle$: $\|V^{(N)}(A)\|^2 = \overline{c_N} \langle V^{(N)}(A) | V^{(N)}(B) \rangle$,
  and similarly $|V^{(N)}(B)\|^2 = \cdots$. Combined with
  $\|V^{(N)}(\cdot)\|^2 \to (\text{finite positive limit})$ from the
  multiplicity-aware BNT expansion plus pairwise BNT cross-orthogonality in
  the limit, $|c_N|$ tends to a finite positive ratio. So $c_N$ is eventually
  bounded above and below away from $0$.
- $\sum_q \nu_{k_0,q}^N$ is a finite sum (length $r_{k_0} \ge 1$) of
  $N$th-power unit-modulus complex numbers. **Key lemma (paper Lem1 /
  almost-periodicity / Lem:app\_simple):** this sequence does **not** tend
  to $0$. (At $N = 0$ it equals $r_{k_0} \ge 1$; by almost-periodicity, the
  sequence has $\limsup_N |\sum_q \nu_{k_0,q}^N| \ge r_{k_0}/\sqrt{r_{k_0}} > 0$
  via Bohr-Bochner. Alternatively the paper's Corollary `Lem1` applied to
  the BNT family of $B$ yields the same conclusion.)
- Therefore $c_N \cdot \mathrm{RHS}_N / c_N = \mathrm{RHS}_N$ does **not**
  tend to $0$. But $\mathrm{LHS}_N \to 0$. Contradiction.

**Where combined-family LI would have entered — and doesn't here.** The
above projection uses:

- Per-tensor BNT cross-overlap decay on the $B$ side (consequence of the
  paper's BNT minimality + Lemma A.2): supplied by `IsCanonicalFormBNT`
  / `IsCanonicalFormBNT.toIsCanonicalForm` plus
  `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left` from
  `NondecayingPartnerUnique`.
- Per-tensor BNT self-overlap convergence on the $B$ side: supplied by
  `IsCanonicalForm.overlap_tendsto_one` / `HasNormalizedSelfOverlap`.
- Non-decay of $\sum_q \nu_{k_0,q}^N$: paper's Corollary `Lem1` (the
  Vandermonde-style algebraic fact); already partly in
  `TNLean/Wielandt/...` and `ScalarPowerSumIdentity` modules (cf.
  `docs/paper-gaps/ft_one_copy_scope_restriction.tex`); also derivable
  directly from Lemma A.2 applied within the $B$-BNT.
- Boundedness of $c_N$: derivable from the multiplicity-aware BNT expansion
  plus pairwise orthogonality of BNT MPV families in the limit.

**No combined-family ($A \cup B$) LI is invoked.** No combined residual-family
LI is invoked. The argument is fully one-sided in its LI usage, exactly as the
analysis memo §4.3 catalogues.

### What this means for the discharge plan

The discharge-plan audit chose **Plan A** (leading-only induction with an
exactness sub-lemma) because **Plan B** (direct per-block projection) is
"mathematically **inadequate** in the restricted surface for $k_0 \neq 0$"
(discharge plan §5.4). The qualifier *in the restricted surface* is the
crucial caveat: in the **paper's** unrestricted surface, **Plan B works** for
arbitrary $k_0$, exactly as the analysis memo §6 recommends and as §10's
algebra above confirms.

So the correct path forward is **definitional refactor first, then Plan B**:

1. Migrate the proportional-FT chain off `IsCanonicalFormBNT` and onto
   `SectorDecomposition` + `HasBNTSectorData` (or a relaxed
   `IsCanonicalFormBNT` with multiplicity).
2. In the multiplicity-aware setting, prove the per-block projection of
   CPSV16 Step 1 directly for arbitrary $k_0$ (Plan B from the discharge
   plan; analysis memo §6.1).
3. Retire `_phase_sum_li`, `_phase_sum_li_left`, and
   `selected_*_residual_span` as unused dead code.
4. Retire `fixed_*_all_overlaps_decay_false_*` `sorry`s — they are subsumed
   by the new direct per-block lemma.

If a full refactor is too expensive, **Plan A still works** as a
within-restricted-surface route, but the right-shaped fix is the refactor:
the obstruction is definitional, not mathematical.

---

## 11. References

- **Source paper (primary):** Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and Boundary
  Theories*, Ann. Phys. **378**, 100 (2017); arXiv:1606.00608v4 (CPSV16).
  Pertinent: §II (CF, BNT, biCF, Theorem `thm1`, Corollary `II_cor2`, Corollary
  `thm:Fundamental-CFII`); Appendix A (CFII definition, Lemma `equalMPS`,
  Corollary `eqV`, Corollary `Lem1`, Lemma `Lem:app_simple`, proof of Theorem
  `thm1`).
  Local copy: `Papers/1606.00608/MPDO-22-12-17-2.tex`.
- **Cross-reference:** Cirac, Pérez-García, Schuch, Verstraete, *Matrix product
  states and projected entangled pair states*, Rev. Mod. Phys. **93**, 045003
  (2021); arXiv:2011.12127. Section IV.A.4, Theorem IV.4.
- **Cross-reference:** Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product
  State Representations*, Quantum Inf. Comput. **7** (2007); quant-ph/0608197.
  PGVWC07 canonical-form conventions.
- **Internal:** `blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md`
  (analysis memo); `audits/2026-05-13_cpsv16_ft_paper_vs_code_structural_map.md`
  (paper-vs-code structural map);
  `audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md` (discharge plan);
  `docs/paper-gaps/ft_one_copy_scope_restriction.tex` (scope restriction).
- **Code:**
  - `TNLean/MPS/BNT/Construction.lean` (`IsCanonicalFormBNT`,
    `IsNormalCanonicalFormBNT`, `BlockPermutationGaugePhaseConclusion`).
  - `TNLean/MPS/BNT/Basic.lean` (`IsBNT`).
  - `TNLean/PiAlgebra/CanonicalFormSepAux.lean` (`IsCanonicalForm`,
    `IsNormalCanonicalForm`, `HasInjectiveBlocks`, `IsLeftCanonicalBlockFamily`,
    `HasNormalizedSelfOverlap`, `HasStrictOrderedNonzeroWeights`).
  - `TNLean/MPS/Defs.lean` (`mpv`, `GaugeEquiv`, `SameMPV₂`,
    `ProportionalMPV₂`, `NonzeroProportionalMPV₂`,
    `EventuallyNonzeroProportionalMPV₂`, `GaugePhaseEquiv`, `IsNormal`,
    `IsNBlkInjective`).
  - `TNLean/MPS/Overlap/Basic.lean` (`MPVSpace`, `mpvState`, `mpvInner`,
    `mpvOverlap`).
  - `TNLean/MPS/SharedInfra/BlockAssembly.lean` (`toTensorFromBlocks`).
  - `TNLean/MPS/SharedInfra/SectorDecomposition.lean` (`SectorDecomposition`,
    `SectorWeightData.coeff`).
  - `TNLean/MPS/CanonicalForm/Reduction.lean` (`IsIrreducibleTensor`).
  - `TNLean/Channel/Peripheral/Spectrum.lean` (`IsPrimitive` on channels).
  - `TNLean/Wielandt/Primitivity/PaperDefinitions.lean` (`IsPrimitivePaper`).
  - `TNLean/MPS/FundamentalTheorem/Full/` (the proportional FT chain).
