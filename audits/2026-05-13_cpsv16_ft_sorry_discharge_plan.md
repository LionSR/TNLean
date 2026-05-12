# CPSV16 Proportional FT: Discharge Plan for the Two Fixed-Block Sorries

**Date:** 2026-05-13  
**Status:** Plausibility study (read‑only)  
**Scope:** `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean` lines 912–913, 949–950

---

## 0. Context and Ground Truths

Before analyzing the two plans, we must register two immutable facts
established by the background documents.

### 0.1 The analysis memo

`blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md` (Section 4.3)
concludes that the CPSV16 proof of the Fundamental Theorem uses **only**
per‑tensor BNT facts—never combined‑family linear independence of  
$\{V^{(N)}(A_j)\} \cup \{V^{(N)}(B_k)\}$.  
The paper's Step 1 is a one‑shot per‑block existence argument driven by
inner‑product projection, not a peel‑induction. Any helper lemma requiring
combined‑family LI is asking for strictly more than the paper needs.

### 0.2 The scope restriction

`TNLean/MPS/BNT/Construction.lean` lines 96–98 document the
*surface* on which all downstream FT theorems live:

> **Scope restriction (one‑copy‑per‑sector):** `mu_strict_anti` forces
> $r_j = 1$; all downstream FT theorems are restricted to this special case.

Concretely:
- $\|\mu_0\| = 1$ (line 204) by the BNT normalization.
- $k > 0 \implies \|\mu_k\| < 1$ (from `mu_strict_anti : StrictAnti (‖μ·‖)`).
- Non‑leading BNT blocks have **strictly decaying weights** that
  geometrically kill their MPV state norm as $N \to \infty$.

This is *not* true in the general CPSV16 BNT where each sector carries a
multiplicity $r_j$ and the BNT expansion coefficients are
$\sum_{q=1}^{r_j} \nu_{j,q}^N$—sums of unit‑modulus complex numbers that
do **not** tend to zero. The scope restriction makes non‑leading blocks
invisible at asymptotic length, which breaks the inner‑product projection
argument the paper uses for arbitrary $k_0$.

---

## 1. The Two Sorries

File: `NondecayingOverlap.lean`

```lean
lemma fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    (A B hA hB hrA hrB hProp k₀ : Fin rB) (hAllDecay : ∀ j, Tendsto (overlap (A j) (B k₀)) → 0) : False := by
  sorry

lemma fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    (A B hA hB hrA hrB hProp j₀ : Fin rA) (hAllDecay : ∀ k, Tendsto (overlap (A j₀) (B k)) → 0) : False := by
  sorry
```

**What these statements claim** (paper lines 1181–1185):  
Fix a block $B_{k_0}$ (or $A_{j_0}$). If **every** cross‑overlap with the
other family decays to zero, then the two total MPV families cannot be
eventually proportional—contradiction.

**What is already proved:**
- Leading‑block versions (`_leading_` variants, lines 827–877) dispatch
  via `dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (`ProportionalDominant.lean` line 850).
- No‑tail cases (`_finOne` variants) dispatch via coefficient extraction
  from an LI family with an empty right‑hand residual.

**What is NOT proved:** the general $k_0 \neq 0$ / $j_0 \neq 0$ case.

---

## 2. The Proved Leading‑Block Contradiction

File: `ProportionalDominant.lean`, lemma
`dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
(line 850).

### 2.1 Normalization used

The proof normalizes by the **leading weight**:
- A‑side: divide by $\mu_A(0)^N$ (the largest A‑weight, norm = 1).
- B‑side: divide by $\mu_B(0)^N$ (the largest B‑weight, also norm = 1
  after `dominant_weight_norm_eq`).

The ratio bounds are:
- $\|\mu_A(j)/\mu_A(0)\| \le 1$ for all $j$ (by `mu_antitone`),
  strictly $< 1$ for $j \neq 0$ (by `mu_strict_anti`).
- Same for B.

### 2.2 Projection target

Projects onto:
- $\langle V(A_0) \mid \cdot \rangle$ (to check B‑leading decay)
- $\langle V(B_0) \mid \cdot \rangle$ (to check A‑leading decay)

**Key:** the projection vector is the **leading block** on the *other*
side, not the fixed block $B_{k_0}$.

### 2.3 Contradiction mechanism

**(A) For the B‑leading case:** assume all $\langle A_j \mid B_0 \rangle \to 0$.

Normalized identity ($\div \mu_A(0)^N$):
$$\text{LHS} = \underbrace{\sum_j (\mu_A(j)/\mu_A(0))^N \langle B_0 \mid A_j \rangle}_{\to 0 \text{ (all } \langle B_0 \mid A_j \rangle \to 0 \text{; ratios } \le 1)}$$
$$\text{RHS} = c_N (\mu_B(0)/\mu_A(0))^N \underbrace{\sum_k (\mu_B(k)/\mu_B(0))^N \langle B_0 \mid B_k \rangle}_{\to 1 \text{ (k=0 term dominates)}}$$

The adjusted scalar $|c_N (\mu_B(0)/\mu_A(0))^N| \to 1$ (from
`exists_dominant_adjusted_scalar_tendsto_norm_one`), so RHS norm → 1.
LHS norm → 0 ⇒ contradiction.

**(B) For the A‑leading case:** symmetric, with roles swapped.

### 2.4 Why it works only for the leading block

All ratio terms $|\mu_A(j)/\mu_A(0)| \le 1$ and $|\mu_B(k)/\mu_B(0)| \le 1$.
The self‑term on the projected side has ratio exactly $1$ and inner → 1—all
other terms have inner → 0 and ratio $\le$ 1 (hence bounded).  
If we tried to project onto $V(B_{k_0})$ instead of $V(B_0)$, the ratio
$|\mu_B(k)/\mu_B(k_0)|$ for $k < k_0$ would exceed 1, destroying the
``bounded × → 0 → 0'' argument. The scope restriction's geometric weight
decay for $k_0 \neq 0$ makes the self‑term itself tend to zero
($|\mu_B(k_0)|<1$), so even the dominant term vanishes.

> **Conclusion:** the leading‑block proof **does not generalize** to
> arbitrary $k_0$ by simply changing the projection target.

---

## 3. The Equal‑MPV Induction Architecture

File: `NondecayingOverlap.lean`, lemma
`exists_nondecaying_overlap_of_sameMPV₂_CFBNT` (lines 82–623).

### 3.1 Proof structure

| Step | What | Key mechanism |
|------|------|---------------|
| A | $\|\mu_A(0)\| = \|\mu_B(0)\|$ | Normalized inner‑product identity + bounds |
| B | Dominant block contradiction | Projection onto leading block (like §2) |
| C | Dominant match $B_0 = \zeta^N A_0$ | GPE from non‑decaying overlap |
| D | $\mu_A(0) = \mu_B(0) \cdot \zeta$ | Ratio $= 1$ from $(\text{ratio})^N \cdot \text{inner} \to 1$ |
| E | Exact tail identity | $hTailState$ after subtracting dominant summands |
| F | Non‑dominant blocks via IH | Reindex tails → `Fin (r-1)`; apply IH on smaller `rA+rB` |

### 3.2 Critical ingredient for induction

Steps D–E produce an **exact** tail identity (for all $N$):

$$\sum_{j \neq 0} \mu_A(j)^N \cdot V(A_j) = \sum_{k \neq 0} \mu_B(k)^N \cdot V(B_k)$$

This is used as the `hTailReindex` argument to the recursive call (line 568,
614). The recursion requires that the tail families satisfy `SameMPV₂` and
`IsCanonicalFormBNT`—both inherited because the leading pair is *exactly*
matched, not just asymptotically.

### 3.3 What changes for the proportional case

In the proportional case the identity is:

$$\sum_j \mu_A(j)^N \cdot V(A_j) = c_N \cdot \sum_k \mu_B(k)^N \cdot V(B_k)$$

For the induction to go through, we need (eventually):

$$\sum_{j \neq 0} \mu_A(j)^N \cdot V(A_j) = c_N \cdot \sum_{k \neq 0} \mu_B(k)^N \cdot V(B_k)$$

This requires the **exact** coefficient identity:

$$\mu_A(0)^N = c_N \cdot \mu_B(0)^N \cdot \zeta^N \qquad\text{(for all sufficiently large } N\text{)}$$

Currently we only have the **asymptotic** convergence:

$$c_N \cdot (\mu_B(0) \cdot \zeta \;/\; \mu_A(0))^N \longrightarrow 1$$

(lemma `exists_dominant_phase_adjusted_scalar_tendsto_one`, line 303).

---

## 4. Plan A — Leading‑Only Induction

### 4.1 The idea

Prove exact tail proportionality after matching the leading pair, then
induct on $r_A + r_B$ exactly as the equal‑MPV proof does. The two
`sorry` lemmas are subsumed by the top‑level
`exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT`.

### 4.2 What already works

The equal‑MPV induction infrastructure (tail reindexing, `IsCanonicalFormBNT`
inheritance via `isCanonicalFormBNT_tail_succ`, the `SameMPV₂` construction
for tails) is ready. The **dominant block case** is fully proved (leading‑block
contradiction, leading‑partner identification, phase extraction, scalar
convergence).

### 4.3 The missing sub‑lemma

We need:

```lean
lemma exact_leading_coefficient_identity_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    (A B hA hB hrA hrB hProp hPhase) :
    ∀ᶠ N in atTop,
      (μA ⟨0, hrA_pos⟩) ^ N = (c N) * ((μB ⟨0, hrB_pos⟩) * ζ) ^ N := ...
```

(i.e., the asymptotic ratio → 1 upgrades to exact equality eventually.)

**Candidates to supply this:**

**(a) Discreteness + algebraic constraints.**  
The scalars $c_N$ are extracted as the unique proportionality constants at
each length $N$. If the convergence $c_N (\mu_B(0)\zeta/\mu_A(0))^N \to 1$
is strong enough (e.g., the error decays faster than any geometric sequence),
and if $c_N$ comes from a finite‑dimensional algebraic relation (the MPV
expansion in the BNT basis), one might argue that the ratio must be
identically 1 for large $N$. This requires a new lemma about the
**rate** of convergence of the adjusted scalar—not just that its norm
tends to 1, but that the complex value itself tends to 1 fast enough
that the only possible limiting values for a discrete parameter are 1.

*Complexity:* moderate (∼30–50 lines), highest‑risk sub‑lemma.

**(b) Projection + BNT‑A linear independence.**  
Use the BNT linear independence of $\{V(A_j)\}_j$ alone. Write the
proportionality identity, substitute the phase relation for $V(B_0)$,
then take inner products with each $V(A_j)$. For $j = 0$, the diagonal term
gives information about the adjusted scalar. For $j \neq 0$, the
cross‑inner‑products ``see'' both A‑off‑diagonal terms (→ 0) and B‑k
terms. With careful asymptotics, one might extract that the adjusted
ratio's deviation from 1 is forced to zero by the fact that all other
coefficients are asymptotically determined by the A‑basis.

*Complexity:* higher (∼80–120 lines). Would use
`geometric_mul_inner_tendsto_zero` and `bounded_mul_tendsto_zero` in a
systematic coefficient‑matching argument.

**(c) Normalize to equal‑MPV case.**  
Define rescaled families $\tilde A$ and $\tilde B$ whose weights are
normalized by $\mu_A(0)$. The proportionality $c_N$ is absorbed into a
new $c'_N$ that tends to 1. Then the normalized identity becomes an
``asymptotically equal‑MPV'' equation. Using the leading dominant
projection plus the LI of the A‑family, extract coefficient identities.
This essentially repeats the equal‑MPV proof at a normalized level.

*Complexity:* highest (∼150–200 lines). Essentially a full re‑proof.

### 4.4 Plan A assessment

- **Plausible:** yes, provided the sub‑lemma in §4.3 is resolved.
- **Self‑contained:** the needed new lemma is *one* statement about exact
  coefficient recovery; once proved, the rest is a mechanical clone of
  the equal‑MPV induction.
- **Source fidelity:** this deviates from the paper's one‑shot per‑block
  argument, but the paper's argument is itself unavailable in the
  restricted surface (see §0.2). An induction that handles the restricted
  case is a reasonable formalization choice.

---

## 5. Plan B — Direct Per‑Block Projection

### 5.1 What the paper does

Fix $B_{k_0}$. Assume $\langle V(B_{k_0}) \mid V(A_j) \rangle \to 0$ for
all $j$. Take the inner product of the proportionality identity with
$V(B_{k_0})$:

$$\underbrace{\sum_{k'} \bigl(\sum_q \nu_{k',q}^N\bigr) \langle B_{k_0} \mid B_{k'} \rangle}_{\text{self-term } \sim \sum_q \nu_{k_0,q}^N \;\not\to\; 0}
= \lambda_N \underbrace{\sum_j \bigl(\sum_q \mu_{j,q}^N\bigr) \langle B_{k_0} \mid A_j \rangle}_{\to\; 0}$$

The BNT coefficients $\sum_q \nu_{k_0,q}^N$ are sums of unit‑modulus
numbers → do not tend to 0. Contradiction.

### 5.2 Why it fails in the restricted surface

In the one‑copy‑per‑sector surface, $\|\mu_B(k_0)\| < 1$ for $k_0 \neq 0$.
The BNT expansion coefficient for block $B_{k_0}$ is the single scalar
$\mu_B(k_0)^N$, which **tends to zero geometrically**. The self‑term

$$\mu_B(k_0)^N \cdot \langle V(B_{k_0}) \mid V(B_{k_0}) \rangle \;\sim\; \mu_B(k_0)^N \to 0$$

no longer provides a non‑vanishing contribution. Even if the LHS → 0 and
RHS → 0, the proportionality $\lambda_N$ may be bounded—no contradiction.

Moreover, the cross‑terms from $k < k_0$ (larger weights) introduce
$|\mu_B(k)/\mu_B(k_0)| > 1$ geometric growth competing with inner‑product
exponential decay. The ``bounded × → 0 → 0'' technique from the
leading‑block proof does not apply.

### 5.3 Attempted rescue: Lemma Lem1 + coefficient extraction

The lemma `eventually_linearIndependent_all_left_single_right_…` supplies
LI of $\{V(A_j)\} \cup \{V(B_{k_0})\}$, which is valid under $hAllDecay$.

The proportionality identity can be rearranged:

$$\underbrace{\sum_j \mu_A(j)^N V(A_j) - c_N \mu_B(k_0)^N V(B_{k_0})}_{\text{in span}\{V(A_j)\} \cup \{V(B_{k_0})\}}
= \underbrace{c_N \sum_{k \neq k_0} \mu_B(k)^N V(B_k)}_{\text{in span}\{V(B_k)\}_{k\neq k_0}}$$

The residual RHS is **not** in the LI family, so coefficient extraction
via LI does **not** directly give the contradiction. The residual
$V(B_k)_{k \neq k_0}$ must be eliminated to use the LI.

For $r_B = 1$ (no‑tail case), the residual is empty → coefficient
extraction works → already proved (`_finOne`).

But for $r_B \ge 2$, the residual persists and LI alone is insufficient.

### 5.4 Plan B assessment

- **Plausible in full CPSV16 setting:** yes (the paper's proof).
- **Plausible in restricted surface:** **NO** for $k_0 \neq 0$.
  The combination of (i) geometric weight decay of non‑leading blocks
  and (ii) residual B‑terms outside the LI family blocks the direct
  projection contradiction.
- **Possible salvage:** prove that the residual tail $\sum_{k \neq k_0}$
  also projects to zero under $hAllDecay$ after some renormalization.
  This essentially reduces to Plan A's induction.

---

## 6. Dead‑Code Audit

If either plan succeeds, the following helper lemmas become dead code
because they require combined‑family LI that is never needed for the
final result:

| Lemma | File | Line | Why dead |
|-------|------|------|----------|
| `eventually_selected_weighted_mpvState_eq_smul_of_phase_sum_and_li` | `ProportionalExpansion.lean` | 376 | Requires `hLI : LinearIndependent (Sum.elim (all A) (tail B))` |
| `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li` | `ProportionalExpansion.lean` | 698 | Requires same LI hypothesis |
| `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li_left` | `ProportionalExpansionLeft.lean` | 47 | Symmetric variant |

Additionally, if `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT`
is proved by induction (Plan A), then `fixed_right_all_overlaps_decay_false_…`
and `fixed_left_all_overlaps_decay_false_…` are never called directly—they
become **internal lemmas** of the inductive proof or can be removed.

The following lemmas **remain load‑bearing** under either plan:

| Lemma | File | Role |
|-------|------|------|
| `dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `ProportionalDominant.lean:850` | Leading‑block contradiction |
| `exists_dominant_adjusted_scalar_tendsto_norm_one_…` | `ProportionalDominant.lean:536` | Scalar norm convergence |
| `exists_dominant_phase_adjusted_scalar_tendsto_one_…` | `ProportionalDominant.lean:303` | Phase‑adjusted scalar limit |
| `exists_leading_phase_tail_diff_tendsto_zero_…` | `LeadingTail.lean:47` | Leading‑erased tail asymptotic |
| `leading_right_nondecaying_partner_eq_leading_left_…` | `LeadingPartner.lean:39` | Uniqueness of leading partner |
| `exists_phase_mpvState_eq_smul_of_nondecaying_overlap_CFBNT` | `NondecayingPartnerUnique.lean` | Phase extraction from non‑decaying overlap |
| `isCanonicalFormBNT_tail_succ` / `_succAbove` | `NondecayingOverlap.lean:636,675` | Tail BNT inheritance |
| `eventually_linearIndependent_all_left_single_right_…` / `_all_right_single_left_…` | `NondecayingOverlap.lean:709,768` | Lemma Lem1 input (may be needed in exactness lemma) |
| `sum_tendsto_one_of_diag` | External (HelperLemmas?) | Dominant diagonal limit |

---

## 7. Recommendation

### 7.1 Chosen plan: Plan A — Induction with an exactness sub‑lemma

**Rationale:**

1. Plan B is mathematically **inadequate** in the restricted surface for
   $k_0 \neq 0$ (geometric weight decay kills the contradiction).
2. Plan A re‑uses the already‑proved equal‑MPV induction architecture and
   requires exactly **one new lemma** as a gateway.
3. The new lemma (§4.3) is a natural statement: upgrade an asymptotic
   convergence to an exact eventual identity. This has independent
   mathematical value.

### 7.2 Implementation roadmap

**Phase 1 — Exact leading coefficient identity (∼50–100 lines)**

Prove:
```
lemma exact_leading_coefficient_eventually_eq_... 
  (hProp : EventuallyNonzeroProportionalMPV₂ ...)
  (hPhase : ∀ N, mpvState (B b0) N = ζ^N • mpvState (A a0) N) :
  ∀ᶠ N in atTop,
    (μA a0)^N = (c N) * ((μB b0) * ζ)^N :=
```

Suggested proof strategy: use `exists_dominant_phase_adjusted_scalar_tendsto_one`
to get $c_N \cdot (\mu_B(0) \zeta / \mu_A(0))^N \to 1$. Then combine with
the BNT‑A linear independence (`hA.isBNT.eventually_li`) plus the
proportionality identity to extract that the deviation $c_N \cdot
(\mu_B(0) \zeta)^N - \mu_A(0)^N$ multiplies $V(A_0)$ and must vanish
for large $N$ because all other terms in the weighted‑sum identity are
asymptotically in the span of $\{V(A_j)\}_{j \neq 0}$ modulo a term
in the B‑span that tends to zero.

*Candidate technical ingredients:*
- `geometric_mul_inner_tendsto_zero` for cross‑terms
- `eventually_linearIndependent_all_left_single_right_…` (Lemma Lem1 input,
  which holds given the all‑overlaps‑decay hypothesis for the leading block)
- `bounded_mul_tendsto_zero` for asymptotic control

**Phase 2 — Tail identity (∼30 lines)**

Use the exact coefficient identity plus the phase relation to subtract
the dominant summand:
```
hTailState : ∀ᶠ N in atTop,
  Σ_{j≠a0} μA_j^N • V(A_j) = c_N • Σ_{k≠b0} μB_k^N • V(B_k)
```

This follows mechanically from `eventually_weighted_mpvState_tail_eq_smul_sequence_of_total_and_selected`
(already in `ProportionalExpansion.lean` line 463).

**Phase 3 — Tail proportionality (∼40 lines)**

Use `eventuallyNonzeroProportionalMPV₂_tail_succ_of_total_and_selected`
(line 568) to obtain `EventuallyNonzeroProportionalMPV₂` for the tail
families. The tail BNT inheritance is already provided by
`isCanonicalFormBNT_tail_succ`.

**Phase 4 — Induction (∼80 lines, mostly copy of equal‑MPV)**

Write `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT`
as an induction on $r_A+r_B$:
- Base: leading blocks → `exists_nondecaying_overlap_dominant_…`
- Step: for non‑dominant $j_0 \neq 0$ or $k_0 \neq 0$, apply Phase 1–3,
  reindex tails, invoke IH on smaller $r_A+r_B$.

**Phase 5 — Clean up**

- Remove or deprecate the two `sorry` lemmas (they become unused).
- Remove the dead‑code `_phase_sum_li` lemmas if confirmed unused.
- Update `NondecayingOverlap.lean` docstring.

### 7.3 Estimated total effort

∼200–300 lines of new/existing code, spread across:
- `ProportionalDominant.lean` (exactness lemma, ∼50–100)
- `NondecayingOverlap.lean` (induction, ∼100–150)
- Minor adjustments in `ProportionalExpansion.lean` (tail identity wiring, ∼30)

### 7.4 Risks

| Risk | Mitigation |
|------|------------|
| Exactness lemma requires stronger rate bounds than available | Fall back to Plan B with a re‑examination of whether weight‑decay can be circumvented using the $c_N$ renormalization; or record as an open problem in the scope‑restriction document |
| Induction termination with eventual (not exact) tail identity | Use `ihN : ∀ᶠ N` and thread `Filter.Eventually` through the induction—the equal‑MPV proof uses exact (∀ N) identities, but eventual suffices for the non‑decaying overlap conclusion |
| Dead‑code removal causes import breakage | Keep the lemmas as `deprecated` stubs redirecting to the new proof for one release cycle |

---

## 8. References

- **Source paper:** arXiv:1606.00608v4, Appendix A, pp. 29–32 (Theorem II.1 proof).
- **Blueprint analysis:** `blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md`
- **Paper‑gaps plan:** `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`
- **Scope restriction:** `docs/paper-gaps/ft_one_copy_scope_restriction.tex`
- **Equal‑MPV induction:** `NondecayingOverlap.lean:82–623`
- **Leading‑block contradiction:** `ProportionalDominant.lean:850–907`
- **Conditional tail‑peeling:** `ProportionalExpansion.lean:376–753`
