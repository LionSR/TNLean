
# Verification: Full FT Recovery from v2's Machinery

This note provides a step-by-step verification of whether v2's blueprint
can recover the full Fundamental Theorem ([CPGSV21, Corollary IV.5])
and whether the proposed bridging lemma works as claimed.

---

## 1. The Three Statements

### Literature ([CPGSV21, Corollary IV.5])

> If two tensors A and B in canonical form generate the same MPV for
> all N, then (i) the dimensions of the matrices A^i and B^i coincide,
> and (ii) there is an invertible matrix X such that A^i = XB^iX^{-1}.

This is the unconditional equal-MPV FT. No assumption on common block
structure.

### v1 (Theorem 10.13)

> Under the same hypotheses as Theorem 10.12 (two CF-BNT decompositions),
> if the MPV families are equal (not just proportional), then the
> block-diagonal tensors are gauge equivalent (not just gauge-phase
> equivalent).

v1's proof: Apply Theorem 10.12 (proportional FT) → permutation + 
gauge-phase equivalence. Then use Newton–Girard (Theorem 10.9) to show
{μ_k^A} = {μ_k^B} as multisets. Combine for global gauge equivalence.

### v2 (Theorem 11.3)

> Fix a common block structure: same r, same D_k, same μ_k. If two
> CF-BNT families on this common data generate the same MPV family,
> then each pair (A_k, B_k) is gauge equivalent, and hence the assembled
> block-diagonal tensors are gauge equivalent.

v2 assumes common block structure (including equal weights) as input.

---

## 2. Verification That v2 Is Strictly Weaker (As Written)

v2's Theorem 11.3 requires as input:
- Same number of blocks r: provided by Theorem 11.1 ✔
- Same bond dimensions D_k (after permutation): provided by Theorem 11.1 ✔
- **Same weights μ_k**: NOT provided by Theorem 11.1.

Theorem 11.1 gives gauge-phase equivalence B_{π(j)} = e^{iφ_j} X_j A_j X_j^{-1},
but does NOT output any relationship between the weights μ_j^A and μ_k^B.
The weights are part of the CF-BNT input data, not part of the conclusion.

Therefore, as written, v2 cannot chain Theorem 11.1 → Theorem 11.3 to
prove the full equal-MPV FT. The weight matching is the missing step.

**Confirmed: v2's Theorem 11.3 is strictly weaker than v1's Theorem 10.13
and [CPGSV21, Corollary IV.5] as written.**

---

## 3. Verification of the Bridging Argument

### Setup

Suppose V^{(N)}(A_tot) = V^{(N)}(B_tot) for all N (equal MPVs), where:
- A_tot = ⊕_j μ_j^A A_j (CF-BNT decomposition)
- B_tot = ⊕_k μ_k^B B_k (CF-BNT decomposition)

### Step 1: Apply Theorem 11.1 (proportional FT with c_N = 1)

Equal MPVs are a special case of proportional MPVs (c_N = 1).
Theorem 11.1 gives:
(a) r_A = r_B =: r
(b) A permutation π with D_j^A = D_{π(j)}^B
(c) Gauge-phase equivalence: B_{π(j)}^i = e^{iφ_j} X_j A_j^i X_j^{-1}

### Step 2: Weight matching from BNT linear independence

By Theorem 2.24 (MPV decomposition):

  V^{(N)}(A_tot)_σ = ∑_j (μ_j^A)^N V^{(N)}(A_j)_σ
  V^{(N)}(B_tot)_σ = ∑_k (μ_k^B)^N V^{(N)}(B_k)_σ

From gauge-phase equivalence (Step 1c):

  V^{(N)}(B_{π(j)})_σ = tr((e^{iφ_j})^N X_j A_j^{i_1}...A_j^{i_N} X_j^{-1})
                       = e^{iNφ_j} V^{(N)}(A_j)_σ

Reindex the B-sum using k = π(j):

  V^{(N)}(B_tot)_σ = ∑_j (μ_{π(j)}^B)^N · e^{iNφ_j} · V^{(N)}(A_j)_σ

Equal MPVs then give:

  ∑_j [(μ_j^A)^N − (μ_{π(j)}^B · e^{iφ_j})^N] V^{(N)}(A_j)_σ = 0
  for all N and σ.

By Theorem 10.5 (CF-BNT yields BNT), the block MPVs {V^{(N)}(A_j)} are
linearly independent for sufficiently large N. Therefore, for each j:

  (μ_j^A)^N = (μ_{π(j)}^B · e^{iφ_j})^N   for all large N.

This forces:

  μ_j^A = μ_{π(j)}^B · e^{iφ_j}   for each j.            (*)

### Step 3: Global gauge equivalence (phase absorption)

From (*) and the gauge-phase equivalence B_{π(j)}^i = e^{iφ_j} X_j A_j^i X_j^{-1}:

The j-th block of the B-side (after reindexing by π) contributes:

  μ_{π(j)}^B · B_{π(j)}^i = μ_{π(j)}^B · e^{iφ_j} · X_j A_j^i X_j^{-1}
                            = μ_j^A · X_j A_j^i X_j^{-1}        [by (*)]

Therefore:

  ⊕_j μ_{π(j)}^B B_{π(j)}^i = ⊕_j μ_j^A · X_j A_j^i X_j^{-1}
                                = (⊕_j X_j) · (⊕_j μ_j^A A_j^i) · (⊕_j X_j)^{-1}

This is: B_tot (reindexed by π) = X · A_tot · X^{-1},
where X = ⊕_j X_j (block-diagonal invertible matrix).

This is global gauge equivalence. ✔

---

## 4. Key Observations

### The bridging argument does NOT need Theorem 11.3

The full equal-MPV FT follows from Theorem 11.1 alone plus the three-step
argument above (linear independence → weight matching → phase absorption).
Theorem 11.3 (same-structure FT) is not used. This is because the phase
absorption in Step 3 simultaneously handles the weight matching and the
gauge upgrade — the phase e^{iφ_j} gets absorbed into the weight, turning
gauge-phase equivalence directly into global gauge equivalence.

### The bridging argument does NOT need Newton–Girard

The weight matching in Step 2 uses BNT linear independence (Theorem 10.5),
not Newton–Girard. This is a more elementary argument than v1's route
(which used Newton–Girard to match the weight multisets).

### Why v1 used Newton–Girard

v1's Theorem 10.12 concluded gauge-phase equivalence B_{σ(k)} ~_{gp} A_k.
From equal MPVs and the MPV decomposition (summing over σ), v1 extracted:

  ∑_k (μ_k^A)^N = ∑_k (μ_k^B)^N   for all N

(by summing V^{(N)}(A_tot)_σ = V^{(N)}(B_tot)_σ over all σ and using
orthogonality, or equivalently by taking N = 1, 2, ...). Newton–Girard
then gave multiset equality {μ_k^A} = {μ_k^B}.

This is a different (and less direct) route to the same conclusion.
The BNT linear independence approach (Step 2 above) is more efficient
because it extracts the per-block weight matching directly, rather than
going through the aggregate power sums.

### What the blueprint should do

The most natural fix is to add a single theorem after Theorem 11.1:

> **Theorem 11.X (Full equal-MPV Fundamental Theorem).** Let A_tot and
> B_tot be as in Theorem 11.1. If V^{(N)}(A_tot) = V^{(N)}(B_tot)
> for all N, then the block-diagonal tensors are gauge equivalent.
>
> *Proof.* Apply Theorem 11.1 with c_N = 1 to get r_A = r_B, a
> permutation π, and gauge-phase equivalence B_{π(j)}^i = e^{iφ_j}
> X_j A_j^i X_j^{-1}. By Theorem 10.5, the block MPVs {V^{(N)}(A_j)}
> are linearly independent for large N. Substituting the gauge-phase
> identity into the equal-MPV equation and comparing coefficients gives
> μ_j^A = μ_{π(j)}^B · e^{iφ_j}. The phase is then absorbed:
> μ_{π(j)}^B · B_{π(j)}^i = μ_j^A · X_j A_j^i X_j^{-1}, so the
> block-diagonal tensors are related by the block-diagonal gauge
> X = ⊕_j X_j (after reindexing by π).

This theorem recovers the full [CPGSV21, Corollary IV.5] using only
Theorems 11.1 and 10.5 from v2's existing machinery. Newton–Girard and
Theorem 11.3 are both unnecessary for this conclusion.

---

## 5. Revised Status of Theorems

| Theorem | Status after this analysis |
|---|---|
| Theorem 11.1 (proportional FT) | Essential ✔ |
| Theorem 11.2 (proportional FT, NT route) | Essential ✔ |
| Theorem 11.3 (same-structure equal-MPV FT) | Useful but not needed for the full FT |
| Theorem 10.5 (CF-BNT yields BNT) | Essential for the bridging argument ✔ |
| Theorem 10.7 (BNT permutation) | Essential (used by Theorem 11.1) ✔ |
| Theorems 10.11–10.12 (Newton–Girard) | Orphaned: not needed by any route |
| Theorem 10.9 (coefficient ratio decay) | Still indirectly needed for Theorem 10.7 |
| Theorem 9.15 (same-structure CF FT) | Used by Theorem 11.3, but Theorem 11.3 itself is dispensable |
