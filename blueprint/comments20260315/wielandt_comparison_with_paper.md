
# Wielandt Paper [SPGWC10] — Consolidated Comparison with Blueprint v1 and v2

## 0. Preliminary: Equivalence of Definitions

The paper's three equivalent notions of primitivity ([SPGWC10, Proposition 3]):

- **(a) Primitive**: ∃n such that H_n(A,φ) = ℂ^D for all φ (every output has full
  rank after n applications).
- **(b) Eventually full Kraus rank**: ∃n such that S_n(A) = M_D(ℂ).
- **(c) Strongly irreducible**: unique eigenvalue of modulus 1, with PD
  eigenvector.

The paper's "normal tensor" ([CPGSV21, Definition IV.1]; [Cirac MPDO fixed
points, Definition 2.2]) is defined as condition (c): the transfer operator is a
primitive channel. This is equivalent to: no nontrivial invariant subspaces
(irreducible) AND no periodic eigenvalues (peripheral spectrum = {1}).

The blueprint's Definition 2.19 defines "normal" as condition (b): ∃L₀ such that
S_{L₀}(A) = M_D(ℂ).

**These are equivalent** by Proposition 3 of [SPGWC10]. The blueprint's algebraic
definition and the paper's spectral definition describe the same class of
tensors. The cumulative spanning condition T_N(A) = M_D(ℂ) is strictly weaker
(it corresponds to irreducibility, which allows periodicity).

---

## 1. Structure of the Proof in [SPGWC10]

The paper proves bounds on the Kraus spanning index i(A) — the smallest n such
that S_n(A) = M_D(ℂ) — for a primitive channel E_A with D×D matrices and d
Kraus operators.

### Step 1: Lemma 1 — nonzero trace product

**Input**: Primitive channel E_A.
**Method**: Define cumulative span T_n(A) = Σ_{m≤n} S_m(A). Show dim T_{n+1} >
dim T_n whenever T_n ≠ M_D, because stabilisation contradicts primitivity. Since
dim T_1 = d, this gives T_{D²-d+1} = M_D. Therefore 𝟙 is a linear combination of
word products of lengths ≤ D²-d+1, so at least one word product has nonzero
trace.
**Output**: ∃ word w with |w| ≤ D²-d+1 and tr(A_w) ≠ 0.

### Step 2: Lemma 2(a) — eigenvector spreading

**Input**: A single Kraus operator A₁ (or word product) with eigenvector
A₁|φ⟩ = μ|φ⟩, μ ≠ 0.
**Method**: Define K_n(A,φ) = span{A_w|φ⟩ : |w| ≤ n}. Same dimension-growth
argument: dim K_n < D ⟹ dim K_{n+1} > dim K_n, since stabilisation contradicts
primitivity. So K_{D-1} = ℂ^D.
**Padding trick** (Eq. 4): Any word of length k_n ≤ D-1 can be padded to exact
length D-1 by appending copies of the eigenvector index, since A₁^m|φ⟩ =
μ^m|φ⟩. So K_n = H_n (cumulative = fixed-length vector span).
**Output**: H_{D-1}(A,φ) = ℂ^D.

### Step 3: Lemma 2(b) — rank-one extraction

**Input**: A₁ with eigenvector φ, A₁ not invertible.
**Method**: Jordan decomposition of A₁.
- Let P be the (non-Hermitian) projector onto the nonzero-eigenvalue Jordan
  blocks (size D̃ × D̃).
- Let r = size of the largest zero-eigenvalue Jordan block.
- Key properties: A₁P = PA₁, A₁^r = A₁^r P.
- Define rectangular span R_n(A) = P · S_n(A) ⊆ M_{D̃×D}(ℂ).
- Since A₁ is invertible on range(P), left-multiplication by A₁ preserves
  linear independence in R_n, so dim R_{n+1} ≥ dim R_n.
- Primitivity forces dim R_n to keep growing until R_{D̃D} = P · M_D(ℂ).
- For any |ψ⟩: ∃A ∈ S_{D̃D} with PA = |φ⟩⟨ψ|.
- Then |φ⟩⟨ψ| = A₁^r · PA / μ^r = A₁^r · A / μ^r ∈ S_{D̃D+r}.
- Bound: D̃D + r ≤ D² - D + 1 (using D̃ ≤ D - r, r ≥ 1).
**Output**: |φ⟩⟨ψ| ∈ S_{D²-D+1}(A) for ALL |ψ⟩.

### Step 4: Assembly (Theorem 1)

**Case 3** (S₁ contains element with nonzero eigenvalue):
- Lemma 2(a): H_{D-1}(A,φ) = ℂ^D (all column directions from φ).
- Lemma 2(b): |φ⟩⟨ψ| ∈ S_{D²-D+1} for all ψ (all rank-one operators from φ).
- Combining: for any basis vector e_j, there exists M_j ∈ S_{D-1} with M_j φ = e_j
  (from column spanning). And |φ⟩⟨e_j| ∈ S_{D²-D+1}. Product: E_{ij} = M_i·|φ⟩⟨e_j|
  ∈ S_{D²}. So S_{D²} = M_D.

**Case 1** (general):
- Block to E^n for n ≤ D²-d+1 (Lemma 1) to get a Kraus operator with
  nonzero eigenvalue. Apply Case 3 to the blocked channel.
- Gives i(A) ≤ (D²-d+1)D².

**Case 2** (S₁ contains invertible element):
- Direct dimension-growth argument on S_n gives i(A) ≤ D²-d+1.

---

## 2. Comparison with Blueprint v2

### Notation mapping

| Paper                    | Blueprint v2            |
|--------------------------|-------------------------|
| S_n(A) (word span)       | S_n(A) (Def 7.1)        |
| T_n(A) (cumulative span) | T_n(A) (Def 7.2)        |
| H_n(A,φ) (fixed-len vec) | H_n(A,φ) (Def 7.25)     |
| K_n(A,φ) (cumul vec)     | K_n(A,φ) (Def 7.16)     |
| Primitive / normal        | Normal (Def 2.19)        |
| Jordan decomposition      | Fitting decomposition    |
| i(A) (Kraus spanning idx) | Not named explicitly     |

### What matches faithfully

**Lemma 1 ↔ §7.1–7.3 (Theorems 7.5–7.13).**
The cumulative-span stabilisation argument is reproduced faithfully. The
blueprint proves T_{D²}(A) = M_D (without tracking the Kraus rank d for the
sharper D²-d+1 bound). This is explicitly noted in Remark 7.24.

**Lemma 2(a) ↔ §7.4–7.5 (Theorems 7.14–7.19) + §7.7 (Lemma 7.27).**
Eigenvector extraction, cumulative vector spanning, and the padding trick
(K_n = H_n) are faithfully reproduced. The padding argument in Lemma 7.27 matches
Eq. (4) of the paper exactly.

**Proposition 3 (equivalence of primitivity notions) ↔ §7.10 + Chapter 8.**
The equivalence is split across chapters: (b)⟹(a) is Proposition 1 / Theorem
7.23; (a)⟹(c) uses the Perron–Frobenius and spectral theory of Chapters 4–5;
(c)⟹(b) uses the Burnside bridge (§8.4.1) plus the aperiodicity results
(§7.11). This factoring is appropriate for formalization.

### Key deviations

#### Deviation 1: Hypothesis stated as "normal" (Def 2.19) rather than "primitive"

The paper assumes primitivity (strongly irreducible channel). The blueprint
assumes normality (eventually full Kraus rank). Since these are equivalent by
Proposition 3, this is not a mathematical deviation — it is a choice of which
equivalent characterization to take as the starting point. For formalization,
starting from the algebraic condition (b) is natural since it directly provides
the spanning hypothesis needed by the Wielandt arguments.

**Verdict**: Correct, no issue. ✔

#### Deviation 2: Lemma 2(b) — different proof strategy for rank-one extraction

This is the most significant deviation between the paper and the blueprint.

**Paper's approach**: Uses the Jordan normal form of A₁ to identify the invertible
part (nonzero-eigenvalue Jordan blocks) and the nilpotent part. Defines the
rectangular span R_n = P · S_n and shows it grows until R_{D̃D} = P · M_D by the
same dimension-growth-or-primitivity-contradiction argument. Then uses the
identity A₁^r = A₁^r P to produce |φ⟩⟨ψ| for ALL |ψ⟩.

**Blueprint's approach** (Theorem 7.35): Uses the Fitting decomposition
(generalized eigenspaces) instead of the Jordan form. Blocks the tensor to
A^{[N₀]} where S_{N₀}(A) = M_D. Extracts column eigenvector φ and row (transpose)
eigenvector ψ from separate Kraus operators of the blocked tensor. Produces ONE
rank-one element φψ^T ∈ S_{2D}(A^{[N₀]}) via the Fitting projections P = (B_{j₀})^D
and Q = (B_{k₀})^D.

**Key differences**:

1. The paper produces |φ⟩⟨ψ| for ALL ψ via the rectangular span R_n. The
   blueprint produces φψ^T for ONE specific ψ (a transpose eigenvector).

2. The paper's Lemma 2(b) is self-contained (given A₁ with nonzero eigenvalue).
   The blueprint's Theorem 7.35 additionally requires S_{N₀}(A) = M_D as input
   (normality at a specific length), because it works on the blocked tensor.

3. The paper uses the Jordan form (non-Hermitian projector P, invertibility of
   A₁ on range(P)). The blueprint uses the Fitting decomposition (generalized
   eigenspaces, nilpotent power bound).

**How does one rank-one element suffice?** The assembly step (Theorem 7.34) uses:
- Column eigenvector spreading: H_{D-1}(B, φ) = ℂ^D (from Lemma 2(a) applied to
  the blocked tensor).
- Row eigenvector spreading: transpose spreading for ψ gives the row directions.
- The rank-one element φψ^T, combined with the row and column directions,
  recovers all rank-one operators |φ⟩⟨e_j| needed for the assembly.

The mechanism is: from φψ^T ∈ S_m(B), multiply on the right by matrices from
S_{D-1}(B) that map ψ to the various basis vectors e_j (these exist because the
transpose eigenvector spreads to all of ℂ^D). This gives |φ⟩⟨e_j| ∈ S_{m+D-1}(B).
Combined with the column spreading H_{D-1}(B,φ) = ℂ^D, the assembly theorem
(Theorem 7.28) yields S_{n+m}(B) = M_D.

**However**, there is a subtlety: the "multiply on the right" step requires that
the matrices mapping ψ to e_j lie in some S_k(B). This comes from transpose
eigenvector spreading for the blocked tensor B = A^{[N₀]}, which gives
H_{D-1}(B^T, ψ) = ℂ^D. The transpose word span S_k(B^T) is NOT the same as
S_k(B) in general (the transpose of a word product A_{w₁}...A_{w_k} is
A_{w_k}^T...A_{w₁}^T, which reverses the order). So the claim that right-
multiplication by elements of S_k(B) maps ψ to arbitrary vectors requires care.

The actual mechanism in Theorem 7.28 is different: it requires
|φ⟩⟨e_j| ∈ S_m(A) for each j, and the column spanning H_n = ℂ^D. The rank-one
operators |φ⟩⟨e_j| come from the rank-one element φψ^T combined with matrices
that "rotate" ψ into the various e_j directions. These rotations need to come
from the word span, and the mechanism for this is the key step that's compressed
in the blueprint.

**Verdict**: The blueprint's approach is correct in principle but the proof of
Theorem 7.35 is the most compressed step in the entire blueprint. The connection
between "one rank-one element" and "all rank-one operators |φ⟩⟨e_j|" needs to be
made explicit. The paper's approach is more direct (it produces ALL rank-one
operators from φ via the rectangular span), while the blueprint takes a more
indirect route through blocking and transpose eigenvectors.

#### Deviation 3: Fitting decomposition replaces Jordan normal form

The paper uses the Jordan normal form throughout: decomposing A₁ into Jordan
blocks, identifying the invertible part P, using A₁^r = A₁^r P. The blueprint
uses generalized eigenspaces (Fitting decomposition) as a substitute, since
Mathlib may not have the full Jordan form.

The Fitting decomposition provides:
- Decomposition into nilpotent part (generalized 0-eigenspace) and invertible
  part (nonzero generalized eigenspaces).
- Nilpotent power bound: f^n = 0 on n-dimensional nilpotent part.
- The projections onto the eigenspaces.

This gives essentially the same structural information as the Jordan form for the
purposes of the Wielandt argument. The specific Jordan block size r (used in
the paper's D̃D + r bound) is replaced by the nilpotent power bound D in the
blueprint's S_{2D} estimate.

**Verdict**: Correct and pragmatic formalization choice. The resulting bounds are
weaker (2D instead of D̃D + r ≤ D² - D + 1) but the qualitative result is the
same. ✔

#### Deviation 4: Weaker quantitative bounds

| Result | Paper bound | Blueprint bound |
|--------|-------------|-----------------|
| Cumulative span | T_{D²-d+1} = M_D | T_{D²} = M_D |
| Nonzero trace word | |w| ≤ D²-d+1 | |w| ≤ D² |
| Rank-one extraction | S_{D²-D+1} | S_{2D}(A^{[N₀]}) |
| Full spanning (general) | i(A) ≤ (D²-d+1)D² | ∃N: S_N = M_D (no explicit bound) |
| Full spanning (case 3) | i(A) ≤ D² | ∃N: S_N = M_D (no explicit bound) |

The blueprint does not track the Kraus rank d and does not aim for optimal
bounds. Remark 7.24 explicitly acknowledges this.

**Verdict**: Acceptable scope limitation. ✔

#### Deviation 5: Proof of Theorem 7.31 (blocking preserves normality)

The blueprint claims: if A is normal and L > 0, then A^{[L]} is also normal.

The proof says: "If S_N(A) = M_D(ℂ) then S_{NL}(A) = M_D(ℂ) (padding by
repeated single-letter words). By Lemma 7.32, S_{NL}(A) ⊆ S_N(A^{[L]}), so
S_N(A^{[L]}) = M_D(ℂ)."

The intermediate step "S_N(A) = M_D ⟹ S_{NL}(A) = M_D" is claimed via "padding
by repeated single-letter words." This needs care.

Since S_N(A) = M_D(ℂ) and A is normal (= primitive channel), the equivalence
(b)⟺(c) tells us the channel is strongly irreducible. By [SPGWC10, Proposition
3], S_n(A) = M_D for all n ≥ i(A). In particular S_{NL}(A) = M_D for NL ≥ i(A).
Since S_N = M_D means N ≥ i(A), and NL ≥ N ≥ i(A), we get S_{NL} = M_D.

So the claim is correct, but the justification "padding by repeated single-letter
words" is misleading. The correct justification is that once S_n = M_D for some
n, it holds for all larger n (by primitivity / the equivalence theorem). The
one-line proof sketch should be replaced by this cleaner argument.

**Verdict**: Theorem correct; proof sketch needs minor repair. ⚠️

---

## 3. v1 → v2 Changes Relevant to the Wielandt Chapter

### Lemma 2(b) gap: CLOSED in v2

v1 explicitly noted (Remark 7.29/7.36 in v1 numbering) that the rank-one
extraction step was incomplete. v2 closes this via Theorem 7.35 (rank-one
extraction) and Theorem 7.36 (fully unconditional Lemma 2(b)).

### DS gauge → TP gauge: FIXED in v2

v1's primitivity definition bundled DS-gauge normalization. v2's Definition 7.38
uses TP normalization only, consistent with the Chapters 4–6 corrections.

### Remark 7.41 (v1) → Remark 7.44 (v2): definition mismatch

The observation that the spectral-gap primitivity condition without ρ > 0 does
not imply irreducibility is preserved. The counterexample (D=2, ρ=diag(1,0)) is
retained. This is a correct warning about the Lean definition being weaker than
the paper's notion.

---

## 4. Summary of Issues

### Resolved from v1 to v2

1. Lemma 2(b) rank-one extraction gap: closed.
2. DS gauge assumption: eliminated.
3. Missing proof expansions: several proofs are now more detailed.

### Remaining issues in v2

1. **Theorem 7.31 proof sketch** ("padding by single-letter words") is misleading.
   The correct argument uses the fact that S_n = M_D for all n ≥ i(A) once
   primitivity is established. Should be rephrased.

2. **Theorem 7.35 proof** (rank-one extraction via Fitting decomposition) is the
   most compressed step. The mechanism by which one rank-one element φψ^T
   suffices to recover all rank-one operators |φ⟩⟨e_j| should be expanded. The
   paper avoids this issue entirely by producing ALL rank-one operators |φ⟩⟨ψ|
   directly.

3. **Theorem 7.14 proof** should clarify that the Fitting decomposition gives
   generalized eigenvectors, and an additional step is needed to extract actual
   eigenvectors.

4. **Forward dependency**: Theorem 7.52 cites Chapter 8's Burnside bridge
   (Theorems 8.20–8.21). This creates a presentation-level circular dependency
   between Chapters 7 and 8 (though the mathematical dependency is acyclic).

5. **Quantitative bounds** are not tracked. This is explicitly acknowledged and
   acceptable.

### No mathematical errors detected

The blueprint's Chapter 7 correctly reproduces the logical content of [SPGWC10]
for the results it claims. The deviations are: weaker bounds (acceptable),
different proof technique for Lemma 2(b) (correct but compressed), and
Fitting decomposition replacing Jordan form (pragmatic formalization choice).
