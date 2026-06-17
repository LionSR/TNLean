
# Blueprint Review — Chapter 7 (Wielandt Bound)

This review follows the protocol in `blueprint_review_protocol.md` and the
format established in the Chapter 8 review. It covers v2 of the blueprint,
identifies v1 → v2 changes, compares against the source paper [SPGWC10],
and checks cross-chapter consistency with Chapters 2–6 and 8.

---

## 1. Role of Chapter 7 in the Blueprint

Chapter 7 proves a quantum analog of Wielandt's inequality following [SPGWC10]:
for a normal MPS tensor with bond dimension D, the cumulative span of matrix
products stabilises at T_{D²}(A) = M_D(ℂ), and there exists a fixed length N with
S_N(A) = M_D(ℂ). The chapter has three logical blocks:

1. **§7.1–7.6**: Wielandt bound via cumulative span + eigenvector spreading.
   (Paper's Lemma 1 + Lemma 2(a) + assembly.)
2. **§7.7–7.8**: Fixed-length matrix spanning via rank-one extraction.
   (Paper's Lemma 2(b).)
3. **§7.9–7.11**: Primitivity–normality bridge + aperiodicity results.
   (Paper's Proposition 3, factored across chapters.)

The chapter feeds into Chapters 8–10 (canonical form reduction, block
separation, BNT theory).

---

## 2. Global Assessment

| Aspect                   | Evaluation                                          |
|--------------------------|-----------------------------------------------------|
| Mathematical correctness | Theorem statements correct; one proof bound unjustified (Thm 7.35) |
| Conceptual clarity       | Good; layered structure matches the paper            |
| Structural quality       | Good                                                |
| Cross-chapter consistency| One forward dependency on Ch8 (Burnside bridge)      |
| Literature alignment     | Faithful to [SPGWC10]; weaker bounds acknowledged    |
| Literature citations     | Several citation errors (see §4)                     |

---

## 3. v1 → v2 Changes

### What did NOT change

Contrary to an earlier assessment (which I correct here), **§7.1–7.8 are
essentially identical between v1 and v2**. The Lemma 2(b) gap closure (Theorems
7.34–7.36) was already present in v1. The theorem numbering shifted slightly
(v1's 7.27 → v2's 7.28, v1's 7.30 → v2's 7.31, etc.) but the content and proofs
are the same.

### What DID change: §7.9–7.11 (primitivity and normality)

v1 ended Chapter 7 at Theorem 7.40 + Remark 7.41 (definition mismatch), listing
two open gaps and using "DS gauge" in Theorems 7.37–7.38.

v2 adds substantial new content:

**3-A. DS gauge → TP gauge.** v1's Theorem 7.37 said "primitive MPS tensor (with
DS gauge)." v2's Definition 7.38 uses TP normalization: Σ (A^i)† A^i = 𝟙.
Consistent with the Ch4/Ch5/Ch6 corrections.

**3-B. Remark 7.41 (v1) → Remark 7.44 (v2).** The definition mismatch warning is
preserved but expanded. The counterexample (D = 2, ρ = diag(1,0)) is retained.
The chain primitive + ρ PosDef ⟹ irreducible ⟹ algSpan = M_D ⟹ normal is now
stated explicitly.

**3-C. Theorem 7.45 (NEW in v2).** Primitive + PD fixed point ⟹ irreducible
tensor. Fully expanded contrapositive proof using the convergence ℰ^n(σ) →
(tr(σ)/tr(ρ))ρ. This was listed as an open gap in v1's Remark 7.41, item 1.

**3-D. §7.11 entirely NEW in v2.** The aperiodicity bridge:
- Remark 7.46 (aperiodicity condition 𝟙 ∈ S₁(A) is explicit hypothesis)
- Remark 7.47 (counterexample: cumulative spanning ≠ normality)
- Theorems 7.48–7.53 (aperiodicity ⟹ word span monotonicity ⟹ T_n = S_n ⟹
  normality; full chain irreducible + aperiodicity ⟹ normal)
- Remark 7.54 (normal-canonical route bypasses aperiodicity bridge)

**3-E. v1's Remark 7.41, item 2 (open gap).** v1 noted: "upgrade ∃N, T_N = M_D to
fixed-length S_L = M_D requires aperiodicity input." v2 resolves this via §7.11:
Theorems 7.49–7.50 show that aperiodicity (𝟙 ∈ S₁) collapses T_n to S_n, giving
the upgrade.

### Correction to my earlier review

In the earlier review process I stated that "the most important v1→v2 achievement
is the closure of the Lemma 2(b) gap." This was wrong. The Lemma 2(b) closure
(Theorems 7.34–7.36, Remark 7.36) was already present in v1. The actual v1→v2
changes are concentrated in §7.9–7.11: the primitivity–normality bridge, the
expanded proof of Theorem 7.45, and the entire aperiodicity section.

---

## 4. Statement-by-Statement Review

### Section 7.1 — Cumulative span

**Definition 7.1 (Word span).** S_n(A) = span{A^w : |w| = n}.
Correct.

⚠️ **Citation error.** The blueprint says "This is [SPGWC10, Eq. (1)]." But
Eq. (1) of [SPGWC10] is the channel definition E_A(X) = Σ A_k X A_k†. The word
span S_n(A) is introduced in §II of the paper, in the paragraph after Eq. (1),
without a numbered equation. The citation should be "[SPGWC10, §II]."

**Paper comparison**: S_n(A) matches the paper's notation exactly.

**Definition 7.2 (Cumulative span).** T_n(A) = S_0 + S_1 + ⋯ + S_n.
Correct. The paper uses R_n in Lemma 1 for this; the blueprint's T_n notation
is cleaner.

**Paper comparison**: T_n corresponds to R_n in the paper's Lemma 1 proof. The
paper denotes it R_n = "the span of all S_m with m ≤ n." Same object, different
letter.

**Lemma 7.3 (Monotonicity).** Correct.

**Lemma 7.4 (Dimension bound).** dim T_n ≤ D². Correct.

**Theorem 7.5 (Stabilisation).** T_n = T_{n+1} ⟹ T_m = T_n for all m ≥ n.
Correct. Matches the paper's (*) argument in Lemma 1.

**Theorem 7.6 (Dimension growth).** T_n ≠ T_{n+1} ⟹ dim T_{n+1} > dim T_n.
Correct. Same logic as the paper.

**Lemma 7.7 (Word span = block injectivity).** S_L = M_D ↔ L-block injective.
Correct. Links to Definition 2.18 in Chapter 2.

**Paper comparison**: Not stated as a separate lemma in the paper; it's implicit
in the definition of eventually full Kraus rank (property (b) in §II).

### Section 7.2 — Fitting decomposition

**Definition 7.8 (Fitting decomposition).** Lists four properties of the
generalized eigenspace decomposition.

⚠️ **Terminology stretch.** The classical "Fitting decomposition" is V = ker(f^n)
⊕ im(f^n), which is the decomposition into the nilpotent part and the
automorphic part. The blueprint uses the term for the full generalized eigenspace
decomposition. This is harmless for formalization (Mathlib likely uses
generalized eigenspaces) but slightly nonstandard.

**Theorem 7.9 (Exists).** Correct.

**Paper comparison**: The paper uses the Jordan normal form directly ([SPGWC10,
Lemma 2(b)] explicitly writes "We write A₁ in the Jordan standard form"). The
blueprint substitutes generalized eigenspaces. This is the main technical
deviation from the paper's proof method — see §6 below.

**Theorem 7.10 (Nilpotent power bound).** f^n = 0 on n-dimensional nilpotent
space. Correct and standard.

### Section 7.3 — Nonzero trace product

**Theorem 7.11 (T_n reaches M_D — explicit bound).** If A is normal, ∃n ≤ D²
with T_n = M_D. Correct.

**Paper comparison**: The paper's Lemma 1 gives the sharper bound n ≤ D² − d + 1,
tracking the Kraus rank d = dim S₁(A). The blueprint uses dim T_0 = 1 (since
S_0 = span{𝟙}) rather than dim T_1 = d, yielding the weaker D² bound. This is
explicitly acknowledged in Remark 7.24.

⚠️ **Subtle point**: the paper's Lemma 1 starts with dim R₁ = d (= dim S₁), but
the blueprint's cumulative span T_0 = S_0 = span{𝟙} has dimension 1. Then T_1 =
S_0 + S_1, which has dimension ≤ 1 + d. The dimension-growth argument gives at
most D² − 1 strict increases from dim T_0 = 1, yielding T_{D²} = M_D. The paper
gets D² − d strict increases from dim R₁ = d. The blueprint's bound is correct
but weaker.

**Theorem 7.12 (T_{D²} = M_D).** Correct corollary.

**Theorem 7.13 (Nonzero trace product).** ∃w with |w| ≤ D² and tr(A^w) ≠ 0.
Correct. Matches [SPGWC10, Lemma 1].

⚠️ Requires D ≥ 1 (since tr(𝟙) = D). Not stated. Harmless since normality for
D = 0 is vacuous.

⚠️ **Citation check.** The blueprint says "This is [SPGWC10, Lemma 1]." Correct.

### Section 7.4 — Eigenvector extraction

**Theorem 7.14 (Nonzero trace ⟹ eigenvector).** Correct.

⚠️ The proof says "the Fitting decomposition ensures the corresponding
generalized eigenspace is nontrivial, yielding an eigenvector." Strictly, the
Fitting decomposition gives a generalized eigenvector. Over ℂ, every
endomorphism has (genuine) eigenvectors, so the conclusion holds, but the
mechanism is: nonzero eigenvalue μ ⟹ generalized μ-eigenspace is nontrivial ⟹
the restriction of M to this space has eigenvalue μ ⟹ there exists a genuine
eigenvector. The proof is correct but the intermediate step could be more
explicit.

**Theorem 7.15 (Eigenvalue extraction).** Correct. Combines 7.13 and 7.14.

**Paper comparison**: Matches the paper's argument between Lemma 1 and Lemma 2.

### Section 7.5 — Eigenvector spreading

**Definition 7.16 (Cumulative vector span).** K_n(A, φ) = span{A^w φ : |w| ≤ n}.
Correct.

⚠️ **Citation.** Says "This is [SPGWC10, proof of Lemma 2(a)]." The cumulative
vector span is defined there as "S_n" (different from the matrix word span also
called S_n). The paper defines K_n in the proof text, not as a numbered equation.
The citation is acceptable but could be more precise.

**Theorem 7.17 (Stabilisation).** Correct. Same argument as Theorem 7.5.

**Lemma 7.18 (Vector span from matrix span).** If T_N = M_D and φ ≠ 0, then
K_N(A, φ) = ℂ^D. Correct.

**Theorem 7.19 (Eigenvector spreading).** If A^{i₀} φ = μφ with μ ≠ 0, then
K_{D-1}(A, φ) = ℂ^D. Correct. This is [SPGWC10, Lemma 2(a)].

⚠️ **Citation check.** Says "This is [SPGWC10, Lemma 2(a)]." Correct.

**Paper comparison**: The proof matches the paper line by line. The dimension-
growth-or-stabilisation argument in ℂ^D (dimension D rather than D²) is
identical.

⚠️ **Application note**: The theorem requires A^{i₀} φ = μφ with i₀ a single
physical index. But Theorem 7.15 produces A^{w₀} φ = μφ with w₀ a word. The
resolution is blocking: A^{w₀} becomes a single Kraus operator (A^{[L]})_{j₀} of
the blocked tensor. This is handled by Theorem 7.33.

### Section 7.6 — Assembly

**Definition 7.20 (Wielandt analysis).** Correct packaging.

**Theorems 7.21–7.23.** All correct. The Wielandt bound T_{D²} = M_D follows.

**Theorem 7.23.** Says "This is [SPGWC10, Theorem 1]." This is approximately
correct — the paper's Theorem 1 gives quantitative bounds on i(A), while the
blueprint's Theorem 7.23 gives only the cumulative-span result T_{D²} = M_D,
which is a weaker statement. The fixed-length result (∃N: S_N = M_D) is
Theorem 7.36.

**Remark 7.24 (Blocking-length estimates).** Honestly notes that the sharper
bounds D⁴ for injectivity and 3D⁵ for bi-canonical form are not proved.

### Section 7.7 — Lemma 2(b): fixed-length matrix spanning

**Definition 7.25 (Fixed-length vector span).** H_n(A, φ) = span{A^w φ : |w| = n}.
Correct.

⚠️ Says "This is S_n(A)|φ⟩ in the notation of [SPGWC10]." In the paper, H_n is
defined in §II as "H_n(A, φ) := S_n(A)|φ⟩." This is correct, but note that the
paper uses H_n as a primary object (defined in §II before the proofs), while the
blueprint defines it only in §7.7 after already using K_n extensively. This is a
structural rearrangement, not an error.

**Lemma 7.26 (Word span products).** S_m · S_n ⊆ S_{m+n}. Correct.

**Lemma 7.27 (Eigenvector padding).** K_n = H_n if A^{i₀} φ = μφ. Correct.

**Paper comparison**: Matches Eq. (4) of [SPGWC10] exactly. The padding trick is:
any word of length k ≤ n is padded to length n by appending n − k copies of i₀,
using A^{i₀^m} φ = μ^m φ.

**Theorem 7.28 (Assembly step).** If H_n = ℂ^D and |φ⟩⟨e_j| ∈ S_m for each j,
then S_{n+m} = M_D. Correct.

**Paper comparison**: This corresponds to the assembly step in the proof of
[SPGWC10, Theorem 1, Case 3]. The paper writes: "|χ⟩⟨ψ| ∈ S_{D²}(B)," using
Lemma 2(a) for the column direction and Lemma 2(b) for the row direction. The
blueprint isolates the assembly as a separate theorem — this is a structural
improvement for formalization.

**Lemma 7.29 (Blocking transfer).** S_n(A^{[L]}) = M_D ⟹ S_{nL}(A) = M_D.
Correct. Direction: S_n(A^{[L]}) ⊆ S_{nL}(A), so if the left side equals M_D, so
does the right.

**Remark 7.30 (Relation with Lemma 2(b)).** Correct overview.

### Section 7.8 — Blocked tensor and rectangular span

**Theorem 7.31 (Blocking preserves normality).**
Result: correct. Proof sketch: **has an issue**.

The proof says: "If S_N(A) = M_D then S_{NL}(A) = M_D (padding by repeated
single-letter words)."

This "padding" claim is problematic as a direct algebraic argument. Padding each
letter of a length-N word to a block of L identical letters gives a word of
length NL, but the resulting word product is (A_{i₁})^L · (A_{i₂})^L · ⋯ ·
(A_{i_N})^L, which is NOT equal to A_{i₁} · A_{i₂} · ⋯ · A_{i_N} in general.

The correct justification: S_N(A) = M_D means A is normal (Definition 2.19).
By [SPGWC10, Proposition 3], normality ⟺ primitivity of the channel. For a
primitive channel, S_n(A) = M_D for all n ≥ i(A). Since N ≥ i(A) and NL ≥ N,
S_{NL}(A) = M_D.

Alternatively, without invoking the equivalence: S_N = M_D means 𝟙 ∈ S_N. Then
S_N ⊆ S_{N+N} (multiply any element of S_N by elements of S_N; since 𝟙 ∈ S_N, we
get S_N · 𝟙 ⊆ S_{2N}... wait, 𝟙 ∈ S_N doesn't give 𝟙 ∈ S_1, so this doesn't
directly give monotonicity). Actually: for M ∈ S_N, M = M · 𝟙, and
𝟙 = Σ c_w A^w with each |w| = N. So M · 𝟙 = Σ c_w M · A^w ∈ S_{2N}. Thus
S_N ⊆ S_{2N}. Iterating: S_N ⊆ S_{kN} for all k ≥ 1. In particular
M_D = S_N ⊆ S_{NL}. ✔

So the claim IS correct via this iterated-identity argument, but the blueprint's
stated justification ("padding by repeated single-letter words") is misleading.
The correct mechanism is: 𝟙 ∈ S_N (since S_N = M_D), so any M ∈ S_N satisfies
M = M · 𝟙 ∈ S_N · S_N ⊆ S_{2N}, giving S_N ⊆ S_{2N} ⊆ ⋯ ⊆ S_{kN}.

**Lemma 7.32 (Chunking).** S_{nL}(A) ⊆ S_n(A^{[L]}). Correct.

**Theorem 7.33 (Word eigenvector → blocked eigenvector).** Correct and trivial.

**Theorem 7.34 (Wielandt blocked assembly).** Given column eigenvector, transpose
eigenvector, and rank-one element in S_m(A^{[L]}), concludes
S_{((D-1)+m+(D-1))·L}(A) = M_D.

**Paper comparison**: This theorem has no direct counterpart in the paper. The
paper's assembly (Theorem 1) works directly with the unblocked tensor. The
blueprint introduces blocking as an intermediate step. This is a structural
deviation motivated by the formalization strategy — see §6 below.

The proof applies Theorem 7.28 to the blocked tensor B = A^{[L]}. But
Theorem 7.28 requires hypothesis (2): |φ⟩⟨e_j| ∈ S_m(B) for each j. The proof
sketch doesn't explain how this hypothesis is satisfied from the given data
(column eigenvector, transpose eigenvector, one rank-one element φψ^T). See the
discussion of Theorem 7.35 below.

**Theorem 7.35 (Rank-one extraction for blocked tensor).** This is the key
technical result and the most significant deviation from the paper.

Statement: Given normality at length N₀ (S_{N₀} = M_D), produces eigenvectors
φ, ψ and a rank-one element φψ^T ∈ S_m(A^{[N₀]}).

### Why rank-one elements are needed

The goal of the full Wielandt argument is S_N(A) = M_D for some fixed N. The
earlier steps give column spreading: H_{D-1}(A, φ) = ℂ^D (for any target vector
e_i, there exists M_i ∈ S_{D-1} with M_i φ = e_i). But to build all matrix units
E_{ij} = |e_i⟩⟨e_j|, the assembly step (Theorem 7.28) also requires rank-one
operators |φ⟩⟨e_j| ∈ S_m(A) for every j. Column spreading provides the |e_i⟩
part; rank-one operators provide the ⟨e_j| part. Without rank-one operators in
the word span, column spreading alone cannot reach all matrices.

### How the paper [SPGWC10] does it (Lemma 2(b))

The paper uses the Jordan normal form of a Kraus operator A₁ with eigenvector φ.
It decomposes A₁ into its invertible part (nonzero-eigenvalue Jordan blocks,
size D̃) and nilpotent part. The key construction is the rectangular span
R_n = P · S_n(A), where P is the (non-Hermitian) projector onto the invertible
part. Since A₁ is invertible on range(P), left-multiplication by A₁ preserves
linear independence in R_n, so dim R_n grows until R_{D̃D} = P · M_D. This means:
for ANY |ψ⟩, there exists A ∈ S_{D̃D} with PA = |φ⟩⟨ψ|. The recovery step
A₁^r · PA / μ^r puts this back in a word span: |φ⟩⟨ψ| ∈ S_{D̃D+r} for ALL ψ.

The result: hypothesis (2) of the assembly step is satisfied directly, for every
basis vector e_j, with m = D² − D + 1.

### How the blueprint does it (Theorem 7.35)

The blueprint takes a different route. Instead of the Jordan form and rectangular
span, it:

1. Blocks the tensor to B = A^{[N₀]}.
2. Extracts a column eigenvector φ from some B^{j₀} (via nonzero trace →
   eigenvector).
3. Extracts a row (transpose) eigenvector ψ from some (B^{k₀})^T.
4. Claims φψ^T ∈ S_{2D}(B) via the Fitting decomposition.

The claimed mechanism: set P = (B^{j₀})^D and Q = (B^{k₀})^D. The Fitting
decomposition gives φ ∈ range(P) and ψ ∈ range(Q^T). Then φψ^T ∈
range(mulLeft(P) ∘ mulRight(Q)) ⊆ S_{2D}(B).

### The issue with the m = 2D bound

The proof claims range(mulLeft(P) ∘ mulRight(Q)) ⊆ S_{2D}(B). Let me trace what
this means concretely.

Since φ ∈ range(P), there exists v with Pv = φ. Since ψ ∈ range(Q^T), there
exists u with Q^T u = ψ. Then:

    φψ^T = (Pv)(Q^T u)^T = (Pv)(u^T Q) = P · (vu^T) · Q.

Now P = (B^{j₀})^D ∈ S_D(B) (it is the word (j₀, j₀, ..., j₀) of length D), and
similarly Q = (B^{k₀})^D ∈ S_D(B). The product P · (vu^T) · Q is a sandwich of a
word-span element, an arbitrary matrix vu^T, and another word-span element.

The word-span product rule (Lemma 7.26) says S_m · S_n ⊆ S_{m+n}, but this
applies when BOTH factors are in word spans. The sandwich P · (vu^T) · Q involves
an arbitrary middle factor vu^T that is NOT in any word span in general. So the
conclusion P(vu^T)Q ∈ S_{2D}(B) does not follow from the product rule.

For the inclusion to hold, one would need vu^T ∈ S_0(B) = span{𝟙}, but vu^T is
an arbitrary rank-one matrix, not a scalar multiple of the identity.

### The theorem statement is still correct

The rank-one element φψ^T does lie in SOME S_m(B). This follows from the fact
that B is normal (by Theorem 7.31), so S_M(B) = M_D(ℂ) for some M. Since
φψ^T ∈ M_D, it lies in S_M(B). The existential statement (∃m: φψ^T ∈ S_m(B)) is
therefore correct. Only the specific bound m = 2D is unjustified.

Since the downstream results (Theorems 7.34 and 7.36) only need the existence of
some m (the final bound on N depends on m but no specific value is required for
the qualitative result ∃N: S_N = M_D), the theorem and all its consequences
remain valid.

### Proposed fixes

**Fix 1 (minimal):** Weaken the proof to state "φψ^T ∈ S_m(B) for some m" without
claiming m = 2D. The existence follows from normality of B: since S_M(B) = M_D
for some M, every matrix including φψ^T lies in S_M(B). This makes the
downstream Theorem 7.36 correct with a possibly larger (but still finite) bound.

**Fix 2 (following the paper):** Replace the proof with the paper's rectangular
span argument adapted to the Fitting decomposition. Define R_n = P · S_n(B)
where P = (B^{j₀})^D. Show that left-multiplication by B^{j₀} preserves linear
independence in R_n (since B^{j₀} is invertible on range(P) by the Fitting
decomposition). The same dimension-growth-or-primitivity-contradiction argument
gives R_{D̃·D}(B) = P · M_D. Then for any ψ, there exists A ∈ S_{D̃·D}(B) with
PA = |φ⟩⟨ψ|, and |φ⟩⟨ψ| = (B^{j₀})^r · A / μ^r ∈ S_{D̃·D+r}(B). This
produces ALL rank-one operators |φ⟩⟨e_j| ∈ S_{D²-D+1}(B), directly satisfying
hypothesis (2) of Theorem 7.28 without needing a transpose eigenvector at all.

**Fix 3 (intermediate):** Keep the Fitting-decomposition approach but use a
correct bound. Since B is normal, S_M(B) = M_D for some M. Then for any
matrix X ∈ M_D, X ∈ S_M(B), so PXQ ∈ S_{D+M+D}(B) = S_{2D+M}(B) (using the
product rule: P ∈ S_D, X ∈ S_M, Q ∈ S_D). This gives m = 2D + M, which is
correct but depends on M (the normality index of B).

**Recommended fix:** Fix 2 is the cleanest since it follows the paper's approach
and avoids the transpose eigenvector entirely. It also gives the sharpest bound
and makes the proof self-contained (no circular dependence on Theorem 7.36 for
the existence of m). However, it requires formalizing the rectangular span growth
argument, which the paper does via Jordan form and the blueprint would need to
do via the Fitting decomposition.

**Theorem 7.36 (Fixed-length word-span saturation).** ∃N: S_N(A) = M_D.
Correct modulo Theorem 7.35.

⚠️ **Citation.** Says "This gives the fixed-length spanning conclusion
corresponding to [SPGWC10, Lemma 2(b)]." Correct reference.

**Remark 7.37.** Notes the blocking route. Correct.

### Section 7.9 — Primitive MPS tensors

**Definition 7.38 (Primitive MPS tensor).** TP gauge + PSD fixed point + spectral
gap ρ_spec(ℰ_A − P) < 1.

v2 uses TP normalization; v1 used DS gauge. ✔ Fixed.

**Theorem 7.39 (Primitive overlap convergence).** O_{AA}(N) → 1. Correct, from
Theorem 6.21.

### Section 7.10 — Primitivity and normality

**Theorems 7.40–7.41.** Nonzero word products, iterated transfer nonvanishing.
Correct.

**Theorem 7.42 (Fixed-point uniqueness from spectral gap).** Correct.

**Theorem 7.43 (Complement powers → 0).** Correct.

**Remark 7.44 (Spectral gap vs positive definiteness).** Important. Notes that
Definition 7.38 (PSD ρ) is weaker than the paper's notion (PD ρ). Counterexample
(D = 2, ρ = diag(1,0)) is valid. The chain primitive + ρ PosDef ⟹ irreducible ⟹
algSpan = M_D ⟹ normal is stated explicitly.

⚠️ The remark says "The last step uses the aperiodicity condition 𝟙 ∈ S₁(A)
from Remark 7.46." This is correct: the chain to normality requires the
additional aperiodicity input.

**Theorem 7.45 (Primitive + PD ⟹ irreducible).** NEW in v2. Correct.
The contrapositive proof is clean:
1. Assume invariant projection P.
2. σ = PρP is invariant under ℰ^n.
3. Convergence: ℰ^n(σ) → (tr(σ)/tr(ρ))ρ.
4. (𝟙 − P)ρ = 0 contradicts ρ > 0.

**Paper comparison**: This corresponds to one direction of [SPGWC10,
Proposition 3, (a) ⟹ (c)]. The paper proves it differently (via the spectral
characterization), but the content is equivalent.

### Section 7.11 — Cumulative span to word span (NEW in v2)

**Remark 7.46 (Aperiodicity condition).** 𝟙 ∈ S₁(A) is an additional hypothesis,
NOT implied by TP normalization. Correct and important.

**Remark 7.47 (Counterexample).** A₀ = E₁₂, A₁ = E₂₁. T₂ = M₂ but S_n ≠ M₂ for
any n. The tensor is not normal — it's irreducible with period 2. ✔

Note: This counterexample shows that cumulative spanning (T_N = M_D) does NOT
imply normality (S_L = M_D for some L). The gap is the periodicity.

**Theorem 7.48 (Aperiodicity ⟹ word span monotonicity).** If 𝟙 ∈ S₁, then
S_n ⊆ S_{n+1}. Correct. Proof: M = M · 𝟙 ∈ S_n · S₁ ⊆ S_{n+1}.

**Theorem 7.49 (Aperiodicity ⟹ T_n = S_n).** Correct.

**Theorem 7.50 (T_N = M_D + aperiodicity ⟹ normal).** Correct.

**Theorem 7.51 (algSpan = M_D + aperiodicity ⟹ normal).** Correct.

**Theorem 7.52 (Irreducible + aperiodicity ⟹ normal).** Correct. Assembles:
irreducible → irreducible action (Thm 8.20) → algSpan = M_D (Thm 8.21, Burnside)
→ normal (Thm 7.51).

⚠️ **Forward dependency on Chapter 8.** Cites Theorems 8.20 and 8.21.
Mathematical dependency is acyclic (the Burnside results don't depend on the
rest of Chapter 8), but it creates a presentation-level circular dependency.

⚠️ **Citation.** Says "This corresponds to [SPGWC10, Theorem 1 / Proposition 3]."
This is approximately correct but conflates two results. Proposition 3 is the
equivalence of primitivity notions; Theorem 1 is the quantitative bound. The
theorem most closely corresponds to one direction of Proposition 3: (c) ⟹ (b).

**Theorem 7.53 (Primitive + PD + aperiodicity ⟹ normal).** Correct. Chains
Theorems 7.45 and 7.52.

**Remark 7.54.** Clarifies that the aperiodicity bridge is only needed for the
block-injective route (Definition 2.19), not for the normal-canonical route
(Chapters 8–10). Good.

---

## 5. Cross-Chapter Consistency

### Definitions

**Normal tensor (Def 2.19 vs paper's definition):** As established earlier in this
project, these are equivalent by [SPGWC10, Proposition 3]: eventual block
injectivity (Def 2.19) ⟺ primitive channel (paper's Definition IV.1). The
blueprint uses the algebraic characterization; the paper uses the spectral one.
The bridge theorems (7.45, 7.52, 8.26) establish directions of this equivalence
within the formalization.

This resolves the "two meanings of normal" issue (X-1 from the Ch2–6 remaining
issues file): the two definitions are equivalent, so X-1 is a presentation issue
(both characterizations should be mentioned together with a note on
equivalence), not a mathematical discrepancy.

### Chapter 2

Lemma 7.7 correctly links S_L = M_D to L-block injectivity (Def 2.18). No issues.

### Chapter 6

Theorem 7.39 correctly cites Theorem 6.21 (self-overlap convergence). No issues.

### Chapter 8

Forward dependency: Theorem 7.52 cites Theorems 8.20–8.21 (Burnside bridge).
Acyclic mathematically; circular in presentation.

Theorem 7.52 is also cited in Chapter 8's Remark 2.20 and Theorem 8.26 as part
of the bridge. Consistent.

### DS gauge

Fully eliminated from v2 Chapter 7. Definition 7.38 uses TP gauge. Consistent
with Chapters 4–6.

---

## 6. Deviations from the Paper [SPGWC10]

### Deviation 1: Hypothesis is "normal" (Def 2.19) rather than "primitive"

The paper assumes primitivity throughout. The blueprint assumes normality
(eventual full Kraus rank). Since these are equivalent by Proposition 3, this is
not a mathematical deviation. For formalization, starting from the algebraic
condition is natural.

### Deviation 2: Weaker quantitative bounds

The paper tracks the Kraus rank d and obtains D² − d + 1 bounds. The blueprint
uses D² throughout. Acknowledged in Remark 7.24.

### Deviation 3: Fitting decomposition replaces Jordan normal form

The paper uses the Jordan normal form for Lemma 2(b). The blueprint uses
generalized eigenspaces. This provides the same structural information
(nilpotent vs invertible decomposition) but with weaker quantitative control
(the specific Jordan block size r used in the paper's bound D̃D + r ≤ D² − D + 1
is replaced by the nilpotent power bound D).

### Deviation 4: Lemma 2(b) proof strategy

**Paper**: Uses the rectangular span R_n = P · S_n (where P is the non-Hermitian
projector onto the invertible Jordan blocks). Shows R_n grows until
R_{D̃D} = P · M_D. Recovers |φ⟩⟨ψ| for ALL ψ via A₁^r = A₁^r P.

**Blueprint**: Blocks the tensor, extracts one column eigenvector and one
transpose eigenvector, produces ONE rank-one element φψ^T. Compensates by using
the blocked assembly theorem with both column and row eigenvector spreading.

The paper's approach is more direct: it produces all rank-one operators from φ in
one step, and the assembly is then straightforward. The blueprint's approach is
more indirect: it produces one rank-one element and relies on a more complex
assembly mechanism.

### Deviation 5: The theorem numbering citation for Theorem 7.23

Theorem 7.23 says "This is [SPGWC10, Theorem 1]." The paper's Theorem 1 gives
quantitative bounds on i(A), while the blueprint's Theorem 7.23 gives only the
cumulative-span result T_{D²} = M_D. The fixed-length result ∃N: S_N = M_D is
Theorem 7.36 (which more closely corresponds to the paper's Theorem 1, Case 3).

---

## 7. Corrections to Earlier Review

1. **Lemma 2(b) gap closure timing.** Earlier I stated this was a v1→v2 change.
   It was not — the closure was already in v1. The actual v1→v2 changes are
   in §7.9–7.11 only.

2. **"Two meanings of normal" (X-1).** Earlier I flagged this as a moderate
   terminology issue. After the discussion establishing that Def 2.19 and the
   paper's "normal" are equivalent by [SPGWC10, Proposition 3], this is
   downgraded to a presentation issue. The blueprint should add a remark
   noting the equivalence.

3. **Theorem 7.31 proof.** Earlier I thought the "padding" argument was wrong.
   After further analysis, the result IS correct, but via a different mechanism
   than stated: S_N = M_D implies 𝟙 ∈ S_N, then S_N ⊆ S_{2N} ⊆ ⋯ ⊆ S_{kN}.
   The "padding by single-letter words" phrasing is misleading but the theorem
   stands.

---

## 8. Cleanup Checklist

1. **Definition 7.1**: Fix citation "[SPGWC10, Eq. (1)]" → "[SPGWC10, §II]."
2. **Theorem 7.13**: Add D ≥ 1 hypothesis for completeness.
3. **Theorem 7.14 proof**: Clarify eigenvector vs generalized eigenvector step.
4. **Theorem 7.23**: Clarify that this is the cumulative-span result; the paper's
   Theorem 1 gives the stronger fixed-length bound via Lemma 2(b).
5. **Theorem 7.31 proof**: Replace "padding by repeated single-letter words" with
   the correct argument: S_N = M_D implies 𝟙 ∈ S_N, so S_N ⊆ S_{kN} for all
   k ≥ 1 by iterated multiplication.
6. **Theorem 7.35 proof**: The bound m = 2D for φψ^T ∈ S_{2D}(B) is
   unjustified. The argument P(vu^T)Q ∈ S_{2D}(B) fails because the middle
   factor vu^T is not a word-span element; the word-span product rule only
   applies when all factors are in word spans. The theorem statement (∃m) is
   correct by normality, but the specific bound needs repair. Three fixes are
   proposed in the Theorem 7.35 discussion: (1) weaken to ∃m without a bound,
   (2) follow the paper's rectangular span argument adapted to Fitting
   decomposition, or (3) use S_{2D+M}(B) where M is the normality index.
   Fix (2) is recommended as it follows the paper most faithfully and avoids
   the transpose eigenvector entirely.
7. **Theorem 7.52**: Consider moving the Burnside bridge (Thms 8.20–8.21) to
   Chapter 7 to eliminate the circular presentation dependency.
8. **Definition 7.38**: Consider requiring ρ > 0 (positive definite) to match
   the paper's notion. The current PSD requirement is weaker and forces
   additional hypotheses in Theorems 7.45 and 7.53.
9. **Add equivalence remark**: Near Definition 2.19 or §7.10, add a remark
   noting that normality (Def 2.19) ⟺ primitive channel ⟺ strongly
   irreducible, citing [SPGWC10, Proposition 3]. This resolves the X-1
   terminology issue from the Ch2–6 review.

---

## 9. Final Assessment

Chapter 7 is mathematically correct in all its theorem statements. The core
Wielandt bound (§7.1–7.8) follows [SPGWC10] faithfully, with the expected
deviations (Fitting decomposition replacing Jordan form, weaker quantitative
bounds). The primitivity–normality bridge (§7.9–7.11, new in v2) correctly
establishes the connections needed for later chapters.

The most important issue is the rank-one extraction proof (Theorem 7.35). The
theorem statement (∃m: φψ^T ∈ S_m(B)) is correct, but the claimed bound m = 2D
is unjustified: the proof attempts to sandwich an arbitrary matrix between two
word-span elements, which does not produce a word-span element. The recommended
fix is to follow the paper's rectangular span argument (adapted to the Fitting
decomposition), which produces all rank-one operators |φ⟩⟨ψ| directly and avoids
the need for a transpose eigenvector entirely.

All other issues are citation corrections (Definition 7.1, Theorem 7.23), minor
proof clarifications (Theorems 7.14, 7.31), and structural suggestions (forward
dependency on Chapter 8, definition strengthening for 7.38).
