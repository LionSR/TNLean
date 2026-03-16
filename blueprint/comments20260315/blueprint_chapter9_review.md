
# Blueprint Review — Chapter 9 (Block Permutation and Separation)

This review follows the protocol in `blueprint_review_protocol.md` and the
format established in the Chapter 8 review. It covers v2 of the blueprint,
identifies v1 → v2 changes, compares against the source papers [PGVWC07]
and [CPGSV21], and checks cross-chapter consistency with Chapters 2–8 and
forward dependencies on Chapters 10–11.

---

## 1. Role of Chapter 9 in the Blueprint

Chapter 9 has two distinct functions:

1. **§9.1–9.2 (Block permutation algebra and pi-algebra linear extension):**
   Establishes that every ℂ-algebra automorphism of a product ∏ M_{D_k}(ℂ)
   decomposes as a permutation followed by per-block inner automorphisms
   (Skolem–Noether). Then uses the per-block linear extensions from
   Chapter 3 to show that per-block same-MPV implies global gauge
   equivalence.

2. **§9.3 (Block separation):** Defines the canonical form predicate and
   proves the block separation theorem: if two block-diagonal tensors in
   canonical form generate the same MPV family, then each block pair
   generates the same MPV family. The argument proceeds by induction on
   the number of blocks, using the spectral gap (Chapter 6) to peel off the
   dominant block at each step.

The chapter draws on Chapters 3, 6, and 8, and feeds into Chapters 10–11
(BNT theory and full assembly).

---

## 2. Global Assessment

| Aspect | Evaluation |
|---|---|
| Mathematical correctness | Correct |
| Conceptual clarity | Good; clean two-part structure |
| Structural quality | Good; short and focused |
| Cross-chapter consistency | Substantially improved from v1 (DS → TP); one residual issue (see §5) |
| Literature alignment | Good; [PGVWC07], [CPGSV21], [Wol12] tracked |
| v1 → v2 changes | Definition 9.8 corrected (DS → TP); Theorem 9.14 added |

Chapter 9 is the shortest chapter reviewed so far, and the cleanest. The
mathematical content is standard (block permutation algebra is textbook
semisimple algebra; the block separation is a straightforward induction using
the spectral gap). The most important structural contribution is packaging
these results for the Lean formalization.

---

## 2a. Notation Clarity

Several notational choices in this chapter are unclear or nonstandard.

**Theorem 9.1: the arrow ∏_k R_k →̃ ∏_k R_k.** The symbol →̃ (rendered
as \stackrel{\sim}{\to} in the PDF) presumably means "isomorphism." This
is a common LaTeX convention but it is ambiguous in context — does it
mean ring isomorphism, ℂ-algebra isomorphism, or just any bijective
homomorphism? Theorem 9.1 says "ring isomorphism" in the name but uses
this arrow without defining it. For a Lean formalization, the type of
morphism must be precise. Recommendation: either write "ring isomorphism
T : ∏_k R_k → ∏_k R_k" (dropping the tilde, since "ring isomorphism" is
already stated), or define the arrow explicitly.

**Definition 9.5: the same →̃ arrow.** Reappears as
T : ∏_k M_{D_k}(ℂ) →̃ ∏_k M_{D_k}(ℂ). Here it means "ℂ-algebra
isomorphism." But in Theorem 9.1 it meant "ring isomorphism." The switch
from ring to algebra is silent. This should be noted.

**Theorem 9.3: T(M)_k = X_k M_{σ(k)} X_k^{-1}.** The subscript _k on
T(M)_k denotes "the k-th block component of T(M)." This notation is not
defined. A reader would need to understand that elements of ∏_k M_{D_k}(ℂ)
are tuples M = (M_1, …, M_r), and T(M)_k means the k-th component of the
image. This is standard for product algebras but should be stated once.

**Definition 9.4: A_k, B_k notation.** The definition says "Given injective
tensors A_k, B_k of bond dimension D_k with the same MPV for each block
k." Here A_k denotes a *family* of matrices {A^i_k}_{i=1}^d for each
block index k. The superscript i (physical index) is suppressed in the
notation "A_k." This is consistent with the rest of the blueprint but
potentially confusing: "A_k" could be read as a single matrix rather than
a d-tuple. The notation T_k(A^i_k) = B^i_k makes the physical index
explicit, but only inside the definition of T_k.

**Lemma 9.12: V^{(N)}(A_k)_σ.** This notation appears throughout §9.3 and
is defined earlier (Chapter 2), but it packs a lot of information: V^{(N)}
is the MPV at system size N, (A_k) specifies the block tensor, and _σ is
the spin configuration (a multi-index σ = (σ_1, …, σ_N)). The formula
∑_k μ_k^N (V^{(N)}(A_k)_σ − V^{(N)}(B_k)_σ) = 0 for all N, σ
is a statement about equality of components of vectors in (ℂ^d)^{⊗N}.
This is correct but dense. Adding "for all system sizes N ≥ 1 and spin
configurations σ" would help.

**Definition 9.8: O_{A_k A_k}(N).** The self-overlap notation is defined in
Chapter 2 (Definition 2.26) but not recalled here. A reader encountering
it for the first time in §9.3 would need to look it up. A brief reminder
"O_{AB}(N) = ⟨V^{(N)}(A) | V^{(N)}(B)⟩ / (‖V^{(N)}(A)‖ · ‖V^{(N)}(B)‖)"
or a cross-reference would help.

**Theorem 9.7: ⊕_k μ_k A_k.** The direct sum notation for block-diagonal
tensors. This is defined in Definition 8.1 / Definition 2.23, but the
notation ⊕_k μ_k A_k is slightly ambiguous — it could mean ⊕_k (μ_k A_k)
(which is intended: each block is the tensor μ_k A_k) or (⊕_k μ_k) · A_k
(which makes no sense but could be misread). Parentheses would help:
⊕_k (μ_k A_k).

**Overall assessment:** The notation is functional but compressed. For a
formalization blueprint, where every symbol needs a precise type, the
compressed notation creates ambiguity. The main issues are: (a) the →̃
arrow used without definition for two different kinds of isomorphism,
(b) suppressed physical indices on tensor families, and (c) the
self-overlap and MPV-component notation used without local recall.

---

## 3. v1 → v2 Changes

### What changed

**3-A. DS gauge → TP normalization in Definition 9.8.**
v1's condition 2 reads: "each A_k is in DS gauge (∑_i (A^i_k)† A^i_k = 𝟙)."
v2's condition 2 reads: "each A_k satisfies the TP normalization ∑_i (A^i_k)† A^i_k = 𝟙."

The formula is identical — ∑_i (A^i_k)† A^i_k = 𝟙 — but v1 calls it "DS gauge"
while v2 calls it "TP normalization." This is the same correction applied
across Chapters 4–8: the condition ∑_i (A^i)† A^i = 𝟙 is the trace-preserving
(TP) condition on the transfer map, not the doubly stochastic (DS) condition.
DS would additionally require ∑_i A^i (A^i)† = 𝟙 (unitality). The v1
terminology was misleading; v2 corrects it.

**Consistency check:** This matches the DS → TP corrections in Chapters 4
(reviewed), 5 (reviewed), 6 (reviewed), 7 (reviewed, Definition 7.38), and 8
(reviewed, Theorem 8.24). ✔

**3-B. DS gauge → TP normalization in Theorem 9.12 (v1) / 9.13 (v2).**
v1's Theorem 9.12 assumes "(B_k) be injective tensors in DS gauge."
v2's Theorem 9.13 assumes "(B_k) be injective tensors satisfying the same TP
normalization ∑_i (B^i_k)† B^i_k = 𝟙."
Same correction as 3-A applied to the comparison tensors B_k. ✔

**3-C. Theorem 9.14 (entirely new in v2).**
v2 adds a normal-canonical companion to Theorem 9.13. It uses
Definition 8.28 (normal canonical form predicate) instead of Definition 9.8
and assumes the B_k are irreducible (rather than injective). The proof
replaces the explicit self-overlap hypothesis with Theorem 8.29 and uses
Theorem 8.30 for the leading-block identification. This was not present in
v1.

**3-D. Chapter 3 cross-reference renumbering.**
v1's Theorem 9.6 cites "Theorems 3.8 and 3.9" and "Lemma 3.12."
v2's Theorem 9.6 cites "Theorems 3.6 and 3.7" and "Lemma 3.10."
This reflects the v1 → v2 renumbering in Chapter 3:
- v1 Thm 3.8 (linear extension) → v2 Thm 3.6
- v1 Thm 3.9 (multiplicativity) → v2 Thm 3.7
- v1 Lemma 3.12 (promotion) → v2 Lemma 3.10

Similarly, v1's Theorem 9.7 cites "Theorem 3.13" (single-block FT), while
v2's Theorem 9.7 cites "Theorem 3.11." This reflects v1 Thm 3.13 → v2
Thm 3.11. ✔

**3-E. Theorem numbering shift.**
Due to the addition of Theorem 9.14, the subsequent theorem numbers shift:
- v1 Thm 9.10 (Vandermonde) → v2 Thm 9.11
- v1 Lemma 9.11 (block separation core) → v2 Lemma 9.12
- v1 Thm 9.12 (block separation) → v2 Thm 9.13
- v1 Thm 9.13 (CF FT) → v2 Thm 9.15
- v2 Thm 9.14 (normal-canonical block separation) is NEW

### What did NOT change

**§9.1 (Theorems 9.1–9.3):** Identical between v1 and v2 in content. The
proofs are the same (block ideal lattice, dimension comparison, Skolem–
Noether). The Skolem–Noether reference was updated from "Theorem 3.11"
(v1) to "Theorem 3.9" (v2), reflecting the Chapter 3 renumbering.

**§9.2 (Definition 9.4, Definition 9.5, Theorems 9.6–9.7):** Content identical
except for the Chapter 3 cross-reference updates noted in 3-D above.

**Remark 9.9 (v1) / Remark 9.9 (v2):** Content essentially identical.

**Remark 9.10 (v2):** New in v2; provides the normal-canonical companion
note for Definition 9.8. Short and correct.

**Theorem 9.11 (Vandermonde) and Lemma 9.12 (block separation core):**
Content identical to v1 Thm 9.10 and Lemma 9.11 except for the TP
terminology update.

---

## 4. Statement-by-Statement Review

### Section 9.1 — Block permutation algebra

**Theorem 9.1 (Ring isomorphisms permute block ideals).**
Correct. Here is the argument in full, since the blueprint's proof sketch
is compressed:

The product ring R = ∏_{k=1}^r R_k has two-sided ideals
I_k = {x ∈ R : x_j = 0 for j ≠ k} (the "block ideals"). Each I_k is
isomorphic to R_k as a ring, and since R_k is simple (no nontrivial
two-sided ideals), I_k is a *minimal* nonzero two-sided ideal of R — an
atom in the ideal lattice. Moreover, these are the *only* atoms: any
nonzero two-sided ideal J of R must contain some I_k (project J onto each
factor; at least one projection is nonzero; simplicity of R_k then forces
the projection to be all of R_k). Since T is a ring isomorphism,
T(I_k) is again a minimal nonzero two-sided ideal of R, hence T(I_k) =
I_{σ(k)} for some index σ(k). Since T is bijective, the map k ↦ σ(k) is
a permutation. ✔

⚠️ **Ring vs algebra: the two-level structure (verified against Lean code).**
The blueprint states Theorem 9.1 for "ring isomorphisms" of products of
"simple rings," then silently switches to "algebra automorphisms" in
Theorems 9.2 and 9.3. This transition is not commented on.

Examining the Lean formalization (`BlockPermutation.lean`), the code
handles this carefully with a **two-level architecture**:

*Ring level (`≃+*` = `RingEquiv`):* The block ideal permutation, the
`componentMap` definition (M ↦ T(Pi.single i M)(σ i)), and the proofs
of multiplicativity (`componentMap_map_mul`), unit preservation
(`componentMap_map_one`), injectivity, surjectivity, and bijectivity are
all proved for `RingEquiv` on products of `IsSimpleRing` types. This is
the correct generality for these results — they do not need ℂ-linearity.

*Algebra level (`≃ₐ[ℂ]` = `AlgEquiv`):* Two things require the upgrade
to ℂ-algebra equivalence:
- `componentMap_map_smul_of_algEquiv`: the componentMap commutes with
  ℂ-scalar multiplication *only* when T is a ℂ-algebra map. A ring
  automorphism could compose with complex conjugation, breaking scalar
  compatibility.
- `dim_preserved`: dimension is a ℂ-vector space invariant. The proof
  that D_{σ(k)} = D_k uses the fact that a ℂ-algebra isomorphism
  M_n(ℂ) → M_m(ℂ) preserves ℂ-vector space dimension, hence n² = m²,
  hence n = m. A bare ring isomorphism would not give this.

The final theorem `algEquiv_pi_matrix_decomposition` takes `AlgEquiv` as
input and produces σ, the dimension proof D(σ i) = D i, and per-block
GL matrices X_k.

**What the blueprint should document:** The two-level structure is a
genuine design choice in the Lean code that the blueprint should describe.
The blueprint's Theorem 9.1 (ring level) is correctly stated at the ring
level, and the Lean code confirms this is the right generality. But the
blueprint should note explicitly where and why the upgrade to ℂ-algebra
is needed (Theorems 9.2 and 9.3). Currently the transition is silent,
which obscures a real type-theoretic distinction that the Lean code makes
explicit.

**Theorem 9.2 (Dimension preservation).**
Correct. As confirmed by the Lean code (`dim_preserved`), this requires
`AlgEquiv`, not just `RingEquiv`. The argument: T restricts to a
ℂ-algebra isomorphism M_{D_k}(ℂ) ≅ M_{D_{σ(k)}}(ℂ), which forces
D_k² = D_{σ(k)}² as ℂ-vector space dimensions, hence D_k = D_{σ(k)}.
The ℂ-linearity is essential here — a ring isomorphism M_n(ℂ) → M_m(ℂ)
only gives n² = m² as abelian groups, which is weaker (though still
sufficient over ℂ, since the characteristic is 0). The Lean code takes
the cleaner route via ℂ-vector space dimension.

**Theorem 9.3 (Decomposition of automorphisms of ∏ M_{D_k}(ℂ)).**
Correct. The full argument, which the blueprint compresses into three
lines:

Let T be a ℂ-algebra automorphism of R = ∏_{k=1}^r M_{D_k}(ℂ).

Step 1 (Permutation): By Theorem 9.1, T permutes the block ideals:
T(I_k) = I_{σ(k)} for some permutation σ.

Step 2 (Dimension matching): By Theorem 9.2, D_{σ(k)} = D_k for all k.
This uses the fact that a ℂ-algebra isomorphism M_n(ℂ) ≅ M_m(ℂ) forces
n = m (since dim_ℂ M_n(ℂ) = n²).

Step 3 (Per-block inner automorphism): The restriction T|_{I_k} gives a
ℂ-algebra isomorphism I_k → I_{σ(k)}, which is the same as a ℂ-algebra
isomorphism M_{D_k}(ℂ) → M_{D_{σ(k)}}(ℂ) = M_{D_k}(ℂ) (using Step 2).
By Skolem–Noether (Theorem 3.9), every ℂ-algebra automorphism of
M_{D_k}(ℂ) is inner: T|_{I_k}(M) = X_k M X_k^{-1} for some invertible
X_k ∈ GL_{D_k}(ℂ).

Combining: T(M)_k = X_k M_{σ(k)} X_k^{-1}. ✔

⚠️ **Citation check.** The text says "see [CPGSV21, §IV.A] for the MPS
context." I was unable to directly verify the section numbering of [CPGSV21]
from the available PDFs (I have [CPGSV21] = Cirac et al., Review of TN, but
the section numbering in that paper may differ from the citation). This should
be independently verified. The mathematical content of Theorem 9.3 is
standard and does not depend on the citation being correct.

**Cross-reference check:** Theorem 9.3 cites "Theorem 3.9" (Skolem–Noether).
In v2, Theorem 3.9 is indeed the Skolem–Noether theorem. ✔

### Section 9.2 — Pi-algebra linear extension

**Definition 9.4 (Per-block linear extension).**
Correct. Given injective A_k, B_k with same MPV, the per-block linear
extension T_k is defined by T_k(A^i_k) = B^i_k, extended by linearity.
Existence and uniqueness follow from injectivity (the {A^i_k} span M_{D_k}(ℂ)).

⚠️ **Missing hypothesis.** The definition says "Given injective tensors A_k,
B_k of bond dimension D_k with the same MPV for each block k." It does not
require B_k to be injective, only A_k. This is correct — B_k need not be
injective for the linear extension to exist, since we only need {A^i_k} to form
a spanning set. However, for the downstream application (Theorem 9.7),
both A_k and B_k must be injective. The asymmetry is correct but should be
noted for the formalization: the definition applies with weaker hypotheses
than the theorem.

**Definition 9.5 (Product algebra automorphism).**
⚠️ **This is labeled as a definition but contains a nontrivial claim.** It
states: "The per-block linear extensions T_k are ℂ-algebra homomorphisms,
and assembling them blockwise gives a single ℂ-algebra automorphism."
This requires proof:
- T_k being a ℂ-algebra homomorphism requires multiplicativity (from
  Theorem 3.7) and the unit-preservation promotion (from Lemma 3.10).
- The assembly into a product automorphism requires checking that the
  blockwise map is surjective (which follows because each T_k is bijective
  by Theorem 3.8).

In v2, the proof of this claim is deferred to Theorem 9.6. So Definition 9.5
is really a forward declaration that is justified by Theorem 9.6. For a Lean
formalization, this should be a theorem, not a definition.

**Theorem 9.6 (Per-block linear extensions assemble).**
Correct. The full argument, since the blueprint compresses several steps:

Hypotheses: For each block k = 1, …, r, A_k and B_k are injective tensors
of bond dimension D_k generating the same MPV family.

Step 1 (Per-block linear extension exists): By Theorem 3.6, for each k
there is a unique linear map T_k : M_{D_k}(ℂ) → M_{D_k}(ℂ) with
T_k(A^i_k) = B^i_k for all physical indices i. Existence uses the fact
that {A^i_k}_i spans M_{D_k}(ℂ) (by injectivity of A_k); uniqueness
follows from the same spanning property.

Step 2 (Multiplicativity): By Theorem 3.7, each T_k is multiplicative:
T_k(MN) = T_k(M) T_k(N). This uses the same-MPV hypothesis applied to
length-2 words (see Chapter 3 review, Theorem 3.7).

Step 3 (Nonzero and bijective): T_k ≠ 0 since T_k(A^i_k) = B^i_k and
B_k is assumed to have same MPV as A_k (so B^i_k ≠ 0 for some i, by
Theorem 3.5). By Theorem 3.8 (simplicity of M_D(ℂ)), a nonzero
multiplicative ℂ-linear endomorphism of M_{D_k}(ℂ) is bijective.

Step 4 (Promotion to algebra homomorphism): By Lemma 3.10, a
multiplicative surjective ℂ-linear map T_k preserves the unit:
T_k(𝟙) = 𝟙. Hence T_k is a ℂ-algebra automorphism of M_{D_k}(ℂ).

Step 5 (Assembly): Define T : ∏_k M_{D_k}(ℂ) → ∏_k M_{D_k}(ℂ) by
T(M)_k = T_k(M_k). This is a ℂ-algebra automorphism of the product
(each component is an automorphism). Theorem 9.3 decomposes it as
a permutation σ followed by per-block inner automorphisms X_k. ✔

**Cross-reference check:** Cites "Theorems 3.6 and 3.7" and "Lemma 3.10."
These are correct in v2:
- Theorem 3.6 = existence/uniqueness of linear extension ✔
- Theorem 3.7 = multiplicativity of linear extension ✔
- Lemma 3.10 = promotion to algebra homomorphism ✔

⚠️ **Logical subtlety in Step 5.** The assembly T(M)_k = T_k(M_k) maps
the k-th block to the k-th block. But Theorem 9.3 tells us that T
decomposes as a permutation + per-block conjugation, meaning
T(M)_k = X_k M_{σ(k)} X_k^{-1}. This appears to contradict the assembly:
if T_k acts on the k-th block, how can a permutation appear?

The resolution: T_k is defined by T_k(A^i_k) = B^i_k. If the "matching"
of blocks is such that B_k is related to A_{σ(k)} (not A_k) for some
permutation σ, then T_k(M_{D_k}(ℂ)) will map into the σ(k)-th block.
But this contradicts the assembly T(M)_k = T_k(M_k), which maps block k
to block k.

In fact, the assembly as stated *does* map block k to block k, because
T_k : M_{D_k}(ℂ) → M_{D_k}(ℂ) is a map on the k-th block algebra.
The permutation σ from Theorem 9.3 then acts *within* the resulting
automorphism: the automorphism T sends the k-th block ideal to the
σ(k)-th block ideal, but only in the sense that the induced permutation
of ideals is σ. Since T(M)_k = T_k(M_k) and T is an automorphism,
what happens is that T_k must itself encode the permutation: T_k takes
elements of M_{D_k}(ℂ) (sitting in the k-th block) and produces elements
that, viewed in the product, have landed in the σ(k)-th block.

Wait — this does not work. T_k : M_{D_k}(ℂ) → M_{D_k}(ℂ) is an
endomorphism of M_{D_k}(ℂ), so it maps block k to block k. The assembly
T(M)_k = T_k(M_k) is a block-diagonal map. A block-diagonal map has
trivial permutation σ = id.

⚠️ **This means Theorem 9.6 actually proves that the permutation is
trivial in this setting.** The per-block same-MPV hypothesis (A_k same MPV
as B_k for the *same* k) forces the assembled automorphism to be
block-diagonal, hence σ = id. The permutation σ from Theorem 9.3 is the
identity, and the conclusion is simply that B^i_k = X_k A^i_k X_k^{-1}
for each k. The permutation becomes nontrivial only when one starts from
a *global* same-MPV condition (as in Theorem 9.13/9.15), where one does
not know a priori which blocks match.

This is not a mistake in the theorem, but the proof sketch's invocation of
"permutation σ" in Theorem 9.6 is misleading — in the per-block same-MPV
setting, the permutation is always trivial. The nontrivial permutation
only appears when combining with the block separation theorem (Theorem
9.13), where the global same-MPV is first decomposed into per-block same-
MPV *up to permutation*.

**Theorem 9.7 (Per-block same MPV gives global gauge equivalence).**
Correct. The proof applies the single-block FT (Theorem 3.11) to each
block, then assembles via Theorem 8.4.

**Cross-reference check:**
- "Theorem 3.11" = single-block FT. In v2, Theorem 3.11 is indeed the
  single-block FT. ✔
- "Theorem 8.4" = global gauge from block gauge. In v2, Theorem 8.4
  is correct. ✔

⚠️ **Theorem 9.7 does not use the permutation.** The theorem states that
"each pair (A_k, B_k) is gauge equivalent" — i.e., it asserts gauge equivalence
with the *same* block index k, not up to a permutation. This is correct
given the hypothesis (per-block same-MPV), but the reader might expect
the permutation from Theorem 9.6 to appear. The permutation is relevant
when one starts from a *global* same-MPV condition and deduces per-block
same-MPV up to reordering. This distinction matters for the
formalization: Theorem 9.7 takes per-block same-MPV as input (no
permutation needed); the permutation appears only in the combined
result of Theorem 9.15.

### Section 9.3 — Block separation

**Definition 9.8 (Canonical form predicate).**
Correct. Lists five conditions: (1) injective, (2) TP normalization,
(3) strictly decreasing moduli, (4) nonzero weights, (5) self-overlap
convergence.

✔ **DS → TP correction confirmed.** v2 uses "TP normalization
∑_i (A^i_k)† A^i_k = 𝟙" rather than v1's "DS gauge." The formula is
identical but the terminology is now correct. This resolves item 11 of
the Chapter 8 cleanup checklist.

⚠️ **Citation check: [Wol12, Thm. 6.7, item 3].**
The text says: "Condition (5) is a primitivity hypothesis: for a primitive
channel ([Wol12, Thm. 6.7, item 3]), T^n(ρ) → ρ_∞ for every initial state."
I verified this against Wolf's book. Theorem 6.7 item 3 states: "For all
density matrices ρ the limit lim_{k→∞} T^k(ρ) exists, is independent of ρ and
given by a positive definite density matrix ρ_∞." This is a characterization
of primitive maps, not a direct statement about self-overlap convergence.
The self-overlap convergence O_{AA}(N) → 1 follows from this (since the
overlap equals tr(ℰ^N_A) and the transfer map converges to a rank-one
projection), but the citation is to the correct theorem. ✔

⚠️ **Citation check: [Wol12, Thm. 6.8].**
The text says "See also [Wol12, Thm. 6.8] for the completely-positive
characterisation." Wolf's Theorem 6.8 gives equivalent characterizations of
primitivity for CP maps, including the condition that Kraus monomials
eventually span M_D(ℂ). This is correct. ✔

⚠️ **Observation on the predicate structure.** The canonical form predicate
requires self-overlap convergence (condition 5) as an explicit hypothesis.
Remark 9.9 then notes that this is redundant when primitivity holds
(via Theorem 8.24). This design choice is defensible for the formalization:
it allows the predicate to be satisfied without proving primitivity. However,
it means the canonical form predicate is *weaker* than what the literature
typically assumes (primitivity implies both TP normalization and overlap
convergence). For the Lean formalization, this weaker predicate is fine since
Theorem 8.24 can supply the overlap convergence when needed.

**Remark 9.9.**
Correct. Notes that condition (5) is derivable from primitivity via
Theorem 8.24. Accurate cross-reference. ✔

**Remark 9.10 (Normal-canonical companion).**
Correct. Notes that Definition 8.28 (normal canonical form predicate) is the
companion predicate for the irreducible/primitive route. ✔

**Theorem 9.11 (Vandermonde separation).**
Correct. Standard Vandermonde invertibility argument.

⚠️ **Slight imprecision in the statement.** The theorem says "If μ_1, …, μ_r
are pairwise distinct complex numbers and ∑_{k=1}^r c_k μ_k^N = 0 for
N = 0, 1, …, r − 1, then c_k = 0 for all k." The quantification is over
N = 0, …, r − 1, which gives exactly r equations for r unknowns. This is
correct: the Vandermonde matrix V with V_{Nk} = μ_k^N is invertible when the
μ_k are distinct, so Vc = 0 implies c = 0. ✔

However, this theorem is never directly used in the chapter. The block
separation argument (Lemma 9.12) uses the *spectral gap* to peel off blocks,
not the Vandermonde argument. The Vandermonde theorem is presumably
included for completeness or for use in Chapter 10 (coefficient
convergence). This should be noted: it is a "stored" result for later use.

**Lemma 9.12 (Block separation core).**
This is the technical heart of the chapter. The blueprint's proof sketch is
very compressed, so let me give the full argument.

**Statement:** Let ((μ_k), (A_k)) satisfy the canonical form predicate, and
let (B_k) be injective tensors satisfying TP normalization. If
∑_k μ_k^N (V^{(N)}(A_k)_σ − V^{(N)}(B_k)_σ) = 0 for all N ≥ 1 and all
spin configurations σ, then each pair (A_k, B_k) generates the same MPV
family.

**Full proof by strong induction on r (number of blocks).**

*Base case (r = 1):* The hypothesis gives μ_1^N (V^{(N)}(A_1)_σ −
V^{(N)}(B_1)_σ) = 0 for all N, σ. Since μ_1 ≠ 0 (condition 4 of the
canonical form predicate), divide by μ_1^N to get V^{(N)}(A_1)_σ =
V^{(N)}(B_1)_σ for all N, σ. This is exactly "same MPV." ✔

*Inductive step (r ≥ 2):* Assume the result for all collections with
fewer than r blocks. We need to show A_0 and B_0 generate the same MPV
(using 0-indexing for the leading block, which has the largest |μ_0|).

Step 1 (Take overlaps with A_0): Contract the hypothesis with
V^{(N)}(A_0)_σ^* (i.e., take the inner product with the MPV of A_0).
This gives:

∑_k μ_k^N (O_{A_0 A_k}(N) − O_{A_0 B_k}(N)) = 0

where O_{A_0 A_k}(N) = ∑_σ V^{(N)}(A_0)_σ^* V^{(N)}(A_k)_σ is the
(unnormalized) overlap.

Actually, more precisely: the overlap O_{AB}(N) as defined in Chapter 2
is tr(F^N_{AB}) where F_{AB} is the mixed transfer operator. What
matters is that O_{A_0 A_k}(N) can be expressed as tr(F^N_{A_0 A_k}),
and the spectral radius controls the growth.

Step 2 (Isolate the leading block): Divide by μ_0^N:

(O_{A_0 A_0}(N) − O_{A_0 B_0}(N)) + ∑_{k≥1} (μ_k/μ_0)^N (O_{A_0 A_k}(N) − O_{A_0 B_k}(N)) = 0.

Since |μ_k/μ_0| < 1 for k ≥ 1 (strictly decreasing moduli, condition 3),
and overlaps are bounded (since all tensors are TP-normalized, the
eigenvalue bound Theorem 6.10/6.11 gives |O_{A_0 A_k}(N)| ≤ C for some
constant C), each term in the sum over k ≥ 1 vanishes as N → ∞.

Therefore: O_{A_0 A_0}(N) − O_{A_0 B_0}(N) → 0 as N → ∞.

Step 3 (Identify leading blocks): By condition 5 of the canonical form
predicate, O_{A_0 A_0}(N) → 1. Combined with Step 2:
O_{A_0 B_0}(N) → 1.

Now we use the spectral gap. If A_0 and B_0 were *not* gauge-phase
equivalent, then:
- If D_{A_0} = D_{B_0}: Theorem 6.17 gives O_{A_0 B_0}(N) → 0.
- If D_{A_0} ≠ D_{B_0}: Theorem 6.15 gives O_{A_0 B_0}(N) → 0.

In either case O_{A_0 B_0}(N) → 0, contradicting O_{A_0 B_0}(N) → 1.
So A_0 and B_0 *must* be gauge-phase equivalent (Definition 2.13), which
implies they generate the same MPV family.

⚠️ **The proof sketch cites "the proportional FT (Theorem 8.23)" but the
actual argument is a contrapositive of Theorem 6.17 (overlap decay).**
Theorem 8.23 requires proportional MPV (V^{(N)}(A)_σ = c_N V^{(N)}(B)_σ),
which is not what we have. What we have is O_{A_0 B_0}(N) → 1, which is
the overlap converging to 1 — a weaker condition. The correct citation is
Theorem 6.17 (contrapositive). This is not a mathematical error (the
conclusion is the same) but it matters for Lean: the proof term would
invoke Theorem 6.17, not Theorem 8.23.

Step 4 (Peel off the leading block): Since A_0 and B_0 have the same
MPV, V^{(N)}(A_0)_σ = V^{(N)}(B_0)_σ for all N, σ. Substituting back:

∑_{k≥1} μ_k^N (V^{(N)}(A_k)_σ − V^{(N)}(B_k)_σ) = 0 for all N, σ.

This is the same hypothesis with r − 1 blocks. The remaining data
((μ_k)_{k≥1}, (A_k)_{k≥1}) still satisfies the canonical form predicate:
- Injective: inherited. ✔
- TP: inherited. ✔
- Strictly decreasing moduli: removing the largest preserves ordering. ✔
- Nonzero weights: inherited. ✔
- Self-overlap convergence: inherited. ✔

The comparison tensors (B_k)_{k≥1} still satisfy injectivity and TP. ✔

By the induction hypothesis, each pair (A_k, B_k) for k ≥ 1 generates
the same MPV family. Combined with Step 3 (A_0, B_0 same MPV), the
result follows. ✔

⚠️ **One subtlety in Step 2.** I claimed the overlaps are bounded. More
precisely: O_{A_0 A_k}(N) = tr(F^N_{A_0 A_k}) where F_{A_0 A_k} is the
mixed transfer operator. By Theorem 6.11, ρ(F_{A_0 A_k}) ≤ 1 for TP-
normalized tensors. So |O_{A_0 A_k}(N)| ≤ D² · ρ(F_{A_0 A_k})^N ≤ D²
(using submultiplicativity of the operator trace and the spectral radius
bound). Actually, the bound is slightly more subtle: tr(F^N) is not simply
bounded by D² · ρ(F)^N (the operator trace can exceed the spectral
radius). The correct bound is: for any ε > 0, |tr(F^N)| ≤ C_ε (ρ(F) + ε)^N
for some constant C_ε (Gelfand formula). Since ρ(F_{A_0 A_k}) ≤ 1,
the overlaps grow at most polynomially (or are bounded). Meanwhile,
(μ_k/μ_0)^N decays exponentially, so the product vanishes. ✔

**Theorem 9.13 (Block separation from canonical form).**
Correct. Applies Lemma 9.12 to the identity obtained from same-MPV of
the block-diagonal tensors. The proof correctly notes that the canonical
form predicate supplies all needed hypotheses for (A_k), while TP
normalization and injectivity are assumed for (B_k).

⚠️ **Asymmetry in hypotheses.** The canonical form predicate applies to
(A_k), not to (B_k). In particular, (B_k) are not required to satisfy
condition (5) (self-overlap convergence). This is correct — the peeling
argument only needs the self-overlap of A_0 (the "test" tensor), not of B_0.
However, it does require O_{B_0 B_0}(N) to remain bounded, which is
automatic since all overlaps of TP-normalized tensors are bounded by 1
(Theorem 6.10/6.11).

**Theorem 9.14 (Block separation from normal canonical form).**
NEW in v2. Correct. The proof parallels Theorem 9.13 but uses:
- Theorem 8.29 to supply the self-overlap convergence (replacing condition
  5 of Definition 9.8),
- Theorem 8.30 to identify the leading comparison block from the
  nondecaying mixed overlap.

**Cross-reference check:**
- "Theorem 8.29" = self-overlap derived in normal canonical form. ✔
- "Theorem 8.30" = modulus-one eigenvalue rigidity for irreducible TP
  blocks. ✔

⚠️ **Subtle point about Theorem 8.30.** In the block-injective route
(Theorem 9.13), the leading-block identification comes from the spectral
gap: A_0 and B_0 are both injective and TP, so O_{A_0 B_0}(N) → 1 forces
gauge-phase equivalence by Theorem 6.12/6.17. In the normal-canonical
route (Theorem 9.14), A_0 is only irreducible (not necessarily injective),
so Theorem 6.17 does not directly apply. Instead, Theorem 8.30 is used:
it shows that a modulus-one eigenvector for the mixed transfer map forces
gauge-phase equivalence under irreducibility. The proof sketch in the
blueprint is compressed but correct.

⚠️ **Forward dependency on (B_k) being irreducible.** Theorem 9.14
assumes "(B_k) be irreducible tensors of the same bond dimensions." This
is stronger than the injectivity assumption in Theorem 9.13. The reason:
Theorem 8.30 requires irreducibility of *both* tensors in the pair. In the
block-injective route, injectivity suffices because injective tensors have PD
fixed points and Theorem 6.12 handles the spectral argument. In the
normal-canonical route, irreducibility is the correct substitute.

**Theorem 9.15 (Canonical form fundamental theorem, same-structure
version).**
Correct. Combines Theorem 9.13 (block separation) with Theorem 9.7
(per-block same MPV → global gauge equivalence).

⚠️ **Naming note.** This is called "same-structure version" because it
assumes both block-diagonal tensors have the same block structure (same
number of blocks, same scaling factors, same bond dimensions). The
general version (different block structures) requires the BNT permutation
machinery of Chapter 10 and the full assembly of Chapter 11.

---

## 5. Cross-Chapter Consistency

### DS → TP correction (resolved)

The Chapter 8 cleanup checklist item 11 flagged: "Check Chapter 9
consistency — the canonical form predicate (Definition 9.8) may still use DS
gauge language from v1, which would be inconsistent with v2's Chapter 8."

**Resolution:** v2 Definition 9.8 now uses "TP normalization." ✔ This is
consistent with:
- Chapter 4 (DS correction, reviewed)
- Chapter 5 (DS correction, reviewed)
- Chapter 6 (DS correction, reviewed)
- Chapter 7 (Definition 7.38 uses TP, reviewed)
- Chapter 8 (Theorem 8.24 uses TP, reviewed)

### v1 remnant in v2 Chapter 8

⚠️ However, I note that v1's Chapter 8 (blueprint20260302.pdf) still uses
"DS gauge" in several places:
- v1 Theorem 8.24 condition 2: "each A_k is in DS gauge"
- v1 Theorem 8.26: "Assume that A is doubly stochastic"
- v1 Remark 8.25: "DS gauge"

In v2 Chapter 8, Theorem 8.24 was checked in the Chapter 8 review and
confirmed to use TP. But Theorem 8.26 in v2 still says "doubly stochastic"
according to the Chapter 8 review (which noted the v2 proof uses the
adjoint-fixed-point route, correctly). This is because blocking to achieve
primitivity does require the DS condition (or the adjoint route). The
Chapter 8 review already covers this. No new inconsistency from
Chapter 9's perspective.

### Chapter 3 cross-references

All Chapter 3 cross-references in Chapter 9 have been updated to v2
numbering:
- Thm 9.3 cites Thm 3.9 (Skolem–Noether) ✔
- Thm 9.6 cites Thms 3.6, 3.7 and Lemma 3.10 ✔
- Thm 9.7 cites Thm 3.11 (single-block FT) ✔

### Chapter 6 cross-references

Lemma 9.12 implicitly uses:
- Theorem 6.15 (rectangular overlap decay, for cross-block overlaps when
  D_j ≠ D_k)
- Theorem 6.17 (overlap decay for non-gauge-phase-equivalent tensors of
  same dimension)

These are correctly cited in the v1 proof (which is more detailed) and
implicitly present in the v2 proof sketch. The Chapter 6 review confirmed
both theorems are correct in v2.

### Chapter 8 cross-references

- Thm 9.7 cites Thm 8.4 (global gauge from block gauge) ✔
- Lemma 9.12 proof cites Thm 8.23 (proportional MPV → gauge-phase
  equivalence) — technically the argument uses Thm 6.17 contrapositive,
  see §4 discussion above
- Thm 9.14 cites Thms 8.29 and 8.30 ✔

### Chapter 2 dependencies

Definition 9.8 uses the notion of "injective" tensor (Definition 2.17),
"TP normalization" (which is the condition ∑_i (A^i)† A^i = 𝟙 from
Definition 4.7/4.12), and "self-overlap" (Definition 2.26). These are all
consistent.

### Forward dependencies on Chapter 10

Theorem 9.11 (Vandermonde separation) is not used in Chapter 9 itself.
It is stored for use in Chapter 10 (coefficient convergence). This should
be noted: the theorem is a "forward deposit" for Chapter 10.

Theorem 9.15 (CF FT, same-structure version) is the starting point for
Chapter 10's BNT theory. Chapter 10 extends it to different block
structures via the BNT permutation machinery.

### Forward dependencies on Chapter 11

Chapter 11 (Full Assembly) combines Chapter 9's block separation
(Theorems 9.13/9.14) with Chapter 10's BNT permutation (Theorems
10.7/10.8) to produce the full Fundamental Theorem. No issues from
Chapter 9's perspective.

### Two meanings of "normal"

The Chapter 8 review flagged the "two meanings of normal" issue (X-1).
Chapter 9 does not use the word "normal" in the Definition 2.19 sense;
it only refers to the "canonical form predicate" (Definition 9.8) and the
"normal canonical form predicate" (Definition 8.28). Remark 9.10 correctly
distinguishes the two. No new issues from Chapter 9.

---

## 6. Deviation Analysis: Blueprint vs Literature

The chapter header says: "The approach follows [PGVWC07] and [CPGSV21]."
This is misleading. The chapter uses essentially **none** of the proof
techniques from either paper. The algebraic decomposition in §9.1 is
standard semisimple algebra (Wedderburn–Artin + Skolem–Noether); the
block separation in §9.3 uses an induction-on-blocks argument via the
spectral gap that appears in neither reference. What the chapter shares
with the papers is the *goal* (uniqueness of the canonical form) and the
*algebraic framework* (automorphisms of product algebras), not the proof
methods.

### Deviation 1: Block separation technique

**[PGVWC07] (Theorem 7):** The paper proves uniqueness of the
TI canonical form for a *single-block* tensor (condition C1 = injectivity;
condition C2 = unique eigenvalue of modulus 1). The proof works as
follows:

1. Lift the TI-MPS to an OBC representation using D² × D² matrices
   A^[j]_i for the middle sites of the chain.
2. From same-MPV of two TI canonical representations (B_i, C_i), and
   uniqueness of the OBC canonical form (Theorem 2), extract D⁴
   invertible D² × D² intertwining matrices W_k satisfying
   W_k (C_i ⊗ 𝟙) = (B_i ⊗ 𝟙) W_{k+1}.
3. Apply a Horn–Johnson lemma ([HJ91, Thm. 4.4.14] = their
   Proposition 2): the solution space of W(C_i ⊗ 𝟙) = (B_i ⊗ 𝟙)W is
   S ⊗ M_n, where S is the solution space of XC_i = B_iX.
4. Use their Proposition 1 (a linear-algebraic lemma about dependent
   solutions) to extract a single nonzero R with RC_i = (1/x) B_i R.
5. Use the fixed-point structure (Λ = ∑ B_i† Λ B_i and uniqueness of
   the fixed point) to show |x|² = 1, then RR† = 𝟙 (using that B has
   a single block), so R is unitary.

This proof is inherently *single-block*: condition C1 guarantees a
single block in the canonical form, and the OBC lifting produces the
D² × D² matrices needed for the intertwining argument. The paper does
not prove block separation for multi-block canonical forms by this
method.

**[CPGSV21] (Theorem 4.1):** The review paper deduces block separation
from BNT uniqueness. The argument goes:

1. Start with a BNT decomposition (Definition 4.2 in the paper).
2. Use the linear independence of block MPVs (for large N) to extract
   per-block coefficients from the global MPV identity.
3. Deduce per-block same-MPV from the coefficient matching.
4. Apply the single-block fundamental theorem to each matched pair.

The key point: [CPGSV21] works "from above" — it assumes the BNT
decomposition exists and deduces block separation from it. The blueprint
works "from below" — it proves block separation directly by peeling off
the dominant block using the spectral gap, without assuming a BNT
structure.

**Blueprint (Lemma 9.12 / Theorem 9.13):** The proof uses:

1. Induction on the number of blocks r.
2. At each step, take overlaps with the leading block A_0.
3. Cross-block contributions from k ≥ 1 decay as (|μ_k|/|μ_0|)^N → 0
   (spectral gap).
4. The surviving term gives O_{A_0 A_0}(N) − O_{A_0 B_0}(N) → 0.
5. Contrapositive of Theorem 6.17 gives gauge-phase equivalence of the
   leading blocks.
6. Peel off the leading block and apply induction.

**Assessment:** The blueprint's technique is genuinely different from both
papers. It relies on the spectral gap (Chapter 6) and the overlap
convergence (Chapter 6, §6.7) as the main engine, combined with the
strictly decreasing moduli to kill cross-terms. Neither [PGVWC07] nor
[CPGSV21] uses this induction-on-blocks-via-spectral-gap strategy.

The v1 blueprint had an explicit paragraph acknowledging this deviation
(after Theorem 9.12/v1): "In [PGVWC07], the uniqueness of the canonical
form is proved differently... In [CPGSV21], the block separation is
deduced from the BNT uniqueness... Our formalization makes the
separation explicit by induction on the number of blocks r." **v2 removes
this paragraph.** This is a regression in transparency — the deviation
should be acknowledged. See cleanup item 6.

### Deviation 2: The canonical form predicate itself

**[PGVWC07] (Theorem 4, conditions):** The paper's canonical form has
three conditions per block:
1. ∑_i A^j_i (A^j_i)† = 𝟙  (left normalization),
2. ∑_i (A^j_i)† Λ^j A^j_i = Λ^j for diagonal PD Λ^j (right fixed
   point),
3. 𝟙 is the *unique* fixed point of X ↦ ∑ A^j_i X (A^j_i)†.

This is the "doubly stochastic" setup: condition 1 is TP, condition 2
gives a PD fixed point for the adjoint, and condition 3 is a uniqueness
requirement equivalent to irreducibility of the transfer map.

**Blueprint (Definition 9.8):** The canonical form predicate uses:
1. Injective,
2. TP normalization ∑_i (A^i_k)† A^i_k = 𝟙,
3. Strictly decreasing moduli,
4. Nonzero weights,
5. Self-overlap convergence O_{A_k A_k}(N) → 1.

Notable differences:
- The blueprint uses *injectivity* (condition 1) rather than the paper's
  condition 3 (unique fixed point). Injectivity is strictly stronger than
  irreducibility (injective ⟹ S₁(A) = M_D(ℂ) ⟹ algebraically
  spanning ⟹ irreducible), so this is a stronger hypothesis.
- The blueprint does not require the Λ^j fixed point (condition 2 of the
  paper). Instead, it requires self-overlap convergence (condition 5),
  which is a *consequence* of primitivity.
- The blueprint uses right-normalization ∑_i (A^i)† A^i = 𝟙 (TP for
  ℰ_A), while the paper uses left-normalization ∑_i A_i A_i† = 𝟙.
  These are related by the gauge transformation A_i ↦ X^{-1/2} A_i X^{1/2}
  where X is the PD fixed point, but they are not the same condition.

⚠️ **The normalization convention differs.** [PGVWC07] Theorem 4
condition 1 is ∑_i A^j_i (A^j_i)† = 𝟙, which means the transfer map
X ↦ ∑ A_i X A_i† is *unital* (not trace-preserving). The blueprint's
condition ∑_i (A^i)† A^i = 𝟙 means the transfer map X ↦ ∑ A_i X A_i†
is *trace-preserving*. These are dual conditions. The paper's canonical
form is in the "unital gauge" while the blueprint's is in the "TP gauge."
Both are achievable from the other by a gauge transformation using the
PD fixed point (Theorem 5.10 in the blueprint). This is not an error
but it is a significant notational deviation from [PGVWC07] that should
be noted, since it affects all formulas involving overlaps and spectral
gaps.

### Deviation 3: §9.1 algebraic decomposition

**[CPGSV21, §IV.A]:** The paper discusses the automorphism structure of
∏ M_{D_k}(ℂ) in the MPS context and derives the permutation +
per-block conjugation decomposition.

**Blueprint (Theorems 9.1–9.3):** The same result, stated from first
principles (block ideals are atoms, Skolem–Noether for each block). The
mathematical content is identical. The blueprint does not use any
technique *from* [CPGSV21] that isn't standard algebra; it simply proves
the same standard result.

**Assessment:** This is a fair citation — the blueprint proves the same
standard algebraic result and cites [CPGSV21, §IV.A] as the place where
it appears in the MPS literature. No deviation in substance.

### Deviation 4: §9.2 linear extension assembly

**[PGVWC07]:** The single-block uniqueness (Theorem 7) uses the OBC
intertwining argument, not the linear-extension approach.

**[CPGSV21]:** Uses the BNT framework to derive block matching.

**Blueprint (§9.2):** Assembles per-block linear extensions T_k into a
product algebra automorphism, then applies the §9.1 decomposition.
This is the blueprint's own construction — it lifts the Chapter 3
single-block linear extension to the multi-block setting. Neither paper
takes this route; the blueprint's approach is a natural multi-block
generalization of the Chapter 3 technique.

### Summary of deviations

| Component | [PGVWC07] technique | [CPGSV21] technique | Blueprint technique |
|---|---|---|---|
| Single-block uniqueness | OBC lift + Horn–Johnson intertwining | (cites [PGVWC07]) | Chapter 3 linear extension + Skolem–Noether (Thm 3.11) |
| Block separation | Not addressed (single-block only) | Deduced from BNT uniqueness | Induction on blocks via spectral gap (Lemma 9.12) |
| Multi-block matching | Not addressed | BNT permutation rigidity | Product algebra automorphism decomposition (§9.1–9.2) |
| Normalization convention | Unital gauge (∑ A_i A_i† = 𝟙) | Unital gauge | TP gauge (∑ A_i† A_i = 𝟙) |

**Recommendation:** The chapter header should be revised from "The
approach follows [PGVWC07] and [CPGSV21]" to something like: "The
*results* correspond to the canonical form uniqueness of [PGVWC07] and
the block separation of [CPGSV21]. The *proof technique* — induction on
blocks via the spectral gap — is specific to this formalization."

### [Wol12] (Wolf, Quantum Channels)

Citations in Definition 9.8 verified:
- [Wol12, Thm. 6.7, item 3]: primitive channel convergence ✔
- [Wol12, Thm. 6.8]: CP primitive maps ✔
These are reference citations for context, not proof techniques. No
deviation.

---

## 7. AI-Style Language Issues

The chapter is well-written and concise. A few items to flag:

- **"Pi-algebra linear extension" (§9.2 title):** The "Pi-algebra" naming
  is presumably short for "product algebra" (∏_k M_{D_k}(ℂ)). This is
  nonstandard — neither mathematicians nor physicists would call this a
  "Pi-algebra." Standard terms would be "product algebra" or "semisimple
  algebra." Recommendation: rename to "Product algebra linear extension."

- **"Only this one-sided normalization is part of the predicate"
  (Definition 9.8 remark):** Clear and well-phrased. No issue.

- **"The canonical form predicate retains condition (5) explicitly because
  the overlap limit may also be assumed directly" (Remark 9.9):** Slightly
  awkward. Suggested: "The predicate retains condition (5) as an explicit
  hypothesis because it can be verified independently of primitivity."

---

## 8. Cleanup Checklist

1. **§9.1: document the ring → algebra two-level structure.** The Lean
   code (`BlockPermutation.lean`) proves the block ideal permutation at
   the ring level (`RingEquiv`), then upgrades to `AlgEquiv` for dimension
   preservation and the Skolem–Noether decomposition. The blueprint's
   Theorem 9.1 is correctly stated at the ring level, but the transition
   to algebra automorphisms in Theorems 9.2–9.3 is silent. The blueprint
   should note where and why the upgrade is needed: (a) dimension
   preservation requires ℂ-vector space structure, (b) Skolem–Noether
   requires central simple algebra structure, and (c) scalar compatibility
   of the per-block componentMap requires ℂ-linearity.

2. **Definition 9.5: reclassify as a theorem or merge into Theorem 9.6.**
   As written, it contains a nontrivial claim (the T_k are algebra
   homomorphisms and assemble into an automorphism) that is not justified
   until Theorem 9.6.

3. **Lemma 9.12 proof: correct the citation of Theorem 8.23.** The actual
   argument uses the contrapositive of Theorem 6.17 (overlap decay), not
   Theorem 8.23 (proportional MPV). Make the chain explicit:
   O_{A_0 B_0}(N) → 1 ≠ 0, so by contrapositive of Theorem 6.17, A_0
   and B_0 are gauge-phase equivalent, hence same MPV.

4. **Theorem 9.6: clarify that the permutation is trivial.** In the
   per-block same-MPV setting, the assembled automorphism is
   block-diagonal, so σ = id. The nontrivial permutation only appears
   when combining with the block separation. The current statement is
   not wrong but is misleading.

5. **Note that Theorem 9.11 (Vandermonde) is unused in Chapter 9.**
   It is a stored result for Chapter 10. Add a forward reference.

6. **§9.2 title: rename "Pi-algebra" to "Product algebra."**

7. **Restore the deviation acknowledgment (removed from v1).** v1 had an
   explicit paragraph after Theorem 9.12 acknowledging that the proof
   technique differs from both [PGVWC07] and [CPGSV21]. v2 removes this.
   Given the extent of the deviations (see §6), this paragraph should be
   restored and expanded. More importantly, the chapter header "The
   approach follows [PGVWC07] and [CPGSV21]" should be revised to
   distinguish the results (which do correspond to the literature) from
   the proof techniques (which are entirely different).

8. **Verify [CPGSV21, §IV.A] section numbering** against the actual paper.

9. **Note the normalization convention deviation.** Definition 9.8 uses TP
   gauge (∑ (A^i)† A^i = 𝟙), while [PGVWC07] Theorem 4 uses the dual
   unital gauge (∑ A_i A_i† = 𝟙). The two are related by a gauge
   transformation, but this should be noted explicitly since it affects the
   direction of all spectral-gap arguments in §9.3.

10. **Notation: define the →̃ arrow.** Used in Theorems 9.1 and
    Definition 9.5 for two different kinds of isomorphism (ring vs
    ℂ-algebra) without definition. Either drop it and state "isomorphism"
    in words, or define it once.

11. **Notation: define T(M)_k.** The block-component notation for elements
    of the product algebra needs a one-line definition.

12. **Notation: add a local recall of O_{AB}(N).** The self-overlap and
    mixed overlap appear throughout §9.3 but are defined only in Chapter 2.

---

## 8a. Cross-Cutting Recommendation: Documenting Type-Level Transitions

The ring → algebra issue in §9.1 (cleanup item 1) is an instance of a
broader pattern that affects the entire blueprint. The general problem:

**The Lean type system forces every morphism to carry its structure
explicitly** — a ring homomorphism (`≃+*`), a ℂ-algebra equivalence
(`≃ₐ[ℂ]`), a linear map, a multiplicative map, etc., are all different
types, and upgrading from one to another requires an explicit proof step.
The blueprint, written in informal mathematics, routinely makes these
transitions silently. This creates a systematic gap between the blueprint
and the Lean code: the blueprint reads as if the proof is a smooth
narrative, while the Lean code reveals intermediate type-coercion steps
that are nontrivial.

**Instances identified in Chapter 9:**

1. **§9.1: Ring isomorphism → ℂ-algebra equivalence.** Theorem 9.1 works
   for `RingEquiv` on simple rings. Theorems 9.2 and 9.3 require
   `AlgEquiv`. The blueprint switches silently. The Lean code tracks this
   via separate types and proves scalar compatibility
   (`componentMap_map_smul_of_algEquiv`) only at the algebra level.

2. **§9.2: Linear map → multiplicative map → algebra homomorphism →
   algebra automorphism.** The per-block linear extension T_k goes through
   four type transitions in the proof of Theorem 9.6:
   - Linear map (from Theorem 3.6: T_k is a ℂ-linear map)
   - Multiplicative (from Theorem 3.7: T_k(MN) = T_k(M)T_k(N))
   - Bijective (from Theorem 3.8: nonzero multiplicative → bijective)
   - Unital, hence algebra homomorphism (from Lemma 3.10)
   Each step is a separate theorem in the Lean code. The blueprint
   compresses them into "Each T_k exists uniquely and is multiplicative
   by Theorems 3.6 and 3.7. Promotion to algebra homomorphisms (Lemma
   3.10) and assembly into the product gives an algebra automorphism."

3. **§9.3: Tensors as families vs single matrices.** The notation A_k
   denotes a family {A^i_k}_{i=1}^d of matrices, but in the overlap
   formulas it is treated as a single object indexing a transfer map.
   This is not a morphism-type issue per se, but a similar pattern of
   compressed notation that hides a type distinction the Lean code must
   make explicit.

**Expected instances in other chapters (to check during Chapters 10–11
review):**

- **Channel theory (Chapters 4–5):** The distinction between positive
  maps, completely positive maps, trace-preserving maps, and channels
  (CP + TP) involves similar type transitions. A "channel" in the
  blueprint is often just a CP map that happens to be TP, but in Lean
  these are separate typeclasses or bundled structures.

- **Spectral theory (Chapter 6):** The mixed transfer operator F_{AB} is
  defined as a linear map, but the spectral radius bound (Theorem 6.10)
  requires properties of the underlying channel (KS inequality, TP
  normalization). The blueprint moves freely between "eigenvalue of F_{AB}"
  and "eigenvalue of the transfer map of a TP tensor" without flagging
  the structure that makes the bound work.

- **Wielandt bound (Chapter 7):** The word span S_n(A) and cumulative
  span T_n(A) are subspaces of M_D(ℂ), but the normality condition
  requires them to equal M_D(ℂ) as an *algebra* (not just as a vector
  space). The distinction between "spanning as a vector space" and
  "generating as an algebra" is another type-level transition.

- **BNT theory (Chapter 10):** The BNT decomposition involves
  block-diagonal tensors, coefficient arrays, and overlap matrices. The
  type of the coefficient array (convergent sequences with nonzero
  limits) is a structured object in Lean but is treated as a plain
  sequence in the blueprint.

**General recommendation for the blueprint:** Each chapter should include
a brief "formalization notes" paragraph (or remark) identifying the key
type-level transitions in that chapter's proofs. This serves two
purposes:

1. It helps the Lean formalizer know where the nontrivial coercion steps
   are, rather than discovering them during formalization.
2. It helps the mathematical reader understand the proof structure at a
   level of detail that the compressed proof sketches omit.

This does not require changing the theorem statements — the informal
mathematics can remain as-is. The addition is purely documentary: "Note:
the proof of Theorem X.Y requires upgrading the map T from a ring
homomorphism to an algebra equivalence, which is verified in the Lean
code via [specific lemma]." This is the kind of annotation that makes a
blueprint genuinely useful for a formalization project, rather than just a
condensed textbook.

---

## 9. Final Assessment

Chapter 9 is mathematically correct in v2. The most important v1 → v2
change is the DS → TP correction in Definition 9.8 and Theorem 9.13,
which resolves item 11 of the Chapter 8 cleanup checklist. The addition of
Theorem 9.14 (normal-canonical block separation) extends the block
separation to the irreducible/primitive route, paralleling the two-route
structure established in Chapter 8.

The most significant finding of this review is the extent of the deviation
from the cited literature. The chapter header claims to follow [PGVWC07]
and [CPGSV21], but the proof techniques are entirely different:
- [PGVWC07] proves single-block uniqueness via OBC lifting and
  Horn–Johnson matrix-equation intertwining;
- [CPGSV21] deduces block separation from BNT uniqueness;
- The blueprint proves block separation by induction on the number of
  blocks, using the spectral gap to peel off the dominant block.

These are three genuinely different proof strategies arriving at related
(but not identical) conclusions. The blueprint's approach is arguably
the cleanest for formalization, since it avoids both the OBC detour of
[PGVWC07] and the BNT dependency of [CPGSV21]. But the chapter should
be transparent about this deviation rather than claiming to "follow" the
papers.

The normalization convention also differs: [PGVWC07] uses the unital
gauge (∑ A_i A_i† = 𝟙) while the blueprint uses the TP gauge
(∑ (A^i)† A^i = 𝟙). These are dual conditions related by a gauge
transformation, but the difference propagates through all overlap and
spectral-gap arguments.

A new cross-cutting issue identified in this review (§8a): the blueprint
systematically omits type-level transitions that the Lean code must make
explicit. The ring → algebra transition in §9.1 is the clearest example,
but the pattern recurs in §9.2 (linear → multiplicative → bijective →
unital → automorphism) and is expected to appear throughout the remaining
chapters. The recommendation is to add brief "formalization notes" to
each chapter documenting these transitions. This would make the blueprint
substantially more useful as a formalization guide.

At the proof level, the only issue is the citation of Theorem 8.23 in
Lemma 9.12's proof sketch, where the actual argument uses Theorem 6.17's
contrapositive. All other issues are structural (Definition 9.5
misclassification, §9.2 naming, unused Theorem 9.11).

The chapter correctly serves as the bridge between the canonical form
reduction (Chapter 8) and the BNT/full assembly (Chapters 10–11).
