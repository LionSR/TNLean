# **Synthesized Review of the Final Blueprint Annotations**

Project: Fundamental Theorem of Matrix Product States formalization  
Basis: blueprint\_annotations.docx, the annotated blueprint PDF, and the subsequent corrected audit discussion  
Scope: Chapters 2–13 of the annotated blueprint, with global issues and proof structure  
Purpose: Produce a clean, exportable review that records the mathematical content of the margin notes, corrects misreadings, and states the corresponding fixes in standard mathematical language.

## **Overview**

The original Word document is a useful record of the annotations, but it should not be treated as final. Several items in it are correct, several are too weak, and a few misidentify the actual mathematical issue. The main point is that the single-block theorem and the basic Perron–Frobenius infrastructure are not where the main difficulty lies. The delicate part is the passage from strict or same-structure block-comparison lemmas to the full canonical-form Fundamental Theorem, where repeated blocks and equal-modulus sectors have to be handled explicitly.

The main conclusions are:

1. The single-block algebraic proof is structurally good.

2. The channel/Perron–Frobenius/Wielandt material is mostly plausible, but the exposition is more detailed than necessary and some statements need sharper hypotheses.

3. The terminology around normality, block injectivity, normalization, and transfer-map adjoints must be made precise.

4. Strict-modulus and one-copy-per-sector hypotheses must be clearly marked as subcases. They are not harmless conventions.

5. Equal-modulus and repeated-copy BNT sectors are essential for the theorem in the paper.

6. Projection-limit arguments for non-dominant blocks should be replaced by coefficient comparison using full combined-family linear independence.

7. The final blueprint should distinguish:

   * the statement from the literature,

   * the formal statement currently proved,

   * the remaining implications needed to pass from one to the other.

## **The theorem statement being checked**

Before auditing the blueprint, one must fix which theorem is being formalized. There are at least three distinct targets.

### **Level A: Single-block injective/normal FT**

For injective or normal single-block tensors, equality of MPV families implies similarity gauge, possibly up to a scalar phase depending on whether the theorem is equal-MPV or proportional-MPV.

This is the algebraic core. The proof should run through trace agreement, linear extension, multiplicativity, automorphism of a full matrix algebra, and Skolem–Noether.

### **Level B: Canonical-form multi-block FT**

For tensors already in canonical form, equality of all MPVs implies matching of normal blocks, matching of weights after phase absorption, and global gauge equivalence of the block-diagonal tensors.

This is the literature-level Fundamental Theorem as usually stated for tensors in canonical form.

### **Level C: Fully unconditional arbitrary-tensor theorem**

Starting from arbitrary tensors, first reduce to canonical form: remove nilpotent/zero triangular parts, decompose into irreducible blocks, normalize/gauge, block to remove periodicity, and obtain normal/primitive blocks. Then apply the canonical-form uniqueness theorem.

This is stronger than the usual theorem statement and requires a separate existence reduction.

Rule: One should not let a proof of Level B be presented as Level C unless the upstream canonical-form existence reduction is explicitly chained into the final theorem.

## **Proof strategy**

For the canonical-form multi-block theorem, the proof structure should be:

same MPV  
 \-\> trace/coefficient equality  
 \-\> single-block gauge or gauge-phase matching  
 \-\> block separation / BNT linear independence  
 \-\> block permutation  
 \-\> weight and phase matching  
 \-\> global gauge equivalence

For the arbitrary-tensor theorem, prepend:

arbitrary tensor  
 \-\> remove upper-triangular, nilpotent, and zero parts  
 \-\> irreducible live blocks  
 \-\> TP or canonical gauge  
 \-\> blocking removes periodicity  
 \-\> primitive/normal blocks  
 \-\> BNT/canonical form

Every theorem used in the main proof should be checked against this strategy: it should either be one of these implications or be moved to an appendix or a technical formalization section.

## **Global points**

### **G1. Block-injectivity terminology is overloaded**

The document uses phrases close to “block injective” in two different senses:

* $L$-block injective: products of length $L$ span the full matrix algebra.

* block-injective canonical form: a direct sum of injective or eventually injective blocks.

This is a real terminology problem, not merely a request to “verify injectivity.”

Reserve $L$-block injective for injectivity after blocking. Use block-injective canonical form only for direct sums of injective blocks. Make this distinction explicit where both notions appear.

### **G2. Blocking is introduced too late**

Blocking appears after normality, even though normality is discussed using injectivity after blocking.

This is not a logical circularity, because normality can be stated directly in terms of length-L products. But it is an expository dependency problem.

Either move the blocking section earlier, or add a forward reference at the normality definition: “The formal blocked tensor is introduced below; here the condition is stated directly in terms of length-L words.”

### **G3. “Normalized” must always specify the normalization**

“Normalized” is used for several different conditions: TP normalization, unital normalization, right/left canonical gauges, and spectral-radius normalization.

This matters because the transfer map

E\_A(X) \= sum\_i A^i X (A^i)^dagger

is trace-preserving when

sum\_i (A^i)^dagger A^i \= 1,

but unital when

sum\_i A^i (A^i)^dagger \= 1\.

Kadison–Schwarz applies to a unital map. In a TP-normalized MPS convention, this is usually the adjoint map.

Replace bare “normalized” by the relevant condition: TP-normalized, unital-normalized, right-canonical, left-canonical, or spectral-radius-normalized.

### **G4. Kadison–Schwarz must be applied to the correct map**

The blueprint states Kadison–Schwarz for unital Kraus maps, but MPS transfer maps are often TP-normalized.

The theorem is correct, but downstream proofs must say whether they apply KS to E or to E^\*.

Record the convention: “For a TP-normalized transfer map, apply Kadison–Schwarz to the adjoint map.”

### **G5. Repeated definitions and theorem restatements should be marked as recalls**

Several chapters restate Kraus maps, adjoints, unitality, trace preservation, and KS inequalities as if they were new.

Repetition is acceptable only if it improves local readability and is labelled as recall.

Present repeated definitions as recalls, or refer back to the original definitions.

### **G6. Editorial/source remarks should not be inside theorem statements**

Several theorem statements end with source-location or proof-role commentary.

Theorem statements should contain only mathematical hypotheses and conclusions. Attribution, role in the proof, and source correspondence belong in remarks.

Put such sentences after the theorem.

### **G7. Source line-number references are not useful for readers**

The blueprint cites manuscript line numbers from source papers.

Line numbers are unusable unless every reader has the exact same TeX/PDF extraction.

Refer to theorem numbers, sections, or proof steps, e.g. “the invariant-support projection step.”

### **G8. Strict-modulus and one-copy-per-sector predicates are too strong unless scoped**

The blueprint repeatedly uses formulations where block weights have strictly decreasing moduli and each BNT sector has only one copy.

This is not a harmless ordering convention. The literature allows repeated copies and equal-modulus sectors.

Example:

A \= C ⊕ (-C)

has one normal tensor C with two weights 1 and \-1. Its MPV contribution is

V\_N(A) \= (1 \+ (-1)^N) V\_N(C),

which cannot be represented by a single scalar power.

State explicitly that strict-modulus results treat the distinct-modulus subcase. Treat equal-modulus and repeated-copy BNT sectors as part of the main theorem, not as an afterthought.

### **G9. Projection-limit arguments fail for non-dominant blocks**

A proof by projecting onto a non-dominant block does not generally give a contradiction, because both sides may decay.

For a non-dominant block with weight lambda, terms of order lambda^N tend to zero. A lower-bound/projection argument can therefore fail.

Use coefficient comparison based on linear independence of the full combined family. The coefficient may be small, but if it is nonzero, linear independence still detects it.

### **G10. Normality must not drift between algebraic and spectral formulations**

The blueprint sometimes treats “normal” as an algebraic eventual-spanning condition, sometimes as spectral primitivity.

These are equivalent only under hypotheses and missing reductions.

State which formulation is being used, and cite or prove the implication when passing from one formulation to the other.

### **G11. Use standard mathematical language, not implementation language**

Phrases such as “transport,” “discharge,” “assembly,” “stored as a field,” and “chains through” appear in prose.

Use “conjugate,” “satisfy,” “construction,” “proof,” “included as a hypothesis,” and “preserved under.”

---

# **Chapter-by-Chapter Synthesis**

## **Chapter 2 — Matrix Product Vectors**

### **Ch2.1 Periodic-chain aliases: “where are these used?”**

The earlier reading was that the site-periodic tensor-family definitions appear orphaned.

They are not necessarily useless, because they may be intended for the periodic Fundamental Theorem. But they are premature in the basic MPV chapter.

A sentence such as “These definitions are included for the later periodic-chain theorem and are not used in the aperiodic proof route” would be enough.

### **Ch2.2 Lemma 2.20: “loaded word”**

The earlier reading was that the word “symmetric” is overloaded and perhaps means the equality case.

The lemma is mathematically fine if “symmetric” means symmetric as a relation: if V(A)=c\_N V(B) with nonzero c\_N, then V(B)=c\_N^{-1} V(A). It is not about the special case c\_N=1.

Rewrite as: “Nonzero proportionality is symmetric as a relation, by inverting the scalar at each length.”

### **Ch2.3 Normality and block injectivity**

The handwriting asks to verify the meaning of injectivity and the possible clash with $L$-block injectivity.

This is the terminology conflict described above. The problem is not a false theorem but overloaded naming.

Distinguish $L$-block injectivity from block-injective canonical form.

### **Ch2.4 Definition 2.39: “awkward”**

The earlier reading was that Definition 2.39 seems to repeat the block-injective canonical-form definition.

It is not necessarily a duplicate. It may isolate the block-diagonal assembly operation from the additional injectivity assumptions.

A better title is “Construction: block-diagonal form from weighted blocks”; the surrounding text should say why this construction is separated from the canonical-form predicate.

## **Chapter 3 — Single-Block Fundamental Theorem**

### **Ch3.1 General assessment**

The chapter is structurally clean. The proof structure is visible:

same MPV  
 \-\> trace agreement  
 \-\> linear extension  
 \-\> multiplicative automorphism  
 \-\> Skolem--Noether gauge

### **Ch3.2 Theorem 3.11 needs a high-level strategy paragraph**

The proof jumps directly into technical details.

Before the proof, add a short paragraph:

The strategy is to convert equality of MPV coefficients into an algebraic map on the virtual matrix algebra. Since the tensor is injective, the one-site matrices span the full matrix algebra, so the assignment on generators extends uniquely to a linear map. Trace agreement for longer words forces multiplicativity. Simplicity of the matrix algebra makes this map an automorphism, and Skolem–Noether identifies it as conjugation by an invertible matrix.

## **Chapter 4 — Quantum Channels and Positive Maps**

### **Ch4.1 “Channel” used before definition**

A theorem refers to channels before the term is defined.

Move the quantum-channel definition before the theorem, or rewrite the theorem without using the word “channel.”

### **Ch4.2 Density matrices compact: topology issue**

The earlier reading was that the topology was missing.

The blueprint already states entry-wise topology in at least one version. The issue is at most wording clarity.

Write: “The set of density matrices is compact in the entry-wise topology.”

*Alternatively*, just say that the *set* of density matrices are compact.

### **Ch4.3 Injective MPS transfer map is irreducible**

The theorem is stated for MPS tensors, but the proof only uses the Kraus family spanning the full matrix algebra.

State a general Kraus-family lemma first, then specialize to MPS tensors.

### **Ch4.4 Peripheral spectrum notation**

sigma(T) and spectral radius should be defined before peripheral-spectrum definitions.

Introduce the finite-dimensional spectrum notation before defining the peripheral spectrum.

### **Ch4.5 Root-of-unity lemmas and finiteness**

Finiteness of peripheral eigenvalues is tautological in finite dimension; root-of-unity lemmas are over-separated.

Demote trivial statements to remarks or internal Lean lemmas; expose only the packaged theorem.

### **Ch4.6 KS/unital-vs-TP issue**

The theorem is correct for unital maps, but later MPS transfer-map use must be checked.

Explicitly state: “For a TP-normalized MPS transfer map, apply this theorem to the adjoint.”

## **Chapter 5 — Schwarz Inequalities and Multiplicative Domains**

### **Ch5.1 Repeated Kraus definitions**

Definitions 5.1–5.4 restate Chapter 4\.

Chapter 5 is the natural home for KS and multiplicative-domain material, so local recall is acceptable.

Present the repeated definitions as a “Recall” block.

### **Ch5.2 Definition 5.4: trace-preserving Kraus map**

The name may appear new, but it is mainly a recall of the TP condition.

It is useful because it makes the adjoint-unital point explicit.

It should say explicitly that if sum\_i K\_i^dag K\_i \= 1, then E is trace-preserving and E^\* is unital, so KS applies to E^\*.

### **Ch5.3 KS theorem duplication**

The KS inequality is also in Chapter 4\.

Prefer moving the substantive KS proof to Chapter 5 and leaving only a forward pointer in Chapter 4\.

### **Ch5.4 Schur complement proof**

The proof invokes Schur complement without defining the needed lemma.

Either state the Schur-complement lemma or use the Stinespring/isometry proof:

E(X^dag X) \- E(X)^dag E(X)  
 \= V^dag X^dag (1 \- V V^dag) X V \>= 0\.

## **Chapter 6 — Perron–Frobenius Theory**

### **Ch6.1 Wolf attribution**

Do not imply Wolf developed Perron–Frobenius theory for CP maps.

A natural wording is: “We follow Wolf’s presentation, together with the classical Evans–Hoegh-Krohn source.”

### **Ch6.2 Theorem 6.3 vs Theorem 6.4**

The earlier reading was that Theorem 6.4 might be redundant because 6.3 already gives positive definiteness.

They are not redundant. Theorem 6.3 assumes an injective tensor; Theorem 6.4 assumes irreducibility of the transfer map. The latter is the more useful Perron–Frobenius statement.

A short remark can record the implication chain:

injective tensor \-\> irreducible transfer map \-\> positive fixed point is positive definite.

### **Ch6.3 Rho notation**

rho is used for several fixed-point roles.

Use role-specific notation: rho\_fp, rho\_A, sigma\_A, etc.

### **Ch6.4 Dimension hypothesis D \> 0**

In Lean, the zero-dimensional matrix algebra may create degenerate cases.

Carry D \> 0 whenever density matrices, normalized traces, or positive fixed points are used. Or maybe one can simply impose that D \\geq 1\. 

### **Ch6.5 TP reduction in spectral-radius proofs**

Some spectral claims are proved by passing through TP normalization without explaining why this is legitimate.

The proof should include the reduction explicitly: gauge by a positive definite Perron eigenvector, rescale by the spectral radius, prove the normalized statement, and then transfer the conclusion back using similarity and rescaling invariance.

### **Ch6.6 Spectral package / iff theorem**

Directional theorems and bundled definitions make the chapter feel bloated.

In prose, state the iff theorem directly. Directional lemmas can remain as Lean declarations if needed.

## **Chapter 7 — Spectral Gap and Block Separation**

### **Ch7.1 Too many named intermediate lemmas**

Some theorem names reflect technical formalization details rather than mathematical content.

The exposition should distinguish the mathematical proof structure from internal Lean lemmas. Only mathematically meaningful names should appear in the main blueprint.

### **Ch7.2 Matrix trace vs superoperator trace**

The earlier reading was that the distinction may be unnecessary.

The distinction is real: tr(F\_AB^N(1)) is a matrix trace after applying the transfer map; Tr(F\_AB^N) is the operator trace of the superoperator.

Keep the distinction, but move it to a remark rather than theorem statement.

### **Ch7.3 “Transported matrix X’”**

The gauged mixed-transfer proof uses an undefined transported matrix.

Define it explicitly. If gauges are G\_A and G\_B, write the transformed eigenvector as something like

X' \= G\_A X G\_B^{-1}

or whatever is correct for the adopted convention. Then prove the covariance identity.

### **Ch7.4 “Weak irreducibility” / TP gauge**

TP normalization is a gauge convention, not the substantive weakening.

The real weakening is injectivity of the tensor to irreducibility of the transfer map. TP gauge is supplied by PF theory.

The section title can simply be “Spectral gap under irreducibility in TP gauge.”

### **Ch7.5 Wolf equivalences section**

The chapter collects many primitivity equivalences.

Indicate which equivalences are on the main Fundamental Theorem route, which ones support the channel theory, and which ones belong in an appendix.

## **Chapter 8 — Wielandt Bound**

### **Ch8.1 Fitting decomposition terminology**

“Fitting decomposition” may not match the full generalized-eigenspace decomposition being stated.

Fitting decomposition is a standard term in some algebraic contexts, but the blueprint seems to use it for the full generalized eigenspace decomposition.

Use “generalized-eigenspace/Fitting decomposition,” and align with Mathlib terminology if possible.

### **Ch8.2 General assessment**

Chapter 8 is cleaner than surrounding chapters. No major mathematical issue was detected from the handwriting.

## **Chapter 9 — Canonical Form Reduction**

### **Ch9.1 Strengthening beyond left-canonical form**

Stronger predicates add strict modulus ordering and one-copy-per-sector assumptions.

Left-canonical normalization is a harmless gauge choice under the right hypotheses. Strict-modulus and one-copy-per-sector are not harmless.

The statement should say explicitly that the predicate covers a distinct-norm, one-copy-per-sector subcase; equal-norm and repeated-copy sectors require BNT grouping and multiplicity machinery.

### **Ch9.2 Definition 9.4: normality and uniqueness**

The earlier reading was that Normality as defined may not imply uniqueness.

If the definition includes both irreducibility/no invariant projection and primitive peripheral spectrum, uniqueness is expected. The real warning is not to define normality only by peripheral spectrum {1}.

The text can say: “The peripheral-spectrum condition alone is not normality; absence of nontrivial invariant projections is also essential.”

### **Ch9.3 Remark 9.7 premature**

The remark may rely on facts established only later.

Move it later or label it as forward-looking orientation.

### **Ch9.4 Theorem 9.14 hard to parse**

The theorem statement mixes a non-scalar fixed-point condition with source commentary.

Before the theorem, say: “The next lemma is the splitting step: a non-scalar positive fixed point yields a nontrivial invariant support projection.” Put source commentary in a remark.

### **Ch9.5 Burnside-style passage**

“Burnside-style passage” is unexplained jargon.

State Burnside’s theorem explicitly: an irreducible subalgebra of M\_D(C) is all of M\_D(C).

### **Ch9.6 Strict ordering and GHz/GHZ conflict**

Strictly ordered moduli conflict with standard block-injective examples with equal-modulus blocks.

Treat strict ordering as a subcase. Use norm-class grouping and BNT multiplicity for the general theorem.

### **Ch9.7 Undefined sigma\_partial**

Peripheral spectrum notation appears without definition.

Define sigma\_per(E) as {lambda in sigma(E): |lambda| \= r(E)} or cross-reference the earlier definition.

### **Ch9.8 Definitions 9.47–9.48 norm-class grouping**

The earlier reading was that these definitions may restrict the goal.

These definitions are probably necessary, not restrictive. They are the mechanism for handling equal-modulus blocks.

Motivate them explicitly: “To remove the artificial distinct-norm assumption, group blocks by common weight modulus.”

### **Ch9.9 Lemma 9.62 adjoint primitivity**

The lemma might seem to conflict with GHZ-type examples.

The lemma is fine under its hypotheses. GHZ is not primitive, so it is not a counterexample.

Use this lemma only after restriction to primitive blocks, not for a general block-injective direct sum.

## **Chapter 10 — Block Permutation and Separation**

### **Ch10.1 Strict-weight same-structure subcase**

Chapter 10 contains strict-modulus block-separation and comparison with already aligned block structure lemmas.

These are useful subcase lemmas, but not the general BNT comparison theorem.

Before the strict-modulus lemmas, insert:

The following separation lemmas apply to the strict-modulus, same-structure case. Equal-modulus and repeated-copy sectors are handled by the BNT and sector-weight machinery.

### **Ch10.2 Line-number references**

Remarks cite source line ranges and obscure the mathematical proof structure.

Replace by structural descriptions: finite product algebra automorphism, dominant-modulus peeling, and deferred equal-modulus BNT comparison.

## **Chapter 11 — Basis of Normal Tensors**

### **Ch11.1 Chapter motivation**

The chapter introduces BNT, coefficient arrays, separation, Newton–Girard, and permutation rigidity without enough plain mathematical motivation.

Start with:

A basis of normal tensors is a minimal list of inequivalent normal blocks. For large enough system size, their MPVs are linearly independent. This lets one compare coefficients block by block after matching normal blocks.

### **Ch11.2 Normality wording conflict**

The chapter risks presenting algebraic and spectral normality as two unrelated notions.

Say explicitly that these are two formulations of normality connected by a separate implication, and invoke the relevant direction.

### **Ch11.3 Coefficient convergence**

Raw powers mu\_j^N need not converge unless rescaled or unless all relevant moduli are controlled.

Use fixed-large-N coefficient comparison from linear independence, or explicitly rescale by dominant modulus before taking limits.

### **Ch11.4 Newton–Girard**

Newton–Girard may be useful for recovering multisets of weights from power sums, but it should not obscure the simpler equal-MPV weight-matching route when one-copy sectors suffice.

Clarify whether Newton–Girard is essential or only used for repeated-sector multiset recovery.

## **Chapter 12 — Common Primitive Surface / After-Blocking Reduction**

### **Ch12.1 General role**

The chapter feels redundant and more detailed than needed in the exposition.

It is not mathematically redundant if it packages arbitrary tensor reduction into blocked primitive block form. But much of its prose likely exposes technical formalization details.

Compress to three main theorems:

1. arbitrary tensor admits a blocked primitive decomposition;

2. same-MPV equality survives blocking and zero-tail removal;

3. two equal-MPV tensors can be put into a common primitive-block comparison form.

Everything else should move to proof notes or appendix.

### **Ch12.2 Gauge notation: U vs X**

If the map is a general invertible gauge, using U suggests unitarity.

Use X for general invertible gauges and reserve U for unitary maps.

### **Ch12.3 “Transport” language**

“Transport” is nonstandard unless there is an actual transport-of-structure construction.

Use “conjugate by the gauge” or “rewrite in the gauged representation.”

## **Chapter 13 — Proof of the Fundamental Theorem**

### **Ch13.1 Theorem statement marked “not ready”**

The chapter states a theorem from the source paper but marks it “not ready.”

This means the chapter mixes statements from the literature, conditional formal statements, strict special cases, and intended final conclusions.

Separate into three layers:

1. Statement from the literature.

2. Actually proved formal intermediate theorem.

3. Remaining missing reductions/gaps.

### **Ch13.2 Equal-MPV theorem and weight matching**

Matching blocks up to gauge-phase is not yet global gauge equivalence unless weights match after phase absorption.

In the usual MPS proof, suppose

A \= direct sum\_j mu\_j^A A\_j,  
B \= direct sum\_k mu\_k^B B\_k,

and block matching gives

B\_{pi(j)}^i \= exp(i phi\_j) X\_j A\_j^i X\_j^{-1},

then equality of MPVs gives

sum\_j \[(mu\_j^A)^N \- (mu\_{pi(j)}^B exp(i phi\_j))^N\] V\_N(A\_j) \= 0\.

By BNT linear independence for large N, each coefficient vanishes, so

mu\_j^A \= mu\_{pi(j)}^B exp(i phi\_j).

Then the phases are absorbed into the weights and the block-diagonal tensors are globally gauge equivalent.

Package this argument as the final equal-MPV theorem.

### **Ch13.3 Repeated-copy sectors**

The full BNT structure in the paper allows a sector to contain several copies of the same normal block with weights mu\_{j,q}.

Then the coefficient of a BNT vector is a power sum:

c\_j(N) \= sum\_q mu\_{j,q}^N.

The final theorem must either:

* handle repeated-copy sectors via power-sum comparison and Newton–Girard/multiset recovery; or

* explicitly restrict to the one-copy case and state that the theorem is weaker than the literature theorem.

### **Ch13.4 Avoid non-dominant projection arguments**

Projection estimates detect dominant blocks but may fail for non-dominant blocks.

Use full combined-family linear independence. This detects nonzero coefficients even if they decay exponentially.

---

# **Verification and Redundancy Notes**

## **Repeated items that are verified or strongly supported**

1. Kraus-map and channel definitions are repeated between Chapters 4 and 5\.

2. KS appears in both Chapter 4 and Chapter 5; Chapter 5 is the better home.

3. Peripheral-spectrum finite-dimensional finiteness is tautological.

4. Root-of-unity lemmas are over-separated for prose, though Lean may benefit from separate declarations.

5. The strict-modulus block comparison is a subcase, not the general theorem.

6. Norm-class grouping is not a restriction; it is needed to handle equal-modulus blocks.

## **Corrections to the Word transcript**

1. Lemma 2.20: “symmetric” is not wrong if it means relation-symmetric; it just needs clearer wording.

2. Theorem 4.10: topology may already be stated; the issue is only clarity.

3. Theorem 6.4 is not redundant with 6.3; it has weaker and more reusable hypotheses.

4. The trace distinction in Theorem 7.5 is real and should be kept, but moved to a remark.

5. Definition 9.4 is not obviously wrong if irreducibility/no-invariant-projection is included; the danger is dropping that part.

6. Definitions 9.47–9.48 are likely necessary, not restrictive.

7. GHZ/GHz examples do not refute primitivity lemmas; they show the hypotheses do not apply to unreduced block-injective direct sums.

## **Ambiguous handwriting**

Some diagram circles and short marks do not carry enough information to infer an issue. These should remain listed as ambiguous rather than be guessed. In particular:

* circles around early tensor-network diagrams without text;

* “CFI?” near canonical-gauge discussion, likely “canonical form I,” but not certain;

* exact reason for the U notation complaint in Chapter 12, unless the surrounding theorem confirms U is not unitary.

---

# **Checklist**

## **Points to resolve before relying on the blueprint**

1. Specify the exact target theorem: canonical-form FT or arbitrary-tensor FT.

2. Separate existence of canonical form from uniqueness within canonical form.

3. State explicitly when strict-modulus or one-copy-per-sector assumptions are being used, and do not let them enter the general theorem unnoticed.

4. Include repeated/equal-modulus BNT sector machinery explicitly.

5. Replace non-dominant projection-limit reasoning by coefficient comparison using full linear independence.

6. Clarify all normalization conventions and KS-adjoint usage.

7. Correct MPV overlap bilinear/conjugate-linear wording.

8. Prove or cite normality missing reductions when moving between algebraic and spectral formulations.

## **Improvements to exposition**

1. Move editorial/source commentary out of theorem statements.

2. Replace manuscript line-number citations with theorem/section/structural citations.

3. Reduce technical Lean lemma names in the main prose.

4. Put proof-strategy summaries before long technical chapters.

5. Use standard terms: conjugate, satisfy, preserve, construction, theorem, proof.

6. Use consistent notation for gauges, fixed points, spectra, and transfer maps.

## **Smaller cleanup items**

1. Demote tautological finite-dimensional spectral facts to remarks.

2. Use Mathlib’s terminology for “Fitting decomposition” if it differs from the present wording.

3. Move site-periodic aliases closer to the periodic theorem unless needed early.

4. Use forward references when definitions are intentionally introduced early.

---

# **A cleaner organization for the blueprint**

The blueprint would be much easier to verify if reorganized into four layers.

## **Layer 1: Algebraic core**

* MPVs, word evaluation, trace coefficients.

* Single-block FT.

* Gauge and gauge-phase equivalence.

## **Layer 2: Channel and spectral infrastructure**

* Positive maps and transfer maps.

* PF fixed points and canonical gauges.

* KS/multiplicative domain.

* Spectral gap and overlap decay.

* Wielandt bound.

## **Layer 3: Canonical form existence**

* Remove triangular/nilpotent/zero parts.

* Decompose into irreducible blocks.

* Gauge to TP/canonical form.

* Block to remove periodicity.

* Obtain primitive/normal blocks.

* Group into BNT sectors.

## **Layer 4: Canonical-form uniqueness and final FT**

* BNT linear independence.

* Block permutation.

* Gauge-phase matching.

* Weight/power-sum comparison.

* Phase absorption.

* Global gauge equivalence.

This architecture would make it clear which results are mathematical, which are formalization infrastructure, and which are merely subcase lemmas.

---

# **Final assessment**

The Word document captured many real margin comments, but it underestimates the seriousness of the strict-modulus/BNT issue and contains several incorrect readings. The corrected synthesis is:

* Chapters 2–8 are mostly repairable through terminology, ordering, and proof-organization cleanup.

* Chapter 9 is the first genuinely delicate point because it introduces strengthened canonical-form predicates.

* Chapters 10–13 are the main theorem-formulation risk: comparison with already aligned block structure must not be confused with the full BNT theorem.

* The final theorem should be checked against the statement in the paper: equality of MPVs for tensors in canonical form should imply global gauge equivalence without assuming common block structure or one-copy sectors.

* For arbitrary tensors, canonical-form existence is a separate upstream theorem and should not be silently folded into the FT unless fully proved.

The blueprint appears to contain many useful components for the formalization, but it needs a sharper theorem statement and a cleaner final theorem. The central missing or delicate step is the passage from block/gauge-phase matching to full global gauge equivalence in the presence of repeated and equal-modulus BNT sectors.