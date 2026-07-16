# Source audit: Wolf material relevant to Q3

**Date:** 2026-07-16  
**Question:** Does Michael M. Wolf's lecture note supply the missing Schatten
one-norm, quantum Pinsker, complete MLSI tensorization, or nonautonomous entropy
evolution used in Q3?  
**Primary source:** Michael M. Wolf, *Quantum Channels & Operations: Guided
Tour*, July 5, 2012.  
**Repository transcription:** `Notes/WolfNoteTexSource/`.

## Executive conclusion

Wolf supplies the static finite-dimensional **Schatten and trace-norm
background**, but not the remaining analytic inputs in the Q3 proof.

1. Chapter 8, Section 8.1 defines Schatten `p`-norms and identifies the `p = 1`
   case with the trace norm. It also states or proves several useful norm and
   trace-distance results.
2. The notes contain no quantum Pinsker inequality, either by name or in the
   form `‖ρ - σ‖₁² ≤ 2 D(ρ ‖ σ)`.
3. The notes contain no logarithmic Sobolev, modified logarithmic Sobolev, or
   complete modified logarithmic Sobolev inequality, and no corresponding
   tensorization theorem.
4. Chapters 1 and 7 treat homogeneous evolution with a fixed Hamiltonian or
   fixed generator. They do not prove a nonautonomous relative-entropy chain
   rule for a measurable or locally integrable Hamiltonian `H(t)`.

Consequently, Wolf is a suitable source for trace-norm foundations but is not
a self-contained source for the Q3 proof. Quantum Pinsker, CMLSI tensorization,
and the nonautonomous entropy argument require later sources or direct proofs.

## Exact source and version

The TNLean bibliographies identify the source as follows:

- `blueprint/src/references.bib:42-49`;
- `docs/paper-gaps/references.bib:109-113`.

The cited item is Michael M. Wolf, *Quantum Channels & Operations: Guided
Tour*, lecture notes, 2012. The archived PDF title page gives the more precise
version date **July 5, 2012**. Its second page says that the notes are based on a
2008/2009 Niels Bohr Institute course and warns that passages remain cryptic,
erroneous, incomplete, or missing.

The local Chapter 8 transcription is
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`. Its header says that the
transcription is partial and reaches the heading of Section 8.8, so the full
2012 PDF was also checked when determining absence claims.

Theorem, proposition, and lemma numbers cited in this audit follow the printed
numbering of the July 5, 2012 PDF, not the transcription's LaTeX
auto-numbering. Because the transcription is partial and numbers all
theorem-like environments from one per-section counter, it assigns different
numbers to the same results (for example, the result cited here as
Theorem 8.16 carries a different automatic number in the transcription).
Locate results in the transcription by the quoted line ranges, not by
searching for printed theorem numbers.

## Coverage table

| Q3 ingredient | Wolf location | Source status | Current TNLean status | Sufficient for Q3? |
|---|---|---|---|---|
| Schatten/trace one-norm definition | Chapter 8, Section 8.1, printed pp. 131-132; local lines 63-95 | Defined | Foundational singular-value sum in PR #4031 | Only as the distance foundation |
| Basic trace-norm facts | Chapter 8, Section 8.1; Theorems 8.2 and 8.3; Chapter 8, Sections 8.5 and 8.7 | Mixture of statements, proof sketches, and proofs | Mostly not yet formalized | Only partial distance background; norm structure, duality, and contractivity remain |
| Quantum Pinsker | No location | Absent | Absent | No |
| CMLSI and tensorization | No location | Absent | Absent | No |
| Fixed-generator GKSL dynamics | Chapter 7, Section 7.1.2, Theorem 7.1 | Proved | Substantially formalized | Only the autonomous algebraic background |
| Nonautonomous entropy evolution | No location | Absent | Absent | No |

## 1. Schatten and trace one-norm material

### 1.1 Definitions

The useful source text begins in
`Notes/WolfNoteTexSource/ch08_distance_measures.tex:44-104`.

At lines 63-69 Wolf defines the Schatten `p`-norm

```text
‖A‖ₚ = (∑ᵢ sᵢ(A)ᵖ)¹ᐟᵖ,  p ≥ 1.
```

Equation **(8.1)** at lines 77-85 states monotonicity in `p`, including

```text
‖A‖₁ ≥ ‖A‖₂ ≥ ‖A‖∞.
```

Lines 86-95 identify

```text
‖A‖₁ = ‖A‖₍d₎ = tr |A|
```

and call it the trace norm.

### 1.2 Useful statements and their proof status

The following distinctions matter for formalization.

- **Theorem 8.2, “Unitarily invariant norms,” local lines 106-142.**
  It states Hölder, Lidskii, Ky Fan dominance, and Araki-Lieb-Thirring
  inequalities. The notes collect these assertions but do not give complete
  proofs there.
- **Equation (8.6), local lines 144-148.**
  The trace-pairing Hölder inequality
  `|tr(A†B)| ≤ ‖A‖ₚ ‖B‖q` is derived from the preceding Hölder statement.
- **Theorem 8.3, local lines 170-195.**
  It gives variational formulas, including
  `‖A‖₁ = sup_U |tr(A†U)|`. The proof is a sketch and contains an explicit
  ellipsis.
- **Theorem 8.12, printed pp. 141-142; local lines 541-566.**
  The quantum Neyman-Pearson theorem gives the operational interpretation of
  trace distance. A proof is included.
- **Theorem 8.16 and Eq. (8.80), printed p. 148; local lines 898-918.**
  A positive trace-preserving map contracts the trace norm on Hermitian inputs,
  and hence contracts trace distance between states. A proof is included.
- **Lemma 8.3, printed pp. 148-149; local lines 920 onward.**
  It identifies the trace-norm contraction coefficient with a supremum over
  orthogonal pure states. A proof is included.

### 1.3 Current formalization

PR #4031 adds `TNLean/Analysis/SchattenNorm.lean` with:

- `Matrix.schattenOneNorm`;
- `Matrix.traceNorm`;
- `Matrix.traceNorm_eq_sum_support`;
- `Matrix.traceNorm_eq_sum_range_finrank_range`;
- `Matrix.traceNorm_eq_sum_fin`;
- nonnegativity, zero, and strict-positivity characterizations.

This first increment uses Mathlib's `LinearMap.singularValues` and proves Wolf's
finite-dimensional singular-value sum with trailing zeros. It deliberately does
not substitute the ambient matrix operator norm.

Still missing from the Wolf trace-norm development are:

- the triangle inequality and a bundled norm structure;
- the equality `Matrix.traceNorm A = Re tr |A|`;
- scalar homogeneity and unitary invariance;
- the operator-norm dual variational formula;
- Theorem 8.16 trace-norm contractivity.

These are genuine follow-up formalization tasks. The source proof status above
should be preserved in their documentation: Theorem 8.16 has a source proof,
whereas several Section 8.1 results are only collected or sketched.

## 2. Quantum Pinsker is absent

Q3 uses the natural-logarithm convention

```text
‖ρ - σ‖₁² ≤ 2 D(ρ ‖ σ).
```

The complete 2012 PDF contains no occurrence of “Pinsker” and no unnamed
statement with this formula. Chapter 8 discusses its two sides separately:

- the classical `ℓ₁` divergence appears in Eq. **(8.31)**;
- quantum relative entropy appears in Section 8.4.2;
- trace norm appears in hypothesis testing and contractivity.

No theorem joins relative entropy to squared trace distance.

A notation trap occurs in Proposition 8.3 and Eqs. **(8.70)-(8.75)**: the symbol
`D(ρ₁, ρ₂)` there denotes **Hilbert's projective metric**, not quantum relative
entropy. Those inequalities are not Pinsker and cannot discharge the Q3 step.

TNLean already defines `quantumRelativeEntropy` in
`TNLean/Analysis/Entropy.lean`, but no quantum Pinsker theorem currently
connects it to `Matrix.traceNorm`.

## 3. CMLSI and tensorization are absent

No occurrence or definition of the following was found in Wolf:

- logarithmic Sobolev inequality;
- modified logarithmic Sobolev inequality;
- complete modified logarithmic Sobolev inequality;
- ancilla-stable entropy production;
- tensorization of a complete MLSI constant.

Chapter 7 develops autonomous semigroup structure, generators, relaxation, and
fixed points. Chapter 8 develops static distance and entropy quantities. Neither
chapter contains the complete entropy-production inequality used in Q3.

The Q3 proof's CMLSI input must therefore be attributed to the later
Gao--Rouzé theory or proved directly. Wolf should not be cited for that step.

## 4. Nonautonomous entropy evolution is absent

Wolf treats homogeneous evolution:

- Chapter 1, Section 1.3, Eq. **(1.18)**: `U_t = exp(iHt)` for a fixed
  Hamiltonian `H`;
- Chapter 7, Eq. **(7.2)**: `T_t = exp(tL)` and `dT_t/dt = LT_t` for a fixed
  generator `L`;
- Chapter 7, Lemma 7.1, Eqs. **(7.10)-(7.13)**: Duhamel and Dyson--Phillips
  formulas comparing fixed generators;
- Chapter 7, Theorem 7.1, Eqs. **(7.20)-(7.23)**: time-independent GKSL forms.

The notes do not formulate or prove the Q3 evolution

```text
ρ̇_t = -i[H(t), ρ_t] + D(ρ_t)
```

for strongly measurable, locally integrable `H(t)`. In particular, they do not
supply:

- existence and uniqueness of the absolutely continuous trajectory;
- an almost-everywhere relative-entropy chain rule;
- cancellation of the time-dependent Hamiltonian contribution;
- the non-full-rank regularization argument;
- integration of the entropy-production inequality for locally integrable
  drives.

The existing TNLean Wolf Chapter 7 development covers the autonomous material:

- `TNLean/Channel/Semigroup/Basic.lean` formalizes Wolf Proposition 7.1;
- `TNLean/Channel/Semigroup/LindbladForm/Basic.lean` formalizes Eq. (7.21);
- `TNLean/Channel/Semigroup/KossakowskiForm.lean` formalizes Eq. (7.23);
- `TNLean/Channel/Semigroup/LiouvillianKernel.lean` formalizes Theorem 7.2.

This infrastructure is reusable, but it does not constitute a nonautonomous
entropy theorem.

## 5. Existing Wolf Chapter 8 material in TNLean

TNLean already formalizes some Chapter 8 entropy content:

- `TNLean/Analysis/Entropy.lean` defines `vonNeumannEntropy`, citing Wolf
  Section 8.2 and Eq. (8.15);
- the same module defines `quantumRelativeEntropy` and proves elementary
  trace-log identities;
- `TNLean/Analysis/KyFanNorm.lean` develops sums of ordered Hermitian
  eigenvalues and explicitly notes that this agrees with the genuine
  singular-value Ky Fan norm only on the positive-semidefinite cone.

There is currently no public `WolfChapter8Index` analogous to
`TNLean/Channel/WolfChapter2Index.lean` and
`TNLean/Channel/WolfChapter6Index.lean`.

## Formalization roadmap

The source-faithful order is:

1. **Schatten one-norm foundation** — PR #4031.
2. **Norm structure and `tr |A|` identification** — finish the mathematical
   meaning of Wolf's trace-norm terminology.
3. **Unitary invariance and duality** — Wolf Section 8.1, with explicit notice
   where the source gives only a proof sketch.
4. **Trace-distance contractivity** — formalize Wolf Theorem 8.16 from its
   positive/negative-part proof.
5. **Quantum Pinsker** — separate later-source PR; not Wolf.
6. **CMLSI and tensorization** — separate Gao--Rouzé-source PR; not Wolf.
7. **Nonautonomous entropy chain rule** — separate ODE/entropy-analysis PR; not
   Wolf.

## Attribution policy

- Cite **Wolf Chapter 8** for Schatten/trace-norm definitions, the stated
  Section 8.1 norm facts, quantum Neyman-Pearson, and trace-norm contractivity.
- Distinguish a theorem merely stated or sketched by Wolf from one with an
  actual proof in the notes.
- Do not cite Wolf for quantum Pinsker, CMLSI tensorization, or nonautonomous
  entropy evolution.
- Do not call the ambient matrix operator norm a trace norm.

## Final status

| Question | Answer |
|---|---|
| Does Wolf define the Schatten/trace one-norm? | **Yes.** |
| Does Wolf provide useful trace-norm facts? | **Yes**, with mixed proof status. |
| Does Wolf prove quantum Pinsker? | **No.** |
| Does Wolf contain CMLSI tensorization? | **No.** |
| Does Wolf contain the nonautonomous Q3 entropy argument? | **No.** |
| Is Wolf alone sufficient to formalize Q3? | **No.** |
| Is TNLean's trace-norm foundation now started? | **Yes, in PR #4031.** |
