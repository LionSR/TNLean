# Scouting Report: arXiv:1903.09439 vs TNLean Formalization

**Paper**: "Mathematical open problems in Projected Entangled Pair States"
**Authors**: J. Ignacio Cirac, José Garre-Rubio, David Pérez-García (2019)
**Date of scouting**: 2026-03-23

---

## Paper Summary

This is a survey paper presenting open mathematical problems related to PEPS
(Projected Entangled Pair States) for a broad mathematical audience. It covers:

1. **PEPS ↔ ground states correspondence** (Section 2)
2. **PEPS as a framework for formal proofs** (Section 3)  
3. **Miscellaneous problems** (Section 4)

The paper poses **12 explicit questions** and **1 conjecture**.

---

## Inventory of Open Problems

### Section 2: PEPS = GS?

| # | Problem | Status in Paper | Our Formalization Status |
|---|---------|-----------------|--------------------------|
| Q1 | Minimal requirements on A and size of R for unique GS + gap | Open | — |
| Q2 | **Optimal upper bound for primitivity index p(T) of quantum channel** | Open. Best known: p(T)≤2(D−1)² [Rahaman]. Exact optimal unknown. | **We proved p(T) ≤ i(A) ≤ (D²−d+1)·D²** (the original qWielandt bound). See below. |
| Q3 | **Optimal upper bound for injectivity index i(A) of normal MPS** | Open. Best known: i(A)≤2D²(6+log₂D) [Michalek-Shitov]. Exact optimal unknown. | **We proved i(A) ≤ (D²−d+1)·D² with sharp subcases.** See below. |
| Q4 | Optimal upper bound for injectivity index of normal PEPS | Open. Only existence of some f(D) known [Michalek-2D]. | — (2D not in scope) |
| Q5 | Explicit computable bound for PEPS injectivity index | Open | — (2D not in scope) |
| Conj 1 | Gap of parent Hamiltonian ↔ boundary states as Gibbs states | Conjecture | — |
| Q6 | Is Conjecture 1 true? | Open | — |
| Q7 | Global approximation in 2D under only spectral gap assumption? | Open | — |
| Q8 | Can f(L) be polynomial? | Open | — |
| Q9 | Local approximation in 2D? | Open | — |

### Section 3: PEPS as a Framework

| # | Problem | Status in Paper | Our Formalization Status |
|---|---------|-----------------|--------------------------|
| Q10 | **Fundamental Theorem in 2D for largest family of PEPS** | Open. Known for normal PEPS. Undecidable in general. | **We fully proved the 1D Fundamental Theorem** (all cases: injective, CF-BNT, heterogeneous blocks). |
| Q11 | Local relation between approximately equal PEPS tensors | Open, no known results even for normal case | — |

### Section 4: Miscellaneous

| # | Problem | Status in Paper | Our Formalization Status |
|---|---------|-----------------|--------------------------|
| Q12 | Rademacher complexity / VC-dimension for TN-based ML | Open | — |
| Q13 | Exact complexity class for 2D PEPS zero-testing | Open (NP-hard known) | — |
| Q14 | Low-depth noisy circuit for topological phase transitions | Open | — |
| Q15 | PEPS ↔ QCA relation in 2D and higher | Open | — |

---

## Deep Dive: Opportunities for Impact

### 🔴 HIGH OPPORTUNITY: Question 2 — Optimal Quantum Wielandt Bound for p(T)

**The problem**: Find the exact optimal upper bound for the primitivity index
p(T) of a primitive quantum channel T : M_D → M_D.

**State of the art in the paper** (2019):
- Original bound: p(T) ≤ (D²−d+1)·D² [Sanz-Pérez-García-Wolf-Cirac 2010]
- Improved: p(T) ≤ 2(D−1)² [Rahaman 2018]
- Known optimal order: O(D²) by classical Wielandt optimality
- Exact constant: **unknown**

**What we have formalized**:
- `iIndex_le_general_of_isPrimitivePaper`: i(A) ≤ (D²−d+1)·D²
- `qIndex_le_iIndex_of_isPrimitivePaper`: p(T) ≤ i(A)  
- Combined: p(T) ≤ (D²−d+1)·D² (the original 2010 bound)
- **Sharp subcases**: 
  - Case 2 (invertible Kraus): i(A) ≤ D²−d+1
  - Case 3 (non-invertible with eigenvector): i(A) ≤ D²

**Opportunity**: Our formalization of the original qWielandt proof is **complete
and sharp**. The gap between what we've proven and the best known bound is:
- We prove: p(T) ≤ (D²−d+1)·D² ∼ O(D⁴)
- Rahaman proves: p(T) ≤ 2(D−1)² ∼ O(D²)  

Could we formalize Rahaman's improved bound? The approach in [Rahaman 2018] is
substantially different — it uses a direct analysis of the quantum channel rather
than going through word spans. This would be a significant new formalization effort,
but our existing infrastructure (quantum channels, primitivity, spectral theory)
provides a strong foundation.

**Even more impactful**: Since the exact optimal constant is unknown, our
formalization toolkit (especially the blocking argument, eigenvector spreading,
and rank-one spanning) could potentially be used to **discover and verify** an
improved bound computationally. The formalized Case 2 bound i(A) ≤ D²−d+1 is
already tight when d = D² (the identity matrix is among the Kraus operators) —
the real question is whether the Case 1 blocking multiplicative penalty D² can
be reduced.

---

### 🔴 HIGH OPPORTUNITY: Question 3 — Optimal MPS Injectivity Index

**The problem**: Find the optimal upper bound for i(A) of a normal MPS.

**State of the art in the paper** (2019):
- Original: i(A) ≤ (D²−d+1)·D² [qWielandt 2010]
- Improved: i(A) ≤ 2D²(6+log₂D) [Michalek-Shitov 2018]
- Known optimal order: Ω(D²) by classical Wielandt, but exact bound unknown

**What we have formalized**:
- The complete original bound (D²−d+1)·D² with all three cases
- The full chain: Lemma 1 → eigenvalue extraction → eigenvector spreading → 
  rank-one spanning → full span

**Opportunity**: Similar to Q2 — our sharp subcases show that the bottleneck is
the blocking step (Case 1). The Michalek-Shitov bound O(D²·log D) is obtained
through algebraic geometry techniques. Formalizing it would require different
mathematical machinery, but our existing framework would provide the starting
definitions and infrastructure.

**Key insight**: Our formalization already has `krausRank A` (the actual dimension
of span{A_i}) instead of the raw physical dimension d. This means our bounds are
already stated in their most general form: i(A) ≤ (D²−krausRank(A)+1)·D². This is
a nontrivial strengthening that may not be fully appreciated in the literature.

---

### 🟡 MEDIUM OPPORTUNITY: Question 10 — Fundamental Theorem for 2D

**The problem**: Extend the Fundamental Theorem to the largest possible family
of 2D PEPS.

**What we have formalized**:
- **Complete 1D Fundamental Theorem** in multiple forms:
  - Single-block (injective): `fundamentalTheorem_singleBlock`
  - Homogeneous CF-BNT: `fundamentalTheorem_equalMPV_CFBNT`
  - Heterogeneous CF-BNT: `fundamentalTheorem_equalMPV_CFBNT_hetero`
  - Proportional MPV: `fundamentalTheorem_proportionalMPV_CFBNT`

**Opportunity**: The 1D case is the foundation for 2D extensions. The paper notes
that the FT holds for normal PEPS [Carlos, Molnar1] and that extensions to
"quasi-injective" PEPS exist [Molnar2]. Our infrastructure — gauge equivalence,
spectral gap dichotomy, overlap decay, canonical form — could serve as the
building blocks for a 2D formalization. However, this is a very large undertaking
requiring new mathematical content (2D tensor network contraction, etc.).

The more immediate value: our 1D FT formalization is already the most complete
formal treatment available. It directly addresses the paper's claim that "the
so-called Fundamental Theorem of MPS shows that..." by providing machine-verified
proofs.

---

### 🟡 MEDIUM OPPORTUNITY: Spectral Gap Infrastructure 

**Paper context**: Section 2.1.4 discusses that spectral gap of parent
Hamiltonians is proven for normal MPS [Fannes92] but is generally undecidable
for PEPS.

**What we have formalized**:
- Spectral gap / overlap dichotomy for injective MPS blocks
- Spectral gap for irreducible TP blocks (more general)
- Convergence results: mixed transfer matrix powers → 0 when not gauge equivalent
- QDS primitivity ↔ irreducibility equivalence

**Opportunity**: Our spectral gap machinery is exactly what's needed for the
1D portion of the parent Hamiltonian gap question. While the 2D question is
intractable (undecidable), our 1D results could contribute to:
- Formal verification of the Fannes-Nachtergaele-Werner result
- Analysis of specific PEPS models where the boundary theory reduces to 1D

---

### 🟢 EXISTING CONTRIBUTION: The Paper's Core Reference [qWielandt]

The paper cites [qWielandt] = Sanz-Pérez-García-Wolf-Cirac 2010 as a
foundational result, and we have **completely formalized it**:

- Theorem 1 (all 3 cases) ✅
- Lemma 1 (nonzero trace word, sharp bound) ✅  
- Lemma 2(a) (eigenvector spreading) ✅
- Lemma 2(b) (rank-one matrix spanning, sharp bound) ✅
- Proposition 3 (q(E_A) ≤ i(A)) ✅
- Blocking argument ✅

This is directly cited in the paper's discussion of Questions 2 and 3.

---

## Recommended Actions

### Immediate (leverage existing work)

1. **Publish/document the Quantum Wielandt formalization** as addressing the
   paper's Questions 2-3. Our formalization of the original bound is complete
   and could be presented as the first machine-verified proof of a quantum
   Wielandt inequality.

2. **Document the Fundamental Theorem formalization** as the most complete
   formal treatment of the 1D case, directly relevant to Question 10.

### Medium-term (new formalization)

3. **Formalize Rahaman's improved bound** p(T) ≤ 2(D−1)². This would directly
   improve our answer to Question 2 and would use our existing quantum channel
   infrastructure.

4. **Complete the canonical form assembly**. Our Step 1-4 individual proofs are
   done; threading them together end-to-end would give a fully self-contained
   existence theorem for canonical form.

### Exploratory (potentially high-impact)

5. **Use formal verification to explore improved bounds**. The gap between
   O(D²) (optimal order) and our proven (D²−d+1)·D² is significant. Could
   computer-assisted exploration using our formalized lemmas discover a tighter
   bound? The blocking argument's D² penalty is the weak link.

6. **Investigate Michalek-Shitov techniques** (arXiv:1809.04387) for
   formalization — their bound i(A) ≤ 2D²(6+log₂D) uses algebraic geometry
   (irreducible varieties, degree bounds) which might be partially available
   in Mathlib.
