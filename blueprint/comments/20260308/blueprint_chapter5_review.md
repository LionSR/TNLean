
# Blueprint Review – Chapter 5 (Quantum Perron–Frobenius Theory)

This document records the **full adversarial review of Chapter 5** of `blueprint20260302.pdf`.

The review follows the **Blueprint Review Protocol** used for previous chapters and incorporates:

- global chapter assessment
- statement-by-statement analysis
- cross-chapter dependency checks (Chapters 2–4 → Chapter 5)
- literature consistency checks
- structural and stylistic issues
- cleanup recommendations

The goal of the chapter is to establish the **Quantum Perron–Frobenius theorem for injective MPS transfer maps**.

---

# 1. Role of Chapter 5 in the Blueprint

Chapter 5 proves the Perron–Frobenius structure of the MPS transfer operator.

Given a tensor

A = {A_i}_{i=1}^d

define the transfer map

E_A(X) = Σ_i A_i X A_i†.

The chapter establishes that for **injective tensors**:

1. A nonzero positive semidefinite fixed point exists.
2. Any nonzero positive semidefinite fixed point is **positive definite**.
3. The positive definite fixed point is **unique up to scaling**.

This is the finite-dimensional version of the **quantum Perron–Frobenius theorem**.

These results are later used to:

- normalize tensors via gauge transformations
- analyze the spectral structure of transfer operators
- derive contraction properties in Chapter 6.

---

# 2. Global Assessment

Overall the chapter is **mathematically sound** and structurally stronger than Chapters 2 and 3.

Strengths:

- Clear Perron–Frobenius structure.
- Correct use of the channel framework developed in Chapter 4.
- The proof of positive definiteness (Theorem 5.1) is particularly clean.

However several issues remain:

1. **Normalization subtleties inherited from Chapter 4.**

   The section titled “Doubly stochastic gauge” may mislead readers into thinking that
   both unitality and trace-preservation can be enforced simultaneously by a single
   similarity gauge. This is not generally true for a single MPS tensor.

2. **A formalization artifact (Theorem 5.6).**

   The statement about the case D = 0 is mathematically trivial and does not belong
   in the conceptual exposition of the blueprint.

3. **Minor logical ordering issues** (irreducible version appears after the injective case).

Overall evaluation:

| Category | Evaluation |
|---|---|
Mathematical correctness | Good |
Conceptual clarity | Mostly good |
Structural quality | Moderate |
Cross-chapter consistency | One issue (gauge normalization) |

---

# 3. Statement-by-Statement Review

## Theorem 5.1 — Positive semidefinite fixed point is positive definite

Statement:

If A is injective and ρ ≥ 0 with E_A(ρ) = ρ and ρ ≠ 0,
then ρ is positive definite.

Proof idea:

1. Suppose v†ρv = 0.
2. Then ρv = 0.
3. From the fixed-point equation:

   ρ = Σ_i A_i ρ A_i†

   one obtains

   ρ A_i† v = 0 for all i.

4. Thus ker(ρ) is invariant under all A_i†.
5. Injectivity implies span{A_i} = M_D(C),
   so ker(ρ) is invariant under all matrices.
6. Hence ker(ρ) = C^D and ρ = 0, contradiction.

Assessment:

✔ Correct  
✔ Uses injectivity in an essential way  
✔ Cleaner than the generic irreducible-map argument

However one proof step is slightly compressed:

> invariance under all matrices ⇒ kernel is whole space.

A formalization will likely require a short linear-algebra lemma stating that
a nonzero subspace invariant under the full matrix algebra must equal the entire space.

---

## Theorem 5.2 — Irreducible version

Statement:

If E_A is irreducible and ρ ≥ 0 is a nonzero fixed point,
then ρ is positive definite.

Assessment:

✔ Correct

However the ordering is slightly awkward.

The irreducible-map statement is the **more general theorem**, and the injective case
(Theorem 5.1) is a special case via

injectivity ⇒ irreducibility (Chapter 4).

Thus the irreducible theorem should ideally appear first.

---

## Theorem 5.3 — Uniqueness of positive semidefinite fixed point

Statement:

If ρ, σ ≥ 0 are nonzero fixed points of E_A for an injective tensor,
then

σ = c ρ

for some scalar c.

Proof structure:

1. By Theorem 5.1 both matrices are positive definite.
2. Write

   ρ = S S†.

3. Define

   H = (S†)⁻¹ σ S⁻¹.

4. Let c₀ be the minimal eigenvalue of H.
5. Then

   τ = σ − c₀ ρ

   is positive semidefinite and fixed by the channel.
6. τ is singular, contradicting Theorem 5.1 unless τ = 0.

Assessment:

✔ Correct  
✔ Standard Perron–Frobenius argument

Minor issue:

The statement allows c ∈ C, but the proof produces

c > 0

since it is an eigenvalue of a positive definite Hermitian matrix.

Thus the statement should specify

c ∈ ℝ_{>0}.

---

## Theorem 5.4 — Existence of a PSD fixed point

Assumption:

Σ_i A_i† A_i = I

so that E_A is trace-preserving.

Conclusion:

There exists a nonzero positive semidefinite fixed point.

Proof:

Uses the Cesàro fixed-point theorem for channels established in Chapter 4.

Assessment:

✔ Correct  
✔ Proper use of Chapter 4 results

However the theorem unnecessarily assumes **injectivity**.
Existence of a PSD fixed point follows from the channel property alone.

---

## Theorem 5.5 — Quantum Perron–Frobenius theorem

Statement:

For injective tensors with the normalization

Σ_i A_i† A_i = I

there exists a **unique positive definite fixed point up to scaling**.

Proof:

Combines Theorems 5.4, 5.1, and 5.3.

Assessment:

✔ Correct  
✔ Standard Perron–Frobenius result

---

## Theorem 5.6 — Case D = 0

Statement:

The theorem holds without assuming D ≥ 1 because
the zero matrix is vacuously positive definite when D = 0.

Assessment:

This is a **formalization artifact**.

Problems:

1. Positive definiteness of a 0×0 matrix is purely conventional.
2. A bond dimension D = 0 does not represent a meaningful tensor network state.

Recommendation:

Remove this theorem from the blueprint narrative.
If needed for Lean formalization, treat it as an internal implementation detail.

---

# 4. Gauge Normalization Section

## Section title: “Doubly stochastic gauge”

This section contains two theorems.

### Theorem 5.7 — Unital gauge

If ρ is a fixed point of E_A and

ρ = S S†,

then

A_i' = S⁻¹ A_i S

satisfies

Σ_i A_i' (A_i')† = I.

Thus the gauged transfer map is **unital**.

---

### Theorem 5.8 — Trace-preserving gauge

If σ is a fixed point of the adjoint map E_A* and

σ = S† S,

then

A_i' = S A_i S⁻¹

satisfies

Σ_i (A_i')† A_i' = I.

Thus the gauged transfer map is **trace-preserving**.

---

### Structural issue

The section title suggests that both properties can be imposed simultaneously.

However the theorems only produce:

- one gauge that makes the map **unital**
- another gauge that makes the map **trace-preserving**

These are generally **different similarity transformations**.

Therefore the section title is misleading.

Recommendation:

Rename the section to something like:

> Gauge normalizations from faithful fixed points

or

> Unital and trace-preserving gauges.

---

# 5. Cross-Chapter Consistency Check

Before producing this review, all previous chapter review files were re-examined.

The following checks were performed.

---

## 5.1 Chapter 2 issues

Chapter 2 issues included:

- MPV vs MPS terminology drift
- implicit MPV coefficient definition
- redundant definitions

Impact on Chapter 5:

None of these affect Chapter 5 mathematically.

Chapter 5 only depends on the tensor matrices A_i and their transfer map.

Thus Chapter 2 issues do **not propagate**.

---

## 5.2 Chapter 3 issues

Chapter 3 involved:

- trace-pairing arguments
- algebra generated by tensor words
- injectivity definition

Chapter 5 only uses the property

span{A_i} = M_D(C).

This is exactly the injectivity definition used in Chapter 3.

Therefore Chapter 3 issues do **not affect the Perron–Frobenius results**.

---

## 5.3 Chapter 4 issues

Chapter 4 introduced the CP-map framework and channel theory.

Chapter 5 relies on several of those results:

- channel normalization
- existence of fixed points via Cesàro averages
- irreducibility properties

These dependencies are correct.

However one Chapter-4 issue **does propagate**.

### Important inherited issue

The Chapter-4 review established that a single MPS tensor
cannot generally be gauge-transformed so that its transfer map is both

- unital and
- trace-preserving

simultaneously.

Chapter 5 currently names Section 5.4

“Doubly stochastic gauge”.

But the theorems in that section only construct
two separate gauges.

Thus the normalization language must be handled carefully
to avoid contradicting the Chapter-4 analysis.

---

# 6. Literature Consistency

The chapter references:

- Evans–Høegh-Krohn (1978)
- Wolf (2012)

The results align with standard finite-dimensional
Perron–Frobenius theory for completely positive maps.

However the actual proof structure is closer to
finite-dimensional channel arguments than to the
general C*-algebraic treatment in Evans–Høegh-Krohn.

---

# 7. Cleanup Checklist

Before considering the chapter finalized, the following changes are recommended.

1. Swap the order of Theorems 5.1 and 5.2 so that the irreducible version appears first.
2. In Theorem 5.3 restrict the scalar to c > 0.
3. Remove the injectivity assumption from Theorem 5.4.
4. Remove or demote Theorem 5.6.
5. Rename Section 5.4 to avoid the misleading phrase “doubly stochastic”.
6. Add an explicit remark clarifying that the unital and trace-preserving gauges
   are generally different transformations.

---

# Final Assessment

The Perron–Frobenius structure established in Chapter 5 is mathematically correct.

The main issues are:

- presentation details
- normalization terminology

Once these are corrected, the chapter forms a solid bridge between

the operator-theoretic framework of Chapter 4 and the
spectral analysis of transfer operators in Chapter 6.