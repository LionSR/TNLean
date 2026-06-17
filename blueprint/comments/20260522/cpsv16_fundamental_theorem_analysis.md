# Notes on the agent's flag for Lemma A.2 / Fundamental Theorem of MPV

*Reference:* Cirac–Pérez‑García–Schuch–Verstraete, *Matrix Product Density Operators: Renormalization Fixed Points and Boundary Theories*, Ann. Phys. **378**, 100 (2017); arXiv:1606.00608v4. Citations below are to the v4 numbering (Appendix A, pp. 29–32 in the manuscript).

---

## 1. What the agent is actually claiming

Restated in plain terms, the flag is:

> The helper lemmas use, as a hypothesis (`hLI`), that the *combined* family
> $\bigl\{|V^{(N)}(A_j)\rangle : j \in \mathcal{A}\bigr\}\,\cup\,\bigl\{|V^{(N)}(B_k)\rangle : k \neq k_0\bigr\}$
> (or its mirror image) is linearly independent for all sufficiently large $N$.
> This is **not** implied by the BNT hypotheses on $A$ and $B$ alone, because a remaining $B_k$ could already be phase‑equivalent to some $A_j$, making the combined family linearly dependent for every $N$. The independence has to come from the fixed‑block argument at the precise block being peeled, not from BNT‑ness.

I want to evaluate two questions:

1. Is the *mathematical observation* about combined‑family dependence correct?
2. Does the **CPSV16 proof itself** need this combined‑family independence, or is the Lean encoding asking for more than the paper actually uses?

**Short answer.** (1) Yes, the observation is correct. (2) The CPSV16 proof does **not** need combined‑family independence — it uses only the per‑tensor BNT independence and an overlap argument. If your Lean structure carries combined‑family independence as a hypothesis, then either (a) you are formalizing a *different*, stronger statement than the paper proves, or (b) your proof structure has been pushed into a peeling‑induction that the paper does not use, and the hypothesis can be eliminated by restructuring.

The agent has correctly noticed a real subtlety. You are not being stupid. But the conclusion the agent draws ("this independence has to come from the fixed‑block argument") is the wrong fix — the right fix is to avoid needing the combined‑family independence at all.

---

## 2. Setup and notation, fixed from the paper

For a tensor $A$ with $D \times D$ matrices $A^i$ ($i = 1, \ldots, d$), the (translationally invariant) MPV is
$$
|V^{(N)}(A)\rangle = \sum_{i_1, \ldots, i_N} \operatorname{tr}(A^{i_1} \cdots A^{i_N}) \,|i_1, \ldots, i_N\rangle.
$$
The transfer operator is $\mathcal{E}_A(X) = \sum_i A^i X A^{i\dagger}$ with matrix representation $E_A = \sum_i A^i \otimes \overline{A^i}$.

**Normal tensor (NT).** $A$ is normal iff $\mathcal{E}_A$ is a *primitive* channel (after blocking, irreducible with trivial peripheral spectrum, equivalently: unique eigenvalue $\lambda = 1$ in modulus, with strictly positive eigenvector). Such MPVs are called normal MPVs (NMPVs).

**Canonical form (CF).** $A^i = \bigoplus_{k=1}^{r} \mu_k A^i_k$ with each $A_k$ normal, and the $\mu_k$ scaled so each transfer operator $\mathcal{E}_k$ has spectral radius 1.

**Basis of normal tensors (BNT).** Definition 2.6 in the paper: NTs $\{A_j\}_{j=1}^{g}$ form a BNT for $A$ iff
1. for each $N$, $|V^{(N)}(A)\rangle$ is a linear combination of the $|V^{(N)}(A_j)\rangle$;
2. there exists $N_0$ such that for all $N > N_0$, the $|V^{(N)}(A_j)\rangle$ are linearly independent.

The decomposition (eq. 20a in the paper) reads
$$
A^i = X \Bigl( \bigoplus_{j=1}^{g} M_j \otimes A^i_j \Bigr) X^{-1}, \qquad |V^{(N)}(A)\rangle = \sum_{j=1}^{g} \Bigl( \sum_{q=1}^{r_j} \mu_{j,q}^N \Bigr) |V^{(N)}(A_j)\rangle,
$$
where $M_j$ is diagonal with entries $\mu_{j,q}$.

**Crucial point about BNT‑ness.** The BNT independence condition (ii) is *internal* to $A$ (or to $B$): it constrains $\{|V^{(N)}(A_j)\rangle\}_{j \in \mathcal{A}}$ alone. It does not say anything about cross‑independence between $A$'s BNT and $B$'s BNT.

---

## 3. The agent's mathematical observation: yes, combined‑family independence is *not* automatic

**Toy counterexample.** Take any normal tensor $C$. Set $A := C$ and $B := C$. Both are in CF, each has BNT $\{C\}$ (a single element), and both BNTs satisfy Definition 2.6 (i) and (ii) trivially. The combined family is
$$
\bigl\{ |V^{(N)}(C)\rangle \bigr\} \,\cup\, \bigl\{ |V^{(N)}(C)\rangle \bigr\} = \{|V^{(N)}(C)\rangle, |V^{(N)}(C)\rangle\},
$$
which is maximally dependent. More generally, whenever any $B_k$ is phase‑equivalent to some $A_j$ — exactly the situation that the Fundamental Theorem is trying to detect — the combined family has dependencies of the form $|V^{(N)}(B_k)\rangle = e^{i\phi_k N} |V^{(N)}(A_j)\rangle$, which hold for *every* $N$.

So combined‑family independence is a strictly stronger statement than BNT‑ness for $A$ and $B$ separately. The agent is right on this.

---

## 4. What does the CPSV16 proof actually use? A slow read

I will walk through the proof of the Fundamental Theorem of MPV as given in the paper (Appendix A, p. 32) step by step, marking each invocation of linear independence and identifying *which* family is involved.

### 4.1 The statement (paper's "Theorem", p. 32)

> Let $A$ and $B$ be two tensors in CF, with BNT $A^i_{k_a}$ and $B^i_{k_b}$ ($k_{a,b} = 1, \ldots, g_{a,b}$), respectively. If for all $N$, $A$ and $B$ generate MPV that are proportional to each other, then: (i) $g_a = g_b =: g$; (ii) for all $k$ there exists $j_k$, phases $\phi_k$, and non‑singular matrices $X_k$ such that $B^i_k = e^{i\phi_k} X_k A^i_{j_k} X_k^{-1}$.

### 4.2 The proof, annotated

The paper's proof reads (verbatim, p. 32, slightly cleaned typography):

> *"To prove the Theorem we reason very similarly as in the proof of Proposition 2.7. Let us first consider $B_k$ for some given $k$. It is not possible that $\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle \to 0$ as $N \to \infty$ for all $j$, since otherwise the MPV generated by $A$ and $B$ could not be proportional for all $N$ (Lemma A.4). Thus, according to Corollary A.3, there must exist one $j_k$ such that $|V^{(N)}(B_k)\rangle = e^{i\phi_k N} |V^{(N)}(A_{j_k})\rangle$. According to Lemma A.2 we have $B_k = e^{i\phi_k} X_k A_{j_k} X_k^{-1}$. We also conclude that $g_a \geq g_b$. But if we had considered $A_k$ to start with, we would obtain $g_b \geq g_a$, so that $g_a = g_b$."*

Let me unpack each step and mark dependencies on linear‑independence facts.

**Step 1.** "Let us first consider $B_k$ for some given $k$. It is not possible that $\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle \to 0$ as $N \to \infty$ for all $j$."

This is a claim of the form: for the fixed block $B_k$, there exists $j$ (depending on $k$) such that $\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle \not\to 0$.

**Justification used:** Lemma A.4. Let me state it precisely.

> **Corollary A.4 (p. 31, paper).** Any set of NMPV $\{V_j\}_{j=1}^{g}$ fulfilling $\langle V_j | V_{j'} \rangle \to \delta_{j,j'}$ for $N \to \infty$ is linearly independent for $N$ sufficiently large.

The paper calls this Lemma A.4 (it is labelled Corollary A.4 — a minor labelling glitch in the text on p. 32, where the same statement is referred to once as Lemma A.4). The content used is what its proof gives, which is the *contrapositive*: if a family of NMPVs becomes pairwise orthogonal in the limit but is supposed to span a particular MPV, you cannot have a vanishing‑in‑all‑directions tail.

**Sharper version of Step 1, in‑gear with what is actually needed.** Suppose, for contradiction, that $\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle \to 0$ for all $j$. The proportionality assumption gives, for $N$ large enough that the MPVs are nonzero,
$$
|V^{(N)}(B)\rangle = \lambda_N |V^{(N)}(A)\rangle.
$$
Take the inner product with $|V^{(N)}(B_k)\rangle$. On the LHS,
$$
\langle V^{(N)}(B_k) | V^{(N)}(B) \rangle = \sum_{k'} \Bigl(\sum_q \nu_{k',q}^N\Bigr) \langle V^{(N)}(B_k) | V^{(N)}(B_{k'}) \rangle.
$$
By Corollary A.3 / Lemma A.2 applied to the BNT of $B$ (Definition 2.6(ii) for $B$ excludes any two distinct BNT elements from being phase‑equivalent, by minimality; combined with Lemma A.2 this forces $\langle V^{(N)}(B_k) | V^{(N)}(B_{k'}) \rangle \to 0$ for $k' \neq k$, and $\to 1$ for $k' = k$). So the LHS behaves like $\sum_q \nu_{k,q}^N$ plus terms vanishing as $N \to \infty$.

For the LHS not to be identically $o(1)$ — which would force $B_k$'s contribution to vanish, contradicting the BNT property — we need $\sum_q \nu_{k,q}^N \not\to 0$. (For the BNT eigenvalues $\nu_{k,q}$, all have modulus 1 by the normalization $\mu \to \nu$ that puts the transfer operator at spectral radius 1; so $\sum_q \nu_{k,q}^N$ is a sum of unit‑modulus complex numbers, which can vanish for some $N$ but cannot tend to 0.)

On the RHS, by assumption all $\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle \to 0$, so
$$
\langle V^{(N)}(B_k) | V^{(N)}(A) \rangle = \sum_j \Bigl(\sum_q \mu_{j,q}^N\Bigr) \langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle \to 0
$$
(provided $\sum_q \mu_{j,q}^N$ is bounded — which it is, being a sum of unit‑modulus numbers). Multiplying by $\lambda_N$ should give the LHS; if $\lambda_N$ is bounded, the RHS $\to 0$ and we get a contradiction with the LHS not going to 0.

The boundedness of $\lambda_N$ is also a consequence of the BNT normalization (both sides are bounded in norm as $N \to \infty$, indeed $\langle V^{(N)}(A) | V^{(N)}(A) \rangle$ tends to a finite positive limit by Lemma A.2 applied to each $A_j$).

**Where the BNT independence is used.** Implicitly, in the step "for the LHS not to be $o(1)$, $B_k$'s contribution must not be canceled by other $B_{k'}$'s". The cleanest formal route is: use the BNT independence of $\{B_k\}$ to expand the proportionality equation in that basis, and conclude that each coefficient must vanish identically — which contradicts $\sum_q \nu_{k,q}^N \not\to 0$.

But — and this is the point — **the linear independence used here is of $\{|V^{(N)}(B_k)\rangle\}_{k=1}^{g_b}$ alone**, not of any combined family.

**Step 2.** "According to Corollary A.3, there must exist one $j_k$ such that $|V^{(N)}(B_k)\rangle = e^{i\phi_k N} |V^{(N)}(A_{j_k})\rangle$."

From Step 1 we have *some* $j$ with $\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle \not\to 0$. By Lemma A.2, the limit $|\langle V^{(N)}(B_k) | V^{(N)}(A_j) \rangle|$ exists and is $0$ or $1$. Combined with not going to $0$, the limit must be $1$. Corollary A.3 then upgrades this to the *exact* equality $|V^{(N)}(B_k)\rangle = e^{i\phi N} |V^{(N)}(A_j)\rangle$ for all $N$.

No further independence assumption is invoked here. Lemma A.2 itself uses no independence — it is the per‑pair statement.

**Step 3.** "According to Lemma A.2 we have $B_k = e^{i\phi_k} X_k A_{j_k} X_k^{-1}$."

Direct application of the dimension/gauge statement in Lemma A.2.

**Step 4 (the count argument).** "We also conclude that $g_a \geq g_b$."

This is where the agent's flag points, so let me look at it carefully.

The map $k \mapsto j_k$ is well defined by Steps 1–3. The claim $g_a \geq g_b$ is equivalent to this map being **injective**. The paper does not state explicitly why it is injective; this is left as an exercise. Let me check.

Suppose $j_{k} = j_{k'}$ for two distinct BNT indices $k \neq k'$ of $B$. Then
$$
|V^{(N)}(B_k)\rangle = e^{i\phi_k N} |V^{(N)}(A_{j_k})\rangle, \qquad |V^{(N)}(B_{k'})\rangle = e^{i\phi_{k'} N} |V^{(N)}(A_{j_k})\rangle,
$$
so $|V^{(N)}(B_k)\rangle = e^{i(\phi_k - \phi_{k'}) N} |V^{(N)}(B_{k'})\rangle$. By Corollary A.3 applied to the pair $(B_k, B_{k'})$, this forces $B_k$ and $B_{k'}$ to be phase‑equivalent BNT elements of $B$. But the BNT minimality (Definition 2.6 (ii) / Proposition 2.7 (ii)) says that no two BNT elements are phase‑equivalent. Contradiction. So $k \mapsto j_k$ is injective, and $g_a \geq g_b$.

**Where the independence is used in Step 4.** Only the BNT minimality of $\{B_k\}$ — that is, condition (ii) of Definition 2.6. This is *not* the linear‑independence condition (ii) of the BNT definition; it is the separate minimality condition (ii) of Proposition 2.7 / the definition of a BNT. The two are different. The linear‑independence condition (ii) of Definition 2.6 is, for completeness, what makes the BNT decomposition unique up to gauge and phase; the minimality (ii) of Proposition 2.7 is what was just used.

(The two conditions are equivalent under the BNT structure, but they enter the argument at different places, and conflating them is a real source of confusion in the Lean encoding.)

**Step 5.** "But if we had considered $A_k$ to start with, we would obtain $g_b \geq g_a$, so that $g_a = g_b$."

Symmetry. Same proof with roles of $A$ and $B$ swapped, using the BNT of $A$.

---

### 4.3 Summary of what the proof uses

To prove the Fundamental Theorem, the proof draws on the following facts:

| Fact | Family that needs to be linearly independent / minimal |
|---|---|
| Lemma A.2 (the dichotomy 0/1 for overlap of two NMPVs) | None — per‑pair statement |
| Corollary A.3 (overlap → 1 implies exact phase equality) | None — per‑pair statement |
| Corollary A.4 (orthogonal‑in‑limit ⇒ independent) | Only the *implicit* family it talks about, never a combined one |
| BNT linear independence (Def. 2.6 (ii)) for $A$ alone | $\{|V^{(N)}(A_j)\rangle\}_{j \in \mathcal{A}}$ |
| BNT linear independence (Def. 2.6 (ii)) for $B$ alone | $\{|V^{(N)}(B_k)\rangle\}_{k \in \mathcal{B}}$ |
| BNT minimality (Def. 2.6 + Prop. 2.7 (ii)) for $A$, $B$ | Per‑tensor — no two BNT elements phase‑equivalent |

**At no point does the proof need the combined family $\{|V^{(N)}(A_j)\rangle\} \cup \{|V^{(N)}(B_k)\rangle\}$ to be linearly independent.**

Indeed it *cannot* — if the conclusion of the Fundamental Theorem holds, every $B_k$ is phase‑equivalent to some $A_{j_k}$, so the combined family is maximally dependent.

---

## 5. Why your Lean helper lemmas might be asking for the wrong thing

The agent reports that the helpers are stated as:

```
eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li
```

with hypothesis `hLI` that the combined family
$$
\bigl\{|V^{(N)}(A_j)\rangle : j \in \mathcal{A}\bigr\}\,\cup\,\bigl\{|V^{(N)}(B_k)\rangle : k \neq k_0\bigr\}
$$
is linearly independent for sufficiently large $N$.

This shape suggests a **peeling induction**: you pick a block $B_{k_0}$, match it to some $A_{j_0}$, remove both, and recurse on the smaller pair. To run such an induction you would want, inductively, that the *remaining* combined family is independent — so that the recursive hypothesis can be applied.

**Two problems with this structure.**

**(a) The hypothesis can never hold once a matching is found.** If at the previous step you proved $|V^{(N)}(B_{k_0})\rangle = e^{i\phi_0 N} |V^{(N)}(A_{j_0})\rangle$, then for every remaining $B_k$ ($k \neq k_0$) that ends up matched to some remaining $A_j$ during the induction, you get a phase equivalence — and at the inductive step before that matching is found, the combined family at the current level might be independent (the matching for *this* level has not yet been carried out), but once you peel, the next level's combined family includes potentially many $B_k, A_{j_k}$ pairs already related. So the inductive hypothesis is fragile.

More concretely: even at the *initial* step, if the original pair $A, B$ has $g_a = g_b = g \geq 2$ and the Fundamental Theorem's conclusion holds, then the combined family already has the linear dependencies $|V^{(N)}(B_k)\rangle - e^{i\phi_k N} |V^{(N)}(A_{j_k})\rangle = 0$ for every $k$. So the hypothesis $hLI$ on the combined family *fails for the actual situation the theorem is about*. The lemma is vacuously vacuous, in a bad way.

**(b) The paper's proof is not a peel‑induction.** It is a one‑shot existence argument applied *independently* to each $B_k$. There is no recursion on a shrinking pair of families. The matching $k \mapsto j_k$ is built block‑by‑block, each block treated independently, with injectivity at the end coming from BNT minimality.

---

## 6. Recommended Lean restructuring

The natural Lean lemma structure that mirrors the actual CPSV16 proof is:

### 6.1 Per‑block existence lemma

```
lemma exists_match_of_proportional
  {A B : Tensor} (hA : IsBNT A) (hB : IsBNT B)
  (hprop : ∀ N, Proportional (V N A) (V N B))
  (k : Fin g_b) :
  ∃ (j : Fin g_a) (φ : ℝ),
    ∀ N, V N (B.block k) = exp (I * φ * N) • V N (A.block j) :=
```

The proof uses:

- Lemma A.2 (per‑pair dichotomy).
- Corollary A.3 (limit‑1 ⇒ exact phase equality for all $N$).
- The BNT linear independence of $\{V^{(N)}(B_k)\}_k$ alone (Def. 2.6 (ii) for $B$).
- The boundedness/non‑vanishing of the BNT eigenvalue sums.
- The proportionality hypothesis.

No combined‑family independence is required.

### 6.2 Injectivity lemma (separately)

```
lemma match_is_injective
  {A B : Tensor} (hA : IsBNT A) (hB : IsBNT B)
  (hprop : ∀ N, Proportional (V N A) (V N B))
  (match_fn : Fin g_b → Fin g_a)
  (φ_fn : Fin g_b → ℝ)
  (h_match : ∀ k N, V N (B.block k) = exp (I * φ_fn k * N) • V N (A.block (match_fn k))) :
  Function.Injective match_fn :=
```

Proof: if $\mathrm{match\_fn}(k) = \mathrm{match\_fn}(k')$ then $B_k$ and $B_{k'}$ are phase‑related, but by BNT minimality for $B$ (Prop. 2.7 (ii)), distinct BNT blocks are not phase‑related. Hence $k = k'$.

This uses *minimality* of the BNT of $B$, again only the per‑tensor property.

### 6.3 The Fundamental Theorem assembled

Bundle 6.1 and 6.2 with the symmetric statement (swap $A, B$) to get $g_a = g_b$. Then 6.1 gives both the matching and the gauge transformation (the second from Lemma A.2's last clause).

---

## 7. Aside: a sub‑step in CPSV16 that I think is worth flagging for your formalization

While we're here, two small things that are not bugs but are worth being explicit about for Lean:

**(i) The "$\sum_q \nu_{k,q}^N \not\to 0$" claim.** This is invoked implicitly in Step 1 of the proof (Section 4.2 above). The paper does not separately prove that a sum of unit‑modulus complex numbers cannot tend to zero in a fixed‑length sum — though it is true (a sum $\sum_{q=1}^{r_j} e^{i N \theta_q}$ is almost‑periodic, hence does not tend to 0; in fact its $\limsup$ over $N$ is bounded below by Bohr almost‑periodicity, or more simply by Lemma A.5 / Vandermonde nondegeneracy).

For Lean, this is worth factoring as a small lemma: a non‑empty finite sum of complex numbers of modulus 1 has $\limsup_{N \to \infty} |\sum_q z_q^N| > 0$, indeed $\geq 1$ (taking $N = 0$).

Wait — that's actually trivial. $N$ is a free variable ranging over $\mathbb{N}$, and at $N = 0$ the sum is $r_j \neq 0$. So the sequence $N \mapsto \sum_q \nu_{k,q}^N$ is *not* identically zero. What we need is slightly stronger: it does not *tend* to zero. This follows from almost‑periodicity, or from Lemma A.5 if you prefer the path the paper uses.

Actually re‑reading the paper, the argument they wrap into Lemma A.5 + Corollary A.4 is exactly designed to bypass this — Corollary A.4 says that pairwise‑limit‑orthogonal NMPVs are independent for $N$ large, and the proof of the Fundamental Theorem applies this to $\{V^{(N)}(B_k)\}_{k}$ to extract that the coefficients $\sum_q \nu_{k,q}^N$ are non‑degenerate as $N$ varies.

**(ii) The "$X$ is an isometry" line in Lemma A.2's proof.** I mentioned this in the previous round. The Cauchy–Schwarz‑plus‑(A.1a)/(A.1b) calculation gives $X^\dagger X = c \mathbf{1}$ for some $c > 0$ (because $X^\dagger X$ is a fixed point of the unital primitive map $\mathcal{E}_a^*$). Rescaling $X$ sets $c = 1$. Then $X$ is an isometry $\mathbb{C}^{D_a} \to \mathbb{C}^{D_b}$, which requires $D_a \leq D_b$; the symmetric argument gives $D_a \geq D_b$, hence equality and $X$ is unitary.

The paper's phrasing "$\sum_i A^{i\dagger}_a X^\dagger X A^i_a = X^\dagger X = \mathbf{1}$" elides the rescaling. For Lean, carry $X^\dagger X = c\mathbf{1}$ as the actual conclusion and rescale at the end.

**(iii) The "subspace where $A^i_a$ vanishes" phrasing.** Also from before. The argument is that $\ker X$ is a common invariant subspace of $\{A^i_a\}_i$ (not a subspace where they vanish), which is forbidden by normality. The paper's phrasing is sloppy; the argument is correct.

---

## 8. What I'd say to the agent

The agent has spotted a real issue with the *Lean encoding*, not with the *paper*. Specifically:

> "This independence has to come from the fixed‑block argument at the precise block being peeled, not from the BNT hypotheses alone."

The first half is wrong: the independence **does not come from the fixed‑block argument either**, because the combined family is in fact *not* independent at the level of the Fundamental Theorem's conclusion. The hypothesis as stated is too strong — it would make the lemma vacuously true (or vacuously inapplicable) in the regime where the Fundamental Theorem actually applies.

The second half is right: the combined‑family independence does not follow from BNT‑ness, which the agent has correctly diagnosed.

The fix is to restructure the helper lemmas so they never need combined‑family independence. The CPSV16 proof is not a peel‑induction — it is a one‑shot per‑block existence statement plus a separate injectivity (minimality) argument. Mirroring that structure in Lean should let you delete `hLI` from the helpers entirely.

---

## 9. References

- Cirac, Pérez‑García, Schuch, Verstraete, *Matrix Product Density Operators: Renormalization Fixed Points and Boundary Theories*, Ann. Phys. **378**, 100 (2017); [arXiv:1606.00608v4](https://arxiv.org/abs/1606.00608). Appendix A (pp. 29–32) contains Definitions A.1 (CFII), Lemma A.2, Corollaries A.3 and A.4, Lemma A.5, the proof of Proposition 2.7, and the Fundamental Theorem of MPV.
- Cirac, Pérez‑García, Schuch, Verstraete, *Matrix product states and projected entangled pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. **93**, 045003 (2021). Section IV.A.4 (Theorem IV.4 and Corollary IV.5) restates the Fundamental Theorem and points to Cirac et al. 2017a for the proof details.
- De las Cuevas, Cirac, Schuch, Pérez‑García, *Irreducible forms of Matrix Product States: Theory and Applications*, [arXiv:1708.00029](https://arxiv.org/abs/1708.00029). An alternative formulation (irreducible form rather than CF + BNT) where the analogous fundamental theorem is proved without requiring the periodicity blocking. Worth comparing if you want a cleaner formalization target.
- Wolf, *Quantum Channels and Operations — Guided Tour* (2012), Chapter 6 (especially Theorems 6.2, 6.6, 6.7). Standard reference for primitivity and irreducibility of CP maps; equivalent characterizations needed for the "normal tensor ⇒ no common nontrivial invariant subspace of $\{A^i\}$" fact used in Lemma A.2's proof.
