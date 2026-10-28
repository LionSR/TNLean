# Matrix concentration for the LVV construction

The relevant sources are LVV, [arXiv:1307.5143v1](https://arxiv.org/abs/1307.5143v1), Section 2.3.1, and the [published Methods theorem and supplementary proof](https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf), DOI 10.1038/nphys3345. The distinction between their ground-energy dependences is recorded in [the sampling note](../paper-gaps/lvv13_sampling_ground_energy.tex). This audit concerns the pinned Mathlib v4.35.0-rc3 and QICLean revision `c97ffd63d9b52bdec7191d25aca66b9af7a2f872`.

The finite uniform specialization of the alternating-adjoint moment bound below is now proved by `Matrix.average_norm_average_pow_le_of_centered` in `TNLean/Algebra/FiniteMatrixMoments.lean`. Its hypotheses are finite nonempty sample and matrix index sets, exact centering of each sample family, a uniform operator-norm bound, and an integer moment order $p\ge1$. It assumes none of the word count, cancellation, spectral comparison or moment estimate as additional hypotheses. The general probability formulation, the sharp matrix Bernstein theorem and the source-correct sampler remain separate outstanding tasks.

## A sufficient moment estimate

Let $N,\ell\ge1$ and $R\ge0$. Let $X_1,\ldots,X_\ell$ be independent random complex $N\times N$ matrices of common mean $A$, with $\|X_j-A\|\le R$ almost surely. Fix an accuracy $\eta>0$. Put $Y_j=X_j-A$ and consider the self-adjoint dilation

$$
H_j=\begin{pmatrix}0&Y_j\\Y_j^*&0\end{pmatrix}.
$$

It has mean zero and norm $\|H_j\|=\|Y_j\|\le R$. Also $\|\sum_jH_j\|=\|\sum_jY_j\|$. For every integer $p\ge1$, expand the trace of $(\sum_jH_j)^{2p}$ as a sum over ordered words in the sample labels.

1. A word with a label appearing exactly once has zero expectation. Condition on all the other samples, integrate the unique occurrence, and use $\mathbb EH_j=0$. Noncommutativity does not affect this argument: the factors to either side remain in their original order.
2. Every remaining word uses at most $p$ labels. Its number is at most $\ell^p p^{2p}$: each such word factors as a map from its $2p$ positions to $p$ places followed by a map from those places to the $\ell$ labels. Unused places can be filled with the first label. The case $\ell=0$ is empty and can be separated.
3. Each word contributes absolute expected trace at most $2N R^{2p}$. This follows from $|\operatorname{tr}B|\le2N\|B\|$ and submultiplicativity.
4. Since the sum is Hermitian, its even spectral powers are nonnegative and $\|\sum_jH_j\|^{2p}\le\operatorname{tr}((\sum_jH_j)^{2p})$.

Consequently,

$$
\mathbb E\left\|\frac1\ell\sum_{j=1}^{\ell}X_j-A\right\|^{2p}
\le 2N\left(\frac{p^2R^2}{\ell}\right)^p,
$$

and Markov's inequality gives

$$
\Pr\left(\left\|\frac1\ell\sum_{j=1}^{\ell}X_j-A\right\|\ge\eta\right)
\le 2N\left(\frac{p^2R^2}{\ell\eta^2}\right)^p.
$$

For a target failure probability $0<\delta<1$, choose

$$
p\ge\max\{1,\lceil\log_4(2N/\delta)\rceil\},
\qquad
\ell\ge4p^2R^2/\eta^2.
$$

The failure probability is at most $\delta$. On an $n$-site chain of fixed local dimension $d$, $N=d^n$ and $p=O(n+\log(1/\delta))$. Thus the sample count is polynomial whenever $R$, $1/\eta$, and $\log(1/\delta)$ are polynomial. This estimate is weaker than Tropp's variance-sensitive matrix Bernstein inequality but has the required logarithmic dependence on the Hilbert-space dimension.

## An alternative using alternating adjoints

The same method can avoid the dilation. Write $S=\sum_jY_j$ and expand $\operatorname{tr}((S^*S)^p)$ into ordered words of length $2p$, with adjointed and unadjointed factors alternating. A singleton sample label again gives zero expectation, since $\mathbb EY_j=\mathbb EY_j^*=0$. The remaining words obey the same $\ell^p p^{2p}$ count, and each contributes absolute expected trace at most $NR^{2p}$. The positive semidefinite spectral theorem gives $\|S\|^{2p}\le\operatorname{tr}((S^*S)^p)$. This proves the displayed moment and probability estimates with $N$ in place of $2N$. It requires neither a dilation norm identity nor a changed sampler. The finite uniform version of this argument is now formalized by `Matrix.average_norm_average_pow_le_of_centered`, including the alternating expansion, singleton cancellation, spectral comparison and their composition. The corresponding theorem for general independent random matrices and the sharp concentration theorem remain unproved.

## Proved finite ingredients and remaining probability results

- `Fintype.card_even_words_without_singleton` in `TNLean/Algebra/NoSingletonWords.lean` proves the bound $\ell^p p^{2p}$ for words of length $2p$ with no singleton letter, by the finite-fiber count and factorization described above. It is a counting theorem only.
- `Fintype.sum_pow_eq_sum_ordered_words` in QICLean's `Algebra/FiniteSumPowers.lean` gives the ordered expansion without any commutativity assumption.
- QICLean's `Probability/IndependentCovariance.lean` supplies product-measure integration identities. Mathlib supplies `MeasureTheory.integral_pi`, finite product probability measures, independence, and scalar Markov bounds.
- `Fintype.sum_ordered_word_eq_zero_of_singleton` in `TNLean/Algebra/SingletonWordCancellation.lean` proves singleton cancellation for finite independent uniform assignments into any noncommutative semiring, allowing position-dependent factors. It uses `Equiv.funSplitAt`, `Equiv.sum_comp` and `Fintype.sum_prod_type` to isolate the unique sample coordinate. The existing ordered product `MultilinearMap.mkPiAlgebraFin`, together with `MultilinearMap.map_update_sum` and `MultilinearMap.map_update_zero`, then gives cancellation. There is no new product decomposition and no conditional-expectation hypothesis.
- `Matrix.average_norm_average_pow_le_of_centered` proves the complete finite uniform moment estimate with coefficient $N$. The alternating expansion uses `MultilinearMap.map_sum` and `List.ofFn_fin_repeat`; the per-word bound uses `Matrix.PosSemidef.norm_trace_mul_le` at the identity, `List.nnnorm_prod_le` and `List.prod_le_pow_length`; the spectral comparison uses `CFC.norm_pow`, `Matrix.l2_opNorm_conjTranspose_mul_self` and `Matrix.PosSemidef.l2_opNorm_le_trace_re`. These steps are derived inside the proof. No Hermiticity assumption is imposed on the samples.
- `Matrix.finite_uniform_tail_bound_of_centered` in `TNLean/Algebra/FiniteMatrixSampling.lean` proves the finite Markov consequence: the fraction of assignments with sample-mean norm at least $\eta$ is at most $N(p^2R^2/(\ell\eta^2))^p$. The same module proves existence when this bound is less than one, and gives the sufficient conditions $N<4^p$ and $\ell\eta^2\ge4p^2R^2$. For an uncentered family of norm at most $R$, it derives the norm bound $2R$ after subtracting the uniform mean and proves approximation of that mean under $\ell\eta^2\ge16p^2R^2$. The corresponding general probability theorem, sharp matrix Bernstein inequality and source sampler remain separate tasks.
- An alternative is to sample $(C^mP_I+C^mP_I^*)/2$, whose expectation is the Hermitian ideal power. Then no dilation is needed. The sampler is changed explicitly, and the adjoint words at most double the number of product terms; their bond estimates must be proved. This does not establish the original sampler's norm estimate.

The pinned QICLean trace-power Lieb concavity statements do not directly provide concavity of $B\mapsto\operatorname{tr}\exp(H+\log B)$. No Golden–Thompson or matrix Bernstein theorem was found in the pinned libraries. The finite moment proof avoids both results.

## The ground-energy dependence remains essential

For the original samples, the crude norm bound is $R\le C^m+1$, where $C=(1-E_0/n)^{-1}$. The normalization estimate in the sampling note gives, at a suitable spectral power,

$$
C^{2m}\le n^2Q^{2E_0/\varepsilon}.
$$

The moment method therefore retains the energy-dependent polynomial exponent of the publication. It does not prove a uniform polynomial sample count for extensive ground energy. The commuting counterexample in the note rules out that inference. The unrestricted construction in issues #9822–#9823 requires a different approximate projection; the published supplement points to Huang's construction, arXiv:1406.6355, for this purpose.

The sharp matrix Bernstein inequality stated in #9822 remains an outstanding task in its own right. The finite uniform moment estimate and its Markov corollary give sample existence under explicit norm and cardinality bounds; they do not complete that sharp concentration theorem or construct the source-specific sampled filter. Both the stated concentration theorem and a correct sampler with the required ground-energy dependence remain outstanding under #9822–#9823.


## A possible route to the sharp i.i.d. theorem

For the explicitly identically distributed formulation in #9822, full Lieb log-MGF concavity may be unnecessary. Let $Y_1,\ldots,Y_\ell$ be independent copies of a centered Hermitian $N\times N$ matrix $Y$, with $\|Y\|\le R$ almost surely. For $\theta\ge0$, Golden–Thompson and conditioning give

$$
\mathbb E\operatorname{tr}\exp\left(\theta\sum_jY_j\right)
\le N\left\|\mathbb E\exp(\theta Y)\right\|^\ell.
$$

For $R>0$, the scalar exponential majorant, applied by functional calculus, gives

$$
\exp(\theta Y)\le I+\theta Y+g_R(\theta)Y^2,
\qquad
g_R(\theta)=\frac{e^{\theta R}-1-\theta R}{R^2}.
$$

After taking expectations, centering removes the linear term. Consequently

$$
\left\|\mathbb E\exp(\theta Y)\right\|
\le\exp\left(g_R(\theta)\left\|\mathbb EY^2\right\|\right).
$$

The case $R=0$ is separate and immediate. The resulting scalar optimization is the usual Bernstein argument. For non-Hermitian square samples, a Hermitian dilation has dimension $2N$ and variance norm $\max\{\|\mathbb EYY^*\|,\|\mathbb EY^*Y\|\}$. This requires the dilation identities to be proved. Golden–Thompson, the matrix exponential majorant, the required probability argument and the final sharp tail bound remain unproved here.

For nonidentically distributed samples, the same conditioning argument controls a sum of individual variance norms. It does not by itself give the sharper norm of the summed variances. This is the distinction for which a Lieb-based argument may be needed.

## Location of the general probability development

A general matrix probability theorem belongs in QICLean. Before it uses these finite ingredients, move `NoSingletonWords.lean`, `SingletonWordCancellation.lean`, `FiniteMatrixMoments.lean` and `FiniteMatrixSampling.lean` together to QICLean, with the first two under `Algebra/` and the latter two under `Analysis/`. Their proofs depend only on Mathlib and existing QICLean results. QICLean must not import the TNLean versions. The current placement permits verification against the pinned companion revision while keeping the later order of dependencies explicit.


## The proved Lieb concavity alternative

A direct derivation is now formalized in `TNLean/Algebra/TraceExpLogConcavity.lean`. The theorem `Matrix.concaveOn_trace_exp_add_log` proves concavity of $A\mapsto\operatorname{Re}\operatorname{tr}\exp(H+\log A)$ on the positive-definite cone for every Hermitian $H$. The proof follows [Tropp, *From joint convexity of quantum relative entropy to a concavity theorem of Lieb*](https://tropp.caltech.edu/papers/Tro12-Joint-Convexity.pdf), Fact 3, Lemma 6 and Theorem 1. It derives unnormalized Klein, the attained trace variational formula and the concavity inequality from QICLean's existing positive-definite relative-entropy joint convexity. No trace normalization or new analytic assumption is imposed.

This provides the concavity needed for the trace-exponential Jensen argument in matrix concentration. Golden–Thompson itself is still unproved here, but it need not be assumed for this route. The finite i.i.d. Bernstein theorem with the variance norm in #9822 remains the next target. The scalar exponential majorant, conditional finite expectation argument, dilation and final tail optimization remain to be proved.

The alternative elementary proof in [Oliveira, arXiv:1004.3821, Section 5](https://arxiv.org/abs/1004.3821) requires a dyadic trace-power comparison and a Lie-product limit; neither was found as a theorem in the pinned libraries. The pinching proof in [Sutter, Berta and Tomamichel, arXiv:1604.03023, Section 2.2](https://arxiv.org/abs/1604.03023) requires spectral pinching and its polynomial tensor-power count. The relative-entropy route uses the existing joint convexity result directly.

`TraceExpLogConcavity.lean` imports only Mathlib and QICLean, so it can be transferred independently to QICLean's `Analysis/` before the probability development. It does not depend on the four finite word, moment and sampling modules above.
