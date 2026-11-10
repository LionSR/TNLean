# Matrix concentration for the LVV construction

The sources are LVV, [arXiv:1307.5143v1](https://arxiv.org/abs/1307.5143v1), Theorem 2.13 and Section 2.3.1, and [Tropp, *User-friendly tail bounds for sums of random matrices*](https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf), Theorem 1.6. The [published LVV Methods and supplementary proof](https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf) retain a ground-energy-dependent sampling exponent. That distinction is recorded in [the normalized-power sampling note](../paper-gaps/lvv13_sampling_ground_energy.tex).

## The companion concentration theorem

`Matrix.measureReal_le_norm_average_sub_le` in QICLean's `Probability/MatrixBernstein.lean` proves the general iid complex square-matrix theorem. For independent identically distributed measurable matrices with actual common mean $\mu$, positive sample count $\ell$, and $\|X_j-\mu\|\le R$ almost surely, it gives

$$
\Pr\left(\left\|\ell^{-1}\sum_jX_j-\mu\right\|\ge t\right)
\le2N\exp\left(-\frac{\ell t^2}{2\sigma^2+2Rt/3}\right),
\qquad t\ge0,
$$

where $\sigma^2=\max\{\|\mathbb EYY^*\|,\|\mathbb EY^*Y\|\}$ and $Y=X_0-\mu$. The actual centered Gram expectations, coefficient $1/3$ and dimension factor $2N$ are retained. The source's omitted variance norms are clarified in the [QICLean variance note](https://sirui-lu.com/QICLean/paper-gaps/lvv13_matrix_bernstein_variance_norm.pdf). No local copy of that companion-owned note is retained.

QICLean also proves the general rectangular theorem `Matrix.measureReal_le_norm_sum_le`, with the norm of each sum of Gram expectations as its variance. Its analytic ingredients are the proved Lieb concavity in `Analysis/LiebTraceExponential.lean`, the scalar and matrix Bernstein estimates in `Analysis/MatrixBernsteinScalar.lean` and `Analysis/MatrixBernsteinInputs.lean`, the rectangular Hermitian dilation, and the bounded matrix cumulant argument in `Probability/MatrixCumulantSubadditivity.lean`. The latter's bounded-summand scope is recorded in the [QICLean scope note](https://sirui-lu.com/QICLean/paper-gaps/tropp12_bounded_summands_scope.pdf).

These results supersede TNLean's unused generic trace-exponential and sharp-concentration proof chain. The companion theorem uses measurable random matrices, as in the source. Unused TNLean formulations admitting only almost-everywhere measurability and separate finite-uniform sharp variants are not retained as compatibility declarations.

## The completed finite moment argument

The elementary finite argument remains available in QICLean. `Algebra/NoSingletonWords.lean` and `Algebra/SingletonWordCancellation.lean` retain the counting and cancellation declarations. `Probability/FiniteMatrixMoments.lean` and `Probability/FiniteMatrixSampling.lean` retain the matrix moment, Markov and sample-existence declarations with their existing mathematical signatures.

For centered complex $N\times N$ samples $X_b(a)$ of norm at most $R$, let $\ell$ be the positive number of sample labels. For an integer $p\ge1$, put $S_\sigma=\sum_bX_b(\sigma(b))$ and expand $\operatorname{tr}((S_\sigma^*S_\sigma)^p)$.

1. A word containing a sample label exactly once has zero expectation. `Fintype.sum_ordered_word_eq_zero_of_singleton` separates that coordinate using `Equiv.funSplitAt`; `MultilinearMap.map_update_sum` and `map_update_zero` cancel its centered factor without changing the ordered product.
2. The remaining words use at most $p$ labels. `Fintype.card_even_words_without_singleton` bounds their number by $\ell^p p^{2p}$, by factoring their $2p$ positions through a set of $p$ elements.
3. Each word contributes absolute expected trace at most $NR^{2p}$, using $|\operatorname{tr}B|\le N\|B\|$ and submultiplicativity.
4. The positive spectral theorem gives $\|S_\sigma\|^{2p}\le\operatorname{tr}((S_\sigma^*S_\sigma)^p)$. Summation and normalization therefore give

$$
\mathbb E\left\|\ell^{-1}\sum_bX_b\right\|^{2p}
\le N\left(\frac{p^2R^2}{\ell}\right)^p.
$$

`Matrix.average_norm_average_pow_le_of_centered` proves this finite uniform estimate. `Matrix.finite_uniform_tail_bound_of_centered` gives its Markov consequence

$$
\Pr\left(\left\|\ell^{-1}\sum_bX_b\right\|\ge\eta\right)
\le N\left(\frac{p^2R^2}{\ell\eta^2}\right)^p.
$$

For $0<\delta<1$, it suffices to choose $p\ge\max\{1,\lceil\log_4(N/\delta)\rceil\}$ and $\ell\eta^2\ge4p^2R^2$. On an $n$-site chain of fixed local dimension, $\log N=O(n)$, so this is polynomial whenever $R$, $\eta^{-1}$ and $\log(1/\delta)$ are polynomial. For an uncentered family of norm at most $R$, subtracting its actual uniform mean derives the bound $2R$; `Matrix.exists_average_sub_mean_norm_lt` supplies mean approximation under $N<4^p$ and $\ell\eta^2\ge16p^2R^2$.

## One family with matrix approximation and controlled word counts

For $\ell$ uniform independent words of length $m$ over $n\ge1$ letters, QICLean's `Probability/UniformWordFrequency.lean` derives the exact moment $\mathbb E2^{C_a(w)}=(1+1/n)^m$. It bounds the actual exceptional fraction by

$$
n\ell\frac{(1+1/n)^m}{2^u}\le n\ell\exp(m/n-u\log2).
$$

The logarithmic ceiling of $(m/n+\log(n\ell/\delta))/\log2$, truncated below at zero, gives failure probability at most $\delta$. Empty sample families are allowed for this frequency theorem.

`Probability/JointWordSampling.lean` uses a nonempty sample family. For an arbitrary word-dependent matrix $Y(w)$ with $\|Y(w)\|\le R$ and its actual uniform mean $\mu$, it bounds the union of matrix-approximation failure and any excessive letter count on the same full finite word-family space by

$$
N\left(\frac{4p^2R^2}{\ell\eta^2}\right)^p
+n\ell\exp(m/n-u\log2).
$$

If this numerical sum is below one, one actual sample simultaneously satisfies mean-approximation error below $\eta$ and all counts below $u$. Neither a successful sample nor a concentration inequality is an extra hypothesis.

## The physical normalization remains a separate application

For the original normalized-power samples, the uncentered operator norm is bounded by $C^m$, where $C=(1-E_0/n)^{-1}$. At a suitable spectral power, the sampling note proves

$$
C^{2m}\le n^2Q^{2E_0/\varepsilon}.
$$

Thus both the moment argument and the source Bernstein estimate retain the ground-energy dependence in the publication. The generic joint theorem does not identify a physical word product with the desired Hamiltonian power: that application must prove the actual mean identity, the operator-norm bound and the frequency-dependent bond estimate. A polynomial sample count with degree independent of extensive $E_0$ does not follow from this original sampler. These statements concern the normalized-power route; the separate physical-filter viable-set induction has its own construction.
