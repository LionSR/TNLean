# Matrix concentration for the LVV construction

The sources are LVV, [arXiv:1307.5143v1](https://arxiv.org/abs/1307.5143v1), Theorem 2.13 and Section 2.3.1, and [Tropp, *User-friendly tail bounds for sums of random matrices*](https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf), Theorem 1.6. The published LVV ground-energy correction is in the [Methods and supplementary proof](https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf), DOI 10.1038/nphys3345. This audit uses Mathlib v4.35.0-rc3 and pinned QICLean revision `c97ffd63d9b52bdec7191d25aca66b9af7a2f872`.

## The completed iid matrix Bernstein theorem

`Matrix.probability_matrix_bernstein` in `TNLean/Algebra/MatrixBernstein.lean` proves the general-probability complex square-matrix inequality used by LVV. Let $X_1,\ldots,X_\ell$ be actually independent and identically distributed $d\times d$ complex random matrices on a probability space, with $d,\ell\ge1$, common actual mean $\mu$, and $\|X_j-\mu\|\le R$ almost surely. Put $Y=X_1-\mu$ and

$$
\sigma^2=\max\{\|\mathbb EYY^*\|,\|\mathbb EY^*Y\|\}.
$$

For every $t\ge0$ the theorem gives

$$
\Pr\left(\left\|\frac1\ell\sum_{j=1}^{\ell}X_j-\mu\right\|\ge t\right)
\le2d\exp\left(-\frac{\ell t^2}{2\sigma^2+2Rt/3}\right).
$$

The two Gram expectations are computed from actual centered samples. Identical distribution identifies them across indices. Measurability is derived from `IdentDistrib`; integrability, centered means, the dilation identities and the variance cap are proved inside the argument. The norm bound forces $R\ge0$. No common marginal measure, variance cap, moment generating function estimate, concentration inequality or integrability premise is supplied as additional data. The positive sample count is explicit. At a zero denominator the field inverse-zero convention gives the immediate bound by $2d$.

The variance is the scalar maximum of the two operator norms, as in Tropp. The matrix-valued maximum printed in LVV is read accordingly. The former finite-uniform restriction and this notational clarification are recorded in [the source comparison note](../paper-gaps/finite_uniform_matrix_bernstein.tex). The theorem establishes the iid complex square-matrix case quoted by LVV; it does not claim Tropp's sharper nonidentical-distribution variance norm or the arbitrary rectangular general-probability theorem.

## The proved analytic and probability argument

1. `TraceExpLogConcavity.lean` derives unnormalized Klein, the attained trace variational formula and full concavity of $A\mapsto\operatorname{Re}\operatorname{tr}\exp(H+\log A)$ on the positive-definite cone. The proof follows [Tropp, *From joint convexity of quantum relative entropy to a concavity theorem of Lieb*](https://tropp.caltech.edu/papers/Tro12-Joint-Convexity.pdf), Fact 3, Lemma 6 and Theorem 1, using QICLean's unnormalized relative-entropy joint convexity. No trace-one premise is introduced. An independent mathematical review confirmed the normalization, attainment, domain and empty-index case.
2. The factorial estimate $2\,3^k\le(k+2)!$ gives $e^x\le1+x+x^2/(2(1-a/3))$ for $|x|\le a<3$. Functional calculus gives the matrix exponential majorant. `TraceExpIntegralBounds.lean` derives its integrability and proves, for centered bounded Hermitian $Z$,

   $$
   \log\mathbb Ee^{\theta Z}
   \le\frac{\theta^2\|\mathbb EZ^2\|}{2(1-\theta R/3)}I,
   \qquad\theta\ge0,\quad\theta R<3.
   $$

   Integral Jensen is applied on the closed convex set above $e^{-R}I$; compactness of a finite-dimensional matrix ball derives all continuous-composition integrability. Operator monotonicity of the logarithm completes the variance bound.
3. `IndependentTraceExponential.lean` separates product coordinates with `measurePreserving_piFinSuccAbove` and Fubini's `integral_prod_symm`. Its product-space theorem permits different bounded Hermitian marginal laws. Mathlib's `iIndepFun.map_fun_eq_pi_map` identifies the actual joint distribution, and `integral_map` transfers the joint and marginal integrals. Thus the independent trace-exponential inequality is derived from genuine independence.
4. `HermitianMatrixBernstein.lean` applies scalar exponential Markov to the actual upper spectral event and optimizes the parameter. For a common individual variance cap $\sigma^2$, it gives $d\exp(-\tau^2/(2m\sigma^2+2R\tau/3))$. If $m\sigma^2>0$, choose $\theta=\tau/(m\sigma^2+R\tau/3)$; if $m\sigma^2=0<R\tau$, choose $\theta=3/(2R)$; in the zero-denominator case choose $\theta=0$. These cases include zero variance, threshold and sample count. For unrelated laws this uses $m\sigma^2$, rather than the sharper norm of the summed variances.
5. `HermitianDilation.lean` proves the norm and positive spectral endpoint of $\mathcal D(Y)=\left(\begin{smallmatrix}0&Y\\Y^*&0\end{smallmatrix}\right)$. `HermitianDilationIntegral.lean` makes it a real-linear isometry, so its Bochner mean commutes with dilation without an integrability premise. The squared diagonal blocks are $YY^*$ and $Y^*Y$. Existing continuous linear corner embeddings identify their integrals; positive-semidefinite block domination gives the exact required upper variance cap. The one-sided spectral event yields dimension $2d$ directly.
6. `MatrixBernstein.lean` centers the actual iid samples, derives equality of both Gram expectations by `IdentDistrib.comp` and `IdentDistrib.integral_eq`, applies the Hermitian theorem, and proves the sample-mean normalization. The final variance and dimension coefficient are those in the source.

Golden–Thompson is not assumed or proved by this argument. The unrestricted integrable version of the trace-exponential iteration and the sharper variance norm for unrelated distributions remain outside this development. The bounded analytic form suffices for the iid source theorem.

## Finite probability results and ownership

`TraceExpFiniteJensen.lean`, `BernsteinExponentialBound.lean`, `FiniteHermitianBernstein.lean` and `FiniteMatrixBernstein.lean` give independently checked finite uniform forms of the same concentration argument. The rectangular finite theorem has dimension factor $d_1+d_2$. The finite word-moment proof below gives another route with a weaker tail but the same logarithmic dependence on dimension.

The generic analytic, finite sampling and matrix probability modules belong in QICLean. The word-counting and singleton-cancellation modules should move to its `Algebra/`; the analytic and concentration modules should move to `Analysis/` and `Probability/` in dependency order. Their proofs use only Mathlib and existing QICLean results. QICLean must not import their TNLean copies. The source-specific filtered-operator and tensor-network bond estimates remain in TNLean.

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

The same method can avoid the dilation. Write $S=\sum_jY_j$ and expand $\operatorname{tr}((S^*S)^p)$ into ordered words of length $2p$, with adjointed and unadjointed factors alternating. A singleton sample label again gives zero expectation, since $\mathbb EY_j=\mathbb EY_j^*=0$. The remaining words obey the same $\ell^p p^{2p}$ count, and each contributes absolute expected trace at most $NR^{2p}$. The positive semidefinite spectral theorem gives $\|S\|^{2p}\le\operatorname{tr}((S^*S)^p)$. This proves the displayed moment and probability estimates with $N$ in place of $2N$. It requires neither a dilation norm identity nor a changed sampler. The finite uniform version of this argument is now formalized by `Matrix.average_norm_average_pow_le_of_centered`, including the alternating expansion, singleton cancellation, spectral comparison and their composition. The corresponding general-probability moment theorem remains outside this finite word argument. The sharp general-probability Bernstein theorem is proved separately by the preceding Lieb argument.

## The finite moment ingredients

- `Fintype.card_even_words_without_singleton` in `TNLean/Algebra/NoSingletonWords.lean` proves the bound $\ell^p p^{2p}$ for words of length $2p$ with no singleton letter, by the finite-fiber count and factorization described above. It is a counting theorem only.
- `Fintype.sum_pow_eq_sum_ordered_words` in QICLean's `Algebra/FiniteSumPowers.lean` gives the ordered expansion without any commutativity assumption.
- QICLean's `Probability/IndependentCovariance.lean` supplies product-measure integration identities. Mathlib supplies `MeasureTheory.integral_pi`, finite product probability measures, independence, and scalar Markov bounds.
- `Fintype.sum_ordered_word_eq_zero_of_singleton` in `TNLean/Algebra/SingletonWordCancellation.lean` proves singleton cancellation for finite independent uniform assignments into any noncommutative semiring, allowing position-dependent factors. It uses `Equiv.funSplitAt`, `Equiv.sum_comp` and `Fintype.sum_prod_type` to isolate the unique sample coordinate. The existing ordered product `MultilinearMap.mkPiAlgebraFin`, together with `MultilinearMap.map_update_sum` and `MultilinearMap.map_update_zero`, then gives cancellation. There is no new product decomposition and no conditional-expectation hypothesis.
- `Matrix.average_norm_average_pow_le_of_centered` proves the complete finite uniform moment estimate with coefficient $N$. The alternating expansion uses `MultilinearMap.map_sum` and `List.ofFn_fin_repeat`; the per-word bound uses `Matrix.PosSemidef.norm_trace_mul_le` at the identity, `List.nnnorm_prod_le` and `List.prod_le_pow_length`; the spectral comparison uses `CFC.norm_pow`, `Matrix.l2_opNorm_conjTranspose_mul_self` and `Matrix.PosSemidef.l2_opNorm_le_trace_re`. These steps are derived inside the proof. No Hermiticity assumption is imposed on the samples.
- `Matrix.finite_uniform_tail_bound_of_centered` in `TNLean/Algebra/FiniteMatrixSampling.lean` proves the finite Markov consequence: the fraction of assignments with sample-mean norm at least $\eta$ is at most $N(p^2R^2/(\ell\eta^2))^p$. The same module proves existence when this bound is less than one, and gives the sufficient conditions $N<4^p$ and $\ell\eta^2\ge4p^2R^2$. For an uncentered family of norm at most $R$, it derives the norm bound $2R$ after subtracting the uniform mean and proves approximation of that mean under $\ell\eta^2\ge16p^2R^2$. The general-probability moment extension is separate from these finite statements. The sharp Bernstein theorem is proved by the Lieb argument; the source sampler remains a further task.

The finite moment proof is independent of the Lieb trace-log-exponential argument used for the sharp Bernstein theorem.

## The ground-energy dependence remains essential

For the original samples, the crude norm bound is $R\le C^m+1$, where $C=(1-E_0/n)^{-1}$. The normalization estimate in the sampling note gives, at a suitable spectral power,

$$
C^{2m}\le n^2Q^{2E_0/\varepsilon}.
$$

The moment method therefore retains the energy-dependent polynomial exponent of the publication. It does not prove a uniform polynomial sample count for extensive ground energy. The commuting counterexample in the note rules out that inference. The unrestricted construction in issues #9822–#9823 requires a different approximate projection; the published supplement points to Huang's construction, arXiv:1406.6355, for this purpose.

The sharp matrix Bernstein part of the source theorem is now proved. The norm approximation of a sampled operator must still be combined with the simultaneous word-frequency bound in LVV Corollary 2.14 and with the correct ground-energy dependence. The concentration theorem does not itself construct that sampled operator. The source-specific power sampler remains a separate obligation under #9822–#9823. The polynomial successive-family construction is proved separately using the physical Gaussian filters of Huang; it does not use or validate the unrestricted power-sampling claim. Its exact precision and quantitative scope are recorded in `2026-10-28_lvv_successive_construction.md`.
