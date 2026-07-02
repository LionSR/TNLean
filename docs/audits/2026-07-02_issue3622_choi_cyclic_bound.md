# Issue #3622: Choi-Type Cyclic Bound

Issue #3622 asks for the positivity of the Choi-type map in Wolf Chapter 3,
Example 3.1, equation (3.20), for \(1 \le n \le d-2\).

The current reduction is:

\[
T_C(|v\rangle\langle v|)
= \operatorname{diag}(a_i)-|v\rangle\langle v|,
\qquad
a_i=(d-n)|v_i|^2+\sum_{k=1}^n |v_{i-k}|^2.
\]

The Schur-complement criterion already formalized reduces rank-one positivity
to the scalar estimate

\[
\sum_i \frac{|v_i|^2}{a_i}\le 1.
\]

The equality of the total weights is not sufficient for this estimate.  In
general, from \(\sum_i x_i=\sum_i y_i\) one cannot conclude
\(\sum_i x_i/y_i\le 1\).  The Choi-type problem needs the cyclic placement of
the shifted weights in \(a_i\).  Thus the remaining theorem should isolate a
cyclic reciprocal inequality for nonnegative \(x_i\):

\[
\sum_i
\frac{x_i}{(d-n)x_i+\sum_{k=1}^n x_{i-k}}\le 1.
\]

Once this inequality is proved for \(1 \le n \le d-2\), it can be applied with
\(x_i=|v_i|^2\) to discharge the conditional rank-one positivity lemma and then
the positive-map statement for \(T_C\).
