# Issue #832 blocker note — primitive trace-power constancy does not force rank one

## Summary

The target implication from issue #832,

```lean
Matrix.IsPrimitive T → Matrix.TracePowersConstant T → Matrix.HasRankOneFactorization T
```

is **false in general** for nonnegative primitive real matrices.

A concrete counterexample is

\[
T =
\begin{pmatrix}
0 & 0 & 1/2 \\
1/2 & 1/2 & 0 \\
1/2 & 1/2 & 1/2
\end{pmatrix}.
\]

## Why this is a counterexample

1. `T` is primitive, because
   \[
   T^2 =
   \begin{pmatrix}
   1/4 & 1/4 & 1/4 \\
   1/4 & 1/4 & 1/4 \\
   1/2 & 1/2 & 1/2
   \end{pmatrix}
   \]
   has all entries strictly positive.
2. `T` has constant trace powers:
   - `tr(T) = 1`,
   - `tr(T^2) = 1`, and
   - `T^3 = T^2`, hence `T^n = T^2` for every `n ≥ 2`, so `tr(T^n) = 1` for all positive `n`.
3. `T` is not rank one. For example, the first row `(0, 0, 1/2)` and the second row
   `(1/2, 1/2, 0)` are not proportional.

Equivalently, the spectrum is `{1, 0, 0}`, so the trace-power identities only force the
non-Perron eigenvalues to vanish; they do **not** force the matrix itself to be the Perron
rank-one projector.

## Consequence for the MPDO development

The current placeholder

```lean
Matrix.PrimitiveTracePowersConstantImpliesRankOne
```

cannot be discharged as a standalone Perron--Frobenius theorem with only the present
hypotheses.

So the real remaining gap after PR #807 is slightly different:

- either extract a **stronger matrix hypothesis** from the full ZCL relation than mere trace-power
  constancy,
- or formalize the local `η_{k,h}` / `r_k,l_h` layer first (issue #833) and prove rank one from
  that richer structure.

In particular, the paper sentence “primitive + constant trace powers implies `T_{k,h} = a_k b_h`”
appears to use additional structure that is not captured by the abstract matrix statement alone.
