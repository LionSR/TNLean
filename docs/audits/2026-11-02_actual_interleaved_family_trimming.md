# Actual interleaved tensor-family applications and collective trims

Each successor applies the retained-factor family to the current interval
space, chooses an orthonormal basis of that actual image span, and takes its
actual collective trim. The same target, family, reference and positive
threshold are used throughout. This is the corrected recursive assignment
from ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
as documented in `docs/paper-gaps/alvv16_approximation_parameters.tex`.

## One step and every actual iterate

Let $K=\sum_iF_i\otimes R_i$ in interval/exterior coordinates. The target
$T$ and its orthogonal complement are invariant, the minimum norm gain on
$T$ is one, and the squared contraction on $T^\perp$ is at most $\Delta$.
The filter need not act as the identity or have a constant eigenvalue on $T$.
The actual family image of a $\delta$-viable space has normalized error

$$
 f(\delta)=\frac{\Delta\delta}{1-\delta+\Delta\delta}.
$$

For a reference mutually $\varepsilon$-close to $T$, with all-span MPS bond
at most $D$, the actual weighted trim has error at most

$$
 E(\delta)=(1+\theta)((1+\theta)f(\delta)
 +(1+1/\theta)\varepsilon+2\xi\sqrt{mD^2})
 +(1+1/\theta)\varepsilon,\qquad m=\max(r-p-1,0).
$$

The whole outside environment is retained, hence the squared reference bond.
No closeness between the whole image and its trim is assumed. Both the filtered
viability and the target-relative trimming estimate are derived for the literal
output.

Starting at the given actual space $S_0$, the recursive definition performs this
operation at every successor. Its actual dimension is at most $N^j\dim S_0$
after $j$ rounds, where $N$ is the number of retained factors. Each positive
iterate has at most that many recorded generators, with the same bound on
$\xi^2$ times their internal-cut Schmidt ranks. The bound is for those actual
spanning vectors, not for all vectors in their span.

A numerical envelope with $0\le\delta_j<1$ and $E(\delta_j)\le\delta_{j+1}$
proves viability of every actual iterate. With $0<a\le1$, $\theta=a/64$,
reference error at most $a^2/16384$ and threshold error $\xi\sqrt{mD^2}\le
a/256$, the simpler condition $f(\delta_j)+a/16\le\delta_{j+1}$ suffices.

## Scope and remaining physical construction

These are supporting lemmas with explicit operator, reference and numerical
hypotheses. They do not assert existence of the physical family, construction
of its reference at the required accuracy, successful sampling, or the eventual
small scalar envelope. Those conditions must be discharged in the physical
application; they are not substituted for a source-labelled algorithm theorem.

If the Haar sample and filter target a clipped low-energy space, comparison of
that target with the original ground space is a second, distinct budget.
Shrinking the reference error alone while retaining a constant original/clipped
comparison does not control the first trim of a nearly orthogonal sample. The
independent cutoff and polynomial degree must eventually be calibrated at the
same honest count and suppression bound. No adaptive joint probability, printed
round count, energy-estimation invariant or running time is asserted here.
