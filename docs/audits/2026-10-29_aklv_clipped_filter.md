# The actual clipped AKLV Chebyshev filter

The two new mathematical modules construct a polynomial filter for the actual
two-exterior truncation of the original positive-contraction nearest-neighbour
chain. Its spatial decomposition, norm ceiling, and rank-one projector gap are
proved from the physical data. None of them is supplied to the headline theorem.

## Source and hypotheses

The source is [arXiv:1301.1162v1](https://arxiv.org/src/1301.1162v1),
`1dfrustrated34.tex`, SHA-256
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.
Lemma 4.1, lines 530–583, gives the normalized Chebyshev amplitude. Lemma 4.2
bounds the rank of an arbitrary polynomial at the central cut. Section 6.1,
lines 879–963, gives the original bounded-term chain, its three energy
normalizations and two exterior clippings. The subsequent application uses the
polynomial of this actual clipped Hamiltonian.

The headline theorem takes the original supported interactions
\(0\le h_i\le I\), a unit original ground vector \(\Omega\), its energy \(\mu\),
and an attained first excited gap \(g>0\). It assumes

\[
H-\mu I\ge g(I-|\Omega\rangle\langle\Omega|),
\qquad \mu+g\in\operatorname{spec}(H).
\]

The actual first excited energy and the complete gap inequality imply uniqueness.
Two distinct spectral values force local dimension at least two. This dimension
condition is derived rather than supplied. The energy shifts are constructed
before the truncation threshold, and the clipped ground vector is chosen before
the polynomial degree.

The minimum window width \(s\ge6\) and the original support and aggregate middle
energy-shift conventions remain explicit. They are documented in
`docs/paper-gaps/aklv13_two_block_robustness.tex`. No claim is made for smaller
windows or for arbitrary independently supplied exterior matrices.

## Actual operator and quantitative bounds

Let \(C_0,C_1,C_2\) be the original three consecutive regional sums at cuts
\(a+2\) and \(a+s-1\), and let \(e_0,e_1,e_2\) be the constructed reference
minima. Put \(F_j=\min(C_j,e_j+t)\) by continuous functional calculus. The actual
fully clipped operator satisfies

\[
B=\bigl(F_0-(e_0+e_1+e_2)I\bigr)
  +\sum_{j=0}^{s-3}h_{a+1+j}+F_2.
\]

The first term acts on \([0,a+2)\), the last on \([a+s-1,L)\). Thus the retained
window has width \(s-2\), with exactly the original central cut. The scalar shift
is placed in the left exterior only for this algebraic decomposition; the actual
operator remains the source's two-exterior truncation.

The constructed regional lower bounds give \(B\ge0\). The clipped exterior
ceilings and the \(s-2\) retained positive contractions give

\[
B\le(2t+s-2-e_1)I\le(2t+s)I,
\qquad \|B\|\le2t+s.
\]

For

\[
t\ge\frac{1024}{g}\left(\frac{E_0}{g}+1\right),
\]

the actual canonical spectral comparison supplies a phase-aligned unit ground
vector \(\phi\), energy \(E\ge0\), and a spectral gap at least \(9g/10\), with
\(\|\phi-\Omega\|^2\le e^{-t/16}/100\). Expansion in the complete canonical
basis proves the corresponding matrix projector-gap inequality. The uniqueness
consequence identifies its rank-one projection with that of the phase-aligned
vector.

For every \(\ell\ge0\), the constructed real polynomial \(p\) has exact degree
\(\ell\), satisfies \(p(E)=1\), and gives the same operator \(K=p(B)\) in both
estimates:

\[
\|K-|\phi\rangle\langle\phi|\|
 \le A:=2\exp\!\left(-2\ell\sqrt{\frac{9g}{10(2t+s)}}\right),
\]

\[
\operatorname{OSR}_{a+\lfloor s/2\rfloor}(K)
 \le\bigl(q(\ell+1)\bigr)^ {
 32(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}.
\]

The exact Chebyshev denominator is \(2t+s-E\); nonnegativity of \(E\) permits
the displayed uniform weakening. The rank theorem first gives coefficient 16
with division by \(s-2\). For \(s\ge6\), division with remainder proves
\(\lfloor\ell/(s-2)\rfloor\le2\lfloor\ell/s\rfloor+1\), giving coefficient 32
with the original width. The filter preserves \(\phi^\perp\), where its squared
shrinking coefficient is \(A^2\). Degree zero is included.

The rank estimate uses the corrected word count in the
[QICLean interpolation and word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).
The spectral comparison uses the corrected hard-truncation spectral windows in
[the companion note](https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf).

## Remaining entropy argument

This theorem constructs an actual physical filter. It does not choose the
entropy parameters, prove the initial product-overlap estimate, or construct
the sequence of normalized outputs for increasing truncation thresholds in
AKLV Lemma 6.3. Those steps must compare the changing clipped ground vectors
with the original ground vector. A filter fixing one clipped ground vector
cannot be treated as fixing the original vector.

## Verification status

The actual named modules pass separate strict checks with strict implicit
arguments, Mathlib's standard linters, warnings as errors, and the default
heartbeat limit:

| Module | SHA-256 | Time |
| --- | --- | --- |
| `AKLV/ClippedHamiltonian.lean` | `04a24c14ddcbf986efc4e7b16cdf67073e8ba131a0672236973b3d1ff135eb4c` | 5.77 s |
| `AKLV/ClippedFilter.lean` | `927517bd924fb2bb3b0f639040a1782cce2d6441f467da2ee6bb42ae39f1c3ee` | 7.81 s |

Imported manual foundation inspection of all three public declarations passes in
3.32 seconds. Their foundations are precisely `propext`, `Classical.choice`, and
`Quot.sound`. Inspection commands remain under `/tmp`; no permanent fixture is
added. The scoped tactic scan finds no repeated blocks at its default thresholds.
The shared ledger records the two occurrences of the scalar rank-one projection
identity as a candidate for a future generic companion-library lemma.

These are private checks against the fully built TNLean revision
`22519023a42896c04763ad0497970964481daaff` and its pinned QICLean revision
`637184a66a8c2215adec3bd28fc1a872ca382836`. A guard records the exact source and
object hashes of 277 imported TNLean and QICLean modules and checks them before
and after elaboration. The two new sources and objects are checked again during
imported foundation inspection. The existing dependency artifacts are read only;
all newly produced objects are private temporary files. No dependency pin,
shared cache, other worktree, or Mathlib source is changed.

No ordinary build is queued by this contribution. Ordinary named-module and
compiled-blueprint verification remain pending common integration. The new
chapter belongs after `ch35_aklv_physical_robustness.tex`; chapter registration
remains with integration.
