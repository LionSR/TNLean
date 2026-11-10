# AKLV robustness and the actual filter at a logarithmic threshold

The physical two-exterior truncation now has the stronger sufficient threshold

\[
T(g)=1024+16\log(1/g).
\]

The actual ground vector, spectral gap, norm ceiling and polynomial filter are
constructed from the original positive-contraction nearest-neighbour chain.
The existing polynomial-threshold theorem signatures are preserved as corollaries.
This contribution does not yet choose the favorable entropy parameters or
construct the varying-truncation approximation sequence.

## Source and mathematical scope

The official source is [arXiv:1301.1162v1](https://arxiv.org/src/1301.1162v1),
`1dfrustrated34.tex`, SHA-256
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.
The bounded-term setting, normalization and actual exterior clippings are in
lines 879–963. Lemmas 4.1–4.2 give the Chebyshev suppression and polynomial
operator Schmidt rank. The subsequent entropy application must still be proved
using those actual filters.

The physical signatures retain original supported interactions \(0\le h_i\le I\),
a unit ground vector \(\Omega\) of energy \(\mu\), the positive rank-one projector
gap \(g\), and actual spectral attainment of \(\mu+g\). The two distinct energies
force \(q\ge2\). The endpoint trial vector then derives \(g\le1\); it is not
assumed separately. The reference minima and normalized energy \(E_0\in[0,6]\)
are chosen before the truncation parameter.

The restriction \(s\ge6\), corrected left exterior support, and aggregate middle
energy shift remain explicit in the existing module markers and
`docs/paper-gaps/aklv13_two_block_robustness.tex`. No arbitrary-exterior extension
or smaller-window conclusion is asserted.

## Why the logarithmic threshold suffices

The existing actual spectral comparison requires

\[
t\ge\max\{g+11,\;g+8\log(C_1/(\tau g))\},
\qquad C_1=10^6\cdot64e^{3/4}.
\]

Set \(\tau=e^{-t/16}\). The second condition becomes

\[
t\ge2g+16\log(C_1/g).
\]

Since \(0<g\le1\) and \(\log C_1\le61\), both conditions follow from
\(t\ge1024+16\log(1/g)\). The same complete canonical spectral comparison gives
gap at least \(9g/10\) for the actual two-exterior truncation and an actual
phase-aligned unit ground vector with

\[
\|\phi-\Omega\|^2\le e^{-t/16}/100.
\]

The norm and spatial decomposition of this same matrix give positivity and
\(\|B\|\le2t+s\). Its constructed projector gap supplies the actual Chebyshev
polynomial for every degree \(\ell\), with amplitude at most

\[
2\exp\left(-2\ell\sqrt{\frac{9g}{10(2t+s)}}\right)
\]

and same-cut rank at most

\[
\bigl(q(\ell+1)\bigr)^ {
32(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}.
\]

No spectral ceiling, rank, spatial decomposition or truncated ground vector is
supplied. The reference minima precede \(t\), and the actual clipped ground
vector precedes \(\ell\). The coarser signatures follow from
\(T(g)\le1024/g\) and \(E_0\ge0\). Each spectral, phase and polynomial
construction is used once; the old statements do not duplicate it.

The rank count and spectral comparison continue to use the documented
[corrected interpolation count](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf)
and [corrected spectral windows](https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf).

## The companion eigenvector lemma

The former basis-expansion proofs of ground-energy spectral membership have
been replaced by the generic companion lemma
`Matrix.mem_spectrum_real_of_mulVec_eq_smul`, in the existing
`Analysis/PositiveGapUniqueness.lean` module. A real eigenvalue with a nonzero
Euclidean eigenvector belongs to the real spectrum. The lemma has no
Hermiticity, normalization or gap hypothesis. Its proof applies Mathlib's
nonzero-eigenvector and spectrum results through the matrix-to-linear-map
identification. No second ground-state predicate or new helper module is added.

## Verification

The actual named modules pass strict private checking with the package implicit
argument settings, Mathlib standard linters, warnings as errors and default
heartbeat limit:

| Module | SHA-256 | Time |
| --- | --- | --- |
| QIC `Analysis/PositiveGapUniqueness.lean` | `85e1384c01f0ba05db2c6f0995145969d553cdfc75255fbb238a169ed06ac8a7` | 3.35 s |
| TN `AKLV/PhysicalRobustness.lean` | `069fbf7d4ca3ba44ce77fa3a0b6494d0a90f3d6816ed7aabc8ed9bcfa2a30325` | 4.57 s |
| TN `AKLV/ClippedFilter.lean` | `0c0d618e72bd4916ed36315df734a0984e8c80d73fbdbcfe376af7f5f2382e2e` | 7.74 s |

Imported manual foundation inspection passes for seven public declarations in
3.22 seconds, including both retained polynomial-threshold theorems. All seven
depend only on `propext`, `Classical.choice`, and `Quot.sound`. Commands remain
under `/tmp`; there is no permanent inspection fixture. The scoped tactic scan
finds no repeated blocks at its default thresholds.

These are checks against the read-only, fully built TNLean mathematical snapshot
`5cec1958d1a56d1f20cfdbd1161ef946a410f41c`, with QICLean
`cc9e79084d26336c95e843c13928a3963a9debb2`, together with the explicitly listed
modified companion module checked first in the private namespace. They are not
ordinary verification at an unchanged companion pin. The guards record 277
imported TNLean/QICLean source and object hashes and recheck them before and
after elaboration. The modified companion and the two modified TNLean source
and object hashes are also checked during the imported foundation audit.

Both contribution worktrees contain source only, with no `.lake` directory.
Existing artifacts are read only and all new objects are temporary. No provider,
dependency pin, shared cache or Mathlib source is changed. No ordinary build is
queued by this contribution. Ordinary module and compiled-blueprint checks
remain with common integration. No aggregator or chapter registration changes
are needed.
