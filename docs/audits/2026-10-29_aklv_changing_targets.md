# A coherent AKLV changing-target sequence

## Mathematical statement

`exists_aklv_physical_changing_target_sequence` chooses a universal real
constant $A\ge21$ before the finite chain, local dimension, interaction,
ground energy, gap and ground vector. Put
$u=1+\log q+\log(1/g)$ and $s=\lceil Au^2/g\rceil$.
The current theorem assumes a fitting physical window $a+s+1\le L$ and
retains the actual first excited energy $\mu+g$ as physical data.
The interaction terms are the original supported nearest-neighbour positive
contractions, and the ground vector has the original rank-one projector-gap
bound. These data derive $q\ge2$, $0<g\le1$ and $s\ge21$.

The physical initialization chooses three actual regional minima $e_j$ and
a normalized ground energy $E_0$ with $0\le E_0\le6$ and
$E_0+\sum_j e_j=\mu$. It produces the actual clipped ground vector and
an actual normalized polynomial image of a product vector across the
central cut. The product vector, polynomial, nonzero filtered image and
unit scalar phase are retained in `IsAKLVSequenceInitialization`.
The proved initial logarithmic rank budget is retained as well.

For $i\ge0$ define $\beta_i=2^{-i}$ and
$t_i=T(g)+16i\log2$, with $T(g)=1024+16\log(1/g)$.
For $i\ge1$ use $\ell_i=\lceil5\sqrt{(2t_i+s)/g}\rceil$.
The actual squared Chebyshev shrinking factor is at most $1/256$,
and the clipped target's squared error is at most $\beta_i/100$.
The window and central cut are fixed throughout this sequence.

The actual physical refinement returns minima for the same three reference
Hamiltonians. `Matrix.groundEnergy_eq_of_normalized_eigenvectors` identifies
them with the initially selected minima. Thus every threshold clips the
same normalized physical Hamiltonian. The clipped eigenvectors, their
positive projector gaps and their phases relative to the original ground
vector are derived by the existing physical theorem, rather than supplied
as inputs to the recursion.

The private subtype `State i` carries unit norm, squared distance at most
$\beta_i/16$ from the original ground vector, and rank at most $R_i$.
For every actual state, the checked physical step constructs a successor
with its actual polynomial-image relation. A literal dependent `Nat.rec`
iterates the chosen successor. The choice specification proves every edge
relation from the actual preceding state. The resulting sequence is not
an independent choice of approximants at different indices.

In `IsAKLVSequenceStep`, each successor retains its actual target $\phi$,
energy $E$, polynomial $p$ of the chosen degree, scalar phase $c$, and
$K=p(B)$, with $K\phi=\phi$, $K\psi_i\ne0$ and
$\psi_{i+1}=cK\psi_i/\|K\psi_i\|$.
The exact rank budget is
$R_i=D_0\prod_{j=1}^iD_j$, where
$D_0=[q(s^2+1)]^{32(2s+1)}$ and
$D_j=[q(\ell_j+1)]^{32(\lfloor\ell_j/s\rfloor+\lfloor\sqrt{\ell_j}\rfloor+1)}$.
It uses the sharp window-dependent bounds, without a replacement by a
crude exponential in the degree.

## Source and remaining scope

The official local AKLV source is
`/tmp/tnlean-aklv-official-source-20261029/source/1dfrustrated34.tex`,
SHA-256 `65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.
The source is arXiv:1301.1162v1; the relevant changing-target construction
is Lemma `l:5`, lines 1003–1052. The printed proof summary's additive
expression for the rank at line 1053 must be read logarithmically, as in
item 2 of the lemma. The exact product is retained here.

This is a bounded construction in the explicit available-window and
actual-gap scope documented in
`docs/paper-gaps/aklv13_two_block_robustness.tex`. It does not establish the
remaining summed logarithmic rank estimate, entropy summation, or the
separate accuracy-dependent enlarged-window estimate at lines 1503–1517.
No independent area-law or MPS approximation theorem is used. A boundary
or short-chain alternative will use exact finite-dimensional cut rank,
rather than assuming a fitting window.

## Shared inequality

Three prior calculations in `Initialization` and `VariableWindowRefinement`
repeated the squared triangle inequality. They now use the general
seminormed-group inequality `norm_sub_sq_le_two_mul_add` in the separate
Mathlib-only QIC leaf `Analysis/NormSquaredTriangle.lean`. Its companion
contribution is frozen at
`aa5ede2ad00ab2106c5106549caa743d078b0722`, based on the checked QIC revision.
No generic norm theorem is introduced in TNLean, and the phase-distance
module is unchanged.

## Verification

Five actual TN production modules and the new QIC leaf passed separate
strict private checks. The provider was fully checked TN mathematical
snapshot `da3ab8dcc9f9149cbbdcc56cae817ff783825f24`, documentation-only
successor `f93bc77b3dddcc292125eea18b96af153225251b`, with exact QIC package
`4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`. Fresh source and ordinary-object
guards covered 299 imported TN/QIC modules, and all selected import roots
reported zero pending dependencies. The new QIC leaf was checked as its
actual separate module, followed by the two refactored consumers and the
new physical sequence modules.

The checks used strict CI flags, both automatic implicit options disabled,
Mathlib standard linters and warnings as errors. The new scalar, physical
step and final recursion modules passed in 4.39, 10.19 and 7.92 seconds;
the refactored initialization and refinement passed in 11.15 and 12.72
seconds. A separate imported foundation audit inspected all 20 public
declarations in these modules, including the shared QIC helper, and found
only `propext`, `Classical.choice`, and `Quot.sound` (or a subset).
Manual audit commands and objects are under the system temporary directory,
not repository fixtures.

All provider sources and objects remained read-only. New objects were
written to a private temporary namespace; no artifact was copied and no
Mathlib source was built. No ordinary build was queued. Ordinary build and
compiled blueprint verification remain integration gates. Generated
aggregators and chapter registration are excluded; the new chapter belongs
after `ch35_aklv_variable_window_refinement.tex`.

### Checked source hashes

| Production source | SHA-256 |
|---|---|
| `TNLean/MPS/AreaLaw/AKLV/SequenceParameters.lean` | `1dcb50990b6650b4fd7248bd9bd45d3daf75f456c4989758abbd62eeab8f3a8e` |
| `QICLean/Analysis/NormSquaredTriangle.lean` | `8f01a0829125e1412ad5f625a203716dc5c41f907709892e55bd9e84dbcd6ed7` |
| `TNLean/MPS/AreaLaw/AKLV/Initialization.lean` | `3a00f0b764707d09897a988668722064cf10e56071da6da15978273026eb13e6` |
| `TNLean/MPS/AreaLaw/AKLV/VariableWindowRefinement.lean` | `780f959ebaa4372f638619a9f72e0f2b6b6aa38c8f44effb0343e46a5bf42575` |
| `TNLean/MPS/AreaLaw/AKLV/ChangingTargetStep.lean` | `83587a34617dbcd0502cc75bf9031d2d53b2193e5c5842ea3c75b7b55f2e7edd` |
| `TNLean/MPS/AreaLaw/AKLV/ChangingTargets.lean` | `676b27ad4abaca9b89b16d6a023b140d429f7f6dfe5bd325bf5f9714c4336bde` |
