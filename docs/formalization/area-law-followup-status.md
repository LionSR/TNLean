# Ground-state area laws and polynomial PEPS approximation

Assessment dated 8 October 2026. The complete ground-state area law
(Theorem 1.1 of *A two-dimensional area law from a global spectral gap*) and the
polynomial PEPS approximation theorem (Theorem 1.1 of *Polynomial PEPS
approximation of gapped square-grid ground states*) remain unfinished. The
results below establish distinct steps of their proofs. The combined QICLean
build, strict examples, all 54 public kernel reports, and complete blueprint
PDF, web and declaration checks have passed. The three TNLean modules for
regional entropy, conditional boundary arithmetic and radius scales have also
passed their actual module builds and all seven strict kernel audits. The complete
TNLean root build and native declaration check for the entire blueprint have
passed, as have the complete PDF and web builds. The 2085-page PDF has no undefined
references or citations; its new entropy and collar statements were inspected
on printed pages 1696–1697. The commands and hashed evidence are recorded in
`docs/provenance/evidence/8759-entropy-dimension/full-verification/`.
The QICLean
dependency update remains separate. All manuscript
references use the September 24, 2026 versions at OpenAI source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

For a positive matrix \(\rho\), choose eigenvalue indices \(E\) of positive
total mass \(z\), and suppose the selected eigenvalues lie between
\(e^{-S(\rho)-w}\) and \(e^{-S(\rho)+w}\). The actual normalized restriction
\(\rho_E=z^{-1}P_E\rho P_E\) is positive, has trace one and rank \(|E|\), and
satisfies
\[
\bigl|\log\operatorname{rank}\rho_E-S(\rho)\bigr|\le w+|\log z|,
\qquad
\bigl|S(\rho_E)-S(\rho)\bigr|\le w+|\log z|.
\]
These QICLean results establish the matrix interpretation of the
[typical-Schmidt estimates preceding Proposition 8.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L39-L55).
They allow a kernel outside the selected indices. The canonical selection can now be constructed from the actual spectral
surprisal tail. For a density matrix, a tail at most \(\delta<1\) gives
\(1-\delta\le z\le1\), and hence positive mass. The corresponding
logarithmic rank and entropy errors are at most
\(w-\log(1-\delta)\). For a unit bipartite vector, the actual normalized
selected vector has distance at most \(\sqrt{2\delta}\). These two proofs
are published in [QICLean #608](https://github.com/LionSR/QICLean/pull/608),
at mathematical source revision
`79b9d503971a4ff2409fa557e174b46b13fdbbda`. The complete library build, strict
kernel and provenance checks, and full blueprint PDF, web and declaration
checks have passed. They assume the tail estimate.
[QICLean #611](https://github.com/LionSR/QICLean/pull/611) proves its uniform
numerical specialization: for fixed \(\theta\ge0\) and \(C>0\), there is
\(N\ge2\) such that, for every \(n\ge N\) and \(0<B\le Cn\),
\[
2e^{e/2}\exp\!\left(-\frac{n^{3/5}}{32\sqrt{(1+\theta)B}}\right)
\le n^{-100}.
\]
The mathematical source is frozen at
`317ecbd4478f243b844fb8d4a1d70fbbfd9c1f9a`; its complete library build,
57 combined kernel reports and full blueprint checks passed.
Deriving the boundary budget for the physical cut remains necessary before
these results yield \(z\ge1-n^{-100}\). The sector norm comparisons of
Proposition 8.1 also remain open.

For any normalized finite-product pure state and disjoint regions \(T,E\),
QICLean now supplies an isometry on the entire complementary Hilbert space and
two normalized purifications \(s,s'\), with
\[
\| (\mathrm{id}_{TE}\otimes V)\psi-s\otimes s'\|
\le\sqrt{2(1-e^{-I_\psi(T:E)/2})}\le\sqrt{I_\psi(T:E)}.
\]
This establishes [the splitting consequence, PEPS Lemma 6.4](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/05-frames.tex#L352-L391)
for varying local dimensions and empty regions. No polynomial bound in system size is asserted for the new
purifying dimensions. In particular, \(I_\psi(T:E)\le L^{-60}\) gives error
at most \(L^{-30}\). This is a complement isometry; a distributed
construction still has to use it with the required locality and dimension bounds.

Three further inequalities are proved for actual regional reduced matrices:
\(I_\psi(X:C\mid Z)\ge0\) for pairwise disjoint regions,
\(S_\psi(R\cup T)+S_\psi(R\cap T)\le S_\psi(R)+S_\psi(T)\), and
\(I_\psi(R:J)\le I_\psi(T:J)\) whenever \(R\subseteq T\) and
\(T\cap J=\varnothing\). These balanced entropy inequalities hold even for
unnormalized vectors; ordinary mutual-information positivity for such vectors
is not asserted. Monotonicity establishes
[the final discarding step of Proposition 10.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex#L560-L561),
not the amplified information estimate itself.

For a unit vector \(\Omega\) with local dimension \(q\ge1\), the new TNLean
entropy argument uses the existing regional density matrix to obtain \(S_\Omega(D)\le |D|\log q\). For an ordered two-family partition,
let \(P_i\) be the union of earlier pieces with the same label. If
\(I_\Omega(X_i:(\Lambda\setminus A)\cup P_i)\le\varepsilon_i\),
\(|D|\le c_D b\), and \(\sum_i\varepsilon_i\le c_Eb\), where
\(b=|\partial_\Lambda A|\), then
\[
S_\Omega(A)\le\left(c_D\log q+\frac{c_E}{2}\right)b.
\]
This is the [final numerical implication in the area-law proof](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L846-L857),
conditional on the partition and its stated estimates. It does not establish
their existence or uniformity. The actual TNLean modules and both strict kernel
audits have passed; their
[evidence records](../provenance/openai-math.d/8759-entropy-dimension.json) refer
to immutable production revision `548f23f7b274af443eb3644d8153f15148565c31`.

The proved radius estimate isolates the numerical part of
[Proposition 10.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex#L261-L287).
With \(\gamma=(1-\varepsilon)/\alpha<\beta\), it turns
\(r\le Cn^\gamma\) into a threshold, depending only on \(C\) and \(\eta>0\), above
which \(\lfloor n^{1-\varepsilon}\rfloor+2r<\eta n^\beta\). Hence every
eventually admissible radius sequence satisfies
\(\lfloor n^{1-\varepsilon}\rfloor+2r(n)=o(n^\beta)\).
The exponent gap, rounded threshold and little-o proofs have passed the actual
TNLean module build and all five strict kernel audits, recorded in the
[radius evidence](../provenance/openai-math.d/8757-radius-scales.json). This estimate
does not construct an amplification radius or prove a remote-information bound.

The accepted QICLean development now contains marginal moment and tail bounds
for actual ground vectors, including interactions with designated supports
(QICLean #590, #595 and #600). Their specialization to the physical scales and
regions of the comparator argument remains separate from the finite-dimensional
truncation argument. The area law still requires the auxiliary-sector
estimates, amplified information bounds of Proposition 10.2, and the ordered
geometric decomposition of [Proposition 11.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L98-L142). The remote estimate must control
the whole exterior together with the same-family past in the original ground
state. Residual sizes and summed scale losses must be bounded using only the fixed local dimension, interaction range, interaction norm bound
and full-system spectral gap, before the domain, Hamiltonian and cut are chosen; zero-boundary cases must also be
included. The numerical entropy implication alone cannot supply those facts.

The actual typical vector also has a regional formulation in
[QICLean #606](https://github.com/LionSR/QICLean/pull/606): its selection depends
only on the original marginal of the selected region, and every disjoint
physical region has reduced density bounded above by the original density
divided by \(z\). For unit input, its entropy is bounded by the original
regional entropy divided by \(z\). These statements have passed a complete
library build, all six additional kernel audits, provenance validation and
blueprint verification; their dependency update into TNLean remains separate.

[QICLean #609](https://github.com/LionSR/QICLean/pull/609) constructs the
selected Schmidt vector on the smaller coordinate space \(\mathbb C^E\).
Its actual spectral isometry satisfies \(J^\dagger J=I\) and
\(JJ^\dagger=P_E\). The vector
\(\chi=z^{-1/2}(J^\dagger\otimes I)\psi\) has norm one, embeds exactly into
the typical truncation, has diagonal first marginal with entries \(p_i/z\),
and preserves the complementary marginal. Positive selected mass suffices;
the original vector need not be unit. The complete library, all eight new
kernel audits, provenance and full blueprint checks have passed.

[QICLean #610](https://github.com/LionSR/QICLean/pull/610) proves the actual
one-copy Bell contraction. With \(d=|E|\), let
\(u=d^{-1/2}\sum_{i\in E}|i\rangle_C|i\rangle_R\) and
\(\beta=d^{-1/2}\sum_{i\in E}J|i\rangle_A|i\rangle_C\).
Positive selected mass gives \(\|\beta\|=1\), and the orthogonal projection
\(P=|\beta\rangle\langle\beta|\) satisfies
\[
(P\otimes I_{RB})(\psi_{AB}\otimes u_{CR})
=\frac{\sqrt z}{d}\,\beta_{AC}\otimes\chi_{RB},
\]
after the indicated regrouping of tensor factors.
The mathematical source is frozen at
`90e6071e32453006906390bd4e4f71ff4c5251a0`; the complete library build,
69 combined kernel reports and full blueprint checks passed.
[QICLean #614](https://github.com/LionSR/QICLean/pull/614) proves the literal
repeated-copy identity with coefficient \((\sqrt z/d)^k\), for every copy
number including zero, together with the repeated projection and permutation
identities. Its five new kernel reports, complete library and blueprint
checks passed. The entropy-compatible label selection and inverse metric
comparison remain separate steps.

[QICLean #618](https://github.com/LionSR/QICLean/pull/618) proves that an
actual density matrix on \(q^k\) dimensions has a Schur sector of mass at least
\((k+1)^{-q^2}\). For a unit vector with an arbitrary additional factor, this
is the squared norm of its projection onto the same sector. The two proofs,
complete library and blueprint checks passed. This generic selection does
not enforce the entropy window needed for the common label sequence.

[QICLean #621](https://github.com/LionSR/QICLean/pull/621) derives the exact
projected mass of the repeated uniform auxiliary pair, nonzero occurrence
precisely when the acting operator is nonzero in positive one-copy dimension,
and matching left and right central Schur labels. Three proofs and complete
library and blueprint checks passed. These results supply the initial
occurrence and matching assertions; they do not establish the required
entropy-compatible label probability in the selected Schmidt state.

[QICLean #615](https://github.com/LionSR/QICLean/pull/615) proves the actual
spectral cutoff mass bound from a first moment.
[QICLean #622](https://github.com/LionSR/QICLean/pull/622) applies it to the
physical replica Hamiltonian and excitation count. The one-copy gap yields
cutoff mass at least one minus the mean excess energy divided by the gap and
cutoff fraction, with arbitrary auxiliary factors. The literal cutoff is the
sum of the actual excitation-sector projectors, and their components have an
exact squared-norm partition. All fourteen new kernel reports and the
complete library and blueprint checks passed. The factorization of the
ground-state copies, dimension bound and inverse metric estimate are separate.

[QICLean #616](https://github.com/LionSR/QICLean/pull/616) proves the balanced
regional entropy cancellation in the auxiliary-pair argument directly for
actual pure-state marginals. For unit input, the resulting expression is
nonnegative by subadditivity and complementary entropy. Both proofs and
complete library and blueprint checks passed.

[QICLean #624](https://github.com/LionSR/QICLean/pull/624) proves independent-copy
surprisal concentration for actual tensor-power densities, including singular
one-copy states. A window of width \(k^{3/4}\) has tail mass at most
\(V_\rho/\sqrt{k}\), with the variance computed from the actual one-copy
spectrum. Four kernel reports and complete library and blueprint checks passed.
[QICLean #626](https://github.com/LionSR/QICLean/pull/626) proves actual replica
permutation covariance, including invariance of the literal tensor-power
density and preservation of fixed auxiliary sectors by the actual physical
cutoff. Five kernel reports and complete library and blueprint checks passed.
[QICLean #625](https://github.com/LionSR/QICLean/pull/625) extracts the actual
ground-state tensor from the complementary copies of each excitation
component by explicit contraction and proves equality of the remainder's norm.
Four kernel reports and complete library and blueprint checks passed.
[QICLean #627](https://github.com/LionSR/QICLean/pull/627) proves the numerical
threshold needed for that combination: for fixed \(V\in\mathbb R\) and
\(m\in\mathbb N\), eventually
\[
 V/\sqrt{k}+(k+1)^m\exp(-k^{3/4}/2)\le\tfrac12.
\]
The new proof, five combined kernel reports and complete library and blueprint
checks passed. The coefficient one half is inside the exponential.

[QICLean #629](https://github.com/LionSR/QICLean/pull/629), with source and
mathematical exposition frozen at `89941482`, proves one common sequence for an arbitrary density matrix,
including singular states. Its eventual mass is at least
\([2(k+1)^{q^2}]^{-1}\), and \(\log d_{\lambda_k}=kS(\rho)+o(k)\).
For a unit bipartite vector, it also proves the corresponding squared norm
of the actual central projection of its literal tensor powers, using its
actual reduced density. All four proofs pass strict Lean checking and exact
standard-kernel checks. The complete 9,713-job library build, source-bound
provenance and complete PDF/web/native declaration checks passed. The actual
pure-vector identities are separately verified in
[QICLean #628](https://github.com/LionSR/QICLean/pull/628), including zero
copies and singular marginals. These statements supply the high-label input,
while the
comparator and inverse metric arguments remain unfinished. None of these
draft results has yet changed TNLean's dependency pin.

[QICLean #630](https://github.com/LionSR/QICLean/pull/630), with proof
frozen at `d7fa8954`, gives the grouped-label operator inequalities: on the
full representation space,
\(F_{\mathrm{good}}+F_{\mathrm{bad}}\le F_{\mathrm{whole}}\le
F_{\mathrm{good}}+F_{\mathrm{bad}}+\log\binom{k}{r}I\).
Compatibility follows from the actual joint projections. Strict checking,
the complete 9,707-job library build, the exact standard-kernel audit,
provenance and complete PDF/web/native declaration checks passed. The occurring bad-copy dimension bound is proved separately below; transfer
to an actual excitation component remains a further step.

[QICLean #631](https://github.com/LionSR/QICLean/pull/631) has source and
exposition frozen at `f0c7d137`. It proves that one label sequence gives, for every positive copy
number, a nonzero vector of norm at most one, the correct physical mean
energy, matching labels on the two auxiliary systems and simultaneous
permutation symmetry. The same sequence retains the selected state's
eventual inverse-polynomial projected mass and entropy asymptotic. A
positive-mass sector of the actual marginal repairs only finitely many
initial terms. Strict Lean checking and an independent mathematical review
passed. The complete 9,716-job library build, two exact standard-kernel
reports, provenance and complete PDF/web/native declaration checks also
passed. The physical Schmidt-truncation instantiation and later comparator
estimates remain separate.

[QICLean #632](https://github.com/LionSR/QICLean/pull/632), with the two
new mathematical sources frozen at `fe621df0` and `0b6ff5a3`, proves that
an occurring bad-copy label has dimension at most \(|C|^r\), even with
the good copies retained as multiplicity. Consequently
\[
 F_{\mathrm{bad}}\le r\log|C|I,\qquad
 F_{\mathrm{whole}}\le F_{\mathrm{good}}+
 \left(r\log|C|+\log\binom{k}{r}\right)I.
\]
The statements include empty coordinate sets and zero copy groups, with the
total real logarithm. The complete 9,709-job library build, three exact
standard-kernel reports (one inherited and two new), provenance and complete
PDF/web/native checks passed. The actual whole-label compression and physical
component quadratic-form estimate remain separate.

[QICLean #633](https://github.com/LionSR/QICLean/pull/633), with source and
exposition frozen at `6c2e9382`, proves the literal covariance
\(U_\sigma R_B=R_{\sigma B}U_\sigma\). A permutation stabilizing \(B\)
therefore commutes with the component projection, including arbitrary
disjoint auxiliary operators, and projection preserves the corresponding
fixed-vector equation. The three identities require no normalization and
include zero copies. Strict checking, the complete 9,710-job library build,
three standard-kernel reports, provenance and complete PDF/web/native checks
passed. They do not assert commutation with the band metric.

[QICLean #635](https://github.com/LionSR/QICLean/pull/635), at checked head
`141ea11e`, transfers simultaneous permutation fixedness to the literal
auxiliary reduced density of an actual excitation component. Its two results
require no normalization or independent-copy assumption. The complete
9,711-job library build, strict checking, two standard-kernel reports,
provenance and complete PDF/web/native checks passed. Invariance of the
marginal does not imply independence of its copies.

[QICLean #636](https://github.com/LionSR/QICLean/pull/636), with mathematical
source `40d9ab9e` and documentary head `3b78880a`, proves the counting estimates
for actual excitation subsets. For \(0\le p\le1/2\) and \(r\le pk\),
\[
 \log\binom{k}{r}\le kh(p),\qquad
 \sum_{r\le pk}\binom{k}{r}\le(k+1)e^{kh(p)}.
\]
The corresponding cardinality estimate counts the actual subsets of a finite
set. Zero copies and both endpoints are included. The complete 9,761-job
library build, strict checking, four standard-kernel reports, exact provenance
and PDF/web/native checks passed; the native list contains 3,381 declarations.
These scalar bounds supply the counting step, while the inverse-compression
operator inequality remains separate.

[QICLean #637](https://github.com/LionSR/QICLean/pull/637), at checked head
`307cead4`, compresses the good-copy label observable to an actual whole-copy
label and transfers the resulting lower bound to an excitation component.
The only support premise concerns the original vector's whole auxiliary label;
component support and the good/bad coordinate split are derived. The complete
9,727-job library build, two fresh standard-kernel reports, exact provenance
and complete PDF/web/native checks passed. The numerical high-label threshold
and the later inverse metric comparison remain separate.

[QICLean #638](https://github.com/LionSR/QICLean/pull/638), at checked head
`77f935df`, proves that tracing the bad physical copies gives
\(|\Omega_G\rangle\langle\Omega_G|\otimes\rho_{\mathcal K}(w)\), where
\(w\) is the actual excitation component and \(\rho_{\mathcal K}(w)\)
is its own auxiliary marginal. The ground-state contraction gives the same
auxiliary matrix. Only the prescribed one-copy ground vector is unit; zero
components and zero copies are included. The complete 9,690-job library build,
two fresh standard-kernel reports, exact provenance and complete PDF/web/native
checks passed. The physical regional restriction is established below. Good-auxiliary
symmetry and the actual local component moment are established below.

[QICLean #639](https://github.com/LionSR/QICLean/pull/639), at checked head
`41c946d4`, instantiates the repeated Bell contraction with the actual
selected Schmidt vector and derives the common-label prevector sequence.
Positive selected mass suffices for the contraction, including zero copies
and selected indices of zero eigenvalue. The sequence additionally assumes
the original ground vector is unit and satisfies its ground-state equation.
The complete 9,719-job library build, two fresh standard-kernel reports,
exact provenance and complete PDF/web/native checks passed. The physical
Schmidt window and the inverse metric comparison remain separate.

[QICLean #640](https://github.com/LionSR/QICLean/pull/640), at checked head
`551f1cd4`, restricts the good physical copies to a region \(Q\).
For \(m=|B^c|\), its literal reduced matrix is
\[
 \rho_Q(\Omega)^{\otimes m}\otimes\rho_{\mathcal K}(w),
\]
after the specified chosen enumeration of the good copies. Only the
one-copy ground vector is unit; the excitation component \(w\) may vanish.
The complete 9,714-job library build, one fresh standard-kernel report,
exact provenance and complete PDF/web/native checks passed. The joint physical
and good-auxiliary marginal and the local component moment are established
below. None of these results asserts the complete inverse-compression inequality.

[QICLean #643](https://github.com/LionSR/QICLean/pull/643), at checked head
`72f13fda`, defines the literal good-auxiliary marginal by tracing all
physical copies, bad auxiliary copies and exterior copies. It derives
invariance under every good-copy permutation solely from the original
vector's simultaneous copy fixedness. The ground vector need not be unit;
zero components, zero copies and empty coordinate sets are included.
The complete 9,729-job library build, three fresh standard-kernel reports,
original provenance, the 434-page PDF and complete web/native checks passed.
The symmetry supplies the auxiliary premise for the merge-moment estimate;
it imposes no independence assumption on the auxiliary copies.

[QICLean #648](https://github.com/LionSR/QICLean/pull/648), at checked head
`5a835680`, proves the exact expansion of the exponential merge deficit in
its actual joint central projections, and the corresponding trace identity
for an arbitrary matrix. Only the commuting separate actions and their
simultaneous product are assumed; the exponent is any real number. The
complete 9,792-job library build, two fresh standard-kernel reports,
original provenance, the 446-page PDF and complete web/native checks passed.

[QICLean #649](https://github.com/LionSR/QICLean/pull/649), at checked head
`ef7442f0`, proves the merge-moment estimate on the literal paired copy space.
For a positive matrix invariant under both separate actions, the label-ratio
moment is bounded by \( (m+1)^{(|Q|\,|C|)^2}\operatorname{Tr}\rho \)
for every real exponent at most one. The trace-one form is also proved.
Total normalization includes zero mass, empty bases and zero copies.
The complete 9,792-job library build, seven fresh standard-kernel reports,
original provenance, the 447-page PDF and complete web/native checks passed.
The actual local component application is established below. Identifying
both regional marginals and merge deficits on a common space remains separate.

[QICLean #651](https://github.com/LionSR/QICLean/pull/651), at checked head
`771e955a`, defines the literal joint marginal of the good physical Q copies
and the good auxiliary C copies. For the same selected component, it is the
product of the one-copy physical marginal tensor power and the actual good
auxiliary marginal. Only the one-copy vector is unit; no independence of the
auxiliary copies is assumed. The complete 9,733-job library build, two fresh
standard-kernel reports, original provenance, the revised 437-page PDF and
complete web/native checks passed.

[QICLean #652](https://github.com/LionSR/QICLean/pull/652), at checked head
`b5ba8ae2`, applies the paired merge moment to that actual component. For
\(m=|B^c|\) and every real \(b\le1\),
\[
 \operatorname{Re}\operatorname{Tr}\!\left[
  \rho_{QC}(w)e^{b(F_Q+F_C-F_{QC})}\right]
 \le (m+1)^{(|Q|\,|C|)^2}\|w\|^2.
\]
The only vector premises are the unit one-copy vector and the original
simultaneous permutation symmetry. Positivity, both separate marginal
symmetries and the trace mass are derived from the same selected component.
Zero components, zero copies and empty good sets are included. The complete
9,821-job library build passed at `65b283fc`; the later book revision
`3587609f` adopts the checked #651 exposition without changing Lean sources
or dependency pins. The revised 469-page PDF, all 3,753 declaration checks,
the complete 50-page web reader, one fresh standard-kernel report, original
provenance and 138 portable artifact bindings passed. The QC moment alone
does not combine the two regional deficits or prove inverse compression.

[QICLean #654](https://github.com/LionSR/QICLean/pull/654), at checked head
`2c3b04b6`, proves an auxiliary arithmetic-mean estimate for a positive weight
and two commuting Hermitian matrices:
\[
 \operatorname{Re}\operatorname{Tr}(\rho e^{a(A+B)})
 \le \tfrac12\left(
  \operatorname{Re}\operatorname{Tr}(\rho e^{2aA})+
  \operatorname{Re}\operatorname{Tr}(\rho e^{2aB})\right).
\]
The weight need not be normalized or commute with either matrix. This is a
separate sufficient estimate for doubled polynomial moments; it is not
identified with the Cauchy--Schwarz inequality printed in the paper. The
complete 9,793-job library build, one fresh standard-kernel report, original
provenance, the 447-page PDF and complete web/native checks passed.

[QICLean #655](https://github.com/LionSR/QICLean/pull/655), at checked head
`038138a0`, defines the actual paired merge deficit and places the QC and VR
deficits on a common product copy space. Their identity lifts commute,
their joint exponential factors as an operator, and each individual complex
trace pairing is the pairing with its actual partial trace. The common
matrix may be correlated; the joint trace is not asserted to factor. The
six exact standard-kernel reports, original provenance, complete 9,793-job
library build, 448-page PDF and complete web/native checks passed.

[QICLean #656](https://github.com/LionSR/QICLean/pull/656), at checked head
`3652227d`, constructs the actual common good-copy density in the full
physical space Q tensor Y tensor V. It retains Q,C,V,R and traces every Y
coordinate. Both regional auxiliary partial traces and the original
component's squared trace mass are proved without normalization or symmetry
premises. Its source is `f5877818`, independent evidence `127e81f0`, and exact
two-line inclusion `fa392bef`. The full 9,734-job library build, four fresh
standard-kernel reports, original provenance, the 438-page PDF and complete
web/native checks passed. The complete manifest has 111 source/evidence
bindings and preserves every parent file except those inclusion lines.
The historical bipartite source is retained; its four statements are replaced
by the full QYV construction, with no parallel bipartite definitions.

[QICLean #659](https://github.com/LionSR/QICLean/pull/659), at checked head
`a820e67e`, bounds the joint exponential of both actual deficits in that
common density. With only the unit one-copy vector and original simultaneous
physical/C/R copy symmetry, for every real \(a\) with \(2a\le1\), the joint
trace is at most the average of the two polynomial moment bounds, multiplied
by the same component's squared norm. The literal exterior-region exchange
preserves Y and derives the second ground norm, symmetry and component mass.
The source is `7c8099cf`, independent evidence `1966e51e`, and exact two-line
inclusion `589ae558`. The full 9,825-job library build, strict source and fresh
standard-kernel report, original provenance, 472-page PDF and complete
web/native checks passed. Root independently inspected the proof, exact
report, 89-file manifest and complete PDF/mobile statements and proofs.
The arithmetic-mean estimate is an auxiliary polynomial step; physical
spectral restriction and the inverse-compression theorem remain separate.

[QICLean #658](https://github.com/LionSR/QICLean/pull/658), at checked head
`f675fee8`, proves positivity of the actual merge deficit for commuting
permutation actions and their pointwise product, then specializes it to the
literal paired-copy actions. It also proves that the closed nonnegative
spectral projection of a positive semidefinite matrix is the identity and
that an arbitrary Hermitian intertwiner into such a matrix's spectrum is
fixed by that projection. No injectivity or nonzero range is assumed.
The source is `a9415ed9`, independent evidence `7c3842d2`, and exact two-line
inclusion `7f93d770`. The full 9,823-job build, four original and four fresh
standard-kernel reports, original provenance, 471-page PDF and complete
web/native checks passed. The 175-file manifest preserves all 4,454 parent
files, with only the two inclusion lines changed. Four preliminary metadata
check failures and their successful corrections are retained explicitly.

[QICLean #661](https://github.com/LionSR/QICLean/pull/661), at checked head
`1c5769bed4719bb3e766800a4dad55164dacd6ee`, proves that the actual
physical good-copy density is fixed by the physical symmetric projection.
It retains every good physical coordinate, including Y, together with the
whole auxiliary system. Only the unit one-copy physical vector is assumed;
the auxiliary vector is arbitrary, and zero components and zero good-copy
counts are included. The mathematical source is `24f1008f`, followed by the
docstring-only citation revision `eba46627`, independent evidence `6bd427e9`,
and exact two-line inclusion `9b955ec2`. The full 9,735-job library build,
strict and fresh standard-kernel checks, original provenance, 438-page PDF
and complete web/native checks passed. The integration manifest has 106
bindings and the leaf manifest 116; the complete physical statement and
proof were inspected in the PDF and mobile reader. Reducing the auxiliary
systems to their good copies and expressing the density in five-factor
coordinates are subsequent steps.

[QICLean #662](https://github.com/LionSR/QICLean/pull/662), at checked head
`ca72e88dd71e5e6c8b6f2f8f2d2df35b1af94ae6`, proves the exact physical
exponential label moment of the actual excitation component. For every real
exponent, it is the iid regional-density moment multiplied by the same
component's squared norm. The literal left-hand pairing retains all
complementary physical and exterior coordinates. Only the one-copy ground
vector is unit; zero copies and zero components are included. The source is
`fc4db3db`, original evidence `a2b266d6`, and exact inclusion `1dba3aeb`.
The full 9,826-job build, sole strict and fresh standard-kernel report,
provenance, 473-page PDF and complete web/native checks passed. The 97-binding
manifest and complete PDF/mobile statement, proof and formula endpoint were
independently inspected. The signed centered analytic rate remains separate.

[QICLean #663](https://github.com/LionSR/QICLean/pull/663), at checked head
`1a61097225a153adeb32270edb0778363e2ddfb1`, establishes the actual compatible
physical projection on the five independent factors Q,Y,V,C,R. With
\(G=F_Q+F_V-F_Y\), physical symmetric projection P and
\(J=\mathbf1_{[0,\infty)}(G)\), it proves
\(GP=P(F_Q+F_V-F_{QV})\) and \(JP=P\). Every real functional calculus of G
commutes with the actual QC, VR, C and R label observables and both merge
deficits. Neither global positivity of G nor preservation of P by a merge
is assumed. Source `117c20bc`, original evidence `925b12b6` and exact
inclusion `a31ba42a` remain unchanged. The full 9,824-job build, five fresh
standard-kernel reports, provenance, 472-page PDF, complete web/native checks
and 68-artifact manifest passed. All 4,553 parent files are preserved, with
only the stated inclusion and ledger additions. Root read the entire source
and inspected both complete PDF pages and the mobile section. Application
to the literal five-factor good-copy density remains subsequent work.

The source physical space has independent regions Q, Y and V. A common
component density for QC and VR must trace every Y copy, in addition to the
bad physical and auxiliary copies. The local QC theorem above accommodates
this by taking the physical complement to be YV. The common-density
identities are now proved as above. The actual two-deficit moment is the separate auxiliary estimate above.
The compatible physical projection is now established above; its application
to the literal component density remains a subsequent contribution. In particular,
\(F_Q+F_V-F_Y\) cannot be identified globally with the QV merge deficit.

The accepted [QICLean #580](https://github.com/LionSR/QICLean/pull/580)
contains the compatible merge and grouped-copy dimension inequalities of
Lemma 6.1. Their application to the actual good-copy component and the
logarithmic dimension comparison remains separate. The accepted
[QICLean #612](https://github.com/LionSR/QICLean/pull/612) proves the conditional
movement estimate of area-law Lemma 5.1; it was merged at `29c9584d`.
The accepted [QICLean #617](https://github.com/LionSR/QICLean/pull/617)
proves the faithful-state marginal-phase comparison of Lemma 5.2; it was
merged at `8b9b4bcd`. The singular-state extension remains a separate
contribution.
The accepted
[QICLean #613](https://github.com/LionSR/QICLean/pull/613) supplies a maximizing
nested feasible filter family, commutation with its marginals, and the
floor-clipped spectral form in the area-law initial-buffer argument.
The floor-to-zero limit and physical energy assembly remain to be established.
These nested-filter results do not by themselves complete the separate PEPS
patch-minimum proposition.

[QICLean #607](https://github.com/LionSR/QICLean/pull/607) proves that a positive
definite matrix and any nonzero real power have the same commutant. In
particular, commutation with \((x+bI)^{-a/2}\), for \(x\ge0\) and
\(a,b>0\), implies commutation with \(x\). This is the functional-calculus
step after native patch stationarity. It does not establish the preceding
commutation premise. Its three proofs, complete library build, kernel audits,
provenance validation and blueprint checks have passed.

For PEPS approximation, the separate draft proving attainment of the
regularized patch minimum does not yet establish
[Proposition 4.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L24-L562).
Stationarity, constrained spectral optimization, the energy estimate for
noncommuting filters, growth of the regularized minimum and the ordered
first-head expansion remain to be assembled. Likewise,
[distributed density compression, Theorem 5.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L132),
still needs a concrete composition of the circuit, branch and local tensor
constructions with uniform polynomial bounds. Those steps must connect the
proved splitting, truncation and compression estimates to a nonzero PEPS whose
normalized vector has phase-minimized error at most \(L^{-1}\).


The chronological source-gate expansion for PEPS compression is separately
published in [TNLean #8887](https://github.com/LionSR/TNLean/pull/8887),
with mathematical source frozen at
`02ff0a871f6e1847f847f00609ba89c3942ab5c4` and evidence head
`cc0a19f9b2f35b5bd843bd82e9b0e2cecbdcdccb`. It retains exterior aggregate
contractions, original occurrences and source positions, and the full complex
coefficients in the operator and density identities. Strict checking,
55 standard-kernel reports, blueprint checks and a canonical provenance
replay covering 323 declarations passed. These checks are distinguished from
a complete Lake build. The actual corrected-density estimate, source sampling,
physical protocol and local tensor-network construction remain separate.

[TNLean #8893](https://github.com/LionSR/TNLean/pull/8893) adds the fixed-slot,
original-vector and direct selective-contraction statements to that source
expansion. Its mathematical source is `6246647741ce41a55a3897329336055330dd7e6f`
and publication head is `4097a00b1`. The 19 exported declarations have separate
source and kernel evidence. A complete build of the preceding #8887
integration has also passed. Adoption of the full QICLean source chain into
the current TNLean development is being checked separately; the actual
corrected-density estimate and physical construction remain open.

[QICLean #634](https://github.com/LionSR/QICLean/pull/634) provides the checked
integration of the PEPS source estimates and the accepted Schur-label results
of #593. Its final mathematical source is `035e5cc6` and evidence head is
`4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0`. All 25 incoming PEPS proof modules
retain their source text. The complete 9,791-job library build passed, together
with eight fresh standard-kernel reports, preservation of 1,455 frozen files,
all 240 source-chapter declaration targets, the 446-page PDF and complete web
checks. The earlier 21 strict source regressions and 325 provenance mappings
retain their historical records; they are not described as fresh checks of
the entire contribution. The PEPS coordinator is adopting this exact checked
QICLean revision in the separate TNLean integration. The distributed
compression and polynomial PEPS theorems remain unfinished.
[TNLean #8896](https://github.com/LionSR/TNLean/pull/8896), at head `cbdcf495f`,
adopts that exact QICLean revision at source `17a29d236`. Its coordinator
reports strict checks of the 66 affected TNLean modules and the two refreshed
aggregators, 342 imported standard-kernel reports, all 20,810 blueprint names
and exact preservation of the earlier proof sources. These checks are distinct
from the earlier complete library builds and from the unfinished physical
compression argument.

[TNLean #8900](https://github.com/LionSR/TNLean/pull/8900), at head
`329d192af`, supplies deterministic identities for the corrections at the
original source positions, above the preceding integration. Its mathematical
source is `f932b80f`; the exact QICLean dependency remains `4be0ef42`.
The coordinator reports 67 new and 24 refreshed standard-kernel reports,
strict checking of 35 affected modules, 585 provenance entries and all
20,877 compiled blueprint declaration names. The Gaussian estimates, actual
frame identifications and complete corrected-density bound remain separate.

[TNLean #8903](https://github.com/LionSR/TNLean/pull/8903), at head
`70e23f40`, continues the Gaussian and Schmidt estimates at source
`258925377`. Its dependency is the separately checked QICLean helper
contribution [#646](https://github.com/LionSR/QICLean/pull/646), at
`b2521d2a`. The coordinator reports 17 strict checks, 30 standard-kernel
reports, all 614 provenance entries, all 20,906 blueprint declaration names
and focused rendering checks. These are narrow checks, distinct from a
complete library build. The actual norm integrability and some-sample
bound are further checked local consequences reported by that coordinator;
the complete physical compression and polynomial PEPS theorem remain open.

The later dependency updates use
[QICLean #650](https://github.com/LionSR/QICLean/pull/650), at head
`caac4b54`, source `92b6eea7`. It supplies ten generic identities and bounds
for physical partial traces in orthonormal coordinates, including block
and integrability consequences. The coordinator reports six strict checks,
ten standard-kernel reports, focused PDF/web inspection and preservation
of 958 source files. These are narrow checks, not a complete library build.
The dependency-update TNLean heads were `429d55a3` for #8896, `1d718899` for #8900 and
`f96e06dc` for #8903. They synchronize the dependency with #650; the
mathematical source `25892537` and the Gaussian/Schmidt evidence at
`70e23f40` remain unchanged. The earlier checks described above retain
their original revisions and are not claimed as fresh checks of these
later dependency updates.

The later evidence-only packaging correction advances #8896 to `fa9aa3ee`,
#8900 to `1704ccd4`, and #8903 to `ba981227`. It retains the exact bytes of
an overlength archived kernel-audit script as a compressed artifact with its
uncompressed hash. The proof sources and dependency pins remain unchanged;
the coordinator reports the historical validators and module policy passed.

[TNLean #8908](https://github.com/LionSR/TNLean/pull/8908), at head
`456204230ab8548568dbbccdac39b894d1539ff5`, adds physical Gaussian source
estimates at mathematical source
`5547d32efa79b3b18150eb07be2bfcda4a68f79a`. The coordinator reports 27 strict
module checks, 86 selected standard-kernel reports, all 20,983 compiled
blueprint names, 691 canonical provenance entries and focused rendering of
the 45-page mathematical supplement. These are narrow checks; a complete
library build is not claimed for this contribution. The separately used
QICLean #650 dependency has passed its full remote CI. The coordinator subsequently reports that the actual Schmidt input/output
substitutions and physical frame identities are proved and the resulting
actual correction-term integral estimate has passed strict checking. The
common-sample error estimate and sampled operator network remain under
construction; these later proofs are not assigned the earlier contribution's
verification records.

[TNLean #8912](https://github.com/LionSR/TNLean/pull/8912), at head
`2f5a2d3f4163dd25caf8c0845bc81b6c5826493f`, constructs the original circuit's
source-only replacement with physical density error at most half the
prescribed accuracy, retaining participating parties, whole-lifetime counts,
coefficient bounds and unequal physical dimensions. It also constructs the
actual Schmidt input and output data with their original physical/discarded
coordinates. Mathematical source: `33695425897e6f9895884741c0677aa38750361b`.
The coordinator reports 48 strict compilations, 328 standard-kernel reports
(300 new and 28 inherited declarations), 14,697 imported artifact hashes,
a direct library-root check of all 21,283 blueprint names, and the visually
reviewed 55-page focused PDF and seven-page web reader. These are precise
narrow checks; no full Lake build or declaration-checker invocation is
claimed. The final sampled tensor-network representation remains unfinished.

[TNLean #8914](https://github.com/LionSR/TNLean/pull/8914), at checked head
`0fa31ddad11ab7a8f06a3a34f1381c3ff974e8bf`, constructs one common global
Gaussian sample with physical operator error at most one quarter of the
prescribed accuracy. The corrected-term estimates use the original
coefficients, lifetime participation and physical dimensions; source
Schmidt data and regional orthonormal bases are chosen within the proof.
For every real accuracy exponent, the same sample count has an explicit
polynomial bound. This is the sampling step of Theorem 5.2; the actual
tensor-network contraction and final assembly remain unfinished.
The coordinator records 13 strict direct checks, 18 standard-kernel reports,
14,707 imported artifact hashes, direct library-root declaration checking of
21,301 names, 1,009 provenance entries, and a visually inspected 59-page
focused PDF and seven-page web reader. These are direct and focused checks;
no local full Lake build is claimed.

The accepted [QICLean #589](https://github.com/LionSR/QICLean/pull/589), merged
at `48425ea8ed2390a94c71870ac19142490e5df5b7`, supplies the Schur–Weyl
commutant and highest-weight development for reuse in subsequent proofs.
The accepted Schur-label contribution #593 is included in the separately
checked QICLean integration described above. Neither contribution changes the
dependency pin of the earlier verified TNLean entropy results.
