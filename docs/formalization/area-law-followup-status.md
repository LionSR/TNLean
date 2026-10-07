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

The accepted [QICLean #589](https://github.com/LionSR/QICLean/pull/589), merged
at `48425ea8ed2390a94c71870ac19142490e5df5b7`, supplies the Schur–Weyl
commutant and highest-weight development for reuse in subsequent proofs.
This later accepted contribution has not changed the dependency pin of the
verified TNLean results above.
