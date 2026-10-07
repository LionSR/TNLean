# Ground-state area laws and polynomial PEPS approximation

Assessment dated 7 October 2026. The complete ground-state area law
(Theorem 1.1 of *A two-dimensional area law from a global spectral gap*) and the
polynomial PEPS approximation theorem (Theorem 1.1 of *Polynomial PEPS
approximation of gapped square-grid ground states*) remain unfinished. The
results below establish distinct steps of their proofs. The combined QICLean
build, strict examples, all 27 public kernel reports, and complete blueprint
PDF, web and declaration checks have passed. Incorporation into the TNLean
dependency and the actual TNLean module builds remain pending. All manuscript
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
They allow a kernel outside the selected indices. They do not construct the
selection from a spectral gap or prove the sector norm comparisons of
Proposition 8.1.

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
their existence or uniformity. The physical entropy and numerical proof steps
passed standalone Lean checks; the actual TNLean module builds and axiom audit
are still pending.

The proved radius estimate isolates the numerical part of
[Proposition 10.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex#L261-L287).
With \(\gamma=(1-\varepsilon)/\alpha<\beta\), it turns
\(r\le Cn^\gamma\) into a threshold, depending only on \(C\) and \(\eta>0\), above
which \(\lfloor n^{1-\varepsilon}\rfloor+2r<\eta n^\beta\). Hence every
eventually admissible radius sequence satisfies
\(\lfloor n^{1-\varepsilon}\rfloor+2r(n)=o(n^\beta)\).
The exponent gap, rounded threshold and little-o proofs are complete and pass
standalone Lean checks; verification against the actual TNLean imports is pending. This estimate
does not construct an amplification radius or prove a remote-information bound.

The area law still requires the physical concentration and auxiliary-sector
estimates, amplified information bounds of Proposition 10.2, and the ordered
geometric decomposition of [Proposition 11.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L98-L142). The remote estimate must control
the whole exterior together with the same-family past in the original ground
state. Residual sizes and summed scale losses must be bounded using only the fixed local dimension, interaction range, interaction norm bound
and full-system spectral gap, before the domain, Hamiltonian and cut are chosen; zero-boundary cases must also be
included. The numerical entropy implication alone cannot supply those facts.

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
