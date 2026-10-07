# Regional dimension bounds and the final entropy estimate

Let \(\Lambda\subset\mathbb Z^2\) be finite, let \(q\in\mathbb N\), and let
\(\Omega\in\bigotimes_{v\in\Lambda}\mathbb C^q\) be a unit vector. The entropy
of any region \(A\subseteq\Lambda\) satisfies
\[
S_\Omega(A)\le |A|\log q.
\]
The regional density matrix is positive semidefinite with trace one. Its entropy
is at most the logarithm of its rank, and its rank is at most the dimension
\(q^{|A|}\) of the regional Hilbert space. The statement includes the empty
region and the one-dimensional local space \(q=1\), without conditions on a
Hamiltonian or a spectral gap.

For an ordered two-family decomposition
\(A=D\mathbin{\dot\cup}\bigcup_iX_i\), write
\(P_i=\bigcup_{j<i,\,f_j=f_i}X_j\). Suppose
\(I_\Omega(X_i:(\Lambda\setminus A)\cup P_i)\le\varepsilon_i\),
\(|D|\le c_D|\partial_\Lambda A|\), and
\(\sum_i\varepsilon_i\le c_E|\partial_\Lambda A|\). Two-family entropy
cancellation and the dimension bound then give
\[
S_\Omega(A)
\le\left(c_D\log q+\frac{c_E}{2}\right)|\partial_\Lambda A|.
\]

These are the dimension estimate and the final numerical implication in the
[proof of Theorem 1.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L846-L857)
of OpenAI's *A two-dimensional area law from a global spectral gap*
(September 24, 2026). Both proofs are independently written. No upstream Lean
proof text is copied or adapted.

The numerical implication does not construct the decomposition or establish
its estimates. It also does not show that \(c_D\) and \(c_E\) can be chosen
uniformly in the domain, Hamiltonian, and cut. Those are the remaining
geometric and analytic steps of the ground-state area law; the source theorem
must remain unmarked until they are proved.

Implementation: `TNLean/PEPS/AreaLaw/EntropyDimension.lean` and
`TNLean/PEPS/AreaLaw/BoundaryEntropyAssembly.lean`. The existing finite-domain
regional entropy is identified with the QICLean finite-product entropy; no
additional state, density matrix, partition, or entropy definition is introduced.

Assisted by OpenAI Codex. Human mathematical review remains separate from
successful Lean elaboration and the axiom audit.
