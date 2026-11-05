# Related Lean libraries

Six public Lean 4 libraries by Erickson Tjoa and collaborators cover
neighbouring mathematics on the same Lean and Mathlib line as TNLean, under
the Apache licence. They were described to this project in issue #9485. This
page records what they contain, where they meet TNLean, and the division of
labour agreed there, so that work here reuses their results instead of
reproving them.

## The libraries

| Library | Content | Depends on |
|---|---|---|
| [LocalAlgebrasLean](https://github.com/etjoa002/LocalAlgebrasLean) | Nets of local algebras; the qudit net; the quasi-local algebra of a lattice of `d`-level systems as the norm closure of the local matrix algebras, with its universal property | Mathlib |
| [LocalityLean](https://github.com/etjoa002/LocalityLean) | Lieb–Robinson bounds for bounded local generators on a net, with the published spin-system bounds as corollaries; open systems; local approximation and the approximate cellular automaton; harmonic bosons | LocalAlgebrasLean, LinearAQFT, BosonicLean |
| [LinearAQFT](https://github.com/etjoa002/LinearAQFT) | Algebraic quantum field theory of linear fields: the CCR net and the Dimock axioms, on a lattice and on Minkowski space | LocalAlgebrasLean, BosonicLean |
| [BosonicLean](https://github.com/etjoa002/BosonicLean) | Gaussian covariance matrices, Gaussian matrix product states, the CCR algebra, its states and Gaussian channels, the formal Fock space | Mathlib |
| [FermionicLean](https://github.com/etjoa002/FermionicLean) | Fermionic Gaussian states of finitely many modes and Gaussian fermionic matrix product states: contraction, periodic chains in momentum space, Wick's theorem, the Kitaev chain as unique gapped ground state, entanglement rank across a cut | Mathlib |
| [QCALean](https://github.com/etjoa002/QCALean) | Quantum cellular automata, first Gaussian automata on a lattice of oscillators: symbols, the symplectic criterion, convergence to stationary covariances, lattice channels | LocalAlgebrasLean, LinearAQFT, BosonicLean |

Each library states its main theorems in its `verify/CORE.md`, and each is
written together with lecture notes that set the order and choice of results.

## Where they meet TNLean

- **Matrix product unitaries and cellular automata.** The correspondence
  between matrix product unitaries and one-dimensional cellular automata
  (the GNVW index, the Margolus decomposition, support algebras, recovery of
  the standard form from an automaton) and the gauging of matrix product
  unitary symmetries (arXiv:2502.20257) are the next steps of QCALean on its
  qudit side. To avoid two formalizations of the same results, the TNLean
  issues on these topics (#5710, #6028, #6029, #7035, #7036, #7038, #7039,
  #7040, #7122, and the gauging trackers #7256, #7257, #7259 to #7262, #7281,
  #7295) are left to that group, who report progress on them. Where TNLean
  already has a statement, theirs is stated so that the two agree under the
  isomorphism of the quasi-local algebras below.
- **The quasi-local algebra.** TNLean defines `SpinChain.QuasiLocalAlgebra d`
  as the completion of the algebraic local algebra
  (`TNLean/QCA/QuasiLocal.lean`). LocalAlgebrasLean defines
  `quasiLocalAlgebra s₀` as the norm closure of the local matrix algebras among
  bounded operators on a configuration Hilbert space, with a universal property
  for compatible families of unital star homomorphisms. That property gives a
  star isomorphism between the two constructions, after which theorems transfer
  in both directions. The namespaces do not collide.
- **Lieb–Robinson bounds.** TNLean has propagation results in
  `TNLean/Circuit/LiebRobinson/` and in the PEPS area-law development.
  LocalityLean proves the analytic bounds and a local-approximation theorem.
  The statements have not been compared in detail.
- **Gaussian tensor networks.** TNLean has none; BosonicLean and FermionicLean
  cover Gaussian matrix product states, bosonic and fermionic.

## How TNLean would use them

Either arrangement leaves existing TNLean code unchanged: add a library to
`lakefile.toml`, pinned to a commit as QICLean is, with one bridge file per
overlap (for example the star isomorphism of the two quasi-local algebras)
written when a TNLean result first needs a theorem from that side; or a
separate bridge library, maintained by that group, depending on TNLean and on
their libraries and containing only the isomorphisms and transferred theorems.
Neither project restructures around the other's definitions. Problem reports
for their libraries go through their own issue trackers.
