# One-dimensional area-law Comparator challenge

`Challenge.lean` states the qualitative one-dimensional area law. It imports only Mathlib.
This single file can be copied into a project using Mathlib `v4.35.0-rc3`;
neither TNLean nor QICLean is needed to read or elaborate the challenge.

For fixed local dimension `q ≥ 1`, range `R`, interaction bound `J ≥ 0`, and gap
lower bound `Δ > 0`, the theorem asserts a nonnegative constant `C` such that
every finite open chain with these parameters has ground-state entropy at most
`C` across every cut. The ground state is unique. The constant is chosen before
the chain length and Hamiltonian. Locality, the reduced density matrix, entropy,
and the global gap inequality are explicitly defined using Mathlib. No specific
dependence of `C` on the physical parameters is asserted.

`Solution.lean` proves the same theorem from
`TNLean.MPS.AreaLaw.Hastings.exists_regionEntropy_prefix_le`, the development of
Hastings' argument. It identifies the explicitly defined reduced density matrix
and entropy with those used by that theorem. It does not import `Challenge`.
The definitions are repeated in the solution so that the two files elaborate
independently; Comparator checks that these definitions agree. The proof hole
in `Challenge.lean` is intentional; the solution has none.

`comparator.json` requests equality of the theorem statements, including all
definitions they use, and allows only `propext`, `Quot.sound`, and
`Classical.choice`. There are no definition holes.

From the TNLean repository root on macOS, build with the required cache guard:

```sh
scripts/lake_build_locked.sh Challenge Solution
```

In an already prepared Linux checkout, run the bundled Comparator:

```sh
lake comparator --config verification/area-law/comparator.json
```

On macOS, the bundled Linux sandbox is unavailable. A local check without that
sandbox can be run under the repository lock:

```sh
scripts/lake_build_locked.sh -- lake comparator --inadvisably-no-sandbox \
  --config verification/area-law/comparator.json
```

References: [Comparator](https://github.com/leanprover/comparator), now included
in Lean as `lake comparator`; Hastings,
[*An area law for one-dimensional quantum systems*](https://arxiv.org/abs/0705.2024),
eq. (entbd). The quantitative changes in TNLean's Hastings proof are documented
in the four paper-gap notes cited in `Solution.lean`; this challenge asks only
for the length-independent conclusion.

Local validation on 2026-10-29 with Lean `v4.35.0-rc3`: both modules built, and
the macOS command above completed with `Lean default kernel accepts the solution`
and `Your solution is okay!`. This checked statement agreement, the permitted
axioms, and kernel acceptance, with sandboxing disabled.
