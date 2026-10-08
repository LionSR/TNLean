# Blueprint for complete semi-regular canonical parent spaces

## Coverage

The four new fragments cover all 206 public declarations in the 29 modules
added or reorganized by `859017c07`, `8cbffdae2`, and `d573f6a1e`, as present
at `22eb9657f`. They use 57 mathematical entries, with 38 proof sketches.
Every declaration has one owning tag, and every statement and proof is marked
with its checked status. No earlier range/support ownership is duplicated.

Read the fragments in this order after the existing fixed-representation and
open-region support results:

1. `ch24_peps_semiregular_parent_support.tex`: sparse multiplicity action,
   oriented crossing factors, numbered coordinates, regional operator blocks,
   and product support derived from internal slices.
2. `ch24_peps_copy_parent_transport.tex`: arbitrary positive copy counts,
   actual open-boundary formulas in both directions, supported global
   inverses, whole-parent equivalence, and removal of physical copy weights.
3. `ch24_peps_fourier_parent_transport.tex`: arbitrary-boundary coordinate
   transport, exterior blocks, and complete parent and Hamiltonian kernels.
4. `ch24_peps_semiregular_parent_equivalence.tex`: derived irreducible blocks,
   normalized Fourier coordinates, the actual incident representation, and
   arbitrary physical G-injective parent kernels.

The main declaration is
`TNLean.PEPS.nonempty_ker_regionParentHamiltonian_semiRegularGInjective_equiv`,
owned by `thm:peps_semiregular_g_injective_parent_kernel`.

## Mathematical boundaries

The final statement keeps one unitary semi-regular representation uniformly
on the ordered graph, constant incidence, vertex coverage, and internal-edge
coverage explicit. The physical dimension may differ from the regular
canonical dimension. The local Hamiltonian terms are arbitrary positive
matrices whose kernels equal the actual open-region ranges.

The copy-parent comparison needs internal-edge coverage for its supported
inverses. Its two forward/adjoint inclusions need no coverage. The invertible
physical copy filter and Fourier-coordinate comparison need no coverage.
The arbitrary physical G-injective comparison adds vertex coverage.

These results do not themselves identify native right/up torus coordinates
or the named commuting-pair closure vectors. A native specialization may cite
them without claiming that this ordered-graph statement alone proves the full
source theorem. Link-dependent representations, orientation conventions,
and small-period identifications must be handled in that specialization.
No equality of positive-energy spectra or spectral gaps is asserted.

## Checks

- Forward declaration resolution and unique tag ownership pass against the
  frozen source and the manifest-pinned QICLean source.
- The reverse changed-declaration check passes with base `859017c07^`, head
  `22eb9657f`, and the 29 packet modules. A separate complete-file inventory
  verifies all 206 public declarations, including the moved declarations.
- Every new `ref` and `uses` target exists in the complete blueprint source.
- All four files are formatted with the pinned latexindent 3.24.7 configuration.
- A focused 17-page XeLaTeX PDF renders with no overfull boxes or unresolved
  references or citations. All pages were inspected as a contact sheet, with
  the crossing-boundary identities and final kernel theorem inspected at
  full-page scale.
- The focused web excerpt is generated with the repository's plasTeX
  configuration and texra-blueprint 0.3.8. Reader-facing browser regression
  passes all four generated pages, with 1,070 typeset mathematics instances
  checked at 360-pixel and 1,440-pixel widths, including expanded proofs.
  It finds no unresolved references, visible metadata commands, malformed
  mathematical environments, or whole-page horizontal overflow.

The isolated rendering fixture uses label-only anchors for 19 existing
references outside the excerpt; those targets are independently checked in
the real source. It does not alter the repository routers. Compiled
`leanblueprint checkdecls` and the complete routed build belong to the combined
integration check; this documentation-only change does not rebuild Lean or
change imports, workflows, or MPU-gauging files.
