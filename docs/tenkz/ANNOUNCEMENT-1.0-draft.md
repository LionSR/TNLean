# tenkz 1.0 announcement — DRAFT

<!-- Native sub-issue #5357 of #4164. This draft may land before the soak;
     it does NOT authorize a version bump. Every `[[PENDING-RELEASE: ...]]`
     token below is a placeholder the serial release owner replaces when
     #4164 completes after the 28-day soak. Publication is blocked while any
     PENDING-RELEASE token remains; check mechanically with:

         grep -n 'PENDING-RELEASE' docs/tenkz/ANNOUNCEMENT-1.0-draft.md

     Acceptance (#5357): no unsupported faithfulness claim, no stale
     transitional syntax (no tenkzfree, no millimetre placement, no
     out=/in=, no deleted scripts), one representative figure in the current
     documented surface. -->

Pending release fields:

- version number: `[[PENDING-RELEASE: version]]`
- publication date: `[[PENDING-RELEASE: date]]`
- freeze SHA: `[[PENDING-RELEASE: freeze-sha]]`
- archive hash: `[[PENDING-RELEASE: archive-hash]]`
- CTAN URL: `[[PENDING-RELEASE: ctan-url]]`
- release URL: `[[PENDING-RELEASE: release-url]]`
- compatibility/versioning policy reference (#5352, DESIGN.md): `[[PENDING-RELEASE: policy-section]]`

---

## tenkz `[[PENDING-RELEASE: version]]`: a declarative language for tensor-network diagrams

Released `[[PENDING-RELEASE: date]]`.

tenkz is the tensor-network diagram package of the TNLean project. It draws
matrix product states, tensor trains, PEPS sheets, string diagrams, and
channel sandwiches as *declared structure*, not as placed ink: an author
states what the network is, and the package measures where the ink goes.

### Addresses, never coordinates

A tenkz picture is a set of typed records — atoms, wires, and marks — that
live at *addresses* inside a declared frame. A frame (flat grid, projected
plane, or circle) gives every address a place and local axes, so the author
never measures a length and never names a page direction: the outward
physical leg of a row is that row's own normal, a label's quadrant is a
bearing in the host's axes, and orientation is a consequence of where a
record sits. Every index ends in exactly one of a bond, a closure, or a
declared open leg — and `tenkzeq` checks that the two sides of a pictured
equation expose the same boundary signature.

### One figure

The gauge equation Bⁱ = X Aⁱ X⁻¹ of the fundamental theorem of matrix
product states:

```latex
\[
  \begin{tenkz}[physical=up]
    \tn[up=$i$]{B}
  \end{tenkz}
  \;=\;
  \begin{tenkz}[physical=up]
    \tnX{X} & \tn[up=$i$]{A} & \tnX{X^{-1}}
  \end{tenkz}
\]
```

No coordinates, no lengths: `physical=up` declares each atom's outward leg,
`&` chains atoms along the row, and the protruding stubs on both sides are
the same boundary signature — two open virtual indices and one physical
index — which the equation check verifies.

### The compatibility promise

The manual is the contract. From 1.0 on, the documented surface — the
registry vocabulary of environments, commands, and keys, and the `.tnlog`
event stream the checking tools consume — changes only per the versioning
policy (`[[PENDING-RELEASE: policy-section]]`): patch releases fix rendering
defects, minor releases extend the vocabulary by declaration, and breaking
changes require a major release. Older documents keep compiling through the
compatibility spellings listed exhaustively in the manual's compatibility
chapter; each alias reads old sources and normalizes to the same semantic
events as its canonical replacement.

### Where things live

- Package on CTAN: `[[PENDING-RELEASE: ctan-url]]`
- Manual (PDF): ships with the package; source at `docs/tenkz/` in the
  TNLean repository
- Release notes and archive: `[[PENDING-RELEASE: release-url]]`
  (archive hash `[[PENDING-RELEASE: archive-hash]]`, frozen at
  `[[PENDING-RELEASE: freeze-sha]]`)
- Project: <https://github.com/LionSR/TNLean>

### Known limitations

- tenkz is a LaTeX package (expl3 over TikZ); it renders where LaTeX
  renders.
- It is a tensor-network language, not a general commutative-diagram tool;
  coherence diagrams are better served by plain tikz-cd.
- Compatibility spellings exist to read older documents. New documents use
  canonical spellings; the compatibility chapter is a sunset list, not a
  second surface.
- The language grows by declaration (`\tndeclare`), not by per-figure
  drawing commands; raw-coordinate escape hatches exist but sit outside the
  checked surface.
