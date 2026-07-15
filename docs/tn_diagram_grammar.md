# Tensor-network diagram calculus

This document specifies the tensor-network notation used in the blueprint and
the accompanying slides.  A diagram is a labelled network of typed ports.  Its
mathematical content is determined by its atoms, its contractions, and its open
interfaces; numerical canvas coordinates are not part of the notation.

The implementation is the repository-local TikZ library in `tex/tn/`, loaded by

```tex
\usetikzlibrary{tn}
```

The library is the single source of glyph geometry, layout dimensions,
typography, colours, port schemas, reusable motifs, and chapter-diagram
declarations.  Chapter and slide sources use only the public commands described
below.

## Mathematical conventions

- A solid line joining two ports denotes contraction of the corresponding
  indices.  Ordinary contractions are straight whenever the topology permits.
- Virtual and physical indices are distinct types.  A morphism endpoint is a
  third type and is used for maps between complete networks rather than tensor
  indices.  The library rejects a contraction between unlike types.
- A curved line is reserved for a trace or a genuinely periodic identification.
  Orthogonal routing may be used when a straight contraction would obscure the
  order of composition.
- A crossing is never left implicit.  Coincident lines meet only at a declared
  junction; noninteracting lines cross only at a declared bridge.
- Colour is redundant.  Labels, topology, line form, or boundary form preserve
  every distinction in greyscale.
- Tensor products and direct sums are written as mathematical symbols.  They
  are not represented by index contractions.

The first atom of a term is placed at its origin.  Every subsequent atom is
placed relative to a named atom:

```tex
\begin{TNDiagram}[normal]
  \TNMPSSite{leftTensor}{at=origin}{A}
  \TNMPSSite{rightTensor}{right=of leftTensor}{B}
  \TNConnectVirtual{leftTensorE}{rightTensorW}
  \TNOpenVirtualWest{leftTensorW}
  \TNOpenVirtualEast{rightTensorE}
  \TNOpenPhysicalNorth{leftTensorN}
  \TNOpenPhysicalNorth{rightTensorN}
\end{TNDiagram}
```

The name of an atom is local to one `TNDiagram`.  It prefixes the names of all
ports on that atom.  Thus `leftTensorE` is the east virtual port of
`leftTensor`.

## Public vocabulary

The following marked block is checked against the TeX declarations by the
semantic audit.  It deliberately lists the small constructive vocabulary, not
the 115 named chapter diagrams derived from the catalogue.

<!-- TN-PUBLIC-VOCABULARY:BEGIN -->

The structural containers are `TNDiagram`, `TNTerm`, `TNRelation`, and
`TNEquationRow`.  Layout profiles are selected by `TNLayoutProfile` and are
named `normal` and `compact`.

The declared atoms and oriented maps are `TNTensor`, `TNComponent`, `TNFactor`,
`TNMap`, `TNState`, `TNExpression`, `TNInsertion`, `TNJunction`,
`TNOperatorState`, `TNSectorGauge`, `TNInverseSectorGauge`, `TNMPSSite`,
`TNMPOSite`, `TNRotatedMPOSite`, `TNPEPSSite`, `TNDoubleLayer`,
`TNPurificationSite`, `TNStackedMPOProduct`, `TNCompactTraceCell`,
`TNTrivalentMapRight`, `TNTrivalentMapLeft`, `TNTrivalentMapDown`, and
`TNTrivalentMapUp`.  A general oriented trivalent map is made with
`TNTrivalentMap`; its named specializations are `TNSplitMap`, `TNMergeMap`,
`TNFusionMap`, `TNCofusionMap`, `TNActionMap`, `TNCoactionMap`,
`TNPhysicalSplitMap`, and `TNPhysicalMergeMap`.

Typed composition uses `TNConnectVirtual`, `TNConnectPhysical`, and
`TNConnectMorphism`.  Orthogonal variants are `TNConnectVirtualHV`,
`TNConnectVirtualVH`, `TNConnectPhysicalHV`, `TNConnectPhysicalVH`,
`TNConnectMorphismHV`, and `TNConnectMorphismVH`.  Traces use
`TNTraceVirtualBelow`, `TNTraceVirtualAbove`, `TNTraceVirtualRight`,
`TNTracePhysicalBelow`, `TNTracePhysicalAbove`, and `TNTracePhysicalRight`.
Named aliases use `TNPortAlias`.  Open interfaces use `TNOpenVirtualWest`,
`TNOpenVirtualEast`, `TNOpenVirtualNorth`, `TNOpenVirtualSouth`,
`TNOpenPhysicalWest`, `TNOpenPhysicalEast`, `TNOpenPhysicalNorth`, and
`TNOpenPhysicalSouth`.

Labels attached to mathematical objects use `TNLabelAbove`, `TNLabelBelow`,
`TNLabelLeft`, or `TNLabelRight`.  Grouped regions use `TNGroupingRegion`,
`TNGroupingRegionAbove`, or `TNGroupingRegionSelectedBelow` and are fitted to
named atoms.  Repeated omissions use `TNOmission` or `TNStackedOmission`.

<!-- TN-PUBLIC-VOCABULARY:END -->

Raw points, arbitrary anchors, arbitrary paths, and freely placed labels are
not public notation.  In particular, clients must not use `TNPoint`,
`TNPointBetween`, `TNLabel`, `TNPlacedLabel`, any `TNPlacedLabel...` variant,
`TNCanvas`, `TNGroupBoundary`, `TNFactorBoundary`, `TNAnnotation`,
`TNSelectedPath`, `TNSecondaryPath`, `TNSelectedRegionPath`,
`TNSecondaryRegionPath`, or `TNComplementRegionPath`.  Raw TikZ drawing,
coordinates, shifts, scales, line widths, fills, padding, and box dimensions
are likewise forbidden in chapters, slides, and catalogue declarations.

## Port schemas

Port roles are mathematical and do not change when a glyph is rotated or
reflected.

| Atom | Virtual ports | Physical ports |
|---|---|---|
| MPS site | `West`, `East` | `Ket` |
| MPO site | `West`, `East` | `Ket`, `Bra` |
| Rotated MPO site | `North`, `South` | `Ket`, `Bra` |
| PEPS site | `West`, `East`, `North`, `South` | `Ket` |
| Operator state | `WestKet`, `WestBra`, `EastKet`, `EastBra` | none |
| Sector gauge | `West`, `East`, `Block`, `Copy` | none |
| Inverse sector gauge | `West`, `East`, `Block`, `Copy` | none |
| Double layer | `UpperWest`, `UpperEast`, `LowerWest`, `LowerEast` | contracted internally |
| Purification site | `KetWest`, `KetEast`, `BraWest`, `BraEast` | `Ket`, `Bra`, `KetAncilla`, `BraAncilla` |
| Stacked MPO product | `UpperWest`, `UpperEast`, `LowerWest`, `LowerEast` | `UpperKet`, `LowerBra` |
| Compact trace cell | none | contracted internally |

Every trivalent map has the virtual roles `Combined`, `FactorOne`, and
`FactorTwo`.  In the right orientation `Combined` lies to the west; in the left
orientation it lies to the east.  In the down orientation it lies to the south;
in the up orientation it lies to the north.  These rotations change placement,
not meaning.  Physical split and merge maps use the same ordered roles with
physical port type.

Aliases may supply a theorem-specific name such as `MPO` or `StateIn`, but the
alias retains the type of its source and must terminate at a declared atom
port.  Duplicate names, missing ports, incompatible aliases, alias cycles, and
a trace whose endpoints coincide are errors.

## Placement, labels, and regions

Allowed placement keys are `at=origin`, `left=of`, `right=of`, `above=of`,
`below=of`, and the four diagonal relations to a named atom.  Canonical glyph
and motif definitions may contain numerical geometry inside `tex/tn/`; clients
may not.  PEPS constructions are specified by integer lattice indices and
adjacency data rather than canvas positions.

A label belongs to an atom, a port, a contraction, or a fitted region boundary.
It must not float at an unrelated point of the canvas.  Indices use
`\scriptscriptstyle`; glyph labels use `\scriptstyle`.  All typography inherits
the ambient mathematical font.

Fitted boundaries indicate factors, regions, sectors, or stages of a
construction.  They are used only when the enclosure has mathematical meaning.
Decorative boxes and backgrounds are omitted.  Curved boundaries and region
colours never substitute for labels.

## Display form and figure form

A local definition, contraction identity, or short equality is a mathematical
display.  A diagram is a numbered figure only when spatial topology,
multi-stage routing, a lattice region, or a substantial fusion tree is itself
part of the mathematical assertion.  Captions are reserved for these figures.
The role is recorded in the catalogue declaration and is checked against every
chapter use.

Each chapter-facing construction has one declaration:

```tex
\TNDeclareDiagram
  {TNExampleIdentity}
  {leftLabel,rightLabel}
  {display}
  {normal}
  {\TNExampleIdentity{A}{B}}
  {chapter/example.tex}
  {<body composed from public atoms and contractions>}
```

The seven fields are respectively the command name, argument schema, display
role, layout profile, audit sample, page context, and body.  The renderer and
gallery read these declarations directly; no parallel list of names, roles,
arguments, or examples is maintained in Python.

## Themes and dimensions

The print theme uses `black!92` for primary ink, `black!55` for secondary ink,
and `red!65!black` for the accent.  Blue and violet occur only when a region or
sector distinction is mathematically genuine.  The dark theme uses `white!94`,
`white!60`, and `orange!80!white`, with cyan and magenta for the corresponding
region and sector distinctions.

Ordinary structure has line width 0.55 pt, secondary guides 0.40 pt, and
distinguished boundaries 0.80 pt.  These values and all spacing dimensions are
defined centrally.  The `normal` and `compact` profiles choose discrete reading
dimensions; they do not scale a completed diagram.  A construction that is too
wide is divided into aligned terms, rows, or panels rather than reduced below
its intended reading size.

## Audit and gallery

Every rendered diagram emits a semantic event log containing its atoms, ports,
aliases, contractions, motif boundaries, and declared crossings.  The audit
checks the event stream, canonicalizes the labelled network graph, and rejects
ill-typed or incomplete constructions.  It also rejects private implementation
commands, raw TikZ, client geometry, stale declarations, ignored arguments,
undeclared crossings, and repeated four-to-eight-atom topologies that should be
a named motif.

The generated gallery contains every declared atom and every registered
diagram.  Atom pages state the complete typed port schema.  Diagram pages show
the actual publication size and a tightly cropped magnified view, together with
the command name, role, profile, and page context.  Print and dark-theme crops
retain at least 3 pt of clear margin between ink and canvas boundary.

## Author checklist

Before adding or changing a diagram, verify the following.

1. The mathematical objects, port types, open interfaces, and contraction
   order agree with the source statement.
2. Atoms are named by their mathematical role and placed only relative to
   previously named atoms or lattice indices.
3. Every contraction joins compatible named ports.  Traces and crossings are
   explicit; ordinary contractions remain straight.
4. Labels belong to semantic anchors and remain clear of sites, wires, and
   boundaries.  Colour supplies no unique information.
5. A topology repeated in four or more atoms is expressed by a shared motif.
6. The declaration records its arguments, role, profile, sample, and every
   page context.  No argument is ignored.
7. The strict semantic audit, gallery, print and dark renders, and the relevant
   pages have been inspected at their actual reading size.
