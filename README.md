# TNLean

[![Lean Action CI](https://github.com/LionSR/TNLean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/lean_action_ci.yml)
[![Compile blueprint](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml)
![sorries](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/sorries.json)
![axioms](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/axioms.json)
![Lean](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/lean.json)
![Mathlib](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/mathlib.json)

TNLean is a Lean 4 library for finite-dimensional tensor-network mathematics.  Its
central thread is the Fundamental Theorem of Matrix Product States (MPS), with
formal developments of finite-dimensional quantum channels, Perron--Frobenius
and quantum Wielandt theory, parent Hamiltonians, matrix-product density
operators (MPDOs), renormalization fixed points (RFPs), and the present PEPS
frontier.  The project is built on
[Mathlib](https://github.com/leanprover-community/mathlib4) and currently uses
Lean 4 / Mathlib `v4.29.0`.

This is a research formalization.  The maintained root import is

```lean
import TNLean
```

and it imports the public modules intended for downstream users.  Some frontier
files still contain explicit `sorry`s or sanctioned axioms; the badges above and
the LeanBlueprint give the current accounting.  The README below is therefore
conservative: it separates proved infrastructure and theorem packages from the
canonical-form, parent-Hamiltonian, MPDO/RFP, and PEPS arguments that remain
active formalization fronts.

## Mathematical scope

### Matrix product states and the Fundamental Theorem

The MPS core introduces tensors `MPSTensor d D`, word evaluation, matrix product
vector (MPV) coefficients, injectivity, blocking, transfer maps, overlap matrices,
block-diagonal tensors, and gauge equivalence.  The basic single-block theorem is
proved by extending the map $A^i \mapsto B^i$ linearly, proving multiplicativity
from MPV equality, and applying Skolem--Noether for full matrix algebras:

```lean
theorem MPSTensor.fundamentalTheorem_singleBlock {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) : GaugeEquiv A B
```

The library also contains chain-level variants, translation-invariance
corollaries, finite-length SameMPV interfaces, and bridges between equality of
periodic states and equality of MPV families under explicit hypotheses.

The multi-block and canonical-form development is substantially larger.  It
formalizes BNT-style block data, block permutations, normal and canonical-form
predicates, overlap decay hypotheses, coefficient-convergence statements, and
same-structure assembly theorems.  Current top-level theorems include the
canonical-form equal-MPV and proportional-MPV results under explicit structural
and coefficient hypotheses, together with reduction theorems that decompose a
general tensor, normalize nonzero irreducible blocks by a trace-preserving gauge,
and remove periods by blocking or cyclic-sector decomposition.  What is not yet
advertised as a completed theorem is the fully automatic passage from arbitrary
raw tensors to the final paper-level canonical form with all common-length,
zero-tail, and sector-comparison hypotheses derived internally.

### Quantum channels and Perron--Frobenius theory

The channel side works with finite-dimensional matrix algebras.  It includes
positive and completely positive maps, density-matrix retracts, partial traces,
Choi--Jamiolkowski matrices, Kraus representations, Stinespring dilations, CP
order and Radon--Nikodym infrastructure, POVMs, Schwarz inequalities and
multiplicative domains, fixed-point algebras, irreducibility, stationary supports,
peripheral spectra, and finite-dimensional quantum Markov semigroups in the
style of Wolf's *Quantum Channels & Operations*.

One recurrent tool is the Perron--Frobenius existence theorem for positive maps,
proved through a Brouwer fixed-point theorem on density matrices:

```lean
theorem exists_posSemidef_eigenvector [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpos : IsPositiveMap E)
    (hNZ : ∀ {ρ : Matrix (Fin D) (Fin D) ℂ}, ρ.PosSemidef → ρ ≠ 0 → E ρ ≠ 0) :
    ∃ (ρ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ),
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < r ∧ E ρ = (r : ℂ) • ρ
```

The formalized Wolf material is selective rather than a chapter-by-chapter
completion.  Chapters on Schwarz inequalities, spectral theory, fixed points, and
semigroups are the most developed; entropy and some operator-convexity facts are
recorded as explicit axiomatized interfaces while the corresponding finite-
dimensional analysis is built out.

### Quantum Wielandt theory

The Wielandt hierarchy supplies span-growth infrastructure, rank-one extraction,
rectangular span arguments, primitive-map definitions, and paper-facing endpoint
modules.  A central current theorem is the cumulative $D^2$ bound for the
project's normality predicate:

```lean
theorem cumulative_wielandt_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤
```

The active frontier here is to align sharpened quantum Wielandt bounds with the
subspace elements and constants used in the source literature.  The repository
keeps mathematical notes under `docs/paper-gaps/` when a paper argument and the
formal statement are not identical.

### Parent Hamiltonians, MPDO/RFP, PEPS, and examples

The parent-Hamiltonian modules define local terms and finite-chain ground spaces,
prove basic frustration-free and annihilation statements, develop intersection
and wrapping-window infrastructure, and contain unique-ground-state theorems for
injective or normal MPS under the hypotheses stated in the Lean declarations.
The martingale and overlapping-window estimates needed for spectral-gap proofs
remain an active frontier.

The MPDO and RFP modules contain foundations for matrix-product density
operators, locally purified density operators, vertical and bi-canonical form,
zero-correlation-length and RFP predicates, pure-recovery and structural-form
interfaces, fusion-isometry and commuting-form constructions, and related
bridges.  These files should be read as a growing formal infrastructure for the
MPDO/RFP parts of the tensor-network story, not as a completed classification
proof.

The PEPS directory gives finite-graph tensor definitions, state coefficients,
virtual insertion and blocking infrastructure, local gauge operations, and the
current scaffold for the injective PEPS Fundamental Theorem.  The PEPS theorem
statements are intentionally present near the definitions they require, but the
complete proof of the two-dimensional theorem is still future work.

The repository also contains small MPS examples such as AKLT, GHZ, even parity,
and $\mathbb{Z}/2\mathbb{Z}$ examples, together with the `TNLean/PiAlgebra/`
directory of algebraic Fundamental-Theorem variants.

## Module structure

`TNLean.lean` is the public import surface.  It imports maintained modules and
intentionally leaves archival material in `TNLean/Archive/` outside the root
import.  The main source tree is organized as follows.

| Path | Role |
|---|---|
| `TNLean/Algebra`, `TNLean/Analysis`, `TNLean/Topology` | Matrix algebra, trace pairings, Gram matrices, Frobenius norms, Skolem--Noether, convergence helpers, and finite-dimensional fixed-point infrastructure. |
| `TNLean/Axioms`, `TNLean/Entropy` | Explicit interfaces for Brouwer, strong subadditivity, Beigi recovery, operator convexity, and entropy corollaries. |
| `TNLean/Channel` | Quantum-channel representations, Schwarz theory, fixed points, irreducibility, peripheral spectra, semigroups, determinants, POVMs, and Wolf chapter index modules. |
| `TNLean/QPF`, `TNLean/Spectral` | Perron--Frobenius, positivity, mixed transfers, overlap decay, spectral gaps, and quantitative correlation estimates. |
| `TNLean/MPS/Core`, `TNLean/MPS/Chain`, `TNLean/MPS/Overlap` | MPS tensors, words, blocking, chains, transfer maps, and overlap matrices. |
| `TNLean/MPS/FundamentalTheorem`, `TNLean/MPS/BNT`, `TNLean/MPS/CanonicalForm`, `TNLean/MPS/Periodic`, `TNLean/MPS/Structure` | Single-block, same-structure, BNT, periodic, and canonical-form Fundamental-Theorem material. |
| `TNLean/MPS/ParentHamiltonian` | Parent Hamiltonians, local projectors, ground spaces, intersection and wrapping-window arguments, commuting cases, and martingale estimates. |
| `TNLean/MPS/MPDO`, `TNLean/MPS/RFP` | MPDO/LPDO foundations, canonical-form and zero-correlation-length predicates, pure RFP structures, and structural bridges. |
| `TNLean/Wielandt` | Quantum Wielandt span growth, rank-one constructions, rectangular span, primitivity equivalences, and paper-facing endpoints. |
| `TNLean/PEPS` | PEPS definitions, virtual insertions, blocking, local gauge transformations, and the injective PEPS theorem frontier. |
| `TNLean/PiAlgebra` | Algebraic Fundamental-Theorem variants and block-separation statements. |
| `blueprint/`, `docs/` | The LeanBlueprint, style and contribution guides, CI documentation, and paper-gap notes. |

For exact imports, read `TNLean.lean`; it is the most reliable snapshot of the
maintained library surface.

## Current frontiers

The issue tracker contains fine-grained formalization tasks.  The main fronts at
the present release state are:

- completing the arbitrary-tensor-to-final-canonical-form path, especially common
  blocking lengths, cyclic-sector comparison, zero-tail transport, and the
  finite-length span equalities used by the block permutation theorem;
- strengthening the parent-Hamiltonian story from intersection and uniqueness
  results toward martingale and overlapping-window spectral-gap estimates;
- extending the quantum Wielandt endpoint to the sharpened bounds and subspace
  elements used in the current paper notes;
- turning the MPDO/RFP structural interfaces into complete classification
  arguments; and
- replacing the PEPS Fundamental-Theorem scaffold by a full proof of local gauge
  existence, consistency, and uniqueness.

Known mathematical deviations, missing hypotheses, or places where the formal
route differs from a cited source are recorded in `docs/paper-gaps/` as
stand-alone mathematical notes.

## Building

The Lean version is pinned by `lean-toolchain`; Mathlib is pinned in
`lakefile.toml` and `lake-manifest.json`.

```bash
# Optional but recommended: download pre-built Mathlib artifacts.
lake exe cache get

# Build the default target, which is TNLean.
lake build

# Equivalently, build the public Lean library target.
lake build TNLean

# Check a single file during development.
lake env lean TNLean/MPS/FundamentalTheorem/Basic.lean
```

Repository-specific notes for the Lean/Mathlib `4.29.0` migration live in
[`docs/upgrade_4_29.md`](docs/upgrade_4_29.md).

## Blueprint and documentation

The LeanBlueprint in `blueprint/` is the mathematical companion to the Lean
library.  Its chapters cover the MPS core, the single-block theorem, quantum
channels, Perron--Frobenius theory, Schwarz inequalities, spectral theory,
quantum Wielandt, canonical form, BNT and block-permutation arguments, periodic
Fundamental-Theorem material, semigroups, PEPS, symmetry, parent Hamiltonians,
correlations, and examples.

Typical blueprint commands are:

```bash
lake build TNLean
cd blueprint
leanblueprint checkdecls
leanblueprint web   # or: leanblueprint pdf / leanblueprint all
```

The command `leanblueprint checkdecls` assumes that the Lean declarations named
in the blueprint are available from a successful Lean build.  General repository
guidance for contributors is in `AGENTS.md` and `CLAUDE.md`; style and review
conventions are in `docs/`.

## References

The formalization draws principally on the following sources.

- D. Pérez-García, F. Verstraete, M. M. Wolf, J. I. Cirac,
  *Matrix Product State Representations*,
  [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197),
  Quantum Inf. Comput. **7** (2007).
- M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac,
  *A quantum version of Wielandt's inequality*,
  [arXiv:0909.5347](https://arxiv.org/abs/0909.5347),
  J. Math. Phys. **51**, 102205 (2010).
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete,
  *Matrix Product Density Operators*,
  [arXiv:1606.00608](https://arxiv.org/abs/1606.00608),
  Annals of Physics **378** (2017).
- G. De las Cuevas, J. I. Cirac, N. Schuch, D. Pérez-García,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  [arXiv:1708.00029](https://arxiv.org/abs/1708.00029),
  J. Math. Phys. **58**, 121901 (2017).
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete,
  *Matrix Product States and Projected Entangled Pair States*,
  [arXiv:2011.12127](https://arxiv.org/abs/2011.12127),
  Rev. Mod. Phys. **93**, 045003 (2021).
- A. Molnár, N. Schuch, F. Verstraete, J. I. Cirac,
  *Fundamental theorem for injective projected entangled pair states*,
  [arXiv:1804.04964](https://arxiv.org/abs/1804.04964) (2018).
- M. M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012).
- [Mathlib4](https://github.com/leanprover-community/mathlib4), the Lean 4
  mathematics library.
