<p align="center">
  <img src="docs/logo.svg" alt="TNLean" width="440">
</p>

<p align="center">
  <b>Tensor-network theory, formalized in Lean 4.</b>
</p>

[![PR CI](https://github.com/LionSR/TNLean/actions/workflows/pr-ci.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/pr-ci.yml)
[![Compile blueprint](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml)
![sorries](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/sorries.json)
![axioms](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/axioms.json)
![Lean](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/lean.json)
![Mathlib](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/mathlib.json)

TNLean is a [Lean 4](https://lean-lang.org/) library, built on
[Mathlib](https://github.com/leanprover-community/mathlib4), that formalizes
the mathematics of tensor networks: matrix product states (MPS), the quantum
channels and transfer operators that govern them, and the theorems relating
the two. Every result is checked by Lean down to the axioms it assumes.

The first released part of the library is the **fundamental theorem of matrix
product states** (Pérez-García, Verstraete, Wolf, Cirac 2007; Cirac,
Pérez-García, Schuch, Verstraete 2017): two tensors generate the same quantum
states at every system size exactly when an invertible change of basis on the
bond indices, a gauge transformation, relates them. Proving this required
formalizing the quantum-information theory the proof rests on, following
Wolf's *Quantum Channels & Operations*: channel representations, Schwarz
inequalities, quantum Perron-Frobenius theory, and the quantum Wielandt
inequality. The library also contains material beyond the fundamental
theorem, at varying levels of completeness; the sections below say what is
proved and what is not.

The mathematics is written up in the
[blueprint](https://lionsr.github.io/TNLean/blueprint/), which states each
definition and theorem in ordinary mathematical language and links it to the
Lean proof. It is available as a
[web version](https://lionsr.github.io/TNLean/blueprint/), a
[full PDF](https://lionsr.github.io/TNLean/blueprint.pdf), and a
[separate FT-MPS PDF](https://lionsr.github.io/TNLean/blueprint-ch01-12.pdf),
the fundamental-theorem part that is being released first. The generated
[API documentation](https://lionsr.github.io/TNLean/docs/) covers every
declaration in the Lean source.

The agent-driven workflow used to build this library is described in the
companion paper: S. Lu, E. Tjoa, J. I. Cirac, *Multi-agent Autoformalization
of Tensor Network Theory*,
[arXiv:2607.07857](https://arxiv.org/abs/2607.07857). Most of the
formalization was carried out by agents running on
[TeXRA](https://texra.ai), whose `lean-env-action` also sets up the Lean and
blueprint toolchain used in the workflows under `.github/workflows/`.

The library loads as a single import (Lean 4 / Mathlib `v4.32.0`):

```lean
import TNLean
```

This is a research formalization in progress, not a finished textbook. Some
files contain unfinished proofs (`sorry`) or results assumed as axioms; the
badges above track the current counts.

## What is proved

### The fundamental theorem of matrix product states

An MPS describes a quantum state on a chain by assigning a matrix `A^i` to
each local basis state; products of these matrices give the state's
coefficients. The library defines these tensors (`MPSTensor d D`) and proves
the fundamental theorem in both of its forms.

The single-block case: if a tensor is injective (its matrices span the full
matrix algebra) and two tensors generate the same states, then they are
related by a gauge transformation.

```lean
theorem MPSTensor.fundamentalTheorem_singleBlock {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) : GaugeEquiv A B
```

The general case: an arbitrary tensor decomposes into normal blocks, and the
library constructs this canonical form, the basis of normal tensors that
makes it unique, and the multi-block theorem
(`MPSTensor.fundamentalTheorem_equal_canonicalForm`): two canonical forms
generating the same states at every length are related by a single invertible
gauge. The exact hypotheses of each theorem are stated in its Lean signature
and in the blueprint.

As a first physics application, the library proves that an on-site symmetry
of an injective MPS induces a projective representation on the bond space,
whose cohomology class is a well-defined invariant of the symmetric tensor.
This is the MPS ingredient in the classification of one-dimensional
symmetry-protected topological phases.

### Quantum channels and Perron-Frobenius theory

Following Wolf's *Quantum Channels & Operations*, the library develops
quantum channels on finite-dimensional matrix algebras: the Choi, Kraus, and
Stinespring representations, Kadison-Schwarz inequalities with their equality
case and the multiplicative domain, fixed-point structure, irreducibility,
peripheral spectra, and quantum Markov semigroups. The chapters most relevant
to MPS are the most developed.

A recurring tool is the quantum Perron-Frobenius theorem: every positive map
has a positive-semidefinite eigenvector with positive eigenvalue. The proof
runs through a Brouwer fixed-point argument on density matrices; Brouwer's
theorem itself is imported from an external Lean formalization (via Scarf's
lemma) rather than assumed.

```lean
theorem exists_posSemidef_eigenvector [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpos : IsPositiveMap E)
    (hNZ : ∀ {ρ : Matrix (Fin D) (Fin D) ℂ}, ρ.PosSemidef → ρ ≠ 0 → E ρ ≠ 0) :
    ∃ (ρ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ),
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < r ∧ E ρ = (r : ℂ) • ρ
```

### Quantum Wielandt theory

The quantum Wielandt inequality controls how quickly products of a tensor's
matrices span the whole matrix algebra, which determines the blocking length
after which a normal tensor becomes injective. For a normal tensor the
library proves a spanning length of at most `D^2`, where `D` is the bond
dimension:

```lean
theorem cumulativeSpan_eq_top_of_isNormal_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤
```

Sharpening this bound to match the constants in the literature is ongoing.

## What is in progress

Beyond the released core, the library develops several neighboring topics,
each at an earlier stage.

- **Parent Hamiltonians.** Local Hamiltonians whose ground space is the MPS,
  with frustration-freeness and ground-state uniqueness proved for injective
  and normal tensors. The estimates that would give a spectral gap are not
  yet done.
- **Matrix-product density operators.** Mixed-state analogues of MPS, their
  canonical and zero-correlation-length forms, and renormalization fixed
  points. This is a foundation, not yet a complete classification.
- **Projected entangled pair states (PEPS).** The two-dimensional
  generalization of MPS, with fundamental-theorem results for normal PEPS on
  finite graphs.
- **Entropy.** Von Neumann entropy, strong subadditivity, and quantum Markov
  chains.
- **Examples.** Concrete states such as AKLT, GHZ, even parity, and the
  $\mathbb{Z}/2\mathbb{Z}$ models, alongside algebraic variants of the
  fundamental theorem.

Where a formal statement does not exactly match its cited source, the
discrepancy is recorded as a mathematical note under `docs/paper-gaps/`.

## Organization of the source

The generated file `TNLean.lean` collects everything imported as one library;
legacy material in `TNLean/Archive/` is kept out of it. Directory aggregators
are generated too. Never edit these aggregators by hand. After adding, moving,
or removing a production `.lean` file, regenerate and check them with:

```bash
python3 scripts/generate_import_aggregators.py
python3 scripts/generate_import_aggregators.py --check
```

See [`docs/import_structure.md`](docs/import_structure.md) for the hierarchy and
Archive policy. The source is grouped as follows.

| Path | Contents |
|---|---|
| `TNLean/Algebra`, `TNLean/Analysis`, `TNLean/Topology` | Linear algebra of matrices: traces, Gram matrices, Frobenius norms, Skolem-Noether, and convergence and fixed-point results. |
| `TNLean/Axioms` | The few results still assumed as axioms, isolated in dedicated modules so the assumption boundary stays auditable (the `axioms` badge counts them). |
| `TNLean/Entropy` | Von Neumann entropy, strong subadditivity, mutual information, and quantum Markov chains. |
| `TNLean/Channel` | Quantum channels: representations, Schwarz theory, fixed points, irreducibility, peripheral spectra, and semigroups. |
| `TNLean/QPF`, `TNLean/Spectral` | Perron-Frobenius theory, spectral gaps, and correlation-decay estimates. |
| `TNLean/MPS/Core`, `TNLean/MPS/Chain`, `TNLean/MPS/Overlap` | Matrix product states: tensors, words, blocking, transfer maps, and overlap matrices. |
| `TNLean/MPS/FundamentalTheorem`, `.../BNT`, `.../CanonicalForm`, `.../Periodic`, `.../Structure`, `.../Irreducible` | The fundamental theorem in its single-block, multi-block, canonical-form, and periodic versions. |
| `TNLean/MPS/Symmetry` | On-site and virtual symmetry, cohomology of cocycles, and string order. |
| `TNLean/MPS/ParentHamiltonian` | Parent Hamiltonians, their ground spaces, and uniqueness of the ground state. |
| `TNLean/MPS/MPDO`, `TNLean/MPS/RFP` | Matrix-product density operators and renormalization fixed points. |
| `TNLean/MPS/Examples` | Worked examples (AKLT, GHZ, even parity, $\mathbb{Z}/2\mathbb{Z}$). |
| `TNLean/Wielandt` | The quantum Wielandt inequality and primitivity. |
| `TNLean/PEPS` | Projected entangled pair states on finite graphs. |
| `TNLean/PiAlgebra` | Algebraic variants of the fundamental theorem. |
| `blueprint/`, `docs/` | The mathematical companion text, conventions, and notes on gaps from the sources. |

## Status

The README does not track which individual results are complete; the
authoritative, always-current picture is:

- the `sorries` and `axioms` badges at the top of this page, counting
  unfinished proofs and assumed results;
- the [blueprint](https://lionsr.github.io/TNLean/blueprint/), which marks
  each theorem as formalized or not; and
- `docs/paper-gaps/`, which records where a formal statement diverges from
  its cited source.

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

Repository-specific notes from past Lean/Mathlib upgrades are collected in
[`docs/upgrade_4_29.md`](docs/upgrade_4_29.md).

## Blueprint and documentation

The blueprint in `blueprint/` states the definitions and theorems in ordinary
mathematical language and links each one to its Lean proof. It is built with
`leanblueprint` on top of a successful `lake build`:

```bash
lake build TNLean
cd blueprint
leanblueprint checkdecls
leanblueprint web   # or: leanblueprint pdf / leanblueprint all
```

The FT-MPS release volume is built by
`scripts/build_blueprint_ch01_12.sh` and published automatically with the
rest of the site.

Conventions for contributors are collected in `AGENTS.md`, `CLAUDE.md`, and
`docs/`.

## License

The Lean source, the blueprint, and the other original content of this
repository are released under the Apache License 2.0 (see
[`LICENSE`](LICENSE)). The `Papers/` directory contains the arXiv sources of
the papers being formalized; these are third-party works that remain under
their authors' copyright and are **not** covered by the repository license.
See [`Papers/NOTICE.md`](Papers/NOTICE.md).

## References

The formalization draws principally on the following sources.

- D. Pérez-García, F. Verstraete, M. M. Wolf, J. I. Cirac,
  *Matrix Product State Representations*,
  [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197),
  Quantum Inf. Comput. **7** (2007).
- M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac,
  *A quantum version of Wielandt's inequality*,
  [arXiv:0909.5347](https://arxiv.org/abs/0909.5347),
  IEEE Trans. Inf. Theory **56**(9), 4668--4673 (2010).
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and Boundary Theories*,
  [arXiv:1606.00608](https://arxiv.org/abs/1606.00608),
  Ann. Phys. **378**, 100--149 (2017).
- G. De las Cuevas, J. I. Cirac, N. Schuch, D. Pérez-García,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  [arXiv:1708.00029](https://arxiv.org/abs/1708.00029),
  J. Math. Phys. **58**, 121901 (2017).
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete,
  *Matrix Product States and Projected Entangled Pair States*,
  [arXiv:2011.12127](https://arxiv.org/abs/2011.12127),
  Rev. Mod. Phys. **93**, 045003 (2021).
- A. Molnár, J. Garre-Rubio, D. Pérez-García, N. Schuch, J. I. Cirac,
  *Normal projected entangled pair states generating the same state*,
  [arXiv:1804.04964](https://arxiv.org/abs/1804.04964),
  New J. Phys. **20**, 113017 (2018).
- D. Pérez-García, M. M. Wolf, M. Sanz, F. Verstraete, J. I. Cirac,
  *String Order and Symmetries in Quantum Spin Lattices*,
  [arXiv:0802.0447](https://arxiv.org/abs/0802.0447),
  Phys. Rev. Lett. **100**, 167202 (2008).
- C. Fernández-González, N. Schuch, M. M. Wolf, J. I. Cirac, D. Pérez-García,
  *Frustration free gapless Hamiltonians for Matrix Product States*,
  [arXiv:1210.6613](https://arxiv.org/abs/1210.6613),
  Commun. Math. Phys. **333**, 299--333 (2015).
- N. Schuch, I. Cirac, D. Pérez-García,
  *PEPS as ground states: Degeneracy and topology*,
  [arXiv:1001.3807](https://arxiv.org/abs/1001.3807),
  Ann. Phys. **325**, 2153--2192 (2010).
- J. I. Cirac, J. Garre-Rubio, D. Pérez-García,
  *Mathematical open problems in projected entangled pair states*,
  [arXiv:1903.09439](https://arxiv.org/abs/1903.09439),
  Rev. Mat. Complut. **32**, 579--599 (2019).
- M. M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012).
- [Mathlib4](https://github.com/leanprover-community/mathlib4), the Lean 4
  mathematics library.
