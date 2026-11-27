# One tensor type: design and migration

Status: proposal, 2026-11-21. This document carries out steps T.1 and T.2 of
`many_body_circuit_architecture.md` ("One tensor type over a physical and a bond basis type";
"the `toMPSTensor` conversion and the definitions of `blockTensor` are swept; blocking becomes
a change of basis type"). It applies the rules of that document: one definition per object
(No dual systems), statements as general as their layer (Generality), and the
build, switch, sweep, delete method.

Progress, 2026-11-26. T.1a and T.1b are done. T.2a′ is done: `MPOTensor d D` is
`MPTensor (Fin d × Fin d) (Fin D)`, and a letter is written `M (i, j)`. The operator part of T.2b
is done: `MPOTensor.blockTensor` is `Kraus.block` renumbered by the blocked ket and bra
indices, and `blockTwo` is the case of two sites. Neither name is deleted yet: `toMPSTensor`
(about 2,500 uses) waits for T.1c, since its codomain is `MPSTensor (d * d) D`, and `blockTwo`
(about 700 uses) waits for the statements over `Fin (d * d)` to be restated.

T.1c is done in part. The definitions of `MPS/Tensor/Defs` (`coeff`, `mpv`, `GaugeEquiv`,
`SameMPV`, `SameMPV₂`, `SameMPV₂Pos`, the two proportionality predicates, `GaugePhaseEquiv`,
`UnitGaugePhaseEquiv`, `IsLeftCanonical`) and their lemmas are stated on `MPTensor α β` and live
in the namespace `MPTensor`; so are `IsReduction` (on `MPTensor α β`), `IsDressedProportional`
(on `MPTensor α β` with boundaries `Matrix μ β ℂ`), `mpvOverlap` (on `MPTensor α (Fin D)`), and
the residual of a reduction with its nilpotency bounds and window sums, with the lemmas of
`MPS/Tensor/Reduction/ReductionResidual` and `ReductionUniqueness` (on `MPTensor α (Fin D)`).
Their dot lemmas elsewhere moved with them, still at `Fin d`, `Fin D`; files that named them
without a prefix open `MPTensor`. Two Kraus heads of the scan, `IsInjective` and `IsNormal`, and
`evalWord`, `transferMap` were already general after T.1a. The bond of `mpvOverlap` stays `Fin D`:
with a general bond, the instances of a bond `Fin (f x)` of a dependent family of blocks stop
matching after `f x` is unfolded. `IsNormalTensor`, `IsCPSVCanonicalForm` and
`IsMPUCanonicalForm` cannot be restated in TNLean alone: their irreducibility clause is QICLean's
`Kraus.IsIrreducibleFamily`, which is stated for `Fin d → Matrix (Fin D) (Fin D) ℂ`; generalizing
it (with `HasInvariantProj`) in QICLean comes first. T.1c also leaves the 95 consuming
definitions outside these heads, and the lemmas about the restated heads that are still stated at
`Fin d`. T.2a can start for the consumers of the restated heads; T.2c, T.3 and T.4 remain.

All counts were measured by the scripts listed in §6 on TNLean `e8f8dd3202` (5,417 modules
outside `Archive/`) and QICLean `80e0a1782` (1,874 modules). Comments and docstrings are
stripped before counting, so a name mentioned only in prose is not a use.

## 1. The problem

### 1.1 Tensor types

| Type | Definition | Modules | Uses |
|---|---|--:|--:|
| `MPSTensor d D := Fin d → Matrix (Fin D) (Fin D) ℂ` | QICLean `Kraus/Word.lean` | 1,628 (+10 in QICLean) | 10,437 |
| `MPOTensor d D := Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ` | `MPS/Operator/Defs.lean` | 788 | 3,828 |
| `MPSChainTensor d D n := Fin n → MPSTensor d D` (site-dependent, constant bond) | `MPS/Tensor/Chain/Defs.lean` | 63 | 518 |
| `OBCChainTensor d D N` (open chain, bond dimensions `Fin (N+1) → ℕ`, rectangular letters) | `MPS/Tensor/VaryingBond/VaryingBondOBC.lean` | 44 | 442 |
| `VaryingBondChain d D N` (periodic chain, bond dimensions `Fin N → ℕ`) | `MPS/Tensor/VaryingBond/VaryingBondChain.lean` | 20 | 86 |
| `OpenMPSRepresentation`, `IsOpenMPS` (area law; wrap `OBCChainTensor`) | `MPS/Tensor/VaryingBond/OpenMPS.lean` | 134 | 346 |
| `IsometryTree d χ R h n` (tree of isometries `Matrix (Fin n → Fin d) (Fin χ) ℂ`) | `MPS/Preparation/Tree/IsometryTree.lean` | 5 | 46 |
| `TNLean.PEPS.Tensor G d` (graph, bond dimensions `Edge G → ℕ`, vector-valued) | `PEPS/Tensor/Network/Defs.lean` | 113 | 889 |
| `PEPS.Approximation.Tensor q L`, `TwoBlockTensor` | `PEPS/Approximation`, `PEPS/FundamentalTheorem/Injective/TwoInjectiveComparison` | 11 | 59 |
| unnamed `Fin _ → Matrix (Fin _) (Fin _) ℂ` | everywhere | 137 (+100 in QICLean) | 699 (+489) |
| unnamed `Fin _ → Fin _ → Matrix` | everywhere | 51 | 168 |

The QICLean Kraus layer is stated for `Fin d → Matrix (Fin D) (Fin D) ℂ` only: its word
evaluation, spans, injectivity, normality and blocking take `{d D : ℕ}`. It already has a
second word evaluation over an arbitrary bond type, the root-namespace `evalWord` of
`Kraus/MultiBlockWord.lean`, written because the first could not take the bond type
`Σ k, Fin (dim k)`. Only the Kraus map `Kraus.mapLM (K : ι → Matrix n n ℂ)` is general.

### 1.2 Operations defined per type

| Operation | Name(s) | Modules | Uses |
|---|---|--:|--:|
| word evaluation | `Kraus.evalWord` (MPS), `MPOTensor.evalWord` (two words, `0` on unequal lengths), `MPSChainTensor.eval`, `OBCChainTensor.coeff`, `VaryingBondChain.coeff`, `Kraus.rectangularEval`, QICLean root `evalWord` | 495 | 4,594 |
| coefficients | `mpv`, `mpo`, `mpoMatrixEntry` | 327 / 358 / 97 | 1,928 / 2,546 / 145 |
| transfer map | `Kraus.transferMap`, `MPOTensor.transferMap` | 358 | 2,518 |
| conversion | `MPOTensor.toMPSTensor : MPOTensor d D → MPSTensor (d * d) D` | 264 | 1,892 |
| scaled conversion | `MPOTensor.normalizedFlattening` (MPU) | 42 | 288 |
| blocking | see §1.4 | 370 | 3,417 |
| stacking | `mulTensor` (bond `Fin (D₁ * D₂)`), `actTensor` (bond `Fin (D₁ * D₂)`), `tensorProduct` (MPS and MPU), `doubledTensor` | 134 / 64 / 118 / 6 | 712 / 337 / 399 / 66 |
| direct sums | `MPOTensor.directSum` (bond `Fin (D₁ + D₂)`), `blockSum` (MPS and MPO) | 29 / 21 | 108 / 155 |
| reindexing | `reindexPhysical` (5 definitions), `reindexBond` | 77 / 4 | 381 / 13 |
| gauge | `GaugeEquiv`, inline `X * A i * X⁻¹` | 133 | 371 |
| adjoints | `physicalAdjointTensor`, `adjointTensor` | 57 / 6 | 215 / 20 |

### 1.3 The dual-system test

"Two things are a dual system if some lemma has to be proved for each of them."

- The namespace `MPOTensor` holds 3,506 declarations (8,969 with its sub-namespaces). Of
  these, 29 repeat the short name of an `MPSTensor` or `Kraus` declaration because the
  statement had to be proved again for the curried pair alphabet: `evalWord`,
  `evalWord_nil`, `evalWord_cons`, `evalWord_append`, `evalWord_smul`,
  `evalWord_replicate`, `evalWord_reindexPhysical`, `evalWord_tensorProduct`,
  `evalWord_blockSum`, `transferMap`, `transferMap_apply`, `transferMap_pos`,
  `reindexPhysical`, `blockTensor`, `blockTensor_smul`, `blockSum`, `tensorProduct`,
  `tensorProduct_apply`, `IsInjective`, `IsSAL`, `IsZCL`, `mapStar`, `padBond`,
  `physRealize` (with `_mul`, `_spec`, `Left`, `Left_spec`), `siteOperator`.
- 100 declarations carry `toMPSTensor` in their name and 32 carry `normalizedFlattening`:
  they translate between the pair alphabet and `Fin (d * d)`
  (`evalWord_toMPSTensor_ofFn`, `transferMap_eq_toMPSTensor`, `mpo_apply_toMPSTensor`, ...).
- Three chain types (`MPSChainTensor`, 120 declarations; `OBCChainTensor`, 69;
  `VaryingBondChain`, 46) each define their own product along the chain, beside
  `Kraus.rectangularEval` in QICLean.
- Two word evaluations in QICLean (`Kraus.evalWord`, root `evalWord`).

### 1.4 Blockings

Nine declarations are named `blockTensor` (or start with it). Three of them block a tensor;
six transport a structure along a blocking, and are not dual definitions:

| Declaration | What it blocks | Physical basis of the result |
|---|---|---|
| QICLean `Kraus.blockTensor` | MPS tensor | `Fin (blockPhysDim d L)`, decoded by `finFunctionFinEquiv` |
| `MPOTensor.blockTensor` (`MPDO/PhysicalBlocking`) | MPO tensor, ket and bra words separately | `Fin (blockPhysDim d L)` twice |
| `MPSChainTensor.blockTensor` (`Chain/BlockTensor`) | site-dependent chain | `Fin (blockPhysDim d n)` |
| `CPSVCanonicalFormData.blockTensor`, `CPSVCanonicalFormIIData.blockTensor` | canonical-form data | (structure) |
| `SectorDecomposition.blockTensor` | sector decomposition | (structure) |
| `PairCompression.blockTensor` | fusion compression | (structure) |
| `blockTensorCFIIData`, `IsMPUCanonicalFormII.blockTensor` | MPU canonical form II | (structure) |

Four more tensor blockings carry other names: `MPOTensor.blockTwo : MPOTensor d D →
MPOTensor (d * d) D` (98 modules), `chainBlockTensor` and `rectangularBlockTensor`
(`MPS/Preparation`), `flattenedIteratedBlockTensor` (`MPS/Core`). The re-encodings they need
are `blockPhysDim` (228 modules, 2,119 uses), `wordOfBlock`/`decodeBlock`/`decodeBlockEquiv`
(93 modules, 739 uses) and `blockedDoubledIndexEquiv`.

### 1.5 Index arithmetic

In the 2,326 modules that mention a tensor type there are 9,412 occurrences of the
re-encoding vocabulary: `finProdFinEquiv` 3,266, `Fin (a * b)` 2,595, `Fin (blockPhysDim _ _)`
877, `Fin (a + b)` (second summand not a numeral) 655, `modNat` 523, `divNat` 513,
`finSumFinEquiv` 376, `Fin.cast` 308, `Fin (a ^ b)` 155, `finFunctionFinEquiv` 144. By
directory (all modules; directories with at least 40):

| Directory | `finProdFinEquiv` | `divNat`+`modNat` | `Fin (a * b)` | `Fin (a ^ b)` | `Fin (a + b)` | `Fin (blockPhysDim …)` | total |
|---|--:|--:|--:|--:|--:|--:|--:|
| `MPS/MPDO` | 845 | 492 | 767 | 58 | 41 | 51 | 2,497 |
| `MPS/MPU` | 1,032 | 142 | 685 | 0 | 6 | 466 | 2,364 |
| `MPS/Symmetry` | 750 | 73 | 639 | 12 | 289 | 9 | 2,056 |
| `MPS/AreaLaw` | 260 | 14 | 610 | 47 | 44 | 0 | 984 |
| `MPS/Examples` | 136 | 276 | 120 | 0 | 57 | 17 | 694 |
| `MPS/Preparation` | 102 | 1 | 163 | 68 | 60 | 112 | 534 |
| `MPS/ParentHamiltonian` | 25 | 0 | 7 | 0 | 130 | 16 | 249 |
| `MPS/Core` | 112 | 28 | 22 | 0 | 0 | 42 | 221 |
| `MPS/CanonicalForm` | 93 | 4 | 13 | 6 | 9 | 44 | 202 |
| `Algebra` | 28 | 8 | 104 | 0 | 15 | 0 | 192 |
| `MPS/FundamentalTheorem` | 21 | 6 | 20 | 0 | 68 | 4 | 157 |
| `MPS/Periodic` | 0 | 0 | 18 | 0 | 0 | 108 | 127 |
| `PEPS` (top level) | 9 | 10 | 2 | 0 | 1 | 0 | 112 |
| all of TNLean | 3,517 | 1,060 | 3,349 | 200 | 727 | 877 | 10,771 |

Part of this is arithmetic on the sites of a chain (`Fin (N * L)` sites in `N` blocks of
`L`), which is legitimate; the tensor-induced part is the physical `Fin (d * d)`,
`Fin (d ^ L)` and the bond `Fin (D₁ * D₂)`, `Fin (D₁ + D₂)`.

## 2. Design

### 2.1 The type

```lean
universe u v

/-- A matrix product tensor with physical basis `α` and bond basis `β`: one matrix on the
bond space for each physical basis element. As a family of matrices indexed by `α` it is a
finite Kraus family, and every Kraus statement applies to it unchanged. -/
abbrev MPTensor (α : Type u) (β : Type v) : Type (max u v) := α → Matrix β β ℂ

/-- The tensor of local dimension `d` and bond dimension `D`. -/
abbrev MPSTensor (d D : ℕ) := MPTensor (Fin d) (Fin D)

/-- The operator tensor of local dimension `d`: physical basis ket × bra. -/
abbrev MPOTensor (d D : ℕ) := MPTensor (Fin d × Fin d) (Fin D)   -- final form, §2.3
```

The physical and the bond index are arbitrary types, and the letters are square. Square
letters are what a translation-invariant network needs: words multiply, and the periodic
coefficient is a trace. Site-dependent bonds (open chains with varying bond dimension) are a
second object, the chain of §2.7, whose letters are rectangular; a family over sites of
square tensors (`MPSChainTensor`) is its case with constant bases. Isometry trees are a
different network geometry and stay apart (§2.10).

`MPTensor` is an abbreviation, not a structure, for two reasons. The Kraus API applies
without a coercion, and the existing `MPSTensor d D` is then *by definition* the case
`α = Fin d`, `β = Fin D`, so that no statement changes its type at the switch.
`MPSTensor` and `MPOTensor` stay as named special cases after the migration: their facts
follow by unfolding, which is what the dual-system test allows.

### 2.2 What lives where

The tensor *is* an unbundled Kraus family. So the operations that see only a family of
operators on one space stay in QICLean and are generalized there to index types; TNLean does
not define them again. The operations that combine bond spaces, or read the family as a
state or an operator on a chain, are tensor-network notions and live in TNLean.

| QICLean `Kraus` (generalized from `{d D : ℕ}` to `{ι n : Type*}`) | TNLean `MPTensor` |
|---|---|
| `evalWord (K : ι → Matrix n n ℂ) : List ι → Matrix n n ℂ` and its 8 basic lemmas | `mpv`, `mpo` (the periodic vector and operator) |
| `reindexPhysical`, `wordSpan`, `cumulativeSpan`, `IsInjective`, `IsNBlkInjective`, `IsNormal`, `HasEventuallyFullWordSpan` | `act`, `mul` (stacking, bond `β × β'`) |
| `transferMap := mapLM` (already general) | `directSum` (bond `β ⊕ β'`) |
| `block (K : ι → Matrix n n ℂ) (L : ℕ) : (Fin L → ι) → Matrix n n ℂ` | `blockOp` (blocking an operator tensor) |
| `rectangularEval` with bond *types* (§2.7) | `reindexBond`, `gauge` |

The abbreviation `MPSTensor` leaves QICLean (it names a tensor network; its 10 QICLean
modules state their lemmas for the Kraus family type) and is defined in TNLean beside
`MPTensor`, in a new module `TNLean/MPS/Tensor.lean` imported by `MPS/Tensor/Defs`. QICLean's root
`evalWord` of `MultiBlockWord` is deleted: it is `Kraus.evalWord` at the bond type
`Σ k, Fin (dim k)`.

Core signatures (all type-checked in the prototype, §3):

```lean
namespace Kraus   -- QICLean
variable {ι : Type u} {ι' : Type w} {n : Type v} [Fintype n] [DecidableEq n]
def evalWord (K : ι → Matrix n n ℂ) : List ι → Matrix n n ℂ
def reindexPhysical (f : ι' → ι) (K : ι → Matrix n n ℂ) : ι' → Matrix n n ℂ
def wordSpan (K : ι → Matrix n n ℂ) (N : ℕ) : Submodule ℂ (Matrix n n ℂ)
def IsInjective (A : ι → Matrix n n ℂ) : Prop
def IsNBlkInjective (A : ι → Matrix n n ℂ) (N : ℕ) : Prop
def IsNormal (A : ι → Matrix n n ℂ) : Prop
noncomputable abbrev transferMap [Fintype ι] (A : ι → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ := mapLM A
def block (A : ι → Matrix n n ℂ) (L : ℕ) : (Fin L → ι) → Matrix n n ℂ :=
  fun w => evalWord A (List.ofFn w)
end Kraus

namespace MPTensor   -- TNLean
variable {α : Type u} {α' : Type u'} {α'' : Type u''} {β : Type v} {β' : Type v'}
  {γ : Type w} [Fintype β] [DecidableEq β] [Fintype β'] [DecidableEq β']
def mpv (A : MPTensor α β) {N : ℕ} (σ : Fin N → α) : ℂ :=
  trace (Kraus.evalWord A (List.ofFn σ))
def mpo (M : MPTensor (α × α') β) (N : ℕ) : Matrix (Fin N → α) (Fin N → α') ℂ :=
  Matrix.of fun σ τ => mpv M fun k => (σ k, τ k)
def act [Fintype α'] (T : MPTensor (α × α') β) (A : MPTensor α' β') :
    MPTensor α (β × β') := fun i => ∑ j, T (i, j) ⊗ₖ A j
def mul [Fintype α'] (M : MPTensor (α × α') β) (N : MPTensor (α' × α'') β') :
    MPTensor (α × α'') (β × β') := fun p => ∑ j, M (p.1, j) ⊗ₖ N (j, p.2)
def directSum (A : MPTensor α β) (B : MPTensor α β') : MPTensor α (β ⊕ β') :=
  fun i => Matrix.fromBlocks (A i) 0 0 (B i)
def blockOp (M : MPTensor (α × α') β) (L : ℕ) :
    MPTensor ((Fin L → α) × (Fin L → α')) β :=
  Kraus.reindexPhysical (Equiv.arrowProdEquivProdArrow (Fin L) _ _).symm (Kraus.block M L)
def reindexBond [Fintype γ] [DecidableEq γ] (e : β ≃ γ) (A : MPTensor α β) : MPTensor α γ :=
  fun i => Matrix.reindex e e (A i)
def gauge (X : GL β ℂ) (A : MPTensor α β) : MPTensor α β :=
  fun i => (X : Matrix β β ℂ) * A i * ((X⁻¹ : GL β ℂ) : Matrix β β ℂ)
end MPTensor
```

(The prototype states `block` in the namespace `MPTensor`; in the migration it is QICLean's
`Kraus.block`, replacing `Kraus.blockTensor`.)

### 2.3 Operator tensors

An operator tensor is a tensor whose physical basis is a product `α × α'` (ket × bra). Then:

- `toMPSTensor` disappears: the operator tensor *is* a tensor, every MPS statement applies to
  it, and the 100 bridge declarations of §1.3 are deleted or become `rfl`.
- `MPOTensor.evalWord` (two words, `0` on unequal lengths) is replaced by `Kraus.evalWord M`
  on the paired word `List.ofFn fun k => (σ k, τ k)`; `MPOTensor.transferMap` by
  `Kraus.transferMap M`; `mpo` reads the coefficient on the paired configuration.
- Blocking an operator tensor gives the basis `(Fin L → α) × (Fin L → α')`, again an
  operator tensor, so `blockOp` and `blockTwo` (`L = 2`) are one definition.

The final form of `MPOTensor d D` is therefore uncurried, `MPTensor (Fin d × Fin d) (Fin D)`.
The curried form cannot be switched to it by an abbreviation: every application `M i j`
becomes `M (i, j)` (prototype error F2). The script estimates at most 4,565 such
applications in 434 modules (`MPS/MPU` 2,097, `MPS/MPDO` 1,714, `MPS/Symmetry` 642), an upper
bound since it counts every variable bound at the operator type followed by two arguments.
Until that sweep, `MPOTensor` keeps its curried definition and the product-basis tensor is
`↿M` (Mathlib's `Function.uncurry`), which *is* an `MPTensor (Fin d × Fin d) (Fin D)` with
`(↿M) (i, j) = M i j` by `rfl` (prototype F2'). During that period `↿M` replaces
`M.toMPSTensor` and is a notation, not a conversion: no lemma is stated about `↿` itself.

### 2.4 Blocking

Blocking `L` sites changes the physical basis to the words `Fin L → α`; it never passes
through `Fin (d ^ L)`. The facts the prototype proves:

```lean
theorem evalWord_block (A : MPTensor α β) (L : ℕ) (ws : List (Fin L → α)) :
    Kraus.evalWord (block A L) ws = Kraus.evalWord A (ws.flatMap List.ofFn)
theorem evalWord_block_ofFn (A : MPTensor α β) (L N : ℕ) (σ : Fin N → Fin L → α) :
    Kraus.evalWord (block A L) (List.ofFn σ) =
      Kraus.evalWord A (List.ofFn fun k : Fin (N * L) => σ k.divNat k.modNat)
theorem block_block (A : MPTensor α β) (L M : ℕ) (σ : Fin M → Fin L → α) :
    block (block A L) M σ = block A (M * L) (fun k => σ k.divNat k.modNat)
theorem isNBlkInjective_iff_isInjective_block (A : MPTensor α β) (N : ℕ) :
    Kraus.IsNBlkInjective A N ↔ Kraus.IsInjective (block A N) := Iff.rfl
theorem transferMap_block [Fintype α] (A : MPTensor α β) (L : ℕ) :
    Kraus.transferMap (block A L) = Kraus.transferMap A ^ L
theorem blockTensor_eq_reindex_block (A : MPSTensor d D) (L : ℕ) :
    Kraus.blockTensor A L =
      Kraus.reindexPhysical (Kraus.decodeBlockEquiv d L) (block A L) := rfl
```

The remaining arithmetic is on the sites of the chain (`Fin (N * L)`), where it belongs.
The 25-line proof of `isNBlkInjective_iff_blockTensor_isInjective` becomes `Iff.rfl`, and the
existing `transferMap_blockTensor` becomes one reindexing of a sum.

The three tensor blockings and the four others of §1.4 become `Kraus.block` (states,
site-dependent chains through §2.7) and `MPTensor.blockOp` (operators). The six structure
transports keep their role, are renamed `.block`, and change type with their tensor.

### 2.5 Stacking, direct sums, bond reindexing and gauge

`act T A` and `mul M N` have bond basis `β × β'`; `directSum A B` has `β ⊕ β'`. The
existing forms are their reindexings along `finProdFinEquiv` and `finSumFinEquiv`, by
definition:

```lean
theorem actTensor_eq_reindexBond_act (T : MPOTensor d D₁) (A : MPSTensor d D₂) :
    MPOTensor.actTensor T A = reindexBond finProdFinEquiv (act (↿T) A) := rfl
```

and the word formula `evalWord_actTensor` (an induction in the library) becomes a corollary
of `evalWord_act` with three rewrites. Bond reindexing, gauge transformations and every
other unital homomorphism of the bond algebra are one lemma:

```lean
theorem evalWord_map (f : Matrix β β ℂ →+* Matrix γ γ ℂ) (A : MPTensor α β) (w : List α) :
    Kraus.evalWord (fun i => f (A i)) w = f (Kraus.evalWord A w)
```

### 2.6 Transfer maps and Kraus families

The transfer map of a tensor is `Kraus.mapLM` of its letters, for every physical basis, so
`MPOTensor.transferMap M = Kraus.transferMap (↿M)` (a sum over the product basis) and the
transfer map of a blocked tensor is a power. A tensor bundles to QICLean's `KrausFamily β β`
as `⟨α, A⟩`, with `(toKrausFamily A).map = Kraus.transferMap A`; tensor statements do not
need the bundle, and `KrausFamily` lives in `Type` (prototype F4), so the bundle exists only
for bases in `Type`.

### 2.7 Chains with site-dependent bases

One open chain type replaces the products of `MPSChainTensor`, `OBCChainTensor`,
`VaryingBondChain` and `Kraus.rectangularEval`: rectangular letters with a physical basis
per site and a bond basis per bond, as in the Sites layer (`X : V → Type`):

```lean
def Chain.eval : {n : ℕ} → (α : ℕ → Type u) → (β : ℕ → Type v) → [∀ i, Fintype (β i)] →
    [∀ i, DecidableEq (β i)] →
    (∀ i : Fin n, α i.val → Matrix (β i.val) (β (i.val + 1)) ℂ) →
    (∀ i : Fin n, α i.val) → Matrix (β 0) (β n) ℂ
```

`Kraus.rectangularEval b A s = Chain.eval (fun _ => Fin d) (fun i => Fin (b i)) A s` and, for
constant bases, `Chain.eval (fun _ => α) (fun _ => β) (fun _ => A) s =
Kraus.evalWord A (List.ofFn s)`; both are proved in the prototype. The bases are indexed by
`ℕ` rather than `Fin (n + 1)`, as in `rectangularEval`: the recursion shifts the index, and
over `ℕ` the shift needs no transport. Bond dimensions bounded by `D` (the `bondDim_le` fields)
become hypotheses on `Fintype.card (β i)`. A periodic chain with varying bonds closes with an
equivalence `β n ≃ β 0`; this is not prototyped.

### 2.8 PEPS

`TNLean.PEPS.Tensor G d` is kept separate. It is a different object: vector-valued tensors on
an arbitrary graph, contracted by a sum over all bond configurations, with no word structure
and no transfer map; the relation to an MPS is a construction, `cycleTensorOfMPS`, with a
theorem comparing the states. The same generality rule applies to it in follow-on F1: physical
bases `V → Type` and bond bases `Edge G → Type` in place of `Fin d` and
`Fin (bondDim e)` (1,012 uses of `Fin (… bondDim …)` in 118 modules).

### 2.9 Universes and instances

- `MPTensor (α : Type u) (β : Type v) : Type (max u v)`. Blocked bases `Fin L → α`, products
  and sums stay in the same universes. `KrausFamily` and the circuit core are in `Type`; this
  restricts only the bundle of §2.6.
- Definitions take exactly the instances their bodies need: `[Fintype β] [DecidableEq β]`
  for word evaluation (the identity matrix and the product), `[Fintype β]` for `mpv` (the
  trace), `[Fintype α]` (resp. `α'`) for the transfer map and stacking (sums over the
  physical basis). No definition takes `[DecidableEq α]`; proofs obtain it by `classical`
  (the prototype's `evalWord_act`, `transferMap_block`). `reindexPhysical` needs no instance
  and is computable (QICLean marks it `noncomputable` without need).
- General lemmas live in the namespace `MPTensor`. Dot notation unfolds abbreviations, so
  `A.block 2` works for `A : MPSTensor d D`; the converse does not hold: a term whose type is
  `MPTensor (Fin d) (Fin D)` does not see the namespace `MPSTensor` (prototype F3). Lemmas
  are therefore moved to `MPTensor` when they are generalized, never left in `MPSTensor`.

### 2.10 Deliberately not generalized

- Scalars `ℂ`, finite bases, matrices on basis types (as in the architecture document).
- Square letters for translation-invariant tensors; rectangular letters only in chains.
- Sites of a chain stay `Fin N`; the arithmetic `Fin (N * L)` of blocked chains stays.
- Statements whose proofs use the dimension as a number (quantum Wielandt bounds in
  `D`, `d`; Perron–Frobenius arguments indexed by `Fin D`) stay at `Fin d`, `Fin D`; they
  apply to any `MPTensor α β` through `Fintype.equivFin`, as theorems, not as a second type.
- Isometry trees (`IsometryTree`) and staircase preparations: they are circuits of
  isometries `Matrix (Fin n → Fin d) (Fin χ) ℂ`, not matrix product tensors.
- PEPS (§2.8).

## 3. What the prototype established

Four modules, `Proto/A_Abbrev`, `B_Blocking`, `C_Stacking`, `D_Transfer`, elaborate with no
error against the oleans of `worktrees/hot-main` (TNLean `414a18fb88`), and a fifth,
`Proto/E_Errors`, records the failures. The prototype works inside the namespace `Proto`, so
that `MPSTensor`, `Kraus.evalWord`, ... resolve to the generalized declarations while the
library is loaded; library code is pasted character for character to test that it compiles
unchanged.

(a) Abbreviations. `Proto.MPSTensor d D = _root_.MPSTensor d D` and the same for
`MPOTensor` are `rfl`. Over the generalized Kraus API (`{ι n : Type*}`), the following
compile verbatim: from QICLean `evalWord_append`, `evalWord_smul`,
`evalWord_reindexPhysical`, `evalWord_conjTranspose`, `wordSpan`, `IsInjective`,
`IsNBlkInjective`, `blockTensor`, `isNBlkInjective_iff_blockTensor_isInjective`; from TNLean
`MPS/Tensor/Defs` `coeff`, `mpv`, `mpv_zero_length` (`simp` still produces `D`),
`mpv_reindexPhysical`, `GaugeEquiv`, `SameMPV`; from `MPS/Operator/Defs` `toMPSTensor`,
`MPOTensor.evalWord`, `evalWord_toMPSTensor_ofFn`, `transferMap`,
`transferMap_eq_toMPSTensor`; from `MPS/Operator/Product/ActionTensor` `actTensor` and the induction
proof of `evalWord_actTensor`. The one forced textual change is a named argument: the body
of `IsNormal` uses `IsNBlkInjective (d := d) (D := D)`, which must become
`(ι := Fin d) (n := Fin D)` (error F1: "Invalid argument name `d`"). The generic and the old
`Kraus.evalWord` are equal (by induction) but not `rfl`, being different constants; hence the
switch *replaces* QICLean's definition instead of adding one.

(b) Blocking. `evalWord_block`, `evalWord_block_ofFn`, `block_block`, `block_one` proved;
`isNBlkInjective_iff_isInjective_block` is `Iff.rfl`; the existing blocking is
`blockTensor_eq_reindex_block` by `rfl`; `MPOTensor.blockTensor M L i j` equals
`block (↿M) L` on the paired ket and bra words, through
`evalWord_ofFn_eq_uncurry : evalWord M (ofFn σ) (ofFn τ) = Kraus.evalWord (↿M) (ofFn fun k => (σ k, τ k))`.

(c) Stacking. `act`, `mul`, `evalWord_act` (induction, closed by `Fin.consEquiv` and
`Fintype.sum_prod_type`), `mpv_act : mpv (act T A) σ = ∑ τ, mpo T L σ τ * mpv A τ`,
`actTensor_eq_reindexBond_act` by `rfl`, the library's `evalWord_actTensor` as a three-rewrite
corollary, `evalWord_map`, `evalWord_reindexBond`, `evalWord_gauge`, `directSum`,
`evalWord_directSum`, `mpv_directSum`.

(d) Transfer maps. `transferMap_block` (power of the transfer map, general basis),
`mpoTransferMap_eq` (MPO transfer map is the transfer map of `↿M`), the library's
`transferMap_blockTensor` derived by one sum reindexing, `toKrausFamily_map`.

(e) Chains. `Chain.eval` with bases indexed by `ℕ`; `rectangularEval_eq` and `eval_const`.

Errors that shaped the design (`Proto/E_Errors.log`):

| | Attempt | Error | Consequence |
|---|---|---|---|
| F1 | `Kraus.IsNBlkInjective (d := d) (D := D) A N` after generalizing | Invalid argument name `d` | the named-argument sweep of T.1b |
| F2 | `M i j` with `M : MPTensor (Fin d × Fin d) (Fin D)` | argument `i : Fin d` expected `Fin d × Fin d` | the operator type cannot switch by abbreviation; `↿M` in the meantime |
| F3 | `A.SameMPV A` with `A : MPTensor (Fin d) (Fin D)` | invalid field: no `Function.SameMPV` | general lemmas go to the namespace `MPTensor` |
| F4 | `⟨α, A⟩ : KrausFamily β β` with `β : Type u` | expected `Type` | the bundle is restricted to `Type`; tensors are not bundled |
| F5 | `↿M : MPSTensor (d * d) D` | type mismatch | `toMPSTensor` cannot become the identity while its type mentions `Fin (d * d)`; it is removed, not redefined |

Also found during the prototype: `Matrix.kroneckerMap_one_one` leaves the bond type of `1`
undetermined at a general type (`DecidableEq ?m` stuck); `Matrix.one_kronecker_one` is the
form to use. Mathlib has no `trace_fromBlocks`; the direct-sum trace is
`Fintype.sum_sum_type` on the diagonal.

## 4. Migration

Each step builds with no `sorry`. "Rebuild" names what the step recompiles; the steps that
rebuild all of TNLean should share one full build with other pending work.

| Step | Repository | Content | Files | Scriptable | Rebuild |
|---|---|---|--:|---|---|
| T.1a | QICLean | Generalize `Kraus/Word`, `WordSpan`, `Injectivity`, `Transfer` (39 declarations) to `{ι n : Type*}`; add `Kraus.block` with `evalWord_block`, `transferMap_block`, `isNBlkInjective_iff_isInjective_block`; define `blockTensor` from `block`; generalize `rectangularEval` to bond types; delete root `evalWord` of `MultiBlockWord`; remove `MPSTensor` | 4 defining + 7 (50 named arguments) + 10 (`MPSTensor`) + consumers of root `evalWord` | named arguments: yes; definitions: by hand | QICLean downstream of `Kraus/Word` |
| T.1b | TNLean, pin move | `TNLean/MPS/Tensor.lean`: `MPTensor`, `MPSTensor`, `MPOTensor` (curried); named-argument sweep | 1 new + 88 (1,345 named arguments, 1,337 of them on `Kraus.transferMap`) | yes (`tensor_sweep.py named-args`) | all of TNLean (5,417), with the pin move |
| T.1c | TNLean | Restate on `MPTensor α β` the definitions of `MPS/Tensor/Defs` (68 declarations; 20 named arguments in 7 modules) and the definitions that pair-alphabet tensors are fed to: the uses of `toMPSTensor` sit inside 138 distinct application heads, 95 of them TNLean definitions (1,278 uses), the most used `GaugeEquiv` 58, `IsInjective` 50, `SameMPV₂Pos` 49, `evalWord` 43, `IsMPUCanonicalForm` 41, `IsReduction` 40, `IsCPSVCanonicalForm` 33, `mpvOverlap` 24, `transferMap` 21, `mpv` 18, `IsNormal` 17, `IsNormalTensor` 15 (counts from a textual scan, approximate); move them to the namespace `MPTensor` | at most 127 defining modules, by directory | no: a restatement, done only where the proof does not use `Fin` | `MPS/Tensor/Defs` downstream (3,168) |
| T.2a | TNLean | `toMPSTensor` and `normalizedFlattening` retyped to the product basis, `M.toMPSTensor ↦ ↿M`; bridge lemmas deleted | 264 (1,892 uses): 31 scriptable (100 uses), 143 with pair-alphabet arithmetic (1,072), 31 with compound conversions (155), 59 declaring bridges (565) | 31 fully, 174 partly, 59 by hand | `MPDO/Defs` downstream (1,470) |
| T.2a′ | TNLean | `MPOTensor` uncurried; `M i j ↦ M (i, j)`, driven by the elaborator's errors; `MPOTensor.evalWord`, `MPOTensor.transferMap` deleted | 434 (≤ 4,565 applications) | no; error-driven, one directory per pull request | `MPDO/Defs` downstream (1,470) |
| T.2b | TNLean | One blocking: `Kraus.block` and `MPTensor.blockOp`; `blockPhysDim`, `wordOfBlock`, `decodeBlock(Equiv)`, `blockTwo`, `blockedDoubledIndexEquiv` deleted; structure transports renamed `.block` | 370 (3,417 uses): 87 scriptable (527), 149 with `Fin (blockPhysDim …)` arithmetic (1,452), 121 operator blockings after T.2a′ (1,168), 13 defining (270) | 87 fully, 149 partly | `Core/Blocking` downstream (2,283) |
| T.2c | TNLean | Remove the tensor-induced index arithmetic directory by directory (table of §1.5), together with the follow-on F2 restructuring of the same directory | `MPS/MPDO` 2,497, `MPS/MPU` 2,364, `MPS/Symmetry` 2,056, `MPS/Examples` 694, `MPS/Preparation` 534, the rest below 250 | no | per directory |
| T.3 | both | Chains: `MPSChainTensor`, `OBCChainTensor`, `VaryingBondChain` onto `Chain.eval` | 63 + 44 + 20 modules | partly | `Chain/Defs` downstream (1,637) |
| T.4 | TNLean | Delete the temporary names: `toMPSTensor`, `Kraus.blockTensor`, `MPOTensor.blockTensor`, `blockTwo`, the decoding equivalences; `MPSTensor`, `MPOTensor` stay as named special cases | small | yes | small |

Order and sharing. T.1a and T.1b ride one QICLean pin move and its full rebuild. T.1c changes
`MPS/Tensor/Defs` and can share that rebuild when its first part (the definitions of `MPS/Tensor/Defs`) goes
into the same pull request as T.1b; its later parts are per directory. T.2a depends on
T.1c for every consumer it feeds `↿M` to. T.2a′ precedes the operator part of T.2b. T.2c is a
restatement, not a sweep (the method forbids a sweep to replace index arithmetic by basis
types), and is scheduled with the F2 restructuring of `MPS/MPDO`, `MPS/MPU`, `MPS/AreaLaw` so
that each module is rewritten once.

Expected breaks at T.1b, beyond named arguments: `Kraus.evalWord` applied to a `fun` whose
binder type is omitted and cannot be inferred from an expected type (previously `d` was
fixed by the `Fin d` annotation); `rfl` proofs that relied on the two word evaluations being
the same constant (none found in the prototype); `@Kraus.…` explicit applications (none in
TNLean).

## 5. Open decisions

1. **The name of the general type.** `MPTensor α β` (recommended: it says matrix product,
   covers states and operators, and leaves `MPSTensor d D` free as the named case).
   Alternatives: `TNLean.Tensor α β` (collides in reading with `TNLean.PEPS.Tensor`), or a
   final rename of `MPTensor` to `MPSTensor` after the ℕ form is retired (a second sweep;
   not recommended).
2. **Uncurried operator type.** Recommended: uncurry (T.2a′), because blocking and stacking
   of operators are then the general operations at a product basis, and a curried general
   operator type would be a second general type. The alternative, keeping the curried
   `MPOTensor d D` with `↿M` as the tensor, saves the ≤ 4,565 application rewrites but
   leaves the blocked operator tensor outside the type `MPOTensor`.
3. **Ownership of `block`.** Recommended: QICLean `Kraus.block`, since blocking a Kraus family
   into words is channel theory (`transferMap_block` is composition of the channel). The
   alternative keeps it in TNLean as `MPTensor.block`, as in the prototype.
4. **Chain bases indexed by `ℕ` or by `Fin (n + 1)`.** Recommended: `ℕ`, as prototyped and as
   in `rectangularEval`; `Fin (n + 1)` needs a transport at every recursion step.
5. **`KrausFamily` universes.** Recommended: leave `KrausFamily` in `Type`; no tensor statement
   needs the bundle. Revisit only if a circuit statement must hold a tensor as a cell.
6. **Scope of T.1c.** Recommended: restate only what the 95 definitions consuming `toMPSTensor` and
   the blockings need, directory by directory, leaving `Fin`-dependent theory (Wielandt
   bounds) as it is; a wholesale restatement of the 10,445 declarations of `MPSTensor` is not
   justified by any consumer.

## 6. Scripts and prototype

Kept with this proposal (outside the repository until adopted; the sweep script would move to
`scripts/` with T.1b):

- `inventory.py <TNLean root> [<QICLean root>] [--json out]`: the counts of §1.
- `tensor_sweep.py {named-args, to-mps-tensor, mpo-apply, block-tensor} <root>
  [--qiclean …] [--decl-files …] [--apply] [--list]`: dry run by default; `--apply` rewrites
  only the files classified as scriptable.
- `heads_of_to_mps.py <root>`: the consumers of `toMPSTensor` (T.1c scope).
- `rdeps.py <root> <module>…`: number of modules downstream of a module.
- `Proto/A_Abbrev.lean`, `B_Blocking.lean`, `C_Stacking.lean`, `D_Transfer.lean`,
  `E_Errors.lean` (+ `E_Errors.log`) and `check.sh`, which elaborates them against the
  oleans of a built worktree without writing into any `.lake`.
