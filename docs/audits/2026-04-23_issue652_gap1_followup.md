# Issue #652 follow-up audit — Gap §1 / general BNT sector endpoint

Date: 2026-04-23
Branch: `feat/652-bnt-grouping-v2`
Supersedes: `audits/2026-04-21_issue652_gap1_blocker.md`

## Executive summary

The April 21 audit correctly showed that the original Step 1 request is false:
whole-tensor `SameMPV₂` does **not** imply the same-side hypothesis
`hMPVEq : ‖μ j‖ = ‖μ k‖ → SameMPV₂ (blocks j) (blocks k)`.

After re-reading the current Lean endpoint and the paper proofs, the sharper
conclusion is:

1. `exists_bnt_grouping` is only a **norm-class collapse** theorem. It is not
   the full basis-of-normal-tensors construction from
   [CPSV17, Proposition `prop:char-BNT`] /
   [CPSV21, Proposition `prop:char-BNT`].
2. The after-blocking endpoint must be stated at the level of **general BNT
   sector decompositions**, not strict `IsCanonicalFormBNT` families. The
   paper-level decomposition has coefficients
   `c_j(N) = ∑ q, μ_{j,q} ^ N`, not one geometric weight per basis block.
3. The genuinely missing formal content is therefore a two-step sector
   endpoint:
   (a) a one-sided BNT-sector construction from arbitrary TP-primitive-
   irreducible blocks, and
   (b) a heterogeneous equal-case comparison theorem for two such sector
   decompositions.

This is sharper than the April 21 audit: the missing theorem family is not only
"compare two sector decompositions once they exist". We also still lack the
paper's **general** one-sided BNT construction that allows several distinct BNT
basis tensors to occur at the same coefficient modulus.

## Existing Lean theorems already on `main`

The current library already provides all of the following.

### Reduction / blocking infrastructure

- `exists_tp_primitive_blockDecomp_after_blocking`
  (`TNLean/MPS/CanonicalForm/Assembly/TPPrimitiveReduction.lean`)
- `bilateral_commonPeriod_blocking_tp_primitive_normal`
  (`TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`)
- `sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks`
  (`TNLean/MPS/Core/BlockingInfrastructure.lean`)
- `isPrimitive_transferMap_blockTensor_of_dvd`
- `isIrreducibleTensor_blockTensor_of_tp_primitive_irr`
- `isNormal_of_tp_primitive_irreducible`

So the common-period arithmetic is **not** the blocker anymore.

### Special-case same-side grouping

- `exists_bnt_grouping`
  (`TNLean/MPS/CanonicalForm/BNTGrouping.lean`)
- `exists_bnt_grouping_of_gaugePhaseEquiv`
- `exists_sectorDecomp_of_tp_primitive_irr_blocks`
  (`TNLean/MPS/CanonicalForm/EqualNormBridge.lean`)

These theorems cover only the special case where same-side equal-norm blocks are
already known to collapse onto one basis tensor.

### Current equal-case endpoints

- `fundamentalTheorem_equalMPV_CFBNT_hetero`
  (`TNLean/MPS/FundamentalTheorem/Full.lean`)
- `fundamentalTheorem_equalMPV_sectorDecomposition`
  (`TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean`)

The first theorem is for **strict** CF-BNT families with one weight per block.
The second theorem is for **sector decompositions over a shared basis**.
Neither theorem covers the missing paper-level endpoint by itself.

## New clarification beyond the April 21 audit

### 1. `exists_bnt_grouping` is not the paper's full BNT construction

The theorem `exists_bnt_grouping` groups by **weight norm classes** and outputs a
sector decomposition with one basis tensor per norm class and strictly
decreasing representative norms.

That is a useful special case, but it is stronger than the paper's general BNT
shape. In [CPSV17, Eq. `eq:II_ABasicTensors`] and [CPSV21, Eq. `eq:II_ABasicTensors`],
a tensor in canonical form is written as

$$
  A^i = \bigoplus_{j=1}^g \bigoplus_{q=1}^{r_j}
    \mu_{j,q} X_{j,q} A_j^i X_{j,q}^{-1},
  \qquad
  |V^{(N)}(A)\rangle = \sum_{j=1}^g
    \left(\sum_{q=1}^{r_j} \mu_{j,q}^N\right)
    |V^{(N)}(A_j)\rangle.
$$

Nothing in that formula forbids two **different** basis tensors `A_j`, `A_k`
from having coefficient multisets with the same modulus. The current Lean
special case forbids that by construction.

The scalar counterexample from the April 21 audit shows exactly why this matters:

- `A₀(0) = 1`, `A₀(1) = 0`
- `A₁(0) = 0`, `A₁(1) = 1`
- `μ₀ = μ₁ = 1`

These are TP, primitive, irreducible, same norm, and not `SameMPV₂`. Any
correct one-sided BNT construction must allow them to survive as **two distinct
basis tensors at the same modulus**. Therefore the current theorem shape
`equal norm class = one basis tensor` cannot be the general endpoint.

### 2. The shared-basis sector theorem covers only the last paper step

`fundamentalTheorem_equalMPV_sectorDecomposition` proves equality of sector
weight multisets **once the two sides already share the same basis**.

This matches only the last part of the paper proof of the equal case
([CPSV17, proof of Corollary `II_cor2`, lines 1184–1192] /
[CPSV21, Corollary `II_cor2`, lines 1896–1900]): after the BNT basis tensors are
already matched, compare the power sums `∑_q μ_{j,q}^N` and recover the weight
multisets.

What is still missing is the earlier heterogeneous step:

- from `SameMPV₂` of the **total** sector tensors,
- recover the BNT basis matching across the two sides,
- and only then compare the sector coefficients on the matched basis.

## Paper-level theorem family that is actually missing

The paper proof decomposes into three layers.

### Layer A. One-sided BNT construction

Paper source:

- [CPSV17, Proposition `prop:char-BNT`, lines 1135–1148]
- [CPSV21, Proposition `prop:char-BNT`, lines 1852–1861]

This is the appendix construction of a basis of normal tensors by choosing a
maximal subset with decaying mixed overlaps and then expressing every remaining
block by gauge phase relative to one representative.

A Lean theorem close to the paper shape should look like:

```lean
/-- Suggested helper predicate packaging the paper-level BNT sector data. -/
structure HasBNTSectorData (P : SectorDecomposition d) : Prop where
  basis_ncf :
    IsNormalCanonicalForm
      (fun j : Fin P.basisCount =>
        P.weight j ⟨0, P.copies_pos j⟩)
      P.basis
  basis_blocks : BlocksNotGaugePhaseEquiv (d := d) P.basis
  class_const_norm :
    ∀ j (q : Fin (P.copies j)),
      ‖P.weight j q‖ = ‖P.weight j ⟨0, P.copies_pos j⟩‖
```

```lean
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, IsPrimitive (transferMap (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P
```

This theorem would **replace** the current attempt to strengthen
`exists_bnt_grouping`. The point is not to derive `hMPVEq`; the point is to
formalize the paper's general BNT construction, which does not require that all
same-modulus blocks on one side coincide.

### Layer B. Heterogeneous equal-case comparison for BNT sector decompositions

Paper source:

- [CPSV17, Theorem `thm1`, lines 1167–1183]
- [CPSV21, Theorem `thm1`, lines 1891–1893]
- [CPSV17, Corollary `II_cor2`, proof lines 1184–1192]
- [CPSV21, Corollary `II_cor2`, lines 1896–1900]

A Lean theorem close to the needed endpoint should look like:

```lean
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero
    (P Q : SectorDecomposition d)
    (hP : HasBNTSectorData (d := d) P)
    (hQ : HasBNTSectorData (d := d) Q)
    (hSame : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ _h : P.basisCount = Q.basisCount,
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
        ∃ hCopies : ∀ j : Fin P.basisCount,
          P.copies j = Q.copies (perm j),
          ∀ j : Fin P.basisCount,
            ∃ hdim : P.basisDim j = Q.basisDim (perm j),
              ∃ ζ : ℂ, ζ ≠ 0 ∧ ‖ζ‖ = 1 ∧
                GaugePhaseEquiv (d := d)
                  (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
                  (Q.basis (perm j)) ∧
                Finset.univ.val.map (P.weight j) =
                  Finset.univ.val.map
                    (fun q =>
                      ζ * Q.weight (perm j)
                        (Fin.cast (hCopies j) q))
```

This is the actual missing bridge between the two current endpoints:

- it starts from two **different** BNT sector decompositions,
- first matches the basis tensors up to permutation and gauge phase,
- then absorbs the phases into the sector weights,
- and finally compares the sector-weight multisets.

The existing theorem
`fundamentalTheorem_equalMPV_sectorDecomposition` would then become the
**shared-basis subroutine** for the final weight-multiset line after transporting
`Q` along the matched permutation and absorbed phases.

### Layer C. After-blocking assembly theorem

Once Layers A and B exist, the structural after-blocking theorem can finally be
retargeted honestly:

```lean
theorem fundamentalTheorem_after_blocking_sector
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ p : ℕ, 0 < p ∧
      ∃ P : SectorDecomposition (blockPhysDim d p),
      ∃ Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
        SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
        HasBNTSectorData (d := blockPhysDim d p) P ∧
        HasBNTSectorData (d := blockPhysDim d p) Q ∧
        -- plus the permutation / phase / sector-weight conclusion of Layer B
        True
```

The placeholder `True` above is exactly the Layer-B conclusion instantiated at
physical dimension `blockPhysDim d p`. The common-period blocking itself is
already formalized on `main`; the missing content is the sector endpoint.

## Why the current code stops exactly before these theorems

- `exists_bnt_grouping` and
  `exists_sectorDecomp_of_tp_primitive_irr_blocks` are special-case tools for
  already-collapsible norm classes.
- `fundamentalTheorem_equalMPV_CFBNT_hetero` is a theorem for strict
  `toTensorFromBlocks μ basis` data, not for sector coefficients
  `c_j(N) = ∑_q μ_{j,q}^N`.
- `fundamentalTheorem_equalMPV_sectorDecomposition` compares sector weights only
  after a common basis is already fixed.
- The coefficient-convergence route from
  `fundamentalTheorem_proportionalMPV_CFBNT` still does not apply to general
  sector coefficients, exactly as documented in
  `TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean:290-295`.

## Recommended next split

1. **General BNT construction issue**:
   formalize Proposition `prop:char-BNT` for TP-primitive-irreducible block
   families and land `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`.
2. **Heterogeneous sector comparison issue**:
   formalize the basis-matching + phase-absorption theorem
   `fundamentalTheorem_equalMPV_sectorDecomposition_hetero`.
3. **Assembly issue**:
   retarget `fundamentalTheorem_after_blocking_structural` at the sector
   endpoint, then tighten the `\notready` blueprint remark in
   `blueprint/src/chapter/ch11_assembly.tex`.

## Bottom line

Issue #652 still cannot be closed by trying to discharge `hMPVEq` inside the
current `exists_bnt_grouping` statement. The correct endpoint is a **general BNT
sector endpoint**, matching the paper's Appendix-A construction and the theorem /
corollary pair in §IV of the review article.
