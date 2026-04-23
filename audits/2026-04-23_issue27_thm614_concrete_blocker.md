# 2026-04-23 — Issue #27 audit: Cor. 6.6 support-corner path and Thm. 6.14 concrete blocker

## Scope

I worked in the isolated worktree `.worktrees/issue-27-cor66` on branch
`feat/27-cor66-corner-algebra`, after reading:

- `CLAUDE.md`
- `docs/PROOF_INTEGRITY.md`
- `docs/style.md`
- `docs/blueprint_style_guide.md`
- issue #27
- the current fixed-point / stationary-support / cyclic-decomposition files
- the Chapter 6 index and blueprint section

I targeted **Wolf Cor. 6.6** first, as requested.

## Main finding for Cor. 6.6

The earlier blocker description

> "`cornerSubmodule Q` is only a `Submodule`; we still need to package the corner as a unital `*`-algebra with unit `Q`"

is **partly outdated**.

### What Mathlib already provides

`Mathlib/RingTheory/Idempotents.lean` already defines the corner type

- `IsIdempotentElem.Corner (e := P) hP`

for an idempotent `P`, together with the ring structure whose unit is `P`.
More precisely, for an idempotent `P` it gives:

- the carrier `Set.range (P * · * P)`;
- `Semiring` / `Ring` instances on the corner;
- the correct unit `1 = P`.

So the missing step is **not** to build the corner ring from nothing.

### What is still actually missing

For the matrix corner needed in Cor. 6.6, the missing pieces are:

1. **Complex-linear packaging on the corner type**
   - no out-of-the-box `SMul ℂ`, `Module ℂ`, or `Algebra ℂ` instance on
     `IsIdempotentElem.Corner (e := P) hP.2`;
2. **Star packaging on the corner type**
   - no out-of-the-box `Star`, `StarRing`, or `StarModule ℂ` instance,
     even when `P` is self-adjoint;
3. **Bridge to the existing API**
   - the repository-side corner object is still `cornerSubmodule P`, so one still
     needs a clean equivalence between
     `cornerSubmodule P = {X | P * X * P = X}`
     and Mathlib's `IsIdempotentElem.Corner` carrier;
4. **Faithfulness of the compressed fixed point**
   - after compressing to the support, the resulting fixed point on the smaller
     matrix algebra must be shown `PosDef`, not merely `PosSemidef`.

That last point is the real proof bottleneck preventing a short derivation of
Cor. 6.6 from the existing `fixedPointsStarSubalgebra` /
`adjointFixedPointsStarSubalgebra` machinery.

## Expected proof route for Cor. 6.6

Let `ρ ≥ 0` satisfy `map K ρ = ρ`, and let
`P := supportProj ρ`.
Then:

1. `lowerZero_of_posSemidef_fixedPoint` gives
   `∀ i, (1 - P) * K_i * P = 0`.
2. Hence the supported Kraus family
   `A_i := K_i * P`
   lands in the corner and satisfies
   `∑ A_i† A_i = P`.
3. The existing compression infrastructure
   (`cornerCompressionExpand`, `cornerCompressionInvFun`,
   `cornerCompressionLinearEquiv`, or the stronger
   `exists_compressedTensor_of_supported_projection`) should then produce a
   smaller Kraus family `C` on `M_n(ℂ)` with
   `∑ C_i† C_i = 1`.
4. The compressed fixed point
   `ρ_c`
   should be the top-left block of `U† ρ U` on the support sector, hence
   positive definite.
5. Apply `adjointFixedPointsStarSubalgebra` to `C` and transport the result back
   to the corner.

### Remaining missing lemma for step 4

The clean missing lemma is essentially:

> if `ρ.PosSemidef` and `P = supportProj ρ`, then the compression of `ρ` to the
> support sector is `PosDef`.

A promising proof route is:

- publicize the archived kernel lemma
  `supportProj_mulVec_eq_zero_of_mulVec_eq_zero`
  from `TNLean/Archive/BlockingPeriodicityCFII2.lean`;
- combine it with
  - `PosSemidef.submatrix`, and
  - either `PosSemidef.posDef_iff_isUnit` or a direct kernel-vector contradiction.

In other words, **Cor. 6.6 now looks close**, but it still needs one faithful-
compression lemma plus the corner `ℂ`/`*`-algebra instances.

## Thm. 6.14 concrete-realization blocker

The harder remaining part of Wolf Thm. 6.14 is still exactly the one already
noted in issue #27 and in the earlier Chapter 6 fixed-point follow-up work:

- the current file `TNLean/Channel/FixedPoint/WedderburnDecomp.lean` gives
  semisimplicity and an abstract product decomposition;
- `IsWedderburnBlockDecomp` records only
  - the number of simple blocks,
  - block dimensions,
  - multiplicities,
  - an ambient-dimension bound, and
  - an `AlgEquiv` to a product of matrix algebras.

What is still missing for the full Wolf statement is the **concrete ambient
realization**

\[
\operatorname{Fix}(T^*) = U \Bigl(0 \oplus \bigoplus_k M_{d_k}(\mathbb C) \otimes 1_{m_k}\Bigr) U^\dagger,
\]

and then the density-block refinement

\[
\operatorname{Fix}(T) = U \Bigl(0 \oplus \bigoplus_k M_{d_k}(\mathbb C) \otimes \rho_k\Bigr) U^\dagger.
\]

### Why the present infrastructure stops short

Mathlib currently gives the **abstract** Wedderburn--Artin decomposition of a
finite-dimensional semisimple algebra over `ℂ`, but not the additional data
needed here:

1. a `StarAlgEquiv` / C\*-compatible version of the decomposition;
2. a proof that the algebra can be realized by **unitary conjugation** inside the
   ambient matrix algebra;
3. the multiplicity-space decomposition giving the `⊗ 1_{m_k}` factors;
4. the final transport from the adjoint-fixed algebra to the Schrödinger fixed
   space with density blocks `ρ_k`.

So the honest next theorem for Thm. 6.14 is not another abstract algebra
statement. It is a **representation-theoretic realization theorem** for finite-
dimensional `*`-subalgebras of `M_D(ℂ)`.

## Recommendation

If issue #27 is continued immediately, the best next slice is still:

1. expose a public kernel/support lemma for `supportProj`,
2. add `ℂ`-module + `*`-ring instances on the corner type
   `IsIdempotentElem.Corner`,
3. prove the compressed support fixed point is `PosDef`,
4. then finish Cor. 6.6.

Only after that is it worth returning to the full concrete/unitary part of
Thm. 6.14.
