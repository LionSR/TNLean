/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.NonNormalFixedPoint
import TNLean.MPS.SharedInfra.SectorDecomposition

/-!
# The fixed-point state of a tensor in canonical form

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material) write a tensor
that is not normal as `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` with normal `A_j`
forming a basis of normal tensors (eq. (S2)). After blocking `q` sites they replace each
normal positive part `P_j` by its fixed point `P_{j,∞}` and obtain the state
`∑ⱼ βⱼ |Ω_j⟩` of eq. (S7), with `βⱼ = ∑ₖ μ_{j,k}^N` (eq. (S4)) and
`|Ω_j⟩ = ⊗ₖ |ω_j⟩_{R_k L_{k+1}}`. They then assert the local orthogonality
`⟨ω_j|ω_{j'}⟩ = δ_{jj'}` of the pairs, which makes `W : |j⟩ ↦ |ω_j⟩` an isometry and
gives the GHZ form `|Ω'⟩ = W^{⊗M} |χ_M⟩` of eq. (19).

`TNLean.MPS.Preparation.NonNormalFixedPoint` states these objects for an arbitrary pair
family and takes the local orthogonality as a hypothesis. This file makes one instance of
these objects for a canonical form: the pairs are the fixed-point pairs of the blocks of a
sector decomposition, each embedded in the bond space of the assembled tensor on the
coordinates of one copy of its block, and their local orthogonality is proved. The source
does not make this identification, and the orthogonality proved here follows from the
placement alone.

## Identifications made

The canonical form of eq. (S2) is a `SectorDecomposition`: its basis blocks are the
`A_j`, its copies of block `j` carry the weights `μ_{j,k}`, and its assembled tensor
`SectorDecomposition.toTensor` is the direct sum `⊕_{(j,k)} μ_{j,k} A_j`, which is
`⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_j` up to the order of the bond coordinates. The bond
space of `A` is `ℂ^D` with `D = P.totalDim`. A `SectorDecomposition` carries no normality,
basis-of-normal-tensors, or gauge condition on its blocks.

* **The weights.** `βⱼ` is the sector coefficient `P.coeff N j = ∑ₖ μ_{j,k}^N`, and
  `αⱼ^{(N)}` is `ghzAmplitude` of it.
* **The pairs.** Block `j` carries a matrix `σ_j` on its own bond space `ℂ^{D_j}`, a
  parameter of the construction; the intended instance is the positive definite,
  unit-trace right fixed point of the transfer map of `A_j` in the gauge of eq.
  `eq:Ek_decomp`, but nothing here ties `σ_j` to `A_j`. Its pair is `fixedPointPair σ_j`
  (see `TNLean.MPS.Preparation.FixedPointPairs` for the vectorization convention). The
  only properties used are `σ_j ≥ 0` and `Tr σ_j = 1`.
* **The embedding.** The source calls the pairs vectors of `ℂ^{D²}`, the physical space of
  the positive part `P` of the blocked tensor, which is the bond space `ℂ^D ⊗ ℂ^D` of `A`,
  but does not say where the pair of block `j` sits when `m_j > 1`. Here the pair of
  block `j` is placed on the coordinates of one chosen copy `κ j` of that block
  (`SectorDecomposition.copyCoord`), on both legs. Pairs of distinct blocks then sit on
  disjoint coordinates whatever copies are chosen, so the family is orthonormal; this uses
  neither normality nor the basis-of-normal-tensors property.

**False source (multiplicity):** when some block has multiplicity `m_j ≥ 2`, no product
of pairs, on one copy or spread over the copies, makes the state `V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` of
eq. (S7) approximate `|φ_N⟩`. For `A⁰ = diag(1, 1, 0)`, `A¹ = diag(0, 0, 1)` (two
one-dimensional normal blocks, the first with `m_1 = 2` and weights `(1, 1)`) the target is
proportional to `2|0⋯0⟩ + |1⋯1⟩`, but `V` maps the one-copy pair of the first block to
`|0⋯0⟩/√2` at every site, and the overlap with the target tends to `1/√5` as `M → ∞`,
for every `q`. The block form `⊕ⱼ diag(μ_{j,k}^q) ⊗ P_j` of the positive part asserted
in eq. (S5) fails in this case. Documented in
`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`. The approximating state is
therefore not instantiated with these pairs; `nonNormalApproxState` states it for an
arbitrary family.

Neither the block form of eq. (S5) nor the error estimate is formalized here.

## Main declarations

* `MPSTensor.embedPair` — the pair of a block, pushed into a larger bond space along a
  coordinate map.
* `MPSTensor.inner_embedPair_self`, `MPSTensor.inner_embedPair_eq_zero_of_disjoint` —
  embedding along one injective map preserves overlaps, and embeddings along maps with
  disjoint ranges are orthogonal.
* `MPSTensor.mpv_toTensorFromBlocks_fixedPointTensor` — `⊕ₖ μₖ^q P_∞`, formed in the
  bond space of one block, generates `(∑ₖ μₖ^{qM}) |Ω⟩` on `M` sites.
* `MPSTensor.SectorDecomposition.copyCoord` — the bond coordinates of one copy of a block.
* `MPSTensor.SectorDecomposition.embeddedFixedPointPair` — the fixed-point pairs of the
  blocks, each on one copy of its block.
* `MPSTensor.SectorDecomposition.inner_embeddedFixedPointPair` — local orthogonality
  `⟨ω_j|ω_{j'}⟩ = δ_{jj'}` of these pairs.
* `MPSTensor.SectorDecomposition.canonicalFixedPointState` — `|Ω'⟩` of eq. (19) for the
  canonical form, with its GHZ form and normalization.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, eqs. (19), (S2), (S4), (S5), (S7).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace MPSTensor

variable {d D D' : ℕ}

/-! ## Embedding a pair into a larger bond space -/

/-- The pair `ω ∈ ℂ^{D'} ⊗ ℂ^{D'}` of a block, pushed into the bond space `ℂ^D ⊗ ℂ^D`
along a coordinate map `ι : Fin D' → Fin D` applied to both legs: its coefficient at
`(ι r, ι l)` is `ω (r, l)`, and it vanishes off the image. This is the embedding of the
pairs `|ω_j⟩` of the blocks of arXiv:2307.01696, eq. (S2), into the physical space
`ℂ^{D²}` of the blocked positive part, as used in eq. (S7). -/
def embedPair (ι : Fin D' → Fin D) (ω : Fin D' × Fin D' → ℂ) (p : Fin D × Fin D) : ℂ :=
  ∑ x, if (ι x.1, ι x.2) = p then ω x else 0

/-- Along an injective coordinate map, the embedded pair has the coefficients of the
original pair on the image (arXiv:2307.01696, eq. (S7)). -/
theorem embedPair_apply {ι : Fin D' → Fin D} (hι : Function.Injective ι)
    (ω : Fin D' × Fin D' → ℂ) (a b : Fin D') :
    embedPair ι ω (ι a, ι b) = ω (a, b) := by
  rw [embedPair, Finset.sum_eq_single (a, b)]
  · simp
  · intro x _ hx
    refine ite_eq_right_iff.2 fun h => absurd ?_ hx
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (hι h1) (hι h2)
  · simp

/-- The overlap of two embedded pairs, as a double sum over the coordinates of the
blocks: `⟨ι_* ω|ι'_* ω'⟩ = ∑_{x, y} [ι x = ι' y] conj(ω x) ω' y`. -/
theorem inner_embedPair {D'' : ℕ} (ι : Fin D' → Fin D) (ι' : Fin D'' → Fin D)
    (ω : Fin D' × Fin D' → ℂ) (ω' : Fin D'' × Fin D'' → ℂ) :
    ∑ p, star (embedPair ι ω p) * embedPair ι' ω' p =
      ∑ x : Fin D' × Fin D', ∑ y : Fin D'' × Fin D'',
        if (ι x.1, ι x.2) = (ι' y.1, ι' y.2) then star (ω x) * ω' y else 0 := by
  have hterm : ∀ (x : Fin D' × Fin D') (y : Fin D'' × Fin D''),
      ∑ p : Fin D × Fin D, star (if (ι x.1, ι x.2) = p then ω x else 0) *
          (if (ι' y.1, ι' y.2) = p then ω' y else 0) =
        if (ι x.1, ι x.2) = (ι' y.1, ι' y.2) then star (ω x) * ω' y else 0 := by
    intro x y
    rw [Finset.sum_eq_single (ι x.1, ι x.2)]
    · by_cases h : (ι x.1, ι x.2) = (ι' y.1, ι' y.2)
      · simp [h]
      · simp [h, Ne.symm h]
    · intro p _ hp
      simp [Ne.symm hp]
    · simp
  calc ∑ p, star (embedPair ι ω p) * embedPair ι' ω' p
      = ∑ p : Fin D × Fin D, ∑ x : Fin D' × Fin D', ∑ y : Fin D'' × Fin D'',
          star (if (ι x.1, ι x.2) = p then ω x else 0) *
            (if (ι' y.1, ι' y.2) = p then ω' y else 0) := by
        simp only [embedPair, star_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x : Fin D' × Fin D', ∑ y : Fin D'' × Fin D'', ∑ p : Fin D × Fin D,
          star (if (ι x.1, ι x.2) = p then ω x else 0) *
            (if (ι' y.1, ι' y.2) = p then ω' y else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y

/-- Embedding along one injective coordinate map preserves overlaps:
`⟨ι_* ω|ι_* ω'⟩ = ⟨ω|ω'⟩`. With `ω = ω'` the fixed-point pair of a block, this is the
diagonal part `⟨ω_j|ω_j⟩ = 1` of the local orthogonality in arXiv:2307.01696, the
sentence after eq. (S7). -/
theorem inner_embedPair_self {ι : Fin D' → Fin D} (hι : Function.Injective ι)
    (ω ω' : Fin D' × Fin D' → ℂ) :
    ∑ p, star (embedPair ι ω p) * embedPair ι ω' p = ∑ x, star (ω x) * ω' x := by
  rw [inner_embedPair]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hiff : ∀ y : Fin D' × Fin D',
      ((ι x.1, ι x.2) = (ι y.1, ι y.2)) ↔ x = y := fun y => by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Prod.ext (hι h1) (hι h2)
    · rintro rfl; rfl
  simp_rw [hiff]
  simp

/-- Pairs embedded along coordinate maps with disjoint ranges are orthogonal. This is the
off-diagonal part `⟨ω_j|ω_{j'}⟩ = 0`, `j ≠ j'`, of the local orthogonality in
arXiv:2307.01696, the sentence after eq. (S7), obtained from
`inner_pair_eq_zero_of_disjoint`: the right legs of the two embedded pairs are supported on
the disjoint ranges. -/
theorem inner_embedPair_eq_zero_of_disjoint {D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a b, ι a ≠ ι' b)
    (ω : Fin D' × Fin D' → ℂ) (ω' : Fin D'' × Fin D'' → ℂ) :
    ∑ p, star (embedPair ι ω p) * embedPair ι' ω' p = 0 := by
  classical
  have hsupp : ∀ {n : ℕ} (κ : Fin n → Fin D) (η : Fin n × Fin n → ℂ) (p : Fin D × Fin D),
      p.1 ∉ Finset.univ.image κ → embedPair κ η p = 0 := by
    intro n κ η p hp
    refine Finset.sum_eq_zero fun x _ => ite_eq_right_iff.2 fun hx => absurd ?_ hp
    exact Finset.mem_image.2 ⟨x.1, Finset.mem_univ _, (Prod.mk.inj hx).1⟩
  refine inner_pair_eq_zero_of_disjoint (S := Finset.univ.image ι)
    (S' := Finset.univ.image ι') ?_ (hsupp ι ω) (hsupp ι' ω')
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hx'
  exact h a b hb.symm

/-- The product of embedded pairs, read on configurations inside the image, is the
product of the original pairs: embedding the pair of a block embeds its fixed-point state
`|Ω_j⟩ = ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` (arXiv:2307.01696, eq. (S7)). -/
theorem pairProductState_embedPair {M : ℕ} {ι : Fin D' → Fin D} (hι : Function.Injective ι)
    (ω : Fin D' × Fin D' → ℂ) (c : Fin M → Fin D' × Fin D') :
    pairProductState (embedPair ι ω) (fun k => (ι (c k).1, ι (c k).2)) =
      pairProductState ω c := by
  simp only [pairProductState, embedPair_apply hι]

/-! ## The multiplicity of a block -/

/-- The tensor `⊕ₖ μₖ^q P_∞`, formed in the bond space `ℂ^D ⊗ ℂ^D` of one block from the
fixed-point tensor `P_∞` of a matrix `σ`, generates on `M ≥ 1` blocked sites the state
`(∑ₖ μₖ^{qM}) |Ω⟩`, with `|Ω⟩` the product of the pairs of `σ` in that same bond space.
This is the replacement of `P_j` by `P_{j,∞}` in the block
`diag(μ_{j,1}^q, …, μ_{j,m_j}^q) ⊗ P_j` of arXiv:2307.01696, eq. (S5), read in the block's
own bond space; it is not a statement about the embedded pairs of the assembled tensor, and
it does not show that the multiplicities enter eq. (S7) only through `βⱼ`, which fails when
some `m_j ≥ 2` (`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`). -/
theorem mpv_toTensorFromBlocks_fixedPointTensor {m : ℕ} (μ : Fin m → ℂ)
    (σ : Matrix (Fin D) (Fin D) ℂ) (q : ℕ) {M : ℕ} [NeZero M] (τ : Fin M → Fin (D * D)) :
    mpv (toTensorFromBlocks (dim := fun _ : Fin m => D) (fun k => μ k ^ q)
        (fun _ => fixedPointTensor σ)) τ =
      (∑ k, μ k ^ (q * M)) *
        pairProductState (fixedPointPair σ) (fun k => finProdFinEquiv.symm (τ k)) := by
  rw [mpv_toTensorFromBlocks_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mpv_fixedPointTensor, smul_eq_mul, pow_mul]

/-! ## The pairs of a canonical form -/

namespace SectorDecomposition

/-- The bond coordinate, in the assembled tensor `P.toTensor`, of the coordinate `a` of the
copy `k` of the block `j`: the position of the block `μ_{j,k} A_j` in the direct sum
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` of arXiv:2307.01696, eq. (S2)
(`toTensor_copyCoord`). -/
noncomputable def copyCoord (P : SectorDecomposition d) (j : Fin P.basisCount)
    (k : Fin (P.copies j)) (a : Fin (P.basisDim j)) : Fin P.totalDim :=
  finSigmaFinEquiv ⟨P.flatIndexEquiv ⟨j, k⟩, Fin.cast (P.flatDim_flatIndexEquiv ⟨j, k⟩).symm a⟩

/-- The coordinates of one copy of one block are distinct. -/
theorem copyCoord_injective (P : SectorDecomposition d) (j : Fin P.basisCount)
    (k : Fin (P.copies j)) : Function.Injective (P.copyCoord j k) := by
  intro a b h
  have h' := Sigma.mk.inj_iff.1 (finSigmaFinEquiv.injective h)
  exact Fin.cast_injective _ (eq_of_heq h'.2)

/-- Coordinates of distinct blocks are distinct, whatever copies are used: the blocks of
arXiv:2307.01696, eq. (S2), have orthogonal supports in the bond space. -/
theorem copyCoord_ne_of_ne (P : SectorDecomposition d) {j j' : Fin P.basisCount}
    (hj : j ≠ j') (k : Fin (P.copies j)) (k' : Fin (P.copies j'))
    (a : Fin (P.basisDim j)) (a' : Fin (P.basisDim j')) :
    P.copyCoord j k a ≠ P.copyCoord j' k' a' := by
  intro h
  have h1 := (Sigma.mk.inj_iff.1 (finSigmaFinEquiv.injective h)).1
  exact hj (congrArg Sigma.fst (P.flatIndexEquiv.injective h1))

/-- The assembled tensor restricted to the coordinates of the copy `k` of the block `j` is
the weighted block `μ_{j,k} A_j`: `copyCoord` is the position of that block in
arXiv:2307.01696, eq. (S2). -/
theorem toTensor_copyCoord (P : SectorDecomposition d) (i : Fin d) (j : Fin P.basisCount)
    (k : Fin (P.copies j)) (a b : Fin (P.basisDim j)) :
    P.toTensor i (P.copyCoord j k a) (P.copyCoord j k b) = P.weight j k * P.basis j i a b := by
  have key : ∀ (s : Fin P.totalCopies) (jk : (j : Fin P.basisCount) × Fin (P.copies j))
      (hs : P.flatIndexEquiv.symm s = jk) (h : P.basisDim jk.1 = P.flatDim s)
      (a b : Fin (P.basisDim jk.1)),
      P.toTensor i (finSigmaFinEquiv ⟨s, Fin.cast h a⟩) (finSigmaFinEquiv ⟨s, Fin.cast h b⟩) =
        P.weight jk.1 jk.2 * P.basis jk.1 i a b := by
    intro s jk hs h a b
    subst hs
    simp [toTensor, toTensorFromBlocks, flatWeight, flatBasis, Matrix.reindex_apply,
      Matrix.blockDiagonal'_apply_eq]
    rfl
  exact key _ ⟨j, k⟩ (P.flatIndexEquiv.symm_apply_apply _) _ a b

/-- The fixed-point pair `|ω_j⟩` of the block `j` of a canonical form (arXiv:2307.01696,
eq. (S2)), embedded in the bond space `ℂ^D ⊗ ℂ^D` of the assembled tensor on the
coordinates of the copy `κ j` of that block. The matrix `σ j` is a parameter; the intended
instance is the right fixed point of the block `A_j` in the gauge of eq. `eq:Ek_decomp`.
The source does not say where the pair sits when the block has several copies; the copy
is the parameter `κ`. Every choice gives an orthonormal family
(`inner_embeddedFixedPointPair`), but when some block has several copies no choice makes
eq. (S7) approximate the state (`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`). -/
noncomputable def embeddedFixedPointPair (P : SectorDecomposition d)
    (σ : (j : Fin P.basisCount) → Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (j : Fin P.basisCount) :
    Fin P.totalDim × Fin P.totalDim → ℂ :=
  embedPair (P.copyCoord j (κ j)) (fixedPointPair (σ j))

/-- Local orthogonality `⟨ω_j|ω_{j'}⟩ = δ_{jj'}` of the embedded fixed-point pairs of a
canonical form, the property asserted in arXiv:2307.01696 after eq. (S7): distinct blocks
occupy disjoint bond coordinates, and each pair has norm `Tr σ_j = 1`. The proof uses only
the placement and `σ_j ≥ 0`, `Tr σ_j = 1`, not normality or the basis-of-normal-tensors
property the source invokes. -/
theorem inner_embeddedFixedPointPair (P : SectorDecomposition d)
    {σ : (j : Fin P.basisCount) → Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (j j' : Fin P.basisCount) :
    ∑ p, star (P.embeddedFixedPointPair σ κ j p) * P.embeddedFixedPointPair σ κ j' p =
      if j = j' then 1 else 0 := by
  unfold embeddedFixedPointPair
  split_ifs with h
  · subst h
    rw [inner_embedPair_self (P.copyCoord_injective j (κ j)), fixedPointPair_norm_sq (hσ j),
      htr j]
  · exact inner_embedPair_eq_zero_of_disjoint
      (fun a a' => P.copyCoord_ne_of_ne h (κ j) (κ j') a a') _ _

/-- The map `W : |j⟩ ↦ |ω_j⟩` of arXiv:2307.01696, the paragraph after eq. (19), formed
from the embedded fixed-point pairs of a canonical form, is an isometry. -/
theorem isIsometry_pairIsometry_embeddedFixedPointPair (P : SectorDecomposition d)
    {σ : (j : Fin P.basisCount) → Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) :
    (pairIsometry (P.embeddedFixedPointPair σ κ)).IsIsometry :=
  isIsometry_pairIsometry (P.inner_embeddedFixedPointPair hσ htr κ)

/-! ## The fixed-point state of a canonical form -/

/-- The fixed-point state `|Ω'⟩ = ∑ⱼ αⱼ^{(N)} ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` of arXiv:2307.01696,
eq. (19), for a canonical form of eq. (S2): the pairs are the embedded fixed-point pairs of
the blocks, and the coefficients are `αⱼ^{(N)} = βⱼ / (∑ₗ |βₗ|²)^{1/2}` with
`βⱼ = ∑ₖ μ_{j,k}^N` (the display following eq. (S7)), on a ring of `M` blocked sites. -/
noncomputable def canonicalFixedPointState (P : SectorDecomposition d)
    (σ : (j : Fin P.basisCount) → Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (N M : ℕ) :
    (Fin M → Fin P.totalDim × Fin P.totalDim) → ℂ :=
  nonNormalFixedPointState (ghzAmplitude (P.coeff N)) (P.embeddedFixedPointPair σ κ)

/-- The GHZ form of the fixed-point state of a canonical form, arXiv:2307.01696, the
paragraph after eq. (19): `|Ω'⟩ = W^{⊗M} |χ_M⟩` in the bond coordinates `R_k L_{k+1}`, with
`W : |j⟩ ↦ |ω_j⟩` an isometry (`isIsometry_pairIsometry_embeddedFixedPointPair`). -/
theorem canonicalFixedPointState_eq_tensorPower_mulVec_ghzState (P : SectorDecomposition d)
    (σ : (j : Fin P.basisCount) → Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (N M : ℕ)
    (p : Fin M → Fin P.totalDim × Fin P.totalDim) :
    P.canonicalFixedPointState σ κ N M ((bondRegrouping M P.totalDim).symm p) =
      (Matrix.tensorPower M (pairIsometry (P.embeddedFixedPointPair σ κ)) *ᵥ
        ghzState (ghzAmplitude (P.coeff N))) p :=
  nonNormalFixedPointState_eq_tensorPower_mulVec_ghzState _ _ p

/-- The fixed-point state of a canonical form is normalized, `⟨Ω'|Ω'⟩ = 1`, on every ring
of `M ≥ 1` blocked sites at a length `N` where some weight `βₗ` is nonzero
(arXiv:2307.01696, eq. (19) and the display following eq. (S7), whose denominator is
nonzero exactly then). -/
theorem canonicalFixedPointState_norm_sq (P : SectorDecomposition d)
    {σ : (j : Fin P.basisCount) → Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) {N M : ℕ} (hM : M ≠ 0)
    (hβ : P.coeff N ≠ 0) :
    ∑ c : Fin M → Fin P.totalDim × Fin P.totalDim,
      star (P.canonicalFixedPointState σ κ N M c) * P.canonicalFixedPointState σ κ N M c =
        1 :=
  nonNormalFixedPointState_norm_sq hM hβ (P.inner_embeddedFixedPointPair hσ htr κ)

end SectorDecomposition

end MPSTensor
