/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ProjectiveRepresentation
import TNLean.MPS.Core.ReductionBlocking
import TNLean.MPS.Core.ReductionExistence
import TNLean.MPS.MPU.GroupRepresentation

/-!
# Common blocking for the pair reductions of an MPU representation

For an MPU representation $\{\mathcal U_g\}_{g\in G}$ by simple injective
tensors, the product tensor $\mathcal U_g\mathcal U_h$ and the tensor
$\mathcal U_{gh}$ generate the same positive-length matrix product vectors, so
each pair $(g,h)$ admits a rectangular reduction $(V_{g,h},W_{g,h})$ from
$\mathcal U_g\mathcal U_h$ to $\mathcal U_{gh}$.  This file selects one such
reduction for every pair, records its MGSC18 nilpotency length
$N_0(g,h)$, and chooses one positive common blocking length $L$ with
$N_0(g,h)\leq L+1$ for every pair.  After blocking every tensor by $L$
sites, the selected reductions are reductions of the blocked representation,
and one blocked exterior site suffices for the exterior identity of every
pair:
$$
  B^{\mathbf p}W_{g,h}A^{\mathbf c}V_{g,h}B^{\mathbf q}
    =B^{\mathbf p\mathbf c\mathbf q},
  \qquad |\mathbf p|,|\mathbf q|\geq1,\ \mathbf c\neq\emptyset,
$$
with $A=\mathcal U_{gh}^{[L]}$ and $B=\mathcal U_g^{[L]}\mathcal U_h^{[L]}$.

**Local fix (arXiv:2502.20257, `main.tex` line 1498):** the source says that
the nilpotency length can always be reduced to one by blocking.  The
one-site exterior identity above is the content of that sentence used here.
The blocked residual letters need not vanish, and the blocked nilpotency
length of MGSC18 Definition 8 need not equal one; see
`docs/paper-gaps/mgsc18_nilpotency_length_one_terminology.tex`.

Fusion tensors and the associator are not defined here.

## Main definitions

* `MPOTensor.GroupFamily.productTensor`, `MPOTensor.GroupFamily.targetTensor`:
  the vectorized tensors $\mathcal U_g\mathcal U_h$ and $\mathcal U_{gh}$.
* `MPOTensor.GroupFamily.ReductionFamily`: one selected reduction for every
  pair.
* `MPOTensor.GroupFamily.ReductionFamily.nilpotencyLength`: the MGSC18
  nilpotency length of the selected reduction of a pair.
* `MPOTensor.GroupFamily.ReductionFamily.commonBufferLength`: one positive
  length `L` with `N₀(g,h) ≤ L + 1` for every pair.
* `MPOTensor.GroupFamily.ReductionFamily.block`: the selected reductions as
  reductions of the commonly blocked representation.
* `MPOTensor.GroupFamily.ReductionFamily.smul`: the reciprocal scalar
  rescaling of a family of selected reductions by a scalar $2$-cochain.

## Main results

* `MPOTensor.GroupFamily.IsRepresentation.nonempty_reductionFamily`: a
  representation admits a selected reduction for every pair.
* `MPOTensor.GroupFamily.ReductionFamily.block_hasExteriorBufferLength_one`:
  after blocking by any positive `L` with `N₀(g,h) ≤ L + 1` for every pair,
  one exterior site suffices for every pair.
* `MPOTensor.GroupFamily.IsRepresentation.exists_block_reductionFamily_one`:
  the common-blocking theorem, packaged with the blocked representation.
* `MPOTensor.GroupFamily.ReductionFamily.hasExteriorBufferLength_smul`,
  `MPOTensor.GroupFamily.ReductionFamily.block_smul`: the reciprocal scalar
  rescaling preserves the exterior buffer lengths and commutes with blocking.

Sources: arXiv:2502.20257, `main.tex` lines 1403--1405 and 1498;
arXiv:2405.00439v2, Theorem 1 and its footnote, `MPU-DW.tex` lines 358--364.
-/

open scoped Matrix

namespace MPOTensor

namespace GroupFamily

universe u

variable {G : Type u} {d : ℕ}

/-- The vectorized product tensor $\mathcal U_g\mathcal U_h$, the source of the
reduction for the pair `(g, h)`.

Source: arXiv:2502.20257, `main.tex` lines 1403--1405. -/
noncomputable def productTensor (F : GroupFamily G d) (g h : G) :
    MPSTensor (d * d) (F.bondDim g * F.bondDim h) :=
  (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor

/-- Blocking every tensor by `L` sites blocks the product tensor, up to the
canonical pairing of the blocked ket and bra words. -/
theorem productTensor_block (F : GroupFamily G d) (g h : G) (L : ℕ) :
    (F.block L).productTensor g h =
      Kraus.reindexPhysical (blockedDoubledIndexEquiv d L)
        (MPSTensor.blockTensor (F.productTensor g h) L) := by
  change (mulTensor (MPOTensor.blockTensor (F.tensor g) L)
    (MPOTensor.blockTensor (F.tensor h) L)).toMPSTensor = _
  rw [← blockTensor_mulTensor, toMPSTensor_blockTensor]
  rfl

variable [Group G]

/-- The vectorized tensor $\mathcal U_{gh}$, the target of the reduction for the
pair `(g, h)`.

Source: arXiv:2502.20257, `main.tex` lines 1403--1405. -/
def targetTensor (F : GroupFamily G d) (g h : G) :
    MPSTensor (d * d) (F.bondDim (g * h)) :=
  (F.tensor (g * h)).toMPSTensor

/-- Blocking every tensor by `L` sites blocks the target tensor, up to the
canonical pairing of the blocked ket and bra words. -/
theorem targetTensor_block (F : GroupFamily G d) (g h : G) (L : ℕ) :
    (F.block L).targetTensor g h =
      Kraus.reindexPhysical (blockedDoubledIndexEquiv d L)
        (MPSTensor.blockTensor (F.targetTensor g h) L) := by
  change (MPOTensor.blockTensor (F.tensor (g * h)) L).toMPSTensor = _
  rw [toMPSTensor_blockTensor]
  rfl

/-- One selected rectangular reduction $(V_{g,h},W_{g,h})$ from
$\mathcal U_g\mathcal U_h$ to $\mathcal U_{gh}$ for every pair `(g, h)`.  The
reduction identities are the interior fusion equation `eq:fusion_2` of
arXiv:2502.20257 together with $V_{g,h}W_{g,h}=1$.

Source: arXiv:2502.20257, `main.tex` lines 1403--1405 and `eq:fusion_2`;
arXiv:1706.07329v2, Definition following Proposition 20. -/
structure ReductionFamily (F : GroupFamily G d) where
  /-- The reduction matrix $V_{g,h}$ from the product bond to the target bond. -/
  V : ∀ g h : G, Matrix (Fin (F.bondDim (g * h))) (Fin (F.bondDim g * F.bondDim h)) ℂ
  /-- The reduction matrix $W_{g,h}$ from the target bond to the product bond. -/
  W : ∀ g h : G, Matrix (Fin (F.bondDim g * F.bondDim h)) (Fin (F.bondDim (g * h))) ℂ
  /-- $(V_{g,h},W_{g,h})$ is a rectangular reduction from
  $\mathcal U_g\mathcal U_h$ to $\mathcal U_{gh}$. -/
  isReduction : ∀ g h : G,
    MPSTensor.IsReduction (F.productTensor g h) (F.targetTensor g h) (V g h) (W g h)

/-- A simple injective MPU representation admits a selected reduction for every
pair: the product tensor and the target tensor generate the same
positive-length matrix product vectors, and the target is injective.

Source: arXiv:2502.20257, `main.tex` lines 1403--1405, invoking
arXiv:1706.07329v2, Proposition 20 in its equality case. -/
theorem IsRepresentation.nonempty_reductionFamily (F : GroupFamily G d)
    (hF : F.IsRepresentation) : Nonempty F.ReductionFamily := by
  have hpair : ∀ g h : G,
      ∃ (V : Matrix (Fin (F.bondDim (g * h))) (Fin (F.bondDim g * F.bondDim h)) ℂ)
        (W : Matrix (Fin (F.bondDim g * F.bondDim h)) (Fin (F.bondDim (g * h))) ℂ),
        MPSTensor.IsReduction (F.productTensor g h) (F.targetTensor g h) V W :=
    fun g h ↦ MPSTensor.exists_isReduction_of_isInjective_of_sameMPV₂Pos _ _
      (hF.isInjective (g * h)) (hF.sameMPV₂Pos_mulTensor F g h).symm
  choose V W hVW using hpair
  exact ⟨⟨V, W, hVW⟩⟩

namespace ReductionFamily

variable {F : GroupFamily G d}

/-- The MGSC18 nilpotency length $N_0(g,h)$ of the selected reduction of the
pair `(g, h)`.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines
3147--3152. -/
noncomputable def nilpotencyLength (R : F.ReductionFamily) (g h : G) : ℕ :=
  MPSTensor.reductionResidualNilpotencyLength (F.productTensor g h)
    (F.targetTensor g h) (R.V g h) (R.W g h)

/-- Every selected reduction satisfies the exterior identity with exterior
buffers of at least `m` sites on each side:
$B^{\mathbf p}W_{g,h}A^{\mathbf c}V_{g,h}B^{\mathbf q}=B^{\mathbf p\mathbf c\mathbf q}$
for every nonempty central word $\mathbf c$ and all $|\mathbf p|,|\mathbf q|\geq m$.

Source: arXiv:2502.20257, `eq:fusion_1`, `main.tex` lines 1409--1498, with
$m\geq\ell$. -/
def HasExteriorBufferLength (R : F.ReductionFamily) (m : ℕ) : Prop :=
  ∀ g h : G, MPSTensor.IsReductionExteriorBufferLength (F.productTensor g h)
    (F.targetTensor g h) (R.V g h) (R.W g h) m

/-- The nilpotency length of a pair, less one, is an exterior buffer length for
that pair.  Positive-length closed-chain equality comes from the
representation law. -/
theorem isReductionExteriorBufferLength_nilpotencyLength (R : F.ReductionFamily)
    (hF : F.IsRepresentation) (g h : G) :
    MPSTensor.IsReductionExteriorBufferLength (F.productTensor g h)
      (F.targetTensor g h) (R.V g h) (R.W g h) (R.nilpotencyLength g h - 1) :=
  (R.isReduction g h).isReductionExteriorBufferLength_nilpotencyLength
    (hF.sameMPV₂Pos_mulTensor F g h).symm

/-- The exterior identity `eq:fusion_1` before blocking: any `m` with
$N_0(g,h)\leq m+1$ for every pair is a common exterior buffer length.

Source: arXiv:2502.20257, `eq:fusion_1`, `main.tex` lines 1409--1498. -/
theorem hasExteriorBufferLength_of_le (R : F.ReductionFamily)
    (hF : F.IsRepresentation) {m : ℕ}
    (hN : ∀ g h : G, R.nilpotencyLength g h ≤ m + 1) :
    R.HasExteriorBufferLength m :=
  fun g h ↦ (R.isReductionExteriorBufferLength_nilpotencyLength hF g h).mono
    (by have := hN g h; omega)

/-- The selected reductions, transported to the representation blocked by `L`
sites.  The reduction matrices are unchanged; only the physical alphabet of the
tensors changes. -/
noncomputable def block (R : F.ReductionFamily) (L : ℕ) :
    (F.block L).ReductionFamily where
  V := R.V
  W := R.W
  isReduction g h := by
    rw [productTensor_block, targetTensor_block]
    exact ((R.isReduction g h).blockTensor L).reindexPhysical _

/-- After blocking by a positive `L` with $N_0(g,h)\leq L+1$ for every pair,
one blocked exterior site suffices for every pair.

Source: arXiv:2502.20257, `main.tex` line 1498, read as the exterior identity
`eq:fusion_1` with $m\geq1$; arXiv:2405.00439v2, Theorem 1 and its footnote,
`MPU-DW.tex` lines 358--364. -/
theorem block_hasExteriorBufferLength_one (R : F.ReductionFamily)
    (hF : F.IsRepresentation) {L : ℕ} (hL : 0 < L)
    (hN : ∀ g h : G, R.nilpotencyLength g h ≤ L + 1) :
    (R.block L).HasExteriorBufferLength 1 := by
  intro g h
  change MPSTensor.IsReductionExteriorBufferLength ((F.block L).productTensor g h)
    ((F.block L).targetTensor g h) (R.V g h) (R.W g h) 1
  rw [productTensor_block, targetTensor_block]
  exact ((R.isReductionExteriorBufferLength_nilpotencyLength hF g h).blockTensor hL
    (by have := hN g h; omega)).reindexPhysical _

/-- The reciprocal scalar rescaling of a family of selected reductions by a
scalar $2$-cochain $\beta\colon G^2\to\mathbb{C}^\times$:
$W_{g,h}\mapsto\beta_{g,h}W_{g,h}$ and
$V_{g,h}\mapsto\beta_{g,h}^{-1}V_{g,h}$.  The rescaled matrices are again a
family of selected reductions of the same representation.

Under the identification $F^<_{g,h}=V_{g,h}$, $F^>_{g,h}=W_{g,h}$ this is the
gauge freedom of the fusion tensors in arXiv:2502.20257, `eq:scalar_fus_ten`,
`main.tex` lines 1500--1504.  The source calls the fusion tensors "defined up
to a scalar"; what is stated here is that a reciprocal rescaling of a family
of selected reductions is again such a family, not that every family arises
this way. -/
noncomputable def smul (R : F.ReductionFamily)
    (β : TNLean.Algebra.ScalarCocycle G) : F.ReductionFamily where
  V g h := (β g h : ℂ)⁻¹ • R.V g h
  W g h := (β g h : ℂ) • R.W g h
  isReduction g h := (R.isReduction g h).reciprocal_smul (β g h).ne_zero

/-- The reciprocal scalar rescaling preserves the exterior identity
`eq:fusion_1` for the same buffer length, in both directions: the two scalars
meet inside the central segment $W_{g,h}A_{g,h}^{\mathbf c}V_{g,h}$ and
cancel. -/
theorem hasExteriorBufferLength_smul (R : F.ReductionFamily)
    (β : TNLean.Algebra.ScalarCocycle G) (m : ℕ) :
    (R.smul β).HasExteriorBufferLength m ↔ R.HasExteriorBufferLength m := by
  unfold HasExteriorBufferLength
  refine forall_congr' fun g ↦ forall_congr' fun h ↦ ?_
  exact MPSTensor.IsReductionExteriorBufferLength.reciprocal_smul_iff
    (β g h).ne_zero

/-- The reciprocal scalar rescaling commutes with physical blocking: blocking
acts on the tensors only, and the rescaling acts on the reduction matrices
only. -/
theorem block_smul (R : F.ReductionFamily) (β : TNLean.Algebra.ScalarCocycle G)
    (L : ℕ) : (R.smul β).block L = (R.block L).smul β := rfl

section Finite

variable [Fintype G]

/-- One positive common blocking length for a finite group: the common buffer
length of the family of nilpotency lengths $N_0(g,h)$ over all pairs. -/
noncomputable def commonBufferLength (R : F.ReductionFamily) : ℕ :=
  _root_.commonBufferLength fun p : G × G ↦ R.nilpotencyLength p.1 p.2

/-- The common blocking length is positive. -/
theorem commonBufferLength_pos (R : F.ReductionFamily) : 0 < R.commonBufferLength :=
  _root_.commonBufferLength_pos _

/-- Every pair satisfies $N_0(g,h)\leq L+1$ for the common blocking length `L`. -/
theorem nilpotencyLength_le_commonBufferLength_add_one (R : F.ReductionFamily) (g h : G) :
    R.nilpotencyLength g h ≤ R.commonBufferLength + 1 :=
  le_commonBufferLength_add_one (fun p : G × G ↦ R.nilpotencyLength p.1 p.2) (g, h)

/-- After the common block, one blocked exterior site suffices for every pair. -/
theorem block_commonBufferLength_hasExteriorBufferLength_one (R : F.ReductionFamily)
    (hF : F.IsRepresentation) :
    (R.block R.commonBufferLength).HasExteriorBufferLength 1 :=
  R.block_hasExteriorBufferLength_one hF R.commonBufferLength_pos
    R.nilpotencyLength_le_commonBufferLength_add_one

end Finite

end ReductionFamily

/-- Common blocking for the one-site fusion identities of a finite-group MPU
representation: there is a positive length `L` such that the blocked family is
again a simple injective MPU representation and admits, for every pair
`(g, h)`, a reduction from $\mathcal U_g^{[L]}\mathcal U_h^{[L]}$ to
$\mathcal U_{gh}^{[L]}$ whose exterior identity holds with one blocked site on
each side.

Source: arXiv:2502.20257, `main.tex` line 1498; arXiv:2405.00439v2, Theorem 1
and its footnote, `MPU-DW.tex` lines 358--364. -/
theorem IsRepresentation.exists_block_reductionFamily_one [Finite G]
    (F : GroupFamily G d) (hF : F.IsRepresentation) :
    ∃ L : ℕ, 0 < L ∧ (F.block L).IsRepresentation ∧
      ∃ R : (F.block L).ReductionFamily, R.HasExteriorBufferLength 1 := by
  have := Fintype.ofFinite G
  obtain ⟨R⟩ := hF.nonempty_reductionFamily F
  exact ⟨R.commonBufferLength, R.commonBufferLength_pos,
    hF.block F R.commonBufferLength R.commonBufferLength_pos,
    R.block R.commonBufferLength, R.block_commonBufferLength_hasExteriorBufferLength_one hF⟩

end GroupFamily

end MPOTensor
