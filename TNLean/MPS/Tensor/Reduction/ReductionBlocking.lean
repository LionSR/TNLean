/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.CommonBufferLength
import TNLean.MPS.Tensor.Physical.Blocking
import TNLean.MPS.Tensor.Reduction.ReductionResidual

/-!
# Rectangular reductions under physical blocking

A rectangular reduction $(V,W)$ from $B$ to $A$ intertwines every word, so it
is also a reduction between the blocked tensors $B^{[L]}$ and $A^{[L]}$ and
between physically reindexed tensors.  This file records these transports and
the exterior-buffer form of the first fusion equation of arXiv:2502.20257: with
exterior buffers of at least $m$ sites,
$$
  B^{\mathbf p}WA^{\mathbf c}VB^{\mathbf q}=B^{\mathbf p\mathbf c\mathbf q}
$$
for every nonempty central word $\mathbf c$.  A residual nilpotency bound $N$
of MGSC18 supplies the buffer length $N-1$, and blocking by $L\geq N-1$ sites
makes one blocked exterior site suffice.  For a finite family of reductions,
the common buffer length of `QICLean.Algebra.Combinatorics.CommonBufferLength` is one such
$L$ for every member.

**Local fix (arXiv:2502.20257, `main.tex` line 1498; arXiv:2405.00439v2,
`MPU-DW.tex` line 358):** both sources say that blocking reduces the
nilpotency length to one.  The formalized content of that sentence is the
one-site exterior identity below.  The blocked residual letters need not
vanish, and the blocked nilpotency length of MGSC18 Definition 8 need not be
one; see `docs/paper-gaps/mgsc18_nilpotency_length_one_terminology.tex`.

## Main definitions

* `MPSTensor.IsReductionExteriorBufferLength`: the exterior identity with
  buffers of length at least `m`.

## Main results

* `MPTensor.IsReduction.isReductionExteriorBufferLength_of_bound`: a residual
  nilpotency bound `N` gives exterior buffer length `N - 1`.
* `MPTensor.IsReduction.block`,
  `MPSTensor.IsReductionExteriorBufferLength.block`: transport through
  physical blocking `Kraus.block`.
* `MPTensor.IsReduction.reindexPhysical`,
  `MPSTensor.IsReductionExteriorBufferLength.reindexPhysical`: transport
  through a physical reindexing of both tensors.
* `MPTensor.IsReduction.block_commonBufferLength_one`: for a member of
  a finite family of nilpotency bounds, blocking by the common buffer length
  makes one blocked exterior site suffice.
* `MPSTensor.IsReductionExteriorBufferLength.reciprocal_smul`: the reciprocal
  scalar rescaling of arXiv:2502.20257, `eq:scalar_fus_ten`, preserves an
  exterior buffer length.
-/

open MPTensor

open scoped Matrix
namespace MPSTensor

variable {α α' : Type*} {D_A D_B : ℕ}

/-- A word of blocks of length `L` flattens to a word of `L` times as many sites. -/
private theorem length_flatMap_ofFn {L : ℕ} (ws : List (Fin L → α)) :
    (ws.flatMap List.ofFn).length = ws.length * L := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [List.flatMap_cons, List.length_append, List.length_ofFn, ih, List.length_cons,
        Nat.succ_mul, Nat.add_comm]

/-- The exterior identity of the first fusion equation with exterior buffers of
length at least `m`: for every nonempty central word `c` and all words `p`, `q`
with `m ≤ |p|` and `m ≤ |q|`,
$B^{\mathbf p}WA^{\mathbf c}VB^{\mathbf q}=B^{\mathbf p\mathbf c\mathbf q}$.

Source: arXiv:2502.20257, `eq:fusion_1`, `main.tex` lines 1409--1498, with
exterior length $m\geq\ell$; the one-block identity of MGSC18, arXiv:1706.07329v2,
Lemma `lem:B_expand` with Definition 8, `cornerproblem.tex` lines 3147--3152
and 3993--4005. -/
def IsReductionExteriorBufferLength (B : MPTensor α (Fin D_B)) (A : MPTensor α (Fin D_A))
    (V : Matrix (Fin D_A) (Fin D_B) ℂ) (W : Matrix (Fin D_B) (Fin D_A) ℂ)
    (m : ℕ) : Prop :=
  ∀ p c q : List α, c ≠ [] → m ≤ p.length → m ≤ q.length →
    Kraus.evalWord B p * W * Kraus.evalWord A c * V * Kraus.evalWord B q =
      Kraus.evalWord B (p ++ c ++ q)

namespace IsReductionExteriorBufferLength

variable {B : MPTensor α (Fin D_B)} {A : MPTensor α (Fin D_A)}
  {V : Matrix (Fin D_A) (Fin D_B) ℂ} {W : Matrix (Fin D_B) (Fin D_A) ℂ} {m : ℕ}

/-- Longer exterior buffers remain exterior buffers. -/
theorem mono (h : IsReductionExteriorBufferLength B A V W m) {n : ℕ}
    (hmn : m ≤ n) : IsReductionExteriorBufferLength B A V W n :=
  fun p c q hc hp hq ↦ h p c q hc (hmn.trans hp) (hmn.trans hq)

/-- The reciprocal scalar rescaling $W\mapsto\beta W$, $V\mapsto\beta^{-1}V$
by a nonzero `β` leaves the exterior identity unchanged: the two scalars meet
inside the central segment $WA^{\mathbf c}V$ and cancel.

Under the identification $F^<=V$, $F^>=W$ this is the scalar gauge freedom of
arXiv:2502.20257, `eq:scalar_fus_ten`, `main.tex` lines 1500--1504, applied to
the exterior fusion equation `eq:fusion_1`, `main.tex` lines 1409--1456. -/
theorem reciprocal_smul_iff {β : ℂ} (hβ : β ≠ 0) :
    IsReductionExteriorBufferLength B A (β⁻¹ • V) (β • W) m ↔
      IsReductionExteriorBufferLength B A V W m := by
  unfold IsReductionExteriorBufferLength
  simp (disch := exact hβ) only [matrix_reciprocal_smul]

/-- The reciprocal scalar rescaling preserves an exterior buffer length, for
the same `m`. -/
theorem reciprocal_smul (h : IsReductionExteriorBufferLength B A V W m) {β : ℂ}
    (hβ : β ≠ 0) : IsReductionExteriorBufferLength B A (β⁻¹ • V) (β • W) m :=
  (reciprocal_smul_iff hβ).2 h

/-- Reindexing the physical alphabet of both tensors by the same map preserves
an exterior buffer length. -/
theorem reindexPhysical (h : IsReductionExteriorBufferLength B A V W m)
    (f : α' → α) :
    IsReductionExteriorBufferLength (Kraus.reindexPhysical f B)
      (Kraus.reindexPhysical f A) V W m := by
  intro p c q hc hp hq
  simp only [Kraus.evalWord_reindexPhysical, List.map_append]
  exact h _ _ _ (by simpa using hc) (by simpa using hp) (by simpa using hq)

/-- Blocking by `L > 0` sites turns an exterior buffer of `m` original sites
into an exterior buffer of `k` blocked sites once `m ≤ k * L`.  In particular
one blocked exterior site suffices when `m ≤ L`. -/
theorem block (h : IsReductionExteriorBufferLength B A V W m) {L k : ℕ}
    (hL : 0 < L) (hk : m ≤ k * L) :
    IsReductionExteriorBufferLength (Kraus.block B L) (Kraus.block A L) V W k := by
  intro p c q hc hp hq
  rw [Kraus.evalWord_append, Kraus.evalWord_append, Kraus.evalWord_block,
    Kraus.evalWord_block, Kraus.evalWord_block, Kraus.evalWord_block,
    ← Kraus.evalWord_append, ← Kraus.evalWord_append]
  refine h _ _ _ ?_ ?_ ?_
  · intro hnil
    have hlen := length_flatMap_ofFn c
    rw [hnil, List.length_nil] at hlen
    have hpos := Nat.mul_pos (List.length_pos_of_ne_nil hc) hL
    omega
  · rw [length_flatMap_ofFn]
    exact hk.trans (Nat.mul_le_mul_right L hp)
  · rw [length_flatMap_ofFn]
    exact hk.trans (Nat.mul_le_mul_right L hq)

end IsReductionExteriorBufferLength

section IsReduction

open MPTensor.IsReduction

variable {B : MPTensor α (Fin D_B)} {A : MPTensor α (Fin D_A)}
  {V : Matrix (Fin D_A) (Fin D_B) ℂ} {W : Matrix (Fin D_B) (Fin D_A) ℂ}

/-- A residual nilpotency bound `N` gives exterior buffer length `N - 1`.

This is the exterior-buffer identity restated with buffers measured in sites:
the bound `N ≤ |p| + 1` reads `N - 1 ≤ |p|`. -/
theorem _root_.MPTensor.IsReduction.isReductionExteriorBufferLength_of_bound
    (h : IsReduction B A V W)
    {N : ℕ} (hBound : IsReductionResidualNilpotencyBound B A V W N) :
    IsReductionExteriorBufferLength B A V W (N - 1) :=
  fun p c q hc hp hq ↦
    h.evalWord_mul_reduced_exterior_eq_evalWord_append hBound p c q hc
      (by omega) (by omega)

/-- The MGSC18 nilpotency length of a reduction, less one, is an exterior
buffer length whenever the closed chains of positive length agree. -/
theorem _root_.MPTensor.IsReduction.isReductionExteriorBufferLength_nilpotencyLength
    (h : IsReduction B A V W)
    (hSame : SameMPV₂Pos B A) :
    IsReductionExteriorBufferLength B A V W
      (reductionResidualNilpotencyLength B A V W - 1) :=
  h.isReductionExteriorBufferLength_of_bound
    (h.reductionResidualNilpotencyLength_isBound hSame)

/-- Common blocking for a finite family of nilpotency bounds `N i`: blocking by
the common buffer length $L=\max(1,\max_i(N_i-1))$ makes one blocked exterior
site suffice for the member with bound `N i`, since $N_i\leq L+1$.

Source: arXiv:2502.20257, `main.tex` line 1498, read as the exterior identity
of `eq:fusion_1` with $m\geq1$ after blocking; the bound $N_i\leq L+1$ is the
hypothesis of the exterior-buffer identity, not the vanishing of a blocked
residual letter. -/
theorem _root_.MPTensor.IsReduction.block_commonBufferLength_one (h : IsReduction B A V W)
    {ι : Type*} [Fintype ι] (N : ι → ℕ) {i : ι}
    (hBound : IsReductionResidualNilpotencyBound B A V W (N i)) :
    IsReductionExteriorBufferLength (Kraus.block B (commonBufferLength N))
      (Kraus.block A (commonBufferLength N)) V W 1 :=
  (h.isReductionExteriorBufferLength_of_bound hBound).block
    (commonBufferLength_pos N) (by have := le_commonBufferLength_add_one N i; omega)

/-- Reindexing the physical alphabet of both tensors by the same map preserves
a rectangular reduction. -/
theorem _root_.MPTensor.IsReduction.reindexPhysical (h : IsReduction B A V W) (f : α' → α) :
    IsReduction (Kraus.reindexPhysical f B) (Kraus.reindexPhysical f A) V W := by
  refine ⟨h.mul_eq_one, fun w ↦ ?_⟩
  rw [Kraus.evalWord_reindexPhysical, Kraus.evalWord_reindexPhysical, h.evalWord]

/-- A rectangular reduction between tensors is a rectangular reduction between
their physical blockings by the same length. -/
theorem _root_.MPTensor.IsReduction.block (h : IsReduction B A V W) (L : ℕ) :
    IsReduction (Kraus.block B L) (Kraus.block A L) V W := by
  refine ⟨h.mul_eq_one, fun w ↦ ?_⟩
  rw [Kraus.evalWord_block, Kraus.evalWord_block, h.evalWord]

end IsReduction

end MPSTensor
