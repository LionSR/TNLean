/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EncodedFrame

/-!
# Small-patch rewrites of encoded frames

Lemma 6.3 of the polynomial-PEPS manuscript changes an encoded frame on boundedly many small
square patches. The old and new frames share their untouched holes, with the same encodings and
tag owners; only boundedly many holes are affected. With the projectors `P_1, …, P_m` of the
additional patches, the canonical rewrite is
`M = K_new P_m ⋯ P_1 K_oldᴴ`, extended by the identity on the tags of the untouched holes,
where `K_old` and `K_new` encode only the affected holes.

This file states the data and the four conditions of Lemma 6.3, constructs `M`, and proves that
it is a contraction and that `‖M Ω_old - Ω_new‖ ≤ (m + r_old) ε`. The rewrite is placed in
canonical coordinates: the tags of the untouched holes come first in both frames. Since the
encodings of holes with disjoint footprints commute (`rawProd_commute`), this ordering is the
canonical identification of tag orderings of Definition 6.1. Only the first condition is used
for the reference error; the others serve the polynomial expansion
(`TNLean.PEPS.EncodedFrame.SmallPatchRewrite.Conditions`).

## Main definitions

* `EncodedFrame.SmallPatchRewrite`: old and new frames sharing untouched holes, and the
  additional patches.
* `EncodedFrame.SmallPatchRewrite.Conditions`: the four conditions of Lemma 6.3.
* `EncodedFrame.SmallPatchRewrite.rewrite`: the canonical rewrite `M` between the layouts.

## Main results

* `EncodedFrame.SmallPatchRewrite.norm_rewrite_le_one`: `M` is a contraction.
* `EncodedFrame.SmallPatchRewrite.rewrite_mul_encoder`: the exact intertwining identity
  `M K_{F_old} = K_{F_new} P_m ⋯ P_1 ∏_a P_a^{old}`.
* `EncodedFrame.SmallPatchRewrite.norm_rewrite_refVec_sub_le`: `eq:rewrite-reference-error`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 182–252.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Operator norms under reindexing and identity extension -/

section Norms

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq n]
  [DecidableEq n']

/-- A bound on the action on every vector bounds the operator norm. -/
theorem l2_opNorm_le_of_act {A : Matrix m n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ψ : EuclideanSpace ℂ n, ‖act A ψ‖ ≤ c * ‖ψ‖) : ‖A‖ ≤ c := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hc fun ψ => h ψ

/-- Relabelling rows and columns does not increase the operator norm. -/
theorem l2_opNorm_reindex_le (e : m ≃ m') (f : n ≃ n') (A : Matrix m n ℂ) :
    ‖reindex e f A‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_act (norm_nonneg _) fun ψ => ?_
  have h := norm_act_le A (WithLp.toLp 2 fun j => ψ (f j))
  have hψ : ‖(WithLp.toLp 2 fun j => ψ (f j) : EuclideanSpace ℂ n)‖ = ‖ψ‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp f (fun j => ‖ψ j‖ ^ 2)
  have hA : ‖act (reindex e f A) ψ‖ = ‖act A (WithLp.toLp 2 fun j => ψ (f j))‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine (Equiv.sum_comp e fun i' => ‖act (reindex e f A) ψ i'‖ ^ 2).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [reindex_apply, mulVec, dotProduct, submatrix_apply]
    congr 2
    rw [← Equiv.sum_comp f]
    simp
  rw [hA, ← hψ]
  exact h

/-- Tensoring with an identity on a finite reference does not increase the operator norm. -/
theorem l2_opNorm_kronecker_one_le {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix m n ℂ) :
    ‖A ⊗ₖ (1 : Matrix κ κ ℂ)‖ ≤ ‖A‖ :=
  l2_opNorm_le_of_act (norm_nonneg _) fun ψ => l2_opNorm_kronecker_one_mulVec_le A ψ

end Norms

variable {pos : ι → ℝ × ℝ} {Party : Type*}

theorem PairwiseDisjointOuter.left {l₁ l₂ : List (Hole pos q Party)}
    (h : PairwiseDisjointOuter ((l₁ ++ l₂).map Hole.patch)) :
    PairwiseDisjointOuter (l₁.map Hole.patch) := by
  rw [List.map_append] at h
  exact List.Pairwise.sublist (List.sublist_append_left _ _) h

theorem PairwiseDisjointOuter.right {l₁ l₂ : List (Hole pos q Party)}
    (h : PairwiseDisjointOuter ((l₁ ++ l₂).map Hole.patch)) :
    PairwiseDisjointOuter (l₂.map Hole.patch) := by
  rw [List.map_append] at h
  exact List.Pairwise.sublist (List.sublist_append_right _ _) h

/-! ### The data and the conditions of Lemma 6.3 -/

/-- **Data of Lemma 6.3.** Old and new one-sheet frames whose hole lists are
`untouched ++ oldAffected` and `untouched ++ newAffected`: the untouched holes, with their
encodings and tag owners, agree, and appear first in both tag orderings. The `m` additional
square patches `(c_i, u_i)` carry the projectors of Proposition 4.1. The finite set `parties` is
the specified list of parties of condition (iv).

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 184–192. -/
structure SmallPatchRewrite (pos : ι → ℝ × ℝ) (q : ℕ) (Party : Type*) where
  /-- The raw owners of the old frame. -/
  ownerOld : ι → Party
  /-- The raw owners of the new frame. -/
  ownerNew : ι → Party
  /-- The untouched holes: same hole, encoding and tag owner in both frames. -/
  untouched : List (Hole pos q Party)
  /-- The affected holes of the old frame. -/
  oldAffected : List (Hole pos q Party)
  /-- The affected holes of the new frame. -/
  newAffected : List (Hole pos q Party)
  /-- The additional square patches, in a fixed order; the first is applied last. -/
  patches : List (SquarePatch pos q)
  /-- The specified list of parties of condition (iv). -/
  parties : Finset Party
  disjoint_old : PairwiseDisjointOuter ((untouched ++ oldAffected).map Hole.patch)
  disjoint_new : PairwiseDisjointOuter ((untouched ++ newAffected).map Hole.patch)

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

/-- The old frame `F_old`. -/
abbrev oldFrame : Frame pos q Party := ⟨R.ownerOld, R.untouched ++ R.oldAffected, R.disjoint_old⟩

/-- The new frame `F_new`. -/
abbrev newFrame : Frame pos q Party := ⟨R.ownerNew, R.untouched ++ R.newAffected, R.disjoint_new⟩

/-- The physical outer footprints of the untouched holes. -/
def untouchedFootprint : Set ι := footprint (R.untouched.map Hole.patch)

/-- **The four conditions of Lemma 6.3.**

1. Every patch's outer square avoids the physical outer footprints of the untouched holes, and
   so do the affected old and new holes.
2. The union of the patch inner squares contains every site whose raw owner changes and the
   entire physical outer footprint of every affected old or new hole.
3. In each patch's outer square, the sites outside `H^-(F_old)` have at most two old owners,
   and the sites outside `H^-(F_new)` have at most two new owners.
4. All raw owners, old and new, on the patch footprints and on the affected-hole footprints,
   and all affected tag owners, belong to the specified list of parties.

The patches may overlap, and old affected holes may overlap new affected holes.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 193–207. -/
structure Conditions : Prop where
  /-- Condition (i), for the patches. -/
  patch_avoid : ∀ P ∈ R.patches, Disjoint (P.outer : Set ι) R.untouchedFootprint
  /-- Condition (i), for the affected old and new holes. -/
  affected_avoid : ∀ h ∈ R.oldAffected ++ R.newAffected,
    Disjoint (h.patch.outer : Set ι) R.untouchedFootprint
  /-- Condition (ii), for the sites whose raw owner changes. -/
  changed_mem : ∀ x, R.ownerOld x ≠ R.ownerNew x → x ∈ innerUnion R.patches
  /-- Condition (ii), for the outer footprints of the affected holes. -/
  affected_subset : ∀ h ∈ R.oldAffected ++ R.newAffected,
    (h.patch.outer : Set ι) ⊆ innerUnion R.patches
  /-- Condition (iii), old owners. -/
  old_owners : ∀ P ∈ R.patches, ∃ S : Finset Party, S.card ≤ 2 ∧
    ∀ x ∈ P.outer, x ∉ R.oldFrame.innerHoles → R.ownerOld x ∈ S
  /-- Condition (iii), new owners. -/
  new_owners : ∀ P ∈ R.patches, ∃ S : Finset Party, S.card ≤ 2 ∧
    ∀ x ∈ P.outer, x ∉ R.newFrame.innerHoles → R.ownerNew x ∈ S
  /-- Condition (iv), raw owners on the involved footprints. -/
  raw_owners_mem : ∀ x ∈ footprint R.patches ∪
      footprint ((R.oldAffected ++ R.newAffected).map Hole.patch),
    R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties
  /-- Condition (iv), affected tag owners. -/
  tag_owners_mem : ∀ h ∈ R.oldAffected ++ R.newAffected, h.tagOwner ∈ R.parties

/-- Condition (i) alone: the patches and the affected holes avoid the untouched footprints. -/
structure AvoidsUntouched : Prop where
  patch_avoid : ∀ P ∈ R.patches, Disjoint (P.outer : Set ι) R.untouchedFootprint
  affected_avoid : ∀ h ∈ R.oldAffected ++ R.newAffected,
    Disjoint (h.patch.outer : Set ι) R.untouchedFootprint

theorem Conditions.avoidsUntouched {R : SmallPatchRewrite pos q Party} (h : R.Conditions) :
    R.AvoidsUntouched :=
  ⟨h.patch_avoid, h.affected_avoid⟩

/-! ### The canonical rewrite -/

/-- The product `P_m ⋯ P_1` of the additional patch projectors. -/
def patchProj : Matrix (ι → Fin q) (ι → Fin q) ℂ := projProd R.patches

/-- The affected part `K_new P_m ⋯ P_1 K_oldᴴ` of the rewrite, between the affected tags and
the raw registers. -/
def affectedRewrite [NeZero q] :
    Matrix (TagSpace R.newAffected × (ι → Fin q)) (TagSpace R.oldAffected × (ι → Fin q)) ℂ :=
  frameEncoder R.newAffected * R.patchProj * (frameEncoder R.oldAffected)ᴴ

/-- Coordinates of a layout of the form `untouched ++ affected`, with the untouched tags as
the outer factor. -/
def layoutEquiv (l : List (Hole pos q Party)) :
    (TagSpace l × (ι → Fin q)) × TagSpace R.untouched ≃ TagSpace (R.untouched ++ l) × (ι → Fin q)
    where
  toFun x := ((tagAppendEquiv R.untouched l).symm (x.2, x.1.1), x.1.2)
  invFun y := (((tagAppendEquiv R.untouched l y.1).2, y.2), (tagAppendEquiv R.untouched l y.1).1)
  left_inv x := by simp
  right_inv y := by simp

/-- **The canonical rewrite (`eq:rewrite-map`).** `M = K_new P_m ⋯ P_1 K_oldᴴ` on the affected
tags and the raw registers, and the identity on the tags of the untouched holes. Its input
layout is that of `F_old` and its output layout is that of `F_new`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 222–232. -/
def rewrite [NeZero q] : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ :=
  reindex (R.layoutEquiv R.newAffected) (R.layoutEquiv R.oldAffected)
    (R.affectedRewrite ⊗ₖ (1 : Matrix (TagSpace R.untouched) (TagSpace R.untouched) ℂ))

theorem norm_affectedRewrite_le_one [NeZero q] : ‖R.affectedRewrite‖ ≤ 1 := by
  have h2 := norm_frameEncoder_le_one R.disjoint_old.right
  rw [← l2_opNorm_conjTranspose] at h2
  exact norm_mul_le_one (norm_mul_le_one (norm_frameEncoder_le_one R.disjoint_new.right)
    (norm_projProd_le_one R.patches)) h2

/-- **The canonical rewrite is a contraction.**

Polynomial-PEPS manuscript, `05-frames.tex`, line 232. -/
theorem norm_rewrite_le_one [NeZero q] : ‖R.rewrite‖ ≤ 1 :=
  ((l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_kronecker_one_le _)).trans
    R.norm_affectedRewrite_le_one

/-! ### The exact intertwining identity and the reference error -/

omit [DecidableEq ι] in
theorem kronecker_one_mul_apply {m n l κ : Type*} [Fintype n] [Fintype κ] [DecidableEq κ]
    (N : Matrix m n ℂ) (C : Matrix (n × κ) l ℂ) (r : m) (u : κ) (τ : l) :
    ((N ⊗ₖ (1 : Matrix κ κ ℂ)) * C) (r, u) τ = (N * Matrix.of fun s τ => C (s, u) τ) r τ := by
  simp [mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply]

/-- The products of the untouched hole encodings commute with the affected encodings, the patch
projectors and the affected old projectors. -/
theorem commute_untouched [NeZero q] (hR : R.AvoidsUntouched) (u : TagSpace R.untouched)
    (a : TagSpace R.newAffected) :
    Commute (rawProd R.untouched u)
      (rawProd R.newAffected a * R.patchProj * projProd (R.oldAffected.map Hole.patch)) := by
  have hU := rawProd_mem_supportedOperators R.untouched u
  have hnew : Disjoint R.untouchedFootprint (footprint (R.newAffected.map Hole.patch)) :=
    (disjoint_footprint_of_forall fun p hp => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact hR.affected_avoid h (List.mem_append_right _ hh)).symm
  have hold : Disjoint R.untouchedFootprint (footprint (R.oldAffected.map Hole.patch)) :=
    (disjoint_footprint_of_forall fun p hp => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact hR.affected_avoid h (List.mem_append_left _ hh)).symm
  have hpatch : Disjoint R.untouchedFootprint (footprint R.patches) :=
    (disjoint_footprint_of_forall hR.patch_avoid).symm
  refine ((commute_of_mem_supportedOperators hnew hU
    (rawProd_mem_supportedOperators _ a)).mul_right
    (commute_of_mem_supportedOperators hpatch hU (projProd_mem_supportedOperators _))).mul_right
    (commute_of_mem_supportedOperators hold hU (projProd_mem_supportedOperators _))

/-- The encoding of a frame `untouched ++ affected`, in the coordinates with the untouched tags
as the outer factor. -/
theorem encoder_layoutEquiv [NeZero q] {l : List (Hole pos q Party)}
    (hd : PairwiseDisjointOuter ((R.untouched ++ l).map Hole.patch))
    (hl : Disjoint (footprint (R.untouched.map Hole.patch)) (footprint (l.map Hole.patch)))
    (b : TagSpace l) (ρ : ι → Fin q) (u : TagSpace R.untouched) (τ : ι → Fin q) :
    (Frame.encoder ⟨R.ownerOld, R.untouched ++ l, hd⟩) (R.layoutEquiv l ((b, ρ), u)) τ =
      (rawProd l b * rawProd R.untouched u) ρ τ := by
  change rawProd (R.untouched ++ l) ((tagAppendEquiv _ _).symm (u, b)) ρ τ = _
  rw [rawProd_append, Equiv.apply_symm_apply]
  exact congrFun (congrFun (rawProd_commute hl u b).eq ρ) τ

/-- **Exact intertwining identity.** Under condition (i),
`M K_{F_old} = K_{F_new} P_m ⋯ P_1 ∏_a P_a^{old}`, where the last product runs over the
affected old holes. The untouched encodings commute through the factors of `M`, and
`K_oldᴴ K_old` is the product of the affected old-hole projectors.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 234–237. -/
theorem rewrite_mul_encoder [NeZero q] (hR : R.AvoidsUntouched) :
    R.rewrite * R.oldFrame.encoder =
      R.newFrame.encoder * (R.patchProj * projProd (R.oldAffected.map Hole.patch)) := by
  set P₀ := projProd (R.oldAffected.map Hole.patch)
  set eN := R.layoutEquiv R.newAffected
  set eO := R.layoutEquiv R.oldAffected
  set K := R.affectedRewrite ⊗ₖ (1 : Matrix (TagSpace R.untouched) (TagSpace R.untouched) ℂ)
  have hgram : (frameEncoder R.oldAffected)ᴴ * frameEncoder R.oldAffected = P₀ :=
    frameEncoder_conjTranspose_mul_self R.disjoint_old.right
  have hfoot (l : List (Hole pos q Party)) (hl : ∀ h ∈ l, h ∈ R.oldAffected ++ R.newAffected) :
      Disjoint (footprint (R.untouched.map Hole.patch)) (footprint (l.map Hole.patch)) :=
    (disjoint_footprint_of_forall fun p hp => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact hR.affected_avoid h (hl h hh)).symm
  have hUO := hfoot R.oldAffected fun h hh => List.mem_append_left _ hh
  have hUN := hfoot R.newAffected fun h hh => List.mem_append_right _ hh
  -- The identity in the coordinates with the untouched tags as the outer factor.
  have key : K * R.oldFrame.encoder.submatrix eO id =
      R.newFrame.encoder.submatrix eN id * (R.patchProj * P₀) := by
    ext ⟨⟨a, σ⟩, u⟩ τ
    rw [kronecker_one_mul_apply]
    have hstack : (Matrix.of fun (s : TagSpace R.oldAffected × (ι → Fin q)) τ =>
        R.oldFrame.encoder.submatrix eO id (s, u) τ) =
          frameEncoder R.oldAffected * rawProd R.untouched u := by
      rw [frameEncoder, stack_mul]
      ext ⟨b, ρ⟩ τ
      exact R.encoder_layoutEquiv R.disjoint_old hUO b ρ u τ
    have hnew (ρ : ι → Fin q) : R.newFrame.encoder.submatrix eN id ((a, σ), u) ρ =
        (rawProd R.newAffected a * rawProd R.untouched u) σ ρ :=
      R.encoder_layoutEquiv R.disjoint_new hUN a σ u ρ
    rw [hstack, affectedRewrite, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (frameEncoder R.oldAffected)ᴴ, hgram, frameEncoder, stack_mul,
      stack_apply]
    have hc : rawProd R.newAffected a * (R.patchProj * (P₀ * rawProd R.untouched u)) =
        (rawProd R.newAffected a * rawProd R.untouched u) * (R.patchProj * P₀) := by
      have h : rawProd R.untouched u * (rawProd R.newAffected a * R.patchProj * P₀) =
          rawProd R.newAffected a * R.patchProj * P₀ * rawProd R.untouched u :=
        (R.commute_untouched hR u a).eq
      calc rawProd R.newAffected a * (R.patchProj * (P₀ * rawProd R.untouched u))
          = rawProd R.newAffected a * R.patchProj * P₀ * rawProd R.untouched u := by
            simp only [Matrix.mul_assoc]
        _ = rawProd R.untouched u * rawProd R.newAffected a * (R.patchProj * P₀) := by
            rw [← h]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [(rawProd_commute hUN u a).eq]
    rw [hc, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun ρ _ => by rw [hnew ρ]
  have h1 : R.rewrite * R.oldFrame.encoder =
      (K * R.oldFrame.encoder.submatrix eO id).submatrix eN.symm id := by
    rw [← submatrix_mul_equiv K _ eN.symm eO.symm id, submatrix_submatrix,
      Equiv.self_comp_symm, Function.comp_id, submatrix_id_id]
    rfl
  have h2 : R.newFrame.encoder * (R.patchProj * P₀) =
      (R.newFrame.encoder.submatrix eN id * (R.patchProj * P₀)).submatrix eN.symm id := by
    rw [← submatrix_mul_equiv _ _ eN.symm (Equiv.refl _) id, submatrix_submatrix,
      Equiv.self_comp_symm]
    simp
  rw [h1, h2, key]

/-- **Lemma 6.3, reference error (`eq:rewrite-reference-error`).** Suppose the patches and the
affected holes avoid the untouched footprints (condition (i)). If every additional patch
projector and every affected old-hole projector has error at most `ε` on `Ω`, then
`‖M Ω_{F_old} - Ω_{F_new}‖ ≤ (m + r_old) ε`. No commutation of overlapping patch projectors and
no smallness of the errors of the untouched holes is assumed.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 207–213;
proof lines 234–252. -/
theorem norm_rewrite_refVec_sub_le [NeZero q] (hR : R.AvoidsUntouched)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} {ε : ℝ}
    (hpatch : ∀ P ∈ R.patches, ‖act P.proj Ω - Ω‖ ≤ ε)
    (hold : ∀ h ∈ R.oldAffected, ‖act h.patch.proj Ω - Ω‖ ≤ ε) :
    ‖act R.rewrite (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤
      (R.patches.length + R.oldAffected.length) * ε := by
  have hE : act R.rewrite (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω =
      act R.newFrame.encoder
        (act (projProd (R.patches ++ R.oldAffected.map Hole.patch)) Ω - Ω) := by
    rw [Frame.refVec, Frame.refVec, ← act_mul, R.rewrite_mul_encoder hR, act_mul,
      projProd_append, act_sub_right]
    rfl
  rw [hE]
  refine (norm_act_le_of_norm_le_one R.newFrame.norm_encoder_le_one _).trans ?_
  refine (norm_act_projProd_sub_le (ε := ε) fun p hp => ?_).trans ?_
  · rcases List.mem_append.mp hp with hp | hp
    · exact hpatch p hp
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact hold h hh
  · simp

/-- **Lemma 6.3, canonical rewrite.** Under the four conditions of Lemma 6.3, with every
additional patch projector and every affected old-hole projector of error at most `ε` on `Ω`,
the canonical map `M` between the old and new layouts is a contraction and
`‖M Ω_{F_old} - Ω_{F_new}‖ ≤ (m + r_old) ε`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–213;
proof lines 221–252. -/
theorem smallPatchRewrite [NeZero q] (hR : R.Conditions) {Ω : EuclideanSpace ℂ (ι → Fin q)}
    {ε : ℝ} (hpatch : ∀ P ∈ R.patches, ‖act P.proj Ω - Ω‖ ≤ ε)
    (hold : ∀ h ∈ R.oldAffected, ‖act h.patch.proj Ω - Ω‖ ≤ ε) :
    ‖R.rewrite‖ ≤ 1 ∧
      ‖act R.rewrite (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤
        (R.patches.length + R.oldAffected.length) * ε :=
  ⟨R.norm_rewrite_le_one, R.norm_rewrite_refVec_sub_le hR.avoidsUntouched hpatch hold⟩

end SmallPatchRewrite

end TNLean.PEPS.EncodedFrame
