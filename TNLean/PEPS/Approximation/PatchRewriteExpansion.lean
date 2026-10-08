/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PatchRewrite

/-!
# Branches of a small-patch rewrite

The proof of Lemma 6.3 expands the canonical rewrite `M = K_new P_m ⋯ P_1 K_oldᴴ` by expanding
each tag of an affected hole and each additional patch projector in its cylinder terms. A
*complete branch* chooses a tag `(j, ℓ)` for every affected new hole, every patch and every
affected old hole. This file proves:

* the exact branch expansion `M = ∑_β M_β`, and the count of branches: if every hole and patch
  has at most `D` cylinder terms, there are at most `D ^ (r_new + m + r_old)` branches;
* the site-level wire classification of every branch, for every choice of radii: every site of
  a selected old-hole square and of a selected new-hole square lies in a selected patch square;
  the sites of a selected patch square that no selected old-hole square consumes have at most
  two old owners, and dually for new owners; a site in no selected patch square keeps its
  owner; and all these owners belong to the specified list of parties;
* the final rescaling: summing branchwise approximations of total error at most `δ / 2` and
  dividing by `1 + δ / 2` gives a contraction within `δ` of `M`, and the integer `k` of the
  whole-group truncation can be chosen so that `N g / √k ≤ δ / 2`.

**Scope restriction (monomial structure):** the step of the proof of Lemma 6.3 that turns one
branch into a residual tensor network of normalized bras and kets, applies the whole-group
truncation of Lemma 6.2 to it, and reads every product term as an allowed monomial of
Theorem 5.2 is not formalized here (`05-frames.tex`, lines 254–330). It needs allowed
monomials as operators: chronological products of one-party contractions and of normalized pair
sources and pair effects between two named parties, which the library does not yet have.
Consequently the clause "`M_a` has a polynomial expansion into allowed monomials using only the
specified parties" of Lemma 6.3 is not formalized; `norm_rescale_sum_le_of_branches`
assembles `M_a` from any branchwise approximations. Documented in
`docs/paper-gaps/polypeps_small_rewrite_monomials.tex`.

## Main definitions

* `EncodedFrame.PatchTags`, `EncodedFrame.cylProd`: the cylinder-term choices for a list of
  patches and the corresponding ordered product of cylinder projectors.
* `EncodedFrame.SmallPatchRewrite.Branch`, `EncodedFrame.SmallPatchRewrite.branchOp`: complete
  branches and their operators.

## Main results

* `EncodedFrame.SmallPatchRewrite.rewrite_eq_sum_branch`: `M = ∑_β M_β`.
* `EncodedFrame.SmallPatchRewrite.card_branch_le`: the number of branches.
* `EncodedFrame.SmallPatchRewrite.oldSample_subset_patchSquares`,
  `EncodedFrame.SmallPatchRewrite.newSample_subset_patchSquares`,
  `EncodedFrame.SmallPatchRewrite.exists_old_owners_of_patch_input`,
  `EncodedFrame.SmallPatchRewrite.exists_new_owners_of_patch_output`,
  `EncodedFrame.SmallPatchRewrite.ownerOld_eq_ownerNew_of_direct`: the wire classification.
* `EncodedFrame.norm_rescale_sum_le_of_branches`, `EncodedFrame.truncationRank_spec`:
  rescaling and the choice of `k`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 254–344.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ}

/-! ### Cylinder-term choices for a list of patches -/

/-- A choice of one cylinder term `(j, ℓ)` for every patch of the list. -/
def PatchTags : List (SquarePatch pos q) → Type
  | [] => Unit
  | p :: l => p.Tag × PatchTags l

instance instFintypePatchTags : (l : List (SquarePatch pos q)) → Fintype (PatchTags l)
  | [] => inferInstanceAs (Fintype Unit)
  | p :: l =>
    haveI := instFintypePatchTags l
    inferInstanceAs (Fintype (p.Tag × PatchTags l))

instance instDecidableEqPatchTags : (l : List (SquarePatch pos q)) → DecidableEq (PatchTags l)
  | [] => inferInstanceAs (DecidableEq Unit)
  | p :: l =>
    haveI := instDecidableEqPatchTags l
    inferInstanceAs (DecidableEq (p.Tag × PatchTags l))

/-- The ordered product of the chosen cylinder projectors. -/
def cylProd : (l : List (SquarePatch pos q)) → PatchTags l → Matrix (ι → Fin q) (ι → Fin q) ℂ
  | [], _ => 1
  | p :: l, s => p.cyl s.1 * cylProd l s.2

/-- Expanding every projector of the list in its cylinder terms. -/
theorem projProd_eq_sum_cylProd :
    (l : List (SquarePatch pos q)) → projProd l = ∑ s, cylProd l s
  | [] => by
    change (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) = ∑ _s : Unit, 1
    simp
  | p :: l => by
    rw [projProd, List.map_cons, List.prod_cons]
    change p.proj * projProd l = ∑ s : p.Tag × PatchTags l, p.cyl s.1 * cylProd l s.2
    rw [projProd_eq_sum_cylProd l, SquarePatch.proj, Finset.sum_mul_sum, Fintype.sum_prod_type]

theorem card_patchTags_le {D : ℕ} :
    (l : List (SquarePatch pos q)) → (∀ p ∈ l, Fintype.card p.Tag ≤ D) →
      Fintype.card (PatchTags l) ≤ D ^ l.length
  | [], _ => by
    change Fintype.card Unit ≤ D ^ 0
    simp
  | p :: l, h => by
    change Fintype.card (p.Tag × PatchTags l) ≤ D ^ (l.length + 1)
    rw [Fintype.card_prod, pow_succ, mul_comm]
    exact Nat.mul_le_mul (card_patchTags_le l fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))
      (h p List.mem_cons_self)

variable {Party : Type*}

theorem card_tagSpace_le {D : ℕ} :
    (l : List (Hole pos q Party)) → (∀ h ∈ l, Fintype.card h.patch.Tag ≤ D) →
      Fintype.card (TagSpace l) ≤ D ^ l.length
  | [], _ => by
    change Fintype.card Unit ≤ D ^ 0
    simp
  | h :: l, hD => by
    change Fintype.card (h.patch.Tag × TagSpace l) ≤ D ^ (l.length + 1)
    rw [Fintype.card_prod, pow_succ, mul_comm]
    exact Nat.mul_le_mul (card_tagSpace_le l fun h' hh' => hD h' (List.mem_cons_of_mem _ hh'))
      (hD h List.mem_cons_self)

/-- The entries of `stack B * X * (stack A)ᴴ`. -/
theorem stack_mul_mul_stack_conjTranspose_apply {S T m : Type*} [Fintype m]
    (B : S → Matrix m m ℂ) (X : Matrix m m ℂ) (A : T → Matrix m m ℂ) (s : S) (σ : m) (t : T)
    (ρ : m) : (stack B * X * (stack A)ᴴ) (s, σ) (t, ρ) = (B s * X * (A t)ᴴ) σ ρ := by
  simp [Matrix.mul_apply, stack_apply]

/-! ### Branches of the canonical rewrite -/

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

/-- A complete branch: a tag of every affected new hole, a cylinder term of every additional
patch, and a tag of every affected old hole.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 254–257. -/
abbrev Branch : Type := TagSpace R.newAffected × PatchTags R.patches × TagSpace R.oldAffected

/-- The operator of a branch `β = (a, s, b)`: `|a⟩⟨b| ⊗ R^{new}_a C_s (R^{old}_b)ᴴ`, where
`C_s` is the ordered product of the chosen cylinder projectors. -/
def branchOp [NeZero q] (β : R.Branch) :
    Matrix (TagSpace R.newAffected × (ι → Fin q)) (TagSpace R.oldAffected × (ι → Fin q)) ℂ :=
  Matrix.of fun x y =>
    if x.1 = β.1 ∧ y.1 = β.2.2 then
      (rawProd R.newAffected β.1 * cylProd R.patches β.2.1 * (rawProd R.oldAffected β.2.2)ᴴ)
        x.2 y.2
    else 0

/-- **Branch expansion of the affected rewrite.** -/
theorem affectedRewrite_eq_sum_branchOp [NeZero q] :
    R.affectedRewrite = ∑ β, R.branchOp β := by
  ext ⟨a, σ⟩ ⟨b, ρ⟩
  rw [affectedRewrite, frameEncoder, frameEncoder, stack_mul_mul_stack_conjTranspose_apply,
    patchProj, projProd_eq_sum_cylProd, Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [branchOp, of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a (fun a' _ ha' => by simp [Ne.symm ha'])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp only [true_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]

/-- **Branch expansion of the canonical rewrite.** `M = ∑_β M_β`, where `M_β` is the branch
operator on the affected tags and the raw registers, extended by the identity on the untouched
tags.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 254–257. -/
theorem rewrite_eq_sum_branch [NeZero q] :
    R.rewrite = ∑ β, reindex (R.layoutEquiv R.newAffected) (R.layoutEquiv R.oldAffected)
      (R.branchOp β ⊗ₖ (1 : Matrix (TagSpace R.untouched) (TagSpace R.untouched) ℂ)) := by
  ext x y
  simp only [rewrite, reindex_apply, submatrix_apply, Matrix.sum_apply, kroneckerMap_apply,
    affectedRewrite_eq_sum_branchOp, Finset.sum_mul]

/-- **Number of branches.** If every affected hole and every additional patch has at most `D`
cylinder terms, there are at most `D ^ (r_new + m + r_old)` complete branches.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 255–257 and 331–332. -/
theorem card_branch_le {D : ℕ} (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ D)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ D)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ D) :
    Fintype.card R.Branch ≤
      D ^ (R.newAffected.length + R.patches.length + R.oldAffected.length) := by
  rw [Fintype.card_prod, Fintype.card_prod, pow_add, pow_add, mul_assoc]
  exact Nat.mul_le_mul (card_tagSpace_le _ hnew)
    (Nat.mul_le_mul (card_patchTags_le _ hpatch) (card_tagSpace_le _ hold))

/-! ### Wire classification of a branch -/

/-- The union of the selected patch squares of a branch, for a choice `jP` of radius of every
patch. -/
def patchSquares (jP : ∀ P ∈ R.patches, Fin P.n) : Set ι :=
  {x | ∃ P, ∃ hP : P ∈ R.patches, x ∈ P.sample (jP P hP)}

theorem innerUnion_subset_patchSquares (jP : ∀ P ∈ R.patches, Fin P.n) :
    innerUnion R.patches ⊆ R.patchSquares jP := by
  rintro x ⟨P, hP, hx⟩
  exact ⟨P, hP, P.inner_subset_sample _ hx⟩

/-- **Decoded old-hole kets have no open output legs.** Under condition (ii), for every choice
of radii, every site of the selected square of an affected old hole lies in a selected patch
square, so each of its output legs meets a later patch bra.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 285–288. -/
theorem oldSample_subset_patchSquares (hR : R.Conditions) (jP : ∀ P ∈ R.patches, Fin P.n)
    {h : Hole pos q Party} (hh : h ∈ R.oldAffected) (j : Fin h.patch.n) :
    (h.patch.sample j : Set ι) ⊆ R.patchSquares jP :=
  (Finset.coe_subset.mpr (h.patch.sample_subset_outer j)).trans
    ((hR.affected_subset h (List.mem_append_left _ hh)).trans
      (R.innerUnion_subset_patchSquares jP))

/-- **New-hole encoding bras have no open input legs.** Under condition (ii), for every choice
of radii, every site of the selected square of an affected new hole lies in a selected patch
square, so each of its input legs meets an earlier patch ket.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 288–291. -/
theorem newSample_subset_patchSquares (hR : R.Conditions) (jP : ∀ P ∈ R.patches, Fin P.n)
    {h : Hole pos q Party} (hh : h ∈ R.newAffected) (j : Fin h.patch.n) :
    (h.patch.sample j : Set ι) ⊆ R.patchSquares jP :=
  (Finset.coe_subset.mpr (h.patch.sample_subset_outer j)).trans
    ((hR.affected_subset h (List.mem_append_right _ hh)).trans
      (R.innerUnion_subset_patchSquares jP))

/-- A site of a patch outer square inside `H^-(F_old)` lies in the inner square of an affected
old hole: by condition (i) it is not in an untouched hole. -/
theorem mem_oldAffected_inner_of_mem_innerHoles (hR : R.Conditions) {P : SquarePatch pos q}
    (hP : P ∈ R.patches) {x : ι} (hx : x ∈ P.outer) (hH : x ∈ R.oldFrame.innerHoles) :
    ∃ h ∈ R.oldAffected, x ∈ h.patch.inner := by
  obtain ⟨p, hp, hxp⟩ := hH
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
  rcases List.mem_append.mp hh with hu | ha
  · exact absurd (subset_footprint (List.mem_map_of_mem hu) (h.patch.inner_subset_outer hxp))
      (Set.disjoint_left.mp (hR.patch_avoid P hP) hx)
  · exact ⟨h, ha, hxp⟩

/-- The new-frame analogue of `mem_oldAffected_inner_of_mem_innerHoles`. -/
theorem mem_newAffected_inner_of_mem_innerHoles (hR : R.Conditions) {P : SquarePatch pos q}
    (hP : P ∈ R.patches) {x : ι} (hx : x ∈ P.outer) (hH : x ∈ R.newFrame.innerHoles) :
    ∃ h ∈ R.newAffected, x ∈ h.patch.inner := by
  obtain ⟨p, hp, hxp⟩ := hH
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
  rcases List.mem_append.mp hh with hu | ha
  · exact absurd (subset_footprint (List.mem_map_of_mem hu) (h.patch.inner_subset_outer hxp))
      (Set.disjoint_left.mp (hR.patch_avoid P hP) hx)
  · exact ⟨h, ha, hxp⟩

/-- **Open inputs of a patch bra have at most two old owners.** For every choice of radii of
the affected old holes, the sites of a selected patch square that no selected old-hole square
consumes lie outside `H^-(F_old)` in the patch outer square, so by condition (iii) their old
owners form a set of at most two parties.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 293–300. -/
theorem exists_old_owners_of_patch_input (hR : R.Conditions) {P : SquarePatch pos q}
    (hP : P ∈ R.patches) (j : Fin P.n) (jO : ∀ h ∈ R.oldAffected, Fin h.patch.n) :
    ∃ S : Finset Party, S.card ≤ 2 ∧ ∀ x ∈ P.sample j,
      (∀ h, ∀ hh : h ∈ R.oldAffected, x ∉ h.patch.sample (jO h hh)) → R.ownerOld x ∈ S := by
  obtain ⟨S, hS, hown⟩ := hR.old_owners P hP
  refine ⟨S, hS, fun x hx hfree => hown x (P.sample_subset_outer j hx) fun hH => ?_⟩
  obtain ⟨h, hh, hxh⟩ := R.mem_oldAffected_inner_of_mem_innerHoles hR hP
    (P.sample_subset_outer j hx) hH
  exact hfree h hh (h.patch.inner_subset_sample _ hxh)

/-- **Open outputs of a patch ket have at most two new owners.** For every choice of radii of
the affected new holes, the sites of a selected patch square that no selected new-hole square
receives have at most two new owners, by condition (iii).

Polynomial-PEPS manuscript, `05-frames.tex`, lines 300–302. -/
theorem exists_new_owners_of_patch_output (hR : R.Conditions) {P : SquarePatch pos q}
    (hP : P ∈ R.patches) (j : Fin P.n) (jN : ∀ h ∈ R.newAffected, Fin h.patch.n) :
    ∃ S : Finset Party, S.card ≤ 2 ∧ ∀ x ∈ P.sample j,
      (∀ h, ∀ hh : h ∈ R.newAffected, x ∉ h.patch.sample (jN h hh)) → R.ownerNew x ∈ S := by
  obtain ⟨S, hS, hown⟩ := hR.new_owners P hP
  refine ⟨S, hS, fun x hx hfree => hown x (P.sample_subset_outer j hx) fun hH => ?_⟩
  obtain ⟨h, hh, hxh⟩ := R.mem_newAffected_inner_of_mem_innerHoles hR hP
    (P.sample_subset_outer j hx) hH
  exact hfree h hh (h.patch.inner_subset_sample _ hxh)

/-- **Direct wires keep their owner.** For every choice of patch radii, a raw site in no
selected patch square has equal old and new owners, by condition (ii).

Polynomial-PEPS manuscript, `05-frames.tex`, lines 267–273. -/
theorem ownerOld_eq_ownerNew_of_direct (hR : R.Conditions) (jP : ∀ P ∈ R.patches, Fin P.n)
    {x : ι} (hx : x ∉ R.patchSquares jP) : R.ownerOld x = R.ownerNew x := by
  by_contra hne
  exact hx (R.innerUnion_subset_patchSquares jP (hR.changed_mem x hne))

/-- **Only the specified parties participate.** Every old and new raw owner of a site of a
selected patch square or of a selected affected-hole square belongs to the specified list of
parties, by condition (iv).

Polynomial-PEPS manuscript, `05-frames.tex`, lines 203–205 and 342–343. -/
theorem owners_mem_parties_of_mem_sample (hR : R.Conditions) {x : ι}
    (hx : (∃ P ∈ R.patches, ∃ j, x ∈ P.sample j) ∨
      (∃ h ∈ R.oldAffected ++ R.newAffected, ∃ j, x ∈ h.patch.sample j)) :
    R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties := by
  refine hR.raw_owners_mem x ?_
  rcases hx with ⟨P, hP, j, hxj⟩ | ⟨h, hh, j, hxj⟩
  · exact Or.inl (subset_footprint hP (P.sample_subset_outer j hxj))
  · exact Or.inr (subset_footprint (List.mem_map_of_mem hh) (h.patch.sample_subset_outer j hxj))

/-! ### The reference error of an approximation -/

/-- **Reference error of an approximation of the rewrite.** If `‖M_a - M‖ ≤ δ` and `‖Ω‖ ≤ 1`,
then `‖M_a Ω_{F_old} - Ω_{F_new}‖ ≤ δ + (m + r_old) ε`, under the hypotheses of
`norm_rewrite_refVec_sub_le`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 213–218 and 343–344. -/
theorem norm_act_refVec_sub_le_of_approx [NeZero q] (hR : R.AvoidsUntouched)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) {ε δ : ℝ}
    (hpatch : ∀ P ∈ R.patches, ‖act P.proj Ω - Ω‖ ≤ ε)
    (hold : ∀ h ∈ R.oldAffected, ‖act h.patch.proj Ω - Ω‖ ≤ ε)
    {Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ} (hMa : ‖Ma - R.rewrite‖ ≤ δ) :
    ‖act Ma (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤
      δ + (R.patches.length + R.oldAffected.length) * ε := by
  have hsplit : act Ma (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω =
      act (Ma - R.rewrite) (R.oldFrame.refVec Ω) +
        (act R.rewrite (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω) := by
    rw [act_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ (R.norm_rewrite_refVec_sub_le hR hpatch hold))
  calc ‖act (Ma - R.rewrite) (R.oldFrame.refVec Ω)‖
      ≤ ‖Ma - R.rewrite‖ * ‖R.oldFrame.refVec Ω‖ := norm_act_le _ _
    _ ≤ δ * 1 := mul_le_mul hMa ((R.oldFrame.norm_refVec_le Ω).trans hΩ) (norm_nonneg _)
        ((norm_nonneg _).trans hMa)
    _ = δ := mul_one δ

end SmallPatchRewrite

/-- **The error specialization of Lemma 6.3.** With `ε = L^{-60}` and `δ = L^{-30}` (the
choice `a = 30`), the reference error `δ + c ε` of a rewrite with `c = m + r_old` is at most
`L^{-20}` once `c + 1 ≤ L^{10}`; for a bounded number of patches and affected holes this holds
for all large `L`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 217–218 and 343–344. -/
theorem rewrite_error_le_inv_pow_twenty {L : ℝ} (hL : 1 ≤ L) {c : ℕ}
    (hc : (c + 1 : ℝ) ≤ L ^ 10) : (L ^ 30)⁻¹ + c * (L ^ 60)⁻¹ ≤ (L ^ 20)⁻¹ := by
  have hL0 : 0 < L := by linarith
  have h60 : (L ^ 60)⁻¹ ≤ (L ^ 30)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hL (by norm_num))
  calc (L ^ 30)⁻¹ + c * (L ^ 60)⁻¹ ≤ (L ^ 30)⁻¹ + c * (L ^ 30)⁻¹ := by gcongr
    _ = (c + 1) * (L ^ 30)⁻¹ := by ring
    _ ≤ L ^ 10 * (L ^ 30)⁻¹ := by gcongr
    _ = (L ^ 20)⁻¹ := by
      field_simp

/-! ### Rescaling and the choice of the truncation rank -/

section Rescale

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Rescaling restores contractivity.** If `‖M‖ ≤ 1` and `‖M' - M‖ ≤ δ / 2` with `δ ≥ 0`, then
`M_a = M' / (1 + δ / 2)` satisfies `‖M_a‖ ≤ 1` and `‖M_a - M‖ ≤ δ`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 335–341. -/
theorem norm_rescale_le {M M' : Matrix m n ℂ} (hM : ‖M‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ‖M' - M‖ ≤ δ / 2) :
    ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) • M'‖ ≤ 1 ∧ ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) • M' - M‖ ≤ δ := by
  have hc : (0 : ℝ) < 1 + δ / 2 := by linarith
  have hM' : ‖M'‖ ≤ 1 + δ / 2 := by
    calc ‖M'‖ = ‖(M' - M) + M‖ := by rw [sub_add_cancel]
      _ ≤ ‖M' - M‖ + ‖M‖ := norm_add_le _ _
      _ ≤ 1 + δ / 2 := by linarith
  have hnc : ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ)‖ = (1 + δ / 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  constructor
  · rw [norm_smul, hnc]
    calc (1 + δ / 2)⁻¹ * ‖M'‖ ≤ (1 + δ / 2)⁻¹ * (1 + δ / 2) :=
          mul_le_mul_of_nonneg_left hM' (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  · have hsplit : (((1 + δ / 2)⁻¹ : ℝ) : ℂ) • M' - M =
        (((1 + δ / 2)⁻¹ : ℝ) : ℂ) • (M' - M) - (((δ / 2) / (1 + δ / 2) : ℝ) : ℂ) • M := by
      rw [smul_sub, sub_sub, ← add_smul]
      congr 1
      have hr : (1 + δ / 2)⁻¹ + (δ / 2) / (1 + δ / 2) = 1 := by
        field_simp
      have : (((1 + δ / 2)⁻¹ : ℝ) : ℂ) + (((δ / 2) / (1 + δ / 2) : ℝ) : ℂ) = 1 := by
        exact_mod_cast hr
      rw [this, one_smul]
    rw [hsplit]
    have hn2 : ‖(((δ / 2) / (1 + δ / 2) : ℝ) : ℂ)‖ = (δ / 2) / (1 + δ / 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hc.le)]
    calc ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) • (M' - M) - (((δ / 2) / (1 + δ / 2) : ℝ) : ℂ) • M‖
        ≤ ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) • (M' - M)‖ + ‖(((δ / 2) / (1 + δ / 2) : ℝ) : ℂ) • M‖ :=
          norm_sub_le _ _
      _ ≤ (1 + δ / 2)⁻¹ * (δ / 2) + (δ / 2) / (1 + δ / 2) * 1 := by
          rw [norm_smul, norm_smul, hnc, hn2]
          exact add_le_add (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le))
            (mul_le_mul_of_nonneg_left hM (div_nonneg (by linarith) hc.le))
      _ = δ / (1 + δ / 2) := by field_simp; ring
      _ ≤ δ := div_le_self hδ (by linarith)

/-- **Assembling `M_a` from branchwise approximations.** Let `M = ∑_β M_β` be a contraction
with `N` branches, and let every branch operator have an approximation `M'_β` with
`‖M_β - M'_β‖ ≤ η`. If `N η ≤ δ / 2`, then `M_a = (∑_β M'_β) / (1 + δ / 2)` is a contraction with
`‖M_a - M‖ ≤ δ`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 331–341. -/
theorem norm_rescale_sum_le_of_branches {β : Type*} [Fintype β] {M : Matrix m n ℂ}
    (hM : ‖M‖ ≤ 1) (Mb Mb' : β → Matrix m n ℂ) (hsum : M = ∑ b, Mb b) {η δ : ℝ}
    (hδ : 0 ≤ δ) (hb : ∀ b, ‖Mb b - Mb' b‖ ≤ η) (hη : Fintype.card β * η ≤ δ / 2) :
    ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) • ∑ b, Mb' b‖ ≤ 1 ∧
      ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) • ∑ b, Mb' b - M‖ ≤ δ := by
  refine norm_rescale_le hM hδ ?_
  rw [hsum, ← Finset.sum_sub_distrib]
  calc ‖∑ b, (Mb' b - Mb b)‖ ≤ ∑ b, ‖Mb' b - Mb b‖ := norm_sum_le _ _
    _ ≤ ∑ _b : β, η := Finset.sum_le_sum fun b _ => by rw [norm_sub_rev]; exact hb b
    _ = Fintype.card β * η := by simp
    _ ≤ δ / 2 := hη

end Rescale

/-- An integer `k ≥ 1` with `N g / √k ≤ δ / 2`: the truncation rank in the proof of Lemma 6.3. -/
def truncationRank (N g δ : ℝ) : ℕ := ⌈(2 * N * g / δ) ^ 2⌉₊ + 1

theorem one_le_truncationRank (N g δ : ℝ) : 1 ≤ truncationRank N g δ :=
  Nat.le_add_left _ _

/-- **Choice of the truncation rank.** With `k = truncationRank N g δ`, the summed branch error
`N g / √k` is at most `δ / 2`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 331–334. -/
theorem truncationRank_spec {N g δ : ℝ} (hN : 0 ≤ N) (hg : 0 ≤ g) (hδ : 0 < δ) :
    N * (g / √(truncationRank N g δ)) ≤ δ / 2 := by
  set k := truncationRank N g δ
  have hk : (0 : ℝ) < k := by exact_mod_cast one_le_truncationRank N g δ
  have hsq : (2 * N * g / δ) ^ 2 ≤ k := by
    calc (2 * N * g / δ) ^ 2 ≤ ⌈(2 * N * g / δ) ^ 2⌉₊ := Nat.le_ceil _
      _ ≤ k := by simp [k, truncationRank]
  have hroot : 2 * N * g / δ ≤ √k := by
    rw [← Real.sqrt_sq (div_nonneg (by positivity) hδ.le)]
    exact Real.sqrt_le_sqrt hsq
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk
  rw [mul_div_assoc', div_le_div_iff₀ hsk (by norm_num : (0 : ℝ) < 2)]
  rw [div_le_iff₀ hδ] at hroot
  linarith

end TNLean.PEPS.EncodedFrame
