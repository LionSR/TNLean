/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PatchRewriteExpansion
import TNLean.PEPS.Approximation.SiteChainTruncation

/-!
# Branch networks of a small-patch rewrite

The second assertion of Lemma 6.3 `lem:small-rewrite` of the polynomial-PEPS manuscript
approximates the canonical rewrite `M = K_new P_m ⋯ P_1 K_oldᴴ` by a contraction `M_a` with
`‖M_a - M‖ ≤ L^{-a}` and a polynomial sum expansion. Its proof expands `M` into branches, reads
each branch as a tensor network of normalized bras and kets, truncates that network with
Lemma 6.2, and sums and rescales. This file carries out the network part and the assembly.

For a branch `(a, s, b)` the raw operator `R^{new}_a C_s (R^{old}_b)ᴴ` is the chain of the steps
`|0⟩⟨u'_r|` of the affected new holes, `|w_i⟩⟨w_i|` of the patch terms and `|u_t⟩⟨0|` of the
affected old holes (`branchRaw_eq_chainOp`). Under the four conditions of Lemma 6.3 only the bras
and kets of the patch terms have open legs (`mem_patchVertices_of_isOpen`), so there are at most
`2m` open-leg groups; the open input legs of a patch bra have at most two old owners and the open
output legs of a patch ket at most two new owners, all in the specified list
(`exists_owners_of_isOpen_inl`, `exists_owners_of_isOpen_inr`). Lemma 6.2 then approximates each
branch within `2m / √k` by at most `k ^ (2m)` product terms with coefficients of modulus at most
one, uniformly in the dimensions of the sites (`exists_branch_truncation`), and the rescaling of
`norm_rescale_sum_le_of_branches` gives `M_δ` (`exists_contractive_approx`).

**Scope restriction (monomial reading):** the last step of the proof of Lemma 6.3
(`05-frames.tex`, lines 306–316), reading each product term as a monomial allowed by Theorem 5.2,
is not formalized. `exists_contractive_approx` gives the product terms as explicit tensor products
of normalized vectors and covectors on the open-leg groups of the patch vertices (each group on at
most two parties of the specified list), of product zero vectors on the selected hole squares, of
tag basis vectors, and of identities (`SiteChain.termOp_apply`); their identification with the
operators of allowed monomials (`PairEffect.PartyChain`) on the registers of the frames, one per
site and per tag (`EncodedFrame.layoutRegs`, `EncodedFrame.layoutIso` in
`TNLean.PEPS.Approximation.FrameRegisters`), is not constructed. The number of terms is
bounded through the number `N` of branches only (`card_branch_le`); it becomes polynomial in `L`
with the cylinder-term bound of Proposition 4.1, which the patch data do not record, and bounded
numbers of patches and affected holes. Documented in
`docs/paper-gaps/polypeps_small_rewrite_monomials.tex`. Elimination: write each product term as
an allowed party chain on the registers of the frames, moving the registers of each open-leg group
in front with the reordering words of `TNLean.PEPS.Approximation.SiteRegisters` and
`TNLean.PEPS.Approximation.RegisterReordering`, placing the grouped factors with
`EncodedFrame.layoutIso_place` (`TNLean.PEPS.Approximation.FrameRegisters`), and reading the
explicit matrices with the front-register calculus (`PairEffect.eval_localMap`), and carry the
cylinder-term bound.

## Main definitions

* `EncodedFrame.SquarePatch.encStep`, `EncodedFrame.SquarePatch.patchStep`,
  `EncodedFrame.SquarePatch.decStep`: the rank-one steps of a cylinder term.
* `EncodedFrame.SmallPatchRewrite.branchSteps`, `EncodedFrame.SmallPatchRewrite.branchChain`: the
  steps of a branch.
* `EncodedFrame.SmallPatchRewrite.patchVertices`: the bra and ket vertices of the patch terms.

## Main results

* `EncodedFrame.SmallPatchRewrite.branchRaw_eq_chainOp`: a branch is a chain of rank-one steps.
* `EncodedFrame.SmallPatchRewrite.mem_patchVertices_of_isOpen`,
  `EncodedFrame.SmallPatchRewrite.exists_owners_of_isOpen_inl`,
  `EncodedFrame.SmallPatchRewrite.exists_owners_of_isOpen_inr`: the open-leg groups.
* `EncodedFrame.SmallPatchRewrite.exists_branch_truncation`: the truncation of one branch.
* `EncodedFrame.SmallPatchRewrite.exists_contractive_approx`: the contraction `M_δ` with
  `‖M_δ - M‖ ≤ δ` and its expansion into product terms.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 214–217; proof lines 254–341.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open SiteChain WholeGroup

variable {ι : Type*} {q : ℕ}

/-! ### Chains given by lists

The chain of the steps of a list `L` is `L.get`, the head of the list being applied last. -/

section ThreeParts

variable (A B C : List (Step ι q))

theorem get_append₃_mem_left (i : Fin (A ++ B ++ C).length) (hi : (i : ℕ) < A.length) :
    (A ++ B ++ C).get i ∈ A := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hi]
  exact List.getElem_mem _

theorem get_append₃_mem_mid (i : Fin (A ++ B ++ C).length) (hi₁ : A.length ≤ i)
    (hi₂ : (i : ℕ) < A.length + B.length) : (A ++ B ++ C).get i ∈ B := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right hi₁]
  exact List.getElem_mem _

theorem get_append₃_mem_right (i : Fin (A ++ B ++ C).length) (hi : A.length + B.length ≤ i) :
    (A ++ B ++ C).get i ∈ C := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (by simp; omega)]
  exact List.getElem_mem _

theorem exists_get_append₃_eq_mid {s : Step ι q} (hs : s ∈ B) :
    ∃ i : Fin (A ++ B ++ C).length, A.length ≤ (i : ℕ) ∧ (i : ℕ) < A.length + B.length ∧
      (A ++ B ++ C).get i = s := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hs
  refine ⟨⟨A.length + p, by simp; omega⟩, by simp, by simp; omega, ?_⟩
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
  simp

theorem exists_get_append₃_eq_right {s : Step ι q} (hs : s ∈ C) :
    ∃ i : Fin (A ++ B ++ C).length, A.length + B.length ≤ (i : ℕ) ∧
      (A ++ B ++ C).get i = s := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hs
  refine ⟨⟨A.length + B.length + p, by simp; omega⟩, by simp, ?_⟩
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (by simp)]
  simp

theorem exists_get_append₃_eq_left {s : Step ι q} (hs : s ∈ A) :
    ∃ i : Fin (A ++ B ++ C).length, (i : ℕ) < A.length ∧ (A ++ B ++ C).get i = s := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hs
  refine ⟨⟨p, by simp; omega⟩, hp, ?_⟩
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hp]

end ThreeParts

/-! ### Tag blocks -/

theorem norm_stack_indicator_le_one {U m : Type*} [Fintype U] [Fintype m] [DecidableEq U]
    [DecidableEq m] (c : U) :
    ‖stack fun t : U => if t = c then (1 : Matrix m m ℂ) else 0‖ ≤ 1 := by
  refine IsIsometry.l2_opNorm_le_one ?_
  change (stack _)ᴴ * stack _ = 1
  rw [stack_conjTranspose_mul_stack, Finset.sum_eq_single c (fun t _ ht => by simp [ht])
    (by simp)]
  simp

theorem norm_tagLift_le {S T m : Type*} [Fintype S] [Fintype T] [Fintype m] [DecidableEq S]
    [DecidableEq T] [DecidableEq m] (a : S) (b : T) (Y : Matrix m m ℂ) :
    ‖tagLift a b Y‖ ≤ ‖Y‖ := by
  have h : tagLift a b Y = (stack fun t : S => if t = a then (1 : Matrix m m ℂ) else 0) * Y *
      (stack fun t : T => if t = b then (1 : Matrix m m ℂ) else 0)ᴴ := by
    ext x y
    rw [stack_mul_mul_stack_conjTranspose_apply]
    by_cases hx : x.1 = a <;> by_cases hy : y.1 = b <;> simp [tagLift, hx, hy]
  rw [h]
  refine (l2_opNorm_mul _ _).trans ?_
  rw [l2_opNorm_conjTranspose]
  refine (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)).trans ?_
  calc _ ≤ (1 * ‖Y‖) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right
        (norm_stack_indicator_le_one a) (norm_nonneg _)) (norm_stack_indicator_le_one b)
        (norm_nonneg _) (by positivity)
    _ = ‖Y‖ := by ring

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

theorem SquarePatch.exists_mem_sample_of_mem_tagSample (p : SquarePatch pos q) {t : p.Tag}
    {x : ι} (hx : x ∈ p.tagSample t) : ∃ j, x ∈ p.sample j := by
  rcases t with t | t
  · exact absurd hx (Finset.notMem_empty x)
  · exact ⟨t.1.1, hx⟩

variable [NeZero q]

theorem chainOp_get (L : List (Step ι q)) : chainOp L.get = (L.map Step.op).prod := by
  conv_rhs => rw [← List.ofFn_get L, List.map_ofFn]
  rfl

/-! ### Cylinder terms as rank-one steps -/

namespace SquarePatch

variable (p : SquarePatch pos q)

/-- The unit vector of a cylinder term: `v_{jℓ}` on `D_j` at a term `(j, ℓ)`, and the unit vector
on the one configuration of the empty square at the identity term of an empty outer sample. -/
def tagVec : (t : p.Tag) → EuclideanSpace ℂ (p.tagSample t → Fin q)
  | .inl _ => WithLp.toLp 2 (zeroVec ∅)
  | .inr s => p.vec s.1.1 s.1.2

theorem norm_tagVec (t : p.Tag) : ‖p.tagVec t‖ = 1 := by
  rcases t with t | t
  · exact Step.norm_zeroState (⟨∅, none, none⟩ : Step ι q)
  · exact p.norm_vec _ _

/-- The step `|0⟩⟨v|` of a hole encoding at a cylinder term. -/
def encStep (t : p.Tag) : Step ι q := ⟨p.tagSample t, none, some (p.tagVec t)⟩

/-- The step `|v⟩⟨v|` of a patch projector at a cylinder term. -/
def patchStep (t : p.Tag) : Step ι q := ⟨p.tagSample t, some (p.tagVec t), some (p.tagVec t)⟩

/-- The step `|v⟩⟨0|` of a hole decoding at a cylinder term. -/
def decStep (t : p.Tag) : Step ι q := ⟨p.tagSample t, some (p.tagVec t), none⟩

theorem siteLift_empty_zeroVec :
    siteLift (∅ : Finset ι)
      (vecMulVec (zeroVec (q := q) (∅ : Finset ι))
        (star (zeroVec (q := q) (∅ : Finset ι)))) = 1 := by
  have h : vecMulVec (zeroVec (q := q) (∅ : Finset ι))
      (star (zeroVec (q := q) (∅ : Finset ι))) = 1 := by
    ext a b
    have hab : a = b := funext fun x => absurd x.2 (Finset.notMem_empty _)
    have ha0 : a = 0 := funext fun x => absurd x.2 (Finset.notMem_empty _)
    subst hab ha0
    simp [vecMulVec_apply, zeroVec]
  rw [h, siteLift, embedOp_one]

theorem branch_eq_op (t : p.Tag) : p.branch t = (p.encStep t).op := by
  rcases t with t | t
  · exact siteLift_empty_zeroVec.symm
  · rfl

theorem cyl_eq_op (t : p.Tag) : p.cyl t = (p.patchStep t).op := by
  rcases t with t | t
  · exact siteLift_empty_zeroVec.symm
  · rfl

theorem branch_conjTranspose_eq_op (t : p.Tag) : (p.branch t)ᴴ = (p.decStep t).op := by
  rw [branch_eq_op, Step.op, Step.op, siteLift_conjTranspose, conjTranspose_vecMulVec, star_star]
  rfl

end SquarePatch

/-! ### The steps of a branch -/

variable {Party : Type*}

/-- The encoding steps `|0⟩⟨v|` of a list of holes at a tag configuration, in the order of the
list. -/
def encSteps : (l : List (Hole pos q Party)) → TagSpace l → List (Step ι q)
  | [], _ => []
  | h :: l, t => h.patch.encStep t.1 :: encSteps l t.2

/-- The decoding steps `|v⟩⟨0|` of a list of holes at a tag configuration, in reverse order. -/
def decSteps : (l : List (Hole pos q Party)) → TagSpace l → List (Step ι q)
  | [], _ => []
  | h :: l, t => decSteps l t.2 ++ [h.patch.decStep t.1]

/-- The steps `|v⟩⟨v|` of a list of patches at a choice of cylinder terms. -/
def patchSteps : (l : List (SquarePatch pos q)) → PatchTags l → List (Step ι q)
  | [], _ => []
  | p :: l, s => p.patchStep s.1 :: patchSteps l s.2

theorem rawProd_eq_prod : (l : List (Hole pos q Party)) → (t : TagSpace l) →
    rawProd l t = ((encSteps l t).map Step.op).prod
  | [], _ => rfl
  | h :: l, t => by
    rw [rawProd, encSteps, List.map_cons, List.prod_cons, h.patch.branch_eq_op,
      rawProd_eq_prod l t.2]

theorem rawProd_conjTranspose_eq_prod : (l : List (Hole pos q Party)) → (t : TagSpace l) →
    (rawProd l t)ᴴ = ((decSteps l t).map Step.op).prod
  | [], _ => conjTranspose_one
  | h :: l, t => by
    rw [rawProd, conjTranspose_mul, rawProd_conjTranspose_eq_prod l t.2, decSteps,
      List.map_append, List.prod_append, h.patch.branch_conjTranspose_eq_op]
    simp

theorem cylProd_eq_prod : (l : List (SquarePatch pos q)) → (s : PatchTags l) →
    cylProd l s = ((patchSteps l s).map Step.op).prod
  | [], _ => rfl
  | p :: l, s => by
    rw [cylProd, patchSteps, List.map_cons, List.prod_cons, p.cyl_eq_op, cylProd_eq_prod l s.2]

theorem length_patchSteps : (l : List (SquarePatch pos q)) → (s : PatchTags l) →
    (patchSteps l s).length = l.length
  | [], _ => rfl
  | _ :: l, s => by rw [patchSteps, List.length_cons, length_patchSteps l s.2, List.length_cons]

theorem mem_holeSquares_iff_encSteps {x : ι} : (l : List (Hole pos q Party)) → (t : TagSpace l) →
    (x ∈ holeSquares l t ↔ ∃ s ∈ encSteps l t, x ∈ s.sites)
  | [], _ => by simp [holeSquares, encSteps]
  | h :: l, t => by
    simp only [holeSquares, encSteps, Set.mem_union, Finset.mem_coe, List.mem_cons,
      exists_eq_or_imp, mem_holeSquares_iff_encSteps l t.2]
    rfl

theorem mem_holeSquares_iff_decSteps {x : ι} : (l : List (Hole pos q Party)) → (t : TagSpace l) →
    (x ∈ holeSquares l t ↔ ∃ s ∈ decSteps l t, x ∈ s.sites)
  | [], _ => by simp [holeSquares, decSteps]
  | h :: l, t => by
    simp only [holeSquares, decSteps, Set.mem_union, Finset.mem_coe, List.mem_append,
      List.mem_singleton, mem_holeSquares_iff_decSteps l t.2]
    constructor
    · rintro (hx | ⟨s, hs, hx⟩)
      · exact ⟨_, Or.inr rfl, hx⟩
      · exact ⟨s, Or.inl hs, hx⟩
    · rintro ⟨s, hs | rfl, hx⟩
      · exact Or.inr ⟨s, hs, hx⟩
      · exact Or.inl hx

theorem mem_patchSquares_iff {x : ι} : (l : List (SquarePatch pos q)) → (s : PatchTags l) →
    (x ∈ patchSquares l s ↔ ∃ st ∈ patchSteps l s, x ∈ st.sites)
  | [], _ => by simp [patchSquares, patchSteps]
  | p :: l, s => by
    simp only [patchSquares, patchSteps, Set.mem_union, Finset.mem_coe, List.mem_cons,
      exists_eq_or_imp, mem_patchSquares_iff l s.2]
    rfl

theorem ket_eq_none_of_mem_encSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ encSteps l t → s.ket = none
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · rfl
    · exact ket_eq_none_of_mem_encSteps l t.2 hs

theorem bra_eq_none_of_mem_decSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ decSteps l t → s.bra = none
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_append.mp hs with hs | hs
    · exact bra_eq_none_of_mem_decSteps l t.2 hs
    · rw [List.mem_singleton.mp hs]
      rfl

theorem exists_of_mem_patchSteps {s : Step ι q} : (l : List (SquarePatch pos q)) →
    (σ : PatchTags l) → s ∈ patchSteps l σ →
      ∃ P ∈ l, ∃ j : P.Tag, s.sites = P.tagSample j ∧ s.ket.isSome ∧ s.bra.isSome
  | [], _, hs => absurd hs List.not_mem_nil
  | p :: l, σ, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨p, List.mem_cons_self, σ.1, rfl, rfl, rfl⟩
    · obtain ⟨P, hP, j, hj⟩ := exists_of_mem_patchSteps l σ.2 hs
      exact ⟨P, List.mem_cons_of_mem _ hP, j, hj⟩

theorem norm_le_one_of_mem_encSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ encSteps l t → ‖s.ketVec‖ ≤ 1 ∧ ‖s.braVec‖ ≤ 1
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨Step.norm_ketVec_le_one fun v hv => absurd hv (Option.not_mem_none v),
        Step.norm_braVec_le_one fun v hv => ?_⟩
      obtain rfl := Option.some_injective _ hv.symm
      exact (h.patch.norm_tagVec _).le
    · exact norm_le_one_of_mem_encSteps l t.2 hs

theorem norm_le_one_of_mem_decSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ decSteps l t → ‖s.ketVec‖ ≤ 1 ∧ ‖s.braVec‖ ≤ 1
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_append.mp hs with hs | hs
    · exact norm_le_one_of_mem_decSteps l t.2 hs
    · rw [List.mem_singleton.mp hs]
      refine ⟨Step.norm_ketVec_le_one fun v hv => ?_,
        Step.norm_braVec_le_one fun v hv => absurd hv (Option.not_mem_none v)⟩
      obtain rfl := Option.some_injective _ hv.symm
      exact (h.patch.norm_tagVec _).le

theorem norm_le_one_of_mem_patchSteps {s : Step ι q} : (l : List (SquarePatch pos q)) →
    (σ : PatchTags l) → s ∈ patchSteps l σ → ‖s.ketVec‖ ≤ 1 ∧ ‖s.braVec‖ ≤ 1
  | [], _, hs => absurd hs List.not_mem_nil
  | p :: l, σ, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨Step.norm_ketVec_le_one fun v hv => ?_, Step.norm_braVec_le_one fun v hv => ?_⟩
      · obtain rfl := Option.some_injective _ hv.symm
        exact (p.norm_tagVec _).le
      · obtain rfl := Option.some_injective _ hv.symm
        exact (p.norm_tagVec _).le
    · exact norm_le_one_of_mem_patchSteps l σ.2 hs

/-! ### The network of a branch -/

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

/-- The steps of a branch `(a, s, b)`, in the order of the product `R^{new}_a C_s (R^{old}_b)ᴴ`:
the encodings `|0⟩⟨u'_r|` of the affected new holes, the cylinder terms `|w_i⟩⟨w_i|` of the
patches, and the decodings `|u_t⟩⟨0|` of the affected old holes, the last applied first.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 257–266. -/
def branchSteps (β : R.Branch) : List (Step ι q) :=
  encSteps R.newAffected β.1 ++ patchSteps R.patches β.2.1 ++ decSteps R.oldAffected β.2.2

/-- The chain of steps of a branch. -/
abbrev branchChain (β : R.Branch) : Fin (R.branchSteps β).length → Step ι q :=
  (R.branchSteps β).get

/-- **The raw branch operator is the chain operator of its steps.** -/
theorem branchRaw_eq_chainOp (β : R.Branch) : R.branchRaw β = chainOp (R.branchChain β) := by
  rw [chainOp_get, branchSteps, List.map_append, List.map_append, List.prod_append,
    List.prod_append, branchRaw, rawProd_eq_prod, cylProd_eq_prod, rawProd_conjTranspose_eq_prod]

theorem norm_vec_le_one_of_mem_branchSteps (β : R.Branch) {s : Step ι q}
    (hs : s ∈ R.branchSteps β) : ‖s.ketVec‖ ≤ 1 ∧ ‖s.braVec‖ ≤ 1 := by
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact norm_le_one_of_mem_encSteps _ _ hs
    · exact norm_le_one_of_mem_patchSteps _ _ hs
  · exact norm_le_one_of_mem_decSteps _ _ hs

/-- The indices of the patch steps of a branch. -/
def patchIndices (β : R.Branch) : Finset (Fin (R.branchSteps β).length) :=
  Finset.univ.filter fun i => (encSteps R.newAffected β.1).length ≤ (i : ℕ) ∧
    (i : ℕ) < (encSteps R.newAffected β.1).length + R.patches.length

/-- The bra and ket vertices of the patch steps of a branch. -/
def patchVertices (β : R.Branch) :
    Finset (Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) :=
  (R.patchIndices β).image Sum.inl ∪ (R.patchIndices β).image Sum.inr

theorem card_patchVertices_le (β : R.Branch) :
    (R.patchVertices β).card ≤ 2 * R.patches.length := by
  have hI : (R.patchIndices β).card ≤ R.patches.length := by
    have h := Finset.card_le_card_of_injOn
      (fun i : Fin (R.branchSteps β).length => (i : ℕ) - (encSteps R.newAffected β.1).length)
      (s := R.patchIndices β) (t := Finset.range R.patches.length)
      (fun i hi => by
        simp only [patchIndices, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] at hi
        simp only [Finset.coe_range, Set.mem_Iio]
        omega)
      (fun i hi j hj hij => by
        simp only [patchIndices, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] at hi hj
        exact Fin.ext (by simp only at hij; omega))
    simpa using h
  calc (R.patchVertices β).card
      ≤ ((R.patchIndices β).image Sum.inl).card + ((R.patchIndices β).image Sum.inr).card :=
        Finset.card_union_le _ _
    _ ≤ (R.patchIndices β).card + (R.patchIndices β).card :=
        add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ 2 * R.patches.length := by omega

/-- **Only patch vertices have open legs.** In every branch, under the conditions of Lemma 6.3,
an open input leg belongs to the bra of a patch term and an open output leg to the ket of a
patch term: decoded old-hole kets have no open output legs, new-hole bras have no open input
legs, and the product zero vectors of the hole encodings carry no open legs.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 282–302. -/
theorem mem_patchIndices_of_isOpen (hR : R.Conditions) (β : R.Branch)
    {v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length} {x : ι}
    (h : IsOpen (R.branchChain β) v x) : (Sum.elim id id v) ∈ R.patchIndices β := by
  set E := encSteps R.newAffected β.1
  set P := patchSteps R.patches β.2.1
  set D := decSteps R.oldAffected β.2.2
  have hP : P.length = R.patches.length := length_patchSteps _ _
  simp only [patchIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases v with j | i
  · obtain ⟨hx, hE, hb⟩ := h
    have hj2 : (j : ℕ) < E.length + P.length := by
      by_contra hc
      have := bra_eq_none_of_mem_decSteps _ _ (get_append₃_mem_right E P D j (by omega))
      change ((E ++ P ++ D).get j).bra.isSome = true at hb
      rw [this] at hb
      exact absurd hb (by simp)
    have hj1 : E.length ≤ (j : ℕ) := by
      by_contra hc
      have hmem := get_append₃_mem_left E P D j (by omega)
      have hxh : x ∈ holeSquares R.newAffected β.1 :=
        (mem_holeSquares_iff_encSteps _ _).mpr ⟨_, hmem, hx⟩
      obtain ⟨s', hs', hxs'⟩ :=
        (mem_patchSquares_iff _ _).mp (R.newSample_subset_patchSquares hR β.2.1 β.1 hxh)
      obtain ⟨i', hi'1, -, hi'⟩ := exists_get_append₃_eq_mid E P D hs'
      exact hE ⟨i', Fin.lt_def.mpr (by omega), by
        change x ∈ ((E ++ P ++ D).get i').sites
        rw [hi']
        exact hxs'⟩
    exact ⟨hj1, hP ▸ hj2⟩
  · obtain ⟨hx, hL, hk⟩ := h
    have hi1 : E.length ≤ (i : ℕ) := by
      by_contra hc
      have := ket_eq_none_of_mem_encSteps _ _ (get_append₃_mem_left E P D i (by omega))
      change ((E ++ P ++ D).get i).ket.isSome = true at hk
      rw [this] at hk
      exact absurd hk (by simp)
    have hi2 : (i : ℕ) < E.length + P.length := by
      by_contra hc
      have hmem := get_append₃_mem_right E P D i (by omega)
      have hxh : x ∈ holeSquares R.oldAffected β.2.2 :=
        (mem_holeSquares_iff_decSteps _ _).mpr ⟨_, hmem, hx⟩
      obtain ⟨s', hs', hxs'⟩ :=
        (mem_patchSquares_iff _ _).mp (R.oldSample_subset_patchSquares hR β.2.1 β.2.2 hxh)
      obtain ⟨i', -, hi'2, hi'⟩ := exists_get_append₃_eq_mid E P D hs'
      exact hL ⟨i', Fin.lt_def.mpr (by omega), by
        change x ∈ ((E ++ P ++ D).get i').sites
        rw [hi']
        exact hxs'⟩
    exact ⟨hi1, hP ▸ hi2⟩

theorem mem_patchVertices_of_isOpen (hR : R.Conditions) (β : R.Branch)
    {v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length} {x : ι}
    (h : IsOpen (R.branchChain β) v x) : v ∈ R.patchVertices β := by
  have hv := R.mem_patchIndices_of_isOpen hR β h
  rcases v with j | i
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)

/-- **Open input legs have at most two old owners.** The open input legs of a bra vertex of a
branch lie at sites of the selected square of one patch term that no selected old-hole square
consumes; by condition (iii) their old owners form a set of at most two parties, and by
condition (iv) all their owners belong to the specified list.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 292–305. -/
theorem exists_owners_of_isOpen_inl (hR : R.Conditions) (β : R.Branch)
    (j : Fin (R.branchSteps β).length) :
    ∃ S : Finset Party, S.card ≤ 2 ∧ ∀ x, IsOpen (R.branchChain β) (.inl j) x →
      R.ownerOld x ∈ S ∧ R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties := by
  by_cases hj : ∃ x, IsOpen (R.branchChain β) (.inl j) x
  · obtain ⟨x₀, hx₀⟩ := hj
    have hrange := R.mem_patchIndices_of_isOpen hR β hx₀
    simp only [patchIndices, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inl,
      id] at hrange
    set E := encSteps R.newAffected β.1
    set P := patchSteps R.patches β.2.1
    set D := decSteps R.oldAffected β.2.2
    have hP : P.length = R.patches.length := length_patchSteps _ _
    obtain ⟨Q, hQ, t, hsites, -, -⟩ :=
      exists_of_mem_patchSteps _ _ (get_append₃_mem_mid E P D j hrange.1 (by omega))
    obtain ⟨S, hS, hown⟩ := R.exists_old_owners_of_patch_input hR hQ t β.2.2
    refine ⟨S, hS, fun x hx => ?_⟩
    have hxQ : x ∈ Q.tagSample t := by
      have := hx.1
      change x ∈ ((E ++ P ++ D).get j).sites at this
      rwa [hsites] at this
    refine ⟨hown x hxQ fun hxh => ?_, R.owners_mem_parties_of_mem_sample hR
      (Or.inl ⟨Q, hQ, Q.exists_mem_sample_of_mem_tagSample hxQ⟩)⟩
    obtain ⟨s', hs', hxs'⟩ := (mem_holeSquares_iff_decSteps _ _).mp hxh
    obtain ⟨i', hi'1, hi'⟩ := exists_get_append₃_eq_right E P D hs'
    exact hx.2.1 ⟨i', Fin.lt_def.mpr (by omega), by
      change x ∈ ((E ++ P ++ D).get i').sites
      rw [hi']
      exact hxs'⟩
  · exact ⟨∅, by simp, fun x hx => absurd ⟨x, hx⟩ hj⟩

/-- **Open output legs have at most two new owners.** The open output legs of a ket vertex of a
branch lie at sites of the selected square of one patch term that no selected new-hole square
receives; by condition (iii) their new owners form a set of at most two parties, and by
condition (iv) all their owners belong to the specified list.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 300–305. -/
theorem exists_owners_of_isOpen_inr (hR : R.Conditions) (β : R.Branch)
    (i : Fin (R.branchSteps β).length) :
    ∃ S : Finset Party, S.card ≤ 2 ∧ ∀ x, IsOpen (R.branchChain β) (.inr i) x →
      R.ownerNew x ∈ S ∧ R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties := by
  by_cases hi : ∃ x, IsOpen (R.branchChain β) (.inr i) x
  · obtain ⟨x₀, hx₀⟩ := hi
    have hrange := R.mem_patchIndices_of_isOpen hR β hx₀
    simp only [patchIndices, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inr,
      id] at hrange
    set E := encSteps R.newAffected β.1
    set P := patchSteps R.patches β.2.1
    set D := decSteps R.oldAffected β.2.2
    have hP : P.length = R.patches.length := length_patchSteps _ _
    obtain ⟨Q, hQ, t, hsites, -, -⟩ :=
      exists_of_mem_patchSteps _ _ (get_append₃_mem_mid E P D i hrange.1 (by omega))
    obtain ⟨S, hS, hown⟩ := R.exists_new_owners_of_patch_output hR hQ t β.1
    refine ⟨S, hS, fun x hx => ?_⟩
    have hxQ : x ∈ Q.tagSample t := by
      have := hx.1
      change x ∈ ((E ++ P ++ D).get i).sites at this
      rwa [hsites] at this
    refine ⟨hown x hxQ fun hxh => ?_, R.owners_mem_parties_of_mem_sample hR
      (Or.inl ⟨Q, hQ, Q.exists_mem_sample_of_mem_tagSample hxQ⟩)⟩
    obtain ⟨s', hs', hxs'⟩ := (mem_holeSquares_iff_encSteps _ _).mp hxh
    obtain ⟨i', hi'1, hi'⟩ := exists_get_append₃_eq_left E P D hs'
    exact hx.2.1 ⟨i', Fin.lt_def.mpr (by omega), by
      change x ∈ ((E ++ P ++ D).get i').sites
      rw [hi']
      exact hxs'⟩
  · exact ⟨∅, by simp, fun x hx => absurd ⟨x, hx⟩ hi⟩

/-- **Truncation of one branch (Lemma 6.2 applied to the branch network).** Under the conditions
of Lemma 6.3, for every branch and every `k ≥ 1` there are orthonormal families of at most `k`
vectors on the open-leg groups of the branch network and coefficients of modulus at most one
such that the raw branch operator `R^{new}_a C_s (R^{old}_b)ᴴ` differs in operator norm by at
most `2m / √k` from the sum of the corresponding product terms, of which there are at most
`k ^ (2m)`. The bound does not depend on the dimensions of the sites.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 306–329. -/
theorem exists_branch_truncation (hR : R.Conditions) (β : R.Branch) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (r : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length → ℕ)
      (e : (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r v) →
        EuclideanSpace ℂ (Group (R.branchChain β) v))
      (c : ((v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r v)) → ℂ),
      (∀ v, r v ≤ k) ∧ (∀ v, Orthonormal ℂ (e v)) ∧ (∀ i, ‖c i‖ ≤ 1) ∧
      Fintype.card ((v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) →
        Fin (r v)) ≤ k ^ (2 * R.patches.length) ∧
      ‖R.branchRaw β - ∑ i, c i • termOp (R.branchChain β) e i‖ ≤
        ((2 * R.patches.length : ℕ) : ℝ) / √k := by
  have hnorm := fun i : Fin (R.branchSteps β).length =>
    R.norm_vec_le_one_of_mem_branchSteps β (List.getElem_mem (l := R.branchSteps β) i.2)
  obtain ⟨r, e, c, hr, he, hc, hcard, herr⟩ := exists_chainOp_truncation (R.branchChain β)
    (fun i => (hnorm i).1) (fun i => (hnorm i).2) (R.patchVertices β)
    (fun v hv x hx => hv (R.mem_patchVertices_of_isOpen hR β hx)) k hk
  refine ⟨r, e, c, hr, he, hc, hcard.trans (Nat.pow_le_pow_right hk
    (R.card_patchVertices_le β)), ?_⟩
  rw [branchRaw_eq_chainOp]
  exact herr.trans (div_le_div_of_nonneg_right (by exact_mod_cast R.card_patchVertices_le β)
    (Real.sqrt_nonneg _))

omit [NeZero q] in
theorem liftBranch_sub (β : R.Branch) (Y Y' : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    R.liftBranch β Y - R.liftBranch β Y' = R.liftBranch β (Y - Y') := by
  ext x y
  simp only [liftBranch, tagLift, reindex_apply, submatrix_apply, Matrix.sub_apply,
    kroneckerMap_apply, of_apply]
  split_ifs <;> ring

omit [NeZero q] in
theorem norm_liftBranch_le (β : R.Branch) (Y : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    ‖R.liftBranch β Y‖ ≤ ‖Y‖ :=
  (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_kronecker_one_le _).trans
    (norm_tagLift_le _ _ _))

/-- **Lemma 6.3, approximation of the rewrite by product terms.** Under the four conditions of
Lemma 6.3, for every `δ > 0` (for instance `δ = L^{-a}`) let `N` be the number of branches,
`m` the number of additional patches, and `k = ⌈(4 N m / δ)²⌉ + 1` the truncation rank. For
every branch there are orthonormal families of at most `k` vectors on the open-leg groups of its
network and coefficients of modulus at most one, at most `k ^ (2m)` of them, such that
`M_δ = (1 + δ / 2)⁻¹ ∑_β |a⟩⟨b| ⊗ (∑_i c_{β,i} T_{β,i}) ⊗ 1` is a contraction with
`‖M_δ - M‖ ≤ δ`. Each product term `T_{β,i}` is the tensor product of normalized vectors on the
open output legs of the patch kets and normalized covectors on the open input legs of the patch
bras of the branch (`mem_patchVertices_of_isOpen`), each group on at most two parties of the
specified list (`exists_owners_of_isOpen_inl`, `exists_owners_of_isOpen_inr`), of the product
zero vectors of the hole encodings, and of the identity on the sites outside the selected patch
squares (`termOp_apply`).

The reading of each product term as an allowed monomial of Theorem 5.2 on the registers of the
frames, and a polynomial bound on `N`, are not part of this statement; see the scope restriction
in the module docstring.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 214–217;
proof lines 254–341. -/
theorem exists_contractive_approx (hR : R.Conditions) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : (β : R.Branch) → Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length → ℕ)
      (e : (β : R.Branch) → (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) →
        Fin (r β v) → EuclideanSpace ℂ (Group (R.branchChain β) v))
      (c : (β : R.Branch) →
        ((v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r β v)) → ℂ),
      (∀ β v, r β v ≤
        truncationRank (Fintype.card R.Branch) ((2 * R.patches.length : ℕ) : ℝ) δ) ∧
      (∀ β v, Orthonormal ℂ (e β v)) ∧ (∀ β i, ‖c β i‖ ≤ 1) ∧
      (∀ β, Fintype.card ((v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) →
        Fin (r β v)) ≤ truncationRank (Fintype.card R.Branch) ((2 * R.patches.length : ℕ) : ℝ)
          δ ^ (2 * R.patches.length)) ∧
      ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) •
          ∑ β, R.liftBranch β (∑ i, c β i • termOp (R.branchChain β) (e β) i)‖ ≤ 1 ∧
      ‖(((1 + δ / 2)⁻¹ : ℝ) : ℂ) •
          ∑ β, R.liftBranch β (∑ i, c β i • termOp (R.branchChain β) (e β) i) - R.rewrite‖ ≤
        δ := by
  set k := truncationRank (Fintype.card R.Branch) ((2 * R.patches.length : ℕ) : ℝ) δ
  have hk : 1 ≤ k := one_le_truncationRank _ _ _
  choose r e c hr he hc hcard herr using fun β => R.exists_branch_truncation hR β k hk
  obtain ⟨h1, h2⟩ := norm_rescale_sum_le_of_branches R.norm_rewrite_le_one
    (fun β => R.liftBranch β (R.branchRaw β))
    (fun β => R.liftBranch β (∑ i, c β i • termOp (R.branchChain β) (e β) i))
    R.rewrite_eq_sum_branch hδ.le
    (η := ((2 * R.patches.length : ℕ) : ℝ) / √k)
    (fun β => by
      rw [liftBranch_sub]
      exact (R.norm_liftBranch_le β _).trans (herr β))
    (truncationRank_spec (by positivity) (by positivity) hδ)
  exact ⟨r, e, c, hr, he, hc, hcard, h1, h2⟩

end SmallPatchRewrite

end TNLean.PEPS.EncodedFrame
