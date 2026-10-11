/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.RankOneBlocks
import TNLean.PEPS.Approximation.SiteChainTruncation

/-!
# Product terms of a chain of site operators as products of rank-one blocks

The whole-group truncation of a chain of rank-one site steps
(`TNLean.PEPS.Approximation.SiteChainTruncation`) approximates the chain operator by product terms
`termOp`: tensor products of one vector on the open output legs of each ket, one covector on the
open input legs of each bra, product zero vectors at the fixed legs, and identities. This file
writes such a product term as an ordered product of rank-one blocks
(`TNLean.PEPS.Approximation.RankOneBlocks`), each of which is an allowed monomial on the registers
of a frame:

* the bra blocks `|0⟩⟨w_j|`, one per bra vertex, on its open input legs;
* the one-site blocks `|0⟩⟨0|_x`, one per site touched by the chain;
* the ket blocks `|v_i⟩⟨0|`, one per ket vertex, on its open output legs.

Read from right to left, the bra blocks consume the open inputs and leave zeros, the one-site
blocks impose the fixed input zeros and leave zeros on every touched site, and the ket blocks
prepare the open outputs; the fixed output zeros remain (`SiteChain.termOp_eq_smul_prod`). A
vertex without open legs contributes a scalar of modulus at most one.

On the registers of a frame, the one-site blocks may change the owner of their site
(`EncodedFrame.exists_zeroChain`), and a block on a group of sites with at most two owners is
an allowed monomial using only these owners (`EncodedFrame.exists_groupBlock`).

## Main definitions

* `EncodedFrame.zeroBlock`, `EncodedFrame.emptyBlock`: the one-site zero block and the trivial
  block.

## Main results

* `EncodedFrame.exists_chain_listProd`: a product of operators of monomials on one layout.
* `EncodedFrame.exists_zeroChain`: the one-site zero blocks of a list of sites, changing owners.
* `EncodedFrame.exists_groupBlock`: a block on a group of sites with at most two owners.
* `SiteChain.termOp_eq_smul_prod`: a product term as a scalar times a product of blocks.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 262–273 (factoring out the tag maps, the zero bras and kets and the
  direct wires) and 306–316 (the product terms as allowed monomials).

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Particular blocks -/

section Blocks

variable [NeZero q]

/-- The block of one site `x` carrying `|0⟩⟨0|`. -/
def zeroBlock (x : ι) : RankOneBlock ι q :=
  ⟨{x}, {x}ᶜ, disjoint_compl_right, zeroPair _ _, zeroPair _ _⟩

theorem zeroBlock_ketAt (x : ι) (c : ι → Fin q) :
    (zeroBlock x).ketAt c = if c x = 0 then 1 else 0 :=
  (zeroPair_apply _ _ disjoint_compl_right c).trans (by simp)

theorem zeroBlock_braAt (x : ι) (c : ι → Fin q) :
    (zeroBlock x).braAt c = if c x = 0 then 1 else 0 :=
  zeroBlock_ketAt x c

/-- The trivial block, with no site; its operator is the identity. -/
def emptyBlock : RankOneBlock ι q :=
  ⟨∅, Finset.univ, Finset.disjoint_empty_left _, zeroPair _ _, zeroPair _ _⟩

theorem emptyBlock_ketAt (c : ι → Fin q) : (emptyBlock : RankOneBlock ι q).ketAt c = 1 :=
  (zeroPair_apply _ _ (Finset.disjoint_empty_left _) c).trans (by simp)

theorem emptyBlock_braAt (c : ι → Fin q) : (emptyBlock : RankOneBlock ι q).braAt c = 1 :=
  emptyBlock_ketAt c

theorem emptyBlock_op : (emptyBlock : RankOneBlock ι q).op = 1 := by
  ext c' c
  rw [RankOneBlock.op_apply, emptyBlock_ketAt, emptyBlock_braAt, Matrix.one_apply]
  have h : (∀ x ∈ (emptyBlock : RankOneBlock ι q).E, c' x = c x) ↔ c' = c :=
    ⟨fun h => funext fun x => h x (Finset.mem_univ x), fun h x _ => congrFun h x⟩
  simp only [h, star_one, mul_one]

end Blocks

/-! ### Products of monomials on one layout -/

section ListProd

variable {Party : Type}

theorem prod_map_one_kronecker {κ τ : Type} [Fintype κ] [DecidableEq κ] [Fintype τ]
    [DecidableEq τ] {γ : Type} (B : γ → Matrix τ τ ℂ) :
    (ks : List γ) → (ks.map fun k => (1 : Matrix κ κ ℂ) ⊗ₖ B k).prod =
      (1 : Matrix κ κ ℂ) ⊗ₖ (ks.map B).prod
  | [] => by simp
  | k :: ks => by
      rw [List.map_cons, List.prod_cons, prod_map_one_kronecker B ks, List.map_cons,
        List.prod_cons, ← mul_kronecker_mul, one_mul]

/-- **A product of monomial operators on one layout.** If each operator `A k` of a list is the
operator of an allowed monomial on the layout `L`, in the coordinates `iso`, using only the
parties of `S`, then so is the product `A k₁ ⋯ A k_r`, with the pair sources and pair effects
added up. -/
theorem exists_chain_listProd {L : Layout Party} {κ : Type} [Fintype κ] [DecidableEq κ]
    (iso : Mem L ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ) (S : Set Party) {γ : Type}
    (A : γ → Matrix κ κ ℂ) (src eff : γ → ℕ) : (ks : List γ) →
    (∀ k ∈ ks, ∃ M : PartyChain L L, M.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount ≤ src k ∧
      M.toEffectChain.effectCount ≤ eff k ∧
      ∀ z, iso (M.toEffectChain.eval z) = act (A k) (iso z)) →
    ∃ M : PartyChain L L, M.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount ≤ (ks.map src).sum ∧
      M.toEffectChain.effectCount ≤ (ks.map eff).sum ∧
      ∀ z, iso (M.toEffectChain.eval z) = act (ks.map A).prod (iso z)
  | [], _ => ⟨.final (.id L), trivial, trivial, le_rfl, le_rfl, fun z => by
      simp only [List.map_nil, List.prod_nil, act_one]
      rfl⟩
  | k :: ks, h => by
      obtain ⟨M, h₁, h₂, h₃, h₄, h₅⟩ :=
        exists_chain_listProd iso S A src eff ks fun k' hk' => h k' (List.mem_cons_of_mem _ hk')
      obtain ⟨Mk, k₁, k₂, k₃, k₄, k₅⟩ := h k List.mem_cons_self
      obtain ⟨a₁, a₂, a₃, a₄⟩ := PartyChain.append_props S M Mk h₁ h₂ k₁ k₂
      refine ⟨M.append Mk, a₁, a₂, ?_, ?_, fun z => ?_⟩
      · rw [a₃, List.map_cons, List.sum_cons]
        omega
      · rw [a₄, List.map_cons, List.sum_cons]
        omega
      · rw [PartyChain.eval_append, ContinuousLinearMap.comp_apply, k₅, h₅, List.map_cons,
          List.prod_cons, act_mul]

end ListProd

/-! ### One-site zero blocks changing owners -/

section ZeroChain

variable [NeZero q] {pos : ι → ℝ × ℝ} {Party : Type}

private theorem notMem_compl_union_singleton {x y : ι} :
    y ∉ (({x} : Finset ι) ∪ ({x} : Finset ι)ᶜ)ᶜ := by
  simp only [Finset.mem_compl, Finset.mem_union, not_not]
  by_cases h : y = x
  · exact Or.inl (Finset.mem_singleton.mpr h)
  · exact Or.inr (by simpa using h)

private theorem pairwise_zeroBlock {W : List ι} (hW : W.Nodup) :
    (W.map (zeroBlock (q := q))).Pairwise fun b b' => ∀ x, x ∈ b.E ∨ x ∈ b'.E := by
  rw [List.pairwise_map]
  refine hW.imp fun {x y} hxy z => ?_
  by_cases hz : z = x
  · subst hz
    exact Or.inr (by simpa [zeroBlock] using hxy)
  · exact Or.inl (by simpa [zeroBlock] using hz)

/-- **One-site zero blocks with a change of owners.** For a list `W` of distinct sites, outside
of which the owners `own` and `own'` agree, the product of the one-site zero blocks
`|0⟩⟨0|_x`, `x ∈ W`, is the operator of an allowed monomial from the registers of a frame with
owners `own` to those with owners `own'`, using only the owners of the sites of `W` before and
after, with no pair source and no pair effect. At each site the register is contracted with
`⟨0|` at its owner before and prepared as `|0⟩` at its owner after. -/
theorem exists_zeroChain (l : List (Hole pos q Party)) (S : Set Party) :
    (W : List ι) → W.Nodup → (own own' : ι → Party) → (∀ x ∈ W, own x ∈ S ∧ own' x ∈ S) →
    (∀ x ∉ W, own x = own' x) →
    ∃ M : PartyChain (layoutRegs q l own) (layoutRegs q l own'),
      M.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount = 0 ∧
      ∀ z, layoutIso l own' (M.toEffectChain.eval z) =
        act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ
          ((W.map (zeroBlock (q := q))).map RankOneBlock.op).prod) (layoutIso l own z)
  | [], _, own, own', _, hown => by
      obtain rfl : own = own' := funext fun x => hown x List.not_mem_nil
      refine ⟨.final (.id _), trivial, trivial, rfl, rfl, fun z => ?_⟩
      simp only [List.map_nil, List.prod_nil, one_kronecker_one, act_one]
      rfl
  | x :: W, hW, own, own', hS, hown => by
      have hxW : x ∉ W := (List.nodup_cons.mp hW).1
      set mid : ι → Party := fun y => if y ∈ W then own' y else own y with hmid
      obtain ⟨M, h₁, h₂, h₃, h₄, h₅⟩ := exists_zeroChain l S W (List.nodup_cons.mp hW).2 own mid
        (fun y hy => ⟨(hS y (List.mem_cons_of_mem _ hy)).1, by
          simpa [hmid, hy] using (hS y (List.mem_cons_of_mem _ hy)).2⟩)
        (fun y hy => by simp [hmid, hy])
      obtain ⟨Mx, k₁, k₂, k₃, k₃', k₄, k₄', k₅⟩ := exists_rankOneBlock_chain l mid own'
        (zeroBlock x) (pA := own x) (pB := own x) (pA' := own' x) (pB' := own' x)
        (fun y hy => by
          obtain rfl : y = x := Finset.mem_singleton.mp hy
          simp [hmid, hxW])
        (fun y hy => absurd hy notMem_compl_union_singleton)
        (fun y hy => by rw [Finset.mem_singleton.mp hy])
        (fun y hy => absurd hy notMem_compl_union_singleton)
        (fun y hy => by
          have hyx : y ≠ x := by simpa [zeroBlock] using hy
          by_cases hyW : y ∈ W
          · simp [hmid, hyW]
          · simp only [hmid, hyW, ite_false]
            exact hown y (by simp [hyx, hyW]))
        (norm_zeroPair _ _) (norm_zeroPair _ _) (hS x List.mem_cons_self).1
        (hS x List.mem_cons_self).1 (hS x List.mem_cons_self).2 (hS x List.mem_cons_self).2
      obtain ⟨a₁, a₂, a₃, a₄⟩ := PartyChain.append_props S M Mx h₁ h₂ k₁ k₂
      refine ⟨M.append Mx, a₁, a₂, by rw [a₃, h₃, k₃' rfl], by rw [a₄, h₄, k₄' rfl],
        fun z => ?_⟩
      rw [PartyChain.eval_append, ContinuousLinearMap.comp_apply, k₅, h₅, ← act_mul,
        ← mul_kronecker_mul, one_mul, List.map_cons, List.map_cons, List.prod_cons]

end ZeroChain

/-! ### Blocks on groups of sites with at most two owners -/

section GroupBlock

variable [NeZero q] {pos : ι → ℝ × ℝ} {Party : Type}

private theorem eq_of_card_le_two {P : Finset Party} (hP : P.card ≤ 2) {a b c : Party} (ha : a ∈ P)
    (hb : b ∈ P) (hc : c ∈ P) (hba : b ≠ a) (hca : c ≠ a) : b = c := by
  by_contra hbc
  have := Finset.two_lt_card_iff.mpr ⟨a, b, c, ha, hb, hc, hba.symm, hca.symm, hbc⟩
  omega

/-- **A block on a group of sites with at most two owners.** Let `O` be a nonempty group of
sites whose owners lie in a set of at most two parties, all in `S`, and let `v`, `w` be unit
vectors on the configurations of the group. There is a block with the sites outside the group as
its complement, reading `v` and `w` on every configuration, whose operator
`1_tags ⊗ |v⟩⟨w|_O ⊗ 1` is an allowed monomial on the registers of a frame, using only the
parties of `S`, with at most one pair source and at most one pair effect: the sites of the group
held by one owner form the part `T`, the others the part `U`.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 306–313: a group vector
is a normalized state or covector on one party, or a normalized bipartite one on its two
owners. -/
theorem exists_groupBlock (l : List (Hole pos q Party)) (own : ι → Party) (S : Set Party)
    (O : ι → Prop) [DecidablePred O] (hne : ∃ x, O x)
    (hO : ∃ P : Finset Party, P.card ≤ 2 ∧ ∀ x, O x → own x ∈ P) (hS : ∀ x, O x → own x ∈ S)
    (v w : EuclideanSpace ℂ ({x // O x} → Fin q)) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ b : RankOneBlock ι q, (∀ x, x ∈ b.E ↔ ¬O x) ∧ (∀ c, b.ketAt c = v fun x => c x.1) ∧
      (∀ c, b.braAt c = w fun x => c x.1) ∧
      ∃ M : PartyChain (layoutRegs q l own) (layoutRegs q l own),
        M.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount ≤ 1 ∧ M.toEffectChain.effectCount ≤ 1 ∧
        ∀ z, layoutIso l own (M.toEffectChain.eval z) =
          act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ b.op) (layoutIso l own z) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨P, hP, hPO⟩ := hO
  set pA := own x₀
  set T : Finset ι := Finset.univ.filter fun x => O x ∧ own x = pA
  set E : Finset ι := Finset.univ.filter fun x => ¬O x
  have hT : ∀ x ∈ T, O x := fun x hx => (Finset.mem_filter.mp hx).2.1
  have hU : ∀ x ∈ (T ∪ E)ᶜ, O x ∧ own x ≠ pA := fun x hx => by
    simp only [T, E, Finset.mem_compl, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or, not_and, not_not] at hx
    exact ⟨hx.2, hx.1 hx.2⟩
  set pB : Party := if h : ∃ x, O x ∧ own x ≠ pA then own h.choose else pA
  have hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB := fun x hx => by
    have hex : ∃ x, O x ∧ own x ≠ pA := ⟨x, hU x hx⟩
    simp only [pB, hex, dite_true]
    exact eq_of_card_le_two hP (hPO x₀ hx₀) (hPO x (hU x hx).1) (hPO _ hex.choose_spec.1)
      (hU x hx).2 hex.choose_spec.2
  have hpB : pB ∈ S := by
    simp only [pB]
    split_ifs with hex
    · exact hS _ hex.choose_spec.1
    · exact hS x₀ hx₀
  obtain ⟨vk, hvk, hvk'⟩ := exists_pairVec O hT v
  obtain ⟨vb, hvb, hvb'⟩ := exists_pairVec O hT w
  have hTE : Disjoint T E := Finset.disjoint_left.mpr fun x hxT hxE =>
    (Finset.mem_filter.mp hxE).2 (hT x hxT)
  let b : RankOneBlock ι q := ⟨T, E, hTE, vk, vb⟩
  obtain ⟨M, m₁, m₂, m₃, -, m₄, -, m₅⟩ := exists_rankOneBlock_chain l own own b
    (pA := pA) (pB := pB) (pA' := pA) (pB' := pB) (fun x hx => (Finset.mem_filter.mp hx).2.2)
    hB (fun x hx => (Finset.mem_filter.mp hx).2.2) hB (fun _ _ => rfl) (hvk.trans hv)
    (hvb.trans hw) (hS x₀ hx₀) hpB (hS x₀ hx₀) hpB
  exact ⟨b, fun x => by simp [b, E], hvk', hvb', M, m₁, m₂, m₃, m₄, m₅⟩

/-- The basis vector of the zero configuration of a group of sites, the analogue of `zeroVec`
and `zeroPair` on the configurations of the group. -/
def zeroGroupVec (O : ι → Prop) [DecidablePred O] : EuclideanSpace ℂ ({x // O x} → Fin q) :=
  EuclideanSpace.single 0 1

theorem norm_zeroGroupVec (O : ι → Prop) [DecidablePred O] :
    ‖zeroGroupVec (q := q) O‖ = 1 := by
  simp [zeroGroupVec]

omit [DecidableEq ι] in
theorem zeroGroupVec_apply (O : ι → Prop) [DecidablePred O] (c : ι → Fin q) :
    zeroGroupVec (q := q) O (fun x => c x.1) = if ∀ x, O x → c x = 0 then 1 else 0 := by
  rw [zeroGroupVec, PiLp.single_apply]
  congr 1
  exact propext ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x.1 x.2⟩

/-- **The block of a bra vertex.** Let `f` be a unit vector on a group `O` of sites, read as the
covector `⟨f|`. There are a block on the sites of `O` and a scalar `s` of modulus at most one
with `f(c|_O) = s · \overline{w(c)}` and the zero vector as ket, whose operator
`1_tags ⊗ |0⟩⟨w|_O ⊗ 1` is an allowed monomial using only the parties of `S`, with at most one pair
source and one pair effect when `O` is nonempty and none otherwise. When `O` is nonempty its
owners must lie in a set of at most two parties of `S`; the block is then that of
`exists_groupBlock` and `s = 1`. When `O` is empty, the block is trivial and `s = f(·)`. -/
theorem exists_braVertexBlock (l : List (Hole pos q Party)) (own : ι → Party) (S : Set Party)
    (O : ι → Prop) [DecidablePred O]
    (hO : (∃ x, O x) → ∃ P : Finset Party, P.card ≤ 2 ∧ ∀ x, O x → own x ∈ P ∧ own x ∈ S)
    (f : EuclideanSpace ℂ ({x // O x} → Fin q)) (hf : ‖f‖ = 1) :
    ∃ (b : RankOneBlock ι q) (s : ℂ), ‖s‖ ≤ 1 ∧ (∀ x, x ∈ b.E ↔ ¬O x) ∧
      (∀ c, b.ketAt c = if ∀ x, O x → c x = 0 then 1 else 0) ∧
      (∀ c, f (fun x => c x.1) = s * star (b.braAt c)) ∧
      ∃ M : PartyChain (layoutRegs q l own) (layoutRegs q l own),
        M.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount ≤ (if ∃ x, O x then 1 else 0) ∧
        M.toEffectChain.effectCount ≤ (if ∃ x, O x then 1 else 0) ∧
        ∀ z, layoutIso l own (M.toEffectChain.eval z) =
          act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ b.op) (layoutIso l own z) := by
  classical
  by_cases hne : ∃ x, O x
  · obtain ⟨P, hP, hPO⟩ := hO hne
    have hfo : Orthonormal ℂ fun _ : Unit => f := by
      rw [orthonormal_iff_ite]
      intro _ _
      simp [inner_self_eq_norm_sq_to_K, hf]
    obtain ⟨b, hbE, hbK, hbB, M, m₁, m₂, m₃, m₄, m₅⟩ := exists_groupBlock l own S O hne
      ⟨P, hP, fun x hx => (hPO x hx).1⟩ (fun x hx => (hPO x hx).2) (zeroGroupVec O)
      (WholeGroup.conjFamily (fun _ : Unit => f) ()) (norm_zeroGroupVec O)
      ((WholeGroup.orthonormal_conjFamily hfo).1 ())
    refine ⟨b, 1, by simp, hbE, fun c => by rw [hbK, zeroGroupVec_apply], fun c => ?_, M, m₁,
      m₂, by simpa [hne] using m₃, by simpa [hne] using m₄, m₅⟩
    rw [hbB]
    simp [WholeGroup.conjFamily]
  · refine ⟨emptyBlock, f fun x => (0 : ι → Fin q) x.1, ?_, fun x => ?_, fun c => ?_,
      fun c => ?_, .final (.id _), trivial, trivial, Nat.zero_le _, Nat.zero_le _, fun z => ?_⟩
    · rw [← hf]
      exact PiLp.norm_apply_le f _
    · simpa [emptyBlock] using fun h => hne ⟨x, h⟩
    · rw [emptyBlock_ketAt]
      rw [ite_eq_left fun x h => absurd ⟨x, h⟩ hne]
    · rw [emptyBlock_braAt, star_one, mul_one]
      exact congrArg (fun d => f d) (funext fun (x : {x // O x}) => absurd ⟨x.1, x.2⟩ hne)
    · rw [emptyBlock_op, one_kronecker_one, act_one]
      rfl

/-- **The block of a ket vertex.** The analogue of `exists_braVertexBlock` for the vector `|f⟩`:
a block on the sites of `O` with zero bra and ket reading `f` up to a scalar `s` of modulus at
most one. -/
theorem exists_ketVertexBlock (l : List (Hole pos q Party)) (own : ι → Party) (S : Set Party)
    (O : ι → Prop) [DecidablePred O]
    (hO : (∃ x, O x) → ∃ P : Finset Party, P.card ≤ 2 ∧ ∀ x, O x → own x ∈ P ∧ own x ∈ S)
    (f : EuclideanSpace ℂ ({x // O x} → Fin q)) (hf : ‖f‖ = 1) :
    ∃ (b : RankOneBlock ι q) (s : ℂ), ‖s‖ ≤ 1 ∧ (∀ x, x ∈ b.E ↔ ¬O x) ∧
      (∀ c, b.braAt c = if ∀ x, O x → c x = 0 then 1 else 0) ∧
      (∀ c, f (fun x => c x.1) = s * b.ketAt c) ∧
      ∃ M : PartyChain (layoutRegs q l own) (layoutRegs q l own),
        M.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount ≤ (if ∃ x, O x then 1 else 0) ∧
        M.toEffectChain.effectCount ≤ (if ∃ x, O x then 1 else 0) ∧
        ∀ z, layoutIso l own (M.toEffectChain.eval z) =
          act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ b.op) (layoutIso l own z) := by
  classical
  by_cases hne : ∃ x, O x
  · obtain ⟨P, hP, hPO⟩ := hO hne
    obtain ⟨b, hbE, hbK, hbB, M, m₁, m₂, m₃, m₄, m₅⟩ := exists_groupBlock l own S O hne
      ⟨P, hP, fun x hx => (hPO x hx).1⟩ (fun x hx => (hPO x hx).2) f (zeroGroupVec O) hf
      (norm_zeroGroupVec O)
    refine ⟨b, 1, by simp, hbE, fun c => by rw [hbB, zeroGroupVec_apply], fun c => by
      rw [hbK, one_mul], M, m₁, m₂, by simpa [hne] using m₃, by simpa [hne] using m₄, m₅⟩
  · refine ⟨emptyBlock, f fun x => (0 : ι → Fin q) x.1, ?_, fun x => ?_, fun c => ?_,
      fun c => ?_, .final (.id _), trivial, trivial, Nat.zero_le _, Nat.zero_le _, fun z => ?_⟩
    · rw [← hf]
      exact PiLp.norm_apply_le f _
    · simpa [emptyBlock] using fun h => hne ⟨x, h⟩
    · rw [emptyBlock_braAt]
      rw [ite_eq_left fun x h => absurd ⟨x, h⟩ hne]
    · rw [emptyBlock_ketAt, mul_one]
      exact congrArg (fun d => f d) (funext fun (x : {x // O x}) => absurd ⟨x.1, x.2⟩ hne)
    · rw [emptyBlock_op, one_kronecker_one, act_one]
      rfl

end GroupBlock

end TNLean.PEPS.EncodedFrame

/-! ### Product terms of a chain as products of blocks -/

namespace TNLean.PEPS.SiteChain

open EncodedFrame

section OpenLegs

variable {ι : Type*} {q : ℕ} {n : ℕ} (st : Fin n → Step ι q)

/-- The step applied first among those touching a site is unique. -/
theorem eq_of_not_earlierTouch {x : ι} {j k : Fin n} (hj : x ∈ (st j).sites)
    (hj' : ¬EarlierTouch st j x) (hk : x ∈ (st k).sites) (hk' : ¬EarlierTouch st k x) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact absurd ⟨k, h, hk⟩ hj'
  · exact h
  · exact absurd ⟨j, h, hj⟩ hk'

/-- The step applied last among those touching a site is unique. -/
theorem eq_of_not_laterTouch {x : ι} {j k : Fin n} (hj : x ∈ (st j).sites)
    (hj' : ¬LaterTouch st j x) (hk : x ∈ (st k).sites) (hk' : ¬LaterTouch st k x) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact absurd ⟨j, h, hj⟩ hk'
  · exact h
  · exact absurd ⟨k, h, hk⟩ hj'

/-- An open input leg at a site belongs to one bra vertex. -/
theorem eq_of_isOpen_inl {x : ι} {j k : Fin n} (hj : IsOpen st (.inl j) x)
    (hk : IsOpen st (.inl k) x) : j = k :=
  eq_of_not_earlierTouch st hj.1 hj.2.1 hk.1 hk.2.1

/-- An open output leg at a site belongs to one ket vertex. -/
theorem eq_of_isOpen_inr {x : ι} {j k : Fin n} (hj : IsOpen st (.inr j) x)
    (hk : IsOpen st (.inr k) x) : j = k :=
  eq_of_not_laterTouch st hj.1 hj.2.1 hk.1 hk.2.1

theorem not_untouched_of_isOpen {v : Fin n ⊕ Fin n} {x : ι} (h : IsOpen st v x) :
    ¬Untouched st x := by
  rcases v with j | j
  · exact fun hu => hu j h.1
  · exact fun hu => hu j h.1

/-- A site has a fixed input leg exactly when it is touched and is an open input leg of no bra
vertex. -/
theorem fixedIn_iff (x : ι) :
    FixedIn st x ↔ ¬Untouched st x ∧ ¬∃ j, IsOpen st (.inl j) x := by
  constructor
  · rintro ⟨j, hxj, hE, hb⟩
    refine ⟨fun hu => hu j hxj, fun ⟨k, hk⟩ => ?_⟩
    obtain rfl := eq_of_not_earlierTouch st hxj hE hk.1 hk.2.1
    have := hk.2.2
    rw [hb] at this
    exact Bool.false_ne_true this
  · rintro ⟨hu, hno⟩
    simp only [Untouched, not_forall, not_not] at hu
    obtain ⟨j, hxj, hE⟩ := exists_inEnd hu
    refine ⟨j, hxj, hE, ?_⟩
    by_contra hb
    exact hno ⟨j, hxj, hE, by simpa only [Bool.not_eq_false] using hb⟩

/-- A site has a fixed output leg exactly when it is touched and is an open output leg of no
ket vertex. -/
theorem fixedOut_iff (x : ι) :
    FixedOut st x ↔ ¬Untouched st x ∧ ¬∃ j, IsOpen st (.inr j) x := by
  constructor
  · rintro ⟨j, hxj, hL, hk⟩
    refine ⟨fun hu => hu j hxj, fun ⟨k, hk'⟩ => ?_⟩
    obtain rfl := eq_of_not_laterTouch st hxj hL hk'.1 hk'.2.1
    have := hk'.2.2
    rw [hk] at this
    exact Bool.false_ne_true this
  · rintro ⟨hu, hno⟩
    simp only [Untouched, not_forall, not_not] at hu
    obtain ⟨j, hxj, hL⟩ := exists_outEnd hu
    refine ⟨j, hxj, hL, ?_⟩
    by_contra hk
    exact hno ⟨j, hxj, hL, by simpa only [Bool.not_eq_false] using hk⟩

end OpenLegs

private theorem ite_ite_mul_eq {A A' C C' : Prop} {_ : Decidable A} {_ : Decidable A'}
    {_ : Decidable C} {_ : Decidable C'} (hA : A ↔ A') (hC : C ↔ C') (X : ℂ) :
    (if A then (if C then (1 : ℂ) else 0) * X else 0) = if A' ∧ C' then X else 0 := by
  by_cases hA' : A' <;> by_cases hC' : C' <;> simp [hA, hC, hA', hC']

private theorem list_prod_map_ite_one {α : Type*} (p : α → Prop) [DecidablePred p] (L : List α)
    {_ : Decidable (∀ y ∈ L, p y)} :
    (L.map fun y => if p y then (1 : ℂ) else 0).prod = if ∀ y ∈ L, p y then 1 else 0 := by
  split_ifs with h
  · refine List.prod_eq_one fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    simp [h y hy]
  · push Not at h
    obtain ⟨y, hy, hpy⟩ := h
    exact List.prod_eq_zero (List.mem_map.mpr ⟨y, hy, by simp [hpy]⟩)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {n : ℕ}
  (st : Fin n → Step ι q)

/-- The product of bra blocks reading the open input legs. -/
theorem prod_braBlocks_apply (B : Fin n → RankOneBlock ι q)
    (hE : ∀ j x, x ∈ (B j).E ↔ ¬IsOpen st (.inl j) x)
    (hK : ∀ j c, (B j).ketAt c = if ∀ x, IsOpen st (.inl j) x → c x = 0 then 1 else 0)
    (b c : ι → Fin q) :
    ((List.ofFn B).map RankOneBlock.op).prod b c =
      if (∀ x, (¬∃ j, IsOpen st (.inl j) x) → b x = c x) ∧
          (∀ x, (∃ j, IsOpen st (.inl j) x) → b x = 0) then
        ∏ j, star ((B j).braAt c) else 0 := by
  classical
  have hpw : (List.ofFn B).Pairwise fun b b' => ∀ x, x ∈ b.E ∨ x ∈ b'.E :=
    List.pairwise_ofFn.mpr fun j k hjk x => by
      by_contra h
      simp only [not_or, hE, not_not] at h
      exact absurd (eq_of_isOpen_inl st h.1 h.2) hjk.ne
  rw [RankOneBlock.prod_op_apply _ hpw, List.map_ofFn, List.prod_ofFn]
  have hmem : ∀ x, (∀ b' ∈ List.ofFn B, x ∈ b'.E) ↔ ¬∃ j, IsOpen st (.inl j) x := fun x => by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, hE, not_exists]
  simp only [Function.comp_apply, hK, Finset.prod_mul_distrib, Fintype.prod_boole]
  exact ite_ite_mul_eq (forall_congr' fun x => imp_congr_left (hmem x))
    ⟨fun h x ⟨j, hj⟩ => h j x hj, fun h j x hj => h x ⟨j, hj⟩⟩ _

/-- The product of ket blocks preparing the open output legs. -/
theorem prod_ketBlocks_apply (K : Fin n → RankOneBlock ι q)
    (hE : ∀ j x, x ∈ (K j).E ↔ ¬IsOpen st (.inr j) x)
    (hB : ∀ j c, (K j).braAt c = if ∀ x, IsOpen st (.inr j) x → c x = 0 then 1 else 0)
    (a' a : ι → Fin q) :
    ((List.ofFn K).map RankOneBlock.op).prod a' a =
      if (∀ x, (¬∃ j, IsOpen st (.inr j) x) → a' x = a x) ∧
          (∀ x, (∃ j, IsOpen st (.inr j) x) → a x = 0) then
        ∏ j, (K j).ketAt a' else 0 := by
  classical
  have hpw : (List.ofFn K).Pairwise fun b b' => ∀ x, x ∈ b.E ∨ x ∈ b'.E :=
    List.pairwise_ofFn.mpr fun j k hjk x => by
      by_contra h
      simp only [not_or, hE, not_not] at h
      exact absurd (eq_of_isOpen_inr st h.1 h.2) hjk.ne
  rw [RankOneBlock.prod_op_apply _ hpw, List.map_ofFn, List.prod_ofFn]
  have hmem : ∀ x, (∀ b' ∈ List.ofFn K, x ∈ b'.E) ↔ ¬∃ j, IsOpen st (.inr j) x := fun x => by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, hE, not_exists]
  have hB' : ∀ j c, star ((K j).braAt c) =
      if ∀ x, IsOpen st (.inr j) x → c x = 0 then 1 else 0 := fun j c => by
    rw [hB]
    split_ifs <;> simp
  simp only [Function.comp_apply, hB', Finset.prod_mul_distrib, Fintype.prod_boole]
  rw [mul_comm]
  exact ite_ite_mul_eq (forall_congr' fun x => imp_congr_left (hmem x))
    ⟨fun h x ⟨j, hj⟩ => h j x hj, fun h j x hj => h x ⟨j, hj⟩⟩ _

omit [Fintype ι] in
/-- The product of the one-site zero blocks of a list of distinct sites. -/
theorem prod_zeroBlocks_apply [Fintype ι] {W : List ι} (hW : W.Nodup) (a b : ι → Fin q) :
    ((W.map (zeroBlock (q := q))).map RankOneBlock.op).prod a b =
      if (∀ x ∉ W, a x = b x) ∧ (∀ x ∈ W, a x = 0) ∧ (∀ x ∈ W, b x = 0) then 1 else 0 := by
  classical
  rw [RankOneBlock.prod_op_apply _ (pairwise_zeroBlock hW), List.map_map]
  have hmem : ∀ x, (∀ b' ∈ W.map (zeroBlock (q := q)), x ∈ b'.E) ↔ x ∉ W := fun x => by
    simp only [List.forall_mem_map, zeroBlock, Finset.mem_compl, Finset.mem_singleton]
    exact ⟨fun h hx => h x hx rfl, fun h y hy hxy => h (hxy ▸ hy)⟩
  have hprod : (W.map ((fun b' : RankOneBlock ι q => b'.ketAt a * star (b'.braAt b)) ∘
      zeroBlock)).prod = if ∀ y ∈ W, a y = 0 ∧ b y = 0 then 1 else 0 := by
    refine Eq.trans ?_ (list_prod_map_ite_one (fun y => a y = 0 ∧ b y = 0) W)
    refine congrArg List.prod (List.map_congr_left fun y _ => ?_)
    simp only [Function.comp_apply, zeroBlock_ketAt, zeroBlock_braAt]
    by_cases ha : a y = 0 <;> by_cases hb : b y = 0 <;> simp [ha, hb]
  simp only [hmem, hprod]
  have h : (∀ y ∈ W, a y = 0 ∧ b y = 0) ↔ (∀ x ∈ W, a x = 0) ∧ ∀ x ∈ W, b x = 0 :=
    ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩, fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  simp only [h]
  split_ifs <;> simp_all

/-- **A product term as a product of rank-one blocks.** Let the bra blocks `B j` sit on the open
input legs of the bra vertices, with zero kets and with bras reading the covectors of the term
up to scalars `s_j`, and the ket blocks `K j` on the open output legs of the ket vertices, with
zero bras and with kets reading the vectors of the term up to scalars `t_j`; let `W` list the
sites touched by the chain. Then the product term is
`(∏ s_j ∏ t_j) · K ⋯ K · Z ⋯ Z · B ⋯ B`, where `Z` are the one-site zero blocks of `W`. Read from
right to left: the bras consume the open inputs and leave zeros, the zero blocks impose the
fixed input zeros, and the kets prepare the open outputs; the fixed output zeros remain.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 262–273 and 306–316. -/
theorem termOp_eq_smul_prod {r : Fin n ⊕ Fin n → ℕ}
    (e : (v : Fin n ⊕ Fin n) → Fin (r v) → EuclideanSpace ℂ (Group st v))
    (i : (v : Fin n ⊕ Fin n) → Fin (r v)) (B K : Fin n → RankOneBlock ι q) (sB sK : Fin n → ℂ)
    (hBE : ∀ j x, x ∈ (B j).E ↔ ¬IsOpen st (.inl j) x)
    (hBK : ∀ j c, (B j).ketAt c = if ∀ x, IsOpen st (.inl j) x → c x = 0 then 1 else 0)
    (hBB : ∀ j c, e (.inl j) (i (.inl j)) (fun x => c x.1) = sB j * star ((B j).braAt c))
    (hKE : ∀ j x, x ∈ (K j).E ↔ ¬IsOpen st (.inr j) x)
    (hKB : ∀ j c, (K j).braAt c = if ∀ x, IsOpen st (.inr j) x → c x = 0 then 1 else 0)
    (hKK : ∀ j c, e (.inr j) (i (.inr j)) (fun x => c x.1) = sK j * (K j).ketAt c)
    {W : List ι} (hWn : W.Nodup) (hW : ∀ x, x ∈ W ↔ ¬Untouched st x) :
    termOp st e i = ((∏ j, sB j) * ∏ j, sK j) •
      (((List.ofFn K).map RankOneBlock.op).prod *
        ((W.map (zeroBlock (q := q))).map RankOneBlock.op).prod *
        ((List.ofFn B).map RankOneBlock.op).prod) := by
  classical
  have hInW : ∀ x, (∃ j, IsOpen st (.inl j) x) → x ∈ W := fun x ⟨j, hj⟩ =>
    (hW x).mpr (not_untouched_of_isOpen st hj)
  have hOutW : ∀ x, (∃ j, IsOpen st (.inr j) x) → x ∈ W := fun x ⟨j, hj⟩ =>
    (hW x).mpr (not_untouched_of_isOpen st hj)
  ext c' c
  set b₀ : ι → Fin q := fun x => if ∃ j, IsOpen st (.inl j) x then 0 else c x with hb₀
  set a₀ : ι → Fin q := fun x => if x ∈ W then 0 else c x with ha₀
  rw [Matrix.smul_apply, Matrix.mul_apply, Finset.sum_eq_single b₀ (fun b _ hb => ?_)
    (fun h => absurd (Finset.mem_univ _) h), Matrix.mul_apply,
    Finset.sum_eq_single a₀ (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · rw [prod_braBlocks_apply st B hBE hBK, prod_ketBlocks_apply st K hKE hKB,
      prod_zeroBlocks_apply hWn, termOp_apply]
    have hB₀ : (∀ x, (¬∃ j, IsOpen st (.inl j) x) → b₀ x = c x) ∧
        (∀ x, (∃ j, IsOpen st (.inl j) x) → b₀ x = 0) :=
      ⟨fun x hx => by simp [hb₀, hx], fun x hx => by simp [hb₀, hx]⟩
    rw [ite_eq_left hB₀]
    have hgood : Good st c' c ↔
        ((∀ x, (¬∃ j, IsOpen st (.inr j) x) → c' x = a₀ x) ∧
          (∀ x, (∃ j, IsOpen st (.inr j) x) → a₀ x = 0)) ∧
        ((∀ x ∉ W, a₀ x = b₀ x) ∧ (∀ x ∈ W, a₀ x = 0) ∧ (∀ x ∈ W, b₀ x = 0)) := by
      have hK₂ : ∀ x, (∃ j, IsOpen st (.inr j) x) → a₀ x = 0 := fun x hx => by
        simp [ha₀, hOutW x hx]
      have hZ₁ : ∀ x ∉ W, a₀ x = b₀ x := fun x hx => by
        have hx' : ¬∃ j, IsOpen st (.inl j) x := fun h => hx (hInW x h)
        simp [ha₀, hb₀, hx, hx']
      have hZ₂ : ∀ x ∈ W, a₀ x = 0 := fun x hx => by simp [ha₀, hx]
      constructor
      · rintro ⟨hu, hfi, hfo⟩
        refine ⟨⟨fun x hx => ?_, hK₂⟩, hZ₁, hZ₂, fun x hx => ?_⟩
        · by_cases hxW : x ∈ W
          · rw [hfo x ((fixedOut_iff st x).mpr ⟨(hW x).mp hxW, hx⟩)]
            simp [ha₀, hxW]
          · rw [hu x (by simpa [hW] using hxW)]
            simp [ha₀, hxW]
        · by_cases hx' : ∃ j, IsOpen st (.inl j) x
          · simp [hb₀, hx']
          · simp only [hb₀, hx', ite_false]
            exact hfi x ((fixedIn_iff st x).mpr ⟨(hW x).mp hx, hx'⟩)
      · rintro ⟨⟨hK, -⟩, -, -, hZ⟩
        refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
        · have hxW : x ∉ W := by simpa [hW] using hx
          rw [hK x fun h => hxW (hOutW x h)]
          simp [ha₀, hxW]
        · obtain ⟨h₁, h₂⟩ := (fixedIn_iff st x).mp hx
          have := hZ x ((hW x).mpr h₁)
          simpa [hb₀, h₂] using this
        · obtain ⟨h₁, h₂⟩ := (fixedOut_iff st x).mp hx
          rw [hK x h₂]
          simp [ha₀, (hW x).mpr h₁]
    simp only [Fintype.prod_sum_type, groupsOf, hBB, hKK, Finset.prod_mul_distrib, smul_eq_mul]
    by_cases hg : Good st c' c
    · rw [ite_eq_left hg, ite_eq_left (hgood.mp hg).1, ite_eq_left (hgood.mp hg).2]
      ring
    · rw [ite_eq_right hg]
      by_cases h₁ : (∀ x, (¬∃ j, IsOpen st (.inr j) x) → c' x = a₀ x) ∧
          (∀ x, (∃ j, IsOpen st (.inr j) x) → a₀ x = 0)
      · rw [ite_eq_left h₁, ite_eq_right fun h₂ => hg (hgood.mpr ⟨h₁, h₂⟩)]
        ring
      · rw [ite_eq_right h₁]
        ring
  · rw [prod_zeroBlocks_apply hWn]
    split_ifs with h
    · refine absurd (funext fun x => ?_) ha
      by_cases hx : x ∈ W
      · rw [h.2.1 x hx]
        simp [ha₀, hx]
      · have hx' : ¬∃ j, IsOpen st (.inl j) x := fun h => hx (hInW x h)
        rw [h.1 x hx]
        simp [ha₀, hb₀, hx, hx']
    · simp
  · rw [prod_braBlocks_apply st B hBE hBK]
    split_ifs with h
    · refine absurd (funext fun x => ?_) hb
      by_cases hx : ∃ j, IsOpen st (.inl j) x
      · rw [h.2 x hx]
        simp [hb₀, hx]
      · rw [h.1 x hx]
        simp [hb₀, hx]
    · simp

end TNLean.PEPS.SiteChain
