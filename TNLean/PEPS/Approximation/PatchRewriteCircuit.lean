/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.MonomialFixesOutside
import TNLean.PEPS.Approximation.PartyGateOriginalCircuit
import TNLean.PEPS.Approximation.PatchRewriteMonomials
import TNLean.PEPS.Approximation.SampledOriginalCircuit

/-!
# The small-patch rewrite as one gate of the specified parties

The second assertion of Lemma 6.3 `lem:small-rewrite` of the polynomial-PEPS manuscript says that
the small-patch rewrite is a bounded change: a polynomial sum of monomials allowed by Theorem 5.2
on the specified list of parties, accurate on the reference vectors to `O(L^{-20})`
(`SmallPatchRewrite.exists_allowed_monomial_approx_refVec`). This file reads that sum as an
original circuit with at most one nonprivate gate whose participants lie in the specified list
(`SmallPatchRewrite.exists_originalCircuit_refVec`), the form in which the changes of the
protocol of Proposition 7.1 are composed.

Two facts make the sum one gate of the specified parties.

* The registers of the other parties are the same in the two frames
  (`SmallPatchRewrite.restrict_regs_eq`): an affected tag is held by a specified party, and a
  raw register whose owner changes lies in a patch footprint, where both owners are specified
  (conditions (ii) and (iv)).
* Every monomial of the expansion uses only specified parties and moves a specified register at
  every exchange of tensor factors, so it leaves the other registers in place
  (`SmallPatchRewrite.fixesOutside_of_mem`).

## Main results

* `EncodedFrame.SmallPatchRewrite.restrict_regs_eq`
* `EncodedFrame.SmallPatchRewrite.exists_originalCircuit_refVec`

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 188–218; original circuits, `04-compression.tex`, lines 21–43; the
  gates of Proposition 7.1, `06-geometry.tex`, lines 574–583.
-/

noncomputable section

open Matrix ContinuousLinearMap
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

/-! ### The registers of the unspecified parties -/

/-- The tag registers of holes whose tag owners are all deselected restrict to nothing. -/
theorem restrict_tagRegs_eq_nil (f : Party → Bool) :
    (l : List (Hole pos q Party)) → (∀ h ∈ l, f h.tagOwner = false) →
      Layout.restrict f (tagRegs l) = []
  | [], _ => rfl
  | h :: l, hl => by
      rw [tagRegs, Layout.restrict_cons, hl h List.mem_cons_self,
        restrict_tagRegs_eq_nil f l fun h' hh' => hl h' (List.mem_cons_of_mem _ hh')]
      rfl

theorem tagRegs_append (l₁ l₂ : List (Hole pos q Party)) :
    tagRegs (l₁ ++ l₂) = tagRegs l₁ ++ tagRegs l₂ := by
  induction l₁ with
  | nil => rfl
  | cons h l₁ ih => exact congrArg (List.cons _) ih

omit [Fintype ι] [DecidableEq ι] in
/-- Raw registers whose owners agree wherever one of them is selected restrict to the same
registers. -/
theorem restrict_siteRegs_congr (f : Party → Bool) (own own' : ι → Party) :
    (S : List ι) → (∀ x ∈ S, (f (own x) = true ∨ f (own' x) = true) → own x = own' x) →
      Layout.restrict f (siteRegs q own S) = Layout.restrict f (siteRegs q own' S)
  | [], _ => rfl
  | x :: S, h => by
      have ih := restrict_siteRegs_congr f own own' S fun y hy => h y (List.mem_cons_of_mem _ hy)
      change Layout.restrict f (⟨own x, _⟩ :: siteRegs q own S) =
        Layout.restrict f (⟨own' x, _⟩ :: siteRegs q own' S)
      rw [Layout.restrict_cons, Layout.restrict_cons, ih]
      by_cases hx : f (own x) = true ∨ f (own' x) = true
      · rw [h x List.mem_cons_self hx]
      · push Not at hx
        simp [Bool.not_eq_true] at hx
        simp [hx.1, hx.2]

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

variable [DecidableEq Party] in
/-- **The other registers are the same in the two frames.** Under the conditions of Lemma 6.3,
the registers of `F_old` and of `F_new` held by parties outside the specified list coincide: the
affected tags are held by specified parties (condition (iv)), and a raw register whose owner
changes lies in a patch footprint (condition (ii)), where both its owners are specified
(condition (iv)).

Polynomial-PEPS manuscript, Lemma 6.3, `05-frames.tex`, lines 193–207. -/
theorem restrict_regs_eq (hR : R.Conditions) :
    Layout.restrict (fun p ↦ !decide (p ∈ R.parties)) R.oldFrame.regs =
      Layout.restrict (fun p ↦ !decide (p ∈ R.parties)) R.newFrame.regs := by
  have hsel : ∀ l : List (Hole pos q Party), (∀ h ∈ l, h.tagOwner ∈ R.parties) →
      Layout.restrict (fun p ↦ !decide (p ∈ R.parties)) (tagRegs l) = [] := fun l hl =>
    restrict_tagRegs_eq_nil _ l fun h hh => by simp [hl h hh]
  change Layout.restrict _ (tagRegs (R.untouched ++ R.oldAffected) ++ siteRegs q R.ownerOld _) =
    Layout.restrict _ (tagRegs (R.untouched ++ R.newAffected) ++ siteRegs q R.ownerNew _)
  rw [tagRegs_append, tagRegs_append, Layout.restrict_append, Layout.restrict_append,
    Layout.restrict_append, Layout.restrict_append,
    hsel _ fun h hh => hR.tag_owners_mem h (List.mem_append_left _ hh),
    hsel _ fun h hh => hR.tag_owners_mem h (List.mem_append_right _ hh),
    restrict_siteRegs_congr _ R.ownerOld R.ownerNew _ fun x _ hx => ?_]
  by_contra hne
  obtain ⟨h₁, h₂⟩ := hR.raw_owners_mem x
    (Or.inl (innerUnion_subset_footprint _ (hR.changed_mem x hne)))
  rcases hx with hx | hx <;> simp_all

variable [DecidableEq Party] in
/-- A monomial using only the specified parties and moving a specified register at every
exchange of tensor factors leaves the registers of the other parties in place. -/
theorem fixesOutside_of_mem (hR : R.Conditions) (M : PartyChain R.oldFrame.regs R.newFrame.regs)
    (hU : M.UsesOnly (R.parties : Set Party))
    (hM : M.SwapsMeetSet (R.parties : Set Party)) :
    M.FixesOutside R.parties (R.restrict_regs_eq hR) := by
  have hS : {p | decide (p ∈ R.parties) = true} = (R.parties : Set Party) := by
    ext
    simp
  exact PartyChain.fixesOutside_of_swapsMeet R.parties _ M (hS ▸ hU)
    (hM _ fun x hx => decide_eq_true hx)

variable [NeZero q]

/-- **Lemma 6.3, the small-patch rewrite as one gate.** In the setting of
`exists_allowed_monomial_approx_refVec`, let the specified list of parties be nonempty and the
memory of the registers of `F_old` be nonzero. There are a contraction `M_30` with
`‖M_30 - M‖ ≤ L^{-30}` and `‖M_30 Ω_{F_old} - Ω_{F_new}‖ ≤ (2b + 1) L^{-20}`, and an original
circuit from the registers of `F_old` to those of `F_new` whose operator is `M_30` in canonical
coordinates. It has at most one nonprivate gate, every participant of each of its gates lies in
the specified list of at most `b` parties, and its gate expansion has at most `K L^e` allowed
monomials, each with at most `2b` normalized pair effects, and coefficients of total modulus at
most `K L^e`, with `K` and `e` as in `exists_allowed_monomial_approx_polynomial` for `a = 30`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218;
original circuits, `04-compression.tex`, lines 21–43; the gates of Proposition 7.1,
`06-geometry.tex`, lines 574–583. -/
theorem exists_originalCircuit_refVec (hR : R.Conditions) {C c b L : ℕ}
    (hL : 1 ≤ L) (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ C * L ^ c)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hm : R.patches.length ≤ b) (hrold : R.oldAffected.length ≤ b)
    (hrnew : R.newAffected.length ≤ b) (hparties : R.parties.card ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ P ∈ R.patches, ‖act P.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ h ∈ R.oldAffected, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hS₀ : R.parties.Nonempty) (hne : Nontrivial (Mem R.oldFrame.regs)) :
    ∃ (w : OriginalCircuit R.oldFrame.regs R.newFrame.regs)
      (Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ), ‖Ma‖ ≤ 1 ∧
      ‖Ma - R.rewrite‖ ≤ ((L : ℝ) ^ 30)⁻¹ ∧
      ‖act Ma (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      (∀ z, R.newFrame.regIso (w.eval z) = act Ma (R.oldFrame.regIso z)) ∧
      w.nonprivateCount ≤ 1 ∧ (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑R.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) := by
  classical
  obtain ⟨-, G, hG, hGp, Ma, hMa1, hMa, href, hz⟩ :=
    R.exists_allowed_monomial_approx_refVec hR hL hnew hpatch hold hm hrold hrnew hparties hΩ
      hεpatch hεold
  have hsum : ∀ (z : Mem R.oldFrame.regs) (K : PartyGate R.oldFrame.regs R.newFrame.regs),
      R.newFrame.regIso (gate (toGate K) z) =
        (K.map fun p => p.1 • R.newFrame.regIso (p.2.toEffectChain.eval z)).sum := by
    intro z K
    induction K with
    | nil => exact map_zero _
    | cons p K ih =>
        change R.newFrame.regIso ((p.1 • p.2.toEffectChain.eval + gate (toGate K)) z) = _
        rw [_root_.add_apply, map_add, ih, _root_.smul_apply,
          LinearIsometryEquiv.map_smul, List.map_cons, List.sum_cons]
  have hgate : ∀ z, R.newFrame.regIso (gate (toGate G) z) = act Ma (R.oldFrame.regIso z) :=
    fun z => (hsum z G).trans (hz z)
  have hN : ‖gate (toGate G)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [← LinearIsometryEquiv.norm_map R.newFrame.regIso, hgate, one_mul,
      ← LinearIsometryEquiv.norm_map R.oldFrame.regIso z]
    exact norm_act_le_of_norm_le_one hMa1 _
  obtain ⟨w, hw, hcount, hpart, hexp, hmono⟩ := PartyGate.exists_originalCircuit R.parties hS₀
    (R.restrict_regs_eq hR) G (fun m hm => (hGp m hm).2.1)
    (fun m hm => R.fixesOutside_of_mem hR m.2 (hGp m hm).2.2.1 (hGp m hm).2.2.2.1) hN hne
  refine ⟨w, Ma, hMa1, hMa, href, fun z => by rw [hw, hgate], hcount, hpart,
    hexp _ _ (fun m hm => (hGp m hm).2.2.2.2.2) ?_, w.isMonomialBounded_mono hmono hG⟩
  refine (List.sum_le_length_nsmul _ 1 fun x hx => ?_).trans ?_
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    exact (hGp m hm).1
  · rw [List.length_map, nsmul_eq_mul, mul_one]
    exact_mod_cast hG

end SmallPatchRewrite

end TNLean.PEPS.EncodedFrame
