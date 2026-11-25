/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Original.Sequence
import TNLean.PEPS.Approximation.PartyCircuit.PartyGateSourceBound
import TNLean.PEPS.Approximation.PatchRewrite.PatchRewriteMonomials

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

* Outside the specified parties the output of the gate has the basis of the old frame
  (`SmallPatchRewrite.gateSystem_eq_of_notMem`): an affected tag is held by a specified party,
  and a raw site whose owner changes lies in a patch footprint, where both owners are specified
  (conditions (ii) and (iv)).
* Every monomial of the expansion uses only specified parties.

The gate is followed by a relabelling of the bases (no gate) from its output to the registers of
the new frame, which differ from it only by one-point tag factors of the affected holes at the
other parties.

## Main results

* `EncodedFrame.SmallPatchRewrite.gateSystem_eq_of_notMem`
* `EncodedFrame.SmallPatchRewrite.exists_originalCircuit_refVec_isSourceBounded`: the gate, with
  at most `2b` pair sources in every monomial (Theorem 5.2, item 3, `04-compression.tex`,
  lines 143–147).
* `EncodedFrame.SmallPatchRewrite.exists_originalCircuit_refVec`: the same without the
  pair-source bound.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 188–218; original circuits, `04-compression.tex`, lines 21–43; the
  gates of Proposition 7.1, `06-geometry.tex`, lines 574–583.
-/

noncomputable section

open Matrix ManyBody QuantumCircuit.Party
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}
  [Fintype Party] [DecidableEq Party]

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

omit [Fintype Party] in
/-- **Outside the specified parties the output of the gate is the old frame.** Under the
conditions of Lemma 6.3, at a party outside the specified list the tags of the gate output are
those of the old frame by construction, and the raw sites it owns are the same in both frames:
a raw site whose owner changes lies in a patch footprint (condition (ii)), where both its owners
are specified (condition (iv)).

Polynomial-PEPS manuscript, Lemma 6.3, `05-frames.tex`, lines 193–207. -/
theorem gateSystem_eq_of_notMem (hR : R.Conditions) {v : Party} (hv : v ∉ R.parties) :
    R.gateSystem q v = R.oldFrame.system v := by
  refine congrArg₂ (· × ·) (R.gateTag_of_notMem hv)
    (Sheet.system_eq_of_owner_iff (S := ⟨R.ownerOld⟩) (S' := ⟨R.ownerNew⟩) fun x ↦ ?_)
  by_cases hx : R.ownerOld x = R.ownerNew x
  · change R.ownerNew x = v ↔ R.ownerOld x = v
    rw [hx]
  obtain ⟨h₁, h₂⟩ := hR.raw_owners_mem x
    (Finset.mem_union_left _ (innerUnion_subset_footprint _ (hR.changed_mem x hx)))
  exact ⟨fun h ↦ absurd (h ▸ h₂) hv, fun h ↦ absurd (h ▸ h₁) hv⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem placeBetween_univ {X Y : Party → Type} [∀ p, DecidableEq (X p)]
    (h : ∀ v ∉ (Finset.univ : Finset Party), Y v = X v)
    (K : Matrix (RegionConfig Y Finset.univ) (RegionConfig X Finset.univ) ℂ) :
    placeBetween Finset.univ h K = K.submatrix (univConfigEquiv Y) (univConfigEquiv X) := by
  ext y x
  rw [placeBetween_apply, ite_eq_left fun v hv ↦ absurd (Finset.mem_univ v) hv]
  rfl

variable [NeZero q]

/-- **Lemma 6.3, the small-patch rewrite as one gate, with its pair sources.** In the setting of
`exists_allowed_monomial_approx_refVec`, there are a contraction `M_30` with
`‖M_30 - M‖ ≤ L^{-30}` and `‖M_30 Ω_{F_old} - Ω_{F_new}‖ ≤ (2b + 1) L^{-20}`, and an original
circuit from the registers of `F_old` to those of `F_new` whose operator is `M_30` in canonical
coordinates. It has at most one nonprivate gate, every participant of each of its gates lies in
the specified list of at most `b` parties, and its gate expansion has at most `K L^e` allowed
monomials, each with at most `2b` normalized pair effects and at most `2b` pair sources, and
coefficients of total modulus at most `K L^e`, with `K` and `e` as in
`exists_allowed_monomial_approx_polynomial` for `a = 30`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218;
Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem exists_originalCircuit_refVec_isSourceBounded (hR : R.Conditions) {C c b L : ℕ}
    (hL : 1 ≤ L) (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ C * L ^ c)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hm : R.patches.length ≤ b) (hrold : R.oldAffected.length ≤ b)
    (hrnew : R.newAffected.length ≤ b) (hparties : R.parties.card ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ P ∈ R.patches, ‖toEuclideanLin P.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ h ∈ R.oldAffected, ‖toEuclideanLin h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) :
    ∃ (w : OriginalCircuit R.oldFrame.system R.newFrame.system)
      (Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ), ‖Ma‖ ≤ 1 ∧
      ‖Ma - R.rewrite‖ ≤ ((L : ℝ) ^ 30)⁻¹ ∧
      ‖toEuclideanLin Ma (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.op = reindex R.newFrame.configEquiv.symm R.oldFrame.configEquiv.symm Ma ∧
      w.nonprivateCount ≤ 1 ∧ (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑R.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      w.IsSourceBounded (2 * b) := by
  obtain ⟨-, g, hG, hGp, Ma, hMa1, hMa, href, hz⟩ :=
    R.exists_allowed_monomial_approx_refVec hR hL hnew hpatch hold hm hrold hrnew hparties hΩ
      hεpatch hεold
  have hY : ∀ v ∉ R.parties, R.gateSystem q v = R.oldFrame.system v :=
    fun v hv ↦ R.gateSystem_eq_of_notMem hR hv
  have hN : ‖placeBetween Finset.univ (fun v hv ↦ hY v fun h ↦ hv (Finset.subset_univ _ h))
      (WeightedGate.ev g ())‖ ≤ 1 := by
    rw [placeBetween_univ, hz]
    exact (l2_opNorm_submatrix_le_of_injective _ (univConfigEquiv _).injective
      (univConfigEquiv _).injective).trans ((l2_opNorm_reindex_le _ _ _).trans hMa1)
  obtain ⟨w, hw, hcount, hpart, hexp, hmono, hsrc⟩ :=
    WeightedGate.exists_originalCircuit_isSourceBounded R.parties (Finset.subset_univ _) hY g
      (fun t ht ↦ (hGp t ht).2.1) (fun t ht ↦ (hGp t ht).2.2.1) hN
  let e : ∀ s, R.newFrame.system s ≃ R.gateSystem q s :=
    fun s ↦ (R.gateTagEquiv hR s).prodCongr (Equiv.refl _)
  refine ⟨w.comp (OriginalCircuit.relabel e), Ma, hMa1, hMa, href, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨hsrc _ fun t ht ↦ (hGp t ht).2.2.2.1,
      OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero
        (OriginalCircuit.nonprivateCount_relabel e) _⟩⟩
  · rw [OriginalCircuit.op_comp, OriginalCircuit.op_relabel, PEquiv.toMatrix_toPEquiv_mul, hw,
      placeBetween_univ, hz]
    ext y x
    simp [reindex_apply, gateConfigEquiv, oldConfigEquiv, univConfigEquiv, e]
  · rw [OriginalCircuit.nonprivateCount_comp, OriginalCircuit.nonprivateCount_relabel, add_zero]
    exact hcount
  · rintro (i | i)
    · exact hpart i
    · exact OriginalCircuit.forall_participants_of_nonprivateCount_eq_zero
        (Q := fun D ↦ (↑D : Set Party) ⊆ ↑R.parties) (OriginalCircuit.nonprivateCount_relabel e) i
  · refine hexp _ _ (fun t ht ↦ (hGp t ht).2.2.2.2) ?_
    refine (List.sum_le_length_nsmul _ 1 fun x hx ↦ ?_).trans ?_
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact (hGp t ht).1
    · rw [List.length_map, nsmul_eq_mul, mul_one]
      exact_mod_cast hG
  · exact OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero
      (OriginalCircuit.nonprivateCount_relabel e) _ _
  · exact w.isMonomialBounded_mono hmono hG
  · exact OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero
      (OriginalCircuit.nonprivateCount_relabel e) _

/-- **Lemma 6.3, the small-patch rewrite as one gate.** In the setting of
`exists_allowed_monomial_approx_refVec`, there are a contraction `M_30` with
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
    (hεpatch : ∀ P ∈ R.patches, ‖toEuclideanLin P.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ h ∈ R.oldAffected, ‖toEuclideanLin h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) :
    ∃ (w : OriginalCircuit R.oldFrame.system R.newFrame.system)
      (Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ), ‖Ma‖ ≤ 1 ∧
      ‖Ma - R.rewrite‖ ≤ ((L : ℝ) ^ 30)⁻¹ ∧
      ‖toEuclideanLin Ma (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.op = reindex R.newFrame.configEquiv.symm R.oldFrame.configEquiv.symm Ma ∧
      w.nonprivateCount ≤ 1 ∧ (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑R.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) := by
  obtain ⟨w, Ma, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, -⟩ :=
    R.exists_originalCircuit_refVec_isSourceBounded hR hL hnew hpatch hold hm hrold hrnew hparties
      hΩ hεpatch hεold
  exact ⟨w, Ma, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

end SmallPatchRewrite

end TNLean.PEPS.EncodedFrame
