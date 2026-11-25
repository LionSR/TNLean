/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Norm.MatrixKroneckerContraction
import QICLean.Circuit.Party.Original.Basic
import QICLean.Circuit.Party.Syntax.RestrictMonomial

/-!
# A sum of monomials on a set of parties as one gate, with its pair sources

A bounded change of the protocol of Proposition 7.1 may be a sum `∑_ξ c_ξ M_ξ` of allowed
monomials, as in the small-patch rewrite of Lemma 6.3, all of which use only the parties of a
fixed finite set `S` (`06-geometry.tex`, lines 574–583). Such a sum is a weighted gate on a cell
`D ⊇ S` whose monomials use only `S`; outside `S` they act as the identification of the equal
bases. Reading every monomial on the parties of `S` (`WeightedGate.restrict`) gives a weighted gate
on the cell `S` with the same operator, the same coefficients and the same numbers of pair effects
and pair sources in each monomial. If `S` has a single party, the gate is a contraction of that
party instead, as the original circuits require.

## Main results

* `TNLean.PEPS.PairEffect.norm_le_norm_placeBetween`: placing a matrix on a region does not
  decrease its norm when the configurations outside the region exist.
* `QuantumCircuit.Party.WeightedGate.exists_originalCircuit_of_norm_le_one`: a contraction on a
  set of parties with allowed monomials is an original circuit of these parties.
* `QuantumCircuit.Party.WeightedGate.exists_originalCircuit_isSourceBounded`: such a sum is an
  original circuit with at most one nonprivate gate, whose participants lie in `S`, with the
  pair-effect, coefficient, monomial and pair-source bounds of the sum.
* `QuantumCircuit.Party.WeightedGate.exists_originalCircuit`: the same without the pair-source
  bound.

## References

* Polynomial-PEPS manuscript (September 24, 2026), original circuits, `04-compression.tex`,
  lines 21–43 and 199–208; Theorem 5.2, item 3, lines 143–147; the gates of Proposition 7.1,
  `06-geometry.tex`, lines 574–583; Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`,
  lines 188–218.
-/

noncomputable section

open Matrix ManyBody QuantumCircuit.Party
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.PairEffect

variable {P : Type} [DecidableEq P]

variable [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [∀ p, DecidableEq (Y p)] in
/-- **Placing a matrix on a region does not decrease its norm** when the region has a
complement configuration: the matrix is a submatrix of its placement. -/
theorem norm_le_norm_placeBetween (D : Finset P) (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) (z : ComplConfig X D) :
    ‖K‖ ≤ ‖placeBetween D hXY K‖ := by
  classical
  have hK : K = (placeBetween D hXY K).submatrix
      (fun a ↦ (cutEquiv Y D).symm (a, complCast hXY z)) (fun b ↦ (cutEquiv X D).symm (b, z)) := by
    ext a b
    exact (placeBetween_apply_cutEquiv_symm hXY K a b z).symm
  conv_lhs => rw [hK]
  refine l2_opNorm_submatrix_le_of_injective _ (fun a a' h ↦ ?_) (fun b b' h ↦ ?_)
  · simpa using congrArg Prod.fst ((cutEquiv Y D).symm.injective h)
  · simpa using congrArg Prod.fst ((cutEquiv X D).symm.injective h)

/-- The configurations of a one-party region are those of its party. -/
def singletonConfigEquiv (T : P → Type) {S : Finset P} {p : P} (hS : S = {p}) :
    RegionConfig T S ≃ T p where
  toFun y := y ⟨p, hS ▸ Finset.mem_singleton_self p⟩
  invFun a v := cast (congrArg T (Finset.mem_singleton.mp (hS ▸ v.2)).symm) a
  left_inv y := by
    funext v
    obtain ⟨v, hv⟩ := v
    obtain rfl := Finset.mem_singleton.mp (hS ▸ hv)
    rfl
  right_inv _ := rfl

omit [∀ p, Fintype (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- A matrix on a one-party region, read on its party and placed back at that party, is the
matrix placed on the region. -/
theorem placeBetween_submatrix_singletonConfigEquiv {S : Finset P} {p : P} (hS : S = {p})
    (hY : ∀ v ∉ S, Y v = X v) (K : Matrix (RegionConfig Y S) (RegionConfig X S) ℂ) :
    placeBetween {p} (fun v hv ↦ hY v (hS ▸ hv))
        ((reindex (singletonConfigEquiv Y hS) (singletonConfigEquiv X hS) K).submatrix
          (fun y ↦ y ⟨p, Finset.mem_singleton_self p⟩)
          (fun x ↦ x ⟨p, Finset.mem_singleton_self p⟩)) =
      placeBetween S hY K := by
  subst hS
  congr 1
  ext y x
  simp only [submatrix_apply, reindex_apply]
  congr 1 <;> exact (singletonConfigEquiv _ rfl).left_inv _

end TNLean.PEPS.PairEffect

namespace QuantumCircuit.Party.WeightedGate

open TNLean.PEPS.PairEffect

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- **A contraction with allowed monomials on a set of parties is one gate of these parties.** A
weighted gate `g` on the cell `S` whose monomials are allowed and whose matrix is a contraction,
placed on `S`, is the operator of an original circuit with at most one nonprivate gate, whose
participants lie in `S`, and whose expansion has the coefficients and the monomials of `g`. If `S`
has a single party, the circuit is a contraction of that party. Polynomial-PEPS manuscript,
`04-compression.tex`, lines 21–43 and 199–208. -/
theorem exists_originalCircuit_of_norm_le_one (S : Finset P) (hY : ∀ v ∉ S, Y v = X v)
    (g : WeightedGate S X Y) (hA : WeightedGate.IsAllowed g) (hN : ‖WeightedGate.ev g ()‖ ≤ 1) :
    ∃ c : OriginalCircuit X Y,
      c.op = placeBetween S hY (WeightedGate.ev g ()) ∧
      c.nonprivateCount ≤ 1 ∧ (∀ i, (↑(c.participants i) : Set P) ⊆ ↑S) ∧
      (∀ (r : ℕ) (s : ℝ), (∀ t ∈ g.terms, t.2.effectCount ≤ r) →
        (g.terms.map fun t ↦ ‖t.1‖).sum ≤ s → c.IsExpansionBounded r s) ∧
      (∀ K : ℕ, g.terms.length ≤ K → c.IsMonomialBounded K) ∧
      ∀ r : ℕ, (∀ t ∈ g.terms, t.2.sourceCount ≤ r) → c.IsSourceBounded r := by
  by_cases hC : S.card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hC
    have hYp : ∀ v ≠ p, Y v = X v := fun v hv ↦ hY v (by simpa [hp] using hv)
    let U := reindex (singletonConfigEquiv Y hp) (singletonConfigEquiv X hp) (WeightedGate.ev g ())
    have hU1 : ‖U‖ ≤ 1 := (l2_opNorm_reindex_le _ _ _).trans hN
    refine ⟨OriginalCircuit.localOp p hYp U hU1, ?_, by simp, fun i ↦ i.elim, fun _ _ _ _ ↦ trivial,
      fun _ _ ↦ trivial, fun _ _ ↦ trivial⟩
    rw [OriginalCircuit.op_localOp]
    exact placeBetween_submatrix_singletonConfigEquiv hp hY _
  · exact ⟨OriginalCircuit.gate S hY (OriginalGate.ofWeightedGate g hC hA hN), by
      rw [OriginalCircuit.op_gate]; rfl, by simp, fun _ ↦ subset_rfl, fun _ _ hr hs ↦ ⟨hr, hs⟩,
      fun _ hK ↦ hK, fun _ hr ↦ hr⟩

/-- **A sum of monomials on a set of parties as one gate, with its pair sources.** Let
`g = ∑_ξ c_ξ M_ξ` be a weighted gate on a cell `D` whose monomials are allowed and use only the
parties of `S ⊆ D`, the bases outside `S` being equal, and let the gate placed on its cell be a
contraction. Then the gate is the operator of an original circuit with at most one nonprivate gate,
whose participants lie in `S`. Its expansion has the coefficients and the monomials of `g`, read on
the parties of `S`, so the pair-effect and coefficient bounds of `g`, its number of monomials and
the number of pair sources of every monomial are kept. If `S` has a single party, the circuit is a
contraction of that party.

Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43, 143–147 and 199–208, and
`06-geometry.tex`, lines 574–583. -/
theorem exists_originalCircuit_isSourceBounded {D : Finset P} (S : Finset P) (hSD : S ⊆ D)
    (hY : ∀ v ∉ S, Y v = X v) (g : WeightedGate D X Y) (hA : WeightedGate.IsAllowed g)
    (hU : ∀ t ∈ g.terms, t.2.UsesOnly S)
    (hN : ‖placeBetween D (fun v hv ↦ hY v fun h ↦ hv (hSD h)) (WeightedGate.ev g ())‖ ≤ 1) :
    ∃ c : OriginalCircuit X Y,
      c.op = placeBetween D (fun v hv ↦ hY v fun h ↦ hv (hSD h)) (WeightedGate.ev g ()) ∧
      c.nonprivateCount ≤ 1 ∧ (∀ i, (↑(c.participants i) : Set P) ⊆ ↑S) ∧
      (∀ (r : ℕ) (s : ℝ), (∀ t ∈ g.terms, t.2.effectCount ≤ r) →
        (g.terms.map fun t ↦ ‖t.1‖).sum ≤ s → c.IsExpansionBounded r s) ∧
      c.IsMonomialBounded g.terms.length ∧
      ∀ r : ℕ, (∀ t ∈ g.terms, t.2.sourceCount ≤ r) → c.IsSourceBounded r := by
  set g' := g.restrict S hSD hU
  have hop : placeBetween D (fun v hv ↦ hY v fun h ↦ hv (hSD h)) (WeightedGate.ev g ()) =
      placeBetween S hY (WeightedGate.ev g' ()) := by
    have h := WeightedGate.op_gate_restrict S hSD g hU (fun v hv ↦ hY v fun h ↦ hv (hSD h)) hY
    rw [PartyCircuit.op_gate, PartyCircuit.op_gate] at h
    exact h
  by_cases hN' : ‖WeightedGate.ev g' ()‖ ≤ 1
  · obtain ⟨c, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_originalCircuit_of_norm_le_one S hY g'
      (WeightedGate.isAllowed_restrict S hSD hU hA) hN'
    refine ⟨c, h₁.trans hop.symm, h₂, h₃, fun r s hr hs ↦ h₄ r s (fun t ht ↦ ?_) ?_,
      h₅ _ (WeightedGate.length_terms_restrict S hSD g hU).le, fun r hr ↦ h₆ r fun t ht ↦ ?_⟩
    · obtain ⟨t', ht', h⟩ := WeightedGate.exists_mem_terms_of_mem_restrict S hSD (h := hU) ht
      rw [h]
      exact (Monomial.effectCount_restrict S hSD t'.2 (hU t' ht')).trans_le (hr t' ht')
    · have h := congrArg (List.map fun z : ℂ ↦ ‖z‖) (WeightedGate.map_fst_terms_restrict S hSD g hU)
      simp only [List.map_map] at h
      exact (congrArg List.sum h).trans_le hs
    · obtain ⟨t', ht', h⟩ := WeightedGate.exists_mem_terms_of_mem_restrict S hSD (h := hU) ht
      rw [h]
      exact (Monomial.sourceCount_restrict S hSD t'.2 (hU t' ht')).trans_le (hr t' ht')
  · -- The gate on `S` is not a contraction, so the configurations outside `S` do not exist, and
    -- neither do the configurations of all parties: the operator vanishes, and the gate with no
    -- monomials realizes it.
    have hE : IsEmpty (Config X) :=
      ⟨fun x ↦ hN' ((norm_le_norm_placeBetween S hY _ fun v ↦ x v).trans (hop ▸ hN))⟩
    obtain ⟨c, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_originalCircuit_of_norm_le_one S hY
      (⟨[]⟩ : WeightedGate S X Y) (fun _ h ↦ absurd h List.not_mem_nil)
      (by simp [WeightedGate.ev])
    refine ⟨c, ?_, h₂, h₃, fun r s _ hs ↦ ?_, h₅ _ (Nat.zero_le _), fun r _ ↦ h₆ r fun _ h ↦
      absurd h List.not_mem_nil⟩
    · ext _ x
      exact isEmptyElim x
    · refine c.isExpansionBounded_mono (h₄ r 0 (fun _ h ↦ absurd h List.not_mem_nil) le_rfl) le_rfl
        ((List.sum_nonneg fun _ h ↦ ?_).trans hs)
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp h
      exact norm_nonneg _

/-- **A sum of monomials using a set of parties is one gate of these parties.** The conclusion of
`exists_originalCircuit_isSourceBounded` without the pair-source bound: an original circuit with
the operator of the gate, at most one nonprivate gate, whose participants lie in `S`, and the
pair-effect, coefficient and monomial bounds of the sum.

Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43 and 199–208, and
`06-geometry.tex`, lines 574–583. -/
theorem exists_originalCircuit {D : Finset P} (S : Finset P) (hSD : S ⊆ D)
    (hY : ∀ v ∉ S, Y v = X v) (g : WeightedGate D X Y) (hA : WeightedGate.IsAllowed g)
    (hU : ∀ t ∈ g.terms, t.2.UsesOnly S)
    (hN : ‖placeBetween D (fun v hv ↦ hY v fun h ↦ hv (hSD h)) (WeightedGate.ev g ())‖ ≤ 1) :
    ∃ c : OriginalCircuit X Y,
      c.op = placeBetween D (fun v hv ↦ hY v fun h ↦ hv (hSD h)) (WeightedGate.ev g ()) ∧
      c.nonprivateCount ≤ 1 ∧ (∀ i, (↑(c.participants i) : Set P) ⊆ ↑S) ∧
      (∀ (r : ℕ) (s : ℝ), (∀ t ∈ g.terms, t.2.effectCount ≤ r) →
        (g.terms.map fun t ↦ ‖t.1‖).sum ≤ s → c.IsExpansionBounded r s) ∧
      c.IsMonomialBounded g.terms.length := by
  obtain ⟨c, h₁, h₂, h₃, h₄, h₅, -⟩ :=
    exists_originalCircuit_isSourceBounded S hSD hY g hA hU hN
  exact ⟨c, h₁, h₂, h₃, h₄, h₅⟩

end QuantumCircuit.Party.WeightedGate
