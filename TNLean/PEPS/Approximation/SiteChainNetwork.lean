/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixCyclicPathSum
import TNLean.PEPS.Approximation.EncodedFrame
import TNLean.PEPS.Approximation.WholeGroupContraction

/-!
# Chains of rank-one site operators as tensor networks

The proof of Lemma 6.3 `lem:small-rewrite` of the polynomial-PEPS manuscript reads every branch
of the canonical rewrite as a tensor network of normalized bras and kets. This file builds that
network for an arbitrary ordered product of rank-one site operators and identifies its
contraction with the product.

A *step* is an operator `|k⟩⟨b|_S ⊗ 1` on the raw registers `ℂ^q` of a sheet, acting on the
sites of a finite set `S`; its output vector `k` and its input vector `b` are vectors on the
configurations of `S`, or the product zero vector `|0⟩^{⊗ S}`. In a chain `L_0 L_1 ⋯ L_{n-1}`
the step `n - 1` is applied first. Each step contributes two vertices, its bra `⟨b|` and its ket
`|k⟩`, kept distinct. Following every site in chronological order through the steps touching
it, the output of a ket at that site is joined to the input of the next bra touching it; these
are the wires. The input of a bra at a site touched by no earlier step is an open input leg, and
the output of a ket at a site touched by no later step is an open output leg, unless the vector
of that vertex is the product zero vector, whose legs are fixed to `0`. Sites touched by no step
are passed through. Every wire joins a ket to a bra, so no wire joins a vertex to itself.

## Main definitions

* `SiteChain.Step`, `SiteChain.Step.op`: rank-one steps and their operators.
* `SiteChain.chainOp`: the ordered product of the operators of a chain.
* `SiteChain.Edge`, `SiteChain.tail`, `SiteChain.head`: the wires and their endpoints.
* `SiteChain.IsOpen`, `SiteChain.Group`: the open legs of a vertex and their configurations.
* `SiteChain.tensor`: the vertex tensors of the network.
* `SiteChain.Good`, `SiteChain.groupsOf`: the configurations on which the chain operator can be
  nonzero, and the open-leg configurations they determine.

## Main results

* `SiteChain.chainOp_apply`: the chain operator is the contraction of its network.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 257–281.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators

noncomputable section

namespace TNLean.PEPS.SiteChain

open EncodedFrame WholeGroup

/-! ### Rank-one steps -/

/-- A rank-one step `|k⟩⟨b|_S ⊗ 1` on the sites of a finite set `S`. The output vector `k` and the
input vector `b` are vectors on the configurations of `S`, or the product zero vector
`|0⟩^{⊗ S}`, recorded as `none`. No norm is imposed here; the truncation results assume norm at
most one. -/
structure Step (ι : Type*) (q : ℕ) where
  /-- The sites on which the step acts. -/
  sites : Finset ι
  /-- The output vector, or `none` for the product zero vector. -/
  ket : Option (EuclideanSpace ℂ (sites → Fin q))
  /-- The input vector, or `none` for the product zero vector. -/
  bra : Option (EuclideanSpace ℂ (sites → Fin q))

variable {ι : Type*} {q : ℕ}

namespace Step

variable [NeZero q]

section

variable (s : Step ι q)

/-- The product zero vector `|0⟩^{⊗ S}` on the sites of the step. -/
def zeroState : EuclideanSpace ℂ (s.sites → Fin q) := WithLp.toLp 2 (zeroVec s.sites)

/-- The output vector of the step. -/
def ketVec : EuclideanSpace ℂ (s.sites → Fin q) := s.ket.getD s.zeroState

/-- The input vector of the step. -/
def braVec : EuclideanSpace ℂ (s.sites → Fin q) := s.bra.getD s.zeroState

theorem zeroState_apply_of_ne {c : s.sites → Fin q} (hc : c ≠ 0) : s.zeroState c = 0 := by
  simp [zeroState, zeroVec, hc]

theorem ketVec_of_none (h : s.ket = none) : s.ketVec = s.zeroState := by
  simp [ketVec, h]

theorem braVec_of_none (h : s.bra = none) : s.braVec = s.zeroState := by
  simp [braVec, h]

end

variable [DecidableEq ι]

theorem norm_zeroState (s : Step ι q) : ‖s.zeroState‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  rw [Finset.sum_eq_single (0 : s.sites → Fin q) (fun c _ hc => by
    rw [zeroState_apply_of_ne s hc, norm_zero, zero_pow two_ne_zero]) (by simp)]
  simp [zeroState, zeroVec]

theorem norm_ketVec_le_one {s : Step ι q} (h : ∀ v ∈ s.ket, ‖v‖ ≤ 1) : ‖s.ketVec‖ ≤ 1 := by
  rcases hs : s.ket with _ | v
  · rw [ketVec_of_none s hs, norm_zeroState]
  · rw [ketVec, hs]
    exact h v hs

theorem norm_braVec_le_one {s : Step ι q} (h : ∀ v ∈ s.bra, ‖v‖ ≤ 1) : ‖s.braVec‖ ≤ 1 := by
  rcases hs : s.bra with _ | v
  · rw [braVec_of_none s hs, norm_zeroState]
  · rw [braVec, hs]
    exact h v hs

variable [Fintype ι] (s : Step ι q)

/-- The operator `|k⟩⟨b|_S ⊗ 1` of the step. -/
def op : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  siteLift s.sites (vecMulVec ⇑s.ketVec (star ⇑s.braVec))

theorem op_apply (ρ ρ' : ι → Fin q) :
    s.op ρ ρ' = if ∀ x ∉ s.sites, ρ x = ρ' x then
      s.ketVec (fun x => ρ x) * star (s.braVec (fun x => ρ' x)) else 0 := by
  rw [op, siteLift, embedOp_apply]
  have h : AgreeOff (Subtype.val : s.sites → ι) ρ ρ' ↔ ∀ x ∉ s.sites, ρ x = ρ' x :=
    forall_congr' fun x => imp_congr_left
      ⟨fun h hx => h ⟨x, hx⟩ rfl, fun h j hj => h (hj ▸ j.2)⟩
  simp only [h, vecMulVec_apply, Pi.star_apply]
  rfl

end Step

/-! ### Chains of steps and their wires -/

variable {n : ℕ} (st : Fin n → Step ι q)

/-- A site touched by no step. -/
def Untouched (x : ι) : Prop := ∀ i, x ∉ (st i).sites

/-- The site `x` is touched by a step applied after the step `i`. -/
def LaterTouch (i : Fin n) (x : ι) : Prop := ∃ j < i, x ∈ (st j).sites

/-- The site `x` is touched by a step applied before the step `i`. -/
def EarlierTouch (i : Fin n) (x : ι) : Prop := ∃ j, i < j ∧ x ∈ (st j).sites

/-! ### Paths along a chain -/

section Path

variable {st} {ρ : Fin (n + 1) → ι → Fin q}

/-- Along a path whose consecutive configurations agree off the sites of each step, a site keeps
its value across steps that do not touch it. -/
theorem path_const (hρ : ∀ i : Fin n, ∀ x ∉ (st i).sites, ρ i.castSucc x = ρ i.succ x)
    (x : ι) (a : ℕ) (ha : a ≤ n) : ∀ b, a ≤ b → ∀ hb : b ≤ n,
      (∀ i : Fin n, a ≤ i → (i : ℕ) < b → x ∉ (st i).sites) →
        ρ ⟨a, Nat.lt_succ_of_le ha⟩ x = ρ ⟨b, Nat.lt_succ_of_le hb⟩ x
  | 0, hab, _, _ => by
    obtain rfl : a = 0 := Nat.le_zero.mp hab
    rfl
  | b + 1, hab, hb, h => by
    rcases Nat.lt_or_eq_of_le hab with hab | rfl
    · rw [path_const hρ x a ha b (Nat.le_of_lt_succ hab) (Nat.le_of_succ_le hb)
        fun i hi hib => h i hi (Nat.lt_succ_of_lt hib)]
      exact hρ ⟨b, hb⟩ x (h ⟨b, hb⟩ (Nat.le_of_lt_succ hab) (Nat.lt_succ_self b))
    · rfl

/-- Along a path of nonzero weight, a site keeps its value across steps that do not touch it. -/
theorem path_const_fin
    (hρ : ∀ i : Fin n, ∀ x ∉ (st i).sites, ρ i.castSucc x = ρ i.succ x) (x : ι)
    {a b : Fin (n + 1)} (hab : a ≤ b)
    (h : ∀ i : Fin n, (a : ℕ) ≤ i → (i : ℕ) < b → x ∉ (st i).sites) : ρ a x = ρ b x :=
  path_const hρ x a (Nat.le_of_lt_succ a.2) b hab (Nat.le_of_lt_succ b.2) h

theorem exists_outEnd {x : ι} (h : ∃ i, x ∈ (st i).sites) :
    ∃ i, x ∈ (st i).sites ∧ ¬LaterTouch st i x := by
  classical
  exact ⟨Fin.find _ h, Fin.find_spec h, fun ⟨_, hj, hx⟩ => Fin.find_min h hj hx⟩

theorem exists_inEnd {x : ι} (h : ∃ i, x ∈ (st i).sites) :
    ∃ j, x ∈ (st j).sites ∧ ¬EarlierTouch st j x := by
  classical
  obtain ⟨i, hi⟩ := h
  have hne : (Finset.univ.filter fun j => x ∈ (st j).sites).Nonempty := ⟨i, by simp [hi]⟩
  refine ⟨_, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2, fun ⟨j', hj', hx⟩ => ?_⟩
  exact absurd (Finset.le_max' _ j' (by simp [hx])) (not_le.mpr hj')

end Path

variable [DecidableEq ι]

instance (i : Fin n) (x : ι) : Decidable (LaterTouch st i x) := by
  unfold LaterTouch; infer_instance

instance (i : Fin n) (x : ι) : Decidable (EarlierTouch st i x) := by
  unfold EarlierTouch; infer_instance

/-- The internal wires: the output of the step `e.2` at the site `e.1`, when a later step touches
`e.1`. Each such wire ends at the next step touching `e.1`. -/
def Edge : Type _ := {e : ι × Fin n // e.1 ∈ (st e.2).sites ∧ LaterTouch st e.2 e.1}

instance [Fintype ι] : Fintype (Edge st) := by unfold Edge; infer_instance

instance : DecidableEq (Edge st) := by unfold Edge; infer_instance

/-- The step at which a wire ends: the largest index below `e.2` touching the site `e.1`. -/
def prevIdx (e : Edge st) : Fin n :=
  (Finset.univ.filter fun j => j < e.1.2 ∧ e.1.1 ∈ (st j).sites).max'
    (let ⟨j, hj, hx⟩ := e.2.2; ⟨j, by simp [hj, hx]⟩)

theorem prevIdx_spec (e : Edge st) : prevIdx st e < e.1.2 ∧ e.1.1 ∈ (st (prevIdx st e)).sites := by
  have h := Finset.max'_mem (Finset.univ.filter fun j => j < e.1.2 ∧ e.1.1 ∈ (st j).sites)
    (let ⟨j, hj, hx⟩ := e.2.2; ⟨j, by simp [hj, hx]⟩)
  exact (Finset.mem_filter.mp h).2

theorem le_prevIdx (e : Edge st) {j : Fin n} (hj : j < e.1.2) (hx : e.1.1 ∈ (st j).sites) :
    j ≤ prevIdx st e :=
  Finset.le_max' _ j (by simp [hj, hx])

/-- The step applied first after the step `j` that touches the site `x`. -/
def nextIdx (j : Fin n) (x : ι) (h : EarlierTouch st j x) : Fin n :=
  Fin.find (fun i => j < i ∧ x ∈ (st i).sites) h

/-- The wire entering the step `j` at a site `x` touched by an earlier step. -/
def edgeInto (j : Fin n) (x : ι) (hx : x ∈ (st j).sites) (h : EarlierTouch st j x) : Edge st :=
  ⟨(x, nextIdx st j x h), (Fin.find_spec h).2, ⟨j, (Fin.find_spec h).1, hx⟩⟩

theorem prevIdx_edgeInto (j : Fin n) (x : ι) (hx : x ∈ (st j).sites) (h : EarlierTouch st j x) :
    prevIdx st (edgeInto st j x hx h) = j := by
  obtain ⟨hlt, hmem⟩ := prevIdx_spec st (edgeInto st j x hx h)
  refine le_antisymm ?_ (le_prevIdx st _ (Fin.find_spec h).1 hx)
  by_contra hjp
  exact Fin.find_min h hlt ⟨lt_of_not_ge hjp, hmem⟩

theorem edgeInto_prevIdx (e : Edge st) :
    edgeInto st (prevIdx st e) e.1.1 (prevIdx_spec st e).2
      ⟨e.1.2, (prevIdx_spec st e).1, e.2.1⟩ = e := by
  refine Subtype.ext (Prod.ext rfl ?_)
  refine (Fin.find_eq_iff _).mpr ⟨⟨(prevIdx_spec st e).1, e.2.1⟩, fun i hi h => ?_⟩
  exact absurd (le_prevIdx st e hi h.2) (not_le.mpr h.1)

/-- The tail of a wire: the output (ket) vertex of the step `e.2`. Vertices `inl j` are the input
(bra) vertices and vertices `inr i` the output (ket) vertices. -/
def tail (e : Edge st) : Fin n ⊕ Fin n := .inr e.1.2

/-- The head of a wire: the input (bra) vertex of the next step touching its site. -/
def head (e : Edge st) : Fin n ⊕ Fin n := .inl (prevIdx st e)

theorem tail_ne_head (e : Edge st) : tail st e ≠ head st e := Sum.inr_ne_inl

/-- The open legs of a vertex: the input legs of a bra vertex at sites touched by no earlier
step, and the output legs of a ket vertex at sites touched by no later step, unless the vector of
that vertex is the product zero vector. -/
def IsOpen : Fin n ⊕ Fin n → ι → Prop
  | .inl j, x => x ∈ (st j).sites ∧ ¬EarlierTouch st j x ∧ (st j).bra.isSome
  | .inr i, x => x ∈ (st i).sites ∧ ¬LaterTouch st i x ∧ (st i).ket.isSome

instance (v : Fin n ⊕ Fin n) : DecidablePred (IsOpen st v) := by
  cases v <;> (intro x; unfold IsOpen; infer_instance)

/-- The configurations of the open-leg group of a vertex. -/
abbrev Group (v : Fin n ⊕ Fin n) : Type _ := {x // IsOpen st v x} → Fin q

instance : DecidablePred (Untouched st) := fun x => by
  unfold Untouched; infer_instance

/-! ### The wire configurations of a labelling -/

section Wire

variable (σ τ : ι → Fin q) (β : Edge st → Fin q)

/-- The output of the step `j` at a site `x` it touches: the wire label when a later step touches
`x`, and the output configuration otherwise. -/
def outVal (j : Fin n) (x : ι) (hx : x ∈ (st j).sites) : Fin q :=
  if h : LaterTouch st j x then β ⟨(x, j), hx, h⟩ else σ x

/-- The configuration between the steps `k - 1` and `k` determined by a labelling of the wires:
the output of the last step at index `≥ k` touching the site, or the input configuration. -/
def wire (k : Fin (n + 1)) (x : ι) : Fin q :=
  if h : ∃ j : Fin n, (k : ℕ) ≤ j ∧ x ∈ (st j).sites then
    outVal st σ β (Fin.find _ h) x (Fin.find_spec h).2
  else τ x

theorem outVal_congr {j j' : Fin n} (h : j = j') (x : ι) (hx : x ∈ (st j).sites)
    (hx' : x ∈ (st j').sites) : outVal st σ β j x hx = outVal st σ β j' x hx' := by
  subst h; rfl

theorem wire_eq_of_find {k : Fin (n + 1)} {x : ι} {j : Fin n} (hj : (k : ℕ) ≤ j)
    (hx : x ∈ (st j).sites) (hmin : ∀ j' < j, (k : ℕ) ≤ j' → x ∉ (st j').sites) :
    wire st σ τ β k x = outVal st σ β j x hx := by
  rw [wire, dite_eq_left ⟨j, hj, hx⟩]
  exact outVal_congr st σ β
    ((Fin.find_eq_iff _).mpr ⟨⟨hj, hx⟩, fun j' hj' h => hmin j' hj' h.1 h.2⟩)
    x _ hx

theorem wire_eq_of_not {k : Fin (n + 1)} {x : ι}
    (h : ∀ j : Fin n, (k : ℕ) ≤ j → x ∉ (st j).sites) : wire st σ τ β k x = τ x := by
  rw [wire, dite_eq_right fun ⟨j, hj, hx⟩ => h j hj hx]

theorem wire_castSucc {i : Fin n} {x : ι} (hx : x ∈ (st i).sites) :
    wire st σ τ β i.castSucc x = outVal st σ β i x hx :=
  wire_eq_of_find st σ τ β (le_refl _) hx fun _ hj' h => absurd h (not_le.mpr hj')

theorem wire_succ {j : Fin n} {x : ι} (hx : x ∈ (st j).sites) :
    wire st σ τ β j.succ x =
      if h : EarlierTouch st j x then β (edgeInto st j x hx h) else τ x := by
  split_ifs with h
  · have hs := Fin.find_spec h
    rw [wire_eq_of_find st σ τ β (j := nextIdx st j x h) (by rw [Fin.val_succ]; exact hs.1) hs.2
      fun j' hj' hk hx' => Fin.find_min h hj' ⟨by rw [Fin.val_succ] at hk; exact hk, hx'⟩]
    exact dite_eq_left ⟨j, hs.1, hx⟩
  · exact wire_eq_of_not st σ τ β fun j' hj' hx' => h ⟨j', hj', hx'⟩

theorem wire_castSucc_eq_succ {i : Fin n} {x : ι} (hx : x ∉ (st i).sites) :
    wire st σ τ β i.castSucc x = wire st σ τ β i.succ x := by
  by_cases h : ∃ j : Fin n, ((i.succ : Fin (n + 1)) : ℕ) ≤ j ∧ x ∈ (st j).sites
  · have hs := Fin.find_spec h
    have hR : wire st σ τ β i.succ x = outVal st σ β (Fin.find _ h) x hs.2 := by
      rw [wire, dite_eq_left h]
    rw [hR]
    refine wire_eq_of_find st σ τ β (j := Fin.find _ h)
      (Nat.le_of_succ_le (n := (i : ℕ)) hs.1) hs.2 ?_
    intro j' hj' hk hx'
    refine Fin.find_min h hj' ⟨?_, hx'⟩
    rcases Nat.lt_or_eq_of_le hk with hk | hk
    · exact hk
    · exact absurd ((Fin.ext hk.symm : j' = i) ▸ hx') hx
  · push Not at h
    rw [wire_eq_of_not st σ τ β h, wire_eq_of_not st σ τ β]
    intro j hj hx'
    rcases Nat.lt_or_eq_of_le hj with hj | hj
    · exact h j hj hx'
    · exact hx ((Fin.ext hj.symm : j = i) ▸ hx')

theorem wire_last (x : ι) : wire st σ τ β (Fin.last n) x = τ x :=
  wire_eq_of_not st σ τ β fun j hj _ => absurd j.2 (not_lt.mpr hj)

theorem wire_zero (hσ : ∀ x, Untouched st x → σ x = τ x) (x : ι) :
    wire st σ τ β 0 x = σ x := by
  by_cases h : ∃ j : Fin n, x ∈ (st j).sites
  · obtain ⟨j, hj⟩ := h
    have hex : ∃ j : Fin n, ((0 : Fin (n + 1)) : ℕ) ≤ j ∧ x ∈ (st j).sites :=
      ⟨j, Nat.zero_le _, hj⟩
    rw [wire, dite_eq_left hex, outVal, dite_eq_right]
    rintro ⟨j', hj', hx'⟩
    exact Fin.find_min hex hj' ⟨Nat.zero_le _, hx'⟩
  · push Not at h
    rw [wire_eq_of_not st σ τ β fun j _ => h j]
    exact (hσ x h).symm

theorem wire_edge (e : Edge st) : wire st σ τ β e.1.2.castSucc e.1.1 = β e := by
  rw [wire_castSucc st σ τ β e.2.1, outVal, dite_eq_left e.2.2]
  rfl

theorem wire_injective (σ τ : ι → Fin q) : Function.Injective (wire st σ τ) := fun β β' h =>
  funext fun e => by rw [← wire_edge st σ τ β e, ← wire_edge st σ τ β' e, h]

end Wire

section Path

variable {st} {ρ : Fin (n + 1) → ι → Fin q}

/-- A path with nonzero weight is the wire configuration of the labelling it induces. -/
theorem eq_wire_of_path {σ τ : ι → Fin q}
    (hρ : ∀ i : Fin n, ∀ x ∉ (st i).sites, ρ i.castSucc x = ρ i.succ x)
    (h0 : ρ 0 = σ) (hn : ρ (Fin.last n) = τ) :
    ρ = wire st σ τ (fun e => ρ e.1.2.castSucc e.1.1) := by
  funext k x
  by_cases h : ∃ j : Fin n, (k : ℕ) ≤ j ∧ x ∈ (st j).sites
  · have hs := Fin.find_spec h
    set j := Fin.find _ h
    rw [wire, dite_eq_left h]
    have hkj : ρ k x = ρ j.castSucc x :=
      path_const hρ x k (Nat.le_of_lt_succ k.2) j hs.1 j.2.le
        fun i hki hij hxi => Fin.find_min h hij ⟨hki, hxi⟩
    rw [hkj, outVal]
    split_ifs with hl
    · rfl
    · rw [← h0]
      exact (path_const hρ x 0 (Nat.zero_le _) j (Nat.zero_le _) j.2.le
        fun i _ hij hxi => hl ⟨i, hij, hxi⟩).symm
  · push Not at h
    rw [wire_eq_of_not _ _ _ _ h, ← hn]
    exact path_const hρ x k (Nat.le_of_lt_succ k.2) n (Nat.le_of_lt_succ k.2) le_rfl
      fun i hki _ => h i hki

end Path

variable [NeZero q]

/-- The local output configuration of the ket vertex of the step `i`: wire labels on the sites
touched later, the open legs elsewhere, and `0` for a product zero vector. -/
def ketCfg (i : Fin n) (lab : {e // IsIncident (tail st) (head st) (.inr i) e} → Fin q)
    (o : Group st (.inr i)) : (st i).sites → Fin q := fun x =>
  if h : LaterTouch st i x.1 then lab ⟨⟨(x.1, i), x.2, h⟩, Or.inl rfl⟩
  else if hk : (st i).ket.isSome then o ⟨x.1, x.2, h, hk⟩ else 0

/-- The local input configuration of the bra vertex of the step `j`. -/
def braCfg (j : Fin n) (lab : {e // IsIncident (tail st) (head st) (.inl j) e} → Fin q)
    (o : Group st (.inl j)) : (st j).sites → Fin q := fun x =>
  if h : EarlierTouch st j x.1 then
    lab ⟨edgeInto st j x.1 x.2 h, Or.inr (congrArg Sum.inl (prevIdx_edgeInto st j x.1 x.2 h))⟩
  else if hb : (st j).bra.isSome then o ⟨x.1, x.2, h, hb⟩ else 0

/-- The open-leg configurations read off from an output configuration `σ` and an input
configuration `τ`. -/
def groupsOf (σ τ : ι → Fin q) : (v : Fin n ⊕ Fin n) → Group st v
  | .inl _ => fun x => τ x.1
  | .inr _ => fun x => σ x.1

/-- A site whose first step has the product zero vector as input. -/
def FixedIn (x : ι) : Prop :=
  ∃ j, x ∈ (st j).sites ∧ ¬EarlierTouch st j x ∧ (st j).bra.isSome = false

/-- A site whose last step has the product zero vector as output. -/
def FixedOut (x : ι) : Prop :=
  ∃ i, x ∈ (st i).sites ∧ ¬LaterTouch st i x ∧ (st i).ket.isSome = false

/-- The configurations on which the chain operator can be nonzero: untouched sites are passed
through, and the sites entering or leaving through a product zero vector carry `0`. -/
def Good (σ τ : ι → Fin q) : Prop :=
  (∀ x, Untouched st x → σ x = τ x) ∧ (∀ x, FixedIn st x → τ x = 0) ∧
    (∀ x, FixedOut st x → σ x = 0)

theorem ketCfg_groupsOf {σ τ : ι → Fin q} (hG : Good st σ τ) (β : Edge st → Fin q) (i : Fin n) :
    ketCfg st i (fun e => β e) (groupsOf st σ τ (.inr i)) =
      fun x : (st i).sites => wire st σ τ β i.castSucc x := by
  funext x
  rw [wire_castSucc st σ τ β x.2, ketCfg, outVal]
  by_cases h : LaterTouch st i x.1
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h]
    by_cases hk : (st i).ket.isSome
    · rw [dite_eq_left hk]
      rfl
    · rw [dite_eq_right hk]
      exact (hG.2.2 x ⟨i, x.2, h, by simpa using hk⟩).symm

theorem braCfg_groupsOf {σ τ : ι → Fin q} (hG : Good st σ τ) (β : Edge st → Fin q) (j : Fin n) :
    braCfg st j (fun e => β e) (groupsOf st σ τ (.inl j)) =
      fun x : (st j).sites => wire st σ τ β j.succ x := by
  funext x
  rw [wire_succ st σ τ β x.2, braCfg]
  by_cases h : EarlierTouch st j x.1
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h]
    by_cases hb : (st j).bra.isSome
    · rw [dite_eq_left hb]
      rfl
    · rw [dite_eq_right hb]
      exact (hG.2.1 x ⟨j, x.2, h, by simpa using hb⟩).symm

variable [Fintype ι]

instance (σ τ : ι → Fin q) : Decidable (Good st σ τ) := by
  unfold Good Untouched FixedIn FixedOut; infer_instance

/-- The ordered product `L_0 L_1 ⋯ L_{n-1}` of the operators of the steps; the step `n - 1` is
applied first. -/
def chainOp : Matrix (ι → Fin q) (ι → Fin q) ℂ := (List.ofFn fun i => (st i).op).prod

/-- The vertex tensors of the network of a chain: the conjugate input vector at each bra vertex
and the output vector at each ket vertex. -/
def tensor : VertexTensors (tail st) (head st) (fun _ => Fin q) (Group st)
  | .inl j => fun lab o => star ((st j).braVec (braCfg st j lab o))
  | .inr i => fun lab o => (st i).ketVec (ketCfg st i lab o)

/-! ### The chain operator as the contraction of its network -/

section Contraction

variable {σ τ : ι → Fin q}

/-- A path of nonzero weight has the prescribed endpoints, consecutive configurations agree off
the sites of each step, and the vectors of each step do not vanish on it. -/
theorem path_of_ne_zero {ρ : Fin (n + 1) → ι → Fin q}
    (h : (if ρ 0 = σ ∧ ρ (Fin.last n) = τ then
      ∏ i : Fin n, (st i).op (ρ i.castSucc) (ρ i.succ) else 0) ≠ 0) :
    ρ 0 = σ ∧ ρ (Fin.last n) = τ ∧ ∀ i : Fin n,
      (∀ x ∉ (st i).sites, ρ i.castSucc x = ρ i.succ x) ∧
        (st i).ketVec (fun x => ρ i.castSucc x) ≠ 0 ∧
          (st i).braVec (fun x => ρ i.succ x) ≠ 0 := by
  split_ifs at h with hend
  · refine ⟨hend.1, hend.2, fun i => ?_⟩
    have hi := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ _)
    rw [Step.op_apply] at hi
    split_ifs at hi with hag
    · exact ⟨hag, left_ne_zero_of_mul hi, fun h0 => hi (by rw [h0, star_zero, mul_zero])⟩
    · exact absurd rfl hi
  · exact absurd rfl h

/-- **The chain operator is the contraction of its network.** For every output configuration `σ`
and input configuration `τ`, the entry of `L_0 ⋯ L_{n-1}` vanishes unless the untouched sites
are passed through and the sites entering or leaving through product zero vectors carry `0`; in
that case it is the contraction of the network of bras and kets, evaluated on the open legs read
off from `σ` and `τ`. Each wire joins the output of a step at a site to the next step touching
that site, so no wire joins a vertex to itself.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
`05-frames.tex`, lines 274–281. -/
theorem chainOp_apply (σ τ : ι → Fin q) :
    chainOp st σ τ = if Good st σ τ then contraction (tensor st) (groupsOf st σ τ) else 0 := by
  rw [chainOp, Matrix.ofFn_prod_apply]
  split_ifs with hG
  · symm
    refine Fintype.sum_of_injective (wire st σ τ) (wire_injective st σ τ) _ _ ?_ ?_
    · intro ρ hρ
      by_contra hne
      obtain ⟨h0, hn, hstep⟩ := path_of_ne_zero st hne
      exact hρ ⟨_, (eq_wire_of_path (fun i => (hstep i).1) h0 hn).symm⟩
    · intro β
      rw [ite_eq_left ⟨funext (wire_zero st σ τ β hG.1), funext (wire_last st σ τ β)⟩,
        Fintype.prod_sum_type, mul_comm, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Step.op_apply, ite_eq_left fun x hx => wire_castSucc_eq_succ st σ τ β hx]
      change (st i).ketVec (ketCfg st i (fun e => β e) (groupsOf st σ τ (.inr i))) *
          star ((st i).braVec (braCfg st i (fun e => β e) (groupsOf st σ τ (.inl i)))) = _
      rw [ketCfg_groupsOf st hG, braCfg_groupsOf st hG]
  · refine Finset.sum_eq_zero fun ρ _ => ?_
    by_contra hne
    obtain ⟨h0, hn, hstep⟩ := path_of_ne_zero st hne
    have hρ := fun i => (hstep i).1
    refine hG ⟨fun x hx => ?_, fun x ⟨j, hxj, hE, hb⟩ => ?_, fun x ⟨i, hxi, hL, hk⟩ => ?_⟩
    · rw [← h0, ← hn]
      exact path_const_fin hρ x (Fin.zero_le _) fun i _ _ => hx i
    · by_contra hτ
      refine (hstep j).2.2 ?_
      rw [Step.braVec_of_none _ (by simpa using hb)]
      refine Step.zeroState_apply_of_ne _ fun hc => hτ ?_
      have hx : ρ j.succ x = τ x := by
        rw [← hn]
        exact path_const_fin hρ x (Fin.le_last _) fun i hi _ hxi => hE ⟨i, hi, hxi⟩
      rw [← hx]
      exact congrFun hc ⟨x, hxj⟩
    · by_contra hσ
      refine (hstep i).2.1 ?_
      rw [Step.ketVec_of_none _ (by simpa using hk)]
      refine Step.zeroState_apply_of_ne _ fun hc => hσ ?_
      have hx : ρ i.castSucc x = σ x := by
        rw [← h0]
        exact (path_const_fin hρ x (Fin.zero_le _) fun j _ hj hxj => hL ⟨j, hj, hxj⟩).symm
      rw [← hx]
      exact congrFun hc ⟨x, hxi⟩

end Contraction

end TNLean.PEPS.SiteChain
