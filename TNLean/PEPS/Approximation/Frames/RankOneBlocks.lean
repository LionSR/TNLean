/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Sheet.Placement
import QICLean.Circuit.Party.Syntax.Frame
import QICLean.Circuit.Party.Syntax.Relabel
import QICLean.Circuit.Party.Syntax.RestrictMonomial
import TNLean.PEPS.Approximation.EncodedFrame

/-!
# Rank-one operators on blocks of sites as allowed monomials

The last step of the proof of Lemma 6.3 of the polynomial-PEPS manuscript reads a product of
normalized vectors and covectors on groups of sites, each group on at most two parties, as a
monomial allowed by Theorem 5.2. This file provides the operators of that reading and their
monomials on the sheets, at every party the raw configurations of the sites it owns.

* `EncodedFrame.RankOneBlock`: a block of sites split into a part `T` and a part `U`, with the
  complement `E`, and two unit vectors on `(T → Fin q) × (U → Fin q)`; its operator is
  `|v⟩⟨w|_{T ∪ U} ⊗ 1_E` (`RankOneBlock.op`, `RankOneBlock.op_apply`). Products of operators of
  pairwise disjoint blocks are computed entrywise (`RankOneBlock.prod_op_apply`).
* `EncodedFrame.zeroPair`, `EncodedFrame.exists_pairVec`: the zero basis vector of a block and a
  vector on the sites of a group read on its two parts.
* `EncodedFrame.pairBra`, `EncodedFrame.pairKet`, `EncodedFrame.privateBra`,
  `EncodedFrame.privateKet`: a bra or a ket on factors of the bases of two distinct parties (a
  pair effect or a pair source after a relabelling of the bases), or of one party (a private
  map), with their operators read through `EncodedFrame.twoPartyConfigEquiv` and
  `ManyBody.factorConfigEquiv`.
* `EncodedFrame.exists_rankOneBlock_monomial`: if the sites of `T` are owned by `p_A` before and
  `p_A'` after, and those of `U` by `p_B` and `p_B'`, the operator of a block is, in canonical
  site coordinates (`EncodedFrame.univSheetEquiv`), an allowed monomial from the sheet before to
  the sheet after, using only these four parties, with at most one pair source and at most one
  pair effect.

## Main definitions

* `EncodedFrame.RankOneBlock`, `EncodedFrame.RankOneBlock.op`, `EncodedFrame.zeroPair`.
* `EncodedFrame.univSheet`, `EncodedFrame.univSheetEquiv`, `EncodedFrame.blockRest`.

## Main results

* `EncodedFrame.RankOneBlock.op_apply`, `EncodedFrame.RankOneBlock.prod_op_apply`.
* `EncodedFrame.exists_pairVec`: a vector on the sites of a group read on its two parts.
* `EncodedFrame.exists_sheetBra`, `EncodedFrame.exists_sheetKet`,
  `EncodedFrame.exists_rankOneBlock_monomial`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 306–316; allowed monomials, `04-compression.tex`, lines 32–35.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

noncomputable section

open Matrix

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

variable (ι q) in
/-- A rank-one block: the sites outside `E`, split into `T` and `U = (T ∪ E)ᶜ`, carry the
rank-one map `|v⟩⟨w|`, with `v` and `w` vectors on `(T → Fin q) × (U → Fin q)`; the sites of
`E` are untouched. -/
structure RankOneBlock where
  /-- The first part of the block. -/
  T : Finset ι
  /-- The sites outside the block. -/
  E : Finset ι
  /-- The first part of the block lies in the block. -/
  disj : Disjoint T E
  /-- The output vector. -/
  ket : EuclideanSpace ℂ ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q))
  /-- The input vector. -/
  bra : EuclideanSpace ℂ ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q))

namespace RankOneBlock

variable (b : RankOneBlock ι q)

/-- The output vector read on a configuration of all sites. -/
def ketAt (c : ι → Fin q) : ℂ :=
  b.ket ((fun x : b.T => c x), (fun x : {v // v ∉ b.T ∪ b.E} => c x))

/-- The input vector read on a configuration of all sites. -/
def braAt (c : ι → Fin q) : ℂ :=
  b.bra ((fun x : b.T => c x), (fun x : {v // v ∉ b.T ∪ b.E} => c x))

/-- The operator `|v⟩⟨w|_{T ∪ U} ⊗ 1_E` of a block, entry by entry: the entry at `(c', c)` is
`v(c') \overline{w(c)}` when `c'` and `c` agree on `E`, and `0` otherwise. -/
def op : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  Matrix.of fun c' c ↦ if ∀ x ∈ b.E, c' x = c x then b.ketAt c' * star (b.braAt c) else 0

/-- The entries of the operator of a block. -/
theorem op_apply (c' c : ι → Fin q) :
    b.op c' c = if ∀ x ∈ b.E, c' x = c x then b.ketAt c' * star (b.braAt c) else 0 :=
  rfl

omit [Fintype ι] in
private theorem notMem_E_of_mem_T {x : ι} (hx : x ∈ b.T) : x ∉ b.E :=
  Finset.disjoint_left.mp b.disj hx

omit [Fintype ι] in
/-- Two configurations agreeing outside `E` agree on both parts of the block. -/
private theorem restrict_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) :
    ((fun x : b.T => c x) = fun x : b.T => c' x) ∧
      ((fun x : {v // v ∉ b.T ∪ b.E} => c x) = fun x : {v // v ∉ b.T ∪ b.E} => c' x) :=
  ⟨funext fun x => h x (b.notMem_E_of_mem_T x.2),
    funext fun x => h x fun hx => x.2 (Finset.mem_union_right _ hx)⟩

omit [Fintype ι] in
theorem ketAt_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) : b.ketAt c = b.ketAt c' := by
  obtain ⟨h₁, h₂⟩ := b.restrict_congr h
  rw [ketAt, ketAt, h₁, h₂]

omit [Fintype ι] in
theorem braAt_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) : b.braAt c = b.braAt c' := by
  obtain ⟨h₁, h₂⟩ := b.restrict_congr h
  rw [braAt, braAt, h₁, h₂]

/-- **Products of disjoint blocks.** If every site lies outside all blocks of the list but at
most one, the product of their operators has the entry `∏_b v_b(c') \overline{w_b(c)}` when `c'`
and `c` agree outside all blocks, and `0` otherwise. -/
theorem prod_op_apply : (bs : List (RankOneBlock ι q)) →
    bs.Pairwise (fun b b' => ∀ x, x ∈ b.E ∨ x ∈ b'.E) → (c' c : ι → Fin q) →
    (bs.map op).prod c' c = if ∀ x, (∀ b ∈ bs, x ∈ b.E) → c' x = c x then
      (bs.map fun b => b.ketAt c' * star (b.braAt c)).prod else 0
  | [], _, c', c => by
      have h : (c' = c) ↔ ∀ x, (∀ b ∈ ([] : List (RankOneBlock ι q)), x ∈ b.E) → c' x = c x :=
        ⟨fun h x _ => congrFun h x, fun h => funext fun x => h x fun b hb => absurd hb
          List.not_mem_nil⟩
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply, h]
  | b :: bs, hd, c', c => by
      have hdb : ∀ b' ∈ bs, ∀ x, x ∈ b.E ∨ x ∈ b'.E := (List.pairwise_cons.mp hd).1
      have ih := prod_op_apply bs (List.pairwise_cons.mp hd).2
      set c₀ : ι → Fin q := fun x => if x ∈ b.E then c' x else c x with hc₀
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply,
        Finset.sum_eq_single c₀ (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ _) h)]
      · rw [op_apply, ih, ite_eq_left fun x hx => by rw [hc₀]; simp [hx]]
        have hrest : ∀ x, (∀ b' ∈ bs, x ∈ b'.E) → c₀ x = c x ↔
            (∀ b' ∈ b :: bs, x ∈ b'.E) → c' x = c x := by
          intro x
          by_cases hx : x ∈ b.E
          · simp [hc₀, hx]
          · simp only [hc₀, hx, ite_false, List.mem_cons, forall_eq_or_imp, false_and,
              false_implies, iff_true]
            simp
        have hb : b.braAt c₀ = b.braAt c := b.braAt_congr fun x hx => by simp [hc₀, hx]
        have hk : (bs.map fun b' => b'.ketAt c₀ * star (b'.braAt c)) =
            bs.map fun b' => b'.ketAt c' * star (b'.braAt c) := by
          refine List.map_congr_left fun b' hb' => ?_
          rw [b'.ketAt_congr fun x hx => ?_]
          rcases hdb b' hb' x with h | h
          · simp [hc₀, h]
          · exact absurd h hx
        simp only [forall_congr' hrest, hb, hk, List.map_cons, List.prod_cons]
        split_ifs <;> ring
      · rw [op_apply, ih]
        split_ifs with h₁ h₂
        · refine absurd (funext fun x => ?_) ha
          by_cases hx : x ∈ b.E
          · rw [← h₁ x hx]
            simp [hc₀, hx]
          · rw [h₂ x fun b' hb' => (hdb b' hb' x).resolve_left hx]
            simp [hc₀, hx]
        all_goals simp

end RankOneBlock

/-- The basis vector of the zero configuration on `(T → Fin q) × (U → Fin q)`, the analogue of
`zeroVec` on the two parts of a block. -/
def zeroPair [NeZero q] (T E : Finset ι) :
    EuclideanSpace ℂ ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q)) :=
  EuclideanSpace.single (0, 0) 1

theorem norm_zeroPair [NeZero q] (T E : Finset ι) : ‖zeroPair (q := q) T E‖ = 1 := by
  simp [zeroPair]

/-- The zero basis vector read on a configuration: `1` if the configuration vanishes on
`T ∪ U`, and `0` otherwise. -/
theorem zeroPair_apply [NeZero q] (T E : Finset ι) (h : Disjoint T E) (c : ι → Fin q) :
    zeroPair (q := q) T E ((fun x : T => c x), (fun x : {v // v ∉ T ∪ E} => c x)) =
      if ∀ x ∉ E, c x = 0 then 1 else 0 := by
  rw [zeroPair, PiLp.single_apply]
  congr 1
  apply propext
  constructor
  · intro hc x hx
    by_cases hT : x ∈ T
    · exact congrFun (congrArg Prod.fst hc) ⟨x, hT⟩
    · exact congrFun (congrArg Prod.snd hc) ⟨x, by simp [hT, hx]⟩
  · intro hc
    refine Prod.ext (funext fun x => hc x (Finset.disjoint_left.mp h x.2))
      (funext fun x => hc x fun hx => x.2 (Finset.mem_union_right _ hx))

/-- **A vector on a group of sites, read on two parts.** Let the group be the set of sites
satisfying `O`, with complement `E`, and let `T` be part of it. Every vector `f` on the
configurations of the group is a vector of the same norm on `(T → Fin q) × (U → Fin q)`,
`U = (T ∪ E)ᶜ`, with the same values on every configuration. -/
theorem exists_pairVec (O : ι → Prop) [DecidablePred O] {T : Finset ι} (hT : ∀ x ∈ T, O x)
    (f : EuclideanSpace ℂ ({x // O x} → Fin q)) :
    ∃ v : EuclideanSpace ℂ
        ((T → Fin q) × ({v // v ∉ T ∪ Finset.univ.filter fun x => ¬O x} → Fin q)),
      ‖v‖ = ‖f‖ ∧ ∀ c : ι → Fin q,
        v ((fun x : T => c x),
          (fun x : {v // v ∉ T ∪ Finset.univ.filter fun x => ¬O x} => c x)) =
          f fun x => c x.1 := by
  set E := Finset.univ.filter fun x => ¬O x
  have hU : ∀ x : {x // O x}, x.1 ∉ T → x.1 ∉ T ∪ E := fun x hx => by
    simp [E, hx, x.2]
  have hO : ∀ x : {v // v ∉ T ∪ E}, O x.1 := fun x => by
    have : (x : ι) ∉ T ∪ E := x.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_not, E] at this
    exact this.2
  let e : ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q)) ≃ ({x // O x} → Fin q) :=
    { toFun := fun ab x => if hx : x.1 ∈ T then ab.1 ⟨x.1, hx⟩ else ab.2 ⟨x.1, hU x hx⟩
      invFun := fun d => (fun x => d ⟨x.1, hT x.1 x.2⟩, fun x => d ⟨x.1, hO x⟩)
      left_inv := fun ab => by
        refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
        · simp [x.2]
        · have hx : x.1 ∉ T := fun h => x.2 (Finset.mem_union_left _ h)
          simp [hx]
      right_inv := fun d => funext fun x => by
        by_cases hx : x.1 ∈ T <;> simp [hx] }
  refine ⟨WithLp.toLp 2 fun ab => f (e ab), ?_, fun c => ?_⟩
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp e (fun d => ‖f d‖ ^ 2)
  · change f (e _) = _
    refine congrArg (fun d => f d) (funext fun x => ?_)
    by_cases hx : x.1 ∈ T <;> simp [e, hx]


/-! ### Rank-one monomials on systems split at two parties -/

section RankOneMonomials

open ManyBody QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P] {X Z : ↥(Finset.univ : Finset P) → Type}
  {α β : Type} {pA pB : ↥(Finset.univ : Finset P)}

/-- The basis of a party of a system `X` read as that of `Z` with the factor `α` added at `pA`
and `β` at `pB`, from identifications `X pA ≃ α × Z pA`, `X pB ≃ β × Z pB` and the equality of
the bases elsewhere. -/
def twoPartySplit (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (s : ↥(Finset.univ : Finset P)) :
    X s ≃ addPair Z hAB α β s :=
  if hA : s = pA then hA ▸ eA.trans (addPairLeft hAB α β).symm
  else if hB : s = pB then hB ▸ eB.trans (addPairRight hAB α β).symm
  else (Equiv.cast (hZ s hA hB)).trans (Equiv.cast (addPair_of_ne hAB α β hA hB).symm)

theorem twoPartySplit_left (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (y : X pA) :
    twoPartySplit hAB eA eB hZ pA y = (addPairLeft hAB α β).symm (eA y) := by
  simp [twoPartySplit]

theorem twoPartySplit_right (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (y : X pB) :
    twoPartySplit hAB eA eB hZ pB y = (addPairRight hAB α β).symm (eB y) := by
  simp [twoPartySplit, hAB.symm]

theorem twoPartySplit_of_ne (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) {s : ↥(Finset.univ : Finset P)} (hA : s ≠ pA)
    (hB : s ≠ pB) (y : X s) :
    twoPartySplit hAB eA eB hZ s y =
      cast (addPair_of_ne hAB α β hA hB).symm (cast (hZ s hA hB) y) := by
  simp [twoPartySplit, hA, hB]

/-- The configurations of `X` read as pairs of a configuration of `α × β` and one of `Z`. -/
def twoPartyConfigEquiv (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) : Config X ≃ (α × β) × Config Z :=
  (Equiv.piCongrRight (twoPartySplit hAB eA eB hZ)).trans (addPairConfigEquiv hAB α β)

theorem twoPartyConfigEquiv_fst (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA)
    (eB : X pB ≃ β × Z pB) (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (x : Config X) :
    (twoPartyConfigEquiv hAB eA eB hZ x).1 = ((eA (x pA)).1, (eB (x pB)).1) := by
  simp [twoPartyConfigEquiv, twoPartySplit_left, twoPartySplit_right]

theorem twoPartyConfigEquiv_snd_left (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA)
    (eB : X pB ≃ β × Z pB) (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (x : Config X) :
    (twoPartyConfigEquiv hAB eA eB hZ x).2 pA = (eA (x pA)).2 := by
  simp [twoPartyConfigEquiv, twoPartySplit_left]

theorem twoPartyConfigEquiv_snd_right (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA)
    (eB : X pB ≃ β × Z pB) (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (x : Config X) :
    (twoPartyConfigEquiv hAB eA eB hZ x).2 pB = (eB (x pB)).2 := by
  simp [twoPartyConfigEquiv, twoPartySplit_right]

theorem twoPartyConfigEquiv_snd_of_ne (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA)
    (eB : X pB ≃ β × Z pB) (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (x : Config X)
    {s : ↥(Finset.univ : Finset P)} (hA : s ≠ pA) (hB : s ≠ pB) :
    (twoPartyConfigEquiv hAB eA eB hZ x).2 s = cast (hZ s hA hB) (x s) := by
  rw [twoPartyConfigEquiv, Equiv.trans_apply,
    addPairConfigEquiv_apply_snd_of_ne (hp := hA) (hq := hB),
    Equiv.piCongrRight_apply, Pi.map_apply, twoPartySplit_of_ne _ _ _ _ hA hB, cast_cast, cast_cast]

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]
  [∀ s, DecidableEq (Z s)] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **The pair bra.** The relabelling of `X` into `Z` with fresh factors at `pA ≠ pB`, followed
by the pair effect `⟨w|` on them. -/
def pairBra (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (w : EuclideanSpace ℂ (α × β)) :
    Monomial (Finset.univ : Finset P) X Z :=
  PartyCircuit.comp (PartyCircuit.relabel fun s ↦ (twoPartySplit hAB eA eB hZ s).symm)
    (PartyCircuit.gate {pA, pB} (PairEffectGate.ofAddPair hAB α β w Z).outside
      (.inr (PairEffectGate.ofAddPair hAB α β w Z)))

/-- **The pair ket.** The pair source `|v⟩` on fresh factors at `pA ≠ pB`, followed by the
relabelling of `Z` with these factors into `Y`. -/
def pairKet {Y : ↥(Finset.univ : Finset P) → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (hAB : pA ≠ pB) (eA : Y pA ≃ α × Z pA) (eB : Y pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → Y s = Z s) (v : EuclideanSpace ℂ (α × β)) :
    Monomial (Finset.univ : Finset P) Z Y :=
  PartyCircuit.comp (Word.sourceAt hAB α β v Z).toChain
    (PartyCircuit.relabel fun s ↦ twoPartySplit hAB eA eB hZ s)


section Ops

variable {Y : ↥(Finset.univ : Finset P) → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The operator of the pair bra is `⟨w| ⊗ 1` read through `twoPartyConfigEquiv`. -/
theorem op_pairBra (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (w : EuclideanSpace ℂ (α × β)) :
    (pairBra hAB eA eB hZ w).op chainEv =
      (effectMatrix w (Config Z)).submatrix id (twoPartyConfigEquiv hAB eA eB hZ) := by
  have hce : (PairEffectGate.ofAddPair hAB α β w Z).configEquiv = addPairConfigEquiv hAB α β :=
    SourceGate.configEquiv_ofAddPair hAB _ _ _ _
  rw [pairBra, PartyCircuit.op_comp (P := ↥(Finset.univ : Finset P)) (G := ChainGate),
    ChainGate.op_gate_inr, hce, PartyCircuit.op_relabel, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The operator of the pair ket is `|v⟩ ⊗ 1` read through `twoPartyConfigEquiv`. -/
theorem op_pairKet (hAB : pA ≠ pB) (eA : Y pA ≃ α × Z pA) (eB : Y pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → Y s = Z s) (v : EuclideanSpace ℂ (α × β)) :
    (pairKet hAB eA eB hZ v).op chainEv = prepMatrix (twoPartyConfigEquiv hAB eA eB hZ) v := by
  rw [pairKet, PartyCircuit.op_comp (P := ↥(Finset.univ : Finset P)) (G := ChainGate),
    PartyCircuit.op_relabel_mul, Word.op_toChain, Word.op_sourceAt]
  rfl

theorem isAllowed_pairBra (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) {w : EuclideanSpace ℂ (α × β)} (hw : ‖w‖ = 1) :
    (pairBra hAB eA eB hZ w).IsAllowed chainEv ChainGate.IsAllowed :=
  ⟨PartyCircuit.isAllowed_relabel _ _, (PairEffectGate.norm_ev_le _ ()).trans hw.le, hw⟩

theorem isAllowed_pairKet (hAB : pA ≠ pB) (eA : Y pA ≃ α × Z pA) (eB : Y pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → Y s = Z s) {v : EuclideanSpace ℂ (α × β)} (hv : ‖v‖ = 1) :
    (pairKet hAB eA eB hZ v).IsAllowed chainEv ChainGate.IsAllowed :=
  ⟨(Word.isAllowed_sourceAt hAB α β hv Z).toChain, PartyCircuit.isAllowed_relabel _ _⟩

omit [∀ s, Fintype (X s)] in
theorem usesOnly_pairBra (S : Finset P) (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA)
    (eB : X pB ≃ β × Z pB) (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s)
    (w : EuclideanSpace ℂ (α × β)) (hA : pA.1 ∈ S) (hB : pB.1 ∈ S) :
    Monomial.UsesOnly S (pairBra hAB eA eB hZ w) := by
  refine ⟨fun s hs ↦ ?_, fun v hv ↦ ?_⟩
  · have hsA : s ≠ pA := fun h ↦ hs (h ▸ hA)
    have hsB : s ≠ pB := fun h ↦ hs (h ▸ hB)
    refine ⟨(addPair_of_ne hAB α β hsA hsB).trans (hZ s hsA hsB).symm, fun y x ↦ ?_⟩
    have : (twoPartySplit hAB eA eB hZ s).symm y =
        cast ((addPair_of_ne hAB α β hsA hsB).trans (hZ s hsA hsB).symm) y := by
      apply (twoPartySplit hAB eA eB hZ s).injective
      rw [Equiv.apply_symm_apply, twoPartySplit_of_ne _ _ _ _ hsA hsB, cast_cast, cast_cast,
        cast_eq]
    simp [PEquiv.toMatrix_apply, this]
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    exacts [hA, hB]

theorem usesOnly_pairKet (S : Finset P) (hAB : pA ≠ pB) (eA : Y pA ≃ α × Z pA)
    (eB : Y pB ≃ β × Z pB) (hZ : ∀ s, s ≠ pA → s ≠ pB → Y s = Z s)
    (v : EuclideanSpace ℂ (α × β)) (hA : pA.1 ∈ S) (hB : pB.1 ∈ S) :
    Monomial.UsesOnly S (pairKet hAB eA eB hZ v) := by
  refine ⟨fun u hu ↦ ?_, fun s hs ↦ ?_⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    exacts [hA, hB]
  · have hsA : s ≠ pA := fun h ↦ hs (h ▸ hA)
    have hsB : s ≠ pB := fun h ↦ hs (h ▸ hB)
    refine ⟨(hZ s hsA hsB).trans (addPair_of_ne hAB α β hsA hsB).symm, fun y x ↦ ?_⟩
    simp [PEquiv.toMatrix_apply, twoPartySplit_of_ne _ _ _ _ hsA hsB, cast_cast]

omit [∀ s, Fintype (X s)] in
theorem sourceCount_pairBra (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (w : EuclideanSpace ℂ (α × β)) :
    (pairBra hAB eA eB hZ w).sourceCount = 0 :=
  rfl

omit [∀ s, Fintype (X s)] in
theorem effectCount_pairBra (hAB : pA ≠ pB) (eA : X pA ≃ α × Z pA) (eB : X pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → X s = Z s) (w : EuclideanSpace ℂ (α × β)) :
    (pairBra hAB eA eB hZ w).effectCount = 1 :=
  rfl

theorem sourceCount_pairKet (hAB : pA ≠ pB) (eA : Y pA ≃ α × Z pA) (eB : Y pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → Y s = Z s) (v : EuclideanSpace ℂ (α × β)) :
    (pairKet hAB eA eB hZ v).sourceCount = 1 :=
  rfl

theorem effectCount_pairKet (hAB : pA ≠ pB) (eA : Y pA ≃ α × Z pA) (eB : Y pB ≃ β × Z pB)
    (hZ : ∀ s, s ≠ pA → s ≠ pB → Y s = Z s) (v : EuclideanSpace ℂ (α × β)) :
    (pairKet hAB eA eB hZ v).effectCount = 0 :=
  rfl

/-- **The private bra** `⟨w|` on the factor `α × β` of the basis of one party. -/
def privateBra (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Z s = X s) (e : X p ≃ (α × β) × Z p)
    (w : EuclideanSpace ℂ (α × β)) : Monomial (Finset.univ : Finset P) X Z :=
  (Word.localDiscard p hZ w e).toChain

/-- **The private ket** `|v⟩` on a fresh factor `α × β` of the basis of one party. -/
def privateKet (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Y s = Z s) (e : Y p ≃ (α × β) × Z p)
    (v : EuclideanSpace ℂ (α × β)) : Monomial (Finset.univ : Finset P) Z Y :=
  (Word.localPrepare p hZ v e).toChain

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem op_privateBra (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Z s = X s)
    (e : X p ≃ (α × β) × Z p) (w : EuclideanSpace ℂ (α × β)) :
    (privateBra p hZ e w).op chainEv = (effectMatrix w (Config Z)).submatrix id
      (factorConfigEquiv p (fun s hs ↦ (hZ s hs).symm) e) := by
  rw [privateBra, Word.op_toChain, Word.op_localDiscard]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem op_privateKet (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Y s = Z s)
    (e : Y p ≃ (α × β) × Z p) (v : EuclideanSpace ℂ (α × β)) :
    (privateKet p hZ e v).op chainEv = prepMatrix (factorConfigEquiv p hZ e) v := by
  rw [privateKet, Word.op_toChain, Word.op_localPrepare_eq_prepMatrix]

omit [DecidableEq α] [DecidableEq β] in
theorem isAllowed_privateBra (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Z s = X s)
    (e : X p ≃ (α × β) × Z p) {w : EuclideanSpace ℂ (α × β)} (hw : ‖w‖ = 1) :
    (privateBra p hZ e w).IsAllowed chainEv ChainGate.IsAllowed :=
  (Word.isAllowed_localDiscard p hZ w e hw).toChain

omit [DecidableEq α] [DecidableEq β] in
theorem isAllowed_privateKet (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Y s = Z s)
    (e : Y p ≃ (α × β) × Z p) {v : EuclideanSpace ℂ (α × β)} (hv : ‖v‖ = 1) :
    (privateKet p hZ e v).IsAllowed chainEv ChainGate.IsAllowed :=
  (Word.isAllowed_localPrepare p hZ v e hv).toChain

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] in
theorem usesOnly_privateBra (S : Finset P) (p : ↥(Finset.univ : Finset P))
    (hZ : ∀ s ≠ p, Z s = X s) (e : X p ≃ (α × β) × Z p) (w : EuclideanSpace ℂ (α × β))
    (hp : p.1 ∈ S) : Monomial.UsesOnly S (privateBra p hZ e w) :=
  hp

omit [∀ s, Fintype (Z s)] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem usesOnly_privateKet (S : Finset P) (p : ↥(Finset.univ : Finset P))
    (hZ : ∀ s ≠ p, Y s = Z s) (e : Y p ≃ (α × β) × Z p) (v : EuclideanSpace ℂ (α × β))
    (hp : p.1 ∈ S) : Monomial.UsesOnly S (privateKet p hZ e v) :=
  hp

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] in
theorem sourceCount_privateBra (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Z s = X s)
    (e : X p ≃ (α × β) × Z p) (w : EuclideanSpace ℂ (α × β)) :
    (privateBra p hZ e w).sourceCount = 0 :=
  rfl

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] in
theorem effectCount_privateBra (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Z s = X s)
    (e : X p ≃ (α × β) × Z p) (w : EuclideanSpace ℂ (α × β)) :
    (privateBra p hZ e w).effectCount = 0 :=
  rfl

omit [∀ s, Fintype (Z s)] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem sourceCount_privateKet (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Y s = Z s)
    (e : Y p ≃ (α × β) × Z p) (v : EuclideanSpace ℂ (α × β)) :
    (privateKet p hZ e v).sourceCount = 0 :=
  rfl

omit [∀ s, Fintype (Z s)] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem effectCount_privateKet (p : ↥(Finset.univ : Finset P)) (hZ : ∀ s ≠ p, Y s = Z s)
    (e : Y p ≃ (α × β) × Z p) (v : EuclideanSpace ℂ (α × β)) :
    (privateKet p hZ e v).effectCount = 0 :=
  rfl

end Ops

end RankOneMonomials


/-! ### Rank-one blocks as monomials on the sheets -/

section SheetMonomials

open ManyBody QuantumCircuit.Party

variable {Party : Type} [Fintype Party] [DecidableEq Party]

variable (q) in
/-- The sheet of the owners `own`, on the parties of `Finset.univ`: at every party the
configurations of the sites it owns. -/
abbrev univSheet (own : ι → Party) : ↥(Finset.univ : Finset Party) → Type :=
  fun s ↦ Sheet.system q ⟨own⟩ s.1

/-- The configurations of a sheet in canonical site coordinates. -/
def univSheetEquiv (own : ι → Party) : Config (univSheet q own) ≃ (ι → Fin q) where
  toFun z x := z ⟨own x, Finset.mem_univ _⟩ ⟨x, (mem_blockPreimage_singleton _).mpr rfl⟩
  invFun c _ v := c v.1
  left_inv z := by
    funext ⟨s, hs⟩ ⟨v, hv⟩
    obtain rfl : own v = s := (mem_blockPreimage_singleton _).mp hv
    rfl
  right_inv _ := rfl

omit [DecidableEq ι] in
theorem univSheetEquiv_apply_of_eq {own : ι → Party} (z : Config (univSheet q own)) {x : ι}
    {s : ↥(Finset.univ : Finset Party)} (h : own x = s.1) :
    univSheetEquiv own z x = z s ⟨x, (mem_blockPreimage_singleton _).mpr h⟩ := by
  obtain ⟨s, hs⟩ := s
  obtain rfl : own x = s := h
  rfl

omit [DecidableEq ι] in
theorem univSheetEquiv_symm_apply (own : ι → Party) (c : ι → Fin q)
    (s : ↥(Finset.univ : Finset Party)) (v) : (univSheetEquiv own).symm c s v = c v.1 :=
  rfl

variable (q) in
/-- The sites outside a block, `E`, at the party `s` of the owners `oE`. -/
abbrev blockRest (E : Finset ι) (oE : ι → Party) : ↥(Finset.univ : Finset Party) → Type :=
  fun s ↦ {x // x ∈ E ∧ oE x = s.1} → Fin q

omit [Fintype ι] [DecidableEq ι] [Fintype Party] in
/-- Reading a function on a subtype along an equality of predicates. -/
theorem cast_subtype_fun_apply {a b : ι → Prop} (h : ({x // a x} → Fin q) = ({x // b x} → Fin q))
    (hab : ∀ x, a x ↔ b x) (f : {x // a x} → Fin q) (w : {x // b x}) :
    cast h f w = f ⟨w.1, (hab w.1).mpr w.2⟩ := by
  obtain rfl : a = b := funext fun x ↦ propext (hab x)
  rfl

omit [DecidableEq ι] in
theorem univSheet_eq_blockRest {E : Finset ι} {oE own : ι → Party}
    {s : ↥(Finset.univ : Finset Party)} (h : ∀ x, own x = s.1 ↔ x ∈ E ∧ oE x = s.1) :
    univSheet q own s = blockRest q E oE s :=
  congrArg (fun a : ι → Prop ↦ {x // a x} → Fin q)
    (funext fun x ↦ propext ((mem_blockPreimage_singleton _).trans (h x)))

/-- The configurations of the sites outside a block of a rank-one block, two parts of it. -/
def blockSplit (T E : Finset ι) (h : Disjoint T E) :
    ({x // x ∉ E} → Fin q) ≃ (T → Fin q) × ({v // v ∉ T ∪ E} → Fin q) where
  toFun c := (fun x ↦ c ⟨x, Finset.disjoint_left.mp h x.2⟩,
    fun x ↦ c ⟨x, fun hx ↦ x.2 (Finset.mem_union_right _ hx)⟩)
  invFun ab x := if hx : x.1 ∈ T then ab.1 ⟨x, hx⟩ else ab.2 ⟨x, by simp [hx, x.2]⟩
  left_inv c := funext fun x ↦ by by_cases hx : x.1 ∈ T <;> simp [hx]
  right_inv ab := by
    refine Prod.ext (funext fun x ↦ ?_) (funext fun x ↦ ?_)
    · simp [x.2]
    · have hx : x.1 ∉ T := fun h ↦ x.2 (Finset.mem_union_left _ h)
      simp [hx]

variable (b : RankOneBlock ι q)

/-- **The bra of a block as a monomial on a sheet.** If the part `T` of the block is owned by
`pA` and the part `U` by `pB`, the covector `⟨w|` on `T ∪ U` is a monomial from the sheet to
the sites outside the block, a pair effect when `pA ≠ pB` and a private bra otherwise, read
through configuration coordinates that are the restrictions to `T`, to `U` and to `E`. -/
theorem exists_sheetBra (S : Finset Party) (own : ι → Party) {pA pB : Party}
    (hA : ∀ x ∈ b.T, own x = pA) (hB : ∀ x ∈ (b.T ∪ b.E)ᶜ, own x = pB)
    {w : EuclideanSpace ℂ ((b.T → Fin q) × ({v // v ∉ b.T ∪ b.E} → Fin q))} (hw : ‖w‖ = 1)
    (hSA : pA ∈ S) (hSB : pB ∈ S) :
    ∃ (M : Monomial (Finset.univ : Finset Party) (univSheet q own) (blockRest q b.E own))
      (φ : Config (univSheet q own) ≃ ((b.T → Fin q) × ({v // v ∉ b.T ∪ b.E} → Fin q)) ×
        Config (blockRest q b.E own)),
      M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount = 0 ∧
      M.effectCount ≤ 1 ∧ (pA = pB → M.effectCount = 0) ∧
      M.op chainEv = (effectMatrix w (Config (blockRest q b.E own))).submatrix id φ ∧
      (∀ x, (φ x).1 = (fun t : b.T ↦ univSheetEquiv own x t,
        fun u : {v // v ∉ b.T ∪ b.E} ↦ univSheetEquiv own x u)) ∧
      ∀ x s u, (φ x).2 s u = univSheetEquiv own x u.1 := by
  classical
  have hU : ∀ x, x ∉ b.T → x ∉ b.E → own x = pB := fun x h₁ h₂ ↦
    hB x (by simp [h₁, h₂])
  set qA : ↥(Finset.univ : Finset Party) := ⟨pA, Finset.mem_univ _⟩
  set qB : ↥(Finset.univ : Finset Party) := ⟨pB, Finset.mem_univ _⟩
  have hZ : ∀ s : ↥(Finset.univ : Finset Party), s ≠ qA → s ≠ qB →
      univSheet q own s = blockRest q b.E own s := fun s hsA hsB ↦
    univSheet_eq_blockRest fun x ↦ ⟨fun h ↦ ⟨by
      by_contra hE
      by_cases hT : x ∈ b.T
      · exact hsA (Subtype.ext (h.symm.trans (hA x hT)))
      · exact hsB (Subtype.ext (h.symm.trans (hU x hT hE))), h⟩, fun h ↦ h.2⟩
  by_cases hAB : pA = pB
  · subst hAB
    have h : ∀ x, own x = pA ↔ x ∉ b.E ∨ (x ∈ b.E ∧ own x = pA) := fun x ↦
      ⟨fun h ↦ (em (x ∈ b.E)).symm.imp id (⟨·, h⟩), fun h ↦ h.elim (fun hE ↦ by
        by_cases hT : x ∈ b.T
        · exact hA x hT
        · exact hU x hT hE) And.right⟩
    let e : univSheet q own qA ≃ ((b.T → Fin q) × ({v // v ∉ b.T ∪ b.E} → Fin q)) ×
        blockRest q b.E own qA :=
      (Sheet.splitEquiv q ⟨own⟩ pA (· ∉ b.E) (fun x ↦ x ∈ b.E ∧ own x = pA) h
        fun _ h₁ h₂ ↦ h₁ h₂.1).trans ((blockSplit b.T b.E b.disj).prodCongr (Equiv.refl _))
    have hZ' : ∀ s ≠ qA, blockRest q b.E own s = univSheet q own s :=
      fun s hs ↦ (hZ s hs hs).symm
    refine ⟨privateBra qA hZ' e w, _, isAllowed_privateBra qA hZ' e hw,
      usesOnly_privateBra S qA hZ' e w hSA, rfl, Nat.zero_le _, fun _ ↦ rfl,
      op_privateBra qA hZ' e w, fun x ↦ ?_, fun x s u ↦ ?_⟩
    · rw [factorConfigEquiv_apply_fst]
      refine Prod.ext (funext fun t ↦ ?_) (funext fun t ↦ ?_)
      · exact (univSheetEquiv_apply_of_eq x (s := qA) (hA t t.2)).symm
      · exact (univSheetEquiv_apply_of_eq x (s := qA) (hU t (fun h ↦ t.2
          (Finset.mem_union_left _ h)) fun h ↦ t.2 (Finset.mem_union_right _ h))).symm
    · by_cases hs : s = qA
      · subst hs
        have := (factorConfigEquiv_apply_snd_eq_iff qA (fun s hs ↦ (hZ' s hs).symm) e x
          (factorConfigEquiv qA (fun s hs ↦ (hZ' s hs).symm) e x).2).mp rfl
        rw [← this.1]
        exact (univSheetEquiv_apply_of_eq x (s := qA) u.2.2).symm
      · have := (factorConfigEquiv_apply_snd_eq_iff qA (fun s hs ↦ (hZ' s hs).symm) e x
          (factorConfigEquiv qA (fun s hs ↦ (hZ' s hs).symm) e x).2).mp rfl
        rw [← this.2 s hs, cast_subtype_fun_apply _ (fun x ↦ (mem_blockPreimage_singleton _).trans
          ⟨fun h' ↦ ⟨by
            by_contra hE
            by_cases hT : x ∈ b.T
            · exact hs (Subtype.ext (h'.symm.trans (hA x hT)))
            · exact hs (Subtype.ext (h'.symm.trans (hU x hT hE))), h'⟩, fun h' ↦ h'.2⟩)]
        exact (univSheetEquiv_apply_of_eq x u.2.2).symm
  · have hqAB : qA ≠ qB := fun h ↦ hAB (congrArg Subtype.val h)
    have hAh : ∀ x, own x = pA ↔ x ∈ b.T ∨ (x ∈ b.E ∧ own x = pA) := fun x ↦
      ⟨fun h ↦ by
        by_cases hT : x ∈ b.T
        · exact Or.inl hT
        · by_cases hE : x ∈ b.E
          · exact Or.inr ⟨hE, h⟩
          · exact absurd (h.symm.trans (hU x hT hE)) hAB, fun h ↦ h.elim (hA x) And.right⟩
    have hBh : ∀ x, own x = pB ↔ x ∉ b.T ∪ b.E ∨ (x ∈ b.E ∧ own x = pB) := fun x ↦
      ⟨fun h ↦ by
        by_cases hT : x ∈ b.T
        · exact absurd ((hA x hT).symm.trans h) hAB
        · by_cases hE : x ∈ b.E
          · exact Or.inr ⟨hE, h⟩
          · exact Or.inl (by simp [hT, hE]), fun h ↦ h.elim (hB x ∘ Finset.mem_compl.mpr)
            And.right⟩
    let eA : univSheet q own qA ≃ (b.T → Fin q) × blockRest q b.E own qA :=
      Sheet.splitEquiv q ⟨own⟩ pA (· ∈ b.T) (fun x ↦ x ∈ b.E ∧ own x = pA) hAh
        fun _ h₁ h₂ ↦ Finset.disjoint_left.mp b.disj h₁ h₂.1
    let eB : univSheet q own qB ≃ ({v // v ∉ b.T ∪ b.E} → Fin q) × blockRest q b.E own qB :=
      Sheet.splitEquiv q ⟨own⟩ pB (· ∉ b.T ∪ b.E) (fun x ↦ x ∈ b.E ∧ own x = pB) hBh
        fun _ h₁ h₂ ↦ h₁ (Finset.mem_union_right _ h₂.1)
    refine ⟨pairBra hqAB eA eB hZ w, twoPartyConfigEquiv hqAB eA eB hZ,
      isAllowed_pairBra hqAB eA eB hZ hw, usesOnly_pairBra S hqAB eA eB hZ w hSA hSB,
      sourceCount_pairBra hqAB eA eB hZ w, (effectCount_pairBra hqAB eA eB hZ w).le,
      fun h ↦ absurd h hAB, op_pairBra hqAB eA eB hZ w, fun x ↦ ?_, fun x s u ↦ ?_⟩
    · rw [twoPartyConfigEquiv_fst]
      refine Prod.ext (funext fun t ↦ ?_) (funext fun t ↦ ?_)
      · exact (univSheetEquiv_apply_of_eq x (s := qA) (hA t t.2)).symm
      · exact (univSheetEquiv_apply_of_eq x (s := qB) (hB t (Finset.mem_compl.mpr t.2))).symm
    · by_cases hsA : s = qA
      · subst hsA
        rw [twoPartyConfigEquiv_snd_left]
        exact (univSheetEquiv_apply_of_eq x u.2.2).symm
      by_cases hsB : s = qB
      · subst hsB
        rw [twoPartyConfigEquiv_snd_right]
        exact (univSheetEquiv_apply_of_eq x u.2.2).symm
      rw [twoPartyConfigEquiv_snd_of_ne _ _ _ _ _ hsA hsB, cast_subtype_fun_apply _
        (fun x ↦ (mem_blockPreimage_singleton _).trans ⟨fun h ↦ ⟨by
          by_contra hE
          by_cases hT : x ∈ b.T
          · exact hsA (Subtype.ext (h.symm.trans (hA x hT)))
          · exact hsB (Subtype.ext (h.symm.trans (hU x hT hE))), h⟩, fun h ↦ h.2⟩)]
      exact (univSheetEquiv_apply_of_eq x u.2.2).symm


/-- **The ket of a block as a monomial on a sheet.** If the part `T` of the block is owned by
`pA'` and the part `U` by `pB'` under the owners `own'`, which agree with `own` on `E`, the
vector `|v⟩` on `T ∪ U` is a monomial from the sites outside the block to the sheet of `own'`, a
pair source when `pA' ≠ pB'` and a private preparation otherwise, read through the restrictions
to `T`, to `U` and to `E`. -/
theorem exists_sheetKet (S : Finset Party) (own own' : ι → Party) {pA pB : Party}
    (hA : ∀ x ∈ b.T, own' x = pA) (hB : ∀ x ∈ (b.T ∪ b.E)ᶜ, own' x = pB)
    (hE : ∀ x ∈ b.E, own' x = own x)
    {v : EuclideanSpace ℂ ((b.T → Fin q) × ({v // v ∉ b.T ∪ b.E} → Fin q))} (hv : ‖v‖ = 1)
    (hSA : pA ∈ S) (hSB : pB ∈ S) :
    ∃ (M : Monomial (Finset.univ : Finset Party) (blockRest q b.E own) (univSheet q own'))
      (ψ : Config (univSheet q own') ≃ ((b.T → Fin q) × ({v // v ∉ b.T ∪ b.E} → Fin q)) ×
        Config (blockRest q b.E own)),
      M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly S ∧ M.effectCount = 0 ∧
      M.sourceCount ≤ 1 ∧ (pA = pB → M.sourceCount = 0) ∧
      M.op chainEv = prepMatrix ψ v ∧
      (∀ y, (ψ y).1 = (fun t : b.T ↦ univSheetEquiv own' y t,
        fun u : {v // v ∉ b.T ∪ b.E} ↦ univSheetEquiv own' y u)) ∧
      ∀ y s u, (ψ y).2 s u = univSheetEquiv own' y u.1 := by
  classical
  have hU : ∀ x, x ∉ b.T → x ∉ b.E → own' x = pB := fun x h₁ h₂ ↦
    hB x (by simp [h₁, h₂])
  set qA : ↥(Finset.univ : Finset Party) := ⟨pA, Finset.mem_univ _⟩
  set qB : ↥(Finset.univ : Finset Party) := ⟨pB, Finset.mem_univ _⟩
  have hiff : ∀ s : ↥(Finset.univ : Finset Party), s ≠ qA → s ≠ qB →
      ∀ x, own' x = s.1 ↔ x ∈ b.E ∧ own x = s.1 := fun s hsA hsB x ↦
    ⟨fun h ↦ by
      by_cases hE' : x ∈ b.E
      · exact ⟨hE', (hE x hE').symm.trans h⟩
      by_cases hT : x ∈ b.T
      · exact absurd (Subtype.ext (h.symm.trans (hA x hT))) hsA
      · exact absurd (Subtype.ext (h.symm.trans (hU x hT hE'))) hsB,
      fun h ↦ (hE x h.1).trans h.2⟩
  have hZ : ∀ s : ↥(Finset.univ : Finset Party), s ≠ qA → s ≠ qB →
      univSheet q own' s = blockRest q b.E own s := fun s hsA hsB ↦
    univSheet_eq_blockRest (hiff s hsA hsB)
  have hu : ∀ (s : ↥(Finset.univ : Finset Party)) (u : {x // x ∈ b.E ∧ own x = s.1}),
      own' u.1 = s.1 := fun s u ↦ (hE u.1 u.2.1).trans u.2.2
  by_cases hAB : pA = pB
  · subst hAB
    have h : ∀ x, own' x = pA ↔ x ∉ b.E ∨ (x ∈ b.E ∧ own x = pA) := fun x ↦
      ⟨fun h ↦ (em (x ∈ b.E)).symm.imp id fun hE' ↦ ⟨hE', (hE x hE').symm.trans h⟩,
        fun h ↦ h.elim (fun hE' ↦ by
          by_cases hT : x ∈ b.T
          · exact hA x hT
          · exact hU x hT hE') fun h ↦ (hE x h.1).trans h.2⟩
    let e : univSheet q own' qA ≃ ((b.T → Fin q) × ({v // v ∉ b.T ∪ b.E} → Fin q)) ×
        blockRest q b.E own qA :=
      (Sheet.splitEquiv q ⟨own'⟩ pA (· ∉ b.E) (fun x ↦ x ∈ b.E ∧ own x = pA) h
        fun _ h₁ h₂ ↦ h₁ h₂.1).trans ((blockSplit b.T b.E b.disj).prodCongr (Equiv.refl _))
    have hZ' : ∀ s ≠ qA, univSheet q own' s = blockRest q b.E own s :=
      fun s hs ↦ hZ s hs hs
    refine ⟨privateKet qA hZ' e v, _, isAllowed_privateKet qA hZ' e hv,
      usesOnly_privateKet S qA hZ' e v hSA, rfl, Nat.zero_le _, fun _ ↦ rfl,
      op_privateKet qA hZ' e v, fun y ↦ ?_, fun y s u ↦ ?_⟩
    · rw [factorConfigEquiv_apply_fst]
      refine Prod.ext (funext fun t ↦ ?_) (funext fun t ↦ ?_)
      · exact (univSheetEquiv_apply_of_eq y (s := qA) (hA t t.2)).symm
      · exact (univSheetEquiv_apply_of_eq y (s := qA) (hU t (fun h ↦ t.2
          (Finset.mem_union_left _ h)) fun h ↦ t.2 (Finset.mem_union_right _ h))).symm
    · have := (factorConfigEquiv_apply_snd_eq_iff qA hZ' e y
        (factorConfigEquiv qA hZ' e y).2).mp rfl
      by_cases hs : s = qA
      · subst hs
        rw [← this.1]
        exact (univSheetEquiv_apply_of_eq y (s := qA) (hu _ u)).symm
      · rw [← this.2 s hs, cast_subtype_fun_apply _ fun x ↦
          (mem_blockPreimage_singleton _).trans (hiff s hs hs x)]
        exact (univSheetEquiv_apply_of_eq y (hu s u)).symm
  · have hqAB : qA ≠ qB := fun h ↦ hAB (congrArg Subtype.val h)
    have hAh : ∀ x, own' x = pA ↔ x ∈ b.T ∨ (x ∈ b.E ∧ own x = pA) := fun x ↦
      ⟨fun h ↦ by
        by_cases hT : x ∈ b.T
        · exact Or.inl hT
        · by_cases hE' : x ∈ b.E
          · exact Or.inr ⟨hE', (hE x hE').symm.trans h⟩
          · exact absurd (h.symm.trans (hU x hT hE')) hAB,
        fun h ↦ h.elim (hA x) fun h ↦ (hE x h.1).trans h.2⟩
    have hBh : ∀ x, own' x = pB ↔ x ∉ b.T ∪ b.E ∨ (x ∈ b.E ∧ own x = pB) := fun x ↦
      ⟨fun h ↦ by
        by_cases hT : x ∈ b.T
        · exact absurd ((hA x hT).symm.trans h) hAB
        · by_cases hE' : x ∈ b.E
          · exact Or.inr ⟨hE', (hE x hE').symm.trans h⟩
          · exact Or.inl (by simp [hT, hE']),
        fun h ↦ h.elim (hB x ∘ Finset.mem_compl.mpr) fun h ↦ (hE x h.1).trans h.2⟩
    let eA : univSheet q own' qA ≃ (b.T → Fin q) × blockRest q b.E own qA :=
      Sheet.splitEquiv q ⟨own'⟩ pA (· ∈ b.T) (fun x ↦ x ∈ b.E ∧ own x = pA) hAh
        fun _ h₁ h₂ ↦ Finset.disjoint_left.mp b.disj h₁ h₂.1
    let eB : univSheet q own' qB ≃ ({v // v ∉ b.T ∪ b.E} → Fin q) × blockRest q b.E own qB :=
      Sheet.splitEquiv q ⟨own'⟩ pB (· ∉ b.T ∪ b.E) (fun x ↦ x ∈ b.E ∧ own x = pB) hBh
        fun _ h₁ h₂ ↦ h₁ (Finset.mem_union_right _ h₂.1)
    refine ⟨pairKet hqAB eA eB hZ v, twoPartyConfigEquiv hqAB eA eB hZ,
      isAllowed_pairKet hqAB eA eB hZ hv, usesOnly_pairKet S hqAB eA eB hZ v hSA hSB,
      effectCount_pairKet hqAB eA eB hZ v, (sourceCount_pairKet hqAB eA eB hZ v).le,
      fun h ↦ absurd h hAB, op_pairKet hqAB eA eB hZ v, fun y ↦ ?_, fun y s u ↦ ?_⟩
    · rw [twoPartyConfigEquiv_fst]
      refine Prod.ext (funext fun t ↦ ?_) (funext fun t ↦ ?_)
      · exact (univSheetEquiv_apply_of_eq y (s := qA) (hA t t.2)).symm
      · exact (univSheetEquiv_apply_of_eq y (s := qB) (hB t (Finset.mem_compl.mpr t.2))).symm
    · by_cases hsA : s = qA
      · subst hsA
        rw [twoPartyConfigEquiv_snd_left]
        exact (univSheetEquiv_apply_of_eq y (hu _ u)).symm
      by_cases hsB : s = qB
      · subst hsB
        rw [twoPartyConfigEquiv_snd_right]
        exact (univSheetEquiv_apply_of_eq y (hu _ u)).symm
      rw [twoPartyConfigEquiv_snd_of_ne _ _ _ _ _ hsA hsB, cast_subtype_fun_apply _
        fun x ↦ (mem_blockPreimage_singleton _).trans (hiff s hsA hsB x)]
      exact (univSheetEquiv_apply_of_eq y (hu s u)).symm

/-- **A rank-one block as an allowed monomial on the sheets.** Let the sites of `T` be owned by
`p_A` before and by `p_A'` after, those of `U = (T ∪ E)ᶜ` by `p_B` and `p_B'`, and the sites of
`E` by the same party before and after. For unit vectors `v` and `w`, the operator
`|v⟩⟨w|_{T ∪ U} ⊗ 1_E` is, in canonical site coordinates, the operator of an allowed monomial
from the sheet of `own` to that of `own'` that uses only `p_A`, `p_B`, `p_A'` and `p_B'`, with at
most one normalized pair source, none when `p_A' = p_B'`, and at most one normalized pair effect,
none when `p_A = p_B`.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 306–316: each group
vector on at most two owners is a normalized pair state or effect, or a private map. -/
theorem exists_rankOneBlock_monomial (S : Finset Party) (own own' : ι → Party)
    {pA pB pA' pB' : Party} (hA : ∀ x ∈ b.T, own x = pA) (hB : ∀ x ∈ (b.T ∪ b.E)ᶜ, own x = pB)
    (hA' : ∀ x ∈ b.T, own' x = pA') (hB' : ∀ x ∈ (b.T ∪ b.E)ᶜ, own' x = pB')
    (hE : ∀ x ∈ b.E, own x = own' x) (hv : ‖b.ket‖ = 1) (hw : ‖b.bra‖ = 1) (hSA : pA ∈ S)
    (hSB : pB ∈ S) (hSA' : pA' ∈ S) (hSB' : pB' ∈ S) :
    ∃ M : Monomial (Finset.univ : Finset Party) (univSheet q own) (univSheet q own'),
      M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly S ∧
      M.sourceCount ≤ 1 ∧ (pA' = pB' → M.sourceCount = 0) ∧
      M.effectCount ≤ 1 ∧ (pA = pB → M.effectCount = 0) ∧
      M.op chainEv = reindex (univSheetEquiv own').symm (univSheetEquiv own).symm b.op := by
  obtain ⟨M₁, φ, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := exists_sheetBra b S own hA hB hw hSA hSB
  obtain ⟨M₂, ψ, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈⟩ :=
    exists_sheetKet b S own own' hA' hB' (fun x hx ↦ (hE x hx).symm) hv hSA' hSB'
  refine ⟨M₁.comp M₂, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩, ?_, fun h ↦ ?_, ?_, fun h ↦ ?_, ?_⟩
  · rw [Monomial.sourceCount_comp, a₃, zero_add]
    exact b₄
  · rw [Monomial.sourceCount_comp, a₃, b₅ h]
  · rw [Monomial.effectCount_comp, b₃, add_zero]
    exact a₄
  · rw [Monomial.effectCount_comp, b₃, a₅ h]
  · rw [PartyCircuit.op_comp (P := ↥(Finset.univ : Finset Party)) (G := ChainGate), a₆, b₆]
    ext y x
    rw [prepMatrix_mul_apply, submatrix_apply, effectMatrix_apply, id, reindex_apply,
      submatrix_apply, Equiv.symm_symm, Equiv.symm_symm, RankOneBlock.op_apply, b₇, a₇]
    have hiff : (ψ y).2 = (φ x).2 ↔
        ∀ e ∈ b.E, univSheetEquiv own' y e = univSheetEquiv own x e := by
      refine ⟨fun h e he ↦ ?_, fun h ↦ funext fun s ↦ funext fun u ↦ ?_⟩
      · have := congrFun (congrFun h ⟨own e, Finset.mem_univ _⟩) ⟨e, he, rfl⟩
        rwa [b₈, a₈] at this
      · rw [b₈, a₈]
        exact h u.1 u.2.1
    by_cases h : ∀ e ∈ b.E, univSheetEquiv own' y e = univSheetEquiv own x e
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      rfl
    · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h, mul_zero]

end SheetMonomials

end TNLean.PEPS.EncodedFrame
