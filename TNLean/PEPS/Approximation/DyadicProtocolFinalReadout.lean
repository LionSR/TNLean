/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicFrozenHoleCount
import TNLean.PEPS.Approximation.DyadicProtocolOwners
import TNLean.PEPS.Approximation.GuideFramePatchData
import TNLean.PEPS.Approximation.SheetStackReadout

/-!
# The final reference vector of the dyadic protocol

At the end of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the main guide
is the guide of the unit squares: every site, a cell center `(i + 1/2, j + 1/2)`, reads the label
of its own unit square, held by the unit-square party of that square. The holes of the main frame
sit at grid corners with outer radius below `1/2`, so their encodings are trivial; the other
reference factors, the frozen auxiliary frames and the idle registers, form `Ξ`
(`06-geometry.tex`, lines 669–681). This file instantiates the final regrouping
`EncodedFrame.exists_readoutCircuit_norm` on these parties.

* `DyadicProtocol.exists_reference_changes_of_readoutCircuit`: for any protocol whose
  unit-square parties are the raw owners of a main frame `M` with trivial holes, whose final
  physical order and private registers are those of the final regrouping of the stack `M :: Fs`,
  and whose final reference vector is the regrouped reference vector of that stack, the readout
  of the final reference vector is `Ω ⊗ Ξ` with `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`, given the frame
  constraints of the other sheets at accuracy `L⁻⁶⁰` and at most `C L³` holes on them.
* `unitLevelFrame`: the encoded frame of the guide at the end of the last level `n = 1`, with
  holes at a finite set of grid corners. Its raw owner at a site is the unit-square party of the
  site (`unitLevelFrame_owner`), so distinct sites have distinct owners.
* `DyadicProtocol.exists_reference_changes_unitLevel`: the final reference vector of item 4 of
  Proposition 7.1 with the constant `214`, for the main frame `unitLevelFrame` and the frozen
  auxiliary frames of the schedule, one for each change that initializes an auxiliary sheet, with
  their holes counted by `sum_frozenHoles_le_cube` and their patches supplied by Proposition 4.1 at
  accuracy `L⁻⁶⁰`.

The trajectory of the protocol is not fixed here: the frozen auxiliary frames, the idle registers
and the final reference vector are arbitrary data satisfying the stated identities.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 4,
  `06-geometry.tex`, lines 39–51, and its proof: the sites at cell centers and the hierarchy
  (lines 62–67), the guides of a level (lines 82–100), the frozen auxiliary holes (lines 653–656)
  and the final reference (lines 669–681).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame TNLean.Lattice.Sheet TNLean.Lattice.PartyCircuit

/-! ### The final reference vector of a protocol -/

namespace DyadicProtocol

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- If the unit-square parties of a protocol are given by `own`, the physical output of the party
`own v` has dimension `q`. -/
theorem physicalDimension_eq_of_site_eq {own : SquareLatticeVertex L L → P}
    (hsite : ∀ v, D.site v = own v) (v : SquareLatticeVertex L L) :
    D.physicalDimension (own v) = q := by
  rw [← hsite]
  exact D.physicalDimension_site v

/-- If the unit-square parties of a protocol are given by `own`, every party outside the range
of `own` has a physical output of dimension one. -/
theorem physicalDimension_eq_one_of_site_eq {own : SquareLatticeVertex L L → P}
    (hsite : ∀ v, D.site v = own v) (p : P) (hp : p ∉ Set.range own) :
    D.physicalDimension p = 1 :=
  D.physicalDimension_eq_one p fun ⟨v, hv⟩ => hp ⟨v, (hsite v).symm.trans hv⟩

/-- Transport of a physical-private readout along equalities of the physical order and of the
private registers. -/
private theorem exists_readout_eq_of_eq [DecidableEq P] {d : P → ℕ} {o o' : List P}
    {pr pr' : Layout P} (ho : o = o') (hp : pr = pr') (hn : o.Nodup) (hm : ∀ p, p ∈ o)
    (hn' : o'.Nodup) (hm' : ∀ p, p ∈ o') [FiniteDimensional ℂ (Mem pr).carrier]
    [FiniteDimensional ℂ (Mem pr').carrier] {x : Mem (familyPhysicalOutputLayout d o pr)}
    {y : Mem (familyPhysicalOutputLayout d o' pr')}
    (hx : x = Layout.memCongr (congrArg₂ (familyPhysicalOutputLayout d) ho hp).symm y)
    {Ω' : EuclideanSpace ℂ ((p : P) → Fin (d p))}
    (Ξ' : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem pr').carrier)))
    (h : familyLabelledPhysicalReadout d o' hn' hm' pr' y =
      Matrix.euclideanTensorVector Ω' Ξ') :
    ∃ Ξ : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem pr).carrier)), ‖Ξ‖ = ‖Ξ'‖ ∧
      familyLabelledPhysicalReadout d o hn hm pr x = Matrix.euclideanTensorVector Ω' Ξ := by
  subst ho hp hx
  exact ⟨Ξ', rfl, h⟩

/-- **The final reference vector of a protocol.** Let the unit-square parties of a protocol be
the raw owners of a main frame `M` with trivial holes, let its final layout be the output layout
of the final regrouping of the stack `M :: Fs` followed by the idle layout `ℓ`, and let its final
reference vector be the regrouped reference vector of that stack with an idle vector of norm
one. If `‖Ω‖ = 1`, every hole of the other sheets satisfies the frame constraint at accuracy
`L⁻⁶⁰`, and the other sheets carry at most `C L³` holes in total, then the readout of the final
reference vector is `Ω ⊗ Ξ` with `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–51, and its proof, lines 653–656 and 669–681. -/
theorem exists_reference_changes_of_readoutCircuit [DecidableEq P] [NeZero q]
    {pos : SquareLatticeVertex L L → ℝ × ℝ} (M : Frame pos q P) (Fs : List (Frame pos q P))
    (ℓ : Layout P) (hown : Function.Injective M.owner) (hM : ∀ h ∈ M.holes, h.patch.outer = ∅)
    (hsite : ∀ v, D.site v = M.owner v) (horder : D.physicalOrder = siteOrder M.owner)
    (hpriv : D.privateOutput = readoutPrivate M Fs ℓ) {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1)
    (hL : 0 < L) {C : ℝ}
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F => (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3) {ξ : Mem ℓ}
    (hξ : ‖ξ‖ = 1)
    (href : Layout.memCongr D.layout_changes (D.reference D.changes) =
      Layout.memCongr (congrArg₂ (familyPhysicalOutputLayout D.physicalDimension) horder
          hpriv).symm
        ((readoutCircuit D.physicalDimension M Fs ℓ (D.physicalDimension_eq_of_site_eq hsite)
          (D.physicalDimension_eq_one_of_site_eq hsite)).eval (stackVec Ω (M :: Fs) ξ))) :
    ∃ Ξ : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem D.privateOutput))),
      ‖Ξ‖ ≤ 1 ∧ 1 - C / (L : ℝ) ^ 57 ≤ ‖Ξ‖ ∧
        D.readout (D.reference D.changes) = Matrix.euclideanTensorVector Ω Ξ := by
  have he : ∀ σ v, (D.physicalConfigEquiv σ v : ℕ) = σ (M.owner v) := fun σ v => by
    rw [D.physicalConfigEquiv_apply_val, hsite]
  have hfin := Layout.finiteDimensional_mem_of_registers _ D.finite_privateOutput
  have : FiniteDimensional ℂ (Mem (readoutPrivate M Fs ℓ)).carrier := hpriv ▸ hfin
  obtain ⟨Ξ', h1, h2, h3⟩ := exists_readoutCircuit_norm D.physicalDimension M Fs ℓ hown _ _ hM _ he
    hΩ hL hε hholes hξ
  obtain ⟨Ξ, hΞ, h⟩ := exists_readout_eq_of_eq horder hpriv D.physicalOrder_nodup
    D.mem_physicalOrder (nodup_siteOrder hown) (mem_siteOrder M.owner) href Ξ' h3
  exact ⟨Ξ, hΞ ▸ h1, hΞ ▸ h2, readout_eq_euclideanTensorVector D _ Ω Ξ h⟩

end DyadicProtocol

/-! ### The main frame at the last level -/

variable {L k q : ℕ}

/-- The unit square of the hierarchy of `[0, 2 ^ k] ^ 2` at the address of a site, when
`L ≤ 2 ^ k`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 62–67 and 643–645. -/
def unitSquare (hk : L ≤ 2 ^ k) (v : SquareLatticeVertex L L) : DyadicSquare k :=
  ⟨0, ⟨v.1, lt_of_lt_of_le v.1.isLt (by simpa using hk)⟩,
    ⟨v.2, lt_of_lt_of_le v.2.isLt (by simpa using hk)⟩⟩

theorem toTriple_unitSquare (hk : L ≤ 2 ^ k) (v : SquareLatticeVertex L L) :
    (unitSquare hk v).toTriple = (0, (v.1 : ℕ), (v.2 : ℕ)) :=
  rfl

/-- Distinct sites have distinct unit squares. -/
theorem unitSquare_injective (hk : L ≤ 2 ^ k) : Function.Injective (unitSquare hk) := by
  intro v w h
  have h' := congrArg DyadicSquare.toTriple h
  simp only [toTriple_unitSquare, Prod.mk.injEq, true_and] at h'
  exact Prod.ext (Fin.ext h'.1) (Fin.ext h'.2)

/-- The sites of the square lie at cell centers. -/
theorem isCellCenter_cellCenterPos (v : SquareLatticeVertex L L) :
    IsCellCenter (cellCenterPos L v) :=
  ⟨(v.1 : ℕ), (v.2 : ℕ), by simp [cellCenterPos]⟩

/-- The unit block of a site at its cell center. -/
theorem blockIndex_one_cellCenterPos (v : SquareLatticeVertex L L) :
    blockIndex 1 (cellCenterPos L v) = (((v.1 : ℕ) : ℤ), ((v.2 : ℕ) : ℤ)) := by
  have h (n : ℕ) : ⌊((n : ℝ) + 1 / 2) / 1⌋ = (n : ℤ) := by
    rw [div_one, Int.floor_natCast_add, add_eq_left, Int.floor_eq_zero_iff]
    norm_num
  simp only [blockIndex, cellCenterPos, h]

/-- **The main frame at the last level.** The encoded frame of the guide at the end of the level
`n = 1`, when every unit block of the root square carries its own label, read through the label
map `labelParty S` of a repainted square `S`, with holes at the centers of the finite set `V`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100, 109–125 and 669–672. -/
abbrev unitLevelFrame (k : ℕ) (done : Set (ℤ × ℤ)) (S : RepaintedSquare k)
    (rank : GuideLabel → ℕ) (V : Finset (ℝ × ℝ))
    (patch : ℝ × ℝ → SquarePatch (cellCenterPos L) q)
    (hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer) :
    Frame (cellCenterPos L) q (ProtocolParty k) :=
  guideFrame (cellCenterPos L) q (blockGuide 1 (protocolLevelLabels k 0 done)) (labelParty S)
    guidePlaceholder rank V patch hV

variable {done : Set (ℤ × ℤ)} {S : RepaintedSquare k} {rank : GuideLabel → ℕ}
  {V : Finset (ℝ × ℝ)} {patch : ℝ × ℝ → SquarePatch (cellCenterPos L) q}
  {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer}

/-- **Raw owners at the last level.** Once every unit block of the root square is repainted, the
raw owner of a site in the main frame is the unit-square party of the site.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 48–51 and 669–673. -/
theorem unitLevelFrame_owner (hk : L ≤ 2 ^ k) (hdone : {Q | InRoot ((2 : ℤ) ^ k) Q} ⊆ done)
    (v : SquareLatticeVertex L L) :
    (unitLevelFrame k done S rank V patch hV).owner v = .inl (unitSquare hk v) := by
  classical
  have hroot : InRoot ((2 : ℤ) ^ (k - 0)) (((v.1 : ℕ) : ℤ), ((v.2 : ℕ) : ℤ)) := by
    have h1 : ((v.1 : ℕ) : ℤ) < 2 ^ k := by exact_mod_cast lt_of_lt_of_le v.1.isLt hk
    have h2 : ((v.2 : ℕ) : ℤ) < 2 ^ k := by exact_mod_cast lt_of_lt_of_le v.2.isLt hk
    simp only [Nat.sub_zero]
    exact ⟨by positivity, h1, by positivity, h2⟩
  have hmem : (((v.1 : ℕ) : ℤ), ((v.2 : ℕ) : ℤ)) ∈ done := hdone (by simpa using hroot)
  simp only [guideFrame_owner, blockGuide, blockIndex_one_cellCenterPos, protocolLevelLabels,
    levelLabels, hroot, hmem, ite_true, newParty, Int.toNat_natCast]
  rw [← toTriple_unitSquare hk v, labelParty_toTriple]

/-- Distinct sites have distinct raw owners in the main frame at the last level. -/
theorem unitLevelFrame_owner_injective (hk : L ≤ 2 ^ k)
    (hdone : {Q | InRoot ((2 : ℤ) ^ k) Q} ⊆ done) :
    Function.Injective (unitLevelFrame k done S rank V patch hV).owner := by
  intro v w h
  rw [unitLevelFrame_owner hk hdone, unitLevelFrame_owner hk hdone] at h
  exact unitSquare_injective hk (Sum.inl_injective h)

/-- **The final reference vector of the dyadic protocol.** Let `L ≤ 2 ^ k < 2 L`, and let a
protocol on the parties of the hierarchy of `[0, 2 ^ k] ^ 2` end as follows. The main frame is the
frame at the end of the last level, with holes at grid corners whose patches have outer radius
below `1/2`. The other sheets are frozen auxiliary frames, one for each change of the schedule
that initializes an auxiliary sheet, each with at most as many holes as its final guide has true
vertices and with patches supplied by Proposition 4.1 at accuracy `L⁻⁶⁰`, followed by idle
registers with a vector of norm one. The unit-square party of a site is the party of its unit
square, and the final layout and reference vector are those of the final regrouping. Then, for
`‖Ω‖ = 1`, the readout of the final reference vector is `Ω ⊗ Ξ` with
`1 - 214 L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–51, and its proof, lines 653–656 and 669–681. -/
theorem DyadicProtocol.exists_reference_changes_unitLevel [NeZero q]
    (D : DyadicProtocol L q (ProtocolParty k)) (hk : L ≤ 2 ^ k) (hk' : 2 ^ k < 2 * L)
    (hdone : {Q | InRoot ((2 : ℤ) ^ k) Q} ⊆ done) (hc : ∀ z ∈ V, (patch z).center = z)
    (hcorner : ∀ z ∈ V, ∃ Q, z = blockCorner 1 Q) (hs : ∀ z ∈ V, 2 * (patch z).scale < 1 / 2)
    {κ : Type*} (large : DyadicSquare k → Bool)
    (Fr : ProtocolEvent k × RepaintOp → RepaintingBaseline κ × (ℝ × ℝ) × SquareEdge)
    (aux : ProtocolEvent k × RepaintOp → Frame (cellCenterPos L) q (ProtocolParty k))
    (haux : ∀ x ∈ (protocolSchedule k large).filter fun x => x.2.IsAuxInit,
      (aux x).holes.length ≤
        {c | IsTrueVertex (frozenAuxGuide (Fr x).1 (Fr x).2.1 (Fr x).2.2) c}.ncard)
    {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1) {B₀ C c : ℝ}
    (supply : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L)
    (hsupply : ∀ x ∈ (protocolSchedule k large).filter fun x => x.2.IsAuxInit,
      ∀ h ∈ (aux x).holes, IsSuppliedPatch supply h.patch)
    (ℓ : Layout (ProtocolParty k)) {ξ : Mem ℓ} (hξ : ‖ξ‖ = 1)
    (hsite : ∀ v, D.site v = .inl (unitSquare hk v))
    (horder : D.physicalOrder = siteOrder (unitLevelFrame k done S rank V patch hV).owner)
    (hpriv : D.privateOutput = readoutPrivate (unitLevelFrame k done S rank V patch hV)
      (((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map aux) ℓ)
    (href : Layout.memCongr D.layout_changes (D.reference D.changes) =
      Layout.memCongr (congrArg₂ (familyPhysicalOutputLayout D.physicalDimension) horder
          hpriv).symm
        ((readoutCircuit D.physicalDimension (unitLevelFrame k done S rank V patch hV)
          (((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map aux) ℓ
          (D.physicalDimension_eq_of_site_eq fun v => (hsite v).trans
            (unitLevelFrame_owner hk hdone v).symm)
          (D.physicalDimension_eq_one_of_site_eq fun v => (hsite v).trans
            (unitLevelFrame_owner hk hdone v).symm)).eval
          (stackVec Ω (unitLevelFrame k done S rank V patch hV ::
            ((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map aux) ξ))) :
    ∃ Ξ : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem D.privateOutput))),
      ‖Ξ‖ ≤ 1 ∧ 1 - 214 / (L : ℝ) ^ 57 ≤ ‖Ξ‖ ∧
        D.readout (D.reference D.changes) = Matrix.euclideanTensorVector Ω Ξ := by
  have hL : 0 < L := by
    by_contra h
    have : L = 0 := by omega
    subst this
    simp at hk'
  have hM := (guideFrame_unitLevel (g := blockGuide 1 (protocolLevelLabels k 0 done))
    (own := labelParty S) (ph := guidePlaceholder) (rank := rank) (hV := hV)
    isCellCenter_cellCenterPos hc hcorner hs).1
  refine D.exists_reference_changes_of_readoutCircuit _ _ ℓ
    (unitLevelFrame_owner_injective hk hdone) hM
    (fun v => (hsite v).trans (unitLevelFrame_owner hk hdone v).symm) horder hpriv hΩ hL
    ?_ ?_ hξ href
  · intro F hF h hh
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hF
    rw [← GuideFrameRewrite.rpow_neg_sixty]
    exact (hsupply x hx h hh).norm_act_proj_sub_le
  · have hnat := sum_frozenHoles_le_cube hk' large Fr
    have hle : ((((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map aux).map
        fun F => F.holes.length).sum ≤ 214 * L ^ 3 := by
      rw [List.map_map]
      exact (List.sum_le_sum fun x hx => haux x hx).trans hnat
    have hcast : ((((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map aux).map
        fun F => (F.holes.length : ℝ)).sum =
        (((((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map aux).map
          fun F => F.holes.length).sum : ℕ) := by
      simp only [Nat.cast_list_sum, List.map_map, Function.comp_def]
    rw [hcast]
    exact_mod_cast hle

end TNLean.PEPS.Approximation
