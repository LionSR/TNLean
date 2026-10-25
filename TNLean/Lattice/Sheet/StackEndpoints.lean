/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Stack

/-!
# Initialization and reordering of the sheets

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds the main
sheet, the active auxiliary sheets, the frozen auxiliary sheets and the auxiliary copies of `Ω`
not yet in use. Every copy of `Ω`, including the main copy at the root, is initialized privately
at its future owner, so the initial vector is a pure product across parties
(`06-geometry.tex`, lines 658–667). This file supplies two pieces of that bookkeeping for the
memory of a list of sheets of an arbitrary type, each sheet `F` with registers `regs F` and a
reference vector `ref F` (`Lattice.stackRegs`, `Lattice.stackVec`).

* **Reordering the sheets.** A permutation of the sheets is implemented by a word of exchanges
  of tensor factors that carries the reference vector of the sheets, in the old order, to the
  reference vector in the new order (`Lattice.exists_reordering_stackVec`). In particular an
  auxiliary sheet can be moved next to the main sheet before a lens exchange, which acts on two
  adjacent sheets (`Lattice.liftTwo`). As an original circuit the reordering has no nonprivate
  gate (`Lattice.exists_originalCircuit_stackVec_of_perm`).
* **The initial private maps.** If each sheet of a list is held entirely by one party, the
  whole private memory of a party can be taken to be the memory of its sheets. One private map
  per party then splits these whole memories into the registers of the sheets, and carries the
  product of the reference vectors of the parties to the reference vector of all sheets
  (`Lattice.exists_originalCircuit_initial`).

## Main results

* `Lattice.exists_reordering_stackVec`, `Lattice.exists_originalCircuit_stackVec_of_perm`.
* `Lattice.stackVec_append`.
* `Lattice.exists_originalCircuit_initial`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 21–23 and 39–41 (statement) and 653–667 (initialization and the
  reference vectors); private maps, `04-compression.tex`, lines 21–36 and 137–139.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.Lattice

open TNLean.Lattice.PartyCircuit

variable {κ : Type*} {Party : Type}

/-! ### Registers of concatenated lists of sheets -/

/-- The registers of a concatenated list of sheets. -/
theorem stackRegs_append (regs : κ → Layout Party) (A B : List κ) (ℓ : Layout Party) :
    stackRegs regs A [] ++ stackRegs regs B ℓ = stackRegs regs (A ++ B) ℓ := by
  induction A with
  | nil => rfl
  | cons F A ih => exact (List.append_assoc _ _ _).trans (congrArg (regs F ++ ·) ih)

section Reference

variable {regs : κ → Layout Party} (ref : (F : κ) → Mem (regs F))

/-- The reference vector of a list of sheets, with no idle registers. -/
abbrev framesVec (Fs : List κ) : Mem (stackRegs regs Fs []) :=
  stackVec ref Fs (ℓ := []) (1 : ℂ)

private theorem appendIso_symm_memCongr_heq (a : Layout Party) {b c : Layout Party} (h : b = c)
    (x : Mem a) (y : Mem b) :
    HEq ((appendIso a b).symm (x ⊗ₜ y)) ((appendIso a c).symm (x ⊗ₜ Layout.memCongr h y)) := by
  cases h
  rfl

/-- The reference vector of a concatenated list of sheets is the product of the reference
vectors of the two lists. -/
theorem stackVec_append (A B : List κ) {ℓ : Layout Party} (ξ : Mem ℓ) :
    Layout.memCongr (stackRegs_append regs A B ℓ)
        ((appendIso (stackRegs regs A []) (stackRegs regs B ℓ)).symm
          (framesVec ref A ⊗ₜ stackVec ref B ξ)) =
      stackVec ref (A ++ B) ξ := by
  induction A with
  | nil =>
      change (appendIso ([] : Layout Party) (stackRegs regs B ℓ)).symm
        ((1 : ℂ) ⊗ₜ stackVec ref B ξ) = _
      rw [appendIso_nil_symm_tmul, one_smul]
      rfl
  | cons F A ih =>
      apply eq_of_heq
      refine (Layout.memCongr_apply_heq _ _).trans ?_
      refine (appendIso_assoc_symm_heq (regs F) (stackRegs regs A []) (stackRegs regs B ℓ)
        (ref F) (framesVec ref A) (stackVec ref B ξ)).symm.trans ?_
      change HEq _ ((appendIso (regs F) (stackRegs regs (A ++ B) ℓ)).symm
        (ref F ⊗ₜ stackVec ref (A ++ B) ξ))
      rw [← ih]
      exact appendIso_symm_memCongr_heq (regs F) _ _ _

/-! ### Reordering the sheets -/

/-- **Reordering the sheets.** A permutation of a list of sheets is implemented on their
registers, followed by untouched registers `ℓ`, by a word of exchanges of tensor factors that
carries the reference vector of the sheets in the old order to the reference vector in the new
order. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 662–667, and allowed monomials,
`04-compression.tex`, lines 32–35. -/
theorem exists_reordering_stackVec {Fs Fs' : List κ} (h : Fs.Perm Fs') (ℓ : Layout Party) :
    ∃ w : Word (stackRegs regs Fs ℓ) (stackRegs regs Fs' ℓ), w.IsReordering ∧
      ∀ ξ : Mem ℓ, w.eval (stackVec ref Fs ξ) = stackVec ref Fs' ξ := by
  induction h with
  | nil => exact ⟨.id _, Word.isReordering_id _, fun _ => rfl⟩
  | cons F _ ih =>
      obtain ⟨w, hw, he⟩ := ih
      exact ⟨Word.frameList (regs F) w, hw.frameList _, fun ξ => by
        change (Word.frameList (regs F) w).eval ((appendIso _ _).symm (ref F ⊗ₜ _)) = _
        rw [Word.eval_frameList_appendIso_symm, he]
        rfl⟩
  | swap F G Fs =>
      exact ⟨Word.exchangeBlocks (regs G) (regs F) (stackRegs regs Fs ℓ),
        Word.isReordering_exchangeBlocks _ _ _,
        fun ξ => Word.eval_exchangeBlocks_appendIso_symm _ _ _ _ _ _⟩
  | trans _ _ ih ih' =>
      obtain ⟨w, hw, he⟩ := ih
      obtain ⟨w', hw', he'⟩ := ih'
      exact ⟨.comp w w', hw.comp hw', fun ξ => by
        rw [Word.eval_comp, comp_apply, he, he']⟩

/-- **Reordering the sheets, as an original circuit.** The reordering of
`exists_reordering_stackVec` has no nonprivate gate, so every participant condition holds
vacuously, and it carries the reference vector of the sheets to the reference vector in the
new order. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 662–667, and original circuits,
`04-compression.tex`, lines 199–208. -/
theorem exists_originalCircuit_stackVec_of_perm {Fs Fs' : List κ} (h : Fs.Perm Fs')
    (ℓ : Layout Party) :
    ∃ c : OriginalCircuit (stackRegs regs Fs ℓ) (stackRegs regs Fs' ℓ), c.nonprivateCount = 0 ∧
      (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      ∀ ξ : Mem ℓ, c.eval (stackVec ref Fs ξ) = stackVec ref Fs' ξ := by
  obtain ⟨w, hw, he⟩ := exists_reordering_stackVec ref h ℓ
  refine ⟨w.toOriginalCircuit hw.isAllowed, Word.nonprivateCount_toOriginalCircuit_of_isReordering
    hw, fun S g => Word.participants_toOriginalCircuit_subset _ _ (hw.usesOnly S) g,
    fun r s => Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw.sourceCount_eq r s,
    fun K => Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw.sourceCount_eq K, fun ξ => ?_⟩
  rw [Word.eval_toOriginalCircuit, he]

/-! ### Identity changes -/

/-- **The identity change.** A change that leaves the sheet unchanged is the original circuit
without operations: it has no nonprivate gate and no reference error. It is kept as a change so
that the counts of changes per event do not depend on the geometry. Polynomial-PEPS manuscript,
`06-geometry.tex`, lines 432–438 and 529–541. -/
theorem exists_originalCircuit_of_eq {F F' : κ} (h : F = F') :
    ∃ c : OriginalCircuit (regs F) (regs F'), c.nonprivateCount = 0 ∧
      (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      c.eval (ref F) = ref F' := by
  subst h
  exact ⟨.id _, rfl, fun _ g => (nomatch g), fun _ _ => trivial, fun _ => trivial, rfl⟩

end Reference

/-! ### The initial private maps -/

section Initial

variable (regs : κ → Layout Party)

private theorem memCongr_self_symm_apply {a : Layout Party} (h : a = a) (x : Mem a) :
    (Layout.memCongr h).symm x = x :=
  rfl

/-- The whole initial private memory of a party that holds the list of sheets `Fs`: the memory
of the registers of these sheets. -/
abbrev framesSpace (Fs : List κ) : HSpace := Mem (stackRegs regs Fs [])

/-- The private map of a party that splits its whole memory `ℂ ⊗ M` into the registers of its
sheets. -/
def splitMap (Fs : List κ) (p : Party) :
    Mem [(⟨p, framesSpace regs Fs⟩ : Reg Party)] →L[ℂ] Mem (stackRegs regs Fs []) :=
  (TensorProduct.ridIsometry ℂ (framesSpace regs Fs)).toLinearIsometry.toContinuousLinearMap

theorem splitMap_tmul_one (Fs : List κ) (p : Party) (x : framesSpace regs Fs) :
    splitMap regs Fs p (x ⊗ₜ (1 : ℂ)) = x := by
  simp [splitMap]

theorem norm_splitMap_le (Fs : List κ) (p : Party) : ‖splitMap regs Fs p‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- The initial private maps: every party `p` of the list `ps`, holding the sheets `blk p`,
splits its whole memory into the registers of these sheets, by one private map each. -/
def splitCircuit (blk : Party → List κ) (hblk : ∀ p, ∀ r ∈ stackRegs regs (blk p) [], r.owner = p) :
    (ps : List Party) →
      OriginalCircuit (ps.map fun p => (⟨p, framesSpace regs (blk p)⟩ : Reg Party))
        (stackRegs regs (ps.flatMap blk) [])
  | [] => .id []
  | p :: ps =>
      .comp (.privateMap p (a := [⟨p, framesSpace regs (blk p)⟩]) (by simp) (hblk p)
          (splitMap regs (blk p) p) (norm_splitMap_le regs _ _)
          (ps.map fun p => (⟨p, framesSpace regs (blk p)⟩ : Reg Party)))
        ((OriginalCircuit.frameList (stackRegs regs (blk p) [])
            (splitCircuit blk hblk ps)).castLayouts
          rfl ((stackRegs_append regs _ _ _).trans (by rw [List.flatMap_cons])))

theorem nonprivateCount_splitCircuit (blk : Party → List κ)
    (hblk : ∀ p, ∀ r ∈ stackRegs regs (blk p) [], r.owner = p) :
    (ps : List Party) → (splitCircuit regs blk hblk ps).nonprivateCount = 0
  | [] => rfl
  | _ :: ps => by
      simp only [splitCircuit, OriginalCircuit.nonprivateCount,
        OriginalCircuit.nonprivateCount_castLayouts, OriginalCircuit.nonprivateCount_frameList,
        nonprivateCount_splitCircuit blk hblk ps]

theorem isExpansionBounded_splitCircuit (blk : Party → List κ)
    (hblk : ∀ p, ∀ r ∈ stackRegs regs (blk p) [], r.owner = p) (r : ℕ) (s : ℝ) :
    (ps : List Party) → (splitCircuit regs blk hblk ps).IsExpansionBounded r s
  | [] => trivial
  | _ :: ps => ⟨trivial, OriginalCircuit.isExpansionBounded_castLayouts _ _ _
      (OriginalCircuit.isExpansionBounded_frameList _
        (isExpansionBounded_splitCircuit blk hblk r s ps) _)⟩

theorem isMonomialBounded_splitCircuit (blk : Party → List κ)
    (hblk : ∀ p, ∀ r ∈ stackRegs regs (blk p) [], r.owner = p) (K : ℕ) :
    (ps : List Party) → (splitCircuit regs blk hblk ps).IsMonomialBounded K
  | [] => trivial
  | _ :: ps => ⟨trivial, OriginalCircuit.isMonomialBounded_castLayouts _ _ _
      (OriginalCircuit.isMonomialBounded_frameList _
        (isMonomialBounded_splitCircuit blk hblk K ps) _)⟩

theorem participants_splitCircuit_subset (blk : Party → List κ)
    (hblk : ∀ p, ∀ r ∈ stackRegs regs (blk p) [], r.owner = p) (S : Set Party) :
    (ps : List Party) → (g : (splitCircuit regs blk hblk ps).nonprivateLocations) →
      (↑((splitCircuit regs blk hblk ps).participants g) : Set Party) ⊆ S
  | [], g => nomatch g
  | _ :: ps, g => by
      rcases g with g | g
      · exact nomatch g
      · exact OriginalCircuit.participants_castLayouts_subset _ _ _
          (OriginalCircuit.participants_frameList_subset _
            (participants_splitCircuit_subset blk hblk S ps) _) g

variable {regs} (ref : (F : κ) → Mem (regs F))

/-- The initial private maps carry the product of the reference vectors of the parties to the
reference vector of all sheets. -/
theorem eval_splitCircuit (blk : Party → List κ)
    (hblk : ∀ p, ∀ r ∈ stackRegs regs (blk p) [], r.owner = p)
    (hx : ∀ p, ‖framesVec ref (blk p)‖ = 1) :
    (ps : List Party) →
      (splitCircuit regs blk hblk ps).eval
          (ProductInput.ofParties (fun p => framesSpace regs (blk p))
            (fun p => framesVec ref (blk p)) hx ps).vector =
        framesVec ref (ps.flatMap blk)
  | [] => rfl
  | p :: ps => by
      have ih := eval_splitCircuit blk hblk hx ps
      simp only [splitCircuit, OriginalCircuit.eval, OriginalCircuit.eval_castLayouts,
        comp_apply, isoL_apply, ProductInput.ofParties, ProductInput.vector]
      erw [appendIso_one_tmul]
      rw [rTensor_tmul, splitMap_tmul_one, memCongr_self_symm_apply]
      rw [OriginalCircuit.eval_frameList_appendIso_symm, ih]
      apply eq_of_heq
      refine (Layout.memCongr_apply_heq _ _).trans ?_
      refine HEq.trans ?_ (heq_of_eq (stackVec_append ref (blk p) (ps.flatMap blk) (ℓ := [])
        (1 : ℂ)))
      refine HEq.trans ?_ (Layout.memCongr_apply_heq _ _).symm
      congr 1

/-- **The initial private maps.** Let every sheet `F` of the list `Fs` be held entirely by the
party `holder F`. Take as the whole initial memory of each party the memory of its sheets, in
their order in `Fs`, and as its initial vector the product of their reference vectors, of norm
one. One private map per party splits the whole memories into the registers of the sheets, and
a reordering puts the sheets in the order of `Fs`. The resulting original circuit has no
nonprivate gate and carries the initial product vector exactly to the reference vector of `Fs`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 21–23 and 658–667 (“Initialize all
required copies of `Ω` privately at their future owners, including the main copy at the root.
This is a pure product initialization across parties”), and the product inputs of Theorem 5.2,
`04-compression.tex`, lines 137–139. -/
theorem exists_originalCircuit_initial [Fintype Party] [DecidableEq Party] (Fs : List κ)
    (holder : κ → Party) (hown : ∀ F ∈ Fs, ∀ r ∈ regs F, r.owner = holder F)
    (hx : ∀ p, ‖framesVec ref (Fs.filter fun F => holder F = p)‖ = 1) :
    ∃ c : OriginalCircuit
        (ProductInput.wholePartyLayout fun p => framesSpace regs (Fs.filter fun F => holder F = p))
        (stackRegs regs Fs []),
      c.nonprivateCount = 0 ∧ (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      c.eval (ProductInput.ofAllParties _ _ hx).vector = framesVec ref Fs := by
  set blk : Party → List κ := fun p => Fs.filter fun F => holder F = p
  have hblk : ∀ p, ∀ r ∈ stackRegs regs (blk p) [], r.owner = p := by
    intro p
    suffices ∀ G : List κ, (∀ F ∈ G, holder F = p ∧ F ∈ Fs) →
        ∀ r ∈ stackRegs regs G [], r.owner = p from
      this _ fun F hF => by
        obtain ⟨h1, h2⟩ := List.mem_filter.1 hF
        exact ⟨by simpa using h2, h1⟩
    intro G hG
    induction G with
    | nil => simp
    | cons F G ih =>
        intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · obtain ⟨h1, h2⟩ := hG F List.mem_cons_self
          exact (hown F h2 r hr).trans h1
        · exact ih (fun F hF => hG F (List.mem_cons_of_mem _ hF)) r hr
  have hperm : ((Finset.univ : Finset Party).toList.flatMap blk).Perm Fs := by
    classical
    rw [List.perm_iff_count]
    intro F
    have key : ∀ p, (blk p).count F = if holder F = p then Fs.count F else 0 := by
      intro p
      split_ifs with hp
      · exact List.count_filter (by simpa using hp)
      · exact List.count_eq_zero.2 fun h => hp (by simpa using (List.mem_filter.1 h).2)
    rw [List.count_flatMap, Function.comp_def, Finset.sum_map_toList]
    simp only [key, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  obtain ⟨c, h0, hP, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm ref hperm []
  refine ⟨.comp (splitCircuit regs blk hblk _) c, ?_, fun S g => ?_, fun r s =>
    ⟨isExpansionBounded_splitCircuit regs blk hblk r s _, hE r s⟩,
    fun K => ⟨isMonomialBounded_splitCircuit regs blk hblk K _, hM K⟩, ?_⟩
  · change (splitCircuit regs blk hblk _).nonprivateCount + c.nonprivateCount = 0
    rw [nonprivateCount_splitCircuit, h0]
  · rcases g with g | g
    · exact participants_splitCircuit_subset regs blk hblk S _ g
    · exact hP S g
  · change c.eval ((splitCircuit regs blk hblk _).eval _) = _
    exact (congrArg c.eval (eval_splitCircuit ref blk hblk hx _)).trans (he (1 : ℂ))

end Initial

end TNLean.Lattice
