/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scan.ReceivingRegions
import TNLean.PEPS.AreaLaw.Scan.StatusContainment
import TNLean.PEPS.AreaLaw.Scan.StatusCutBounds

/-!
# The four physical collar regions at every actual terminal

The original target, positive near region, middle and far region form a
partition at each completed or pre-charge terminal. The complement of the
same compact truncation set lies in every far region. These are consequences
of the actual status invariants, not assumptions about an independently
supplied family of leaves.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 868--873 and 900--911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- Every literal terminal has the disjoint collar partition and contains
the outside of the same truncation set on its far side. The horizon does not
enter the compact-containment argument. Source: `08-scanner.tex`, 900--911. -/
theorem terminalPartition_collar_geometry
    {I : Type} [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)}
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (H L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (j : terminalFamily S.K S.m S.M H) (g : Fin S.K) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S H j g
    let U := positiveNear S.depth σ
    let Y := middle σ
    let V := receiving σ true
    receiving σ false = X ∪ U ∧
      U ∪ Y = positiveNearMiddle S.depth σ ∧
      V = (receiving σ false ∪ Y)ᶜ ∧
      Disjoint X U ∧ Disjoint X Y ∧ Disjoint X V ∧
      Disjoint U Y ∧ Disjoint U V ∧ Disjoint Y V ∧
      X ∪ U ∪ Y ∪ V = Finset.univ ∧ (S.truncationSet L)ᶜ ⊆ V := by
  classical
  intro X σ U Y V
  have hnear : receiving σ false = X ∪ U := by
    cases j with
    | inl j => exact (state_receiving_regions hT S hdepth j.2 g).1
    | inr j => exact (oldChargeState_receiving_regions hT S hdepth j.2 g).1
  have hmiddle : ∀ x, σ x = none → 0 < S.depth x := by
    cases j with
    | inl j =>
      exact fun x hx ↦ lt_of_lt_of_le (by decide : (0 : ℤ) < 1)
        (Finset.mem_Icc.mp (S.state_depth_bounds j.2 g hL x hx)).1
    | inr j =>
      exact fun x hx ↦ lt_of_lt_of_le (by decide : (0 : ℤ) < 1)
        (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds j.2 g hL x hx)).1
  have hUYeq : U ∪ Y = positiveNearMiddle S.depth σ := by
    simp only [U, Y, positiveNear, positiveNearMiddle, Finset.filter_union,
      (Finset.filter_eq_self (s := middle σ) (p := fun x ↦ 0 < S.depth x)).mpr
        (fun x hx ↦ hmiddle x (Finset.mem_filter.mp hx).2)]
  have hfar : V = (receiving σ false ∪ Y)ᶜ := by
    ext x
    cases hx : σ x with
    | none => simp [V, Y, receiving, middle, hx]
    | some side => cases side <;> simp [V, Y, receiving, middle, hx]
  have hfar' : V = (X ∪ U ∪ Y)ᶜ := by rw [hfar, hnear]
  have hXU : Disjoint X U := Finset.disjoint_left.mpr fun x hx hu ↦ by
    have hd : S.depth x ≤ 0 := by
      simpa only [hdepth, Nat.cast_zero] using
        (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
          ((ambientDilation_zero T).symm ▸ (Finset.mem_filter.mp hx).2)
    exact (not_lt_of_ge hd) (Finset.mem_filter.mp hu).2
  have hnearY : Disjoint (receiving σ false) Y := by
    refine Finset.disjoint_left.mpr fun x hx hy ↦ ?_
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rw [hx'] at hy'
    cases hy'
  have hXnear : X ⊆ receiving σ false := by rw [hnear]; exact Finset.subset_union_left
  have hUnear : U ⊆ receiving σ false := Finset.filter_subset _ _
  have hdisjoint (Q : Finset (Site Λ)) (hQ : Q ⊆ X ∪ U ∪ Y) : Disjoint Q V := by
    rw [hfar']
    exact Finset.disjoint_left.mpr fun x hx hv ↦ (Finset.mem_compl.mp hv) (hQ hx)
  have hcover : X ∪ U ∪ Y ∪ V = Finset.univ := by rw [hfar']; simp
  have hcompact : Vᶜ ⊆ S.truncationSet L := by
    cases j with
    | inl j => exact S.state_far_compl_subset_truncationSet j.2 g hL
    | inr j => exact S.oldChargeState_far_compl_subset_truncationSet j.2 g hL
  have hWfar : (S.truncationSet L)ᶜ ⊆ V := by
    intro x hx
    by_contra hv
    exact (Finset.mem_compl.mp hx) (hcompact (Finset.mem_compl.mpr hv))
  exact ⟨hnear, hUYeq, hfar, hXU, hnearY.mono_left hXnear,
    hdisjoint X (Finset.subset_union_left.trans Finset.subset_union_left),
    hnearY.mono_left hUnear,
    hdisjoint U (Finset.subset_union_right.trans Finset.subset_union_left),
    hdisjoint Y Finset.subset_union_right, hcover, hWfar⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
