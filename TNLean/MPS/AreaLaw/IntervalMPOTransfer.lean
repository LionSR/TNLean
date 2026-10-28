/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.RegionalMiddleFactors
import TNLean.MPS.AreaLaw.FixedConfigurationExtension
import TNLean.MPS.AreaLaw.IntervalSlice
import TNLean.Algebra.MatrixFactorExchange
import Mathlib.Data.Matrix.Basis

/-!
# Matrix product bounds under a change of interval

Restricting an operator to the overlap of two intervals and fixing the
remaining row and column configurations gives an operator on the new interval.
The supplied open-boundary bond bound becomes `max 1 D`, including an overlap
of length zero. Increasing coordinates preserve the original order of sites.

The prescribed regional family is formed from the old middle matrices and
standard matrix units before any exterior coefficients are supplied. Its
cardinality counts the two transferred configuration spaces exactly. The
algebraic exchange of matrix factors and extension by a fixed configuration
are imported from their existing modules.

These are interval-transfer identities supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. Positivity of the local
dimension and nonreversed overlap are explicit hypotheses.
-/

open Matrix
open scoped BigOperators Kronecker Matrix

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Fix the exterior of an interval and extend the resulting vector into a new
chain by a prescribed exterior configuration, preserving increasing site order.
The bound includes empty and one-site intervals. This composes the interval
restriction used in Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
lines 436–470, with the elementary extension step used in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem IsOpenMPS.intervalSlice_extend_by_configuration {T L N d D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin T → Fin d)}
    (hψ : IsOpenMPS T d D (fun x ↦ ψ x))
    (a : ℕ) (ha : a + L ≤ T) (σ₀ : Fin T → Fin d)
    (b : ℕ) (hb : b + L ≤ N)
    (η : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} → Fin d) :
    IsOpenMPS N d (max 1 D) (fun σ ↦
      if (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ σ v.val) = η
      then TNLean.MPS.AreaLaw.intervalSlice (L := L) ψ a σ₀
        (fun r : Fin L ↦ σ ⟨b + r.val, by omega⟩) else 0) := by
  exact IsOpenMPS.extend_interval_by_configuration
    (ψ := TNLean.MPS.AreaLaw.intervalSlice (L := L) ψ a σ₀) (hψ.intervalSlice a ha σ₀) b hb η

/-- Fix exterior row and column configurations on an interval, then extend by
specified row and column configurations on a new chain. The paired physical
alphabet gives bond bound `max 1 D`, including zero lengths and dimensions.
This is elementary interval transport supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333. -/
private theorem isOpenMPS_matrix_intervalSlice_extend_by_configuration
    {T L N q D : ℕ}
    (V : Matrix (Fin T → Fin q) (Fin T → Fin q) ℂ)
    (hV : IsOpenMPS T (q * q) D (fun x ↦
      V (fun j ↦ (finProdFinEquiv.symm (x j)).1)
        (fun j ↦ (finProdFinEquiv.symm (x j)).2)))
    (a : ℕ) (ha : a + L ≤ T) (σr₀ σc₀ : Fin T → Fin q)
    (b : ℕ) (hb : b + L ≤ N)
    (ηr ηc : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} → Fin q) :
    let W : Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ := fun σ τ ↦
      if (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ σ v.val) = ηr ∧
          (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ τ v.val) = ηc
      then V (insertInterval a σr₀ (fun r : Fin L ↦ σ ⟨b + r.val, by omega⟩))
        (insertInterval a σc₀ (fun r : Fin L ↦ τ ⟨b + r.val, by omega⟩)) else 0
    IsOpenMPS N (q * q) (max 1 D) (fun x ↦
      W (fun j ↦ (finProdFinEquiv.symm (x j)).1)
        (fun j ↦ (finProdFinEquiv.symm (x j)).2)) := by
  classical
  let e : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv
  let W : Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ := fun σ τ ↦
    if (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ σ v.val) = ηr ∧
        (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ τ v.val) = ηc
    then V (insertInterval a σr₀ (fun r : Fin L ↦ σ ⟨b + r.val, by omega⟩))
      (insertInterval a σc₀ (fun r : Fin L ↦ τ ⟨b + r.val, by omega⟩)) else 0
  change IsOpenMPS N (q * q) (max 1 D)
    (fun x ↦ W (fun j ↦ (e.symm (x j)).1) (fun j ↦ (e.symm (x j)).2))
  let ψ : EuclideanSpace ℂ (Fin T → Fin (q * q)) := WithLp.toLp 2 fun x ↦
    V (fun j ↦ (e.symm (x j)).1) (fun j ↦ (e.symm (x j)).2)
  let ξ : Fin T → Fin (q * q) := fun j ↦ e (σr₀ j, σc₀ j)
  let η : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} → Fin (q * q) :=
    fun v ↦ e (ηr v, ηc v)
  have hψ : IsOpenMPS T (q * q) D (fun x ↦ ψ x) := hV
  have h := hψ.intervalSlice_extend_by_configuration a ha ξ b hb η
  have hfun :
      (fun x : Fin N → Fin (q * q) ↦
        W (fun j ↦ (e.symm (x j)).1) (fun j ↦ (e.symm (x j)).2)) =
        (fun x : Fin N → Fin (q * q) ↦
          if (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ x v.val) = η
          then TNLean.MPS.AreaLaw.intervalSlice (L := L) ψ a ξ
            (fun r : Fin L ↦ x ⟨b + r.val, by omega⟩) else 0) := by
    funext x
    have hmatch :
        (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ x v.val) = η ↔
          (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦
            (e.symm (x v.val)).1) = ηr ∧
          (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦
            (e.symm (x v.val)).2) = ηc := by
      constructor
      · intro hx
        constructor
        · funext v
          have hv := congrArg (fun z ↦ (e.symm z).1) (congrFun hx v)
          simpa only [η, Equiv.symm_apply_apply] using hv
        · funext v
          have hv := congrArg (fun z ↦ (e.symm z).2) (congrFun hx v)
          simpa only [η, Equiv.symm_apply_apply] using hv
      · rintro ⟨hr, hc⟩
        funext v
        apply e.symm.injective
        apply Prod.ext
        · simpa only [η, Equiv.symm_apply_apply] using congrFun hr v
        · simpa only [η, Equiv.symm_apply_apply] using congrFun hc v
    have hrow :
        (fun j : Fin T ↦
          (e.symm (insertInterval a ξ
            (fun r : Fin L ↦ x ⟨b + r.val, by omega⟩) j)).1) =
          insertInterval a σr₀
            (fun r : Fin L ↦ (e.symm (x ⟨b + r.val, by omega⟩)).1) := by
      funext j
      by_cases hj : a ≤ j.val ∧ j.val < a + L
      · simp only [insertInterval, dite_eq_left hj]
      · simp only [insertInterval, dite_eq_right hj, ξ, Equiv.symm_apply_apply]
    have hcol :
        (fun j : Fin T ↦
          (e.symm (insertInterval a ξ
            (fun r : Fin L ↦ x ⟨b + r.val, by omega⟩) j)).2) =
          insertInterval a σc₀
            (fun r : Fin L ↦ (e.symm (x ⟨b + r.val, by omega⟩)).2) := by
      funext j
      by_cases hj : a ≤ j.val ∧ j.val < a + L
      · simp only [insertInterval, dite_eq_left hj]
      · simp only [insertInterval, dite_eq_right hj, ξ, Equiv.symm_apply_apply]
    change (if
      (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦
        (e.symm (x v.val)).1) = ηr ∧
      (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦
        (e.symm (x v.val)).2) = ηc
      then V (insertInterval a σr₀
        (fun r : Fin L ↦ (e.symm (x ⟨b + r.val, by omega⟩)).1))
        (insertInterval a σc₀
          (fun r : Fin L ↦ (e.symm (x ⟨b + r.val, by omega⟩)).2)) else 0) =
      (if (fun v : {v : Fin N // ¬(b ≤ v.val ∧ v.val < b + L)} ↦ x v.val) = η
      then V (fun j ↦ (e.symm (insertInterval a ξ
        (fun r : Fin L ↦ x ⟨b + r.val, by omega⟩) j)).1)
        (fun j ↦ (e.symm (insertInterval a ξ
          (fun r : Fin L ↦ x ⟨b + r.val, by omega⟩) j)).2) else 0)
    simp only [hmatch, hrow, hcol]
  rw [hfun]
  exact h

end TNLean.MPS.AreaLaw

namespace FiniteProduct

variable {V : Type*} [DecidableEq V] (β : V → Type*)

/-- The first old-middle coordinate is restriction to the removed region. -/
private theorem changingOldMiddleConfigEquiv_apply_fst (E J : Finset V)
    (x : Configuration β E) (v : ↥(E \ J)) :
    (changingOldMiddleConfigEquiv β E J x).1 v =
      x ⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩ := by
  simp [changingOldMiddleConfigEquiv, unionEquiv, configurationCongr_apply]

/-- The second old-middle coordinate is restriction to the common intersection. -/
private theorem changingOldMiddleConfigEquiv_apply_snd (E J : Finset V)
    (x : Configuration β E) (v : ↥(E ∩ J)) :
    (changingOldMiddleConfigEquiv β E J x).2 v =
      x ⟨v.val, (Finset.mem_inter.mp v.property).1⟩ := by
  simp [changingOldMiddleConfigEquiv, unionEquiv, configurationCongr_apply]

/-- Outside the new middle, inverse restriction uses the removed-region coordinate. -/
private theorem changingOldMiddleConfigEquiv_symm_apply_of_notMem (E J : Finset V)
    (xA : Configuration β (E \ J)) (xC : Configuration β (E ∩ J))
    (v : ↥E) (hv : v.val ∉ J) :
    (changingOldMiddleConfigEquiv β E J).symm (xA, xC) v =
      xA ⟨v.val, Finset.mem_sdiff.mpr ⟨v.property, hv⟩⟩ := by
  let a : ↥(E \ J) := ⟨v.val, Finset.mem_sdiff.mpr ⟨v.property, hv⟩⟩
  have h := congrArg
    (fun z : Configuration β (E \ J) × Configuration β (E ∩ J) ↦ z.1 a)
    ((changingOldMiddleConfigEquiv β E J).apply_symm_apply (xA, xC))
  rw [changingOldMiddleConfigEquiv_apply_fst] at h
  exact h

/-- Inside the new middle, inverse restriction uses the common-intersection coordinate. -/
private theorem changingOldMiddleConfigEquiv_symm_apply_of_mem (E J : Finset V)
    (xA : Configuration β (E \ J)) (xC : Configuration β (E ∩ J))
    (v : ↥E) (hv : v.val ∈ J) :
    (changingOldMiddleConfigEquiv β E J).symm (xA, xC) v =
      xC ⟨v.val, Finset.mem_inter.mpr ⟨v.property, hv⟩⟩ := by
  let c : ↥(E ∩ J) := ⟨v.val, Finset.mem_inter.mpr ⟨v.property, hv⟩⟩
  have h := congrArg
    (fun z : Configuration β (E \ J) × Configuration β (E ∩ J) ↦ z.2 c)
    ((changingOldMiddleConfigEquiv β E J).apply_symm_apply (xA, xC))
  rw [changingOldMiddleConfigEquiv_apply_snd] at h
  exact h

/-- The first new-middle coordinate is restriction to the newly retained region. -/
private theorem changingNewMiddleConfigEquiv_apply_fst (E J : Finset V)
    (x : Configuration β J) (v : ↥(J \ E)) :
    (changingNewMiddleConfigEquiv β E J x).1 v =
      x ⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩ := by
  simp [changingNewMiddleConfigEquiv, changingOldMiddleConfigEquiv,
    Equiv.prodCongr, unionEquiv, configurationCongr_apply]

/-- The second new-middle coordinate uses the same literal intersection E∩J. -/
private theorem changingNewMiddleConfigEquiv_apply_snd (E J : Finset V)
    (x : Configuration β J) (v : ↥(E ∩ J)) :
    (changingNewMiddleConfigEquiv β E J x).2 v =
      x ⟨v.val, (Finset.mem_inter.mp v.property).2⟩ := by
  simp [changingNewMiddleConfigEquiv, changingOldMiddleConfigEquiv,
    Equiv.prodCongr, unionEquiv, configurationCongr_apply]

end FiniteProduct

namespace TNLean.MPS.AreaLaw

/-- In increasing coordinates on an interval, membership in a second interval
is membership in their overlap. This elementary coordinate identity supports
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem intervalShiftOrderIso_mem_overlap {T c d u v : ℕ}
    (hcd : c ≤ d) (hd : d ≤ T) (i : Fin (d - c)) :
    (intervalShiftOrderIso hcd hd i).val ∈ interval T u v ↔
      max c u - c ≤ i.val ∧
        i.val < (max c u - c) + (min d v - max c u) := by
  have hE := mem_interval.mp (intervalShiftOrderIso hcd hd i).property
  calc
    (intervalShiftOrderIso hcd hd i).val ∈ interval T u v ↔
        (intervalShiftOrderIso hcd hd i).val ∈
          interval T (max c u) (min d v) := by
      simp only [mem_interval]
      omega
    _ ↔ _ := intervalShiftOrderIso_mem_subinterval hcd hd (Nat.le_max_left c u) i

/-- Natural coordinates outside the overlap correspond to the actual interval
difference, with the same increasing physical positions. Neither the second
interval nor the overlap is required to be nonempty. This is an auxiliary
coordinate identity supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. -/
private def intervalDifferenceNaturalEquiv {T c d u v : ℕ}
    (hcd : c ≤ d) (hd : d ≤ T) :
    {i : Fin (d - c) // ¬(max c u - c ≤ i.val ∧
      i.val < (max c u - c) + (min d v - max c u))} ≃
      ↥(interval T c d \ interval T u v) := by
  let e := intervalShiftOrderIso hcd hd
  have hmem (i : Fin (d - c)) :
      (e i).val ∈ interval T u v ↔
        max c u - c ≤ i.val ∧
          i.val < (max c u - c) + (min d v - max c u) :=
    intervalShiftOrderIso_mem_overlap hcd hd i
  refine {
    toFun := fun i ↦ ⟨(e i.val).val, Finset.mem_sdiff.mpr
      ⟨(e i.val).property, fun hJ ↦ i.property ((hmem i.val).mp hJ)⟩⟩
    invFun := fun x ↦ ⟨e.symm ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro hi
    have hJ := (hmem (e.symm
      ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩)).mpr hi
    rw [e.apply_symm_apply] at hJ
    exact (Finset.mem_sdiff.mp x.property).2 hJ
  · intro i
    apply Subtype.ext
    change e.symm (e i.val) = i.val
    exact e.symm_apply_apply i.val
  · intro x
    apply Subtype.ext
    change (e (e.symm
      ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩)).val = x.val
    exact congrArg Subtype.val
      (e.apply_symm_apply ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩)

/-- The interval-difference equivalence retains the original physical site.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem intervalDifferenceNaturalEquiv_apply_val {T c d u v : ℕ}
    (hcd : c ≤ d) (hd : d ≤ T)
    (i : {i : Fin (d - c) // ¬(max c u - c ≤ i.val ∧
      i.val < (max c u - c) + (min d v - max c u))}) :
    (intervalDifferenceNaturalEquiv hcd hd i).val =
      (intervalShiftOrderIso hcd hd i.val).val := rfl

/-- One actual transferred regional factor has natural interval MPO bound
`max 1 D`. The two regions are intervals with nonreversed overlap; their
increasing coordinates are the canonical interval order isomorphisms. The
positive local dimension supplies only a dummy common configuration.
This is the individual-factor change-of-cuts step supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem isOpenMPS_changingRegionalMiddleFactor
    {T q c d u v D : ℕ} (hq : 0 < q)
    (hcd : c ≤ d) (hd : d ≤ T) (huv : u ≤ v) (hv : v ≤ T)
    (hover : max c u ≤ min d v)
    (Vphys : Matrix (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d))
      (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d)) ℂ)
    (hV : let eE := intervalShiftOrderIso hcd hd
      IsOpenMPS (d - c) (q * q) D (fun x ↦
        Vphys (fun z ↦ (finProdFinEquiv.symm (x (eE.symm z))).1)
          (fun z ↦ (finProdFinEquiv.symm (x (eE.symm z))).2)))
    (αr αc : FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q)
      (interval T c d \ interval T u v))
    (ηr ηc : FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q)
      (interval T u v \ interval T c d)) :
    let old := FiniteProduct.changingOldMiddleConfigEquiv
      (fun _ : Fin T ↦ Fin q) (interval T c d) (interval T u v)
    let new := FiniteProduct.changingNewMiddleConfigEquiv
      (fun _ : Fin T ↦ Fin q) (interval T c d) (interval T u v)
    let Wphys := ((Matrix.single ηr ηc (1 : ℂ)) ⊗ₖ
      Matrix.operatorBlock (Vphys.reindex old old) αr αc).reindex new.symm new.symm
    let eJ := intervalShiftOrderIso huv hv
    IsOpenMPS (v - u) (q * q) (max 1 D) (fun x ↦
      Wphys (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).1)
        (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).2)) := by
  let β := fun _ : Fin T ↦ Fin q
  let E := interval T c d
  let J := interval T u v
  let old := FiniteProduct.changingOldMiddleConfigEquiv β E J
  let new := FiniteProduct.changingNewMiddleConfigEquiv β E J
  let Wphys := ((Matrix.single ηr ηc (1 : ℂ)) ⊗ₖ
    Matrix.operatorBlock (Vphys.reindex old old) αr αc).reindex new.symm new.symm
  let eE := intervalShiftOrderIso hcd hd
  let eJ := intervalShiftOrderIso huv hv
  let toE : (Fin (d - c) → Fin q) → FiniteProduct.Configuration β E :=
    fun σ z ↦ σ (eE.symm z)
  let toJ : (Fin (v - u) → Fin q) → FiniteProduct.Configuration β J :=
    fun σ z ↦ σ (eJ.symm z)
  change IsOpenMPS (v - u) (q * q) (max 1 D) (fun x ↦
    Wphys (toJ (fun j ↦ (finProdFinEquiv.symm (x j)).1))
      (toJ (fun j ↦ (finProdFinEquiv.symm (x j)).2)))
  let Vnat := Vphys.submatrix toE toE
  have hVnat : IsOpenMPS (d - c) (q * q) D (fun x ↦
      Vnat (fun j ↦ (finProdFinEquiv.symm (x j)).1)
        (fun j ↦ (finProdFinEquiv.symm (x j)).2)) := hV
  let left := max u c
  let right := min v d
  let len := right - left
  let a := left - c
  let b := left - u
  have ha : a + len ≤ d - c := by dsimp only [a, len, left, right]; omega
  have hb : b + len ≤ v - u := by dsimp only [b, len, left, right]; omega
  let eB := intervalDifferenceNaturalEquiv (u := c) (v := d) huv hv
  let ηrN : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} → Fin q :=
    fun j ↦ ηr (eB j)
  let ηcN : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} → Fin q :=
    fun j ↦ ηc (eB j)
  have hBsite (j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)}) :
      (⟨(eB j).val, (Finset.mem_sdiff.mp (eB j).property).1⟩ : ↥J) = eJ j.val := by
    apply Subtype.ext
    exact intervalDifferenceNaturalEquiv_apply_val (u := c) (v := d) huv hv j
  have hmatch (η : FiniteProduct.Configuration β (J \ E))
      (σ : Fin (v - u) → Fin q) :
      (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ σ j.val) =
          (fun j ↦ η (eB j)) ↔ (new (toJ σ)).1 = η := by
    constructor
    · intro h
      funext z
      obtain ⟨j, rfl⟩ := eB.surjective z
      rw [FiniteProduct.changingNewMiddleConfigEquiv_apply_fst]
      change σ (eJ.symm
        ⟨(eB j).val, (Finset.mem_sdiff.mp (eB j).property).1⟩) = η (eB j)
      rw [hBsite j, eJ.symm_apply_apply]
      exact congrFun h j
    · intro h
      funext j
      have hj := congrFun h (eB j)
      rw [FiniteProduct.changingNewMiddleConfigEquiv_apply_fst] at hj
      change σ (eJ.symm
        ⟨(eB j).val, (Finset.mem_sdiff.mp (eB j).property).1⟩) = η (eB j) at hj
      rw [hBsite j, eJ.symm_apply_apply] at hj
      exact hj
  let z0 : Fin q := ⟨0, hq⟩
  let core0 : FiniteProduct.Configuration β (E ∩ J) := fun _ ↦ z0
  let fixed (α : FiniteProduct.Configuration β (E \ J)) : Fin (d - c) → Fin q :=
    fun i ↦ old.symm (α, core0) (eE i)
  have hfill (α : FiniteProduct.Configuration β (E \ J))
      (σ : Fin (v - u) → Fin q) :
      toE (insertInterval a (fixed α)
        (fun r : Fin len ↦ σ ⟨b + r.val, by omega⟩)) =
        old.symm (α, (new (toJ σ)).2) := by
    funext z
    have hnat : a ≤ (eE.symm z).val ∧ (eE.symm z).val < a + len ↔ z.val ∈ J := by
      have hm := intervalShiftOrderIso_mem_overlap (u := u) (v := v) hcd hd (eE.symm z)
      simpa only [a, len, left, right, eE, J, max_comm c u, min_comm d v,
        (intervalShiftOrderIso hcd hd).apply_symm_apply z] using hm.symm
    by_cases hz : z.val ∈ J
    · rw [FiniteProduct.changingOldMiddleConfigEquiv_symm_apply_of_mem β E J
        α ((new (toJ σ)).2) z hz]
      rw [FiniteProduct.changingNewMiddleConfigEquiv_apply_snd]
      change insertInterval a (fixed α)
          (fun r : Fin len ↦ σ ⟨b + r.val, by omega⟩) (eE.symm z) =
        σ (eJ.symm ⟨z.val, hz⟩)
      simp only [insertInterval, dite_eq_left (hnat.mpr hz)]
      apply congrArg σ
      apply Fin.ext
      change b + ((z.val.val - c) - a) = z.val.val - u
      have hE := mem_interval.mp z.property
      have hJ := mem_interval.mp hz
      dsimp only [a, b, left]
      omega
    · rw [FiniteProduct.changingOldMiddleConfigEquiv_symm_apply_of_notMem β E J
        α ((new (toJ σ)).2) z hz]
      change insertInterval a (fixed α)
          (fun r : Fin len ↦ σ ⟨b + r.val, by omega⟩) (eE.symm z) =
        α ⟨z.val, Finset.mem_sdiff.mpr ⟨z.property, hz⟩⟩
      simp only [insertInterval, dite_eq_right (fun h ↦ hz (hnat.mp h))]
      change old.symm (α, core0) (eE (eE.symm z)) = _
      rw [eE.apply_symm_apply]
      exact FiniteProduct.changingOldMiddleConfigEquiv_symm_apply_of_notMem
        β E J α core0 z hz
  let Wslice : Matrix (Fin (v - u) → Fin q) (Fin (v - u) → Fin q) ℂ := fun σ τ ↦
    if (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ σ j.val) = ηrN ∧
        (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ τ j.val) = ηcN
    then Vnat (insertInterval a (fixed αr) (fun r : Fin len ↦ σ ⟨b + r.val, by omega⟩))
      (insertInterval a (fixed αc) (fun r : Fin len ↦ τ ⟨b + r.val, by omega⟩)) else 0
  have hslice : IsOpenMPS (v - u) (q * q) (max 1 D) (fun x ↦
      Wslice (fun j ↦ (finProdFinEquiv.symm (x j)).1)
        (fun j ↦ (finProdFinEquiv.symm (x j)).2)) :=
    isOpenMPS_matrix_intervalSlice_extend_by_configuration
      Vnat hVnat a ha (fixed αr) (fixed αc) b hb ηrN ηcN
  have hW : (fun (σ τ : Fin (v - u) → Fin q) ↦ Wphys (toJ σ) (toJ τ)) = Wslice := by
    funext σ τ
    change Matrix.single ηr ηc (1 : ℂ) ((new (toJ σ)).1) ((new (toJ τ)).1) *
        Vphys (old.symm (αr, (new (toJ σ)).2)) (old.symm (αc, (new (toJ τ)).2)) =
      (if (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ σ j.val) = ηrN ∧
          (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ τ j.val) = ηcN
      then Vphys
        (toE (insertInterval a (fixed αr) (fun r : Fin len ↦ σ ⟨b + r.val, by omega⟩)))
        (toE (insertInterval a (fixed αc) (fun r : Fin len ↦ τ ⟨b + r.val, by omega⟩))) else 0)
    rw [hfill αr σ, hfill αc τ]
    simp only [Matrix.single_apply, ite_mul, one_mul, zero_mul]
    by_cases h : ηr = (new (toJ σ)).1 ∧ ηc = (new (toJ τ)).1
    · have hn :
          (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ σ j.val) = ηrN ∧
          (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ τ j.val) = ηcN :=
        ⟨(hmatch ηr σ).mpr h.1.symm, (hmatch ηc τ).mpr h.2.symm⟩
      rw [ite_eq_left h, ite_eq_left hn]
    · have hn : ¬(
          (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ σ j.val) = ηrN ∧
          (fun j : {j : Fin (v - u) // ¬(b ≤ j.val ∧ j.val < b + len)} ↦ τ j.val) = ηcN) := by
        intro hn
        exact h ⟨((hmatch ηr σ).mp hn.1).symm, ((hmatch ηc τ).mp hn.2).symm⟩
      rw [ite_eq_right h, ite_eq_right hn]
  rw [← hW] at hslice
  exact hslice

/-- The actual regional change of interval has one prescribed family with
natural MPO bounds and an exact cardinality. Exterior coefficients are
supplied only afterwards. Positivity and the interval containments are
explicit; the overlap may have length zero. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333, without a sharp bond,
algorithmic, or complete source-theorem assertion. -/
theorem changingRegionalMiddleFamily_mpo_and_global_decomposition
    {T q c d u v : ℕ} {ι : Type*} [Fintype ι]
    (hq : 0 < q) (hcd : c ≤ d) (hd : d ≤ T) (huv : u ≤ v) (hv : v ≤ T)
    (hover : max c u ≤ min d v)
    (V : ι → Matrix (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d))
      (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d)) ℂ)
    (D : ι → ℕ)
    (hV : ∀ t, let eE := intervalShiftOrderIso hcd hd
      IsOpenMPS (d - c) (q * q) (D t) (fun x ↦
        V t (fun z ↦ (finProdFinEquiv.symm (x (eE.symm z))).1)
          (fun z ↦ (finProdFinEquiv.symm (x (eE.symm z))).2))) :
    let β := fun _ : Fin T ↦ Fin q
    let E := interval T c d
    let J := interval T u v
    let A := E \ J
    let B := J \ E
    let I := ι × (FiniteProduct.Configuration β A × FiniteProduct.Configuration β A) ×
      (FiniteProduct.Configuration β B × FiniteProduct.Configuration β B)
    let W := FiniteProduct.changingRegionalMiddleFamily β E J V
    let eJ := intervalShiftOrderIso huv hv
    Fintype.card I = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) ∧
      (∀ r : I, IsOpenMPS (v - u) (q * q) (max 1 (D r.1)) (fun x ↦
        W r (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).1)
          (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).2))) ∧
      ∀ M : ι → Matrix (FiniteProduct.Configuration β Eᶜ)
          (FiniteProduct.Configuration β Eᶜ) ℂ,
        ∃ Mnew : I → Matrix (FiniteProduct.Configuration β Jᶜ)
            (FiniteProduct.Configuration β Jᶜ) ℂ,
          (∑ t, M t ⊗ₖ V t).submatrix
            ((FiniteProduct.splitEquiv β E).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv β E).trans (Equiv.prodComm _ _)) =
          (∑ r, Mnew r ⊗ₖ W r).submatrix
            ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)) := by
  let β := fun _ : Fin T ↦ Fin q
  let E := interval T c d
  let J := interval T u v
  let A := E \ J
  let B := J \ E
  let I := ι × (FiniteProduct.Configuration β A × FiniteProduct.Configuration β A) ×
    (FiniteProduct.Configuration β B × FiniteProduct.Configuration β B)
  let W := FiniteProduct.changingRegionalMiddleFamily β E J V
  let eJ := intervalShiftOrderIso huv hv
  have hcard : Fintype.card I = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) := by
    calc
      Fintype.card I = Fintype.card ι *
          Fintype.card (FiniteProduct.Configuration β A) ^ 2 *
          Fintype.card (FiniteProduct.Configuration β B) ^ 2 :=
        Matrix.card_exchangedMiddleFamily_index
      _ = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) := by
        simp only [FiniteProduct.Configuration, β, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_coe, ← pow_mul]
        rw [Nat.mul_assoc, ← pow_add]
        rw [show A.card * 2 + B.card * 2 = 2 * A.card + 2 * B.card by omega]
  have hW : ∀ r : I, IsOpenMPS (v - u) (q * q) (max 1 (D r.1)) (fun x ↦
      W r (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).1)
        (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).2)) := by
    intro r
    have hfactor := isOpenMPS_changingRegionalMiddleFactor hq hcd hd huv hv hover
      (V r.1) (hV r.1) r.2.1.1 r.2.1.2 r.2.2.1 r.2.2.2
    convert hfactor using 1
    funext x
    simp only [W, FiniteProduct.changingRegionalMiddleFamily, β, E, J, eJ,
      Matrix.exchangedMiddleFamily, Matrix.exchangedMiddleFactor, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.single_apply, Equiv.symm_symm]
    split_ifs <;> rfl
  refine ⟨hcard, hW, ?_⟩
  intro M
  exact FiniteProduct.exists_changingRegional_exterior_family β E J V M

end TNLean.MPS.AreaLaw

end
