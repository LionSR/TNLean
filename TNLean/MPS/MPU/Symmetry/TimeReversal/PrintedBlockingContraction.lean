/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.TimeReversal.PrintedBlockingGates
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardFormOpenWord
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardFormCircuit
import QICLean.Algebra.Matrix.MatrixCyclicPathSum

/-!
# Open contraction of the printed blocking circuits

Source: arXiv:1703.09188, StandardForm, lines 603--617, and
`prop:sigma1-and-sigma2-equal`, lines 1689--1700.

**Scope restriction (square supplied gates):** The supplied-form applications
start with both intermediate spaces equal to the original spin space.
Reduction from a general rectangular standard form is separate; see
`docs/paper-gaps/mpu_printed_blocking_square_scope.tex`.
-/

open scoped Matrix BigOperators
open Matrix QuantumCircuit

namespace MPOTensor

private theorem consecutive_pair_product_apply {d n p m : ℕ} (hp : p + 2 * m ≤ n)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (x y : Fin n → Fin d) :
    (List.ofFn fun j : Fin m ↦ printedPairGate n (p + 2 * j.val)
      (by have := j.isLt; omega) A).prod x y =
      if ∀ i : Fin n, i.val < p ∨ p + 2 * m ≤ i.val → x i = y i then
        ∏ j : Fin m, A (x ⟨p + 2 * j.val, by have := j.isLt; omega⟩,
          x ⟨p + 2 * j.val + 1, by have := j.isLt; omega⟩)
          (y ⟨p + 2 * j.val, by have := j.isLt; omega⟩,
            y ⟨p + 2 * j.val + 1, by have := j.isLt; omega⟩)
      else 0 := by
  let e (j : Fin m) (t : Fin 2) : Fin n :=
    ⟨p + 2 * j.val + t.val, by have := j.isLt; have := t.isLt; omega⟩
  have he (j : Fin m) : Function.Injective (e j) := by
    intro t t' htt
    apply Fin.ext
    have h := congrArg Fin.val htt
    dsimp only [e] at h
    omega
  have hd (j j' : Fin m) (hne : j ≠ j') : Disjoint (Set.range (e j)) (Set.range (e j')) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨t, rfl⟩ ⟨t', hh⟩
    have h := congrArg Fin.val hh
    dsimp only [e] at h
    have := t.isLt
    have := t'.isLt
    apply hne
    apply Fin.ext
    omega
  let B := Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
    (finTwoArrowEquiv (Fin d)).symm A
  have hg (j : Fin m) : printedPairGate n (p + 2 * j.val) (by have := j.isLt; omega) A =
      ManyBody.placeAlong (X := fun _ ↦ Fin d) ⟨e j, he j⟩ B := rfl
  have hc : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).Pairwise
      (Function.onFun Commute fun j ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin d) ⟨e j, he j⟩ B) := by
    intro j _ j' _ hne
    refine ManyBody.commute_placeAlong_of_disjoint _ ?_ _ _
    rw [← Finset.disjoint_coe]
    simpa using hd j j' hne
  have hprod : (List.ofFn fun j : Fin m ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin d) ⟨e j, he j⟩ B).prod =
      Finset.univ.noncommProd
        (fun j ↦ ManyBody.placeAlong (X := fun _ ↦ Fin d) ⟨e j, he j⟩ B) hc := by
    have hc' : ((List.finRange m).toFinset : Set (Fin m)).Pairwise
        (Function.onFun Commute fun j ↦
          ManyBody.placeAlong (X := fun _ ↦ Fin d) ⟨e j, he j⟩ B) := by
      simpa only [List.toFinset_finRange] using hc
    simpa only [List.toFinset_finRange, List.ofFn_eq_map] using
      (Finset.noncommProd_toFinset (List.finRange m) _ hc' (List.nodup_finRange m)).symm
  simp_rw [hg]
  rw [hprod, noncommProd_placeAlong_apply e he (fun _ ↦ B) _
    (fun j _ j' _ hne ↦ hd j j' hne)]
  have hout : (∀ i : Fin n, (∀ j ∈ (Finset.univ : Finset (Fin m)), ∀ t, e j t ≠ i) →
      x i = y i) ↔ ∀ i : Fin n, i.val < p ∨ p + 2 * m ≤ i.val → x i = y i := by
    constructor
    · intro h i hi
      apply h i
      intro j _ t ht
      have hval := congrArg Fin.val ht
      dsimp only [e] at hval
      have := j.isLt
      have := t.isLt
      rcases hi with hi | hi <;> omega
    · intro h i hi
      apply h i
      by_contra hnot
      have hr : p ≤ i.val ∧ i.val < p + 2 * m := by omega
      let j : Fin m := ⟨(i.val - p) / 2, by omega⟩
      let t : Fin 2 := ⟨(i.val - p) % 2, by omega⟩
      apply hi j (Finset.mem_univ _) t
      apply Fin.ext
      dsimp only [e, j, t]
      omega
  by_cases hx : ∀ i : Fin n, (∀ j ∈ (Finset.univ : Finset (Fin m)), ∀ t, e j t ≠ i) →
      x i = y i
  · rw [ite_eq_left hx, ite_eq_left (hout.mp hx)]
    apply Finset.prod_congr rfl
    intro j _
    rfl
  · rw [ite_eq_right hx, ite_eq_right (fun h ↦ hx (hout.mpr h))]

/-- The fully covering unshifted layer is the tensor product of its pair
entries, in original-spin order. Source: arXiv:1703.09188, lines 1689--1694. -/
theorem printedCellLayer_full_apply {d k : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x y : Fin (2 * k) → Fin d) :
    printedCellLayer k 0 k (by omega) A x y =
      ∏ j : Fin k, A (x ⟨2 * j.val, by have := j.isLt; omega⟩,
        x ⟨2 * j.val + 1, by have := j.isLt; omega⟩)
        (y ⟨2 * j.val, by have := j.isLt; omega⟩,
          y ⟨2 * j.val + 1, by have := j.isLt; omega⟩) := by
  have hcov : ∀ i : Fin (2 * k), i.val < 0 ∨ 0 + 2 * k ≤ i.val → x i = y i := by
    intro i hi
    have := i.isLt
    omega
  have h := consecutive_pair_product_apply (n := 2 * k) (p := 0) (m := k)
    (by omega) A x y
  rw [ite_eq_left hcov] at h
  have hl : printedCellLayer k 0 k (by omega) A =
      (List.ofFn fun j : Fin k ↦ printedPairGate (2 * k) (0 + 2 * j.val)
        (by have := j.isLt; omega) A).prod := by
    unfold printedCellLayer
    apply printedPairGate_prod_congr
    intro j
    omega
  rw [hl, h]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Nat.zero_add]

/-- The internal shifted layer fixes the first and last original spins;
its remaining entries are the product of the shifted pair entries.
Source: arXiv:1703.09188, lines 1689--1694. -/
theorem printedLinkLayer_full_apply {d k : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x y : Fin (2 * (k + 1)) → Fin d) :
    printedLinkLayer (k + 1) 0 k (by omega) A x y =
      if x ⟨0, by omega⟩ = y ⟨0, by omega⟩ ∧
          x ⟨2 * k + 1, by omega⟩ = y ⟨2 * k + 1, by omega⟩ then
        ∏ j : Fin k, A (x ⟨2 * j.val + 1, by have := j.isLt; omega⟩,
          x ⟨2 * j.val + 2, by have := j.isLt; omega⟩)
          (y ⟨2 * j.val + 1, by have := j.isLt; omega⟩,
            y ⟨2 * j.val + 2, by have := j.isLt; omega⟩)
      else 0 := by
  have hout : (∀ i : Fin (2 * (k + 1)), i.val < 1 ∨ 1 + 2 * k ≤ i.val → x i = y i) ↔
      x ⟨0, by omega⟩ = y ⟨0, by omega⟩ ∧
        x ⟨2 * k + 1, by omega⟩ = y ⟨2 * k + 1, by omega⟩ := by
    constructor
    · intro h
      constructor
      · exact h ⟨0, by omega⟩ (Or.inl (by change 0 < 1; omega))
      · exact h ⟨2 * k + 1, by omega⟩ (Or.inr (by change 1 + 2 * k ≤ 2 * k + 1; omega))
    · rintro ⟨hfirst, hlast⟩ i hi
      have hv := i.isLt
      rcases hi with hi | hi
      · have he : i = ⟨0, by omega⟩ := by ext; dsimp; omega
        simpa only [he] using hfirst
      · have he : i = ⟨2 * k + 1, by omega⟩ := by ext; dsimp; omega
        simpa only [he] using hlast
  have h := consecutive_pair_product_apply (n := 2 * (k + 1)) (p := 1) (m := k)
    (by omega) A x y
  simp only [hout] at h
  have hl : printedLinkLayer (k + 1) 0 k (by omega) A =
      (List.ofFn fun j : Fin k ↦ printedPairGate (2 * (k + 1)) (1 + 2 * j.val)
        (by have := j.isLt; omega) A).prod := by
    unfold printedLinkLayer
    apply printedPairGate_prod_congr
    intro j
    omega
  rw [hl, h]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have ha : 1 + 2 * j.val = 2 * j.val + 1 := by omega
  simp only [ha]

/-- The open finite network through the first supplied left half factor,
all unshifted gates and internal shifted gates, and the last supplied
right half factor. Virtual endpoints remain free.
Source: arXiv:1703.09188, StandardForm, lines 603--617 and 1689--1698. -/
noncomputable def printedOpenGateContraction {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (i j : Fin (k + 1) → Fin d × Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  fun α γ ↦ ∑ h : Fin (k + 1) → Fin d × Fin d,
    S.X₂ (α, (i 0).1) (h 0).1 *
      (∏ p : Fin k, v ((i p.castSucc).2, (i p.succ).1)
        ((h p.castSucc).2, (h p.succ).1)) *
      (∏ p : Fin (k + 1), u (h p) (j p)) *
      S.X₁ ((i (Fin.last k)).2, γ) (h (Fin.last k)).2

private theorem printedOpenGateContraction_succ {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (i j : Fin (k + 1 + 1) → Fin d × Fin d) :
    printedOpenGateContraction S i j =
      W (finProdFinEquiv (i 0), finProdFinEquiv (j 0)) *
        printedOpenGateContraction S (i ∘ Fin.succ) (j ∘ Fin.succ) := by
  ext α γ
  symm
  simp only [Matrix.mul_apply, S.W_apply, Equiv.symm_apply_apply,
    printedOpenGateContraction]
  conv_rhs =>
    rw [Matrix.sum_fin_cons]
    simp only [Fintype.sum_prod_type, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.castSucc_zero, ← Fin.succ_castSucc, ← Fin.succ_last,
      Function.comp_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_last_two_first_four]
  refine Finset.sum_congr₂ fun t _ s _ ↦ ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [S.v_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  simp only [Function.comp_apply, Fin.prod_univ_succ]
  ring

/-- The open product of any positive number of supplied standard-form
letters is exactly the printed internal gate contraction. No periodic
trace or canonical-presentation hypothesis is used.
Source: arXiv:1703.09188, StandardForm, lines 603--617 and 1689--1698. -/
theorem TwoSiteStandardFormData.evalWord_eq_printedOpenGateContraction {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (i j : Fin (k + 1) → Fin d × Fin d) :
    evalWord W (List.ofFn fun p ↦ finProdFinEquiv (i p))
        (List.ofFn fun p ↦ finProdFinEquiv (j p)) = printedOpenGateContraction S i j := by
  induction k with
  | zero =>
    ext α γ
    simp [printedOpenGateContraction, Matrix.sum_fin_cons, List.ofFn_succ,
      evalWord_cons, evalWord_nil, Fintype.sum_prod_type, S.W_apply]
  | succ k ih =>
    have hi : (List.ofFn fun p ↦ finProdFinEquiv (i p)) =
        finProdFinEquiv (i 0) ::
          List.ofFn (fun p : Fin (k + 1) ↦ finProdFinEquiv (i p.succ)) := List.ofFn_succ
    have hj : (List.ofFn fun p ↦ finProdFinEquiv (j p)) =
        finProdFinEquiv (j 0) ::
          List.ofFn (fun p : Fin (k + 1) ↦ finProdFinEquiv (j p.succ)) := List.ofFn_succ
    rw [hi, hj, evalWord_cons]
    exact (congrArg (W (finProdFinEquiv (i 0), finProdFinEquiv (j 0)) * ·)
      (ih (i ∘ Fin.succ) (j ∘ Fin.succ))).trans (printedOpenGateContraction_succ S i j).symm

/-- Actual arbitrary positive physical blocking is the open printed gate
network with its original virtual endpoints. The physical blocked indices
are decoded in their existing order.
Source: arXiv:1703.09188, lines 1689--1698. -/
theorem TwoSiteStandardFormData.blockTensor_eq_printedOpenGateContraction {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (I J : Fin (Kraus.blockPhysDim (d * d) (k + 1))) :
    blockTensor W (k + 1) (I, J) = printedOpenGateContraction S
      (fun p ↦ finProdFinEquiv.symm (Kraus.decodeBlock (d * d) (k + 1) I p))
      (fun p ↦ finProdFinEquiv.symm (Kraus.decodeBlock (d * d) (k + 1) J p)) := by
  rw [blockTensor_apply]
  change evalWord W (List.ofFn (Kraus.decodeBlock (d * d) (k + 1) I))
    (List.ofFn (Kraus.decodeBlock (d * d) (k + 1) J)) = _
  simpa only [Equiv.apply_symm_apply] using S.evalWord_eq_printedOpenGateContraction
    (fun p ↦ finProdFinEquiv.symm (Kraus.decodeBlock (d * d) (k + 1) I p))
    (fun p ↦ finProdFinEquiv.symm (Kraus.decodeBlock (d * d) (k + 1) J p))

private noncomputable abbrev spinPairEquiv (d k : ℕ) :
    (Fin k → Fin d × Fin d) ≃ (Fin (2 * k) → Fin d) :=
  (twoSiteChainConfigEquiv d k).trans
    (Equiv.arrowCongr (finCongr (Nat.mul_comm k 2)) (Equiv.refl (Fin d)))

private theorem spinPairEquiv_apply {d k : ℕ} (z : Fin k → Fin d × Fin d)
    (a : Fin k) (b : Fin 2) :
    spinPairEquiv d k z ⟨2 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩ =
      (finTwoArrowEquiv (Fin d)).symm (z a) b := by
  have hr : finProdFinEquiv.symm
      (⟨2 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩ : Fin (k * 2)) =
      (a, b) := by
    apply finProdFinEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    change 2 * a.val + b.val = b.val + 2 * a.val
    omega
  simp [spinPairEquiv, twoSiteChainConfigEquiv, twoSitePairConfigEquiv,
    Kraus.blockedConfigEquiv, twoSiteBlockEquiv, Equiv.arrowCongr,
    Kraus.blockConfigEquiv_apply, Function.comp_apply, hr]

private theorem spinPairEquiv_even {d k : ℕ} (z : Fin k → Fin d × Fin d) (a : Fin k) :
    spinPairEquiv d k z ⟨2 * a.val, by have := a.isLt; omega⟩ = (z a).1 := by
  simpa [finTwoArrowEquiv] using spinPairEquiv_apply z a 0

private theorem spinPairEquiv_odd {d k : ℕ} (z : Fin k → Fin d × Fin d) (a : Fin k) :
    spinPairEquiv d k z ⟨2 * a.val + 1, by have := a.isLt; omega⟩ = (z a).2 := by
  simpa [finTwoArrowEquiv] using spinPairEquiv_apply z a 1

private theorem cell_pair_apply {d k : ℕ}
    (u : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (i j : Fin k → Fin d × Fin d) :
    printedCellLayer k 0 k (by omega) u (spinPairEquiv d k i) (spinPairEquiv d k j) =
      ∏ p : Fin k, u (i p) (j p) := by
  rw [printedCellLayer_full_apply]
  apply Finset.prod_congr rfl
  intro p _
  simp only [spinPairEquiv_even, spinPairEquiv_odd, Prod.eta]

private theorem link_pair_apply {d k : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (i h : Fin (k + 1) → Fin d × Fin d) :
    printedLinkLayer (k + 1) 0 k (by omega) v
        (spinPairEquiv d (k + 1) i) (spinPairEquiv d (k + 1) h) =
      if (i 0).1 = (h 0).1 ∧ (i (Fin.last k)).2 = (h (Fin.last k)).2 then
        ∏ p : Fin k, v ((i p.castSucc).2, (i p.succ).1)
          ((h p.castSucc).2, (h p.succ).1) else 0 := by
  have hfirst (z : Fin (k + 1) → Fin d × Fin d) :
      spinPairEquiv d (k + 1) z ⟨0, by omega⟩ = (z 0).1 := by
    simpa only [Fin.val_zero, Nat.mul_zero] using spinPairEquiv_even z 0
  have hlast (z : Fin (k + 1) → Fin d × Fin d) :
      spinPairEquiv d (k + 1) z ⟨2 * k + 1, by omega⟩ = (z (Fin.last k)).2 :=
    spinPairEquiv_odd z (Fin.last k)
  rw [printedLinkLayer_full_apply, hfirst, hfirst, hlast, hlast]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  have hp (z : Fin (k + 1) → Fin d × Fin d) :
      spinPairEquiv d (k + 1) z ⟨2 * p.val + 1, by have := p.isLt; omega⟩ =
        (z p.castSucc).2 := spinPairEquiv_odd z p.castSucc
  have hn (z : Fin (k + 1) → Fin d × Fin d) :
      spinPairEquiv d (k + 1) z ⟨2 * p.val + 2, by have := p.isLt; omega⟩ =
        (z p.succ).1 := by
    have h := spinPairEquiv_even z p.succ
    simpa only [Fin.val_succ, Nat.mul_add, Nat.mul_one] using h
  rw [hp, hn, hp, hn]

private theorem input_pair_apply {d k : ℕ}
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (i j : Fin (k + 1) → Fin d × Fin d) :
    printedInputCircuit (k + 1) (by omega) u v
        (spinPairEquiv d (k + 1) i) (spinPairEquiv d (k + 1) j) =
      ∑ h : Fin (k + 1) → Fin d × Fin d,
        (if (i 0).1 = (h 0).1 ∧ (i (Fin.last k)).2 = (h (Fin.last k)).2 then
          ∏ p : Fin k, v ((i p.castSucc).2, (i p.succ).1)
            ((h p.castSucc).2, (h p.succ).1) else 0) *
          ∏ p : Fin (k + 1), u (h p) (j p) := by
  have hl : printedLinkLayer (k + 1) 0 (k + 1 - 1) (by omega) v =
      printedLinkLayer (k + 1) 0 k (by omega) v := by
    congr 1
  unfold printedInputCircuit
  rw [hl, Matrix.mul_apply]
  rw [← Fintype.sum_equiv (spinPairEquiv d (k + 1))
    (fun h ↦ printedLinkLayer (k + 1) 0 k (by omega) v
      (spinPairEquiv d (k + 1) i) (spinPairEquiv d (k + 1) h) *
        printedCellLayer (k + 1) 0 (k + 1) (by omega) u
          (spinPairEquiv d (k + 1) h) (spinPairEquiv d (k + 1) j))
    _ (fun _ ↦ rfl)]
  simp only [link_pair_apply, cell_pair_apply]

private def boundaryPairConfig {d k : ℕ} (i : Fin (k + 1) → Fin d × Fin d)
    (a b : Fin d) : Fin (k + 1) → Fin d × Fin d :=
  fun p ↦ (if p = 0 then a else (i p).1, if p = Fin.last k then b else (i p).2)

private theorem boundary_input_contraction {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (i j : Fin (k + 1) → Fin d × Fin d)
    (α γ : Fin D) :
    (∑ a : Fin d, ∑ b : Fin d,
      S.X₂ (α, (i 0).1) a *
        printedInputCircuit (k + 1) (by omega) u v
          (spinPairEquiv d (k + 1) (boundaryPairConfig i a b))
          (spinPairEquiv d (k + 1) j) * S.X₁ ((i (Fin.last k)).2, γ) b) =
      printedOpenGateContraction S i j α γ := by
  have hb0 (a b : Fin d) : (boundaryPairConfig i a b 0).1 = a := by
    simp only [boundaryPairConfig, ite_true]
  have hblast (a b : Fin d) : (boundaryPairConfig i a b (Fin.last k)).2 = b := by
    simp only [boundaryPairConfig, ite_true]
  have hv (a b : Fin d) (h : Fin (k + 1) → Fin d × Fin d) :
      (∏ p : Fin k, v ((boundaryPairConfig i a b p.castSucc).2,
        (boundaryPairConfig i a b p.succ).1) ((h p.castSucc).2, (h p.succ).1)) =
      ∏ p : Fin k, v ((i p.castSucc).2, (i p.succ).1)
        ((h p.castSucc).2, (h p.succ).1) := by
    apply Finset.prod_congr rfl
    intro p _
    have hlast : p.castSucc ≠ Fin.last k := by
      intro hh
      have := congrArg Fin.val hh
      have := p.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at *
      omega
    have hfirst : p.succ ≠ 0 := Fin.succ_ne_zero p
    simp only [boundaryPairConfig, hlast, hfirst, ite_false]
  simp only [input_pair_apply, hb0, hblast, hv]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  unfold printedOpenGateContraction
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]
  simp only [ite_and, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem spinPairEquiv_boundary {d k : ℕ}
    (i : Fin (k + 1) → Fin d × Fin d) (a b : Fin d) :
    spinPairEquiv d (k + 1) (boundaryPairConfig i a b) =
      fun q ↦ if q.val = 0 then a else if q.val = 2 * k + 1 then b else
        spinPairEquiv d (k + 1) i q := by
  funext q
  let p : Fin (k + 1) := ⟨q.val / 2, by have := q.isLt; omega⟩
  let t : Fin 2 := ⟨q.val % 2, by omega⟩
  have hq : q = ⟨2 * p.val + t.val, by have := p.isLt; have := t.isLt; omega⟩ := by
    apply Fin.ext
    dsimp only [p, t]
    omega
  rw [hq]
  by_cases ht : t.val = 0
  · have ht' : t = 0 := Fin.ext ht
    simp only [ht', Fin.val_zero, Nat.add_zero]
    rw [spinPairEquiv_even, spinPairEquiv_even]
    simp only [boundaryPairConfig, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    split_ifs <;> simp_all
    omega
  · have ht' : t = 1 := by
      apply Fin.ext
      have := t.isLt
      change t.val = 1
      omega
    simp only [ht', Fin.val_one]
    rw [spinPairEquiv_odd, spinPairEquiv_odd]
    simp only [boundaryPairConfig, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    split_ifs <;> simp_all

/-- The actual open word is the literal printed input circuit, contracted
only with the original two virtual endpoint factors. The placed circuit
keeps every original spin and changes only its two exterior output values
inside this boundary contraction.
Source: arXiv:1703.09188, StandardForm, lines 603--617 and 1689--1698. -/
theorem TwoSiteStandardFormData.evalWord_eq_printedInputCircuit {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (i j : Fin (k + 1) → Fin d × Fin d)
    (α γ : Fin D) :
    let e := (twoSiteChainConfigEquiv d (k + 1)).trans
      (Equiv.arrowCongr (finCongr (Nat.mul_comm (k + 1) 2)) (Equiv.refl (Fin d)))
    evalWord W (List.ofFn fun p ↦ finProdFinEquiv (i p))
        (List.ofFn fun p ↦ finProdFinEquiv (j p)) α γ =
      ∑ a : Fin d, ∑ b : Fin d, S.X₂ (α, e i ⟨0, by omega⟩) a *
        printedInputCircuit (k + 1) (by omega) u v
          (fun p ↦ if p.val = 0 then a else if p.val = 2 * k + 1 then b else e i p)
          (e j) *
          S.X₁ (e i ⟨2 * k + 1, by omega⟩, γ) b := by
  rw [S.evalWord_eq_printedOpenGateContraction]
  have h := (boundary_input_contraction S i j α γ).symm
  simp only [spinPairEquiv_boundary] at h
  have hf : spinPairEquiv d (k + 1) i ⟨0, by omega⟩ = (i 0).1 := by
    simpa only [Fin.val_zero, Nat.mul_zero] using spinPairEquiv_even i 0
  have hl : spinPairEquiv d (k + 1) i ⟨2 * k + 1, by omega⟩ =
      (i (Fin.last k)).2 := spinPairEquiv_odd i (Fin.last k)
  simpa only [hf, hl] using h

end MPOTensor
