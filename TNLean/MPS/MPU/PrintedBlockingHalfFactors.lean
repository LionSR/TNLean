/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.PrintedBlockingContraction

/-!
# Half-word coordinates and the printed blocked half factors

Source: arXiv:1703.09188, StandardForm, lines 603--617, and the
arbitrary-blocking representatives, lines 1689--1698.

**Scope restriction (square supplied gates):** The supplied-form applications
start with both intermediate spaces equal to the original spin space.
Reduction from a general rectangular standard form is separate; see
`docs/paper-gaps/mpu_printed_blocking_square_scope.tex`.
-/

open Matrix
open scoped BigOperators

namespace MPOTensor

/-- Concatenate two decoded half words into the original ordered spins.
Source: arXiv:1703.09188, lines 1689--1698. -/
noncomputable def printedHalfWordEquiv (d k : ℕ) :
    (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ≃
      (Fin (2 * k) → Fin d) :=
  ((Kraus.decodeBlockEquiv d k).prodCongr (Kraus.decodeBlockEquiv d k)).trans
    ((Fin.appendEquiv k k).trans
      (Equiv.arrowCongr (finCongr (by omega : k + k = 2 * k)) (Equiv.refl (Fin d))))

private theorem halfWord_left {d k : ℕ}
    (a b : Fin (Kraus.blockPhysDim d k)) (p : Fin k) :
    printedHalfWordEquiv d k (a, b) ⟨p.val, by have := p.isLt; omega⟩ =
      Kraus.decodeBlock d k a p := by
  change Fin.append (Kraus.decodeBlock d k a) (Kraus.decodeBlock d k b)
    (Fin.castAdd k p) = _
  exact Fin.addCases_left p

private theorem halfWord_right {d k : ℕ}
    (a b : Fin (Kraus.blockPhysDim d k)) (p : Fin k) :
    printedHalfWordEquiv d k (a, b) ⟨k + p.val, by have := p.isLt; omega⟩ =
      Kraus.decodeBlock d k b p := by
  change Fin.append (Kraus.decodeBlock d k a) (Kraus.decodeBlock d k b)
    (Fin.natAdd k p) = _
  exact Fin.addCases_right p

/-- The actual printed input circuit in the two ordered half-word bases.
Source: arXiv:1703.09188, lines 1689--1694. -/
noncomputable def printedBlockedInputGate {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ :=
  Matrix.reindex (printedHalfWordEquiv d k).symm (printedHalfWordEquiv d k).symm
    (printedInputCircuit k hk u v)

/-- The centered output circuit in the same two ordered half-word bases.
Source: arXiv:1703.09188, lines 1695--1698. -/
noncomputable def printedBlockedOutputGate {d : ℕ} (k : ℕ) (hk : 0 < k)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ :=
  Matrix.reindex (printedHalfWordEquiv d k).symm (printedHalfWordEquiv d k).symm
    (printedOutputCircuit k hk v)

/-- Extend the supplied left half factor by identity on its following
spectator spins. Source: arXiv:1703.09188, lines 1689--1698. -/
noncomputable def printedBlockedHalfLeft {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin D × Fin (Kraus.blockPhysDim d (k + 1)))
      (Fin (Kraus.blockPhysDim d (k + 1))) ℂ := fun i t ↦
  if Fin.tail (Kraus.decodeBlock d (k + 1) i.2) =
      Fin.tail (Kraus.decodeBlock d (k + 1) t) then
    S.X₂ (i.1, Kraus.decodeBlock d (k + 1) i.2 0)
      (Kraus.decodeBlock d (k + 1) t 0) else 0

/-- Extend the supplied right half factor by identity on its preceding
spectator spins. Source: arXiv:1703.09188, lines 1689--1698. -/
noncomputable def printedBlockedHalfRight {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin (Kraus.blockPhysDim d (k + 1)) × Fin D)
      (Fin (Kraus.blockPhysDim d (k + 1))) ℂ := fun i s ↦
  if Fin.init (Kraus.decodeBlock d (k + 1) i.1) =
      Fin.init (Kraus.decodeBlock d (k + 1) s) then
    S.X₁ (Kraus.decodeBlock d (k + 1) i.1 (Fin.last k), i.2)
      (Kraus.decodeBlock d (k + 1) s (Fin.last k)) else 0

/-- The two half-word versions of the literal circuits remain unitary.
Source: arXiv:1703.09188, lines 1689--1698. -/
theorem printedBlockedGates_mem_unitaryGroup {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hv : v ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
    printedBlockedInputGate k hk u v ∈ Matrix.unitaryGroup
        (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ ∧
      printedBlockedOutputGate k hk v ∈ Matrix.unitaryGroup
        (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ := by
  obtain ⟨hi, ho⟩ := printedBlockingCircuits_mem_unitaryGroup k hk u v hu hv
  exact ⟨Matrix.reindex_mem_unitaryGroup _ _ hi, Matrix.reindex_mem_unitaryGroup _ _ ho⟩

/-- In half-word coordinates the centered printed gate fixes precisely
all spectator entries outside the last spin of the first half and the
first spin of the second half.
Source: arXiv:1703.09188, lines 1695--1698. -/
theorem printedBlockedOutputGate_apply {d k : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (a b s t : Fin (Kraus.blockPhysDim d (k + 1))) :
    printedBlockedOutputGate (k + 1) (by omega) v (a, b) (s, t) =
      if Fin.init (Kraus.decodeBlock d (k + 1) a) =
          Fin.init (Kraus.decodeBlock d (k + 1) s) ∧
        Fin.tail (Kraus.decodeBlock d (k + 1) b) =
          Fin.tail (Kraus.decodeBlock d (k + 1) t) then
        v (Kraus.decodeBlock d (k + 1) a (Fin.last k),
            Kraus.decodeBlock d (k + 1) b 0)
          (Kraus.decodeBlock d (k + 1) s (Fin.last k),
            Kraus.decodeBlock d (k + 1) t 0) else 0 := by
  have hout : (∀ p : Fin (2 * (k + 1)), p.val < k ∨ k + 2 ≤ p.val →
      printedHalfWordEquiv d (k + 1) (a, b) p =
        printedHalfWordEquiv d (k + 1) (s, t) p) ↔
      Fin.init (Kraus.decodeBlock d (k + 1) a) =
        Fin.init (Kraus.decodeBlock d (k + 1) s) ∧
      Fin.tail (Kraus.decodeBlock d (k + 1) b) =
        Fin.tail (Kraus.decodeBlock d (k + 1) t) := by
    constructor
    · intro h
      constructor
      · funext p
        have hh := h ⟨p.val, by have := p.isLt; omega⟩ (Or.inl p.isLt)
        change Kraus.decodeBlock d (k + 1) a p.castSucc =
          Kraus.decodeBlock d (k + 1) s p.castSucc
        exact (halfWord_left a b p.castSucc).symm.trans
          (hh.trans (halfWord_left s t p.castSucc))
      · funext p
        have hh := h ⟨k + 1 + p.succ.val, by have := p.isLt; omega⟩
          (Or.inr (by change k + 2 ≤ k + 1 + p.succ.val; simp; omega))
        change Kraus.decodeBlock d (k + 1) b p.succ =
          Kraus.decodeBlock d (k + 1) t p.succ
        exact (halfWord_right a b p.succ).symm.trans
          (hh.trans (halfWord_right s t p.succ))
    · rintro ⟨hleft, hright⟩ p hp
      have hpn := p.isLt
      by_cases hi : p.val < k + 1
      · let q : Fin k := ⟨p.val, by rcases hp with hp | hp <;> omega⟩
        have he : p = ⟨q.castSucc.val, by have := q.isLt; omega⟩ := rfl
        rw [he, halfWord_left, halfWord_left]
        exact congrFun hleft q
      · let q : Fin k := ⟨p.val - (k + 2), by omega⟩
        have he : p = ⟨k + 1 + q.succ.val, by have := q.isLt; omega⟩ := by
          apply Fin.ext
          dsimp only [q, Fin.val_succ]
          rcases hp with hp | hp <;> omega
        rw [he, halfWord_right, halfWord_right]
        exact congrFun hright q
  unfold printedBlockedOutputGate printedOutputCircuit
  change printedPairGate (2 * (k + 1)) k (by omega) v
    (printedHalfWordEquiv d (k + 1) (a, b))
    (printedHalfWordEquiv d (k + 1) (s, t)) = _
  rw [printedPairGate_apply]
  have hfirst (x y : Fin (Kraus.blockPhysDim d (k + 1))) :
      printedHalfWordEquiv d (k + 1) (x, y) ⟨k, by omega⟩ =
        Kraus.decodeBlock d (k + 1) x (Fin.last k) := halfWord_left x y (Fin.last k)
  have hlast (x y : Fin (Kraus.blockPhysDim d (k + 1))) :
      printedHalfWordEquiv d (k + 1) (x, y) ⟨k + 1, by omega⟩ =
        Kraus.decodeBlock d (k + 1) y 0 := by
    simpa only [Fin.val_zero, Nat.add_zero] using halfWord_right x y 0
  simp only [hout, hfirst, hlast]

/-- Contracting the actual identity-spectator half factors gives the
literal centered printed output gate at every positive blocking length.
Source: arXiv:1703.09188, StandardForm, lines 603--617 and 1695--1698. -/
theorem TwoSiteStandardFormData.printedBlocked_output_contraction {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (a b s t : Fin (Kraus.blockPhysDim d (k + 1))) :
    printedBlockedOutputGate (k + 1) (by omega) v (a, b) (s, t) =
      ∑ β : Fin D, printedBlockedHalfRight S (a, β) s *
        printedBlockedHalfLeft S (β, b) t := by
  rw [printedBlockedOutputGate_apply]
  by_cases hleft : Fin.init (Kraus.decodeBlock d (k + 1) a) =
      Fin.init (Kraus.decodeBlock d (k + 1) s) <;>
    by_cases hright : Fin.tail (Kraus.decodeBlock d (k + 1) b) =
      Fin.tail (Kraus.decodeBlock d (k + 1) t) <;>
    simp only [printedBlockedHalfRight, printedBlockedHalfLeft, hleft, hright,
      ite_true, ite_false, and_self, false_and, and_false, mul_zero, zero_mul,
      Finset.sum_const_zero, S.v_apply]

/-- Relabel the actual k-block physical alphabet by its first and last
k original spins, each encoded as a half word. The original physical
pairs are preserved before this middle cut.
Source: arXiv:1703.09188, lines 1689--1698. -/
noncomputable def printedBlockedPhysicalEquiv (d k : ℕ) :
    Fin (Kraus.blockPhysDim d k * Kraus.blockPhysDim d k) ≃
      Fin (Kraus.blockPhysDim (d * d) k) :=
  finProdFinEquiv.symm |>.trans (printedHalfWordEquiv d k) |>.trans
    (Equiv.arrowCongr (finCongr (Nat.mul_comm k 2)) (Equiv.refl (Fin d))).symm |>.trans
    (twoSiteChainConfigEquiv d k).symm |>.trans
    (twoSitePairConfigEquiv d k) |>.trans (Kraus.decodeBlockEquiv (d * d) k).symm

private theorem sum_blocked_half_left {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (α : Fin D) (a : Fin (Kraus.blockPhysDim d (k + 1)))
    (F : Fin (Kraus.blockPhysDim d (k + 1)) → ℂ) :
    (∑ t, printedBlockedHalfLeft S (α, a) t * F t) =
      ∑ x : Fin d, S.X₂ (α, Kraus.decodeBlock d (k + 1) a 0) x *
        F ((Kraus.decodeBlockEquiv d (k + 1)).symm
          (Fin.cons x (Fin.tail (Kraus.decodeBlock d (k + 1) a)))) := by
  rw [← (Kraus.decodeBlockEquiv d (k + 1)).symm.sum_comp
    (fun t ↦ printedBlockedHalfLeft S (α, a) t * F t)]
  simp only [printedBlockedHalfLeft, Kraus.decodeBlock_decodeBlockEquiv_symm]
  rw [Matrix.sum_fin_cons]
  simp only [Fin.tail_cons, Fin.cons_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

private theorem sum_blocked_half_right {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (γ : Fin D) (b : Fin (Kraus.blockPhysDim d (k + 1)))
    (F : Fin (Kraus.blockPhysDim d (k + 1)) → ℂ) :
    (∑ s, F s * printedBlockedHalfRight S (b, γ) s) =
      ∑ y : Fin d, F ((Kraus.decodeBlockEquiv d (k + 1)).symm
          (Fin.snoc (Fin.init (Kraus.decodeBlock d (k + 1) b)) y)) *
        S.X₁ (Kraus.decodeBlock d (k + 1) b (Fin.last k), γ) y := by
  rw [← (Kraus.decodeBlockEquiv d (k + 1)).symm.sum_comp
    (fun s ↦ F s * printedBlockedHalfRight S (b, γ) s)]
  simp only [printedBlockedHalfRight, Kraus.decodeBlock_decodeBlockEquiv_symm]
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) ↦ Fin d)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply, Fin.init_snoc, Fin.snoc_last,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem halfWord_boundary {d k : ℕ}
    (a b : Fin (Kraus.blockPhysDim d (k + 1))) (x y : Fin d) :
    printedHalfWordEquiv d (k + 1)
      ((Kraus.decodeBlockEquiv d (k + 1)).symm
          (Fin.cons x (Fin.tail (Kraus.decodeBlock d (k + 1) a))),
        (Kraus.decodeBlockEquiv d (k + 1)).symm
          (Fin.snoc (Fin.init (Kraus.decodeBlock d (k + 1) b)) y)) =
      fun q ↦ if q.val = 0 then x else if q.val = 2 * k + 1 then y else
        printedHalfWordEquiv d (k + 1) (a, b) q := by
  have hcons (w : Fin (k + 1) → Fin d) :
      Fin.cons x (Fin.tail w) = fun p ↦ if p.val = 0 then x else w p := by
    have h := congrArg (fun z ↦ Function.update z 0 x) (Fin.cons_self_tail w)
    calc
      _ = Function.update w 0 x := by simpa only [Fin.update_cons_zero] using h
      _ = _ := by funext p; simp only [Function.update_apply, Fin.ext_iff, Fin.val_zero]
  have hsnoc (w : Fin (k + 1) → Fin d) :
      Fin.snoc (Fin.init w) y = fun p ↦ if p.val = k then y else w p := by
    have h := congrArg (fun z ↦ Function.update z (Fin.last k) y) (Fin.snoc_init_self w)
    calc
      _ = Function.update w (Fin.last k) y := by
        simpa only [Fin.update_snoc_last] using h
      _ = _ := by funext p; simp only [Function.update_apply, Fin.ext_iff, Fin.val_last]
  funext q
  by_cases hq : q.val < k + 1
  · let p : Fin (k + 1) := ⟨q.val, hq⟩
    have he : q = ⟨p.val, by have := p.isLt; omega⟩ := rfl
    rw [he, halfWord_left, halfWord_left, Kraus.decodeBlock_decodeBlockEquiv_symm,
      hcons]
    have hlast : p.val ≠ 2 * k + 1 := by have := p.isLt; omega
    simp only [hlast, ite_false]
  · let p : Fin (k + 1) := ⟨q.val - (k + 1), by have := q.isLt; omega⟩
    have he : q = ⟨k + 1 + p.val, by have := p.isLt; omega⟩ := by
      apply Fin.ext
      dsimp only [p]
      omega
    rw [he, halfWord_right, halfWord_right, Kraus.decodeBlock_decodeBlockEquiv_symm,
      hsnoc]
    have hfirst : k + 1 + p.val ≠ 0 := by omega
    have hlast : k + 1 + p.val = 2 * k + 1 ↔ p.val = k := by omega
    simp only [hfirst, hlast, ite_false]

private theorem blocked_halves_contract_input {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (α γ : Fin D) (a b c e : Fin (Kraus.blockPhysDim d (k + 1))) :
    (∑ t, ∑ s, printedBlockedHalfLeft S (α, a) t *
      printedBlockedInputGate (k + 1) (by omega) u v (t, s) (c, e) *
        printedBlockedHalfRight S (b, γ) s) =
      ∑ x : Fin d, ∑ y : Fin d, S.X₂ (α, Kraus.decodeBlock d (k + 1) a 0) x *
        printedInputCircuit (k + 1) (by omega) u v
          (fun p ↦ if p.val = 0 then x else if p.val = 2 * k + 1 then y else
            printedHalfWordEquiv d (k + 1) (a, b) p)
          (printedHalfWordEquiv d (k + 1) (c, e)) *
            S.X₁ (Kraus.decodeBlock d (k + 1) b (Fin.last k), γ) y := by
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [sum_blocked_half_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_blocked_half_right]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  unfold printedBlockedInputGate
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    halfWord_boundary]

/-- Decoding the physical relabelling recovers the original ordered pair
configuration associated to the two half words.
Source: arXiv:1703.09188, lines 1689--1698. -/
theorem printedBlockedPhysicalEquiv_decode (d k : ℕ)
    (I : Fin (Kraus.blockPhysDim d k * Kraus.blockPhysDim d k)) :
    let e := (twoSiteChainConfigEquiv d k).trans
      (Equiv.arrowCongr (finCongr (Nat.mul_comm k 2)) (Equiv.refl (Fin d)))
    Kraus.decodeBlock (d * d) k (printedBlockedPhysicalEquiv d k I) =
      twoSitePairConfigEquiv d k (e.symm
        (printedHalfWordEquiv d k (finProdFinEquiv.symm I))) := by
  change Kraus.decodeBlock (d * d) k
    ((Kraus.decodeBlockEquiv (d * d) k).symm _) = _
  rw [Kraus.decodeBlock_decodeBlockEquiv_symm]
  rfl

/-- The original tensor at arbitrary positive blocking has the open
standard-form contraction through the literal printed input gate and
identity-spectator half factors, in the stated physical half-word basis.
Source: arXiv:1703.09188, StandardForm, lines 603--617 and 1689--1698. -/
theorem TwoSiteStandardFormData.printedBlocked_input_contraction {d D k : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (I J : Fin (Kraus.blockPhysDim d (k + 1) * Kraus.blockPhysDim d (k + 1)))
    (α γ : Fin D) :
    reindexPhysical (printedBlockedPhysicalEquiv d (k + 1))
        (blockTensor W (k + 1)) I J α γ =
      ∑ t, ∑ s, printedBlockedHalfLeft S (α, (finProdFinEquiv.symm I).1) t *
        printedBlockedInputGate (k + 1) (by omega) u v (t, s) (finProdFinEquiv.symm J) *
          printedBlockedHalfRight S ((finProdFinEquiv.symm I).2, γ) s := by
  let e := (twoSiteChainConfigEquiv d (k + 1)).trans
    (Equiv.arrowCongr (finCongr (Nat.mul_comm (k + 1) 2)) (Equiv.refl (Fin d)))
  let i := e.symm (printedHalfWordEquiv d (k + 1) (finProdFinEquiv.symm I))
  let j := e.symm (printedHalfWordEquiv d (k + 1) (finProdFinEquiv.symm J))
  have hp (K : Fin (Kraus.blockPhysDim d (k + 1) * Kraus.blockPhysDim d (k + 1))) :
      Kraus.decodeBlock (d * d) (k + 1) (printedBlockedPhysicalEquiv d (k + 1) K) =
        fun p ↦ finProdFinEquiv
          (e.symm (printedHalfWordEquiv d (k + 1) (finProdFinEquiv.symm K)) p) :=
    printedBlockedPhysicalEquiv_decode d (k + 1) K
  have hfirst (a b : Fin (Kraus.blockPhysDim d (k + 1))) :
      printedHalfWordEquiv d (k + 1) (a, b) ⟨0, by omega⟩ =
        Kraus.decodeBlock d (k + 1) a 0 := by
    simpa only [Fin.val_zero] using halfWord_left a b 0
  have hlast (a b : Fin (Kraus.blockPhysDim d (k + 1))) :
      printedHalfWordEquiv d (k + 1) (a, b) ⟨2 * k + 1, by omega⟩ =
        Kraus.decodeBlock d (k + 1) b (Fin.last k) := by
    have hh := halfWord_right a b (Fin.last k)
    simpa only [Fin.val_last, show k + 1 + k = 2 * k + 1 from by omega] using hh
  calc
    _ = evalWord W (List.ofFn fun p ↦ finProdFinEquiv (i p))
        (List.ofFn fun p ↦ finProdFinEquiv (j p)) α γ := by
      exact congrArg₂ (fun f g ↦ evalWord W (List.ofFn f) (List.ofFn g) α γ) (hp I) (hp J)
    _ = _ := by
      have h := S.evalWord_eq_printedInputCircuit i j α γ
      simpa only [i, j, e, Equiv.apply_symm_apply, hfirst, hlast, Prod.eta] using h
    _ = _ := (blocked_halves_contract_input S α γ
      (finProdFinEquiv.symm I).1 (finProdFinEquiv.symm I).2
      (finProdFinEquiv.symm J).1 (finProdFinEquiv.symm J).2).symm

/-- The actual arbitrary positive block has the literal printed two-site
standard form after splitting its original spins into two half words.
The original virtual bond space and explicit identity-spectator half
factors are retained; no canonical representative or comparison gauge
is assumed.
Source: arXiv:1703.09188, StandardForm, lines 603--617 and 1689--1698. -/
noncomputable def TwoSiteStandardFormData.printedBlock {d D : ℕ}
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (k : ℕ) (hk : 0 < k) :
    TwoSiteStandardFormData
      (reindexPhysical (printedBlockedPhysicalEquiv d k) (blockTensor W k))
      (printedBlockedInputGate k hk u v) (printedBlockedOutputGate k hk v) := by
  obtain ⟨hu, hv⟩ := printedBlockedGates_mem_unitaryGroup k hk u v
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup u).mp S.u_unitary)
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup v).mp S.v_unitary)
  have hpos : 0 < Kraus.blockPhysDim d k := by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_pos S.phys_pos _
  cases k with
  | zero => omega
  | succ k =>
    exact {
      phys_pos := hpos
      bond_pos := S.bond_pos
      left_pos := hpos
      right_pos := hpos
      X₁ := printedBlockedHalfRight S
      X₂ := printedBlockedHalfLeft S
      u_unitary := (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr hu
      v_unitary := (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr hv
      v_apply := S.printedBlocked_output_contraction
      W_apply := S.printedBlocked_input_contraction
    }

end MPOTensor
