/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixReindexUnitary
import TNLean.Circuit.EmbeddedProduct
import TNLean.Circuit.PairProduct

/-!
# The printed gates for arbitrary physical blocking

The input circuit on `2k` original spins applies `u` on each unshifted pair
and `v` on the `k-1` internal shifted pairs. The output circuit applies `v`
on the middle pair and the identity on the `k-1` spins at each end.

Source: arXiv:1703.09188, `prop:sigma1-and-sigma2-equal`, lines 1689--1700.
-/

open scoped Matrix Kronecker BigOperators
open Matrix QuantumCircuit

namespace MPOTensor

private def spinWindow (n p m : ℕ) (h : p + m ≤ n) : Fin m ↪ Fin n :=
  (Fin.natAddEmb p).trans (Fin.castLEEmb h)

/-- Place a two-spin matrix on consecutive original spins `p,p+1`.
Source: arXiv:1703.09188, the site labels in lines 1657--1733. -/
noncomputable def printedPairGate {d : ℕ} (n p : ℕ) (h : p + 2 ≤ n)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  embedOp (spinWindow n p 2 h)
    (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
      (finTwoArrowEquiv (Fin d)).symm A)

/-- The matrix entries of a placed pair gate keep every exterior spin fixed.
Source: arXiv:1703.09188, lines 1689--1700. -/
theorem printedPairGate_apply {d : ℕ} (n p : ℕ) (h : p + 2 ≤ n)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x y : Fin n → Fin d) :
    printedPairGate n p h A x y =
      if ∀ i : Fin n, i.val < p ∨ p + 2 ≤ i.val → x i = y i then
        A (x ⟨p, by omega⟩, x ⟨p + 1, by omega⟩)
          (y ⟨p, by omega⟩, y ⟨p + 1, by omega⟩)
      else 0 := by
  have hc : AgreeOff (spinWindow n p 2 h) x y ↔
      ∀ i : Fin n, i.val < p ∨ p + 2 ≤ i.val → x i = y i := by
    constructor
    · intro hxy i hi
      apply hxy i
      intro j hj
      have hv := congrArg Fin.val hj
      change p + j.val = i.val at hv
      have := j.isLt
      rcases hi with hi | hi <;> omega
    · intro hxy i hi
      apply hxy i
      by_contra hout
      have hr : p ≤ i.val ∧ i.val < p + 2 := by omega
      let j : Fin 2 := ⟨i.val - p, by omega⟩
      apply hi j
      apply Fin.ext
      change p + (i.val - p) = i.val
      omega
  change (if AgreeOff (spinWindow n p 2 h) x y then
    A (x ⟨p, by omega⟩, x ⟨p + 1, by omega⟩)
      (y ⟨p, by omega⟩, y ⟨p + 1, by omega⟩) else 0) = _
  simp only [hc]

/-- Placing a gate inside a consecutively placed interval adds the offsets.
Source: arXiv:1703.09188, the successive local placements in lines 1721--1729. -/
theorem printedPairGate_embed {d n m p q : ℕ} (hq : q + 2 ≤ m)
    (hp : p + q + 2 ≤ n) (f : Fin m → Fin n) (hf : Function.Injective f)
    (hpos : ∀ i, (f i).val = p + i.val)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    embedOp f (printedPairGate m q hq A) = printedPairGate n (p + q) hp A := by
  unfold printedPairGate
  rw [embedOp_embedOp hf]
  congr 1
  funext i
  apply Fin.ext
  change (f (spinWindow m q 2 hq i)).val = p + q + i.val
  rw [hpos]
  change p + (q + i.val) = p + q + i.val
  omega

/-- Disjoint original-spin pairs carry commuting gates.
Source: arXiv:1703.09188, the disjoint layers in lines 1689--1733. -/
theorem printedPairGate_commute {d n p q : ℕ} (hp : p + 2 ≤ n) (hq : q + 2 ≤ n)
    (hdisj : p + 2 ≤ q ∨ q + 2 ≤ p)
    (A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Commute (printedPairGate n p hp A) (printedPairGate n q hq B) := by
  apply commute_embedOp_of_disjoint (spinWindow n p 2 hp).injective
    (spinWindow n q 2 hq).injective
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨i, rfl⟩ ⟨j, hij⟩
  have hval := congrArg Fin.val hij
  change q + j.val = p + i.val at hval
  have hi := i.isLt
  have hj := j.isLt
  rcases hdisj with hdisj | hdisj <;> omega

/-- A unitary two-spin gate stays unitary when placed in a longer chain.
Source: arXiv:1703.09188, lines 1689--1700. -/
theorem printedPairGate_mem_unitaryGroup {d : ℕ} (n p : ℕ) (h : p + 2 ≤ n)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
    printedPairGate n p h A ∈ Matrix.unitaryGroup (Fin n → Fin d) ℂ :=
  embedOp_mem_unitary (spinWindow n p 2 h).injective
    (Matrix.reindex_mem_unitaryGroup (finTwoArrowEquiv (Fin d)).symm _ hA)

/-- The unshifted pair gates in cells `a,...,a+m-1` of a `2k`-spin chain.
Source: arXiv:1703.09188, lines 1692--1694 and 1721--1725. -/
noncomputable def printedCellLayer {d : ℕ} (k a m : ℕ) (h : a + m ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ :=
  (List.ofFn fun j : Fin m ↦
    printedPairGate (2 * k) (2 * (a + j.val)) (by have := j.isLt; omega) A).prod

/-- The shifted pair gates after cells `a,...,a+m-1` of a `2k`-spin chain.
Source: arXiv:1703.09188, lines 1692--1694 and 1721--1725. -/
noncomputable def printedLinkLayer {d : ℕ} (k a m : ℕ) (h : a + m + 1 ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ :=
  (List.ofFn fun j : Fin m ↦
    printedPairGate (2 * k) (2 * (a + j.val) + 1) (by have := j.isLt; omega) A).prod

/-- A cell layer with no gates is the identity. -/
@[simp] theorem printedCellLayer_zero {d : ℕ} (k a : ℕ) (h : a ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    printedCellLayer k a 0 (by omega) A = 1 := by
  simp [printedCellLayer]

/-- A shifted layer with no gates is the identity. -/
@[simp] theorem printedLinkLayer_zero {d : ℕ} (k a : ℕ) (h : a + 1 ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    printedLinkLayer k a 0 h A = 1 := by
  simp [printedLinkLayer]

/-- Split off the first unshifted gate in a consecutive cell layer.
Source: arXiv:1703.09188, the successive factors in lines 1721--1729. -/
theorem printedCellLayer_succ {d : ℕ} (k a m : ℕ) (h : a + (m + 1) ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    printedCellLayer k a (m + 1) h A =
      printedPairGate (2 * k) (2 * a) (by omega) A *
        printedCellLayer k (a + 1) m (by omega) A := by
  simp only [printedCellLayer, List.ofFn_succ, List.prod_cons]
  congr 1
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  congr 1
  simp only [Fin.val_succ]
  omega

/-- Split off the first shifted gate in a consecutive link layer.
Source: arXiv:1703.09188, the successive factors in lines 1721--1729. -/
theorem printedLinkLayer_succ {d : ℕ} (k a m : ℕ) (h : a + (m + 1) + 1 ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    printedLinkLayer k a (m + 1) h A =
      printedPairGate (2 * k) (2 * a + 1) (by omega) A *
        printedLinkLayer k (a + 1) m (by omega) A := by
  simp only [printedLinkLayer, List.ofFn_succ, List.prod_cons]
  congr 1
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  congr 1
  simp only [Fin.val_succ]
  omega

/-- Split off the last unshifted gate in a consecutive cell layer.
Source: arXiv:1703.09188, lines 1721--1729. -/
theorem printedCellLayer_succ_last {d : ℕ} (k a m : ℕ) (h : a + (m + 1) ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    printedCellLayer k a (m + 1) h A =
      printedCellLayer k a m (by omega) A *
        printedPairGate (2 * k) (2 * (a + m)) (by omega) A := by
  unfold printedCellLayer
  rw [List.ofFn_succ', List.prod_concat]
  rfl

/-- Split off the last shifted gate in a consecutive link layer.
Source: arXiv:1703.09188, lines 1721--1729. -/
theorem printedLinkLayer_succ_last {d : ℕ} (k a m : ℕ) (h : a + (m + 1) + 1 ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    printedLinkLayer k a (m + 1) h A =
      printedLinkLayer k a m (by omega) A *
        printedPairGate (2 * k) (2 * (a + m) + 1) (by omega) A := by
  unfold printedLinkLayer
  rw [List.ofFn_succ', List.prod_concat]
  rfl

/-- Consecutively embedding a cell layer translates all of its cells.
Source: arXiv:1703.09188, the arbitrary-blocking circuits, lines 1689--1698. -/
theorem printedCellLayer_embed {d k K a m b : ℕ} (h : a + m ≤ k)
    (hK : b + a + m ≤ K) (f : Fin (2 * k) → Fin (2 * K))
    (hf : Function.Injective f) (hpos : ∀ i, (f i).val = 2 * b + i.val)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    embedOp f (printedCellLayer k a m h A) = printedCellLayer K (b + a) m hK A := by
  unfold printedCellLayer
  rw [embedOp_list_prod hf, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  have hj := j.isLt
  convert printedPairGate_embed (p := 2 * b) (q := 2 * (a + j.val))
    (by omega) (by omega) f hf hpos A using 1 <;> congr 1
  omega

/-- Consecutively embedding a shifted layer translates all of its links.
Source: arXiv:1703.09188, the arbitrary-blocking circuits, lines 1689--1698. -/
theorem printedLinkLayer_embed {d k K a m b : ℕ} (h : a + m + 1 ≤ k)
    (hK : b + a + m + 1 ≤ K) (f : Fin (2 * k) → Fin (2 * K))
    (hf : Function.Injective f) (hpos : ∀ i, (f i).val = 2 * b + i.val)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    embedOp f (printedLinkLayer k a m h A) = printedLinkLayer K (b + a) m hK A := by
  unfold printedLinkLayer
  rw [embedOp_list_prod hf, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  have hj := j.isLt
  convert printedPairGate_embed (p := 2 * b) (q := 2 * (a + j.val) + 1)
    (by omega) (by omega) f hf hpos A using 1 <;> congr 1
  omega

/-- A pair gate commutes with a cell layer lying wholly to either side.
Source: arXiv:1703.09188, lines 1721--1729. -/
theorem printedPairGate_commute_cellLayer {d k a m p : ℕ}
    (hp : p + 2 ≤ 2 * k) (hl : a + m ≤ k)
    (hdisj : p + 2 ≤ 2 * a ∨ 2 * (a + m) ≤ p)
    (A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Commute (printedPairGate (2 * k) p hp A) (printedCellLayer k a m hl B) := by
  apply Commute.list_prod_right
  intro C hC
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hC
  apply printedPairGate_commute
  have hj := j.isLt
  rcases hdisj with hdisj | hdisj
  · left; omega
  · right; omega

/-- A pair gate commutes with a shifted layer lying wholly to either side.
Source: arXiv:1703.09188, lines 1721--1729. -/
theorem printedPairGate_commute_linkLayer {d k a m p : ℕ}
    (hp : p + 2 ≤ 2 * k) (hl : a + m + 1 ≤ k)
    (hdisj : p + 2 ≤ 2 * a + 1 ∨ 2 * (a + m) + 1 ≤ p)
    (A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Commute (printedPairGate (2 * k) p hp A) (printedLinkLayer k a m hl B) := by
  apply Commute.list_prod_right
  intro C hC
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hC
  apply printedPairGate_commute
  have hj := j.isLt
  rcases hdisj with hdisj | hdisj
  · left; omega
  · right; omega

/-- Placing a pair gate commutes with taking its adjoint. -/
@[simp] theorem printedPairGate_conjTranspose {d : ℕ} (n p : ℕ) (h : p + 2 ≤ n)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (printedPairGate n p h A)ᴴ = printedPairGate n p h Aᴴ := by
  rw [printedPairGate, embedOp_conjTranspose]
  rfl

/-- Taking adjoints of a cell layer takes the adjoint of each disjoint gate.
Source: arXiv:1703.09188, lines 1721--1732. -/
theorem printedCellLayer_conjTranspose {d : ℕ} (k a m : ℕ) (h : a + m ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (printedCellLayer k a m h A)ᴴ = printedCellLayer k a m h Aᴴ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [printedCellLayer_succ_last, Matrix.conjTranspose_mul,
      printedPairGate_conjTranspose, ih (by omega), printedCellLayer_succ_last]
    exact (printedPairGate_commute_cellLayer (by omega) (by omega)
      (Or.inr (by omega)) Aᴴ Aᴴ).eq

/-- Taking adjoints of a shifted layer takes the adjoint of each disjoint gate.
Source: arXiv:1703.09188, lines 1721--1732. -/
theorem printedLinkLayer_conjTranspose {d : ℕ} (k a m : ℕ) (h : a + m + 1 ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (printedLinkLayer k a m h A)ᴴ = printedLinkLayer k a m h Aᴴ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [printedLinkLayer_succ_last, Matrix.conjTranspose_mul,
      printedPairGate_conjTranspose, ih (by omega), printedLinkLayer_succ_last]
    exact (printedPairGate_commute_linkLayer (by omega) (by omega)
      (Or.inr (by omega)) Aᴴ Aᴴ).eq

/-- A consecutive unshifted layer of unitary gates is unitary.
Source: arXiv:1703.09188, lines 1692--1694. -/
theorem printedCellLayer_mem_unitaryGroup {d : ℕ} (k a m : ℕ) (h : a + m ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
    printedCellLayer k a m h A ∈ Matrix.unitaryGroup (Fin (2 * k) → Fin d) ℂ := by
  apply Submonoid.list_prod_mem
  intro C hC
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hC
  exact printedPairGate_mem_unitaryGroup _ _ _ A hA

/-- A consecutive shifted layer of unitary gates is unitary.
Source: arXiv:1703.09188, lines 1692--1694. -/
theorem printedLinkLayer_mem_unitaryGroup {d : ℕ} (k a m : ℕ) (h : a + m + 1 ≤ k)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
    printedLinkLayer k a m h A ∈ Matrix.unitaryGroup (Fin (2 * k) → Fin d) ℂ := by
  apply Submonoid.list_prod_mem
  intro C hC
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hC
  exact printedPairGate_mem_unitaryGroup _ _ _ A hA

/-- The printed input circuit `u^(k)` on the ordered `2k` original spins.
Source: arXiv:1703.09188, lines 1689--1694. -/
noncomputable def printedInputCircuit {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ :=
  printedLinkLayer k 0 (k - 1) (by omega) v * printedCellLayer k 0 k (by omega) u

/-- The printed output circuit `v^(k)` on the middle original-spin pair.
Source: arXiv:1703.09188, lines 1695--1698. -/
noncomputable def printedOutputCircuit {d : ℕ} (k : ℕ) (hk : 0 < k)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ :=
  printedPairGate (2 * k) (k - 1) (by omega) v

/-- The literal arbitrary-blocking circuits are unitary when `u,v` are unitary.
Source: arXiv:1703.09188, lines 1689--1698. -/
theorem printedBlockingCircuits_mem_unitaryGroup {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hv : v ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
    printedInputCircuit k hk u v ∈ Matrix.unitaryGroup (Fin (2 * k) → Fin d) ℂ ∧
      printedOutputCircuit k hk v ∈ Matrix.unitaryGroup (Fin (2 * k) → Fin d) ℂ := by
  exact ⟨Submonoid.mul_mem _ (printedLinkLayer_mem_unitaryGroup _ _ _ _ v hv)
    (printedCellLayer_mem_unitaryGroup _ _ _ _ u hu),
    printedPairGate_mem_unitaryGroup _ _ _ v hv⟩

/-- Appending one original cell adds its unshifted gate on the right and
its connecting shifted gate on the left of the embedded old input circuit.
Source: arXiv:1703.09188, the printed input gate, lines 1689--1694. -/
theorem printedInputCircuit_succ {d : ℕ} (k : ℕ) (hk : 0 < k)
    (f : Fin (2 * k) → Fin (2 * (k + 1))) (hf : Function.Injective f)
    (hpos : ∀ i, (f i).val = i.val)
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    printedInputCircuit (k + 1) (by omega) u v =
      printedPairGate (2 * (k + 1)) (2 * k - 1) (by omega) v *
        embedOp f (printedInputCircuit k hk u v) *
        printedPairGate (2 * (k + 1)) (2 * k) (by omega) u := by
  have hc := printedCellLayer_embed (b := 0) (a := 0) (m := k)
    (by omega) (by omega) f hf (by simpa using hpos) u
  have hv := printedLinkLayer_embed (b := 0) (a := 0) (m := k - 1)
    (by omega) (by omega) f hf (by simpa using hpos) v
  have hlink : printedLinkLayer (k + 1) 0 k (by omega) v =
      printedLinkLayer (k + 1) 0 (k - 1) (by omega) v *
        printedPairGate (2 * (k + 1)) (2 * k - 1) (by omega) v := by
    convert printedLinkLayer_succ_last (k + 1) 0 (k - 1) (by omega) v using 1 <;>
      congr 1
    all_goals congr 1
    all_goals omega
  have hcomm := printedPairGate_commute_linkLayer
    (k := k + 1) (p := 2 * k - 1) (a := 0) (m := k - 1)
    (by omega) (by omega) (Or.inr (by omega)) v v
  unfold printedInputCircuit
  rw [← embedOp_mul hf, hc, hv]
  have hlen : k + 1 - 1 = k := by omega
  have hlinks : printedLinkLayer (k + 1) 0 (k + 1 - 1) (by omega) v =
      printedLinkLayer (k + 1) 0 k (by omega) v := by congr 1
  rw [hlinks, hlink, printedCellLayer_succ_last, ← hcomm.eq]
  simp only [Matrix.mul_assoc]
  congr
  omega

end MPOTensor
