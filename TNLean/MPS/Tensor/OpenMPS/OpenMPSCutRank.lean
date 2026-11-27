/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.OpenMPSRank
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import TNLean.MPS.Tensor.OpenMPS.SupportedCutRank
import QICLean.Channel.Schmidt.Rank
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Cut ranks of open-boundary matrix product states

Splitting a rectangular tensor contraction at a virtual bond factors the cut matrix
through that bond space. Thus an internal cut of an open-boundary matrix product state
of bond dimension at most `D` has rank at most `D`, including when `D = 0`.
Together with the construction from cut ranks, this characterizes `IsOpenMPS`.
The endpoint cuts have rank at most one and impose no condition on `D`.

## References

* SWVC07, arXiv:0705.0292v2, `paper_v2.tex`, lines 234–264: the cut-rank bound
  used in the lower bound on approximation error.
* TNLean one-dimensional note, Part IIa, Proposition `prop:VC`, lines 39–62.
* Landau, Vazirani, Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 393 and 399: appending a
  site in a fixed state does not raise the bond dimension (`IsOpenMPS.snoc`).

## Extension by a fixed exterior configuration

A state on a contiguous interval extends to the full chain by fixing a basis
configuration on its complement. At each cut, the extended coefficient matrix
is obtained from the corresponding interior coefficient matrix by the two
configuration restriction maps and by diagonal matching indicators. Its rank
is therefore at most the interior cut rank. Cuts outside the interval have
rank at most one.

Consequently an interior bond bound `D` gives the full-chain bound `max 1 D`.
The maximum accounts for empty and one-site intervals, whose internal bond
conditions allow `D = 0` even for a nonzero state.

## Bond dimension after applying an operator

Across each internal cut, applying an operator multiplies the Schmidt rank of a vector by
at most the operator-Schmidt rank. Consequently, an operator with operator-Schmidt rank at
most `D` at every internal cut sends an open matrix product state of bond dimension at most
`b` to one of bond dimension at most `D * b`.

This is the bond-growth estimate in the error-reduction step of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Claim `c:errorreduction`, lines 580–592, especially line 591.
The estimate includes zero vectors, zero bond bounds and chains with at most one site.

## Finite spans of open-boundary matrix product states

A vector in the span of a finite set of matrix product states of bond dimension at most
`D` has bond dimension at most the cardinality of the set times `D`. The estimate follows
from subadditivity of the ranks of the coefficient matrices at each internal cut.

This is the finite-span estimate used in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Claim `c:2`, lines 520–527. It is independent of the
Hamiltonian and of any choice of a viable witness.
-/

open ManyBody (interval mem_interval)

section

open scoped BigOperators
open Matrix
open ManyBody (cutMatrix)

namespace TNLean.MPS.AreaLaw

/-- Join the bond indices strictly to the left and right of a cut with its fixed bond index. -/
private def joinBondPath {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1))
    (z : B k) (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (r : (j : {j : Fin (L + 1) // k < j}) → B j) (j : Fin (L + 1)) : B j :=
  if h : j < k then l ⟨j, h⟩ else
    if h' : j = k then h'.symm ▸ z else r ⟨j, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h')⟩

/-- A bond path is determined by its index at the cut and its restrictions to either side. -/
private def bondPathEquiv {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1)) :
    ((j : Fin (L + 1)) → B j) ≃
      B k × ((j : {j : Fin (L + 1) // j < k}) → B j) ×
        ((j : {j : Fin (L + 1) // k < j}) → B j) where
  toFun p := (p k, (fun j ↦ p j), fun j ↦ p j)
  invFun p := joinBondPath B k p.1 p.2.1 p.2.2
  left_inv := by
    intro p
    funext j
    simp only [joinBondPath, dite_eq_ite, ite_eq_left_iff]
    intro h
    split_ifs with he <;> subst_vars <;> rfl
  right_inv := by
    rintro ⟨z, l, r⟩
    simp +contextual [joinBondPath, funext_iff, lt_asymm, ne_of_gt]

/-- Extend the left bond path to the cut by assigning the prescribed cut index. -/
private def leftBondPath {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1))
    (z : B k) (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (j : Fin (L + 1)) (hj : j ≤ k) : B j :=
  if h : j < k then l ⟨j, h⟩ else (le_antisymm hj (le_of_not_gt h)).symm ▸ z

/-- Extend the right bond path to the cut by assigning the prescribed cut index. -/
private def rightBondPath {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1))
    (z : B k) (r : (j : {j : Fin (L + 1) // k < j}) → B j)
    (j : Fin (L + 1)) (hj : k ≤ j) : B j :=
  if h : k < j then r ⟨j, h⟩ else (le_antisymm (le_of_not_gt h) hj).symm ▸ z

/-- On or to the left of the cut, the joined path agrees with the extended left path. -/
private theorem joinBondPath_of_le {L : ℕ} (B : Fin (L + 1) → Type*)
    (k : Fin (L + 1)) (z : B k)
    (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (r : (j : {j : Fin (L + 1) // k < j}) → B j)
    (j : Fin (L + 1)) (hj : j ≤ k) :
    joinBondPath B k z l r j = leftBondPath B k z l j hj := by
  by_cases h : j < k
  · simp [joinBondPath, leftBondPath, h]
  · have he : j = k := le_antisymm hj (le_of_not_gt h)
    subst j
    simp [joinBondPath, leftBondPath]

/-- On or to the right of the cut, the joined path agrees with the extended right path. -/
private theorem joinBondPath_of_ge {L : ℕ} (B : Fin (L + 1) → Type*)
    (k : Fin (L + 1)) (z : B k)
    (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (r : (j : {j : Fin (L + 1) // k < j}) → B j)
    (j : Fin (L + 1)) (hj : k ≤ j) :
    joinBondPath B k z l r j = rightBondPath B k z r j hj := by
  by_cases h : k < j
  · simp [joinBondPath, rightBondPath, h, not_lt_of_ge hj, ne_of_gt h]
  · obtain rfl := le_antisymm (le_of_not_gt h) hj
    simp [joinBondPath, rightBondPath]

/-- Contract the tensors strictly to the left of the cut, keeping its bond index fixed. -/
private noncomputable def leftContraction {L q D : ℕ} (A : OBCChainTensor q D L)
    (k : Fin (L + 1)) (a : (v : {v : Fin L // v ∈ interval L 0 k}) → Fin q)
    (z : Fin (A.bondDim k)) : ℂ :=
  ∑ l : (j : {j : Fin (L + 1) // j < k}) → Fin (A.bondDim j),
    ∏ i : {i : Fin L // i ∈ interval L 0 k},
      A.tensor i (a i)
        (leftBondPath (fun j ↦ Fin (A.bondDim j)) k z l i.1.castSucc
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.le_of_lt (mem_interval.mp i.2).2)))
        (leftBondPath (fun j ↦ Fin (A.bondDim j)) k z l i.1.succ
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.succ_le_of_lt (mem_interval.mp i.2).2)))

/-- Contract the tensors on the right of the cut, keeping its bond index fixed. -/
private noncomputable def rightContraction {L q D : ℕ} (A : OBCChainTensor q D L)
    (k : Fin (L + 1)) (b : (v : {v : Fin L // v ∉ interval L 0 k}) → Fin q)
    (z : Fin (A.bondDim k)) : ℂ :=
  ∑ r : (j : {j : Fin (L + 1) // k < j}) → Fin (A.bondDim j),
    ∏ i : {i : Fin L // i ∉ interval L 0 k},
      A.tensor i (b i)
        (rightBondPath (fun j ↦ Fin (A.bondDim j)) k z r i.1.castSucc
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.le_of_not_lt (fun h ↦ i.2 (mem_interval.mpr ⟨Nat.zero_le _, h⟩)))))
        (rightBondPath (fun j ↦ Fin (A.bondDim j)) k z r i.1.succ
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.le_succ_of_le (Nat.le_of_not_lt
              fun h ↦ i.2 (mem_interval.mpr ⟨Nat.zero_le _, h⟩)))))

/-- The full contraction is the sum over the cut bond of the two partial contractions.
This is the bond splitting underlying SWVC07, arXiv:0705.0292v2, lines 234–264. -/
private theorem coeff_eq_sum_left_mul_right {L q D : ℕ} (A : OBCChainTensor q D L)
    (k : Fin (L + 1)) (a : (v : {v : Fin L // v ∈ interval L 0 k}) → Fin q)
    (b : (v : {v : Fin L // v ∉ interval L 0 k}) → Fin q) :
    A.coeff ((ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 k)).symm (a, b)) =
      ∑ z, leftContraction A k a z * rightContraction A k b z := by
  classical
  rw [OBCChainTensor.coeff, ← (bondPathEquiv (fun j ↦ Fin (A.bondDim j)) k).symm.sum_comp]
  simp only [Fintype.sum_prod_type, bondPathEquiv, Equiv.coe_fn_symm_mk,
    leftContraction, rightContraction, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun l _ ↦
    Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin L ↦ i ∈ interval L 0 k)]
  congr 1
  · refine Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun i _ ↦ ?_
    rw [ManyBody.cutEquiv_symm_apply_mem (X := fun _ ↦ Fin q) a b i.2]
    exact congrArg₂ (fun x y ↦ A.tensor i (a i) x y)
      (joinBondPath_of_le _ _ _ _ _ _ _) (joinBondPath_of_le _ _ _ _ _ _ _)
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [ManyBody.cutEquiv_symm_apply_not_mem (X := fun _ ↦ Fin q) a b i.2]
    exact congrArg₂ (fun x y ↦ A.tensor i (b i) x y)
      (joinBondPath_of_ge _ _ _ _ _ _ _) (joinBondPath_of_ge _ _ _ _ _ _ _)

/-- The cut matrix factors through the virtual bond space, with any overall scalar absorbed
into the left factor. Source: SWVC07, arXiv:0705.0292v2, lines 234–264. -/
private theorem exists_cutMatrix_factorization {L q D : ℕ}
    (A : OBCChainTensor q D L) (c : ℂ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ∀ x, ψ x = c * A.coeff x)
    (k : Fin (L + 1)) :
    ∃ (U : Matrix ((v : {v : Fin L // v ∈ interval L 0 k}) → Fin q)
        (Fin (A.bondDim k)) ℂ)
      (V : Matrix (Fin (A.bondDim k))
        ((v : {v : Fin L // v ∉ interval L 0 k}) → Fin q) ℂ),
      cutMatrix (interval L 0 k) ψ = U * V := by
  classical
  refine ⟨Matrix.of (fun a z ↦ c * leftContraction A k a z),
    Matrix.of (fun z b ↦ rightContraction A k b z), ?_⟩
  ext a b
  rw [ManyBody.cutMatrix_apply, hψ, Matrix.mul_apply]
  simp only [Matrix.of_apply, mul_assoc, ← Finset.mul_sum]
  exact congrArg (c * ·) (coeff_eq_sum_left_mul_right A k a b)

/-- A cut matrix of a scalar multiple of an open-boundary contraction has rank at most
the dimension of the actual virtual bond, including a zero-dimensional bond.
Source: SWVC07, arXiv:0705.0292v2, lines 234–264; the one-dimensional note,
Part IIa, Proposition `prop:VC`, lines 39–62. -/
theorem rank_cutMatrix_le_bondDim {L q D : ℕ} (A : OBCChainTensor q D L) (c : ℂ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ∀ x, ψ x = c * A.coeff x)
    (k : Fin (L + 1)) : (cutMatrix (interval L 0 k) ψ).rank ≤ A.bondDim k := by
  obtain ⟨U, V, hUV⟩ := exists_cutMatrix_factorization A c ψ hψ k
  rw [hUV]
  simpa using (rank_mul_le_left U V).trans (rank_le_card_width U)

/-- Every internal cut of an open-boundary MPS has rank bounded by its internal
bond dimension. No normalization or positivity assumption on `D` is needed.
Source: SWVC07, arXiv:0705.0292v2, lines 234–264; the one-dimensional note,
Part IIa, Proposition `prop:VC`, lines 39–62. -/
theorem IsOpenMPS.rank_cutMatrix_le {L q D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    (cutMatrix (interval L 0 k) ψ).rank ≤ D := by
  obtain ⟨A, c, hD, hA⟩ := hψ
  exact (rank_cutMatrix_le_bondDim A c ψ hA ⟨k, by omega⟩).trans
    (hD ⟨k, by omega⟩ hk0 hkL)

/-- Internal cut ranks characterize open-boundary matrix product states, also for
empty and one-site chains and for `D = 0`.
Source: SWVC07, arXiv:0705.0292v2, lines 234–264; the one-dimensional note,
Part IIa, Proposition `prop:VC`, lines 39–62. -/
theorem isOpenMPS_iff_internal_cutMatrix_rank_le {L q D : ℕ}
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    IsOpenMPS L q D (fun x ↦ ψ x) ↔
      ∀ k : ℕ, 0 < k → k < L → (cutMatrix (interval L 0 k) ψ).rank ≤ D := by
  exact ⟨fun h k hk0 hkL ↦ h.rank_cutMatrix_le hk0 hkL,
    isOpenMPS_of_internal_cutMatrix_rank_le ψ⟩

/-- Enlarging the allowed bond dimension preserves an open-boundary matrix
product representation. This follows from the internal-cut characterization
in SWVC07, arXiv:0705.0292v2, lines 234–264, including empty chains and
zero bond bounds. -/
theorem IsOpenMPS.mono {L q D D' : ℕ} {psi : (Fin L → Fin q) → ℂ}
    (hpsi : IsOpenMPS L q D psi) (hD : D ≤ D') : IsOpenMPS L q D' psi := by
  apply (isOpenMPS_iff_internal_cutMatrix_rank_le (WithLp.toLp 2 psi)).mpr
  intro k hk0 hkL
  exact (hpsi.rank_cutMatrix_le (ψ := WithLp.toLp 2 psi) hk0 hkL).trans hD

/-- **Appending a site.** If `w` is an open-boundary matrix product state of bond dimension at
most `b` on `n` sites and `0 < b`, then `x ↦ w (x₀, …, x_{n-1}) f (x_n)` is one on `n + 1`
sites: the new internal bond carries rank at most one (arXiv:1307.5143v1, algo53.tex,
lines 393 and 399). -/
theorem IsOpenMPS.snoc {n q b : ℕ} (hb : 0 < b) {w : (Fin n → Fin q) → ℂ}
    (hw : IsOpenMPS n q b w) (f : Fin q → ℂ) :
    IsOpenMPS (n + 1) q b fun x ↦ w (Fin.init x) * f (x (Fin.last n)) := by
  classical
  set W : EuclideanSpace ℂ (Fin n → Fin q) := WithLp.toLp 2 w
  set W' : EuclideanSpace ℂ (Fin (n + 1) → Fin q) :=
    WithLp.toLp 2 fun x ↦ w (Fin.init x) * f (x (Fin.last n))
  have hW : IsOpenMPS n q b fun x ↦ W x := hw
  refine isOpenMPS_of_internal_cutMatrix_rank_le W' fun j hj0 hjn ↦ ?_
  have hlast : Fin.last n ∉ interval (n + 1) 0 j := by
    simp only [mem_interval, Fin.val_last, Nat.zero_le, true_and]
    omega
  let ra : (ManyBody.RegionConfig (fun _ ↦ Fin q) (interval (n + 1) 0 j)) →
      (ManyBody.RegionConfig (fun _ ↦ Fin q) (interval n 0 j)) :=
    fun a v ↦ a ⟨v.1.castSucc,
        by simpa only [mem_interval, Fin.val_castSucc, Nat.zero_le, true_and] using v.2⟩
  let rb : ((v : {v : Fin (n + 1) // v ∉ interval (n + 1) 0 j}) → Fin q) →
      ((v : {v : Fin n // v ∉ interval n 0 j}) → Fin q) :=
    fun b v ↦ b ⟨v.1.castSucc,
        by simpa only [mem_interval, Fin.val_castSucc, Nat.zero_le, true_and] using v.2⟩
  let Lm : Matrix (ManyBody.RegionConfig (fun _ ↦ Fin q) (interval (n + 1) 0 j))
      (ManyBody.RegionConfig (fun _ ↦ Fin q) (interval n 0 j)) ℂ :=
    Matrix.of fun a a' ↦ if a' = ra a then 1 else 0
  let R : Matrix ((v : {v : Fin n // v ∉ interval n 0 j}) → Fin q)
      ((v : {v : Fin (n + 1) // v ∉ interval (n + 1) 0 j}) → Fin q) ℂ :=
    Matrix.of fun c b ↦ if c = rb b then f (b ⟨Fin.last n, hlast⟩) else 0
  have hcut : cutMatrix (interval (n + 1) 0 j) W' = Lm * cutMatrix (interval n 0 j) W * R := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (rb b) (fun c _ hc ↦ by simp [R, hc]) (by simp),
      Matrix.mul_apply, Finset.sum_eq_single (ra a) (fun a' _ ha ↦ by simp [Lm, ha]) (by simp)]
    simp only [Lm, R, Matrix.of_apply, ite_true, one_mul, ManyBody.cutMatrix_apply]
    change w _ * f _ = w _ * f _
    congr 1
    · congr 1
      funext v
      simp only [Fin.init, Equiv.piEquivPiSubtypeProd_symm_apply, mem_interval,
        Nat.zero_le, true_and, Fin.val_castSucc, ra, rb]
    · simp [Equiv.piEquivPiSubtypeProd_symm_apply, hlast]
  rw [hcut]
  refine ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)).trans ?_
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hjn) with hjn' | rfl
  · exact hW.rank_cutMatrix_le hj0 hjn'
  · exact (rank_cutMatrix_le_one_of_le le_rfl W).trans hb

end TNLean.MPS.AreaLaw

end

section

open ManyBody (cutMatrix)

namespace TNLean.MPS.AreaLaw

/-- Extend an interval state by a fixed configuration on its complement, with
open-boundary bond bound `max 1 D`. The cut-rank argument also includes empty
and one-site intervals. This is elementary cut-movement algebra used in ALVV,
arXiv:1602.08828v2, Proposition 5.7, `prop:Cheby-AGSP-eff`, line 1332. -/
theorem IsOpenMPS.extend_interval_by_configuration {T L q D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) (a : ℕ) (ha : a + L ≤ T)
    (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q) :
    IsOpenMPS T q (max 1 D) (fun σ ↦
      if (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ σ v.val) = η
      then ψ (fun r : Fin L ↦ σ ⟨a + r.val, by omega⟩) else 0) := by
  classical
  let χ : EuclideanSpace ℂ (Fin T → Fin q) := WithLp.toLp 2 fun σ ↦
    if (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ σ v.val) = η
    then ψ (fun r : Fin L ↦ σ ⟨a + r.val, by omega⟩) else 0
  change IsOpenMPS T q (max 1 D) (fun σ ↦ χ σ)
  apply isOpenMPS_of_internal_cutMatrix_rank_le χ
  intro j _ _
  let k := min L (j - a)
  have hcut (r : Fin L) : r.val < k ↔ a + r.val < j := by
    change r.val < min L (j - a) ↔ a + r.val < j
    rw [lt_min_iff]
    omega
  let f : ((v : {v : Fin T // v ∈ interval T 0 j}) → Fin q) →
      ((v : {v : Fin L // v ∈ interval L 0 k}) → Fin q) := fun x r ↦
    x ⟨⟨a + r.val.val, by omega⟩,
      mem_interval.mpr ⟨Nat.zero_le _, (hcut r.val).mp (mem_interval.mp r.property).2⟩⟩
  let g : ((v : {v : Fin T // v ∉ interval T 0 j}) → Fin q) →
      ((v : {v : Fin L // v ∉ interval L 0 k}) → Fin q) := fun y r ↦
    y ⟨⟨a + r.val.val, by omega⟩, by
      intro hr
      exact r.property (mem_interval.mpr ⟨Nat.zero_le _, (hcut r.val).mpr (mem_interval.mp hr).2⟩)⟩
  let P := fun x : ((v : {v : Fin T // v ∈ interval T 0 j}) → Fin q) ↦
    ∀ (v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)})
      (hv : v.val ∈ interval T 0 j), x ⟨v.val, hv⟩ = η v
  let Q := fun y : ((v : {v : Fin T // v ∉ interval T 0 j}) → Fin q) ↦
    ∀ (v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)})
      (hv : v.val ∉ interval T 0 j), y ⟨v.val, hv⟩ = η v
  let u := fun x ↦ if P x then (1 : ℂ) else 0
  let v := fun y ↦ if Q y then (1 : ℂ) else 0
  let M := (cutMatrix (interval L 0 k) ψ).submatrix f g
  have hfactor : cutMatrix (interval T 0 j) χ = Matrix.diagonal u * M * Matrix.diagonal v := by
    ext x y
    have hmatch :
        (fun w : {w : Fin T // ¬(a ≤ w.val ∧ w.val < a + L)} ↦
          (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval T 0 j)).symm (x, y) w.val) = η
        ↔ P x ∧ Q y := by
      constructor
      · intro h
        constructor
        · intro w hw
          have he := congrFun h w
          rw [ManyBody.cutEquiv_symm_apply_mem (X := fun _ ↦ Fin q) x y hw] at he
          exact he
        · intro w hw
          have he := congrFun h w
          rw [ManyBody.cutEquiv_symm_apply_not_mem (X := fun _ ↦ Fin q) x y hw] at he
          exact he
      · rintro ⟨hp, hq⟩
        funext w
        by_cases hw : w.val ∈ interval T 0 j
        · rw [ManyBody.cutEquiv_symm_apply_mem (X := fun _ ↦ Fin q) x y hw]
          exact hp w hw
        · rw [ManyBody.cutEquiv_symm_apply_not_mem (X := fun _ ↦ Fin q) x y hw]
          exact hq w hw
    have hcore :
        (fun r : Fin L ↦
          (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval T 0 j)).symm (x, y)
            ⟨a + r.val, by omega⟩) =
          (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 k)).symm (f x, g y) := by
      funext r
      by_cases hr : r ∈ interval L 0 k
      · have hv : (⟨a + r.val, by omega⟩ : Fin T) ∈ interval T 0 j :=
          mem_interval.mpr ⟨Nat.zero_le _, (hcut r).mp (mem_interval.mp hr).2⟩
        rw [ManyBody.cutEquiv_symm_apply_mem (X := fun _ ↦ Fin q) x y hv,
          ManyBody.cutEquiv_symm_apply_mem (X := fun _ ↦ Fin q) (f x) (g y) hr]
      · have hv : (⟨a + r.val, by omega⟩ : Fin T) ∉ interval T 0 j := by
          intro hv
          exact hr (mem_interval.mpr ⟨Nat.zero_le _, (hcut r).mpr (mem_interval.mp hv).2⟩)
        rw [ManyBody.cutEquiv_symm_apply_not_mem (X := fun _ ↦ Fin q) x y hv,
          ManyBody.cutEquiv_symm_apply_not_mem (X := fun _ ↦ Fin q) (f x) (g y) hr]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, ManyBody.cutMatrix_apply]
    change (if
      (fun w : {w : Fin T // ¬(a ≤ w.val ∧ w.val < a + L)} ↦
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval T 0 j)).symm (x, y) w.val) = η
      then ψ (fun r : Fin L ↦
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval T 0 j)).symm (x, y)
          ⟨a + r.val, by omega⟩) else 0) =
        (if P x then 1 else 0) * (cutMatrix (interval L 0 k) ψ) (f x) (g y) * (if Q y then 1 else 0)
    simp only [hmatch, hcore, ManyBody.cutMatrix_apply]
    by_cases hp : P x <;> by_cases hq : Q y <;> simp [hp, hq]
  have hrank : (cutMatrix (interval T 0 j) χ).rank ≤ (cutMatrix (interval L 0 k) ψ).rank := by
    rw [hfactor]
    exact ((Matrix.rank_mul_le_left (Matrix.diagonal u * M) (Matrix.diagonal v)).trans
      (Matrix.rank_mul_le_right (Matrix.diagonal u) M)).trans
        (Matrix.rank_submatrix_le (cutMatrix (interval L 0 k) ψ) f g)
  apply hrank.trans
  by_cases hk0 : k = 0
  · rw [hk0]
    exact (rank_cutMatrix_zero_le ψ).trans (le_max_left 1 D)
  · by_cases hkL : L ≤ k
    · exact (rank_cutMatrix_le_one_of_le hkL ψ).trans (le_max_left 1 D)
    · exact (hψ.rank_cutMatrix_le (Nat.pos_of_ne_zero hk0) (lt_of_not_ge hkL)).trans
        (le_max_right 1 D)

end TNLean.MPS.AreaLaw

end

section

open Matrix
open ManyBody (cutMatrix)

namespace TNLean.MPS.AreaLaw

/-- Applying an operator increases a cut rank by at most its operator-Schmidt rank.
LVV13, arXiv:1307.5143v1, `algo53.tex`, Claim `c:errorreduction`, lines 584–591. -/
theorem rank_cutMatrix_toEuclideanLin_le_operatorSchmidtRank_mul {L q : ℕ}
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ) :
    (cutMatrix (interval L 0 k) (toEuclideanLin K ψ)).rank ≤
      operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) K) *
        (cutMatrix (interval L 0 k) ψ).rank := by
  rw [cutMatrix_toEuclideanLin]
  exact Matrix.schmidtRank_mulVec_le _ _

/-- An operator with operator-Schmidt rank at most `D` at each internal cut multiplies an
MPS bond bound by at most `D`. LVV13, arXiv:1307.5143v1, `algo53.tex`, Claim
`c:errorreduction`, lines 580–592. -/
theorem IsOpenMPS.toEuclideanLin {L q b D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q b (fun x ↦ ψ x))
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hK : ∀ k : ℕ, 0 < k → k < L →
      operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) K) ≤ D) :
    IsOpenMPS L q (D * b) (fun x ↦ toEuclideanLin K ψ x) := by
  apply isOpenMPS_of_internal_cutMatrix_rank_le
  intro k hk0 hkL
  exact (rank_cutMatrix_toEuclideanLin_le_operatorSchmidtRank_mul K ψ k).trans
    (Nat.mul_le_mul (hK k hk0 hkL) (hψ.rank_cutMatrix_le hk0 hkL))

end TNLean.MPS.AreaLaw

end

section

open Matrix
open ManyBody (cutMatrix)

namespace TNLean.MPS.AreaLaw

/-- A vector in the span of `S` has bond dimension at most `S.card * D` if each member of
`S` has bond dimension at most `D`. This is the finite-span estimate in LVV13,
`algo53.tex`, Claim `c:2`, lines 520–527. No normalization or positivity of `D` is required. -/
theorem isOpenMPS_of_mem_span {L q D : ℕ}
    (S : Finset ((Fin L → Fin q) → ℂ))
    (hS : ∀ w ∈ S, IsOpenMPS L q D w) {v : (Fin L → Fin q) → ℂ}
    (hv : v ∈ Submodule.span ℂ (S : Set ((Fin L → Fin q) → ℂ))) :
    IsOpenMPS L q (S.card * D) v := by
  classical
  obtain ⟨a, -, rfl⟩ := Submodule.mem_span_finset.mp hv
  apply (isOpenMPS_iff_internal_cutMatrix_rank_le
    (WithLp.toLp 2 (∑ w ∈ S, a w • w))).mpr
  intro k hk0 hkL
  let A := fun w : (Fin L → Fin q) → ℂ ↦ a w • cutMatrix (interval L 0 k) (WithLp.toLp 2 w)
  have hcut : cutMatrix (interval L 0 k) (WithLp.toLp 2 (∑ w ∈ S, a w • w)) =
      ∑ w ∈ S, A w := by
    ext p r
    simp [A, ManyBody.cutMatrix_apply, Finset.sum_apply, Matrix.sum_apply]
  rw [hcut]
  have hA (w) (hw : w ∈ S) : (A w).rank ≤ D := by
    by_cases ha : a w = 0
    · simp [A, ha]
    · simpa only [A, rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero ha)] using
        (hS w hw).rank_cutMatrix_le (ψ := WithLp.toLp 2 w) hk0 hkL
  have hr := LinearMap.rank_finsetSum_le S (fun w ↦ Matrix.toLin' (A w))
  have hcard (w) (hw : w ∈ S) : (Matrix.toLin' (A w)).rank ≤ (D : Cardinal) := by
    rw [LinearMap.rank, ← Module.finrank_eq_rank', Matrix.toLin'_apply']
    exact_mod_cast hA w hw
  have hsum : (∑ w ∈ S, Matrix.toLin' (A w)).rank ≤
      ((S.card * D : ℕ) : Cardinal) := by
    simpa using hr.trans (Finset.sum_le_sum hcard)
  rw [← map_sum] at hsum
  convert (Cardinal.toNat_le_toNat hsum Cardinal.natCast_lt_aleph0) using 1
  all_goals simp only [Matrix.rank, Module.finrank, LinearMap.rank,
    Matrix.toLin'_apply', Cardinal.toNat_natCast]
  congr 3

/-- A vector in the span of a finite indexed family of MPS has the family
cardinality times their common bond bound. Repeated and zero family members
are allowed. LVV13, arXiv:1307.5143v1, Claim `c:2`, lines 520–527. -/
theorem isOpenMPS_of_mem_span_range {L q D : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → ((Fin L → Fin q) → ℂ)) (hu : ∀ i, IsOpenMPS L q D (u i))
    {v : (Fin L → Fin q) → ℂ} (hv : v ∈ Submodule.span ℂ (Set.range u)) :
    IsOpenMPS L q (Fintype.card ι * D) v := by
  classical
  let S : Finset ((Fin L → Fin q) → ℂ) := Finset.univ.image u
  have hset : (S : Set ((Fin L → Fin q) → ℂ)) = Set.range u := by
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hS : ∀ w ∈ S, IsOpenMPS L q D w := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    exact hu i
  have hcard : S.card ≤ Fintype.card ι := by
    simpa only [Finset.card_univ] using (Finset.card_image_le (s := Finset.univ) (f := u))
  have hv' : v ∈ Submodule.span ℂ (S : Set ((Fin L → Fin q) → ℂ)) := by
    simpa only [hset] using hv
  exact (isOpenMPS_of_mem_span S hS hv').mono (Nat.mul_le_mul_right D hcard)

end TNLean.MPS.AreaLaw

end
