import TNLean.PEPS.CycleMPSTensor
import TNLean.PEPS.RegionBlock.Basic
import TNLean.Algebra.TracePairing

/-!
# Arc injectivity of the cycle tensor from block injectivity of the MPS tensor

The closed-chain corollaries of the Fundamental Theorem for normal PEPS
(arXiv:1804.04964, Section 3, lines 1585--1668 of
`Papers/1804.04964/paper_normal.tex`) hypothesize that blocking any `L`
consecutive sites of the matrix product state gives an injective tensor.  For
one site-independent tensor this is `L`-block injectivity in the matrix
language of the development's MPS chapters (`MPSTensor.IsNBlkInjective`): the
word products of length `L` span the full matrix algebra.  This file proves
that `L`-block injectivity of the matrix tensor gives blocked-region linear
independence of its cycle tensor on every arc of `L` consecutive sites
(`regionBlockedTensorInjective_cycleTensorOfMPS`), the hypothesis consumed by
the graph-level corollary `fundamentalTheorem_normalMPS_cycle`.

The proof identifies the blocked tensor of an arc with the matrix products of
the words read along the arc.  An arc of `L < n` consecutive sites has exactly
two boundary-crossing bonds, the bond entering its first site and the bond
leaving its last site (`isRegionBoundaryEdge_cycleArcFrom_iff`); the blocked
weight of the arc at a boundary assignment `(a, b)` and a physical word `x`
is the matrix-product entry `(A^{x_0} ⋯ A^{x_{L-1}})_{a b}`, repeated once for
each free assignment of the `n - (L + 1)` bonds away from the arc
(`regionBlockedWeight_cycleTensorOfMPS`).  Linear independence of these
entry families over the boundary pairs is the nondegeneracy of the trace
pairing against the spanning word products
(`matrix_eq_zero_of_isNBlkInjective`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, corollaries after the theorem labelled `normal`, lines
  1585--1668 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace TNLean
namespace PEPS

variable {n d D : ℕ}

section ArcGeometry

variable [NeZero n]

/-- The site of the arc starting at `s` at offset `j`. -/
def arcSite {L : ℕ} (hLn : L < n) (s : Fin n) (j : Fin L) : Fin n :=
  s + ⟨j.val, lt_trans j.isLt hLn⟩

theorem arcSite_mem {L : ℕ} (hLn : L < n) (s : Fin n) (j : Fin L) :
    arcSite hLn s j ∈ cycleArcFrom s L := by
  rw [mem_cycleArcFrom]
  show (s + ⟨j.val, lt_trans j.isLt hLn⟩ - s).val < L
  rw [add_sub_cancel_left]
  exact j.isLt

/-- The word of physical indices read along the arc starting at `s`. -/
def arcWord {L : ℕ} (hLn : L < n) (s : Fin n)
    (τ : RegionPhysicalConfig (V := Fin n) (d := d) (cycleArcFrom s L)) : Fin L → Fin d :=
  fun j => τ ⟨arcSite hLn s j, arcSite_mem hLn s j⟩

/-- The last site of the arc of `L` consecutive sites starting at `s`. -/
def arcLastSite {L : ℕ} (hL : 0 < L) (hLn : L < n) (s : Fin n) : Fin n :=
  s + ⟨L - 1, by omega⟩

/-- The sites of the arc, enumerated in arc order. -/
def arcSiteEquiv {L : ℕ} (hLn : L < n) (s : Fin n) :
    Fin L ≃ {w : Fin n // w ∈ cycleArcFrom s L} where
  toFun j := ⟨arcSite hLn s j, arcSite_mem hLn s j⟩
  invFun w := ⟨(w.1 - s).val, mem_cycleArcFrom.mp w.2⟩
  left_inv j := by
    apply Fin.ext
    show ((s + ⟨j.val, lt_trans j.isLt hLn⟩ - s : Fin n)).val = j.val
    rw [add_sub_cancel_left]
  right_inv w := by
    apply Subtype.ext
    show s + (⟨(w.1 - s).val, _⟩ : Fin n) = w.1
    rw [show (⟨(w.1 - s).val, lt_trans (mem_cycleArcFrom.mp w.2) hLn⟩ : Fin n) = w.1 - s from
      Fin.ext rfl, add_comm, sub_add_cancel]

/-!
### The two boundary bonds of an arc

An arc of `L < n` consecutive sites has exactly two boundary-crossing bonds:
the bond entering its first site and the bond leaving its last site.
-/

/-- A successor bond crosses the boundary of the arc exactly when it enters
the first site or leaves the last site. -/
theorem isRegionBoundaryEdge_cycleSuccEdge_iff (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L)
    (hLn : L < n) (s u : Fin n) :
    IsRegionBoundaryEdge (G := SimpleGraph.cycleGraph n) (cycleArcFrom s L)
        (cycleSuccEdge hn u) ↔
      u = s - 1 ∨ u = arcLastSite hL hLn s := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hu := u.isLt
  have hs := s.isLt
  -- The crossing condition sees the two cyclic endpoints `u` and `u + 1`,
  -- in either stored order.
  have hmem : IsRegionBoundaryEdge (G := SimpleGraph.cycleGraph n) (cycleArcFrom s L)
      (cycleSuccEdge hn u) ↔
      ((u ∈ cycleArcFrom s L ∧ u + 1 ∉ cycleArcFrom s L) ∨
        (u ∉ cycleArcFrom s L ∧ u + 1 ∈ cycleArcFrom s L)) := by
    rcases (show u.val + 1 < n ∨ u.val + 1 = n by omega) with hc | hc
    · have h11 : (cycleSuccEdge hn u).1.1 = u := by rw [cycleSuccEdge_val_of_lt hn hc]
      have h12 : (cycleSuccEdge hn u).1.2 = u + 1 := by rw [cycleSuccEdge_val_of_lt hn hc]
      unfold IsRegionBoundaryEdge
      rw [h11, h12]
    · have h11 : (cycleSuccEdge hn u).1.1 = u + 1 := by rw [cycleSuccEdge_val_of_eq hn hc]
      have h12 : (cycleSuccEdge hn u).1.2 = u := by rw [cycleSuccEdge_val_of_eq hn hc]
      unfold IsRegionBoundaryEdge
      rw [h11, h12]
      tauto
  rw [hmem, arcLastSite]
  simp only [mem_cycleArcFrom, not_lt, Fin.ext_iff, val_sub_eq_ite, Fin.val_add_eq_ite, h1]
  split_ifs <;> omega

/-- The boundary-crossing bonds of an arc of `L < n` consecutive sites are the
bond entering its first site and the bond leaving its last site. -/
theorem isRegionBoundaryEdge_cycleArcFrom_iff (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L)
    (hLn : L < n) (s : Fin n) (f : Edge (SimpleGraph.cycleGraph n)) :
    IsRegionBoundaryEdge (G := SimpleGraph.cycleGraph n) (cycleArcFrom s L) f ↔
      f = cycleSuccEdge hn (s - 1) ∨ f = cycleSuccEdge hn (arcLastSite hL hLn s) := by
  obtain ⟨u, rfl⟩ := cycleSuccEdge_surjective hn f
  rw [isRegionBoundaryEdge_cycleSuccEdge_iff hn hL hLn s u]
  constructor
  · rintro (h | h) <;> [exact Or.inl (congrArg _ h); exact Or.inr (congrArg _ h)]
  · rintro (h | h) <;>
      [exact Or.inl (cycleSuccEdge_injective hn h); exact Or.inr (cycleSuccEdge_injective hn h)]

/-- The two boundary bonds of an arc are distinct. -/
theorem arcLastSite_ne_pred (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n) (s : Fin n) :
    arcLastSite hL hLn s ≠ s - 1 := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hs := s.isLt
  intro h
  have hval := congrArg Fin.val h
  rw [arcLastSite] at hval
  simp only [val_sub_eq_ite, Fin.val_add_eq_ite, h1] at hval
  split_ifs at hval <;> omega

/-- The boundary bond entering the first site of the arc, as a boundary edge. -/
def arcLeftBoundary (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n) (s : Fin n) :
    {f : Edge (SimpleGraph.cycleGraph n) //
      IsRegionBoundaryEdge (G := SimpleGraph.cycleGraph n) (cycleArcFrom s L) f} :=
  ⟨cycleSuccEdge hn (s - 1),
    (isRegionBoundaryEdge_cycleArcFrom_iff hn hL hLn s _).mpr (Or.inl rfl)⟩

/-- The boundary bond leaving the last site of the arc, as a boundary edge. -/
def arcRightBoundary (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n) (s : Fin n) :
    {f : Edge (SimpleGraph.cycleGraph n) //
      IsRegionBoundaryEdge (G := SimpleGraph.cycleGraph n) (cycleArcFrom s L) f} :=
  ⟨cycleSuccEdge hn (arcLastSite hL hLn s),
    (isRegionBoundaryEdge_cycleArcFrom_iff hn hL hLn s _).mpr (Or.inr rfl)⟩

/-- Every boundary edge of the arc is its left bond or its right bond. -/
theorem arcBoundary_eq_left_or_right (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n)
    (s : Fin n)
    (f : {f : Edge (SimpleGraph.cycleGraph n) //
      IsRegionBoundaryEdge (G := SimpleGraph.cycleGraph n) (cycleArcFrom s L) f}) :
    f = arcLeftBoundary hn hL hLn s ∨ f = arcRightBoundary hn hL hLn s := by
  rcases (isRegionBoundaryEdge_cycleArcFrom_iff hn hL hLn s f.1).mp f.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- The two boundary bonds of the arc are distinct boundary edges. -/
theorem arcRightBoundary_ne_leftBoundary (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n)
    (s : Fin n) :
    arcRightBoundary hn hL hLn s ≠ arcLeftBoundary hn hL hLn s := by
  intro h
  exact arcLastSite_ne_pred hn hL hLn s
    (cycleSuccEdge_injective hn (congrArg Subtype.val h))

end ArcGeometry

section BlockedWeight

variable [NeZero n]

/-!
### The blocked weight of an arc

The blocked weight of the arc at a boundary assignment and a physical
configuration is a matrix-product entry of the word read along the arc,
repeated once for each free assignment of the bonds away from the arc.
-/

/-- The sites of the bond window of the arc: the window holds the `L + 1`
bonds touching the arc, labelled by the site on whose successor side each
bond sits, starting at the bond entering the first site. -/
def arcWindowEquiv {L : ℕ} (hLn : L < n) :
    {u : Fin n // u.val < L + 1} ≃ Fin (L + 1) where
  toFun u := ⟨u.1.val, u.2⟩
  invFun t := ⟨⟨t.val, by omega⟩, t.isLt⟩
  left_inv u := Subtype.ext (Fin.ext rfl)
  right_inv t := Fin.ext rfl

/-- Splitting a cyclic bond assignment into the window of the `L + 1` bonds
touching the arc starting at `s` (translated to start at the bond entering
the first site) and the assignment of the remaining bonds. -/
def arcBondSplitEquiv {L : ℕ} (hLn : L < n) (s : Fin n) :
    (Fin n → Fin D) ≃
      ((Fin (L + 1) → Fin D) × ({u : Fin n // ¬ u.val < L + 1} → Fin D)) :=
  (Equiv.arrowCongr (Equiv.addLeft (s - 1)).symm (Equiv.refl (Fin D))).trans
    ((Equiv.piEquivPiSubtypeProd (fun u : Fin n => u.val < L + 1) (fun _ => Fin D)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (arcWindowEquiv hLn) (Equiv.refl (Fin D))) (Equiv.refl _)))

/-- The window component of a split bond assignment reads the original
assignment at the translated bond. -/
theorem arcBondSplitEquiv_fst_apply {L : ℕ} (hLn : L < n) (s : Fin n)
    (g : Fin n → Fin D) (t : Fin (L + 1)) :
    (arcBondSplitEquiv hLn s g).1 t = g (s - 1 + ⟨t.val, by omega⟩) := rfl

omit [NeZero n] in
/-- The number of bonds away from the arc window. -/
theorem card_arcComplement {L : ℕ} (hLn : L < n) :
    Fintype.card {u : Fin n // ¬ u.val < L + 1} = n - (L + 1) := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_congr (arcWindowEquiv (n := n) hLn), Fintype.card_fin]

/-- **The blocked weight of an arc is a matrix-product entry.**  At a boundary
assignment `bdry` and a physical configuration `τ`, the blocked weight of the
arc of `L` consecutive sites starting at `s` is the entry of the word product
of `A` along the arc at the two boundary bond indices, times one factor `D`
for each of the `n - (L + 1)` bonds away from the arc.

Source: arXiv:1804.04964, Section 3, lines 1585--1668 of
`Papers/1804.04964/paper_normal.tex`: blocking `L` consecutive sites of an
MPS gives the tensor whose components are the matrix products
`A^{x_1} ⋯ A^{x_L}` with the two outer bonds open. -/
theorem regionBlockedWeight_cycleTensorOfMPS (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L)
    (hLn : L < n) (A : MPSTensor d D) (s : Fin n)
    (bdry : RegionBoundaryConfig (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
      (cycleArcFrom s L))
    (τ : RegionPhysicalConfig (V := Fin n) (d := d) (cycleArcFrom s L)) :
    regionBlockedWeight (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
        (cycleArcFrom s L) bdry τ =
      (D : ℂ) ^ (n - (L + 1)) *
        MPSTensor.evalWord A (List.ofFn (arcWord hLn s τ))
          (bdry (arcLeftBoundary hn hL hLn s)) (bdry (arcRightBoundary hn hL hLn s)) := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hs := s.isLt
  set a := bdry (arcLeftBoundary hn hL hLn s) with ha
  set b := bdry (arcRightBoundary hn hL hLn s) with hb
  set x := arcWord hLn s τ with hx
  -- Pointwise bond relabelling under the translation by `s - 1`.
  have hshift0 : s - 1 + (⟨(0 : Fin (L + 1)).val, by omega⟩ : Fin n) = s - 1 := by
    apply Fin.ext
    simp only [Fin.val_zero, Fin.val_add_eq_ite, val_sub_eq_ite, h1]
    split_ifs <;> omega
  have hshiftL : s - 1 + (⟨(Fin.last L).val, by omega⟩ : Fin n) = arcLastSite hL hLn s := by
    apply Fin.ext
    rw [arcLastSite]
    simp only [Fin.val_last, Fin.val_add_eq_ite, val_sub_eq_ite, h1]
    split_ifs <;> omega
  have hshiftCast : ∀ j : Fin L,
      s - 1 + (⟨(j.castSucc).val, by omega⟩ : Fin n) = arcSite hLn s j - 1 := by
    intro j
    apply Fin.ext
    rw [arcSite]
    simp only [Fin.val_castSucc, Fin.val_add_eq_ite, val_sub_eq_ite, h1]
    split_ifs <;> omega
  have hshiftSucc : ∀ j : Fin L,
      s - 1 + (⟨(j.succ).val, by omega⟩ : Fin n) = arcSite hLn s j := by
    intro j
    apply Fin.ext
    rw [arcSite]
    simp only [Fin.val_succ, Fin.val_add_eq_ite, val_sub_eq_ite, h1]
    split_ifs <;> omega
  calc (regionBlockedWeight (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
        (cycleArcFrom s L) bdry τ)
      = ∑ ζ : VirtualConfig (cycleTensorOfMPS hn A),
          if regionBoundaryLabel (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
              (cycleArcFrom s L) ζ = bdry then
            ∏ w : {w : Fin n // w ∈ cycleArcFrom s L},
              (cycleTensorOfMPS hn A).component w.1 (fun ie => ζ ie.1) (τ w)
          else 0 := by
        rw [regionBlockedWeight, Finset.sum_filter]
    _ = ∑ ζ : VirtualConfig (cycleTensorOfMPS hn A),
          if ζ (cycleSuccEdge hn (s - 1)) = a ∧
              ζ (cycleSuccEdge hn (arcLastSite hL hLn s)) = b then
            ∏ w : {w : Fin n // w ∈ cycleArcFrom s L},
              (cycleTensorOfMPS hn A).component w.1 (fun ie => ζ ie.1) (τ w)
          else 0 := by
        refine Finset.sum_congr rfl fun ζ _ => if_congr ?_ rfl rfl
        constructor
        · intro h
          exact ⟨congrFun h (arcLeftBoundary hn hL hLn s),
            congrFun h (arcRightBoundary hn hL hLn s)⟩
        · rintro ⟨hLft, hRgt⟩
          funext f
          rcases arcBoundary_eq_left_or_right hn hL hLn s f with rfl | rfl
          · exact hLft
          · exact hRgt
    _ = ∑ g : Fin n → Fin D,
          if g (s - 1) = a ∧ g (arcLastSite hL hLn s) = b then
            ∏ j : Fin L, A (x j) (g (arcSite hLn s j - 1)) (g (arcSite hLn s j))
          else 0 := by
        refine Fintype.sum_equiv
          (Equiv.arrowCongr (cycleEdgeEquiv hn).symm (Equiv.refl (Fin D))) _ _ fun ζ => ?_
        refine if_congr Iff.rfl ?_ rfl
        exact (Fintype.prod_equiv (arcSiteEquiv hLn s)
          (fun j => A (x j) (ζ (cycleSuccEdge hn (arcSite hLn s j - 1)))
            (ζ (cycleSuccEdge hn (arcSite hLn s j))))
          (fun w => (cycleTensorOfMPS hn A).component w.1 (fun ie => ζ ie.1) (τ w))
          (fun j => rfl)).symm
    _ = ∑ p : (Fin (L + 1) → Fin D) × ({u : Fin n // ¬ u.val < L + 1} → Fin D),
          if p.1 0 = a ∧ p.1 (Fin.last L) = b then
            ∏ j : Fin L, A (x j) (p.1 j.castSucc) (p.1 j.succ)
          else 0 := by
        refine Fintype.sum_equiv (arcBondSplitEquiv hLn s) _ _ fun g => ?_
        refine if_congr (and_congr ?_ ?_) (Finset.prod_congr rfl fun j _ => ?_) rfl
        · rw [arcBondSplitEquiv_fst_apply hLn s g 0, hshift0]
        · rw [arcBondSplitEquiv_fst_apply hLn s g (Fin.last L), hshiftL]
        · rw [arcBondSplitEquiv_fst_apply hLn s g j.castSucc,
            arcBondSplitEquiv_fst_apply hLn s g j.succ, hshiftCast j, hshiftSucc j]
    _ = ∑ ρ : Fin (L + 1) → Fin D,
          (D : ℂ) ^ (n - (L + 1)) *
            (if ρ 0 = a ∧ ρ (Fin.last L) = b then
              ∏ j : Fin L, A (x j) (ρ j.castSucc) (ρ j.succ)
            else 0) := by
        have hconst : ∀ c : ℂ,
            (∑ _y : {u : Fin n // ¬ u.val < L + 1} → Fin D, c) =
              (D : ℂ) ^ (n - (L + 1)) * c := by
          intro c
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, card_arcComplement hLn,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun ρ _ =>
          hconst (if ρ 0 = a ∧ ρ (Fin.last L) = b then
            ∏ j : Fin L, A (x j) (ρ j.castSucc) (ρ j.succ) else 0)
    _ = (D : ℂ) ^ (n - (L + 1)) *
          MPSTensor.evalWord A (List.ofFn x) a b := by
        rw [← Finset.mul_sum, MPSTensor.evalWord_ofFn_apply A L x a b]

end BlockedWeight

section InjectivityBridge

/-!
### From block injectivity to blocked-region linear independence

Block injectivity of the matrix tensor says the length-`L` word products span
the full matrix algebra; by the nondegeneracy of the trace pairing, the only
matrix of coefficients pairing to zero against all of them is zero.  Together
with the blocked-weight computation this gives the arc-injectivity hypothesis
of the closed-chain corollary.
-/

/-- A coefficient matrix pairing to zero against all length-`L` word products
of a block-injective tensor is zero.

Source: arXiv:1804.04964, Section 3, lines 1585--1668 of
`Papers/1804.04964/paper_normal.tex`: injectivity of the blocked tensor of
`L` consecutive sites, read through the nondegenerate trace pairing. -/
theorem matrix_eq_zero_of_isNBlkInjective {L : ℕ} {A : MPSTensor d D}
    (hA : MPSTensor.IsNBlkInjective A L) (C : Matrix (Fin D) (Fin D) ℂ)
    (hC : ∀ x : Fin L → Fin d,
      ∑ p : Fin D × Fin D, C p.1 p.2 * MPSTensor.evalWord A (List.ofFn x) p.1 p.2 = 0) :
    C = 0 := by
  classical
  -- The pairing against `C` is the trace pairing against `Cᵀ`.
  have hpair : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      Matrix.trace (Cᵀ * M) = ∑ p : Fin D × Fin D, C p.1 p.2 * M p.1 p.2 := by
    intro M
    rw [Fintype.sum_prod_type]
    calc Matrix.trace (Cᵀ * M)
        = ∑ a : Fin D, ∑ b : Fin D, Cᵀ a b * M b a := by
          simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      _ = ∑ a : Fin D, ∑ b : Fin D, C b a * M b a := by
          simp [Matrix.transpose_apply]
      _ = ∑ b : Fin D, ∑ a : Fin D, C b a * M b a := Finset.sum_comm
  -- The trace functional against `Cᵀ` vanishes on a spanning set, hence everywhere.
  have hker : ∀ M : Matrix (Fin D) (Fin D) ℂ, Matrix.trace (Cᵀ * M) = 0 := by
    intro M
    have hM : M ∈ Submodule.span ℂ (Set.range fun x : Fin L → Fin d =>
        MPSTensor.evalWord A (List.ofFn x)) := by
      rw [hA]; exact Submodule.mem_top
    have hle : Submodule.span ℂ (Set.range fun x : Fin L → Fin d =>
        MPSTensor.evalWord A (List.ofFn x)) ≤
        LinearMap.ker ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          (LinearMap.mulLeft ℂ Cᵀ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.mulLeft_apply, Matrix.traceLinearMap_apply]
      rw [hpair]
      exact hC x
    simpa using hle hM
  have hCt : Cᵀ = 0 := MPSTensor.trace_mul_right_eq_zero hker
  simpa using congrArg Matrix.transpose hCt

variable [NeZero n]

/-- The boundary assignment of the arc taking value `a` on the bond entering
its first site and `b` on the bond leaving its last site. -/
def arcBoundaryConfig (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n)
    (A : MPSTensor d D) (s : Fin n) (a b : Fin D) :
    RegionBoundaryConfig (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
      (cycleArcFrom s L) :=
  fun f => if f = arcLeftBoundary hn hL hLn s then a else b

@[simp] theorem arcBoundaryConfig_left (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n)
    (A : MPSTensor d D) (s : Fin n) (a b : Fin D) :
    arcBoundaryConfig hn hL hLn A s a b (arcLeftBoundary hn hL hLn s) = a :=
  if_pos rfl

@[simp] theorem arcBoundaryConfig_right (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n)
    (A : MPSTensor d D) (s : Fin n) (a b : Fin D) :
    arcBoundaryConfig hn hL hLn A s a b (arcRightBoundary hn hL hLn s) = b :=
  if_neg (arcRightBoundary_ne_leftBoundary hn hL hLn s)

/-- A boundary assignment of the arc is determined by its two bond values. -/
theorem arcBoundaryConfig_recon (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L) (hLn : L < n)
    (A : MPSTensor d D) (s : Fin n)
    (bdry : RegionBoundaryConfig (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
      (cycleArcFrom s L)) :
    arcBoundaryConfig hn hL hLn A s (bdry (arcLeftBoundary hn hL hLn s))
      (bdry (arcRightBoundary hn hL hLn s)) = bdry := by
  funext f
  rcases arcBoundary_eq_left_or_right hn hL hLn s f with rfl | rfl
  · exact arcBoundaryConfig_left hn hL hLn A s _ _
  · exact arcBoundaryConfig_right hn hL hLn A s _ _

/-- **Arc injectivity of the cycle tensor from block injectivity.**  If the
length-`L` word products of `A` span the full matrix algebra, then the blocked
tensor of every arc of `L` consecutive sites of the cycle tensor of `A` is
injective.  This produces the arc-injectivity hypothesis of the closed-chain
corollary from the matrix-level hypothesis of the source.

Source: arXiv:1804.04964, Section 3, lines 1585--1668 of
`Papers/1804.04964/paper_normal.tex`: "blocking any `L` consecutive sites
results in an injective tensor", read for one site-independent tensor. -/
theorem regionBlockedTensorInjective_cycleTensorOfMPS (hn : 3 ≤ n) {L : ℕ} (hL : 0 < L)
    (hLn : L < n) (hD : 0 < D) {A : MPSTensor d D}
    (hA : MPSTensor.IsNBlkInjective A L) (s : Fin n) :
    RegionBlockedTensorInjective (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
      (cycleArcFrom s L) := by
  classical
  rw [RegionBlockedTensorInjective, Fintype.linearIndependent_iff]
  intro c hc bdry
  -- The coefficients form a matrix over the two boundary bond indices.
  set C : Matrix (Fin D) (Fin D) ℂ :=
    fun a b => c (arcBoundaryConfig hn hL hLn A s a b) with hCdef
  -- The boundary assignments are in bijection with the pairs of bond values.
  have hbij : Function.Bijective (fun p : Fin D × Fin D =>
      arcBoundaryConfig hn hL hLn A s p.1 p.2) := by
    constructor
    · intro p q hpq
      have h1 := congrFun hpq (arcLeftBoundary hn hL hLn s)
      have h2 := congrFun hpq (arcRightBoundary hn hL hLn s)
      simp only [arcBoundaryConfig_left] at h1
      simp only [arcBoundaryConfig_right] at h2
      exact Prod.ext h1 h2
    · intro bdry'
      exact ⟨(bdry' (arcLeftBoundary hn hL hLn s), bdry' (arcRightBoundary hn hL hLn s)),
        arcBoundaryConfig_recon hn hL hLn A s bdry'⟩
  -- The linear relation pairs `C` to zero against every word product.
  have hzero : ∀ x : Fin L → Fin d,
      ∑ p : Fin D × Fin D, C p.1 p.2 * MPSTensor.evalWord A (List.ofFn x) p.1 p.2 = 0 := by
    intro x
    set τ : RegionPhysicalConfig (V := Fin n) (d := d) (cycleArcFrom s L) :=
      fun w => x ⟨(w.1 - s).val, mem_cycleArcFrom.mp w.2⟩ with hτ
    have hword : arcWord hLn s τ = x := by
      funext j
      show x ⟨((arcSite hLn s j : Fin n) - s).val, _⟩ = x j
      refine congrArg x (Fin.ext ?_)
      show ((s + ⟨j.val, lt_trans j.isLt hLn⟩ - s : Fin n)).val = j.val
      rw [add_sub_cancel_left]
    have hcτ : ∑ bdry' : RegionBoundaryConfig (G := SimpleGraph.cycleGraph n)
        (cycleTensorOfMPS hn A) (cycleArcFrom s L),
        c bdry' * regionBlockedTensorFamily (G := SimpleGraph.cycleGraph n)
          (cycleTensorOfMPS hn A) (cycleArcFrom s L) bdry' τ = 0 := by
      have hfun := congrFun hc τ
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hfun
    have hEq := Fintype.sum_equiv (Equiv.ofBijective _ hbij)
      (fun p : Fin D × Fin D =>
        c (arcBoundaryConfig hn hL hLn A s p.1 p.2) *
          regionBlockedTensorFamily (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
            (cycleArcFrom s L) (arcBoundaryConfig hn hL hLn A s p.1 p.2) τ)
      (fun bdry' =>
        c bdry' * regionBlockedTensorFamily (G := SimpleGraph.cycleGraph n)
          (cycleTensorOfMPS hn A) (cycleArcFrom s L) bdry' τ)
      (fun p => rfl)
    have hpairs : ∑ p : Fin D × Fin D,
        c (arcBoundaryConfig hn hL hLn A s p.1 p.2) *
          regionBlockedTensorFamily (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
            (cycleArcFrom s L) (arcBoundaryConfig hn hL hLn A s p.1 p.2) τ = 0 :=
      hEq.trans hcτ
    have hexp : ∀ p : Fin D × Fin D,
        c (arcBoundaryConfig hn hL hLn A s p.1 p.2) *
          regionBlockedTensorFamily (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
            (cycleArcFrom s L) (arcBoundaryConfig hn hL hLn A s p.1 p.2) τ =
        (D : ℂ) ^ (n - (L + 1)) *
          (C p.1 p.2 * MPSTensor.evalWord A (List.ofFn x) p.1 p.2) := by
      intro p
      have hwt := regionBlockedWeight_cycleTensorOfMPS hn hL hLn A s
        (arcBoundaryConfig hn hL hLn A s p.1 p.2) τ
      rw [arcBoundaryConfig_left, arcBoundaryConfig_right, hword] at hwt
      calc c (arcBoundaryConfig hn hL hLn A s p.1 p.2) *
          regionBlockedTensorFamily (G := SimpleGraph.cycleGraph n) (cycleTensorOfMPS hn A)
            (cycleArcFrom s L) (arcBoundaryConfig hn hL hLn A s p.1 p.2) τ
          = C p.1 p.2 * ((D : ℂ) ^ (n - (L + 1)) *
              MPSTensor.evalWord A (List.ofFn x) p.1 p.2) := by rw [← hwt]; rfl
        _ = (D : ℂ) ^ (n - (L + 1)) *
              (C p.1 p.2 * MPSTensor.evalWord A (List.ofFn x) p.1 p.2) := by ring
    have hfactored : (D : ℂ) ^ (n - (L + 1)) *
        ∑ p : Fin D × Fin D, C p.1 p.2 * MPSTensor.evalWord A (List.ofFn x) p.1 p.2 = 0 := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_congr rfl fun p _ => hexp p]
      exact hpairs
    rcases mul_eq_zero.mp hfactored with h | h
    · exact absurd h (pow_ne_zero _ (Nat.cast_ne_zero.mpr hD.ne'))
    · exact h
  have hC0 : C = 0 := matrix_eq_zero_of_isNBlkInjective hA C hzero
  have hentry := congrFun (congrFun hC0 (bdry (arcLeftBoundary hn hL hLn s)))
    (bdry (arcRightBoundary hn hL hLn s))
  rw [← arcBoundaryConfig_recon hn hL hLn A s bdry]
  exact hentry

end InjectivityBridge

end PEPS
end TNLean
