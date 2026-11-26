/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.RetainedCoreFamilies
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.TraceCoreSlices
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.Product.ProductVector
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Placement.Basic
import QICLean.ManyBody.Entropy.Filter.OutputCovariance
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Finset.Nat
import TNLean.MPS.Operator.Periodic.TraceChainOperator
import QICLean.ManyBody.Sites.Placement.PlaceAlong
import QICLean.Analysis.Norm.PrincipalSubmatrixNorm

/-!
# Natural coordinates for physical interval operators

Increasing coordinates identify a physical interval with a finite initial
segment and identify the complement of a subinterval in those coordinates.
Padding the actual core tensors by identity letters represents their supported
extension, with the supplied closing matrix and virtual space unchanged.
A physical operator on the complementary sites becomes a retained matrix
tensored with the interior identity under the same coordinate identification.

Empty intervals and zero local dimensions are included whenever the stated
configurations exist. These are coordinate and contraction identities
supporting ALVV, arXiv:1602.08828v2, equation H-mid-cut and Proposition 5.7,
lines 810–821 and 1324–1333.

## Native restriction of a supported operator approximation

A fixed configuration outside an interval restricts an actual operator chain
to its native site coordinates. The virtual dimension is unchanged and
placing the restricted operator back on the original chain preserves the
approximation error. The source operator is genuinely supported on the
interval, rather than supplied with a native representation.

This is operator algebra for ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268.
-/

section

open ManyBody (card_interval_le interval interval_mono mem_interval)

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix
open TNLean.MPS.AreaLaw

noncomputable section

namespace MPOTensor

/-- Extend the actual ordered core tensors by identity letters on the
complementary sites. The supplied virtual dimension is unchanged.
Supporting the cut movement in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333. -/
def identityExtendInterval {T L q B : ℕ}
    (A : Fin L → MPOTensor q B) (a : ℕ) (_ha : a + L ≤ T) :
    Fin T → MPOTensor q B := fun v (i, j) ↦
  if h : a ≤ v.val ∧ v.val < a + L then
    A ⟨v.val - a, by omega⟩ (i, j)
  else if i = j then 1 else 0

/-- When the two physical configurations agree off the interval, the exterior
identity letters leave precisely the supplied ordered interior product.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem prod_identityExtendInterval_of_eq_outside {T L q B : ℕ}
    (A : Fin L → MPOTensor q B) (a : ℕ) (ha : a + L ≤ T)
    (σ τ : Fin T → Fin q)
    (h : ∀ v, (∀ r : Fin L, (⟨a + r.val, by omega⟩ : Fin T) ≠ v) → σ v = τ v) :
    (List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v, τ v))).prod =
      (List.ofFn (fun r : Fin L ↦
        A r ((σ ⟨a + r.val, by omega⟩), (τ ⟨a + r.val, by omega⟩)))).prod := by
  let f := List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v, τ v))
  have hp : f.take a = List.replicate a (1 : Matrix (Fin B) (Fin B) ℂ) := by
    apply List.ext_getElem
    · simp only [f, List.length_take, List.length_ofFn, List.length_replicate]
      omega
    · intro i hi hi'
      have hiA : i < a := by simpa only [List.length_replicate] using hi'
      have heq : σ ⟨i, by omega⟩ = τ ⟨i, by omega⟩ := h ⟨i, by omega⟩ (by
        intro r hr
        have he := congrArg Fin.val hr
        dsimp at he
        omega)
      simp only [f, List.getElem_take, List.getElem_ofFn, List.getElem_replicate]
      simp [identityExtendInterval, show ¬(a ≤ i ∧ i < a + L) by omega, heq]
  have hm : (f.drop a).take L = List.ofFn (fun r : Fin L ↦
      A r ((σ ⟨a + r.val, by omega⟩), (τ ⟨a + r.val, by omega⟩))) := by
    apply List.ext_getElem
    · simp only [f, List.length_take, List.length_drop, List.length_ofFn]
      omega
    · intro i hi hi'
      have hiL : i < L := by simpa only [List.length_ofFn] using hi'
      simp only [f, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      simp [identityExtendInterval,
        show a ≤ a + i ∧ a + i < a + L by omega]
  have hs : f.drop (a + L) =
      List.replicate (T - (a + L)) (1 : Matrix (Fin B) (Fin B) ℂ) := by
    apply List.ext_getElem
    · simp only [f, List.length_drop, List.length_ofFn, List.length_replicate]
    · intro i hi hi'
      have hiT : a + L + i < T := by
        have := hi'
        simp only [List.length_replicate] at this
        omega
      have heq : σ ⟨a + L + i, hiT⟩ = τ ⟨a + L + i, hiT⟩ :=
        h ⟨a + L + i, hiT⟩ (by
          intro r hr
          have he := congrArg Fin.val hr
          dsimp at he
          omega)
      simp only [f, List.getElem_drop, List.getElem_ofFn, List.getElem_replicate]
      simp [identityExtendInterval, heq]
  change f.prod = _
  rw [TNLean.MPS.AreaLaw.orderedProduct_partition_interval f a L, hp, hm, hs]
  simp

/-- The actual trace operator of the identity extension is the usual supported
operator on the full chain. Its closing matrix and bond dimension are exactly
those of the supplied core, including empty chains and zero dimensions.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem trace_identityExtendInterval_eq_placeAlong {T L q B : ℕ}
    (A : Fin L → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T) :
    (Matrix.of fun σ τ : Fin T → Fin q ↦ Matrix.trace (C *
      (List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v, τ v))).prod)) =
      ManyBody.placeAlong (X := fun _ ↦ Fin q) (ManyBody.chainWindow a ha)
        (Matrix.of fun σ τ : Fin L → Fin q ↦ Matrix.trace
          (C * (List.ofFn (fun v ↦ A v (σ v, τ v))).prod)) := by
  classical
  ext σ τ
  rw [ManyBody.placeAlong_apply]
  by_cases h : ∀ v, (∀ u, ManyBody.chainWindow a ha u ≠ v) → σ v = τ v
  · rw [ite_eq_left h]
    simp only [Matrix.of_apply]
    exact congrArg (fun P : Matrix (Fin B) (Fin B) ℂ ↦ Matrix.trace (C * P))
      (prod_identityExtendInterval_of_eq_outside A a ha σ τ h)
  · rw [ite_eq_right h]
    obtain ⟨v, hv, hne⟩ : ∃ v : Fin T,
        (∀ r : Fin L, ManyBody.chainWindow a ha r ≠ v) ∧ σ v ≠ τ v := by
      simpa only [not_forall, not_imp, exists_prop] using h
    have hout : ¬(a ≤ v.val ∧ v.val < a + L) := by
      intro hi
      apply hv ⟨v.val - a, by omega⟩
      apply Fin.ext
      change a + (v.val - a) = v.val
      omega
    have hz : identityExtendInterval A a ha v (σ v, τ v) = 0 := by
      simp [identityExtendInterval, hout, hne]
    have hmem : (0 : Matrix (Fin B) (Fin B) ℂ) ∈
        List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v, τ v)) := by
      simp only [List.mem_ofFn]
      exact ⟨v, hz⟩
    simp only [Matrix.of_apply, List.prod_eq_zero hmem, Matrix.mul_zero, Matrix.trace_zero]

end MPOTensor

namespace TNLean.MPS.AreaLaw

/-- Increasing coordinates on a chain interval whose endpoints lie in the chain.
Supporting the natural core ordering in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
def intervalShiftOrderIso {L a b : ℕ} (hab : a ≤ b) (hb : b ≤ L) :
    Fin (b - a) ≃o ↥(interval L a b) where
  toFun i := ⟨⟨a + i.val, by omega⟩,
    mem_interval.mpr (by change a ≤ a + i.val ∧ a + i.val < b; omega)⟩
  invFun x := ⟨x.val.val - a, by have hx := mem_interval.mp x.property; omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have hx := mem_interval.mp x.property
    dsimp
    omega
  map_rel_iff' := by
    intro i j
    change a + i.val ≤ a + j.val ↔ i.val ≤ j.val
    omega

/-- The literal inclusion of nested physical intervals is the natural coordinate
shift. Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1332–1333. -/
private theorem nestedInterval_inclusion_trans_shift {T c a b d : ℕ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T) :
    (intervalShiftOrderIso hab (hbd.trans hd)).toEquiv.toEmbedding.trans
        (⟨fun x : ↥(interval T a b) ↦
          (⟨x.val, mem_interval.mpr (by
            have hx := mem_interval.mp x.property
            constructor <;> omega)⟩ : ↥(interval T c d)),
          fun x y hxy ↦ Subtype.ext (by have h := congrArg Subtype.val hxy; exact h)⟩ :
          ↥(interval T a b) ↪ ↥(interval T c d)) =
      (ManyBody.chainWindow (a - c) (show a - c + (b - a) ≤ d - c by omega)).trans
        (intervalShiftOrderIso (show c ≤ d by omega) hd).toEquiv.toEmbedding := by
  refine Function.Embedding.ext fun i ↦ ?_
  apply Subtype.ext
  apply Fin.ext
  change a + i.val = c + (a - c + i.val)
  omega

/-- Extending from the smaller physical interval agrees with padding in the
larger interval's increasing coordinates. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem placeAlong_nestedInterval_inclusion {T q c a b d : ℕ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T)
    (M : Matrix (Fin (b - a) → Fin q) (Fin (b - a) → Fin q) ℂ) :
    let eK := intervalShiftOrderIso hab (hbd.trans hd)
    let eE := intervalShiftOrderIso (show c ≤ d by omega) hd
    let inc : ↥(interval T a b) ↪ ↥(interval T c d) :=
      ⟨fun x ↦ (⟨x.val, mem_interval.mpr (by
        have hx := mem_interval.mp x.property
        constructor <;> omega)⟩ : ↥(interval T c d)),
        fun x y hxy ↦ Subtype.ext (by have h := congrArg Subtype.val hxy; exact h)⟩
    ManyBody.placeAlong (X := fun _ ↦ Fin q) inc
        (ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding M) =
      ManyBody.placeAlong (X := fun _ ↦ Fin q) eE.toEquiv.toEmbedding
        (ManyBody.placeAlong (X := fun _ ↦ Fin q)
          (ManyBody.chainWindow (a - c) (show a - c + (b - a) ≤ d - c by omega)) M) := by
  intro eK eE inc
  rw [ManyBody.placeAlong_placeAlong, ManyBody.placeAlong_placeAlong]
  exact congrArg
    (fun w : Fin (b - a) ↪ ↥(interval T c d) ↦ ManyBody.placeAlong (X := fun _ ↦ Fin q) w M)
    (nestedInterval_inclusion_trans_shift hca hab hbd hd)

end TNLean.MPS.AreaLaw

namespace MPOTensor

/-- The actual operator on a nested physical interval is represented by the
literal identity padding of the supplied ordered core tensors. Both physical
placements use increasing coordinates, and the closing matrix and virtual
space are unchanged. This is the placement step for ALVV,
arXiv:1602.08828v2, eq:H-mid-cut and Proposition 5.7, lines 1332–1333. -/
private theorem trace_identityExtendInterval_nested_inclusion
    {T q B c a b d : ℕ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T)
    (A : Fin (b - a) → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ) :
    let eK := intervalShiftOrderIso hab (hbd.trans hd)
    let eE := intervalShiftOrderIso (show c ≤ d by omega) hd
    let inc : ↥(interval T a b) ↪ ↥(interval T c d) :=
      ⟨fun x ↦ (⟨x.val, mem_interval.mpr (by
        have hx := mem_interval.mp x.property
        constructor <;> omega)⟩ : ↥(interval T c d)),
        fun x y hxy ↦ Subtype.ext (by have h := congrArg Subtype.val hxy; exact h)⟩
    ManyBody.placeAlong (X := fun _ ↦ Fin q) inc
        (ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding
          (Matrix.of fun σ τ : Fin (b - a) → Fin q ↦
            Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v, τ v))).prod))) =
      ManyBody.placeAlong (X := fun _ ↦ Fin q) eE.toEquiv.toEmbedding
        (Matrix.of fun σ τ : Fin (d - c) → Fin q ↦
          Matrix.trace (C * (List.ofFn (fun v ↦
            identityExtendInterval (T := d - c) A (a - c) (by omega)
              v (σ v, τ v))).prod)) := by
  intro eK eE inc
  have hpad := trace_identityExtendInterval_eq_placeAlong (T := d - c)
    A C (a - c) (by omega)
  calc
    _ = ManyBody.placeAlong (X := fun _ ↦ Fin q) eE.toEquiv.toEmbedding
        (ManyBody.placeAlong (X := fun _ ↦ Fin q)
          (ManyBody.chainWindow (a - c) (show a - c + (b - a) ≤ d - c by omega))
          (Matrix.of fun σ τ : Fin (b - a) → Fin q ↦
            Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v, τ v))).prod))) :=
      placeAlong_nestedInterval_inclusion hca hab hbd hd _
    _ = _ := congrArg
      (fun K : Matrix (Fin (d - c) → Fin q) (Fin (d - c) → Fin q) ℂ ↦
        ManyBody.placeAlong (X := fun _ ↦ Fin q) eE.toEquiv.toEmbedding K) hpad.symm

end MPOTensor

namespace TNLean.MPS.AreaLaw

/-- A possibly empty subinterval has the expected natural coordinates inside
an increasing interval. Reversed endpoints give an empty subinterval on both
sides. Supporting the strict core in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem intervalShiftOrderIso_mem_subinterval {T c d u v : ℕ}
    (hcd : c ≤ d) (hd : d ≤ T) (hcu : c ≤ u)
    (i : Fin (d - c)) :
    (intervalShiftOrderIso hcd hd i).val ∈ interval T u v ↔
      u - c ≤ i.val ∧ i.val < (u - c) + (v - u) := by
  rw [mem_interval]
  change u ≤ c + i.val ∧ c + i.val < v ↔ _
  omega

/-- The natural subinterval lies in the enclosing natural chain, including
an empty subinterval. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem intervalShift_subinterval_length_le {c d u v : ℕ}
    (hcu : c ≤ u) (hud : u ≤ d) (hvd : v ≤ d) :
    (u - c) + (v - u) ≤ d - c := by
  omega

/-- Increasing interval coordinates identify the single physical collar with
its natural complement. Overlapping collars are not counted twice.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. -/
def intervalComplementEquiv {T c d u v : ℕ}
    (hcd : c ≤ d) (hd : d ≤ T) (hcu : c ≤ u) :
    {i : Fin (d - c) // ¬(u - c ≤ i.val ∧ i.val < (u - c) + (v - u))} ≃
      ↥(Finset.univ.filter (fun x : ↥(interval T c d) ↦
        x.val ∉ interval T u v)) :=
  (intervalShiftOrderIso hcd hd).toEquiv.subtypeEquiv (fun i ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (not_congr (intervalShiftOrderIso_mem_subinterval hcd hd hcu i)).symm)

/-- The local lift from the single natural collar is its retained/interior
tensor product in increasing interval coordinates. This includes empty
intervals and zero local dimensions. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem localLift_retainedInterval {T L q : ℕ}
    (a : ℕ) (ha : a + L ≤ T) :
    let C := Finset.univ.filter
      (fun v : Fin T ↦ ¬(a ≤ v.val ∧ v.val < a + L))
    let f := fun (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q)
      (v : C) ↦ η ⟨v.val, by simpa only
        [C, Finset.mem_filter, Finset.mem_univ, true_and] using v.property⟩
    ∀ K : Matrix (ManyBody.RegionConfig (fun _ ↦ Fin q) C)
      (ManyBody.RegionConfig (fun _ ↦ Fin q) C) ℂ,
      ManyBody.place C K =
        ((K.submatrix f f) ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).submatrix
          (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm := by
  classical
  intro C f K
  ext σ τ
  rw [ManyBody.place_apply]
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  have hiff : (∀ v ∉ C, σ v = τ v) ↔
      (fun r : Fin L ↦ σ ⟨a + r.val, by omega⟩) =
        (fun r : Fin L ↦ τ ⟨a + r.val, by omega⟩) := by
    constructor
    · intro h
      funext r
      apply h
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      omega
    · intro h v hv
      have hi : a ≤ v.val ∧ v.val < a + L := by
        simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
      have hr := congrFun h ⟨v.val - a, by omega⟩
      change σ ⟨a + (v.val - a), by omega⟩ = τ ⟨a + (v.val - a), by omega⟩ at hr
      have he : (⟨a + (v.val - a), by omega⟩ : Fin T) = v := by
        apply Fin.ext
        dsimp
        omega
      exact (congrArg σ he).symm.trans (hr.trans (congrArg τ he))
  by_cases h : ((retainedIntervalEquiv a ha).symm σ).2 =
      ((retainedIntervalEquiv a ha).symm τ).2
  · have hp : ∀ v ∉ C, σ v = τ v := hiff.mpr h
    simp only [ite_eq_left hp, ite_eq_left h, mul_one]
    rfl
  · have hp : ¬(∀ v ∉ C, σ v = τ v) := fun ht ↦ h (hiff.mp ht)
    simp only [ite_eq_right hp, ite_eq_right h, mul_zero]

/-- Placing an operator along a bijection and reading it in the corresponding
coordinates recovers that operator, including empty configuration spaces.
Supporting natural interval coordinates in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem submatrix_placeAlong_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {q : ℕ} (e : ι ≃ κ) (X : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    (ManyBody.placeAlong (X := fun _ ↦ Fin q) e.toEmbedding X).submatrix
      (fun σ : ι → Fin q ↦ σ ∘ e.symm) (fun σ : ι → Fin q ↦ σ ∘ e.symm) = X := by
  classical
  ext σ τ
  rw [Matrix.submatrix_apply, ManyBody.placeAlong_apply]
  have h : ∀ v, (∀ u, e.toEmbedding u ≠ v) → (σ ∘ e.symm) v = (τ ∘ e.symm) v :=
    fun v hv ↦ False.elim (hv (e.symm v) (e.apply_symm_apply v))
  rw [ite_eq_left h]
  congr 1 <;> funext i <;>
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, e.symm_apply_apply]

/-- The supplied physical local lift in natural chain coordinates is the
natural collar lift with the same regional matrix transported to those
coordinates. This specializes `Entropy.localLift_relabel` and supports the
collar comparison in ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333, without a bond or approximation assertion. -/
private theorem localLift_physical_submatrix_eq_natural
    {Vphys : Type*} [Fintype Vphys] [DecidableEq Vphys] {T L q : ℕ}
    (e : Fin T ≃ Vphys) (a : ℕ) (Cphys : Finset Vphys)
    (hC : ∀ r : Fin T,
      r ∈ Finset.univ.filter (fun v : Fin T ↦ ¬(a ≤ v.val ∧ v.val < a + L)) ↔
        e r ∈ Cphys)
    (Kphys : Matrix (ManyBody.RegionConfig (fun _ ↦ Fin q) Cphys)
      (ManyBody.RegionConfig (fun _ ↦ Fin q) Cphys) ℂ) :
    let Cnat := Finset.univ.filter (fun v : Fin T ↦ ¬(a ≤ v.val ∧ v.val < a + L))
    let hDphys : ∀ v : Vphys, v ∈ Cphys ↔ e.symm v ∈ Cnat := fun v ↦ by
      simpa only [Equiv.apply_symm_apply] using (hC (e.symm v)).symm
    let r := ManyBody.regionConfigurationEquiv
      (X := fun _ : Vphys ↦ Fin q) (X' := fun _ : Fin T ↦ Fin q)
      Cphys Cnat e.symm hDphys (fun _ ↦ Equiv.refl (Fin q))
    (ManyBody.place Cphys Kphys).submatrix
        (fun σ : Fin T → Fin q ↦ σ ∘ e.symm)
        (fun σ : Fin T → Fin q ↦ σ ∘ e.symm) =
      ManyBody.place Cnat (Matrix.reindex r r Kphys) := by
  intro Cnat hDphys r
  have h := Entropy.localLift_relabel
    (n := fun _ : Vphys ↦ q) (n' := fun _ : Fin T ↦ q)
    Cphys Cnat e.symm hDphys (fun _ ↦ Equiv.refl (Fin q)) Kphys
  simpa only [Matrix.reindex_apply, ManyBody.siteConfigurationEquiv,
    Equiv.coe_piCongr_symm, Equiv.refl_symm, Equiv.refl_apply, r, Function.comp_def] using h

/-- A physical collar operator becomes a retained matrix tensored with the
interior identity in natural interval coordinates. The retained matrix is
chosen from the supplied operator and coordinate map alone. This composes
existing local-lift covariance with the retained/interior decomposition used
in ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem exists_retainedMatrix_of_physical_localLift
    {Vphys : Type*} [Fintype Vphys] [DecidableEq Vphys] {T L q : ℕ}
    (e : Fin T ≃ Vphys) (a : ℕ) (ha : a + L ≤ T) (Cphys : Finset Vphys)
    (hC : ∀ r : Fin T,
      r ∈ Finset.univ.filter (fun v : Fin T ↦ ¬(a ≤ v.val ∧ v.val < a + L)) ↔
        e r ∈ Cphys)
    (Kphys : Matrix (ManyBody.RegionConfig (fun _ ↦ Fin q) Cphys)
      (ManyBody.RegionConfig (fun _ ↦ Fin q) Cphys) ℂ) :
    ∃ Kret : Matrix ({v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q)
      ({v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q) ℂ,
      (ManyBody.place Cphys Kphys).submatrix
          (fun σ : Fin T → Fin q ↦ σ ∘ e.symm)
          (fun σ : Fin T → Fin q ↦ σ ∘ e.symm) =
        (Kret ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).submatrix
          (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm := by
  classical
  let Cnat := Finset.univ.filter (fun v : Fin T ↦ ¬(a ≤ v.val ∧ v.val < a + L))
  let hDphys : ∀ v : Vphys, v ∈ Cphys ↔ e.symm v ∈ Cnat := fun v ↦ by
    simpa only [Equiv.apply_symm_apply] using (hC (e.symm v)).symm
  let r := ManyBody.regionConfigurationEquiv
    (X := fun _ : Vphys ↦ Fin q) (X' := fun _ : Fin T ↦ Fin q)
    Cphys Cnat e.symm hDphys (fun _ ↦ Equiv.refl (Fin q))
  let Knat := Matrix.reindex r r Kphys
  let f := fun (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q)
      (v : Cnat) ↦ η ⟨v.val, by simpa only
        [Cnat, Finset.mem_filter, Finset.mem_univ, true_and] using v.property⟩
  refine ⟨Knat.submatrix f f, ?_⟩
  have hcov := localLift_physical_submatrix_eq_natural e a Cphys hC Kphys
  exact hcov.trans (localLift_retainedInterval a ha Knat)

end TNLean.MPS.AreaLaw

namespace MPOTensor

/-- Reading the actual nested physical middle operator in increasing
coordinates gives the trace of the literal identity-padded supplied tensors.
The same closing matrix and virtual dimension are retained. Supporting ALVV,
arXiv:1602.08828v2, eq:H-mid-cut and Proposition 5.7, lines 1332–1333. -/
theorem trace_identityExtendInterval_nested_natural
    {T q B c a b d : ℕ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T)
    (A : Fin (b - a) → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ) :
    let eK := intervalShiftOrderIso hab (hbd.trans hd)
    let eE := intervalShiftOrderIso (show c ≤ d by omega) hd
    let inc : ↥(interval T a b) ↪ ↥(interval T c d) :=
      ⟨fun x ↦ (⟨x.val, mem_interval.mpr (by
        have hx := mem_interval.mp x.property
        constructor <;> omega)⟩ : ↥(interval T c d)),
        fun x y hxy ↦ Subtype.ext (by have h := congrArg Subtype.val hxy; exact h)⟩
    (ManyBody.placeAlong (X := fun _ ↦ Fin q) inc
      (ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding
        (Matrix.of fun σ τ : Fin (b - a) → Fin q ↦
          Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v, τ v))).prod)))).submatrix
        (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm)
        (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm) =
      (Matrix.of fun σ τ : Fin (d - c) → Fin q ↦ Matrix.trace (C *
        (List.ofFn (fun v ↦ identityExtendInterval (T := d - c) A (a - c)
          (by omega) v (σ v, τ v))).prod)) := by
  intro eK eE inc
  have hME := trace_identityExtendInterval_nested_inclusion hca hab hbd hd A C
  have hread := congrArg
    (fun K : Matrix (↥(interval T c d) → Fin q) (↥(interval T c d) → Fin q) ℂ ↦
      K.submatrix (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm)
        (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm)) hME
  exact hread.trans (submatrix_placeAlong_equiv eE.toEquiv _)

end MPOTensor

end

section

open Matrix
open scoped BigOperators Kronecker

namespace TNLean.MPS.AreaLaw

/-- An actual operator supported on a chain interval has the exact nested
embedding of a finite site-dependent trace core used by the physical viable
family. Empty intervals and zero local dimensions are permitted. Elementary
support and coordinate algebra supporting ALVV, arXiv:1602.08828v2,
Theorem `t:ais`, lines 1010–1024; no efficient bond or running time is asserted. -/
theorem exists_traceChainOperator_of_supported_interval
    {L q c d : ℕ} (hcd : c ≤ d) (hd : d ≤ L)
    (A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hA : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) A (interval L c d)) :
    ∃ (B : ℕ) (Acore : Fin (d - c) → MPOTensor q B)
      (C0 : Matrix (Fin B) (Fin B) ℂ),
      A = ManyBody.place (X := fun _ ↦ Fin q) (interval L c d)
        (ManyBody.placeAlong (X := fun _ ↦ Fin q)
          (intervalShiftOrderIso hcd hd).toEquiv.toEmbedding
          (MPOTensor.traceChainOperator Acore C0)) := by
  let eI := intervalShiftOrderIso hcd hd
  let w : Fin (d - c) ↪ Fin L := eI.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  have hrange : Finset.univ.map w = interval L c d := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩
      exact (eI u).property
    · intro hi
      refine ⟨eI.symm ⟨i, hi⟩, ?_⟩
      exact congrArg Subtype.val (eI.apply_symm_apply ⟨i, hi⟩)
  have hs : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Finset.univ.map w) := by
    rw [hrange]
    exact hA
  obtain ⟨M, hM⟩ := ManyBody.exists_eq_placeAlong_of_mem_supportedOperators w hs
  obtain ⟨B, Acore, C0, hcore⟩ := MPOTensor.exists_traceChainOperator_of_finite_matrix M
  refine ⟨B, Acore, C0, ?_⟩
  rw [hM, hcore, ← ManyBody.placeAlong_subtype]
  exact (ManyBody.placeAlong_placeAlong _ _ _).symm

end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

/-- An interval longer than `4 * ell` has inward endpoints with the margins
required by the two-window bond geometry. Each endpoint moves by at most
`ell`, and the removed collars contain at most `2 * ell` sites.
This is an auxiliary interval reduction for ALVV, arXiv:1602.08828v2,
local `local_alg_arxiv_v2.tex` line 1000 and Proposition 5.7, lines 1311–1333.
It asserts no operator decomposition or area-law conclusion. -/
theorem inward_effective_cuts (L ell p q : ℕ)
    (hell : 1 ≤ ell) (hpq : p ≤ q) (hqL : q ≤ L) (hlong : 4 * ell < q - p) :
    let p' := max p ell
    let q' := min q (L - ell)
    let a := p' - ell
    let b := q' - ell - 1
    a + ell = p' ∧ b + ell + 1 = q' ∧
      a + 2 * ell ≤ b ∧ b + 2 * ell ≤ L - 1 ∧
      p ≤ p' ∧ p' ≤ q' ∧ q' ≤ q ∧ 2 * ell + 1 ≤ q' - p' ∧
      p' - p ≤ ell ∧ q - q' ≤ ell ∧ (p' - p) + (q - q') ≤ 2 * ell ∧
      interval L (a + ell) (b + ell + 1) ⊆ interval L p q ∧
      (interval L p q \ interval L (a + ell) (b + ell + 1)).card ≤ 2 * ell := by
  intro p' q' a b
  have hpp : p ≤ p' := Nat.le_max_left p ell
  have help : ell ≤ p' := Nat.le_max_right p ell
  have hqq : q' ≤ q := Nat.min_le_left q (L - ell)
  have hqLell : q' ≤ L - ell := Nat.min_le_right q (L - ell)
  have hpUpper : p' ≤ p + ell := by
    change max p ell ≤ p + ell
    omega
  have hqLower : q - ell ≤ q' := by
    change q - ell ≤ min q (L - ell)
    omega
  have hspan : p' + 2 * ell + 1 ≤ q' := by omega
  have hmidOrder : p' ≤ q' := by omega
  have hgap : 2 * ell + 1 ≤ q' - p' := by omega
  have hleft : p' - p ≤ ell := by omega
  have hright : q - q' ≤ ell := by omega
  have htotal : (p' - p) + (q - q') ≤ 2 * ell := by omega
  have haEnd : a + ell = p' := by
    change p' - ell + ell = p'
    omega
  have hbEnd : b + ell + 1 = q' := by
    change q' - ell - 1 + ell + 1 = q'
    omega
  have hleftAPI : a + 2 * ell ≤ b := by
    change p' - ell + 2 * ell ≤ q' - ell - 1
    omega
  have hrightAPI : b + 2 * ell ≤ L - 1 := by
    change q' - ell - 1 + 2 * ell ≤ L - 1
    omega
  have hsub : interval L p' q' ⊆ interval L p q :=
    interval_mono hpp hqq
  have hdiff : interval L p q \ interval L p' q' =
      interval L p p' ∪ interval L q' q := by
    ext i
    simp only [Finset.mem_sdiff, mem_interval, Finset.mem_union]
    omega
  have hcard : (interval L p q \ interval L p' q').card ≤ 2 * ell := by
    rw [hdiff]
    calc
      (interval L p p' ∪ interval L q' q).card ≤
          (interval L p p').card + (interval L q' q).card :=
        Finset.card_union_le _ _
      _ ≤ (p' - p) + (q - q') :=
        Nat.add_le_add (card_interval_le (L := L) p p')
          (card_interval_le (L := L) q' q)
      _ ≤ 2 * ell := htotal
  refine ⟨haEnd, hbEnd, hleftAPI, hrightAPI, hpp, hmidOrder, hqq, hgap,
    hleft, hright, htotal, ?_, ?_⟩
  · simpa only [haEnd, hbEnd] using hsub
  · simpa only [haEnd, hbEnd] using hcard

end TNLean.MPS.AreaLaw

end

end

section

open ManyBody (interval mem_interval)

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Restricting an actual Hermitian operator chain to a supported interval
preserves its approximation error after native placement. The same actual
site tensors and closing matrix are retained. Supporting ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_native_interval_slice_of_mpo_approximation {N q l r D : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ N + 1)
    (P : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hPs : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      P (interval (N + 1) l r))
    (Aglobal : Fin (N + 1) → MPOTensor q D)
    (hA : (MPOTensor.traceChainOperator Aglobal 1).IsHermitian)
    (xi : ℝ) (herr : ‖P - MPOTensor.traceChainOperator Aglobal 1‖ ≤ xi) :
    let sigma0 : Fin (N + 1) → Fin q := fun _ ↦ ⟨0, hq⟩
    let insert := insertInterval (L := r - l) l sigma0
    let eJ := intervalShiftOrderIso hlr hrL
    let e : Fin (r - l) ↪ Fin (N + 1) :=
      eJ.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
    ∃ (Acore : Fin (r - l) → MPOTensor q D)
      (C0 : Matrix (Fin D) (Fin D) ℂ),
      let Z := MPOTensor.traceChainOperator Acore C0
      let Zphys := ManyBody.placeAlong (X := fun _ ↦ Fin q) e Z
      Z.IsHermitian ∧ Zphys.IsHermitian ∧
        P = ManyBody.placeAlong (X := fun _ ↦ Fin q) e (P.submatrix insert insert) ∧
        ‖P.submatrix insert insert - Z‖ ≤ xi ∧ ‖P - Zphys‖ ≤ xi := by
  classical
  intro sigma0 insert eJ e
  have hmap : Finset.univ.map e = interval (N + 1) l r := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩
      exact (eJ u).property
    · intro hi
      exact ⟨eJ.symm ⟨i, hi⟩, congrArg Subtype.val (eJ.apply_symm_apply ⟨i, hi⟩)⟩
  have hs : P ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Finset.univ.map e) := by
    rw [hmap]
    exact hPs
  obtain ⟨M, hM⟩ := ManyBody.exists_eq_placeAlong_of_mem_supportedOperators e hs
  have hread (sigma : Fin (r - l) → Fin q) : insert sigma ∘ e = sigma := by
    funext u
    change insert sigma (eJ u).val = sigma u
    simp [insert, insertInterval, eJ, intervalShiftOrderIso, u.isLt]
  have hgoff (sigma tau : Fin (r - l) → Fin q) :
      ∀ v, (∀ u, e u ≠ v) → insert sigma v = insert tau v := by
    intro v hv
    have hout : ¬(l ≤ v.val ∧ v.val < l + (r - l)) := by
      intro hvin
      have hvJ : v ∈ interval (N + 1) l r := mem_interval.mpr (by omega)
      rw [← hmap] at hvJ
      obtain ⟨u, -, hu⟩ := Finset.mem_map.mp hvJ
      exact hv u hu
    simp only [insert, insertInterval, dite_eq_right hout]
  have hsliceP : P.submatrix insert insert = M := by
    ext sigma tau
    rw [Matrix.submatrix_apply, hM, ManyBody.placeAlong_apply,
      ite_eq_left (hgoff sigma tau)]
    exact congrArg₂ M (hread sigma) (hread tau)
  have hbound : l + (r - l) ≤ N + 1 := by omega
  let C0 := MPOTensor.actualRetainedIntervalClosing (L := r - l)
    Aglobal 1 l hbound (fun v ↦ sigma0 v.val) (fun v ↦ sigma0 v.val)
  let Acore : Fin (r - l) → MPOTensor q D := fun u ↦ Aglobal ⟨l + u.val, by omega⟩
  have hcore : (MPOTensor.traceChainOperator Aglobal 1).submatrix insert insert =
      MPOTensor.traceChainOperator Acore C0 := by
    ext sigma tau
    exact MPOTensor.trace_actual_retainedInterval_eq Aglobal 1 l hbound
      (fun v ↦ sigma0 v.val) (fun v ↦ sigma0 v.val) sigma tau
  have hNativeError :
      ‖P.submatrix insert insert - MPOTensor.traceChainOperator Acore C0‖ ≤ xi := by
    have hinj : Function.Injective insert :=
      (show Function.LeftInverse (fun x : Fin (N + 1) → Fin q ↦ x ∘ e) insert
        from hread).injective
    rw [← hcore]
    change ‖(P - MPOTensor.traceChainOperator Aglobal 1).submatrix insert insert‖ ≤ xi
    exact (Matrix.l2_opNorm_principal_submatrix_le _ _ hinj).trans herr
  exact
    let Z := MPOTensor.traceChainOperator Acore C0
    let hZ : Z.IsHermitian :=
      (congrArg Matrix.IsHermitian hcore).mp (hA.submatrix insert)
    let hMError : ‖M - Z‖ ≤ xi :=
      (congrArg (fun X : Matrix (Fin (r - l) → Fin q) (Fin (r - l) → Fin q) ℂ ↦
        ‖X - Z‖ ≤ xi) hsliceP).mp hNativeError
    let hDifference : P - ManyBody.placeAlong (X := fun _ ↦ Fin q) e Z =
        ManyBody.placeAlong (X := fun _ ↦ Fin q) e (M - Z) :=
      (congrArg (fun K ↦ K - ManyBody.placeAlong (X := fun _ ↦ Fin q) e Z) hM).trans
        (ManyBody.placeAlong_sub (X := fun _ ↦ Fin q) e M Z).symm
    ⟨Acore, C0, hZ,
      ManyBody.isHermitian_placeAlong (X := fun _ ↦ Fin q) e hZ,
      hM.trans (congrArg (ManyBody.placeAlong (X := fun _ ↦ Fin q) e) hsliceP.symm),
      hNativeError,
      (congrArg norm hDifference).le.trans
        ((ManyBody.norm_placeAlong_le (X := fun _ ↦ Fin q) e _).trans hMError)⟩

end TNLean.MPS.AreaLaw

end
