/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RetainedCoreFamilies
import TNLean.MPS.AreaLaw.TraceCoreSlices
import TNLean.MPS.AreaLaw.Basic
import TNLean.Circuit.SiteEmbedding
import QICLean.Entropy.LocalLift
import QICLean.Entropy.RegionUnion
import QICLean.Entropy.FilterOutputCovariance
import Mathlib.Data.List.OfFn

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
-/

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
    Fin T → MPOTensor q B := fun v i j ↦
  if h : a ≤ v.val ∧ v.val < a + L then
    A ⟨v.val - a, by omega⟩ i j
  else if i = j then 1 else 0

/-- When the two physical configurations agree off the interval, the exterior
identity letters leave precisely the supplied ordered interior product.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem prod_identityExtendInterval_of_agreeOff {T L q B : ℕ}
    (A : Fin L → MPOTensor q B) (a : ℕ) (ha : a + L ≤ T)
    (σ τ : Fin T → Fin q)
    (h : QuantumCircuit.AgreeOff (fun r : Fin L ↦ (⟨a + r.val, by omega⟩ : Fin T)) σ τ) :
    (List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v) (τ v))).prod =
      (List.ofFn (fun r : Fin L ↦
        A r (σ ⟨a + r.val, by omega⟩) (τ ⟨a + r.val, by omega⟩))).prod := by
  let f := List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v) (τ v))
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
      A r (σ ⟨a + r.val, by omega⟩) (τ ⟨a + r.val, by omega⟩)) := by
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
private theorem trace_identityExtendInterval_eq_embedOp {T L q B : ℕ}
    (A : Fin L → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T) :
    (Matrix.of fun σ τ : Fin T → Fin q ↦ Matrix.trace (C *
      (List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v) (τ v))).prod)) =
      QuantumCircuit.embedOp
        (fun r : Fin L ↦ (⟨a + r.val, by omega⟩ : Fin T))
        (Matrix.of fun σ τ : Fin L → Fin q ↦ Matrix.trace
          (C * (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod)) := by
  classical
  ext σ τ
  rw [QuantumCircuit.embedOp_apply]
  by_cases h : QuantumCircuit.AgreeOff
      (fun r : Fin L ↦ (⟨a + r.val, by omega⟩ : Fin T)) σ τ
  · rw [ite_eq_left h]
    simpa only [Matrix.of_apply, Function.comp_def] using
      congrArg (fun P : Matrix (Fin B) (Fin B) ℂ ↦ Matrix.trace (C * P))
        (prod_identityExtendInterval_of_agreeOff A a ha σ τ h)
  · rw [ite_eq_right h]
    obtain ⟨v, hv, hne⟩ : ∃ v : Fin T,
        (∀ r : Fin L, (⟨a + r.val, by omega⟩ : Fin T) ≠ v) ∧ σ v ≠ τ v := by
      simpa only [QuantumCircuit.AgreeOff, not_forall, not_imp, exists_prop] using h
    have hout : ¬(a ≤ v.val ∧ v.val < a + L) := by
      intro hi
      apply hv ⟨v.val - a, by omega⟩
      apply Fin.ext
      dsimp
      omega
    have hz : identityExtendInterval A a ha v (σ v) (τ v) = 0 := by
      simp [identityExtendInterval, hout, hne]
    have hmem : (0 : Matrix (Fin B) (Fin B) ℂ) ∈
        List.ofFn (fun v ↦ identityExtendInterval A a ha v (σ v) (τ v)) := by
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
private theorem nestedInterval_inclusion_comp_shift {T c a b d : ℕ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T) :
    (fun i : Fin (b - a) ↦
      (⟨(intervalShiftOrderIso hab (hbd.trans hd) i).val,
        mem_interval.mpr (by
          have hi := (intervalShiftOrderIso hab (hbd.trans hd) i).property
          rw [mem_interval] at hi
          constructor <;> omega)⟩ : ↥(interval T c d))) =
      fun i ↦ intervalShiftOrderIso (show c ≤ d by omega) hd
        ⟨a - c + i.val, by omega⟩ := by
  funext i
  apply Subtype.ext
  apply Fin.ext
  change a + i.val = c + (a - c + i.val)
  omega

/-- Extending from the smaller physical interval agrees with padding in the
larger interval's increasing coordinates. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem embedOp_nestedInterval_inclusion {T q c a b d : ℕ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T)
    (M : Matrix (Fin (b - a) → Fin q) (Fin (b - a) → Fin q) ℂ) :
    let eK := intervalShiftOrderIso hab (hbd.trans hd)
    let eE := intervalShiftOrderIso (show c ≤ d by omega) hd
    let inc := fun x : ↥(interval T a b) ↦
      (⟨x.val, mem_interval.mpr (by
        have hx := mem_interval.mp x.property
        constructor <;> omega)⟩ : ↥(interval T c d))
    QuantumCircuit.embedOp inc (QuantumCircuit.embedOp eK M) =
      QuantumCircuit.embedOp eE (QuantumCircuit.embedOp
        (fun i : Fin (b - a) ↦ (⟨a - c + i.val, by omega⟩ : Fin (d - c))) M) := by
  intro eK eE inc
  have hinc : Function.Injective inc := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : ↥(interval T c d) ↦ z.val) hxy)
  rw [QuantumCircuit.embedOp_embedOp hinc,
    QuantumCircuit.embedOp_embedOp eE.injective]
  exact congrArg (fun f : Fin (b - a) → ↥(interval T c d) ↦ QuantumCircuit.embedOp f M)
    (nestedInterval_inclusion_comp_shift hca hab hbd hd)

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
    let inc := fun x : ↥(interval T a b) ↦
      (⟨x.val, mem_interval.mpr (by
        have hx := mem_interval.mp x.property
        constructor <;> omega)⟩ : ↥(interval T c d))
    QuantumCircuit.embedOp inc
        (QuantumCircuit.embedOp eK (Matrix.of fun σ τ : Fin (b - a) → Fin q ↦
          Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod))) =
      QuantumCircuit.embedOp eE (Matrix.of fun σ τ : Fin (d - c) → Fin q ↦
        Matrix.trace (C * (List.ofFn (fun v ↦
          identityExtendInterval (T := d - c) A (a - c) (by omega)
            v (σ v) (τ v))).prod)) := by
  intro eK eE inc
  have hpad := trace_identityExtendInterval_eq_embedOp (T := d - c)
    A C (a - c) (by omega)
  calc
    _ = QuantumCircuit.embedOp eE
        (QuantumCircuit.embedOp
          (fun i : Fin (b - a) ↦ (⟨a - c + i.val, by omega⟩ : Fin (d - c)))
          (Matrix.of fun σ τ : Fin (b - a) → Fin q ↦
            Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod))) :=
      embedOp_nestedInterval_inclusion hca hab hbd hd _
    _ = _ := congrArg
      (fun X : Matrix (Fin (d - c) → Fin q) (Fin (d - c) → Fin q) ℂ ↦
        QuantumCircuit.embedOp eE X) hpad.symm

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
    ∀ K : Matrix (Entropy.RegionConfig (fun _ : Fin T ↦ q) C)
      (Entropy.RegionConfig (fun _ : Fin T ↦ q) C) ℂ,
      Entropy.localLift C K =
        ((K.submatrix f f) ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).submatrix
          (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm := by
  classical
  intro C f K
  ext σ τ
  rw [Entropy.localLift_apply]
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
private theorem embedOp_equiv_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {q : ℕ} (e : ι ≃ κ) (X : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    (QuantumCircuit.embedOp e X).submatrix
      (fun σ : ι → Fin q ↦ σ ∘ e.symm) (fun σ : ι → Fin q ↦ σ ∘ e.symm) = X := by
  classical
  ext σ τ
  rw [Matrix.submatrix_apply, QuantumCircuit.embedOp_apply]
  have h : QuantumCircuit.AgreeOff e (σ ∘ e.symm) (τ ∘ e.symm) := by
    intro v hv
    exact False.elim (hv (e.symm v) (e.apply_symm_apply v))
  rw [ite_eq_left h]
  congr 1 <;> funext i <;> simp only [Function.comp_apply, e.symm_apply_apply]

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
    (Kphys : Matrix (Entropy.RegionConfig (fun _ : Vphys ↦ q) Cphys)
      (Entropy.RegionConfig (fun _ : Vphys ↦ q) Cphys) ℂ) :
    let Cnat := Finset.univ.filter (fun v : Fin T ↦ ¬(a ≤ v.val ∧ v.val < a + L))
    let hDphys : ∀ v : Vphys, v ∈ Cphys ↔ e.symm v ∈ Cnat := fun v ↦ by
      simpa only [Equiv.apply_symm_apply] using (hC (e.symm v)).symm
    let r := Entropy.regionConfigurationEquiv
      (n := fun _ : Vphys ↦ q) (n' := fun _ : Fin T ↦ q)
      Cphys Cnat e.symm hDphys (fun _ ↦ Equiv.refl (Fin q))
    (Entropy.localLift Cphys Kphys).submatrix
        (fun σ : Fin T → Fin q ↦ σ ∘ e.symm)
        (fun σ : Fin T → Fin q ↦ σ ∘ e.symm) =
      Entropy.localLift Cnat (Matrix.reindex r r Kphys) := by
  intro Cnat hDphys r
  have h := Entropy.localLift_relabel
    (n := fun _ : Vphys ↦ q) (n' := fun _ : Fin T ↦ q)
    Cphys Cnat e.symm hDphys (fun _ ↦ Equiv.refl (Fin q)) Kphys
  simpa only [Matrix.reindex_apply, Entropy.siteConfigurationEquiv,
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
    (Kphys : Matrix (Entropy.RegionConfig (fun _ : Vphys ↦ q) Cphys)
      (Entropy.RegionConfig (fun _ : Vphys ↦ q) Cphys) ℂ) :
    ∃ Kret : Matrix ({v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q)
      ({v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q) ℂ,
      (Entropy.localLift Cphys Kphys).submatrix
          (fun σ : Fin T → Fin q ↦ σ ∘ e.symm)
          (fun σ : Fin T → Fin q ↦ σ ∘ e.symm) =
        (Kret ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).submatrix
          (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm := by
  classical
  let Cnat := Finset.univ.filter (fun v : Fin T ↦ ¬(a ≤ v.val ∧ v.val < a + L))
  let hDphys : ∀ v : Vphys, v ∈ Cphys ↔ e.symm v ∈ Cnat := fun v ↦ by
    simpa only [Equiv.apply_symm_apply] using (hC (e.symm v)).symm
  let r := Entropy.regionConfigurationEquiv
    (n := fun _ : Vphys ↦ q) (n' := fun _ : Fin T ↦ q)
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
    let inc := fun x : ↥(interval T a b) ↦
      (⟨x.val, mem_interval.mpr (by
        have hx := mem_interval.mp x.property
        constructor <;> omega)⟩ : ↥(interval T c d))
    (QuantumCircuit.embedOp inc
      (QuantumCircuit.embedOp eK (Matrix.of fun σ τ : Fin (b - a) → Fin q ↦
        Matrix.trace (C * (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod)))).submatrix
        (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm)
        (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm) =
      (Matrix.of fun σ τ : Fin (d - c) → Fin q ↦ Matrix.trace (C *
        (List.ofFn (fun v ↦ identityExtendInterval (T := d - c) A (a - c)
          (by omega) v (σ v) (τ v))).prod)) := by
  intro eK eE inc
  have hME := trace_identityExtendInterval_nested_inclusion hca hab hbd hd A C
  have hread := congrArg
    (fun X : Matrix (↥(interval T c d) → Fin q) (↥(interval T c d) → Fin q) ℂ ↦
      X.submatrix (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm)
        (fun σ : Fin (d - c) → Fin q ↦ σ ∘ eE.symm)) hME
  exact hread.trans (embedOp_equiv_submatrix eE.toEquiv _)

end MPOTensor

end
