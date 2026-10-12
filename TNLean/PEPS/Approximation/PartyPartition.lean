/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordPermutation

/-!
# Partitioning registers by their owners

The memory of a layout is canonically the tensor product of the registers whose owners
satisfy a predicate and the remaining registers. Within each part, the original order is
preserved. This is the tensor-factor identification used to collect local maps by party in
the Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 233–251.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open ContinuousLinearMap

namespace Layout

variable {P : Type}

/-- The registers whose owners satisfy the given Boolean predicate, in their original order.
Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 233–251. -/
def restrict (f : P → Bool) (ℓ : Layout P) : Layout P :=
  ℓ.filter (fun r ↦ f r.owner)

@[simp] theorem restrict_nil (f : P → Bool) : restrict f [] = [] := rfl

@[simp] theorem restrict_cons (f : P → Bool) (r : Reg P) (ℓ : Layout P) :
    restrict f (r :: ℓ) = if f r.owner then r :: restrict f ℓ else restrict f ℓ :=
  List.filter_cons

@[simp] theorem restrict_append (f : P → Bool) (a b : Layout P) :
    restrict f (a ++ b) = restrict f a ++ restrict f b :=
  List.filter_append a b

/-- Retaining a party retains every register of a layout owned by that party. -/
theorem restrict_eq_self_of_owner (f : P → Bool) {p : P} {ℓ : Layout P}
    (h : ∀ r ∈ ℓ, r.owner = p) (hp : f p = true) : restrict f ℓ = ℓ := by
  exact List.filter_eq_self.mpr (fun r hr ↦ by simpa [h r hr] using hp)

/-- Excluding a party removes every register of a layout owned by that party. -/
theorem restrict_eq_nil_of_owner (f : P → Bool) {p : P} {ℓ : Layout P}
    (h : ∀ r ∈ ℓ, r.owner = p) (hp : f p = false) : restrict f ℓ = [] := by
  exact List.filter_eq_nil_iff.mpr (fun r hr ↦ by simp [h r hr, hp])

/-- The canonical identification of memories belonging to equal layouts. -/
def memCongr {a b : Layout P} (h : a = b) : Mem a ≃ₗᵢ[ℂ] Mem b :=
  h ▸ LinearIsometryEquiv.refl ℂ (Mem a)

@[simp] theorem memCongr_rfl (a : Layout P) :
    memCongr (rfl : a = a) = LinearIsometryEquiv.refl ℂ (Mem a) := rfl

/-- Reversing a layout equality gives the inverse memory identification.
Source: polynomial-PEPS, `04-compression.tex`, lines 246–267. -/
theorem memCongr_symm {a b : Layout P} (h : a = b) :
    memCongr h.symm = (memCongr h).symm := by
  cases h
  rfl

/-- Appending a head register commutes with the equality identification of the tail.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267. -/
theorem memCongr_cons_tmul (r : Reg P) {a b : Layout P} (h : a = b)
    (x : r.space) (y : Mem a) :
    memCongr (congrArg (r :: ·) h) (x ⊗ₜ y) = x ⊗ₜ memCongr h y := by
  cases h
  rfl

/-- The canonical partition of a layout memory into the selected registers and their
complement. The empty memory is identified with `ℂ ⊗ ℂ` by the left unit isometry.
Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 233–251. -/
def partitionIso (f : P → Bool) : (ℓ : Layout P) →
    Mem ℓ ≃ₗᵢ[ℂ] Mem (restrict f ℓ) ⊗[ℂ] Mem (restrict (fun p ↦ !f p) ℓ)
  | [] => (TensorProduct.lidIsometry ℂ ℂ).symm
  | r :: ℓ => if h : f r.owner = true then by
      rw [restrict_cons, restrict_cons, h]
      exact ((partitionIso f ℓ).lTensor r.space).trans
        (TensorProduct.assocIsometry ℂ r.space (Mem (restrict f ℓ))
          (Mem (restrict (fun p ↦ !f p) ℓ))).symm
    else by
      have h' : f r.owner = false := Bool.eq_false_iff.mpr h
      rw [restrict_cons, restrict_cons, h']
      exact ((partitionIso f ℓ).lTensor r.space).trans
        (leftCommIso r.space (Mem (restrict f ℓ))
          (Mem (restrict (fun p ↦ !f p) ℓ)))

/-- Constructor recurrence when the first register belongs to the selected part. -/
theorem partitionIso_cons_true (f : P → Bool) (r : Reg P) (ℓ : Layout P)
    (h : f r.owner = true) :
    HEq (partitionIso f (r :: ℓ))
      (((partitionIso f ℓ).lTensor r.space).trans
        (TensorProduct.assocIsometry ℂ r.space (Mem (restrict f ℓ))
          (Mem (restrict (fun p ↦ !f p) ℓ))).symm) := by
  simp only [partitionIso, dite_eq_left h, Eq.mpr, eqRec_heq_iff]
  rfl

/-- Constructor recurrence when the first register belongs to the complementary part. -/
theorem partitionIso_cons_false (f : P → Bool) (r : Reg P) (ℓ : Layout P)
    (h : f r.owner = false) :
    HEq (partitionIso f (r :: ℓ))
      (((partitionIso f ℓ).lTensor r.space).trans
        (leftCommIso r.space (Mem (restrict f ℓ))
          (Mem (restrict (fun p ↦ !f p) ℓ)))) := by
  have hn : ¬f r.owner = true := by simp [h]
  simp only [partitionIso, dite_eq_right hn, Eq.mpr, eqRec_heq_iff]
  rfl

private theorem iso_apply_heq {A B C : HSpace} (h : B = C)
    (e : A ≃ₗᵢ[ℂ] B) (e' : A ≃ₗᵢ[ℂ] C) (he : HEq e e') (x : A) :
    HEq (e x) (e' x) := by
  subst h
  cases he
  rfl

/-- The selected-head recurrence evaluated on an elementary tensor. -/
theorem partitionIso_cons_true_tmul (f : P → Bool) (r : Reg P) (ℓ : Layout P)
    (h : f r.owner = true) (x : r.space) (y : Mem ℓ) :
    HEq (partitionIso f (r :: ℓ) (x ⊗ₜ[ℂ] y))
      ((TensorProduct.assocIsometry ℂ r.space (Mem (restrict f ℓ))
        (Mem (restrict (fun p ↦ !f p) ℓ))).symm (x ⊗ₜ[ℂ] partitionIso f ℓ y)) := by
  apply (iso_apply_heq (A := Mem (r :: ℓ))
    (B := HSpace.of (Mem (restrict f (r :: ℓ)) ⊗[ℂ]
      Mem (restrict (fun p ↦ !f p) (r :: ℓ))))
    (C := HSpace.of ((r.space ⊗[ℂ] Mem (restrict f ℓ)) ⊗[ℂ]
      Mem (restrict (fun p ↦ !f p) ℓ)))
    (by rw [restrict_cons, restrict_cons, h]; rfl) _ _
    (partitionIso_cons_true f r ℓ h) (x ⊗ₜ[ℂ] y)).trans
  simp

/-- The complementary-head recurrence evaluated on an elementary tensor. -/
theorem partitionIso_cons_false_tmul (f : P → Bool) (r : Reg P) (ℓ : Layout P)
    (h : f r.owner = false) (x : r.space) (y : Mem ℓ) :
    HEq (partitionIso f (r :: ℓ) (x ⊗ₜ[ℂ] y))
      (leftCommIso r.space (Mem (restrict f ℓ))
        (Mem (restrict (fun p ↦ !f p) ℓ)) (x ⊗ₜ[ℂ] partitionIso f ℓ y)) := by
  apply (iso_apply_heq (A := Mem (r :: ℓ))
    (B := HSpace.of (Mem (restrict f (r :: ℓ)) ⊗[ℂ]
      Mem (restrict (fun p ↦ !f p) (r :: ℓ))))
    (C := HSpace.of (Mem (restrict f ℓ) ⊗[ℂ]
      (r.space ⊗[ℂ] Mem (restrict (fun p ↦ !f p) ℓ))))
    (by rw [restrict_cons, restrict_cons, h]; rfl) _ _
    (partitionIso_cons_false f r ℓ h) (x ⊗ₜ[ℂ] y)).trans
  simp

/-- Equal selected and complementary register lists preserve the selected-head
associativity identification. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 233–251 and 409–450. -/
theorem selectedHead_heq (r : Reg P) {a b a' b' : Layout P}
    (ha : a = a') (hb : b = b') (x : r.space)
    {y : Mem a ⊗[ℂ] Mem b} {z : Mem a' ⊗[ℂ] Mem b'} (h : HEq y z) :
    HEq ((TensorProduct.assocIsometry ℂ r.space (Mem a) (Mem b)).symm (x ⊗ₜ[ℂ] y))
      ((TensorProduct.assocIsometry ℂ r.space (Mem a') (Mem b')).symm (x ⊗ₜ[ℂ] z)) := by
  subst ha
  subst hb
  cases h
  rfl

/-- Equal selected and complementary register lists preserve the complementary-head
exchange identification. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 233–251 and 409–450. -/
theorem complementaryHead_heq (r : Reg P) {a b a' b' : Layout P}
    (ha : a = a') (hb : b = b') (x : r.space)
    {y : Mem a ⊗[ℂ] Mem b} {z : Mem a' ⊗[ℂ] Mem b'} (h : HEq y z) :
    HEq (leftCommIso r.space (Mem a) (Mem b) (x ⊗ₜ[ℂ] y))
      (leftCommIso r.space (Mem a') (Mem b') (x ⊗ₜ[ℂ] z)) := by
  subst ha
  subst hb
  cases h
  rfl

/-- Addition respects identification of equal memory spaces and their vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–450. -/
theorem add_heq {A B : HSpace} (h : A = B) {x y : A} {x' y' : B}
    (hx : HEq x x') (hy : HEq y y') : HEq (x + y) (x' + y') := by
  subst h
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq hx) (eq_of_heq hy))

/-- A prefix owned by a selected party joins the selected tensor factor. -/
theorem partitionIso_append_true_tmul (f : P → Bool) {p : P} (a ℓ : Layout P)
    (ha : ∀ r ∈ a, r.owner = p) (hp : f p = true)
    (s : Mem a) (x : Mem (restrict f ℓ)) (y : Mem (restrict (fun p ↦ !f p) ℓ)) :
    HEq (partitionIso f (a ++ ℓ)
      ((appendIso a ℓ).symm (s ⊗ₜ[ℂ] (partitionIso f ℓ).symm (x ⊗ₜ[ℂ] y))))
      ((appendIso a (restrict f ℓ)).symm (s ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y) := by
  induction a with
  | nil => simp [appendIso, TensorProduct.smul_tmul]
  | cons r a ih =>
      induction s using TensorProduct.inductionOn with
      | add u v hu hv =>
          simp only [TensorProduct.add_tmul, map_add]
          exact add_heq
            (A := HSpace.of (Mem (restrict f ((r :: a) ++ ℓ)) ⊗[ℂ]
              Mem (restrict (fun p ↦ !f p) ((r :: a) ++ ℓ))))
            (B := HSpace.of (Mem ((r :: a) ++ restrict f ℓ) ⊗[ℂ]
              Mem (restrict (fun p ↦ !f p) ℓ)))
            (by rw [restrict_append, restrict_eq_self_of_owner f ha hp,
              restrict_append, restrict_eq_nil_of_owner (fun p ↦ !f p) ha
                (by simp [hp]), List.nil_append]) hu hv
      | tmul u v =>
          rw [appendIso_symm_cons_tmul]
          apply (partitionIso_cons_true_tmul f r (a ++ ℓ)
            (by simpa [ha r (by simp)] using hp) u _).trans
          have ha' : ∀ t ∈ a, t.owner = p := fun t ht ↦ ha t (List.mem_cons_of_mem r ht)
          apply (selectedHead_heq r
            (by rw [restrict_append, restrict_eq_self_of_owner f ha' hp])
            (by rw [restrict_append, restrict_eq_nil_of_owner (fun p ↦ !f p) ha'
                (by simp [hp]), List.nil_append]) u (ih ha' v)).trans
          rfl

/-- A prefix owned by an excluded party joins the complementary tensor factor. -/
theorem partitionIso_append_false_tmul (f : P → Bool) {p : P} (a ℓ : Layout P)
    (ha : ∀ r ∈ a, r.owner = p) (hp : f p = false)
    (s : Mem a) (x : Mem (restrict f ℓ)) (y : Mem (restrict (fun p ↦ !f p) ℓ)) :
    HEq (partitionIso f (a ++ ℓ)
      ((appendIso a ℓ).symm (s ⊗ₜ[ℂ] (partitionIso f ℓ).symm (x ⊗ₜ[ℂ] y))))
      (x ⊗ₜ[ℂ] (appendIso a (restrict (fun p ↦ !f p) ℓ)).symm (s ⊗ₜ[ℂ] y)) := by
  induction a with
  | nil => simp [appendIso, TensorProduct.tmul_smul]
  | cons r a ih =>
      induction s using TensorProduct.inductionOn with
      | add u v hu hv =>
          simp only [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add]
          exact add_heq
            (A := HSpace.of (Mem (restrict f ((r :: a) ++ ℓ)) ⊗[ℂ]
              Mem (restrict (fun p ↦ !f p) ((r :: a) ++ ℓ))))
            (B := HSpace.of (Mem (restrict f ℓ) ⊗[ℂ]
              Mem ((r :: a) ++ restrict (fun p ↦ !f p) ℓ)))
            (by rw [restrict_append, restrict_eq_nil_of_owner f ha hp, List.nil_append,
              restrict_append, restrict_eq_self_of_owner (fun p ↦ !f p) ha
                (by simp [hp])]) hu hv
      | tmul u v =>
          rw [appendIso_symm_cons_tmul]
          apply (partitionIso_cons_false_tmul f r (a ++ ℓ)
            (by simpa [ha r (by simp)] using hp) u _).trans
          have ha' : ∀ t ∈ a, t.owner = p := fun t ht ↦ ha t (List.mem_cons_of_mem r ht)
          apply (complementaryHead_heq r
            (by rw [restrict_append, restrict_eq_nil_of_owner f ha' hp, List.nil_append])
            (by rw [restrict_append, restrict_eq_self_of_owner (fun p ↦ !f p) ha'
                (by simp [hp])]) u (ih ha' v)).trans
          rfl

/-- Two selected registers remain together in their original order. -/
theorem partitionIso_cons_cons_true_true_tmul (f : P → Bool) (r t : Reg P)
    (ℓ : Layout P) (hr : f r.owner = true) (ht : f t.owner = true)
    (x : r.space) (y : t.space) (a : Mem (restrict f ℓ))
    (b : Mem (restrict (fun p ↦ !f p) ℓ)) :
    HEq (partitionIso f (r :: t :: ℓ)
      (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (partitionIso f ℓ).symm (a ⊗ₜ[ℂ] b))))
      ((x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] a)) ⊗ₜ[ℂ] b) := by
  apply (partitionIso_cons_true_tmul f r (t :: ℓ) hr x _).trans
  apply (selectedHead_heq r (a' := t :: restrict f ℓ)
    (b' := restrict (fun p ↦ !f p) ℓ)
    (by simp only [restrict_cons, ht, ↓reduceIte])
    (by simp only [restrict_cons, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]) x
    (partitionIso_cons_true_tmul f t ℓ ht y _)).trans
  simp

/-- Registers in opposite parts enter their respective factors. -/
theorem partitionIso_cons_cons_true_false_tmul (f : P → Bool) (r t : Reg P)
    (ℓ : Layout P) (hr : f r.owner = true) (ht : f t.owner = false)
    (x : r.space) (y : t.space) (a : Mem (restrict f ℓ))
    (b : Mem (restrict (fun p ↦ !f p) ℓ)) :
    HEq (partitionIso f (r :: t :: ℓ)
      (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (partitionIso f ℓ).symm (a ⊗ₜ[ℂ] b))))
      ((x ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] b)) := by
  apply (partitionIso_cons_true_tmul f r (t :: ℓ) hr x _).trans
  apply (selectedHead_heq r (a' := restrict f ℓ)
    (b' := t :: restrict (fun p ↦ !f p) ℓ)
    (by simp only [restrict_cons, ht, Bool.false_eq_true, ↓reduceIte])
    (by simp only [restrict_cons, ht, Bool.not_false, ↓reduceIte]) x
    (partitionIso_cons_false_tmul f t ℓ ht y _)).trans
  simp

/-- An excluded register followed by a selected register enters the two parts in order. -/
theorem partitionIso_cons_cons_false_true_tmul (f : P → Bool) (r t : Reg P)
    (ℓ : Layout P) (hr : f r.owner = false) (ht : f t.owner = true)
    (x : r.space) (y : t.space) (a : Mem (restrict f ℓ))
    (b : Mem (restrict (fun p ↦ !f p) ℓ)) :
    HEq (partitionIso f (r :: t :: ℓ)
      (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (partitionIso f ℓ).symm (a ⊗ₜ[ℂ] b))))
      ((y ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] b)) := by
  apply (partitionIso_cons_false_tmul f r (t :: ℓ) hr x _).trans
  apply (complementaryHead_heq r (a' := t :: restrict f ℓ)
    (b' := restrict (fun p ↦ !f p) ℓ)
    (by simp only [restrict_cons, ht, ↓reduceIte])
    (by simp only [restrict_cons, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]) x
    (partitionIso_cons_true_tmul f t ℓ ht y _)).trans
  simp

/-- Two excluded registers remain together in their original order. -/
theorem partitionIso_cons_cons_false_false_tmul (f : P → Bool) (r t : Reg P)
    (ℓ : Layout P) (hr : f r.owner = false) (ht : f t.owner = false)
    (x : r.space) (y : t.space) (a : Mem (restrict f ℓ))
    (b : Mem (restrict (fun p ↦ !f p) ℓ)) :
    HEq (partitionIso f (r :: t :: ℓ)
      (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (partitionIso f ℓ).symm (a ⊗ₜ[ℂ] b))))
      (a ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] b))) := by
  apply (partitionIso_cons_false_tmul f r (t :: ℓ) hr x _).trans
  apply (complementaryHead_heq r (a' := restrict f ℓ)
    (b' := t :: restrict (fun p ↦ !f p) ℓ)
    (by simp only [restrict_cons, ht, Bool.false_eq_true, ↓reduceIte])
    (by simp only [restrict_cons, ht, Bool.not_false, ↓reduceIte]) x
    (partitionIso_cons_false_tmul f t ℓ ht y _)).trans
  simp

end Layout

end TNLean.PEPS.PairEffect
