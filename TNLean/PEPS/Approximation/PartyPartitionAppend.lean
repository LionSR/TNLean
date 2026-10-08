/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyPartition
import TNLean.PEPS.Approximation.PartyLayout

/-!
# Compatibility of register partitions with concatenation

Partitioning each of two register lists and then gathering the two selected
parts gives the same tensor identification as partitioning their concatenation.
This identifies the partition by parties with the independent separation of
physical and discarded registers.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–450.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-partypartitionappend-01
Downstream declaration:
TNLean.PEPS.PairEffect.Layout.appendPartitionIso

Provenance-ID: 8769-physical-partypartitionappend-02
Downstream declaration:
TNLean.PEPS.PairEffect.Layout.appendPartitionIso_tmul

Provenance-ID: 8769-physical-partypartitionappend-03
Downstream declaration:
TNLean.PEPS.PairEffect.Layout.partitionIso_append_tmul

-/


noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Layout
variable {P : Type}

/-- Regroup two partitioned register lists and concatenate each pair of parts. -/
def appendPartitionIso (a₁ a₂ b₁ b₂ : Layout P) :
    (Mem a₁ ⊗[ℂ] Mem a₂) ⊗[ℂ] (Mem b₁ ⊗[ℂ] Mem b₂) ≃ₗᵢ[ℂ]
      Mem (a₁ ++ b₁) ⊗[ℂ] Mem (a₂ ++ b₂) :=
  (pairRegroup (Mem a₁) (Mem a₂) (Mem b₁) (Mem b₂)).trans
    (TensorProduct.congrIsometry (appendIso a₁ b₁).symm (appendIso a₂ b₂).symm)

/-- Regrouping sends the four original factors to the corresponding two concatenations. -/
theorem appendPartitionIso_tmul (a₁ a₂ b₁ b₂ : Layout P)
    (x₁ : Mem a₁) (x₂ : Mem a₂) (y₁ : Mem b₁) (y₂ : Mem b₂) :
    appendPartitionIso a₁ a₂ b₁ b₂ ((x₁ ⊗ₜ[ℂ] x₂) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)) =
      (appendIso a₁ b₁).symm (x₁ ⊗ₜ[ℂ] y₁) ⊗ₜ[ℂ]
        (appendIso a₂ b₂).symm (x₂ ⊗ₜ[ℂ] y₂) := by
  simp [appendPartitionIso, pairRegroup_tmul]

private theorem appendPartitionIso_cons_left (r : Reg P) (a₁ a₂ b₁ b₂ : Layout P)
    (u : r.space) (x : Mem a₁ ⊗[ℂ] Mem a₂) (y : Mem b₁ ⊗[ℂ] Mem b₂) :
    appendPartitionIso (r :: a₁) a₂ b₁ b₂
      (((TensorProduct.assocIsometry ℂ r.space (Mem a₁) (Mem a₂)).symm
        (u ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ] y) =
      (TensorProduct.assocIsometry ℂ r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))).symm
        (u ⊗ₜ[ℂ] appendPartitionIso a₁ a₂ b₁ b₂ (x ⊗ₜ[ℂ] y)) := by
  let f := (isoL (appendPartitionIso (r :: a₁) a₂ b₁ b₂) ∘L
    (isoL (TensorProduct.assocIsometry ℂ r.space (Mem a₁) (Mem a₂)).symm ∘L
      appendLeft u).rTensor (Mem b₁ ⊗[ℂ] Mem b₂)).toLinearMap
  let g := (isoL
    (TensorProduct.assocIsometry ℂ r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))).symm ∘L
      appendLeft u ∘L isoL (appendPartitionIso a₁ a₂ b₁ b₂)).toLinearMap
  have h : f = g := TensorProduct.ext_fourfold' fun x₁ x₂ y₁ y₂ ↦ by
    change appendPartitionIso (r :: a₁) a₂ b₁ b₂
      (((TensorProduct.assocIsometry ℂ r.space (Mem a₁) (Mem a₂)).symm
        (u ⊗ₜ[ℂ] (x₁ ⊗ₜ[ℂ] x₂))) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)) = _
    simp only [TensorProduct.assocIsometry_symm_apply, TensorProduct.assoc_symm_tmul]
    rw [appendPartitionIso_tmul (r :: a₁) a₂ b₁ b₂ (u ⊗ₜ[ℂ] x₁) x₂ y₁ y₂]
    change _ = (TensorProduct.assocIsometry ℂ r.space
      (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))).symm
        (u ⊗ₜ[ℂ] appendPartitionIso a₁ a₂ b₁ b₂
          ((x₁ ⊗ₜ[ℂ] x₂) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)))
    rw [appendPartitionIso_tmul]
    rfl
  exact LinearMap.congr_fun h (x ⊗ₜ[ℂ] y)

private theorem appendPartitionIso_cons_right (r : Reg P) (a₁ a₂ b₁ b₂ : Layout P)
    (u : r.space) (x : Mem a₁ ⊗[ℂ] Mem a₂) (y : Mem b₁ ⊗[ℂ] Mem b₂) :
    appendPartitionIso a₁ (r :: a₂) b₁ b₂
      ((leftCommIso r.space (Mem a₁) (Mem a₂) (u ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ] y) =
      leftCommIso r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))
        (u ⊗ₜ[ℂ] appendPartitionIso a₁ a₂ b₁ b₂ (x ⊗ₜ[ℂ] y)) := by
  let f := (isoL (appendPartitionIso a₁ (r :: a₂) b₁ b₂) ∘L
    (isoL (leftCommIso r.space (Mem a₁) (Mem a₂)) ∘L
      appendLeft u).rTensor (Mem b₁ ⊗[ℂ] Mem b₂)).toLinearMap
  let g := (isoL (leftCommIso r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))) ∘L
    appendLeft u ∘L isoL (appendPartitionIso a₁ a₂ b₁ b₂)).toLinearMap
  have h : f = g := TensorProduct.ext_fourfold' fun x₁ x₂ y₁ y₂ ↦ by
    change appendPartitionIso a₁ (r :: a₂) b₁ b₂
      (leftCommIso r.space (Mem a₁) (Mem a₂)
        (u ⊗ₜ[ℂ] (x₁ ⊗ₜ[ℂ] x₂)) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)) = _
    simp only [leftCommIso_tmul]
    rw [appendPartitionIso_tmul a₁ (r :: a₂) b₁ b₂ x₁ (u ⊗ₜ[ℂ] x₂) y₁ y₂]
    change _ = leftCommIso r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))
      (u ⊗ₜ[ℂ] appendPartitionIso a₁ a₂ b₁ b₂
        ((x₁ ⊗ₜ[ℂ] x₂) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)))
    rw [appendPartitionIso_tmul]
    rfl
  exact LinearMap.congr_fun h (x ⊗ₜ[ℂ] y)

private theorem appendPartitionIso_heq {a₁ a₂ a₁' a₂' : Layout P}
    (ha : a₁ = a₁') (hb : a₂ = a₂') (b₁ b₂ : Layout P)
    {x : Mem a₁ ⊗[ℂ] Mem a₂} {x' : Mem a₁' ⊗[ℂ] Mem a₂'}
    (hx : HEq x x') (y : Mem b₁ ⊗[ℂ] Mem b₂) :
    HEq (appendPartitionIso a₁ a₂ b₁ b₂ (x ⊗ₜ[ℂ] y))
      (appendPartitionIso a₁' a₂' b₁ b₂ (x' ⊗ₜ[ℂ] y)) := by
  cases ha
  cases hb
  cases hx
  rfl

private theorem selectedHead_heq (r : Reg P) {a b a' b' : Layout P}
    (ha : a = a') (hb : b = b') (x : r.space)
    {y : Mem a ⊗[ℂ] Mem b} {z : Mem a' ⊗[ℂ] Mem b'} (h : HEq y z) :
    HEq ((TensorProduct.assocIsometry ℂ r.space (Mem a) (Mem b)).symm (x ⊗ₜ[ℂ] y))
      ((TensorProduct.assocIsometry ℂ r.space (Mem a') (Mem b')).symm (x ⊗ₜ[ℂ] z)) := by
  cases ha
  cases hb
  cases h
  rfl

private theorem complementaryHead_heq (r : Reg P) {a b a' b' : Layout P}
    (ha : a = a') (hb : b = b') (x : r.space)
    {y : Mem a ⊗[ℂ] Mem b} {z : Mem a' ⊗[ℂ] Mem b'} (h : HEq y z) :
    HEq (leftCommIso r.space (Mem a) (Mem b) (x ⊗ₜ[ℂ] y))
      (leftCommIso r.space (Mem a') (Mem b') (x ⊗ₜ[ℂ] z)) := by
  cases ha
  cases hb
  cases h
  rfl

private theorem add_heq {A B : HSpace} (h : A = B) {x y : A} {x' y' : B}
    (hx : HEq x x') (hy : HEq y y') : HEq (x + y) (x' + y') := by
  cases h
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq hx) (eq_of_heq hy))

/-- Partitioning a concatenation agrees with partitioning each list and then
joining its selected and complementary parts. The heterogeneous equality
records precisely the two list identities `restrict_append`. -/
theorem partitionIso_append_tmul (f : P → Bool) (a b : Layout P)
    (x : Mem a) (y : Mem b) :
    HEq (partitionIso f (a ++ b) ((appendIso a b).symm (x ⊗ₜ[ℂ] y)))
      (appendPartitionIso (restrict f a) (restrict (fun p ↦ !f p) a)
        (restrict f b) (restrict (fun p ↦ !f p) b)
        (partitionIso f a x ⊗ₜ[ℂ] partitionIso f b y)) := by
  induction a with
  | nil =>
      apply heq_of_eq
      obtain ⟨z, rfl⟩ := (partitionIso f b).symm.surjective y
      induction z using TensorProduct.inductionOn with
      | add z t hz ht =>
          simp only [map_add, TensorProduct.tmul_add, hz, ht]
          rfl
      | tmul u v =>
          simp only [List.nil_append, restrict_nil, LinearIsometryEquiv.apply_symm_apply]
          change partitionIso f b ((appendIso [] b).symm
            (x ⊗ₜ[ℂ] (partitionIso f b).symm (u ⊗ₜ[ℂ] v))) =
            appendPartitionIso [] [] (restrict f b) (restrict (fun p ↦ !f p) b)
              (((1 : ℂ) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v))
          rw [appendPartitionIso_tmul [] [] _ _ (1 : ℂ) x u v]
          simp [appendIso, TensorProduct.tmul_smul]
  | cons r a ih =>
      induction x using TensorProduct.inductionOn with
      | add x z hx hz =>
          simp only [TensorProduct.add_tmul, map_add]
          exact add_heq
            (A := HSpace.of (Mem (restrict f ((r :: a) ++ b)) ⊗[ℂ]
              Mem (restrict (fun p ↦ !f p) ((r :: a) ++ b))))
            (B := HSpace.of (Mem (restrict f (r :: a) ++ restrict f b) ⊗[ℂ]
              Mem (restrict (fun p ↦ !f p) (r :: a) ++ restrict (fun p ↦ !f p) b)))
            (by rw [restrict_append, restrict_append]) hx hz
      | tmul u v =>
          rw [appendIso_symm_cons_tmul]
          cases h : f r.owner with
          | true =>
              have hr := (appendPartitionIso_heq
                (by simp [h] : restrict f (r :: a) = r :: restrict f a)
                (by simp [h] : restrict (fun p ↦ !f p) (r :: a) = restrict (fun p ↦ !f p) a)
                (restrict f b) (restrict (fun p ↦ !f p) b)
                (partitionIso_cons_true_tmul f r a h u v) (partitionIso f b y)).trans
                  (heq_of_eq (appendPartitionIso_cons_left r _ _ _ _ u _ _))
              exact (partitionIso_cons_true_tmul f r (a ++ b) h u _).trans
                ((selectedHead_heq r (restrict_append f a b)
                  (restrict_append (fun p ↦ !f p) a b) u (ih v)).trans hr.symm)
          | false =>
              have hr := (appendPartitionIso_heq
                (by simp [h] : restrict f (r :: a) = restrict f a)
                (by simp [h] : restrict (fun p ↦ !f p) (r :: a) = r :: restrict (fun p ↦ !f p) a)
                (restrict f b) (restrict (fun p ↦ !f p) b)
                (partitionIso_cons_false_tmul f r a h u v) (partitionIso f b y)).trans
                  (heq_of_eq (appendPartitionIso_cons_right r _ _ _ _ u _ _))
              exact (partitionIso_cons_false_tmul f r (a ++ b) h u _).trans
                ((complementaryHead_heq r (restrict_append f a b)
                  (restrict_append (fun p ↦ !f p) a b) u (ih v)).trans hr.symm)

end TNLean.PEPS.PairEffect.Layout
