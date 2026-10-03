/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic
import TNLean.Circuit.EmbeddedProduct
import TNLean.Circuit.CleanUnitaryImplementation
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fintype

/-!
# Columns of two disjoint interval implementations

Two operators placed on disjoint registers act independently, and leave every
remaining register unchanged. The exact matrix formula below retains arbitrary
spectator inputs. It derives the joint initialized-column identity from the two
individual identities, without assuming the joint identity.

The register decomposition is defined using the ranges of the two placements.
The initialized basis embeddings use this same decomposition, so their matrix
products reduce to Kronecker products.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor QuantumCircuit
open scoped Kronecker

namespace MPUCircuit

/-- Two configurations agree outside both placed registers.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def AgreeOffPair {d a b n : ℕ} (e : Fin a → Fin n) (f : Fin b → Fin n)
    (x y : Cfg d n) : Prop := ∀ s, (∀ i, e i ≠ s) → (∀ j, f j ≠ s) → x s = y s

open scoped Classical in
/-- The product of two disjoint placed operators has the product of their matrix entries, with a
delta condition on all remaining sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mul_embedOp_disjoint_apply {d a b n : ℕ}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (hdisj : Disjoint (Set.range e) (Set.range f))
    (X : Matrix (Cfg d a) (Cfg d a) ℂ) (Y : Matrix (Cfg d b) (Cfg d b) ℂ)
    (x y : Cfg d n) :
    (embedOp e X * embedOp f Y) x y =
      if AgreeOffPair e f x y then X (x ∘ e) (y ∘ e) * Y (x ∘ f) (y ∘ f) else 0 := by
  classical
  let m : Bool → ℕ := fun z ↦ if z then a else b
  let E : ∀ z, Fin (m z) ↪ Fin n
    | true => e
    | false => f
  let M : ∀ z, Matrix (Cfg d (m z)) (Cfg d (m z)) ℂ
    | true => X
    | false => Y
  have hD : ((Finset.univ : Finset Bool) : Set Bool).PairwiseDisjoint
      (fun z ↦ Set.range (E z)) := by
    intro z _ w _ hzw
    cases z <;> cases w
    · exact (hzw rfl).elim
    · exact hdisj.symm
    · exact hdisj
    · exact (hzw rfl).elim
  have hC : ((Finset.univ : Finset Bool) : Set Bool).Pairwise
      (Function.onFun Commute fun z ↦ embedOp (E z) (M z)) := by
    intro z hz w hw hzw
    exact commute_embedOp_of_disjoint (E z).injective (E w).injective
      (hD hz hw hzw) (M z) (M w)
  have h := noncommProd_embedOp_apply (fun z ↦ (E z : Fin (m z) → Fin n))
    (fun z ↦ (E z).injective) M Finset.univ hD hC x y
  have hc : (∀ i, (∀ z ∈ (Finset.univ : Finset Bool), ∀ j, E z j ≠ i) → x i = y i) ↔
      AgreeOffPair e f x y := by
    constructor
    · intro h i hi hj
      apply h i
      intro z _
      cases z
      · exact hj
      · exact hi
    · intro h i hi
      exact h i (hi true (Finset.mem_univ _)) (hi false (Finset.mem_univ _))
  have hp : (Finset.univ : Finset Bool).noncommProd
      (fun z ↦ embedOp (E z) (M z)) hC = embedOp e X * embedOp f Y := by
    simp [Fintype.univ_bool, E, M]
  rw [hp] at h
  simp only [hc] at h
  simpa [E, M] using h


/-- Configurations on the sites outside a placement.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
abbrev OutsidePlacedConfig (d : ℕ) {m n : ℕ} (e : Fin m ↪ Fin n) :=
  {s : Fin n // s ∉ Set.range e} → Fin d

/-- A configuration decomposes into its placed and remaining registers.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def placedConfigEquiv (d : ℕ) {m n : ℕ} (e : Fin m ↪ Fin n) :
    Cfg d n ≃ Cfg d m × OutsidePlacedConfig d e := by
  classical
  exact (Equiv.arrowCongr
    ((Equiv.sumCongr e.toEquivRange (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e))).symm
    (Equiv.refl (Fin d))).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The placed component is restriction along the placement.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem placedConfigEquiv_fst (d : ℕ) {m n : ℕ} (e : Fin m ↪ Fin n) (x : Cfg d n) :
    (placedConfigEquiv d e x).1 = x ∘ e := rfl

/-- The remaining component is restriction to the complement of the placement.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem placedConfigEquiv_snd (d : ℕ) {m n : ℕ} (e : Fin m ↪ Fin n) (x : Cfg d n) :
    (placedConfigEquiv d e x).2 = fun s ↦ x s.val := rfl

/-- Two disjoint placed registers and their complement give a decomposition of the full
configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def jointPlacedConfigEquiv (d : ℕ) {a b n : ℕ}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f)) :
    Cfg d n ≃ (Cfg d a × Cfg d b) × OutsidePlacedConfig d (Fin.Embedding.append h) :=
  (placedConfigEquiv d (Fin.Embedding.append h)).trans
    (Equiv.prodCongr (Fin.appendEquiv a b).symm (Equiv.refl _))

/-- The first component is restriction to the first register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedConfigEquiv_left (d : ℕ) {a b n : ℕ}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f)) (x : Cfg d n) :
    (jointPlacedConfigEquiv d e f h x).1.1 = x ∘ e := by
  funext i
  change x (Fin.append e f (Fin.castAdd b i)) = x (e i)
  rw [Fin.append_left]

/-- The second component is restriction to the second register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedConfigEquiv_right (d : ℕ) {a b n : ℕ}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f)) (x : Cfg d n) :
    (jointPlacedConfigEquiv d e f h x).1.2 = x ∘ f := by
  funext i
  change x (Fin.append e f (Fin.natAdd a i)) = x (f i)
  rw [Fin.append_right]

/-- The last component retains all remaining sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedConfigEquiv_snd (d : ℕ) {a b n : ℕ}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f)) (x : Cfg d n) :
    (jointPlacedConfigEquiv d e f h x).2 = fun s ↦ x s.val := rfl

/-- Agreement outside both placements is equality of the remaining configurations.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem agreeOffPair_iff_outside_eq {d a b n : ℕ}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f)) (x y : Cfg d n) :
    AgreeOffPair e f x y ↔
      (jointPlacedConfigEquiv d e f h x).2 = (jointPlacedConfigEquiv d e f h y).2 := by
  constructor
  · intro hxy
    funext s
    apply hxy s.val
    · intro i hi
      apply s.2
      exact ⟨Fin.castAdd b i, by simpa only [Fin.Embedding.coe_append, Fin.append_left] using hi⟩
    · intro i hi
      apply s.2
      exact ⟨Fin.natAdd a i, by simpa only [Fin.Embedding.coe_append, Fin.append_right] using hi⟩
  · intro hxy s he hf
    have hs : s ∉ Set.range (Fin.Embedding.append h) := by
      rintro ⟨i, hi⟩
      refine Fin.addCases (fun j hj ↦ he j ?_) (fun j hj ↦ hf j ?_) i hi
      · simpa only [Fin.Embedding.coe_append, Fin.append_left] using hj
      · simpa only [Fin.Embedding.coe_append, Fin.append_right] using hj
    exact congrFun hxy ⟨s, hs⟩

open scoped Classical in
/-- In the disjoint-register coordinates, the product is the two child operators tensored with the
identity on all remaining sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem reindex_mul_embedOp_of_disjoint {d a b n : ℕ}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (X : Matrix (Cfg d a) (Cfg d a) ℂ) (Y : Matrix (Cfg d b) (Cfg d b) ℂ) :
    Matrix.reindex (jointPlacedConfigEquiv d e f h) (jointPlacedConfigEquiv d e f h)
      (embedOp e X * embedOp f Y) =
      (X ⊗ₖ Y) ⊗ₖ (1 : Matrix (OutsidePlacedConfig d (Fin.Embedding.append h))
        (OutsidePlacedConfig d (Fin.Embedding.append h)) ℂ) := by
  classical
  ext p q
  obtain ⟨x, rfl⟩ := (jointPlacedConfigEquiv d e f h).surjective p
  obtain ⟨y, rfl⟩ := (jointPlacedConfigEquiv d e f h).surjective q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply,
    jointPlacedConfigEquiv_left, jointPlacedConfigEquiv_right]
  rw [mul_embedOp_disjoint_apply e f h X Y x y, agreeOffPair_iff_outside_eq e f h]
  split_ifs <;> simp only [mul_one, mul_zero]


/-- The product of two basis encodings and an encoding of the remaining registers.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def jointPlacedBasisEmbedding {d a b n : ℕ} {α β τ : Type*}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (g : α ↪ Cfg d a) (k : β ↪ Cfg d b)
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append h)) :
    ((α × β) × τ) ↪ Cfg d n :=
  ((g.prodMap k).prodMap t).trans (jointPlacedConfigEquiv d e f h).symm.toEmbedding

open scoped Classical in
/-- The initialized inclusion for the joint encoding is the Kronecker product of the three
initialized inclusions.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem initializedBasisMatrix_jointPlacedBasisEmbedding {d a b n : ℕ} {α β τ : Type*}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (g : α ↪ Cfg d a) (k : β ↪ Cfg d b)
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append h)) :
    (initializedBasisMatrix (jointPlacedBasisEmbedding e f h g k t)).submatrix
      (jointPlacedConfigEquiv d e f h).symm id =
      (initializedBasisMatrix g ⊗ₖ initializedBasisMatrix k) ⊗ₖ initializedBasisMatrix t := by
  classical
  ext p q
  change (if (jointPlacedConfigEquiv d e f h).symm p =
      (jointPlacedConfigEquiv d e f h).symm ((g q.1.1, k q.1.2), t q.2)
    then (1 : ℂ) else 0) =
      ((if p.1.1 = g q.1.1 then 1 else 0) * (if p.1.2 = k q.1.2 then 1 else 0)) *
        (if p.2 = t q.2 then 1 else 0)
  simp only [(jointPlacedConfigEquiv d e f h).symm.injective.eq_iff,
    Prod.ext_iff]
  split_ifs <;> simp_all

open scoped Classical in
/-- The two individual initialized-column identities imply the joint product identity, including
arbitrary encoded spectator states.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedColumns_of_individual {d a b n : ℕ} {α β γ δ τ : Type*}
    [Fintype γ] [Fintype δ] [Fintype τ]
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (g : α ↪ Cfg d a) (k : β ↪ Cfg d b)
    (g' : γ ↪ Cfg d a) (k' : δ ↪ Cfg d b)
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append h))
    (X : Matrix (Cfg d a) (Cfg d a) ℂ) (Y : Matrix (Cfg d b) (Cfg d b) ℂ)
    (V : Matrix γ α ℂ) (W : Matrix δ β ℂ)
    (hX : X * initializedBasisMatrix g = initializedBasisMatrix g' * V)
    (hY : Y * initializedBasisMatrix k = initializedBasisMatrix k' * W) :
    (embedOp e X * embedOp f Y) *
      initializedBasisMatrix (jointPlacedBasisEmbedding e f h g k t) =
      initializedBasisMatrix (jointPlacedBasisEmbedding e f h g' k' t) *
        ((V ⊗ₖ W) ⊗ₖ (1 : Matrix τ τ ℂ)) := by
  classical
  apply (Matrix.reindex (jointPlacedConfigEquiv d e f h) (Equiv.refl _)).injective
  change ((embedOp e X * embedOp f Y) *
      initializedBasisMatrix (jointPlacedBasisEmbedding e f h g k t)).submatrix
        (jointPlacedConfigEquiv d e f h).symm id =
    (initializedBasisMatrix (jointPlacedBasisEmbedding e f h g' k' t) *
      ((V ⊗ₖ W) ⊗ₖ (1 : Matrix τ τ ℂ))).submatrix
        (jointPlacedConfigEquiv d e f h).symm id
  rw [← Matrix.submatrix_mul_equiv _ _ (jointPlacedConfigEquiv d e f h).symm
      (jointPlacedConfigEquiv d e f h).symm id,
    ← Matrix.submatrix_mul_equiv _ _ (jointPlacedConfigEquiv d e f h).symm (Equiv.refl _) id]
  change Matrix.reindex (jointPlacedConfigEquiv d e f h) (jointPlacedConfigEquiv d e f h)
      (embedOp e X * embedOp f Y) *
      (initializedBasisMatrix (jointPlacedBasisEmbedding e f h g k t)).submatrix
        (jointPlacedConfigEquiv d e f h).symm id =
    (initializedBasisMatrix (jointPlacedBasisEmbedding e f h g' k' t)).submatrix
      (jointPlacedConfigEquiv d e f h).symm id * ((V ⊗ₖ W) ⊗ₖ (1 : Matrix τ τ ℂ))
  rw [reindex_mul_embedOp_of_disjoint e f h,
    initializedBasisMatrix_jointPlacedBasisEmbedding e f h g k t,
    initializedBasisMatrix_jointPlacedBasisEmbedding e f h g' k' t]
  simp only [← Matrix.mul_kronecker_mul, hX, hY, Matrix.one_mul, Matrix.mul_one]

end MPUCircuit
