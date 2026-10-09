/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.ReplicaTransport.SymmetricMetric

/-!
# Commutation of nested physical band metrics

The scanner partitions in Section 9 satisfy `P ∪ Y ⊆ P'` across ordered bands.
The complement identity of Lemma 6.2 holds only on the symmetric replica
subspace. We retain its projection throughout the substitution of the far
metric by the metric of `P ∪ Y`; the resulting nested/disjoint factors commute.
This proves the cross-band hypothesis of Proposition 7.4 from physical regions.
-/

open scoped Matrix
open Matrix PermutationRepresentation

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

private theorem product_mul_projection_congr {ι : Type*} [Fintype ι]
    {A A' B B' E : Matrix ι ι ℂ} (hA : A * E = A' * E)
    (hB : B * E = B' * E) (hB' : Commute E B') :
    (A * B) * E = (A' * B') * E := by
  calc
    (A * B) * E = A * (B * E) := mul_assoc _ _ _
    _ = A * (B' * E) := by rw [hB]
    _ = (A * E) * B' := by rw [← hB'.eq, mul_assoc]
    _ = (A' * E) * B' := by rw [hA]
    _ = (A' * B') * E := by rw [mul_assoc, hB'.eq, mul_assoc]

private theorem labelObservable_mul_symProj_compl (k : ℕ) (Q : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f *
        symProj (copyPerm (Entropy.SiteConfig n) k) =
      labelObservable (subsystemPerm k (fun v => Fin (n v)) Qᶜ) f *
        symProj (copyPerm (Entropy.SiteConfig n) k) := by
  simp only [labelObservable, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_assoc, smul_mul_assoc, labelProj_mul_symProj_compl]

private theorem commute_labelObservable_of_subset (k : ℕ) {Q Q' : Finset V}
    (h : Q ⊆ Q') (f f' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f)
      (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q') f') := by
  rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
  exact commute_groupAlgebraRep_subsystemPerm_of_subset _ k h
    (sum_smul_centralIdem_mem_center _) _

private theorem commute_symProj_labelObservable (k : ℕ) (Q : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (symProj (copyPerm (Entropy.SiteConfig n) k))
      (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f) :=
  commute_symProj_of_forall_commute_permOp fun s =>
    commute_copyPerm_labelObservable k Q f s

variable [∀ v, NeZero (n v)] {t : ℝ}

private theorem commute_labelObservable_bandMetric (ht : 0 ≤ t) (k : ℕ)
    {π : PYF V} (hπ : π.IsPartition) {Q : Finset V} (hQ : Q ⊆ π.P)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f)
      (bandMetric n t k π) := by
  have hP := commute_labelObservable_of_subset (n := n) k hQ f
    (fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹)
  have hF := commute_replicaMetric_of_disjoint' (n := n) k
    (hπ.2.1.mono_left hQ) f
    (fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹)
  have hY := commute_replicaMetric_of_disjoint' (n := n) k
    (hπ.1.mono_left hQ) f (replicaLabelWeight (fun v => Fin (n v)) t)
  unfold bandMetric leafMetric leafRoot
  rw [replicaMetric_inv_eq ht, replicaMetric_inv_eq ht]
  exact ((hP.mul_right hF).mul_right hY).pow_right 2

/-- Physical ordered partitions have commuting band metrics on the symmetric
replica subspace. The complement substitution is made only after multiplication
by the symmetric projection, never as a global matrix identity. -/
theorem bandMetric_commute_on_symmetric_of_nested (ht : 0 ≤ t) (k : ℕ)
    {π π' : PYF V} (hπ : π.IsPartition) (hπ' : π'.IsPartition)
    (h : π.P ∪ π.Y ⊆ π'.P) :
    ∀ w ∈ symmetricSubspace k (fun v => Fin (n v)),
      bandMetric n t k π *ᵥ (bandMetric n t k π' *ᵥ w) =
        bandMetric n t k π' *ᵥ (bandMetric n t k π *ᵥ w) := by
  let πm : PYF V := ⟨π.P, π.Y, π.Fᶜ⟩
  have hFc : π.Fᶜ = π.P ∪ π.Y := by
    apply Finset.ext
    intro v
    have hc := Finset.ext_iff.mp hπ.2.2.2 v
    have hd := Finset.disjoint_left.mp (hπ.2.1.sup_left hπ.2.2.1)
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_univ, iff_true] at hc ⊢
    constructor
    · intro hn
      rcases hc with h | h
      · exact h
      · exact (hn h).elim
    · intro hp hf
      exact hd (Finset.mem_union.mpr hp) hf
  have hcomm : Commute (bandMetric n t k πm) (bandMetric n t k π') := by
    have hP := commute_labelObservable_bandMetric (n := n) ht k hπ' (Q := π.P)
      (Finset.subset_union_left.trans h)
      (fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹)
    have hF := commute_labelObservable_bandMetric (n := n) ht k hπ' (Q := π.Fᶜ)
      (by simpa only [hFc] using h)
      (fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹)
    have hY := commute_labelObservable_bandMetric (n := n) ht k hπ' (Q := π.Y)
      (Finset.subset_union_right.trans h) (replicaLabelWeight (fun v => Fin (n v)) t)
    change Commute (leafRoot n t k π.P π.Y π.Fᶜ ^ 2) (bandMetric n t k π')
    unfold leafRoot
    rw [replicaMetric_inv_eq ht, replicaMetric_inv_eq ht]
    exact ((hP.mul_left hF).mul_left hY).pow_left 2
  have heq : bandMetric n t k π * symProj (copyPerm (Entropy.SiteConfig n) k) =
      bandMetric n t k πm * symProj (copyPerm (Entropy.SiteConfig n) k) := by
    have hi := labelObservable_mul_symProj_compl (n := n) k π.F
      (fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹)
    have hroot : leafRoot n t k π.P π.Y π.F * symProj (copyPerm (Entropy.SiteConfig n) k) =
        leafRoot n t k π.P π.Y π.Fᶜ * symProj (copyPerm (Entropy.SiteConfig n) k) := by
      simp only [leafRoot, replicaMetric_inv_eq ht, replicaMetric]
      exact product_mul_projection_congr
        (product_mul_projection_congr rfl hi (commute_symProj_labelObservable k _ _))
        rfl (commute_symProj_labelObservable k _ _)
    have hc : Commute (symProj (copyPerm (Entropy.SiteConfig n) k))
        (leafRoot n t k π.P π.Y π.Fᶜ) := by
      simp only [leafRoot, replicaMetric_inv_eq ht, replicaMetric]
      exact ((commute_symProj_labelObservable k _ _).mul_right
        (commute_symProj_labelObservable k _ _)).mul_right
        (commute_symProj_labelObservable k _ _)
    simpa only [bandMetric, leafMetric, πm, pow_two] using
      product_mul_projection_congr hroot hroot hc
  intro w hw
  have hwE := symProj_mulVec_of_mem (copyPerm (Entropy.SiteConfig n) k) hw
  have hc := commute_symProj_bandMetric (n := n) t k π'
  have hright : (bandMetric n t k π * bandMetric n t k π') *
      symProj (copyPerm (Entropy.SiteConfig n) k) =
      (bandMetric n t k π' * bandMetric n t k π) *
        symProj (copyPerm (Entropy.SiteConfig n) k) := by
    calc
      _ = (bandMetric n t k πm * bandMetric n t k π') *
          symProj (copyPerm (Entropy.SiteConfig n) k) :=
        product_mul_projection_congr heq rfl hc
      _ = (bandMetric n t k π' * bandMetric n t k πm) *
          symProj (copyPerm (Entropy.SiteConfig n) k) := by rw [hcomm.eq]
      _ = _ := by rw [mul_assoc, ← heq, mul_assoc]
  have hv := congrArg (fun M => M *ᵥ w) hright
  simpa only [← Matrix.mulVec_mulVec, hwE] using hv

/-- The identity-complement extensions of ordered physical band metrics commute. -/
theorem commute_symBandMetric_of_nested (ht : 0 ≤ t) (k : ℕ)
    {π π' : PYF V} (hπ : π.IsPartition) (hπ' : π'.IsPartition)
    (h : π.P ∪ π.Y ⊆ π'.P) :
    Commute (symBandMetric n t k π) (symBandMetric n t k π') :=
  (commute_symBandMetric_iff t k π π').mpr
    (bandMetric_commute_on_symmetric_of_nested ht k hπ hπ' h)

end TensorPower.ReplicaTransport
