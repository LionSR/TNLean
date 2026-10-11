/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.PartyPartition
import Mathlib.Data.List.NodupEquivFin

/-! Physical registers with their original party-dependent dimensions.
Source: polynomial-PEPS, `04-compression.tex:137–151`.
-/
noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap
variable {P : Type}

/-- Every physical register has its original party-dependent dimension.
Source: polynomial-PEPS, `04-compression.tex:137–151`. -/
def familyPhysicalLayout (d : P → ℕ) (ps : List P) : Layout P :=
  ps.map fun p ↦ ⟨p, euc (Fin (d p))⟩

/-- The tensor basis of the actual physical registers, before relabelling positions
by original parties. Source: polynomial-PEPS, `04-compression.tex:137–151`. -/
def familyPhysicalListBasis (d : P → ℕ) : (ps : List P) →
    OrthonormalBasis ((i : Fin ps.length) → Fin (d (ps.get i))) ℂ
      (Mem (familyPhysicalLayout d ps)).carrier
  | [] => by
      convert OrthonormalBasis.singleton ((i : Fin 0) → Fin (d (([] : List P).get i))) ℂ <;> rfl
  | p :: ps => ((EuclideanSpace.basisFun (Fin (d p)) ℂ).tensorProduct
      (familyPhysicalListBasis d ps)).reindex
        (Fin.consEquiv (fun i ↦ Fin (d ((p :: ps).get i))))

/-- The physical tensor basis is indexed by original party labels, with each
original local dimension preserved.
Source: polynomial-PEPS, `04-compression.tex:137–151`. -/
def familyLabelledPhysicalBasis [Fintype P] [DecidableEq P] (d : P → ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) :
    OrthonormalBasis ((p : P) → Fin (d p)) ℂ
      (Mem (familyPhysicalLayout d ps)).carrier :=
  (familyPhysicalListBasis d ps).reindex
    (Equiv.piCongrLeft (fun p : P ↦ Fin (d p))
      (List.Nodup.getEquivOfForallMemList ps hps hcover))

/-- Restriction preserves the original physical dimensions and party order.
Source: polynomial-PEPS, `04-compression.tex:137–151` and `233–251`. -/
theorem restrict_familyPhysicalLayout (d : P → ℕ) (ps : List P) (mask : P → Bool) :
    Layout.restrict mask (familyPhysicalLayout d ps) =
      familyPhysicalLayout d (ps.filter mask) := by
  simp [Layout.restrict, familyPhysicalLayout, List.filter_map, Function.comp_def]

/-- An exhaustive ordering without repetitions contains each selected party once.
Source: polynomial-PEPS, `04-compression.tex:18–25` and `233–251`. -/
theorem length_filter_region [DecidableEq P] (ps : List P) (hps : ps.Nodup)
    (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    (ps.filter fun p ↦ decide (p ∈ A)).length = A.card := by
  have hset : (ps.filter fun p ↦ decide (p ∈ A)).toFinset = A := by
    ext p
    simp [hcover p]
  exact (List.toFinset_card_of_nodup (hps.filter _)).symm.trans
    (congrArg Finset.card hset)

/-- The filtered positions enumerate exactly the original party labels in the region.
Source: polynomial-PEPS, `04-compression.tex:233–251`. -/
def filteredPartyEquiv [DecidableEq P] (ps : List P) (hps : ps.Nodup)
    (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    Fin (ps.filter fun p ↦ decide (p ∈ A)).length ≃ {p // p ∈ A} :=
  (List.Nodup.getEquiv _ (hps.filter _)).trans
    (Equiv.subtypeEquivRight fun p ↦ by simp [hcover p])

/-- The actual selected physical memory has tensor coordinates labelled by its
original parties with their original dimensions.
Source: polynomial-PEPS, `04-compression.tex:137–151` and `233–251`. -/
def familyRestrictedPhysicalBasis [DecidableEq P] (d : P → ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    OrthonormalBasis ((p : {p // p ∈ A}) → Fin (d p)) ℂ
      (Mem (Layout.restrict (fun p ↦ decide (p ∈ A))
        (familyPhysicalLayout d ps))).carrier :=
  ((familyPhysicalListBasis d (ps.filter fun p ↦ decide (p ∈ A))).reindex
    (Equiv.piCongrLeft (fun p : {p // p ∈ A} ↦ Fin (d p))
      (filteredPartyEquiv ps hps hcover A))).map
        (Layout.memCongr (restrict_familyPhysicalLayout d ps
          (fun p ↦ decide (p ∈ A)))).symm

/-- The actual regional physical dimension is the product of the original local
physical dimensions. Source: polynomial-PEPS, `04-compression.tex:137–151`. -/
theorem finrank_restrict_familyPhysicalLayout [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (A : Finset P) :
    Module.finrank ℂ (Mem (Layout.restrict (fun p ↦ decide (p ∈ A))
      (familyPhysicalLayout d ps))).carrier = ∏ p ∈ A, d p := by
  simpa only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort] using
    Module.finrank_eq_card_basis (familyRestrictedPhysicalBasis d ps hps hcover A).toBasis

/-- The source's per-party physical dimension bound implies the regional bound
without replacing any physical register by a larger space.
Source: polynomial-PEPS, `04-compression.tex:137–151`. -/
theorem finrank_restrict_familyPhysicalLayout_le [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (A : Finset P) {D : ℕ} (hD : ∀ p ∈ A, d p ≤ D) :
    Module.finrank ℂ (Mem (Layout.restrict (fun p ↦ decide (p ∈ A))
      (familyPhysicalLayout d ps))).carrier ≤ D ^ A.card := by
  rw [finrank_restrict_familyPhysicalLayout d ps hps hcover A]
  simpa only [Finset.prod_const] using Finset.prod_le_prod hD

/-- The original physical registers followed by the actual discarded private registers.
Source: polynomial-PEPS, `04-compression.tex:137–151`. -/
def familyPhysicalOutputLayout (d : P → ℕ) (ps : List P) (priv : Layout P) : Layout P :=
  familyPhysicalLayout d ps ++ priv

/-- Exact physical-private coordinates retain each party's original local dimension.
No numerical restriction is imposed on discarded private dimensions.
Source: polynomial-PEPS, `04-compression.tex:137–151` and `223–227`. -/
def familyLabelledPhysicalReadout [Fintype P] [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier] :
    Mem (familyPhysicalOutputLayout d ps priv) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (((p : P) → Fin (d p)) × Fin (Module.finrank ℂ (Mem priv).carrier)) :=
  (appendIso (familyPhysicalLayout d ps) priv).trans
    (((familyLabelledPhysicalBasis d ps hps hcover).tensorProduct
      (stdOrthonormalBasis ℂ (Mem priv).carrier)).repr)

/-- Split the original dependent physical configuration into region and exterior.
Source: polynomial-PEPS, `04-compression.tex:233–251`. -/
def familyRegionalPhysicalIndexEquiv [DecidableEq P] (d : P → ℕ) (A : Finset P) :
    ((p : P) → Fin (d p)) ≃
      ((p : {p // p ∈ A}) → Fin (d p)) × ((p : {p // p ∉ A}) → Fin (d p)) :=
  Equiv.piEquivPiSubtypeProd (fun p : P ↦ p ∈ A) (fun p ↦ Fin (d p))

/-- Exact regional readout on the original physical/private memory; the exterior
physical coordinates and private registers are grouped into the discarded factor.
Source: polynomial-PEPS, `04-compression.tex:137–151` and `223–251`. -/
def familyRegionalPhysicalReadout [Fintype P] [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier] (A : Finset P) :
    Mem (familyPhysicalOutputLayout d ps priv) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (((p : {p // p ∈ A}) → Fin (d p)) ×
        (((p : {p // p ∉ A}) → Fin (d p)) × Fin (Module.finrank ℂ (Mem priv).carrier))) :=
  (appendIso (familyPhysicalLayout d ps) priv).trans
    ((((familyLabelledPhysicalBasis d ps hps hcover).tensorProduct
      (stdOrthonormalBasis ℂ (Mem priv).carrier)).reindex
        ((Equiv.prodCongr (familyRegionalPhysicalIndexEquiv d A)
          (Equiv.refl (Fin (Module.finrank ℂ (Mem priv).carrier)))).trans
            (Equiv.prodAssoc _ _ _))).repr)

/-- The actual regional readout preserves vector norms and is a contraction.
Source: polynomial-PEPS, `04-compression.tex:223–251`. -/
theorem norm_familyRegionalPhysicalReadout_le_one [Fintype P] [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier] (A : Finset P) :
    ‖isoL (familyRegionalPhysicalReadout d ps hps hcover priv A)‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- Original party labels are unchanged by the family physical layout.
Source: polynomial-PEPS, `04-compression.tex:137–151`. -/
theorem familyPhysicalLayout_owners (d : P → ℕ) (ps : List P) :
    (familyPhysicalLayout d ps).map Reg.owner = ps := by
  simp [familyPhysicalLayout, Function.comp_def]

/-- Regional coordinates split the same original party-dependent configuration.
Source: polynomial-PEPS, `04-compression.tex:137–151` and `223–251`. -/
theorem familyRegionalPhysicalReadout_apply [Fintype P] [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier] (A : Finset P)
    (x : Mem (familyPhysicalOutputLayout d ps priv))
    (s : (p : {p // p ∈ A}) → Fin (d p))
    (t : (p : {p // p ∉ A}) → Fin (d p))
    (i : Fin (Module.finrank ℂ (Mem priv).carrier)) :
    familyRegionalPhysicalReadout d ps hps hcover priv A x (s, (t, i)) =
      familyLabelledPhysicalReadout d ps hps hcover priv x
        ((familyRegionalPhysicalIndexEquiv d A).symm (s, t), i) := by
  let B := (familyLabelledPhysicalBasis d ps hps hcover).tensorProduct
    (stdOrthonormalBasis ℂ (Mem priv).carrier)
  let e := (Equiv.prodCongr (familyRegionalPhysicalIndexEquiv d A)
    (Equiv.refl (Fin (Module.finrank ℂ (Mem priv).carrier)))).trans (Equiv.prodAssoc _ _ _)
  change (B.reindex e).repr ((appendIso (familyPhysicalLayout d ps) priv) x) (s, (t, i)) =
    B.repr ((appendIso (familyPhysicalLayout d ps) priv) x)
      ((familyRegionalPhysicalIndexEquiv d A).symm (s, t), i)
  exact B.repr_reindex e _ (s, (t, i))

/-- The regional coordinate set has the product of the original local dimensions.
Source: polynomial-PEPS, `04-compression.tex:137–151` and `233–251`. -/
theorem card_familyRegionalPhysicalIndex [DecidableEq P] (d : P → ℕ) (A : Finset P) :
    Fintype.card ((p : {p // p ∈ A}) → Fin (d p)) = ∏ p ∈ A, d p := by
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort]
end TNLean.PEPS.PairEffect
