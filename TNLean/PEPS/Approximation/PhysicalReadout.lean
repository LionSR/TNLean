/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.PartyPartition
import Mathlib.Data.List.NodupEquivFin

/-! Labelled physical outputs with unrestricted private dimensions.
Source: polynomial-PEPS, `04-compression.tex:18–25`, `218–229`.
-/
noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap
variable {P : Type}

/-- One physical register of dimension `d` for every party in the given order.
The owner of each physical register is retained explicitly.
Source: polynomial-PEPS, `04-compression.tex:18–25`. -/
def physicalLayout (d : ℕ) (ps : List P) : Layout P :=
  ps.map fun p ↦ ⟨p, euc (Fin d)⟩

/-- Tensor basis of the actual physical memory; its indices assign one value
in `Fin d` to each register occurrence.
Source: polynomial-PEPS, `04-compression.tex:18–25`. -/
def physicalListBasis (d : ℕ) : (ps : List P) →
    OrthonormalBasis (Fin ps.length → Fin d) ℂ (Mem (physicalLayout d ps)).carrier
  | [] => by
      convert OrthonormalBasis.singleton (Fin 0 → Fin d) ℂ <;> rfl
  | p :: ps => ((EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct
      (physicalListBasis d ps)).reindex (Fin.consEquiv (fun _ ↦ Fin d))

/-- Physical coordinates are labelled by the original parties, not by discarded
private register dimensions. Source: polynomial-PEPS, `04-compression.tex:18–25`. -/
def labelledPhysicalBasis [Fintype P] [DecidableEq P] (d : ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) :
    OrthonormalBasis (P → Fin d) ℂ (Mem (physicalLayout d ps)).carrier :=
  (physicalListBasis d ps).reindex
    (Equiv.piCongrLeft' (fun _ : Fin ps.length ↦ Fin d)
      (List.Nodup.getEquivOfForallMemList ps hps hcover))

/-- Original output: one physical register at each party, followed by the actual
private registers which will be discarded.
Source: polynomial-PEPS, `04-compression.tex:18–25` and `223–227`. -/
def physicalOutputLayout (d : ℕ) (ps : List P) (priv : Layout P) : Layout P :=
  physicalLayout d ps ++ priv

/-- Exact coordinates for the original labelled physical output and discarded
private memory. Finite-dimensionality is the source convention; its value is
unrestricted. Source: polynomial-PEPS, `04-compression.tex:18` and `223–227`. -/
def labelledPhysicalReadout [Fintype P] [DecidableEq P] (d : ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (priv : Layout P)
    [FiniteDimensional ℂ (Mem priv).carrier] :
    Mem (physicalOutputLayout d ps priv) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((P → Fin d) × Fin (Module.finrank ℂ (Mem priv).carrier)) :=
  (appendIso (physicalLayout d ps) priv).trans
    (((labelledPhysicalBasis d ps hps hcover).tensorProduct
      (stdOrthonormalBasis ℂ (Mem priv).carrier)).repr)

/-- The physical register owners are exactly the original party ordering.
Source: polynomial-PEPS, `04-compression.tex:18–25`. -/
theorem physicalLayout_owners (d : ℕ) (ps : List P) :
    (physicalLayout d ps).map Reg.owner = ps := by
  simp [physicalLayout, Function.comp_def]

/-- A region with `|A|` parties has precisely `d^|A|` physical configurations.
Private registers do not appear in this cardinality.
Source: polynomial-PEPS, `04-compression.tex:18–25` and `233–251`. -/
theorem card_regionalPhysicalIndex [DecidableEq P] (d : ℕ) (A : Finset P) :
    Fintype.card ({p // p ∈ A} → Fin d) = d ^ A.card := by
  simp

/-- Split physical configurations according to their original party labels.
Source: polynomial-PEPS, `04-compression.tex:233–251`. -/
def regionalPhysicalIndexEquiv [DecidableEq P] (d : ℕ) (A : Finset P) :
    (P → Fin d) ≃ ({p // p ∈ A} → Fin d) × ({p // p ∉ A} → Fin d) :=
  Equiv.piEquivPiSubtypeProd (fun p : P ↦ p ∈ A) (fun _ ↦ Fin d)

/-- Exact regional readout: the physical coordinates of the region are retained;
exterior physical coordinates and the actual private registers are discarded.
Source: polynomial-PEPS, `04-compression.tex:223–251`. -/
def regionalPhysicalReadout [Fintype P] [DecidableEq P] (d : ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (priv : Layout P)
    [FiniteDimensional ℂ (Mem priv).carrier] (A : Finset P) :
    Mem (physicalOutputLayout d ps priv) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (({p // p ∈ A} → Fin d) ×
        (({p // p ∉ A} → Fin d) × Fin (Module.finrank ℂ (Mem priv).carrier))) :=
  (appendIso (physicalLayout d ps) priv).trans
    ((((labelledPhysicalBasis d ps hps hcover).tensorProduct
      (stdOrthonormalBasis ℂ (Mem priv).carrier)).reindex
        ((Equiv.prodCongr (regionalPhysicalIndexEquiv d A)
          (Equiv.refl (Fin (Module.finrank ℂ (Mem priv).carrier)))).trans
            (Equiv.prodAssoc _ _ _))).repr)

/-- The actual regional readout is a contraction.
Source: polynomial-PEPS, `04-compression.tex:223–251`. -/
theorem norm_regionalPhysicalReadout_le_one [Fintype P] [DecidableEq P]
    (d : ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier] (A : Finset P) :
    ‖isoL (regionalPhysicalReadout d ps hps hcover priv A)‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- The regional coordinate is obtained by splitting the same labelled physical
configuration, not by choosing a new comparison density.
Source: polynomial-PEPS, `04-compression.tex:223–251`. -/
theorem regionalPhysicalReadout_apply [Fintype P] [DecidableEq P]
    (d : ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier] (A : Finset P)
    (x : Mem (physicalOutputLayout d ps priv))
    (s : {p // p ∈ A} → Fin d) (t : {p // p ∉ A} → Fin d)
    (i : Fin (Module.finrank ℂ (Mem priv).carrier)) :
    regionalPhysicalReadout d ps hps hcover priv A x (s, (t, i)) =
      labelledPhysicalReadout d ps hps hcover priv x
        ((regionalPhysicalIndexEquiv d A).symm (s, t), i) := by
  let B := (labelledPhysicalBasis d ps hps hcover).tensorProduct
    (stdOrthonormalBasis ℂ (Mem priv).carrier)
  let e := (Equiv.prodCongr (regionalPhysicalIndexEquiv d A)
    (Equiv.refl (Fin (Module.finrank ℂ (Mem priv).carrier)))).trans (Equiv.prodAssoc _ _ _)
  change (B.reindex e).repr ((appendIso (physicalLayout d ps) priv) x) (s, (t, i)) =
    B.repr ((appendIso (physicalLayout d ps) priv) x)
      ((regionalPhysicalIndexEquiv d A).symm (s, t), i)
  exact B.repr_reindex e _ (s, (t, i))

/-- The actual physical Hilbert space of a region has dimension `d^|A|`.
Source: polynomial-PEPS, `04-compression.tex:18–25` and `233–251`. -/
theorem finrank_regionalPhysicalSpace (d : ℕ) (A : Finset P) :
    Module.finrank ℂ (EuclideanSpace ℂ ({p // p ∈ A} → Fin d)) = d ^ A.card := by
  classical
  simp
end TNLean.PEPS.PairEffect

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- Selecting physical register owners selects exactly the corresponding entries
of the original party ordering. Source: polynomial-PEPS, `04-compression.tex:233–251`. -/
theorem restrict_physicalLayout (d : ℕ) (ps : List P) (mask : P → Bool) :
    Layout.restrict mask (physicalLayout d ps) = physicalLayout d (ps.filter mask) := by
  simp [Layout.restrict, physicalLayout, List.filter_map, Function.comp_def]

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

/-- The actual tensor product of `n` physical registers has dimension `d^n`.
Source: polynomial-PEPS, `04-compression.tex:18–25`. -/
theorem finrank_physicalLayout (d : ℕ) (ps : List P) :
    Module.finrank ℂ (Mem (physicalLayout d ps)).carrier = d ^ ps.length := by
  classical
  simpa using Module.finrank_eq_card_basis (physicalListBasis d ps).toBasis

/-- The actual memory of the physical registers owned by a region has
precisely dimension `d^|A|`; discarded private dimensions do not occur.
Source: polynomial-PEPS, `04-compression.tex:18–25` and `233–251`. -/
theorem finrank_restrict_physicalLayout [DecidableEq P]
    (d : ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (A : Finset P) :
    Module.finrank ℂ (Mem (Layout.restrict (fun p ↦ decide (p ∈ A))
      (physicalLayout d ps))).carrier = d ^ A.card := by
  have h := (Layout.memCongr (restrict_physicalLayout d ps
    (fun p ↦ decide (p ∈ A)))).toLinearEquiv.finrank_eq
  exact h.trans ((finrank_physicalLayout d _).trans
    (congrArg (fun n ↦ d ^ n) (length_filter_region ps hps hcover A)))

/-- The filtered positions enumerate exactly the original party labels in the region.
Source: polynomial-PEPS, `04-compression.tex:233–251`. -/
def filteredPartyEquiv [DecidableEq P] (ps : List P) (hps : ps.Nodup)
    (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    Fin (ps.filter fun p ↦ decide (p ∈ A)).length ≃ {p // p ∈ A} :=
  (List.Nodup.getEquiv _ (hps.filter _)).trans
    (Equiv.subtypeEquivRight fun p ↦ by simp [hcover p])

/-- Tensor coordinates on the actual selected physical registers, labelled by
original parties. Source: polynomial-PEPS, `04-compression.tex:18–25` and `233–251`. -/
def restrictedPhysicalBasis [DecidableEq P] (d : ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    OrthonormalBasis ({p // p ∈ A} → Fin d) ℂ
      (Mem (Layout.restrict (fun p ↦ decide (p ∈ A)) (physicalLayout d ps))).carrier :=
  ((physicalListBasis d (ps.filter fun p ↦ decide (p ∈ A))).reindex
    (Equiv.piCongrLeft' (fun _ ↦ Fin d) (filteredPartyEquiv ps hps hcover A))).map
      (Layout.memCongr (restrict_physicalLayout d ps (fun p ↦ decide (p ∈ A)))).symm
end TNLean.PEPS.PairEffect
