import TNLean.PEPS.TorusDualOpenDeformation

open TNLean.PEPS.DependentBondNetwork

#print axioms network_deltaCompletedTensor

open TNLean.PEPS

-- Parallel edges and self-edge incidence coordinates are preserved.
example (v : TorusVertex 1 1) :
    Fintype.card (IncidentEndpoint torusLabelledBondTail torusLabelledBondHead v) = 4 :=
  card_torusIncidentEndpoint v

-- A translated collar crosses a coordinate seam while remaining embedded.
private def collar : TorusDualCollar 5 5 :=
  ⟨⟨(4, 4), 2, 2, by decide, by decide⟩, by decide, by decide⟩

example : collar.patch.origin ∈ collar.region := collar.origin_mem

example : TorusDualCollar 2 2 :=
  ⟨⟨(0, 0), 0, 0, by decide, by decide⟩, by decide, by decide⟩

example : ¬ ∃ C : TorusDualCollar 3 3, C.patch.cols = 2 := by
  rintro ⟨C, hc⟩
  have := C.cols_lt
  omega

#print axioms labelledNetwork_eq_torusBondNetwork
#print axioms torusBondNetwork_deltaCompletedTensor
#print axioms TorusDualCollar.neighbors_mem
#print axioms TorusDualCollar.exists_internalFluxGauge
#print axioms TorusDualCollar.openCoefficient_eq
#print axioms TorusDualCollar.correlatedBoundary_eq

-- The delta bridge uses a labelled self bond with its two independent incidences.
example (A : (v : (Set.univ : Set Unit)) →
    LocalConfig (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) (fun _ ↦ Fin 2) v.1 → ℂ)
    (O : Unit → Matrix (Fin 2) (Fin 2) ℂ)
    (θ : RegionBoundaryEndpoint (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) Set.univ → Fin 2) :
    network (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) (fun _ ↦ Fin 2)
      (deltaCompletedTensor _ _ Set.univ A 0 θ)
      (internalBondMatrices _ _ Set.univ O) (fun _ ↦ PUnit.unit.{1}) =
      openCoefficient _ _ Set.univ A O θ :=
  network_deltaCompletedTensor _ _ Set.univ A O 0 θ

-- Empty virtual alphabets do not introduce a hidden Nonempty premise.
example (A : collar.region → (Empty × Empty × Empty × Empty) → ℂ)
    (O : TorusLabelledBond 5 5 → Matrix Empty Empty ℂ)
    (θ : RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead collar.region → Empty) :
    torusOpenCoefficient collar.region A O θ = 0 :=
  torusOpenCoefficient_eq_zero_of_isEmpty _ ⟨collar.patch.origin, collar.origin_mem⟩ A O θ

#print axioms torusOpenCoefficient_eq_zero_of_isEmpty
set_option pp.proofs true in
#print TorusDualCollar.openCoefficient_eq
