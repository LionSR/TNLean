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
