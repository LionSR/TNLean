import TNLean.PEPS.TorusDualOpenDeformation

/-! Regressions and axiom audits for the native collared open-boundary specialization. -/

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

private def fullCollar : TorusDualCollar 2 2 :=
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

-- The delta-exterior identity uses a labelled self bond with its two independent incidences.
example (A : (v : (Set.univ : Set Unit)) →
    LocalConfig (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) (fun _ ↦ Fin 2) v.1 → ℂ)
    (O : Unit → Matrix (Fin 2) (Fin 2) ℂ)
    (θ : RegionBoundaryEndpoint (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) Set.univ → Fin 2) :
    network (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) (fun _ ↦ Fin 2)
      (deltaCompletedTensor (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) Set.univ A 0 θ)
      (internalBondMatrices (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) Set.univ O)
      (fun _ ↦ PUnit.unit.{1}) =
      openCoefficient (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) Set.univ A O θ :=
  network_deltaCompletedTensor (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ()) Set.univ A O 0 θ

-- This zero-size patch has a full 2×2 collar, hence no crossing incidences.
private theorem fullCollar_mem (v : TorusVertex 2 2) : v ∈ fullCollar.region := by
  rcases v with ⟨x, y⟩
  fin_cases x <;> fin_cases y
  · exact ⟨0, by decide, 0, by decide, by decide⟩
  · exact ⟨0, by decide, 1, by decide, by decide⟩
  · exact ⟨1, by decide, 0, by decide, by decide⟩
  · exact ⟨1, by decide, 1, by decide, by decide⟩

private def emptyBoundary :
    RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead fullCollar.region → Empty :=
  fun p ↦ False.elim (p.2.2 (fullCollar_mem
    (endpointVertex torusLabelledBondTail torusLabelledBondHead (p.1.1, !p.1.2))))

-- An explicit boundary assignment exists: this Empty-alphabet regression is nonvacuous.
example (A : fullCollar.region → (Empty × Empty × Empty × Empty) → ℂ)
    (O : TorusLabelledBond 2 2 → Matrix Empty Empty ℂ) :
    torusOpenCoefficient fullCollar.region A O emptyBoundary = 0 :=
  torusOpenCoefficient_eq_zero_of_isEmpty _
    ⟨fullCollar.patch.origin, fullCollar.origin_mem⟩ A O emptyBoundary

#print axioms torusOpenCoefficient_eq_zero_of_isEmpty
#check TorusDualCollar.openCoefficient_eq
