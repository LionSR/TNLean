import TNLean.PEPS.Examples.HoneycombCluster

/-! Edgewise contraction of six graph-state bonds with six outgoing legs.
The edge lists are parameters: identifying them with all the incidences of a
honeycomb face is a separate geometric step. -/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Sum the six internal bond indices while fixing the six boundary indices.
Each factor is the same oriented leg used in graphStatePEPS.component. -/
noncomputable def sixBondContraction (inner outer : Fin 6 → Edge G)
    (site : Fin 6 → V) (s : V → Fin 2) (β : Fin 6 → Fin 2) : ℂ :=
  ∑ η : Fin 6 → Fin 2,
    (∏ i, graphStateLeg G (inner i).1.1 (inner i) (η i) (s (inner i).1.1) *
      graphStateLeg G (inner i).1.2 (inner i) (η i) (s (inner i).1.2)) *
    ∏ i, graphStateLeg G (site i) (outer i) (β i) (s (site i))

/-- Each contracted internal bond contributes the normalized controlled-Z sign.
The remaining factors are the six boundary identity or Hadamard entries. -/
theorem sixBondContraction_factor (inner outer : Fin 6 → Edge G)
    (site : Fin 6 → V) (s : V → Fin 2) (β : Fin 6 → Fin 2) :
    sixBondContraction G inner outer site s β =
      (∏ i, hadamardEntry (s (inner i).1.1) (s (inner i).1.2)) *
      ∏ i, graphStateLeg G (site i) (outer i) (β i) (s (site i)) := by
  classical
  unfold sixBondContraction
  rw [← Finset.sum_mul, ← Fintype.prod_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have h : (inner i).1.1 ≠ (inner i).1.2 := (inner i).2.1.ne
  simp [graphStateLeg, h]

end TNLean.PEPS
