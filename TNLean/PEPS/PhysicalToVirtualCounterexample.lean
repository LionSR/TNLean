import TNLean.PEPS.InsertionRealization

/-!
# The unrestricted physical-to-virtual recovery is false without positive bonds

This file is a checked counterexample. The statement of
`physical_to_virtual_insertion` is false once the positive-bond hypothesis is
dropped: a zero-dimensional edge incident to an endpoint empties the edge
boundary configuration, so the resonate hypothesis holds vacuously while the
recovery conclusion remains a genuine constraint that fails for a nontrivial
right-endpoint operator.

The explicit witness is the graph on three vertices with the distinguished edge
of bond dimension one and a second edge of bond dimension zero at the left
endpoint. `PhysicalToVirtualInsertionStatement_false` refutes the universe-0
specialization of the hypothesis-free statement;
`physical_to_virtual_insertion` itself carries the restored hypothesis that
every bond dimension is positive.

Source: the positive-bond assumption is the standing assumption of
arXiv:1804.04964 that injective PEPS have nonzero-dimensional virtual bond
spaces. The same defect was found and corrected for the edge-blocked three-site
injectivity (issue #1366).
-/

namespace TNLean
namespace PEPS
namespace PhysicalToVirtualCounterexample

open scoped BigOperators

abbrev V3 := Fin 3

def adj3 (a b : V3) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

instance : DecidableRel adj3 := by unfold adj3; infer_instance

def G3 : SimpleGraph V3 where
  Adj := adj3
  symm := by
    intro a b h
    unfold adj3 at *
    fin_cases a <;> fin_cases b <;> simp_all
  loopless := ⟨by intro a; unfold adj3; fin_cases a <;> simp⟩

instance : DecidableRel G3.Adj := by
  change DecidableRel adj3
  infer_instance

def e3 : Edge G3 := ⟨(0, 1), by constructor <;> decide⟩
def f3 : Edge G3 := ⟨(0, 2), by constructor <;> decide⟩

theorem f3_ne_e3 : f3 ≠ e3 := by decide

/-- bond dimension: 1 on e (distinguished), 0 on f (the extra zero bond at u). -/
def bd : Edge G3 → ℕ := fun g => if g = e3 then 1 else 0

theorem bd_e3 : bd e3 = 1 := by simp [bd]
theorem bd_f3 : bd f3 = 0 := by simp [bd, f3_ne_e3]

/-- The tensor: d = 2. Right endpoint (vertex 1) outputs e_0 = ![1,0] on its
single config; other vertices output 0 (their config spaces are empty anyway). -/
def A3 : Tensor G3 2 where
  bondDim := bd
  component v :=
    match v with
    | 0 => fun _ _ => 0
    | 1 => fun _ => ![1, 0]
    | 2 => fun _ _ => 0

theorem A3_bondDim_e3 : A3.bondDim e3 = 1 := bd_e3
theorem A3_bondDim_f3 : A3.bondDim f3 = 0 := bd_f3

theorem e3_left : e3.1.1 = (0 : V3) := rfl
theorem e3_right : e3.1.2 = (1 : V3) := rfl

/-- f3 as an incident edge of vertex 0. -/
def f3incident : IncidentEdge G3 (0 : V3) := ⟨f3, Or.inl rfl⟩

/-- Left endpoint local config is empty (incident edge f3 has bond 0). -/
instance : IsEmpty (LocalVirtualConfig A3 (0 : V3)) := by
  refine ⟨fun c => ?_⟩
  have h := c f3incident
  rw [show A3.bondDim f3incident.1 = 0 from A3_bondDim_f3] at h
  exact h.elim0

/-- f3 is an other-incident edge of vertex 0 relative to the distinguished edge. -/
def f3other : OtherIncidentEdge (G := G3) (0 : V3) (edgeLeftIncident (G := G3) e3) :=
  ⟨f3incident, by decide⟩

/-- Left residual config is empty (it includes the f3-coordinate of bond 0). -/
instance : IsEmpty (ResidualLocalConfig A3 (edgeLeftIncident (G := G3) e3)) := by
  refine ⟨fun c => ?_⟩
  have h := c f3other
  rw [show A3.bondDim f3other.1.1 = 0 from A3_bondDim_f3] at h
  exact h.elim0

/-- Hence the edge-middle boundary label is empty. -/
instance : IsEmpty (EdgeMiddleBoundaryLabel (G := G3) A3 e3) :=
  Prod.isEmpty_left

/-- The only incident edge of vertex 1 is the distinguished edge e3. -/
theorem incident_one_eq (ie : IncidentEdge G3 (1 : V3)) : ie.1 = e3 := by
  revert ie; decide

/-- Every incident-edge bond at vertex 1 has dimension 1. -/
theorem bondDim_incident_one (ie : IncidentEdge G3 (1 : V3)) :
    A3.bondDim ie.1 = 1 := by
  rw [incident_one_eq ie]; exact A3_bondDim_e3

/-- The right endpoint local config type has exactly one element. -/
theorem rightConfig_unique :
    ∀ a b : LocalVirtualConfig A3 (1 : V3), a = b := by
  intro a b
  funext ie
  have h1 : A3.bondDim ie.1 = 1 := bondDim_incident_one ie
  haveI : Subsingleton (Fin (A3.bondDim ie.1)) := by rw [h1]; infer_instance
  apply Subsingleton.elim

/-- `A3.component 1 η = ![1,0]` for every (the unique) config `η`. -/
theorem A3_component_one (η : LocalVirtualConfig A3 (1 : V3)) :
    A3.component (1 : V3) η = ![1, 0] := rfl

/-- The right endpoint local tensor map applied to `c` evaluated at index 0
recovers `c` at the unique config. -/
theorem localTensorMap_one_apply_zero (c : LocalVirtualConfig A3 (1 : V3) → ℂ)
    (η₀ : LocalVirtualConfig A3 (1 : V3)) :
    localTensorMap A3 (1 : V3) c 0 = c η₀ := by
  classical
  simp only [localTensorMap, Fintype.linearCombination_apply]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single η₀]
  · simp [A3_component_one]
  · intro b _ hb
    rw [rightConfig_unique b η₀] at hb
    exact absurd rfl hb
  · intro h; exact absurd (Finset.mem_univ η₀) h

/-- Right endpoint local tensor map is injective. -/
theorem right_injective : Function.Injective (localTensorMap A3 (1 : V3)) := by
  intro c c' h
  funext η
  have h0 := congrFun h 0
  rw [localTensorMap_one_apply_zero c η, localTensorMap_one_apply_zero c' η] at h0
  exact h0

/-- Left endpoint local tensor map is injective (its domain is empty). -/
theorem left_injective : Function.Injective (localTensorMap A3 (0 : V3)) := by
  intro c c' _
  funext η
  exact (IsEmpty.false η).elim

/-- Middle tensor family is linearly independent (its index type is empty). -/
theorem middle_injective : EdgeMiddleTensorInjective (G := G3) A3 e3 :=
  linearIndependent_empty_type

/-- The blocked three-site object is injective. -/
theorem A3_edgeBlockedThreeSiteInjective :
    EdgeBlockedThreeSiteInjective (G := G3) A3 e3 :=
  { left_injective := by
      have : e3.1.1 = (0 : V3) := e3_left
      rw [this]; exact left_injective
    middle_injective := middle_injective
    right_injective := by
      have : e3.1.2 = (1 : V3) := e3_right
      rw [this]; exact right_injective }

/-- The ordinary edge-boundary configuration type is empty (its left residual
field ranges over an empty type). -/
instance : IsEmpty (EdgeBoundaryConfig (G := G3) A3 e3) := by
  refine ⟨fun β => ?_⟩
  exact (IsEmpty.false β.leftResidual).elim

/-- The "bad" right physical operator: coordinate swap on `Fin 2 → ℂ`. It sends
`![1,0]` to `![0,1]`, which is not a scalar multiple of `![1,0]`. -/
def O2bad : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x := ![x 1, x 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp

theorem O2bad_apply_e0 : O2bad (![1, 0] : Fin 2 → ℂ) = ![0, 1] := by
  funext i; fin_cases i <;> simp [O2bad]

/-- Everything in the image of the right endpoint local tensor map has a zero in
coordinate 1 (the image lies in the span of `![1,0]`). -/
theorem localTensorMap_one_apply_one (w : LocalVirtualConfig A3 (1 : V3) → ℂ) :
    localTensorMap A3 (1 : V3) w 1 = 0 := by
  classical
  simp only [localTensorMap, Fintype.linearCombination_apply]
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero ?_
  intro η _
  simp [A3_component_one]

/-- The right endpoint local config type is inhabited (assign 0 to every
incident-edge bond, each of which has dimension 1). -/
instance : Inhabited (LocalVirtualConfig A3 (1 : V3)) :=
  ⟨fun ie => ⟨0, by rw [bondDim_incident_one ie]; exact Nat.one_pos⟩⟩

/-- The unique right-endpoint config. -/
def η₀ : LocalVirtualConfig A3 (1 : V3) := default

/-- The right endpoint local tensor map sends the single basis vector to `![1,0]`. -/
theorem localTensorMap_one_single :
    localTensorMap A3 (1 : V3) (Pi.single η₀ (1 : ℂ)) = ![1, 0] := by
  rw [localTensorMap_apply_single]
  exact A3_component_one η₀

/-! ### The scope refutation -/

/-- The type of the original `physical_to_virtual_insertion` statement, generic
over the graph, vertex set, and physical dimension. This is the universe-0
specialization of the signature of `TNLean.PEPS.physical_to_virtual_insertion`. -/
def PhysicalToVirtualInsertionStatement : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (A : Tensor G d) (e : Edge G)
    (_ : EdgeBlockedThreeSiteInjective (G := G) A e)
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (_ : ∀ σ : V → Fin d,
      (∑ β : EdgeBoundaryConfig (G := G) A e,
        O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2)),
    ∃ M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
      (∀ c : LocalVirtualConfig A e.1.1 → ℂ,
        O₁ (localTensorMap A e.1.1 c) =
          localTensorMap A e.1.1
            (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose c)) ∧
        ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
          O₂ (localTensorMap A e.1.2 c) =
            localTensorMap A e.1.2
              (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c)

/-- The original `physical_to_virtual_insertion` statement is FALSE as written:
no proof of its signature can exist, because our explicit witness
`(G3, A3, e3, id, O2bad)` satisfies all of its hypotheses yet refutes its
conclusion. -/
theorem PhysicalToVirtualInsertionStatement_false :
    ¬ PhysicalToVirtualInsertionStatement := by
  intro hThm
  -- Build the resonate hypothesis at our witness (both sides empty sums).
  have hEq : ∀ σ : V3 → Fin 2,
      (∑ β : EdgeBoundaryConfig (G := G3) A3 e3,
        (LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
            (A3.component e3.1.1 (edgeLeftLocalConfig (G := G3) A3 e3 β)) (σ e3.1.1) *
          edgeOpenMiddleWeight (G := G3) A3 e3 σ β.leftResidual β.rightResidual *
          A3.component e3.1.2 (edgeRightLocalConfig (G := G3) A3 e3 β) (σ e3.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G3) A3 e3,
          A3.component e3.1.1 (edgeLeftLocalConfig (G := G3) A3 e3 β) (σ e3.1.1) *
            edgeOpenMiddleWeight (G := G3) A3 e3 σ β.leftResidual β.rightResidual *
            O2bad (A3.component e3.1.2 (edgeRightLocalConfig (G := G3) A3 e3 β)) (σ e3.1.2) := by
    intro σ
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty]
  obtain ⟨M, _, hRight⟩ :=
    hThm A3 e3 A3_edgeBlockedThreeSiteInjective LinearMap.id O2bad hEq
  have hRight' : ∀ c : LocalVirtualConfig A3 (1 : V3) → ℂ,
      O2bad (localTensorMap A3 (1 : V3) c) =
        localTensorMap A3 (1 : V3)
          (localIncidentMatrixOp A3 (edgeRightIncident (G := G3) e3) M c) := hRight
  have hr := hRight' (Pi.single η₀ (1 : ℂ))
  rw [localTensorMap_one_single] at hr
  have h1 := congrFun hr 1
  rw [O2bad_apply_e0] at h1
  rw [localTensorMap_one_apply_one] at h1
  simp at h1

end PhysicalToVirtualCounterexample
end PEPS
end TNLean
