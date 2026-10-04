/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.WState
import TNLean.MPS.ParentHamiltonian.GroundSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# One-species product vacua with boundary states

The matrices `A⁰ = diag(q, 1)` and `A¹ = |0⟩⟨1|` produce a product vacuum
and a one-particle state with amplitude `qᵏ` at site `k`. Their full open
matrix-product space is exactly the span of these two vectors at every positive
length. The complex parameter allows the phase in the original PVBS model.

Source: Bachmann and Nachtergaele, arXiv:1112.4097, Section II,
equations (1)–(8), with one particle species and the physical sites in
left-to-right order. The review arXiv:2011.12127 uses the parameter `q = 1 + λ`.
The critical value is `q = 1`, where the boundary excitation is the W state.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The one-species PVBS tensor, with `A⁰ = diag(q,1)` and `A¹ = |0⟩⟨1|`. -/
def pvbsTensor (q : ℂ) : MPSTensor 2 2 :=
  fun i => if i = 0 then !![q, 0; 0, 1] else wRaising

/-- The vacuum configuration vector `|0⋯0⟩`. -/
noncomputable def pvbsVacuum (N : ℕ) : NSiteSpace 2 N := Pi.single 0 1

/-- The one-particle PVBS vector. Its coefficient at a particle on site `k`
is `qᵏ`, with the first site numbered zero. -/
noncomputable def pvbsEdge (q : ℂ) : (N : ℕ) → NSiteSpace 2 N
  | 0 => 0
  | N + 1 => fun σ => if σ 0 = 0 then q * pvbsEdge q N (Fin.tail σ)
      else pvbsVacuum N (Fin.tail σ)

/-- The PVBS tensor becomes the open-boundary W tensor at the critical parameter. -/
@[simp] theorem pvbsTensor_one : pvbsTensor 1 = wTensor := by
  funext i
  fin_cases i <;> simp [pvbsTensor, wTensor, wRaising, Matrix.one_fin_two]

/-- The vacuum coefficient at its unique nonzero configuration. -/
@[simp] theorem pvbsVacuum_zero (N : ℕ) : pvbsVacuum N 0 = 1 := by
  simp [pvbsVacuum]

/-- The empty-chain vacuum has coefficient one. -/
@[simp] theorem pvbsVacuum_nil (σ : Cfg 2 0) : pvbsVacuum 0 σ = 1 := by
  have hσ : σ = 0 := Subsingleton.elim _ _
  simpa only [hσ] using pvbsVacuum_zero 0

/-- Appending a first physical site to the vacuum. -/
theorem pvbsVacuum_cons (i : Fin 2) {N : ℕ} (σ : Cfg 2 N) :
    pvbsVacuum (N + 1) (Fin.cons i σ) = if i = 0 then pvbsVacuum N σ else 0 := by
  have heq : Fin.cons i σ = (0 : Cfg 2 (N + 1)) ↔ i = 0 ∧ σ = 0 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, funext fun j => congrFun h j.succ⟩
    · rintro ⟨rfl, rfl⟩
      ext j
      refine Fin.cases rfl (fun _ => rfl) j
  simp [pvbsVacuum, Pi.single_apply, heq, ite_and]

/-- A zero physical site multiplies the remaining one-particle amplitude by `q`. -/
@[simp] theorem pvbsEdge_cons_zero (q : ℂ) {N : ℕ} (σ : Cfg 2 N) :
    pvbsEdge q (N + 1) (Fin.cons 0 σ) = q * pvbsEdge q N σ := by
  simp [pvbsEdge]

/-- A particle at the first physical site requires the remaining sites to be empty. -/
@[simp] theorem pvbsEdge_cons_one (q : ℂ) {N : ℕ} (σ : Cfg 2 N) :
    pvbsEdge q (N + 1) (Fin.cons 1 σ) = pvbsVacuum N σ := by
  simp [pvbsEdge]

/-- The one-particle state has no vacuum component. -/
@[simp] theorem pvbsEdge_zero (q : ℂ) (N : ℕ) : pvbsEdge q N 0 = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change q * pvbsEdge q N 0 = 0
    rw [ih, mul_zero]

/-- The first-site excitation has unit amplitude. -/
@[simp] theorem pvbsEdge_first (q : ℂ) (N : ℕ) :
    pvbsEdge q (N + 1) (Fin.cons 1 0) = 1 := by
  simp

/-- The vacuum vanishes on the first-site excitation. -/
@[simp] theorem pvbsVacuum_first (N : ℕ) :
    pvbsVacuum (N + 1) (Fin.cons 1 0) = 0 := by
  simp [pvbsVacuum_cons]

/-- All matrix elements of a PVBS word: only the vacuum and one-particle
coefficients survive. -/
theorem evalWord_pvbsTensor (q : ℂ) (N : ℕ) (σ : Cfg 2 N) :
    Kraus.evalWord (pvbsTensor q) (List.ofFn σ) =
      !![q ^ N * pvbsVacuum N σ, pvbsEdge q N σ; 0, pvbsVacuum N σ] := by
  induction N with
  | zero =>
    have hσ : σ = 0 := Subsingleton.elim _ _
    subst σ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pvbsEdge, pvbsVacuum]
  | succ N ih =>
    obtain ⟨⟨i, τ⟩, rfl⟩ := (Fin.consEquiv fun _ : Fin (N + 1) => Fin 2).surjective σ
    change Kraus.evalWord (pvbsTensor q) (List.ofFn (Fin.cons i τ)) =
      !![q ^ (N + 1) * pvbsVacuum (N + 1) (Fin.cons i τ),
        pvbsEdge q (N + 1) (Fin.cons i τ); 0, pvbsVacuum (N + 1) (Fin.cons i τ)]
    rw [List.ofFn_cons, Kraus.evalWord_cons, ih]
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [pvbsTensor, wRaising, Matrix.mul_apply, Fin.sum_univ_two,
        pvbsVacuum_cons, pvbsEdge, pow_succ, mul_assoc, mul_left_comm]

/-- The standard open-boundary contraction is the geometric one-particle state. -/
theorem pvbsTensor_openState (q : ℂ) (N : ℕ) :
    openState wLeftBoundary wRightBoundary (pvbsTensor q) N = pvbsEdge q N := by
  ext σ
  simp [openState, openCoeff, wLeftBoundary, wRightBoundary, evalWord_pvbsTensor]

/-- At the critical parameter, the PVBS boundary state is the unnormalized W state. -/
theorem pvbsEdge_one (N : ℕ) : pvbsEdge 1 N = wIndicator N := by
  rw [← pvbsTensor_openState, pvbsTensor_one, wTensor_openState_eq_wIndicator]

/-- Arbitrary matrix boundaries give exactly two coefficients: vacuum and particle. -/
theorem groundSpaceMap_pvbsTensor (q : ℂ) (N : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    groundSpaceMap (pvbsTensor q) N X =
      (q ^ N * X 0 0 + X 1 1) • pvbsVacuum N + X 1 0 • pvbsEdge q N := by
  ext σ
  simp [groundSpaceMap_apply, evalWord_pvbsTensor, Matrix.trace, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]
  ring

/-- Membership in the open MPS space is precisely a vacuum-particle superposition. -/
theorem mem_groundSpace_pvbsTensor_iff (q : ℂ) (N : ℕ) (v : NSiteSpace 2 N) :
    v ∈ groundSpace (pvbsTensor q) N ↔
      ∃ a b : ℂ, v = a • pvbsVacuum N + b • pvbsEdge q N := by
  rw [groundSpace, LinearMap.mem_range]
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨_, _, groundSpaceMap_pvbsTensor q N X⟩
  · rintro ⟨a, b, rfl⟩
    refine ⟨!![0, 0; b, a], ?_⟩
    simp [groundSpaceMap_pvbsTensor]

/-- The open MPS space is the span of the vacuum and the geometric edge vector. -/
theorem groundSpace_pvbsTensor (q : ℂ) (N : ℕ) :
    groundSpace (pvbsTensor q) N = Submodule.span ℂ {pvbsVacuum N, pvbsEdge q N} := by
  ext v
  rw [mem_groundSpace_pvbsTensor_iff, Submodule.mem_span_pair]
  exact ⟨fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩, fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩⟩

/-- The two open-boundary states are linearly independent on every nonempty chain. -/
theorem linearIndependent_pvbs_states (q : ℂ) (N : ℕ) :
    LinearIndependent ℂ ![pvbsVacuum (N + 1), pvbsEdge q (N + 1)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := congrFun hc (0 : Cfg 2 (N + 1))
  have h1 := congrFun hc (Fin.cons 1 0)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    pvbsVacuum_zero, pvbsEdge_zero, pvbsVacuum_first, pvbsEdge_first,
    mul_one, mul_zero, add_zero, zero_add, Pi.zero_apply] at h0 h1
  intro i
  fin_cases i <;> assumption

/-- The open MPS boundary space has exactly two dimensions at every positive length. -/
theorem finrank_groundSpace_pvbsTensor (q : ℂ) (N : ℕ) :
    Module.finrank ℂ (groundSpace (pvbsTensor q) (N + 1)) = 2 := by
  rw [groundSpace_pvbsTensor, ← Matrix.range_cons_cons_empty _ _ ![]]
  simpa using finrank_span_eq_card (linearIndependent_pvbs_states q N)

/-- The one-particle amplitude is the geometric weight printed in the PVBS construction. -/
theorem pvbsEdge_excitedAt (q : ℂ) (N : ℕ) (k : Fin N) :
    pvbsEdge q N (excitedAt N k) = q ^ k.val := by
  induction N with
  | zero => exact k.elim0
  | succ N ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · have h : excitedAt (N + 1) 0 = Fin.cons 1 0 := by
        funext j
        refine Fin.cases (by simp [excitedAt]) (fun j => by simp [excitedAt]) j
      simp [h]
    · have h : excitedAt (N + 1) k.succ = Fin.cons 0 (excitedAt N k) := by
        funext j
        refine Fin.cases (by simp [excitedAt, eq_comm]) (fun j => by simp [excitedAt]) j
      simp [h, ih, pow_succ, mul_comm]

/-- The vacuum coefficient vanishes on any one-particle configuration. -/
theorem pvbsVacuum_excitedAt (N : ℕ) (k : Fin N) : pvbsVacuum N (excitedAt N k) = 0 := by
  have h : excitedAt N k ≠ 0 := by
    intro h
    have hh := congrFun h k
    simp [excitedAt] at hh
  simp [pvbsVacuum, h]

end MPSTensor
