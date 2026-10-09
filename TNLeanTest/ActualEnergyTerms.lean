/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEnergyTerms
import TNLean.PEPS.AreaLaw.Scan.FillSupportCompatibility

/-!
# Actual energy construction regressions

The auxiliary dimensions are two and three. Both off-diagonal auxiliary
changes must vanish. Disconnected physical components are retained, the empty
truncation set retains every term, dimension one remains valid, and labelled
sums and replica normalization are preserved.
-/

set_option autoImplicit false

open scoped Matrix MatrixOrder ComplexOrder Kronecker
open Entropy TensorPower TensorPower.ReplicaTransport
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

noncomputable section
namespace TNLeanTest.ActualEnergyTerms

private def aux : Bool → ℕ := fun b => if b then 3 else 2

private instance (b : Bool) : NeZero (aux b) := by
  constructor
  cases b <;> norm_num [aux]

example (v : Unit ⊕ Bool) : NeZero (augmentedDimensions 2 aux v) := inferInstance

private def configuration (x : Fin 2) (c : Fin 2) (r : Fin 3) :
    SiteConfig (augmentedDimensions (V := Unit) 2 aux) :=
  Sum.rec (fun _ => x) (fun b => match b with | false => c | true => r)

private def projector : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ :=
  Matrix.diagonal fun x => if x () = 0 then 1 else 0

-- A nonzero qubit projector has value one at every joint auxiliary basis state.
example : augmentOperator 2 aux projector (configuration 0 1 2)
    (configuration 0 1 2) = 1 := by
  simp [augmentOperator, Equiv.sumPiEquivProdPi, Equiv.coe_fn_mk, configuration, projector]

example : augmentOperator 2 aux projector (configuration 1 1 2)
    (configuration 1 1 2) = 0 := by
  simp [augmentOperator, Equiv.sumPiEquivProdPi, Equiv.coe_fn_mk, configuration, projector]

-- Two distinct labels carrying the same nonzero term still contribute twice.
example : augmentOperator 2 aux (∑ _i : Fin 2, projector) (configuration 0 1 2)
    (configuration 0 1 2) = 2 := by
  simp [augmentOperator, Equiv.sumPiEquivProdPi, Equiv.coe_fn_mk, configuration,
    projector, Matrix.ofNat_apply]

example (h : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) (x y : Fin 2) :
    augmentOperator 2 aux h (configuration x 0 0) (configuration y 0 0) =
      h (fun _ => x) (fun _ => y) := by
  simp [augmentOperator, Equiv.sumPiEquivProdPi, Equiv.coe_fn_mk, configuration]

-- Altering only C, or only R, separately detects a missing auxiliary identity.
example (h : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) (x y : Fin 2) :
    augmentOperator 2 aux h (configuration x 0 0) (configuration y 1 0) = 0 := by
  have hne : (fun b => configuration x 0 0 (.inr b)) ≠
      (fun b => configuration y 1 0 (.inr b)) := by
    intro he
    have h01 : (0 : Fin 2) = (1 : Fin 2) := congrFun he false
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) h01
  change h (fun _ => x) (fun _ => y) *
    (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ) _ _ = 0
  have hz : (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
      (fun b => configuration x 0 0 (.inr b))
      (fun b => configuration y 1 0 (.inr b)) = 0 := Matrix.one_apply_ne hne
  exact mul_eq_zero_of_right (h (fun _ => x) (fun _ => y)) hz

example (h : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) (x y : Fin 2) :
    augmentOperator 2 aux h (configuration x 0 0) (configuration y 0 2) = 0 := by
  have hne : (fun b => configuration x 0 0 (.inr b)) ≠
      (fun b => configuration y 0 2 (.inr b)) := by
    intro he
    have h02 : (0 : Fin 3) = (2 : Fin 3) := congrFun he true
    exact (by decide : (0 : Fin 3) ≠ (2 : Fin 3)) h02
  change h (fun _ => x) (fun _ => y) *
    (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ) _ _ = 0
  have hz : (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
      (fun b => configuration x 0 0 (.inr b))
      (fun b => configuration y 0 2 (.inr b)) = 0 := Matrix.one_apply_ne hne
  exact mul_eq_zero_of_right (h (fun _ => x) (fun _ => y)) hz

example (D : Finset Unit) : Sum.inr false ∉ physicalRegion D ∧
    Sum.inr true ∉ physicalRegion D := by simp [physicalRegion]

example (h : Matrix (Unit → Fin 1) (Unit → Fin 1) ℂ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    0 ≤ augmentOperator 1 aux h ∧ augmentOperator 1 aux h ≤ 1 :=
  augmentOperator_mem_Icc 1 aux h0 h1

example (h : Fin 3 → Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) :
    augmentOperator 2 aux (h 0 + h 1 + h 2) =
      ∑ i : Fin 3, augmentOperator 2 aux (h i) := by
  simpa [Fin.sum_univ_succ, add_assoc] using augmentOperator_sum 2 aux Finset.univ h

private def domain : Finset (ℤ × ℤ) := {(0, 0), (2, 0)}
private def leftSite : Site domain := ⟨(0, 0), by simp [domain]⟩
private def rightSite : Site domain := ⟨(2, 0), by simp [domain]⟩

private theorem graph_eq_bot : domainGraph domain = ⊥ := by
  ext x y
  have hx := x.property
  have hy := y.property
  simp only [domain, Finset.mem_insert, Finset.mem_singleton] at hx hy
  change ((x.val.2 = y.val.2 ∧ (x.val.1 + 1 = y.val.1 ∨ y.val.1 + 1 = x.val.1)) ∨
    (x.val.1 = y.val.1 ∧ (x.val.2 + 1 = y.val.2 ∨ y.val.2 + 1 = x.val.2))) ↔ False
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> norm_num

private def scan (A : Finset (Site domain)) :
    CollarScan (Site domain) (AdmissibleSupport domain 0) where
  graph := domainGraph domain
  A := A
  depth _ := 0
  anchor i := i.property.1.choose
  n := 1
  m := 1
  K := 1
  D := 1
  r₀ := 0
  C₁ := 1

private theorem anchor_mem (A : Finset (Site domain)) (i : AdmissibleSupport domain 0) :
    (scan A).anchor i ∈ i.val := i.property.1.choose_spec

private def rightLabel : AdmissibleSupport domain 0 :=
  ⟨{rightSite}, isAdmissibleSupport_singleton domain 0 rightSite⟩

private theorem right_anchor (A : Finset (Site domain)) :
    (scan A).anchor rightLabel = rightSite := by
  simpa only [rightLabel, Finset.mem_singleton] using anchor_mem A rightLabel

-- The retained component is the designated physical singleton, never an
-- auxiliary-augmented set or the empty set.
example (h : LocalHamiltonian domain 2 0 1) (Ω : StateSpace domain 2) (Δ : ℝ) :
    ((scan {leftSite}).actualEnergyTerms h Ω Δ 0 aux).support rightLabel =
      physicalRegion {rightSite} := by
  change physicalRegion (designatedSupport (scan {leftSite}).graph
    ((scan {leftSite}).truncationSet 0) (scan {leftSite}).r₀
    ((scan {leftSite}).anchor rightLabel)) = _
  rw [right_anchor]
  apply congrArg physicalRegion
  have hne : rightSite ≠ leftSite := by decide
  ext x
  simp [designatedSupport, componentFinset, scan, CollarScan.truncationSet,
    setDist, graph_eq_bot, SimpleGraph.edist_bot_of_ne hne, SimpleGraph.reachable_bot, eq_comm]

-- A nonempty truncation set in the other connected component leaves the actual
-- positive spectral-filter term intact, rather than replacing it by zero.
example (h : LocalHamiltonian domain 2 0 1) (Ω : StateSpace domain 2) (Δ : ℝ) :
    (scan {leftSite}).truncatedEnergyTerm h Ω Δ 0 rightLabel =
      h.positiveTerm Δ Ω rightLabel := by
  have hne : rightSite ≠ leftSite := by
    intro he
    have := congrArg Subtype.val he
    norm_num [rightSite, leftSite] at this
  unfold CollarScan.truncatedEnergyTerm
  rw [right_anchor]
  simp [truncatedConstraint, scan, CollarScan.truncationSet, setDist, graph_eq_bot,
    SimpleGraph.edist_bot_of_ne hne]

example (h : LocalHamiltonian domain 2 0 1) (Ω : StateSpace domain 2) (Δ : ℝ)
    (i : AdmissibleSupport domain 0) :
    (scan ∅).truncatedEnergyTerm h Ω Δ 0 i = h.positiveTerm Δ Ω i := by
  simp [CollarScan.truncatedEnergyTerm, truncatedConstraint, scan,
    CollarScan.truncationSet, setDist]

example (h : LocalHamiltonian domain 1 0 1) (Ω : StateSpace domain 1)
    (hΩ : ‖Ω‖ = 1) (A : Finset (Site domain)) :
    (∀ i, 0 ≤ ((scan A).actualEnergyTerms h Ω 1 0 aux).term i) ∧
    (∀ i, ((scan A).actualEnergyTerms h Ω 1 0 aux).term i ≤ 1) ∧
    (∀ i, IsSupportedOn (((scan A).actualEnergyTerms h Ω 1 0 aux).term i)
      (((scan A).actualEnergyTerms h Ω 1 0 aux).support i)) :=
  (scan A).actualEnergyTerms_spec h Ω rfl (anchor_mem A) (by norm_num) hΩ 0 aux

example (h : LocalHamiltonian domain 2 0 1) (Ω : StateSpace domain 2) (Δ : ℝ) (k : ℕ) :
    ((scan ∅).actualEnergyTerms h Ω Δ 0 aux).replicaEnergy k =
      copyMean (augmentedDimensions 2 aux) k
        (augmentOperator 2 aux (∑ i, h.positiveTerm Δ Ω i)) := by
  rw [CollarScan.replicaEnergy_actualEnergyTerms]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp [CollarScan.truncatedEnergyTerm, truncatedConstraint, scan,
    CollarScan.truncationSet, setDist]

private def pathDomain : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0), (4, 0)}
private def p0 : Site pathDomain := ⟨(0, 0), by simp [pathDomain]⟩
private def p1 : Site pathDomain := ⟨(1, 0), by simp [pathDomain]⟩
private def p2 : Site pathDomain := ⟨(2, 0), by simp [pathDomain]⟩
private def p4 : Site pathDomain := ⟨(4, 0), by simp [pathDomain]⟩

private def pathScan (A : Finset (Site pathDomain)) :
    CollarScan (Site pathDomain) (AdmissibleSupport pathDomain 0) where
  graph := domainGraph pathDomain
  A := A
  depth _ := 0
  anchor i := i.property.1.choose
  n := 1
  m := 1
  K := 1
  D := 1
  r₀ := 0
  C₁ := 1

private def originLabel : AdmissibleSupport pathDomain 0 :=
  ⟨{p0}, isAdmissibleSupport_singleton pathDomain 0 p0⟩

private theorem origin_anchor (A : Finset (Site pathDomain)) :
    (pathScan A).anchor originLabel = p0 := by
  have hm : (pathScan A).anchor originLabel ∈ originLabel.val :=
    originLabel.property.1.choose_spec
  simpa only [originLabel, Finset.mem_singleton] using hm

private theorem path_adjacent : (domainGraph pathDomain).Adj p0 p1 := by
  norm_num [domainGraph, p0, p1]

private theorem island_distance : (domainGraph pathDomain).edist p0 p4 = ⊤ := by
  apply SimpleGraph.edist_eq_top_of_not_reachable
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (by decide : p0 ≠ p4)
  ext x
  change (domainGraph pathDomain).Adj p4 x ↔ False
  have hx := x.property
  simp only [pathDomain, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> norm_num [domainGraph, p4, hx]

-- A retained component has three sites. Its non-anchor neighbor remains in the
-- actual support even though the base-radius-zero ball is only the anchor.
example (h : LocalHamiltonian pathDomain 2 0 1) (Ω : StateSpace pathDomain 2) (Δ : ℝ) :
    Sum.inl p1 ∈ ((pathScan {p4}).actualEnergyTerms h Ω Δ 0 aux).support originLabel := by
  change Sum.inl p1 ∈ physicalRegion (designatedSupport (pathScan {p4}).graph
    ((pathScan {p4}).truncationSet 0) (pathScan {p4}).r₀
    ((pathScan {p4}).anchor originLabel))
  rw [origin_anchor]
  apply Finset.mem_map.mpr
  refine ⟨p1, ?_, rfl⟩
  simpa [designatedSupport, pathScan, CollarScan.truncationSet, setDist,
    island_distance, componentFinset] using path_adjacent.reachable

example : p1 ∉ QuantumCircuit.graphBall (domainGraph pathDomain) p0 0 := by
  simp [QuantumCircuit.graphBall, p0, p1]

private theorem path_distance_two : (domainGraph pathDomain).edist p0 p2 = 2 := by
  have h12 : (domainGraph pathDomain).Adj p1 p2 := by norm_num [domainGraph, p1, p2]
  have hle : (domainGraph pathDomain).edist p0 p2 ≤ (2 : ℕ∞) := by
    calc (domainGraph pathDomain).edist p0 p2 ≤
        (domainGraph pathDomain).edist p0 p1 + (domainGraph pathDomain).edist p1 p2 :=
      (domainGraph pathDomain).edist_triangle
      _ = 2 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr path_adjacent,
        SimpleGraph.edist_eq_one_iff_adj.mpr h12]; norm_num
  have hnot : ¬ (domainGraph pathDomain).edist p0 p2 ≤ (1 : ℕ∞) := by
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    norm_num [domainGraph, p0, p2]
  have hfinite : (domainGraph pathDomain).edist p0 p2 ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hle
  have hcast := ENat.natCast_toNat hfinite
  have hnle := ENat.toNat_le_of_le_natCast hle
  have hnnot : ¬ ((domainGraph pathDomain).edist p0 p2).toNat ≤ 1 := by
    intro hn
    apply hnot
    rw [← hcast]
    exact_mod_cast hn
  have hn : ((domainGraph pathDomain).edist p0 p2).toNat = 2 := by omega
  rw [← hcast, hn]
  rfl

-- Finite distance two gives radius one, strictly above the base radius zero.
example (h : LocalHamiltonian pathDomain 2 0 1) (Ω : StateSpace pathDomain 2) (Δ : ℝ) :
    Sum.inl p1 ∈ ((pathScan {p2}).actualEnergyTerms h Ω Δ 0 aux).support originLabel := by
  change Sum.inl p1 ∈ physicalRegion (designatedSupport (pathScan {p2}).graph
    ((pathScan {p2}).truncationSet 0) (pathScan {p2}).r₀
    ((pathScan {p2}).anchor originLabel))
  rw [origin_anchor]
  apply Finset.mem_map.mpr
  refine ⟨p1, ?_, rfl⟩
  simpa [designatedSupport, pathScan, CollarScan.truncationSet, setDist,
    path_distance_two, truncationRadius, QuantumCircuit.graphBall] using
    (SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (Or.inl path_adjacent))

-- The exact support field supplies both existing transport compatibility seams.
example {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
    [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x => ambientDepth T hT x.val) {k L : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) (aux : Bool → ℕ) :
    (S.fillTransportData histTree).SupportCompatible (S.actualEnergyTerms h Ω Δ L aux) ∧
    (S.chargeTransportData histTree choiceTree).SupportCompatible
      (S.actualEnergyTerms h Ω Δ L aux) := by
  exact ⟨S.fillTransportData_supportCompatible_domainGraph hT hgraph hdepth histTree
    hn hk hr hDpos hD hL hrows hclear _ _ (fun _ => rfl),
    S.chargeTransportData_supportCompatible_domainGraph hT hgraph hdepth histTree choiceTree
      hn hk hr hDpos hD hL hrows hclear _ _ (fun _ => rfl)⟩

end TNLeanTest.ActualEnergyTerms
