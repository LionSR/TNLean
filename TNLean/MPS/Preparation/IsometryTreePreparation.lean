/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Compile.ChainUniversality
import QICLean.Circuit.Model.Measurement
import QICLean.Circuit.Protocol.Teleportation.Hop
import TNLean.MPS.Preparation.UnequalRegisterTreeState

/-!
# Measurement implementation of coherent isometry trees

Binary trees with fixed-width registers and uniformly bounded physical leaves have
measurement implementations in depth proportional to their height. The virtual dimension
is arbitrary. The measurement circuit implements the same linear map on every admissible input,
with an outcome scalar independent of that input, so superpositions across canonical sectors
remain coherent. The output equality includes all physical sites, including the temporary registers.

Source: arXiv:2307.01696, eq. (16) and "Tree-RG circuit with measurements".

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit
open Kraus (blockPhysDim)

namespace MPSPreparation

/-- Trees on arbitrary disjoint blocks are implemented by measurement circuits of depth
`C (h + 1)`, where `C` depends only on the physical dimension, register width and leaf bound.
The circuit acts simultaneously on all inputs having zero at the interior scratch sites, with an
outcome scalar independent of the input.

Source: arXiv:2307.01696, "Tree-RG circuit with measurements". -/
theorem exists_rounds_blockLayerOp_treeBlockOp (d s c : ℕ) [NeZero d] [NeZero s] :
    ∃ C : ℕ, ∀ {χ : ℕ} (V : (m : ℕ) → Matrix (Cfg d m) (Fin χ) ℂ)
      (W : ℕ → ℕ → Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ)
      (h : ℕ) {M N : ℕ} [NeZero N] (ℓ : Fin M → ℕ) (hN : ∑ b, ℓ b = N)
      (w : Fin M → ℕ → ℕ) (hT : ∀ b, IsTreeLayout h s (ℓ b) (w b)),
      (∀ b (p : Fin (2 ^ (h + 1))), leafLen h (ℓ b) (w b) p ≤ c) →
      ∀ (ι₀ : Fin M → Fin χ → Cfg d (s + s)) (enc : Fin χ → Cfg d s),
      ∃ R : Circuit (Geometry.ring N) KrausGate (ManyBody.Qudits (Fin N) d)
          (ManyBody.Qudits (Fin N) d),
        R.Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement ∧ R.depth ≤ C * (h + 1) ∧
        R.IsImplementationOn KrausGate.ev {v | IsZeroOn (treeCentralSites h s hN w) v}
          (blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) ∧
        ∀ m : R.Index, ∃ a : ℂ,
          ∀ v, IsZeroOn (treeCentralSites h s hN w) v →
            R.kraus KrausGate.ev m *ᵥ v =
              a • ((blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) *ᵥ v) := by
  classical
  have hs : 1 ≤ s := NeZero.pos s
  have : NeZero (s + s) := ⟨by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, ∀ X : Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ,
      X ∈ unitary (Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) →
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (s + s))) K X :=
    ⟨_, fun X hX ↦ isGateProduct_pathGraph_unitaryGateCount hX⟩
  have hleaf : ∀ n : Fin (c + 1), ∃ K' : ℕ, 2 ≤ n.val →
      ∀ X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ),
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) K' X := fun n => by
    by_cases hn : 2 ≤ n.val
    · have : NeZero n.val := ⟨by omega⟩
      exact ⟨_, fun _ X hX ↦ isGateProduct_pathGraph_unitaryGateCount hX⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose Kl hKl using hleaf
  refine ⟨4 * s + K + ∑ n, Kl n,
    fun {χ} V W h {M N} _ ℓ hN w hT hbound ι₀ enc => ?_⟩
  set X := fun b => treeNodeGate (h := h) (n := ℓ b) (w := w b) W (ι₀ b) enc
  set U := fun b => treeLeafGate (hT b) V (ι₀ b) enc
  obtain ⟨R₁, hR₁f, hR₁d, hR₁E⟩ := exists_rounds_blockLayerOp_treeLevelsOp (hN := hN) (hT := hT)
    (X := X) (K := K) fun b j p => hK _ (treeNodeGate_mem_unitary W (ι₀ b) enc j p)
  obtain ⟨u, -, hud, huop⟩ := isUnitaryCircuitOn_blockLayerOp_treeLeafOp (hN := hN) (hT := hT) U
    (K := ∑ n, Kl n) fun b p => by
      have h1 := two_mul_le_leafLen (hT b) p.isLt
      have h2 := hbound b p
      exact (hKl ⟨_, (by omega : leafLen h (ℓ b) (w b) p < c + 1)⟩
        (by simp only; omega) _ (treeLeafGate_mem_unitary (hT b) V (ι₀ b) enc p)).mono
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  have hleafR : u.toCircuit.IsImplementationOn KrausGate.ev Set.univ
      (blockLayerOp hN fun b => treeLeafOp (hT b) (U b)) := by
    rw [← huop]
    exact Circuit.isImplementationOn_of_kraus_eq (fun p ↦ u.kraus_eq_op p) _
  have hall : (R₁.comp u.toCircuit).IsImplementationOn KrausGate.ev
      {v | IsZeroOn (treeCentralSites h s hN w) v}
      (blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) := by
    have := hR₁E.comp hleafR fun _ _ => trivial
    simpa only [← blockLayerOp_mul, treeBlockOp, X, U] using this
  have hunitary : (blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) ∈
      unitary (Matrix (Cfg d N) (Cfg d N) ℂ) := by
    rw [blockLayerOp_eq_list_prod]
    apply Submonoid.list_prod_mem
    intro Z hZ
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hZ
    exact ManyBody.placeAlong_mem_unitaryGroup _ (treeBlockOp_mem_unitary (hT b) V W (ι₀ b) enc)
  refine ⟨R₁.comp u.toCircuit, hR₁f.comp _ (u.forall_isUnitary.mono fun _ hK ↦ Or.inl hK),
    ?_, hall, ?_⟩
  · have hu : u.toCircuit.depth ≤ ∑ n, Kl n := hud
    refine (Circuit.depth_comp _ _).trans ?_
    nlinarith
  · exact fun m => hall.exists_smul_of_isometry
      (E := zeroOnSubmodule (treeCentralSites h s hN w))
      (Matrix.mem_unitaryGroup_iff'.mp hunitary) m

end MPSPreparation
