/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.Circuit.SparseRegisterPadding
import QICLean.Circuit.Model.Measurement

/-!
# Constant-depth coherent GHZ preparation on sparse registers

The registers occupy the final `r` physical sites of arbitrary cyclic blocks of length at
least `3r`. Their first `r` sites are measurement ancillas. The remaining sites supply the
teleportation scratch space, all of which is restored exactly. A one-site parity padding
rotation accommodates every combination of even and odd block lengths.

The quantum depth depends only on `d` and `r`, never on block lengths or their number.
Measurements, on-site corrections, and global classical feedforward are free in the measurement
circuit model. All outcomes are retained, and the final correction has a scalar
independent of the coherent label amplitudes. This realizes the constant-depth GHZ seed in
arXiv:2307.01696, paragraph "Long-range MPS using measurements".

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
* arXiv:2103.13367, Example 1.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators

namespace MPSPreparation

variable {d M N r : ℕ} {ℓ : Fin M → ℕ}

/-- A unitary circuit is a measurement circuit implementing its operator on every vector. -/
private theorem exists_circuit_of_isUnitaryCircuit [NeZero N] {K : ℕ}
    {W : Matrix (Cfg d N) (Cfg d N) ℂ} (hW : IsUnitaryCircuit (Geometry.ring N) K W) :
    ∃ c : Circuit (Geometry.ring N) KrausGate (ManyBody.Qudits (Fin N) d)
        (ManyBody.Qudits (Fin N) d),
      c.Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement ∧ c.depth ≤ K ∧
        c.IsImplementationOn KrausGate.ev Set.univ W := by
  obtain ⟨u, hud, huop⟩ := hW
  refine ⟨u.toCircuit, u.forall_isUnitary.mono fun _ hK ↦ Or.inl hK, hud, ?_⟩
  rw [← huop]
  exact u.isImplementationOn _

/-- The physical scratch sites strictly between a block's first and last registers. -/
noncomputable def windowCentralSites (hN : ∑ k, ℓ k = N) (r : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun i ↦
    ∃ (k : Fin M) (p : Fin (ℓ k)), r ≤ p.val ∧ p.val < ℓ k - r ∧ i = blockSite hN k p

theorem mem_windowCentralSites {hN : ∑ k, ℓ k = N} {r : ℕ} {i : Fin N} :
    i ∈ windowCentralSites hN r ↔
      ∃ (k : Fin M) (p : Fin (ℓ k)), r ≤ p.val ∧ p.val < ℓ k - r ∧ i = blockSite hN k p := by
  classical
  simp [windowCentralSites]

/-- The distant controlled-subtraction layer has a constant-depth measurement implementation
on every coherent state whose central physical scratch sites carry zero. Odd gaps are handled
by constant-size padding rotations; every scratch site is restored by the exact operator
identity. On each branch the scalar does not depend on the input. -/
theorem exists_rounds_sparseBlockShift [NeZero d] (hr : 2 ≤ r) :
    ∃ C : ℕ, ∀ {M N : ℕ} [NeZero N] {ℓ : Fin M → ℕ}
      (hN : ∑ k, ℓ k = N) (hℓ : ∀ k, 3 * r ≤ ℓ k),
      ∃ c : Circuit (Geometry.ring N) KrausGate (ManyBody.Qudits (Fin N) d)
          (ManyBody.Qudits (Fin N) d),
        c.Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement ∧ c.depth ≤ C ∧
        c.IsImplementationOn KrausGate.ev {v | IsZeroOn (d := d) (windowCentralSites hN r) v}
          (blockLayerOp hN (fun k => ManyBody.placeAlong (X := fun _ ↦ Fin d)
            ⟨SparseRegister.ends (by have := hℓ k; omega), SparseRegister.ends_injective _⟩
            ((tailShift r).permMatrix ℂ))) ∧
        ∀ p : c.Index, ∃ z : ℂ,
          ∀ v : Cfg d N → ℂ, IsZeroOn (windowCentralSites hN r) v →
            c.kraus KrausGate.ev p *ᵥ v = z •
              (blockLayerOp hN (fun k => ManyBody.placeAlong (X := fun _ ↦ Fin d)
                ⟨SparseRegister.ends (by have := hℓ k; omega), SparseRegister.ends_injective _⟩
                ((tailShift r).permMatrix ℂ)) *ᵥ v) := by
  classical
  obtain ⟨KP, hKP⟩ := SparseRegister.exists_isUnitaryCircuitOn_paddingAll (d := d) (r := r)
  have : NeZero (r + r) := ⟨by omega⟩
  obtain ⟨KX, hKX⟩ : ∃ KX, ∀ X : Matrix (Cfg d (r + r)) (Cfg d (r + r)) ℂ,
      X ∈ unitary (Matrix (Cfg d (r + r)) (Cfg d (r + r)) ℂ) →
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (r + r))) KX X :=
    ⟨_, fun X hX ↦ isGateProduct_pathGraph_unitaryGateCount hX⟩
  refine ⟨2 * KP + 4 * r + KX, fun {M N} _ {ℓ} hN hℓ => ?_⟩
  have : NeZero r := ⟨by omega⟩
  let hp : ∀ k, r + 1 ≤ ℓ k := fun k => by have := hℓ k; omega
  let π := SparseRegister.paddingAll hN hp
  let gs := List.ofFn (SparseRegister.gate (d := d) hN hr hℓ)
  obtain ⟨cP, hPf, hPd, hP⟩ := exists_circuit_of_isUnitaryCircuit (hKP hN hp).1.isUnitaryCircuit
  obtain ⟨cQ, hQf, hQd, hQ⟩ := exists_circuit_of_isUnitaryCircuit (hKP hN hp).2.isUnitaryCircuit
  obtain ⟨cG, hGf, hGd, hG⟩ := RegisterGate.exists_rounds
    (SparseRegister.pairwise_gates (d := d) hN hr hℓ) (K := KX) (by
      intro g hg
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
      exact hKX _ (Equiv.Perm.permMatrix_mem_unitaryGroup _))
  have hmap : ∀ v ∈ (Set.univ : Set (Cfg d N → ℂ)) ∩
      {v | IsZeroOn (d := d) (windowCentralSites hN r) v},
      ManyBody.sitePermOp π *ᵥ v ∈ {v | ∀ g ∈ gs, IsZeroOn g.interior v} := by
    rintro v ⟨-, hv⟩ g hg x hx i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    obtain ⟨⟨p, hp₁, hp₂, hi'⟩, hfix⟩ := SparseRegister.gate_interior hN hr hℓ k hi
    rw [ManyBody.sitePermOp_mulVec] at hx
    have h := hv (x ∘ π) hx i (mem_windowCentralSites.mpr ⟨k, p, hp₁, hp₂, hi'⟩)
    change x (π i) = 0 at h
    have hfix' : π i = i := hfix
    rwa [hfix'] at h
  have hPQ := ((hP.mono Set.inter_subset_left).comp hG hmap).comp hQ
    (fun _ _ => Set.mem_univ _)
  have heq := SparseRegister.padding_conj_gates (d := d) hN hr hℓ
  rw [Matrix.mul_assoc] at heq
  have hImpl : ((cP.comp cG).comp cQ).IsImplementationOn KrausGate.ev
      {v | IsZeroOn (d := d) (windowCentralSites hN r) v}
      (blockLayerOp hN (fun k => ManyBody.placeAlong (X := fun _ ↦ Fin d)
        ⟨SparseRegister.ends (by have := hℓ k; omega), SparseRegister.ends_injective _⟩
        ((tailShift r).permMatrix ℂ))) := by
    rw [← heq]
    exact hPQ.mono fun v hv => ⟨Set.mem_univ v, hv⟩
  have hWu : blockLayerOp hN (fun k => ManyBody.placeAlong (X := fun _ ↦ Fin d)
      ⟨SparseRegister.ends (by have := hℓ k; omega), SparseRegister.ends_injective _⟩
      ((tailShift r).permMatrix ℂ)) ∈ Matrix.unitaryGroup (Cfg d N) ℂ := by
    unfold blockLayerOp
    refine Finset.noncommProd_induction _ _ _ (fun X => X ∈ Matrix.unitaryGroup _ ℂ) ?_ ?_ ?_
    · exact fun _ _ ha hb => Submonoid.mul_mem _ ha hb
    · exact Submonoid.one_mem _
    · intro k _
      exact ManyBody.placeAlong_mem_unitaryGroup _ (ManyBody.placeAlong_mem_unitaryGroup _
        (Equiv.Perm.permMatrix_mem_unitaryGroup _))
  refine ⟨(cP.comp cG).comp cQ, (hPf.comp _ hGf).comp _ hQf, ?_, hImpl, fun p => ?_⟩
  · have h1 := Circuit.depth_comp (cP.comp cG) cQ
    have h2 := Circuit.depth_comp cP cG
    omega
  · obtain ⟨z, hz⟩ := hImpl.exists_smul_of_isometry
      (E := zeroOnSubmodule (windowCentralSites hN r)) (Matrix.mem_unitaryGroup_iff'.mp hWu) p
    exact ⟨z, fun v hv => hz v hv⟩

private theorem windowGHZInitial_ne_zero [NeZero d] [NeZero M]
    (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k) :
    (fun σ : Cfg d N ↦ ∏ i, windowGHZInitial (d := d) hN hr i (σ i)) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 fun _ => 0
  have h2 : ∏ i, windowGHZInitial (d := d) hN hr i ((fun _ => (0 : Fin d)) i) = 1 :=
    Finset.prod_eq_one fun i _ => by unfold windowGHZInitial; split_ifs <;> simp
  exact one_ne_zero (h2.symm.trans h1)

private theorem seed_copy_isZeroOn [NeZero d] [NeZero M]
    (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k)
    (S : Matrix (Cfg d r) (Cfg d r) ℂ) :
    IsZeroOn (d := d) (windowCentralSites hN r)
      ((pairLayerOp hN hr (fun _ => (copyShift r).permMatrix ℂ) *
        ManyBody.placeAlong (X := fun _ ↦ Fin d)
          ⟨registerSite hN hr 0, registerSite_injective hN hr 0⟩ S) *ᵥ
        fun σ ↦ ∏ i, windowGHZInitial (d := d) hN hr i (σ i)) := by
  classical
  have hoff : ∀ i ∈ windowCentralSites hN r, ∀ k j, pairSite hN hr k j ≠ i := by
    intro i hi k' j h
    obtain ⟨k, p, hp₁, hp₂, rfl⟩ := mem_windowCentralSites.mp hi
    have := (blockSite_mem_pairSite hN hr k p).mp ⟨k', j, h⟩
    omega
  have hi : IsZeroOn (d := d) (windowCentralSites hN r)
      (fun σ ↦ ∏ i, windowGHZInitial (d := d) hN hr i (σ i)) := by
    intro x hx i hi
    have hn : ¬∃ k j, k ≠ 0 ∧ registerSite hN hr k j = i := by
      rintro ⟨k, j, -, h⟩
      exact hoff i hi k (Fin.castAdd r j) h
    have hx' : windowGHZInitial (d := d) hN hr i (x i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
    unfold windowGHZInitial at hx'
    rw [ite_eq_right hn] at hx'
    simpa [Pi.single_apply] using hx'
  have hS : IsZeroOn (d := d) (windowCentralSites hN r)
      (ManyBody.placeAlong (X := fun _ ↦ Fin d)
          ⟨registerSite hN hr 0, registerSite_injective hN hr 0⟩ S *ᵥ
        fun σ ↦ ∏ i, windowGHZInitial (d := d) hN hr i (σ i)) := by
    refine hi.mulVec_of_mem_supportedOperators
      (T := Finset.univ.map ⟨registerSite hN hr 0, registerSite_injective hN hr 0⟩) ?_
      (ManyBody.placeAlong_mem_supportedOperators (X := fun _ : Fin N ↦ Fin d)
        ⟨registerSite hN hr 0, registerSite_injective hN hr 0⟩ S)
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hi'
    exact hoff i hi 0 (Fin.castAdd r j) hj
  rw [← mulVec_mulVec, pairLayerOp_mulVec_eq_comp hN hr
    (fun _ _ => Matrix.permMatrix_mulVec (copyShift r))]
  intro x hx i hi
  have h := hS _ hx i hi
  rw [layerCfg_apply_of_forall_ne _ (hoff i hi)] at h
  exact h

/-- **Constant-depth coherent GHZ preparation on sparse physical registers.** For fixed local
dimension and fixed register width `r ≥ 2`, the depth bound is independent of all block lengths
and their number. Every cyclic partition with block widths at least `3r` is allowed, including
one block and arbitrary parity patterns. Every physical site outside the specified final
registers is restored to zero, with no postselection or unrecorded ancillas. -/
theorem exists_isMeasurementConversion_windowGHZState [NeZero d] (hr₁ : 2 ≤ r) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k), (∀ k, 3 * r ≤ ℓ k) →
      ∀ α : Cfg d r → ℂ, ∑ u, star (α u) * α u = 1 →
        ∃ v : Fin N → Fin d → ℂ, IsMeasurementConversion (Geometry.ring N) C
          (fun σ ↦ ∏ i, v i (σ i)) (windowGHZState hN hr α) := by
  classical
  have : NeZero r := ⟨by omega⟩
  have : NeZero (r + r) := ⟨by omega⟩
  obtain ⟨KS, hKS⟩ : ∃ KS, ∀ X : Matrix (Cfg d r) (Cfg d r) ℂ,
      X ∈ unitary (Matrix (Cfg d r) (Cfg d r) ℂ) →
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph r)) KS X :=
    ⟨_, fun X hX ↦ isGateProduct_pathGraph_unitaryGateCount hX⟩
  obtain ⟨KA, hKA⟩ : ∃ KA, ∀ X : Matrix (Cfg d (r + r)) (Cfg d (r + r)) ℂ,
      X ∈ unitary (Matrix (Cfg d (r + r)) (Cfg d (r + r)) ℂ) →
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (r + r))) KA X :=
    ⟨_, fun X hX ↦ isGateProduct_pathGraph_unitaryGateCount hX⟩
  obtain ⟨CB, hCB⟩ := exists_rounds_sparseBlockShift (d := d) hr₁
  refine ⟨KS + KA + CB, fun {M} _ ℓ {N} _ hN hr hℓ α hα => ?_⟩
  obtain ⟨S, hSu, hS⟩ := exists_windowGHZSeedUnitary α hα
  have hseed : IsUnitaryCircuitOn (Geometry.ring N) Finset.univ KS
      (ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d)
        ⟨registerSite hN hr 0, registerSite_injective hN hr 0⟩ S) :=
    (IsGateProduct.isUnitaryCircuitOn_ring
      (ManyBody.windowEquiv ⟨registerSite hN hr 0, registerSite_injective hN hr 0⟩)
      (fun i j h => by
        change registerSite hN hr 0 j = registerSite hN hr 0 i + 1
        rw [registerSite_eq, registerSite_eq]
        exact blockSite_succ hN 0 _ _ (by simp; omega)) (hKS S hSu)).mono_set
      (Finset.subset_univ _)
  have hcopy := isUnitaryCircuitOn_pairLayerOp hN hr fun _ =>
    hKA _ (Equiv.Perm.permMatrix_mem_unitaryGroup (copyShift r))
  obtain ⟨cA, hAf, hAd, hA⟩ := exists_circuit_of_isUnitaryCircuit (hcopy.mul hseed).isUnitaryCircuit
  obtain ⟨cB, hBf, hBd, hB, -⟩ := hCB hN hℓ
  set φ : Cfg d N → ℂ := fun σ ↦ ∏ i, windowGHZInitial (d := d) hN hr i (σ i) with hφ
  have hAB := (hA.mono (Set.subset_univ {φ})).comp hB (by
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact seed_copy_isZeroOn hN hr S)
  have hdiff : (blockLayerOp hN (fun k => ManyBody.placeAlong (X := fun _ ↦ Fin d)
        ⟨SparseRegister.ends (by have := hℓ k; omega), SparseRegister.ends_injective _⟩
        ((tailShift r).permMatrix ℂ)) *
      (pairLayerOp hN hr (fun _ => (copyShift r).permMatrix ℂ) *
        ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d)
          ⟨registerSite hN hr 0, registerSite_injective hN hr 0⟩ S)) *ᵥ φ =
      windowGHZDifference hN hr α := by
    rw [← Matrix.mul_assoc]
    exact windowGHZDifference_eq_mulVec hN hr α S hS _
      (fun k => SparseRegister.ends_shift_mulVec (by have := hℓ k; omega))
  have h₁ : IsMeasurementConversion (Geometry.ring N) (KA + KS + CB) φ
      (windowGHZDifference hN hr α) := by
    rw [← hdiff]
    exact hAB.isMeasurementConversion (hAf.comp _ hBf)
      ((Circuit.depth_comp _ _).trans (Nat.add_le_add hAd hBd))
      (windowGHZInitial_ne_zero hN hr) (Set.mem_singleton φ)
  obtain ⟨D, V, hV, hR⟩ := exists_windowGHZCorrectionRound (d := d) hN hr
  have h₂ : IsMeasurementConversion (Geometry.ring N) 0 (windowGHZDifference hN hr α)
      (windowGHZState hN hr α) := by
    refine ⟨h₁.ne_zero, Circuit.measureCorrect D V, Circuit.forall_measureCorrect D hV,
      (Circuit.depth_measureCorrect D V).le, fun p => ?_⟩
    obtain ⟨c, hc⟩ := hR (Layer.measure.outcome p.1)
    exact ⟨c, by rw [Circuit.kraus_measureCorrect]; exact hc α⟩
  exact ⟨windowGHZInitial hN hr, (h₁.trans h₂).mono (by omega)⟩

end MPSPreparation
