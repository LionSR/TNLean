/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SparseRegisterPadding
import TNLean.Circuit.Measurement.CoherentRounds
import TNLean.Circuit.Teleportation.ZeroSubspace

/-!
# Constant-depth coherent GHZ preparation on sparse registers

The registers occupy the final `r` physical sites of arbitrary cyclic blocks of length at
least `3r`. Their first `r` sites are measurement ancillas. The remaining sites supply the
teleportation scratch space, all of which is restored exactly. A one-site parity padding
rotation accommodates every combination of even and odd block lengths.

The quantum depth depends only on `d` and `r`, never on block lengths or their number.
Measurements, on-site corrections, and global classical feedforward are free in the existing
measurement-round model. All outcomes are retained, and the final correction has a scalar
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

private theorem exists_rounds_of_isCircuitOn [NeZero d] [NeZero N] {K : ℕ}
    {W : Matrix (Cfg d N) (Cfg d N) ℂ} (hW : IsCircuitOn Set.univ K W) :
    ∃ Rs : List (MeasurementRound d N), (Rs.map MeasurementRound.depth).sum = K + 2 ∧
      MeasurementRound.IsRoundsImplementationOn Rs Set.univ W := by
  obtain ⟨Ls, hlen, -, hLs⟩ := hW
  let R := TeleportHop.round Ls [] TeleportHop.valid_nil
  refine ⟨[R], ?_, ?_⟩
  · simp [R, MeasurementRound.depth, TeleportHop.round, hlen]
  · have h := (TeleportHop.isImplementationOn_round (d := d) Ls
      (TeleportHop.valid_nil (N := N))).isRoundsImplementationOn
    rw [TeleportHop.chainPerm_nil, Matrix.one_mul, ← hLs] at h
    exact h.mono fun _ _ => fun _ _ _ hi => hi.elim

/-- The physical scratch sites strictly between a block's first and last registers. -/
def windowCentralSites (hN : ∑ k, ℓ k = N) (r : ℕ) : Set (Fin N) :=
  {i | ∃ (k : Fin M) (p : Fin (ℓ k)), r ≤ p.val ∧ p.val < ℓ k - r ∧ i = blockSite hN k p}

/-- The distant controlled-subtraction layer has a constant-depth measurement implementation
on every coherent state whose central physical scratch sites carry zero. Odd gaps are handled
by constant-size padding rotations; every scratch site is restored by the exact operator
identity. -/
theorem exists_rounds_sparseBlockShift [NeZero d] (hr : 2 ≤ r) :
    ∃ C : ℕ, ∀ {M N : ℕ} [NeZero N] {ℓ : Fin M → ℕ}
      (hN : ∑ k, ℓ k = N) (hℓ : ∀ k, 3 * r ≤ ℓ k),
      ∃ Rs : List (MeasurementRound d N), (Rs.map MeasurementRound.depth).sum = C ∧
        MeasurementRound.IsRoundsImplementationOn Rs
          {v | IsZeroOn (d := d) (windowCentralSites hN r) v}
          (blockLayerOp hN (fun k => embedOp (SparseRegister.ends (by have := hℓ k; omega))
            ((tailShift r).permMatrix ℂ))) ∧
        ∀ m : MeasurementRound.OutcomeHistory Rs, ∃ c : ℂ,
          ∀ v : Cfg d N → ℂ, IsZeroOn (windowCentralSites hN r) v →
            MeasurementRound.historyKraus Rs m *ᵥ v = c •
              (blockLayerOp hN (fun k => embedOp (SparseRegister.ends (by have := hℓ k; omega))
                ((tailShift r).permMatrix ℂ)) *ᵥ v) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨KP, hKP⟩ := SparseRegister.exists_isCircuitOn_paddingAll (d := d) hd (by omega : 1 ≤ r)
  obtain ⟨KX, hKX⟩ := exists_isPairProduct (d := d) (n := r + r) hd (by omega)
  refine ⟨2 * KP + 4 * r + KX + 6, fun {M N} _ {ℓ} hN hℓ => ?_⟩
  let : NeZero r := ⟨by omega⟩
  let hp : ∀ k, r + 1 ≤ ℓ k := fun k => by have := hℓ k; omega
  let π := SparseRegister.paddingAll hN hp
  let gs := List.ofFn (SparseRegister.gate (d := d) hN hr hℓ)
  obtain ⟨RsP, hRsP, hP⟩ := exists_rounds_of_isCircuitOn (hKP hN hp).1
  obtain ⟨RsQ, hRsQ, hQ⟩ := exists_rounds_of_isCircuitOn (hKP hN hp).2
  obtain ⟨RsG, hRsG, hG⟩ := RegisterGate.exists_rounds
    (SparseRegister.pairwise_gates (d := d) hN hr hℓ) (K := KX) (by
      intro g hg
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
      exact hKX _ (Equiv.Perm.permMatrix_mem_unitaryGroup _))
  have hmap : ∀ v ∈ {v | IsZeroOn (d := d) (windowCentralSites hN r) v},
      (cfgPerm π).permMatrix ℂ *ᵥ v ∈ {v | ∀ g ∈ gs, IsZeroOn g.interior v} := by
    intro v hv g hg x hx i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    obtain ⟨⟨p, hp₁, hp₂, hi'⟩, hfix⟩ := SparseRegister.gate_interior hN hr hℓ k hi
    rw [Matrix.permMatrix_mulVec] at hx
    have h := hv (cfgPerm π x) hx i ⟨k, p, hp₁, hp₂, hi'⟩
    change x (π i) = 0 at h
    simpa only [π, hfix] using h
  have hPQ := ((hP.mono (Set.subset_univ _)).append hG hmap).append hQ
    (fun _ _ => Set.mem_univ _)
  have hImpl : MeasurementRound.IsRoundsImplementationOn (RsP ++ RsG ++ RsQ)
      {v | IsZeroOn (windowCentralSites hN r) v}
      (blockLayerOp hN (fun k => embedOp (SparseRegister.ends (by have := hℓ k; omega))
        ((tailShift r).permMatrix ℂ))) := by
    have heq := SparseRegister.padding_conj_gates (d := d) hN hr hℓ
    rw [Matrix.mul_assoc] at heq
    simpa only [← List.append_assoc, heq] using hPQ
  refine ⟨RsP ++ RsG ++ RsQ, ?_, hImpl, fun m => ?_⟩
  · simp only [List.map_append, List.sum_append, hRsP, hRsG, hRsQ]
    omega
  · apply hImpl.exists_history_scalar (E := zeroOnSubmodule (windowCentralSites hN r)) _ m
    unfold blockLayerOp
    refine Finset.noncommProd_induction _ _ _ (fun X => X ∈ unitary _) ?_ ?_ ?_
    · exact fun _ _ ha hb => Submonoid.mul_mem _ ha hb
    · exact Submonoid.one_mem _
    · intro k _
      apply embedOp_mem_unitary (blockSite_injective hN k)
      exact embedOp_mem_unitary (SparseRegister.ends_injective _)
        (Equiv.Perm.permMatrix_mem_unitaryGroup _)

private theorem windowGHZInitial_ne_zero [NeZero d] [NeZero M]
    (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k) :
    productVector (windowGHZInitial (d := d) hN hr) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 fun _ => 0
  have h2 : productVector (windowGHZInitial (d := d) hN hr) (fun _ => (0 : Fin d)) = 1 :=
    Finset.prod_eq_one fun i _ => by unfold windowGHZInitial; split_ifs <;> simp
  exact one_ne_zero (h2.symm.trans h1)

private theorem seed_copy_isZeroOn [NeZero d] [NeZero M]
    (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k)
    (S : Matrix (Cfg d r) (Cfg d r) ℂ) :
    IsZeroOn (d := d) (windowCentralSites hN r)
      ((pairLayerOp hN hr (fun _ => (copyShift r).permMatrix ℂ) *
        embedOp (registerSite hN hr 0) S) *ᵥ productVector (windowGHZInitial (d := d) hN hr)) := by
  classical
  have hoff : ∀ i ∈ windowCentralSites hN r, ∀ k j, pairSite hN hr k j ≠ i := by
    rintro i ⟨k, p, hp₁, hp₂, rfl⟩ k' j h
    have := (blockSite_mem_pairSite hN hr k p).mp ⟨k', j, h⟩
    omega
  have hi : IsZeroOn (d := d) (windowCentralSites hN r)
      (productVector (windowGHZInitial (d := d) hN hr)) := by
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
      (embedOp (registerSite hN hr 0) S *ᵥ productVector (windowGHZInitial (d := d) hN hr)) := by
    refine hi.mulVec_of_mem_supportedOperators ?_
      (embedOp_mem_supportedOperators (registerSite_injective hN hr 0) S)
    rw [Set.disjoint_left]
    rintro i hi ⟨j, hj⟩
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
theorem exists_isPreparedWithMeasurementRoundsInDepth_windowGHZState [NeZero d] (hr₁ : 2 ≤ r) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k), (∀ k, 3 * r ≤ ℓ k) →
      ∀ α : Cfg d r → ℂ, ∑ u, star (α u) * α u = 1 →
        IsPreparedWithMeasurementRoundsInDepth C (windowGHZState hN hr α) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨KS, hKS⟩ := exists_isPairProduct (d := d) (n := r) hd hr₁
  obtain ⟨KA, hKA⟩ := exists_isPairProduct (d := d) (n := r + r) hd (by omega)
  obtain ⟨CB, hCB⟩ := exists_rounds_sparseBlockShift (d := d) hr₁
  refine ⟨KS + KA + 2 + CB, fun {M} _ ℓ {N} _ hN hr hℓ α hα => ?_⟩
  obtain ⟨S, hSu, hS⟩ := exists_windowGHZSeedUnitary α hα
  have hseed : IsCircuitOn Set.univ KS (embedOp (registerSite hN hr 0) S) := by
    refine ((hKS S hSu).isCircuitOn (registerSite_injective hN hr 0) fun i j h => ?_).mono_set
      (Set.subset_univ _)
    rw [registerSite_eq, registerSite_eq]
    exact blockSite_succ hN 0 _ _ (by simp; omega)
  have hcopy := isCircuitOn_pairLayerOp hN hr fun _ =>
    hKA _ (Equiv.Perm.permMatrix_mem_unitaryGroup (copyShift r))
  obtain ⟨RsA, hRsA, hA⟩ := exists_rounds_of_isCircuitOn (hseed.mul hcopy)
  obtain ⟨RsB, hRsB, hB, -⟩ := hCB hN hℓ
  let v := windowGHZInitial (d := d) hN hr
  have hAB := (hA.mono (show {productVector v} ⊆ Set.univ from Set.subset_univ _)).append hB (by
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact seed_copy_isZeroOn hN hr S)
  obtain ⟨R, hRdepth, hR⟩ := exists_windowGHZCorrectionRound (d := d) hN hr
  refine ⟨v, (RsA ++ RsB) ++ [R], ?_, windowGHZInitial_ne_zero hN hr, fun w hw _ => ?_⟩
  · simp only [List.map_append, List.sum_append, hRsA, hRsB, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hRdepth]
    omega
  obtain ⟨u, hu, hw⟩ := MeasurementRound.mem_outputs_append.mp hw
  obtain ⟨c, rfl⟩ := hAB _ rfl u hu
  obtain ⟨w', hw', rfl⟩ := MeasurementRound.mem_outputs_smul c hw
  have hdiff := windowGHZDifference_eq_mulVec hN hr α S hS
    (fun k => embedOp (SparseRegister.ends (by have := hℓ k; omega)) ((tailShift r).permMatrix ℂ))
    (fun k => SparseRegister.ends_shift_mulVec (by have := hℓ k; omega))
  rw [Matrix.mul_assoc] at hdiff
  rw [hdiff] at hw'
  obtain ⟨m, hm⟩ := R.mem_outputs_cons.mp hw'
  rw [MeasurementRound.outputs_nil, Set.mem_singleton_iff] at hm
  obtain ⟨c', hc'⟩ := hR m
  exact ⟨c * c', by rw [hm, hc' α, smul_smul]⟩

end MPSPreparation
