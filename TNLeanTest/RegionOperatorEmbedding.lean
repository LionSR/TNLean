/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionOperatorEmbedding

/-!
# Tests for regional operator embeddings

The empty region acts by a scalar identity; the full region has no spectator
condition. Zero physical dimension is tested with both nonempty and empty
ambient vertex sets. An asymmetric complex one-site matrix checks the order
of the two matrix indices, its phase, and the spectator identity.
-/

open TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}

-- The empty regional configuration space has one element, even when d = 0.
example (c : ℂ) :
    regionLocalTerm (d := d) (∅ : Finset V) (Matrix.of fun _ _ => c) =
      c • (1 : Matrix (V → Fin d) (V → Fin d) ℂ) := by
  classical
  rw [regionLocalTerm_eq_embedOp]
  ext σ τ
  simp [QuantumCircuit.embedOp_apply, agreeOff_region_iff, ← funext_iff,
    Matrix.one_apply, mul_ite]

-- The full region retains the entries of the original matrix.
example (H : Matrix (RegionPhysicalConfig (V := V) (d := d) Finset.univ)
    (RegionPhysicalConfig (V := V) (d := d) Finset.univ) ℂ) :
    regionLocalTerm Finset.univ H =
      H.submatrix (fullRegionConfigEquiv d) (fullRegionConfigEquiv d) := by
  classical
  rw [regionLocalTerm_eq_embedOp]
  ext σ τ
  simp [QuantumCircuit.embedOp_apply, agreeOff_region_iff, fullRegionConfigEquiv,
    Matrix.submatrix_apply, Function.comp_def]

-- Physical dimension one leaves exactly one global and one regional configuration.
example (R : Finset V)
    (H : Matrix (RegionPhysicalConfig (d := 1) R) (RegionPhysicalConfig (d := 1) R) ℂ) :
    regionLocalTerm R H = H (fun _ => 0) (fun _ => 0) •
      (1 : Matrix (V → Fin 1) (V → Fin 1) ℂ) := by
  classical
  rw [regionLocalTerm_eq_embedOp]
  ext σ τ
  have hσ : σ = fun _ => 0 := Subsingleton.elim _ _
  have hτ : τ = fun _ => 0 := Subsingleton.elim _ _
  subst σ τ
  simp [QuantumCircuit.embedOp_apply, agreeOff_region_iff, Function.comp_def]

-- With a nonempty ambient set, zero physical dimension has no configurations.
example [Nonempty V] (R : Finset V)
    (H : Matrix (RegionPhysicalConfig (d := 0) R) (RegionPhysicalConfig (d := 0) R) ℂ) :
    regionLocalTerm R H = 0 := by
  classical
  rw [regionLocalTerm_eq_embedOp]
  ext σ τ
  exact Fin.elim0 (σ (Classical.choice ‹Nonempty V›))

-- With an empty ambient set, dimension zero still has one configuration.
example :
    regionLocalTerm (d := 0) (∅ : Finset (Fin 0)) (Matrix.of fun _ _ => Complex.I)
      Fin.elim0 Fin.elim0 = Complex.I := by
  rw [regionLocalTerm_eq_embedOp, QuantumCircuit.embedOp_apply]
  simp [QuantumCircuit.agreeOff_refl]

private def complexOffDiagonal :
    Matrix (RegionPhysicalConfig (V := Fin 2) (d := 2) {0})
      (RegionPhysicalConfig (V := Fin 2) (d := 2) {0}) ℂ :=
  fun σ τ => (!![0, Complex.I; 2 + Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ)
    (σ ⟨0, by simp⟩) (τ ⟨0, by simp⟩)

-- A transpose or conjugate transpose would change this nonreal upper entry.
example : regionLocalTerm {0} complexOffDiagonal ![0, 0] ![1, 0] = Complex.I := by
  rw [regionLocalTerm_eq_embedOp]
  simp [QuantumCircuit.embedOp_apply, agreeOff_region_iff, complexOffDiagonal,
    Fin.forall_fin_two]

-- The reverse entry has a different real part as well as a nonreal phase.
example : regionLocalTerm {0} complexOffDiagonal ![1, 0] ![0, 0] = 2 + Complex.I := by
  rw [regionLocalTerm_eq_embedOp]
  simp [QuantumCircuit.embedOp_apply, agreeOff_region_iff, complexOffDiagonal,
    Fin.forall_fin_two]

-- Changing a spectator coordinate forces the entry to vanish.
example : regionLocalTerm {0} complexOffDiagonal ![0, 0] ![1, 1] = 0 := by
  rw [regionLocalTerm_eq_embedOp]
  simp [QuantumCircuit.embedOp_apply, agreeOff_region_iff, Fin.forall_fin_two]

-- The dependent lift has exactly the same complex entry after reindexing.
example :
    dependentRegionOperatorLift (Out := fun _ : Fin 2 => Fin 2) {0} complexOffDiagonal
      (fullRegionConfigEquiv 2 ![0, 0]) (fullRegionConfigEquiv 2 ![1, 0]) = Complex.I := by
  rw [dependentRegionOperatorLift_eq_reindex_embedOp]
  simp [Matrix.reindex_apply, QuantumCircuit.embedOp_apply, agreeOff_region_iff,
    complexOffDiagonal, Fin.forall_fin_two]
