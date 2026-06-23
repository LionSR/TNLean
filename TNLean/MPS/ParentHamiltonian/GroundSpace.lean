import TNLean.MPS.Defs
import TNLean.MPS.Overlap.Basic

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Pi

/-!
# Ground space for parent Hamiltonians

For a tensor \(A\) and block length \(L\), the local ground space is
\(G_L(A) = \operatorname{range} Γ_L\), where
\(X ↦ (σ ↦ \operatorname{tr}(A^σ X))\).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The local Hilbert space on \(N\) sites, written in the computational basis as
functions on configurations `σ : Fin N → Fin d`. -/
abbrev NSiteSpace (d N : ℕ) := Cfg d N → ℂ

/-- The boundary-condition parametrization \(Γ_L\); its image is the local MPS
ground space. -/
noncomputable def groundSpaceMap (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] NSiteSpace d L :=
  LinearMap.pi fun σ : Fin L → Fin d =>
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ (evalWord A (List.ofFn σ)))

@[simp] lemma groundSpaceMap_apply (A : MPSTensor d D) (L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (σ : Fin L → Fin d) :
    groundSpaceMap A L X σ = Matrix.trace (evalWord A (List.ofFn σ) * X) := by
  simp [groundSpaceMap, Matrix.traceLinearMap_apply]

/-- Ground space on \(L\) consecutive sites:
\(G_L(A) = \operatorname{range} Γ_L\). -/
noncomputable def groundSpace (A : MPSTensor d D) (L : ℕ) :
    Submodule ℂ (NSiteSpace d L) :=
  (groundSpaceMap A L).range

lemma trace_gauge_boundary (X : GL (Fin D) ℂ) (E Y : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (((X : Matrix (Fin D) (Fin D) ℂ) * E *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) * Y) =
      Matrix.trace (E * (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        Y * (X : Matrix (Fin D) (Fin D) ℂ))) := by
  set Xmat : Matrix (Fin D) (Fin D) ℂ := (X : Matrix (Fin D) (Fin D) ℂ)
  set Xinv : Matrix (Fin D) (Fin D) ℂ :=
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  calc
    Matrix.trace ((Xmat * E * Xinv) * Y)
        = Matrix.trace (Xmat * E * (Xinv * Y)) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace ((Xinv * Y) * Xmat * E) := by
        simpa using Matrix.trace_mul_cycle Xmat E (Xinv * Y)
    _ = Matrix.trace (E * (Xinv * Y * Xmat)) := by
        simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm ((Xinv * Y) * Xmat) E

/-- A virtual gauge change does not change the local ground space. -/
theorem GaugeEquiv.groundSpace_le {A B : MPSTensor d D}
    (h : GaugeEquiv A B) (L : ℕ) :
    groundSpace B L ≤ groundSpace A L := by
  rcases h with ⟨X, hX⟩
  rintro ψ ⟨Y, rfl⟩
  refine ⟨((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * Y *
      (X : Matrix (Fin D) (Fin D) ℂ), ?_⟩
  ext σ
  rw [groundSpaceMap_apply, groundSpaceMap_apply]
  rw [evalWord_gauge X hX]
  exact (trace_gauge_boundary X (evalWord A (List.ofFn σ)) Y).symm

/-- Gauge-equivalent tensors have identical local ground spaces at every
length. -/
theorem GaugeEquiv.groundSpace_eq {A B : MPSTensor d D}
    (h : GaugeEquiv A B) (L : ℕ) :
    groundSpace A L = groundSpace B L := by
  apply le_antisymm
  · exact h.symm.groundSpace_le L
  · exact h.groundSpace_le L

/-- The span of the periodic MPS vectors associated to a finite family of BNT
components.

See arXiv:1606.00608, Definition 3.9, source lines 522--524. The source writes
the component vectors as \(|V^{(N)}(A_j)\rangle\), \(j=1,\ldots,g\). -/
noncomputable def bntMPSVectorSpan {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ (Set.range fun j : Fin r => (mpv (A j) : NSiteSpace d N))

lemma groundSpace_finrank_le (A : MPSTensor d D) (L : ℕ) :
    Module.finrank ℂ (groundSpace A L) ≤ D ^ 2 := by
  have hRange : Module.finrank ℂ (groundSpace A L) ≤
      Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) := by
    exact LinearMap.finrank_range_le (groundSpaceMap A L)
  have hMatrix : Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) = D ^ 2 :=
    by simp [Module.finrank_matrix, Fintype.card_fin, pow_two]
  exact hRange.trans (by simp [hMatrix])

/-- The ambient local space has dimension \(d^L\). -/
lemma nSiteSpace_finrank (d L : ℕ) :
    Module.finrank ℂ (NSiteSpace d L) = d ^ L := by
  calc
    Module.finrank ℂ (NSiteSpace d L)
        = Fintype.card (Cfg d L) := by
            simp [NSiteSpace, Module.finrank_fintype_fun_eq_card]
    _ = d ^ L := by simp

/-- If \(d^L > D^2\), then \(G_L(A)\) is a proper subspace. -/
lemma groundSpace_ne_top (A : MPSTensor d D) (L : ℕ) (hDim : d ^ L > D ^ 2) :
    groundSpace A L ≠ ⊤ := by
  intro hTop
  have hLe' : Module.finrank ℂ (groundSpace A L) ≤ D ^ 2 := groundSpace_finrank_le A L
  rw [hTop] at hLe'
  have hLe : d ^ L ≤ D ^ 2 := by simpa [nSiteSpace_finrank] using hLe'
  omega

end MPSTensor
