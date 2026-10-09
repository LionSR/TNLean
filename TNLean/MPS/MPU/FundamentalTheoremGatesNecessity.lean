import TNLean.MPS.MPU.FundamentalTheoremLetters
import TNLean.MPS.MPU.SelectedSourceGateVirtualGauge

/-!
# The fundamental theorem of matrix product unitaries: gates, necessity

Two simple tensors in canonical form II with the same periodic operators at every length at
least two have gates related by unitaries on the two internal legs. The letter-level theorem
supplies the bond unitary `z`; the selected-factor and selected-gate comparison theorems, stated
for the sandwich `z U z†`, are transported along the equality `V = z U z†`.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), relation (35a) and
the contraction of the half-factor relations (35b). Milestone M-A, Theorem A2.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

/-- Equal operators at every length at least two express `V` as the unitary sandwich of `U`. -/
theorem IsMPUCanonicalFormII.eq_virtualSandwich_of_mpo_eq
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ z : Matrix.unitaryGroup (Fin D) ℂ,
      V = virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ)) := by
  obtain ⟨hdim, z, hz⟩ := (hU.mpo_eq_iff_exists_unitary_conj hV).mp hEq
  refine ⟨z, ?_⟩
  funext i j
  rw [hz i j]
  rfl

/-- **Fundamental theorem, gates, necessity.** Simple tensors in canonical form II with equal
periodic operators at every length at least two have the same source ranks and gates related by
unitaries `x` on the left rank and `y` on the right rank:
`u_V = (x ⊗ y) u_U` and `v_V = v_U (y† ⊗ x†)`, with the gates of the fixed factorizations.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648): the first relation
is (35a); the second is the contraction of the two half-factor relations (35b) over the bond,
not (35b) itself. The half-factor relations themselves are
`IsMPUCanonicalFormII.exists_selected_source_factor_unitary_gauges` applied to the unitary `z`
of `eq_virtualSandwich_of_mpo_eq`. Simplicity of both tensors is assumed because the gate
comparison theorem is stated for simple tensors; the mathematical argument does not need it. -/
theorem IsMPUCanonicalFormII.exists_source_gate_unitary_gauges_of_mpo_eq
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
      (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      sourceU V hV.ρ hV.ρ_posDef =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef) ∧
      sourceV V hV.ρ hV.ρ_posDef =
        Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (sourceV U hU.ρ hU.ρ_posDef) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  obtain ⟨z, rfl⟩ := hU.eq_virtualSandwich_of_mpo_eq hV hEq
  obtain ⟨x, y, hu, hv⟩ := hU.exists_selected_source_gate_unitary_gauges hSU z hV hSV
  exact ⟨_, _, x, y, hu, hv⟩

end MPOTensor
