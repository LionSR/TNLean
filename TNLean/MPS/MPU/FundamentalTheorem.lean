import TNLean.MPS.MPU.FundamentalTheoremGatesNecessity
import TNLean.MPS.MPU.FundamentalTheoremGates

/-!
# The fundamental theorem of matrix product unitaries

The combined statement. For simple tensors `U, V` in canonical form II the following are
equivalent: the periodic operators agree at every length at least two; the bond dimensions agree
and the letters are unitarily conjugate. Either implies that the gates of the fixed
factorizations are related by unitaries `x, y` on the two internal legs; and gates so related
give equal periodic operators on rings of even length
(`TwoSiteStandardFormData.mpo_eq_of_gate_gauges`).

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), equation (35a) and
the contraction of (35b). The source states the theorem for the two-site standard forms; the
letter-level equivalence makes its remark that `z` is unitary into a statement, and the parity
example
(`StandardFormParityCounterexample.lean`) shows that the gate relations alone determine the
operators only on rings of even length. Milestone M-A, Theorem A4.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

/-- **Fundamental theorem of matrix product unitaries** (CPSV17 Thm III.10), for simple tensors
in canonical form II with the same bond dimension: equal periodic operators at every length at
least two are equivalent to a unitary conjugation of the letters, and imply the gate relations
`u_V = (x ⊗ y) u_U`, `v_V = v_U (y† ⊗ x†)` for unitaries `x, y` on the internal legs. -/
theorem IsMPUCanonicalFormII.fundamentalTheorem
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V) :
    ((∀ N : ℕ, 1 < N → mpo U N = mpo V N) ↔
      ∃ z : Matrix.unitaryGroup (Fin D) ℂ,
        V = virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
          (star (z : Matrix (Fin D) (Fin D) ℂ))) ∧
    ((∀ N : ℕ, 1 < N → mpo U N = mpo V N) →
      ∃ (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
        (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
        sourceU V hV.ρ hV.ρ_posDef =
          ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
            Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
              (sourceU U hU.ρ hU.ρ_posDef) ∧
        sourceV V hV.ρ hV.ρ_posDef =
          Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (sourceV U hU.ρ hU.ρ_posDef) *
            (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
              star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ))) := by
  refine ⟨⟨fun hEq => hU.eq_virtualSandwich_of_mpo_eq hV hEq, ?_⟩,
    fun hEq => hU.exists_source_gate_unitary_gauges_of_mpo_eq hSU hV hSV hEq⟩
  rintro ⟨z, rfl⟩ N _
  exact mpo_eq_of_unitary_conj rfl z (fun i j => rfl) N

end MPOTensor
