/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPortIO
import TNLean.Circuit.Channel.PhysicalPortPureOutput

/-!
# Pure-state conversions on the original physical ports

A dimension-bounded native channel taking a pure input to a normalized
pure output has a compiled unitary realization on the original physical ports.
The designated data and scratch registers start and end in their product zero
state. The final vector factors into that encoded output and a derived
normalized environment vector, at intersite depth `2 * Nat.clog d B * T`.

**Scope restriction (bounded exact pure-state conversion):** the intermediate
local dimension bound is explicit; for a family it must be fixed before the
chain length. The final dilation environment need not reset or factor over
sites. This theorem does not supply the source's adaptive block/control rules.
See `docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.

Source: Piroli, Styliaris and Cirac, arXiv:2103.13367v3, main-text paragraphs
"Quantum circuits and LOCC" and "State transformations with QC and LOCC",
HTML lines 45–53: product ancillary initialization, free onsite unitaries,
and the final local measurements. This is the exact pure-output consequence
of the bounded channel compiler, rather than an unrestricted phase statement.
-/

noncomputable section

open Matrix

namespace QuantumCircuit

variable {B d N T : ℕ} [NeZero d] [NeZero N]

/-- Compile a bounded native pure-state conversion with its original-port
input and output and product-zero designated memory. The environment vector is
derived from the compiled output; no simulator, decoupling or environment
reset premise is supplied. The full channel identity on all logical operators
is retained at physical depth `2 * Nat.clog d B * T`.

Source: arXiv:2103.13367v3, "Quantum circuits and LOCC" and "State transformations
with QC and LOCC", HTML lines 45–53. The intermediate dimension bound must be
uniform before quantifying over chain lengths in any family application. -/
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_pure_output
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (ψ φ : (Fin N → Fin d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Ψ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    let V := registerEncoding (PortRegisters.wordCodeConfiguration
      (N := N) (PortRegisters.portWordCode d k))
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : (Fin A → Fin d) → ℂ,
          IsPhysicalPortUnitary ((PortRegisters.layout N k).append owner) (2 * k * T) U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d ∘ₗ
            PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
              PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ ∧
          star η ⬝ᵥ η = 1 ∧ ∀ x e,
            ((appendMatrixSplit W A d U) *ᵥ
              (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ (V *ᵥ ψ))) (x, e) =
                (V *ᵥ φ) x * η e := by
  dsimp only
  let k := Nat.clog d B
  let V := registerEncoding (PortRegisters.wordCodeConfiguration
    (N := N) (PortRegisters.portWordCode d k))
  have hV : Vᴴ * V = 1 := registerEncoding_isIsometry _
  have hφV : star (V *ᵥ φ) ⬝ᵥ (V *ᵥ φ) = 1 := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hV, one_mulVec, hφ]
  have hPure (ξ : (Fin N → Fin d) → ℂ) :
      PortRegisters.wordInitialization (PortRegisters.portWordCode d k)
        (vecMulVec ξ (star ξ)) = vecMulVec (V *ᵥ ξ) (star (V *ᵥ ξ)) := by
    change V * vecMulVec ξ (star ξ) * Vᴴ = _
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec]
  obtain ⟨Γ, hΓ, hports⟩ := h.exists_physicalPortIO hd hN
  have hΓOutput : Γ (vecMulVec (V *ᵥ ψ) (star (V *ᵥ ψ))) =
      vecMulVec (V *ᵥ φ) (star (V *ᵥ φ)) := by
    calc
      _ = Γ (PortRegisters.wordInitialization (PortRegisters.portWordCode d k)
          (vecMulVec ψ (star ψ))) := congrArg Γ (hPure ψ).symm
      _ = PortRegisters.wordInitialization (PortRegisters.portWordCode d k)
          (Ψ (vecMulVec ψ (star ψ))) := LinearMap.congr_fun hports _
      _ = vecMulVec (V *ᵥ φ) (star (V *ᵥ φ)) := by rw [hOutput, hPure]
  obtain ⟨A, owner, U, η, hU, hDilation, hη, hfactor⟩ :=
    hΓ.exists_appended_unitary_dilation_pure_output (V *ᵥ ψ) (V *ᵥ φ) hφV hΓOutput
  refine ⟨A, owner, U, η, hU, ?_, hη, hfactor⟩
  exact (congrArg (fun Φ ↦ Φ ∘ₗ
    PortRegisters.wordInitialization (PortRegisters.portWordCode d k)) hDilation).trans hports

end QuantumCircuit
