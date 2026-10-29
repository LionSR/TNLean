/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.ApproximateConversion
import TNLean.Circuit.Channel.PhysicalPortDilation
import TNLean.Circuit.Channel.PhysicalPortIO
import QICLean.Channel.PureMarginalApproximation

/-!
# Approximate pure-state conversions on the original physical ports

The actual unitary compiled from a bounded native channel approximately
produces the prescribed original-port pure state tensored with a derived
unit environment vector. Full trace-norm error `ε` gives Euclidean vector
error at most `√(2 * ε)` at the same physical depth `2 * Nat.clog d B * T`.
Both input and target vectors are normalized.

**Scope restriction (bounded pure-output approximation):** a family must fix
the intermediate dimension bound before the chain length. This does not
reset the additional environment or establish adaptive protocol-block or
control conditions. See `docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.

Source context: Piroli, Styliaris and Cirac, arXiv:2103.13367v3, main-text
paragraphs "Quantum circuits and LOCC" and "Phases of matter". The latter
uses trace-norm approximation after tracing ancillary spins. The estimate
here is a derived consequence of that error criterion and the actual bounded
compiler, rather than an unrestricted source phase classification.
-/

noncomputable section

open Matrix

namespace QuantumCircuit

variable {B d N T : ℕ} [NeZero d] [NeZero N]

/-- The actual bounded compiler approximately produces the prescribed pure
state on its original ports, tensored with a derived normalized environment,
with Euclidean error at most `√(2 * ε)`. Both the input and target are unit
vectors; no joint-output or decoupling estimate is supplied as a premise.
The same unitary retains its full logical channel identity and physical depth.
Source context: arXiv:2103.13367v3, "Quantum circuits and LOCC" and
"Phases of matter", the trace-norm criterion after tracing ancillary spins. -/
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_approximate_output
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (ψ φ : (Fin N → Fin d) → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1) {ε : ℝ}
    (herror : chainTraceNorm (Ψ (vecMulVec ψ (star ψ)) - vecMulVec φ (star φ)) ≤ ε) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    let V := registerEncoding (PortRegisters.wordCodeConfiguration
      (N := N) (PortRegisters.portWordCode d k))
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : EuclideanSpace ℂ (Fin A → Fin d),
          IsPhysicalPortUnitary ((PortRegisters.layout N k).append owner) (2 * k * T) U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d ∘ₗ
            PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
              PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ ∧
          ‖η‖ = 1 ∧
          ‖(WithLp.toLp 2 (((appendMatrixSplit W A d U) *ᵥ
              (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ (V *ᵥ ψ))) -
                fun p => (V *ᵥ φ) p.1 * η p.2) :
            EuclideanSpace ℂ ((Fin W → Fin d) × (Fin A → Fin d)))‖ ≤ Real.sqrt (2 * ε) := by
  dsimp only
  let k := Nat.clog d B
  let W := N * (1 + k + k)
  let V := registerEncoding (PortRegisters.wordCodeConfiguration
    (N := N) (PortRegisters.portWordCode d k))
  have hV : Vᴴ * V = 1 := registerEncoding_isIsometry _
  have hUnit (ξ : (Fin N → Fin d) → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) :
      ‖(WithLp.toLp 2 (V *ᵥ ξ) : EuclideanSpace ℂ (Fin W → Fin d))‖ = 1 := by
    have hξV : star (V *ᵥ ξ) ⬝ᵥ (V *ᵥ ξ) = 1 := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hV, one_mulVec, hξ]
    have hs : ‖(WithLp.toLp 2 (V *ᵥ ξ) : EuclideanSpace ℂ (Fin W → Fin d))‖ ^ 2 = 1 := by
      rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp,
        dotProduct_comm, hξV, Complex.one_re]
    nlinarith [norm_nonneg (WithLp.toLp 2 (V *ᵥ ξ) : EuclideanSpace ℂ (Fin W → Fin d))]
  have hPure (ξ : (Fin N → Fin d) → ℂ) :
      PortRegisters.wordInitialization (PortRegisters.portWordCode d k)
        (vecMulVec ξ (star ξ)) = vecMulVec (V *ᵥ ξ) (star (V *ᵥ ξ)) := by
    change V * vecMulVec ξ (star ξ) * Vᴴ = _
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec]
  obtain ⟨Γ, hΓ, hports⟩ := h.exists_physicalPortIO hd hN
  obtain ⟨A, owner, U, hU, hDilation⟩ := hΓ.exists_appended_unitary_dilation
  let Ω := (appendMatrixSplit W A d U) *ᵥ
    (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ (V *ᵥ ψ))
  have hMarginal : partialTraceRight (vecMulVec Ω (star Ω)) =
      Γ (vecMulVec (V *ᵥ ψ) (star (V *ᵥ ψ))) := by
    have heq := LinearMap.congr_fun hDilation (vecMulVec (V *ᵥ ψ) (star (V *ᵥ ψ)))
    change discardAppendedEnvironment W A d
      (U * appendEnvironmentInput W A d (vecMulVec (V *ᵥ ψ) (star (V *ᵥ ψ))) * Uᴴ) = _ at heq
    rw [discardAppendedEnvironment_conj] at heq
    change partialTraceRight (appendMatrixSplit W A d U *
      (fixedEnvEmbedding (0 : Fin A → Fin d) * vecMulVec (V *ᵥ ψ) (star (V *ᵥ ψ)) *
        (fixedEnvEmbedding (0 : Fin A → Fin d))ᴴ) * (appendMatrixSplit W A d U)ᴴ) = _ at heq
    simp only [mul_vecMulVec, vecMulVec_mul, ← star_mulVec] at heq
    exact heq
  have hΩunit : ‖(WithLp.toLp 2 Ω : EuclideanSpace ℂ
      ((Fin W → Fin d) × (Fin A → Fin d)))‖ = 1 := by
    have htrace := congrArg Matrix.trace hMarginal
    rw [trace_partialTraceRight, trace_vecMulVec, hΓ.isKrausCPTP.trace_map,
      trace_vecMulVec] at htrace
    have hs : ‖(WithLp.toLp 2 Ω : EuclideanSpace ℂ
        ((Fin W → Fin d) × (Fin A → Fin d)))‖ ^ 2 = 1 := by
      rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp, htrace]
      have hunit := hUnit ψ hψ
      have hsq := congrArg (fun x : ℝ => x ^ 2) hunit
      rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp] at hsq
      simpa only [one_pow] using hsq
    nlinarith [norm_nonneg (WithLp.toLp 2 Ω : EuclideanSpace ℂ
      ((Fin W → Fin d) × (Fin A → Fin d)))]
  have hNative : rectangularTraceNorm
      (Ψ (vecMulVec ψ (star ψ)) - vecMulVec φ (star φ)) ≤ ε := by
    have heq (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
        chainTraceNorm X = rectangularTraceNorm X := by
      change traceNorm (Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _) X) = _
      rw [← rectangularTraceNorm_square, rectangularTraceNorm_reindex]
    rwa [heq] at herror
  have hJointError : rectangularTraceNorm
      (partialTraceRight (vecMulVec Ω (star Ω)) -
        vecMulVec (V *ᵥ φ) (star (V *ᵥ φ))) ≤ ε := by
    rw [hMarginal, ← hPure ψ, ← hPure φ]
    have heq := LinearMap.congr_fun hports (vecMulVec ψ (star ψ))
    change Γ (PortRegisters.wordInitialization (PortRegisters.portWordCode d k)
      (vecMulVec ψ (star ψ))) = _ at heq
    rw [heq, ← map_sub]
    change rectangularTraceNorm (V *
      (Ψ (vecMulVec ψ (star ψ)) - vecMulVec φ (star φ)) * Vᴴ) ≤ ε
    rw [rectangularTraceNorm_isometry_sandwich _ V V hV hV]
    exact hNative
  obtain ⟨η, hη, happrox⟩ := exists_unit_product_approx_of_pure_marginal
    (WithLp.toLp 2 Ω) (WithLp.toLp 2 (V *ᵥ φ)) hΩunit (hUnit φ hφ) hJointError
  refine ⟨A, owner, U, η, hU, ?_, hη, ?_⟩
  · exact (congrArg (fun Φ ↦ Φ ∘ₗ
      PortRegisters.wordInitialization (PortRegisters.portWordCode d k)) hDilation).trans hports
  · simpa only [WithLp.toLp_sub] using happrox

end QuantumCircuit
