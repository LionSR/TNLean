/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceNormContractionCoefficient
import QICLean.Analysis.TraceNormVariational

/-!
# Trace norm of a difference of pure states

For unit vectors `ψ` and `φ`, the trace norm of `|ψ⟩⟨ψ| - |φ⟩⟨φ|` is at most
`2 √(2 (1 - |⟨ψ|φ⟩|))`. Choosing the phase `c` with `⟨ψ|cφ⟩ = |⟨ψ|φ⟩|`, the difference is
`|ψ - cφ⟩⟨ψ| + |cφ⟩⟨ψ - cφ|`, each rank-one term has trace norm at most
`‖ψ - cφ‖`, and `‖ψ - cφ‖² = 2 - 2|⟨ψ|φ⟩|`. So a sequence of unit vectors whose overlap
with a sequence of target states tends to one in modulus converges to it in trace norm,
which is the convergence used by Piroli, Styliaris and Cirac (arXiv:2103.13367, paragraph
"Phases of matter") to compare sequences of states.

## Main definitions

* `Matrix.traceNormPureSub` — the trace norm of `|ψ⟩⟨ψ| - |φ⟩⟨φ|` for vectors of a finite
  Euclidean space, through any enumeration of its index type.

## Main results

* `Matrix.traceNorm_vecMulVec_le` — `‖|u⟩⟨v|‖₁ ≤ ‖u‖ ‖v‖`.
* `Matrix.traceNorm_pureStateProj_sub_le` — `‖|ψ⟩⟨ψ| - |φ⟩⟨φ|‖₁ ≤ 2 √(2 (1 - |⟨ψ|φ⟩|))`
  for unit vectors.
* `Matrix.traceNormPureSub_le` — the same bound for vectors of an arbitrary finite
  Euclidean space.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), paragraph "Phases of matter": the trace-norm
  convergence `‖σ_M - |φ_M⟩⟨φ_M|‖₁ → 0`.
* Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 8.1 (trace norm).
-/

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Matrix

variable {D : ℕ}

/-- A unitary matrix preserves the Euclidean norm. -/
theorem norm_toLp_mulVec_of_mem_unitaryGroup {U : Matrix (Fin D) (Fin D) ℂ}
    (hU : U ∈ unitaryGroup (Fin D) ℂ) (v : Fin D → ℂ) :
    ‖WithLp.toLp 2 (U *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have hinner : ⟪WithLp.toLp 2 (U *ᵥ v), WithLp.toLp 2 (U *ᵥ v)⟫_ℂ =
      ⟪WithLp.toLp 2 v, WithLp.toLp 2 v⟫_ℂ := by
    rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
      star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').mp hU, one_mulVec, dotProduct_comm]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
  have h2 : ‖WithLp.toLp 2 (U *ᵥ v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by exact_mod_cast hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- **Trace norm of a rank-one matrix.** `‖|u⟩⟨v|‖₁ ≤ ‖u‖ ‖v‖`: for the unitary `U` attaining
the trace norm in its variational form, `‖|u⟩⟨v|‖₁ = |⟨u|Uv⟩| ≤ ‖u‖ ‖Uv‖ = ‖u‖ ‖v‖`. -/
theorem traceNorm_vecMulVec_le (u v : Fin D → ℂ) :
    traceNorm (vecMulVec u (star v)) ≤ ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ := by
  obtain ⟨U, hU, htr⟩ := exists_mem_unitaryGroup_trace_conjTranspose_mul_eq (vecMulVec u (star v))
  have htrace : ((vecMulVec u (star v))ᴴ * U).trace =
      ⟪WithLp.toLp 2 u, WithLp.toLp 2 (U *ᵥ v)⟫_ℂ := by
    rw [conjTranspose_vecMulVec, star_star, vecMulVec_mul, trace_vecMulVec,
      EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u) (WithLp.toLp 2 (U *ᵥ v))
  rw [← htrace, htr, Complex.norm_real, Real.norm_of_nonneg (traceNorm_nonneg _),
    norm_toLp_mulVec_of_mem_unitaryGroup hU] at h
  exact h

/-- **Trace norm of a difference of pure states.** For unit vectors `ψ` and `φ`,
`‖|ψ⟩⟨ψ| - |φ⟩⟨φ|‖₁ ≤ 2 √(2 (1 - |⟨ψ|φ⟩|))`.

With the phase `c` making `⟨ψ|cφ⟩ = |⟨ψ|φ⟩|`, `|ψ⟩⟨ψ| - |φ⟩⟨φ| = |ψ - cφ⟩⟨ψ| + |cφ⟩⟨ψ - cφ|`,
whose trace norm is at most `2 ‖ψ - cφ‖ = 2 √(2 - 2 |⟨ψ|φ⟩|)`. -/
theorem traceNorm_pureStateProj_sub_le {ψ φ : EuclideanSpace ℂ (Fin D)} (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) :
    traceNorm (pureStateProj (WithLp.ofLp ψ) - pureStateProj (WithLp.ofLp φ)) ≤
      2 * Real.sqrt (2 * (1 - ‖⟪ψ, φ⟫_ℂ‖)) := by
  set z : ℂ := ⟪ψ, φ⟫_ℂ with hz
  -- The phase aligning `φ` with `ψ`.
  obtain ⟨c, hc1, hcz⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ c * z = (‖z‖ : ℂ) := by
    by_cases hz0 : z = 0
    · exact ⟨1, by simp, by simp [hz0]⟩
    · have hnz : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz0
      refine ⟨conj z / ‖z‖, ?_, ?_⟩
      · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          div_self (norm_ne_zero_iff.mpr hz0)]
      · rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        field_simp
        push_cast
        ring
  set φ' : EuclideanSpace ℂ (Fin D) := c • φ with hφ'
  have hcc : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]
    norm_num
  have hproj : pureStateProj (WithLp.ofLp φ') = pureStateProj (WithLp.ofLp φ) := by
    ext i j
    simp only [pureStateProj, vecMulVec_apply, hφ', WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, star_mul']
    calc c * φ i * (star c * star (φ j)) = (c * star c) * (φ i * star (φ j)) := by ring
      _ = φ i * star (φ j) := by rw [hcc, one_mul]
  have hφ'1 : ‖φ'‖ = 1 := by rw [hφ', norm_smul, hc1, hφ, one_mul]
  have hinner : ⟪ψ, φ'⟫_ℂ = (‖z‖ : ℂ) := by rw [hφ', inner_smul_right, hcz]
  -- The decomposition into two rank-one terms.
  have hdecomp : pureStateProj (WithLp.ofLp ψ) - pureStateProj (WithLp.ofLp φ) =
      vecMulVec (WithLp.ofLp (ψ - φ')) (star (WithLp.ofLp ψ)) +
        vecMulVec (WithLp.ofLp φ') (star (WithLp.ofLp (ψ - φ'))) := by
    rw [← hproj]
    ext i j
    simp only [pureStateProj, sub_apply, add_apply, vecMulVec_apply, WithLp.ofLp_sub,
      Pi.sub_apply, Pi.star_apply, star_sub]
    ring
  have hsub : ‖ψ - φ'‖ = Real.sqrt (2 * (1 - ‖z‖)) := by
    have h2 : ‖ψ - φ'‖ ^ 2 = 2 * (1 - ‖z‖) := by
      have hre : RCLike.re ((‖z‖ : ℝ) : ℂ) = ‖z‖ := Complex.ofReal_re _
      rw [@norm_sub_sq ℂ, hψ, hφ'1, hinner, hre]
      ring
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  calc traceNorm (pureStateProj (WithLp.ofLp ψ) - pureStateProj (WithLp.ofLp φ))
      ≤ traceNorm (vecMulVec (WithLp.ofLp (ψ - φ')) (star (WithLp.ofLp ψ))) +
          traceNorm (vecMulVec (WithLp.ofLp φ') (star (WithLp.ofLp (ψ - φ')))) := by
        rw [hdecomp]
        exact traceNorm_add_le _ _
    _ ≤ ‖ψ - φ'‖ * ‖ψ‖ + ‖φ'‖ * ‖ψ - φ'‖ :=
        add_le_add (traceNorm_vecMulVec_le _ _) (traceNorm_vecMulVec_le _ _)
    _ = 2 * Real.sqrt (2 * (1 - ‖z‖)) := by rw [hψ, hφ'1, hsub]; ring

variable {ι : Type*} [Fintype ι]

/-- The trace norm of `|ψ⟩⟨ψ| - |φ⟩⟨φ|` for vectors of the finite Euclidean space
`EuclideanSpace ℂ ι`, computed after enumerating `ι` by `Fintype.equivFin`. The trace norm does
not depend on the enumeration; `traceNormPureSub_le` is the bound used here.

Source: arXiv:2103.13367, paragraph "Phases of matter", the trace norm
`‖σ_M - |φ_M⟩⟨φ_M|‖₁` at a pure state `σ_M = |ψ_M⟩⟨ψ_M|`. -/
def traceNormPureSub (ψ φ : EuclideanSpace ℂ ι) : ℝ :=
  traceNorm
    (pureStateProj (WithLp.ofLp (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι) ψ)) -
      pureStateProj (WithLp.ofLp (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι) φ)))

theorem traceNormPureSub_nonneg (ψ φ : EuclideanSpace ℂ ι) : 0 ≤ traceNormPureSub ψ φ :=
  traceNorm_nonneg _

/-- **Trace norm of a difference of pure states**, for vectors of a finite Euclidean space:
`‖|ψ⟩⟨ψ| - |φ⟩⟨φ|‖₁ ≤ 2 √(2 (1 - |⟨ψ|φ⟩|))` for unit vectors `ψ` and `φ`. -/
theorem traceNormPureSub_le {ψ φ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNormPureSub ψ φ ≤ 2 * Real.sqrt (2 * (1 - ‖⟪ψ, φ⟫_ℂ‖)) := by
  set e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  have h := traceNorm_pureStateProj_sub_le (ψ := e ψ) (φ := e φ) (by rw [e.norm_map, hψ])
    (by rw [e.norm_map, hφ])
  rwa [e.inner_map_map] at h

end Matrix
