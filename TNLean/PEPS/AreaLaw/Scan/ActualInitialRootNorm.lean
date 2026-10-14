/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Representation.ReplicaTransport.RootMetricFloor
import TNLean.PEPS.AreaLaw.Scan.FillTransport

/-!
# Initial normalization of the actual fill

The polynomial floor for a transport root gives a logarithmic upper bound
for the squared filtered norm at the initial actual fill. The scanner and
local dimensions are fixed before the replica count and vector. Validity
and band commutation follow from the actual fill construction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 458–461, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower TensorPower.ReplicaTransport

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

/-- The initial actual fill root has a logarithmic filtered-norm upper bound
for the same supplied vector of Euclidean norm at most one. The constant is
chosen before the replica count and vector.
Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 458–461, at `openai/math@adc7f124`.
This is the initial normalization estimate, not the complete scanner theorem. -/
theorem exists_actualFillData_initial_log_filteredNormSq_bound
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
        ‖(EuclideanSpace.equiv
          (Config k fun v => Fin (n v)) ℂ).symm pre‖ ≤ 1 →
        Real.log (Matrix.Transport.filteredNormSq
          ((S.actualFillData hm hM 0).rootPath n (a / 2) k 0) pre) ≤
          C * Real.log ((k : ℝ) + 2) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_rootPath_log_filteredNormSq_bound n (half_pos ha)
  exact ⟨C₀ * (S.K : ℝ) / 2,
    div_nonneg (mul_nonneg hC₀ (Nat.cast_nonneg S.K)) zero_le_two,
    fun k pre hpre ↦ hbound S.K (S.actualFillData hm hM 0)
      (S.actualFillData_isAdmissible hm hM 0) k
      (S.fillTransportData_crossBandCommute _ n (half_pos ha).le k) 0 pre hpre⟩

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
