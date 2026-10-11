/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeParameterBound

/-!
# Degenerate intervals and zero replicas in the charge integral

Equal interval endpoints give equality in the one-round formula. At zero
replicas the left side vanishes, while scalar integrability still applies to
every supplied vector. Entropy-gain integrability retains its nonzero-vector
hypothesis.
-/

set_option autoImplicit false

open TensorPower TensorPower.ReplicaTransport MeasureTheory
open TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualChargeParameterBound

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)

/-- The zero-length interval gives the exact equality `0 = 0`, including both
logarithmic terms and the interval-length factor on the error. -/
theorem equal_endpoints (a α A B : ℝ) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    let D := S.actualChargeData hm hM s
    (r : ℝ) * a * α *
        (∫ x in p..p, S.actualChargeEntropyDefect hm hM s n E (a / 2) r pre x) =
      Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p) pre) -
        Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p) pre) +
        (p - p) * (A + B) := by
  simp

/-- The zero-replica charge integral has zero prefactor, without requiring the
supplied vector to vanish. -/
theorem zero_replica_prefactor (a α p₀ p₁ : ℝ)
    (pre : Config 0 (fun v => Fin (n v)) → ℂ) :
    (0 : ℝ) * a * α *
      (∫ p in p₀..p₁, S.actualChargeEntropyDefect hm hM s n E (a / 2) 0 pre p) = 0 := by
  simp

/-- At zero replicas both integrability theorems apply to the same nonzero
supplied vector; the charge theorem alone also permits the zero vector. -/
theorem zero_replica_integrability {a : ℝ} (ha : 0 ≤ a)
    (pre : Config 0 (fun v => Fin (n v)) → ℂ) (hne : pre ≠ 0) :
    IntervalIntegrable (S.actualChargeEntropyDefect hm hM s n E (a / 2) 0 pre)
        volume 0 1 ∧
      IntervalIntegrable ((S.actualChargeData hm hM s).entropyGain n (a / 2) 0 pre)
        volume 0 1 := by
  have ht : 0 ≤ a / 2 := div_nonneg ha (by norm_num)
  exact ⟨S.intervalIntegrable_actualChargeEntropyDefect hm hM s n E ht 0 pre,
    (S.actualChargeData hm hM s).intervalIntegrable_entropyGain
      (S.actualChargeData_isAdmissible hm hM s) ht
      (S.chargeTransportData_crossBandCommute _ _ n ht 0) hne⟩

end TNLeanTest.ActualChargeParameterBound

set_option linter.hashCommand false

open TNLeanTest.ActualChargeParameterBound in
/-- info:
'TNLeanTest.ActualChargeParameterBound.zero_replica_integrability'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zero_replica_integrability
