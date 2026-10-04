/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Conversion

/-!
# Onsite instruments with classical feedforward

An onsite channel specifies local Kraus operators and therefore a local quantum instrument.
Recording the Kraus index at every site gives an outcome tuple which can be communicated
globally. The continuation may depend on the entire tuple. Averaging the unnormalized branch
operations gives a trace-preserving completely positive map whenever every continuation is a
channel. No division by outcome probabilities is used.

## Main results

* `QuantumCircuit.OnsiteChannel.feedforwardMap_isKrausCPTP` — conditional continuation
  followed by forgetting outcomes gives a channel.
* `QuantumCircuit.OnsiteChannel.feedforwardMap_const` — ignoring outcomes gives ordinary
  channel composition.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraphs "Quantum circuits and LOCC"
  and "State transformations with QC and LOCC".
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace QuantumCircuit

variable {d e f N : ℕ}

namespace OnsiteChannel

/-- Measure the Kraus outcomes of an onsite instrument, communicate their tuple, and apply
an outcome-dependent channel. The summands act on unnormalized post-measurement states. -/
def feedforwardMap (Φ : OnsiteChannel d e (Fin N))
    (Ψ : ((i : Fin N) → Fin (Φ.r i)) →
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ :=
  ∑ J, Ψ J ∘ₗ singleKrausMap (Φ.krausOp J)

/-- Conditional continuation preserves the normalization of the onsite instrument. -/
theorem feedforwardMap_isKrausCPTP (Φ : OnsiteChannel d e (Fin N))
    (Ψ : ((i : Fin N) → Fin (Φ.r i)) →
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ)
    (hΨ : ∀ J, IsKrausCPTP (Ψ J)) : IsKrausCPTP (Φ.feedforwardMap Ψ) := by
  classical
  choose r K hK hnorm using hΨ
  let A (p : (J : (i : Fin N) → Fin (Φ.r i)) × Fin (r J)) := K p.1 p.2 * Φ.krausOp p.1
  have hmap : Φ.feedforwardMap Ψ = rectangularKrausMap A := by
    apply LinearMap.ext
    intro X
    simp only [feedforwardMap, LinearMap.sum_apply, LinearMap.comp_apply,
      singleKrausMap_apply]
    change (∑ J, Ψ J (Φ.krausOp J * X * (Φ.krausOp J)ᴴ)) =
      ∑ p, A p * X * (A p)ᴴ
    simp only [hK, Fintype.sum_sigma, A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hmap]
  apply rectangularKrausMap_isKrausCPTP
  calc
    ∑ p, (A p)ᴴ * A p =
        ∑ J, (Φ.krausOp J)ᴴ * (∑ j, (K J j)ᴴ * K J j) * Φ.krausOp J := by
      simp only [A, Fintype.sum_sigma, Matrix.conjTranspose_mul, Matrix.mul_sum,
        Matrix.sum_mul, Matrix.mul_assoc]
    _ = ∑ J, (Φ.krausOp J)ᴴ * Φ.krausOp J := by simp only [hnorm, Matrix.mul_one]
    _ = 1 := Φ.sum_krausOp

/-- If the continuation ignores the outcome, averaging the instrument first has the same
result. -/
theorem feedforwardMap_const (Φ : OnsiteChannel d e (Fin N))
    (Ψ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ) :
    Φ.feedforwardMap (fun _ ↦ Ψ) = Ψ ∘ₗ Φ.map := by
  apply LinearMap.ext
  intro X
  simp only [feedforwardMap, LinearMap.sum_apply, LinearMap.comp_apply,
    singleKrausMap_apply]
  change (∑ J, Ψ (Φ.krausOp J * X * (Φ.krausOp J)ᴴ)) =
    Ψ (∑ J, Φ.krausOp J * X * (Φ.krausOp J)ᴴ)
  rw [map_sum]

/-- A channel applied after classical feedforward may be composed into every continuation. -/
theorem comp_feedforwardMap {g : ℕ} (Φ : OnsiteChannel d e (Fin N))
    (Ψ : ((i : Fin N) → Fin (Φ.r i)) →
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ)
    (Θ : Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin g) (Fin N → Fin g) ℂ) :
    Θ ∘ₗ Φ.feedforwardMap Ψ = Φ.feedforwardMap (fun J ↦ Θ ∘ₗ Ψ J) := by
  ext X a b
  simp only [feedforwardMap, LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
    Matrix.sum_apply]

end OnsiteChannel

end QuantumCircuit
