/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Periodic.StepOrbitSectors
import QICLean.Channel.KrausCornerCompression
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.Core.BlockingTransfer
import QICLean.Channel.Peripheral.PeriodicityRemoval

/-!
# Peripheral spectrum after prescribed blocking

For a periodic tensor of period m, positive blocking by p leaves precisely the
roots of unity of order dividing m/gcd(m,p) in the peripheral spectrum.
This is the ambient spectral calculation in arXiv:1708.00029, the proof of
Lemma `lem:blocking-arbitrary`.

**Local fix (powered roots):** The printed root set omits the exponent p.
The correct peripheral roots satisfy z^(m/gcd(m,p)) = 1; see
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.

## Main results

* `IsPeriodic.peripheral_blockTensor`: the exact ambient peripheral spectrum.
* `IsPeriodic.peripheral_compressed_blockTensor`: the peripheral-root bound for
  any invariant compressed block.
* `adjoint_compressed_blockTensor_projection`: the cyclic action survives compression.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma 6.
-/

open scoped Matrix BigOperators
open Fin.NatCast

namespace MPSTensor

/-- Spectral mapping for positive blocking preserves exactly the powers of the
original peripheral eigenvalues. Source: arXiv:1708.00029, proof of
Lemma `lem:blocking-arbitrary`. -/
theorem peripheralEigenvalues_blockTensor {d D : ℕ} (A : MPSTensor d D)
    {p : ℕ} (hp : 0 < p) :
    peripheralEigenvalues (Kraus.transferMap (blockTensor A p)) =
      (fun z : ℂ => z ^ p) '' peripheralEigenvalues (Kraus.transferMap A) := by
  rw [transferMap_blockTensor]
  ext z
  simp only [peripheralEigenvalues, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hz, hnorm⟩
    have hs := (Module.End.hasEigenvalue_iff_mem_spectrum).1 hz
    rw [spectrum.map_pow_of_pos (𝕜 := ℂ) (a := Kraus.transferMap A) hp] at hs
    obtain ⟨w, hw, rfl⟩ := hs
    refine ⟨w, ⟨(Module.End.hasEigenvalue_iff_mem_spectrum).2 hw, ?_⟩, rfl⟩
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) (Nat.ne_of_gt hp)).1
      (by simpa only [norm_pow] using hnorm)
  · rintro ⟨w, ⟨hw, hnorm⟩, rfl⟩
    exact ⟨hw.pow p, by simp only [norm_pow, hnorm, one_pow]⟩

/-- Positive blocking changes the ambient peripheral root order from m to m/gcd(m,p).
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, peripheral-spectrum argument. -/
theorem IsPeriodic.peripheral_blockTensor {d D m : ℕ} {A : MPSTensor d D}
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    peripheralEigenvalues (Kraus.transferMap (blockTensor A p)) =
      {z : ℂ | z ^ (m / m.gcd p) = 1} := by
  rw [peripheralEigenvalues_blockTensor A hp, hA.peripheral_eq]
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← pow_mul, ← Nat.mul_div_assoc p (Nat.gcd_dvd_left m p), Nat.mul_comm p m,
      Nat.mul_div_assoc m (Nat.gcd_dvd_right m p), pow_mul, hw, one_pow]
  · intro hz
    obtain ⟨w, hw⟩ := hA.primitiveRoot
    have hpw := hw.pow_div_gcd p (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left p hA.period_pos))
    let : NeZero (m / m.gcd p) := ⟨Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_left p hA.period_pos)⟩
    obtain ⟨k, hk, hzk⟩ := hpw.eq_pow_of_pow_eq_one hz
    refine ⟨w ^ k, ?_, ?_⟩
    · rw [← pow_mul, Nat.mul_comm k m, pow_mul, hw.pow_eq_one, one_pow]
    · simpa only [← pow_mul, Nat.mul_comm k p] using hzk

/-- A compressed invariant block cannot introduce additional peripheral roots.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, peripheral-spectrum argument. -/
theorem IsPeriodic.peripheral_compressed_blockTensor {d D m n : ℕ}
    {A : MPSTensor d D} (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p)
    (C : MPSTensor (blockPhysDim d p) n) (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1) (hC : ∀ i, C i = Vᴴ * blockTensor A p i * V)
    (hcomm : ∀ i, (V * Vᴴ) * blockTensor A p i = blockTensor A p i * (V * Vᴴ))
    {z : ℂ} (hz : z ∈ peripheralEigenvalues (Kraus.transferMap C)) :
    z ^ (m / m.gcd p) = 1 := by
  have hint : ∀ i, blockTensor A p i * V = V * C i := by
    intro i
    calc
      blockTensor A p i * V = (blockTensor A p i * (V * Vᴴ)) * V := by
        simp [Matrix.mul_assoc, hV]
      _ = ((V * Vᴴ) * blockTensor A p i) * V := by rw [hcomm i]
      _ = V * C i := by rw [hC i]; simp only [Matrix.mul_assoc]
  have hzA : z ∈ peripheralEigenvalues (Kraus.transferMap (blockTensor A p)) :=
    ⟨hasEigenvalue_transferMap_of_intertwine (blockTensor A p) C V hV hint hz.1, hz.2⟩
  rwa [hA.peripheral_blockTensor hp] at hzA

/-- Compression to a step orbit preserves the cyclic action of the blocked adjoint map.
Source: arXiv:1708.00029, final display in the proof of Lemma `lem:blocking-arbitrary`. -/
theorem adjoint_compressed_blockTensor_projection {d D m n : ℕ} [NeZero m]
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (p : ℕ) (a : Fin (m.gcd p))
    (C : MPSTensor (blockPhysDim d p) n) (V : Matrix (Fin D) (Fin n) ℂ)
    (hC : ∀ i, C i = Vᴴ * blockTensor A p i * V)
    (hV : V * Vᴴ = stepOrbitProjection P p a)
    (k : Fin (m / m.gcd p)) :
    Kraus.transferMap (fun i => (C i)ᴴ)
        (Vᴴ * P (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m)) (a, k)) * V) =
      Vᴴ * P (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m)) (a, k) +
        (p : Fin m)) * V := by
  let u := Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m)) (a, k)
  have hleft : stepOrbitProjection P p a * P u = P u := by
    simpa [u] using stepOrbitProjection_mul_original P hproj hsum p a a k
  have hright : P u * stepOrbitProjection P p a = P u := by
    have h := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul, (hproj u).1.eq,
      (stepOrbitProjection_isOrthogonalProjection P hproj hsum p a).1.eq] using h
  have hexpand : V * (Vᴴ * P u * V) * Vᴴ = P u := by
    calc
      V * (Vᴴ * P u * V) * Vᴴ = (V * Vᴴ) * P u * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = P u := by rw [hV, hleft, hright]
  have hCstar : ∀ i, (C i)ᴴ = Vᴴ * (blockTensor A p i)ᴴ * V := by
    intro i
    rw [hC i]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  change Kraus.map (fun i => (C i)ᴴ) (Vᴴ * P u * V) = _
  rw [Kraus.map_compressed_eq_conj _ _ V hCstar, hexpand]
  change Vᴴ * Kraus.transferMap (fun i => (blockTensor A p i)ᴴ) (P u) * V = _
  rw [adjoint_blockTensor_projection P A hA hshift]

end MPSTensor
