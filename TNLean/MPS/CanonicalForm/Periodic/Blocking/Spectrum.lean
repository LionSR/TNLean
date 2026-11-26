/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Irreducible.Periodic
import TNLean.MPS.CanonicalForm.Periodic.Blocking.StepOrbitSectors
import QICLean.Channel.KrausMap.KrausCornerCompression
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureSpectral
import TNLean.MPS.Tensor.Physical.BlockingTransfer
import QICLean.Channel.Peripheral.Spectrum.AdjointSpectrum

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
* `MPSTensor.IsPeriodic.peripheral_compressed_stepOrbit_eq`: peripheral eigenvalues of the
  prescribed blocks.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma 6.
-/

open scoped Matrix BigOperators
open Fin.NatCast
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

section Spectrum

/-- Spectral mapping for positive blocking preserves exactly the powers of the
original peripheral eigenvalues. Source: arXiv:1708.00029, proof of
Lemma `lem:blocking-arbitrary`. -/
theorem peripheralEigenvalues_blockTensor {d D : ℕ} (A : MPSTensor d D)
    {p : ℕ} (hp : 0 < p) :
    peripheralEigenvalues (Kraus.transferMap (blockTensor A p)) =
      (fun z : ℂ => z ^ p) '' peripheralEigenvalues (Kraus.transferMap A) := by
  rw [Kraus.transferMap_blockTensor]
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

end Spectrum

section Eigenvalues

/-!
## Peripheral eigenvalues of the prescribed blocks

The cyclic projections produce eigenvectors for all roots of unity of order
m/gcd(m,p), as in arXiv:1708.00029, Lemma 6. Irreducibility and eigenvalue
multiplicities are separate from this equality of spectral sets.

**Local fix (powered roots):** The peripheral root order is m/gcd(m,p), correcting
the omitted exponent in the paper; see `docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.

### Main results

* `IsPeriodic.peripheral_compressed_stepOrbit_eq`: every compressed orbit block
  has precisely the expected peripheral roots.

### References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma 6.
-/

/-- If `f` shifts a cyclic family `v` and `z ^ q = 1`, then `∑ z ^ k • v k` is an
eigenvector of `f` with eigenvalue `z⁻¹`. -/
private theorem map_cyclic_sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {q : ℕ} [NeZero q] (f : M →ₗ[ℂ] M) (v : Fin q → M)
    (hshift : ∀ k, f (v k) = v (k + 1)) (z : ℂ) (hz : z ^ q = 1) :
    f (∑ k, z ^ k.val • v k) = z⁻¹ • ∑ k, z ^ k.val • v k := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h, NeZero.ne q] at hz
  have hpow (k : Fin q) : z ^ (k + 1).val = z * z ^ k.val := by
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rw [← pow_eq_pow_mod (k.val + 1) hz, pow_succ, mul_comm]
  have h : z • f (∑ k, z ^ k.val • v k) = ∑ k, z ^ k.val • v k := by
    simp only [map_sum, map_smul, hshift, Finset.smul_sum, smul_smul]
    simp_rw [← hpow]
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin q)) (fun k => z ^ k.val • v k)
  calc
    f (∑ k, z ^ k.val • v k) = z⁻¹ • (z • f (∑ k, z ^ k.val • v k)) := by
      rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
    _ = z⁻¹ • ∑ k, z ^ k.val • v k := by rw [h]

/-- Every `q`-th root of unity gives a nonzero eigenvector of the compressed adjoint
transfer map, namely the Fourier sum of the compressed orbit projections.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, final step. -/
private theorem hasEigenvalue_adjoint_compressed_stepOrbit
    {d D m n : ℕ} [NeZero m]
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hne : ∀ u, P u ≠ 0) (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (p : ℕ) (a : Fin (m.gcd p))
    (C : MPSTensor (blockPhysDim d p) n) (V : Matrix (Fin D) (Fin n) ℂ)
    (hC : ∀ i, C i = Vᴴ * blockTensor A p i * V)
    (hV : V * Vᴴ = stepOrbitProjection P p a)
    (z : ℂ) (hz : z ^ (m / m.gcd p) = 1) :
    Module.End.HasEigenvalue (Kraus.transferMap (fun i => (C i)ᴴ)) z⁻¹ := by
  let : NeZero (m / m.gcd p) :=
    ⟨Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_left p (Nat.pos_of_ne_zero (NeZero.ne m)))⟩
  let e := Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))
  let v := fun k : Fin (m / m.gcd p) => Vᴴ * P (e (a, k)) * V
  have hcycle (k : Fin (m / m.gcd p)) :
      Kraus.transferMap (fun i => (C i)ᴴ) (v k) = v (k + 1) := by
    rw [show v k = Vᴴ * P (e (a, k)) * V from rfl,
      adjoint_compressed_blockTensor_projection P hproj hsum A hA hshift p a C V hC hV k]
    rw [← Fin.stepOrbitEquiv_add_one m p (Nat.pos_of_ne_zero (NeZero.ne m)) a k]
  have hlift (k : Fin (m / m.gcd p)) : V * v k * Vᴴ = P (e (a, k)) := by
    have hleft : (V * Vᴴ) * P (e (a, k)) = P (e (a, k)) := by
      rw [hV]
      simpa [e] using stepOrbitProjection_mul_original P hproj hsum p a a k
    have hright : P (e (a, k)) * (V * Vᴴ) = P (e (a, k)) := by
      have h := congrArg Matrix.conjTranspose hleft
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        (hproj (e (a, k))).1.eq] using h
    change V * (Vᴴ * P (e (a, k)) * V) * Vᴴ = _
    calc
      V * (Vᴴ * P (e (a, k)) * V) * Vᴴ =
          ((V * Vᴴ) * P (e (a, k))) * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
      _ = P (e (a, k)) := by rw [hleft, hright]
  have hprod (k : Fin (m / m.gcd p)) :
      P (e (a, k)) * P (e (a, 0)) = if k = 0 then P (e (a, 0)) else 0 := by
    rw [orthogonalProjection_mul_eq_ite_of_sum_eq_one P hproj hsum]
    simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq, true_and]
    split_ifs with hk
    · rw [hk]
    · rfl
  apply hasEigenvalue_of_eigenvector_eq _ z⁻¹ (∑ k, z ^ k.val • v k)
  · exact map_cyclic_sum _ v hcycle z hz
  · intro hzero
    have h := congrArg (fun X => V * X * Vᴴ * P (e (a, 0))) hzero
    have hliftSum : V * (∑ k, z ^ k.val • v k) * Vᴴ =
        ∑ k, z ^ k.val • P (e (a, k)) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hlift]
    rw [hliftSum] at h
    simp only [Matrix.sum_mul, Matrix.smul_mul, hprod] at h
    exact hne (e (a, 0)) (by simpa using h)

/-- Every prescribed orbit block has the full peripheral root set of order m/gcd(m,p).
Source: arXiv:1708.00029, Lemma 6, the final spectral argument. This statement does not
assert irreducibility or the multiplicities of these eigenvalues. -/
theorem IsPeriodic.peripheral_compressed_stepOrbit_eq {d D m n : ℕ} [NeZero m]
    {A : MPSTensor d D} (hA : IsPeriodic m A)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hne : ∀ u, P u ≠ 0) (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    {p : ℕ} (hp : 0 < p) (a : Fin (m.gcd p))
    (C : MPSTensor (blockPhysDim d p) n) (V : Matrix (Fin D) (Fin n) ℂ)
    (hiso : Vᴴ * V = 1) (hV : V * Vᴴ = stepOrbitProjection P p a)
    (hC : ∀ i, C i = Vᴴ * blockTensor A p i * V) :
    peripheralEigenvalues (Kraus.transferMap C) = {z : ℂ | z ^ (m / m.gcd p) = 1} := by
  ext z
  constructor
  · intro hz
    exact hA.peripheral_compressed_blockTensor hp C V hiso hC
      (fun i => by rw [hV]; exact stepOrbitProjection_mul_blockTensor P A hshift p a i) hz
  · intro hz
    have hw : ((star z)⁻¹) ^ (m / m.gcd p) = 1 := by
      rw [inv_pow, ← star_pow, hz, star_one, inv_one]
    have he := hasEigenvalue_adjoint_compressed_stepOrbit P hproj hsum hne A
      hA.leftCanonical hshift p a C V hC hV ((star z)⁻¹) hw
    simp only [inv_inv] at he
    have he' := (Kraus.hasEigenvalue_mapLM_conjTranspose_iff C (star z)).mp he
    simp only [star_star] at he'
    refine ⟨he', ?_⟩
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg z)
      (Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_left p hA.period_pos))).mp
    simpa only [norm_pow, norm_one] using congrArg norm hz

end Eigenvalues

end MPSTensor
