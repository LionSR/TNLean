/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockingSpectrum
import QICLean.Channel.Peripheral.AdjointSpectrum

/-!
# Peripheral eigenvalues of the prescribed blocks

The cyclic projections produce eigenvectors for all roots of unity of order
m/gcd(m,p), as in arXiv:1708.00029, Lemma 6. Irreducibility and eigenvalue
multiplicities are separate from this equality of spectral sets.

**Local fix (powered roots):** The peripheral root order is m/gcd(m,p), correcting
the omitted exponent in the paper; see `docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.

## Main results

* `IsPeriodic.peripheral_compressed_stepOrbit_eq`: every compressed orbit block
  has precisely the expected peripheral roots.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma 6.
-/

open scoped Matrix BigOperators
open Fin.NatCast

namespace MPSTensor

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

end MPSTensor
