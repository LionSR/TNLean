/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition.Basic

/-!
# Sector dynamics for cyclic decompositions

This file studies the dynamics on the sectors coming from a cyclic
decomposition: corner preservation, irreducibility on each sector, primitivity
of the sector restrictions, and the permutation variant used later in the
peripheral-spectrum development.

## Main statements

* `preserves_corner_pow_of_cyclic_decomp`
* `isIrreducible_restriction_of_cyclic_decomp`
* `isPrimitive_restriction_of_cyclic_decomp`
* `preserves_corner_pow_orderOf_of_perm_decomp`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm. 6.6, Thm. 6.16]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

section PrimitivityOfSectors

variable {D m : ℕ} [NeZero m]

private def cyclicIndex (k : Fin m) (n : ℕ) : Fin m :=
  ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

@[simp] private lemma cyclicIndex_zero (k : Fin m) :
    cyclicIndex (m := m) k 0 = k := by
  ext
  simp only [cyclicIndex, add_zero, Nat.mod_eq_of_lt k.is_lt, Fin.eta]

private lemma cyclicIndex_succ (k : Fin m) (n : ℕ) :
    cyclicIndex (m := m) k (n + 1) = cyclicIndex k n + 1 := by
  ext
  change (((k : ℕ) + n) + 1) % m = ((((k : ℕ) + n) % m) + 1 % m) % m
  exact Nat.add_mod ((k : ℕ) + n) 1 m

@[simp] private lemma cyclicIndex_self (k : Fin m) :
    cyclicIndex (m := m) k m = k := by
  ext
  change ((k : ℕ) + m) % m = k
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]

/-- The `m`-th power of the channel preserves each cyclic corner `P_k · M_D(ℂ) · P_k`.

The cyclic permutation of the projections alone is not enough for this conclusion for a general
linear map. We therefore assume the left- and right-multiplicative-domain identities on the
sector projections, which are the abstract consequences needed from the multiplicative-domain
argument in Wolf Theorem 6.6. -/
theorem preserves_corner_pow_of_cyclic_decomp
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (_hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)) :
    ∀ k : Fin m, PreservesCorner (P k) (T ^ m) := by
  have hstep :
      ∀ n : ℕ, ∀ k : Fin m, ∀ X : MatrixAlg D,
        (T ^ n) (P (cyclicIndex k n) * X * P (cyclicIndex k n)) =
          P k * ((T ^ n) X) * P k := by
    intro n
    induction n with
    | zero =>
        intro k X
        simp only [pow_zero, cyclicIndex_zero, Module.End.one_apply]
    | succ n ih =>
        intro k X
        calc
          (T ^ (n + 1))
              (P (cyclicIndex k (n + 1)) * X * P (cyclicIndex k (n + 1)))
              = (T ^ n) (T (P (cyclicIndex k (n + 1)) * X * P (cyclicIndex k (n + 1)))) := by
                  simp only [pow_succ, Module.End.mul_apply]
          _ = (T ^ n) (T (P (cyclicIndex k n + 1) * X * P (cyclicIndex k n + 1))) := by
                  rw [cyclicIndex_succ k n]
          _ = (T ^ n) (P (cyclicIndex k n) * T X * P (cyclicIndex k n)) := by
                  congr 1
                  calc
                    T (P (cyclicIndex k n + 1) * X * P (cyclicIndex k n + 1))
                        = T (P (cyclicIndex k n + 1) * X) * T (P (cyclicIndex k n + 1)) := by
                            exact hMulRight (cyclicIndex k n + 1) (P (cyclicIndex k n + 1) * X)
                    _ = (T (P (cyclicIndex k n + 1)) * T X) * T (P (cyclicIndex k n + 1)) := by
                            rw [hMulLeft (cyclicIndex k n + 1) X]
                    _ = P (cyclicIndex k n) * T X * P (cyclicIndex k n) := by
                            rw [hcyclic (cyclicIndex k n)]
          _ = P k * ((T ^ n) (T X)) * P k := ih k (T X)
          _ = P k * ((T ^ (n + 1)) X) * P k := by
                  simp only [pow_succ, Module.End.mul_apply]
  intro k X
  have hmk : (T ^ m) (P k * X * P k) = P k * ((T ^ m) X) * P k := by
    simpa using hstep m k X
  rw [hmk]
  calc
    P k * (P k * ((T ^ m) X) * P k) * P k
        = (P k * P k) * ((T ^ m) X) * (P k * P k) := by
            simp only [Matrix.mul_assoc]
    _ = P k * ((T ^ m) X) * P k := by
            simp only [(hPproj k).2, Matrix.mul_assoc]

/-- Wolf Theorem 6.6 corollary: an orbit-sum lift from invariant corner subprojections to
ambient invariant projections implies irreducibility of the `m`-step dynamics on each cyclic
sector. -/
theorem isIrreducible_restriction_of_cyclic_decomp
    {T : MatrixEnd D}
    (hIrr : IsIrreducibleMap T)
    (P : Fin m → MatrixAlg D)
    (_hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (_hPsum : ∑ k : Fin m, P k = 1)
    (_hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hLift :
      ∀ k : Fin m, ∀ Q : MatrixAlg D,
        IsOrthogonalProjection Q →
        Q * P k = Q →
        P k * Q = Q →
        PreservesCorner Q (T ^ m) →
        ∃ R : MatrixAlg D,
          IsOrthogonalProjection R ∧
          PreservesCorner R T ∧
          (Q = 0 ↔ R = 0) ∧
          (Q = P k ↔ R = 1)) :
    ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
  intro k Q hQproj hQP hPQ hQinv
  rcases hLift k Q hQproj hQP hPQ hQinv with ⟨R, hRproj, hRinv, hQzero, hQfull⟩
  rcases hIrr R hRproj hRinv with hR0 | hR1
  · left
    exact hQzero.mpr hR0
  · right
    exact hQfull.mpr hR1
/-- Wolf Theorem 6.6 corollary: the `m`-step dynamics on each cyclic sector is primitive. -/
theorem isPrimitive_restriction_of_cyclic_decomp
    {T : MatrixEnd D} [NeZero D] {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k))
    (hPne : ∀ k : Fin m, P k ≠ 0) :
    ∀ k : Fin m,
      IsPrimitive
        (cornerRestriction (P k) (T ^ m)
          (preserves_corner_pow_of_cyclic_decomp
            (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight k)) := by
  let hInv : ∀ k : Fin m, PreservesCorner (P k) (T ^ m) :=
    preserves_corner_pow_of_cyclic_decomp (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight
  have hone_mem : (1 : ℂ) ∈ peripheralEigenvalues T := by
    rw [hperiph]
    exact ⟨0, by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero]⟩
  rcases hone_mem.1.exists_hasEigenvector with ⟨ρ, hρeig⟩
  have hρ_fix : T ρ = ρ := by
    exact (Module.End.HasEigenvector.apply_eq_smul hρeig).trans (by simp only [one_smul])
  have hρ_ne : ρ ≠ 0 := (Module.End.hasEigenvector_iff.mp hρeig).2
  have hper_pow : ∀ μ : ℂ, μ ∈ peripheralEigenvalues T → μ ^ m = 1 := by
    intro μ hμ
    rw [hperiph] at hμ
    rcases hμ with ⟨j, rfl⟩
    calc
      (γ ^ (j : ℕ)) ^ m = γ ^ ((j : ℕ) * m) := by rw [pow_mul]
      _ = γ ^ (m * (j : ℕ)) := by rw [Nat.mul_comm]
      _ = (γ ^ m) ^ (j : ℕ) := by rw [pow_mul]
      _ = 1 := by simp only [hγprim.pow_eq_one, one_pow]
  have hperiph_pow : peripheralEigenvalues (T ^ m) = {1} :=
    peripheralEigenvalues_pow_eq_singleton
      (E := T) (p := m) (hp := Nat.pos_of_ne_zero (NeZero.ne m))
      hper_pow ρ hρ_fix hρ_ne
  have hcyclic_pow : ∀ n : ℕ, ∀ k : Fin m, (T ^ n) (P (cyclicIndex k n)) = P k := by
    intro n
    induction n with
    | zero =>
        intro k
        simp only [pow_zero, cyclicIndex_zero, Module.End.one_apply]
    | succ n ih =>
        intro k
        calc
          (T ^ (n + 1)) (P (cyclicIndex k (n + 1)))
              = (T ^ n) (T (P (cyclicIndex k (n + 1)))) := by
                  simp only [pow_succ, Module.End.mul_apply]
          _ = (T ^ n) (T (P (cyclicIndex k n + 1))) := by
                  rw [cyclicIndex_succ k n]
          _ = (T ^ n) (P (cyclicIndex k n)) := by
                  rw [hcyclic (cyclicIndex k n)]
          _ = P k := ih k
  have hPk_fix : ∀ k : Fin m, (T ^ m) (P k) = P k := by
    intro k
    simpa using hcyclic_pow m k
  have hPk_corner : ∀ k : Fin m, P k ∈ cornerSubmodule (P k) := by
    intro k
    change P k * P k * P k = P k
    rw [Matrix.mul_assoc, (hPproj k).2, (hPproj k).2]
  have hcorner_fix : ∀ k : Fin m,
      cornerRestriction (P k) (T ^ m) (hInv k) ⟨P k, hPk_corner k⟩ = ⟨P k, hPk_corner k⟩ := by
    intro k
    apply Subtype.ext
    simpa using hPk_fix k
  have hcorner_ne : ∀ k : Fin m, (⟨P k, hPk_corner k⟩ : cornerSubmodule (P k)) ≠ 0 := by
    intro k hzero
    apply hPne k
    have hval := congrArg Subtype.val hzero
    simpa using hval
  have huniq : ∀ k : Fin m, ∀ μ : ℂ,
      Module.End.HasEigenvalue (cornerRestriction (P k) (T ^ m) (hInv k)) μ →
      ‖μ‖ = 1 → μ = 1 := by
    intro k μ hμeig hμnorm
    rcases hμeig.exists_hasEigenvector with ⟨X, hX⟩
    have hX_mem : X ∈ Module.End.eigenspace (cornerRestriction (P k) (T ^ m) (hInv k)) μ :=
      (Module.End.hasEigenvector_iff.mp hX).1
    have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
    have hX_eq : cornerRestriction (P k) (T ^ m) (hInv k) X = μ • X :=
      (Module.End.mem_eigenspace_iff).1 hX_mem
    have hX_eq_val : (T ^ m) X.1 = μ • X.1 := congrArg Subtype.val hX_eq
    have hX_mem_ambient : X.1 ∈ Module.End.eigenspace (T ^ m) μ :=
      (Module.End.mem_eigenspace_iff).2 hX_eq_val
    have hX_ne_ambient : X.1 ≠ 0 := by
      intro h0
      apply hX_ne
      apply Subtype.ext
      simpa using h0
    have hX_eig_ambient : Module.End.HasEigenvector (T ^ m) μ X.1 :=
      (Module.End.hasEigenvector_iff).2 ⟨hX_mem_ambient, hX_ne_ambient⟩
    have hμ_ambient : μ ∈ peripheralEigenvalues (T ^ m) :=
      ⟨Module.End.hasEigenvalue_of_hasEigenvector hX_eig_ambient, hμnorm⟩
    rw [hperiph_pow] at hμ_ambient
    exact hμ_ambient
  intro k
  exact isPrimitive_of_unique_norm_one
    (cornerRestriction (P k) (T ^ m) (hInv k))
    ⟨P k, hPk_corner k⟩
    (hcorner_fix k)
    (hcorner_ne k)
    (huniq k)

section PermutationBlockStructure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Permutation-based variant of `preserves_corner_pow_of_cyclic_decomp`.

This isolates the part of Wolf Thm. 6.16 that only needs a permutation action on blocks:
if `T` permutes a family of sector projections via a permutation `σ`, then the `orderOf σ`-th
iterate preserves each sector corner. -/
theorem preserves_corner_pow_orderOf_of_perm_decomp
    {T : MatrixEnd D}
    (σ : Equiv.Perm ι)
    (P : ι → MatrixAlg D)
    (hPproj : ∀ k : ι, IsOrthogonalProjection (P k))
    (hperm : ∀ k : ι, T (P (σ k)) = P k)
    (hMulLeft : ∀ k : ι, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : ι, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)) :
    ∀ k : ι, PreservesCorner (P k) (T ^ orderOf σ) := by
  have hstep :
      ∀ n : ℕ, ∀ k : ι, ∀ X : MatrixAlg D,
        (T ^ n) (P ((σ ^ n) k) * X * P ((σ ^ n) k)) =
          P k * ((T ^ n) X) * P k := by
    intro n
    induction n with
    | zero =>
        intro k X
        simp only [pow_zero, Equiv.Perm.coe_one, id_eq, Module.End.one_apply]
    | succ n ih =>
        intro k X
        calc
          (T ^ (n + 1)) (P ((σ ^ (n + 1)) k) * X * P ((σ ^ (n + 1)) k))
              = (T ^ n) (T (P ((σ ^ (n + 1)) k) * X * P ((σ ^ (n + 1)) k))) := by
                  simp only [
                    pow_succ, Equiv.Perm.coe_mul, Function.comp_apply,
                    Module.End.mul_apply
                  ]
          _ = (T ^ n) (T (P (σ ((σ ^ n) k)) * X * P (σ ((σ ^ n) k)))) := by
                  simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
          _ = (T ^ n) (P ((σ ^ n) k) * T X * P ((σ ^ n) k)) := by
                  congr 1
                  calc
                    T (P (σ ((σ ^ n) k)) * X * P (σ ((σ ^ n) k))
                        ) = T (P (σ ((σ ^ n) k)) * X) * T (P (σ ((σ ^ n) k))) := by
                              exact hMulRight (σ ((σ ^ n) k)) (P (σ ((σ ^ n) k)) * X)
                    _ = (T (P (σ ((σ ^ n) k))) * T X) * T (P (σ ((σ ^ n) k))) := by
                          rw [hMulLeft (σ ((σ ^ n) k)) X]
                    _ = P ((σ ^ n) k) * T X * P ((σ ^ n) k) := by
                          rw [hperm ((σ ^ n) k)]
          _ = P k * ((T ^ n) (T X)) * P k := ih k (T X)
          _ = P k * ((T ^ (n + 1)) X) * P k := by simp only [pow_succ, Module.End.mul_apply]
  intro k X
  have hmain :
      (T ^ orderOf σ) (P ((σ ^ orderOf σ) k) * X * P ((σ ^ orderOf σ) k)) =
        P k * ((T ^ orderOf σ) X) * P k := hstep (orderOf σ) k X
  have hσ : (σ ^ orderOf σ) = 1 := pow_orderOf_eq_one σ
  have hmk : (T ^ orderOf σ) (P k * X * P k) = P k * ((T ^ orderOf σ) X) * P k := by
    simpa [hσ] using hmain
  calc
    P k * (T ^ orderOf σ) (P k * X * P k) * P k
        = P k * (P k * ((T ^ orderOf σ) X) * P k) * P k := by rw [hmk]
    _ = (P k * P k) * ((T ^ orderOf σ) X) * (P k * P k) := by
            simp only [Matrix.mul_assoc]
    _ = P k * ((T ^ orderOf σ) X) * P k := by
            simp only [(hPproj k).2, Matrix.mul_assoc]
    _ = (T ^ orderOf σ) (P k * X * P k) := by rw [hmk]

end PermutationBlockStructure

end PrimitivityOfSectors
