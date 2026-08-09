/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.ClosureFixedPointKraus
import TNLean.Channel.Schwarz.MultiplicativeDomainPowers
import TNLean.Channel.Peripheral.Spectrum
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Peripheral eigenvalues form a cyclic group

For an irreducible unital Kraus map with a positive definite adjoint-fixed point,
we prove:

1. **Product closure**: if \(\mu\) and \(\nu\) are peripheral eigenvalues,
   then \(\mu\nu\) is peripheral.
2. **Cyclic group characterization**: the peripheral spectrum is
   \(\{\gamma^j\mid 0\leq j<m\}\), where \(m\) is its cardinality and
   \(\gamma\) is a primitive \(m\)-th root of unity.

The product closure proof uses:
- KS equality for peripheral eigenvectors (`ks_equality_of_peripheral_eigenvector_of_fixedPoint`)
- Right multiplicative domain (`multiplicative_domain_right`)
- Irreducibility → peripheral eigenvectors are invertible
  (via `posDef_of_posSemidef_fixedPoint_irreducible_cp`)

The cyclic characterization uses product and power closure to show directly
that every peripheral eigenvalue is an \(m\)-th root of unity, where \(m\) is
the number of peripheral eigenvalues. A primitive \(m\)-th root and a cardinality
comparison then give the required parametrization.

**Scope restriction (complete positivity and adjoint fixed point):** Wolf
Theorem 6.6 assumes an irreducible positive unital Schwarz map. This module
assumes a finite Kraus family and a positive-definite fixed point of its adjoint,
and proves the cyclicity conclusion in item (1) without the order bound. See
`docs/paper-gaps/wolf_thm6_6_kraus_scope.tex`.

## References

- [M. Wolf, *Quantum Channels & Operations*, Theorem 6.6]
- [Evans–Hoegh-Krohn, *Spectral properties of positive maps on C*-algebras*]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

/-!
## Invertibility of peripheral eigenvectors

This file reuses `isUnit_peripheral_eigenvector` from
`TNLean/Channel/Peripheral/ClosureFixedPointKraus.lean`.
-/

/-!
## Product closure of peripheral eigenvalues

The key new result: for an irreducible unital Kraus map with a PD adjoint-fixed point,
the peripheral eigenvalues are closed under multiplication.
-/

/-- **Peripheral eigenvalues are closed under multiplication** for irreducible unital
Kraus maps with a PD adjoint-fixed point.

Proof: Take eigenvectors `X, Y` for `μ, ν`. The KS equality at `X` gives
`E(Y * X) = E(Y) * E(X) = (ν * μ) • (Y * X)`. Since `X, Y` are units
(by `isUnit_peripheral_eigenvector`), `Y * X ≠ 0`, so `μ * ν` is an
eigenvalue with norm 1. This is the multiplication-closure step in the
finite-Kraus specialization of Wolf Theorem 6.6(1).

**Scope restriction (complete positivity and adjoint fixed point):** Wolf
Theorem 6.6 assumes an irreducible positive unital Schwarz map, whereas this
declaration assumes a finite Kraus family and a positive-definite fixed point of
its adjoint. See `docs/paper-gaps/wolf_thm6_6_kraus_scope.tex`. -/
theorem peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (Kraus.mapLM K)) :
    ∀ μ ν : ℂ,
      μ ∈ peripheralEigenvalues (Kraus.mapLM K) →
      ν ∈ peripheralEigenvalues (Kraus.mapLM K) →
        μ * ν ∈ peripheralEigenvalues (Kraus.mapLM K) := by
  classical
  intro μ ν hμ hν
  rcases hμ with ⟨hμ_eig, hμ_norm⟩
  rcases hν with ⟨hν_eig, hν_norm⟩
  -- Extract nonzero eigenvectors.
  rcases hμ_eig.exists_hasEigenvector with ⟨X, hX_eigvec⟩
  rcases hν_eig.exists_hasEigenvector with ⟨Y, hY_eigvec⟩
  have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX_eigvec).2
  have hY_ne : Y ≠ 0 := (Module.End.hasEigenvector_iff.mp hY_eigvec).2
  have hEig_X : Kraus.mapLM K X = μ • X :=
    Module.End.mem_eigenspace_iff.1 (Module.End.hasEigenvector_iff.mp hX_eigvec).1
  have hEig_Y : Kraus.mapLM K Y = ν • Y :=
    Module.End.mem_eigenspace_iff.1 (Module.End.hasEigenvector_iff.mp hY_eigvec).1
  -- KS equality at X.
  have hEig_X_map : Kraus.map K X = μ • X := by
    simpa [Kraus.mapLM_apply] using hEig_X
  have h_unital' : Kraus.IsUnital K := h_unital.toIsUnital
  have hKS_X_map :
      Kraus.map K (Xᴴ * X) = (Kraus.map K X)ᴴ * Kraus.map K X :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K h_unital' hρ hfix X μ hEig_X_map hμ_norm
  have hKS_X :
      KadisonSchwarz.krausMap (d := d) (D := D) K (Xᴴ * X)
        = (KadisonSchwarz.krausMap (d := d) (D := D) K X)ᴴ
            * KadisonSchwarz.krausMap (d := d) (D := D) K X := by
    simpa [Kraus.map, KadisonSchwarz.krausMap] using hKS_X_map
  -- Multiplicative domain: E(Y * X) = E(Y) * E(X).
  have hMD :
      KadisonSchwarz.krausMap (d := d) (D := D) K (Y * X) =
        KadisonSchwarz.krausMap (d := d) (D := D) K Y *
          KadisonSchwarz.krausMap (d := d) (D := D) K X :=
    KadisonSchwarz.multiplicative_domain_right K h_unital X hKS_X Y
  -- Express the multiplicative-domain identity through `mapLM`.
  have hMD_mapLM :
      Kraus.mapLM K (Y * X) =
        Kraus.mapLM K Y *
          Kraus.mapLM K X := by
    simpa [Kraus.mapLM_apply, KadisonSchwarz.krausMap] using hMD
  -- Compute: E(Y * X) = (ν * μ) • (Y * X).
  have hEig_prod : Kraus.mapLM K (Y * X) = (ν * μ) • (Y * X) := by
    calc
      Kraus.mapLM K (Y * X)
          = Kraus.mapLM K Y *
              Kraus.mapLM K X := hMD_mapLM
      _ = (ν • Y) * (μ • X) := by rw [hEig_Y, hEig_X]
      _ = (ν * μ) • (Y * X) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Y * X ≠ 0 since X, Y are units.
  have hX_unit : IsUnit X :=
    isUnit_peripheral_eigenvector K h_unital ρ hρ hfix hIrr X μ hEig_X hμ_norm hX_ne
  have hY_unit : IsUnit Y :=
    isUnit_peripheral_eigenvector K h_unital ρ hρ hfix hIrr Y ν hEig_Y hν_norm hY_ne
  have hYX_ne : Y * X ≠ 0 := (hY_unit.mul hX_unit).ne_zero
  -- μ * ν = ν * μ is a peripheral eigenvalue.
  have hEig_prod' : Kraus.mapLM K (Y * X) = (μ * ν) • (Y * X) := by
    rw [mul_comm μ ν]; exact hEig_prod
  have hHasEig : Module.End.HasEigenvalue
      (Kraus.mapLM K) (μ * ν) := by
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr hEig_prod', hYX_ne⟩)
  have hNorm : ‖μ * ν‖ = 1 := by
    rw [norm_mul, hμ_norm, hν_norm, mul_one]
  exact ⟨hHasEig, hNorm⟩

/-!
## Peripheral eigenvalues form a cyclic group of roots of unity

Using product closure, power closure, and the root-of-unity property, we show
\(\operatorname{peripheralEigenvalues}(E)=\{\gamma^j\mid j\in\mathrm{Fin}(m)\}\),
where \(m\) is the cardinality of the peripheral eigenvalue set and \(\gamma\)
is a primitive \(m\)-th root of unity.

The proof strategy:
1. The peripheral set \(S\) is closed under products, powers, and inverses.
2. Multiplication by any \(\mu\in S\) permutes \(S\), so a product comparison
   gives \(\mu^{|S|}=1\).
3. Choose a primitive \(|S|\)-th root \(\gamma\) using
   `Complex.isPrimitiveRoot_exp`.
4. Compare cardinalities with the set of \(|S|\)-th roots to obtain
   \(S=\{\gamma^j\mid j\in\mathrm{Fin}(|S|)\}\).
-/

/-- The peripheral eigenvalues of an irreducible unital Kraus map with a PD
adjoint-fixed point form a cyclic group of roots of unity.

Specifically, if \(m\) is the number of peripheral eigenvalues, there exists a
primitive \(m\)-th root of unity \(\gamma\) such that the peripheral spectrum is
\(\{\gamma^j\mid 0\leq j<m\}\).

This is the finite-Kraus specialization of the cyclicity conclusion in Wolf
Theorem 6.6(1), and it connects the channel-level peripheral spectrum to the
cyclic decomposition of MPS tensors.

**Scope restriction (complete positivity and adjoint fixed point):** Wolf
Theorem 6.6 assumes an irreducible positive unital Schwarz map, whereas this
declaration assumes a finite Kraus family and a positive-definite fixed point of
its adjoint. See `docs/paper-gaps/wolf_thm6_6_kraus_scope.tex`.

The proof uses:
- Product closure (`peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint`)
- Power closure (`peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint`)
- Roots of unity property (`peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint`)
- `Complex.isPrimitiveRoot_exp` and `IsPrimitiveRoot.card_nthRootsFinset`
- `IsPrimitiveRoot.eq_pow_of_pow_eq_one`: elements of order dividing \(m\) are
  powers of a primitive \(m\)-th root -/
theorem peripheralEigenvalues_eq_range_primitiveRoot [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (Kraus.mapLM K)) :
    let E := Kraus.mapLM K
    let hfin := peripheralEigenvalues_finite (f := E)
    let m := hfin.toFinset.card
    0 < m ∧
    ∃ (γ : ℂ), IsPrimitiveRoot γ m ∧
      peripheralEigenvalues E = Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
  set E := Kraus.mapLM K with E_def
  set hfin := peripheralEigenvalues_finite (f := E) with hfin_def
  set S := hfin.toFinset with S_def
  set m := S.card with m_def
  -- m ≥ 1: the identity map E(I) = I gives 1 ∈ peripheralEigenvalues E.
  have h1_mem : (1 : ℂ) ∈ peripheralEigenvalues E := by
    refine ⟨?_, by simp⟩
    -- E is unital: E(I) = I → 1 is an eigenvalue.
    have hfix_one : E (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
      simp only [E_def, Kraus.mapLM_apply, Kraus.map_apply]
      convert h_unital using 1
      simp [KadisonSchwarz.IsUnitalKraus]
    have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
    have hone_ne : (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
      intro h
      have hentry := congrArg
        (fun M : Matrix (Fin D) (Fin D) ℂ => M ⟨0, hDpos⟩ ⟨0, hDpos⟩) h
      simp at hentry
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (by simp [hfix_one]), hone_ne⟩)
  have h1_finset : (1 : ℂ) ∈ S := hfin.mem_toFinset.mpr h1_mem
  have hm_pos : 0 < m := Finset.card_pos.mpr ⟨1, h1_finset⟩
  refine ⟨hm_pos, ?_⟩
  -- The peripheral eigenvalues are all roots of unity with a common bound.
  have hroot : ∀ μ ∈ S, ∃ p : ℕ, 0 < p ∧ μ ^ p = 1 := by
    intro μ hμ
    exact peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint
      K h_unital ρ hρ hfix hIrr μ (hfin.mem_toFinset.mp hμ)
  -- Product closure.
  have hmul : ∀ μ ν, μ ∈ S → ν ∈ S → μ * ν ∈ S := by
    intro μ ν hμ hν
    exact hfin.mem_toFinset.mpr
      (peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint
        K h_unital ρ hρ hfix hIrr μ ν (hfin.mem_toFinset.mp hμ) (hfin.mem_toFinset.mp hν))
  -- Power closure.
  have hpow : ∀ μ, μ ∈ S → ∀ n : ℕ, μ ^ n ∈ S := by
    intro μ hμ n
    exact hfin.mem_toFinset.mpr
      (peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint
        K h_unital ρ hρ hfix hIrr μ (hfin.mem_toFinset.mp hμ) n)
  -- Inverse closure: μ ∈ S → μ⁻¹ ∈ S (since μ^(ord-1) = μ⁻¹ for roots of unity).
  have hinv : ∀ μ, μ ∈ S → μ⁻¹ ∈ S := by
    intro μ hμ
    obtain ⟨p, hp_pos, hp_one⟩ := hroot μ hμ
    -- μ⁻¹ = μ^(p-1) since μ^p = 1.
    have hμ_ne : μ ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.pos_iff_ne_zero.mp hp_pos)] at hp_one
      exact zero_ne_one hp_one
    have : μ⁻¹ = μ ^ (p - 1) := by
      have key : μ ^ (p - 1) * μ = 1 := by
        have := hp_one
        conv at this => rw [show p = (p - 1) + 1 from
          (Nat.succ_pred_eq_of_pos hp_pos).symm, pow_succ]
        exact this
      have key2 : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ_ne
      exact mul_right_cancel₀ hμ_ne (by rw [key, key2])
    rw [this]
    exact hpow μ hμ (p - 1)
  -- Lagrange step: every element of S satisfies μ^m = 1.
  -- Proof: for μ ∈ S, the bijection ν ↦ μ * ν permutes S, so ∏ S = μ^m * ∏ S.
  -- Cancelling the nonzero product gives μ^m = 1.
  have hall_mth_root : ∀ μ, μ ∈ S → μ ^ m = 1 := by
    intro μ hμ
    -- Every element of S is nonzero (root of unity).
    have hne : ∀ ν, ν ∈ S → ν ≠ 0 := by
      intro ν hν habs
      obtain ⟨p, hp_pos, hp_one⟩ := hroot ν hν
      rw [habs, zero_pow (Nat.pos_iff_ne_zero.mp hp_pos)] at hp_one
      exact zero_ne_one hp_one
    have hμ_ne : μ ≠ 0 := hne μ hμ
    have hP_ne : ∏ ν ∈ S, ν ≠ 0 := prod_ne_zero_iff.mpr fun ν hν => hne ν hν
    -- The bijection ν ↦ μ * ν permutes S, so ∏_{ν ∈ S} (μ * ν) = ∏_{ν ∈ S} ν.
    have hperm : ∏ ν ∈ S, (μ * ν) = ∏ ν ∈ S, ν :=
      Finset.prod_bij' (fun ν _ => μ * ν) (fun ν _ => μ⁻¹ * ν)
        (fun ν hν => hmul μ ν hμ hν) (fun ν hν => hmul _ ν (hinv μ hμ) hν)
        (fun ν _ => inv_mul_cancel_left₀ hμ_ne ν)
        (fun ν _ => mul_inv_cancel_left₀ hμ_ne ν)
        (fun _ _ => rfl)
    -- Also ∏_{ν ∈ S} (μ * ν) = μ^m * ∏_{ν ∈ S} ν (by distributivity + prod_const).
    have hsplit : ∏ ν ∈ S, (μ * ν) = μ ^ m * ∏ ν ∈ S, ν := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    -- Combine: μ^m * P = P, cancel P ≠ 0 to get μ^m = 1.
    have h_eq : μ ^ m * ∏ ν ∈ S, ν = 1 * ∏ ν ∈ S, ν := by
      rw [one_mul]; exact hsplit.symm.trans hperm
    exact mul_right_cancel₀ hP_ne h_eq
  -- With all elements being m-th roots, use IsPrimitiveRoot to get the range form.
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
  haveI : NeZero m := ⟨hm_ne⟩
  set γ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
  have hγ : IsPrimitiveRoot γ m := Complex.isPrimitiveRoot_exp m hm_ne
  refine ⟨γ, hγ, ?_⟩
  -- Show: peripheralEigenvalues E = Set.range (fun j : Fin m => γ ^ (j : ℕ))
  ext μ
  constructor
  · -- (→) μ ∈ peripheralEigenvalues E → μ ∈ range
    intro hμ
    have hμS : μ ∈ S := hfin.mem_toFinset.mpr hμ
    have hμm : μ ^ m = 1 := hall_mth_root μ hμS
    obtain ⟨i, hi_lt, hi_eq⟩ := hγ.eq_pow_of_pow_eq_one hμm
    exact ⟨⟨i, hi_lt⟩, hi_eq⟩
  · -- (←) μ ∈ range → μ ∈ peripheralEigenvalues E
    rintro ⟨j, rfl⟩
    -- S ⊆ {m-th roots of unity} (from hall_mth_root) and |S| = m = |{m-th roots}|
    -- (from IsPrimitiveRoot.card_nthRootsFinset), so S = {m-th roots}, hence γ ∈ S.
    have hγ_mem : γ ∈ S := by
      have hS_sub : S ⊆ Polynomial.nthRootsFinset m (1 : ℂ) := by
        intro ν hν
        exact (Polynomial.mem_nthRootsFinset hm_pos (1 : ℂ)).mpr (hall_mth_root ν hν)
      have hcard_roots : #(Polynomial.nthRootsFinset m (1 : ℂ)) = m :=
        hγ.card_nthRootsFinset
      have hS_eq : S = Polynomial.nthRootsFinset m (1 : ℂ) :=
        Finset.eq_of_subset_of_card_le hS_sub (by omega)
      rw [hS_eq]
      exact (Polynomial.mem_nthRootsFinset hm_pos (1 : ℂ)).mpr hγ.pow_eq_one
    exact hfin.mem_toFinset.mp (hpow γ hγ_mem j)

end Kraus
