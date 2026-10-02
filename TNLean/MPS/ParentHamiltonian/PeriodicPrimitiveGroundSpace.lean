/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockedGroundSpace
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain

/-!
# Primitive sectors and exact local support after removal of the period

For a periodic tensor of period \(m\), blocking by a positive multiple \(p\)
of \(m\) gives period-one compressed sectors. Their trace-preserving
normalization, irreducibility, and peripheral primitivity supply primitive
fixed-point data with faithful invariant matrices. The compressed tensors
themselves form the primitive family, whose direct sum retains the exact
local MPS space on every number of blocked sites, including zero.

The sector dimensions are positive and sum to the original bond dimension.
The proof requires no inequivalence assumption on the compressed sectors.
Blocking by \(m\) itself gives a family indexed by \(m\) sectors.

Source: De las Cuevas--Cirac--Schuch--Perez-Garcia, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451; Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435,
and the support spaces of Section 3, lines 1504--1538.

**Local fix (powered roots):** The compressed peripheral period is
\(m/\gcd(m,p)\), as recorded in
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`. Under \(m\mid p\)
this corrected period is one.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d D m : ℕ}

/-- A period-one normalized irreducible tensor has primitive fixed-point
witnesses with a faithful invariant matrix. This is the finite-dimensional
Perron--Frobenius step underlying the normalization in Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435. -/
theorem exists_isPrimitiveMPS_of_isPeriodic_one [NeZero D] {A : MPSTensor d D}
    (hA : IsPeriodic 1 A) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, IsPrimitiveMPS A ρ ∧ ρ.PosDef := by
  obtain ⟨hIrr, hTP, hPrim⟩ := (IsPeriodic.one_iff_primitive A).1 hA
  obtain ⟨ρ, hP⟩ :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  exact ⟨ρ, hP, hP.posDef_of_isIrreducibleFamily hIrr⟩

/-- Blocking a periodic tensor by any positive multiple of its period gives
primitive sectors with positive bond dimensions and faithful invariant matrices.
Their direct sum has the exact blocked local support space at every length.
The sector dimensions sum to the original bond dimension. Source: DCCSP17,
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451;
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem IsPeriodic.exists_isPrimitiveMPS_groundSpaceDecomposition_of_dvd
    {A : MPSTensor d D} (hA : IsPeriodic m A) (p : ℕ)
    (hp : 0 < p) (hdiv : m ∣ p) :
    ∃ (dim : Fin (m.gcd p) → ℕ) (hdim : ∀ a, 0 < dim a),
      let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
      ∃ (B : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
        (ρ : (a : Fin (m.gcd p)) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
      (∑ a, dim a) = D ∧
      (∀ a, IsPrimitiveMPS (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
      (∀ N, groundSpaceES (blockTensor A p) N =
        groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) B) N) := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, dim, B, V, _hproj, _hsum, _hne, _hshift, hdim, htotal, _hcan,
    _hiso, _hV, _hC, _hInt, hGS, hPeriod⟩ :=
    hA.exists_stepOrbit_groundSpaceDecomposition p hp
  have hquot : m / m.gcd p = 1 := by
    rw [Nat.gcd_eq_left hdiv, Nat.div_self hA.period_pos]
  have hOne (a : Fin (m.gcd p)) : IsPeriodic 1 (B a) := by
    simpa only [hquot] using hPeriod a
  let : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
  choose ρ hP hρ using fun a => exists_isPrimitiveMPS_of_isPeriodic_one (hOne a)
  exact ⟨dim, hdim, B, ρ, htotal, hP, hρ, hGS⟩

/-- Blocking by the period gives exactly that many primitive sectors,
retaining the original blocked support spaces for all lengths, including zero.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451, specialized to the block length equal to the period. -/
theorem IsPeriodic.exists_isPrimitiveMPS_groundSpaceDecomposition
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (hdim : ∀ a, 0 < dim a),
      let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
      ∃ (B : (a : Fin m) → MPSTensor (blockPhysDim d m) (dim a))
        (ρ : (a : Fin m) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
      (∑ a, dim a) = D ∧
      (∀ a, IsPrimitiveMPS (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
      (∀ N, groundSpaceES (blockTensor A m) N =
        groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) B) N) := by
  have h := hA.exists_isPrimitiveMPS_groundSpaceDecomposition_of_dvd
    m hA.period_pos (dvd_refl m)
  rw [Nat.gcd_self] at h
  exact h

end MPSTensor
