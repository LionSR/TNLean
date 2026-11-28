/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicBlockedGroundSpace
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalityChain
import TNLean.MPS.CanonicalForm.Periodic.Overlap.SelfOverlapNonrep
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PrimitiveSectorRepresentatives

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
Lemma lem:blocking-arbitrary, lines 434--451; Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435,
and the support spaces of Section 3, lines 1504--1538.

**Local fix (powered roots):** The compressed peripheral period is
\(m/\gcd(m,p)\), as recorded in
docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex. Under \(m\mid p\)
this corrected period is one.

## Primitive sectors with their cyclic support projections

A normalized periodic tensor has a cyclic isometric resolution whose blocked
sectors are normalized primitive tensors with faithful invariant matrices.
Different cyclic sectors are inequivalent up to similarity and phase.
The resolution retains both block intertwiners, so it identifies literal
word contractions as well as periodic matrix product vectors.

The projection labels here follow the inverse convention
\(P_{u+1}A_i=A_iP_u\). Replacing the label by its negative gives
the word-degree convention \(P_uA_i=A_iP_{u+1}\).

Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag;
Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675.

It also contains the following results.

* `MPSTensor.IsPeriodic.exists_inequivalent_primitive_groundStatePresentation_of_dvd`,
  `MPSTensor.IsPeriodic.exists_inequivalent_primitive_groundStatePresentation`: inequivalent
  primitive presentations of periodically blocked local spaces.
-/

open MPTensor

section PeriodicPrimitiveGroundSpace

section

open scoped ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D m : ℕ}

/-- A period-one normalized irreducible tensor has primitive fixed-point
witnesses with a faithful invariant matrix. This is the finite-dimensional
Perron--Frobenius step underlying the normalization in Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435. -/
theorem exists_hasComplementaryFixedPointGap_of_isPeriodic_one [NeZero D] {A : MPTensor α (Fin D)}
    (hA : IsPeriodic 1 A) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.HasComplementaryFixedPointGap A ρ ∧ ρ.PosDef := by
  obtain ⟨hIrr, hTP, hPrim⟩ := (IsPeriodic.one_iff_primitive A).1 hA
  obtain ⟨ρ, hP⟩ :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  exact ⟨ρ, hP, hP.posDef_of_isIrreducibleFamily hIrr⟩

/-- Blocking a periodic tensor by any positive multiple of its period gives
primitive sectors with positive bond dimensions and faithful invariant matrices.
Their direct sum has the exact blocked local support space at every length.
The sector dimensions sum to the original bond dimension. Source: DCCSP17,
arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451;
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem IsPeriodic.exists_hasComplementaryFixedPointGap_groundSpaceDecomposition_of_dvd
    {A : MPTensor α (Fin D)} (hA : IsPeriodic m A) (p : ℕ)
    (hp : 0 < p) (hdiv : m ∣ p) :
    ∃ (dim : Fin (m.gcd p) → ℕ) (hdim : ∀ a, 0 < dim a),
      let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
      ∃ (B : (a : Fin (m.gcd p)) → MPTensor (Fin p → α) (Fin (dim a)))
        (ρ : (a : Fin (m.gcd p)) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
      (∑ a, dim a) = D ∧
      (∀ a, Kraus.HasComplementaryFixedPointGap (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
      (∀ N, ((groundSpace (Kraus.block A p) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) =
        ((groundSpace (toTensorFromBlocks (μ := fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap)) := by
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
  choose ρ hP hρ using fun a => exists_hasComplementaryFixedPointGap_of_isPeriodic_one (hOne a)
  exact ⟨dim, hdim, B, ρ, htotal, hP, hρ, hGS⟩

/-- Blocking by the period gives exactly that many primitive sectors,
retaining the original blocked support spaces for all lengths, including zero.
Source: DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary,
lines 434--451, specialized to the block length equal to the period. -/
theorem IsPeriodic.exists_hasComplementaryFixedPointGap_groundSpaceDecomposition
    {A : MPTensor α (Fin D)} (hA : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (hdim : ∀ a, 0 < dim a),
      let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
      ∃ (B : (a : Fin m) → MPTensor (Fin m → α) (Fin (dim a)))
        (ρ : (a : Fin m) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
      (∑ a, dim a) = D ∧
      (∀ a, Kraus.HasComplementaryFixedPointGap (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
      (∀ N, ((groundSpace (Kraus.block A m) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) =
        ((groundSpace (toTensorFromBlocks (μ := fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap)) := by
  have h := hA.exists_hasComplementaryFixedPointGap_groundSpaceDecomposition_of_dvd
    m hA.period_pos (dvd_refl m)
  rw [Nat.gcd_self] at h
  exact h

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {α : Type*} [Fintype α] [DecidableEq α] {D m : ℕ}

/-- Periodicity supplies a primitive faithful inequivalent cyclic sector
resolution, including its support projections and both rectangular block
intertwiners. Every sector dimension is positive.
Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag;
Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPeriodic.exists_cyclic_primitive_sector_resolution
    {A : MPTensor α (Fin D)} (hA : IsPeriodic m A) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (dim : Fin m → ℕ) (hdim : ∀ j, 0 < dim j),
      let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
      ∃ (B : (j : Fin m) → MPTensor (Fin m → α) (Fin (dim j)))
        (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
        (V : (j : Fin m) → Matrix (Fin D) (Fin (dim j)) ℂ)
        (ρ : (j : Fin m) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
        (∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
        BlocksNotGaugePhaseEquiv B ∧
        (∀ j, IsOrthogonalProjection (P j)) ∧ (∑ j, P j) = 1 ∧
        (∀ j i, P (j + 1) * A i = A i * P j) ∧
        (∀ j, (V j)ᴴ * V j = 1) ∧ (∀ j, V j * (V j)ᴴ = P j) ∧
        (∀ j i, Kraus.block A m i * V j = V j * B j i) ∧
        (∀ j i, (V j)ᴴ * Kraus.block A m i = B j i * (V j)ᴴ) := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨dim, B, P, φ, V, hTP, hMPV, hproj, hsum, hcycle, hComm, hTrace,
    hTransfer, hMul, hStar, hdim, hLetter, hiso, hV, hEmbed⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hA
  have hcycle' : ∀ k : Fin m,
      Kraus.transferMap (fun i => (A i)ᴴ) (P (k + 1)) = P k := by
    intro k
    simpa [cyclicNextOfPos, Fin.add_def] using hcycle k
  have hData : IsCyclicSectorDecomp A B :=
    ⟨P, φ, hproj, hsum, hcycle', hComm, hTrace, hTransfer, hMul, hStar⟩
  let : ∀ j, NeZero (dim j) := fun j => ⟨hdim j⟩
  have hPrim (j : Fin m) :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp A hA B hTP hMPV hData j (hdim j)
  have hOne (j : Fin m) : IsPeriodic 1 (B j) :=
    (IsPeriodic.one_iff_primitive (B j)).2 ⟨(hPrim j).2, hTP j, (hPrim j).1⟩
  have hDistinct : BlocksNotGaugePhaseEquiv B := fun j k hjk e =>
    sectorBlocks_not_gaugePhaseEquiv_of_ne A hA B hTP hMPV hproj hsum hcycle'
      hComm hTrace hTransfer hMul hStar hLetter hiso hV hEmbed hdim hjk e
  have hShift : ∀ j i, P (j + 1) * A i = A i * P j :=
    offDiag_shift_of_adjoint_cyclic_shift A hA.leftCanonical hproj hcycle'
  choose ρ hP hρ using fun j => exists_hasComplementaryFixedPointGap_of_isPeriodic_one (hOne j)
  have hCorner (j : Fin m) (i : Fin m → α) :
      V j * B j i * (V j)ᴴ = P j * Kraus.block A m i * P j :=
    (hEmbed j (B j i)).symm.trans (hLetter j i)
  have hVPleft (j : Fin m) : (V j)ᴴ * P j = (V j)ᴴ := by
    rw [← hV, ← Matrix.mul_assoc, hiso, Matrix.one_mul]
  have hVPright (j : Fin m) : P j * V j = V j := by
    rw [← hV, Matrix.mul_assoc, hiso, Matrix.mul_one]
  have hInt (j : Fin m) (i : Fin m → α) :
      Kraus.block A m i * V j = V j * B j i := by
    have h := congrArg (fun X => X * V j) (hCorner j i)
    simp only [Matrix.mul_assoc, hiso, Matrix.mul_one, hVPright] at h
    rw [← Matrix.mul_assoc, hComm, Matrix.mul_assoc, hVPright] at h
    exact h.symm
  have hCoInt (j : Fin m) (i : Fin m → α) :
      (V j)ᴴ * Kraus.block A m i = B j i * (V j)ᴴ := by
    have h := congrArg (fun X => (V j)ᴴ * X) (hCorner j i)
    simp only [← Matrix.mul_assoc, hiso, Matrix.one_mul, hVPleft] at h
    rw [Matrix.mul_assoc, ← hComm, ← Matrix.mul_assoc, hVPleft] at h
    exact h.symm
  exact ⟨dim, (fun j => Nat.pos_of_ne_zero (hdim j)), B, P, V, ρ, hP, hρ,
    hDistinct, hproj, hsum, hShift, hiso, hV, hInt, hCoInt⟩
end MPSTensor

end

end PeriodicPrimitiveGroundSpace

section PeriodicGroundStatePresentation

/-!
## Inequivalent primitive presentations of periodically blocked local spaces

Blocking a periodic tensor by a positive multiple of its period gives a
finite primitive family with faithful invariant matrices. Selecting one
representative of each gauge-phase class produces a nonempty, pairwise
inequivalent family with the same joint local MPS space at every chain
length, including zero. The representative tensors and invariant matrices
are inherited from the compressed sectors.

These are finite support identities. They require neither supplied sector
inequivalence nor positivity assumptions on ambient dimensions. The positive
sector dimensions are obtained from the periodic compression. Their role in
quasi-local state classification is separate from this finite presentation.

Source: DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary,
lines 434--451; CPSV16, arXiv:1606.00608, Proposition prop:char-BNT
and Theorem thm1; Nachtergaele, arXiv:cond-mat/9410110,
Section 3 and Lemma disjoint.

**Local fix (powered roots):** The period-removing compression uses the
corrected peripheral period documented in
docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D m : ℕ}

/-- A periodic tensor, blocked by any positive multiple of its period,
admits a nonempty finite family of pairwise gauge-phase inequivalent primitive
sectors with faithful invariant matrices and the exact same joint support
at every length. No sector inequivalence assumption is supplied.
Source: DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary,
lines 434--451; CPSV16, arXiv:1606.00608, Proposition prop:char-BNT
and Theorem thm1; Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint. -/
theorem IsPeriodic.exists_inequivalent_primitive_groundStatePresentation_of_dvd
    {A : MPTensor α (Fin D)} (hA : IsPeriodic m A) (p : ℕ)
    (hp : 0 < p) (hdiv : m ∣ p) :
    ∃ (g : ℕ), 0 < g ∧
      ∃ (dim : Fin g → ℕ) (hdim : ∀ a, 0 < dim a),
        let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
        ∃ (B : (a : Fin g) → MPTensor (Fin p → α) (Fin (dim a)))
          (ρ : (a : Fin g) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
          (∀ a, Kraus.HasComplementaryFixedPointGap (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
          BlocksNotGaugePhaseEquiv B ∧
          (∀ N, ((groundSpace (Kraus.block A p) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
              =
            ((groundSpace (toTensorFromBlocks (μ := fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ
                _).symm.toLinearMap)) := by
  classical
  obtain ⟨dim, hdim, B, ρ, _htotal, hP, hρ, hGS⟩ :=
    hA.exists_hasComplementaryFixedPointGap_groundSpaceDecomposition_of_dvd p hp hdiv
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  obtain ⟨g, sel, _hsel, hpos, hP', hρ', hDistinct, hCover, hGS'⟩ :=
    exists_primitive_sector_representatives (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ
  have hr : 0 < m.gcd p := by
    rw [Nat.gcd_eq_left hdiv]
    exact hA.period_pos
  obtain ⟨k, _e, _he⟩ := hCover ⟨0, hr⟩
  exact ⟨g, Fin.pos k, (fun k => dim (sel k)), hpos,
    (fun k => B (sel k)), (fun k => ρ (sel k)), hP', hρ', hDistinct,
    fun N => (hGS N).trans (hGS' N)⟩

/-- Blocking a periodic tensor by its period gives a nonempty primitive
sector presentation with faithful invariant matrices, derived pairwise
inequivalence, and exact support at every chain length, including zero.
Source: DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary;
CPSV16, arXiv:1606.00608, Proposition prop:char-BNT and Theorem thm1. -/
theorem IsPeriodic.exists_inequivalent_primitive_groundStatePresentation
    {A : MPTensor α (Fin D)} (hA : IsPeriodic m A) :
    ∃ (g : ℕ), 0 < g ∧
      ∃ (dim : Fin g → ℕ) (hdim : ∀ a, 0 < dim a),
        let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
        ∃ (B : (a : Fin g) → MPTensor (Fin m → α) (Fin (dim a)))
          (ρ : (a : Fin g) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ),
          (∀ a, Kraus.HasComplementaryFixedPointGap (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
          BlocksNotGaugePhaseEquiv B ∧
          (∀ N, ((groundSpace (Kraus.block A m) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
              =
            ((groundSpace (toTensorFromBlocks (μ := fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ
                _).symm.toLinearMap)) := by
  exact hA.exists_inequivalent_primitive_groundStatePresentation_of_dvd
    m hA.period_pos (dvd_refl m)

end MPSTensor

end PeriodicGroundStatePresentation
