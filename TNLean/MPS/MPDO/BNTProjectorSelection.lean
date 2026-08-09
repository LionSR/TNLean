/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.MPDO.BNTSourceSectorProjectors
import TNLean.MPS.MPDO.CommonWeightAbsorption
import TNLean.MPS.MPDO.SitewisePhysicalMatrix

/-!
# Local selection by the BNT sector projectors

The projectors obtained from the Hayashi--Markov sectors select the physical
support of the corresponding basis-of-normal-tensors representative.  More
precisely, the physical slice of normal sector `i` has no block from `P_s` to
`P_t` unless `s = t = i`.

This is equation `PjKiPj` in arXiv:1606.00608, Appendix C.2.  It is the local
statement used immediately afterward to derive `generateMPDO` and the
positive-length density-operator compression formula `sigmaNKj`.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1680--1759.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d g : ℕ} {dim : Fin g → ℕ}

open PhysicalSectorFactorization

/-- Distinct Hayashi sectors give a zero physical-slice corner.

Source: arXiv:1606.00608, Appendix C.2, equation `Qks`, lines 1698--1735. -/
theorem sectorProjection_mul_physicalSlice_mul_sectorProjection_eq_zero_of_ne
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g)
    (β α : Fin (dim s)) {k l : Fin hη.m} (hkl : k ≠ l) :
    hη.sectorProjection k * physicalSlice (K s) β α *
        hη.sectorProjection l = 0 := by
  obtain ⟨β₃, α₁, hm⟩ := Matrix.exists_entry_ne_zero_of_ne_zero _ (hR s)
  apply EtaStructure.sectorProjection_mul_mul_sectorProjection_eq_zero_of_block hη
  rintro ⟨aL, aR⟩ ⟨bL, bR⟩
  exact isMPOBlockLeftInverse_bnt_markov_offdiagonal
    hC hρ hη s hm β α hkl aL aR bL bR

/-- An active diagonal Hayashi corner vanishes for every BNT representative
except the representative assigned to that Hayashi sector.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1733--1737. -/
theorem sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_ne_label
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0)
    (k : {k : Fin hη.m // hη.p k ≠ 0}) (s : Fin g)
    (hs : s ≠ bntSectorLabel hC hρ hη hR k)
    (β α : Fin (dim s)) :
    hη.sectorProjection k * physicalSlice (K s) β α *
        hη.sectorProjection k = 0 := by
  apply EtaStructure.sectorProjection_mul_mul_sectorProjection_eq_zero_of_block hη
  intro a b
  by_contra hab
  apply hs
  apply (bntMarkovBlockNonzero_iff_eq_bntSectorLabel
    hC hρ hη hR k s).mp
  refine ⟨β, α, ?_⟩
  intro hzero
  exact hab (congrFun (congrFun hzero a) b)

/-- An inactive Hayashi sector has a zero diagonal corner in every BNT
representative.  The nonzero closing matrix prevents an invisible physical
block from remaining in a zero-weight Markov summand.

Source: arXiv:1606.00608, Appendix C.2, lines 1698--1737, where zero summands
are removed before the projector construction. -/
theorem sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_probability_eq_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g)
    (β α : Fin (dim s)) (k : Fin hη.m) (hk : hη.p k = 0) :
    hη.sectorProjection k * physicalSlice (K s) β α *
        hη.sectorProjection k = 0 := by
  obtain ⟨β₃, α₁, hm⟩ := Matrix.exists_entry_ne_zero_of_ne_zero _ (hR s)
  apply EtaStructure.sectorProjection_mul_mul_sectorProjection_eq_zero_of_block hη
  rintro ⟨aL, aR⟩ ⟨bL, bR⟩
  have hkey := isMPOBlockLeftInverse_bnt_markov_key_formula hC hρ hη
    (⟨s, α₁, β⟩) (⟨s, α, β₃⟩) k k aL aR bL bR
  simp only [dite_true, hk, Complex.ofReal_zero, zero_mul] at hkey
  exact (mul_eq_zero.mp hkey.symm).resolve_left hm

/-- An inactive Hayashi projection annihilates every physical slice on the
left. -/
theorem sectorProjection_mul_physicalSlice_eq_zero_of_probability_eq_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g)
    (β α : Fin (dim s)) (k : Fin hη.m) (hk : hη.p k = 0) :
    hη.sectorProjection k * physicalSlice (K s) β α = 0 := by
  calc
    hη.sectorProjection k * physicalSlice (K s) β α =
        hη.sectorProjection k * physicalSlice (K s) β α * 1 := by simp
    _ = hη.sectorProjection k * physicalSlice (K s) β α *
        (∑ l : Fin hη.m, hη.sectorProjection l) := by
      rw [hη.sum_sectorProjection]
    _ = ∑ l : Fin hη.m,
        hη.sectorProjection k * physicalSlice (K s) β α *
          hη.sectorProjection l := by rw [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      by_cases hkl : k = l
      · subst l
        exact sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_probability_eq_zero
          hC hρ hη hR s β α k hk
      · exact sectorProjection_mul_physicalSlice_mul_sectorProjection_eq_zero_of_ne
          hC hρ hη hR s β α hkl

/-- An active Hayashi projection assigned to another normal sector
annihilates the physical slice on the left. -/
theorem sectorProjection_mul_physicalSlice_eq_zero_of_ne_label
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0)
    (k : {k : Fin hη.m // hη.p k ≠ 0}) (s : Fin g)
    (hs : s ≠ bntSectorLabel hC hρ hη hR k)
    (β α : Fin (dim s)) :
    hη.sectorProjection k * physicalSlice (K s) β α = 0 := by
  calc
    hη.sectorProjection k * physicalSlice (K s) β α =
        hη.sectorProjection k * physicalSlice (K s) β α * 1 := by simp
    _ = hη.sectorProjection k * physicalSlice (K s) β α *
        (∑ l : Fin hη.m, hη.sectorProjection l) := by
      rw [hη.sum_sectorProjection]
    _ = ∑ l : Fin hη.m,
        hη.sectorProjection k * physicalSlice (K s) β α *
          hη.sectorProjection l := by rw [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      by_cases hkl : (k : Fin hη.m) = l
      · subst l
        exact sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_ne_label
          hC hρ hη hR k s hs β α
      · exact sectorProjection_mul_physicalSlice_mul_sectorProjection_eq_zero_of_ne
          hC hρ hη hR s β α hkl

/-- An inactive Hayashi projection annihilates every physical slice on the
right. -/
theorem physicalSlice_mul_sectorProjection_eq_zero_of_probability_eq_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g)
    (β α : Fin (dim s)) (k : Fin hη.m) (hk : hη.p k = 0) :
    physicalSlice (K s) β α * hη.sectorProjection k = 0 := by
  calc
    physicalSlice (K s) β α * hη.sectorProjection k =
        1 * physicalSlice (K s) β α * hη.sectorProjection k := by simp
    _ = (∑ l : Fin hη.m, hη.sectorProjection l) *
        physicalSlice (K s) β α * hη.sectorProjection k := by
      rw [hη.sum_sectorProjection]
    _ = ∑ l : Fin hη.m,
        hη.sectorProjection l * physicalSlice (K s) β α *
          hη.sectorProjection k := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      by_cases hlk : l = k
      · subst l
        exact sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_probability_eq_zero
          hC hρ hη hR s β α k hk
      · exact sectorProjection_mul_physicalSlice_mul_sectorProjection_eq_zero_of_ne
          hC hρ hη hR s β α hlk

/-- An active Hayashi projection assigned to another normal sector
annihilates the physical slice on the right. -/
theorem physicalSlice_mul_sectorProjection_eq_zero_of_ne_label
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0)
    (k : {k : Fin hη.m // hη.p k ≠ 0}) (s : Fin g)
    (hs : s ≠ bntSectorLabel hC hρ hη hR k)
    (β α : Fin (dim s)) :
    physicalSlice (K s) β α * hη.sectorProjection k = 0 := by
  calc
    physicalSlice (K s) β α * hη.sectorProjection k =
        1 * physicalSlice (K s) β α * hη.sectorProjection k := by simp
    _ = (∑ l : Fin hη.m, hη.sectorProjection l) *
        physicalSlice (K s) β α * hη.sectorProjection k := by
      rw [hη.sum_sectorProjection]
    _ = ∑ l : Fin hη.m,
        hη.sectorProjection l * physicalSlice (K s) β α *
          hη.sectorProjection k := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      by_cases hlk : l = (k : Fin hη.m)
      · subst l
        exact sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_ne_label
          hC hρ hη hR k s hs β α
      · exact sectorProjection_mul_physicalSlice_mul_sectorProjection_eq_zero_of_ne
          hC hρ hη hR s β α hlk

/-- The BNT projector labelled by `s` acts as the identity on the left of
the physical slice of representative `s`. -/
theorem bntSectorProjection_mul_physicalSlice_self
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g)
    (β α : Fin (dim s)) :
    bntSectorProjection hC hρ hη hR s * physicalSlice (K s) β α =
      physicalSlice (K s) β α := by
  classical
  have hinactive :
      (∑ k : {k : Fin hη.m // ¬ hη.p k ≠ 0},
        hη.sectorProjection k * physicalSlice (K s) β α) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact sectorProjection_mul_physicalSlice_eq_zero_of_probability_eq_zero
      hC hρ hη hR s β α k (not_ne_iff.mp k.property)
  have hactive :
      (∑ k : {k : Fin hη.m // hη.p k ≠ 0},
        hη.sectorProjection k * physicalSlice (K s) β α) =
          physicalSlice (K s) β α := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (p := fun k : Fin hη.m ↦ hη.p k ≠ 0)
      (fun k ↦ hη.sectorProjection k * physicalSlice (K s) β α)
    rw [hinactive, add_zero] at hsplit
    calc
      _ = ∑ k : Fin hη.m,
          hη.sectorProjection k * physicalSlice (K s) β α := hsplit
      _ = (∑ k : Fin hη.m, hη.sectorProjection k) *
          physicalSlice (K s) β α := by rw [Finset.sum_mul]
      _ = _ := by rw [hη.sum_sectorProjection, Matrix.one_mul]
  rw [bntSectorProjection, Finset.sum_mul]
  calc
    (∑ k : {k : Fin hη.m // hη.p k ≠ 0},
      (if bntSectorLabel hC hρ hη hR k = s then
        hη.sectorProjection k else 0) * physicalSlice (K s) β α) =
        ∑ k : {k : Fin hη.m // hη.p k ≠ 0},
          hη.sectorProjection k * physicalSlice (K s) β α := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : bntSectorLabel hC hρ hη hR k = s
      · simp [hk]
      · rw [if_neg hk, Matrix.zero_mul]
        symm
        exact sectorProjection_mul_physicalSlice_eq_zero_of_ne_label
          hC hρ hη hR k s (Ne.symm hk) β α
    _ = _ := hactive

/-- The BNT projector labelled by `s` acts as the identity on the right of
the physical slice of representative `s`. -/
theorem physicalSlice_mul_bntSectorProjection_self
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g)
    (β α : Fin (dim s)) :
    physicalSlice (K s) β α * bntSectorProjection hC hρ hη hR s =
      physicalSlice (K s) β α := by
  classical
  have hinactive :
      (∑ k : {k : Fin hη.m // ¬ hη.p k ≠ 0},
        physicalSlice (K s) β α * hη.sectorProjection k) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact physicalSlice_mul_sectorProjection_eq_zero_of_probability_eq_zero
      hC hρ hη hR s β α k (not_ne_iff.mp k.property)
  have hactive :
      (∑ k : {k : Fin hη.m // hη.p k ≠ 0},
        physicalSlice (K s) β α * hη.sectorProjection k) =
          physicalSlice (K s) β α := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (p := fun k : Fin hη.m ↦ hη.p k ≠ 0)
      (fun k ↦ physicalSlice (K s) β α * hη.sectorProjection k)
    rw [hinactive, add_zero] at hsplit
    calc
      _ = ∑ k : Fin hη.m,
          physicalSlice (K s) β α * hη.sectorProjection k := hsplit
      _ = physicalSlice (K s) β α *
          (∑ k : Fin hη.m, hη.sectorProjection k) := by rw [Finset.mul_sum]
      _ = _ := by rw [hη.sum_sectorProjection, Matrix.mul_one]
  rw [bntSectorProjection, Finset.mul_sum]
  calc
    (∑ k : {k : Fin hη.m // hη.p k ≠ 0},
      physicalSlice (K s) β α *
        (if bntSectorLabel hC hρ hη hR k = s then
          hη.sectorProjection k else 0)) =
        ∑ k : {k : Fin hη.m // hη.p k ≠ 0},
          physicalSlice (K s) β α * hη.sectorProjection k := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : bntSectorLabel hC hρ hη hR k = s
      · simp [hk]
      · rw [if_neg hk, Matrix.mul_zero]
        symm
        exact physicalSlice_mul_sectorProjection_eq_zero_of_ne_label
          hC hρ hη hR k s (Ne.symm hk) β α
    _ = _ := hactive

/-- The physical slice of a normal representative is supported exactly in
its matching BNT physical sector.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1680--1755. -/
theorem bntSectorProjection_mul_physicalSlice_mul_self
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g)
    (β α : Fin (dim s)) :
    bntSectorProjection hC hρ hη hR s * physicalSlice (K s) β α *
        bntSectorProjection hC hρ hη hR s = physicalSlice (K s) β α := by
  rw [bntSectorProjection_mul_physicalSlice_self hC hρ hη hR,
    physicalSlice_mul_bntSectorProjection_self hC hρ hη hR]

/-- The matching BNT projection fixes the ket index of its normal
representative.

Source: arXiv:1606.00608, Appendix C.2, lines 1733--1770. -/
theorem ketLeftMul_bntSectorProjection_basis
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g) :
    (K s).ketLeftMul (bntSectorProjection hC hρ hη hR s) = K s := by
  ext a b β α
  simp only [ketLeftMul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h := congrFun (congrFun
    (bntSectorProjection_mul_physicalSlice_self hC hρ hη hR s β α) a) b
  simpa only [Matrix.mul_apply, physicalSlice] using h

/-- The BNT-labelled physical projectors select the matching normal sector:
the corner `P_s K_i P_t` vanishes if `s ≠ t` or `i ≠ s`.

**Scope restriction (closing matrices):** the generic statement retains the
nonzero-closing hypothesis used in the cancellation argument.  The source
specialization derives it in `BNTThreeSiteReducedClosure.lean`.

Source: arXiv:1606.00608, Appendix C.2, equation `PjKiPj`, lines 1680--1742. -/
theorem bntSectorProjection_mul_physicalSlice_mul_eq_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (i s t : Fin g)
    (hst : s ≠ t ∨ i ≠ s) (β α : Fin (dim i)) :
    bntSectorProjection hC hρ hη hR s * physicalSlice (K i) β α *
        bntSectorProjection hC hρ hη hR t = 0 := by
  classical
  rw [bntSectorProjection, bntSectorProjection, Finset.sum_mul,
    Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hks : bntSectorLabel hC hρ hη hR k = s
  · by_cases hlt : bntSectorLabel hC hρ hη hR l = t
    · simp only [hks, hlt, if_pos]
      by_cases hkl : (k : Fin hη.m) = l
      · have hsub : k = l := Subtype.ext hkl
        subst l
        rcases hst with hst | his
        · exact False.elim (hst (hks.symm.trans hlt))
        · apply sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_ne_label
            hC hρ hη hR k i
          exact fun hi ↦ his (hi.trans hks)
      · exact sectorProjection_mul_physicalSlice_mul_sectorProjection_eq_zero_of_ne
          hC hρ hη hR i β α hkl
    · simp [hlt]
  · simp [hks]

/-- Summing the diagonal BNT-sector corners recovers every physical slice of
a normal representative:
\[
  \sum_s P_s\,\mathcal K_i^{\beta,\alpha}\,P_s
    =\mathcal K_i^{\beta,\alpha}.
\]
This is the one-site algebraic content of the orthogonal direct-sum
decomposition of the sector states.

Source: arXiv:1606.00608, Appendix C.2, lines 1733--1770. -/
theorem sum_bntSectorProjection_mul_physicalSlice_mul_self
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (i : Fin g)
    (β α : Fin (dim i)) :
    (∑ s : Fin g,
      bntSectorProjection hC hρ hη hR s * physicalSlice (K i) β α *
        bntSectorProjection hC hρ hη hR s) =
      physicalSlice (K i) β α := by
  classical
  rw [Finset.sum_eq_single i]
  · exact bntSectorProjection_mul_physicalSlice_mul_self
      hC hρ hη hR i β α
  · intro s _ hsi
    exact bntSectorProjection_mul_physicalSlice_mul_eq_zero
      hC hρ hη hR i s s (Or.inr (Ne.symm hsi)) β α
  · simp

/-- Changing the physical basis of representative `i` by the BNT projector
`P_s` retains that representative exactly when `s = i` and otherwise gives
the zero tensor.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1680--1755. -/
theorem changePhysicalBasis_bntSectorProjection_basis
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (i s : Fin g) :
    changePhysicalBasis (bntSectorProjection hC hρ hη hR s) (K i) =
      if s = i then K i else 0 := by
  classical
  let P := bntSectorProjection hC hρ hη hR s
  have hP : IsOrthogonalProjection P :=
    bntSectorProjection_isOrthogonal hC hρ hη hR s
  ext a b β α
  simp only [changePhysicalBasis]
  rw [hP.1.eq]
  by_cases hsi : s = i
  · subst s
    rw [if_pos rfl]
    exact Matrix.ext_iff.mpr
      (bntSectorProjection_mul_physicalSlice_mul_self
        hC hρ hη hR i β α) a b
  · rw [if_neg hsi]
    have hzero := bntSectorProjection_mul_physicalSlice_mul_eq_zero
      hC hρ hη hR i s s (Or.inr fun his ↦ hsi his.symm) β α
    exact Matrix.ext_iff.mpr hzero a b

/-- The MPO of the zero local tensor vanishes at every physical chain length. -/
theorem mpo_zero_of_pos {D : ℕ} {N : ℕ} (hN : 0 < N) :
    mpo (0 : MPOTensor d D) N = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  ext u v
  obtain ⟨a, u', rfl⟩ : ∃ a u', u = Fin.cons a u' :=
    ⟨u 0, u ∘ Fin.succ, (Fin.cons_self_tail u).symm⟩
  obtain ⟨b, v', rfl⟩ : ∃ b v', v = Fin.cons b v' :=
    ⟨v 0, v ∘ Fin.succ, (Fin.cons_self_tail v).symm⟩
  rw [mpo_cons_cons]
  simp

/-- Sitewise compression of a BNT representative by `P_s` retains precisely
the matching representative.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNKj`, lines 1756--1759. -/
theorem singleKrausMap_sitewise_bntSectorProjection_mpo_basis
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) {N : ℕ} (hN : 0 < N)
    (i s : Fin g) :
    singleKrausMap
        (sitewisePhysicalMatrix (bntSectorProjection hC hρ hη hR s) N)
        (mpo (K i) N) =
      if s = i then mpo (K i) N else 0 := by
  rw [singleKrausMap_sitewisePhysicalMatrix_mpo,
    changePhysicalBasis_bntSectorProjection_basis hC hρ hη hR]
  by_cases hsi : s = i
  · simp [hsi]
  · simp [hsi, mpo_zero_of_pos hN]

/-- The MPO representative obtained by absorbing the common copy weight into
the BNT representative.

Source: arXiv:1606.00608, Appendix C.2, equation `CFK`, lines 1660--1665. -/
noncomputable def commonWeightAbsorbedBasisMPOTensor
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (j : Fin S.basisCount) :
    MPOTensor d (S.basisDim j) :=
  fun a b => S.commonWeight hWeight j • S.basisMPOTensor j a b

/-- The matching BNT projection fixes the ket index after the common copy
weight has been absorbed into the normal representative.

Source: arXiv:1606.00608, Appendix C.2, lines 1660--1665 and 1733--1770. -/
theorem ketLeftMul_bntSectorProjection_commonWeightAbsorbedBasis
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ)
    (hη : EtaStructure ρ) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (s : Fin S.basisCount) :
    (commonWeightAbsorbedBasisMPOTensor S hWeight s).ketLeftMul
        (bntSectorProjection hC hρ hη hR s) =
      commonWeightAbsorbedBasisMPOTensor S hWeight s := by
  ext a b β α
  have h := congrFun (congrFun (congrFun (congrFun
    (ketLeftMul_bntSectorProjection_basis hC hρ hη hR s) a) b) β) α
  simp only [ketLeftMul, commonWeightAbsorbedBasisMPOTensor,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
  calc
    ∑ x, bntSectorProjection hC hρ hη hR s a x *
        (S.commonWeight hWeight s * S.basisMPOTensor s x b β α) =
        S.commonWeight hWeight s *
          ∑ x, bntSectorProjection hC hρ hη hR s a x *
            S.basisMPOTensor s x b β α := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        (Fintype.sum_mul_mul_eq_mul_sum_mul (R := ℂ) _ _ _)
    _ = _ := by rw [h]

/-- Returning the absorbed-weight MPO representative to doubled-index MPS
coordinates gives the absorbed representative defined in
`CommonWeightAbsorption.lean`. -/
@[simp] theorem commonWeightAbsorbedBasisMPOTensor_toMPSTensor
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (j : Fin S.basisCount) :
    (commonWeightAbsorbedBasisMPOTensor S hWeight j).toMPSTensor =
      S.commonWeightAbsorbedBasis hWeight j := by
  funext ab
  change S.commonWeight hWeight j •
      S.basis j (finProdFinEquiv (ab.divNat, ab.modNat)) =
    S.commonWeight hWeight j • S.basis j ab
  exact congrArg (fun x => S.commonWeight hWeight j • S.basis j x)
    (finProdFinEquiv.apply_symm_apply ab)

/-- Absorbing the common weight scales the length-`N` MPO by its `N`-th
power. -/
theorem mpo_commonWeightAbsorbedBasisMPOTensor
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (j : Fin S.basisCount)
    {N : ℕ} (u v : Fin N → Fin d) :
    mpo (commonWeightAbsorbedBasisMPOTensor S hWeight j) N u v =
      (S.commonWeight hWeight j) ^ N * mpo (S.basisMPOTensor j) N u v := by
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
    commonWeightAbsorbedBasisMPOTensor_toMPSTensor]
  change MPSTensor.mpv
      (fun i => S.commonWeight hWeight j • S.basis j i)
      (fun n => finProdFinEquiv (u n, v n)) = _
  rw [MPSTensor.mpv_smul, ← MPSTensor.mpv_toMPSTensor_pairConfig,
    S.basisMPOTensor_toMPSTensor]

/-- The positive-length MPO is the sum of the absorbed normal
representatives, each multiplied by its copy number.

Source: arXiv:1606.00608, Appendix C.2, lines 1660--1665 and 1753--1770. -/
theorem mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {N : ℕ} (hN : 0 < N) :
    mpo M N = ∑ s : Fin S.basisCount,
      (S.copies s : ℂ) • mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N := by
  ext u v
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [S.mpo_eq_sum_coeff_basisMPOTensor M hM hN u v]
  apply Finset.sum_congr rfl
  intro s _
  rw [S.coeff_eq_copies_mul_commonWeight_pow hWeight,
    mpo_commonWeightAbsorbedBasisMPOTensor]
  ring

/-- Compressing the full MPO by the sitewise BNT projection selects the
matching absorbed-weight representative with its natural copy multiplicity.

This is the generic form with the closing matrices and simultaneous inverse
displayed explicitly.  The source specialization below derives these data
from common blocking and SAL.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNKj`, lines 1756--1759. -/
theorem singleKrausMap_sitewise_bntSectorProjection_mpo
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ)
    (hη : EtaStructure ρ) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    {N : ℕ} (hN : 0 < N) (s : Fin S.basisCount) :
    singleKrausMap
        (sitewisePhysicalMatrix (bntSectorProjection hC hρ hη hR s) N)
        (mpo M N) =
      (S.copies s : ℂ) •
        mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N := by
  classical
  have hmpo : mpo M N = ∑ j : Fin S.basisCount,
      S.coeff N j • mpo (S.basisMPOTensor j) N := by
    ext u v
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact S.mpo_eq_sum_coeff_basisMPOTensor M hM hN u v
  rw [hmpo, map_sum]
  simp_rw [map_smul]
  simp_rw [singleKrausMap_sitewise_bntSectorProjection_mpo_basis
    hC hρ hη hR hN]
  rw [Finset.sum_eq_single s]
  · simp only [if_true]
    ext u v
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [S.coeff_eq_copies_mul_commonWeight_pow hWeight,
      mpo_commonWeightAbsorbedBasisMPOTensor]
    ring
  · intro t _ hts
    simp [Ne.symm hts]
  · simp

/-- The literal tensor-power form of `sigmaNKj`:
\[
  P_s^{\otimes N}\,\rho^{(N)}(M)\,P_s^{\otimes N}
  =r_s\,\rho^{(N)}(\mathcal K_s).
\]

The right-hand projector is not written with an adjoint because an
orthogonal one-site projection has a Hermitian sitewise tensor power.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNKj`, lines 1756--1759. -/
theorem sitewise_bntSectorProjection_mul_mpo_mul_self
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ)
    (hη : EtaStructure ρ) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    {N : ℕ} (hN : 0 < N) (s : Fin S.basisCount) :
    let P := sitewisePhysicalMatrix
      (bntSectorProjection hC hρ hη hR s) N
    P * mpo M N * P =
      (S.copies s : ℂ) •
        mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N := by
  dsimp only
  let P := sitewisePhysicalMatrix
    (bntSectorProjection hC hρ hη hR s) N
  have hP : P.IsHermitian := sitewisePhysicalMatrix_isHermitian
    (bntSectorProjection_isOrthogonal hC hρ hη hR s).1 N
  calc
    P * mpo M N * P = singleKrausMap P (mpo M N) := by
      rw [singleKrausMap_apply, hP.eq]
    _ = _ := singleKrausMap_sitewise_bntSectorProjection_mpo
      M S hM hWeight hC hρ hη hR hN s

/-- For the normalized four-site SAL marginal, the source BNT projectors obey
the local selection rule `P_s K_i P_t = 0` unless `s = t = i`, and their
sitewise tensor powers select the corresponding absorbed-weight MPO at every
positive chain length:
\[
  P_s^{\otimes N}\,\rho^{(N)}(M)\,P_s^{\otimes N}
  =r_s\,\rho^{(N)}(\mathcal K_s).
\]

There is no independent nonzero-closing-matrix hypothesis.  The normalized
four-site BNT closure supplies it from SAL, copy independence, and
nonnilpotence.

The Hayashi decomposition uses the proved forward
Hayashi--Ruskai--Hayden--Jozsa--Petz--Winter characterization of equality in
strong subadditivity, `hayashi_ssa_equality_characterization_forward`.

**Source hypothesis (biCF):** the one-letter simultaneous span is precisely
the block-injective canonical-form assumption imposed at the start of Case II
in arXiv:1606.00608, line 1628.  It supplies the simultaneous inverse used in
the source proof.  Its relation with finite physical blocking is recorded in
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj`, `generateMPDO`,
and `sigmaNKj`, lines 1680--1759. -/
theorem exists_bntProjectorSelection_positiveLength_of_sameMPV₂Pos_isSAL
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M) :
    let ρ := Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))
      (M.reducedBlockState 4 3 (by omega))
    ∃ (C : Matrix (MPSTensor.BlockEntryIndex S.basisDim)
        (Fin d × Fin d) ℂ),
      ∃ hC : MPSTensor.IsMPOBlockLeftInverse
          (fun j ↦ S.basisMPOTensor j) C,
        ∃ hη : EtaStructure ρ,
          let hρ : IsThreeSiteFamilyClosure
              (fun j ↦ S.basisMPOTensor j)
              (S.normalizedThreeSiteClosingMatrix M 1) ρ :=
            (reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
              M S hM hWeight hnonNil hSAL).1
          let hR : ∀ j : Fin S.basisCount,
              S.normalizedThreeSiteClosingMatrix M 1 j ≠ 0 :=
            (reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
              M S hM hWeight hnonNil hSAL).2
          (∀ (i s t : Fin S.basisCount), s ≠ t ∨ i ≠ s →
              ∀ (β α : Fin (S.basisDim i)),
                bntSectorProjection hC hρ hη hR s *
                    physicalSlice (S.basisMPOTensor i) β α *
                    bntSectorProjection hC hρ hη hR t = 0) ∧
            (∀ (N : ℕ), 0 < N → ∀ s : Fin S.basisCount,
              let P := sitewisePhysicalMatrix
                (bntSectorProjection hC hρ hη hR s) N
              P * mpo M N * P =
                (S.copies s : ℂ) •
                  mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N) := by
  dsimp only
  obtain ⟨C, hC, hη, _hunique, _hproj, _horth, _hsum⟩ :=
    exists_bntSectorProjectors_four_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL
  let hClosure :=
    reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
      M S hM hWeight hnonNil hSAL
  let hρ := hClosure.1
  let hR := hClosure.2
  refine ⟨C, hC, hη, ?_, ?_⟩
  · intro i s t hst β α
    exact bntSectorProjection_mul_physicalSlice_mul_eq_zero
      hC hρ hη hR i s t hst β α
  · intro N hN s
    exact sitewise_bntSectorProjection_mul_mpo_mul_self
      M S hM hWeight hC hρ hη hR hN s

end MPOTensor
