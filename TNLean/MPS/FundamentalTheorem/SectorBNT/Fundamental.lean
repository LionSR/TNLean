/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.CoeffIdentity
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch
import TNLean.MPS.FundamentalTheorem.SectorBNT.WeightEquiv
import TNLean.MPS.FundamentalTheorem.Multi

/-!
# BNT equal-MPV sector witnesses (CPSV16 §II.C lines 1182–1192)

This module combines the full-basis matching (`StrongMatch`) and the
exact coefficient identity (`CoeffIdentity`) into the sector-witness
conclusion of the CPSV16/CPSV21 fundamental theorem on the
`IsBNTCanonicalForm` surface.

Paper anchors:

* CPSV16 §II.C lines 1182–1186: full BNT basis matching by the `Lem1`
  contradiction and symmetry argument.
* CPSV16 §II.C lines 1187–1188: exact power-sum coefficient comparison,
  recovering copy multiplicities and weights up to the matched phase.
* CPSV21 Definition 4.2 lines 1846–1850 and the two-layer display at
  lines 1864–1884: per-block BNT normalization on the basis tensors.
  The per-block convention on copy coefficients
  `∀ j, ∃ q, ‖μ_{j,q}‖ = 1` — implicit in CPSV16 §II.C line 1182's
  projection argument — is taken as an explicit theorem-level hypothesis
  here, not as a structural field of `IsBNTCanonicalForm`.

The theorem below exposes the sector-level witnesses needed before assembling
the global CPSV16 gauge `⊕_j (𝟙_{r_j} ⊗ Y_j)`.  It does not use
`dropSector` recursion, partial-union combined LI, or asymptotic-difference
multiset recovery.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- The `P`-side copy weight transported into the flattened copy coordinates of `Q`.

For a matched basis bijection `β : Fin Q.basisCount ≃ Fin P.basisCount` and
per-block copy permutations `τ k`, this is the weight array appearing in the
coordinate-level direct sum
`⊕_{(k,q)} P.weight (β k) (τ k q) • P.basis (β k)`.
It is the Lean counterpart of the reindexing implicit in CPSV16 §II.C lines
1189–1192 before forming the global gauge `⊕_k (𝟙_{r_k} ⊗ X_k)`. -/
noncomputable def matched_p_weight {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k))) :
    Fin Q.totalCopies → ℂ :=
  fun s =>
    let x := Q.flatIndexEquiv.symm s
    P.weight (β x.1) (τ x.1 x.2)

/-- The `P`-side basis tensor transported into the flattened copy coordinates of `Q`.

The output is indexed by `Fin Q.totalCopies`, with each copy `(k,q)` carrying the
cast of `P.basis (β k)` to the matched `Q.basisDim k`. -/
noncomputable def matched_p_basis {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k) :
    (s : Fin Q.totalCopies) → MPSTensor d (Q.flatDim s) := fun s => by
  change MPSTensor d (Q.basisDim (Q.flatIndexEquiv.symm s).1)
  exact cast (congr_arg (MPSTensor d) (hDim (Q.flatIndexEquiv.symm s).1))
    (P.basis (β (Q.flatIndexEquiv.symm s).1))

/-- Duplicate the per-basis gauge matrices over all copies in the flattened `Q` coordinates.

This realizes the `𝟙_{r_k} ⊗ X_k` part of CPSV16 §II.C line 1191. -/
noncomputable def matched_block_gauge {Q : SectorDecomposition d}
    (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ) :
    (s : Fin Q.totalCopies) → GL (Fin (Q.flatDim s)) ℂ := fun s => by
  change GL (Fin (Q.basisDim (Q.flatIndexEquiv.symm s).1)) ℂ
  exact Xblock (Q.flatIndexEquiv.symm s).1

/-- **Global block gauge from matched sectors and copy weights.**

Assume the sectors of two sector decompositions have already been matched, and
assume that the block gauges, phases, and copy-weight identities all use the
same phases. Then the flattened `Q`-tensor is obtained by conjugating the
matched-coordinate `P`-tensor by the direct sum
`⊕_k (𝟙_{r_k} ⊗ X_k)`.

This is the pure assembly part of CPSV16 §II.C lines 1189–1192. It does not
prove the coefficient comparison that supplies the weight identities. -/
theorem sector_bnt_global_gauge_of_matched_weights
    {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
    (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
    (ζ : Fin Q.basisCount → ℂ)
    (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ)
    (hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0)
    (hConj : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i =
        ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
            Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)))
    (hWeight : ∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
      Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) :
    ∃ X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ,
      X = globalGaugeOfBlocks (matched_block_gauge (Q := Q) Xblock) ∧
      ∀ i : Fin d,
        toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
          (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
            (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
            toTensorFromBlocks (d := d)
              (μ := matched_p_weight (P := P) (Q := Q) β τ)
              (matched_p_basis (P := P) (Q := Q) β hDim) i *
            (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
              Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := by
  classical
  let μP : Fin Q.totalCopies → ℂ := matched_p_weight (P := P) (Q := Q) β τ
  let AP : (s : Fin Q.totalCopies) → MPSTensor d (Q.flatDim s) :=
    matched_p_basis (P := P) (Q := Q) β hDim
  let Xcoord : (s : Fin Q.totalCopies) → GL (Fin (Q.flatDim s)) ℂ :=
    matched_block_gauge (Q := Q) Xblock
  have hWeighted : ∀ (s : Fin Q.totalCopies) (i : Fin d),
      (Q.flatWeight s) • Q.flatBasis s i =
        (Xcoord s : Matrix (Fin (Q.flatDim s)) (Fin (Q.flatDim s)) ℂ) *
          ((μP s) • AP s i) *
          (((Xcoord s)⁻¹ : GL (Fin (Q.flatDim s)) ℂ) :
            Matrix (Fin (Q.flatDim s)) (Fin (Q.flatDim s)) ℂ) := by
    intro s i
    let x := Q.flatIndexEquiv.symm s
    let k : Fin Q.basisCount := x.1
    let q : Fin (Q.copies k) := x.2
    have hμ : μP s = Q.weight k q * ζ k := by
      have hw := hWeight k q
      change P.weight (β k) (τ k q) = Q.weight k q * ζ k
      calc
        P.weight (β k) (τ k q) = ζ k * Q.weight k q := by
          rw [hw, ← mul_assoc, mul_inv_cancel₀ (hζ_ne k), one_mul]
        _ = Q.weight k q * ζ k := by ring
    change (Q.weight k q) • Q.basis k i =
      (Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
        ((μP s) • (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i) *
        (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
          Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)
    rw [hConj k i, hμ]
    simp [smul_smul, Matrix.mul_assoc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have hFormula :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj
      (μ := fun _ : Fin Q.totalCopies => (1 : ℂ))
      (A := fun s i => μP s • AP s i)
      (B := fun s i => Q.flatWeight s • Q.flatBasis s i)
      Xcoord hWeighted
  have hLeft :
      toTensorFromBlocks (d := d) (μ := fun _ : Fin Q.totalCopies => (1 : ℂ))
        (fun s i => μP s • AP s i) =
        toTensorFromBlocks (d := d) (μ := μP) AP := by
    funext i
    simp [toTensorFromBlocks]
  have hRight :
      toTensorFromBlocks (d := d) (μ := fun _ : Fin Q.totalCopies => (1 : ℂ))
        (fun s i => Q.flatWeight s • Q.flatBasis s i) =
        toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis := by
    funext i
    simp [toTensorFromBlocks]
  refine ⟨globalGaugeOfBlocks Xcoord, rfl, ?_⟩
  intro i
  calc
    toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
        toTensorFromBlocks (d := d) (μ := fun _ : Fin Q.totalCopies => (1 : ℂ))
          (fun s i => Q.flatWeight s • Q.flatBasis s i) i := by
            rw [hRight]
    _ = (globalGaugeOfBlocks Xcoord : Matrix
            (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
            (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
          toTensorFromBlocks (d := d) (μ := fun _ : Fin Q.totalCopies => (1 : ℂ))
            (fun s i => μP s • AP s i) i *
          (((globalGaugeOfBlocks Xcoord)⁻¹ :
              GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
            Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
              (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := hFormula i
    _ = (globalGaugeOfBlocks Xcoord : Matrix
            (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
            (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
          toTensorFromBlocks (d := d) (μ := μP) AP i *
          (((globalGaugeOfBlocks Xcoord)⁻¹ :
              GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
            Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
              (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := by
            rw [hLeft]

/-- **Conditional proportional global gauge from matched copy weights.**

For proportional MPV families, the proportional sector-matching theorem supplies
the matched BNT basis, unit phases, and block gauges of CPSV16 §II.C lines
1184--1186. If the remaining coefficient-comparison step supplies copy
permutations whose weights obey the same phases, then the direct-sum gauge
assembly uses the same algebra as the equal-MPV corollary in lines 1189--1192.

This theorem isolates the exact residual input for the proportional
global-gauge upgrade: the copy-weight identity. That residual input is not
provided by the CPSV16 proportional theorem; lines 1187--1192 are the
equal-MPV corollary, where the length-dependent proportionality scalar is
identically one. -/
theorem ft_sector_bnt_proportional_global_gauge_of_weight_data
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (ζ : Fin Q.basisCount → ℂ)
      (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) ∧
      ∀ (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k))),
        (∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
          Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) →
        ∃ X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ,
          X = globalGaugeOfBlocks (matched_block_gauge (Q := Q) Xblock) ∧
          ∀ i : Fin d,
            toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
              (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
                toTensorFromBlocks (d := d)
                  (μ := matched_p_weight (P := P) (Q := Q) β τ)
                  (matched_p_basis (P := P) (Q := Q) β hDim) i *
                (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
                  Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                    (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := by
  classical
  obtain ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, _hMpv⟩ :=
    ft_sector_bnt_proportional_sector_match_witnesses
      (P := P) (Q := Q) hP hQ hUnitP hUnitQ hProp
  refine ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, ?_⟩
  intro τ hWeight
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := by
    intro k hzero
    have hnorm := hζ_norm k
    simp [hzero] at hnorm
  exact sector_bnt_global_gauge_of_matched_weights
    (P := P) (Q := Q) β hDim τ ζ Xblock hζ_ne hConj hWeight

/-- **BNT equal-MPV sector-witness theorem (CPSV16 §II.C lines 1184–1188).**

If two BNT sector decompositions satisfying `IsBNTCanonicalForm` generate the
same MPV family, then their BNT basis sectors are bijectively matched by
gauge-phase equivalence.  For each matched sector, the copy multiplicities
agree and the raw copy weights agree after multiplying by the inverse of the
gauge phase and permuting the copies. -/
theorem ft_sector_bnt_equal_sector_dataPos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount),
      (∀ k, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k)) ∧
      (∀ k, P.copies (β k) = Q.copies k) ∧
      ∃ ζ : Fin Q.basisCount → ℂ, (∀ k, ‖ζ k‖ = 1) ∧
        ∀ k, ∃ τ : Fin (Q.copies k) ≃ Fin (P.copies (β k)),
          ∀ q : Fin (Q.copies k), Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ q) := by
  classical
  obtain ⟨β, hβMatchFull⟩ := bijective_match_of_sameMPVPos hP hQ hUnitP hUnitQ hEqual
  let hMatch : ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k) :=
    fun k => by
      obtain ⟨h, hGPE, _hNondecay⟩ := hβMatchFull k
      exact ⟨h, hGPE⟩
  have hCoeff := coeff_identity_via_global_gaugePos hP hQ hEqual β hMatch
  let ζ : Fin Q.basisCount → ℂ := fun k => (hCoeff k).choose
  have hζ_norm : ∀ k : Fin Q.basisCount, ‖ζ k‖ = 1 := fun k =>
    (hCoeff k).choose_spec.1
  have hCoeff_eventual : ∀ k : Fin Q.basisCount,
      ∃ N₀, ∀ N > N₀, P.coeff N (β k) = (ζ k) ^ N * Q.coeff N k := fun k =>
    (hCoeff k).choose_spec.2
  have hWeightData : ∀ k : Fin Q.basisCount,
      ∃ (hCopies : P.copies (β k) = Q.copies k)
        (τ : Fin (P.copies (β k)) ≃ Fin (Q.copies k)),
        ∀ q : Fin (P.copies (β k)),
          Q.weight k (τ q) = (ζ k)⁻¹ * P.weight (β k) q := by
    intro k
    obtain ⟨N₀, hCoeff_k⟩ := hCoeff_eventual k
    have hζ_ne : ζ k ≠ 0 := by
      intro hzero
      have hnorm := hζ_norm k
      simp [hzero] at hnorm
    exact matched_sector_weight_equiv (P := P) (Q := Q)
      (j₀ := β k) (k₀' := k) (ζ := ζ k) hζ_ne (N₀ := N₀) hCoeff_k
  let hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k := fun k =>
    (hWeightData k).choose
  refine ⟨β, hMatch, hCopies, ζ, hζ_norm, ?_⟩
  intro k
  obtain ⟨hC, τPQ, hτPQ⟩ := hWeightData k
  refine ⟨τPQ.symm, ?_⟩
  intro q
  have hpoint := hτPQ (τPQ.symm q)
  simpa using hpoint

/-- Reformulation for the all-length `SameMPV₂` form. -/
theorem ft_sector_bnt_equal_sector_data
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount),
      (∀ k, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k)) ∧
      (∀ k, P.copies (β k) = Q.copies k) ∧
      ∃ ζ : Fin Q.basisCount → ℂ, (∀ k, ‖ζ k‖ = 1) ∧
        ∀ k, ∃ τ : Fin (Q.copies k) ≃ Fin (P.copies (β k)),
          ∀ q : Fin (Q.copies k), Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ q) :=
  ft_sector_bnt_equal_sector_dataPos
    (P := P) (Q := Q) hP hQ hUnitP hUnitQ hEqual.toSameMPV₂Pos

/-- **Global gauge in matched flattened coordinates (CPSV16 §II.C lines 1189–1192).**

This is the coordinate-level construction of the global gauge.  Starting
from equal MPV families on the BNT canonical-form surface, it produces:

* the full basis bijection `β`,
* per-block bond-dimension equalities and gauge matrices `Xblock k`,
* copy permutations `τ k` with the **same** phase `ζ k` as the block gauge, and
* the explicit flattened global matrix
  `X = globalGaugeOfBlocks (matched_block_gauge Xblock)`.

The final displayed equality says that the unfolded flattened presentation of
`Q.toTensor` is obtained by conjugating the `P`-side sector tensor written in
`Q`'s flattened copy coordinates.  In paper notation this is the direct-sum
matrix `⊕_k (𝟙_{r_k} ⊗ X_k)`.  The remaining conversion from this
matched-coordinate presentation to a literal `GaugeEquiv P.toTensor Q.toTensor`
is only a coordinate permutation/cast of the flattened direct sum and is
intentionally not hidden here; the theorem exposes the explicit CPSV16 witness
rather than an opaque existential. -/
theorem ft_sector_bnt_equal_global_gaugePos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (_hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k)
      (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
      (ζ : Fin Q.basisCount → ℂ)
      (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) ∧
      (∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
        Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) ∧
      ∃ X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ,
        X = globalGaugeOfBlocks (matched_block_gauge (Q := Q) Xblock) ∧
        ∀ i : Fin d,
          toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
            (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
              (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
              toTensorFromBlocks (d := d)
                (μ := matched_p_weight (P := P) (Q := Q) β τ)
                (matched_p_basis (P := P) (Q := Q) β hDim) i *
              (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
                Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                  (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := by
  classical
  obtain ⟨β, hβMatchFull⟩ := bijective_match_of_sameMPVPos hP hQ hUnitP hUnitQ hEqual
  let hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k :=
    fun k => (hβMatchFull k).choose
  let hGPE : ∀ k : Fin Q.basisCount,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) (Q.basis k) :=
    fun k => (hβMatchFull k).choose_spec.1
  let Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ :=
    fun k => (hGPE k).choose
  let ζ : Fin Q.basisCount → ℂ := fun k => (hGPE k).choose_spec.choose
  have hConj : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i =
        ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
            Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)) := by
    intro k i
    exact (hGPE k).choose_spec.choose_spec.2 i
  have hMpv : ∀ (k : Fin Q.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis k) σ = (ζ k) ^ N * mpv (P.basis (β k)) σ := by
    intro k N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k)))
      (B := Q.basis k) (Xblock k) (ζ k) (hConj k) N σ,
      mpv_cast_dim (hDim k) (P.basis (β k)) N σ]
  have hζ_norm : ∀ k : Fin Q.basisCount, ‖ζ k‖ = 1 := by
    intro k
    have hAA : Tendsto (fun N => ‖mpvOverlap (d := d) (P.basis (β k)) (P.basis (β k)) N‖)
        atTop (𝓝 (1 : ℝ)) := by
      have h1 := (hP.basis_normalized_self_overlap (β k)).norm
      simpa using h1
    have hBB : Tendsto (fun N => ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k) N‖)
        atTop (𝓝 (1 : ℝ)) := by
      have h1 := (hQ.basis_normalized_self_overlap k).norm
      simpa using h1
    have hScale :=
      mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := P.basis (β k)) (B := Q.basis k)
        (ζ := ζ k) (hMpv k)
    exact norm_eq_one_of_selfOverlap_scale (ζ := ζ k) hAA hBB hScale
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := by
    intro k hzero
    have hnorm := hζ_norm k
    simp [hzero] at hnorm
  have hCoeff := coeff_identity_via_matched_mpv_phasePos hP hEqual β ζ hMpv
  have hWeightData : ∀ k : Fin Q.basisCount,
      ∃ (hCopies : P.copies (β k) = Q.copies k)
        (τPQ : Fin (P.copies (β k)) ≃ Fin (Q.copies k)),
        ∀ q : Fin (P.copies (β k)),
          Q.weight k (τPQ q) = (ζ k)⁻¹ * P.weight (β k) q := by
    intro k
    obtain ⟨N₀, hCoeff_k⟩ := hCoeff k
    exact matched_sector_weight_equiv (P := P) (Q := Q)
      (j₀ := β k) (k₀' := k) (ζ := ζ k) (hζ_ne k) (N₀ := N₀) hCoeff_k
  let hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k := fun k =>
    (hWeightData k).choose
  let τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)) :=
    fun k => (hWeightData k).choose_spec.choose.symm
  have hWeight : ∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
      Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q) := by
    intro k q
    have hpoint := (hWeightData k).choose_spec.choose_spec
      ((hWeightData k).choose_spec.choose.symm q)
    simpa [τ] using hpoint
  obtain ⟨X, hXdef, hGauge⟩ :=
    sector_bnt_global_gauge_of_matched_weights
      (P := P) (Q := Q) β hDim τ ζ Xblock hζ_ne hConj hWeight
  exact ⟨β, hDim, hCopies, τ, ζ, Xblock, hζ_norm, hConj, hWeight, X, hXdef, hGauge⟩

/-- Reformulation for the all-length `SameMPV₂` form. -/
theorem ft_sector_bnt_equal_global_gauge
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (_hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k)
      (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
      (ζ : Fin Q.basisCount → ℂ)
      (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) ∧
      (∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
        Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) ∧
      ∃ X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ,
        X = globalGaugeOfBlocks (matched_block_gauge (Q := Q) Xblock) ∧
        ∀ i : Fin d,
          toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
            (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
              (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
              toTensorFromBlocks (d := d)
                (μ := matched_p_weight (P := P) (Q := Q) β τ)
                (matched_p_basis (P := P) (Q := Q) β hDim) i *
              (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
                Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                  (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :=
  ft_sector_bnt_equal_global_gaugePos
    (P := P) (Q := Q) hP hQ hUnitP hUnitQ hEqual.toSameMPV₂Pos

end MPSTensor
