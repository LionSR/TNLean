/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Order.ComplexPhasePositivity
import TNLean.MPS.FundamentalTheorem.Sectors.CoeffIdentity
import TNLean.MPS.FundamentalTheorem.Sectors.ProportionalMatchCore
import TNLean.MPS.Tensor.DirectSum.GaugeEquiv
import TNLean.MPS.FundamentalTheorem.Sectors.WeightEquiv
import TNLean.MPS.Transfer.Irreducible.UnitaryGauge
import TNLean.MPS.Tensor.DirectSum.BlockGauge

/-!
# BNT equal-MPV sector witnesses

This module combines the full-basis matching (`StrongMatch`) and the
exact coefficient identity (`CoeffIdentity`) into the sector-witness
conclusion of the CPSV16/CPSV21 fundamental theorem on the
`IsBNTCanonicalForm` surface.

Paper anchors:

* CPSV16 Appendix MPV proof, line 1182: full BNT basis matching by the `Lem1`
  contradiction and symmetry argument.
* CPSV16 Appendix MPV proof, lines 1187–1188: exact power-sum coefficient
  comparison, recovering copy multiplicities and weights up to the matched
  phase.
* CPSV21 Definition 4.2 lines 1846–1850 and the two-layer display at
  lines 1864–1884: per-block BNT normalization on the basis tensors.  The
  equal-MPV route below uses the exact matcher and therefore does not require
  per-sector unit-modulus copy-weight hypotheses.

The theorem below exposes the sector-level witnesses needed before assembling
the global CPSV16 gauge `⊕_j (𝟙_{r_j} ⊗ Y_j)`.  The proof path is:
full-basis matching, exact coefficient comparison, copy-weight recovery, and
then the direct-sum gauge assembly.

It also contains the following results.

* `MPSTensor.SectorBNTCopyWeightMatching`,
  `MPSTensor.SectorBNTCopyWeightMatching.of_coeff_identity`: copy-weight matching for matched BNT
  sectors.
* `MPSTensor.ft_sector_bnt_proportional_unitary_sector_match_witnesses`,
  `MPSTensor.ft_sector_bnt_equal_unitary_global_gauge_witnesses`: unitary refinement of proportional
  BNT sector matching.
-/

section CopyWeightMatching

/-!
## Copy-weight matching for matched BNT sectors

This module records the copy-level weight comparison used in the BNT
Fundamental Theorem.

After the sector bijection and per-sector gauge phases have been fixed, the
CPSV16 Appendix MPV proof compares the resulting coefficient power sums and
identifies the copy weights, up to the same phase, inside each matched sector.
The source anchor is arXiv:1606.00608, Appendix MPV proof line 1188, with the
finite power-sum lemma at lines 1155--1163.

The results here are purely algebraic: they assume the eventual
coefficient identity for each matched sector and produce the copy permutations
and pointwise weight identities needed by the direct-sum gauge assembly.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Copy-weight matching for matched BNT sectors.**

For a matched sector bijection `β : Fin Q.basisCount ≃ Fin P.basisCount` and
phases `ζ k`, this structure records the copy-level part of the CPSV16
Appendix MPV proof, line 1188: each copy of a `Q`-sector is paired with a copy
of the matched `P`-sector, and the corresponding raw weights satisfy
`ν_{k,q} = (ζ k)⁻¹ μ_{β k, τ_k q}`.

The proportional theorem in CPSV16 gives the sector matching at the theorem
statement lines 1167--1170 and the Appendix MPV proof line 1182.  The
coefficient comparison that constructs this copy-weight matching is the
remaining source-faithful input before the proportional global-gauge theorem
can be obtained without an explicit coefficient-identity hypothesis. -/
structure SectorBNTCopyWeightMatching {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (ζ : Fin Q.basisCount → ℂ) where
  /-- Copy permutation inside each matched sector. -/
  copy_equiv : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k))
  /-- Matched copy-weight identity with the same phase as the sector gauge. -/
  weight_eq : ∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
    Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (copy_equiv k q)

/-- **Construct copy-weight matching from matched-sector coefficient identities.**

Assume that every matched sector satisfies the eventual coefficient identity

`P.coeff N (β k) = (ζ k)^N * Q.coeff N k`.

If each phase `ζ k` is nonzero, then the finite power-sum comparison recovers,
sector by sector, the copy permutation and the pointwise identity

`Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ_k q)`.

This constructs the copy-weight matching established in CPSV16 Appendix MPV
proof, line 1188, using the finite power-sum lemma from lines 1155--1163. -/
noncomputable def SectorBNTCopyWeightMatching.of_coeff_identity
    {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (ζ : Fin Q.basisCount → ℂ)
    (hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0)
    (hCoeff : ∀ k : Fin Q.basisCount, ∃ N₀, ∀ N > N₀,
      P.coeff N (β k) = (ζ k) ^ N * Q.coeff N k) :
    SectorBNTCopyWeightMatching (P := P) (Q := Q) β ζ := by
  classical
  have hData : ∀ k : Fin Q.basisCount,
      ∃ (_hCopies : P.copies (β k) = Q.copies k)
        (τ : Fin (P.copies (β k)) ≃ Fin (Q.copies k)),
        ∀ q : Fin (P.copies (β k)),
          Q.weight k (τ q) = (ζ k)⁻¹ * P.weight (β k) q := by
    intro k
    obtain ⟨N₀, hCoeff_k⟩ := hCoeff k
    exact matched_sector_weight_equiv (P := P) (Q := Q)
      (j₀ := β k) (k₀' := k) (ζ := ζ k) (hζ_ne k) (N₀ := N₀) hCoeff_k
  refine
    { copy_equiv := fun k => (hData k).choose_spec.choose.symm
      weight_eq := ?_ }
  intro k q
  have hPoint := (hData k).choose_spec.choose_spec ((hData k).choose_spec.choose.symm q)
  simpa using hPoint

end MPSTensor

end CopyWeightMatching

section Fundamental

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- The `P`-side copy weight transported into the flattened copy coordinates of `Q`.

For a bijection `β : Fin Q.basisCount ≃ Fin P.basisCount` between BNT basis
sectors and per-block copy permutations `τ k`, this is the weight array
appearing in the coordinate-level direct sum
`⊕_{(k,q)} P.weight (β k) (τ k q) • P.basis (β k)`.
It is the Lean counterpart of the reindexing implicit in CPSV16 Appendix MPV
proof, lines 1189–1192, before forming the global gauge
`⊕_k (𝟙_{r_k} ⊗ X_k)`. -/
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

/-- **Global block gauge from matched sectors and copy weights.**

Assume the sectors of two sector decompositions have already been matched, and
assume that the block gauges, phases, and copy-weight identities all use the
same phases. Then the flattened `Q`-tensor is obtained by conjugating the
matched-coordinate `P`-tensor by the direct sum
`⊕_k (𝟙_{r_k} ⊗ X_k)`.

This is the pure assembly part of CPSV16 Appendix MPV proof, lines 1189–1192.
It does not prove the coefficient comparison that supplies the weight
identities. -/
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

/-- **Global block gauge from a copy-weight matching.**

This is the same direct-sum gauge assembly as
`sector_bnt_global_gauge_of_matched_weights`, with the copy permutations and
weight identities supplied by `SectorBNTCopyWeightMatching`.

It is the pure algebraic assembly of CPSV16 Appendix MPV proof, lines
1189--1192, after the line-1188 copy-weight comparison has been supplied. -/
theorem sector_bnt_global_gauge_of_copy_weight_matching
    {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
    (ζ : Fin Q.basisCount → ℂ)
    (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ)
    (hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0)
    (hConj : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i =
        ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
            Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)))
    (W : SectorBNTCopyWeightMatching (P := P) (Q := Q) β ζ) :
    ∃ X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ,
      X = globalGaugeOfBlocks (matched_block_gauge (Q := Q) Xblock) ∧
      ∀ i : Fin d,
        toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
          (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
            (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
            toTensorFromBlocks (d := d)
              (μ := matched_p_weight (P := P) (Q := Q) β W.copy_equiv)
              (matched_p_basis (P := P) (Q := Q) β hDim) i *
            (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
              Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :=
  sector_bnt_global_gauge_of_matched_weights
    (P := P) (Q := Q) β hDim W.copy_equiv ζ Xblock hζ_ne hConj W.weight_eq

/-- **Conditional proportional global gauge from a copy-weight matching.**

This records the remaining copy-weight comparison as a single
`SectorBNTCopyWeightMatching` input, instead of exposing separate copy
permutations and pointwise identities as separate hypotheses.

The theorem therefore separates the two mathematical ingredients:

* CPSV16 Appendix MPV theorem statement, lines 1167--1170, and proof line 1182
  give the sector bijection, unit phases, and block gauges;
* the still-open proportional coefficient comparison must construct the
  copy-weight matching.  Once it is available, the global gauge is the
  equal-MPV corollary's direct-sum algebra from Appendix MPV proof,
  lines 1189--1192.

The proportional sector matching used here is supplied by the exact matcher, so
no per-sector unit-modulus copy-weight hypothesis is required. -/
theorem ft_sector_bnt_proportional_global_gauge_of_copy_weight_matching
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
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
      ∀ W : SectorBNTCopyWeightMatching (P := P) (Q := Q) β ζ,
        ∃ X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ,
          X = globalGaugeOfBlocks (matched_block_gauge (Q := Q) Xblock) ∧
          ∀ i : Fin d,
            toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
              (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
                toTensorFromBlocks (d := d)
                  (μ := matched_p_weight (P := P) (Q := Q) β W.copy_equiv)
                  (matched_p_basis (P := P) (Q := Q) β hDim) i *
                (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
                  Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                    (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := by
  classical
  obtain ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, _hMpv⟩ :=
    ft_sector_bnt_proportional_sector_match_witnesses
      (P := P) (Q := Q) hP hQ hProp
  refine ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, ?_⟩
  intro W
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := fun k =>
    Complex.ne_zero_of_norm_eq_one (hζ_norm k)
  exact sector_bnt_global_gauge_of_copy_weight_matching
    (P := P) (Q := Q) β hDim ζ Xblock hζ_ne hConj W

/-- **Conditional proportional global gauge from coefficient identities.**

This is the proportional analogue of the equal-MPV coefficient-to-gauge passage,
with the still-open coefficient comparison kept as an explicit input.  The
proportional sector-matching theorem supplies the sector bijection, phases, and
block gauges.  If those same phases satisfy the eventual matched-sector
coefficient identities, then the matched-sector coefficient comparison recovers
the copy-weight matching and the direct-sum global gauge follows.

The coefficient identity is the precise remaining CPSV16 Appendix MPV line
1188 input; until it is derived from the proportional MPV hypothesis, this
theorem is a conditional assembly statement rather than the unrestricted
source theorem.

The proportional sector matching used here is supplied by the exact matcher, so
no per-sector unit-modulus copy-weight hypothesis is required. -/
theorem ft_sector_bnt_proportional_global_gauge_of_coeff_identity
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
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
      ((∀ k : Fin Q.basisCount, ∃ N₀, ∀ N > N₀,
        P.coeff N (β k) = (ζ k) ^ N * Q.coeff N k) →
        ∃ W : SectorBNTCopyWeightMatching (P := P) (Q := Q) β ζ,
          ∃ X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ,
            X = globalGaugeOfBlocks (matched_block_gauge (Q := Q) Xblock) ∧
            ∀ i : Fin d,
              toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
                (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                  (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
                  toTensorFromBlocks (d := d)
                    (μ := matched_p_weight (P := P) (Q := Q) β W.copy_equiv)
                    (matched_p_basis (P := P) (Q := Q) β hDim) i *
                  (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
                    Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                      (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ)) := by
  classical
  obtain ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, hGlobal⟩ :=
    ft_sector_bnt_proportional_global_gauge_of_copy_weight_matching
      (P := P) (Q := Q) hP hQ hProp
  refine ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, ?_⟩
  intro hCoeff
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := fun k =>
    Complex.ne_zero_of_norm_eq_one (hζ_norm k)
  let W : SectorBNTCopyWeightMatching (P := P) (Q := Q) β ζ :=
    SectorBNTCopyWeightMatching.of_coeff_identity
      (P := P) (Q := Q) β ζ hζ_ne hCoeff
  exact ⟨W, hGlobal W⟩

/-- **Equal-MPV matched copy-weight witnesses.**

From full-basis BNT matching and coefficient comparison one obtains a sector
bijection β, bond-dimension equalities, unit phases ζ k, block gauges X k, and
a copy-weight matching for the same phases.

The matched coefficient identities give the sectorwise power-sum comparison
\[
  \sum_q \mu_{\beta(k),q}^N = \sum_q (\zeta_k \nu_{k,q})^N
\]
for all sufficiently large \(N\).  Finite power-sum comparison then gives the
copy permutations and weight identities.

Source: CPSV16, Appendix MPV proof, lines 1187–1192. -/
theorem ft_sector_bnt_equal_matched_copy_weight_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
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
      Nonempty (SectorBNTCopyWeightMatching (P := P) (Q := Q) β ζ) := by
  classical
  obtain ⟨β, hβMatchFull⟩ := bijective_match_of_sameMPV hP hQ hEqual
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
    exact norm_eq_one_of_selfOverlap_scale (ζ := ζ k) hAA hBB
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := P.basis (β k)) (B := Q.basis k)
        (ζ := ζ k) (hMpv k))
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := fun k =>
    Complex.ne_zero_of_norm_eq_one (hζ_norm k)
  have hCoeff := coeff_identity_via_matched_mpv_phase hP hEqual β ζ
    (fun k N _hN σ => hMpv k N σ)
  let W : SectorBNTCopyWeightMatching (P := P) (Q := Q) β ζ :=
    SectorBNTCopyWeightMatching.of_coeff_identity
      (P := P) (Q := Q) β ζ hζ_ne hCoeff
  exact ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, ⟨W⟩⟩

/-- **BNT equal-MPV sector-witness theorem.**

If two BNT sector decompositions satisfying `IsBNTCanonicalForm` generate the
same MPV family, then their BNT basis sectors are bijectively matched by
gauge-phase equivalence.  For each matched sector, the copy multiplicities
agree and the raw copy weights agree after multiplying by the inverse of the
gauge phase and permuting the copies.

Source: CPSV16, §II.C lines 354–361 and Appendix MPV proof, lines 1182–1188. -/
theorem ft_sector_bnt_equal_sector_data
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount),
      (∀ k, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k)) ∧
      (∀ k, P.copies (β k) = Q.copies k) ∧
      ∃ ζ : Fin Q.basisCount → ℂ, (∀ k, ‖ζ k‖ = 1) ∧
        ∀ k, ∃ τ : Fin (Q.copies k) ≃ Fin (P.copies (β k)),
          ∀ q : Fin (Q.copies k), Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ q) := by
  classical
  obtain ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, ⟨W⟩⟩ :=
    ft_sector_bnt_equal_matched_copy_weight_witnesses
      (P := P) (Q := Q) hP hQ hEqual
  let hMatch : ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k) :=
    fun k => by
      exact ⟨hDim k, Xblock k, ζ k,
        Complex.ne_zero_of_norm_eq_one (hζ_norm k), hConj k⟩
  have hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k := by
    intro k
    have hcard := Fintype.card_congr (W.copy_equiv k)
    simpa using hcard.symm
  refine ⟨β, hMatch, hCopies, ζ, hζ_norm, ?_⟩
  intro k
  exact ⟨W.copy_equiv k, W.weight_eq k⟩

/-- **Global gauge in matched flattened coordinates.**

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
intentionally not hidden here; the theorem exposes the explicit CPSV16
Appendix MPV proof witness rather than an opaque existential.

Source: CPSV16, Appendix MPV proof, lines 1189–1192. -/
theorem ft_sector_bnt_equal_global_gauge
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
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
  obtain ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, ⟨W⟩⟩ :=
    ft_sector_bnt_equal_matched_copy_weight_witnesses
      (P := P) (Q := Q) hP hQ hEqual
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := fun k =>
    Complex.ne_zero_of_norm_eq_one (hζ_norm k)
  let hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k := by
    intro k
    have hcard := Fintype.card_congr (W.copy_equiv k)
    simpa using hcard.symm
  let τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)) :=
    W.copy_equiv
  obtain ⟨X, hXdef, hGauge⟩ :=
    sector_bnt_global_gauge_of_copy_weight_matching
      (P := P) (Q := Q) β hDim ζ Xblock hζ_ne hConj W
  exact ⟨β, hDim, hCopies, τ, ζ, Xblock, hζ_norm, hConj, W.weight_eq, X, hXdef,
    hGauge⟩

end MPSTensor

end Fundamental

section Unitary

/-!
## Unitary refinement of proportional BNT sector matching

The proportional Fundamental Theorem matches the basis normal tensors of two
canonical forms by gauge-phase equivalences. When the basis tensors satisfy the
BNT canonical form hypotheses of left-canonicity and irreducibility, the
matched gauges may be chosen unitary.

This is the proportional part of Canonical Form II in Cirac et al.,
arXiv:1606.00608, Corollary A.6, lines 1197–1199.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **Canonical Form II unitary refinement of proportional BNT matching.**

Let two BNT canonical forms generate eventually nonzero proportional MPV
families.  Their basis normal tensors can be matched bijectively so that each
matched pair has the same bond dimension and differs by a unit phase and a
unitary conjugation.

The BNT hypotheses already include left canonicity and irreducibility for each
basis tensor.  Thus no hypothesis beyond those of the proportional BNT theorem
is needed for this refinement.

Source: Cirac et al., arXiv:1606.00608, Corollary A.6, lines 1197–1199. -/
theorem ft_sector_bnt_proportional_unitary_sector_match_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (ζ : Fin Q.basisCount → ℂ)
      (U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      ∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
  classical
  obtain ⟨β, hDim, ζ₀, X, hζ₀, hConj, _hMpv⟩ :=
    ft_sector_bnt_proportional_sector_match_witnesses hP hQ hProp
  have hGPE : ∀ k : Fin Q.basisCount,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) (Q.basis k) :=
    fun k => ⟨X k, ζ₀ k, Complex.ne_zero_of_norm_eq_one (hζ₀ k), hConj k⟩
  have hUnitary : ∀ k : Fin Q.basisCount,
      ∃ (U : Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧
        ∀ i, Q.basis k i = ζ •
          ((U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
    intro k
    let : NeZero (Q.basisDim k) := ⟨ne_of_gt (hQ.basis_dim_pos k)⟩
    apply exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible (hGPE k)
    · exact (leftCanonical_cast_dim (hDim k) (P.basis (β k))).2
        (hP.basis_left_canonical (β k))
    · exact hQ.basis_left_canonical k
    · exact (isIrreducibleFamily_cast_dim (hDim k) (P.basis (β k))).2
        (hP.basis_irreducible (β k))
    · exact hQ.basis_irreducible k
  let U : (k : Fin Q.basisCount) →
      Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ :=
    fun k => (hUnitary k).choose
  let ζ : Fin Q.basisCount → ℂ :=
    fun k => (hUnitary k).choose_spec.choose
  refine ⟨β, hDim, ζ, U, ?_, ?_⟩
  · intro k
    exact (hUnitary k).choose_spec.choose_spec.1
  · intro k i
    exact (hUnitary k).choose_spec.choose_spec.2 i

/-- **Equal-MPV global gauge assembled from the unitary sector gauges.**

For equal BNT canonical forms, the sector phase used by the unitary conjugation
is the same phase that occurs in the copy-weight identity. Repeating each
sector unitary over its matched copies therefore gives a unitary block-diagonal
global gauge in matched flattened coordinates.

Source: arXiv:1606.00608, Corollary A.6 and Appendix MPV proof,
lines 1182--1199. -/
theorem ft_sector_bnt_equal_unitary_global_gauge_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (_hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k)
      (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
      (ζ : Fin Q.basisCount → ℂ)
      (U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ)
      (X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ)) ∧
      (∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
        Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) ∧
      (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
        (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) ∈
        Matrix.unitaryGroup (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ ∧
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
  obtain ⟨β, hDim, ζ, Xblock, hζ, hConj, ⟨W⟩⟩ :=
    ft_sector_bnt_equal_matched_copy_weight_witnesses hP hQ hEqual
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := fun k =>
    Complex.ne_zero_of_norm_eq_one (hζ k)
  have hUnitary : ∀ k : Fin Q.basisCount,
      ∃ U : Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ,
        ∀ i, Q.basis k i = ζ k •
          ((U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
    intro k
    let : NeZero (Q.basisDim k) := ⟨ne_of_gt (hQ.basis_dim_pos k)⟩
    obtain ⟨U, _, hU⟩ :=
      exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
        (Xblock k) (ζ k) (hζ_ne k) (hConj k)
        ((leftCanonical_cast_dim (hDim k) (P.basis (β k))).2
          (hP.basis_left_canonical (β k)))
        (hQ.basis_left_canonical k)
        ((isIrreducibleFamily_cast_dim (hDim k) (P.basis (β k))).2
          (hP.basis_irreducible (β k)))
        (hQ.basis_irreducible k)
    exact ⟨U, hU⟩
  let U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ :=
    fun k => (hUnitary k).choose
  have hConjU : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i = ζ k •
        ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) :=
    fun k => (hUnitary k).choose_spec
  let Ugl : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ :=
    fun k => unitaryGL (U k)
  have hConjGL : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i = ζ k •
        ((Ugl k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (((Ugl k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
            Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)) := by
    intro k i
    change Q.basis k i = ζ k •
      ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
        (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
        (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ)
    exact hConjU k i
  obtain ⟨X, hX, hGauge⟩ :=
    sector_bnt_global_gauge_of_copy_weight_matching
      β hDim ζ Ugl hζ_ne hConjGL W
  have hXunitary :
      (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
        (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) ∈
        Matrix.unitaryGroup (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ := by
    rw [hX]
    let Ucopy : (s : Fin Q.totalCopies) →
        Matrix.unitaryGroup (Fin (Q.flatDim s)) ℂ :=
      fun s => U (Q.flatIndexEquiv.symm s).1
    exact globalGaugeOfBlocks_unitaryGL_mem Ucopy
  have hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k := by
    intro k
    have hcard := Fintype.card_congr (W.copy_equiv k)
    simpa using hcard.symm
  exact ⟨β, hDim, hCopies, W.copy_equiv, ζ, U, X, hζ, hConjU,
    W.weight_eq, hXunitary, hGauge⟩

end MPSTensor

end Unitary
