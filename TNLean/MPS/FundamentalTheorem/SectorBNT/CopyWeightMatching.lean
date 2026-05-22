/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.WeightEquiv

/-!
# Copy-weight matching for matched BNT sectors

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
