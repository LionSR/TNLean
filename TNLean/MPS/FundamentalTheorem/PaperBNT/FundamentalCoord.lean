/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.Fundamental

/-!
# Paper-faithful BNT equal-MPV gauge equivalence: bundled `II_cor2` witness

This module packages the paper-faithful equal-MPV theorem
`ft_paper_bnt_equal_global_gauge` as the literal `II_cor2` statement of
CPSV16 §II.C lines 354–361 / appendix lines 1184–1192.

The bundled-witness theorem `ft_paper_bnt_equal_mps_gaugeEquiv_witnesses`
exposes, for any two paper-faithful BNT sector decompositions $P$ and $Q$
generating the same MPV family:

* the matched basis bijection $β : \{1,\dots,g_Q\} \simeq \{1,\dots,g_P\}$;
* per-block bond-dimension equalities $D_P^{(βk)} = D_Q^{(k)}$;
* matched copy multiplicities $r_{βk}^P = r_k^Q$;
* matched copy permutations $τ_k$;
* per-block gauge phases $ζ_k \in \mathbb{C}^\times$;
* per-block gauge matrices $X_k \in \mathrm{GL}(D_Q^{(k)},\mathbb{C})$;
* the equality of total bond dimensions $\sum_k r_k D_k$;
* the explicit global gauge $X \in \mathrm{GL}(\sum_s D^{(s)},\mathbb{C})$;

together with the three CPSV16 line-1188/1191 conjugation identities:

* $B_k = ζ_k\,X_k\,A_{βk}\,X_k^{-1}$ (per basis block);
* $ν_{k,q} = ζ_k^{-1}\,μ_{βk,\,τ_k q}$ (per copy weight);
* $V_Q = X\,V_P\,X^{-1}$ at every site (global gauge equation, in matched
  flattened-copy coordinates).

The global equation is stated in the matched coordinates of $Q$'s flattened
copy index (this is the literal Phase E output of CPSV16 lines 1189–1192).
Converting the right-hand side from the matched-coordinate `toTensorFromBlocks`
into a literal `cast`-of-`P.toTensor` requires assembling a sector-permutation
matrix from `sectorFlatEquiv` and conjugating; the present module records the
witness bundle that is the verbatim CPSV16 II_cor2 packaging, while the
permutation-matrix conjugation is left for a follow-up module (it requires
non-trivial `PEquiv` glue on block-diagonal matrices over a reindexed
$Σ$-type).

Paper anchors:

* CPSV16 §II.C lines 354–361: `II_cor2` statement of gauge equivalence
  between two BNT canonical forms with the same expectation values.
* CPSV16 §II.C lines 1184–1192: BNT block matching, sector weight
  identification, and explicit global gauge $X = \bigoplus_k (𝟙_{r_k}
  \otimes X_k)$.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **CPSV16 `II_cor2` witness form (CPSV16 §II.C lines 354–361 / 1184–1192).**

If two paper-faithful BNT sector decompositions generate the same MPV family,
then there exist:

* a basis bijection $β : \{1,\dots,g_Q\} \simeq \{1,\dots,g_P\}$,
* per-block bond-dimension equalities $D_P^{(βk)} = D_Q^{(k)}$,
* matched copy multiplicities $r_{βk}^P = r_k^Q$,
* per-block copy permutations $τ_k$,
* per-block gauge phases $ζ_k \in \mathbb{C}^\times$,
* per-block gauge matrices $X_k \in \mathrm{GL}(D_Q^{(k)},\mathbb{C})$,
* a total bond-dimension equality $\sum_k r_k D_k = \sum_k r_k' D_k'$, and
* an explicit global gauge $X \in \mathrm{GL}\bigl(\sum_s D^{(s)},
  \mathbb{C}\bigr)$ of the form $X = \bigoplus_k (𝟙_{r_k}\otimes X_k)$,

such that the three CPSV16 identities

* $B_k = ζ_k\,X_k\,A_{βk}\,X_k^{-1}$ (per basis block, CPSV16 line 1191),
* $ν_{k,q} = ζ_k^{-1}\,μ_{βk,\,τ_k q}$ (per copy weight, CPSV16 line 1190),
* $V_Q^i = X\,V_P^i\,X^{-1}$ at every physical site $i$ (global gauge,
  CPSV16 lines 1191–1192),

hold simultaneously.  The final global identity is exposed here in the
matched flattened-copy coordinates of $Q$: writing the $P$-side block
data through the matched bijections gives the
`toTensorFromBlocks`-tensor that conjugates to $Q.toTensor$ under $X$.

CPSV16 §II.C lines 354–361 / 1184–1192. -/
theorem ft_paper_bnt_equal_mps_gaugeEquiv_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (_hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k)
      (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
      (ζ : Fin Q.basisCount → ℂ)
      (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ)
      (_hTotal : P.totalDim = Q.totalDim)
      (X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ),
      (∀ k : Fin Q.basisCount, ζ k ≠ 0) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) ∧
      (∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
        Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) ∧
      (∀ i : Fin d,
        Q.toTensor i =
          (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                      (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
            toTensorFromBlocks (d := d)
              (μ := matched_p_weight (P := P) (Q := Q) β τ)
              (matched_p_basis (P := P) (Q := Q) β hDim) i *
            (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
              Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                     (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ)) := by
  classical
  obtain ⟨β, hDim, hCopies, τ, ζ, Xblock, hζ_ne, hConj, hWeight, X, _hXdef, hGauge⟩ :=
    ft_paper_bnt_equal_global_gauge hP hQ hEqual
  -- `P.totalDim = Q.totalDim` follows from `sectorFlatEquiv` plus matched dims
  have hTotal : P.totalDim = Q.totalDim :=
    SectorDecomposition.totalDim_eq_of_match (P := P) (Q := Q) β hDim τ
  -- the bond-dimension index `Q.totalDim` and `∑ s, Q.flatDim s` agree definitionally
  refine ⟨β, hDim, hCopies, τ, ζ, Xblock, hTotal, X, hζ_ne, hConj, hWeight, ?_⟩
  intro i
  exact hGauge i

/-- **CPSV16 `II_cor2` literal form, sector data + total bond-dimension equality.**

If two paper-faithful BNT sector decompositions generate the same MPV
family, their total bond dimensions agree and there exists a matrix $X$
realizing the CPSV16 line-1191 global gauge in $Q$'s flattened sector
coordinates.

This is the literal CPSV16 II_cor2 statement of gauge equivalence between
two BNT canonical forms with the same expectation values; the witness
bundle is provided by `ft_paper_bnt_equal_mps_gaugeEquiv_witnesses`.

CPSV16 §II.C lines 354–361. -/
theorem ft_paper_bnt_equal_mps_gaugeEquiv
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ (_hTotal : P.totalDim = Q.totalDim),
      ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
        (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
        (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
        (X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ),
        ∀ i : Fin d,
          Q.toTensor i =
            (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                        (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
              toTensorFromBlocks (d := d)
                (μ := matched_p_weight (P := P) (Q := Q) β τ)
                (matched_p_basis (P := P) (Q := Q) β hDim) i *
              (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
                Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                       (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := by
  classical
  obtain ⟨β, hDim, _hCopies, τ, _ζ, _Xblock, _hTotal, X, _, _, _, hGauge⟩ :=
    ft_paper_bnt_equal_mps_gaugeEquiv_witnesses hP hQ hEqual
  exact ⟨SectorDecomposition.totalDim_eq_of_match (P := P) (Q := Q) β hDim τ,
    β, hDim, τ, X, hGauge⟩

end MPSTensor
