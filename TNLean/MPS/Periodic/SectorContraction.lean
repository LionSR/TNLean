/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.CornerContraction
import TNLean.MPS.Periodic.SectorLift
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Lifting the sector right inverse to an ambient corner right inverse

This file builds the **sector → ambient-corner `Ω` lift** of arXiv:1708.00029,
Appendix A (lines 1026--1062): the construction that turns the *sector* right
inverse `Ω` — the one supplied by the normality input
`exists_common_sectorDecompositionMaps_of_isNormal_leftCanonical`, which recovers
`evalWord (blocks k) …` on the sector bond space `Fin (dim k)` — into the
*ambient corner* right inverse that the contraction lemma
`MPSTensor.cornerProd_contraction` needs, recovering `cornerProd P A k …` on the
ambient bond space `Fin D` for corner-supported matrices.

## From sector words to single-site words

The sector right inverse works with *blocked* words `σ : Fin L → Fin (d^m)` over
the blocked alphabet, while the contraction works with *single-site* words
`j : Fin (m·L) → Fin d`.  The two are matched by `flattenBlockedWord`: a blocked
word of length `L` flattens to a single-site word of length `m·L`, and the
`directIteratedBlockEquiv` of `MPS/Core/BlockingInfrastructure` packages this as a
bijection `blockFlattenEquiv`.

Under the paper off-diagonal convention `P k · A i = A i · P (k+1)` the repeated
corner-transition product telescopes:
`cornerProd P A k (flattenBlockedWord d m W) = (φ k (evalWord (blocks k) W)).1`
(`cornerProd_flatten_eq_phi_evalWord`), the algebraic content of eq:Fu read
through the corner isomorphism `φ`.  Transporting the sector recovery identity
`eq:Omegauprop` through `φ` along this telescoping produces the ambient corner
right inverse.

## Main results

* `MPSTensor.blockFlattenEquiv` — the bijection
  `(Fin L → Fin (blockPhysDim d m)) ≃ (Fin (m·L) → Fin d)` realizing
  `flattenBlockedWord` at the level of word-indexing functions.
* `MPSTensor.cornerProd_flatten_eq_phi_evalWord` — the telescoping identity
  identifying `cornerProd P A k` over a flattened blocked word with the corner
  image of the sector word product.
* `MPSTensor.exists_ambientCornerRightInverse_of_sectorRightInverse` — **the
  sector right inverse lift**: from the sector right inverse `Ω` (recovering
  `evalWord (blocks k) …` on `Fin (dim k)`) it produces the ambient corner right
  inverse `Ω̂` recovering `cornerProd P A k …` on `Fin D` for every
  corner-supported matrix.  This is exactly the `hΩ` hypothesis of
  `MPSTensor.cornerProd_contraction`.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A (eq:Auprop, eq:Fu, eq:Omegauprop).
-/

open scoped Matrix BigOperators
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## The flattening bijection on word-indexing functions -/

/-- The bijection between *blocked* words of length `L` over the alphabet
`Fin (blockPhysDim d m)` and *single-site* words of length `m·L` over `Fin d`,
realizing the list-level `flattenBlockedWord` at the level of indexing functions.
It is assembled from the decode bijections `decodeBlockEquiv` and the grouping
bijection `directIteratedBlockEquiv` of iterated blocking. -/
noncomputable def blockFlattenEquiv (d m L : ℕ) :
    (Fin L → Fin (blockPhysDim d m)) ≃ (Fin (m * L) → Fin d) :=
  (decodeBlockEquiv (blockPhysDim d m) L).symm.trans
    ((directIteratedBlockEquiv d m L).symm.trans (decodeBlockEquiv d (m * L)))

/-- `blockFlattenEquiv` realizes `flattenBlockedWord`: the single-site word of a
blocked word `σ` is the flattening of `List.ofFn σ`. -/
theorem ofFn_blockFlattenEquiv (d m L : ℕ) (σ : Fin L → Fin (blockPhysDim d m)) :
    List.ofFn (blockFlattenEquiv d m L σ) = flattenBlockedWord d m (List.ofFn σ) := by
  have hword :
      wordOfBlock (blockPhysDim d m) L
          ((decodeBlockEquiv (blockPhysDim d m) L).symm σ) = List.ofFn σ := by
    rw [wordOfBlock, decodeBlock_decodeBlockEquiv_symm]
  calc List.ofFn (blockFlattenEquiv d m L σ)
      = wordOfBlock d (m * L)
          (iteratedBlockIndex d m L ((decodeBlockEquiv (blockPhysDim d m) L).symm σ)) := by
        simp only [blockFlattenEquiv, Equiv.trans_apply, decodeBlockEquiv_apply,
          directIteratedBlockEquiv_symm_apply, wordOfBlock]
    _ = flattenBlockedWord d m
          (wordOfBlock (blockPhysDim d m) L ((decodeBlockEquiv (blockPhysDim d m) L).symm σ)) :=
        wordOfBlock_iteratedBlockIndex d m L _
    _ = flattenBlockedWord d m (List.ofFn σ) := by rw [hword]

/-! ## Telescoping identity for flattened words -/

section Telescoping

variable {m : ℕ} [NeZero m]

/-- **Corner product of flattened words** (arXiv:1708.00029, Appendix A, eq:Fu
read through the corner isomorphism).

Under the paper off-diagonal convention `P k · A i = A i · P (k+1)`, the repeated
corner-transition product over a *flattened* nonempty blocked word `W` telescopes
into the corner image of the sector word product:
`cornerProd P A k (flattenBlockedWord d m W) = (φ k (evalWord (blocks k) W)).1`.

Each length-`m` block of the flattening collapses, by `cornerProd_eq_blockDiagCorner`
and the corner letter identity `hletter`, to the corner letter
`(φ k (blocks k I)).1`; the multiplicativity `hMul` of `φ` reassembles the letters
into the sector word product.  The empty word is excluded so the induction stays
inside the corner without needing the corner unit `(φ k 1).1 = P k`. -/
theorem cornerProd_flatten_eq_phi_evalWord
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hshift : ∀ k (i : Fin d), P k * A i = A i * P (k + 1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hletter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    (k : Fin m) :
    ∀ W : List (Fin (blockPhysDim d m)), W ≠ [] →
      cornerProd P A k (flattenBlockedWord d m W) = (φ k (evalWord (blocks k) W)).1 := by
  intro W
  -- Single-block collapse, reused below.
  have hsingle : ∀ I : Fin (blockPhysDim d m),
      cornerProd P A k (wordOfBlock d m I) = (φ k (blocks k I)).1 := by
    intro I
    rw [cornerProd_eq_blockDiagCorner P A hproj hshift k I, hletter k I]
  -- Junction shift of one length-`m` block is trivial.
  have hjunc : ∀ I : Fin (blockPhysDim d m),
      (k + (wordOfBlock d m I).length • (1 : Fin m)) = k := by
    intro I; rw [length_wordOfBlock, nsmul_card_one_fin, add_zero]
  induction W with
  | nil => intro h; exact absurd rfl h
  | cons I W' ih =>
    intro _
    rcases W' with _ | ⟨J, W''⟩
    · -- single block `[I]`
      rw [flattenBlockedWord_cons, flattenBlockedWord_nil, List.append_nil, hsingle I,
        evalWord_cons, evalWord_nil, mul_one]
    · -- `I :: J :: W''`
      rw [flattenBlockedWord_cons,
        cornerProd_append P A hproj k (wordOfBlock d m I) (flattenBlockedWord d m (J :: W'')),
        hjunc I, hsingle I, ih (by simp), ← hMul, ← evalWord_cons]

end Telescoping

/-! ## Ambient corner right inverse from the sector right inverse -/

section Lift

variable {m : ℕ} [NeZero m]

/-- **Sector → ambient-corner `Ω` lift** (arXiv:1708.00029, Appendix A, lines
1026--1062, the construction around eq:Omegauprop).

Given:

* cyclic sector projectors `P` under the paper off-diagonal convention
  `P k · A i = A i · P (k+1)` (`hshift`);
* the multiplicative corner isomorphisms `φ` with the corner letter identity
  `hletter` (the eq:Cu / eq:Auprop data of a cyclic sector decomposition);
* a positive common word length `L` and a *sector* right inverse `Ω` recovering
  every sector word product, `∑_σ Ω k X σ • evalWord (blocks k) (List.ofFn σ) = X`
  (the output of
  `exists_common_sectorDecompositionMaps_of_isNormal_leftCanonical`, eq:Omegauprop),

there is an *ambient corner* right inverse `Ω̂` over single-site words of length
`m·L` recovering every corner-supported matrix:
`∑_j Ω̂ k Y j • cornerProd P A k (List.ofFn j) = Y` whenever `P k · Y · P k = Y`.

This is exactly the `hΩ` hypothesis consumed by `MPSTensor.cornerProd_contraction`
(applied at sector `k+1` to the corner-supported inserted matrices `X k`). -/
theorem exists_ambientCornerRightInverse_of_sectorRightInverse
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hshift : ∀ k (i : Fin d), P k * A i = A i * P (k + 1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hletter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    (L : ℕ) (hL : 0 < L)
    (Ω : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ]
        ((Fin L → Fin (blockPhysDim d m)) → ℂ))
    (hΩ : ∀ (k : Fin m) (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      ∑ σ : Fin L → Fin (blockPhysDim d m),
        Ω k X σ • evalWord (blocks k) (List.ofFn σ) = X) :
    ∃ Ωhat : (k : Fin m) → MatrixAlg D → ((Fin (m * L) → Fin d) → ℂ),
      ∀ (k : Fin m) (Y : MatrixAlg D), P k * Y * P k = Y →
        ∑ j : Fin (m * L) → Fin d, Ωhat k Y j • cornerProd P A k (List.ofFn j) = Y := by
  classical
  -- The corner projection of any matrix lands in the corner submodule.
  have hcornerMem : ∀ (k : Fin m) (Y : MatrixAlg D),
      P k * Y * P k ∈ cornerSubmodule (P k) := by
    intro k Y
    have hidem : P k * P k = P k := (hproj k).2
    change P k * (P k * Y * P k) * P k = P k * Y * P k
    calc P k * (P k * Y * P k) * P k
        = (P k * P k) * Y * (P k * P k) := by simp only [Matrix.mul_assoc]
      _ = P k * Y * P k := by rw [hidem]
  refine ⟨fun k Y j =>
      Ω k ((φ k).symm ⟨P k * Y * P k, hcornerMem k Y⟩)
        ((blockFlattenEquiv d m L).symm j), ?_⟩
  intro k Y hY
  set X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
    (φ k).symm ⟨P k * Y * P k, hcornerMem k Y⟩ with hX
  -- The recovered ambient matrix is `Y`.
  have hφX : (φ k X).1 = Y := by
    rw [hX, LinearEquiv.apply_symm_apply]; exact hY
  -- The corner-embedding of `φ k`, as a linear map.
  let ψ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ] MatrixAlg D :=
    (cornerSubmodule (P k)).subtype ∘ₗ
      (φ k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ] cornerSubmodule (P k))
  have hψ : ∀ Z, ψ Z = (φ k Z).1 := fun _ => rfl
  -- Telescoping identity per blocked word, after reindexing.
  have hbridge : ∀ σ : Fin L → Fin (blockPhysDim d m),
      cornerProd P A k (List.ofFn (blockFlattenEquiv d m L σ))
        = (φ k (evalWord (blocks k) (List.ofFn σ))).1 := by
    intro σ
    rw [ofFn_blockFlattenEquiv]
    exact cornerProd_flatten_eq_phi_evalWord P A blocks φ hproj hshift hMul hletter k
      (List.ofFn σ) (List.ne_nil_of_length_pos (by rw [List.length_ofFn]; exact hL))
  -- Linearity of the corner embedding collapses the blocked recovery sum.
  have hlin :
      ψ (∑ σ : Fin L → Fin (blockPhysDim d m),
          Ω k X σ • evalWord (blocks k) (List.ofFn σ))
        = ∑ σ : Fin L → Fin (blockPhysDim d m),
            Ω k X σ • (φ k (evalWord (blocks k) (List.ofFn σ))).1 := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_smul, hψ]
  calc ∑ j : Fin (m * L) → Fin d,
        Ω k X ((blockFlattenEquiv d m L).symm j) • cornerProd P A k (List.ofFn j)
      = ∑ σ : Fin L → Fin (blockPhysDim d m),
          Ω k X ((blockFlattenEquiv d m L).symm (blockFlattenEquiv d m L σ))
            • cornerProd P A k (List.ofFn (blockFlattenEquiv d m L σ)) := by
        rw [← Equiv.sum_comp (blockFlattenEquiv d m L)
          (fun j => Ω k X ((blockFlattenEquiv d m L).symm j) • cornerProd P A k (List.ofFn j))]
    _ = ∑ σ : Fin L → Fin (blockPhysDim d m),
          Ω k X σ • (φ k (evalWord (blocks k) (List.ofFn σ))).1 := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Equiv.symm_apply_apply, hbridge σ]
    _ = ψ X := by rw [← hlin, hΩ k X]
    _ = Y := by rw [hψ, hφX]

/-- **Step 3 of the contraction**: the ambient corner `Ω` lift feeds
`MPSTensor.cornerProd_contraction` (arXiv:1708.00029, Appendix A, lines
1057--1062, the `Ω`-contraction producing eq:resultprop).

Given the same cyclic sector data as
`exists_ambientCornerRightInverse_of_sectorRightInverse` and a family of inserted
matrices `X k` supported on the corner `P (k+1)`, summing the concatenated chain
`∏_k (A_k^{σ_k} · F_{k+1}^{ρ_k})` against the lifted inverse coefficients
collapses each repeated product `F_{k+1}` to the inserted matrix `X k`, leaving
the chain `∏_k (A_k^{σ_k} · X k)`.

The right inverse `Ω` is the *sector* one (`eq:Omegauprop` on `Fin (dim k)`); the
lift transports it to the ambient corner so the contraction's hypothesis is met. -/
theorem exists_cornerProd_contraction_of_sectorRightInverse
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hshift : ∀ k (i : Fin d), P k * A i = A i * P (k + 1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hletter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    (L : ℕ) (hL : 0 < L)
    (Ω : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ]
        ((Fin L → Fin (blockPhysDim d m)) → ℂ))
    (hΩ : ∀ (k : Fin m) (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      ∑ σ : Fin L → Fin (blockPhysDim d m),
        Ω k X σ • evalWord (blocks k) (List.ofFn σ) = X)
    (σ : Fin m → Fin d) (X : Fin m → MatrixAlg D)
    (hXcorner : ∀ k : Fin m, P (k + 1) * X k * P (k + 1) = X k) :
    ∃ Ωhat : (k : Fin m) → MatrixAlg D → ((Fin (m * L) → Fin d) → ℂ),
      ∑ ρ : Fin m → (Fin (m * L) → Fin d),
          (∏ k, Ωhat (k + 1) (X k) (ρ k)) •
            (List.ofFn (fun k => cornerLetter P A k (σ k) *
              cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod
        = (List.ofFn (fun k => cornerLetter P A k (σ k) * X k)).prod := by
  obtain ⟨Ωhat, hΩhat⟩ :=
    exists_ambientCornerRightInverse_of_sectorRightInverse
      P A blocks φ hproj hshift hMul hletter L hL Ω hΩ
  exact ⟨Ωhat,
    cornerProd_contraction P A (m * L) Ωhat σ X
      (fun k => hΩhat (k + 1) (X k) (hXcorner k))⟩

end Lift

end MPSTensor
