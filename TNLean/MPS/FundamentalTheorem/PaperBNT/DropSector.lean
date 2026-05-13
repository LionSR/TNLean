/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.Basic

/-!
# Dropping a BNT sector from a sector decomposition

This module supplies the infrastructure to remove one BNT sector from a
`SectorDecomposition` while preserving the paper-faithful canonical-form
predicate `IsBNTCanonicalForm`.  It is the foundational piece needed by the
strong-induction route to the full equal-MPV non-decaying-overlap statement
(CPSV16 §II `II_cor2`, lines 1172–1192): once a matched BNT block pair has
been identified between two families with `SameMPV₂`, the sector and its
multi-copy weights are removed from both sides and the argument repeats on
the smaller pair.  No coefficient or overlap identity is asserted here; that
content belongs to the matched-sector subtraction lemma scheduled for a
follow-up landing.

The operation produces a fresh `SectorDecomposition` with
`basisCount` reduced by one, the basis-block family reindexed by
`Fin.succAbove`, and the multi-copy `SectorWeightData` restricted to the
surviving indices.  Each field of `IsBNTCanonicalForm` is transferred by
composition with `Fin.succAbove`; the `bnt_data` (eventual linear
independence on a subfamily) field uses `LinearIndependent.comp` with the
`Fin.succAbove_right_injective` injectivity datum.

## Main definitions

* `SectorDecomposition.dropSector`: drop the sector indexed by
  `i₀ : Fin (n + 1)` when `P.basisCount = n + 1`.

## Main lemmas

* `dropSector_basisCount`, `dropSector_basisDim`, `dropSector_basis`,
  `dropSector_copies`, `dropSector_weight`, `dropSector_coeff`:
  componentwise unfolding lemmas.
* `mpv_toTensor_dropSector_add_coeff_mpv_basis`: removing the sector
  contributes `P.coeff N i · mpv (P.basis i) σ` to the MPV
  (CPSV16 lines 287–301 raw two-layer display).
* `IsBNTCanonicalForm.dropSector`: the paper-faithful canonical-form
  predicate is preserved by `dropSector`.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and
  Boundary Theories*, arXiv:1606.00608.  Lines 264–279 (gauge-phase sector
  grouping), 287–301 (raw two-layer BNT display with coefficient
  `∑_q μ_{j,q}^N`), 1172–1192 (`II_cor2` matched-pair subtraction in the
  induction step), 1184–1188 (raw power-sum comparison for the matched
  sector).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix product states and projected entangled pair states*,
  arXiv:2011.12127.  Lines 1846–1884 (BNT and two-layer BNT decomposition
  with raw `μ_{j,q}`).
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

namespace SectorDecomposition

/-- **Drop a BNT sector.**

When `P.basisCount = n + 1`, this removes the sector indexed by
`i₀ : Fin (n + 1)` and produces a new `SectorDecomposition` with
`basisCount = n`.  The surviving basis-block family is reindexed by
`Fin.cast h.symm ∘ Fin.succAbove i₀`; the multi-copy `SectorWeightData`
follows the same reindexing.

The construction is purely structural: each field of the resulting
`SectorDecomposition` is obtained from the original `P` by pre-composition
with the succAbove embedding.  No analytic content is asserted at this
stage; the matched-sector subtraction identities that drive the CPSV16
§II `II_cor2` induction (lines 1172–1192) are stated in a follow-up
module. -/
def dropSector (P : SectorDecomposition d) {n : ℕ}
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) :
    SectorDecomposition d where
  basisCount := n
  basisDim j := P.basisDim (Fin.cast h.symm (i₀.succAbove j))
  basis j := P.basis (Fin.cast h.symm (i₀.succAbove j))
  sectors :=
    { copies := fun j => P.copies (Fin.cast h.symm (i₀.succAbove j))
      copies_pos := fun _ => P.copies_pos _
      weight := fun j q => P.weight (Fin.cast h.symm (i₀.succAbove j)) q
      weight_ne_zero := fun _ q => P.weight_ne_zero _ q }

variable {P : SectorDecomposition d} {n : ℕ}

@[simp] theorem dropSector_basisCount
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) :
    (P.dropSector h i₀).basisCount = n := rfl

@[simp] theorem dropSector_basisDim
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) (j : Fin n) :
    (P.dropSector h i₀).basisDim j =
      P.basisDim (Fin.cast h.symm (i₀.succAbove j)) := rfl

@[simp] theorem dropSector_basis
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) (j : Fin n) :
    (P.dropSector h i₀).basis j =
      P.basis (Fin.cast h.symm (i₀.succAbove j)) := rfl

@[simp] theorem dropSector_copies
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) (j : Fin n) :
    (P.dropSector h i₀).copies j =
      P.copies (Fin.cast h.symm (i₀.succAbove j)) := rfl

@[simp] theorem dropSector_weight
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) (j : Fin n)
    (q : Fin ((P.dropSector h i₀).copies j)) :
    (P.dropSector h i₀).weight j q =
      P.weight (Fin.cast h.symm (i₀.succAbove j)) q :=
  rfl

/-- The sector coefficient on the dropped decomposition is the original
sector coefficient at the reindexed basis position
(CPSV16 lines 287–301). -/
@[simp] theorem dropSector_coeff
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) (N : ℕ) (j : Fin n) :
    (P.dropSector h i₀).coeff N j =
      P.coeff N (Fin.cast h.symm (i₀.succAbove j)) := rfl

/-- **MPV expansion of the dropped tensor.**

Removing the sector at index `i₀` from `P` subtracts the contribution
`P.coeff N i · mpv (P.basis i) σ` of that sector from the assembled MPV.
This is the raw two-layer BNT display of CPSV16 lines 287–301 read on
the dropped decomposition. -/
theorem mpv_toTensor_dropSector_add_coeff_mpv_basis
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (P.dropSector h i₀).toTensor σ +
        P.coeff N (Fin.cast h.symm i₀) *
          mpv (P.basis (Fin.cast h.symm i₀)) σ =
      mpv P.toTensor σ := by
  classical
  have hP : mpv P.toTensor σ =
      ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ :=
    P.mpv_toTensor_eq_sum_coeff σ
  -- Re-index the sum over `Fin P.basisCount` to a sum over `Fin (n + 1)`
  -- using the equality `h : P.basisCount = n + 1`.
  have hReindex :
      ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ =
        ∑ j : Fin (n + 1),
          P.coeff N (Fin.cast h.symm j) * mpv (P.basis (Fin.cast h.symm j)) σ := by
    refine Fintype.sum_equiv (Fin.castOrderIso h).toEquiv _ _ ?_
    intro j
    rfl
  -- Split off the `i₀` term using `Fin.sum_univ_succAbove`.
  have hSplit :
      ∑ j : Fin (n + 1),
          P.coeff N (Fin.cast h.symm j) * mpv (P.basis (Fin.cast h.symm j)) σ =
        P.coeff N (Fin.cast h.symm i₀) *
            mpv (P.basis (Fin.cast h.symm i₀)) σ +
          ∑ j : Fin n,
            P.coeff N (Fin.cast h.symm (i₀.succAbove j)) *
              mpv (P.basis (Fin.cast h.symm (i₀.succAbove j))) σ :=
    Fin.sum_univ_succAbove
      (fun j : Fin (n + 1) =>
        P.coeff N (Fin.cast h.symm j) * mpv (P.basis (Fin.cast h.symm j)) σ) i₀
  -- The tail equals the MPV of the dropped tensor.
  have hTail :
      ∑ j : Fin n,
          P.coeff N (Fin.cast h.symm (i₀.succAbove j)) *
            mpv (P.basis (Fin.cast h.symm (i₀.succAbove j))) σ =
        mpv (P.dropSector h i₀).toTensor σ := by
    have := (P.dropSector h i₀).mpv_toTensor_eq_sum_coeff σ
    -- `(P.dropSector h i₀).coeff N j = P.coeff N (Fin.cast h.symm (i₀.succAbove j))`,
    -- `(P.dropSector h i₀).basis j = P.basis (Fin.cast h.symm (i₀.succAbove j))`.
    simpa [dropSector_basis, dropSector_coeff] using this.symm
  rw [hP, hReindex, hSplit, hTail]
  ring

/-- Symmetric form of `mpv_toTensor_dropSector_add_coeff_mpv_basis`:
the dropped MPV equals the original MPV minus the sector contribution. -/
theorem mpv_toTensor_dropSector_eq_sub
    (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (P.dropSector h i₀).toTensor σ =
      mpv P.toTensor σ -
        P.coeff N (Fin.cast h.symm i₀) *
          mpv (P.basis (Fin.cast h.symm i₀)) σ := by
  have := mpv_toTensor_dropSector_add_coeff_mpv_basis (P := P) h i₀ σ
  linear_combination this

end SectorDecomposition

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d} {n : ℕ}

/-- **`IsBNTCanonicalForm` is preserved by `dropSector`.**

Every field of the paper-faithful canonical-form predicate transfers from
`P` to `P.dropSector h i₀` by pre-composition with the reindexing map
`Fin.cast h.symm ∘ Fin.succAbove i₀`:

* per-block bond-dimension positivity, injectivity, irreducibility,
  left-canonical form, and normalized self-overlap are pointwise
  properties evaluated at the reindexed basis position;
* `bnt_data` (eventual linear independence of the basis MPV family) is
  closed under restriction to a subfamily via `LinearIndependent.comp`
  applied to the `Fin.succAbove` embedding (CPSV21 line 1850);
* `basis_distinct` transfers because the reindexing map is injective, so
  pairs of distinct basis indices on the dropped decomposition correspond
  to pairs of distinct basis indices on the original (CPSV16 lines 264–279
  gauge-phase grouping rule).

This is the foundational lemma for the CPSV16 §II `II_cor2` induction step
(lines 1172–1192). -/
def dropSector
    (hP : IsBNTCanonicalForm P) (h : P.basisCount = n + 1) (i₀ : Fin (n + 1)) :
    IsBNTCanonicalForm (P.dropSector h i₀) where
  basis_dim_pos _ := hP.basis_dim_pos _
  basis_injective _ := hP.basis_injective _
  basis_irreducible _ := hP.basis_irreducible _
  basis_left_canonical _ := hP.basis_left_canonical _
  basis_normalized_self_overlap _ := hP.basis_normalized_self_overlap _
  bnt_data := by
    -- Eventual linear independence carries over to the succAbove-subfamily.
    obtain ⟨N₀, hLI⟩ := hP.bnt_data
    refine ⟨N₀, ?_⟩
    intro N hN
    have hLI_full :
        LinearIndependent ℂ
          (fun j : Fin P.basisCount => mpvState (P.basis j) N) :=
      hLI N hN
    -- Compose with the injection `Fin.cast h.symm ∘ Fin.succAbove i₀`.
    have hCastInj :
        Function.Injective (Fin.cast h.symm : Fin (n + 1) → Fin P.basisCount) :=
      fun _ _ hxy => Fin.ext (by simpa [Fin.cast] using hxy)
    have hInj :
        Function.Injective
          (fun j : Fin n => Fin.cast h.symm (i₀.succAbove j)) := by
      intro j k hjk
      have hjk' : i₀.succAbove j = i₀.succAbove k := hCastInj hjk
      exact Fin.succAbove_right_injective hjk'
    -- `LinearIndependent.comp` produces LI of the composed family.
    have :=
      hLI_full.comp (fun j : Fin n => Fin.cast h.symm (i₀.succAbove j)) hInj
    -- The composed family is exactly the basis MPV family of the dropped
    -- decomposition.
    simpa [SectorDecomposition.dropSector_basis, Function.comp] using this
  basis_distinct := by
    -- Distinctness in the cast-compatible gauge-phase shape transfers to
    -- the subfamily because the reindexing is injective.
    intro j k hjk hdim
    have hCastInj :
        Function.Injective (Fin.cast h.symm : Fin (n + 1) → Fin P.basisCount) :=
      fun _ _ hxy => Fin.ext (by simpa [Fin.cast] using hxy)
    have hjk' :
        Fin.cast h.symm (i₀.succAbove j) ≠ Fin.cast h.symm (i₀.succAbove k) := by
      intro he
      have h₁ : i₀.succAbove j = i₀.succAbove k := hCastInj he
      exact hjk (Fin.succAbove_right_injective h₁)
    -- Apply the original `basis_distinct`.
    exact hP.basis_distinct
      (Fin.cast h.symm (i₀.succAbove j)) (Fin.cast h.symm (i₀.succAbove k))
      hjk' hdim

end IsBNTCanonicalForm

end MPSTensor
