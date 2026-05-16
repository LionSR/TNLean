/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.Api
import TNLean.MPS.FundamentalTheorem.SectorWeightComparison

/-!
# Matched-sector weight multiset equality and permutation extraction

This module isolates the two **exact-algebraic** reusable conclusions of
the matched-sector coefficient identity:

* `matched_sector_weight_multiset_eq` — given an eventual coefficient
  identity `P.coeff N j₀ = ζ^N · Q.coeff N k₀'` (for `N > N₀`, with
  `ζ ≠ 0`), the per-copy weight multisets coincide and the per-sector
  copy multiplicities match: `P.copies j₀ = Q.copies k₀'`.

* `matched_sector_weight_equiv` — refines the multiset equality into an
  explicit permutation `τ : Fin (P.copies j₀) ≃ Fin (Q.copies k₀')` with
  `Q.weight k₀' (τ q) = ζ⁻¹ · P.weight j₀ q` for every copy index `q`.

These statements are exact-algebraic: they consume only
`power_sums_eq_of_eventually_eq_hetero` and
`Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card` from
`SectorWeightComparison.lean`, together with a generic
`Multiset.map`-permutation extractor over `Fin n` proved by induction
on `n`.  No dominant-pair-matching surface, drop-sector recursion, or
Newton–Girard inversion is involved.

## Paper anchors

* CPSV16 §II.C lines 1158–1167, 1184, 1188 (arXiv:1606.00608): for a
  fixed matched sector, equal power sums (eventually in `N`) and nonzero
  per-copy weights imply equal cardinalities and equal weight multisets,
  hence the per-copy gauge-phase identification
  `μ_{j,q} = ν_{j,τ(q)} · e^{i\phi_j}`.

## Tags

matrix product states, fundamental theorem, BNT, matched-sector weight
multiset, gauge-phase per-copy identification.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **Matched-sector weight multiset equality and per-copy multiplicity match.**

If `P.coeff N j₀ = ζ^N · Q.coeff N k₀'` for every `N` past some threshold
`N₀`, with `ζ ≠ 0`, then `P.copies j₀ = Q.copies k₀'` and the two
per-copy weight multisets agree:
`Multiset.map (P.weight j₀) Finset.univ.val
   = Multiset.map (fun q => ζ * Q.weight k₀' q) Finset.univ.val`.

This is CPSV16 line 1188 read on a single matched sector: equal power
sums (eventually in `N`) and nonzero entries imply equal multisets, hence
equal cardinalities.

The proof composes `power_sums_eq_of_eventually_eq_hetero` (extension
from eventual to all positive exponents) with
`Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card`
(unequal-cardinality power-sum recovery). -/
theorem matched_sector_weight_multiset_eq
    {P Q : SectorDecomposition d}
    (j₀ : Fin P.basisCount) (k₀' : Fin Q.basisCount)
    (ζ : ℂ) (hζ : ζ ≠ 0)
    {N₀ : ℕ}
    (hCoeff : ∀ N > N₀, P.coeff N j₀ = ζ ^ N * Q.coeff N k₀') :
    ∃ hCopies : P.copies j₀ = Q.copies k₀',
      Multiset.map (P.weight j₀) (Finset.univ : Finset (Fin (P.copies j₀))).val
        = Multiset.map
            (fun q : Fin (P.copies j₀) =>
              ζ * Q.weight k₀' (Fin.cast hCopies q))
            (Finset.univ : Finset (Fin (P.copies j₀))).val := by
  classical
  -- Define the rescaled `Q`-side weight family `w'(q) := ζ · Q.weight k₀' q`.
  -- Its power sums match the `P`-side weight `P.weight j₀` power sums
  -- eventually.
  let wQ : Fin (Q.copies k₀') → ℂ := fun q => ζ * Q.weight k₀' q
  have hwQ_ne : ∀ q : Fin (Q.copies k₀'), wQ q ≠ 0 := by
    intro q
    exact mul_ne_zero hζ (Q.weight_ne_zero k₀' q)
  have hwP_ne : ∀ q : Fin (P.copies j₀), P.weight j₀ q ≠ 0 :=
    fun q => P.weight_ne_zero j₀ q
  -- Eventual equality of `∑ (P.weight j₀ q)^N` and `∑ (ζ · Q.weight k₀' q)^N`.
  have hPow : ∀ N, N₀ + 1 ≤ N →
      (∑ q : Fin (P.copies j₀), (P.weight j₀ q) ^ N)
        = ∑ q : Fin (Q.copies k₀'), wQ q ^ N := by
    intro N hN
    have hN' : N > N₀ := by omega
    have hCN := hCoeff N hN'
    -- Unfold `coeff` on both sides and distribute `ζ^N` through the `Q` sum.
    have hPdef : P.coeff N j₀
        = ∑ q : Fin (P.copies j₀), (P.weight j₀ q) ^ N :=
      P.coeff_eq_sum_weight_pow N j₀
    have hQdef : Q.coeff N k₀'
        = ∑ q : Fin (Q.copies k₀'), (Q.weight k₀' q) ^ N :=
      Q.coeff_eq_sum_weight_pow N k₀'
    have hRHS_distrib :
        ζ ^ N * (∑ q : Fin (Q.copies k₀'), (Q.weight k₀' q) ^ N)
          = ∑ q : Fin (Q.copies k₀'), wQ q ^ N := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro q _
      change ζ ^ N * (Q.weight k₀' q) ^ N = (ζ * Q.weight k₀' q) ^ N
      rw [mul_pow]
    calc
      ∑ q : Fin (P.copies j₀), (P.weight j₀ q) ^ N
          = P.coeff N j₀ := hPdef.symm
      _ = ζ ^ N * Q.coeff N k₀' := hCN
      _ = ζ ^ N * (∑ q : Fin (Q.copies k₀'), (Q.weight k₀' q) ^ N) := by
            rw [hQdef]
      _ = ∑ q : Fin (Q.copies k₀'), wQ q ^ N := hRHS_distrib
  -- Extend to all positive exponents via
  -- `power_sums_eq_of_eventually_eq_hetero`.
  have hAll :=
    SectorWeightData.power_sums_eq_of_eventually_eq_hetero
      (P.weight j₀) wQ hwP_ne hwQ_ne (M := N₀ + 1) hPow
  -- Apply the unequal-cardinality multiset-recovery lemma.
  obtain ⟨hCopies, hMultiset⟩ :=
    Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card
      (P.copies j₀) (Q.copies k₀') (P.weight j₀) wQ hwP_ne hwQ_ne
      (fun k _hk _hkMax => hAll k)
  refine ⟨hCopies, ?_⟩
  -- The recovery lemma yields
  --   `Multiset.map (P.weight j₀) univ = Multiset.map wQ univ`,
  -- and `wQ q = ζ · Q.weight k₀' q`.  Reindex via `Fin.cast hCopies`.
  have hReindex :
      (Finset.univ : Finset (Fin (Q.copies k₀'))).val.map wQ
        = (Finset.univ : Finset (Fin (P.copies j₀))).val.map
            (fun q : Fin (P.copies j₀) =>
              ζ * Q.weight k₀' (Fin.cast hCopies q)) := by
    let e : Fin (P.copies j₀) ≃ Fin (Q.copies k₀') :=
      (Fin.castOrderIso hCopies).toEquiv
    have hMap : Multiset.map e
        (Finset.univ : Finset (Fin (P.copies j₀))).val
          = (Finset.univ : Finset (Fin (Q.copies k₀'))).val :=
      Multiset.map_univ_val_equiv e
    calc
      (Finset.univ : Finset (Fin (Q.copies k₀'))).val.map wQ
          = (Multiset.map e
                (Finset.univ : Finset (Fin (P.copies j₀))).val).map wQ := by
            rw [hMap]
      _ = (Finset.univ : Finset (Fin (P.copies j₀))).val.map (wQ ∘ e) := by
            rw [Multiset.map_map]
      _ = (Finset.univ : Finset (Fin (P.copies j₀))).val.map
            (fun q : Fin (P.copies j₀) =>
              ζ * Q.weight k₀' (Fin.cast hCopies q)) := by
            refine Multiset.map_congr rfl ?_
            intro q _; rfl
  exact hMultiset.trans hReindex

/-! ### Matched-sector weight-permutation extractor

The multiset equality above is upgraded to an *explicit* permutation
`τ : Fin (P.copies j₀) ≃ Fin (Q.copies k₀')` matching individual per-copy
weights up to the gauge-phase factor `ζ`.  This is the per-copy form of
CPSV16 line 1188 (`μ_{j,q} = ν_{j,q} · e^{i\phi_j}` for an indexing of
the `Q`-copies determined by a matching).

The proof reduces to a generic auxiliary lemma extracting an `Equiv.Perm` from a
multiset-map equality on `Fin`, then composes with the cardinality cast
and clears the `ζ` factor with `mul_inv_cancel₀ hζ`.
-/

/-- **Auxiliary: extract `Equiv.Perm (Fin n)` from a multiset map equality.**

Given `f, g : Fin n → α` whose `Multiset.map`s over `Finset.univ.val`
coincide, there exists a permutation `σ` of `Fin n` with
`f q = g (σ q)` for every `q`.

Proof by induction on `n`: at the successor step, locate an index `j`
in the codomain of `g` matching `f 0`, decompose both multisets via
`Fin.univ_succAbove`, apply the inductive hypothesis to the restricted
functions on `Fin n`, and reassemble via `finSuccEquiv'` and
`Equiv.optionCongr`. -/
private lemma exists_perm_of_multiset_map_univ_eq {α : Type*} :
    ∀ {n : ℕ} (f g : Fin n → α),
      Multiset.map f (Finset.univ : Finset (Fin n)).val =
        Multiset.map g (Finset.univ : Finset (Fin n)).val →
      ∃ σ : Equiv.Perm (Fin n), ∀ q, f q = g (σ q) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _
    exact ⟨Equiv.refl _, fun q => q.elim0⟩
  | succ n ih =>
    intro f g hMap
    classical
    -- Locate `j : Fin (n+1)` with `g j = f 0`.
    have hMem : f 0 ∈ Multiset.map g (Finset.univ : Finset (Fin (n+1))).val := by
      rw [← hMap]
      exact Multiset.mem_map_of_mem f (Finset.mem_univ_val 0)
    obtain ⟨j, _hjMem, hj⟩ := Multiset.mem_map.mp hMem
    -- `Multiset.map h univ = h p ::ₘ Multiset.map (h ∘ p.succAbove) univ`.
    have decomp : ∀ (h : Fin (n+1) → α) (p : Fin (n+1)),
        Multiset.map h (Finset.univ : Finset (Fin (n+1))).val =
          h p ::ₘ Multiset.map (h ∘ p.succAbove)
            (Finset.univ : Finset (Fin n)).val := by
      intro h p
      have hUniv : (Finset.univ : Finset (Fin (n+1))).val =
          p ::ₘ ((Finset.univ : Finset (Fin n)).val.map p.succAboveEmb) := by
        rw [Fin.univ_succAbove n p, Finset.cons_val, Finset.map_val]
      rw [hUniv, Multiset.map_cons, Multiset.map_map]
      rfl
    -- Reduce to a multiset-map equality on `Fin n`.
    have hRestricted :
        Multiset.map (f ∘ (0 : Fin (n+1)).succAbove)
            (Finset.univ : Finset (Fin n)).val =
          Multiset.map (g ∘ j.succAbove)
            (Finset.univ : Finset (Fin n)).val := by
      have hEqCons :
          f 0 ::ₘ Multiset.map (f ∘ (0 : Fin (n+1)).succAbove)
              (Finset.univ : Finset (Fin n)).val =
            g j ::ₘ Multiset.map (g ∘ j.succAbove)
              (Finset.univ : Finset (Fin n)).val := by
        rw [← decomp f 0, ← decomp g j]
        exact hMap
      rw [hj] at hEqCons
      exact (Multiset.cons_inj_right (f 0)).mp hEqCons
    -- Apply the inductive hypothesis.
    obtain ⟨σ', hσ'⟩ := ih _ _ hRestricted
    -- Assemble `σ : Fin (n+1) ≃ Fin (n+1)` via `finSuccEquiv'`.
    refine ⟨((finSuccEquiv' (0 : Fin (n+1))).trans σ'.optionCongr).trans
              (finSuccEquiv' j).symm, ?_⟩
    intro q
    refine q.cases ?_ ?_
    · -- Case `q = 0`: `σ 0 = j`, and `g j = f 0` by `hj`.
      simp only [Equiv.trans_apply, finSuccEquiv'_at,
        Equiv.optionCongr_apply, Option.map_none, finSuccEquiv'_symm_none]
      exact hj.symm
    · -- Case `q = i.succ`: `σ i.succ = j.succAbove (σ' i)`.
      intro i
      have hRec := hσ' i
      simp only [Function.comp_apply, Fin.zero_succAbove] at hRec
      simp only [Equiv.trans_apply, ← Fin.zero_succAbove,
        finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquiv'_symm_some]
      exact hRec

set_option linter.unusedVariables false in
/-- **Matched-sector weight-permutation extractor.**

Refines `matched_sector_weight_multiset_eq` into an explicit permutation
`τ` realising CPSV16 line 1188's per-copy identification.

Paper anchor: CPSV16 §II.C lines 1158-1167, 1184, 1188 (arXiv:1606.00608). -/
theorem matched_sector_weight_equiv
    {P Q : SectorDecomposition d}
    (j₀ : Fin P.basisCount) (k₀' : Fin Q.basisCount)
    (ζ : ℂ) (hζ : ζ ≠ 0)
    {N₀ : ℕ}
    (hCoeff : ∀ N > N₀, P.coeff N j₀ = ζ ^ N * Q.coeff N k₀') :
    ∃ (hCopies : P.copies j₀ = Q.copies k₀')
      (τ : Fin (P.copies j₀) ≃ Fin (Q.copies k₀')),
      ∀ q : Fin (P.copies j₀),
        Q.weight k₀' (τ q) = ζ⁻¹ * P.weight j₀ q := by
  classical
  obtain ⟨hCopies, hMultiset⟩ :=
    matched_sector_weight_multiset_eq j₀ k₀' ζ hζ hCoeff
  -- Extract `σ : Fin (P.copies j₀) ≃ Fin (P.copies j₀)` matching the
  -- per-copy weights up to the gauge-phase factor `ζ`.
  obtain ⟨σ, hσ⟩ :=
    exists_perm_of_multiset_map_univ_eq
      (P.weight j₀)
      (fun q : Fin (P.copies j₀) => ζ * Q.weight k₀' (Fin.cast hCopies q))
      hMultiset
  -- Compose with the cardinality cast `Fin (P.copies j₀) ≃ Fin (Q.copies k₀')`.
  let castEquiv : Fin (P.copies j₀) ≃ Fin (Q.copies k₀') :=
    (Fin.castOrderIso hCopies).toEquiv
  refine ⟨hCopies, σ.trans castEquiv, ?_⟩
  intro q
  have hPoint : P.weight j₀ q = ζ * Q.weight k₀' (Fin.cast hCopies (σ q)) :=
    hσ q
  have hQ : Q.weight k₀' ((σ.trans castEquiv) q)
      = Q.weight k₀' (Fin.cast hCopies (σ q)) := by
    simp [castEquiv]
  rw [hQ, hPoint, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul]

end MPSTensor
