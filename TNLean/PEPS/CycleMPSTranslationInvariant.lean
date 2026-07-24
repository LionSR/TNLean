/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.CycleMPSFundamentalTheorem
import TNLean.PEPS.NormalEdgeGaugeFamily

/-!
# The single-gauge form of the Fundamental Theorem for translation-invariant normal MPS

This file delivers the translation-invariant corollary of the Fundamental
Theorem for normal PEPS on the closed chain (arXiv:1804.04964, Section 3, the
corollary for TI MPS, lines 1624--1661 of
`Papers/1804.04964/paper_normal.tex`): two matrix tensors `A, B`, each
`L`-block injective, generating the same closed-chain state on `n ≥ 3L`
sites, are related by a *single* invertible matrix `Z` and a constant `λ`
with `λ^n = 1` through `B^i = λ · Z⁻¹ A^i Z`
(`fundamentalTheorem_normalMPS_translationInvariant`).  The gauge `Z` is
unique up to a multiplicative constant; the uniqueness clause
(`fundamentalTheorem_normalMPS_translationInvariant_gauge_unique`) is now
delivered by `TNLean/PEPS/CycleMPSOverlapCapstone.lean`.

The derivation collapses the per-bond gauge family of the matrix-form
corollary (`fundamentalTheorem_normalMPS`).  The per-bond relation
`B^i = Z_v⁻¹ A^i Z_{v+1}`, iterated along a word, conjugates every word
product of `B` by the gauges at the two ends of the word
(`evalWord_eq_conj_of_gaugeFamily`).  Comparing the iterated relation at
starting sites `v` and `v + 1` over the spanning length-`L` word products of
`A` shows that the two conjugations agree on the full matrix algebra, so
consecutive gauges differ by a nonzero scalar
(`gaugeFamily_succ_proportional`): the empty word pins the two bond
transports `Z_v⁻¹ Z_{v+L} = Z_{v+1}⁻¹ Z_{v+1+L}` to the same matrix, and the
centralizer of the full matrix algebra is the scalars.  The same-state
relation pins consecutive scalars against the nonzero tensor `B`, so a
single scalar `λ` relates all consecutive gauges; following the bonds once
around the closed chain returns to the starting bond, forcing `λ^n = 1`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, the corollary for TI MPS, lines 1624--1661 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix
open scoped Fin.NatCast

namespace TNLean
namespace PEPS

/-! ### Linear extension and centralizer helpers

Two-sided multiplication maps agreeing on a spanning set agree everywhere,
and two invertible matrices inducing the same two-sided conjugation of the
full matrix algebra are proportional. -/

/-- Two two-sided multiplication maps that agree on a spanning set of the
matrix algebra agree on every matrix. -/
private theorem conj_eq_conj_of_span {D : ℕ} {S : Set (Matrix (Fin D) (Fin D) ℂ)}
    (hS : Submodule.span ℂ S = ⊤) {P Q P' Q' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ M ∈ S, P * M * Q = P' * M * Q') (M : Matrix (Fin D) (Fin D) ℂ) :
    P * M * Q = P' * M * Q' := by
  have hmaps :
      (LinearMap.mulRight ℂ Q).comp (LinearMap.mulLeft ℂ P) =
        (LinearMap.mulRight ℂ Q').comp (LinearMap.mulLeft ℂ P') := by
    apply LinearMap.ext_on hS
    intro N hN
    simpa [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      using h N hN
  simpa [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    using congrArg (fun f => f M) hmaps

/-- **Proportionality from a shared two-sided conjugation.**  Two invertible
matrices `Z`, `Z'` with `Z⁻¹ W Z = Z'⁻¹ W Z'` for every matrix `W` differ by
a nonzero scalar.  This is the centralizer step of the closed-chain
collapse: `Z' Z⁻¹` commutes with the full matrix algebra, hence is a
scalar. -/
private theorem gl_proportional_of_conj_eq {D : ℕ} (Z Z' : GL (Fin D) ℂ)
    (h : ∀ W : Matrix (Fin D) (Fin D) ℂ,
      ((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * W *
          (Z : Matrix (Fin D) (Fin D) ℂ) =
        ((Z'⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * W *
          (Z' : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ c : ℂˣ, (Z' : Matrix (Fin D) (Fin D) ℂ) =
      (c : ℂ) • (Z : Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨c, hc⟩ := gl_conj_unique_scalar Z⁻¹ Z'⁻¹ fun N => by
    rw [inv_inv, inv_inv]
    exact h N
  have hflip := gl_inv_coe_smul hc
  rw [inv_inv, inv_inv] at hflip
  exact ⟨c⁻¹, hflip⟩

/-! ### Iterating the per-bond relation along a word -/

/-- **The per-bond gauge relation iterated along a word.**  If
`B^i = Z_v⁻¹ A^i Z_{v+1}` at every site of the closed chain, then every word
product of `B` is the word product of `A` conjugated by the gauges at the
two ends of the word: `B^{w} = Z_v⁻¹ A^{w} Z_{v+|w|}`, indices on the chain.

Source: arXiv:1804.04964, Section 3 — the step from the per-bond conclusion
of the first corollary after the theorem labelled `normal` (lines
1585--1622 of `Papers/1804.04964/paper_normal.tex`) towards its
translation-invariant form (lines 1624--1661). -/
theorem evalWord_eq_conj_of_gaugeFamily {n d D : ℕ} [NeZero n] {A B : MPSTensor d D}
    {Z : Fin n → GL (Fin D) ℂ}
    (hZ : ∀ (v : Fin n) (i : Fin d),
      B i = ((Z v)⁻¹ : GL (Fin D) ℂ) * A i * (Z (v + 1) : GL (Fin D) ℂ))
    (w : List (Fin d)) (v : Fin n) :
    MPSTensor.evalWord B w =
      ((Z v)⁻¹ : GL (Fin D) ℂ) * MPSTensor.evalWord A w *
        (Z (v + (w.length : Fin n)) : GL (Fin D) ℂ) := by
  induction w generalizing v with
  | nil =>
      simp only [MPSTensor.evalWord_nil, List.length_nil, Nat.cast_zero, add_zero,
        Matrix.mul_one, Units.inv_mul]
  | cons i w ih =>
      have hidx : v + ((i :: w).length : Fin n) = v + 1 + (w.length : Fin n) := by
        rw [List.length_cons, Nat.cast_add, Nat.cast_one, ← add_assoc, add_right_comm]
      rw [MPSTensor.evalWord_cons, MPSTensor.evalWord_cons, hZ v i, ih (v + 1), hidx]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

/-! ### Collapsing the per-bond family -/

/-- **Consecutive per-bond gauges are proportional.**  For an `L`-block
injective tensor `A`, the per-bond relation `B^i = Z_v⁻¹ A^i Z_{v+1}` at
every site forces consecutive gauges to differ by a nonzero scalar:
iterating the relation along the spanning length-`L` words from the
starting sites `v` and `v + 1` shows that conjugation by `Z_v` and by
`Z_{v+1}` agree on the full matrix algebra — the empty word pins the two
bond transports `Z_v⁻¹ Z_{v+L} = Z_{v+1}⁻¹ Z_{v+1+L}` to the same matrix —
and the centralizer of the full matrix algebra is the scalars.

Source: arXiv:1804.04964, Section 3, the corollary for TI MPS, lines
1624--1661 of `Papers/1804.04964/paper_normal.tex` — the collapse of the
per-bond gauges of the first corollary to a single gauge. -/
theorem gaugeFamily_succ_proportional {n L d D : ℕ} [NeZero n] {A B : MPSTensor d D}
    (hA : MPSTensor.IsNBlkInjective A L) {Z : Fin n → GL (Fin D) ℂ}
    (hZ : ∀ (v : Fin n) (i : Fin d),
      B i = ((Z v)⁻¹ : GL (Fin D) ℂ) * A i * (Z (v + 1) : GL (Fin D) ℂ)) (v : Fin n) :
    ∃ c : ℂˣ, (Z (v + 1) : Matrix (Fin D) (Fin D) ℂ) =
      (c : ℂ) • (Z v : Matrix (Fin D) (Fin D) ℂ) := by
  have hAspan : Submodule.span ℂ (Set.range fun σ : Fin L → Fin d =>
      MPSTensor.evalWord A (List.ofFn σ)) = ⊤ := hA
  -- The iterated relations at `v` and `v + 1` agree on the spanning word
  -- products, hence on every matrix.
  have hE : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      ((Z v)⁻¹ : GL (Fin D) ℂ) * M * (Z (v + (L : Fin n)) : GL (Fin D) ℂ) =
        ((Z (v + 1))⁻¹ : GL (Fin D) ℂ) * M *
          (Z (v + 1 + (L : Fin n)) : GL (Fin D) ℂ) := by
    refine conj_eq_conj_of_span hAspan ?_
    rintro M ⟨σ, rfl⟩
    have h1 := evalWord_eq_conj_of_gaugeFamily hZ (List.ofFn σ) v
    have h2 := evalWord_eq_conj_of_gaugeFamily hZ (List.ofFn σ) (v + 1)
    rw [List.length_ofFn] at h1 h2
    exact h1.symm.trans h2
  -- The empty word pins the two bond transports to the same matrix.
  have hG : (((Z v)⁻¹ * Z (v + (L : Fin n)) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      (((Z (v + 1))⁻¹ * Z (v + 1 + (L : Fin n)) : GL (Fin D) ℂ) :
        Matrix (Fin D) (Fin D) ℂ) := by
    have h1 := hE 1
    rw [Matrix.mul_one, Matrix.mul_one] at h1
    rw [Units.val_mul, Units.val_mul]
    exact h1
  have hGu : ((Z v)⁻¹ * Z (v + (L : Fin n)) : GL (Fin D) ℂ) =
      (Z (v + 1))⁻¹ * Z (v + 1 + (L : Fin n)) := Units.ext hG
  -- Cancelling the common bond transport leaves equal conjugations.
  have hconj : ∀ W : Matrix (Fin D) (Fin D) ℂ,
      ((Z v)⁻¹ : GL (Fin D) ℂ) * W * (Z v : Matrix (Fin D) (Fin D) ℂ) =
        ((Z (v + 1))⁻¹ : GL (Fin D) ℂ) * W * (Z (v + 1) : Matrix (Fin D) (Fin D) ℂ) := by
    intro W
    have h := hE W
    have hsplit : (Z (v + (L : Fin n)) : Matrix (Fin D) (Fin D) ℂ) =
        (Z v : Matrix (Fin D) (Fin D) ℂ) *
          (((Z v)⁻¹ * Z (v + (L : Fin n)) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [← Units.val_mul, mul_inv_cancel_left]
    have hsplit' : (Z (v + 1 + (L : Fin n)) : Matrix (Fin D) (Fin D) ℂ) =
        (Z (v + 1) : Matrix (Fin D) (Fin D) ℂ) *
          (((Z v)⁻¹ * Z (v + (L : Fin n)) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [hGu, ← Units.val_mul, mul_inv_cancel_left]
    rw [hsplit, hsplit'] at h
    simp only [← Matrix.mul_assoc] at h
    exact (Units.isUnit ((Z v)⁻¹ * Z (v + (L : Fin n)))).mul_right_cancel h
  exact gl_proportional_of_conj_eq (Z v) (Z (v + 1)) hconj

/-! ### The translation-invariant corollary -/

/-- **Fundamental Theorem for translation-invariant normal MPS, single-gauge
form** (arXiv:1804.04964, Section 3, the corollary for TI MPS; strengthened
to the optimal system size of the alternative proof of its Section
`normal_alt`).

Two matrix tensors `A` and `B` on `n ≥ 2L + 1` sites, each `L`-block
injective — the matrix form of "blocking `L` consecutive sites results in an
injective tensor" — generating the same closed-chain state at the single
size `n`, are related by one invertible matrix `Z` and a constant `λ` with
`λ^n = 1` through `B^i = λ · Z⁻¹ A^i Z` for every `i`.

The system size is the optimal `n ≥ 2L + 1` of the source's alternative
proof (line 1623 and Section `normal_alt`, the corollary after Lemma 5),
rather than the `n ≥ 3L` of the Section-`normal` blocking route: the proof
delegates to the overlapping-window corollary
`fundamentalTheorem_normalMPS_translationInvariant_of_overlap`.

Source: arXiv:1804.04964, Section 3, the corollary for TI MPS, lines
1624--1661 of `Papers/1804.04964/paper_normal.tex`, strengthened to
`n ≥ 2L + 1` per line 1623 and Section `normal_alt`. -/
theorem fundamentalTheorem_normalMPS_translationInvariant {n L d D : ℕ} [NeZero n]
    (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (hD : 0 < D) (A B : MPSTensor d D)
    (hA : MPSTensor.IsNBlkInjective A L) (hB : MPSTensor.IsNBlkInjective B L)
    (hAB : ∀ σ : Fin n → Fin d, MPSTensor.mpv A σ = MPSTensor.mpv B σ) :
    ∃ (Z : GL (Fin D) ℂ) (lam : ℂ), lam ^ n = 1 ∧
      ∀ i : Fin d, B i = lam • ((Z⁻¹ : GL (Fin D) ℂ) * A i * (Z : GL (Fin D) ℂ)) :=
  fundamentalTheorem_normalMPS_translationInvariant_of_overlap hL hn hD A B hA hB hAB

end PEPS
end TNLean
