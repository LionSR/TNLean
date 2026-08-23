/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.CycleMPSFundamentalTheorem

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
proved in `TNLean/PEPS/CycleMPSOverlapCapstone.lean`.

The derivation collapses the per-bond gauge family of the matrix-form
corollary (`fundamentalTheorem_normalMPS`).  The per-bond relation
`B^i = Z_v⁻¹ A^i Z_{v+1}`, iterated along a word, conjugates every word
product of `B` by the gauges at the two ends of the word
(`evalWord_eq_conj_of_gaugeFamily`).  Comparing the iterated relation at
starting sites `v` and `v + 1` over the spanning length-`L` word products of
`A` shows that the two conjugations agree on the full matrix algebra, so
consecutive gauges differ by a nonzero scalar
(`gaugeFamily_succ_proportional`): taking the identity pins the two bond
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

/-! ### Collapsing the per-bond family -/

/-- **Consecutive per-bond gauges are proportional.**  For an `L`-block
injective tensor `A`, the per-bond relation `B^i = Z_v⁻¹ A^i Z_{v+1}` at
every site forces consecutive gauges to differ by a nonzero scalar:
iterating the relation along the spanning length-`L` words from the
starting sites `v` and `v + 1` shows that conjugation by `Z_v` and by
`Z_{v+1}` agree on the full matrix algebra — taking the identity pins the
two bond transports `Z_v⁻¹ Z_{v+L} = Z_{v+1}⁻¹ Z_{v+1+L}` to the same matrix —
and the centralizer of the full matrix algebra is the scalars.

Source: arXiv:1804.04964, Section 3, the corollary for TI MPS, lines
1624--1661 of `Papers/1804.04964/paper_normal.tex` — the collapse of the
per-bond gauges of the first corollary to a single gauge. -/
theorem gaugeFamily_succ_proportional {n L d D : ℕ} [NeZero n] {A B : MPSTensor d D}
    (hA : Kraus.IsNBlkInjective A L) {Z : Fin n → GL (Fin D) ℂ}
    (hZ : ∀ (v : Fin n) (i : Fin d),
      B i = ((Z v)⁻¹ : GL (Fin D) ℂ) * A i * (Z (v + 1) : GL (Fin D) ℂ)) (v : Fin n) :
    ∃ c : ℂˣ, (Z (v + 1) : Matrix (Fin D) (Fin D) ℂ) =
      (c : ℂ) • (Z v : Matrix (Fin D) (Fin D) ℂ) := by
  have hAspan : Submodule.span ℂ (Set.range fun σ : Fin L → Fin d =>
      Kraus.evalWord A (List.ofFn σ)) = ⊤ := hA
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
  exact gl_proportional_of_transport_eq (Z v) (Z (v + (L : Fin n))) (Z (v + 1))
    (Z (v + 1 + (L : Fin n))) hE

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
    (hA : Kraus.IsNBlkInjective A L) (hB : Kraus.IsNBlkInjective B L)
    (hAB : ∀ σ : Fin n → Fin d, MPSTensor.mpv A σ = MPSTensor.mpv B σ) :
    ∃ (Z : GL (Fin D) ℂ) (lam : ℂ), lam ^ n = 1 ∧
      ∀ i : Fin d, B i = lam • ((Z⁻¹ : GL (Fin D) ℂ) * A i * (Z : GL (Fin D) ℂ)) :=
  fundamentalTheorem_normalMPS_translationInvariant_of_overlap hL hn hD A B hA hB hAB

end PEPS
end TNLean
