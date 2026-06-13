import TNLean.PEPS.CycleMPSWordTransport
import TNLean.PEPS.CycleMPSChainOverlapWindow

/-!
# Bond-operator extraction from overlapping windows on the closed chain

This file states the matrix-tensor form of Lemma 5 of arXiv:1804.04964
(lines 2045--2255 of `Papers/1804.04964/paper_normal.tex`), specialized to
one site-independent tensor: if a deformation of a closed-chain state of a
block-injective tensor `B` is realized by operators on each of the `L + 1`
overlapping length-`L` windows around a bond — equivalently, by deformed
window tensors `C 0, …, C L`, where `C j` replaces the blocked tensor of the
window starting `j` sites left of the bond — then the deformation is a
single virtual operation `X` on the bond:

* `C 0` factors as the window product times `X` on the right, and `C L` as
  `X` on the left of the window product
  (`MPSTensor.overlapWindow_exists_bondOperator`), and
* `X` is unique (`MPSTensor.bondOperator_unique`).

The proofs specialize the site-dependent form of Lemma 5
(`TNLean/PEPS/CycleMPSChainOverlapWindow.lean`), which is the setting in
which the source states the lemma, through the constant chain placing `B`
at every site: the arc products of the constant chain are the word products
of `B`, and block injectivity of `B` is window injectivity of the constant
chain.  This specialized form is the one consumed by the closed-chain
corollaries of Section `normal_alt` for one repeated tensor.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Lemma 5 of Section `normal_alt`, lines 2045--2255 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Uniqueness of the bond operator -/

/-- **Uniqueness of the bond operator** (arXiv:1804.04964, Lemma 5: the maps
to `X` "are uniquely defined", lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`; the mechanism is the insertion
uniqueness of lines 1940--1960).

Two matrices multiplying every spanning word product to the same family on
the right are equal.  This is the spanning-family uniqueness
`MPSChainTensor.eq_of_span_mul_left` read on the word products of one
block-injective tensor. -/
theorem bondOperator_unique {B : MPSTensor d D} {L : ℕ}
    (hB : IsNBlkInjective B L) {X X' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ a : Fin L → Fin d,
      evalWord B (List.ofFn a) * X = evalWord B (List.ofFn a) * X') : X = X' :=
  MPSChainTensor.eq_of_span_mul_left
    (W := fun a : Fin L → Fin d => evalWord B (List.ofFn a)) hB h

/-! ### Extracting the bond operator from the two ends -/

/-- **Bond-operator extraction from an intertwining pair** (arXiv:1804.04964,
Lemma 5, the comparison of the two ends, lines 2211--2255 of
`Papers/1804.04964/paper_normal.tex`, after the model of
`eq:inj_O->X_argument`, line 377).

If `F a ⬝ B^b = B^a ⬝ G b` for all length-`L` words `a`, `b`, with the word
products of `B` spanning, then a single matrix `X` factors both families:
`F` is the word products times `X` on the right, `G` is `X` times the word
products.  This is the spanning-family extraction
`MPSChainTensor.exists_bondOperator_of_intertwine_span` with both spanning
families the word products of `B`. -/
theorem exists_bondOperator_of_intertwine {B : MPSTensor d D} {L : ℕ}
    (hB : IsNBlkInjective B L)
    (F G : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ a b : Fin L → Fin d,
      F a * evalWord B (List.ofFn b) = evalWord B (List.ofFn a) * G b) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      (∀ a, F a = evalWord B (List.ofFn a) * X) ∧
        (∀ b, G b = X * evalWord B (List.ofFn b)) :=
  MPSChainTensor.exists_bondOperator_of_intertwine_span
    (W₁ := fun a : Fin L → Fin d => evalWord B (List.ofFn a))
    (W₂ := fun b : Fin L → Fin d => evalWord B (List.ofFn b)) hB hB F G h

/-! ### The bond-operator extraction theorem -/

/-- **Lemma 5 of arXiv:1804.04964 for matrix tensors** (lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`, specialized to one site-independent
tensor).

Let `B` be `L`-block injective on a closed chain of `n ≥ 2L + 1` sites, and
let `C 0, …, C L` be deformed window tensors — `C j` replaces the blocked
tensor of the `L`-site window starting `j` sites left of a fixed bond; in the
source, `C j` is the physical operator `O_{j+1}` contracted with the blocked
window it acts on.  If the deformed states agree for consecutive window
positions — the hypothesis quantifies the closed-chain coefficient over a
common refinement: a prefix of `j` sites, the `L + 1` sites covered by the
two windows, and the remaining sites — then the deformation is a virtual
operation on the bond: a single matrix `X` with `C 0` the window products
times `X` on the right and `C L` equal to `X` times the window products.

Together with `MPSTensor.bondOperator_unique`, the assignments `C 0 ↦ X` and
`C L ↦ X` are uniquely defined; their algebra-homomorphism property (the
source's maps `O_1 ↦ X` and `O_3^T ↦ X`) is established for the insertion
correspondence in `TNLean/PEPS/CycleMPSOverlapInsertion.lean`, where the
deformed window tensors carry the algebra structure transported from the
deforming network.

The proof places `B` at every site of the site-dependent form
(`MPSChainTensor.overlapWindow_exists_bondOperator`), which is the setting
in which the source states Lemma 5. -/
theorem overlapWindow_exists_bondOperator {B : MPSTensor d D} {n L : ℕ}
    (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (hB : IsNBlkInjective B L)
    (C : ℕ → (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hstate : ∀ j, j < L → ∀ {q : ℕ}, j + (L + 1) + q = n →
      ∀ (pre : Fin j → Fin d) (u : Fin (L + 1) → Fin d) (post : Fin q → Fin d),
      Matrix.trace (evalWord B (List.ofFn pre) *
          (C j (Fin.init u) * B (u (Fin.last L))) * evalWord B (List.ofFn post)) =
        Matrix.trace (evalWord B (List.ofFn pre) *
          (B (u 0) * C (j + 1) (Fin.tail u)) * evalWord B (List.ofFn post))) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      (∀ a, C 0 a = evalWord B (List.ofFn a) * X) ∧
        (∀ b, C L b = X * evalWord B (List.ofFn b)) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨X, hX0, hXL⟩ := MPSChainTensor.overlapWindow_exists_bondOperator
    (A := fun _ : Fin n => B) hL hn
    (MPSChainTensor.isWindowInjective_const hB) 0 C
    (fun j hj {q} hq pre u post => by
      simpa only [MPSChainTensor.arcEval_const] using hstate j hj hq pre u post)
  refine ⟨X, fun a => ?_, fun b => ?_⟩
  · rw [hX0 a, MPSChainTensor.arcEval_const]
  · rw [hXL b, MPSChainTensor.arcEval_const]

end MPSTensor
