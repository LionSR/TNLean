import TNLean.PEPS.CycleMPSOverlapWindow
import TNLean.Algebra.SkolemNoether

/-!
# The insertion correspondence of the overlapping-window route

This file applies the bond-operator extraction of
`TNLean/PEPS/CycleMPSOverlapWindow.lean` — the matrix-tensor form of Lemma 5
of arXiv:1804.04964 (lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`) — to two `L`-block-injective tensors
`A`, `B` generating the same closed-chain state on `n ≥ 2L + 1` sites, and
delivers the conjugation between the two networks at length `n`
(`MPSTensor.exists_conjugation_of_mpv_eq`):
an invertible matrix `Z` with `B^w = Z ⬝ A^w ⬝ Z⁻¹` for every word `w` of
length `n`.

The route follows the source's derivation of the `n ≥ 2L + 1` corollary from
Lemma 5 (lines 1961--2043 for the forward realization, lines 2045--2295 for
the converse and the corollary):

1. A virtual insertion `X` on a bond of the `A`-network is realized on each
   of the `L + 1` overlapping windows around the bond
   (`eq:normal_resonate`, lines 1961--2043): the deformed window tensor at
   position `j` places `X` after the first `L - j` letters of the window.
2. The deformed window tensors are transported to the `B`-network by the word
   transport `Λ` of `TNLean/PEPS/CycleMPSWordTransport.lean`; the same-state
   hypothesis makes the transported deformations generate one common state.
3. Lemma 5 for the `B`-network extracts a bond operator `Y = Φ X`, with
   `Λ (A^a ⬝ X) = B^a ⬝ Φ X` and `Λ (X ⬝ A^b) = Φ X ⬝ B^b` on all window
   words.  Uniqueness of the bond operator makes `X ↦ Φ X` linear, unital and
   multiplicative — the source's algebra-homomorphism clause for
   `O_1 ↦ X` and `O_3^T ↦ X` (line 2253).
4. A unital multiplicative endomorphism of a full matrix algebra is an
   automorphism, and by Skolem--Noether it is inner: `Φ X = Z⁻¹ ⬝ X ⬝ Z`
   (the source's `Y = Z⁻¹ X Z`, lines 582--584 in the injective case).
   Pairing the insertions against all closed-chain words turns the relation
   `⟨X, A^w⟩ = ⟨Φ X, B^w⟩` into the conjugation `B^w = Z ⬝ A^w ⬝ Z⁻¹` at
   length `n`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section `normal_alt`, lines 1915--2295 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Words with one insertion -/

/-- The word product with a matrix inserted after the first `p` letters: the
matrix-tensor form of the deformed window tensors of arXiv:1804.04964,
`eq:X->O` (line 333) and the windows of `eq:normal_resonate` (lines
1961--2043 of `Papers/1804.04964/paper_normal.tex`). -/
private noncomputable def insertedWord (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (p : ℕ) (w : List (Fin d)) : Matrix (Fin D) (Fin D) ℂ :=
  evalWord A (w.take p) * X * evalWord A (w.drop p)

private theorem insertedWord_length (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) {w : List (Fin d)} {p : ℕ} (hp : w.length ≤ p) :
    insertedWord A X p w = evalWord A w * X := by
  rw [insertedWord, List.take_of_length_le hp, List.drop_of_length_le hp,
    evalWord_nil, Matrix.mul_one]

private theorem insertedWord_zero (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)) :
    insertedWord A X 0 w = X * evalWord A w := by
  rw [insertedWord, List.take_zero, List.drop_zero, evalWord_nil, Matrix.one_mul]

/-- Appending a letter beyond the insertion point. -/
private theorem insertedWord_append_letter (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) {p : ℕ} {w : List (Fin d)} (hp : p ≤ w.length)
    (i : Fin d) :
    insertedWord A X p w * A i = insertedWord A X p (w ++ [i]) := by
  rw [insertedWord, insertedWord, List.take_append_of_le_length hp,
    List.drop_append_of_le_length hp, evalWord_append]
  simp only [evalWord_cons, evalWord_nil, Matrix.mul_one, Matrix.mul_assoc]

/-- Prepending a letter before the insertion point. -/
private theorem insertedWord_cons_letter (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (p : ℕ) (w : List (Fin d)) (i : Fin d) :
    A i * insertedWord A X p w = insertedWord A X (p + 1) (i :: w) := by
  rw [insertedWord, insertedWord, List.take_succ_cons, List.drop_succ_cons,
    evalWord_cons]
  simp only [Matrix.mul_assoc]

/-! ### The transported deformation generates the inserted state -/

/-- **The transport intertwines the closed-chain pairings**
(arXiv:1804.04964, the mechanism of Lemma 5, lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`): expanding any matrix `M` over the
window products of `A` and re-reading the expansion in the `B`-network leaves
every closed-chain coefficient of total length `n` unchanged. -/
private theorem trace_transport_sandwich {A B : MPSTensor d D} {n L : ℕ}
    (hA : IsNBlkInjective A L)
    (hAB : ∀ σ : Fin n → Fin d, mpv A σ = mpv B σ)
    {Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hΛ : ∀ τ : Fin L → Fin d,
      Λ (evalWord A (List.ofFn τ)) = evalWord B (List.ofFn τ))
    (M : Matrix (Fin D) (Fin D) ℂ) (pre post : List (Fin d))
    (hlen : pre.length + L + post.length = n) :
    Matrix.trace (evalWord B pre * Λ M * evalWord B post) =
      Matrix.trace (evalWord A pre * M * evalWord A post) := by
  classical
  have hspan : Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
      evalWord A (List.ofFn τ)) = ⊤ := hA
  have hM : M ∈ Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
      evalWord A (List.ofFn τ)) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp hM
  have hΛM : Λ M = ∑ τ : Fin L → Fin d, c τ • evalWord B (List.ofFn τ) := by
    rw [← hc, map_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [map_smul, hΛ τ]
  have decomp : ∀ (T : MPSTensor d D) (N : Matrix (Fin D) (Fin D) ℂ),
      N = (∑ τ : Fin L → Fin d, c τ • evalWord T (List.ofFn τ)) →
      Matrix.trace (evalWord T pre * N * evalWord T post) =
        ∑ τ : Fin L → Fin d,
          c τ * Matrix.trace (evalWord T (pre ++ (List.ofFn τ ++ post))) := by
    intro T N hN
    rw [hN, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
    congr 1
    rw [evalWord_append, evalWord_append, Matrix.mul_assoc]
  rw [decomp B (Λ M) hΛM, decomp A M hc.symm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  exact (trace_evalWord_eq_of_mpv_eq hAB (by simp; omega)).symm

/-! ### The insertion correspondence -/

/-- **The insertion correspondence at one bond** (arXiv:1804.04964, Lemma 5
applied to the deformations realizing a virtual insertion, lines 1961--2255
of `Papers/1804.04964/paper_normal.tex`): for every insertion `X` on the
`A`-network there is a unique `Y` on the `B`-network with
`Λ (A^a ⬝ X) = B^a ⬝ Y` and `Λ (X ⬝ A^b) = Y ⬝ B^b` on all window words. -/
private theorem exists_insertion_image {A B : MPSTensor d D} {n L : ℕ}
    (hL : 0 < L) (hn : 2 * L + 1 ≤ n)
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hAB : ∀ σ : Fin n → Fin d, mpv A σ = mpv B σ)
    {Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hΛ : ∀ τ : Fin L → Fin d,
      Λ (evalWord A (List.ofFn τ)) = evalWord B (List.ofFn τ))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      (∀ a : Fin L → Fin d,
        Λ (evalWord A (List.ofFn a) * X) = evalWord B (List.ofFn a) * Y) ∧
        (∀ b : Fin L → Fin d,
          Λ (X * evalWord A (List.ofFn b)) = Y * evalWord B (List.ofFn b)) := by
  classical
  -- The deformed window tensors transported to the `B`-network.
  set C : ℕ → (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun j s => Λ (insertedWord A X (L - j) (List.ofFn s)) with hC
  -- All transported deformations generate the same state: each one matches
  -- the `A`-state with `X` inserted on the bond.
  have hstate : ∀ j, j < L → ∀ {q : ℕ}, j + (L + 1) + q = n →
      ∀ (pre : Fin j → Fin d) (u : Fin (L + 1) → Fin d) (post : Fin q → Fin d),
      Matrix.trace (evalWord B (List.ofFn pre) *
          (C j (Fin.init u) * B (u (Fin.last L))) * evalWord B (List.ofFn post)) =
        Matrix.trace (evalWord B (List.ofFn pre) *
          (B (u 0) * C (j + 1) (Fin.tail u)) * evalWord B (List.ofFn post)) := by
    intro j hj q hq pre u post
    have hlen_init : (List.ofFn (Fin.init u)).length = L := by simp
    have hlen_tail : (List.ofFn (Fin.tail u)).length = L := by simp
    -- The left side: absorb the trailing letter into the suffix, transport,
    -- and push the letter back into the deformed word.
    have hleft : Matrix.trace (evalWord B (List.ofFn pre) *
        (C j (Fin.init u) * B (u (Fin.last L))) * evalWord B (List.ofFn post)) =
        Matrix.trace (evalWord A (List.ofFn pre) *
          insertedWord A X (L - j) (List.ofFn u) * evalWord A (List.ofFn post)) := by
      have e1 : evalWord B (List.ofFn pre) *
          (C j (Fin.init u) * B (u (Fin.last L))) * evalWord B (List.ofFn post) =
          evalWord B (List.ofFn pre) * C j (Fin.init u) *
            evalWord B (u (Fin.last L) :: List.ofFn post) := by
        rw [evalWord_cons]
        simp only [Matrix.mul_assoc]
      rw [e1, hC]
      rw [trace_transport_sandwich hA hAB hΛ _ (List.ofFn pre)
        (u (Fin.last L) :: List.ofFn post) (by simp; omega)]
      have e2 : evalWord A (List.ofFn pre) *
          insertedWord A X (L - j) (List.ofFn (Fin.init u)) *
            evalWord A (u (Fin.last L) :: List.ofFn post) =
          evalWord A (List.ofFn pre) *
            (insertedWord A X (L - j) (List.ofFn (Fin.init u)) * A (u (Fin.last L))) *
              evalWord A (List.ofFn post) := by
        rw [evalWord_cons]
        simp only [Matrix.mul_assoc]
      rw [e2, insertedWord_append_letter A X (by omega : L - j ≤
        (List.ofFn (Fin.init u)).length) (u (Fin.last L))]
      have e3 : List.ofFn (Fin.init u) ++ [u (Fin.last L)] = List.ofFn u := by
        rw [List.ofFn_succ' u, List.concat_eq_append]
        rfl
      rw [e3]
    -- The right side: absorb the leading letter into the prefix, transport,
    -- and push the letter back into the deformed word.
    have hright : Matrix.trace (evalWord B (List.ofFn pre) *
        (B (u 0) * C (j + 1) (Fin.tail u)) * evalWord B (List.ofFn post)) =
        Matrix.trace (evalWord A (List.ofFn pre) *
          insertedWord A X (L - j) (List.ofFn u) * evalWord A (List.ofFn post)) := by
      have e1 : evalWord B (List.ofFn pre) *
          (B (u 0) * C (j + 1) (Fin.tail u)) * evalWord B (List.ofFn post) =
          evalWord B (List.ofFn pre ++ [u 0]) * C (j + 1) (Fin.tail u) *
            evalWord B (List.ofFn post) := by
        rw [evalWord_append]
        simp only [evalWord_cons, evalWord_nil, Matrix.mul_one, Matrix.mul_assoc]
      rw [e1, hC]
      rw [trace_transport_sandwich hA hAB hΛ _ (List.ofFn pre ++ [u 0])
        (List.ofFn post) (by simp; omega)]
      have e2 : evalWord A (List.ofFn pre ++ [u 0]) *
          insertedWord A X (L - (j + 1)) (List.ofFn (Fin.tail u)) *
            evalWord A (List.ofFn post) =
          evalWord A (List.ofFn pre) *
            (A (u 0) * insertedWord A X (L - (j + 1)) (List.ofFn (Fin.tail u))) *
              evalWord A (List.ofFn post) := by
        rw [evalWord_append]
        simp only [evalWord_cons, evalWord_nil, Matrix.mul_one, Matrix.mul_assoc]
      rw [e2, insertedWord_cons_letter A X (L - (j + 1)) (List.ofFn (Fin.tail u))
        (u 0)]
      have e3 : u 0 :: List.ofFn (Fin.tail u) = List.ofFn u := by
        rw [List.ofFn_succ (f := u)]
        rfl
      have e4 : L - (j + 1) + 1 = L - j := by omega
      rw [e3, e4]
    rw [hleft, hright]
  -- Lemma 5 extracts the bond operator.
  obtain ⟨Y, hY1, hY2⟩ := overlapWindow_exists_bondOperator hL hn hB C hstate
  refine ⟨Y, fun a => ?_, fun b => ?_⟩
  · have h0 := hY1 a
    simp only [hC, Nat.sub_zero] at h0
    rw [← insertedWord_length A X (p := L) (by simp : (List.ofFn a).length ≤ L)]
    exact h0
  · have hL0 := hY2 b
    simp only [hC, Nat.sub_self, insertedWord_zero] at hL0
    exact hL0

/-! ### Assembling the conjugation -/

/-- A nonzero-size identity matrix is nonzero. -/
private theorem matrix_one_ne_zero (hD : 0 < D) :
    (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h ⟨0, hD⟩) ⟨0, hD⟩
  rw [Matrix.one_apply_eq] at hentry
  exact one_ne_zero hentry

/-- Any list of declared length is the word of a tuple. -/
private theorem exists_ofFn_of_length {l : List (Fin d)} {k : ℕ}
    (hl : l.length = k) : ∃ a : Fin k → Fin d, List.ofFn a = l := by
  subst hl
  exact ⟨l.get, List.ofFn_get l⟩

/-- **The conjugation between two same-state networks at length `n ≥ 2L + 1`**
(arXiv:1804.04964, Lemma 5 and the first half of the closed-chain corollary
of Section `normal_alt`, lines 1961--2295 of
`Papers/1804.04964/paper_normal.tex`, specialized to one site-independent
tensor).

Two `L`-block-injective tensors with the same closed-chain coefficients at
one length `n ≥ 2L + 1` have conjugate word products at length `n`: there is
an invertible `Z` with `B^w = Z ⬝ A^w ⬝ Z⁻¹` for every word `w` of length
`n`.  The insertion correspondence `X ↦ Y` built from Lemma 5 is linear by
uniqueness of the bond operator, unital and multiplicative — the source's
algebra-homomorphism clause (line 2253) — hence an automorphism of the full
matrix algebra, and by Skolem--Noether (the source's argument at lines
582--584) it is conjugation by some `Z`; pairing insertions against all
closed-chain words of length `n` transfers the conjugation to the word
products. -/
theorem exists_conjugation_of_mpv_eq {n L : ℕ} (hL : 0 < L) (hn : 2 * L + 1 ≤ n)
    (A B : MPSTensor d D) (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hAB : ∀ σ : Fin n → Fin d, mpv A σ = mpv B σ) :
    ∃ Z : GL (Fin D) ℂ, ∀ w : List (Fin d), w.length = n →
      evalWord B w = (Z : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
        ((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · -- All `0 × 0` matrices are equal.
    subst hD0
    refine ⟨1, fun w hw => ?_⟩
    apply Matrix.ext
    intro a b
    exact a.elim0
  -- The word transport from the same-state hypothesis.
  obtain ⟨Λ, hΛ⟩ := exists_mpvTransport (k := L) (q := n - L) (by omega) hA
    (isNBlkInjective_of_le hL hA (by omega)) hAB
  -- The insertion correspondence, with its defining identities.
  have hins := exists_insertion_image hL hn hA hB hAB hΛ
  -- The identity decomposition over the `B`-window products.
  have hspanB : Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
      evalWord B (List.ofFn τ)) = ⊤ := hB
  have h1B : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
      (Set.range fun τ : Fin L → Fin d => evalWord B (List.ofFn τ)) :=
    hspanB ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1B
  -- The correspondence as a linear map.
  set Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    ∑ b : Fin L → Fin d, α b •
      (Λ ∘ₗ LinearMap.mulRight ℂ (evalWord A (List.ofFn b))) with hΦdef
  have hΦ_apply : ∀ X, Φ X = ∑ b : Fin L → Fin d,
      α b • Λ (X * evalWord A (List.ofFn b)) := by
    intro X
    rw [hΦdef]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.mulRight_apply]
  -- `Φ X` is the bond operator of `X`.
  have hΦY : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      (∀ a : Fin L → Fin d,
        Λ (evalWord A (List.ofFn a) * X) = evalWord B (List.ofFn a) * Φ X) ∧
        (∀ b : Fin L → Fin d,
          Λ (X * evalWord A (List.ofFn b)) = Φ X * evalWord B (List.ofFn b)) := by
    intro X
    obtain ⟨Y, hY1, hY2⟩ := hins X
    have hYΦ : Φ X = Y := by
      rw [hΦ_apply]
      calc (∑ b : Fin L → Fin d, α b • Λ (X * evalWord A (List.ofFn b)))
          = ∑ b : Fin L → Fin d, α b • (Y * evalWord B (List.ofFn b)) :=
            Finset.sum_congr rfl fun b _ => by rw [hY2 b]
        _ = ∑ b : Fin L → Fin d, Y * (α b • evalWord B (List.ofFn b)) :=
            Finset.sum_congr rfl fun b _ =>
              (mul_smul_comm (α b) Y (evalWord B (List.ofFn b))).symm
        _ = Y * ∑ b : Fin L → Fin d, α b • evalWord B (List.ofFn b) := by
            rw [← Finset.mul_sum]
        _ = Y := by rw [hα, Matrix.mul_one]
    rw [hYΦ]
    exact ⟨hY1, hY2⟩
  have hΦ1 : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (a : Fin L → Fin d),
      Λ (evalWord A (List.ofFn a) * X) = evalWord B (List.ofFn a) * Φ X :=
    fun X => (hΦY X).1
  have hΦ2 : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (b : Fin L → Fin d),
      Λ (X * evalWord A (List.ofFn b)) = Φ X * evalWord B (List.ofFn b) :=
    fun X => (hΦY X).2
  -- The right-multiplication relation extends from window products to all
  -- matrices, making `Φ` multiplicative.
  have hΛr : ∀ (X M : Matrix (Fin D) (Fin D) ℂ), Λ (M * X) = Λ M * Φ X := by
    intro X
    have hext := LinearMap.ext_on_range
      (v := fun a : Fin L → Fin d => evalWord A (List.ofFn a)) (hv := hA)
      (f := Λ ∘ₗ LinearMap.mulRight ℂ X)
      (g := (LinearMap.mulRight ℂ (Φ X)) ∘ₗ Λ)
      (fun a => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
        rw [hΦ1 X a, hΛ a])
    intro M
    have := congrArg (· M) hext
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply] using this
  have hΦmul : ∀ M N : Matrix (Fin D) (Fin D) ℂ, Φ (M * N) = Φ M * Φ N := by
    intro M N
    apply bondOperator_unique hB
    intro a
    calc evalWord B (List.ofFn a) * Φ (M * N)
        = Λ (evalWord A (List.ofFn a) * (M * N)) := (hΦ1 (M * N) a).symm
      _ = Λ ((evalWord A (List.ofFn a) * M) * N) := by rw [Matrix.mul_assoc]
      _ = Λ (evalWord A (List.ofFn a) * M) * Φ N := hΛr N _
      _ = (evalWord B (List.ofFn a) * Φ M) * Φ N := by rw [hΦ1 M a]
      _ = evalWord B (List.ofFn a) * (Φ M * Φ N) := Matrix.mul_assoc _ _ _
  -- `Φ` is unital, hence nonzero, hence an automorphism.
  have hΦone : Φ 1 = 1 := by
    apply bondOperator_unique hB (X := Φ 1) (X' := 1)
    intro a
    calc evalWord B (List.ofFn a) * Φ 1
        = Λ (evalWord A (List.ofFn a) * 1) := (hΦ1 1 a).symm
      _ = Λ (evalWord A (List.ofFn a)) := by rw [Matrix.mul_one]
      _ = evalWord B (List.ofFn a) := hΛ a
      _ = evalWord B (List.ofFn a) * 1 := (Matrix.mul_one _).symm
  have hΦne : Φ ≠ 0 := by
    intro h0
    apply matrix_one_ne_zero hD
    rw [← hΦone, h0]
    rfl
  have hBij := linear_mul_endomorphism_bijective Φ hΦmul hΦne
  let fHom := linearMapToAlgHom Φ hΦmul hBij.surjective
  let f := AlgEquiv.ofBijective fHom hBij
  obtain ⟨P, hP⟩ := skolemNoether_matrix f
  have hΦP : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Φ X = (P : Matrix (Fin D) (Fin D) ℂ) * X *
        ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro X
    have : f X = Φ X := rfl
    rw [← this]
    exact hP X
  -- The closed-chain pairing of insertions, in cyclic form.
  have hpair : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)),
      w.length = n →
      Matrix.trace (X * evalWord A w) = Matrix.trace (Φ X * evalWord B w) := by
    intro X w hw
    -- Split the word into its head of length `n - L` and tail window.
    have hdrop : (w.drop (n - L)).length = L := by
      rw [List.length_drop]
      omega
    obtain ⟨a, ha⟩ := exists_ofFn_of_length hdrop
    have hsplit : w = w.take (n - L) ++ List.ofFn a := by
      rw [ha, List.take_append_drop]
    have htake : (w.take (n - L)).length = n - L := by
      rw [List.length_take]
      omega
    -- The sandwich relation at the window, from the transport bridge.
    have hsand : Matrix.trace (Λ (evalWord A (List.ofFn a) * X) *
        evalWord B (w.take (n - L))) =
        Matrix.trace (evalWord A (List.ofFn a) * X * evalWord A (w.take (n - L))) := by
      have hb := trace_transport_sandwich hA hAB hΛ
        (evalWord A (List.ofFn a) * X) [] (w.take (n - L)) (by simp [htake]; omega)
      simpa only [evalWord_nil, Matrix.one_mul] using hb
    calc Matrix.trace (X * evalWord A w)
        = Matrix.trace (X * (evalWord A (w.take (n - L)) *
            evalWord A (List.ofFn a))) := by
          rw [← evalWord_append, ← hsplit]
      _ = Matrix.trace (evalWord A (List.ofFn a) * (X *
            evalWord A (w.take (n - L)))) := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (evalWord A (List.ofFn a) * X *
            evalWord A (w.take (n - L))) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (Λ (evalWord A (List.ofFn a) * X) *
            evalWord B (w.take (n - L))) := hsand.symm
      _ = Matrix.trace (evalWord B (List.ofFn a) * Φ X *
            evalWord B (w.take (n - L))) := by rw [hΦ1 X a]
      _ = Matrix.trace (Φ X * (evalWord B (w.take (n - L)) *
            evalWord B (List.ofFn a))) := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
            Matrix.mul_assoc]
      _ = Matrix.trace (Φ X * evalWord B w) := by
          rw [← evalWord_append, ← hsplit]
  -- Strip the insertions: the word products are conjugate.
  refine ⟨P, fun w hw => ?_⟩
  have hAw : evalWord A w =
      ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * evalWord B w *
        (P : Matrix (Fin D) (Fin D) ℂ) := by
    apply (Matrix.ext_iff_trace_mul_left).2
    intro X
    calc Matrix.trace (X * evalWord A w)
        = Matrix.trace (Φ X * evalWord B w) := hpair X w hw
      _ = Matrix.trace ((P : Matrix (Fin D) (Fin D) ℂ) * X *
            ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              evalWord B w) := by rw [hΦP X]
      _ = Matrix.trace (X * (((P⁻¹ : GL (Fin D) ℂ) :
            Matrix (Fin D) (Fin D) ℂ) * evalWord B w *
              (P : Matrix (Fin D) (Fin D) ℂ))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
            Matrix.mul_assoc, Matrix.mul_assoc]
  calc evalWord B w
      = ((P * P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * evalWord B w *
          ((P * P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
        rw [mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    _ = (P : Matrix (Fin D) (Fin D) ℂ) *
          (((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * evalWord B w *
            (P : Matrix (Fin D) (Fin D) ℂ)) *
          ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
        rw [Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by rw [← hAw]

end MPSTensor
