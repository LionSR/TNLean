import TNLean.PEPS.CycleMPSChainOverlapWindow
import TNLean.PEPS.CycleMPSWordTransport
import TNLean.Algebra.SkolemNoether

/-!
# The site-dependent insertion correspondence of the overlapping-window route

This file applies the site-dependent bond-operator extraction of
`TNLean/PEPS/CycleMPSChainOverlapWindow.lean` — Lemma 5 of arXiv:1804.04964
(lines 2045--2255 of `Papers/1804.04964/paper_normal.tex`) — to two
window-injective site-dependent chains `A`, `B` generating the same
closed-chain state on `n ≥ 2L + 1` sites, and delivers

* the insertion correspondence at each bond as an algebra homomorphism
  (`MPSChainTensor.exists_insertionHom`): a linear map `Φ` of the matrix
  algebra, unital and multiplicative — the source's clause that the maps
  `O_1 ↦ X` and `O_3^T ↦ X` "are uniquely defined and are
  algebra-homomorphisms" (line 2253) — pairing every insertion `X` on the
  `A`-chain with `Φ X` on the `B`-chain against all closed-chain words;
* its uniqueness (`MPSChainTensor.insertionHom_unique`); and
* the conjugation between the two chains at length `n`
  (`MPSChainTensor.exists_conjugation_of_sameState`): at every bond an
  invertible matrix `Z` with `B`-arc products of full length conjugate to
  the `A`-arc products, the site-dependent analogue of
  `MPSTensor.exists_conjugation_of_mpv_eq`.

The route mirrors the site-independent file
`TNLean/PEPS/CycleMPSOverlapInsertion.lean`, with one transport per window
start: a virtual insertion `X` on a bond of the `A`-chain is realized on
each of the `L + 1` overlapping windows around the bond
(`eq:normal_resonate`, lines 1961--2043), each deformed window is
transported to the `B`-chain by the arc transport at its own starting site
(`MPSChainTensor.exists_arcTransport`), the same-state hypothesis makes the
transported deformations generate one common state, and Lemma 5 for the
`B`-chain extracts the bond operator `Φ X`.  Uniqueness of the bond
operator makes `Φ` linear, unital and multiplicative; Skolem--Noether makes
it inner, and pairing insertions against all closed-chain words turns the
conjugation of insertions into the conjugation of arc products.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one
bond dimension `D`.  Documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section `normal_alt`, lines 1915--2295 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix
open scoped Fin.NatCast

namespace MPSChainTensor

variable {d D n : ℕ}

/-! ### The arc transport between same-state chains -/

/-- Concatenating a tuple word with a list splits the arc product at the
declared intermediate site. -/
private theorem arcEval_ofFn_mul [NeZero n] (A : MPSChainTensor d D n)
    {k : ℕ} (s : ℕ) (τ : Fin k → Fin d) (w : List (Fin d)) :
    arcEval A s (List.ofFn τ) * arcEval A (s + k) w =
      arcEval A s (List.ofFn τ ++ w) := by
  rw [arcEval_append, List.length_ofFn]

/-- **Arc transport between same-state chains** (the site-dependent form of
the operator-transport mechanism of arXiv:1804.04964, Lemma 5, lines
2045--2255 of `Papers/1804.04964/paper_normal.tex`).

If the chains `A` and `B` generate the same closed-chain state, and the
`A`-arc products of length `k` starting at site `s` and of the
complementary length `n - k` starting at site `s + k` both span the matrix
algebra, then a linear map `Λ` of the matrix algebra carries every
length-`k` arc product of `A` at site `s` to the corresponding arc product
of `B`.  The pairing against the complementary arc products is injective by
spanning and trace nondegeneracy, and the rotated same-state reading
matches the `A`- and `B`-pairings on the spanning arc family. -/
theorem exists_arcTransport [NeZero n] {A B : MPSChainTensor d D n}
    {s k q : ℕ} (hkq : k + q = n)
    (hAk : Submodule.span ℂ (Set.range fun τ : Fin k → Fin d =>
      arcEval A s (List.ofFn τ)) = ⊤)
    (hAq : Submodule.span ℂ (Set.range fun ρ : Fin q → Fin d =>
      arcEval A (s + k) (List.ofFn ρ)) = ⊤)
    (hAB : SameState A B) :
    ∃ Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      ∀ τ : Fin k → Fin d,
        Λ (arcEval A s (List.ofFn τ)) = arcEval B s (List.ofFn τ) := by
  classical
  set ΨA : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ((Fin q → Fin d) → ℂ) :=
    LinearMap.pi fun ρ => (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulRight ℂ (arcEval A (s + k) (List.ofFn ρ))) with hΨA
  set ΨB : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ((Fin q → Fin d) → ℂ) :=
    LinearMap.pi fun ρ => (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulRight ℂ (arcEval B (s + k) (List.ofFn ρ))) with hΨB
  have hΨA_apply : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Fin q → Fin d),
      ΨA M ρ = Matrix.trace (M * arcEval A (s + k) (List.ofFn ρ)) :=
    fun M ρ => rfl
  have hΨB_apply : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Fin q → Fin d),
      ΨB M ρ = Matrix.trace (M * arcEval B (s + k) (List.ofFn ρ)) :=
    fun M ρ => rfl
  refine MPSTensor.exists_linearMap_apply_eq _ _ ΨA ΨB hAk ?_ ?_
  · -- Injectivity of the `A`-pairing: spanning at the complementary length
    -- plus trace nondegeneracy.
    rw [LinearMap.ker_eq_bot']
    intro M hM
    refine eq_of_trace_pairing_span (F := fun ρ : Fin q → Fin d =>
      arcEval A (s + k) (List.ofFn ρ)) hAq (N := 0) fun ρ => ?_
    rw [Matrix.zero_mul, Matrix.trace_zero, ← hΨA_apply]
    exact congrArg (· ρ) hM
  · -- The two pairings match on the spanning arc family: both compute the
    -- closed-chain coefficient of the concatenated word, equal at length
    -- `n` by the rotated same-state reading.
    intro τ
    funext ρ
    rw [hΨA_apply, hΨB_apply, arcEval_ofFn_mul, arcEval_ofFn_mul]
    exact hAB.trace_arcEval_eq s (by simp [hkq])

/-! ### The transported deformation generates the inserted state -/

/-- **The transport intertwines the closed-chain pairings**
(arXiv:1804.04964, the mechanism of Lemma 5, lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`, site-dependent form): expanding any
matrix `M` over the window products of `A` at the window start `s` and
re-reading the expansion in the `B`-chain leaves every closed-chain
coefficient of total length `n` unchanged. -/
private theorem trace_transport_sandwich [NeZero n] {A B : MPSChainTensor d D n}
    {L : ℕ} (hA : IsWindowInjective A L) (hAB : SameState A B) {s : ℕ}
    {Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hΛ : ∀ τ : Fin L → Fin d,
      Λ (arcEval A s (List.ofFn τ)) = arcEval B s (List.ofFn τ))
    (M : Matrix (Fin D) (Fin D) ℂ) {s₀ : ℕ} (pre post : List (Fin d))
    (hs : s₀ + pre.length = s) (hlen : pre.length + L + post.length = n) :
    Matrix.trace (arcEval B s₀ pre * Λ M * arcEval B (s + L) post) =
      Matrix.trace (arcEval A s₀ pre * M * arcEval A (s + L) post) := by
  classical
  have hM : M ∈ Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
      arcEval A s (List.ofFn τ)) := (hA s) ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp hM
  have hΛM : Λ M = ∑ τ : Fin L → Fin d, c τ • arcEval B s (List.ofFn τ) := by
    rw [← hc, map_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [map_smul, hΛ τ]
  have decomp : ∀ (T : MPSChainTensor d D n) (N : Matrix (Fin D) (Fin D) ℂ),
      N = (∑ τ : Fin L → Fin d, c τ • arcEval T s (List.ofFn τ)) →
      Matrix.trace (arcEval T s₀ pre * N * arcEval T (s + L) post) =
        ∑ τ : Fin L → Fin d,
          c τ * Matrix.trace (arcEval T s₀ (pre ++ (List.ofFn τ ++ post))) := by
    intro T N hN
    rw [hN, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
    congr 1
    rw [arcEval_append, arcEval_append, List.length_ofFn, hs, Matrix.mul_assoc]
  rw [decomp B (Λ M) hΛM, decomp A M hc.symm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  exact (hAB.trace_arcEval_eq s₀ (by simp; omega)).symm

/-! ### Arcs with one insertion -/

/-- The arc product with a matrix inserted after the first `p` letters: the
site-dependent form of the deformed window tensors of arXiv:1804.04964,
`eq:X->O` (line 333) and the windows of `eq:normal_resonate` (lines
1961--2043 of `Papers/1804.04964/paper_normal.tex`). -/
private noncomputable def insertedArc [NeZero n] (A : MPSChainTensor d D n)
    (X : Matrix (Fin D) (Fin D) ℂ) (s p : ℕ) (w : List (Fin d)) :
    Matrix (Fin D) (Fin D) ℂ :=
  arcEval A s (w.take p) * X * arcEval A (s + p) (w.drop p)

private theorem insertedArc_length [NeZero n] (A : MPSChainTensor d D n)
    (X : Matrix (Fin D) (Fin D) ℂ) {s p : ℕ} {w : List (Fin d)}
    (hp : w.length ≤ p) : insertedArc A X s p w = arcEval A s w * X := by
  rw [insertedArc, List.take_of_length_le hp, List.drop_of_length_le hp,
    arcEval_nil, Matrix.mul_one]

private theorem insertedArc_zero [NeZero n] (A : MPSChainTensor d D n)
    (X : Matrix (Fin D) (Fin D) ℂ) (s : ℕ) (w : List (Fin d)) :
    insertedArc A X s 0 w = X * arcEval A s w := by
  rw [insertedArc, List.take_zero, List.drop_zero, arcEval_nil,
    Matrix.one_mul, Nat.add_zero]

/-- Appending a letter beyond the insertion point, at the site following the
arc. -/
private theorem insertedArc_append_letter [NeZero n] (A : MPSChainTensor d D n)
    (X : Matrix (Fin D) (Fin D) ℂ) {s p t : ℕ} {w : List (Fin d)}
    (hp : p ≤ w.length) (ht : t = s + w.length) (i : Fin d) :
    insertedArc A X s p w * A ((t : ℕ) : Fin n) i =
      insertedArc A X s p (w ++ [i]) := by
  subst ht
  rw [insertedArc, insertedArc, List.take_append_of_le_length hp,
    List.drop_append_of_le_length hp, arcEval_append, List.length_drop,
    show s + p + (w.length - p) = s + w.length by omega, arcEval_cons,
    arcEval_nil, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- Prepending a letter before the insertion point, at the site preceding
the arc. -/
private theorem insertedArc_cons_letter [NeZero n] (A : MPSChainTensor d D n)
    (X : Matrix (Fin D) (Fin D) ℂ) (s p : ℕ) (w : List (Fin d)) (i : Fin d) :
    A ((s : ℕ) : Fin n) i * insertedArc A X (s + 1) p w =
      insertedArc A X s (p + 1) (i :: w) := by
  rw [insertedArc, insertedArc, List.take_succ_cons, List.drop_succ_cons,
    arcEval_cons, show s + (p + 1) = s + 1 + p by omega]
  simp only [Matrix.mul_assoc]

/-! ### The insertion correspondence at one bond -/

/-- **The insertion correspondence at one bond** (arXiv:1804.04964, Lemma 5
applied to the deformations realizing a virtual insertion, lines 1961--2255
of `Papers/1804.04964/paper_normal.tex`, site-dependent form): for every
insertion `X` on the bond `(r + L - 1, r + L)` of the `A`-chain there is a
`Y` on the same bond of the `B`-chain with
`Λ 0 (A`-window`⬝ X) = B`-window`⬝ Y` on the window ending at the bond and
`Λ L (X ⬝ A`-window`) = Y ⬝ B`-window on the window starting at the bond,
where `Λ j` is the arc transport at the window start `r + j`. -/
private theorem exists_insertion_image [NeZero n] {A B : MPSChainTensor d D n}
    {L : ℕ} (hL : 0 < L) (hn : 2 * L + 1 ≤ n)
    (hA : IsWindowInjective A L) (hB : IsWindowInjective B L)
    (hAB : SameState A B) (r : ℕ)
    {Λ : ℕ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hΛ : ∀ (j : ℕ) (τ : Fin L → Fin d),
      Λ j (arcEval A (r + j) (List.ofFn τ)) = arcEval B (r + j) (List.ofFn τ))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      (∀ a : Fin L → Fin d,
        Λ 0 (arcEval A r (List.ofFn a) * X) = arcEval B r (List.ofFn a) * Y) ∧
        (∀ b : Fin L → Fin d,
          Λ L (X * arcEval A (r + L) (List.ofFn b)) =
            Y * arcEval B (r + L) (List.ofFn b)) := by
  classical
  -- The deformed window tensors transported to the `B`-chain, one transport
  -- per window start.
  set C : ℕ → (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun j s' => Λ j (insertedArc A X (r + j) (L - j) (List.ofFn s')) with hC
  -- All transported deformations generate the same state: each one matches
  -- the `A`-state with `X` inserted on the bond.
  have hstate : ∀ j, j < L → ∀ {q : ℕ}, j + (L + 1) + q = n →
      ∀ (pre : Fin j → Fin d) (u : Fin (L + 1) → Fin d) (post : Fin q → Fin d),
      Matrix.trace (arcEval B r (List.ofFn pre) *
          (C j (Fin.init u) * B ((r + j + L : ℕ) : Fin n) (u (Fin.last L))) *
          arcEval B (r + j + L + 1) (List.ofFn post)) =
        Matrix.trace (arcEval B r (List.ofFn pre) *
          (B ((r + j : ℕ) : Fin n) (u 0) * C (j + 1) (Fin.tail u)) *
          arcEval B (r + j + L + 1) (List.ofFn post)) := by
    intro j hj q hq pre u post
    -- The left side: absorb the trailing letter into the suffix, transport,
    -- and push the letter back into the deformed arc.
    have hleft : Matrix.trace (arcEval B r (List.ofFn pre) *
        (C j (Fin.init u) * B ((r + j + L : ℕ) : Fin n) (u (Fin.last L))) *
        arcEval B (r + j + L + 1) (List.ofFn post)) =
        Matrix.trace (arcEval A r (List.ofFn pre) *
          insertedArc A X (r + j) (L - j) (List.ofFn u) *
          arcEval A (r + j + L + 1) (List.ofFn post)) := by
      have e1 : arcEval B r (List.ofFn pre) *
          (C j (Fin.init u) * B ((r + j + L : ℕ) : Fin n) (u (Fin.last L))) *
          arcEval B (r + j + L + 1) (List.ofFn post) =
          arcEval B r (List.ofFn pre) * C j (Fin.init u) *
            arcEval B (r + j + L) (u (Fin.last L) :: List.ofFn post) := by
        rw [arcEval_cons]
        simp only [Matrix.mul_assoc]
      rw [e1]
      simp only [hC]
      rw [trace_transport_sandwich hA hAB (hΛ j) _ (List.ofFn pre)
        (u (Fin.last L) :: List.ofFn post) (by simp)
        (by simp; omega)]
      have e2 : arcEval A r (List.ofFn pre) *
          insertedArc A X (r + j) (L - j) (List.ofFn (Fin.init u)) *
            arcEval A (r + j + L) (u (Fin.last L) :: List.ofFn post) =
          arcEval A r (List.ofFn pre) *
            (insertedArc A X (r + j) (L - j) (List.ofFn (Fin.init u)) *
              A ((r + j + L : ℕ) : Fin n) (u (Fin.last L))) *
              arcEval A (r + j + L + 1) (List.ofFn post) := by
        rw [arcEval_cons]
        simp only [Matrix.mul_assoc]
      rw [e2, insertedArc_append_letter A X
        (by simp : L - j ≤ (List.ofFn (Fin.init u)).length)
        (by simp : r + j + L = r + j + (List.ofFn (Fin.init u)).length)
        (u (Fin.last L))]
      have e3 : List.ofFn (Fin.init u) ++ [u (Fin.last L)] = List.ofFn u := by
        rw [List.ofFn_succ' u, List.concat_eq_append]
        rfl
      rw [e3]
    -- The right side: absorb the leading letter into the prefix, transport,
    -- and push the letter back into the deformed arc.
    have hright : Matrix.trace (arcEval B r (List.ofFn pre) *
        (B ((r + j : ℕ) : Fin n) (u 0) * C (j + 1) (Fin.tail u)) *
        arcEval B (r + j + L + 1) (List.ofFn post)) =
        Matrix.trace (arcEval A r (List.ofFn pre) *
          insertedArc A X (r + j) (L - j) (List.ofFn u) *
          arcEval A (r + j + L + 1) (List.ofFn post)) := by
      have e1 : arcEval B r (List.ofFn pre) *
          (B ((r + j : ℕ) : Fin n) (u 0) * C (j + 1) (Fin.tail u)) *
          arcEval B (r + j + L + 1) (List.ofFn post) =
          arcEval B r (List.ofFn pre ++ [u 0]) * C (j + 1) (Fin.tail u) *
            arcEval B (r + j + L + 1) (List.ofFn post) := by
        rw [arcEval_append, List.length_ofFn, arcEval_cons, arcEval_nil,
          Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      have hΛ1 : ∀ τ : Fin L → Fin d,
          Λ (j + 1) (arcEval A (r + j + 1) (List.ofFn τ)) =
            arcEval B (r + j + 1) (List.ofFn τ) := by
        intro τ
        have h := hΛ (j + 1) τ
        rwa [← Nat.add_assoc r j 1] at h
      rw [e1]
      simp only [hC]
      rw [← Nat.add_assoc r j 1, show r + j + L + 1 = r + j + 1 + L by omega]
      rw [trace_transport_sandwich hA hAB hΛ1 _
        (List.ofFn pre ++ [u 0]) (List.ofFn post)
        (by simp; omega) (by simp; omega)]
      have e2 : arcEval A r (List.ofFn pre ++ [u 0]) *
          insertedArc A X (r + j + 1) (L - (j + 1)) (List.ofFn (Fin.tail u)) *
            arcEval A (r + j + 1 + L) (List.ofFn post) =
          arcEval A r (List.ofFn pre) *
            (A ((r + j : ℕ) : Fin n) (u 0) *
              insertedArc A X (r + j + 1) (L - (j + 1)) (List.ofFn (Fin.tail u))) *
              arcEval A (r + j + 1 + L) (List.ofFn post) := by
        rw [arcEval_append, List.length_ofFn, arcEval_cons, arcEval_nil,
          Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [e2]
      have e4 : A ((r + j : ℕ) : Fin n) (u 0) *
          insertedArc A X (r + j + 1) (L - (j + 1)) (List.ofFn (Fin.tail u)) =
          insertedArc A X (r + j) (L - j) (List.ofFn u) := by
        rw [insertedArc_cons_letter A X (r + j) (L - (j + 1))
          (List.ofFn (Fin.tail u)) (u 0),
          show L - (j + 1) + 1 = L - j by omega]
        congr 1
        rw [List.ofFn_succ (f := u)]
        rfl
      rw [e4, show r + j + 1 + L = r + j + L + 1 by omega]
    rw [hleft, hright]
  -- Lemma 5 extracts the bond operator on the `B`-chain.
  obtain ⟨Y, hY1, hY2⟩ := overlapWindow_exists_bondOperator hL hn hB r C hstate
  refine ⟨Y, fun a => ?_, fun b => ?_⟩
  · have h0 := hY1 a
    simp only [hC, Nat.sub_zero] at h0
    rw [← insertedArc_length A X (s := r) (p := L)
      (by simp : (List.ofFn a).length ≤ L)]
    exact h0
  · have hL0 := hY2 b
    simp only [hC, Nat.sub_self, insertedArc_zero] at hL0
    exact hL0

/-! ### The insertion correspondence as an algebra homomorphism -/

/-- Any list of declared length is the word of a tuple. -/
private theorem exists_ofFn_of_length {l : List (Fin d)} {k : ℕ}
    (hl : l.length = k) : ∃ a : Fin k → Fin d, List.ofFn a = l := by
  subst hl
  exact ⟨l.get, List.ofFn_get l⟩

/-- A nonzero-size identity matrix is nonzero. -/
private theorem matrix_one_ne_zero (hD : 0 < D) :
    (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h ⟨0, hD⟩) ⟨0, hD⟩
  rw [Matrix.one_apply_eq] at hentry
  exact one_ne_zero hentry

/-- **The insertion correspondence is an algebra homomorphism**
(arXiv:1804.04964, Lemma 5, the closing clause at line 2253 of
`Papers/1804.04964/paper_normal.tex`: the maps `O_1 ↦ X` and `O_3^T ↦ X`
"are uniquely defined and are algebra-homomorphisms", site-dependent form).

For two window-injective site-dependent chains generating the same
closed-chain state on `n ≥ 2L + 1` sites, the correspondence sending an
insertion `X` on the bond `(r + L - 1, r + L)` of the `A`-chain to the bond
operator extracted by Lemma 5 on the `B`-chain is a linear, unital and
multiplicative map `Φ` of the matrix algebra; it pairs the two chains
against every closed-chain word read from the bond.  Uniqueness is
`MPSChainTensor.insertionHom_unique`.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one
bond dimension `D`.  Documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem exists_insertionHom [NeZero n] {L : ℕ} (hL : 0 < L)
    (hn : 2 * L + 1 ≤ n) (A B : MPSChainTensor d D n)
    (hA : IsWindowInjective A L) (hB : IsWindowInjective B L)
    (hAB : SameState A B) (r : ℕ) :
    ∃ Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      Φ 1 = 1 ∧ (∀ M N, Φ (M * N) = Φ M * Φ N) ∧
        ∀ (X : Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)), w.length = n →
          Matrix.trace (X * arcEval A (r + L) w) =
            Matrix.trace (Φ X * arcEval B (r + L) w) := by
  classical
  -- One arc transport per window start.
  have hch : ∀ j : ℕ, ∃ Λj : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ,
      ∀ τ : Fin L → Fin d,
        Λj (arcEval A (r + j) (List.ofFn τ)) = arcEval B (r + j) (List.ofFn τ) :=
    fun j => exists_arcTransport (k := L) (q := n - L) (by omega)
      (hA.arc_span hL le_rfl _) (hA.arc_span hL (by omega) _) hAB
  choose Λ hΛ using hch
  have hΛ0 : ∀ τ : Fin L → Fin d,
      Λ 0 (arcEval A r (List.ofFn τ)) = arcEval B r (List.ofFn τ) := by
    intro τ
    have h := hΛ 0 τ
    rwa [Nat.add_zero] at h
  have hins := exists_insertion_image hL hn hA hB hAB r hΛ
  -- The identity decomposition over the `B`-window products at the bond.
  have h1B : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
      (Set.range fun b : Fin L → Fin d => arcEval B (r + L) (List.ofFn b)) :=
    (hB (r + L)) ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1B
  -- The correspondence as a linear map.
  set Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    ∑ b : Fin L → Fin d, α b •
      (Λ L ∘ₗ LinearMap.mulRight ℂ (arcEval A (r + L) (List.ofFn b))) with hΦdef
  have hΦ_apply : ∀ X, Φ X = ∑ b : Fin L → Fin d,
      α b • Λ L (X * arcEval A (r + L) (List.ofFn b)) := by
    intro X
    rw [hΦdef]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.mulRight_apply]
  -- `Φ X` is the bond operator of `X`.
  have hΦY : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      (∀ a : Fin L → Fin d,
        Λ 0 (arcEval A r (List.ofFn a) * X) = arcEval B r (List.ofFn a) * Φ X) ∧
        (∀ b : Fin L → Fin d,
          Λ L (X * arcEval A (r + L) (List.ofFn b)) =
            Φ X * arcEval B (r + L) (List.ofFn b)) := by
    intro X
    obtain ⟨Y, hY1, hY2⟩ := hins X
    have hYΦ : Φ X = Y := by
      rw [hΦ_apply]
      calc (∑ b : Fin L → Fin d, α b • Λ L (X * arcEval A (r + L) (List.ofFn b)))
          = ∑ b : Fin L → Fin d, α b • (Y * arcEval B (r + L) (List.ofFn b)) :=
            Finset.sum_congr rfl fun b _ => by rw [hY2 b]
        _ = ∑ b : Fin L → Fin d, Y * (α b • arcEval B (r + L) (List.ofFn b)) :=
            Finset.sum_congr rfl fun b _ => (mul_smul_comm _ _ _).symm
        _ = Y * ∑ b : Fin L → Fin d, α b • arcEval B (r + L) (List.ofFn b) := by
            rw [← Finset.mul_sum]
        _ = Y := by rw [hα, Matrix.mul_one]
    rw [hYΦ]
    exact ⟨hY1, hY2⟩
  have hΦ1 : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (a : Fin L → Fin d),
      Λ 0 (arcEval A r (List.ofFn a) * X) = arcEval B r (List.ofFn a) * Φ X :=
    fun X => (hΦY X).1
  -- The right-multiplication relation extends from window products to all
  -- matrices, making `Φ` multiplicative.
  have hΛr : ∀ (X M : Matrix (Fin D) (Fin D) ℂ),
      Λ 0 (M * X) = Λ 0 M * Φ X := by
    intro X
    have hext := LinearMap.ext_on_range
      (v := fun a : Fin L → Fin d => arcEval A r (List.ofFn a)) (hv := hA r)
      (f := Λ 0 ∘ₗ LinearMap.mulRight ℂ X)
      (g := (LinearMap.mulRight ℂ (Φ X)) ∘ₗ Λ 0)
      (fun a => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
        rw [hΦ1 X a, hΛ0 a])
    intro M
    have := congrArg (· M) hext
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply] using this
  have hΦmul : ∀ M N : Matrix (Fin D) (Fin D) ℂ, Φ (M * N) = Φ M * Φ N := by
    intro M N
    apply eq_of_span_mul_left (W := fun a : Fin L → Fin d =>
      arcEval B r (List.ofFn a)) (hB r)
    intro a
    calc arcEval B r (List.ofFn a) * Φ (M * N)
        = Λ 0 (arcEval A r (List.ofFn a) * (M * N)) := (hΦ1 (M * N) a).symm
      _ = Λ 0 ((arcEval A r (List.ofFn a) * M) * N) := by rw [Matrix.mul_assoc]
      _ = Λ 0 (arcEval A r (List.ofFn a) * M) * Φ N := hΛr N _
      _ = (arcEval B r (List.ofFn a) * Φ M) * Φ N := by rw [hΦ1 M a]
      _ = arcEval B r (List.ofFn a) * (Φ M * Φ N) := Matrix.mul_assoc _ _ _
  have hΦone : Φ 1 = 1 := by
    apply eq_of_span_mul_left (W := fun a : Fin L → Fin d =>
      arcEval B r (List.ofFn a)) (hB r)
    intro a
    calc arcEval B r (List.ofFn a) * Φ 1
        = Λ 0 (arcEval A r (List.ofFn a) * 1) := (hΦ1 1 a).symm
      _ = Λ 0 (arcEval A r (List.ofFn a)) := by rw [Matrix.mul_one]
      _ = arcEval B r (List.ofFn a) := hΛ0 a
      _ = arcEval B r (List.ofFn a) * 1 := (Matrix.mul_one _).symm
  refine ⟨Φ, hΦone, hΦmul, fun X w hw => ?_⟩
  -- The closed-chain pairing of insertions, read from the bond.
  have hdrop : (w.drop (n - L)).length = L := by
    rw [List.length_drop]
    omega
  obtain ⟨a, ha⟩ := exists_ofFn_of_length hdrop
  have htake : (w.take (n - L)).length = n - L := by
    rw [List.length_take]
    omega
  have hsplit : w = w.take (n - L) ++ List.ofFn a := by
    rw [ha, List.take_append_drop]
  -- The sandwich relation at the window, from the transport bridge.
  have hsand : Matrix.trace (Λ 0 (arcEval A r (List.ofFn a) * X) *
      arcEval B (r + L) (w.take (n - L))) =
      Matrix.trace (arcEval A r (List.ofFn a) * X *
        arcEval A (r + L) (w.take (n - L))) := by
    have hb := trace_transport_sandwich hA hAB hΛ0
      (arcEval A r (List.ofFn a) * X) (s₀ := r) [] (w.take (n - L))
      (by simp) (by simp [htake]; omega)
    simpa only [arcEval_nil, Matrix.one_mul] using hb
  -- Fold the rotated word on each chain.
  have hfold : ∀ T : MPSChainTensor d D n,
      arcEval T (r + L) (w.take (n - L)) * arcEval T r (List.ofFn a) =
        arcEval T (r + L) w := by
    intro T
    conv_rhs => rw [hsplit]
    rw [arcEval_append, htake, show r + L + (n - L) = r + n by omega,
      arcEval_add_n]
  calc Matrix.trace (X * arcEval A (r + L) w)
      = Matrix.trace (X * (arcEval A (r + L) (w.take (n - L)) *
          arcEval A r (List.ofFn a))) := by rw [hfold A]
    _ = Matrix.trace (arcEval A r (List.ofFn a) * X *
          arcEval A (r + L) (w.take (n - L))) := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = Matrix.trace (Λ 0 (arcEval A r (List.ofFn a) * X) *
          arcEval B (r + L) (w.take (n - L))) := hsand.symm
    _ = Matrix.trace (arcEval B r (List.ofFn a) * Φ X *
          arcEval B (r + L) (w.take (n - L))) := by rw [hΦ1 X a]
    _ = Matrix.trace (Φ X * (arcEval B (r + L) (w.take (n - L)) *
          arcEval B r (List.ofFn a))) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = Matrix.trace (Φ X * arcEval B (r + L) w) := by rw [hfold B]

/-- **Uniqueness of the insertion correspondence** (arXiv:1804.04964,
Lemma 5, line 2253 of `Papers/1804.04964/paper_normal.tex`: the maps
"are uniquely defined", site-dependent form).  Two linear maps pairing
identically against all closed-chain words of the window-injective `B`-chain
are equal. -/
theorem insertionHom_unique [NeZero n] {B : MPSChainTensor d D n} {L : ℕ}
    (hL : 0 < L) (hn : L ≤ n) (hB : IsWindowInjective B L) (p : ℕ)
    {Φ Φ' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)), w.length = n →
      Matrix.trace (Φ X * arcEval B p w) = Matrix.trace (Φ' X * arcEval B p w)) :
    Φ = Φ' := by
  refine LinearMap.ext fun X => ?_
  refine eq_of_trace_pairing_span (F := fun ρ : Fin n → Fin d =>
    arcEval B p (List.ofFn ρ)) (hB.arc_span hL hn p) fun ρ => ?_
  exact h X (List.ofFn ρ) (by simp)

/-! ### The conjugation between same-state chains -/

/-- **The conjugation between two same-state site-dependent chains at length
`n ≥ 2L + 1`** (arXiv:1804.04964, Lemma 5 and the closed-chain corollary of
Section `normal_alt`, lines 1961--2295 of
`Papers/1804.04964/paper_normal.tex`, site-dependent form; the
site-independent specialization is
`MPSTensor.exists_conjugation_of_mpv_eq`).

Two window-injective site-dependent chains generating the same closed-chain
state on `n ≥ 2L + 1` sites have conjugate arc products of full length at
every bond: for each site `p` there is an invertible `Z` with
`B`-arc `= Z ⬝ A`-arc `⬝ Z⁻¹` for every word of length `n` read from site
`p`.  The insertion correspondence at the bond is an algebra automorphism
of the full matrix algebra, by Skolem--Noether inner; pairing insertions
against all closed-chain words transfers the conjugation to the arc
products.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one
bond dimension `D`.  Documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem exists_conjugation_of_sameState [NeZero n] {L : ℕ} (hL : 0 < L)
    (hn : 2 * L + 1 ≤ n) (A B : MPSChainTensor d D n)
    (hA : IsWindowInjective A L) (hB : IsWindowInjective B L)
    (hAB : SameState A B) (p : ℕ) :
    ∃ Z : GL (Fin D) ℂ, ∀ w : List (Fin d), w.length = n →
      arcEval B p w = (Z : Matrix (Fin D) (Fin D) ℂ) * arcEval A p w *
        ((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · -- All `0 × 0` matrices are equal.
    subst hD0
    refine ⟨1, fun w hw => ?_⟩
    apply Matrix.ext
    intro a b
    exact a.elim0
  -- The insertion correspondence at the bond `(p - 1, p)`, reading the
  -- chain from the window start `p + (n - L)`.
  obtain ⟨Φ, hΦone, hΦmul, hpair⟩ :=
    exists_insertionHom hL hn A B hA hB hAB (p + (n - L))
  have hpair' : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)),
      w.length = n →
      Matrix.trace (X * arcEval A p w) = Matrix.trace (Φ X * arcEval B p w) := by
    intro X w hw
    have h := hpair X w hw
    rwa [show p + (n - L) + L = p + n by omega, arcEval_add_n,
      arcEval_add_n] at h
  -- `Φ` is unital, hence nonzero, hence an automorphism, hence inner.
  have hΦne : Φ ≠ 0 := by
    intro h0
    apply matrix_one_ne_zero hD
    rw [← hΦone, h0]
    rfl
  have hBij := MPSTensor.linear_mul_endomorphism_bijective Φ hΦmul hΦne
  let fHom := MPSTensor.linearMapToAlgHom Φ hΦmul hBij.surjective
  let f := AlgEquiv.ofBijective fHom hBij
  obtain ⟨P, hP⟩ := MPSTensor.skolemNoether_matrix f
  have hΦP : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Φ X = (P : Matrix (Fin D) (Fin D) ℂ) * X *
        ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro X
    have : f X = Φ X := rfl
    rw [← this]
    exact hP X
  -- Strip the insertions: the arc products are conjugate.
  refine ⟨P, fun w hw => ?_⟩
  have hAw : arcEval A p w =
      ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * arcEval B p w *
        (P : Matrix (Fin D) (Fin D) ℂ) := by
    apply (Matrix.ext_iff_trace_mul_left).2
    intro X
    calc Matrix.trace (X * arcEval A p w)
        = Matrix.trace (Φ X * arcEval B p w) := hpair' X w hw
      _ = Matrix.trace ((P : Matrix (Fin D) (Fin D) ℂ) * X *
            ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              arcEval B p w) := by rw [hΦP X]
      _ = Matrix.trace (X * (((P⁻¹ : GL (Fin D) ℂ) :
            Matrix (Fin D) (Fin D) ℂ) * arcEval B p w *
              (P : Matrix (Fin D) (Fin D) ℂ))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
            Matrix.mul_assoc, Matrix.mul_assoc]
  calc arcEval B p w
      = ((P * P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * arcEval B p w *
          ((P * P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
        rw [mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    _ = (P : Matrix (Fin D) (Fin D) ℂ) *
          (((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * arcEval B p w *
            (P : Matrix (Fin D) (Fin D) ℂ)) *
          ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
        rw [Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin D) (Fin D) ℂ) * arcEval A p w *
          ((P⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by rw [← hAw]

end MPSChainTensor
