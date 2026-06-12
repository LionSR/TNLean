import TNLean.PEPS.CycleMPSChainArc

/-!
# Bond-operator extraction from overlapping windows, site-dependent form

This file proves the matrix-tensor form of Lemma 5 of arXiv:1804.04964
(lines 2045--2255 of `Papers/1804.04964/paper_normal.tex`) for
site-dependent tensors, the setting in which the source states it: a closed
chain carries one tensor per site (`A_1, …, A_5` on five sites in the
source's display, with `L = 2`), every window of `L` consecutive sites is
injective, and a deformation of the closed-chain state is realized by
operators on each of the `L + 1` overlapping length-`L` windows around a
bond.  Then the deformation is a single virtual operation `X` on the bond:

* the deformed window left of the bond factors as the window product times
  `X` on the right, and the deformed window right of the bond as `X` times
  the window product
  (`MPSChainTensor.overlapWindow_exists_bondOperator`), and
* `X` is unique (`MPSChainTensor.eq_of_span_mul_left` applied to either
  spanning window).

The proof follows the source.  Comparing the windows at positions `j` and
`j + 1` through the rest of the chain — an arc of `n - L - 1 ≥ L` sites,
injective by the arc-spanning lemma — strips the state equality to a
letter-level relation (the source's `eq:normal_act_123` and
`eq:normal_act_234`, lines 2140--2167).  Chaining the `L` relations along
the `2L` sites flanking the bond turns the leftmost window into the
rightmost one (the source's plugging of `A_4` and `A_1`, lines 2168--2210),
and the two ends are compared as in `eq:inj_O->X_argument` (line 377): a
combination of window products representing the identity extracts the bond
operator from either side, and the two extractions agree
(`MPSChainTensor.exists_bondOperator_of_intertwine_span`).

The previously landed `TNLean/PEPS/CycleMPSOverlapWindow.lean` proves the
same statement for one site-independent tensor; it now delegates to this
file through the constant chain.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one bond
dimension `D`.  Documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Lemma 5 of Section `normal_alt`, lines 2045--2255 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix
open scoped Fin.NatCast

namespace MPSChainTensor

variable {d D n : ℕ}

/-! ### Extracting the bond operator from the two ends -/

/-- **Bond-operator extraction from an intertwining pair, spanning-family
form** (arXiv:1804.04964, Lemma 5, the comparison of the two ends, lines
2211--2255 of `Papers/1804.04964/paper_normal.tex`, after the model of
`eq:inj_O->X_argument`, line 377).

If `F a ⬝ W₂ b = W₁ a ⬝ G b` for two spanning families `W₁`, `W₂` of the
matrix algebra — on the chain, the products of the windows on the two sides
of the bond — then a single matrix `X` factors both deforming families:
`F` is the first family times `X` on the right, `G` is `X` times the second
family.  `X` is the combination of the `G`-family by coefficients
representing the identity over `W₂`, and the two factorizations agree
because the mirrored combination of the `F`-family collapses onto the same
matrix. -/
theorem exists_bondOperator_of_intertwine_span {ι κ : Type*}
    [Finite ι] [Finite κ]
    {W₁ : ι → Matrix (Fin D) (Fin D) ℂ} {W₂ : κ → Matrix (Fin D) (Fin D) ℂ}
    (hW₁ : Submodule.span ℂ (Set.range W₁) = ⊤)
    (hW₂ : Submodule.span ℂ (Set.range W₂) = ⊤)
    (F : ι → Matrix (Fin D) (Fin D) ℂ) (G : κ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ a b, F a * W₂ b = W₁ a * G b) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      (∀ a, F a = W₁ a * X) ∧ (∀ b, G b = X * W₂ b) := by
  cases nonempty_fintype κ
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range W₂) := hW₂ ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
  set X₀ : Matrix (Fin D) (Fin D) ℂ := ∑ b, α b • G b with hX₀
  have hF : ∀ a, F a = W₁ a * X₀ := by
    intro a
    calc F a = F a * (1 : Matrix (Fin D) (Fin D) ℂ) := (Matrix.mul_one _).symm
      _ = F a * ∑ b, α b • W₂ b := by rw [hα]
      _ = ∑ b, α b • (F a * W₂ b) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => mul_smul_comm _ _ _
      _ = ∑ b, α b • (W₁ a * G b) := Finset.sum_congr rfl fun b _ => by rw [h a b]
      _ = ∑ b, W₁ a * (α b • G b) := Finset.sum_congr rfl fun b _ =>
          (mul_smul_comm _ _ _).symm
      _ = W₁ a * X₀ := by rw [← Finset.mul_sum, hX₀]
  refine ⟨X₀, hF, fun b => ?_⟩
  -- The left factorization of `G`: compare against the right factorization
  -- through the intertwining relation and strip the spanning first family.
  apply eq_of_span_mul_left hW₁ (X := G b) (X' := X₀ * W₂ b)
  intro a
  calc W₁ a * G b = F a * W₂ b := (h a b).symm
    _ = (W₁ a * X₀) * W₂ b := by rw [hF a]
    _ = W₁ a * (X₀ * W₂ b) := Matrix.mul_assoc _ _ _

/-! ### Stripping the state equality to the letter level -/

/-- **Window comparison through the complementary arc** (arXiv:1804.04964,
Lemma 5, the inversions producing `eq:normal_act_123` and
`eq:normal_act_234`, lines 2140--2167 of
`Papers/1804.04964/paper_normal.tex`, site-dependent form).

If the states obtained by applying the deformed window tensors `C` at
position `j` and `C'` at position `j + 1` — windows starting at sites
`r + j` and `r + j + 1` of the closed chain — agree, then comparing through
the remaining `n - L - 1 ≥ L` sites, whose arc products span by the
arc-spanning lemma, strips the equality to the letter level: on every
window of `L + 1` sites, `C` contracted with the trailing letter at site
`r + j + L` equals the leading letter at site `r + j` contracted with
`C'`. -/
private theorem window_letter_step [NeZero n] {A : MPSChainTensor d D n}
    {L : ℕ} (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (hA : IsWindowInjective A L)
    {r j q : ℕ} (hq : j + (L + 1) + q = n)
    {C C' : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ}
    (hstate : ∀ (pre : Fin j → Fin d) (u : Fin (L + 1) → Fin d)
      (post : Fin q → Fin d),
      Matrix.trace (arcEval A r (List.ofFn pre) *
          (C (Fin.init u) * A ((r + j + L : ℕ) : Fin n) (u (Fin.last L))) *
          arcEval A (r + j + L + 1) (List.ofFn post)) =
        Matrix.trace (arcEval A r (List.ofFn pre) *
          (A ((r + j : ℕ) : Fin n) (u 0) * C' (Fin.tail u)) *
          arcEval A (r + j + L + 1) (List.ofFn post)))
    (u : Fin (L + 1) → Fin d) :
    C (Fin.init u) * A ((r + j + L : ℕ) : Fin n) (u (Fin.last L)) =
      A ((r + j : ℕ) : Fin n) (u 0) * C' (Fin.tail u) := by
  apply eq_of_trace_pairing_span (F := fun ρ : Fin (q + j) → Fin d =>
    arcEval A (r + j + L + 1) (List.ofFn ρ)) (hA.arc_span hL (by omega) _)
  intro ρ
  -- Split the complementary arc into the suffix and the prefix of the
  -- chain, both read from the bond outward.
  set post : Fin q → Fin d := fun i => ρ (Fin.castLE (by omega) i) with hpost
  set pre : Fin j → Fin d := fun i => ρ (Fin.natAdd q i) with hpre
  have hρ : List.ofFn post ++ List.ofFn pre = List.ofFn ρ :=
    (List.ofFn_add (f := ρ)).symm
  have key : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      Matrix.trace (arcEval A r (List.ofFn pre) * M *
          arcEval A (r + j + L + 1) (List.ofFn post)) =
        Matrix.trace (M * arcEval A (r + j + L + 1) (List.ofFn ρ)) := by
    intro M
    calc Matrix.trace (arcEval A r (List.ofFn pre) * M *
            arcEval A (r + j + L + 1) (List.ofFn post))
        = Matrix.trace (arcEval A (r + j + L + 1) (List.ofFn post) *
            (arcEval A r (List.ofFn pre) * M)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (M * (arcEval A (r + j + L + 1) (List.ofFn post) *
            arcEval A r (List.ofFn pre))) := by
          rw [← Matrix.mul_assoc]
          exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (M * arcEval A (r + j + L + 1) (List.ofFn ρ)) := by
          rw [← hρ, arcEval_append, List.length_ofFn,
            show r + j + L + 1 + q = r + n by omega, arcEval_add_n]
  rw [← key, ← key]
  exact hstate pre u post

/-! ### Chaining the windows across the bond -/

/-- The deformed window shifted `k` sites: the first `L - k` letters are
read from the tail of `a`, the remaining `k` letters from the head of
`b`. -/
private def shiftWindow {L : ℕ} (k : ℕ) (hk : k ≤ L) (a b : Fin L → Fin d) :
    Fin L → Fin d := fun i =>
  if h : i.val + k < L then a ⟨i.val + k, h⟩
  else b ⟨i.val + k - L, by have := i.isLt; omega⟩

private theorem shiftWindow_zero {L : ℕ} (hk : 0 ≤ L) (a b : Fin L → Fin d) :
    shiftWindow 0 hk a b = a := by
  funext i
  have hi := i.isLt
  simp only [shiftWindow]
  rw [dif_pos (show i.val + 0 < L by omega)]
  exact congrArg a (Fin.ext (show i.val + 0 = i.val by omega))

private theorem shiftWindow_self {L : ℕ} (hk : L ≤ L) (a b : Fin L → Fin d) :
    shiftWindow L hk a b = b := by
  funext i
  have hi := i.isLt
  simp only [shiftWindow]
  rw [dif_neg (show ¬ i.val + L < L by omega)]
  exact congrArg b (Fin.ext (show i.val + L - L = i.val by omega))

private theorem shiftWindow_apply_zero {L' k : ℕ} (hk : k ≤ L')
    (hk' : k ≤ L' + 1) (a b : Fin (L' + 1) → Fin d) :
    shiftWindow k hk' a b 0 = a ⟨k, by omega⟩ := by
  have h0 : (0 : Fin (L' + 1)).val = 0 := rfl
  simp only [shiftWindow]
  rw [dif_pos (show (0 : Fin (L' + 1)).val + k < L' + 1 by omega)]
  exact congrArg a (Fin.ext (show (0 : Fin (L' + 1)).val + k = k by omega))

/-- Shifting the deformed window by one site: popping the leading letter and
appending the next letter of `b`. -/
private theorem tail_snoc_shiftWindow {L' k : ℕ} (hk : k ≤ L')
    (hk' : k ≤ L' + 1) (hk1 : k + 1 ≤ L' + 1) (a b : Fin (L' + 1) → Fin d) :
    Fin.tail (α := fun _ => Fin d)
        (Fin.snoc (α := fun _ => Fin d) (shiftWindow k hk' a b)
          (b ⟨k, by omega⟩)) =
      shiftWindow (k + 1) hk1 a b := by
  funext i
  induction i using Fin.lastCases with
  | last =>
      change Fin.snoc (α := fun _ => Fin d) (shiftWindow k hk' a b)
          (b ⟨k, by omega⟩) (Fin.last L').succ =
        shiftWindow (k + 1) hk1 a b (Fin.last L')
      rw [Fin.succ_last, Fin.snoc_last]
      have hlast : (Fin.last L').val = L' := rfl
      simp only [shiftWindow]
      rw [dif_neg (show ¬ (Fin.last L').val + (k + 1) < L' + 1 by omega)]
      exact congrArg b
        (Fin.ext (show k = (Fin.last L').val + (k + 1) - (L' + 1) by omega))
  | cast i =>
      change Fin.snoc (α := fun _ => Fin d) (shiftWindow k hk' a b)
          (b ⟨k, by omega⟩) i.castSucc.succ =
        shiftWindow (k + 1) hk1 a b i.castSucc
      rw [Fin.succ_castSucc, Fin.snoc_castSucc]
      have hsucc : (i.succ : Fin (L' + 1)).val = i.val + 1 := Fin.val_succ i
      have hcast : (i.castSucc : Fin (L' + 1)).val = i.val := Fin.val_castSucc i
      have hi := i.isLt
      simp only [shiftWindow]
      by_cases h2 : i.val + 1 + k < L' + 1
      · rw [dif_pos (show (i.succ : Fin (L' + 1)).val + k < L' + 1 by omega),
          dif_pos (show (i.castSucc : Fin (L' + 1)).val + (k + 1) < L' + 1 by
            omega)]
        exact congrArg a (Fin.ext
          (show (i.succ : Fin (L' + 1)).val + k =
            (i.castSucc : Fin (L' + 1)).val + (k + 1) by omega))
      · rw [dif_neg (show ¬ (i.succ : Fin (L' + 1)).val + k < L' + 1 by omega),
          dif_neg (show ¬ (i.castSucc : Fin (L' + 1)).val + (k + 1) < L' + 1 by
            omega)]
        exact congrArg b (Fin.ext
          (show (i.succ : Fin (L' + 1)).val + k - (L' + 1) =
            (i.castSucc : Fin (L' + 1)).val + (k + 1) - (L' + 1) by omega))

/-- **Chaining the overlapping windows across the bond** (arXiv:1804.04964,
Lemma 5, the step plugging `A_4` and `A_1` into `eq:normal_act_123` and
`eq:normal_act_234`, lines 2168--2210 of
`Papers/1804.04964/paper_normal.tex`, site-dependent form).

Iterating the letter-level relation `L` times along the `2L` sites flanking
the bond moves the deformed window from the left of the bond to the right:
the leftmost deformed window contracted with the right block equals the
left block contracted with the rightmost deformed window. -/
private theorem chain_windows [NeZero n] {A : MPSChainTensor d D n} {L : ℕ}
    (hL : 0 < L) (r : ℕ)
    (C : ℕ → (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hstep : ∀ k, k < L → ∀ u : Fin (L + 1) → Fin d,
      C k (Fin.init u) * A ((r + k + L : ℕ) : Fin n) (u (Fin.last L)) =
        A ((r + k : ℕ) : Fin n) (u 0) * C (k + 1) (Fin.tail u))
    (a b : Fin L → Fin d) :
    C 0 a * arcEval A (r + L) (List.ofFn b) =
      arcEval A r (List.ofFn a) * C L b := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have S : ∀ k, ∀ hk : k ≤ L' + 1,
      C 0 a * arcEval A (r + (L' + 1))
          (List.ofFn fun i : Fin k => b (Fin.castLE hk i)) =
        arcEval A r (List.ofFn fun i : Fin k => a (Fin.castLE hk i)) *
          C k (shiftWindow k hk a b) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp only [List.ofFn_zero, arcEval_nil, Matrix.mul_one, Matrix.one_mul]
        rw [shiftWindow_zero hk a b]
    | succ k IH =>
        intro hk1
        have hk : k ≤ L' := by omega
        set u : Fin (L' + 1 + 1) → Fin d :=
          Fin.snoc (α := fun _ => Fin d) (shiftWindow k (by omega) a b)
            (b ⟨k, by omega⟩) with hu
        have hinit : Fin.init u = shiftWindow k (by omega) a b :=
          Fin.init_snoc _ _
        have hlast : u (Fin.last (L' + 1)) = b ⟨k, by omega⟩ := Fin.snoc_last _ _
        have hzero : u 0 = a ⟨k, by omega⟩ := by
          rw [hu, show (0 : Fin (L' + 1 + 1)) = Fin.castSucc 0 from
            Fin.castSucc_zero.symm, Fin.snoc_castSucc]
          exact shiftWindow_apply_zero hk (by omega) a b
        have htail : Fin.tail u = shiftWindow (k + 1) hk1 a b :=
          tail_snoc_shiftWindow hk (by omega) hk1 a b
        calc C 0 a * arcEval A (r + (L' + 1))
              (List.ofFn fun i : Fin (k + 1) => b (Fin.castLE hk1 i))
            = C 0 a * (arcEval A (r + (L' + 1))
                (List.ofFn fun i : Fin k => b (Fin.castLE (by omega) i)) *
                A ((r + (L' + 1) + k : ℕ) : Fin n) (b ⟨k, by omega⟩)) := by
              rw [arcEval_take_succ A (r + (L' + 1)) hk1 b]
          _ = (C 0 a * arcEval A (r + (L' + 1))
                (List.ofFn fun i : Fin k => b (Fin.castLE (by omega) i))) *
                A ((r + (L' + 1) + k : ℕ) : Fin n) (b ⟨k, by omega⟩) := by
              rw [Matrix.mul_assoc]
          _ = (arcEval A r (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                C k (shiftWindow k (by omega) a b)) *
                A ((r + (L' + 1) + k : ℕ) : Fin n) (b ⟨k, by omega⟩) := by
              rw [IH (by omega)]
          _ = arcEval A r (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                (C k (Fin.init u) *
                  A ((r + k + (L' + 1) : ℕ) : Fin n) (u (Fin.last (L' + 1)))) := by
              rw [hinit, hlast, Matrix.mul_assoc,
                show r + (L' + 1) + k = r + k + (L' + 1) by omega]
          _ = arcEval A r (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                (A ((r + k : ℕ) : Fin n) (u 0) * C (k + 1) (Fin.tail u)) := by
              rw [hstep k (by omega) u]
          _ = (arcEval A r (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                A ((r + k : ℕ) : Fin n) (a ⟨k, by omega⟩)) *
                C (k + 1) (shiftWindow (k + 1) hk1 a b) := by
              rw [hzero, htail, Matrix.mul_assoc]
          _ = arcEval A r (List.ofFn fun i : Fin (k + 1) => a (Fin.castLE hk1 i)) *
                C (k + 1) (shiftWindow (k + 1) hk1 a b) := by
              rw [arcEval_take_succ A r hk1 a]
  have hfull := S (L' + 1) le_rfl
  have hcast : ∀ f : Fin (L' + 1) → Fin d,
      (fun i : Fin (L' + 1) => f (Fin.castLE le_rfl i)) = f := by
    intro f
    funext i
    exact congrArg f (Fin.ext rfl)
  rw [hcast a, hcast b, shiftWindow_self le_rfl a b] at hfull
  exact hfull

/-! ### The site-dependent bond-operator extraction theorem -/

/-- **Lemma 5 of arXiv:1804.04964 for site-dependent matrix tensors**
(lines 2045--2255 of `Papers/1804.04964/paper_normal.tex`).

Let the closed chain on `n ≥ 2L + 1` sites carry one tensor per site, every
window of `L > 0` consecutive sites injective, and let `C 0, …, C L` be
deformed window tensors around the bond `(r + L - 1, r + L)`: `C j`
replaces the blocked tensor of the `L`-site window starting at site
`r + j`.  In the source's five-site display (`L = 2`, bond `(2, 3)`), `C j`
is the physical operator `O_{j+1}` contracted with the blocked window it
acts on.  If the deformed states agree for consecutive window positions —
the hypothesis quantifies the closed-chain coefficient over a common
refinement: a prefix of `j` sites starting at site `r`, the `L + 1` sites
covered by the two windows, and the remaining sites — then the deformation
is a virtual operation on the bond: a single matrix `X` with `C 0` the
window products starting at site `r` times `X` on the right, and `C L`
equal to `X` times the window products starting at site `r + L`.

`X` is unique by `MPSChainTensor.eq_of_span_mul_left` applied to the
spanning window starting at `r`; the algebra-homomorphism clause of the
source lemma (its final sentence, the maps `O_1 ↦ X` and `O_3^T ↦ X`) is
established with the site-dependent insertion correspondence in
`TNLean/PEPS/CycleMPSChainOverlapInsertion.lean`.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one
bond dimension `D`.  Documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem overlapWindow_exists_bondOperator [NeZero n] {A : MPSChainTensor d D n}
    {L : ℕ} (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (hA : IsWindowInjective A L)
    (r : ℕ) (C : ℕ → (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hstate : ∀ j, j < L → ∀ {q : ℕ}, j + (L + 1) + q = n →
      ∀ (pre : Fin j → Fin d) (u : Fin (L + 1) → Fin d) (post : Fin q → Fin d),
      Matrix.trace (arcEval A r (List.ofFn pre) *
          (C j (Fin.init u) * A ((r + j + L : ℕ) : Fin n) (u (Fin.last L))) *
          arcEval A (r + j + L + 1) (List.ofFn post)) =
        Matrix.trace (arcEval A r (List.ofFn pre) *
          (A ((r + j : ℕ) : Fin n) (u 0) * C (j + 1) (Fin.tail u)) *
          arcEval A (r + j + L + 1) (List.ofFn post))) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      (∀ a, C 0 a = arcEval A r (List.ofFn a) * X) ∧
        (∀ b, C L b = X * arcEval A (r + L) (List.ofFn b)) := by
  have hstep : ∀ k, k < L → ∀ u : Fin (L + 1) → Fin d,
      C k (Fin.init u) * A ((r + k + L : ℕ) : Fin n) (u (Fin.last L)) =
        A ((r + k : ℕ) : Fin n) (u 0) * C (k + 1) (Fin.tail u) := by
    intro k hk u
    exact window_letter_step hL hn hA (r := r) (j := k)
      (q := n - (k + (L + 1))) (by omega)
      (fun pre u' post => hstate k hk (by omega) pre u' post) u
  exact exists_bondOperator_of_intertwine_span (hA r) (hA (r + L)) (C 0) (C L)
    (chain_windows hL r C hstep)

end MPSChainTensor
