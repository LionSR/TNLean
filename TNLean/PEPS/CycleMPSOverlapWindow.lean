import TNLean.PEPS.CycleMPSWordTransport

/-!
# Bond-operator extraction from overlapping windows on the closed chain

This file proves the matrix-tensor form of Lemma 5 of arXiv:1804.04964
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

The proof follows the source.  Comparing the windows at `j` and `j + 1`
through the rest of the chain — an arc of `n - L - 1 ≥ L` sites, injective by
the span-extension lemma — strips the state equality to a letter-level
relation `C j (w) ⬝ B = B ⬝ C (j+1) (w shifted)` (the source's
`eq:normal_act_123` and `eq:normal_act_234`, lines 2140--2210).  Chaining the
`L` relations along a window of `2L` sites turns the leftmost window into the
rightmost one (the source's plugging of `A_4` and `A_1`, lines 2168--2210),
and the two ends are compared as in `eq:inj_O->X_argument` (line 377): a
combination of window products representing the identity extracts the bond
operator from either side, and the two extractions agree.

The source states Lemma 5 for site-dependent tensors on five sites with
`L = 2`; this file proves the statement for one site-independent tensor,
arbitrary `L > 0`, and any chain length `n ≥ 2L + 1`, which is the form the
closed-chain corollaries of Section `normal_alt` consume.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Lemma 5 of Section `normal_alt`, lines 2045--2255 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Stripping the state equality to the letter level -/

/-- **Window comparison through the complementary arc** (arXiv:1804.04964,
Lemma 5, the inversions producing `eq:normal_act_123` and
`eq:normal_act_234`, lines 2140--2167 of
`Papers/1804.04964/paper_normal.tex`).

If the states obtained by applying the deformed window tensors `C` at
position `j` and `C'` at position `j + 1` agree, then comparing through the
remaining `n - L - 1 ≥ L` sites — whose word products span by the extension
lemma — strips the equality to the letter level: on every window of `L + 1`
sites, `C` contracted with a trailing letter equals a leading letter
contracted with `C'`. -/
private theorem window_letter_step {B : MPSTensor d D} {n L : ℕ}
    (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (hB : IsNBlkInjective B L)
    {j q : ℕ} (hq : j + (L + 1) + q = n)
    {C C' : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ}
    (hstate : ∀ (pre : Fin j → Fin d) (u : Fin (L + 1) → Fin d)
      (post : Fin q → Fin d),
      Matrix.trace (evalWord B (List.ofFn pre) *
          (C (Fin.init u) * B (u (Fin.last L))) * evalWord B (List.ofFn post)) =
        Matrix.trace (evalWord B (List.ofFn pre) *
          (B (u 0) * C' (Fin.tail u)) * evalWord B (List.ofFn post)))
    (u : Fin (L + 1) → Fin d) :
    C (Fin.init u) * B (u (Fin.last L)) = B (u 0) * C' (Fin.tail u) := by
  apply eq_of_trace_mul_evalWord_eq (m := q + j)
    (isNBlkInjective_of_le hL hB (by omega))
  intro ρ
  -- Split the complementary arc into the suffix and the prefix of the chain.
  set post : Fin q → Fin d := fun i => ρ (Fin.castLE (by omega) i) with hpost
  set pre : Fin j → Fin d := fun i => ρ (Fin.natAdd q i) with hpre
  have hρ : List.ofFn post ++ List.ofFn pre = List.ofFn ρ := (List.ofFn_add (f := ρ)).symm
  have key : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      Matrix.trace (evalWord B (List.ofFn pre) * M * evalWord B (List.ofFn post)) =
        Matrix.trace (M * evalWord B (List.ofFn ρ)) := by
    intro M
    calc Matrix.trace (evalWord B (List.ofFn pre) * M * evalWord B (List.ofFn post))
        = Matrix.trace (evalWord B (List.ofFn post) *
            (evalWord B (List.ofFn pre) * M)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (M * (evalWord B (List.ofFn post) *
            evalWord B (List.ofFn pre))) := by
          rw [← Matrix.mul_assoc]
          exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (M * evalWord B (List.ofFn ρ)) := by
          rw [← evalWord_append, hρ]
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

private theorem shiftWindow_apply_zero {L' k : ℕ} (hk : k ≤ L') (hk' : k ≤ L' + 1)
    (a b : Fin (L' + 1) → Fin d) :
    shiftWindow k hk' a b 0 = a ⟨k, by omega⟩ := by
  have h0 : (0 : Fin (L' + 1)).val = 0 := rfl
  simp only [shiftWindow]
  rw [dif_pos (show (0 : Fin (L' + 1)).val + k < L' + 1 by omega)]
  exact congrArg a (Fin.ext (show (0 : Fin (L' + 1)).val + k = k by omega))

/-- Shifting the deformed window by one site: popping the leading letter and
appending the next letter of `b`. -/
private theorem tail_snoc_shiftWindow {L' k : ℕ} (hk : k ≤ L') (hk' : k ≤ L' + 1)
    (hk1 : k + 1 ≤ L' + 1) (a b : Fin (L' + 1) → Fin d) :
    Fin.tail (α := fun _ => Fin d)
        (Fin.snoc (α := fun _ => Fin d) (shiftWindow k hk' a b) (b ⟨k, by omega⟩)) =
      shiftWindow (k + 1) hk1 a b := by
  funext i
  induction i using Fin.lastCases with
  | last =>
      show Fin.snoc (α := fun _ => Fin d) (shiftWindow k hk' a b)
          (b ⟨k, by omega⟩) (Fin.last L').succ = shiftWindow (k + 1) hk1 a b (Fin.last L')
      rw [Fin.succ_last, Fin.snoc_last]
      have hlast : (Fin.last L').val = L' := rfl
      simp only [shiftWindow]
      rw [dif_neg (show ¬ (Fin.last L').val + (k + 1) < L' + 1 by omega)]
      exact congrArg b
        (Fin.ext (show k = (Fin.last L').val + (k + 1) - (L' + 1) by omega))
  | cast i =>
      show Fin.snoc (α := fun _ => Fin d) (shiftWindow k hk' a b)
          (b ⟨k, by omega⟩) i.castSucc.succ = shiftWindow (k + 1) hk1 a b i.castSucc
      rw [Fin.succ_castSucc, Fin.snoc_castSucc]
      have hsucc : (i.succ : Fin (L' + 1)).val = i.val + 1 := Fin.val_succ i
      have hcast : (i.castSucc : Fin (L' + 1)).val = i.val := Fin.val_castSucc i
      have hi := i.isLt
      simp only [shiftWindow]
      by_cases h2 : i.val + 1 + k < L' + 1
      · rw [dif_pos (show (i.succ : Fin (L' + 1)).val + k < L' + 1 by omega),
          dif_pos (show (i.castSucc : Fin (L' + 1)).val + (k + 1) < L' + 1 by omega)]
        exact congrArg a (Fin.ext
          (show (i.succ : Fin (L' + 1)).val + k =
            (i.castSucc : Fin (L' + 1)).val + (k + 1) by omega))
      · rw [dif_neg (show ¬ (i.succ : Fin (L' + 1)).val + k < L' + 1 by omega),
          dif_neg (show ¬ (i.castSucc : Fin (L' + 1)).val + (k + 1) < L' + 1 by omega)]
        exact congrArg b (Fin.ext
          (show (i.succ : Fin (L' + 1)).val + k - (L' + 1) =
            (i.castSucc : Fin (L' + 1)).val + (k + 1) - (L' + 1) by omega))

/-- The word product of the first `k + 1` letters peels its last letter. -/
private theorem evalWord_take_succ {B : MPSTensor d D} {L k : ℕ}
    (hk : k + 1 ≤ L) (f : Fin L → Fin d) :
    evalWord B (List.ofFn fun i : Fin (k + 1) => f (Fin.castLE hk i)) =
      evalWord B (List.ofFn fun i : Fin k => f (Fin.castLE (by omega) i)) *
        B (f ⟨k, by omega⟩) := by
  have hsnoc : (fun i : Fin (k + 1) => f (Fin.castLE hk i)) =
      Fin.snoc (α := fun _ => Fin d)
        (fun i : Fin k => f (Fin.castLE (by omega) i)) (f ⟨k, by omega⟩) := by
    funext i
    induction i using Fin.lastCases with
    | last =>
        rw [Fin.snoc_last]
        exact congrArg f (Fin.ext
          (show (Fin.castLE hk (Fin.last k)).val = k from rfl))
    | cast i =>
        rw [Fin.snoc_castSucc]
        exact congrArg f (Fin.ext
          (show (Fin.castLE hk i.castSucc).val = (Fin.castLE (by omega) i).val from rfl))
  rw [hsnoc, evalWord_ofFn_snoc]

/-- **Chaining the overlapping windows across the bond** (arXiv:1804.04964,
Lemma 5, the step plugging `A_4` and `A_1` into `eq:normal_act_123` and
`eq:normal_act_234`, lines 2168--2210 of
`Papers/1804.04964/paper_normal.tex`).

Iterating the letter-level relation `L` times along a window of `2L` sites
moves the deformed window from the left of the bond to the right: the
leftmost deformed window contracted with the right block equals the left
block contracted with the rightmost deformed window. -/
private theorem chain_windows {B : MPSTensor d D} {L : ℕ} (hL : 0 < L)
    (C : ℕ → (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hstep : ∀ k, k < L → ∀ u : Fin (L + 1) → Fin d,
      C k (Fin.init u) * B (u (Fin.last L)) = B (u 0) * C (k + 1) (Fin.tail u))
    (a b : Fin L → Fin d) :
    C 0 a * evalWord B (List.ofFn b) = evalWord B (List.ofFn a) * C L b := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have S : ∀ k, ∀ hk : k ≤ L' + 1,
      C 0 a * evalWord B (List.ofFn fun i : Fin k => b (Fin.castLE hk i)) =
        evalWord B (List.ofFn fun i : Fin k => a (Fin.castLE hk i)) *
          C k (shiftWindow k hk a b) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp only [List.ofFn_zero, evalWord_nil, Matrix.mul_one, Matrix.one_mul]
        rw [shiftWindow_zero hk a b]
    | succ k IH =>
        intro hk1
        have hk : k ≤ L' := by omega
        set u : Fin (L' + 1 + 1) → Fin d :=
          Fin.snoc (α := fun _ => Fin d) (shiftWindow k (by omega) a b)
            (b ⟨k, by omega⟩) with hu
        have hinit : Fin.init u = shiftWindow k (by omega) a b := Fin.init_snoc _ _
        have hlast : u (Fin.last (L' + 1)) = b ⟨k, by omega⟩ := Fin.snoc_last _ _
        have hzero : u 0 = a ⟨k, by omega⟩ := by
          rw [hu, show (0 : Fin (L' + 1 + 1)) = Fin.castSucc 0 from
            Fin.castSucc_zero.symm, Fin.snoc_castSucc]
          exact shiftWindow_apply_zero hk (by omega) a b
        have htail : Fin.tail u = shiftWindow (k + 1) hk1 a b :=
          tail_snoc_shiftWindow hk (by omega) hk1 a b
        calc C 0 a *
              evalWord B (List.ofFn fun i : Fin (k + 1) => b (Fin.castLE hk1 i))
            = C 0 a * (evalWord B (List.ofFn fun i : Fin k =>
                b (Fin.castLE (by omega) i)) * B (b ⟨k, by omega⟩)) := by
              rw [evalWord_take_succ hk1 b]
          _ = (C 0 a * evalWord B (List.ofFn fun i : Fin k =>
                b (Fin.castLE (by omega) i))) * B (b ⟨k, by omega⟩) := by
              rw [Matrix.mul_assoc]
          _ = (evalWord B (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                C k (shiftWindow k (by omega) a b)) * B (b ⟨k, by omega⟩) := by
              rw [IH (by omega)]
          _ = evalWord B (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                (C k (Fin.init u) * B (u (Fin.last (L' + 1)))) := by
              rw [hinit, hlast, Matrix.mul_assoc]
          _ = evalWord B (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                (B (u 0) * C (k + 1) (Fin.tail u)) := by
              rw [hstep k (by omega) u]
          _ = (evalWord B (List.ofFn fun i : Fin k => a (Fin.castLE (by omega) i)) *
                B (a ⟨k, by omega⟩)) * C (k + 1) (shiftWindow (k + 1) hk1 a b) := by
              rw [hzero, htail, Matrix.mul_assoc]
          _ = evalWord B (List.ofFn fun i : Fin (k + 1) => a (Fin.castLE hk1 i)) *
                C (k + 1) (shiftWindow (k + 1) hk1 a b) := by
              rw [evalWord_take_succ hk1 a]
  have hfull := S (L' + 1) le_rfl
  have hcast : ∀ f : Fin (L' + 1) → Fin d,
      (fun i : Fin (L' + 1) => f (Fin.castLE le_rfl i)) = f := by
    intro f
    funext i
    exact congrArg f (Fin.ext rfl)
  rw [hcast a, hcast b, shiftWindow_self le_rfl a b] at hfull
  exact hfull

/-! ### Extracting the bond operator from the two ends -/

/-- **Uniqueness of the bond operator** (arXiv:1804.04964, Lemma 5: the maps
to `X` "are uniquely defined", lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`; the mechanism is the insertion
uniqueness of lines 1940--1960).

Two matrices multiplying every spanning word product to the same family on
the right are equal. -/
theorem bondOperator_unique {B : MPSTensor d D} {L : ℕ}
    (hB : IsNBlkInjective B L) {X X' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ a : Fin L → Fin d,
      evalWord B (List.ofFn a) * X = evalWord B (List.ofFn a) * X') : X = X' := by
  have hspan : Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
      evalWord B (List.ofFn τ)) = ⊤ := hB
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
      (Set.range fun τ : Fin L → Fin d => evalWord B (List.ofFn τ)) :=
    hspan ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
  calc X = (1 : Matrix (Fin D) (Fin D) ℂ) * X := (Matrix.one_mul _).symm
    _ = (∑ τ : Fin L → Fin d, α τ • evalWord B (List.ofFn τ)) * X := by rw [hα]
    _ = ∑ τ : Fin L → Fin d, α τ • (evalWord B (List.ofFn τ) * X) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun τ _ =>
          smul_mul_assoc (α τ) (evalWord B (List.ofFn τ)) X
    _ = ∑ τ : Fin L → Fin d, α τ • (evalWord B (List.ofFn τ) * X') :=
        Finset.sum_congr rfl fun τ _ => by rw [h τ]
    _ = (∑ τ : Fin L → Fin d, α τ • evalWord B (List.ofFn τ)) * X' := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun τ _ =>
          (smul_mul_assoc (α τ) (evalWord B (List.ofFn τ)) X').symm
    _ = X' := by rw [hα, Matrix.one_mul]

/-- **Bond-operator extraction from an intertwining pair** (arXiv:1804.04964,
Lemma 5, the comparison of the two ends, lines 2211--2255 of
`Papers/1804.04964/paper_normal.tex`, after the model of
`eq:inj_O->X_argument`, line 377).

If `F a ⬝ B^b = B^a ⬝ G b` for all length-`L` words `a`, `b`, with the word
products of `B` spanning, then a single matrix `X` factors both families:
`F` is the word products times `X` on the right, `G` is `X` times the word
products.  `X` is the combination of the `G`-family by coefficients
representing the identity, and the two factorizations agree because the
mirrored combination of the `F`-family collapses onto the same matrix. -/
theorem exists_bondOperator_of_intertwine {B : MPSTensor d D} {L : ℕ}
    (hB : IsNBlkInjective B L)
    (F G : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ a b : Fin L → Fin d,
      F a * evalWord B (List.ofFn b) = evalWord B (List.ofFn a) * G b) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      (∀ a, F a = evalWord B (List.ofFn a) * X) ∧
        (∀ b, G b = X * evalWord B (List.ofFn b)) := by
  have hspan : Submodule.span ℂ (Set.range fun τ : Fin L → Fin d =>
      evalWord B (List.ofFn τ)) = ⊤ := hB
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
      (Set.range fun τ : Fin L → Fin d => evalWord B (List.ofFn τ)) :=
    hspan ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
  set X₀ : Matrix (Fin D) (Fin D) ℂ := ∑ τ : Fin L → Fin d, α τ • G τ with hX₀
  have hF : ∀ a, F a = evalWord B (List.ofFn a) * X₀ := by
    intro a
    calc F a = F a * (1 : Matrix (Fin D) (Fin D) ℂ) := (Matrix.mul_one _).symm
      _ = F a * ∑ τ : Fin L → Fin d, α τ • evalWord B (List.ofFn τ) := by rw [hα]
      _ = ∑ τ : Fin L → Fin d, α τ • (F a * evalWord B (List.ofFn τ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ =>
            mul_smul_comm (α τ) (F a) (evalWord B (List.ofFn τ))
      _ = ∑ τ : Fin L → Fin d, α τ • (evalWord B (List.ofFn a) * G τ) :=
          Finset.sum_congr rfl fun τ _ => by rw [h a τ]
      _ = ∑ τ : Fin L → Fin d, evalWord B (List.ofFn a) * (α τ • G τ) :=
          Finset.sum_congr rfl fun τ _ =>
            (mul_smul_comm (α τ) (evalWord B (List.ofFn a)) (G τ)).symm
      _ = evalWord B (List.ofFn a) * X₀ := by rw [← Finset.mul_sum, hX₀]
  refine ⟨X₀, hF, fun b => ?_⟩
  -- The left factorization of `G`: compare against the right factorization
  -- through the intertwining relation and strip the spanning word products.
  apply bondOperator_unique hB (X := G b) (X' := X₀ * evalWord B (List.ofFn b))
  intro a
  calc evalWord B (List.ofFn a) * G b
      = F a * evalWord B (List.ofFn b) := (h a b).symm
    _ = (evalWord B (List.ofFn a) * X₀) * evalWord B (List.ofFn b) := by rw [hF a]
    _ = evalWord B (List.ofFn a) * (X₀ * evalWord B (List.ofFn b)) :=
        Matrix.mul_assoc _ _ _

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
deforming network. -/
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
  have hstep : ∀ k, k < L → ∀ u : Fin (L + 1) → Fin d,
      C k (Fin.init u) * B (u (Fin.last L)) = B (u 0) * C (k + 1) (Fin.tail u) := by
    intro k hk u
    exact window_letter_step hL hn hB (q := n - (k + (L + 1))) (by omega)
      (fun pre u' post => hstate k hk (by omega) pre u' post) u
  exact exists_bondOperator_of_intertwine hB (C 0) (C L) (chain_windows hL C hstep)

end MPSTensor
