import TNLean.MPS.Chain.Defs
import TNLean.Algebra.TracePairing

/-!
# Arc products and window injectivity for site-dependent closed chains

This file provides the site-dependent vocabulary for the overlapping-window
route to the closed-chain corollaries of the Fundamental Theorem for normal
PEPS (arXiv:1804.04964, Section `normal_alt`, lines 1915--2295 of
`Papers/1804.04964/paper_normal.tex`).  The source states its Lemma 5 (lines
2045--2255) for site-dependent tensors `A_1, …, A_5` on five sites whose
two-site windows are injective; the previously landed development
(`TNLean/PEPS/CycleMPSOverlapWindow.lean` and its consumers) specializes to
one site-independent tensor.  Here the closed chain carries a family of
tensors, one per site (`MPSChainTensor d D n`), and the basic objects are

* `MPSChainTensor.arcEval`: the ordered product of the letters of a word
  along an arc of consecutive sites, starting at a given site of the closed
  chain; site indices wrap around the chain.
* `MPSChainTensor.IsWindowInjective`: every window of `L` consecutive sites
  is injective — the word products of the window span the full matrix
  algebra (the source's "the blocking of any two consecutive tensors is
  injective", lines 1928--1940, for the general window length `L`).
* `MPSChainTensor.IsWindowInjective.arc_span`: every arc of at least `L`
  sites is then injective as well — the site-dependent form of "any region
  of at least size two is also injective" (line 1940).
* `MPSChainTensor.SameState.trace_arcEval_eq`: equality of the closed-chain
  states read on words based at an arbitrary site, by rotating the trace
  once around the chain.

The file also records the spanning-family forms of the trace-stripping and
factor-uniqueness arguments used by the route
(`eq_of_trace_pairing_span`, `eq_of_span_mul_left`, `eq_of_mul_span_right`),
stated for an arbitrary spanning family of matrices so that both the
site-independent word products and the site-dependent arc products feed
them.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one bond
dimension `D`, matching the chain vocabulary of `TNLean/MPS/Chain/Defs.lean`.
Documented in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

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

/-! ### Arc products along the closed chain -/

/-- **The arc product of a site-dependent chain** (arXiv:1804.04964, the
site-dependent windows of Section `normal_alt`, lines 1915--2255 of
`Papers/1804.04964/paper_normal.tex`).  The word `w` is read on the arc of
consecutive sites starting at site `s` of the closed chain: the first letter
is contracted with the tensor at site `s`, the second with the tensor at
site `s + 1`, and so on, indices wrapping around the chain. -/
def arcEval [NeZero n] (A : MPSChainTensor d D n) :
    ℕ → List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | _, [] => 1
  | s, i :: w => A (s : Fin n) i * arcEval A (s + 1) w

@[simp] lemma arcEval_nil [NeZero n] (A : MPSChainTensor d D n) (s : ℕ) :
    arcEval A s [] = 1 := rfl

@[simp] lemma arcEval_cons [NeZero n] (A : MPSChainTensor d D n) (s : ℕ)
    (i : Fin d) (w : List (Fin d)) :
    arcEval A s (i :: w) = A (s : Fin n) i * arcEval A (s + 1) w := rfl

/-- Concatenation splits the arc product at the matching intermediate
site. -/
lemma arcEval_append [NeZero n] (A : MPSChainTensor d D n) (s : ℕ)
    (w₁ w₂ : List (Fin d)) :
    arcEval A s (w₁ ++ w₂) = arcEval A s w₁ * arcEval A (s + w₁.length) w₂ := by
  induction w₁ generalizing s with
  | nil => simp
  | cons i w₁ ih =>
      rw [List.cons_append, arcEval_cons, arcEval_cons, ih (s + 1),
        Matrix.mul_assoc, List.length_cons,
        show s + (w₁.length + 1) = s + 1 + w₁.length by omega]

/-- The arc product depends on its starting site only through its residue on
the closed chain. -/
lemma arcEval_add_n [NeZero n] (A : MPSChainTensor d D n) (s : ℕ)
    (w : List (Fin d)) : arcEval A (s + n) w = arcEval A s w := by
  induction w generalizing s with
  | nil => simp
  | cons i w ih =>
      rw [arcEval_cons, arcEval_cons, show s + n + 1 = s + 1 + n by omega, ih,
        Nat.cast_add, Fin.natCast_self, add_zero]

/-- The arc product depends on its starting site only modulo the chain
length. -/
lemma arcEval_mod [NeZero n] (A : MPSChainTensor d D n) (s : ℕ)
    (w : List (Fin d)) : arcEval A (s % n) w = arcEval A s w := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      rcases lt_or_ge s n with hs | hs
      · rw [Nat.mod_eq_of_lt hs]
      · conv_rhs => rw [show s = s - n + n by omega]
        rw [arcEval_add_n, Nat.mod_eq_sub_mod hs]
        exact ih (s - n) (by omega)

/-- On the constant chain the arc product is the word product of the
repeated tensor. -/
lemma arcEval_const [NeZero n] (B : MPSTensor d D) (s : ℕ) (w : List (Fin d)) :
    arcEval (fun _ : Fin n => B) s w = MPSTensor.evalWord B w := by
  induction w generalizing s with
  | nil => rfl
  | cons i w ih => rw [arcEval_cons, MPSTensor.evalWord_cons, ih (s + 1)]

/-- **Arc products telescope under a cyclic gauge**
(arXiv:1804.04964, Applications section, lines 1863--1889).

If two site-dependent chains are related by a cyclic virtual gauge, then every
arc product of the second chain is the corresponding arc product of the first
chain conjugated by the gauges at the two boundary bonds.  For a full closed
chain this is the cancellation mechanism behind the source's substitution of
the \(L_i,R_i\) expression into the trace. -/
theorem arcEval_eq_gauge_conj [NeZero n] {A B : MPSChainTensor d D n}
    {Z : Fin n → GL (Fin D) ℂ}
    (hZ : ∀ (k : Fin n) (i : Fin d),
      B k i = (Z k : Matrix (Fin D) (Fin D) ℂ) * A k i *
        (((Z (cyclicSucc k))⁻¹ : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ))
    (s : ℕ) (w : List (Fin d)) :
    arcEval B s w =
      (Z (s : Fin n) : Matrix (Fin D) (Fin D) ℂ) * arcEval A s w *
        (((Z ((s + w.length : ℕ) : Fin n))⁻¹ : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ) := by
  induction w generalizing s with
  | nil =>
      simp only [arcEval_nil, List.length_nil, Nat.add_zero, Matrix.mul_one,
        Units.mul_inv]
  | cons i w ih =>
      have hsucc : cyclicSucc (s : Fin n) = ((s + 1 : ℕ) : Fin n) := by
        rw [cyclicSucc_eq_add_one]
        norm_num [Nat.cast_add]
      have hlen : s + (i :: w).length = s + 1 + w.length := by
        rw [List.length_cons]
        omega
      rw [arcEval_cons, arcEval_cons, hZ (s : Fin n) i, hsucc, ih (s + 1), hlen]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

/-- The arc product of the word of the first `k + 1` letters of a tuple
peels its last letter at the matching site. -/
lemma arcEval_take_succ [NeZero n] (A : MPSChainTensor d D n) (s : ℕ)
    {L k : ℕ} (hk : k + 1 ≤ L) (f : Fin L → Fin d) :
    arcEval A s (List.ofFn fun i : Fin (k + 1) => f (Fin.castLE hk i)) =
      arcEval A s (List.ofFn fun i : Fin k => f (Fin.castLE (by omega) i)) *
        A ((s + k : ℕ) : Fin n) (f ⟨k, by omega⟩) := by
  have hsnoc : (List.ofFn fun i : Fin (k + 1) => f (Fin.castLE hk i)) =
      (List.ofFn fun i : Fin k => f (Fin.castLE (by omega) i)) ++ [f ⟨k, by omega⟩] := by
    rw [List.ofFn_succ' fun i : Fin (k + 1) => f (Fin.castLE hk i),
      List.concat_eq_append]
    congr 1
  rw [hsnoc, arcEval_append, List.length_ofFn, arcEval_cons, arcEval_nil,
    Matrix.mul_one]

/-! ### Window injectivity and arc spanning -/

/-- **Window injectivity of a site-dependent chain** (arXiv:1804.04964,
Section `normal_alt`: "the blocking of any two consecutive tensors … is
injective", lines 1928--1940 of `Papers/1804.04964/paper_normal.tex`, for a
general window length `L`).  Every window of `L` consecutive sites of the
closed chain is injective: the arc products of the window span the full
matrix algebra.  The starting site ranges over `ℕ`; by
`MPSChainTensor.arcEval_mod` this quantifies exactly over the `n` windows of
the chain. -/
def IsWindowInjective [NeZero n] (A : MPSChainTensor d D n) (L : ℕ) : Prop :=
  ∀ s : ℕ, Submodule.span ℂ (Set.range fun a : Fin L → Fin d =>
    arcEval A s (List.ofFn a)) = ⊤

/-- A site-independent block-injective tensor is window injective as a
constant chain. -/
theorem isWindowInjective_const [NeZero n] {B : MPSTensor d D} {L : ℕ}
    (hB : MPSTensor.IsNBlkInjective B L) :
    IsWindowInjective (fun _ : Fin n => B) L := by
  intro s
  have hcast : (fun a : Fin L → Fin d =>
      arcEval (fun _ : Fin n => B) s (List.ofFn a)) =
      fun a : Fin L → Fin d => MPSTensor.evalWord B (List.ofFn a) := by
    funext a
    exact arcEval_const B s (List.ofFn a)
  rw [hcast]
  exact hB

/-- Sitewise algebraic injectivity is window injectivity at length one.

This is the `L = 1` specialization used for the injective closed-chain
Fundamental Theorem in arXiv:1804.04964, Theorem `thm:inj_MPS`
(lines 688--725). -/
theorem isWindowInjective_one_of_isInjective [NeZero n] {A : MPSChainTensor d D n}
    (hA : IsInjective A) : IsWindowInjective A 1 := by
  intro s
  have hrange : (Set.range fun a : Fin 1 → Fin d => arcEval A s (List.ofFn a)) =
      Set.range (A (s : Fin n)) := by
    ext M
    constructor
    · rintro ⟨a, hM⟩
      refine ⟨a 0, ?_⟩
      simpa only [List.ofFn_succ, List.ofFn_zero, arcEval_cons, arcEval_nil,
        Matrix.mul_one] using hM
    · rintro ⟨i, hM⟩
      refine ⟨fun _ => i, ?_⟩
      simpa only [List.ofFn_succ, List.ofFn_zero, arcEval_cons, arcEval_nil,
        Matrix.mul_one] using hM
  rw [hrange]
  exact hA (s : Fin n)

/-- Left multiplication by the letter at the preceding site maps the full
arc span one site downstream into the arc span one letter longer. -/
private theorem mul_left_letter_mem_arc_span [NeZero n]
    {A : MPSChainTensor d D n} {m s : ℕ}
    (hm : Submodule.span ℂ (Set.range fun u : Fin m → Fin d =>
      arcEval A (s + 1) (List.ofFn u)) = ⊤)
    (i : Fin d) (Q : Matrix (Fin D) (Fin D) ℂ) :
    A (s : Fin n) i * Q ∈ Submodule.span ℂ
      (Set.range fun w : Fin (m + 1) → Fin d => arcEval A s (List.ofFn w)) := by
  have hQ : Q ∈ Submodule.span ℂ (Set.range fun u : Fin m → Fin d =>
      arcEval A (s + 1) (List.ofFn u)) := hm ▸ Submodule.mem_top
  induction hQ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      change A (s : Fin n) i * arcEval A (s + 1) (List.ofFn u) ∈ _
      have hcons : arcEval A s (List.ofFn (Fin.cons i u)) =
          A (s : Fin n) i * arcEval A (s + 1) (List.ofFn u) := by
        rw [List.ofFn_succ, arcEval_cons, Fin.cons_zero]
        simp only [Fin.cons_succ]
      exact Submodule.subset_span ⟨Fin.cons i u, hcons⟩
  | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **Arc spanning from window injectivity** (arXiv:1804.04964, Section
`normal_alt`, line 1940 of `Papers/1804.04964/paper_normal.tex`: "any region
of at least size two is also injective", site-dependent form for a general
window length `L`).  If every window of `L > 0` consecutive sites is
injective, then the arc products of any length `m ≥ L`, starting at any
site, span the full matrix algebra: write the identity as a combination of
window products at the starting site, peel the leading letter of each, and
absorb the remainder into the spanning arcs one site downstream and one
letter shorter. -/
theorem IsWindowInjective.arc_span [NeZero n] {A : MPSChainTensor d D n}
    {L : ℕ} (hL : 0 < L) (hA : IsWindowInjective A L) {m : ℕ} (hm : L ≤ m)
    (s : ℕ) :
    Submodule.span ℂ (Set.range fun ρ : Fin m → Fin d =>
      arcEval A s (List.ofFn ρ)) = ⊤ := by
  induction m, hm using Nat.le_induction generalizing s with
  | base => exact hA s
  | succ m hLm IH =>
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      rw [eq_top_iff]
      intro P _
      have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
          Submodule.span ℂ (Set.range fun v : Fin (L' + 1) → Fin d =>
            arcEval A s (List.ofFn v)) := (hA s) ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
      have hP : P = ∑ v : Fin (L' + 1) → Fin d,
          c v • (arcEval A s (List.ofFn v) * P) := by
        calc P = (1 : Matrix (Fin D) (Fin D) ℂ) * P := (one_mul P).symm
          _ = (∑ v : Fin (L' + 1) → Fin d,
                c v • arcEval A s (List.ofFn v)) * P := by rw [hc]
          _ = ∑ v : Fin (L' + 1) → Fin d,
                c v • (arcEval A s (List.ofFn v) * P) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun v _ => smul_mul_assoc _ _ _
      rw [hP]
      refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ ?_
      have hsplit : arcEval A s (List.ofFn v) * P =
          A (s : Fin n) (v 0) * (arcEval A (s + 1) (List.ofFn (Fin.tail v)) * P) := by
        rw [List.ofFn_succ, arcEval_cons, Matrix.mul_assoc]
        rfl
      rw [hsplit]
      exact mul_left_letter_mem_arc_span (IH (s + 1)) (v 0) _

/-! ### Reading the closed-chain state on rotated arcs -/

/-- The arc product of a word of tuple letters is the ordered product of the
matrices selected at the rebased sites. -/
private theorem arcEval_ofFn_eq_prod [NeZero n] (A : MPSChainTensor d D n) :
    ∀ {m : ℕ} (g : Fin m → Fin n) (τ : Fin m → Fin d) (s : ℕ),
      (∀ k : Fin m, ((s + k.val : ℕ) : Fin n) = g k) →
      arcEval A s (List.ofFn τ) = Fin.prod fun k => A (g k) (τ k) := by
  intro m
  induction m with
  | zero =>
      intro g τ s hg
      rw [List.ofFn_zero, arcEval_nil, Fin.prod_zero]
  | succ m ih =>
      intro g τ s hg
      rw [List.ofFn_succ, arcEval_cons,
        Fin.prod_succ fun k => A (g k) (τ k)]
      congr 1
      · rw [← hg 0]
        norm_num
      · exact ih (fun k => g k.succ) (fun k => τ k.succ) (s + 1) fun k => by
          change ((s + 1 + k.val : ℕ) : Fin n) = g k.succ
          rw [← hg k.succ]
          congr 1
          rw [Fin.val_succ]
          omega

/-- The closed-chain coefficient is the trace of the arc product based at
site `0`. -/
lemma coeff_eq_trace_arcEval [NeZero n] (A : MPSChainTensor d D n)
    (σ : Fin n → Fin d) :
    coeff A σ = Matrix.trace (arcEval A 0 (List.ofFn σ)) := by
  rw [coeff_eq]
  congr 1
  rw [arcEval_ofFn_eq_prod A (fun k => k) σ 0 fun k => by
    rw [Nat.zero_add, Fin.cast_val_eq_self]]
  rfl

/-- A cyclic virtual gauge leaves the closed-chain state unchanged
(arXiv:1804.04964, Applications section, lines 1863--1889). -/
theorem GaugeEquiv.sameState [NeZero n] {A B : MPSChainTensor d D n}
    (hAB : GaugeEquiv A B) : SameState A B := by
  obtain ⟨Z, hZ⟩ := hAB
  intro σ
  rw [coeff_eq_trace_arcEval A σ, coeff_eq_trace_arcEval B σ]
  have hEval := arcEval_eq_gauge_conj (A := A) (B := B) (Z := Z) hZ 0 (List.ofFn σ)
  rw [hEval, List.length_ofFn]
  simpa using (MPSTensor.trace_conj_eq (Z 0) (arcEval A 0 (List.ofFn σ))).symm

/-- Rotating the closed trace one site forward: the leading letter moves to
the end of the word, and the arc rebases one site downstream. -/
private theorem trace_arcEval_rotate_one [NeZero n] (A : MPSChainTensor d D n)
    (s : ℕ) (i : Fin d) {w : List (Fin d)} (hw : (i :: w).length = n) :
    Matrix.trace (arcEval A s (i :: w)) =
      Matrix.trace (arcEval A (s + 1) (w ++ [i])) := by
  rw [arcEval_cons, Matrix.trace_mul_comm, arcEval_append, arcEval_cons,
    arcEval_nil, Matrix.mul_one]
  congr 2
  have hlen : s + 1 + w.length = s + n := by
    simp only [List.length_cons] at hw
    omega
  rw [hlen, Nat.cast_add, Fin.natCast_self, add_zero]

/-- **The closed-chain state read on rotated arcs.**  Two site-dependent
chains generating the same state have equal traces on full-length words
based at every site, not only at site `0`: rotate the trace once around the
chain (arXiv:1804.04964, the cyclic reading of the closed-chain state used
throughout Section `normal_alt`, lines 1915--2295 of
`Papers/1804.04964/paper_normal.tex`). -/
theorem SameState.trace_arcEval_eq [NeZero n] {A B : MPSChainTensor d D n}
    (hAB : SameState A B) (s : ℕ) {w : List (Fin d)} (hw : w.length = n) :
    Matrix.trace (arcEval A s w) = Matrix.trace (arcEval B s w) := by
  induction s generalizing w with
  | zero =>
      obtain ⟨σ, rfl⟩ : ∃ σ : Fin n → Fin d, List.ofFn σ = w := by
        subst hw
        exact ⟨w.get, List.ofFn_get w⟩
      rw [← coeff_eq_trace_arcEval, ← coeff_eq_trace_arcEval]
      exact hAB σ
  | succ s ih =>
      rcases w.eq_nil_or_concat' with rfl | ⟨u, j, rfl⟩
      · rw [List.length_nil] at hw
        exact absurd hw.symm (NeZero.ne n)
      · have hlen : (j :: u).length = n := by
          simpa using hw
        rw [← trace_arcEval_rotate_one A s j hlen,
          ← trace_arcEval_rotate_one B s j hlen]
        exact ih hlen

/-! ### Spanning-family stripping lemmas -/

/-- **Trace stripping against a spanning family.**  Two matrices with the
same trace pairing against a spanning family of matrices are equal — the
spanning-family form of the uniqueness of virtual insertions
(arXiv:1804.04964, lines 1940--1960 of
`Papers/1804.04964/paper_normal.tex`). -/
theorem eq_of_trace_pairing_span {ι : Sort*} {F : ι → Matrix (Fin D) (Fin D) ℂ}
    (hspan : Submodule.span ℂ (Set.range F) = ⊤)
    {M N : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ i, Matrix.trace (M * F i) = Matrix.trace (N * F i)) : M = N := by
  have hzero : ∀ Q : Matrix (Fin D) (Fin D) ℂ,
      Matrix.trace ((M - N) * Q) = 0 := by
    intro Q
    have hQ : Q ∈ Submodule.span ℂ (Set.range F) := hspan ▸ Submodule.mem_top
    induction hQ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [Matrix.sub_mul, Matrix.trace_sub, h i, sub_self]
    | zero => rw [Matrix.mul_zero, Matrix.trace_zero]
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]
  exact sub_eq_zero.mp (MPSTensor.trace_mul_right_eq_zero hzero)

/-- **Uniqueness of a right factor against a spanning family** — the
spanning-family form of the uniqueness of the bond operator
(arXiv:1804.04964, Lemma 5: the maps to `X` "are uniquely defined", lines
2045--2255 of `Papers/1804.04964/paper_normal.tex`).  Two matrices
multiplying every member of a spanning family to the same product on the
right are equal. -/
theorem eq_of_span_mul_left {ι : Type*} [Finite ι]
    {W : ι → Matrix (Fin D) (Fin D) ℂ}
    (hspan : Submodule.span ℂ (Set.range W) = ⊤)
    {X X' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ i, W i * X = W i * X') : X = X' := by
  cases nonempty_fintype ι
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range W) := hspan ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
  calc X = (1 : Matrix (Fin D) (Fin D) ℂ) * X := (Matrix.one_mul _).symm
    _ = (∑ i, α i • W i) * X := by rw [hα]
    _ = ∑ i, α i • (W i * X) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => smul_mul_assoc _ _ _
    _ = ∑ i, α i • (W i * X') := Finset.sum_congr rfl fun i _ => by rw [h i]
    _ = (∑ i, α i • W i) * X' := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm
    _ = X' := by rw [hα, Matrix.one_mul]

/-- **Uniqueness of a left factor against a spanning family** — the mirror
of `MPSChainTensor.eq_of_span_mul_left`. -/
theorem eq_of_mul_span_right {ι : Type*} [Finite ι]
    {W : ι → Matrix (Fin D) (Fin D) ℂ}
    (hspan : Submodule.span ℂ (Set.range W) = ⊤)
    {X X' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ i, X * W i = X' * W i) : X = X' := by
  cases nonempty_fintype ι
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range W) := hspan ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
  calc X = X * (1 : Matrix (Fin D) (Fin D) ℂ) := (Matrix.mul_one _).symm
    _ = X * ∑ i, α i • W i := by rw [hα]
    _ = ∑ i, α i • (X * W i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    _ = ∑ i, α i • (X' * W i) := Finset.sum_congr rfl fun i _ => by rw [h i]
    _ = X' * ∑ i, α i • W i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (mul_smul_comm _ _ _).symm
    _ = X' := by rw [hα, Matrix.mul_one]

end MPSChainTensor
