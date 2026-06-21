import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Word-span extension and word transport for block-injective matrix tensors

This file provides the linear-algebraic inputs of the overlapping-window route
to the closed-chain corollaries of the Fundamental Theorem for normal PEPS
(arXiv:1804.04964, Section `normal_alt`, lines 1915--2295 of
`Papers/1804.04964/paper_normal.tex`), at the matrix-tensor level:

* `MPSTensor.isNBlkInjective_of_le`: block injectivity at length `L > 0`
  extends to every length `m ≥ L` — the chain form of "any region of at least
  size [`L`] is also injective" (arXiv:1804.04964, line 1940, after the union
  lemma `lem:injective_union`, lines 1324--1417).
* `MPSTensor.eq_of_trace_mul_evalWord_eq`: two matrices with the same trace
  pairing against a spanning family of word products are equal — the
  uniqueness of virtual insertions (arXiv:1804.04964, lines 1940--1960: equal
  states with insertions `X` and `Y` on the same bond force `X = Y`).
* `MPSTensor.exists_mpvTransport`: for two tensors with the same closed-chain
  coefficients at one length `n = k + q` and word products of lengths `k`, `q`
  spanning, a linear map of the matrix algebra carries each length-`k` word
  product of the first tensor to that of the second.  This is the
  operator-transport mechanism underlying the source's Lemma 5 (lines
  2045--2255): a physical operator is expanded over the window products of one
  network and re-read in the other.
* `MPSTensor.exists_evalWordTransport`: the same transport when the two
  tensors have *equal* (not just equal-trace) word products at length `n`,
  with the pairing taken in the matrix algebra.

The transports are produced by the left-inverse construction used for the
linear extension of the single-block Fundamental Theorem
(`TNLean/MPS/Structure/LinearExtension.lean`): the pairing of the matrix
algebra against the complementary word products is injective on the first
tensor's side by spanning and nondegeneracy, the same-state hypothesis
matches the two pairings on the spanning family, and a left inverse of the
second pairing assembles the transport.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section `normal_alt`, lines 1915--2295 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Block injectivity extends to longer blocks -/

/-- Left multiplication by a letter maps the full length-`m` word span into
the length-`(m+1)` word span. -/
private theorem mul_left_letter_mem_span {A : MPSTensor d D} {m : ℕ}
    (hm : Submodule.span ℂ (Set.range fun u : Fin m → Fin d =>
      evalWord A (List.ofFn u)) = ⊤)
    (i : Fin d) (Q : Matrix (Fin D) (Fin D) ℂ) :
    A i * Q ∈ Submodule.span ℂ (Set.range fun w : Fin (m + 1) → Fin d =>
      evalWord A (List.ofFn w)) := by
  have hQ : Q ∈ Submodule.span ℂ (Set.range fun u : Fin m → Fin d =>
      evalWord A (List.ofFn u)) := hm ▸ Submodule.mem_top
  induction hQ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [← evalWord_ofFn_cons]
      exact Submodule.subset_span ⟨Fin.cons i u, rfl⟩
  | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **Block injectivity extends to longer blocks.**  If the word products of
length `L > 0` span the full matrix algebra, so do the word products of any
length `m ≥ L`: write the identity as a combination of length-`L` products,
peel the leading letter of each, and absorb the remainder into the spanning
products one length below.

Source: arXiv:1804.04964, line 1940 of `Papers/1804.04964/paper_normal.tex`
("any region of at least size two is also injective", after the union lemma
`lem:injective_union`, lines 1324--1417), specialized to the closed chain
with one site-independent tensor. -/
theorem isNBlkInjective_of_le {A : MPSTensor d D} {L : ℕ} (hL : 0 < L)
    (hA : IsNBlkInjective A L) {m : ℕ} (hm : L ≤ m) : IsNBlkInjective A m := by
  induction m, hm using Nat.le_induction with
  | base => exact hA
  | succ m hLm IH =>
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      have hspanL : Submodule.span ℂ (Set.range fun v : Fin (L' + 1) → Fin d =>
          evalWord A (List.ofFn v)) = ⊤ := hA
      have hspanm : Submodule.span ℂ (Set.range fun u : Fin m → Fin d =>
          evalWord A (List.ofFn u)) = ⊤ := IH
      rw [IsNBlkInjective, eq_top_iff]
      intro P _
      have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
          Submodule.span ℂ (Set.range fun v : Fin (L' + 1) → Fin d =>
            evalWord A (List.ofFn v)) := hspanL ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
      have hP : P = ∑ v : Fin (L' + 1) → Fin d,
          c v • (evalWord A (List.ofFn v) * P) := by
        calc P = (1 : Matrix (Fin D) (Fin D) ℂ) * P := (one_mul P).symm
          _ = (∑ v : Fin (L' + 1) → Fin d, c v • evalWord A (List.ofFn v)) * P := by
              rw [hc]
          _ = ∑ v : Fin (L' + 1) → Fin d, c v • (evalWord A (List.ofFn v) * P) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun v _ => smul_mul_assoc _ _ _
      rw [hP]
      refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ ?_
      have hsplit : evalWord A (List.ofFn v) * P =
          A (v 0) * (evalWord A (List.ofFn (Fin.tail v)) * P) := by
        rw [show v = Fin.cons (v 0) (Fin.tail v) from (Fin.cons_self_tail v).symm,
          evalWord_ofFn_cons, Matrix.mul_assoc, Fin.cons_zero, Fin.tail_cons]
      rw [hsplit]
      exact mul_left_letter_mem_span hspanm (v 0) _

/-! ### Trace stripping against a spanning word family -/

/-- **Uniqueness of virtual insertions.**  Two matrices with the same trace
pairing against a spanning family of word products are equal.

Source: arXiv:1804.04964, lines 1940--1960 of
`Papers/1804.04964/paper_normal.tex`: two insertions `X`, `Y` on the same
bond generating the same state are equal, by injectivity of the rest of the
chain. -/
theorem eq_of_trace_mul_evalWord_eq {B : MPSTensor d D} {m : ℕ}
    (hspan : Submodule.span ℂ (Set.range fun ρ : Fin m → Fin d =>
      evalWord B (List.ofFn ρ)) = ⊤)
    {M N : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ ρ : Fin m → Fin d,
      Matrix.trace (M * evalWord B (List.ofFn ρ)) =
        Matrix.trace (N * evalWord B (List.ofFn ρ))) : M = N := by
  have hmaps :
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ M) =
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ N) := by
    apply LinearMap.ext_on_range
      (v := fun ρ : Fin m → Fin d => evalWord B (List.ofFn ρ)) (hv := hspan)
    intro ρ
    simpa only [Matrix.traceLinearMap_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply] using h ρ
  apply (Matrix.ext_iff_trace_mul_right).2
  intro Q
  simpa only [Matrix.traceLinearMap_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply] using congrArg (fun f => f Q) hmaps

/-! ### The generic transport construction -/

/-- **Transport through a pair of matched pairings.**  Given two families
`F`, `G` of matrices indexed by the same finite type, with `F` spanning, and
two linear pairings `ΨA`, `ΨB` of the matrix algebra into a common space such
that `ΨA` is injective and `ΨA (F i) = ΨB (G i)` for every index, there is a
linear map of the matrix algebra carrying each `F i` to `G i`.  This is the
left-inverse construction of the linear extension for the single-block
Fundamental Theorem (`TNLean/MPS/Structure/LinearExtension.lean`).  The
site-dependent arc transports of
`TNLean/PEPS/CycleMPSChainOverlapInsertion.lean` consume it as well. -/
theorem exists_linearMap_apply_eq {ι : Type*} [Finite ι]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F G : ι → Matrix (Fin D) (Fin D) ℂ)
    (ΨA ΨB : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] V)
    (hspan : Submodule.span ℂ (Set.range F) = ⊤)
    (hker : LinearMap.ker ΨA = ⊥)
    (hpair : ∀ i, ΨA (F i) = ΨB (G i)) :
    ∃ Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      ∀ i, Λ (F i) = G i := by
  classical
  cases nonempty_fintype ι
  let lcF := Fintype.linearCombination ℂ F
  let lcG := Fintype.linearCombination ℂ G
  have hsurj : Function.Surjective lcF := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  have hcomp : ΨA ∘ₗ lcF = ΨB ∘ₗ lcG := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, lcF, lcG, Fintype.linearCombination_apply,
      map_sum, map_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [hpair i]
  have hrange : LinearMap.range ΨA ≤ LinearMap.range ΨB := by
    rw [show LinearMap.range ΨA = LinearMap.range (ΨA ∘ₗ lcF) from by
      simp [LinearMap.range_comp, LinearMap.range_eq_top.2 hsurj], hcomp]
    exact LinearMap.range_comp_le_range lcG ΨB
  have hkerB : LinearMap.ker ΨB = ⊥ := ker_bot_of_range_le ΨA ΨB hker hrange
  obtain ⟨g, hg⟩ := ΨB.exists_leftInverse_of_injective hkerB
  refine ⟨g ∘ₗ ΨA, fun i => ?_⟩
  rw [LinearMap.comp_apply, hpair i]
  simpa using congrArg (· (G i)) hg

/-! ### Bridging closed-chain coefficients and word lists -/

/-- Equality of the closed-chain coefficients at length `n`, read on word
lists of length `n`. -/
theorem trace_evalWord_eq_of_mpv_eq {A B : MPSTensor d D} {n : ℕ}
    (hAB : ∀ σ : Fin n → Fin d, mpv A σ = mpv B σ)
    {w : List (Fin d)} (hw : w.length = n) :
    Matrix.trace (evalWord A w) = Matrix.trace (evalWord B w) := by
  subst hw
  simpa [mpv, coeff, List.ofFn_get] using hAB w.get

/-- Equality of the word products at length `n`, read on word lists of
length `n`. -/
theorem evalWord_eq_of_forall_fin_eq {A C : MPSTensor d D} {n : ℕ}
    (hAC : ∀ σ : Fin n → Fin d,
      evalWord C (List.ofFn σ) = evalWord A (List.ofFn σ))
    {w : List (Fin d)} (hw : w.length = n) :
    evalWord C w = evalWord A w := by
  subst hw
  simpa [List.ofFn_get] using hAC w.get

/-! ### The two transports -/

/-- **Word transport from equal closed-chain coefficients** (the mechanism of
arXiv:1804.04964, Lemma 5, lines 2045--2255 of
`Papers/1804.04964/paper_normal.tex`).

If `A` and `B` have the same closed-chain coefficients at one length
`n = k + q`, and the length-`k` and length-`q` word products of `A` span the
matrix algebra, then a linear map `Λ` of the matrix algebra carries every
length-`k` word product of `A` to the corresponding word product of `B`.
This is the matrix-level form of expanding a physical operator over the
window products of one network and re-reading the expansion in the other:
the pairing against the complementary length-`q` products is injective for
`A` by spanning and trace nondegeneracy, and the same-state hypothesis
matches the `A`- and `B`-pairings on the spanning window family. -/
theorem exists_mpvTransport {A B : MPSTensor d D} {n k q : ℕ} (hkq : k + q = n)
    (hAk : Submodule.span ℂ (Set.range fun τ : Fin k → Fin d =>
      evalWord A (List.ofFn τ)) = ⊤)
    (hAq : Submodule.span ℂ (Set.range fun ρ : Fin q → Fin d =>
      evalWord A (List.ofFn ρ)) = ⊤)
    (hAB : ∀ σ : Fin n → Fin d, mpv A σ = mpv B σ) :
    ∃ Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      ∀ τ : Fin k → Fin d,
        Λ (evalWord A (List.ofFn τ)) = evalWord B (List.ofFn τ) := by
  classical
  set ΨA : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ((Fin q → Fin d) → ℂ) :=
    LinearMap.pi fun ρ => (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulRight ℂ (evalWord A (List.ofFn ρ))) with hΨA
  set ΨB : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ((Fin q → Fin d) → ℂ) :=
    LinearMap.pi fun ρ => (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulRight ℂ (evalWord B (List.ofFn ρ))) with hΨB
  have hΨA_apply : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Fin q → Fin d),
      ΨA M ρ = Matrix.trace (M * evalWord A (List.ofFn ρ)) := fun M ρ => rfl
  have hΨB_apply : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Fin q → Fin d),
      ΨB M ρ = Matrix.trace (M * evalWord B (List.ofFn ρ)) := fun M ρ => rfl
  refine exists_linearMap_apply_eq _ _ ΨA ΨB hAk ?_ ?_
  · -- Injectivity of the `A`-pairing: spanning at length `q` plus trace
    -- nondegeneracy.
    rw [LinearMap.ker_eq_bot']
    intro M hM
    have h : ∀ ρ : Fin q → Fin d,
        Matrix.trace (M * evalWord A (List.ofFn ρ)) =
          Matrix.trace ((0 : Matrix (Fin D) (Fin D) ℂ) * evalWord A (List.ofFn ρ)) := by
      intro ρ
      rw [Matrix.zero_mul, Matrix.trace_zero, ← hΨA_apply]
      exact congrArg (· ρ) hM
    exact eq_of_trace_mul_evalWord_eq hAq h
  · -- The two pairings match on the spanning window family: both compute the
    -- closed-chain coefficient of the concatenated word, equal at length `n`.
    intro τ
    funext ρ
    rw [hΨA_apply, hΨB_apply, ← evalWord_append, ← evalWord_append]
    exact trace_evalWord_eq_of_mpv_eq hAB (by simp [hkq])

/-- **Word transport from equal word products.**  If `C` and `A` have equal
word products at one length `n = k + q` — not only equal traces — and the
length-`k` and length-`q` word products of `A` span, then a linear map `Λ`
carries every length-`k` word product of `A` to that of `C`.  The pairing is
taken in the matrix algebra rather than through the trace.

This is the transport used after the gauge of arXiv:1804.04964 Lemma 5
(lines 2045--2255 of `Papers/1804.04964/paper_normal.tex`) has been absorbed,
when the two closed chains have matching matrix products at length `n`. -/
theorem exists_evalWordTransport {A C : MPSTensor d D} {n k q : ℕ} (hkq : k + q = n)
    (hAk : Submodule.span ℂ (Set.range fun τ : Fin k → Fin d =>
      evalWord A (List.ofFn τ)) = ⊤)
    (hAq : Submodule.span ℂ (Set.range fun ρ : Fin q → Fin d =>
      evalWord A (List.ofFn ρ)) = ⊤)
    (hAC : ∀ w : List (Fin d), w.length = n → evalWord C w = evalWord A w) :
    ∃ Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      ∀ τ : Fin k → Fin d,
        Λ (evalWord A (List.ofFn τ)) = evalWord C (List.ofFn τ) := by
  classical
  set ΨA : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((Fin q → Fin d) → Matrix (Fin D) (Fin D) ℂ) :=
    LinearMap.pi fun ρ => LinearMap.mulRight ℂ (evalWord A (List.ofFn ρ)) with hΨA
  set ΨC : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((Fin q → Fin d) → Matrix (Fin D) (Fin D) ℂ) :=
    LinearMap.pi fun ρ => LinearMap.mulRight ℂ (evalWord C (List.ofFn ρ)) with hΨC
  have hΨA_apply : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Fin q → Fin d),
      ΨA M ρ = M * evalWord A (List.ofFn ρ) := fun M ρ => rfl
  have hΨC_apply : ∀ (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Fin q → Fin d),
      ΨC M ρ = M * evalWord C (List.ofFn ρ) := fun M ρ => rfl
  refine exists_linearMap_apply_eq _ _ ΨA ΨC hAk ?_ ?_
  · -- Injectivity of the `A`-pairing: a matrix annihilating a spanning
    -- family on the right annihilates the identity.
    rw [LinearMap.ker_eq_bot']
    intro M hM
    have hQ : ∀ Q : Matrix (Fin D) (Fin D) ℂ, M * Q = 0 := by
      intro Q
      have hQmem : Q ∈ Submodule.span ℂ (Set.range fun ρ : Fin q → Fin d =>
          evalWord A (List.ofFn ρ)) := hAq ▸ Submodule.mem_top
      induction hQmem using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨ρ, rfl⟩ := hx
          rw [← hΨA_apply]
          exact congrArg (· ρ) hM
      | zero => rw [Matrix.mul_zero]
      | add x y _ _ hx hy => rw [Matrix.mul_add, hx, hy, add_zero]
      | smul c x _ hx => rw [Matrix.mul_smul, hx, smul_zero]
    calc M = M * 1 := (Matrix.mul_one M).symm
      _ = 0 := hQ 1
  · -- The two pairings match on the spanning window family: both compute the
    -- length-`n` matrix product of the concatenated word.
    intro τ
    funext ρ
    rw [hΨA_apply, hΨC_apply, ← evalWord_append, ← evalWord_append]
    exact (evalWord_eq_of_forall_fin_eq (n := n)
      (fun σ => hAC (List.ofFn σ) (by simp)) (by simp [hkq])).symm

end MPSTensor
