/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.BlockStrip
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.FundamentalTheorem.FiniteLength
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan

/-!
# Periodic boundary closure for MPS chains

This file proves that the boundary matrix \(X\) arising from the open-chain
intersection property commutes with all one-site matrices \(A_j\) of an
injective MPS tensor on a periodic chain.

## Proof strategy

On a periodic chain of \(N\) sites with window size \(L\), the boundary-crossing
cyclic window starts at position \(N-1\) and contains the first \(L-1\) sites. The proof
proceeds as follows:

1. At the boundary-crossing position \(N-1\), the cyclic configuration separates into
   the \(L\) sites of the boundary-crossing support and the complementary
   sites labelled by \(\tau\).

2. The corresponding word product factors as
   \(A^{\mathrm{tail}}A^{\mathrm{comp}}A^{\sigma_0}\), so trace cyclicity
   rotates the tensor at the periodic boundary.

3. The rotation gives an identity of the form
   \(X A^{\mathrm{tail}}A^{\mathrm{comp}}
     = A^{\mathrm{tail}}Y_\tau\)
   for every boundary tail and every condition on the complementary sites.

4. Block injectivity extends the identity from word products to the full
   matrix algebra. Applying the same spanning argument to the complementary
   words gives \(XM=MX\) for every matrix \(M\), hence \(XA_j=A_jX\).

## Main results

The main statements show that the two identities
\[
  A^\mu A^j X = Y_\mu A^j,
  \qquad
  X A^j A^\mu = A^jY_\mu
\]
imply commutation with fixed-length word products; that fixed-length
commutation propagates to long words; and that block injectivity then gives
\(XA_j=A_jX\) for every one-site matrix. They also record the one-sided
uniqueness consequences of block injectivity used in the periodic-boundary
comparison.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C, lines 1976--2094
* [FNW92] Sections 3–4

## External input — Quantum Wielandt vector-to-matrix span

This file imports `TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan`, which supplies
the spanning step used in the periodic boundary-closure argument:

> **Vector-to-matrix spanning step (arXiv:0909.5347, Lemma 2(a) / Wolf Chapter 6).**
> If the vector-valued images of Kraus word products span the full vector space
> \(ℂ^D\), then the matrix-valued word products span the full matrix
> algebra \(M_D(ℂ)\).  Concretely: \(\operatorname{span}\{A_w v\} = \mathbb C^D\)
> for all \(v \ne 0\) implies \(\operatorname{span}\{A_w\} = M_D(\mathbb C)\).

In MPS notation after blocking: for an injective tensor \(A\), the Kraus word
products of length \(L-1\) span \(M_D(\mathbb C)\).
This spanning conclusion is what allows the proof to extend the word-compatibility
identity from word products to arbitrary matrices \(M\), yielding \(XM=MX\)
for all matrices \(M\), hence \(XA_j=A_jX\) for each one-site matrix.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

private theorem fin_cons_mk_succ {L : ℕ} (i : Fin d) (σ : Fin L → Fin d)
    (k : Fin L) (h : k.val + 1 < L + 1) :
    (Fin.cons (n := L) (α := fun _ => Fin d) i σ) ⟨k.val + 1, h⟩ = σ k := by
  have hidx : (⟨k.val + 1, h⟩ : Fin (L + 1)) = k.succ := by
    ext
    rfl
  rw [hidx, Fin.cons_succ]

/-! ### Cyclic config decomposition at the last-site boundary-crossing position

These lemmas analyze the structure of `cyclicCfg` at position \(N-1\),
where the window wraps from the last site back to the first sites. -/

/-- At the last-site boundary-crossing position \(N-1\), the cyclic config's last site is
\(\sigma_w(0)\). -/
private theorem cyclicCfg_last_eq {N L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨N - 1, by omega⟩ =
      σ_w ⟨0, by omega⟩ := by
  simp only [cyclicCfg]
  have hval : (N - 1 : ℕ) + N - (N - 1 : ℕ) = N := by omega
  have hoffset : ((N - 1) + N - (N - 1)) % N = 0 := by
    rw [hval]; exact Nat.mod_self N
  rw [dif_pos (show ((N - 1) + N - (N - 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp

/-- At the wrapping position \(N-1\), sites \(0,\ldots,L-2\) get
\(\sigma_w(1),\ldots,\sigma_w(L-1)\). -/
private theorem cyclicCfg_window_site {N L : ℕ} (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk : k < L - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      σ_w ⟨k + 1, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - 1)) % N = k + 1 := by
    have : k + N - (N - 1) = k + 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dif_pos (show (k + N - (N - 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp [hoffset]

/-- At the wrapping position \(N-1\), complement sites get \(\tau\) values. -/
private theorem cyclicCfg_complement_site {N L : ℕ} (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk1 : L - 1 ≤ k) (hk2 : k < N - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      τ ⟨k, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - 1)) % N = k + 1 := by
    have : k + N - (N - 1) = k + 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dif_neg (show ¬((k + N - (N - 1)) % N < L) by rw [hoffset]; omega)]

/-! ### Snoc factorization

Factor the full cyclic configuration product as \(A^{\mathrm{init}} A_{\sigma_w(0)}\),
then split \(\mathrm{init}\) into window-tail and complement parts. -/

/-- The word product along the cyclic configuration at position \(M\) on \(M+1\) sites
decomposes as \(A^{\mathrm{init}} A_{\sigma_w(0)}\), where \(\mathrm{init}\) covers
sites \(0,\ldots,M-1\). -/
theorem evalWord_cyclicCfg_snoc {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ)) =
    evalWord A (List.ofFn (fun k : Fin M =>
      cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ
        (Fin.castSucc k))) *
    A (σ_w ⟨0, by omega⟩) := by
  set cfg := cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ
  -- cfg = Fin.snoc init (σ_w 0)
  have hsnoc : cfg = Fin.snoc (fun k : Fin M => cfg (Fin.castSucc k))
      (σ_w ⟨0, by omega⟩) := by
    funext ⟨k, hk⟩
    by_cases hkM : k < M
    · have : (⟨k, hk⟩ : Fin (M + 1)) = Fin.castSucc ⟨k, hkM⟩ := by
        ext; simp [Fin.castSucc]
      rw [this, Fin.snoc_castSucc]
    · have : (⟨k, hk⟩ : Fin (M + 1)) = Fin.last M := by
        ext; simp [Fin.last]; omega
      rw [this, Fin.snoc_last]
      exact cyclicCfg_last_eq (by omega) hLN hL σ_w τ
  rw [show List.ofFn cfg = List.ofFn (Fin.snoc (fun k : Fin M => cfg (Fin.castSucc k))
      (σ_w ⟨0, by omega⟩)) from by rw [← hsnoc]]
  rw [evalWord_ofFn_snoc]

/-- The init part of the cyclic config at position M decomposes into
tail (window sites 1..L-1) and complement (sites L-1..M-1). -/
theorem init_evalWord_split {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    evalWord A (List.ofFn (fun k : Fin M =>
      cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ (Fin.castSucc k))) =
    evalWord A (List.ofFn (fun k : Fin (L - 1) => σ_w ⟨k.val + 1, by omega⟩)) *
    evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
      τ ⟨k.val + L - 1, by omega⟩)) := by
  rw [← evalWord_append]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append]; omega
  · intro k hk1 hk2
    simp only [List.length_ofFn] at hk1
    simp only [List.getElem_ofFn]
    by_cases hkL : k < L - 1
    · -- Window site: init(k) = σ_w(k+1)
      rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hkL),
          List.getElem_ofFn]
      exact cyclicCfg_window_site (by omega) (by omega) hL σ_w τ hkL
    · -- Complement site: init(k) = τ(k)
      rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega),
          List.getElem_ofFn]
      simp only [List.length_ofFn]
      have hcomp := cyclicCfg_complement_site (by omega : 2 ≤ M + 1) hLN hL σ_w τ
        (show L - 1 ≤ k from by omega) (show k < M from by omega)
      -- hcomp is about cyclicCfg at the original index; use Fin.castSucc ⟨k, _⟩.
      have : (Fin.castSucc (⟨k, by omega⟩ : Fin M) : Fin (M + 1)) =
          ⟨k, by omega⟩ := by ext; simp [Fin.castSucc]
      rw [this] at *
      -- The complement site: cyclicCfg returns τ(k)
      -- After unfolding, offset = k+1 ≥ L, so returns τ
      unfold cyclicCfg
      simp only []
      have hoffset : (k + (M + 1) - M) % (M + 1) = k + 1 := by
        have : k + (M + 1) - M = k + 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [dif_neg (by rw [hoffset]; omega)]
      congr 1; ext; simp; omega

/-! ### Factorization at the second boundary-crossing position

At the second boundary-crossing position \(N - L + 1\), the cyclic word starts
with the last window site, then runs through the complement, then finishes with
the remaining \(L - 1\) window sites.  This yields the factorization needed for
the second block-injective extraction. -/

/-- At the second boundary-crossing position \(N - L + 1\), site \(0\) carries
the final window entry \(\sigma_w(L-1)\). -/
private theorem cyclicCfg_mirror_zero_eq {N L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicCfg (by omega : 0 < N) L ⟨N - L + 1, by omega⟩ σ_w τ ⟨0, by omega⟩ =
      σ_w ⟨L - 1, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (0 + N - (N - L + 1)) % N = L - 1 := by
    have : 0 + N - (N - L + 1) = L - 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hoffset_lt : (0 + N - (N - L + 1)) % N < L := by
    rw [hoffset]
    omega
  rw [dif_pos hoffset_lt]
  apply congrArg σ_w
  ext
  exact hoffset

/-- At the second boundary-crossing position \(N - L + 1\), the complement sites
\(1,\ldots,N-L\) keep their \(\tau\) values. -/
private theorem cyclicCfg_mirror_complement_site {N L : ℕ}
    (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < N - L + 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - L + 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      τ ⟨k, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - L + 1)) % N = k + L - 1 := by
    have : k + N - (N - L + 1) = k + L - 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dif_neg (show ¬((k + N - (N - L + 1)) % N < L) by rw [hoffset]; omega)]

/-- At the second boundary-crossing position \(N - L + 1\), the final \(L - 1\)
physical sites carry the first \(L - 1\) entries of the window. -/
private theorem cyclicCfg_mirror_window_site {N L : ℕ}
    (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk : k < L - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - L + 1, by omega⟩ σ_w τ
        ⟨N - L + 1 + k, by omega⟩ =
      σ_w ⟨k, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (N - L + 1 + k + N - (N - L + 1)) % N = k := by
    have : N - L + 1 + k + N - (N - L + 1) = N + k := by omega
    rw [this, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [dif_pos (show (N - L + 1 + k + N - (N - L + 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp [hoffset]

/-- At the second boundary-crossing position \(N - L + 1\), the cyclic word factors as
the final window letter, then the complement word, then the remaining
\((L - 1)\)-site window head. -/
private theorem evalWord_cyclicCfg_cons {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) L
      ⟨M + 1 - L + 1, by omega⟩ σ_w τ)) =
    A (σ_w ⟨L - 1, by omega⟩) *
      evalWord A (List.ofFn (fun k : Fin (M + 1 - L) => τ ⟨k.val + 1, by omega⟩)) *
      evalWord A (List.ofFn (fun k : Fin (L - 1) =>
        σ_w ⟨k.val, Nat.lt_trans k.isLt (by omega)⟩)) := by
  let cfg : Fin (M + 1) → Fin d :=
    cyclicCfg (by omega : 0 < M + 1) L ⟨M + 1 - L + 1, by omega⟩ σ_w τ
  let comp : Fin (M + 1 - L) → Fin d := fun k => τ ⟨k.val + 1, by omega⟩
  let head : Fin (L - 1) → Fin d := fun k => σ_w ⟨k.val, Nat.lt_trans k.isLt (by omega)⟩
  let tail : Fin M → Fin d := fun k =>
    if h : k.val < M + 1 - L
    then comp ⟨k.val, h⟩
    else head ⟨k.val - (M + 1 - L), by omega⟩
  have hcons : cfg = Fin.cons (σ_w ⟨L - 1, by omega⟩) tail := by
    funext x
    refine Fin.cases ?_ ?_ x
    · simpa [cfg] using cyclicCfg_mirror_zero_eq (by omega : 2 ≤ M + 1) hLN hL σ_w τ
    · intro k
      rw [Fin.cons_succ]
      by_cases hkC : k.val < M + 1 - L
      · have hcomp := cyclicCfg_mirror_complement_site (by omega : 2 ≤ M + 1) hLN hL σ_w τ
          (show 1 ≤ k.val + 1 from by omega) (show k.val + 1 < M + 1 - L + 1 from by omega)
        have hsucc : (Fin.succ k : Fin (M + 1)) = ⟨k.val + 1, by omega⟩ := by
          ext
          simp [Fin.succ]
        simpa [cfg, tail, comp, hkC, hsucc] using hcomp
      · have hwin := cyclicCfg_mirror_window_site (by omega : 2 ≤ M + 1) hLN hL σ_w τ
          (k := k.val - (M + 1 - L)) (show k.val - (M + 1 - L) < L - 1 from by omega)
        have hsucc : (Fin.succ k : Fin (M + 1)) =
            ⟨M + 1 - L + 1 + (k.val - (M + 1 - L)), by omega⟩ := by
          ext
          simp [Fin.succ]
          omega
        simpa [cfg, tail, head, comp, hkC, hsucc] using hwin
  have htail : List.ofFn tail = List.ofFn comp ++ List.ofFn head := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append]
      omega
    · intro k hk1 hk2
      simp only [List.length_ofFn] at hk1
      simp only [List.getElem_ofFn]
      by_cases hkC : k < M + 1 - L
      · rw [List.getElem_append_left (by simpa using hkC)]
        rw [List.getElem_ofFn]
        simp [tail, comp, head, hkC]
      · rw [List.getElem_append_right (by simpa [List.length_ofFn] using hkC)]
        rw [List.getElem_ofFn]
        simp only [List.length_ofFn]
        simp [tail, comp, head, hkC]
  rw [show List.ofFn cfg = List.ofFn (Fin.cons (σ_w ⟨L - 1, by omega⟩) tail) by rw [hcons]]
  rw [evalWord_ofFn_cons, htail, evalWord_append]
  simp [comp, head, Matrix.mul_assoc]

/-! ### Trace rotation and matrix equation extraction

Use \(\operatorname{tr}(P \cdot Q) = \operatorname{tr}(Q \cdot P)\) to rotate
across the periodic boundary,
then extract a matrix equation via `groundSpaceMap_injective`. -/

private theorem wrapping_window_matEq {A : MPSTensor d D} [NeZero D]
    (hA : IsInjective A) {L : ℕ} (hL : 1 < L) {M : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin (M + 1) → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ τ σ_w, Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ)) :
    ∀ (σ_tail : Fin (L - 1) → Fin d) (τ : Fin (M + 1) → Fin d),
      X * evalWord A (List.ofFn σ_tail) *
        evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
          τ ⟨k.val + L - 1, by omega⟩)) =
      evalWord A (List.ofFn σ_tail) * Y τ := by
  -- Trace rotation FIRST (before mkσ to avoid whnf blowup)
  have hTraceRot : ∀ (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d),
      Matrix.trace (A (σ_w ⟨0, by omega⟩) * X *
        evalWord A (List.ofFn (fun k : Fin M =>
          cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ (Fin.castSucc k)))) =
      Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ) := by
    intro σ_w τ
    set P := evalWord A (List.ofFn (fun k : Fin M =>
      cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ (Fin.castSucc k)))
    set Aj := A (σ_w ⟨0, by omega⟩)
    calc Matrix.trace (Aj * X * P)
        = Matrix.trace (P * (Aj * X)) := Matrix.trace_mul_comm (Aj * X) P
      _ = Matrix.trace (P * Aj * X) := by rw [← Matrix.mul_assoc]
      _ = Matrix.trace (evalWord A (List.ofFn
            (cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ)) * X) := by
          rw [← evalWord_cyclicCfg_snoc hM (by omega) hL σ_w τ]
      _ = Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ) := hY τ σ_w
  -- Build σ_w from j and σ_tail
  let mkσ (j : Fin d) (σ_tail : Fin (L - 1) → Fin d) : Fin L → Fin d :=
    fun k => if h : k.val = 0 then j else σ_tail ⟨k.val - 1, by omega⟩
  -- Properties of mkσ
  have mkσ_zero : ∀ j σ_tail, mkσ j σ_tail ⟨0, by omega⟩ = j := by
    intro j σ_tail; simp [mkσ]
  have mkσ_tail_eq : ∀ j σ_tail,
      (fun k : Fin (L - 1) => (mkσ j σ_tail) ⟨k.val + 1, by omega⟩) = σ_tail := by
    intro j σ_tail; ext ⟨k, hk⟩
    simp [mkσ]
  have mkσ_evalWord : ∀ j σ_tail,
      evalWord A (List.ofFn (mkσ j σ_tail)) =
      A j * evalWord A (List.ofFn σ_tail) := by
    intro j σ_tail
    have hlist : List.ofFn (mkσ j σ_tail) = [j] ++ List.ofFn σ_tail := by
      apply List.ext_getElem
      · simp [List.length_ofFn]; omega
      · intro k hk1 hk2
        simp only [List.length_ofFn] at hk1
        simp only [List.getElem_ofFn]
        by_cases hk0 : k = 0
        · subst hk0; simp [mkσ]
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_cons, List.length_nil]
          rw [List.getElem_ofFn]
          simp [mkσ, show k ≠ 0 from hk0]
    rw [hlist, evalWord_append]; simp [evalWord_cons, evalWord_nil]
  -- Matrix equation via groundSpaceMap_injective on 1 site
  intro σ_tail τ
  apply groundSpaceMap_injective hA (show 0 < 1 from by omega)
  ext σ₁
  simp only [groundSpaceMap_apply]
  rw [show List.ofFn σ₁ = [σ₁ 0] from by
    apply List.ext_getElem <;> simp]
  simp only [evalWord_cons, evalWord_nil, mul_one]
  have key := hTraceRot (mkσ (σ₁ 0) σ_tail) τ
  rw [mkσ_zero] at key
  rw [init_evalWord_split hM (by omega) hL (mkσ (σ₁ 0) σ_tail) τ] at key
  rw [mkσ_tail_eq] at key
  rw [mkσ_evalWord] at key
  rw [Matrix.mul_assoc (A (σ₁ 0)) X, ← Matrix.mul_assoc X,
      Matrix.mul_assoc (A (σ₁ 0))] at key
  exact key

/-- Block injectivity strips the cyclic-window tail block at the boundary and
yields the one-sided compatibility \(C_τ A_j X = Y_τ A_j\). The
complementary second cyclic-window comparison is the remaining local step
needed for the two-sided relation. -/
theorem wrapping_window_compatibility_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin (M + 1) → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ τ σ_w, Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1) ⟨M, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ)) :
    ∀ (j : Fin d) (τ : Fin (M + 1) → Fin d),
      evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
        τ ⟨k.val + L₀, by omega⟩)) * A j * X =
      Y τ * A j := by
  have hM1 : 1 ≤ M := by omega
  have hL : 1 < L₀ + 1 := by omega
  intro j τ
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  ext σ_tail
  have key := hY τ (Fin.cons j σ_tail)
  rw [evalWord_cyclicCfg_snoc hM1 (by omega) hL (Fin.cons j σ_tail) τ] at key
  rw [init_evalWord_split hM1 (by omega) hL (Fin.cons j σ_tail) τ] at key
  rw [evalWord_ofFn_cons] at key
  simp only [fin_cons_mk_succ] at key
  have key' :
      Matrix.trace
          (evalWord A (List.ofFn σ_tail) *
            (evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
              τ ⟨k.val + L₀, by omega⟩)) *
              A j * X)) =
        Matrix.trace (A j * evalWord A (List.ofFn σ_tail) * Y τ) := by
    simpa [Matrix.mul_assoc] using key
  simp only [groundSpaceMap_apply] at *
  calc
    Matrix.trace
        (evalWord A (List.ofFn σ_tail) *
          (evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            τ ⟨k.val + L₀, by omega⟩)) *
            A j * X))
      = Matrix.trace (A j * evalWord A (List.ofFn σ_tail) * Y τ) := key'
    _ = Matrix.trace ((evalWord A (List.ofFn σ_tail) * Y τ) * A j) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_comm (A j) (evalWord A (List.ofFn σ_tail) * Y τ))
    _ = Matrix.trace
        (evalWord A (List.ofFn σ_tail) * (Y τ * A j)) := by
          simp [Matrix.mul_assoc]

/-- The second cyclic position used in the closure property exposes the
compatibility \(X A_j C_τ = A_j Y_τ\) after block-injective cancellation of the
trailing \(L₀\)-site block. -/
theorem wrapping_window_mirror_compatibility_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin (M + 1) → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ τ σ_w, Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1) ⟨M + 1 - L₀, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ)) :
    ∀ (j : Fin d) (τ : Fin (M + 1) → Fin d),
      X * A j * evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
        τ ⟨k.val + 1, by omega⟩)) =
      A j * Y τ := by
  intro j τ
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  ext σ_head
  simp only [groundSpaceMap_apply]
  have key := hY τ (Fin.snoc σ_head j)
  have hfactor := evalWord_cyclicCfg_cons (A := A) (show 1 ≤ M by omega) (by omega) (by omega)
    (Fin.snoc σ_head j) τ
  have hfactor' :
      evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1)
          ⟨M + 1 - L₀, by omega⟩ (Fin.snoc σ_head j) τ)) =
        A j *
          evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            τ ⟨k.val + 1, by omega⟩)) *
          evalWord A (List.ofFn σ_head) := by
    convert hfactor using 2
    · have hstart : (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) =
          ⟨M - L₀ + 1, by omega⟩ := by
            ext
            simp
            omega
      simpa using congrArg List.ofFn
        (congrArg
          (fun s => cyclicCfg (by omega : 0 < M + 1) (L₀ + 1) s (Fin.snoc σ_head j) τ)
          hstart)
    · congr 1
      change A j = A ((@Fin.snoc L₀ (fun _ => Fin d) σ_head j) (Fin.last L₀))
      rw [Fin.snoc_last]
    · congr 1
      apply List.ext_getElem
      · simp [List.length_ofFn]
      · intro k hk1 hk2
        simp only [List.length_ofFn] at hk1
        simp only [List.getElem_ofFn]
        have hcast : (⟨k, Nat.lt_trans hk1 (Nat.lt_succ_self L₀)⟩ : Fin (L₀ + 1)) =
            Fin.castSucc ⟨k, hk1⟩ := by
              ext
              simp [Fin.castSucc]
        rw [hcast, Fin.snoc_castSucc]
  rw [hfactor'] at key
  rw [evalWord_ofFn_snoc] at key
  have key' :
      Matrix.trace
          ((A j *
              evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                τ ⟨k.val + 1, by omega⟩)) *
              evalWord A (List.ofFn σ_head)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_head) * (A j * Y τ)) := by
    simpa [Fin.init, Fin.init_snoc, Matrix.mul_assoc] using key
  calc
    Matrix.trace
        (evalWord A (List.ofFn σ_head) *
          (X * A j * evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            τ ⟨k.val + 1, by omega⟩))))
      = Matrix.trace
          ((A j *
              evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                τ ⟨k.val + 1, by omega⟩)) *
              evalWord A (List.ofFn σ_head)) * X) := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle'
                (evalWord A (List.ofFn σ_head))
                X
                (A j * evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                  τ ⟨k.val + 1, by omega⟩))))
    _ = Matrix.trace (evalWord A (List.ofFn σ_head) * (A j * Y τ)) := by
          simpa [Matrix.mul_assoc] using key'

/-! ### Complement-word algebraic closure

The two one-sided cyclic-window identities close the boundary matrix once they
take the form
\[
  A^\mu A^j X = Y_\mu A^j,
  \qquad
  X A^j A^\mu = A^jY_\mu
\]
with the same word \(\mu\) on complementary sites and the same matrix
\(Y_\mu\). -/

/-- A boundary condition whose cyclic-window complement is the prescribed
word on the complementary sites.

For the boundary-crossing window beginning at the last site, the complement
occupies physical sites \(L₀, \ldots, N - 2\).  This construction fills exactly
those sites with \(\mu\); the remaining sites receive the letter \(\eta\) and do
not affect the complement word extracted by the last-site boundary-crossing
identity. -/
def wrappedMiddleBackground (L₀ N : ℕ) (η : Fin d)
    (μ : Fin (N - (L₀ + 1)) → Fin d) : Fin N → Fin d :=
  fun i =>
    if h : L₀ ≤ i.val ∧ i.val < N - 1 then
      μ ⟨i.val - L₀, by omega⟩
    else
      η

/-- A boundary condition whose second boundary-crossing window complement is the
prescribed word on the complementary sites.

For the second boundary-crossing window, the complement occupies physical sites
\(1, \ldots, N - L₀ - 1\).  This construction fills exactly those sites with
\(\mu\); all other sites receive the letter \(\eta\). -/
def mirrorMiddleBackground (L₀ N : ℕ) (η : Fin d)
    (μ : Fin (N - (L₀ + 1)) → Fin d) : Fin N → Fin d :=
  fun i =>
    if h : 1 ≤ i.val ∧ i.val < N - L₀ then
      μ ⟨i.val - 1, by omega⟩
    else
      η

/-- Extracting the wrapped complement from `wrappedMiddleBackground` returns the
prescribed word on the complementary sites. -/
theorem wrappedMiddleBackground_complement (L₀ N : ℕ) (η : Fin d)
    (μ : Fin (N - (L₀ + 1)) → Fin d) :
    (fun k : Fin (N - (L₀ + 1)) =>
      wrappedMiddleBackground L₀ N η μ ⟨k.val + L₀, by omega⟩) = μ := by
  ext k
  simp only [wrappedMiddleBackground]
  rw [dif_pos]
  · congr 1
    ext
    simp
  · constructor <;> omega

/-- Extracting the mirror complement from `mirrorMiddleBackground` returns the
prescribed word on the complementary sites. -/
theorem mirrorMiddleBackground_complement (L₀ N : ℕ) (η : Fin d)
    (μ : Fin (N - (L₀ + 1)) → Fin d) :
    (fun k : Fin (N - (L₀ + 1)) =>
      mirrorMiddleBackground L₀ N η μ ⟨k.val + 1, by omega⟩) = μ := by
  ext k
  simp only [mirrorMiddleBackground]
  rw [dif_pos]
  · congr 1
  · constructor <;> omega

/-- Reindexed cyclic-window identities give the two equations with one matrix
\(Y_\mu\).

The one-sided inputs have the form
\[
  A^\mu A^j X = Y^+_{\tau^+_\eta(\mu)}A^j,
  \qquad
  X A^j A^\mu = A^jY^-_{\tau^-_\eta(\mu)}.
\]
The boundary-crossing comparison
\[
  Y^+_{\tau^+_\eta(\mu)} = Y^-_{\tau^-_\eta(\mu)}
\]
therefore gives the two identities with the same matrix \(Y_\mu\). -/
theorem two_sided_middle_compatibility_of_wrapped_witness_comparison
    {A : MPSTensor d D} {L₀ N : ℕ} (η : Fin d)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Ywrap Ymirror : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hWrap : ∀ (j : Fin d) (τ : Fin N → Fin d),
      evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
        τ ⟨k.val + L₀, by omega⟩)) * A j * X = Ywrap τ * A j)
    (hMirror : ∀ (j : Fin d) (τ : Fin N → Fin d),
      X * A j * evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
        τ ⟨k.val + 1, by omega⟩)) = A j * Ymirror τ)
    (hCompare : ∀ μ : Fin (N - (L₀ + 1)) → Fin d,
      Ywrap (wrappedMiddleBackground L₀ N η μ) =
        Ymirror (mirrorMiddleBackground L₀ N η μ)) :
    ∃ Y : (Fin (N - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      (∀ (j : Fin d) (μ : Fin (N - (L₀ + 1)) → Fin d),
        evalWord A (List.ofFn μ) * A j * X = Y μ * A j) ∧
      (∀ (j : Fin d) (μ : Fin (N - (L₀ + 1)) → Fin d),
        X * A j * evalWord A (List.ofFn μ) = A j * Y μ) := by
  refine ⟨fun μ => Ywrap (wrappedMiddleBackground L₀ N η μ), ?_, ?_⟩
  · intro j μ
    have h := hWrap j (wrappedMiddleBackground L₀ N η μ)
    simpa [wrappedMiddleBackground_complement] using h
  · intro j μ
    have h := hMirror j (mirrorMiddleBackground L₀ N η μ)
    have hCmp := hCompare μ
    simpa [mirrorMiddleBackground_complement, hCmp.symm] using h

/-- Two one-sided identities with the same matrix \(Y_\mu\) force \(X\) to commute
with every word obtained by adjoining one physical letter on each side.

This is the algebraic core of the remaining normal parent-Hamiltonian closure
property: after the two cyclic windows have been compared so that their matrices
agree on a shared complement \(\mu\), the identities \(A^μ A^b X = Y_μ A^b\) and
\(X A^a A^μ = A^a Y_μ\) imply
\(X A^a A^μ A^b = A^a A^μ A^b X\). -/
theorem commutes_words_of_two_sided_middle_compatibility
    {A : MPSTensor d D} {m : ℕ} {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin m → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hLeft : ∀ (j : Fin d) (μ : Fin m → Fin d),
      evalWord A (List.ofFn μ) * A j * X = Y μ * A j)
    (hRight : ∀ (j : Fin d) (μ : Fin m → Fin d),
      X * A j * evalWord A (List.ofFn μ) = A j * Y μ) :
    ∀ ω : Fin (m + 2) → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X := by
  intro ω
  let a : Fin d := ω ⟨0, by omega⟩
  let tail : Fin (m + 1) → Fin d := Fin.tail ω
  let μ : Fin m → Fin d := Fin.init tail
  let b : Fin d := tail (Fin.last m)
  have htail : Fin.tail ω = Fin.snoc μ b := by
    dsimp only [tail, μ, b]
    exact (Fin.snoc_init_self (Fin.tail ω)).symm
  have hω : ω = Fin.cons a (Fin.snoc μ b) := by
    rw [← Fin.cons_self_tail ω, htail]
    simp [a]
  rw [hω, evalWord_ofFn_cons, evalWord_ofFn_snoc]
  calc
    X * (A a * (evalWord A (List.ofFn μ) * A b))
        = (X * A a * evalWord A (List.ofFn μ)) * A b := by
            simp [Matrix.mul_assoc]
    _ = (A a * Y μ) * A b := by rw [hRight a μ]
    _ = A a * (Y μ * A b) := by simp [Matrix.mul_assoc]
    _ = A a * (evalWord A (List.ofFn μ) * A b * X) := by rw [← hLeft b μ]
    _ = (A a * (evalWord A (List.ofFn μ) * A b)) * X := by
            simp [Matrix.mul_assoc]

/-- If \(X\) commutes with all words of a fixed length \(m\), then it commutes
with all words whose length is any multiple of \(m\).

The proof chunks a list of length \(q * m\) into a length-\(m\) prefix and a shorter
multiple-length suffix. This formalizes the amplification step that promotes
fixed-length commutation to the long-word commutation hypothesis required by
the block-injective boundary-contraction theorem. -/
theorem commutes_words_mul_of_commutes_words {A : MPSTensor d D}
    {m q : ℕ} {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X) :
    ∀ ω : Fin (q * m) → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X := by
  suffices hList : ∀ q : ℕ, ∀ w : List (Fin d), w.length = q * m →
      X * evalWord A w = evalWord A w * X by
    intro ω
    exact hList q (List.ofFn ω) (by simp)
  intro q
  induction q with
  | zero =>
      intro w hw
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
      simp [hw0]
  | succ q ih =>
      intro w hw
      have htake_len : (w.take m).length = m := by
        have hm_le : m ≤ w.length := by
          rw [hw, Nat.succ_mul]
          omega
        rw [List.length_take, Nat.min_eq_left hm_le]
      let μ : Fin m → Fin d := fun i => (w.take m).get ⟨i.val, by simp [htake_len]⟩
      have hμ : List.ofFn μ = w.take m := by
        simpa [μ, htake_len] using (List.ofFn_get (w.take m))
      have hdrop_len : (w.drop m).length = q * m := by
        rw [List.length_drop, hw, Nat.succ_mul]
        omega
      have hdrop_comm := ih (w.drop m) hdrop_len
      calc
        X * evalWord A w
            = X * evalWord A (w.take m ++ w.drop m) := by
                rw [List.take_append_drop m w]
        _ = X * (evalWord A (w.take m) * evalWord A (w.drop m)) := by
                rw [evalWord_append]
        _ = (X * evalWord A (w.take m)) * evalWord A (w.drop m) := by
                rw [Matrix.mul_assoc]
        _ = (evalWord A (w.take m) * X) * evalWord A (w.drop m) := by
                rw [← hμ, hComm μ]
        _ = evalWord A (w.take m) * (X * evalWord A (w.drop m)) := by
                simp [Matrix.mul_assoc]
        _ = evalWord A (w.take m) * (evalWord A (w.drop m) * X) := by
                rw [hdrop_comm]
        _ = (evalWord A (w.take m) * evalWord A (w.drop m)) * X := by
                simp [Matrix.mul_assoc]
        _ = evalWord A (w.take m ++ w.drop m) * X := by
                rw [evalWord_append]
        _ = evalWord A w * X := by
                rw [List.take_append_drop m w]

/-! ### Main commutation result

Extend from the boundary-crossing equation to full commutation via spanning. -/

/-- If a boundary matrix commutes with all words of some length \(m ≥ L₀\), then
block injectivity forces it to commute with every generator. -/
theorem boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes
    {A : MPSTensor d D} {L₀ m : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hm : L₀ ≤ m) {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X) :
    ∀ j : Fin d, X * A j = A j * X := by
  intro j
  exact commutes_all_of_commutes_long_words_of_isNBlkInjective
    (A := A) hInj hL₀ hm hComm (A j)

/-- If left multiplication by \(Z\) annihilates every word product of length \(k\),
and words of some longer length \(n\) span the full matrix algebra, then \(Z = 0\).

This is the padding form needed in the normal periodic-boundary argument: a
zero-product relation obtained for a short complement word can be multiplied by
all padding words up to any length whose exact word span is \(\top\). -/
theorem eq_zero_of_mul_evalWord_eq_zero_of_wordSpan_eq_top
    {A : MPSTensor d D} {k n : ℕ} {Z : Matrix (Fin D) (Fin D) ℂ}
    (htop : wordSpan A n = ⊤) (hkn : k ≤ n)
    (hzero : ∀ σ : Fin k → Fin d, Z * evalWord A (List.ofFn σ) = 0) :
    Z = 0 := by
  have hzero_span : ∀ M ∈ wordSpan A n, Z * M = 0 := by
    apply Submodule.span_induction
    · intro M hM
      rcases hM with ⟨σ, rfl⟩
      let w := List.ofFn σ
      have htake_len : (w.take k).length = k := by
        rw [List.length_take]
        have hwlen : w.length = n := by simp [w]
        omega
      let σk : Fin k → Fin d := fun i =>
        (w.take k).get ⟨i.val, by simp [htake_len]⟩
      have hσk : List.ofFn σk = w.take k := by
        simpa [σk, htake_len] using (List.ofFn_get (w.take k))
      have hprefix : Z * evalWord A (w.take k) = 0 := by
        simpa [hσk] using hzero σk
      calc
        Z * evalWord A w = Z * evalWord A (w.take k ++ w.drop k) := by
          rw [List.take_append_drop k w]
        _ = Z * (evalWord A (w.take k) * evalWord A (w.drop k)) := by
          rw [evalWord_append]
        _ = (Z * evalWord A (w.take k)) * evalWord A (w.drop k) := by
          rw [Matrix.mul_assoc]
        _ = 0 := by rw [hprefix, zero_mul]
    · simp
    · intro M₁ M₂ _ _ h₁ h₂
      simp [Matrix.mul_add, h₁, h₂]
    · intro c M _ hM
      simp [hM]
  have h1 : Z * (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
    hzero_span 1 (htop ▸ Submodule.mem_top)
  simpa using h1

/-- Block-injective padding variant of
`eq_zero_of_mul_evalWord_eq_zero_of_wordSpan_eq_top`.

If \(A\) is \(L₀\)-block-injective, then every positive multiple of \(L₀\) has full
word span. Hence a zero-product relation at length \(k\) already forces \(Z = 0\)
as soon as \(k\) is bounded by such a multiple. -/
theorem eq_zero_of_mul_evalWord_eq_zero_of_isNBlkInjective_of_le_mul
    {A : MPSTensor d D} {L₀ k q : ℕ} (hInj : IsNBlkInjective A L₀)
    (hq : 1 ≤ q) (hkq : k ≤ q * L₀) {Z : Matrix (Fin D) (Fin D) ℂ}
    (hzero : ∀ σ : Fin k → Fin d, Z * evalWord A (List.ofFn σ) = 0) :
    Z = 0 := by
  exact eq_zero_of_mul_evalWord_eq_zero_of_wordSpan_eq_top
    (A := A) (k := k) (n := q * L₀)
    (wordSpan_top_of_mul A ((wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj) q hq)
    hkq hzero

/-- A right boundary witness is unique once its products with all one-site
tensors are fixed.

This is the one-sided uniqueness consequence of block injectivity used in the
periodic-boundary comparison: a positive block-injective word span turns
equality after multiplying by each one-site tensor into equality of the
boundary matrices. -/
theorem right_witness_unique_of_isNBlkInjective
    {A : MPSTensor d D} {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Y₁ Y₂ : Matrix (Fin D) (Fin D) ℂ}
    (hY : ∀ j : Fin d, Y₁ * A j = Y₂ * A j) :
    Y₁ = Y₂ := by
  have hzero : ∀ σ : Fin 1 → Fin d, (Y₁ - Y₂) * evalWord A (List.ofFn σ) = 0 := by
    intro σ
    have heval : evalWord A (List.ofFn σ) = A (σ 0) := by
      simp [evalWord]
    rw [heval, sub_mul, hY (σ 0), sub_self]
  have hsub : Y₁ - Y₂ = 0 :=
    eq_zero_of_mul_evalWord_eq_zero_of_isNBlkInjective_of_le_mul
      (A := A) (L₀ := L₀) (k := 1) (q := 1) hInj (by omega) (by omega) hzero
  exact sub_eq_zero.mp hsub

/-- A left boundary witness is unique once all one-site tensors have the same
products with it. -/
theorem left_witness_unique_of_isNBlkInjective
    {A : MPSTensor d D} {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Y₁ Y₂ : Matrix (Fin D) (Fin D) ℂ}
    (hY : ∀ j : Fin d, A j * Y₁ = A j * Y₂) :
    Y₁ = Y₂ := by
  have hlist : ∀ w : List (Fin d), w ≠ [] →
      evalWord A w * Y₁ = evalWord A w * Y₂ := by
    intro w hw
    induction w with
    | nil => cases hw rfl
    | cons j rest ih =>
        cases rest with
        | nil =>
            simpa [evalWord] using hY j
        | cons k rest =>
            have htail : evalWord A (k :: rest) * Y₁ = evalWord A (k :: rest) * Y₂ :=
              ih (by simp)
            calc
              evalWord A (j :: k :: rest) * Y₁
                  = A j * (evalWord A (k :: rest) * Y₁) := by
                      simp [evalWord, Matrix.mul_assoc]
              _ = A j * (evalWord A (k :: rest) * Y₂) := by rw [htail]
              _ = evalWord A (j :: k :: rest) * Y₂ := by
                      simp [evalWord, Matrix.mul_assoc]
  have hword : ∀ σ : Fin L₀ → Fin d,
      evalWord A (List.ofFn σ) * Y₁ = evalWord A (List.ofFn σ) * Y₂ := by
    intro σ
    apply hlist
    intro hnil
    have hlen : L₀ = 0 := by
      simpa [List.length_ofFn] using congrArg List.length hnil
    omega
  have hmul : LinearMap.mulRight ℂ Y₁ = LinearMap.mulRight ℂ Y₂ := by
    apply LinearMap.ext_on_range
      (v := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
    · simpa [wordSpan] using (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
    · intro σ
      simpa [LinearMap.mulRight_apply] using hword σ
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) * Y₁ =
      (1 : Matrix (Fin D) (Fin D) ℂ) * Y₂ := by
    simpa [LinearMap.mulRight_apply] using
      congrArg (fun f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ =>
        f (1 : Matrix (Fin D) (Fin D) ℂ)) hmul
  simpa using h1

/-- If `groundSpaceMap A N X` lies in every cyclic window's ground space,
then \(X\) commutes with all generators \(A_j\).

The boundary-crossing local condition forces the boundary matrix into the center
of the algebra generated by \(\{A_j\}\), giving the periodic-chain uniqueness
step. -/
theorem boundary_matrix_commutes {A : MPSTensor d D} [NeZero D]
    (hA : IsInjective A) {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ∀ (i : Fin N) (τ : Fin N → Fin d),
      cyclicRestrictₗ (by omega : 0 < N) L i τ (groundSpaceMap A N X) ∈
        groundSpace A L) :
    ∀ j : Fin d, X * A j = A j * X := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : 1 ≤ M := by omega
  have hN0 : 0 < M + 1 := by omega
  -- Extract Y_τ from boundary-crossing ground-space membership.
  have hGS : ∀ τ : Fin (M + 1) → Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ σ_w : Fin L → Fin d,
        Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg hN0 L ⟨M, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y) := by
    intro τ
    have hmem := hψ ⟨M, by omega⟩ τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    refine ⟨Y, fun σ_w => ?_⟩
    have : cyclicRestrictₗ hN0 L ⟨M, by omega⟩ τ (groundSpaceMap A (M + 1) X) σ_w =
        groundSpaceMap A L Y σ_w := by rw [← hY]
    simp only [cyclicRestrictₗ_apply, groundSpaceMap_apply] at this
    exact this
  choose Y hY using hGS
  -- Matrix equation from wrapping_window_matEq
  have hMatEq := wrapping_window_matEq hA hL hM (by omega) Y (fun τ σ_w => hY τ σ_w)
  -- Extend to all M₁ via spanning in σ_tail (wordSpan(L-1) = ⊤)
  have hMatEq2 : ∀ (M₁ : Matrix (Fin D) (Fin D) ℂ) (τ : Fin (M + 1) → Fin d),
      X * M₁ * evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
        τ ⟨k.val + L - 1, by omega⟩)) = M₁ * Y τ := by
    intro M₁ τ
    have hfg : (LinearMap.mulLeft ℂ X).comp
        (LinearMap.mulRight ℂ (evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
          τ ⟨k.val + L - 1, by omega⟩)))) =
        LinearMap.mulRight ℂ (Y τ) := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin (L - 1) → Fin d => evalWord A (List.ofFn σ))
      · simpa [wordSpan] using wordSpan_eq_top_of_isInjective hA (by omega : 0 < L - 1)
      · intro σ_tail
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
                    LinearMap.mulRight_apply]
        rw [← Matrix.mul_assoc]; exact hMatEq σ_tail τ
    have := congrArg (· M₁) hfg
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
               LinearMap.mulRight_apply] at this
    rw [← Matrix.mul_assoc] at this; exact this
  -- Y τ = X * compProd(τ) (take M₁ = 1)
  have hYeq : ∀ τ : Fin (M + 1) → Fin d,
      Y τ = X * evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
        τ ⟨k.val + L - 1, by omega⟩)) := by
    intro τ; have := hMatEq2 1 τ; rw [mul_one, one_mul] at this; exact this.symm
  -- (X * M₁ - M₁ * X) * compProd(τ) = 0 for all M₁, τ
  have hCommComp : ∀ (M₁ : Matrix (Fin D) (Fin D) ℂ) (τ : Fin (M + 1) → Fin d),
      (X * M₁ - M₁ * X) * evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
        τ ⟨k.val + L - 1, by omega⟩)) = 0 := by
    intro M₁ τ
    have h1 := hMatEq2 M₁ τ
    rw [hYeq τ, ← Matrix.mul_assoc] at h1
    rw [sub_mul, sub_eq_zero]; exact h1
  -- Conclude: X * M₁ = M₁ * X
  haveI : NeZero d := neZero_d_of_isInjective hA
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hComm : ∀ M₁ : Matrix (Fin D) (Fin D) ℂ, X * M₁ = M₁ * X := by
    intro M₁
    by_cases hML : M + 1 = L
    · have h0 : M + 1 - L = 0 := by omega
      have := hCommComp M₁ (fun _ => ⟨0, hd⟩)
      simp only [h0, List.ofFn_zero, evalWord_nil, mul_one] at this
      exact sub_eq_zero.mp this
    · have hML' : 0 < M + 1 - L := by omega
      have hφ : LinearMap.mulLeft ℂ (X * M₁ - M₁ * X) = 0 := by
        apply LinearMap.ext_on_range
          (v := fun f : Fin (M + 1 - L) → Fin d => evalWord A (List.ofFn f))
        · simpa [wordSpan] using wordSpan_eq_top_of_isInjective hA hML'
        · intro f
          simp only [LinearMap.mulLeft_apply, LinearMap.zero_apply]
          let τ₀ : Fin (M + 1) → Fin d := fun k =>
            if h : L - 1 ≤ k.val ∧ k.val < M
            then f ⟨k.val - (L - 1), by omega⟩
            else ⟨0, hd⟩
          have hτ₀ : (fun k : Fin (M + 1 - L) => τ₀ ⟨k.val + L - 1, by omega⟩) = f := by
            ext ⟨k, hk⟩; simp only [τ₀]
            rw [dif_pos ⟨by omega, by omega⟩]
            congr 2; ext1; dsimp only; omega
          rw [← hτ₀]; exact hCommComp M₁ τ₀
      have := congrArg (· 1) hφ
      simp only [LinearMap.mulLeft_apply, mul_one, LinearMap.zero_apply] at this
      exact sub_eq_zero.mp this
  intro j; exact hComm (A j)

end MPSTensor
