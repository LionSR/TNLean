/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.VaryingOBCIntersection
import QICLean.Kraus.RectangularChain
import Mathlib.Data.List.OfFn

/-!
# Reconstruction along a varying-bond open chain

Adjacent-pair coefficient sections determine a single boundary matrix for the whole
chain. The induction enlarges an actual prefix, using its derived row-isometry and
C1 at the next site. Each enlargement is the canonical adjoint construction in the
source's three-site argument. Physical words outside a section are lists, so no
identification of different virtual bond spaces is needed.

The conclusion is a representation-intersection theorem. Passage from the kernel of
an actual varying-bond parent Hamiltonian to the adjacent-pair sections is a separate
step; it is not assumed as a completed parent-Hamiltonian uniqueness theorem here.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 proof,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 1212–1237.
-/

open scoped Matrix BigOperators

namespace Matrix

variable {d : ℕ}

/-- Appending one physical letter appends its actual rectangular site matrix.
Source: PGVWC07, Theorem 9 proof, lines 1233–1237. -/
theorem obc_rectangularEval_snoc (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {n : ℕ} (w : Fin n → Fin d) (i : Fin d) :
    Kraus.rectangularEval b (fun k : Fin (n + 1) ↦ A k.val) (Fin.snoc w i) =
      Kraus.rectangularEval b (fun k : Fin n ↦ A k.val) w * A n i := by
  induction n generalizing b with
  | zero => simp [Kraus.rectangularEval]
  | succ n ih =>
    have hw : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
    rw [hw, ← Fin.cons_snoc_eq_snoc_cons]
    simp only [Kraus.rectangularEval, Fin.cons_succ]
    rw [ih (fun k ↦ b (k + 1)) (fun k ↦ A (k + 1))]
    exact (Matrix.mul_assoc _ _ _).symm

/-- Every actual prefix of a row-isometric varying-bond chain is row-isometric.
The identity is proved on the true endpoint spaces, without square padding.
Source: PGVWC07, Theorem 9 proof, lines 1224–1237. -/
theorem obc_rectangularEval_row_isometry (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (n : ℕ)
    (hA : ∀ k < n, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (b k)) _ ℂ)) :
    ∑ w : Fin n → Fin d,
      Kraus.rectangularEval b (fun k : Fin n ↦ A k.val) w *
        (Kraus.rectangularEval b (fun k : Fin n ↦ A k.val) w)ᴴ =
      (1 : Matrix (Fin (b 0)) _ ℂ) := by
  induction n generalizing b with
  | zero => simp [Kraus.rectangularEval]
  | succ n ih =>
    have htail := ih (fun k ↦ b (k + 1)) (fun k ↦ A (k + 1))
      (fun k hk ↦ hA (k + 1) (by omega))
    have hprod := obc_block_row_isometry (A 0)
      (fun w : Fin n → Fin d ↦
        Kraus.rectangularEval (fun k ↦ b (k + 1))
          (fun k : Fin n ↦ A (k.val + 1)) w)
      (hA 0 (by omega)) htail
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Fin d)).sum_comp]
    refine Eq.trans (Finset.sum_congr rfl fun x _ ↦ ?_) hprod
    simp only [Fin.consEquiv_apply, Kraus.rectangularEval, Fin.cons_succ]
    rfl

private theorem ofFn_snoc_eq {α : Type*} {n : ℕ} (w : Fin n → α) (i : α) :
    List.ofFn (Fin.snoc w i) = List.ofFn w ++ [i] := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

/-- The source's overlap argument reconstructs one boundary matrix on the full chain
from the actual adjacent-pair sections. Only sitewise C1 and canonical row-isometry
are assumed. The physical length is at least two, so an adjacent interaction exists.
Source: PGVWC07, Theorem 9 proof, equation unique-OBC and the final induction,
lines 1212–1237. -/
theorem obc_trace_reconstruction_of_adjacent_pair_sections (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (hA : ∀ k < N, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (b k)) _ ℂ))
    (hC1 : ∀ k < N, Submodule.span ℂ (Set.range (A k)) = ⊤)
    (ψ : List (Fin d) → ℂ)
    (hpair : ∀ (u v : List (Fin d)), u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (b (u.length + 2))) (Fin (b u.length)) ℂ,
        ∀ i j, ψ (u ++ i :: j :: v) = Matrix.trace (X * A u.length i * A (u.length + 1) j)) :
    ∃ X : Matrix (Fin (b N)) (Fin (b 0)) ℂ,
      ∀ w : Fin N → Fin d,
        ψ (List.ofFn w) =
          Matrix.trace (X * Kraus.rectangularEval b (fun k : Fin N ↦ A k.val) w) := by
  classical
  have hprefix : ∀ r : ℕ, r + 2 ≤ N → ∀ v : List (Fin d), r + 2 + v.length = N →
      ∃ X : Matrix (Fin (b (r + 2))) (Fin (b 0)) ℂ,
        ∀ w : Fin (r + 2) → Fin d,
          ψ (List.ofFn w ++ v) = Matrix.trace
            (X * Kraus.rectangularEval b (fun k : Fin (r + 2) ↦ A k.val) w) := by
    intro r
    induction r with
    | zero =>
      intro _ v hv
      obtain ⟨X, hX⟩ := hpair [] v (by simpa using hv)
      refine ⟨X, fun w ↦ ?_⟩
      simpa [List.ofFn_succ, Kraus.rectangularEval, Matrix.mul_assoc] using hX (w 0) (w 1)
    | succ r ih =>
      intro hr v hv
      let P : (Fin (r + 1) → Fin d) → Matrix (Fin (b 0)) (Fin (b (r + 1))) ℂ :=
        fun u ↦ Kraus.rectangularEval b (fun k : Fin (r + 1) ↦ A k.val) u
      let φ : (Fin (r + 1) → Fin d) → Fin d → Fin d → ℂ :=
        fun u i j ↦ ψ (List.ofFn u ++ i :: j :: v)
      have hP : ∑ u, P u * (P u)ᴴ = (1 : Matrix (Fin (b 0)) _ ℂ) :=
        obc_rectangularEval_row_isometry b A (r + 1) (fun k hk ↦ hA k (by omega))
      have hLeft (j : Fin d) : ∃ X : Matrix (Fin (b (r + 2))) (Fin (b 0)) ℂ,
          ∀ u i, φ u i j = Matrix.trace (X * P u * A (r + 1) i) := by
        obtain ⟨X, hX⟩ := ih (by omega) (j :: v) (by simp only [List.length_cons]; omega)
        refine ⟨X, fun u i ↦ ?_⟩
        have hx := hX (Fin.snoc u i)
        rw [ofFn_snoc_eq, obc_rectangularEval_snoc] at hx
        simpa only [φ, P, List.append_assoc, List.singleton_append, Matrix.mul_assoc] using hx
      have hRight (u : Fin (r + 1) → Fin d) :
          ∃ Y : Matrix (Fin (b (r + 3))) (Fin (b (r + 1))) ℂ,
            ∀ i j, φ u i j = Matrix.trace (Y * A (r + 1) i * A (r + 2) j) := by
        have key : ∀ m : ℕ, m = (List.ofFn u).length →
            ∃ Y : Matrix (Fin (b (m + 2))) (Fin (b m)) ℂ,
              ∀ i j, ψ (List.ofFn u ++ i :: j :: v) =
                Matrix.trace (Y * A m i * A (m + 1) j) := by
          intro m hm
          subst hm
          exact hpair (List.ofFn u) v (by simp only [List.length_ofFn]; omega)
        obtain ⟨Y, hY⟩ := key (r + 1) (by simp)
        exact ⟨Y, fun i j ↦ hY i j⟩
      obtain ⟨Z, hZ⟩ := obc_three_site_reconstruction_of_pair_sections P
        (A (r + 1)) (A (r + 2)) hP (hC1 (r + 1) (by omega)) φ hLeft hRight
      refine ⟨Z, fun w ↦ ?_⟩
      have hz := hZ (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last (r + 1)))
        (w (Fin.last (r + 2)))
      have hw : Fin.snoc
          (Fin.snoc (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last (r + 1))))
          (w (Fin.last (r + 2))) = w := by
        rw [Fin.snoc_init_self, Fin.snoc_init_self]
      have heval := congrArg
        (fun s ↦ Kraus.rectangularEval b (fun k : Fin (r + 3) ↦ A k.val) s) hw
      rw [obc_rectangularEval_snoc, obc_rectangularEval_snoc] at heval
      have hlist := congrArg List.ofFn hw
      rw [ofFn_snoc_eq, ofFn_snoc_eq] at hlist
      rw [← heval, ← hlist]
      simpa only [φ, P, List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append, Matrix.mul_assoc] using hz
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  simpa only [List.append_nil] using hprefix m (by omega) [] (by simp)

/-- Singleton endpoint bonds turn the reconstructed boundary into a scalar, so
every coefficient family satisfying adjacent-pair conditions lies in the represented state line.
This is the final scalar-boundary step, rather than an assertion that normalized
vectors have the same global phase.
Source: PGVWC07, Theorem 9 proof, lines 1233–1237. -/
theorem obc_scalar_reconstruction_of_adjacent_pair_sections (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (hleft : b 0 = 1) (hright : b N = 1)
    (hA : ∀ k < N, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (b k)) _ ℂ))
    (hC1 : ∀ k < N, Submodule.span ℂ (Set.range (A k)) = ⊤)
    (ψ : List (Fin d) → ℂ)
    (hpair : ∀ (u v : List (Fin d)), u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (b (u.length + 2))) (Fin (b u.length)) ℂ,
        ∀ i j, ψ (u ++ i :: j :: v) = Matrix.trace (X * A u.length i * A (u.length + 1) j)) :
    ∃ c : ℂ, ∀ w : Fin N → Fin d,
      ψ (List.ofFn w) = c *
        Kraus.rectangularEval b (fun k : Fin N ↦ A k.val) w
          (Fin.cast hleft.symm 0) (Fin.cast hright.symm 0) := by
  classical
  let _ : Unique (Fin (b 0)) := Equiv.unique (finCongr hleft)
  let _ : Unique (Fin (b N)) := Equiv.unique (finCongr hright)
  obtain ⟨X, hX⟩ := obc_trace_reconstruction_of_adjacent_pair_sections b A hN hA hC1 ψ hpair
  let l : Fin (b 0) := Fin.cast hleft.symm 0
  let r : Fin (b N) := Fin.cast hright.symm 0
  refine ⟨X r l, fun w ↦ ?_⟩
  have htrace (P : Matrix (Fin (b 0)) (Fin (b N)) ℂ) :
      Matrix.trace (X * P) = X r l * P l r := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_unique]
    rw [show (default : Fin (b 0)) = l from Subsingleton.elim _ _,
      show (default : Fin (b N)) = r from Subsingleton.elim _ _]
  exact (hX w).trans (htrace _)

end Matrix
