/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisSimpleSpectrum

/-!
# A basis of a degenerate ground space by iterated compressions

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1695–1705, chooses a basis of a ground space of
dimension `n > 2` by iteration: diagonalize the compression `P M_j P`, then, among eigenvectors
sharing an eigenvalue, diagonalize a further compression `P M_k P` with two different eigenvalues,
and proceed until every off-diagonal matrix element is bounded.

Here the basis is an orthonormal family `v : Fin n → E` and the iteration is recorded by real
labels `r ℓ a` at levels `ℓ = 0, 1, …`: the class of `a` at level `ℓ` is the set of `c` whose
labels agree with those of `a` at every level below `ℓ`, and the operator `A ℓ` of level `ℓ` acts
diagonally on each class, with eigenvalue `r ℓ c` at `v c`. For two basis vectors `a`, `b` in one
class with different labels at that level, expanding both products in the basis gives
`(r_a - r_b) ⟨v_a, B v_b⟩ = ⟨v_a, [A, B] v_b⟩ - ∑_{c ∉ class} (⟨v_a, A v_c⟩ ⟨v_c, B v_b⟩ -
⟨v_a, B v_c⟩ ⟨v_c, A v_b⟩)`. The terms with `c` outside the class are products of matrix
elements between vectors separated at an earlier level, which the earlier levels bound. The
smallest difference `levelGap` between distinct labels in one class is positive, so every
matrix element is bounded at the first level separating its two vectors. By induction on the
level, with all commutators of the compressions at most `K` and those with `B` at most `K_B`, the
elements of `B` are bounded at every level by `levelBoundB`, which is linear in `K_B`; when the
iteration separates every pair after `L` levels, as the source's iteration ends once every
off-diagonal element is bounded, this bounds the off-diagonal part of `B`. With two levels, the
bound is written out (`norm_inner_le_of_two_levels`).

## Main statements

* `inner_commutator_apply_eq_sum`: the matrix elements of a commutator in a basis preserved by
  both operators.
* `abs_sub_mul_norm_inner_le`: one level of the iteration.
* `labelClass`, `levelGap`, `levelGap_pos`: the classes of the iteration and the smallest
  difference of distinct labels in a class.
* `norm_inner_le_of_mem_labelClass`: the bound at the first level separating two basis vectors.
* `levelBoundA`, `levelBoundB`, `norm_inner_A_le_levelBoundA`, `norm_inner_le_levelBoundB`,
  `norm_offDiagonalPartFamily_le_levelBoundB`: every level, by induction.
* `norm_inner_le_of_two_levels`, `norm_offDiagonalPartFamily_le_of_two_levels`: two levels, with
  the bound written out.

**Local fix (cross terms of the iteration):** the source states that the further compressions
bound the remaining off-diagonal elements. Since the compression `P_C M_k P_C` to a class `C`
differs from `M_k`, its commutator with `P_C B P_C` differs from `[M_k, B]` by the terms through
vectors outside `C`. These are kept explicitly, as products of matrix elements already bounded at
earlier levels. Documented in `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- **Matrix elements of a commutator.** If `A` and `B` map each `v_b` into the span of the
family `v`, then
`⟨v_a, [A, B] v_b⟩ = ∑_c (⟨v_a, A v_c⟩ ⟨v_c, B v_b⟩ - ⟨v_a, B v_c⟩ ⟨v_c, A v_b⟩)`. -/
theorem inner_commutator_apply_eq_sum {v : Fin n → E} (A B : E →L[𝕜] E)
    (hA : ∀ b, A (v b) = ∑ c, ⟪v c, A (v b)⟫_𝕜 • v c)
    (hB : ∀ b, B (v b) = ∑ c, ⟪v c, B (v b)⟫_𝕜 • v c) (a b : Fin n) :
    ⟪v a, (A * B - B * A) (v b)⟫_𝕜 =
      ∑ c, (⟪v a, A (v c)⟫_𝕜 * ⟪v c, B (v b)⟫_𝕜 - ⟪v a, B (v c)⟫_𝕜 * ⟪v c, A (v b)⟫_𝕜) := by
  have h1 : ⟪v a, A (B (v b))⟫_𝕜 = ∑ c, ⟪v a, A (v c)⟫_𝕜 * ⟪v c, B (v b)⟫_𝕜 := by
    conv_lhs => rw [hB b]
    simp [map_sum, inner_sum, inner_smul_right, mul_comm]
  have h2 : ⟪v a, B (A (v b))⟫_𝕜 = ∑ c, ⟪v a, B (v c)⟫_𝕜 * ⟪v c, A (v b)⟫_𝕜 := by
    conv_lhs => rw [hA b]
    simp [map_sum, inner_sum, inner_smul_right, mul_comm]
  change ⟪v a, A (B (v b)) - B (A (v b))⟫_𝕜 = _
  rw [inner_sub_right, h1, h2, ← Finset.sum_sub_distrib]

/-- **One level of the iteration.** Let `v` be orthonormal, let `A` and `B` map each `v_b` into the
span of `v`, and let `A` act diagonally on the vectors indexed by a set `S`, with eigenvalue `r_c`
at `v_c`. Then for `a, b ∈ S`,
`|r_a - r_b| ‖⟨v_a, B v_b⟩‖ ≤ ‖[A, B]‖ + ∑_{c ∉ S} (‖⟨v_a, A v_c⟩‖ ‖⟨v_c, B v_b⟩‖ +
‖⟨v_a, B v_c⟩‖ ‖⟨v_c, A v_b⟩‖)`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1683–1705. -/
theorem abs_sub_mul_norm_inner_le {v : Fin n → E} (hv : Orthonormal 𝕜 v) (A B : E →L[𝕜] E)
    (hA : ∀ b, A (v b) = ∑ c, ⟪v c, A (v b)⟫_𝕜 • v c)
    (hB : ∀ b, B (v b) = ∑ c, ⟪v c, B (v b)⟫_𝕜 • v c) (S : Finset (Fin n)) (r : Fin n → ℝ)
    (hdiag : ∀ c ∈ S, ∀ d ∈ S, ⟪v c, A (v d)⟫_𝕜 = if c = d then (r c : 𝕜) else 0)
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) :
    |r a - r b| * ‖⟪v a, B (v b)⟫_𝕜‖ ≤ ‖A * B - B * A‖ +
      ∑ c ∈ Sᶜ, (‖⟪v a, A (v c)⟫_𝕜‖ * ‖⟪v c, B (v b)⟫_𝕜‖ +
        ‖⟪v a, B (v c)⟫_𝕜‖ * ‖⟪v c, A (v b)⟫_𝕜‖) := by
  set f : Fin n → 𝕜 := fun c =>
    ⟪v a, A (v c)⟫_𝕜 * ⟪v c, B (v b)⟫_𝕜 - ⟪v a, B (v c)⟫_𝕜 * ⟪v c, A (v b)⟫_𝕜
  have e1 : ∑ c ∈ S, ⟪v a, A (v c)⟫_𝕜 * ⟪v c, B (v b)⟫_𝕜 = (r a : 𝕜) * ⟪v a, B (v b)⟫_𝕜 := by
    rw [Finset.sum_congr rfl fun c hc => by rw [hdiag a ha c hc]]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, ha, ↓reduceIte]
  have e2 : ∑ c ∈ S, ⟪v a, B (v c)⟫_𝕜 * ⟪v c, A (v b)⟫_𝕜 = ⟪v a, B (v b)⟫_𝕜 * (r b : 𝕜) := by
    rw [Finset.sum_congr rfl fun c hc => by rw [hdiag c hc b hb]]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hb, ↓reduceIte]
  have hS : ∑ c ∈ S, f c = ((r a - r b : ℝ) : 𝕜) * ⟪v a, B (v b)⟫_𝕜 := by
    simp only [f]
    rw [Finset.sum_sub_distrib, e1, e2]
    push_cast
    ring
  have hsum : ⟪v a, (A * B - B * A) (v b)⟫_𝕜 = ∑ c ∈ S, f c + ∑ c ∈ Sᶜ, f c := by
    rw [inner_commutator_apply_eq_sum A B hA hB, Finset.sum_add_sum_compl]
  have hkey : ((r a - r b : ℝ) : 𝕜) * ⟪v a, B (v b)⟫_𝕜 =
      ⟪v a, (A * B - B * A) (v b)⟫_𝕜 - ∑ c ∈ Sᶜ, f c := by
    rw [hsum, hS]
    ring
  have hcomm : ‖⟪v a, (A * B - B * A) (v b)⟫_𝕜‖ ≤ ‖A * B - B * A‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hv.1 a, one_mul]
    simpa [hv.1 b] using (A * B - B * A).le_opNorm (v b)
  have hrest : ‖∑ c ∈ Sᶜ, f c‖ ≤ ∑ c ∈ Sᶜ, (‖⟪v a, A (v c)⟫_𝕜‖ * ‖⟪v c, B (v b)⟫_𝕜‖ +
      ‖⟪v a, B (v c)⟫_𝕜‖ * ‖⟪v c, A (v b)⟫_𝕜‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  calc |r a - r b| * ‖⟪v a, B (v b)⟫_𝕜‖ = ‖((r a - r b : ℝ) : 𝕜) * ⟪v a, B (v b)⟫_𝕜‖ := by
        rw [norm_mul, RCLike.norm_ofReal]
    _ ≤ ‖⟪v a, (A * B - B * A) (v b)⟫_𝕜‖ + ‖∑ c ∈ Sᶜ, f c‖ := by
        rw [hkey]
        exact norm_sub_le _ _
    _ ≤ _ := add_le_add hcomm hrest

/-- The class of `a` at level `ℓ` of the iteration: the indices whose labels agree with those of
`a` at every level below `ℓ`. At level `0` it is everything. -/
noncomputable def labelClass (r : ℕ → Fin n → ℝ) (ℓ : ℕ) (a : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun c => ∀ m < ℓ, r m c = r m a

theorem mem_labelClass {r : ℕ → Fin n → ℝ} {ℓ : ℕ} {a c : Fin n} :
    c ∈ labelClass r ℓ a ↔ ∀ m < ℓ, r m c = r m a := by
  simp [labelClass]

theorem self_mem_labelClass (r : ℕ → Fin n → ℝ) (ℓ : ℕ) (a : Fin n) : a ∈ labelClass r ℓ a :=
  mem_labelClass.mpr fun _ _ => rfl

/-- The pairs separated first at level `ℓ`: in one class at level `ℓ`, with different labels at
level `ℓ`. -/
noncomputable def levelPairs (r : ℕ → Fin n → ℝ) (ℓ : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.2 ∈ labelClass r ℓ p.1 ∧ r ℓ p.1 ≠ r ℓ p.2

/-- The smallest difference between distinct labels of level `ℓ` within one class, or `1` when
level `ℓ` separates no pair. This is the source's `δλ` at level `ℓ`, which is positive in finite
dimension. -/
noncomputable def levelGap (r : ℕ → Fin n → ℝ) (ℓ : ℕ) : ℝ :=
  if h : (levelPairs r ℓ).Nonempty then
    (levelPairs r ℓ).inf' h fun p => |r ℓ p.1 - r ℓ p.2|
  else 1

theorem levelGap_pos (r : ℕ → Fin n → ℝ) (ℓ : ℕ) : 0 < levelGap r ℓ := by
  unfold levelGap
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    intro p hp
    have hne := (Finset.mem_filter.mp hp).2.2
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  · exact one_pos

theorem levelGap_le {r : ℕ → Fin n → ℝ} {ℓ : ℕ} {a b : Fin n} (hb : b ∈ labelClass r ℓ a)
    (hab : r ℓ a ≠ r ℓ b) : levelGap r ℓ ≤ |r ℓ a - r ℓ b| := by
  have hp : (a, b) ∈ levelPairs r ℓ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hab⟩
  unfold levelGap
  split_ifs with h
  · exact Finset.inf'_le (fun p => |r ℓ p.1 - r ℓ p.2|) hp
  · exact absurd ⟨_, hp⟩ h

theorem mem_labelClass_symm {r : ℕ → Fin n → ℝ} {ℓ : ℕ} {a c : Fin n}
    (h : c ∈ labelClass r ℓ a) : a ∈ labelClass r ℓ c :=
  mem_labelClass.mpr fun m hm => (mem_labelClass.mp h m hm).symm

theorem labelClass_eq_of_mem {r : ℕ → Fin n → ℝ} {ℓ : ℕ} {a b : Fin n}
    (hb : b ∈ labelClass r ℓ a) : labelClass r ℓ b = labelClass r ℓ a := by
  ext c
  simp only [mem_labelClass]
  constructor
  · intro h m hm
    rw [h m hm, mem_labelClass.mp hb m hm]
  · intro h m hm
    rw [h m hm, ← mem_labelClass.mp hb m hm]

variable (A : ℕ → E →L[𝕜] E) (r : ℕ → Fin n → ℝ)

/-- **The bound at the first separating level.** Let `v` be orthonormal, let the operators
`A ℓ` and `B` map each `v_b` into the span of `v`, and let `A ℓ` act diagonally on each class of
level `ℓ`, with eigenvalue `r ℓ c` at `v c`. If `b` is in the class of `a` at level `ℓ` and their
labels at level `ℓ` differ, then
`‖⟨v_a, B v_b⟩‖ ≤ (‖[A ℓ, B]‖ + ∑_{c ∉ class} (…)) / δ_ℓ`, with `δ_ℓ = levelGap r ℓ > 0` and the
sum over the indices outside the class, which are separated from `a` and `b` at an earlier level.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1705. -/
theorem norm_inner_le_of_mem_labelClass {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (hA : ∀ ℓ b, A ℓ (v b) = ∑ c, ⟪v c, A ℓ (v b)⟫_𝕜 • v c) (B : E →L[𝕜] E)
    (hB : ∀ b, B (v b) = ∑ c, ⟪v c, B (v b)⟫_𝕜 • v c)
    (hdiag : ∀ ℓ a, ∀ c ∈ labelClass r ℓ a, ∀ d ∈ labelClass r ℓ a,
      ⟪v c, A ℓ (v d)⟫_𝕜 = if c = d then (r ℓ c : 𝕜) else 0)
    {ℓ : ℕ} {a b : Fin n} (hb : b ∈ labelClass r ℓ a) (hab : r ℓ a ≠ r ℓ b) :
    ‖⟪v a, B (v b)⟫_𝕜‖ ≤ (‖A ℓ * B - B * A ℓ‖ +
      ∑ c ∈ (labelClass r ℓ a)ᶜ, (‖⟪v a, A ℓ (v c)⟫_𝕜‖ * ‖⟪v c, B (v b)⟫_𝕜‖ +
        ‖⟪v a, B (v c)⟫_𝕜‖ * ‖⟪v c, A ℓ (v b)⟫_𝕜‖)) / levelGap r ℓ := by
  have h := abs_sub_mul_norm_inner_le hv (A ℓ) B (hA ℓ) hB (labelClass r ℓ a) (r ℓ)
    (hdiag ℓ a) (self_mem_labelClass r ℓ a) hb
  rw [le_div_iff₀ (levelGap_pos r ℓ), mul_comm]
  exact (mul_le_mul_of_nonneg_right (levelGap_le hb hab) (norm_nonneg _)).trans h

/-- **Two levels, explicitly.** In the setting of `norm_inner_le_of_mem_labelClass`, suppose two
levels separate every pair of basis vectors: any two distinct indices have different labels at
level `0` or at level `1`. Then every off-diagonal element of `B` is at most
`max (‖[A 0, B]‖ / δ₀) ((‖[A 1, B]‖ + 2 n ‖[A 0, A 1]‖ ‖[A 0, B]‖ / δ₀²) / δ₁)`, with
`δ_ℓ = levelGap r ℓ`. With `A 0 = P M_j P`, `A 1 = P M_k P` and `B = P M_i P`, this is the
source's step from `M_j` to `M_k`, Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1695–1705. -/
theorem norm_inner_le_of_two_levels {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (hA : ∀ ℓ b, A ℓ (v b) = ∑ c, ⟪v c, A ℓ (v b)⟫_𝕜 • v c) (B : E →L[𝕜] E)
    (hB : ∀ b, B (v b) = ∑ c, ⟪v c, B (v b)⟫_𝕜 • v c)
    (hdiag : ∀ ℓ a, ∀ c ∈ labelClass r ℓ a, ∀ d ∈ labelClass r ℓ a,
      ⟪v c, A ℓ (v d)⟫_𝕜 = if c = d then (r ℓ c : 𝕜) else 0)
    (hsep : ∀ a b, a ≠ b → r 0 a ≠ r 0 b ∨ r 1 a ≠ r 1 b) {a b : Fin n} (hab : a ≠ b) :
    ‖⟪v a, B (v b)⟫_𝕜‖ ≤ max (‖A 0 * B - B * A 0‖ / levelGap r 0)
      ((‖A 1 * B - B * A 1‖ + 2 * n * (‖A 0 * A 1 - A 1 * A 0‖ / levelGap r 0) *
        (‖A 0 * B - B * A 0‖ / levelGap r 0)) / levelGap r 1) := by
  have hall0 (x y : Fin n) : y ∈ labelClass r 0 x := mem_labelClass.mpr fun m hm => absurd hm
    (Nat.not_lt_zero m)
  -- The bound at level `0`, for any operator.
  have hlevel0 (X : E →L[𝕜] E) (hX : ∀ b, X (v b) = ∑ c, ⟪v c, X (v b)⟫_𝕜 • v c) {x y : Fin n}
      (hxy : r 0 x ≠ r 0 y) : ‖⟪v x, X (v y)⟫_𝕜‖ ≤ ‖A 0 * X - X * A 0‖ / levelGap r 0 := by
    have h := norm_inner_le_of_mem_labelClass A r hv hA X hX hdiag (hall0 x y) hxy
    have hempty : (labelClass r 0 x)ᶜ = ∅ := by
      ext c
      simp [hall0 x c]
    rwa [hempty, Finset.sum_empty, add_zero] at h
  by_cases h0 : r 0 a = r 0 b
  · have h1 : r 1 a ≠ r 1 b := (hsep a b hab).resolve_left (not_not.mpr h0)
    refine le_max_of_le_right ?_
    have hb : b ∈ labelClass r 1 a := mem_labelClass.mpr fun m hm => by
      rw [Nat.lt_one_iff.mp hm]
      exact h0.symm
    refine (norm_inner_le_of_mem_labelClass A r hv hA B hB hdiag hb h1).trans ?_
    set α := ‖A 0 * A 1 - A 1 * A 0‖ / levelGap r 0
    set β := ‖A 0 * B - B * A 0‖ / levelGap r 0
    have hα : 0 ≤ α := div_nonneg (norm_nonneg _) (levelGap_pos r 0).le
    have hβ : 0 ≤ β := div_nonneg (norm_nonneg _) (levelGap_pos r 0).le
    have hout (c : Fin n) (hc : c ∈ (labelClass r 1 a)ᶜ) : r 0 a ≠ r 0 c := by
      intro h
      apply Finset.mem_compl.mp hc
      exact mem_labelClass.mpr fun m hm => by rw [Nat.lt_one_iff.mp hm]; exact h.symm
    have hterm (c : Fin n) (hc : c ∈ (labelClass r 1 a)ᶜ) :
        ‖⟪v a, A 1 (v c)⟫_𝕜‖ * ‖⟪v c, B (v b)⟫_𝕜‖ + ‖⟪v a, B (v c)⟫_𝕜‖ * ‖⟪v c, A 1 (v b)⟫_𝕜‖
          ≤ 2 * (α * β) := by
      have hac := hout c hc
      have hcb : r 0 c ≠ r 0 b := fun h => hac (h0.trans h.symm)
      have e1 := hlevel0 (A 1) (hA 1) hac
      have e2 := hlevel0 B hB hcb
      have e3 := hlevel0 B hB hac
      have e4 := hlevel0 (A 1) (hA 1) hcb
      have p1 := mul_le_mul e1 e2 (norm_nonneg _) hα
      have p2 := mul_le_mul e3 e4 (norm_nonneg _) hβ
      linarith
    have hsum : ∑ c ∈ (labelClass r 1 a)ᶜ, (‖⟪v a, A 1 (v c)⟫_𝕜‖ * ‖⟪v c, B (v b)⟫_𝕜‖ +
          ‖⟪v a, B (v c)⟫_𝕜‖ * ‖⟪v c, A 1 (v b)⟫_𝕜‖) ≤ 2 * n * α * β :=
      calc _ ≤ ∑ _c ∈ (labelClass r 1 a)ᶜ, 2 * (α * β) := Finset.sum_le_sum hterm
        _ = (labelClass r 1 a)ᶜ.card * (2 * (α * β)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ n * (2 * (α * β)) := by
            gcongr
            exact_mod_cast (Finset.card_le_univ _).trans (Fintype.card_fin n).le
        _ = 2 * n * α * β := by ring
    exact div_le_div_of_nonneg_right (by linarith [hsum]) (levelGap_pos r 1).le
  · exact (hlevel0 B hB h0).trans (le_max_left _ _)

/-- **The off-diagonal part after two levels.** Under the hypotheses of
`norm_inner_le_of_two_levels`, the off-diagonal part of `B` in the basis has norm at most `n - 1`
times the bound on its elements. With `B = P M_i P` this bounds `o(i)`, Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1705. -/
theorem norm_offDiagonalPartFamily_le_of_two_levels [NeZero n] {v : Fin n → E}
    (hv : Orthonormal 𝕜 v) (hA : ∀ ℓ b, A ℓ (v b) = ∑ c, ⟪v c, A ℓ (v b)⟫_𝕜 • v c)
    (B : E →L[𝕜] E) (hB : ∀ b, B (v b) = ∑ c, ⟪v c, B (v b)⟫_𝕜 • v c)
    (hdiag : ∀ ℓ a, ∀ c ∈ labelClass r ℓ a, ∀ d ∈ labelClass r ℓ a,
      ⟪v c, A ℓ (v d)⟫_𝕜 = if c = d then (r ℓ c : 𝕜) else 0)
    (hsep : ∀ a b, a ≠ b → r 0 a ≠ r 0 b ∨ r 1 a ≠ r 1 b) :
    ‖offDiagonalPartFamily v B‖ ≤ (n - 1 : ℕ) * max (‖A 0 * B - B * A 0‖ / levelGap r 0)
      ((‖A 1 * B - B * A 1‖ + 2 * n * (‖A 0 * A 1 - A 1 * A 0‖ / levelGap r 0) *
        (‖A 0 * B - B * A 0‖ / levelGap r 0)) / levelGap r 1) :=
  norm_offDiagonalPartFamily_le hv B
    ((div_nonneg (norm_nonneg _) (levelGap_pos r 0).le).trans (le_max_left _ _))
    fun _ _ hab => norm_inner_le_of_two_levels A r hv hA B hB hdiag hsep hab

/-- An index outside the class of `a` at level `ℓ` is separated from `a` at a first level `m < ℓ`:
it lies in the class of `a` at level `m` and has a different label there. -/
theorem exists_lt_mem_labelClass_ne {r : ℕ → Fin n → ℝ} {ℓ : ℕ} {a c : Fin n}
    (hc : c ∉ labelClass r ℓ a) : ∃ m < ℓ, c ∈ labelClass r m a ∧ r m a ≠ r m c := by
  have hex : ∃ m, m < ℓ ∧ r m c ≠ r m a := by
    by_contra h
    push Not at h
    exact hc (mem_labelClass.mpr h)
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, mem_labelClass.mpr fun m hm => ?_,
    fun h => (Nat.find_spec hex).2 h.symm⟩
  by_contra hne
  exact Nat.find_min hex hm ⟨hm.trans (Nat.find_spec hex).1, hne⟩

/-- **The cross terms at a level.** Suppose every element of `A (ℓ + 1)` between two indices
separated at a level `m ≤ ℓ` is at most `α`, and every such element of `X` at most `β`. Then for
`b` in the class of `a` at level `ℓ + 1`, the cross terms of `norm_inner_le_of_mem_labelClass`
are at most `2 n α β`. -/
theorem sum_cross_le {v : Fin n → E} {ℓ : ℕ} (X : E →L[𝕜] E) {a b : Fin n}
    (hb : b ∈ labelClass r (ℓ + 1) a) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hAent : ∀ m ≤ ℓ, ∀ x y, y ∈ labelClass r m x → r m x ≠ r m y →
      ‖⟪v x, A (ℓ + 1) (v y)⟫_𝕜‖ ≤ α)
    (hXent : ∀ m ≤ ℓ, ∀ x y, y ∈ labelClass r m x → r m x ≠ r m y → ‖⟪v x, X (v y)⟫_𝕜‖ ≤ β) :
    ∑ c ∈ (labelClass r (ℓ + 1) a)ᶜ, (‖⟪v a, A (ℓ + 1) (v c)⟫_𝕜‖ * ‖⟪v c, X (v b)⟫_𝕜‖ +
      ‖⟪v a, X (v c)⟫_𝕜‖ * ‖⟪v c, A (ℓ + 1) (v b)⟫_𝕜‖) ≤ 2 * n * α * β := by
  have hterm (c : Fin n) (hc : c ∈ (labelClass r (ℓ + 1) a)ᶜ) :
      ‖⟪v a, A (ℓ + 1) (v c)⟫_𝕜‖ * ‖⟪v c, X (v b)⟫_𝕜‖ +
        ‖⟪v a, X (v c)⟫_𝕜‖ * ‖⟪v c, A (ℓ + 1) (v b)⟫_𝕜‖ ≤ 2 * (α * β) := by
    obtain ⟨m, hm, hca, hne⟩ := exists_lt_mem_labelClass_ne (Finset.mem_compl.mp hc)
    have hml : m ≤ ℓ := Nat.lt_succ_iff.mp hm
    -- `b` agrees with `a` below level `ℓ + 1`, so it is separated from `c` at level `m` too.
    have hbm : b ∈ labelClass r m a := mem_labelClass.mpr fun k hk =>
      mem_labelClass.mp hb k (hk.trans hm)
    have hrb : r m b = r m a := mem_labelClass.mp hb m hm
    have hbc : b ∈ labelClass r m c := by
      rw [labelClass_eq_of_mem hca]
      exact hbm
    have hcb : r m c ≠ r m b := fun h => hne (by rw [h, hrb])
    have e1 := hAent m hml a c hca hne
    have e2 := hXent m hml c b hbc hcb
    have e3 := hXent m hml a c hca hne
    have e4 := hAent m hml c b hbc hcb
    have p1 := mul_le_mul e1 e2 (norm_nonneg _) hα
    have p2 := mul_le_mul e3 e4 (norm_nonneg _) hβ
    linarith
  calc _ ≤ ∑ _c ∈ (labelClass r (ℓ + 1) a)ᶜ, 2 * (α * β) := Finset.sum_le_sum hterm
    _ = (labelClass r (ℓ + 1) a)ᶜ.card * (2 * (α * β)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * (2 * (α * β)) := by
        gcongr
        exact_mod_cast (Finset.card_le_univ _).trans (Fintype.card_fin n).le
    _ = 2 * n * α * β := by ring

/-- The bound on the elements of the compressions `A ℓ` between indices separated at level `ℓ`,
when their commutators are at most `K`: `α₀ = K / δ₀` and
`α_{ℓ+1} = max α_ℓ ((K + 2 n α_ℓ²) / δ_{ℓ+1})`. -/
noncomputable def levelBoundA (n : ℕ) (r : ℕ → Fin n → ℝ) (K : ℝ) : ℕ → ℝ
  | 0 => K / levelGap r 0
  | ℓ + 1 => max (levelBoundA n r K ℓ)
      ((K + 2 * n * levelBoundA n r K ℓ ^ 2) / levelGap r (ℓ + 1))

/-- The bound on the elements of `B` between indices separated at level `ℓ`, when its
commutators with the compressions are at most `K_B` and those of the compressions among
themselves at most `K`: `β₀ = K_B / δ₀` and `β_{ℓ+1} = max β_ℓ ((K_B + 2 n α_ℓ β_ℓ) / δ_{ℓ+1})`.
It is linear in `K_B`. -/
noncomputable def levelBoundB (n : ℕ) (r : ℕ → Fin n → ℝ) (K KB : ℝ) : ℕ → ℝ
  | 0 => KB / levelGap r 0
  | ℓ + 1 => max (levelBoundB n r K KB ℓ)
      ((KB + 2 * n * levelBoundA n r K ℓ * levelBoundB n r K KB ℓ) / levelGap r (ℓ + 1))

theorem levelBoundA_nonneg {K : ℝ} (hK : 0 ≤ K) : ∀ ℓ, 0 ≤ levelBoundA n r K ℓ
  | 0 => div_nonneg hK (levelGap_pos r 0).le
  | ℓ + 1 => le_max_of_le_left (levelBoundA_nonneg hK ℓ)

theorem levelBoundA_mono (K : ℝ) {m ℓ : ℕ} (h : m ≤ ℓ) :
    levelBoundA n r K m ≤ levelBoundA n r K ℓ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_max_left _ _)

theorem levelBoundB_nonneg {K KB : ℝ} (hK : 0 ≤ K) (hKB : 0 ≤ KB) :
    ∀ ℓ, 0 ≤ levelBoundB n r K KB ℓ
  | 0 => div_nonneg hKB (levelGap_pos r 0).le
  | ℓ + 1 => le_max_of_le_left (levelBoundB_nonneg hK hKB ℓ)

theorem levelBoundB_mono (K KB : ℝ) {m ℓ : ℕ} (h : m ≤ ℓ) :
    levelBoundB n r K KB m ≤ levelBoundB n r K KB ℓ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_max_left _ _)

section Assembly

variable {v : Fin n → E} (hv : Orthonormal 𝕜 v)
  (hA : ∀ ℓ b, A ℓ (v b) = ∑ c, ⟪v c, A ℓ (v b)⟫_𝕜 • v c)
  (hdiag : ∀ ℓ a, ∀ c ∈ labelClass r ℓ a, ∀ d ∈ labelClass r ℓ a,
    ⟪v c, A ℓ (v d)⟫_𝕜 = if c = d then (r ℓ c : 𝕜) else 0)
include hv hA hdiag

/-- The elements at the first separating level, when the cross terms are bounded by `2 n α β`. -/
private theorem norm_inner_le_step (X : E →L[𝕜] E)
    (hX : ∀ b, X (v b) = ∑ c, ⟪v c, X (v b)⟫_𝕜 • v c) {KX α β : ℝ} {ℓ : ℕ}
    (hKX : ‖A (ℓ + 1) * X - X * A (ℓ + 1)‖ ≤ KX) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hAent : ∀ m ≤ ℓ, ∀ x y, y ∈ labelClass r m x → r m x ≠ r m y →
      ‖⟪v x, A (ℓ + 1) (v y)⟫_𝕜‖ ≤ α)
    (hXent : ∀ m ≤ ℓ, ∀ x y, y ∈ labelClass r m x → r m x ≠ r m y → ‖⟪v x, X (v y)⟫_𝕜‖ ≤ β)
    {a b : Fin n} (hb : b ∈ labelClass r (ℓ + 1) a) (hab : r (ℓ + 1) a ≠ r (ℓ + 1) b) :
    ‖⟪v a, X (v b)⟫_𝕜‖ ≤ (KX + 2 * n * α * β) / levelGap r (ℓ + 1) :=
  (norm_inner_le_of_mem_labelClass A r hv hA X hX hdiag hb hab).trans
    (div_le_div_of_nonneg_right (add_le_add hKX (sum_cross_le A r X hb hα hβ hAent hXent))
      (levelGap_pos r (ℓ + 1)).le)

/-- The elements at level `0`, where the class is everything. -/
private theorem norm_inner_le_zero (X : E →L[𝕜] E)
    (hX : ∀ b, X (v b) = ∑ c, ⟪v c, X (v b)⟫_𝕜 • v c) {KX : ℝ}
    (hKX : ‖A 0 * X - X * A 0‖ ≤ KX) {a b : Fin n} (hab : r 0 a ≠ r 0 b) :
    ‖⟪v a, X (v b)⟫_𝕜‖ ≤ KX / levelGap r 0 := by
  have hall : b ∈ labelClass r 0 a := mem_labelClass.mpr fun m hm => absurd hm (Nat.not_lt_zero m)
  have h := norm_inner_le_of_mem_labelClass A r hv hA X hX hdiag hall hab
  have hempty : (labelClass r 0 a)ᶜ = ∅ := by
    ext c
    simp [mem_labelClass]
  rw [hempty, Finset.sum_empty, add_zero] at h
  exact h.trans (div_le_div_of_nonneg_right hKX (levelGap_pos r 0).le)

/-- **The compressions at every level.** If all commutators `[A ℓ, A m]` are at most `K`, then
every element of every `A m` between two indices separated first at level `ℓ` is at most
`levelBoundA n r K ℓ`. -/
theorem norm_inner_A_le_levelBoundA {K : ℝ} (hK : 0 ≤ K)
    (hKA : ∀ ℓ m, ‖A ℓ * A m - A m * A ℓ‖ ≤ K) :
    ∀ ℓ m, ∀ a b, b ∈ labelClass r ℓ a → r ℓ a ≠ r ℓ b →
      ‖⟪v a, A m (v b)⟫_𝕜‖ ≤ levelBoundA n r K ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro m a b hb hab
    rcases ℓ with _ | ℓ
    · exact norm_inner_le_zero A r hv hA hdiag (A m) (hA m) (hKA 0 m) hab
    · have hent : ∀ (Y : ℕ), ∀ k ≤ ℓ, ∀ x y, y ∈ labelClass r k x → r k x ≠ r k y →
          ‖⟪v x, A Y (v y)⟫_𝕜‖ ≤ levelBoundA n r K ℓ := fun Y k hk x y hy hxy =>
        (ih k (Nat.lt_succ_of_le hk) Y x y hy hxy).trans (levelBoundA_mono r K hk)
      refine (norm_inner_le_step A r hv hA hdiag (A m) (hA m) (hKA (ℓ + 1) m)
        (levelBoundA_nonneg r hK ℓ) (levelBoundA_nonneg r hK ℓ) (hent (ℓ + 1)) (hent m) hb
        hab).trans ?_
      refine le_trans (le_of_eq ?_) (le_max_right _ _)
      ring

/-- **Any operator at every level.** If all commutators `[A ℓ, A m]` are at most `K` and all
`[A ℓ, B]` at most `K_B`, every element of `B` between two indices separated first at level `ℓ`
is at most `levelBoundB n r K K_B ℓ`, which is linear in `K_B`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1705. -/
theorem norm_inner_le_levelBoundB {K KB : ℝ} (hK : 0 ≤ K) (hKB : 0 ≤ KB)
    (hKA : ∀ ℓ m, ‖A ℓ * A m - A m * A ℓ‖ ≤ K) (B : E →L[𝕜] E)
    (hB : ∀ b, B (v b) = ∑ c, ⟪v c, B (v b)⟫_𝕜 • v c)
    (hKBB : ∀ ℓ, ‖A ℓ * B - B * A ℓ‖ ≤ KB) :
    ∀ ℓ, ∀ a b, b ∈ labelClass r ℓ a → r ℓ a ≠ r ℓ b →
      ‖⟪v a, B (v b)⟫_𝕜‖ ≤ levelBoundB n r K KB ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro a b hb hab
    rcases ℓ with _ | ℓ
    · exact norm_inner_le_zero A r hv hA hdiag B hB (hKBB 0) hab
    · have hAent : ∀ k ≤ ℓ, ∀ x y, y ∈ labelClass r k x → r k x ≠ r k y →
          ‖⟪v x, A (ℓ + 1) (v y)⟫_𝕜‖ ≤ levelBoundA n r K ℓ := fun k hk x y hy hxy =>
        (norm_inner_A_le_levelBoundA A r hv hA hdiag hK hKA k (ℓ + 1) x y hy hxy).trans
          (levelBoundA_mono r K hk)
      have hBent : ∀ k ≤ ℓ, ∀ x y, y ∈ labelClass r k x → r k x ≠ r k y →
          ‖⟪v x, B (v y)⟫_𝕜‖ ≤ levelBoundB n r K KB ℓ := fun k hk x y hy hxy =>
        (ih k (Nat.lt_succ_of_le hk) x y hy hxy).trans (levelBoundB_mono r K KB hk)
      exact (norm_inner_le_step A r hv hA hdiag B hB (hKBB (ℓ + 1))
        (levelBoundA_nonneg r hK ℓ) (levelBoundB_nonneg r hK hKB ℓ) hAent hBent hb hab).trans
        (le_max_right _ _)

/-- **The off-diagonal part after `L` levels.** If every pair of distinct indices is separated at
some level below `L` (the source's iteration ends after `L` steps), then under the bounds of
`norm_inner_le_levelBoundB` the off-diagonal part of `B` has norm at most
`(n - 1) levelBoundB n r K K_B (L - 1)`. With `B = P M_i P` this bounds `o(i)`, Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1705. -/
theorem norm_offDiagonalPartFamily_le_levelBoundB [NeZero n] {K KB : ℝ} (hK : 0 ≤ K)
    (hKB : 0 ≤ KB) (hKA : ∀ ℓ m, ‖A ℓ * A m - A m * A ℓ‖ ≤ K) (B : E →L[𝕜] E)
    (hB : ∀ b, B (v b) = ∑ c, ⟪v c, B (v b)⟫_𝕜 • v c)
    (hKBB : ∀ ℓ, ‖A ℓ * B - B * A ℓ‖ ≤ KB) {L : ℕ}
    (hsep : ∀ a b, a ≠ b → ∃ ℓ < L, r ℓ a ≠ r ℓ b) :
    ‖offDiagonalPartFamily v B‖ ≤ (n - 1 : ℕ) * levelBoundB n r K KB (L - 1) := by
  refine norm_offDiagonalPartFamily_le hv B (levelBoundB_nonneg r hK hKB _) fun a b hab => ?_
  obtain ⟨ℓ, hℓ, hne⟩ := hsep a b hab
  obtain ⟨m, hm, hbm, hrm⟩ : ∃ m ≤ ℓ, b ∈ labelClass r m a ∧ r m a ≠ r m b := by
    by_cases hb : b ∈ labelClass r ℓ a
    · exact ⟨ℓ, le_rfl, hb, hne⟩
    · obtain ⟨m, hm, hbm, hrm⟩ := exists_lt_mem_labelClass_ne hb
      exact ⟨m, hm.le, hbm, hrm⟩
  exact (norm_inner_le_levelBoundB A r hv hA hdiag hK hKB hKA B hB hKBB m a b hbm hrm).trans
    (levelBoundB_mono r K KB (by omega))

end Assembly

end TNLean.Lattice
