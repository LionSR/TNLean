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
matrix element is bounded at the first level separating its two vectors. With two levels, the
bound is explicit (`norm_inner_le_of_two_levels`).

## Main statements

* `inner_commutator_apply_eq_sum`: the matrix elements of a commutator in a basis preserved by
  both operators.
* `abs_sub_mul_norm_inner_le`: one level of the iteration.
* `labelClass`, `levelGap`, `levelGap_pos`: the classes of the iteration and the smallest
  difference of distinct labels in a class.
* `norm_inner_le_of_mem_labelClass`: the bound at the first level separating two basis vectors.
* `norm_inner_le_of_two_levels`, `norm_offDiagonalPartFamily_le_of_two_levels`: two levels, with
  explicit constants.

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

end TNLean.Lattice
