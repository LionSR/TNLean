/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.FrustrationFree.PhysicalDetectability
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Analysis.Projection.DetectabilityLemma
import QICLean.ManyBody.Sites.Support
import QICLean.ManyBody.Hamiltonian.FrustrationFree

/-!
# The actual regional frustration-free truncation

For an interval of sites, retain the original interactions outside the
interval and replace its two parity layers by the complements of their
actual projection products. The construction is ALVV, arXiv:1602.08828v2,
`def:FF-tH`, lines 1467–1487. Positivity and the common kernel are proved
without a uniqueness or gap hypothesis.

## Support of the actual physical parity products

A parity product acts on any region containing its selected bond terms.
This is the support step in ALVV, arXiv:1602.08828v2, `thm:FF-tH`,
lines 1543–1568. No commutation or projection hypothesis is required.

## The truncation as an interaction

The retained bond terms and the two regional parity complements are the terms of one interaction
on the chain, `regionalTruncationInteraction`, whose Hamiltonian is the truncation. For
projection terms its zero space is the zero space of the original interaction
(`zeroSpace_regionalTruncationInteraction`): ALVV, arXiv:1602.08828v2, `thm:FF-tH`,
lines 1543–1550.
-/

section

open ManyBody (interval mem_interval)

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)

/-- The actual regional Hamiltonian obtained by replacing the two internal
parity layers by their complementary products. ALVV, arXiv:1602.08828v2,
`def:FF-tH`, lines 1467–1487. -/
noncomputable def physicalFrustrationFreeTruncation
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  (∑ i, if a ≤ i.val ∧ i.val + 1 < b then 0 else Φ.term i) +
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
      (1 - physicalParityProduct
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) 0) +
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
      (1 - physicalParityProduct
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) 1)

private theorem restrict_term_isStarProjection
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (s : Fin (L - 1) → Prop) [DecidablePred s]
    (i : Fin (L - 1)) : IsStarProjection ((Φ.restrict s).term i) :=
  ManyBody.Interaction.forall_restrict_term (IsStarProjection.zero _) (hp i)

private theorem regionalParityComplement_isStarProjection
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b p : ℕ) :
    IsStarProjection
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
        (1 - physicalParityProduct
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p)) := by
  exact (physicalParityProduct_isStarProjection
    (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b)
    (restrict_term_isStarProjection Φ hp _) p).one_sub.map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm.toStarAlgHom

/-- The actual regional frustration-free truncation is positive semidefinite.
ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1550. -/
theorem physicalFrustrationFreeTruncation_posSemidef
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ) :
    (physicalFrustrationFreeTruncation Φ a b).PosSemidef := by
  unfold physicalFrustrationFreeTruncation
  refine (Matrix.PosSemidef.add (Matrix.PosSemidef.add ?_
    (Matrix.nonneg_iff_posSemidef.mp
      (regionalParityComplement_isStarProjection Φ hp a b 0).nonneg))
      (Matrix.nonneg_iff_posSemidef.mp
        (regionalParityComplement_isStarProjection Φ hp a b 1).nonneg))
  exact Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ ↦ ite_nonneg (le_refl 0) (hp i).nonneg)

/-- The actual parity product retains the common support of its selected terms.
ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1568. -/
theorem isSupportedOn_physicalParityProduct
    (Φ : ManyBody.BondInteraction L q)
    (p : ℕ) (D : Finset (Fin L))
    (hs : ∀ i, i.val % 2 = p → ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (Φ.term i) D) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      ((T).symm (physicalParityProduct Φ p)) D := by
  change _ ∈ ManyBody.supportedOperators _ _
  apply QuantumCircuit.mem_supportedOperators_complementProd
  intro k hk
  change (T).symm (if hk' : k < L - 1 then
      if k % 2 = p then T (Φ.term ⟨k, hk'⟩) else 0 else 0) ∈
    ManyBody.supportedOperators (fun _ ↦ Fin q) D
  rw [dite_eq_left hk]
  split_ifs with hp
  · rw [StarAlgEquiv.symm_apply_apply]
    exact hs ⟨k, hk⟩ hp
  · simpa only [map_zero] using
      (zero_mem (ManyBody.supportedOperators (fun _ ↦ Fin q) D))

/-- The actual parity product of the interval-restricted family is supported
on that same site interval. The support is derived from the original
nearest-neighbour terms. ALVV, arXiv:1602.08828v2, `def:FF-tH`,
lines 1467--1487. -/
theorem isSupportedOn_regionalParityProduct
    (Φ : ManyBody.BondInteraction L q) (a b p : ℕ) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      ((T).symm (physicalParityProduct (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p))
      (interval L a b) := by
  change _ ∈ ManyBody.supportedOperators _ _
  apply isSupportedOn_physicalParityProduct
  intro i _
  rw [ManyBody.Interaction.restrict_term]
  split_ifs with hi
  · apply ManyBody.IsSupportedOn.mono (Φ.mem i)
    intro v hv
    simp only [mem_interval] at *
    omega
  · change _ ∈ ManyBody.supportedOperators _ _
    exact zero_mem (ManyBody.supportedOperators (fun _ : Fin L ↦ Fin q) _)

/-- The regional truncation as an interaction on the chain: the bond term `h_i` on its bond
when the bond `{i, i + 1}` is not contained in the site interval `[a, b)`, zero otherwise, and
the two regional parity complements `I - Q_p` on `[a, b)`. ALVV, arXiv:1602.08828v2,
`def:FF-tH`, lines 1467–1487. -/
noncomputable def regionalTruncationInteraction
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ) :
    ManyBody.Interaction (fun _ : Fin L ↦ Fin q)
      (Sum.elim (fun i : Fin (L - 1) ↦ interval L i.val (i.val + 2))
        fun _ : Fin 2 ↦ interval L a b) where
  term := Sum.elim (fun i ↦ if a ≤ i.val ∧ i.val + 1 < b then 0 else Φ.term i)
    fun p ↦ (T).symm (1 - physicalParityProduct
      (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val)
  mem := by
    rintro (i | p)
    · dsimp only [Sum.elim_inl]
      split_ifs
      · exact zero_mem _
      · exact Φ.mem i
    · dsimp only [Sum.elim_inr]
      rw [map_sub, map_one]
      exact sub_mem (one_mem _) (isSupportedOn_regionalParityProduct Φ a b p.val)

/-- The Hamiltonian of the regional truncation interaction is the regional truncation.
ALVV, arXiv:1602.08828v2, `def:FF-tH`, lines 1467–1487. -/
theorem hamiltonian_regionalTruncationInteraction
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ) :
    (regionalTruncationInteraction Φ a b).hamiltonian =
      physicalFrustrationFreeTruncation Φ a b := by
  simp only [ManyBody.Interaction.hamiltonian, Fintype.sum_sum_type, Fin.sum_univ_two,
    regionalTruncationInteraction, Sum.elim_inl, Sum.elim_inr, physicalFrustrationFreeTruncation,
    Fin.val_zero, Fin.val_one]
  exact (add_assoc _ _ _).symm

/-- Every term of the regional truncation interaction is an orthogonal projection when the bond
terms are. ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and
1543–1550. -/
theorem isStarProjection_regionalTruncationInteraction_term
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ)
    (j : Fin (L - 1) ⊕ Fin 2) :
    IsStarProjection ((regionalTruncationInteraction Φ a b).term j) := by
  rcases j with i | p
  · change IsStarProjection (if a ≤ i.val ∧ i.val + 1 < b then 0 else Φ.term i)
    split_ifs
    · exact IsStarProjection.zero _
    · exact hp i
  · exact regionalParityComplement_isStarProjection Φ hp a b p.val

/-- **The zero space of the regional truncation.** For projection bond terms, a vector is
annihilated by every term of the regional truncation interaction exactly when it is annihilated
by every bond term. This does not require a ground vector, uniqueness, or a gap.
ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1550. -/
theorem zeroSpace_regionalTruncationInteraction
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ) :
    (regionalTruncationInteraction Φ a b).zeroSpace = Φ.zeroSpace := by
  ext x
  simp only [ManyBody.Interaction.zeroSpace_eq_iInf_ker, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ j, T ((regionalTruncationInteraction Φ a b).term j) x = 0) ↔
    ∀ i, T (Φ.term i) x = 0
  constructor
  · intro hterm
    have hfix (p : Fin 2) :
        physicalParityProduct
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val x = x := by
      have hp := hterm (.inr p)
      change T ((T).symm (1 - physicalParityProduct
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val)) x = 0 at hp
      rw [StarAlgEquiv.apply_symm_apply] at hp
      exact (sub_eq_zero.mp hp).symm
    intro i
    by_cases hi : a ≤ i.val ∧ i.val + 1 < b
    · have hm := (physicalParityProduct_apply_eq_self_iff
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b)
        (restrict_term_isStarProjection Φ hp _) (i.val % 2) x).mp
          (hfix ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩) i rfl
      simpa only [ManyBody.Interaction.restrict_term, ite_eq_left hi] using hm
    · have hi' := hterm (.inl i)
      change T (if a ≤ i.val ∧ i.val + 1 < b then 0 else Φ.term i) x = 0 at hi'
      rwa [ite_eq_right hi] at hi'
  · intro hzero
    have hmask : T (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b).hamiltonian x = 0 := by
      simp only [ManyBody.Interaction.hamiltonian, map_sum, _root_.sum_apply,
        ManyBody.Interaction.restrict_term, apply_ite,
        map_zero, DFunLike.ite_apply, _root_.zero_apply, hzero, ite_self, Finset.sum_const_zero]
    have hfix (p : Fin 2) :
        physicalParityProduct
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val x = x :=
      physicalParityProduct_fixes_kernel
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b)
        (restrict_term_isStarProjection Φ hp _) hmask p.val
    rintro (i | p)
    · change T (if a ≤ i.val ∧ i.val + 1 < b then 0 else Φ.term i) x = 0
      split_ifs
      · simp
      · exact hzero i
    · change T ((T).symm (1 - physicalParityProduct
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val)) x = 0
      rw [StarAlgEquiv.apply_symm_apply, _root_.sub_apply, hfix p,
        one_apply_eq_self, sub_self]

/-- The two actual regional replacement terms have total operator norm at
most two. ALVV, arXiv:1602.08828v2, `def:FF-tH` and `def:HLeven-odd`,
lines 1467–1487. -/
theorem norm_physicalFrustrationFreeTruncation_region_le_two
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
        (1 - physicalParityProduct
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) 0) +
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
        (1 - physicalParityProduct
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) 1)‖ ≤ 2 := by
  simpa only [one_add_one_eq_two] using (norm_add_le _ _).trans
    (add_le_add
      (IsStarProjection.norm_le _ (regionalParityComplement_isStarProjection Φ hp a b 0))
      (IsStarProjection.norm_le _ (regionalParityComplement_isStarProjection Φ hp a b 1)))

/-- The complementary masses of the original parity products are bounded
by the actual regional truncated energy. ALVV, arXiv:1602.08828v2,
`thm:FF-tH`, lines 1543–1550. No vector normalization or gap is required. -/
theorem sum_norm_sq_sub_physicalParityProduct_le_truncation
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖x - physicalParityProduct Φ 0 x‖ ^ 2 +
      ‖x - physicalParityProduct Φ 1 x‖ ^ 2 ≤
        (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (physicalFrustrationFreeTruncation Φ a b) x⟫_ℂ).re := by
  let Ψ := Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b
  let Ψg := Φ.restrict fun i ↦ ¬(a ≤ i.val ∧ i.val + 1 < b)
  have hP (p : ℕ) : IsStarProjection (physicalParityProduct Ψ p) :=
    physicalParityProduct_isStarProjection Ψ
      (restrict_term_isStarProjection Φ hp _) p
  have hsplit (p : ℕ) : physicalParityProduct Φ p =
      physicalParityProduct Ψ p * physicalParityProduct Ψg p := by
    exact physicalParityProduct_partition Φ
      (fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p
  have hmass (p : ℕ) : ‖x - physicalParityProduct Φ p x‖ ^ 2 ≤
      ‖x - physicalParityProduct Ψ p x‖ ^ 2 +
        ‖x - physicalParityProduct Ψg p x‖ ^ 2 := by
    rw [hsplit p]
    exact ContinuousLinearMap.IsStarProjection.norm_sub_apply_sq_le (hP p) x
      (physicalParityProduct Ψg p x)
  have hout := sum_norm_sq_sub_physicalParityProduct_le Ψg
    (restrict_term_isStarProjection Φ hp _) x
  have hg : Ψg.hamiltonian = ∑ i, if a ≤ i.val ∧ i.val + 1 < b then 0 else Φ.term i :=
    Finset.sum_congr rfl fun i _ ↦ by
      by_cases hi : a ≤ i.val ∧ i.val + 1 < b
      · rw [ManyBody.Interaction.restrict_term, ite_eq_right (not_not_intro hi), ite_eq_left hi]
      · rw [ManyBody.Interaction.restrict_term, ite_eq_left hi, ite_eq_right hi]
  have hnorm (p : ℕ) :
      (⟪x, (1 - physicalParityProduct Ψ p) x⟫_ℂ).re =
        ‖x - physicalParityProduct Ψ p x‖ ^ 2 :=
    ContinuousLinearMap.IsStarProjection.re_inner_apply_self (hP p).one_sub x
  have henergy :
      (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (physicalFrustrationFreeTruncation Φ a b) x⟫_ℂ).re =
      (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Ψg.hamiltonian x⟫_ℂ).re +
        ‖x - physicalParityProduct Ψ 0 x‖ ^ 2 +
          ‖x - physicalParityProduct Ψ 1 x‖ ^ 2 := by
    rw [← hnorm 0, ← hnorm 1, hg]
    simp only [physicalFrustrationFreeTruncation, map_add, StarAlgEquiv.apply_symm_apply,
      _root_.add_apply, inner_add_right, Complex.add_re]
    rfl
  linarith only [hmass 0, hmass 1, hout, henergy]

/-- The converse detectability estimate with the actual regional truncated
energy and the original physical detectability operator. ALVV,
arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1568. The constant three
strengthens the source's converse constant four. -/
theorem one_sub_three_mul_truncated_energy_le_norm_sq_physicalDetectability
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ)
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1) :
    1 - 3 * (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (physicalFrustrationFreeTruncation Φ a b) x⟫_ℂ).re ≤
        ‖physicalDetectability Φ x‖ ^ 2 := by
  have hconv :=
    ContinuousLinearMap.IsStarProjection.one_sub_three_mul_le_norm_sq_apply_apply
      (physicalParityProduct_isStarProjection Φ hp 1)
      (physicalParityProduct_isStarProjection Φ hp 0) hx
  have hmass := sum_norm_sq_sub_physicalParityProduct_le_truncation Φ hp a b x
  change _ ≤ ‖physicalDetectability Φ x‖ ^ 2 at hconv
  linarith only [hmass, hconv]

/-- A unit vector orthogonal to the full truncated kernel has a uniform
positive truncated energy, derived from the original nonzero spectral gap.
ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1562–1568. The bound applies
to arbitrary kernel dimension and does not require an upper bound on the gap. -/
theorem physicalFrustrationFreeTruncation_energy_ge_of_spectral_gap
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ e ∈ spectrum ℝ Φ.hamiltonian, e = 0 ∨ gamma ≤ e)
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1)
    (horth : ∀ z : EuclideanSpace ℂ (Fin L → Fin q),
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (physicalFrustrationFreeTruncation Φ a b) z = 0 → ⟪z, x⟫_ℂ = 0) :
    gamma / (3 * (4 + gamma)) ≤
      (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (physicalFrustrationFreeTruncation Φ a b) x⟫_ℂ).re := by
  have hden : 0 < 4 + gamma := by linarith only [hgamma]
  have hconv := one_sub_three_mul_truncated_energy_le_norm_sq_physicalDetectability
    Φ hp a b hx
  have hpsd (i : Fin (L - 1)) : (Φ.term i).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (hp i).nonneg
  have hpsd' (j : Fin (L - 1) ⊕ Fin 2) :
      ((regionalTruncationInteraction Φ a b).term j).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (isStarProjection_regionalTruncationInteraction_term Φ hp a b j).nonneg
  have hD := norm_sq_physicalDetectability_le_of_spectral_gap Φ hp hgamma hgap
    fun z hz ↦ horth z (by
      rw [← hamiltonian_regionalTruncationInteraction]
      refine ((ManyBody.Interaction.zeroVector_tfae hpsd' z).out 1 5).mp ?_
      rw [zeroSpace_regionalTruncationInteraction Φ hp a b]
      exact ((ManyBody.Interaction.zeroVector_tfae hpsd z).out 1 5).mpr hz)
  have hDunit : ‖physicalDetectability Φ x‖ ^ 2 ≤ 4 / (4 + gamma) := by
    simpa only [hx, one_pow, mul_one] using hD
  have hmul := (le_div_iff₀ hden).mp (hconv.trans hDunit)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3) hden)).mpr
  nlinarith only [hmul]

/-- The actual regional frustration-free truncation retains a nonzero spectral
gap of at least `gamma / (3 * (4 + gamma))`. This proves the spectral
conclusion of ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1562–1568,
for the full kernel, without a dimension-one assumption. -/
theorem physicalFrustrationFreeTruncation_spectral_gap
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ e ∈ spectrum ℝ Φ.hamiltonian, e = 0 ∨ gamma ≤ e) :
    ∀ e ∈ spectrum ℝ (physicalFrustrationFreeTruncation Φ a b),
      e = 0 ∨ gamma / (3 * (4 + gamma)) ≤ e := by
  have hH := (physicalFrustrationFreeTruncation_posSemidef Φ hp a b).isHermitian
  rintro e he
  obtain ⟨i, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ he
  by_cases hzero : hH.eigenvalues i = 0
  · exact Or.inl hzero
  · refine Or.inr ?_
    have horth : ∀ z : EuclideanSpace ℂ (Fin L → Fin q),
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (physicalFrustrationFreeTruncation Φ a b) z = 0 →
        ⟪z, hH.eigenvectorBasis i⟫_ℂ = 0 := by
      intro z hz
      have hi := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH z (hH.eigenvectorBasis i)
      change ⟪Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (physicalFrustrationFreeTruncation Φ a b) z, hH.eigenvectorBasis i⟫_ℂ =
        ⟪z, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (physicalFrustrationFreeTruncation Φ a b) (hH.eigenvectorBasis i)⟫_ℂ at hi
      rw [hz, inner_zero_left, hH.toEuclideanCLM_eigenvectorBasis, inner_smul_right] at hi
      exact (mul_eq_zero.mp hi.symm).resolve_left (Complex.ofReal_ne_zero.mpr hzero)
    have henergy := physicalFrustrationFreeTruncation_energy_ge_of_spectral_gap
      Φ hp a b hgamma hgap (hH.eigenvectorBasis.norm_eq_one i) horth
    rw [hH.toEuclideanCLM_eigenvectorBasis, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hH.eigenvectorBasis.norm_eq_one i] at henergy
    simpa using henergy

end TNLean.MPS.AreaLaw

end
