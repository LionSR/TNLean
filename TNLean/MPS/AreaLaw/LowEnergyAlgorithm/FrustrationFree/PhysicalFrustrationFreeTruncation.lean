/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.FrustrationFree.PhysicalDetectability
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Analysis.Projection.Residual
import QICLean.ManyBody.Sites.SupportedComplementProduct

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
-/

section

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

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

private noncomputable def regionalTruncationTerm
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ) :
    Fin (L - 1) ⊕ Fin 2 →
      (EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
  | .inl i => if a ≤ i.val ∧ i.val + 1 < b then 0 else
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Φ.term i)
  | .inr p => 1 - physicalParityProduct
      (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val

private theorem sum_regionalTruncationTerm
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ) :
    (∑ i, regionalTruncationTerm Φ a b i) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (physicalFrustrationFreeTruncation Φ a b) := by
  simp only [Fintype.sum_sum_type, regionalTruncationTerm, Fin.sum_univ_two,
    physicalFrustrationFreeTruncation, map_add, map_sum, apply_ite, map_zero,
    StarAlgEquiv.apply_symm_apply, Fin.val_zero, Fin.val_one]
  exact (add_assoc _ _ _).symm

private theorem regionalTruncationTerm_isStarProjection
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ)
    (i : Fin (L - 1) ⊕ Fin 2) : IsStarProjection (regionalTruncationTerm Φ a b i) := by
  cases i <;> dsimp only [regionalTruncationTerm]
  case inl i =>
    split_ifs <;> first
      | exact IsStarProjection.zero _
      | exact (hp i).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
  case inr p =>
    exact (physicalParityProduct_isStarProjection
      (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b)
      (restrict_term_isStarProjection Φ hp _) p.val).one_sub

/-- The actual regional truncation preserves the full kernel of the original
Hamiltonian. This does not require a ground vector, uniqueness, or a gap.
ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1550. -/
theorem physicalFrustrationFreeTruncation_kernel_iff
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (a b : ℕ)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (physicalFrustrationFreeTruncation Φ a b) x = 0 ↔
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian x = 0 := by
  constructor
  · intro hx
    have hsum : (∑ i, (regionalTruncationTerm Φ a b i).toLinearMap) x = 0 := by
      simpa only [← sum_regionalTruncationTerm, _root_.sum_apply, LinearMap.sum_apply,
        ContinuousLinearMap.coe_coe] using hx
    have hterm (i : Fin (L - 1) ⊕ Fin 2) : regionalTruncationTerm Φ a b i x = 0 :=
      ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero _
        (fun j ↦ ContinuousLinearMap.IsStarProjection.isSymmetricProjection
          (regionalTruncationTerm_isStarProjection Φ hp a b j)) hsum i
    have hfix (p : Fin 2) :
        physicalParityProduct
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val x = x := by
      exact (sub_eq_zero.mp (hterm (.inr p))).symm
    have hzero (i : Fin (L - 1)) :
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Φ.term i) x = 0 := by
      by_cases hi : a ≤ i.val ∧ i.val + 1 < b
      · have hm := (physicalParityProduct_apply_eq_self_iff
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b)
          (restrict_term_isStarProjection Φ hp _) (i.val % 2) x).mp
            (hfix ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩) i rfl
        simpa only [ManyBody.Interaction.restrict_term, ite_eq_left hi] using hm
      · simpa only [regionalTruncationTerm, ite_eq_right hi] using hterm (.inl i)
    simp only [ManyBody.Interaction.hamiltonian, map_sum, _root_.sum_apply, hzero,
      Finset.sum_const_zero]
  · intro hx
    have hzero (i : Fin (L - 1)) :
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Φ.term i) x = 0 :=
      ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
        (fun j ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (Φ.term j)).toLinearMap)
        (fun j ↦ ContinuousLinearMap.IsStarProjection.isSymmetricProjection
          ((hp j).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))))
        (by simpa only [ManyBody.Interaction.hamiltonian, map_sum, _root_.sum_apply,
          LinearMap.sum_apply, ContinuousLinearMap.coe_coe] using hx) i
    have hmask : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b).hamiltonian x = 0 := by
      simp only [ManyBody.Interaction.hamiltonian, map_sum, _root_.sum_apply,
        ManyBody.Interaction.restrict_term, apply_ite,
        map_zero, DFunLike.ite_apply, _root_.zero_apply, hzero, ite_self, Finset.sum_const_zero]
    have hfix (p : Fin 2) :
        physicalParityProduct
          (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p.val x = x :=
      physicalParityProduct_fixes_kernel
        (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b)
        (restrict_term_isStarProjection Φ hp _) hmask p.val
    suffices hterm : ∀ i, regionalTruncationTerm Φ a b i x = 0 by
      simp only [← sum_regionalTruncationTerm, _root_.sum_apply, hterm, Finset.sum_const_zero]
    rintro (i | p) <;> simp [regionalTruncationTerm, DFunLike.ite_apply, hzero, hfix]

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
  have hD := norm_sq_physicalDetectability_le_of_spectral_gap Φ hp hgamma hgap
    (fun z hz ↦ horth z ((physicalFrustrationFreeTruncation_kernel_iff Φ hp a b z).mpr hz))
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

section

open ManyBody (interval mem_interval)

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)

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

end TNLean.MPS.AreaLaw

end
