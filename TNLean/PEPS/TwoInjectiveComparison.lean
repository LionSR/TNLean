import TNLean.PEPS.TwoInjectiveComparison.Basic

/-!
# Two-injective-tensor comparison for PEPS

This file contains the scalar proportionality conclusion and the public
comparison theorem used in the injective PEPS Fundamental Theorem.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {Bond : Type*} [Fintype Bond]
variable {bondDim : Bond → Type*} [∀ b, Fintype (bondDim b)]

/-! ### From the bond gauge to scalar proportionality -/

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- Coefficient matching for a bilinear form over two linearly independent
families. If the bilinear form `∑_{k,l} c k l · u k · w l` vanishes for every
pair of test vectors and the families `u`, `w` are linearly independent, then
all coefficients `c k l` vanish.

This is the elementary bilinear separation used to read off the gauge
constraints from the one-leg-open contraction identities of arXiv:1804.04964,
Section 3, Lemma inj_equal_tensors_2. -/
theorem bilinear_coeff_zero {K L V1 V2 : Type*} [Fintype K] [Fintype L]
    {u : K → V1 → ℂ} {w : L → V2 → ℂ}
    (hu : LinearIndependent ℂ u) (hw : LinearIndependent ℂ w)
    (c : K → L → ℂ)
    (h : ∀ (p1 : V1) (p2 : V2), (∑ k, ∑ l, c k l * u k p1 * w l p2) = 0) :
    ∀ k l, c k l = 0 := by
  classical
  have step : ∀ (p1 : V1) (l : L), (∑ k, c k l * u k p1) = 0 := by
    intro p1
    have hzero : (∑ l, (∑ k, c k l * u k p1) • w l) = 0 := by
      funext p2
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hrw : (∑ l, (∑ k, c k l * u k p1) * w l p2)
            = ∑ k, ∑ l, c k l * u k p1 * w l p2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [Finset.sum_mul]
      rw [hrw]
      exact h p1 p2
    exact (Fintype.linearIndependent_iff.1 hw) _ hzero
  intro k₀ l₀
  have hzero : (∑ k, c k l₀ • u k) = 0 := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact step p1 l₀
  exact (Fintype.linearIndependent_iff.1 hu) _ hzero k₀

open scoped Classical in
/-- Reindexing a one-bond-open sum by the bond update `μ ↦ update μ b q`, which
bijects the configurations valued `p` at bond `b` onto those valued `q`.

This is the change of summation variable that turns the `A`-side of a one-leg-open
contraction into a sum over the configurations on the `A₂`-leg, used in
arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2. -/
theorem reindex_update {M : Type*} [AddCommMonoid M]
    (b : Bond) (p q : bondDim b) (f : SharedBondConfig bondDim → M) :
    (∑ μ : SharedBondConfig bondDim, if μ b = p then f (Function.update μ b q) else 0)
      = ∑ ρ : SharedBondConfig bondDim, if ρ b = q then f ρ else 0 := by
  classical
  rw [← Finset.sum_filter (fun μ : SharedBondConfig bondDim => μ b = p),
    ← Finset.sum_filter (fun ρ : SharedBondConfig bondDim => ρ b = q)]
  refine Finset.sum_bij' (fun μ _ => Function.update μ b q) (fun ρ _ => Function.update ρ b p)
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ ⊢
    rw [Function.update_self]
  · intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    rw [Function.update_self]
  · intro μ hμ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ
    change Function.update (Function.update μ b q) b p = μ
    rw [Function.update_idem, ← hμ, Function.update_eq_self]
  · intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    change Function.update (Function.update ρ b p) b q = ρ
    rw [Function.update_idem, ← hρ, Function.update_eq_self]
  · intro μ hμ
    rfl

open scoped Classical in
/-- The master per-bond constraint on the bond gauge `g`. Substituting the two
gauge equations `A₁ = g · B₁` and `B₂ = g · A₂` into the one-leg-open contraction
identity (`sameOpenBondContraction`) and separating the two injective families
`B₁` and `A₂` forces, for every shared bond `b` and every pair of endpoints
`p, q`, the identity

`[ρ b = q] · g (update ρ b p) ν = [ν b = p] · g ρ (update ν b q)`

for all configurations `ν, ρ`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem bondGauge_master_constraint
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (g : Matrix (SharedBondConfig bondDim) (SharedBondConfig bondDim) ℂ)
    (hg1 : ∀ (η₁ : External₁) (μ : SharedBondConfig bondDim) (σ₁ : Physical₁),
      A₁ η₁ μ σ₁ = ∑ ν, g μ ν * B₁ η₁ ν σ₁)
    (hg2 : ∀ (η₂ : External₂) (ν : SharedBondConfig bondDim) (σ₂ : Physical₂),
      B₂ η₂ ν σ₂ = ∑ μ, g μ ν * A₂ η₂ μ σ₂)
    (hB₁c : LinearIndependent ℂ
      (fun ν : SharedBondConfig bondDim => fun p : External₁ × Physical₁ => B₁ p.1 ν p.2))
    (hA₂c : LinearIndependent ℂ
      (fun ρ : SharedBondConfig bondDim => fun p : External₂ × Physical₂ => A₂ p.1 ρ p.2))
    (hopen : SameTwoBlockInsertions A₁ B₁ A₂ B₂) :
    ∀ (b : Bond) (p q : bondDim b) (ν ρ : SharedBondConfig bondDim),
      (if ρ b = q then g (Function.update ρ b p) ν else 0) =
        (if ν b = p then g ρ (Function.update ν b q) else 0) := by
  classical
  intro b p q
  have key := bilinear_coeff_zero (K := SharedBondConfig bondDim) (L := SharedBondConfig bondDim)
    (V1 := External₁ × Physical₁) (V2 := External₂ × Physical₂)
    (u := fun ν p => B₁ p.1 ν p.2) (w := fun ρ p => A₂ p.1 ρ p.2)
    hB₁c hA₂c
    (fun ν ρ => (if ρ b = q then g (Function.update ρ b p) ν else 0)
                 - (if ν b = p then g ρ (Function.update ν b q) else 0))
    ?_
  · intro ν ρ
    have := key ν ρ
    rwa [sub_eq_zero] at this
  · rintro ⟨η₁, σ₁⟩ ⟨η₂, σ₂⟩
    have hO := sameOpenBondContraction A₁ B₁ A₂ B₂ hopen b p q η₁ η₂ σ₁ σ₂
    -- Rewrite the `A`-side as a bilinear form with coefficient `cLHS`.
    have hLHS : (∑ μ : SharedBondConfig bondDim,
          (if μ b = p then A₁ η₁ μ σ₁ * A₂ η₂ (Function.update μ b q) σ₂ else 0))
        = ∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ρ b = q then g (Function.update ρ b p) ν else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ := by
      have stepA : (∑ μ : SharedBondConfig bondDim,
            (if μ b = p then A₁ η₁ μ σ₁ * A₂ η₂ (Function.update μ b q) σ₂ else 0))
          = ∑ μ : SharedBondConfig bondDim,
            (if μ b = p then
              (fun ρ : SharedBondConfig bondDim =>
                (∑ ν, g (Function.update ρ b p) ν * B₁ η₁ ν σ₁) * A₂ η₂ ρ σ₂)
                (Function.update μ b q)
              else 0) := by
        refine Finset.sum_congr rfl ?_
        intro μ _
        by_cases hμ : μ b = p
        · rw [if_pos hμ, if_pos hμ]
          simp only [Function.update_idem]
          rw [hg1 η₁ μ σ₁, ← hμ, Function.update_eq_self]
        · rw [if_neg hμ, if_neg hμ]
      rw [stepA, reindex_update b p q
        (fun ρ : SharedBondConfig bondDim =>
          (∑ ν, g (Function.update ρ b p) ν * B₁ η₁ ν σ₁) * A₂ η₂ ρ σ₂)]
      have stepB : (∑ ρ : SharedBondConfig bondDim,
            (if ρ b = q then
              (∑ ν, g (Function.update ρ b p) ν * B₁ η₁ ν σ₁) * A₂ η₂ ρ σ₂ else 0))
          = ∑ ρ : SharedBondConfig bondDim, ∑ ν : SharedBondConfig bondDim,
              (if ρ b = q then g (Function.update ρ b p) ν else 0)
                * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ := by
        refine Finset.sum_congr rfl ?_
        intro ρ _
        by_cases hρ : ρ b = q
        · simp only [if_pos hρ]
          rw [Finset.sum_mul]
        · simp [if_neg hρ]
      rw [stepB]
      exact Finset.sum_comm
    -- Rewrite the `B`-side as a bilinear form with coefficient `cRHS`.
    have hRHS : (∑ μ : SharedBondConfig bondDim,
          (if μ b = p then B₁ η₁ μ σ₁ * B₂ η₂ (Function.update μ b q) σ₂ else 0))
        = ∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ν b = p then g ρ (Function.update ν b q) else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ := by
      refine Finset.sum_congr rfl ?_
      intro ν _
      by_cases hν : ν b = p
      · simp only [if_pos hν]
        rw [hg2 η₂ (Function.update ν b q) σ₂, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro ρ _; ring
      · simp only [if_neg hν]
        rw [eq_comm, Finset.sum_eq_zero]
        intro ρ _; ring
    -- Combine: the difference of the two bilinear forms vanishes.
    rw [hLHS, hRHS] at hO
    -- Rewrite the target difference-of-coefficients sum as the bilinear difference.
    rw [show (∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
          ((if ρ b = q then g (Function.update ρ b p) ν else 0)
            - (if ν b = p then g ρ (Function.update ν b q) else 0))
            * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂)
        = (∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ρ b = q then g (Function.update ρ b p) ν else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂)
          - ∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ν b = p then g ρ (Function.update ν b q) else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ from ?_]
    · rw [hO, sub_self]
    · rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro ν _
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro ρ _
      ring

open scoped Classical in
/-- The bond gauge is a nonzero scalar multiple of the identity. Iterating the
master per-bond constraint over all shared bonds forces `g` to vanish off the
diagonal and to be constant along it; invertibility (`g * g' = 1`) makes the
constant nonzero.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. The paper packages this as
the statement that the residual gauges `Z`, `U`, `W` on three leg pairs are each
scalar. -/
theorem bondGauge_scalar_of_master
    [Nonempty (SharedBondConfig bondDim)]
    (g g' : Matrix (SharedBondConfig bondDim) (SharedBondConfig bondDim) ℂ)
    (hgg' : g * g' = 1)
    (hmaster : ∀ (b : Bond) (p q : bondDim b) (ν ρ : SharedBondConfig bondDim),
      (if ρ b = q then g (Function.update ρ b p) ν else 0) =
        (if ν b = p then g ρ (Function.update ν b q) else 0)) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ μ ν : SharedBondConfig bondDim,
      g μ ν = lam * (if μ = ν then 1 else 0) := by
  classical
  -- `g` vanishes whenever the configurations differ at some bond.
  have hoffdiag : ∀ (b : Bond) (μ ν : SharedBondConfig bondDim),
      μ b ≠ ν b → g μ ν = 0 := by
    intro b μ ν hne
    have h := hmaster b (μ b) (μ b) ν μ
    rw [if_pos rfl, Function.update_eq_self] at h
    rw [if_neg (fun hh => hne hh.symm)] at h
    exact h
  have hdiag : ∀ μ ν : SharedBondConfig bondDim, μ ≠ ν → g μ ν = 0 := by
    intro μ ν hne
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hne
    exact hoffdiag b μ ν hb
  -- The diagonal value is invariant under changing a single bond coordinate.
  have hconst1 : ∀ (b : Bond) (q : bondDim b) (ν : SharedBondConfig bondDim),
      g ν ν = g (Function.update ν b q) (Function.update ν b q) := by
    intro b q ν
    have h := hmaster b (ν b) q ν (Function.update ν b q)
    rw [Function.update_self, if_pos rfl] at h
    rw [Function.update_idem, Function.update_eq_self] at h
    rw [if_pos rfl] at h
    exact h
  -- Diagonal values agree whenever configurations agree off a finite bond set.
  have hagree : ∀ (s : Finset Bond) (μ ν : SharedBondConfig bondDim),
      (∀ b, b ∉ s → μ b = ν b) → g μ μ = g ν ν := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro μ ν hagree
        have : μ = ν := by
          funext b; exact hagree b (Finset.notMem_empty b)
        rw [this]
    | insert b s hbs ih =>
        intro μ ν hagree
        have hstep : g ν ν = g (Function.update ν b (μ b)) (Function.update ν b (μ b)) :=
          hconst1 b (μ b) ν
        have hrest : ∀ c, c ∉ s → μ c = (Function.update ν b (μ b)) c := by
          intro c hc
          by_cases hcb : c = b
          · subst hcb; rw [Function.update_self]
          · rw [Function.update_of_ne hcb]
            exact hagree c (by simp [Finset.mem_insert, hcb, hc])
        rw [hstep]
        exact ih μ (Function.update ν b (μ b)) hrest
  let μ₀ : SharedBondConfig bondDim := Classical.arbitrary (SharedBondConfig bondDim)
  let lam : ℂ := g μ₀ μ₀
  have hdiagconst : ∀ μ : SharedBondConfig bondDim, g μ μ = lam :=
    fun μ => hagree Finset.univ μ μ₀ (fun b hb => absurd (Finset.mem_univ b) hb)
  -- `g` is `lam` on the diagonal and `0` off it.
  have hform : ∀ μ ν : SharedBondConfig bondDim, g μ ν = lam * (if μ = ν then 1 else 0) := by
    intro μ ν
    by_cases h : μ = ν
    · subst h; rw [if_pos rfl, mul_one]; exact hdiagconst μ
    · rw [if_neg h, mul_zero]; exact hdiag μ ν h
  -- Invertibility forces `lam ≠ 0`.
  have hlam : lam ≠ 0 := by
    intro hlam0
    have hone : (g * g') μ₀ μ₀ = 1 := by rw [hgg']; simp
    rw [Matrix.mul_apply] at hone
    have hzero : (∑ ν, g μ₀ ν * g' ν μ₀) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro ν _
      rw [hform μ₀ ν, hlam0, zero_mul, zero_mul]
    rw [hzero] at hone
    exact one_ne_zero hone.symm
  exact ⟨lam, hlam, hform⟩

/-! ### Main comparison theorem -/

/-- The substantive case of the generalized two-injective comparison, where every
shared virtual bond carries a nonempty index space (so the configuration family
is nonempty).

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`.

The fully contracted identity supplies a bond gauge `g` with `A₁ = g · B₁` and
`B₂ = g · A₂` (`exists_bondGauge_of_fullContraction`). Substituting both gauge
equations into each one-leg-open contraction (`sameOpenBondContraction`) and
separating the two injective families `B₁` and `A₂` yields the master per-bond
constraint `bondGauge_master_constraint`. Iterating that constraint over all
shared bonds forces `g` to be a nonzero scalar multiple of the identity
(`bondGauge_scalar_of_master`), which is exactly the source statement that the
residual gauges on the freed leg groups are scalar. Reinserting `g = lam · 1`
into the gauge equations gives `A₁ = lam · B₁` and `A₂ = lam⁻¹ · B₂`. -/
theorem two_injective_tensor_insertion_comparison_core
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty Bond] [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hB₁ : IsTwoBlockInjective B₁) (hB₂ : IsTwoBlockInjective B₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂)
    (hbond : ∀ b, Nonempty (bondDim b)) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  classical
  haveI : Nonempty (SharedBondConfig bondDim) := Classical.nonempty_pi.mpr hbond
  -- The bond gauge from operator-Schmidt uniqueness.
  obtain ⟨g, g', hgg', hg1, hg2⟩ :=
    exists_bondGauge_of_fullContraction A₁ B₁ A₂ B₂ hA₁ hA₂ hB₁ hB₂
      (fullContraction_eq A₁ B₁ A₂ B₂ hinsert)
  -- Config-indexed independence of the inner families.
  have hB₁c := hB₁.config_linearIndependent
  have hA₂c := hA₂.config_linearIndependent
  -- The master per-bond constraint, then scalar-diagonality of the gauge.
  have hmaster := bondGauge_master_constraint A₁ B₁ A₂ B₂ g hg1 hg2 hB₁c hA₂c hinsert
  obtain ⟨lam, hlam, hform⟩ := bondGauge_scalar_of_master g g' hgg' hmaster
  refine ⟨lam, hlam, ?_, ?_⟩
  · -- A₁ = lam • B₁.
    intro η₁ μ σ₁
    rw [hg1 η₁ μ σ₁]
    rw [Finset.sum_congr rfl (fun ν _ => by rw [hform μ ν])]
    rw [Finset.sum_eq_single μ]
    · rw [if_pos rfl, mul_one]
    · intro ν _ hν
      rw [if_neg (fun hh => hν hh.symm), mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- A₂ = lam⁻¹ • B₂, equivalently B₂ = lam • A₂.
    intro η₂ ν σ₂
    have hB₂eq : B₂ η₂ ν σ₂ = lam * A₂ η₂ ν σ₂ := by
      rw [hg2 η₂ ν σ₂]
      rw [Finset.sum_congr rfl (fun μ _ => by rw [hform μ ν])]
      rw [Finset.sum_eq_single ν]
      · rw [if_pos rfl, mul_one]
      · intro μ _ hμ
        rw [if_neg hμ, mul_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hlam, mul_comm]
    rw [mul_comm] at hB₂eq
    exact hB₂eq

/-- **Generalized two-injective-tensor comparison.**

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1068--1203 of Papers/1804.04964/paper_normal.tex.

This is the source comparison theorem in an abstract form with nonempty
spectator external boundary spaces; the statement in the paper is recovered by
taking these spaces to be one-point spaces. If `A₁,A₂,B₁,B₂` are injective
tensors joined by a finite nonempty family of shared virtual bonds, and
inserting an arbitrary matrix on any shared bond gives the same two-tensor
coefficient for the `A`-pair and the `B`-pair, then there is a nonzero scalar
`λ` such that `A₁ = λ B₁` and `A₂ = λ⁻¹ B₂`.

When the shared-bond configuration family is nonempty the result is the
substantive case `two_injective_tensor_insertion_comparison_core`: the fully
contracted identity yields a bond gauge that the one-leg-open contractions force
to be a nonzero scalar multiple of the identity, giving $A_1=\lambda B_1$ and
$A_2=\lambda^{-1}B_2$ (arXiv:1804.04964, Section 3, lines 1157--1204). The
single-shared-bond specialization is `two_injective_tensor_insertion_comparison_singletonBond`.
When some shared bond carries an empty index space the configuration family is
empty and the conclusion holds vacuously
(`twoBlockReciprocalScalarProportional_of_isEmpty_config`). -/
theorem two_injective_tensor_insertion_comparison
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty Bond] [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hB₁ : IsTwoBlockInjective B₁) (hB₂ : IsTwoBlockInjective B₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  classical
  -- If some shared bond is empty, the configuration family is empty and the
  -- conclusion is vacuous (the source uses nonzero-dimensional bonds).
  by_cases hcfg : Nonempty (SharedBondConfig bondDim)
  · -- All bonds are nonempty; this is the substantive case.
    have hbond : ∀ b, Nonempty (bondDim b) := Classical.nonempty_pi.mp hcfg
    exact two_injective_tensor_insertion_comparison_core
      A₁ B₁ A₂ B₂ hA₁ hA₂ hB₁ hB₂ hinsert hbond
  · exact twoBlockReciprocalScalarProportional_of_isEmpty_config A₁ B₁ A₂ B₂
      (not_nonempty_iff.mp hcfg)

/-! ### One vertex against its complement -/

/-- **One-vertex versus complement comparison.**

Source: arXiv:1804.04964, Section 3, immediately after Lemma
inj_equal_tensors_2, lines 1205--1210 of
Papers/1804.04964/paper_normal.tex.

After the edge gauges have been absorbed into the second PEPS tensor family,
the source blocks one vertex against its complement. The post-absorption
insertion equality arXiv:1804.04964, eq:inj_equal_edge, supplies equality of
all one-bond insertions for this two-block pair. Applying Lemma
inj_equal_tensors_2 then gives scalar proportionality of the selected vertex
tensor with its modified counterpart.

This theorem records precisely that final local use of the generalized
two-injective comparison in an abstract form with nonempty spectator external
boundary spaces: the selected vertex is the first block and its complement is
the second block. -/
theorem one_vertex_complement_comparison
    {ExternalVertex ExternalComplement PhysicalVertex PhysicalComplement : Type*}
    [Nonempty Bond] [Nonempty ExternalVertex] [Nonempty ExternalComplement]
    (Avertex Bvertex : TwoBlockTensor bondDim ExternalVertex PhysicalVertex)
    (Acomplement Bcomplement :
      TwoBlockTensor bondDim ExternalComplement PhysicalComplement)
    (hAvertex : IsTwoBlockInjective Avertex)
    (hAcomplement : IsTwoBlockInjective Acomplement)
    (hBvertex : IsTwoBlockInjective Bvertex)
    (hBcomplement : IsTwoBlockInjective Bcomplement)
    (hinsert :
      SameTwoBlockInsertions Avertex Bvertex Acomplement Bcomplement) :
    ∃ c : ℂ, c ≠ 0 ∧ TwoBlockScalarProportional Avertex Bvertex c := by
  rcases two_injective_tensor_insertion_comparison
      Avertex Bvertex Acomplement Bcomplement
      hAvertex hAcomplement hBvertex hBcomplement hinsert with
    ⟨c, hc_ne, hvertex, _hcomplement⟩
  exact ⟨c, hc_ne, hvertex⟩

end PEPS
end TNLean
