/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import TNLean.Channel.Wigner.Upstream.Unitary

/-!
# Transition probability on complex projective space

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

For two rays `p, q` in the complex projective space `ℙ ℂ E` of a complex
inner-product space `E`, the **transition probability** is the
phase-invariant quadratic form

  `transProb p q = ‖⟪p.rep, q.rep⟫‖² / (‖p.rep‖² · ‖q.rep‖²)`,

the squared overlap of the two rays normalised to representative norms. On
normalised representatives this is the Born weight `‖⟪ψ, φ⟫‖²`; the
normalisation makes it independent of the chosen representatives, hence a
genuine function of the projective points.

This file delivers the transition-probability API plus the **forward
(realisability) direction** of the Wigner / Fubini–Study rigidity
correspondence:

* `transProbVec` — the vector-level form, with scaling invariance in each
  argument (`transProbVec_smul_left/right`), the bounds
  `transProbVec_nonneg`, `transProbVec_le_one`, and the diagonal
  normalisation `transProbVec_self`.
* `transProb` — the projective form, with the load-bearing
  well-definedness rewriter `transProb_mk` valid for *arbitrary* nonzero
  representatives.
* `transProb_smul_unitary` — **the forward direction**: every unitary in
  `Matrix.unitaryGroup (Fin N) ℂ`, acting on `ℂℙ^{N-1}`, preserves the
  transition probability. This is the `U(N) ⊆ transition-preservers` half
  of the rigidity correspondence.
* `transProb_eq_one_iff` / `transProb_eq_zero_iff` — the equality and
  orthogonality characterisations (coincidence and orthogonality of rays),
  the provable hooks for the converse.

## Open target (not proved here): the Wigner / Fubini–Study converse

The converse of `transProb_smul_unitary` is the **Wigner / Fubini–Study
rigidity theorem**: every transition-probability-preserving self-map of
`ℙ ℂ E` is induced by a unitary (equivalently, the isometry group of
`ℂℙⁿ` with the Fubini–Study metric is the projective unitary group
`PU(n+1)`). This is multi-session Mathlib-gap mathematics — it requires
phase-coherence bookkeeping, extraction of (semi)linearity from the
overlap data, and ruling out the antiunitary branch via the Kähler complex
structure (over ℂ, transition-probability preservation alone admits both
the unitary and antiunitary classes; the holomorphic / Kähler structure
selects the unitary one). It is **not** stated here as an axiom or a
`sorry`; this file is the foundation on which it will eventually be stated.

## Provenance

Staged as upstream Mathlib material. All declarations live under
`namespace Projectivization` with no `CsdLean4`-namespace prefix; the
`CsdLean4/Mathlib/...` location is the only staging signal. Intended
location: `Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean`.


## TNLean adaptation provenance

Adapted from `zblore/csd-lean4` at commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06` under the Apache License 2.0.
Original source path:
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean`.

The adaptation replaces the full Fubini--Study topology, Haar, measure, and
continuity import by the reduced unitary bridge and rewrites only the
action-on-`mk` proof for Mathlib 4.32's projectivization action API.

## Tags

projectivization, transition probability, Fubini-Study, Wigner theorem,
unitary group, complex projective space
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization ComplexOrder
open Matrix

namespace Projectivization

/-! ## Vector-level transition probability -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The vector-level transition probability of two vectors `ψ, φ` in a
complex inner-product space: the squared overlap normalised by the squared
norms. On unit vectors this is the Born weight `‖⟪ψ, φ⟫‖²`. The
inner-product orientation is Mathlib's: `inner ℂ ψ φ` is conjugate-linear
in `ψ` and linear in `φ`; the form is insensitive to this choice. -/
noncomputable def transProbVec (ψ φ : E) : ℝ :=
  ‖(inner ℂ ψ φ : ℂ)‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2)

/-- Scaling the first argument by a nonzero scalar leaves `transProbVec`
unchanged: the `‖c‖²` introduced in the numerator (via `inner_smul_left`,
the conjugate factor having equal norm) cancels the one in the
denominator. -/
lemma transProbVec_smul_left {c : ℂ} (hc : c ≠ 0) (ψ φ : E) :
    transProbVec (c • ψ) φ = transProbVec ψ φ := by
  unfold transProbVec
  rw [inner_smul_left, norm_smul, norm_mul, mul_pow, RCLike.norm_conj, mul_pow]
  have : ‖c‖ ^ 2 ≠ 0 := by positivity
  field_simp

/-- Scaling the second argument by a nonzero scalar leaves `transProbVec`
unchanged. -/
lemma transProbVec_smul_right {c : ℂ} (hc : c ≠ 0) (ψ φ : E) :
    transProbVec ψ (c • φ) = transProbVec ψ φ := by
  unfold transProbVec
  rw [inner_smul_right, norm_mul, norm_smul, mul_pow, mul_pow]
  have : ‖c‖ ^ 2 ≠ 0 := by positivity
  field_simp

/-- `transProbVec` is nonnegative. -/
lemma transProbVec_nonneg (ψ φ : E) : 0 ≤ transProbVec ψ φ := by
  unfold transProbVec; positivity

/-- `transProbVec` is bounded by `1`, by Cauchy–Schwarz
(`norm_inner_le_norm`). The degenerate cases `ψ = 0` or `φ = 0` make the
denominator zero, so the quotient is `0 ≤ 1` by the `div_zero`
convention. -/
lemma transProbVec_le_one (ψ φ : E) : transProbVec ψ φ ≤ 1 := by
  unfold transProbVec
  rcases eq_or_ne ψ 0 with h | h
  · simp [h]
  rcases eq_or_ne φ 0 with h' | h'
  · simp [h']
  rw [div_le_one (by positivity)]
  calc ‖(inner ℂ ψ φ : ℂ)‖ ^ 2
      ≤ (‖ψ‖ * ‖φ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ψ φ) 2
    _ = ‖ψ‖ ^ 2 * ‖φ‖ ^ 2 := by ring

/-- The diagonal value is `1` for any nonzero vector: `⟪ψ, ψ⟫ = ‖ψ‖²`. -/
lemma transProbVec_self {ψ : E} (h : ψ ≠ 0) : transProbVec ψ ψ = 1 := by
  unfold transProbVec
  have hnorm : ‖(inner ℂ ψ ψ : ℂ)‖ = ‖ψ‖ ^ 2 := by
    rw [@inner_self_eq_norm_sq_to_K ℂ, norm_pow]; simp
  rw [hnorm]
  have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr h
  field_simp

/-! ## Projective transition probability -/

/-- The **transition probability** between two projective points, defined
on their canonical (nonzero) representatives `Projectivization.rep`. The
well-definedness across the choice of representative is `transProb_mk`. -/
noncomputable def transProb (p q : ℙ ℂ E) : ℝ :=
  transProbVec p.rep q.rep

/-- A canonical representative of `mk v hv` is a nonzero scalar multiple of
`v`. -/
lemma rep_mk_eq_smul {v : E} (hv : v ≠ 0) :
    ∃ a : ℂˣ, (Projectivization.mk ℂ v hv).rep = a • v := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ v hv).rep v
      (Projectivization.rep_nonzero _) hv).mp (by rw [Projectivization.mk_rep])
  exact ⟨a, ha.symm⟩

/-- **Well-definedness rewriter.** For arbitrary nonzero representatives
`v, w`, the projective transition probability equals the vector-level form
on `v, w`. The canonical reps differ from `v, w` by nonzero scalars, which
the scaling-invariance lemmas absorb. -/
lemma transProb_mk {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    transProb (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw)
      = transProbVec v w := by
  unfold transProb
  obtain ⟨a, ha⟩ := rep_mk_eq_smul hv
  obtain ⟨b, hb⟩ := rep_mk_eq_smul hw
  rw [ha, hb, Units.smul_def, Units.smul_def,
      transProbVec_smul_left (c := (a : ℂ)) (by exact_mod_cast a.ne_zero),
      transProbVec_smul_right (c := (b : ℂ)) (by exact_mod_cast b.ne_zero)]

/-! ## Forward (realisability) direction: `U(N) ⊆` transition-preservers -/

variable {N : ℕ}

/-- Unitary inner-product preservation on `EuclideanSpace ℂ (Fin N)`:
`⟪U v, U w⟫ = ⟪v, w⟫` for `U` a matrix-unitary, where the action is the
`toEuclideanLin` of the matrix. Routes through
`EuclideanSpace.inner_eq_star_dotProduct`, `star_mulVec`, and the unitary
relation `Uᴴ * U = 1`. -/
lemma inner_toEuclideanLin_unitary
    (U : Matrix.unitaryGroup (Fin N) ℂ) (v w : EuclideanSpace ℂ (Fin N)) :
    (inner ℂ (Matrix.toEuclideanLin U.val v)
        (Matrix.toEuclideanLin U.val w) : ℂ)
      = inner ℂ v w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  show (U.val *ᵥ w.ofLp) ⬝ᵥ star (U.val *ᵥ v.ofLp) = w.ofLp ⬝ᵥ star v.ofLp
  rw [Matrix.star_mulVec, dotProduct_comm (U.val *ᵥ w.ofLp), ← dotProduct_mulVec,
      mulVec_mulVec, show (U.val)ᴴ * U.val = 1 from Unitary.coe_star_mul_self U,
      one_mulVec, dotProduct_comm]

/-- The unitary action sends `mk v` to `mk (toEuclideanLin U v)`. -/
lemma smul_mk_eq_mk_toEuclideanLin
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    U • (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (Matrix.toEuclideanLin U.val v)
          (Matrix.UnitaryGroup.toEuclideanLin_unitary_apply_ne_zero U hv) := by
  change Matrix.UnitaryGroup.toEuclideanLinearEquivHom U •
      Projectivization.mk ℂ v hv = _
  rw [Projectivization.smul_mk]
  rfl

/-- **Forward (realisability) direction.** Every unitary in
`Matrix.unitaryGroup (Fin N) ℂ`, acting on `ℂℙ^{N-1}`, preserves the
transition probability:

  `transProb (U • p) (U • q) = transProb p q`.

This is the `U(N) ⊆ transition-preservers` half of the Wigner /
Fubini–Study rigidity correspondence. The converse (a
transition-preserving self-map is induced by a unitary) is the open target
documented in the module header. -/
theorem transProb_smul_unitary
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    transProb (U • p) (U • q) = transProb p q := by
  -- Reduce both points to `mk` of their canonical reps.
  conv_lhs => rw [← p.mk_rep, ← q.mk_rep]
  rw [smul_mk_eq_mk_toEuclideanLin U p.rep_nonzero,
      smul_mk_eq_mk_toEuclideanLin U q.rep_nonzero,
      transProb_mk]
  -- Now `transProbVec (U p.rep) (U q.rep) = transProb p q` by unitary
  -- preservation of inner products and norms.
  unfold transProb transProbVec
  rw [inner_toEuclideanLin_unitary U p.rep q.rep]
  congr 1
  -- denominator: ‖U v‖ = ‖v‖ via ‖x‖² = re ⟪x,x⟫ and inner preservation.
  have hnorm : ∀ x : EuclideanSpace ℂ (Fin N),
      ‖(Matrix.toEuclideanLin U.val) x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ,
        inner_toEuclideanLin_unitary U x x]
  rw [hnorm, hnorm]

/-! ## Equality and orthogonality characterisations (converse hooks) -/

/-- **Coincidence characterisation.** The transition probability is `1` iff
the two projective points are equal. The forward implication is the
Cauchy–Schwarz equality case (`norm_inner_eq_norm_iff`): saturation forces
the representatives to be parallel, hence the same projective point. -/
theorem transProb_eq_one_iff (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    transProb p q = 1 ↔ p = q := by
  unfold transProb transProbVec
  have hp : p.rep ≠ 0 := p.rep_nonzero
  have hq : q.rep ≠ 0 := q.rep_nonzero
  have hpn : (0:ℝ) < ‖p.rep‖ := norm_pos_iff.mpr hp
  have hqn : (0:ℝ) < ‖q.rep‖ := norm_pos_iff.mpr hq
  have hden : (0:ℝ) < ‖p.rep‖ ^ 2 * ‖q.rep‖ ^ 2 := by positivity
  rw [div_eq_one_iff_eq (ne_of_gt hden)]
  constructor
  · intro h
    -- ‖⟪p,q⟫‖² = ‖p‖²‖q‖²  ⇒  ‖⟪p,q⟫‖ = ‖p‖‖q‖  (both sides nonneg)
    have hnorm : ‖(inner ℂ p.rep q.rep : ℂ)‖ = ‖p.rep‖ * ‖q.rep‖ := by
      have hsq : ‖(inner ℂ p.rep q.rep : ℂ)‖ ^ 2 = (‖p.rep‖ * ‖q.rep‖) ^ 2 := by
        rw [h]; ring
      nlinarith [norm_nonneg (inner ℂ p.rep q.rep : ℂ),
        mul_nonneg hpn.le hqn.le, hsq]
    obtain ⟨r, hr0, hr⟩ := (norm_inner_eq_norm_iff hp hq).mp hnorm
    -- q.rep = r • p.rep with r ≠ 0 ⇒ mk q.rep = mk p.rep ⇒ p = q
    have hmk : Projectivization.mk ℂ q.rep hq = Projectivization.mk ℂ p.rep hp :=
      (Projectivization.mk_eq_mk_iff' ℂ q.rep p.rep hq hp).mpr ⟨r, hr.symm⟩
    rw [q.mk_rep, p.mk_rep] at hmk
    exact hmk.symm
  · intro h
    subst h
    have hnorm : ‖(inner ℂ p.rep p.rep : ℂ)‖ = ‖p.rep‖ ^ 2 := by
      rw [@inner_self_eq_norm_sq_to_K ℂ, norm_pow]; simp
    rw [hnorm]; ring

/-- **Orthogonality characterisation.** The transition probability is `0`
iff the representatives are orthogonal. Since both representatives are
nonzero, the denominator is nonzero, so the quotient vanishes iff the
numerator does, i.e. iff `‖⟪p.rep, q.rep⟫‖ = 0`. -/
theorem transProb_eq_zero_iff (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    transProb p q = 0 ↔ (inner ℂ p.rep q.rep : ℂ) = 0 := by
  unfold transProb transProbVec
  have hp : p.rep ≠ 0 := p.rep_nonzero
  have hq : q.rep ≠ 0 := q.rep_nonzero
  have hden : ‖p.rep‖ ^ 2 * ‖q.rep‖ ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff]
  simp only [hden, or_false, pow_eq_zero_iff (n := 2) (by norm_num), norm_eq_zero]

end Projectivization
