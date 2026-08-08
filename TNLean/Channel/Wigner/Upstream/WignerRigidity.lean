/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import TNLean.Channel.Wigner.Upstream.TransitionProbability

/-!
# Step (1) of the Wigner / Fubini–Study rigidity converse

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

This file builds **STEP (1)** of the Wigner / Fubini–Study rigidity converse on
top of the transition-probability foundation
(`Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean`). It
delivers:

* `TransProbPreserving f` — the predicate that a self-map `f : ℙ ℂ E → ℙ ℂ E`
  preserves the transition probability `transProb`;
* `TransProbPreserving.injective` — such a map is injective (a transition
  probability `1` forces coincidence, via `transProb_self` and
  `transProb_eq_one_iff`);
* `transProbPreserving_unitary` — the **realisability inclusion**: every unitary
  in `Matrix.unitaryGroup (Fin N) ℂ`, acting on `ℂℙ^{N-1}`, is
  `TransProbPreserving`. This is the `U(N) → TransProbPreserving` map whose
  surjectivity-up-to-phase is the deferred Wigner statement;
* `TransProbPreserving.orthogonal` / `.inner_rep_eq_zero_iff` — preservation of
  orthogonality, both as a `transProb = 0` face and an `inner = 0` face;
* `TransProbPreserving.pairwise_orthogonal` and
  `orthonormalBasis_pairwise_orthogonal` — the "orthonormal frame ↦ pairwise
  orthogonal family" content: an orthonormal basis induces a pairwise-orthogonal
  projective family, and a `TransProbPreserving` map sends it to one.

## Steps (2a) and (2b) (proved here): image frame and candidate unitary

* **(2a) The image orthonormal frame.** `imageVec` is the unit-normalised
  canonical representative of the image ray `f (mk (b i))`; `imageVec_norm`,
  `imageVec_ne_zero`, and `imageVec_orthonormal` (off-diagonals transported from
  the source frame through `TransProbPreserving.inner_rep_eq_zero_iff`) make it
  an orthonormal family, packaged as `imageOrthonormalBasis` (an orthonormal
  family of cardinality `N` in `EuclideanSpace ℂ (Fin N)`, `finrank = N`, spans).
  `mk_imageOrthonormalBasis` records that the `i`-th image ONB vector spans the
  image ray: `mk (imageOrthonormalBasis i) = f (mk (b i))`.
* **(2b) The candidate unitary.** `candidateUnitary hf b` is the
  `OrthonormalBasis.equiv` change of frame `b ↦ imageOrthonormalBasis hf b`
  along the identity reindexing of `Fin N`, a genuine `≃ₗᵢ[ℂ]`. The headline
  `candidateUnitary_agrees_on_basis` is the agreement on the basis points:
  `mk (candidateUnitary hf b (b i)) = f (mk (b i))` for every `i`.

## Step (2c) frame reduction (proved here): the reduced map fixes the basis

* **The projective image of an isometry equiv.** `projMap e` is the
  `Projectivization.map` of a linear isometry equivalence `e`'s underlying
  injective linear map. It preserves the transition probability
  (`transProb_projMap`, via the vector-level `transProbVec_linearIsometryEquiv`
  from `e.inner_map_map` and `e.norm_map`), hence is `TransProbPreserving`
  (`projMap_transProbPreserving`). `TransProbPreserving.comp` gives closure of
  the predicate under composition. (All general in `E`.)
* **The frame-reduced map.** `reducedMap hf b := projMap (candidateUnitary hf b).symm ∘ f`
  is `TransProbPreserving` (`reducedMap_transProbPreserving`) and **fixes every
  source basis ray** (`reducedMap_fixes_basis`):
  `reducedMap hf b (mk (b i)) = mk (b i)` for every `i`. The proof rewrites
  `f (mk (b i))` backward via `candidateUnitary_agrees_on_basis`, pushes the
  inverse candidate unitary's projective map through `projMap_mk`, and applies
  `LinearIsometryEquiv.symm_apply_apply`.

This reduces the open converse to the **Wigner normal-form problem** for the
reduced map, addressed in Stages 1–3 below.

## Stage 1 (proved here): moduli preservation

* `TransProbPreserving.transProb_of_fixed` — a preserving map fixing a point `q`
  preserves the transition probability from every point to `q`.
* `transProb_srcPoint` — the transition probability to the `i`-th basis ray is the
  normalised squared modulus of the `i`-th coordinate `b.repr ψ i`.
* `reducedMap_coord_modulus` — **Stage 1 headline**: writing
  `reducedMap hf b (mk ψ) = mk φ`, the modulus profile
  `‖b.repr φ i‖² / ‖φ‖² = ‖b.repr ψ i‖² / ‖ψ‖²` is preserved coordinate-by-coordinate.

## Stage 2 (proved here): the two-level phase normal form

* `add_basis_ne_zero`, `repr_eq_pair_of_support`, `mk_eq_two_level_of_profile` —
  support and reconstruction infrastructure.
* `reducedMap_two_level_normal_form` — **Stage 2 headline**: for distinct
  `i₀ ≠ i`, `reducedMap hf b (mk (b i₀ + b i)) = mk (b i₀ + ε • b i)` for a
  unimodular `ε`. The image ray is pinned up to the single phase `ε`.

Both stages are derived from `TransProbPreserving` alone; **no ℂ-linearity is
assumed** anywhere.

## The antiunitary witness (proved here): `conjProj`

`conjProj` is coordinatewise complex conjugation as a ray map
(`conjVec` on representatives), a **concrete** `TransProbPreserving` inhabitant
(`conjProj_transProbPreserving`) of the **antiunitary** class: `conjVec` is
conjugate-linear (`conjVec_smul : conjVec (c • ψ) = conj c • conjVec ψ`), not the
underlying map of any `≃ₗᵢ[ℂ]`. This makes the eventual dichotomy non-vacuous on
the antiunitary side. Built on the conjugation inner/norm identities
`conjVec_inner : ⟪conjVec u, conjVec v⟫ = conj ⟪u, v⟫` and
`conjVec_norm : ‖conjVec ψ‖ = ‖ψ‖`.

## Stage 3 piece 1 (proved here): the diagonal-phase reduction

`diagUnitary b ε hε` is the diagonal-in-`b` isometry with unit-modulus phases
`ε` (via the `ε`-scaled orthonormal basis, `scaledBasis`); `twoLevelPhase`
extracts the Stage-2 phases anchored at `ε i₀ := 1`; and
`diagReducedMap hf b i₀ := projMap D⁻¹ ∘ reducedMap hf b` (with `D` built from
those phases) is `TransProbPreserving` (`diagReducedMap_transProbPreserving`),
fixes every basis ray (`diagReducedMap_fixes_basis`), **and** fixes the two-level
rays `mk (b i₀ + b i)` for every `i ≠ i₀` (`diagReducedMap_fixes_two_level`).
This is the setup the cocycle step (pieces 2–3) consumes. `D` is constructed
*from* the extracted phases, not posited of `f`: **no ℂ-linearity is assumed.**

## Stage 3 piece 2 (proved here): the cocycle coboundary structure

On the diagonally reduced map `g := diagReducedMap hf b i₀` the coordinate
overlap algebra pins the pairwise relative phases up to sign:

* `diagReducedMap_coord_modulus` — Stage-1 moduli transported to `g`.
* `diagReducedMap_two_level_relphase` — the anchored real-part relation
  `Re(d̄_{i₀} d_i)/‖φ‖² = Re(c̄_{i₀} c_i)/‖ψ‖²`.
* `diagReducedMap_fixes_three_level` (**W4**) — the equal triple ray
  `mk (b i₀ + b i + b j)` is fixed, via moduli + saturation
  (`norm_eq_re_imp_eq`, `eq_of_re_conj_mul_eq`) + `repr_eq_triple_of_support`.
* `diagReducedMap_fixes_two_level_general` (**W4**) — the non-anchored ray
  `mk (b i + b j)` (`i, j ≠ i₀`) is fixed, using the triple as a probe.
* `diagReducedMap_pairwise_relphase` (**W4**) — the unconditional pairwise
  real-part relation for all `i, j ≠ i₀`, the full **coboundary structure**.

Every probe is real-coordinate, so the fixings are consistent with **both** the
unitary and antiunitary branches: piece 2 establishes the coboundary structure,
**not** the global sign (that is piece 3). **No ℂ-linearity is assumed.**

## Stage 3 piece 3 (W5, proved here): complex probe, reconstruction, dichotomy

The converse of the realisability inclusion `transProbPreserving_unitary` is the
**Wigner / Fubini–Study rigidity theorem**:

> `theorem (informal): TransProbPreserving f → (∃ U : Matrix.unitaryGroup (Fin N) ℂ,`
> `  f = fun p => U • p) ∨ (∃ antiunitary A, f = A-ray-action)`

equivalently, the isometry group of `ℂℙⁿ` with the Fubini–Study metric is the
projective **semi**-unitary group. It is **not** stated here as an axiom or a
`sorry`.

**Scope note (CL-024 audit, 2026-08-06; updated same day).** This module
proves the EXISTENCE clause of the Wigner/Bargmann theorem. The up-to-phase
**uniqueness** clause is formalized in companion modules: matrix vocabulary in
`PhaseRigidity.lean` (`exists_unit_smul_of_smul_eq_smul`, the `U(N) → PU(N)`
circle kernel — predating the audit, which missed it) and this theorem's own
`projMap`/`conjProj` vocabulary in `WignerUniqueness.lean`
(`exists_unit_smul_of_projMap_eq`, `exists_unit_smul_of_projMap_conjProj_eq`,
via the involution `conjProj_conjProj`). The branch-EXCLUSIVITY facts (a map
cannot be both unitary- and antiunitary-induced, `2 ≤ N`) live downstream:
`Projectivization.conjProj_ne_projMap` / `smul_action_not_antiunitary`
(`Empirical/CSD/Gates/WignerDischarge.lean`) and the Bargmann-invariant
discriminator (`Projectivization/Bargmann.lean`, `LF4/BargmannSelection.lean`).
Cite those modules, not this one, for uniqueness/exclusivity claims. Piece 3 (W5) delivers the branch-distinguishing machinery:

* `two_level_imrelphase_of_fixes` / `_flips` — the **complex `I`-probe** pins the
  *imaginary* part of the relative phase, the datum the real probes of pieces 1–2
  could not reach (fixed complex ray ⟹ `Im` preserved; flipped ⟹ `Im` negated).
* `eq_id_of_fixes_all_two_level` / `eq_bconj_of_flips_complex` — the two
  **reconstruction** directions: a map fixing all basis + real + complex two-level
  rays is the **identity** on rays; one that flips the complex rays is
  coordinatewise **conjugation** in `b` (`bConjVec`). ℂ-linearity is an OUTPUT.
* `diagReducedMap_complex_probe` — the complex probe ray `mk (b i₀ + I • b i)` is
  *not* conjugation-invariant, so the diagonally reduced map sends it to itself
  (`+`) or to `mk (b i₀ − I • b i)` (`−`): the per-pair `± I` branch datum.
* `diagReducedMap_dichotomy_of_complexSign` — the **assembly**: given the global
  complex-sign closure (all complex two-level rays fixed, or all flipped), the
  reduced map is globally the identity, or globally `bConjVec` conjugation. Both
  branches genuine; the antiunitary branch is not dropped.

**W6 (DONE).** The unconditional `wigner_rigidity` **is** stated and proved here.
The global-sign closure — the per-pair `± I` datum is consistent across all pairs
(fixes-all ∨ flips-all) — is discharged in `diagReducedMap_complexSign_closure`
via the non-anchored per-pair dichotomy (`diagReducedMap_complex_probe_general`),
the master witness `masterVec`, the abstract Gram-triple core `sign_link_core`,
order swap by injectivity, and index linking; the unconditional
`diagReducedMap_dichotomy` and the headline `wigner_rigidity` (unitary ∨
antiunitary, ℂ-linearity an output) follow, foundational-triple only. See the
`Stage 3 complete (W6)` section at the end of this file. **Scope of "piece 2
CLOSED" (load-bearing):** piece 2 delivers the
*sign-free real-part relations* — the full pairwise data `Re(conj dᵢ·dⱼ)/‖φ‖² =
Re(conj cᵢ·cⱼ)/‖ψ‖²` (equivalently the pairwise cosines `cos(βⱼ−βᵢ)=cos(αⱼ−αᵢ)`)
for every pair, which pin the phase configuration up to global rotation AND a
single global reflection. The phrases "2-cocycle"/"coboundary structure" are
narrative labels: no formal `Complex.arg`-based additive identity
`θ(i,j)=θ(i₀,j)−θ(i₀,i)` or `H²` object is constructed, because extracting one
presupposes choosing an `arg` branch — i.e. resolving the ± reflection — which is
precisely piece 3. **Critical honesty notes (load-bearing).**

* `reducedMap_fixes_basis` does **not** make `reducedMap` the identity: the
  diagonal-phase freedom is genuine and is exactly the Stage-2 phase `ε`, pinned
  only by the Stage-3 cocycle. Do not read frame reduction as `reducedMap = id`
  nor as `f = projMap (candidateUnitary hf b)`.
* Transition-probability preservation over `ℂ` admits both the unitary and the
  antiunitary classes; the holomorphic / Kähler complex structure selects the
  unitary one. Stage 3 must *derive* ℂ-linearity from the overlap data, **not**
  assume it: a smuggled linearity hypothesis would beg the question.

## Provenance

Staged as upstream Mathlib material. All declarations live under
`namespace Projectivization` with no `CsdLean4`-namespace prefix; the
`CsdLean4/Mathlib/...` location is the only staging signal. Intended location:
`Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean`.


## TNLean adaptation provenance

Adapted from `zblore/csd-lean4` at commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06` under the Apache License 2.0.
Original source path:
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean`.

The complete upstream proof is retained. The only adaptation in this module is
the import path to the reduced Lean 4.32 transition-probability dependency.

## Tags

projectivization, transition probability, Fubini-Study, Wigner theorem,
unitary group, complex projective space, isometry, orthogonality
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization ComplexOrder
open Matrix

namespace Projectivization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Diagonal value of the projective transition probability -/

/-- The diagonal value of the projective transition probability is `1`: any
projective point coincides with itself. Reduces to `transProbVec_self` on the
(nonzero) canonical representative via `transProb_mk`. -/
lemma transProb_self (p : ℙ ℂ E) : transProb p p = 1 := by
  conv_lhs => rw [← p.mk_rep]
  rw [transProb_mk p.rep_nonzero p.rep_nonzero, transProbVec_self p.rep_nonzero]

/-! ## The transition-probability-preserving predicate -/

/-- A self-map of `ℙ ℂ E` is **transition-probability preserving** when it
preserves `transProb` on every pair of projective points. The
realisability direction `transProbPreserving_unitary` shows every unitary
action is such a map; the converse (every such map is induced by a unitary) is
the open Wigner target documented in the module header. -/
def TransProbPreserving (f : ℙ ℂ E → ℙ ℂ E) : Prop :=
  ∀ p q, transProb (f p) (f q) = transProb p q

/-! ## Realisability inclusion: `U(N) → TransProbPreserving` -/

variable {N : ℕ}

/-- A transition-probability-preserving self-map of `ℂℙ^{N-1}` is injective: if
`f p = f q` then `transProb p q = transProb (f p) (f q) = transProb (f p) (f p)
= 1`, so `p = q` by `transProb_eq_one_iff`. (The coincidence characterisation
`transProb_eq_one_iff` is the `EuclideanSpace ℂ (Fin N)` ingredient.) -/
theorem TransProbPreserving.injective
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : TransProbPreserving f) :
    Function.Injective f := by
  intro p q hpq
  rw [← transProb_eq_one_iff, ← hf p q, hpq, transProb_self]

/-- **Realisability inclusion.** Every unitary in `Matrix.unitaryGroup (Fin N) ℂ`,
acting on `ℂℙ^{N-1}`, is transition-probability preserving. Immediate from
`transProb_smul_unitary`. This is the `U(N) → TransProbPreserving` map; the
surjectivity-up-to-phase of this map is the deferred Wigner statement. -/
theorem transProbPreserving_unitary
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    TransProbPreserving (fun p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) => U • p) :=
  fun p q => transProb_smul_unitary U p q

/-! ## The antiunitary witness `conjProj`

Over `ℂ`, transition-probability preservation admits a second class beyond the
unitary one: the **antiunitary** class, realised by complex conjugation. This
subsection builds it concretely. `conjVec` is coordinatewise complex conjugation
on `EuclideanSpace ℂ (Fin N)`, a **conjugate-linear** isometry
(`conjVec_smul` shows the semilinear scaling law `conjVec (c • ψ) = conj c • conjVec ψ`,
which is *not* the linear law of any `≃ₗᵢ[ℂ]`). Its ray map `conjProj` is
`TransProbPreserving` (`conjProj_transProbPreserving`), so the eventual
Wigner dichotomy is not vacuous on the antiunitary side. -/

/-- Coordinatewise complex conjugation on `EuclideanSpace ℂ (Fin N)`: the
conjugate-linear isometry `ψ ↦ (fun i => conj (ψ i))`. -/
noncomputable def conjVec (ψ : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun i => (starRingEnd ℂ) (ψ.ofLp i))

/-- `conjVec` acts coordinatewise: `(conjVec ψ) i = conj (ψ i)` (definitional). -/
lemma conjVec_ofLp (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (conjVec ψ).ofLp i = (starRingEnd ℂ) (ψ.ofLp i) := rfl

/-- **Conjugation inner identity.** `⟪conjVec u, conjVec v⟫ = conj ⟪u, v⟫`.
Reduces via `PiLp.inner_apply` to the coordinatewise identity
`conj(conj (u i)) * conj (v i) = conj (conj (u i) * v i)` (`RCLike.inner_apply'`,
`map_mul`, `Complex.conj_conj`). -/
lemma conjVec_inner (u v : EuclideanSpace ℂ (Fin N)) :
    (inner ℂ (conjVec u) (conjVec v) : ℂ) = (starRingEnd ℂ) (inner ℂ u v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply', RCLike.inner_apply', map_mul, conjVec_ofLp, conjVec_ofLp,
      Complex.conj_conj]

/-- **Conjugation norm identity.** `‖conjVec ψ‖ = ‖ψ‖`. Both squared norms are
the real part of the (conjugation-swapped) self inner product `conjVec_inner`;
`RCLike.conj_re` drops the conjugation on the real part. -/
lemma conjVec_norm (ψ : EuclideanSpace ℂ (Fin N)) : ‖conjVec ψ‖ = ‖ψ‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (conjVec ψ)), ← Real.sqrt_sq (norm_nonneg ψ)]
  congr 1
  rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
  have h2 : RCLike.re (inner ℂ (conjVec ψ) (conjVec ψ) : ℂ)
      = RCLike.re ((starRingEnd ℂ) (inner ℂ ψ ψ)) := by rw [conjVec_inner]
  rwa [RCLike.conj_re] at h2

/-- **Semilinearity of `conjVec`.** `conjVec (c • ψ) = conj c • conjVec ψ`. This
conjugate-linear scaling law witnesses that `conjVec` is genuinely antiunitary:
it is not the linear scaling law satisfied by any `≃ₗᵢ[ℂ]`, so `conjProj` is not
`projMap` of a complex-linear isometry equivalence. -/
lemma conjVec_smul (c : ℂ) (ψ : EuclideanSpace ℂ (Fin N)) :
    conjVec (c • ψ) = (starRingEnd ℂ) c • conjVec ψ := by
  ext i
  show (starRingEnd ℂ) ((c • ψ).ofLp i) = ((starRingEnd ℂ) c • conjVec ψ).ofLp i
  simp [conjVec_ofLp, map_mul]

/-- `conjVec` preserves nonvanishing: `‖conjVec ψ‖ = ‖ψ‖ ≠ 0`. -/
lemma conjVec_ne_zero {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) : conjVec ψ ≠ 0 := by
  rw [← norm_ne_zero_iff, conjVec_norm]; exact norm_ne_zero_iff.mpr hψ

/-- **Conjugation preserves the vector transition probability.**
`transProbVec (conjVec u) (conjVec v) = transProbVec u v`: the numerator is
fixed since `‖conj ⟪u,v⟫‖ = ‖⟪u,v⟫‖` (`conjVec_inner` + `RCLike.norm_conj`), the
denominator by `conjVec_norm`. -/
lemma conjVec_transProbVec (u v : EuclideanSpace ℂ (Fin N)) :
    transProbVec (conjVec u) (conjVec v) = transProbVec u v := by
  unfold transProbVec
  rw [conjVec_inner, RCLike.norm_conj, conjVec_norm, conjVec_norm]

/-- The **antiunitary ray map**: complex conjugation of the canonical
representative. Total and well-defined (conjugation is norm-preserving and
injective, so the image ray does not depend on representative choice up to the
scaling `conjVec_smul` absorbs). -/
noncomputable def conjProj (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  Projectivization.mk ℂ (conjVec p.rep) (conjVec_ne_zero p.rep_nonzero)

/-- **HEADLINE (antiunitary witness).** `conjProj` is `TransProbPreserving`.
Reduce both image rays to `mk (conjVec ·.rep)` via `transProb_mk`, then apply
`conjVec_transProbVec`. This exhibits a concrete `TransProbPreserving` inhabitant
of the **antiunitary** class: `conjVec` is conjugate-linear (`conjVec_smul`), not
the underlying map of any `≃ₗᵢ[ℂ]`; for `2 ≤ N` the ray-level map `conjProj` is
not `projMap` of any unitary (`conjProj_ne_projMap`, WignerDischarge — at
`N ≤ 1` the projective space has at most one point and the distinction vanishes).
The eventual Wigner dichotomy is thus non-vacuous on the antiunitary side. -/
theorem conjProj_transProbPreserving :
    TransProbPreserving (conjProj (N := N)) := by
  intro p q
  show transProb (Projectivization.mk ℂ (conjVec p.rep) _)
      (Projectivization.mk ℂ (conjVec q.rep) _) = transProb p q
  rw [transProb_mk (conjVec_ne_zero p.rep_nonzero) (conjVec_ne_zero q.rep_nonzero),
      conjVec_transProbVec]
  rfl

/-- **Ray-map identity for `conjProj` on arbitrary representatives.**
`conjProj (mk v hv) = mk (conjVec v)`. The canonical representative of `mk v hv`
is `a • v` for some nonzero `a`; `conjVec (a • v) = conj a • conjVec v`
(`conjVec_smul`), a nonzero rescaling, so both sides span the same ray. This is
the representative-independent form of `conjProj`, needed for the eventual
antiunitary assembly (Stage 3). -/
lemma conjProj_mk {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    conjProj (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (conjVec v) (conjVec_ne_zero hv) := by
  unfold conjProj
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ (Projectivization.mk ℂ v hv).rep v
    (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(starRingEnd ℂ) a, ?_⟩
  rw [← ha, conjVec_smul]

/-! ## Orthogonality preservation -/

/-- `mk`-level orthogonality rewriter: for nonzero representatives `v, w`, the
projective transition probability of `mk v`, `mk w` vanishes iff `v ⟂ w`.
Routes through `transProb_mk` and the fact that the (positive) denominator of
`transProbVec` is irrelevant to vanishing. -/
lemma transProb_mk_eq_zero_iff {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    transProb (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw) = 0
      ↔ (inner ℂ v w : ℂ) = 0 := by
  rw [transProb_mk hv hw]
  unfold transProbVec
  have hden : ‖v‖ ^ 2 * ‖w‖ ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff]
  simp only [hden, or_false, pow_eq_zero_iff (n := 2) (by norm_num), norm_eq_zero]

/-- **Orthogonality preservation (transProb face).** A transition-probability-
preserving map preserves orthogonality of projective points (read as
`transProb = 0`): the hypothesis rewrites the LHS to the RHS. -/
theorem TransProbPreserving.orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℙ ℂ E → ℙ ℂ E} (hf : TransProbPreserving f) (p q : ℙ ℂ E) :
    transProb (f p) (f q) = 0 ↔ transProb p q = 0 := by
  rw [hf p q]

/-- **Orthogonality preservation (inner-product face).** A transition-probability-
preserving self-map of `ℂℙ^{N-1}` preserves orthogonality of the canonical
representatives. Combines `.orthogonal` with the orthogonality characterisation
`transProb_eq_zero_iff` on both sides. -/
theorem TransProbPreserving.inner_rep_eq_zero_iff
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : TransProbPreserving f) (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    (inner ℂ (f p).rep (f q).rep : ℂ) = 0 ↔ (inner ℂ p.rep q.rep : ℂ) = 0 := by
  rw [← transProb_eq_zero_iff, ← transProb_eq_zero_iff, hf p q]

/-! ## Orthogonal projective families and orthonormal frames -/

/-- Orthogonality of two projective points, read off the transition
probability: `Orthogonal p q` means `transProb p q = 0` (equivalently, the
representatives are inner-product orthogonal). -/
def Orthogonal (p q : ℙ ℂ E) : Prop := transProb p q = 0

/-- **Orthogonal family preservation.** A transition-probability-preserving map
sends a pairwise-orthogonal projective family to a pairwise-orthogonal family.
Pointwise consequence of `.orthogonal`. -/
theorem TransProbPreserving.pairwise_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℙ ℂ E → ℙ ℂ E} (hf : TransProbPreserving f)
    {ι : Type*} {P : ι → ℙ ℂ E}
    (h : Pairwise (fun i j => transProb (P i) (P j) = 0)) :
    Pairwise (fun i j => transProb (f (P i)) (f (P j)) = 0) :=
  fun i j hij => (hf.orthogonal (P i) (P j)).mpr (h hij)

/-- **Orthonormal frame ↦ pairwise-orthogonal projective family.** An
orthonormal basis of `EuclideanSpace ℂ (Fin N)` induces a pairwise-orthogonal
family of projective points (distinct basis rays are orthogonal). Uses
`b.orthonormal.2` (the off-diagonal vanishing of an `Orthonormal` family) and
the `mk`-level rewriter `transProb_mk_eq_zero_iff`. Composing with
`TransProbPreserving.pairwise_orthogonal` exhibits the "orthonormal frame ↦
pairwise-orthogonal family" content at the orthogonality level. -/
theorem orthonormalBasis_pairwise_orthogonal
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Pairwise (fun i j =>
      transProb (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
        (Projectivization.mk ℂ (b j) (b.orthonormal.ne_zero j)) = 0) :=
  fun i j hij =>
    (transProb_mk_eq_zero_iff (b.orthonormal.ne_zero i) (b.orthonormal.ne_zero j)).mpr
      (b.orthonormal.2 hij)

/-! ## Step (2a): the image orthonormal frame

A `TransProbPreserving` map `f` together with a source orthonormal basis `b`
produces an orthonormal family of *image* representatives, the unit-normalised
canonical reps of the image rays `f (mk (b i))`. Pairwise orthogonality is
transported from the source frame through `inner_rep_eq_zero_iff`; the diagonal
is unit by construction. Indexed by `Fin N` in a space of `finrank = N`, the
family is an orthonormal basis. Each image ONB vector spans the image ray:
`mk (imageOrthonormalBasis i) = f (mk (b i))`. -/

variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-- The `i`-th source basis projective point `mk (b i)`. A definitional
abbreviation kept folded inside the helper lemmas; the public headlines
(`mk_imageOrthonormalBasis`, `candidateUnitary_agrees_on_basis`) restate it as
the explicit `mk ℂ (b i) (b.orthonormal.ne_zero i)`. -/
noncomputable def srcPoint
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)

/-- `srcPoint` unfolds to the explicit `mk` of the basis vector. -/
lemma srcPoint_eq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    srcPoint b i = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := rfl

/-- The unit-normalised canonical representative of the image ray
`f (mk (b i))`. Normalising the (nonzero) rep `(f (srcPoint b i)).rep` by the
real reciprocal of its norm (cast to `ℂ`) gives a unit vector spanning the same
ray. -/
noncomputable def imageVec
    (_hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    EuclideanSpace ℂ (Fin N) :=
  ((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ) • (f (srcPoint b i)).rep

/-- The reciprocal-norm scalar in `imageVec` is nonzero (the rep is nonzero, so
its norm is positive). -/
lemma imageVec_scalar_ne_zero
    (_hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have hne : (f (srcPoint b i)).rep ≠ 0 := (f (srcPoint b i)).rep_nonzero
  have hpos : (0 : ℝ) < ‖(f (srcPoint b i)).rep‖ := norm_pos_iff.mpr hne
  exact_mod_cast (ne_of_gt (inv_pos.mpr hpos))

/-- `imageVec` is nonzero. -/
lemma imageVec_ne_zero
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    imageVec hf b i ≠ 0 := by
  unfold imageVec
  exact smul_ne_zero (imageVec_scalar_ne_zero hf b i) (f (srcPoint b i)).rep_nonzero

/-- `imageVec` has unit norm: the reciprocal-norm scaling normalises the rep. -/
lemma imageVec_norm
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ‖imageVec hf b i‖ = 1 := by
  have hpos : (0 : ℝ) < ‖(f (srcPoint b i)).rep‖ :=
    norm_pos_iff.mpr (f (srcPoint b i)).rep_nonzero
  unfold imageVec
  rw [norm_smul, Complex.norm_real, norm_inv, Real.norm_eq_abs,
      abs_of_pos hpos, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- The image family `imageVec hf b` is orthonormal. Off-diagonal: the source
basis rays are orthogonal (`orthonormalBasis_pairwise_orthogonal` +
`transProb_eq_zero_iff` on the canonical reps), `inner_rep_eq_zero_iff hf`
transports this to the *image* reps, and the scalar normalisation factors pull
out of `inner` leaving `0`. Diagonal: `imageVec_norm`. -/
lemma imageVec_orthonormal
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Orthonormal ℂ (imageVec hf b) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases eq_or_ne i j with hij | hij
  · subst hij
    simp only [if_true]
    rw [inner_self_eq_norm_sq_to_K, imageVec_norm hf b i]
    norm_num
  · simp only [if_neg hij]
    -- source rays orthogonal ⇒ source reps orthogonal ⇒ image reps orthogonal
    have hsrc : transProb (srcPoint b i) (srcPoint b j) = 0 :=
      orthonormalBasis_pairwise_orthogonal b hij
    have hsrc_inner : (inner ℂ (srcPoint b i).rep (srcPoint b j).rep : ℂ) = 0 :=
      (transProb_eq_zero_iff (srcPoint b i) (srcPoint b j)).mp hsrc
    have himg_inner : (inner ℂ (f (srcPoint b i)).rep (f (srcPoint b j)).rep : ℂ) = 0 :=
      (hf.inner_rep_eq_zero_iff (srcPoint b i) (srcPoint b j)).mpr hsrc_inner
    unfold imageVec
    rw [inner_smul_left, inner_smul_right, himg_inner, mul_zero, mul_zero]

/-- The image orthonormal family, packaged as an `OrthonormalBasis (Fin N)`:
an orthonormal family of cardinality `N` in `EuclideanSpace ℂ (Fin N)`
(`finrank = N`) spans the whole space, so `OrthonormalBasis.mk` applies. -/
noncomputable def imageOrthonormalBasis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) := by
  refine OrthonormalBasis.mk (imageVec_orthonormal hf b) ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro x _
    exact (Subsingleton.elim x 0) ▸ Submodule.zero_mem _
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hcard : Fintype.card (Fin N) = Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) := by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    rw [(imageVec_orthonormal hf b).linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- `imageOrthonormalBasis` evaluates to `imageVec` (the `OrthonormalBasis.mk`
apply lemma). -/
lemma imageOrthonormalBasis_apply
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    imageOrthonormalBasis hf b i = imageVec hf b i := by
  unfold imageOrthonormalBasis
  rw [OrthonormalBasis.coe_mk]

/-- **The image ONB vector's ray is the image ray.** `imageVec hf b i` is a
nonzero scalar multiple of `(f (srcPoint b i)).rep`, so `mk (imageVec ..)`
equals `mk ((f (srcPoint b i)).rep) = f (srcPoint b i)` by the `mk`-scaling
characterisation `mk_eq_mk_iff'` and `mk_rep`. -/
lemma mk_imageOrthonormalBasis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    Projectivization.mk ℂ (imageOrthonormalBasis hf b i)
        ((imageOrthonormalBasis_apply hf b i).symm ▸ imageVec_ne_zero hf b i)
      = f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)) := by
  show _ = f (srcPoint b i)
  -- mk (imageONB i) = mk (imageVec i) = mk ((f (srcPoint i)).rep) = f (srcPoint i).
  -- `mk` is proof-irrelevant in the nonzero hypothesis, so the dependent proof
  -- argument is immaterial; chain three `mk` equalities.
  have hrep_ne : (f (srcPoint b i)).rep ≠ 0 := (f (srcPoint b i)).rep_nonzero
  have h1 : Projectivization.mk ℂ (imageOrthonormalBasis hf b i)
        ((imageOrthonormalBasis_apply hf b i).symm ▸ imageVec_ne_zero hf b i)
      = Projectivization.mk ℂ (imageVec hf b i) (imageVec_ne_zero hf b i) := by
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ?_
    exact ⟨1, by rw [one_smul, imageOrthonormalBasis_apply]⟩
  have h2 : Projectivization.mk ℂ (imageVec hf b i) (imageVec_ne_zero hf b i)
      = Projectivization.mk ℂ (f (srcPoint b i)).rep hrep_ne := by
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ?_
    exact ⟨((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ), rfl⟩
  rw [h1, h2, Projectivization.mk_rep]

/-! ## Step (2b): the candidate unitary

The candidate unitary is the `OrthonormalBasis.equiv` change-of-frame
`b ↦ imageOrthonormalBasis hf b` along the identity reindexing. On the source
basis vectors it reproduces the image ONB vectors, hence (via
`mk_imageOrthonormalBasis`) agrees ray-by-ray with `f` on the basis points.
This is the unitary candidate for the Wigner converse; the open content is
extending the agreement off the basis (step (2c)) and ruling out the antiunitary
branch (step (2d)). -/

/-- The candidate unitary: the linear isometry equivalence carrying the source
orthonormal basis `b` to the image orthonormal basis along the identity
reindexing of `Fin N`. -/
noncomputable def candidateUnitary
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  b.equiv (imageOrthonormalBasis hf b) (Equiv.refl (Fin N))

/-- The candidate unitary sends the `i`-th source basis vector to the `i`-th
image ONB vector. From `OrthonormalBasis.equiv_apply_basis` and
`Equiv.refl_apply`. -/
lemma candidateUnitary_apply_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    candidateUnitary hf b (b i) = imageOrthonormalBasis hf b i := by
  unfold candidateUnitary
  rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]

/-- **Step (2b) headline.** The candidate unitary agrees with `f` on the basis
points: the ray spanned by `candidateUnitary hf b (b i)` is exactly the image
ray `f (mk (b i))`. Composes `candidateUnitary_apply_basis` (the image ONB
vector) with `mk_imageOrthonormalBasis` (its ray is the image ray). -/
theorem candidateUnitary_agrees_on_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    Projectivization.mk ℂ (candidateUnitary hf b (b i))
        ((candidateUnitary hf b).toLinearEquiv.map_ne_zero_iff.mpr (b.orthonormal.ne_zero i))
      = f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)) := by
  rw [← mk_imageOrthonormalBasis hf b i]
  -- both rays are `mk` of the same vector `imageOrthonormalBasis hf b i`
  -- (after rewriting `candidateUnitary hf b (b i)` to it); `mk` is irrelevant to
  -- the nonzero-proof argument.
  congr 1
  · exact candidateUnitary_apply_basis hf b i

/-! ## Step (2c) frame reduction: projective image of an isometry equiv

The projective map `projMap e` of a linear isometry equivalence `e` preserves
`transProb` (`transProb_projMap`), so it is `TransProbPreserving`
(`projMap_transProbPreserving`). Composing `f` with the projective map of the
*inverse* candidate unitary yields `reducedMap`, which is `TransProbPreserving`
and **fixes every basis ray** (`reducedMap_fixes_basis`). This reduces the open
converse step (2c) to the single Wigner normal-form lemma stated in the module
header. These declarations are general in `E` wherever they do not consume the
`EuclideanSpace`-specific `candidateUnitary`. -/

section ProjMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The projective self-map induced by a linear isometry equivalence `e`: the
`Projectivization.map` of `e`'s underlying (injective) linear map. -/
noncomputable def projMap (e : E ≃ₗᵢ[ℂ] E) : ℙ ℂ E → ℙ ℂ E :=
  Projectivization.map e.toLinearEquiv.toLinearMap e.injective

/-- `projMap e` sends `mk v` to `mk (e v)`. The nonzero side is `e v ≠ 0` from
`e.injective` (an injective linear map is zero-preserving), packaged through
`Projectivization.map_mk`. -/
lemma projMap_mk (e : E ≃ₗᵢ[ℂ] E) (v : E) (hv : v ≠ 0) :
    projMap e (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (e v) (e.toLinearEquiv.map_ne_zero_iff.mpr hv) := by
  unfold projMap
  rw [Projectivization.map_mk]
  rfl

/-- `projMap` of the identity is the identity ray map. -/
@[simp] lemma projMap_refl :
    projMap (LinearIsometryEquiv.refl ℂ E) = id := by
  funext p
  induction p using Projectivization.ind with
  | h v hv => rw [projMap_mk]; rfl

/-- `projMap` is functorial: the ray map of a composite is the composite of the
ray maps (`trans` composes left-to-right, so `projMap e₂` applies second). -/
lemma projMap_trans (e₁ e₂ : E ≃ₗᵢ[ℂ] E) :
    projMap (e₁.trans e₂) = projMap e₂ ∘ projMap e₁ := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Function.comp_apply, projMap_mk, projMap_mk, projMap_mk]
    rfl

/-- **Transition probability is invariant under a linear isometry equivalence
(vector level).** `transProbVec (e u) (e v) = transProbVec u v`: the numerator
is fixed by `e.inner_map_map`, the denominator by `e.norm_map`. -/
lemma transProbVec_linearIsometryEquiv (e : E ≃ₗᵢ[ℂ] E) (u v : E) :
    transProbVec (e u) (e v) = transProbVec u v := by
  unfold transProbVec
  rw [e.inner_map_map u v, e.norm_map u, e.norm_map v]

/-- **`projMap e` preserves `transProb` (projective level).** Reduce both points
to `mk` of their canonical reps, push `projMap` through `projMap_mk`, collapse to
`transProbVec` via `transProb_mk`, then apply
`transProbVec_linearIsometryEquiv`. -/
lemma transProb_projMap (e : E ≃ₗᵢ[ℂ] E) (p q : ℙ ℂ E) :
    transProb (projMap e p) (projMap e q) = transProb p q := by
  conv_lhs => rw [← p.mk_rep, ← q.mk_rep]
  rw [projMap_mk e p.rep p.rep_nonzero, projMap_mk e q.rep q.rep_nonzero,
      transProb_mk]
  conv_rhs => rw [← p.mk_rep, ← q.mk_rep, transProb_mk p.rep_nonzero q.rep_nonzero]
  exact transProbVec_linearIsometryEquiv e p.rep q.rep

/-- **`projMap e` is `TransProbPreserving`.** Immediate from `transProb_projMap`.
General in `E`. -/
theorem projMap_transProbPreserving (e : E ≃ₗᵢ[ℂ] E) :
    TransProbPreserving (projMap e) :=
  fun p q => transProb_projMap e p q

/-- **Composition of `TransProbPreserving` maps.** `g ∘ f` preserves `transProb`
when both `g` and `f` do. General in `E`. -/
theorem TransProbPreserving.comp {g f : ℙ ℂ E → ℙ ℂ E}
    (hg : TransProbPreserving g) (hf : TransProbPreserving f) :
    TransProbPreserving (fun p => g (f p)) :=
  fun p q => by rw [hg (f p) (f q), hf p q]

end ProjMap

/-! ## Step (2c) frame reduction: the reduced map fixes every basis ray

`reducedMap hf b := projMap (candidateUnitary hf b).symm ∘ f`. It is
`TransProbPreserving` and fixes every source basis ray, since on `srcPoint b i`
the candidate unitary's projective map reproduces `f`'s value (by
`candidateUnitary_agrees_on_basis`) and its inverse returns to the basis ray. -/

variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-- The **frame-reduced map**: post-compose `f` with the projective map of the
*inverse* candidate unitary. Designed so that the basis rays become fixed
points. -/
noncomputable def reducedMap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  fun p => projMap (candidateUnitary hf b).symm (f p)

/-- **`reducedMap` is `TransProbPreserving`.** It is the composition
`projMap (candidateUnitary hf b).symm ∘ f`; compose `hf` with
`projMap_transProbPreserving`. -/
theorem reducedMap_transProbPreserving
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    TransProbPreserving (reducedMap hf b) :=
  (projMap_transProbPreserving (candidateUnitary hf b).symm).comp hf

/-- **HEADLINE (frame reduction).** The frame-reduced map fixes every source
basis ray: `reducedMap hf b (mk (b i)) = mk (b i)`.

Proof chain. Write `U := candidateUnitary hf b`. By definition
`reducedMap hf b (srcPoint b i) = projMap U.symm (f (srcPoint b i))`. Rewrite
`f (srcPoint b i)` backward via `candidateUnitary_agrees_on_basis` to
`mk (U (b i))`; push `projMap U.symm` through `projMap_mk` to
`mk (U.symm (U (b i)))`; and `U.symm (U (b i)) = b i` by
`LinearIsometryEquiv.symm_apply_apply`. `mk` is proof-irrelevant in its nonzero
hypothesis, so the dependent nonzero proofs are immaterial.

**Critical honesty note.** Fixing the basis rays does *not* make `reducedMap`
the identity: the diagonal-phase freedom is genuine and is exactly what the
remaining normal-form lemma (step (2c)) must pin down. Do not read this as
`reducedMap = id` or `f = projMap (candidateUnitary hf b)`. -/
theorem reducedMap_fixes_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    reducedMap hf b (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := by
  set U := candidateUnitary hf b with hU
  show projMap U.symm (f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)
  rw [← candidateUnitary_agrees_on_basis hf b i, ← hU,
      projMap_mk U.symm (U (b i))
        ((candidateUnitary hf b).toLinearEquiv.map_ne_zero_iff.mpr (b.orthonormal.ne_zero i))]
  -- `U.symm (U (b i)) = b i`; `mk` is irrelevant to the nonzero-proof argument.
  congr 1
  exact U.symm_apply_apply (b i)

/-! ## Stage 1: moduli preservation

A `TransProbPreserving` map fixing a projective point `q` preserves the
transition probability from every point to `q` (`TransProbPreserving.transProb_of_fixed`).
Applied to `reducedMap hf b`, which fixes every source basis ray, this shows the
**modulus profile** of the coordinates in the basis `b` is preserved: writing
`reducedMap hf b (mk ψ) = mk φ`, the normalised squared modulus
`‖b.repr ψ i‖² / ‖ψ‖²` of each coordinate is preserved
(`reducedMap_coord_modulus`). This is the coordinate-free heart of the Wigner
normal-form argument; it does not yet pin phases. -/

/-- **Moduli-preservation kernel.** A transition-probability-preserving map
fixing a projective point `q` preserves the transition probability from every
point to `q`. General in `E`. -/
theorem TransProbPreserving.transProb_of_fixed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {g : ℙ ℂ E → ℙ ℂ E} (hg : TransProbPreserving g)
    {q : ℙ ℂ E} (hq : g q = q) (p : ℙ ℂ E) :
    transProb (g p) q = transProb p q := by
  conv_lhs => rw [← hq]
  exact hg p q

/-- The transition probability from `mk ψ` to the `i`-th source basis ray
`srcPoint b i` is the normalised squared modulus of the `i`-th coordinate
`b.repr ψ i`. Uses `norm_inner_symm` and `OrthonormalBasis.repr_apply_apply` to
identify `‖⟪ψ, b i⟫‖ = ‖b.repr ψ i‖`, and `Orthonormal.norm_eq_one` to drop the
unit basis norm from the denominator. -/
lemma transProb_srcPoint
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    transProb (Projectivization.mk ℂ ψ hψ) (srcPoint b i)
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  rw [srcPoint_eq, transProb_mk hψ (b.orthonormal.ne_zero i)]
  unfold transProbVec
  rw [b.orthonormal.norm_eq_one i, one_pow, mul_one, norm_inner_symm,
      ← b.repr_apply_apply]

/-- **Stage 1 (moduli preservation).** Writing `reducedMap hf b (mk ψ) = mk φ`,
the normalised squared modulus of every coordinate in the basis `b` is preserved:
`‖b.repr φ i‖² / ‖φ‖² = ‖b.repr ψ i‖² / ‖ψ‖²`, where `φ` is the canonical
representative of the image ray. Combines the moduli-preservation kernel
`TransProbPreserving.transProb_of_fixed` (with `q = srcPoint b i`, fixed by
`reducedMap_fixes_basis`) and the coordinate reading `transProb_srcPoint`. -/
theorem reducedMap_coord_modulus
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    ‖b.repr (reducedMap hf b (Projectivization.mk ℂ ψ hψ)).rep i‖ ^ 2
        / ‖(reducedMap hf b (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have hfix : reducedMap hf b (srcPoint b i) = srcPoint b i := by
    rw [srcPoint_eq]; exact reducedMap_fixes_basis hf b i
  have key := (reducedMap_transProbPreserving hf b).transProb_of_fixed hfix
    (Projectivization.mk ℂ ψ hψ)
  rw [transProb_srcPoint b hψ i] at key
  set gp := reducedMap hf b (Projectivization.mk ℂ ψ hψ) with hgp
  have hgp_coord : transProb gp (srcPoint b i)
      = ‖b.repr gp.rep i‖ ^ 2 / ‖gp.rep‖ ^ 2 := by
    conv_lhs => rw [← Projectivization.mk_rep gp]
    exact transProb_srcPoint b gp.rep_nonzero i
  rw [← hgp_coord, key]

/-! ## Stage 2: the two-level phase normal form

For distinct indices `i₀ ≠ i`, the frame-reduced map sends the superposition ray
`mk (b i₀ + b i)` to a ray `mk (b i₀ + ε • b i)` with `ε` unimodular
(`reducedMap_two_level_normal_form`). Stage 1 forces the image rep to be
supported on `{i₀, i}` with equal coordinate moduli there; normalising the ray so
that the `i₀`-coordinate is `1` leaves a single unit phase `ε := d_i / d_{i₀}`.
The genuine content is the support restriction plus the modulus equality; the
phase `ε` is *not* yet pinned to `1` (that is Stage 3, the cocycle). -/

/-- The sum of two distinct basis vectors is nonzero: its squared norm is `2`
(Pythagoras via `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`, using the
orthogonality `b.orthonormal.2 hij` and the unit norms). -/
lemma add_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    (b i₀ + b i : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have h2 : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖
      * ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ = 2 := by
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
          (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀,
        b.orthonormal.norm_eq_one i]
    norm_num
  rw [h, norm_zero, mul_zero] at h2
  norm_num at h2

/-- **Support reconstruction.** A vector whose coordinates in the basis `b`
vanish outside `{i₀, i}` is the pair sum of its two surviving coordinates.
`OrthonormalBasis.sum_repr` expands `φ`, `Finset.sum_subset` drops the null
coordinates, and `Finset.sum_pair` collapses the two-element sum. -/
lemma repr_eq_pair_of_support
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (φ : EuclideanSpace ℂ (Fin N)) {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0) :
    φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i := by
  have hvanish : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      j ∉ ({i₀, i} : Finset (Fin N)) → b.repr φ j • b j = 0 := by
    intro j _ hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    push Not at hj
    rw [hsupp j hj.1 hj.2, zero_smul]
  calc φ = ∑ j, b.repr φ j • b j := (b.sum_repr φ).symm
    _ = ∑ j ∈ ({i₀, i} : Finset (Fin N)), b.repr φ j • b j :=
          (Finset.sum_subset (Finset.subset_univ _) hvanish).symm
    _ = b.repr φ i₀ • b i₀ + b.repr φ i • b i := Finset.sum_pair hij

/-- **Profile ⇒ two-level normal form.** A nonzero vector supported on `{i₀, i}`
with equal coordinate moduli there (and nonzero `i₀`-coordinate) spans the ray
`mk (b i₀ + ε • b i)` for the unit phase `ε := (b.repr φ i) / (b.repr φ i₀)`.
Factoring `b.repr φ i₀` out of the pair reconstruction rescales the ray; the
modulus equality gives `‖ε‖ = 1`. -/
lemma mk_eq_two_level_of_profile
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {φ : EuclideanSpace ℂ (Fin N)} (hφ : φ ≠ 0) {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0)
    (ha : b.repr φ i₀ ≠ 0)
    (hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖) :
    ∃ (ε : ℂ) (hne : (b i₀ + ε • b i : EuclideanSpace ℂ (Fin N)) ≠ 0),
      ‖ε‖ = 1 ∧
      Projectivization.mk ℂ φ hφ = Projectivization.mk ℂ (b i₀ + ε • b i) hne := by
  have hrec : φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i :=
    repr_eq_pair_of_support b φ hij hsupp
  set a := b.repr φ i₀ with ha_def
  set c := b.repr φ i with hc_def
  have hfactor : a • (b i₀ + (c / a) • b i) = φ := by
    have hac : a * (c / a) = c := by field_simp
    rw [smul_add, smul_smul, hac, ← hrec]
  have hne : (b i₀ + (c / a) • b i : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hfactor
    exact hφ hfactor.symm
  refine ⟨c / a, hne, ?_, ?_⟩
  · rw [norm_div, hmod, div_self (norm_ne_zero_iff.mpr ha)]
  · exact (Projectivization.mk_eq_mk_iff' ℂ φ (b i₀ + (c / a) • b i) hφ hne).mpr
      ⟨a, hfactor⟩

/-- **Stage 2 (two-level phase normal form).** For distinct `i₀ ≠ i`, the
frame-reduced map sends the superposition ray `mk (b i₀ + b i)` to
`mk (b i₀ + ε • b i)` for a unimodular `ε`. Stage 1 (`reducedMap_coord_modulus`)
forces the image rep to be supported on `{i₀, i}` with equal moduli there;
`mk_eq_two_level_of_profile` packages the ray normal form. This pins the image
ray up to the single phase `ε`; pinning `ε = 1` (globally coherently) is the
Stage 3 cocycle, not proved here. -/
theorem reducedMap_two_level_normal_form
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    ∃ (ε : ℂ) (hne : (b i₀ + ε • b i : EuclideanSpace ℂ (Fin N)) ≠ 0),
      ‖ε‖ = 1 ∧
      reducedMap hf b
          (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i₀ + ε • b i) hne := by
  -- Coordinates of the source superposition `w = b i₀ + b i`.
  have hwj : ∀ j, b.repr (b i₀ + b i) j
      = (if j = i₀ then (1 : ℂ) else 0) + (if j = i then 1 else 0) := by
    intro j
    rw [b.repr_apply_apply, inner_add_right,
        orthonormal_iff_ite.mp b.orthonormal j i₀,
        orthonormal_iff_ite.mp b.orthonormal j i]
  have hwi0 : b.repr (b i₀ + b i) i₀ = 1 := by
    rw [hwj i₀, if_pos rfl, if_neg hij, add_zero]
  have hwi : b.repr (b i₀ + b i) i = 1 := by
    rw [hwj i, if_neg (Ne.symm hij), if_pos rfl, zero_add]
  have hwnorm : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
          (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀,
        b.orthonormal.norm_eq_one i]
    norm_num
  -- The image rep `φ` and the transported moduli (Stage 1).
  set φ := (reducedMap hf b
      (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))).rep
    with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hmodj : ∀ j, ‖b.repr φ j‖ ^ 2 / ‖φ‖ ^ 2
      = ‖b.repr (b i₀ + b i) j‖ ^ 2
          / ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
    intro j
    rw [hφ_def]
    exact reducedMap_coord_modulus hf b (add_basis_ne_zero b hij) j
  -- Support of `φ` is `{i₀, i}`.
  have hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0 := by
    intro j hj0 hji
    have hz : ‖b.repr φ j‖ ^ 2 / ‖φ‖ ^ 2 = 0 := by
      rw [hmodj j, hwj j, if_neg hj0, if_neg hji, add_zero, norm_zero]
      norm_num
    have hsq : ‖b.repr φ j‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hz with h | h
      · exact h
      · exact absurd h (ne_of_gt hφpos)
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hsq
  -- The `i₀`-coordinate of `φ` is nonzero (its modulus² is `‖φ‖²/2`).
  have ha : b.repr φ i₀ ≠ 0 := by
    intro h
    have hmj := hmodj i₀
    rw [hwi0, h, norm_zero, hwnorm, norm_one] at hmj
    norm_num at hmj
  -- The `i` and `i₀` coordinate moduli agree.
  have hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖ := by
    have hi := hmodj i
    have hi0 := hmodj i₀
    rw [hwi, norm_one, hwnorm] at hi
    rw [hwi0, norm_one, hwnorm] at hi0
    have hd := hi.trans hi0.symm
    rw [div_eq_div_iff (ne_of_gt hφpos) (ne_of_gt hφpos)] at hd
    have heq2 : ‖b.repr φ i‖ ^ 2 = ‖b.repr φ i₀‖ ^ 2 :=
      mul_right_cancel₀ (ne_of_gt hφpos) hd
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ i)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), heq2]
  -- Assemble via the profile normal form.
  obtain ⟨ε, hne, hεnorm, hmkeq⟩ :=
    mk_eq_two_level_of_profile b hφne hij hsupp ha hmod
  refine ⟨ε, hne, hεnorm, ?_⟩
  rw [← hmkeq]
  exact (Projectivization.mk_rep _).symm

/-! ## Stage 3 piece 1: the diagonal-phase reduction

The first piece of the Stage 3 residual, on the critical path to the dichotomy.
It removes the Stage-2 two-level phases by post-composing the frame-reduced map
`g = reducedMap hf b` with a diagonal isometry `D⁻¹` in the basis `b`.

* **The diagonal isometry.** For a unit-modulus phase family `ε : Fin N → ℂ`
  (`∀ i, ‖ε i‖ = 1`), the scaled family `fun i => ε i • b i` is again an
  orthonormal basis (`scaledBasis`); `diagUnitary b ε hε` is the `≃ₗᵢ[ℂ]`
  carrying `b` to it, so `diagUnitary (b i) = ε i • b i`
  (`diagUnitary_apply_basis`) and `(diagUnitary).symm (b i) = (ε i)⁻¹ • b i`
  (`diagUnitary_symm_apply_basis`). This is diagonal *in the basis `b`*, not in
  the standard basis, so it is built as an `OrthonormalBasis.equiv`, not a
  `Matrix.diagonal`.
* **The extracted phases.** `twoLevelPhase hf b i₀` reads off, per index, the
  Stage-2 phase `εᵢ` from `reducedMap_two_level_normal_form` (anchored at
  `ε i₀ := 1`), with `‖twoLevelPhase hf b i₀ j‖ = 1` for every `j`
  (`twoLevelPhase_norm`).
* **The diagonally-reduced map.** `diagReducedMap hf b i₀ := projMap (D).symm ∘
  reducedMap hf b` with `D := diagUnitary b (twoLevelPhase hf b i₀) …`. It is
  `TransProbPreserving` (`diagReducedMap_transProbPreserving`), still fixes every
  basis ray (`diagReducedMap_fixes_basis`), and additionally **fixes the
  two-level rays** `mk (b i₀ + b i)` for every `i ≠ i₀`
  (`diagReducedMap_fixes_two_level`) — the setup the cocycle step (pieces 2–3)
  consumes. **No ℂ-linearity is assumed:** `D` is constructed *from* the
  extracted phases, not posited of `f`. -/

/-- The scaled family `fun i => ε i • b i` is orthonormal when every phase is
unit modulus (`‖ε i‖ = 1`): the off-diagonals inherit `b`'s orthogonality, and
the diagonal is `conj (ε i) * ε i = ‖ε i‖² = 1` (`RCLike.conj_mul`). -/
lemma scaled_orthonormal
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    Orthonormal ℂ (fun i => ε i • b i) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j]
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [if_true, mul_one]
    rw [RCLike.conj_mul, hε i]; norm_num
  · simp [h]

/-- The `ε`-scaled family spans: cardinality `N` linearly independent vectors in
`finrank = N`. Kept a separate `Prop` lemma so `scaledBasis` is a term-mode `def`
(a tactic-mode data `def` would over-include ambient section variables). -/
lemma scaled_span
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    ⊤ ≤ Submodule.span ℂ (Set.range (fun i => ε i • b i)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro x _
    exact (Subsingleton.elim x 0) ▸ Submodule.zero_mem _
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hcard : Fintype.card (Fin N) = Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) := by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    rw [(scaled_orthonormal b ε hε).linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- The `ε`-scaled orthonormal basis (an orthonormal family of cardinality `N`
in `finrank = N`, so `OrthonormalBasis.mk` applies). -/
noncomputable def scaledBasis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  OrthonormalBasis.mk (scaled_orthonormal b ε hε) (scaled_span b ε hε)

/-- `scaledBasis` evaluates to the scaled basis vector (`OrthonormalBasis.mk`
apply). -/
lemma scaledBasis_apply
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    scaledBasis b ε hε i = ε i • b i := by
  unfold scaledBasis; rw [OrthonormalBasis.coe_mk]

/-- The **diagonal isometry in the basis `b`**: the `≃ₗᵢ[ℂ]` carrying `b` to the
`ε`-scaled basis along the identity reindexing. Diagonal in `b`
(`diagUnitary (b i) = ε i • b i`), unit modulus per coordinate. -/
noncomputable def diagUnitary
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  b.equiv (scaledBasis b ε hε) (Equiv.refl (Fin N))

/-- `diagUnitary` scales the `i`-th basis vector by `ε i`. -/
lemma diagUnitary_apply_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    diagUnitary b ε hε (b i) = ε i • b i := by
  unfold diagUnitary
  rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, scaledBasis_apply]

/-- The inverse `diagUnitary` scales the `i`-th basis vector by `(ε i)⁻¹`.
`diagUnitary ((ε i)⁻¹ • b i) = b i` (since `ε i ≠ 0`), then
`symm_apply_apply`. -/
lemma diagUnitary_symm_apply_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    (diagUnitary b ε hε).symm (b i) = (ε i)⁻¹ • b i := by
  have hεne : ε i ≠ 0 := by rw [← norm_ne_zero_iff, hε i]; norm_num
  have h : diagUnitary b ε hε ((ε i)⁻¹ • b i) = b i := by
    rw [map_smul, diagUnitary_apply_basis, smul_smul, inv_mul_cancel₀ hεne, one_smul]
  conv_lhs => rw [← h]
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The Stage-2 phase, extracted per index and anchored at `ε i₀ := 1`.
For `j ≠ i₀`, `twoLevelPhase hf b i₀ j` is the unit phase `εⱼ` supplied by
`reducedMap_two_level_normal_form` for the pair `(i₀, j)`. -/
noncomputable def twoLevelPhase
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ j : Fin N) : ℂ :=
  if h : j = i₀ then 1
  else Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := j) (Ne.symm h))

/-- The anchor phase is `1`: `twoLevelPhase hf b i₀ i₀ = 1`. -/
lemma twoLevelPhase_self
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    twoLevelPhase hf b i₀ i₀ = 1 := by
  unfold twoLevelPhase; rw [dif_pos rfl]

/-- Every extracted phase is unit modulus: `‖twoLevelPhase hf b i₀ j‖ = 1`
(anchor `‖1‖ = 1`; off-anchor from the Stage-2 `choose_spec`). -/
lemma twoLevelPhase_norm
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ j : Fin N) :
    ‖twoLevelPhase hf b i₀ j‖ = 1 := by
  unfold twoLevelPhase
  rcases eq_or_ne j i₀ with h | h
  · rw [dif_pos h, norm_one]
  · rw [dif_neg h]
    obtain ⟨_, hnorm, _⟩ :=
      Classical.choose_spec (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := j) (Ne.symm h))
    exact hnorm

/-- The **diagonally-reduced map**: `projMap D⁻¹ ∘ reducedMap hf b`, where
`D := diagUnitary b (twoLevelPhase hf b i₀) …` is the diagonal isometry built
from the extracted phases. -/
noncomputable def diagReducedMap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  fun p => projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
    (reducedMap hf b p)

/-- **`diagReducedMap` is `TransProbPreserving`.** Composition of the
preserving `projMap D⁻¹` and the preserving `reducedMap hf b`. -/
lemma diagReducedMap_transProbPreserving
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    TransProbPreserving (diagReducedMap hf b i₀) :=
  (projMap_transProbPreserving
    (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm).comp
    (reducedMap_transProbPreserving hf b)

/-- **`diagReducedMap` still fixes every basis ray.** `reducedMap` fixes
`mk (b i)`, then `projMap D⁻¹` sends it to `mk ((ε i)⁻¹ • b i) = mk (b i)`
(scaling invariance). -/
lemma diagReducedMap_fixes_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ i : Fin N) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := by
  show projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
      (reducedMap hf b _) = _
  rw [reducedMap_fixes_basis hf b i, projMap_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(twoLevelPhase hf b i₀ i)⁻¹, ?_⟩
  rw [diagUnitary_symm_apply_basis]

/-- **HEADLINE (diagonal-phase reduction).** The diagonally-reduced map fixes
the two-level superposition ray `mk (b i₀ + b i)` for every `i ≠ i₀`.

Proof. Stage 2 (`reducedMap_two_level_normal_form`, extracted through
`twoLevelPhase`) gives `reducedMap hf b (mk (b i₀ + b i)) = mk (b i₀ + c • b i)`
with `c := twoLevelPhase hf b i₀ i` unit modulus. Applying `D⁻¹`:
`D⁻¹ (b i₀) = (ε i₀)⁻¹ • b i₀ = b i₀` (anchor `ε i₀ = 1`) and
`D⁻¹ (b i) = c⁻¹ • b i`, so `D⁻¹ (b i₀ + c • b i) = b i₀ + (c c⁻¹) • b i =
b i₀ + b i`. Hence the ray is fixed. This is the setup consumed by the cocycle
step (pieces 2–3): a `TransProbPreserving` map fixing every basis ray and every
two-level ray `mk (b i₀ + b i)`. **No ℂ-linearity assumed.** -/
theorem diagReducedMap_fixes_two_level
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i : Fin N} (hij : i₀ ≠ i) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij) := by
  obtain ⟨_, hnorm, heq⟩ :=
    Classical.choose_spec (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij)
  have hci : twoLevelPhase hf b i₀ i
      = Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij) := by
    rw [twoLevelPhase, dif_neg (Ne.symm hij)]
  set c := Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij) with hc
  have hcne : c ≠ 0 := by rw [← norm_ne_zero_iff, hnorm]; norm_num
  show projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
      (reducedMap hf b _) = _
  rw [heq, projMap_mk]
  have hcomp :
      (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
        (b i₀ + c • b i) = b i₀ + b i := by
    rw [map_add, map_smul, diagUnitary_symm_apply_basis, diagUnitary_symm_apply_basis,
        twoLevelPhase_self hf b i₀, hci]
    simp only [inv_one, one_smul, smul_smul]
    rw [mul_inv_cancel₀ hcne, one_smul]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, hcomp]

/-! ## Stage 3 piece 2: coordinate moduli, the two-level relative phase, cocycle datum

Piece 2 of the Stage-3 residual, the derivation-heavy core, built on the diagonally
reduced map `h := diagReducedMap hf b i₀` (`TransProbPreserving`, fixing every basis
ray and every anchored two-level ray `mk (b i₀ + b i)`). Writing `h (mk ψ) = mk φ`,
`cⱼ := b.repr ψ j`, `dⱼ := b.repr φ j`:

* **Moduli** (`coord_modulus_of_fixes_basis`, `diagReducedMap_coord_modulus`):
  `‖dⱼ‖² / ‖φ‖² = ‖cⱼ‖² / ‖ψ‖²`, for any `TransProbPreserving` map fixing the basis
  rays.
* **Two-level relative phase** (`two_level_relphase_of_fixes`,
  `diagReducedMap_two_level_relphase`) — the heart of piece 2:
  `Re(d̄_{i₀} d_i) / ‖φ‖² = Re(c̄_{i₀} c_i) / ‖ψ‖²`, i.e.
  `arg(d_i / d_{i₀}) = ± arg(c_i / c_{i₀})`. The overlap fixes only the real part;
  the sign of the imaginary part — the cocycle's ℤ/2 datum — stays free.
* **Conditional pairwise relation** (`diagReducedMap_pairwise_relphase_of_fixed`):
  for any pair `(i, j)` whose two-level ray is fixed by `h`, the analogous relation
  `Re(d̄_i d_j) / ‖φ‖² = Re(c̄_i c_j) / ‖ψ‖²` holds.

**No ℂ-linearity of `f`/`h` is used anywhere below**: every relation comes from the
`transProb`/`transProbVec` overlap algebra, the fixed-point content of
`diagReducedMap`, and the moduli. The precise residual is documented after the
lemmas and in the `Stage 3 (residual)` section. -/

/-- **Complex parallelogram expansion.** For `A B : ℂ`,
`‖A + B‖² = ‖A‖² + ‖B‖² + 2·Re(conj A · B)`. Via `Complex.normSq_add` and
`Complex.normSq_eq_norm_sq`; `(A · conj B).re = (conj A · B).re` since `re` is
conjugation-invariant. -/
lemma cnorm_add_sq (A B : ℂ) :
    ‖A + B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * ((starRingEnd ℂ) A * B).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add]
  have hre : (A * (starRingEnd ℂ) B).re = ((starRingEnd ℂ) A * B).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  rw [hre]

/-- The inner product of `ψ` with a basis vector is the conjugate of the
corresponding coordinate: `⟪ψ, b j⟫ = conj (b.repr ψ j)`. From
`OrthonormalBasis.repr_apply_apply` (`b.repr ψ j = ⟪b j, ψ⟫`) and
`inner_conj_symm`. -/
lemma inner_eq_conj_repr
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    (inner ℂ ψ (b j) : ℂ) = (starRingEnd ℂ) (b.repr ψ j) := by
  rw [b.repr_apply_apply]
  exact (inner_conj_symm ψ (b j)).symm

/-- The inner product of `ψ` with a two-level basis sum unfolds to the conjugate
of the coordinate sum: `⟪ψ, b i₀ + b i⟫ = conj (b.repr ψ i₀ + b.repr ψ i)`. -/
lemma inner_add_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i₀ i : Fin N) :
    (inner ℂ ψ (b i₀ + b i) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i₀ + b.repr ψ i) := by
  rw [inner_add_right, inner_eq_conj_repr b ψ i₀, inner_eq_conj_repr b ψ i, map_add]

/-- The squared norm of a two-level basis sum is `2` (Pythagoras via
`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` and the unit norms). -/
lemma add_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
        (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀, b.orthonormal.norm_eq_one i]
  norm_num

/-- **Two-level overlap in coordinates.** The transition probability from `mk ψ`
to the two-level ray `mk (b i₀ + b i)` is
`‖b.repr ψ i₀ + b.repr ψ i‖² / (‖ψ‖² · 2)`. Combines `transProb_mk`,
`inner_add_basis` (the numerator), `RCLike.norm_conj`, and `add_basis_norm_sq`
(the denominator's `‖b i₀ + b i‖² = 2`). -/
lemma transProb_two_level
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) {i₀ i : Fin N} (hij : i₀ ≠ i) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = ‖b.repr ψ i₀ + b.repr ψ i‖ ^ 2 / (‖ψ‖ ^ 2 * 2) := by
  rw [transProb_mk hψ (add_basis_ne_zero b hij)]
  unfold transProbVec
  rw [inner_add_basis, RCLike.norm_conj, add_basis_norm_sq b hij]

/-- **Moduli preservation for a basis-fixing preserver.** Any
`TransProbPreserving` map `g` that fixes every source basis ray preserves the
normalised squared modulus of every coordinate:
`‖b.repr (g (mk ψ)).rep i‖² / ‖(g (mk ψ)).rep‖² = ‖b.repr ψ i‖² / ‖ψ‖²`.
Generalises `reducedMap_coord_modulus` off `reducedMap` to an abstract `g`; the
proof is the same `transProb_of_fixed` + `transProb_srcPoint` composition. -/
theorem coord_modulus_of_fixes_basis
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ j, g (srcPoint b j) = srcPoint b j)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    ‖b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i‖ ^ 2
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have key := hg.transProb_of_fixed (hfixb i) (Projectivization.mk ℂ ψ hψ)
  rw [transProb_srcPoint b hψ i] at key
  set gp := g (Projectivization.mk ℂ ψ hψ) with hgp
  have hgp_coord : transProb gp (srcPoint b i)
      = ‖b.repr gp.rep i‖ ^ 2 / ‖gp.rep‖ ^ 2 := by
    conv_lhs => rw [← Projectivization.mk_rep gp]
    exact transProb_srcPoint b gp.rep_nonzero i
  rw [← hgp_coord, key]

/-- **Two-level relative-phase constraint (general).** Let `g` be
`TransProbPreserving`, fixing every basis ray and the two-level ray
`mk (b i₀ + b i)`. Writing `g (mk ψ) = mk φ`, the *real part* of the relative
phase between the `i₀`- and `i`-coordinates is preserved:
`Re(conj d_{i₀} · d_i) / ‖φ‖² = Re(conj c_{i₀} · c_i) / ‖ψ‖²`, with
`cⱼ = b.repr ψ j`, `dⱼ = b.repr φ j`.

Proof. The two-level overlap `transProb (g (mk ψ)) (mk (b i₀ + b i))` equals
`transProb (mk ψ) (mk (b i₀ + b i))` because `g` fixes the two-level ray
(`transProb_of_fixed`); `transProb_two_level` reads both as
`‖·₀ + ·ᵢ‖² / (‖·‖² · 2)`. Cross-multiplying and expanding the numerators with
`cnorm_add_sq` leaves, after cancelling the modulus terms via
`coord_modulus_of_fixes_basis`, exactly the real-part relation.

**No linearity is used**: this is pure overlap algebra. The imaginary part of
`conj d_{i₀} · d_i` — the sign of the relative phase, the cocycle's ℤ/2 datum —
is *not* pinned, and the result holds for both the unitary (`d = c`) and
antiunitary (`d = conj c`) branches. -/
theorem two_level_relphase_of_fixes
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ j, g (srcPoint b j) = srcPoint b j)
    {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hfix2 : g (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i₀)
          * b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i).re
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i₀) * b.repr ψ i).re / ‖ψ‖ ^ 2 := by
  have hA := hg.transProb_of_fixed hfix2 (Projectivization.mk ℂ ψ hψ)
  rw [transProb_two_level b hψ hij] at hA
  have md0 := coord_modulus_of_fixes_basis hg b hfixb hψ i₀
  have mdi := coord_modulus_of_fixes_basis hg b hfixb hψ i
  set q := g (Projectivization.mk ℂ ψ hψ) with hq
  have hLHS : transProb q (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = ‖b.repr q.rep i₀ + b.repr q.rep i‖ ^ 2 / (‖q.rep‖ ^ 2 * 2) := by
    conv_lhs => rw [← q.mk_rep]
    exact transProb_two_level b q.rep_nonzero hij
  rw [hLHS] at hA
  have hDφ : ‖q.rep‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr q.rep_nonzero)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hcross := (div_eq_div_iff (mul_ne_zero hDφ (by norm_num : (2 : ℝ) ≠ 0))
    (mul_ne_zero hDψ (by norm_num : (2 : ℝ) ≠ 0))).mp hA
  rw [cnorm_add_sq, cnorm_add_sq] at hcross
  have hm0 := (div_eq_div_iff hDφ hDψ).mp md0
  have hmi := (div_eq_div_iff hDφ hDψ).mp mdi
  rw [div_eq_div_iff hDφ hDψ]
  linear_combination (1 / 4 : ℝ) * hcross - (1 / 2 : ℝ) * hm0 - (1 / 2 : ℝ) * hmi

/-- **Moduli preservation for the diagonally reduced map.** Instance of
`coord_modulus_of_fixes_basis` for `diagReducedMap hf b i₀`. -/
theorem diagReducedMap_coord_modulus
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    ‖b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i‖ ^ 2
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 :=
  coord_modulus_of_fixes_basis (diagReducedMap_transProbPreserving hf b i₀) b
    (fun j => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ j) hψ i

/-- **HEADLINE (two-level relative phase, the heart of piece 2).** The diagonally
reduced map `diagReducedMap hf b i₀` preserves the real part of the relative phase
between the anchor coordinate `i₀` and any coordinate `i ≠ i₀`:
`Re(conj d_{i₀} · d_i) / ‖φ‖² = Re(conj c_{i₀} · c_i) / ‖ψ‖²`, i.e.
`arg(d_i / d_{i₀}) = ± arg(c_i / c_{i₀})`. Instance of `two_level_relphase_of_fixes`
with the basis fixing (`diagReducedMap_fixes_basis`) and the anchored two-level
fixing (`diagReducedMap_fixes_two_level`). The `±` sign is genuinely free (only the
real part is pinned) and no ℂ-linearity is assumed. -/
theorem diagReducedMap_two_level_relphase
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i : Fin N} (hij : i₀ ≠ i)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i₀)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i₀) * b.repr ψ i).re / ‖ψ‖ ^ 2 :=
  two_level_relphase_of_fixes (diagReducedMap_transProbPreserving hf b i₀) b
    (fun j => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ j)
    hij (diagReducedMap_fixes_two_level hf b hij) hψ

/-- **Conditional pairwise relative phase (the (i, j) leg of the 2-cocycle).**
For a pair `(i, j)` whose two-level ray `mk (b i + b j)` is fixed by
`diagReducedMap hf b i₀`, the relative-phase relation
`Re(conj d_i · d_j) / ‖φ‖² = Re(conj c_i · c_j) / ‖ψ‖²` holds. Immediate instance
of `two_level_relphase_of_fixes` for the pair `(i, j)`. The fixing hypothesis
`hfix` is the *only* residual input: the anchored diagonal reduction supplies it
for `i = i₀` (`diagReducedMap_fixes_two_level`) but not for general non-anchored
pairs (see the residual note). -/
theorem diagReducedMap_pairwise_relphase_of_fixed
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    (hfix : diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).re / ‖ψ‖ ^ 2 :=
  two_level_relphase_of_fixes (diagReducedMap_transProbPreserving hf b i₀) b
    (fun k => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k)
    hij hfix hψ

/-! ## Stage 3 piece 2 (W4): triple-support probe and the non-anchored two-level fixing

The non-anchored two-level fixing `g (mk (b i + b j)) = mk (b i + b j)` for
`i, j ≠ i₀` — the missing input that upgrades the pairwise relative-phase relation
to unconditional — is derived here through a **triple-support probe**. The equal
triple ray `mk (b i₀ + b i + b j)` is first shown fixed
(`diagReducedMap_fixes_three_level`), then used as a probe carrying both `i` and
`j` to fix the non-anchored two-level ray
(`diagReducedMap_fixes_two_level_general`), whence the conditional pairwise leg
becomes unconditional (`diagReducedMap_pairwise_relphase`).

**Critical honesty (audit).** Every probe here is a **real-coordinate**
superposition (all surviving source coordinates `= 1`), so its ray is fixed by
the identity and by coordinatewise conjugation **alike**: fixing it is consistent
with **both** the unitary (`d = c`) and antiunitary (`d = conj c`) branches, and
does **not** collapse the global unitary/antiunitary choice. What is established
is the **coboundary structure** of the phase cocycle (the pairwise real-part
relations), not the global sign (piece 3). No ℂ-linearity is assumed: every
alignment comes from moduli preservation, a single fixed-probe overlap, and the
saturation lemma. -/

/-- **Saturation.** A complex number whose real part equals its modulus is that
real part: `‖z‖ = z.re → z = z.re`. Squaring, `z.re² = ‖z‖² = z.re² + z.im²`
forces `z.im = 0`. -/
lemma norm_eq_re_imp_eq {z : ℂ} (h : ‖z‖ = z.re) : z = (z.re : ℂ) := by
  have him : z.im = 0 := by
    have h1 : z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_apply]; exact Complex.normSq_eq_norm_sq z
    have hsq : ‖z‖ ^ 2 = z.re * z.re := by rw [h]; ring
    rw [hsq] at h1
    have : z.im * z.im = 0 := by linarith
    exact mul_self_eq_zero.mp this
  rw [Complex.ext_iff]
  exact ⟨by simp, by rw [him]; simp⟩

/-- **Phase alignment from a saturated overlap.** If two complex numbers have
equal modulus `‖c‖ = ‖a‖`, with `a ≠ 0`, and the real part of `conj a · c`
saturates the modulus product `Re(conj a · c) = ‖a‖²`, then `c = a`. Route:
`‖conj a · c‖ = ‖a‖‖c‖ = ‖a‖²`, so `Re = ‖·‖`; `norm_eq_re_imp_eq` makes
`conj a · c` real and equal to `‖a‖² = conj a · a`; cancel `conj a ≠ 0`. This is
the neutral alignment step; applied to a real-coordinate probe it aligns `d = a`
on **both** the unitary and antiunitary branches, so it does not collapse the
sign. -/
lemma eq_of_re_conj_mul_eq {a c : ℂ} (ha : a ≠ 0) (hmod : ‖c‖ = ‖a‖)
    (hre : ((starRingEnd ℂ) a * c).re = ‖a‖ ^ 2) : c = a := by
  have hnorm : ‖(starRingEnd ℂ) a * c‖ = ((starRingEnd ℂ) a * c).re := by
    rw [norm_mul, RCLike.norm_conj, hmod, hre]; ring
  have hsat : (starRingEnd ℂ) a * c = (((starRingEnd ℂ) a * c).re : ℂ) :=
    norm_eq_re_imp_eq hnorm
  rw [hre] at hsat
  have haa : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]; norm_cast
  have hca : (starRingEnd ℂ) a * c = (starRingEnd ℂ) a * a := by rw [hsat, haa]
  have hconj_ne : (starRingEnd ℂ) a ≠ 0 := star_ne_zero.mpr ha
  exact mul_left_cancel₀ hconj_ne hca

/-- **Triple-support reconstruction.** A vector whose coordinates in the basis
`b` vanish outside `{i₀, i, j}` (distinct) is the triple sum of its three
surviving coordinates. `OrthonormalBasis.sum_repr` expands `φ`,
`Finset.sum_subset` drops the null coordinates, and the three-element
`Finset.sum` collapses. The 3-support analogue of `repr_eq_pair_of_support`. -/
lemma repr_eq_triple_of_support
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (φ : EuclideanSpace ℂ (Fin N)) {i₀ i j : Fin N}
    (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j)
    (hsupp : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → b.repr φ k = 0) :
    φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i + b.repr φ j • b j := by
  have hvanish : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      k ∉ ({i₀, i, j} : Finset (Fin N)) → b.repr φ k • b k = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hsupp k hk.1 hk.2.1 hk.2.2, zero_smul]
  calc φ = ∑ k, b.repr φ k • b k := (b.sum_repr φ).symm
    _ = ∑ k ∈ ({i₀, i, j} : Finset (Fin N)), b.repr φ k • b k :=
          (Finset.sum_subset (Finset.subset_univ _) hvanish).symm
    _ = b.repr φ i₀ • b i₀ + b.repr φ i • b i + b.repr φ j • b j := by
          rw [Finset.sum_insert (by simp [h0i, h0j]),
              Finset.sum_insert (by simp [hij]), Finset.sum_singleton, add_assoc]

/-- The squared norm of a triple basis sum is `3` (Pythagoras: `b i₀ + b i ⟂ b j`
and `‖b i₀ + b i‖² = 2`, `‖b j‖² = 1`). -/
lemma add3_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    ‖(b i₀ + b i + b j : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 3 := by
  have hperp : (inner ℂ (b i₀ + b i : EuclideanSpace ℂ (Fin N)) (b j) : ℂ) = 0 := by
    rw [inner_add_left, orthonormal_iff_ite.mp b.orthonormal i₀ j,
        orthonormal_iff_ite.mp b.orthonormal i j, if_neg h0j, if_neg hij, add_zero]
  have h3 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀ + b i) (b j) hperp
  rw [pow_two, h3]
  have e1 : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖
      * ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ = 2 := by
    rw [← pow_two]; exact add_basis_norm_sq b h0i
  rw [e1, b.orthonormal.norm_eq_one j]; norm_num

/-- A triple of distinct basis vectors sums to a nonzero vector (norm² = `3`). -/
lemma add3_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    (b i₀ + b i + b j : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have hn := add3_basis_norm_sq b h0i h0j hij
  rw [h, norm_zero, zero_pow (by norm_num)] at hn
  norm_num at hn

/-- The inner product of `ψ` with a triple basis sum unfolds to the conjugate of
the coordinate sum: `⟪ψ, b i₀ + b i + b j⟫ = conj (c_{i₀} + c_i + c_j)`. -/
lemma inner_add3_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i₀ i j : Fin N) :
    (inner ℂ ψ (b i₀ + b i + b j) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i₀ + b.repr ψ i + b.repr ψ j) := by
  rw [inner_add_right, inner_add_basis, inner_eq_conj_repr, ← map_add]

/-- **Triple parallelogram expansion.** `‖A + B + C‖² = ‖A‖² + ‖B‖² + ‖C‖²
+ 2·Re(conj A · B) + 2·Re(conj A · C) + 2·Re(conj B · C)`. Two applications of
`cnorm_add_sq` plus `Re(conj (A+B) · C) = Re(conj A · C) + Re(conj B · C)`. -/
lemma cnorm_add3_sq (A B C : ℂ) :
    ‖A + B + C‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2
      + 2 * ((starRingEnd ℂ) A * B).re + 2 * ((starRingEnd ℂ) A * C).re
      + 2 * ((starRingEnd ℂ) B * C).re := by
  rw [cnorm_add_sq (A + B) C, cnorm_add_sq A B]
  have hsplit : ((starRingEnd ℂ) (A + B) * C).re
      = ((starRingEnd ℂ) A * C).re + ((starRingEnd ℂ) B * C).re := by
    rw [map_add, add_mul, Complex.add_re]
  rw [hsplit]; ring

/-- **Triple-level overlap in coordinates.** The transition probability from
`mk ψ` to the equal triple ray `mk (b i₀ + b i + b j)` is
`‖c_{i₀} + c_i + c_j‖² / (‖ψ‖² · 3)`. Combines `transProb_mk`, `inner_add3_basis`
(numerator), `RCLike.norm_conj`, and `add3_basis_norm_sq` (denominator). -/
lemma transProb_three_level
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0)
    {i₀ i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i₀ + b i + b j) (add3_basis_ne_zero b h0i h0j hij))
      = ‖b.repr ψ i₀ + b.repr ψ i + b.repr ψ j‖ ^ 2 / (‖ψ‖ ^ 2 * 3) := by
  rw [transProb_mk hψ (add3_basis_ne_zero b h0i h0j hij)]
  unfold transProbVec
  rw [inner_add3_basis, RCLike.norm_conj, add3_basis_norm_sq b h0i h0j hij]

/-! ## Stage 3 piece 2 (W4): the triple and non-anchored two-level fixings -/

/-- **HEADLINE (triple-support fixing).** The diagonally reduced map fixes the
equal triple superposition ray `mk (b i₀ + b i + b j)` for distinct `i₀, i, j`.

Proof. Write `g := diagReducedMap hf b i₀`, `φ := (g (mk w)).rep` with
`w := b i₀ + b i + b j`. Stage-1 moduli (`coord_modulus_of_fixes_basis`) restrict
`φ` to support `{i₀, i, j}` with equal coordinate moduli `‖d_k‖² = ‖φ‖²/3`. The
two anchored two-level fixings (`diagReducedMap_two_level_relphase` at the probe
`w`) pin `Re(conj d_{i₀} · d_i) = ‖φ‖²/3 = ‖d_{i₀}‖²` and likewise for `j`, which
saturates the modulus product; `eq_of_re_conj_mul_eq` forces `d_i = d_{i₀}` and
`d_j = d_{i₀}`, so `φ = d_{i₀} · w` and `mk φ = mk w`.

**Audit note.** The source coordinates `c_{i₀} = c_i = c_j = 1` are real, so this
fixing is consistent with both `d = c` (unitary) and `d = conj c` (antiunitary):
it establishes cocycle coboundary structure, **not** the global sign. No
ℂ-linearity is assumed. -/
theorem diagReducedMap_fixes_three_level
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i j : Fin N}
    (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i₀ + b i + b j) (add3_basis_ne_zero b h0i h0j hij))
      = Projectivization.mk ℂ (b i₀ + b i + b j) (add3_basis_ne_zero b h0i h0j hij) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  set w : EuclideanSpace ℂ (Fin N) := b i₀ + b i + b j with hw_def
  have hwne : w ≠ 0 := add3_basis_ne_zero b h0i h0j hij
  have hwnorm : ‖w‖ ^ 2 = 3 := add3_basis_norm_sq b h0i h0j hij
  have hwk : ∀ k, b.repr w k
      = (if k = i₀ then (1 : ℂ) else 0) + (if k = i then 1 else 0)
        + (if k = j then 1 else 0) := by
    intro k
    rw [hw_def, b.repr_apply_apply, inner_add_right, inner_add_right,
        orthonormal_iff_ite.mp b.orthonormal k i₀,
        orthonormal_iff_ite.mp b.orthonormal k i,
        orthonormal_iff_ite.mp b.orthonormal k j]
  have hwi0 : b.repr w i₀ = 1 := by rw [hwk i₀, if_pos rfl, if_neg h0i, if_neg h0j]; ring
  have hwi : b.repr w i = 1 := by rw [hwk i, if_neg (Ne.symm h0i), if_pos rfl, if_neg hij]; ring
  have hwj : b.repr w j = 1 := by
    rw [hwk j, if_neg (Ne.symm h0j), if_neg (Ne.symm hij), if_pos rfl]; ring
  have hwzero : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → b.repr w k = 0 := by
    intro k hk0 hki hkj; rw [hwk k, if_neg hk0, if_neg hki, if_neg hkj]; ring
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b hfixb hwne k
    rwa [← hφ_def] at h
  have hsupp : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → b.repr φ k = 0 := by
    intro k hk0 hki hkj
    have hm := hcm k
    rw [hwzero k hk0 hki hkj, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  have md : ∀ k, k = i₀ ∨ k = i ∨ k = j → ‖b.repr φ k‖ ^ 2 = ‖φ‖ ^ 2 / 3 := by
    intro k hk
    have hm := hcm k
    have hck : ‖b.repr w k‖ ^ 2 = 1 := by
      rcases hk with h | h | h
      · rw [h, hwi0, norm_one, one_pow]
      · rw [h, hwi, norm_one, one_pow]
      · rw [h, hwj, norm_one, one_pow]
    rw [hck, hwnorm] at hm
    rw [div_eq_div_iff hden (by norm_num : (3 : ℝ) ≠ 0)] at hm
    rw [eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]; linarith [hm]
  have md_i0 := md i₀ (Or.inl rfl)
  have md_i := md i (Or.inr (Or.inl rfl))
  have md_j := md j (Or.inr (Or.inr rfl))
  have ha0 : b.repr φ i₀ ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by norm_num)] at md_i0
    exact absurd md_i0.symm (div_pos hφpos (by norm_num)).ne'
  have hrel_i : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i).re / ‖φ‖ ^ 2
      = ((starRingEnd ℂ) (b.repr w i₀) * b.repr w i).re / ‖w‖ ^ 2 := by
    have h := diagReducedMap_two_level_relphase hf b i₀ h0i hwne
    rwa [← hφ_def] at h
  rw [hwi0, hwi, hwnorm] at hrel_i
  simp only [map_one, mul_one, Complex.one_re] at hrel_i
  have hrel_j : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ j).re / ‖φ‖ ^ 2
      = ((starRingEnd ℂ) (b.repr w i₀) * b.repr w j).re / ‖w‖ ^ 2 := by
    have h := diagReducedMap_two_level_relphase hf b i₀ h0j hwne
    rwa [← hφ_def] at h
  rw [hwi0, hwj, hwnorm] at hrel_j
  simp only [map_one, mul_one, Complex.one_re] at hrel_j
  have hre_i : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i).re = ‖b.repr φ i₀‖ ^ 2 := by
    rw [div_eq_div_iff hden (by norm_num : (3 : ℝ) ≠ 0)] at hrel_i
    rw [md_i0, eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]; linarith [hrel_i]
  have hre_j : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ j).re = ‖b.repr φ i₀‖ ^ 2 := by
    rw [div_eq_div_iff hden (by norm_num : (3 : ℝ) ≠ 0)] at hrel_j
    rw [md_i0, eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]; linarith [hrel_j]
  have hmod_i : ‖b.repr φ i‖ = ‖b.repr φ i₀‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ i)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), md_i, md_i0]
  have hmod_j : ‖b.repr φ j‖ = ‖b.repr φ i₀‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ j)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), md_j, md_i0]
  have hdi : b.repr φ i = b.repr φ i₀ := eq_of_re_conj_mul_eq ha0 hmod_i hre_i
  have hdj : b.repr φ j = b.repr φ i₀ := eq_of_re_conj_mul_eq ha0 hmod_j hre_j
  have hrec : φ = b.repr φ i₀ • w := by
    have h1 := repr_eq_triple_of_support b φ h0i h0j hij hsupp
    rw [hdi, hdj] at h1
    rw [hw_def, smul_add, smul_add]; exact h1
  have hmkeq : Projectivization.mk ℂ φ hφne = Projectivization.mk ℂ w hwne :=
    (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i₀, hrec.symm⟩
  calc diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne :=
        (Projectivization.mk_rep (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne))).symm
    _ = Projectivization.mk ℂ w hwne := hmkeq

/-- **HEADLINE (non-anchored two-level fixing).** The diagonally reduced map fixes
**every** two-level superposition ray `mk (b i + b j)` with `i, j ≠ i₀`,
`i ≠ j` — not only the anchored ones. This upgrades the pairwise relative-phase
leg to unconditional.

Proof. Write `g := diagReducedMap hf b i₀`, `φ := (g (mk w')).rep`,
`w' := b i + b j`. Stage-1 moduli restrict `φ` to support `{i, j}`
(`d_{i₀} = 0`) with `‖d_i‖² = ‖d_j‖² = ‖φ‖²/2`. The **fixed triple ray**
`mk (b i₀ + b i + b j)` (`diagReducedMap_fixes_three_level`) — a probe carrying
both `i` and `j` — used through `transProb_of_fixed` gives the overlap identity
`‖d_i + d_j‖² / (‖φ‖²·3) = ‖1 + 1‖² / (2·3)`, whence
`Re(conj d_i · d_j) = ‖φ‖²/2 = ‖d_i‖²`, saturating the modulus product;
`eq_of_re_conj_mul_eq` forces `d_j = d_i`, so `φ = d_i · w'` and `mk φ = mk w'`.

**Audit note.** The probe `b i₀ + b i + b j` and the source `b i + b j` are
real-coordinate: consistent with both branches. Coboundary structure, not global
sign. No ℂ-linearity assumed. -/
theorem diagReducedMap_fixes_two_level_general
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i j : Fin N}
    (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  set w : EuclideanSpace ℂ (Fin N) := b i + b j with hw_def
  have hwne : w ≠ 0 := add_basis_ne_zero b hij
  have hwnorm : ‖w‖ ^ 2 = 2 := add_basis_norm_sq b hij
  have hwk : ∀ k, b.repr w k = (if k = i then (1 : ℂ) else 0) + (if k = j then 1 else 0) := by
    intro k
    rw [hw_def, b.repr_apply_apply, inner_add_right,
        orthonormal_iff_ite.mp b.orthonormal k i, orthonormal_iff_ite.mp b.orthonormal k j]
  have hwi : b.repr w i = 1 := by rw [hwk i, if_pos rfl, if_neg hij]; ring
  have hwj : b.repr w j = 1 := by rw [hwk j, if_neg (Ne.symm hij), if_pos rfl]; ring
  have hwi0 : b.repr w i₀ = 0 := by rw [hwk i₀, if_neg h0i, if_neg h0j]; ring
  have hwzero : ∀ k, k ≠ i → k ≠ j → b.repr w k = 0 := by
    intro k hki hkj; rw [hwk k, if_neg hki, if_neg hkj]; ring
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b hfixb hwne k
    rwa [← hφ_def] at h
  have hsupp : ∀ k, k ≠ i → k ≠ j → b.repr φ k = 0 := by
    intro k hki hkj
    have hm := hcm k
    rw [hwzero k hki hkj, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  have hd0 : b.repr φ i₀ = 0 := hsupp i₀ h0i h0j
  have md : ∀ k, k = i ∨ k = j → ‖b.repr φ k‖ ^ 2 = ‖φ‖ ^ 2 / 2 := by
    intro k hk
    have hm := hcm k
    have hck : ‖b.repr w k‖ ^ 2 = 1 := by
      rcases hk with h | h
      · rw [h, hwi, norm_one, one_pow]
      · rw [h, hwj, norm_one, one_pow]
    rw [hck, hwnorm] at hm
    rw [div_eq_div_iff hden (by norm_num : (2 : ℝ) ≠ 0)] at hm
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]; linarith [hm]
  have md_i := md i (Or.inl rfl)
  have md_j := md j (Or.inr rfl)
  have ha_i : b.repr φ i ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by norm_num)] at md_i
    exact absurd md_i.symm (div_pos hφpos (by norm_num)).ne'
  -- triple-support probe overlap
  have hfix3 := diagReducedMap_fixes_three_level hf b h0i h0j hij
  have hoverlap := hg.transProb_of_fixed hfix3 (Projectivization.mk ℂ w hwne)
  rw [show diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne) = Projectivization.mk ℂ φ hφne
        from (Projectivization.mk_rep
          (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne))).symm,
      transProb_three_level b hφne h0i h0j hij,
      transProb_three_level b hwne h0i h0j hij,
      hd0, hwi0, hwi, hwj, hwnorm, zero_add, zero_add] at hoverlap
  have h11 : ‖(1 : ℂ) + 1‖ ^ 2 = 4 := by
    rw [cnorm_add_sq]
    simp only [norm_one, one_pow, map_one, mul_one, Complex.one_re]; norm_num
  rw [h11] at hoverlap
  have hDφ : ‖φ‖ ^ 2 * 3 ≠ 0 := mul_ne_zero hden (by norm_num)
  have hcross := (div_eq_div_iff hDφ (by norm_num : (2 : ℝ) * 3 ≠ 0)).mp hoverlap
  rw [cnorm_add_sq, md_i, md_j] at hcross
  have hRe : ((starRingEnd ℂ) (b.repr φ i) * b.repr φ j).re = ‖b.repr φ i‖ ^ 2 := by
    rw [md_i, eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]; nlinarith [hcross]
  have hmod_ij : ‖b.repr φ j‖ = ‖b.repr φ i‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ j)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i)), md_j, md_i]
  have hdj : b.repr φ j = b.repr φ i := eq_of_re_conj_mul_eq ha_i hmod_ij hRe
  have hrec : φ = b.repr φ i • w := by
    have h1 := repr_eq_pair_of_support b φ hij hsupp
    rw [hdj] at h1
    rw [hw_def, smul_add]; exact h1
  have hmkeq : Projectivization.mk ℂ φ hφne = Projectivization.mk ℂ w hwne :=
    (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i, hrec.symm⟩
  calc diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne :=
        (Projectivization.mk_rep (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne))).symm
    _ = Projectivization.mk ℂ w hwne := hmkeq

/-- **HEADLINE (unconditional pairwise relative phase, the 2-cocycle coboundary).**
For **any** distinct `i, j ≠ i₀`, the diagonally reduced map preserves the real
part of the relative phase between coordinates `i` and `j`:
`Re(conj d_i · d_j) / ‖φ‖² = Re(conj c_i · c_j) / ‖ψ‖²`, for every source ray
`mk ψ`. Discharges the `hfix` hypothesis of
`diagReducedMap_pairwise_relphase_of_fixed` via the non-anchored two-level fixing
`diagReducedMap_fixes_two_level_general`.

Together with `diagReducedMap_two_level_relphase` (the anchored legs
`(i₀, k)`), the pairwise legs `(i, j)` here give the full **coboundary
structure** of the phase 2-cocycle — the real-part relations
`Re(c̄_i d_j) = Re(c̄_i c_j)·‖φ‖²/‖ψ‖²` for all pairs — with the ± sign of the
imaginary parts still free (the ℤ/2 datum resolved only by piece 3). No
ℂ-linearity is assumed. -/
theorem diagReducedMap_pairwise_relphase
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (h0i : i₀ ≠ i) (h0j : i₀ ≠ j) (hij : i ≠ j)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).re / ‖ψ‖ ^ 2 :=
  diagReducedMap_pairwise_relphase_of_fixed hf b i₀ hij
    (diagReducedMap_fixes_two_level_general hf b h0i h0j hij) hψ

/-! ## Stage 3 piece 3 (W5): the complex probe, the global sign, and the dichotomy

Piece 3 is the finish. Pieces 1–2 established the phase-cocycle **coboundary
structure** through **real-coordinate** probes, which cannot see the global
unitary/antiunitary sign (they are fixed by the identity and by coordinatewise
conjugation alike). Piece 3 introduces the **complex probe** `mk (b i₀ + I • b i)`,
whose ray is *not* conjugation-invariant, so it **distinguishes** the two branches,
and assembles the global dichotomy.

The layout:

* **Imaginary relative phase.** The `I`-probe overlap
  (`transProb_two_level_I`, `transProb_two_level_negI`) pins the *imaginary*
  part of the relative phase, the datum invisible to piece 2:
  `two_level_imrelphase_of_fixes` (from a fixed complex ray) and
  `two_level_imrelphase_of_flips` (from a flipped one, the antiunitary reading).
* **Reconstruction.** Given a `TransProbPreserving` map fixing every basis ray,
  every real two-level ray `mk (b i + b j)`, and every complex two-level ray
  `mk (b i + I • b j)`, the full Gram datum `conj dᵢ · dⱼ · ‖ψ‖² =
  conj cᵢ · cⱼ · ‖φ‖²` is pinned, forcing `φ = λ • ψ`, i.e. the map is the
  **identity on rays** (`eq_id_of_fixes_all_two_level`). If instead the complex
  rays are *flipped*, the datum conjugates and the map is **coordinatewise
  conjugation** in the basis `b` (`eq_bconj_of_flips_complex`). ℂ-linearity is an
  **output** of this reconstruction, never an input.
* **The complex probe local dichotomy.** For each `i ≠ i₀` the diagonally reduced
  map sends `mk (b i₀ + I • b i)` to `mk (b i₀ + I • b i)` (plus branch) or
  `mk (b i₀ - I • b i)` (minus branch): the anchored real-part relation forces the
  image phase to have zero real part, and unit modulus leaves exactly `± I`
  (`diagReducedMap_complex_probe`).

No ℂ-linearity is assumed anywhere below. -/

/-- The imaginary-part conversion `(x · I · conj y).re = (conj x · y).im`,
a coordinate identity in `ℂ`. -/
lemma re_mul_I_eq_im (x y : ℂ) :
    (x * Complex.I * (starRingEnd ℂ) y).re = ((starRingEnd ℂ) x * y).im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]; ring

/-- **Complex "difference" parallelogram.** `‖A - I·B‖² = ‖A‖² + ‖B‖²
+ 2·(conj A · B).im`. Pure real-coordinate algebra via `Complex.normSq`. -/
lemma cnorm_sub_I_sq (A B : ℂ) :
    ‖A - Complex.I * B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * ((starRingEnd ℂ) A * B).im := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Complex "sum" parallelogram with `I`.** `‖A + I·B‖² = ‖A‖² + ‖B‖²
- 2·(conj A · B).im`. Pure real-coordinate algebra via `Complex.normSq`. -/
lemma cnorm_add_I_sq (A B : ℂ) :
    ‖A + Complex.I * B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * ((starRingEnd ℂ) A * B).im := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ### The `I`-probe `b i + I • b j` -/

/-- Squared norm of the `I`-probe: `‖b i + I • b j‖² = 2` (Pythagoras,
`‖I • b j‖ = ‖b j‖ = 1`). -/
lemma Iadd_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    ‖(b i + Complex.I • b j : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
  have hperp : (inner ℂ (b i) (Complex.I • b j) : ℂ) = 0 := by
    rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j, if_neg hij, mul_zero]
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i) (Complex.I • b j) hperp,
      b.orthonormal.norm_eq_one i, norm_smul, Complex.norm_I, one_mul,
      b.orthonormal.norm_eq_one j]
  norm_num

/-- The `I`-probe is nonzero (norm² = 2). -/
lemma Iadd_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    (b i + Complex.I • b j : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have hn := Iadd_basis_norm_sq b hij
  rw [h, norm_zero, zero_pow (by norm_num)] at hn
  norm_num at hn

/-- Inner product of `ψ` with the `I`-probe:
`⟪ψ, b i + I • b j⟫ = conj cᵢ + I · conj cⱼ`. -/
lemma inner_Iadd_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i j : Fin N) :
    (inner ℂ ψ (b i + Complex.I • b j) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) + Complex.I * (starRingEnd ℂ) (b.repr ψ j) := by
  rw [inner_add_right, inner_smul_right, inner_eq_conj_repr b ψ i, inner_eq_conj_repr b ψ j]

/-- **`I`-probe overlap.** `transProb (mk ψ) (mk (b i + I • b j))
= ‖cᵢ - I · cⱼ‖² / (‖ψ‖² · 2)`. The numerator conjugate identity
`conj cᵢ + I · conj cⱼ = conj (cᵢ - I · cⱼ)` plus `RCLike.norm_conj` puts it in the
`c`-coordinate form. -/
lemma transProb_two_level_I
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) {i j : Fin N} (hij : i ≠ j) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = ‖b.repr ψ i - Complex.I * b.repr ψ j‖ ^ 2 / (‖ψ‖ ^ 2 * 2) := by
  have hnum : ((starRingEnd ℂ) (b.repr ψ i) + Complex.I * (starRingEnd ℂ) (b.repr ψ j))
      = (starRingEnd ℂ) (b.repr ψ i - Complex.I * b.repr ψ j) := by
    rw [map_sub, map_mul, Complex.conj_I]; ring
  rw [transProb_mk hψ (Iadd_basis_ne_zero b hij)]
  unfold transProbVec
  rw [inner_Iadd_basis, Iadd_basis_norm_sq b hij, hnum, RCLike.norm_conj]

/-- **Imaginary relative-phase constraint (fixed complex ray).** Let `g` be
`TransProbPreserving`, fixing every basis ray and the complex two-level ray
`mk (b i + I • b j)`. Writing `g (mk ψ) = mk φ`, the *imaginary* part of the
relative phase is preserved: `Im(conj dᵢ · dⱼ) / ‖φ‖² = Im(conj cᵢ · cⱼ) / ‖ψ‖²`.
The `I`-probe is *not* conjugation-invariant, so this is the datum piece 2 could
not reach. Pure overlap algebra; no ℂ-linearity. -/
theorem two_level_imrelphase_of_fixes
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    {i j : Fin N} (hij : i ≠ j)
    (hfixI : g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (g (Projectivization.mk ℂ ψ hψ)).rep j).im
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).im / ‖ψ‖ ^ 2 := by
  have hA := hg.transProb_of_fixed hfixI (Projectivization.mk ℂ ψ hψ)
  rw [transProb_two_level_I b hψ hij] at hA
  have md0 := coord_modulus_of_fixes_basis hg b hfixb hψ i
  have mdi := coord_modulus_of_fixes_basis hg b hfixb hψ j
  set q := g (Projectivization.mk ℂ ψ hψ) with hq
  have hLHS : transProb q
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = ‖b.repr q.rep i - Complex.I * b.repr q.rep j‖ ^ 2 / (‖q.rep‖ ^ 2 * 2) := by
    conv_lhs => rw [← q.mk_rep]
    exact transProb_two_level_I b q.rep_nonzero hij
  rw [hLHS] at hA
  have hDφ : ‖q.rep‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr q.rep_nonzero)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hcross := (div_eq_div_iff (mul_ne_zero hDφ (by norm_num : (2 : ℝ) ≠ 0))
    (mul_ne_zero hDψ (by norm_num : (2 : ℝ) ≠ 0))).mp hA
  rw [cnorm_sub_I_sq, cnorm_sub_I_sq] at hcross
  have hm0 := (div_eq_div_iff hDφ hDψ).mp md0
  have hmi := (div_eq_div_iff hDφ hDψ).mp mdi
  rw [div_eq_div_iff hDφ hDψ]
  linear_combination (1 / 4 : ℝ) * hcross - (1 / 2 : ℝ) * hm0 - (1 / 2 : ℝ) * hmi

/-! ### The `-I`-probe `b i - I • b j` (the flipped complex ray) -/

/-- Squared norm of the `-I`-probe: `‖b i - I • b j‖² = 2`. -/
lemma subI_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    ‖(b i - Complex.I • b j : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
  have hperp : (inner ℂ (b i) (-(Complex.I • b j)) : ℂ) = 0 := by
    rw [inner_neg_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j,
        if_neg hij, mul_zero, neg_zero]
  rw [sub_eq_add_neg, sq,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i) (-(Complex.I • b j)) hperp,
      b.orthonormal.norm_eq_one i, norm_neg, norm_smul, Complex.norm_I, one_mul,
      b.orthonormal.norm_eq_one j]
  norm_num

/-- The `-I`-probe is nonzero (norm² = 2). -/
lemma subI_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    (b i - Complex.I • b j : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have hn := subI_basis_norm_sq b hij
  rw [h, norm_zero, zero_pow (by norm_num)] at hn
  norm_num at hn

/-- Inner product of `ψ` with the `-I`-probe:
`⟪ψ, b i - I • b j⟫ = conj cᵢ - I · conj cⱼ`. -/
lemma inner_subI_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i j : Fin N) :
    (inner ℂ ψ (b i - Complex.I • b j) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) - Complex.I * (starRingEnd ℂ) (b.repr ψ j) := by
  rw [inner_sub_right, inner_smul_right, inner_eq_conj_repr b ψ i, inner_eq_conj_repr b ψ j]

/-- **`-I`-probe overlap.** `transProb (mk ψ) (mk (b i - I • b j))
= ‖cᵢ + I · cⱼ‖² / (‖ψ‖² · 2)`. -/
lemma transProb_two_level_negI
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) {i j : Fin N} (hij : i ≠ j) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
      = ‖b.repr ψ i + Complex.I * b.repr ψ j‖ ^ 2 / (‖ψ‖ ^ 2 * 2) := by
  have hnum : ((starRingEnd ℂ) (b.repr ψ i) - Complex.I * (starRingEnd ℂ) (b.repr ψ j))
      = (starRingEnd ℂ) (b.repr ψ i + Complex.I * b.repr ψ j) := by
    rw [map_add, map_mul, Complex.conj_I]; ring
  rw [transProb_mk hψ (subI_basis_ne_zero b hij)]
  unfold transProbVec
  rw [inner_subI_basis, subI_basis_norm_sq b hij, hnum, RCLike.norm_conj]

/-- **Imaginary relative-phase constraint (flipped complex ray).** If `g`
`TransProbPreserving` fixes every basis ray and *flips* the complex two-level ray,
`g (mk (b i + I • b j)) = mk (b i - I • b j)`, then the imaginary part of the
relative phase is **negated**: `Im(conj dᵢ · dⱼ) / ‖φ‖² = -Im(conj cᵢ · cⱼ) / ‖ψ‖²`.
This is the antiunitary reading. No ℂ-linearity. -/
theorem two_level_imrelphase_of_flips
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    {i j : Fin N} (hij : i ≠ j)
    (hflipI : g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (g (Projectivization.mk ℂ ψ hψ)).rep j).im
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = (-((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).im) / ‖ψ‖ ^ 2 := by
  have hA := hg (Projectivization.mk ℂ ψ hψ)
    (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
  rw [hflipI, transProb_two_level_I b hψ hij] at hA
  have md0 := coord_modulus_of_fixes_basis hg b hfixb hψ i
  have mdi := coord_modulus_of_fixes_basis hg b hfixb hψ j
  set q := g (Projectivization.mk ℂ ψ hψ) with hq
  have hLHS : transProb q
        (Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
      = ‖b.repr q.rep i + Complex.I * b.repr q.rep j‖ ^ 2 / (‖q.rep‖ ^ 2 * 2) := by
    conv_lhs => rw [← q.mk_rep]
    exact transProb_two_level_negI b q.rep_nonzero hij
  rw [hLHS] at hA
  have hDφ : ‖q.rep‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr q.rep_nonzero)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hcross := (div_eq_div_iff (mul_ne_zero hDφ (by norm_num : (2 : ℝ) ≠ 0))
    (mul_ne_zero hDψ (by norm_num : (2 : ℝ) ≠ 0))).mp hA
  rw [cnorm_add_I_sq, cnorm_sub_I_sq] at hcross
  have hm0 := (div_eq_div_iff hDφ hDψ).mp md0
  have hmi := (div_eq_div_iff hDφ hDψ).mp mdi
  rw [div_eq_div_iff hDφ hDψ]
  linear_combination (-(1 / 4) : ℝ) * hcross + (1 / 2 : ℝ) * hm0 + (1 / 2 : ℝ) * hmi

/-! ### Reconstruction: from the Gram datum to the identity / conjugation -/

/-- Real part of a product with a real scalar on the right: `(z · r).re = z.re · r`. -/
lemma mul_ofReal_re (z : ℂ) (r : ℝ) : (z * (r : ℂ)).re = z.re * r := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Imaginary part of a product with a real scalar on the right: `(z · r).im = z.im · r`. -/
lemma mul_ofReal_im (z : ℂ) (r : ℝ) : (z * (r : ℂ)).im = z.im * r := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

/-- **Reconstruction (unitary branch).** A `TransProbPreserving` map `g` fixing
every basis ray, every real two-level ray `mk (b i + b j)`, and every complex
two-level ray `mk (b i + I • b j)` is the **identity on rays**:
`g (mk ψ) = mk ψ` for every `ψ ≠ 0`.

The real relations (`two_level_relphase_of_fixes`) and the imaginary relations
(`two_level_imrelphase_of_fixes`) together pin the full Gram datum
`conj dᵢ · dⱼ · ‖ψ‖² = conj cᵢ · cⱼ · ‖φ‖²` for every pair; taking a reference
index `i₁` with `c_{i₁} ≠ 0` gives `dⱼ = λ · cⱼ` with `λ` fixed, so `φ = λ • ψ`.
**ℂ-linearity is an output here, not an input.** -/
theorem eq_id_of_fixes_all_two_level
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    (hR : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
    (hI : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    g (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ ψ hψ := by
  set φ := (g (Projectivization.mk ℂ ψ hψ)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hφne)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  -- reference index with nonzero source coordinate
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, b.repr ψ i₁ ≠ 0 := by
    by_contra h; push Not at h
    apply hψ
    have hsum := b.sum_repr ψ
    rw [← hsum]; exact Finset.sum_eq_zero (fun j _ => by rw [h j, zero_smul])
  -- the full Gram datum
  have key : ∀ j, (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ j * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ j * ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rcases eq_or_ne i₁ j with h | h
    · subst h
      have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
      rw [← hφ_def] at hm
      have hmc := (div_eq_div_iff hDφ hDψ).mp hm
      have e1 : (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ i₁ = ((‖b.repr φ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      have e2 : (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁ = ((‖b.repr ψ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      rw [e1, e2]; exact_mod_cast hmc
    · have hre := two_level_relphase_of_fixes hg b hfixb h (hR i₁ j h) hψ
      have him := two_level_imrelphase_of_fixes hg b hfixb h (hI i₁ j h) hψ
      rw [← hφ_def] at hre him
      have hrec := (div_eq_div_iff hDφ hDψ).mp hre
      have himc := (div_eq_div_iff hDφ hDψ).mp him
      apply Complex.ext
      · rw [mul_ofReal_re, mul_ofReal_re]; exact hrec
      · rw [mul_ofReal_im, mul_ofReal_im]; exact himc
  -- `d_{i₁} ≠ 0`
  have hd1 : b.repr φ i₁ ≠ 0 := by
    have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
    rw [← hφ_def] at hm
    intro h0
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr ψ i₁‖ ^ 2 / ‖ψ‖ ^ 2 = 0 := hm.symm
    rcases div_eq_zero_iff.mp hz with hh | hh
    · exact hi₁ (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hh))
    · exact hDψ hh
  set lam : ℂ := (starRingEnd ℂ) (b.repr ψ i₁) * ((‖φ‖ ^ 2 : ℝ) : ℂ)
      / ((starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ)) with hlam
  have hden' : (starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by simpa using hd1) (by exact_mod_cast hDψ)
  have hcoord : ∀ j, b.repr φ j = lam * b.repr ψ j := by
    intro j
    rw [hlam, div_mul_eq_mul_div, eq_div_iff hden']
    linear_combination (key j)
  have hlamne : lam ≠ 0 := by
    rw [hlam]
    apply div_ne_zero
    · exact mul_ne_zero (by simpa using hi₁) (by exact_mod_cast hDφ)
    · exact hden'
  have hφlam : φ = lam • ψ := by
    rw [← b.sum_repr φ, ← b.sum_repr ψ, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hcoord j, smul_smul]
  have hmkψ : g (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ φ hφne :=
    (Projectivization.mk_rep _).symm
  rw [hmkψ]
  exact (Projectivization.mk_eq_mk_iff' ℂ φ ψ hφne hψ).mpr ⟨lam, hφlam.symm⟩

/-- Coordinatewise complex conjugation **in the basis `b`**:
`bConjVec b ψ = ∑ⱼ conj(b.repr ψ j) • b j`. Its `k`-th coordinate is
`conj(b.repr ψ k)` (`repr_bConjVec`). For the standard basis this is `conjVec`. -/
noncomputable def bConjVec
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  ∑ j, (starRingEnd ℂ) (b.repr ψ j) • b j

/-- The `k`-th coordinate of `bConjVec b ψ` is `conj (b.repr ψ k)`. -/
lemma repr_bConjVec
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (k : Fin N) :
    b.repr (bConjVec b ψ) k = (starRingEnd ℂ) (b.repr ψ k) := by
  rw [b.repr_apply_apply]
  unfold bConjVec
  rw [inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k k, if_pos rfl, mul_one]
  · intro j _ hjk
    rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k j, if_neg (Ne.symm hjk),
        mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `bConjVec b ψ` is nonzero when `ψ` is (some conjugate coordinate is nonzero). -/
lemma bConjVec_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) : bConjVec b ψ ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, b.repr ψ k ≠ 0 := by
    by_contra h; push Not at h; apply hψ
    rw [← b.sum_repr ψ]; exact Finset.sum_eq_zero (fun j _ => by rw [h j, zero_smul])
  intro h0
  have hk0 : (starRingEnd ℂ) (b.repr ψ k) = 0 := by
    rw [← repr_bConjVec b ψ k, h0]; simp
  exact hk (by simpa using hk0)

/-- A unit-modulus complex number with zero real part is `± I`. Squaring the norm,
`ε.im² = 1`, so `ε.im = ±1` and `ε = ⟨0, ±1⟩`. -/
lemma unit_re_zero_eq_I_or_negI {ε : ℂ} (h1 : ‖ε‖ = 1) (h2 : ε.re = 0) :
    ε = Complex.I ∨ ε = -Complex.I := by
  have hkey : ε.re * ε.re + ε.im * ε.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [h2] at hkey
  have him : ε.im = 1 ∨ ε.im = -1 := by
    have hii : ε.im * ε.im = 1 := by linarith
    exact mul_self_eq_one_iff.mp hii
  rcases him with h | h
  · left; apply Complex.ext
    · rw [h2, Complex.I_re]
    · rw [h, Complex.I_im]
  · right; apply Complex.ext
    · rw [h2, Complex.neg_re, Complex.I_re, neg_zero]
    · rw [h, Complex.neg_im, Complex.I_im]

/-- **Reconstruction (antiunitary branch).** A `TransProbPreserving` map `g` fixing
every basis ray, every real two-level ray `mk (b i + b j)`, and *flipping* every
complex two-level ray, `g (mk (b i + I • b j)) = mk (b i - I • b j)`, is
**coordinatewise conjugation** in the basis `b`:
`g (mk ψ) = mk (bConjVec b ψ)` for every `ψ ≠ 0`.

The real relations survive, but the imaginary relations are negated
(`two_level_imrelphase_of_flips`), conjugating the Gram datum to
`conj dᵢ · dⱼ · ‖ψ‖² = cᵢ · conj cⱼ · ‖φ‖²`, so `dⱼ = μ · conj cⱼ` and
`φ = μ • bConjVec b ψ`. **No ℂ-linearity is assumed**; this is the genuine
antiunitary branch of the Wigner disjunction. -/
theorem eq_bconj_of_flips_complex
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    (hR : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
    (hflip : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    g (Projectivization.mk ℂ ψ hψ)
      = Projectivization.mk ℂ (bConjVec b ψ) (bConjVec_ne_zero b hψ) := by
  set φ := (g (Projectivization.mk ℂ ψ hψ)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hφne)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, b.repr ψ i₁ ≠ 0 := by
    by_contra h; push Not at h
    apply hψ
    rw [← b.sum_repr ψ]; exact Finset.sum_eq_zero (fun j _ => by rw [h j, zero_smul])
  have key : ∀ j, (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ j * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) ((starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ j) * ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rcases eq_or_ne i₁ j with h | h
    · subst h
      have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
      rw [← hφ_def] at hm
      have hmc := (div_eq_div_iff hDφ hDψ).mp hm
      have e1 : (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ i₁ = ((‖b.repr φ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      have e2 : (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁ = ((‖b.repr ψ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      have hconj_real : (starRingEnd ℂ) ((starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁)
          = (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁ := by
        rw [map_mul, Complex.conj_conj, mul_comm]
      rw [e1, hconj_real, e2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
      exact hmc
    · have hre := two_level_relphase_of_fixes hg b hfixb h (hR i₁ j h) hψ
      have him := two_level_imrelphase_of_flips hg b hfixb h (hflip i₁ j h) hψ
      rw [← hφ_def] at hre him
      have hrec := (div_eq_div_iff hDφ hDψ).mp hre
      have himc := (div_eq_div_iff hDφ hDψ).mp him
      apply Complex.ext
      · rw [mul_ofReal_re, mul_ofReal_re, Complex.conj_re]; exact hrec
      · rw [mul_ofReal_im, mul_ofReal_im, Complex.conj_im]; exact himc
  have hd1 : b.repr φ i₁ ≠ 0 := by
    have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
    rw [← hφ_def] at hm
    intro h0
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr ψ i₁‖ ^ 2 / ‖ψ‖ ^ 2 = 0 := hm.symm
    rcases div_eq_zero_iff.mp hz with hh | hh
    · exact hi₁ (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hh))
    · exact hDψ hh
  set mu : ℂ := b.repr ψ i₁ * ((‖φ‖ ^ 2 : ℝ) : ℂ)
      / ((starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ)) with hmu
  have hden' : (starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by simpa using hd1) (by exact_mod_cast hDψ)
  have hcoord : ∀ j, b.repr φ j = mu * (starRingEnd ℂ) (b.repr ψ j) := by
    intro j
    have hk : (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ j * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
        = b.repr ψ i₁ * (starRingEnd ℂ) (b.repr ψ j) * ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
      have := key j
      rwa [map_mul, Complex.conj_conj] at this
    rw [hmu, div_mul_eq_mul_div, eq_div_iff hden']
    linear_combination hk
  have hmune : mu ≠ 0 := by
    rw [hmu]
    exact div_ne_zero (mul_ne_zero hi₁ (by exact_mod_cast hDφ)) hden'
  have hφmu : φ = mu • bConjVec b ψ := by
    rw [← b.sum_repr φ]
    unfold bConjVec
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hcoord j, smul_smul]
  have hmkψ : g (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ φ hφne :=
    (Projectivization.mk_rep _).symm
  rw [hmkψ]
  exact (Projectivization.mk_eq_mk_iff' ℂ φ (bConjVec b ψ) hφne (bConjVec_ne_zero b hψ)).mpr
    ⟨mu, hφmu.symm⟩

/-! ### The complex probe: the branch-distinguishing local dichotomy -/

/-- **HEADLINE (the complex probe).** For `i ≠ i₀` the diagonally reduced map sends
the complex probe ray `mk (b i₀ + I • b i)` to *either* itself (**plus** branch)
*or* `mk (b i₀ - I • b i)` (**minus** branch).

Unlike the real probes of pieces 1–2, the complex probe ray is *not* invariant
under coordinatewise conjugation (`conjVec (b i₀ + I • b i) = b i₀ - I • b i`), so
it **distinguishes** the unitary branch (`+`) from the antiunitary branch (`-`).

Proof. Stage-1 moduli restrict the image `φ` to support `{i₀, i}` with equal
coordinate moduli. The anchored real relation
(`diagReducedMap_two_level_relphase`) at the source coordinates `c_{i₀} = 1`,
`c_i = I` gives `Re(conj d_{i₀} · d_i) = 0`, so the ratio `ε := d_i / d_{i₀}` has
zero real part and unit modulus, hence `ε = ± I` (`unit_re_zero_eq_I_or_negI`).
The two signs are the two branches. No ℂ-linearity is assumed. -/
theorem diagReducedMap_complex_probe
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i : Fin N} (hii : i₀ ≠ i) :
    diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i₀ + Complex.I • b i) (Iadd_basis_ne_zero b hii))
      = Projectivization.mk ℂ (b i₀ + Complex.I • b i) (Iadd_basis_ne_zero b hii)
    ∨ diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i₀ + Complex.I • b i) (Iadd_basis_ne_zero b hii))
      = Projectivization.mk ℂ (b i₀ - Complex.I • b i) (subI_basis_ne_zero b hii) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  set w : EuclideanSpace ℂ (Fin N) := b i₀ + Complex.I • b i with hw
  have hwne : w ≠ 0 := Iadd_basis_ne_zero b hii
  have hwnorm : ‖w‖ ^ 2 = 2 := Iadd_basis_norm_sq b hii
  -- coordinates of `w`
  have hw_i0 : b.repr w i₀ = 1 := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal i₀ i₀, if_pos rfl,
        orthonormal_iff_ite.mp b.orthonormal i₀ i, if_neg hii, mul_zero, add_zero]
  have hw_i : b.repr w i = Complex.I := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal i i₀, if_neg (Ne.symm hii),
        orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl, mul_one, zero_add]
  have hw_zero : ∀ k, k ≠ i₀ → k ≠ i → b.repr w k = 0 := by
    intro k hk0 hki
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal k i₀, if_neg hk0,
        orthonormal_iff_ite.mp b.orthonormal k i, if_neg hki, mul_zero, add_zero]
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b hfixb hwne k
    rwa [← hφ] at h
  -- support of `φ` is `{i₀, i}`
  have hsupp : ∀ k, k ≠ i₀ → k ≠ i → b.repr φ k = 0 := by
    intro k hk0 hki
    have hm := hcm k
    rw [hw_zero k hk0 hki, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  -- `d_{i₀} ≠ 0` and modulus equality
  have ha : b.repr φ i₀ ≠ 0 := by
    intro h0
    have hm := hcm i₀
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div, hw_i0, norm_one, one_pow, hwnorm] at hm
    norm_num at hm
  have hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖ := by
    have hi := hcm i
    have hi0 := hcm i₀
    rw [hw_i, Complex.norm_I, one_pow, hwnorm] at hi
    rw [hw_i0, norm_one, one_pow, hwnorm] at hi0
    have hd := hi.trans hi0.symm
    rw [div_eq_div_iff hden hden] at hd
    have heq2 : ‖b.repr φ i‖ ^ 2 = ‖b.repr φ i₀‖ ^ 2 := mul_right_cancel₀ hden hd
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ i)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), heq2]
  -- the phase `ε := d_i / d_{i₀}` and `d_i = ε · d_{i₀}`
  set ε : ℂ := b.repr φ i / b.repr φ i₀ with hε
  have hεnorm : ‖ε‖ = 1 := by rw [hε, norm_div, hmod, div_self (norm_ne_zero_iff.mpr ha)]
  have hdi : b.repr φ i = ε * b.repr φ i₀ := by rw [hε, div_mul_cancel₀ _ ha]
  -- the anchored real relation forces `Re ε = 0`
  have hrel := diagReducedMap_two_level_relphase hf b i₀ hii hwne
  rw [← hφ, hw_i0, hw_i, hwnorm, map_one, one_mul, Complex.I_re, zero_div] at hrel
  have hRe : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i).re = 0 := by
    rcases div_eq_zero_iff.mp hrel with h | h
    · exact h
    · exact absurd h hden
  have hεre : ε.re = 0 := by
    rw [hdi] at hRe
    have hr : (starRingEnd ℂ) (b.repr φ i₀) * (ε * b.repr φ i₀)
        = ε * ((‖b.repr φ i₀‖ ^ 2 : ℝ) : ℂ) := by
      rw [show (starRingEnd ℂ) (b.repr φ i₀) * (ε * b.repr φ i₀)
            = ε * ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i₀) from by ring, RCLike.conj_mul]
      norm_cast
    rw [hr, mul_ofReal_re] at hRe
    have hpos : (0 : ℝ) < ‖b.repr φ i₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
    exact (mul_eq_zero.mp hRe).resolve_right (ne_of_gt hpos)
  -- the reconstruction of `mk w`'s image and the ± dichotomy
  have hgw : diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne := (Projectivization.mk_rep _).symm
  have hpair : φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i :=
    repr_eq_pair_of_support b φ hii hsupp
  rcases unit_re_zero_eq_I_or_negI hεnorm hεre with hI | hnI
  · left
    have hval : b.repr φ i₀ • w = φ := by
      conv_rhs => rw [hpair, hdi, hI]
      rw [hw]; module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i₀, hval⟩
  · right
    have hval : b.repr φ i₀ • (b i₀ - Complex.I • b i) = φ := by
      conv_rhs => rw [hpair, hdi, hnI]
      module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ (b i₀ - Complex.I • b i) hφne
      (subI_basis_ne_zero b hii)).mpr ⟨b.repr φ i₀, hval⟩

/-! ### The reduced-map dichotomy (conditional on the global complex sign) -/

/-- The diagonally reduced map fixes **every** real two-level ray `mk (b i + b j)`,
`i ≠ j` (anchored via `diagReducedMap_fixes_two_level`, non-anchored via
`diagReducedMap_fixes_two_level_general`, with an `add_comm` swap for the `j = i₀`
case). Discharges the `hR` hypothesis of the reconstruction lemmas for the
concrete diagonally reduced map. -/
theorem diagReducedMap_fixes_real_all
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    ∀ i j (hij : i ≠ j),
      diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij) := by
  intro i j hij
  rcases eq_or_ne i i₀ with rfl | hi
  · exact diagReducedMap_fixes_two_level hf b hij
  · rcases eq_or_ne j i₀ with rfl | hj
    · have hfix := diagReducedMap_fixes_two_level hf b (Ne.symm hij)
      have heq : Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij)
          = Projectivization.mk ℂ (b j + b i) (add_basis_ne_zero b (Ne.symm hij)) :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul, add_comm]⟩
      rw [heq, hfix]
    · exact diagReducedMap_fixes_two_level_general hf b (Ne.symm hi) (Ne.symm hj) hij

/-- **The reduced-map Wigner dichotomy (conditional on the global sign).**
Given the **global complex-sign closure** `hsign` — either the diagonally reduced
map `g := diagReducedMap hf b i₀` fixes *every* complex two-level ray
`mk (b i + I • b j)`, or it flips *every* one to `mk (b i - I • b j)` — the map is
**globally** the identity on rays, or **globally** coordinatewise conjugation in
the basis `b`:

* fixes-all branch ⟹ `g (mk ψ) = mk ψ` for all `ψ` (the **unitary** class);
* flips-all branch ⟹ `g (mk ψ) = mk (bConjVec b ψ)` for all `ψ` (the **antiunitary**
  class).

The real fixings are discharged internally (`diagReducedMap_fixes_real_all`); the
two disjuncts feed the two reconstruction lemmas. **The antiunitary branch is
genuinely present** and **ℂ-linearity is an output**, never assumed. The single
residual to an unconditional Wigner converse is `hsign`, for which
`diagReducedMap_complex_probe` supplies the per-pair `± I` datum; see the
`Stage 3 (residual)` note. -/
theorem diagReducedMap_dichotomy_of_complexSign
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    (hsign :
      (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      ∨ (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))) :
    (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ ψ hψ)
    ∨ (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)
          = Projectivization.mk ℂ (bConjVec b ψ) (bConjVec_ne_zero b hψ)) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hR := diagReducedMap_fixes_real_all hf b i₀
  rcases hsign with hfix | hflip
  · exact Or.inl (fun ψ hψ => eq_id_of_fixes_all_two_level hg b hfixb hR hfix hψ)
  · exact Or.inr (fun ψ hψ => eq_bconj_of_flips_complex hg b hfixb hR hflip hψ)

theorem diagReducedMap_relphase_all
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).re / ‖ψ‖ ^ 2 :=
  two_level_relphase_of_fixes (diagReducedMap_transProbPreserving hf b i₀) b
    (fun k => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k)
    hij (diagReducedMap_fixes_real_all hf b i₀ i j hij) hψ

theorem diagReducedMap_complex_probe_general
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) :
    diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij)
    ∨ diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  set w : EuclideanSpace ℂ (Fin N) := b i + Complex.I • b j with hw
  have hwne : w ≠ 0 := Iadd_basis_ne_zero b hij
  have hwnorm : ‖w‖ ^ 2 = 2 := Iadd_basis_norm_sq b hij
  have hw_i : b.repr w i = 1 := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl,
        orthonormal_iff_ite.mp b.orthonormal i j, if_neg hij, mul_zero, add_zero]
  have hw_j : b.repr w j = Complex.I := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal j i, if_neg (Ne.symm hij),
        orthonormal_iff_ite.mp b.orthonormal j j, if_pos rfl, mul_one, zero_add]
  have hw_zero : ∀ k, k ≠ i → k ≠ j → b.repr w k = 0 := by
    intro k hki hkj
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal k i, if_neg hki,
        orthonormal_iff_ite.mp b.orthonormal k j, if_neg hkj, mul_zero, add_zero]
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b
      (fun m => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ m) hwne k
    rwa [← hφ] at h
  have hsupp : ∀ k, k ≠ i → k ≠ j → b.repr φ k = 0 := by
    intro k hki hkj
    have hm := hcm k
    rw [hw_zero k hki hkj, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  have ha : b.repr φ i ≠ 0 := by
    intro h0
    have hm := hcm i
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div, hw_i, norm_one, one_pow, hwnorm] at hm
    norm_num at hm
  have hmod : ‖b.repr φ j‖ = ‖b.repr φ i‖ := by
    have hi := hcm j
    have hi0 := hcm i
    rw [hw_j, Complex.norm_I, one_pow, hwnorm] at hi
    rw [hw_i, norm_one, one_pow, hwnorm] at hi0
    have hd := hi.trans hi0.symm
    rw [div_eq_div_iff hden hden] at hd
    have heq2 : ‖b.repr φ j‖ ^ 2 = ‖b.repr φ i‖ ^ 2 := mul_right_cancel₀ hden hd
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ j)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i)), heq2]
  set ε : ℂ := b.repr φ j / b.repr φ i with hε
  have hεnorm : ‖ε‖ = 1 := by rw [hε, norm_div, hmod, div_self (norm_ne_zero_iff.mpr ha)]
  have hdj : b.repr φ j = ε * b.repr φ i := by rw [hε, div_mul_cancel₀ _ ha]
  have hrel := diagReducedMap_relphase_all hf b i₀ hij hwne
  rw [← hφ, hw_i, hw_j, map_one, one_mul, Complex.I_re, zero_div] at hrel
  have hRe : ((starRingEnd ℂ) (b.repr φ i) * b.repr φ j).re = 0 := by
    rcases div_eq_zero_iff.mp hrel with h | h
    · exact h
    · exact absurd h hden
  have hεre : ε.re = 0 := by
    rw [hdj] at hRe
    have hr : (starRingEnd ℂ) (b.repr φ i) * (ε * b.repr φ i)
        = ε * ((‖b.repr φ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [show (starRingEnd ℂ) (b.repr φ i) * (ε * b.repr φ i)
            = ε * ((starRingEnd ℂ) (b.repr φ i) * b.repr φ i) from by ring, RCLike.conj_mul]
      norm_cast
    rw [hr, mul_ofReal_re] at hRe
    have hpos : (0 : ℝ) < ‖b.repr φ i‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
    exact (mul_eq_zero.mp hRe).resolve_right (ne_of_gt hpos)
  have hgw : diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne := (Projectivization.mk_rep _).symm
  have hpair : φ = b.repr φ i • b i + b.repr φ j • b j :=
    repr_eq_pair_of_support b φ hij hsupp
  rcases unit_re_zero_eq_I_or_negI hεnorm hεre with hI | hnI
  · left
    have hval : b.repr φ i • w = φ := by
      conv_rhs => rw [hpair, hdj, hI]
      rw [hw]; module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i, hval⟩
  · right
    have hval : b.repr φ i • (b i - Complex.I • b j) = φ := by
      conv_rhs => rw [hpair, hdj, hnI]
      module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ (b i - Complex.I • b j) hφne
      (subI_basis_ne_zero b hij)).mpr ⟨b.repr φ i, hval⟩

/-- Gram datum for a fixed complex ray. -/
theorem diagReducedMap_gram_of_fixed
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    (hfixI : diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    (starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j
          * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j
          * ((‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2 : ℝ) : ℂ) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hre := diagReducedMap_relphase_all hf b i₀ hij hψ
  have him := two_level_imrelphase_of_fixes hg b hfixb hij hfixI hψ
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep with hφ
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (Projectivization.rep_nonzero _))
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hrec := (div_eq_div_iff hDφ hDψ).mp hre
  have himc := (div_eq_div_iff hDφ hDψ).mp him
  apply Complex.ext
  · rw [mul_ofReal_re, mul_ofReal_re]; exact hrec
  · rw [mul_ofReal_im, mul_ofReal_im]; exact himc

/-- Gram datum for a flipped complex ray. -/
theorem diagReducedMap_gram_of_flips
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    (hflipI : diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    (starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j
          * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j)
          * ((‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2 : ℝ) : ℂ) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hre := diagReducedMap_relphase_all hf b i₀ hij hψ
  have him := two_level_imrelphase_of_flips hg b hfixb hij hflipI hψ
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep with hφ
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (Projectivization.rep_nonzero _))
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hrec := (div_eq_div_iff hDφ hDψ).mp hre
  have himc := (div_eq_div_iff hDφ hDψ).mp him
  apply Complex.ext
  · rw [mul_ofReal_re, mul_ofReal_re, Complex.conj_re]; exact hrec
  · rw [mul_ofReal_im, mul_ofReal_im, Complex.conj_im]; exact himc

/-- Gram datum on the diagonal (moduli). -/
theorem diagReducedMap_gram_diag
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) (i : Fin N)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    (starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i
          * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) * b.repr ψ i
          * ((‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2 : ℝ) : ℂ) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep with hφ
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (Projectivization.rep_nonzero _))
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hmc := (div_eq_div_iff hDφ hDψ).mp hm
  have e1 : (starRingEnd ℂ) (b.repr φ i) * b.repr φ i = ((‖b.repr φ i‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]; norm_cast
  have e2 : (starRingEnd ℂ) (b.repr ψ i) * b.repr ψ i = ((‖b.repr ψ i‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]; norm_cast
  rw [e1, e2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
  exact hmc

/-! ## Master witness and the global-sign closure -/

/-- Master witness vector: `∑ a, (1 + I·a) • b a`. All coordinates nonzero and
all pairwise imaginary relative phases nonzero. -/
noncomputable def masterVec
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    EuclideanSpace ℂ (Fin N) :=
  ∑ a : Fin N, (1 + Complex.I * ((a : ℕ) : ℂ)) • b a

lemma masterVec_repr
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (k : Fin N) :
    b.repr (masterVec b) k = 1 + Complex.I * ((k : ℕ) : ℂ) := by
  rw [b.repr_apply_apply]
  unfold masterVec
  rw [inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k k, if_pos rfl, mul_one]
  · intro j _ hjk
    rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k j, if_neg (Ne.symm hjk),
        mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma masterVec_coord_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (k : Fin N) :
    b.repr (masterVec b) k ≠ 0 := by
  rw [masterVec_repr]
  have hre : (1 + Complex.I * ((k : ℕ) : ℂ)).re = 1 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  intro h
  rw [h] at hre
  simp at hre

lemma masterVec_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (k : Fin N) :
    masterVec b ≠ 0 := by
  intro h
  exact masterVec_coord_ne_zero b k (by rw [h]; simp)

lemma masterVec_im_ne
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {a c : Fin N} (hac : a ≠ c) :
    ((starRingEnd ℂ) (b.repr (masterVec b) a) * b.repr (masterVec b) c).im ≠ 0 := by
  rw [masterVec_repr, masterVec_repr]
  have him : ((starRingEnd ℂ) (1 + Complex.I * ((a : ℕ) : ℂ)) * (1 + Complex.I * ((c : ℕ) : ℂ))).im
      = ((c : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    simp only [map_add, map_one, map_mul, Complex.conj_I, Complex.conj_natCast]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im]
    ring
  rw [him, sub_ne_zero]
  intro h
  exact hac (Fin.val_injective (Nat.cast_injective h)).symm

/-- The complex probe `mk (b i + I • b j)` and its conjugate `mk (b i - I • b j)`
are distinct projective points (their reps are orthogonal). -/
lemma Iprobe_ne_negIprobe
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i j : Fin N} (hij : i ≠ j) :
    Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij)
      ≠ Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij) := by
  intro h
  have h0 : transProb (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      (Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij)) = 0 := by
    rw [transProb_mk_eq_zero_iff]
    have e1 : (inner ℂ (b i) (b i) : ℂ) = 1 := by
      rw [orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl]
    have e2 : (inner ℂ (b i) (b j) : ℂ) = 0 := by
      rw [orthonormal_iff_ite.mp b.orthonormal i j, if_neg hij]
    have e3 : (inner ℂ (b j) (b i) : ℂ) = 0 := by
      rw [orthonormal_iff_ite.mp b.orthonormal j i, if_neg (Ne.symm hij)]
    have e4 : (inner ℂ (b j) (b j) : ℂ) = 1 := by
      rw [orthonormal_iff_ite.mp b.orthonormal j j, if_pos rfl]
    rw [inner_add_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, e1, e2, e3, e4]
    simp [Complex.conj_I]
  rw [h, transProb_self] at h0
  exact one_ne_zero h0

/-- Abstract algebraic core of the global-sign linking: given the Gram equations
for three coordinates and the master genericity (imaginary relative phases
nonzero), the fixed/flipped sign of the pair `(a,b)` matches that of `(b,c)`. -/
lemma sign_link_core {cA cB cC dA dB dC : ℂ} {S F : ℝ}
    (hFpos : (0 : ℝ) < F)
    (hcA : cA ≠ 0) (hcB : cB ≠ 0) (hcC : cC ≠ 0)
    (hImAB : ((starRingEnd ℂ) cA * cB).im ≠ 0)
    (hImBC : ((starRingEnd ℂ) cB * cC).im ≠ 0)
    {Γab Γbc Γac : ℂ}
    (Eab : (starRingEnd ℂ) dA * dB * (S : ℂ) = Γab * (F : ℂ))
    (Ebc : (starRingEnd ℂ) dB * dC * (S : ℂ) = Γbc * (F : ℂ))
    (Eac : (starRingEnd ℂ) dA * dC * (S : ℂ) = Γac * (F : ℂ))
    (Ebb : (starRingEnd ℂ) dB * dB * (S : ℂ) = (starRingEnd ℂ) cB * cB * (F : ℂ))
    (hAB : Γab = (starRingEnd ℂ) cA * cB ∨ Γab = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB))
    (hBC : Γbc = (starRingEnd ℂ) cB * cC ∨ Γbc = (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC))
    (hAC : Γac = (starRingEnd ℂ) cA * cC ∨ Γac = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cC)) :
    (Γab = (starRingEnd ℂ) cA * cB ↔ Γbc = (starRingEnd ℂ) cB * cC) := by
  have hFc : (F : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
  have hdia : Γab * Γbc = Γac * ((starRingEnd ℂ) cB * cB) := by
    have hbase : ((starRingEnd ℂ) dA * dB * (S : ℂ)) * ((starRingEnd ℂ) dB * dC * (S : ℂ))
        = ((starRingEnd ℂ) dA * dC * (S : ℂ)) * ((starRingEnd ℂ) dB * dB * (S : ℂ)) := by ring
    rw [Eab, Ebc, Eac, Ebb] at hbase
    have h2 : Γab * Γbc * ((F : ℂ) * (F : ℂ))
        = Γac * ((starRingEnd ℂ) cB * cB) * ((F : ℂ) * (F : ℂ)) := by linear_combination hbase
    exact mul_right_cancel₀ (mul_ne_zero hFc hFc) h2
  have hsrc : ((starRingEnd ℂ) cA * cB) * ((starRingEnd ℂ) cB * cC)
      = ((starRingEnd ℂ) cA * cC) * ((starRingEnd ℂ) cB * cB) := by ring
  have hγab : (starRingEnd ℂ) cA * cB ≠ 0 := mul_ne_zero (by simpa using hcA) hcB
  have hγbc : (starRingEnd ℂ) cB * cC ≠ 0 := mul_ne_zero (by simpa using hcB) hcC
  have hγbb_real : (starRingEnd ℂ) ((starRingEnd ℂ) cB * cB) = (starRingEnd ℂ) cB * cB := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  have hsrcC : (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB) * (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC)
      = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cC) * ((starRingEnd ℂ) cB * cB) := by
    rw [← map_mul, hsrc, map_mul, hγbb_real]
  constructor
  · intro hABf
    by_contra hBCn
    have hBCflip : Γbc = (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC) := hBC.resolve_left hBCn
    rcases hAC with hACf | hACflip
    · rw [hABf, hBCflip, hACf] at hdia
      have hz : (starRingEnd ℂ) cA * cB
          * ((starRingEnd ℂ) ((starRingEnd ℂ) cB * cC) - (starRingEnd ℂ) cB * cC) = 0 := by
        linear_combination hdia - hsrc
      rcases mul_eq_zero.mp hz with h | h
      · exact hγab h
      · exact hImBC (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h))
    · rw [hABf, hBCflip, hACflip] at hdia
      have hz : ((starRingEnd ℂ) cA * cB - (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB))
          * (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC) = 0 := by
        linear_combination hdia - hsrcC
      rcases mul_eq_zero.mp hz with h | h
      · exact hImAB (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h).symm)
      · exact hγbc (by simpa only [starRingEnd_apply, star_eq_zero] using h)
  · intro hBCf
    by_contra hABn
    have hABflip : Γab = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB) := hAB.resolve_left hABn
    rcases hAC with hACf | hACflip
    · rw [hABflip, hBCf, hACf] at hdia
      have hz : ((starRingEnd ℂ) ((starRingEnd ℂ) cA * cB) - (starRingEnd ℂ) cA * cB)
          * ((starRingEnd ℂ) cB * cC) = 0 := by
        linear_combination hdia - hsrc
      rcases mul_eq_zero.mp hz with h | h
      · exact hImAB (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h))
      · exact hγbc h
    · rw [hABflip, hBCf, hACflip] at hdia
      have hz : (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB)
          * ((starRingEnd ℂ) cB * cC - (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC)) = 0 := by
        linear_combination hdia - hsrcC
      rcases mul_eq_zero.mp hz with h | h
      · exact hγab (by simpa only [starRingEnd_apply, star_eq_zero] using h)
      · exact hImBC (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h).symm)

/-- Abbreviation: the diagonally reduced map fixes the complex two-level ray `(i,j)`. -/
def CFixed (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) : Prop :=
  diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij)

/-- Middle-index linking: the complex sign of `(a,bx)` matches that of `(bx,c)`. -/
theorem diagReducedMap_complexSign_link
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {a bx c : Fin N} (hab : a ≠ bx) (hbc : bx ≠ c) (hac : a ≠ c) :
    CFixed hf b i₀ hab ↔ CFixed hf b i₀ hbc := by
  have hψne : masterVec b ≠ 0 := masterVec_ne_zero b a
  have hφne : (diagReducedMap hf b i₀ (Projectivization.mk ℂ (masterVec b) hψne)).rep ≠ 0 :=
    Projectivization.rep_nonzero _
  have hFpos : (0 : ℝ)
      < ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ (masterVec b) hψne)).rep‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hφne) 2
  have Ebb := diagReducedMap_gram_diag hf b i₀ bx (ψ := masterVec b) hψne
  have hcA := masterVec_coord_ne_zero b a
  have hcB := masterVec_coord_ne_zero b bx
  have hcC := masterVec_coord_ne_zero b c
  have hImAB := masterVec_im_ne b hab
  have hImBC := masterVec_im_ne b hbc
  constructor
  · intro hAB
    rcases diagReducedMap_complex_probe_general hf b i₀ hbc with hBC | hBC
    · exact hBC
    · exfalso
      have Eab := diagReducedMap_gram_of_fixed hf b i₀ hab hAB (ψ := masterVec b) hψne
      have Ebc := diagReducedMap_gram_of_flips hf b i₀ hbc hBC (ψ := masterVec b) hψne
      rcases diagReducedMap_complex_probe_general hf b i₀ hac with hAC | hAC
      · have Eac := diagReducedMap_gram_of_fixed hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
        exact hImBC (Complex.conj_eq_iff_im.mp (hcore.mp rfl))
      · have Eac := diagReducedMap_gram_of_flips hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
        exact hImBC (Complex.conj_eq_iff_im.mp (hcore.mp rfl))
  · intro hBC
    rcases diagReducedMap_complex_probe_general hf b i₀ hab with hAB | hAB
    · exact hAB
    · exfalso
      have Eab := diagReducedMap_gram_of_flips hf b i₀ hab hAB (ψ := masterVec b) hψne
      have Ebc := diagReducedMap_gram_of_fixed hf b i₀ hbc hBC (ψ := masterVec b) hψne
      rcases diagReducedMap_complex_probe_general hf b i₀ hac with hAC | hAC
      · have Eac := diagReducedMap_gram_of_fixed hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
        exact hImAB (Complex.conj_eq_iff_im.mp (hcore.mpr rfl))
      · have Eac := diagReducedMap_gram_of_flips hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
        exact hImAB (Complex.conj_eq_iff_im.mp (hcore.mpr rfl))

/-- Order swap: the complex sign of `(i,j)` matches that of `(j,i)` (by injectivity). -/
theorem diagReducedMap_complexSign_swap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) :
    CFixed hf b i₀ hij → CFixed hf b i₀ (Ne.symm hij) := by
  intro hfix
  rcases diagReducedMap_complex_probe_general hf b i₀ (Ne.symm hij) with hji | hji
  · exact hji
  · exfalso
    have hLvec : Complex.I • (b i - Complex.I • b j) = b j + Complex.I • b i := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]
    have hRvec : (-Complex.I) • (b i + Complex.I • b j) = b j - Complex.I • b i := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul, add_comm,
          ← sub_eq_add_neg]
    have hL : Projectivization.mk ℂ (b j + Complex.I • b i) (Iadd_basis_ne_zero b (Ne.symm hij))
        = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij) :=
      (Projectivization.mk_eq_mk_iff' ℂ (b j + Complex.I • b i) (b i - Complex.I • b j)
        (Iadd_basis_ne_zero b (Ne.symm hij)) (subI_basis_ne_zero b hij)).mpr ⟨Complex.I, hLvec⟩
    have hR : Projectivization.mk ℂ (b j - Complex.I • b i) (subI_basis_ne_zero b (Ne.symm hij))
        = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij) :=
      (Projectivization.mk_eq_mk_iff' ℂ (b j - Complex.I • b i) (b i + Complex.I • b j)
        (subI_basis_ne_zero b (Ne.symm hij)) (Iadd_basis_ne_zero b hij)).mpr ⟨-Complex.I, hRvec⟩
    rw [hL, hR] at hji
    have hginj := (diagReducedMap_transProbPreserving hf b i₀).injective
    have hReq := hginj (hji.trans hfix.symm)
    exact Iprobe_ne_negIprobe b hij hReq.symm

/-- Order swap as an iff. -/
theorem diagReducedMap_complexSign_swapIff
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) :
    CFixed hf b i₀ hij ↔ CFixed hf b i₀ (Ne.symm hij) :=
  ⟨diagReducedMap_complexSign_swap hf b i₀ hij,
   diagReducedMap_complexSign_swap hf b i₀ (Ne.symm hij)⟩

/-- Shared-first-index linking: the complex sign of `(a,bx)` matches that of `(a,c)`. -/
theorem diagReducedMap_complexSign_link'
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {a bx c : Fin N} (hab : a ≠ bx) (hac : a ≠ c) (hbc : bx ≠ c) :
    CFixed hf b i₀ hab ↔ CFixed hf b i₀ hac :=
  (diagReducedMap_complexSign_swapIff hf b i₀ hab).trans
    (diagReducedMap_complexSign_link hf b i₀ (Ne.symm hab) hac hbc)

/-- Global constancy: the complex sign is the same for every pair. -/
theorem diagReducedMap_complexSign_all
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) {k l : Fin N} (hkl : k ≠ l) :
    CFixed hf b i₀ hij ↔ CFixed hf b i₀ hkl := by
  by_cases h1 : i = k
  · subst h1
    by_cases h2 : j = l
    · subst h2; exact Iff.rfl
    · exact diagReducedMap_complexSign_link' hf b i₀ hij hkl h2
  · by_cases h2 : i = l
    · subst h2
      by_cases h3 : j = k
      · subst h3; exact diagReducedMap_complexSign_swapIff hf b i₀ hij
      · exact (diagReducedMap_complexSign_link' hf b i₀ hij h1 h3).trans
          (diagReducedMap_complexSign_swapIff hf b i₀ h1)
    · by_cases h3 : j = k
      · subst h3
        exact (diagReducedMap_complexSign_swapIff hf b i₀ hij).trans
          (diagReducedMap_complexSign_link' hf b i₀ (Ne.symm hij) hkl h2)
      · by_cases h4 : j = l
        · subst h4
          exact (diagReducedMap_complexSign_swapIff hf b i₀ hij).trans
            ((diagReducedMap_complexSign_link' hf b i₀ (Ne.symm hij) (Ne.symm hkl) h1).trans
             (diagReducedMap_complexSign_swapIff hf b i₀ (Ne.symm hkl)))
        · exact (diagReducedMap_complexSign_link' hf b i₀ hij h1 h3).trans
            ((diagReducedMap_complexSign_swapIff hf b i₀ h1).trans
             (diagReducedMap_complexSign_link' hf b i₀ (Ne.symm h1) hkl h2))

/-- **HEADLINE (global-sign closure).** The per-pair `± I` complex-probe datum is
globally consistent: either every complex two-level ray is fixed, or every one is
flipped. Discharges the `hsign` hypothesis of
`diagReducedMap_dichotomy_of_complexSign` from transition-probability preservation
alone. -/
theorem diagReducedMap_complexSign_closure
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    ∨ (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij)) := by
  rcases lt_or_ge N 2 with hN | hN
  · haveI : Subsingleton (Fin N) := Fin.subsingleton_iff_le_one.mpr (by omega)
    exact Or.inl (fun i j hij => absurd (Subsingleton.elim i j) hij)
  · have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by norm_num)
    rcases diagReducedMap_complex_probe_general hf b i₀ h01 with hfix | hflip
    · exact Or.inl (fun i j hij => (diagReducedMap_complexSign_all hf b i₀ h01 hij).mp hfix)
    · refine Or.inr (fun i j hij => ?_)
      rcases diagReducedMap_complex_probe_general hf b i₀ hij with hf2 | hf2
      · exact absurd ((diagReducedMap_complexSign_all hf b i₀ hij h01).mp hf2)
          (fun hcfix => Iprobe_ne_negIprobe b h01 (hcfix.symm.trans hflip))
      · exact hf2

/-- **HEADLINE (unconditional reduced-map dichotomy).** The diagonally reduced map
is globally the identity on rays, or globally coordinatewise conjugation in `b`.
The global-sign residual is discharged (`diagReducedMap_complexSign_closure`);
both branches are genuine and no ℂ-linearity is assumed. -/
theorem diagReducedMap_dichotomy
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ ψ hψ)
    ∨ (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)
          = Projectivization.mk ℂ (bConjVec b ψ) (bConjVec_ne_zero b hψ)) :=
  diagReducedMap_dichotomy_of_complexSign hf b i₀ (diagReducedMap_complexSign_closure hf b i₀)

/-! ## STEP 2: assembly of the Wigner rigidity theorem -/

section Assembly
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `projMap` functoriality: composition of projective isometry maps. -/
lemma projMap_comp (e₁ e₂ : E ≃ₗᵢ[ℂ] E) (p : ℙ ℂ E) :
    projMap e₁ (projMap e₂ p) = projMap (e₂.trans e₁) p := by
  conv_lhs => rw [← p.mk_rep]
  conv_rhs => rw [← p.mk_rep]
  rw [projMap_mk e₂ p.rep p.rep_nonzero,
      projMap_mk e₁ (e₂ p.rep) (e₂.toLinearEquiv.map_ne_zero_iff.mpr p.rep_nonzero),
      projMap_mk (e₂.trans e₁) p.rep p.rep_nonzero]
  simp only [LinearIsometryEquiv.trans_apply]

/-- `projMap e` and `projMap e.symm` are inverse. -/
lemma projMap_symm_projMap (e : E ≃ₗᵢ[ℂ] E) (p : ℙ ℂ E) :
    projMap e (projMap e.symm p) = p := by
  conv_lhs => rw [← p.mk_rep]
  rw [projMap_mk e.symm p.rep p.rep_nonzero,
      projMap_mk e (e.symm p.rep) (e.symm.toLinearEquiv.map_ne_zero_iff.mpr p.rep_nonzero)]
  conv_rhs => rw [← p.mk_rep]
  congr 1
  exact e.apply_symm_apply p.rep

end Assembly

/-- Coordinatewise conjugation in the standard basis is `conjVec`. -/
lemma bConjVec_basisFun (ψ : EuclideanSpace ℂ (Fin N)) :
    bConjVec (EuclideanSpace.basisFun (Fin N) ℂ) ψ = conjVec ψ := by
  apply (EuclideanSpace.basisFun (Fin N) ℂ).repr.injective
  ext k
  rw [repr_bConjVec, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_repr]
  exact (conjVec_ofLp ψ k).symm

/-- **HEADLINE (Wigner / Fubini-Study rigidity converse).** Every
transition-probability-preserving self-map of `ℂℙ^{N-1}` is induced by a unitary
(`projMap e` for a `≃ₗᵢ[ℂ]` `e`) or by an antiunitary (`projMap e ∘ conjProj`).
ℂ-linearity of `e` is an OUTPUT of the construction (the reduced map lands on the
identity), never assumed; the antiunitary branch is genuinely present
(`conjProj`); the global unitary/antiunitary sign is forced from
transition-probability preservation alone. Foundational-triple only. -/
theorem wigner_rigidity
    (hf : TransProbPreserving f) :
    (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N), ∀ p, f p = projMap e p)
    ∨ (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        ∀ p, f p = projMap e (conjProj p)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact Or.inl ⟨LinearIsometryEquiv.refl ℂ _,
      fun p => absurd (Subsingleton.elim p.rep 0) p.rep_nonzero⟩
  · set b := EuclideanSpace.basisFun (Fin N) ℂ with hb
    set i₀ : Fin N := ⟨0, hN⟩ with hi0
    set U := candidateUnitary hf b with hU
    set D := diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀) with hD
    have hfe : ∀ p, f p = projMap U (projMap D (diagReducedMap hf b i₀ p)) := by
      intro p
      have h1 : reducedMap hf b p = projMap D (diagReducedMap hf b i₀ p) :=
        (projMap_symm_projMap D (reducedMap hf b p)).symm
      have h2 : f p = projMap U (reducedMap hf b p) :=
        (projMap_symm_projMap U (f p)).symm
      rw [h2, h1]
    rcases diagReducedMap_dichotomy hf b i₀ with hid | hconj
    · refine Or.inl ⟨D.trans U, fun p => ?_⟩
      have hthis : diagReducedMap hf b i₀ p = p := by
        have hp := hid p.rep p.rep_nonzero; rwa [p.mk_rep] at hp
      rw [hfe p, hthis, projMap_comp]
    · refine Or.inr ⟨D.trans U, fun p => ?_⟩
      have hthis : diagReducedMap hf b i₀ p = conjProj p := by
        have hp := hconj p.rep p.rep_nonzero
        rw [p.mk_rep] at hp
        rw [hp]
        refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
        rw [one_smul, bConjVec_basisFun]
      rw [hfe p, hthis, projMap_comp]


/-! ## Stage 3 complete (W6): the Wigner / Fubini-Study rigidity converse

Stages 1-3 are proved with **no linearity assumed** on `f`, only
`TransProbPreserving`. Stage 3 piece 3 (W5) delivered the complex probe, both
reconstruction directions, and the reduced-map dichotomy conditional on the
global complex-sign closure. **W6 discharges that closure**
(`diagReducedMap_complexSign_closure`) from transition-probability preservation
alone: the per-pair `± I` datum is globally consistent (all complex two-level
rays fixed, or all flipped). The route is (a) the non-anchored per-pair `± I`
dichotomy (`diagReducedMap_complex_probe_general`); (b) the master witness
`masterVec` with every pairwise imaginary relative phase nonzero
(`masterVec_im_ne`); (c) the abstract Gram-triple core `sign_link_core`, ruling
out mixed signs via the rank-1 identity `g_ab g_bc = g_ac ‖d_b‖²` and the
imaginary relative phases; (d) order swap by injectivity
(`diagReducedMap_complexSign_swap`, distinct rays `mk (b i + I b j)` and
`mk (b i - I b j)`) plus index linking (`..._link` / `..._link'` / `..._all`).
Neither `Complex.arg` nor any linearity is used; both `±` branches stay alive
until the probes resolve them.

The unconditional `diagReducedMap_dichotomy` follows, and the headline
`wigner_rigidity` inverts the frame reductions
(`f = projMap (candidateUnitary hf b) ∘ projMap D ∘ diagReducedMap`, with
`b` the standard basis so `bConjVec b = conjVec`) to conclude that every
`TransProbPreserving` self-map of `ℂℙ^{N-1}` is `projMap e` for a `≃ₗᵢ[ℂ]` `e`
(**unitary**) or `projMap e ∘ conjProj` (**antiunitary**). The antiunitary
branch is genuinely present (`conjProj`); ℂ-linearity of `e` is an OUTPUT of the
dichotomy landing on the identity, never assumed; the global sign is forced, not
posited. Foundational triple only (`propext, Classical.choice, Quot.sound`); no
`busch`, no `sorry`, no `native_decide`.
-/

/-! ## The `Matrix.unitaryGroup` reformulation

`wigner_rigidity` produces a `≃ₗᵢ[ℂ]` witness `e` and states `f = projMap e`
(or `= projMap e ∘ conjProj`). This section restates the theorem in the classic
`∃ U : Matrix.unitaryGroup (Fin N) ℂ, f = U • ·` form, where `U • ·` is the exact
projective action used by `transProbPreserving_unitary` /
`transProb_smul_unitary` (the `MulAction.compHom` of
`Matrix.UnitaryGroup.toEuclideanLinearEquivHom`). The bridge is the matrix of the
isometry in the standard basis: `unitaryOfIsometry e := toEuclideanLin.symm e`,
whose columns are `e (basisFun j)`, hence `star M * M = 1` by the isometry
property `e.inner_map_map` and orthonormality of `basisFun`. The antiunitary
branch is kept genuinely present as `U • conjProj p`. -/

/-- The matrix of a linear isometry equivalence in the standard basis of
`EuclideanSpace ℂ (Fin N)`, i.e. the inverse image under the linear equivalence
`Matrix.toEuclideanLin`. Its `toEuclideanLin` is `e` by construction
(`unitaryOfIsometry_toEuclideanLin`); it lies in `unitaryGroup`
(`unitaryOfIsometry_mem`). -/
noncomputable def unitaryOfIsometry
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.toEuclideanLin.symm (e : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))

/-- `toEuclideanLin (unitaryOfIsometry e) = e`: the matrix realises the isometry's
linear map. Immediate from `LinearEquiv.apply_symm_apply`. -/
lemma unitaryOfIsometry_toEuclideanLin
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin (unitaryOfIsometry e)
      = (e : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) :=
  LinearEquiv.apply_symm_apply _ _

/-- Column formula: the `(i, j)` entry of `unitaryOfIsometry e` is the `i`-th
coordinate of `e (basisFun j)`. Evaluate `toEuclideanLin (unitaryOfIsometry e)`
at the standard basis vector `basisFun j` (= `Pi.single j 1` after `ofLp`) and use
`unitaryOfIsometry_toEuclideanLin`. -/
lemma unitaryOfIsometry_apply
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) (i j : Fin N) :
    unitaryOfIsometry e i j = e (EuclideanSpace.basisFun (Fin N) ℂ j) i := by
  have h : Matrix.toEuclideanLin (unitaryOfIsometry e) (EuclideanSpace.basisFun (Fin N) ℂ j)
      = e (EuclideanSpace.basisFun (Fin N) ℂ j) := by
    rw [unitaryOfIsometry_toEuclideanLin]; rfl
  calc unitaryOfIsometry e i j
      = (unitaryOfIsometry e *ᵥ Pi.single j (1 : ℂ)) i := by
          rw [Matrix.mulVec_single_one, Matrix.col_apply]
    _ = (Matrix.toEuclideanLin (unitaryOfIsometry e)
          (EuclideanSpace.basisFun (Fin N) ℂ j)).ofLp i := by
          rw [EuclideanSpace.basisFun_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
            PiLp.ofLp_single]
    _ = e (EuclideanSpace.basisFun (Fin N) ℂ j) i := by rw [h]

/-- `unitaryOfIsometry e` is a unitary matrix: `star M * M = 1`, because the
`(j, k)` entry of `star M * M` is `⟪e (basisFun j), e (basisFun k)⟫ =
⟪basisFun j, basisFun k⟫ = δ_{jk}` via `e.inner_map_map` and orthonormality of
`basisFun`. -/
lemma unitaryOfIsometry_mem
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    unitaryOfIsometry e ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  calc ∑ i, (star (unitaryOfIsometry e)) j i * unitaryOfIsometry e i k
      = ∑ i, (starRingEnd ℂ) (e (EuclideanSpace.basisFun (Fin N) ℂ j) i)
          * e (EuclideanSpace.basisFun (Fin N) ℂ k) i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Matrix.star_apply, unitaryOfIsometry_apply, unitaryOfIsometry_apply]
        rfl
    _ = (inner ℂ (e (EuclideanSpace.basisFun (Fin N) ℂ j))
          (e (EuclideanSpace.basisFun (Fin N) ℂ k)) : ℂ) := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [RCLike.inner_apply']
    _ = (inner ℂ (EuclideanSpace.basisFun (Fin N) ℂ j)
          (EuclideanSpace.basisFun (Fin N) ℂ k) : ℂ) := e.inner_map_map _ _
    _ = if j = k then 1 else 0 :=
        orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin N) ℂ).orthonormal j k

/-- The `unitaryGroup` element attached to a linear isometry equivalence. -/
noncomputable def unitaryGroupOfIsometry
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨unitaryOfIsometry e, unitaryOfIsometry_mem e⟩

/-- **The action bridge.** `projMap e` agrees with the `unitaryGroup` ray action
`unitaryGroupOfIsometry e • ·` used by `transProbPreserving_unitary`. Reduce `p`
to `mk p.rep`, push both sides through `projMap_mk` /
`smul_mk_eq_mk_toEuclideanLin`, and note the underlying vectors agree since
`toEuclideanLin (unitaryOfIsometry e) = e`. -/
theorem projMap_eq_smul_unitary
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    projMap e p = unitaryGroupOfIsometry e • p := by
  conv_lhs => rw [← p.mk_rep]
  conv_rhs => rw [← p.mk_rep]
  rw [projMap_mk e p.rep p.rep_nonzero,
      smul_mk_eq_mk_toEuclideanLin (unitaryGroupOfIsometry e) p.rep_nonzero]
  have hvec : Matrix.toEuclideanLin ((unitaryGroupOfIsometry e).val) p.rep = e p.rep := by
    show Matrix.toEuclideanLin (unitaryOfIsometry e) p.rep = e p.rep
    rw [unitaryOfIsometry_toEuclideanLin]; rfl
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul, hvec]⟩

/-- **HEADLINE (Wigner rigidity, `unitaryGroup` form).** The classic statement:
every transition-probability-preserving self-map of `ℂℙ^{N-1}` is `U • ·` for a
`U : Matrix.unitaryGroup (Fin N) ℂ` (the **unitary** branch) or `U • conjProj ·`
(the **antiunitary** branch), with `U • ·` the same `MulAction` used by
`transProbPreserving_unitary`. Reformulation of `wigner_rigidity` through the
isometry-to-matrix bridge `projMap_eq_smul_unitary`; no ℂ-linearity is assumed on
`f`, the antiunitary branch is genuinely present, foundational-triple only. -/
theorem wigner_rigidity_unitaryGroup
    (hf : TransProbPreserving f) :
    (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, f p = U • p)
    ∨ (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, f p = U • conjProj p) := by
  rcases wigner_rigidity hf with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨unitaryGroupOfIsometry e,
      fun p => by rw [he p, projMap_eq_smul_unitary e p]⟩
  · exact Or.inr ⟨unitaryGroupOfIsometry e,
      fun p => by rw [he p, projMap_eq_smul_unitary e (conjProj p)]⟩

end Projectivization
