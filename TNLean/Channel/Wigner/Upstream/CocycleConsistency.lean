/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import TNLean.Channel.Wigner.Upstream.PhaseNormalization

/-!
# Projective Wigner rigidity: coordinate moduli, relative phases, and cocycle consistency

This module is adapted from
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean` in
`zblore/csd-lean4` at commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06`, under the Apache License 2.0.
The upstream single source file was split mechanically at semantic section
boundaries, preserving declaration order, to satisfy TNLean's module-size policy.
The only proof-level adaptation is inherited from the reduced Lean 4.32 import
cone; this section's upstream proof text is otherwise unchanged.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization ComplexOrder
open Matrix

namespace Projectivization

variable {N : ℕ}
variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-! ## Stage 3 piece 2: coordinate moduli, the two-level relative phase, cocycle datum

Piece 2 of the Stage-3 residual, the derivation-heavy core, built on the diagonally
reduced map `h := diagReducedMap hf b i₀` (`TransProbPreserving`, fixing every basis
ray and every anchored two-level ray `mk (b i₀ + b i)`). Writing `h (mk ψ) = mk φ`,
`cⱼ := b.repr ψ j`, `dⱼ := b.repr φ j`:

* **Moduli** (`coord_modulus_of_fixes_basis`, `diagReducedMap_coord_modulus`):
  `‖dⱼ‖² / ‖φ‖² = ‖cⱼ‖² / ‖ψ‖²`, for any `TransProbPreserving` map
  fixing the basis rays.
* **Two-level relative phase** (`two_level_relphase_of_fixes`,
  `diagReducedMap_two_level_relphase`) — the heart of piece 2:
  `Re(conj(d_{i₀}) d_i) / ‖φ‖² = Re(conj(c_{i₀}) c_i) / ‖ψ‖²`, i.e.
  `arg(d_i / d_{i₀}) = ± arg(c_i / c_{i₀})`. The overlap fixes only the real part;
  the sign of the imaginary part — the cocycle's ℤ/2 datum — stays free.
* **Conditional pairwise relation** (`diagReducedMap_pairwise_relphase_of_fixed`):
  for any pair `(i, j)` whose two-level ray is fixed by `h`, the analogous relation
  `Re(conj(d_i) d_j) / ‖φ‖² = Re(conj(c_i) c_j) / ‖ψ‖²` holds.

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
  have hre_i :
      ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i).re = ‖b.repr φ i₀‖ ^ 2 := by
    rw [div_eq_div_iff hden (by norm_num : (3 : ℝ) ≠ 0)] at hrel_i
    rw [md_i0, eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]; linarith [hrel_i]
  have hre_j :
      ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ j).re = ‖b.repr φ i₀‖ ^ 2 := by
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
  rw [show
        diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne) =
          Projectivization.mk ℂ φ hφne from (Projectivization.mk_rep
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
`Re(conj(c_i) d_j) = Re(conj(c_i) c_j)·‖φ‖²/‖ψ‖²` for all pairs —
with the ± sign of the imaginary parts still free (the ℤ/2 datum resolved only by piece 3). No
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

end Projectivization
