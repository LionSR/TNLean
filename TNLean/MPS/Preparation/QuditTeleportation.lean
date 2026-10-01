/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.WeylTwirl
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.Preparation.MeasurementRounds
import TNLean.MPS.Preparation.PermutationGates

/-!
# Teleportation of qudits in constant depth

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 moves the registers of an
isometry next to each other by teleportation: "creating nearest-neighbor entangled pairs, then
performing simultaneous measurements, and correcting (without postselection) based on the
measurement outcomes". This file proves that such a teleportation is one measurement round of
depth `2`, whatever the distance, and for any number of registers moved in parallel.

## One hop

A *hop* consists of three distinct sites `c`, `e`, `f`, the pair `{c, e}` and the pair `{e, f}`
being neighbouring pairs of the ring. With labels in `ℤ_d`, `ζ = e^{2πi/d}`, and the Fourier
matrix `F = d^{-1/2} (ζ^{ab})_{a,b}`:

* the gate of the first layer on `{e, f}` applies `F` at `e`, then
  `|a⟩_e |b⟩_f ↦ |a⟩_e |b + a⟩_f`; from `|0⟩_e |0⟩_f` it prepares the maximally entangled pair
  `d^{-1/2} ∑ⱼ |j⟩_e |j⟩_f`;
* the gate of the second layer on `{c, e}` applies `|a⟩_c |b⟩_e ↦ |a⟩_c |b - a⟩_e`, then `F`
  at `c`;
* the sites `c` and `e` are measured in the computational basis.

For the outcomes `z_c`, `z_e`, the content of `c` is found at `f`, acted on by the generalized
Pauli matrix `X^{z_e} Z^{z_c}`, the measured sites carry `|z_c⟩` and `|z_e⟩`, and the amplitude is
`1/d` (`MPSPreparation.TeleportHop.pre_mulVec`). The inverse of these single-site unitaries is a
correction.

## Chains of hops in one round

In a list of hops, the hop `h` comes after the hops `hs` when its sites `e` and `f` are not sites
of `hs` and its site `c` is not a site `c` or `e` of `hs`; its site `c` may be the site `f` of an
earlier hop, so that hops form chains `c₀ → f₀ = c₁ → f₁ = c₂ → ⋯`. All the hops are performed
in one round: the first layers of all hops, the second layers of all hops, one measurement and
one correction. Pushing the correction of a hop to the end is possible because a single-site
unitary at the site `c` of a hop reappears, after the hop, at its site `f`; no commutation
relation of Pauli matrices is needed, the correction being the inverse of the accumulated
single-site unitaries. On the vectors with `|0⟩` at the sites `e` and `f` of every hop, the round
acts, for every outcome, as `d^{-H}` times the permutation of sites that moves the content of
`c` to `f` hop after hop, `H` the number of hops
(`MPSPreparation.TeleportHop.isImplementationOn_round`).
In particular a register is moved along a chain of `L` hops, across `2L` sites, in depth `2`.

## Main definitions

* `MPSPreparation.quditFourier`, `MPSPreparation.quditPauli` — `F` and `X^x Z^z`.
* `MPSPreparation.IsZeroOn` — a vector with `|0⟩` at the sites of a set.
* `MPSPreparation.cfgPerm` — the permutation of configurations induced by a permutation of sites.
* `MPSPreparation.TeleportHop`, `MPSPreparation.TeleportHop.Valid`.
* `MPSPreparation.TeleportHop.round` — the measurement round of a list of hops, after a given
  circuit.

## Main results

* `MPSPreparation.quditFourier_mem_unitary`, `MPSPreparation.quditPauli_mem_unitary`.
* `MPSPreparation.TeleportHop.pre_mulVec` — one hop.
* `MPSPreparation.TeleportHop.isImplementationOn_round` — teleportation along chains of hops,
  in one round of depth `2` after the given circuit.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Tree-RG circuit with measurements".
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 2 (teleportation through maximally
  entangled pairs between neighbouring sites by LOCC).
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ}

/-! ### Single-site operators as Kronecker products -/

section SingleSite

/-- The single-site family: `u` at the site `t` and the identity elsewhere. -/
private theorem finKronecker_update_one_apply (t : Fin N) (u : Matrix (Fin d) (Fin d) ℂ)
    (y x : Cfg d N) :
    finKronecker (Function.update (1 : Fin N → Matrix (Fin d) (Fin d) ℂ) t u) y x =
      if x = Function.update y t (x t) then u (y t) (x t) else 0 := by
  classical
  rw [finKronecker_apply, Fintype.prod_eq_mul_prod_compl t, Function.update_self]
  have hrest : ∏ i ∈ ({t}ᶜ : Finset (Fin N)),
      Function.update (1 : Fin N → Matrix (Fin d) (Fin d) ℂ) t u i (y i) (x i) =
        if x = Function.update y t (x t) then 1 else 0 := by
    rw [Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (by simpa using hi), Pi.one_apply, one_apply]]
    rw [Finset.prod_boole]
    congr 1
    refine propext ⟨fun h => funext fun i => ?_, fun h i hi => ?_⟩
    · by_cases hi : i = t
      · subst hi; simp
      · rw [Function.update_of_ne hi]; exact (h i (by simpa using hi)).symm
    · rw [h, Function.update_of_ne (by simpa using hi)]
  rw [hrest]
  split_ifs <;> simp

/-- **A single-site operator on a vector.** The operator `u` at the site `t` maps `v` to
`y ↦ ∑ⱼ u_{y_t, j} v(y[t ↦ j])`. -/
theorem finKronecker_update_one_mulVec_apply (t : Fin N) (u : Matrix (Fin d) (Fin d) ℂ)
    (v : Cfg d N → ℂ) (y : Cfg d N) :
    (finKronecker (Function.update (1 : Fin N → Matrix (Fin d) (Fin d) ℂ) t u) *ᵥ v) y =
      ∑ j, u (y t) j * v (Function.update y t j) := by
  classical
  simp only [mulVec, dotProduct, finKronecker_update_one_apply, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun x => x t) (fun j => Function.update y t j) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_univ _
  · intro j _; simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.symm
  · intro j _; simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [← hx]

/-- A permutation of the labels at the site `t` acts on a vector by moving the label at `t`. -/
theorem finKronecker_update_one_permMatrix_mulVec (t : Fin N) (σ : Equiv.Perm (Fin d))
    (v : Cfg d N → ℂ) :
    finKronecker (Function.update (1 : Fin N → Matrix (Fin d) (Fin d) ℂ) t (σ.permMatrix ℂ)) *ᵥ v =
      fun y => v (Function.update y t (σ (y t))) := by
  classical
  funext y
  rw [finKronecker_update_one_mulVec_apply, Finset.sum_eq_single (σ (y t))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro j _ hj
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Ne.symm hj]
  · simp

/-- The Kronecker product of a family equal to `1` off a set `S` acts on `S`. -/
theorem finKronecker_mem_supportedOperators_of_eq_one {S : Set (Fin N)}
    {g : Fin N → Matrix (Fin d) (Fin d) ℂ} (hg : ∀ i ∉ S, g i = 1) :
    finKronecker g ∈ supportedOperators d S :=
  finKronecker_mem_supportedOperators hg

end SingleSite

/-! ### The Fourier matrix and the generalized Pauli matrices -/

section Fourier

variable [NeZero d]

/-- The primitive `d`-th root of unity `ζ = e^{2πi/d}`. -/
noncomputable def quditRoot (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

theorem isPrimitiveRoot_quditRoot : IsPrimitiveRoot (quditRoot d) d :=
  Complex.isPrimitiveRoot_exp d (NeZero.ne d)

theorem norm_quditRoot_pow (k : ℕ) : ‖quditRoot d ^ k‖ = 1 := by
  rw [norm_pow, isPrimitiveRoot_quditRoot.norm'_eq_one (NeZero.ne d), one_pow]

theorem star_quditRoot_pow_mul_self (k : ℕ) :
    star (quditRoot d ^ k) * quditRoot d ^ k = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    norm_quditRoot_pow]
  norm_num

/-- The Fourier matrix `F_{ab} = d^{-1/2} ζ^{ab}` on the labels `0, …, d-1`.

Source: arXiv:2103.13367, Example 2 (teleportation by LOCC); the measurement in the basis of
maximally entangled pairs is a computational-basis measurement after `F`. -/
noncomputable def quditFourier (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  of fun a b => ((Real.sqrt d : ℝ) : ℂ)⁻¹ * quditRoot d ^ (a.val * b.val)

omit [NeZero d] in
theorem quditFourier_apply (a b : Fin d) :
    quditFourier d a b = ((Real.sqrt d : ℝ) : ℂ)⁻¹ * quditRoot d ^ (a.val * b.val) :=
  rfl

private theorem sum_quditRoot_pow (a c : Fin d) :
    ∑ b : Fin d, quditRoot d ^ (a.val * b.val) * star (quditRoot d ^ (c.val * b.val)) =
      if a = c then (d : ℂ) else 0 := by
  have hζ := isPrimitiveRoot_quditRoot (d := d)
  have hconj : star (quditRoot d) = (quditRoot d)⁻¹ :=
    Matrix.starRingEnd_eq_inv_of_isPrimitiveRoot hζ
  have hζ0 : quditRoot d ≠ 0 := hζ.ne_zero (NeZero.ne d)
  set ξ := quditRoot d ^ a.val * star (quditRoot d) ^ c.val with hξ
  have hterm : ∀ b : Fin d, quditRoot d ^ (a.val * b.val) * star (quditRoot d ^ (c.val * b.val))
      = ξ ^ b.val := fun b => by
    rw [hξ, star_pow, mul_pow, ← pow_mul, ← pow_mul]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun b => ξ ^ b)]
  have hξd : ξ ^ d = 1 := by
    rw [hξ, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val, mul_comm c.val, pow_mul, pow_mul,
      hconj, inv_pow, hζ.pow_eq_one, inv_one, one_pow, one_pow, mul_one]
  have hξ1 : ξ = 1 ↔ a = c := by
    rw [hξ, hconj, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hζ0)]
    exact ⟨fun h => Fin.ext (hζ.pow_inj a.isLt c.isLt h), fun h => by rw [h]⟩
  by_cases h : a = c
  · rw [ite_eq_left h, hξ1.mpr h]
    simp
  · rw [ite_eq_right h]
    have key := geom_sum_mul ξ d
    rw [hξd, sub_self] at key
    exact (mul_eq_zero.mp key).resolve_right (sub_ne_zero_of_ne fun h' => h (hξ1.mp h'))

/-- The Fourier matrix is unitary. -/
theorem quditFourier_mem_unitary : quditFourier d ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  refine Matrix.mem_unitaryGroup_iff.mpr ?_
  ext a c
  have hs : star (((Real.sqrt d : ℝ) : ℂ)⁻¹) = ((Real.sqrt d : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hterm : ∀ b : Fin d, quditFourier d a b * star (quditFourier d c b) =
      (d : ℂ)⁻¹ * (quditRoot d ^ (a.val * b.val) * star (quditRoot d ^ (c.val * b.val))) :=
    fun b => by
      have hd : ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹ = (d : ℂ)⁻¹ := by
        rw [Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg _)]
        push_cast
        rfl
      rw [quditFourier_apply, quditFourier_apply, star_mul', hs, ← hd]
      ring
  rw [mul_apply]
  simp only [star_apply, hterm, ← Finset.mul_sum, sum_quditRoot_pow, one_apply]
  split_ifs
  · exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  · simp

/-- The generalized Pauli matrix `X^x Z^z`, with entries `(X^x Z^z)_{p,q} = [p - x = q] ζ^{zq}`;
it maps `|q⟩` to `ζ^{zq} |q + x⟩`. -/
noncomputable def quditPauli (z x : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Equiv.Perm.permMatrix ℂ (Equiv.subRight x) * diagonal fun q => quditRoot d ^ (z.val * q.val)

theorem quditPauli_apply (z x p q : Fin d) :
    quditPauli z x p q = if p - x = q then quditRoot d ^ (z.val * q.val) else 0 := by
  simp [quditPauli, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, mul_diagonal]

theorem quditPauli_mem_unitary (z x : Fin d) :
    quditPauli z x ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  refine Submonoid.mul_mem _ (Equiv.Perm.permMatrix_mem_unitaryGroup _) ?_
  refine Matrix.mem_unitaryGroup_iff.mpr ?_
  rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext q
  rw [Pi.star_apply, mul_comm]
  exact star_quditRoot_pow_mul_self _

end Fourier

/-! ### Vectors with `|0⟩` at given sites and permutations of sites -/

section Sites

variable [NeZero d]

/-- The vector `v` has `|0⟩` at the sites of `S`: it vanishes at every configuration with a
nonzero label at a site of `S`. -/
def IsZeroOn (S : Set (Fin N)) (v : Cfg d N → ℂ) : Prop :=
  ∀ x, v x ≠ 0 → ∀ i ∈ S, x i = 0

theorem IsZeroOn.mono {S S' : Set (Fin N)} {v : Cfg d N → ℂ} (h : IsZeroOn S' v)
    (hS : S ⊆ S') : IsZeroOn S v := fun x hx i hi => h x hx i (hS hi)

theorem IsZeroOn.smul {S : Set (Fin N)} {v : Cfg d N → ℂ} (h : IsZeroOn S v) (c : ℂ) :
    IsZeroOn S (c • v) := fun x hx => h x fun h0 => hx (by simp [h0])

/-- A single-site operator at a site outside `S` keeps `|0⟩` at the sites of `S`. -/
theorem IsZeroOn.finKronecker_update_one_mulVec {S : Set (Fin N)} {v : Cfg d N → ℂ}
    (h : IsZeroOn S v) {t : Fin N} (ht : t ∉ S) (u : Matrix (Fin d) (Fin d) ℂ) :
    IsZeroOn S
      (finKronecker (Function.update (1 : Fin N → Matrix (Fin d) (Fin d) ℂ) t u) *ᵥ v) := by
  intro y hy i hi
  rw [finKronecker_update_one_mulVec_apply] at hy
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have := h _ (right_ne_zero_of_mul hj) i hi
  rwa [Function.update_of_ne (by rintro rfl; exact ht hi)] at this

end Sites

/-- The permutation `x ↦ x ∘ π` of the configurations induced by a permutation `π` of the
sites. -/
def cfgPerm (π : Equiv.Perm (Fin N)) : Equiv.Perm (Cfg d N) where
  toFun x := x ∘ π
  invFun x := x ∘ π.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem cfgPerm_apply (π : Equiv.Perm (Fin N)) (x : Cfg d N) : cfgPerm π x = x ∘ π := rfl

/-- **Moving single-site operators across a permutation of sites.** -/
theorem permMatrix_cfgPerm_mul_finKronecker (π : Equiv.Perm (Fin N))
    (g : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    (cfgPerm π).permMatrix ℂ * finKronecker g =
      finKronecker (fun i => g (π.symm i)) * (cfgPerm π).permMatrix ℂ := by
  classical
  ext x y
  simp only [mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, finKronecker_apply]
  rw [Finset.sum_eq_single ((cfgPerm π).symm y)]
  · simp only [Equiv.apply_symm_apply, ite_true]
    refine Fintype.prod_equiv π _ _ fun i => ?_
    simp [cfgPerm]
  · intro z _ hz
    rw [ite_eq_right fun h => hz (by rw [← h, Equiv.symm_apply_apply])]
  · simp

theorem IsZeroOn.permMatrix_cfgPerm_mulVec [NeZero d] {S : Set (Fin N)} {v : Cfg d N → ℂ}
    (h : IsZeroOn S v) {π : Equiv.Perm (Fin N)} (hπ : ∀ i ∈ S, π i = i) :
    IsZeroOn S ((cfgPerm π).permMatrix ℂ *ᵥ v) := by
  intro y hy i hi
  rw [permMatrix_mulVec] at hy
  have := h _ hy i hi
  simpa [cfgPerm, hπ i hi] using this

/-! ### One hop -/

variable [NeZero N]

/-- A hop of a teleportation chain: three distinct sites `c`, `e`, `f` with `{e, f}` and
`{c, e}` neighbouring pairs of the ring, written as the pairs `{k₁, k₁ + 1}` and
`{k₂, k₂ + 1}`. The content of `c` is teleported to `f` through the maximally entangled pair
prepared on `{e, f}`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("creating
nearest-neighbor entangled pairs"). -/
structure TeleportHop (N : ℕ) [NeZero N] where
  /-- The site whose content is teleported. -/
  c : Fin N
  /-- The site of the pair next to `c`, measured with `c`. -/
  e : Fin N
  /-- The site receiving the content. -/
  f : Fin N
  /-- The left site of the pair `{e, f}`. -/
  k₁ : Fin N
  /-- The left site of the pair `{c, e}`. -/
  k₂ : Fin N
  bond_k₁ : bond k₁ = {e, f}
  bond_k₂ : bond k₂ = {c, e}
  c_ne_e : c ≠ e
  c_ne_f : c ≠ f
  e_ne_f : e ≠ f

namespace TeleportHop

/-- The forward hop from `c` to `c + 2` on a ring of at least three sites. -/
def forward (hN : 3 ≤ N) (c : Fin N) : TeleportHop N where
  c := c
  e := c + 1
  f := c + 1 + 1
  k₁ := c + 1
  k₂ := c
  bond_k₁ := rfl
  bond_k₂ := rfl
  c_ne_e := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)] at this
    rcases Nat.lt_or_ge (c.val + 1) N with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at this; omega
    · have : c.val + 1 = N := by have := c.isLt; omega
      simp_all
  c_ne_f := by
    intro h
    have := congrArg Fin.val h
    rw [add_assoc, Fin.val_add, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N),
      Nat.mod_eq_of_lt (by omega : 1 + 1 < N)] at this
    have hc := c.isLt
    rcases Nat.lt_or_ge (c.val + 2) N with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at this; omega
    · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at this; omega
  e_ne_f := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_add (c + 1), Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)] at this
    have hc := (c + 1).isLt
    rcases Nat.lt_or_ge ((c + 1).val + 1) N with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at this; omega
    · have : (c + 1).val + 1 = N := by omega
      simp_all

/-- The backward hop from `c` to `c - 2` on a ring of at least three sites. -/
def backward (hN : 3 ≤ N) (c : Fin N) : TeleportHop N where
  c := c
  e := c - 1
  f := c - 1 - 1
  k₁ := c - 1 - 1
  k₂ := c - 1
  bond_k₁ := by rw [bond, sub_add_cancel, Set.pair_comm]
  bond_k₂ := by rw [bond, sub_add_cancel, Set.pair_comm]
  c_ne_e := fun h => (forward hN (c - 1)).c_ne_e (by
    change c - 1 = c - 1 + 1
    rw [sub_add_cancel]
    exact h.symm)
  c_ne_f := fun h => (forward hN (c - 1 - 1)).c_ne_f (by
    change c - 1 - 1 = c - 1 - 1 + 1 + 1
    rw [sub_add_cancel, sub_add_cancel]
    exact h.symm)
  e_ne_f := fun h => (forward hN (c - 1 - 1)).c_ne_e (by
    change c - 1 - 1 = c - 1 - 1 + 1
    rw [sub_add_cancel]
    exact h.symm)

variable [NeZero d] (h : TeleportHop N)

/-- The gate of the first layer, on `{e, f}`: `F` at `e`, then `|a⟩_e |b⟩_f ↦ |a⟩_e |b + a⟩_f`,
which acts on vectors as `v ↦ v(x[f ↦ x_f - x_e])`. -/
noncomputable def gate₁ : Matrix (Cfg d N) (Cfg d N) ℂ :=
  (shiftPerm h.f (fun x => -x h.e) fun x c => by
    rw [Function.update_of_ne h.e_ne_f]).permMatrix ℂ *
    finKronecker (Function.update 1 h.e (quditFourier d))

/-- The gate of the second layer, on `{c, e}`: `|a⟩_c |b⟩_e ↦ |a⟩_c |b - a⟩_e`, acting on vectors
as `v ↦ v(x[e ↦ x_e + x_c])`, then `F` at `c`. -/
noncomputable def gate₂ : Matrix (Cfg d N) (Cfg d N) ℂ :=
  finKronecker (Function.update 1 h.c (quditFourier d)) *
    (shiftPerm h.e (fun x => x h.c) fun x c => by
      rw [Function.update_of_ne h.c_ne_e]).permMatrix ℂ

theorem gate₁_mem_unitary : h.gate₁ (d := d) ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ) :=
  Submonoid.mul_mem _ (Equiv.Perm.permMatrix_mem_unitaryGroup _)
    (finKronecker_mem_unitary fun i => by
      by_cases hi : i = h.e
      · subst hi; rw [Function.update_self]; exact quditFourier_mem_unitary
      · rw [Function.update_of_ne hi]; exact one_mem _)

theorem gate₂_mem_unitary : h.gate₂ (d := d) ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ) :=
  Submonoid.mul_mem _
    (finKronecker_mem_unitary fun i => by
      by_cases hi : i = h.c
      · subst hi; rw [Function.update_self]; exact quditFourier_mem_unitary
      · rw [Function.update_of_ne hi]; exact one_mem _)
    (Equiv.Perm.permMatrix_mem_unitaryGroup _)

theorem gate₁_mem_supportedOperators :
    h.gate₁ (d := d) ∈ supportedOperators d ({h.e, h.f} : Set (Fin N)) := by
  refine mul_mem_supportedOperators
    (IsLocalPerm.permMatrix_mem_supportedOperators
      (isLocalPerm_shiftPerm (Or.inr rfl) _ _ fun x y hxy => by rw [hxy h.e (Or.inl rfl)]))
    (finKronecker_mem_supportedOperators fun i hi => ?_)
  rw [Function.update_of_ne fun h' => hi (Or.inl h')]
  rfl

theorem gate₂_mem_supportedOperators :
    h.gate₂ (d := d) ∈ supportedOperators d ({h.c, h.e} : Set (Fin N)) := by
  refine mul_mem_supportedOperators (finKronecker_mem_supportedOperators fun i hi => ?_)
    (IsLocalPerm.permMatrix_mem_supportedOperators
      (isLocalPerm_shiftPerm (Or.inr rfl) _ _ fun x y hxy => by rw [hxy h.c (Or.inl rfl)]))
  rw [Function.update_of_ne fun h' => hi (Or.inl h')]
  rfl

/-- The operator of one hop before the correction, for the outcomes `z_c` and `z_e`: the two gates
followed by the projections onto `|z_c⟩` at `c` and `|z_e⟩` at `e`. -/
noncomputable def pre (z : Cfg d N) : Matrix (Cfg d N) (Cfg d N) ℂ :=
  ctrlProj {h.e} z * ctrlProj {h.c} z * h.gate₂ * h.gate₁

/-- The single-site unitaries left by one hop: `|z_c⟩` at `c` and `|z_e⟩` at `e`, prepared from
`|0⟩` by shifts, and `X^{z_e} Z^{z_c}` at `f`. -/
noncomputable def frame (z : Cfg d N) : Fin N → Matrix (Fin d) (Fin d) ℂ :=
  Function.update (Function.update
    (Function.update 1 h.c (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.c))))
    h.e (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.e)))) h.f (quditPauli (z h.c) (z h.e))

theorem frame_mem_unitary (z : Cfg d N) (i : Fin N) :
    h.frame z i ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  simp only [frame, Function.update_apply]
  split_ifs
  · exact quditPauli_mem_unitary _ _
  · exact Equiv.Perm.permMatrix_mem_unitaryGroup _
  · exact Equiv.Perm.permMatrix_mem_unitaryGroup _
  · exact one_mem _

theorem frame_of_ne (z : Cfg d N) {i : Fin N} (hc : i ≠ h.c) (he : i ≠ h.e) (hf : i ≠ h.f) :
    h.frame z i = 1 := by
  simp [frame, Function.update_of_ne, hc, he, hf]

/-- The configuration permutation exchanging the sites `c` and `f`. -/
def swapPerm : Equiv.Perm (Cfg d N) := cfgPerm (Equiv.swap h.c h.f)

/-- **One hop.** On a vector with `|0⟩` at `e` and `f`, the hop for the outcomes `z_c`, `z_e`
is `1/d` times the exchange of `c` and `f` followed by the single-site unitaries
`|0⟩ ↦ |z_c⟩` at `c`, `|0⟩ ↦ |z_e⟩` at `e`, and `X^{z_e} Z^{z_c}` at `f`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" (teleportation through a
nearest-neighbour entangled pair). -/
theorem pre_mulVec (z : Cfg d N) {v : Cfg d N → ℂ} (hv : IsZeroOn {h.e, h.f} v) :
    h.pre z *ᵥ v = (d : ℂ)⁻¹ •
      (finKronecker (h.frame z) *ᵥ (h.swapPerm.permMatrix ℂ *ᵥ v)) := by
  classical
  have hce := h.c_ne_e
  have hcf := h.c_ne_f
  have hef := h.e_ne_f
  set s : ℂ := ((Real.sqrt d : ℝ) : ℂ)⁻¹ with hs
  have hF0 : ∀ a, quditFourier d a 0 = s := fun a => by simp [quditFourier_apply, s]
  have hss : s * s = (d : ℂ)⁻¹ := by
    rw [hs, Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg _)]
    push_cast
    rfl
  have hve : ∀ x, x h.e ≠ 0 → v x = 0 := fun x hx => by
    by_contra hne; exact hx (hv x hne h.e (Or.inl rfl))
  have hvf : ∀ x, x h.f ≠ 0 → v x = 0 := fun x hx => by
    by_contra hne; exact hx (hv x hne h.f (Or.inr rfl))
  -- The first layer.
  have h1 : finKronecker (Function.update 1 h.e (quditFourier d)) *ᵥ v =
      fun w => s * v (Function.update w h.e 0) := by
    funext w
    rw [finKronecker_update_one_mulVec_apply, Finset.sum_eq_single 0]
    · rw [hF0]
    · intro j _ hj
      rw [hve _ (by simpa using hj), mul_zero]
    · simp
  have hG1 : h.gate₁ *ᵥ v = fun w =>
      s * v (Function.update (Function.update w h.f (w h.f + -w h.e)) h.e 0) := by
    rw [gate₁, ← mulVec_mulVec, h1, permMatrix_mulVec]
    rfl
  -- The second layer.
  have hG2 : ∀ y, (h.gate₂ *ᵥ (h.gate₁ *ᵥ v)) y =
      quditFourier d (y h.c) (y h.f - y h.e) * s *
        v (Function.update (Function.update (Function.update y h.c (y h.f - y h.e)) h.e 0)
          h.f 0) := by
    intro y
    rw [gate₂, ← mulVec_mulVec, hG1, permMatrix_mulVec, finKronecker_update_one_mulVec_apply,
      Finset.sum_eq_single (y h.f - y h.e)]
    · simp only [Function.comp_apply, shiftPerm_apply]
      rw [← mul_assoc]
      congr 2
      funext i
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · intro j _ hj
      simp only [Function.comp_apply, shiftPerm_apply]
      rw [hvf, mul_zero, mul_zero]
      simp only [Function.update_apply, ite_eq_right hef.symm, ite_eq_right hcf.symm,
        ite_eq_right hce.symm]
      intro h0
      apply hj
      simp only [ite_true] at h0
      rw [add_neg_eq_zero] at h0
      rw [h0, add_sub_cancel_left]
    · simp
  -- The frame is a product of three single-site operators.
  have hframe : finKronecker (h.frame z) =
      finKronecker (Function.update 1 h.c (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.c)))) *
        (finKronecker (Function.update 1 h.e (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.e)))) *
          finKronecker (Function.update 1 h.f (quditPauli (z h.c) (z h.e)))) := by
    rw [finKronecker_mul, finKronecker_mul]
    congr 1
    funext i
    simp only [frame, Function.update_apply, Pi.one_apply]
    split_ifs <;> simp_all
  funext y
  have hL : (h.pre z *ᵥ v) y = (if y h.e = z h.e then 1 else 0) *
      ((if y h.c = z h.c then 1 else 0) * (h.gate₂ *ᵥ (h.gate₁ *ᵥ v)) y) := by
    simp only [pre, ← mulVec_mulVec, ctrlProj, mulVec_diagonal, Finset.mem_singleton, forall_eq]
  rw [hL, hG2, Pi.smul_apply, smul_eq_mul, hframe, ← mulVec_mulVec, ← mulVec_mulVec,
    finKronecker_update_one_permMatrix_mulVec, finKronecker_update_one_permMatrix_mulVec]
  simp only [finKronecker_update_one_mulVec_apply, quditPauli_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, permMatrix_mulVec, Function.comp_apply,
    swapPerm, cfgPerm_apply, Equiv.subRight_apply]
  simp only [Function.update_apply, ite_eq_right hef.symm, ite_eq_right hcf.symm,
    ite_eq_right hce.symm]
  by_cases he : y h.e = z h.e
  · by_cases hc : y h.c = z h.c
    · rw [ite_eq_left he, ite_eq_left hc, one_mul, one_mul, quditFourier_apply, ← hss, he, hc]
      have hcfg : Function.update (Function.update (Function.update y h.c (y h.f - z h.e)) h.e 0)
          h.f 0 = Function.update (Function.update (Function.update y h.c (z h.c - z h.c)) h.e
            (z h.e - z h.e)) h.f (y h.f - z h.e) ∘ ⇑(Equiv.swap h.c h.f) := by
        funext i
        simp only [Function.comp_apply, Equiv.swap_apply_def, Function.update_apply]
        split_ifs <;> simp_all
      rw [hcfg, ← hs]
      ring
    · rw [ite_eq_left he, ite_eq_right hc, mul_zero, hvf, mul_zero, mul_zero]
      simp only [Function.comp_apply, Equiv.swap_apply_right, Function.update_apply,
        ite_eq_right hcf, ite_eq_right hce, ite_true]
      exact sub_ne_zero.mpr hc
  · rw [ite_eq_right he, hve, mul_zero, mul_zero]
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hce.symm hef,
      Function.update_apply, ite_eq_right hef, ite_true]
    exact sub_ne_zero.mpr he

end TeleportHop

end MPSPreparation
