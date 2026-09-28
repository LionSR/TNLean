/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.LocalChannelCircuit

/-!
# Onsite channels and local channel conversions

An onsite channel between local dimensions `d` and `e` on a chain of `N` sites is a tensor
product `⊗ᵢ Φᵢ` of channels `Φᵢ : M_d → M_e`, one per site. Attaching an ancilla in a fixed
state at every site and discarding the ancilla of every site are onsite channels. A *local
channel conversion* of depth `T` alternates onsite channels with `T` layers of local channels
on pairs of neighbouring sites,
`Φ_T ∘ L_T ∘ Φ_{T-1} ∘ ⋯ ∘ L_1 ∘ Φ_0`, where the local dimension may change at each onsite
channel. This is the channel form of the circuits `V' = U_ℓ V_ℓ ⋯ U_1 V_1 U_0` of
arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC", with ancillas attached to
each site, local operations between the layers, and "ancillas traced out at the end", but
without measurements or classical communication.

Local channel conversion is a directed relation: it is reflexive at depth `0` and transitive
with additive depth, but it is not symmetric, since a channel need not be undone by another
channel. The two facts proved here are its transitivity and its basic obstruction:

* conversions compose, and the depths add (`IsLocalChannelConversion.trans`);
* a density matrix obtained from a product density by a conversion of depth `T` has vanishing
  connected correlations for operators at ring distance larger than `2T`
  (`trace_mul_mul_eq_of_isLocalChannelConversion`).

The second fact rests on the Heisenberg locality of onsite channels: the dual of an onsite
channel maps an operator acting on `X` to an operator acting on the same set `X`
(`OnsiteChannel.dual_mem_supportedOperators`), and it is multiplicative on operators acting on
disjoint sets (`OnsiteChannel.dual_mul`).

## Conventions

The local dimension of a site carrying `a` ancilla levels next to a `d`-level system is
`d * a`, with the pair `(x, b) : Fin d × Fin a` encoded as `finProdFinEquiv (x, b)`. An onsite
channel is given by rectangular Kraus operators `Kᵢⱼ : e × d` at each site `i` with
`∑ⱼ Kᵢⱼ† Kᵢⱼ = 1`; its Kraus operators on the chain are the products `⊗ᵢ K_{i J(i)}` over
choice functions `J`.

## Main definitions

* `MPSPreparation.OnsiteChannel` — an onsite channel between two local dimensions, with its
  map `OnsiteChannel.map` and Heisenberg dual `OnsiteChannel.dual`.
* `MPSPreparation.OnsiteChannel.id`, `MPSPreparation.OnsiteChannel.attach`,
  `MPSPreparation.OnsiteChannel.attachZero`, `MPSPreparation.OnsiteChannel.discard` — the
  identity, attaching an ancilla in a fixed state, and discarding the ancilla.
* `MPSPreparation.IsLocalChannelProtocol` — maps of the form
  `Φ_T ∘ L_T ∘ ⋯ ∘ L_1 ∘ Φ_0` with `T` channel layers `L_t`.
* `MPSPreparation.IsLocalChannelConversion` — conversion of one density matrix into another
  by such a map of depth at most `T`.

## Main results

* `MPSPreparation.OnsiteChannel.map_isKrausCPTP`, `MPSPreparation.OnsiteChannel.map_finKronecker`
  — onsite channels are channels and map product operators to product operators.
* `MPSPreparation.OnsiteChannel.dual_mem_supportedOperators`,
  `MPSPreparation.OnsiteChannel.dual_mul` — Heisenberg locality of onsite channels.
* `MPSPreparation.IsLocalChannelProtocol.isKrausCPTP` — a conversion map is a channel.
* `MPSPreparation.IsLocalChannelConversion.refl`, `MPSPreparation.IsLocalChannelConversion.trans`
  — reflexivity at depth `0` and composition with additive depth.
* `MPSPreparation.isLocalChannelConversion_circuit` — attaching ancillas, running a local
  channel circuit of depth `T` and discarding is a conversion of depth `T`.
* `MPSPreparation.trace_mul_mul_eq_of_isLocalChannelConversion` — vanishing connected
  correlations beyond distance `2T` for densities converted from product densities.

## Follow-ups

Approximate conversions in trace norm with polylogarithmic depth, as in the phase equivalence
of arXiv:2103.13367, are not treated here. Blocking a fixed number of sites into one, which
changes the number of sites, is not treated here. Measurements with classical feedforward,
the LOCC part of arXiv:2103.13367, are not treated here.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), main text, paragraph "Quantum circuits and
  LOCC" (ancillas attached to each site, local unitaries on each site and its ancillas between
  the layers of a circuit), paragraph "Phases of matter" (protocols "where ancillas are traced
  out at the end" define a channel), and Proposition `propQCA2`, eq. `eq:necessary_condition`.
* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), main text before Theorem 1 (local circuits).
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder

namespace MPSPreparation

variable {d e f N : ℕ}

/-! ### Rectangular product operators -/

/-- The Kraus map whose Kraus operators are the products `⊗ᵢ K_{i J(i)}` maps a product
operator `⊗ᵢ mᵢ` to the product `⊗ᵢ ∑ⱼ Kᵢⱼ mᵢ Kᵢⱼ†`. -/
theorem rectangularKrausMap_rectKronecker_finKronecker {r : Fin N → ℕ}
    (K : (i : Fin N) → Fin (r i) → Matrix (Fin e) (Fin d) ℂ)
    (m : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    rectangularKrausMap (fun J : (i : Fin N) → Fin (r i) ↦ rectKronecker fun i ↦ K i (J i))
        (finKronecker m) =
      finKronecker fun i ↦ rectangularKrausMap (K i) (m i) := by
  change ∑ J, _ * _ * _ = _
  simp only [rectKronecker_conjTranspose, ← rectKronecker_eq_finKronecker, rectKronecker_mul]
  exact sum_rectKronecker fun i j ↦ K i j * m i * (K i j)ᴴ

/-! ### Onsite channels -/

/-- An *onsite channel* from `d`-level to `e`-level sites on a chain of `N` sites: at each site
`i` a channel `M_d → M_e` given by Kraus operators `kraus i j : e × d` with
`∑ⱼ (kraus i j)† (kraus i j) = 1`. On the chain it acts as the tensor product of these
channels.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (local operations
`U = ⊗ᵢ uᵢ` acting on each site and its ancillas, with ancillas "initialized in a product
state"), with channels in place of unitaries so that attaching and discarding ancillas are
included. -/
structure OnsiteChannel (d e N : ℕ) where
  /-- The number of Kraus operators of the channel at site `i`. -/
  r : Fin N → ℕ
  /-- The Kraus operators of the channel at site `i`. -/
  kraus : (i : Fin N) → Fin (r i) → Matrix (Fin e) (Fin d) ℂ
  sum_kraus : ∀ i, ∑ j, (kraus i j)ᴴ * kraus i j = 1

namespace OnsiteChannel

/-- The channel `M_d → M_e` at site `i`. -/
noncomputable def siteMap (Φ : OnsiteChannel d e N) (i : Fin N) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin e) (Fin e) ℂ :=
  rectangularKrausMap (Φ.kraus i)

/-- The Heisenberg dual `M_e → M_d` of the channel at site `i`. -/
noncomputable def siteDual (Φ : OnsiteChannel d e N) (i : Fin N) :
    Matrix (Fin e) (Fin e) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  rectangularKrausMap fun j ↦ (Φ.kraus i j)ᴴ

/-- The Kraus operator `⊗ᵢ K_{i J(i)}` of an onsite channel on the chain, for a choice
function `J` of one Kraus index per site. -/
def krausOp (Φ : OnsiteChannel d e N) (J : (i : Fin N) → Fin (Φ.r i)) :
    Matrix (Cfg e N) (Cfg d N) ℂ :=
  rectKronecker fun i ↦ Φ.kraus i (J i)

/-- The map of an onsite channel on density matrices of the chain.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (local operations
on each site and its ancillas). -/
noncomputable def map (Φ : OnsiteChannel d e N) :
    Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ :=
  rectangularKrausMap Φ.krausOp

/-- The Heisenberg dual of an onsite channel. -/
noncomputable def dual (Φ : OnsiteChannel d e N) :
    Matrix (Cfg e N) (Cfg e N) ℂ →ₗ[ℂ] Matrix (Cfg d N) (Cfg d N) ℂ :=
  rectangularKrausMap fun J ↦ (Φ.krausOp J)ᴴ

theorem sum_krausOp (Φ : OnsiteChannel d e N) :
    ∑ J, (Φ.krausOp J)ᴴ * Φ.krausOp J = 1 := by
  simp only [krausOp, rectKronecker_conjTranspose, rectKronecker_mul]
  rw [sum_rectKronecker fun i j ↦ (Φ.kraus i j)ᴴ * Φ.kraus i j]
  simp only [Φ.sum_kraus, rectKronecker_eq_finKronecker, finKronecker_one]

/-- An onsite channel is trace-preserving and completely positive. -/
theorem map_isKrausCPTP (Φ : OnsiteChannel d e N) : IsKrausCPTP Φ.map :=
  rectangularKrausMap_isKrausCPTP _ Φ.sum_krausOp

/-- An onsite channel maps the product operator `⊗ᵢ σᵢ` to `⊗ᵢ Φᵢ(σᵢ)`. -/
theorem map_finKronecker (Φ : OnsiteChannel d e N) (σ : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Φ.map (finKronecker σ) = finKronecker fun i ↦ Φ.siteMap i (σ i) :=
  rectangularKrausMap_rectKronecker_finKronecker Φ.kraus σ

/-- The dual of an onsite channel maps the product operator `⊗ᵢ mᵢ` to `⊗ᵢ Φᵢ†(mᵢ)`. -/
theorem dual_finKronecker (Φ : OnsiteChannel d e N) (m : Fin N → Matrix (Fin e) (Fin e) ℂ) :
    Φ.dual (finKronecker m) = finKronecker fun i ↦ Φ.siteDual i (m i) := by
  simp only [dual, krausOp, rectKronecker_conjTranspose]
  exact rectangularKrausMap_rectKronecker_finKronecker (fun i j ↦ (Φ.kraus i j)ᴴ) m

/-- The dual of a channel is unital. -/
theorem siteDual_one (Φ : OnsiteChannel d e N) (i : Fin N) : Φ.siteDual i 1 = 1 := by
  change ∑ j, (Φ.kraus i j)ᴴ * 1 * (Φ.kraus i j)ᴴᴴ = 1
  simpa only [conjTranspose_conjTranspose, Matrix.mul_one] using Φ.sum_kraus i

/-- Schrödinger–Heisenberg duality for an onsite channel: `tr(Φ(ρ) A) = tr(ρ Φ†(A))`. -/
theorem trace_map_mul (Φ : OnsiteChannel d e N) (ρ : Matrix (Cfg d N) (Cfg d N) ℂ)
    (A : Matrix (Cfg e N) (Cfg e N) ℂ) : trace (Φ.map ρ * A) = trace (ρ * Φ.dual A) :=
  trace_rectangularKrausMap_mul _ ρ A

/-- **Heisenberg locality of onsite channels.** The dual of an onsite channel maps an operator
acting on the sites `X` to an operator acting on the same sites: onsite channels do not
spread supports.

Source: arXiv:2103.13367, Supplemental Material, proof of the area law ("`U_n ∈ LU`, so it
does not increase" the entanglement across a cut), in the Heisenberg picture. -/
theorem dual_mem_supportedOperators (Φ : OnsiteChannel d e N) {X : Set (Fin N)}
    {A : Matrix (Cfg e N) (Cfg e N) ℂ} (hA : A ∈ supportedOperators e X) :
    Φ.dual A ∈ supportedOperators d X := by
  refine (Submodule.span_le (p := (supportedOperators d X).comap Φ.dual)).mpr ?_ hA
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, dual_finKronecker]
  exact finKronecker_mem_supportedOperators fun i hi ↦ by rw [hm i hi, siteDual_one]

/-- The dual of an onsite channel is multiplicative on operators acting on disjoint sets of
sites. -/
theorem dual_mul (Φ : OnsiteChannel d e N) {X Y : Set (Fin N)} (hXY : Disjoint X Y)
    {A B : Matrix (Cfg e N) (Cfg e N) ℂ} (hA : A ∈ supportedOperators e X)
    (hB : B ∈ supportedOperators e Y) : Φ.dual (A * B) = Φ.dual A * Φ.dual B := by
  have key := eq_of_mem_supportedOperators₂
    ((LinearMap.mul ℂ (Matrix (Cfg e N) (Cfg e N) ℂ)).compr₂ Φ.dual)
    ((LinearMap.mul ℂ (Matrix (Cfg d N) (Cfg d N) ℂ)).compl₁₂ Φ.dual Φ.dual)
    (fun m m' hm hm' ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
      rw [finKronecker_mul, dual_finKronecker, dual_finKronecker, dual_finKronecker,
        finKronecker_mul]
      congr 1
      funext i
      by_cases hi : i ∈ X
      · rw [hm' i (Set.disjoint_left.mp hXY hi), Matrix.mul_one, siteDual_one, Matrix.mul_one]
      · rw [hm i hi, Matrix.one_mul, siteDual_one, Matrix.one_mul]) hA hB
  simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] using key

/-! ### Identity, attaching and discarding ancillas -/

/-- The identity onsite channel, with the single Kraus operator `1` at every site. -/
def id (d N : ℕ) : OnsiteChannel d d N where
  r _ := 1
  kraus _ _ := 1
  sum_kraus _ := by simp

theorem id_map (d N : ℕ) : (OnsiteChannel.id d N).map = LinearMap.id := by
  refine LinearMap.ext fun X ↦ ?_
  change ∑ _ : (i : Fin N) → Fin 1, rectKronecker (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) * X *
    (rectKronecker fun _ ↦ 1)ᴴ = X
  simp [rectKronecker_eq_finKronecker]

/-- The Kraus operator `x ↦ x ⊗ v` of attaching an ancilla vector `v : Fin a → ℂ` to a
`d`-level site, the pair `(x, b)` being encoded as `finProdFinEquiv (x, b)`. -/
def ancillaKraus (d : ℕ) {a : ℕ} (v : Fin a → ℂ) : Matrix (Fin (d * a)) (Fin d) ℂ :=
  Matrix.of fun p y ↦ if (finProdFinEquiv.symm p).1 = y then v (finProdFinEquiv.symm p).2 else 0

theorem ancillaKraus_apply {a : ℕ} (v : Fin a → ℂ) (x y : Fin d) (b : Fin a) :
    ancillaKraus d v (finProdFinEquiv (x, b)) y = if x = y then v b else 0 := by
  simp only [ancillaKraus, of_apply, Equiv.symm_apply_apply]

theorem conjTranspose_ancillaKraus_mul {a : ℕ} (v : Fin a → ℂ) :
    (ancillaKraus d v)ᴴ * ancillaKraus d v = (star v ⬝ᵥ v) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext y y'
  rw [mul_apply, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single y (fun x _ hx ↦ Finset.sum_eq_zero fun b _ ↦ by
      simp [conjTranspose_apply, ancillaKraus_apply, hx]) (fun h ↦ absurd (Finset.mem_univ _) h)]
  by_cases h : y = y'
  · subst h
    simp [conjTranspose_apply, ancillaKraus_apply, dotProduct]
  · simp [conjTranspose_apply, ancillaKraus_apply, h]

/-- Attaching at every site an `a`-level ancilla in the density `∑ₖ wₖ wₖ†`, given by vectors
`wₖ` with `∑ₖ ‖wₖ‖² = 1`.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" ("adding ancillas
(initialized in a product state) … to each lattice site"). -/
noncomputable def attach (d N : ℕ) {a s : ℕ} (w : Fin s → Fin a → ℂ)
    (hw : ∑ k, star (w k) ⬝ᵥ w k = 1) : OnsiteChannel d (d * a) N where
  r _ := s
  kraus _ k := ancillaKraus d (w k)
  sum_kraus _ := by
    simp only [conjTranspose_ancillaKraus_mul, ← Finset.sum_smul, hw, one_smul]

/-- Attaching an ancilla maps `X` to `X ⊗ τ` with `τ = ∑ₖ wₖ wₖ†`. -/
theorem attach_siteMap_apply {a s : ℕ} (w : Fin s → Fin a → ℂ)
    (hw : ∑ k, star (w k) ⬝ᵥ w k = 1) (i : Fin N) (X : Matrix (Fin d) (Fin d) ℂ)
    (x y : Fin d) (b c : Fin a) :
    (attach d N w hw).siteMap i X (finProdFinEquiv (x, b)) (finProdFinEquiv (y, c)) =
      X x y * ∑ k, w k b * star (w k c) := by
  change (∑ k, ancillaKraus d (w k) * X * (ancillaKraus d (w k))ᴴ :
    Matrix (Fin (d * a)) (Fin (d * a)) ℂ) _ _ = _
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, ancillaKraus_apply, Finset.mul_sum,
    apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-- Attaching the ancilla state `|0⟩` at every site. -/
noncomputable def attachZero (d a N : ℕ) [NeZero a] : OnsiteChannel d (d * a) N :=
  attach d N (fun _ : Fin 1 ↦ Pi.single 0 1) (by simp)

/-- The Kraus operator `x ⊗ b ↦ x`, for a fixed ancilla level `b`, of discarding an `a`-level
ancilla. -/
def discardKraus (d : ℕ) {a : ℕ} (b : Fin a) : Matrix (Fin d) (Fin (d * a)) ℂ :=
  Matrix.of fun y p ↦ if p = finProdFinEquiv (y, b) then 1 else 0

/-- Discarding at every site an `a`-level ancilla: the partial trace over the ancilla factor.

Source: arXiv:2103.13367, main text, paragraph "Phases of matter" (protocols "where ancillas
are traced out at the end"). -/
def discard (d a N : ℕ) : OnsiteChannel (d * a) d N where
  r _ := a
  kraus _ b := discardKraus d b
  sum_kraus _ := by
    ext p q
    have h := finProdFinEquiv.sum_comp fun r : Fin (d * a) ↦
      if p = r then (if q = r then (1 : ℂ) else 0) else 0
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, discardKraus, of_apply,
      apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
    rw [h]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_apply]
    exact if_congr eq_comm rfl rfl

/-- Discarding the ancilla is the partial trace `Y ↦ ∑_b Y_{(x, b), (y, b)}`. -/
theorem discard_siteMap_apply {a : ℕ} (i : Fin N) (Y : Matrix (Fin (d * a)) (Fin (d * a)) ℂ)
    (x y : Fin d) :
    (discard d a N).siteMap i Y x y =
      ∑ b, Y (finProdFinEquiv (x, b)) (finProdFinEquiv (y, b)) := by
  change (∑ b : Fin a, discardKraus d b * Y * (discardKraus d b)ᴴ :
    Matrix (Fin d) (Fin d) ℂ) x y = _
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, discardKraus, of_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp [ite_mul, mul_ite, Finset.sum_ite_eq']

/-- Discarding an attached ancilla gives back the one-site operator. -/
theorem discard_siteMap_attach_siteMap {a s : ℕ} (w : Fin s → Fin a → ℂ)
    (hw : ∑ k, star (w k) ⬝ᵥ w k = 1) (i : Fin N) (X : Matrix (Fin d) (Fin d) ℂ) :
    (discard d a N).siteMap i ((attach d N w hw).siteMap i X) = X := by
  ext x y
  simp only [discard_siteMap_apply, attach_siteMap_apply, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [dotProduct, Pi.star_apply] at hw
  rw [show ∑ k, ∑ b, w k b * star (w k b) = 1 by
    rw [← hw]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_comm _ _]
  exact mul_one _

end OnsiteChannel

/-! ### Local channel conversions -/

section Ring

open Fin.CommRing

variable [NeZero N]

/-- The maps `Φ_T ∘ L_T ∘ Φ_{T-1} ∘ ⋯ ∘ L_1 ∘ Φ_0` alternating onsite channels `Φ_t`, which may
change the local dimension, with `T` layers `L_t` of local channels on pairs of neighbouring
sites.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC": the circuits
`V' = U_ℓ V_ℓ ⋯ U_1 V_1 U_0` with local operations `U_n` on each site and its ancillas
between the layers `V_n`, here with channels in place of unitaries and without measurements;
attaching and discarding ancillas are onsite channels. -/
inductive IsLocalChannelProtocol :
    {d e : ℕ} → ℕ → (Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ) → Prop
  /-- An onsite channel is a protocol without layers. -/
  | onsite {d e : ℕ} (Φ : OnsiteChannel d e N) : IsLocalChannelProtocol 0 Φ.map
  /-- A layer of local channels applied after a protocol adds one to its depth. -/
  | layer {d e T : ℕ} {Ψ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ}
      (hΨ : IsLocalChannelProtocol T Ψ) (L : ChannelLayer e N) :
      IsLocalChannelProtocol (T + 1) (L.map ∘ₗ Ψ)
  /-- An onsite channel applied after a protocol keeps its depth. -/
  | onsite_comp {d e f T : ℕ}
      {Ψ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ}
      (hΨ : IsLocalChannelProtocol T Ψ) (Φ : OnsiteChannel e f N) :
      IsLocalChannelProtocol T (Φ.map ∘ₗ Ψ)

namespace IsLocalChannelProtocol

/-- A local channel protocol is trace-preserving and completely positive. -/
theorem isKrausCPTP {T : ℕ}
    {Ψ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ}
    (h : IsLocalChannelProtocol T Ψ) : IsKrausCPTP Ψ := by
  induction h with
  | onsite Φ => exact Φ.map_isKrausCPTP
  | layer _ L ih => exact isKrausCPTP_comp ih L.map_isKrausCPTP
  | onsite_comp _ Φ ih => exact isKrausCPTP_comp ih Φ.map_isKrausCPTP

/-- Protocols compose, and their depths add. -/
theorem comp {T₁ T₂ : ℕ}
    {Ψ₁ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ}
    {Ψ₂ : Matrix (Cfg e N) (Cfg e N) ℂ →ₗ[ℂ] Matrix (Cfg f N) (Cfg f N) ℂ}
    (h₁ : IsLocalChannelProtocol T₁ Ψ₁) (h₂ : IsLocalChannelProtocol T₂ Ψ₂) :
    IsLocalChannelProtocol (T₁ + T₂) (Ψ₂ ∘ₗ Ψ₁) := by
  induction h₂ with
  | onsite Φ => exact h₁.onsite_comp Φ
  | layer _ L ih => exact ih.layer L
  | onsite_comp _ Φ ih => exact ih.onsite_comp Φ

/-- Applying a local channel circuit after a protocol adds its number of layers to the
depth. -/
theorem channelCircuitMap_comp {T : ℕ}
    {Ψ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ}
    (h : IsLocalChannelProtocol T Ψ) (Ls : List (ChannelLayer e N)) :
    IsLocalChannelProtocol (T + Ls.length) (channelCircuitMap Ls ∘ₗ Ψ) := by
  induction Ls generalizing T Ψ with
  | nil => exact h
  | cons L Ls ih =>
    have := ih (h.layer L)
    rw [List.length_cons, show T + (Ls.length + 1) = T + 1 + Ls.length by omega]
    exact this

/-- **Light cone of a protocol.** A protocol of depth `T` has a Heisenberg dual for the trace
pairing that maps operators acting on `X` to operators acting on the sites within ring
distance `T` of `X`, and is multiplicative on operators acting on sets whose
`T`-neighbourhoods are disjoint.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the light cone of a
depth-`T` circuit), here with channels and onsite operations. -/
theorem exists_dual {T : ℕ}
    {Ψ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg e N) (Cfg e N) ℂ}
    (h : IsLocalChannelProtocol T Ψ) :
    ∃ Ψ' : Matrix (Cfg e N) (Cfg e N) ℂ →ₗ[ℂ] Matrix (Cfg d N) (Cfg d N) ℂ,
      (∀ ρ A, trace (Ψ ρ * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Set (Fin N), ∀ A ∈ supportedOperators e X,
        Ψ' A ∈ supportedOperators d (neighbourhood X T)) ∧
      (∀ X Y : Set (Fin N), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ supportedOperators e X, ∀ B ∈ supportedOperators e Y,
          Ψ' (A * B) = Ψ' A * Ψ' B) := by
  induction h with
  | onsite Φ =>
    refine ⟨Φ.dual, Φ.trace_map_mul, fun X A hA ↦ ?_, fun X Y hXY A hA B hB ↦ ?_⟩
    · exact supportedOperators_mono (subset_neighbourhood X 0) (Φ.dual_mem_supportedOperators hA)
    · exact Φ.dual_mul (hXY.mono (subset_neighbourhood X 0) (subset_neighbourhood Y 0)) hA hB
  | @layer e T Ψ _ L ih =>
    obtain ⟨Ψ', hdual, hcone, hmul⟩ := ih
    have hsub (Z : Set (Fin N)) : neighbourhood (neighbourhood Z 1) T ⊆ neighbourhood Z (T + 1) :=
      by simpa only [add_comm] using neighbourhood_neighbourhood_subset Z 1 T
    refine ⟨Ψ' ∘ₗ L.dual, fun ρ A ↦ ?_, fun X A hA ↦ ?_, fun X Y hXY A hA B hB ↦ ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hdual]
      exact L.trace_map_mul _ A
    · exact supportedOperators_mono (hsub X) (hcone _ _ (L.dual_mem_supportedOperators hA))
    · have hXY' := hXY.mono (hsub X) (hsub Y)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        L.dual_mul (hXY'.mono (subset_neighbourhood _ T) (subset_neighbourhood _ T)) hA hB]
      exact hmul _ _ hXY' _ (L.dual_mem_supportedOperators hA) _ (L.dual_mem_supportedOperators hB)
  | onsite_comp _ Φ ih =>
    obtain ⟨Ψ', hdual, hcone, hmul⟩ := ih
    refine ⟨Ψ' ∘ₗ Φ.dual, fun ρ A ↦ ?_, fun X A hA ↦ ?_, fun X Y hXY A hA B hB ↦ ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hdual]
      exact Φ.trace_map_mul _ A
    · exact hcone X _ (Φ.dual_mem_supportedOperators hA)
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        Φ.dual_mul (hXY.mono (subset_neighbourhood X _) (subset_neighbourhood Y _)) hA hB]
      exact hmul X Y hXY _ (Φ.dual_mem_supportedOperators hA) _ (Φ.dual_mem_supportedOperators hB)

end IsLocalChannelProtocol

/-- A density matrix `ρ` on `d`-level sites is *locally convertible in depth `T`* into a
density matrix `σ` on `d'`-level sites when `σ = Ψ(ρ)` for a protocol `Ψ` of depth at most `T`
alternating onsite channels (attaching ancillas, local operations on each site and its
ancillas, discarding ancillas) with layers of local channels on pairs of neighbouring sites.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (circuits
`V' = U_ℓ V_ℓ ⋯ U_1 V_1 U_0` with ancillas) and paragraph "Phases of matter" (a protocol
"where ancillas are traced out at the end, defines a quantum channel"), without measurements
or classical communication. -/
def IsLocalChannelConversion {d' : ℕ} (T : ℕ) (ρ : Matrix (Cfg d N) (Cfg d N) ℂ)
    (σ : Matrix (Cfg d' N) (Cfg d' N) ℂ) : Prop :=
  ∃ T' ≤ T, ∃ Ψ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg d' N) (Cfg d' N) ℂ,
    IsLocalChannelProtocol T' Ψ ∧ Ψ ρ = σ

namespace IsLocalChannelConversion

variable {d' d'' : ℕ}

/-- Every density matrix is converted into itself in depth `0`. -/
theorem refl (ρ : Matrix (Cfg d N) (Cfg d N) ℂ) : IsLocalChannelConversion 0 ρ ρ :=
  ⟨0, le_rfl, _, .onsite (OnsiteChannel.id d N), by rw [OnsiteChannel.id_map, LinearMap.id_apply]⟩

theorem mono {T T' : ℕ} {ρ : Matrix (Cfg d N) (Cfg d N) ℂ} {σ : Matrix (Cfg d' N) (Cfg d' N) ℂ}
    (h : IsLocalChannelConversion T ρ σ) (hT : T ≤ T') : IsLocalChannelConversion T' ρ σ := by
  obtain ⟨T₀, hT₀, Ψ, hΨ, rfl⟩ := h
  exact ⟨T₀, hT₀.trans hT, Ψ, hΨ, rfl⟩

/-- **Composition of conversions.** Converting `ρ` into `σ` in depth `T₁` and `σ` into `τ` in
depth `T₂` converts `ρ` into `τ` in depth `T₁ + T₂`.

Source: arXiv:2103.13367, main text, paragraph "Phases of matter" (composing transformations
requires adding their depths). -/
theorem trans {T₁ T₂ : ℕ} {ρ : Matrix (Cfg d N) (Cfg d N) ℂ}
    {σ : Matrix (Cfg d' N) (Cfg d' N) ℂ} {τ : Matrix (Cfg d'' N) (Cfg d'' N) ℂ}
    (h₁ : IsLocalChannelConversion T₁ ρ σ) (h₂ : IsLocalChannelConversion T₂ σ τ) :
    IsLocalChannelConversion (T₁ + T₂) ρ τ := by
  obtain ⟨S₁, hS₁, Ψ₁, hΨ₁, rfl⟩ := h₁
  obtain ⟨S₂, hS₂, Ψ₂, hΨ₂, rfl⟩ := h₂
  exact ⟨S₁ + S₂, add_le_add hS₁ hS₂, _, hΨ₁.comp hΨ₂, rfl⟩

/-- A conversion is realized by a trace-preserving completely positive map. -/
theorem exists_isKrausCPTP {T : ℕ} {ρ : Matrix (Cfg d N) (Cfg d N) ℂ}
    {σ : Matrix (Cfg d' N) (Cfg d' N) ℂ} (h : IsLocalChannelConversion T ρ σ) :
    ∃ Ψ : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ] Matrix (Cfg d' N) (Cfg d' N) ℂ,
      IsKrausCPTP Ψ ∧ Ψ ρ = σ := by
  obtain ⟨_, -, Ψ, hΨ, rfl⟩ := h
  exact ⟨Ψ, hΨ.isKrausCPTP, rfl⟩

/-- A conversion maps density matrices to density matrices. -/
theorem density {T : ℕ} {ρ : Matrix (Cfg d N) (Cfg d N) ℂ}
    {σ : Matrix (Cfg d' N) (Cfg d' N) ℂ} (h : IsLocalChannelConversion T ρ σ)
    (hρ : ρ.PosSemidef ∧ trace ρ = 1) : σ.PosSemidef ∧ trace σ = 1 := by
  obtain ⟨Ψ, hΨ, rfl⟩ := h.exists_isKrausCPTP
  exact ⟨hΨ.map_posSemidef hρ.1, (hΨ.trace_map ρ).trans hρ.2⟩

end IsLocalChannelConversion

/-- Attaching ancillas by an onsite channel, running a local channel circuit with at most `T`
layers on the enlarged sites, and discarding by a second onsite channel is a conversion of
depth `T`.

Source: arXiv:2103.13367, main text, paragraph "Phases of matter" ("a given preparation
protocol … (where ancillas are traced out at the end), defines a quantum channel"). -/
theorem isLocalChannelConversion_circuit {d' T : ℕ} (In : OnsiteChannel d e N)
    (Ls : List (ChannelLayer e N)) (hLs : Ls.length ≤ T) (Out : OnsiteChannel e d' N)
    (ρ : Matrix (Cfg d N) (Cfg d N) ℂ) :
    IsLocalChannelConversion T ρ (Out.map (channelCircuitMap Ls (In.map ρ))) := by
  exact ⟨0 + Ls.length, by omega, _,
    ((IsLocalChannelProtocol.onsite In).channelCircuitMap_comp Ls).onsite_comp Out, rfl⟩

/-- A density matrix prepared from a product density by a local channel circuit of depth `T`
is converted from that product density in depth `T`. -/
theorem IsChannelPreparedInDepth.exists_isLocalChannelConversion {T : ℕ}
    {ρ : Matrix (Cfg d N) (Cfg d N) ℂ} (h : IsChannelPreparedInDepth T ρ) :
    ∃ σ : Fin N → Matrix (Fin d) (Fin d) ℂ, (∀ i, (σ i).PosSemidef ∧ trace (σ i) = 1) ∧
      IsLocalChannelConversion T (finKronecker σ) ρ := by
  obtain ⟨Ls, rfl, σ, hσ, rfl⟩ := h
  refine ⟨σ, hσ, ?_⟩
  simpa [OnsiteChannel.id_map] using isLocalChannelConversion_circuit (OnsiteChannel.id d N) Ls
    le_rfl (OnsiteChannel.id d N) (finKronecker σ)

/-- **Vanishing connected correlations beyond distance `2T`.** If a density matrix `σ` is
converted in depth `T` from a product density `⊗ᵢ σᵢ`, then for operators `A`, `B` acting on
sets at ring distance larger than `2T`, `tr(σ AB) = tr(σ A) tr(σ B)`.

Source: arXiv:2103.13367, main text, Proposition `propQCA2`, eq. `eq:necessary_condition`,
stated there for pure states prepared from `|0⟩^{⊗M}` by unitary circuits of depth `ℓ`; here
for product densities, local channels, ancillas and discarding, without measurements. -/
theorem trace_mul_mul_eq_of_isLocalChannelConversion {d' T : ℕ}
    {σ₀ : Fin N → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Cfg d' N) (Cfg d' N) ℂ} (h : IsLocalChannelConversion T (finKronecker σ₀) σ)
    {X Y : Set (Fin N)} (hXY : IsSeparatedBy X Y (2 * T)) {A B : Matrix (Cfg d' N) (Cfg d' N) ℂ}
    (hA : A ∈ supportedOperators d' X) (hB : B ∈ supportedOperators d' Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B) := by
  obtain ⟨T', hT', Ψ, hΨ, rfl⟩ := h
  obtain ⟨Ψ', hdual, hcone, hmul⟩ := hΨ.exists_dual
  have hsep : IsSeparatedBy X Y (2 * T') := fun x hx y hy m hm ↦
    hXY x hx y hy m (hm.trans (by exact_mod_cast Nat.mul_le_mul_left 2 hT'))
  have hdisj := disjoint_neighbourhood_of_isSeparatedBy hsep
  have hfac := trace_finKronecker_mul_mul hdisj σ₀ (hcone X A hA) (hcone Y B hB)
  rw [trace_finKronecker, Finset.prod_eq_one fun i _ ↦ hσ₀ i, mul_one] at hfac
  rw [hdual, hdual, hdual, hmul X Y hdisj A hA B hB, hfac]

end Ring

end MPSPreparation
