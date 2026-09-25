/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.KramersWannierPhysical
import TNLean.Algebra.BinaryCharacterSum
import TNLean.Algebra.ComplexSqrt
import TNLean.Algebra.GeneralizeDecide
import TNLean.Algebra.FinCyclicInduction

/-!
# Kramers–Wannier duality: the relations of the source

**Source.** Aasen, Mong, Fendley 2016 (arXiv:1601.07185), subsection "The duality defect",
`References/1601.07185/source/Ising-Defects.tex` lines 989–1056: the duality defect `D_σ` with
matrix elements `⟨h'|D_σ|h⟩ = 2^{-L/2} (-1)^{Σ_j (h_{j-1} + h_j) h'_{j-1/2}}` (lines 996–1000),
the local relations `D_σ σ^z_j σ^z_{j+1} = μ^x_{j+1/2} D_σ` and
`D_σ σ^x_j = μ^z_{j-1/2} μ^z_{j+1/2} D_σ` (lines 1004–1007), and the fusion algebra
`D_ψ² = 1`, `D_σ D_ψ = D_ψ D_σ = D_σ`, `D_σ² = 1 + D_ψ`, `D_σ (D_σ² - 2) = 0`
(lines 1033–1056). Seiberg, Shao 2023 (arXiv:2307.02534), section "Non-invertible lattice
translation of the transverse-field Ising model",
`References/2307.02534/source/Majoranadraft.tex` lines 2442–2444 and 2466–2475: the local
relations `𝖣 Z_j = X_j X_{j+1} 𝖣`, `𝖣 X_j X_{j+1} = Z_{j+1} 𝖣` and the algebra
`𝖣² = ½(1 + η) T`, `𝖣 η = η 𝖣 = 𝖣`, `T^N = 1`, `T 𝖣 = 𝖣 T`, `T η = η T`,
`𝖣^{2N} = ½(1 + η)`, `𝖣† = 𝖣 T⁻¹`, `𝖣 𝖣† = 𝖣† 𝖣 = ½(1 + η)` of the non-invertible
translation of the periodic Ising chain.

**Formalized here.** For the periodic operator `K = kwTensor.mpo N` on a ring of `N ≥ 1`
sites, the claims of Aasen–Mong–Fendley: both local relations, the fusion `Kᵀ K = 2^N (1 + η)`
on the original lattice, `K Kᵀ K = 2^{N+1} K`, and their normalized forms for
`D_σ = 2^{-N/2} K`.

**Project results.** The transpose relation `Kᵀ = K Tᵀ = Tᵀ K` with the one-site translation `T`;
the dual-lattice companion `K Kᵀ = 2^N (1 + η)`, which the source does not print; the actions of `K`
on the paramagnetic and ferromagnetic states (the module
`TNLean.MPS.FundamentalTheorem.Reduction.Examples.KramersWannierAction` identifies these states with
the periodic states of `plusTensor` and `ghz`); and, for the rescaled operator
`𝖣 = 2^{-(N+1)/2} Kᵀ`, the local relations and the algebra that Seiberg–Shao print for
their operator, read in the Hadamard-rotated basis. These are not the Seiberg–Shao theorems:
`𝖣` is not identified with their circuit (lines 2432–2437), and their `T_Ising` is read as
`Tᵀ`, which the conjugation action at line 2108 fixes only up to a scalar.

**Conventions.** The kernel of `K` is `2^{N/2}` times the kernel of `D_σ` under
`h'_{j+1/2} ↦ a j` (output) and `h_j ↦ b j` (input), so that `μ^r_{j+1/2}` acts on output site
`j`. The source composes `D_σ` with its return map to the primal lattice, whose matrix elements
are the same numbers read with the arguments exchanged (lines 1001–1002); here that return map
is the transpose, and `D_σ²` of the source is `D_σᵀ D_σ`. Seiberg–Shao work in a basis where
duality exchanges `Z_j` and `X_j X_{j+1}` and their translation `T_Ising` sends site `j` to
`j + 1`. After the site-uniform Hadamard change of basis their local relations
(`Majoranadraft.tex` lines 2442–2444) are satisfied by the transposed kernel `Kᵀ`, and
`T_Ising` becomes `Tᵀ = T⁻¹` for the translation `T = translate N` of this file, which sends
site `j` to `j - 1`. The operator `𝖣` is therefore built from `Kᵀ`; this file proves its local
relations and algebra and does not identify it with the circuit of Seiberg–Shao.

## Main definitions

* `KWExample.siteX`, `KWExample.siteZ`, `KWExample.siteZZ`: single-site Pauli operators and the
  nearest-neighbour product `Z_j Z_{j+1}` on the periodic spin space.
* `KWExample.translate`: the one-site translation, equal to `shiftTensor.mpo N`.
* `KWExample.kwDefect`: the defect `D_σ = 2^{-N/2} K`.
* `KWExample.kwTranslation`: the rescaled transposed kernel `𝖣 = 2^{-(N+1)/2} Kᵀ`.
* `KWExample.plusState`, `KWExample.ghzState`: the unnormalized paramagnetic and ferromagnetic
  states.

## Main results

* `KWExample.kwTensor_mpo_mul_siteX`, `KWExample.kwTensor_mpo_mul_siteZZ`: the local duality
  relations.
* `KWExample.kwTensor_mpo_transpose`, `KWExample.kwTensor_mpo_transpose_mul`,
  `KWExample.kwTensor_mpo_mul_transpose`, `KWExample.kwTensor_mpo_mul_transpose_mul`: the
  transpose relation and the unnormalized fusion relations.
* `KWExample.kwDefect_transpose_mul`, `KWExample.kwDefect_mul_transpose_mul`: `D_σ² = 1 + D_ψ`
  and `D_σ (D_σ² - 2) = 0`.
* `KWExample.kwTranslation_mul_siteX`, `KWExample.kwTranslation_mul_siteZZ`: the local relations
  of Seiberg–Shao in the Hadamard-rotated basis.
* `KWExample.kwTranslation_mul_self`, `KWExample.kwTranslation_conjTranspose`,
  `KWExample.kwTranslation_mul_conjTranspose`, `KWExample.kwTranslation_pow_two_mul`: the
  algebra of Seiberg–Shao.
* `KWExample.kwTensor_mpo_mulVec_plus`, `KWExample.kwTensor_mpo_mulVec_ghz`: `K P = 2^N G` and
  `K G = 2 P`; `KWExample.kwTensor_mpo_mulVec_single_zero` and
  `KWExample.kwTensor_mpo_mulVec_single_flipConfig_zero`: `K |0…0⟩ = K |1…1⟩ = P`; and
  `KWExample.kwTensor_mpo_normalized_mulVec_plus`, `KWExample.kwTensor_mpo_normalized_mulVec_ghz`:
  the normalized forms for `U = 2^{-(N+1)/2} K`.
* `KWExample.kwTensor_mpo_conjTranspose_eq_inv_translate_mul`,
  `KWExample.kwTensor_mpo_conjTranspose_mul`, `KWExample.kwTensor_mpo_mul_conjTranspose`: the
  adjoint forms `K† = T⁻¹ K` and `K† K = K K† = 2^N (1 + η)`.

## References

- [arXiv:1601.07185](https://arxiv.org/abs/1601.07185) -- D. Aasen, R. S. K. Mong,
  P. Fendley, *Topological defects on the lattice I: The Ising model*
- [arXiv:2307.02534](https://arxiv.org/abs/2307.02534) -- N. Seiberg, S.-H. Shao,
  *Majorana chain and Ising model -- (non-invertible) translations, anomalies, and emanant
  symmetries*
-/

noncomputable section

open scoped Matrix BigOperators Fin.NatCast

namespace KWExample

open MPSTensor
open Complex (invSqrtTwo invSqrtTwo_mul_self invSqrtTwo_pow_mul_self star_invSqrtTwo)

variable {N : ℕ}

/-! ### Binary signs and the character sum -/

/-- The sign `(-1)^{x y}` of two bits. -/
def bitSign (x y : Fin 2) : ℂ := (-1 : ℂ) ^ (x.val * y.val)

theorem bitSign_add_right (x y z : Fin 2) :
    bitSign x (y + z) = bitSign x y * bitSign x z := by
  unfold bitSign
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [show (1 + 1 : Fin 2) = 0 from rfl]

theorem bitSign_comm (x y : Fin 2) : bitSign x y = bitSign y x := by
  unfold bitSign
  rw [mul_comm]

theorem bitSign_add_left (x y z : Fin 2) :
    bitSign (x + y) z = bitSign x z * bitSign y z := by
  rw [bitSign_comm, bitSign_add_right, bitSign_comm z, bitSign_comm z]

@[simp] theorem bitSign_zero_left (y : Fin 2) : bitSign 0 y = 1 := by
  simp [bitSign]

@[simp] theorem bitSign_zero_right (x : Fin 2) : bitSign x 0 = 1 := by
  simp [bitSign]

theorem bitSign_one_left (y : Fin 2) : bitSign 1 y = (-1 : ℂ) ^ y.val := by
  simp [bitSign]

theorem star_bitSign (x y : Fin 2) : star (bitSign x y) = bitSign x y := by
  simp [bitSign]

/-- The character sum over configurations of length `N`, in the notation of `bitSign`. -/
theorem sum_prod_bitSign (g : Fin N → Fin 2) :
    ∑ a : Fin N → Fin 2, ∏ j, bitSign (a j) (g j) = if g = 0 then (2 : ℂ) ^ N else 0 := by
  simpa [bitSign] using Fintype.sum_prod_neg_one_pow_val_mul (R := ℂ) g

/-! ### The two phase forms of the kernel -/

/-- The kernel as a product of bit signs, grouped by output site: the output bit `a j`
couples to the two input bits `b j` and `b (j + 1)`. -/
theorem kwTensor_mpo_eq_prod_bitSign [NeZero N] (a b : Fin N → Fin 2) :
    kwTensor.mpo N a b = ∏ j, bitSign (a j) (b j + b (j + 1)) := by
  rw [kwTensor_mpo_eq_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold bitSign
  generalize a j = x, b j = y, b (j + 1) = z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [show (1 + 1 : Fin 2) = 0 from rfl]

/-- The kernel grouped by input site: the input bit `b j` couples to the two output bits
`a j` and `a (j - 1)`. -/
theorem kwTensor_mpo_eq_prod_bitSign_dual [NeZero N] (a b : Fin N → Fin 2) :
    kwTensor.mpo N a b = ∏ j, bitSign (b j) (a j + a (j - 1)) := by
  rw [kwTensor_mpo_eq_prod_bitSign]
  simp only [bitSign_add_right, Finset.prod_mul_distrib]
  have h : ∏ j, bitSign (a j) (b (j + 1)) = ∏ j, bitSign (a (j - 1)) (b j) :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun j => by simp)
  rw [h]
  congr 1 <;> exact Finset.prod_congr rfl fun j _ => bitSign_comm _ _

/-! ### Configuration identities -/

theorem ne_flipConfig [NeZero N] (x : Fin N → Fin 2) : x ≠ flipConfig x := by
  intro h
  have h0 := congrFun h 0
  revert h0
  simp only [flipConfig]
  generalize_decide x 0

/-- The two indicators `c = x` and `c = flipConfig x` add to the indicator that
`c + x` is constant around the ring. -/
theorem ite_eq_add_ite_eq_flipConfig [NeZero N] (c x : Fin N → Fin 2) :
    ((if c = x then 1 else 0) + (if c = flipConfig x then 1 else 0) : ℂ) =
      if ∀ j, c j + x j = c (j + 1) + x (j + 1) then 1 else 0 := by
  classical
  by_cases h1 : c = x
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (ne_flipConfig c), ite_eq_left]
    · simp
    · intro j
      rw [(Fin.add_eq_zero_iff_eq _ _).mpr rfl, (Fin.add_eq_zero_iff_eq _ _).mpr rfl]
  by_cases h2 : c = flipConfig x
  · subst h2
    rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_left]
    · simp
    · intro j
      simp only [flipConfig]
      generalize_decide x j, x (j + 1)
  · rw [ite_eq_right h1, ite_eq_right h2, add_zero, ite_eq_right]
    intro hcond
    have hconst : ∀ j, c j + x j = c 0 + x 0 := fun j =>
      Fin.cyclic_induction (P := fun j => c j + x j = c 0 + x 0) rfl
        (fun i hi => (hcond i).symm.trans hi) j
    generalize hv : c 0 + x 0 = v at hconst
    fin_cases v
    · exact h1 (funext fun j => (Fin.add_eq_zero_iff_eq _ _).mp (hconst j))
    · exact h2 (funext fun j => (Fin.add_eq_one_iff_eq_rev _ _).mp (hconst j))

theorem one_add_spinFlip_apply (c x : Fin N → Fin 2) :
    (1 + spinFlip N) c x =
      ((if c = x then 1 else 0) + (if c = flipConfig x then 1 else 0) : ℂ) := by
  simp [Matrix.add_apply, Matrix.one_apply, spinFlip]

/-- A character sum whose vanishing condition says that `c + x` is constant evaluates to
`2 ^ N` times the entry of `1 + spinFlip N`. -/
theorem sum_prod_bitSign_eq_one_add_spinFlip [NeZero N] (g c x : Fin N → Fin 2)
    (hg : g = 0 ↔ ∀ j, c j + x j = c (j + 1) + x (j + 1)) :
    ∑ a : Fin N → Fin 2, ∏ j, bitSign (a j) (g j) = (2 : ℂ) ^ N * (1 + spinFlip N) c x := by
  classical
  rw [sum_prod_bitSign, one_add_spinFlip_apply, ite_eq_add_ite_eq_flipConfig]
  by_cases h : g = 0
  · rw [ite_eq_left h, ite_eq_left (hg.mp h), mul_one]
  · rw [ite_eq_right h, ite_eq_right (mt hg.mpr h), mul_zero]

/-! ### Translation and its matrix product operator -/

/-- The one-site translation `(T ψ)(c) = ψ(c ∘ (· - 1))`: its kernel is `1` exactly when the
output configuration is the input shifted by one site, `c j = b (j + 1)`. -/
def translate (N : ℕ) [NeZero N] : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun c b => if c = fun j => b (j + 1) then 1 else 0

theorem eq_shift_iff [NeZero N] (b c : Fin N → Fin 2) :
    (b = fun j => c (j + 1)) ↔ c = fun j => b (j - 1) := by
  constructor <;> rintro rfl <;> funext j <;> simp

theorem mul_translate_apply [NeZero N] (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (c b : Fin N → Fin 2) : (M * translate N) c b = M c fun j => b (j + 1) := by
  simp [Matrix.mul_apply, translate]

theorem translate_mul_apply [NeZero N] (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (c b : Fin N → Fin 2) : (translate N * M) c b = M (fun j => c (j - 1)) b := by
  simp [Matrix.mul_apply, translate, eq_shift_iff]

theorem mul_transpose_translate_apply [NeZero N]
    (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (c b : Fin N → Fin 2) :
    (M * (translate N)ᵀ) c b = M c fun j => b (j - 1) := by
  simp [Matrix.mul_apply, translate, eq_shift_iff]

theorem mul_spinFlip_apply (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (c b : Fin N → Fin 2) : (M * spinFlip N) c b = M c (flipConfig b) := by
  simp [Matrix.mul_apply, spinFlip]

theorem flipConfig_eq_iff (c d : Fin N → Fin 2) : flipConfig c = d ↔ c = flipConfig d := by
  constructor <;> rintro rfl <;> simp

theorem spinFlip_mul_apply (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (c b : Fin N → Fin 2) : (spinFlip N * M) c b = M (flipConfig c) b := by
  simp [Matrix.mul_apply, spinFlip, ← flipConfig_eq_iff]

/-- The local entries of the translation tensor: the letter `(s', s)` is the matrix unit
`E_{s, s'}`. -/
theorem shiftTensor_apply (a b u v : Fin 2) :
    shiftTensor a b u v = if u = b ∧ v = a then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> fin_cases v <;>
    norm_num [shiftTensor, shiftIntTensor, complexOfInt]

/-- Bridge: the periodic operator of the translation tensor `shiftTensor` is `translate N`
at every positive length. -/
theorem shiftTensor_mpo_eq_translate [NeZero N] : shiftTensor.mpo N = translate N := by
  classical
  ext a b
  change Matrix.trace (MPOTensor.evalWord shiftTensor (List.ofFn a) (List.ofFn b)) = _
  rw [← MPOTensor.evalWord_toMPSTensor_pairConfig,
    MPSTensor.trace_evalWord_eq_sum_cyclic]
  have hlocal (j : Fin N) (g : Fin N → Fin 2) :
      shiftTensor.toMPSTensor (finProdFinEquiv (a j, b j)) (g j) (g (j + 1)) =
        if g j = b j ∧ g (j + 1) = a j then 1 else 0 := by
    generalize a j = x, b j = y
    fin_cases x <;> fin_cases y <;> exact shiftTensor_apply _ _ _ _
  simp_rw [hlocal]
  rw [Finset.sum_eq_single b]
  · simp only [true_and, translate]
    by_cases h : a = fun j => b (j + 1)
    · simp [h]
    · rw [ite_eq_right h]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Ne.symm hj])
  · intro g _ hgb
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hgb
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  · simp

theorem translate_mul_transpose [NeZero N] : translate N * (translate N)ᵀ = 1 := by
  ext c b
  rw [mul_transpose_translate_apply, translate, Matrix.one_apply]
  simp

theorem transpose_translate_mul [NeZero N] : (translate N)ᵀ * translate N = 1 := by
  ext c b
  rw [mul_translate_apply, Matrix.transpose_apply, translate, Matrix.one_apply]
  congr 1
  exact propext ⟨fun h => funext fun j => by simpa using (congrFun h (j - 1)).symm,
    fun h => by rw [h]⟩

theorem translate_pow_apply [NeZero N] (k : ℕ) (c b : Fin N → Fin 2) :
    (translate N ^ k) c b = if c = fun j => b (j + (k : Fin N)) then 1 else 0 := by
  induction k generalizing b with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, mul_translate_apply, ih]
    simp only [Nat.cast_succ, add_assoc]

/-- The translation has order `N` on the ring of `N` sites. -/
theorem translate_pow_self [NeZero N] : translate N ^ N = 1 := by
  ext c b
  rw [translate_pow_apply, Matrix.one_apply]
  simp

theorem spinFlip_mul_translate [NeZero N] :
    spinFlip N * translate N = translate N * spinFlip N := by
  ext c b
  rw [spinFlip_mul_apply, mul_spinFlip_apply, translate, translate]
  simp only [flipConfig_eq_iff]
  rfl

/-! ### Local duality relations -/

/-- The bit flip `X_j` at site `j`, sending the basis vector at `b` to the one at
`b + δ_j`. -/
def siteX (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun c b => if c = b + Pi.single j 1 then 1 else 0

/-- The phase `Z_j` at site `j`, diagonal with entry `(-1)^{b_j}`. -/
def siteZ (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.diagonal fun b => (-1 : ℂ) ^ (b j).val

/-- The nearest-neighbour product `Z_j Z_{j+1}`. -/
def siteZZ [NeZero N] (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  siteZ j * siteZ (j + 1)

theorem mul_siteX_apply (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (j : Fin N)
    (c b : Fin N → Fin 2) : (M * siteX j) c b = M c (b + Pi.single j 1) := by
  simp [Matrix.mul_apply, siteX]

theorem siteX_mul_apply (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (j : Fin N)
    (c b : Fin N → Fin 2) : (siteX j * M) c b = M (c + Pi.single j 1) b := by
  simp [Matrix.mul_apply, siteX, Fin.pi_eq_add_iff_eq_add c]

theorem siteZZ_eq_diagonal [NeZero N] (j : Fin N) :
    siteZZ j = Matrix.diagonal fun b => (-1 : ℂ) ^ (b j).val * (-1 : ℂ) ^ (b (j + 1)).val := by
  rw [siteZZ, siteZ, siteZ, Matrix.diagonal_mul_diagonal]

theorem siteX_mul_self (j : Fin N) : siteX j * siteX j = 1 := by
  ext c b
  rw [siteX_mul_apply, siteX, Matrix.one_apply]
  simp

theorem siteZ_mul_self (j : Fin N) : siteZ j * siteZ j = 1 := by
  rw [siteZ, Matrix.diagonal_mul_diagonal]
  simp [neg_one_pow_mul_neg_one_pow_self, Matrix.diagonal_one]

theorem siteX_mul_siteX_comm (j k : Fin N) : siteX j * siteX k = siteX k * siteX j := by
  ext c b
  rw [siteX_mul_apply, siteX_mul_apply, siteX, siteX]
  refine if_congr ?_ rfl rfl
  simp only [funext_iff, Pi.add_apply]
  refine forall_congr' fun i => ?_
  generalize_decide c i, b i, (Pi.single j 1 : Fin N → Fin 2) i,
    (Pi.single k 1 : Fin N → Fin 2) i

theorem siteZ_mul_siteZ_comm (j k : Fin N) : siteZ j * siteZ k = siteZ k * siteZ j := by
  rw [siteZ, siteZ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp only [mul_comm]

/-- The product of bit signs picks up one extra factor when a single input bit is flipped. -/
theorem prod_bitSign_add_single (u y : Fin N → Fin 2) (j : Fin N) :
    ∏ i, bitSign ((u + Pi.single j 1 : Fin N → Fin 2) i) (y i) =
      (∏ i, bitSign (u i) (y i)) * bitSign 1 (y j) := by
  classical
  simp only [Pi.add_apply, bitSign_add_left, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- **Duality maps `X_j` to `Z_{j-1} Z_j`.** In the index convention of this file, where the
output bit `a j` stands for the dual site `j + 1/2`, the source relation
`D_σ σ^x_j = μ^z_{j-1/2} μ^z_{j+1/2} D_σ` reads `K X_j = Z_{j-1} Z_j K`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1004–1006,
second relation. -/
theorem kwTensor_mpo_mul_siteX [NeZero N] (j : Fin N) :
    kwTensor.mpo N * siteX j = siteZZ (j - 1) * kwTensor.mpo N := by
  ext a b
  rw [mul_siteX_apply, siteZZ_eq_diagonal, Matrix.diagonal_mul,
    kwTensor_mpo_eq_prod_bitSign_dual, kwTensor_mpo_eq_prod_bitSign_dual,
    prod_bitSign_add_single, sub_add_cancel, bitSign_add_right, bitSign_one_left,
    bitSign_one_left]
  ring

/-- **Duality maps `Z_j Z_{j+1}` to `X_j`.** With the output bit `a j` standing for the dual
site `j + 1/2`, the source relation `D_σ σ^z_j σ^z_{j+1} = μ^x_{j+1/2} D_σ` reads
`K Z_j Z_{j+1} = X_j K`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1004–1006,
first relation. -/
theorem kwTensor_mpo_mul_siteZZ [NeZero N] (j : Fin N) :
    kwTensor.mpo N * siteZZ j = siteX j * kwTensor.mpo N := by
  ext a b
  rw [siteZZ_eq_diagonal, Matrix.mul_diagonal, siteX_mul_apply,
    kwTensor_mpo_eq_prod_bitSign, kwTensor_mpo_eq_prod_bitSign,
    prod_bitSign_add_single, bitSign_add_right, bitSign_one_left, bitSign_one_left]

/-! ### The fusion algebra of Aasen–Mong–Fendley -/

/-- The global spin flip is an involution, the relation `D_ψ² = 1`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1052–1056. -/
theorem spinFlip_mul_self : spinFlip N * spinFlip N = 1 := by
  ext c b
  simp [spinFlip_mul_apply, spinFlip, Matrix.one_apply, flipConfig_eq_iff]

/-- The inverse translation is the transpose of `translate N`. -/
theorem translate_inv [NeZero N] : (translate N)⁻¹ = (translate N)ᵀ :=
  Matrix.inv_eq_right_inv translate_mul_transpose

/-- The kernel is invariant under a simultaneous translation of input and output. -/
theorem translate_mul_kwTensor_mpo [NeZero N] :
    translate N * kwTensor.mpo N = kwTensor.mpo N * translate N := by
  ext c b
  rw [translate_mul_apply, mul_translate_apply, kwTensor_mpo_eq_prod_bitSign,
    kwTensor_mpo_eq_prod_bitSign]
  exact Fintype.prod_equiv (Equiv.subRight 1) _ _ (fun j => by simp)

/-- Project result: **the transpose of the kernel is the kernel followed by an inverse
translation**, `Kᵀ = K T⁻¹ = T⁻¹ K`, where `T` is the one-site translation `translate N` and
`T⁻¹ = Tᵀ` (`translate_inv`). The source states only that the matrix elements are symmetric,
`⟨h|D_σ|h'⟩ = ⟨h'|D_σ|h⟩` (arXiv:1601.07185,
`References/1601.07185/source/Ising-Defects.tex` lines 1001–1002), so that its return map
from the dual lattice is `Kᵀ`; the comparison with `K` is computed here. -/
theorem kwTensor_mpo_transpose [NeZero N] :
    (kwTensor.mpo N)ᵀ = kwTensor.mpo N * (translate N)ᵀ := by
  ext b a
  rw [Matrix.transpose_apply, mul_transpose_translate_apply, kwTensor_mpo_eq_prod_bitSign_dual,
    kwTensor_mpo_eq_prod_bitSign]
  exact Finset.prod_congr rfl fun j _ => by rw [add_sub_cancel_right, add_comm]

/-- The transpose relation with the translation on the left, `Kᵀ = Tᵀ K`. -/
theorem kwTensor_mpo_transpose_eq_transpose_translate_mul [NeZero N] :
    (kwTensor.mpo N)ᵀ = (translate N)ᵀ * kwTensor.mpo N := by
  rw [kwTensor_mpo_transpose]
  calc kwTensor.mpo N * (translate N)ᵀ
      = (translate N)ᵀ * (translate N * kwTensor.mpo N) * (translate N)ᵀ := by
        rw [← Matrix.mul_assoc, transpose_translate_mul, Matrix.one_mul]
    _ = (translate N)ᵀ * kwTensor.mpo N := by
        rw [translate_mul_kwTensor_mpo, Matrix.mul_assoc, Matrix.mul_assoc,
          translate_mul_transpose, Matrix.mul_one]

/-- The kernel is recovered from its transpose by one translation, `K = Kᵀ T`. -/
theorem kwTensor_mpo_eq_transpose_mul [NeZero N] :
    kwTensor.mpo N = (kwTensor.mpo N)ᵀ * translate N := by
  rw [kwTensor_mpo_transpose, Matrix.mul_assoc, transpose_translate_mul, Matrix.mul_one]

/-- The entries of the kernel are real. -/
theorem star_kwTensor_mpo_apply [NeZero N] (a b : Fin N → Fin 2) :
    star (kwTensor.mpo N a b) = kwTensor.mpo N a b := by
  rw [kwTensor_mpo_eq_prod_bitSign, star_prod]
  exact Finset.prod_congr rfl fun j _ => star_bitSign _ _

/-- **Two duality defects fuse to `1 + D_ψ`**, in the unnormalized form: returning from the
dual lattice with the transposed kernel gives `Kᵀ K = 2^N (1 + η)`. The sum over the dual
variable imposes the constraint `h_j + h'_j + h_{j+1} + h'_{j+1} = 0` of the source.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1033–1039. -/
theorem kwTensor_mpo_transpose_mul [NeZero N] :
    (kwTensor.mpo N)ᵀ * kwTensor.mpo N = (2 : ℂ) ^ N • (1 + spinFlip N) := by
  ext c x
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, kwTensor_mpo_eq_prod_bitSign, ← Finset.prod_mul_distrib,
    ← bitSign_add_right]
  refine sum_prod_bitSign_eq_one_add_spinFlip _ c x ?_
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  simp only [Pi.zero_apply]
  generalize c j = u, c (j + 1) = v, x j = w, x (j + 1) = z
  revert u v w z; decide

/-- Project result: the companion fusion on the dual lattice, `K Kᵀ = 2^N (1 + η)`. The source
says only that `D_σ` also maps the dual lattice back to the original
(arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` line 990) and computes the
fusion on the original lattice alone (lines 1033–1039); this dual-lattice form is not printed. -/
theorem kwTensor_mpo_mul_transpose [NeZero N] :
    kwTensor.mpo N * (kwTensor.mpo N)ᵀ = (2 : ℂ) ^ N • (1 + spinFlip N) := by
  ext c x
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, kwTensor_mpo_eq_prod_bitSign_dual, ← Finset.prod_mul_distrib,
    ← bitSign_add_right]
  refine sum_prod_bitSign_eq_one_add_spinFlip _ c x ?_
  rw [funext_iff]
  refine Iff.trans ?_ (Fin.forall_sub_one_iff (P := fun i k => c k + x k = c i + x i))
  refine forall_congr' fun j => ?_
  simp only [Pi.zero_apply]
  generalize c j = u, c (j - 1) = v, x j = w, x (j - 1) = z
  revert u v w z; decide

/-- The kernel is real, so its adjoint is its transpose, `K† = Kᵀ`. -/
theorem kwTensor_mpo_conjTranspose [NeZero N] :
    (kwTensor.mpo N)ᴴ = (kwTensor.mpo N)ᵀ := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_kwTensor_mpo_apply]

/-- Project result: the adjoint of the kernel is the kernel followed by the inverse translation,
`K† = T⁻¹ K`. -/
theorem kwTensor_mpo_conjTranspose_eq_inv_translate_mul [NeZero N] :
    (kwTensor.mpo N)ᴴ = (translate N)⁻¹ * kwTensor.mpo N := by
  rw [kwTensor_mpo_conjTranspose, translate_inv, kwTensor_mpo_transpose_eq_transpose_translate_mul]

/-- The Gram matrix `K† K = 2^N (1 + η)`, the adjoint form of `kwTensor_mpo_transpose_mul`. -/
theorem kwTensor_mpo_conjTranspose_mul [NeZero N] :
    (kwTensor.mpo N)ᴴ * kwTensor.mpo N = (2 : ℂ) ^ N • (1 + spinFlip N) := by
  rw [kwTensor_mpo_conjTranspose, kwTensor_mpo_transpose_mul]

/-- The Gram matrix `K K† = 2^N (1 + η)`, the adjoint form of `kwTensor_mpo_mul_transpose`. -/
theorem kwTensor_mpo_mul_conjTranspose [NeZero N] :
    kwTensor.mpo N * (kwTensor.mpo N)ᴴ = (2 : ℂ) ^ N • (1 + spinFlip N) := by
  rw [kwTensor_mpo_conjTranspose, kwTensor_mpo_mul_transpose]

/-- **`D_σ (D_σ² − 2) = 0`**, in the unnormalized form `K Kᵀ K = 2^{N+1} K`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` line 1048. -/
theorem kwTensor_mpo_mul_transpose_mul [NeZero N] :
    kwTensor.mpo N * (kwTensor.mpo N)ᵀ * kwTensor.mpo N = (2 : ℂ) ^ (N + 1) • kwTensor.mpo N := by
  rw [Matrix.mul_assoc, kwTensor_mpo_transpose_mul, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_one, kwTensor_mpo_mul_spinFlip, pow_succ, mul_smul, two_smul]

/-- Project result: the square of the kernel on a single lattice, `K² = 2^N (1 + η) T`,
obtained from `K = Kᵀ T` and `K Kᵀ = 2^N (1 + η)`. Here `T = translate N` moves every site
backward by one; the forward translation appears in the square of `Kᵀ`
(`kwTranslation_mul_self`). -/
theorem kwTensor_mpo_mul_self [NeZero N] :
    kwTensor.mpo N * kwTensor.mpo N = (2 : ℂ) ^ N • ((1 + spinFlip N) * translate N) := by
  calc kwTensor.mpo N * kwTensor.mpo N
      = kwTensor.mpo N * ((kwTensor.mpo N)ᵀ * translate N) := by
        rw [← kwTensor_mpo_eq_transpose_mul]
    _ = _ := by rw [← Matrix.mul_assoc, kwTensor_mpo_mul_transpose, Matrix.smul_mul]

/-! ### The normalized defect operators -/

/-- The duality defect `D_σ = 2^{-N/2} K` in the normalization of the source.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 996–999. -/
def kwDefect (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  invSqrtTwo ^ N • kwTensor.mpo N

/-- **`D_σ² = 1 + D_ψ`**: the defect followed by its return to the primal lattice.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1033–1039
and lines 1052–1056. -/
theorem kwDefect_transpose_mul [NeZero N] :
    (kwDefect N)ᵀ * kwDefect N = 1 + spinFlip N := by
  rw [kwDefect, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    kwTensor_mpo_transpose_mul, smul_smul, smul_smul, invSqrtTwo_pow_mul_self, one_smul]

/-- Project result: the companion relation on the dual lattice, `D_σ D_σᵀ = 1 + D_ψ`, the
normalized form of `kwTensor_mpo_mul_transpose`. The source computes the fusion on the original
lattice only (arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex`
lines 1033–1039). -/
theorem kwDefect_mul_transpose [NeZero N] :
    kwDefect N * (kwDefect N)ᵀ = 1 + spinFlip N := by
  rw [kwDefect, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    kwTensor_mpo_mul_transpose, smul_smul, smul_smul, invSqrtTwo_pow_mul_self, one_smul]

/-- **`D_σ D_ψ = D_ψ D_σ = D_σ`**.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1043–1047. -/
theorem kwDefect_mul_spinFlip [NeZero N] : kwDefect N * spinFlip N = kwDefect N := by
  rw [kwDefect, Matrix.smul_mul, kwTensor_mpo_mul_spinFlip]

/-- Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines
1043–1047 and lines 1052–1056. -/
theorem spinFlip_mul_kwDefect [NeZero N] : spinFlip N * kwDefect N = kwDefect N := by
  rw [kwDefect, Matrix.mul_smul, spinFlip_mul_kwTensor_mpo]

/-- **`D_σ (D_σ² − 2) = 0`**, read as `D_σ D_σᵀ D_σ = 2 D_σ`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` line 1048. -/
theorem kwDefect_mul_transpose_mul [NeZero N] :
    kwDefect N * (kwDefect N)ᵀ * kwDefect N = (2 : ℂ) • kwDefect N := by
  rw [kwDefect_mul_transpose, Matrix.add_mul, Matrix.one_mul, spinFlip_mul_kwDefect, two_smul]

/-! ### The non-invertible translation of Seiberg–Shao

Seiberg–Shao write the transverse-field Ising chain with the duality exchanging `Z_j` and
`X_j X_{j+1}`. After the site-uniform Hadamard change of basis, which exchanges `X` and `Z`
on every site, their relations `𝖣 Z_j = X_j X_{j+1} 𝖣` and `𝖣 X_j X_{j+1} = Z_{j+1} 𝖣` read
`𝖣 X_j = Z_j Z_{j+1} 𝖣` and `𝖣 Z_j Z_{j+1} = X_{j+1} 𝖣`, their `η = ∏ Z_j` becomes the global
spin flip `spinFlip N`, and their translation `T_Ising`, which sends `X_j` to `X_{j+1}`,
becomes `Tᵀ = T⁻¹` for the translation `T = translate N` of this file. The transposed kernel
`Kᵀ` satisfies these relations, while `K` itself sends `X_j` to `Z_{j-1} Z_j` and so matches
them only after the reflection `j ↦ -j` of the chain. The operator of this section is
therefore built from `Kᵀ`.

Every relation of this section is a project result: it shows that `𝖣` satisfies a relation that
Seiberg–Shao print for their operator. `𝖣` is not identified with their circuit, and their
`T_Ising` is read as `Tᵀ`. -/

theorem transpose_translate_mul_apply [NeZero N]
    (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (c b : Fin N → Fin 2) :
    ((translate N)ᵀ * M) c b = M (fun j => c (j + 1)) b := by
  simp [Matrix.mul_apply, translate]

/-- The transposed translation moves a bit flip one site forward, `Tᵀ X_j = X_{j+1} Tᵀ`:
under conjugation it acts as the translation `T_Ising` of Seiberg–Shao,
`References/2307.02534/source/Majoranadraft.tex` line 2108. -/
theorem transpose_translate_mul_siteX [NeZero N] (j : Fin N) :
    (translate N)ᵀ * siteX j = siteX (j + 1) * (translate N)ᵀ := by
  ext c b
  rw [transpose_translate_mul_apply, mul_transpose_translate_apply, siteX, siteX]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · funext i
    have hi := congrFun h (i - 1)
    simp only [Pi.add_apply, sub_add_cancel] at hi ⊢
    rw [hi]
    congr 1
    simp [Pi.single_apply, sub_eq_iff_eq_add]
  · subst h
    funext i
    simp only [Pi.add_apply, add_sub_cancel_right]
    congr 1
    simp [Pi.single_apply]

theorem transpose_translate_inv [NeZero N] : ((translate N)ᵀ)⁻¹ = translate N :=
  Matrix.inv_eq_right_inv transpose_translate_mul

theorem spinFlip_transpose : (spinFlip N)ᵀ = spinFlip N := by
  ext c b
  simp only [Matrix.transpose_apply, spinFlip]
  exact if_congr ((flipConfig_eq_iff b c).symm.trans eq_comm) rfl rfl

theorem spinFlip_mul_transpose_translate [NeZero N] :
    spinFlip N * (translate N)ᵀ = (translate N)ᵀ * spinFlip N := by
  rw [← spinFlip_transpose, ← Matrix.transpose_mul, ← spinFlip_mul_translate,
    Matrix.transpose_mul]

theorem transpose_translate_pow_self [NeZero N] : (translate N)ᵀ ^ N = 1 := by
  rw [← Matrix.transpose_pow, translate_pow_self, Matrix.transpose_one]

theorem siteX_transpose (j : Fin N) : (siteX j)ᵀ = siteX j := by
  ext c b
  simp only [Matrix.transpose_apply, siteX]
  exact if_congr (Fin.pi_eq_add_iff_eq_add _ _ _) rfl rfl

theorem siteZZ_transpose [NeZero N] (j : Fin N) : (siteZZ j)ᵀ = siteZZ j := by
  rw [siteZZ_eq_diagonal, Matrix.diagonal_transpose]

/-- The rescaled transposed kernel `𝖣 = 2^{-(N+1)/2} Kᵀ`, the non-invertible translation of
Seiberg–Shao in the Hadamard-rotated basis described above. Its local relations are
`kwTranslation_mul_siteX` and `kwTranslation_mul_siteZZ`. Seiberg–Shao define their operator
by a circuit, `References/2307.02534/source/Majoranadraft.tex` lines 2432–2437; that the
circuit coincides with this matrix after the change of basis is not proved here. -/
def kwTranslation (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  invSqrtTwo ^ (N + 1) • (kwTensor.mpo N)ᵀ

theorem invSqrtTwo_pow_succ_mul_self (n : ℕ) :
    invSqrtTwo ^ (n + 1) * invSqrtTwo ^ (n + 1) * (2 : ℂ) ^ n = (2 : ℂ)⁻¹ := by
  calc invSqrtTwo ^ (n + 1) * invSqrtTwo ^ (n + 1) * (2 : ℂ) ^ n
      = (invSqrtTwo ^ n * invSqrtTwo ^ n * 2 ^ n) * (invSqrtTwo * invSqrtTwo) := by ring
    _ = (2 : ℂ)⁻¹ := by rw [invSqrtTwo_pow_mul_self, invSqrtTwo_mul_self, one_mul]

/-- Project result: **`𝖣` maps `X_j` to `Z_j Z_{j+1}`**, the first relation of
arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2442–2444,
`𝖣 Z_j = X_j X_{j+1} 𝖣`, read in the Hadamard-rotated basis. -/
theorem kwTranslation_mul_siteX [NeZero N] (j : Fin N) :
    kwTranslation N * siteX j = siteZZ j * kwTranslation N := by
  have h := congrArg Matrix.transpose (kwTensor_mpo_mul_siteZZ (N := N) j)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, siteZZ_transpose, siteX_transpose] at h
  rw [kwTranslation, Matrix.smul_mul, Matrix.mul_smul, h]

/-- Project result: **`𝖣` maps `Z_j Z_{j+1}` to `X_{j+1}`**, the second relation of
arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2442–2444,
`𝖣 X_j X_{j+1} = Z_{j+1} 𝖣`, read in the Hadamard-rotated basis. -/
theorem kwTranslation_mul_siteZZ [NeZero N] (j : Fin N) :
    kwTranslation N * siteZZ j = siteX (j + 1) * kwTranslation N := by
  have h := congrArg Matrix.transpose (kwTensor_mpo_mul_siteX (N := N) (j + 1))
  rw [Matrix.transpose_mul, Matrix.transpose_mul, siteZZ_transpose, siteX_transpose,
    add_sub_cancel_right] at h
  rw [kwTranslation, Matrix.smul_mul, Matrix.mul_smul, ← h]

/-- Project result: **`𝖣² = ½(1 + η) Tᵀ`**, the relation `𝖣² = ½(1 + η) T_Ising` of
arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2469–2473, with `T_Ising`
read as the transposed translation `(translate N)ᵀ`, which moves every site forward by one
(`transpose_translate_mul_siteX`). -/
theorem kwTranslation_mul_self [NeZero N] :
    kwTranslation N * kwTranslation N =
      (2 : ℂ)⁻¹ • ((1 + spinFlip N) * (translate N)ᵀ) := by
  have hsq : (kwTensor.mpo N)ᵀ * (kwTensor.mpo N)ᵀ =
      (2 : ℂ) ^ N • ((1 + spinFlip N) * (translate N)ᵀ) := by
    calc (kwTensor.mpo N)ᵀ * (kwTensor.mpo N)ᵀ
        = (kwTensor.mpo N)ᵀ * (kwTensor.mpo N * (translate N)ᵀ) := by
          rw [← kwTensor_mpo_transpose]
      _ = _ := by rw [← Matrix.mul_assoc, kwTensor_mpo_transpose_mul, Matrix.smul_mul]
  rw [kwTranslation, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul,
    invSqrtTwo_pow_succ_mul_self]

/-- Project result: **`𝖣 η = η 𝖣 = 𝖣`**, the relation of arXiv:2307.02534,
`References/2307.02534/source/Majoranadraft.tex` lines 2469–2473, second line. -/
theorem kwTranslation_mul_spinFlip [NeZero N] :
    kwTranslation N * spinFlip N = kwTranslation N := by
  rw [kwTranslation, Matrix.smul_mul, kwTensor_mpo_transpose_eq_transpose_translate_mul,
    Matrix.mul_assoc, kwTensor_mpo_mul_spinFlip]

/-- Project result: `η 𝖣 = 𝖣`, the companion of `kwTranslation_mul_spinFlip`
(arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2469–2473, second line).
-/
theorem spinFlip_mul_kwTranslation [NeZero N] :
    spinFlip N * kwTranslation N = kwTranslation N := by
  rw [kwTranslation, Matrix.mul_smul, kwTensor_mpo_transpose, ← Matrix.mul_assoc,
    spinFlip_mul_kwTensor_mpo]

/-- Project result: **`Tᵀ 𝖣 = 𝖣 Tᵀ`**, the relation `T_Ising 𝖣 = 𝖣 T_Ising` of
arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2469–2473, third line, with
`T_Ising` read as `(translate N)ᵀ`. The companions `T_Ising^N = 1` and `T_Ising η = η T_Ising` are
`transpose_translate_pow_self` and `spinFlip_mul_transpose_translate`. -/
theorem transpose_translate_mul_kwTranslation [NeZero N] :
    (translate N)ᵀ * kwTranslation N = kwTranslation N * (translate N)ᵀ := by
  rw [kwTranslation, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_mul,
    ← Matrix.transpose_mul, translate_mul_kwTensor_mpo]

/-- The transposed kernel is real, so its adjoint is the kernel itself. -/
theorem kwTensor_mpo_transpose_conjTranspose [NeZero N] :
    ((kwTensor.mpo N)ᵀ)ᴴ = kwTensor.mpo N := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_kwTensor_mpo_apply]

/-- Project result: **`𝖣† = 𝖣 (Tᵀ)⁻¹`**, the relation `𝖣† = 𝖣 T_Ising⁻¹` of
arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2475, with `T_Ising` read as
`(translate N)ᵀ`. -/
theorem kwTranslation_conjTranspose [NeZero N] :
    (kwTranslation N)ᴴ = kwTranslation N * ((translate N)ᵀ)⁻¹ := by
  rw [kwTranslation, Matrix.conjTranspose_smul, star_pow, star_invSqrtTwo,
    kwTensor_mpo_transpose_conjTranspose, transpose_translate_inv, Matrix.smul_mul,
    ← kwTensor_mpo_eq_transpose_mul]

/-- Project result: **`𝖣 𝖣† = ½(1 + η)`**, the relation of arXiv:2307.02534,
`References/2307.02534/source/Majoranadraft.tex` line 2475. -/
theorem kwTranslation_mul_conjTranspose [NeZero N] :
    kwTranslation N * (kwTranslation N)ᴴ = (2 : ℂ)⁻¹ • (1 + spinFlip N) := by
  rw [kwTranslation, Matrix.conjTranspose_smul, star_pow, star_invSqrtTwo,
    kwTensor_mpo_transpose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    kwTensor_mpo_transpose_mul, smul_smul, smul_smul, invSqrtTwo_pow_succ_mul_self]

/-- Project result: **`𝖣† 𝖣 = ½(1 + η)`**, the relation of arXiv:2307.02534,
`References/2307.02534/source/Majoranadraft.tex` line 2475. -/
theorem kwTranslation_conjTranspose_mul [NeZero N] :
    (kwTranslation N)ᴴ * kwTranslation N = (2 : ℂ)⁻¹ • (1 + spinFlip N) := by
  rw [kwTranslation, Matrix.conjTranspose_smul, star_pow, star_invSqrtTwo,
    kwTensor_mpo_transpose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    kwTensor_mpo_mul_transpose, smul_smul, smul_smul, invSqrtTwo_pow_succ_mul_self]

theorem half_one_add_spinFlip_isIdempotentElem :
    IsIdempotentElem ((2 : ℂ)⁻¹ • (1 + spinFlip N)) := by
  rw [IsIdempotentElem, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, spinFlip_mul_self]
  rw [show 1 + spinFlip N + (spinFlip N + 1) = (2 : ℂ) • (1 + spinFlip N) by
    rw [two_smul]; abel, smul_smul]
  norm_num

/-- Project result: **`𝖣^{2N} = ½(1 + η)`**, the consequence stated in arXiv:2307.02534,
`References/2307.02534/source/Majoranadraft.tex` line 2474. -/
theorem kwTranslation_pow_two_mul [NeZero N] :
    kwTranslation N ^ (2 * N) = (2 : ℂ)⁻¹ • (1 + spinFlip N) := by
  have hcomm : Commute ((2 : ℂ)⁻¹ • (1 + spinFlip N)) (translate N)ᵀ := by
    refine Commute.smul_left ?_ _
    exact (Commute.one_left _).add_left spinFlip_mul_transpose_translate
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [pow_mul, sq, kwTranslation_mul_self, ← Matrix.smul_mul, hcomm.mul_pow,
    transpose_translate_pow_self, Matrix.mul_one, hn,
    half_one_add_spinFlip_isIdempotentElem.pow_succ_eq]

/-! ### Action on the paramagnetic and ferromagnetic states -/

/-- The unnormalized paramagnetic state `∑_s |s⟩ = (|0⟩ + |1⟩)^{⊗ N}`. -/
def plusState (N : ℕ) : (Fin N → Fin 2) → ℂ := fun _ => 1

/-- The unnormalized ferromagnetic state `|0…0⟩ + |1…1⟩`. -/
def ghzState (N : ℕ) : (Fin N → Fin 2) → ℂ :=
  fun c => (if c = 0 then 1 else 0) + (if c = flipConfig 0 then 1 else 0)

/-- Project result: **duality maps the paramagnet to the ferromagnet**, `K P = 2^N G`. This
illustrates the exchange of the disordered and the ordered phase described in words in
arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` line 1026; the source
prints no state action. -/
theorem kwTensor_mpo_mulVec_plus [NeZero N] :
    kwTensor.mpo N *ᵥ plusState N = (2 : ℂ) ^ N • ghzState N := by
  ext a
  simp only [Matrix.mulVec, dotProduct, plusState, mul_one, Pi.smul_apply, smul_eq_mul]
  simp_rw [kwTensor_mpo_eq_prod_bitSign_dual]
  rw [sum_prod_bitSign_eq_one_add_spinFlip _ a 0, one_add_spinFlip_apply]
  · rfl
  rw [funext_iff]
  refine Iff.trans ?_ (Fin.forall_sub_one_iff
    (P := fun i k => a k + (0 : Fin N → Fin 2) k = a i + (0 : Fin N → Fin 2) i))
  refine forall_congr' fun j => ?_
  simp only [Pi.zero_apply, add_zero]
  generalize a j = u, a (j - 1) = v
  revert u v; decide

/-- Project result: **duality maps the ferromagnet to twice the paramagnet**, `K G = 2 P`,
the companion of `kwTensor_mpo_mulVec_plus`. -/
theorem kwTensor_mpo_mulVec_ghz [NeZero N] :
    kwTensor.mpo N *ᵥ ghzState N = (2 : ℂ) • plusState N := by
  ext a
  simp only [Matrix.mulVec, dotProduct, ghzState, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, kwTensor_mpo_flip_input,
    Pi.smul_apply, plusState, smul_eq_mul]
  simp only [kwTensor_mpo_eq_prod_bitSign, Pi.zero_apply, add_zero, bitSign_zero_right,
    Finset.prod_const_one]
  norm_num

/-- Project result: the all-zero configuration is mapped to the unnormalized paramagnetic
state, `K |0…0⟩ = P`. -/
theorem kwTensor_mpo_mulVec_single_zero [NeZero N] :
    kwTensor.mpo N *ᵥ Pi.single (0 : Fin N → Fin 2) 1 = plusState N := by
  ext a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, kwTensor_mpo_eq_prod_bitSign]
  simp [bitSign, plusState]

/-- Project result: the all-one configuration is mapped to the unnormalized paramagnetic
state, `K |1…1⟩ = P`. -/
theorem kwTensor_mpo_mulVec_single_flipConfig_zero [NeZero N] :
    kwTensor.mpo N *ᵥ Pi.single (flipConfig (0 : Fin N → Fin 2)) 1 = plusState N := by
  ext a
  rw [← congrFun (kwTensor_mpo_mulVec_single_zero (N := N)) a, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply, kwTensor_mpo_flip_input]

/-- Project result: with `U = 2^{-(N+1)/2} K`, the normalized paramagnetic state
`2^{-N/2} P` is mapped to the normalized ferromagnetic state `2^{-1/2} G`. -/
theorem kwTensor_mpo_normalized_mulVec_plus [NeZero N] :
    (invSqrtTwo ^ (N + 1) • kwTensor.mpo N) *ᵥ (invSqrtTwo ^ N • plusState N) =
      invSqrtTwo • ghzState N := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, kwTensor_mpo_mulVec_plus, smul_smul,
    smul_smul]
  congr 1
  linear_combination invSqrtTwo * invSqrtTwo_pow_mul_self N

/-- Project result: with `U = 2^{-(N+1)/2} K`, the normalized ferromagnetic state
`2^{-1/2} G` is mapped to the normalized paramagnetic state `2^{-N/2} P`. -/
theorem kwTensor_mpo_normalized_mulVec_ghz [NeZero N] :
    (invSqrtTwo ^ (N + 1) • kwTensor.mpo N) *ᵥ (invSqrtTwo • ghzState N) =
      invSqrtTwo ^ N • plusState N := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, kwTensor_mpo_mulVec_ghz, smul_smul,
    smul_smul]
  congr 1
  linear_combination (2 * invSqrtTwo ^ N) * invSqrtTwo_mul_self

end KWExample
