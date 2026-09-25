/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.KramersWannierSource

/-!
# Kramers–Wannier duality: the circuit of Seiberg–Shao

**Source.** Seiberg, Shao 2023 (arXiv:2307.02534), section "Non-invertible lattice translation of
the transverse-field Ising model", `References/2307.02534/source/Majoranadraft.tex`
lines 2431–2437: the non-invertible translation
`𝖣 = e^{-2π i N/8} (d^z_1 d^x_1) ⋯ (d^z_{N-1} d^x_{N-1}) d^z_N (1 + η)/2` with
`d^z_j = (1 + i Z_j)/√2`, `d^x_j = (1 + i X_j X_{j+1})/√2` and `η = ∏_j Z_j`, on a ring of
`N` sites; lines 2442–2444: its local relations `𝖣 Z_j = X_j X_{j+1} 𝖣` and
`𝖣 X_j X_{j+1} = Z_{j+1} 𝖣`; lines 2466–2475: its algebra with `η` and `T_Ising`.

**Formalized here.** The circuit `𝖣` exactly as printed, and the identity
`H 𝖣 H = 2^{-(N+1)/2} Kᵀ`, where `H` is the Hadamard gate on every site and `K = kwTensor.mpo N`
is the raw periodic duality operator: after the Hadamard change of basis the circuit is the
operator `kwTranslation N` of `TNLean.MPS.Examples.KramersWannierSource`, with scalar exactly
one. Consequently the printed local relations of the circuit hold for all `j`, including the
bond `X_N X_1` that the circuit does not contain, together with `𝖣 η = η 𝖣 = 𝖣`,
`𝖣 𝖣† = 𝖣† 𝖣 = ½(1 + η)`, and `𝖣² = ½(1 + η) T_Ising`, where `T_Ising` is the transposed
translation `Tᵀ`: it sends `|m_1, …, m_N⟩` to `|m_N, m_1, …, m_{N-1}⟩`, the action of the product
of swap gates by which the source defines it (lines 2115–2123), and it commutes with `H`.

**Conventions.** Sites `1, …, N` of the source are sites `0, …, N - 1` here. The circuit
is a product of matrices with the leftmost factor applied last.

## Main definitions

* `KWExample.hadamard`: the Hadamard gate `H^{⊗N}` on every site.
* `KWExample.ssGateZ`, `KWExample.ssGateXX`, `KWExample.ssEta`: the local factors `d^z_j`,
  `d^x_j` and the symmetry `η = ∏_j Z_j` of the source.
* `KWExample.ssCircuit`: the circuit `𝖣` on `n + 1` sites.

## Main results

* `KWExample.hadamard_mul_ssCircuit_mul_hadamard`: `H 𝖣 H = kwTranslation (n + 1)`.
* `KWExample.ssCircuit_mul_siteZ`, `KWExample.ssCircuit_mul_siteXX`: the local relations of the
  source for the circuit.
* `KWExample.ssCircuit_mul_ssEta`, `KWExample.ssEta_mul_ssCircuit`,
  `KWExample.ssCircuit_mul_conjTranspose`, `KWExample.ssCircuit_conjTranspose_mul`,
  `KWExample.ssCircuit_mul_self`: the algebra of the source for the circuit.
* `KWExample.ssCircuit_mulVec_eq_zero_iff`, `KWExample.exists_ssCircuit_mulVec_eq_iff`: the
  kernel of the circuit is the sector `η = -1` and its range the sector `η = +1`.
* `KWExample.transpose_translate_apply`, `KWExample.hadamard_mul_transpose_translate`: the
  translation `T_Ising = Tᵀ` and its commutation with the Hadamard gate.

## References

- [arXiv:2307.02534](https://arxiv.org/abs/2307.02534) -- N. Seiberg, S.-H. Shao,
  *Majorana chain and Ising model -- (non-invertible) translations, anomalies, and emanant
  symmetries*
-/

noncomputable section

open scoped Matrix BigOperators Fin.NatCast

namespace KWExample

open Complex (I invSqrtTwo invSqrtTwo_mul_self invSqrtTwo_pow_mul_self star_invSqrtTwo)

variable {N : ℕ}

/-! ### The Hadamard change of basis -/

/-- The Hadamard gate on every site, `⟨c|H^{⊗N}|b⟩ = 2^{-N/2} (-1)^{c · b}`. -/
def hadamard (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun c b => invSqrtTwo ^ N * ∏ j, bitSign (c j) (b j)

/-- Conjugating a diagonal sign operator by the Hadamard gate: the result is the permutation
`b ↦ b + g`. -/
theorem hadamard_mul_diagonal_mul_hadamard_apply (g c b : Fin N → Fin 2) :
    (hadamard N * Matrix.diagonal (fun x : Fin N → Fin 2 => ∏ j, bitSign (x j) (g j)) *
        hadamard N) c b =
      if c + g + b = 0 then 1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, hadamard]
  have h (x : Fin N → Fin 2) :
      invSqrtTwo ^ N * (∏ j, bitSign (c j) (x j)) * (∏ j, bitSign (x j) (g j)) *
          (invSqrtTwo ^ N * ∏ j, bitSign (x j) (b j)) =
        invSqrtTwo ^ N * invSqrtTwo ^ N * ∏ j, bitSign (x j) ((c + g + b) j) := by
    simp only [Pi.add_apply, bitSign_add_right, Finset.prod_mul_distrib, bitSign_comm (c _)]
    ring
  simp_rw [h, ← Finset.mul_sum, sum_prod_bitSign]
  split_ifs
  · exact invSqrtTwo_pow_mul_self N
  · exact mul_zero _

/-- The diagonal sign operator with exponent vector `g`, `∏_j (-1)^{x_j g_j}`. -/
theorem prod_bitSign_single (x : Fin N → Fin 2) (j : Fin N) :
    ∏ k, bitSign (x k) ((Pi.single j 1 : Fin N → Fin 2) k) = (-1 : ℂ) ^ (x j).val := by
  classical
  rw [Finset.prod_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  rw [Pi.single_eq_same, bitSign_comm, bitSign_one_left]

theorem siteZ_eq_diagonal_prod_bitSign (j : Fin N) :
    siteZ j = Matrix.diagonal fun x => ∏ k, bitSign (x k) ((Pi.single j 1 : Fin N → Fin 2) k) := by
  simp_rw [prod_bitSign_single]
  rfl

theorem hadamard_mul_self : hadamard N * hadamard N = 1 := by
  ext c b
  have h := hadamard_mul_diagonal_mul_hadamard_apply (N := N) 0 c b
  simp only [Pi.zero_apply, bitSign_zero_right, Finset.prod_const_one, Matrix.diagonal_one,
    Matrix.mul_one, add_zero] at h
  rw [h, Matrix.one_apply]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · funext j
    exact (Fin.add_eq_zero_iff_eq _ _).mp (congrFun h j)
  · subst h
    funext j
    exact (Fin.add_eq_zero_iff_eq _ _).mpr rfl

/-- The Hadamard gate exchanges `Z_j` and `X_j`: `H Z_j H = X_j`. -/
theorem hadamard_mul_siteZ_mul_hadamard (j : Fin N) :
    hadamard N * siteZ j * hadamard N = siteX j := by
  ext c b
  rw [siteZ_eq_diagonal_prod_bitSign, hadamard_mul_diagonal_mul_hadamard_apply, siteX]
  refine if_congr ?_ rfl rfl
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply]
  refine forall_congr' fun k => ?_
  generalize_decide c k, b k, (Pi.single j 1 : Fin N → Fin 2) k

/-- Conjugation by the Hadamard gate is multiplicative. -/
theorem hadamard_mul_mul_mul_hadamard (A B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    hadamard N * (A * B) * hadamard N =
      (hadamard N * A * hadamard N) * (hadamard N * B * hadamard N) := by
  calc hadamard N * (A * B) * hadamard N
      = hadamard N * A * (hadamard N * hadamard N) * B * hadamard N := by
        rw [hadamard_mul_self, Matrix.mul_one, Matrix.mul_assoc (hadamard N) A B]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The Hadamard gate exchanges `X_j` and `Z_j`: `H X_j H = Z_j`. -/
theorem hadamard_mul_siteX_mul_hadamard (j : Fin N) :
    hadamard N * siteX j * hadamard N = siteZ j := by
  rw [← hadamard_mul_siteZ_mul_hadamard, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hadamard_mul_self, Matrix.one_mul, Matrix.mul_assoc, hadamard_mul_self, Matrix.mul_one]

theorem hadamard_mul_one_add_smul_mul_hadamard (c : ℂ)
    (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    hadamard N * (1 + c • A) * hadamard N = 1 + c • (hadamard N * A * hadamard N) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hadamard_mul_self, Matrix.mul_smul,
    Matrix.smul_mul]

/-- Conjugation by the Hadamard gate distributes over a list product. -/
theorem hadamard_mul_list_prod_mul_hadamard
    (l : List (Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)) :
    hadamard N * l.prod * hadamard N = (l.map fun A => hadamard N * A * hadamard N).prod := by
  induction l with
  | nil => simp [hadamard_mul_self]
  | cons A l ih => rw [List.prod_cons, hadamard_mul_mul_mul_hadamard, ih, List.map_cons,
      List.prod_cons]

/-! ### The circuit as printed -/

/-- The local factor `d^z_j = (1 + i Z_j)/√2 = e^{iπ Z_j/4}`.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2434. -/
def ssGateZ (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  invSqrtTwo • (1 + I • siteZ j)

/-- The local factor `d^x_j = (1 + i X_j X_{j+1})/√2 = e^{iπ X_j X_{j+1}/4}`.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2435. -/
def ssGateXX [NeZero N] (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  invSqrtTwo • (1 + I • (siteX j * siteX (j + 1)))

/-- The `ℤ₂` symmetry `η = ∏_j Z_j` of the source, as an ordered product.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2435. -/
def ssEta (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  (List.ofFn fun j : Fin N => siteZ j).prod

/-- The non-invertible translation of Seiberg–Shao on `N = n + 1` sites,
`𝖣 = e^{-2π i N/8} (d^z_1 d^x_1) ⋯ (d^z_{N-1} d^x_{N-1}) d^z_N (1 + η)/2`, with the source's
sites `1, …, N` relabelled `0, …, n`. The factors `d^x_j` run over the open chain `j < n`; the
bond between the last and the first site does not occur.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2431–2437. -/
def ssCircuit (n : ℕ) : Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) ℂ :=
  Complex.exp (-(2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) / 8)) •
    ((List.ofFn fun k : Fin n => ssGateZ k.castSucc * ssGateXX k.castSucc).prod *
      ssGateZ (Fin.last n) * ((2 : ℂ)⁻¹ • (1 + ssEta (n + 1))))

/-! ### The circuit in the Hadamard frame -/

/-- The Hadamard image of `d^z_j`, the gate `(1 + i X_j)/√2`. -/
def hGateX (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  invSqrtTwo • (1 + I • siteX j)

/-- The Hadamard image of `d^x_j`, the diagonal gate `(1 + i Z_j Z_{j+1})/√2`. -/
def hGateZZ [NeZero N] (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  invSqrtTwo • (1 + I • siteZZ j)

theorem hadamard_mul_ssGateZ_mul_hadamard (j : Fin N) :
    hadamard N * ssGateZ j * hadamard N = hGateX j := by
  rw [ssGateZ, Matrix.mul_smul, Matrix.smul_mul, hadamard_mul_one_add_smul_mul_hadamard,
    hadamard_mul_siteZ_mul_hadamard, hGateX]

theorem hadamard_mul_ssGateXX_mul_hadamard [NeZero N] (j : Fin N) :
    hadamard N * ssGateXX j * hadamard N = hGateZZ j := by
  rw [ssGateXX, Matrix.mul_smul, Matrix.smul_mul, hadamard_mul_one_add_smul_mul_hadamard,
    hadamard_mul_mul_mul_hadamard, hadamard_mul_siteX_mul_hadamard,
    hadamard_mul_siteX_mul_hadamard, hGateZZ, siteZZ]

/-- The Hadamard gate carries `η = ∏_j Z_j` to the global spin flip `∏_j X_j`. -/
theorem hadamard_mul_ssEta_mul_hadamard : hadamard N * ssEta N * hadamard N = spinFlip N := by
  have hdiag : ssEta N = Matrix.diagonal fun x => ∏ k, bitSign (x k) ((1 : Fin N → Fin 2) k) := by
    have h : (List.ofFn fun j : Fin N => siteZ j) =
        (List.ofFn fun j : Fin N => fun x : Fin N → Fin 2 => (-1 : ℂ) ^ (x j).val).map
          (Matrix.diagonalRingHom (Fin N → Fin 2) ℂ) := by
      rw [List.map_ofFn]
      rfl
    rw [ssEta, h, ← map_list_prod, List.prod_ofFn]
    simp only [Matrix.diagonalRingHom_apply, Pi.one_apply, bitSign_comm _ 1, bitSign_one_left]
    congr 1
    funext x
    exact Finset.prod_apply x _ _
  ext c b
  rw [hdiag, hadamard_mul_diagonal_mul_hadamard_apply, spinFlip]
  clear hdiag
  refine if_congr ?_ rfl rfl
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, Pi.one_apply, flipConfig]
  refine forall_congr' fun k => ?_
  generalize_decide c k, b k

theorem hadamard_mul_one_add_mul_hadamard (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    hadamard N * (1 + A) * hadamard N = 1 + hadamard N * A * hadamard N := by
  simpa using hadamard_mul_one_add_smul_mul_hadamard (1 : ℂ) A

/-! ### The single-path evaluation in the Hadamard frame

Each gate `(1 + i X_k)/√2` changes only the bit at site `k`, and each site carries exactly one
such gate. An entry of the product of the gates is therefore a single product along one path of
intermediate configurations, with no sum. -/

theorem hGateZZ_eq_diagonal [NeZero N] (j : Fin N) :
    hGateZZ j = Matrix.diagonal fun b =>
      invSqrtTwo * (1 + I * ((-1 : ℂ) ^ (b j).val * (-1 : ℂ) ^ (b (j + 1)).val)) := by
  ext c b
  by_cases h : c = b <;>
    simp [hGateZZ, siteZZ_eq_diagonal, h]

theorem mul_hGateX_apply (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (j : Fin N)
    (c b : Fin N → Fin 2) :
    (M * hGateX j) c b = invSqrtTwo * (M c b + I * M c (b + Pi.single j 1)) := by
  rw [hGateX, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_apply,
    Matrix.add_apply, Matrix.smul_apply, mul_siteX_apply, smul_eq_mul, smul_eq_mul]

/-- The weight of one step of the path: the gate `(1 + i X_k)/√2` from bit `y` to bit `x`,
followed by the diagonal gate `(1 + i Z_k Z_{k+1})/√2` on the bits `y` and `z`. -/
private def pathWeight (x y z : Fin 2) : ℂ :=
  invSqrtTwo * (if x = y then 1 else I) *
    (invSqrtTwo * (1 + I * ((-1 : ℂ) ^ y.val * (-1 : ℂ) ^ z.val)))

/-- Entries of the first `m` gate pairs of the circuit in the Hadamard frame: the input and output
agree from site `m` on, and the entry is the product of the path weights over the first `m`
sites. -/
private theorem prefix_apply (n : ℕ) (m : ℕ) (hm : m ≤ n) (c b : Fin (n + 1) → Fin 2) :
    (List.ofFn fun k : Fin m =>
        hGateX ((k : ℕ) : Fin (n + 1)) * hGateZZ ((k : ℕ) : Fin (n + 1))).prod c b =
      if ∀ k : Fin (n + 1), m ≤ k.val → c k = b k then
        ∏ k ∈ Finset.range m,
          pathWeight (c (k : Fin (n + 1))) (b (k : Fin (n + 1))) (c ((k + 1 : ℕ) : Fin (n + 1)))
      else 0 := by
  classical
  induction m generalizing b with
  | zero =>
    have hiff : (∀ k : Fin (n + 1), 0 ≤ k.val → c k = b k) ↔ c = b :=
      ⟨fun h => funext fun k => h k (Nat.zero_le _), fun h k _ => h ▸ rfl⟩
    simp only [List.ofFn_zero, List.prod_nil, Matrix.one_apply, Finset.range_zero,
      Finset.prod_empty]
    exact if_congr hiff.symm rfl rfl
  | succ m ih =>
    have hm' : m ≤ n := Nat.le_of_succ_le hm
    set s : Fin (n + 1) := ((m : ℕ) : Fin (n + 1)) with hs
    have hsval : s.val = m := Fin.val_cast_of_lt (Nat.lt_succ_of_le hm')
    have hs1 : s + 1 = ((m + 1 : ℕ) : Fin (n + 1)) := by rw [hs]; push_cast; rfl
    have hs1val : (((m + 1 : ℕ)) : Fin (n + 1)).val = m + 1 :=
      Fin.val_cast_of_lt (Nat.lt_succ_of_le hm)
    have hlt (k : ℕ) (hk : k < m) : ((k : ℕ) : Fin (n + 1)) ≠ s := by
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_cast_of_lt (by omega), hsval] at this
      omega
    have hsingle (k : ℕ) (hk : k < m) :
        (b + Pi.single s 1 : Fin (n + 1) → Fin 2) ((k : ℕ) : Fin (n + 1)) =
          b ((k : ℕ) : Fin (n + 1)) := by
      simp [hlt k hk]
    have hsingle_s : (b + Pi.single s 1 : Fin (n + 1) → Fin 2) s = b s + 1 := by simp
    have hprod : (∏ k ∈ Finset.range m, pathWeight (c (k : Fin (n + 1)))
          ((b + Pi.single s 1 : Fin (n + 1) → Fin 2) (k : Fin (n + 1)))
          (c ((k + 1 : ℕ) : Fin (n + 1)))) =
        ∏ k ∈ Finset.range m,
          pathWeight (c (k : Fin (n + 1))) (b (k : Fin (n + 1))) (c ((k + 1 : ℕ) : Fin (n + 1))) :=
      Finset.prod_congr rfl fun k hk => by rw [hsingle k (Finset.mem_range.mp hk)]
    -- the bit at site `m + 1` is read from the input, which agrees with the output there
    have hnext (hS : ∀ k : Fin (n + 1), m + 1 ≤ k.val → c k = b k) :
        b (s + 1) = c ((m + 1 : ℕ) : Fin (n + 1)) := by
      rw [hs1]; exact (hS _ hs1val.ge).symm
    rw [List.ofFn_succ', List.prod_concat, ← Matrix.mul_assoc, hGateZZ_eq_diagonal,
      Matrix.mul_diagonal]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← hs, mul_hGateX_apply, ih hm' b, ih hm' _, Finset.prod_range_succ, hprod]
    by_cases hc : c s = b s
    · have hno : ¬ ∀ k : Fin (n + 1), m ≤ k.val →
          c k = (b + Pi.single s 1 : Fin (n + 1) → Fin 2) k := by
        intro h
        have := h s hsval.ge
        rw [hsingle_s, hc] at this
        revert this; generalize b s = x; revert x; decide
      rw [ite_eq_right hno, mul_zero, add_zero]
      have hiff : (∀ k : Fin (n + 1), m ≤ k.val → c k = b k) ↔
          ∀ k : Fin (n + 1), m + 1 ≤ k.val → c k = b k := by
        refine ⟨fun h k hk => h k (by omega), fun h k hk => ?_⟩
        rcases Nat.eq_or_lt_of_le hk with hk' | hk'
        · have : k = s := Fin.ext (by rw [hsval, hk'])
          rw [this, hc]
        · exact h k hk'
      by_cases hS : ∀ k : Fin (n + 1), m + 1 ≤ k.val → c k = b k
      · rw [ite_eq_left (hiff.mpr hS), ite_eq_left hS, hnext hS, pathWeight, ite_eq_left hc]
        ring
      · rw [ite_eq_right (mt hiff.mp hS), ite_eq_right hS]
        ring
    · have hno : ¬ ∀ k : Fin (n + 1), m ≤ k.val → c k = b k := fun h => hc (h s hsval.ge)
      rw [ite_eq_right hno, zero_add]
      have hiff : (∀ k : Fin (n + 1), m ≤ k.val →
            c k = (b + Pi.single s 1 : Fin (n + 1) → Fin 2) k) ↔
          ∀ k : Fin (n + 1), m + 1 ≤ k.val → c k = b k := by
        refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
        · have hks : k ≠ s := fun h' => by rw [h', hsval] at hk; omega
          rw [h k (by omega)]
          simp [hks]
        · rcases Nat.eq_or_lt_of_le hk with hk' | hk'
          · have : k = s := Fin.ext (by rw [hsval, hk'])
            rw [this, hsingle_s]
            revert hc; generalize c s = x, b s = y; revert x y; decide
          · have hks : k ≠ s := fun h' => by rw [h', hsval] at hk'; omega
            rw [h k hk']
            simp [hks]
      by_cases hS : ∀ k : Fin (n + 1), m + 1 ≤ k.val → c k = b k
      · rw [ite_eq_left (hiff.mpr hS), ite_eq_left hS, hnext hS, pathWeight, ite_eq_right hc]
        ring
      · rw [ite_eq_right (mt hiff.mp hS), ite_eq_right hS]
        ring

/-- The full product of gates in the Hadamard frame, before the projection: a single path
with the last gate `(1 + i X_n)/√2`. -/
private theorem prefix_mul_hGateX_last_apply (n : ℕ) (c b : Fin (n + 1) → Fin 2) :
    ((List.ofFn fun k : Fin n =>
        hGateX ((k : ℕ) : Fin (n + 1)) * hGateZZ ((k : ℕ) : Fin (n + 1))).prod *
        hGateX (Fin.last n)) c b =
      invSqrtTwo * (if c (Fin.last n) = b (Fin.last n) then 1 else I) *
        ∏ k ∈ Finset.range n,
          pathWeight (c (k : Fin (n + 1))) (b (k : Fin (n + 1)))
            (c ((k + 1 : ℕ) : Fin (n + 1))) := by
  classical
  have hlast (k : Fin (n + 1)) : n ≤ k.val ↔ k = Fin.last n :=
    ⟨fun h => Fin.ext (by have := k.isLt; simp; omega), fun h => by simp [h]⟩
  have hsingle (k : ℕ) (hk : k < n) :
      (b + Pi.single (Fin.last n) 1 : Fin (n + 1) → Fin 2) ((k : ℕ) : Fin (n + 1)) =
        b ((k : ℕ) : Fin (n + 1)) := by
    have hne : ((k : ℕ) : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_cast_of_lt (Nat.lt_succ_of_le hk.le), Fin.val_last] at this
      omega
    simp [hne]
  have hprod : (∏ k ∈ Finset.range n, pathWeight (c (k : Fin (n + 1)))
        ((b + Pi.single (Fin.last n) 1 : Fin (n + 1) → Fin 2) (k : Fin (n + 1)))
        (c ((k + 1 : ℕ) : Fin (n + 1)))) =
      ∏ k ∈ Finset.range n,
        pathWeight (c (k : Fin (n + 1))) (b (k : Fin (n + 1))) (c ((k + 1 : ℕ) : Fin (n + 1))) :=
    Finset.prod_congr rfl fun k hk => by rw [hsingle k (Finset.mem_range.mp hk)]
  rw [mul_hGateX_apply, prefix_apply n n le_rfl, prefix_apply n n le_rfl, hprod]
  have hiff (x : Fin (n + 1) → Fin 2) :
      (∀ k : Fin (n + 1), n ≤ k.val → c k = x k) ↔ c (Fin.last n) = x (Fin.last n) :=
    ⟨fun h => h _ (by simp), fun h k hk => by rw [(hlast k).mp hk]; exact h⟩
  simp only [hiff, Pi.add_apply, Pi.single_eq_same]
  by_cases hc : c (Fin.last n) = b (Fin.last n)
  · have hno : ¬ c (Fin.last n) = b (Fin.last n) + 1 := by
      rw [hc]; generalize b (Fin.last n) = x; revert x; decide
    rw [ite_eq_left hc, ite_eq_right hno, ite_eq_left hc]
    ring
  · have hyes : c (Fin.last n) = b (Fin.last n) + 1 := by
      revert hc; generalize c (Fin.last n) = x, b (Fin.last n) = y; revert x y; decide
    rw [ite_eq_right hc, ite_eq_left hyes, ite_eq_right hc]
    ring

/-! ### Phase bookkeeping -/

private theorem pathWeight_eq (x y z : Fin 2) :
    pathWeight x y z =
      invSqrtTwo * invSqrtTwo * (1 + I) * (I ^ x.val * (-I) ^ z.val) * bitSign y (x + z) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    (simp [pathWeight, bitSign]; ring_nf; try simp only [Complex.I_sq]; try ring_nf)

private theorem bitSign_rev_left (y w : Fin 2) :
    bitSign y.rev w = bitSign y w * (-1 : ℂ) ^ w.val := by
  fin_cases y <;> fin_cases w <;> simp [bitSign]

/-- A telescoping product `∏_{k<m} u_k v_{k+1} = u_0 v_m` when `v_k u_k = 1`. -/
private theorem prod_range_mul_succ_eq (u v : ℕ → ℂ) (h : ∀ k, v k * u k = 1) (m : ℕ) :
    ∏ k ∈ Finset.range m, u k * v (k + 1) = u 0 * v m := by
  induction m with
  | zero => rw [Finset.prod_range_zero, mul_comm, h 0]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    linear_combination (u 0 * v (m + 1)) * h m

private theorem neg_I_pow_mul_I_pow (x : Fin 2) : (-I) ^ x.val * I ^ x.val = 1 := by
  fin_cases x <;> simp

/-- The scalar `e^{-2π i N/8}` of the circuit is `(e^{-iπ/4})^N` with `e^{-iπ/4} = (1 - i)/√2`. -/
private theorem exp_circuitPhase (n : ℕ) :
    Complex.exp (-(2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) / 8)) =
      (invSqrtTwo * (1 - I)) ^ (n + 1) := by
  have harg : -(2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) / 8) =
      ((n + 1 : ℕ) : ℂ) * (((-(Real.pi / 4) : ℝ) : ℂ) * I) := by
    push_cast; ring
  have hsqrt : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = invSqrtTwo := by
    rw [Complex.invSqrtTwo, Real.sqrt_div_self', one_div, Complex.ofReal_inv]
  rw [harg, Complex.exp_nat_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.ofReal_neg,
    hsqrt]
  ring

/-- The boundary factor: the last gate, the projection `½(1 + η)`, the leftover phases of the
telescoping products, and the scalar `e^{-iπ/4}` combine to the sign of the closing bond. -/
private theorem boundary_phase (x y z : Fin 2) :
    (1 - I) * 2⁻¹ * (I ^ x.val * (-I) ^ z.val) *
        ((if z = y then 1 else I) + (if z = y.rev then 1 else I) *
          ((-1 : ℂ) ^ x.val * (-1 : ℂ) ^ z.val)) =
      bitSign y (z + x) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    (simp [bitSign]; ring_nf; try simp only [Complex.I_sq, Complex.I_pow_three]; try ring_nf)

/-! ### The circuit is the Hadamard image of the rescaled transposed kernel -/

private theorem hadamard_mul_ssCircuit_mul_hadamard_eq_prefix (n : ℕ) :
    hadamard (n + 1) * ssCircuit n * hadamard (n + 1) =
      Complex.exp (-(2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) / 8)) •
        ((List.ofFn fun k : Fin n =>
            hGateX ((k : ℕ) : Fin (n + 1)) * hGateZZ ((k : ℕ) : Fin (n + 1))).prod *
          hGateX (Fin.last n) * ((2 : ℂ)⁻¹ • (1 + spinFlip (n + 1)))) := by
  rw [ssCircuit, Matrix.mul_smul, Matrix.smul_mul, hadamard_mul_mul_mul_hadamard,
    hadamard_mul_mul_mul_hadamard, hadamard_mul_list_prod_mul_hadamard, List.map_ofFn,
    Matrix.mul_smul, Matrix.smul_mul, hadamard_mul_one_add_mul_hadamard,
    hadamard_mul_ssEta_mul_hadamard, hadamard_mul_ssGateZ_mul_hadamard]
  congr 4
  refine congrArg List.ofFn (funext fun k => ?_)
  simp only [Function.comp_apply, hadamard_mul_mul_mul_hadamard,
    hadamard_mul_ssGateZ_mul_hadamard, hadamard_mul_ssGateXX_mul_hadamard, Fin.coe_eq_castSucc]

/-- **The Seiberg–Shao circuit is the Kramers–Wannier kernel in the Hadamard frame**:
`H^{⊗N} 𝖣 H^{⊗N} = 2^{-(N+1)/2} Kᵀ = kwTranslation N` on `N = n + 1` sites, with scalar exactly
one. Here `K = kwTensor.mpo N` has kernel `(-1)^{∑_j a_j (b_j + b_{j+1})}`.

The proof evaluates the circuit entrywise. In the Hadamard frame each factor `(1 + i X_k)/√2`
changes only bit `k`, so each entry of the gate product is one product along a single path;
the diagonal factors `(1 + i Z_k Z_{k+1})/√2` contribute the phases `e^{±iπ/4}` of the open-chain
bonds, the projection `½(1 + η)` supplies the closing bond, and the scalar `e^{-2π i N/8}` cancels
the accumulated phase.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2431–2437 (the
circuit); the identification with the kernel is a project result. -/
theorem hadamard_mul_ssCircuit_mul_hadamard (n : ℕ) :
    hadamard (n + 1) * ssCircuit n * hadamard (n + 1) = kwTranslation (n + 1) := by
  rw [hadamard_mul_ssCircuit_mul_hadamard_eq_prefix]
  ext c b
  have hproj (M : Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) ℂ) :
      (M * ((2 : ℂ)⁻¹ • (1 + spinFlip (n + 1)))) c b = 2⁻¹ * (M c b + M c (flipConfig b)) := by
    rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_apply, Matrix.add_apply,
      mul_spinFlip_apply, smul_eq_mul]
  have h0 : c ((0 : ℕ) : Fin (n + 1)) = c 0 := by rw [Nat.cast_zero]
  have hn : c ((n : ℕ) : Fin (n + 1)) = c (Fin.last n) := by rw [Fin.natCast_eq_last]
  have hP (x : Fin (n + 1) → Fin 2) :
      ∏ k ∈ Finset.range n,
          pathWeight (c (k : Fin (n + 1))) (x (k : Fin (n + 1))) (c ((k + 1 : ℕ) : Fin (n + 1))) =
        (invSqrtTwo * invSqrtTwo * (1 + I)) ^ n *
          (I ^ (c 0).val * (-I) ^ (c (Fin.last n)).val) *
          ∏ k ∈ Finset.range n,
            bitSign (x (k : Fin (n + 1)))
              (c (k : Fin (n + 1)) + c ((k + 1 : ℕ) : Fin (n + 1))) := by
    have htel := prod_range_mul_succ_eq (fun k => I ^ (c (k : Fin (n + 1))).val)
      (fun k => (-I) ^ (c (k : Fin (n + 1))).val) (fun k => neg_I_pow_mul_I_pow _) n
    simp only [h0, hn] at htel
    simp_rw [pathWeight_eq]
    rw [← htel, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
  have hB : ∏ k ∈ Finset.range n,
        bitSign ((flipConfig b) (k : Fin (n + 1)))
          (c (k : Fin (n + 1)) + c ((k + 1 : ℕ) : Fin (n + 1))) =
      (∏ k ∈ Finset.range n,
        bitSign (b (k : Fin (n + 1))) (c (k : Fin (n + 1)) + c ((k + 1 : ℕ) : Fin (n + 1)))) *
        ((-1 : ℂ) ^ (c 0).val * (-1 : ℂ) ^ (c (Fin.last n)).val) := by
    have hsign (x z : Fin 2) : (-1 : ℂ) ^ (x + z).val = (-1 : ℂ) ^ x.val * (-1 : ℂ) ^ z.val := by
      fin_cases x <;> fin_cases z <;> simp
    simp_rw [flipConfig, bitSign_rev_left, Finset.prod_mul_distrib, hsign]
    rw [prod_range_mul_succ_eq (fun k => (-1 : ℂ) ^ (c (k : Fin (n + 1))).val)
      (fun k => (-1 : ℂ) ^ (c (k : Fin (n + 1))).val)
      (fun k => neg_one_pow_mul_neg_one_pow_self _) n, h0, hn]
  have hK : ∏ j : Fin (n + 1), bitSign (b j) (c j + c (j + 1)) =
      (∏ k ∈ Finset.range n,
        bitSign (b (k : Fin (n + 1))) (c (k : Fin (n + 1)) + c ((k + 1 : ℕ) : Fin (n + 1)))) *
        bitSign (b (Fin.last n)) (c (Fin.last n) + c 0) := by
    rw [Fin.prod_univ_castSucc, Fin.last_add_one,
      ← Fin.prod_univ_eq_prod_range (fun k => bitSign (b (k : Fin (n + 1)))
        (c (k : Fin (n + 1)) + c ((k + 1 : ℕ) : Fin (n + 1)))) n]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Fin.coe_eq_castSucc]
    push_cast
    rfl
  have he : Complex.exp (-(2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) / 8)) *
      (invSqrtTwo * invSqrtTwo * (1 + I)) ^ n = invSqrtTwo ^ n * (invSqrtTwo * (1 - I)) := by
    have hωX : invSqrtTwo * (1 - I) * (invSqrtTwo * invSqrtTwo * (1 + I)) = invSqrtTwo := by
      have hI : (1 - I) * (1 + I) = 2 := by ring_nf; rw [Complex.I_sq]; ring
      calc invSqrtTwo * (1 - I) * (invSqrtTwo * invSqrtTwo * (1 + I))
          = (invSqrtTwo * invSqrtTwo) * invSqrtTwo * ((1 - I) * (1 + I)) := by ring
        _ = invSqrtTwo := by rw [invSqrtTwo_mul_self, hI]; field_simp
    rw [exp_circuitPhase, pow_succ', mul_assoc, ← mul_pow, hωX, mul_comm]
  have hbd := boundary_phase (c 0) (b (Fin.last n)) (c (Fin.last n))
  rw [Matrix.smul_apply, hproj, prefix_mul_hGateX_last_apply, prefix_mul_hGateX_last_apply,
    hP b, hP (flipConfig b), hB, smul_eq_mul, kwTranslation, Matrix.smul_apply,
    Matrix.transpose_apply, kwTensor_mpo_eq_prod_bitSign, hK, smul_eq_mul]
  rw [show (b (Fin.last n)).rev = flipConfig b (Fin.last n) from rfl] at hbd
  set E := Complex.exp (-(2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) / 8))
  set B := ∏ k ∈ Finset.range n,
    bitSign (b (k : Fin (n + 1))) (c (k : Fin (n + 1)) + c ((k + 1 : ℕ) : Fin (n + 1)))
  set t₁ : ℂ := if c (Fin.last n) = b (Fin.last n) then 1 else I
  set t₂ : ℂ := if c (Fin.last n) = flipConfig b (Fin.last n) then 1 else I
  set φ := I ^ (c 0).val * (-I) ^ (c (Fin.last n)).val
  set σ := (-1 : ℂ) ^ (c 0).val * (-1 : ℂ) ^ (c (Fin.last n)).val
  set X := invSqrtTwo * invSqrtTwo * (1 + I)
  linear_combination (2⁻¹ * invSqrtTwo * φ * B * (t₁ + t₂ * σ)) * he +
    (invSqrtTwo ^ (n + 2) * B) * hbd

/-! ### The printed relations for the circuit -/

theorem ssCircuit_eq (n : ℕ) :
    ssCircuit n = hadamard (n + 1) * kwTranslation (n + 1) * hadamard (n + 1) := by
  rw [← hadamard_mul_ssCircuit_mul_hadamard, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hadamard_mul_self, Matrix.one_mul, Matrix.mul_assoc, hadamard_mul_self, Matrix.mul_one]

/-- Transport of an intertwining relation `A B = C A` through the Hadamard change of basis. -/
theorem hadamard_conj_intertwine {A B C : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (h : A * B = C * A) :
    (hadamard N * A * hadamard N) * (hadamard N * B * hadamard N) =
      (hadamard N * C * hadamard N) * (hadamard N * A * hadamard N) := by
  rw [← hadamard_mul_mul_mul_hadamard, h, hadamard_mul_mul_mul_hadamard]

theorem ssEta_eq : ssEta N = hadamard N * spinFlip N * hadamard N := by
  rw [← hadamard_mul_ssEta_mul_hadamard, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hadamard_mul_self, Matrix.one_mul, Matrix.mul_assoc, hadamard_mul_self, Matrix.mul_one]

theorem siteZ_eq_hadamard_conj (j : Fin N) : siteZ j = hadamard N * siteX j * hadamard N :=
  (hadamard_mul_siteX_mul_hadamard j).symm

theorem siteXX_eq_hadamard_conj [NeZero N] (j : Fin N) :
    siteX j * siteX (j + 1) = hadamard N * siteZZ j * hadamard N := by
  rw [siteZZ, hadamard_mul_mul_mul_hadamard, hadamard_mul_siteZ_mul_hadamard,
    hadamard_mul_siteZ_mul_hadamard]

/-- **`𝖣 Z_j = X_j X_{j+1} 𝖣`** for the circuit, at every site of the ring, including the
closing bond `X_N X_1` that does not occur among the factors of the circuit.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2442–2447. -/
theorem ssCircuit_mul_siteZ (n : ℕ) (j : Fin (n + 1)) :
    ssCircuit n * siteZ j = (siteX j * siteX (j + 1)) * ssCircuit n := by
  rw [ssCircuit_eq, siteZ_eq_hadamard_conj, siteXX_eq_hadamard_conj]
  exact hadamard_conj_intertwine (kwTranslation_mul_siteX j)

/-- **`𝖣 X_j X_{j+1} = Z_{j+1} 𝖣`** for the circuit, at every site of the ring.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2442–2447. -/
theorem ssCircuit_mul_siteXX (n : ℕ) (j : Fin (n + 1)) :
    ssCircuit n * (siteX j * siteX (j + 1)) = siteZ (j + 1) * ssCircuit n := by
  rw [ssCircuit_eq, siteZ_eq_hadamard_conj, siteXX_eq_hadamard_conj]
  exact hadamard_conj_intertwine (kwTranslation_mul_siteZZ j)

/-- **`𝖣 η = 𝖣`** for the circuit.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2471. -/
theorem ssCircuit_mul_ssEta (n : ℕ) : ssCircuit n * ssEta (n + 1) = ssCircuit n := by
  rw [ssCircuit_eq, ssEta_eq, ← hadamard_mul_mul_mul_hadamard, kwTranslation_mul_spinFlip]

/-- **`η 𝖣 = 𝖣`** for the circuit.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2471. -/
theorem ssEta_mul_ssCircuit (n : ℕ) : ssEta (n + 1) * ssCircuit n = ssCircuit n := by
  rw [ssCircuit_eq, ssEta_eq, ← hadamard_mul_mul_mul_hadamard, spinFlip_mul_kwTranslation]

theorem hadamard_conjTranspose : (hadamard N)ᴴ = hadamard N := by
  ext c b
  simp only [Matrix.conjTranspose_apply, hadamard, star_mul', star_pow, star_invSqrtTwo,
    star_prod, star_bitSign, bitSign_comm (b _)]

theorem conjTranspose_hadamard_conj (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    (hadamard N * A * hadamard N)ᴴ = hadamard N * Aᴴ * hadamard N := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hadamard_conjTranspose,
    Matrix.mul_assoc]

theorem hadamard_conj_half_one_add (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    hadamard N * ((2 : ℂ)⁻¹ • (1 + A)) * hadamard N =
      (2 : ℂ)⁻¹ • (1 + hadamard N * A * hadamard N) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, hadamard_mul_one_add_mul_hadamard]

/-- **`𝖣 𝖣† = ½(1 + η)`** for the circuit.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2475. -/
theorem ssCircuit_mul_conjTranspose (n : ℕ) :
    ssCircuit n * (ssCircuit n)ᴴ = (2 : ℂ)⁻¹ • (1 + ssEta (n + 1)) := by
  rw [ssCircuit_eq, conjTranspose_hadamard_conj, ← hadamard_mul_mul_mul_hadamard,
    kwTranslation_mul_conjTranspose, hadamard_conj_half_one_add, ← ssEta_eq]

/-- **`𝖣† 𝖣 = ½(1 + η)`** for the circuit.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2475. -/
theorem ssCircuit_conjTranspose_mul (n : ℕ) :
    (ssCircuit n)ᴴ * ssCircuit n = (2 : ℂ)⁻¹ • (1 + ssEta (n + 1)) := by
  rw [ssCircuit_eq, conjTranspose_hadamard_conj, ← hadamard_mul_mul_mul_hadamard,
    kwTranslation_conjTranspose_mul, hadamard_conj_half_one_add, ← ssEta_eq]

/-- The transposed translation sends the basis vector at `b` to the one at `b (· - 1)`, the
action `|m_1, …, m_N⟩ ↦ |m_N, m_1, …, m_{N-1}⟩` of the product of swap gates
`T_Ising = t_1 ⋯ t_{N-1}` of arXiv:2307.02534,
`References/2307.02534/source/Majoranadraft.tex` lines 2115–2123. -/
theorem transpose_translate_apply [NeZero N] (c b : Fin N → Fin 2) :
    (translate N)ᵀ c b = if c = fun j => b (j - 1) then 1 else 0 := by
  rw [Matrix.transpose_apply, translate]
  exact if_congr (eq_shift_iff b c) rfl rfl

/-- The site-uniform Hadamard gate commutes with the translation. -/
theorem hadamard_mul_transpose_translate [NeZero N] :
    hadamard N * (translate N)ᵀ = (translate N)ᵀ * hadamard N := by
  ext c b
  rw [mul_transpose_translate_apply, transpose_translate_mul_apply, hadamard, hadamard]
  congr 1
  exact (Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun j => by simp)).symm

/-- **`𝖣² = ½(1 + η) T_Ising`** for the circuit, with `T_Ising = Tᵀ` the translation that sends
`|m_1, …, m_N⟩` to `|m_N, m_1, …, m_{N-1}⟩` (`transpose_translate_apply`).

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2470. -/
theorem ssCircuit_mul_self (n : ℕ) :
    ssCircuit n * ssCircuit n =
      (2 : ℂ)⁻¹ • ((1 + ssEta (n + 1)) * (translate (n + 1))ᵀ) := by
  have hT : hadamard (n + 1) * (translate (n + 1))ᵀ * hadamard (n + 1) = (translate (n + 1))ᵀ := by
    rw [hadamard_mul_transpose_translate, Matrix.mul_assoc, hadamard_mul_self, Matrix.mul_one]
  rw [ssCircuit_eq, ← hadamard_mul_mul_mul_hadamard, kwTranslation_mul_self, Matrix.mul_smul,
    Matrix.smul_mul, hadamard_mul_mul_mul_hadamard, hadamard_mul_one_add_mul_hadamard, hT,
    ← ssEta_eq]

/-! ### Kernel and range of the circuit -/

/-- **The kernel of the circuit is the sector `η = -1`**: `𝖣 v = 0 ↔ η v = -v`.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2423 (the
operator has a kernel, the states with `η = -1`). -/
theorem ssCircuit_mulVec_eq_zero_iff (n : ℕ) (v : (Fin (n + 1) → Fin 2) → ℂ) :
    ssCircuit n *ᵥ v = 0 ↔ ssEta (n + 1) *ᵥ v = -v := by
  constructor
  · intro h
    have h2 : ((ssCircuit n)ᴴ * ssCircuit n) *ᵥ v = 0 := by
      rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    rw [ssCircuit_conjTranspose_mul, Matrix.smul_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec] at h2
    have h3 := (smul_eq_zero.mp h2).resolve_left (inv_ne_zero two_ne_zero)
    rw [eq_neg_iff_add_eq_zero]
    exact (add_comm _ _).trans h3
  · intro h
    have h2 : ssCircuit n *ᵥ v = -(ssCircuit n *ᵥ v) := by
      conv_lhs => rw [← ssCircuit_mul_ssEta, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_neg]
    rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h2
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **The range of the circuit is the sector `η = +1`**: `y` is in the range of `𝖣` exactly
when `η y = y`. On this sector `𝖣 𝖣† = ½(1 + η)` is the identity, so `𝖣` acts there as a
unitary, the partial isometry of the source.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2423 (in the
orthogonal complement of the kernel, the states with `η = +1`, the operator acts unitarily). -/
theorem exists_ssCircuit_mulVec_eq_iff (n : ℕ) (y : (Fin (n + 1) → Fin 2) → ℂ) :
    (∃ v, ssCircuit n *ᵥ v = y) ↔ ssEta (n + 1) *ᵥ y = y := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [Matrix.mulVec_mulVec, ssEta_mul_ssCircuit]
  · intro hy
    refine ⟨(ssCircuit n)ᴴ *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, ssCircuit_mul_conjTranspose, Matrix.smul_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, hy, ← two_smul ℂ y, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]

end KWExample
