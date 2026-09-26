/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Nonnegative integer representations of `Rep(S₃)` and `su(2)₄`

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section `sec:examples`,
`Papers/2203.12563/REsubmission.tex` lines 1890–1931 (`su(2)₄`: the fusion table of the labels
`0, 1/2, 1, 3/2, 2`, the two phases, the action of the labels on the four blocks `x, y, z, s`
of the module `𝓜_TY`, and the invariance of `{x, y, z}` and `{s}` under the labels `0, 1, 2`)
and lines 1933–1989 (`Rep(S₃)`: the fusion rules of `1, π, ψ`, the embedding into `su(2)₄`
by `0, 1, 2 ↦ 1, π, ψ`, and the actions on the blocks of the four phases labelled by the
subgroups `ℤ₁, ℤ₂, ℤ₃, S₃`, with the correspondences to restrictions of the `su(2)₄` phases).

**Formalized here.** The two fusion rings, and each printed action as a nonnegative integer
representation (`MPOTensor.IsNIMRep`, the relation of lines 564–565) on which the unit acts as
the identity: the regular representation and `𝓜_TY` of `su(2)₄`; the representations of the
four `Rep(S₃)` phases, the last of which is the regular one. The embedding of `Rep(S₃)` as the
integer labels of `su(2)₄`, and the source's identification of the `ℤ₁`, `ℤ₂` and `ℤ₃` phases
with restrictions of the `su(2)₄` phases. The rank-one case of the classification: the only
action of `Rep(S₃)` on one block with the unit acting trivially is the `ℤ₁` phase, and
`su(2)₄` has none.

**Local fix (`ℤ₃` table):** the printed `ℤ₃` action has `ψ` exchanging `y` and `z`, which is
not a representation (`MPOTensor.not_isNIMRep_repS3Z3Printed`); `ψ` fixes every block, as in
the source's own identification of this phase with `𝓜_TY` on `{x, y, z}` (line 1972).
Documented in `docs/paper-gaps/glm23_reps3_su24_module_list.tex`.

**Scope restriction (printed list):** the source's statements that `su(2)₄` has exactly two
phases and `Rep(S₃)` exactly the four listed ones rest on the classification of module
categories that it cites; beyond one block, completeness of the lists is not formalized.
Documented in `docs/paper-gaps/glm23_reps3_su24_module_list.tex`.

## Main definitions

* `MPOTensor.su24Fusion`, `MPOTensor.su24TY`: the `su(2)₄` fusion ring and the action on the
  four blocks of `𝓜_TY`.
* `MPOTensor.repS3Fusion`, `MPOTensor.repS3Z1`, `MPOTensor.repS3Z2`, `MPOTensor.repS3Z3`: the
  `Rep(S₃)` fusion ring and the actions of the `ℤ₁`, `ℤ₂`, `ℤ₃` phases.
* `MPOTensor.repS3Z3Printed`: the `ℤ₃` action as printed.
* `MPOTensor.repS3ToSU24`: the labels `1, π, ψ` as the integer labels `0, 1, 2` of `su(2)₄`.

## Main results

* `MPOTensor.isNIMRep_su24Fusion`, `MPOTensor.isNIMRep_su24TY`,
  `MPOTensor.isNIMRep_repS3Fusion`, `MPOTensor.isNIMRep_repS3Z1`, `MPOTensor.isNIMRep_repS3Z2`,
  `MPOTensor.isNIMRep_repS3Z3`: the actions represent the fusion rings.
* `MPOTensor.not_isNIMRep_repS3Z3Printed`: the printed `ℤ₃` action does not.
* `MPOTensor.su24Fusion_repS3ToSU24`: `Rep(S₃)` is the fusion subring of integer labels.
* `MPOTensor.su24TY_repS3ToSU24_castSucc`, `MPOTensor.su24TY_repS3ToSU24_last`,
  `MPOTensor.su24Fusion_repS3ToSU24_half`: the `ℤ₃`, `ℤ₁` and `ℤ₂` phases as restrictions.
* `MPOTensor.isFusionCharacter_repS3Fusion_iff`, `MPOTensor.not_isFusionCharacter_su24Fusion`:
  the actions on one block.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

namespace MPOTensor

/-! ### `su(2)₄` -/

/-- **The `su(2)₄` fusion ring** (arXiv:2203.12563, lines 1891–1904): the labels
`0, 1/2, 1, 3/2, 2` are indexed by `0, …, 4` (twice the spin), and `su24Fusion a b c` is the
multiplicity of `c` in `a × b` from the printed table. -/
def su24Fusion : Fin 5 → Matrix (Fin 5) (Fin 5) ℕ
  | 0 => 1
  | 1 => !![0, 1, 0, 0, 0; 1, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0]
  | 2 => !![0, 0, 1, 0, 0; 0, 1, 0, 1, 0; 1, 0, 1, 0, 1; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0]
  | 3 => !![0, 0, 0, 1, 0; 0, 0, 1, 0, 1; 0, 1, 0, 1, 0; 1, 0, 1, 0, 0; 0, 1, 0, 0, 0]
  | 4 => !![0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0]

/-- The label `0` is the unit of `su(2)₄` (arXiv:2203.12563, lines 1891–1904). -/
theorem isFusionUnit_su24Fusion : IsFusionUnit su24Fusion 0 := by
  intro b c
  fin_cases b <;> fin_cases c <;> simp [su24Fusion, Matrix.one_apply]

/-- **The first `su(2)₄` phase** (arXiv:2203.12563, line 1909): five blocks, one for each
label, acted on by the fusion rules themselves; the regular representation is a nonnegative
integer representation. -/
theorem isNIMRep_su24Fusion : IsNIMRep su24Fusion su24Fusion := by
  unfold IsNIMRep; decide +kernel

/-- **The action on the blocks of `𝓜_TY`** (arXiv:2203.12563, lines 1911–1925): the blocks
`x, y, z, s` are indexed by `0, 1, 2, 3`, and `su24TY a u v` is the multiplicity of `v` in
`a · u`: the labels `0` and `2` fix every block, `1/2` and `3/2` send `x, y, z` to `s` and `s`
to `x + y + z`, and `1` sends `x` to `y + z` (and cyclically) and `s` to `2 s`. -/
def su24TY : Fin 5 → Matrix (Fin 4) (Fin 4) ℕ
  | 0 => 1
  | 1 => !![0, 0, 0, 1; 0, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 0]
  | 2 => !![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 0, 0; 0, 0, 0, 2]
  | 3 => !![0, 0, 0, 1; 0, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 0]
  | 4 => 1

/-- **The second `su(2)₄` phase** (arXiv:2203.12563, lines 1911–1925): the action on the four
blocks of `𝓜_TY` is a nonnegative integer representation of `su(2)₄`, with the unit acting as
the identity. -/
theorem isNIMRep_su24TY : IsNIMRep su24Fusion su24TY := by
  unfold IsNIMRep; decide +kernel

/-! ### `Rep(S₃)` -/

/-- **The `Rep(S₃)` fusion ring** (arXiv:2203.12563, line 1934): the labels `1, π, ψ` are
indexed by `0, 1, 2`, with `π × π = 1 + π + ψ`, `ψ × ψ = 1` and `ψ × π = π × ψ = π`. -/
def repS3Fusion : Fin 3 → Matrix (Fin 3) (Fin 3) ℕ
  | 0 => 1
  | 1 => !![0, 1, 0; 1, 1, 1; 0, 1, 0]
  | 2 => !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The label `1` is the unit of `Rep(S₃)` (arXiv:2203.12563, line 1934). -/
theorem isFusionUnit_repS3Fusion : IsFusionUnit repS3Fusion 0 := by
  intro b c
  fin_cases b <;> fin_cases c <;> simp [repS3Fusion, Matrix.one_apply]

/-- **The `S₃` phase is the regular representation** (arXiv:2203.12563, lines 1974–1987): the
action on the three blocks `x, y, z`, indexed by `0, 1, 2`, is `π · x = y`,
`π · y = x + y + z`, `π · z = y`, `ψ · x = z`, `ψ · y = y`, `ψ · z = x`, which "reproduces the
fusion rules of `Rep(S₃)`": it is `repS3Fusion` with `x, y, z = 1, π, ψ`. -/
theorem repS3Fusion_eq_table :
    repS3Fusion 1 = !![0, 1, 0; 1, 1, 1; 0, 1, 0] ∧
      repS3Fusion 2 = !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  ⟨rfl, rfl⟩

/-- The regular representation of `Rep(S₃)` is a nonnegative integer representation
(arXiv:2203.12563, lines 1974–1987). -/
theorem isNIMRep_repS3Fusion : IsNIMRep repS3Fusion repS3Fusion := by
  unfold IsNIMRep; decide +kernel

/-- **The `ℤ₁` phase** (arXiv:2203.12563, lines 1939–1940): one block `s`, invariant under `1`
and `ψ`, with `π · s = 2 s`. -/
def repS3Z1 : Fin 3 → Matrix (Fin 1) (Fin 1) ℕ
  | 0 => 1
  | 1 => !![2]
  | 2 => 1

/-- The `ℤ₁` action is a nonnegative integer representation of `Rep(S₃)`. -/
theorem isNIMRep_repS3Z1 : IsNIMRep repS3Fusion repS3Z1 := by
  unfold IsNIMRep; decide +kernel

/-- **The `ℤ₂` phase** (arXiv:2203.12563, lines 1943–1957): two blocks `x, y`, with
`π · x = π · y = x + y` and `ψ` exchanging `x` and `y`. -/
def repS3Z2 : Fin 3 → Matrix (Fin 2) (Fin 2) ℕ
  | 0 => 1
  | 1 => !![1, 1; 1, 1]
  | 2 => !![0, 1; 1, 0]

/-- The `ℤ₂` action is a nonnegative integer representation of `Rep(S₃)`. -/
theorem isNIMRep_repS3Z2 : IsNIMRep repS3Fusion repS3Z2 := by
  unfold IsNIMRep; decide +kernel

/-- **The `ℤ₃` phase** (arXiv:2203.12563, lines 1959–1971, with the `ψ` row corrected): three
blocks `x, y, z`, with `π · x = y + z` (and cyclically) and `ψ` fixing every block. The source
prints `ψ · y = z`, `ψ · z = y`; see `MPOTensor.not_isNIMRep_repS3Z3Printed`. -/
def repS3Z3 : Fin 3 → Matrix (Fin 3) (Fin 3) ℕ
  | 0 => 1
  | 1 => !![0, 1, 1; 1, 0, 1; 1, 1, 0]
  | 2 => 1

/-- The `ℤ₃` action is a nonnegative integer representation of `Rep(S₃)`. -/
theorem isNIMRep_repS3Z3 : IsNIMRep repS3Fusion repS3Z3 := by
  unfold IsNIMRep; decide +kernel

/-- The `ℤ₃` action as printed at arXiv:2203.12563, lines 1959–1971, with `ψ` fixing `x` and
exchanging `y` and `z`. -/
def repS3Z3Printed : Fin 3 → Matrix (Fin 3) (Fin 3) ℕ
  | 0 => 1
  | 1 => !![0, 1, 1; 1, 0, 1; 1, 1, 0]
  | 2 => !![1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- **The printed `ℤ₃` action is not a representation** (arXiv:2203.12563, lines 1959–1971):
with `ψ` exchanging `y` and `z`, the relation `π × π = 1 + π + ψ` fails on the blocks, since
`π · (π · y) = 2 y + x + z` while `(1 + π + ψ) · y = y + x + 2 z`. -/
theorem not_isNIMRep_repS3Z3Printed : ¬ IsNIMRep repS3Fusion repS3Z3Printed := by
  unfold IsNIMRep; decide +kernel

/-! ### `Rep(S₃)` inside `su(2)₄` -/

/-- **`Rep(S₃)` as the integer labels of `su(2)₄`** (arXiv:2203.12563, line 1934): `1, π, ψ`
correspond to `0, 1, 2`, indexed by `0, 2, 4`. -/
def repS3ToSU24 : Fin 3 → Fin 5 := ![0, 2, 4]

/-- **`Rep(S₃)` is a fusion subring of `su(2)₄`** (arXiv:2203.12563, line 1934): the fusion
rules of the integer labels are those of `Rep(S₃)`. -/
theorem su24Fusion_repS3ToSU24 (a b c : Fin 3) :
    su24Fusion (repS3ToSU24 a) (repS3ToSU24 b) (repS3ToSU24 c) = repS3Fusion a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

/-- Products of integer labels of `su(2)₄` contain no half-integer label (arXiv:2203.12563,
line 1934). -/
theorem su24Fusion_repS3ToSU24_odd (a b : Fin 3) {c : Fin 5} (hc : c = 1 ∨ c = 3) :
    su24Fusion (repS3ToSU24 a) (repS3ToSU24 b) c = 0 := by
  rcases hc with rfl | rfl <;> fin_cases a <;> fin_cases b <;> rfl

/-- **The `ℤ₃` phase is `𝓜_TY` on `{x, y, z}`** (arXiv:2203.12563, lines 1927 and 1972): the
integer labels of `su(2)₄` act on the blocks `x, y, z` of `𝓜_TY` as in the `ℤ₃` phase. -/
theorem su24TY_repS3ToSU24_castSucc (a : Fin 3) (u v : Fin 3) :
    su24TY (repS3ToSU24 a) u.castSucc v.castSucc = repS3Z3 a u v := by
  fin_cases a <;> fin_cases u <;> fin_cases v <;> rfl

/-- **The `ℤ₁` phase is `𝓜_TY` on `{s}`** (arXiv:2203.12563, lines 1927 and 1940): the integer
labels of `su(2)₄` act on the block `s` of `𝓜_TY` as in the `ℤ₁` phase. -/
theorem su24TY_repS3ToSU24_last (a : Fin 3) :
    su24TY (repS3ToSU24 a) (Fin.last 3) (Fin.last 3) = repS3Z1 a 0 0 := by
  fin_cases a <;> rfl

/-- The integer labels of `su(2)₄` do not mix `{x, y, z}` and `{s}` in `𝓜_TY`
(arXiv:2203.12563, line 1927). -/
theorem su24TY_repS3ToSU24_mix (a : Fin 3) (u : Fin 3) :
    su24TY (repS3ToSU24 a) u.castSucc (Fin.last 3) = 0 ∧
      su24TY (repS3ToSU24 a) (Fin.last 3) u.castSucc = 0 := by
  fin_cases a <;> fin_cases u <;> exact ⟨rfl, rfl⟩

/-- **The `ℤ₂` phase is the regular `su(2)₄` phase on `{1/2, 3/2}`** (arXiv:2203.12563,
line 1957): the integer labels of `su(2)₄` act on the blocks `1/2, 3/2` of the first phase as
in the `ℤ₂` phase, with `x, y = 1/2, 3/2`. -/
theorem su24Fusion_repS3ToSU24_half (a : Fin 3) (u v : Fin 2) :
    su24Fusion (repS3ToSU24 a) (![1, 3] u) (![1, 3] v) = repS3Z2 a u v := by
  fin_cases a <;> fin_cases u <;> fin_cases v <;> rfl

/-! ### Actions on one block -/

/-- **The only action of `Rep(S₃)` on one block is the `ℤ₁` phase** (arXiv:2203.12563,
lines 1939–1940). A nonnegative integer representation on one block with the unit acting
trivially is a fusion character in `ℕ`; `m_ψ² = 1` gives `m_ψ = 1`, and then
`m_π² = 1 + m_π + m_ψ` gives `m_π = 2`. -/
theorem isFusionCharacter_repS3Fusion_iff (m : Fin 3 → ℕ) :
    IsFusionCharacter repS3Fusion 0 m ↔ m = ![1, 2, 1] := by
  constructor
  · rintro ⟨h0, hmul⟩
    have h22 : m 2 * m 2 = 1 := by
      simpa [repS3Fusion, Fin.sum_univ_three, h0] using hmul 2 2
    have h11 : m 1 * m 1 = 1 + m 1 + m 2 := by
      have h := hmul 1 1
      simp only [repS3Fusion, Fin.sum_univ_three, h0] at h
      simpa [add_assoc] using h
    have h2 : m 2 = 1 := by nlinarith
    have h1 : m 1 = 2 := by nlinarith
    funext i
    fin_cases i <;> simp [h0, h1, h2]
  · rintro rfl
    refine ⟨rfl, ?_⟩
    decide +kernel

/-- **`su(2)₄` acts on no single block** (arXiv:2203.12563, lines 1906–1925: both phases have
more than one block). A fusion character in `ℕ` would give `m_2 = 1`, then `m_1 = 2`, then
`m_{1/2}² = 3`. -/
theorem not_isFusionCharacter_su24Fusion (m : Fin 5 → ℕ) :
    ¬ IsFusionCharacter su24Fusion 0 m := by
  rintro ⟨h0, hmul⟩
  have h44 : m 4 * m 4 = 1 := by
    simpa [su24Fusion, Fin.sum_univ_five, h0] using hmul 4 4
  have h22 : m 2 * m 2 = 1 + m 2 + m 4 := by
    have h := hmul 2 2
    simp only [su24Fusion, Fin.sum_univ_five, h0] at h
    simpa [add_assoc] using h
  have h11 : m 1 * m 1 = 1 + m 2 := by
    have h := hmul 1 1
    simp only [su24Fusion, Fin.sum_univ_five, h0] at h
    simpa using h
  have h4 : m 4 = 1 := by nlinarith
  have h2 : m 2 = 2 := by nlinarith
  have : m 1 ≤ 2 := by nlinarith
  interval_cases (m 1) <;> omega

end MPOTensor
