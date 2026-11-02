/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import TNLean.Lattice.TranslationSupercell

/-!
# Momentum sectors of the ground space and the supercell

Let an abelian group `G` act on the sites of a finite system, and let `H` be invariant under the
site permutations `P_g`. Hastings, *Solving gapped Hamiltonians locally*
(arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1613–1618), chooses the ground states as
eigenvectors of the translations, with momenta `k_a`. Here the ground space is the span of its
**momentum sectors**: for a character `χ : G →* ℂ`, the vectors `v` of the ground space with
`P_g v = χ(g) v` for every `g`. The **supercell** is the intersection of the kernels of the
characters whose sector is nonzero. Its elements are exactly the `g` with `P_g v = v` for every
ground vector `v`, the property that lines 1626–1630 derive for the translations by whole
supercells. This supplies the subgroup assumed in `TranslationSupercell.lean`.

## Main results

* `TNLean.Lattice.momentumSector`: the vectors of the ground space with momentum `χ`.
* `TNLean.Lattice.iSup_momentumSector`: the momentum sectors span the ground space.
* `TNLean.Lattice.supercell`: the intersection of the kernels of the characters with a nonzero
  sector.
* `TNLean.Lattice.mem_supercell_iff`: `g` lies in the supercell exactly when `P_g` leaves every
  ground vector unchanged.
* `TNLean.Lattice.sitePermMatrix_mulVec_eq_of_mem_supercell`: the hypothesis on the subgroup in
  the theorems of `TranslationSupercell.lean`, for the supercell.

## Proof

The site permutations have finite order, so each `P_g` is semisimple on the ground space, which
they leave invariant. Commuting semisimple operators on a finite-dimensional complex space are
simultaneously diagonalizable, so the ground space is the sum of the joint eigenspaces
`⋂_g ker(P_g - χ(g))` over functions `χ : G → ℂ`. On a nonzero joint eigenspace `χ` is
multiplicative, because `P_{gh} = P_g P_h`, so it is a character.
-/

open Matrix Module.End

namespace TNLean.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [CommGroup G] [MulAction G V]
  {q : ℕ}

private theorem toEuclideanLin_apply_eq (A : Matrix (V → Fin q) (V → Fin q) ℂ)
    (v : EuclideanSpace ℂ (V → Fin q)) :
    toEuclideanLin A v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := rfl

theorem toEuclideanLin_sitePermMatrix_mul (g h : G) (v : EuclideanSpace ℂ (V → Fin q)) :
    toEuclideanLin (sitePermMatrix q (g * h)) v =
      toEuclideanLin (sitePermMatrix q g) (toEuclideanLin (sitePermMatrix q h) v) := by
  simp [toEuclideanLin_apply_eq, sitePermMatrix_mul, mulVec_mulVec]

theorem toEuclideanLin_sitePermMatrix_one (v : EuclideanSpace ℂ (V → Fin q)) :
    toEuclideanLin (sitePermMatrix (V := V) q (1 : G)) v = v := by
  rw [toEuclideanLin_apply_eq]
  simp only [sitePermMatrix, map_one, one_mulVec, WithLp.toLp_ofLp]

/-- An invariant `H` has its ground space mapped into itself by every site permutation. -/
theorem mapsTo_groundEigenspace_sitePermMatrix {H : Matrix (V → Fin q) (V → Fin q) ℂ}
    (hInv : IsSiteInvariant G q H) (E₀ : ℝ) (g : G) :
    Set.MapsTo (toEuclideanLin (sitePermMatrix (V := V) q g)) (groundEigenspace H E₀ : Set _)
      (groundEigenspace H E₀ : Set _) := fun v hv ↦ by
  rw [SetLike.mem_coe, mem_groundEigenspace_iff] at hv ⊢
  rw [toEuclideanLin_apply_eq, WithLp.ofLp_toLp, mulVec_mulVec, ← (hInv g).eq, ← mulVec_mulVec,
    hv, mulVec_smul]

variable (G q) in
/-- **The momentum sector** of the ground space of `H` at energy `E₀` for a character
`χ : G →* ℂ`: the ground vectors `v` with `P_g v = χ(g) v` for every `g`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1613–1618, ground states that are eigenvectors
of the translations with momentum `k_a`, for which `χ(x) = e^{i k_a · x}`. -/
noncomputable def momentumSector (H : Matrix (V → Fin q) (V → Fin q) ℂ) (E₀ : ℝ)
    (χ : G →* ℂ) : Submodule ℂ (EuclideanSpace ℂ (V → Fin q)) :=
  groundEigenspace H E₀ ⊓ ⨅ g, eigenspace (toEuclideanLin (sitePermMatrix q g)) (χ g)

theorem momentumSector_le_groundEigenspace (H : Matrix (V → Fin q) (V → Fin q) ℂ) (E₀ : ℝ)
    (χ : G →* ℂ) : momentumSector G q H E₀ χ ≤ groundEigenspace H E₀ :=
  inf_le_left

theorem toEuclideanLin_sitePermMatrix_of_mem_momentumSector
    {H : Matrix (V → Fin q) (V → Fin q) ℂ} {E₀ : ℝ} {χ : G →* ℂ}
    {v : EuclideanSpace ℂ (V → Fin q)} (hv : v ∈ momentumSector G q H E₀ χ) (g : G) :
    toEuclideanLin (sitePermMatrix q g) v = χ g • v :=
  mem_eigenspace_iff.mp (Submodule.mem_iInf _ |>.mp hv.2 g)

/-- A site permutation has finite order on the configurations. -/
theorem exists_pow_sitePermMatrix_eq_one (g : G) :
    ∃ N : ℕ, 0 < N ∧ sitePermMatrix (V := V) q g ^ N = 1 := by
  let := arrowAction (G := G) (A := V) (B := Fin q)
  set σ := MulAction.toPermHom G (V → Fin q) g
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  simp only [sitePermMatrix, σ, ← map_pow, pow_orderOf_eq_one, map_one]

/-- **The momentum sectors span the ground space.** For an abelian group acting on the sites and
an invariant `H`, every ground vector is a sum of ground vectors with definite momentum.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1613–1618: "we can pick the ground
states to be eigenvectors of the translation operators". -/
theorem iSup_momentumSector {H : Matrix (V → Fin q) (V → Fin q) ℂ}
    (hInv : IsSiteInvariant G q H) (E₀ : ℝ) :
    ⨆ χ : G →* ℂ, momentumSector G q H E₀ χ = groundEigenspace H E₀ := by
  set K := groundEigenspace H E₀
  let R : G → Module.End ℂ K := fun g ↦
    (toEuclideanLin (sitePermMatrix q g)).restrict
      (mapsTo_groundEigenspace_sitePermMatrix hInv E₀ g)
  have hR (g : G) (v : K) : (R g v : EuclideanSpace ℂ (V → Fin q)) =
      toEuclideanLin (sitePermMatrix q g) v := rfl
  have hRmul (g h : G) (v : K) : R (g * h) v = R g (R h v) := by
    ext1; simp only [hR, toEuclideanLin_sitePermMatrix_mul]
  have hcomm : Pairwise fun g h ↦ Commute (R g) (R h) := fun g h _ ↦
    LinearMap.ext fun v ↦ by
      change R g (R h v) = R h (R g v)
      rw [← hRmul, ← hRmul, mul_comm]
  have hss (g : G) : Module.End.IsFinitelySemisimple (R g) := by
    obtain ⟨N, hN, hpow⟩ := exists_pow_sitePermMatrix_eq_one (V := V) (q := q) g
    refine (isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X ^ N - 1) ?_ ?_)
      |>.isFinitelySemisimple
    · exact (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hN.ne') one_ne_zero).squarefree
    · have hRpow (n : ℕ) (v : K) : ((R g ^ n) v : EuclideanSpace ℂ (V → Fin q)) =
          toEuclideanLin (sitePermMatrix q g ^ n) v := by
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, hR, ih, pow_succ', toEuclideanLin_apply_eq,
            toEuclideanLin_apply_eq, toEuclideanLin_apply_eq, WithLp.ofLp_toLp, mulVec_mulVec]
      have hRN : R g ^ N = 1 := LinearMap.ext fun v ↦ Subtype.ext <| by
        rw [hRpow, hpow, toEuclideanLin_apply_eq, one_mulVec, WithLp.toLp_ofLp]; rfl
      simp [hRN]
  have htop : ⨆ χ : G → ℂ, ⨅ g, eigenspace (R g) (χ g) = ⊤ := by
    have := iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute R hcomm
      fun g ↦ iSup_maxGenEigenspace_eq_top (R g)
    simpa only [IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace (hss _)] using this
  refine le_antisymm (iSup_le fun χ ↦ momentumSector_le_groundEigenspace H E₀ χ) ?_
  -- every joint eigenspace of the restrictions lies in a momentum sector
  have hjoint (χ : G → ℂ) :
      (⨅ g, eigenspace (R g) (χ g)).map K.subtype ≤ ⨆ χ : G →* ℂ, momentumSector G q H E₀ χ := by
    by_cases hbot : ⨅ g, eigenspace (R g) (χ g) = ⊥
    · simp [hbot]
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hwg (g : G) : R g w = χ g • w := mem_eigenspace_iff.mp (Submodule.mem_iInf _ |>.mp hw g)
    have hmul (g h : G) : χ (g * h) = χ g * χ h := by
      have := hRmul g h w
      rw [hwg, hwg, map_smul, hwg, smul_smul, mul_comm (χ h)] at this
      exact smul_left_injective ℂ hw0 this
    have hone : χ 1 = 1 := by
      have : R 1 w = w := by ext1; simp [hR]
      rw [hwg] at this
      exact smul_left_injective ℂ hw0 (this.trans (one_smul ℂ w).symm)
    let χ' : G →* ℂ := ⟨⟨χ, hone⟩, hmul⟩
    refine le_trans ?_ (le_iSup _ χ')
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, Submodule.mem_iInf _ |>.mpr fun g ↦ mem_eigenspace_iff.mpr ?_⟩
    have := mem_eigenspace_iff.mp (Submodule.mem_iInf _ |>.mp hu g)
    simpa [hR, χ'] using congrArg Subtype.val this
  calc K = (⊤ : Submodule ℂ K).map K.subtype := by simp
    _ = (⨆ χ : G → ℂ, ⨅ g, eigenspace (R g) (χ g)).map K.subtype := by rw [htop]
    _ ≤ _ := by rw [Submodule.map_iSup]; exact iSup_le hjoint

variable (G q) in
/-- **The supercell**: the elements of `G` on which every character with a nonzero momentum
sector of the ground space is trivial. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1626–1630, the translations by whole supercells, which leave every ground state unchanged
(`mem_supercell_iff`). -/
noncomputable def supercell (H : Matrix (V → Fin q) (V → Fin q) ℂ) (E₀ : ℝ) : Subgroup G :=
  ⨅ (χ : G →* ℂ) (_ : momentumSector G q H E₀ χ ≠ ⊥), χ.ker

/-- **The supercell fixes the ground space.** For an abelian group acting on the sites and an
invariant `H`, `g` lies in the supercell exactly when `P_g v = v` for every ground vector `v`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1626–1630: "all of the `n` ground
states are unchanged by translation by a supercell". -/
theorem mem_supercell_iff {H : Matrix (V → Fin q) (V → Fin q) ℂ}
    (hInv : IsSiteInvariant G q H) {E₀ : ℝ} {g : G} :
    g ∈ supercell G q H E₀ ↔
      ∀ v ∈ groundEigenspace H E₀, toEuclideanLin (sitePermMatrix q g) v = v := by
  simp only [supercell, Subgroup.mem_iInf, MonoidHom.mem_ker]
  constructor
  · intro hg v hv
    rw [← iSup_momentumSector hInv E₀] at hv
    induction hv using Submodule.iSup_induction' with
    | mem χ v hv =>
      by_cases hbot : momentumSector G q H E₀ χ = ⊥
      · rw [hbot, Submodule.mem_bot] at hv; simp [hv]
      · rw [toEuclideanLin_sitePermMatrix_of_mem_momentumSector hv, hg χ hbot, one_smul]
    | zero => simp
    | add v w _ _ hv hw => rw [map_add, hv, hw]
  · intro hg χ hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have := (toEuclideanLin_sitePermMatrix_of_mem_momentumSector hv g).symm.trans
      (hg v (momentumSector_le_groundEigenspace H E₀ χ hv))
    exact smul_left_injective ℂ hv0 (this.trans (one_smul ℂ v).symm)

/-- The supercell satisfies the hypothesis on the subgroup in
`groundCompression_sitePermMatrix_conj`, `groundCompression_commutator_eq_of_mem_supercell` and
`norm_groundCompression_commutator_le_of_mem_supercell`. -/
theorem sitePermMatrix_mulVec_eq_of_mem_supercell {H : Matrix (V → Fin q) (V → Fin q) ℂ}
    (hInv : IsSiteInvariant G q H) {E₀ : ℝ} {g : G} (hg : g ∈ supercell G q H E₀)
    (v : EuclideanSpace ℂ (V → Fin q)) (hv : v ∈ groundEigenspace H E₀) :
    sitePermMatrix q g *ᵥ WithLp.ofLp v = WithLp.ofLp v := by
  simpa [toEuclideanLin_apply_eq] using congrArg WithLp.ofLp ((mem_supercell_iff hInv).mp hg v hv)

end TNLean.Lattice
