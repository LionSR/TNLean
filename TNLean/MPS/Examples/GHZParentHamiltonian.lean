/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# GHZ parent-Hamiltonian local ground space

This file records the two-site ground-space calculation for the GHZ tensor and
the periodic nearest-neighbour chain ground-space equation.

## References

* Fernández-González--Wolf--Sanz--Pérez-García 2012, arXiv:1210.6613,
  Section 3, lines 432--455.
* Cirac--Pérez-García--Schuch--Verstraete 2021, arXiv:2011.12127,
  lines 1194--1196 and line 2205.
-/

namespace MPSTensor

/-- The computational two-site vector \(\ket{ab}\) for the physical space
\((\mathbb C^2)^{\otimes 2}\). -/
def twoSiteKet (a b : Fin 2) : NSiteSpace 2 2 :=
  Pi.single (fun k : Fin 2 => if k = 0 then a else b) 1

/-- The computational basis vector \(\ket{a}^{\otimes N}\).
This is the constant product vector in the two-fold GHZ degeneracy,
arXiv:2011.12127, line 2205. -/
def constantKet (a : Fin 2) (N : ℕ) : NSiteSpace 2 N :=
  Pi.single (fun _ : Fin N => a) 1

private theorem ghz_groundSpaceMap_two
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    groundSpaceMap ghzTensor 2 X =
      X 0 0 • twoSiteKet 0 0 + X 1 1 • twoSiteKet 1 1 := by
  ext σ
  let a₀ : Fin 2 := σ 0
  let a₁ : Fin 2 := σ 1
  have hσ : σ = fun k : Fin 2 => if k = 0 then a₀ else a₁ := by
    ext k
    fin_cases k <;> simp [a₀, a₁]
  suffices hcalc : ∀ a b : Fin 2,
      groundSpaceMap ghzTensor 2 X (fun k : Fin 2 => if k = 0 then a else b) =
        (X 0 0 • twoSiteKet 0 0 + X 1 1 • twoSiteKet 1 1)
          (fun k : Fin 2 => if k = 0 then a else b) by
    rw [hσ]
    exact hcalc a₀ a₁
  intro a b
  fin_cases a <;> fin_cases b
  · have hne :
        (fun _ : Fin 2 => (0 : Fin 2)) ≠ (fun _ : Fin 2 => (1 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne]
  · have hne0 :
        (fun k : Fin 2 => if k = 0 then (0 : Fin 2) else (1 : Fin 2)) ≠
          (fun _ : Fin 2 => (0 : Fin 2)) := by
      decide
    have hne1 :
        (fun k : Fin 2 => if k = 0 then (0 : Fin 2) else (1 : Fin 2)) ≠
          (fun _ : Fin 2 => (1 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne0, hne1]
  · have hne0 :
        (fun k : Fin 2 => if k = 0 then (1 : Fin 2) else (0 : Fin 2)) ≠
          (fun _ : Fin 2 => (0 : Fin 2)) := by
      decide
    have hne1 :
        (fun k : Fin 2 => if k = 0 then (1 : Fin 2) else (0 : Fin 2)) ≠
          (fun _ : Fin 2 => (1 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne0, hne1]
  · have hne :
        (fun _ : Fin 2 => (1 : Fin 2)) ≠ (fun _ : Fin 2 => (0 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne]

/-- The local parent-space equation for the GHZ tensor is
\[
  \mathcal G_2(A_{\mathrm{GHZ}})
  =
  \operatorname{span}_{\mathbb C}\{\ket{00},\ket{11}\}.
\]
This is arXiv:1210.6613, lines 449--455. -/
theorem ghz_groundSpace_two_eq_span :
    groundSpace ghzTensor 2 =
      Submodule.span ℂ
        ({twoSiteKet 0 0, twoSiteKet 1 1} : Set (NSiteSpace 2 2)) := by
  apply le_antisymm
  · rintro ψ ⟨X, rfl⟩
    rw [ghz_groundSpaceMap_two]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro ψ hψ
    rw [groundSpace]
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
    rcases hψ with rfl | rfl
    · refine ⟨Matrix.diagonal (Pi.single (0 : Fin 2) 1), ?_⟩
      rw [ghz_groundSpaceMap_two]
      simp [twoSiteKet]
    · refine ⟨Matrix.diagonal (Pi.single (1 : Fin 2) 1), ?_⟩
      rw [ghz_groundSpaceMap_two]
      simp [twoSiteKet]

private lemma twoSiteKet_same_apply_mixed (c : Fin 2) {a b : Fin 2} (hab : a ≠ b) :
    twoSiteKet c c (fun k : Fin 2 => if k = 0 then a else b) = 0 := by
  have hne :
      (fun k : Fin 2 => if k = 0 then c else c) ≠
        (fun k : Fin 2 => if k = 0 then a else b) := by
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    apply hab
    exact h0.symm.trans h1
  rw [twoSiteKet, Pi.single_eq_of_ne hne.symm]

private lemma mem_ghz_two_span_apply_mixed {v : NSiteSpace 2 2}
    (hv : v ∈ Submodule.span ℂ
      ({twoSiteKet 0 0, twoSiteKet 1 1} : Set (NSiteSpace 2 2)))
    {a b : Fin 2} (hab : a ≠ b) :
    v (fun k : Fin 2 => if k = 0 then a else b) = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact twoSiteKet_same_apply_mixed 0 hab
      · exact twoSiteKet_same_apply_mixed 1 hab
  | zero => simp
  | add _ _ _ _ h₁ h₂ => rw [Pi.add_apply, h₁, h₂, add_zero]
  | smul c _ _ h => rw [Pi.smul_apply, h, smul_zero]

private lemma mem_ghz_two_span_of_apply_mixed_eq_zero {v : NSiteSpace 2 2}
    (hzero : ∀ {a b : Fin 2}, a ≠ b →
      v (fun k : Fin 2 => if k = 0 then a else b) = 0) :
    v ∈ Submodule.span ℂ
      ({twoSiteKet 0 0, twoSiteKet 1 1} : Set (NSiteSpace 2 2)) := by
  have hdecomp :
      v = v (fun _ : Fin 2 => (0 : Fin 2)) • twoSiteKet 0 0 +
        v (fun _ : Fin 2 => (1 : Fin 2)) • twoSiteKet 1 1 := by
    suffices hcalc : ∀ a₀ a₁ : Fin 2,
        v (fun k : Fin 2 => if k = 0 then a₀ else a₁) =
          (v (fun _ : Fin 2 => (0 : Fin 2)) • twoSiteKet 0 0 +
            v (fun _ : Fin 2 => (1 : Fin 2)) • twoSiteKet 1 1)
              (fun k : Fin 2 => if k = 0 then a₀ else a₁) by
      ext σ
      let a₀ : Fin 2 := σ 0
      let a₁ : Fin 2 := σ 1
      have hσ : σ = fun k : Fin 2 => if k = 0 then a₀ else a₁ := by
        ext k
        fin_cases k <;> simp [a₀, a₁]
      rw [hσ]
      exact hcalc a₀ a₁
    intro a₀ a₁
    fin_cases a₀ <;> fin_cases a₁
    · have hne :
          (fun _ : Fin 2 => (0 : Fin 2)) ≠ (fun _ : Fin 2 => (1 : Fin 2)) := by
        decide
      simp [twoSiteKet, hne]
    · have hmix : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
      have hne0 :
          (fun k : Fin 2 => if k = 0 then (0 : Fin 2) else (1 : Fin 2)) ≠
            (fun _ : Fin 2 => (0 : Fin 2)) := by
        decide
      have hne1 :
          (fun k : Fin 2 => if k = 0 then (0 : Fin 2) else (1 : Fin 2)) ≠
            (fun _ : Fin 2 => (1 : Fin 2)) := by
        decide
      simp [twoSiteKet, hzero hmix, hne0, hne1]
    · have hmix : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
      have hne0 :
          (fun k : Fin 2 => if k = 0 then (1 : Fin 2) else (0 : Fin 2)) ≠
            (fun _ : Fin 2 => (0 : Fin 2)) := by
        decide
      have hne1 :
          (fun k : Fin 2 => if k = 0 then (1 : Fin 2) else (0 : Fin 2)) ≠
            (fun _ : Fin 2 => (1 : Fin 2)) := by
        decide
      simp [twoSiteKet, hzero hmix, hne0, hne1]
    · have hne :
          (fun _ : Fin 2 => (1 : Fin 2)) ≠ (fun _ : Fin 2 => (0 : Fin 2)) := by
        decide
      simp [twoSiteKet, hne]
  rw [hdecomp]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private lemma extractWindow_two_eq {N : ℕ} (i : Fin N)
    (σ : Fin N → Fin 2) :
    extractWindow 2 i σ =
      fun k : Fin 2 => if k = 0 then σ i else σ (cyclicForwardSite i 1) := by
  ext k
  fin_cases k <;> simp [extractWindow, cyclicForwardSite, Nat.mod_eq_of_lt]

private lemma cyclicCfg_extractWindow_eq {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (σ : Fin N → Fin 2) :
    cyclicCfg (by omega : 0 < N) 2 i (extractWindow 2 i σ) σ = σ := by
  ext k
  simp only [cyclicCfg]
  by_cases hk : (k.val + N - i.val) % N < 2
  · rw [dif_pos hk]
    have hsite :
        k =
          ⟨(i.val + (k.val + N - i.val) % N) % N,
            Nat.mod_lt _ (by omega : 0 < N)⟩ :=
      eq_cyclic_site_of_offset_eq (N := N) (by omega : 0 < N)
        (i := i) (k := k) (r := (k.val + N - i.val) % N) rfl
    exact congrArg Fin.val (by simpa [extractWindow] using congrArg σ hsite.symm)
  · rw [dif_neg hk]

private lemma ghz_chainGroundSpace_apply_eq_zero_of_adjacent_ne {N : ℕ} (hN : 2 ≤ N)
    {ψ : NSiteSpace 2 N} (hψ : ψ ∈ chainGroundSpace ghzTensor 2 N)
    {σ : Fin N → Fin 2} {i : Fin N}
    (hne : σ i ≠ σ (cyclicForwardSite i 1)) :
    ψ σ = 0 := by
  have hNpos : 0 < N := by omega
  rw [chainGroundSpace, dif_pos ⟨hNpos, hN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  have hv := hψ i σ
  rw [ghz_groundSpace_two_eq_span] at hv
  have hzero := mem_ghz_two_span_apply_mixed hv hne
  have hwindow := extractWindow_two_eq i σ
  rw [← hwindow] at hzero
  have hcfg := cyclicCfg_extractWindow_eq hN i σ
  simpa [cyclicRestrictₗ_apply, hcfg] using hzero

private lemma exists_adjacent_ne_of_not_constant {N : ℕ} (hN : 2 ≤ N)
    (σ : Fin N → Fin 2)
    (hzero : σ ≠ fun _ : Fin N => (0 : Fin 2))
    (hone : σ ≠ fun _ : Fin N => (1 : Fin 2)) :
    ∃ i : Fin N, σ i ≠ σ (cyclicForwardSite i 1) := by
  by_contra hnone
  have hadj : ∀ i : Fin N, σ i = σ (cyclicForwardSite i 1) := by
    intro i
    by_contra hne
    exact hnone ⟨i, hne⟩
  let i₀ : Fin N := ⟨0, by omega⟩
  have hconst : ∀ n : ℕ, (hn : n < N) → σ ⟨n, hn⟩ = σ i₀ := by
    intro n
    induction n with
    | zero =>
        intro hn
        rfl
    | succ n ih =>
        intro hn
        have hnlt : n < N := by omega
        have hforward :
            cyclicForwardSite ⟨n, hnlt⟩ 1 = ⟨n + 1, hn⟩ := by
          ext
          simp [cyclicForwardSite, Nat.mod_eq_of_lt (by omega : n + 1 < N)]
        calc
          σ ⟨n + 1, hn⟩ = σ (cyclicForwardSite ⟨n, hnlt⟩ 1) := by rw [hforward]
          _ = σ ⟨n, hnlt⟩ := (hadj ⟨n, hnlt⟩).symm
          _ = σ i₀ := ih hnlt
  by_cases hbase : σ i₀ = 0
  · apply hzero
    ext k
    exact congrArg Fin.val ((hconst k.val k.isLt).trans hbase)
  · apply hone
    have hbase' : σ i₀ = 1 := by
      apply Fin.ext
      have hne : (σ i₀).val ≠ 0 := by
        intro hval
        exact hbase (Fin.ext hval)
      omega
    ext k
    exact congrArg Fin.val ((hconst k.val k.isLt).trans hbase')

/-- Each vector \(\ket{a}^{\otimes N}\) satisfies all GHZ two-site cyclic
constraints. -/
theorem constantKet_mem_ghz_chainGroundSpace {N : ℕ} (hN : 2 ≤ N) (a : Fin 2) :
    constantKet a N ∈ chainGroundSpace ghzTensor 2 N := by
  have hNpos : 0 < N := by omega
  rw [chainGroundSpace, dif_pos ⟨hNpos, hN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  rw [ghz_groundSpace_two_eq_span]
  apply mem_ghz_two_span_of_apply_mixed_eq_zero
  intro b c hbc
  rw [cyclicRestrictₗ_apply, constantKet]
  have hstart :
      cyclicCfg hNpos 2 i (fun k : Fin 2 => if k = 0 then b else c) τ i = b := by
    simp [cyclicCfg]
  have hnext :
      cyclicCfg hNpos 2 i (fun k : Fin 2 => if k = 0 then b else c) τ
        (cyclicForwardSite i 1) = c := by
    have hoff : ((cyclicForwardSite i 1).val + N - i.val) % N = 1 := by
      simp [cyclicForwardSite, offset_mod_eq i.isLt (by omega : 1 < N)]
    simp [cyclicCfg, hoff]
  have hne :
      cyclicCfg hNpos 2 i (fun k : Fin 2 => if k = 0 then b else c) τ ≠
        (fun _ : Fin N => a) := by
    intro hcfg
    have hb : b = a := by
      simpa [hstart] using congrFun hcfg i
    have hc : c = a := by
      simpa [hnext] using congrFun hcfg (cyclicForwardSite i 1)
    exact hbc (hb.trans hc.symm)
  rw [Pi.single_eq_of_ne hne]

/-- The periodic nearest-neighbour GHZ constraints have exactly the two constant
configuration vectors as their common kernel:
\[
  \mathcal G_{N,2}(A_{\mathrm{GHZ}})
  =
  \operatorname{span}_{\mathbb C}
    \{\ket{0}^{\otimes N},\ket{1}^{\otimes N}\}.
\]
This is the cyclic-window form of the two-fold degeneracy in
arXiv:2011.12127, line 2205. -/
theorem ghz_chainGroundSpace_two_eq_constant_span {N : ℕ} (hN : 2 ≤ N) :
    chainGroundSpace ghzTensor 2 N =
      Submodule.span ℂ
        ({constantKet 0 N, constantKet 1 N} : Set (NSiteSpace 2 N)) := by
  apply le_antisymm
  · intro ψ hψ
    let zeroCfg : Fin N → Fin 2 := fun _ => 0
    let oneCfg : Fin N → Fin 2 := fun _ => 1
    have hdecomp :
        ψ = ψ zeroCfg • constantKet 0 N + ψ oneCfg • constantKet 1 N := by
      ext σ
      by_cases hσzero : σ = zeroCfg
      · rw [hσzero]
        have hzero_ne_one : zeroCfg ≠ oneCfg := by
          intro h
          have hval := congrFun h ⟨0, by omega⟩
          simp [zeroCfg, oneCfg] at hval
        have hket0 : constantKet 0 N zeroCfg = 1 := by
          simp [constantKet, zeroCfg]
        have hket1 : constantKet 1 N zeroCfg = 0 := by
          rw [constantKet, Pi.single_eq_of_ne hzero_ne_one]
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hket0, hket1]
        simp
      · by_cases hσone : σ = oneCfg
        · rw [hσone]
          have hone_ne_zero : oneCfg ≠ zeroCfg := by
            intro h
            have hval := congrFun h ⟨0, by omega⟩
            simp [zeroCfg, oneCfg] at hval
          have hket0 : constantKet 0 N oneCfg = 0 := by
            rw [constantKet, Pi.single_eq_of_ne hone_ne_zero]
          have hket1 : constantKet 1 N oneCfg = 1 := by
            simp [constantKet, oneCfg]
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hket0, hket1]
          simp
        · obtain ⟨i, hi⟩ :=
            exists_adjacent_ne_of_not_constant hN σ hσzero hσone
          have hψσ :=
            ghz_chainGroundSpace_apply_eq_zero_of_adjacent_ne hN hψ hi
          have hket0 : constantKet 0 N σ = 0 := by
            rw [constantKet, Pi.single_eq_of_ne hσzero]
          have hket1 : constantKet 1 N σ = 0 := by
            rw [constantKet, Pi.single_eq_of_ne hσone]
          rw [hψσ, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hket0, hket1]
          simp
    rw [hdecomp]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro ψ hψ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
    rcases hψ with rfl | rfl
    · exact constantKet_mem_ghz_chainGroundSpace hN 0
    · exact constantKet_mem_ghz_chainGroundSpace hN 1

end MPSTensor
