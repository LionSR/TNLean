import TNLean.PEPS.AreaLaw.Amplification.ComponentChannelOscillation

/-! Consumers for the full channel of a component-supported positive contraction. -/

open QuantumCircuit TNLean.PEPS.AreaLaw Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

-- Exact stabilization needs support alone, with no decay or positivity hypothesis.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x}) :
    ∃ N, ∀ n ≥ N, siteExpectation q (graphBall G a n) k = k ∧
      ∀ B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ,
        localRootChannel (graphBall G a n) k B = spectatorRootChannel k B :=
  exists_localRootChannel_graphBall_eq_of_component_support G a hk

-- Taking the actual errors gives a finite full-channel bound with no tail input.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B +
      2 * ∑ l ∈ (Finset.range (Finset.univ.sup (G.dist a) + 1)).filter
          (fun l : ℕ => G.edist a y ≤ l),
        localRootChannelShellBound (fun r => ‖k - siteExpectation q (graphBall G a r) k‖) l *
          ∑ z ∈ graphBall G a l, siteOscillation q z B :=
  siteOscillation_spectatorRootChannel_le_of_component_support G a hk₀ hk₁ hk _ _
    le_rfl (fun _ _ => le_rfl) y B

-- A disconnected observed site has no increment, for arbitrary non-Hermitian B.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    (y : ι) (hy : ¬G.Reachable a y)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B :=
  siteOscillation_spectatorRootChannel_le_of_edist_eq_top G a hk₀ hk₁ hk y
    (G.edist_eq_top_of_not_reachable hy) B

-- No hidden nonemptiness assumption is imposed on the spectator.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    (y : ι) (hy : G.edist a y = ⊤)
    (B : Matrix ((ι → Fin q) × Fin 0) ((ι → Fin q) × Fin 0) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B :=
  siteOscillation_spectatorRootChannel_le_of_edist_eq_top G a hk₀ hk₁ hk y hy B

-- Exact stabilization kills the first successor shell past the cutoff.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannelShell (graphBall G a) k (Finset.univ.sup (G.dist a) + 1) B = 0 :=
  localRootChannelShell_graphBall_succ_eq_zero_of_component_support G a hk le_rfl B

-- A one-site supported contraction on two isolated sites leaves the other oscillation bounded.
example {k : Matrix (Fin 2 → Fin q) (Fin 2 → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (hk : k ∈ supportedOperators q ({0} : Set (Fin 2)))
    (B : Matrix ((Fin 2 → Fin q) × Aux) ((Fin 2 → Fin q) × Aux) ℂ) :
    siteOscillation q 1 (spectatorRootChannel k B) ≤ siteOscillation q 1 B := by
  have hcomponent : {x : Fin 2 | (⊥ : SimpleGraph (Fin 2)).Reachable 0 x} = {0} := by
    ext x
    simp [eq_comm]
  apply siteOscillation_spectatorRootChannel_le_of_edist_eq_top
    (⊥ : SimpleGraph (Fin 2)) 0 hk₀ hk₁ (by rwa [hcomponent]) 1
  exact SimpleGraph.edist_eq_top_of_not_reachable (by simp)

-- A spectator-only observable may be non-Hermitian and still has zero physical oscillation.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    (y : ι) (C : Matrix Aux Aux ℂ) :
    siteOscillation q y
      (spectatorRootChannel k ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C)) = 0 := by
  apply le_antisymm _ (siteOscillation_nonneg y _)
  simpa only [siteOscillation_one_kronecker, Finset.sum_const_zero, mul_zero, add_zero] using
    siteOscillation_spectatorRootChannel_le_of_component_support G a hk₀ hk₁ hk
      (fun l => ‖k - siteExpectation q (graphBall G a l) k‖)
      (Finset.univ.sup (G.dist a)) le_rfl (fun _ _ => le_rfl) y
      ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C)

/--
info: 'TNLean.PEPS.AreaLaw.siteExpectation_graphBall_eq_of_component_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.siteExpectation_graphBall_eq_of_component_support

/--
info: 'TNLean.PEPS.AreaLaw.norm_sub_siteExpectation_graphBall_eq_zero_of_component_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_sub_siteExpectation_graphBall_eq_zero_of_component_support

/--
info: 'TNLean.PEPS.AreaLaw.localRootChannel_graphBall_eq_of_component_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.localRootChannel_graphBall_eq_of_component_support

/--
info: 'TNLean.PEPS.AreaLaw.exists_localRootChannel_graphBall_eq_of_component_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.exists_localRootChannel_graphBall_eq_of_component_support

/--
info: 'TNLean.PEPS.AreaLaw.localRootChannelShell_graphBall_succ_eq_zero_of_component_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.localRootChannelShell_graphBall_succ_eq_zero_of_component_support

/--
info: 'TNLean.PEPS.AreaLaw.siteOscillation_spectatorRootChannel_le_of_component_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.siteOscillation_spectatorRootChannel_le_of_component_support

/--
info: 'TNLean.PEPS.AreaLaw.siteOscillation_spectatorRootChannel_le_of_edist_eq_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.siteOscillation_spectatorRootChannel_le_of_edist_eq_top
