import TNLean.MPS.Examples.PeriodicFullRingPhase

/-!
# Periodic String Order regression checks

These checks retain the zero-length insertion, actual periodic norm limit,
and a non-Hermitian fixed observable in the thermodynamic-limit statements.
The imported example also tests a nonreal full-ring phase and nonconvergence.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

/-- A zero-length middle string inserts the identity, independently of the
physical twist or canonical assumptions. -/
example {d D : ℕ} (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ) :
    physicalObservableTransfer A 0 (Matrix.finKronecker fun _ : Fin 0 => u) =
      LinearMap.id := by
  simpa only [twistedTransferIter_zero] using
    physicalObservableTransfer_finKronecker_const A u 0

/-- The periodic norm limit uses the existing canonical example without an
extra all-length nonvanishing premise. -/
example : Tendsto (fun L : ℕ =>
    ⟪mpvState stringPhaseTensor L, mpvState stringPhaseTensor L⟫_ℂ)
    atTop (nhds (1 : ℂ)) := by
  exact pureCanonical_mpvState_inner_self_tendsto_one stringPhaseTensor
    ((1 / 2 : ℂ) • 1) stringPhaseTensor_canonical.1
    stringPhaseTensor_canonical.2.1 stringPhaseTensor_canonical.2.2
    stringPhaseTensor_unital stringPhaseTensor_pure

/-- A non-Hermitian matrix unit is admitted as a fixed physical observable;
the thermodynamic bridge requires no Hermitian-observable hypothesis. -/
example :
    Tendsto
      (fun n : ℕ => mpvExpectation stringPhaseTensor (1 + n)
        (appendObservable
          (fun τ σ : Fin 1 → Fin 4 =>
            (Matrix.single (0 : Fin 4) 1 (1 : ℂ)) (τ 0) (σ 0))
          (1 : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℂ)))
      atTop (nhds (Matrix.trace (((1 / 2 : ℂ) • 1) *
        physicalObservableTransfer stringPhaseTensor 1
          (fun τ σ : Fin 1 → Fin 4 =>
            (Matrix.single (0 : Fin 4) 1 (1 : ℂ)) (τ 0) (σ 0)) 1))) := by
  exact pureCanonical_mpvExpectation_appendObservable_tendsto stringPhaseTensor
    ((1 / 2 : ℂ) • 1) stringPhaseTensor_canonical.1
    stringPhaseTensor_canonical.2.1 stringPhaseTensor_canonical.2.2
    stringPhaseTensor_unital stringPhaseTensor_pure 1 _

end MPSTensor

section AxiomChecks
set_option linter.hashCommand false

/--
info: 'MPSTensor.physicalObservableTransfer_finKronecker_const'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.physicalObservableTransfer_finKronecker_const

/--
info: 'MPSTensor.pureCanonical_mpvState_inner_self_tendsto_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_mpvState_inner_self_tendsto_one

/--
info: 'MPSTensor.pureCanonical_eventually_mpvState_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_eventually_mpvState_ne_zero

/--
info: 'MPSTensor.pureCanonical_mpvExpectation_appendObservable_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_mpvExpectation_appendObservable_tendsto

/--
info: 'MPSTensor.pureCanonical_mpvExpectation_string_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_mpvExpectation_string_tendsto

/--
info: 'MPSTensor.mpvExpectation_finKronecker_const_eq_trace_div'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.mpvExpectation_finKronecker_const_eq_trace_div

/--
info: 'MPSTensor.mpvExpectation_finKronecker_const_eq_phase_pow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.mpvExpectation_finKronecker_const_eq_phase_pow

/--
info: 'MPSTensor.pureCanonical_mpvExpectation_fullRing_not_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_mpvExpectation_fullRing_not_tendsto

/--
info: 'MPSTensor.pureCanonical_mpvExpectation_fullRing_dichotomy'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_mpvExpectation_fullRing_dichotomy

/--
info: 'MPSTensor.stringPhaseTensor_fullRing_I_eq_pow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.stringPhaseTensor_fullRing_I_eq_pow

/--
info: 'MPSTensor.stringPhaseTensor_fullRing_neg_one_not_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.stringPhaseTensor_fullRing_neg_one_not_tendsto

end AxiomChecks
