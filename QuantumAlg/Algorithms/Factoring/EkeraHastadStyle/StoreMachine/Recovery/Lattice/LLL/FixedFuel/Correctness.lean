/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.SecondStep

/-!
# Actual fixed-fuel LLL correctness

The actual two-bit phase encoding selects exactly the original mathematical
LLL step, including terminal identity. Induction over actual repeated stores
establishes the original invariant for the original mathematical fixed-fuel run.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem bit_value (actual : CShape.Value .bit) (expected : Bool)
    (equal : actual.toBool = expected) : actual = .bit expected := by
  cases actual with
  | bit value => exact congrArg CShape.Value.bit equal

/-- The actual terminal and phase reads select exactly one original mathematical LLL step. -/
theorem stepInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (input : NumberTheory.IntegerBasis3) (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) :
    StoreInvariant refs input (step refs store).1 (NumberTheory.lllStep3 state) := by
  have represented := invariant.phase
  change StoreInvariant refs input
    (stepArmStep refs (store.read (.storage refs.machine.done.toCStorageRef)) store).1 _
  cases phase : state.phase with
  | first =>
    rw [phase] at represented
    have doneRead := bit_value _ false represented.2
    have pairRead := bit_value _ false represented.1
    rw [doneRead]
    change StoreInvariant refs input
      (nonDoneArmStep refs (store.read (.storage refs.machine.secondPhase.toCStorageRef)) store).1 _
    rw [pairRead]
    exact firstStepInto_correct refs separation input store state invariant phase
  | second =>
    rw [phase] at represented
    have doneRead := bit_value _ false represented.2
    have pairRead := bit_value _ true represented.1
    rw [doneRead]
    change StoreInvariant refs input
      (nonDoneArmStep refs (store.read (.storage refs.machine.secondPhase.toCStorageRef)) store).1 _
    rw [pairRead]
    exact secondStepInto_correct refs separation input store state invariant phase
  | done =>
    rw [phase] at represented
    have doneRead := bit_value _ true represented.2
    rw [doneRead]
    have mathematical := NumberTheory.lllStep3_done_basis_phase state phase
    refine ⟨?_, ?_, ?_, invariant.bounded.step, invariant.capacity,
      LatticeStepBounds.stepFits_of_boundedFrom invariant.bounded.step invariant.capacity⟩
    · rw [mathematical.1]
      exact invariant.basis
    · rw [mathematical.2]
      exact represented
    · rw [mathematical.1]
      exact invariant.gram

/-- Every finite actual execution realizes the original mathematical fixed-fuel run invariant. -/
theorem fixedFuelInto_correct (fuel : Nat) (refs : Refs ctx width) (separation : Separation refs)
    (input : NumberTheory.IntegerBasis3) (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) :
    StoreInvariant refs input (fixedFuelStep fuel refs store).1
      (NumberTheory.lllRun3 fuel state) := by
  change StoreInvariant refs input ((fun current => (step refs current).1)^[fuel] store) _
  induction fuel generalizing store state with
  | zero => exact invariant
  | succ fuel ih =>
    rw [Function.iterate_succ_apply, NumberTheory.lllRun3]
    exact ih _ _ (stepInto_correct refs separation input store state invariant)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
