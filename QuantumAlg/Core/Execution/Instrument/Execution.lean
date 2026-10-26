/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Composition.Record

public import QuantumAlg.Core.Execution.Instrument.Remap

import all QuantumAlg.Core.Execution.Instrument.Remap
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Sequential actual circuits with retained instrument blocks

Both premises concern the existing components' actual interpreter equations.
The second physical operator reads the real first output Store. The theorem
retains the full chronological Path, hidden state, overwritten Store fibers
and arbitrary external reference. It introduces no instrument constructor.
-/

@[expose] public section

namespace QuantumAlg.Execution.Instrument

noncomputable section

open Execution
open scoped BigOperators

attribute [local instance] Classical.decEq

variable {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {gates : GateModel}
  {ctx : RuntimeCtx .quantum} {allowAllocation : Bool}

/-- The actual component Store and Path retain old history and persistent hidden state. -/
def retainedRecord {Path Outcome History : Type}
    (record : Store ctx → Outcome → Store ctx × Path)
    (entry : Store ctx × (services.HiddenState × History)) (outcome : Outcome) :
    Store ctx × (services.HiddenState × (History × Path)) :=
  let next := record entry.1 outcome
  (next.1, (entry.2.1, (entry.2.2, next.2)))

/-- The second retained outcome is evaluated on the first component's actual Store. -/
def sequenceRetainedRecord {FirstOutcome SecondOutcome : Type}
    (first second : Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation)
    (firstRecord : Store ctx → FirstOutcome → Store ctx × first.Path)
    (secondRecord : Store ctx → SecondOutcome → Store ctx × second.Path)
    (store : Store ctx) (firstOutcome : FirstOutcome) (secondOutcome : SecondOutcome) :
    Store ctx × (first.seq second).Path :=
  let head := firstRecord store firstOutcome
  let tail := secondRecord head.1 secondOutcome
  (tail.1, (head.2, tail.2))

/-- Proved full component block equations compose through the same actual sequential interpreter. -/
lemma execute_sequenceRetainedBlocks {FirstOutcome SecondOutcome : Type}
    [Fintype FirstOutcome] [Fintype SecondOutcome]
    (first second : Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation)
    (firstRecord : Store ctx → FirstOutcome → Store ctx × first.Path)
    (secondRecord : Store ctx → SecondOutcome → Store ctx × second.Path)
    (firstOperator : (Reference : Register) → Store ctx → FirstOutcome →
      HilbertOperator (Register.prod ctx.register Reference))
    (secondOperator : (Reference : Register) → Store ctx → SecondOutcome →
      HilbertOperator (Register.prod ctx.register Reference))
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)) result,
      ((first.execute environment Reference state).block result).matrix =
        ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : FirstOutcome,
          if retainedRecord firstRecord original outcome = result then
            firstOperator Reference original.1 outcome * (state.block original).matrix *
              (firstOperator Reference original.1 outcome).conjTranspose
          else 0)
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)) result,
      ((second.execute environment Reference state).block result).matrix =
        ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : SecondOutcome,
          if retainedRecord secondRecord original outcome = result then
            secondOperator Reference original.1 outcome * (state.block original).matrix *
              (secondOperator Reference original.1 outcome).conjTranspose
          else 0)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × (first.seq second).Path))) :
    (((first.seq second).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ firstOutcome : FirstOutcome, ∑ secondOutcome : SecondOutcome,
          if retainedRecord
              (fun store outcomes => sequenceRetainedRecord first second firstRecord secondRecord
                store outcomes.1 outcomes.2) original (firstOutcome, secondOutcome) = result then
            (secondOperator Reference (firstRecord original.1 firstOutcome).1 secondOutcome *
                firstOperator Reference original.1 firstOutcome) * (state.block original).matrix *
              (secondOperator Reference (firstRecord original.1 firstOutcome).1 secondOutcome *
                firstOperator Reference original.1 firstOutcome).conjTranspose
          else 0 := by
  let middle := first.execute environment Reference state
  let final := second.execute environment Reference middle
  let wrap : Store ctx × (services.HiddenState × ((History × first.Path) × second.Path)) →
      Store ctx × (services.HiddenState × (History × (first.seq second).Path)) :=
    fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2))))
  have actual : (first.seq second).execute environment Reference state =
      final.mapClassical wrap := by
    rw [Circuit.execute_seq]
    exact ExecutionState.executionState_mapClassical_congr final rfl
  refine (congrArg (fun executed : State ctx Reference
    (services.HiddenState × (History × (first.seq second).Path)) =>
      (executed.block result).matrix) actual).trans ?_
  have remapped := mapClassical_retained_matrix final
    (retainedRecord (services := services) secondRecord)
    (fun original outcome => secondOperator Reference original.1 outcome *
      (middle.block original).matrix *
        (secondOperator Reference original.1 outcome).conjTranspose)
    (by
      intro selected
      have proved := secondEquation Reference middle selected
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      split_ifs <;> simp_all) wrap result
  refine remapped.trans ?_
  dsimp only [middle]
  simp_rw [firstEquation Reference state]
  have composed := composeRetainedBlocks (retainedRecord (services := services) firstRecord)
    (fun original outcome =>
      wrap (retainedRecord (services := services) secondRecord original outcome))
    (fun original outcome => firstOperator Reference original.1 outcome *
      (state.block original).matrix * (firstOperator Reference original.1 outcome).conjTranspose)
    (fun original outcome => secondOperator Reference original.1 outcome) result
  simpa only [retainedRecord, sequenceRetainedRecord, wrap,
    Matrix.conjTranspose_mul, mul_assoc] using composed

end

end QuantumAlg.Execution.Instrument
