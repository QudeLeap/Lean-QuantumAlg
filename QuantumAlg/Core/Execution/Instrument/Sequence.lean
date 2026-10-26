/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Recorded
import all QuantumAlg.Core.Execution.Instrument.Recorded

/-!
# Sequential actual instruments with complete service records

The second component reads the first component's real returned Store and
service state. Both actual Paths remain in their original order. The finite
fiber composition retains overwrites and every incoming History, for an
arbitrary external Reference. This certificate changes no instruction.
-/

@[expose] public section

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {FirstOutcome LastOutcome : Type}
  [Fintype FirstOutcome] [Fintype LastOutcome]
  {first last : Circuit (.quantum gates oracles operations services) ctx ctx true}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- The full real first output supplies the second component's input record. -/
def sourceRecordedSequenceRecord
    (head : RecordedInstrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment)
    (original : Store ctx × services.HiddenState) (outcomes : FirstOutcome × LastOutcome) :
    (Store ctx × services.HiddenState) × (first.seq last).Path :=
  let middle := head.record original outcomes.1
  let final := tail.record middle.1 outcomes.2
  (final.1, (middle.2, final.2))

/-- Actual sequential execution composes complete returned records and the same local Kraus rows. -/
def RecordedInstrument.seq (head : RecordedInstrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment) :
    RecordedInstrument (first.seq last) (FirstOutcome × LastOutcome) environment where
  record := sourceRecordedSequenceRecord head tail
  operator original outcomes :=
    tail.operator (head.record original outcomes.1).1 outcomes.2 *
      head.operator original outcomes.1
  blocks := by
    intro Reference History _ state result
    let middle := first.execute environment Reference state
    let final := last.execute environment Reference middle
    let wrap := fun entry : Store ctx ×
        (services.HiddenState × ((History × first.Path) × last.Path)) =>
      (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2))))
    have execution : (first.seq last).execute environment Reference state =
        final.mapClassical wrap := by
      rw [Circuit.execute_seq]
      exact ExecutionState.executionState_mapClassical_congr final rfl
    refine (congrArg (fun output : State ctx Reference
      (services.HiddenState × (History × (first.seq last).Path)) =>
        (output.block result).matrix) execution).trans ?_
    have remapped := mapClassical_retained_matrix final
      (sourceFullRetainedRecord tail.record)
      (fun original outcome =>
        referenceLift Reference (tail.operator (original.1, original.2.1) outcome) *
          (middle.block original).matrix *
            (referenceLift Reference
              (tail.operator (original.1, original.2.1) outcome)).conjTranspose)
      (by
        intro selected
        exact (tail.blocks Reference middle selected).trans (sum_condition_decisions _ _ _ _))
      wrap result
    refine remapped.trans ?_
    dsimp only [middle]
    simp_rw [head.blocks Reference state]
    have composed := composeRetainedBlocks
      (sourceFullRetainedRecord head.record)
      (fun original outcome => wrap (sourceFullRetainedRecord tail.record original outcome))
      (fun original outcome =>
        referenceLift Reference (head.operator (original.1, original.2.1) outcome) *
          (state.block original).matrix *
            (referenceLift Reference
              (head.operator (original.1, original.2.1) outcome)).conjTranspose)
      (fun original outcome =>
        referenceLift Reference (tail.operator (original.1, original.2.1) outcome)) result
    refine composed.trans ?_
    apply Finset.sum_congr rfl
    intro original _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro firstOutcome _
    apply Finset.sum_congr rfl
    intro lastOutcome _
    have sameRecord : wrap (sourceFullRetainedRecord tail.record
        (sourceFullRetainedRecord head.record original firstOutcome) lastOutcome) =
        sourceFullRetainedRecord (sourceRecordedSequenceRecord head tail)
          original (firstOutcome, lastOutcome) := rfl
    rw [sameRecord]
    by_cases selected : sourceFullRetainedRecord
        (sourceRecordedSequenceRecord head tail) original (firstOutcome, lastOutcome) = result
    · rw [if_pos selected, if_pos selected]
      simp only [sourceFullRetainedRecord, referenceLift_mul,
        Matrix.conjTranspose_mul, mul_assoc]
    · rw [if_neg selected, if_neg selected]

end

end QuantumAlg.Execution
