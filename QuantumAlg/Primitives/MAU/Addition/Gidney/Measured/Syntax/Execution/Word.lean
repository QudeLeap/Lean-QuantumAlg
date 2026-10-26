/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Execution
import all QuantumAlg.Core.Execution.Instrument.Execution

/-!
# Full actual retained blocks of the compiled measured instruction word

The induction follows the literal instruction compiler and the actual
sequential interpreter. Every physical measurement outcome, selected phase
path, original Store/history fiber and arbitrary reference remains explicit
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution EncodedBit.MeasuredUncompute
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

private lemma instruction_matrix (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result :
    (((instruction.circuit physical sameWires output).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : instruction.PhysicalOutcome physical sameWires,
          if Execution.Instrument.retainedRecord (instruction.actualRecord (oracles := oracles)
              (operations := operations) (services := services) physical sameWires output)
              original outcome = result then
            instruction.actualKraus physical sameWires output environment.quantum Reference
                original.1 outcome * (state.block original).matrix *
              (instruction.actualKraus physical sameWires output environment.quantum Reference
                original.1 outcome).conjTranspose
          else 0 := by
  ext left right
  have actual :=
    circuit_block_matrix physical sameWires output instruction environment state result left right
  refine actual.trans ?_
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  have sameRecord : Execution.Instrument.retainedRecord (instruction.actualRecord (oracles :=
    oracles)
      (operations := operations) (services := services) physical sameWires output)
      original outcome =
      instruction.actualHistoryRecord (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output original outcome := rfl
  by_cases selected : instruction.actualHistoryRecord (oracles := oracles)
      (operations := operations) (services := services) physical sameWires output
      original outcome = result
  · simp only [if_pos selected, if_pos (sameRecord.trans selected)]
  · have notSelected : ¬ Execution.Instrument.retainedRecord (instruction.actualRecord (oracles :=
    oracles)
        (operations := operations) (services := services) physical sameWires output)
        original outcome = result := fun hit => selected (sameRecord.symm.trans hit)
    simp only [if_neg selected, if_neg notSelected, Matrix.zero_apply]

/-- The same actual word executes exactly its chronological retained native operator products. -/
lemma wordCircuit_block_matrix (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment) :
    ∀ (word : List (Instruction encoding records)) (Reference : Register)
      {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)) result,
    (((wordCircuit physical sameWires output word).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcomes : WordOutcomes physical sameWires word,
          if Execution.Instrument.retainedRecord (wordActualRecord (oracles := oracles)
            (operations := operations)
              (services := services) physical sameWires output word) original outcomes = result then
            wordActualKraus (oracles := oracles) (operations := operations)
              (services := services) physical sameWires output environment.quantum Reference word
                original.1 outcomes * (state.block original).matrix *
              (wordActualKraus (oracles := oracles) (operations := operations)
              (services := services) physical sameWires output environment.quantum Reference word
                original.1 outcomes).conjTranspose
          else 0 := by
  intro word
  induction word with
  | nil =>
      intro Reference History _ state result
      change Store ctx × (services.HiddenState × (History × Unit)) at result
      let update : Store ctx × (services.HiddenState × History) →
          Store ctx × (services.HiddenState × (History × Unit)) :=
        fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))
      have actual :
          (wordCircuit (oracles := oracles) (operations := operations) (services := services)
            physical sameWires output []).execute environment Reference state =
          state.mapClassical update :=
        (Circuit.execute_id environment state).trans
          (ExecutionState.executionState_mapClassical_congr state rfl)
      refine (congrArg (fun final : State ctx Reference
        (services.HiddenState × (History × Unit)) => (final.block result).matrix) actual).trans ?_
      have pushed := ExecutionState.mapClassical_block_matrix state update result
      refine pushed.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      have card : Fintype.card
          (WordOutcomes physical sameWires ([] : List (Instruction encoding records))) = 1 := by
        change Fintype.card Unit = 1
        exact Fintype.card_unit
      let block : HilbertOperator (Register.prod ctx.register Reference) :=
        if update original = result then (state.block original).matrix else 0
      have constantSum :
          (∑ _outcomes : WordOutcomes physical sameWires
            ([] : List (Instruction encoding records)), block) = block := by
        rw [Finset.sum_const, Finset.card_univ, card, one_nsmul]
      refine constantSum.symm.trans ?_
      apply Finset.sum_congr rfl
      intro outcome _
      change Unit at outcome
      cases outcome
      have sameRecord : Execution.Instrument.retainedRecord
          (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
            physical sameWires output []) original () = update original := rfl
      by_cases selected : update original = result
      · have actualSelected := sameRecord.trans selected
        simp only [block, if_pos selected, if_pos actualSelected, wordActualKraus,
          Matrix.conjTranspose_one, one_mul, mul_one]
      · have actualNotSelected : ¬ Execution.Instrument.retainedRecord
            (wordActualRecord (oracles := oracles) (operations := operations)
              (services := services) physical sameWires output []) original () = result :=
          fun hit => selected (sameRecord.symm.trans hit)
        simp only [block, if_neg selected, if_neg actualNotSelected]
  | cons instruction rest ih =>
      intro Reference History _ state result
      change Store ctx × (services.HiddenState × (History ×
        ((instruction.circuit (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output).Path ×
          (wordCircuit (oracles := oracles) (operations := operations) (services := services)
            physical sameWires output rest).Path))) at result
      have actual := Execution.Instrument.execute_sequenceRetainedBlocks
        (instruction.circuit (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output)
        (wordCircuit (oracles := oracles) (operations := operations) (services := services)
          physical sameWires output rest)
        (instruction.actualRecord (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output)
        (wordActualRecord (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output rest)
        (fun reference store outcome =>
          instruction.actualKraus physical sameWires output environment.quantum reference
            store outcome)
        (fun reference store outcomes =>
          wordActualKraus (oracles := oracles) (operations := operations)
              (services := services) physical sameWires output environment.quantum reference
            rest store outcomes)
        environment
        (fun reference _ _ input selected => instruction_matrix physical sameWires output
          instruction environment input selected)
        (fun reference _ _ input selected => ih reference input selected)
        Reference state result
      refine actual.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      simp only [WordOutcomes, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro firstOutcome _
      apply Finset.sum_congr rfl
      intro secondOutcome _
      rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
