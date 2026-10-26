/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Execution.Unitary

/-!
# Actual full retained blocks of each native adder instruction

The operator is extracted from the existing compiled instruction: native
unitary, physical H/MZ/reset, or the Z selected by its actual caller Store.
The execution equation retains all original Store/history overwrite fibers
and every off-diagonal entry beside an arbitrary reference
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The exact retained physical operator selected on the actual incoming Store. -/
def actualKraus (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (Reference : Register)
    (instruction : Instruction encoding records) (store : Store ctx) :
    instruction.PhysicalOutcome physical sameWires →
      HilbertOperator (Register.prod ctx.register Reference) :=
  match instruction with
  | .native gates => fun _ => UnitaryOperator.prodTensor
      ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (EncodedBit.GateSpec.programList physical oracles gates)).matrix environment)
      (1 : UnitaryOperator Reference)
  | .vent target _ => fun outcome =>
      EncodedBit.MeasuredUncompute.placedKraus target physical ctx sameWires
        environment outcome Reference
  | .phase target record => fun _ => UnitaryOperator.prodTensor
      ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (phaseProgram physical target
          (store.read (.storage (output record).toCStorageRef)).toFin)).matrix environment)
      (1 : UnitaryOperator Reference)

/-- Chronological retained product; every phase reads the real intermediate caller Store. -/
def wordActualKraus (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (Reference : Register) :
    (word : List (Instruction encoding records)) → Store ctx →
      WordOutcomes physical sameWires word →
        HilbertOperator (Register.prod ctx.register Reference)
  | [], _, _ => 1
  | instruction :: rest, store, outcomes =>
      let first := instruction.actualRecord (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output store outcomes.1
      wordActualKraus physical sameWires output environment Reference rest first.1 outcomes.2 *
        instruction.actualKraus physical sameWires output environment Reference store outcomes.1

/-- Lift the actual chronological Store and Path without changing hidden state or old history. -/
def actualHistoryRecord (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records) {History : Type}
    (entry : Store ctx × (services.HiddenState × History))
    (outcome : instruction.PhysicalOutcome physical sameWires) :
    Store ctx × (services.HiddenState × (History ×
      (instruction.circuit (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output).Path)) :=
  let result := instruction.actualRecord (oracles := oracles) (operations := operations)
    (services := services) physical sameWires output entry.1 outcome
  (result.1, (entry.2.1, (entry.2.2, result.2)))

/-- The same actual interpreter gives every complete retained block of one instruction. -/
lemma circuit_block_matrix (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (instruction.circuit (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output).Path)))
    (left right : (Register.prod ctx.register Reference).Index) :
    (((instruction.circuit physical sameWires output).execute environment Reference state).block
      result).matrix left right =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : instruction.PhysicalOutcome physical sameWires,
          if instruction.actualHistoryRecord (oracles := oracles) (operations := operations)
              (services := services) physical sameWires output original outcome = result then
            (instruction.actualKraus physical sameWires output environment.quantum Reference
                original.1 outcome * (state.block original).matrix *
              (instruction.actualKraus physical sameWires output environment.quantum Reference
                original.1 outcome).conjTranspose) left right
          else 0 := by
  cases instruction with
  | native gates =>
      change Store ctx × (services.HiddenState × (History × Unit)) at result
      let program := unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (EncodedBit.GateSpec.programList physical oracles gates)
      have actual := congrArg
        (fun matrix : HilbertOperator (Register.prod ctx.register Reference) => matrix left right)
        (native_matrix program environment state result)
      simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply] at actual
      refine actual.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      let : Unique (PhysicalOutcome physical sameWires
        (Instruction.native gates : Instruction encoding records)) := inferInstanceAs (Unique Unit)
      simp only [Fintype.sum_unique]
      have sameRecord : actualHistoryRecord (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output (.native gates) original default =
          (original.1, (original.2.1, (original.2.2, ()))) := rfl
      by_cases selected : (original.1, (original.2.1, (original.2.2, ()))) = result
      · have actualSelected := sameRecord.trans selected
        simp only [if_pos selected, if_pos actualSelected]
        rfl
      · have actualNotSelected : ¬ actualHistoryRecord (oracles := oracles)
            (operations := operations) (services := services) physical sameWires output
            (.native gates) original default = result :=
          fun actualSelected => selected (sameRecord.symm.trans actualSelected)
        simp only [if_neg selected, if_neg actualNotSelected]
  | vent target record =>
      exact EncodedBit.MeasuredUncompute.placedCircuit_block_matrix target physical ctx
        sameWires (finiteOutput
          (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
          (output record)) environment state result left right
  | phase target record =>
      change Store ctx × (services.HiddenState ×
        (History × (Σ _ : (CShape.finite 2).Value, Unit))) at result
      let input := CInputRef.storage (output record).toCStorageRef
      let program := fun value : (CShape.finite 2).Value =>
        unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (phaseProgram (oracles := oracles) physical target value.toFin)
      have actual := congrArg
        (fun matrix : HilbertOperator (Register.prod ctx.register Reference) => matrix left right)
        (selected_matrix input program environment state result)
      simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply] at actual
      refine actual.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      let : Unique (PhysicalOutcome physical sameWires
        (Instruction.phase target record : Instruction encoding records)) :=
        inferInstanceAs (Unique Unit)
      simp only [Fintype.sum_unique]
      have sameRecord : actualHistoryRecord (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output (.phase target record) original default =
          (original.1, (original.2.1, (original.2.2, ⟨original.1.read input, ()⟩))) := rfl
      by_cases selected :
          (original.1, (original.2.1, (original.2.2, ⟨original.1.read input, ()⟩))) = result
      · have actualSelected := sameRecord.trans selected
        simp only [if_pos selected, if_pos actualSelected]
        rfl
      · have actualNotSelected : ¬ actualHistoryRecord (oracles := oracles)
            (operations := operations) (services := services) physical sameWires output
            (.phase target record) original default = result :=
          fun actualSelected => selected (sameRecord.symm.trans actualSelected)
        simp only [if_neg selected, if_neg actualNotSelected]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
