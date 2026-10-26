/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Tail
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Execution.Word

/-!
# Complete actual retained instrument of the original measured exponent stage

Composition follows the existing circuit's H/arithmetic/feedback/H/MZ/reset
order. Its matrix product and record are derived from each actual interpreter
equation, including the real arithmetic output Store used by feedback
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev StageExecCtx := context base noQuantum m ell width

variable (modulus : BitVec width)
  (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
  (outputs : Fin bits → CWriteRef (StageExecCtx base noQuantum m ell width) (.finite 2))
  (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)

private abbrev middle :=
  (arithmetic base noQuantum m ell width wide modulus (unit ^ (2 ^ position.rev.val))).seq
    (stageTail base noQuantum m ell width inverse outputs position)

private def middleRecord (store : Store (StageExecCtx base noQuantum m ell width))
    (outcomes : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position ×
      Fin ((StageExecCtx base noQuantum m ell width).quantumLayout.wire
        (control base noQuantum m ell width)).dimension) :
    Store (StageExecCtx base noQuantum m ell width) ×
      (middle base noQuantum m ell width modulus wide inverse outputs unit position).Path :=
  Execution.Instrument.sequenceRetainedRecord
    (arithmetic base noQuantum m ell width wide modulus (unit ^ (2 ^ position.rev.val)))
    (stageTail base noQuantum m ell width inverse outputs position)
    (stageArithmeticRecord base noQuantum m ell width modulus wide unit position)
    (stageTailRecord base noQuantum m ell width inverse outputs position)
    store outcomes.1 outcomes.2

private def middleKraus (environment : model.Environment) (Reference : Register)
    (store : Store (StageExecCtx base noQuantum m ell width))
    (outcomes : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position ×
      Fin ((StageExecCtx base noQuantum m ell width).quantumLayout.wire
        (control base noQuantum m ell width)).dimension) :
    HilbertOperator ((StageExecCtx base noQuantum m ell width).register.prod Reference) :=
  stageTailKraus base noQuantum m ell width inverse outputs position environment Reference
      (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
        outcomes.1).1 outcomes.2 *
    stageArithmeticKraus base noQuantum m ell width modulus wide unit position environment store
      outcomes.1 Reference

private lemma middle_block_matrix (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (StageExecCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (result : Store (StageExecCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (middle base noQuantum m ell width modulus wide inverse outputs unit position).Path))) :
    (((middle base noQuantum m ell width modulus wide inverse outputs unit position).execute
      environment Reference state).block result).matrix =
      ∑ original : Store (StageExecCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcomes,
          if Execution.Instrument.retainedRecord
              (middleRecord base noQuantum m ell width modulus wide inverse outputs unit position)
              original outcomes = result then
            middleKraus base noQuantum m ell width modulus wide inverse outputs unit position
                environment Reference original.1 outcomes * (state.block original).matrix *
              (middleKraus base noQuantum m ell width modulus wide inverse outputs unit position
                environment Reference original.1 outcomes).conjTranspose
          else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (arithmetic base noQuantum m ell width wide modulus (unit ^ (2 ^ position.rev.val)))
    (stageTail base noQuantum m ell width inverse outputs position)
    (stageArithmeticRecord base noQuantum m ell width modulus wide unit position)
    (stageTailRecord base noQuantum m ell width inverse outputs position)
    (fun reference store measured => stageArithmeticKraus base noQuantum m ell width modulus wide
      unit position environment store measured reference)
    (stageTailKraus base noQuantum m ell width inverse outputs position environment)
    environment
    (fun reference _ _ original selected => wordCircuit_block_matrix (Physical.qubits width)
      (context_wires base noQuantum m ell width) (ventCell base noQuantum m ell width) environment
      ((Physical.layout width).multiplicationWord wide modulus
        ((unit ^ (2 ^ position.rev.val) : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
        (((unit ^ (2 ^ position.rev.val))⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
      reference original selected)
    (fun reference _ _ original selected => stageTail_block_matrix base noQuantum m ell width
      inverse outputs position environment reference original selected)
    Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_prod_type]
  rfl

private lemma stageRecord_sequence_eq (store : Store (StageExecCtx base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((StageExecCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    Execution.Instrument.sequenceRetainedRecord
      (Circuit.unitary (single base noQuantum m ell width Gate.HOp))
      (middle base noQuantum m ell width modulus wide inverse outputs unit position)
      (fun original (_ : Unit) => (original, ()))
      (middleRecord base noQuantum m ell width modulus wide inverse outputs unit position)
      store () (measured, outcome) =
    stageRecord base noQuantum m ell width modulus wide inverse outputs unit position store
      measured outcome := rfl

private lemma stageKraus_sequence_eq (environment : model.Environment) (Reference : Register)
    (store : Store (StageExecCtx base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((StageExecCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    middleKraus base noQuantum m ell width modulus wide inverse outputs unit position environment
        Reference store (measured, outcome) *
      (UnitaryOperator.prodTensor
        ((single base noQuantum m ell width Gate.HOp).matrix environment.quantum)
        (1 : UnitaryOperator Reference) :
          HilbertOperator ((StageExecCtx base noQuantum m ell width).register.prod Reference)) =
    stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit position
      environment store measured outcome Reference := rfl

/-- The actual stage interpreter yields exactly its original chronological record matrices. -/
lemma stage_block_matrix (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (StageExecCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (result : Store (StageExecCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path))) :
    (((stage base noQuantum m ell width wide inverse outputs modulus unit position).execute
      environment Reference state).block result).matrix =
      ∑ original : Store (StageExecCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position,
          ∑ outcome,
            if Execution.Instrument.retainedRecord (fun store outcomes => stageRecord base
              noQuantum m ell width modulus
                wide inverse outputs unit position store outcomes.1 outcomes.2)
                original (measured, outcome) = result then
              stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit position
                  environment original.1 measured outcome Reference *
                (state.block original).matrix *
                (stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit
                  position
                  environment original.1 measured outcome Reference).conjTranspose
            else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (Circuit.unitary (single base noQuantum m ell width Gate.HOp))
    (middle base noQuantum m ell width modulus wide inverse outputs unit position)
    (fun store (_ : Unit) => (store, ()))
    (middleRecord base noQuantum m ell width modulus wide inverse outputs unit position)
    (fun reference _ (_ : Unit) =>
      (UnitaryOperator.prodTensor
        ((single base noQuantum m ell width Gate.HOp).matrix environment.quantum)
        (1 : UnitaryOperator reference) :
          HilbertOperator ((StageExecCtx base noQuantum m ell width).register.prod reference)))
    (middleKraus base noQuantum m ell width modulus wide inverse outputs unit position environment)
    environment
    (by
      intro reference history historyFinite original selected
      have proved := stageHadamard_block_matrix base noQuantum m ell width environment reference
        original selected
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro entry _
      apply Finset.sum_congr rfl
      intro outcome _
      split_ifs <;> rfl)
    (by
      intro reference history historyFinite original selected
      have proved := middle_block_matrix base noQuantum m ell width modulus wide inverse outputs
        unit position environment reference original selected
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro entry _
      apply Finset.sum_congr rfl
      intro outcome _
      split_ifs <;> rfl)
    Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro original _
  conv_lhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro measured _
  apply Finset.sum_congr rfl
  intro outcome _
  have sameRecord := congrArg
    (fun next : Store (StageExecCtx base noQuantum m ell width) ×
        (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path =>
      (next.1, (original.2.1, (original.2.2, next.2))))
    (stageRecord_sequence_eq base noQuantum m ell width modulus wide inverse outputs unit position
      original.1 measured outcome)
  have sameOperator := stageKraus_sequence_eq base noQuantum m ell width modulus wide inverse
    outputs unit position environment Reference original.1 measured outcome
  by_cases selected : Execution.Instrument.retainedRecord (fun store outcomes => stageRecord base
    noQuantum m ell width
      modulus wide inverse outputs unit position store outcomes.1 outcomes.2)
      original (measured, outcome) = result
  · have selectedActual : Execution.Instrument.retainedRecord
        (fun store outcomes => Execution.Instrument.sequenceRetainedRecord
          (Circuit.unitary (single base noQuantum m ell width Gate.HOp))
          (middle base noQuantum m ell width modulus wide inverse outputs unit position)
          (fun old (_ : Unit) => (old, ()))
          (middleRecord base noQuantum m ell width modulus wide inverse outputs unit position)
          store outcomes.1 outcomes.2) original ((), (measured, outcome)) = result :=
      sameRecord.trans selected
    simp only [if_pos selected, if_pos selectedActual]
    rw [sameOperator]
  · have notSelected : ¬ Execution.Instrument.retainedRecord
        (fun store outcomes => Execution.Instrument.sequenceRetainedRecord
          (Circuit.unitary (single base noQuantum m ell width Gate.HOp))
          (middle base noQuantum m ell width modulus wide inverse outputs unit position)
          (fun old (_ : Unit) => (old, ()))
          (middleRecord base noQuantum m ell width modulus wide inverse outputs unit position)
          store outcomes.1 outcomes.2) original ((), (measured, outcome)) = result :=
      fun hit => selected (sameRecord.symm.trans hit)
    simp only [if_neg selected, if_neg notSelected]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
