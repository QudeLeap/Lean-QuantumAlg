/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Resources
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# The paid native packing operation in the actual measured reset ledger

The existing native-operation metric counts every classical operation once.
In particular packing the measured finite cells is one paid nominal encoding
instruction. Quantum H/X and actual MZ retain their own separate coordinates;
neither the mask's width nor its actual storage is erased by this observation.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

private lemma pure_classical_weight
    (program : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout) (path : Unit) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
        (allowAllocation := false) program).resourcePool path) = 0 := by
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    (ResourcePool.ofList (program.eventTrace BitWord.model services)) = 0
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost program BitWord.model services]
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        program BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

private lemma resultReadouts_classical_weight (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)).resourcePool path) = 0 := by
  rw [Circuit.measurementSequence_resourcePool, ResourcePool.weightedCount_ofList]
  simp only [List.map_map, Function.comp_def, Circuit.zEvent,
    Resource.Event.classicalOperationWeight, List.map_const', List.sum_replicate, smul_zero]

private lemma classicalWeight_seq {model : ExecutionModel} {context : RuntimeCtx model.kind}
    {allocate : Bool} (first second : Circuit model context context allocate)
    (path : (first.seq second).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((first.seq second).resourcePool path) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (first.resourcePool path.1) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (second.resourcePool path.2) := by
  simp only [Circuit.resourcePool, Circuit.eventTrace, ResourcePool.ofList_append,
    ResourcePool.weightedCount_add]

/-- The actual native packing instruction is paid once on every complete measured reset path. -/
lemma measuredResetWordCircuit_classical_weight (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (path : (measuredResetWordCircuit (oracles := oracles) (services := services)
      physical sameWires target distinct output mask).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((measuredResetWordCircuit physical sameWires target distinct output mask).resourcePool
        path) = 1 := by
  dsimp only [measuredResetWordCircuit, Circuit.Path] at path
  unfold measuredResetWordCircuit
  rw [classicalWeight_seq, classicalWeight_seq, classicalWeight_seq,
    pure_classical_weight, resultReadouts_classical_weight]
  have packed : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((MaskParity.instruction (oracles := oracles) (services := services)
        (resultPackOp output mask)).resourcePool path.2.2.1) = 1 := rfl
  rw [packed]
  change 0 + (0 + (1 + ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
      (allowAllocation := false)
      (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (wordXProgram physical oracles target distinct (resultConstant path.2.2.2.1)))).resourcePool
          path.2.2.2.2))) = 1
  rw [pure_classical_weight]

end

end QuantumAlg.EncodedBit.WindowLookup
