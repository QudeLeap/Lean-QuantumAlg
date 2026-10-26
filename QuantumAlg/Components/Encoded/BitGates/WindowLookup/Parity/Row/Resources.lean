/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Resources
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Actual paid parity row classical work and physical feedback depth

Every column pays its actual clear and every selected measured-bit XOR.
The stored vector selects the actual native fan-in phase, whose physical
parallel layers retain their original quantum depth. All bounds concern
actual paths, independently of the incoming Store or a unary promise.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

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

/-- The actual clear and selected measured-bit XORs are each paid once. -/
lemma program_classical_weight (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services) parity inputs).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((program (oracles := oracles) (services := services)
        parity inputs).resourcePool path) = inputs.length + 1 := by
  rw [Circuit.resourcePool, program_eventTrace, ResourcePool.weightedCount_ofList]
  simp [Resource.Event.classicalOperationWeight]

/-- The actual paid row uses at most one clear and the complete result width per low column. -/
lemma rowProgram_classical_weight_le (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (table : Fin columns → Fin (2 ^ wordWidth))
    (indices : List (Fin columns))
    (path : (rowProgram (oracles := oracles) (services := services)
      measured parity table indices).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((rowProgram (oracles := oracles) (services := services)
        measured parity table indices).resourcePool path) ≤
        indices.length * (wordWidth + 1) := by
  induction indices with
  | nil =>
      dsimp only [rowProgram, Circuit.Path] at path
      cases path
      simp [rowProgram, Circuit.resourcePool, Circuit.eventTrace]
  | cons index rest ih =>
      dsimp only [rowProgram, Circuit.Path] at path
      have tail := ih path.2
      have selected := Word.constantOneIndices_length_le (table index)
      change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (((program (oracles := oracles) (services := services)
          (parity index) (selectedInputs measured (table index))).seq
          (rowProgram (oracles := oracles) (services := services)
            measured parity table rest)).resourcePool path) ≤ _
      rw [classicalWeight_seq, program_classical_weight]
      dsimp only [selectedInputs]
      rw [List.length_map, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The actual clear and full row retain zero quantum duration
while keeping their classical events. -/
lemma rowProgram_quantumTime (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (table : Fin columns → Fin (2 ^ wordWidth))
    (indices : List (Fin columns))
    (path : (rowProgram (oracles := oracles) (services := services)
      measured parity table indices).Path) :
    (rowProgram (oracles := oracles) (services := services)
      measured parity table indices).depth Resource.Event.quantumDuration path = 0 := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      dsimp only [rowProgram, Circuit.Path] at path
      change (program (oracles := oracles) (services := services)
        (parity index) (selectedInputs measured (table index))).depth
        Resource.Event.quantumDuration path.1 +
          (rowProgram (oracles := oracles) (services := services)
            measured parity table rest).depth Resource.Event.quantumDuration path.2 = 0
      rw [program_quantumTime, ih, Nat.zero_add]

private lemma pure_classical_weight
    (native : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout) (path : Unit) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
        (allowAllocation := false) native).resourcePool path) = 0 := by
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    (ResourcePool.ofList (native.eventTrace BitWord.model services)) = 0
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost native BitWord.model services]
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        native BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

/-- The actual complete paid row retains its original native-operation classical bound. -/
lemma rowCircuit_classical_weight_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (path : (rowCircuit (oracles := oracles) (services := services) physical sameWires
      measured parity table target distinct selector outside height).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((rowCircuit physical sameWires measured parity table target distinct selector outside
        height).resourcePool path) ≤ columns * (wordWidth + 1) := by
  dsimp only [rowCircuit, SelectorFrame.placedCircuit, Circuit.Path] at path
  have first := rowProgram_classical_weight_le measured parity table
    (List.ofFn fun index : Fin columns => index) path.1
  simp only [List.length_ofFn] at first
  let native := unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (wordMaskParityPhaseProgram physical oracles target distinct selector outside
      (storedConstant path.2.1) height)
  have last := pure_classical_weight (services := services) native ()
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    (ResourcePool.ofList (native.eventTrace BitWord.model services)) = 0 at last
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    (ResourcePool.ofList
      ((rowProgram (oracles := oracles) (services := services)
        measured parity table (List.ofFn fun index : Fin columns => index)).eventTrace path.1 ++
          native.eventTrace BitWord.model services)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.weightedCount_add, last, Nat.add_zero]
  exact first

/-- Stored-mask physical fan-in retains its actual parallel quantum depth after all paid XORs. -/
lemma rowCircuit_quantumTime_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (path : (rowCircuit (oracles := oracles) (services := services) physical sameWires
      measured parity table target distinct selector outside height).Path) :
    (rowCircuit physical sameWires measured parity table target distinct selector outside
      height).depth Resource.Event.quantumDuration path ≤ 2 * height + 3 := by
  dsimp only [rowCircuit, SelectorFrame.placedCircuit, Circuit.Path] at path
  change (rowProgram (oracles := oracles) (services := services)
    measured parity table (List.ofFn fun index : Fin columns => index)).depth
    Resource.Event.quantumDuration path.1 + _ ≤ _
  rw [rowProgram_quantumTime, Nat.zero_add]
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (wordMaskParityPhaseProgram physical oracles target distinct selector outside
        (storedConstant path.2.1) height)).eventDepth BitWord.model services) ≤ _
  rw [unitaryOfEqualWires_depth, UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]
  exact maskedParityPhaseProgram_quantumTime_le physical oracles
    (constantMaskTarget target (storedConstant path.2.1))
    (constantMaskTarget_distinct target distinct (storedConstant path.2.1)) selector
    (fun index => outside ((Word.constantOneIndices (storedConstant path.2.1)).get index)) height

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity
