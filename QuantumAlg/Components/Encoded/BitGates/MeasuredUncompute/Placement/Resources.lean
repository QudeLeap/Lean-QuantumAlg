/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Placement
import all QuantumAlg.Core.Execution.Trace

/-!
# Literal resources of the actual equal-wire placed reset

The placed instruction word keeps its native Hadamard and its selected reset,
measures the corresponding physical wire, and retains the caller's complete
storage. Equality of complete ordered wire records introduces no paid gate
[G25, main.tex:199-295].
-/

namespace QuantumAlg.EncodedBit.MeasuredUncompute

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {oracles : OracleModel}
  (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
  (ctx : RuntimeCtx .quantum)
  (sameWires : layout.toQuantum.wires = ctx.quantumLayout.wires)
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}
  (output : CWriteRef ctx
    (.finite (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension))

/-- The actual placed path contains H, MZ and precisely its read-back-selected native reset. -/
lemma placedCircuit_eventTrace
    (path : (placedCircuit (oracles := oracles) target layout ctx sameWires output operations
      services allowAllocation).Path) :
    (placedCircuit target layout ctx sameWires output operations services
      allowAllocation).eventTrace path =
      .gate .singleQubit :: Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension
        operations services ::
          (correction target layout
            (placedOutcome target layout ctx sameWires path.2.2.1.toFin)).eventTrace operations
              services := rfl

/-- Exactly one physical qubit is measured and zero or one reset X follows its Hadamard. -/
lemma placedCircuit_eventTrace_cases
    (path : (placedCircuit (oracles := oracles) target layout ctx sameWires output operations
      services allowAllocation).Path) :
    (placedCircuit target layout ctx sameWires output operations services
      allowAllocation).eventTrace path =
      [.gate .singleQubit, Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        2 operations services] ∨
    (placedCircuit target layout ctx sameWires output operations services
      allowAllocation).eventTrace path =
      [.gate .singleQubit, Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        2 operations services, .gate .singleQubit] := by
  let amount : Fin (layout.toQuantum.wire target.wire).dimension :=
    -(actualOutcome target layout
      (placedOutcome target layout ctx sameWires path.2.2.1.toFin))
  have shifted := QuditShift.qubitShiftCircuit_events layout.toQuantum target.wire rfl oracles
    amount operations services
  have traced : (placedCircuit target layout ctx sameWires output operations services
      allowAllocation).eventTrace path =
      .gate .singleQubit :: Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension
        operations services :: (if amount = 0 then [] else [.gate .singleQubit]) :=
    (placedCircuit_eventTrace target layout ctx sameWires output path).trans
      (congrArg (fun tail => Resource.Event.gate
          (model := .quantum AlgorithmGate.model oracles operations services)
          AlgorithmGate.Coordinate.singleQubit ::
        Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
          (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension
          operations services :: tail) shifted)
  by_cases zero : amount = 0
  · left
    exact traced.trans (by simp only [zero, if_true, placedWire_qubit])
  · right
    exact traced.trans (by simp only [zero, if_false, placedWire_qubit])

/-- Every visited context preserves the caller's actual resident and auxiliary capacities. -/
lemma placedCircuit_spaces
    (path : (placedCircuit (oracles := oracles) target layout ctx sameWires output operations
      services allowAllocation).Path) :
    (placedCircuit target layout ctx sameWires output operations services
      allowAllocation).peakResidentSpace path = ctx.residentSpace ∧
      (placedCircuit target layout ctx sameWires output operations services
        allowAllocation).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  constructor
  · change SpacePool.max ctx.residentSpace
      (SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0)) = _
    rw [SpacePool.max_zero, SpacePool.max_self, SpacePool.max_self]
  · change SpacePool.max ctx.auxiliarySpace
      (SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0)) = _
    rw [SpacePool.max_zero, SpacePool.max_self, SpacePool.max_self]

end

end QuantumAlg.EncodedBit.MeasuredUncompute
