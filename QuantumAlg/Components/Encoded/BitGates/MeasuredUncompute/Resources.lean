/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Circuit
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Resources
import all QuantumAlg.Core.Execution.Trace

/-!
# Literal resources of physical X-basis measurement and reset

The Hadamard and outcome-selected X are actual native gates. Measurement,
write/read dependence and the retained result cell remain in the same path.
This circuit neither allocates nor releases any quantum or classical storage
[G25, main.tex:199-295].
-/

namespace QuantumAlg.EncodedBit.MeasuredUncompute

noncomputable section

private instance dimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}
  (wire : Fin ctx.systemCount)
  (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
  (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))

/-- The complete ordered path charges H, one MZ, and the actual selected identity/X. -/
lemma eventTrace
    (path : (circuit (oracles := oracles) wire qubit output operations services
      allowAllocation).Path) :
    (circuit wire qubit output operations services allowAllocation).eventTrace path =
      .gate .singleQubit :: Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        (ctx.quantumLayout.wire wire).dimension
        operations services ::
        (QuditShift.qubitShiftCircuit ctx.quantumLayout wire qubit oracles
          (-path.2.2.1.toFin)).eventTrace operations services := rfl

/-- The path has exactly one physical measurement and at most two one-qubit gates. -/
lemma eventTrace_cases
    (path : (circuit (oracles := oracles) wire qubit output operations services
      allowAllocation).Path) :
    (circuit wire qubit output operations services allowAllocation).eventTrace path =
      [.gate .singleQubit, Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        2 operations services] ∨
    (circuit wire qubit output operations services allowAllocation).eventTrace path =
      [.gate .singleQubit, Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        2 operations services, .gate .singleQubit] := by
  let amount : Fin (ctx.quantumLayout.wire wire).dimension := -path.2.2.1.toFin
  have shifted := QuditShift.qubitShiftCircuit_events ctx.quantumLayout wire qubit oracles
    amount operations services
  have traced : (circuit wire qubit output operations services allowAllocation).eventTrace path =
      .gate .singleQubit :: Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
        (ctx.quantumLayout.wire wire).dimension operations services ::
          (if amount = 0 then [] else [.gate .singleQubit]) :=
    (eventTrace wire qubit output path).trans
      (congrArg (fun tail => Resource.Event.gate
          (model := .quantum AlgorithmGate.model oracles operations services)
          AlgorithmGate.Coordinate.singleQubit ::
        Circuit.zEvent (gates := AlgorithmGate.model) (oracles := oracles)
          (ctx.quantumLayout.wire wire).dimension operations services :: tail) shifted)
  by_cases zero : amount = 0
  · left
    exact traced.trans (by simp only [zero, if_true, qubit])
  · right
    exact traced.trans (by simp only [zero, if_false, qubit])

/-- Both native space peaks equal the complete caller context, including the measured cell. -/
lemma spaces
    (path : (circuit (oracles := oracles) wire qubit output operations services
      allowAllocation).Path) :
    (circuit wire qubit output operations services allowAllocation).peakResidentSpace path =
        ctx.residentSpace ∧
      (circuit wire qubit output operations services allowAllocation).peakAuxiliarySpace path =
        ctx.auxiliarySpace := by
  constructor
  · change SpacePool.max ctx.residentSpace
      (SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0)) = _
    rw [SpacePool.max_zero, SpacePool.max_self, SpacePool.max_self]
  · change SpacePool.max ctx.auxiliarySpace
      (SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0)) = _
    rw [SpacePool.max_zero, SpacePool.max_self, SpacePool.max_self]

end

end QuantumAlg.EncodedBit.MeasuredUncompute
