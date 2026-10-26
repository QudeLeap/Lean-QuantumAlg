/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Count
import all QuantumAlg.Components.GateModel.Algorithm.Resources.Events

/-!
# Complete independent pool for actual measured word reset

The two physical single-qubit layers, every real qubit measurement and the
width-indexed nominal packing operation all appear in the allowance. Stored
masks may select fewer X gates, but never change the paid pack coordinate.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

/-- Independent full native allowance for H, actual MZ, paid packing and selected X. -/
def measuredResetWordEnvelope (services : ClassicalOracleModel) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  AlgorithmGate.gateEnvelope BitWord.model services width 0 0 +
    (width • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) +
      (ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.classicalOperation (.nominalEncoding (.packFiniteBits width))) +
        AlgorithmGate.gateEnvelope BitWord.model services width 0 0))

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} {width : Nat}

/-- Every actual reset path obeys the complete independent pool, including its nominal pack. -/
lemma measuredResetWordCircuit_pool_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (path : (measuredResetWordCircuit (oracles := .empty) (services := services)
      physical sameWires target distinct output mask).Path) :
    (measuredResetWordCircuit physical sameWires target distinct output mask).resourcePool path ≤
      measuredResetWordEnvelope services width := by
  dsimp only [measuredResetWordCircuit, Circuit.Path] at path
  have first := AlgorithmGate.algorithmGate_unitaryCircuit_pool_le (ctx := ctx) (allocate := false)
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (wordHadamardProgram physical .empty target distinct)) BitWord.model services width 0 0
    (by
      intro coordinate
      rw [unitaryOfEqualWires_cost, wordHadamard_gate_count]
      cases coordinate <;> simp) path.1
  have last := AlgorithmGate.algorithmGate_unitaryCircuit_pool_le (ctx := ctx) (allocate := false)
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (wordXProgram physical .empty target distinct (resultConstant path.2.2.2.1)))
    BitWord.model services width 0 0
    (by
      intro coordinate
      rw [unitaryOfEqualWires_cost]
      have actual := wordX_gate_count_le (oracles := .empty) physical target distinct
        (resultConstant path.2.2.2.1) coordinate
      cases coordinate <;> simpa using actual) path.2.2.2.2
  have measured := Circuit.measurementSequence_qubit_resourcePool
    (gates := AlgorithmGate.model) (oracles := .empty) (operations := BitWord.model)
    (classicalOracles := services) (allowAllocation := false)
    (resultReadouts physical sameWires target output) (by
      intro item member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact resultWire_qubit physical sameWires (target.bit index)) path.2.1
  simp only [resultReadouts, List.length_ofFn] at measured
  change ResourcePool.ofList (_ ++ (_ ++ (_ ++ _))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add first (add_le_add measured.le (add_le_add le_rfl last))

end

end QuantumAlg.EncodedBit.WindowLookup
