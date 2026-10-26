/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin.Parallel.Frame
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Exact native pool and four-step paired Fredkin duration -/

namespace QuantumAlg.EncodedBit.FredkinParallel.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The event traversal includes all four CNOTs and both real Toffolis. -/
lemma program_eventTrace (frame : Frame encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) :
    (frame.program physical oracles).eventTrace =
      [.gate .cnot, .gate .cnot, .gate .toffoli, .gate .toffoli, .gate .cnot, .gate .cnot] := by
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    UnitaryCircuit.seq_eventTrace, WindowLookup.CnotLayer.program_eventTrace,
    cnotLayer_gates]
  rfl

/-- The exact actual native ledger is two Toffolis, four CNOTs and no one-qubit gate. -/
lemma program_counts (frame : Frame encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (frame.program physical oracles).eventCost = 2 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (frame.program physical oracles).eventCost = 4 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (frame.program physical oracles).eventCost = 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_eventTrace]
  simp [ResourcePool.ofList, ResourcePool.count]

/-- Shared control keeps the two actual Toffolis sequential between the independent layers. -/
lemma program_quantumTime (frame : Frame encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) :
    (frame.program physical oracles).evaluatedEventDepth Resource.Event.quantumDuration = 4 := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    WindowLookup.CnotLayer.program_quantumTime]
  change (if frame.cnotLayer.edges = [] then 0 else 1) +
    (1 + (1 + (if frame.cnotLayer.edges = [] then 0 else 1))) = 4
  simp only [cnotLayer, List.cons_ne_nil, if_false]

end

end QuantumAlg.EncodedBit.FredkinParallel.Frame
