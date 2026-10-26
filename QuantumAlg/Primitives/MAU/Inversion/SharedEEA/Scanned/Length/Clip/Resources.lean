/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Resources

/-! # Actual native P-256 clipping resources, including activation and borrow -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The real negative high-bit activation is exactly X, Toffoli, X. -/
lemma activeGates_events (width : Nat) :
    (activeGates width).map (GateSpec.event .empty) =
      [.gate .singleQubit, .gate .toffoli, .gate .singleQubit] := by
  rfl

private lemma p256_activation_resources :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (activationProgram 256).eventCost = 1 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (activationProgram 256).eventCost = 0 ∧
      (activationProgram 256).evaluatedEventDepth Resource.Event.quantumDuration = 3 := by
  have selected : narrow 256 := by decide
  have events := activeGates_events 256
  refine ⟨?_, ?_, ?_⟩
  · rw [activationProgram, activationGates, if_pos selected, GateSpec.programList_eventCost,
      events, ResourcePool.count_ofList]
    simp
  · rw [activationProgram, activationGates, if_pos selected, GateSpec.programList_eventCost,
      events, ResourcePool.count_ofList]
    simp
  · have length := congrArg List.length events
    simp only [List.length_map, List.length_cons, List.length_nil] at length
    rw [activationProgram, activationGates, if_pos selected, GateSpec.programList_quantumTime,
      length]

/-- Exact native Toffoli count of the complete real clipping preparation. -/
lemma p256_prepareProgram_toffoli_count (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (prepareProgram 256 field).eventCost = 36 := by
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    LengthBoundary.p256_prepareProgram_toffoli_count, p256_activation_resources.1,
    LengthDifference.program_toffoli_count]
  decide

/-- Exact complete clipping CNOT count; neither the public load nor activation adds one. -/
lemma p256_prepareProgram_cnot_count (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (prepareProgram 256 field).eventCost = 84 := by
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    LengthBoundary.p256_prepareProgram_cnot_count, p256_activation_resources.2.1,
    LengthDifference.program_cnot_count]
  decide

/-- Actual quantum duration includes public loading, parallel metadata subtraction,
negative-control activation and the full serial borrow-output subtraction. -/
lemma p256_prepareProgram_quantumTime_le (field : Field) :
    (prepareProgram 256 field).evaluatedEventDepth Resource.Event.quantumDuration ≤ 108 := by
  have boundary := LengthBoundary.prepareProgram_quantumTime_le 256 field (by decide)
  have weight : LengthBoundary.constantWeight 256 field ≤ 3 := by
    cases field <;> decide
  rw [prepareProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, p256_activation_resources.2.2,
    LengthDifference.program_quantumTime]
  have numeric : ScanMetadata.addressWidth 256 = 10 ∧ subtractionWidth 256 = 9 := by decide
  rw [numeric.1] at boundary
  rw [numeric.2]
  norm_num only at boundary ⊢
  simp only [if_true, if_false]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
