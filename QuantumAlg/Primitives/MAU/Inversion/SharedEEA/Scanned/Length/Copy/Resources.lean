/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Bit
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Positive

/-! # Exact paid native resources of the complete original length XOR -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy

noncomputable section

open EncodedBit LengthCoordinates

private lemma positive_events (width : Nat) (poolFlag : Bool) (field : Field) :
    (positiveGates width poolFlag field).map (GateSpec.event .empty) =
      List.replicate (4 * width.size) (.gate .toffoli) := by
  have blocks (bits : List (Fin width.size)) :
      (bits.flatMap (bitGates width poolFlag field)).map (GateSpec.event .empty) =
        List.replicate (4 * bits.length) (.gate .toffoli) := by
    induction bits with
    | nil => rfl
    | cons bit rest ih =>
        rw [List.flatMap_cons, List.map_append, bitGates_events, ih]
        rw [show 4 * (bit :: rest).length = 4 + 4 * rest.length by
          simp only [List.length_cons]
          omega,
          List.replicate_add]
  simpa only [positiveGates, List.length_finRange] using blocks (List.finRange width.size)

/-- Two actual X masks and exactly four native Toffolis per original finite output bit. -/
lemma gates_events (width : Nat) (poolFlag : Bool) (field : Field) :
    (gates width poolFlag field).map (GateSpec.event .empty) =
      [.gate .singleQubit] ++ List.replicate (4 * width.size) (.gate .toffoli) ++
        [.gate .singleQubit] := by
  (simp only [gates, List.map_append, List.map_cons, List.map_nil, positive_events]; rfl)

/-- The event pool and actual sequential duration come from that same physical native word. -/
lemma program_resources (width : Nat) (poolFlag : Bool) (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program width poolFlag field).eventCost = 4 * width.size ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program width poolFlag field).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program width poolFlag field).eventCost = 2 ∧
      (program width poolFlag field).evaluatedEventDepth Resource.Event.quantumDuration =
        4 * width.size + 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [program, GateSpec.programList_eventCost, gates_events, ResourcePool.count_ofList]
    simp
  · rw [program, GateSpec.programList_eventCost, gates_events, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq]
  · rw [program, GateSpec.programList_eventCost, gates_events, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq]
  · have length := congrArg List.length (gates_events width poolFlag field)
    simp only [List.length_map, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate] at length
    rw [program, GateSpec.programList_quantumTime, length]
    omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy
