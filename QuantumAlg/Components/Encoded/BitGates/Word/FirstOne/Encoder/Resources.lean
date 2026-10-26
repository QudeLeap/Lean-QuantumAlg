/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Exact native trace and charged quantum duration of the balanced first-one encoder

All native coordinates remain separate in the exact event pool. The
independent bound charges every output Toffoli, both complete masks and
arbitrary-work tests, both prefix CNOTs, and the sentinel CNOT load.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Independent exact native sequence for this complete original balanced priority problem. -/
def encoderTrace (count outputWidth height : Nat) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  List.replicate (Word.constantOneIndices (BitVec.ofNat outputWidth count).toFin).length
      (.gate .cnot) ++ emitterTrace outputWidth (Frame.priorityTree count height)

/-- Independent upper bound for the full sequential native program,
including both tests per fork. -/
def encoderLimit (count outputWidth height : Nat) : Nat :=
  outputWidth + count * (outputWidth + 20 * height) + 24 * (count - 1)

namespace Frame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- Every actual native event is retained in the independent exact original-source trace. -/
lemma encoderGates_events (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth) :
    (frame.encoderGates height capacity fits).map (GateSpec.event .empty) =
      encoderTrace count outputWidth height := by
  rw [encoderGates, List.map_append, frame.gatesAt_events]
  unfold sentinelGates Word.controlledXorConstantGates
  simp only [List.map_map, encoderTrace]
  congr 1
  change (Word.constantOneIndices (BitVec.ofNat outputWidth count).toFin).map
    (fun _ => Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot) = _
  simp

/-- The same actual event pool exposes CNOT, Toffoli and single-qubit coordinates independently. -/
lemma encoderProgram_eventCost (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (frame.encoderProgram height capacity fits).eventCost =
      ResourcePool.ofList (encoderTrace count outputWidth height) := by
  rw [encoderProgram, GateSpec.programList_eventCost, frame.encoderGates_events]

/-- Every separately selected native coordinate has its exact original-trace multiplicity. -/
lemma encoderProgram_eventCount (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (event : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count event (frame.encoderProgram height capacity fits).eventCost =
      (encoderTrace count outputWidth height).count event := by
  rw [frame.encoderProgram_eventCost, ResourcePool.count_ofList]

/-- The original complete balanced tree yields a closed bound on the actual entire native list. -/
lemma encoderGates_length_le (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (frame.encoderGates height capacity fits).length ≤ encoderLimit count outputWidth height := by
  have sentinel := Word.controlledXorConstantGates_length_le_width
    (frame.stack.bit ⟨0, by omega⟩) frame.output (BitVec.ofNat outputWidth count).toFin
    (fun output => Ne.symm (frame.outputStack output _))
  have emitted := frame.gatesAt_length_le (priorityTree count height)
    (priorityTree_distinct capacity) 0
    (by have bounded := priorityTree_height (count := count) (depth := height); omega)
  have volume := ListPriority.Tree.balanced_testVolume_le height (List.finRange count)
    (by simpa only [List.length_finRange] using capacity)
  have forks := ListPriority.Tree.balanced_forks_le height (List.finRange count)
  rw [priorityTree_leaves capacity, List.length_finRange] at emitted
  simp only [List.length_finRange] at volume forks
  change (priorityTree count height).testVolume ≤ count * height at volume
  change (priorityTree count height).forks ≤ count - 1 at forks
  change frame.sentinelGates.length ≤ outputWidth at sentinel
  simp only [encoderGates, List.length_append, encoderLimit]
  nlinarith

/-- The actual sequential native depth is exactly the complete charged original trace length. -/
lemma encoderProgram_unitDepth (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (frame.encoderProgram height capacity fits).evaluatedEventDepth (fun _ => 1) =
      (encoderTrace count outputWidth height).length := by
  rw [encoderProgram, GateSpec.programList_evaluatedEventDepth_unit]
  simpa only [List.length_map] using congrArg List.length
    (frame.encoderGates_events height capacity fits)

/-- The actual quantum duration retains every native dependency
and satisfies the independent bound. -/
lemma encoderProgram_quantumTime_le (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (frame.encoderProgram height capacity fits).evaluatedEventDepth Resource.Event.quantumDuration ≤
      encoderLimit count outputWidth height := by
  have duration := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (frame.encoderProgram height capacity fits) .empty .empty
  change (frame.encoderProgram height capacity fits).evaluatedEventDepth
      Resource.Event.quantumDuration =
    (frame.encoderProgram height capacity fits).evaluatedEventDepth (fun _ => 1) at duration
  rw [duration, encoderProgram, GateSpec.programList_evaluatedEventDepth_unit]
  exact frame.encoderGates_length_le height capacity fits

end Frame

end

end QuantumAlg.EncodedBit.FirstOne
