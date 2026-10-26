/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy.Encoder
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Exact native policy encoder trace and actual quantum duration

A concrete physical test implementation proves its own complete trace.
The compiler retains both real tests, both children, both prefix CNOTs
and the original paid sentinel load, with every native coordinate separate.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Independent complete event recurrence for a real native test backend. -/
def policyEmitterTrace {count : Nat}
    (testTrace : Nat → List (Resource.Event (.quantum AlgorithmGate.model .empty)))
    (outputWidth : Nat) : ListPriority.Tree (Fin count) →
      List (Resource.Event (.quantum AlgorithmGate.model .empty))
  | .empty => []
  | .leaf label => List.replicate
      (Word.constantOneIndices (Frame.leafMask (outputWidth := outputWidth) label)).length
      (.gate .toffoli)
  | .fork higher lower => testTrace higher.leaves.length ++
      (policyEmitterTrace testTrace outputWidth lower ++ (.gate .cnot ::
        (policyEmitterTrace testTrace outputWidth higher ++
          (testTrace higher.leaves.length ++ [.gate .cnot]))))

/-- Independent full policy trace, including the original real root-controlled sentinel CNOTs. -/
def policyEncoderTrace
    (testTrace : Nat → List (Resource.Event (.quantum AlgorithmGate.model .empty)))
    (count outputWidth height : Nat) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  List.replicate (Word.constantOneIndices (BitVec.ofNat outputWidth count).toFin).length
    (.gate .cnot) ++ policyEmitterTrace testTrace outputWidth (Frame.priorityTree count height)

namespace TestPolicy

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  {frame : Frame encoding count outputWidth depth} (policy : TestPolicy frame)
  (testTrace : Nat → List (Resource.Event (.quantum AlgorithmGate.model .empty)))
  (testEvents : ∀ labels distinct level present,
    (policy.gates labels distinct level present).map (GateSpec.event .empty) =
      testTrace labels.length)

include testEvents

/-- Every real policy test and every literal child is retained
in the exact recursive native trace. -/
lemma policy_gatesAt_events (tree : ListPriority.Tree (Fin count)) (unique : tree.leaves.Nodup)
    (level : Nat) (fits : level + tree.height ≤ depth) :
    (policy.gatesAt tree unique level fits).map (GateSpec.event .empty) =
      policyEmitterTrace testTrace outputWidth tree := by
  induction tree generalizing level with
  | empty => rfl
  | leaf label =>
      simp only [gatesAt, Word.doubleControlledXorConstantGates, List.map_map, policyEmitterTrace]
      change (Word.constantOneIndices (Frame.leafMask (outputWidth := outputWidth) label)).map
        (fun _ => Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .toffoli) = _
      simp
  | fork higher lower higherTrace lowerTrace =>
      dsimp only [gatesAt, policyEmitterTrace]
      simp only [List.map_append, List.map_cons, List.map_nil, testEvents, lowerTrace, higherTrace]
      rfl

/-- The actual full native policy word has exactly the independent original sentinel trace. -/
lemma policyEncoderGates_events (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (policy.encoderGates height capacity fits).map (GateSpec.event .empty) =
      policyEncoderTrace testTrace count outputWidth height := by
  rw [encoderGates, List.map_append, policy.policy_gatesAt_events testTrace testEvents]
  unfold Frame.sentinelGates Word.controlledXorConstantGates
  simp only [List.map_map, policyEncoderTrace]
  congr 1
  change (Word.constantOneIndices (BitVec.ofNat outputWidth count).toFin).map
    (fun _ => Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot) = _
  simp

/-- All actual native coordinates are kept independently in the same proved policy event pool. -/
lemma policyEncoderProgram_eventCost (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (policy.encoderProgram height capacity fits).eventCost =
      ResourcePool.ofList (policyEncoderTrace testTrace count outputWidth height) := by
  rw [encoderProgram, GateSpec.programList_eventCost,
    policy.policyEncoderGates_events testTrace testEvents]

/-- The complete actual sequential duration equals the length of the exact native policy trace. -/
lemma policyEncoderProgram_quantumDuration (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (policy.encoderProgram height capacity fits).evaluatedEventDepth
        Resource.Event.quantumDuration =
      (policyEncoderTrace testTrace count outputWidth height).length := by
  have duration := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (policy.encoderProgram height capacity fits) .empty .empty
  change (policy.encoderProgram height capacity fits).evaluatedEventDepth
      Resource.Event.quantumDuration =
    (policy.encoderProgram height capacity fits).evaluatedEventDepth (fun _ => 1) at duration
  rw [duration, encoderProgram, GateSpec.programList_evaluatedEventDepth_unit]
  simpa only [List.length_map] using congrArg List.length
    (policy.policyEncoderGates_events testTrace testEvents height capacity fits)

end TestPolicy

end

end QuantumAlg.EncodedBit.FirstOne
