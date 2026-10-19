/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Actual resource traces of masked one-dirty conjunctions

Negative controls retain both native X masks. The borrowed conjunction keeps
its exact small-width gate families and linear Toffoli schedule. All counts
come from the literal executed list, with the arbitrary work bit restored.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout
noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls)
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

private lemma patternMask_events (expected : Fin controls → Bool) :
    (layout.patternMaskGates expected).map (GateSpec.event oracles) =
      List.replicate (patternMaskIndices expected).length
        (Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .singleQubit) := by
  simp only [patternMaskGates, List.map_map]
  change (patternMaskIndices expected).map (fun _ =>
    Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .singleQubit) = _
  simp

/-- The complete mask/conjunction/unmask trace retains every native coordinate. -/
lemma patternGates_events (expected : Fin controls → Bool) :
    (layout.patternGates expected).map (GateSpec.event oracles) =
      List.replicate (patternMaskIndices expected).length (.gate .singleQubit) ++
        (if controls = 0 then [.gate .singleQubit]
          else if controls = 1 then [.gate .cnot]
          else List.replicate (gateCount controls) (.gate .toffoli)) ++
        List.replicate (patternMaskIndices expected).length (.gate .singleQubit) := by
  rw [patternGates, List.map_append, List.map_append, List.map_reverse,
    patternMask_events, gates_events, List.reverse_replicate]

/-- Exact dependency depth includes both masks and all actual conjunction gates. -/
lemma patternGates_program_depth (expected : Fin controls → Bool) :
    (GateSpec.programList physical oracles (layout.patternGates expected)).evaluatedEventDepth
      (fun _ => 1) = 2 * (patternMaskIndices expected).length + gateCount controls := by
  rw [GateSpec.programList_evaluatedEventDepth_unit, patternGates_length, gates_length]

/-- The zero predicate masks every original source bit, including the empty-width case. -/
lemma zeroPattern_program_depth :
    (GateSpec.programList physical oracles (layout.patternGates fun _ => false)).evaluatedEventDepth
      (fun _ => 1) = 2 * controls + gateCount controls := by
  rw [patternGates_program_depth]
  simp [patternMaskIndices]

end
end QuantumAlg.EncodedBit.Word.OneDirtyLayout
