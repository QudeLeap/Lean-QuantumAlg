/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Restoration

/-!
# Actual unary preparation and restoration single-qubit events

The geometric native move stages contain only their actual Toffoli and
CNOT gates. Preparation has its original seed X; reversing that same native
program pays the same seed X again when restoring the reused result systems.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

namespace UnaryMoveFrame

/-- Actual unary move stages contain no single-qubit instruction. -/
lemma program_singleQubit_count {count : Nat} (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (frame.program physical oracles).eventCost = 0 := by
  rw [frame.program_eventCost, ResourcePool.count_add, ResourcePool.count_scale,
    ResourcePool.count_scale, ResourcePool.count_singleton, ResourcePool.count_singleton]
  rfl

end UnaryMoveFrame

namespace UnaryFrame

variable {width : Nat}

/-- Every actual geometric unary stage keeps only its Toffoli and CNOT events. -/
lemma stagesProgramAt_singleQubit_count (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (remaining depth : Nat) (fits : depth + remaining = width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (frame.stagesProgramAt physical oracles remaining depth fits).eventCost = 0 := by
  induction remaining generalizing depth with
  | zero => rfl
  | succ remaining ih =>
      rw [stagesProgramAt, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        UnaryMoveFrame.program_singleQubit_count, ih, Nat.zero_add]

/-- The original actual unary preparation pays precisely its one seed X gate. -/
lemma program_singleQubit_count (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (frame.program physical oracles).eventCost = 1 := by
  rw [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    frame.stagesProgramAt_singleQubit_count, Nat.add_zero, GateSpec.program_eventCost,
    ResourcePool.count_singleton]
  rfl

/-- The actual native inverse pays the same original seed X, without a free reset. -/
lemma uncomputeProgram_singleQubit_count (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (frame.uncomputeProgram physical).eventCost = 1 := by
  rw [frame.uncomputeProgram_event_count, frame.program_singleQubit_count]

end UnaryFrame

end

end QuantumAlg.EncodedBit.WindowLookup
