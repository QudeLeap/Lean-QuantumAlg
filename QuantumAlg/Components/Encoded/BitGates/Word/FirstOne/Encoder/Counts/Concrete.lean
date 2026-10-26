/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Counts.Scalar

/-! # Exact native coordinates of the complete 259-position first-one encoder -/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Every complete balanced higher-subword occurrence is counted at the actual nine levels. -/
lemma priority259_testVolume : (Frame.priorityTree 259 9).testVolume = 1049 := by
  rw [priorityTree_volume_scalar 259 9 (by decide)]
  decide

/-- The compact complete original tree has exactly 258 actual forks. -/
lemma priority259_forks : (Frame.priorityTree 259 9).forks = 258 := by
  rw [priorityTree_forks_scalar 259 9 (by decide)]
  decide

/-- The exact complete native Toffoli recurrence retains both tests and all output masks. -/
lemma priority259_toffoli : emitterToffoliCount 10 (Frame.priorityTree 259 9) = 12640 := by
  rw [priorityTree_toffoli_scalar 259 10 9 (by decide)]
  decide

/-- The two prefix CNOTs at every original fork contribute their exact native coordinate. -/
lemma priority259_cnot : emitterCnotCount (Frame.priorityTree 259 9) = 516 := by
  rw [priorityTree_cnot_scalar 259 9 (by decide)]
  decide

/-- The original full-count sentinel has exactly three paid CNOT mask positions. -/
lemma priority259_sentinel :
    (Word.constantOneIndices (BitVec.ofNat 10 259).toFin).length = 3 := by decide

namespace Frame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {depth : Nat}
  (frame : Frame encoding 259 10 depth)

/-- All three separately named coordinates belong to the actual complete original native program. -/
lemma encoderProgram259_counts (fits : 9 ≤ depth) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (frame.encoderProgram 9 (by decide) fits).eventCost = 12640 ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (frame.encoderProgram 9 (by decide) fits).eventCost = 519 ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (frame.encoderProgram 9 (by decide) fits).eventCost = 4196 := by
  constructor
  · rw [frame.encoderProgram_toffoliCount, priority259_toffoli]
  · constructor
    · rw [frame.encoderProgram_cnotCount, priority259_cnot, priority259_sentinel]
    · rw [frame.encoderProgram_singleCount, priority259_testVolume]

/-- The actual complete sequential quantum dependency depth includes every native gate. -/
lemma encoderProgram259_unitDepth (fits : 9 ≤ depth) :
    (frame.encoderProgram 9 (by decide) fits).evaluatedEventDepth (fun _ => 1) = 17355 := by
  have counts := frame.encoderProgram259_counts fits
  rw [encoderProgram, GateSpec.programList_evaluatedEventDepth_unit,
    ← GateSpec.primitiveEventCount_programList]
  change GateSpec.primitiveEventCount (frame.encoderProgram 9 (by decide) fits) = 17355
  rw [GateSpec.primitiveEventCount, counts.1, counts.2.1, counts.2.2]

end Frame

end

end QuantumAlg.EncodedBit.FirstOne
