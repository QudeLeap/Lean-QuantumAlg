/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Normal

/-! # Actual native coordinates of genuine normal selection and its inverse -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal

noncomputable section

open QuantumAlg.EncodedBit

lemma program_native_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        program.eventCost = 2032 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        program.eventCost = 1 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        program.eventCost = 512 := by
  have actual := layout.controlledNonzeroGates_native_counts Window.Enable.outputBit
    flag_sources flag_output flag_work (by omega)
  rw [Word.OneDirtyLayout.gateCount_of_five_le (by omega : 5 ≤ 256 + 1)] at actual
  simpa only [program, gates, GateSpec.programList_toffoli_count_eq_sum,
    GateSpec.programList_cnot_count_eq_sum, GateSpec.programList_x_count_eq_sum] using actual

lemma inverseProgram_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus inverseProgram.eventCost =
      ResourcePool.count focus program.eventCost := by
  simp only [inverseProgram, program, GateSpec.programList_eventCost, ResourcePool.count_ofList,
    List.map_reverse, List.count_reverse]

lemma program_quantumTime :
    program.evaluatedEventDepth Resource.Event.quantumDuration = 2545 := by
  rw [program, GateSpec.programList_quantumTime]
  change (layout.controlledNonzeroGates Window.Enable.outputBit flag_sources flag_output
    flag_work).length = 2545
  rw [Word.OneDirtyLayout.controlledNonzeroGates_length,
    Word.OneDirtyLayout.gateCount_of_five_le (by omega : 5 ≤ 256 + 1)]

lemma inverseProgram_quantumTime :
    inverseProgram.evaluatedEventDepth Resource.Event.quantumDuration = 2545 := by
  rw [inverseProgram, GateSpec.programList_quantumTime, List.length_reverse]
  exact (GateSpec.programList_quantumTime (QubitLayout.canonical _) .empty gates).symm.trans
    program_quantumTime

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal
