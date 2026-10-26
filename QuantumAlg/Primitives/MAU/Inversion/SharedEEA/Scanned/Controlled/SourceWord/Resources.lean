/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord

/-! # Actual native resources of the selected source word -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSourceWord

noncomputable section

open EncodedBit

private lemma source_events (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    (sourceGates width body).map (GateSpec.event .empty) = body.map (GateSpec.event .empty) :=
  GateSpec.map_event_prodLeft (poolEncoding width) body

/-- Every source CNOT and all four Toffolis per actual dirty-control lowering are charged. -/
lemma program_toffoli_count (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program width body).eventCost =
        (body.map GateSpec.cnotMultiplicity).sum +
          4 * (body.map GateSpec.toffoliMultiplicity).sum := by
  have actual := ExternalWord.program_toffoli_count (Scanned.encoding width)
    (sourceGates width body)
  rw [GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty (source_events width body),
    GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty (source_events width body)] at actual
  exact actual

/-- Every actual source X becomes one paid CNOT. -/
lemma program_cnot_count (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program width body).eventCost = (body.map GateSpec.xMultiplicity).sum := by
  have actual := ExternalWord.program_cnot_count (Scanned.encoding width) (sourceGates width body)
  rw [GateSpec.sum_xMultiplicity_eq_of_events_eq .empty (source_events width body)] at actual
  exact actual

lemma program_singleQubit_count (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program width body).eventCost = 0 :=
  ExternalWord.program_singleQubit_count (Scanned.encoding width) (sourceGates width body)

/-- The same actual selected native word supplies its sequential duration. -/
lemma program_quantumTime (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    (program width body).evaluatedEventDepth Resource.Event.quantumDuration =
      (body.map GateSpec.xMultiplicity).sum + (body.map GateSpec.cnotMultiplicity).sum +
        4 * (body.map GateSpec.toffoliMultiplicity).sum := by
  have actual := ExternalWord.program_quantumTime (Scanned.encoding width) (sourceGates width body)
  rw [GateSpec.sum_xMultiplicity_eq_of_events_eq .empty (source_events width body),
    GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty (source_events width body),
    GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty (source_events width body)] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSourceWord
