/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Predicated
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-!
# Native ledgers of actual source-prefix lifts and selected predicate payloads

The original predicate word and its reverse both execute. Only its
middle word receives real external dirty-work control. These counts
follow the actual emitted source list, including every negative mask.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSourceWord

noncomputable section

open EncodedBit

private lemma lifted_events (width : Nat)
    (body : List (GateSpec (SharedEEA.encoding width))) :
    (liftedGates width body).map (GateSpec.event .empty) =
      body.map (GateSpec.event .empty) := by
  have first := GateSpec.map_event_prodLeft (oracles := .empty)
    ExternalWord.flags (sourceGates width body)
  have second := GateSpec.map_event_prodLeft (oracles := .empty) (poolEncoding width) body
  exact first.trans second

/-- The actual full source-prefix placement retains every source Toffoli occurrence. -/
lemma liftedGates_toffoli_count (width : Nat)
    (body : List (GateSpec (SharedEEA.encoding width))) :
    ((liftedGates width body).map GateSpec.toffoliMultiplicity).sum =
      (body.map GateSpec.toffoliMultiplicity).sum :=
  GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty (lifted_events width body)

/-- Both spectator-prefix extensions preserve each source CNOT occurrence. -/
lemma liftedGates_cnot_count (width : Nat)
    (body : List (GateSpec (SharedEEA.encoding width))) :
    ((liftedGates width body).map GateSpec.cnotMultiplicity).sum =
      (body.map GateSpec.cnotMultiplicity).sum :=
  GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty (lifted_events width body)

/-- Every actual source X mask remains in the same extended physical prefix. -/
lemma liftedGates_x_count (width : Nat)
    (body : List (GateSpec (SharedEEA.encoding width))) :
    ((liftedGates width body).map GateSpec.xMultiplicity).sum =
      (body.map GateSpec.xMultiplicity).sum :=
  GateSpec.sum_xMultiplicity_eq_of_events_eq .empty (lifted_events width body)

/-- The actual selected list has the same native control expansion as its emitted program. -/
lemma selectedGates_toffoli_count (width : Nat)
    (body : List (GateSpec (SharedEEA.encoding width))) :
    ((selectedGates width body).map GateSpec.toffoliMultiplicity).sum =
      (body.map GateSpec.cnotMultiplicity).sum +
        4 * (body.map GateSpec.toffoliMultiplicity).sum := by
  rw [← GateSpec.programList_toffoli_count_eq_sum
    (layout := QubitLayout.canonical _) (oracles := .empty)]
  exact program_toffoli_count width body

/-- Each actual selected source X contributes precisely one native CNOT. -/
lemma selectedGates_cnot_count (width : Nat)
    (body : List (GateSpec (SharedEEA.encoding width))) :
    ((selectedGates width body).map GateSpec.cnotMultiplicity).sum =
      (body.map GateSpec.xMultiplicity).sum := by
  rw [← GateSpec.programList_cnot_count_eq_sum
    (layout := QubitLayout.canonical _) (oracles := .empty)]
  exact program_cnot_count width body

/-- No single-qubit instruction remains inside the actual selected source list. -/
lemma selectedGates_x_count (width : Nat)
    (body : List (GateSpec (SharedEEA.encoding width))) :
    ((selectedGates width body).map GateSpec.xMultiplicity).sum = 0 := by
  rw [← GateSpec.programList_x_count_eq_sum
    (layout := QubitLayout.canonical _) (oracles := .empty)]
  exact program_singleQubit_count width body

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSourceWord

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPredicated

noncomputable section

open EncodedBit

/-- Both actual source preparations and every selected payload Toffoli remain in the native pool. -/
lemma program_toffoli_count (width : Nat)
    (prepare middle : List (GateSpec (SharedEEA.encoding width))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program width prepare middle).eventCost =
        2 * (prepare.map GateSpec.toffoliMultiplicity).sum +
          (middle.map GateSpec.cnotMultiplicity).sum +
            4 * (middle.map GateSpec.toffoliMultiplicity).sum := by
  simp only [program, GateSpec.programList_toffoli_count_eq_sum, gates,
    List.map_append, List.sum_append, ControlledSourceWord.liftedGates_toffoli_count,
    ControlledSourceWord.selectedGates_toffoli_count, List.map_reverse, List.sum_reverse]
  omega

/-- The complete word retains source CNOTs and converts only actual payload X into CNOTs. -/
lemma program_cnot_count (width : Nat)
    (prepare middle : List (GateSpec (SharedEEA.encoding width))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program width prepare middle).eventCost =
        2 * (prepare.map GateSpec.cnotMultiplicity).sum +
          (middle.map GateSpec.xMultiplicity).sum := by
  simp only [program, GateSpec.programList_cnot_count_eq_sum, gates,
    List.map_append, List.sum_append, ControlledSourceWord.liftedGates_cnot_count,
    ControlledSourceWord.selectedGates_cnot_count, List.map_reverse, List.sum_reverse]
  omega

/-- Every native X belongs to one of the two original actual predicate computations. -/
lemma program_singleQubit_count (width : Nat)
    (prepare middle : List (GateSpec (SharedEEA.encoding width))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program width prepare middle).eventCost = 2 * (prepare.map GateSpec.xMultiplicity).sum := by
  simp only [program, GateSpec.programList_x_count_eq_sum, gates,
    List.map_append, List.sum_append, ControlledSourceWord.liftedGates_x_count,
    ControlledSourceWord.selectedGates_x_count, List.map_reverse, List.sum_reverse]
  omega

/-- The actual serial dependency duration charges every source and native selected payload gate. -/
lemma program_quantumTime (width : Nat)
    (prepare middle : List (GateSpec (SharedEEA.encoding width))) :
    (program width prepare middle).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * ((prepare.map GateSpec.toffoliMultiplicity).sum +
        (prepare.map GateSpec.cnotMultiplicity).sum + (prepare.map GateSpec.xMultiplicity).sum) +
          (middle.map GateSpec.xMultiplicity).sum + (middle.map GateSpec.cnotMultiplicity).sum +
            4 * (middle.map GateSpec.toffoliMultiplicity).sum := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty) (gates width prepare middle)
  change GateSpec.primitiveEventCount (program width prepare middle) = _ at native
  rw [GateSpec.primitiveEventCount, program_toffoli_count, program_cnot_count,
    program_singleQubit_count] at native
  rw [program, GateSpec.programList_quantumTime, ← native]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPredicated
