/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.PhaseProgram
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Support
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding

/-!
# The actual minimal-work controlled reflection in amplitude estimation

Small sources use their literal work-free controlled circuits. Larger sources
use the selected existing phase position, or the explicitly present exceptional
work position. Every basis value is restored on both control branches; the
phase is exactly the source's positive zero reflection, including global sign.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

/-- The actual elementary S0 selected at the source width and original phase control. -/
def reflection {t : Nat} : (n : Nat) → Fin t → UnitaryCircuit (Qubits (totalQubits t n))
  | 0, stage =>
      ZeroReflection.SmallPhase.program (phaseWidth t 0) 0 (by omega) (controlWire 0 stage)
  | 1, stage =>
      ZeroReflection.SmallPhase.program (phaseWidth t 1) 1 (by omega) (controlWire 1 stage)
  | 2, stage =>
      ZeroReflection.SmallPhase.program (phaseWidth t 2) 2 (by omega) (controlWire 2 stage)
  | extra + 3, stage => ZeroReflection.PhaseWorkspace.program (phaseWidth t (extra + 3)) (extra + 2)
      (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
      (controlWire_ne_workWire (extra + 3) stage (by omega))

/-- Containment follows from the addresses of the actual elementary leaves. -/
theorem reflection_physical_idx_subset_range {t : Nat} (n : Nat) (stage : Fin t) :
    (reflection n stage).physical_idx ⊆ List.range (totalQubits t n) := by
  match n with
  | 0 =>
      exact ZeroReflection.SmallPhase.program_physical_idx_subset_range
        (phaseWidth t 0) 0 (by omega) (controlWire 0 stage)
  | 1 =>
      exact ZeroReflection.SmallPhase.program_physical_idx_subset_range
        (phaseWidth t 1) 1 (by decide) (controlWire 1 stage)
  | 2 =>
      exact ZeroReflection.SmallPhase.program_physical_idx_subset_range
        (phaseWidth t 2) 2 (by decide) (controlWire 2 stage)
  | extra + 3 =>
      exact ZeroReflection.PhaseWorkspace.program_physical_idx_subset_range
        (phaseWidth t (extra + 3)) (extra + 2)
        (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
        (controlWire_ne_workWire (extra + 3) stage (by omega))

/-- Full-register action restores every phase and work coordinate on both control branches. -/
theorem reflection_applyVec_pair {t : Nat} (n : Nat) (stage : Fin t)
    (phase : Fin (2 ^ phaseWidth t n)) (source : Fin (2 ^ n)) :
    (reflection n stage).applyVec
        (NormalizedVector.ket (R := Qubits (totalQubits t n)) (prodEquiv (phase, source))).vec =
      if (BinaryLabelEncoding.finIdentityBit (phaseWidth t n) (controlWire n stage)).get phase then
        if source = 0 then
          (NormalizedVector.ket (R := Qubits (totalQubits t n)) (prodEquiv (phase, source))).vec
        else -(NormalizedVector.ket (R := Qubits (totalQubits t n)) (prodEquiv (phase, source))).vec
      else (NormalizedVector.ket (R := Qubits (totalQubits t n))
        (prodEquiv (phase, source))).vec := by
  match n with
  | 0 =>
      exact ZeroReflection.SmallPhase.program_applyVec_pair
        (phaseWidth t 0) 0 (by omega) (controlWire 0 stage) phase source
  | 1 =>
      exact ZeroReflection.SmallPhase.program_applyVec_pair
        (phaseWidth t 1) 1 (by decide) (controlWire 1 stage) phase source
  | 2 =>
      exact ZeroReflection.SmallPhase.program_applyVec_pair
        (phaseWidth t 2) 2 (by decide) (controlWire 2 stage) phase source
  | extra + 3 =>
      exact ZeroReflection.PhaseWorkspace.program_applyVec_pair
        (phaseWidth t (extra + 3)) (extra + 2)
        (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
        (controlWire_ne_workWire (extra + 3) stage (by omega)) phase source

/-- The actual native coordinate pool is the independent width-only elementary formula. -/
theorem reflection_eventCost {t : Nat} (n : Nat) (stage : Fin t) :
    (reflection n stage).eventCost = ZeroReflection.controlledElementaryEventPool n := by
  match n with
  | 0 =>
      exact ZeroReflection.SmallPhase.program_eventCost
        (phaseWidth t 0) 0 (by omega) (controlWire 0 stage)
  | 1 =>
      exact ZeroReflection.SmallPhase.program_eventCost
        (phaseWidth t 1) 1 (by decide) (controlWire 1 stage)
  | 2 =>
      exact ZeroReflection.SmallPhase.program_eventCost
        (phaseWidth t 2) 2 (by decide) (controlWire 2 stage)
  | extra + 3 =>
      exact ZeroReflection.PhaseWorkspace.program_eventCost
        (phaseWidth t (extra + 3)) (extra + 2) (by omega)
        (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
        (controlWire_ne_workWire (extra + 3) stage (by omega))

/-- Every selected elementary reflection runs sequentially with exactly its native gate count. -/
theorem reflection_unitDepth {t : Nat} (n : Nat) (stage : Fin t) :
    (reflection n stage).evaluatedEventDepth (fun _ => 1) =
      ZeroReflection.controlledElementaryGateCount n := by
  match n with
  | 0 =>
      exact ZeroReflection.SmallPhase.program_unitDepth
        (phaseWidth t 0) 0 (by omega) (controlWire 0 stage)
  | 1 =>
      exact ZeroReflection.SmallPhase.program_unitDepth
        (phaseWidth t 1) 1 (by decide) (controlWire 1 stage)
  | 2 =>
      exact ZeroReflection.SmallPhase.program_unitDepth
        (phaseWidth t 2) 2 (by decide) (controlWire 2 stage)
  | extra + 3 =>
      exact ZeroReflection.PhaseWorkspace.program_unitDepth
        (phaseWidth t (extra + 3)) (extra + 2) (by omega)
        (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
        (controlWire_ne_workWire (extra + 3) stage (by omega))

end

end QuantumAlg.AmplitudeEstimation.Elementary
