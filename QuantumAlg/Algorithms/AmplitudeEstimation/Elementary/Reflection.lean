/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.PhaseProgram
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Program
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

private abbrev physical (width : Nat) : QubitLayout width where
  physical_idx := Fin.val
  physical_idx_injective := Fin.val_injective

/-- The selected source reflection uses the original phase control and existing work position. -/
def reflection (oracles : OracleModel) {t : Nat} : (n : Nat) → Fin t →
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
  | 0, stage => ZeroReflection.SmallPhase.program oracles (phaseWidth t 0) 0
      (physical (totalQubits t 0)) (by omega) (controlWire 0 stage)
  | 1, stage => ZeroReflection.SmallPhase.program oracles (phaseWidth t 1) 1
      (physical (totalQubits t 1)) (by omega) (controlWire 1 stage)
  | 2, stage => ZeroReflection.SmallPhase.program oracles (phaseWidth t 2) 2
      (physical (totalQubits t 2)) (by omega) (controlWire 2 stage)
  | extra + 3, stage => ZeroReflection.PhaseWorkspace.program oracles
      (phaseWidth t (extra + 3)) (extra + 2) (physical (totalQubits t (extra + 3)))
      (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
      (controlWire_ne_workWire (extra + 3) stage (by omega))

/-- Full-register action restores every phase and work coordinate on both control branches. -/
lemma reflection_applyVec_pair (oracles : OracleModel) {environment : oracles.Interpretation}
    {t : Nat} (n : Nat) (stage : Fin t)
    (phase : Fin (2 ^ phaseWidth t n)) (source : Fin (2 ^ n)) :
    (reflection oracles n stage).applyVec environment
        (NormalizedVector.ket (R := (physical (totalQubits t n)).toQuantum.register)
          ((physical (totalQubits t n)).basisEquiv.symm (prodEquiv (phase, source)))).vec =
      if (BinaryLabelEncoding.finIdentityBit (phaseWidth t n) (controlWire n stage)).get phase then
        if source = 0 then
          (NormalizedVector.ket (R := (physical (totalQubits t n)).toQuantum.register)
          ((physical (totalQubits t n)).basisEquiv.symm (prodEquiv (phase, source)))).vec
        else -(NormalizedVector.ket (R := (physical (totalQubits t n)).toQuantum.register)
          ((physical (totalQubits t n)).basisEquiv.symm (prodEquiv (phase, source)))).vec
      else (NormalizedVector.ket (R := (physical (totalQubits t n)).toQuantum.register)
        ((physical (totalQubits t n)).basisEquiv.symm (prodEquiv (phase, source)))).vec := by
  match n with
  | 0 =>
      exact ZeroReflection.SmallPhase.program_applyVec_pair oracles
        (phaseWidth t 0) 0 (physical (totalQubits t 0)) (by omega) (controlWire 0 stage)
        phase source
  | 1 =>
      exact ZeroReflection.SmallPhase.program_applyVec_pair oracles
        (phaseWidth t 1) 1 (physical (totalQubits t 1)) (by decide) (controlWire 1 stage)
        phase source
  | 2 =>
      exact ZeroReflection.SmallPhase.program_applyVec_pair oracles
        (phaseWidth t 2) 2 (physical (totalQubits t 2)) (by decide) (controlWire 2 stage)
        phase source
  | extra + 3 =>
      exact ZeroReflection.PhaseWorkspace.program_applyVec_pair oracles
        (phaseWidth t (extra + 3)) (extra + 2)
        (physical (totalQubits t (extra + 3))) (controlWire (extra + 3) stage)
        (workWire (extra + 3) stage (by omega))
        (controlWire_ne_workWire (extra + 3) stage (by omega)) phase source

/-- The actual native coordinate pool is the independent width-only elementary formula. -/
lemma reflection_eventCost (oracles : OracleModel) {t : Nat} (n : Nat) (stage : Fin t) :
    (reflection oracles n stage).eventCost =
      ZeroReflection.controlledElementaryEventPool oracles n := by
  match n with
  | 0 =>
      exact ZeroReflection.SmallPhase.program_eventCost oracles
        (phaseWidth t 0) 0 (physical (totalQubits t 0)) (by omega) (controlWire 0 stage)
  | 1 =>
      exact ZeroReflection.SmallPhase.program_eventCost oracles
        (phaseWidth t 1) 1 (physical (totalQubits t 1)) (by decide) (controlWire 1 stage)
  | 2 =>
      exact ZeroReflection.SmallPhase.program_eventCost oracles
        (phaseWidth t 2) 2 (physical (totalQubits t 2)) (by decide) (controlWire 2 stage)
  | extra + 3 =>
      exact ZeroReflection.PhaseWorkspace.program_eventCost oracles
        (phaseWidth t (extra + 3)) (extra + 2)
        (physical (totalQubits t (extra + 3))) (by omega)
        (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
        (controlWire_ne_workWire (extra + 3) stage (by omega))

/-- Every selected elementary reflection runs sequentially with exactly its native gate count. -/
lemma reflection_unitDepth (oracles : OracleModel) {t : Nat} (n : Nat) (stage : Fin t) :
    (reflection oracles n stage).evaluatedEventDepth (fun _ => 1) =
      ZeroReflection.controlledElementaryGateCount n := by
  match n with
  | 0 =>
      exact ZeroReflection.SmallPhase.program_unitDepth oracles
        (phaseWidth t 0) 0 (physical (totalQubits t 0)) (by omega) (controlWire 0 stage)
  | 1 =>
      exact ZeroReflection.SmallPhase.program_unitDepth oracles
        (phaseWidth t 1) 1 (physical (totalQubits t 1)) (by decide) (controlWire 1 stage)
  | 2 =>
      exact ZeroReflection.SmallPhase.program_unitDepth oracles
        (phaseWidth t 2) 2 (physical (totalQubits t 2)) (by decide) (controlWire 2 stage)
  | extra + 3 =>
      exact ZeroReflection.PhaseWorkspace.program_unitDepth oracles
        (phaseWidth t (extra + 3)) (extra + 2)
        (physical (totalQubits t (extra + 3))) (by omega)
        (controlWire (extra + 3) stage) (workWire (extra + 3) stage (by omega))
        (controlWire_ne_workWire (extra + 3) stage (by omega))

end

end QuantumAlg.AmplitudeEstimation.Elementary
