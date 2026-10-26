/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Rotation.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Correction.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Cleanup.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Correction.Program

/-!
# Actual modular doubling on two original quantum words and one flag

The original source word supplies all dirty borrowing. The target is rotated,
corrected under its original high bit, conditionally reduced, then used to
clear the original reduction flag. The inverse retains every instruction.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

def doublingGates : List (GateSpec encoding) :=
  rotationGates ++ evenCorrectionGates ++ complementCarryGates ++
    Correction.correctionGates ++ Cleanup.cleanupGates

def doublingProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty doublingGates

/-- Full action for every label, without discarding the original complement or flag. -/
def doublingStep (state : Registers) : Registers :=
  Cleanup.cleanupStep (Correction.correctionStep (complementCarryStep
    (evenCorrectionStep (stepList rotationGates state))))

lemma doublingGates_step (state : Registers) :
    stepList doublingGates state = doublingStep state := by
  rw [doublingGates, stepList_append, stepList_append, stepList_append, stepList_append,
    evenCorrectionGates_step, complementCarryGates_step, Correction.correctionGates_step]
  rfl

/-- Complete native unitary realization preserves every relative phase and external reference. -/
lemma doubling_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding doublingProgram environment doublingStep :=
  realizesList_congrStep (QubitLayout.canonical _) .empty doublingGates doublingGates_step
    environment

def inverseDoublingGates : List (GateSpec encoding) := doublingGates.reverse

def inverseDoublingProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty inverseDoublingGates

/-- The literal complete adjoint restores the entire original physical frame. -/
lemma inverseDoubling_doubling (state : Registers) :
    stepList inverseDoublingGates (doublingStep state) = state := by
  rw [← doublingGates_step]
  exact stepList_reverse_stepList doublingGates state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
