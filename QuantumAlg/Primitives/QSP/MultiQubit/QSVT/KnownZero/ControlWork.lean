/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Phase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase.Controlled
import all QuantumAlg.Components.Gates.Construction

/-!
# Native phase words borrowing an original control wire

The source suffix is grouped as k controls, one final control, and n signal
wires. The final control serves as restored work for the first k controls.
No positive signal-width assumption is needed to construct this word.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

/-- Phase wire, first controls, final control, then original signal wires. -/
abbrev layout (k n : Nat) := ProjectorPhase.layout (k + (1 + n))

private def lastControl (k n : Nat) : Fin (1 + (k + (1 + n))) :=
  Fin.natAdd 1 (Fin.natAdd k (0 : Fin (1 + n)))

private theorem lastControl_ne_phase (k n : Nat) : lastControl k n ≠ 0 := by
  intro same
  have values := congrArg Fin.val same
  change 1 + (k + 0) = 0 at values
  omega

/-- An actual zero-controlled phase-wire flip using the final original control. -/
def lastFlip (k n : Nat) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  let mask := Gate.singleQubitAt (layout k n) oracles Gate.XOp (lastControl k n) rfl
  (mask.seq (Gate.cnotAt (layout k n) oracles (lastControl k n)
    (0 : Fin (1 + (k + (1 + n))))
    (lastControl_ne_phase k n) rfl rfl)).seq mask

/-- The first controls borrow and restore the final control, even when there are no signal wires. -/
def firstRotation (k n : Nat) (oracles : OracleModel) (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  ProjectorPhase.controlledRotation (KnownZero.flip k (1 + n) (by omega) oracles) angle

/-- Two conditional half rotations and two final-control flips form the intersection word. -/
def intersectionRotation (k n : Nat) (oracles : OracleModel) (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  (((firstRotation k n oracles (angle / 2)).seq (lastFlip k n oracles)).seq
    (firstRotation k n oracles (-(angle / 2)))).seq (lastFlip k n oracles)

/-- The unconditional source phase followed by the intersection-controlled correction. -/
def phase (k n : Nat) (oracles : OracleModel) (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  (Gate.singleQubitAt (layout k n) oracles (rotZStdOp (2 * angle))
    (0 : Fin (1 + (k + (1 + n)))) rfl).seq
    (intersectionRotation k n oracles (-4 * angle))

/-- The final-control flip retains both masks and its native CNOT. -/
theorem controlWork_lastFlip_depth (k n : Nat) (oracles : OracleModel) :
    (lastFlip k n oracles).evaluatedEventDepth (fun _ => 1) = 3 := rfl

/-- The complete word has linear depth in the number of original controls, including n=0. -/
theorem controlWork_phase_depth (k n : Nat) (oracles : OracleModel) (angle : ℝ) :
    (phase k n oracles angle).evaluatedEventDepth (fun _ => 1) =
      4 * (2 * k + EncodedBit.Word.OneDirtyLayout.gateCount k) + 11 := by
  simp only [phase, intersectionRotation, UnitaryCircuit.evaluatedEventDepth_seq,
    firstRotation, ProjectorPhase.controlledRotation_depth, KnownZero.flip_depth,
    controlWork_lastFlip_depth]
  change 1 + ((2 * (2 * k + EncodedBit.Word.OneDirtyLayout.gateCount k) + 2 + 3 +
    (2 * (2 * k + EncodedBit.Word.OneDirtyLayout.gateCount k) + 2)) + 3) = _
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
