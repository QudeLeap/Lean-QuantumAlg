/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Parallel.Resources

/-! # Actual paired alignment with complete original two-word semantics -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Parallel

noncomputable section

open EncodedBit

def frame (width : Nat) (field : ArithmeticGeometry.Field) :
    PermutationBarrelParallel.Frame (Scanned.encoding width) (width + 3) width.size where
  left := ArithmeticAlignment.barrel width true field
  rightBit := ArithmeticRotation.bit width false
  rightDistinct := (ArithmeticAlignment.barrel width false field).distinct
  cross := by
    intro first second same
    have values := congrArg Fin.val same
    change (ArithmeticRotation.bit width true first).wire.val =
      (ArithmeticRotation.bit width false second).wire.val at values
    rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
    simp at values
    have within := first.isLt
    omega
  rightControl := (ArithmeticAlignment.barrel width false field).separate

/-- The same original second-word placement and full metadata controls are retained literally. -/
lemma frame_rightBarrel (width : Nat) (field : ArithmeticGeometry.Field) :
    (frame width field).rightBarrel = ArithmeticAlignment.barrel width false field := rfl

/-- Both original complete barrel source lists occur in the unchanged mathematical source order. -/
lemma serialGates_eq (width : Nat) (field : ArithmeticGeometry.Field) :
    (frame width field).serialGates (ArithmeticAlignment.permutation width)
        (PermutationBarrel.binaryStages width.size) = ArithmeticAlignment.pairGates width field :=
  rfl

/-- Actual native alignment on the identical original quantum carrier, with no new allocation. -/
def pairProgram (width : Nat) (field : ArithmeticGeometry.Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  (frame width field).program (QubitLayout.canonical _) .empty
    (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size)

/-- Full same-source semantics include every old finite metadata and arbitrary work value. -/
lemma pairProgram_realizes (width : Nat) (field : ArithmeticGeometry.Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (Scanned.encoding width) (pairProgram width field) environment
      (GateSpec.stepList (ArithmeticAlignment.pairGates width field)) := by
  have actual := (frame width field).program_realizes (QubitLayout.canonical _) .empty
    (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size) environment
  rw [serialGates_eq] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Parallel
