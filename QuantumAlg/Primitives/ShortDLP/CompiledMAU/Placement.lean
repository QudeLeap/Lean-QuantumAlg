/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Reassociate the same three physical short-DLP fields

These transport facts retain one flat bit string and every actual physical
identity. They introduce no system or event and support placement of the
second exponentiation after the untouched first exponent field.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Transport a sealed circuit across a proved equality of qubit counts.  This
does not permute wires: both the source and target are the same flat physical
bit string, with only the parenthesization of `Nat` addition changed. -/
def castProgram {sourceWidth targetWidth : Nat}
    (hwidth : sourceWidth = targetWidth)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical sourceWidth).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical targetWidth).toQuantum :=
  hwidth ▸ program

/-- Width transport preserves the strict event pool. -/
@[simp] theorem castProgram_eventCost {sourceWidth targetWidth : Nat}
    (hwidth : sourceWidth = targetWidth)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical sourceWidth).toQuantum) :
    (castProgram hwidth program).eventCost = program.eventCost := by
  subst targetWidth
  rfl

/-- Width transport preserves the strict event critical path. -/
@[simp] theorem castProgram_eventDepth {sourceWidth targetWidth : Nat}
    (hwidth : sourceWidth = targetWidth)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical sourceWidth).toQuantum) :
    (castProgram hwidth program).eventDepth = program.eventDepth := by
  subst targetWidth
  rfl

/-- Width transport retains the exact native and query event sequence. -/
@[simp] theorem castProgram_eventTrace {sourceWidth targetWidth : Nat}
    (hwidth : sourceWidth = targetWidth)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical sourceWidth).toQuantum) :
    (castProgram hwidth program).eventTrace = program.eventTrace := by
  subst targetWidth
  rfl

/-- Transport a basis label across the same width equality. -/
def castLabel {sourceWidth targetWidth : Nat}
    (hwidth : sourceWidth = targetWidth)
    (label : Fin (2 ^ sourceWidth)) : Fin (2 ^ targetWidth) :=
  Fin.cast (congrArg (fun width => 2 ^ width) hwidth) label

/-- Width transport preserves a proved computational-basis action. -/
theorem applyNormalized_castProgram {sourceWidth targetWidth : Nat}
    (hwidth : sourceWidth = targetWidth)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical sourceWidth).toQuantum)
    (input output : Fin (2 ^ sourceWidth))
    (happly : program.applyNormalized (NormalizedVector.ket
      ((QubitLayout.canonical sourceWidth).basisEquiv.symm input)) =
      NormalizedVector.ket
        ((QubitLayout.canonical sourceWidth).basisEquiv.symm output)) :
    (castProgram hwidth program).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical targetWidth).basisEquiv.symm
            (castLabel hwidth input))) =
      NormalizedVector.ket
        ((QubitLayout.canonical targetWidth).basisEquiv.symm
          (castLabel hwidth output)) := by
  subst targetWidth
  simpa [castLabel, castProgram] using happly

/-- Reassociate the three consecutive fields without changing a basis-label
value or any physical wire address. -/
def reassociateLabel (left middle right : Nat) :
    Fin (2 ^ (left + (middle + right))) →
      Fin (2 ^ (left + middle + right)) :=
  castLabel (Nat.add_assoc left middle right).symm

/-- Any proof of the associativity equality transports the right-associated
and left-associated three-field encodings to the same flat physical label. -/
theorem castLabel_prodEquiv
    {left middle right : Nat}
    (hwidth : left + (middle + right) = left + middle + right)
    (leftLabel : Fin (2 ^ left)) (middleLabel : Fin (2 ^ middle))
    (rightLabel : Fin (2 ^ right)) :
    castLabel hwidth
        (prodEquiv (leftLabel, prodEquiv (middleLabel, rightLabel))) =
      prodEquiv (prodEquiv (leftLabel, middleLabel), rightLabel) := by
  apply Fin.ext
  simp [castLabel, prodEquiv, pow_add, Nat.add_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

/-- The canonical reassociation proof preserves the three-field basis label. -/
theorem reassociateLabel_prodEquiv
    {left middle right : Nat}
    (leftLabel : Fin (2 ^ left)) (middleLabel : Fin (2 ^ middle))
    (rightLabel : Fin (2 ^ right)) :
    reassociateLabel left middle right
        (prodEquiv (leftLabel, prodEquiv (middleLabel, rightLabel))) =
      prodEquiv (prodEquiv (leftLabel, middleLabel), rightLabel) :=
  castLabel_prodEquiv (Nat.add_assoc left middle right).symm
    leftLabel middleLabel rightLabel

end

end QuantumAlg.ShortDLP.CompiledMAU
