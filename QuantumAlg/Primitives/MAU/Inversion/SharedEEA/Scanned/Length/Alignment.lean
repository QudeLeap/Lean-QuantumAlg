/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Barrel
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Uncontrolled

/-!
# Actual complete-metadata alignment for terminal length reads

Coefficient length reads use negative physical displacement by the old
divisor length. Divisor reads use positive displacement by the refreshed
coefficient length and an additional paid public one-position rotation.
Both choices emit actual native instructions on one original full word.
All metadata and the whole shared pool remain outside that word.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates

/-- Each write reads its other retained original length field. -/
def metadataField : Field → ArithmeticGeometry.Field
  | .coefficient => .divisor
  | .divisor => .coefficient

/-- The signs are fixed by the original physical source coordinate order. -/
def permutation (width : Nat) : Field → Equiv.Perm (Fin (width + 3))
  | .coefficient => (finRotate (width + 3))⁻¹
  | .divisor => finRotate (width + 3)

/-- Every original boundary bit controls a real native public-power permutation. -/
def barrelGates (width : Nat) (field : Field) (first : Bool) :
    List (GateSpec (encoding width)) :=
  (ArithmeticAlignment.barrel width first (metadataField field)).gates
    (permutation width field) (PermutationBarrel.binaryStages width.size)

/-- A public unit rotation is still an actual three-CNOT exchange word. -/
def publicGates (width : Nat) (field : Field) (first : Bool) :
    List (GateSpec (encoding width)) :=
  match field with
  | .coefficient => []
  | .divisor =>
      ((ArithmeticRotation.frame width first (SharedEEA.controlBit width)
        (by rw [SharedEEA.controlBit_wire]; omega))).uncontrolledGates
          (Permutation.transpositions (finRotate (width + 3)))

/-- The complete paid preparation is independent of every runtime boundary value. -/
def gates (width : Nat) (field : Field) (first : Bool) :
    List (GateSpec (encoding width)) :=
  barrelGates width field first ++ publicGates width field first

/-- The same physical program is used for every original label. -/
def program (width : Nat) (field : Field) (first : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width field first)

/-- Complete native ket semantics precede any arithmetic trajectory restriction. -/
lemma program_realizes (width : Nat) (field : Field) (first : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width field first) environment
      (GateSpec.stepList (gates width field first)) :=
  GateSpec.realizesList (QubitLayout.canonical _) .empty _ environment

/-- Complete finite metadata values supply the actual barrel displacement. -/
lemma barrel_bit_get (width : Nat) (field : Field) (first : Bool)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width first index).get
        (GateSpec.stepList (barrelGates width field first) state) =
      (ArithmeticRotation.bit width first
        ((permutation width field ^ (boundaryValue field state.1).toNat) index)).get state := by
  apply (ArithmeticAlignment.barrel width first (metadataField field)).binary_bit_get
  intro selected
  have actual := ArithmeticAlignment.control_get width first (metadataField field) selected state
  cases field <;> exact actual

/-- The additional public displacement also executes on inactive quantum-control branches. -/
lemma public_bit_get (width : Nat) (field : Field) (first : Bool)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width first index).get
        (GateSpec.stepList (publicGates width field first) state) =
      (ArithmeticRotation.bit width first
        (if field = .divisor then finRotate (width + 3) index else index)).get state := by
  cases field with
  | coefficient => rfl
  | divisor =>
      exact (ArithmeticRotation.frame width first (SharedEEA.controlBit width)
        (by rw [SharedEEA.controlBit_wire]; omega)).uncontrolled_fixed_get
          (finRotate (width + 3)) index state

/-- Every output bit has the exact chronological full-word displacement. -/
lemma gates_bit_get (width : Nat) (field : Field) (first : Bool)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width first index).get
        (GateSpec.stepList (gates width field first) state) =
      (ArithmeticRotation.bit width first
        ((permutation width field ^ (boundaryValue field state.1).toNat)
          (if field = .divisor then finRotate (width + 3) index else index))).get state := by
  rw [gates, GateSpec.stepList_append, public_bit_get, barrel_bit_get]

/-- All original systems outside the selected word retain their arbitrary values. -/
lemma gates_get_outside (width : Nat) (field : Field) (first : Bool)
    (observed : EncodedBit (encoding width))
    (outside : ∀ index, (ArithmeticRotation.bit width first index).wire ≠ observed.wire)
    (state : Data width) :
    observed.get (GateSpec.stepList (gates width field first) state) = observed.get state := by
  rw [gates, GateSpec.stepList_append]
  have public_read (value : Data width) :
      observed.get (GateSpec.stepList (publicGates width field first) value) =
        observed.get value := by
    cases field with
    | coefficient => rfl
    | divisor =>
        exact (ArithmeticRotation.frame width first (SharedEEA.controlBit width)
          (by rw [SharedEEA.controlBit_wire]; omega)).uncontrolled_get_outside
            _ observed outside value
  rw [public_read]
  exact (ArithmeticAlignment.barrel width first (metadataField field)).gates_get_outside
    _ _ observed outside state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment
