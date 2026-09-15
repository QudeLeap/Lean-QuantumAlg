/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Placement
import all QuantumAlg.Core.Execution.Local.Framing.Resources

/-!
# Actual constant-unit conversion in the complete measured scalar workspace

The existing Gidney multiplier acts on one coordinate and the existing A
word, with all original history and finite cells retained. Framing keeps
every exponent and the selector physically resident. Pair conversion runs
X then Y, using the same A word for both actual invocations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open MeasuredUncompute Execution

private def extendedProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryCircuit (Qubits (sourceEncoding width).width) :=
  UnitaryCircuit.prodLeft (n := retainedWidth width)
    (MAU.Multiplication.Gidney.program width modulus coefficient)

private theorem extended_within (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (extendedProgram width modulus coefficient).physical_idx ⊆
      List.range (sourceEncoding width).width := by
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  rw [MAU.Multiplication.Gidney.gidneyUnitMultiplication_physical]
  change List.range (2 * width) ⊆ List.range (width + width)
  rw [two_mul]
  exact List.Subset.refl _

/-- The real native two-word program is placed through its exact physical coordinate ports. -/
def nativeProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    UnitaryCircuit (Qubits (ProductPlacement.frameEncoding width).width) :=
  (placement width coordinate).place (extendedProgram width modulus coefficient)
    (extended_within width modulus coefficient)

/-- Independent two-word multiplication in the grouping induced by actual physical ports. -/
def nativeAction (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    ProductPlacement.Frame width → ProductPlacement.Frame width :=
  (placement width coordinate).step (fun state =>
    (Nat.FixedWidth.unitMultiplicationPairEquiv modulus coefficient state.1, state.2))

/-- Every full basis label follows the actual placed multiplier exactly, including history. -/
theorem nativeProgram_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    UnitaryCircuit.Realizes (ProductPlacement.frameEncoding width)
      (nativeProgram width modulus coefficient coordinate)
      (nativeAction width modulus coefficient coordinate) :=
  (placement width coordinate).place_realizes (extended_within width modulus coefficient)
    (UnitaryCircuit.Realizes.prodLeft
      (right := BinaryLabelEncoding.finIdentity (retainedWidth width))
      (MAU.Multiplication.Gidney.gidneyUnitMultiplication_realizes width modulus coefficient))

/-- The declared native footprint contains the complete existing arithmetic frame. -/
theorem nativeProgram_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    (nativeProgram width modulus coefficient coordinate).physical_idx =
      List.range (ProductPlacement.frameEncoding width).width :=
  EncodedBit.FullPlacement.place_physical _ _ _

/-- The same native program follows the actual runtime basis and lists every original wire. -/
def runtimeProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    UnitaryCircuit (NumeratorMeasurement.context width).register :=
  (UnitaryCircuit.reindex (NumeratorMeasurement.frameBasis width).symm
    (nativeProgram width modulus coefficient coordinate)).seq
      (.identity (NumeratorMeasurement.context width).register
        (NumeratorMeasurement.context width).physicalIdx
        (NumeratorMeasurement.context width).identitiesNodup)

/-- All placed leaves address actual original wires in the retained-cell runtime context. -/
theorem runtimeProgram_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    (runtimeProgram width modulus coefficient coordinate).physical_idx =
      (NumeratorMeasurement.context width).physicalIdx := by
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  intro wire present
  change wire ∈ (nativeProgram width modulus coefficient coordinate).physical_idx at present
  rw [nativeProgram_physical] at present
  change wire ∈ (NumeratorMeasurement.context width).physicalIdx
  rw [NumeratorMeasurement.context_physical]
  exact MAU.Inversion.SharedEEA.InverseRuntimeFrame.range_contained width present

/-- One actual unitary instruction keeps the original measured arithmetic context intact. -/
def originalCircuit (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    Circuit (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  .unitary (runtimeProgram width modulus coefficient coordinate)
    (runtimeProgram_physical width modulus coefficient coordinate)

/-- One actual coordinate conversion retains every exponent, selector, history bit
and result cell. -/
def coordinateCircuit (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    Circuit (readyContext width count) (readyContext width count) :=
  ContextUnion.frameLocal (originalCircuit width modulus coefficient coordinate) (by trivial)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)

/-- The coordinate conversion allocates and releases no runtime entry. -/
theorem coordinateCircuit_isLocal (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    (coordinateCircuit width count modulus coefficient coordinate).IsLocal :=
  ContextUnion.frameLocal_isLocal _ _ _ _

/-- Conversion of both original coordinates performs two real multiplier invocations
on one A word. -/
def pairCircuit (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    Circuit (readyContext width count) (readyContext width count) :=
  (coordinateCircuit width count modulus coefficient .x).seq
    (coordinateCircuit width count modulus coefficient .y)

/-- Both coordinate invocations retain exactly the same full context. -/
theorem pairCircuit_isLocal (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (pairCircuit width count modulus coefficient).IsLocal :=
  ⟨coordinateCircuit_isLocal _ _ _ _ _, coordinateCircuit_isLocal _ _ _ _ _⟩

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
