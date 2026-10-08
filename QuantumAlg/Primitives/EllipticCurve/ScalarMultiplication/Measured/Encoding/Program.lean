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
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (sourceEncoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (retainedWidth width)
    (MAU.Multiplication.Gidney.program width modulus coefficient)

/-- The real native two-word program is placed through its exact physical coordinate ports. -/
def nativeProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).toQuantum :=
  (placement width coordinate).place (extendedProgram width modulus coefficient)

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
  (placement width coordinate).place_realizes
    (UnitaryCircuit.Realizes.onBinaryPrefix
      (right := BinaryLabelEncoding.finIdentity (retainedWidth width))
      (MAU.Multiplication.Gidney.gidneyUnitMultiplication_realizes width modulus coefficient))

/-- Match each canonical frame wire to its original live measured-runtime position. -/
private def runtimePosition (width : Nat) :
    Fin (ProductPlacement.frameEncoding width).width ↪
      Fin (NumeratorMeasurement.context width).systemCount := by
  unfold NumeratorMeasurement.context
  exact (MAU.Inversion.SharedEEA.InverseRuntimeFrame.position width).trans
    (MeasurementCells.wireEquiv
      (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width).toEmbedding

private theorem runtimeDimensions (width : Nat)
    (index : Fin (ProductPlacement.frameEncoding width).width) :
    ((QubitLayout.canonical (ProductPlacement.frameEncoding width).width).toQuantum.wire
      index).dimension =
      ((NumeratorMeasurement.context width).quantumLayout.wire
        (runtimePosition width index)).dimension := by
  change _ =
    ((MeasurementCells.context (MAU.Inversion.SharedEEA.InversePreparation.after width)
      2 width).quantumLayout.wire
      (MeasurementCells.wireEquiv
        (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width
        (MAU.Inversion.SharedEEA.InverseRuntimeFrame.position width index))).dimension
  rw [MeasurementCells.wireEquiv_preserved]
  exact MAU.Inversion.SharedEEA.InverseRuntimeFrame.position_dimensions width index

private theorem runtimePosition_surjective (width : Nat) :
    Function.Surjective (runtimePosition width) := by
  intro target
  obtain ⟨old, rfl⟩ := (MeasurementCells.wireEquiv
    (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width).surjective target
  obtain ⟨index, same⟩ :=
    MAU.Inversion.SharedEEA.InverseRuntimeFrame.position_surjective width old
  exact ⟨index, congrArg (MeasurementCells.wireEquiv
    (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width) same⟩

/-- The selected physical basis is the original complete encoded frame basis. -/
private theorem runtimeSelected (width : Nat)
    (basis : (NumeratorMeasurement.context width).register.Index) :
    UnitaryCircuit.selectedInput
      (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).toQuantum
      (NumeratorMeasurement.context width).quantumLayout
      (runtimePosition width) (runtimeDimensions width) basis =
        (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm
          (NumeratorMeasurement.frameBasis width basis) := by
  obtain ⟨old, rfl⟩ := (MeasurementCells.basisEquiv
    (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width).surjective basis
  have same : UnitaryCircuit.selectedInput
      (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).toQuantum
      (NumeratorMeasurement.context width).quantumLayout
      (runtimePosition width) (runtimeDimensions width)
      (MeasurementCells.basisEquiv
        (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width old) =
        UnitaryCircuit.selectedInput
          (MAU.Inversion.SharedEEA.InverseRuntimeFrame.source width)
          (MAU.Inversion.SharedEEA.InversePreparation.after width).quantumLayout
          (MAU.Inversion.SharedEEA.InverseRuntimeFrame.position width)
          (MAU.Inversion.SharedEEA.InverseRuntimeFrame.position_dimensions width) old := by
    funext index
    apply Fin.ext
    exact MeasurementCells.basisEquiv_value
      (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width old
      (MAU.Inversion.SharedEEA.InverseRuntimeFrame.position width index)
  rw [same]
  exact (MAU.Inversion.SharedEEA.InverseRuntimeFrame.selectedBasis_eq_basisEquiv width old).trans
    (by
      change _ =
        (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm
        ((MAU.Inversion.SharedEEA.InverseAssembly.basisEquiv width)
          ((MeasurementCells.basisEquiv
            (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width).symm
              ((MeasurementCells.basisEquiv
                (MAU.Inversion.SharedEEA.InversePreparation.after width) 2 width) old)))
      rw [Equiv.symm_apply_apply]
      rfl)

/-- The same native program follows the actual runtime basis and lists every original wire. -/
def runtimeProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    UnitaryCircuit AlgorithmGate.model .empty
      (NumeratorMeasurement.context width).quantumLayout :=
  UnitaryCircuit.placeAt
    (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).toQuantum
    (NumeratorMeasurement.context width).quantumLayout
    (runtimePosition width) (runtimeDimensions width)
    (nativeProgram width modulus coefficient coordinate)

/-- Transport an exact native basis action to the complete live runtime frame. -/
theorem runtimeProgram_apply_ket (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (input output : Fin (2 ^ (ProductPlacement.frameEncoding width).width))
    (actual : (nativeProgram width modulus coefficient coordinate).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm
          input)) =
      NormalizedVector.ket
        ((QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm
          output)) :
    (runtimeProgram width modulus coefficient coordinate).applyNormalized
      (NormalizedVector.ket ((NumeratorMeasurement.frameBasis width).symm input)) =
    NormalizedVector.ket ((NumeratorMeasurement.frameBasis width).symm output) := by
  apply UnitaryCircuit.placeAt_applyNormalized_ket_of_eq
    (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).toQuantum
    (NumeratorMeasurement.context width).quantumLayout
    (runtimePosition width) (runtimeDimensions width)
    (nativeProgram width modulus coefficient coordinate)
    ((QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm input)
    ((QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm output)
    actual ((NumeratorMeasurement.frameBasis width).symm input)
    ((NumeratorMeasurement.frameBasis width).symm output)
  · rw [runtimeSelected]
    exact congrArg
      (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm
      ((NumeratorMeasurement.frameBasis width).apply_symm_apply input)
  · rw [runtimeSelected]
    exact congrArg
      (QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm
      ((NumeratorMeasurement.frameBasis width).apply_symm_apply output)
  · funext index
    obtain ⟨sourceIndex, same⟩ := runtimePosition_surjective width index.val
    have present : index.val ∈ Finset.univ.map (runtimePosition width) := by
      rw [← same]
      exact Finset.mem_map_of_mem _ (Finset.mem_univ sourceIndex)
    exact False.elim ((Finset.mem_compl.mp index.property) present)

/-- One actual unitary instruction keeps the original measured arithmetic context intact. -/
def originalCircuit (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  .unitary (runtimeProgram width modulus coefficient coordinate)

/-- One actual coordinate conversion retains every exponent, selector, history bit
and result cell. -/
def coordinateCircuit (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext width count) (readyContext width count) :=
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
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext width count) (readyContext width count) :=
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
