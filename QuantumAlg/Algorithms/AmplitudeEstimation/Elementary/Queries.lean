/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Algorithms.QPE.Query
import all QuantumAlg.Algorithms.QPE.Query.Matrix
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Oracle.AmplitudeAmplification.Circuit
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Explicit source access in native amplitude estimation

Ordinary preparation and its explicitly granted inverse act on the source suffix.
The good recognizer has separately granted controlled access at the original
phase bit. Every other phase and work system remains in the same physical word.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

/-- Preparation, inverse preparation and controlled recognition are separately granted. -/
abbrev oracles {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) : OracleModel :=
  AmplitudeAmplificationSource.model U good true true

private def sourcePositions (phases n : Nat) : Fin n ↪ Fin (phases + n) where
  toFun := Fin.natAdd phases
  inj' := by intro left right same; exact Fin.ext (by simpa using congrArg Fin.val same)

/-- One ordinary preparation on precisely the original source suffix. -/
def preparation {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    UnitaryCircuit AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.ofPositions (oracles U good) .preparation
    (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
    (sourcePositions (phaseWidth t n) n) (fun _ => rfl))

/-- One granted inverse preparation on exactly the same source positions. -/
def inversePreparation {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    UnitaryCircuit AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.ofPositions (oracles U good) (.inversePreparation rfl)
    (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
    (sourcePositions (phaseWidth t n) n) (fun _ => rfl))

/-- One granted controlled recognizer at the original selected phase bit. -/
def controlledGoodReflection {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    UnitaryCircuit AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.ofPositions (oracles U good) (.controlledGoodReflection rfl)
    (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
    (QuantumPhaseEstimation.Native.sourcePositions n (extendedStage n stage)) (fun _ => rfl))

/-- The actual granted query has the original full controlled-bit matrix, including phase. -/
theorem controlledGoodReflection_matrix {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (controlledGoodReflection U good stage).binaryMatrix =
      qpeControlledBitOp (phaseWidth t n)
        (OrthogonalProjector.rankOnePhaseReflectionOp good) (extendedStage n stage) := by
  change (QuantumPhaseEstimation.Native.sourceQuery AlgorithmGate.model
    (OrthogonalProjector.rankOnePhaseReflectionOp good)
    (extendedStage n stage)).binaryMatrix = _
  exact QuantumPhaseEstimation.Native.qpeNative_sourceQuery_binaryMatrix
    AlgorithmGate.model (OrthogonalProjector.rankOnePhaseReflectionOp good) (extendedStage n stage)

theorem preparation_eventCost {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (preparation t U good).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle AmplitudeAmplificationSource.Coordinate.preparation) := rfl

theorem inversePreparation_eventCost {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (inversePreparation t U good).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle AmplitudeAmplificationSource.Coordinate.inversePreparation) := rfl

theorem controlledGoodReflection_eventCost {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (controlledGoodReflection U good stage).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle AmplitudeAmplificationSource.Coordinate.controlledGoodReflection) := rfl

theorem preparation_unitDepth {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (preparation t U good).evaluatedEventDepth (fun _ => 1) = 1 := rfl

theorem inversePreparation_unitDepth {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (inversePreparation t U good).evaluatedEventDepth (fun _ => 1) = 1 := rfl

theorem controlledGoodReflection_unitDepth {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (controlledGoodReflection U good stage).evaluatedEventDepth (fun _ => 1) = 1 := rfl

end

end QuantumAlg.AmplitudeEstimation.Elementary
