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
abbrev oracles (n : Nat) : OracleModel :=
  AmplitudeAmplificationSource.model n true true

private def sourcePositions (phases n : Nat) : Fin n ↪ Fin (phases + n) where
  toFun := Fin.natAdd phases
  inj' := by intro left right same; exact Fin.ext (by simpa using congrArg Fin.val same)

/-- One ordinary preparation on precisely the original source suffix. -/
def preparation (n : Nat) (t : Nat) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.ofPositions (oracles n) .preparation
    (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
    (sourcePositions (phaseWidth t n) n) (fun _ => rfl))

/-- One granted inverse preparation on exactly the same source positions. -/
def inversePreparation (n : Nat) (t : Nat) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.ofPositions (oracles n) (.inversePreparation rfl)
    (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
    (sourcePositions (phaseWidth t n) n) (fun _ => rfl))

/-- One granted controlled recognizer at the original selected phase bit. -/
def controlledGoodReflection (n : Nat) {t : Nat} (stage : Fin t) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.ofPositions (oracles n) (.controlledGoodReflection rfl)
    (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
    (QuantumPhaseEstimation.Native.sourcePositions n (extendedStage n stage)) (fun _ => rfl))

lemma preparation_eventCost (n : Nat) (t : Nat) :
    (preparation n t).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle AmplitudeAmplificationSource.Coordinate.preparation) := rfl

lemma inversePreparation_eventCost (n : Nat) (t : Nat) :
    (inversePreparation n t).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle AmplitudeAmplificationSource.Coordinate.inversePreparation) := rfl

lemma controlledGoodReflection_eventCost (n : Nat) {t : Nat} (stage : Fin t) :
    (controlledGoodReflection n stage).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle AmplitudeAmplificationSource.Coordinate.controlledGoodReflection) := rfl

lemma preparation_unitDepth (n : Nat) (t : Nat) :
    (preparation n t).evaluatedEventDepth (fun _ => 1) = 1 := rfl

lemma inversePreparation_unitDepth (n : Nat) (t : Nat) :
    (inversePreparation n t).evaluatedEventDepth (fun _ => 1) = 1 := rfl

lemma controlledGoodReflection_unitDepth (n : Nat) {t : Nat} (stage : Fin t) :
    (controlledGoodReflection n stage).evaluatedEventDepth (fun _ => 1) = 1 := rfl

end

end QuantumAlg.AmplitudeEstimation.Elementary
