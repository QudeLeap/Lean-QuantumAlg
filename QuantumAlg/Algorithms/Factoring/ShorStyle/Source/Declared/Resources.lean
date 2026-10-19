/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources
import all QuantumAlg.Primitives.QFT.Native.Inverse.Depth

/-!
# Independent resources of a declared Shor member

The closed pool includes the original phase Hadamards, every native inverse
Fourier gate, and one ordinary modular-exponentiation query. These exact
counts belong to the selected member even in an arbitrary surrounding
classical model. Runtime preparation, measurement, reset and classical
processing are separate instructions and are not included in this pure word.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource

noncomputable section

variable (width phaseBits : Nat)

/-- The independently stated native pool of the complete three-stage member. -/
def eventEnvelope (operations : ClassicalOpModel := .empty)
    (services : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum AlgorithmGate.model (model width phaseBits) operations services) :=
  ResourcePool.singleton (model := .quantum AlgorithmGate.model (model width phaseBits)
      operations services) (.gate .singleQubit) (2 * phaseBits + 3 * phaseBits.choose 2) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model (model width phaseBits)
      operations services) (.gate .cnot)
      (2 * phaseBits.choose 2 + 3 * (phaseBits / 2)) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model (model width phaseBits)
      operations services) (.oracle .modularExponentiation)

/-- The independent sequential depth includes parallel preparation, one query and native readout. -/
def depthBudget (phaseBits : Nat) : Nat :=
  (if phaseBits = 0 then 0 else 1) + 1 +
    (phaseBits + 5 * phaseBits.choose 2 + (if phaseBits / 2 = 0 then 0 else 3))

/-- Exactly one ordinary query is charged by the actual selected query instruction. -/
lemma oracleLayer_eventCost (gates : GateModel) (base : Fin (2 ^ width))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    (oracleLayer width phaseBits gates base).eventCost operations services =
      ResourcePool.singleton
        (model := .quantum gates (model width phaseBits) operations services)
        (.oracle .modularExponentiation) := by
  rfl

/-- Count each actual native gate or query in the complete selected member. -/
lemma circuit_event_count (base : Fin (2 ^ width))
    (event : Resource.Event (.quantum AlgorithmGate.model (model width phaseBits))) :
    ResourcePool.count event (circuit width phaseBits base).eventCost =
      (2 * phaseBits + 3 * phaseBits.choose 2) *
        (if .gate .singleQubit = event then 1 else 0) +
      (2 * phaseBits.choose 2 + 3 * (phaseBits / 2)) *
        (if .gate .cnot = event then 1 else 0) +
      (if .oracle .modularExponentiation = event then 1 else 0) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    initialLayer, readoutLayer,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    Gate.HadamardLayer.hadamardLayer_circuit_eventCost (model width phaseBits) phaseBits,
    oracleLayer_eventCost,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count
      (model width phaseBits) event phaseBits]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton]
  ring

/-- The independent event formula equals the actual pool in every classical context. -/
lemma circuit_eventCost_eq_envelope (base : Fin (2 ^ width))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    (circuit width phaseBits base).eventCost operations services =
      eventEnvelope width phaseBits operations services := by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((circuit width phaseBits base).eventCost operations services) =
      ResourcePool.count event (eventEnvelope width phaseBits operations services)
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      cases coordinate <;> simp [circuit_event_count, eventEnvelope]
  | oracle coordinate =>
      cases coordinate; simp [circuit_event_count, eventEnvelope]
  | classicalOperation coordinate => simp [eventEnvelope]
  | classicalQuery coordinate => simp [eventEnvelope]
  | preparation dimension => simp [eventEnvelope]
  | measurement dimension => simp [eventEnvelope]

/-- Every selected base consumes exactly one ordinary query in the same fixed model. -/
lemma circuit_queryCount (base : Fin (2 ^ width))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model (model width phaseBits) operations services)
        (.oracle .modularExponentiation)
        ((circuit width phaseBits base).eventCost operations services) = 1 := by
  rw [circuit_eventCost_eq_envelope width phaseBits base operations services]
  simp [eventEnvelope]

/-- Native single-qubit instructions include both Hadamard preparation and inverse-QFT gates. -/
lemma circuit_singleQubitCount (base : Fin (2 ^ width))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model (model width phaseBits) operations services)
        (.gate .singleQubit)
        ((circuit width phaseBits base).eventCost operations services) =
      2 * phaseBits + 3 * phaseBits.choose 2 := by
  rw [circuit_eventCost_eq_envelope width phaseBits base operations services]
  simp [eventEnvelope]

/-- Every controlled phase and final swap contributes its actual inverse-QFT CNOTs. -/
lemma circuit_cnotCount (base : Fin (2 ^ width))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model (model width phaseBits) operations services)
        (.gate .cnot)
        ((circuit width phaseBits base).eventCost operations services) =
      2 * phaseBits.choose 2 + 3 * (phaseBits / 2) := by
  rw [circuit_eventCost_eq_envelope width phaseBits base operations services]
  simp [eventEnvelope]

/-- The declared-query member's actual native peripherals contain no Toffoli instruction. -/
lemma circuit_toffoliCount (base : Fin (2 ^ width))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model (model width phaseBits) operations services)
        (.gate .toffoli)
        ((circuit width phaseBits base).eventCost operations services) = 0 := by
  rw [circuit_eventCost_eq_envelope width phaseBits base operations services]
  simp [eventEnvelope]

/-- Parallel phase preparation has one layer exactly when the phase register is nonempty. -/
lemma initialLayer_unit_depth :
    (initialLayer width phaseBits).evaluatedEventDepth (fun _ => 1) =
      if phaseBits = 0 then 0 else 1 := by
  rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth (model width phaseBits) phaseBits

/-- One ordinary query is one dependency step of the pure member. -/
lemma oracleLayer_unit_depth (gates : GateModel) (base : Fin (2 ^ width)) :
    (oracleLayer width phaseBits gates base).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

/-- The actual generated inverse QFT retains every sequential native layer. -/
lemma readoutLayer_unit_depth :
    (readoutLayer width phaseBits).evaluatedEventDepth (fun _ => 1) =
      phaseBits + 5 * phaseBits.choose 2 + (if phaseBits / 2 = 0 then 0 else 3) := by
  rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth
    (model width phaseBits) phaseBits

/-- The exact member depth equals its independently stated sequential budget. -/
lemma circuit_unit_depth (base : Fin (2 ^ width)) :
    (circuit width phaseBits base).evaluatedEventDepth (fun _ => 1) =
      depthBudget phaseBits := by
  change (initialLayer width phaseBits).evaluatedEventDepth (fun _ => 1) +
    (oracleLayer width phaseBits AlgorithmGate.model base).evaluatedEventDepth (fun _ => 1) +
      (readoutLayer width phaseBits).evaluatedEventDepth (fun _ => 1) = _
  rw [initialLayer_unit_depth, oracleLayer_unit_depth, readoutLayer_unit_depth]
  rfl

/-- Selecting classical operations or services preserves the actual quantum dependency depth. -/
lemma circuit_unit_depth_classical_context (base : Fin (2 ^ width))
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    DepthExpr.depthEval (fun _ => 1)
        ((circuit width phaseBits base).eventDepth operations services) =
      depthBudget phaseBits := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context, circuit_unit_depth]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource
