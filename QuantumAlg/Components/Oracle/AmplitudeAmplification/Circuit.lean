/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.AmplitudeAmplification
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Actual granted amplitude-amplification queries

A source occurrence fixes its coordinate and dimensions through the selected
oracle declaration; the environment supplies its operator. Placement supplies only the actual
  physical wires. Inverse and
controlled calls consume the grant evidence required by that model.
-/

namespace QuantumAlg.AmplitudeAmplificationSource.Circuit

noncomputable section

variable (gates : GateModel) (width : Nat)
  (allowInverse allowControlledGood : Bool)

/-- Execute one available source instance at its complete dimension-correct placement. -/
def program (query : Query allowInverse allowControlledGood)
    (placement : ((model width allowInverse allowControlledGood).signature query).Placement) :
    UnitaryCircuit gates (model width allowInverse allowControlledGood) placement.layout :=
  .query (OracleModel.Application.onPlacement
    (model width allowInverse allowControlledGood) query placement)

/-- The complete matrix is fixed by the declared query, with exact physical coordinate transport. -/
lemma program_matrix
    (environment : (model width allowInverse allowControlledGood).Interpretation)
    (query : Query allowInverse allowControlledGood)
    (placement : ((model width allowInverse allowControlledGood).signature query).Placement) :
    (program gates width allowInverse allowControlledGood query placement).matrix environment =
      UnitaryOperator.reindex placement.indexEquiv.symm
        (environment.operator query) := by
  rw [program, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  rfl

/-- One actual call contributes exactly its declared coordinate to the query ledger. -/
lemma program_eventCost (query : Query allowInverse allowControlledGood)
    (placement : ((model width allowInverse allowControlledGood).signature query).Placement) :
    (program gates width allowInverse allowControlledGood query placement).eventCost =
      ResourcePool.singleton
        (model := .quantum gates (model width allowInverse allowControlledGood))
        (.oracle ((model width allowInverse allowControlledGood).coordinate query)) := rfl

/-- One granted source query occupies one abstract dependency step. -/
lemma program_unitDepth (query : Query allowInverse allowControlledGood)
    (placement : ((model width allowInverse allowControlledGood).signature query).Placement) :
    (program gates width allowInverse allowControlledGood query placement).evaluatedEventDepth
        (fun _ => 1) = 1 := rfl

/-- Place the declared preparation call on exactly the supplied source wires. -/
def preparation (physical : QubitLayout width) :
    UnitaryCircuit gates (model width allowInverse allowControlledGood) physical.toQuantum :=
  program gates width allowInverse allowControlledGood .preparation
    ((QuantumSignature.qubits width).place physical.physical_idx physical.physical_idx_injective)

/-- Place the declared inversePreparation call on exactly the supplied source wires. -/
def inversePreparation (granted : allowInverse = true) (physical : QubitLayout width) :
    UnitaryCircuit gates (model width allowInverse allowControlledGood) physical.toQuantum :=
  program gates width allowInverse allowControlledGood (.inversePreparation granted)
    ((QuantumSignature.qubits width).place physical.physical_idx physical.physical_idx_injective)

/-- Place the declared goodReflection call on exactly the supplied source wires. -/
def goodReflection (physical : QubitLayout width) :
    UnitaryCircuit gates (model width allowInverse allowControlledGood) physical.toQuantum :=
  program gates width allowInverse allowControlledGood .goodReflection
    ((QuantumSignature.qubits width).place physical.physical_idx physical.physical_idx_injective)

/-- Place the declared controlledGoodReflection call on exactly the supplied source wires. -/
def controlledGoodReflection (granted : allowControlledGood = true)
    (physical : QubitLayout (1 + width)) :
    UnitaryCircuit gates (model width allowInverse allowControlledGood) physical.toQuantum :=
  program gates width allowInverse allowControlledGood (.controlledGoodReflection granted)
    ((QuantumSignature.qubits (1 + width)).place
      physical.physical_idx physical.physical_idx_injective)

end

end QuantumAlg.AmplitudeAmplificationSource.Circuit
