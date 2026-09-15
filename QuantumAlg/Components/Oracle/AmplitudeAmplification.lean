/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Source queries for amplitude amplification

The source supplies preparation `U`, its inverse, and the good-state phase
reflection. These declarations keep the three actual calls on distinct native
coordinates [Lin22, appqpe.tex:189-219]. The known all-zero reflection is owned
separately by `ZeroReflection`; it is not a good-reflection oracle query.

Each occurrence accepts only the source operator or state and its physical
placement. Quantum control is added by the unitary circuit construction.
-/

namespace QuantumAlg.AmplitudeAmplificationSource

noncomputable section

/-- Native source-preparation query coordinate. -/
def preparationLabel (n : Nat) : Resource.SubroutineLabel :=
  { family := "QuantumAlg.Components.Oracle.AmplitudeAmplification"
    name := "source-preparation"
    parameters := [n] }

/-- Native inverse-source-preparation query coordinate. -/
def inversePreparationLabel (n : Nat) : Resource.SubroutineLabel :=
  { family := "QuantumAlg.Components.Oracle.AmplitudeAmplification"
    name := "inverse-source-preparation"
    parameters := [n] }

/-- Native query coordinate for `I - 2|good><good|`. -/
def goodReflectionLabel (n : Nat) : Resource.SubroutineLabel :=
  { family := "QuantumAlg.Components.Oracle.AmplitudeAmplification"
    name := "good-state-phase-reflection"
    parameters := [n] }

/-- The preparation event emitted by the declared source call. -/
public def preparationEvent (n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (preparationLabel n).quantum

/-- The inverse event emitted by the declared adjoint source call. -/
public def inversePreparationEvent (n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (inversePreparationLabel n).quantum

/-- The good-reflection event emitted by the declared source call. -/
public def goodReflectionEvent (n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (goodReflectionLabel n).quantum

/-- An occurrence of the source preparation, with no assumed controlled access. -/
def preparationLeafAt {n : Nat} (U : UnitaryOperator (Qubits n))
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.subroutine (preparationLabel n) systemIdx U

/-- An occurrence of the inverse of the same source operator. -/
def inversePreparationLeafAt {n : Nat} (U : UnitaryOperator (Qubits n))
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.subroutine (inversePreparationLabel n) systemIdx U.dagger

/-- An occurrence of the source good-state phase reflection. -/
def goodReflectionLeafAt {n : Nat} (good : NormalizedVector (Qubits n))
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.subroutine (goodReflectionLabel n) systemIdx
    (OrthogonalProjector.rankOnePhaseReflectionOp good)

end

end QuantumAlg.AmplitudeAmplificationSource
