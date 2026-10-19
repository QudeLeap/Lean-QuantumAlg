/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.AmplitudeAmplification.Circuit
import all QuantumAlg.Components.Oracle.AmplitudeAmplification.Circuit
import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# The actual source-query amplitude-amplification program

One initial preparation query is followed by k occurrences of the source
recognizer, inverse preparation, elementary positive zero reflection, and
preparation. The selected work suffix remains part of the full register.
The program is defined at every width and iteration count.
-/

namespace QuantumAlg.AmplitudeAmplification.Native

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- This source route explicitly grants inverse preparation and only ordinary good reflection. -/
public abbrev oracles (n : Nat) :
    OracleModel := AmplitudeAmplificationSource.model n true false

/-- Source operators interpret the fixed public query signature. -/
@[expose] public def interpretation {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) : (oracles n).Interpretation :=
  AmplitudeAmplificationSource.interpretation U good true false

/-- Ordinary preparation acts on the source while preserving the actual work suffix. -/
def preparation (n : Nat) (k : Nat) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout :=
  (AmplitudeAmplificationSource.Circuit.program AlgorithmGate.model n true false
    .preparation (QuantumSignature.qubits n).canonicalPlacement).onBinaryPrefix (helperWidth n k)

/-- The inverse call is an instance of the route's explicitly granted inverse access. -/
def inversePreparation (n : Nat) (k : Nat) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout :=
  (AmplitudeAmplificationSource.Circuit.program AlgorithmGate.model n true false
    (.inversePreparation rfl) (QuantumSignature.qubits n).canonicalPlacement).onBinaryPrefix
      (helperWidth n k)

/-- The supplied good-state phase reflection is called without coherent control. -/
def goodReflection (n : Nat) (k : Nat) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout :=
  (AmplitudeAmplificationSource.Circuit.program AlgorithmGate.model n true false
    .goodReflection (QuantumSignature.qubits n).canonicalPlacement).onBinaryPrefix (helperWidth n k)

/-- Literal iteration includes the native positive zero reflection and its exact sign. -/
def step (n : Nat)
    (k : Nat) (nonzero : k ≠ 0) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout :=
  (((goodReflection n k).seq (inversePreparation n k)).seq
    (ZeroReflection.Workspace.reflection (oracles n) n k nonzero)).seq
      (preparation n k)

/-- Initial preparation followed by exactly the requested number of actual source iterations. -/
def program (n : Nat)
    (k : Nat) :
    UnitaryCircuit AlgorithmGate.model (oracles n)
      (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout :=
  if zero : k = 0 then preparation n k
  else (preparation n k).seq (UnitaryCircuit.iterate k (step n k zero))

end

end QuantumAlg.AmplitudeAmplification.Native
