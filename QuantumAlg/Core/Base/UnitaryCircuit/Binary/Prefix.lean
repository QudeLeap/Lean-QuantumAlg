/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
public import QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Native execution on the original canonical prefix

The prefix embedding retains the original physical identities and dimensions.
The added suffix is already present, remains untouched, and grants no extra
native operation or oracle access.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Place each original prefix wire at exactly its original physical position. -/
@[expose]
public def binaryPrefixEmbedding (prefixWidth suffixWidth : Nat) :
    QuantumLayout.Embedding (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout
      (QuantumSignature.qubits (prefixWidth + suffixWidth)).canonicalPlacement.layout where
  position :=
    { toFun := Fin.castAdd suffixWidth
      inj' := by
        intro left right same
        apply Fin.ext
        exact congrArg (fun index : Fin (prefixWidth + suffixWidth) => index.val) same }
  wire_eq := fun _ => rfl

/-- Execute the unchanged native word while preserving the complete existing suffix. -/
public def onBinaryPrefix {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat}
    (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits (prefixWidth + suffixWidth)).canonicalPlacement.layout :=
  embed (binaryPrefixEmbedding prefixWidth suffixWidth) body

/-- Prefix placement preserves every native event and declared-query multiplicity. -/
public lemma unitaryCircuit_onBinaryPrefix_eventCost
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat} (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).eventCost = body.eventCost := by
  rfl

/-- Prefix placement retains the complete ordered native event trace. -/
public lemma unitaryCircuit_onBinaryPrefix_eventTrace
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat} (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).eventTrace = body.eventTrace := by
  rfl

/-- Prefix placement preserves the complete native dependency expression. -/
public lemma unitaryCircuit_onBinaryPrefix_eventDepth
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat} (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).eventDepth = body.eventDepth := by
  rfl

/-- Prefix placement preserves depth under every event-duration assignment. -/
public lemma unitaryCircuit_onBinaryPrefix_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat}
    (suffixWidth : Nat) (duration : Resource.Event (.quantum gates oracles) → Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rfl

/-- Prefix placement preserves the deepest chain of each selected event. -/
public lemma unitaryCircuit_onBinaryPrefix_eventQueryDepth
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat}
    (suffixWidth : Nat) (focus : Resource.Event (.quantum gates oracles))
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).eventQueryDepth focus =
      body.eventQueryDepth focus := by
  rfl

/-- Prefix placement preserves the linearized dependency resource pool. -/
public lemma unitaryCircuit_onBinaryPrefix_resourcesFromEventDepth
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat} (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).resourcesFromEventDepth =
      body.resourcesFromEventDepth := by
  rfl

/-- The suffix introduces no dependency step into the original executed word. -/
public lemma unitaryCircuit_onBinaryPrefix_unit_depth
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat} (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).evaluatedEventDepth (fun _ => 1) =
      body.evaluatedEventDepth (fun _ => 1) := by
  rfl


/-- Descriptive source occurrences remain attached to the same placed native word. -/
public lemma unitaryCircuit_onBinaryPrefix_macroCount
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat} (suffixWidth : Nat)
    (name : String)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) :
    (onBinaryPrefix suffixWidth body).macroCount name = body.macroCount name := by
  rw [onBinaryPrefix]
  exact macroCount_embed (binaryPrefixEmbedding prefixWidth suffixWidth) body name

end

end QuantumAlg.UnitaryCircuit
