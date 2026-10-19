/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
public import QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Layout.Quantum.Relabeling
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Qubit

/-!
# Actual native execution on a canonical suffix

Relocate every original physical wire behind an existing prefix, then embed the
same construction into the complete layout. Native operations, oracle grants
and dependency depths are preserved; the prefix is untouched.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Injectively shift physical identities behind the complete existing prefix. -/
def binarySuffixShift (prefixWidth : Nat) : Nat ↪ Nat where
  toFun index := prefixWidth + index
  inj' := fun _ _ same => Nat.add_left_cancel same

/-- The shifted original wires are exactly the canonical suffix positions. -/
def binarySuffixEmbedding (prefixWidth suffixWidth : Nat) :
    QuantumLayout.Embedding
      ((QuantumSignature.qubits suffixWidth).canonicalPlacement.layout.relabel
        (binarySuffixShift prefixWidth))
      (QuantumSignature.qubits (prefixWidth + suffixWidth)).canonicalPlacement.layout where
  position :=
    { toFun := Fin.natAdd prefixWidth
      inj' := by
        intro left right same
        apply Fin.ext
        have equal := congrArg Fin.val same
        exact Nat.add_left_cancel equal }
  wire_eq := fun _ => rfl

/-- Execute the actual relocated word without acting on the existing prefix. -/
public def onBinarySuffix {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits (prefixWidth + suffixWidth)).canonicalPlacement.layout :=
  embed (binarySuffixEmbedding prefixWidth suffixWidth)
    (body.relabel (binarySuffixShift prefixWidth))

/-- Canonical-layout form of suffix placement. This keeps typed-qubit clients
from depending on reducibility of the equivalent signature presentation. -/
public def onCanonicalBinarySuffix {gates : GateModel} {oracles : OracleModel}
    {suffixWidth : Nat} (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical suffixWidth).toQuantum) :
    UnitaryCircuit gates oracles
      (QubitLayout.canonical (prefixWidth + suffixWidth)).toQuantum :=
  onBinarySuffix prefixWidth body

/-- Suffix placement retains every actual native and oracle occurrence. -/
public lemma unitaryCircuit_onBinarySuffix_eventCost
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat} (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    (onBinarySuffix prefixWidth body).eventCost = body.eventCost := by
  change (body.relabel (binarySuffixShift prefixWidth)).eventCost = body.eventCost
  exact relabel_eventCost body (binarySuffixShift prefixWidth)

/-- Suffix placement retains the complete ordered native event trace. -/
public lemma unitaryCircuit_onBinarySuffix_eventTrace
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat} (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    (onBinarySuffix prefixWidth body).eventTrace = body.eventTrace := by
  change (body.relabel (binarySuffixShift prefixWidth)).eventTrace = body.eventTrace
  exact relabel_eventTrace body (binarySuffixShift prefixWidth)

/-- Suffix placement preserves the complete native dependency expression. -/
lemma unitaryCircuit_onBinarySuffix_eventDepth
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat} (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    (onBinarySuffix prefixWidth body).eventDepth = body.eventDepth := by
  change (body.relabel (binarySuffixShift prefixWidth)).eventDepth = body.eventDepth
  exact relabel_eventDepth body (binarySuffixShift prefixWidth)

/-- Suffix placement preserves depth under every event-duration assignment. -/
public lemma unitaryCircuit_onBinarySuffix_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat) (duration : Resource.Event (.quantum gates oracles) → Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    (onBinarySuffix prefixWidth body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  unfold evaluatedEventDepth
  rw [unitaryCircuit_onBinarySuffix_eventDepth]

/-- Suffix placement preserves the deepest chain of each selected event. -/
lemma unitaryCircuit_onBinarySuffix_eventQueryDepth
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat) (focus : Resource.Event (.quantum gates oracles))
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    (onBinarySuffix prefixWidth body).eventQueryDepth focus =
      body.eventQueryDepth focus := by
  unfold eventQueryDepth
  rw [unitaryCircuit_onBinarySuffix_eventDepth]

/-- Suffix placement preserves the linearized dependency resource pool. -/
lemma unitaryCircuit_onBinarySuffix_resourcesFromEventDepth
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat} (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    (onBinarySuffix prefixWidth body).resourcesFromEventDepth =
      body.resourcesFromEventDepth := by
  unfold resourcesFromEventDepth
  rw [unitaryCircuit_onBinarySuffix_eventDepth]

/-- Suffix placement adds no dependency step. -/
lemma unitaryCircuit_onBinarySuffix_unit_depth
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat} (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) :
    (onBinarySuffix prefixWidth body).evaluatedEventDepth (fun _ => 1) =
      body.evaluatedEventDepth (fun _ => 1) := by
  change DepthExpr.depthEval (fun _ => 1)
    (body.relabel (binarySuffixShift prefixWidth)).eventDepth = _
  rw [relabel_eventDepth]
  rfl

/-- Canonical suffix placement retains every actual native and oracle event. -/
public lemma onCanonicalBinarySuffix_eventCost
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical suffixWidth).toQuantum) :
    (onCanonicalBinarySuffix prefixWidth body).eventCost = body.eventCost := by
  exact unitaryCircuit_onBinarySuffix_eventCost prefixWidth body

/-- Canonical suffix placement retains evaluated dependency depth. -/
public lemma onCanonicalBinarySuffix_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat) (duration : Resource.Event (.quantum gates oracles) → Nat)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical suffixWidth).toQuantum) :
    (onCanonicalBinarySuffix prefixWidth body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  exact unitaryCircuit_onBinarySuffix_evaluatedEventDepth prefixWidth duration body

end

end QuantumAlg.UnitaryCircuit
