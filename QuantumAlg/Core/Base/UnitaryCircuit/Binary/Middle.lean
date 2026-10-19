/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Relabeling
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Native execution around an existing canonical middle field

The middle embedding relocates the original right field behind an already
present middle field. The original left and right fields retain their order,
the middle field remains untouched, and no new native or oracle event is
introduced.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Numeric action of inserting a physical-address interval. -/
public def binaryMiddleIndex (leftWidth middleWidth index : Nat) : Nat :=
  if index < leftWidth then index else index + middleWidth

/-- Inserting one address interval never identifies two original systems. -/
public lemma binaryMiddleIndex_injective (leftWidth middleWidth : Nat) :
    Function.Injective (binaryMiddleIndex leftWidth middleWidth) := by
  intro left right same
  by_cases leftBefore : left < leftWidth <;>
    by_cases rightBefore : right < leftWidth <;>
      simp [binaryMiddleIndex, leftBefore, rightBefore] at same <;> omega

/-- Shift every original physical identity at or beyond the middle boundary. -/
public def binaryMiddleShift (leftWidth middleWidth : Nat) : Nat ↪ Nat where
  toFun := binaryMiddleIndex leftWidth middleWidth
  inj' := binaryMiddleIndex_injective leftWidth middleWidth

/-- Insert the middle positions into the canonical logical order. -/
public def binaryMiddlePosition (leftWidth middleWidth rightWidth : Nat) :
    Fin (leftWidth + rightWidth) ↪ Fin (leftWidth + middleWidth + rightWidth) where
  toFun index :=
    ⟨binaryMiddleShift leftWidth middleWidth index.val, by
      change binaryMiddleIndex leftWidth middleWidth index.val < _
      unfold binaryMiddleIndex
      split <;> omega⟩
  inj' := by
    intro left right same
    apply Fin.ext
    exact (binaryMiddleShift leftWidth middleWidth).injective
      (congrArg Fin.val same)

/-- Original left positions retain their canonical position. -/
public lemma binaryMiddlePosition_left
    {leftWidth middleWidth rightWidth : Nat} (index : Fin leftWidth) :
    binaryMiddlePosition leftWidth middleWidth rightWidth
        (Fin.castAdd rightWidth index) =
      Fin.castAdd rightWidth (Fin.castAdd middleWidth index) := by
  apply Fin.ext
  change binaryMiddleIndex leftWidth middleWidth index.val = index.val
  simp [binaryMiddleIndex, index.isLt]

/-- Original right positions move behind the complete middle field. -/
public lemma binaryMiddlePosition_right
    {leftWidth middleWidth rightWidth : Nat} (index : Fin rightWidth) :
    binaryMiddlePosition leftWidth middleWidth rightWidth
        (Fin.natAdd leftWidth index) =
      Fin.natAdd (leftWidth + middleWidth) index := by
  apply Fin.ext
  change binaryMiddleIndex leftWidth middleWidth (leftWidth + index.val) =
    leftWidth + middleWidth + index.val
  simp [binaryMiddleIndex]
  omega

/-- The relocated original word occupies precisely the canonical left and
right fields around the existing middle field. -/
def binaryMiddleEmbedding (leftWidth middleWidth rightWidth : Nat) :
    QuantumLayout.Embedding
      ((QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout.relabel
        (binaryMiddleShift leftWidth middleWidth))
      (QuantumSignature.qubits
        (leftWidth + middleWidth + rightWidth)).canonicalPlacement.layout where
  position := binaryMiddlePosition leftWidth middleWidth rightWidth
  wire_eq := by
    intro index
    rfl

/-- Execute an actual native word on the existing left and right fields while
preserving the complete middle field. -/
public def onBinaryMiddle {gates : GateModel} {oracles : OracleModel}
    {leftWidth rightWidth : Nat} (middleWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits
        (leftWidth + middleWidth + rightWidth)).canonicalPlacement.layout :=
  embed (binaryMiddleEmbedding leftWidth middleWidth rightWidth)
    (body.relabel (binaryMiddleShift leftWidth middleWidth))

/-- Middle placement retains the complete ordered native event trace. -/
public lemma unitaryCircuit_onBinaryMiddle_eventTrace
    {gates : GateModel} {oracles : OracleModel} {leftWidth rightWidth : Nat}
    (middleWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (onBinaryMiddle middleWidth body).eventTrace = body.eventTrace := by
  unfold onBinaryMiddle
  change (body.relabel (binaryMiddleShift leftWidth middleWidth)).eventTrace =
    body.eventTrace
  exact relabel_eventTrace body (binaryMiddleShift leftWidth middleWidth)

/-- Middle placement preserves every native event and query multiplicity. -/
public lemma unitaryCircuit_onBinaryMiddle_eventCost
    {gates : GateModel} {oracles : OracleModel} {leftWidth rightWidth : Nat}
    (middleWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (onBinaryMiddle middleWidth body).eventCost = body.eventCost := by
  rw [← ofList_eventTrace_eq_eventCost, unitaryCircuit_onBinaryMiddle_eventTrace,
    ofList_eventTrace_eq_eventCost]

/-- Middle placement preserves the complete native dependency expression. -/
public lemma unitaryCircuit_onBinaryMiddle_eventDepth
    {gates : GateModel} {oracles : OracleModel} {leftWidth rightWidth : Nat}
    (middleWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (onBinaryMiddle middleWidth body).eventDepth = body.eventDepth := by
  unfold onBinaryMiddle
  change (body.relabel (binaryMiddleShift leftWidth middleWidth)).eventDepth =
    body.eventDepth
  exact relabel_eventDepth body (binaryMiddleShift leftWidth middleWidth)

/-- Middle placement preserves depth under every event-duration assignment. -/
public lemma unitaryCircuit_onBinaryMiddle_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {leftWidth rightWidth : Nat}
    (middleWidth : Nat) (duration : Resource.Event (.quantum gates oracles) → Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (onBinaryMiddle middleWidth body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  unfold evaluatedEventDepth
  rw [unitaryCircuit_onBinaryMiddle_eventDepth]

/-- Middle placement preserves the deepest chain of each selected event. -/
public lemma unitaryCircuit_onBinaryMiddle_eventQueryDepth
    {gates : GateModel} {oracles : OracleModel} {leftWidth rightWidth : Nat}
    (middleWidth : Nat) (focus : Resource.Event (.quantum gates oracles))
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (onBinaryMiddle middleWidth body).eventQueryDepth focus =
      body.eventQueryDepth focus := by
  unfold eventQueryDepth
  rw [unitaryCircuit_onBinaryMiddle_eventDepth]

/-- Middle placement preserves the linearized dependency resource pool. -/
public lemma unitaryCircuit_onBinaryMiddle_resourcesFromEventDepth
    {gates : GateModel} {oracles : OracleModel} {leftWidth rightWidth : Nat}
    (middleWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (onBinaryMiddle middleWidth body).resourcesFromEventDepth =
      body.resourcesFromEventDepth := by
  unfold resourcesFromEventDepth
  rw [unitaryCircuit_onBinaryMiddle_eventDepth]

end

end QuantumAlg.UnitaryCircuit
