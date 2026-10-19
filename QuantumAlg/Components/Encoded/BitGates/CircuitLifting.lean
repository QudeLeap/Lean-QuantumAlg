/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Middle

/-!
# Canonical binary register lifting

These operations place an actual circuit on a prefix, suffix, or the two fields
around an untouched middle register. The selected gate and oracle models are
preserved, and Core's layout embeddings carry the physical placement proof.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}

/-- Execute an actual circuit on the canonical prefix and leave the appended
suffix untouched. -/
def prodLeft {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits m).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits (m + n)).canonicalPlacement.layout :=
  onBinaryPrefix n program

/-- Execute an actual circuit on the canonical suffix and leave the preceding
prefix untouched. -/
def prodRight {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits (m + n)).canonicalPlacement.layout :=
  onBinarySuffix m program

@[simp] lemma prodLeft_eventTrace {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits m).canonicalPlacement.layout) :
    (prodLeft (n := n) program).eventTrace = program.eventTrace :=
  unitaryCircuit_onBinaryPrefix_eventTrace n program

@[simp] lemma prodRight_eventTrace {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (prodRight (m := m) program).eventTrace = program.eventTrace :=
  unitaryCircuit_onBinarySuffix_eventTrace m program

@[simp] lemma prodLeft_eventCost {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits m).canonicalPlacement.layout) :
    (prodLeft (n := n) program).eventCost = program.eventCost :=
  unitaryCircuit_onBinaryPrefix_eventCost n program

@[simp] lemma prodRight_eventCost {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (prodRight (m := m) program).eventCost = program.eventCost :=
  unitaryCircuit_onBinarySuffix_eventCost m program

@[simp] lemma prodLeft_eventDepth {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits m).canonicalPlacement.layout) :
    (prodLeft (n := n) program).eventDepth = program.eventDepth :=
  unitaryCircuit_onBinaryPrefix_eventDepth n program

@[simp] lemma prodRight_eventDepth {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (prodRight (m := m) program).eventDepth = program.eventDepth :=
  unitaryCircuit_onBinarySuffix_eventDepth m program

@[simp] lemma prodLeft_evaluatedEventDepth {m n : Nat}
    (assign : Resource.Event (.quantum gates oracles) → Nat)
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits m).canonicalPlacement.layout) :
    (prodLeft (n := n) program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign :=
  unitaryCircuit_onBinaryPrefix_evaluatedEventDepth n assign program

@[simp] lemma prodRight_evaluatedEventDepth {m n : Nat}
    (assign : Resource.Event (.quantum gates oracles) → Nat)
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (prodRight (m := m) program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign :=
  unitaryCircuit_onBinarySuffix_evaluatedEventDepth m assign program

@[simp] lemma prodLeft_eventQueryDepth {m n : Nat}
    (focus : Resource.Event (.quantum gates oracles))
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits m).canonicalPlacement.layout) :
    (prodLeft (n := n) program).eventQueryDepth focus =
      program.eventQueryDepth focus :=
  unitaryCircuit_onBinaryPrefix_eventQueryDepth n focus program

@[simp] lemma prodRight_eventQueryDepth {m n : Nat}
    (focus : Resource.Event (.quantum gates oracles))
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (prodRight (m := m) program).eventQueryDepth focus =
      program.eventQueryDepth focus :=
  unitaryCircuit_onBinarySuffix_eventQueryDepth m focus program

lemma prodLeft_resourcesFromEventDepth {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits m).canonicalPlacement.layout) :
    (prodLeft (n := n) program).resourcesFromEventDepth =
      program.resourcesFromEventDepth :=
  unitaryCircuit_onBinaryPrefix_resourcesFromEventDepth n program

lemma prodRight_resourcesFromEventDepth {m n : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (prodRight (m := m) program).resourcesFromEventDepth =
      program.resourcesFromEventDepth :=
  unitaryCircuit_onBinarySuffix_resourcesFromEventDepth m program

/-- Execute an actual circuit on the original left and right fields while an
inserted canonical middle field remains untouched. -/
def insertMiddle {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits
        (leftWidth + middleWidth + rightWidth)).canonicalPlacement.layout :=
  onBinaryMiddle middleWidth program

@[simp] lemma insertMiddle_eventTrace
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (insertMiddle (middleWidth := middleWidth) program).eventTrace =
      program.eventTrace :=
  unitaryCircuit_onBinaryMiddle_eventTrace middleWidth program

@[simp] lemma insertMiddle_eventCost
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (insertMiddle (middleWidth := middleWidth) program).eventCost =
      program.eventCost :=
  unitaryCircuit_onBinaryMiddle_eventCost middleWidth program

@[simp] lemma insertMiddle_eventDepth
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (insertMiddle (middleWidth := middleWidth) program).eventDepth =
      program.eventDepth :=
  unitaryCircuit_onBinaryMiddle_eventDepth middleWidth program

@[simp] lemma insertMiddle_evaluatedEventDepth
    {leftWidth middleWidth rightWidth : Nat}
    (assign : Resource.Event (.quantum gates oracles) → Nat)
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (insertMiddle (middleWidth := middleWidth) program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign :=
  unitaryCircuit_onBinaryMiddle_evaluatedEventDepth middleWidth assign program

@[simp] lemma insertMiddle_eventQueryDepth
    {leftWidth middleWidth rightWidth : Nat}
    (focus : Resource.Event (.quantum gates oracles))
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (insertMiddle (middleWidth := middleWidth) program).eventQueryDepth focus =
      program.eventQueryDepth focus :=
  unitaryCircuit_onBinaryMiddle_eventQueryDepth middleWidth focus program

lemma insertMiddle_resourcesFromEventDepth
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout) :
    (insertMiddle (middleWidth := middleWidth) program).resourcesFromEventDepth =
      program.resourcesFromEventDepth :=
  unitaryCircuit_onBinaryMiddle_resourcesFromEventDepth middleWidth program

end

end QuantumAlg.UnitaryCircuit
