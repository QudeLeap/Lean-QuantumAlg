/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
public import QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Native execution on one binary wire

A one-qubit native word can be placed at any physical wire of a canonical
binary register by adjoining untouched prefix and suffix registers.  The
construction keeps the literal word and exposes its action on arbitrary raw
vectors split around the active wire.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Execute a one-qubit word at one physical wire of a canonical binary
register. -/
public def onBinaryWire {gates : GateModel} {oracles : OracleModel}
    {width : Nat} (wire : Fin width)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 1).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout :=
  ((onBinarySuffix wire.val body).onBinaryPrefix (width - wire.val - 1)).castQubitWidth
    (by omega)

/-- Assemble a raw register vector from the prefix, active qubit and suffix. -/
public def binaryWireVec {width : Nat} (wire : Fin width)
    (prefixState : HilbertVector (Qubits wire.val))
    (active : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits (width - wire.val - 1))) :
    HilbertVector (Qubits width) :=
  castQubitWidthVec (by omega)
    (HilbertVector.tensor (HilbertVector.tensor prefixState active) suffix)

/-- One-wire vector assembly is linear in its active qubit. -/
public theorem binaryWireVec_add_active {width : Nat} (wire : Fin width)
    (prefixState : HilbertVector (Qubits wire.val))
    (first second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits (width - wire.val - 1))) :
    binaryWireVec wire prefixState (first + second) suffix =
      binaryWireVec wire prefixState first suffix +
        binaryWireVec wire prefixState second suffix := by
  apply WithLp.ofLp_injective
  funext index
  simp [binaryWireVec, castQubitWidthVec_apply]

/-- One-wire vector assembly is linear in scalar multiples of its active
qubit. -/
public theorem binaryWireVec_smul_active {width : Nat} (wire : Fin width)
    (prefixState : HilbertVector (Qubits wire.val)) (scalar : ℂ)
    (active : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits (width - wire.val - 1))) :
    binaryWireVec wire prefixState (scalar • active) suffix =
      scalar • binaryWireVec wire prefixState active suffix := by
  apply WithLp.ofLp_injective
  funext index
  simp [binaryWireVec, castQubitWidthVec_apply, smul_eq_mul]

/-- Single-wire placement applies the supplied word only to the active qubit
and fixes both surrounding raw-vector fields. -/
public theorem unitaryCircuit_onBinaryWire_applyVec
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (wire : Fin width)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 1).canonicalPlacement.layout)
    (prefixState : HilbertVector (Qubits wire.val))
    (active : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits (width - wire.val - 1))) :
    (onBinaryWire wire body).binaryMatrix.applyVec
        (binaryWireVec wire prefixState active suffix) =
      binaryWireVec wire prefixState (body.binaryMatrix.applyVec active) suffix := by
  unfold onBinaryWire binaryWireVec
  rw [castQubitWidth_binaryMatrix_applyVec,
    unitaryCircuit_onBinaryPrefix_applyVec_tensor,
    unitaryCircuit_onBinarySuffix_applyVec_tensor]

/-- Binary-coordinate spelling of one-wire vector action. -/
public theorem onBinaryWire_applyBinaryVec
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (wire : Fin width)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 1).canonicalPlacement.layout)
    (prefixState : HilbertVector (Qubits wire.val))
    (active : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits (width - wire.val - 1))) :
    (onBinaryWire wire body).applyBinaryVec
        (binaryWireVec wire prefixState active suffix) =
      binaryWireVec wire prefixState (body.applyBinaryVec active) suffix := by
  exact unitaryCircuit_onBinaryWire_applyVec wire body prefixState active suffix

/-- Single-wire placement preserves the ordered native-event trace. -/
public theorem unitaryCircuit_onBinaryWire_eventTrace
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (wire : Fin width)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 1).canonicalPlacement.layout) :
    (onBinaryWire wire body).eventTrace = body.eventTrace := by
  simp [onBinaryWire, castQubitWidth_eventTrace,
    unitaryCircuit_onBinaryPrefix_eventTrace,
    unitaryCircuit_onBinarySuffix_eventTrace]

/-- Single-wire placement preserves the exact native and oracle event pool. -/
public theorem unitaryCircuit_onBinaryWire_eventCost
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (wire : Fin width)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 1).canonicalPlacement.layout) :
    (onBinaryWire wire body).eventCost = body.eventCost := by
  rw [onBinaryWire, castQubitWidth_eventCost,
    unitaryCircuit_onBinaryPrefix_eventCost,
    unitaryCircuit_onBinarySuffix_eventCost]

/-- Single-wire placement preserves dependency depth under every duration
assignment. -/
public theorem unitaryCircuit_onBinaryWire_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (wire : Fin width)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 1).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (onBinaryWire wire body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rw [onBinaryWire, castQubitWidth_evaluatedEventDepth,
    unitaryCircuit_onBinaryPrefix_evaluatedEventDepth,
    unitaryCircuit_onBinarySuffix_evaluatedEventDepth]

end

end QuantumAlg.UnitaryCircuit
