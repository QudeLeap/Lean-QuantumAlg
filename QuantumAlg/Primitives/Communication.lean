/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init

/-!
# Communication resources for quantum protocols

Communication resources are protocol-level quantities, not gate costs.  This
small shared primitive keeps classical messages, transmitted quantum systems,
and shared Bell pairs separate from the `UnitaryCircuit` resource ledger until a
future protocol semantics derives them from communication actions.
-/

section

namespace QuantumAlg

/-- Communication resources appearing in protocol statements. -/
public structure CommunicationProfile where
  /-- Classical bits communicated by the protocol. -/
  classicalBits : Nat
  /-- Qubits transmitted by the protocol. -/
  transmittedQubits : Nat
  /-- Shared Bell pairs consumed or produced by the protocol. -/
  bellPairs : Nat
deriving DecidableEq

namespace CommunicationProfile

/-- Exact communication-resource claim for a protocol statement. -/
public def HasExactCounts (profile : CommunicationProfile)
    (classicalBits transmittedQubits bellPairs : Nat) : Prop :=
  profile.classicalBits = classicalBits ∧
    profile.transmittedQubits = transmittedQubits ∧
    profile.bellPairs = bellPairs

@[simp]
public theorem hasExactCounts_mk (classicalBits transmittedQubits bellPairs : Nat) :
    HasExactCounts
      { classicalBits := classicalBits, transmittedQubits := transmittedQubits,
        bellPairs := bellPairs }
      classicalBits transmittedQubits bellPairs := by
  simp [HasExactCounts]

end CommunicationProfile

end QuantumAlg

end
