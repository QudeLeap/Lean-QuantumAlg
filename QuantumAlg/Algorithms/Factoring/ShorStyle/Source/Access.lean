/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.OrderFinding.AccessCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Family
import all QuantumAlg.Util.RSA.ResidueSampling

/-!
# Parameter-dependent Shor circuit access

This module constructs the order-finding circuit family selected by an encoded
residue parameter. Sampling and its source probability law are separate owners.
The modular-exponentiation event coordinate depends on the public modulus and
register widths but not on the hidden sampled base.  Every family member is a
real circuit whose event pool, event depth, and placement are proved equal to
the one common family projection.

The order-finding layout follows [Sho95, source.tex:1124-1169,1183-1245].
The reversible modular-exponentiation family and its exponent/work-register
interface follow [VBE95, 9511018.tex:334-376,438-485] and the order-finding
circuit presentation in [Bea02, arxivfact.tex:37-42,146-171,203-213].
-/

section

namespace QuantumAlg
namespace Factoring
namespace ShorStyle
namespace Canonical

open OrderFinding

noncomputable section

/-- Base-independent label for one internally selected modular-exponentiation
query.  The hidden base remains in the member operator, not the event key. -/
def modExpFamilyLabel (N t m : Nat) : Resource.SubroutineLabel :=
  { family := "shor-factoring"
    name := "sampled-modular-exponentiation"
    parameters := [N, t, m] }

/-- Strict query coordinate for the hidden-base modular-exponentiation family
[VBE95, 9511018.tex:334-376] [Bea02, arxivfact.tex:146-171]. -/
def modExpFamilyEvent (N t m : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (modExpFamilyLabel N t m).quantum

namespace EndpointDeclarations

/-- Auditable raw pairing for the hidden-base modular-exponentiation family. -/
def modExpFamilyLeafAt {N x t m : Nat} (systemIdx : List Nat)
    (access : ModExpOracleAccess N x t m) :
    UnitaryLeaf (Qubits (t + m)) :=
  UnitaryLeaf.subroutine (modExpFamilyLabel N t m) systemIdx
    (modExpOracle access)

end EndpointDeclarations

/-- Real hidden-base oracle leaf with a public base-independent event label. -/
def modExpFamilyLeaf {N x t m : Nat} (access : ModExpOracleAccess N x t m) :
    UnitaryLeaf (Qubits (t + m)) :=
  EndpointDeclarations.modExpFamilyLeafAt (List.range (t + m)) access

/-- The sealed hidden-base modular-exponentiation circuit. -/
def modExpFamilyCircuit {N x t m : Nat}
    (access : ModExpOracleAccess N x t m) : UnitaryCircuit (Qubits (t + m)) :=
  UnitaryCircuit.ofLeaf (modExpFamilyLeaf access) List.nodup_range

/-- The base-independent query label changes only accounting, not the actual
modular-exponentiation operator selected for this base. -/
@[simp] theorem modExpFamilyCircuit_applyNormalized_eq {N x t m : Nat}
    (access : ModExpOracleAccess N x t m)
    (state : NormalizedVector (Qubits (t + m))) :
    (modExpFamilyCircuit access).applyNormalized state =
      (orderFindingOracleCircuit access).applyNormalized state :=
  rfl

@[simp] theorem modExpFamilyCircuit_physical_idx {N x t m : Nat}
    (access : ModExpOracleAccess N x t m) :
    (modExpFamilyCircuit access).physical_idx = List.range (t + m) :=
  rfl

@[simp] theorem modExpFamilyCircuit_eventCost {N x t m : Nat}
    (access : ModExpOracleAccess N x t m) :
    (modExpFamilyCircuit access).eventCost =
      ResourcePool.singleton (modExpFamilyEvent N t m) :=
  rfl

/-- Complete prepare-query-readout circuit for one encoded runtime base. -/
def memberCircuit {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    UnitaryCircuit (Qubits (phaseBits N + modulusBits N)) :=
  let base := parameter.first.toNat
  let access : ModExpOracleAccess N base (phaseBits N) (modulusBits N) :=
    { modulus_pos := input.modulus_pos
      register_fits := input.register_fits }
  UnitaryCircuit.seq
    (orderFindingPreparationCircuit (phaseBits N) (modulusBits N))
    (UnitaryCircuit.seq (modExpFamilyCircuit access)
      (orderFindingReadoutCircuit (phaseBits N) (modulusBits N)))

@[simp] theorem memberCircuit_physical_idx {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (memberCircuit input parameter).physical_idx =
      List.range (phaseBits N + modulusBits N) := by
  simp [memberCircuit, UnitaryCircuit.seq]

/-- The hidden-base family member has the exact source-facing operator of the
canonical order-finding circuit for its encoded base. -/
@[simp] theorem memberCircuit_applyNormalized_eq {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (state : NormalizedVector (Qubits (phaseBits N + modulusBits N))) :
    (memberCircuit input parameter).applyNormalized state =
      (orderFindingCircuit
        ({ modulus_pos := input.modulus_pos
           register_fits := input.register_fits } :
          ModExpOracleAccess N parameter.first.toNat
            (phaseBits N) (modulusBits N))).applyNormalized state :=
  rfl

/-- Common event pool of every hidden-base member. -/
def memberEventCost (N : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton WalshHadamard.hadamardEvent (phaseBits N) +
    (ResourcePool.singleton
        (modExpFamilyEvent N (phaseBits N) (modulusBits N)) +
      (QFTCircuit (phaseBits N)).eventCost)

/-- Common strict event-depth tree of every hidden-base member. -/
def memberEventDepth (N : Nat) : DepthExpr (Resource.Event .quantum) :=
  .seq (orderFindingPreparationCircuit
      (phaseBits N) (modulusBits N)).eventDepth
    (.seq (.atom (modExpFamilyEvent N (phaseBits N) (modulusBits N)))
      (orderFindingReadoutCircuit
        (phaseBits N) (modulusBits N)).eventDepth)

@[simp] theorem memberCircuit_eventCost {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (memberCircuit input parameter).eventCost = memberEventCost N := by
  have daggerCost :
      (UnitaryCircuit.dagger (QFTCircuit (phaseBits N))).eventCost =
        (QFTCircuit (phaseBits N)).eventCost := rfl
  simp [memberCircuit, memberEventCost, orderFindingPreparationCircuit,
    orderFindingReadoutCircuit, UnitaryCircuit.tensorQubits, daggerCost]

/-- Certified strict-event family selected from the retained runtime value. -/
def circuitFamily {N : Nat} (input : Input N) :
    UnitaryCircuitFamily (CShape.Value (ParameterShape (modulusBits N)))
      (Qubits (phaseBits N + modulusBits N)) where
  member := memberCircuit input
  eventEnvelope := memberEventCost N
  member_eventCost_le parameter := (memberCircuit_eventCost input parameter).le
  depthEnvelope := memberEventDepth N
  member_eventDepth_le := by
    intro parameter assignment
    exact le_rfl
  commonPhysicalIdx := List.range (phaseBits N + modulusBits N)
  member_physical_idx := memberCircuit_physical_idx input


end

end Canonical
end ShorStyle
end Factoring
end QuantumAlg

end
