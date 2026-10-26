/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Construction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Placement
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

/-!
# Exact physical-wire placement of the measured recycling carrier

Complete ordered wire records transport the actual single-control native
gates and canonical arithmetic carrier. The proof compares original wire
identities and values, rather than only register dimensions
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Placement

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Actual full physical basis correspondence from the same complete ordered wire records. -/
def basis : (Physical.qubits width).toQuantum.register.Index ≃
    (Context base noQuantum m ell width).register.Index :=
  basisOfEqualWires (Physical.qubits width).toQuantum
    (Context base noQuantum m ell width).quantumLayout (context_wires base noQuantum m ell width)

/-- The arbitrary single-qubit operator is native on the original physical arithmetic control. -/
def physicalSingle (width : Nat) (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (Physical.qubits width).toQuantum :=
  Gate.singleQubitAt (Physical.qubits width).toQuantum .empty operator
    (Physical.layout width).control.wire rfl

/-- The actual context-level one-qubit word has exactly the full physical source matrix. -/
lemma measuredSingle_matrix (environment : OracleModel.empty.Interpretation)
    (operator : UnitaryOperator (Qubits 1)) :
    (single base noQuantum m ell width operator).matrix environment =
      UnitaryOperator.reindex (basis base noQuantum m ell width)
        ((physicalSingle width operator).matrix environment) :=
  Recycling.Placement.single_equal_wires_matrix (environment := environment)
    (Physical.qubits width).toQuantum (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) operator (Physical.layout width).control.wire rfl
      (control_qubit base noQuantum m ell width)

/-- The actual control refers to the identical original bottom-level physical system. -/
lemma measuredSingle_physical_wire :
    (Context base noQuantum m ell width).quantumLayout.wire (control base noQuantum m ell width) =
      (Physical.qubits width).toQuantum.wire (Physical.layout width).control.wire :=
  wireAtCorrespondingPosition (Physical.qubits width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) (Physical.layout width).control.wire

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Canonical original control/unit carrier represented in the actual allocated caller frame. -/
def embedding : (Recycling.Carrier.full modulus.toNat).Index ↪
    (Context base noQuantum m ell width).register.Index :=
  (Measured.Carrier.embedding modulus).trans (basis base noQuantum m ell width).toEmbedding

/-- Actual zero-control carrier retained between the measured chronological stages. -/
def zeroEmbedding : (Recycling.Carrier.units modulus.toNat).Index ↪
    (Context base noQuantum m ell width).register.Index :=
  (Measured.Carrier.zeroEmbedding modulus).trans (basis base noQuantum m ell width).toEmbedding

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Placement
