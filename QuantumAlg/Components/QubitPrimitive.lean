/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QubitPrimitive.Word
public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.QubitPrimitive.Word
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Addressed reversible primitives in the default native language

Each circuit uses the model-owned X, CNOT or Toffoli instance on its actual
physical arguments. The full ambient qubit layout stays in its type. Operator,
native event, dependency depth and footprint come from that same application.
The binary-word semantics use the fixed big-endian interpretation of the layout.
-/

namespace QuantumAlg.QubitPrimitive

noncomputable section

/-- The exact native coordinate of this primitive in the chosen oracle environment. -/
@[expose]
public def event {n : Nat} (primitive : QubitPrimitive n) (oracles : OracleModel) :
    Resource.Event (.quantum AlgorithmGate.model oracles) :=
  .gate (AlgorithmGate.model.coordinate (nativeToken primitive))

/-- One actual native gate, with its physical arguments embedded in the full register. -/
@[expose]
public def leaf {n : Nat} (primitive : QubitPrimitive n) (layout : QubitLayout n)
    (oracles : OracleModel) : UnitaryLeaf AlgorithmGate.model oracles layout.toQuantum :=
  .gate (nativeApplication layout primitive)

/-- The native execution retains the original addressed word operator with exact phase. -/
public lemma leaf_operator {n : Nat} (primitive : QubitPrimitive n) (layout : QubitLayout n)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((leaf primitive layout oracles).operator environment) =
      UnitaryOperator.reindex layout.basisEquiv.symm primitive.operator :=
  nativeApplication_operator layout primitive

/-- The footprint is the actual ordered physical control and target positions. -/
public lemma leaf_systemIdx {n : Nat} (primitive : QubitPrimitive n) (layout : QubitLayout n)
    (oracles : OracleModel) :
    (leaf primitive layout oracles).systemIdx =
      (nativePositions primitive).map layout.physical_idx :=
  nativeApplication_physicalFootprint layout primitive

/-- The event is fixed by the same applied native instance. -/
public lemma leaf_event {n : Nat} (primitive : QubitPrimitive n) (layout : QubitLayout n)
    (oracles : OracleModel) :
    (leaf primitive layout oracles).event = event primitive oracles := by
  cases primitive <;> rfl

/-- Execute the actual native application on the supplied complete physical layout. -/
@[expose]
public def circuit {n : Nat} (primitive : QubitPrimitive n) (layout : QubitLayout n)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  UnitaryCircuit.native (nativeApplication layout primitive)

/-- The actual circuit matrix is the original word operator in the fixed physical basis. -/
public lemma primitiveCircuit_matrix {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((circuit primitive layout oracles).matrix environment) =
      UnitaryOperator.reindex layout.basisEquiv.symm primitive.operator :=
  (UnitaryCircuit.native_matrix environment (nativeApplication layout primitive)).trans
    (nativeApplication_operator layout primitive)

/-- In canonical binary coordinates, a native primitive retains its declared
word operator exactly. -/
public lemma circuit_canonical_binaryMatrix {n : Nat}
    (primitive : QubitPrimitive n) (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((circuit primitive (QubitLayout.canonical n) oracles).binaryMatrix environment) =
      primitive.operator := by
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n)
      ((circuit primitive (QubitLayout.canonical n) oracles).matrix environment) =
    primitive.operator
  rw [primitiveCircuit_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n).symm primitive.operator

/-- One primitive emits one occurrence of its actual model coordinate. -/
public lemma primitiveCircuit_eventTrace {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n) (oracles : OracleModel) :
    (circuit primitive layout oracles).eventTrace = [event primitive oracles] := by
  rw [circuit, UnitaryCircuit.native_eventTrace, nativeApplication_coordinate]
  rfl

/-- Literal multiplicity follows the same applied native token. -/
public lemma primitiveCircuit_eventCost {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n) (oracles : OracleModel) :
    (circuit primitive layout oracles).eventCost =
      ResourcePool.singleton (event primitive oracles) := by
  rw [circuit, UnitaryCircuit.native_eventCost, nativeApplication_coordinate]
  rfl

/-- One actual primitive is one atomic dependency step. -/
public lemma primitiveCircuit_eventDepth {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n) (oracles : OracleModel) :
    (circuit primitive layout oracles).eventDepth = .atom (event primitive oracles) := by
  cases primitive <;> rfl

/-- The primitive contributes exactly one occurrence to its own native coordinate. -/
public lemma primitiveCircuit_eventCount {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n) (oracles : OracleModel) :
    ResourcePool.count (event primitive oracles)
      (circuit primitive layout oracles).eventCost = 1 := by
  rw [primitiveCircuit_eventCost, ResourcePool.count_singleton_self]

/-- Distinct event coordinates receive no charge from this native instruction. -/
public lemma primitiveCircuit_eventCount_of_ne {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n) (oracles : OracleModel)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    (different : focus ≠ event primitive oracles) :
    ResourcePool.count focus (circuit primitive layout oracles).eventCost = 0 := by
  rw [primitiveCircuit_eventCost]
  exact ResourcePool.count_singleton_of_ne different 1

/-- Linearizing the actual dependency path yields the same native ledger. -/
public lemma primitiveCircuit_resourcesFromEventDepth {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n) (oracles : OracleModel) :
    (circuit primitive layout oracles).resourcesFromEventDepth =
      (circuit primitive layout oracles).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (circuit primitive layout oracles)

/-- The circuit's actual normalized-state action retains the original addressed word update. -/
lemma circuit_applyNormalized_ket {n : Nat} (primitive : QubitPrimitive n)
    (layout : QubitLayout n) (oracles : OracleModel) (label : Fin (2 ^ n))
      (environment : oracles.Interpretation) :
    ((circuit primitive layout oracles).applyNormalized environment)
      (NormalizedVector.ket (layout.basisEquiv.symm label)) =
        NormalizedVector.ket (layout.basisEquiv.symm (primitive.applyLabel label)) :=
  nativeApplication_apply_ket layout primitive label

end

end QuantumAlg.QubitPrimitive
