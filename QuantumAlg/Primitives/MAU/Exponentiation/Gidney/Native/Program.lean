/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Placement
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Prepare and execute the actual native exponentiation oracle

Basis regrouping and physical relabeling implement the same four-word
placement. The final zero-event identity records the complete existing
context order. Execution really prepares the two missing work words before
the gate sequence; it imposes no initialization requirement on caller storage.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

private def transportedProgram (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit (preparedContext exponentWidth width).register :=
  UnitaryCircuit.reindex (R := Qubits (oracleEncoding exponentWidth width).width)
    (preparedBasisEquiv exponentWidth width).symm (oracleProgram exponentWidth width modulus base)

private def placementRelabeling (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    PhysicalLayout.Relabeling (transportedProgram exponentWidth width modulus base).physical_idx
      ((transportedProgram exponentWidth width modulus base).physical_idx.map
        (nativePlacementWire exponentWidth width)) where
  toFun := nativePlacementWire exponentWidth width
  map_layout := rfl
  old_nodup := (transportedProgram exponentWidth width modulus base).physical_idx_nodup
  new_nodup := (transportedProgram exponentWidth width modulus base).physical_idx_nodup.map
    (gidneyExponentNativePlacement_injective exponentWidth width)

private def mappedProgram (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit (preparedContext exponentWidth width).register :=
  (transportedProgram exponentWidth width modulus base).relabel
    (placementRelabeling exponentWidth width modulus base)

private theorem mappedProgram_physical_range (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (mappedProgram exponentWidth width modulus base).physical_idx ⊆
      (preparedContext exponentWidth width).physicalIdx := by
  change (oracleProgram exponentWidth width modulus base).physical_idx.map
    (nativePlacementWire exponentWidth width) ⊆ _
  intro wire mappedMember
  obtain ⟨source, sourceMember, mappedEq⟩ := List.mem_map.mp mappedMember
  rw [gidneyExponentOracle_physical] at sourceMember
  have placedMember := gidneyExponentPreparedContext_contains exponentWidth width
    (List.mem_range.mpr (gidneyExponentNativePlacement_range exponentWidth width source
      (List.mem_range.mp sourceMember)))
  exact mappedEq ▸ placedMember

/-- The actual oracle gates occupy their prepared/input wires and retain every final live system. -/
def nativeUnitary (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit (preparedContext exponentWidth width).register :=
  (mappedProgram exponentWidth width modulus base).seq
    (UnitaryCircuit.identity (preparedContext exponentWidth width).register
      (preparedContext exponentWidth width).physicalIdx
      (preparedContext exponentWidth width).identitiesNodup)

theorem gidneyExponentNativeUnitary_physical (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (nativeUnitary exponentWidth width modulus base).physical_idx =
      (preparedContext exponentWidth width).physicalIdx := by
  change (mappedProgram exponentWidth width modulus base).physical_idx ∪
    (preparedContext exponentWidth width).physicalIdx = _
  exact (mappedProgram_physical_range exponentWidth width modulus base).union_eq_right

/-- Placement changes only the basis coordinates of the already proved actual oracle operator. -/
theorem gidneyExponentNativeUnitary_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (nativeUnitary exponentWidth width modulus base).matrix =
      UnitaryOperator.reindex (preparedBasisEquiv exponentWidth width).symm
        (oracleProgram exponentWidth width modulus base).matrix := by
  let carrier := UnitaryCircuit.identity (preparedContext exponentWidth width).register
    (preparedContext exponentWidth width).physicalIdx
    (preparedContext exponentWidth width).identitiesNodup
  have transported := UnitaryCircuit.reindex_matrix
    (R := Qubits (oracleEncoding exponentWidth width).width)
    (S := (preparedContext exponentWidth width).register)
    (preparedBasisEquiv exponentWidth width).symm (oracleProgram exponentWidth width modulus base)
  have mapped := (UnitaryCircuit.relabel_matrix
    (transportedProgram exponentWidth width modulus base)
    (placementRelabeling exponentWidth width modulus base)).trans
      (congrArg (fun operator : UnitaryOperator (preparedContext exponentWidth width).register =>
        (operator : HilbertOperator (preparedContext exponentWidth width).register)) transported)
  apply Subtype.ext
  exact (UnitaryCircuit.seq_matrix (mappedProgram exponentWidth width modulus base) carrier).trans
    ((congrArg₂ (fun left right :
        HilbertOperator (preparedContext exponentWidth width).register => left * right)
      (UnitaryCircuit.identity_matrix (preparedContext exponentWidth width).register
        (preparedContext exponentWidth width).physicalIdx
        (preparedContext exponentWidth width).identitiesNodup) mapped).trans (one_mul _))

theorem gidneyExponentNativeUnitary_eventCost (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (nativeUnitary exponentWidth width modulus base).eventCost =
      (oracleProgram exponentWidth width modulus base).eventCost := by
  change (mappedProgram exponentWidth width modulus base).eventCost + 0 = _
  exact (add_zero _).trans
    ((UnitaryCircuit.relabel_eventCost (transportedProgram exponentWidth width modulus base)
      (placementRelabeling exponentWidth width modulus base)).trans
        (UnitaryCircuit.reindex_eventCost (R := Qubits (oracleEncoding exponentWidth width).width)
          (S := (preparedContext exponentWidth width).register)
          (preparedBasisEquiv exponentWidth width).symm
          (oracleProgram exponentWidth width modulus base)))

theorem gidneyExponentNativeUnitary_depth (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (nativeUnitary exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) =
      (oracleProgram exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) := by
  change (mappedProgram exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) + 0 = _
  exact (Nat.add_zero _).trans
    ((UnitaryCircuit.evaluatedEventDepth_relabel
      (transportedProgram exponentWidth width modulus base)
      (placementRelabeling exponentWidth width modulus base) (fun _ => 1)).trans
        (congrArg (DepthExpr.depthEval (fun _ => (1 : Nat)))
          (UnitaryCircuit.reindex_eventDepth
            (R := Qubits (oracleEncoding exponentWidth width).width)
            (S := (preparedContext exponentWidth width).register)
            (preparedBasisEquiv exponentWidth width).symm
            (oracleProgram exponentWidth width modulus base))))

/-- Actual preparation of both missing work words followed by the exact native oracle. -/
def nativeCode (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Circuit (Execution.OwnedQubits.context (exponentWidth + width))
      (preparedContext exponentWidth width) :=
  (Circuit.prepare (Execution.OwnedQubits.context (exponentWidth + width))
    workKey (workLayout exponentWidth width) (gidneyExponentWork_fresh exponentWidth width)
    (gidneyExponentWork_disjoint exponentWidth width)
    (workPreparation exponentWidth width modulus positive)).seq
      (Circuit.unitary (nativeUnitary exponentWidth width modulus base)
        (gidneyExponentNativeUnitary_physical exponentWidth width modulus base))

end

end QuantumAlg.MAU.Exponentiation.Gidney
