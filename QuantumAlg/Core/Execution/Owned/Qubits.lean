/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Execution.Context.Layout

/-!
# A supplied owned qubit word

The context contains exactly one supplied owned register. Its binary basis
is identified through equality of the actual ordered wire records. There is
no preparation, classical storage, borrowed workspace, or dimension padding.
The same live word contributes to resident and owned auxiliary accounting.
-/

namespace QuantumAlg.Execution.OwnedQubits

noncomputable section

private def qubitLayout (width : Nat) : QubitLayout width :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

private def layout (width : Nat) : QuantumLayout width := (qubitLayout width).toQuantumLayout

/-- A supplied owned word on physical systems zero through width minus one. -/
@[reducible] public def context (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ (layout width) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private lemma layout_wires (width : Nat) :
    (layout width).wires = (context width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (layout width).wires = (layout width).wires ++ []
  exact (List.append_nil _).symm

/-- The canonical typed-qubit layout has exactly the ordered wires of the
supplied owned-word context. -/
public lemma canonical_wires (width : Nat) :
    (QubitLayout.canonical width).toQuantum.wires =
      (context width).quantumLayout.wires := by
  rw [← layout_wires width]
  rfl

/-- Big-endian binary labels of exactly the context's physical qubit word. -/
public def basisEquiv (width : Nat) : (context width).register.Index ≃ (Qubits width).Index :=
  (Execution.basisOfEqualWires (layout width) (context width).quantumLayout
    (layout_wires width)).symm.trans (qubitLayout width).binaryIndexEquiv

/-- The full physical interface contains every supplied wire, even at width zero. -/
lemma ownedQubits_physicalIdx (width : Nat) :
    (context width).physicalIdx = List.range width := by
  change ((layout width).wires ++ []).map QuantumWire.identity = List.range width
  simp only [List.append_nil, QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun index : Fin width => index.val) = List.range width
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

/-- Independent dimension-sensitive space of one width-qubit word. -/
public def space (width : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then width else 0

/-- Resident space counts the supplied word and no other storage. -/
lemma ownedQubits_resident (width : Nat) :
    (context width).residentSpace = space width := by
  simp only [context, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (qubitLayout width).toQuantumLayout_dimensionCount dimension

/-- The owned auxiliary coordinate describes the same word, not another allocation. -/
lemma ownedQubits_auxiliary (width : Nat) :
    (context width).auxiliarySpace = space width := by
  simp only [context, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (qubitLayout width).toQuantumLayout_dimensionCount dimension

end

end QuantumAlg.Execution.OwnedQubits
