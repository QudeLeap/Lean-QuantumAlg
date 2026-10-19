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
# A supplied mutable qubit interface

The context contains exactly one caller-supplied register. Its systems remain
resident and may be transformed into the output, so they carry neither a
borrowed-restoration obligation nor an algorithm-owned auxiliary-space charge.
No preparation or independence promise is attached to the interface.
-/

namespace QuantumAlg.Execution.SuppliedQubits

noncomputable section

private def qubitLayout (width : Nat) : QubitLayout width :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

private def layout (width : Nat) : QuantumLayout width := (qubitLayout width).toQuantumLayout

/-- A supplied mutable word on physical systems zero through width minus one. -/
@[reducible] public def context (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addSuppliedLayout ⟨0⟩ (layout width) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private lemma layout_wires (width : Nat) :
    (layout width).wires = (context width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (layout width).wires = (layout width).wires ++ []
  exact (List.append_nil _).symm

/-- Big-endian binary labels of exactly the supplied physical qubit word. -/
public def basisEquiv (width : Nat) : (context width).register.Index ≃ (Qubits width).Index :=
  (Execution.basisOfEqualWires (layout width) (context width).quantumLayout
    (layout_wires width)).symm.trans (qubitLayout width).binaryIndexEquiv

/-- The full physical interface contains every supplied wire, including at width zero. -/
lemma suppliedQubits_physicalIdx (width : Nat) :
    (context width).physicalIdx = List.range width := by
  change ((layout width).wires ++ []).map QuantumWire.identity = List.range width
  simp only [List.append_nil, QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun index : Fin width => index.val) = List.range width
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

/-- Dimension-sensitive space of one width-qubit interface. -/
public def space (width : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then width else 0

/-- Resident space counts every supplied system. -/
lemma suppliedQubits_resident (width : Nat) :
    (context width).residentSpace = space width := by
  simp only [context, RuntimeCtx.residentSpace_addSuppliedLayout,
    RuntimeCtx.residentSpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (qubitLayout width).toQuantumLayout_dimensionCount dimension

/-- Caller-supplied input/output systems do not count as auxiliary storage. -/
lemma suppliedQubits_auxiliary (width : Nat) :
    (context width).auxiliarySpace = 0 := by
  simp only [context, RuntimeCtx.auxiliarySpace_addSuppliedLayout,
    RuntimeCtx.auxiliarySpace_empty]

end

end QuantumAlg.Execution.SuppliedQubits
