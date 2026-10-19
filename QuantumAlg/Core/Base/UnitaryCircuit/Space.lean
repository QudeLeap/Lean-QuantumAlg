/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.Accounting.Flow
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Space of the circuit's actual physical interface

A circuit's type fixes its complete physical layout, including idle systems.
Each system contributes to the space coordinate for its own positive dimension.
No separate footprint or caller-supplied containment claim chooses this space.
An identity circuit on a nonempty layout therefore still occupies that layout.

The isolated unitary circuit borrows its entire interface and cannot allocate
or release storage. Its resident space contains the whole interface, while
its auxiliary space is zero. Ownership and extra work storage belong to the
surrounding typed execution. The canonical context below is an observation of
one interface; its private key is not an execution-time allocator.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- A private storage identity for the canonical observation of one borrowed interface. -/
private def interfaceStorageKey : StorageKey := ⟨0⟩

/-- The full physical interface is borrowed, including every idle system. -/
def interfaceContext {count : Nat} (layout : QuantumLayout count) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedLayout interfaceStorageKey layout
    (by change interfaceStorageKey ∉ ([] : List StorageKey); simp)
    (by change List.Disjoint layout.identities []; simp)

/-- A unitary circuit keeps its actual input/output interface live throughout execution.
The circuit parameter certifies this layout through its type; no footprint proof is needed. -/
@[nolint unusedArguments]
def interfaceSpaceFlow (_circuit : UnitaryCircuit gates oracles layout) :
    SpaceFlow (interfaceContext layout) (interfaceContext layout) :=
  SpaceFlow.stay (interfaceContext layout)

@[simp] lemma interfaceContext_physicalIdx {count : Nat}
    (layout : QuantumLayout count) :
    (interfaceContext layout).physicalIdx = layout.identities := by
  rw [RuntimeCtx.physicalIdx_eq_flatMap]
  change [RuntimeEntry.borrowedLayout interfaceStorageKey layout].flatMap
    RuntimeEntry.physicalIdx = _
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (List.ofFn layout.wire).map QuantumWire.identity = _
  rw [List.map_ofFn]
  rfl

@[simp] lemma interfaceContext_residentSpace {count : Nat}
    (layout : QuantumLayout count) :
    (interfaceContext layout).residentSpace = SpacePool.ofQuantumLayout layout := by
  simp [interfaceContext]

@[simp] lemma interfaceContext_auxiliarySpace {count : Nat}
    (layout : QuantumLayout count) : (interfaceContext layout).auxiliarySpace = 0 := by
  simp [interfaceContext]

/-- Resident space counts every actual interface system once, independently of touched gates. -/
@[simp] lemma interfaceSpaceFlow_peakResidentSpace
    (circuit : UnitaryCircuit gates oracles layout) :
    circuit.interfaceSpaceFlow.peakResidentSpace = SpacePool.ofQuantumLayout layout := by
  simp [interfaceSpaceFlow]

/-- The unitary construction itself introduces no owned auxiliary storage. -/
@[simp] lemma interfaceSpaceFlow_peakAuxiliarySpace
    (circuit : UnitaryCircuit gates oracles layout) :
    circuit.interfaceSpaceFlow.peakAuxiliarySpace = 0 := by
  simp [interfaceSpaceFlow]

/-- Native dimension coordinates retain heterogeneous systems instead of converting Hilbert size. -/
lemma interfaceSpaceFlow_systems
    (circuit : UnitaryCircuit gates oracles layout) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) circuit.interfaceSpaceFlow.peakResidentSpace =
      layout.dimensionCount dimension := by
  simp

/-- A quantum-only borrowed interface introduces no classical storage cells. -/
lemma interfaceSpaceFlow_classicalBits
    (circuit : UnitaryCircuit gates oracles layout) :
    SpacePool.count .classicalBits circuit.interfaceSpaceFlow.peakResidentSpace = 0 := by
  simp

end

end QuantumAlg.UnitaryCircuit
