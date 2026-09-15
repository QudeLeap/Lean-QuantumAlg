/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Algorithms.Grover.Elementary.Construction
import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Grover's actual source measurements and complete retained storage

Every search wire writes its own retained finite binary cell. One closed
packing instruction reads those n cells and writes the final n-bit index.
Every search and work wire, both result representations, and the borrowed
input remain in complete Output. Only the n source wires are measured.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

open QuantumAlg.Execution

/-- The actual preparation places each declared wire at the same ordered position. -/
@[implicit_reducible]
def preparedWire (n : Nat) (index : Fin n) : Fin (preparedContext n).systemCount :=
  pre.addOwnedLayoutPositionEquiv ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) (Fin.castAdd pre.systemCount index)

theorem preparedWire_preserved (n : Nat) (index : Fin n) :
    (preparedContext n).quantumLayout.wire (preparedWire n index) =
      (runtimeLayout n).wire index := by
  exact (pre.addOwnedLayout_wire_preserved ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) (Fin.castAdd pre.systemCount index)).trans
      (Fin.append_left _ _ index)

/-- The preparation assembly retains the value of every corresponding physical wire. -/
theorem preparedLayoutEquiv_value (n : Nat) (basis : (runtimeLayout n).register.Index)
    (index : Fin n) :
    (preparedLayoutEquiv n basis (preparedWire n index)).val = (basis index).val := by
  change (pre.addOwnedLayoutBasisEquiv ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n)
    ((QuantumLayout.appendBasisEquiv (runtimeLayout n) pre.quantumLayout
      (pre.addOwnedLayout_layoutDisjoint (runtimeLayout n) (preparationDisjoint n))).symm
        (basis, Execution.emptyContextBasis pre pre_systemCount))
    (preparedWire n index)).val = _
  exact (pre.addOwnedLayout_basis_value_preserved ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) _ (Fin.castAdd pre.systemCount index)).trans
      (QuantumLayout.appendJoinBasis_left_value _ _ _ basis _ index)

theorem resultFresh (n k : Nat) :
    (⟨2⟩ : StorageKey) ∉ (preparedContext (totalQubits n k)).keys := by
  change (⟨2⟩ : StorageKey) ∉ [⟨1⟩, ⟨0⟩]
  decide

/-- One retained output bit string, before allocating the separate measured-result cells. -/
@[implicit_reducible]
def resultContext (n k : Nat) : RuntimeCtx .quantum :=
  (preparedContext (totalQubits n k)).addRetained ⟨2⟩ (.bits n) (resultFresh n k)

/-- Every prepared quantum system and every actual result cell remains in the output context. -/
@[reducible] public def post (n k : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (resultContext n k) 2 n

/-- Actual storage holding the final packed result. -/
def resultRef (n k : Nat) : CWriteRef (post n k) (.bits n) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead (preparedContext (totalQubits n k))
      ⟨2⟩ (.bits n) (resultFresh n k)) n

/-- Query positions are carried through the actual preparation and classical allocations. -/
def queryWire (n k : Nat) (index : Fin n) : Fin (post n k).systemCount :=
  MeasurementCells.wireEquiv (resultContext n k) 2 n (preparedWire (totalQubits n k)
    (Fin.castAdd (helperWidth n k) index))

theorem queryWire_dimension (n k : Nat) (index : Fin n) :
    ((post n k).quantumLayout.wire (queryWire n k index)).dimension = 2 := by
  rw [queryWire, MeasurementCells.wireEquiv_preserved]
  change ((preparedContext (totalQubits n k)).quantumLayout.wire
    (preparedWire (totalQubits n k)
    (Fin.castAdd (helperWidth n k) index))).dimension = _
  rw [preparedWire_preserved]
  rfl

/-- Each query wire writes its own real finite binary cell. -/
def queryReadout (n k : Nat) (index : Fin n) : ZReadout (post n k) where
  wire := queryWire n k index
  output := by
    rw [queryWire_dimension]
    exact MeasurementCells.reference (resultContext n k) 2 n index

/-- Measure every search wire in increasing logical order. -/
def readouts (n k : Nat) : List (ZReadout (post n k)) := List.ofFn (queryReadout n k)

/-- This instruction reads the same measured cells and performs the charged bit conversion. -/
def packing (n k : Nat) :
    ClassicalOp (.fixedVector n (.finite 2)) (.bits n) (post n k) (post n k) :=
  .packFiniteBits n (post n k) (MeasurementCells.input (resultContext n k) 2 n) (resultRef n k)

/-- The binary label of the same complete live output basis before measurement. -/
def outputBasisEquiv (n k : Nat) :
    (post n k).register.Index ≃ (Qubits (totalQubits n k)).Index :=
  (MeasurementCells.basisEquiv (resultContext n k) 2 n).symm.trans
    (preparedBasisEquiv (totalQubits n k))

/-- The original source label is the leading factor of the actual complete output basis. -/
def outputSource (n k : Nat) (basis : (post n k).register.Index) : Fin (2 ^ n) :=
  ((prodEquiv (m := n) (n := helperWidth n k)).symm
    (outputBasisEquiv n k basis)).1

theorem readouts_length (n k : Nat) : (readouts n k).length = n := by
  exact List.length_ofFn

theorem readouts_qubits (n k : Nat) :
    ∀ item ∈ readouts n k, ((post n k).quantumLayout.wire item.wire).dimension = 2 := by
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact queryWire_dimension n k index

end

end QuantumAlg.GroverSearch
