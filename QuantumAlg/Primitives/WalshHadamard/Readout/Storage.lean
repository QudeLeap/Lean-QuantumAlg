/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Walsh-Hadamard query readout physical measurements and actual classical result

Each of the n query wires writes one retained finite binary cell. A real
packing instruction subsequently writes the n-bit result. The target wire
is not measured; every quantum system and every allocated classical cell
remains live. At n = 0 the measurement list is empty, while the width-zero
packing instruction still executes and emits its own event.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

open QuantumAlg.Execution

/-- The actual preparation places each declared wire at the same ordered position. -/
@[implicit_reducible]
def preparedWire (n : Nat) (index : Fin (n + 1)) : Fin (preparedContext n).systemCount :=
  pre.addOwnedLayoutPositionEquiv ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) (Fin.castAdd pre.systemCount index)

lemma preparedWire_preserved (n : Nat) (index : Fin (n + 1)) :
    (preparedContext n).quantumLayout.wire (preparedWire n index) =
      (runtimeLayout n).wire index := by
  exact (pre.addOwnedLayout_wire_preserved ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) (Fin.castAdd pre.systemCount index)).trans
      (Fin.append_left _ _ index)

/-- The preparation assembly retains the value of every corresponding physical wire. -/
lemma preparedLayoutEquiv_value (n : Nat) (basis : (runtimeLayout n).register.Index)
    (index : Fin (n + 1)) :
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

lemma resultFresh (n : Nat) : (⟨2⟩ : StorageKey) ∉ (preparedContext n).keys := by
  change (⟨2⟩ : StorageKey) ∉ [⟨1⟩, ⟨0⟩]
  decide

/-- One retained output bit string, before allocating the separate measured-result cells. -/
@[implicit_reducible]
def resultContext (n : Nat) : RuntimeCtx .quantum :=
  (preparedContext n).addRetained ⟨2⟩ (.bits n) (resultFresh n)

/-- Every prepared quantum system and every actual result cell remains in the output context. -/
@[reducible] public def post (n : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (resultContext n) 2 n

/-- Actual storage holding the final packed result. -/
def resultRef (n : Nat) : CWriteRef (post n) (.bits n) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead (preparedContext n) ⟨2⟩ (.bits n) (resultFresh n)) n

/-- Query positions are carried through the actual preparation and classical allocations. -/
def queryWire (n : Nat) (index : Fin n) : Fin (post n).systemCount :=
  MeasurementCells.wireEquiv (resultContext n) 2 n (preparedWire n index.castSucc)

lemma queryWire_dimension (n : Nat) (index : Fin n) :
    ((post n).quantumLayout.wire (queryWire n index)).dimension = 2 := by
  rw [queryWire, MeasurementCells.wireEquiv_preserved]
  change ((preparedContext n).quantumLayout.wire
    (preparedWire n index.castSucc)).dimension = _
  rw [preparedWire_preserved]
  rfl

/-- Each query wire writes its own real finite binary cell. -/
def queryReadout (n : Nat) (index : Fin n) : ZReadout (post n) where
  wire := queryWire n index
  output := by
    rw [queryWire_dimension]
    exact MeasurementCells.reference (resultContext n) 2 n index

/-- Measure the query wires in increasing logical order, leaving the target untouched. -/
def readouts (n : Nat) : List (ZReadout (post n)) := List.ofFn (queryReadout n)

/-- This instruction reads the same measured cells and performs the charged bit conversion. -/
def packing (n : Nat) :
    ClassicalOp (.fixedVector n (.finite 2)) (.bits n) (post n) (post n) :=
  .packFiniteBits n (post n) (MeasurementCells.input (resultContext n) 2 n) (resultRef n)

/-- The binary label of the same complete live output basis before measurement. -/
def outputBasisEquiv (n : Nat) : (post n).register.Index ≃ (Qubits (n + 1)).Index :=
  (MeasurementCells.basisEquiv (resultContext n) 2 n).symm.trans (preparedBasisEquiv n)

lemma readouts_length (n : Nat) : (readouts n).length = n := by
  exact List.length_ofFn

lemma readouts_qubits (n : Nat) :
    ∀ item ∈ readouts n, ((post n).quantumLayout.wire item.wire).dimension = 2 := by
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact queryWire_dimension n index

end

end QuantumAlg.WalshHadamard.Readout
