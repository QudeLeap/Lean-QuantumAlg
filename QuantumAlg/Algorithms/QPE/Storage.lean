/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Owned.Borrowed.Positions
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Actual phase-register Z writes and stored phase-estimation output

The leading `t` phase wires each write a distinct retained finite binary cell.
One charged packing instruction stores their `t` bits in the output cell.
All `t+n` quantum systems and both classical result representations remain
live in complete Output; the unmeasured source register is retained too.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

/-- Every original physical position remains present in the complete live register. -/
@[implicit_reducible]
def preparedWire (t n : Nat) (index : Fin (t + n)) : Fin (preparedContext t n).systemCount :=
  OwnedBorrowedQubits.positionEquiv t n index

theorem preparedWire_preserved (t n : Nat) (index : Fin (t + n)) :
    (preparedContext t n).quantumLayout.wire (preparedWire t n index) =
      (runtimeLayout t n).wire index :=
  OwnedBorrowedQubits.position_wire t n index

theorem preparedLayoutEquiv_value (t n : Nat) (basis : (runtimeLayout t n).register.Index)
    (index : Fin (t + n)) :
    (preparedLayoutEquiv t n basis (preparedWire t n index)).val = (basis index).val :=
  Execution.basisOfEqualWires_value (runtimeLayout t n) (preparedContext t n).quantumLayout
    (runtime_wires t n) basis index

theorem resultFresh (t n : Nat) : (⟨2⟩ : StorageKey) ∉ (preparedContext t n).keys := by
  change (⟨2⟩ : StorageKey) ∉ [⟨0⟩, ⟨1⟩]
  decide

/-- The retained packed output, before the separate per-wire measurement cells. -/
@[implicit_reducible]
def resultContext (t n : Nat) : RuntimeCtx .quantum :=
  (preparedContext t n).addRetained ⟨2⟩ (.bits t) (resultFresh t n)

/-- Every owned and borrowed quantum wire and every actual classical result remains live. -/
@[reducible] public def post (t n : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (resultContext t n) 2 t

def resultRef (t n : Nat) : CWriteRef (post t n) (.bits t) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead (preparedContext t n) ⟨2⟩ (.bits t) (resultFresh t n)) t

/-- The original leading phase wire through actual preparation and allocations. -/
def phaseWire (t n : Nat) (index : Fin t) : Fin (post t n).systemCount :=
  MeasurementCells.wireEquiv (resultContext t n) 2 t
    (preparedWire t n (Fin.castAdd n index))

theorem phaseWire_dimension (t n : Nat) (index : Fin t) :
    ((post t n).quantumLayout.wire (phaseWire t n index)).dimension = 2 := by
  rw [phaseWire, MeasurementCells.wireEquiv_preserved]
  change ((preparedContext t n).quantumLayout.wire
    (preparedWire t n (Fin.castAdd n index))).dimension = _
  rw [preparedWire_preserved]
  rfl

/-- Each phase wire writes its own actual finite binary value. -/
def phaseReadout (t n : Nat) (index : Fin t) : ZReadout (post t n) where
  wire := phaseWire t n index
  output := by
    rw [phaseWire_dimension]
    exact MeasurementCells.reference (resultContext t n) 2 t index

def readouts (t n : Nat) : List (ZReadout (post t n)) := List.ofFn (phaseReadout t n)

/-- The closed instruction reads these same actual cells and stores their bits. -/
def packing (t n : Nat) :
    ClassicalOp (.fixedVector t (.finite 2)) (.bits t) (post t n) (post t n) :=
  .packFiniteBits t (post t n) (MeasurementCells.input (resultContext t n) 2 t) (resultRef t n)

def outputBasisEquiv (t n : Nat) : (post t n).register.Index ≃ (Qubits (t + n)).Index :=
  (MeasurementCells.basisEquiv (resultContext t n) 2 t).symm.trans (preparedBasisEquiv t n)

theorem readouts_length (t n : Nat) : (readouts t n).length = t := List.length_ofFn

theorem readouts_qubits (t n : Nat) :
    ∀ item ∈ readouts t n, ((post t n).quantumLayout.wire item.wire).dimension = 2 := by
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact phaseWire_dimension t n index

end

end QuantumAlg.QuantumPhaseEstimation
