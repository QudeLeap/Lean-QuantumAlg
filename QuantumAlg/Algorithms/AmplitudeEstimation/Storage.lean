/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Actual phase-register Z writes and stored amplitude-estimation output

The leading `t` phase wires each write a distinct retained finite binary cell.
One charged packing instruction stores their `t` bits in the output cell.
All phase, explicit work, and source systems and both classical result
representations remain
live in complete Output; the unmeasured source register is retained too.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

/-- Every prepared system keeps its actual position in the joint owned register. -/
@[implicit_reducible]
def preparedWire (t n : Nat) (index : Fin (t + (Elementary.helperWidth t n + n))) :
    Fin (preparedContext t n).systemCount :=
  pre.addOwnedLayoutPositionEquiv ⟨0⟩ (runtimeLayout t n)
    preparationFresh (preparationDisjoint t n) (Fin.castAdd pre.systemCount index)

lemma preparedWire_preserved (t n : Nat) (index : Fin (t + (Elementary.helperWidth t n + n))) :
    (preparedContext t n).quantumLayout.wire (preparedWire t n index) =
      (runtimeLayout t n).wire index :=
  (pre.addOwnedLayout_wire_preserved ⟨0⟩ (runtimeLayout t n)
    preparationFresh (preparationDisjoint t n) (Fin.castAdd pre.systemCount index)).trans
      (Fin.append_left _ _ index)

lemma preparedLayoutEquiv_value (t n : Nat) (basis : (runtimeLayout t n).register.Index)
    (index : Fin (t + (Elementary.helperWidth t n + n))) :
    (preparedLayoutEquiv t n basis (preparedWire t n index)).val = (basis index).val := by
  change (pre.addOwnedLayoutBasisEquiv ⟨0⟩ (runtimeLayout t n)
    preparationFresh (preparationDisjoint t n)
    ((QuantumLayout.appendBasisEquiv (runtimeLayout t n) pre.quantumLayout
      (pre.addOwnedLayout_layoutDisjoint (runtimeLayout t n) (preparationDisjoint t n))).symm
        (basis, Execution.emptyContextBasis pre pre_systemCount))
    (preparedWire t n index)).val = _
  exact (pre.addOwnedLayout_basis_value_preserved ⟨0⟩ (runtimeLayout t n)
    preparationFresh (preparationDisjoint t n) _ (Fin.castAdd pre.systemCount index)).trans
      (QuantumLayout.appendJoinBasis_left_value _ _ _ basis _ index)

lemma resultFresh (t n : Nat) : (⟨1⟩ : StorageKey) ∉ (preparedContext t n).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The retained packed output, before the separate per-wire measurement cells. -/
@[implicit_reducible]
def resultContext (t n : Nat) : RuntimeCtx .quantum :=
  (preparedContext t n).addRetained ⟨1⟩ (.bits t) (resultFresh t n)

/-- Every owned quantum wire and every actual classical result remains live. -/
@[reducible] public def post (t n : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (resultContext t n) 2 t

def resultRef (t n : Nat) : CWriteRef (post t n) (.bits t) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead (preparedContext t n) ⟨1⟩ (.bits t) (resultFresh t n)) t

/-- The original leading phase wire through actual preparation and allocations. -/
def phaseWire (t n : Nat) (index : Fin t) : Fin (post t n).systemCount :=
  MeasurementCells.wireEquiv (resultContext t n) 2 t
    (preparedWire t n (Fin.castAdd (Elementary.helperWidth t n + n) index))

lemma phaseWire_dimension (t n : Nat) (index : Fin t) :
    ((post t n).quantumLayout.wire (phaseWire t n index)).dimension = 2 := by
  rw [phaseWire, MeasurementCells.wireEquiv_preserved]
  change ((preparedContext t n).quantumLayout.wire
    (preparedWire t n (Fin.castAdd (Elementary.helperWidth t n + n) index))).dimension = _
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

def outputBasisEquiv (t n : Nat) :
    (post t n).register.Index ≃ (Qubits (t + (Elementary.helperWidth t n + n))).Index :=
  (MeasurementCells.basisEquiv (resultContext t n) 2 t).symm.trans (preparedBasisEquiv t n)

lemma readouts_length (t n : Nat) : (readouts t n).length = t := List.length_ofFn

lemma readouts_qubits (t n : Nat) :
    ∀ item ∈ readouts t n, ((post t n).quantumLayout.wire item.wire).dimension = 2 := by
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact phaseWire_dimension t n index

end

end QuantumAlg.AmplitudeEstimation
