/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Context
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Actual phase-register results alongside an existing classical input

The leading `t` phase wires each write a distinct retained finite binary cell.
One charged packing instruction stores their `t` bits in the output cell.
All phase and target systems and both classical result representations remain
live in complete Output; the unmeasured target register is retained too.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

/-- Every prepared system keeps its actual position in the joint owned register. -/
@[implicit_reducible]
def preparedWire (t n : Nat) (index : Fin (t + n)) :
    Fin (preparedContext ctx noQuantum t n).systemCount :=
  ctx.addOwnedLayoutPositionEquiv ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)
    (Fin.castAdd ctx.systemCount index)

theorem preparedWire_preserved (t n : Nat) (index : Fin (t + n)) :
    (preparedContext ctx noQuantum t n).quantumLayout.wire (preparedWire ctx noQuantum t n index) =
      (runtimeLayout t n).wire index :=
  (ctx.addOwnedLayout_wire_preserved ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)
    (Fin.castAdd ctx.systemCount index)).trans
      (Fin.append_left _ _ index)

theorem preparedLayoutEquiv_value (t n : Nat) (basis : (runtimeLayout t n).register.Index)
    (index : Fin (t + n)) :
    (preparedLayoutEquiv ctx noQuantum t n basis
      (preparedWire ctx noQuantum t n index)).val = (basis index).val := by
  change (ctx.addOwnedLayoutBasisEquiv ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)
    ((QuantumLayout.appendBasisEquiv (runtimeLayout t n) ctx.quantumLayout
      (ctx.addOwnedLayout_layoutDisjoint (runtimeLayout t n)
        (preparationDisjoint ctx noQuantum t n))).symm
        (basis, Execution.emptyContextBasis ctx (input_systemCount ctx noQuantum)))
    (preparedWire ctx noQuantum t n index)).val = _
  exact (ctx.addOwnedLayout_basis_value_preserved ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n) _
    (Fin.castAdd ctx.systemCount index)).trans
      (QuantumLayout.appendJoinBasis_left_value _ _ _ basis _ index)

/-- The retained packed output, before the separate per-wire measurement cells. -/
@[implicit_reducible]
def resultContext (t n : Nat) : RuntimeCtx .quantum :=
  (preparedContext ctx noQuantum t n).addRetained
    (preparedContext ctx noQuantum t n).canonicalFreshKey (.bits t)
    (preparedContext ctx noQuantum t n).canonicalFreshKey_fresh

/-- Every owned quantum wire and every actual classical result remains live. -/
@[reducible] public def post (t n : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (resultContext ctx noQuantum t n) 2 t

def resultRef (t n : Nat) : CWriteRef (post ctx noQuantum t n) (.bits t) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead (preparedContext ctx noQuantum t n)
      (preparedContext ctx noQuantum t n).canonicalFreshKey (.bits t)
      (preparedContext ctx noQuantum t n).canonicalFreshKey_fresh) t

/-- The original leading phase wire through actual preparation and allocations. -/
def phaseWire (t n : Nat) (index : Fin t) : Fin (post ctx noQuantum t n).systemCount :=
  MeasurementCells.wireEquiv (resultContext ctx noQuantum t n) 2 t
    (preparedWire ctx noQuantum t n (Fin.castAdd n index))

theorem phaseWire_dimension (t n : Nat) (index : Fin t) :
    ((post ctx noQuantum t n).quantumLayout.wire
      (phaseWire ctx noQuantum t n index)).dimension = 2 := by
  rw [phaseWire, MeasurementCells.wireEquiv_preserved]
  change ((preparedContext ctx noQuantum t n).quantumLayout.wire
    (preparedWire ctx noQuantum t n (Fin.castAdd n index))).dimension = _
  rw [preparedWire_preserved ctx noQuantum]
  rfl

/-- Each phase wire writes its own actual finite binary value. -/
def phaseReadout (t n : Nat) (index : Fin t) : ZReadout (post ctx noQuantum t n) where
  wire := phaseWire ctx noQuantum t n index
  output := by
    rw [phaseWire_dimension ctx noQuantum]
    exact MeasurementCells.reference (resultContext ctx noQuantum t n) 2 t index

def readouts (t n : Nat) : List (ZReadout (post ctx noQuantum t n)) :=
  List.ofFn (phaseReadout ctx noQuantum t n)

/-- The closed instruction reads these same actual cells and stores their bits. -/
def packing (t n : Nat) :
    ClassicalOp (.fixedVector t (.finite 2)) (.bits t)
      (post ctx noQuantum t n) (post ctx noQuantum t n) :=
  .packFiniteBits t (post ctx noQuantum t n)
    (MeasurementCells.input (resultContext ctx noQuantum t n) 2 t) (resultRef ctx noQuantum t n)

def outputBasisEquiv (t n : Nat) :
    (post ctx noQuantum t n).register.Index ≃ (Qubits (t + n)).Index :=
  (MeasurementCells.basisEquiv (resultContext ctx noQuantum t n) 2 t).symm.trans
    (preparedBasisEquiv ctx noQuantum t n)

theorem readouts_length (t n : Nat) : (readouts ctx noQuantum t n).length = t := List.length_ofFn

theorem readouts_qubits (t n : Nat) :
    ∀ item ∈ readouts ctx noQuantum t n,
      ((post ctx noQuantum t n).quantumLayout.wire item.wire).dimension = 2 := by
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact phaseWire_dimension ctx noQuantum t n index

end

end QuantumAlg.OrderFinding.Sampling.Framed
