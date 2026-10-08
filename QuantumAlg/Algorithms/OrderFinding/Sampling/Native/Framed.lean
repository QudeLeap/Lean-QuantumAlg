/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Components.Classical.Model.BitWord.Placement

/-!
# Source sample with an existing classical input frame

The caller's original classical cells remain in the input and output. Fresh
phase and target qubits receive the same declared modular-exponentiation
query, native gates and stored phase readout as the empty-input sample. The
premise says that the input has no quantum systems; it imposes no restriction
on the borrowed classical values or their external-reference correlations.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

/-- The original source circuit uses no extra native or classical grants. -/
public abbrev model {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    ExecutionModel := Sampling.Native.model access

include noQuantum in
private theorem preparationDisjoint (t width : Nat) :
    List.Disjoint (Sampling.Native.runtimeLayout t width).identities ctx.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum]
  exact List.disjoint_nil_right _

/-- Add only a fresh quantum block to the caller's existing classical frame. -/
@[implicit_reducible]
public def preparedContext (t width : Nat) : RuntimeCtx .quantum :=
  ctx.addOwnedLayout ctx.canonicalFreshKey (Sampling.Native.runtimeLayout t width)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t width)

private theorem preparedContext_quantumWires (t width : Nat) :
    (preparedContext ctx noQuantum t width).quantumWires =
      (Sampling.Native.runtimeLayout t width).wires := by
  change (Sampling.Native.runtimeLayout t width).wires ++ ctx.quantumWires = _
  rw [noQuantum, List.append_nil]

/-- The native word and prepared runtime have exactly the same physical wires. -/
public theorem prepared_wires (t width : Nat) :
    (Sampling.Native.runtimeLayout t width).wires =
      (preparedContext ctx noQuantum t width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, preparedContext_quantumWires]

/-- Run the same source word while retaining the input's classical cells. -/
public def nativeProgram {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    UnitaryCircuit AlgorithmGate.model (OrderFinding.Native.sourceModel access)
      (preparedContext ctx noQuantum t width).quantumLayout :=
  Execution.unitaryOfEqualWires (Sampling.Native.runtimeLayout t width)
    (preparedContext ctx noQuantum t width).quantumLayout
    (prepared_wires ctx noQuantum t width) (OrderFinding.Native.circuit access)

/-- One actual zero preparation allocates the phase and target block. -/
public def preparationCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) ctx (preparedContext ctx noQuantum t width) :=
  .prepareZero ctx ctx.canonicalFreshKey (Sampling.Native.runtimeLayout t width)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t width)

/-- Retain one new packed phase word alongside the original input frame. -/
@[implicit_reducible]
public def resultContext (t width : Nat) : RuntimeCtx .quantum :=
  (preparedContext ctx noQuantum t width).addRetained
    (preparedContext ctx noQuantum t width).canonicalFreshKey (.bits t)
    (preparedContext ctx noQuantum t width).canonicalFreshKey_fresh

/-- All original cells and new quantum and measured cells remain live. -/
@[reducible] public def post (t width : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (resultContext ctx noQuantum t width) 2 t

/-- The actual packed phase-word location. -/
public def resultRef (t width : Nat) : CWriteRef (post ctx noQuantum t width) (.bits t) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead (preparedContext ctx noQuantum t width)
      (preparedContext ctx noQuantum t width).canonicalFreshKey (.bits t)
      (preparedContext ctx noQuantum t width).canonicalFreshKey_fresh) t

/-- Every original phase and target wire retains its physical identity. -/
public def preparedWire (t width : Nat) (index : Fin (t + width)) :
    Fin (preparedContext ctx noQuantum t width).systemCount :=
  ctx.addOwnedLayoutPositionEquiv ctx.canonicalFreshKey
    (Sampling.Native.runtimeLayout t width) ctx.canonicalFreshKey_fresh
    (preparationDisjoint ctx noQuantum t width) (Fin.castAdd ctx.systemCount index)

private theorem preparedWire_preserved (t width : Nat) (index : Fin (t + width)) :
    (preparedContext ctx noQuantum t width).quantumLayout.wire
      (preparedWire ctx noQuantum t width index) =
        (Sampling.Native.runtimeLayout t width).wire index :=
  (ctx.addOwnedLayout_wire_preserved ctx.canonicalFreshKey
    (Sampling.Native.runtimeLayout t width) ctx.canonicalFreshKey_fresh
    (preparationDisjoint ctx noQuantum t width)
    (Fin.castAdd ctx.systemCount index)).trans (Fin.append_left _ _ index)

/-- The phase qubit remains in place through all retained-cell allocations. -/
public def phaseWire (t width : Nat) (index : Fin t) :
    Fin (post ctx noQuantum t width).systemCount :=
  MeasurementCells.wireEquiv (resultContext ctx noQuantum t width) 2 t
    (preparedWire ctx noQuantum t width (Fin.castAdd width index))

/-- Every selected phase position is still a dimension-two wire. -/
public theorem phaseWire_dimension (t width : Nat) (index : Fin t) :
    ((post ctx noQuantum t width).quantumLayout.wire
      (phaseWire ctx noQuantum t width index)).dimension = 2 := by
  rw [phaseWire, MeasurementCells.wireEquiv_preserved]
  change ((preparedContext ctx noQuantum t width).quantumLayout.wire
    (preparedWire ctx noQuantum t width (Fin.castAdd width index))).dimension = _
  rw [preparedWire_preserved]
  rfl

/-- Each original phase wire writes its corresponding retained binary cell. -/
public def phaseReadout (t width : Nat) (index : Fin t) :
    ZReadout (post ctx noQuantum t width) where
  wire := phaseWire ctx noQuantum t width index
  output := by
    rw [phaseWire_dimension]
    exact MeasurementCells.reference (resultContext ctx noQuantum t width) 2 t index

/-- Read every phase position once in its original order. -/
public def readouts (t width : Nat) : List (ZReadout (post ctx noQuantum t width)) :=
  List.ofFn (phaseReadout ctx noQuantum t width)

/-- A selected bit-word operation packs those same measured cells. -/
public def packing (t width : Nat) :
    ClassicalOp (.fixedVector t (.finite 2)) (.bits t)
      (post ctx noQuantum t width) (post ctx noQuantum t width) :=
  .packFiniteBits t (post ctx noQuantum t width)
    (MeasurementCells.input (resultContext ctx noQuantum t width) 2 t)
    (resultRef ctx noQuantum t width)

/-- Allocate the packed output and each binary measurement cell. -/
public def allocationCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) (preparedContext ctx noQuantum t width)
      (post ctx noQuantum t width) :=
  .seq (.retain (model := model access) (preparedContext ctx noQuantum t width)
    (preparedContext ctx noQuantum t width).canonicalFreshKey (.bits t)
    (preparedContext ctx noQuantum t width).canonicalFreshKey_fresh)
    (MeasurementCells.allocate (model := model access)
      (resultContext ctx noQuantum t width) 2 t)

/-- Prepare, execute the source query word, then allocate retained outputs. -/
public def beforeMeasurement {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) ctx (post ctx noQuantum t width) :=
  .seq (preparationCode ctx noQuantum access)
    (.seq (.unitary (nativeProgram ctx noQuantum access))
      (allocationCode ctx noQuantum access))

/-- Actual Z writes and finite-word packing finish the sample. -/
public def readoutCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) (post ctx noQuantum t width)
      (post ctx noQuantum t width) :=
  .seq (Circuit.measurementSequence (readouts ctx noQuantum t width))
    (.classical (BitWord.application (packing ctx noQuantum t width)))

/-- One complete sample preserves the caller's original classical frame. -/
public def code {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    Circuit (model access) ctx (post ctx noQuantum t width) :=
  .seq (beforeMeasurement ctx noQuantum access)
    (readoutCode ctx noQuantum access)

/-- The returned word is the actual packed phase result from the same code. -/
@[expose] public def run {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    AlgorithmRun (model access) ctx (post ctx noQuantum t width) (.bits t) where
  code := code ctx noQuantum access
  output := Output.all (post ctx noQuantum t width)
    (.read (.storage (resultRef ctx noQuantum t width).toCStorageRef))

/-- The complete manifest reads the retained word after real measurement. -/
public theorem run_result {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (record : (run ctx noQuantum access).Record) :
    (run ctx noQuantum access).result record =
      record.1.read (.storage (resultRef ctx noQuantum t width).toCStorageRef) := rfl

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
