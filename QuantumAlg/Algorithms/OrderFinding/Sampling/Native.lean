/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Native
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Algorithm.AlgorithmRun
public import QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Algorithms.OrderFinding.Native
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Complete source order-finding sample

The empty input receives one owned all-zero phase and target register. The
native word executes one declared modular-exponentiation query, then each
phase wire writes a retained Z-result cell. A closed finite-word instruction
packs those measured bits into the returned result. The target remains live
through the complete output [dW19, qcnotes.tex:2203-2225].
-/

namespace QuantumAlg.OrderFinding.Sampling.Native

noncomputable section

open QuantumAlg.Execution

/-- Native gates, one supplied source query and width-indexed classical operations. -/
public abbrev model {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    ExecutionModel :=
  .quantum AlgorithmGate.model (OrderFinding.Native.sourceModel access) BitWord.model .empty

/-- The source sample has no prior quantum or classical input. -/
@[reducible] public def pre : RuntimeCtx .quantum := RuntimeCtx.empty

/-- All phase and target qubits keep their original canonical physical identities. -/
public abbrev runtimeLayout (t width : Nat) : QuantumLayout (t + width) :=
  (QuantumSignature.qubits (t + width)).canonicalPlacement.layout

private theorem preparationFresh : (⟨0⟩ : StorageKey) ∉ pre.keys := by decide

private theorem preparationDisjoint (t width : Nat) :
    List.Disjoint (runtimeLayout t width).identities pre.physicalIdx :=
  List.disjoint_nil_right _

/-- All source qubits are owned and initialized before the unitary word. -/
@[implicit_reducible]
public def preparedContext (t width : Nat) : RuntimeCtx .quantum :=
  pre.addOwnedLayout ⟨0⟩ (runtimeLayout t width)
    preparationFresh (preparationDisjoint t width)

private theorem preparedContext_quantumWires (t width : Nat) :
    (preparedContext t width).quantumWires = (runtimeLayout t width).wires := by
  change (runtimeLayout t width).wires ++ [] = _
  exact List.append_nil _

public theorem prepared_wires (t width : Nat) :
    (runtimeLayout t width).wires = (preparedContext t width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, preparedContext_quantumWires]

/-- The selected source word acts on exactly the wires prepared by this run. -/
public def nativeProgram {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    UnitaryCircuit AlgorithmGate.model (OrderFinding.Native.sourceModel access)
      (preparedContext t width).quantumLayout :=
  Execution.unitaryOfEqualWires (runtimeLayout t width)
    (preparedContext t width).quantumLayout (prepared_wires t width)
      (OrderFinding.Native.circuit access)

private theorem resultFresh (t width : Nat) :
    (⟨1⟩ : StorageKey) ∉ (preparedContext t width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The packed result occupies an actual retained cell. -/
@[implicit_reducible]
public def resultContext (t width : Nat) : RuntimeCtx .quantum :=
  (preparedContext t width).addRetained ⟨1⟩ (.bits t) (resultFresh t width)

/-- The output retains both quantum registers, the packed result and each bit cell. -/
@[reducible] public def post (t width : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (resultContext t width) 2 t

/-- Store the actual finite-word result in the retained output cell. -/
public def resultRef (t width : Nat) : CWriteRef (post t width) (.bits t) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead (preparedContext t width) ⟨1⟩ (.bits t)
      (resultFresh t width)) t

/-- Preserve the physical position of each original phase or target qubit. -/
public def preparedWire (t width : Nat) (index : Fin (t + width)) :
    Fin (preparedContext t width).systemCount :=
  pre.addOwnedLayoutPositionEquiv ⟨0⟩ (runtimeLayout t width)
    preparationFresh (preparationDisjoint t width) (Fin.castAdd pre.systemCount index)

private theorem preparedWire_preserved (t width : Nat) (index : Fin (t + width)) :
    (preparedContext t width).quantumLayout.wire (preparedWire t width index) =
      (runtimeLayout t width).wire index :=
  (pre.addOwnedLayout_wire_preserved ⟨0⟩ (runtimeLayout t width)
    preparationFresh (preparationDisjoint t width)
    (Fin.castAdd pre.systemCount index)).trans (Fin.append_left _ _ index)

/-- The selected phase qubit passes unchanged through the result allocations. -/
public def phaseWire (t width : Nat) (index : Fin t) : Fin (post t width).systemCount :=
  MeasurementCells.wireEquiv (resultContext t width) 2 t
    (preparedWire t width (Fin.castAdd width index))

public theorem phaseWire_dimension (t width : Nat) (index : Fin t) :
    ((post t width).quantumLayout.wire (phaseWire t width index)).dimension = 2 := by
  rw [phaseWire, MeasurementCells.wireEquiv_preserved]
  change ((preparedContext t width).quantumLayout.wire
    (preparedWire t width (Fin.castAdd width index))).dimension = _
  rw [preparedWire_preserved]
  rfl

/-- One actual Z readout writes each original phase wire to its matching cell. -/
public def phaseReadout (t width : Nat) (index : Fin t) : ZReadout (post t width) where
  wire := phaseWire t width index
  output := by
    rw [phaseWire_dimension]
    exact MeasurementCells.reference (resultContext t width) 2 t index

/-- The complete phase register is measured in its original logical order. -/
public def readouts (t width : Nat) : List (ZReadout (post t width)) :=
  List.ofFn (phaseReadout t width)

/-- The output word is packed from those same retained measurement cells. -/
public def packing (t width : Nat) :
    ClassicalOp (.fixedVector t (.finite 2)) (.bits t) (post t width) (post t width) :=
  .packFiniteBits t (post t width)
    (MeasurementCells.input (resultContext t width) 2 t) (resultRef t width)

/-- Every source system is prepared to its original computational zero. -/
public def preparationCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) pre (preparedContext t width) :=
  .prepareZero pre ⟨0⟩ (runtimeLayout t width)
    preparationFresh (preparationDisjoint t width)

/-- Allocate the packed result and the individual measured-bit cells. -/
public def allocationCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) (preparedContext t width) (post t width) :=
  .seq (.retain (model := model access) (preparedContext t width)
    ⟨1⟩ (.bits t) (resultFresh t width))
    (MeasurementCells.allocate (model := model access) (resultContext t width) 2 t)

/-- Source preparation and the unitary word precede the measured readout. -/
public def beforeMeasurement {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) pre (post t width) :=
  .seq (preparationCode access)
    (.seq (.unitary (nativeProgram access)) (allocationCode access))

/-- Retained Z writes and the closed packing instruction complete one sample. -/
public def readoutCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (model access) (post t width) (post t width) :=
  .seq (Circuit.measurementSequence (readouts t width))
    (.classical (BitWord.application (packing t width)))

/-- The full source sample includes preparation, one query and actual stored readout. -/
public def code {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    Circuit (model access) pre (post t width) :=
  .seq (beforeMeasurement access) (readoutCode access)

/-- The result is read from the retained word produced by this exact code. -/
@[expose] public def run {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    AlgorithmRun (model access) pre (post t width) (.bits t) where
  code := code access
  output := Output.all (post t width)
    (.read (.storage (resultRef t width).toCStorageRef))

/-- The endpoint returns its actual retained packed word. -/
public theorem run_result {N x t width : Nat} (access : ModExpOracleAccess N x t width)
    (record : (run access).Record) :
    (run access).result record =
      record.1.read (.storage (resultRef t width).toCStorageRef) := rfl

end

end QuantumAlg.OrderFinding.Sampling.Native
