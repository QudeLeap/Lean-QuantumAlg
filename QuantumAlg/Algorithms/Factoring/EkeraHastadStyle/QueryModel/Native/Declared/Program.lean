/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Primitives.ShortDLP.Oracle.Declared
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Placement
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# One actual original-width short-DLP observation

The input fixes one oracle model for every runtime parameter value. A stored
parameter selects one declared query instance. The same original-width bank,
finite measurement cells and paid bit packing survive in the complete output.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

/-- All runtime parameter values use one fixed group-query and bit-word model. -/
public abbrev model {N : Nat} (input : Input N) : ExecutionModel :=
  .quantum AlgorithmGate.model
    (ShortDLP.declaredModel (Native.encoding input)) BitWord.model .empty

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
  (input : Input N)

/-- Allocate the original-width bank with actual zero preparation. -/
def prepare : Circuit (model input) base (Native.bankContext base noQuantum N) :=
  .prepareZero base base.canonicalFreshKey (Native.layout N) base.canonicalFreshKey_fresh
    (Native.allocationDisjoint base noQuantum N)

/-- Allocate the same finite result cells and one packed output cell. -/
def allocate : Circuit (model input) (Native.bankContext base noQuantum N)
    (Native.context base noQuantum N) :=
  .seq (MeasurementCells.allocate (model := model input)
    (Native.bankContext base noQuantum N) 2
    (measurementBits N))
    (Circuit.retain (model := model input) (Native.cellsContext base noQuantum N)
      (Native.cellsContext base noQuantum N).canonicalFreshKey
      (.bits (measurementBits N))
      (Native.cellsContext base noQuantum N).canonicalFreshKey_fresh)

/-- The current classical value selects a query from the fixed model. -/
def selected (parameter : CInputRef base (ParameterShape N)) :
    Circuit (model input) (Native.context base noQuantum N)
      (Native.context base noQuantum N) :=
  .branch (Native.liftInput base noQuantum N parameter) fun value =>
    .unitary (Native.declaredMember N
      (Native.nativeOracle_context_wires base noQuantum N) input value)

/-- One exponent wire writes to its own live finite cell. -/
def readout (index : Fin (measurementBits N)) :
    ZReadout (Native.context base noQuantum N) where
  wire := Native.wireEquiv N (Native.nativeOracle_context_wires base noQuantum N)
    ⟨index.val, by
      have bound := index.isLt
      change index.val < ShortDLP.firstBits (Native.parameters N) +
        (Native.parameters N).ell at bound
      unfold ShortDLP.totalQubits
      omega⟩
  output := by
    rw [Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N)]
    exact Native.cells base noQuantum N index

/-- Actual Z readouts follow the two original exponent-register positions. -/
def readouts : List (ZReadout (Native.context base noQuantum N)) :=
  List.ofFn (readout base noQuantum N)

/-- The original finite bits are packed by one declared classical operation. -/
def packing : ClassicalOp (.fixedVector (measurementBits N) (.finite 2))
    (.bits (measurementBits N)) (Native.context base noQuantum N)
    (Native.context base noQuantum N) :=
  .packFiniteBits (measurementBits N) (Native.context base noQuantum N)
    (.fixedVector fun index =>
      .storage (Native.cells base noQuantum N index).toCStorageRef)
    (Native.resultRef base noQuantum N)

/-- The selected quantum stage, actual measurements and paid packing. -/
def body (parameter : CInputRef base (ParameterShape N)) :
    Circuit (model input) (Native.context base noQuantum N)
      (Native.context base noQuantum N) :=
  .seq (selected base noQuantum N input parameter)
    (.seq (Circuit.measurementSequence (readouts base noQuantum N))
      (.classical (BitWord.application (packing base noQuantum N))))

/-- One prepared observation, with every actual operation in execution order. -/
def code (parameter : CInputRef base (ParameterShape N)) :
    Circuit (model input) base (Native.context base noQuantum N) :=
  .seq (prepare base noQuantum N input)
    (.seq (allocate base noQuantum N input) (body base noQuantum N input parameter))

/-- Return the packed exponent bits while retaining every live bank and cell. -/
def run (parameter : CInputRef base (ParameterShape N)) :
    AlgorithmRun (model input) base (Native.context base noQuantum N)
      (.bits (measurementBits N)) where
  code := code base noQuantum N input parameter
  output := Output.all (Native.context base noQuantum N)
    (.read (.storage (Native.resultRef base noQuantum N).toCStorageRef))

/-- The output enumerates every live storage entry. -/
theorem output_listing (parameter : CInputRef base (ParameterShape N)) :
    (run base noQuantum N input parameter).output.listing =
      (Native.context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
