/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Placement
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# One actual original-width oracle sample

One real zero-state preparation precedes the original parameter-selected
oracle member. Actual Z instructions record the exponent outcomes, and one
real packing instruction writes their bit string. Every final live cell and
the quantum bank remain in the complete output. This constructor runs once;
it does not provide a free reset for later samples.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Allocate the one original-width bank in its actual zero initial state. -/
def prepare : Circuit base (bankContext base noQuantum N) :=
  .prepare base base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N) (preparation N)

/-- Every measurement cell and the packed result are initialized by real retention. -/
def allocate : Circuit (bankContext base noQuantum N) (context base noQuantum N) :=
  .seq (MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N))
    (.retain (cellsContext base noQuantum N) (cellsContext base noQuantum N).canonicalFreshKey
      (.bits (measurementBits N)) (cellsContext base noQuantum N).canonicalFreshKey_fresh)

/-- Read the original parameter before choosing its actual XOR member. -/
def selected (input : Input N) (parameter : CInputRef base (ParameterShape N)) :
    Circuit (context base noQuantum N) (context base noQuantum N) :=
  .branch (liftInput base noQuantum N parameter) fun value =>
    .unitary (member N (nativeOracle_context_wires base noQuantum N) input value)
      (nativeOracle_member_physicalIdx N (nativeOracle_context_wires base noQuantum N) input value)

/-- Each source exponent position is measured into its actual finite cell. -/
def readout (index : Fin (measurementBits N)) : ZReadout (context base noQuantum N) where
  wire := wireEquiv N (nativeOracle_context_wires base noQuantum N)
    ⟨index.val, by
      have bound := index.isLt
      change index.val < ShortDLP.firstBits (parameters N) + (parameters N).ell at bound
      unfold ShortDLP.totalQubits
      omega⟩
  output := by
    rw [nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)]
    exact cells base noQuantum N index

/-- The exponent-register order is preserved by the actual sequence. -/
def readouts : List (ZReadout (context base noQuantum N)) := List.ofFn (readout base noQuantum N)

/-- One charged instruction packs only the observed finite cells. -/
def packing : ClassicalOp (.fixedVector (measurementBits N) (.finite 2))
    (.bits (measurementBits N)) (context base noQuantum N) (context base noQuantum N) :=
  .packFiniteBits (measurementBits N) (context base noQuantum N)
    (.fixedVector fun index => .storage (cells base noQuantum N index).toCStorageRef)
    (resultRef base noQuantum N)

/-- Actual original oracle execution followed by measurement and paid result packing. -/
def body (input : Input N) (parameter : CInputRef base (ParameterShape N)) :
    Circuit (context base noQuantum N) (context base noQuantum N) :=
  .seq (selected base noQuantum N input parameter)
    (.seq (Circuit.measurementSequence (readouts base noQuantum N))
      (.classical (packing base noQuantum N)))

/-- One actual prepared sample, preserving the same complete instruction order. -/
def code (input : Input N) (parameter : CInputRef base (ParameterShape N)) :
    Circuit base (context base noQuantum N) :=
  .seq (prepare base noQuantum N)
    (.seq (allocate base noQuantum N) (body base noQuantum N input parameter))

/-- Observe the actual packed bits while listing every surviving classical and quantum entry. -/
def run (input : Input N) (parameter : CInputRef base (ParameterShape N)) :
    AlgorithmRun base (context base noQuantum N) (.bits (measurementBits N)) where
  code := code base noQuantum N input parameter
  output := Output.all (context base noQuantum N)
    (.read (.storage (resultRef base noQuantum N).toCStorageRef))

/-- No live bank or result storage is hidden from the single-sample output. -/
theorem nativeOracle_output_listing (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) :
    (run base noQuantum N input parameter).output.listing = (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
