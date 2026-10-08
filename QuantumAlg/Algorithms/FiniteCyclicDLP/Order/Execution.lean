/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Circuit
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Components.Classical.Oracle.FiniteGroup
public import QuantumAlg.Core.Execution.Context.Layout.Unitary
public import QuantumAlg.Core.Execution.Measurement.Sequence
public import QuantumAlg.Core.Execution.Measurement.Cells
public import QuantumAlg.Core.Execution.QubitReadouts
public import QuantumAlg.Core.Execution.Output
public import QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# One complete finite-cyclic DLP sampling cycle

The execution owns two exponent registers and one native-dimensional group
system in one physical bank.  It prepares that whole bank at basis zero, runs
the actual preparation-query-inverse-QFT word, then measures exactly the two
exponent registers into retained finite cells.  The group workspace remains
live and is neither encoded as bits nor silently discarded.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExecution

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Quantum gates, the sole `U_x`, default word operations and abstract group multiplication. -/
public abbrev model (P : KnownOrderProblem G) : ExecutionModel :=
  .quantum AlgorithmGate.model (OrderOracle.model P) BitWord.model
    (ClassicalFiniteGroupOracle.model G)

/-- One raw sample contains both ordered exponent-register bit strings. -/
@[expose, implicit_reducible] public def sampleWidth (P : KnownOrderProblem G) : Nat :=
  OrderPreparation.width P + OrderPreparation.width P

/-- Executable preparation data computed from the known positive order. -/
public def canonicalExpansion (P : KnownOrderProblem G) : OrderExpansion P.order :=
  OrderExpansion.canonical P.order (Nat.pos_of_ne_zero P.order_ne_zero)

/-- The sampler has no caller-owned quantum or classical input. -/
@[expose, reducible] public def pre : RuntimeCtx .quantum := RuntimeCtx.empty

/-- The canonical bank key is fresh in the empty input context. -/
public theorem bankFresh : (pre : RuntimeCtx .quantum).canonicalFreshKey ∉ pre.keys := by
  exact RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh pre

/-- The fresh bank shares no physical system with the empty input context. -/
public theorem bankDisjoint (P : KnownOrderProblem G) :
    List.Disjoint (OrderOracle.layout P).identities pre.physicalIdx := by
  rw [pre, RuntimeCtx.runtimeCtx_empty_physicalIdx]
  exact List.disjoint_nil_right _

/-- The empty input contributes no resident storage to the owned bank. -/
public theorem pre_residentSpace : (pre : RuntimeCtx .quantum).residentSpace = 0 := by
  rfl

/-- The complete native-dimensional bank allocated and initialized by this cycle. -/
@[expose] public def bankContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  pre.addOwnedLayout pre.canonicalFreshKey (OrderOracle.layout P)
    bankFresh (bankDisjoint P)

/-- Retained measurement cells coexist with every physical system of the bank. -/
@[expose] public def post (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext P) 2 (sampleWidth P)

/-- One distinct result cell for each exponent-register position. -/
public def cell (P : KnownOrderProblem G) (index : Fin (sampleWidth P)) :
    CWriteRef (post P) (.finite 2) :=
  MeasurementCells.reference (bankContext P) 2 (sampleWidth P) index

/-- The ordered raw sample is a structural read of the actual retained cells. -/
public def sampleInput (P : KnownOrderProblem G) :
    CInputRef (post P) (.fixedVector (sampleWidth P) (.finite 2)) :=
  MeasurementCells.input (bankContext P) 2 (sampleWidth P)

/-- Adding the bank to the empty context preserves its exact ordered wire list. -/
theorem bankContext_wires (P : KnownOrderProblem G) :
    (bankContext P).quantumWires = (OrderOracle.layout P).wires := by
  change (OrderOracle.layout P).wires ++ ([] : List QuantumWire) = _
  rw [List.append_nil]

/-- Retaining finite cells adds no quantum system and changes no physical dimension. -/
theorem post_wires (P : KnownOrderProblem G) :
    (post P).quantumWires = (OrderOracle.layout P).wires := by
  rw [post, MeasurementCells.context_quantumWires, bankContext_wires]

/-- The source layout and terminal runtime have the same ordered physical wires. -/
public theorem sourceWires (P : KnownOrderProblem G) :
    (OrderOracle.layout P).wires = (post P).quantumLayout.wires :=
  (RuntimeCtx.quantumLayout_wires (post P)).trans (post_wires P) |>.symm

/-- Source circuit positions correspond to the unchanged live physical positions. -/
public def wireEquiv (P : KnownOrderProblem G) :
    Fin (OrderPreparation.width P + OrderPreparation.width P + 1) ≃
      Fin (post P).systemCount :=
  Execution.positionsOfEqualWires (OrderOracle.layout P) (post P).quantumLayout
    (sourceWires P)

/-- Runtime labels and source-circuit labels name the same finite value on
every corresponding physical system. -/
public def basisEquiv (P : KnownOrderProblem G) :
    (post P).register.Index ≃ (OrderOracle.layout P).Basis :=
  (Execution.basisOfEqualWires (OrderOracle.layout P) (post P).quantumLayout
    (sourceWires P)).symm

/-- The inverse correspondence is the transport used by the native circuit. -/
public theorem basisEquiv_symm (P : KnownOrderProblem G) :
    (basisEquiv P).symm =
      Execution.basisOfEqualWires (OrderOracle.layout P) (post P).quantumLayout
        (sourceWires P) := by
  rfl

/-- The basis correspondence changes only dependent types, never the value at
an actual physical position. -/
public theorem basisEquiv_wire_value (P : KnownOrderProblem G)
    (basis : (post P).register.Index)
    (index : Fin (OrderPreparation.width P + OrderPreparation.width P + 1)) :
    (basis (wireEquiv P index)).val = (basisEquiv P basis index).val := by
  let correspondence := Execution.basisOfEqualWires
    (OrderOracle.layout P) (post P).quantumLayout (sourceWires P)
  have value := Execution.basisOfEqualWires_value
    (OrderOracle.layout P) (post P).quantumLayout (sourceWires P)
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis) (wireEquiv P index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  exact value

/-- The runtime wirewise zero label is the source circuit's wirewise zero
label under the exact physical correspondence. -/
@[simp] public theorem basisEquiv_zero (P : KnownOrderProblem G) :
    basisEquiv P (post P).quantumLayout.zeroLabel =
      (OrderOracle.layout P).zeroLabel := by
  funext index
  apply Fin.ext
  simpa only [QuantumLayout.zeroLabel, Fin.val_zero] using
    (basisEquiv_wire_value P (post P).quantumLayout.zeroLabel index).symm

/-- Every measured source position is one of the two actual exponent qubits. -/
public theorem exponent_dimension (P : KnownOrderProblem G) (index : Fin (sampleWidth P)) :
    ((post P).quantumLayout.wire
      (wireEquiv P ⟨index.val, by
        have bound := index.isLt
        unfold sampleWidth at bound
        omega⟩)).dimension = 2 := by
  unfold wireEquiv
  rw [Execution.wireAtCorrespondingPosition
    (OrderOracle.layout P) (post P).quantumLayout (sourceWires P)]
  let exponentIndex : Fin
      (OrderPreparation.width P + OrderPreparation.width P) :=
    ⟨index.val, by
      have bound := index.isLt
      unfold sampleWidth at bound
      exact bound⟩
  have position :
      (⟨index.val, by
          have bound := index.isLt
          unfold sampleWidth at bound
          omega⟩ : Fin
            (OrderPreparation.width P + OrderPreparation.width P + 1)) =
        Fin.castAdd 1 exponentIndex := by
    apply Fin.ext
    rfl
  rw [position]
  simp only [OrderOracle.layout, QuantumLayout.append, Fin.append_left]
  rfl

/-- One real Z readout writes the finite value of its corresponding exponent qubit. -/
@[expose] public def readout (P : KnownOrderProblem G) (index : Fin (sampleWidth P)) :
    ZReadout (post P) :=
  Execution.QubitReadouts.readout (wireEquiv P ⟨index.val, by
    have bound := index.isLt
    unfold sampleWidth at bound
    omega⟩) (exponent_dimension P index) (cell P index)

@[simp] public theorem readout_output_key (P : KnownOrderProblem G)
    (index : Fin (sampleWidth P)) :
    (readout P index).output.key = (cell P index).key :=
  Execution.QubitReadouts.readout_key _ (exponent_dimension P index) (cell P index)

/-- Both exponent registers are measured in their original physical order. -/
@[expose] public def readouts (P : KnownOrderProblem G) : List (ZReadout (post P)) :=
  List.ofFn (readout P)

/-- Fixed zero preparation initializes exponents at zero and the anchored group basis at `1_G`. -/
@[expose] public def preparationCode (P : KnownOrderProblem G) :
    Circuit (model P) pre (bankContext P) :=
  .prepareZero pre pre.canonicalFreshKey (OrderOracle.layout P)
    bankFresh (bankDisjoint P)

/-- Allocate exactly the cells written by the terminal measurement sequence. -/
@[expose] public def allocationCode (P : KnownOrderProblem G) :
    Circuit (model P) (bankContext P) (post P) :=
  MeasurementCells.allocate (model := model P) (bankContext P) 2 (sampleWidth P)

/-- The same source circuit transported to the unchanged live bank wires. -/
public def nativeProgram (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    UnitaryCircuit AlgorithmGate.model (OrderOracle.model P) (post P).quantumLayout :=
  Execution.unitaryOfEqualWires (OrderOracle.layout P) (post P).quantumLayout
    (sourceWires P) (OrderCircuit.circuit P expansion)

/-- Equal-wire transport preserves the native dependency expression verbatim. -/
public theorem nativeProgram_eventDepth
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    (nativeProgram P expansion).eventDepth BitWord.model
        (ClassicalFiniteGroupOracle.model G) =
      (OrderCircuit.circuit P expansion).eventDepth BitWord.model
        (ClassicalFiniteGroupOracle.model G) := by
  exact Execution.unitaryOfEqualWires_depth
    (OrderOracle.layout P) (post P).quantumLayout (sourceWires P)
      (OrderCircuit.circuit P expansion) BitWord.model
        (ClassicalFiniteGroupOracle.model G)

/-- Preparation, cell allocation and the source unitary form the coherent
prefix immediately before the terminal reads. -/
@[expose] public def beforeMeasurement (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    Circuit (model P) pre (post P) :=
  .seq (preparationCode P)
    (.seq (allocationCode P)
      (.unitary (nativeProgram P expansion)))

/-- The terminal readout is the actual ordered Z-measurement sequence. -/
@[expose] public def readoutCode (P : KnownOrderProblem G) :
    Circuit (model P) (post P) (post P) :=
  .measurementSequence (readouts P)

/-- Preparation, allocation, actual unitary and every terminal measurement form one cycle. -/
@[expose] public def code (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    Circuit (model P) pre (post P) :=
  .seq (beforeMeasurement P expansion) (readoutCode P)

/-- Complete cycle with no caller-supplied expansion certificate. -/
@[expose] public def canonicalCode (P : KnownOrderProblem G) :
    Circuit (model P) pre (post P) :=
  code P (canonicalExpansion P)

/-- Complete output retains the group workspace, exponent registers and every raw sample cell. -/
public def run (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    AlgorithmRun (model P) pre (post P) (.fixedVector (sampleWidth P) (.finite 2)) where
  code := code P expansion
  output := Output.all (post P) (.read (sampleInput P))

/-- Canonical all-positive-order sampler. -/
public def canonicalRun (P : KnownOrderProblem G) :
    AlgorithmRun (model P) pre (post P) (.fixedVector (sampleWidth P) (.finite 2)) :=
  run P (canonicalExpansion P)

private theorem run_result_internal (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (record : (run P expansion).Record) :
    (run P expansion).result record = record.1.read (sampleInput P) := rfl

public theorem run_result (P : KnownOrderProblem G) (expansion : OrderExpansion P.order)
    (record : (run P expansion).Record) :
    (run P expansion).result record = record.1.read (sampleInput P) :=
  run_result_internal P expansion record

private theorem run_output_listing_internal (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (run P expansion).output.listing = (post P).keys := rfl

public theorem run_output_listing (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (run P expansion).output.listing = (post P).keys :=
  run_output_listing_internal P expansion

end

end QuantumAlg.FiniteCyclicDLP.OrderExecution
