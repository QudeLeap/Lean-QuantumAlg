/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Initialization
public import QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Input
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Core.Execution.Context.Layout.Unitary
public import QuantumAlg.Core.Execution.Measurement.Cells
public import QuantumAlg.Core.Execution.QubitReadouts
public import QuantumAlg.Core.Execution.Output
public import QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Input
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Executed intrinsic ECDLP sampling and retained readout

The original borrowed base and target points remain in the input store. The
sampler allocates the full qubit bank at zero, sets its infinity tag by the
actual native X, executes the declared word, then measures exactly the two
exponent registers into distinct retained cells. The point bank remains live.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Native peripherals, the one granted query and default classical bit operations. -/
@[expose, reducible] public def executionModel
    (I : ECDLPInstance E) : ExecutionModel :=
  .quantum AlgorithmGate.model (model I) BitWord.model .empty

/-- A granted operator supplies semantics to the fixed sampling program. -/
@[expose] public def sourceEnvironment (I : ECDLPInstance E) (A : Access I) :
    (executionModel I).Environment where
  quantum := interpretation I A
  classical := ClassicalOracleModel.emptyInterpretation

/-- Preserve the original two borrowed classical point inputs. -/
public abbrev pre (I : ECDLPInstance E) : RuntimeCtx .quantum := Runtime.Context.pre I

/-- The input contains classical points and has no quantum bank yet. -/
private lemma originalInput_noQuantum (I : ECDLPInstance E) :
    (pre I).quantumWires = [] := rfl

/-- The original borrowed classical inputs require no supplied quantum systems. -/
public lemma pre_noQuantum (I : ECDLPInstance E) : (pre I).quantumWires = [] :=
  originalInput_noQuantum I

/-- Exactly the two original exponent widths are measured. -/
@[expose, implicit_reducible] public def sampleWidth (I : ECDLPInstance E) : Nat :=
  FiniteCyclicDLP.orderWidth (problem I) + FiniteCyclicDLP.orderWidth (problem I)

/-- The full fresh point-and-exponent bank has no overlap with the input context. -/
public lemma bankDisjoint (I : ECDLPInstance E) :
    List.Disjoint (layout I).identities (pre I).physicalIdx := by
  change List.Disjoint (layout I).identities ((pre I).quantumWires.map QuantumWire.identity)
  rw [pre_noQuantum]
  exact List.disjoint_nil_right _

/-- The same real qubit bank is owned by this sampling execution. -/
@[expose] public def bankContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  (pre I).addOwnedLayout (pre I).canonicalFreshKey (layout I)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (pre I)) (bankDisjoint I)

/-- Every measurement cell coexists with all exponent and point qubits. -/
@[expose] public def post (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext I) 2 (sampleWidth I)

/-- The source and allocated bank retain the same ordered physical wire records. -/
public lemma bankContext_wires (I : ECDLPInstance E) :
    (bankContext I).quantumWires = (layout I).wires := by
  change (layout I).wires ++ (pre I).quantumWires = _
  rw [pre_noQuantum, List.append_nil]

/-- Allocation of classical result cells preserves every live physical wire. -/
public lemma sourceWires (I : ECDLPInstance E) :
    (layout I).wires = (post I).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, post, MeasurementCells.context_quantumWires,
    bankContext_wires]

/-- Corresponding runtime positions name the source's exact ordered systems. -/
public def wireEquiv (I : ECDLPInstance E) :
    Fin (Layout.totalQubits I) ≃ Fin (post I).systemCount :=
  Execution.positionsOfEqualWires (layout I) (post I).quantumLayout (sourceWires I)

/-- Runtime basis labels correspond to the exact original source basis. -/
public def basisEquiv (I : ECDLPInstance E) : (post I).register.Index ≃ (layout I).Basis :=
  (Execution.basisOfEqualWires (layout I) (post I).quantumLayout (sourceWires I)).symm

/-- One actual writable cell for each measured exponent qubit. -/
public def cell (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    CWriteRef (post I) (.finite 2) :=
  MeasurementCells.reference (bankContext I) 2 (sampleWidth I) index

/-- The output is a structural read of the actual retained measurement cells. -/
public def sampleInput (I : ECDLPInstance E) :
    CInputRef (post I) (.fixedVector (sampleWidth I) (.finite 2)) :=
  MeasurementCells.input (bankContext I) 2 (sampleWidth I)

/-- Select each exponent position in the unchanged complete physical bank. -/
public def exponentPosition (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    Fin (post I).systemCount :=
  wireEquiv I (Fin.castAdd (Layout.pointWidth E) index)

/-- Each selected exponent system is an actual qubit. -/
public lemma exponent_dimension (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    ((post I).quantumLayout.wire (exponentPosition I index)).dimension = 2 := by
  unfold exponentPosition wireEquiv
  rw [Execution.wireAtCorrespondingPosition (layout I) (post I).quantumLayout (sourceWires I)]
  rfl

/-- Read a named exponent qubit into its own retained finite cell. -/
@[expose] public def readout (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    ZReadout (post I) :=
  QubitReadouts.readout (exponentPosition I index) (exponent_dimension I index) (cell I index)

/-- Both exponent registers are read in their original physical order. -/
@[expose] public def readouts (I : ECDLPInstance E) : List (ZReadout (post I)) :=
  List.ofFn (readout I)

/-- The only allocation preparation initializes every fresh system to zero. -/
@[expose] public def preparationCode (I : ECDLPInstance E) :
    Circuit (executionModel I) (pre I) (bankContext I) :=
  .prepareZero (pre I) (pre I).canonicalFreshKey (layout I)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (pre I)) (bankDisjoint I)

/-- Allocate precisely the retained finite measurement cells. -/
@[expose] public def allocationCode (I : ECDLPInstance E) :
    Circuit (executionModel I) (bankContext I) (post I) :=
  MeasurementCells.allocate (model := executionModel I) (bankContext I) 2 (sampleWidth I)

/-- The native infinity-tag initialization precedes the original sampling word. -/
public def nativeProgram (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    UnitaryCircuit AlgorithmGate.model (model I) (post I).quantumLayout :=
  Execution.unitaryOfEqualWires (layout I) (post I).quantumLayout (sourceWires I)
    ((initializer I).seq (circuit I expansion))

/-- Allocate the bank at zero and retain every actual result cell. -/
@[expose] public def initialCode (I : ECDLPInstance E) :
    Circuit (executionModel I) (pre I) (post I) :=
  .seq (preparationCode I) (allocationCode I)

/-- The actual coherent prefix allocates zero, retains cells and executes the native word. -/
@[expose] public def beforeMeasurement (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Circuit (executionModel I) (pre I) (post I) :=
  .seq (initialCode I) (.unitary (nativeProgram I expansion))

/-- Every terminal Z read is an actual interpreter instruction. -/
@[expose] public def readoutCode (I : ECDLPInstance E) :
    Circuit (executionModel I) (post I) (post I) :=
  .measurementSequence (readouts I)

/-- The complete allocation, initialization, query and retained-measurement sample. -/
@[expose] public def code (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Circuit (executionModel I) (pre I) (post I) :=
  .seq (beforeMeasurement I expansion) (readoutCode I)

/-- Readout exposes its real cells and retains the entire borrowed-input and quantum bank. -/
public def run (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    AlgorithmRun (executionModel I) (pre I) (post I)
      (.fixedVector (sampleWidth I) (.finite 2)) where
  code := code I expansion
  output := Output.all (post I) (.read (sampleInput I))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
