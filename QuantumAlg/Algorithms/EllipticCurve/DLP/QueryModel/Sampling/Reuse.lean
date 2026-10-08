/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.SuccessFloor
public import QuantumAlg.Primitives.ZReset.Bank
public import QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Sequence
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Components.QuditShift.Reset.Circuit
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Core.Execution.Store

/-!
# Actual allocation-free reuse of the intrinsic ECDLP bank

One additional retained two-valued reset cell is allocated once beside the
original exponent result cells. Every round resets the complete owned bank,
executes the original initialized query word, measures the exponents and
resets the same bank again. The final reset writes only its dedicated cell;
the actual exponent results remain available to checked classical recovery.
Neither reset prepares, releases or replaces a quantum system.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

namespace Sampling.Reuse

noncomputable section

open QuantumAlg.Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original full bank and measured cells coexist with one retained reset bit. -/
@[expose] public def context (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  (Sampling.post I).addRetained (Sampling.post I).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I))

/-- The reset instruction writes only this additional, independently fresh cell. -/
public def scratch (I : ECDLPInstance E) : CWriteRef (context I) (.finite 2) :=
  CWriteRef.retainedHead (Sampling.post I) (Sampling.post I).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I))

/-- Each exponent result remains in its original real cell beneath the reset cell. -/
public def cell (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    CWriteRef (context I) (.finite 2) :=
  (Sampling.cell I index).underRetained (Sampling.post I).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I))

/-- Read the same original measured exponent cells after both physical resets. -/
public def sampleInput (I : ECDLPInstance E) :
    CInputRef (context I) (.fixedVector (sampleWidth I) (.finite 2)) :=
  .fixedVector fun index => .storage (cell I index).toCStorageRef

/-- Each original exponent position has the actual reused context's system index type. -/
public def exponentPosition (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    Fin (context I).systemCount := Sampling.exponentPosition I index

/-- The same original exponent wire is a qubit in this actual reused context. -/
public theorem exponent_dimension (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    ((context I).quantumLayout.wire (exponentPosition I index)).dimension = 2 :=
  Sampling.exponent_dimension I index

/-- The single retained reset cell changes no physical identity, dimension or wire order. -/
public theorem ecdlpReuse_sourceWires (I : ECDLPInstance E) :
    (layout I).wires = (context I).quantumLayout.wires :=
  Sampling.sourceWires I

/-- Every system in the unchanged complete bank is an actual qubit. -/
public theorem ecdlpReuse_qubits (I : ECDLPInstance E)
    (wire : Fin (context I).systemCount) :
    ((context I).quantumLayout.wire wire).dimension = 2 := by
  let positions := Execution.positionsOfEqualWires (layout I) (context I).quantumLayout
    (ecdlpReuse_sourceWires I)
  have same := Execution.wireAtCorrespondingPosition (layout I) (context I).quantumLayout
    (ecdlpReuse_sourceWires I) (positions.symm wire)
  change ((context I).quantumLayout.wire (positions (positions.symm wire))) = _ at same
  rw [Equiv.apply_symm_apply] at same
  rw [same]
  rfl

/-- Both actual bank resets use Z readout and its selected native X correction. -/
public def reset (I : ECDLPInstance E) (A : Access I) :
    Circuit (executionModel I A) (context I) (context I) :=
  ZReset.Bank.code (oracles := model I A) (ecdlpReuse_qubits I) (scratch I) BitWord.model

/-- Execute the same native infinity-tag X and the original declared sampling word. -/
public def nativeProgram (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    UnitaryCircuit AlgorithmGate.model (model I A) (context I).quantumLayout :=
  Execution.unitaryOfEqualWires (layout I) (context I).quantumLayout (ecdlpReuse_sourceWires I)
    ((initializer I A).seq (circuit I A expansion))

/-- Measure each original exponent position into its existing retained result cell. -/
public def readout (I : ECDLPInstance E) (index : Fin (sampleWidth I)) :
    ZReadout (context I) :=
  QubitReadouts.readout (exponentPosition I index)
    (exponent_dimension I index) (cell I index)

/-- The original ordered exponent readouts remain distinct from the reset destination. -/
public def readouts (I : ECDLPInstance E) : List (ZReadout (context I)) :=
  List.ofFn (readout I)

/-- A round includes its leading reset, actual sample and required final physical reset. -/
public def code (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Circuit (executionModel I A) (context I) (context I) :=
  (reset I A).seq ((Circuit.unitary (nativeProgram I A expansion)).seq
    ((Circuit.measurementSequence (readouts I)).seq (reset I A)))

private theorem resetSequence_local {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
    (implementations : ∀ wire,
      QuditShift.Realizations AlgorithmGate.model oracles ctx.quantumLayout wire)
    (items : List (ZReadout ctx)) :
    (ZReset.sequence implementations items BitWord.model).IsLocal := by
  induction items with
  | nil => trivial
  | cons head tail induction =>
      exact ⟨⟨trivial, fun _ => trivial⟩, induction⟩

private theorem readoutSequence_local {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
    (items : List (ZReadout ctx)) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      items).IsLocal := by
  induction items with
  | nil => trivial
  | cons head tail induction => exact ⟨trivial, induction⟩

/-- Every actual round reuses the same live bank and allocates no additional entry. -/
public theorem ecdlpReuse_code_isLocal (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (code I A expansion).IsLocal := by
  have resetLocal : (reset I A).IsLocal := resetSequence_local _ _
  exact ⟨resetLocal, ⟨trivial, ⟨readoutSequence_local _, resetLocal⟩⟩⟩

/-- Allocate the original bank, original measured cells and exactly one reset cell once. -/
public def initialCode (I : ECDLPInstance E) (A : Access I) :
    Circuit (executionModel I A) (Sampling.pre I) (context I) :=
  (Sampling.initialCode I A).seq (Circuit.retain (model := executionModel I A) (Sampling.post I)
    (Sampling.post I).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I)))

/-- The complete returned manifest retains every input, point/exponent system and real cell. -/
public def run (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    AlgorithmRun (executionModel I A) (context I) (context I)
      (.fixedVector (sampleWidth I) (.finite 2)) where
  code := code I A expansion
  output := Output.all (context I) (.read (sampleInput I))

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
