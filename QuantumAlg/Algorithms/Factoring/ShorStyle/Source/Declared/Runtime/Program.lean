/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Placement
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Storage
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# One runtime Shor query and actual retained phase measurement

The stored complete sampler parameter selects one member of the fixed model.
The existing owned bank executes the chosen native word, each
phase wire writes a finite cell and one paid packing operation stores the bits.
All prior classical storage, every bank wire and every result cell remain live.
The sampler prefix and joint-law proof are separate owners of the same code.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (N : Nat)
  (sameWires : base.quantumWires = (layout N).wires)

/-- Retain the actual phase result and all finite cells without allocating another bank. -/
def allocate : Circuit (executionModel N) base (Storage.context base N) :=
  .seq (.retain (model := executionModel N) base base.canonicalFreshKey
      (.bits (phaseBits N)) base.canonicalFreshKey_fresh)
    (MeasurementCells.allocate (model := executionModel N) (Storage.resultContext base N)
      2 (phaseBits N))

/-- The actual computed and stored base selects a granted member from the fixed model. -/
def selected (parameter : CInputRef base (ParameterShape (modulusBits N))) :
    Circuit (executionModel N) (Storage.context base N)
      (Storage.context base N) :=
  .branch (Storage.liftInput base N parameter) fun value =>
    .unitary (member N
      ((Storage.quantumWires base N).trans sameWires) value)

/-- One exponent wire writes to its own live finite cell. -/
def readout (index : Fin (phaseBits N)) :
    ZReadout (Storage.context base N) where
  wire := wireEquiv N ((Storage.quantumWires base N).trans sameWires)
    ⟨index.val, by
      have bound := index.isLt
      change index.val < phaseBits N at bound
      unfold bankQubits
      omega⟩
  output := by
    rw [shorDeclared_context_qubits N
      ((Storage.quantumWires base N).trans sameWires)]
    exact Storage.cells base N index

/-- Actual Z readouts follow the original phase-register positions. -/
def readouts : List (ZReadout (Storage.context base N)) :=
  List.ofFn (readout base N sameWires)

/-- The original finite bits are packed by one declared classical operation. -/
def packing : ClassicalOp (.fixedVector (phaseBits N) (.finite 2))
    (.bits (phaseBits N)) (Storage.context base N)
    (Storage.context base N) :=
  .packFiniteBits (phaseBits N) (Storage.context base N)
    (.fixedVector fun index =>
      .storage (Storage.cells base N index).toCStorageRef)
    (Storage.resultRef base N)

/-- The selected quantum stage, actual measurements and paid packing. -/
def body (parameter : CInputRef base (ParameterShape (modulusBits N))) :
    Circuit (executionModel N) (Storage.context base N)
      (Storage.context base N) :=
  .seq (selected base N sameWires parameter)
    (.seq (Circuit.measurementSequence (readouts base N sameWires))
      (.classical (BitWord.application (packing base N))))

/-- One actual selected observation on the existing prepared bank. -/
def code (parameter : CInputRef base (ParameterShape (modulusBits N))) :
    Circuit (executionModel N) base (Storage.context base N) :=
  .seq (allocate base N) (body base N sameWires parameter)

/-- Return the packed exponent bits while retaining every live bank and cell. -/
def run (parameter : CInputRef base (ParameterShape (modulusBits N))) :
    AlgorithmRun (executionModel N) base (Storage.context base N)
      (.bits (phaseBits N)) where
  code := code base N sameWires parameter
  output := Output.all (Storage.context base N)
    (.read (.storage (Storage.resultRef base N).toCStorageRef))

/-- The output enumerates every live storage entry. -/
lemma output_listing (parameter : CInputRef base (ParameterShape (modulusBits N))) :
    (run base N sameWires parameter).output.listing =
      (Storage.context base N).keys := rfl


end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
