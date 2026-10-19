/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Algorithm
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Store

/-!
# Standard boundary for classical algorithm endpoints

The declarations in this module fix the storage layout shared by the
classical endpoint catalog. A semantic input is borrowed at key zero and the
actual circuit retains its result at key one. Its complete Output lists both
cells and reads that result without changing either storage role. The same
interpreter supplies the output distribution and actual event trace. Each
endpoint states its problem and resource limits independently.
-/

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace QuantumAlg
namespace ClassicalEndpoints
namespace Standard

variable {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Stable storage key for the endpoint's borrowed semantic input. -/
def inputKey : StorageKey := ⟨0⟩

/-- Stable storage key for the endpoint's retained and final result. -/
public def resultKey : StorageKey := ⟨1⟩

/-- The input key is fresh for the empty classical runtime context. -/
lemma inputFresh (_inputShape : CShape) :
    inputKey ∉ (RuntimeCtx.empty : RuntimeCtx .classical).keys := by
  simp [inputKey, RuntimeCtx.keys]

/-- One borrowed-input context for a closed semantic input shape. -/
public def pre (inputShape : CShape) : RuntimeCtx .classical :=
  (RuntimeCtx.empty : RuntimeCtx .classical).addBorrowedInput
    inputKey inputShape (inputFresh inputShape)

/-- The borrowed head reference used by the standard endpoint routine. -/
def inputRef (inputShape : CShape) : CInputRef (pre inputShape) inputShape :=
  .storage
    (CStorageRef.borrowedInputHead
      (RuntimeCtx.empty : RuntimeCtx .classical)
      inputKey inputShape (inputFresh inputShape))

/-- The result key is distinct from the sole borrowed input key. -/
public lemma resultFresh (inputShape : CShape) :
    resultKey ∉ (pre inputShape).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- Complete final context: the borrowed input and the actual retained result. -/
public def post (inputShape outputShape : CShape) : RuntimeCtx .classical :=
  (pre inputShape).addRetained resultKey outputShape
    (resultFresh inputShape)

/-- Complete final context for an endpoint retaining an intermediate value and its result. -/
public def stagedPost (inputShape intermediateShape outputShape : CShape) :
    RuntimeCtx .classical :=
  let inputCtx := pre inputShape
  let intermediateKey := inputCtx.canonicalFreshKey
  let intermediateCtx := inputCtx.addRetained intermediateKey intermediateShape
    inputCtx.canonicalFreshKey_fresh
  let outputKey := intermediateCtx.canonicalFreshKey
  intermediateCtx.addRetained outputKey outputShape
    intermediateCtx.canonicalFreshKey_fresh

/-- Read the actual retained result without allocating or promoting storage. -/
def resultRef (inputShape outputShape : CShape) :
    CInputRef
      ((pre inputShape).addRetained resultKey outputShape
        (resultFresh inputShape)) outputShape :=
  .storage
    (CStorageRef.retainedHead (pre inputShape) resultKey outputShape
      (resultFresh inputShape))

/-- Seal the actual circuit with a complete manifest and its existing result readout. -/
def run {inputShape outputShape : CShape}
    (code : Circuit (.classical operations services)
      (pre inputShape) (post inputShape outputShape)) :
    AlgorithmRun (.classical operations services)
      (pre inputShape) (post inputShape outputShape) outputShape where
  code := code
  output := Output.all (post inputShape outputShape)
    (.read (resultRef inputShape outputShape))

/-- Both live cells occur in the final manifest, in the context's actual order. -/
lemma run_output_listing {inputShape outputShape : CShape}
    (code : Circuit (.classical operations services)
      (pre inputShape) (post inputShape outputShape)) :
    (run code).output.listing = [resultKey, inputKey] :=
  rfl

/-- The endpoint returns the value in its actual final retained cell. -/
lemma run_result {inputShape outputShape : CShape}
    (code : Circuit (.classical operations services)
      (pre inputShape) (post inputShape outputShape))
    (record : (run code).Record) :
    (run code).result record = record.1.read (resultRef inputShape outputShape) :=
  rfl

/-- Sealing a circuit preserves its single interpreter and its full input/reference state. -/
lemma run_execute {inputShape outputShape : CShape}
    (code : Circuit (.classical operations services)
      (pre inputShape) (post inputShape outputShape))
    (environment : (ExecutionModel.classical operations services).Environment)
    (Reference : Register)
    (state : ExecutionState (Execution.Store (pre inputShape) × services.HiddenState)
      (Register.prod (pre inputShape).register Reference)) :
    (run code).execute environment Reference state =
      code.execute
      environment Reference (state.mapClassical (fun value => (value.1, (value.2, value.1)))) :=
  rfl

/-- Output probabilities are the actual final-store readout of this execution. -/
lemma run_outputDistribution {inputShape outputShape : CShape}
    (code : Circuit (.classical operations services)
      (pre inputShape) (post inputShape outputShape))
    (environment : (ExecutionModel.classical operations services).Environment)
    {Reference : Register} (input : Execution.OracleInput services (pre inputShape) Reference) :
    (run code).outputDistribution environment input =
      ((run code).executionDistribution environment input).map
        (fun record => record.1.read (resultRef inputShape outputShape)) :=
  rfl

/-- The endpoint reports exactly the events on its actual circuit path. -/
lemma run_eventTraceDistribution {inputShape outputShape : CShape}
    (code : Circuit (.classical operations services)
      (pre inputShape) (post inputShape outputShape))
    (environment : (ExecutionModel.classical operations services).Environment)
    {Reference : Register} (input : Execution.OracleInput services (pre inputShape) Reference) :
    (run code).eventTraceDistribution environment input =
      ((run code).executionDistribution environment input).map
        (fun record => code.eventTrace record.2.2.2) :=
  rfl

/-- The certain success lower bound used by deterministic catalog endpoints. -/
def certain : ProbabilityLowerBound where
  value := 1
  le_one := le_rfl

end Standard
end ClassicalEndpoints
end QuantumAlg

end
