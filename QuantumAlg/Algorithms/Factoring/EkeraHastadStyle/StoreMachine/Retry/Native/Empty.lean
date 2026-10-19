/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# An actual empty result when no recovery batch is requested

The zero-batch case allocates one real optional-factor cell. Its canonical
initial value supplies the empty result without a sampler or recovery call.
The complete execution keeps every caller store value and quantum-reference
block. Allocation emits no native event but its retained classical capacity
is included in both actual space peaks.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryEmpty

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (N : Nat)

/-- The zero-batch output occupies one fresh retained optional-factor cell. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum :=
  base.addRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    base.canonicalFreshKey_fresh

/-- The empty output is read from the actual allocated cell. -/
def resultRef : CWriteRef (context base N) (LatticeBatchRecoveryOutput.OutputShape N) :=
  .retainedHead base base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    base.canonicalFreshKey_fresh

/-- No batch runs; the sole instruction really allocates the output cell. -/
def code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model) base (context base N) :=
  .retain (model := .quantum AlgorithmGate.model .empty BitWord.model)
    base base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    base.canonicalFreshKey_fresh

/-- Every original resource and the actual empty result occur in the complete output. -/
def run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
    base (context base N) (LatticeBatchRecoveryOutput.OutputShape N) where
  code := code base N
  output := Output.all (context base N) (.read (.storage (resultRef base N).toCStorageRef))

/-- The output manifest lists every actual live entry. -/
lemma output_listing : (run base N).output.listing = (context base N).keys := rfl

/-- Actual allocation supplies the empty optional value for every original caller store. -/
lemma run_output (store : Store base) :
    (run base N).output.eval
        (store.pushRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
          base.canonicalFreshKey_fresh) = .optionNone :=
  Store.read_pushRetained_head store base.canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh

/-- The full execution extends the actual store while keeping all input and reference blocks. -/
lemma code_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (code base N).execute environment Reference state = state.mapClassical (fun entry =>
      (entry.1.pushRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
        base.canonicalFreshKey_fresh, (entry.2.1, (entry.2.2, ())))) :=
  Circuit.execute_retain (environment := environment)
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    state base.canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh

/-- Each structural caller read keeps its exact original value after the actual allocation. -/
lemma callerFrame (store : Store base) {shape : CShape} (input : CInputRef base shape) :
    (store.pushRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
        base.canonicalFreshKey_fresh).read
      (input.underRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
        base.canonicalFreshKey_fresh) = store.read input :=
  Store.read_pushRetained_underRetained store base.canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh input

/-- The actual run records its real allocation and the unchanged initial caller store. -/
lemma run_execute {Reference : Register}
    (state : ExecutionState (Store base × ClassicalOracleModel.empty.HiddenState)
      (base.register.prod Reference)) :
    (run base N).execute environment Reference state = state.mapClassical (fun entry =>
      (entry.1.pushRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
        base.canonicalFreshKey_fresh, (entry.2, (entry.1, ())))) := by
  simp only [AlgorithmRun.execute, run, code_execute,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1

/-- The actual trace-derived output distribution is certainly the empty optional value. -/
lemma run_outputDistribution {Reference : Register}
    (input : Execution.OracleInput .empty base Reference) :
    (run base N).outputDistribution environment input = PMF.pure .optionNone := by
  let record : Store base × ClassicalOracleModel.empty.HiddenState → (run base N).Record :=
    fun entry => (entry.1.pushRetained base.canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N)
      base.canonicalFreshKey_fresh, (entry.2, (entry.1, ())))
  have records : (run base N).executionDistribution environment input =
      (input.state.toPMF input.normalized).map record := by
    have actual : (run base N).executionDistribution environment input =
        (input.state.mapClassical record).toPMF
          (input.state.mapClassical_normalized input.normalized record) := by
      apply PMF.ext
      intro entry
      refine congrArg
        (fun state : ExecutionState (run base N).Record
            ((context base N).register.prod Reference) =>
          ENNReal.ofReal (state.block entry).mass)
        ((run_execute (environment := environment) base N input.state).trans ?_)
      congr 1
      exact Subsingleton.elim _ _
    exact actual.trans (ExecutionState.toPMF_mapClassical input.state input.normalized record)
  rw [AlgorithmRun.outputDistribution, records, PMF.map_comp]
  have readRecord : (run base N).result ∘ record =
      Function.const (Store base × ClassicalOracleModel.empty.HiddenState) .optionNone :=
    funext fun entry => run_output base N entry.1
  rw [readRecord, PMF.map_const]

/-- The independent additional capacity is the binary encoding of one optional factor. -/
def additionalSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.bits (modulusBits N + 1))

/-- The actual result cell has exactly the independent classical-bit allowance. -/
lemma resultSpace :
    SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) = additionalSpace N := by
  ext axis
  cases axis <;> simp [additionalSpace, LatticeBatchRecoveryOutput.OutputShape, SpacePool.ofShape]
  omega

/-- The sole allocation emits no native operations. -/
lemma code_eventTrace (path : (code base N).Path) :
    (code base N).eventTrace path = [] := rfl

/-- The actual zero-batch path has zero event multiplicity. -/
lemma code_pool (path : (code base N).Path) :
    (code base N).resourcePool path = 0 := rfl

/-- The actual zero-batch path has no event dependency. -/
lemma code_depth
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model) → Nat)
    (path : (code base N).Path) :
    (code base N).depth duration path = 0 := rfl

/-- The actual resident peak includes the newly retained output and the entire caller context. -/
lemma code_resident (path : (code base N).Path) :
    (code base N).peakResidentSpace path = base.residentSpace + additionalSpace N := by
  have actual : (code base N).peakResidentSpace path = (context base N).residentSpace := by
    funext axis
    change max (base.residentSpace axis) (max ((context base N).residentSpace axis) 0) = _
    rw [Nat.max_zero]
    apply max_eq_right
    cases axis <;> simp [context]
  rw [actual, context, RuntimeCtx.residentSpace_addRetained, resultSpace, add_comm]

/-- The same actual path includes the retained output in its auxiliary peak. -/
lemma code_auxiliary (path : (code base N).Path) :
    (code base N).peakAuxiliarySpace path = base.auxiliarySpace + additionalSpace N := by
  have actual : (code base N).peakAuxiliarySpace path = (context base N).auxiliarySpace := by
    funext axis
    change max (base.auxiliarySpace axis) (max ((context base N).auxiliarySpace axis) 0) = _
    rw [Nat.max_zero]
    apply max_eq_right
    cases axis <;> simp [context]
  rw [actual, context, RuntimeCtx.auxiliarySpace_addRetained, resultSpace, add_comm]

/-- No quantum system is added by the zero-batch output allocation. -/
lemma additionalSpace_quantum (dimension : ℕ+) :
    additionalSpace N (.quantumSystems dimension) = 0 := rfl

/-- The actual zero-batch run jointly restores every borrowed resource and reference correlation. -/
lemma run_restoresBorrowed {Reference : Register}
    (input : Execution.OracleInput .empty base Reference) :
    (run base N).RestoresBorrowed environment input :=
  AlgorithmRun.restoresBorrowed_of_circuit (environment := environment) (run base N)
    (fun _ {_} _ state => Circuit.borrowedRestored_retain (environment := environment)
      (model := .quantum AlgorithmGate.model .empty BitWord.model) base.canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh state) input

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryEmpty
