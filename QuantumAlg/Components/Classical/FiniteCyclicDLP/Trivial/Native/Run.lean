/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Semantics
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect

/-!
# Actual order-one run and its certain output

The original actual retained zero-recovery circuit is the run's sole code.
Its complete output manifest accounts for every original caller entry and
the retained optional candidate. Any normalized input, including mixed states
and arbitrary external reference, gives the actual some-zero result with
probability one. No secret witness is supplied to the executable run.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original actual order-one circuit and complete manifest form one executable run. -/
def zeroRun {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    AlgorithmRun model ctx (ctx.addRetained key (.option (.unsignedWord width)) fresh)
      (.option (.unsignedWord width)) where
  code := zeroRetained ctx width key fresh
  output := Output.all (ctx.addRetained key (.option (.unsignedWord width)) fresh)
    (.read (.storage (CWriteRef.retainedHead ctx key
      (.option (.unsignedWord width)) fresh).toCStorageRef))

/-- Every certified input gives the actual retained some-zero output with probability one. -/
lemma zeroRun_output_probability {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) {Reference : Register}
    (initial : OracleInput model.classicalOracles ctx Reference) :
    (zeroRun ctx width key fresh).outputDistribution environment initial
      (.optionSome (CShape.wordOfNat width 0)) = 1 := by
  rw [AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  change ENNReal.ofReal
    (((zeroRetained ctx width key fresh).execute environment Reference
      (initial.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))).effectWeight
      (fun entry => if entry.1.read (.storage (CWriteRef.retainedHead ctx key
          (.option (.unsignedWord width)) fresh).toCStorageRef) =
          .optionSome (CShape.wordOfNat width 0) then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference))) = 1
  rw [zeroRetained_execute, ExecutionState.effectWeight_mapClassical_decision]
  simp only [zeroRetainedStep_store, Store.read_write_same, if_true]
  rw [ExecutionState.effectWeight_mapClassical_decision]
  change ENNReal.ofReal (∑ entry, (Effect.one (Register.prod ctx.register Reference)).weight
    (initial.state.block entry)) = 1
  simp only [Effect.weight_one]
  change ENNReal.ofReal initial.state.mass = 1
  rw [initial.normalized, ENNReal.ofReal_one]

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native
