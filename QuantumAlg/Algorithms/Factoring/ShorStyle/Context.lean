/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Layout
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Complete native Shor storage and the actual recovery input list

The original input is the unique zero-width borrowed unit anchor, with no
supplied base, factor, order or quantum system. The prepared batch retains
every true sample tuple. One actual retained option cell receives each native
recovery result and then the final first-success result. All sampled systems
and cells remain in the complete final output context.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

open Execution

noncomputable section

/-- The original fixed zero-width borrowed anchor is the entire input interface. -/
@[reducible]
def pre : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput (RuntimeCtx.empty : RuntimeCtx .quantum).canonicalFreshKey
    .unit (RuntimeCtx.empty : RuntimeCtx .quantum).canonicalFreshKey_fresh

/-- Preparation receives no supplied quantum systems. -/
theorem pre_quantumWires : pre.quantumWires = [] := rfl

/-- The original optional modulus-width factor word. -/
def outputShape (N : Nat) : CShape := .option (.unsignedWord (modulusBits N))

/-- One prepared reusable bank and the actual retained tuples from all rounds. -/
@[implicit_reducible]
def sampledContext (N count : Nat) : RuntimeCtx .quantum :=
  NativePreparedBatch.context pre pre_quantumWires N count

/-- The final result key is fresh for every actually retained batch entry. -/
def resultKey (N count : Nat) : StorageKey := (sampledContext N count).canonicalFreshKey

theorem resultFresh (N count : Nat) : resultKey N count ∉ (sampledContext N count).keys :=
  (sampledContext N count).canonicalFreshKey_fresh

/-- Complete output retains the entire sampled bank and all classical cells plus the result. -/
@[implicit_reducible]
def post (N count : Nat) : RuntimeCtx .quantum :=
  (sampledContext N count).addRetained (resultKey N count) (outputShape N) (resultFresh N count)

/-- The true retained optional result that every recovery visit and the final pack overwrite. -/
def resultRef (N count : Nat) : CWriteRef (post N count) (outputShape N) :=
  CWriteRef.retainedHead (sampledContext N count)
    (resultKey N count) (outputShape N) (resultFresh N count)

/-- Each original source tuple stays in the exact cell allocated by the actual sampling batch. -/
def tupleInput (N count : Nat) (index : Fin count) :
    CInputRef (post N count) (NativeIteration.resultShape N) :=
  (NativeBatch.resultInput (NativeBank.context pre pre_quantumWires N) N count index).underRetained
    (resultKey N count) (outputShape N) (resultFresh N count)

/-- The native factor visit reads its actual sampler parameter and measured phase projections. -/
def visitInput (N count : Nat) (index : Fin count) : NativeFactorScan.Inputs (post N count) N where
  parameter := .first (.second (tupleInput N count index))
  phase := .second (.second (tupleInput N count index))

/-- Compile the real tuple references in precisely the source batch's finite index order. -/
def visitInputs (N count : Nat) : List (NativeFactorScan.Inputs (post N count) N) :=
  List.ofFn (visitInput N count)

/-- The new retained result does not move or replace any sampled quantum system. -/
theorem post_quantumWires (N count : Nat) :
    (post N count).quantumWires = (NativeQuantum.runtimeLayout N).wires :=
  NativePreparedBatch.quantumWires pre pre_quantumWires N count

/-- Actual result allocation preserves each complete source tuple's value. -/
theorem tupleInput_read (N count : Nat) (index : Fin count)
    (store : Store (sampledContext N count)) :
    (store.pushRetained (resultKey N count) (outputShape N) (resultFresh N count)).read
      (tupleInput N count index) =
      store.read (NativeBatch.resultInput (NativeBank.context pre pre_quantumWires N)
        N count index) :=
  Store.read_pushRetained_underRetained store _ _ _ _

/-- The actual result destination is disjoint from each original complete sampled tuple. -/
theorem result_tuple_separate (N count : Nat) (index : Fin count) :
    (resultRef N count).key ∉ (tupleInput N count index).storageKeys :=
  CInputRef.fresh_not_mem_storageKeys_underRetained
    (NativeBatch.resultInput (NativeBank.context pre pre_quantumWires N) N count index)
    (resultKey N count) (outputShape N) (resultFresh N count)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
