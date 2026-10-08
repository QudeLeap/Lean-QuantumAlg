/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Program

/-!
# One actual first batch followed by finitely many batches on its existing bank

The sole first-batch constructor precedes the complete suffix. Each suffix
step calls only the actual reuse constructor with structurally lifted original
measurement cells. Every batch executes all its rounds and recovery, and each
factor stays in its own retained cell. Output observes these existing cells in
chronological order and lists every live entry; it adds no physical array.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

open Execution ShortDLP.CompiledMAU

variable {N : Nat}

/-- Actual later batches reuse the same bank and structurally lifted original measurement cells. -/
def suffixCode (input : Input N) : (start : RuntimeCtx .quantum) →
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires) →
    (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2)) →
    (count : Nat) → Circuit RuntimeRound.model start (suffixContext N start count)
  | start, _, _, 0 => .id (model := RuntimeRound.model) start
  | start, wires, originalCells, count + 1 =>
      .seq (NativeBatchReuseRecovery.code start wires originalCells input)
        (suffixCode input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => reuseWrite N (originalCells index)) count)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Exactly one first-batch constructor precedes the actual same-bank suffix. -/
def code (input : Input N) (count : Nat) :
    Circuit RuntimeRound.model base (context base noQuantum N count) :=
  .seq (NativeBatchRecovery.code base noQuantum input)
    (suffixCode input (NativeBatchRecovery.context base noQuantum N)
      (firstWires base noQuantum N) (firstCells base noQuantum N) count)

/-- Complete output reads each real retained factor cell without constructing new storage. -/
def run (input : Input N) (count : Nat) :
    AlgorithmRun RuntimeRound.model base (context base noQuantum N count)
      (.fixedVector (count + 1) (LatticeBatchRecoveryOutput.OutputShape N)) where
  code := code base noQuantum input count
  output := Output.all (context base noQuantum N count)
    (.read (.fixedVector (resultRefs base noQuantum N count)))

/-- All original and newly retained entries occur in the actual final output manifest. -/
theorem output_listing (input : Input N) (count : Nat) :
    (run base noQuantum input count).output.listing =
      (context base noQuantum N count).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain
