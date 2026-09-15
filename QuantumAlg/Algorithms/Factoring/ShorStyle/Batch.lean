/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame

/-!
# Actual finite Shor sampling on one reusable bank

Each round executes the real source sampler, selected quantum program,
measurement, packing and reset/reload. Its actual result cells remain live
while the next round uses the same physical bank. The tuple view below reads
only those cells; assembling a structural input introduces no hidden copy.
The quantum bank is prepared outside this finite sequence exactly once.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch

noncomputable section

/-- The successive actual retained result contexts, starting with the existing owned bank. -/
@[implicit_reducible]
def context (ctx : RuntimeCtx .quantum) (N : Nat) : Nat → RuntimeCtx .quantum
  | 0 => ctx
  | count + 1 => context (NativeIteration.context ctx N) N count

/-- Every round retains the identical ordered physical wire records of the incoming bank. -/
theorem quantumWires (ctx : RuntimeCtx .quantum) (N count : Nat) :
    (context ctx N count).quantumWires = ctx.quantumWires := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact (induction (NativeIteration.context ctx N)).trans (NativeIteration.quantumWires ctx N)

/-- Preserve an earlier operand beneath precisely the allocations performed by the batch. -/
def liftInput {ctx : RuntimeCtx .quantum} (N : Nat) {shape : CShape}
    (input : CInputRef ctx shape) : (count : Nat) → CInputRef (context ctx N count) shape
  | 0 => input
  | count + 1 => liftInput N
      (NativeStorage.liftInput (NativeIteration.sampledContext ctx N) N
        (Sampler.Retained.liftInput (N := N) input)) count

/-- Each indexed tuple reads the genuine retained source, parameter and measured phase. -/
def resultInput (ctx : RuntimeCtx .quantum) (N : Nat) :
    (count : Nat) → Fin count → CInputRef (context ctx N count) (NativeIteration.resultShape N)
  | 0, index => Fin.elim0 index
  | count + 1, index => Fin.cases
      (liftInput N
        (.product (NativeIteration.sampleInput ctx N)
          (.product (NativeIteration.parameterInput ctx N)
            (NativeIteration.phaseInput ctx N))) count)
      (resultInput (NativeIteration.context ctx N) N count) index

/-- The finite result view lists all real tuples in their original execution order. -/
def readout (ctx : RuntimeCtx .quantum) (N count : Nat) :
    CInputRef (context ctx N count) (.fixedVector count (NativeIteration.resultShape N)) :=
  .fixedVector (resultInput ctx N count)

/-- The finite composition uses only the single actual circuit interpreter. -/
def code (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) :
    (count : Nat) → Circuit ctx (context ctx N count)
  | 0 => .id ctx
  | count + 1 => .seq (NativeIteration.code ctx N sameWires)
      (code (NativeIteration.context ctx N) N
        ((NativeIteration.quantumWires ctx N).trans sameWires) count)

/-- The result tuple view accompanies a complete manifest of the full actual live context. -/
def run (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat) :
    AlgorithmRun ctx (context ctx N count)
      (.fixedVector count (NativeIteration.resultShape N)) where
  code := code ctx N sameWires count
  output := Output.all (context ctx N count) (.read (readout ctx N count))

theorem output_listing (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat) :
    (run ctx N sameWires count).output.listing = (context ctx N count).keys := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch
