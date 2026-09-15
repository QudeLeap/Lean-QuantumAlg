/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration.FrameObservation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Distribution

/-!
# Structural reading of every actual retained Shor round

The earlier operand and the first real tuple are lifted together through the
remaining allocations. Reading the indexed result vector gives exactly that
first tuple followed by the actual tail tuples. These are identities of real
references and store reads, with no computed result inserted into the circuit.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch

noncomputable section

/-- The original source outcome expressed in the actual retained tuple's bit conventions. -/
def sourceValue {N : Nat} (source : Input N) (outcome : SourceOutcome N) :
    (NativeIteration.resultShape N).Value :=
  .product (.bits (Sampler.PackedSample.storedBits outcome.sample))
    (.product (parameterValue source outcome.sample) (.bits outcome.measurement))

/-- The exact batch lift preserves the product structure of two existing operands. -/
theorem liftInput_product {ctx : RuntimeCtx .quantum} (N : Nat) {left right : CShape}
    (first : CInputRef ctx left) (second : CInputRef ctx right) (count : Nat) :
    liftInput N (.product first second) count =
      .product (liftInput N first count) (liftInput N second count) := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      have oneRound : NativeIteration.liftInput N (.product first second) =
          .product (NativeIteration.liftInput N first) (NativeIteration.liftInput N second) :=
        NativeIteration.storage_lift_product N (Sampler.Retained.liftInput (N := N) first)
          (Sampler.Retained.liftInput (N := N) second)
      change liftInput N (NativeIteration.liftInput N (.product first second)) count = _
      rw [oneRound, induction]
      rfl

/-- The first tuple is the real first round, under precisely the remaining actual allocations. -/
theorem resultInput_zero (ctx : RuntimeCtx .quantum) (N count : Nat) :
    resultInput ctx N (count + 1) 0 =
      liftInput N (.product (NativeIteration.sampleInput ctx N)
        (.product (NativeIteration.parameterInput ctx N) (NativeIteration.phaseInput ctx N)))
        count := rfl

/-- Every later tuple belongs to the actual tail sequence in the original order. -/
theorem resultInput_succ (ctx : RuntimeCtx .quantum) (N count : Nat) (index : Fin count) :
    resultInput ctx N (count + 1) index.succ =
      resultInput (NativeIteration.context ctx N) N count index := rfl

/-- The function of actual stored tuple reads decomposes into its first entry and true tail. -/
theorem read_resultInput_cons (ctx : RuntimeCtx .quantum) (N count : Nat)
    (store : Execution.Store (context ctx N (count + 1))) :
    (fun index => store.read (resultInput ctx N (count + 1) index)) =
      Fin.cons
        (store.read (liftInput N (.product (NativeIteration.sampleInput ctx N)
          (.product (NativeIteration.parameterInput ctx N) (NativeIteration.phaseInput ctx N)))
          count))
        (fun index => store.read (resultInput (NativeIteration.context ctx N) N count index)) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch
