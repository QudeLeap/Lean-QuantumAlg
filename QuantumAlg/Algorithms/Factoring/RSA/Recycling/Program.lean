/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Allocation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.InitialSeed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Empty
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Chronological RSA batches on one physically allocated recycled-control bank

All classical destinations are retained before the first actual source draw.
That draw and its complete parameter computation precede the sole quantum
allocation. Sixteen real measured members then share the bank, each followed
by paid packing and complete reset plus reload. Later batches draw their own
source only after the preceding recovery. Complete fixed-batch recovery and
first-success selection use their existing native classical programs.

-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev RecycledModel := ShortDLP.CompiledMAU.Recycling.model

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The parent allocates its sole quantum bank over this complete classical frame. -/
def readyContext (count : Nat) : RuntimeCtx .quantum :=
  ShortDLP.CompiledMAU.Recycling.context (ClassicalFrame.context base N count)
    (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)

/-- Source preparation writes the complete parameter into its distinct preallocated cell. -/
def source {ctx : RuntimeCtx .quantum}
    (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N)) : Circuit RecycledModel ctx ctx :=
  (ShorStyle.Canonical.Sampler.PackedSample.draw (model := RecycledModel) N sample).seq
    (ShorStyle.Canonical.Sampler.Program.circuit (model := RecycledModel)
      N (FirstAccepted.cellRead sample) parameter)

/-- The first source is drawn before any quantum bank exists. -/
def firstSource (laterCount : Nat) :
    Circuit RecycledModel (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.context base N (laterCount + 1)) :=
  source N (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (ClassicalFrame.parameterRef base N (laterCount + 1) 0)

/-- Subsequent source draws use the same physical bank without preparing it again. -/
def nextSource (count : Nat) (batch : Fin count) :
    Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  source N
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch))

/-- The stored complete parameter selects the real arithmetic for one chronological member. -/
def member (count : Nat) (batch : Fin count) (index : Fin 16) :
    Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  ShortDLP.CompiledMAU.Recycling.Round.code
    (ClassicalFrame.context base N count)
    (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch))) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.packedRef base N count batch index))

/-- Exactly sixteen complete members execute in chronological order on the same bank. -/
def members (count : Nat) (batch : Fin count) :
    Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  Circuit.forRange 16 (member base noQuantum N count batch)

/-- All sixteen paid packed observations are the actual classical recovery inputs. -/
def terminals (count : Nat) (batch : Fin count) :
    LatticePairRecoveryBatch.Terminals (readyContext base noQuantum N count) N :=
  fun index => FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
    (ClassicalFrame.packedRef base N count batch index))

/-- The existing full recovery allocates and releases its actual scratch on the same bank. -/
def recover (input : Input N) (count : Nat) (batch : Fin count) :
    Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  LatticeFixedBatchRecoveryMachine.into (model := RecycledModel)
    (readyContext base noQuantum N count) input
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.factorRef base N count batch))

/-- Recovery follows the last real member, including that member's terminal bank restart. -/
def batchBody (input : Input N) (count : Nat) (batch : Fin count) :
    Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  (members base noQuantum N count batch).seq (recover base noQuantum N input count batch)

/-- A later batch draws its fresh source after the preceding batch has finished. -/
def nextBatch (input : Input N) (count : Nat) (batch : Fin count) :
    Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  (nextSource base noQuantum N count batch).seq (batchBody base noQuantum N input count batch)

/-- Real optional selection reads every chronological factor and writes the final output. -/
def select (count : Nat) :
    Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  FirstAccepted.Direct.Optional.Allocation.into (model := RecycledModel)
    (fun batch => FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.factorRef base N count batch)))
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.selectedRef base N count))

/-- Positive execution has one bank allocation and no speculative future sampling. -/
def positiveCode (input : Input N) (laterCount : Nat) :
    Circuit RecycledModel base (readyContext base noQuantum N (laterCount + 1)) :=
  (ClassicalFrame.allocate base N (laterCount + 1)).seq
    ((firstSource base N laterCount).seq
      ((ShortDLP.CompiledMAU.Recycling.prepare
        (ClassicalFrame.context base N (laterCount + 1))
        (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).seq
          ((batchBody base noQuantum N input (laterCount + 1) 0).seq
            ((Circuit.forRange laterCount fun index =>
              nextBatch base noQuantum N input (laterCount + 1) index.succ).seq
                (select base noQuantum N (laterCount + 1))))))

/-- The positive output manifest contains every real source, result, bank wire and final factor. -/
def positiveRun (input : Input N) (laterCount : Nat) :
    AlgorithmRun RecycledModel base (readyContext base noQuantum N (laterCount + 1))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  code := positiveCode base noQuantum N input laterCount
  output := Output.all (readyContext base noQuantum N (laterCount + 1))
    (.read (.storage (ClassicalFrame.bankWrite noQuantum N (laterCount + 1)
      (ClassicalFrame.selectedRef base N (laterCount + 1))).toCStorageRef))

/-- No-bank zero execution retains the existing independently verified empty-result context. -/
public def outputContext : Nat → RuntimeCtx .quantum
  | 0 => NativeRetryEmpty.context base N
  | laterCount + 1 => readyContext base noQuantum N (laterCount + 1)

/-- All natural batch counts use the actual empty program or the actual single-bank parent. -/
def run (input : Input N) : (count : Nat) →
    AlgorithmRun RecycledModel base (outputContext base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => NativeRetryEmpty.run base N
  | laterCount + 1 => positiveRun base noQuantum N input laterCount

/-- The zero-count branch literally executes the existing empty-result program. -/
lemma rsaRecyclingParent_run_zero (input : Input N) :
    run base noQuantum N input 0 = NativeRetryEmpty.run base N := rfl

/-- Every surviving live entry occurs in the final output manifest for every batch count. -/
lemma rsaRecyclingParent_output_listing (input : Input N) (count : Nat) :
    (run base noQuantum N input count).output.listing =
      (outputContext base noQuantum N count).keys := by
  cases count <;> rfl

end

end QuantumAlg.Factoring.RSA.Recycling.Program
