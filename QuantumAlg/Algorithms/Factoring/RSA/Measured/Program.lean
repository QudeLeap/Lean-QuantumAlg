/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA.Configuration

public import QuantumAlg.Core.Base.Accounting.Context

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Allocation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Parameters
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Seed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Empty
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Chronological RSA batches on the actual measured constant-workspace bank

All classical destinations are retained before the original first source
draw and complete parameter calculation. The sole quantum allocation has
2n+4 systems. Configured original members execute measured arithmetic,
paid packing and full reset/reload before complete all-pairs recovery.
The original sampler and early-factor precedence remain unchanged
[G25, main.tex:199-295,354-360; EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev MeasuredRSAModel : ExecutionModel :=
  .quantum AlgorithmGate.model .empty BitWord.model

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The parent allocates its sole quantum bank over this complete classical frame. -/
def readyContext (count : Nat) : RuntimeCtx .quantum :=
  ShortDLP.CompiledMAU.Recycling.Measured.context (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)

/-- Original parent cells retain their exact physical identity under the measured frame. -/
def bankWrite (count : Nat) {shape : CShape}
    (ref : CWriteRef (Recycling.ClassicalFrame.context base N count) shape) :
    CWriteRef (readyContext base noQuantum N count) shape :=
  (ShortDLP.CompiledMAU.Recycling.Measured.parentTransport
    (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).liftWrite ref

/-- Structural input lifting preserves the complete original parent read. -/
def bankInput (count : Nat) {shape : CShape}
    (input : CInputRef (Recycling.ClassicalFrame.context base N count) shape) :
    CInputRef (readyContext base noQuantum N count) shape :=
  (ShortDLP.CompiledMAU.Recycling.Measured.parentTransport
    (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).liftInput input

/-- Source preparation writes the complete parameter into its distinct preallocated cell. -/
def source {ctx : RuntimeCtx .quantum}
    (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N)) : Circuit MeasuredRSAModel ctx ctx :=
  (ShorStyle.Canonical.Sampler.PackedSample.draw (model := MeasuredRSAModel) N sample).seq
    (ShorStyle.Canonical.Sampler.Program.circuit (model := MeasuredRSAModel)
      N (FirstAccepted.cellRead sample) parameter)

/-- The first source is drawn before any quantum bank exists. -/
def firstSource (laterCount : Nat) :
    Circuit MeasuredRSAModel (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (Recycling.ClassicalFrame.context base N (laterCount + 1)) :=
  source N (Recycling.ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (Recycling.ClassicalFrame.parameterRef base N (laterCount + 1) 0)

/-- Subsequent source draws use the same physical bank without preparing it again. -/
def nextSource (count : Nat) (batch : Fin count) :
    Circuit MeasuredRSAModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  source N
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.sampleRef base N count batch))
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch))

/-- The stored complete parameter selects the real arithmetic for one chronological member. -/
def member (input : Input N) (count : Nat) (batch : Fin count) (index : Fin membersPerBatch) :
    Circuit MeasuredRSAModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  ShortDLP.CompiledMAU.Recycling.Measured.Round.code
    (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (measuredRSA_arithmeticBits_atLeastTwo input) (modulusWord N)
    (parameterGenerator N) (parameterTargetWord N)
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.packedRef base N count batch index))

/-- Exactly configured complete members execute in chronological order on the same bank. -/
def members (input : Input N) (count : Nat) (batch : Fin count) :
    Circuit MeasuredRSAModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  Circuit.forRange membersPerBatch (member base noQuantum N input count batch)

/-- All configured paid packed observations are the actual classical recovery inputs. -/
def terminals (count : Nat) (batch : Fin count) :
    LatticePairRecoveryBatch.Terminals (readyContext base noQuantum N count) N
      configuration.additionalMembers :=
  fun index => FirstAccepted.cellRead (bankWrite base noQuantum N count
    (Recycling.ClassicalFrame.packedRef base N count batch index))

/-- The existing full recovery allocates and releases its actual scratch on the same bank. -/
def recover (input : Input N) (count : Nat) (batch : Fin count) :
    Circuit MeasuredRSAModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  LatticeFixedBatchRecoveryMachine.into (model := MeasuredRSAModel)
    (readyContext base noQuantum N count) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.factorRef base N count batch))

/-- Recovery follows the last real member, including that member's terminal bank restart. -/
def batchBody (input : Input N) (count : Nat) (batch : Fin count) :
    Circuit MeasuredRSAModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  (members base noQuantum N input count batch).seq (recover base noQuantum N input count batch)

/-- A later batch draws its fresh source after the preceding batch has finished. -/
def nextBatch (input : Input N) (count : Nat) (batch : Fin count) :
    Circuit MeasuredRSAModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  (nextSource base noQuantum N count batch).seq (batchBody base noQuantum N input count batch)

/-- Real optional selection reads every chronological factor and writes the final output. -/
def select (count : Nat) :
    Circuit MeasuredRSAModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) :=
  FirstAccepted.Direct.Optional.Allocation.into (model := MeasuredRSAModel)
    (fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)))
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.selectedRef base N count))

/-- Positive execution has one bank allocation and no speculative future sampling. -/
def positiveCode (input : Input N) (laterCount : Nat) :
    Circuit MeasuredRSAModel base (readyContext base noQuantum N (laterCount + 1)) :=
  (Recycling.ClassicalFrame.allocate base N (laterCount + 1)).seq
    ((firstSource base N laterCount).seq
      ((ShortDLP.CompiledMAU.Recycling.Measured.prepare
        (Recycling.ClassicalFrame.context base N (laterCount + 1))
        (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat).seq
          ((batchBody base noQuantum N input (laterCount + 1) 0).seq
            ((Circuit.forRange laterCount fun index =>
              nextBatch base noQuantum N input (laterCount + 1) index.succ).seq
                (select base noQuantum N (laterCount + 1))))))

/-- The positive output manifest contains every real source, result, bank wire and final factor. -/
def positiveRun (input : Input N) (laterCount : Nat) :
    AlgorithmRun MeasuredRSAModel base (readyContext base noQuantum N (laterCount + 1))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  code := positiveCode base noQuantum N input laterCount
  output := Output.all (readyContext base noQuantum N (laterCount + 1))
    (.read (.storage (bankWrite base noQuantum N (laterCount + 1)
      (Recycling.ClassicalFrame.selectedRef base N (laterCount + 1))).toCStorageRef))

/-- No-bank zero execution retains the existing independently verified empty-result context. -/
public def outputContext : Nat → RuntimeCtx .quantum
  | 0 => NativeRetryEmpty.context base N
  | laterCount + 1 => readyContext base noQuantum N (laterCount + 1)

/-- All natural batch counts use the actual empty program or the actual single-bank parent. -/
def run (input : Input N) : (count : Nat) →
    AlgorithmRun MeasuredRSAModel base (outputContext base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => NativeRetryEmpty.run base N
  | laterCount + 1 => positiveRun base noQuantum N input laterCount

/-- The zero-count branch literally executes the existing empty-result program. -/
lemma rsaMeasuredParent_run_zero (input : Input N) :
    run base noQuantum N input 0 = NativeRetryEmpty.run base N := rfl

/-- Every surviving live entry occurs in the final output manifest for every batch count. -/
lemma rsaMeasuredParent_output_listing (input : Input N) (count : Nat) :
    (run base noQuantum N input count).output.listing =
      (outputContext base noQuantum N count).keys := by
  cases count <;> rfl

end

end QuantumAlg.Factoring.RSA.Measured.Program
