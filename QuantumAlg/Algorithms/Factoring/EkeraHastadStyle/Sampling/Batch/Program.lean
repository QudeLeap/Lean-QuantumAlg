/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition

/-!
# Native first batch in the original sampler-before-preparation order

One actual retained residue sampler runs before the single owned-bank
preparation. The finite measurement cells are then retained once, followed by
sixteen actual member/measurement/packing/reset/reload rounds on that bank.
Each member dispatch reads the real retained parameter through structural
references. No host-supplied sample or proof-supplied generator enters the run.

The result is the original sample, the full unit/early-factor parameter and
the chronological sixteen outcomes. The complete Output also retains every
other live cell and the owned bank, ready for subsequent recovery and reuse.
This first-batch constructor is not called again by a later retry.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open ShortDLP.CompiledMAU
open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The sole quantum allocation follows the actual complete native sampler. -/
def sampleAndPrepare : Circuit RuntimeRound.model base (bankContext base noQuantum N) :=
  .seq (ShorStyle.Canonical.Sampler.Retained.circuit (model := RuntimeRound.model) base N)
    (RuntimeBank.prepare (operations := BitWord.model) (services := .empty) (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)

/-- Shared finite cells are actually allocated once before the measured rounds. -/
def initializeBank : Circuit RuntimeRound.model base (readyContext base noQuantum N) :=
  .seq (sampleAndPrepare base noQuantum N)
    (MeasurementCells.allocate (model := RuntimeRound.model)
      (bankContext base noQuantum N) 2 (measurementBits N))

/-- Sixteen chronological outcomes come from the stored parameter and the same actual bank. -/
def rounds : Circuit RuntimeRound.model
    (readyContext base noQuantum N) (context base noQuantum N) :=
  RuntimeRepetition.code (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
    (parameter base noQuantum N) (cells base noQuantum N) 16

/-- Complete first-batch syntax, preserving source sampling and early-factor handling order. -/
def code : Circuit RuntimeRound.model base (context base noQuantum N) :=
  .seq (initializeBank base noQuantum N) (rounds base noQuantum N)

/-- The original sample, complete parameter and all sixteen actual packed outcomes. -/
def resultShape (N : Nat) : CShape :=
  .product (.bits (residueSamplingBits N))
    (.product (ParameterShape N) (.fixedVector 16 (.bits (measurementBits N))))

/-- Actual complete Output retains the bank and observes only existing result cells. -/
def run : AlgorithmRun RuntimeRound.model base (context base noQuantum N) (resultShape N) where
  code := code base noQuantum N
  output := Output.all (context base noQuantum N)
    (.read (.product (finalSample base noQuantum N)
      (.product (finalParameter base noQuantum N) (finalResults base noQuantum N))))

/-- Nothing live is hidden from the first batch's complete final manifest. -/
theorem nativeBatch_output_listing :
    (run base noQuantum N).output.listing = (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
