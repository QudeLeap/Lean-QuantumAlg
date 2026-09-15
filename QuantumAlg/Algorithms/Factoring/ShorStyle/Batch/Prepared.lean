/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Seed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Preparation

/-!
# One real preparation followed by the complete finite Shor sampling batch

The existing classical frame is preserved while one owned entry allocates the
phase, power and arithmetic words. Every later iteration uses that same bank
and real reset/reload. All source samples, full parameters, measured cells and
packed phase values remain in the complete final output manifest.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch

noncomputable section

open Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = []) (N count : Nat)

/-- The actual single bank and every retained finite-batch result cell. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum :=
  NativeBatch.context (NativeBank.context ctx noQuantum N) N count

/-- Prepare the full physical bank once, then execute the real finite sequence on it. -/
def code : Circuit ctx (context ctx noQuantum N count) :=
  .seq (NativeBank.prepare ctx noQuantum N)
    (NativeBatch.code (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count)

/-- The actual complete sequence has precisely the original prepared bank's wire records. -/
theorem quantumWires :
    (context ctx noQuantum N count).quantumWires = (NativeQuantum.runtimeLayout N).wires :=
  (NativeBatch.quantumWires (NativeBank.context ctx noQuantum N) N count).trans
    (NativeBank.quantumWires ctx noQuantum N)

/-- All final store blocks retain the true source seed and their complete reference entries. -/
theorem code_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N (quantumWires ctx noQuantum N count)).symm
        (NativeQuantum.seedLabel N))
      ((code ctx noQuantum N count).execute Reference state) :=
  BasisSeeded.seq (NativeBank.prepare ctx noQuantum N)
    (NativeBatch.code (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count) _ state
    (NativeBatch.code_seeded (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count
      ((NativeBank.prepare ctx noQuantum N).execute Reference state)
      (NativeBank.prepare_seeded ctx noQuantum N state))

/-- The preparation event prefixes the actual batch trace, including all real reset operations. -/
theorem code_eventTrace (path : (code ctx noQuantum N count).Path) :
    (code ctx noQuantum N count).eventTrace path =
      (NativeQuantum.seedPreparation N).event ::
        (NativeBatch.code (NativeBank.context ctx noQuantum N) N
          (NativeBank.quantumWires ctx noQuantum N) count).eventTrace path.2 := rfl

/-- Read the real tuple vector while listing every retained classical and quantum storage entry. -/
def run : AlgorithmRun ctx (context ctx noQuantum N count)
    (.fixedVector count (NativeIteration.resultShape N)) where
  code := code ctx noQuantum N count
  output := Output.all (context ctx noQuantum N count)
    (.read (NativeBatch.readout (NativeBank.context ctx noQuantum N) N count))

theorem output_listing :
    (run ctx noQuantum N count).output.listing = (context ctx noQuantum N count).keys := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch
