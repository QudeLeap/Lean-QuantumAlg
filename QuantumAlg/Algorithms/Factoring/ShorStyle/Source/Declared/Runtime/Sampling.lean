/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Iteration
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# One actual preparation and the first complete declared Shor sample

The bank is prepared before sampling, as in the original execution schedule.
The real sampler retains its draw and complete computed parameter. The chosen
model-owned query, native peripherals, measurements and paid packing execute
on that bank. Every original caller system and retained result stays listed.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Sampling

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
  (input : Input N)

/-- Allocate the single actual bank by preparing every declared system in zero. -/
def prepare : Circuit (executionModel input) base (bankContext base noQuantum N) :=
  .prepareZero base base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N)

/-- Retain the original draw, complete parameter and actual measured phase results. -/
def context : RuntimeCtx .quantum :=
  Iteration.context (bankContext base noQuantum N) N

/-- The first source sample follows the same real initial bank preparation. -/
def code : Circuit (executionModel input) base (context base noQuantum N) :=
  .seq (prepare base noQuantum N input)
    (Iteration.code (bankContext base noQuantum N) N input
      (bankContext_wires base noQuantum N))

/-- All later classical storage leaves this same bank's complete wire list unchanged. -/
theorem quantumWires :
    (context base noQuantum N).quantumWires = (layout N).wires :=
  (Iteration.quantumWires (bankContext base noQuantum N) N).trans
    (bankContext_wires base noQuantum N)

/-- The source result is read from actual storage and includes the early-factor parameter. -/
def run : AlgorithmRun (executionModel input) base (context base noQuantum N)
    (Iteration.resultShape N) where
  code := code base noQuantum N input
  output := Output.all (context base noQuantum N)
    (.read (.product (Iteration.sampleInput (bankContext base noQuantum N) N)
      (.product (Iteration.parameterInput (bankContext base noQuantum N) N)
        (Iteration.phaseInput (bankContext base noQuantum N) N))))

/-- The actual source result retains the full caller, bank and result manifest. -/
theorem output_listing :
    (run base noQuantum N input).output.listing = (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Sampling
