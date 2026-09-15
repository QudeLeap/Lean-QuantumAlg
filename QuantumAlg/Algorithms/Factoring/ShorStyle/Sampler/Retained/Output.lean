/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Shape
public import QuantumAlg.Core.Algorithm.ClassicalOp
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Readout
import all QuantumAlg.Core.Execution.Output

/-!
# Complete Output of actual retained residue sampling

The manifest lists both real retained results and every original caller key.
Its structural result reads the stored random bits together with the complete
unit, early-factor flag and factor payload. Reading this result performs no
new operation and leaves every classical and quantum system live.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind}

/-- The stored source bits and complete RSA parameter form the actual classical result. -/
public def outputShape (N : Nat) : CShape :=
  .product (.bits (residueSamplingBits N)) (ParameterShape (modulusBits N))

/-- Complete live-key manifest with a structural read of the two actual retained outputs. -/
def output (ctx : RuntimeCtx kind) (N : Nat) : Output (context ctx N) (outputShape N) :=
  Output.all (context ctx N) (.read (.product
    (FirstAccepted.cellRead (sampleRef ctx N)) (FirstAccepted.cellRead (parameterRef ctx N))))

/-- Independent source value, including every retained sample and early-factor bit. -/
public def outputValue {N : Nat} (input : Input N)
    (value : Fin (2 ^ residueSamplingBits N)) : (outputShape N).Value :=
  .product (.bits (PackedSample.storedBits value)) (parameterValue input value)

/-- The complete manifest contains both real result keys and every original caller key. -/
theorem samplerRetained_output_listing (ctx : RuntimeCtx kind) (N : Nat) :
    (output ctx N).listing = (parameterRef ctx N).key :: (sampleRef ctx N).key :: ctx.keys := rfl

/-- Every actual sampled native path reads the independently specified complete source value. -/
theorem samplerRetained_output_outcome (ctx : RuntimeCtx kind) {N : Nat} (input : Input N)
    (store : Store (context ctx N)) (value : Fin (2 ^ residueSamplingBits N)) :
    (output ctx N).eval (outcomeStep ctx N store value).1 = outputValue input value := by
  change CShape.Value.product
    ((outcomeStep ctx N store value).1.read (FirstAccepted.cellRead (sampleRef ctx N)))
    ((outcomeStep ctx N store value).1.read (FirstAccepted.cellRead (parameterRef ctx N))) = _
  exact congrArg₂ CShape.Value.product (samplerRetained_outcome_sample store value)
    (samplerRetained_outcome_parameter input store value)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
