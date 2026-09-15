/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained

/-!
# Actual source sampling and one Shor iteration

The existing native sampler draws the original fixed number of residue
proposal bits and computes the complete parameter, including its early-factor
tag. Its real retained unit selects the compiled quantum member on the same
prepared bank. Actual Z outcomes are packed and retained with their sample
and complete parameter. The bank is reset and reloaded before a later retry.

No supplied outcome distribution, classical callback or detached preparation
is part of this execution. This construction records all the values needed
for the original recovery and even-modulus routes; it does not discard them
when resetting the quantum systems.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration

noncomputable section

variable (ctx : RuntimeCtx .quantum) (N : Nat)

/-- The source sampler's actual retained sample and full parameter context. -/
@[implicit_reducible]
def sampledContext : RuntimeCtx .quantum := Sampler.Retained.context ctx N

/-- The iteration additionally retains the measured phase cells and their packed result. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum := NativeStorage.context (sampledContext ctx N) N

theorem sampled_quantumWires : (sampledContext ctx N).quantumWires = ctx.quantumWires := rfl

/-- Sampling and result retention keep the exact same complete ordered quantum bank. -/
theorem quantumWires : (context ctx N).quantumWires = ctx.quantumWires :=
  (NativeStorage.quantumWires (sampledContext ctx N) N).trans (sampled_quantumWires ctx N)

/-- Read the actual retained source draw after all quantum readout allocations. -/
def sampleInput : CInputRef (context ctx N) (.bits (residueSamplingBits N)) :=
  NativeStorage.liftInput (sampledContext ctx N) N
    (.storage (Sampler.Retained.sampleRef ctx N).toCStorageRef)

/-- The complete sampler parameter, including its early-factor result, remains available. -/
def parameterInput : CInputRef (context ctx N) (ParameterShape (modulusBits N)) :=
  NativeStorage.liftInput (sampledContext ctx N) N
    (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)

/-- This is the same packed phase cell written by the actual measurement round. -/
def phaseInput : CInputRef (context ctx N) (.bits (phaseBits N)) :=
  .storage (NativeStorage.resultRef (sampledContext ctx N) N).toCStorageRef

/-- Draw the source sample, compute its parameter, and execute the actual selected quantum round. -/
def code (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) :
    Circuit ctx (context ctx N) :=
  .seq (Sampler.Retained.circuit ctx N)
    (NativeStorage.round (sampledContext ctx N) N
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef))

/-- All three source-facing values are read from this execution's actual live storage. -/
def resultShape : CShape :=
  .product (.bits (residueSamplingBits N))
    (.product (ParameterShape (modulusBits N)) (.bits (phaseBits N)))

def run (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) :
    AlgorithmRun ctx (context ctx N) (resultShape N) where
  code := code ctx N sameWires
  output := Output.all (context ctx N)
    (.read (.product (sampleInput ctx N) (.product (parameterInput ctx N) (phaseInput ctx N))))

/-- The retained source tuple is only a result view; the full live storage is still listed. -/
theorem output_listing (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) :
    (run ctx N sameWires).output.listing = (context ctx N).keys := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration
