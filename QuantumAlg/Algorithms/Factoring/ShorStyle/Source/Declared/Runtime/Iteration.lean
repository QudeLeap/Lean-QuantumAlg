/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Execution

/-!
# Actual retained sampling followed by the chosen declared Shor member

The original native sampler computes the complete parameter, including the
first early-factor result. The actual stored unit chooses the granted member.
All source bits, parameter cells and physical phase outcomes remain alongside
one unchanged quantum bank, with a full live-storage output manifest.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Iteration

open Execution

noncomputable section

variable (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)

/-- The source sampler's actual retained sample and full parameter context. -/
@[implicit_reducible]
def sampledContext : RuntimeCtx .quantum := Sampler.Retained.context ctx N

/-- The iteration additionally retains the measured phase cells and their packed result. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum := Storage.context (sampledContext ctx N) N

theorem sampled_quantumWires : (sampledContext ctx N).quantumWires = ctx.quantumWires := rfl

/-- Sampling and result retention keep the exact same complete ordered quantum bank. -/
theorem quantumWires : (context ctx N).quantumWires = ctx.quantumWires :=
  (Storage.quantumWires (sampledContext ctx N) N).trans (sampled_quantumWires ctx N)

/-- Read the actual retained source draw after all quantum readout allocations. -/
def sampleInput : CInputRef (context ctx N) (.bits (residueSamplingBits N)) :=
  Storage.liftInput (sampledContext ctx N) N
    (.storage (Sampler.Retained.sampleRef ctx N).toCStorageRef)

/-- The complete sampler parameter, including its early-factor result, remains available. -/
def parameterInput : CInputRef (context ctx N) (ParameterShape (modulusBits N)) :=
  Storage.liftInput (sampledContext ctx N) N
    (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)

/-- This is the same packed phase cell written by the actual measurement round. -/
def phaseInput : CInputRef (context ctx N) (.bits (phaseBits N)) :=
  .storage (Storage.resultRef (sampledContext ctx N) N).toCStorageRef

/-- Draw the source sample, compute its parameter, and execute the actual selected quantum round. -/
def code (sameWires : ctx.quantumWires = (layout N).wires) :
    Circuit (executionModel input) ctx (context ctx N) :=
  .seq (Sampler.Retained.circuit (model := executionModel input) ctx N)
    (Runtime.code (sampledContext ctx N) N input
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef))

/-- All three source-facing values are read from this execution's actual live storage. -/
def resultShape : CShape :=
  .product (.bits (residueSamplingBits N))
    (.product (ParameterShape (modulusBits N)) (.bits (phaseBits N)))

def run (sameWires : ctx.quantumWires = (layout N).wires) :
    AlgorithmRun (executionModel input) ctx (context ctx N) (resultShape N) where
  code := code ctx N input sameWires
  output := Output.all (context ctx N)
    (.read (.product (sampleInput ctx N) (.product (parameterInput ctx N) (phaseInput ctx N))))

/-- The retained source tuple is only a result view; the full live storage is still listed. -/
theorem output_listing (sameWires : ctx.quantumWires = (layout N).wires) :
    (run ctx N input sameWires).output.listing = (context ctx N).keys := rfl


end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Iteration
