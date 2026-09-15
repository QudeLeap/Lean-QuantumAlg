/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual retained phase results around the Shor bank

One packed phase result and one finite cell per measured phase wire are
allocated by actual retain instructions. Earlier sampler values and results
remain in their original cells. Lifting an input only preserves its reference
through those new cells; it performs no host computation or hidden copy.

These allocations do not modify any wire identity or dimension and can be
used around the same owned quantum bank in every retry.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (N : Nat)

/-- The packed result is a real fresh retained bit-string cell. -/
@[implicit_reducible]
def resultContext : RuntimeCtx .quantum :=
  ctx.addRetained ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh

/-- All per-wire results remain live alongside the packed result and the incoming frame. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum := MeasurementCells.context (resultContext ctx N) 2 (phaseBits N)

def resultRef : CWriteRef (context ctx N) (.bits (phaseBits N)) :=
  MeasurementCells.liftWrite 2
    (CWriteRef.retainedHead ctx ctx.canonicalFreshKey (.bits (phaseBits N))
      ctx.canonicalFreshKey_fresh) (phaseBits N)

def cells : Fin (phaseBits N) → CWriteRef (context ctx N) (.finite 2) :=
  MeasurementCells.reference (resultContext ctx N) 2 (phaseBits N)

/-- Any existing actual operand retains its original storage identity. -/
def liftInput {shape : CShape} (input : CInputRef ctx shape) : CInputRef (context ctx N) shape :=
  MeasurementCells.liftInput 2
    (input.underRetained ctx.canonicalFreshKey (.bits (phaseBits N))
      ctx.canonicalFreshKey_fresh) (phaseBits N)

/-- Allocate each declared result cell through the single interpreter. -/
def allocate : Circuit ctx (context ctx N) :=
  .seq (.retain ctx ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (MeasurementCells.allocate (resultContext ctx N) 2 (phaseBits N))

/-- The actual initial values introduced by those retain instructions. -/
def pushStore (store : Store ctx) : Store (context ctx N) :=
  MeasurementCells.pushStore 2 (phaseBits N)
    (store.pushRetained ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)

/-- The quantum bank remains exactly the same ordered list of physical wire records. -/
theorem quantumWires : (context ctx N).quantumWires = ctx.quantumWires :=
  MeasurementCells.context_quantumWires (resultContext ctx N) 2 (phaseBits N)

/-- Actual allocation preserves the value of the original sampler parameter or other operand. -/
theorem read_pushStore_liftInput {shape : CShape} (store : Store ctx)
    (input : CInputRef ctx shape) :
    (pushStore ctx N store).read (liftInput ctx N input) = store.read input := by
  rw [pushStore, liftInput, MeasurementCells.read_pushStore_liftInput]
  exact Store.read_pushRetained_underRetained _ _ _ _ _

/-- Extend real result storage and execute the selected member on the same prepared bank. -/
def round (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) : Circuit ctx (context ctx N) :=
  .seq (allocate ctx N)
    (NativeRound.code N ((quantumWires ctx N).trans sameWires)
      (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N))

/-- All old and new cells and the unchanged bank occur in the same complete output. -/
def run (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) :
    AlgorithmRun ctx (context ctx N) (.bits (phaseBits N)) where
  code := round ctx N sameWires parameter
  output := Output.all (context ctx N) (.read (.storage (resultRef ctx N).toCStorageRef))

theorem output_listing (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) :
    (run ctx N sameWires parameter).output.listing = (context ctx N).keys := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage
