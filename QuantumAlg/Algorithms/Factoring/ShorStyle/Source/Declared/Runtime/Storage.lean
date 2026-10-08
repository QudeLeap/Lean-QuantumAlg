/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Retained Shor phase cells around the existing declared bank

The result allocations preserve the current physical bank. Each retry can
retain its actual sample, complete parameter and phase outcome beside that
same bank without creating a new quantum preparation or changing wire order.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Storage

noncomputable section

open Execution

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

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Storage
