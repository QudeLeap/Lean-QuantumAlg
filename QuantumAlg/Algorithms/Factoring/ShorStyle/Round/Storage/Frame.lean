/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Packed.Frame

/-!
# Actual Shor readout allocation separates every earlier input

The existing allocator creates the packed result and each finite phase cell
with real fresh keys. They cannot alias any structural earlier input. Thus
the actual sampled parameter, source bits and prior results survive the
phase writes without adding a state-domain or caller separation premise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage

noncomputable section

open Execution

variable (ctx : RuntimeCtx .quantum) (N : Nat)

/-- The actual retained phase cells have pairwise distinct storage identities. -/
theorem cells_distinct : Function.Injective (fun index => (cells ctx N index).key) :=
  MeasurementCells.reference_key_injective (resultContext ctx N) 2 (phaseBits N)

/-- Each actual phase cell is separate from every earlier structural input. -/
theorem cells_separate {shape : CShape} (input : CInputRef ctx shape) (index : Fin (phaseBits N)) :
    (cells ctx N index).key ∉ (liftInput ctx N input).storageKeys :=
  MeasurementCells.reference_not_mem_liftInput 2
    (input.underRetained ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (phaseBits N) index

/-- The actual packed result cell is also separate from every earlier structural input. -/
theorem result_separate {shape : CShape} (input : CInputRef ctx shape) :
    (resultRef ctx N).key ∉ (liftInput ctx N input).storageKeys := by
  have key := MeasurementCells.liftWrite_key 2
    (CWriteRef.retainedHead ctx ctx.canonicalFreshKey (.bits (phaseBits N))
      ctx.canonicalFreshKey_fresh) (phaseBits N)
  have keys := MeasurementCells.liftInput_storageKeys 2
    (input.underRetained ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (phaseBits N)
  intro member
  apply CInputRef.fresh_not_mem_storageKeys_underRetained input ctx.canonicalFreshKey
    (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh
  have actual : (resultRef ctx N).key ∈
      (input.underRetained ctx.canonicalFreshKey (.bits (phaseBits N))
        ctx.canonicalFreshKey_fresh).storageKeys := keys ▸ member
  change (resultRef ctx N).key = ctx.canonicalFreshKey at key
  rw [key] at actual
  exact actual

/-- Allocation followed by the real phase writes keeps every original input value. -/
theorem packed_pushStore_read {shape : CShape} (input : CInputRef ctx shape)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (store : Store ctx) (basis : (context ctx N).register.Index) :
    (NativeRound.packedBasisStore N ((quantumWires ctx N).trans sameWires)
      (cells ctx N) (resultRef ctx N) (pushStore ctx N store) basis).read (liftInput ctx N input) =
      store.read input :=
  (NativeRound.packed_read_preserved N ((quantumWires ctx N).trans sameWires)
    (cells ctx N) (resultRef ctx N) (liftInput ctx N input)
    (cells_separate ctx N input) (result_separate ctx N input) (pushStore ctx N store) basis).trans
      (read_pushStore_liftInput ctx N store input)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage
