/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Semantics
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Actual Shor result storage keeps the prepared bank coordinates

The packed result and finite phase cells are actual classical allocations.
Their existing physical basis map carries the same bank seed unchanged.
After the selected quantum round, the real full-bank reset and reload again
establish that seed on every complete final store-reference block.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage

noncomputable section

open Execution

private theorem cells_seed_basis {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (dimension : ℕ+) (count : Nat) :
    MeasurementCells.basisEquiv ctx dimension count
        ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) =
      (NativePlacement.basisEquiv N
        ((MeasurementCells.context_quantumWires ctx dimension count).trans sameWires)).symm
          (NativeQuantum.seedLabel N) := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

variable (ctx : RuntimeCtx .quantum) (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Every real readout allocation preserves the full store-reference bank seed invariant. -/
theorem allocate_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N ((quantumWires ctx N).trans sameWires)).symm
        (NativeQuantum.seedLabel N))
      ((allocate ctx N).execute Reference state) := by
  let allocationHead := Circuit.retain ctx ctx.canonicalFreshKey (.bits (phaseBits N))
    ctx.canonicalFreshKey_fresh
  let middleWires : (resultContext ctx N).quantumWires =
      (NativeQuantum.runtimeLayout N).wires := sameWires
  let middleSeed : (resultContext ctx N).register.Index :=
    (NativePlacement.basisEquiv N middleWires).symm (NativeQuantum.seedLabel N)
  have retained : BasisSeeded.Holds (ctx := resultContext ctx N) middleSeed
      (allocationHead.execute Reference state) :=
    BasisSeeded.retain ((NativePlacement.basisEquiv N sameWires).symm
      (NativeQuantum.seedLabel N)) state seeded ctx.canonicalFreshKey (.bits (phaseBits N))
        ctx.canonicalFreshKey_fresh
  have allocated := MeasurementCells.allocate_seeded (resultContext ctx N) 2 (phaseBits N)
    middleSeed (allocationHead.execute Reference state) retained
  have combined := BasisSeeded.seq allocationHead
    (MeasurementCells.allocate (resultContext ctx N) 2 (phaseBits N))
    (MeasurementCells.basisEquiv (resultContext ctx N) 2 (phaseBits N) middleSeed) state allocated
  have seedEquality := cells_seed_basis N middleWires 2 (phaseBits N)
  exact (congrArg (fun seed : (context ctx N).register.Index =>
    BasisSeeded.Holds (ctx := context ctx N) seed ((allocate ctx N).execute Reference state))
      seedEquality).mp combined

/-- The actual allocated round restores its one existing bank for another source sample. -/
theorem round_seeded (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N ((quantumWires ctx N).trans sameWires)).symm
        (NativeQuantum.seedLabel N))
      ((round ctx N sameWires parameter).execute Reference state) :=
  BasisSeeded.seq (allocate ctx N)
    (NativeRound.code N ((quantumWires ctx N).trans sameWires)
      (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N)) _ state
    (NativeRound.round_seeded N ((quantumWires ctx N).trans sameWires)
      (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N)
      ((allocate ctx N).execute Reference state))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage
