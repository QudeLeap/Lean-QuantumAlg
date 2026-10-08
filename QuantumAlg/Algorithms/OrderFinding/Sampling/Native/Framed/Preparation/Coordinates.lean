/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Preparation
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement

/-!
# Coordinates of physical zero preparation

The generic empty-frame preparation equivalence and the actual native word's
same-wire equivalence identify each source quantum position. The relation is
used to connect the interpreter's prepared density to the Born vector.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

private theorem freshDisjoint (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) (t width : Nat) :
    List.Disjoint (Sampling.Native.runtimeLayout t width).identities ctx.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum]
  exact List.disjoint_nil_right _

/-- The empty-frame preparation and native-word basis maps agree. -/
theorem preparedEmptyBasis_eq_native (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) (t width : Nat) :
    Execution.preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey
      (Sampling.Native.runtimeLayout t width) ctx.canonicalFreshKey_fresh
      (freshDisjoint ctx noQuantum t width) (input_systemCount ctx noQuantum) =
    Execution.basisOfEqualWires (Sampling.Native.runtimeLayout t width)
      (preparedContext ctx noQuantum t width).quantumLayout
      (prepared_wires ctx noQuantum t width) := by
  apply Equiv.ext
  intro basis
  exact Execution.preparedEmptyBasisEquiv_eq_basisOfEqualWires
    ctx ctx.canonicalFreshKey (Sampling.Native.runtimeLayout t width)
    ctx.canonicalFreshKey_fresh (freshDisjoint ctx noQuantum t width)
    (input_systemCount ctx noQuantum) (prepared_wires ctx noQuantum t width) basis

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
