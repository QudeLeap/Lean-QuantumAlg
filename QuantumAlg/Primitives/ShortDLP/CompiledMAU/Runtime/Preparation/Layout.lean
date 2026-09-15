/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Bank
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Placement

/-!
# The first actual preparation and later rounds use the same physical basis

The preparation interpreter appends the source bank to an empty incoming
quantum layout. Later rounds identify the existing bank by its ordered wire
records. The equality below connects these two actual constructions by the
finite value on every corresponding physical wire, not by basis cardinality.

The absence of an earlier quantum bank is used only at this first allocation
boundary. Repeated rounds keep this already allocated bank.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank

noncomputable section

open Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])
  (m ell width : Nat)

private theorem prepared_wire_value (basis : (runtimeLayout m ell width).register.Index)
    (index : Fin (totalQubits (registerParameters m ell width))) :
    (preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
      ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)
      (input_systemCount ctx noQuantum) basis
      (RuntimePlacement.wireEquiv m ell width
        (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width) index)).val =
      (basis index).val := by
  let layout := runtimeLayout m ell width
  let disjoint := allocationDisjoint ctx noQuantum m ell width
  let joined := QuantumLayout.appendJoinBasis layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint)
    basis (emptyContextBasis ctx (input_systemCount ctx noQuantum))
  let assembled := ctx.addOwnedLayoutBasisEquiv ctx.canonicalFreshKey layout
    ctx.canonicalFreshKey_fresh disjoint joined
  have position :
      ctx.addOwnedLayoutPositionEquiv ctx.canonicalFreshKey layout
          ctx.canonicalFreshKey_fresh disjoint (Fin.castAdd ctx.systemCount index) =
        RuntimePlacement.wireEquiv m ell width
          (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width) index := by
    apply Fin.ext
    rfl
  have assembledValue := RuntimeCtx.addOwnedLayout_basis_value_preserved
    ctx ctx.canonicalFreshKey layout ctx.canonicalFreshKey_fresh disjoint
    joined (Fin.castAdd ctx.systemCount index)
  have sourceValue := QuantumLayout.appendJoinBasis_left_value layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint)
    basis (emptyContextBasis ctx (input_systemCount ctx noQuantum)) index
  change (assembled (RuntimePlacement.wireEquiv m ell width
    (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width) index)).val = _
  exact (congrArg (fun wire => (assembled wire).val) position.symm).trans
    (assembledValue.trans sourceValue)

/-- The preparation and reused bank represent exactly the same local physical basis. -/
theorem shortDLP_runtimePrepared_basis (basis : (runtimeLayout m ell width).register.Index) :
    preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
        ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)
        (input_systemCount ctx noQuantum) basis =
      (RuntimePlacement.basisEquiv m ell width
        (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width)).symm
          ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv basis) := by
  let wires := RuntimePlacement.layoutWires m ell width
    (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width)
  let corresponding := basisOfEqualWires (runtimeLayout m ell width)
    (context ctx noQuantum m ell width).quantumLayout wires
  have physical :
      preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
        ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)
        (input_systemCount ctx noQuantum) basis = corresponding basis := by
    funext wire
    obtain ⟨index, rfl⟩ := (RuntimePlacement.wireEquiv m ell width
      (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width)).surjective wire
    apply Fin.ext
    exact (prepared_wire_value ctx noQuantum m ell width basis index).trans
      (basisOfEqualWires_value (runtimeLayout m ell width)
        (context ctx noQuantum m ell width).quantumLayout wires basis index).symm
  change _ = corresponding
    ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm
      ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv basis))
  exact physical.trans (congrArg corresponding
    ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm_apply_apply
      basis).symm)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank
