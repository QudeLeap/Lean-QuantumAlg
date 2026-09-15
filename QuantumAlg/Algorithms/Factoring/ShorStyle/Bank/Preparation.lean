/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Placement
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Preparation.Seed

/-!
# The single actual Shor bank preparation supplies every later round's seed

The first allocation's tensor coordinates coincide with the same physical
wire correspondence used by all later rounds. Its declared basis value is
therefore precisely the zero-phase, unit-power and zero-auxiliary seed.
The actual preparation establishes this in every complete store-reference
block without restricting old classical values or their reference correlations.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeBank

noncomputable section

open Execution NativeQuantum

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = []) (N : Nat)

/-- The first actual tensor assembly and every later bank member use identical physical values. -/
theorem prepared_basis (basis : (runtimeLayout N).register.Index) :
    preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout N)
        ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum N)
        (input_systemCount ctx noQuantum) basis =
      (NativePlacement.basisEquiv N (quantumWires ctx noQuantum N)).symm
        ((OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv
          basis) := by
  let wires := NativePlacement.layoutWires N (quantumWires ctx noQuantum N)
  let corresponding := basisOfEqualWires (runtimeLayout N)
    (context ctx noQuantum N).quantumLayout wires
  have physical := preparedEmptyBasisEquiv_eq_basisOfEqualWires
    ctx ctx.canonicalFreshKey (runtimeLayout N) ctx.canonicalFreshKey_fresh
    (allocationDisjoint ctx noQuantum N) (input_systemCount ctx noQuantum) wires basis
  change _ = corresponding
    ((OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv.symm
      ((OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv basis))
  exact physical.trans (congrArg corresponding
    (Equiv.symm_apply_apply
      (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv
      basis).symm)

/-- The real single preparation establishes the same seed used by every actual selected member. -/
theorem prepare_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N (quantumWires ctx noQuantum N)).symm (seedLabel N))
      ((prepare ctx noQuantum N).execute Reference state) := by
  have seed :
      preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout N)
        ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum N)
        (input_systemCount ctx noQuantum) (seedPreparation N).value =
      (NativePlacement.basisEquiv N (quantumWires ctx noQuantum N)).symm (seedLabel N) :=
    (prepared_basis ctx noQuantum N (seedPreparation N).value).trans
      (congrArg (NativePlacement.basisEquiv N (quantumWires ctx noQuantum N)).symm
        (Equiv.apply_symm_apply
          (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv
          (seedLabel N)))
  have actual := Circuit.prepare_empty_seeded ctx.canonicalFreshKey (runtimeLayout N)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum N) (seedPreparation N)
    (input_systemCount ctx noQuantum) state
  exact (congrArg
    (fun value => BasisSeeded.Holds value ((prepare ctx noQuantum N).execute Reference state))
    seed).mp actual

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeBank
