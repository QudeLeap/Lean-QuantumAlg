/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Preparation.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Basis.Seeded.Unitary
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# The first actual bank preparation establishes the complete seed invariant

Actual zero allocation establishes complete store-reference support at the
physical zero label. The literal X loading word transports that support to
the source seed. Both steps use the common intrinsic basis-support lemmas;
their real execution paths and hidden service state remain in the output.

No normalization, particular classical value or independent reference is
assumed. Later rounds reuse this same initially allocated owned bank.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])
  (m ell width : Nat)

/-- Actual zero allocation and literal loading establish every complete seed block. -/
theorem shortDLP_runtimePrepare_seedBlocks (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks m ell width
      (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width) N
      ((prepare (operations := BitWord.model) (services := .empty)
        ctx noQuantum m ell width N).execute Reference state) := by
  let bank := context ctx noQuantum m ell width
  let wires := shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width
  let allocated := allocateZero (operations := BitWord.model) (services := .empty)
    ctx noQuantum m ell width
  let seed := (RuntimePlacement.basisEquiv m ell width wires).symm
    (CompiledMAU.reloadLabel m ell width N)
  have initialZero :
      preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
        ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)
        (input_systemCount ctx noQuantum)
        (BasisPreparation.zero (runtimeLayout m ell width)).value =
        bank.quantumLayout.zeroLabel := by
    rw [shortDLP_runtimePrepared_basis]
    change (RuntimePlacement.basisEquiv m ell width wires).symm
      ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv
        (runtimeLayout m ell width).zeroLabel) = _
    rw [← shortDLP_runtimeLayout_zeroBasis, Equiv.apply_symm_apply]
    exact RuntimePlacement.shortDLP_runtimeBasis_zero m ell width wires
  have zeroBlocks : BasisSeeded.Holds bank.quantumLayout.zeroLabel
      (allocated.execute Reference state) := by
    have established := Circuit.prepareZero_empty_seeded
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (services := .empty)
      ctx.canonicalFreshKey (runtimeLayout m ell width) ctx.canonicalFreshKey_fresh
      (allocationDisjoint ctx noQuantum m ell width) (input_systemCount ctx noQuantum) state
    rw [initialZero] at established
    exact established
  have loading : (loadProgram ctx noQuantum m ell width N).applyNormalized
      (NormalizedVector.ket bank.quantumLayout.zeroLabel) = NormalizedVector.ket seed :=
    RuntimePlacement.shortDLP_runtimeReload_apply_zero m ell width wires N
  exact BasisSeeded.seq allocated
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (loadProgram ctx noQuantum m ell width N)) seed state
    (BasisSeeded.unitary (operations := BitWord.model) (services := .empty)
      (loadProgram ctx noQuantum m ell width N) bank.quantumLayout.zeroLabel seed
      loading (allocated.execute Reference state) zeroBlocks)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank
