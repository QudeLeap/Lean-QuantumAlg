/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Core.Execution.Basis.Seeded.Record
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Fixed seed in every actual reset and round record

The complete-store seed invariant implies the same pure seed after conditioning
on each hidden service state, incoming history and actual execution path.
Positivity excludes cancellation between the records that the store invariant
sums together. Every block keeps its own probability mass, including zero.

The seed is the original fixed reload label, which may be nonzero. These state
facts do not claim that the caller has finished its independent cycle protocol.
Borrowed restoration is established separately for the owned-bank interface.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma selectedSeed_promise {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds seed state) (label : Store ctx × History)
    (selection : Finset (Fin ctx.systemCount)) :
    (StatePromise.pure (NormalizedVector.ket
      (ctx.quantumLayout.restrictSelectedBasis selection seed))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout selection Reference
        (state.block label)) := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.observeSelection_entry]
  apply Finset.sum_eq_zero
  intro reference _
  apply Finset.sum_eq_zero
  intro complement _
  apply BasisSeeded.block_entry_zero seed state seeded label _ _ reference reference
  intro supported
  apply different
  funext wire
  exact (ctx.quantumLayout.joinSelectedBasis_selected_value
    selection row complement wire).symm.trans
    (congrFun supported.1 wire.val)

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Each reset/reload record has the fixed seed, even when its full history is observed. -/
lemma shortDLP_runtimeResetReload_recordSeed (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (label : Store ctx ×
      (model.HiddenState × (History × (resetReload m ell width sameWires N).Path)))
    (selection : Finset (Fin ctx.systemCount)) :
    (StatePromise.pure (NormalizedVector.ket
      (ctx.quantumLayout.restrictSelectedBasis selection
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N))))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout selection Reference
        (((resetReload m ell width sameWires N).execute
          environment Reference state).block label)) :=
  selectedSeed_promise _ _ (shortDLP_runtimeResetReload_seedBlocks
    m ell width sameWires N state) label selection

/-- Every actual round record reinitializes any selected owned wires to the fixed source seed. -/
lemma shortDLP_runtimeRound_recordSeed {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (label : Store ctx × (model.HiddenState × (History ×
      (code m ell width sameWires parameter N generator target cells result).Path)))
    (selection : Finset (Fin ctx.systemCount)) :
    (StatePromise.pure (NormalizedVector.ket
      (ctx.quantumLayout.restrictSelectedBasis selection
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N))))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout selection Reference
        (((code m ell width sameWires parameter N generator target cells result).execute environment
          Reference state).block label)) :=
  selectedSeed_promise _ _ (shortDLP_runtimeRound_seedBlocks
    m ell width sameWires parameter N generator target cells result state) label selection

-- The general restoration theorem treats the actual circuit as a typed parameter.
-- Its proof does not require expansion of the member program or dependent path tree.
attribute [local irreducible] code

/-- On the actual owned bank, the round restores the entire borrowed classical/reference view. -/
lemma shortDLP_runtimeRound_borrowedRestored {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (noBorrowed : ctx.borrowedQuantumWires = [])
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code m ell width sameWires parameter N generator target cells result).BorrowedRestored
      Reference state
      ((code m ell width sameWires parameter N generator target cells result).execute environment
        Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment)
    (model := model) (pre := ctx) (post := ctx)
    (code m ell width sameWires parameter N generator target cells result)
    noBorrowed Reference (History := History) state

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
