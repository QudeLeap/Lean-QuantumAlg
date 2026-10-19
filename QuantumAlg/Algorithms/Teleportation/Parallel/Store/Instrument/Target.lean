/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument.Input
import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument.Weight
import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument.Physical
import all QuantumAlg.Algorithms.Teleportation.Parallel.Target.Sandwich
import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument
import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource.Insertion
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction

/-!
# The actual recorded full-store branch has the independent joint target

The original local Bell promise alone implies the complete target for every
actual measured store [dW19, qcnotes.tex:785,790,802,804,809]. All Alice and
Bob systems and both external-reference coordinates remain present. The
original store may be correlated with that joint quantum input.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument

noncomputable section

open Execution BellInsertion PhysicalInstrument

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The actual measured branch has its complete original-input-dependent target and real weight. -/
lemma code_store_target_entry
    (environment : model.Environment) (count : Nat) {Reference : Register}
    (input : OracleInput .empty (context count) Reference)
    (admitted : localBellMarginal count input.caller.localState.quantumMarginal =
      DensityOperator.ofPure (bellBank count)) (stored : Store (context count))
    (row column : (context count).register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      (((code count).execute environment) Reference
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))))
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (row, leftRef) (column, rightRef) =
      ((1 / 4 : Real) ^ count) •
        (Target.target count input.caller (stored.read (resultInput count))).matrix
          (row, leftRef) (column, rightRef) := by
  let recorded : State (context count) Reference (model.HiddenState × Store (context count)) :=
    input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have promised : localBellMarginal count recorded.quantumMarginal.marginalLeft =
      DensityOperator.ofPure (bellBank count) := recorded_bellPromise count input admitted
  have inserted := conjugation_eq_inserted count recorded.quantumMarginal promised
    (actualInstrument environment count stored) leftRef rightRef
  have weighted := retained_branch_weight count (retainedPhysicalInsertion count stored)
    (inputReferenceSlice count recorded.quantumMarginal leftRef rightRef)
  rw [actualInstrument_insert_eq] at inserted
  have instrument := code_store_instrument_entry environment count recorded stored row column
    leftRef rightRef
  have complete := instrument.trans
    (congrArg (fun matrix : HilbertOperator (context count).register => matrix row column)
      (inserted.trans weighted))
  have original : recorded.quantumMarginal = input.caller.state.quantumMarginal :=
    recorded_quantumMarginal count input
  rw [original, Matrix.smul_apply,
    Target.retained_sandwich_target_entry count input.caller stored row column leftRef rightRef]
      at complete
  exact complete

end

end QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument
