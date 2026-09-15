/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Execution
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
import all QuantumAlg.Core.Execution.Borrowed.Classical.Reference
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Complete classical-input and reference restoration by actual order sampling

The actual preparation, original source unitary, allocations, Z writes and
packing preserve the caller's complete classical-reference observation. Every
supported classical block participates; no independence or singleton input
premise is needed. All newly allocated systems remain in complete Output.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

include noQuantum in
theorem input_noBorrowedQuantum : ctx.borrowedQuantumWires = [] := by
  have subset := ctx.borrowedQuantumWires_sublist
  rw [noQuantum] at subset
  exact List.sublist_nil.mp subset

theorem prepared_noBorrowedQuantum (t n : Nat) :
    (preparedContext ctx noQuantum t n).borrowedQuantumWires = [] :=
  (preparationCode ctx noQuantum t n).borrowedQuantumWires_preserved.trans
    (input_noBorrowedQuantum ctx noQuantum)

theorem post_noBorrowedQuantum (t n : Nat) :
    (post ctx noQuantum t n).borrowedQuantumWires = [] :=
  (allocationCode ctx noQuantum t n).borrowedQuantumWires_preserved.trans
    (prepared_noBorrowedQuantum ctx noQuantum t n)

theorem preparationCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    (preparationCode ctx noQuantum t n).BorrowedRestored Reference state
      ((preparationCode ctx noQuantum t n).execute Reference state) :=
  Circuit.borrowedRestored_prepare state ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n) (inputPreparation t n)

theorem allocationCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext ctx noQuantum t n) Reference H) :
    (allocationCode ctx noQuantum t n).BorrowedRestored Reference state
      ((allocationCode ctx noQuantum t n).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_retain (preparedContext ctx noQuantum t n).canonicalFreshKey
      (.bits t) (preparedContext ctx noQuantum t n).canonicalFreshKey_fresh state)
    (MeasurementCells.allocate_borrowedRestored (resultContext ctx noQuantum t n) 2 t _)

/-- Every real source sample restores the original classical input and its complete reference. -/
theorem code_borrowedRestored {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    (code ctx noQuantum A).BorrowedRestored Reference state
      ((code ctx noQuantum A).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_seq _ _ state
      (preparationCode_borrowedRestored ctx noQuantum t n state)
      (Circuit.borrowedRestored_seq _ _ _
        (Circuit.borrowedRestored_unitary_classicalReference
          (prepared_noBorrowedQuantum ctx noQuantum t n)
          (nativeProgram ctx noQuantum A) (nativeProgram_placement ctx noQuantum A) _)
        (allocationCode_borrowedRestored ctx noQuantum t n _)))
    (Circuit.borrowedRestored_seq _ _ _
      (Circuit.borrowedRestored_measurementSequence_classicalReference
        (post_noBorrowedQuantum ctx noQuantum t n) (readouts ctx noQuantum t n) _)
      (Circuit.borrowedRestored_classical (packing ctx noQuantum t n) _))

end

end QuantumAlg.OrderFinding.Sampling.Framed
