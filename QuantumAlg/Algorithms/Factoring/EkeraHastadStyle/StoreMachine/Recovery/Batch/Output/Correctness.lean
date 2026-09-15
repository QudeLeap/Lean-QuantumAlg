/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Program

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Actual resize and packing produce the exact selected optional value and caller frame. -/
theorem into_correct (refs : Refs ctx N) (separated : Separation refs) (store : Store ctx) :
    Relation refs store (step refs store).1 := by
  let middle := store.applyOp (resizeOp refs)
  have acceptedFrame : middle.read (FirstAccepted.cellRead refs.selection.accepted) =
      store.read (FirstAccepted.cellRead refs.selection.accepted) :=
    Store.read_applyOp_of_not_mem_storageKeys store (resizeOp refs) _
      separated.acceptedAvoidsNarrow
  have resized : middle.read (FirstAccepted.cellRead refs.narrow) =
      CShape.wordResize (modulusBits N)
        (store.read (FirstAccepted.cellRead refs.selection.selected)) :=
    Store.read_applyOp_output store (resizeOp refs)
  refine ⟨?_, into_callerFrame refs store⟩
  calc
    (step refs store).1.read (FirstAccepted.cellRead refs.result) =
        CShape.packOption (middle.read (.product
          (FirstAccepted.cellRead refs.selection.accepted)
          (FirstAccepted.cellRead refs.narrow))) :=
      Store.read_applyOp_output middle (packOp refs)
    _ = outputValue (QuadraticCandidateSelect.selectedOption refs.selection store) := by
      change CShape.packOption (.product
        (middle.read (FirstAccepted.cellRead refs.selection.accepted))
        (middle.read (FirstAccepted.cellRead refs.narrow))) = _
      rw [acceptedFrame, resized]
      cases acceptedValue : store.read (FirstAccepted.cellRead refs.selection.accepted) with
      | bit accepted =>
        cases accepted <;>
          simp [outputValue, QuadraticCandidateSelect.selectedOption,
            FirstAccepted.selectedOption, acceptedValue, CShape.wordResize,
            CShape.Value.toBool, CShape.packOption]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput
