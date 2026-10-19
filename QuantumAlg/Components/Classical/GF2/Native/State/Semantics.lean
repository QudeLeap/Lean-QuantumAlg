/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State
import all QuantumAlg.Components.Classical.GF2.Native.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Record

/-!
# Complete actual records of the original seven-cell recovery workspace

The existing lexical allocator composes actual push/pop records around the
proved native body. Its fresh cells establish their initial encodings inside
the actual execution. Complete caller-store, reference and history correlations
remain in that same record without imposing a caller initialization premise.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution ClassicalWorkspace

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {environment : model.Environment}
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- Real lexical allocation and release wrap the same actual full-state recovery record. -/
lemma gf2WithState_actualRecord
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ∃ record : Store ctx × model.HiddenState →
        (Store ctx × model.HiddenState) × (withState input output).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withState (model := model) input output).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply ClassicalWorkspace.withCellsFrom_hasRecord environment (Transport.id ctx)
    (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)
  intro inner cells _distinct transport _separated
  exact ⟨Circuit.preserveHiddenRecord (model := model) (intoStep (transport.liftInput input)
      cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output)),
    gf2Into_execute (model := model) (transport.liftInput input)
    cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output)⟩

end

end QuantumAlg.ClassicalRoutines.GF2.Native
