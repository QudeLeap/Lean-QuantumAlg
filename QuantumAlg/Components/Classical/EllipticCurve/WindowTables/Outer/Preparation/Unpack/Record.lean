/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Unpack
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Right-associated complete record for the actual two unpack leaves

The two selected native leaves are followed by an arbitrary real continuation
in the exact right-associated order used by signed-row preparation. A proved
record for that continuation composes without changing the circuit tree or
the type and order of its actual paths.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original right-associated order: first unpack, second unpack, continuation. -/
def twoUnpackThen (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (tail : Circuit model ctx ctx) : Circuit model ctx ctx :=
  .seq
    (BitWord.instruction (execution := model)
      (.unpackEllipticCurvePoint width ctx base rawBase))
    (.seq
      (BitWord.instruction (execution := model)
        (.unpackEllipticCurvePoint width ctx target rawTarget))
      tail)

/-- The actual two native updates feed the continuation on their returned
Store and hidden state, retaining the right-associated three-part Path. -/
def twoUnpackThenRecord
    (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (tail : Circuit model ctx ctx)
    (tailStep : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × tail.Path)
    (before : Store ctx × model.HiddenState) :
    (Store ctx × model.HiddenState) ×
      (twoUnpackThen (model := model) base target rawBase rawTarget tail).Path :=
  Circuit.sequenceRecord
    (BitWord.instruction (execution := model)
      (.unpackEllipticCurvePoint width ctx base rawBase))
    (.seq
      (BitWord.instruction (execution := model)
        (.unpackEllipticCurvePoint width ctx target rawTarget))
      tail)
    (Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
      (.unpackEllipticCurvePoint width ctx base rawBase)))
    (Circuit.sequenceRecord
      (BitWord.instruction (execution := model)
        (.unpackEllipticCurvePoint width ctx target rawTarget))
      tail
      (Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
        (.unpackEllipticCurvePoint width ctx target rawTarget)))
      tailStep) before

/-- The continuation sees exactly the already proved two-unpack Store and
the original hidden state; no later tail write is credited to this prefix. -/
lemma twoUnpackThenRecord_state
    (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (tail : Circuit model ctx ctx)
    (tailStep : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × tail.Path)
    (before : Store ctx × model.HiddenState) :
    (twoUnpackThenRecord (model := model) base target rawBase rawTarget
      tail tailStep before).1 =
      (tailStep (twoUnpackStore base target rawBase rawTarget before.1, before.2)).1 := by
  rfl

/-- A proved real continuation composes with both selected unpack leaves on
every complete State, Reference and incoming History, preserving all blocks. -/
lemma twoUnpackThen_execute
    (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (tail : Circuit model ctx ctx)
    (environment : model.Environment)
    (tailStep : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × tail.Path)
    (tailEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      tail.execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := tailStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (twoUnpackThen (model := model) base target rawBase rawTarget tail).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := twoUnpackThenRecord (model := model) base target rawBase rawTarget
          tail tailStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  unfold twoUnpackThen twoUnpackThenRecord
  apply Circuit.execute_sequenceRecord
  · intro reference history _ initial
    exact (BitWord.bitWord_instruction_execute (environment := environment)
      (execution := model) (.unpackEllipticCurvePoint width ctx base rawBase) initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · apply Circuit.execute_sequenceRecord
    · intro reference history _ initial
      exact (BitWord.bitWord_instruction_execute (environment := environment)
        (execution := model) (.unpackEllipticCurvePoint width ctx target rawTarget) initial).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
    · exact tailEquation

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation
