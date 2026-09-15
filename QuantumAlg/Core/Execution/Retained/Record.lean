/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Retained.Composition
import all QuantumAlg.Core.Execution.MappedTail

/-!
# Complete deterministic records for actual retained continuations

These propositions state equations of the existing interpreter. Abstract
circuit and context parameters keep their finite state carriers independent
of the size of an instantiated algorithm. Each equation retains all store
blocks, paths, histories and arbitrary external-reference correlations.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {pre middle : RuntimeCtx kind}
  {key : StorageKey} {shape : CShape} {fresh : key ∉ middle.keys}

/-- A real retained continuation deterministically maps every complete incoming store block. -/
def RetainedRecord
    (code : Circuit middle (middle.addRetained key shape fresh))
    (step : Store middle → Store (middle.addRetained key shape fresh) × code.Path) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State middle Reference History),
    code.execute Reference state = state.mapClassical
      (D := Store (middle.addRetained key shape fresh) × (History × code.Path))
      (fun entry => ((step entry.1).1, (entry.2, (step entry.1).2)))

/-- A retained tail maps the actual source blocks and keeps both real execution paths. -/
def RetainedTailRecord (first : Circuit pre middle)
    (second : Circuit middle (middle.addRetained key shape fresh))
    (step : Store middle → Store (middle.addRetained key shape fresh) × second.Path) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference History),
    (Circuit.seq first second).execute Reference state =
      (first.execute Reference state).mapClassical
        (D := Store (middle.addRetained key shape fresh) ×
          (History × (Circuit.seq first second).Path))
        (fun entry => ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2))))

/-- Joint preservation covers the complete outgoing quantum register and arbitrary reference. -/
def RetainedQuantumPreserved
    (code : Circuit middle (middle.addRetained key shape fresh)) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State middle Reference History),
    (code.execute Reference state).quantumMarginal = state.quantumMarginal

/-- A classical retained tail preserves exactly the source's outgoing quantum-reference state. -/
def RetainedTailQuantumPreserved (first : Circuit pre middle)
    (second : Circuit middle (middle.addRetained key shape fresh)) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference History),
    ((Circuit.seq first second).execute Reference state).quantumMarginal =
      (first.execute Reference state).quantumMarginal

/-- The existing sequential interpreter law composes a proved complete retained record. -/
theorem RetainedRecord.after (first : Circuit pre middle)
    (second : Circuit middle (middle.addRetained key shape fresh))
    (step : Store middle → Store (middle.addRetained key shape fresh) × second.Path)
    (record : RetainedRecord second step) : RetainedTailRecord first second step := by
  intro Reference History historyFinite state
  refine (execute_seq_retained_mapClassical_tail key shape fresh first second step record
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The complete record equation entails joint quantum-reference marginal preservation. -/
theorem RetainedRecord.quantumPreserved
    (code : Circuit middle (middle.addRetained key shape fresh))
    (step : Store middle → Store (middle.addRetained key shape fresh) × code.Path)
    (record : RetainedRecord code step) : RetainedQuantumPreserved code := by
  intro Reference History historyFinite state
  exact (congrArg ExecutionState.quantumMarginal (record Reference state)).trans
    (ExecutionState.mapClassical_quantumMarginal state _)

/-- Keeping the actual source blocks also keeps their full joint quantum-reference marginal. -/
theorem RetainedTailRecord.quantumPreserved (first : Circuit pre middle)
    (second : Circuit middle (middle.addRetained key shape fresh))
    (step : Store middle → Store (middle.addRetained key shape fresh) × second.Path)
    (record : RetainedTailRecord first second step) :
    RetainedTailQuantumPreserved first second := by
  intro Reference History historyFinite state
  exact (congrArg ExecutionState.quantumMarginal (record Reference state)).trans
    (ExecutionState.mapClassical_quantumMarginal _ _)

end

end QuantumAlg.Circuit
