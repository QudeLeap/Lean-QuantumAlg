/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Promotion
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace

/-!
# Dependency depth under native bit/word selection

Model selection preserves the same sequential and parallel dependencies on
every original path. Arbitrary native durations are pulled back through the
actual event injection. This retains the critical path rather than replacing
it by a serial event-count bound.
-/

namespace QuantumAlg.BitWord

noncomputable section

open scoped BigOperators

private theorem unitaryDepth_lift {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {layout : QuantumLayout count}
    (program : UnitarySequence gates oracles layout)
    (duration : Resource.Event (.quantum gates oracles model) → Nat) :
    DepthExpr.depthEval duration (program.eventDepth model .empty) =
      DepthExpr.depthEval (duration ∘ liftQuantumEvent) (program.eventDepth .empty .empty) := by
  induction program with
  | id => rfl
  | leaf atom => cases atom <;> rfl
  | seq left right leftIH rightIH =>
      simp only [UnitarySequence.eventDepth, DepthExpr.depthEval_seq, leftIH, rightIH]
  | embed placement body bodyIH => exact bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp only [UnitarySequence.eventDepth, DepthExpr.depthEval_tensor, leftIH, rightIH]
  | iterate repetitions body bodyIH =>
      simp only [UnitarySequence.eventDepth, DepthExpr.depthEval_iterate, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp only [UnitarySequence.eventDepth, DepthExpr.depthEval_indexedProduct, startIH]
      exact congrArg (fun total => _ + total) (Finset.sum_congr rfl (fun index _ => stepIH index))
  | macroCall name body bodyIH => exact bodyIH

private theorem parallelDepth_map {A B : Type} (update : A → B) (duration : B → Nat)
    (events : List A) :
    DepthExpr.depthEval duration
        ((events.map update).foldr (fun event rest => .tensor (.atom event) rest) .id) =
      DepthExpr.depthEval (duration ∘ update)
        (events.foldr (fun event rest => .tensor (.atom event) rest) .id) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      simp only [List.map_cons, List.foldr_cons, DepthExpr.depthEval_tensor,
        DepthExpr.depthEval_atom, Function.comp_def, ih]

private theorem preparationDepth_lift (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (layout : QuantumLayout count)
    (duration : Resource.Event (.quantum gates oracles model) → Nat) :
    DepthExpr.depthEval duration (ZeroPreparation.eventDepth gates oracles layout model) =
      DepthExpr.depthEval (duration ∘ liftQuantumEvent)
        (ZeroPreparation.eventDepth gates oracles layout) := by
  simpa only [ZeroPreparation.eventDepth, ZeroPreparation.eventTrace,
    List.map_ofFn, liftQuantumEvent, Function.comp_def] using
      parallelDepth_map liftQuantumEvent duration
        (ZeroPreparation.eventTrace gates oracles layout)

private theorem selectForCircuitAux_depth {source : ExecutionModel}
    {pre post : RuntimeCtx source.kind} (code : Circuit source pre post) :
    ∀ {gates : GateModel} {oracles : OracleModel} (selected : source = .quantum gates oracles)
      (duration : Resource.Event (.quantum gates oracles model) → Nat) (path : code.Path),
      (selectForCircuitAux code selected).code.depth duration
          ((selectForCircuitAux code selected).paths path) =
        code.depth (duration ∘ selectedEvent selected) path := by
  induction code with
  | id ctx => intros gates oracles selected duration path; cases selected; rfl
  | classical application =>
      intro gates oracles selected duration path
      cases selected
      exact False.elim (nomatch application.token)
  | classicalQuery application =>
      intro gates oracles selected duration path
      cases selected
      exact False.elim (nomatch application.query)
  | unitary program =>
      intro gates oracles selected duration path
      cases selected
      exact unitaryDepth_lift program.sequence duration
  | measureZ wire output =>
      intros gates oracles selected duration path
      cases selected
      rfl
  | retain ctx key shape fresh =>
      intros gates oracles selected duration path
      cases selected
      rfl
  | prepareZero ctx key layout fresh disjoint =>
      intro gates oracles selected duration path
      cases selected
      exact preparationDepth_lift _ _ layout duration
  | @seq sourceModel sourcePre middle sourcePost first second firstIH secondIH =>
      intro gates oracles selected duration path
      cases selected
      let left := selectForCircuitAux first rfl
      let right := selectForCircuitAux second rfl
      change left.code.depth duration (left.paths path.1) +
        right.code.depth duration (right.paths path.2) =
        first.depth (duration ∘ liftQuantumEvent) path.1 +
          second.depth (duration ∘ liftQuantumEvent) path.2
      exact congrArg₂ Nat.add (firstIH rfl duration path.1) (secondIH rfl duration path.2)
  | branch input body bodyIH =>
      intro gates oracles selected duration path
      cases selected
      exact bodyIH path.1 rfl duration path.2
  | @iterate sourceModel ctx count body bodyIH =>
      intro gates oracles selected duration path
      cases selected
      let selectedBody := selectForCircuitAux body rfl
      change 0 + (∑ index, selectedBody.code.depth duration (selectedBody.paths (path index))) =
        0 + (∑ index, body.depth (duration ∘ liftQuantumEvent) (path index))
      exact congrArg (fun total => 0 + total)
        (Finset.sum_congr rfl (fun index _ => bodyIH rfl duration (path index)))
  | workspace ctx key shape fresh body bodyIH =>
      intro gates oracles selected duration path
      cases selected
      exact bodyIH rfl duration path

/-- Native selection preserves the complete critical path under every actual event duration. -/
theorem selectForCircuit_depth {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post)
    (duration : Resource.Event (.quantum gates oracles model) → Nat) (path : code.Path) :
    (selectForCircuit code).depth duration (selectForCircuitPathEquiv code path) =
      code.depth (duration ∘ liftQuantumEvent) path :=
  selectForCircuitAux_depth code rfl duration path

end

end QuantumAlg.BitWord
