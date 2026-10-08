/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Circuit.ModelSelection
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Select native bit/word operations beside a pure quantum circuit

An existing circuit with empty classical grants cannot execute a classical
instruction or query. Its quantum gates, measurements, allocations, branches
and execution order can therefore be retained verbatim when a surrounding
algorithm explicitly selects the bit/word native language for later stages.
-/

namespace QuantumAlg.BitWord

noncomputable section

private def selectedCtx {source : ExecutionModel} {gates : GateModel}
    {oracles : OracleModel} (selected : source = .quantum gates oracles)
    (ctx : RuntimeCtx source.kind) : RuntimeCtx .quantum := by
  cases selected
  exact ctx

/-- Embed a pure quantum event without changing its native coordinate. -/
def liftQuantumEvent {gates : GateModel} {oracles : OracleModel} :
    Resource.Event (.quantum gates oracles) →
      Resource.Event (.quantum gates oracles model)
  | .classicalOperation impossible => nomatch impossible
  | .classicalQuery impossible => nomatch impossible
  | .gate coordinate => .gate coordinate
  | .oracle coordinate => .oracle coordinate
  | .preparation dimension => .preparation dimension
  | .measurement dimension => .measurement dimension

/-- Embed the entire literal pure-quantum event ledger into the selected model. -/
def liftQuantumPool {gates : GateModel} {oracles : OracleModel}
    (pool : ResourcePool (.quantum gates oracles)) :
    ResourcePool (.quantum gates oracles model) :=
  pool.map liftQuantumEvent

/-- Selection leaves the total number of native quantum events unchanged. -/
@[simp] theorem liftQuantumPool_card {gates : GateModel} {oracles : OracleModel}
    (pool : ResourcePool (.quantum gates oracles)) :
    (liftQuantumPool pool).card = pool.card := by
  simp [liftQuantumPool]

/-- Every selected duration observes the original coordinates at the same weights. -/
theorem liftQuantumPool_weightedCount {gates : GateModel} {oracles : OracleModel}
    (duration : Resource.Event (.quantum gates oracles model) → Nat)
    (pool : ResourcePool (.quantum gates oracles)) :
    ResourcePool.weightedCount duration (liftQuantumPool pool) =
      ResourcePool.weightedCount (duration ∘ liftQuantumEvent) pool := by
  simp [ResourcePool.weightedCount, liftQuantumPool, Multiset.map_map]

private def selectedEvent {source : ExecutionModel} {gates : GateModel}
    {oracles : OracleModel} (selected : source = .quantum gates oracles) :
    Resource.Event source → Resource.Event (.quantum gates oracles model) := by
  cases selected
  exact liftQuantumEvent

private theorem unitaryEventTrace_lift {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {layout : QuantumLayout count}
    (program : UnitarySequence gates oracles layout) :
    program.eventTrace model .empty =
      (program.eventTrace .empty .empty).map liftQuantumEvent := by
  induction program with
  | id => rfl
  | leaf atom => cases atom <;> rfl
  | seq left right leftIH rightIH =>
      simp only [UnitarySequence.eventTrace, List.map_append, leftIH, rightIH]
  | embed placement body bodyIH => exact bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp only [UnitarySequence.eventTrace, List.map_append, leftIH, rightIH]
  | iterate repetitions body bodyIH =>
      simpa only [UnitarySequence.eventTrace, List.map_flatten, List.map_replicate]
        using congrArg (fun trace => (List.replicate repetitions trace).flatten) bodyIH
  | indexedProduct label steps start step startIH stepIH =>
      simp only [UnitarySequence.eventTrace, List.map_append, List.map_flatten, List.map_ofFn]
      exact congrArg₂ List.append startIH
        (congrArg List.flatten (congrArg List.ofFn
          (funext fun index => stepIH index)))
  | macroCall name body bodyIH => exact bodyIH

private theorem unitaryEventCount_independent {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {layout : QuantumLayout count}
    (program : UnitarySequence gates oracles layout)
    (firstOps secondOps : ClassicalOpModel)
    (firstQueries secondQueries : ClassicalOracleModel) :
    (program.eventTrace firstOps firstQueries).length =
      (program.eventTrace secondOps secondQueries).length := by
  induction program with
  | id | leaf => rfl
  | seq left right leftIH rightIH =>
      simp only [UnitarySequence.eventTrace, List.length_append]
      exact congrArg₂ Nat.add leftIH rightIH
  | embed placement body bodyIH =>
      exact bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp only [UnitarySequence.eventTrace, List.length_append]
      exact congrArg₂ Nat.add leftIH rightIH
  | iterate repetitions body bodyIH =>
      induction repetitions with
      | zero => rfl
      | succ repetitions inductionHypothesis =>
          simp only [UnitarySequence.eventTrace, List.replicate_succ,
            List.flatten_cons, List.length_append]
          exact congrArg₂ Nat.add bodyIH inductionHypothesis
  | indexedProduct label steps start step startIH stepIH =>
      simp only [UnitarySequence.eventTrace, List.length_append]
      congr 1
      simp only [List.length_flatten, List.map_ofFn]
      exact congrArg List.sum (congrArg List.ofFn (funext fun index => stepIH index))
  | macroCall name body bodyIH =>
      exact bodyIH

private structure SelectedCircuit {source : ExecutionModel}
    {pre post : RuntimeCtx source.kind} (original : Circuit source pre post)
    {gates : GateModel} {oracles : OracleModel}
    (selected : source = .quantum gates oracles) where
  code : Circuit (.quantum gates oracles model)
    (selectedCtx selected pre) (selectedCtx selected post)
  paths : original.Path ≃ code.Path
  preservesLocal : original.IsLocal → code.IsLocal
  eventCount : ∀ path : original.Path,
    (code.eventTrace (paths path)).length = (original.eventTrace path).length
  events : ∀ path : original.Path,
    code.eventTrace (paths path) =
      (original.eventTrace path).map (selectedEvent selected)
  visited : ∀ path : original.Path,
    HEq (code.visitedContexts (paths path)) (original.visitedContexts path)

private def selectForCircuitAux {source : ExecutionModel}
    {pre post : RuntimeCtx source.kind} (code : Circuit source pre post) :
    ∀ {gates : GateModel} {oracles : OracleModel}
      (selected : source = .quantum gates oracles), SelectedCircuit code selected := by
  induction code with
  | id ctx =>
      intro gates oracles selected
      cases selected
      exact ⟨Circuit.id (model := .quantum gates oracles model) ctx,
        Equiv.refl _, fun _ => trivial, fun _ => rfl, fun _ => rfl, fun _ => HEq.rfl⟩
  | classical application =>
      intro gates oracles selected
      cases selected
      exact False.elim (nomatch application.token)
  | classicalQuery application =>
      intro gates oracles selected
      cases selected
      exact False.elim (nomatch application.query)
  | unitary program =>
      intro gates oracles selected
      cases selected
      exact ⟨Circuit.unitary (operations := model) program,
        Equiv.refl _, fun _ => trivial,
        fun _ => unitaryEventCount_independent program.sequence model .empty .empty .empty,
        fun _ => unitaryEventTrace_lift program.sequence,
        fun _ => HEq.rfl⟩
  | measureZ wire output =>
      intro gates oracles selected
      cases selected
      exact ⟨Circuit.measureZ (operations := model) wire output,
        Equiv.refl _, fun _ => trivial, fun _ => rfl, fun _ => rfl, fun _ => HEq.rfl⟩
  | retain ctx key shape fresh =>
      intro gates oracles selected
      cases selected
      exact ⟨Circuit.retain (model := .quantum gates oracles model) ctx key shape fresh,
        Equiv.refl _, fun unsupported => False.elim unsupported, fun _ => rfl,
        fun _ => rfl,
        fun _ => HEq.rfl⟩
  | prepareZero ctx key layout fresh disjoint =>
      intro gates oracles selected
      cases selected
      exact ⟨Circuit.prepareZero (operations := model) ctx key layout fresh disjoint,
        Equiv.refl _, fun unsupported => False.elim unsupported,
        fun _ => by simp [Circuit.eventTrace, ZeroPreparation.eventTrace],
        fun _ => by
          simp only [Circuit.eventTrace, ZeroPreparation.eventTrace, List.map_ofFn]
          congr 1,
        fun _ => HEq.rfl⟩
  | seq first second firstIH secondIH =>
      intro gates oracles selected
      cases selected
      let left := firstIH rfl
      let right := secondIH rfl
      exact ⟨.seq left.code right.code,
        Equiv.prodCongr left.paths right.paths,
        fun supported => ⟨left.preservesLocal supported.1,
          right.preservesLocal supported.2⟩,
        fun path => by
          simpa [Circuit.eventTrace, Equiv.prodCongr] using
            congrArg₂ Nat.add (left.eventCount path.1) (right.eventCount path.2),
        fun path => by
          simpa [Circuit.eventTrace, Equiv.prodCongr, List.map_append,
            selectedEvent] using
            congrArg₂ List.append (left.events path.1) (right.events path.2),
        fun path => by
          simp only [Circuit.visitedContexts, Equiv.prodCongr]
          exact heq_of_eq (congrArg₂ List.append
            (eq_of_heq (left.visited path.1)) (eq_of_heq (right.visited path.2)))⟩
  | branch input body bodyIH =>
      intro gates oracles selected
      cases selected
      exact ⟨Circuit.branch input (fun value => (bodyIH value rfl).code),
        Equiv.sigmaCongrRight (fun value => (bodyIH value rfl).paths),
        fun supported value => (bodyIH value rfl).preservesLocal (supported value),
        fun path => (bodyIH path.1 rfl).eventCount path.2,
        fun path => (bodyIH path.1 rfl).events path.2,
        fun path => (bodyIH path.1 rfl).visited path.2⟩
  | iterate count body bodyIH =>
      intro gates oracles selected
      cases selected
      let selectedBody := bodyIH rfl
      exact ⟨.iterate count selectedBody.code,
        Equiv.piCongrRight (fun _ => selectedBody.paths),
        selectedBody.preservesLocal,
        fun path => by
          simp only [Circuit.eventTrace, List.length_flatten, List.map_ofFn]
          exact congrArg List.sum (congrArg List.ofFn
            (funext fun index => selectedBody.eventCount (path index))),
        fun path => by
          simp only [Circuit.eventTrace, List.map_flatten, List.map_ofFn]
          exact congrArg List.flatten (congrArg List.ofFn
            (funext fun index => selectedBody.events (path index))),
        fun path => by
          apply heq_of_eq
          simp only [Circuit.visitedContexts]
          congr 1
          exact congrArg List.flatten
            (congrArg List.ofFn
              (funext fun index => eq_of_heq (selectedBody.visited (path index))))⟩
  | workspace ctx key shape fresh body bodyIH =>
      intro gates oracles selected
      cases selected
      let selectedBody := bodyIH rfl
      exact ⟨Circuit.workspace (model := .quantum gates oracles model) ctx key shape fresh
        selectedBody.code, selectedBody.paths,
        fun unsupported => False.elim unsupported,
        fun path => selectedBody.eventCount path,
        fun path => selectedBody.events path,
        fun path => by
          simp only [Circuit.visitedContexts]
          congr! 2
          exact eq_of_heq (selectedBody.visited path)⟩

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem mapHistory_eta {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {S H P : Type} [Fintype S] [Fintype H] [Fintype P]
    (state : Execution.State ctx Reference (S × (H × P))) :
    state.mapHistory (fun record => (record.1, (record.2.1, record.2.2))) = state := by
  dsimp only [Execution.State.mapHistory]
  apply (ExecutionState.executionState_mapClassical_congr_decision state _ id
    (fun entry => by cases entry; rfl) _ _).trans
  exact ExecutionState.mapClassical_id state

private def selectedState {source : ExecutionModel} {gates : GateModel}
    {oracles : OracleModel} {ctx : RuntimeCtx source.kind} {Reference : Register}
    {H : Type} [Fintype H] (selected : source = .quantum gates oracles)
    (state : Execution.State ctx Reference (source.HiddenState × H)) :
    Execution.State (selectedCtx selected ctx) Reference
      ((.quantum gates oracles model : ExecutionModel).HiddenState × H) := by
  cases selected
  exact state

private theorem iterate_execution_transport {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum}
    (original : Circuit (.quantum gates oracles) ctx ctx)
    (selected : Circuit (.quantum gates oracles model) ctx ctx)
    (paths : original.Path ≃ selected.Path)
    (step : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : Execution.State ctx Reference
        ((.quantum gates oracles : ExecutionModel).HiddenState × H)),
      selected.execute Reference state =
        (original.execute Reference state).mapHistory (fun record =>
          (record.1, (record.2.1, paths record.2.2))))
    (count : Nat) (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State ctx Reference
      ((.quantum gates oracles : ExecutionModel).HiddenState × H)) :
    (Circuit.iterate count selected).execute Reference state =
      ((Circuit.iterate count original).execute Reference state).mapHistory
        (fun record => (record.1, (record.2.1,
          (Equiv.piCongrRight (fun _ => paths)) record.2.2))) := by
  induction count generalizing H with
  | zero =>
      rw [Circuit.execute_iterate_zero, Circuit.execute_iterate_zero]
      simp only [Execution.State.mapHistory_comp, Function.comp_def]
      apply ExecutionState.executionState_mapClassical_congr_decision
        state _ _ (fun entry => by
          congr 1
          exact congrArg (fun paths : Fin 0 → selected.Path =>
            (entry.2.1, (entry.2.2, paths))) (by
              funext index
              exact Fin.elim0 index)) _ _
  | succ count ih =>
      rw [Circuit.execute_iterate_succ, Circuit.execute_iterate_succ]
      rw [step Reference state]
      have natural : (Circuit.iterate count selected).execute Reference
          ((original.execute Reference state).mapHistory
            (fun record => (record.1, (record.2.1, paths record.2.2)))) =
          ((Circuit.iterate count selected).execute Reference
            (original.execute Reference state)).mapHistory
              (fun record =>
                (record.1, ((record.2.1.1, paths record.2.1.2), record.2.2))) := by
        exact Circuit.execute_mapHistory (Circuit.iterate count selected) Reference
          (original.execute Reference state) (fun history => (history.1, paths history.2))
      rw [natural]
      rw [ih (original.execute Reference state)]
      simp only [Execution.State.mapHistory_comp, Function.comp_def]
      apply ExecutionState.executionState_mapClassical_congr_decision
        ((Circuit.iterate count original).execute Reference (original.execute Reference state))
        _ _ (fun entry => by
          simp only [Prod.mk.injEq, true_and]
          funext index
          refine Fin.cases ?_ (fun i => ?_) index <;> rfl) _ _

private theorem selectForCircuitAux_execute {source : ExecutionModel}
    {pre post : RuntimeCtx source.kind} (code : Circuit source pre post) :
    ∀ {gates : GateModel} {oracles : OracleModel}
      (selected : source = .quantum gates oracles) (Reference : Register)
      {H : Type} [Fintype H]
      (state : Execution.State pre Reference (source.HiddenState × H)),
      ((selectForCircuitAux code selected).code.execute Reference
        (selectedState selected state)) =
      selectedState selected ((code.execute Reference state).mapHistory (fun record =>
        (record.1, (record.2.1, (selectForCircuitAux code selected).paths record.2.2)))) := by
  induction code with
  | id ctx =>
      intro gates oracles selected Reference H _ state
      cases selected
      change (Circuit.id (model := .quantum gates oracles model) ctx).execute
          Reference state =
        ((Circuit.id (model := .quantum gates oracles) ctx).execute Reference state).mapHistory
          (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | classical application =>
      intro gates oracles selected Reference H _ state
      cases selected
      exact False.elim (nomatch application.token)
  | classicalQuery application =>
      intro gates oracles selected Reference H _ state
      cases selected
      exact False.elim (nomatch application.query)
  | unitary program =>
      intro gates oracles selected Reference H _ state
      cases selected
      change (Circuit.unitary (operations := model) program).execute Reference state =
        ((Circuit.unitary (operations := .empty) program).execute Reference state).mapHistory
          (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | @measureZ gateModel oracleModel actualCtx operations services wire output =>
      intro gates oracles selected Reference H _ state
      cases selected
      change (Circuit.measureZ (gates := gateModel) (oracles := oracleModel)
          (operations := model) wire output).execute Reference state =
        ((Circuit.measureZ (gates := gateModel) (oracles := oracleModel)
          (operations := .empty) wire output).execute Reference state).mapHistory
          (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | retain ctx key shape fresh =>
      intro gates oracles selected Reference H _ state
      cases selected
      change (Circuit.retain (model := .quantum gates oracles model) ctx key shape fresh).execute
          Reference state =
        ((Circuit.retain (model := .quantum gates oracles) ctx key shape fresh).execute
          Reference state).mapHistory (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | @prepareZero gateModel oracleModel operations services ctx key systemCount layout
      fresh disjoint =>
      intro gates oracles selected Reference H _ state
      cases selected
      change (Circuit.prepareZero (gates := gateModel) (oracles := oracleModel)
          (operations := model) ctx key layout fresh disjoint).execute
          Reference state =
        ((Circuit.prepareZero (gates := gateModel) (oracles := oracleModel)
          (operations := .empty) ctx key layout fresh disjoint).execute
          Reference state).mapHistory (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | @seq sourceModel sourcePre middle sourcePost first second firstIH secondIH =>
      intro gates oracles selected Reference H _ state
      cases selected
      let leftCode : Circuit (.quantum gates oracles model) sourcePre middle :=
        (selectForCircuitAux first rfl).code
      let rightCode : Circuit (.quantum gates oracles model) middle sourcePost :=
        (selectForCircuitAux second rfl).code
      let leftPaths : first.Path ≃ leftCode.Path := (selectForCircuitAux first rfl).paths
      let rightPaths : second.Path ≃ rightCode.Path := (selectForCircuitAux second rfl).paths
      change (leftCode.seq rightCode).execute Reference state =
        ((first.seq second).execute Reference state).mapHistory (fun record =>
          (record.1, (record.2.1,
            (Equiv.prodCongr leftPaths rightPaths) record.2.2)))
      have leftEq : leftCode.execute Reference state =
          (first.execute Reference state).mapHistory (fun record =>
            (record.1, (record.2.1, leftPaths record.2.2))) := by
        exact firstIH rfl Reference state
      have rightEq : rightCode.execute Reference (first.execute Reference state) =
          (second.execute Reference (first.execute Reference state)).mapHistory
            (fun record => (record.1, (record.2.1, rightPaths record.2.2))) := by
        exact secondIH rfl Reference (first.execute Reference state)
      simp only [Circuit.execute_seq]
      rw [leftEq]
      have natural : rightCode.execute Reference
          ((first.execute Reference state).mapHistory (fun record =>
            (record.1, (record.2.1, leftPaths record.2.2)))) =
          (rightCode.execute Reference (first.execute Reference state)).mapHistory
            (fun record =>
              (record.1, ((record.2.1.1, leftPaths record.2.1.2), record.2.2))) := by
        exact Circuit.execute_mapHistory rightCode Reference (first.execute Reference state)
          (fun history => (history.1, leftPaths history.2))
      rw [natural]
      rw [rightEq]
      simp only [Execution.State.mapHistory_comp, Function.comp_def]
      rfl
  | @branch sourceModel sourcePre sourcePost shape input body bodyIH =>
      intro gates oracles selected Reference H _ state
      cases selected
      let compiled (value) : Circuit (.quantum gates oracles model) sourcePre sourcePost :=
        (selectForCircuitAux (body value) rfl).code
      let pathMap (value) : (body value).Path ≃ (compiled value).Path :=
        (selectForCircuitAux (body value) rfl).paths
      let branchPaths : (Circuit.branch input body).Path ≃
          (Circuit.branch (model := .quantum gates oracles model) input compiled).Path :=
        Equiv.sigmaCongrRight pathMap
      let resultMap :
          ((.quantum gates oracles : ExecutionModel).HiddenState ×
            (H × (Circuit.branch input body).Path)) →
          ((.quantum gates oracles model : ExecutionModel).HiddenState ×
            (H × (Circuit.branch (model := .quantum gates oracles model) input compiled).Path)) :=
        fun record => (record.1, (record.2.1, branchPaths record.2.2))
      let originalParts (value) : Execution.State _ Reference
          ((.quantum gates oracles : ExecutionModel).HiddenState ×
            (H × (Circuit.branch input body).Path)) :=
        ((body value).execute Reference
          (state.selectClassical (fun record => record.1.read input) value)).mapHistory
            (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
      let compiledParts (value) : Execution.State _ Reference
          ((.quantum gates oracles model : ExecutionModel).HiddenState ×
            (H × (Circuit.branch (model := .quantum gates oracles model) input compiled).Path)) :=
        ((compiled value).execute Reference
          (state.selectClassical (fun record => record.1.read input) value)).mapHistory
            (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
      have partEq (value) : compiledParts value =
          (originalParts value).mapHistory resultMap := by
        have actual : (compiled value).execute Reference
            (state.selectClassical (fun record => record.1.read input) value) =
          ((body value).execute Reference
            (state.selectClassical (fun record => record.1.read input) value)).mapHistory
              (fun record => (record.1, (record.2.1,
                pathMap value record.2.2))) := by
          exact bodyIH value rfl Reference
            (state.selectClassical (fun record => record.1.read input) value)
        dsimp only [compiledParts, originalParts]
        rw [actual]
        dsimp only [Execution.State.mapHistory]
        conv_lhs => rw [ExecutionState.executionState_mapClassical_comp_instances]
        conv_rhs => rw [ExecutionState.executionState_mapClassical_comp_instances]
        apply ExecutionState.executionState_mapClassical_congr_decision
          ((body value).execute Reference
            (state.selectClassical (fun record => record.1.read input) value))
          _ _ (fun entry => by rfl) _ _
      have originalTotal : ∑ value, (originalParts value).mass ≤ 1 := by
        simp only [originalParts, Execution.State.mapHistory_mass, Circuit.execute_mass,
          ExecutionState.sum_selectClassical_mass]
        exact state.mass_le_one
      have compiledTotal : ∑ value, (compiledParts value).mass ≤ 1 := by
        calc
          _ = ∑ value, (originalParts value).mass := by
            apply Finset.sum_congr rfl
            intro value _
            rw [partEq, Execution.State.mapHistory_mass]
          _ ≤ 1 := originalTotal
      have mappedTotal : ∑ value, ((originalParts value).mapHistory resultMap).mass ≤ 1 := by
        simpa only [Execution.State.mapHistory_mass] using originalTotal
      change (Circuit.branch (model := .quantum gates oracles model) input compiled).execute
          Reference state =
        ((Circuit.branch input body).execute Reference state).mapHistory resultMap
      calc
        _ = ExecutionState.finiteSum compiledParts compiledTotal := rfl
        _ = ExecutionState.finiteSum
            (fun value => (originalParts value).mapHistory resultMap) mappedTotal := by
          apply ExecutionState.ext
          intro output
          apply DensityOperator.ext
          simp only [ExecutionState.finiteSum_block_matrix]
          exact Finset.sum_congr rfl (fun value _ => congrArg
            (fun part => (part.block output).matrix) (partEq value))
        _ = Execution.State.mapHistory
            (ExecutionState.finiteSum originalParts originalTotal) resultMap := by
          convert (ExecutionState.mapClassical_finiteSum originalParts originalTotal
            (fun record => (record.1, resultMap record.2))).symm using 1 <;>
            dsimp only [Execution.State.mapHistory] <;>
            congr! 2
          apply ExecutionState.ext
          intro label
          apply DensityOperator.ext
          simp only [ExecutionState.finiteSum, ExecutionState.mapClassical_block_matrix]
          apply Finset.sum_congr rfl
          intro index _
          apply Finset.sum_congr rfl
          intro entry _
          split_ifs <;> rfl
        _ = _ := congrArg (fun output : Execution.State sourcePost Reference
            ((.quantum gates oracles : ExecutionModel).HiddenState ×
              (H × (Circuit.branch input body).Path)) => output.mapHistory resultMap) (show
          (Circuit.branch input body).execute Reference state =
            ExecutionState.finiteSum originalParts originalTotal from rfl).symm
  | @iterate sourceModel ctx count body bodyIH =>
      intro gates oracles selected Reference H _ state
      cases selected
      let inner : Circuit (.quantum gates oracles model) ctx ctx :=
        (selectForCircuitAux body rfl).code
      let pathMap : body.Path ≃ inner.Path := (selectForCircuitAux body rfl).paths
      change (Circuit.iterate count inner).execute Reference state =
        ((Circuit.iterate count body).execute Reference state).mapHistory
          (fun record => (record.1, (record.2.1,
            (Equiv.piCongrRight (fun _ => pathMap)) record.2.2)))
      refine iterate_execution_transport body inner pathMap ?_ count Reference state
      intro Reference H _ state
      exact bodyIH rfl Reference state
  | @workspace sourceModel ctx key shape fresh body bodyIH =>
      intro gates oracles selected Reference H _ state
      cases selected
      let inner : Circuit (.quantum gates oracles model)
          (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) :=
        (selectForCircuitAux body rfl).code
      let pathMap : body.Path ≃ inner.Path := (selectForCircuitAux body rfl).paths
      change (Circuit.workspace (model := .quantum gates oracles model)
          ctx key shape fresh inner).execute Reference state =
        ((Circuit.workspace (model := .quantum gates oracles)
          ctx key shape fresh body).execute Reference state).mapHistory
          (fun record => (record.1, (record.2.1, pathMap record.2.2)))
      have bodyEq : inner.execute Reference (state.pushWorkspace key shape fresh) =
          (body.execute Reference (state.pushWorkspace key shape fresh)).mapHistory
            (fun record => (record.1, (record.2.1, pathMap record.2.2))) := by
        exact bodyIH rfl Reference (state.pushWorkspace key shape fresh)
      rw [Circuit.execute_workspace, Circuit.execute_workspace, bodyEq]
      exact (Execution.State.mapHistory_popWorkspace key shape fresh
        (body.execute Reference (state.pushWorkspace key shape fresh))
        (fun record => (record.1, (record.2.1, pathMap record.2.2))))

private theorem relabelPath_eq_mapHistory {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {Reference : Register}
    {Hidden H P Q : Type} [Fintype Hidden] [Fintype H] [Fintype P] [Fintype Q]
    (state : Execution.State ctx Reference (Hidden × (H × P))) (paths : P → Q) :
    Circuit.relabelPath state paths =
      state.mapHistory (fun record => (record.1, (record.2.1, paths record.2.2))) := by
  dsimp only [Circuit.relabelPath, Execution.State.mapHistory]
  apply ExecutionState.executionState_mapClassical_congr_decision
    state _ _ (fun entry => rfl) _ _

/-- Certify bit/word model selection on every complete weighted execution state. -/
def selectForCircuitSelection {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) :
    Circuit.QuantumClassicalSelection model code where
  code := (selectForCircuitAux code rfl).code
  paths := (selectForCircuitAux code rfl).paths
  execute := by
    intro Reference H _ state
    let selected : Circuit (.quantum gates oracles model) pre post :=
      (selectForCircuitAux code rfl).code
    let pathMap : code.Path ≃ selected.Path := (selectForCircuitAux code rfl).paths
    change selected.execute Reference state =
      Circuit.relabelPath (code.execute Reference state) pathMap
    have auxiliary : selected.execute Reference state =
        (code.execute Reference state).mapHistory (fun record =>
          (record.1, (record.2.1, pathMap record.2.2))) := by
      exact selectForCircuitAux_execute code rfl Reference state
    have bridge : Circuit.relabelPath (code.execute Reference state) pathMap =
        (code.execute Reference state).mapHistory (fun record =>
          (record.1, (record.2.1, pathMap record.2.2))) := by
      exact relabelPath_eq_mapHistory (code.execute Reference state) pathMap
    exact auxiliary.trans bridge.symm

/-- Preserve a pure quantum program under the certified bit/word selection. -/
def selectForCircuit {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) :
    Circuit (.quantum gates oracles model) pre post :=
  (selectForCircuitSelection code).code

/-- The selected circuit records exactly the original finite path choices. -/
def selectForCircuitPathEquiv {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) :
    code.Path ≃ (selectForCircuit code).Path :=
  (selectForCircuitSelection code).paths

/-- The same actual path has the same number of events after native-language selection. -/
theorem selectForCircuit_eventCount {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) (path : code.Path) :
    ((selectForCircuit code).eventTrace (selectForCircuitPathEquiv code path)).length =
      (code.eventTrace path).length :=
  (selectForCircuitAux code rfl).eventCount path

/-- The selected circuit contains precisely the original quantum events in order. -/
theorem selectForCircuit_eventTrace {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) (path : code.Path) :
    (selectForCircuit code).eventTrace (selectForCircuitPathEquiv code path) =
      (code.eventTrace path).map liftQuantumEvent := by
  exact (selectForCircuitAux code rfl).events path

/-- The exact native multiplicities are preserved under structural model selection. -/
theorem selectForCircuit_resourcePool {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) (path : code.Path) :
    (selectForCircuit code).resourcePool (selectForCircuitPathEquiv code path) =
      liftQuantumPool (code.resourcePool path) := by
  simp only [Circuit.resourcePool, selectForCircuit_eventTrace, liftQuantumPool,
    ResourcePool.ofList]
  rfl

/-- Model selection visits exactly the original live quantum contexts. -/
theorem selectForCircuit_visitedContexts {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) (path : code.Path) :
    (selectForCircuit code).visitedContexts (selectForCircuitPathEquiv code path) =
      code.visitedContexts path := by
  exact eq_of_heq ((selectForCircuitAux code rfl).visited path)

/-- The selected classical language does not change resident quantum space. -/
theorem selectForCircuit_peakResidentSpace {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) (path : code.Path) :
    (selectForCircuit code).peakResidentSpace (selectForCircuitPathEquiv code path) =
      code.peakResidentSpace path := by
  simp only [Circuit.peakResidentSpace, selectForCircuit_visitedContexts]

/-- The selected classical language does not change auxiliary quantum space. -/
theorem selectForCircuit_peakAuxiliarySpace {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) (path : code.Path) :
    (selectForCircuit code).peakAuxiliarySpace (selectForCircuitPathEquiv code path) =
      code.peakAuxiliarySpace path := by
  simp only [Circuit.peakAuxiliarySpace, selectForCircuit_visitedContexts]

/-- Selecting the native bit/word language preserves the allocation-free fragment. -/
theorem selectForCircuit_isLocal {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post) (supported : code.IsLocal) :
    (selectForCircuit code).IsLocal :=
  (selectForCircuitAux code rfl).preservesLocal supported

/-- Selecting bit/word operations preserves the complete weighted execution state,
including the store, hidden state, quantum reference and zero-mass histories. -/
theorem selectForCircuit_execute {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post)
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State pre Reference
      ((.quantum gates oracles : ExecutionModel).HiddenState × H)) :
    (selectForCircuit code).execute Reference state =
      (code.execute Reference state).mapHistory (fun record =>
        (record.1, (record.2.1, selectForCircuitPathEquiv code record.2.2))) := by
  exact selectForCircuitAux_execute code rfl Reference state

end

end QuantumAlg.BitWord
