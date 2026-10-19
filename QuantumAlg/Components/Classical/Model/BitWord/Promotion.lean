/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Execution.Circuit.Local
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Composition.History
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Interpret.Preserving
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

private abbrev selectedCtx {source : ExecutionModel} {gates : GateModel}
    {oracles : OracleModel} {services : ClassicalOracleModel} (selected : source = .quantum gates
      oracles .empty services)
    (ctx : RuntimeCtx source.kind) : RuntimeCtx .quantum := by
  cases selected
  exact ctx

private def liftEvent {gates : GateModel} {oracles : OracleModel}
    {services : ClassicalOracleModel} :
    Resource.Event (.quantum gates oracles .empty services) →
      Resource.Event (.quantum gates oracles model services)
  | .classicalOperation impossible => nomatch impossible
  | .classicalQuery coordinate => .classicalQuery coordinate
  | .gate coordinate => .gate coordinate
  | .oracle coordinate => .oracle coordinate
  | .preparation dimension => .preparation dimension
  | .measurement dimension => .measurement dimension

/-- Embed a pure quantum event without changing its native coordinate. -/
def liftQuantumEvent {gates : GateModel} {oracles : OracleModel} :
    Resource.Event (.quantum gates oracles) →
      Resource.Event (.quantum gates oracles model) := liftEvent

/-- Embed the entire literal pure-quantum event ledger into the selected model. -/
def liftQuantumPool {gates : GateModel} {oracles : OracleModel}
    (pool : ResourcePool (.quantum gates oracles)) :
    ResourcePool (.quantum gates oracles model) :=
  pool.map liftQuantumEvent

/-- Selection leaves the total number of native quantum events unchanged. -/
@[simp] lemma liftQuantumPool_card {gates : GateModel} {oracles : OracleModel}
    (pool : ResourcePool (.quantum gates oracles)) :
    (liftQuantumPool pool).card = pool.card := by
  simp [liftQuantumPool]

/-- Every selected duration observes the original coordinates at the same weights. -/
lemma liftQuantumPool_weightedCount {gates : GateModel} {oracles : OracleModel}
    (duration : Resource.Event (.quantum gates oracles model) → Nat)
    (pool : ResourcePool (.quantum gates oracles)) :
    ResourcePool.weightedCount duration (liftQuantumPool pool) =
      ResourcePool.weightedCount (duration ∘ liftQuantumEvent) pool := by
  simp [ResourcePool.weightedCount, liftQuantumPool, Multiset.map_map]

private def selectedEvent {source : ExecutionModel} {gates : GateModel}
    {oracles : OracleModel} {services : ClassicalOracleModel} (selected : source = .quantum gates
      oracles .empty services) :
    Resource.Event source → Resource.Event (.quantum gates oracles model services) := by
  cases selected
  exact liftEvent

private lemma unitaryEventTrace_lift {gates : GateModel} {oracles : OracleModel} {services :
  ClassicalOracleModel}
    {count : Nat} {layout : QuantumLayout count}
    (program : UnitarySequence gates oracles layout) :
    program.eventTrace model services =
      (program.eventTrace .empty services).map liftEvent := by
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

private lemma unitaryEventCount_independent {gates : GateModel} {oracles : OracleModel}
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

private lemma liftEvent_serviceLeft {gates : GateModel} {oracles : OracleModel}
    {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    (event : Resource.Event (.quantum gates oracles .empty left)) :
    Resource.Event.serviceQuantumLeft join gates oracles model (liftEvent event) =
      liftEvent (Resource.Event.serviceQuantumLeft join gates oracles .empty event) := by
  cases event <;> first | rfl | contradiction

private lemma liftEvent_serviceRight {gates : GateModel} {oracles : OracleModel}
    {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    (event : Resource.Event (.quantum gates oracles .empty right)) :
    Resource.Event.serviceQuantumRight join gates oracles model (liftEvent event) =
      liftEvent (Resource.Event.serviceQuantumRight join gates oracles .empty event) := by
  cases event <;> first | rfl | contradiction

private structure SelectedCircuit {source : ExecutionModel} {allowAllocation : Bool}
    {pre post : RuntimeCtx source.kind} (original : Circuit source pre post allowAllocation)
    {gates : GateModel} {oracles : OracleModel} {services : ClassicalOracleModel}
    (selected : source = .quantum gates oracles .empty services) where
  code : Circuit (.quantum gates oracles model services)
    (selectedCtx selected pre) (selectedCtx selected post) allowAllocation
  paths : original.Path ≃ code.Path
  preservesLocal : original.IsLocal → code.IsLocal
  eventCount : ∀ path : original.Path,
    (code.eventTrace (paths path)).length = (original.eventTrace path).length
  events : ∀ path : original.Path,
    code.eventTrace (paths path) =
      (original.eventTrace path).map (selectedEvent selected)
  visited : ∀ path : original.Path,
    HEq (code.visitedContexts (paths path)) (original.visitedContexts path)

private def selectForCircuitAux {source : ExecutionModel} {allowAllocation : Bool}
    {pre post : RuntimeCtx source.kind} (code : Circuit source pre post allowAllocation) :
    ∀ {gates : GateModel} {oracles : OracleModel} {services : ClassicalOracleModel}
      (selected : source = .quantum gates oracles .empty services), SelectedCircuit code selected :=
        by
  induction code with
  | id ctx =>
      intro gates oracles services selected
      cases selected
      exact ⟨Circuit.id (model := .quantum gates oracles model services) ctx,
        Equiv.refl _, fun _ => trivial, fun _ => rfl, fun _ => rfl, fun _ => HEq.rfl⟩
  | classical application =>
      intro gates oracles services selected
      cases selected
      exact False.elim (nomatch application.token)
  | classicalQuery application =>
      intro gates oracles services selected
      cases selected
      exact ⟨Circuit.classicalQuery (model := .quantum gates oracles model services) application,
        Equiv.refl _, fun unsupported => False.elim unsupported,
        fun _ => rfl, fun _ => rfl, fun _ => HEq.rfl⟩
  | @unitary gateModel oracleModel ctx operations originalServices allocation program =>
      intro gates oracles services selected
      cases selected
      exact ⟨Circuit.unitary (operations := model) (classicalOracles := originalServices) program,
        Equiv.refl _, fun _ => trivial,
        fun _ => unitaryEventCount_independent program.sequence model .empty
          originalServices originalServices,
        fun _ => unitaryEventTrace_lift program.sequence,
        fun _ => HEq.rfl⟩
  | @measureZ gateModel oracleModel ctx operations originalServices allocation wire output =>
      intro gates oracles services selected
      cases selected
      exact ⟨Circuit.measureZ (operations := model)
        (classicalOracles := originalServices) wire output,
        Equiv.refl _, fun _ => trivial, fun _ => rfl, fun _ => rfl, fun _ => HEq.rfl⟩
  | retain ctx key shape fresh =>
      intro gates oracles services selected
      cases selected
      exact ⟨Circuit.retain (model := .quantum gates oracles model services) ctx key shape fresh,
        Equiv.refl _, fun unsupported => False.elim unsupported, fun _ => rfl,
        fun _ => rfl,
        fun _ => HEq.rfl⟩
  | @prepareZero gateModel oracleModel operations originalServices ctx key systemCount layout
      fresh disjoint =>
      intro gates oracles services selected
      cases selected
      exact ⟨Circuit.prepareZero (operations := model)
        (classicalOracles := originalServices) ctx key layout fresh disjoint,
        Equiv.refl _, fun unsupported => False.elim unsupported,
        fun _ => by simp [Circuit.eventTrace, ZeroPreparation.eventTrace],
        fun _ => by
          simp only [Circuit.eventTrace, ZeroPreparation.eventTrace, List.map_ofFn]
          congr 1,
        fun _ => HEq.rfl⟩
  | seq first second firstIH secondIH =>
      intro gates oracles services selected
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
      intro gates oracles services selected
      cases selected
      exact ⟨Circuit.branch input (fun value => (bodyIH value rfl).code),
        Equiv.sigmaCongrRight (fun value => (bodyIH value rfl).paths),
        fun supported value => (bodyIH value rfl).preservesLocal (supported value),
        fun path => (bodyIH path.1 rfl).eventCount path.2,
        fun path => (bodyIH path.1 rfl).events path.2,
        fun path => (bodyIH path.1 rfl).visited path.2⟩
  | iterate count body bodyIH =>
      intro gates oracles services selected
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
      intro gates oracles services selected
      cases selected
      let selectedBody := bodyIH rfl
      exact ⟨Circuit.workspace (model := .quantum gates oracles model services) ctx key shape fresh
        selectedBody.code, selectedBody.paths,
        fun unsupported => False.elim unsupported,
        fun path => selectedBody.eventCount path,
        fun path => selectedBody.events path,
        fun path => by
          simp only [Circuit.visitedContexts]
          congr! 2
          exact eq_of_heq (selectedBody.visited path)⟩
  | embed placement body bodyIH =>
      intro gates oracles services selected
      cases selected
      let inner := bodyIH rfl
      exact ⟨Circuit.embed placement inner.code, inner.paths,
        fun unsupported => False.elim unsupported,
        inner.eventCount, inner.events, fun _ => HEq.rfl⟩
  | parallelClassical join separate first second firstIH secondIH =>
      intro gates oracles services selected
      cases selected
  | parallelQuantum join separate first second firstIH secondIH =>
      intro gates oracles services selected
      cases selected
      let left := firstIH rfl
      let right := secondIH rfl
      exact ⟨Circuit.parallelQuantum join separate left.code right.code,
        Equiv.prodCongr left.paths right.paths,
        fun unsupported => False.elim unsupported,
        fun path => by
          rcases path with ⟨leftPath, rightPath⟩
          simp only [Circuit.eventTrace, List.length_append, List.length_map,
            Equiv.prodCongr, Equiv.coe_fn_mk, Prod.map_apply]
          rw [left.eventCount leftPath, right.eventCount rightPath],
        fun path => by
          rcases path with ⟨leftPath, rightPath⟩
          simp only [Circuit.eventTrace, Equiv.prodCongr, Equiv.coe_fn_mk, Prod.map_apply]
          rw [left.events leftPath, right.events rightPath]
          simp only [List.map_append, List.map_map, selectedEvent, Function.comp_def,
            liftEvent_serviceLeft, liftEvent_serviceRight],
        fun _ => HEq.rfl⟩

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma mapHistory_eta {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {S H P : Type} [Fintype S] [Fintype H] [Fintype P]
    (state : Execution.State ctx Reference (S × (H × P))) :
    state.mapHistory (fun record => (record.1, (record.2.1, record.2.2))) = state := by
  dsimp only [Execution.State.mapHistory]
  apply (ExecutionState.executionState_mapClassical_congr_decision state _ id
    (fun entry => by cases entry; rfl) _ _).trans
  exact ExecutionState.mapClassical_id state

private abbrev PathTransport {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Hidden Path Other : Type} [Fintype Hidden] [Fintype Path] [Fintype Other]
    {Reference : Register}
    (original : Execution.Preserving Hidden ctx ctx Reference Path)
    (selected : Execution.Preserving Hidden ctx ctx Reference Other) (paths : Path → Other) :=
  ∀ {H : Type} [Fintype H] (state : Execution.State ctx Reference (Hidden × H)),
    (selected state).val = (original state).val.mapHistory
      (fun record => (record.1, (record.2.1, paths record.2.2)))

private lemma embed_pathTransport {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    {Hidden Path Other : Type} [Fintype Hidden] [Fintype Path] [Fintype Other]
    (placement : ContextEmbedding localCtx caller) (Reference : Register)
    (original : Execution.Preserving Hidden localCtx localCtx
      (Register.prod placement.frame.register Reference) Path)
    (selected : Execution.Preserving Hidden localCtx localCtx
      (Register.prod placement.frame.register Reference) Other)
    (paths : Path → Other) (same : PathTransport original selected paths) :
    PathTransport (Execution.embedPreserving placement Reference original)
      (Execution.embedPreserving placement Reference selected) paths := by
  intro H _ state
  dsimp only [Execution.embedPreserving]
  rw [same, ← placement.join_mapHistory]
  congr 1
  simp only [Execution.State.mapHistory_comp, Function.comp_def]

private lemma left_pathTransport {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    {Path Other : Type} [Fintype Path] [Fintype Other]
    (original : Execution.Preserving left.HiddenState ctx ctx Reference Path)
    (selected : Execution.Preserving left.HiddenState ctx ctx Reference Other)
    (paths : Path → Other) (same : PathTransport original selected paths) :
    PathTransport (Execution.serviceLeftPreserving join original)
      (Execution.serviceLeftPreserving join selected) paths := by
  intro H _ state
  dsimp only [Execution.serviceLeftPreserving]
  rw [same]
  simp only [Execution.serviceOutputLeft, Execution.State.mapHistory,
    ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma right_pathTransport {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    {Path Other : Type} [Fintype Path] [Fintype Other]
    (original : Execution.Preserving right.HiddenState ctx ctx Reference Path)
    (selected : Execution.Preserving right.HiddenState ctx ctx Reference Other)
    (paths : Path → Other) (same : PathTransport original selected paths) :
    PathTransport (Execution.serviceRightPreserving join original)
      (Execution.serviceRightPreserving join selected) paths := by
  intro H _ state
  dsimp only [Execution.serviceRightPreserving]
  rw [same]
  simp only [Execution.serviceOutputRight, Execution.State.mapHistory,
    ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma parallel_pathTransport {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    {kind : ProblemKind} {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx) (Reference : Register)
    {LeftPath RightPath LeftOther RightOther : Type}
    [Fintype LeftPath] [Fintype RightPath] [Fintype LeftOther] [Fintype RightOther]
    (first : Execution.Preserving left.HiddenState leftCtx leftCtx
      (Register.prod rightCtx.register Reference) LeftPath)
    (second : Execution.Preserving right.HiddenState rightCtx rightCtx
      (Register.prod leftCtx.register Reference) RightPath)
    (leftSelected : Execution.Preserving left.HiddenState leftCtx leftCtx
      (Register.prod rightCtx.register Reference) LeftOther)
    (rightSelected : Execution.Preserving right.HiddenState rightCtx rightCtx
      (Register.prod leftCtx.register Reference) RightOther)
    (leftPaths : LeftPath → LeftOther) (rightPaths : RightPath → RightOther)
    (leftSame : PathTransport first leftSelected leftPaths)
    (rightSame : PathTransport second rightSelected rightPaths)
    (rightNatural : Execution.HistoryNatural rightSelected) :
    PathTransport (Execution.parallelPreserving join separate first second)
      (Execution.parallelPreserving join separate leftSelected rightSelected)
      (Prod.map leftPaths rightPaths) := by
  have firstSame : PathTransport
      (Execution.serviceLeftPreserving join
        (Execution.embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
          Reference first))
      (Execution.serviceLeftPreserving join
        (Execution.embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
          Reference leftSelected)) leftPaths := left_pathTransport join
    (Execution.embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
      Reference first)
    (Execution.embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
      Reference leftSelected) leftPaths
    (embed_pathTransport (ContextEmbedding.alongUnion leftCtx rightCtx separate)
      Reference first leftSelected leftPaths leftSame)
  have secondSame : PathTransport
      (Execution.serviceRightPreserving join
        (Execution.embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
          Reference second))
      (Execution.serviceRightPreserving join
        (Execution.embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
          Reference rightSelected)) rightPaths := right_pathTransport join
    (Execution.embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      Reference second)
    (Execution.embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      Reference rightSelected) rightPaths
    (embed_pathTransport (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      Reference second rightSelected rightPaths rightSame)
  have secondNatural : Execution.HistoryNatural
      (Execution.serviceRightPreserving join
        (Execution.embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
          Reference rightSelected)) := Execution.serviceRightPreserving_history join
    (Execution.embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      Reference rightSelected)
    (Execution.embedPreserving_history
      (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      Reference rightSelected rightNatural)
  intro H _ state
  have natural := secondNatural
    ((Execution.serviceLeftPreserving join
      (Execution.embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
        Reference first)) state).val
    (fun record : H × LeftPath => (record.1, leftPaths record.2))
  dsimp only [Execution.parallelPreserving, Execution.embedServiceLeftPreserving,
    Execution.embedServiceRightPreserving]
  rw [firstSame state, natural, secondSame]
  simp only [Execution.State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def, Prod.map_apply]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def selectedEnvironment {source : ExecutionModel} {gates : GateModel}
    {oracles : OracleModel} {services : ClassicalOracleModel}
    (selected : source = .quantum gates oracles .empty services)
    (environment : source.Environment) :
    (.quantum gates oracles model services : ExecutionModel).Environment := by
  cases selected
  exact ⟨environment.quantum, environment.classical⟩

private def selectedState {source : ExecutionModel} {gates : GateModel}
    {oracles : OracleModel} {services : ClassicalOracleModel} {ctx : RuntimeCtx source.kind}
      {Reference : Register}
    {H : Type} [Fintype H] (selected : source = .quantum gates oracles .empty services)
    (state : Execution.State ctx Reference (source.HiddenState × H)) :
    Execution.State (selectedCtx selected ctx) Reference
      ((.quantum gates oracles model services : ExecutionModel).HiddenState × H) := by
  cases selected
  exact state

private lemma iterate_execution_transport {allowAllocation : Bool} {gates : GateModel} {oracles :
  OracleModel} {services : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum}
    (original : Circuit (.quantum gates oracles .empty services) ctx ctx allowAllocation)
    (selected : Circuit (.quantum gates oracles model services) ctx ctx allowAllocation)
    (paths : original.Path ≃ selected.Path)
    (environment : (.quantum gates oracles .empty services : ExecutionModel).Environment)
    (step : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : Execution.State ctx Reference
        ((.quantum gates oracles .empty services : ExecutionModel).HiddenState × H)),
      selected.execute ⟨environment.quantum, environment.classical⟩ Reference state =
        (original.execute ⟨environment.quantum, environment.classical⟩ Reference state).mapHistory
          (fun record =>
          (record.1, (record.2.1, paths record.2.2))))
    (count : Nat) (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State ctx Reference
      ((.quantum gates oracles .empty services : ExecutionModel).HiddenState × H)) :
    (Circuit.iterate count selected).execute ⟨environment.quantum, environment.classical⟩ Reference
      state =
      ((Circuit.iterate count original).execute ⟨environment.quantum, environment.classical⟩
        Reference state).mapHistory
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
      have natural : (Circuit.iterate count selected).execute ⟨environment.quantum,
        environment.classical⟩ Reference
          ((original.execute ⟨environment.quantum, environment.classical⟩ Reference
            state).mapHistory
            (fun record => (record.1, (record.2.1, paths record.2.2)))) =
          ((Circuit.iterate count selected).execute ⟨environment.quantum, environment.classical⟩
            Reference
            (original.execute ⟨environment.quantum, environment.classical⟩ Reference
              state)).mapHistory
              (fun record =>
                (record.1, ((record.2.1.1, paths record.2.1.2), record.2.2))) := by
        exact Circuit.execute_mapHistory (Circuit.iterate count selected)
          ⟨environment.quantum, environment.classical⟩ Reference
          (original.execute ⟨environment.quantum, environment.classical⟩ Reference state) (fun
            history => (history.1, paths history.2))
      rw [natural]
      rw [ih (original.execute ⟨environment.quantum, environment.classical⟩ Reference state)]
      simp only [Execution.State.mapHistory_comp, Function.comp_def]
      apply ExecutionState.executionState_mapClassical_congr_decision
        ((Circuit.iterate count original).execute ⟨environment.quantum, environment.classical⟩
          Reference (original.execute ⟨environment.quantum, environment.classical⟩ Reference state))
        _ _ (fun entry => by
          simp only [Prod.mk.injEq, true_and]
          funext index
          refine Fin.cases ?_ (fun i => ?_) index <;> rfl) _ _

private lemma selectForCircuitAux_execute {source : ExecutionModel} {allowAllocation : Bool}
    {pre post : RuntimeCtx source.kind} (code : Circuit source pre post allowAllocation) :
    ∀ {gates : GateModel} {oracles : OracleModel} {services : ClassicalOracleModel}
      (selected : source = .quantum gates oracles .empty services)
      (environment : source.Environment) (Reference : Register)
      {H : Type} [Fintype H]
      (state : Execution.State pre Reference (source.HiddenState × H)),
      ((selectForCircuitAux code selected).code.execute
        (selectedEnvironment selected environment) Reference
        (selectedState selected state)) =
      selectedState selected ((code.execute environment Reference state).mapHistory (fun record =>
        (record.1, (record.2.1, (selectForCircuitAux code selected).paths record.2.2)))) := by
  induction code with
  | @id source allocation ctx =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      change (Circuit.id (allowAllocation := allocation) (model := .quantum gates oracles model
        services) ctx).execute ⟨environment.quantum, environment.classical⟩ Reference state =
        ((Circuit.id (allowAllocation := allocation) (model := .quantum gates oracles .empty
          services) ctx).execute ⟨environment.quantum, environment.classical⟩ Reference
            state).mapHistory
          (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | classical application =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      exact False.elim (nomatch application.token)
  | @classicalQuery source ctx allocation application =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      change (Circuit.classicalQuery (allowAllocation := allocation) (model := .quantum gates
        oracles model services)
          application).execute ⟨environment.quantum, environment.classical⟩ Reference state =
        ((Circuit.classicalQuery (allowAllocation := allocation) (model := .quantum gates oracles
          .empty services)
          application).execute ⟨environment.quantum, environment.classical⟩ Reference
            state).mapHistory
            (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | @unitary gateModel oracleModel ctx operations originalServices allocation program =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      change (Circuit.unitary (allowAllocation := allocation) (operations := model)
        (classicalOracles := originalServices) program).execute ⟨environment.quantum,
          environment.classical⟩ Reference state =
        ((Circuit.unitary (allowAllocation := allocation) (operations := .empty) (classicalOracles
          := originalServices) program).execute ⟨environment.quantum, environment.classical⟩
            Reference state).mapHistory
          (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | @measureZ gateModel oracleModel actualCtx operations originalServices allocation wire output =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      change (Circuit.measureZ (allowAllocation := allocation) (gates := gateModel)
        (oracles := oracleModel) (operations := model)
        (classicalOracles := originalServices) wire output).execute ⟨environment.quantum,
          environment.classical⟩ Reference state =
        ((Circuit.measureZ (allowAllocation := allocation) (gates := gateModel)
          (oracles := oracleModel) (operations := .empty)
          (classicalOracles := originalServices) wire output).execute ⟨environment.quantum,
            environment.classical⟩ Reference state).mapHistory
          (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | retain ctx key shape fresh =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      change (Circuit.retain (model := .quantum gates oracles model services) ctx key shape
        fresh).execute ⟨environment.quantum, environment.classical⟩ Reference state =
        ((Circuit.retain (model := .quantum gates oracles .empty services) ctx key shape
          fresh).execute ⟨environment.quantum, environment.classical⟩ Reference state).mapHistory
            (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | @prepareZero gateModel oracleModel operations originalServices ctx key systemCount layout
      fresh disjoint =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      change (Circuit.prepareZero (gates := gateModel) (oracles := oracleModel)
          (operations := model) (classicalOracles := originalServices) ctx key layout fresh
            disjoint).execute ⟨environment.quantum, environment.classical⟩ Reference state =
        ((Circuit.prepareZero (gates := gateModel) (oracles := oracleModel)
          (operations := .empty) (classicalOracles := originalServices) ctx key layout fresh
            disjoint).execute ⟨environment.quantum, environment.classical⟩ Reference
              state).mapHistory (fun record => (record.1, (record.2.1, record.2.2)))
      rw [mapHistory_eta]
      rfl
  | @seq sourceModel sourcePre middle sourcePost allocation first second firstIH secondIH =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      let leftCode : Circuit (.quantum gates oracles model services) sourcePre middle allocation :=
        (selectForCircuitAux first rfl).code
      let rightCode : Circuit (.quantum gates oracles model services) middle sourcePost allocation
        :=
        (selectForCircuitAux second rfl).code
      let leftPaths : first.Path ≃ leftCode.Path := (selectForCircuitAux first rfl).paths
      let rightPaths : second.Path ≃ rightCode.Path := (selectForCircuitAux second rfl).paths
      change (leftCode.seq rightCode).execute ⟨environment.quantum, environment.classical⟩ Reference
        state =
        ((first.seq second).execute ⟨environment.quantum, environment.classical⟩ Reference
          state).mapHistory (fun record =>
          (record.1, (record.2.1,
            (Equiv.prodCongr leftPaths rightPaths) record.2.2)))
      have leftEq : leftCode.execute ⟨environment.quantum, environment.classical⟩ Reference state =
          (first.execute ⟨environment.quantum, environment.classical⟩ Reference state).mapHistory
            (fun record =>
            (record.1, (record.2.1, leftPaths record.2.2))) := by
        exact firstIH rfl environment Reference state
      have rightEq : rightCode.execute ⟨environment.quantum, environment.classical⟩ Reference
        (first.execute ⟨environment.quantum, environment.classical⟩ Reference state) =
          (second.execute ⟨environment.quantum, environment.classical⟩ Reference (first.execute
            ⟨environment.quantum, environment.classical⟩ Reference state)).mapHistory
            (fun record => (record.1, (record.2.1, rightPaths record.2.2))) := by
        exact secondIH rfl environment Reference (first.execute ⟨environment.quantum,
          environment.classical⟩ Reference state)
      simp only [Circuit.execute_seq]
      rw [leftEq]
      have natural : rightCode.execute ⟨environment.quantum, environment.classical⟩ Reference
          ((first.execute ⟨environment.quantum, environment.classical⟩ Reference state).mapHistory
            (fun record =>
            (record.1, (record.2.1, leftPaths record.2.2)))) =
          (rightCode.execute ⟨environment.quantum, environment.classical⟩ Reference (first.execute
            ⟨environment.quantum, environment.classical⟩ Reference state)).mapHistory
            (fun record =>
              (record.1, ((record.2.1.1, leftPaths record.2.1.2), record.2.2))) := by
        exact Circuit.execute_mapHistory rightCode
          ⟨environment.quantum, environment.classical⟩ Reference (first.execute
            ⟨environment.quantum, environment.classical⟩ Reference state)
          (fun history => (history.1, leftPaths history.2))
      rw [natural]
      rw [rightEq]
      simp only [Execution.State.mapHistory_comp, Function.comp_def]
      rfl
  | @branch sourceModel sourcePre sourcePost shape allocation input body bodyIH =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      let compiled (value) : Circuit (.quantum gates oracles model services) sourcePre sourcePost
        allocation :=
        (selectForCircuitAux (body value) rfl).code
      let pathMap (value) : (body value).Path ≃ (compiled value).Path :=
        (selectForCircuitAux (body value) rfl).paths
      let branchPaths : (Circuit.branch input body).Path ≃
          (Circuit.branch (model := .quantum gates oracles model services) input compiled).Path :=
        Equiv.sigmaCongrRight pathMap
      let resultMap :
          ((.quantum gates oracles .empty services : ExecutionModel).HiddenState ×
            (H × (Circuit.branch input body).Path)) →
          ((.quantum gates oracles model services : ExecutionModel).HiddenState ×
            (H × (Circuit.branch (model := .quantum gates oracles model services) input
              compiled).Path)) :=
        fun record => (record.1, (record.2.1, branchPaths record.2.2))
      let originalParts (value) : Execution.State _ Reference
          ((.quantum gates oracles .empty services : ExecutionModel).HiddenState ×
            (H × (Circuit.branch input body).Path)) :=
        ((body value).execute ⟨environment.quantum, environment.classical⟩ Reference
          (state.selectClassical (fun record => record.1.read input) value)).mapHistory
            (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
      let compiledParts (value) : Execution.State _ Reference
          ((.quantum gates oracles model services : ExecutionModel).HiddenState ×
            (H × (Circuit.branch (model := .quantum gates oracles model services) input
              compiled).Path)) :=
        ((compiled value).execute ⟨environment.quantum, environment.classical⟩ Reference
          (state.selectClassical (fun record => record.1.read input) value)).mapHistory
            (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
      have partEq (value) : compiledParts value =
          (originalParts value).mapHistory resultMap := by
        have actual : (compiled value).execute ⟨environment.quantum, environment.classical⟩
          Reference
            (state.selectClassical (fun record => record.1.read input) value) =
          ((body value).execute ⟨environment.quantum, environment.classical⟩ Reference
            (state.selectClassical (fun record => record.1.read input) value)).mapHistory
              (fun record => (record.1, (record.2.1,
                pathMap value record.2.2))) := by
          exact bodyIH value rfl environment Reference
            (state.selectClassical (fun record => record.1.read input) value)
        dsimp only [compiledParts, originalParts]
        rw [actual]
        dsimp only [Execution.State.mapHistory]
        conv_lhs => rw [ExecutionState.executionState_mapClassical_comp_instances]
        conv_rhs => rw [ExecutionState.executionState_mapClassical_comp_instances]
        apply ExecutionState.executionState_mapClassical_congr_decision
          ((body value).execute ⟨environment.quantum, environment.classical⟩ Reference
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
      change (Circuit.branch (model := .quantum gates oracles model services) input
        compiled).execute ⟨environment.quantum, environment.classical⟩ Reference state =
        ((Circuit.branch input body).execute ⟨environment.quantum, environment.classical⟩ Reference
          state).mapHistory resultMap
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
            ((.quantum gates oracles .empty services : ExecutionModel).HiddenState ×
              (H × (Circuit.branch input body).Path)) => output.mapHistory resultMap) (show
          (Circuit.branch input body).execute ⟨environment.quantum, environment.classical⟩ Reference
            state =
            ExecutionState.finiteSum originalParts originalTotal from rfl).symm
  | @iterate sourceModel ctx allocation count body bodyIH =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      let inner : Circuit (.quantum gates oracles model services) ctx ctx allocation :=
        (selectForCircuitAux body rfl).code
      let pathMap : body.Path ≃ inner.Path := (selectForCircuitAux body rfl).paths
      change (Circuit.iterate count inner).execute ⟨environment.quantum, environment.classical⟩
        Reference state =
        ((Circuit.iterate count body).execute ⟨environment.quantum, environment.classical⟩ Reference
          state).mapHistory
          (fun record => (record.1, (record.2.1,
            (Equiv.piCongrRight (fun _ => pathMap)) record.2.2)))
      refine iterate_execution_transport body inner pathMap environment ?_ count Reference state
      intro Reference H _ state
      exact bodyIH rfl environment Reference state
  | @workspace sourceModel ctx key shape fresh body bodyIH =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      let inner : Circuit (.quantum gates oracles model services)
          (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) :=
        (selectForCircuitAux body rfl).code
      let pathMap : body.Path ≃ inner.Path := (selectForCircuitAux body rfl).paths
      change (Circuit.workspace (model := .quantum gates oracles model services)
          ctx key shape fresh inner).execute ⟨environment.quantum, environment.classical⟩ Reference
            state =
        ((Circuit.workspace (model := .quantum gates oracles .empty services)
          ctx key shape fresh body).execute ⟨environment.quantum, environment.classical⟩ Reference
            state).mapHistory
          (fun record => (record.1, (record.2.1, pathMap record.2.2)))
      have bodyEq : inner.execute ⟨environment.quantum, environment.classical⟩ Reference
        (state.pushWorkspace key shape fresh) =
          (body.execute ⟨environment.quantum, environment.classical⟩ Reference (state.pushWorkspace
            key shape fresh)).mapHistory
            (fun record => (record.1, (record.2.1, pathMap record.2.2))) := by
        exact bodyIH rfl environment Reference (state.pushWorkspace key shape fresh)
      rw [Circuit.execute_workspace, Circuit.execute_workspace, bodyEq]
      exact (Execution.State.mapHistory_popWorkspace key shape fresh
        (body.execute ⟨environment.quantum, environment.classical⟩ Reference (state.pushWorkspace
          key shape fresh))
        (fun record => (record.1, (record.2.1, pathMap record.2.2))))
  | embed placement body bodyIH =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      exact embed_pathTransport placement Reference
        (fun state => QuantumAlg.Execution.interpret body environment _ state)
        (fun state => QuantumAlg.Execution.interpret
          (selectForCircuitAux body rfl).code
            ⟨environment.quantum, environment.classical⟩ _ state)
        (selectForCircuitAux body rfl).paths
        (fun {_} _ original => bodyIH rfl environment _ original) state
  | parallelClassical join separate first second firstIH secondIH =>
      intro gates oracles services selected
      cases selected
  | parallelQuantum join separate first second firstIH secondIH =>
      intro gates oracles services selected environment Reference H _ state
      cases selected
      exact parallel_pathTransport join separate Reference
        (fun state => QuantumAlg.Execution.interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ state)
        (fun state => QuantumAlg.Execution.interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ state)
        (fun state => QuantumAlg.Execution.interpret
          (selectForCircuitAux first rfl).code
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ state)
        (fun state => QuantumAlg.Execution.interpret
          (selectForCircuitAux second rfl).code
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ state)
        (selectForCircuitAux first rfl).paths (selectForCircuitAux second rfl).paths
        (fun {_} _ original => firstIH rfl
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun {_} _ original => secondIH rfl
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (fun {_ _} _ _ original update => Circuit.execute_mapHistory
          (selectForCircuitAux second rfl).code
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original update)
        state

private lemma relabelPath_eq_mapHistory {kind : ProblemKind}
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
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) :
    Circuit.QuantumClassicalSelection model code where
  code := (selectForCircuitAux code rfl).code
  paths := (selectForCircuitAux code rfl).paths
  execute := by
    intro environment Reference H _ state
    let selected : Circuit (.quantum gates oracles model) pre post allowAllocation :=
      (selectForCircuitAux code rfl).code
    let pathMap : code.Path ≃ selected.Path := (selectForCircuitAux code rfl).paths
    change selected.execute ⟨environment, ()⟩ Reference state =
      Circuit.relabelPath (code.execute ⟨environment, ()⟩ Reference state) pathMap
    have auxiliary : selected.execute ⟨environment, ()⟩ Reference state =
        (code.execute ⟨environment, ()⟩ Reference state).mapHistory (fun record =>
          (record.1, (record.2.1, pathMap record.2.2))) := by
      exact selectForCircuitAux_execute code rfl ⟨environment, ()⟩ Reference state
    have bridge : Circuit.relabelPath (code.execute ⟨environment, ()⟩ Reference state) pathMap =
        (code.execute ⟨environment, ()⟩ Reference state).mapHistory (fun record =>
          (record.1, (record.2.1, pathMap record.2.2))) := by
      exact relabelPath_eq_mapHistory (code.execute ⟨environment, ()⟩ Reference state) pathMap
    exact auxiliary.trans bridge.symm

/-- Preserve a pure quantum program under the certified bit/word selection. -/
def selectForCircuit {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) :
    Circuit (.quantum gates oracles model) pre post allowAllocation :=
  (selectForCircuitSelection code).code

/-- The selected circuit records exactly the original finite path choices. -/
def selectForCircuitPathEquiv {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) :
    code.Path ≃ (selectForCircuit code).Path :=
  (selectForCircuitSelection code).paths

/-- The same actual path has the same number of events after native-language selection. -/
lemma selectForCircuit_eventCount {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (path : code.Path) :
    ((selectForCircuit code).eventTrace (selectForCircuitPathEquiv code path)).length =
      (code.eventTrace path).length :=
  (selectForCircuitAux code rfl).eventCount path

/-- The selected circuit contains precisely the original quantum events in order. -/
lemma selectForCircuit_eventTrace {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (path : code.Path) :
    (selectForCircuit code).eventTrace (selectForCircuitPathEquiv code path) =
      (code.eventTrace path).map liftQuantumEvent := by
  exact (selectForCircuitAux code rfl).events path

/-- The exact native multiplicities are preserved under structural model selection. -/
lemma selectForCircuit_resourcePool {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (path : code.Path) :
    (selectForCircuit code).resourcePool (selectForCircuitPathEquiv code path) =
      liftQuantumPool (code.resourcePool path) := by
  simp only [Circuit.resourcePool, selectForCircuit_eventTrace, liftQuantumPool,
    ResourcePool.ofList]
  rfl

/-- Model selection visits exactly the original live quantum contexts. -/
lemma selectForCircuit_visitedContexts {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (path : code.Path) :
    (selectForCircuit code).visitedContexts (selectForCircuitPathEquiv code path) =
      code.visitedContexts path := by
  exact eq_of_heq ((selectForCircuitAux code rfl).visited path)

/-- The selected classical language does not change resident quantum space. -/
lemma selectForCircuit_peakResidentSpace {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (path : code.Path) :
    (selectForCircuit code).peakResidentSpace (selectForCircuitPathEquiv code path) =
      code.peakResidentSpace path := by
  simp only [Circuit.peakResidentSpace, selectForCircuit_visitedContexts]

/-- The selected classical language does not change auxiliary quantum space. -/
lemma selectForCircuit_peakAuxiliarySpace {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (path : code.Path) :
    (selectForCircuit code).peakAuxiliarySpace (selectForCircuitPathEquiv code path) =
      code.peakAuxiliarySpace path := by
  simp only [Circuit.peakAuxiliarySpace, selectForCircuit_visitedContexts]

/-- Selecting the native bit/word language preserves the allocation-free fragment. -/
lemma selectForCircuit_isLocal {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (supported : code.IsLocal) :
    (selectForCircuit code).IsLocal :=
  (selectForCircuitAux code rfl).preservesLocal supported

/-- Selecting bit/word operations preserves the complete weighted execution state,
including the store, hidden state, quantum reference and zero-mass histories. -/
lemma selectForCircuit_execute {gates : GateModel} {oracles : OracleModel}
    {environment : (.quantum gates oracles model : ExecutionModel).Environment}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation)
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State pre Reference
      ((.quantum gates oracles : ExecutionModel).HiddenState × H)) :
    (selectForCircuit code).execute environment Reference state =
      (code.execute ⟨environment.quantum, environment.classical⟩ Reference state).mapHistory (fun
        record =>
        (record.1, (record.2.1, selectForCircuitPathEquiv code record.2.2))) := by
  exact selectForCircuitAux_execute code rfl
    ⟨environment.quantum, environment.classical⟩ Reference state

end

end QuantumAlg.BitWord
