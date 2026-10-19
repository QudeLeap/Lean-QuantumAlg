/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.ScopedContinuant
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Actual Euclidean division and continuant candidate prefix

One genuine division writes a live quotient/remainder pair. The candidate
program reads that same stored quotient, updates the continuant and releases
only its product temporary. The division pair remains live for the later
acceptance or Euclidean-advance branch.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- One actual closed Euclidean quotient/remainder instruction on the stored cursor words. -/
def cursorDivision (numerator denominator : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width))) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.product (.unsignedWord width) (.unsignedWord width)) ctx ctx :=
  .divRem width width ctx (.product numerator denominator) division

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual division precedes the continuant update using its retained quotient. -/
def candidatePrefix (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (cursorDivision numerator denominator division))
    (scopedContinuant (model := model) (.first (cellRead division)) previous older candidate)

/-- Concrete store and actual three-operation path after the candidate prefix. -/
def candidatePrefixStep
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (candidatePrefix (model := model) numerator denominator previous older
      division candidate).Path :=
  let divided := BitWord.instructionStep (execution := model)
    (cursorDivision numerator denominator division) store
  let materialized := scopedContinuantStep (model := model) (.first (cellRead division))
    previous older
    candidate divided.1
  (materialized.1, (divided.2, materialized.2))

/-- The actual prefix composes division and materialization on the same complete state. -/
lemma nativeCandidatePrefix_execute
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePrefix (model := model) numerator denominator previous older
      division candidate).execute environment
        Reference state =
      state.mapClassical (fun entry =>
        ((candidatePrefixStep (model := model) numerator denominator previous older
          division candidate entry.1).1,
          (entry.2.1, (entry.2.2,
            (candidatePrefixStep (model := model) numerator denominator previous older
          division candidate
              entry.1).2)))) := by
  simp only [candidatePrefix, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    nativeScopedContinuant_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual written candidate uses the real quotient and the original predecessor words. -/
lemma nativeCandidatePrefix_result
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (previousFree : division.key ∉ previous.storageKeys)
    (olderFree : division.key ∉ older.storageKeys) (store : Store ctx) :
    ((candidatePrefixStep (model := model) numerator denominator previous older
          division candidate store).1).read
        (cellRead candidate) =
      continuantValue (CShape.divRem width width
        (.product (store.read numerator) (store.read denominator))).first
        (store.read previous) (store.read older) := by
  unfold candidatePrefixStep
  simp only [BitWord.instructionStep]
  rw [nativeScopedContinuant_result]
  have quotient : (store.applyOp (cursorDivision numerator denominator division)).read
      (.first (cellRead division)) =
      (CShape.divRem width width
        (.product (store.read numerator) (store.read denominator))).first :=
    congrArg CShape.Value.first (Store.read_applyOp_output store
      (cursorDivision numerator denominator division))
  rw [quotient, Store.read_applyOp_of_not_mem_storageKeys store
    (cursorDivision numerator denominator division) previous previousFree,
    Store.read_applyOp_of_not_mem_storageKeys store
      (cursorDivision numerator denominator division) older olderFree]

/-- The prefix changes only its live division pair and the specified candidate cell. -/
lemma nativeCandidatePrefix_read_other
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (divisionFree : division.key ∉ other.storageKeys)
    (candidateFree : candidate.key ∉ other.storageKeys) (store : Store ctx) :
    ((candidatePrefixStep (model := model) numerator denominator previous older
          division candidate store).1).read
      other = store.read other :=
  (nativeScopedContinuant_read_other (.first (cellRead division)) previous older candidate
    other candidateFree (store.applyOp (cursorDivision numerator denominator division))).trans
    (Store.read_applyOp_of_not_mem_storageKeys store
      (cursorDivision numerator denominator division) other divisionFree)

/-- Its actual event list contains the original-width division, product and sum in that order. -/
lemma nativeCandidatePrefix_eventTrace
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (candidatePrefix (model := model) numerator denominator previous older
      division candidate).Path) :
    (candidatePrefix (model := model) numerator denominator previous older
      division candidate).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.divRem width width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width))] := by
  simp only [candidatePrefix, Circuit.eventTrace, BitWord.bitWord_instruction_eventTrace,
    nativeScopedContinuant_eventTrace, continuantEvents]
  rfl

/-- The three actual dependent arithmetic instructions have unit depth three. -/
lemma nativeCandidatePrefix_unitDepth
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (candidatePrefix (model := model) numerator denominator previous older
      division candidate).Path) :
    (candidatePrefix (model := model) numerator denominator previous older
      division candidate).depth
      (fun _ => 1) path = 3 := by
  rcases path with ⟨divisionPath, continuantPath⟩
  simp only [candidatePrefix, Circuit.depth_seq, BitWord.bitWord_instruction_depth,
    nativeScopedContinuant_unitDepth]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
