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

/-- The actual division precedes the continuant update using its retained quotient. -/
def candidatePrefix (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (cursorDivision numerator denominator division))
    (scopedContinuant (.first (cellRead division)) previous older candidate)

/-- Concrete store and actual three-operation path after the candidate prefix. -/
def candidatePrefixStep
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (candidatePrefix numerator denominator previous older division candidate).Path :=
  let divided := store.applyOp (cursorDivision numerator denominator division)
  let materialized := scopedContinuantStep (.first (cellRead division)) previous older
    candidate divided
  (materialized.1, ((), materialized.2))

/-- The actual prefix composes division and materialization on the same complete state. -/
theorem nativeCandidatePrefix_execute
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidatePrefix numerator denominator previous older division candidate).execute
        Reference state =
      state.mapClassical (fun entry =>
        ((candidatePrefixStep numerator denominator previous older division candidate entry.1).1,
          (entry.2,
            (candidatePrefixStep numerator denominator previous older division candidate
              entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (.classical (cursorDivision numerator denominator division))
    (scopedContinuant (.first (cellRead division)) previous older candidate)
    (fun store => (store.applyOp (cursorDivision numerator denominator division), ()))
    (scopedContinuantStep (.first (cellRead division)) previous older candidate)
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical
        (cursorDivision numerator denominator division) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (nativeScopedContinuant_execute (.first (cellRead division)) previous older candidate)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual written candidate uses the real quotient and the original predecessor words. -/
theorem nativeCandidatePrefix_result
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (previousFree : division.key ∉ previous.storageKeys)
    (olderFree : division.key ∉ older.storageKeys) (store : Store ctx) :
    ((candidatePrefixStep numerator denominator previous older division candidate store).1).read
        (cellRead candidate) =
      continuantValue (CShape.divRem width width
        (.product (store.read numerator) (store.read denominator))).first
        (store.read previous) (store.read older) := by
  unfold candidatePrefixStep
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
theorem nativeCandidatePrefix_read_other
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (divisionFree : division.key ∉ other.storageKeys)
    (candidateFree : candidate.key ∉ other.storageKeys) (store : Store ctx) :
    ((candidatePrefixStep numerator denominator previous older division candidate store).1).read
      other = store.read other :=
  (nativeScopedContinuant_read_other (.first (cellRead division)) previous older candidate
    other candidateFree (store.applyOp (cursorDivision numerator denominator division))).trans
    (Store.read_applyOp_of_not_mem_storageKeys store
      (cursorDivision numerator denominator division) other divisionFree)

/-- Its actual event list contains the original-width division, product and sum in that order. -/
theorem nativeCandidatePrefix_eventTrace
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (candidatePrefix numerator denominator previous older division candidate).Path) :
    (candidatePrefix numerator denominator previous older division candidate).eventTrace path =
      [.classicalOperation (.divRem width width), .classicalOperation (.wordBinary .mulLow width),
        .classicalOperation (.wordBinary .add width)] := rfl

/-- The three actual dependent arithmetic instructions have unit depth three. -/
theorem nativeCandidatePrefix_unitDepth
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (candidatePrefix numerator denominator previous older division candidate).Path) :
    (candidatePrefix numerator denominator previous older division candidate).depth
      (fun _ => 1) path = 3 := rfl

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
