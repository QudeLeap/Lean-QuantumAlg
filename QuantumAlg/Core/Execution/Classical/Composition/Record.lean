/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Exact records of the existing sequential instruction

The record uses the actual first store, actual second store and chronological
paths. Its interpreter theorem is proved with abstract component path types,
so a caller can compose a large fixed program without elaborating its full
finite path at every composition site. There is no additional interpreter.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Record two existing actual component updates on their real intermediate store. -/
def sequenceRecord (first second : Circuit ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path) (store : Store ctx) :
    Store ctx × (Circuit.seq first second).Path :=
  let head := firstStep store
  let tail := secondStep head.1
  (tail.1, (head.2, tail.2))

/-- The actual sequential record returns the second component's real caller store. -/
theorem sequenceRecord_store (first second : Circuit ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path) (store : Store ctx) :
    (sequenceRecord first second firstStep secondStep store).1 =
      (secondStep (firstStep store).1).1 := rfl

/-- Two proved component equations give the complete record of their existing real sequence. -/
theorem execute_sequenceRecord (first second : Circuit ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      letI : DecidableEq (Store ctx) := Classical.decEq _
      letI : DecidableEq History := Classical.decEq _
      letI : DecidableEq first.Path := Classical.decEq _
      first.execute Reference state = state.mapClassical (fun entry =>
        ((firstStep entry.1).1, (entry.2, (firstStep entry.1).2))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      letI : DecidableEq (Store ctx) := Classical.decEq _
      letI : DecidableEq History := Classical.decEq _
      letI : DecidableEq second.Path := Classical.decEq _
      second.execute Reference state = state.mapClassical (fun entry =>
        ((secondStep entry.1).1, (entry.2, (secondStep entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    letI : DecidableEq (Store ctx) := Classical.decEq _
    letI : DecidableEq History := Classical.decEq _
    letI : DecidableEq (Circuit.seq first second).Path := Classical.decEq _
    (Circuit.seq first second).execute Reference state = state.mapClassical (fun entry =>
      ((sequenceRecord first second firstStep secondStep entry.1).1,
        (entry.2, (sequenceRecord first second firstStep secondStep entry.1).2))) := by
  refine (execute_seq_mapClassical first second firstStep secondStep firstEquation secondEquation
    Reference state).trans ?_
  dsimp only [sequenceRecord]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Circuit
