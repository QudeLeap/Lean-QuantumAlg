/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Offset.Loading

/-!
# Actual original offset-loading resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeOffsetMaterializer

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent original signed native formulas in first, second and third coordinate order. -/
def offsetTrace (width : Nat) (offset : NumberTheory.IntegerPoint3) : List (Resource.Event kind) :=
  ClassicalRoutines.ConstantWord.Signed.nativeTrace width offset.1 ++
    (ClassicalRoutines.ConstantWord.Signed.nativeTrace width offset.2.1 ++
      ClassicalRoutines.ConstantWord.Signed.nativeTrace width offset.2.2)

/-- Every actual offset path emits the independently specified original signed-loading formula. -/
theorem setOffsetInto_events (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (path : (setOffsetInto offset refs).Path) :
    (setOffsetInto offset refs).eventTrace path = offsetTrace width offset :=
  congrArg₂ List.append
    (ClassicalRoutines.ConstantWord.Signed.into_events offset.1 refs.offset.first path.1)
    (congrArg₂ List.append
      (ClassicalRoutines.ConstantWord.Signed.into_events offset.2.1 refs.offset.second path.2.1)
      (ClassicalRoutines.ConstantWord.Signed.into_events offset.2.2 refs.offset.third path.2.2))

/-- Actual multiplicities include every coordinate initialization and original signed unit step. -/
theorem setOffsetInto_resourcePool (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (path : (setOffsetInto offset refs).Path) :
    (setOffsetInto offset refs).resourcePool path =
      ResourcePool.ofList (offsetTrace width offset) :=
  congrArg ResourcePool.ofList (setOffsetInto_events offset refs path)

/-- Original three self-initializations and the three signed absolute-value loops. -/
def operationCount (offset : NumberTheory.IntegerPoint3) : Nat :=
  offset.1.natAbs + offset.2.1.natAbs + offset.2.2.natAbs + 3

/-- Actual native count equals the independent offset magnitude formula. -/
theorem setOffsetInto_eventCount (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (path : (setOffsetInto offset refs).Path) :
    ((setOffsetInto offset refs).eventTrace path).length = operationCount offset := by
  rw [setOffsetInto_events]
  simp only [offsetTrace, ClassicalRoutines.ConstantWord.Signed.nativeTrace,
    ClassicalRoutines.ConstantWord.Signed.loopTrace, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil, operationCount]
  omega

/-- The same independent magnitude formula charges all actual sequential dependencies. -/
theorem setOffsetInto_depth (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (path : (setOffsetInto offset refs).Path) :
    (setOffsetInto offset refs).depth (fun _ => 1) path = operationCount offset := by
  change (ClassicalRoutines.ConstantWord.Signed.into offset.1 refs.offset.first).depth
    (fun _ => 1) path.1 +
      ((ClassicalRoutines.ConstantWord.Signed.into offset.2.1 refs.offset.second).depth
        (fun _ => 1) path.2.1 +
        (ClassicalRoutines.ConstantWord.Signed.into offset.2.2 refs.offset.third).depth
          (fun _ => 1) path.2.2) = _
  rw [ClassicalRoutines.ConstantWord.Signed.into_depth,
    ClassicalRoutines.ConstantWord.Signed.into_depth,
    ClassicalRoutines.ConstantWord.Signed.into_depth]
  unfold operationCount
  omega

/-- Actual second and third coordinate loading restore all borrowed-reference correlations. -/
theorem suffixInto_borrowedRestored (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (suffixInto offset refs).BorrowedRestored Reference state
      ((suffixInto offset refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (ClassicalRoutines.ConstantWord.Signed.into_borrowedRestored offset.2.1 refs.offset.second
      Reference state)
    (ClassicalRoutines.ConstantWord.Signed.into_borrowedRestored offset.2.2 refs.offset.third
      Reference _)

/-- Complete actual offset loading restores the full borrowed-reference joint state. -/
theorem setOffsetInto_borrowedRestored (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (setOffsetInto offset refs).BorrowedRestored Reference state
      ((setOffsetInto offset refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (ClassicalRoutines.ConstantWord.Signed.into_borrowedRestored offset.1 refs.offset.first
      Reference state)
    (suffixInto_borrowedRestored offset refs Reference _)

/-- Every actual initialization, unit step and loop boundary retains the original context. -/
theorem setOffsetInto_visited (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (path : (setOffsetInto offset refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (setOffsetInto offset refs).visitedContexts path) : visited = ctx := by
  change visited ∈
    (ClassicalRoutines.ConstantWord.Signed.into offset.1 refs.offset.first).visitedContexts
      path.1 ++
      ((ClassicalRoutines.ConstantWord.Signed.into offset.2.1 refs.offset.second).visitedContexts
        path.2.1 ++
        (ClassicalRoutines.ConstantWord.Signed.into offset.2.2 refs.offset.third).visitedContexts
          path.2.2) at present
  simp only [List.mem_append] at present
  exact present.elim
    (ClassicalRoutines.ConstantWord.Signed.into_visited offset.1 refs.offset.first path.1 visited)
    (fun suffix => suffix.elim
      (ClassicalRoutines.ConstantWord.Signed.into_visited offset.2.1 refs.offset.second
        path.2.1 visited)
      (ClassicalRoutines.ConstantWord.Signed.into_visited offset.2.2 refs.offset.third
        path.2.2 visited))

/-- Resident accounting keeps the original three offset words and all other supplied resources. -/
theorem setOffsetInto_resident_le (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (path : (setOffsetInto offset refs).Path) :
    (setOffsetInto offset refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [setOffsetInto_visited offset refs path visited present]

/-- Auxiliary accounting preserves the original roles without allocating additional cells. -/
theorem setOffsetInto_auxiliary_le (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (path : (setOffsetInto offset refs).Path) :
    (setOffsetInto offset refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [setOffsetInto_visited offset refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeOffsetMaterializer
