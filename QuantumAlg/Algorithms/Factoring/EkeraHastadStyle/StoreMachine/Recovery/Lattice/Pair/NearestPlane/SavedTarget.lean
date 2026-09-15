/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Layout

/-!
# Actual original-target copy followed by nearest-plane execution

Original source-to-LLL execution precedes a three-word target copy. The actual
copy store feeds the actual nearest-plane suffix, preserving the target in the
original independent saved cells before computing the target residual in place.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Original source conditions suffice; the nearest-plane scratch is explicitly initialized. -/
abbrev InitialConditions (store : Store ctx) (refs : Refs ctx N) : Prop :=
  LatticeWideLllMachine.InitialConditions store refs.pairNearest.wide

/-- The original mathematical samples from the actual incoming measurement cells. -/
def sourceSamples (refs : Refs ctx N) (store : Store ctx) :
    RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) ×
      RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) :=
  LatticeWideLllMachine.sourceSamples refs.pairNearest.wide store

/-- Three actual native copies preserve the original loaded target in the original saved cells. -/
def copyInto (refs : Refs ctx N) : Circuit ctx ctx :=
  LatticeRows.pointCopy refs.pairNearest.wide.target.target.point refs.savedTarget

/-- The exact store after the original target's three actual word copies. -/
def copyStore (refs : Refs ctx N) (store : Store ctx) : Store ctx :=
  LatticeRows.pointCopyStore refs.pairNearest.wide.target.target.point refs.savedTarget store

/-- Complete actual copy store and all three native instruction paths. -/
def copyStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (copyInto refs).Path :=
  (copyStore refs store, ((), ((), ())))

/-- Actual three-word target copying retains every incoming state block and original history. -/
theorem copyInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (copyInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((copyStep refs entry.1).1, (entry.2, (copyStep refs entry.1).2))) := by
  refine (LatticeRows.pointCopy_execute refs.pairNearest.wide.target.target.point refs.savedTarget
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual saved-target copy precedes actual in-place nearest-plane reduction. -/
def copyNearestInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (copyInto refs) (LatticeNearestPlaneThree.threeInto (nearestRefs refs))

/-- The actual copy result feeds the actual nearest-plane suffix and both chronological paths. -/
def copyNearestStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (copyNearestInto refs).Path :=
  let copied := copyStep refs store
  let nearest := LatticeNearestPlaneThree.threeStep (nearestRefs refs) copied.1
  (nearest.1, (copied.2, nearest.2))

/-- Actual target copying and nearest plane retain the complete incoming execution state. -/
theorem copyNearestInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (copyNearestInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((copyNearestStep refs entry.1).1, (entry.2, (copyNearestStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (copyInto refs)
    (LatticeNearestPlaneThree.threeInto (nearestRefs refs)) (copyStep refs)
    (LatticeNearestPlaneThree.threeStep (nearestRefs refs)) (copyInto_execute refs)
    (LatticeNearestPlaneThree.threeInto_execute (nearestRefs refs)) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Original source-to-LLL execution, actual saved-target copy and actual nearest plane in order. -/
def pairToNearestPlaneSavedTargetInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticeWideLllMachine.pairToLllInto refs.pairNearest.wide) (copyNearestInto refs)

/-- The complete actual stores and chronological paths of all three original stages. -/
def savedTargetStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (pairToNearestPlaneSavedTargetInto refs).Path :=
  let wide := LatticeWideLllMachine.pairToLllStep refs.pairNearest.wide store
  let nearest := copyNearestStep refs wide.1
  (nearest.1, (wide.2, nearest.2))

/-- The complete actual source-to-saved-target run preserves all incoming reference correlations. -/
theorem pairToNearestPlaneSavedTargetInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pairToNearestPlaneSavedTargetInto refs).execute Reference state =
      state.mapClassical (fun entry =>
        ((savedTargetStep refs entry.1).1, (entry.2, (savedTargetStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeWideLllMachine.pairToLllInto refs.pairNearest.wide) (copyNearestInto refs)
    (LatticeWideLllMachine.pairToLllStep refs.pairNearest.wide) (copyNearestStep refs)
    (LatticeWideLllMachine.pairToLllInto_execute refs.pairNearest.wide)
    (copyNearestInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual saved-target copy preserves every read outside the three saved word identities. -/
theorem copy_callerFrame (refs : Refs ctx N) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (separate : PointCopyFrameAvoids refs.savedTarget other) :
    (copyStore refs store).read other = store.read other :=
  LatticeRows.pointCopy_callerFrame refs.pairNearest.wide.target.target.point refs.savedTarget
    store other separate.first separate.second separate.third

/-- The actual nearest-plane suffix retains every read outside its original combined write set. -/
theorem savedTarget_suffixFrame (refs : Refs ctx N) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape)
    (separate : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs) other) :
    (savedTargetStep refs store).1.read other =
      (copyStore refs
        (LatticeWideLllMachine.pairToLllStep refs.pairNearest.wide store).1).read other :=
  LatticeNearestPlaneThree.threeInto_callerFrame (nearestRefs refs) _ other separate

/-- Every actual read outside the complete original three-stage footprint remains unchanged. -/
theorem pairToNearestPlaneSavedTargetInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerFrameAvoids refs other) :
    (savedTargetStep refs store).1.read other = store.read other := by
  rw [savedTarget_suffixFrame refs store other separate.nearest,
    copy_callerFrame refs _ other separate.copy,
    LatticeWideLllMachine.pairToLllInto_callerFrame refs.pairNearest.wide store other separate.wide]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget
