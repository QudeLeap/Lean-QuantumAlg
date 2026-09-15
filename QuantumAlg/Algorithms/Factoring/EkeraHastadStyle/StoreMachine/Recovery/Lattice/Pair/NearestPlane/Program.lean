/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Target.Preservation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program.Resources

/-!
# Actual original-sample LLL followed by nearest-plane reduction

The actual reduced basis and retained original target feed the three actual
nearest-plane phases. All native paths and incoming reference correlations
belong to the same chronological Circuit interpretation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Caller-owned wide state and nearest-plane phase-local scratch storage. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the wide stage. -/
  wide : LatticeWideLllMachine.Refs ctx N
  /-- Nested references for the third stage. -/
  third : LatticeNearestPlaneThree.ThirdScratchRefs ctx (LatticeWideLllMachine.Width N)
  /-- Nested references for the second stage. -/
  second : LatticeNearestPlaneThree.SecondScratchRefs ctx (LatticeWideLllMachine.Width N)
  /-- Nested references for the first stage. -/
  first : LatticeNearestPlaneThree.FirstScratchRefs ctx (LatticeWideLllMachine.Width N)

/-- The nearest-plane view shares the actual wide basis and target cells. -/
def nearestRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : LatticeNearestPlaneThree.Refs ctx (LatticeWideLllMachine.Width N) where
  basis := refs.wide.initialization.driver.machine.basis
  target := refs.wide.target.target.point
  third := refs.third
  second := refs.second
  first := refs.first

/-- The local and cross-stage separation needed by the composed machine. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  wide : LatticeWideLllMachine.Separation refs.wide
  target : LatticeWideLllTargetPreservation.TargetPreservationSeparation refs.wide
  nearest : LatticeNearestPlaneThree.Separation (nearestRefs refs)

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Only the original unmodified source-basis and target-zero conditions remain at entry. -/
abbrev InitialConditions (store : Store ctx) (refs : Refs ctx N) : Prop :=
  LatticeWideLllMachine.InitialConditions store refs.wide

/-- A complete caller read lies outside both actual source-to-LLL and nearest-plane writes. -/
structure CallerSeparated (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) :
    Prop where
  wide : LatticeWideLllMachine.CallerSeparated refs.wide other
  nearest : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs) other

/-- Original source-to-LLL execution precedes actual three-coordinate nearest-plane reduction. -/
def pairToNearestPlaneInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticeWideLllMachine.pairToLllInto refs.wide)
    (LatticeNearestPlaneThree.threeInto (nearestRefs refs))

/-- The actual reduced basis and retained target store feed the actual nearest-plane suffix. -/
def pairToNearestPlaneStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (pairToNearestPlaneInto refs).Path :=
  let wide := LatticeWideLllMachine.pairToLllStep refs.wide store
  let nearest := LatticeNearestPlaneThree.threeStep (nearestRefs refs) wide.1
  (nearest.1, (wide.2, nearest.2))

/-- The complete actual composition retains every incoming state block and original history. -/
theorem pairToNearestPlaneInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pairToNearestPlaneInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((pairToNearestPlaneStep refs entry.1).1,
        (entry.2, (pairToNearestPlaneStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (LatticeWideLllMachine.pairToLllInto refs.wide)
    (LatticeNearestPlaneThree.threeInto (nearestRefs refs))
    (LatticeWideLllMachine.pairToLllStep refs.wide)
    (LatticeNearestPlaneThree.threeStep (nearestRefs refs))
    (LatticeWideLllMachine.pairToLllInto_execute refs.wide)
    (LatticeNearestPlaneThree.threeInto_execute (nearestRefs refs)) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Every actual read outside the suffix writes survives the nearest-plane call. -/
theorem pairToNearestPlaneInto_suffixFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs) other) :
    (pairToNearestPlaneStep refs store).1.read other =
      (LatticeWideLllMachine.pairToLllStep refs.wide store).1.read other :=
  LatticeNearestPlaneThree.threeInto_callerFrame (nearestRefs refs) _ other separate

/-- Every actual read outside both original component write sets survives the full run. -/
theorem pairToNearestPlaneInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (pairToNearestPlaneStep refs store).1.read other = store.read other :=
  (pairToNearestPlaneInto_suffixFrame refs store other separate.nearest).trans
    (LatticeWideLllMachine.pairToLllInto_callerFrame refs.wide store other separate.wide)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneMachine
