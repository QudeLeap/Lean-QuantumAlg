/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Reset.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Resources

/-!
# Actual initialized fixed-fuel LLL execution

A represented full-rank basis first initializes its actual Gram snapshot and
phase bits, then enters the actual fixed-fuel driver. The resulting basis and
phase realize the original mathematical run from its original initial state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Initialize the original actual machine and execute the requested fixed number of iterations. -/
def initializedInto (fuel : Nat) (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (refreshResetInto refs) (fixedFuelInto fuel refs)

/-- Actual initialized store and full chronological initialization-and-loop path. -/
def initializedStep (fuel : Nat) (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (initializedInto fuel refs).Path :=
  let initialized := refreshResetStep refs store
  let result := fixedFuelStep fuel refs initialized.1
  (result.1, (initialized.2, result.2))

/-- Actual initialization feeds the actual loop without changing histories or reference blocks. -/
theorem initializedInto_execute (fuel : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (initializedInto fuel refs).execute Reference state = state.mapClassical (fun entry =>
      ((initializedStep fuel refs entry.1).1, (entry.2, (initializedStep fuel refs entry.1).2)))
        := by
  refine (Circuit.execute_seq_mapClassical (refreshResetInto refs) (fixedFuelInto fuel refs)
    (refreshResetStep refs) (fixedFuelStep fuel refs) (refreshResetInto_execute refs)
    (fixedFuelInto_execute fuel refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual initialized run needs only the original represented basis, full rank and capacity. -/
theorem initializedInto_correct (fuel : Nat) (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis)
    (fullRank : basis.FullRank)
    (capacity : Nat.size (256 * (NumberTheory.lllStateEnvelope3 basis + 1) ^ 8) + 1 ≤ width) :
    StoreInvariant refs basis (initializedStep fuel refs store).1
      (NumberTheory.lllRun3 fuel (initialState basis)) :=
  fixedFuelInto_correct fuel refs separation basis _ _
    (refreshResetInto_correct refs separation store basis rep fullRank capacity)

/-- Actual initialization and every subsequent iteration retain the original caller read frame. -/
theorem initializedInto_callerFrame (fuel : Nat) (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (initializedStep fuel refs store).1.read other = store.read other := by
  change (fixedFuelStep fuel refs (refreshResetStep refs store).1).1.read other = _
  rw [fixedFuelInto_callerFrame fuel refs _ other separate,
    refreshResetInto_callerFrame refs store other separate]

/-- The initialized run emits the independent initialization and chronological step formulas. -/
theorem initializedInto_events (fuel : Nat) (refs : Refs ctx width)
    (path : (initializedInto fuel refs).Path) :
    (initializedInto fuel refs).eventTrace path = refreshResetTrace width ++
      fixedFuelTrace fuel width (fun index => stepDecisions refs (path.2 index)) := by
  change _ ++ _ = _
  rw [refreshResetInto_events, fixedFuelInto_events]

/-- Actual native multiplicities come from the independent initialization-and-run formula. -/
theorem initializedInto_resourcePool (fuel : Nat) (refs : Refs ctx width)
    (path : (initializedInto fuel refs).Path) :
    (initializedInto fuel refs).resourcePool path = ResourcePool.ofList (refreshResetTrace width ++
      fixedFuelTrace fuel width (fun index => stepDecisions refs (path.2 index))) :=
  congrArg ResourcePool.ofList (initializedInto_events fuel refs path)

/-- Actual initialization followed by a fixed-fuel run uses at most 32 plus 130 per iteration. -/
theorem initializedInto_eventCount_le (fuel : Nat) (refs : Refs ctx width)
    (path : (initializedInto fuel refs).Path) :
    ((initializedInto fuel refs).eventTrace path).length ≤ 32 + 130 * fuel := by
  have loop := fixedFuelInto_eventCount_le fuel refs path.2
  change List.length (_ ++ _) ≤ _
  rw [List.length_append, refreshResetInto_eventCount]
  exact Nat.add_le_add_left loop 32

/-- Unit-duration depth retains initialization and all actual iteration dependencies. -/
theorem initializedInto_depth_le (fuel : Nat) (refs : Refs ctx width)
    (path : (initializedInto fuel refs).Path) :
    (initializedInto fuel refs).depth (fun _ => 1) path ≤ 32 + 130 * fuel := by
  change (refreshResetInto refs).depth (fun _ => 1) path.1 +
    (fixedFuelInto fuel refs).depth (fun _ => 1) path.2 ≤ _
  rw [refreshResetInto_depth]
  exact Nat.add_le_add_left (fixedFuelInto_depth_le fuel refs path.2) 32

/-- Actual initialization and the full loop restore the complete borrowed-reference joint state. -/
theorem initializedInto_borrowedRestored (fuel : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (initializedInto fuel refs).BorrowedRestored Reference state
      ((initializedInto fuel refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (refreshResetInto_borrowedRestored refs Reference state)
    (fixedFuelInto_borrowedRestored fuel refs Reference _)

/-- The initialized run visits only its complete original supplied context. -/
theorem initializedInto_visited (fuel : Nat) (refs : Refs ctx width)
    (path : (initializedInto fuel refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (initializedInto fuel refs).visitedContexts path) : visited = ctx := by
  change visited ∈ (_ ++ _) at present
  rcases List.mem_append.mp present with initialization | loop
  · exact refreshResetInto_visited refs path.1 visited initialization
  · exact fixedFuelInto_visited fuel refs path.2 visited loop

/-- The initialized run counts every original resident resource throughout execution. -/
theorem initializedInto_resident_le (fuel : Nat) (refs : Refs ctx width)
    (path : (initializedInto fuel refs).Path) :
    (initializedInto fuel refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [initializedInto_visited fuel refs path visited present]

/-- The initialized run counts every original auxiliary role throughout execution. -/
theorem initializedInto_auxiliary_le (fuel : Nat) (refs : Refs ctx width)
    (path : (initializedInto fuel refs).Path) :
    (initializedInto fuel refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [initializedInto_visited fuel refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
