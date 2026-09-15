/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Correctness

/-!
# Actual source-to-LLL native resources

The independent formulas include original sample decoding, source-basis and
target loading, Gram refresh, phase reset and the actual selected fixed-fuel
steps. All original context storage and borrowed-reference correlations remain.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Independent native source-basis and selected target instruction formula. -/
def decodeTargetTrace (N : Nat) (bits : List Bool × List Bool) (negates : Bool × Bool) :
    List (Resource.Event kind) :=
  LatticeWideInitializationPrefix.decodeBasisTrace N bits.1 bits.2 ++
    LatticeWideTargetMachine.targetTrace (shortLogBits N) (tradeoffBits N) (Width N)
      negates.1 negates.2

/-- Original terminal outcomes represented in an actual decoder-target execution path. -/
def decodedBits (refs : Refs ctx N) (path : (decodeTargetInto refs).Path) : List Bool × List Bool :=
  (BatchMachine.decodeBits refs.initialization.pair.first path.1.1.1,
    BatchMachine.decodeBits refs.initialization.pair.second path.1.1.2)

/-- Actual arithmetic arms selected by the two stored centered-coordinate comparisons. -/
def targetNegations (refs : Refs ctx N) (path : (decodeTargetInto refs).Path) : Bool × Bool :=
  (LatticeTarget.selectedNegation refs.target.target.first path.2.2.1.2,
    LatticeTarget.selectedNegation refs.target.target.second path.2.2.2.2)

/-- The actual source-and-target path emits the independently selected native formula. -/
theorem decodeTargetInto_events (refs : Refs ctx N) (path : (decodeTargetInto refs).Path) :
    (decodeTargetInto refs).eventTrace path =
      decodeTargetTrace N (decodedBits refs path) (targetNegations refs path) :=
  congrArg₂ List.append
    (LatticeWideInitializationPrefix.decodeBasisInto_events (prefixRefs refs) path.1)
    (LatticeWideTargetMachine.loadTargetInto_events refs.target path.2)

/-- Independent initialization formula after original source and target loading. -/
def initializeTrace (N : Nat) (bits : List Bool × List Bool) (negates : Bool × Bool) :
    List (Resource.Event kind) :=
  decodeTargetTrace N bits negates ++ LatticeFixedFuelMachine.refreshResetTrace (Width N)

/-- Actual source-to-LLL initialization emits its independent complete native formula. -/
theorem initializeWideInto_events (refs : Refs ctx N) (path : (initializeWideInto refs).Path) :
    (initializeWideInto refs).eventTrace path =
      initializeTrace N (decodedBits refs path.1) (targetNegations refs path.1) :=
  congrArg₂ List.append (decodeTargetInto_events refs path.1)
    (LatticeFixedFuelMachine.refreshResetInto_events refs.initialization.driver path.2)

/-- Independent complete formula at the original prescribed public recovery fuel. -/
def pairToLllTrace (N : Nat) (bits : List Bool × List Bool) (negates : Bool × Bool)
    (decisions : Fin (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) →
      LatticeFixedFuelMachine.StepDecisions) : List (Resource.Event kind) :=
  decodeTargetTrace N bits negates ++ (LatticeFixedFuelMachine.refreshResetTrace (Width N) ++
    LatticeFixedFuelMachine.fixedFuelTrace
      (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) (Width N) decisions)

/-- Actual source loading, initialization and selected iterations emit one native formula. -/
theorem pairToLllInto_events (refs : Refs ctx N) (path : (pairToLllInto refs).Path) :
    (pairToLllInto refs).eventTrace path =
      pairToLllTrace N (decodedBits refs path.1) (targetNegations refs path.1)
        (fun index => LatticeFixedFuelMachine.stepDecisions refs.initialization.driver
          (path.2.2 index)) :=
  congrArg₂ List.append (decodeTargetInto_events refs path.1)
    (LatticeFixedFuelMachine.initializedInto_events
      (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
      refs.initialization.driver path.2)

/-- Actual native multiplicities equal the independently selected complete source-to-LLL formula. -/
theorem pairToLllInto_resourcePool (refs : Refs ctx N) (path : (pairToLllInto refs).Path) :
    (pairToLllInto refs).resourcePool path = ResourcePool.ofList
      (pairToLllTrace N (decodedBits refs path.1) (targetNegations refs path.1)
        (fun index => LatticeFixedFuelMachine.stepDecisions refs.initialization.driver
          (path.2.2 index))) :=
  congrArg ResourcePool.ofList (pairToLllInto_events refs path)

/-- Independent operation budget for original decoding, basis loading and target centering. -/
def decodeTargetOperationBound (N : Nat) : Nat :=
  LatticeWideInitializationPrefix.operationBound N + (2 * shortLogBits N + 16)

/-- Independent full source-to-LLL operation budget at the original public recovery fuel. -/
def operationBound (N : Nat) : Nat :=
  decodeTargetOperationBound N +
    (32 + 130 * RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))

/-- Actual source-and-target loading obeys the full independent native count budget. -/
theorem decodeTargetInto_eventCount_le (refs : Refs ctx N)
    (path : (decodeTargetInto refs).Path) :
    ((decodeTargetInto refs).eventTrace path).length ≤ decodeTargetOperationBound N := by
  have prefixCount := LatticeWideInitializationPrefix.decodeBasisInto_eventCount_le
    (prefixRefs refs) path.1
  have target := LatticeWideTargetMachine.loadTargetInto_eventCount_le refs.target path.2
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add prefixCount target

/-- The actual source-to-LLL run obeys the independent complete native count budget. -/
theorem pairToLllInto_eventCount_le (refs : Refs ctx N) (path : (pairToLllInto refs).Path) :
    ((pairToLllInto refs).eventTrace path).length ≤ operationBound N := by
  have decoded := decodeTargetInto_eventCount_le refs path.1
  have initialized := LatticeFixedFuelMachine.initializedInto_eventCount_le
    (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) refs.initialization.driver path.2
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add decoded initialized

/-- Source-and-target unit-duration depth includes all original chronological dependencies. -/
theorem decodeTargetInto_depth_le (refs : Refs ctx N) (path : (decodeTargetInto refs).Path) :
    (decodeTargetInto refs).depth (fun _ => 1) path ≤ decodeTargetOperationBound N :=
  Nat.add_le_add (LatticeWideInitializationPrefix.decodeBasisInto_depth_le (prefixRefs refs) path.1)
    (LatticeWideTargetMachine.loadTargetInto_depth_le refs.target path.2)

/-- Full unit-duration depth includes source loading, initialization and every selected step. -/
theorem pairToLllInto_depth_le (refs : Refs ctx N) (path : (pairToLllInto refs).Path) :
    (pairToLllInto refs).depth (fun _ => 1) path ≤ operationBound N :=
  Nat.add_le_add (decodeTargetInto_depth_le refs path.1)
    (LatticeFixedFuelMachine.initializedInto_depth_le
      (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
      refs.initialization.driver path.2)

/-- Actual source and target loading preserve every original borrowed-reference correlation. -/
theorem decodeTargetInto_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (decodeTargetInto refs).BorrowedRestored Reference state
      ((decodeTargetInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeWideInitializationPrefix.decodeBasisInto_borrowedRestored (prefixRefs refs)
      Reference state)
    (LatticeWideTargetMachine.loadTargetInto_borrowedRestored refs.target Reference _)

/-- The actual complete source-to-LLL run restores the full borrowed-reference joint state. -/
theorem pairToLllInto_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pairToLllInto refs).BorrowedRestored Reference state
      ((pairToLllInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (decodeTargetInto_borrowedRestored refs Reference state)
    (LatticeFixedFuelMachine.initializedInto_borrowedRestored
      (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
      refs.initialization.driver Reference _)

/-- Every actual source and target instruction retains the complete original supplied context. -/
theorem decodeTargetInto_visited (refs : Refs ctx N) (path : (decodeTargetInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (decodeTargetInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim
    (LatticeWideInitializationPrefix.decodeBasisInto_visited (prefixRefs refs) path.1 visited)
    (LatticeWideTargetMachine.loadTargetInto_visited refs.target path.2 visited)

/-- Every actual instruction in the complete source-to-LLL run retains the original full context. -/
theorem pairToLllInto_visited (refs : Refs ctx N) (path : (pairToLllInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (pairToLllInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim (decodeTargetInto_visited refs path.1 visited)
    (LatticeFixedFuelMachine.initializedInto_visited
      (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
      refs.initialization.driver path.2 visited)

/-- Actual source-to-LLL resident accounting retains every originally supplied runtime entry. -/
theorem pairToLllInto_resident_le (refs : Refs ctx N) (path : (pairToLllInto refs).Path) :
    (pairToLllInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [pairToLllInto_visited refs path visited present]

/-- Actual source-to-LLL auxiliary accounting retains every original runtime workspace role. -/
theorem pairToLllInto_auxiliary_le (refs : Refs ctx N) (path : (pairToLllInto refs).Path) :
    (pairToLllInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [pairToLllInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine
