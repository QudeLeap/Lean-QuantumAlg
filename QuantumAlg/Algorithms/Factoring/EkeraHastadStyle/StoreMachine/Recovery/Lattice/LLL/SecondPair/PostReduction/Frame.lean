/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.PostReduction

/-!
# Actual final-reduction write frames

The original phase separation is sufficient to reuse named-cell preservation
from the second-pair prefix. The final reduction needs no unrelated prefix
phase contract or extra input premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The two actual writes of the refreshed first-direction numerator. -/
def refreshCells : List LatticeSecondPairMachine.TransitionCell := [.g31, .refreshG21Product]

/-- The original six mutable identities of the second rounded-division package. -/
def divisionCells : List LatticeSecondPairMachine.TransitionCell :=
  [.division31 .magnitude, .division31 .negative, .division31 .wideNumerator,
    .division31 .wideDenominator, .division31 .division, .division31 .output]

/-- All actual final-reduction writes, using the same original third-row mutable identities. -/
def mutableCells : List LatticeSecondPairMachine.TransitionCell :=
  refreshCells ++ divisionCells ++ LatticeSecondPairMachine.reductionCells

/-- Actual dot refresh preserves all reads outside its two written words. -/
theorem refresh_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : LatticeSecondPairMachine.FrameAvoids refs.machine refreshCells other) :
    (LatticeDotRefresh.refreshStore refs.machine.basis.third refs.machine.basis.first
      (refreshG31Refs refs) store).read other = store.read other :=
  LatticeDotRefresh.refreshInto_callerFrame _ _ _ _ other
    (avoids .g31 (by decide)) (avoids .refreshG21Product (by decide))

/-- Actual final-direction division preserves reads outside its original six mutable cells. -/
theorem division_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : LatticeSecondPairMachine.FrameAvoids refs.machine divisionCells other) :
    (RoundedDiv.bodyStep (model := model) refs.machine.division31 store).1.read other =
      store.read other := by
  apply RoundedDiv.body_callerFrame refs.machine.division31 store other
  intro key member
  change key ∈ divisionCells.map (LatticeSecondPairMachine.cellKey refs.machine) at member
  obtain ⟨cell, cellMember, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact avoids cell cellMember

/-- Actual final row subtraction preserves reads outside the original four mutable words. -/
theorem reduction_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : LatticeSecondPairMachine.FrameAvoids refs.machine
      LatticeSecondPairMachine.reductionCells other) :
    (LatticeArithmetic.pointStore (writeInput refs.machine.division31.output)
      refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct store).read
        other = store.read other :=
  LatticeArithmetic.pointReduce_callerFrame _ _ _ _ _ other
    (avoids .reduceProduct (by decide)) (avoids .b31 (by decide))
    (avoids .b32 (by decide)) (avoids .b33 (by decide))

/-- Complete actual final reduction preserves every read outside the union of its written cells. -/
theorem postReductionInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : LatticeSecondPairMachine.FrameAvoids refs.machine mutableCells other) :
    (postReductionStep (model := model) refs store).1.read other = store.read other := by
  have refresh : LatticeSecondPairMachine.FrameAvoids refs.machine refreshCells other :=
    fun cell member => avoids cell (by simp [mutableCells, member])
  have division : LatticeSecondPairMachine.FrameAvoids refs.machine divisionCells other :=
    fun cell member => avoids cell (by simp [mutableCells, member])
  have reduction : LatticeSecondPairMachine.FrameAvoids refs.machine
      LatticeSecondPairMachine.reductionCells other :=
    fun cell member => avoids cell (by simp [mutableCells, member])
  change (LatticeArithmetic.pointStore (writeInput refs.machine.division31.output)
    refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct
    (RoundedDiv.bodyStep (model := model) refs.machine.division31 (LatticeDotRefresh.refreshStore
      refs.machine.basis.third refs.machine.basis.first
        (refreshG31Refs refs) store)).1).read other = _
  rw [reduction_frame refs _ other reduction, division_frame refs _ other division,
    refresh_frame refs _ other refresh]

/-- The final reduction retains the original first norm word exactly. -/
theorem postReductionInto_g11 {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (postReductionStep (model := model) refs store).1.read
      (writeInput refs.machine.metric.g11) =
      store.read (writeInput refs.machine.metric.g11) :=
  postReductionInto_callerFrame refs store _
    (LatticeSecondPairMachine.metric_avoids refs.machine separation.phase .g11 mutableCells
      (by decide))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction
