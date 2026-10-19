/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Eliminate
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual selected-pivot elimination resources

Each target emits either no event or one original vector-row XOR. Static
pivot skipping and all stored-bit decisions remain in the same path. The
ordered pass is serial and uses precisely its original context, without
allocating a cell. The count bound is a uniform allowance, not an asserted
tight maximum over correlated matrix decisions.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The original native vector-row XOR coordinate, at its actual matrix dimensions. -/
def eliminationEvent (rowCount width : Nat) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.vector .rowXor rowCount width))

private lemma target_selectedTrace
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (eliminateTarget matrix pivot target column).Path) :
    ∃ active : Bool,
      (eliminateTarget matrix pivot target column).eventTrace path =
        (if active then [eliminationEvent (model := model) rowCount width] else []) ∧
      (eliminateTarget matrix pivot target column).depth duration path =
        (if active then duration (eliminationEvent (model := model) rowCount width) else 0) ∧
      (eliminateTarget matrix pivot target column).visitedContexts path = [ctx] := by
  revert path
  dsimp only [eliminateTarget]
  cases decision : instDecidableEqFin rowCount target pivot with
  | isTrue _ =>
      intro path
      exact ⟨false, rfl, rfl, rfl⟩
  | isFalse _ =>
      rintro ⟨value, branchPath⟩
      cases value with
      | bit bit =>
          cases bit
          · exact ⟨false, rfl, rfl, rfl⟩
          · change (BitWord.instruction (execution := model)
              (eliminationXorOp matrix pivot target)).Path at branchPath
            refine ⟨true, ?_, ?_, rfl⟩
            · change (BitWord.instruction (execution := model)
                (eliminationXorOp matrix pivot target)).eventTrace branchPath =
                  [eliminationEvent (model := model) rowCount width]
              rw [BitWord.bitWord_instruction_eventTrace]
              rfl
            · change (BitWord.instruction (execution := model)
                (eliminationXorOp matrix pivot target)).depth duration branchPath =
                  duration (eliminationEvent (model := model) rowCount width)
              rw [BitWord.bitWord_instruction_depth]
              rfl

/-- One actual target emits at most the original single row-XOR event. -/
lemma gf2EliminateTarget_pool_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width)
    (path : (eliminateTarget matrix pivot target column).Path) :
    (eliminateTarget matrix pivot target column).resourcePool path ≤
      ResourcePool.singleton (eliminationEvent (model := model) rowCount width) := by
  obtain ⟨active, trace, _, _⟩ := target_selectedTrace matrix pivot target column (fun _ => 1) path
  change ResourcePool.ofList _ ≤ _
  rw [trace]
  cases active
  · exact zero_le
  · exact le_rfl

/-- The same target's actual dependency depth is bounded by its one possible instruction. -/
lemma gf2EliminateTarget_depth_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (eliminateTarget matrix pivot target column).Path) :
    (eliminateTarget matrix pivot target column).depth duration path ≤
      duration (eliminationEvent (model := model) rowCount width) := by
  obtain ⟨active, _, depth, _⟩ := target_selectedTrace matrix pivot target column duration path
  rw [depth]
  cases active
  · exact Nat.zero_le _
  · exact le_rfl

/-- Actual serial depth is exactly the sum of the target's emitted event durations. -/
lemma gf2EliminateTarget_duration_eventTrace
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (eliminateTarget matrix pivot target column).Path) :
    (eliminateTarget matrix pivot target column).depth duration path =
      (((eliminateTarget matrix pivot target column).eventTrace path).map duration).sum := by
  obtain ⟨active, trace, depth, _⟩ := target_selectedTrace matrix pivot target column duration path
  rw [trace, depth]
  cases active <;> simp only [Bool.false_eq_true, if_false, if_true,
    List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.add_zero]

/-- No target branch allocates or removes any resident entry. -/
lemma gf2EliminateTarget_resident
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width)
    (path : (eliminateTarget matrix pivot target column).Path) :
    (eliminateTarget matrix pivot target column).peakResidentSpace path = ctx.residentSpace := by
  obtain ⟨_, _, _, visited⟩ := target_selectedTrace matrix pivot target column (fun _ => 1) path
  change Circuit.peak RuntimeCtx.residentSpace _ = _
  rw [visited]
  exact SpacePool.max_zero _

/-- Every original auxiliary entry remains live, with no additional target scratch. -/
lemma gf2EliminateTarget_auxiliary
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width)
    (path : (eliminateTarget matrix pivot target column).Path) :
    (eliminateTarget matrix pivot target column).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  obtain ⟨_, _, _, visited⟩ := target_selectedTrace matrix pivot target column (fun _ => 1) path
  change Circuit.peak RuntimeCtx.auxiliarySpace _ = _
  rw [visited]
  exact SpacePool.max_zero _

/-- The real increasing target pass has at most one row-XOR allowance per original row. -/
lemma gf2EliminateWithPivot_pool_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width)
    (path : (eliminateWithPivot matrix pivot column).Path) :
    (eliminateWithPivot matrix pivot column).resourcePool path ≤
      ResourcePool.scale rowCount
        (ResourcePool.singleton (eliminationEvent (model := model) rowCount width)) :=
  Circuit.forRange_pool_le rowCount _ _
    (fun target => gf2EliminateTarget_pool_le matrix pivot target column) path

/-- The full original target order adds the possible dependency duration of every row. -/
lemma gf2EliminateWithPivot_depth_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (eliminateWithPivot matrix pivot column).Path) :
    (eliminateWithPivot matrix pivot column).depth duration path ≤
      rowCount * duration (eliminationEvent (model := model) rowCount width) := by
  change (Circuit.forRange rowCount
    (fun target => eliminateTarget matrix pivot target column)).depth duration path ≤ _
  simpa only [Finset.sum_const, Finset.card_fin, smul_eq_mul] using
    Circuit.forRange_depth_le_sum rowCount
      (fun target => eliminateTarget matrix pivot target column) duration
      (fun _ => duration (eliminationEvent (model := model) rowCount width))
      (fun target => gf2EliminateTarget_depth_le matrix pivot target column duration) path

/-- The same complete path keeps exact serial event-duration accounting. -/
lemma gf2EliminateWithPivot_duration_eventTrace
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (eliminateWithPivot matrix pivot column).Path) :
    (eliminateWithPivot matrix pivot column).depth duration path =
      (((eliminateWithPivot matrix pivot column).eventTrace path).map duration).sum :=
  Circuit.forRange_duration_eventTrace rowCount _ duration
    (fun target => gf2EliminateTarget_duration_eventTrace matrix pivot target column duration) path

/-- The total number of actually emitted native events is at most the number of original rows. -/
lemma gf2EliminateWithPivot_eventCount_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width)
    (path : (eliminateWithPivot matrix pivot column).Path) :
    ((eliminateWithPivot matrix pivot column).eventTrace path).length ≤ rowCount := by
  have bound := Circuit.forRange_eventCount_le rowCount
    (fun target => eliminateTarget matrix pivot target column) 1 (by
      intro target current
      obtain ⟨active, trace, _, _⟩ :=
        target_selectedTrace matrix pivot target column (fun _ => 1) current
      rw [trace]
      cases active
      · exact Nat.zero_le _
      · exact Nat.le_refl _) path
  exact bound.trans_eq (Nat.mul_one rowCount)

/-- The full pass has precisely its original resident storage, independent of target count. -/
lemma gf2EliminateWithPivot_resident
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width)
    (path : (eliminateWithPivot matrix pivot column).Path) :
    (eliminateWithPivot matrix pivot column).peakResidentSpace path = ctx.residentSpace :=
  le_antisymm (Circuit.forRange_resident_le rowCount _ _ le_rfl
    (fun target current =>
      (gf2EliminateTarget_resident matrix pivot target column current).le) path)
    (Circuit.input_residentSpace_le_peak _ path)

/-- No target iteration increases the exact original auxiliary peak. -/
lemma gf2EliminateWithPivot_auxiliary
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width)
    (path : (eliminateWithPivot matrix pivot column).Path) :
    (eliminateWithPivot matrix pivot column).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  le_antisymm (Circuit.forRange_auxiliary_le rowCount _ _ le_rfl
    (fun target current =>
      (gf2EliminateTarget_auxiliary matrix pivot target column current).le) path)
    (Circuit.input_auxiliarySpace_le_peak _ path)

end QuantumAlg.ClassicalRoutines.GF2.Native
