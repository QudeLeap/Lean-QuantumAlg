/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.ResourceBounds
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Complete actual stage and two-stream resource bounds

All statements concern paths of the original stored-feedback/reset program.
A phase opportunity may choose the empty word. A reset performs its real
measurement and at most one native X, writing an existing result cell.
No quantum or classical workspace is allocated by these complete stages.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Resources

noncomputable section

open Execution

private lemma seq_events {ctx : RuntimeCtx .quantum}
    (first second : Circuit model ctx ctx) (path : (first.seq second).Path)
    (left right : ResourcePool model)
    (firstBound : first.resourcePool path.1 ≤ left)
    (secondBound : second.resourcePool path.2 ≤ right) :
    (first.seq second).resourcePool path ≤ left + right := by
  simpa only [Circuit.resourcePool, Circuit.eventTrace, ResourcePool.ofList_append] using
    add_le_add firstBound secondBound

private lemma seq_spaces {ctx : RuntimeCtx .quantum}
    (first second : Circuit model ctx ctx) (path : (first.seq second).Path)
    (firstBound : first.peakResidentSpace path.1 = ctx.residentSpace ∧
      first.peakAuxiliarySpace path.1 = ctx.auxiliarySpace)
    (secondBound : second.peakResidentSpace path.2 = ctx.residentSpace ∧
      second.peakAuxiliarySpace path.2 = ctx.auxiliarySpace) :
    (first.seq second).peakResidentSpace path = ctx.residentSpace ∧
      (first.seq second).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  constructor
  · rw [Circuit.peakResidentSpace_seq, firstBound.1, secondBound.1, SpacePool.max_self]
  · rw [Circuit.peakAuxiliarySpace_seq, firstBound.2, secondBound.2, SpacePool.max_self]

private lemma unitary_spaces {ctx : RuntimeCtx .quantum}
    (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (path : (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true) program).Path) :
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true) program).peakResidentSpace path = ctx.residentSpace ∧
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true) program).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  ⟨Circuit.peakResidentSpace_unitary program path,
    Circuit.peakAuxiliarySpace_unitary program path⟩

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- An actual previous-cell branch executes at most one phase. -/
lemma feedbackBit_events (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (path : (feedbackBit base noQuantum m ell width inverse separation previous).Path) :
    (feedbackBit base noQuantum m ell width inverse separation previous).resourcePool path ≤
      oneQubit := by
  change ResourcePool.ofList
    ((feedbackProgram base noQuantum m ell width inverse separation path.1).eventTrace
      BitWord.model .empty) ≤ _
  cases path.1 with
  | finite bit =>
      by_cases selected : bit.val = 1
      · simp only [feedbackProgram, selected, if_true]
        exact le_rfl
      · simp only [feedbackProgram, selected, if_false]
        change (0 : ResourcePool model) ≤ oneQubit
        exact zero_le

/-- Every chosen phase is a unitary on the same original live context. -/
lemma feedbackBit_spaces (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (path : (feedbackBit base noQuantum m ell width inverse separation previous).Path) :
    (feedbackBit base noQuantum m ell width inverse separation previous).peakResidentSpace path =
        (Context base noQuantum m ell width).residentSpace ∧
      (feedbackBit base noQuantum m ell width inverse separation previous).peakAuxiliarySpace path =
        (Context base noQuantum m ell width).auxiliarySpace :=
  unitary_spaces _ path.2

/-- The complete stored-feedback prefix has at most one phase for each earlier bit. -/
lemma feedbackPrefix_events (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (path : (feedbackPrefix base noQuantum m ell width inverse outputs position
      count bounded).Path) :
    (feedbackPrefix base noQuantum m ell width inverse outputs position
      count bounded).resourcePool path ≤ count • oneQubit := by
  induction count with
  | zero => exact le_rfl
  | succ count ih =>
      have before := ih (Nat.le_of_succ_le bounded) path.1
      have last := feedbackBit_events base noQuantum m ell width inverse
        (position.val - count - 1) (outputs ⟨count, by have bound := position.isLt; omega⟩) path.2
      simpa only [feedbackPrefix, succ_nsmul] using seq_events _ _ path _ _ before last

/-- The same stored-feedback path adds no workspace or retained output. -/
lemma feedbackPrefix_spaces (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (path : (feedbackPrefix base noQuantum m ell width inverse outputs position
      count bounded).Path) :
    (feedbackPrefix base noQuantum m ell width inverse outputs position
      count bounded).peakResidentSpace path = (Context base noQuantum m ell width).residentSpace ∧
      (feedbackPrefix base noQuantum m ell width inverse outputs position
        count bounded).peakAuxiliarySpace path =
          (Context base noQuantum m ell width).auxiliarySpace := by
  induction count with
  | zero => exact ⟨Circuit.peakResidentSpace_id path, Circuit.peakAuxiliarySpace_id path⟩
  | succ count ih =>
      exact seq_spaces _ _ path (ih (Nat.le_of_succ_le bounded) path.1)
        (feedbackBit_spaces base noQuantum m ell width inverse (position.val - count - 1)
          (outputs ⟨count, by have bound := position.isLt; omega⟩) path.2)

/-- The real reset reads once, and its exact negative shift is identity or one native X. -/
lemma measuredReset_events
    (result : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (path : (measuredReset base noQuantum m ell width result).Path) :
    (measuredReset base noQuantum m ell width result).resourcePool path ≤
      oneMeasurement + oneQubit := by
  refine (ZReset.zReset_resourcePool_le_envelope
    (operations := BitWord.model) (services := .empty)
    (control base noQuantum m ell width) (dimensionedCell base noQuantum m ell width result)
    (QuditShift.qubitRealizations (Context base noQuantum m ell width).quantumLayout
      (control base noQuantum m ell width) (control_qubit base noQuantum m ell width) .empty)
    oneQubit (fun amount => ?_) path).trans_eq ?_
  · change ResourcePool.ofList ((QuditShift.qubitShiftCircuit _ _ _ .empty amount).eventTrace
      BitWord.model .empty) ≤ _
    rw [QuditShift.qubitShiftCircuit_events _ _ _ .empty amount BitWord.model .empty]
    split_ifs
    · exact (show (0 : ResourcePool model) ≤ oneQubit from zero_le)
    · exact le_rfl
  · simp only [ZReset.eventEnvelope, control_qubit, oneMeasurement]

/-- Reset changes the existing bank and cell values without allocating any storage. -/
lemma measuredReset_spaces
    (result : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (path : (measuredReset base noQuantum m ell width result).Path) :
    (measuredReset base noQuantum m ell width result).peakResidentSpace path =
        (Context base noQuantum m ell width).residentSpace ∧
      (measuredReset base noQuantum m ell width result).peakAuxiliarySpace path =
        (Context base noQuantum m ell width).auxiliarySpace :=
  ⟨ZReset.zReset_peakResidentSpace _ _ _ path,
    ZReset.zReset_peakAuxiliarySpace _ _ _ path⟩

/-- Two actual Hadamards surround one arithmetic call and the stored feedback prefix. -/
lemma stage_events (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    (path : (stage base noQuantum m ell width inverse outputs N unit position).Path) :
    (stage base noQuantum m ell width inverse outputs N unit position).resourcePool path ≤
      stageBudget width position.val := by
  have firstH := (single_events base noQuantum m ell width Gate.HOp path.1.1).le
  have arithmetic := arithmetic_events base noQuantum m ell width N
    (unit ^ (2 ^ position.rev.val)) path.1.2.1
  have phases := feedbackPrefix_events base noQuantum m ell width inverse outputs position
    position.val le_rfl path.1.2.2.1
  have lastH := (single_events base noQuantum m ell width Gate.HOp path.1.2.2.2).le
  have reset := measuredReset_events base noQuantum m ell width (outputs position) path.2
  refine (seq_events _ _ path _ _
    (seq_events _ _ path.1 _ _ firstH
      (seq_events _ _ path.1.2 _ _ arithmetic
        (seq_events _ _ path.1.2.2 _ _ phases lastH))) reset).trans_eq ?_
  simp only [stageBudget, baseBudget, two_nsmul]
  ac_rfl

/-- The whole stage has exactly the original resident and auxiliary context peaks. -/
lemma stage_spaces (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    (path : (stage base noQuantum m ell width inverse outputs N unit position).Path) :
    (stage base noQuantum m ell width inverse outputs N unit position).peakResidentSpace path =
        (Context base noQuantum m ell width).residentSpace ∧
      (stage base noQuantum m ell width inverse outputs N unit position).peakAuxiliarySpace path =
        (Context base noQuantum m ell width).auxiliarySpace :=
  seq_spaces _ _ path
    (seq_spaces _ _ path.1 (unitary_spaces _ path.1.1)
      (seq_spaces _ _ path.1.2 (unitary_spaces _ path.1.2.1)
        (seq_spaces _ _ path.1.2.2
          (feedbackPrefix_spaces base noQuantum m ell width inverse outputs position
            position.val le_rfl path.1.2.2.1)
          (unitary_spaces _ path.1.2.2.2))))
    (measuredReset_spaces base noQuantum m ell width (outputs position) path.2)

/-- The arithmetic envelope bounds its actual time without multiplying its primitive caps. -/
lemma stage_time (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    (path : (stage base noQuantum m ell width inverse outputs N unit position).Path) :
    (stage base noQuantum m ell width inverse outputs N unit position).quantumTime path ≤
      stageTime width position.val := by
  have firstH := Circuit.depth_le_weightedCount_of_pool_le
    _ Resource.Event.quantumDuration _ path.1.1
    (single_events base noQuantum m ell width Gate.HOp path.1.1).le
  have lastH := Circuit.depth_le_weightedCount_of_pool_le
    _ Resource.Event.quantumDuration _ path.1.2.2.2
    (single_events base noQuantum m ell width Gate.HOp path.1.2.2.2).le
  have phases := Circuit.depth_le_weightedCount_of_pool_le
    _ Resource.Event.quantumDuration _ path.1.2.2.1
    (feedbackPrefix_events base noQuantum m ell width inverse outputs position
      position.val le_rfl path.1.2.2.1)
  have reset := Circuit.depth_le_weightedCount_of_pool_le
    _ Resource.Event.quantumDuration _ path.2
    (measuredReset_events base noQuantum m ell width (outputs position) path.2)
  simp only [oneQubit, oneMeasurement, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.quantumDuration, Nat.one_mul, Nat.mul_one,
    Nat.zero_add] at firstH lastH phases reset
  have arithmetic := arithmetic_time base noQuantum m ell width N
    (unit ^ (2 ^ position.rev.val)) path.1.2.1
  have total := Nat.add_le_add (Nat.add_le_add firstH
    (Nat.add_le_add arithmetic (Nat.add_le_add phases lastH))) reset
  have full :
      (stage base noQuantum m ell width inverse outputs N unit position).quantumTime path ≤
        1 + (MAU.Multiplication.Gidney.controlledTimeBound width + (position.val + 1)) + 1 := total
  unfold stageTime
  omega

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Resources
