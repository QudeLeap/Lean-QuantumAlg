/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.ResourceBounds
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Circuit.Allocation

/-!
# Complete actual native bounds of one measured recycling stage

Bounds follow the actual H, measured arithmetic, stored feedback, H and
MZ/reset sequence. The reused vent bank and retained exponent outputs are
distinct real storage, and no child allocates another system
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources

noncomputable section

open Execution

private lemma seq_pool {ctx : RuntimeCtx .quantum}
    (first second : Circuit model ctx ctx false) (path : (first.seq second).Path)
    (left right : ResourcePool model) (firstBound : first.resourcePool path.1 ≤ left)
    (secondBound : second.resourcePool path.2 ≤ right) :
    (first.seq second).resourcePool path ≤ left + right := by
  simpa only [Circuit.resourcePool, Circuit.eventTrace, ResourcePool.ofList_append] using
    add_le_add firstBound secondBound

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- A stored prior exponent bit selects at most one actual native phase. -/
lemma measuredFeedbackBit_events (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (path : (feedbackBit base noQuantum m ell width inverse separation previous).Path) :
    (feedbackBit base noQuantum m ell width inverse separation previous).resourcePool path ≤
      oneQubit := by
  change ResourcePool.ofList
    ((feedbackProgram base noQuantum m ell width inverse separation path.1).eventTrace
      BitWord.model .empty) ≤ _
  unfold feedbackProgram
  split
  · exact le_rfl
  · exact (show (0 : ResourcePool model) ≤ oneQubit from zero_le)

/-- The actual chronological feedback prefix retains every prior-bit phase opportunity. -/
lemma measuredFeedbackPrefix_events (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (path : (feedbackPrefix base noQuantum m ell width inverse outputs position
      count bounded).Path) :
    (feedbackPrefix base noQuantum m ell width inverse outputs position
      count bounded).resourcePool path ≤ count • oneQubit := by
  induction count with
  | zero => exact le_rfl
  | succ count ih =>
      have earlier := ih (by omega) path.1
      have last := measuredFeedbackBit_events base noQuantum m ell width inverse
        (position.val - count - 1) (outputs ⟨count, by have bound := position.isLt; omega⟩) path.2
      simpa only [feedbackPrefix, succ_nsmul] using seq_pool _ _ path _ _ earlier last

/-- The original control is actually measured, with at most one selected native reset X. -/
lemma measuredControlReset_events
    (result : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (path : (measuredReset base noQuantum m ell width result).Path) :
    (measuredReset base noQuantum m ell width result).resourcePool path ≤
      oneMeasurement + oneQubit := by
  let output := MAU.Addition.Gidney.Measured.Instruction.finiteOutput
    (control_qubit base noQuantum m ell width) result
  refine (ZReset.zReset_resourcePool_le_envelope
    (allowAllocation := false) (operations := BitWord.model) (services := .empty)
    (control base noQuantum m ell width) output
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

/-- The actual arithmetic call keeps the complete independent native measured-multiplier pool. -/
lemma measuredArithmetic_events (wide : 2 ≤ width) (large : 5 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient : (ZMod modulus.toNat)ˣ)
    (path : (arithmetic base noQuantum m ell width wide modulus coefficient).Path) :
    (arithmetic base noQuantum m ell width wide modulus coefficient).resourcePool path ≤
      arithmeticBudget width :=
  MAU.Multiplication.Gidney.Measured.Layout.multiplicationCircuit_pool_bound _ wide large modulus
    positive odd _ _ _ (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width) path

/-- Every actual stage pays its complete measured arithmetic and real control feedback/reset. -/
lemma measuredStage_events (wide : 2 ≤ width) (large : 5 ≤ width)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (path : (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path) :
    (stage base noQuantum m ell width wide inverse outputs modulus unit position).resourcePool
      path ≤ stageBudget width position.val := by
  have firstH : ResourcePool.ofList ((single base noQuantum m ell width Gate.HOp).eventTrace
      BitWord.model .empty) ≤ oneQubit := le_rfl
  have lastH := firstH
  have arithmetic := measuredArithmetic_events base noQuantum m ell width wide large modulus
    positive odd (unit ^ (2 ^ position.rev.val)) path.2.1
  have phases := measuredFeedbackPrefix_events base noQuantum m ell width inverse outputs position
    position.val le_rfl path.2.2.1
  have reset := measuredControlReset_events base noQuantum m ell width (outputs position)
    path.2.2.2.2
  refine (seq_pool _ _ path _ _ firstH
    (seq_pool _ _ path.2 _ _ arithmetic (seq_pool _ _ path.2.2 _ _ phases
      (seq_pool _ _ path.2.2.2 _ _ lastH reset)))).trans_eq ?_
  simp only [stageBudget, baseBudget, two_nsmul]
  ac_rfl

private lemma stage_time_formula (width position : Nat) :
    1 + ((160 * width ^ 2 - 255 * width) + (position + (1 + 1))) =
      stageTime width position := by unfold stageTime; omega

/-- The chronological stage time retains measured arithmetic and all paid feedback gates. -/
lemma measuredStage_time (wide : 2 ≤ width) (large : 5 ≤ width)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (path : (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path) :
    (stage base noQuantum m ell width wide inverse outputs modulus unit position).quantumTime
      path ≤ stageTime width position.val := by
  have arithmetic := arithmetic_quantumTime_bound base noQuantum m ell width wide large modulus
    positive odd (unit ^ (2 ^ position.rev.val)) path.2.1
  have phases := Circuit.depth_le_weightedCount_of_pool_le
    _ Resource.Event.quantumDuration _ path.2.2.1
    (measuredFeedbackPrefix_events base noQuantum m ell width inverse outputs position
      position.val le_rfl path.2.2.1)
  have reset := Circuit.depth_le_weightedCount_of_pool_le
    _ Resource.Event.quantumDuration _ path.2.2.2.2
    (measuredControlReset_events base noQuantum m ell width (outputs position) path.2.2.2.2)
  simp only [oneQubit, oneMeasurement, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.quantumDuration, Nat.one_mul, Nat.mul_one, Nat.zero_add] at phases reset
  have firstH : (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := false) (single base noQuantum m ell width Gate.HOp)).quantumTime path.1 =
      1 := rfl
  have lastH : (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := false) (single base noQuantum m ell width Gate.HOp)).quantumTime
      path.2.2.2.1 = 1 := rfl
  have total := Nat.add_le_add firstH.le
    (Nat.add_le_add arithmetic (Nat.add_le_add phases (Nat.add_le_add lastH.le reset)))
  exact total.trans_eq (stage_time_formula width position.val)

/-- Fixed actual measured stages have exactly their complete original caller storage peaks. -/
lemma measuredStage_spaces (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (path : (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path) :
    (stage base noQuantum m ell width wide inverse outputs modulus unit position).peakResidentSpace
        path = (Context base noQuantum m ell width).residentSpace ∧
      (stage base noQuantum m ell width wide inverse outputs modulus unit
        position).peakAuxiliarySpace path = (Context base noQuantum m ell width).auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ path, Circuit.fixed_peakAuxiliarySpace _ path⟩

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources
