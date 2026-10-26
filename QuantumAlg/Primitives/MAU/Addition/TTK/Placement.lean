/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Parallel
import all QuantumAlg.Primitives.MAU.Addition.TTK.Correctness
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.WordPair.Preservation

/-!
# Actual TTK addition on two ordered words of an existing frame

The complete ordered physical operands determine placement. All other bits
remain present and unchanged. Arithmetic follows the same actual parallel
TTK body, including its all-width semantics, events and dependency schedule.
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit BinaryLabelEncoding

/-- Two disjoint ordered physical words in one complete existing binary frame. -/
structure WordPlacement {Data : Type} (encoding : BinaryLabelEncoding Data) (width : Nat) where
  addend : Word encoding width
  target : Word encoding width
  addendDistinct : Function.Injective (fun index => (addend.bit index).wire)
  targetDistinct : Function.Injective (fun index => (target.bit index).wire)
  separate : ∀ left right, (addend.bit left).wire ≠ (target.bit right).wire
  onto : Function.Surjective encoding.encode

namespace WordPlacement

variable {Data : Type} {frame : BinaryLabelEncoding Data} {width : Nat}
    (placement : WordPlacement frame width)

private lemma source_onto : Function.Surjective (encoding width).encode :=
  (prodEquiv (m := width) (n := width)).surjective

/-- The actual operand positions and their complete existing complement. -/
def subsystem : WireSubsystem (encoding width) frame :=
  wordPairSubsystem placement.addend placement.target placement.addendDistinct
    placement.targetDistinct placement.separate

/-- Place the actual parallel TTK adder without allocating any additional system. -/
def program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical frame.width).toQuantum :=
  placement.subsystem.program source_onto placement.onto (parallelLowRippleProgram width)

/-- Exact two-word arithmetic and complete unchanged complement. -/
def step (state : Data) : Data :=
  (placement.subsystem.full source_onto placement.onto).step
    (fun pair => (lowOutput pair.1, pair.2)) state

/-- Full coherent semantics follow from the actual rescheduled TTK body. -/
lemma program_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes frame placement.program environment placement.step := by
  apply placement.subsystem.program_realizes source_onto placement.onto
  apply (ttkParallelLowRipple_realizes_fold width environment).congrStep
  exact ttkLowRipple_step width

/-- Every actual bit outside the target survives, including the addend and dirty complement. -/
lemma step_get_of_target_ne (state : Data) (bit : EncodedBit frame)
    (outside : ∀ index, (placement.target.bit index).wire ≠ bit.wire) :
    bit.get (placement.step state) = bit.get state :=
  wordPairStep_get_of_target_ne placement.addend placement.target placement.addendDistinct
    placement.targetDistinct placement.separate placement.onto lowOutput (fun _ => rfl)
    bit outside state

private def firstLens (index : Fin width) : EncodedBit (encoding width) :=
  prodLeftBit (finIdentity width) (finIdentity width) (finIdentityBit width index)

private def secondLens (index : Fin width) : EncodedBit (encoding width) :=
  prodRightBit (finIdentity width) (finIdentity width) (finIdentityBit width index)

private lemma fin_bit_get (index : Fin width) (value : Fin (2 ^ width)) :
    (finIdentityBit width index).get value = (BitVec.ofFin value).getMsbD index.val := by
  change value.val.testBit (width - 1 - index.val) = _
  simp only [BitVec.getMsbD_eq_getLsbD, index.isLt, decide_true, Bool.true_and,
    BitVec.getLsbD]
  rfl

private lemma grouped_addend (state : Data) (value : BitVec width)
    (reads : ∀ index, (placement.addend.bit index).get state = value.getMsbD index.val) :
    BitVec.ofFin ((placement.subsystem.full source_onto placement.onto).grouping state).1.1 =
      value := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := placement.subsystem.full_source_read source_onto placement.onto
    (firstLens ⟨index, within⟩) (placement.addend.bit ⟨index, within⟩)
    (wordPairSubsystem_left _ _ _ _ _ ⟨index, within⟩) state
  change (finIdentityBit width ⟨index, within⟩).get _ = _ at actual
  exact (fin_bit_get ⟨index, within⟩ _).symm.trans (actual.trans (reads _))

private lemma grouped_target (state : Data) (value : BitVec width)
    (reads : ∀ index, (placement.target.bit index).get state = value.getMsbD index.val) :
    BitVec.ofFin ((placement.subsystem.full source_onto placement.onto).grouping state).1.2 =
      value := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := placement.subsystem.full_source_read source_onto placement.onto
    (secondLens ⟨index, within⟩) (placement.target.bit ⟨index, within⟩)
    (wordPairSubsystem_right _ _ _ _ _ ⟨index, within⟩) state
  change (finIdentityBit width ⟨index, within⟩).get _ = _ at actual
  exact (fin_bit_get ⟨index, within⟩ _).symm.trans (actual.trans (reads _))

/-- The full target word records the modular sum in its original most-significant-first order. -/
lemma step_target_get (state : Data) (addend target : BitVec width)
    (addendReads : ∀ index, (placement.addend.bit index).get state = addend.getMsbD index.val)
    (targetReads : ∀ index, (placement.target.bit index).get state = target.getMsbD index.val)
    (index : Fin width) :
    (placement.target.bit index).get (placement.step state) =
      (addend + target).getMsbD index.val := by
  have actual := placement.subsystem.full_step_source_read source_onto placement.onto
    (secondLens index) (placement.target.bit index)
    (wordPairSubsystem_right _ _ _ _ _ index) lowOutput state
  change (placement.target.bit index).get (placement.step state) =
    (finIdentityBit width index).get _ at actual
  rw [fin_bit_get] at actual
  have sum : BitVec.ofFin
      (lowOutput ((placement.subsystem.full source_onto placement.onto).grouping state).1).2 =
      addend + target := by
    change BitVec.ofFin
      ((placement.subsystem.full source_onto placement.onto).grouping state).1.1 +
      BitVec.ofFin
      ((placement.subsystem.full source_onto placement.onto).grouping state).1.2 = _
    rw [placement.grouped_addend state addend addendReads,
      placement.grouped_target state target targetReads]
  exact actual.trans (congrArg (fun word : BitVec width => word.getMsbD index.val) sum)

/-- The literal native event word is unchanged by placement. -/
lemma program_eventTrace : placement.program.eventTrace =
    (parallelLowRippleProgram width).eventTrace :=
  placement.subsystem.program_eventTrace source_onto placement.onto _

/-- The actual parallel dependencies are unchanged by the physical placement. -/
lemma program_evaluatedEventDepth
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    placement.program.evaluatedEventDepth duration =
      (parallelLowRippleProgram width).evaluatedEventDepth duration :=
  placement.subsystem.program_evaluatedEventDepth source_onto placement.onto _ duration

end WordPlacement

end

end QuantumAlg.MAU.Addition.TTK
