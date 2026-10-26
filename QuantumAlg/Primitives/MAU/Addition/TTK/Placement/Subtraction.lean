/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-! # Actual adjoint subtraction on two existing physical words -/

namespace QuantumAlg.MAU.Addition.TTK.WordPlacement

noncomputable section

open EncodedBit

variable {Data : Type} {frame : BinaryLabelEncoding Data} {width : Nat}
    (placement : WordPlacement frame width)

/-- Exact reverse of the actual placed adder, including its original parallel dependencies. -/
def subtractProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical frame.width).toQuantum :=
  placement.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- Full physical inverse word action retains the complete original complement. -/
def subtractStep (state : Data) : Data :=
  (placement.subsystem.full source_onto placement.onto).step
    (fun pair => (subtractionOutput pair.1, pair.2)) state

/-- Addition cancels the complete finite subtraction on every original physical label. -/
lemma step_subtractStep (state : Data) : placement.step (placement.subtractStep state) = state := by
  unfold step subtractStep FullPlacement.step
  simp only [Equiv.apply_symm_apply, lowOutput_subtractionOutput, Prod.eta,
    Equiv.symm_apply_apply]

/-- The actual native adjoint realizes that full inverse, including arbitrary retained systems. -/
lemma subtractProgram_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes frame placement.subtractProgram environment placement.subtractStep := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse (placement.program_realizes environment)
  · rw [subtractProgram, UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]
    exact Unitary.star_eq_inv _
  · exact placement.step_subtractStep

/-- Every bit outside the target, including the complete addend and dirty work, is retained. -/
lemma subtractStep_get_of_target_ne (state : Data) (bit : EncodedBit frame)
    (outside : ∀ index, (placement.target.bit index).wire ≠ bit.wire) :
    bit.get (placement.subtractStep state) = bit.get state := by
  have retained := placement.step_get_of_target_ne (placement.subtractStep state) bit outside
  rw [placement.step_subtractStep] at retained
  exact retained.symm

private lemma subtraction_word (pair : Registers width) :
    BitVec.ofFin (subtractionOutput pair).2 = BitVec.ofFin pair.2 - BitVec.ofFin pair.1 := by
  apply BitVec.eq_sub_iff_add_eq.mpr
  have canceled := congrArg (fun value : Registers width => BitVec.ofFin value.2)
    (lowOutput_subtractionOutput width pair)
  change BitVec.ofFin pair.1 + BitVec.ofFin (subtractionOutput pair).2 =
    BitVec.ofFin pair.2 at canceled
  rw [BitVec.add_comm]
  exact canceled

/-- Each actual target coordinate records the exact modular difference in its original order. -/
lemma subtractStep_target_get (state : Data) (addend target : BitVec width)
    (addendReads : ∀ index, (placement.addend.bit index).get state = addend.getMsbD index.val)
    (targetReads : ∀ index, (placement.target.bit index).get state = target.getMsbD index.val)
    (index : Fin width) :
    (placement.target.bit index).get (placement.subtractStep state) =
      (target - addend).getMsbD index.val := by
  have actual := placement.subsystem.full_step_source_read source_onto placement.onto
    (secondLens index) (placement.target.bit index)
    (wordPairSubsystem_right _ _ _ _ _ index) subtractionOutput state
  change (placement.target.bit index).get (placement.subtractStep state) =
    (BinaryLabelEncoding.finIdentityBit width index).get _ at actual
  rw [fin_bit_get] at actual
  have difference : BitVec.ofFin
      (subtractionOutput ((placement.subsystem.full source_onto placement.onto).grouping
        state).1).2 = target - addend := by
    rw [subtraction_word, placement.grouped_target state target targetReads,
      placement.grouped_addend state addend addendReads]
  exact actual.trans (congrArg (fun value : BitVec width => value.getMsbD index.val) difference)

end

end QuantumAlg.MAU.Addition.TTK.WordPlacement
