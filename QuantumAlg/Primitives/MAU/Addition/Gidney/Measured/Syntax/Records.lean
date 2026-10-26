/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Availability

/-!
# Distinct actual physical outcomes retain distinct chronological paths

The actual path records each physical measurement outcome, including when
its destination is later overwritten. Thus different physical outcome words
cannot collapse into one retained record for a fixed original Store.
The outcome cardinality is obtained from these same physical vents
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Each actual measured instruction retains its full physical outcome in its native Path. -/
lemma actualRecord_path_injective (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records) (store : Store ctx) :
    Function.Injective (fun measured =>
      (instruction.actualRecord (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output store measured).2) := by
  cases instruction with
  | native gates =>
      intro first second _
      change Unit at first second
      exact Subsingleton.elim first second
  | vent target record =>
      intro first second same
      have actual := congrArg Prod.fst (congrArg Prod.snd same)
      exact actual
  | phase target record =>
      intro first second _
      change Unit at first second
      exact Subsingleton.elim first second

/-- The actual complete chronological native Path identifies every physical outcome word. -/
lemma wordActualRecord_path_injective (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    ∀ (word : List (Instruction encoding records)) (store : Store ctx),
    Function.Injective (fun measured =>
      (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output word store measured).2) := by
  intro word
  induction word with
  | nil =>
      intro store first second _
      change Unit at first second
      exact Subsingleton.elim first second
  | cons instruction rest ih =>
      intro store first second same
      change instruction.PhysicalOutcome physical sameWires ×
        WordOutcomes physical sameWires rest at first second
      rcases first with ⟨firstHead, firstTail⟩
      rcases second with ⟨secondHead, secondTail⟩
      have heads := actualRecord_path_injective (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output instruction store (congrArg Prod.fst same)
      change firstHead = secondHead at heads
      subst secondHead
      have tailPaths := congrArg Prod.snd same
      have tails := ih
        (instruction.actualRecord (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output store firstHead).1
        tailPaths
      exact congrArg (fun tail : WordOutcomes physical sameWires rest => (firstHead, tail)) tails

/-- One actual vent measures the same physical qubit and has exactly two physical outcomes. -/
lemma physicalOutcome_card_vent (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : EncodedBit encoding) (record : Fin records) :
    Fintype.card ((Instruction.vent target record).PhysicalOutcome physical sameWires) = 2 := by
  change Fintype.card
    (Fin (ctx.quantumLayout.wire
      (EncodedBit.MeasuredUncompute.placedWire target physical ctx sameWires)).dimension) = 2
  rw [Fintype.card_fin]
  exact congrArg PNat.val
    (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)

/-- Exactly the literal physical vents determine the complete actual outcome-word cardinality. -/
lemma wordOutcomes_card (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (word : List (Instruction encoding records)) :
    Fintype.card (WordOutcomes physical sameWires word) = 2 ^ (ventIndices word).length := by
  induction word with
  | nil => rfl
  | cons instruction rest ih =>
      change Fintype.card (instruction.PhysicalOutcome physical sameWires ×
        WordOutcomes physical sameWires rest) = _
      rw [Fintype.card_prod, ih]
      cases instruction with
      | native gates =>
          have cardOne : Fintype.card
              ((Instruction.native gates : Instruction encoding records).PhysicalOutcome physical
                sameWires) = 1 := by
            let _ : Unique
                ((Instruction.native gates : Instruction encoding records).PhysicalOutcome
                  physical sameWires) := inferInstanceAs (Unique Unit)
            exact Fintype.card_unique
          rw [cardOne, one_mul]
          rfl
      | vent target record =>
          rw [physicalOutcome_card_vent]
          simp only [ventIndices, List.length_cons, pow_succ, Nat.mul_comm]
      | phase target record =>
          have cardOne : Fintype.card
              ((Instruction.phase target record).PhysicalOutcome physical sameWires) = 1 := by
            let _ : Unique ((Instruction.phase target record).PhysicalOutcome physical sameWires) :=
              inferInstanceAs (Unique Unit)
            exact Fintype.card_unique
          rw [cardOne, one_mul]
          rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
