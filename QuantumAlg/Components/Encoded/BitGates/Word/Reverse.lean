/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Swap

/-!
# Literal encoded-word bit reversal

The existing three-CNOT word swap exchanges the two symmetric half-words.
This gives a physical reversal with exactly `3 * (width / 2)` CNOT
occurrences. The middle bit of an odd-width word is untouched. No wire
relabeling is substituted for these gates, and no additional bit is used.

The readout and projection laws describe the complete actual gate list
for arbitrary encoded data, including every correlation with its complement.
-/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

private def reverseLeftIndex (width : Nat) (index : Fin (width / 2)) : Fin width :=
  ⟨index.val, index.isLt.trans_le (Nat.div_le_self width 2)⟩

private def reverseRightIndex (width : Nat) (index : Fin (width / 2)) : Fin width :=
  (reverseLeftIndex width index).rev

private theorem reverse_indices_ne (left right : Fin (width / 2)) :
    reverseLeftIndex width left ≠ reverseRightIndex width right := by
  intro same
  have values := congrArg (fun index : Fin width => index.val) same
  have leftBound := left.isLt
  have rightBound := right.isLt
  simp only [reverseLeftIndex, reverseRightIndex, Fin.val_rev] at values
  omega

private def reverseLeftWord (word : Word encoding width) : Word encoding (width / 2) :=
  ⟨fun index => word.bit (reverseLeftIndex width index)⟩

private def reverseRightWord (word : Word encoding width) : Word encoding (width / 2) :=
  ⟨fun index => word.bit (reverseRightIndex width index)⟩

private theorem reverse_left_distinct (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (left right : Fin (width / 2)) (different : left ≠ right) :
    ((reverseLeftWord word).bit left).wire ≠ ((reverseLeftWord word).bit right).wire := by
  apply distinct
  intro same
  apply different
  exact Fin.ext (congrArg (fun index : Fin width => index.val) same)

private theorem reverse_right_distinct (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (left right : Fin (width / 2)) (different : left ≠ right) :
    ((reverseRightWord word).bit left).wire ≠ ((reverseRightWord word).bit right).wire := by
  apply distinct
  intro same
  apply different
  apply Fin.ext
  have values := congrArg (fun index : Fin width => index.val) same
  have leftBound := left.isLt
  have rightBound := right.isLt
  simp only [reverseRightIndex, reverseLeftIndex, Fin.val_rev] at values
  omega

private theorem reverse_cross (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (left right : Fin (width / 2)) :
    ((reverseLeftWord word).bit left).wire ≠ ((reverseRightWord word).bit right).wire :=
  distinct _ _ (reverse_indices_ne left right)

/-- Execute one literal three-CNOT exchange for each symmetric pair. -/
def reverseGates (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  swapGates (reverseLeftWord word) (reverseRightWord word)
    (fun index => reverse_cross word distinct index index)

/-- The reversal program is compiled from that same native gate list. -/
def reverseProgram (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (reverseGates word distinct)

/-- Fold the actual symmetric-pair gate list on the complete encoded data. -/
def reverseStep (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) : Data → Data :=
  GateSpec.stepList (reverseGates word distinct)

/-- Every output word bit is the original physically reversed word bit. -/
theorem reverseStep_get (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (index : Fin width) (state : Data) :
    (word.bit index).get (reverseStep word distinct state) =
      (word.bit index.rev).get state := by
  let separated := fun index => reverse_cross word distinct index index
  by_cases left : index.val < width / 2
  · let pair : Fin (width / 2) := ⟨index.val, left⟩
    have leftIndex : reverseLeftIndex width pair = index := Fin.ext rfl
    have rightIndex : reverseRightIndex width pair = index.rev :=
      congrArg Fin.rev leftIndex
    have actual := swapStep_get_left (reverseLeftWord word) (reverseRightWord word)
      separated pair
      (fun other different => reverse_left_distinct word distinct other pair different)
      (fun other => (reverse_cross word distinct pair other).symm)
      (fun other => reverse_cross word distinct other pair)
      (fun other different => reverse_right_distinct word distinct other pair different) state
    change (word.bit (reverseLeftIndex width pair)).get (reverseStep word distinct state) =
      (word.bit (reverseRightIndex width pair)).get state at actual
    rw [leftIndex, rightIndex] at actual
    exact actual
  · by_cases right : index.rev.val < width / 2
    · let pair : Fin (width / 2) := ⟨index.rev.val, right⟩
      have leftIndex : reverseLeftIndex width pair = index.rev := Fin.ext rfl
      have rightIndex : reverseRightIndex width pair = index := by
        exact (congrArg Fin.rev leftIndex).trans (Fin.rev_rev index)
      have actual := swapStep_get_right (reverseLeftWord word) (reverseRightWord word)
        separated pair
        (fun other different => reverse_left_distinct word distinct other pair different)
        (fun other => (reverse_cross word distinct pair other).symm)
        (fun other => reverse_cross word distinct other pair)
        (fun other different => reverse_right_distinct word distinct other pair different) state
      change (word.bit (reverseRightIndex width pair)).get (reverseStep word distinct state) =
        (word.bit (reverseLeftIndex width pair)).get state at actual
      rw [rightIndex, leftIndex] at actual
      exact actual
    · have middle : index.rev = index := by
        apply Fin.ext
        have within := index.isLt
        simp only [Fin.val_rev] at right ⊢
        omega
      rw [middle]
      apply swapStep_get_observed_of_swap_ne
        (reverseLeftWord word) (reverseRightWord word) separated (word.bit index)
      · intro pair
        apply distinct
        intro same
        have values := congrArg (fun wire : Fin width => wire.val) same
        have within := pair.isLt
        change pair.val = index.val at values
        omega
      · intro pair
        apply distinct
        intro same
        have values := congrArg (fun wire : Fin width => wire.val) same
        have within := pair.isLt
        simp only [reverseRightIndex, reverseLeftIndex, Fin.val_rev] at values
        have middleValue := congrArg (fun wire : Fin width => wire.val) middle
        simp only [Fin.val_rev] at middleValue
        omega

/-- Flips in the selected word suffice to establish preservation of any complete complement. -/
theorem reverseStep_preserves_projection {Projection : Type} (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (project : Data → Projection)
    (preserved : ∀ index state, project ((word.bit index).flip state) = project state)
    (state : Data) : project (reverseStep word distinct state) = project state :=
  swapStep_preserves_projection (reverseLeftWord word) (reverseRightWord word)
    (fun index => reverse_cross word distinct index index) project
    (fun index => preserved (reverseLeftIndex width index))
    (fun index => preserved (reverseRightIndex width index)) state

/-- The same literal native program realizes the entire encoded-data action. -/
theorem reverse_realizes (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (reverseProgram physical oracles word distinct) (reverseStep word distinct) :=
  GateSpec.realizesList physical oracles (reverseGates word distinct)

/-- Exactly three CNOT occurrences are emitted per symmetric pair, including width zero. -/
theorem reverseGates_length (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    (reverseGates word distinct).length = 3 * (width / 2) :=
  swapGates_length (reverseLeftWord word) (reverseRightWord word)
    (fun index => reverse_cross word distinct index index)

/-- Literal serial scheduling charges precisely the same emitted CNOT list. -/
theorem reverseProgram_resources (word : Word encoding width)
    (distinct : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    (reverseProgram physical oracles word distinct).eventCost.card = 3 * (width / 2) ∧
      (reverseProgram physical oracles word distinct).evaluatedEventDepth (fun _ => 1) =
        3 * (width / 2) :=
  ⟨(GateSpec.programList_eventCost_card physical oracles _).trans
      (reverseGates_length word distinct),
    (GateSpec.programList_evaluatedEventDepth_unit physical oracles _).trans
      (reverseGates_length word distinct)⟩

end

end QuantumAlg.EncodedBit.Word
