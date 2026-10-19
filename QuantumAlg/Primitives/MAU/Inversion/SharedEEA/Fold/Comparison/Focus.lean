/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Registers
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Place the actual comparison in word/Iter/Ctrl order

The retained input-fold comparison reads Work2 and writes Iter while
restoring the existing Ctrl helper [LYL+26, sec_EEA/sub_4phase.tex:108-117;
G17, paper.tex:380-389]. The actual Gidney program declares flag/word/helper
order. This owner changes its exact logical basis and each native physical
address together to word/flag/helper order, ready for insertion of the
remaining source fields.

No new permutation gate is declared. Physical placement gives the same addressed
comparison its desired coordinates; the original ordered native events,
full arbitrary flag/helper behavior, and exact amplitudes are retained.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonFocus

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- The physical focus after moving Iter behind the complete Work2 word. -/
abbrev Data (width : Nat) := Fin (2 ^ width) × (Bool × Bool)

/-- The same actual fields in word/Iter/Ctrl order. -/
def encoding (width : Nat) : BinaryLabelEncoding (Data width) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool)

/-- Reassociate and exchange named fields, retaining their complete values. -/
def fieldEquiv (width : Nat) : Addition.Gidney.Registers width ≃ Data width where
  toFun state := (state.2.1, (state.1, state.2.2))
  invFun state := (state.2.1, (state.1, state.2.2))
  left_inv := by rintro ⟨flag, word, helper⟩; rfl
  right_inv := by rintro ⟨word, flag, helper⟩; rfl

/-- Exact binary block splitting and reassembly, with no cardinality-selected equivalence. -/
def indexEquiv (width : Nat) :
    Fin (2 ^ (1 + (width + 1))) ≃ Fin (2 ^ (width + (1 + 1))) where
  toFun label :=
    let flagRest := (prodEquiv (m := 1) (n := width + 1)).symm label
    let wordHelper := (prodEquiv (m := width) (n := 1)).symm flagRest.2
    prodEquiv (m := width) (n := 1 + 1)
      (wordHelper.1, prodEquiv (m := 1) (n := 1) (flagRest.1, wordHelper.2))
  invFun label :=
    let wordRest := (prodEquiv (m := width) (n := 1 + 1)).symm label
    let flagHelper := (prodEquiv (m := 1) (n := 1)).symm wordRest.2
    prodEquiv (m := 1) (n := width + 1)
      (flagHelper.1, prodEquiv (m := width) (n := 1) (wordRest.1, flagHelper.2))
  left_inv := by
    intro label
    simp
  right_inv := by
    intro label
    simp

/-- The exact index map acts on the same field encoding used by the actual comparison. -/
lemma indexEquiv_encode (width : Nat) (state : Addition.Gidney.Registers width) :
    indexEquiv width ((Addition.Gidney.encoding width).encode state) =
      (encoding width).encode (fieldEquiv width state) := by
  rcases state with ⟨flag, word, helper⟩
  change indexEquiv width (prodEquiv (m := 1) (n := width + 1)
      (BinaryLabelEncoding.bool.encode flag,
        prodEquiv (m := width) (n := 1) (word, BinaryLabelEncoding.bool.encode helper))) =
    prodEquiv (m := width) (n := 1 + 1)
      (word, prodEquiv (m := 1) (n := 1)
        (BinaryLabelEncoding.bool.encode flag, BinaryLabelEncoding.bool.encode helper))
  simp only [indexEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

/-- Move the leading flag behind the word and keep every other physical address distinct. -/
def physicalIndex (width index : Nat) : Nat :=
  if index = 0 then width else if index < width + 1 then index - 1 else index

private lemma physicalIndex_injective (width : Nat) :
    Function.Injective (physicalIndex width) := by
  intro left right same
  unfold physicalIndex at same
  split at same <;> split at same
  all_goals try split at same
  all_goals try split at same
  all_goals omega

private lemma physicalIndex_within (width index : Nat) (within : index < width + 2) :
    physicalIndex width index < width + 2 := by
  unfold physicalIndex
  split
  · omega
  · split <;> omega

private lemma widths (width : Nat) :
    (Addition.Gidney.encoding width).width = (encoding width).width := by
  change 1 + (width + 1) = width + (1 + 1)
  omega

private def inversePhysicalIndex (width index : Nat) : Nat :=
  if index < width then index + 1 else if index = width then 0 else index

/-- All three field segments are permuted on actual finite physical wires. -/
def wires (width : Nat) :
    Fin (Addition.Gidney.encoding width).width ≃ Fin (encoding width).width where
  toFun index := ⟨physicalIndex width index.val, by
    change physicalIndex width index.val < width + (1 + 1)
    have bound : index.val < width + 2 := by
      have actual := index.isLt
      change index.val < 1 + (width + 1) at actual
      omega
    exact physicalIndex_within width index.val bound⟩
  invFun index := ⟨inversePhysicalIndex width index.val, by
    have bound := index.isLt
    change index.val < width + (1 + 1) at bound
    change inversePhysicalIndex width index.val < 1 + (width + 1)
    unfold inversePhysicalIndex
    split_ifs <;> omega⟩
  left_inv index := by
    apply Fin.ext
    have bound := index.isLt
    change index.val < 1 + (width + 1) at bound
    change inversePhysicalIndex width (physicalIndex width index.val) = index.val
    unfold inversePhysicalIndex physicalIndex
    split_ifs <;> omega
  right_inv index := by
    apply Fin.ext
    have bound := index.isLt
    change index.val < width + (1 + 1) at bound
    change physicalIndex width (inversePhysicalIndex width index.val) = index.val
    by_cases low : index.val < width
    · have nonzero : index.val + 1 ≠ 0 := by omega
      have inside : index.val + 1 < width + 1 := by omega
      simp only [inversePhysicalIndex, if_pos low, physicalIndex,
        if_neg nonzero, if_pos inside]
      omega
    · by_cases middle : index.val = width
      · simp [inversePhysicalIndex, physicalIndex, middle]
      · have last : index.val = width + 1 := by omega
        have nonzero : index.val ≠ 0 := by omega
        have outside : ¬index.val < width + 1 := by omega
        simp [inversePhysicalIndex, physicalIndex, low, middle, nonzero, outside]

private lemma field_coordinates (width : Nat) (state : Data width)
    (index : Fin (Addition.Gidney.encoding width).width) :
    (BinaryBasis.bigEndianEquiv (encoding width).width).symm
        ((encoding width).encode state) (wires width index) =
      (BinaryBasis.bigEndianEquiv (Addition.Gidney.encoding width).width).symm
        ((Addition.Gidney.encoding width).encode ((fieldEquiv width).symm state)) index := by
  rcases state with ⟨word, flag, helper⟩
  let flagLabel : Fin (2 ^ 1) := BinaryLabelEncoding.bool.encode flag
  let helperLabel : Fin (2 ^ 1) := BinaryLabelEncoding.bool.encode helper
  change finTwoEquiv.symm
      ((prodEquiv (m := width) (n := 1 + 1)
        (word, prodEquiv (m := 1) (n := 1) (flagLabel, helperLabel))).val.testBit
          (wires width index).rev.val) =
    finTwoEquiv.symm
      ((prodEquiv (m := 1) (n := width + 1)
        (flagLabel, prodEquiv (m := width) (n := 1) (word, helperLabel))).val.testBit
          index.rev.val)
  congr 1
  have bound : index.val < width + 2 := by
    have actual := index.isLt
    change index.val < 1 + (width + 1) at actual
    omega
  simp only [Fin.val_rev, wires, Equiv.coe_fn_mk]
  have targetWidth : (encoding width).width = width + 2 := by
    change width + (1 + 1) = width + 2
    omega
  have sourceWidth : (Addition.Gidney.encoding width).width = width + 2 := by
    change 1 + (width + 1) = width + 2
    omega
  rw [targetWidth]
  conv_rhs => arg 2; arg 1; rw [sourceWidth]
  by_cases leading : index.val = 0
  · have targetBit := prodEquiv_testBit_right word
        (prodEquiv (m := 1) (n := 1) (flagLabel, helperLabel)) (⟨1, by decide⟩ : Fin (1 + 1))
    have targetFlag := prodEquiv_testBit_left flagLabel helperLabel (⟨0, by decide⟩ : Fin 1)
    have sourceFlag := prodEquiv_testBit_left flagLabel
      (prodEquiv (m := width) (n := 1) (word, helperLabel)) (⟨0, by decide⟩ : Fin 1)
    have address : physicalIndex width index.val = width := by simp [physicalIndex, leading]
    have targetPosition : width + 2 - (physicalIndex width index.val + 1) = 1 := by
      rw [address]
      omega
    have sourcePosition : width + 2 - (index.val + 1) = width + 1 := by omega
    rw [targetPosition, sourcePosition]
    exact (targetBit.trans targetFlag).trans sourceFlag.symm
  · by_cases inWord : index.val < width + 1
    · let wordBit : Fin width := ⟨width - index.val, by omega⟩
      have targetBit := prodEquiv_testBit_left word
        (prodEquiv (m := 1) (n := 1) (flagLabel, helperLabel)) wordBit
      have sourceOuter := prodEquiv_testBit_right flagLabel
        (prodEquiv (m := width) (n := 1) (word, helperLabel))
        (⟨1 + wordBit.val, by omega⟩ : Fin (width + 1))
      have sourceWord := prodEquiv_testBit_left word helperLabel wordBit
      have address : physicalIndex width index.val = index.val - 1 := by
        simp [physicalIndex, leading, inWord]
      have targetPosition : width + 2 - (physicalIndex width index.val + 1) =
          2 + wordBit.val := by
        rw [address]
        dsimp [wordBit]
        omega
      have sourcePosition : width + 2 - (index.val + 1) =
          1 + wordBit.val := by
        dsimp [wordBit]
        omega
      rw [targetPosition, sourcePosition]
      exact targetBit.trans (sourceOuter.trans sourceWord).symm
    · have last : index.val = width + 1 := by omega
      have targetOuter := prodEquiv_testBit_right word
        (prodEquiv (m := 1) (n := 1) (flagLabel, helperLabel)) (⟨0, by decide⟩ : Fin (1 + 1))
      have targetHelper := prodEquiv_testBit_right flagLabel helperLabel (⟨0, by decide⟩ : Fin 1)
      have sourceOuter := prodEquiv_testBit_right flagLabel
        (prodEquiv (m := width) (n := 1) (word, helperLabel))
        (⟨0, by omega⟩ : Fin (width + 1))
      have sourceHelper := prodEquiv_testBit_right word helperLabel (⟨0, by decide⟩ : Fin 1)
      have address : physicalIndex width index.val = index.val := by
        simp [physicalIndex, leading, inWord]
      have targetPosition : width + 2 - (physicalIndex width index.val + 1) = 0 := by
        rw [address, last]
        omega
      have sourcePosition : width + 2 - (index.val + 1) = 0 := by rw [last]; omega
      rw [targetPosition, sourcePosition]
      exact (targetOuter.trans targetHelper).trans
        (sourceOuter.trans sourceHelper).symm

/-- The semantic field permutation is induced by the actual physical wires. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (Addition.Gidney.encoding width) (encoding width) :=
  EncodedBit.FullPlacement.ofGrouping _ _ (fieldEquiv width).symm (wires width)
    (field_coordinates width)

/-- Transport an existing program's logical basis and each native physical address together. -/
def place (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Addition.Gidney.encoding width).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement width).place body

/-- The exact field action accompanying the existing program's coordinate transport. -/
def placeStep {width : Nat}
    (action : Addition.Gidney.Registers width → Addition.Gidney.Registers width)
    (state : Data width) : Data width :=
  fieldEquiv width (action ((fieldEquiv width).symm state))

/-- The transport preserves exact amplitudes for every action certified by the original program. -/
lemma place_realizes (width : Nat)
    {body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Addition.Gidney.encoding width).width).toQuantum}
    {action : Addition.Gidney.Registers width → Addition.Gidney.Registers width}
    (realizes : UnitaryCircuit.Realizes (Addition.Gidney.encoding width) body environment action) :
    UnitaryCircuit.Realizes (encoding width) (place width body) environment (placeStep action) := by
  exact (placement width).place_realizes realizes

/-- Reordering the coordinates retains the original actual native event sequence. -/
lemma place_eventTrace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Addition.Gidney.encoding width).width).toQuantum) :
    (place width body).eventTrace = body.eventTrace := by
  exact (placement width).place_eventTrace body

/-- The same actual program retains its complete native resource pool. -/
lemma place_eventCost (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Addition.Gidney.encoding width).width).toQuantum) :
    (place width body).eventCost = body.eventCost := by
  exact UnitaryCircuit.placeAt_eventCost _ _ _ _ _

/-- The actual comparison, with its logical basis and primitive addresses transformed together. -/
def program (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  place width (Addition.Gidney.comparisonProgram width pivot)

/-- Exact arithmetic in word-first order, with the helper retained for every input value. -/
def step {width : Nat} (pivot : Nat) (state : Data width) : Data width :=
  (state.1, (state.2.1 ^^ decide (state.1.val < pivot), state.2.2))

/-- The field grouping intertwines the actual comparison specification and the placed one. -/
lemma fieldEquiv_step (width pivot : Nat) (state : Addition.Gidney.Registers width) :
    fieldEquiv width (Addition.Gidney.comparisonOutput pivot state) =
      step pivot (fieldEquiv width state) := rfl

/-- The placed actual native program has exact basis action, without any phase allowance. -/
lemma program_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (program width pivot) environment (step pivot.val) :=
  (place_realizes width (Addition.Gidney.gidneyComparison_realizes width pivot)).congrStep
    (by rintro ⟨word, flag, helper⟩; rfl)

/-- Reordering coordinates preserves every actual native event in its original order. -/
lemma program_eventTrace (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (program width pivot).eventTrace =
      (Addition.Gidney.comparisonProgram width pivot).eventTrace :=
  place_eventTrace width (Addition.Gidney.comparisonProgram width pivot)

/-- The placed comparison has exactly the original native resource pool. -/
lemma program_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (program width pivot).eventCost =
      (Addition.Gidney.comparisonProgram width pivot).eventCost :=
  place_eventCost width (Addition.Gidney.comparisonProgram width pivot)

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonFocus
