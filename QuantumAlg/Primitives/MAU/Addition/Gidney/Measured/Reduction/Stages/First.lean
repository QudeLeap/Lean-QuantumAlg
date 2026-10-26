/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages.Offsets
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Arithmetic
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Frame
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Readout

/-!
# Actual first comparison, measured addition and paid middle flag values

The original addressed word and two active controls determine the first
flag and sum. Actual helper restoration permits the following paid native
toggle without any new clean system [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Original joint value of the two active quantum controls on a complete encoded label. -/
def activeValue (layout : Layout encoding width) (state : Data) : Bool :=
  layout.control.get state && layout.selector.get state

/-- Full frame restoration retains the joint value of both original active quantum controls. -/
lemma frameInvariant_activeValue {layout : Layout encoding width} {initial current : Data}
    (invariant : layout.FrameInvariant initial current) :
    layout.activeValue current = layout.activeValue initial := by
  change ((layout.bit (.inl 0)).get current && (layout.bit (.inl 1)).get current) =
    ((layout.bit (.inl 0)).get initial && (layout.bit (.inl 1)).get initial)
  rw [invariant.active 0, invariant.active 1]

/-- The actual first native comparison retains the entire original target word. -/
lemma firstCompared_sourceWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.sourceWord (layout.firstCompared wide modulus constant initial) =
      layout.sourceWord initial :=
  comparisonGates_sourceWord layout wide _ initial clean

/-- A clean original flag receives exactly the independent first strict-comparison predicate. -/
lemma firstCompared_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    layout.flag.get (layout.firstCompared wide modulus constant initial) =
      firstFlag modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  rw [firstCompared, comparisonGates_flag layout wide _ initial clean, flagClean,
    Bool.false_xor, firstThreshold_nat modulus constant constantBound]
  rfl

/-- The first actual measured addition has exactly the independent first finite-word value. -/
lemma firstAdded_word_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    (layout.sourceWord (layout.firstAdded wide modulus constant initial)).toNat =
      firstWord (2 ^ width) modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  rw [firstAdded, reductionAdder_sourceWord layout wide constant _
    (firstCompared_frame layout wide modulus constant initial clean).clean,
    selected_add_nat, firstCompared_sourceWord layout wide modulus constant initial clean,
    firstCompared_flag layout wide modulus constant constantBound initial clean flagClean]
  rfl

/-- The first actual measured addition retains the original comparison flag value. -/
lemma firstAdded_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    layout.flag.get (layout.firstAdded wide modulus constant initial) =
      firstFlag modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  rw [firstAdded, reductionAdder_flag layout wide constant _
    (firstCompared_frame layout wide modulus constant initial clean).clean,
    firstCompared_flag layout wide modulus constant constantBound initial clean flagClean]

/-- The actual middle native Toffoli retains every addressed original target bit. -/
lemma toggleFlagGates_sourceWord (layout : Layout encoding width) (state : Data) :
    layout.sourceWord (stepList layout.toggleFlagGates state) = layout.sourceWord state := by
  unfold sourceWord
  congr 1
  funext index
  change (layout.target index).get
    (toffoliStep layout.control layout.selector layout.flag state) = (layout.target index).get state
  exact toffoliStep_get_of_target_ne layout.control layout.selector layout.flag
    (layout.target index) (layout.wire_ne (by intro impossible; cases impossible)) state

/-- The paid native middle toggle produces exactly the complementary reduction predicate. -/
lemma middleFlagged_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    layout.flag.get (layout.middleFlagged wide modulus constant initial) =
      secondFlag modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  change layout.flag.get (toffoliStep layout.control layout.selector layout.flag
    (layout.firstAdded wide modulus constant initial)) = _
  rw [toffoliStep_get_target]
  change (layout.flag.get (layout.firstAdded wide modulus constant initial) ^^
    layout.activeValue (layout.firstAdded wide modulus constant initial)) = _
  rw [firstAdded_flag layout wide modulus constant constantBound initial clean flagClean,
    frameInvariant_activeValue (firstAdded_frame layout wide modulus constant initial clean)]
  rfl

/-- The actual middle native toggle leaves the first finite target word unchanged. -/
lemma middleFlagged_word_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    (layout.sourceWord (layout.middleFlagged wide modulus constant initial)).toNat =
      firstWord (2 ^ width) modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  rw [middleFlagged, toggleFlagGates_sourceWord,
    firstAdded_word_nat layout wide modulus constant constantBound initial clean flagClean]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
