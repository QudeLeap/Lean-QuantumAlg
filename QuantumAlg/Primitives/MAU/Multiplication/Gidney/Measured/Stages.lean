/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Invariant
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Constants
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Arithmetic
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Semantics
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch

/-!
# Actual chronological multiplier labels and physically restored row promises

Each macro stage is the label action of the same actual instruction word.
The controlled exchange supplies the explicit inverse MAC with the original
canonical source word as its new target. The two original helpers and flag
remain physically zero at every macro boundary
[VBE95, 9511018.tex:333-367; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open EncodedBit Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Original complete label after the actual forward measured MAC. -/
def forwardLabel (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (initial : Data) : Data :=
  wordLabel (layout.forwardMACWord wide modulus coefficient) initial

/-- Original complete label after the paid native controlled exchange. -/
def exchangedLabel (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (initial : Data) : Data :=
  GateSpec.stepList layout.swapWordGates (layout.forwardLabel wide modulus coefficient initial)

/-- Original complete label after the separately emitted negative-inverse measured MAC. -/
def multipliedLabel (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) (initial : Data) : Data :=
  wordLabel (layout.inverseMACWord wide modulus inverseCoefficient)
    (layout.exchangedLabel wide modulus coefficient initial)

/-- The actual complete word has exactly its independently named chronological macro labels. -/
lemma multiplicationWord_label_stages (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) (initial : Data) :
    wordLabel (layout.multiplicationWord wide modulus coefficient inverseCoefficient) initial =
      layout.multipliedLabel wide modulus coefficient inverseCoefficient initial := by
  rw [multiplicationWord, wordLabel_append, wordLabel_append]
  rfl

/-- The actual forward macro retains the complete original source/control/outside frame. -/
lemma forwardLabel_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial (layout.forwardLabel wide modulus coefficient initial) :=
  accumulatePrefixWord_frame layout wide modulus _ width le_rfl initial clean

/-- The actual forward macro returns a canonical target and physically clears the original flag. -/
lemma forwardLabel_ready (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat) (coefficient : Nat)
    (initial : Data) (ready : layout.Ready modulus initial) :
    layout.Ready modulus (layout.forwardLabel wide modulus coefficient initial) :=
  accumulatePrefixWord_ready layout wide modulus _
    (fun index => forwardConstant_canonical modulus coefficient index positive)
      width le_rfl initial ready

/-- The native exchange retains the original coherent global multiplication control. -/
lemma exchangedLabel_control (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.control.get (layout.exchangedLabel wide modulus coefficient initial) =
      layout.control.get initial :=
  (swapWordGates_control layout _).trans
    (forwardLabel_frame layout wide modulus coefficient initial clean).control

/-- The actual controlled exchange supplies the next macro's canonical clean physical input. -/
lemma exchangedLabel_ready (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat) (coefficient : Nat)
    (initial : Data) (ready : layout.Ready modulus initial)
    (sourceBound : (layout.sourceWord initial).toNat < modulus.toNat) :
    layout.Ready modulus (layout.exchangedLabel wide modulus coefficient initial) where
  clean := fun helper => (swapWordGates_clean layout _ helper).trans
    ((forwardLabel_ready layout wide modulus positive coefficient initial ready).clean helper)
  flag := (swapWordGates_flag layout _).trans
    (forwardLabel_ready layout wide modulus positive coefficient initial ready).flag
  canonical := by
    rw [exchangedLabel, swapWordGates_targetWord]
    split
    · rw [(forwardLabel_frame layout wide modulus coefficient initial ready.clean).source]
      exact sourceBound
    · exact (forwardLabel_ready layout wide modulus positive coefficient initial ready).canonical

/-- The explicit negative-inverse macro returns its original flag and both helpers to zero. -/
lemma multipliedLabel_ready (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (coefficient inverseCoefficient : Nat) (initial : Data) (ready : layout.Ready modulus initial)
    (sourceBound : (layout.sourceWord initial).toNat < modulus.toNat) :
    layout.Ready modulus
      (layout.multipliedLabel wide modulus coefficient inverseCoefficient initial) :=
  accumulatePrefixWord_ready layout wide modulus _
    (fun index => inverseConstant_canonical modulus inverseCoefficient index positive)
      width le_rfl _
      (exchangedLabel_ready layout wide modulus positive coefficient initial ready sourceBound)

/-- The actual explicit inverse MAC retains the source word supplied by the original swap. -/
lemma multipliedLabel_sourceWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.sourceWord (layout.multipliedLabel wide modulus coefficient inverseCoefficient initial) =
      layout.sourceWord (layout.exchangedLabel wide modulus coefficient initial) := by
  have swappedClean : ∀ helper, (layout.clean helper).get
      (layout.exchangedLabel wide modulus coefficient initial) = false := by
    intro helper
    exact (swapWordGates_clean layout _ helper).trans
      ((forwardLabel_frame layout wide modulus coefficient initial clean).clean helper)
  exact (accumulatePrefixWord_frame layout wide modulus _ width le_rfl _ swappedClean).source

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
