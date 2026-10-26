/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
import all QuantumAlg.Util.NearestResidue

/-!
# Pure nearest-rescaled Fourier recovery

Nearest rescaling is followed by canonical modular wrap.  The original signed
right-frequency normalization, checked inverse and candidate reconstruction
then consume those residues unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open ClassicalAlgorithms ClassicalAlgorithms.Modular

/-- Nearest rescaling of the raw left and right physical Fourier labels. -/
def normalize {width : Nat} (spec : ModulusSpec width) (left right : Nat) :
    RawRecovery.NormalizedInput spec where
  left := Residue.ofNat spec (NearestResidue.quotient (left * spec.modulus) (2 ^ width))
  right := Residue.ofNat spec (NearestResidue.quotient (right * spec.modulus) (2 ^ width))

/-- The pure semantic output of nearest recovery and the original checked inverse. -/
def outputOf {width : Nat} (spec : ModulusSpec width) (left right : Nat) :
    Option (FiniteCyclicDLP.Output spec) :=
  let normalized := normalize spec left right
  match NumberTheory.TryInv.eval spec normalized.left with
  | none => none
  | some inverse => some (FiniteCyclicDLP.outputOf spec
      (RawRecovery.helperInput spec normalized inverse))

/-- Checked recovery on arbitrary canonical normalized residues. -/
def outputOfNormalized {width : Nat} (spec : ModulusSpec width)
    (normalized : RawRecovery.NormalizedInput spec) : Option (FiniteCyclicDLP.Output spec) :=
  match NumberTheory.TryInv.eval spec normalized.left with
  | none => none
  | some inverse => some (FiniteCyclicDLP.outputOf spec
      (RawRecovery.helperInput spec normalized inverse))

/-- Nearest normalization of the original big-endian raw-input shape. -/
def normalizeInput {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (RawRecovery.InputShape width)) : RawRecovery.NormalizedInput spec :=
  normalize spec (RawRecovery.leftRaw input) (RawRecovery.rightRaw input)

/-- Exact three-cell observations of checked recovery on canonical residues. -/
def outputCellsNormalized {width : Nat} (spec : ModulusSpec width)
    (normalized : RawRecovery.NormalizedInput spec) :
    CShape.Value (.product .bit (.product (.unsignedWord width) .bit)) :=
  match outputOfNormalized spec normalized with
  | none => .product (.bit false) (.product (CShape.wordOfNat width 0) (.bit false))
  | some output => .product (.bit true)
      (.product (CShape.wordOfNat width output.candidate.val) (.bit output.verified))

/-- Exact three-cell observations of the paid nearest decoder and checked recovery. -/
def outputCells {width : Nat} (spec : ModulusSpec width) (left right : Nat) :
    CShape.Value (.product .bit (.product (.unsignedWord width) .bit)) :=
  outputCellsNormalized spec (normalize spec left right)

/-- Three-cell nearest observations of the original big-endian raw-input shape. -/
def outputCellsInput {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (RawRecovery.InputShape width)) :
    CShape.Value (.product .bit (.product (.unsignedWord width) .bit)) :=
  outputCellsNormalized spec (normalizeInput spec input)

lemma outputCellsNormalized_of_none {width : Nat} (spec : ModulusSpec width)
    (normalized : RawRecovery.NormalizedInput spec)
    (failure : outputOfNormalized spec normalized = none) :
    outputCellsNormalized spec normalized =
      .product (.bit false) (.product (CShape.wordOfNat width 0) (.bit false)) := by
  unfold outputCellsNormalized
  rw [failure]

lemma outputCellsNormalized_of_some {width : Nat} (spec : ModulusSpec width)
    (normalized : RawRecovery.NormalizedInput spec) (output : FiniteCyclicDLP.Output spec)
    (success : outputOfNormalized spec normalized = some output) :
    outputCellsNormalized spec normalized =
      .product (.bit true)
        (.product (CShape.wordOfNat width output.candidate.val) (.bit output.verified)) := by
  unfold outputCellsNormalized
  rw [success]

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
