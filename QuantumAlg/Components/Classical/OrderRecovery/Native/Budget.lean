/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources

/-!
# Independent native finite recovery budgets

These allowances depend only on the declared widths. They include the actual
phase decoder, denominator loader, cursor initialization, bounded candidate
visits and final option packing. Selection uses the coordinatewise maximum of
its two real arms. Temporary continuant and modular-power storage is reused.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

noncomputable section

/-- Literal division, continuant product and continuant sum. -/
def candidateEvents (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem width width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width))]

/-- Literal positivity, modular-one equality and conjunction checks. -/
def validationEvents (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal modulusWidth)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.bit .and))]

/-- The rejected candidate advances four words and tests the real remainder. -/
def rejectionEvents (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width))]

/-- The accepted candidate writes the selected word and the two latches. -/
def acceptanceEvents (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.bit .copy)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.bit .not))]

/-- Coordinatewise allowance for whichever real selection arm is taken. -/
def selectionEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : ResourcePool model :=
  ResourcePool.max (ResourcePool.ofList (rejectionEvents model width))
    (ResourcePool.ofList (acceptanceEvents model width))

/-- One active visit includes the actual modular power and all three checks. -/
def visitEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth width : Nat) : ResourcePool model :=
  ResourcePool.ofList (candidateEvents model width) +
    ((Modular.NativePower.eventEnvelope model modulusWidth width +
      ResourcePool.ofList (validationEvents model modulusWidth width)) +
      selectionEnvelope model width)

/-- Initialization includes the padded decoder, literal loader and three real writes. -/
def initializationEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth width : Nat) : ResourcePool model :=
  TerminalDecode.envelope (model := model) width + (ConstantWord.envelope model width +
    ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment modulusWidth)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.bit .not))])

/-- Fixed width-only budget for the original finite continued-fraction scan. -/
public def eventEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth phaseBits : Nat) : ResourcePool model :=
  initializationEnvelope model modulusWidth (phaseBits + 1) +
    (ResourcePool.scale (2 * (phaseBits + 1)) (visitEnvelope model modulusWidth (phaseBits + 1)) +
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packOption (phaseBits + 1))))))

/-- Independent unit duration allowance, including setup and result encoding. -/
def unitDepthBound (modulusWidth phaseBits : Nat) : Nat :=
  4 * (phaseBits + 1) + 4 +
    2 * (phaseBits + 1) * (2 * modulusWidth + 16 + 6 * (phaseBits + 1))

/-- Thirteen persistent cursor fields and one live division pair, with reused temporaries. -/
def extraClassicalBits (modulusWidth phaseBits : Nat) : Nat :=
  9 * (phaseBits + 1) + 2 * modulusWidth + 4 +
    max (phaseBits + 1) (8 * modulusWidth + 2)

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
