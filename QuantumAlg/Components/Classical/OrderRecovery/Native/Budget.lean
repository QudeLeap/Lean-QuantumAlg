/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
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

/-- Literal division, continuant product and continuant sum. -/
def candidateEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.divRem width width),
    .classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .add width)]

/-- Literal positivity, modular-one equality and conjunction checks. -/
def validationEvents (kind : ProblemKind) (modulusWidth width : Nat) :
    List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .lessThan width),
    .classicalOperation (.wordBinary .equal modulusWidth), .classicalOperation (.bit .and)]

/-- The rejected candidate advances four words and tests the real remainder. -/
def rejectionEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width), .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .copy width), .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordBinary .lessThan width)]

/-- The accepted candidate writes the selected word and the two latches. -/
def acceptanceEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width), .classicalOperation (.bit .copy),
    .classicalOperation (.bit .not)]

/-- Coordinatewise allowance for whichever real selection arm is taken. -/
def selectionEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.max (ResourcePool.ofList (rejectionEvents kind width))
    (ResourcePool.ofList (acceptanceEvents kind width))

/-- One active visit includes the actual modular power and all three checks. -/
def visitEnvelope (kind : ProblemKind) (modulusWidth width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (candidateEvents kind width) +
    ((Modular.NativePower.eventEnvelope kind modulusWidth width +
      ResourcePool.ofList (validationEvents kind modulusWidth width)) +
      selectionEnvelope kind width)

/-- Initialization includes the padded decoder, literal loader and three real writes. -/
def initializationEnvelope (kind : ProblemKind) (modulusWidth width : Nat) : ResourcePool kind :=
  TerminalDecode.envelope width + (ConstantWord.envelope kind width +
    ResourcePool.ofList [.classicalOperation (.wordUnary .increment width),
      .classicalOperation (.wordUnary .increment modulusWidth), .classicalOperation (.bit .not)])

/-- Fixed width-only budget for the original finite continued-fraction scan. -/
public def eventEnvelope (kind : ProblemKind) (modulusWidth phaseBits : Nat) : ResourcePool kind :=
  initializationEnvelope kind modulusWidth (phaseBits + 1) +
    (ResourcePool.scale (2 * (phaseBits + 1)) (visitEnvelope kind modulusWidth (phaseBits + 1)) +
      ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packOption (phaseBits + 1)))))

/-- Independent unit duration allowance, including setup and result encoding. -/
def unitDepthBound (modulusWidth phaseBits : Nat) : Nat :=
  4 * (phaseBits + 1) + 4 +
    2 * (phaseBits + 1) * (2 * modulusWidth + 16 + 6 * (phaseBits + 1))

/-- Thirteen persistent cursor fields and one live division pair, with reused temporaries. -/
def extraClassicalBits (modulusWidth phaseBits : Nat) : Nat :=
  9 * (phaseBits + 1) + 2 * modulusWidth + 4 +
    max (phaseBits + 1) (8 * modulusWidth + 2)

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
