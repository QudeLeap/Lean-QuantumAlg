/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Circuit
import all QuantumAlg.Components.Classical.ConstantWord.Circuit
import all QuantumAlg.Util.Classical.Modular.Basic
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Complete lexical native modular power

The existing canonical base and exponent remain real source references. The
program allocates an extended modulus word, a raw base word and an accumulator;
it unpacks the base, loads the compilation-time modulus with actual shifts
and increments, increments the actual fresh-zero accumulator, executes the
finite exponent circuit, and copies the answer to the caller's result cell.
All three lexical cells are then released by their own workspace instructions.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open ClassicalAlgorithms.Modular

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width exponentWidth : Nat}

/-- The actual extended modulus cell, including the boundary modulus `2^width`. -/
@[reducible] def modulusCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- The raw base word is separate from the original nominal residue storage. -/
@[reducible] def baseCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (modulusCtx ctx width).addWorkspace (modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh

/-- The actual accumulator starts with the canonical zero encoding of its fresh cell. -/
@[reducible] def powerCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (baseCtx ctx width).addWorkspace (baseCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (baseCtx ctx width).canonicalFreshKey_fresh

/-- Lift an original structural read through the three real power scopes. -/
def underPower {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (powerCtx ctx width) shape :=
  ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (baseCtx ctx width).canonicalFreshKey (.unsignedWord width)
        (baseCtx ctx width).canonicalFreshKey_fresh

/-- The existing destination remains the same actual writable cell under all three scopes. -/
def writeUnderPower {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (powerCtx ctx width) shape :=
  ((output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (baseCtx ctx width).canonicalFreshKey (.unsignedWord width)
        (baseCtx ctx width).canonicalFreshKey_fresh

/-- The actual modulus head lifted through the later base and accumulator cells. -/
def modulusCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (powerCtx ctx width) (.unsignedWord (width + 1)) :=
  ((CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (baseCtx ctx width).canonicalFreshKey (.unsignedWord width)
        (baseCtx ctx width).canonicalFreshKey_fresh

/-- The actual raw base cell lifted through the later accumulator head. -/
def baseCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (powerCtx ctx width) (.unsignedWord width) :=
  (CWriteRef.workspaceHead (modulusCtx ctx width) (modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh).underWorkspace
      (baseCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (baseCtx ctx width).canonicalFreshKey_fresh

/-- The last actual scratch head stores the evolving canonical residue word. -/
def accumulatorCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (powerCtx ctx width) (.unsignedWord width) :=
  CWriteRef.workspaceHead (baseCtx ctx width) (baseCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (baseCtx ctx width).canonicalFreshKey_fresh

/-- Actual nominal unpacking of the unchanged original base read. -/
def unpackBaseOp (base : CInputRef ctx (.canonicalResidue width)) :
    ClassicalOp (.canonicalResidue width) (.unsignedWord width)
      (powerCtx ctx width) (powerCtx ctx width) :=
  .unpackCanonicalResidue width (powerCtx ctx width) (underPower base width) (baseCell ctx width)

/-- Increment the real fresh-zero accumulator to initialize canonical one. -/
def initializeOp (ctx : RuntimeCtx kind) (width : Nat) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width)
      (powerCtx ctx width) (powerCtx ctx width) :=
  .wordUnary .increment width (powerCtx ctx width)
    (wordRead (accumulatorCell ctx width)) (accumulatorCell ctx width)

/-- Copy the final actual accumulator into the original destination before releasing scratch. -/
def copyResultOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width)
      (powerCtx ctx width) (powerCtx ctx width) :=
  .wordUnary .copy width (powerCtx ctx width)
    (wordRead (accumulatorCell ctx width)) (writeUnderPower output width)

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The full actual instruction body on the three lexical power cells. -/
def powerBody (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (powerCtx ctx width) (powerCtx ctx width) :=
  .seq (BitWord.instruction (execution := model) (unpackBaseOp base))
    (.seq (ConstantWord.circuit (model := model) (modulusCell ctx width) spec.modulus)
      (.seq (BitWord.instruction (execution := model) (initializeOp ctx width))
        (.seq (exponentCircuit (model := model)
          (wordRead (baseCell ctx width)) (underPower exponent width)
          (wordRead (modulusCell ctx width)) (accumulatorCell ctx width))
          (BitWord.instruction (execution := model) (copyResultOp output)))))

/-- Execute native modular power on actual existing inputs and write the supplied result word. -/
def into (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (.workspace (modulusCtx ctx width) (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh
      (.workspace (baseCtx ctx width) (baseCtx ctx width).canonicalFreshKey
        (.unsignedWord width) (baseCtx ctx width).canonicalFreshKey_fresh
        (powerBody (model := model) spec base exponent output)))

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
