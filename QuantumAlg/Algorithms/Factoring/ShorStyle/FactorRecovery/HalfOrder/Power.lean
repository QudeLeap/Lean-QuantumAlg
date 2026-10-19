/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Parameters
import all QuantumAlg.Components.Classical.Modular.NativePower.Construction

/-!
# Actual stored half-order modular power for Shor factor recovery

One closed right-shift instruction writes the actual stored order divided by
two into a fresh lexical word. The existing native modular-power circuit
reads that same word and original canonical base, writes the caller's result,
then releases its own scratch. Finally the half-order word is released.
No natural-power callback replaces the real finite arithmetic execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower

noncomputable section

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The one real half-order workspace cell adjoined to the unchanged original frame. -/
@[implicit_reducible]
def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh

def halfRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (phaseBits N + 1)) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh

def liftInput {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (context ctx N) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh

def liftWrite {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (context ctx N) shape :=
  output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh

/-- The finite native right shift reads the unchanged actual order operand. -/
def shiftOp (order : CInputRef ctx (.unsignedWord (phaseBits N + 1))) :
    ClassicalOp (.unsignedWord (phaseBits N + 1)) (.unsignedWord (phaseBits N + 1))
      (context ctx N) (context ctx N) :=
  .wordUnary .shiftRight (phaseBits N + 1) (context ctx N)
    (liftInput order) (halfRef ctx N)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Shift the actual order, then run the existing modular-power implementation on its real word. -/
def body (source : Input N) (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) :
    Circuit model (context ctx N) (context ctx N) :=
  .seq (BitWord.instruction (execution := model) (shiftOp order))
    (Modular.NativePower.into (model := model) (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output))

/-- The lexical scope owns and releases the actual half-order storage around that same body. -/
def code (source : Input N) (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh (body (model := model) source base order output)

/-- Exactly one real shift precedes the actual modular-power trace. -/
lemma code_eventTrace (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N)))
    (path : (code (model := model) source base order output).Path) :
    (code (model := model) source base order output).eventTrace path =
      Resource.Event.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .shiftRight (phaseBits N + 1))) ::
        (Modular.NativePower.into (model := model) (modulusSpec source) (liftInput base)
          (.storage (halfRef ctx N).toCStorageRef) (liftWrite output)).eventTrace path.2 := by
  change (BitWord.instruction (execution := model) (shiftOp order)).eventTrace path.1 ++ _ = _
  rw [BitWord.bitWord_instruction_eventTrace]
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower
