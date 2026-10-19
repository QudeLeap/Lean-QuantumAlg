/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Construction
import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Execution
import all QuantumAlg.Components.Classical.ConstantWord.Semantics

/-!
# Actual records of the complete modular-power body

Base unpacking, literal modulus loading, accumulator initialization, selected
exponent steps and the final copy all act on one store. The retained record
contains the actual constant-loader and exponent paths of those same actions.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

/-- The concrete body update and its complete five-stage path. -/
def powerBodyStep (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (powerCtx ctx width)) :
    Store (powerCtx ctx width) × (powerBody (model := model) spec base exponent output).Path :=
  let unpacked := BitWord.instructionStep (execution := model) (unpackBaseOp base) store
  let loaded := ConstantWord.foldStep (model := model) (modulusCell ctx width)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) unpacked.1
  let initialized := BitWord.instructionStep (execution := model) (initializeOp ctx width) loaded.1
  let powered := foldStep (model := model)
    (wordRead (baseCell ctx width)) (wordRead (modulusCell ctx width))
    (accumulatorCell ctx width)
    (List.ofFn (fun index : Fin exponentWidth =>
      CInputRef.wordBitGet (underPower exponent width) index)) initialized.1
  let copied := BitWord.instructionStep (execution := model) (copyResultOp output) powered.1
  (copied.1, (unpacked.2, (loaded.2, (initialized.2, (powered.2, copied.2)))))

/-- The one actual interpreter executes precisely the body record on each full reference block. -/
lemma nativePower_body_execute (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (powerCtx ctx width) Reference (model.HiddenState × History)) :
    (powerBody (model := model) spec base exponent output).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((powerBodyStep (model := model) spec base exponent output entry.1).1,
          (entry.2.1,
            (entry.2.2,
              (powerBodyStep (model := model) spec base exponent output entry.1).2)))) := by
  simp only [powerBody, ConstantWord.circuit, exponentCircuit, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, ConstantWord.constantWord_fold_execute,
    nativePower_fold_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual storage after all three real scratch allocations. -/
def enterPower {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (width : Nat) : Store (powerCtx ctx width) :=
  ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).pushWorkspace (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh).pushWorkspace
        (baseCtx ctx width).canonicalFreshKey (.unsignedWord width)
        (baseCtx ctx width).canonicalFreshKey_fresh

/-- Release exactly the accumulator, raw base and modulus heads, in reverse allocation order. -/
def leavePower {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store (powerCtx ctx width)) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (modulusCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (modulusCtx ctx width).canonicalFreshKey_fresh
      (Store.popWorkspace (baseCtx ctx width).canonicalFreshKey (.unsignedWord width)
        (baseCtx ctx width).canonicalFreshKey_fresh store))

/-- The actual outer store and complete body path after matching lexical releases. -/
def intoStep (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into (model := model) spec base exponent output).Path :=
  let body := powerBodyStep (model := model) spec base exponent output (enterPower store width)
  (leavePower body.1, body.2)

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
