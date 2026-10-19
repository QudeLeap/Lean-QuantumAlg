/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD
import all QuantumAlg.Components.Classical.NumberTheory.FactorRange

/-!
# Actual left-priority factor selection from a stored half-power

The left GCD is physically computed and checked first. Its actual stored
comparison bit selects either its result packaging or the right GCD call.
The right arm computes and checks its own real GCD before packaging the
result. Rejection materializes the actual nominal option-none encoding.

The enclosing lexical factor scope owns these scratch cells, loads the one
and modulus words and supplies the same already-computed half-power operand.
This compositional circuit contains no supplied arithmetic result or predicate.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual reusable GCD candidate, comparison cells and bounded output payload. -/
structure Cells (ctx : RuntimeCtx kind) (N : Nat) where
  candidate : CWriteRef ctx (.unsignedWord (modulusBits N + 1))
  one : CInputRef ctx (.unsignedWord (modulusBits N + 1))
  modulus : CInputRef ctx (.unsignedWord (modulusBits N + 1))
  lower : CWriteRef ctx .bit
  upper : CWriteRef ctx .bit
  payload : CWriteRef ctx (.unsignedWord (modulusBits N))

def checkRefs (cells : Cells ctx N) : FactorRange.Refs ctx (modulusBits N + 1) where
  candidate := .storage cells.candidate.toCStorageRef
  one := cells.one
  modulus := cells.modulus
  lower := cells.lower
  upper := cells.upper

/-- The source factor is copied through an actual resize before its nominal option is packed. -/
def resizeOp (cells : Cells ctx N) :
    ClassicalOp (.unsignedWord (modulusBits N + 1)) (.unsignedWord (modulusBits N)) ctx ctx :=
  .wordResize (modulusBits N + 1) (modulusBits N) ctx
    (.storage cells.candidate.toCStorageRef) cells.payload

def packOp (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    ClassicalOp (.product .bit (.unsignedWord (modulusBits N)))
      (.option (.unsignedWord (modulusBits N))) ctx ctx :=
  .packOption ctx
    (.product (.storage cells.lower.toCStorageRef) (.storage cells.payload.toCStorageRef)) output

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Use the actual comparison bit as the option tag and the actual resized GCD as its payload. -/
def pack (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (resizeOp cells)) (BitWord.instruction (execution
    := model) (packOp cells output))

/-- The right GCD and its comparison are executed only after actual left rejection. -/
def right (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .seq (NativeHalfGCD.code (model := model) (N := N) true halfPower cells.candidate)
    (.seq (FactorRange.code (model := model) (checkRefs cells)) (pack (model := model) cells
      output))

/-- The stored left comparison chooses the physical left result or the real right computation. -/
def choose (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .branch (.storage cells.lower.toCStorageRef)
    (fun value => if value.toBool then pack (model := model) cells output else right (model :=
      model) halfPower cells output)

/-- Actual left GCD, actual comparison and strict source-prescribed left-priority selection. -/
def code (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .seq (NativeHalfGCD.code (model := model) (N := N) false halfPower cells.candidate)
    (.seq (FactorRange.code (model := model) (checkRefs cells)) (choose (model := model) halfPower
      cells output))

/-- Each actual packaging path contains both representation instructions. -/
lemma pack_eventTrace (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (pack (model := model) cells output).Path) :
    (pack (model := model) cells output).eventTrace path =
      [Resource.Event.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize (modulusBits N + 1) (modulusBits N))),
        Resource.Event.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packOption (modulusBits N))))] := by
  simp only [pack, Circuit.eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
