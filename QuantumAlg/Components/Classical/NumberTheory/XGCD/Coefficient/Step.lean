/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Trace

/-!
# Native extended-Euclidean coefficient rotation

The four actual instructions compute the low product, subtract it from the
previous coefficient, and rotate the two coefficient words. Arithmetic uses
the supplied execution width. The signed interpretation and its range proof
are separate from this exact circuit and store equation.

Every quantum block, including its external reference, is retained by these
classical instructions. Scratch values need no initialization promise.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural read of an actual coefficient or scratch cell. -/
def coefficientRead (cell : CWriteRef ctx (.unsignedWord width)) :
    CInputRef ctx (.unsignedWord width) := .storage cell.toCStorageRef

/-- Compute the quotient times the current coefficient modulo the word size. -/
def coefficientProductOp (quotient : CInputRef ctx (.unsignedWord width))
    (first product : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx (.product quotient (coefficientRead first)) product

/-- Subtract the computed product from the previous coefficient. -/
def coefficientSubtractOp (second product updated : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx
    (.product (coefficientRead second) (coefficientRead product)) updated

/-- Copy one existing coefficient word through a charged native instruction. -/
def coefficientCopyOp (source target : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (coefficientRead source) target

/-- Four literal instructions implement one coefficient recurrence and rotation. -/
def coefficientUpdateBody (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (coefficientProductOp quotient first product))
    (.seq (.classical (coefficientSubtractOp second product updated))
      (.seq (.classical (coefficientCopyOp first second))
        (.classical (coefficientCopyOp updated first))))

/-- The actual store produced by precisely those four instruction evaluations. -/
def coefficientUpdateStore (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx :=
  (((store.applyOp (coefficientProductOp quotient first product)).applyOp
    (coefficientSubtractOp second product updated)).applyOp
      (coefficientCopyOp first second)).applyOp (coefficientCopyOp updated first)

/-- The complete execution preserves each quantum-reference block and records its real path. -/
theorem xgcdCoefficientUpdate_execute (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (coefficientUpdateBody quotient first second product updated).execute Reference state =
      state.mapClassical (fun entry =>
        (coefficientUpdateStore quotient first second product updated entry.1,
          (entry.2, ((), ((), ((), ())))))) := by
  simp only [coefficientUpdateBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Independent operation list for one extended-Euclidean coefficient update. -/
def coefficientUpdateEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .sub width),
    .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .copy width)]

/-- The actual path emits one low product, one subtraction, and two copies. -/
theorem xgcdCoefficientUpdate_eventTrace (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody quotient first second product updated).Path) :
    (coefficientUpdateBody quotient first second product updated).eventTrace path =
      coefficientUpdateEvents kind width := rfl

/-- The native resource pool is derived from these same four instructions. -/
theorem xgcdCoefficientUpdate_resourcePool (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody quotient first second product updated).Path) :
    (coefficientUpdateBody quotient first second product updated).resourcePool path =
      ResourcePool.ofList (coefficientUpdateEvents kind width) := rfl

/-- All four dependent operations contribute unit-duration serial depth. -/
theorem xgcdCoefficientUpdate_unitDepth (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody quotient first second product updated).Path) :
    (coefficientUpdateBody quotient first second product updated).depth (fun _ => 1) path = 4 := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
