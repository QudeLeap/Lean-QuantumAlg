/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Model
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Initialization

/-!
# Seven actual lexical cells of the extended-Euclidean state

The heterogeneous layout holds two remainder words, the four coefficients at
the original execution width, and one activity bit. The existing lexical
allocator generates their keys from the actual caller context, establishing
internal distinctness, caller-read separation, and their initial stored values.
A retained result supplies the separate zero sentinel at the enclosing entry.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Remainders, original-width coefficient basis, and the actual branch bit. -/
def stateShapes (width : Nat) : List CShape :=
  [.unsignedWord width, .unsignedWord width,
    .unsignedWord (PureXGCD.executionCoefficientWidth width),
    .unsignedWord (PureXGCD.executionCoefficientWidth width),
    .unsignedWord (PureXGCD.executionCoefficientWidth width),
    .unsignedWord (PureXGCD.executionCoefficientWidth width), .bit]

/-- The current remainder, initially the original left operand. -/
def firstCell (cells : Cells ctx (stateShapes width)) :
    CWriteRef ctx (.unsignedWord width) :=
  (cellAt cells ⟨0, by change 0 < 7; decide⟩).ref

/-- The previous remainder, initially the original right operand. -/
def secondCell (cells : Cells ctx (stateShapes width)) :
    CWriteRef ctx (.unsignedWord width) :=
  (cellAt cells ⟨1, by change 1 < 7; decide⟩).ref

/-- The left coefficient of the current remainder. -/
def firstLeftCell (cells : Cells ctx (stateShapes width)) :
    CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width)) :=
  (cellAt cells ⟨2, by change 2 < 7; decide⟩).ref

/-- The right coefficient of the current remainder. -/
def firstRightCell (cells : Cells ctx (stateShapes width)) :
    CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width)) :=
  (cellAt cells ⟨3, by change 3 < 7; decide⟩).ref

/-- The left coefficient of the previous remainder. -/
def secondLeftCell (cells : Cells ctx (stateShapes width)) :
    CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width)) :=
  (cellAt cells ⟨4, by change 4 < 7; decide⟩).ref

/-- The right coefficient of the previous remainder. -/
def secondRightCell (cells : Cells ctx (stateShapes width)) :
    CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width)) :=
  (cellAt cells ⟨5, by change 5 < 7; decide⟩).ref

/-- The condition selecting the next actual Euclidean iteration. -/
def activeCell (cells : Cells ctx (stateShapes width)) : CWriteRef ctx .bit :=
  (cellAt cells ⟨6, by change 6 < 7; decide⟩).ref

/-- Indexed physical identities of precisely the seven actual state cells. -/
def stateKey (cells : Cells ctx (stateShapes width)) (index : Fin 7) : StorageKey :=
  (cellAt cells index).ref.key

/-- Actual lexical distinctness gives every pair of internal cells different keys. -/
theorem xgcdNativeState_key_injective (cells : Cells ctx (stateShapes width))
    (distinct : cells.Distinct) : Function.Injective (stateKey cells) :=
  workspaceCells_cellAt_key_injective cells distinct

/-- Every state cell avoids every structurally transported caller read. -/
theorem xgcdNativeState_input_separated {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport)
    {shape : CShape} (input : CInputRef outer shape) (index : Fin 7) :
    stateKey cells index ∉ (transport.liftInput input).storageKeys :=
  Cells.workspaceCells_cellAt_transport_avoids cells transport separated input index

/-- Lexical entry gives each actual state cell its declared initial encoding. -/
theorem xgcdNativeState_initial_value (cells : Cells ctx (stateShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) (index : Fin 7) :
    store.read (.storage (cellAt cells index).ref.toCStorageRef) =
      CShape.initialValue ((stateShapes width).get index) :=
  Cells.workspaceCells_cellAt_initialized cells store initialized index

/-- Allocate the seven states through the existing fresh lexical Circuit instruction. -/
def withStateCells {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (width : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner (stateShapes width)),
      cells.Distinct → (transport : Transport ctx inner) →
      cells.TransportSeparated transport → Circuit model inner inner) : Circuit model ctx ctx :=
  withCells ctx (stateShapes width) body

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
