/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Values
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation
import Mathlib.Data.Fin.Rev

/-!
# Original raw-recovery preparation through thirteen actual lexical cells

The original decoded, raw-frequency, constant, scaling and negation cells
are allocated in their original chronological order. They all remain live
through actual preparation and the supplied actual continuation. Fresh
allocation supplies key separation and the denominator and zero initializers.
Any further consumer cells belong to that consumer's actual allocation.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Stack order reverses the original thirteen chronological allocations. -/
def preparationShapes (width : Nat) : List CShape :=
  [.bit, .unsignedWord width, .unsignedWord width, .unsignedWord width,
    .unsignedWord width, .unsignedWord width, scaleDivisionShape width,
    .unsignedWord (width + (width + 1)), .unsignedWord (width + 1),
    .unsignedWord (width + 1), .unsignedWord width, .unsignedWord width,
    .unsignedWord (width + width)]

/-- Rebuild the original semantic roles from their actual reverse-stack positions. -/
def preparationRefs (cells : Cells ctx (preparationShapes width)) : PreparationRefs ctx width where
  decoded := (cellAt cells (12 : Fin 13)).ref
  rawLeft := (cellAt cells (11 : Fin 13)).ref
  rawRight := (cellAt cells (10 : Fin 13)).ref
  modulusWide := (cellAt cells (9 : Fin 13)).ref
  denominator := (cellAt cells (8 : Fin 13)).ref
  product := (cellAt cells (7 : Fin 13)).ref
  division := (cellAt cells (6 : Fin 13)).ref
  left := (cellAt cells (5 : Fin 13)).ref
  right := (cellAt cells (4 : Fin 13)).ref
  modulus := (cellAt cells (3 : Fin 13)).ref
  zero := (cellAt cells (2 : Fin 13)).ref
  negatedRight := (cellAt cells (1 : Fin 13)).ref
  negationFlag := (cellAt cells (0 : Fin 13)).ref

/-- Original chronological key indices are exactly the reversed actual stack indices. -/
theorem preparationRefs_key (cells : Cells ctx (preparationShapes width)) (index : Fin 13) :
    (preparationRefs cells).key index = (cellAt cells index.rev).ref.key := by
  fin_cases index <;> rfl

/-- The actual thirteen allocations supply every pairwise separation used by preparation. -/
theorem preparationRefs_separated (cells : Cells ctx (preparationShapes width))
    (distinct : cells.Distinct) : (preparationRefs cells).Separated := by
  intro left right same
  apply Fin.rev_injective
  apply workspaceCells_cellAt_key_injective cells distinct
  exact (preparationRefs_key cells left).symm.trans
    (same.trans (preparationRefs_key cells right))

/-- Real initial cell contents provide the only two zero premises needed by preparation. -/
theorem preparationRefs_initialized_zero (cells : Cells ctx (preparationShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) :
    (store.read (scaleRead (preparationRefs cells).denominator)).toNat = 0 ∧
      (store.read (scaleRead (preparationRefs cells).zero)).toNat = 0 := by
  constructor
  · exact congrArg CShape.Value.toNat
      (Cells.workspaceCells_cellAt_initialized cells store initialized (8 : Fin 13))
  · exact congrArg CShape.Value.toNat
      (Cells.workspaceCells_cellAt_initialized cells store initialized (2 : Fin 13))

/-- Every actual preparation destination avoids the full storage support of all caller reads. -/
theorem preparationRefs_transport_avoids {outer : RuntimeCtx kind}
    (cells : Cells ctx (preparationShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (index : Fin 13)
    {shape : CShape} (input : CInputRef outer shape) :
    (preparationRefs cells).key index ∉ (transport.liftInput input).storageKeys := by
  rw [preparationRefs_key]
  exact Cells.workspaceCells_cellAt_transport_avoids cells transport separated input index.rev

/-- Keep all original preparation cells live through the actual subsequent consumer. -/
def withPreparation {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (consumer : ∀ {inner : RuntimeCtx model.kind}, PreparationRefs inner width →
      Transport ctx inner → Circuit model inner inner) : Circuit model ctx ctx :=
  withCells (model := model) ctx (preparationShapes width) fun cells _ transport _ =>
    .seq (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (consumer (preparationRefs cells) transport)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
