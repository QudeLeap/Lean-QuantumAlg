/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Preparation
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Resources

/-!
# Live space of the actual paid signed-row preparation

The two unpacked points and negative-coordinate destination are charged for
their complete lexical lifetime. Subtraction and subsequent base doubling
reuse their additional scratch, so their peak is a maximum. Both resident
and auxiliary roles retain the entire original caller context.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open WindowTables.Outer.LiveSpace

/-- Actual additional subtraction cells before their lexical scope returns. -/
def subtractionSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  ((Field.Native.subtractionShapes width).map SpacePool.ofShape).sum +
    Field.Native.subtractionReductionSpace kind width

/-- The two serial arithmetic phases share their actual peak capacity. -/
def arithmeticSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (subtractionSpace kind width) (coefficientScratchSpace kind width)

/-- Actual unpacked-point cells remain live around both arithmetic phases. -/
def additionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  ((scratchShapes width).map SpacePool.ofShape).sum + arithmeticSpace kind width

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma subtraction_bound (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (subtractionSpace model.kind width)
      (Field.Native.subIntoWord (model := model) spec left right output) := by
  intro path
  exact ⟨Field.Native.subIntoWord_resident spec left right output path,
    Field.Native.subIntoWord_auxiliary spec left right output path⟩

/-- Both actual prefix peaks include its lexical cells and the unchanged caller roles. -/
lemma prepare_space (frame : Frame ctx width) (spec : ModulusSpec width)
    (coefficient : Nat) (base target : CInputRef ctx (PointShape width)) :
    Bound (additionalSpace model.kind width)
      (prepare (model := model) frame spec coefficient base target) := by
  unfold prepare
  apply LiveSpace.seq
  · exact (LiveSpace.initialization frame spec coefficient).mono zero_le
  · apply LiveSpace.allocate (Transport.id ctx) (scratchShapes width) _
      (arithmeticSpace model.kind width)
    intro inner cells distinct lift separated
    apply LiveSpace.seq
    · exact (LiveSpace.instruction _).mono zero_le
    · apply LiveSpace.seq
      · exact (LiveSpace.instruction _).mono zero_le
      · apply LiveSpace.seq
        · exact (subtraction_bound _ _ _ _).mono (SpacePool.le_max_left _ _)
        · exact (LiveSpace.pairedBases _ _ _ _ _ _).mono (SpacePool.le_max_right _ _)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
