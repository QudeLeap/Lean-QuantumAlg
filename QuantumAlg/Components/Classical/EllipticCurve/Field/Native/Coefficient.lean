/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Circuit
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Raw
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Actual total field-coefficient program

The original four persistent cells hold the loaded modulus and three raw
XGCD outputs. Widening the denominator has its own lexical lifetime. After
that scope is released, the actual signed-reduction program unconditionally
reduces the right coefficient. Non-unit inputs follow this same total path.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open NumberTheory.Checked.SignedReduction

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural read of the same actual writable coefficient cell. -/
def coefficientRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- The deepest-first list preserves original allocation as modulus, gcd, left, right. -/
def coefficientShapes (width : Nat) : List CShape :=
  [.unsignedWord (signedWidth width), .unsignedWord (signedWidth width),
    .unsignedWord (width + 1), .unsignedWord (width + 1)]

/-- Four original persistent cells; all internal engine scratch is allocated beneath them. -/
structure CoefficientScratch (ctx : RuntimeCtx kind) (width : Nat) where
  modulus : CWriteRef ctx (.unsignedWord (width + 1))
  outputs : NumberTheory.XGCD.Native.RawOutputs ctx (width + 1)

/-- The actual cell roles retain the original four persistent allocation identities. -/
def coefficientScratch (cells : Cells ctx (coefficientShapes width)) :
    CoefficientScratch ctx width where
  modulus := cells.tail.tail.tail.head.ref
  outputs := ⟨cells.tail.tail.head.ref, cells.tail.head.ref, cells.head.ref⟩

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Original actual loading, widened XGCD, and unconditional signed-coefficient reduction. -/
def coefficientBody (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (scratch : CoefficientScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (ConstantWord.circuit scratch.modulus spec.modulus)
    (.seq (NumberTheory.Checked.Native.withWidenedXgcd denominator
      (coefficientRead scratch.modulus) scratch.outputs)
      (NumberTheory.Checked.SignedReduction.Native.withSignedReduction
        (coefficientRead scratch.outputs.rightCoefficient)
        (coefficientRead scratch.modulus) output))

/-- Allocate all original persistent cells and execute the total coefficient path. -/
def coefficientIntoWord (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  withCells ctx (coefficientShapes width) fun cells _ transport _ =>
    coefficientBody spec (transport.liftInput denominator) (coefficientScratch cells)
      (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
