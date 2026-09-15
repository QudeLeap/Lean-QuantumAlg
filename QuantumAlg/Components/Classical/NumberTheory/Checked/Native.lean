/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Body
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Complete actual checked modular inverse

The original persistent allocation order is modulus, raw gcd, raw left
coefficient and raw right coefficient. The loaded modulus belongs to this
subroutine. Success and inverse destinations retain their caller identities;
all four internal cells are released after the actual selected branch.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular SignedReduction XGCD.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The deepest-first list preserves the original modulus, gcd, left, right allocation order. -/
def checkedInverseShapes (width : Nat) : List CShape :=
  [.unsignedWord (signedWidth width), .unsignedWord (signedWidth width),
    .unsignedWord (width + 1), .unsignedWord (width + 1)]

/-- The actual first allocated modulus cell survives until all checked arithmetic finishes. -/
def checkedModulusCell (cells : Cells ctx (checkedInverseShapes width)) :
    CWriteRef ctx (.unsignedWord (width + 1)) :=
  (cellAt cells ⟨3, by change 3 < 4; decide⟩).ref

/-- The three actual persistent raw outputs retain their original gcd, left, right roles. -/
def checkedRawOutputs (cells : Cells ctx (checkedInverseShapes width)) :
    RawOutputs ctx (width + 1) where
  gcd := (cellAt cells ⟨2, by change 2 < 4; decide⟩).ref
  leftCoefficient := (cellAt cells ⟨1, by change 1 < 4; decide⟩).ref
  rightCoefficient := (cellAt cells ⟨0, by change 0 < 4; decide⟩).ref

/-- The original checked inverse uses its own real modulus loader and four internal cells. -/
def withCheckedInverse (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width)) :
    Circuit ctx ctx :=
  withCells ctx (checkedInverseShapes width) fun cells _ transport _ =>
    checkedInverseBody spec (transport.liftInput denominator) (checkedModulusCell cells)
      (checkedRawOutputs cells) (transport.liftWrite success) (transport.liftWrite inverse)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
