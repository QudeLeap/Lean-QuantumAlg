/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Body
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Initialization

/-!
# Actual lexical signed-coefficient reduction

The original work word, sign bit and remainder word are genuinely allocated
in that order. The existing heterogeneous allocator supplies all internal
cell identities, separation and initial values. Both original operands and
the arbitrary original output retain their caller storage identities.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The allocator stores its deepest head first: actual entry is work, sign, then remainder. -/
def signedReductionShapes (width : Nat) : List CShape :=
  [.unsignedWord width, .bit, .unsignedWord (signedWidth width)]

/-- Actual deepest unsigned magnitude-remainder cell. -/
def signedRemainderCell (cells : Cells ctx (signedReductionShapes width)) :
    CWriteRef ctx (.unsignedWord width) :=
  (cellAt cells ⟨0, by change 0 < 3; decide⟩).ref

/-- Actual retained sign bit between the work and remainder scopes. -/
def signedNegativeCell (cells : Cells ctx (signedReductionShapes width)) : CWriteRef ctx .bit :=
  (cellAt cells ⟨1, by change 1 < 3; decide⟩).ref

/-- Actual original signed-width work cell, allocated first. -/
def signedWorkCell (cells : Cells ctx (signedReductionShapes width)) :
    CWriteRef ctx (.unsignedWord (signedWidth width)) :=
  (cellAt cells ⟨2, by change 2 < 3; decide⟩).ref

/-- Complete original signed reduction with three genuine persistent scratch allocations. -/
def withSignedReduction (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  withCells ctx (signedReductionShapes width) fun cells _ transport _ =>
    signedReductionBody (transport.liftInput raw) (transport.liftInput modulus)
      (signedWorkCell cells) (signedNegativeCell cells) (signedRemainderCell cells)
      (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
