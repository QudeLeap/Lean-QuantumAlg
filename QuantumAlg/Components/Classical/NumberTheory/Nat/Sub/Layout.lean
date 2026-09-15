/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.Read

/-!
# Caller-owned storage for saturating natural subtraction

Both words have the same arbitrary width, including zero. The output may
alias an operand: each selected instruction reads its inputs before writing.
No initial value is required for the comparison latch or output word.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSub

/-- Read a writable cell through its existing structural storage reference. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Caller-owned references for one same-width saturating subtraction. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Left subtraction operand. -/
  left : CInputRef ctx (.unsignedWord width)
  /-- Right subtraction operand. -/
  right : CInputRef ctx (.unsignedWord width)
  /-- Workspace comparison flag indicating whether the result saturates. -/
  lessThan : CWriteRef ctx .bit
  lessThanRole : lessThan.toCStorageRef.role = .workspace
  /-- Workspace holding the subtraction result. -/
  output : CWriteRef ctx (.unsignedWord width)
  outputRole : output.toCStorageRef.role = .workspace

/-- Separation retains the operands during comparison and the flag during the selected write. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  leftAvoidsLessThan : refs.lessThan.key ∉ refs.left.storageKeys
  rightAvoidsLessThan : refs.lessThan.key ∉ refs.right.storageKeys
  lessThanAvoidsOutput : refs.output.key ∉ (writeInput refs.lessThan).storageKeys

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSub
