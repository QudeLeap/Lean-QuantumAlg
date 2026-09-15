/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Declared classical calls

A declaration seals its deterministic evaluator and native subroutine label.
A placed call carries actual readable and writable storage references. The
instruction interpreter reads the input, executes this evaluator, writes its
result, and emits the declaration's event as one step.
-/

namespace QuantumAlg

/-- A declaration-owned, shape-indexed deterministic evaluator.

The evaluator is sealed together with its native subroutine coordinate before
it is placed at concrete runtime references.  This keeps algorithm-specific
classical semantics out of the closed `ClassicalOp` instruction vocabulary
while retaining one executable source for store updates and event accounting.
-/
public structure DeclaredClassicalCall.Access (input output : CShape) where
  private mk ::
  /-- Native coordinate owned by this declared classical operation. -/
  label : Resource.SubroutineLabel
  private evaluator : input.Value → output.Value

namespace DeclaredClassicalCall.Access

/-- Seal a deterministic evaluator under its declaration-owned coordinate. -/
def declare {input output : CShape} (label : Resource.SubroutineLabel)
    (evaluator : input.Value → output.Value) :
    DeclaredClassicalCall.Access input output :=
  ⟨label, evaluator⟩

/-- Execute the evaluator fixed by the sealed declaration. -/
public def eval {input output : CShape}
    (access : DeclaredClassicalCall.Access input output) :
    input.Value → output.Value :=
  access.evaluator

end DeclaredClassicalCall.Access

/-- One typed invocation of a sealed declared classical evaluator.

Its input and output references are exact live-store coordinates.  The output
role is restricted to lexical workspace or retained storage, matching the
ordinary typed instruction boundary. -/
public structure DeclaredClassicalCall {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (input output : CShape) where
  private mk ::
  /-- Sealed evaluator and declaration-owned subroutine coordinate. -/
  access : DeclaredClassicalCall.Access input output
  /-- Exact readable cell supplied to the declared evaluator. -/
  inputRef : CInputRef ctx input
  /-- Exact writable cell receiving the evaluator result. -/
  outputRef : CWriteRef ctx output
  writable : outputRef.toCStorageRef.role = .workspace ∨
    outputRef.toCStorageRef.role = .retained

namespace DeclaredClassicalCall

/-- Place a sealed evaluator at exact readable and writable runtime references. -/
public def place {kind : ProblemKind} {ctx : RuntimeCtx kind} {input output : CShape}
    (access : DeclaredClassicalCall.Access input output)
    (inputRef : CInputRef ctx input) (outputRef : CWriteRef ctx output)
    (writable : outputRef.toCStorageRef.role = .workspace ∨
      outputRef.toCStorageRef.role = .retained) :
    DeclaredClassicalCall ctx input output :=
  ⟨access, inputRef, outputRef, writable⟩

/-- The call's deterministic value semantics. -/
public def eval {kind : ProblemKind} {ctx : RuntimeCtx kind} {input output : CShape}
    (call : DeclaredClassicalCall ctx input output) : input.Value → output.Value :=
  call.access.eval

/-- The one native event emitted by a declared call. -/
public def event {kind : ProblemKind} {ctx : RuntimeCtx kind} {input output : CShape}
    (call : DeclaredClassicalCall ctx input output) : Resource.Event kind :=
  .classicalSubroutine call.access.label

end DeclaredClassicalCall

end QuantumAlg
