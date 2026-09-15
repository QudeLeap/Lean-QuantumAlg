/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.TerminalDecode.Encoding
public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Components.Classical.TerminalDecode.Encoding
import all QuantumAlg.Core.Execution.Circuit

/-!
# Native terminal decoder instructions

Each source bit is read after an actual in-place left shift. A stored true bit
selects the increment instruction; a false bit selects identity. Both bit orders
use the same literal fold. No branch computes a decoded word or hides a lookup.

The fold contains exactly the target width's number of shifts. Consequently
its final word is independent of the initial accumulator, without a separate
clearing event. Retained execution allocates the result before this same fold.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open ClassicalAlgorithms.TerminalDecode

/-- Native left shift of the existing accumulator cell. -/
def shiftOp {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (output : CWriteRef ctx (OutputShape width)) :
    ClassicalOp (OutputShape width) (OutputShape width) ctx ctx :=
  .wordUnary .shiftLeft width ctx (writeInput output) output

/-- Native increment of that same cell in the selected true branch. -/
def incrementOp {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (output : CWriteRef ctx (OutputShape width)) :
    ClassicalOp (OutputShape width) (OutputShape width) ctx ctx :=
  .wordUnary .increment width ctx (writeInput output) output

/-- Append one actual structural source bit through stored classical selection. -/
def bitRefRoutine {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx .bit) (output : CWriteRef ctx (OutputShape width)) :
    Circuit ctx ctx :=
  .seq (.classical (shiftOp width output))
    (.branch input (fun value =>
      if value.toBool then .classical (incrementOp width output) else .id ctx))

/-- Literal ordered composition of the source-addressed append instructions. -/
def foldBitRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : CWriteRef ctx (OutputShape width)) :
    List (CInputRef ctx .bit) → Circuit ctx ctx
  | [] => .id ctx
  | input :: rest => .seq (bitRefRoutine input output) (foldBitRefs output rest)

/-- Decode a fixed vector of actual bit references into one existing writable word. -/
def intoFromBitRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (order : BitOrder) (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) : Circuit ctx ctx :=
  foldBitRefs output (List.ofFn (fun index => inputs (sourceIndex order index)))

/-- Decode the stored bit string through the same structural reference fold. -/
def into {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (order : BitOrder) (input : CInputRef ctx (InputShape width))
    (output : CWriteRef ctx (OutputShape width)) : Circuit ctx ctx :=
  intoFromBitRefs order (fun bit => .bitsGet input bit) output

/-- Context retaining the real output word beside every existing runtime entry. -/
abbrev ResultCtx {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  ctx.addRetained key (OutputShape width) fresh

/-- Structural read of the retained output word. -/
def resultRef {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    CInputRef (ResultCtx ctx width key fresh) (OutputShape width) :=
  .storage (CStorageRef.retainedHead ctx key (OutputShape width) fresh)

/-- Allocate the output word, then run the actual decoder beside the older store. -/
def routine {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat)
    (order : BitOrder) (input : CInputRef ctx (InputShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Circuit ctx (ResultCtx ctx width key fresh) :=
  .seq (.retain ctx key (OutputShape width) fresh)
    (into order (input.underRetained key (OutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (OutputShape width) fresh))

end QuantumAlg.ClassicalRoutines.TerminalDecode
