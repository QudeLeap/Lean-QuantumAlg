/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Context.Union.Unitary
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Context.Union.Unitary
import all QuantumAlg.Core.Execution.Context.Union.References
import all QuantumAlg.Core.Execution.Context.Union.Basis
import Mathlib.Logic.Equiv.Basic

/-!
# Compile a local instruction fragment into an actual resident frame

Membership is a proposition about the existing circuit syntax. The compiler
recurses on that original syntax and emits the same `Circuit` language. It
handles identity, actual unitary instructions, Z measurement into existing
cells, sequence, stored-value branching and finite iteration. It introduces
no allocation, state transformer, execution callback or accounting witness.

The right context remains physically resident. Every compiled path records
the same outcomes and branch choices, with Z outcomes transported only by
the equality of their actual wire dimensions.
-/

namespace QuantumAlg.Circuit

/-- The allocation-free quantum/read fragment of the existing circuit language. -/
@[expose]
public def IsLocal : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    Circuit pre post → Prop
  | _, _, _, .id _ => True
  | _, _, _, .classical _ => False
  | _, _, _, .declaredCall _ => False
  | _, _, _, .unitary _ _ => True
  | _, _, _, .measureZ _ _ => True
  | _, _, _, .randomBits _ _ => False
  | _, _, _, .retain _ _ _ _ => False
  | _, _, _, .prepare _ _ _ _ _ _ => False
  | _, _, _, .seq first second => IsLocal first ∧ IsLocal second
  | _, _, _, .branch _ body => ∀ value, IsLocal (body value)
  | _, _, _, .iterate _ body => IsLocal body
  | _, _, _, .workspace _ _ _ _ _ => False

/-- A member of the local fragment has exactly the same input and output context. -/
public theorem isLocal_endpoints {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : IsLocal code) : pre = post := by
  induction code with
  | id | unitary | measureZ => rfl
  | classical | declaredCall | randomBits | retain | prepare | workspace =>
      exact False.elim supported
  | seq first second firstIH secondIH =>
      exact (firstIH supported.1).trans (secondIH supported.2)
  | branch input body bodyIH =>
      exact bodyIH (CShape.initialValue _) (supported _)
  | iterate => rfl

end QuantumAlg.Circuit

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

/-- Separation at the end follows internally from membership in the local fragment. -/
public theorem localPostDisjoint {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal) (frame : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint pre frame) :
    RuntimeCtx.StorageDisjoint post frame :=
  code.isLocal_endpoints supported ▸ separate

/-- The same writable cell, with only its proved local dimension transported. -/
def measurementLeft {left right : RuntimeCtx .quantum}
    (separate : RuntimeCtx.StorageDisjoint left right) (wire : Fin left.systemCount)
    (output : CWriteRef left (.finite (left.quantumLayout.wire wire).dimension)) :
    CWriteRef (left.disjointUnion right separate)
      (.finite ((left.disjointUnion right separate).quantumLayout.wire
        (leftPosition left right separate wire)).dimension) :=
  Eq.mp (congrArg
    (fun dimension : ℕ+ => CWriteRef (left.disjointUnion right separate) (.finite dimension))
    (contextUnion_left_dimension left right separate wire).symm) (writeLeft separate output)

/-- Structurally compile the original supported circuit into the actual disjoint union. -/
public def frameLocal : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    (code : Circuit pre post) → (supported : code.IsLocal) → (frame : RuntimeCtx kind) →
    (separate : RuntimeCtx.StorageDisjoint pre frame) →
    Circuit (pre.disjointUnion frame separate)
      (post.disjointUnion frame (localPostDisjoint code supported frame separate))
  | _, _, _, .id ctx, _, frame, separate => .id (ctx.disjointUnion frame separate)
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .declaredCall _, supported, _, _ => False.elim supported
  | _, _, _, .unitary (ctx := ctx) program placed, _, frame, separate =>
      .unitary (frameUnitary ctx frame separate program placed)
        (contextUnion_frameUnitary_physical ctx frame separate program placed)
  | _, _, _, .measureZ (ctx := ctx) wire output, _, frame, separate =>
      .measureZ (leftPosition ctx frame separate wire) (measurementLeft separate wire output)
  | _, _, _, .randomBits _ _, supported, _, _ => False.elim supported
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepare _ _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, frame, separate =>
      (frameLocal first supported.1 frame separate).seq
        (frameLocal second supported.2 frame
          (localPostDisjoint first supported.1 frame separate))
  | _, _, _, .branch input body, supported, frame, separate =>
      .branch (inputLeft separate input) fun value =>
        frameLocal (body value) (supported value) frame separate
  | _, _, _, .iterate count body, supported, frame, separate =>
      .iterate count (frameLocal body supported frame separate)
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

/-- Original and compiled executions have corresponding actual finite records. -/
public def frameLocalPathEquiv : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    (code : Circuit pre post) → (supported : code.IsLocal) → (frame : RuntimeCtx kind) →
    (separate : RuntimeCtx.StorageDisjoint pre frame) →
    code.Path ≃ (frameLocal code supported frame separate).Path
  | _, _, _, .id _, _, _, _ => Equiv.refl Unit
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .declaredCall _, supported, _, _ => False.elim supported
  | _, _, _, .unitary _ _, _, _, _ => Equiv.refl Unit
  | _, _, _, .measureZ (ctx := ctx) wire _, _, frame, separate =>
      finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
        (contextUnion_left_dimension ctx frame separate wire).symm)
  | _, _, _, .randomBits _ _, supported, _, _ => False.elim supported
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepare _ _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, frame, separate =>
      Equiv.prodCongr (frameLocalPathEquiv first supported.1 frame separate)
        (frameLocalPathEquiv second supported.2 frame
          (localPostDisjoint first supported.1 frame separate))
  | _, _, _, .branch _ body, supported, frame, separate =>
      Equiv.sigmaCongrRight fun value =>
        frameLocalPathEquiv (body value) (supported value) frame separate
  | _, _, _, .iterate _ body, supported, frame, separate =>
      Equiv.piCongrRight fun _ => frameLocalPathEquiv body supported frame separate
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

/-- A native measurement records the same numerical outcome on the corresponding real wire. -/
theorem frameLocalPathEquiv_measureZ_value {left : RuntimeCtx .quantum}
    (frame : RuntimeCtx .quantum) (separate : RuntimeCtx.StorageDisjoint left frame)
    (wire : Fin left.systemCount)
    (output : CWriteRef left (.finite (left.quantumLayout.wire wire).dimension))
    (outcome : Fin (left.quantumLayout.wire wire).dimension) :
    ((frameLocalPathEquiv (.measureZ wire output) trivial frame separate outcome) :
      Fin ((left.disjointUnion frame separate).quantumLayout.wire
        (leftPosition left frame separate wire)).dimension).val =
      outcome.val := by
  rfl

/-- Sequential paths retain the actual first and second execution records in order. -/
theorem frameLocalPathEquiv_seq {pre mid post : RuntimeCtx .quantum}
    (first : Circuit pre mid) (second : Circuit mid post)
    (supported : (first.seq second).IsLocal) (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint pre frame) (path : (first.seq second).Path) :
    frameLocalPathEquiv (first.seq second) supported frame separate path =
      (frameLocalPathEquiv first supported.1 frame separate path.1,
        frameLocalPathEquiv second supported.2 frame
          (localPostDisjoint first supported.1 frame separate) path.2) := by
  rfl

/-- A stored-value branch keeps its actual selected value and the selected body's record. -/
theorem frameLocalPathEquiv_branch {pre post : RuntimeCtx .quantum} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit pre post)
    (supported : (Circuit.branch input body).IsLocal) (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint pre frame) (path : (Circuit.branch input body).Path) :
    frameLocalPathEquiv (.branch input body) supported frame separate path =
      ⟨path.1, frameLocalPathEquiv (body path.1) (supported path.1) frame separate path.2⟩ := by
  rfl

/-- Finite repetition retains the record of every actual iteration at its original index. -/
theorem frameLocalPathEquiv_iterate {ctx : RuntimeCtx .quantum}
    (count : Nat) (body : Circuit ctx ctx) (supported : body.IsLocal)
    (frame : RuntimeCtx .quantum) (separate : RuntimeCtx.StorageDisjoint ctx frame)
    (path : (Circuit.iterate count body).Path) (index : Fin count) :
    frameLocalPathEquiv (.iterate count body) supported frame separate path index =
      frameLocalPathEquiv body supported frame separate (path index) := by
  rfl

end

end QuantumAlg.Execution.ContextUnion
