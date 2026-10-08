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
public def IsLocal : {model : ExecutionModel} → {pre post : RuntimeCtx model.kind} →
    Circuit model pre post → Prop
  | _, _, _, .id _ => True
  | _, _, _, .classical _ => False
  | _, _, _, .classicalQuery _ => False
  | _, _, _, .unitary _ => True
  | _, _, _, .measureZ _ _ => True
  | _, _, _, .retain _ _ _ _ => False
  | _, _, _, .prepareZero _ _ _ _ _ => False
  | _, _, _, .seq first second => IsLocal first ∧ IsLocal second
  | _, _, _, .branch _ body => ∀ value, IsLocal (body value)
  | _, _, _, .iterate _ body => IsLocal body
  | _, _, _, .workspace _ _ _ _ _ => False

/-- A member of the local fragment has exactly the same input and output context. -/
public theorem isLocal_endpoints {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : IsLocal code) : pre = post := by
  induction code with
  | id | unitary | measureZ => rfl
  | classical | classicalQuery | retain | prepareZero | workspace =>
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
public theorem localPostDisjoint {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) (frame : RuntimeCtx model.kind)
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
public def frameLocal : {model : ExecutionModel} → {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) → (frame : RuntimeCtx model.kind) →
    (separate : RuntimeCtx.StorageDisjoint pre frame) →
    Circuit model (pre.disjointUnion frame separate)
      (post.disjointUnion frame (localPostDisjoint code supported frame separate))
  | _, _, _, .id ctx, _, frame, separate => .id (ctx.disjointUnion frame separate)
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _ => False.elim supported
  | _, _, _, .unitary (ctx := ctx) program, _, frame, separate =>
      .unitary (frameUnitary ctx frame separate program)
  | _, _, _, .measureZ (ctx := ctx) wire output, _, frame, separate =>
      .measureZ (leftPosition ctx frame separate wire) (measurementLeft separate wire output)
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _ => False.elim supported
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
public def frameLocalPathEquiv : {model : ExecutionModel} → {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) → (frame : RuntimeCtx model.kind) →
    (separate : RuntimeCtx.StorageDisjoint pre frame) →
    code.Path ≃ (frameLocal code supported frame separate).Path
  | _, _, _, .id _, _, _, _ => Equiv.refl Unit
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _ => False.elim supported
  | _, _, _, .unitary _, _, _, _ => Equiv.refl Unit
  | _, _, _, .measureZ (ctx := ctx) wire _, _, frame, separate =>
      finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
        (contextUnion_left_dimension ctx frame separate wire).symm)
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _ => False.elim supported
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
theorem frameLocalPathEquiv_measureZ_value {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {left : RuntimeCtx .quantum}
    (frame : RuntimeCtx .quantum) (separate : RuntimeCtx.StorageDisjoint left frame)
    (wire : Fin left.systemCount)
    (output : CWriteRef left (.finite (left.quantumLayout.wire wire).dimension))
    (outcome : Fin (left.quantumLayout.wire wire).dimension) :
    ((frameLocalPathEquiv (.measureZ (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) wire output)
      trivial frame separate outcome) :
      Fin ((left.disjointUnion frame separate).quantumLayout.wire
        (leftPosition left frame separate wire)).dimension).val =
      outcome.val := by
  rfl

/-- Sequential paths retain the actual first and second execution records in order. -/
theorem frameLocalPathEquiv_seq {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind}
    (first : Circuit model pre mid) (second : Circuit model mid post)
    (supported : (first.seq second).IsLocal) (frame : RuntimeCtx model.kind)
    (separate : RuntimeCtx.StorageDisjoint pre frame) (path : (first.seq second).Path) :
    frameLocalPathEquiv (first.seq second) supported frame separate path =
      (frameLocalPathEquiv first supported.1 frame separate path.1,
        frameLocalPathEquiv second supported.2 frame
          (localPostDisjoint first supported.1 frame separate) path.2) := by
  rfl

/-- A stored-value branch keeps its actual selected value and the selected body's record. -/
theorem frameLocalPathEquiv_branch {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit model pre post)
    (supported : (Circuit.branch input body).IsLocal) (frame : RuntimeCtx model.kind)
    (separate : RuntimeCtx.StorageDisjoint pre frame) (path : (Circuit.branch input body).Path) :
    frameLocalPathEquiv (.branch input body) supported frame separate path =
      ⟨path.1, frameLocalPathEquiv (body path.1) (supported path.1) frame separate path.2⟩ := by
  rfl

/-- Finite repetition retains the record of every actual iteration at its original index. -/
theorem frameLocalPathEquiv_iterate {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (count : Nat) (body : Circuit model ctx ctx) (supported : body.IsLocal)
    (frame : RuntimeCtx model.kind) (separate : RuntimeCtx.StorageDisjoint ctx frame)
    (path : (Circuit.iterate count body).Path) (index : Fin count) :
    frameLocalPathEquiv (.iterate count body) supported frame separate path index =
      frameLocalPathEquiv body supported frame separate (path index) := by
  rfl

end

end QuantumAlg.Execution.ContextUnion
