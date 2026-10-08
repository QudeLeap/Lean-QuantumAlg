/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Actual original order-one recovery program

The original retained optional word is allocated before the original zero
candidate workspace and inner equality-tag workspace. Actual word equality
constructs the true tag, then the original optional pack stores the zero
candidate. Both lexical cells are released while the result remains live.
The program has no secret input or mathematical result callback.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
variable {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Head-deepest allocation preserves the original candidate-then-tag lexical order. -/
public def zeroShapes (width : Nat) : List CShape := [.bit, .unsignedWord width]

/-- Original equality instruction compares the actual candidate with itself. -/
public def tagOp (candidate : CInputRef ctx (.unsignedWord width)) (tag : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product candidate candidate) tag

/-- Original option pack reads the computed tag and the same actual candidate word. -/
public def packOp (candidate : CInputRef ctx (.unsignedWord width)) (tag : CWriteRef ctx .bit)
    (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ClassicalOp (.product .bit (.unsignedWord width)) (.option (.unsignedWord width)) ctx ctx :=
  .packOption ctx (.product (.storage tag.toCStorageRef) candidate) output

/-- The original two actual native instructions in their original order. -/
public def zeroBody (candidate : CInputRef ctx (.unsignedWord width)) (tag : CWriteRef ctx .bit)
    (output : CWriteRef ctx (.option (.unsignedWord width))) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (tagOp candidate tag))
    (BitWord.instruction (execution := model) (packOp candidate tag output))

/-- Actual equality update followed by actual optional packing, retaining the full Store. -/
public def zeroBodyStore (candidate : CInputRef ctx (.unsignedWord width))
    (tag : CWriteRef ctx .bit)
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx) : Store ctx :=
  (store.applyOp (tagOp candidate tag)).applyOp (packOp candidate tag output)

/-- Allocate the original zero candidate, then inner tag, and release both after packing. -/
public def zeroInto (output : CWriteRef ctx (.option (.unsignedWord width))) :
    Circuit model ctx ctx :=
  withCells ctx (zeroShapes width) fun cells _ transport _ =>
    zeroBody (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
      (transport.liftWrite output)

/-- The actual order-one endpoint retains its optional result before the original zero routine. -/
public def zeroRetained (ctx : RuntimeCtx model.kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Circuit model ctx (ctx.addRetained key (.option (.unsignedWord width)) fresh) :=
  .seq (.retain ctx key (.option (.unsignedWord width)) fresh)
    (zeroInto (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native
