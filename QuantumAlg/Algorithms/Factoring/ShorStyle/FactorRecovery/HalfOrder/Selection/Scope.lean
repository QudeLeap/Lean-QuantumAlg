/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection
import all QuantumAlg.Components.Classical.ConstantWord.Circuit

/-!
# The six actual scratch cells of half-power factor selection

The candidate, one, modulus, two comparison bits and final payload are six
real successive workspace allocations. Their references name the actual
fresh heads. The two constants are loaded by native word instructions before
the real left-priority GCD circuit executes. Both GCD calls also account for
their own lexical operands and expanded Euclidean scratch.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Allocate the actual candidate word after the preceding physical workspace cells. -/
@[implicit_reducible]
def candidateContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh

/-- Allocate the actual one word after the preceding physical workspace cells. -/
@[implicit_reducible]
def oneContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (candidateContext ctx N).addWorkspace (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1))
    (candidateContext ctx N).canonicalFreshKey_fresh

/-- Allocate the actual modulus word after the preceding physical workspace cells. -/
@[implicit_reducible]
def modulusContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (oneContext ctx N).addWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1))
    (oneContext ctx N).canonicalFreshKey_fresh

/-- Allocate the actual lower comparison bit after the preceding physical workspace cells. -/
@[implicit_reducible]
def lowerContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (modulusContext ctx N).addWorkspace (modulusContext ctx N).canonicalFreshKey .bit
    (modulusContext ctx N).canonicalFreshKey_fresh

/-- Allocate the actual upper comparison bit after the preceding physical workspace cells. -/
@[implicit_reducible]
def upperContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (lowerContext ctx N).addWorkspace (lowerContext ctx N).canonicalFreshKey .bit
    (lowerContext ctx N).canonicalFreshKey_fresh

/-- Allocate the actual payload word after the preceding physical workspace cells. -/
@[implicit_reducible]
def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (upperContext ctx N).addWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N))
    (upperContext ctx N).canonicalFreshKey_fresh

/-- The actual fresh candidate word, lifted through precisely its later allocations. -/
def candidateRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N + 1)) :=
  let cell0 := CWriteRef.workspaceHead ctx ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
  let cell1 := cell0.underWorkspace (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
  let cell2 := cell1.underWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  cell5

/-- The actual fresh one word, lifted through precisely its later allocations. -/
def oneRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N + 1)) :=
  let cell1 := CWriteRef.workspaceHead (candidateContext ctx N)
    (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
  let cell2 := cell1.underWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  cell5

/-- The actual fresh modulus word, lifted through precisely its later allocations. -/
def modulusRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N + 1)) :=
  let cell2 := CWriteRef.workspaceHead (oneContext ctx N) (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  cell5

/-- The actual fresh lower comparison bit, lifted through precisely its later allocations. -/
def lowerRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) .bit :=
  let cell3 := CWriteRef.workspaceHead (modulusContext ctx N)
    (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  cell5

/-- The actual fresh upper comparison bit, lifted through precisely its later allocations. -/
def upperRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) .bit :=
  let cell4 := CWriteRef.workspaceHead (lowerContext ctx N) (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  cell5

/-- The actual fresh payload word, lifted through precisely its later allocations. -/
def payloadRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N)) :=
  let cell5 := CWriteRef.workspaceHead (upperContext ctx N) (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  cell5

/-- Preserve the exact original input reference beneath all six real cells. -/
def liftInput {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (context ctx N) shape :=
  let ref0 := input.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
  let ref1 := ref0.underWorkspace (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
  let ref2 := ref1.underWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
  let ref3 := ref2.underWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
  let ref4 := ref3.underWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  let ref5 := ref4.underWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  ref5

/-- Preserve the exact original output reference beneath all six real cells. -/
def liftWrite {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (context ctx N) shape :=
  let ref0 := output.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
  let ref1 := ref0.underWorkspace (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
  let ref2 := ref1.underWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
  let ref3 := ref2.underWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
  let ref4 := ref3.underWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  let ref5 := ref4.underWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
  ref5

/-- The actual six fresh references supplied to the already-defined physical factor circuit. -/
def cells (ctx : RuntimeCtx kind) (N : Nat) :
    NativeHalfFactor.Cells (context ctx N) N where
  candidate := candidateRef ctx N
  one := .storage (oneRef ctx N).toCStorageRef
  modulus := .storage (modulusRef ctx N).toCStorageRef
  lower := lowerRef ctx N
  upper := upperRef ctx N
  payload := payloadRef ctx N

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Load the two actual constants before reading them in the genuine GCD-selection circuit. -/
def body (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (context ctx N) (context ctx N) :=
  .seq (ConstantWord.circuit (model := model) (oneRef ctx N) 1)
    (.seq (ConstantWord.circuit (model := model) (modulusRef ctx N) N)
      (NativeHalfFactor.code (model := model) (liftInput halfPower) (cells ctx N) (liftWrite
          output)))

/-- Enter all six real scratch cells and release them after the actual factor result is written. -/
def code (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh
    (.workspace (candidateContext ctx N) (candidateContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1))
      (candidateContext ctx N).canonicalFreshKey_fresh
      (.workspace (oneContext ctx N) (oneContext ctx N).canonicalFreshKey
        (.unsignedWord (modulusBits N + 1))
        (oneContext ctx N).canonicalFreshKey_fresh
        (.workspace (modulusContext ctx N) (modulusContext ctx N).canonicalFreshKey .bit
          (modulusContext ctx N).canonicalFreshKey_fresh
          (.workspace (lowerContext ctx N) (lowerContext ctx N).canonicalFreshKey .bit
            (lowerContext ctx N).canonicalFreshKey_fresh
            (.workspace (upperContext ctx N) (upperContext ctx N).canonicalFreshKey
              (.unsignedWord (modulusBits N))
              (upperContext ctx N).canonicalFreshKey_fresh
              (body (model := model) halfPower output))))))

end

/-- The entire half-factor scope keeps exactly the original physical quantum bank. -/
lemma quantumWires (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
