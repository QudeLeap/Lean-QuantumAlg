/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction

/-!
# Actual complete factor-recovery workspace around one stored Shor outcome

Seven real lexical entries hold the canonical base, optional recovered order,
its decoded tag and word, the zero comparison operand, two bits and the
half-power. The same original parameter and measured phase references are
structurally lifted through these exact heads. Their real factor-tail circuit
runs before every new head is released; the original output and all existing
quantum-bank and classical entries remain in the final context.

The order-recovery, modular-power and GCD routines retain their own actual
nested scratch scopes in this code. The seven outer cells do not replace or
hide those simultaneous workspace requirements.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual allocation of the canonical base after the preceding real entries. -/
@[implicit_reducible]
def baseContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh

/-- The actual allocation of the optional recovered order after the preceding real entries. -/
@[implicit_reducible]
def orderContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (baseContext ctx N).addWorkspace (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh

/-- The actual allocation of the decoded order tag and word after the preceding real entries. -/
@[implicit_reducible]
def expandedContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (orderContext ctx N).addWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh

/-- The actual allocation of the comparison zero word after the preceding real entries. -/
@[implicit_reducible]
def zeroContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (expandedContext ctx N).addWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh

/-- The actual allocation of the active comparison bit after the preceding real entries. -/
@[implicit_reducible]
def activeContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (zeroContext ctx N).addWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh

/-- The actual allocation of the positive comparison bit after the preceding real entries. -/
@[implicit_reducible]
def positiveContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (activeContext ctx N).addWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh

/-- The actual allocation of the half-power word after the preceding real entries. -/
@[implicit_reducible]
def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (positiveContext ctx N).addWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh

/-- The physical fresh head for the canonical base, lifted through its later entries. -/
def baseRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.canonicalResidue (modulusBits N)) :=
  let cell0 := CWriteRef.workspaceHead ctx ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh
  let cell1 := cell0.underWorkspace (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
  let cell2 := cell1.underWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let cell6 := cell5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  cell6

/-- The physical fresh head for the optional recovered order, lifted through its later entries. -/
def orderRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.option (.unsignedWord (phaseBits N + 1))) :=
  let cell1 := CWriteRef.workspaceHead (baseContext ctx N) (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
  let cell2 := cell1.underWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let cell6 := cell5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  cell6

/-- The physical fresh head for the decoded order tag and word, lifted through its later entries. -/
def expandedRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.product .bit (.unsignedWord (phaseBits N + 1))) :=
  let cell2 := CWriteRef.workspaceHead (orderContext ctx N) (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let cell6 := cell5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  cell6

/-- The physical fresh head for the comparison zero word, lifted through its later entries. -/
def zeroRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (phaseBits N + 1)) :=
  let cell3 := CWriteRef.workspaceHead (expandedContext ctx N)
    (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let cell6 := cell5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  cell6

/-- The physical fresh head for the active comparison bit, lifted through its later entries. -/
def activeRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) .bit :=
  let cell4 := CWriteRef.workspaceHead (zeroContext ctx N) (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let cell5 := cell4.underWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let cell6 := cell5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  cell6

/-- The physical fresh head for the positive comparison bit, lifted through its later entries. -/
def positiveRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) .bit :=
  let cell5 := CWriteRef.workspaceHead (activeContext ctx N) (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let cell6 := cell5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  cell6

/-- The physical fresh head for the half-power word, lifted through its later entries. -/
def halfPowerRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N)) :=
  let cell6 := CWriteRef.workspaceHead (positiveContext ctx N)
    (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  cell6

/-- The exact original input lifted through all seven actual allocations. -/
def liftInput {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (context ctx N) shape :=
  let ref0 := input.underWorkspace ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh
  let ref1 := ref0.underWorkspace (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
  let ref2 := ref1.underWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
  let ref3 := ref2.underWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
  let ref4 := ref3.underWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let ref5 := ref4.underWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let ref6 := ref5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  ref6

/-- The exact original output lifted through all seven actual allocations. -/
def liftWrite {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (context ctx N) shape :=
  let ref0 := output.underWorkspace ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh
  let ref1 := ref0.underWorkspace (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
  let ref2 := ref1.underWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
  let ref3 := ref2.underWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
  let ref4 := ref3.underWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let ref5 := ref4.underWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  let ref6 := ref5.underWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
  ref6

/-- The actual seven references consumed by the genuine stored-outcome factor tail. -/
def cells (ctx : RuntimeCtx kind) (N : Nat) :
    NativeFactorTail.Cells (context ctx N) N where
  base := baseRef ctx N
  order := orderRef ctx N
  expanded := expandedRef ctx N
  zero := zeroRef ctx N
  active := activeRef ctx N
  positive := positiveRef ctx N
  halfPower := halfPowerRef ctx N

section Selected

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Run native factor recovery on the same actual original parameter and phase references. -/
def body (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (context ctx N) (context ctx N) :=
  NativeFactorTail.code (model := model) source (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output)

/-- The genuine seven allocations enclose the same native tail and are all actually released. -/
def code (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh
    (.workspace (baseContext ctx N) (baseContext ctx N).canonicalFreshKey
      (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
      (.workspace (orderContext ctx N) (orderContext ctx N).canonicalFreshKey
        (.product .bit (.unsignedWord (phaseBits N + 1)))
        (orderContext ctx N).canonicalFreshKey_fresh
        (.workspace (expandedContext ctx N) (expandedContext ctx N).canonicalFreshKey
          (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
          (.workspace (zeroContext ctx N) (zeroContext ctx N).canonicalFreshKey
            .bit (zeroContext ctx N).canonicalFreshKey_fresh
            (.workspace (activeContext ctx N) (activeContext ctx N).canonicalFreshKey
              .bit (activeContext ctx N).canonicalFreshKey_fresh
              (.workspace (positiveContext ctx N) (positiveContext ctx N).canonicalFreshKey
                (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
                (body (model := model) source parameter phase output)))))))

end Selected

/-- The whole actual factor scope preserves the exact previously allocated quantum bank. -/
lemma quantumWires (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
