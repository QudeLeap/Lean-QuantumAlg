/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters

/-!
# Actual widened operands of either half-power GCD

Two real lexical words hold the adjacent half-power value and the modulus.
Both have width `m+1`, so neither the successor nor the compiled modulus loses
its highest bit. The destination and every earlier input stay in their exact
original storage roles beneath these scopes.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- First actual lexical word for the adjacent half-power operand. -/
@[implicit_reducible]
def adjacentContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh

/-- Second actual lexical word for the faithfully loaded modulus. -/
@[implicit_reducible]
def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (adjacentContext ctx N).addWorkspace (adjacentContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh

def adjacentRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N + 1)) :=
  (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh

def modulusRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N + 1)) :=
  CWriteRef.workspaceHead (adjacentContext ctx N) (adjacentContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh

def liftInput {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (context ctx N) shape :=
  (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh

def liftWrite {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (context ctx N) shape :=
  (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh

/-- Both lexical cells leave the entire original quantum register unchanged. -/
lemma quantumWires (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
