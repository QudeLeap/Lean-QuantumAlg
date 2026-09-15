/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Layout
import all QuantumAlg.Components.Classical.ConstantWord.Circuit
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Construction

/-!
# The actual two adjacent half-power GCD calls

The direction is a compilation parameter selecting the predecessor or
successor circuit. The same stored half-power is read before any destination
write. The modulus is loaded by the literal native constant-word sequence.
A genuine self-XOR initializes the GCD result used internally as zero; the
existing expanded Euclidean circuit then returns the actual GCD word.

Each invocation releases both operand words and all inner Euclidean scratch.
The later factor selector controls left-first priority on the genuine results.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual structural pair consumed by the existing native Euclidean circuit. -/
def operands (ctx : RuntimeCtx kind) (N : Nat) :
    CInputRef (context ctx N) (NumberTheory.GCD.operandShape (modulusBits N + 1)) :=
  .product (.storage (adjacentRef ctx N).toCStorageRef) (.storage (modulusRef ctx N).toCStorageRef)

/-- Clear the actual GCD output using a closed native instruction on its own stored word. -/
def clearOp (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1))) :
    ClassicalOp
      (.product (.unsignedWord (modulusBits N + 1)) (.unsignedWord (modulusBits N + 1)))
      (.unsignedWord (modulusBits N + 1)) (context ctx N) (context ctx N) :=
  .wordBinary .bitXor (modulusBits N + 1) (context ctx N)
    (.product (.storage (liftWrite output).toCStorageRef)
      (.storage (liftWrite output).toCStorageRef)) (liftWrite output)

/-- The native GCD receives its own actually cleared result, with no zero-input assumption. -/
def gcdTail (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1))) :
    Circuit (context ctx N) (context ctx N) :=
  .seq (.classical (clearOp output))
    (NumberTheory.GCD.lexicalBody (operands ctx N) (liftWrite output))

/-- Literal adjacent arithmetic, modulus loading and the actual Euclidean reduction. -/
def body (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1))) :
    Circuit (context ctx N) (context ctx N) :=
  .seq (NativeAdjacentWord.code successor (liftInput halfPower) (adjacentRef ctx N))
    (.seq (ConstantWord.circuit (modulusRef ctx N) N) (gcdTail output))

/-- Both real adjacent-value operand cells are scoped around the same actual GCD body. -/
def code (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1))) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh
    (.workspace (adjacentContext ctx N) (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body successor halfPower output))

/-- The GCD path contains its real initialization instruction and the expanded Euclidean trace. -/
theorem gcdTail_eventTrace (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (gcdTail output).Path) :
    (gcdTail output).eventTrace path =
      Resource.Event.classicalOperation (.wordBinary .bitXor (modulusBits N + 1)) ::
        (NumberTheory.GCD.lexicalBody (operands ctx N) (liftWrite output)).eventTrace path.2 := rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
