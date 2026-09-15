/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope
import all QuantumAlg.Components.Classical.ConstantWord.Circuit
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction

/-!
# Actual order recovery and factor-tail dispatch from stored Shor outcomes

The real canonical-base pack and existing native order-recovery program read
the stored sampler parameter and the same measured phase bits. A real option
unpack exposes the actual order tag and word. Closed bit and word instructions
check acceptance, positivity and evenness before the real half-order power and
left-priority GCD suffix run.

The known-modulus even case remains first. Otherwise the actual sampler's
early-factor bit has priority over order-based reduction. Every output is
materialized by a real nominal option-pack instruction; no arithmetic or
factor-selection callback is part of this circuit.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The real lexical cells used around order recovery and the final half-power suffix. -/
structure Cells (ctx : RuntimeCtx kind) (N : Nat) where
  base : CWriteRef ctx (.canonicalResidue (modulusBits N))
  order : CWriteRef ctx (.option (.unsignedWord (phaseBits N + 1)))
  expanded : CWriteRef ctx (.product .bit (.unsignedWord (phaseBits N + 1)))
  zero : CWriteRef ctx (.unsignedWord (phaseBits N + 1))
  active : CWriteRef ctx .bit
  positive : CWriteRef ctx .bit
  halfPower : CWriteRef ctx (.unsignedWord (modulusBits N))

/-- The actual nominal unpacked optional order, read structurally from its real storage cell. -/
def expandedRead (cells : Cells ctx N) :
    CInputRef ctx (.product .bit (.unsignedWord (phaseBits N + 1))) :=
  .storage cells.expanded.toCStorageRef

def orderRead (cells : Cells ctx N) : CInputRef ctx (.unsignedWord (phaseBits N + 1)) :=
  .second (expandedRead cells)

def activeRead (cells : Cells ctx N) : CInputRef ctx .bit :=
  .storage cells.active.toCStorageRef

def halfRead (cells : Cells ctx N) : CInputRef ctx (.unsignedWord (modulusBits N)) :=
  .storage cells.halfPower.toCStorageRef

/-- Materialize the exact stored sampler base in the existing canonical residue shape. -/
def packBaseOp (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N) :
    ClassicalOp (.unsignedWord (modulusBits N)) (.canonicalResidue (modulusBits N)) ctx ctx :=
  .packCanonicalResidue (modulusBits N) ctx (.first parameter) cells.base

/-- Decode the actual stored optional recovery result through the existing nominal instruction. -/
def unpackOrderOp (cells : Cells ctx N) :
    ClassicalOp (.option (.unsignedWord (phaseBits N + 1)))
      (.product .bit (.unsignedWord (phaseBits N + 1))) ctx ctx :=
  .unpackOption ctx (.storage cells.order.toCStorageRef) cells.expanded

/-- Self-XOR provides the real zero operand of the actual positivity comparison. -/
def clearZeroOp (cells : Cells ctx N) :
    ClassicalOp (.product (.unsignedWord (phaseBits N + 1)) (.unsignedWord (phaseBits N + 1)))
      (.unsignedWord (phaseBits N + 1)) ctx ctx :=
  .wordBinary .bitXor (phaseBits N + 1) ctx
    (.product (.storage cells.zero.toCStorageRef) (.storage cells.zero.toCStorageRef)) cells.zero

/-- The actual low order bit is complemented into the real evenness latch. -/
def evenOrderOp (cells : Cells ctx N) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (.wordBitGet (orderRead cells) (Fin.last (phaseBits N))) cells.active

def positiveOrderOp (cells : Cells ctx N) :
    ClassicalOp (.product (.unsignedWord (phaseBits N + 1)) (.unsignedWord (phaseBits N + 1)))
      .bit ctx ctx :=
  .wordBinary .lessThan (phaseBits N + 1) ctx
    (.product (.storage cells.zero.toCStorageRef) (orderRead cells)) cells.positive

def positiveEvenOp (cells : Cells ctx N) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (activeRead cells) (.storage cells.positive.toCStorageRef)) cells.active

def acceptedOrderOp (cells : Cells ctx N) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (activeRead cells) (.first (expandedRead cells))) cells.active

/-- The selected false tag or computed even-case payload is packed into the real output. -/
def packOutputOp (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    ClassicalOp (.product .bit (.unsignedWord (modulusBits N)))
      (.option (.unsignedWord (modulusBits N))) ctx ctx :=
  .packOption ctx (.product (activeRead cells) (halfRead cells)) output

/-- Copy the actual sampler's optional early factor with the existing nominal representation. -/
def packEarlyOp (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    ClassicalOp (.product .bit (.unsignedWord (modulusBits N)))
      (.option (.unsignedWord (modulusBits N))) ctx ctx :=
  .packOption ctx (.second parameter) output

/-- The actual accepted order feeds the native power and the fully scoped GCD-selection circuit. -/
def reduce (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit ctx ctx :=
  .seq (NativeHalfPower.code source (.storage cells.base.toCStorageRef)
    (orderRead cells) cells.halfPower) (NativeHalfFactorScope.code (halfRead cells) output)

/-- Every runtime order predicate is materialized by its actual native operation. -/
def guardOrder (cells : Cells ctx N) : Circuit ctx ctx :=
  .seq (.classical (clearZeroOp cells))
    (.seq (.classical (evenOrderOp cells))
      (.seq (.classical (positiveOrderOp cells))
        (.seq (.classical (positiveEvenOp cells)) (.classical (acceptedOrderOp cells)))))

/-- Only the actual true guard executes the half-order reduction; false is really packed as none. -/
def checkedOrder (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit ctx ctx :=
  .seq (guardOrder cells)
    (.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output)))

/-- Preserve the original sampler early-factor priority using its actual stored flag. -/
def dispatch (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit ctx ctx :=
  .branch (.first (.second parameter))
    (fun value => if value.toBool then .classical (packEarlyOp parameter output)
      else checkedOrder source cells output)

/-- Actual non-even prefix: stored base packing, native recovery and nominal order decoding. -/
def recovered (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit ctx ctx :=
  .seq (.classical (packBaseOp parameter cells))
    (.seq (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
      phase cells.order)
      (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output)))

/-- The even-modulus flag is set by two real closed Boolean instructions. -/
def clearActiveOp (cells : Cells ctx N) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (activeRead cells) (activeRead cells)) cells.active

def setActiveOp (cells : Cells ctx N) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (activeRead cells) cells.active

/-- The known-modulus even case actually writes and packages the factor two. -/
def evenModulus (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit ctx ctx :=
  .seq (.classical (clearActiveOp cells))
    (.seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2) (.classical (packOutputOp cells output))))

/-- Preserve the original modulus exception and all actual stored-input factor-recovery branches. -/
def code (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit ctx ctx :=
  if 2 < N ∧ Even N then evenModulus cells output else recovered source parameter phase cells output

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
