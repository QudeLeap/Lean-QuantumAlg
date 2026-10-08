/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit

/-!
# Actual first-success factor scan over the retained Shor outcomes

Every visit uses its own original parameter and measured phase references.
The complete factor scope writes its real optional candidate into the retained
result cell, and a real nominal unpack exposes its tag and word. The existing
FirstAccepted circuit updates persistent latches in the original tuple order.

The two selector scratch roles share one actual bit, as its existing circuit
and separation theorem permit. The final option pack overwrites the result
cell with the first accepted factor. All nested recovery, power and GCD
workspaces remain part of each actual visit; this assembly hides none of them.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The two original stored operands used by one complete factor-recovery visit. -/
structure Inputs (ctx : RuntimeCtx kind) (N : Nat) where
  parameter : CInputRef ctx (ParameterShape (modulusBits N))
  phase : CInputRef ctx (.bits (phaseBits N))

/-- Actual persistent latches, decoded candidate and the single shared Boolean scratch cell. -/
structure Cells (ctx : RuntimeCtx kind) (N : Nat) where
  candidate : CWriteRef ctx (.product .bit (.unsignedWord (modulusBits N)))
  accepted : CWriteRef ctx .bit
  selected : CWriteRef ctx (.unsignedWord (modulusBits N))
  scratch : CWriteRef ctx .bit

/-- The existing native selector reads only the actual decoded candidate cell. -/
def selectorInputs (cells : Cells ctx N) : FirstAccepted.Inputs ctx (modulusBits N) where
  eligible := .first (.storage cells.candidate.toCStorageRef)
  candidate := .second (.storage cells.candidate.toCStorageRef)

/-- The actual available bit is overwritten by the following conjunction in the same cell. -/
def selectorRefs (cells : Cells ctx N) : FirstAccepted.Refs ctx (modulusBits N) where
  accepted := cells.accepted
  selected := cells.selected
  available := cells.scratch
  take := cells.scratch

/-- Clear the persistent latch by a real closed Boolean instruction before the first visit. -/
def clearAcceptedOp (cells : Cells ctx N) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (.storage cells.accepted.toCStorageRef)
    (.storage cells.accepted.toCStorageRef)) cells.accepted

/-- Decode the optional factor actually written by the complete native recovery scope. -/
def unpackOp (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    ClassicalOp (.option (.unsignedWord (modulusBits N)))
      (.product .bit (.unsignedWord (modulusBits N))) ctx ctx :=
  .unpackOption ctx (.storage result.toCStorageRef) cells.candidate

/-- Read both persistent latches and materialize the actual final optional factor. -/
def packOp (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    ClassicalOp (.product .bit (.unsignedWord (modulusBits N)))
      (.option (.unsignedWord (modulusBits N))) ctx ctx :=
  .packOption ctx (.product (.storage cells.accepted.toCStorageRef)
    (.storage cells.selected.toCStorageRef)) result

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual unpack is followed by the one existing first-accepted selector. -/
def selection (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (unpackOp cells result))
    (FirstAccepted.circuit (model := model) (selectorInputs cells) (selectorRefs cells))

/-- Each visit executes full native factor recovery on those same original stored operands. -/
def visit (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .seq (FactorRecovery.NativeFactorScope.code (model := model) source inputs.parameter inputs.phase
    result)
    (selection (model := model) cells result)

/-- Compile the actual finite input-reference list into its ordered sequence of real visits. -/
def scan (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    List (Inputs ctx N) → Circuit model ctx ctx
  | [] => .id ctx
  | inputs :: rest => .seq (visit (model := model) source inputs cells result) (scan source cells
    result rest)

/-- The true complete scan initializes its latch and finally packs the first accepted factor. -/
def code (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (clearAcceptedOp cells))
    (.seq (scan (model := model) source cells result inputs) (BitWord.instruction (execution :=
      model) (packOp cells result)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
