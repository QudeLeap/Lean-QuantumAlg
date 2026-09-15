/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Scan.Iteration

/-!
# Actual finite lexical storage of order recovery

The recovery field list is fixed and algorithm-specific. Its recursion only
assembles existing workspace instructions, fresh heads and structural lifts;
it introduces no instruction syntax or runtime transformation. The same list
defines the live context, each actual field reference, and matching releases.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

/-- The actual finite set of cursor, validation and result-latch cells. -/
inductive RecoveryField where
  | zero | one | numerator | denominator | older | previous | candidate
  | selected | active | accepted | positive | valid | power
  deriving DecidableEq

/-- Each named recovery cell has its actual word or Boolean shape. -/
def recoveryFieldShape (modulusWidth candidateWidth : Nat) : RecoveryField → CShape
  | .one | .power => .unsignedWord modulusWidth
  | .active | .accepted | .positive | .valid => .bit
  | .zero | .numerator | .denominator | .older | .previous | .candidate | .selected =>
      .unsignedWord candidateWidth

/-- The concrete allocation order of the thirteen real recovery fields. -/
@[reducible] def recoveryFields : List RecoveryField :=
  [.zero, .one, .numerator, .denominator, .older, .previous, .candidate,
    .selected, .active, .accepted, .positive, .valid, .power]

variable {kind : ProblemKind}

/-- Actual context obtained by allocating the given suffix of the fixed recovery field list. -/
@[reducible] def fieldsContext (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    List RecoveryField → RuntimeCtx kind
  | [] => ctx
  | field :: rest => fieldsContext
      (ctx.addWorkspace ctx.canonicalFreshKey (recoveryFieldShape modulusWidth candidateWidth field)
        ctx.canonicalFreshKey_fresh) modulusWidth candidateWidth rest

/-- Structural lift of an original read through the actual recovery allocations. -/
def underRecoveryFields {ctx : RuntimeCtx kind} {shape : CShape}
    (modulusWidth candidateWidth : Nat) : (fields : List RecoveryField) → CInputRef ctx shape →
      CInputRef (fieldsContext ctx modulusWidth candidateWidth fields) shape
  | [], input => input
  | field :: rest, input => underRecoveryFields modulusWidth candidateWidth rest
      (input.underWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

/-- Structural lift of an original destination through those same allocations. -/
def writeUnderRecoveryFields {ctx : RuntimeCtx kind} {shape : CShape}
    (modulusWidth candidateWidth : Nat) : (fields : List RecoveryField) → CWriteRef ctx shape →
      CWriteRef (fieldsContext ctx modulusWidth candidateWidth fields) shape
  | [], output => output
  | field :: rest, output => writeUnderRecoveryFields modulusWidth candidateWidth rest
      (output.underWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

/-- Each field reference comes from its genuine fresh head, lifted through subsequent heads. -/
def recoveryFieldCell (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    (fields : List RecoveryField) → (index : Fin fields.length) →
      CWriteRef (fieldsContext ctx modulusWidth candidateWidth fields)
        (recoveryFieldShape modulusWidth candidateWidth (fields.get index))
  | [], index => Fin.elim0 index
  | field :: rest, index =>
      Fin.cases
        (writeUnderRecoveryFields modulusWidth candidateWidth rest
          (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh))
        (fun tail => recoveryFieldCell
          (ctx.addWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
          modulusWidth candidateWidth rest tail) index

/-- Actual allocation and matching release around the recovery body. -/
def scopeRecoveryFields (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    (fields : List RecoveryField) →
      Circuit (fieldsContext ctx modulusWidth candidateWidth fields)
        (fieldsContext ctx modulusWidth candidateWidth fields) → Circuit ctx ctx
  | [], body => body
  | field :: rest, body =>
      .workspace ctx ctx.canonicalFreshKey (recoveryFieldShape modulusWidth candidateWidth field)
        ctx.canonicalFreshKey_fresh
        (scopeRecoveryFields
          (ctx.addWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
          modulusWidth candidateWidth rest body)

/-- Actual repeated canonical initialization of the recovery workspace heads. -/
def enterRecoveryFields {ctx : RuntimeCtx kind} (modulusWidth candidateWidth : Nat) :
    (fields : List RecoveryField) → Store ctx →
      Store (fieldsContext ctx modulusWidth candidateWidth fields)
  | [], store => store
  | field :: rest, store => enterRecoveryFields modulusWidth candidateWidth rest
      (store.pushWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

/-- Actual reverse-order release of precisely those recovery heads. -/
def leaveRecoveryFields (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    (fields : List RecoveryField) →
      Store (fieldsContext ctx modulusWidth candidateWidth fields) → Store ctx
  | [], store => store
  | field :: rest, store =>
      Store.popWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh
        (leaveRecoveryFields
          (ctx.addWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
          modulusWidth candidateWidth rest store)

/-- The complete live recovery context, with every original entry retained. -/
@[reducible] def recoveryContext (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    RuntimeCtx kind :=
  fieldsContext ctx modulusWidth candidateWidth recoveryFields

/-- The scan consumes the exact thirteen field references of the actual allocation sequence. -/
def recoveryCells (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    ScanCells (recoveryContext ctx modulusWidth candidateWidth) modulusWidth candidateWidth where
  cursor :=
    { numerator := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 2
      denominator := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 3
      older := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 4
      previous := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 5
      candidate := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 6
      active := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 8 }
  selected := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 7
  accepted := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 9
  zero := cellRead (recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 0)
  one := cellRead (recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 1)
  power := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 12
  positive := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 10
  valid := recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields 11

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
