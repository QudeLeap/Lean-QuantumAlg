/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual centered target coordinate instructions

The original code compares the preimage with the initially zero scratch,
copies and halves the modulus in that scratch, and compares the preimage
with the half. Both stored predicates select the actual arithmetic arm:
self-subtraction for zero, complement then increment below half, or modulus
minus preimage otherwise. Equality at half follows the nonnegative arm.
Initialization and reference separation are established by the later actual
workspace layout, rather than assumed by this execution construction.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Real source words, temporary predicate cells and the actual target destination. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The previously scaled source k value. -/
  preimage : CInputRef ctx (.unsignedWord width)
  /-- The unchanged original lattice modulus word. -/
  modulus : CInputRef ctx (.unsignedWord width)
  /-- A real initially zero word, later reused for half the modulus. -/
  scratch : CWriteRef ctx (.unsignedWord width)
  /-- The actual equality result. -/
  isZero : CWriteRef ctx .bit
  /-- The actual strict comparison result. -/
  belowHalf : CWriteRef ctx .bit
  /-- The stored raw signed target coordinate. -/
  output : CWriteRef ctx (.unsignedWord width)

/-- Compare the preimage against the actual initial scratch value. -/
def equalOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product refs.preimage (.storage refs.scratch.toCStorageRef)) refs.isZero

/-- Copy the real modulus into the same scratch cell after the equality instruction. -/
def copyOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx refs.modulus refs.scratch

/-- Halve the actual modulus copy using the original one-bit right shift. -/
def halfOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftRight width ctx (.storage refs.scratch.toCStorageRef) refs.scratch

/-- The strict half comparison keeps the source's nonnegative choice at the tie. -/
def lessOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx
    (.product refs.preimage (.storage refs.scratch.toCStorageRef)) refs.belowHalf

/-- The zero arm uses the actual original self-subtraction instruction. -/
def zeroOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx (.product refs.preimage refs.preimage) refs.output

/-- Complement the actual preimage into its target destination. -/
def complementOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .complement width ctx refs.preimage refs.output

/-- Increment the actual complemented destination to finish two's-complement negation. -/
def incrementOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (.storage refs.output.toCStorageRef) refs.output

/-- The remaining source arm subtracts the preimage from the unchanged modulus. -/
def subtractOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx (.product refs.modulus refs.preimage) refs.output

/-- All four original predicate-preparation instructions run unconditionally and in order. -/
def decisionCode (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (equalOp refs)) (.seq (.classical (copyOp refs))
    (.seq (.classical (halfOp refs)) (.classical (lessOp refs))))

/-- The actual negative arm is precisely complement followed by increment. -/
def negateCode (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (complementOp refs)) (.classical (incrementOp refs))

/-- The stored strict comparison selects the two original nonzero arithmetic arms. -/
def belowChoice (refs : Refs ctx width) (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then negateCode refs else .classical (subtractOp refs)

/-- The inner branch reads the actual stored strict comparison. -/
def nonzeroCode (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (.storage refs.belowHalf.toCStorageRef) (belowChoice refs)

/-- The original outer decision selects self-subtraction or the real inner branch. -/
def zeroChoice (refs : Refs ctx width) (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then .classical (zeroOp refs) else nonzeroCode refs

/-- Both branch selections use the predicate cells written by the original decision prefix. -/
def selectionCode (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (.storage refs.isZero.toCStorageRef) (zeroChoice refs)

/-- The complete native centered-coordinate code preserves the source instruction order. -/
def code (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (decisionCode refs) (selectionCode refs)

/-- Exact store updates of the actual four decision instructions. -/
def decisionStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  (((store.applyOp (equalOp refs)).applyOp (copyOp refs)).applyOp (halfOp refs)).applyOp
    (lessOp refs)

/-- Exact store updates of the selected complement-and-increment arm. -/
def negateStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  (store.applyOp (complementOp refs)).applyOp (incrementOp refs)

noncomputable section

/-- The actual stored comparison chooses the matching real arithmetic path. -/
def belowStep (refs : Refs ctx width) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (belowChoice refs value).Path :=
  match value with
  | .bit false => (store.applyOp (subtractOp refs), ())
  | .bit true => (negateStore refs store, ((), ()))

/-- The inner branch records the value actually read and the selected arithmetic path. -/
def nonzeroStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (nonzeroCode refs).Path :=
  let value := store.read (.storage refs.belowHalf.toCStorageRef)
  let selected := belowStep refs value store
  (selected.1, ⟨value, selected.2⟩)

/-- The real equality decision chooses the self-subtraction or complete inner branch record. -/
def zeroStep (refs : Refs ctx width) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (zeroChoice refs value).Path :=
  match value with
  | .bit false => nonzeroStep refs store
  | .bit true => (store.applyOp (zeroOp refs), ())

/-- The outer record stores the equality value actually read from the decision cell. -/
def selectionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (selectionCode refs).Path :=
  let value := store.read (.storage refs.isZero.toCStorageRef)
  let selected := zeroStep refs value store
  (selected.1, ⟨value, selected.2⟩)

/-- The full actual decision-prefix and two-level branch record. -/
def step (refs : Refs ctx width) (store : Store ctx) : Store ctx × (code refs).Path :=
  let selected := selectionStep refs (decisionStore refs store)
  (selected.1, (((), ((), ((), ()))), selected.2))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering
