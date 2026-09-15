/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Centering.Layout

/-!
# Actual stored comparisons and native centered-target arithmetic

Self-XOR initializes the original scratch before the zero test. The original
modulus is then copied and halved, and the actual second comparison is stored.
Both actual comparison bits select native subtraction or complement/increment
in the same chronological Circuit interpreter.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Native zero comparison against the original scratch word after its actual initialization. -/
def zeroOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product refs.a (writeInput refs.scratch)) refs.isZero

/-- Native copy of the original modulus into the original scratch word. -/
def copyOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx refs.modulus refs.scratch

/-- Native strict comparison with the actual halved modulus in the original scratch word. -/
def belowOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx (.product refs.a (writeInput refs.scratch)) refs.belowHalf

/-- Actual scratch initialization, zero test, modulus copy, halving and strict half comparison. -/
def prepareInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (Word.PowerOfTwo.clearOp refs.scratch))
    (.seq (.classical (zeroOp refs)) (.seq (.classical (copyOp refs))
      (.seq (.classical (Word.Split.shiftOp refs.scratch)) (.classical (belowOp refs)))))

/-- The actual chronological five-instruction comparison store. -/
def prepareStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  let cleared := store.applyOp (Word.PowerOfTwo.clearOp refs.scratch)
  let tested := cleared.applyOp (zeroOp refs)
  let copied := tested.applyOp (copyOp refs)
  let halved := copied.applyOp (Word.Split.shiftOp refs.scratch)
  halved.applyOp (belowOp refs)

/-- The actual comparison store and all five native instruction paths. -/
def prepareStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (prepareInto refs).Path :=
  (prepareStore refs store, ((), ((), ((), ((), ())))))

/-- Native raw subtraction of actual supplied words into the original centered output. -/
def subOp (refs : Refs ctx width) (left right : CInputRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx (.product left right) refs.output

/-- Native complement of the actual original coordinate into the centered output. -/
def complementOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .complement width ctx refs.a refs.output

/-- Actual native raw negation of the original coordinate into the centered output. -/
def negateInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (complementOp refs)) (.classical (Word.PowerOfTwo.incrementOp refs.output))

/-- The actual complement/increment store and both chronological instruction paths. -/
def negateStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (negateInto refs).Path :=
  ((store.applyOp (complementOp refs)).applyOp (Word.PowerOfTwo.incrementOp refs.output), ((), ()))

/-- Actual stored half comparison selects raw negation or subtraction from the original modulus. -/
def halfArm (refs : Refs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit true => negateInto refs
  | .bit false => .classical (subOp refs refs.modulus refs.a)

/-- Store and path of the actual selected half-comparison arithmetic arm. -/
def halfArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (halfArm refs flag).Path :=
  match flag with
  | .bit true => negateStep refs store
  | .bit false => (store.applyOp (subOp refs refs.modulus refs.a), ())

/-- Read the actual stored half comparison to select the arithmetic that executes. -/
def halfInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (writeInput refs.belowHalf) (halfArm refs)

/-- The actual half-comparison value and its selected arithmetic store/path. -/
def halfStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (halfInto refs).Path :=
  let flag := store.read (writeInput refs.belowHalf)
  let selected := halfArmStep refs flag store
  (selected.1, ⟨flag, selected.2⟩)

/-- Actual zero comparison selects self-subtraction or the actual stored half-comparison branch. -/
def finishArm (refs : Refs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit true => .classical (subOp refs refs.a refs.a)
  | .bit false => halfInto refs

/-- Store and path of the actual zero-test-selected native arithmetic. -/
def finishArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (finishArm refs flag).Path :=
  match flag with
  | .bit true => (store.applyOp (subOp refs refs.a refs.a), ())
  | .bit false => halfStep refs store

/-- Read the actual stored zero test before executing its actual selected arithmetic. -/
def finishInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (writeInput refs.isZero) (finishArm refs)

/-- The actual zero-test value and its complete selected arithmetic store/path. -/
def finishStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (finishInto refs).Path :=
  let flag := store.read (writeInput refs.isZero)
  let selected := finishArmStep refs flag store
  (selected.1, ⟨flag, selected.2⟩)

/-- Original actual centered-target loading with explicit native scratch initialization. -/
def centeredTargetInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (prepareInto refs) (finishInto refs)

/-- The actual stored comparison results feed the actual selected centered arithmetic. -/
def centeredTargetStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (centeredTargetInto refs).Path :=
  let prepared := prepareStep refs store
  let finished := finishStep refs prepared.1
  (finished.1, (prepared.2, finished.2))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
