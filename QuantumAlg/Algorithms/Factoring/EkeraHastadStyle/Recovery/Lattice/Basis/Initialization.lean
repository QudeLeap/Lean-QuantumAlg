/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Constants.PowerOfTwo

/-!
# Original loading order in the actual twelve-word lattice layout

The two decoded j words are copied into the first basis row before its
third coordinate is incremented. The second row's first coordinate is then
loaded with the power of two, followed by the third row's second coordinate.
All other basis and target words are the actual cells supplied by the same
layout. This module assembles only the existing native loading instructions;
source-value and full-state equations are proved in separate consumers.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth : Nat}

/-- The literal first-row sequence reads the actual decoded source cells under the work layout. -/
def firstCode (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width : Nat) :
    Circuit (BasisLayout.context ctx width) (BasisLayout.context ctx width) :=
  FirstRow.code (BasisLayout.underRead first width) (BasisLayout.underRead second width)
    (BasisLayout.firstRow ctx width)

/-- The original second-row load writes only its first actual coordinate. -/
def secondCode (ctx : RuntimeCtx kind) (width count : Nat) :
    Circuit (BasisLayout.context ctx width) (BasisLayout.context ctx width) :=
  PowerOfTwo.code count (BasisLayout.secondRow ctx width).first

/-- The original third-row load writes only its second actual coordinate. -/
def thirdCode (ctx : RuntimeCtx kind) (width count : Nat) :
    Circuit (BasisLayout.context ctx width) (BasisLayout.context ctx width) :=
  PowerOfTwo.code count (BasisLayout.thirdRow ctx width).second

/-- The original basis loading runs in first-row, second-row and third-row order. -/
def code (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat) :
    Circuit (BasisLayout.context ctx width) (BasisLayout.context ctx width) :=
  .seq (firstCode first second width)
    (.seq (secondCode ctx width count) (thirdCode ctx width count))

/-- The returned store follows exactly the same three actual loading sequences. -/
def storeStep (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (store : Store (BasisLayout.context ctx width)) : Store (BasisLayout.context ctx width) :=
  let firstResult := FirstRow.storeStep (BasisLayout.underRead first width)
    (BasisLayout.underRead second width) (BasisLayout.firstRow ctx width) store
  let secondResult := PowerOfTwo.storeStep count (BasisLayout.secondRow ctx width).first firstResult
  PowerOfTwo.storeStep count (BasisLayout.thirdRow ctx width).second secondResult

/-- Independent native accounting charges all three original loading sequences. -/
def nativeEnvelope (kind : ProblemKind) (sourceWidth width count : Nat) : ResourcePool kind :=
  FirstRow.nativeEnvelope kind sourceWidth width +
    (PowerOfTwo.nativeEnvelope kind width count + PowerOfTwo.nativeEnvelope kind width count)

/-- The same actual instructions have exactly the independent native multiplicities. -/
theorem nativeLattice_basis_initialization_pool
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (path : (code first second width count).Path) :
    (code first second width count).resourcePool path =
      nativeEnvelope kind sourceWidth width count := by
  have firstPool := FirstRow.nativeLattice_firstRow_pool
    (BasisLayout.underRead first width) (BasisLayout.underRead second width)
    (BasisLayout.firstRow ctx width) path.1
  have secondPool := PowerOfTwo.nativeLattice_powerOfTwo_pool count
    (BasisLayout.secondRow ctx width).first path.2.1
  have thirdPool := PowerOfTwo.nativeLattice_powerOfTwo_pool count
    (BasisLayout.thirdRow ctx width).second path.2.2
  exact congrArg₂ (fun first later : ResourcePool kind => first + later) firstPool
    (congrArg₂ (fun left right : ResourcePool kind => left + right) secondPool thirdPool)

/-- The real serial loading depth includes both resizes, three increments and every shift. -/
theorem nativeLattice_basis_initialization_depth
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (duration : Resource.Event kind → Nat) (path : (code first second width count).Path) :
    (code first second width count).depth duration path =
      (duration (.classicalOperation (.wordResize sourceWidth width)) +
        (duration (.classicalOperation (.wordResize sourceWidth width)) +
          duration (.classicalOperation (.wordUnary .increment width)))) +
      ((duration (.classicalOperation (.wordUnary .increment width)) +
          count * duration (.classicalOperation (.wordUnary .shiftLeft width))) +
        (duration (.classicalOperation (.wordUnary .increment width)) +
          count * duration (.classicalOperation (.wordUnary .shiftLeft width)))) := by
  have firstDepth := FirstRow.nativeLattice_firstRow_depth
    (BasisLayout.underRead first width) (BasisLayout.underRead second width)
    (BasisLayout.firstRow ctx width) duration path.1
  have secondDepth := PowerOfTwo.nativeLattice_powerOfTwo_depth count
    (BasisLayout.secondRow ctx width).first duration path.2.1
  have thirdDepth := PowerOfTwo.nativeLattice_powerOfTwo_depth count
    (BasisLayout.thirdRow ctx width).second duration path.2.2
  exact congrArg₂ Nat.add firstDepth (congrArg₂ Nat.add secondDepth thirdDepth)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization
