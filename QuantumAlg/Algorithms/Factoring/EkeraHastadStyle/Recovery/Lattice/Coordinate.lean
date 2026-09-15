/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

/-!
# Actual native lattice coordinate reduction

The original lattice update target minus coefficient times source is two
existing word instructions: low-word multiplication into a fresh lexical
word, then wrapping subtraction into the original target. Both multiplicands
are read before the target changes, so either may alias it. The temporary
word is supplied and released by the circuit itself. This is the literal
coordinate operation used by row reduction and nearest-plane subtraction.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- One actual lexical product word, with the original quantum bank unchanged. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The real new word holding the low product before the original target is written. -/
def product (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) :=
  .workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Original structural reads keep their positions below the single actual product word. -/
def underRead {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (context ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The multiplication reads both original operands before any original write occurs. -/
def multiplyOp (coefficient source : CInputRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) (.unsignedWord width)
      (context ctx width) (context ctx width) :=
  .wordBinary .mulLow width (context ctx width)
    (.product (underRead coefficient width) (underRead source width)) (product ctx width)

/-- The original target receives its wrapping difference from the real stored product. -/
def subtractOp (target : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) (.unsignedWord width)
      (context ctx width) (context ctx width) :=
  .wordBinary .sub width (context ctx width)
    (.product (underRead (.storage target.toCStorageRef) width)
      (.storage (product ctx width).toCStorageRef))
    (target.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)

/-- The two actual native instructions follow the original lattice arithmetic order. -/
def body (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) :
    Circuit (context ctx width) (context ctx width) :=
  .seq (.classical (multiplyOp coefficient source)) (.classical (subtractOp target))

/-- Actual coordinate reduction owns and releases its only temporary classical word. -/
def code (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (body coefficient source target)

/-- The actual two writes before lexical release, independent of the initial product word. -/
def bodyStore (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx width)) :
    Store (context ctx width) :=
  (store.applyOp (multiplyOp coefficient source)).applyOp (subtractOp target)

/-- Exact store update of real allocation, both instructions and the matching release. -/
def storeStep (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (bodyStore coefficient source target
      (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh))

/-- Independent native coordinate allowance for one multiplication and one subtraction. -/
def nativeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordBinary .mulLow width)) +
    ResourcePool.singleton (.classicalOperation (.wordBinary .sub width))

/-- Actual allocation and release add no instructions to the two original arithmetic operations. -/
theorem nativeLattice_coordinate_pool (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (path : (code coefficient source target).Path) :
    (code coefficient source target).resourcePool path = nativeEnvelope kind width := rfl

/-- The actual serial dependency charges exactly both native durations. -/
theorem nativeLattice_coordinate_depth (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (code coefficient source target).Path) :
    (code coefficient source target).depth duration path =
      duration (.classicalOperation (.wordBinary .mulLow width)) +
        duration (.classicalOperation (.wordBinary .sub width)) := rfl

/-- No operation in this actual scoped coordinate update changes the borrowed joint interface. -/
theorem nativeLattice_coordinate_borrowedRestored
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code coefficient source target).BorrowedRestored Reference state
      ((code coefficient source target).execute Reference state) :=
  Circuit.borrowedRestored_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (body coefficient source target) Reference
    (fun {_} _ current => Circuit.borrowedRestored_seq
      (.classical (multiplyOp coefficient source)) (.classical (subtractOp target)) current
      (Circuit.borrowedRestored_classical (multiplyOp coefficient source) current)
      (Circuit.borrowedRestored_classical (subtractOp target) _)) state

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate
