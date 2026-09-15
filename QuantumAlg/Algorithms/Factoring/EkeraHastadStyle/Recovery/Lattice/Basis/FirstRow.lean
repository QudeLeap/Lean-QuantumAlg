/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration
import all QuantumAlg.Core.Execution.Trace

/-!
# The original three native first-basis-row instructions

The first and second decoded j words are resized into the first two actual
basis cells. One actual increment follows in the third cell. The execution
law allows every incoming value in that cell. Connecting this sequence to
the source row (j1, j2, 1) uses the zero value established by actual fresh
basis allocation. No new constant opcode or separate execution layer is used.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.FirstRow

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- The three actual writable coordinates of the original first basis row. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  first : CWriteRef ctx (.unsignedWord width)
  second : CWriteRef ctx (.unsignedWord width)
  third : CWriteRef ctx (.unsignedWord width)

/-- The literal resizing instruction reads one decoded j from its actual structural reference. -/
def resizeOp (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord sourceWidth) (.unsignedWord width) ctx ctx :=
  .wordResize sourceWidth width ctx input output

/-- The original final instruction increments the actual third basis coordinate. -/
def oneOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (.storage refs.third.toCStorageRef) refs.third

/-- The same original three instructions run in their actual chronological order. -/
def code (first second : CInputRef ctx (.unsignedWord sourceWidth))
    (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (resizeOp first refs.first))
    (.seq (.classical (resizeOp second refs.second)) (.classical (oneOp refs)))

/-- The returned store is exactly the three native instruction updates, with no input premise. -/
def storeStep (first second : CInputRef ctx (.unsignedWord sourceWidth))
    (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (resizeOp first refs.first)).applyOp (resizeOp second refs.second)).applyOp
    (oneOp refs)

/-- Independent literal accounting for two real resizes and the following real increment. -/
def nativeEnvelope (kind : ProblemKind) (sourceWidth width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordResize sourceWidth width)) +
    (ResourcePool.singleton (.classicalOperation (.wordResize sourceWidth width)) +
      ResourcePool.singleton (.classicalOperation (.wordUnary .increment width)))

/-- The actual three-operation path has exactly the independent native multiplicities. -/
theorem nativeLattice_firstRow_pool (first second : CInputRef ctx (.unsignedWord sourceWidth))
    (refs : Refs ctx width) (path : (code first second refs).Path) :
    (code first second refs).resourcePool path = nativeEnvelope kind sourceWidth width := rfl

/-- The actual dependency chain charges both resizing operations before the increment. -/
theorem nativeLattice_firstRow_depth (first second : CInputRef ctx (.unsignedWord sourceWidth))
    (refs : Refs ctx width) (duration : Resource.Event kind → Nat)
    (path : (code first second refs).Path) :
    (code first second refs).depth duration path =
      duration (.classicalOperation (.wordResize sourceWidth width)) +
        (duration (.classicalOperation (.wordResize sourceWidth width)) +
          duration (.classicalOperation (.wordUnary .increment width))) := rfl

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Every actual store-keyed quantum-reference block follows the same three recorded operations. -/
theorem nativeLattice_firstRow_execute (first second : CInputRef ctx (.unsignedWord sourceWidth))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code first second refs).execute Reference state =
      state.mapClassical (fun entry => (storeStep first second refs entry.1,
        (entry.2, ((), ((), ()))))) := by
  simp only [code, Circuit.execute_seq, Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  dsimp only [storeStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code first second refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code first second refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

/-- The same three real classical operations restore every complete borrowed interface. -/
theorem nativeLattice_firstRow_borrowedRestored
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code first second refs).BorrowedRestored Reference state
      ((code first second refs).execute Reference state) :=
  Circuit.borrowedRestored_seq (.classical (resizeOp first refs.first))
    (.seq (.classical (resizeOp second refs.second)) (.classical (oneOp refs))) state
    (Circuit.borrowedRestored_classical (resizeOp first refs.first) state)
    (Circuit.borrowedRestored_seq (.classical (resizeOp second refs.second))
      (.classical (oneOp refs)) _
      (Circuit.borrowedRestored_classical (resizeOp second refs.second) _)
      (Circuit.borrowedRestored_classical (oneOp refs) _))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.FirstRow
