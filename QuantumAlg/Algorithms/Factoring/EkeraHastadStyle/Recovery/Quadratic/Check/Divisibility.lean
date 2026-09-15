/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual divisibility completion of a quadratic candidate check

After the actual range comparison, three native instructions compute the
modulus remainder, compare it with the actual zero word, and conjoin that
stored result with the stored range predicate. All instructions execute even
for candidate zero; native natural remainder already defines that case.
No Boolean predicate callback or independent arithmetic oracle is introduced.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Divisibility

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual source words and writable cells used to complete one stored range decision. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The same original modulus as the preceding range comparison. -/
  modulus : CInputRef ctx (.unsignedWord width)
  /-- The same candidate word, including candidate zero. -/
  candidate : CInputRef ctx (.unsignedWord width)
  /-- A real word whose value is established by its enclosing allocation. -/
  zero : CInputRef ctx (.unsignedWord width)
  /-- Actual remainder workspace. -/
  remainder : CWriteRef ctx (.unsignedWord width)
  /-- Actual equality result used by the final conjunction. -/
  divides : CWriteRef ctx .bit
  /-- Actual range result, overwritten with the complete validity predicate. -/
  valid : CWriteRef ctx .bit

/-- Actual unsigned remainder of the two stored source operands. -/
def remainderOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .remainder width ctx (.product refs.modulus refs.candidate) refs.remainder

/-- Actual equality reads the computed remainder and the real zero-word reference. -/
def equalityOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product (.storage refs.remainder.toCStorageRef) refs.zero) refs.divides

/-- Actual conjunction combines the stored range decision with the stored remainder decision. -/
def combineOp (refs : Refs ctx width) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (.storage refs.valid.toCStorageRef)
    (.storage refs.divides.toCStorageRef)) refs.valid

/-- Complete actual divisibility work, without short-circuiting either arithmetic instruction. -/
def code (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (remainderOp refs))
    (.seq (.classical (equalityOp refs)) (.classical (combineOp refs)))

/-- The complete actual store after the three native writes. -/
def storeStep (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (remainderOp refs)).applyOp (equalityOp refs)).applyOp (combineOp refs)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The three actual instructions preserve all complete incoming quantum-reference blocks. -/
theorem nativeQuadratic_divisibility_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code refs).execute Reference state = state.mapClassical (fun entry =>
      (storeStep refs entry.1, (entry.2, ((), ((), ()))))) := by
  simp only [code, Circuit.execute_seq, Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (code refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry => (storeStep refs entry.1, (entry.2, ((), ((), ()))))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Divisibility
