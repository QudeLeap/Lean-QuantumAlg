/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Operations
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Execution
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Semantics

/-!
# Complete execution of the actual quadratic candidate chain

The update records the existing native instructions and the actual paths of
both saturating subtractions and the square root. No mathematical candidate
function is substituted for execution. The full-state equation retains the
entire caller store, incoming history and quantum-reference blocks while those
real deterministic instructions materialize the two words.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The chronological stores and true paths of all seven actual candidate stages. -/
def candidatesStep (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidates input modulus refs).Path :=
  let widened := store.applyOp (widenOp input refs)
  let centered := widened.applyOp (centerOp refs)
  let squared := centered.applyOp (squareOp refs)
  let reduced := NativeSub.intoStep (.storage refs.root.toCStorageRef) modulus refs.root squared
  let rooted := NativeSqrt.intoStep (.storage refs.root.toCStorageRef) refs.root reduced.1
  let lower := NativeSub.intoStep (.storage refs.center.toCStorageRef)
    (.storage refs.root.toCStorageRef) refs.first rooted.1
  (lower.1.applyOp (secondOp refs), ((), ((), ((), (reduced.2, (rooted.2, (lower.2, ())))))))

/-- The actual candidate program preserves every complete incoming quantum-reference block. -/
theorem nativeQuadratic_candidates_execute (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (candidates input modulus refs).execute Reference state = state.mapClassical (fun entry =>
      ((candidatesStep input modulus refs entry.1).1,
        (entry.2, (candidatesStep input modulus refs entry.1).2))) := by
  simp only [candidates, discriminant, squareRoot, firstCandidate,
    Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    NativeSub.nativeSub_into_execute, NativeSqrt.nativeSqrt_into_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact congrArg
    (fun equality : DecidableEq (Store ctx ×
        (History × (candidates input modulus refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry => ((candidatesStep input modulus refs entry.1).1,
          (entry.2, (candidatesStep input modulus refs entry.1).2))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
