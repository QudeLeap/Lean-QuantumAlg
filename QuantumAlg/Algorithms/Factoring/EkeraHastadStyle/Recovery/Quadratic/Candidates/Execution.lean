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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The chronological stores and true paths of all seven actual candidate stages. -/
def candidatesStep (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidates (model := model) input modulus refs).Path :=
  let widened := BitWord.instructionStep (execution := model) (widenOp input refs) store
  let centered := BitWord.instructionStep (execution := model) (centerOp refs) widened.1
  let squared := BitWord.instructionStep (execution := model) (squareOp refs) centered.1
  let reduced := NativeSub.intoStep (model := model)
    (.storage refs.root.toCStorageRef) modulus refs.root squared.1
  let rooted := NativeSqrt.intoStep (model := model)
    (.storage refs.root.toCStorageRef) refs.root reduced.1
  let lower := NativeSub.intoStep (model := model) (.storage refs.center.toCStorageRef)
    (.storage refs.root.toCStorageRef) refs.first rooted.1
  let upper := BitWord.instructionStep (execution := model) (secondOp refs) lower.1
  (upper.1, (widened.2, (centered.2, (squared.2, (reduced.2, (rooted.2, (lower.2, upper.2)))))))

/-- The actual candidate program preserves every complete incoming quantum-reference block. -/
theorem nativeQuadratic_candidates_execute (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidates (model := model) input modulus refs).execute Reference state = state.mapClassical
      (fun entry =>
      ((candidatesStep (model := model) input modulus refs entry.1).1,
        (entry.2.1, (entry.2.2, (candidatesStep (model := model) input modulus refs entry.1).2))))
          := by
  simp only [candidates, discriminant, squareRoot, firstCandidate,
    Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    NativeSub.nativeSub_into_execute, NativeSqrt.nativeSqrt_into_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
