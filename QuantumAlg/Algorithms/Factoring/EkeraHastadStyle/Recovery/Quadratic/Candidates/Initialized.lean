/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Arithmetic
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Constants

/-!
# Actual candidates (model := model) followed by initialization of the reused center word

Both source candidates (model := model) are fully materialized before the actual old center
word is cleared and incremented. The resulting one cell is therefore loaded
by real native instructions, and both candidate words retain their exact
source values. Even a zero-width logarithm has the actual positive candidate
width prescribed by the original bounds.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Initialized

open Execution

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual candidate generation precedes the two native instructions loading the one word. -/
def code (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) : Circuit model ctx ctx :=
  .seq (candidates (model := model) input modulus refs) (CheckConstants.code (model := model)
    refs.center)

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual candidate path is retained before both real initialization instructions. -/
def step (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) (store : Store ctx) :
    Store ctx × (code (model := model) input modulus refs).Path :=
  let materialized := candidatesStep (model := model) input modulus refs store
  let initialized := CheckConstants.step (model := model) refs.center materialized.1
  (initialized.1, (materialized.2, initialized.2))

/-- The composed actual program preserves every complete incoming quantum-reference block. -/
lemma nativeQuadratic_initialized_execute (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) input modulus refs).execute environment
      Reference state = state.mapClassical (fun
      entry =>
      ((step (model := model) input modulus refs entry.1).1, (entry.2.1, (entry.2.2, (step (model
        := model) input modulus refs entry.1).2)))) := by
  simp only [code, Circuit.execute_seq, nativeQuadratic_candidates_execute,
    CheckConstants.nativeQuadratic_check_one_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Initialization preserves both original source candidates and actually loads one. -/
lemma nativeQuadratic_initialized_values (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) (separated : Separated modulus refs) (store : Store ctx) :
    let final := (step (model := model) input modulus refs store).1
    ((final.read (.storage refs.first.toCStorageRef)).toNat,
        (final.read (.storage refs.second.toCStorageRef)).toNat) =
        RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat ∧
      (final.read (.storage refs.center.toCStorageRef)).toNat = 1 := by
  let materialized := (candidatesStep (model := model) input modulus refs store).1
  have firstPreserved := congrArg CShape.Value.toNat
    (CheckConstants.nativeQuadratic_check_one_read_other refs.center
      (.storage refs.first.toCStorageRef)
      (fun present => separated.centerFirst (List.mem_singleton.mp present)) materialized)
  have secondPreserved := congrArg CShape.Value.toNat
    (CheckConstants.nativeQuadratic_check_one_read_other refs.center
      (.storage refs.second.toCStorageRef)
      (fun present => separated.centerSecond (List.mem_singleton.mp present)) materialized)
  have oneFits : 1 < 2 ^ RSA.quadraticWordWidth width :=
    RSA.quadraticCenter_lt_wordCapacity (width := width) (logarithm := 0) (Nat.two_pow_pos width)
  refine ⟨(congrArg₂ Prod.mk firstPreserved secondPreserved).trans
    (nativeQuadratic_candidates_read input modulus refs separated store), ?_⟩
  exact (CheckConstants.nativeQuadratic_check_one_read refs.center materialized).trans
    (Nat.mod_eq_of_lt oneFits)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Initialized
