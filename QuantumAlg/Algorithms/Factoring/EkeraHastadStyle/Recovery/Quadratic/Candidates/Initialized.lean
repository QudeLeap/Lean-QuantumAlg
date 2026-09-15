/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Arithmetic
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Constants

/-!
# Actual candidates followed by initialization of the reused center word

Both source candidates are fully materialized before the actual old center
word is cleared and incremented. The resulting one cell is therefore loaded
by real native instructions, and both candidate words retain their exact
source values. Even a zero-width logarithm has the actual positive candidate
width prescribed by the original bounds.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Initialized

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual candidate generation precedes the two native instructions loading the one word. -/
def code (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) : Circuit ctx ctx :=
  .seq (candidates input modulus refs) (CheckConstants.code refs.center)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual candidate path is retained before both real initialization instructions. -/
def step (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) (store : Store ctx) :
    Store ctx × (code input modulus refs).Path :=
  let materialized := candidatesStep input modulus refs store
  (CheckConstants.storeStep refs.center materialized.1, (materialized.2, ((), ())))

/-- The composed actual program preserves every complete incoming quantum-reference block. -/
theorem nativeQuadratic_initialized_execute (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code input modulus refs).execute Reference state = state.mapClassical (fun entry =>
      ((step input modulus refs entry.1).1, (entry.2, (step input modulus refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (candidates input modulus refs)
    (CheckConstants.code refs.center) (candidatesStep input modulus refs)
    (fun store => (CheckConstants.storeStep refs.center store, ((), ())))
    (fun reference {_} _ initial => by
      refine (nativeQuadratic_candidates_execute input modulus refs reference initial).trans ?_
      congr 1)
    (fun reference {_} _ initial => by
      refine (CheckConstants.nativeQuadratic_check_one_execute
        refs.center reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (code input modulus refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry => ((step input modulus refs entry.1).1,
          (entry.2, (step input modulus refs entry.1).2))))
    (Subsingleton.elim _ _)

end

/-- Initialization preserves both original source candidates and actually loads one. -/
theorem nativeQuadratic_initialized_values (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Quadratic.Refs ctx width) (separated : Separated modulus refs) (store : Store ctx) :
    let final := (step input modulus refs store).1
    ((final.read (.storage refs.first.toCStorageRef)).toNat,
        (final.read (.storage refs.second.toCStorageRef)).toNat) =
        RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat ∧
      (final.read (.storage refs.center.toCStorageRef)).toNat = 1 := by
  let materialized := (candidatesStep input modulus refs store).1
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

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Initialized
