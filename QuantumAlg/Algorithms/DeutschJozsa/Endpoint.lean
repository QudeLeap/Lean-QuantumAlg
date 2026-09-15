/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.DeutschJozsa.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Algorithms.DeutschJozsa.Construction
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Algorithms.DeutschJozsa.Specification
import all QuantumAlg.Algorithms.DeutschJozsa.DistributionLaws
import all QuantumAlg.Primitives.WalshHadamard.Readout.Restoration
import all QuantumAlg.Primitives.WalshHadamard.Readout.Resources
import all QuantumAlg.Primitives.WalshHadamard.Readout.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves

/-!
# The complete native Deutsch-Jozsa endpoint

The sole executable circuit prepares the query and target, executes the
original oracle circuit, writes each query measurement to its own finite
classical cell, and packs the actual results. Complete Output retains every
live entry. The proof uses probabilities and paths from that same execution,
including preservation of its borrowed classical input and arbitrary
external-reference correlations.
-/

namespace QuantumAlg.DeutschJozsa

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The public input contract admits exactly the original constant-or-balanced promise. -/
public theorem problem_valid_iff {n : Nat} (f : WalshHadamard.Oracle n)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem f).valid state ↔ Promise f := Iff.rfl

/-- The actual result is accepted precisely when its all-zero test decides constancy. -/
public theorem problem_accepts_bits_iff {n : Nat} (f : WalshHadamard.Oracle n)
    (initial : Execution.Store pre) (outcome : Fin n → Bool) :
    (problem f).accepts initial (.bits outcome) ↔
      ((outcome = fun _ => false) ↔ IsConstant f) := by
  have zeroOutcome : allZeroOutcome n = (fun _ : Fin n => false) := by
    funext index
    exact Nat.zero_testBit (n - 1 - index.val)
  change ((outcome = allZeroOutcome n) ↔ IsConstant f) ↔ _
  rw [zeroOutcome]

/-- The actual internally prepared circuit, with n real Z writes and complete live Output. -/
public def algorithm {n : Nat} (f : WalshHadamard.Oracle n) :
    Algorithm .quantum pre (post n) (.bits n) where
  run := run f

/-- For every width, including zero, the native execution solves the original promise problem
with probability one and the independently stated complete resource bounds. -/
public theorem main {n : Nat} (f : WalshHadamard.Oracle n) :
    ∃ candidate : Algorithm .quantum pre (post n) (.bits n),
      Algorithm.Solves candidate (problem f) := by
  refine ⟨algorithm f, ?_⟩
  constructor
  · intro Reference input promised
    exact le_of_eq (actual_success f promised input).symm
  · intro _Reference _input _promised requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _promised
    exact code_borrowedRestored f
      (input.state.mapClassical (fun store => (store, store)))
  · intro _Reference _input _promised path _supported
    exact le_of_eq (code_events f path)
  · intro _Reference _input _promised path _supported
    exact code_residentSpace f path
  · intro _Reference _input _promised path _supported
    exact code_auxiliarySpace f path
  · intro _Reference _input _promised path _supported
    exact le_of_eq (code_depth f path)

end

end QuantumAlg.DeutschJozsa
