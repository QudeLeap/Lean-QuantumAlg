/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.DeutschJozsa.Endpoint
import all QuantumAlg.Algorithms.DeutschJozsa.Endpoint
import all QuantumAlg.Algorithms.DeutschJozsa.Endpoint.Execution

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
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

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
public lemma problem_valid_iff {n : Nat} (f : WalshHadamard.Oracle n)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem n).valid (environment f) f state ↔ Promise f :=
  and_iff_right rfl

/-- The actual result is accepted precisely when its all-zero test decides constancy. -/
public lemma problem_accepts_bits_iff {n : Nat} (f : WalshHadamard.Oracle n)
    (initial : Execution.Store pre) (outcome : Fin n → Bool) :
    (problem n).accepts (environment f) f initial (.bits outcome) ↔
      ((outcome = fun _ => false) ↔ IsConstant f) := by
  have zeroOutcome : allZeroOutcome n = (fun _ : Fin n => false) := by
    funext index
    exact Nat.zero_testBit (n - 1 - index.val)
  change ((outcome = allZeroOutcome n) ↔ IsConstant f) ↔ _
  rw [zeroOutcome]

end

end QuantumAlg.DeutschJozsa
