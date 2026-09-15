/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Keys
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Correctness

/-!
# The genuine half-factor scope discharges every internal separation condition

The six actual context entries establish all distinctness conditions used
by the GCD, comparisons and final pack. Every original half-power reference
remains in the old frame. No caller supplies a separation certificate.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem stable_separate
    (input : CInputRef ctx (.unsignedWord (modulusBits N))) (key : StorageKey)
    (scratch : key ∈ scratchKeys ctx N)
    (oneDifferent : key ≠ (oneRef ctx N).key)
    (modulusDifferent : key ≠ (modulusRef ctx N).key) :
    key ∉ (NativeHalfFactor.stableOperands (liftInput input) (cells ctx N)).storageKeys := by
  intro present
  rcases List.mem_append.mp present with half | constants
  · exact scratchKeys_input_separate input key scratch half
  · rcases List.mem_append.mp constants with one | modulus
    · exact oneDifferent (List.mem_singleton.mp one)
    · exact modulusDifferent (List.mem_singleton.mp modulus)

/-- The actual six fresh cells establish every separation condition of the real factor code. -/
theorem cells_separated (ctx : RuntimeCtx kind) (N : Nat)
    (input : CInputRef ctx (.unsignedWord (modulusBits N))) :
    NativeHalfFactor.Separation (liftInput input) (cells ctx N) := by
  constructor
  · exact stable_separate input (candidateRef ctx N).key
      (List.get_mem (scratchKeys ctx N) (5 : Fin 6))
      (scratchKeys_ne ctx N 5 4 (by decide)) (scratchKeys_ne ctx N 5 3 (by decide))
  · exact stable_separate input (lowerRef ctx N).key
      (List.get_mem (scratchKeys ctx N) (2 : Fin 6))
      (scratchKeys_ne ctx N 2 4 (by decide)) (scratchKeys_ne ctx N 2 3 (by decide))
  · exact stable_separate input (upperRef ctx N).key
      (List.get_mem (scratchKeys ctx N) (1 : Fin 6))
      (scratchKeys_ne ctx N 1 4 (by decide)) (scratchKeys_ne ctx N 1 3 (by decide))
  · exact scratchKeys_ne ctx N 2 5 (by decide)
  · exact scratchKeys_ne ctx N 1 5 (by decide)
  · exact scratchKeys_ne ctx N 1 2 (by decide)
  · exact scratchKeys_ne ctx N 0 2 (by decide)

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
