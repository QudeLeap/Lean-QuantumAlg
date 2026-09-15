/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Keys
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Guard.Correctness

/-!
# The complete real scope discharges the native order-guard separation

Each condition is an identity of two positions in the actual seven-head
context, certified by its real key uniqueness. The source caller supplies
no workspace or read-disjointness certificate.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

variable {kind : ProblemKind}

/-- The actual seven allocated cells satisfy every guard read/write condition. -/
theorem guard_separated (ctx : RuntimeCtx kind) (N : Nat) :
    NativeFactorTail.GuardSeparation (cells ctx N) where
  zeroExpanded := scratchKeys_ne ctx N 3 4 (by decide)
  activeExpanded := scratchKeys_ne ctx N 2 4 (by decide)
  positiveExpanded := scratchKeys_ne ctx N 1 4 (by decide)
  activeZero := scratchKeys_ne ctx N 2 3 (by decide)
  positiveActive := scratchKeys_ne ctx N 1 2 (by decide)

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
