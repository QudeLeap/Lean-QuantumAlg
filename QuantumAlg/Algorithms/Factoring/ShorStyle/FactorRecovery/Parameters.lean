/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Util.Classical.OrderRecovery

/-!
# Intrinsic modulus and order-recovery specifications for Shor factoring

Both descriptors depend only on the original public input and its declared
register widths. Their arithmetic consumers need no quantum execution imports.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery

/-- The fixed modulus descriptor consumed by the order, powering, and GCD
seams.  It is built from the public executable input alone. -/
def modulusSpec {N : Nat} (input : Input N) :
    ClassicalAlgorithms.Modular.ModulusSpec (modulusBits N) where
  modulus := N
  two_le := input.modulus_ge_two
  le_capacity := input.register_fits

/-- The original intrinsic order-recovery specification for this source modulus and phase width. -/
def recoverySpec {N : Nat} (input : Input N) :
    ClassicalAlgorithms.OrderRecovery.Spec (modulusBits N) (phaseBits N) :=
  ⟨modulusSpec input⟩

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery
