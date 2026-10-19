/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout

/-!
# Compiled register parameters for Ekerå--Håstad factoring

The compiled arithmetic registers use the independent public source widths.
Their measured dimensions agree exactly with the classical recovery input width.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical

noncomputable section

/-- Actual short-DLP register parameters derived only from `N`. The two
exponent registers reuse the same power and zero auxiliary words. -/
@[implicit_reducible]
def registerParameters (N : Nat) : ShortDLP.RegisterParameters :=
  ShortDLP.CompiledMAU.registerParameters
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)

/-- The compiled terminal registers contain exactly the source-prescribed measured bits. -/
lemma measurementBits_compiledRegisters (N : Nat) :
    measurementBits N =
      ShortDLP.firstBits (registerParameters N) + (registerParameters N).ell := by
  rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
