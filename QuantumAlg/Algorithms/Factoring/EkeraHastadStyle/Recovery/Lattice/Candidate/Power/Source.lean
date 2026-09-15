/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters

/-!
# Candidate-power source-predicate bridge

The candidate-power machine compares canonical natural representatives of a
modular power and target.  This module identifies that comparison with the
source short-logarithm predicate on units.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeCandidatePowerBridge

noncomputable section

/-- The candidate machine's natural modular-power comparison is exactly the
source predicate for the RSA target unit. -/
theorem candidatePowerMatches_targetUnit_iff {N : Nat} (input : Input N)
    (generator : (ZMod N)ˣ) (exponent : Nat) :
    ((generator : ZMod N).val ^ exponent) % N =
        (RSA.targetUnit generator : ZMod N).val ↔
      generator ^ exponent = RSA.targetUnit generator := by
  let _ : NeZero N := input.neZero
  constructor
  · intro hmod
    have hcast :
        (((generator : ZMod N).val ^ exponent : Nat) : ZMod N) =
          (((RSA.targetUnit generator : ZMod N).val : Nat) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff' _ _ N).mpr (by
        simpa only [Nat.mod_eq_of_lt
          (ZMod.val_lt (RSA.targetUnit generator : ZMod N))] using hmod)
    rw [Units.ext_iff, Units.val_pow_eq_pow_val]
    simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hcast
  · intro hpower
    have hvalue :
        (generator : ZMod N) ^ exponent =
          (RSA.targetUnit generator : ZMod N) := by
      simpa only [Units.ext_iff, Units.val_pow_eq_pow_val] using hpower
    have hcast :
        (((generator : ZMod N).val ^ exponent : Nat) : ZMod N) =
          (((RSA.targetUnit generator : ZMod N).val : Nat) : ZMod N) := by
      simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hvalue
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ N).mp hcast
    simpa only [Nat.mod_eq_of_lt (ZMod.val_lt (RSA.targetUnit generator : ZMod N))]
      using hmod

/-- The fixed target exponent computes the canonical target-unit value. -/
theorem targetUnit_val_eq_modularPower {N : Nat} (input : Input N)
    (generator : (ZMod N)ˣ) :
    ((generator : ZMod N).val ^ RSA.targetExponent N) % N =
      (RSA.targetUnit generator : ZMod N).val := by
  exact (candidatePowerMatches_targetUnit_iff input generator
    (RSA.targetExponent N)).2 rfl

end

end LatticeCandidatePowerBridge
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
