/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.PowerAction
import all QuantumAlg.Algorithms.OrderFinding.Oracle

/-!
# Compiled unit words and the unchanged source modular powers

The actual MAU output is the canonical finite-word representative of the
selected modular unit power. Its value agrees with the original source
oracle applied to a zero target. For a parameter produced by the real source
sampler, the selected base is exactly its stored unsigned word. These are
arithmetic equalities; no oracle call is inserted into the native execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

open Nat.FixedWidth

/-- Original source access for the unit selected by the actual stored parameter. -/
theorem sourceAccess {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    OrderFinding.ModExpOracleAccess N ((selectedUnit parameter : ZMod N).val)
      (phaseBits N) (modulusBits N) := {
  modulus_pos := input.modulus_pos
  register_fits := input.register_fits }

/-- The actual canonical power word equals the original zero-target source oracle value. -/
theorem power_word_eq_target {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (exponent : Fin (2 ^ phaseBits N)) :
    unitResidueWord (modulus N) input.modulus_pos (selectedUnit parameter ^ exponent.val) =
      OrderFinding.modExpOracleTarget (sourceAccess input parameter) exponent 0 := by
  let : NeZero N := input.neZero
  have powerValue :
      ((((selectedUnit parameter : ZMod N).val ^ exponent.val : Nat) : ZMod N)) =
        ((selectedUnit parameter ^ exponent.val : (ZMod N)ˣ) : ZMod N) := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val, Units.val_pow_eq_pow_val]
  have numeric := congrArg (fun value : ZMod N => value.val) powerValue
  rw [ZMod.val_natCast] at numeric
  apply Fin.ext
  change ((selectedUnit parameter ^ exponent.val : (ZMod N)ˣ) : ZMod N).val =
    Nat.xor 0 ((selectedUnit parameter : ZMod N).val ^ exponent.val % N)
  exact numeric.symm.trans (Nat.zero_xor _).symm

/-- The source sampler's real stored unit word is precisely the native member's selected base. -/
theorem selectedBase_parameterValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    ((selectedUnit (parameterValue input sample) : ZMod N).val) =
      (parameterValue input sample).first.toNat := by
  rw [selectedUnit_parameterValue input, parameterValue_unit_toNat]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
