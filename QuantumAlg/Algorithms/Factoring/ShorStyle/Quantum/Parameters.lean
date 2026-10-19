/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word

/-!
# Actual modular-power parameters for native Shor members

The complete sampler parameter remains unchanged. Its unit word selects the
compiled modular-power circuit; the early-factor fields remain available for
the original recovery shortcut. Selection is total on every encoded value,
and the actual sampler's canonical unit always selects itself. No extra
coprimality condition is imposed on the algorithm's input.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

/-- The original phase and power words share one additional multiplication word. -/
def totalQubits (N : Nat) : Nat := phaseBits N + (modulusBits N + modulusBits N)

/-- The original public modulus has the lossless bound required by the compiled multiplier. -/
def modulus (N : Nat) : Fin (2 ^ modulusBits N + 1) :=
  ⟨N, Nat.lt_succ_of_le (Nat.le_pow_clog (by norm_num : 1 < 2) N)⟩

/-- Total member selection; the source sampler's unit is always in the first branch. -/
def selectedUnit {N : Nat} (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (ZMod N)ˣ :=
  if coprime : Nat.Coprime parameter.first.toNat N then
    ZMod.unitOfCoprime parameter.first.toNat coprime
  else 1

/-- Reading the source sampler's canonical unit selects that same mathematical unit. -/
lemma selectedUnit_parameterValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    selectedUnit (parameterValue input sample) =
      (RSA.prepareResidueFromBits N (modulusBits N) residueProposalCount sample).unit := by
  let : NeZero N := input.neZero
  unfold selectedUnit
  rw [parameterValue_unit_toNat]
  rw [dif_pos (ZMod.val_coe_unit_coprime
    (RSA.prepareResidueFromBits N (modulusBits N) residueProposalCount sample).unit)]
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime]
  exact ZMod.natCast_zmod_val _

/-- The native bank is four modulus-width words under the unchanged phase-width convention. -/
lemma totalQubits_eq_four_mul (N : Nat) : totalQubits N = 4 * modulusBits N := by
  unfold totalQubits phaseBits
  omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
