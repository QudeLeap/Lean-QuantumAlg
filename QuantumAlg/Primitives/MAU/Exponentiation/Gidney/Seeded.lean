/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Program
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word

/-!
# Full selected-power execution from any canonical unit seed

The actual exponentiation program multiplies any canonical seed unit by the
selected power, returning its shared auxiliary word to zero. This permits
two independent exponent registers to act successively on the same unit
workspace without adding an XOR-copy word [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open QuantumAlg.Nat.FixedWidth.UnitExponentiation Nat.FixedWidth

/-- The complete actual schedule multiplies every canonical seed and returns the same auxiliary. -/
theorem gidneyExponent_seeded (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base seed : (ZMod modulus.val)ˣ)
    (exponent : Fin (2 ^ exponentWidth)) :
    (program exponentWidth width modulus base).applyNormalized
        (NormalizedVector.ket ((encoding exponentWidth width).encode
          (exponent, unitResidueWord modulus positive seed, 0))) =
      NormalizedVector.ket ((encoding exponentWidth width).encode
        (exponent, unitResidueWord modulus positive (base ^ exponent.val * seed), 0)) := by
  have actual := gidneyExponentBits_unit_word exponentWidth width modulus positive base
    (List.ofFn fun bit => bit) exponent seed
  rw [scheduledUnit_all_eq_pow] at actual
  exact UnitaryCircuit.applyNormalized_seq_of_eq actual
    (UnitaryCircuit.applyNormalized_identity (Qubits (encoding exponentWidth width).width)
      (List.range (exponentWidth + 2 * width)) List.nodup_range _)

end

end QuantumAlg.MAU.Exponentiation.Gidney
