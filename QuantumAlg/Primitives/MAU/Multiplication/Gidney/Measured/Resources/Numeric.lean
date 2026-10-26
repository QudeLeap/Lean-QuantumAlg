/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Tactic.NormNum

/-!
# Closed RSA-2048 specialization of the independently derived multiplier limits

The generic actual multiplier establishes the native `28n²-45n` bound and
the explicit complete physical frame establishes `2n+4` resident qubits.
The following arithmetic evaluates those formulas and the twenty-by-four
sampling main term; it does not assert completed outer-algorithm integration
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured

/-- The generic actual native multiplier limit at width 2048. -/
lemma rsa2048_multiplier_toffoli_limit : 28 * 2048 ^ 2 - 45 * 2048 = (117348352 : Nat) := by
  norm_num

/-- The twenty-by-four member count times the specified 2051-multiplier main term. -/
lemma rsa2048_eighty_members_toffoli_main :
    80 * 2051 * (28 * 2048 ^ 2 - 45 * 2048) = (19254517596160 : Nat) := by
  norm_num

/-- The complete physical multiplier frame at the RSA-2048 width. -/
lemma rsa2048_multiplier_qubit_limit : 2 * 2048 + 4 = (4100 : Nat) := by
  norm_num

end QuantumAlg.MAU.Multiplication.Gidney.Measured
