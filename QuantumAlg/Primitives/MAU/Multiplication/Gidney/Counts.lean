/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Counts

/-!
# Native single-qubit count of reversible multiplication

Selected accumulation and its inverse contain no X gates. The intervening
word exchange consists of CNOT gates, so the complete multiplier has no X gates.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open EncodedBit.GateSpec

private lemma wordSwapGates_xMultiplicity_sum (width : Nat) :
    ((wordSwapGates width).map xMultiplicity).sum = 0 := by
  have total := length_eq_multiplicity_sums (wordSwapGates width)
  have cnots : ((wordSwapGates width).map cnotMultiplicity).sum = 3 * width :=
    EncodedBit.Word.swapGates_cnotMultiplicity_sum _ _ _
  rw [gidneyWordSwap_gate_count, cnots] at total
  omega

/-- Every emitted multiplier instruction is a CNOT or Toffoli, including small widths. -/
lemma gidneyUnitMultiplicationGates_xMultiplicity_sum (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    ((gates width modulus coefficient).map xMultiplicity).sum = 0 := by
  simp only [gates, List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
    Accumulate.Gidney.gidneyAccumulateGates_xMultiplicity_sum,
    wordSwapGates_xMultiplicity_sum, Nat.zero_add]

end

end QuantumAlg.MAU.Multiplication.Gidney
