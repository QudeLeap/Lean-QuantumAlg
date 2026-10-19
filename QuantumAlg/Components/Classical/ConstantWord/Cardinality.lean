/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Trace

/-!
# Cardinality of actual constant-word loading

Each supplied bit emits its real shift and at most one selected increment.
The bound counts the existing trace and allows every public constant.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord

variable (model : ExecutionModel) [BitWord.Selected model] (width : Nat)

/-- The actual bit loader emits at most two instructions per supplied bit. -/
lemma loaderTrace_length_le (bits : List Bool) :
    (loaderTrace model width bits).length ≤ 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit remaining ih =>
    cases bit <;> simp only [loaderTrace, List.flatMap_cons, Bool.false_eq_true,
      if_false, List.append_nil, List.length_append, List.length_cons, List.length_nil,
      if_true] at * <;> omega

/-- The existing public constant representation supplies exactly the declared number of bits. -/
lemma constantLoader_length_le (value : Nat) :
    (loaderTrace model width (List.ofFn (constantBits width value))).length ≤ 2 * width := by
  simpa only [List.length_ofFn] using
    loaderTrace_length_le model width (List.ofFn (constantBits width value))

end QuantumAlg.ClassicalRoutines.ConstantWord
