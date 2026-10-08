/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Accumulate

/-!
# Two-word modular accumulation contract

The unchanged source selects a modular offset of the target. Both words
belong to the original input carrier [VBE95, 9511018.tex:333-367].
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

/-- The original source word and modular accumulator. -/
abbrev Registers (width : Nat) := Fin (2 ^ width) × Fin (2 ^ width)

/-- Complete binary encoding of the original two words. -/
def encoding (width : Nat) : BinaryLabelEncoding (Registers width) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
    (BinaryLabelEncoding.finIdentity width)

/-- The unchanged source selects an exact modular offset of the target. -/
def selectedOutput {width : Nat} (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width) : Registers width :=
  (state.1, if state.1.val.testBit selected.val then
    Nat.FixedWidth.modularWordOutput modulus constant state.2 else state.2)

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
