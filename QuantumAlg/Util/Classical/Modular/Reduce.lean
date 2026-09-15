/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.ModEq
import all QuantumAlg.Util.Classical.Arithmetic
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Canonical modular reduction

Reduction accepts an arbitrary fixed-width source word and returns the intrinsic
canonical representative for one `ModulusSpec`.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace Modular
namespace Reduce

/-- An arbitrary fixed-width numerator to reduce. -/
abbrev Input (sourceWidth : Nat) := Word sourceWidth

/-- Every word is a valid reduction input for a proved modulus. -/
@[nolint unusedArguments]
def valid {width sourceWidth : Nat} (_spec : ModulusSpec width)
    (_input : Input sourceWidth) : Prop :=
  True

/-- Mathematical acceptance relation for canonical reduction. -/
def accepts {width sourceWidth : Nat} (spec : ModulusSpec width)
    (input : Input sourceWidth) (output : Residue spec) : Prop :=
  output.val = input.val % spec.modulus

/-- Reduce an arbitrary word to its canonical representative. -/
def eval {width sourceWidth : Nat} (spec : ModulusSpec width)
    (input : Input sourceWidth) : Residue spec :=
  Residue.ofNat spec input.val

@[simp] theorem modularReduce_valid {width sourceWidth : Nat}
    (spec : ModulusSpec width) (input : Input sourceWidth) :
    valid spec input :=
  trivial

theorem modularReduce_input_range {sourceWidth : Nat} (input : Input sourceWidth) :
    input.val < ClassicalAlgorithms.modulus sourceWidth :=
  ClassicalAlgorithms.fixedWidthWord_lt_modulus input

@[simp] theorem modularReduce_eval_val {width sourceWidth : Nat}
    (spec : ModulusSpec width) (input : Input sourceWidth) :
    (eval spec input).val = input.val % spec.modulus :=
  rfl

theorem modularReduce_eval_range {width sourceWidth : Nat}
    (spec : ModulusSpec width) (input : Input sourceWidth) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

theorem modularReduce_eval_modEq {width sourceWidth : Nat}
    (spec : ModulusSpec width) (input : Input sourceWidth) :
    (eval spec input).val ≡ input.val [MOD spec.modulus] :=
  Residue.residueOfNat_modEq spec input.val

theorem modularReduce_eval_accepts {width sourceWidth : Nat}
    (spec : ModulusSpec width) (input : Input sourceWidth) :
    accepts spec input (eval spec input) :=
  rfl

/-- Reduction is value-preserving on an already canonical source word. -/
theorem modularReduce_eval_val_of_canonical {width sourceWidth : Nat}
    (spec : ModulusSpec width) (input : Input sourceWidth)
    (inputCanonical : input.val < spec.modulus) :
    (eval spec input).val = input.val := by
  rw [modularReduce_eval_val, Nat.mod_eq_of_lt inputCanonical]

/-- Reduction equals the evident intrinsic residue on a canonical source word. -/
theorem modularReduce_eval_eq_of_canonical {width sourceWidth : Nat}
    (spec : ModulusSpec width) (input : Input sourceWidth)
    (inputCanonical : input.val < spec.modulus) :
    eval spec input = (⟨input.val, inputCanonical⟩ : Residue spec) := by
  apply Fin.ext
  exact modularReduce_eval_val_of_canonical spec input inputCanonical

/-- At the maximum admitted modulus, every equal-width input is unchanged. -/
theorem modularReduce_eval_val_of_maximum {width : Nat}
    (spec : ModulusSpec width)
    (maximum : spec.modulus = ClassicalAlgorithms.modulus width)
    (input : Input width) :
    (eval spec input).val = input.val :=
  modularReduce_eval_val_of_canonical spec input
    (fixedWidthWord_lt_specModulus_of_eq_capacity spec maximum input)

end Reduce
end Modular

end ClassicalAlgorithms
end QuantumAlg

end
