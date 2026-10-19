/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Selection.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Predicate

/-!
# Actual finite length-and-phase equality for arithmetic placement

Each fixed selector pattern is compared with the actual complete length
and phase source fields. The literal one-dirty pattern circuit xors the
answer into original Ctrl, restoring original Iter and every other field.
No input-dependent classical parameter or prepared quantum value replaces
these source reads [LYL+26, sec_EEA/sub_regshare.tex:22-26;
sec_EEA/sub_opt.tex:43-48,61-66].

Sign belongs to the readout only when requested for a low arithmetic
instruction that retains it. A signed arithmetic instruction uses the
layout omitting Sign so its inverse predicate computation does not read
a value changed by its own selected body.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelectionPredicate

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit ArithmeticSelectionLayout NativePredicate

/-- A compile-time pattern over exactly the retained physical selector sources. -/
abbrev Pattern (width : Nat) (includeSign : Bool) := Fin (sourceCount width includeSign) → Bool

/-- Every actual source bit equals its corresponding fixed selector bit. -/
abbrev Matches {width : Nat} {includeSign : Bool} (expected : Pattern width includeSign)
    (state : Registers width) : Prop :=
  (layout width includeSign).PatternMatches expected state

/-- The actual complete source equality value to xor into the original Ctrl field. -/
def condition {width : Nat} {includeSign : Bool} (expected : Pattern width includeSign)
    (state : Registers width) : Bool :=
  decide (Matches expected state)

/-- Exactly the established mask/conjunction/inverse-mask list at the real source layout. -/
def gates (width : Nat) (includeSign : Bool) (expected : Pattern width includeSign) :
    List (GateSpec (encoding width)) :=
  (layout width includeSign).patternGates expected

/-- Complete actual predicate execution changes only Ctrl, with no initialization premise. -/
lemma gates_step (width : Nat) (includeSign : Bool) (expected : Pattern width includeSign)
    (state : Registers width) :
    GateSpec.stepList (gates width includeSign expected) state =
      xorControl (condition expected state) state :=
  ((layout width includeSign).patternGates_step expected state).trans
    (NativePredicate.conditional_flip_xor (Matches expected state) state)

/-- Changing only Ctrl preserves every actually read source coordinate. -/
lemma condition_xorControl (width : Nat) (includeSign : Bool)
    (expected : Pattern width includeSign) (value : Bool) (state : Registers width) :
    condition expected (xorControl value state) = condition expected state := by
  have retained : ∀ index,
      ((layout width includeSign).source.bit index).get (xorControl value state) =
        ((layout width includeSign).source.bit index).get state := by
    intro index
    change (sourceBit width includeSign index).get (xorControl value state) =
      (sourceBit width includeSign index).get state
    rw [sourceBit_get, sourceBit_get]
    rfl
  simp only [condition, Matches, Word.OneDirtyLayout.PatternMatches, retained]

/-- The actual inverse native list has the same full-frame xor law, retaining arbitrary Iter. -/
lemma reverse_step (width : Nat) (includeSign : Bool) (expected : Pattern width includeSign)
    (state : Registers width) :
    GateSpec.stepList (gates width includeSign expected).reverse state =
      xorControl (condition expected state) state :=
  ((layout width includeSign).patternGates_reverse_step expected state).trans
    (NativePredicate.conditional_flip_xor (Matches expected state) state)

/-- Compile the actual equality gates used in the complete register-state equation. -/
def program (width : Nat) (includeSign : Bool) (expected : Pattern width includeSign) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty
    (gates width includeSign expected)

/-- Exact normalized basis amplitudes of the same actual equality program. -/
lemma program_realizes (width : Nat) (includeSign : Bool)
    (expected : Pattern width includeSign) :
    UnitaryCircuit.Realizes (encoding width) (program width includeSign expected) environment
      (fun state => xorControl (condition expected state) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width includeSign expected) (gates_step width includeSign expected) environment

/-- The implementation has a proved linear elementary gate bound for each fixed pattern. -/
lemma gates_length_le (width : Nat) (includeSign : Bool)
    (expected : Pattern width includeSign) :
    (gates width includeSign expected).length ≤ 10 * sourceCount width includeSign + 1 :=
  (layout width includeSign).patternGates_length_le expected

/-- Unit depth is the actual emitted primitive count, including both masks and all dirty cleanup. -/
lemma program_unitDepth (width : Nat) (includeSign : Bool)
    (expected : Pattern width includeSign) :
    (program width includeSign expected).evaluatedEventDepth (fun _ => 1) =
      (gates width includeSign expected).length :=
  GateSpec.programList_evaluatedEventDepth_unit (QubitLayout.canonical _) .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelectionPredicate
