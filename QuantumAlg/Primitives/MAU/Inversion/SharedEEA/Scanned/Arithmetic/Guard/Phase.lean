/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Signed
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Low
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Predicate

/-!
# The four actual original-field arithmetic phase predicates

Each public source-instruction choice emits one fixed native word.
Its predicate is read from the original quantum fields. Original Iter
is the arbitrary retained control, original Ctrl is the only output,
and the existing arbitrary operand work bit is restored within each
real call [LYL+26, sec_EEA/sub_opt.tex:43-48,61-66].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

/-- Independent source phase condition on the complete original finite source fields. -/
def condition (width : Nat) (signed coefficient : Bool) (state : Data width) : Bool :=
  if signed then
    if coefficient then state.1.flags.first
    else !state.1.flags.first && decide (state.1.divisorLength ≠ 0)
  else
    if coefficient then state.1.flags.first && (state.1.flags.second || !state.1.flags.sign)
    else !state.1.flags.first && (!state.1.flags.second || !state.1.flags.sign) &&
      decide (state.1.divisorLength ≠ 0)

/-- The public signed/low source choice selects its actual emitted native predicate word. -/
def gates (width : Nat) (signed coefficient : Bool) : List (GateSpec (encoding width)) :=
  if signed then signedGates width coefficient else lowGates width coefficient

/-- Flip only original Ctrl by the actual phase condition and original arbitrary Iter. -/
def step (width : Nat) (signed coefficient : Bool) : Data width → Data width :=
  predicateFlip (flag width 4)
    (fun state => condition width signed coefficient state && (flag width 3).get state)

/-- Every native phase word has exactly its independent full-state condition. -/
lemma gates_step (width : Nat) (signed coefficient : Bool) (state : Data width) :
    GateSpec.stepList (gates width signed coefficient) state =
      step width signed coefficient state := by
  cases signed with
  | false =>
      simp only [gates, Bool.false_eq_true, if_false]
      rw [lowGates_step]
      simp only [lowStep, step, predicateFlip, condition, Bool.false_eq_true, if_false]
      rw [Bool.and_comm]
  | true =>
      simp only [gates, if_true]
      rw [signedGates_step]
      simp only [signedStep, step, predicateFlip, condition, if_true]
      rw [Bool.and_comm]

/-- Compile the same physical native phase predicate without adding any quantum system. -/
def program (width : Nat) (signed coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width signed coefficient)

/-- Actual coherent execution preserves the complete source frame and every relative phase. -/
lemma program_realizes (width : Nat) (signed coefficient : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width signed coefficient) environment
      (step width signed coefficient) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step width signed coefficient) environment

/-- The phase predicate reads no part of the complete shared address/prefix/conjunction pool. -/
lemma step_pool (width : Nat) (signed coefficient : Bool) (state : Data width) :
    (step width signed coefficient state).2 = state.2 := by
  unfold step predicateFlip
  split <;> rfl

/-- Replacing the arbitrary original Ctrl changes none of the source condition. -/
lemma condition_control_flip (width : Nat) (signed coefficient : Bool) (state : Data width) :
    condition width signed coefficient ((flag width 4).flip state) =
      condition width signed coefficient state := rfl

/-- Replacing arbitrary original Iter also changes none of the actual source condition. -/
lemma condition_iteration_flip (width : Nat) (signed coefficient : Bool) (state : Data width) :
    condition width signed coefficient ((flag width 3).flip state) =
      condition width signed coefficient state := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
