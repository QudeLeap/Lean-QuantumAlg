/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.PackingBoundary
import all QuantumAlg.Util.NumberTheory.SharedEEA.Quotient.Schedule

/-!
# Exact terminal word and two fixed zero padding positions

The source's shared words have `n+3` bits, with the coefficient at the
left in little-endian order, followed by a zero separator and the
big-endian remainder [LYL+26, sec_EEA/sub_regshare.tex:16-23]. At a genuine
coprime-input terminal boundary, the gcd is one and the conserved cross-sum
forces the first coefficient to equal the modulus. Thus the actual first
word is `reverse_n(p) ++ 001`.

This owner proves that entire word equality from the original input
domain. The fixed positions `n` and `n+1`, counted from the physical left
edge as `getMsbD` indices, are zero. They are distinct from every modulus
bit and from the final constant-one position. These are facts about the
actual packed layout, rather than a dimensional casting argument.

The two positions are candidates for retaining high terminal-counter
bits without allocating extra wires. No claim here says that they are
zero during active phases, that carry/borrow gates have been implemented,
or that their histories can be erased. Selecting their use requires a
real reversible implementation and its own resource accounting. This
owner neither changes the registered source's terminal instructions nor
claims its space formula for an unimplemented repair.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.TerminalPadding

open QuantumAlg.ClassicalAlgorithms.NumberTheory

/-- Active mathematical macro steps preserve the source cross-sum through their exact update. -/
theorem activeRun_balance (fuel : Nat) (state : IterationState) :
    (QuotientTrajectory.activeRun fuel state).balance = state.balance := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    by_cases finished : state.divisor = 0
    · simp only [QuotientTrajectory.activeRun, if_pos finished]
    · rw [QuotientTrajectory.activeRun, if_neg finished, inductionHypothesis,
        IterationState.step_balance]

/-- Every reached macro state satisfies the invariant needed to encode its exact shared words. -/
theorem activeRun_admissible (fuel : Nat) (state : IterationState) (valid : state.Admissible) :
    (QuotientTrajectory.activeRun fuel state).Admissible := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel inductionHypothesis =>
    by_cases finished : state.divisor = 0
    · simpa only [QuotientTrajectory.activeRun, if_pos finished] using valid
    · rw [QuotientTrajectory.activeRun, if_neg finished]
      exact inductionHypothesis (IterationState.step state)
        (IterationState.step_admissible state valid (Nat.pos_of_ne_zero finished))

/-- The actual active macro trajectory from the folded input, with proved adequate fuel. -/
def finalState (modulus input : Nat) : IterationState :=
  QuotientTrajectory.activeRun (Euclid.gcdFuel modulus.size)
    (IterationState.initial modulus (foldInput modulus input).2)

/-- The original positive-residue domain supplies the full final reachable invariant. -/
theorem final_admissible (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (finalState modulus input).Admissible :=
  activeRun_admissible _ _ (folded_initial_admissible modulus input positive bounded)

/-- The exact final cross-sum remains the original modulus. -/
theorem final_balance (modulus input : Nat) : (finalState modulus input).balance = modulus :=
  (activeRun_balance (Euclid.gcdFuel modulus.size)
    (IterationState.initial modulus (foldInput modulus input).2)).trans
      (IterationState.initial_balance modulus _)

/-- Mathematical termination at divisor zero is established internally for every original input. -/
theorem final_divisor (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (finalState modulus input).divisor = 0 :=
  QuotientSchedule.folded_finishes modulus input positive bounded

/-- Every coprime positive input reaches the actual gcd-one terminal remainder. -/
theorem final_remainder (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (finalState modulus input).remainder = 1 := by
  have preserved := QuotientTrajectory.activeRun_gcd (Euclid.gcdFuel modulus.size)
    (IterationState.initial modulus (foldInput modulus input).2)
  change Nat.gcd (finalState modulus input).remainder (finalState modulus input).divisor =
    Nat.gcd modulus (foldInput modulus input).2 at preserved
  rw [final_divisor modulus input positive bounded, Nat.gcd_zero_right,
    foldInput_gcd modulus input bounded.le] at preserved
  exact preserved.trans coprime.symm

/-- The retained terminal coefficient equals the modulus by the exact conserved source cross-sum. -/
theorem final_coefficient (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (finalState modulus input).coefficient = modulus := by
  have conserved := final_balance modulus input
  change (finalState modulus input).remainder * (finalState modulus input).coefficient +
    (finalState modulus input).divisor * (finalState modulus input).previousCoefficient = modulus
      at conserved
  simpa only [final_remainder modulus input coprime positive bounded,
    final_divisor modulus input positive bounded, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
    using conserved

/-- The terminal constant word's complete opposite-endian payload, including all three tail bits. -/
def terminalPayload (modulus : Nat) : WordPacking.Work2Payload modulus.size 3 :=
  ⟨BitVec.ofNatLT modulus (Nat.lt_size_self modulus), 1⟩

/-- The literal terminal first word: reversed modulus followed by exactly the three bits `001`. -/
def terminalWord (modulus : Nat) : BitVec (modulus.size + 3) :=
  WordPacking.packWork2 (terminalPayload modulus)

/-- Exact terminal field values imply equality of the entire physical first word. -/
theorem firstWord_terminal (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (remainder : state.remainder = 1) (coefficient : state.coefficient = modulus) :
    PackingBoundary.firstWord state modulus valid conserved = terminalWord modulus := by
  unfold PackingBoundary.firstWord terminalWord
  exact PackingBoundary.work1_resegment _ _
    (PackingBoundary.first_width state modulus valid conserved) rfl rfl coefficient remainder

/-- The coprime-input domain establishes the complete terminal word without new premises. -/
theorem final_firstWord (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    PackingBoundary.firstWord (finalState modulus input) modulus
        (final_admissible modulus input positive bounded) (final_balance modulus input) =
      terminalWord modulus :=
  firstWord_terminal _ _ _ _ (final_remainder modulus input coprime positive bounded)
    (final_coefficient modulus input coprime positive bounded)

/-- Each original modulus bit occupies its actual distinct left-to-right physical position. -/
theorem terminalWord_main_bit (modulus index : Nat) (within : index < modulus.size) :
    (terminalWord modulus).getMsbD index = modulus.testBit index :=
  WordPacking.packWork2_coefficient_bit (terminalPayload modulus) index within

/-- The two proposed high-counter positions are existing fixed wires of the first shared word. -/
def paddingPosition (modulus : Nat) (index : Fin 2) : Fin (modulus.size + 3) :=
  ⟨modulus.size + index.val, by have bound := index.isLt; omega⟩

/-- The candidate high bits refer to distinct physical positions. -/
theorem paddingPosition_injective (modulus : Nat) :
    Function.Injective (paddingPosition modulus) := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  change modulus.size + left.val = modulus.size + right.val at values
  omega

/-- Neither candidate position overlaps a modulus bit or the final constant-one position. -/
theorem paddingPosition_bounds (modulus : Nat) (index : Fin 2) :
    modulus.size ≤ (paddingPosition modulus index).val ∧
      (paddingPosition modulus index).val < modulus.size + 2 := by
  have bound := index.isLt
  change modulus.size ≤ modulus.size + index.val ∧ modulus.size + index.val < modulus.size + 2
  omega

/-- The actual terminal word supplies two zero bits at precisely the proposed fixed positions. -/
theorem terminalWord_padding_zero (modulus : Nat) (index : Fin 2) :
    (terminalWord modulus).getMsbD (paddingPosition modulus index).val = false := by
  change (WordPacking.packWork2 (terminalPayload modulus)).getMsbD
    (modulus.size + index.val) = false
  rw [WordPacking.packWork2_remainder_bit]
  change (1 : BitVec 3).getMsbD index.val = false
  have bound := index.isLt
  have possibilities : index.val = 0 ∨ index.val = 1 := by omega
  rcases possibilities with zero | one
  · rw [zero]
    decide
  · rw [one]
    decide

/-- The neighboring final bit is one and is excluded from the candidate high-counter positions. -/
theorem terminalWord_last_one (modulus : Nat) :
    (terminalWord modulus).getMsbD (modulus.size + 2) = true := by
  change (WordPacking.packWork2 (terminalPayload modulus)).getMsbD (modulus.size + 2) = true
  rw [WordPacking.packWork2_remainder_bit]
  change (1 : BitVec 3).getMsbD 2 = true
  decide

/-- Both actual fixed positions are zero after the coprime-input macro computation. -/
theorem final_padding_zero (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) (index : Fin 2) :
    (PackingBoundary.firstWord (finalState modulus input) modulus
      (final_admissible modulus input positive bounded) (final_balance modulus input)).getMsbD
        (paddingPosition modulus index).val = false := by
  rw [final_firstWord modulus input coprime positive bounded]
  exact terminalWord_padding_zero modulus index

end QuantumAlg.NumberTheory.SharedEEA.TerminalPadding
