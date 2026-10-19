/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Phase.Exchange

/-!
# Actual phase-two quotient-length increment and retained selector fields

The native Sign selector reads both complete length fields and both phase
bits, and restores all those actual source coordinates before executing
the native quotient update [LYL+26, sec_EEA/sub_regshare.tex:281-287;
LYL+26, sec_EEA/sub_opt.tex:52-59]. This owner follows those exact gates
through their previously proved source-bit equations.

The general increment equation is finite-word arithmetic at every width.
At a reachable division position, the actual alignment bound proves that
the increment does not wrap and that the resulting quotient length is
nonzero. This is derived inside the original macro domain; no caller
supplies a counter-range promise or a classical copy of the live length.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SignQuotientFields

noncomputable section

open RemainderPhaseFrame
open NumberTheory.SharedEEA

private lemma exchange_fields (width : Nat) (selected : Fin (width + 3))
    (state : Registers width) :
    (SelectionSwap.exchange width selected state).coefficientLength = state.coefficientLength ∧
      (SelectionSwap.exchange width selected state).quotientLength = state.quotientLength ∧
        (SelectionSwap.exchange width selected state).flags.first = state.flags.first ∧
          (SelectionSwap.exchange width selected state).flags.second = state.flags.second := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getMsbD_eq
    intro bit within
    exact (SelectionKey.source_coefficient width _ ⟨bit, within⟩).symm.trans
      ((SelectionSwap.exchange_source_get width selected
        (SelectionKey.coefficientIndex width ⟨bit, within⟩) state).trans
          (SelectionKey.source_coefficient width state ⟨bit, within⟩))
  · apply BitVec.eq_of_getMsbD_eq
    intro bit within
    exact (SelectionKey.source_quotient width _ ⟨bit, within⟩).symm.trans
      ((SelectionSwap.exchange_source_get width selected
        (SelectionKey.quotientIndex width ⟨bit, within⟩) state).trans
          (SelectionKey.source_quotient width state ⟨bit, within⟩))
  · exact (SelectionKey.source_first width _).symm.trans
      ((SelectionSwap.exchange_source_get width selected
        (SelectionKey.firstIndex width) state).trans
        (SelectionKey.source_first width state))
  · exact (SelectionKey.source_second width _).symm.trans
      ((SelectionSwap.exchange_source_get width selected
        (SelectionKey.secondIndex width) state).trans
        (SelectionKey.source_second width state))

/-- The actual phase-two source block increments the live finite quotient length by one. -/
lemma source_quotientLength (width : Nat) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    (SignQuotient.sourceStep width state).quotientLength = state.quotientLength + 1 := by
  let selected : Fin (width + 3) :=
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat + 1, within⟩
  have retained := exchange_fields width selected state
  have firstSame := retained.2.2.1.trans first
  have secondSame := retained.2.2.2.trans second
  unfold SignQuotient.sourceStep
  rw [RemainderExchange.selected_source width state first second within]
  change (if PhaseQuotient.condition (SelectionSwap.exchange width selected state) then
      if (SelectionSwap.exchange width selected state).flags.first then
        (SelectionSwap.exchange width selected state).quotientLength - 1
      else (SelectionSwap.exchange width selected state).quotientLength + 1
    else (SelectionSwap.exchange width selected state).quotientLength) = _
  simp only [PhaseQuotient.condition, firstSame, secondSame, Bool.false_xor, if_true,
    Bool.false_eq_true, if_false, retained.2.1]

/-- The actual selector and length program retain the coefficient length and both source phases. -/
lemma source_retained (width : Nat) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    (SignQuotient.sourceStep width state).coefficientLength = state.coefficientLength ∧
      (SignQuotient.sourceStep width state).flags.first = false ∧
        (SignQuotient.sourceStep width state).flags.second = true := by
  unfold SignQuotient.sourceStep
  rw [RemainderExchange.selected_source width state first second within]
  have retained := exchange_fields width
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat + 1, within⟩ state
  exact ⟨retained.1, retained.2.2.1.trans first, retained.2.2.2.trans second⟩

/-- Internal Ctrl-zero specializes the same native quotient update, including all finite widths. -/
lemma native_quotientLength (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    (SignQuotient.step width state).quotientLength = state.quotientLength + 1 := by
  rw [SignQuotient.step_eq_sourceStep width state clean]
  exact source_quotientLength width state first second within

/-- The actual quotient counter reaches the next written length without a reachable wrap. -/
lemma division_quotientLength_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count
        valid conserved active beforeEnd iteration))).quotientLength.toNat =
        count + 1 := by
  let after := ArithmeticBlocks.remainderStep modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration)
  have fields := RemainderPhaseExchange.native_fields state modulus count
    valid conserved active beforeEnd iteration
  have position := RemainderPhaseExchange.next_position state modulus count
    valid conserved active beforeEnd iteration
  have alignment := (Alignment.align_places_le state.remainder state.divisor).trans
    (Nat.size_le_size (Capacity.iteration_fields_le state modulus valid conserved).1)
  have countBound : count + 1 < 2 ^ modulus.size.size :=
    (show count + 1 ≤ modulus.size by omega).trans_lt (Nat.lt_size_self modulus.size)
  have oneBound : 1 < 2 ^ modulus.size.size := by omega
  have quotient : after.quotientLength.toNat = count := fields.2.1
  change (SignQuotient.step modulus.size after).quotientLength.toNat = _
  rw [native_quotientLength modulus.size after fields.2.2.2.2
    fields.2.2.1 fields.2.2.2.1 position.1, BitVec.toNat_add, quotient]
  change (count + 1 % 2 ^ modulus.size.size) % 2 ^ modulus.size.size = count + 1
  rw [Nat.mod_eq_of_lt oneBound, Nat.mod_eq_of_lt countBound]

/-- Every real division update leaves a nonzero written quotient length for phase control. -/
lemma division_quotientLength_ne_zero (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).quotientLength ≠
        0 := by
  intro zero
  have value := congrArg BitVec.toNat zero
  rw [division_quotientLength_toNat state modulus count
    valid conserved active beforeEnd iteration] at value
  change count + 1 = 0 at value
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.SignQuotientFields
