/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Phase.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Boundary.Frame
import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Tail

/-!
# Actual word exchange and length refresh at the Euclidean macro boundary

The zero-shift phase complements precede the actual complete word swap,
coefficient length refresh, divisor length refresh, and Iter flip
[LYL+26, sec_EEA/sub_regshare.tex:306-313]. The exact word resegmentation
and ordered finite length update are already proved independently.

This owner connects those laws to the same actual native boundary block
and all eleven original register fields. A macro frame is a mathematical
basis specification, not input-dependent preparation or another executor.
The next divisor may be zero: no later positive-divisor premise is used
to make the final Euclidean exchange fit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.MacroBoundary

noncomputable section

open NumberTheory.SharedEEA

/-- The actual zero-shift block clears both phase bits on the complete unrotated deshift frame. -/
lemma zero_shift_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    ZeroShiftControl.step (DeshiftPhaseFrame.frame state modulus 0 valid conserved active
      (Nat.zero_le _) false iteration) =
      clearedFrame state modulus valid conserved active iteration := by
  let original := DeshiftPhaseFrame.frame state modulus 0 valid conserved active
    (Nat.zero_le _) false iteration
  have zero : original.shift = (0#modulus.size.size) := by
    apply BitVec.eq_of_toNat_eq
    rfl
  have divisor : original.divisorLength ≠ 0 := by
    intro zeroLength
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zeroLength
    change state.divisor.size = 0 at value
    have positive := Nat.size_pos.mpr active
    omega
  rw [ZeroShiftControl.step_eq_sourceStep original rfl, ZeroShiftControl.sourceStep,
    TerminalPredicate.condition_active original divisor]
  change { original with flags :=
    ⟨if decide (original.shift = (0#modulus.size.size)) then false else true,
      if decide (original.shift = (0#modulus.size.size)) then false else true,
      false, iteration⟩ } = _
  rw [decide_eq_true zero]
  apply Registers.ext_fields
  · rfl
  · exact congrArg
      (fun word : BitVec (CoefficientCapacity.work2CoefficientWidth state modulus +
          state.divisor.size) => word.cast
        (CoefficientCapacity.work2_width state modulus valid conserved))
      (TerminalTail.rotateLeft_zero _)
  · apply BitVec.eq_of_toNat_eq
    exact (NumberTheory.SharedEEA.LengthRefresh.encoded_length_toNat state.coefficient modulus
      (Capacity.iteration_fields_le state modulus valid conserved).2.2.1).symm
  · apply BitVec.eq_of_toNat_eq
    exact Nat.sub_self _
  · apply BitVec.eq_of_toNat_eq
    exact (NumberTheory.SharedEEA.LengthRefresh.encoded_length_toNat state.divisor modulus
      (Capacity.iteration_fields_le state modulus valid conserved).2.1).symm
  · exact zero
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Actual swap, both length updates, and Iter complement reach the next full macro frame. -/
lemma native_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (iteration : Bool) :
    TerminalBoundary.step (clearedFrame state modulus valid conserved active iteration) =
      frame (IterationState.step state) modulus (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) :=
  TerminalBoundaryFrame.native_frame state modulus valid conserved coprime active iteration

/-- Both final native blocks restore the macro flags and advance the complete physical payload. -/
lemma deshift_tail_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (iteration : Bool) :
    TerminalBoundary.step (ZeroShiftControl.step
      (DeshiftPhaseFrame.frame state modulus 0 valid conserved active
        (Nat.zero_le _) false iteration)) =
      frame (IterationState.step state) modulus (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) := by
  rw [zero_shift_frame state modulus valid conserved active iteration,
    native_frame state modulus valid conserved coprime active iteration]

end

end QuantumAlg.MAU.Inversion.SharedEEA.MacroBoundary
