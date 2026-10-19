/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Phase.Frame
import all QuantumAlg.Util.NumberTheory.SharedEEA.Deshift

/-!
# Reachable Sign in the actual complete coefficient comparison

The completed coefficient phase enters phase four with Sign one. Its
first full comparison is false; each later comparison is true. These
distinct inputs all produce Sign one before the actual ordered control
update [LYL+26, sec_EEA/sub_regshare.tex:297-305;
LYL+26, sec_EEA/sub_opt.tex:61-75].

Both comparison bounds follow from the original admissible macro state.
The equality below concerns the actual native coefficient block on its
entire shared-register frame, including every complementary word bit and
arbitrary Iter. No new input predicate or precomputed preparation data is
used to supply the result of the comparison.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DeshiftComparison

noncomputable section

open NumberTheory.SharedEEA DeshiftPhaseFrame

/-- The completed actual coefficient phase is exactly the first deshift frame, including Sign. -/
lemma entry_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    CoefficientTrajectory.phaseFrame state modulus state.quotient.size
        valid conserved active le_rfl iteration =
      frame state modulus state.quotient.size valid conserved active le_rfl true iteration := by
  apply Registers.ext_fields
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change decide (state.quotient.size = state.quotient.size) = true
    exact decide_eq_true rfl
  · change decide (state.quotient.size = state.quotient.size) = true
    exact decide_eq_true rfl
  · rfl
  · rfl

/-- The initial and subsequent full comparisons both give the Sign required by native control. -/
lemma compared_sign (state : IterationState) (count : Nat)
    (valid : state.Admissible) (active : 0 < state.divisor)
    (beforeEnd : count < state.quotient.size) :
    (decide (count = 0) ^^
      decide (state.coefficient * 2 ^ (state.quotient.size - count) ≤
        (IterationState.step state).coefficient)) = true := by
  obtain ⟨positive, lower, upper⟩ := Deshift.phaseValue_bounds state valid active
  have places := Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  change (Alignment.align state.remainder state.divisor).places = state.quotient.size at places
  rw [places] at positive lower upper
  rw [Deshift.phaseValue_eq_next state active] at lower upper
  simpa only [Nat.mul_comm] using
    Deshift.compared_sign state.coefficient (IterationState.step state).coefficient
      state.quotient.size count positive beforeEnd lower upper

/-- The actual native comparison sets Sign one and preserves the complete reachable frame. -/
lemma native_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus (state.quotient.size - count) valid conserved active
        (Nat.sub_le _ _) (decide (count = 0)) iteration) =
      frame state modulus (state.quotient.size - count) valid conserved active
        (Nat.sub_le _ _) true iteration := by
  rw [DeshiftPhaseFrame.native_frame state modulus (state.quotient.size - count)
    valid conserved active (Nat.sub_le _ _) (decide (count = 0)) iteration,
    compared_sign state count valid active beforeEnd]

end

end QuantumAlg.MAU.Inversion.SharedEEA.DeshiftComparison
