/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Algorithms.OrderFinding.General.Recovery.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.SourceEvent
import all QuantumAlg.Util.Classical.OrderRecovery
import all QuantumAlg.Util.Order.Finding

/-!
# Source recovery from the canonical reduced base and a measured sample

This is the original continued-fraction correctness bridge. It depends only
on the source oracle assumptions and the intrinsic finite-word mathematics,
not on a runtime executor or a supplied probability and resource witness.
The actual native recovery program must read this base from the borrowed
classical cell and prove its result agrees with this independent specification.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

/-- The source minimal-order hypothesis is exactly the typed validation
predicate for the reduced borrowed base. -/
lemma semanticInput_minimalUnitOrder {N x r t m : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t m)
    (outcome : TerminalZMeasure.Outcome t) :
    ClassicalAlgorithms.OrderRecovery.MinimalUnitOrder
      (recoverySpec hinput A)
      (semanticInput hinput A outcome) r := by
  have hN : 1 < N := lt_of_lt_of_le (by decide) hinput.modulus_ge_two
  refine ⟨hinput.order_pos, ?_, ?_⟩
  · change (x % N) ^ r ≡ 1 [MOD N]
    have original : x ^ r ≡ 1 [MOD N] := by
      rw [Nat.ModEq, hinput.order_eq_one, Nat.mod_eq_of_lt hN]
    exact (Nat.mod_modEq x N).pow r |>.trans original
  · intro smaller hpositive hsmaller hreturn
    have normalized : x ^ smaller % N = 1 := by
      change (x % N) ^ smaller ≡ 1 [MOD N] at hreturn
      have original := ((Nat.mod_modEq x N).pow smaller).symm.trans hreturn
      rw [Nat.ModEq] at original
      simpa [Nat.mod_eq_of_lt hN] using original
    exact (Nat.not_le_of_lt hsmaller)
      (hinput.minimal smaller hpositive normalized)

/-- Every source-certified recoverable outcome yields the true order under pure recovery. -/
lemma recoverUnitOrder_eq_some_of_recoverableOutcome
    {N x t m r : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (hfit : r < 2 ^ (t + 1))
    {outcome : TerminalZMeasure.Outcome t}
    (hrecoverable : NativeRecoverableOutcome
      (ZMod.unitOfCoprime x hinput.coprime) r outcome) :
    ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
        (recoverySpec hinput A)
        (semanticInput hinput A outcome) =
      some (ClassicalAlgorithms.OrderRecovery.candidateWord t r) := by
  rcases hrecoverable with
    ⟨_orbit, candidate, hvalidated, hcandidate⟩
  subst candidate
  rcases hvalidated.1 with ⟨index, hdenominator⟩
  let spec := recoverySpec hinput A
  let input := semanticInput hinput A outcome
  have member : r ∈
      ClassicalAlgorithms.OrderRecovery.candidateSchedule
        spec input := by
    have trace :=
      ClassicalAlgorithms.OrderRecovery.realConvergentDen_mem_candidateSchedule
        spec input index
    have decodedTrace :
        ((((ClassicalAlgorithms.TerminalDecode.fullRegisterIndex outcome).val : Real) /
          (2 : Real) ^ t).convergent
          index).den ∈
            ClassicalAlgorithms.OrderRecovery.candidateSchedule
              spec input := by
      simpa [spec, input,
        ClassicalAlgorithms.OrderRecovery.decodedIndex,
        ClassicalAlgorithms.OrderRecovery.fullRegisterIndex_val,
        semanticInput] using trace
    rw [hdenominator] at decodedTrace
    exact decodedTrace
  rcases ClassicalAlgorithms.OrderRecovery.candidateSchedule_firstOccurrence
      spec input member with ⟨rejected, suffix, schedule, earlier⟩
  exact
    ClassicalAlgorithms.OrderRecovery.recoverUnitOrder_eq_some_of_recoverableSchedule
      spec input rejected suffix schedule earlier hfit
      (semanticInput_minimalUnitOrder hinput A outcome)

/-- The validity hypotheses make the true order fit the typed candidate word. -/
lemma order_fits_candidateWord {N x r t : Nat}
    (hinput : OrderFinding.Input N x r) (hregister : N ^ 2 ≤ 2 ^ t) :
    r < 2 ^ (t + 1) := by
  calc
    r < N := input_order_lt_modulus hinput
    _ ≤ N ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right N
        (lt_of_lt_of_le (by decide) hinput.modulus_ge_two)
    _ ≤ 2 ^ t := hregister
    _ < 2 ^ (t + 1) :=
      Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self t)

end

end QuantumAlg.OrderFinding.ShorSourceJoint
