/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Values
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Values
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Soundness of checked known-order recovery candidates

The abstract group equality is sufficient to identify every accepted bounded
candidate with the proof-side discrete logarithm.  No representation of a
group element or implementation cost is introduced.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

noncomputable section

universe u

variable {G : Type u} [Group G]

local instance : DecidableEq G := Classical.decEq G

private theorem word_injective {width : Nat} (left right : CShape.Word width)
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- The canonical secret is not truncated by the known-order word width. -/
public theorem secretWord_toNat (P : KnownOrderProblem G)
    (secret : Canonical.Probability.SecretInput P) :
    (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val).toNat =
      secret.secret.val := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  rw [CShape.wordOfNat_val]
  exact Nat.mod_eq_of_lt
    ((ZMod.val_lt secret.secret).trans_le (FiniteCyclicDLP.order_le_fourierModulus P))

/-- Every accepted bounded candidate is the advertised discrete logarithm. -/
public theorem attemptCandidateValue_eq_secret_of_accepted
    (P : KnownOrderProblem G) (secret : Canonical.Probability.SecretInput P)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (modulus : spec.modulus = P.order)
    (input : CShape.Value
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (accepted : attemptAcceptedValue P spec input = true) :
    attemptCandidateValue spec input =
      CShape.wordOfNat (OrderPreparation.width P) secret.secret.val := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  have equality := (Bool.and_eq_true_iff.mp accepted).2
  have samePower :
      P.generator ^ (attemptCandidateValue spec input).toNat =
        P.generator ^ secret.secret.val :=
    (of_decide_eq_true equality).trans secret.target_eq_generator_pow.symm
  have sameResidue := pow_inj_mod.mp samePower
  have bounded := attemptCandidateValue_lt spec input
  rw [modulus] at bounded
  apply word_injective
  rw [secretWord_toNat]
  simpa only [← P.order_eq_orderOf, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (ZMod.val_lt secret.secret)] using sameResidue

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
