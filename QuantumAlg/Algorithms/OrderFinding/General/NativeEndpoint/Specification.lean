/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Resources
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Space
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent specification for the connected native general order finder

The caller supplies a canonical borrowed modular base. The phase width lies
in the source register window, and the result is accepted only when finite
recovery returns the true order. Independent event, depth, resident and
auxiliary budgets apply to the same connected source-sample/recovery circuit.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

/-- The finite recovered word is successful exactly when it contains the true order. -/
def SuccessfulOutcome (r : Nat) {t : Nat}
    (output : CShape.Value (outputShape t)) : Prop :=
  output = .optionSome (.unsignedWord
    (ClassicalAlgorithms.OrderRecovery.candidateWord t r))

/-- The source lower bound lies in the closed unit interval. -/
def successLB (r : Nat) : ProbabilityLowerBound where
  value := ENNReal.ofReal (orderFindingOutputSuccessLowerBound r)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    cases r with
    | zero => simp [orderFindingOutputSuccessLowerBound]
    | succ r =>
        have totientLe : (Nat.totient (r + 1) : Real) ≤ r + 1 := by
          exact_mod_cast Nat.totient_le (r + 1)
        have denominatorPositive : (0 : Real) < 3 * ((r + 1 : Nat) : Real) := by
          positivity
        have rNonnegative : (0 : Real) ≤ r := by positivity
        unfold orderFindingOutputSuccessLowerBound
        apply (div_le_one denominatorPositive).2
        norm_num [Nat.cast_add, Nat.cast_one] at totientLe ⊢
        nlinarith

/-- The actual source sampler and finite recovery solve the original source
input window with one modular-exponentiation query and full retained output. -/
public def problem {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    Problem (Sampling.Native.Framed.model access)
      (pre width) (post t width) (outputShape t) where
  valid := fun state => HasCanonicalBase hinput access state ∧
    0 < t ∧ N ^ 2 ≤ 2 ^ t ∧ 2 ^ t < 2 * N ^ 2
  initialization := fun _ => True
  accepts := fun _ output => SuccessfulOutcome r output
  successLB := successLB r
  states := []
  resources :=
    { events := eventBudget access
      resident := spaceBudget t width + (pre width).residentSpace
      auxiliary := spaceBudget t width + (pre width).auxiliarySpace }
  depth :=
    { duration := fun _ => 1
      limit := depthBudget t width
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
