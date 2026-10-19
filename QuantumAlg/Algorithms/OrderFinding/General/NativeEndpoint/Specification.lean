/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Algorithm.ClassicalOp
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Resources
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Resources
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Space
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
@[expose] public def SuccessfulOutcome (r : Nat) {t : Nat}
    (output : CShape.Value (outputShape t)) : Prop :=
  output = .optionSome (CShape.wordOfNat (t + 1) r)

/-- The source lower bound lies in the closed unit interval. -/
@[expose] public def successLB (r : Nat) : ProbabilityLowerBound where
  value := ENNReal.ofReal ((Nat.totient r : Real) / (3 * (r : Real)))
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    cases r with
    | zero => simp
    | succ r =>
        have totientLe : (Nat.totient (r + 1) : Real) ≤ r + 1 := by
          exact_mod_cast Nat.totient_le (r + 1)
        have denominatorPositive : (0 : Real) < 3 * ((r + 1 : Nat) : Real) := by
          positivity
        have rNonnegative : (0 : Real) ≤ r := by positivity
        apply (div_le_one denominatorPositive).2
        norm_num [Nat.cast_add, Nat.cast_one] at totientLe ⊢
        nlinarith

/-- The public modulus certificate supplies source capacity without an unknown order. -/
public lemma sourceAccess {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat) :
    ModExpOracleAccess spec.modulus x t width where
  modulus_pos := by have := spec.two_le; omega
  register_fits := spec.le_capacity

/-- **Input.** A fitted public modulus, a canonical borrowed modular base, and
a phase width satisfying the original source register window. The true order
is a specification witness, and the environment interprets the declared source query.

**Output.** The retained optional finite word equals the true order on success.

**Resource budget.** Independent native event, depth, resident and auxiliary
formulas cover the source sampler and the complete finite recovery.

**Success.** Every admitted source instance has probability at least
`totient(order) / (3 * order)` of returning its true order.

**Source.** [Sho95, source.tex:1614-1633] [dW19, qcnotes.tex:2293-2301],
with the finite recovery of the
measured phase word and the original canonical-base admission condition. -/
@[expose] public def problem {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat) :
    Problem (Sampling.Native.Framed.model t width)
      (pre width) (post t width) (outputShape t) where
  Witness := Nat
  valid := fun environment order state =>
    ∃ hinput : OrderFinding.Input spec.modulus x order,
      environment.quantum = OrderFinding.Native.interpretation (sourceAccess spec x t) ∧
        HasCanonicalBase hinput (sourceAccess spec x t) state ∧
          0 < t ∧ spec.modulus ^ 2 ≤ 2 ^ t ∧ 2 ^ t < 2 * spec.modulus ^ 2
  initialization := fun _ _ _ => True
  accepts := fun _ order _ output => SuccessfulOutcome order output
  successLB := fun _ order => successLB order
  states := fun _ _ => []
  resources :=
    { events := eventBudget t width
      resident := spaceBudget t width + (pre width).residentSpace
      auxiliary := spaceBudget t width + (pre width).auxiliarySpace }
  quantumTimeLimit := depthBudget t width

/-- Replacing the interpreter API preserves every original source admission condition. -/
public lemma problem_valid_source {N x order t width : Nat}
    (hinput : OrderFinding.Input N x order)
    (access : ModExpOracleAccess N x t width)
    (state : ExecutionState (Execution.Store (pre width)) (pre width).register) :
    (problem (modulusSpec hinput access) x t).valid
        (Sampling.Native.environment access) order state ↔
      HasCanonicalBase hinput access state ∧ 0 < t ∧ N ^ 2 ≤ 2 ^ t ∧ 2 ^ t < 2 * N ^ 2 := by
  constructor
  · rintro ⟨_source, _same, base, window⟩
    exact ⟨base, window⟩
  · rintro ⟨base, window⟩
    exact ⟨hinput, rfl, base, window⟩

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
