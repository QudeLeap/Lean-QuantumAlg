/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Resources
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Success
public import QuantumAlg.Core.Algorithm.Problem

/-!
# Independent all-positive-order finite-cyclic DLP specification

The executable input is empty.  The secret remains a proof-side witness in
the accepted-output relation.  The classical finite-group service may start
in any hidden state because every actual power check begins with its granted
explicit reset query.
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The exact accepted word is the advertised bounded residue logarithm. -/
@[expose] public def accepts {P : KnownOrderProblem G} (secret : FiniteCyclicDLP.Input P)
    (_initial : Execution.Store Reusable.pre)
    (output : CShape.Value (.option (.unsignedWord (OrderPreparation.width P)))) : Prop :=
  output = .optionSome
    (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)

/-- The source endpoint's fixed two-thirds success threshold. -/
@[expose] public def successLowerBound : ProbabilityLowerBound where
  value := ENNReal.ofReal ((2 : Real) / 3)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    norm_num

/-- Complete native event and live-space limits, fixed independently of a path. -/
@[expose] public def resourceBudget (P : KnownOrderProblem G) :
    ResourceBudget (Reusable.model P) where
  events := eventBudget P
  resident := residentBudget P
  auxiliary := auxiliaryBudget P

/-- The independent whole-run unit-event ceiling also bounds quantum computation time. -/
@[expose] public def quantumTimeLimit (P : KnownOrderProblem G) : Nat :=
  depthLimit P (fun _ => 1)

/-- Exact classical recovery protocol for the retained samples.

**Input.** The retained sample vector, with arbitrary incoming reference and
hidden finite-group service state. Every power check explicitly resets that
service before use.

**Output.** One optional word, exactly `recoveredValue P` of the incoming sample
cells. It is zero for order one; otherwise it is the first checked candidate,
or no value when every candidate fails.

**Resource budget.** The independent event allowance is `recoveryEventBudget P`,
with live-space allowances `residentBudget P` and `auxiliaryBudget P`. The unit
depth limit is `recoveryDepthLimit P (fun _ => 1)`. These formulas include result
allocation, verification and first-success selection.

**Success.** The exact input-to-output recovery relation holds with probability
one for every input sample vector.

**Source.** Candidate recovery and group verification follow
[Sho95, source.tex:1907] and [Sho95, source.tex:1984]. The exact deterministic
relation and native resource formulas certify this implementation. -/
@[expose] public def recoveryProblem (P : KnownOrderProblem G) :
    Problem (Reusable.model P) (sampledContext P) (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  Witness := Unit
  valid := fun environment _ _ => environment = Reusable.sourceEnvironment P
  initialization := fun _ _ _ => True
  accepts := fun _ _ initial output => output = recoveredValue P
    (initial.read (Reusable.samplesInput P (sampleCount P)))
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => []
  resources := {
    events := recoveryEventBudget P
    resident := residentBudget P
    auxiliary := auxiliaryBudget P }
  quantumTimeLimit := recoveryDepthLimit P (fun _ => 1)

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
