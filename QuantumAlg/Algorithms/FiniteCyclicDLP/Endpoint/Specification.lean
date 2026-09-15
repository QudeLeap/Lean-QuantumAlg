/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Run
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Primitives.UniformSuperposition
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Resources
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent specification for the original finite-cyclic endpoint

The original secret witness belongs to the accepted-output relation, not the
executable parameters. Local input validity fixes the one borrowed target and
admits every external reference extension. The resource limits are independent
formulas; every live bank, sample, result and recovery workspace is counted.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint.Specification

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Every positive classical block contains the same original encoded borrowed target. -/
public def inputDomain (P : KnownOrderProblem G) (A : Access P)
    (state : ExecutionState (Store (pre P)) (pre P).register) : Prop :=
  ∀ store, 0 < (state.block store).mass → store = inputStore A

/-- The original exact accepted word is the advertised bounded residue-class logarithm. -/
public def accepts {P : KnownOrderProblem G} (input : Probability.SecretInput P)
    (output : CShape.Value (.option (.unsignedWord (orderWidth P)))) : Prop :=
  output = .optionSome (CShape.wordOfNat (orderWidth P) input.secret.val)

/-- The original fixed endpoint threshold is two thirds. -/
public def successLowerBound : ProbabilityLowerBound where
  value := ENNReal.ofReal ((2 : Real) / 3)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    norm_num

/-- Native event and complete storage budgets are fixed before choosing an implementation. -/
public def resourceBudget (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    ResourceBudget .quantum where
  events := eventBudget P B A
  resident := residentBudget P B A
  auxiliary := auxiliaryBudget P B A

/-- Original known-order finite-cyclic discrete logarithms with complete native accounting.

**Input.** The original generator has known finite order N, the target belongs
to its cyclic subgroup, and the original binary expansion has at least two
set bits. Quantum and declared classical group access use the same encoding.
The sole borrowed word is the encoded target. Every normalized local input
with that classical value and every external reference extension is admitted.
The original SecretInput identifies the target's logarithm only in the proof.
**Output.** Exactly the optional word encoding that secret residue is accepted.
The complete output retains the target, the original three-register bank,
every measured sample and the actual result. No final zero-state requirement
is imposed; full borrowed restoration is a separate mandatory obligation.
**Resources.** With t = ceil(log2(12N)), q = 2^t, the original count is
max(1,ceil(log(3)/log(4q^2/(4q^2-totient(N))))). One preparation supplies
one 3t-qubit bank. Every later sample pays for reset before the same literal
member and finite measurement. All samples precede the one result allocation
and complete classical recovery. The independent budget retains the actual
declared group calls, final pack, original parallel unit-depth allowance and
all resident and auxiliary storage, including the borrowed target.
**Success.** The required probability of the original exact answer is at least 2/3.
**Source.** [Sho95, source.tex:1704-1740,1907-1987];
[SV24, Uniform.tex:622-664,775-805,996-1024].
-/
def specification (P : KnownOrderProblem G) (input : Probability.SecretInput P)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    Problem .quantum (pre P) (outputContext P)
      (.option (.unsignedWord (orderWidth P))) where
  valid := inputDomain P A
  accepts := fun _ output => accepts input output
  successLB := successLowerBound
  states := []
  resources := resourceBudget P B A
  depth := .quantum (fun _ => 1) (unitDepthLimit P B A)

/-- Any implementation must satisfy these independently fixed bounds on each actual path. -/
structure ClosedResourceContract (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (code : Circuit (pre P) (outputContext P)) : Prop where
  /-- Every native coordinate, including the encoded query and group calls, is charged. -/
  events : ∀ path, code.resourcePool path ≤ (resourceBudget P B A).events
  /-- Actual reset alternatives are distinguished from the independent event pool. -/
  eventCount : ∀ path, (code.eventTrace path).length ≤ eventCountLimit P B A
  /-- Resident capacity includes the retained bank, all samples, result and input. -/
  resident : ∀ path, code.peakResidentSpace path ≤ (resourceBudget P B A).resident
  /-- Auxiliary capacity follows those same actual contexts and declared roles. -/
  auxiliary : ∀ path, code.peakAuxiliarySpace path ≤ (resourceBudget P B A).auxiliary
  /-- The actual unit-duration critical path obeys the original parallel-aware formula. -/
  depth : ∀ path, code.depth (fun _ => 1) path ≤ unitDepthLimit P B A

/-- The sole actual complete endpoint already meets every independent resource obligation. -/
theorem finiteCyclic_closedResourceContract (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    ClosedResourceContract P B A (run P B A).code where
  events := finiteCyclic_run_pool_le P B A
  eventCount := finiteCyclic_run_eventCount_le P B A
  resident := finiteCyclic_run_resident_le P B A
  auxiliary := finiteCyclic_run_auxiliary_le P B A
  depth := finiteCyclic_run_unitDepth_le P B A

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint.Specification
