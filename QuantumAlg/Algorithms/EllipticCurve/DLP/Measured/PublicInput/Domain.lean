/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# The local public-input domain covers every full reference extension

Only the original two borrowed classical point values are prescribed. The
input domain imposes no quantum state, inverse, auxiliary-zero or reference
condition. Every complete input in this local domain is exactly the existing
prescribed initial input of its original unframed quantum state. The inverse
coordinates retain each full density block, including off-diagonal reference
entries; zero-mass blocks vanish by positivity. No instruction or allocation
is introduced by this mathematical input correspondence.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

/-- The independent local domain prescribes precisely the two original public point values. -/
def inputDomain (problem : KnownOrderProblem E.GroupPoint)
    (localState : ExecutionState (Store (before E exponentWidth))
      (before E exponentWidth).register) : Prop :=
  ∀ value, 0 < (localState.block value).mass →
    value.read (initialBaseRef E exponentWidth) =
        Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      value.read (initialTargetRef E exponentWidth) =
        Canonical.Runtime.Context.pointValue E problem.target.toMathlib

private theorem frame_store_eq (problem : KnownOrderProblem E.GroupPoint)
    (value : Store (frame E exponentWidth))
    (base : value.read (baseRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.generator.toMathlib)
    (target : value.read (targetRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.target.toMathlib) :
    value = store E exponentWidth problem := by
  obtain ⟨targetValue, baseValue, rest⟩ := value
  cases rest
  change baseValue = _ at base
  change targetValue = _ at target
  subst baseValue
  subst targetValue
  rfl

private theorem initialStore_split_left (problem : KnownOrderProblem E.GroupPoint)
    (value : Store (before E exponentWidth))
    (base : value.read (initialBaseRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.generator.toMathlib)
    (target : value.read (initialTargetRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.target.toMathlib) :
    initialStore E exponentWidth problem (split (before_disjoint E exponentWidth) value).1 =
      value := by
  have original := join_split_store (before_disjoint E exponentWidth) value
  have publicBase := contextUnion_read_join_right (before_disjoint E exponentWidth)
    (split (before_disjoint E exponentWidth) value).1
    (split (before_disjoint E exponentWidth) value).2 (baseRef E exponentWidth)
  have publicTarget := contextUnion_read_join_right (before_disjoint E exponentWidth)
    (split (before_disjoint E exponentWidth) value).1
    (split (before_disjoint E exponentWidth) value).2 (targetRef E exponentWidth)
  rw [original] at publicBase publicTarget
  have same := frame_store_eq E exponentWidth problem
    (split (before_disjoint E exponentWidth) value).2
    (publicBase.symm.trans base) (publicTarget.symm.trans target)
  exact (congrArg (join (before_disjoint E exponentWidth)
    (split (before_disjoint E exponentWidth) value).1) same.symm).trans original

/-- Remove only the fixed classical frame labels and reverse the exact full input coordinates. -/
def unframedState {Reference : Register}
    (state : ExecutionState (Store (before E exponentWidth))
      (Register.prod (before E exponentWidth).register Reference)) :
    ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference) :=
  (state.mapClassical (fun value => (split (before_disjoint E exponentWidth) value).1)).reindex
    (beforeJointBasisEquiv E exponentWidth Reference).symm

/-- The original complete state has exactly the incoming mass, with no normalization step. -/
theorem unframedState_mass {Reference : Register}
    (state : ExecutionState (Store (before E exponentWidth))
      (Register.prod (before E exponentWidth).register Reference)) :
    (unframedState E exponentWidth state).mass = state.mass := by
  rw [unframedState, ExecutionState.reindex_mass, ExecutionState.mapClassical_mass]

/-- Prescribing the already-correct public values restores the entire original input state. -/
theorem initialState_unframedState (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register}
    (state : ExecutionState (Store (before E exponentWidth))
      (Register.prod (before E exponentWidth).register Reference))
    (valid : ∀ value, 0 < (state.block value).mass →
      value.read (initialBaseRef E exponentWidth) =
          Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
        value.read (initialTargetRef E exponentWidth) =
          Canonical.Runtime.Context.pointValue E problem.target.toMathlib) :
    initialState E exponentWidth problem (unframedState E exponentWidth state) = state := by
  unfold initialState unframedState
  rw [ExecutionState.coordinate_reindex_mapClassical]
  refine (ExecutionState.coordinate_reindex_inverse
    ((state.mapClassical
      (fun value => (split (before_disjoint E exponentWidth) value).1)).mapClassical
        (initialStore E exponentWidth problem))
    (beforeJointBasisEquiv E exponentWidth Reference).symm).trans ?_
  rw [ExecutionState.executionState_mapClassical_comp]
  refine (ExecutionState.mapClassical_eq_of_support state _ id ?_).trans
    (ExecutionState.mapClassical_id state)
  intro value positive
  exact initialStore_split_left E exponentWidth problem value
    (valid value positive).1 (valid value positive).2

/-- The inverse complete coordinates carry normalization from the actual supplied input. -/
def unframedInput {Reference : Register} (supplied : Input (before E exponentWidth) Reference) :
    Input (Allocation.before p.size (2 * exponentWidth)) Reference where
  state := unframedState E exponentWidth supplied.state
  normalized := (unframedState_mass E exponentWidth supplied.state).trans supplied.normalized

private theorem input_eq_of_state_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} (first second : Input ctx Reference)
    (same : first.state = second.state) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Every reference extension admitted by the local domain is the prescribed complete input. -/
theorem initialInput_unframedInput (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} (supplied : Input (before E exponentWidth) Reference)
    (valid : inputDomain E exponentWidth problem supplied.localState) :
    initialInput E exponentWidth problem (unframedInput E exponentWidth supplied) = supplied := by
  apply input_eq_of_state_eq
  exact initialState_unframedState E exponentWidth problem supplied.state
    (fun value positive => valid value ((supplied.localState_block_mass value).symm ▸ positive))

/-- Every original normalized quantum input supplies an input in the independent local domain. -/
theorem inputDomain_initialInput (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference) :
    inputDomain E exponentWidth problem
      (initialInput E exponentWidth problem original).localState := by
  intro value positive
  rw [Input.localState_block_mass] at positive
  obtain ⟨source, equality, _⟩ := initialState_supported_original E exponentWidth problem
    original.state value positive
  rw [← equality]
  exact ⟨initialStore_base E exponentWidth problem source,
    initialStore_target E exponentWidth problem source⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
