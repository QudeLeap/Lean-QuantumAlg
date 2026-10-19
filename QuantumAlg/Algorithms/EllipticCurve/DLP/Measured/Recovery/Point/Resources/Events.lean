/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Execution
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Resources
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources

/-!
# Complete native event pools of the literal fixed point body

Every bound concerns the seven existing allocation-free FixedPoint definitions
and the same complete syntactic Path. The actual Hadamard layer, ordered
measurements and selected X corrections obey the original numerator allowance.
Both physical embeddings retain the child's events exactly. The selected
controlled suffix and five point stages then satisfy the original independent
native-coordinate budgets.

No old allocating point or arithmetic body is executed, converted or used as
an alternative run. Only the existing native-word costs and independent budget
formulas are reused. These bounds require no input state, cleanup, positive
mass, valid affine denominator or sampling-success premise. Zero widths and
every branch outcome remain quantified.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Events

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

/-- The actual H layer, ordered Z writes and selected X layer pay the original full allowance. -/
lemma numeratorReset_budget (width : Nat) (path : (numeratorReset width).Path) :
    (numeratorReset width).resourcePool path ≤ NumeratorReset.budget width := by
  have first := NumeratorReset.hadamard_cost width path.1
  change ResourcePool.ofList
    (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).eventTrace = _ at first
  have measured := Circuit.measurementSequence_qubit_resourcePool (allowAllocation := false)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty) (NumeratorMeasurement.readouts width)
    (by
      intro item present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
      exact NumeratorMeasurement.wire_dimension width index) path.2.1
  have measuredExact :
      (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (NumeratorMeasurement.readouts width)).resourcePool path.2.1 =
      width • ResourcePool.singleton
        (Circuit.zEvent (gates := AlgorithmGate.model) (oracles := .empty) 2 .empty .empty) := by
    simpa only [NumeratorMeasurement.readouts, QubitReadouts.readouts, List.length_ofFn]
      using measured
  have last := NumeratorReset.reset_budget width path.2.2
  change ResourcePool.ofList
    (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).eventTrace ≤ _
      at last
  change ResourcePool.ofList
    ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).eventTrace ++
      ((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (NumeratorMeasurement.readouts width)).eventTrace path.2.1 ++
        (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).eventTrace)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add first.le (add_le_add measuredExact.le last)

/-- The literal placed controlled word emits exactly its original native event multiplicities. -/
lemma controlledNative_pool (width : Nat) (native : InPlaceControlled.NativeCircuit width)
    (path : (controlledNative width native).Path) :
    (controlledNative width native).resourcePool path = native.eventCost := by
  change ResourcePool.ofList (InPlaceControlled.runtimeProgram width native).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, InPlaceControlled.runtimeProgram_cost]

/-- The actual reset embedding preserves every child gate and measurement on the same Path. -/
lemma controlledReset_budget (width : Nat) (path : (controlledReset width).Path) :
    (controlledReset width).resourcePool path ≤ NumeratorReset.budget width := by
  have embedded := Circuit.resourcePool_embed (allowAllocation := false)
    (ContextEmbedding.alongUnion (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width))
    (numeratorReset width) path
  exact embedded.le.trans (numeratorReset_budget width path)

/-- The actual selected arithmetic suffix pays its original outcome-dependent native budget. -/
lemma controlledBody_budget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (controlledBody operation modulus prime).Path) :
    (controlledBody operation modulus prime).resourcePool path ≤
      InPlaceControlled.events operation modulus.size := by
  change ResourcePool.ofList
    ((controlledNative modulus.size
      (InPlaceControlled.beforeReset operation modulus prime)).eventTrace path.1 ++
      ((controlledReset modulus.size).eventTrace path.2.1 ++
        (controlledNative modulus.size
          (InPlaceControlled.suffix operation modulus prime path.2.2.1)).eventTrace
            path.2.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  unfold InPlaceControlled.events
  exact add_le_add
    ((controlledNative_pool _ _ _).le.trans
      (InPlaceControlled.beforeReset_budget operation modulus prime))
    (add_le_add (controlledReset_budget modulus.size path.2.1)
      ((controlledNative_pool _ _ _).le.trans
        (InPlaceControlled.suffix_budget operation modulus prime path.2.2.1)))

/-- Each literal placed point word retains exactly its original native event multiplicities. -/
lemma pointNative_pool (width : Nat) (native : MeasuredPointAddition.NativeCircuit width)
    (path : (pointNative width native).Path) :
    (pointNative width native).resourcePool path = native.eventCost := by
  change ResourcePool.ofList (MeasuredPointAddition.runtimeProgram width native).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, MeasuredPointAddition.runtimeProgram_cost]

/-- The second actual embedding keeps all measured arithmetic events beside the resident N. -/
lemma pointArithmetic_budget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (pointArithmetic operation modulus prime).Path) :
    (pointArithmetic operation modulus prime).resourcePool path ≤
      InPlaceControlled.events operation modulus.size := by
  have embedded := Circuit.resourcePool_embed (allowAllocation := false)
    (ContextEmbedding.alongUnion (InPlaceControlled.context modulus.size)
      (MeasuredPointAddition.selectorContext modulus.size)
      (MeasuredPointAddition.selector_disjoint modulus.size))
    (controlledBody operation modulus prime) path
  exact embedded.le.trans (controlledBody_budget operation modulus prime path)

private lemma five_pool_bounds {model : ExecutionModel}
    {first second third fourth fifth : ResourcePool model}
    {firstLimit secondLimit thirdLimit fourthLimit fifthLimit : ResourcePool model}
    (firstBound : first ≤ firstLimit) (secondBound : second ≤ secondLimit)
    (thirdBound : third ≤ thirdLimit) (fourthBound : fourth ≤ fourthLimit)
    (fifthBound : fifth ≤ fifthLimit) :
    first + (second + (third + (fourth + fifth))) ≤
      firstLimit + (secondLimit + (thirdLimit + (fourthLimit + fifthLimit))) :=
  add_le_add firstBound (add_le_add secondBound
    (add_le_add thirdBound (add_le_add fourthBound fifthBound)))

private lemma point_native_budget (width : Nat)
    (native : MeasuredPointAddition.NativeCircuit width)
    (budget : ResourcePool (.quantum AlgorithmGate.model .empty))
    (bounded : native.eventCost ≤ budget) (path : (pointNative width native).Path) :
    (pointNative width native).resourcePool path ≤ budget :=
  (pointNative_pool width native path).le.trans bounded

attribute [local irreducible] MeasuredPointAddition.beforeDivision
  MeasuredPointAddition.beforeMultiplication MeasuredPointAddition.afterMultiplication
  MeasuredPointAddition.beforeBudget MeasuredPointAddition.middleBudget
  MeasuredPointAddition.afterBudget

/-- All five actual point stages obey the original complete gate-and-measurement allowance. -/
lemma pointBody_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (pointBody E Q).Path) :
    (pointBody E Q).resourcePool path ≤ MeasuredPointAddition.events p.size := by
  change ResourcePool.ofList
    ((pointNative p.size (MeasuredPointAddition.beforeDivision Q)).eventTrace path.1 ++
      ((pointArithmetic .division p Fact.out).eventTrace path.2.1 ++
        ((pointNative p.size (MeasuredPointAddition.beforeMultiplication Q)).eventTrace
          path.2.2.1 ++
          ((pointArithmetic .multiplication p Fact.out).eventTrace path.2.2.2.1 ++
            (pointNative p.size (MeasuredPointAddition.afterMultiplication E Q)).eventTrace
              path.2.2.2.2)))) ≤ _
  simp only [ResourcePool.ofList_append]
  unfold MeasuredPointAddition.events
  exact five_pool_bounds
    (point_native_budget p.size (MeasuredPointAddition.beforeDivision Q)
      (MeasuredPointAddition.beforeBudget p.size) (MeasuredPointAddition.beforeDivision_budget Q)
      path.1)
    (pointArithmetic_budget .division p Fact.out path.2.1)
    (point_native_budget p.size (MeasuredPointAddition.beforeMultiplication Q)
      (MeasuredPointAddition.middleBudget p.size)
      (MeasuredPointAddition.beforeMultiplication_budget Q) path.2.2.1)
    (pointArithmetic_budget .multiplication p Fact.out path.2.2.2.1)
    (point_native_budget p.size (MeasuredPointAddition.afterMultiplication E Q)
      (MeasuredPointAddition.afterBudget p.size)
      (MeasuredPointAddition.afterMultiplication_budget E Q) path.2.2.2.2)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Events
