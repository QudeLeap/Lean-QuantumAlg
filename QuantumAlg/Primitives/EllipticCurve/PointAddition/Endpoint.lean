/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Specification
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Specification
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Context
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Execution
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Core.Execution.Trace

/-!
# Elliptic-curve point addition

The clean generic domain, controlled mathematical translation, full reference
state and independent native/space/time bounds belong to the problem. The
existence theorem supplies one complete actual algorithm meeting that contract.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition
noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

/-- **Input.** A density supported on clean controlled affine encodings with P distinct
from Q and -Q, extended by an arbitrary reference.
**Output.** The complete live register after the bit-selected group shift; all auxiliary
storage is restored to its clean encoding.
**Resource budget.** The published Toffoli bound, independent native CNOT/depth bounds,
37f+27+3h resident qubits and 35f+26+3h owned auxiliary qubits.
**Success.** Exact full joint-reference action with probability one.
**Source.** [RNSL17, ECDLP.tex:494-555, Algorithm 1] and [PZ03, ecc.tex:559-640]. -/
@[expose] public def problem (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    Problem Execution.model (Execution.context params.width)
      (Execution.context params.width) .unit where
  Witness := Unit
  valid := fun _ _ => Execution.valid E Q
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [StateRequirement.unitary (Execution.semanticOperator E Q)]
  resources := Execution.resources
  quantumTimeLimit := circuitDepthBound params.width

/-- One complete native controlled point-addition algorithm solves the independent clean domain. -/
public theorem main (hcharacteristic : 3 < params.modulus.val)
    (hfieldWidth : params.width = Nat.clog 2 params.modulus.val)
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    ∃ algorithm : Algorithm Execution.model (Execution.context params.width)
        (Execution.context params.width) .unit,
      algorithm.Solves (problem E Q) := by
  refine ⟨Execution.algorithm E Q, ?_⟩
  constructor
  · intro environment _witness Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input allowed _initialization requirement present
    have sameRequirement :
        requirement = StateRequirement.unitary (Execution.semanticOperator E Q) :=
      List.mem_singleton.mp present
    subst requirement
    exact Execution.actual_state (environment := environment) E Q input allowed
  · intro environment _witness Reference input _valid _initialization
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment rfl rfl
      (Execution.program E Q) (Output.all (Execution.context params.width) .unit) input
  · intro environment _witness _Reference _input _valid _initialization path _supported
    change ResourcePool.ofList (Execution.program E Q).eventTrace ≤
      (Execution.resources (params := params)).events
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
    exact Execution.actual_events E hcharacteristic hfieldWidth Q
  · intro environment _witness _Reference _input _valid _initialization path _supported axis
    change Nat.max ((Execution.context params.width).residentSpace axis) 0 ≤
      QuantumAlg.Execution.SuppliedQubits.space (logicalQubitCount params.width) axis
    rw [Execution.context_resident]
    exact le_of_eq ((Nat.max_eq_max _).trans (Nat.max_zero _))
  · intro environment _witness _Reference _input _valid _initialization path _supported axis
    change Nat.max ((Execution.context params.width).auxiliarySpace axis) 0 ≤
      QuantumAlg.Execution.SuppliedQubits.space (auxiliaryQubitCount params.width) axis
    rw [Execution.context_auxiliary]
    exact le_of_eq ((Nat.max_eq_max _).trans (Nat.max_zero _))
  · intro environment _witness _Reference _input _valid _initialization path _supported
    exact Execution.actual_time E Q

end
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition
