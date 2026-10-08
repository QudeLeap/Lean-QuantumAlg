/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit.Space
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint

/-!
# Resource corollary for a controlled-ECADD cascade

This module records the resource-only sequential composition of a fixed number
of controlled elliptic-curve point-addition blocks over one shared logical
carrier.  It deliberately does not state a scalar-action semantic theorem:
that requires a separately supplied per-step generic-domain witness.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ScalarMultiplication
namespace ECADDResourceCorollary

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

variable {E : PrimeFieldShortWeierstrass params.modulus.val}

/-- The actual shared-carrier circuit obtained by sequencing `2 * t` canonical
controlled-ECADD programs. -/
def ecaddCascadeProgram (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) -> AffinePoint E) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width).toQuantum :=
  UnitaryCircuit.indexedProduct "ecadd-cascade" (2 * t)
    (UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical
        GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width).toQuantum)
    (fun i => ControlledPointAddition.program E (addend i))

/-- The common carrier has the exact width of one ECADD block; sequentially
reusing it for `2 * t` blocks does not multiply the logical-qubit count. -/
theorem ecaddCascadeProgram_width_exact :
    GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width =
      ControlledPointAddition.logicalQubitCount params.width := by
  exact ControlledPointAddition.program_width_exact

omit params in
private theorem resourcePool_count_finset_sum
    {kind : ExecutionModel} {Index : Type} [Fintype Index]
    (focus : Resource.Event kind) (pool : Index -> ResourcePool kind) :
    ResourcePool.count focus (∑ index, pool index) =
      ∑ index, ResourcePool.count focus (pool index) := by
  classical
  have aux : ∀ indices : Finset Index,
      ResourcePool.count focus (∑ index ∈ indices, pool index) =
        ∑ index ∈ indices, ResourcePool.count focus (pool index) := by
    intro indices
    induction indices using Finset.induction with
    | empty => simp
    | @insert index rest hindex ih =>
        simp [Finset.sum_insert, hindex, ResourcePool.count_add, ih]
  simpa using aux Finset.univ

/-- The Toffoli count of the actual cascade is at most one width-only ECADD
bound for each of its `2 * t` stored blocks. -/
theorem ecaddCascadeProgram_toffoli_count_le
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) -> AffinePoint E) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (ecaddCascadeProgram E t addend).eventCost ≤
      (2 * t) * ControlledPointAddition.toffoliCountBound params.width := by
  simp only [ecaddCascadeProgram, UnitaryCircuit.indexedProduct_eventCost,
    UnitaryCircuit.identity_eventCost, zero_add]
  rw [resourcePool_count_finset_sum]
  calc
    (∑ i : Fin (2 * t),
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.toffoli)
        (ControlledPointAddition.program E (addend i)).eventCost) ≤
        ∑ _i : Fin (2 * t), ControlledPointAddition.toffoliCountBound params.width :=
      Finset.sum_le_sum fun i _ =>
        ControlledPointAddition.program_toffoli_count_le E (addend i)
    _ = (2 * t) * ControlledPointAddition.toffoliCountBound params.width := by
      simp

/-- The sequential unit-gate depth of the actual cascade is at most one
width-only ECADD depth bound for each of its `2 * t` stored blocks. -/
theorem ecaddCascadeProgram_unitDepth_le
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) -> AffinePoint E) :
    (ecaddCascadeProgram E t addend).evaluatedEventDepth (fun _ => 1) ≤
      (2 * t) * ControlledPointAddition.circuitDepthBound params.width := by
  simp only [ecaddCascadeProgram,
    UnitaryCircuit.evaluatedEventDepth, UnitaryCircuit.indexedProduct_eventDepth,
    DepthExpr.depthEval_indexedProduct, UnitaryCircuit.identity_eventDepth,
    DepthExpr.depthEval_id, zero_add]
  calc
    (∑ i : Fin (2 * t),
        DepthExpr.depthEval
          (fun _ : Resource.Event (.quantum AlgorithmGate.model .empty) => 1)
          (ControlledPointAddition.program E (addend i)).eventDepth) ≤
        ∑ _i : Fin (2 * t), ControlledPointAddition.circuitDepthBound params.width :=
      Finset.sum_le_sum fun i _ => by
        simpa only [UnitaryCircuit.evaluatedEventDepth] using
          ControlledPointAddition.program_unitDepth_le E (addend i)
    _ = (2 * t) * ControlledPointAddition.circuitDepthBound params.width := by
      simp

end

end ECADDResourceCorollary
end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
