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
    UnitaryCircuit (Qubits
      GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width) :=
  UnitaryCircuit.indexedProductNamed "ecadd-cascade" (2 * t)
    (UnitaryCircuit.identity
      (Qubits GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width)
      [] (by simp))
    (fun i => ControlledPointAddition.program E (addend i))

/-- The common carrier has the exact width of one ECADD block; sequentially
reusing it for `2 * t` blocks does not multiply the logical-qubit count. -/
theorem ecaddCascadeProgram_width_exact :
    GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width =
      ControlledPointAddition.logicalQubitCount params.width := by
  exact ControlledPointAddition.program_width_exact

omit params in
private theorem resourcePool_count_finset_sum
    {kind : ProblemKind} {Index : Type} [Fintype Index]
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
    ResourcePool.count (.gate (.builtin "toffoli"))
        (ecaddCascadeProgram E t addend).eventCost ≤
      (2 * t) * ControlledPointAddition.toffoliCountBound params.width := by
  simp only [ecaddCascadeProgram, UnitaryCircuit.indexedProductNamed_eventCost,
    UnitaryCircuit.identity_eventCost, zero_add]
  rw [resourcePool_count_finset_sum]
  calc
    (∑ i : Fin (2 * t), ResourcePool.count (.gate (.builtin "toffoli"))
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
    UnitaryCircuit.evaluatedEventDepth, UnitaryCircuit.indexedProductNamed_eventDepth,
    DepthExpr.depthEval_indexedProduct, UnitaryCircuit.identity_eventDepth,
    DepthExpr.depthEval_id, zero_add]
  calc
    (∑ i : Fin (2 * t),
        DepthExpr.depthEval (fun _ : Resource.Event .quantum => 1)
          (ControlledPointAddition.program E (addend i)).eventDepth) ≤
        ∑ _i : Fin (2 * t), ControlledPointAddition.circuitDepthBound params.width :=
      Finset.sum_le_sum fun i _ => by
        simpa only [UnitaryCircuit.evaluatedEventDepth] using
          ControlledPointAddition.program_unitDepth_le E (addend i)
    _ = (2 * t) * ControlledPointAddition.circuitDepthBound params.width := by
      simp

/-- Every actual cascade block uses the same exact ECADD carrier. -/
theorem ecaddCascadeProgram_physical_idx_subset_range
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) -> AffinePoint E) :
    (ecaddCascadeProgram E t addend).physical_idx ⊆
      List.range (ControlledPointAddition.logicalQubitCount params.width) := by
  unfold ecaddCascadeProgram UnitaryCircuit.indexedProductNamed
  apply UnitaryCircuit.foldl_unionPhysicalIdx_subset
  · simp [UnitaryCircuit.identity]
  · intro footprint hfootprint
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hfootprint
    have hwidth :
        Arithmetic.ModularInversion.physicalWidthFor params.width +
            20 * params.width + 13 =
          ControlledPointAddition.logicalQubitCount params.width :=
      GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding_width_exact.symm.trans
        ControlledPointAddition.program_width_exact
    rw [← hwidth]
    simpa only [ControlledPointAddition.program] using
      (GenericPointAddition.ExceptionalCleanup.translationProgram_physical_idx_subset_range
        (E := E) (Q := addend i))

end

end ECADDResourceCorollary
end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
