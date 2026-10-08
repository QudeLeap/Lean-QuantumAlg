/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QubitPrimitive.Placement
public import QuantumAlg.Components.GateModel.Algorithm.Permutation
public import QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Components.QubitPrimitive.Placement
import all QuantumAlg.Components.GateModel.Algorithm.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Permutation

/-!
# Exact native action and the untouched joint complement

The actual native application induces its declared local permutation on the
addressed arguments. Its full ambient operator preserves every complementary
coordinate, with exact phase and without a separate semantic witness supplied
by the caller.
-/

namespace QuantumAlg.QubitPrimitive

noncomputable section

/-- The fixed local permutation belonging to the primitive's actual native token. -/
@[expose]
public def nativeLocalPermutation {n : Nat} (primitive : QubitPrimitive n) :
    Equiv.Perm (AlgorithmGate.model.signature (nativeToken primitive)).Basis :=
  match primitive with
  | .x _ => AlgorithmGate.xPermutation
  | .cnot _ _ _ => AlgorithmGate.cnotPermutation
  | .toffoli _ _ _ _ _ _ => AlgorithmGate.toffoliPermutation

/-- The same model token determines both the local permutation and its full operator. -/
public theorem nativeLocalPermutation_operator {n : Nat} (primitive : QubitPrimitive n) :
    AlgorithmGate.model.operator (nativeToken primitive) =
      UnitaryOperator.ofPerm (nativeLocalPermutation primitive) := by
  cases primitive with
  | x _ => exact AlgorithmGate.x_operator_ofPerm
  | cnot _ _ _ => exact AlgorithmGate.cnot_operator_ofPerm
  | toffoli _ _ _ _ _ _ => exact AlgorithmGate.toffoli_operator_ofPerm

/-- The same local permutation in the placed application's dependent signature. -/
@[expose]
public def nativePlacedPermutation {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) :
    Equiv.Perm
      (AlgorithmGate.model.signature (nativeApplication layout primitive).occurrence.token).Basis :=
  match primitive with
  | .x _ => AlgorithmGate.xPermutation
  | .cnot _ _ _ => AlgorithmGate.cnotPermutation
  | .toffoli _ _ _ _ _ _ => AlgorithmGate.toffoliPermutation

/-- The physical basis action changes only the addressed argument coordinates. -/
@[expose]
public def nativeAmbientPermutation {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) : Equiv.Perm layout.toQuantum.Basis :=
  (nativeApplication layout primitive).liftPermutation (nativePlacedPermutation layout primitive)

/-- Exact ambient operator of each placed primitive, including all unused systems. -/
public theorem nativeApplication_operator_ofPerm {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) :
    (nativeApplication layout primitive).operator =
      UnitaryOperator.ofPerm (nativeAmbientPermutation layout primitive) := by
  apply GateModel.Application.operator_ofPerm
  cases primitive with
  | x _ => exact AlgorithmGate.x_operator_ofPerm
  | cnot _ _ _ => exact AlgorithmGate.cnot_operator_ofPerm
  | toffoli _ _ _ _ _ _ => exact AlgorithmGate.toffoli_operator_ofPerm

/-- The complete joint complement is unchanged by the actual native permutation. -/
public theorem nativeAmbientPermutation_basis {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) (basis : layout.toQuantum.Basis) :
    (nativeApplication layout primitive).basisEquiv
        (nativeAmbientPermutation layout primitive basis) =
      (nativePlacedPermutation layout primitive
        ((nativeApplication layout primitive).basisEquiv basis).1,
        ((nativeApplication layout primitive).basisEquiv basis).2) := by
  exact (nativeApplication layout primitive).basisEquiv.apply_symm_apply _

end

end QuantumAlg.QubitPrimitive
