/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QubitPrimitive.Semantics
import all QuantumAlg.Components.QubitPrimitive.Semantics
import all QuantumAlg.Components.QubitPrimitive.Placement
import all QuantumAlg.Components.GateModel.Algorithm.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Layout.Qubit

/-!
# Addressed native permutations on binary coordinates

The finite binary action changes the target coordinate using the original
control values. The physical native application implements that same action
on the complete register, including every coordinate outside its footprint.
-/

namespace QuantumAlg.QubitPrimitive

noncomputable section

/-- The addressed reversible action on ordered binary coordinate values. -/
@[expose]
public def basisAction {n : Nat} (primitive : QubitPrimitive n)
    (basis : Fin n → Fin 2) : Fin n → Fin 2 :=
  match primitive with
  | .x target => Function.update basis target (basis target + 1)
  | .cnot control target _ => Function.update basis target (basis control + basis target)
  | .toffoli first second target _ _ _ =>
      Function.update basis target (basis first * basis second + basis target)

private theorem complement_avoids {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n)
    (outside : QuantumLayout.SelectedPosition
      (nativeApplication layout primitive).embedding.selectionᶜ)
    (argument : Fin
      (AlgorithmGate.model.signature
        (nativeApplication layout primitive).occurrence.token).systemCount) :
    outside.val ≠ (nativeApplication layout primitive).embedding.position argument := by
  intro same
  apply (Finset.mem_compl.mp outside.property)
  rw [same]
  exact Finset.mem_map_of_mem _ (Finset.mem_univ _)

/-- The exact physical permutation agrees with the original ordered binary action. -/
public theorem nativeAmbientPermutation_apply {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) (basis : Fin n → Fin 2) :
    nativeAmbientPermutation layout primitive basis = basisAction primitive basis := by
  apply ((nativeApplication layout primitive).liftPermutation_eq_iff
    (nativePlacedPermutation layout primitive) basis (basisAction primitive basis)).mpr
  cases primitive with
  | x target =>
      have localReads (values : Fin n → Fin 2) :
          ((nativeApplication layout (.x target)).basisEquiv values).1 = ![values target] := by
        funext index
        fin_cases index
        apply Fin.ext
        rfl
      constructor
      · refine ((congrArg AlgorithmGate.xPermutation (localReads basis)).trans
          (AlgorithmGate.xPermutation_single (basis target))).trans ?_
        have updated := (localReads (basisAction (.x target) basis)).symm
        simp only [basisAction, Function.update_self] at updated
        exact updated
      · funext outside
        change basis outside.val = (basisAction (.x target) basis) outside.val
        exact (Function.update_of_ne
          (complement_avoids layout (.x target) outside (0 : Fin 1)) _ _).symm
  | cnot control target distinct =>
      have localReads (values : Fin n → Fin 2) :
          ((nativeApplication layout (.cnot control target distinct)).basisEquiv values).1 =
            ![values control, values target] := by
        funext index
        fin_cases index <;> (apply Fin.ext; rfl)
      constructor
      · refine ((congrArg AlgorithmGate.cnotPermutation (localReads basis)).trans
          (AlgorithmGate.cnotPermutation_pair (basis control) (basis target))).trans ?_
        have updated := (localReads (basisAction (.cnot control target distinct) basis)).symm
        simp only [basisAction, Function.update_self, Function.update_of_ne distinct] at updated
        exact updated
      · funext outside
        change basis outside.val = (basisAction (.cnot control target distinct) basis) outside.val
        exact (Function.update_of_ne
          (complement_avoids layout (.cnot control target distinct) outside (1 : Fin 2)) _ _).symm
  | toffoli first second target distinct firstTarget secondTarget =>
      have localReads (values : Fin n → Fin 2) :
          ((nativeApplication layout
            (.toffoli first second target distinct firstTarget secondTarget)).basisEquiv values).1 =
              ![values first, values second, values target] := by
        funext index
        fin_cases index <;> (apply Fin.ext; rfl)
      constructor
      · refine ((congrArg AlgorithmGate.toffoliPermutation (localReads basis)).trans
          (AlgorithmGate.toffoliPermutation_triple
            (basis first) (basis second) (basis target))).trans ?_
        have updated := (localReads (basisAction
          (.toffoli first second target distinct firstTarget secondTarget) basis)).symm
        simp only [basisAction, Function.update_self,
          Function.update_of_ne firstTarget, Function.update_of_ne secondTarget] at updated
        exact updated
      · funext outside
        change basis outside.val =
          (basisAction (.toffoli first second target distinct firstTarget secondTarget)
            basis) outside.val
        exact (Function.update_of_ne
          (complement_avoids layout
            (.toffoli first second target distinct firstTarget secondTarget)
            outside (2 : Fin 3)) _ _).symm

end

end QuantumAlg.QubitPrimitive
