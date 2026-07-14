/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Core.Trainability
public import QuantumAlg.Primitives.QNN.Algebras.SingleQubitDLA
public import QuantumAlg.Primitives.QNN.Algebras.PauliStringSchur

/-!
# Concrete witnesses for trainability interfaces

This module records small adapter witnesses showing that the abstract trainability
interfaces are inhabited by already-formalized QNN families. The adapters reuse existing
variance theorems; they do not introduce new variance mathematics.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

/-- The local `su(2)^{⊕n}` single-qubit-DLA family instantiates the geometric-QML
trainability interface. The family index `m` denotes an `(m + 1)`-qubit register, so
the constant variance theorem applies for every index while avoiding the empty register. -/
def singleQubitDLAGeometricQMLTrainable : GeometricQMLTrainable where
  variance := fun m => (rLocal (n := m + 1) (Nat.succ_pos m)).variance
  c := 1 / 3
  c_pos := by norm_num
  deg := 0
  variance_lb := by
    intro m _hm
    rw [localObs_totalVariance_eq (Nat.succ_pos m)]
    norm_num

/-- Interface-level local/global cost witness: the local side is the single-qubit-DLA
constant-variance family, while the global side is the Schur-discharged `su(2^n)`
consistency-witness sequence. This packages existing endpoints into `CostDependentBP`;
it does not claim a single physical finite-twirl circuit family realizes both sides. -/
def singleQubitLocalSuNGlobalCostDependentBP : CostDependentBP where
  globalVariance := fun m => (suSM m (suHermBasis_schur (m + 1))).variance
  localVariance := fun m => (rLocal (n := m + 1) (Nat.succ_pos m)).variance
  c := 1 / 3
  c_pos := by norm_num
  global_bp := suN_hasBarrenPlateau_schurDischarged
  local_lb := by
    intro m hm
    rw [localObs_totalVariance_eq (Nat.succ_pos m)]
    have hm_ge : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
    calc
      (1 / 3 : ℝ) / (m : ℝ) ≤ (1 / 3 : ℝ) / 1 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm_ge
      _ = 1 / 3 := by norm_num

end

end QuantumAlg
