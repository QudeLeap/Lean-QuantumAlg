/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Reuse

/-!
# Inactive complete inversion on the physically reused Y workspace

The normal selector may be false with zero, arbitrary original words,
and arbitrary finite small history. The physical reuse retains the
whole original pool, internal selector and C/N/W. Both the actual placed
forward and its literal adjoint preserve every admitted complete label.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse

noncomputable section

lemma forward_apply_disabled (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (state : ControlledResidentFrame.Data modulus.size)
    (prefixZero : state.1.1.2.2.1 = 0) (addressZero : state.1.1.2.1 = 0)
    (borrowZero : state.1.1.2.2.2 = false) (control : state.1.1.1.control = false)
    (disabled : state.2.2.1 = false) :
    (forward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode state)) := by
  let source : ControlledResidentFrame.Data modulus.size :=
    ((WorkspaceReuse.placement modulus.size).grouping state.1, state.2)
  have pool := WorkspaceReuse.grouping_pool modulus.size state.1
  have actual := ControlledResidentNormal.program_apply_disabled modulus nontrivial environment
    source ((congrArg (fun value => value.2.1) pool).trans prefixZero)
    ((congrArg Prod.fst pool).trans addressZero)
    ((congrArg (fun value => value.2.2) pool).trans borrowZero)
    ((WorkspaceReuse.grouping_control modulus.size state.1).trans control) disabled
  have placed := (layout modulus.size).place_ket_of_eq _ _ _ actual
  have restored : (layout modulus.size).grouping.symm source = state := by
    apply (layout modulus.size).grouping.injective
    rw [Equiv.apply_symm_apply]
    rfl
  simpa only [forward, restored] using placed

lemma backward_apply_disabled (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (state : ControlledResidentFrame.Data modulus.size)
    (prefixZero : state.1.1.2.2.1 = 0) (addressZero : state.1.1.2.1 = 0)
    (borrowZero : state.1.1.2.2.2 = false) (control : state.1.1.1.control = false)
    (disabled : state.2.2.1 = false) :
    (backward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode state)) := by
  have actual := forward_apply_disabled modulus nontrivial environment state prefixZero
    addressZero borrowZero control disabled
  exact (congrArg (fun value => (backward modulus nontrivial).applyNormalized environment value)
      actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (forward modulus nontrivial) (backward modulus nontrivial)
      (by
        rw [backward, UnitaryCircuit.dagger_matrix,
          Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
            environment]
        exact Unitary.star_eq_inv _) _)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse
