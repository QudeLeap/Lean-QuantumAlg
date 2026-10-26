/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Coefficient.Runtime
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Native.Resources

/-!
# Toffolis of the paid coherent coefficient-phase selection

The three actual metadata add/subtract calls and their native dirty-work
control lowerings determine the count. Public constant loads become
CNOTs, and the two negative-control masks are X instructions. This is
a component count, not a complete arithmetic microstep resource claim.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit

/-- One actual retained-control word turns source CNOTs into one and Toffolis into four. -/
lemma phaseControlledGates_toffoli_count (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    ((phaseControlledGates width positive deshift).map GateSpec.toffoliMultiplicity).sum =
      (if deshift then 2 else 1) *
        (fullWidth width + 2 * (fullWidth width - 1) + 2 * (fullWidth width - 2) +
          8 * (fullWidth width - 1)) := by
  rw [phaseControlledGates, GateSpec.listWithDirtyControl_toffoliMultiplicity_sum,
    nativeCoefficientGates_cnot_count, nativeCoefficientGates_toffoli_count]
  cases deshift <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- Both actual phase words execute in the source circuit, including their full control overhead. -/
lemma runtimeCoefficientGates_toffoli_count (width : Nat) (positive : 1 ≤ width) :
    ((runtimeCoefficientGates width positive).map GateSpec.toffoliMultiplicity).sum =
      3 * (fullWidth width + 2 * (fullWidth width - 1) + 2 * (fullWidth width - 2) +
        8 * (fullWidth width - 1)) := by
  simp only [runtimeCoefficientGates, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, GateSpec.toffoliMultiplicity, phaseControlledGates_toffoli_count,
    Bool.false_eq_true, if_false, if_true]
  omega

/-- The same actual emitted program, rather than an independent formula, owns its Toffoli count. -/
lemma runtimeCoefficientProgram_toffoli_count (width : Nat) (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (runtimeCoefficientProgram width positive).eventCost =
      3 * (fullWidth width + 2 * (fullWidth width - 1) + 2 * (fullWidth width - 2) +
        8 * (fullWidth width - 1)) := by
  rw [runtimeCoefficientProgram, GateSpec.programList_toffoli_count_eq_sum,
    runtimeCoefficientGates_toffoli_count]

/-- P-256 metadata geometry uses exactly 387 Toffolis for this complete paid phase selection. -/
lemma runtimeCoefficientProgram_p256_toffoli :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (runtimeCoefficientProgram 256 (by decide)).eventCost = 387 := by
  rw [runtimeCoefficientProgram_toffoli_count]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
