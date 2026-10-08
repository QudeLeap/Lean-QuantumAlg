/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec

/-!
# Independent P-256 scalar resource ceilings

Every number substitutes the original widths 256, 256, 260 and 4714 attempts
into the generic arithmetic formulas. These conservative implementation
ceilings retain the original preparation and native arithmetic
[PZ03, ecc.tex:448-556; SV24, Uniform.tex:622-664,996-1024]. No circuit,
resource pool, operand maximum or fixed gap table is evaluated here.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources.Limits

open LogicalResources

/-- Independent fixed qubits ceiling from generic parameter substitution. -/
@[expose] public def qubits : Nat := 1_336

theorem qubits_eq : Scalar.qubits 256 260 = qubits := by
  decide

/-- Independent fixed toffoli ceiling from generic parameter substitution. -/
@[expose] public def toffoli : Nat := 1_062_402_918_356_094_122_075_180_928

theorem toffoli_eq : 4714 * Scalar.roundToffoli 256 260 = toffoli := by
  decide

/-- Independent fixed cnot ceiling from generic parameter substitution. -/
@[expose] public def cnot : Nat := 265_600_752_358_190_509_452_117_336

theorem cnot_eq : 4714 * Scalar.roundCnot 256 260 = cnot := by
  simp only [Scalar.roundCnot, Scalar.readoutCnot, Nat.choose_two_right]
  decide

/-- Independent fixed singleQubit ceiling from generic parameter substitution. -/
@[expose] public def singleQubit : Nat := 30_358_927_906_475_193_735

theorem singleQubit_eq : Scalar.loadBits 256 + 4714 * Scalar.roundSingle 256 260 = singleQubit := by
  simp only [Scalar.roundSingle, Scalar.readoutSingle, Nat.choose_two_right]
  decide

/-- Independent fixed maximumCycleDepth ceiling from generic parameter substitution. -/
@[expose] public def maximumCycleDepth : Nat := 281_714_828_399_069_286_791_799

theorem maximumCycleDepth_eq : Scalar.maximumCycleDepth 256 256 260 = maximumCycleDepth := by
  simp only [Scalar.maximumCycleDepth, Scalar.roundEvents,
    Scalar.readoutSingle, Scalar.readoutCnot, Nat.choose_two_right]
  decide

/-- Independent fixed residentBits ceiling from generic parameter substitution. -/
@[expose] public def residentBits : Nat := 1_237_909

theorem residentBits_eq : Scalar.residentBits 256 256 260 = residentBits := by
  decide

/-- Independent fixed auxiliaryBits ceiling from generic parameter substitution. -/
@[expose] public def auxiliaryBits : Nat := 1_236_883

theorem auxiliaryBits_eq : Scalar.auxiliaryBits 256 256 260 = auxiliaryBits := by
  decide

/-- Independent fixed classicalOperations ceiling from generic parameter substitution. -/
@[expose] public def classicalOperations : Nat := 78_654_782_327

theorem classicalOperations_eq :
    4714 * Scalar.recoveryEvents 256 260 + 1 = classicalOperations := by
  decide

/-- Independent fixed wholeRunDepth ceiling from generic parameter substitution. -/
@[expose] public def wholeRunDepth : Nat := 1_328_003_701_073_212_617_921_079_174

theorem wholeRunDepth_eq : Scalar.wholeRunEvents 256 256 260 4714 = wholeRunDepth := by
  simp only [Scalar.wholeRunEvents, Scalar.roundEvents,
    Scalar.readoutSingle, Scalar.readoutCnot, Nat.choose_two_right]
  decide

end QuantumAlg.EllipticCurve.P256LogicalResources.Limits
