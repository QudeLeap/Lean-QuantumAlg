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
@[expose] public def qubits : Nat := 818

lemma qubits_eq : Scalar.streamingQubits 256 = qubits := by
  decide

/-- Independent fixed toffoli ceiling from generic parameter substitution. -/
@[expose] public def toffoli : Nat := 531_202_041_321_957_512_921_829_248

lemma toffoli_eq : 4714 * Scalar.roundToffoli 256 260 = toffoli := by
  decide

/-- Independent fixed cnot ceiling from generic parameter substitution. -/
@[expose] public def cnot : Nat := 132_800_533_099_656_357_163_779_416

lemma cnot_eq : 4714 * Scalar.roundCnot 256 260 = cnot := by
  simp only [Scalar.roundCnot, Scalar.readoutCnot, Nat.choose_two_right]
  decide

/-- Independent fixed singleQubit ceiling from generic parameter substitution. -/
@[expose] public def singleQubit : Nat := 30_358_927_906_475_193_735

lemma singleQubit_eq : Scalar.loadBits 256 + 4714 * Scalar.roundSingle 256 260 = singleQubit := by
  simp only [Scalar.roundSingle, Scalar.readoutSingle, Nat.choose_two_right]
  decide

/-- Independent fixed residentBits ceiling from generic parameter substitution. -/
@[expose] public def residentBits : Nat := 1_237_909

lemma residentBits_eq : Scalar.residentBits 256 256 260 = residentBits := by
  decide

/-- Independent fixed auxiliaryBits ceiling from generic parameter substitution. -/
@[expose] public def auxiliaryBits : Nat := 1_236_883

lemma auxiliaryBits_eq : Scalar.auxiliaryBits 256 256 260 = auxiliaryBits := by
  decide

/-- Independent fixed classicalOperations ceiling from generic parameter substitution. -/
@[expose] public def classicalOperations : Nat := 78_654_782_327

lemma classicalOperations_eq :
    4714 * Scalar.recoveryEvents 256 260 + 1 = classicalOperations := by
  decide

/-- Independent canonical quantum-time ceiling for 4714 reset/sampling attempts. -/
@[expose] public def quantumTime : Nat := 664_002_604_780_313_720_248_530_788

lemma quantumTime_eq : Scalar.quantumTime 256 260 4714 = quantumTime := by
  decide

/-- Independent fixed wholeRunDepth ceiling from generic parameter substitution. -/
@[expose] public def wholeRunDepth : Nat := 664_002_604_780_541_856_479_389_574

lemma wholeRunDepth_eq : Scalar.wholeRunEvents 256 256 260 4714 = wholeRunDepth := by
  simp only [Scalar.wholeRunEvents, Scalar.roundEvents,
    Scalar.readoutSingle, Scalar.readoutCnot, Nat.choose_two_right]
  decide

end QuantumAlg.EllipticCurve.P256LogicalResources.Limits
