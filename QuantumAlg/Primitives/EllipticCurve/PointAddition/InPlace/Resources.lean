/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Correction
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Schedule

/-!
# Closed resources for the in-place point-addition schedule

The bounds in this module are derived from the same native X/CNOT/Toffoli
list that realizes the seventeen-stage schedule.  The formulas are deliberately
independent of public-point bit patterns: each constant xor is bounded by its
word width.  Toffoli count is bounded by total native leaves, while the strict
sequential unit-depth is exactly that leaf count.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace Resources

noncomputable section

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- Public-constant-independent compact-inversion leaf bound. -/
def inversionGateBound (fieldWidth counterTail : Nat) : Nat :=
  234 * fieldWidth * fieldWidth +
    488 * fieldWidth * (fieldWidth - 1) +
      92 * fieldWidth * counterTail + 848 * fieldWidth + 65

/-- Closed leaf bound for one width-neutral Montgomery multiplication. -/
def multiplicationGateBound (fieldWidth : Nat) : Nat :=
  fieldWidth * (282 * fieldWidth + 89)

/-- Closed leaf bound for the complete seventeen-stage point addition. -/
def pointAdditionGateBound (fieldWidth counterTail : Nat) : Nat :=
  6272 * fieldWidth ^ 2 + 3669 * fieldWidth +
    368 * fieldWidth * counterTail + 528

theorem normalizeGates_length_le
    (fieldWidth counterWidth p : Nat) (hp : p < 2 ^ fieldWidth) :
    (MontgomeryOperations.normalizeGates fieldWidth counterWidth p hp).length ≤
      2 * fieldWidth + 1 := by
  have hu := EncodedBit.Word.constantOneIndices_length_le
    (MontgomeryOperations.modulusWord fieldWidth p hp)
  have hs := EncodedBit.Word.constantOneIndices_length_le
    (MontgomeryOperations.coefficientNormalizationWord fieldWidth p hp)
  simp only [MontgomeryOperations.normalizeGates, List.length_append,
    List.length_cons, List.length_nil,
    EncodedBit.Word.xorConstantGates_length]
  omega

theorem inverseScaleGates_length_le
    (fieldTail counterWidth p rounds : Nat) :
    (MontgomeryMultiplication.inverseScaleGates fieldTail counterWidth p
      rounds).length ≤ rounds * (57 * fieldTail.succ + 22) := by
  induction rounds with
  | zero => simp [MontgomeryMultiplication.inverseScaleGates]
  | succ rounds ih =>
      simp only [MontgomeryMultiplication.inverseScaleGates,
        List.length_append, List.length_reverse]
      calc
        _ ≤ rounds * (57 * fieldTail.succ + 22) +
            (57 * fieldTail.succ + 22) :=
          Nat.add_le_add ih
            (CompactCorrection.doublingGates_length_le fieldTail
              counterWidth p)
        _ = (rounds + 1) * (57 * fieldTail.succ + 22) := by
          rw [Nat.add_mul, one_mul, Nat.add_comm]

theorem selectedAddGates_length_le
    (fieldTail counterWidth p : Nat) (bit : Fin fieldTail.succ) :
    (MontgomeryMultiplication.selectedAddGates fieldTail counterWidth p
      bit).length ≤ 3 * (56 * fieldTail.succ + 15) := by
  have hcontrol :=
    EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
      (Layout.mutableYBit fieldTail.succ counterWidth bit)
      (Layout.liftArithmeticBit fieldTail.succ counterWidth
        (MK.Compact.pathBit fieldTail.succ counterWidth))
      (MontgomeryMultiplication.targetAddGates fieldTail counterWidth p)
      (MontgomeryMultiplication.targetAddGates_bitDisjoint_multiplier
        fieldTail counterWidth p bit)
      (MontgomeryMultiplication.targetAddGates_bitDisjoint_path
        fieldTail counterWidth p)
      (Layout.mutableYBit_wire_ne_liftArithmeticBit fieldTail.succ
        counterWidth bit (MK.Compact.pathBit fieldTail.succ counterWidth))
  calc
    _ ≤ 3 *
        (MontgomeryMultiplication.targetAddGates fieldTail counterWidth p).length :=
      hcontrol
    _ = 3 * (CompactCorrection.targetUpdateGates fieldTail counterWidth p).length := by
      simp [MontgomeryMultiplication.targetAddGates,
        MontgomeryMultiplication.targetAddSourceGates]
    _ ≤ 3 * (56 * fieldTail.succ + 15) :=
      Nat.mul_le_mul_left 3
        (CompactCorrection.targetUpdateGates_length_le fieldTail
          counterWidth p)

theorem roundGates_length_le
    (fieldTail counterWidth p : Nat) (bit : Fin fieldTail.succ) :
    (MontgomeryMultiplication.roundGates fieldTail counterWidth p bit).length ≤
      225 * fieldTail.succ + 67 := by
  simp only [MontgomeryMultiplication.roundGates, List.length_append]
  have hselected := selectedAddGates_length_le fieldTail counterWidth p bit
  have hdoubling := CompactCorrection.doublingGates_length_le fieldTail
    counterWidth p
  have hlift :
      (MontgomeryMultiplication.coefficientDoublingGates fieldTail
        counterWidth p).length =
        (CompactCorrection.doublingGates fieldTail counterWidth p).length := by
    simp [MontgomeryMultiplication.coefficientDoublingGates]
  rw [hlift]
  omega

theorem roundsGates_length_le
    (fieldTail counterWidth p : Nat) :
    ∀ bits,
      (MontgomeryMultiplication.roundsGates fieldTail counterWidth p
        bits).length ≤ bits.length * (225 * fieldTail.succ + 67) := by
  intro bits
  induction bits with
  | nil => simp [MontgomeryMultiplication.roundsGates]
  | cons bit rest ih =>
      simp only [MontgomeryMultiplication.roundsGates, List.length_append,
        List.length_cons]
      calc
        _ ≤ (225 * fieldTail.succ + 67) +
            rest.length * (225 * fieldTail.succ + 67) :=
          Nat.add_le_add (roundGates_length_le fieldTail counterWidth p bit) ih
        _ = (rest.length + 1) * (225 * fieldTail.succ + 67) := by
          rw [Nat.add_mul, one_mul, Nat.add_comm]

theorem multiplicationGates_length_le
    (fieldTail counterWidth p : Nat) :
    (MontgomeryMultiplication.gates fieldTail counterWidth p).length ≤
      multiplicationGateBound fieldTail.succ := by
  simp only [MontgomeryMultiplication.gates, List.length_append]
  have hscale := inverseScaleGates_length_le fieldTail counterWidth p
    fieldTail.succ
  have hrounds := roundsGates_length_le fieldTail counterWidth p
    (List.finRange fieldTail.succ)
  rw [List.length_finRange] at hrounds
  have hlift :
      (MontgomeryMultiplication.inverseScalePointGates fieldTail counterWidth p
        fieldTail.succ).length =
        (MontgomeryMultiplication.inverseScaleGates fieldTail counterWidth p
          fieldTail.succ).length := by
    simp [MontgomeryMultiplication.inverseScalePointGates]
  rw [hlift]
  unfold multiplicationGateBound
  nlinarith

theorem constantXPrefixGates_length_le
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    (ModularOperations.constantXPrefixGates fieldTail counterWidth p hp
      constant).length ≤ 8 * fieldTail.succ + 1 := by
  have hnormalize := normalizeGates_length_le fieldTail.succ counterWidth p hp
  have hconstant := EncodedBit.Word.constantOneIndices_length_le constant
  simp only [ModularOperations.constantXPrefixGates, List.length_append,
    RegisterRouting.saveT0LowGates_length,
    RegisterRouting.historyLowToT0Gates_length,
    RegisterRouting.swapXT0Gates_length,
    EncodedBit.Word.xorConstantGates_length]
  omega

theorem constantXGates_length_le
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    (ModularOperations.subtractConstantXGates fieldTail counterWidth p hp
      constant).length ≤ 72 * fieldTail.succ + 17 ∧
    (ModularOperations.addConstantXGates fieldTail counterWidth p hp
      constant).length ≤ 72 * fieldTail.succ + 17 := by
  have hprefix := constantXPrefixGates_length_le fieldTail counterWidth p hp
    constant
  have hupdate := CompactCorrection.targetUpdateGates_length_le fieldTail
    counterWidth p
  constructor <;>
    simp [ModularOperations.subtractConstantXGates,
      ModularOperations.addConstantXGates] <;> omega

theorem controlledTargetUpdateGates_length_le
    (fieldTail counterWidth p : Nat) :
    (ControlledOperations.controlledTargetSubtractGates fieldTail counterWidth
      p).length ≤ 3 * (56 * fieldTail.succ + 15) ∧
    (ControlledOperations.controlledTargetAddGates fieldTail counterWidth
      p).length ≤ 3 * (56 * fieldTail.succ + 15) := by
  constructor
  · exact
      (EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
        _ _ _
        (ControlledOperations.targetSubtractBodyGates_bitDisjoint_control
          fieldTail counterWidth p)
        (ControlledOperations.targetSubtractBodyGates_bitDisjoint_path
          fieldTail counterWidth p)
        (ControlledOperations.controlBit_wire_ne_pathWorkBit fieldTail.succ
          counterWidth)).trans
        (by
          simpa [ControlledOperations.targetSubtractBodyGates] using
            Nat.mul_le_mul_left 3
              (CompactCorrection.targetUpdateGates_length_le fieldTail
                counterWidth p))
  · exact
      (EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
        _ _ _
        (ControlledOperations.targetAddBodyGates_bitDisjoint_control
          fieldTail counterWidth p)
        (ControlledOperations.targetAddBodyGates_bitDisjoint_path
          fieldTail counterWidth p)
        (ControlledOperations.controlBit_wire_ne_pathWorkBit fieldTail.succ
          counterWidth)).trans
        (by
          simpa [ControlledOperations.targetAddBodyGates] using
            Nat.mul_le_mul_left 3
              (CompactCorrection.targetUpdateGates_length_le fieldTail
                counterWidth p))

theorem controlledCoordinateGates_length_le
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    (ControlledOperations.subtractConstantXGates fieldTail counterWidth p hp
      constant).length ≤ 184 * fieldTail.succ + 47 ∧
    (ControlledOperations.addConstantXGates fieldTail counterWidth p hp
      constant).length ≤ 184 * fieldTail.succ + 47 ∧
    (ControlledOperations.subtractT0FromXGates fieldTail counterWidth p hp).length ≤
      182 * fieldTail.succ + 47 ∧
    (ControlledOperations.subtractConstantYGates fieldTail counterWidth p hp
      constant).length ≤ 202 * fieldTail.succ + 47 := by
  have hconstant := constantXPrefixGates_length_le fieldTail counterWidth p hp
    constant
  have htarget := controlledTargetUpdateGates_length_le fieldTail counterWidth p
  have hnormalize := normalizeGates_length_le fieldTail.succ counterWidth p hp
  have hxprefix :
      (ModularOperations.xFromT0PrefixGates fieldTail counterWidth p hp).length ≤
        7 * fieldTail.succ + 1 := by
    simp only [ModularOperations.xFromT0PrefixGates, List.length_append,
      RegisterRouting.t0ToCoefficientGates_length,
      RegisterRouting.swapXT0Gates_length,
      RegisterRouting.coefficientToXGates_length]
    omega
  have hswap :
      (ModularOperations.swapXYGates fieldTail.succ counterWidth).length =
        9 * fieldTail.succ := by
    simp [ModularOperations.swapXYGates]
    omega
  have hsubX :
      (ControlledOperations.subtractConstantXGates fieldTail counterWidth p hp
        constant).length ≤ 184 * fieldTail.succ + 47 := by
    simp [ControlledOperations.subtractConstantXGates]
    omega
  have haddX :
      (ControlledOperations.addConstantXGates fieldTail counterWidth p hp
        constant).length ≤ 184 * fieldTail.succ + 47 := by
    simp [ControlledOperations.addConstantXGates]
    omega
  have hsubT0 :
      (ControlledOperations.subtractT0FromXGates fieldTail counterWidth p hp).length ≤
        182 * fieldTail.succ + 47 := by
    simp [ControlledOperations.subtractT0FromXGates]
    omega
  refine ⟨hsubX, haddX, hsubT0, ?_⟩
  rw [ControlledOperations.subtractConstantYGates]
  simp only [List.length_append, List.length_reverse]
  rw [hswap]
  omega

theorem multiplicationOperationGates_length_le
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    (MontgomeryOperations.t0IntoLambdaGates fieldTail counterWidth p hp).length ≤
        2 * multiplicationGateBound fieldTail.succ + 15 * fieldTail.succ + 2 ∧
    (MontgomeryOperations.xIntoYGates fieldTail counterWidth p hp).length ≤
        2 * multiplicationGateBound fieldTail.succ + 19 * fieldTail.succ + 2 ∧
    (MontgomeryOperations.squareLambdaGates fieldTail counterWidth p hp).length ≤
        2 * multiplicationGateBound fieldTail.succ + 21 * fieldTail.succ + 2 := by
  have hnormalize := normalizeGates_length_le fieldTail.succ counterWidth p hp
  have hmultiply := multiplicationGates_length_le fieldTail counterWidth p
  have ht0prefix :
      (MontgomeryOperations.t0IntoLambdaPrefixGates fieldTail counterWidth p
        hp).length ≤ 7 * fieldTail.succ + 1 := by
    simp only [MontgomeryOperations.t0IntoLambdaPrefixGates,
      MontgomeryOperations.t0IntoLambdaRoutingGates, List.length_append,
      RegisterRouting.saveXHighGates_length,
      RegisterRouting.historyHighToXGates_length,
      RegisterRouting.saveT0LowGates_length,
      RegisterRouting.historyLowToT0Gates_length,
      RegisterRouting.historyLowToCoefficientGates_length]
    omega
  have hxprefix :
      (MontgomeryOperations.xIntoYPrefixGates fieldTail counterWidth p hp).length ≤
        9 * fieldTail.succ + 1 := by
    simp only [MontgomeryOperations.xIntoYPrefixGates, List.length_append,
      RegisterRouting.swapYLambdaGates_length,
      RegisterRouting.saveT0LowGates_length,
      RegisterRouting.historyLowToT0Gates_length,
      RegisterRouting.xToCoefficientGates_length,
      RegisterRouting.coefficientToXGates_length]
    omega
  have hsquarePrefix :
      (MontgomeryOperations.squareLambdaPrefixGates fieldTail counterWidth p
        hp).length ≤ 10 * fieldTail.succ + 1 := by
    simp only [MontgomeryOperations.squareLambdaPrefixGates,
      List.length_append, RegisterRouting.swapYLambdaGates_length,
      RegisterRouting.saveXHighGates_length,
      RegisterRouting.historyHighToXGates_length,
      RegisterRouting.saveT0LowGates_length,
      RegisterRouting.historyLowToT0Gates_length,
      RegisterRouting.yToCoefficientGates_length]
    omega
  constructor
  · rw [MontgomeryOperations.t0IntoLambdaGates_length]
    omega
  constructor
  · rw [MontgomeryOperations.xIntoYGates_length]
    omega
  · rw [MontgomeryOperations.squareLambdaGates_length]
    omega

theorem controlledNegateXGates_length_le
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    (ControlledOperations.negateXGates fieldTail counterWidth p hp).length ≤
      137 * fieldTail.succ + 34 := by
  have hnormalize := normalizeGates_length_le fieldTail.succ counterWidth p hp
  have hupdate := CompactCorrection.targetUpdateGates_length_le fieldTail
    counterWidth p
  have hprefix :
      (ModularOperations.t0FromXPrefixGates fieldTail counterWidth p hp).length ≤
        4 * fieldTail.succ + 1 := by
    simp only [ModularOperations.t0FromXPrefixGates, List.length_append,
      RegisterRouting.xToCoefficientGates_length,
      RegisterRouting.coefficientToXGates_length]
    omega
  have hcompute :
      (ModularOperations.subtractXFromT0Gates fieldTail counterWidth p hp).length ≤
        64 * fieldTail.succ + 17 := by
    simp only [ModularOperations.subtractXFromT0Gates, List.length_append,
      List.length_reverse, ArithmeticLift.gates_length]
    omega
  have hswap :=
    EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
      (Layout.controlBit fieldTail.succ counterWidth)
      (ControlledOperations.pathWorkBit fieldTail.succ counterWidth)
      (RegisterRouting.swapXT0Gates fieldTail.succ counterWidth)
      (ControlledOperations.swapXT0Gates_bitDisjoint_control fieldTail.succ
        counterWidth)
      (ControlledOperations.swapXT0Gates_bitDisjoint_path fieldTail.succ
        counterWidth)
      (ControlledOperations.controlBit_wire_ne_pathWorkBit fieldTail.succ
        counterWidth)
  simp only [ControlledOperations.negateXGates, List.length_append,
    List.length_reverse]
  have hswap' :
      (ControlledOperations.controlledSwapXT0Gates fieldTail.succ
        counterWidth).length ≤ 9 * fieldTail.succ := by
    calc
      _ ≤ 3 * (RegisterRouting.swapXT0Gates fieldTail.succ
          counterWidth).length := hswap
      _ = 9 * fieldTail.succ := by
        simp
        omega
  omega

/-- The literal seventeen-stage ledger obeys its closed native-leaf bound. -/
theorem gates_length_le
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    (Schedule.gates fieldTail counterTail p hpPos hp hfit hcapacity hwidth
      x2 y2).length ≤ pointAdditionGateBound fieldTail.succ counterTail := by
  have hconstant := constantXGates_length_le fieldTail (counterTail + 2) p hp x2
  have hcontrolledX := controlledCoordinateGates_length_le fieldTail
    (counterTail + 2) p hp x2
  have hcontrolledY := controlledCoordinateGates_length_le fieldTail
    (counterTail + 2) p hp y2
  have hcontrolledTriple := controlledCoordinateGates_length_le fieldTail
    (counterTail + 2) p hp
      (Schedule.tripleConstant fieldTail p hpPos hp x2)
  have hoperations := multiplicationOperationGates_length_le fieldTail
    (counterTail + 2) p hp
  have hnegate := controlledNegateXGates_length_le fieldTail
    (counterTail + 2) p hp
  have hinversion :
      (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
        hwidth).length ≤ inversionGateBound fieldTail.succ counterTail := by
    rw [MontgomeryInversion.gates_length]
    exact CompactInversion.compactInversionGates_length_le fieldTail
      counterTail p hfit hcapacity hwidth
  have hpred : fieldTail.succ - 1 = fieldTail := by omega
  simp only [Schedule.gates, Schedule.stageLedgers, List.flatten_cons,
    List.flatten_nil, List.length_append, List.length_reverse,
    List.length_nil, Nat.add_zero]
  simp only [pointAdditionGateBound, inversionGateBound,
    multiplicationGateBound] at *
  rw [hpred] at hinversion
  nlinarith

/-- Circuit compiled from the exact seventeen-stage native ledger. -/
def program
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (Layout.encoding fieldTail.succ (counterTail + 2)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (Schedule.gates fieldTail counterTail p hpPos hp hfit hcapacity hwidth
      x2 y2)

/-- The literal native program maps a certified clean encoded basis state to
the cleaned seventeen-stage endpoint.  This is the semantic bridge for the
same circuit whose resources are counted below. -/
theorem program_applyNormalized_clean_ket
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (data : Schedule.Input fieldTail)
    (certificate : Schedule.CleanCertificate fieldTail counterTail p hpPos hp
      hfit data) :
    (program fieldTail counterTail p hpPos hp hfit hcapacity hwidth
        data.x2 data.y2).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (Layout.encoding fieldTail.succ (counterTail + 2)).width).basisEquiv.symm
            ((Layout.encoding fieldTail.succ (counterTail + 2)).encode
              (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
                data.control data.y1 0 ⟨p, hp⟩ data.x1 0)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
            (Layout.encoding fieldTail.succ (counterTail + 2)).width).basisEquiv.symm
          ((Layout.encoding fieldTail.succ (counterTail + 2)).encode
            (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
              data.control
              (data.outputY counterTail p hpPos hp hfit) 0 ⟨p, hp⟩
              (data.outputX counterTail p hpPos hp hfit) 0))) := by
  have semantic :=
    (Schedule.realizes fieldTail counterTail p hpPos hp hfit hcapacity hwidth
      data.x2 data.y2).apply_encoded_ket
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control data.y1 0 ⟨p, hp⟩ data.x1 0)
  rw [Schedule.step_cleanEndpoint fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth data certificate] at semantic
  exact semantic

/-- Same-circuit Toffoli ceiling obtained from the literal native list. -/
theorem program_toffoli_count_le
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (program fieldTail counterTail p hpPos hp hfit hcapacity hwidth
          x2 y2).eventCost ≤
      pointAdditionGateBound fieldTail.succ counterTail := by
  rw [program, EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  have htotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (Schedule.gates fieldTail counterTail p hpPos hp hfit hcapacity hwidth
      x2 y2)
  exact (by omega :
    ((Schedule.gates fieldTail counterTail p hpPos hp hfit hcapacity hwidth
      x2 y2).map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      (Schedule.gates fieldTail counterTail p hpPos hp hfit hcapacity hwidth
        x2 y2).length).trans
    (gates_length_le fieldTail counterTail p hpPos hp hfit hcapacity hwidth
      x2 y2)

/-- Strict sequential unit-depth obeys the same native-leaf closed form. -/
theorem program_unitDepth_le
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
        (program fieldTail counterTail p hpPos hp hfit hcapacity hwidth x2 y2) ≤
      pointAdditionGateBound fieldTail.succ counterTail := by
  rw [program, EncodedBit.GateSpec.programList_evaluatedEventDepth_unit]
  exact gates_length_le fieldTail counterTail p hpPos hp hfit hcapacity hwidth
    x2 y2

end
end Resources
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
