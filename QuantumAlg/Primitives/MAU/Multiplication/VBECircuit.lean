/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BasisMap
import all QuantumAlg.Util.ModularMultiplicationDomain
import all QuantumAlg.Util.ZModUnits
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate
import all QuantumAlg.Primitives.MAU.Multiplication
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.VBECircuit
import all QuantumAlg.Primitives.MAU.Multiplication.Gate

/-!
# Uniform fixed-layout VBE modular multiplication circuit

This module composes the actual fixed-layout VBE multiply-accumulate program,
an `n`-bit three-CNOT word swap, and the actual reverse-list multiply-accumulate
program for the inverse unit.  All three segments use the same `5*n+4` layout,
and correctness and resources are projected from their one concatenated
BaseGate program [VBE95, 9511018.tex:333-367].
-/

section

namespace QuantumAlg
namespace MAU.Multiplication
namespace VBECircuit

open QuantumAlg.ModularMultiplication

noncomputable section

/-- The modular-multiplication circuit reuses the complete uniform MAC layout. -/
abbrev Registers (n : Nat) :=
  MAU.Multiplication.Accumulate.VBECircuit.Registers n

/-- The shared `5*n+4` binary layout. -/
abbrev encoding (n : Nat) : BinaryLabelEncoding (Registers n) :=
  MAU.Multiplication.Accumulate.VBECircuit.encoding n

/-- Width of the shared modular-multiplication layout. -/
theorem encoding_width (n : Nat) :
    (encoding n).width = 5 * n + 4 :=
  MAU.Multiplication.Accumulate.VBECircuit.encoding_width n

/-- The complete multiplicand word in the shared MAC layout. -/
def multiplicandWord (n : Nat) : EncodedBit.Word (encoding n) n :=
  MAU.Multiplication.Accumulate.VBECircuit.multiplicandWord n

/-- One low accumulator bit, excluding the VBE target overflow position. -/
def accumulatorBit (n : Nat) (bit : Fin n) : EncodedBit (encoding n) :=
  MAU.Multiplication.Accumulate.VBECircuit.targetBit n
    ⟨bit.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩

/-- The low `n` bits of the arithmetic target, used by the actual word swap. -/
def accumulatorWord (n : Nat) : EncodedBit.Word (encoding n) n where
  bit := accumulatorBit n

@[simp] theorem accumulatorBit_get (n : Nat) (bit : Fin n)
    (x : Registers n) :
    (accumulatorBit n bit).get x =
      x.arithmetic.target.val.testBit bit.val := by
  simp [accumulatorBit]

/-- Lifting two distinct arithmetic-workspace wires past the multiplier word
preserves their separation. -/
theorem liftArithmeticBit_ne (n : Nat)
    (left right : EncodedBit (MAU.Addition.VBECircuit.encoding n))
    (hne : left.wire ≠ right.wire) :
    (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n left).wire ≠
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n right).wire := by
  intro h
  have hv := congrArg Fin.val h
  change
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width + left.wire.val =
      (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width + right.wire.val at hv
  apply hne
  apply Fin.ext
  omega

/-- Every multiplier wire is disjoint from every lifted arithmetic wire. -/
theorem multiplicand_liftArithmetic_ne (n : Nat) (multiplierBit : Fin n)
    (observed : EncodedBit (MAU.Addition.VBECircuit.encoding n)) :
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n multiplierBit).wire ≠
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n observed).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hlt :
      (PlainAdder.Schedule.PowerOfTwo.wordBit n multiplierBit).wire.val <
        (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width :=
    (PlainAdder.Schedule.PowerOfTwo.wordBit n multiplierBit).wire.isLt
  simp [MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit,
    MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit,
    EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hv
  omega

theorem multiplicand_pairwise_ne (n : Nat) :
    ∀ i j, i ≠ j →
      ((multiplicandWord n).bit i).wire ≠
        ((multiplicandWord n).bit j).wire := by
  intro i j hij h
  have hw : WireAddress.littleEndianWire i =
      WireAddress.littleEndianWire j := by
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa [multiplicandWord,
      MAU.Multiplication.Accumulate.VBECircuit.multiplicandWord,
      MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit,
      PlainAdder.Schedule.PowerOfTwo.wordBit,
      BinaryLabelEncoding.ofEquivBit,
      EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
      BinaryLabelEncoding.prodLeftWire] using hv
  apply hij
  simpa using congrArg WireAddress.bitIndex hw

theorem accumulator_pairwise_ne (n : Nat) :
    ∀ i j, i ≠ j →
      ((accumulatorWord n).bit i).wire ≠
        ((accumulatorWord n).bit j).wire := by
  intro i j hij h
  have hv := congrArg Fin.val h
  simp [accumulatorWord, accumulatorBit,
    MAU.Multiplication.Accumulate.VBECircuit.targetBit,
    MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit,
    EncodedBit.relabel, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire,
    MAU.Addition.VBECircuit.targetBit_wire_val] at hv
  apply hij
  apply Fin.ext
  omega

theorem multiplicand_accumulator_cross_ne (n : Nat) :
    ∀ i j,
      ((multiplicandWord n).bit i).wire ≠
        ((accumulatorWord n).bit j).wire := by
  intro i j
  exact multiplicand_liftArithmetic_ne n i
    (MAU.Addition.VBECircuit.targetBit n
      ⟨j.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩)

theorem multiplicand_accumulator_diagonal_ne (n : Nat) :
    ∀ i,
      ((multiplicandWord n).bit i).wire ≠
        ((accumulatorWord n).bit i).wire :=
  fun i => multiplicand_accumulator_cross_ne n i i

/-- Actual three-CNOT-per-bit swap program for the multiplicand and low
accumulator words. -/
def swapProgram (n : Nat) : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
  ((encoding n).width)).toQuantum :=
  EncodedBit.Word.swapProgram
    (QubitLayout.canonical _) .empty
    (multiplicandWord n) (accumulatorWord n)
    (multiplicand_accumulator_diagonal_ne n)

/-- Folded semantic action of the exact word-swap program. -/
def swapStep (n : Nat) : Registers n → Registers n :=
  EncodedBit.Word.swapStep
    (multiplicandWord n) (accumulatorWord n)
    (multiplicand_accumulator_diagonal_ne n)

theorem swap_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (swapProgram n) (swapStep n) :=
  EncodedBit.Word.swap_realizes
    (QubitLayout.canonical _) .empty
    (multiplicandWord n) (accumulatorWord n)
    (multiplicand_accumulator_diagonal_ne n)







theorem swapStep_get_multiplicand (n : Nat) (bit : Fin n)
    (x : Registers n) :
    ((multiplicandWord n).bit bit).get (swapStep n x) =
      ((accumulatorWord n).bit bit).get x := by
  have h :=
    EncodedBit.Word.swapStep_get_left_word
      (multiplicandWord n) (accumulatorWord n)
      (multiplicand_accumulator_diagonal_ne n)
      (multiplicand_pairwise_ne n)
      (accumulator_pairwise_ne n)
      (multiplicand_accumulator_cross_ne n) x
  simpa [swapStep] using congrFun h bit

theorem swapStep_get_accumulator (n : Nat) (bit : Fin n)
    (x : Registers n) :
    ((accumulatorWord n).bit bit).get (swapStep n x) =
      ((multiplicandWord n).bit bit).get x := by
  have h :=
    EncodedBit.Word.swapStep_get_right_word
      (multiplicandWord n) (accumulatorWord n)
      (multiplicand_accumulator_diagonal_ne n)
      (multiplicand_pairwise_ne n)
      (accumulator_pairwise_ne n)
      (multiplicand_accumulator_cross_ne n) x
  simpa [swapStep] using congrFun h bit

/-- The physical word swap preserves any arithmetic-workspace bit outside the
low target word. -/
theorem swapStep_get_arithmeticBit_of_target_ne (n : Nat)
    (observed : EncodedBit (MAU.Addition.VBECircuit.encoding n))
    (htarget : ∀ i : Fin n,
      (MAU.Addition.VBECircuit.targetBit n
        ⟨i.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩).wire ≠
          observed.wire)
    (x : Registers n) :
    observed.get (swapStep n x).arithmetic = observed.get x.arithmetic := by
  have h :=
    EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (multiplicandWord n) (accumulatorWord n)
      (multiplicand_accumulator_diagonal_ne n)
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n observed)
      (fun i => multiplicand_liftArithmetic_ne n i observed)
      (fun i =>
        liftArithmeticBit_ne n
          (MAU.Addition.VBECircuit.targetBit n
            ⟨i.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩)
          observed (htarget i)) x
  simpa [swapStep] using h

theorem accumulator_targetHigh_ne (n : Nat) (bit : Fin n) :
    (MAU.Addition.VBECircuit.targetBit n
      ⟨bit.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩).wire ≠
      (MAU.Addition.VBECircuit.targetBit n (Fin.last n)).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [MAU.Addition.VBECircuit.targetBit_wire_val] at hv
  have hbit := bit.isLt
  simp [MAU.Addition.VBECircuit.AdderWidth] at hv
  omega

theorem accumulator_carry_ne (n : Nat) (bit : Fin n) :
    (MAU.Addition.VBECircuit.targetBit n
      ⟨bit.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩).wire ≠
      (MAU.Addition.VBECircuit.carryBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [MAU.Addition.VBECircuit.targetBit_wire_val,
    MAU.Addition.VBECircuit.carryBit_wire_val] at hv
  have hbit := bit.isLt
  omega

theorem accumulator_carryWork_ne (n : Nat) (bit : Fin n)
    (workBit : Fin (MAU.Addition.VBECircuit.AdderWidth n - 1)) :
    (MAU.Addition.VBECircuit.targetBit n
      ⟨bit.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩).wire ≠
      (MAU.Addition.VBECircuit.carryWorkBit n workBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [MAU.Addition.VBECircuit.targetBit_wire_val,
    MAU.Addition.VBECircuit.carryWorkBit_wire_val] at hv
  have hbit := bit.isLt
  omega

theorem accumulator_reductionFlag_ne (n : Nat) (bit : Fin n) :
    (MAU.Addition.VBECircuit.targetBit n
      ⟨bit.val, by simp [MAU.Addition.VBECircuit.AdderWidth]⟩).wire ≠
      (MAU.Addition.VBECircuit.reductionFlagBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [MAU.Addition.VBECircuit.targetBit_wire_val,
    MAU.Addition.VBECircuit.reductionFlagBit_wire_val] at hv
  have hbit := bit.isLt
  omega

/-- Exact fieldwise endpoint of the physical word swap on the shared VBE
workspace. The target high bit and all work fields remain clean. -/
theorem swapStep_workspaceState (n : Nat)
    (left right active parked : PlainAdder.Word n) (flag : Bool) :
    swapStep n
        (MAU.Multiplication.Accumulate.VBECircuit.workspaceState n
          left active parked
          (MAU.Addition.VBECircuit.widenWord n right) flag) =
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState n
        right active parked
        (MAU.Addition.VBECircuit.widenWord n left) flag := by
  let input := MAU.Multiplication.Accumulate.VBECircuit.workspaceState n
    left active parked (MAU.Addition.VBECircuit.widenWord n right) flag
  have hmultiplicand : (swapStep n input).multiplicand = right := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread := swapStep_get_multiplicand n bit input
    simpa [multiplicandWord,
      MAU.Multiplication.Accumulate.VBECircuit.multiplicandWord,
      accumulatorWord, accumulatorBit, input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have htarget :
      (swapStep n input).arithmetic.target =
        MAU.Addition.VBECircuit.widenWord n left := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    by_cases hlow : bit.val < n
    · let low : Fin n := ⟨bit.val, hlow⟩
      have hbit :
          bit =
            (⟨low.val, by
              simp [MAU.Addition.VBECircuit.AdderWidth]⟩ :
              Fin (MAU.Addition.VBECircuit.AdderWidth n)) := by
        apply Fin.ext
        rfl
      rw [hbit]
      have hread := swapStep_get_accumulator n low input
      simpa [multiplicandWord,
        MAU.Multiplication.Accumulate.VBECircuit.multiplicandWord,
        accumulatorWord, accumulatorBit, input,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
    · have hlast :
          bit =
            (Fin.last n : Fin (MAU.Addition.VBECircuit.AdderWidth n)) := by
        apply Fin.ext
        have hbitLt := bit.isLt
        simp [MAU.Addition.VBECircuit.AdderWidth] at hbitLt
        simp
        omega
      rw [hlast]
      have hread :=
        swapStep_get_arithmeticBit_of_target_ne n
          (MAU.Addition.VBECircuit.targetBit n (Fin.last n))
          (accumulator_targetHigh_ne n) input
      have hleftHigh : left.val.testBit n = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt left)
      have hrightHigh : right.val.testBit n = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt right)
      simpa [input, MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        hleftHigh, hrightHigh] using hread
  have hactive :
      (swapStep n input).arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord n active := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      swapStep_get_arithmeticBit_of_target_ne n
        (MAU.Addition.VBECircuit.activeSourceBit n bit)
        (fun low => Ne.symm
          (MAU.Addition.VBECircuit.activeSource_target_ne n bit
            ⟨low.val, by
              simp [MAU.Addition.VBECircuit.AdderWidth]⟩)) input
    simpa [input, MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hcarry : (swapStep n input).arithmetic.carry = false := by
    have hread :=
      swapStep_get_arithmeticBit_of_target_ne n
        (MAU.Addition.VBECircuit.carryBit n)
        (accumulator_carry_ne n) input
    simpa [input, MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hparked : (swapStep n input).arithmetic.parkedSource = parked := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      swapStep_get_arithmeticBit_of_target_ne n
        (MAU.Addition.VBECircuit.parkedSourceBit n bit)
        (fun low => Ne.symm
          (MAU.Addition.VBECircuit.parkedSource_target_ne n bit
            ⟨low.val, by
              simp [MAU.Addition.VBECircuit.AdderWidth]⟩)) input
    simpa [input, MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hwork :
      (swapStep n input).arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth n) := by
    change (swapStep n input).arithmetic.carryWork = 0
    apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    have hread :=
      swapStep_get_arithmeticBit_of_target_ne n
        (MAU.Addition.VBECircuit.carryWorkBit n bit)
        (fun low => accumulator_carryWork_ne n low bit) input
    rw [← MAU.Addition.VBECircuit.carryWorkBit_get]
    rw [hread]
    simp [input, MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState,
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]
  have hflag : (swapStep n input).arithmetic.reductionFlag = flag := by
    have hread :=
      swapStep_get_arithmeticBit_of_target_ne n
        (MAU.Addition.VBECircuit.reductionFlagBit n)
        (accumulator_reductionFlag_ne n) input
    simpa [input, MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  change swapStep n input = _
  apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv n).injective
  change
    ((swapStep n input).multiplicand, (swapStep n input).arithmetic) =
      (right, MAU.Addition.VBECircuit.sourceSwapCleanState n
        active parked (MAU.Addition.VBECircuit.widenWord n left) flag)
  rw [hmultiplicand]
  congr 1
  apply (MAU.Addition.VBECircuit.registersEquiv n).injective
  simp [MAU.Addition.VBECircuit.registersEquiv,
    MAU.Addition.VBECircuit.sourceSwapCleanState,
    hactive, htarget, hcarry, hparked, hwork, hflag]

/-- The actual word swap agrees with the high-level MAC-register swap on the
complete physical clean embedding. -/
theorem swapStep_cleanEmbedding (n N : Nat)
    (x : MAU.Multiplication.Accumulate.Data N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    swapStep n
        (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N x) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
        (MAU.Multiplication.swapMacRegisters x) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hmultiplicand : x.multiplicand.val < 2 ^ n :=
    lt_trans (ZMod.val_lt x.multiplicand) hN
  have haccumulator : x.accumulator.val < 2 ^ n :=
    lt_trans (ZMod.val_lt x.accumulator) hN
  change
    swapStep n
        (MAU.Multiplication.Accumulate.VBECircuit.workspaceState n
          (x.multiplicand.val : PlainAdder.Word n) 0
          (N : PlainAdder.Word n)
          (x.accumulator.val : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) x.flag) =
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState n
        (x.accumulator.val : PlainAdder.Word n) 0
        (N : PlainAdder.Word n)
        (x.multiplicand.val : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) x.flag
  rw [← MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
      n x.accumulator.val haccumulator,
    ← MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
      n x.multiplicand.val hmultiplicand]
  exact swapStep_workspaceState n _ _ _ _ _

/-! ### Actual MAC / swap / inverse-MAC composition -/

/-- Fixed-width classical word storing the residue underlying a unit. -/
def unitWord (n : Nat) {N : Nat} (u : (ZMod N)ˣ) :
    PlainAdder.Word n :=
  ((u : ZMod N).val : PlainAdder.Word n)

/-- Complete forward-MAC, physical-swap, inverse-MAC primitive list.  This
local NCT schedule is the direct construction source for the actual
multiplication program. -/
def multiplicationGates (n N : Nat) (u : (ZMod N)ˣ) :
    List (EncodedBit.GateSpec (encoding n)) :=
  MAU.Multiplication.Accumulate.VBECircuit.macGates
      n N (unitWord n u) ++
    EncodedBit.Word.swapGates
      (multiplicandWord n) (accumulatorWord n)
      (multiplicand_accumulator_diagonal_ne n) ++
    MAU.Multiplication.Accumulate.VBECircuit.macInverseGates
      n N (unitWord n (u⁻¹))

/-- The three exact programs in execution order: forward MAC, physical word
swap, and the reverse-list MAC for the inverse unit. -/
def multiplicationPrograms (n N : Nat) (u : (ZMod N)ˣ) :
    List (UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum) :=
  [MAU.Multiplication.Accumulate.VBECircuit.macProgram n N (unitWord n u),
    swapProgram n,
    MAU.Multiplication.Accumulate.VBECircuit.macInverseProgram n N
      (unitWord n (u⁻¹))]

/-- Full-register semantic actions aligned entry-for-entry with the three
actual circuit segments. -/
def multiplicationSteps (n N : Nat) (u : (ZMod N)ˣ) :
    List (Registers n → Registers n) :=
  [MAU.Multiplication.Accumulate.VBECircuit.macStep n N (unitWord n u),
    swapStep n,
    MAU.Multiplication.Accumulate.VBECircuit.macInverseStep n N
      (unitWord n (u⁻¹))]

theorem multiplicationStages_realize (n N : Nat) (u : (ZMod N)ˣ) :
    List.Forall₂
      (fun program step =>
        UnitaryCircuit.Realizes (encoding n) program step)
      (multiplicationPrograms n N u)
      (multiplicationSteps n N u) := by
  unfold multiplicationPrograms multiplicationSteps
  exact .cons
    (MAU.Multiplication.Accumulate.VBECircuit.mac_realizes n N
      (unitWord n u)) <|
    .cons (swap_realizes n) <|
    .cons
      (MAU.Multiplication.Accumulate.VBECircuit.macInverse_realizes n N
        (unitWord n (u⁻¹))) .nil

/-- One concatenated program is the sole implementation and resource ledger. -/
def multiplicationProgram (n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (multiplicationGates n N u)

/-! ### Strict-event size bound -/

/-- The forward-MAC/swap/inverse-MAC gate list has a quadratic bound. -/
theorem multiplicationGates_length_le (n N : Nat) (u : (ZMod N)ˣ) :
    (multiplicationGates n N u).length ≤
      108 * n ^ 2 + 105 * n := by
  have hforward :=
    MAU.Multiplication.Accumulate.VBECircuit.macGates_length_le
      n N (unitWord n u)
  have hswap := EncodedBit.Word.swapGates_length
    (multiplicandWord n) (accumulatorWord n)
    (multiplicand_accumulator_diagonal_ne n)
  have hinverse :=
    MAU.Multiplication.Accumulate.VBECircuit.macGates_length_le
      n N (unitWord n (u⁻¹))
  simp only [multiplicationGates, List.length_append,
    MAU.Multiplication.Accumulate.VBECircuit.macInverseGates,
    List.length_reverse]
  omega

/-- The actual multiplication circuit has the same quadratic strict-event
bound as its source gate list. -/
theorem multiplicationProgram_eventCount_le (n N : Nat)
    (u : (ZMod N)ˣ) :
    (multiplicationProgram n N u).eventCost.card ≤
      108 * n ^ 2 + 105 * n := by
  rw [multiplicationProgram,
    EncodedBit.GateSpec.programList_eventCost_card]
  exact multiplicationGates_length_le n N u

private theorem multiplicationSwapGates_cnotMultiplicity_sum (n : Nat) :
    ((EncodedBit.Word.swapGates
        (multiplicandWord n) (accumulatorWord n)
        (multiplicand_accumulator_diagonal_ne n)).map
          EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * n := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum
    (QubitLayout.canonical _) .empty]
  simpa [EncodedBit.Word.swapCircuit, EncodedBit.Word.swapProgram] using
    (EncodedBit.Word.swapCircuit_cnot_eventCount
      (QubitLayout.canonical _) .empty
      (multiplicandWord n) (accumulatorWord n)
      (multiplicand_accumulator_diagonal_ne n))

private theorem multiplicationSwapGates_toffoliMultiplicity_sum (n : Nat) :
    ((EncodedBit.Word.swapGates
        (multiplicandWord n) (accumulatorWord n)
        (multiplicand_accumulator_diagonal_ne n)).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  let gates := EncodedBit.Word.swapGates
    (multiplicandWord n) (accumulatorWord n)
    (multiplicand_accumulator_diagonal_ne n)
  have htotal := EncodedBit.GateSpec.primitiveEventCount_programList
    (QubitLayout.canonical (encoding n).width) .empty gates
  unfold EncodedBit.GateSpec.primitiveEventCount at htotal
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum] at htotal
  have hc := multiplicationSwapGates_cnotMultiplicity_sum n
  have hlen : gates.length = 3 * n := by
    exact EncodedBit.Word.swapGates_length
      (multiplicandWord n) (accumulatorWord n)
      (multiplicand_accumulator_diagonal_ne n)
  dsimp only [gates] at htotal hlen ⊢
  omega

private theorem multiplicationSwapGates_xMultiplicity_sum (n : Nat) :
    ((EncodedBit.Word.swapGates
        (multiplicandWord n) (accumulatorWord n)
        (multiplicand_accumulator_diagonal_ne n)).map
          EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  let gates := EncodedBit.Word.swapGates
    (multiplicandWord n) (accumulatorWord n)
    (multiplicand_accumulator_diagonal_ne n)
  have htotal := EncodedBit.GateSpec.primitiveEventCount_programList
    (QubitLayout.canonical (encoding n).width) .empty gates
  unfold EncodedBit.GateSpec.primitiveEventCount at htotal
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum] at htotal
  have hc := multiplicationSwapGates_cnotMultiplicity_sum n
  have hlen : gates.length = 3 * n := by
    exact EncodedBit.Word.swapGates_length
      (multiplicandWord n) (accumulatorWord n)
      (multiplicand_accumulator_diagonal_ne n)
  dsimp only [gates] at htotal hlen ⊢
  omega

/-- Exact Toffoli coordinate of the forward-MAC/swap/inverse-MAC source
schedule. -/
theorem multiplicationGates_toffoliMultiplicity_sum
    (n N : Nat) (u : (ZMod N)ˣ) :
    ((multiplicationGates n N u).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 60 * n ^ 2 := by
  simp [multiplicationGates,
    MAU.Multiplication.Accumulate.VBECircuit.macInverseGates,
    MAU.Multiplication.Accumulate.VBECircuit.macGates_toffoliMultiplicity_sum,
    multiplicationSwapGates_toffoliMultiplicity_sum]
  ring

/-- Bit-pattern-independent CNOT bound of the source multiplication schedule. -/
theorem multiplicationGates_cnotMultiplicity_sum_le
    (n N : Nat) (u : (ZMod N)ˣ) :
    ((multiplicationGates n N u).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      48 * n ^ 2 + 43 * n := by
  have hforward :=
    MAU.Multiplication.Accumulate.VBECircuit.macGates_cnotMultiplicity_sum_le
      n N (unitWord n u)
  have hinverse :=
    MAU.Multiplication.Accumulate.VBECircuit.macGates_cnotMultiplicity_sum_le
      n N (unitWord n (u⁻¹))
  simp only [multiplicationGates, List.map_append, List.sum_append,
    MAU.Multiplication.Accumulate.VBECircuit.macInverseGates,
    List.map_reverse, List.sum_reverse,
    multiplicationSwapGates_cnotMultiplicity_sum]
  nlinarith

/-- Exact X coordinate of the source multiplication schedule. -/
theorem multiplicationGates_xMultiplicity_sum
    (n N : Nat) (u : (ZMod N)ˣ) :
    ((multiplicationGates n N u).map
        EncodedBit.GateSpec.xMultiplicity).sum = 2 * n := by
  simp [multiplicationGates,
    MAU.Multiplication.Accumulate.VBECircuit.macInverseGates,
    MAU.Multiplication.Accumulate.VBECircuit.macGates_xMultiplicity_sum,
    multiplicationSwapGates_xMultiplicity_sum]
  omega

/-- Toffoli-only `ResourcePool.count` projection of the same multiplication
program used by semantics. -/
theorem multiplicationProgram_toffoli_count_eq
    (n N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (multiplicationProgram n N u).eventCost = 60 * n ^ 2 := by
  rw [multiplicationProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact multiplicationGates_toffoliMultiplicity_sum n N u













/-- The strict event schedule of the actual MAC/swap/inverse-MAC program is
independent of the compiled unit. -/
theorem multiplicationGates_events_eq (n N : Nat)
    (left right : (ZMod N)ˣ) :
    (multiplicationGates n N left).map (EncodedBit.GateSpec.event .empty) =
      (multiplicationGates n N right).map (EncodedBit.GateSpec.event .empty) := by
  simp only [multiplicationGates, List.map_append,
    MAU.Multiplication.Accumulate.VBECircuit.macInverseGates,
    List.map_reverse]
  rw [MAU.Multiplication.Accumulate.VBECircuit.macGates_events_eq
      n N (unitWord n left) (unitWord n right),
    MAU.Multiplication.Accumulate.VBECircuit.macGates_events_eq
      n N (unitWord n (left⁻¹)) (unitWord n (right⁻¹))]





/-- The actual VBE multiplication circuit has a strict event pool independent
of the compiled unit, directly from its equal strict event schedule. -/
theorem multiplicationProgram_eventCost_eq (n N : Nat)
    (left right : (ZMod N)ˣ) :
    (multiplicationProgram n N left).eventCost =
      (multiplicationProgram n N right).eventCost := by
  unfold multiplicationProgram
  apply EncodedBit.GateSpec.programList_eventCost_eq_of_events_eq
  exact multiplicationGates_events_eq n N left right

/-- The actual VBE multiplication circuit has a strict event critical path
independent of the compiled unit, directly from its equal strict event
schedule. -/
theorem multiplicationProgram_eventDepth_eq (n N : Nat)
    (left right : (ZMod N)ˣ) :
    (multiplicationProgram n N left).eventDepth =
      (multiplicationProgram n N right).eventDepth := by
  unfold multiplicationProgram
  apply EncodedBit.GateSpec.programList_eventDepth_eq_of_events_eq
  exact multiplicationGates_events_eq n N left right

/-- Folded total action of the exact concatenated physical program. -/
def multiplicationStep (n N : Nat) (u : (ZMod N)ˣ) :
    Registers n → Registers n :=
  EncodedBit.GateSpec.stepList (multiplicationGates n N u)

/-- The multiplication semantic action is definitionally the fold of the
complete primitive gate list used to construct its actual program. -/
theorem multiplicationStep_eq_gateList (n N : Nat) (u : (ZMod N)ˣ)
    (x : Registers n) :
    EncodedBit.GateSpec.stepList (multiplicationGates n N u) x =
      multiplicationStep n N u x :=
  rfl

theorem multiplication_realizes (n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (encoding n)
      (multiplicationProgram n N u) (multiplicationStep n N u) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (multiplicationGates n N u)

/-- Clean physical endpoint stated for the folded semantic action of the one
composed circuit. -/
theorem multiplicationStep_cleanEndpoint (n N : Nat)
    (u : (ZMod N)ˣ) (x : ZMod N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    multiplicationStep n N u
        (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
          (MAU.Multiplication.cleanInput x)) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
        (MAU.Multiplication.cleanOutput u x) := by
  simp only [multiplicationStep, multiplicationGates,
    EncodedBit.GateSpec.stepList_append]
  rw [MAU.Multiplication.Accumulate.VBECircuit.macStep_eq_gateList]
  change
    EncodedBit.GateSpec.stepList
        (MAU.Multiplication.Accumulate.VBECircuit.macInverseGates n N
          (unitWord n (u⁻¹)))
        (swapStep n
          (MAU.Multiplication.Accumulate.VBECircuit.macStep n N
            (unitWord n u)
            (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
              (MAU.Multiplication.cleanInput x)))) = _
  rw [MAU.Multiplication.Accumulate.VBECircuit.macInverseStep_eq_gateList]
  simp only [unitWord]
  rw [MAU.Multiplication.Accumulate.VBECircuit.macStep_cleanEmbedding n N
    (u : ZMod N) (MAU.Multiplication.cleanInput x) hNpos hN (by rfl)]
  rw [swapStep_cleanEmbedding n N
    ((MAU.Multiplication.cleanInput x).addScaled (u : ZMod N)) hNpos hN]
  rw [MAU.Multiplication.swapMacRegisters_addScaled_cleanInput]
  exact
    MAU.Multiplication.Accumulate.VBECircuit.macInverseStep_cleanEndpoint
      n N (((u⁻¹ : (ZMod N)ˣ) : ZMod N))
      (MAU.Multiplication.cleanOutput u x) hNpos hN (by rfl)

/-- The actual composed program maps an encoded clean input to the fully clean
modular-multiplication output. -/
theorem multiplicationProgram_applyNormalized_cleanEndpoint (n N : Nat)
    (u : (ZMod N)ˣ) (x : ZMod N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    (multiplicationProgram n N u).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
            ((encoding n).encode
              (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
                (MAU.Multiplication.cleanInput x))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
          ((encoding n).encode
            (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
              (MAU.Multiplication.cleanOutput u x)))) := by
  simpa only [multiplicationStep_cleanEndpoint n N u x hNpos hN] using
    (multiplication_realizes n N u).apply_encoded_ket
      (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
        (MAU.Multiplication.cleanInput x))

/-- The physical endpoint decodes to the established semantic
MAC/swap/uncompute construction. -/
theorem multiplicationStep_macSwapUncompute (n N : Nat)
    (u : (ZMod N)ˣ) (x : ZMod N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    multiplicationStep n N u
        (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
          (MAU.Multiplication.cleanInput x)) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
        (MAU.Multiplication.macSwapUncompute u
          (MAU.Multiplication.cleanInput x)) := by
  rw [MAU.Multiplication.macSwapUncompute_cleanInput]
  exact multiplicationStep_cleanEndpoint n N u x hNpos hN

/-- The same endpoint realizes the public residue action
`x ↦ multiplyByUnit u x` with all ancillas restored. -/
theorem multiplicationStep_multiplyByUnit (n N : Nat)
    (u : (ZMod N)ˣ) (x : ZMod N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    multiplicationStep n N u
        (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
          (MAU.Multiplication.cleanInput x)) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
        (MAU.Multiplication.cleanInput (multiplyByUnit u x)) := by
  simpa [MAU.Multiplication.cleanInput,
    MAU.Multiplication.cleanOutput, multiplyByUnit] using
    multiplicationStep_cleanEndpoint n N u x hNpos hN

/-! ### Circuit and resource projections from the same program -/

/-- Circuit compiled from the exact forward-MAC, swap, and inverse-MAC program. -/
def multiplicationCircuit (n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  multiplicationProgram n N u

/-- Ordered strict events of the concrete multiplication circuit. -/
def multiplicationEventTrace (n N : Nat) (u : (ZMod N)ˣ) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (multiplicationCircuit n N u).eventTrace

/-- Strict event pool of the concrete multiplication circuit. -/
def multiplicationEventCost (n N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (multiplicationCircuit n N u).eventCost

/-- Strict symbolic event critical path of the multiplication circuit. -/
def multiplicationEventDepth (n N : Nat) (u : (ZMod N)ˣ) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (multiplicationCircuit n N u).eventDepth

/-- Evaluated multiplication depth under literal event durations. -/
def multiplicationEvaluatedEventDepth (n N : Nat) (u : (ZMod N)ˣ)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) : Nat :=
  (multiplicationCircuit n N u).evaluatedEventDepth assign

/-- Multiplication depth selected by one literal event coordinate. -/
def multiplicationEventQueryDepth (n N : Nat) (u : (ZMod N)ˣ)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  (multiplicationCircuit n N u).eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the multiplication pool. -/
def multiplicationEventGateCount (n N : Nat) (u : (ZMod N)ˣ)
    (label : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count
    (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) label)
    (multiplicationCircuit n N u).eventCost

/-- Linearizing multiplication event depth recovers its exact event pool. -/
theorem multiplicationCircuit_resourcesFromEventDepth_eq_eventCost
    (n N : Nat) (u : (ZMod N)ˣ) :
    (multiplicationCircuit n N u).resourcesFromEventDepth =
      (multiplicationCircuit n N u).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (multiplicationCircuit n N u)











/-- Number of qubits in the shared fixed-layout realization.
The selected unit remains explicit to match the sibling resource projections,
while the fixed encoding makes the result depend only on `n`. -/
@[nolint unusedArguments]
def multiplicationQubitCount (n _N : Nat) (_u : (ZMod _N)ˣ) : Nat :=
  (encoding n).width

@[simp] theorem multiplicationQubitCount_eq (n N : Nat) (u : (ZMod N)ˣ) :
    multiplicationQubitCount n N u = 5 * n + 4 := by
  unfold multiplicationQubitCount
  exact encoding_width n



/-- Normalized clean-basis endpoint for the same concrete circuit whose strict
event projections are defined above. -/
theorem multiplicationCircuit_applyNormalized_clean_ket
    (n N : Nat) (u : (ZMod N)ˣ) (x : ZMod N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    (multiplicationCircuit n N u).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
            ((encoding n).encode
              (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
                (MAU.Multiplication.cleanInput x))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
          ((encoding n).encode
            (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
              (MAU.Multiplication.cleanOutput u x)))) := by
  simpa only [multiplicationCircuit] using
    multiplicationProgram_applyNormalized_cleanEndpoint n N u x hNpos hN

/-! ### Residue and selected-unit-carrier bridges -/

/-- Clean-subspace encoding of residue values into the complete physical
layout. -/
def residueEncoding (n N : Nat) (hNpos : 0 < N) (hN : N < 2 ^ n) :
    BinaryLabelEncoding (ZMod N) where
  width := (encoding n).width
  encode := fun x =>
    (encoding n).encode
      (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
        (MAU.Multiplication.cleanInput x))
  encode_injective := by
    let _ : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
    intro x y hxy
    have hphysical := (encoding n).encode_injective hxy
    have hdata :=
      (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding_injective
        n N hNpos hN) hphysical
    simpa [MAU.Multiplication.cleanInput] using
      congrArg MAU.Multiplication.Accumulate.Data.multiplicand hdata

/-- The exact physical program realizes multiplication on all canonically
embedded residue inputs. -/
theorem residue_realizes (n N : Nat) (u : (ZMod N)ˣ)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    UnitaryCircuit.Realizes (residueEncoding n N hNpos hN)
      (multiplicationProgram n N u) (multiplyByUnit u) where
  apply_encoded_ket := by
    intro x
    change
      (multiplicationProgram n N u).applyNormalized
          (NormalizedVector.ket
            ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
              ((encoding n).encode
                (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
                  (MAU.Multiplication.cleanInput x))))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
            ((encoding n).encode
              (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
                (MAU.Multiplication.cleanOutput u x))))
    exact multiplicationProgram_applyNormalized_cleanEndpoint
      n N u x hNpos hN

/-- Package the actual ancilla-extended VBE circuit as the selected
unit-carrier gate contract. -/
def gateRealization {N n : Nat} (D : ModularMultiplicationDomain N n)
    (u : ModularMultiplicationDomain.UnitCarrier D)
    (hN : N < 2 ^ n) :
    MAU.MultiplicationGate.EncodedCircuitRealization D u where
  Physical := Registers n
  encoding := encoding n
  cleanEmbedding := fun x =>
    MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
      (MAU.Multiplication.cleanInput (D.unitResidue x))
  cleanEmbedding_injective := by
    intro x y hxy
    have hdata :=
      (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding_injective
        n N D.modulus_pos hN) hxy
    have hresidue : D.unitResidue x = D.unitResidue y := by
      simpa [MAU.Multiplication.cleanInput] using
        congrArg MAU.Multiplication.Accumulate.Data.multiplicand hdata
    apply Units.ext
    simpa [ModularMultiplicationDomain.unitResidue] using hresidue
  program := multiplicationProgram n N u
  applyNormalized_clean := by
    intro x
    simpa [MAU.Multiplication.cleanInput,
      MAU.Multiplication.cleanOutput, multiplyByUnit,
      ModularMultiplicationDomain.unitResidue,
      ModularMultiplicationDomain.multiplyUnit] using
      multiplicationProgram_applyNormalized_cleanEndpoint
        n N u (D.unitResidue x) D.modulus_pos hN

end

end VBECircuit
end MAU.Multiplication
end QuantumAlg

end
