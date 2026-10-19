/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Correctness
import all QuantumAlg.Primitives.MAU.Addition.TTK.Overflow.Readout

/-!
# Exact correctness of TTK addition with an explicit overflow output

The source's top-bit gates xor the final carry into an arbitrary output bit.
The operand proof is shared with the low-word circuit. Widths zero and one
follow their actual empty or two-gate lists independently
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.GateSpec
open Nat.BinaryArithmetic

private lemma stepList_singleton {Data : Type} {E : BinaryLabelEncoding Data}
    (gate : EncodedBit.GateSpec E) (s : Data) :
    stepList [gate] s = gate.step s := rfl

private lemma overflow_step_zero (s : OverflowRegisters 0) :
    stepList (overflowGates 0) s = overflowOutput s := by
  have ha : s.1.1.val = 0 := by
    have h := s.1.1.isLt
    simp only [Nat.pow_zero] at h
    omega
  have hb : s.1.2.val = 0 := by
    have h := s.1.2.isLt
    simp only [Nat.pow_zero] at h
    omega
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      change s.1.2.val = (s.1.1.val + s.1.2.val) % 2 ^ 0
      rw [ha, hb]; rfl
  · change s.2 = (s.2 ^^ decide (2 ^ 0 ≤ s.1.1.val + s.1.2.val))
    rw [ha, hb]; simp

private lemma overflow_step_one (s : OverflowRegisters 1) :
    stepList (overflowGates 1) s = overflowOutput s := by
  have hlow : stepList (finalXorGates 1) s.1 = lowOutput s.1 := by
    simpa [lowRippleGates, preXorGates, descendingXorGates, carryGates,
      descendingUncomputeGates, ascendingXorGates] using ttkLowRipple_step 1 s.1
  rw [overflowGates, stepList_append, stepList_singleton,
    ttkOverflowCarryGate_step, ttkWithOverflowGateList_step, hlow]
  apply Prod.ext
  · rfl
  · change (s.2 ^^ (s.1.2.val.testBit 0 && s.1.1.val.testBit 0)) =
      (s.2 ^^ decide (2 ^ 1 ≤ s.1.1.val + s.1.2.val))
    rw [← natAddCarry_eq_decide_two_pow_le s.1.1.isLt s.1.2.isLt]
    simp only [natAddCarry]
    cases s.1.1.val.testBit 0 <;> cases s.1.2.val.testBit 0 <;> rfl

private lemma overflow_step_succ_succ (n : Nat) (s : OverflowRegisters (n + 2)) :
    stepList (overflowGates (n + 2)) s = overflowOutput s := by
  let middle := stepList (carryGates (n + 2))
    (stepList (descendingXorGates (n + 2)) (stepList (preXorGates (n + 2)) s.1))
  let top : Fin (n + 2) := ⟨n + 1, by omega⟩
  have hboundary := ttkCarryBoundary (n + 2) s.1
  have hpre : (stepList (preXorGates (n + 2)) s.1).1.val.testBit (n + 1) =
      s.1.1.val.testBit (n + 1) := by
    have h := ttkPreXor_left (n + 2) s.1 top
    simp only [ttkLeftBit_get] at h
    exact h
  have hleft : middle.1.val.testBit (n + 1) =
      (s.1.1.val.testBit (n + 1) ^^
        natAddCarry s.1.1.val s.1.2.val (n + 1)) := by
    have h := hboundary.1 top
    simp only [ttkLeftBit_get] at h
    exact h
  have hright : middle.2.val.testBit (n + 1) =
      (s.1.2.val.testBit (n + 1) ^^ s.1.1.val.testBit (n + 1)) := by
    have h := hboundary.2 top
    rw [ttkRightBit_get] at h
    have hne : top.val ≠ 0 := by
      change n + 1 ≠ 0
      omega
    rw [if_neg hne] at h
    exact h
  have hout := ttkOverflowCarryGate_addition (n + 1) s.1 middle s.2 hleft hright
  have hfinish := ttkFinishCarry (n + 2) s.1 middle hboundary.1 hboundary.2
  rw [overflowGates]
  simp only [stepList_append, stepList_singleton, ttkWithOverflowGateList_step,
    ttkOverflowPreGate_step]
  rw [hpre]
  change
    (stepList (finalXorGates (n + 2))
      (stepList (ascendingXorGates (n + 2))
        (stepList (descendingUncomputeGates (n + 2))
          ((overflowCarryGate (n + 1)).step
            (middle, s.2 ^^ s.1.1.val.testBit (n + 1))).1)),
      ((overflowCarryGate (n + 1)).step
        (middle, s.2 ^^ s.1.1.val.testBit (n + 1))).2) = overflowOutput s
  rw [hout]
  rw [hfinish]
  change (lowOutput s.1, s.2 ^^ natAddCarry s.1.1.val s.1.2.val (n + 2)) =
    (lowOutput s.1, s.2 ^^ decide (2 ^ (n + 2) ≤ s.1.1.val + s.1.2.val))
  rw [natAddCarry_eq_decide_two_pow_le s.1.1.isLt s.1.2.isLt]

/-- The literal overflow gate list computes the low sum and xors the final carry
into an arbitrary initial output bit, at every word width. -/
lemma ttkOverflow_step (n : Nat) (s : OverflowRegisters n) :
    stepList (overflowGates n) s = overflowOutput s := by
  cases n with
  | zero => exact overflow_step_zero s
  | succ n =>
      cases n with
      | zero => exact overflow_step_one s
      | succ n => exact overflow_step_succ_succ n s

/-- The compiled circuit realizes addition on exactly the two operands and its
explicit overflow output, with no clean-output or workspace assumption. -/
lemma ttkOverflow_realizes_addition (n : Nat) :
    UnitaryCircuit.Realizes (overflowEncoding n) (overflowProgram n) environment overflowOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (overflowGates n) (ttkOverflow_step n) environment

end

end QuantumAlg.MAU.Addition.TTK
