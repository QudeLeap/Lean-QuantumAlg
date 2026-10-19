/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Gates
import all QuantumAlg.Primitives.MAU.Addition.TTK.LocalAction

/-!
# Readout of the explicit TTK overflow output

Operand gates preserve the additional output bit. The two top-bit gates xor
the input addend and then the final carry into an arbitrary initial output
[TTK09, qic-loglogaddition-quant.tex:285-302,330-345].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec
open Nat.BinaryArithmetic

/-- Lifting a literal operand gate list preserves an arbitrary output bit. -/
lemma ttkWithOverflowGateList_step {n : Nat}
    (gates : List (EncodedBit.GateSpec (encoding n))) (s : OverflowRegisters n) :
    stepList (gates.map withOverflowGate) s = (stepList gates s.1, s.2) := by
  induction gates generalizing s with
  | nil => rfl
  | cons gate gates ih =>
      simp only [List.map_cons, stepList]
      rw [ttkWithOverflowGate_step, ih]

/-- The top stage-two CNOT changes only the explicit output bit. -/
lemma ttkOverflowPreGate_step (n : Nat) (s : OverflowRegisters (n + 1)) :
    (overflowPreGate n).step s =
      (s.1, s.2 ^^ s.1.1.val.testBit n) := by
  change (if (leftBit (n + 1) ⟨n, Nat.lt_succ_self n⟩).get s.1 then
    (s.1, !s.2) else s) = _
  rw [ttkLeftBit_get]
  cases s.1.1.val.testBit n <;> simp

/-- The top stage-three Toffoli changes only the explicit output bit. -/
lemma ttkOverflowCarryGate_step (n : Nat) (s : OverflowRegisters (n + 1)) :
    (overflowCarryGate n).step s =
      (s.1, s.2 ^^ (s.1.2.val.testBit n && s.1.1.val.testBit n)) := by
  change (if (rightBit (n + 1) ⟨n, Nat.lt_succ_self n⟩).get s.1 &&
    (leftBit (n + 1) ⟨n, Nat.lt_succ_self n⟩).get s.1 then
      (s.1, !s.2) else s) = _
  rw [ttkRightBit_get, ttkLeftBit_get]
  cases s.1.2.val.testBit n && s.1.1.val.testBit n <;> simp

/-- At the source's stage-three boundary, the output becomes `z xor carry`.
The operand state is preserved and the original output bit is unrestricted. -/
lemma ttkOverflowCarryGate_addition (n : Nat)
    (original s : Registers (n + 1)) (z : Bool)
    (hleft : s.1.val.testBit n =
      (original.1.val.testBit n ^^ natAddCarry original.1.val original.2.val n))
    (hright : s.2.val.testBit n =
      (original.2.val.testBit n ^^ original.1.val.testBit n)) :
    (overflowCarryGate n).step (s, z ^^ original.1.val.testBit n) =
      (s, z ^^ natAddCarry original.1.val original.2.val (n + 1)) := by
  let top : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hout := ttkCarryGate_target
    (withOverflowBit (rightBit (n + 1) top))
    (withOverflowBit (leftBit (n + 1) top)) (overflowBit (n + 1))
    (ttkWithOverflowBit_disjoint _ _
      (Ne.symm (ttkLeftRight_disjoint (n + 1) top top)))
    (ttkWithOverflowBit_output_disjoint _) (ttkWithOverflowBit_output_disjoint _)
    (s, z ^^ original.1.val.testBit n)
    (original.1.val.testBit n) (original.2.val.testBit n)
    (natAddCarry original.1.val original.2.val n) z
    (by simpa only [ttkWithOverflowBit_get, ttkRightBit_get] using hright)
    (by simpa only [ttkWithOverflowBit_get, ttkLeftBit_get] using hleft) rfl
  change ((overflowCarryGate n).step (s, z ^^ original.1.val.testBit n)).2 =
    (z ^^ Bool.carry (original.1.val.testBit n) (original.2.val.testBit n)
      (natAddCarry original.1.val original.2.val n)) at hout
  apply Prod.ext
  · rw [ttkOverflowCarryGate_step]
  · simpa only [natAddCarry] using hout

end

end QuantumAlg.MAU.Addition.TTK
