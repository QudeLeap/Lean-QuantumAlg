/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Nonzero
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Readout

/-!
# Actual signed-instruction guard omitting Sign

Coefficient addition reads Phase1; remainder subtraction reads negative
Phase1 and the complete nonzero divisor length. Original Iter is the
same arbitrary retained control. These guards remain valid across a
signed arithmetic update because neither guard reads Sign
[LYL+26, sec_EEA/sub_opt.tex:43-48,61-66].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

/-- The public instruction kind chooses its fixed actual native phase predicate word. -/
def signedGates (width : Nat) (coefficient : Bool) : List (GateSpec (encoding width)) :=
  if coefficient then phaseGates width 1 (by decide) (fun _ => true)
  else nonzeroGates width 1 (by decide) (fun _ => false)

/-- Independent actual-field condition, retaining complete divisor metadata and omitting Sign. -/
def signedStep (width : Nat) (coefficient : Bool) (state : Data width) : Data width :=
  if (flag width 3).get state &&
      (if coefficient then state.1.flags.first
      else !state.1.flags.first && decide (state.1.divisorLength ≠ 0)) then
    (flag width 4).flip state else state

/-- Actual original native gates realize the full signed phase condition on every finite label. -/
lemma signedGates_step (width : Nat) (coefficient : Bool) (state : Data width) :
    GateSpec.stepList (signedGates width coefficient) state =
      signedStep width coefficient state := by
  cases coefficient with
  | false =>
      simp only [signedGates, Bool.false_eq_true, if_false]
      rw [nonzeroGates_step]
      simp only [nonzeroStep, flags_matches_one]
      cases first : state.1.flags.first <;> simp [signedStep, first]
  | true =>
      simp only [signedGates, if_true]
      rw [phaseGates_step]
      simp only [flags_matches_one]
      cases iteration : (flag width 3).get state <;>
        cases first : state.1.flags.first <;> simp [signedStep, iteration, first]

/-- All coherent amplitudes and original complementary systems follow the same native word. -/
lemma signedProgram_realizes (width : Nat) (coefficient : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty (signedGates width coefficient))
      environment (signedStep width coefficient) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (signedGates_step width coefficient) environment

/-- Actual elementary bounds include masks, the full nonzero test and restored dirty work. -/
lemma signedGates_length_le (width : Nat) (coefficient : Bool) :
    (signedGates width coefficient).length ≤
      if coefficient then 21 else 21 + (10 * (width.size + 2) + 1) := by
  cases coefficient with
  | false =>
      simp only [signedGates, Bool.false_eq_true, if_false]
      have actual := nonzeroGates_length_le width 1 (by decide) (fun _ => false)
      omega
  | true =>
      exact phaseGates_length_le width 1 (by decide) (fun _ => true)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
