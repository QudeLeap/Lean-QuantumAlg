/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Trajectory
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.BlockLaws
import all QuantumAlg.Util.NumberTheory.SharedEEA.Deshift.SourceWindow

/-!
# Complete reachable coefficient comparison frame

After the actual coefficient phase, the quotient is empty and the updated
coefficient occupies its complete shared region. Reading the divisor
boundary and current shift gives the entire aligned integer coefficient;
the source window reads precisely the old coefficient with zero high bits
[LYL+26, sec_EEA/sub_regshare.tex:16-20,263-264,297-300]. Its possibly nonzero
Euclidean remainder remains outside that source operand.

All physical widths and comparison interpretations below follow from the
original admissible macro invariant. The comparison is the actual native
coefficient block, with arbitrary incoming Sign and Iter retained. These
are basis-frame refinement equations, not input-dependent preparation or a
second execution mechanism. The post-shift and boundary exchange are later
parts of the same native microstep.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DeshiftPhaseFrame

noncomputable section

open NumberTheory.SharedEEA

private lemma shift_fits (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (within : shift ≤ state.quotient.size) : shift < 2 ^ modulus.size.size :=
  (within.trans (CoefficientPhaseFrame.quotient_size_le state modulus valid conserved)).trans_lt
    (Nat.lt_size_self modulus.size)

/-- The complete physical phase-four frame at its actual retained rotation and Sign. -/
def frame (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (sign iteration : Bool) : Registers modulus.size :=
  { CoefficientTrajectory.phaseFrame state modulus state.quotient.size
      valid conserved active le_rfl iteration with
    secondWord := (WordRotation.packRotatedWork2 shift
      (CoefficientCapacity.work2Payload state modulus state.quotient.size
        valid conserved active)).cast
          (CoefficientCapacity.work2_width state modulus valid conserved)
    shift := BitVec.ofNatLT shift (shift_fits state modulus shift valid conserved within)
    flags := ⟨true, true, sign, iteration⟩ }

/-- Original macro capacity supplies the actual divisor-plus-shift window check internally. -/
lemma window_fits (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (sign iteration : Bool) :
    (frame state modulus shift valid conserved active within sign iteration).divisorLength.toNat +
      (frame state modulus shift valid conserved active within sign iteration).shift.toNat ≤
        modulus.size + 3 := by
  change state.divisor.size + shift ≤ modulus.size + 3
  have aligned := DeshiftWindow.source_window_bound state modulus shift
    valid conserved active within
  have complete := CoefficientCapacity.work2_width state modulus valid conserved
  omega

/-- The enlarged Work1 window is the old coefficient, even with a nonzero remainder. -/
lemma sourceWord_value (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (sign iteration : Bool) :
    let physical := frame state modulus shift valid conserved active within sign iteration
    (CoefficientWindowLaws.sourceWord (DeshiftBlockLaws.window physical
      (window_fits state modulus shift valid conserved active within sign iteration))
        physical).toNat =
        state.coefficient := by
  dsimp only
  change (PhysicalWindow.read (modulus.size + 3 - state.divisor.size - shift)
    ((WordPacking.packWork1
      (CoefficientCapacity.work1Payload state modulus state.quotient.size valid conserved)).cast
        (CoefficientCapacity.work1_width state modulus state.quotient.size
          valid conserved))).toNat = _
  rw [CoefficientPhaseFrame.read_cast]
  exact DeshiftSourceWindow.read_completed state modulus shift valid conserved active within

/-- The actual enlarged Work2 window contains the entire aligned integer coefficient. -/
lemma targetWord_value (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (sign iteration : Bool) :
    let physical := frame state modulus shift valid conserved active within sign iteration
    (CoefficientWindowLaws.targetWord (DeshiftBlockLaws.window physical
      (window_fits state modulus shift valid conserved active within sign iteration))
        physical).toNat =
        (IterationState.step state).coefficient / 2 ^ shift := by
  dsimp only
  change (PhysicalWindow.read (modulus.size + 3 - state.divisor.size - shift)
    ((WordRotation.packRotatedWork2 shift
      (CoefficientCapacity.work2Payload state modulus state.quotient.size
        valid conserved active)).cast
          (CoefficientCapacity.work2_width state modulus valid conserved))).toNat = _
  rw [CoefficientPhaseFrame.read_cast]
  exact DeshiftWindow.read_completed state modulus shift valid conserved active within

/-- Native comparison implements the full source inequality and retains every other frame bit. -/
lemma native_frame (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (sign iteration : Bool) :
    ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus shift valid conserved active within sign iteration) =
        frame state modulus shift valid conserved active within
          (sign ^^ decide (state.coefficient * 2 ^ shift ≤
            (IterationState.step state).coefficient)) iteration := by
  let physical := frame state modulus shift valid conserved active within sign iteration
  have actual := DeshiftBlockLaws.native_frame modulus.size physical rfl rfl rfl
    (window_fits state modulus shift valid conserved active within sign iteration)
  have comparison :
      decide (state.coefficient ≤ (IterationState.step state).coefficient / 2 ^ shift) =
      decide (state.coefficient * 2 ^ shift ≤ (IterationState.step state).coefficient) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      DivisionScale.comparison (IterationState.step state).coefficient state.coefficient shift
  rw [sourceWord_value state modulus shift valid conserved active within sign iteration,
    targetWord_value state modulus shift valid conserved active within sign iteration,
    comparison] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.DeshiftPhaseFrame
