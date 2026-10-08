/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Phase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Bounds

/-!
# Native phase resources on every original register width

The independent budget distinguishes the restored signal-work path, the
restored control-work path, and the completely empty source register. No
projector or source oracle is hidden inside any of these native budgets.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
noncomputable section

/-- Independent native coordinates for one phase slot on the original register widths. -/
def phaseBudget (m n : Nat) (oracles : OracleModel) :
    ResourcePool (.quantum AlgorithmGate.model oracles) :=
  let single := ResourcePool.singleton
    (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
  let cnot := ResourcePool.singleton
    (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
  match m, n with
  | 0, 0 => single
  | k + 1, 0 => 4 • ZeroProjector.SourceWork.budget oracles k + 9 • single + 2 • cnot
  | m, _ + 1 => 2 • ZeroProjector.SourceWork.budget oracles m + single

/-- Independent sequential phase depth, retaining all masks and rotations. -/
def phaseDepth (m n : Nat) : Nat :=
  match m, n with
  | 0, 0 => 1
  | k + 1, 0 => 4 * (2 * k + EncodedBit.Word.OneDirtyLayout.gateCount k) + 11
  | m, _ + 1 => 2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 1

/-- Every native phase event is charged by the same actual execution on all widths. -/
theorem totalPhase_events (m n : Nat) (oracles : OracleModel) (angle : ℝ) :
    (phase m n oracles angle).eventCost = phaseBudget m n oracles := by
  cases n with
  | zero =>
      cases m with
      | zero => exact Gate.singleQubitAt_eventCost _ _ _ _ _
      | succ k => exact ControlWork.controlWork_phase_events k 0 oracles angle
  | succ n =>
      cases m <;> exact KnownZero.phase_events _ (n + 1) (Nat.zero_lt_succ n) oracles angle

/-- Exact dependency depth is derived from the executed native phase word. -/
theorem totalPhase_depth (m n : Nat) (oracles : OracleModel) (angle : ℝ) :
    (phase m n oracles angle).evaluatedEventDepth (fun _ => 1) = phaseDepth m n := by
  cases n with
  | zero =>
      cases m with
      | zero => rfl
      | succ k => exact ControlWork.controlWork_phase_depth k 0 oracles angle
  | succ n =>
      cases m <;> exact KnownZero.phase_depth _ (n + 1) (Nat.zero_lt_succ n) oracles angle

/-- All original widths have a uniform linear native phase-depth bound. -/
theorem totalPhaseDepth_le (m n : Nat) : phaseDepth m n ≤ 40 * m + 3 := by
  cases n with
  | zero =>
      cases m with
      | zero => decide
      | succ k =>
          have bound := KnownZero.conjunction_bound k 1 (by decide)
          simp only [phaseDepth]
          omega
  | succ n =>
      have bound := KnownZero.conjunction_bound m (n + 1) (Nat.zero_lt_succ n)
      simp only [phaseDepth]
      omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
