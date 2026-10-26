/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Cycle
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Pruned

/-!
# Actual native resource expressions for the certified pruned cycle

These exact event pools and evaluated dependency durations come from
the emitted syntax. The same seven-block prefix runs four times per
cycle; only the complete final boundary runs once. Native numerical
component bounds and final inversion/point resources remain separate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

/-- The complete actual word emits its seven-block prefix and one actual boundary. -/
lemma program_eventCost_body_boundary (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost = (bodyProgram width enough).eventCost +
      (TerminalBoundary.program width enough).eventCost := by
  simp only [program, bodyProgram, UnitaryCircuit.seq_eventCost]
  abel

/-- The complete actual word retains the original native dependencies at both blocks. -/
lemma program_quantumTime_body_boundary (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth Resource.Event.quantumDuration =
      (bodyProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration +
        (TerminalBoundary.program width enough).evaluatedEventDepth
          Resource.Event.quantumDuration := by
  simp only [program, bodyProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  omega

/-- Exactly four real prefixes and one real boundary occur in the actual pruned cycle. -/
lemma cycleProgram_eventCost (width : Nat) (enough : 2 ≤ width.size) :
    (cycleProgram width enough).eventCost = 4 • (bodyProgram width enough).eventCost +
      (TerminalBoundary.program width enough).eventCost := by
  simp only [cycleProgram, UnitaryCircuit.seq_eventCost, program_eventCost_body_boundary]
  abel

/-- Dependency duration is evaluated on the actual repeated prefix and retained boundary. -/
lemma cycleProgram_quantumTime (width : Nat) (enough : 2 ≤ width.size) :
    (cycleProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration =
      4 * (bodyProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration +
        (TerminalBoundary.program width enough).evaluatedEventDepth
          Resource.Event.quantumDuration := by
  simp only [cycleProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    program_quantumTime_body_boundary]
  omega

/-- Every actual repeated cycle charges all its native prefix and boundary occurrences. -/
lemma iterate_cycle_eventCost (width count : Nat) (enough : 2 ≤ width.size) :
    (UnitaryCircuit.iterate count (cycleProgram width enough)).eventCost =
      (4 * count) • (bodyProgram width enough).eventCost +
        count • (TerminalBoundary.program width enough).eventCost := by
  rw [UnitaryCircuit.iterate_eventCost, cycleProgram_eventCost, smul_add, smul_smul,
    Nat.mul_comm count 4]

/-- Actual public repetition retains the exact dependency duration of the emitted cycle. -/
lemma iterate_cycle_quantumTime (width count : Nat) (enough : 2 ≤ width.size) :
    (UnitaryCircuit.iterate count (cycleProgram width enough)).evaluatedEventDepth
        Resource.Event.quantumDuration =
      count * (4 * (bodyProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration +
        (TerminalBoundary.program width enough).evaluatedEventDepth
          Resource.Event.quantumDuration) := by
  rw [UnitaryCircuit.evaluatedEventDepth, UnitaryCircuit.iterate_eventDepth,
    DepthExpr.depthEval_iterate]
  change count * (cycleProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration = _
  rw [cycleProgram_quantumTime]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep
