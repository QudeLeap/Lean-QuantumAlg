/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Exact live space of the streaming terminal layout

These identities concern the actual `ECCCaller.terminal` context: one shared
measured arithmetic bank, three indexed qubits, and all `2 * m` retained finite
measurement cells. The cells add classical bits and preserve every quantum
system. Both resident and auxiliary space follow the original storage roles.

The context itself has `3 * width + 4 * width.size + 14` qubits, hence 818 at width 256.
This is not a complete Algorithm space claim: the public point frame, recovery, and
retry execution have not been included or bounded here. No circuit, execution, or
independent budget is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication.MeasuredPlacement

/-- The actual terminal resident pool includes the bank and every retained Fourier cell. -/
lemma streamingTerminal_residentSpace (width m : Nat) :
    (terminal width m).residentSpace =
      (width + 2 * m) • SpacePool.ofShape (.finite 2) +
        OwnedQubits.space (3 * width + 4 * width.size + 14) := by
  rw [terminal, MeasurementCells.context_residentSpace, bank,
    readyContext_resident_exact, readySpace]
  have systems : 3 * width + 4 * width.size + 12 + 2 =
      3 * width + 4 * width.size + 14 := by omega
  rw [systems, add_nsmul]
  ac_rfl

/-- The actual auxiliary pool charges the same owned bank and retained cells. -/
lemma streamingTerminal_auxiliarySpace (width m : Nat) :
    (terminal width m).auxiliarySpace =
      (width + 2 * m) • SpacePool.ofShape (.finite 2) +
        OwnedQubits.space (3 * width + 4 * width.size + 14) := by
  rw [terminal, MeasurementCells.context_auxiliarySpace, bank,
    readyContext_auxiliary_exact, readySpace]
  have systems : 3 * width + 4 * width.size + 12 + 2 =
      3 * width + 4 * width.size + 14 := by omega
  rw [systems, add_nsmul]
  ac_rfl

/-- The bank's width cells and all Fourier cells remain real classical storage. -/
lemma streamingTerminal_classicalBits (width m : Nat) :
    SpacePool.count .classicalBits (terminal width m).residentSpace = width + 2 * m ∧
      SpacePool.count .classicalBits (terminal width m).auxiliarySpace = width + 2 * m := by
  have binaryBits : Nat.clog 2 2 = 1 := by decide
  constructor
  · rw [streamingTerminal_residentSpace]
    simp [SpacePool.count, SpacePool.ofShape, OwnedQubits.space, CShape.bitWidth, binaryBits]
  · rw [streamingTerminal_auxiliarySpace]
    simp [SpacePool.count, SpacePool.ofShape, OwnedQubits.space, CShape.bitWidth, binaryBits]

/-- Exactly the displayed dimension-two systems remain; every other dimension has count zero. -/
lemma streamingTerminal_quantumSystems (width m : Nat) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (terminal width m).residentSpace =
        (if 2 = dimension then 3 * width + 4 * width.size + 14 else 0) ∧
      SpacePool.count (.quantumSystems dimension) (terminal width m).auxiliarySpace =
        (if 2 = dimension then 3 * width + 4 * width.size + 14 else 0) := by
  constructor
  · rw [streamingTerminal_residentSpace]
    simp [SpacePool.count, SpacePool.ofShape, OwnedQubits.space]
  · rw [streamingTerminal_auxiliarySpace]
    simp [SpacePool.count, SpacePool.ofShape, OwnedQubits.space]

/-- Width 256 gives 818 qubits in this terminal context for every number of retained cells. -/
lemma streamingTerminal_width256_qubits (m : Nat) :
    SpacePool.count (.quantumSystems 2) (terminal 256 m).residentSpace = 818 ∧
      SpacePool.count (.quantumSystems 2) (terminal 256 m).auxiliarySpace = 818 := by
  have arithmetic : 3 * 256 + 4 * (256 : Nat).size + 14 = 818 := by decide
  have counts := streamingTerminal_quantumSystems 256 m 2
  simpa only [if_pos rfl, ite_true, arithmetic] using counts

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout
