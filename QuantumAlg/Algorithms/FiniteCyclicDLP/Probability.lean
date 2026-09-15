/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected

/-!
# Shared finite-cyclic DLP probability interface

The canonical probability development is the single implementation of the
source hidden-line analysis.  The concrete code-native runtime reuses these
definitions while supplying its own circuit-specific Born bridge.
-/

section

namespace QuantumAlg

noncomputable section

namespace FiniteCyclicDLP

/-- Proof-side secret input shared by canonical and code-native runtimes. -/
abbrev Input := @Canonical.Probability.SecretInput

namespace Probability

/-- Canonical residue index used by the hidden-line probability analysis. -/
abbrev residueIndex := @Canonical.Probability.residueIndex
/-- Canonical Fourier index selected for one residue. -/
abbrev selectedIndex := @Canonical.Probability.selectedIndex
/-- The canonical selected-index map is injective. -/
alias selectedIndex_injective :=
  Canonical.Probability.selectedIndex_injective
/-- Left fibre coordinate associated with a source index pair. -/
abbrev fiberLeft := @Canonical.Probability.fiberLeft
/-- The fibre coordinate evaluates the oracle multiplier at its source power. -/
alias oracleMultiplier_fiber :=
  Canonical.Probability.oracleMultiplier_fiber
/-- Characterization of source powers produced by the oracle multiplier. -/
alias oracleMultiplier_eq_generator_pow_iff :=
  Canonical.Probability.oracleMultiplier_eq_generator_pow_iff
/-- A bounded source sum agrees with the corresponding Fourier-modulus sum. -/
alias sum_fin_fourierModulus_if_sourceRange :=
  Canonical.Probability.sum_fin_fourierModulus_if_sourceRange
/-- One complex summand in a selected Fourier fibre. -/
abbrev selectedFiberTerm := @Canonical.Probability.selectedFiberTerm
/-- The distinguished zero residue. -/
abbrev zeroResidue := @Canonical.Probability.zeroResidue
/-- Phase of one term in the selected Fourier fibre. -/
abbrev selectedFiberPhase := @Canonical.Probability.selectedFiberPhase
/-- Common unit-modulus phase contributed by a selected tail. -/
abbrev selectedTailPhase := @Canonical.Probability.selectedTailPhase
/-- Residual phase after removing the common tail phase. -/
abbrev selectedErrorPhase := @Canonical.Probability.selectedErrorPhase
/-- The selected fibre phase sum has the calibrated half-order norm lower bound. -/
alias half_order_le_norm_sum_selectedFiberPhase :=
  Canonical.Probability.half_order_le_norm_sum_selectedFiberPhase
/-- Common complex scale factor for a selected fibre. -/
abbrev amplitudeScale := @Canonical.Probability.amplitudeScale
/-- A selected fibre term factors into its common scale and phase. -/
alias selectedFiberTerm_eq_scale_mul_phase :=
  Canonical.Probability.selectedFiberTerm_eq_scale_mul_phase
/-- Canonical raw terminal outcome selected by a unit residue. -/
abbrev selectedOutcome := @Canonical.Probability.selectedRawOutcome
/-- The canonical selected raw outcomes are injectively parameterized. -/
alias selectedOutcome_injective :=
  Canonical.Probability.selectedRawOutcome_injective
/-- Pointwise lower bound for the canonical selected raw outcomes. -/
abbrev selectedTailPointwiseLowerBound :=
  @Canonical.Probability.selectedTailPointwiseLowerBound
/-- Pointwise lower bound after summing all distinct tails. -/
abbrev selectedOutcomePointwiseLowerBound :=
  @Canonical.Probability.selectedRawOutcomePointwiseLowerBound
/-- Family of all selected raw outcomes. -/
abbrev selectedOutcomeFamily :=
  @Canonical.Probability.selectedRawOutcomeFamily
/-- Lower bound obtained by summing the selected-outcome family. -/
abbrev selectedOutcomeFamilyLowerBound :=
  @Canonical.Probability.selectedRawOutcomeFamilyLowerBound

namespace RecoveryBridge

/-- Canonical raw recovery input associated with a selected outcome. -/
abbrev selectedRawInput :=
  @Canonical.Probability.RecoveryBridge.selectedRawInput
/-- The canonical recovery output recovers the selected raw input. -/
alias outputOf_selectedRawInput_recovers :=
  Canonical.Probability.RecoveryBridge.outputOf_selectedRawInput_recovers

end RecoveryBridge
end Probability
end FiniteCyclicDLP

end

end QuantumAlg

end
