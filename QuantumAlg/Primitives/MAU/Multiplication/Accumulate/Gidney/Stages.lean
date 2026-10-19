/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.SmallStage
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stage

/-!
# One actual accumulation stage at every word width

Widths one and two use their direct controlled X/CNOT offset programs.
Every larger width uses two existing source coordinates as the returned
borrowed bits. Width zero has no source bit and no stage. The same exact
two-word interface therefore covers the complete width domain.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Select a real implementation by width, without padding either input word. -/
def stageProgram : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → Fin (modulus.val + 1) →
      UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical (encoding width).width).toQuantum
  | 0, selected, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant => smallStageProgram 1 (by decide) selected modulus constant
  | 2, selected, modulus, constant => smallStageProgram 2 (by decide) selected modulus constant
  | extra + 3, selected, modulus, constant => placedStageProgram extra selected modulus constant

/-- Uniform exact action of the actual all-width stage implementation. -/
lemma gidneyStage_realizes : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    UnitaryCircuit.Realizes (encoding width) (stageProgram width selected modulus constant)
      environment
      (selectedOutput selected modulus constant)
  | 0, selected, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant =>
      gidneySmallStage_realizes 1 (by decide) selected modulus constant
  | 2, selected, modulus, constant =>
      gidneySmallStage_realizes 2 (by decide) selected modulus constant
  | extra + 3, selected, modulus, constant =>
      gidneyPlacedStage_realizes extra selected modulus constant

/-- Every stage inhabits the complete original two-word interface. -/
lemma gidneyStage_interface (width : Nat) :
    (encoding width).width = 2 * width ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (2 * width) :=
  gidneySmallStage_interface width

/-- Independent numerical event bound, with literal small-width branches. -/
def stageEventBound (width : Nat) : Nat :=
  if width ≤ 2 then 9 else 4 * Addition.Gidney.modularOffsetEventBound width

lemma gidneyStage_event_count_bound : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    (stageProgram width selected modulus constant).eventCost.card ≤ stageEventBound width
  | 0, selected, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant =>
      gidneySmallStage_event_count_bound 1 (by decide) selected modulus constant
  | 2, selected, modulus, constant =>
      gidneySmallStage_event_count_bound 2 (by decide) selected modulus constant
  | extra + 3, selected, modulus, constant => by
      change (placedStageProgram extra selected modulus constant).eventCost.card ≤ _
      rw [(gidneyPlacedStage_resources extra selected modulus constant (fun _ => 1)).1]
      have hlarge : ¬extra + 3 ≤ 2 := by omega
      simpa only [stageEventBound, if_neg hlarge] using
        gidneyCanonicalStage_event_count_bound extra modulus constant

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
