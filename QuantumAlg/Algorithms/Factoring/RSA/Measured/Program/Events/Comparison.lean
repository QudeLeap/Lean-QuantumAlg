/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Comparison
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events.General

/-!
# Pure comparison of tight-key and full-input measured RSA event allowances

The tight problem for the original good-key witness remains unchanged.
Its independent native pool fits the separately proved full-input resource
envelope. This comparison alters no actual draw, gate, measurement, stored
result or retry branch [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

omit configuration in
private lemma baseBudget_le_general (width : Nat) :
    Resources.baseBudget width ≤ Resources.General.baseBudget width := by
  have arithmetic := MAU.Multiplication.Gidney.Measured.Layout.multiplicationBudget_le_general
    .empty BitWord.model .empty width
  change (_ + 2 • Resources.oneQubit + Resources.oneQubit + Resources.oneMeasurement) ≤
    (_ + 2 • Resources.oneQubit + Resources.oneQubit + Resources.oneMeasurement)
  exact add_le_add (add_le_add (add_le_add arithmetic le_rfl) le_rfl) le_rfl

omit configuration in
private lemma memberBudget_le_general (m ell width : Nat) :
    Resources.memberBudget m ell width ≤ Resources.General.memberBudget m ell width := by
  change (_ + ((ell + m).choose 2 + ell.choose 2) • Resources.oneQubit) ≤
    (_ + ((ell + m).choose 2 + ell.choose 2) • Resources.oneQubit)
  exact add_le_add (nsmul_le_nsmul_right (baseBudget_le_general width)
    (ShortDLP.CompiledMAU.Recycling.resultBits m ell)) le_rfl

omit configuration in
/-- Packing, reset and reload are identical in the two independent full-round allowances. -/
lemma rsaMeasured_roundEventBudget_le_general (m ell width N : Nat) :
    roundEventBudget m ell width N ≤ generalRoundEventBudget m ell width N := by
  change (Resources.memberBudget m ell width + Round.packingBudget m ell + _) ≤
    (Resources.General.memberBudget m ell width + Round.packingBudget m ell + _)
  exact add_le_add (add_le_add (memberBudget_le_general m ell width) le_rfl) le_rfl

private lemma batchEventBudget_le_general (N : Nat) :
    batchEventBudget N ≤ generalBatchEventBudget N := by
  change (sourceEventBudget N + (membersPerBatch • _ + recoveryEventBudget N)) ≤
    (sourceEventBudget N + (membersPerBatch • _ + recoveryEventBudget N))
  exact add_le_add le_rfl (add_le_add
    (nsmul_le_nsmul_right (rsaMeasured_roundEventBudget_le_general
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N) membersPerBatch) le_rfl)

/-- The original tight-key problem budget fits the separate full-input public envelope. -/
lemma rsaMeasured_eventBudget_le_general (N count : Nat) :
    eventBudget N count ≤ generalEventBudget N count := by
  cases count with
  | zero => exact le_rfl
  | succ laterCount =>
      change (_ + (laterCount + 1) • batchEventBudget N + _) ≤
        (_ + (laterCount + 1) • generalBatchEventBudget N + _)
      exact add_le_add
        (add_le_add le_rfl
          (nsmul_le_nsmul_right (batchEventBudget_le_general N) (laterCount + 1))) le_rfl

end

end QuantumAlg.Factoring.RSA.Measured.Program
