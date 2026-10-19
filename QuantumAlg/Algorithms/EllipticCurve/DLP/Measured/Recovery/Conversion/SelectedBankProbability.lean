/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.ObservationPartitions
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.OutputBankDensity

/-!
# Event weights from the literal converted-stream CP family

The actual reset and converted execution has the sum of traces of its own
complete Store/history bank fibers. Every legal measured path and every
original Store remains a distinct CP summand inside outputBankDensity.

This is a direct event identity, not a selected-frequency success floor.
It makes no comparison with the old readout and assumes neither clean input
nor positive incoming mass.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
namespace SelectedBankProbability

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)
variable {Reference : Register} {History : Type} [Fintype History]

/-- The complete CP family defines the event weight without a legacy execution. -/
def bankEventWeight (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (event : Store (Recovery.Layout.terminal p.size m) → Prop) : ℝ :=
  ∑ final, if event final then
    (OutputBankDensity.outputBankDensity (environment := environment) E fieldTail m seed r points
      coefficient
      state predicate final).trace.re else 0

/-- A selected actual output has exactly the trace sum of the same legal-path CP family. -/
lemma actual_event_weight_eq_bankEventWeight (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (event : Store (Recovery.Layout.terminal p.size m) → Prop)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) :
    ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute environment
      Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
        state)).effectWeight
        (fun record => if predicate record.2.2.1.1 ∧ event record.1 then
          Effect.one ((Recovery.Layout.terminal p.size m).register.prod Reference)
        else Effect.zero ((Recovery.Layout.terminal p.size m).register.prod Reference)) =
      bankEventWeight (environment := environment) E fieldTail m seed r points coefficient state
        predicate event := by
  let output := (convertedStages E r points (Recovery.Layout.order m) coefficient).execute
    environment Reference
    ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference state)
  have partition := ObservationPartitions.fiber_partition_effectWeight output Prod.fst
    (fun _ => ()) (fun record => predicate record.2.2.1.1) (fun value => event value.1)
  calc
    _ = ∑ final, if event final then
        (output.filterClassical
          (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.mass
        else 0 := by
      simpa only [Fintype.sum_unique, and_true] using partition
    _ = _ := by
      unfold bankEventWeight
      apply Finset.sum_congr rfl
      intro final _
      by_cases selected : event final
      · rw [if_pos selected, if_pos selected]
        exact OutputBankDensity.actual_reset_converted_fourier_outputBankDensity_mass
          E fieldTail m seed r points coefficient state predicate positive fits final
      · rw [if_neg selected, if_neg selected]

end
end SelectedBankProbability
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
