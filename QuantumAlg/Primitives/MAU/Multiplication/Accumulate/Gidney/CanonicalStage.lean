/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Carrier
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.ControlPushdown

/-!
# The actual internally borrowed accumulation stage

For word width `extra + 3`, the source supplies the leading selector, the
`extra` untouched coordinates, and the two arbitrary bits required by the
modular offset. The remaining word is the target. Control of comparisons within the
actual offset preserves every source field exactly on both branches.
This intermediate layout contains exactly the two original words; later
placement identifies its fields with the selected source coordinates
[G17, paper.tex:276-293,319-334].
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth BinaryLabelEncoding EncodedBit GateSpec

/-- Expand the selected modular offset into actual native gates on the existing two words. -/
def canonicalGates (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    List (GateSpec (canonicalEncoding extra)) :=
  ControlPushdown.canonicalGates extra modulus constant

/-- Both control branches restore every source field, including both arbitrary borrowed bits. -/
lemma gidneyCanonicalGates_step
    (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : CanonicalRegisters extra) :
    stepList (canonicalGates extra modulus constant) state =
      canonicalOutput modulus constant state :=
  ControlPushdown.canonical_step extra modulus constant state

/-- Execute the literal default-model expansion on its fixed complete carrier. -/
def canonicalProgram (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (canonicalEncoding extra).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (canonicalGates extra modulus constant)

/-- Exact joint-basis semantics of the actual controlled native construction. -/
lemma gidneyCanonicalStage_realizes (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (canonicalEncoding extra)
      (canonicalProgram extra modulus constant) environment (canonicalOutput modulus constant) :=
  realizesList_congrStep _ _ _ (gidneyCanonicalGates_step extra modulus constant) environment

/-- The ledger consists of the gates actually emitted by the control expansion. -/
lemma gidneyCanonicalStage_eventCost (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).eventCost =
      ResourcePool.ofList ((canonicalGates extra modulus constant).map (event .empty)) :=
  programList_eventCost _ _ _

/-- Unit-duration depth counts the full literal sequence, including borrowed-wire restoration. -/
lemma gidneyCanonicalStage_depth_eq_events (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).evaluatedEventDepth (fun _ => 1) =
      (canonicalProgram extra modulus constant).eventCost.card := by
  rw [canonicalProgram, programList_evaluatedEventDepth_unit, programList_eventCost_card]

/-- Quantum duration counts the same actual native instructions as the event ledger. -/
lemma gidneyCanonicalStage_quantumTime_eq_events (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).evaluatedEventDepth
        Resource.Event.quantumDuration =
      (canonicalProgram extra modulus constant).eventCost.card := by
  rw [canonicalProgram, programList_eventCost_card]
  exact ControlPushdown.native_time (canonicalGates extra modulus constant)

/-- The optimized actual list retains the independent original event envelope. -/
lemma gidneyCanonicalStage_event_count_bound (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).eventCost.card ≤
      4 * Addition.Gidney.modularOffsetEventBound (extra + 3) := by
  simpa only [canonicalProgram, canonicalGates, programList_eventCost_card] using
    ControlPushdown.canonical_length_bound extra modulus constant

/-- The original two words are the complete carrier; borrowed fields allocate no additional wire. -/
lemma gidneyCanonicalStage_qubit_count (extra : Nat) :
    (canonicalEncoding extra).width = 2 * (extra + 3) := by
  change 1 + (extra + (1 + ((extra + 3) + 1))) = 2 * (extra + 3)
  omega

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
