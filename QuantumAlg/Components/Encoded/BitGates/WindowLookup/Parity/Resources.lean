/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity
import all QuantumAlg.Core.Execution.Circuit.Allocation

/-!
# Actual native mask-parity accounting

The native self-XOR clear and every selected-input XOR are retained even
though the quantum-duration model assigns zero time to classical events.
Their actual dependency expression still precedes every later stored branch.
The supplied classical parity cell remains part of the complete caller peak.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}

/-- Every actual fold path contains precisely its real width-one XOR operations. -/
lemma foldProgram_eventTrace (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (foldProgram (oracles := oracles) (services := services) parity inputs).Path) :
    (foldProgram parity inputs).eventTrace path = List.replicate inputs.length
      (.classicalOperation (.bit .xor)) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      dsimp only [foldProgram, Circuit.Path] at path
      change [.classicalOperation (.bit .xor)] ++
        (foldProgram parity rest).eventTrace path.2 = _
      rw [ih, List.length_cons, List.replicate_succ]
      rfl

/-- Clearing for each new row is paid in addition to every table-selected measured bit. -/
lemma program_eventTrace (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services) parity inputs).Path) :
    (program parity inputs).eventTrace path = List.replicate (inputs.length + 1)
      (.classicalOperation (.bit .xor)) := by
  change [.classicalOperation (.bit .xor)] ++
    (foldProgram parity inputs).eventTrace path.2 = _
  rw [foldProgram_eventTrace, List.replicate_succ]
  rfl

/-- Native classical XOR instructions retain their exact selected-coordinate multiplicity. -/
lemma program_xor_count (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services) parity inputs).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.classicalOperation (.bit .xor))
      ((program parity inputs).resourcePool path) = inputs.length + 1 := by
  rw [Circuit.resourcePool, program_eventTrace, ResourcePool.count_ofList, List.count_replicate]
  simp only [beq_self_eq_true, if_true]

/-- Native classical processing consumes no quantum-duration step in the selected schedule. -/
lemma foldProgram_quantumTime (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (foldProgram (oracles := oracles) (services := services) parity inputs).Path) :
    (foldProgram parity inputs).depth Resource.Event.quantumDuration path = 0 := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      dsimp only [foldProgram, Circuit.Path] at path
      change 0 + (foldProgram parity rest).depth Resource.Event.quantumDuration path.2 = 0
      rw [ih, Nat.zero_add]

/-- The actual parity clear is classical as well; its dependency remains in the circuit. -/
lemma program_quantumTime (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services) parity inputs).Path) :
    (program parity inputs).depth Resource.Event.quantumDuration path = 0 := by
  change 0 + (foldProgram parity inputs).depth Resource.Event.quantumDuration path.2 = 0
  rw [foldProgram_quantumTime, Nat.zero_add]

/-- The complete classical/quantum caller context is the exact resident peak. -/
lemma program_peakResidentSpace (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services) parity inputs).Path) :
    (program parity inputs).peakResidentSpace path = ctx.residentSpace :=
  Circuit.fixed_peakResidentSpace _ _

/-- Role-based auxiliary accounting includes those same actual supplied parity cells. -/
lemma program_peakAuxiliarySpace (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services) parity inputs).Path) :
    (program parity inputs).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  Circuit.fixed_peakAuxiliarySpace _ _

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity
