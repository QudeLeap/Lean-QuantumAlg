/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.BiFlip
import all QuantumAlg.Util.NumberTheory.SharedEEA.Iteration
import Mathlib.Data.Nat.Size

/-!
# Actual comparison and controlled reflection for the shared-EEA input fold

The literal source program compares with `p/2+1`, flips the retained Iter
flag, and executes the existing coherently controlled bi-flip at pivot
`p+1`. On the original positive-residue domain, the latter word operation
is exactly `p-x` [LYL+26, sec_EEA/sub_4phase.tex:112-117]. These are actual
HRS-backed Gidney programs [G17, paper.tex:276-277,380-389], including the
controlled native event coordinates already carried by the bi-flip.

The comparison word is the complete `size(p)+3`-bit Work2. Both possible
initial flag values and both helper values have an exact total action.
The original-domain specialization obtains Iter zero from internal
preparation and retains the resulting complement bit for reversal. The
input-dependent divisor length is computed by the separate actual writer
after this fold, rather than prepared from a classical input value.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldSourceProgram

noncomputable section

/-- The existing complete Work2 word, including its three physical padding bits. -/
def wordWidth (modulus : Nat) : Nat := modulus.size + 3

private theorem modulus_fits (modulus : Nat) : modulus < 2 ^ wordWidth modulus :=
  (Nat.lt_size_self modulus).trans_le
    (Nat.pow_le_pow_right (by decide) (by unfold wordWidth; omega))

/-- A less-than comparison at this pivot complements the source's strict half-threshold test. -/
def comparisonPivot (modulus : Nat) : Fin (2 ^ wordWidth modulus + 1) :=
  ⟨modulus / 2 + 1, by
    have fits := modulus_fits modulus
    have divided := Nat.div_le_self modulus 2
    omega⟩

/-- The existing bi-flip at `p+1` reflects every original residue to `p-x`. -/
def reflectionPivot (modulus : Nat) : Fin (2 ^ wordWidth modulus + 1) :=
  ⟨modulus + 1, by have fits := modulus_fits modulus; omega⟩

/-- The complete actual comparison, one flag X, and the already certified controlled bi-flip. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Addition.Gidney.encoding (wordWidth modulus)).width).toQuantum :=
  ((Addition.Gidney.comparisonProgram (wordWidth modulus) (comparisonPivot modulus)).seq
    (Addition.Gidney.flagFlipProgram (wordWidth modulus))).seq
      (Addition.Gidney.biFlipProgram (wordWidth modulus) (reflectionPivot modulus))

/-- The actual strict comparison is xored into the existing retained flag. -/
def record (modulus : Nat) (state : Addition.Gidney.Registers (wordWidth modulus)) : Bool :=
  state.1 ^^ decide (modulus / 2 < state.2.1.val)

/-- Total finite-word action of the actual program, including arbitrary initial flag and helper. -/
def step (modulus : Nat) (state : Addition.Gidney.Registers (wordWidth modulus)) :
    Addition.Gidney.Registers (wordWidth modulus) :=
  (record modulus state,
    (if record modulus state then
      Nat.FixedWidth.biFlipWordOutput (reflectionPivot modulus) state.2.1 else state.2.1,
      state.2.2))

private theorem component_steps (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    Addition.Gidney.biFlipOutput (reflectionPivot modulus)
      (Addition.Gidney.flagFlipOutput
        (Addition.Gidney.comparisonOutput (comparisonPivot modulus).val state)) =
      step modulus state := by
  rcases state with ⟨flag, word, helper⟩
  by_cases greater : modulus / 2 < word.val
  · have notLess : ¬word.val < (comparisonPivot modulus).val := by
      change ¬word.val < modulus / 2 + 1
      omega
    cases flag <;>
      simp [Addition.Gidney.biFlipOutput, Addition.Gidney.flagFlipOutput,
        Addition.Gidney.comparisonOutput, step, record, greater, notLess]
  · have less : word.val < (comparisonPivot modulus).val := by
      change word.val < modulus / 2 + 1
      omega
    cases flag <;>
      simp [Addition.Gidney.biFlipOutput, Addition.Gidney.flagFlipOutput,
        Addition.Gidney.comparisonOutput, step, record, greater, less]

/-- Exact coherent action comes from the same three real native component programs. -/
theorem program_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (Addition.Gidney.encoding (wordWidth modulus)) (program modulus)
      (step modulus) := by
  have comparison := Addition.Gidney.gidneyComparison_realizes
    (wordWidth modulus) (comparisonPivot modulus)
  have flag := Addition.Gidney.gidneyFlagFlip_realizes (wordWidth modulus)
  have reflection := Addition.Gidney.gidneyBiFlip_realizes
    (wordWidth modulus) (reflectionPivot modulus)
  exact ((comparison.seq flag).seq reflection).congrStep (component_steps modulus)

/-- The arbitrary existing helper is returned exactly, independently of the input and flag. -/
theorem step_helper (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    (step modulus state).2.2 = state.2.2 := rfl

/-- The complement history remains present in the actual result. -/
theorem step_record (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    (step modulus state).1 = record modulus state := rfl

/-- Internally prepared Iter zero gives exactly the original folded value and its retained flag. -/
theorem step_foldInput (modulus : Nat) (input : Fin (2 ^ wordWidth modulus))
    (helper : Bool) (bounded : input.val < modulus) :
    ((step modulus (false, (input, helper))).1,
      (step modulus (false, (input, helper))).2.1.val) =
        NumberTheory.SharedEEA.foldInput modulus input.val := by
  have reflected : input.val < modulus + 1 := by omega
  by_cases complemented : modulus / 2 < input.val
  · simp [step, record, complemented, NumberTheory.SharedEEA.foldInput,
      Nat.FixedWidth.biFlipWordOutput, Nat.FixedWidth.biFlip, reflectionPivot, reflected]
  · simp [step, record, complemented, NumberTheory.SharedEEA.foldInput]

/-- The retained record reconstructs the original residue, so folding does not erase its history. -/
theorem step_unfoldInput (modulus : Nat) (input : Fin (2 ^ wordWidth modulus))
    (helper : Bool) (bounded : input.val < modulus) :
    NumberTheory.SharedEEA.unfoldInput modulus
        ((step modulus (false, (input, helper))).1,
          (step modulus (false, (input, helper))).2.1.val) = input.val := by
  rw [step_foldInput modulus input helper bounded]
  exact NumberTheory.SharedEEA.unfoldInput_foldInput modulus input.val (Nat.le_of_lt bounded)

/-- The original residue domain supplies the macro initialization invariant internally. -/
theorem step_initial_admissible (modulus : Nat) (input : Fin (2 ^ wordWidth modulus))
    (helper : Bool) (positive : 0 < input.val) (bounded : input.val < modulus) :
    (NumberTheory.SharedEEA.IterationState.initial modulus
      (step modulus (false, (input, helper))).2.1.val).Admissible := by
  have value := congrArg Prod.snd (step_foldInput modulus input helper bounded)
  change (step modulus (false, (input, helper))).2.1.val =
    (NumberTheory.SharedEEA.foldInput modulus input.val).2 at value
  rw [value]
  exact NumberTheory.SharedEEA.folded_initial_admissible modulus input.val positive bounded

/-- The actual native trace includes all three blocks in their execution order. -/
theorem program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace =
      (Addition.Gidney.comparisonProgram
        (wordWidth modulus) (comparisonPivot modulus)).eventTrace ++
        (Addition.Gidney.flagFlipProgram (wordWidth modulus)).eventTrace ++
          (Addition.Gidney.biFlipProgram
            (wordWidth modulus) (reflectionPivot modulus)).eventTrace := by
  simp only [program, UnitaryCircuit.seq_eventTrace]

/-- The actual native pool retains the controlled arithmetic coordinates of the final bi-flip. -/
theorem program_eventCost (modulus : Nat) :
    (program modulus).eventCost =
      (Addition.Gidney.comparisonProgram (wordWidth modulus) (comparisonPivot modulus)).eventCost +
        (Addition.Gidney.flagFlipProgram (wordWidth modulus)).eventCost +
          (Addition.Gidney.biFlipProgram
            (wordWidth modulus) (reflectionPivot modulus)).eventCost := by
  simp only [program, UnitaryCircuit.seq_eventCost]

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldSourceProgram
