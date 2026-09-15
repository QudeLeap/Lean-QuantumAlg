/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Comparison.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.SourceProgram

/-!
# The actual input fold on the complete shared-register frame

The already certified comparison, flag X, and controlled reflection are
placed on Work2, Iter, and the existing Ctrl, among all original source
fields [LYL+26, sec_EEA/sub_4phase.tex:107-117]. Their exact basis action
retains every complementary field and the arbitrary helper. The statement
holds on every encoded frame, before imposing the algorithm's original
positive-residue input domain.

The placement uses the exact binary and physical coordinate maps proved
by the comparison owners. No arithmetic permutation is substituted for the
existing native programs, and no new helper is allocated.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldProgram

noncomputable section

/-- Full-frame action of the actual source fold under the exact named-field decomposition. -/
def step (modulus : Nat) (state : Registers modulus.size) : Registers modulus.size :=
  (FoldRegisters.grouping modulus.size).symm
    (FoldSourceProgram.step modulus (FoldRegisters.grouping modulus.size state).1,
      (FoldRegisters.grouping modulus.size state).2)

/-- The real comparison and controlled reflection, placed on the original full source frame. -/
def program (modulus : Nat) : UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  FoldComparisonPlacement.placeFocus modulus.size
    (FoldComparisonFocus.place (modulus.size + 3) (FoldSourceProgram.program modulus))

/-- Exact all-frame action preserves amplitudes and every spectator coordinate. -/
theorem program_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (program modulus) (step modulus) :=
  (FoldComparisonPlacement.placeFocus_realizes modulus.size
    (FoldComparisonFocus.place_realizes (modulus.size + 3)
      (FoldSourceProgram.program_realizes modulus))).congrStep (by
        intro state
        simp only [FoldComparisonPlacement.focusStep, FoldComparisonFocus.placeStep,
          Equiv.symm_apply_apply, step]
        exact congrArg
          (fun focused : Addition.Gidney.Registers (modulus.size + 3) =>
            (FoldRegisters.grouping modulus.size).symm
              (focused, (FoldRegisters.grouping modulus.size state).2))
          ((FoldComparisonFocus.fieldEquiv (modulus.size + 3)).symm_apply_apply
            (FoldSourceProgram.step modulus (FoldRegisters.grouping modulus.size state).1)))

/-- The original full decomposition exhibits the changed focus and every retained field. -/
theorem step_grouping (modulus : Nat) (state : Registers modulus.size) :
    FoldRegisters.grouping modulus.size (step modulus state) =
      (FoldSourceProgram.step modulus (FoldRegisters.grouping modulus.size state).1,
        (FoldRegisters.grouping modulus.size state).2) :=
  (FoldRegisters.grouping modulus.size).apply_symm_apply _

/-- The complete Work1 word is an untouched spectator, including arbitrary dirty bits. -/
theorem step_firstWord (modulus : Nat) (state : Registers modulus.size) :
    (step modulus state).firstWord = state.firstWord := rfl

/-- Folding leaves the actual divisor-length field unchanged for the following native writer. -/
theorem step_divisorLength (modulus : Nat) (state : Registers modulus.size) :
    (step modulus state).divisorLength = state.divisorLength := rfl

/-- The original existing helper is restored by the same actual arithmetic program. -/
theorem step_control (modulus : Nat) (state : Registers modulus.size) :
    (step modulus state).control = state.control := rfl

/-- The complete native trace is the literal comparison, X, and controlled reflection trace. -/
theorem program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace = (FoldSourceProgram.program modulus).eventTrace :=
  (FoldComparisonPlacement.placeFocus_eventTrace modulus.size _).trans
    (FoldComparisonFocus.place_eventTrace (modulus.size + 3) _)

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldProgram
