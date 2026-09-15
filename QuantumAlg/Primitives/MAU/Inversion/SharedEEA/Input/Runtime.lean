/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.PreparedFrame
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Execute real shared-EEA input preparation, folding, and length writing

One `Circuit.prepare` creates the fixed auxiliary bits beside the original
quantum input. One `Circuit.unitary` then executes the actual comparison,
controlled reflection, and native divisor-length writer on the resulting
physical frame [LYL+26, sec_EEA/sub_4phase.tex:104-117]. The exact wire
assembly identifies this execution with the source initial basis and its
proved native preprocessing result.

All quantum-reference coherences undergo the same actual preparation and
unitary conjugation [dW19, qcnotes.tex:5381,5405,8071]. The full reference
matrix is retained. Only the modulus selects the circuit. No source input
label selects a preparation parameter, and no additional control or dirty
workspace is supplied by the caller. This owner covers preprocessing;
it does not claim the later four-phase loop or inverse cleanup is complete.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InputRuntime

noncomputable section

open Execution InputPreparation

private theorem comparison_range (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (Addition.Gidney.comparisonProgram width pivot).physical_idx ⊆ List.range (width + 2) := by
  rw [Addition.Gidney.gidneyComparison_physical]
  exact List.Subset.refl _

private theorem sourceProgram_range (modulus : Nat) :
    (FoldSourceProgram.program modulus).physical_idx ⊆
      List.range ((modulus.size + 3) + 2) := by
  let width := modulus.size + 3
  have comparison : (Addition.Gidney.comparisonProgram width
      (FoldSourceProgram.comparisonPivot modulus)).physical_idx ⊆ List.range (width + 2) :=
    comparison_range (FoldSourceProgram.wordWidth modulus)
      (FoldSourceProgram.comparisonPivot modulus)
  have flag : (Addition.Gidney.flagFlipProgram width).physical_idx ⊆
      List.range (width + 2) := by
    have actual := EncodedBit.GateSpec.program_physical_idx_subset_range
      (.x (Addition.Gidney.flagBit width))
    have count : (Addition.Gidney.encoding width).width = width + 2 := by
      change 1 + (width + 1) = width + 2
      omega
    unfold Addition.Gidney.flagFlipProgram
    simpa only [count] using actual
  exact UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ comparison flag)
    (Addition.Gidney.gidneyBiFlip_physical_range width
      (FoldSourceProgram.reflectionPivot modulus))

private theorem foldProgram_physical (modulus : Nat) :
    (FoldProgram.program modulus).physical_idx = List.range (encoding modulus.size).width :=
  FoldComparisonPlacement.placeFocus_physical modulus.size _
    (FoldComparisonFocus.place_physical_range (modulus.size + 3)
      (FoldSourceProgram.program modulus) (sourceProgram_range modulus))

private theorem initialProgram_range (modulus : Nat) :
    (InitialFrame.program modulus).physical_idx ⊆ List.range (encoding modulus.size).width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (by rw [foldProgram_physical]; exact List.Subset.refl _)
    (EncodedBit.GateSpec.programList_physical_idx_subset_range
      (InitialLengthWrite.gates modulus.size))

/-- The same native preprocessing program on the actual post-preparation runtime register. -/
def program (modulus : Nat) : UnitaryCircuit (after modulus.size).register :=
  (UnitaryCircuit.reindex (InputAssembly.basisEquiv modulus.size).symm
    (InitialFrame.program modulus)).seq
      (UnitaryCircuit.identity (after modulus.size).register (after modulus.size).physicalIdx
        (after modulus.size).identitiesNodup)

/-- Native addresses occupy exactly the actual live context and no additional helper wire. -/
theorem program_placement (modulus : Nat) :
    (program modulus).physical_idx = (after modulus.size).physicalIdx := by
  change UnitaryCircuit.unionPhysicalIdx (InitialFrame.program modulus).physical_idx
    (after modulus.size).physicalIdx = _
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  intro wire present
  exact range_contained modulus.size (initialProgram_range modulus present)

/-- The post-preprocessing runtime basis corresponding to the actual native full-frame result. -/
def outputBasis (modulus : Nat) (old : (before modulus.size).register.Index) :
    (after modulus.size).register.Index :=
  (InputAssembly.basisEquiv modulus.size).symm
    ((encoding modulus.size).encode
      (InitialFrame.result modulus (inputBasisEquiv modulus.size old)))

/-- Actual preparation followed by the native program has the exact source-result basis action. -/
theorem program_prepared_input (modulus : Nat)
    (old : (before modulus.size).register.Index) :
    (program modulus).applyNormalized
        (NormalizedVector.ket (R := (after modulus.size).register)
          (InputAssembly.assembly modulus.size ((preparation modulus).value, old))) =
      NormalizedVector.ket (R := (after modulus.size).register) (outputBasis modulus old) := by
  have original := InitialFrame.program_initial modulus (inputBasisEquiv modulus.size old)
  have placed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (R := Qubits (encoding modulus.size).width) (S := (after modulus.size).register)
    (InputAssembly.basisEquiv modulus.size).symm (InitialFrame.program modulus) _ _ original
  have initial : (InputAssembly.basisEquiv modulus.size).symm
      ((encoding modulus.size).encode
        (InitialFrame.initial modulus (inputBasisEquiv modulus.size old))) =
        InputAssembly.assembly modulus.size ((preparation modulus).value, old) := by
    apply (InputAssembly.basisEquiv modulus.size).injective
    rw [Equiv.apply_symm_apply]
    exact (InputPreparedFrame.basisEquiv_prepared_initial modulus old).symm
  rw [initial] at placed
  unfold program
  rw [UnitaryCircuit.applyNormalized_seq]
  exact (UnitaryCircuit.applyNormalized_identity (after modulus.size).register
    (after modulus.size).physicalIdx (after modulus.size).identitiesNodup _).trans placed

/-- The native arithmetic is executed by the single live-context unitary instruction. -/
def body (modulus : Nat) : Circuit (after modulus.size) (after modulus.size) :=
  .unitary (program modulus) (program_placement modulus)

/-- The actual circuit performs fixed preparation, native folding, and native length writing. -/
def code (modulus : Nat) : Circuit (before modulus.size) (after modulus.size) :=
  .seq (InputPreparation.circuit modulus) (body modulus)

/-- The actual native preprocessing events survive both exact coordinate transports. -/
theorem program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace = (InitialFrame.program modulus).eventTrace := by
  have empty : (UnitaryCircuit.identity (after modulus.size).register
      (after modulus.size).physicalIdx (after modulus.size).identitiesNodup).eventTrace = [] := rfl
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.reindex_eventTrace,
    empty, List.append_nil]

/-- The actual trace retains preparation, comparison/reflection, and the current length writer. -/
theorem code_eventTrace (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).eventTrace path = (preparation modulus).event ::
      ((FoldSourceProgram.program modulus).eventTrace ++
        (InitialLengthWrite.program modulus.size).eventTrace) := by
  change [(preparation modulus).event] ++ (program modulus).eventTrace = _
  rw [program_eventTrace, InitialFrame.program_eventTrace]
  rfl

variable {Reference : Register} {H : Type} [Fintype H]

/-- Every actual arithmetic block is conjugated by the full local unitary beside the reference. -/
theorem body_block_matrix (modulus : Nat) (state : State (after modulus.size) Reference H)
    (store : Store (after modulus.size)) (history : H) :
    (((body modulus).execute Reference state).block (store, (history, ()))).matrix =
      let operator := UnitaryOperator.prodTensor (program modulus).matrix
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator (Register.prod (after modulus.size).register Reference)) *
        (state.block (store, history)).matrix *
          (operator : HilbertOperator
            (Register.prod (after modulus.size).register Reference)).conjTranspose :=
  Circuit.execute_unitary_block_matrix state (program modulus)
    (program_placement modulus) store history

/-- Actual initialization keeps every input-reference correlation in its full conjugation law. -/
theorem code_quantumMarginal (modulus : Nat) (state : State (before modulus.size) Reference H) :
    ((code modulus).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program modulus).matrix (1 : UnitaryOperator Reference))
        (((InputPreparation.circuit modulus).execute Reference state).quantumMarginal) := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal, body,
    Circuit.execute_unitary]
  simp only [State.unitary, ExecutionState.mapClassical_quantumMarginal]
  exact ExecutionState.fixedUnitary_quantumMarginal _ _

/-- The full external-reference matrix is unchanged by the same actual initialization circuit. -/
theorem code_reference_entry (modulus : Nat) (state : State (before modulus.size) Reference H)
    (left right : Reference.Index) :
    (∑ basis : (after modulus.size).register.Index,
      ((code modulus).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) := by
  rw [code_quantumMarginal]
  exact (DensityOperator.localUnitary_reference_entry (program modulus).matrix
    (((InputPreparation.circuit modulus).execute Reference state).quantumMarginal)
      left right).trans (InputPreparation.execute_reference_entry modulus state left right)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InputRuntime
