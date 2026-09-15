/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Forward
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Inverse
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Native.Resources
import all QuantumAlg.Primitives.MAU.Addition.HRS.IncrementPlacement

/-!
# Actual native coordinates of the complete shared-EEA forward

The source phase instructions and their actual internal controls compile to
literal X, CNOT, and Toffoli lists [LYL+26, sec_EEA/sub_opt.tex:37-75].
The initial fold and final coefficient reflection additionally use the
existing once-controlled Gidney primitives [G17, paper.tex:276-277].

This proves support of the emitted event pool, including all finite
selectors, complete-clock operations, decoder repetitions, physical output
SWAPs, and real X loading and unloading. The alphabet is the existing six
base/once-controlled coordinates, independently of the input modulus or
the program's measured total count. Retained history is not erased from
the program or its accounting [LYL+26, sec_EEA/sub_4phase.tex:119-128].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeSupport

noncomputable section

open EncodedBit

private abbrev Supported {R : Register} (body : UnitaryCircuit R) : Prop :=
  ∀ focus ∈ body.eventCost, focus ∈ Addition.Gidney.offsetAlphabet

private theorem base_mem (focus : Resource.Event .quantum)
    (present : focus ∈ GateSpec.primitiveAlphabet) :
    focus ∈ Addition.Gidney.offsetAlphabet :=
  Multiset.mem_add.mpr (Or.inl present)

private theorem gates_supported {Data : Type} {label : BinaryLabelEncoding Data}
    (gates : List (GateSpec label)) : Supported (GateSpec.programList gates) :=
  fun focus present => base_mem focus (GateSpec.programList_native_support gates focus present)

private theorem seq_supported {R : Register} (left right : UnitaryCircuit R)
    (first : Supported left) (second : Supported right) : Supported (left.seq right) := by
  intro focus present
  rw [UnitaryCircuit.seq_eventCost] at present
  exact (Multiset.mem_add.mp present).elim (first focus) (second focus)

private theorem dagger_supported {R : Register} (body : UnitaryCircuit R)
    (supported : Supported body) : Supported body.dagger := by
  intro focus present
  rw [UnitaryCircuit.dagger_eventCost] at present
  exact supported focus present

private theorem identity_supported (R : Register) (indices : List Nat) (distinct : indices.Nodup) :
    Supported (UnitaryCircuit.identity R indices distinct) := by
  intro focus present
  rw [UnitaryCircuit.identity_eventCost] at present
  simp at present

private theorem iterate_supported {R : Register} (body : UnitaryCircuit R)
    (supported : Supported body) (count : Nat) : Supported (UnitaryCircuit.iterate count body) := by
  have multiples : ∀ count : Nat, ∀ focus ∈ count • body.eventCost,
      focus ∈ Addition.Gidney.offsetAlphabet := by
    intro count
    induction count with
    | zero => simp
    | succ count inductionHypothesis =>
      intro focus present
      rw [succ_nsmul] at present
      exact (Multiset.mem_add.mp present).elim (inductionHypothesis focus) (supported focus)
  exact multiples count

private theorem trace_supported {R S : Register} (body : UnitaryCircuit R)
    (source : UnitaryCircuit S) (same : body.eventTrace = source.eventTrace)
    (supported : Supported source) : Supported body := by
  intro focus present
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, same,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost] at present
  exact supported focus present

private theorem placed_increment (extra width : Nat) :
    Supported (Addition.HRS.placedIncrementProgram extra width) := by
  intro focus present
  rw [(Addition.HRS.hrsPlacedIncrement_resources extra width (fun _ => 1)).1] at present
  exact gates_supported (Addition.HRS.controlledBorrowedIncrementGates width) focus present

private theorem clock (width : Nat) : Supported (ExtendedClockIncrement.program width) :=
  trace_supported _ _ (ExtendedClockIncrement.program_eventTrace width) (placed_increment _ _)

private theorem low (width : Nat) : Supported (LowShiftIncrement.program width) :=
  trace_supported _ _ (LowShiftIncrement.program_eventTrace width) (placed_increment _ _)

private theorem control_place (width : Nat)
    (body : UnitaryCircuit (Qubits (encoding width).width)) (supported : Supported body) :
    Supported (ControlPlacement.place width body) :=
  trace_supported _ _ (ControlPlacement.place_eventTrace width body) supported

private theorem left_pair (width : Nat) : Supported (ControlledShift.leftProgram width) :=
  seq_supported _ _ (control_place width _ (gates_supported _))
    (control_place width _ (clock width))

private theorem right_pair (width : Nat) : Supported (ControlledShift.rightProgram width) :=
  seq_supported _ _ (control_place width _ (gates_supported _))
    (dagger_supported _ (control_place width _ (clock width)))

private theorem guarded (width : Nat) (selected : Bool) :
    Supported (GuardedShift.program width selected) := by
  have first : Supported (GuardedShift.firstProgram width selected) :=
    seq_supported _ _ (gates_supported _)
      (seq_supported _ _ (left_pair width) (gates_supported _))
  have last : Supported (GuardedShift.lastProgram width selected) :=
    seq_supported _ _ (gates_supported _)
      (seq_supported _ _ (seq_supported _ _ (right_pair width) (right_pair width))
        (gates_supported _))
  exact seq_supported _ _ first last

private theorem selector_body {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (coefficient : Bool) :
    Supported (ArithmeticSelector.controlledBody window operation coefficient) := by
  cases coefficient with
  | false =>
    exact trace_supported _ _
      ((ArithmeticWindowControl.program_eventTrace window operation).trans
        (GateSpec.programList_eventTrace _).symm) (gates_supported _)
  | true =>
    exact trace_supported _ _
      ((CoefficientWindowProgram.controlledProgram_eventTrace window operation).trans
        (GateSpec.programList_eventTrace _).symm) (gates_supported _)

private theorem selector {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (coefficient : Bool)
    (selected : ArithmeticSelectionKey.Key width
      (ArithmeticWindowPreservation.readsSign operation)) :
    Supported (ArithmeticSelector.program window operation coefficient selected) :=
  seq_supported _ _ (gates_supported _)
    (seq_supported _ _ (selector_body window operation coefficient) (gates_supported _))

private theorem instruction (width : Nat) (instruction : ArithmeticInstruction.Instruction)
    (selected : ArithmeticSelectionKey.Key width (ArithmeticInstruction.includeSign instruction)) :
    Supported (ArithmeticInstruction.program width instruction selected) := by
  unfold ArithmeticInstruction.program
  split
  · cases choice : ArithmeticInstruction.selectedWindow instruction selected with
    | none => exact identity_supported _ _ _
    | some window => exact selector window _ _ selected
  · exact identity_supported _ _ _

private theorem arithmetic_list (width : Nat) (instruction : ArithmeticInstruction.Instruction)
    (indices : List (ArithmeticSelectionKey.Key width
      (ArithmeticInstruction.includeSign instruction))) :
    Supported (ArithmeticSchedule.listProgram width instruction indices) := by
  induction indices with
  | nil => exact identity_supported _ _ _
  | cons selected rest inductionHypothesis =>
    exact seq_supported _ _ (NativeSupport.instruction width instruction selected)
      inductionHypothesis

private theorem arithmetic (width : Nat) (instruction : ArithmeticInstruction.Instruction) :
    Supported (ArithmeticSchedule.program width instruction) := arithmetic_list width instruction _

private theorem remainder (width : Nat) : Supported (ArithmeticBlocks.remainderProgram width) :=
  seq_supported _ _ (arithmetic width .remainderSubtract)
    (seq_supported _ _ (gates_supported _) (arithmetic width .remainderAddback))

private theorem coefficient (width : Nat) : Supported (ArithmeticBlocks.coefficientProgram width) :=
  seq_supported _ _ (arithmetic width .coefficientSubtract)
    (seq_supported _ _ (gates_supported _) (arithmetic width .coefficientAdd))

private theorem quotient (width : Nat) : Supported (PhaseQuotient.program width) := by
  have increment : Supported (QuotientIncrement.program width) :=
    trace_supported _ _ (QuotientIncrement.program_eventTrace width) (low width)
  have body : Supported (PhaseQuotient.bodyProgram width) :=
    seq_supported _ _ (gates_supported _) (seq_supported _ _ increment (gates_supported _))
  exact seq_supported _ _ (gates_supported _) (seq_supported _ _ body (gates_supported _))

private theorem signQuotient (width : Nat) : Supported (SignQuotient.program width) :=
  seq_supported _ _ (gates_supported _) (quotient width)

/-- The complete eight-block microstep emits only the independently declared native coordinates. -/
theorem microstep (width : Nat) (enough : 2 ≤ width.size)
    (focus : Resource.Event .quantum)
    (present : focus ∈ (NativeMicrostep.program width enough).eventCost) :
    focus ∈ Addition.Gidney.offsetAlphabet := by
  have supported : Supported (NativeMicrostep.program width enough) :=
    seq_supported _ _ (guarded width false)
      (seq_supported _ _ (remainder width)
        (seq_supported _ _ (signQuotient width)
          (seq_supported _ _ (coefficient width)
            (seq_supported _ _ (guarded width true)
              (seq_supported _ _ (gates_supported _)
                (seq_supported _ _ (gates_supported _) (gates_supported _)))))))
  exact supported focus present

private theorem flag (width : Nat) : Supported (Addition.Gidney.flagFlipProgram width) := by
  intro focus present
  rw [Addition.Gidney.gidneyFlagFlip_eventCost] at present
  have same : focus = .gate (.builtin "x") := by
    simpa [ResourcePool.singleton] using present
  rw [same]
  apply base_mem
  simp [GateSpec.primitiveAlphabet, ResourcePool.ofList]

private theorem comparison (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    Supported (Addition.Gidney.comparisonProgram width pivot) :=
  fun focus present => base_mem focus
    (Addition.Gidney.gidneyComparison_native_support width pivot focus present)

private theorem reflection (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    Supported (Addition.Gidney.biFlipProgram width pivot) :=
  fun focus present => Multiset.mem_add.mpr (Or.inr
    (Addition.Gidney.gidneyBiFlip_native_support width pivot focus present))

private theorem fold_source (modulus : Nat) : Supported (FoldSourceProgram.program modulus) :=
  seq_supported _ _ (seq_supported _ _ (comparison _ _) (flag _)) (reflection _ _)

private theorem initial (modulus : Nat) : Supported (InitialFrame.program modulus) :=
  seq_supported _ _
    (trace_supported _ _ (FoldProgram.program_eventTrace modulus) (fold_source modulus))
    (gates_supported _)

private theorem native (modulus : Nat) (nontrivial : 1 < modulus) :
    Supported (NativeSchedule.program modulus nontrivial) :=
  seq_supported _ _ (initial modulus)
    (iterate_supported _ (microstep modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)) _)

private theorem decoder_list (width : Nat) (indices : List (Fin (width.size + 2))) :
    Supported (ClockDecode.sequence width indices) := by
  induction indices with
  | nil => exact gates_supported _
  | cons index rest inductionHypothesis =>
    exact seq_supported _ _ (iterate_supported _ (gates_supported _) _) inductionHypothesis

private theorem correction (modulus : Nat) : Supported (OutputCorrection.program modulus) :=
  trace_supported _ _ (OutputCorrection.program_eventTrace modulus)
    (seq_supported _ _ (seq_supported _ _ (flag _) (reflection _ _)) (flag _))

/-- The actual forward, decoder, and parity correction preserve this finite event support. -/
theorem corrected (modulus : Nat) (nontrivial : 1 < modulus)
    (focus : Resource.Event .quantum)
    (present : focus ∈ (CorrectedSchedule.program modulus nontrivial).eventCost) :
    focus ∈ Addition.Gidney.offsetAlphabet :=
  seq_supported _ _ (seq_supported _ _ (native modulus nontrivial) (decoder_list modulus.size _))
    (correction modulus) focus present

/-- Real loading and output-port gates add no native coordinate outside the same alphabet. -/
theorem inPlace (modulus : Nat) (nontrivial : 1 < modulus)
    (focus : Resource.Event .quantum)
    (present : focus ∈ (InPlaceForward.program modulus nontrivial).eventCost) :
    focus ∈ Addition.Gidney.offsetAlphabet :=
  seq_supported _ _ (gates_supported _)
    (seq_supported _ _ (corrected modulus nontrivial) (gates_supported _)) focus present

/-- The same full dagger retains all coordinates, including the cleanup of retained history. -/
theorem inPlace_dagger (modulus : Nat) (nontrivial : 1 < modulus)
    (focus : Resource.Event .quantum)
    (present : focus ∈ (InPlaceForward.program modulus nontrivial).dagger.eventCost) :
    focus ∈ Addition.Gidney.offsetAlphabet :=
  dagger_supported _ (inPlace modulus nontrivial) focus present

/-- The standalone XOR interface additionally emits the actual copy and the entire same dagger. -/
theorem xor (modulus : Nat) (nontrivial : 1 < modulus)
    (focus : Resource.Event .quantum)
    (present : focus ∈ (NativeInverse.program modulus nontrivial).eventCost) :
    focus ∈ Addition.Gidney.offsetAlphabet := by
  have forward : Supported (NativeInverse.forwardProgram modulus nontrivial) := by
    intro event membership
    have ledger : (NativeInverse.forwardProgram modulus nontrivial).eventCost =
        (CorrectedSchedule.program modulus nontrivial).eventCost :=
      UnitaryCircuit.prodLeft_eventCost (n := modulus.size)
        (CorrectedSchedule.program modulus nontrivial)
    exact corrected modulus nontrivial event (ledger ▸ membership)
  exact seq_supported _ _ forward
    (seq_supported _ _ (gates_supported _) (dagger_supported _ forward)) focus present

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeSupport
