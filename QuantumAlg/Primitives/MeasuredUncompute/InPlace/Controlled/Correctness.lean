/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Native
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Layout
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.BodyState
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap.Readout
import all QuantumAlg.Primitives.MeasuredUncompute.Product.Placement

/-!
# Complete native columns of controlled measured arithmetic

The inactive sector saves the arbitrary original numerator in the existing
accumulator, uses the actual measured mask to cancel its Walsh phase, and
restores the entire original frame with the literal final swap. The active
sector retains the original prime-field contract, including zero numerator.
The coherent-control extension is a project construction over the measured
arithmetic of [LYL+26, sec_point_add/sec_point_add.tex:52-121].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open Execution MAU.Inversion.SharedEEA ProductPlacement ProductReadout

local instance {α : Type} : DecidableEq α := Classical.decEq α
private def controlLabel (active : Bool) : Fin 2 := if active then 1 else 0

private theorem four_actions {R : Register} {A B C D : HilbertOperator R}
    {v₀ v₁ v₂ v₃ v₄ : HilbertVector R} {a b c d : ℂ}
    (first : A.applyVec v₀ = a • v₁) (second : B.applyVec v₁ = b • v₂)
    (third : C.applyVec v₂ = c • v₃) (fourth : D.applyVec v₃ = d • v₄) :
    HilbertOperator.applyVec (D * C * B * A) v₀ = (a * b * c * d) • v₄ := by
  simp only [HilbertOperator.mul_applyVec, first, HilbertOperator.applyVec_smul,
    second, third, fourth, smul_smul, mul_assoc]

/-- The complete frame transformation of the literal inactive CNOT bank. -/
def copyStep (width : Nat) (state : Frame width) : Frame width :=
  EncodedBit.Word.xorIntoStep (FramePorts.numerator width) (FramePorts.accumulator width)
    (fun index => (FramePorts.accumulator_numerator_ne width index index).symm) state

private theorem copy_input (width : Nat) (state : Frame width) :
    input width (copyStep width state) = input width state := by
  apply word_ext
  intro index
  simp only [input, readWord_bit]
  exact EncodedBit.Word.xorIntoStep_get_observed_of_target_ne _ _ _
    ((FramePorts.input width).bit index)
    (fun other => (FramePorts.input_separate width index other).1.symm) state

private theorem copy_numerator (width : Nat) (state : Frame width) :
    numerator width (copyStep width state) = numerator width state := by
  apply word_ext
  intro index
  simp only [numerator, readWord_bit]
  exact EncodedBit.Word.xorIntoStep_get_observed_of_target_ne _ _ _
    ((FramePorts.numerator width).bit index)
    (fun other => FramePorts.accumulator_numerator_ne width other index) state

private theorem copy_accumulator (width : Nat) (state : Frame width)
    (clean : accumulator width state = 0) :
    accumulator width (copyStep width state) = numerator width state := by
  apply word_ext
  intro index
  simp only [accumulator, numerator, readWord_bit]
  rw [copyStep, EncodedBit.Word.xorIntoStep_get_target _ _ _ index
    (fun other different => FramePorts.accumulator_distinct width other index different)
    (fun other => FramePorts.accumulator_numerator_ne width other index)]
  have zero := congrArg (fun value : Fin (2 ^ width) => value.val.testBit index.rev.val) clean
  rw [accumulator, readWord_bit] at zero
  rw [zero]
  simp

private theorem copy_history (width : Nat) (state : Frame width) :
    history width (copyStep width state) = history width state := by
  apply word_ext
  intro index
  simp only [history, BinaryBasis.bigEndianEquiv_bit, Equiv.apply_symm_apply]
  have actual := EncodedBit.Word.xorIntoStep_get_observed_of_target_ne
    (FramePorts.numerator width) (FramePorts.accumulator width)
    (fun selected => (FramePorts.accumulator_numerator_ne width selected selected).symm)
    (FrameSwapReadout.historyBit width index)
    (fun selected => by
      intro same
      have values := congrArg (fun wire : Fin (frameEncoding width).width => wire.val) same
      rw [FramePorts.accumulator_wire] at values
      have within := selected.isLt
      change selected.val =
        if index.val < 6 then width + index.val else 2 * width + index.val at values
      split_ifs at values <;> omega) state
  rw [bit_read, bit_read] at actual
  exact actual

/-- Actual reset after the inactive copy retains every original X and history coordinate. -/
theorem inactive_reset_frame (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) :
    ((copyStep modulus.size (InitialPortProgram.inputFrame modulus value, numerator)).1, 0) =
      (WorkspaceReuse.placement modulus.size).grouping.symm
        (InitialPortProgram.inputFrame modulus value, numerator) := by
  let original : Frame modulus.size := (InitialPortProgram.inputFrame modulus value, numerator)
  let copied := copyStep modulus.size original
  have clean := InPlaceArithmetic.initial_accumulator modulus value numerator
  have saved := (copy_accumulator modulus.size original clean).trans (numerator_eq _ _)
  apply ProductPortLaws.frame_ext
  · rw [ReusedProductReadout.input_symm]
    exact (InPlaceArithmetic.input_pair modulus.size copied.1 0 copied.2).trans
      (copy_input modulus.size original)
  · rw [numerator_eq, ReusedProductReadout.numerator_symm]
    exact clean.symm
  · rw [ReusedProductReadout.accumulator_symm, numerator_eq]
    exact (InPlaceArithmetic.accumulator_pair modulus.size copied.1 0 copied.2).trans saved
  · rw [ReusedProductReadout.history_symm]
    exact (InPlaceArithmetic.history_pair modulus.size copied.1 0 copied.2).trans
      (copy_history modulus.size original)

/-- The inactive correction reads the saved Y in the actual little-endian measurement order. -/
theorem inactive_mask_reads (width : Nat) (state : Frame width) (index : Fin width) :
    ((inactiveWord width).bit index).get
      ((WorkspaceReuse.placement width).grouping.symm state) =
        (numerator width state).val.testBit index.val := by
  have read := readWord_bit (FramePorts.accumulator width)
    ((WorkspaceReuse.placement width).grouping.symm state) index.rev
  rw [Fin.rev_rev] at read
  change (accumulator width ((WorkspaceReuse.placement width).grouping.symm state)).val.testBit
    index.val = _ at read
  rw [ReusedProductReadout.accumulator_symm] at read
  exact read.symm

/-- The inactive sector's actual native and retained-measurement operator, in emitted order. -/
def inactiveOperator (width : Nat) (Reference : Register)
    (stored : Store (NumeratorMeasurement.context width)) :
    HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference) :=
  (InPlaceDivisionConjugation.native width Reference (FrameSwap.program width) :
      HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference)) *
    (InPlaceDivisionConjugation.native width Reference
      (inactiveMask width (stored.read (NumeratorMeasurement.input width))) :
      HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference)) *
    NumeratorResetConjugation.operator width Reference stored *
    (InPlaceDivisionConjugation.native width Reference (copy width) :
      HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference))

/-- Every inactive measured column has the same positive amplitude, for arbitrary X and Y. -/
theorem inactive_operator_ket (modulus : Nat) (value numerator : Fin (2 ^ modulus.size))
    {Reference : Register} (stored : Store (NumeratorMeasurement.context modulus.size))
    (reference : Reference.Index) :
    (inactiveOperator modulus.size Reference stored).applyVec
      (NumeratorFrameBasis.ket modulus.size
        (InitialPortProgram.inputFrame modulus value, numerator) reference).vec =
      WalshHadamard.invSqrtCard modulus.size •
        (NumeratorFrameBasis.ket modulus.size
          (InitialPortProgram.inputFrame modulus value, numerator) reference).vec := by
  let original : Frame modulus.size := (InitialPortProgram.inputFrame modulus value, numerator)
  let copied := copyStep modulus.size original
  let recovered := (WorkspaceReuse.placement modulus.size).grouping.symm original
  have copyRealizes := EncodedBit.Word.xorInto_realizes (QubitLayout.canonical _) .empty
    (FramePorts.numerator modulus.size)
    (FramePorts.accumulator modulus.size)
    (fun index => (FramePorts.accumulator_numerator_ne modulus.size index index).symm)
  have copiedNative := copyRealizes.apply_encoded_ket original
  have copiedAction := NumeratorFrameBasis.native_normalized modulus.size
    (copy modulus.size) original copied copiedNative reference
  have numeratorKept : copied.2 = numerator := by
    have actual := copy_numerator modulus.size original
    rw [numerator_eq, numerator_eq] at actual
    exact actual
  have measured : (NumeratorResetConjugation.operator modulus.size Reference stored).applyVec
      (NumeratorFrameBasis.ket modulus.size copied reference).vec =
      (WalshHadamard.invSqrtCard modulus.size *
        WalshHadamard.walshSign
          (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size)))
          numerator) • (NumeratorFrameBasis.ket modulus.size recovered reference).vec := by
    have actual := NumeratorBranchAction.operator_ket modulus.size stored
      (NumeratorFrameBasis.basis modulus.size copied) reference
    rw [NumeratorFrameBasis.word, NumeratorFrameBasis.replace, numeratorKept] at actual
    rw [inactive_reset_frame modulus value numerator] at actual
    exact actual
  have mask : QubitReadouts.mask (stored.read (NumeratorMeasurement.input modulus.size)) =
      (fun index =>
        (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size))).val.testBit
          index.val) := by
    funext index
    exact (NumeratorReset.outcome_bit _ index).symm
  have correctionNative :
      (inactiveMask modulus.size (stored.read (NumeratorMeasurement.input modulus.size))).applyVec
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode recovered))).vec =
      WalshHadamard.walshSign
        (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size))) numerator •
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode recovered))).vec := by
    have sign := measuredCorrection_sign_walsh (inactiveWord modulus.size) recovered numerator
      (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size)))
      (fun index => (inactive_mask_reads modulus.size original index).trans
        (congrArg (fun word : Fin (2 ^ modulus.size) => word.val.testBit index.val)
          (numerator_eq modulus.size original)))
    have actual := EncodedBit.Word.PhaseCorrection.phaseCorrection_sequence_ket
      (QubitLayout.canonical _) .empty (inactiveWord modulus.size)
      (EncodedBit.Word.PhaseCorrection.selected (fun index =>
        (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size))).val.testBit
          index.val)) recovered
    rw [sign, ← mask] at actual
    exact actual
  have correctionAction := NumeratorFrameBasis.native_action modulus.size
    (inactiveMask modulus.size (stored.read (NumeratorMeasurement.input modulus.size)))
    recovered recovered
    (WalshHadamard.walshSign
      (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size))) numerator)
    correctionNative reference
  have swapAction := NumeratorFrameBasis.native_normalized modulus.size
    (FrameSwap.program modulus.size) recovered original
    (FrameSwapReadout.program_reused_ket modulus.size original) reference
  have combined := four_actions (copiedAction.trans (one_smul ℂ _).symm) measured correctionAction
    (swapAction.trans (one_smul ℂ _).symm)
  have scalar : (1 : ℂ) *
      (WalshHadamard.invSqrtCard modulus.size *
        WalshHadamard.walshSign
          (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size)))
            numerator) *
      WalshHadamard.walshSign
        (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input modulus.size)))
          numerator * 1 =
      WalshHadamard.invSqrtCard modulus.size := by
    rw [one_mul, mul_one, mul_assoc, WalshHadamard.walshSign_mul_self, mul_one]
  exact combined.trans (congrArg (fun coefficient : ℂ => coefficient •
    (NumeratorFrameBasis.ket modulus.size original reference).vec) scalar)

/-- Exact complete-register coordinates place the owned control beside the original joint state. -/
def jointCoordinates (width : Nat) (Reference : Register) :
    (Register.prod (context width).register Reference).Index ≃
      ((Register.prod (NumeratorMeasurement.context width).register Reference).Index × Fin 2) :=
  ((ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width) (controlContext width)
    (control_disjoint width)).prodCongr (Equiv.refl Reference.Index)).trans
      ((Equiv.prodAssoc _ _ _).trans
        ((Equiv.prodCongr (Equiv.refl _)
          ((Equiv.prodComm _ _).trans
            ((Equiv.refl Reference.Index).prodCongr (controlBasis width)))).trans
          (Equiv.prodAssoc _ _ _).symm))

theorem jointCoordinates_label (width : Nat) (Reference : Register) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index)
    (reference : Reference.Index) :
    jointCoordinates width Reference (label width control original, reference) =
      ((original, reference), control) := by
  change
    ((((ContextUnion.unionBasisEquiv _ _ (control_disjoint width))
      ((ContextUnion.unionBasisEquiv _ _ (control_disjoint width)).symm
        (original, (controlBasis width).symm control))).1, reference),
      controlBasis width ((ContextUnion.unionBasisEquiv _ _ (control_disjoint width))
        ((ContextUnion.unionBasisEquiv _ _ (control_disjoint width)).symm
          (original, (controlBasis width).symm control))).2) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem label_surjective (width : Nat) (value : (context width).register.Index) :
    ∃ (control : Fin 2) (original : (NumeratorMeasurement.context width).register.Index),
      label width control original = value := by
  let parts := ContextUnion.unionBasisEquiv _ _ (control_disjoint width) value
  refine ⟨controlBasis width parts.2, parts.1, ?_⟩
  change (ContextUnion.unionBasisEquiv _ _ (control_disjoint width)).symm
    (parts.1, (controlBasis width).symm (controlBasis width parts.2)) = _
  rw [Equiv.symm_apply_apply]
  exact (ContextUnion.unionBasisEquiv _ _ (control_disjoint width)).symm_apply_apply value

/-- Both exact control sectors retain the whole original quantum-reference matrix. -/
def controlBlocks (width : Nat) (Reference : Register)
    (members : Fin 2 →
      HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference)) :
    HilbertOperator (Register.prod (context width).register Reference) :=
  (Matrix.blockDiagonal members).submatrix
    (jointCoordinates width Reference) (jointCoordinates width Reference)

theorem controlBlocks_entry (width : Nat) (Reference : Register)
    (members : Fin 2 →
      HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference))
    (rowControl columnControl : Fin 2)
    (row column : (NumeratorMeasurement.context width).register.Index)
    (rowReference columnReference : Reference.Index) :
    controlBlocks width Reference members (label width rowControl row, rowReference)
      (label width columnControl column, columnReference) =
      if rowControl = columnControl then
        members rowControl (row, rowReference) (column, columnReference) else 0 := by
  rw [controlBlocks, Matrix.submatrix_apply, jointCoordinates_label, jointCoordinates_label,
    Matrix.blockDiagonal_apply]

/-- Exact matrix multiplication retains all cross-control blocks before any support restriction. -/
theorem controlBlocks_mul (width : Nat) (Reference : Register)
    (left right : Fin 2 →
      HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference)) :
    controlBlocks width Reference left * controlBlocks width Reference right =
      controlBlocks width Reference (fun control => left control * right control) := by
  rw [controlBlocks, controlBlocks, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  rfl

/-- The independent original word permutation is activated by the actual quantum control. -/
def target (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register) : UnitaryOperator (Register.prod (context modulus.size).register
      Reference) :=
  UnitaryOperator.reindex
    (R := Register.prod (Qubits 1)
      (Register.prod (NumeratorMeasurement.context modulus.size).register Reference))
    (S := Register.prod (context modulus.size).register Reference)
    ((jointCoordinates modulus.size Reference).trans (Equiv.prodComm _ _)).symm
    (UnitaryOperator.controlled (Qubits 1) (1 : Fin 2)
      (InPlaceTarget.jointOperator operation modulus prime Reference))

/-- The target is independent arithmetic on control one and complete identity on control zero. -/
theorem target_blocks (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) :
    (target operation modulus prime Reference :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control =>
        if control = 1 then
          (InPlaceTarget.jointOperator operation modulus prime Reference :
            HilbertOperator
              (Register.prod (NumeratorMeasurement.context modulus.size).register Reference))
        else 1) := by
  rfl

private def nativeBasisEquiv (width : Nat) :
    (context width).register.Index ≃ (nativeLayout width).toQuantum.register.Index :=
  (Equiv.piCongr
    (Equiv.ofBijective (nativePosition width)
      ⟨(nativePosition width).injective, nativePosition_surjective width⟩)
    (fun index => finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
      (nativePosition_dimensions width index)))).symm

private theorem nativeBasisEquiv_apply (width : Nat)
    (state : (context width).register.Index) :
    nativeBasisEquiv width state = nativeBasis width state := by
  funext index
  apply Fin.ext
  rfl

private theorem native_placed_matrix (width : Nat) (program : NativeCircuit width) :
    ((runtimeProgram width program).matrix : HilbertOperator (context width).register) =
      (program.matrix : HilbertOperator (nativeLayout width).toQuantum.register).submatrix
        (nativeBasisEquiv width) (nativeBasisEquiv width) := by
  ext row column
  simpa only [Matrix.submatrix_apply, nativeBasisEquiv_apply] using
    runtimeProgram_matrix width program row column

/-- The actual placed native member acts on the complete joint reference register. -/
def nativeJoint (width : Nat) (Reference : Register) (program : NativeCircuit width) :
    UnitaryOperator (Register.prod (context width).register Reference) :=
  UnitaryOperator.prodTensor (runtimeProgram width program).matrix (1 : UnitaryOperator Reference)

private theorem nativeJoint_seq (width : Nat) (Reference : Register)
    (first second : NativeCircuit width) :
    (nativeJoint width Reference (first.seq second) :
      HilbertOperator (Register.prod (context width).register Reference)) =
      (nativeJoint width Reference second :
        HilbertOperator (Register.prod (context width).register Reference)) *
      (nativeJoint width Reference first :
        HilbertOperator (Register.prod (context width).register Reference)) := by
  change Matrix.kronecker
      ((runtimeProgram width (first.seq second)).matrix :
        HilbertOperator (context width).register) (1 : HilbertOperator Reference) =
    Matrix.kronecker ((runtimeProgram width second).matrix :
      HilbertOperator (context width).register) (1 : HilbertOperator Reference) *
    Matrix.kronecker ((runtimeProgram width first).matrix :
      HilbertOperator (context width).register) (1 : HilbertOperator Reference)
  rw [native_placed_matrix, native_placed_matrix, native_placed_matrix,
    UnitaryCircuit.seq_matrix]
  have actual := Matrix.mul_kronecker_mul
    ((second.matrix : HilbertOperator (nativeLayout width).toQuantum.register).submatrix
      (nativeBasisEquiv width) (nativeBasisEquiv width))
    ((first.matrix : HilbertOperator (nativeLayout width).toQuantum.register).submatrix
      (nativeBasisEquiv width) (nativeBasisEquiv width))
    (1 : HilbertOperator Reference) (1 : HilbertOperator Reference)
  rw [Matrix.submatrix_mul_equiv, Matrix.one_mul] at actual
  exact actual

private theorem realized_binary_entry {Data : Type} (encoding : BinaryLabelEncoding Data)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum) (step : Data → Data)
    (realized : UnitaryCircuit.Realizes encoding program step)
    (row : Fin (2 ^ encoding.width)) (column : Data) :
    program.binaryMatrix row (encoding.encode column) =
      if row = encoding.encode (step column) then 1 else 0 := by
  have action := UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
    program (encoding.encode column) (encoding.encode (step column))
    (realized.apply_encoded_ket column)
  have entry := congrArg (fun state => state.vec row) action
  change program.binaryMatrix.applyVec
    (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode column)).vec row =
    NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode (step column)) row at entry
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] at entry
  exact entry

private theorem encoded_pair_eq (width : Nat)
    (row : Fin (2 ^ (frameEncoding width).width)) (rowControl : Fin 2)
    (state : Frame width × Bool) :
    prodEquiv (row, rowControl) = (NativeFrameControl.encoding width).encode state ↔
      row = (frameEncoding width).encode state.1 ∧ rowControl = controlLabel state.2 := by
  change (prodEquiv (m := (frameEncoding width).width) (n := 1)) (row, rowControl) =
    (prodEquiv (m := (frameEncoding width).width) (n := 1))
      ((frameEncoding width).encode state.1, controlLabel state.2) ↔ _
  refine (prodEquiv (m := (frameEncoding width).width) (n := 1)).injective.eq_iff.trans ?_
  constructor
  · intro same
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
  · intro same
    exact Prod.ext same.1 same.2

private theorem conditional_matrix (width : Nat) (active : Bool)
    (program : NativeCircuit width)
    (source : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (step : Frame width → Frame width)
    (actual : UnitaryCircuit.Realizes (NativeFrameControl.encoding width) program
      (NativeFrameControl.step width active step))
    (original : UnitaryCircuit.Realizes (frameEncoding width) source step)
    (rowControl columnControl : Fin 2) (row column : Fin (2 ^ (frameEncoding width).width)) :
    program.binaryMatrix (prodEquiv (row, rowControl)) (prodEquiv (column, columnControl)) =
      if rowControl = columnControl then
        if rowControl = controlLabel active then source.binaryMatrix row column
        else if row = column then 1 else 0
      else 0 := by
  obtain ⟨state, rfl⟩ := ProductPlacement.frame_total width column
  have selected : ∃ selected, controlLabel selected = columnControl := by
    fin_cases columnControl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨selected, rfl⟩ := selected
  have controlledEntry := realized_binary_entry (NativeFrameControl.encoding width) program
    (NativeFrameControl.step width active step) actual (prodEquiv (row, rowControl))
    (state, selected)
  have sourceEntry := realized_binary_entry (frameEncoding width) source step original row state
  change program.binaryMatrix (prodEquiv (row, rowControl))
    (prodEquiv ((frameEncoding width).encode state, controlLabel selected)) = _
      at controlledEntry
  have nativeEntry := controlledEntry.trans
    (if_congr (encoded_pair_eq width row rowControl
      (NativeFrameControl.step width active step (state, selected)))
      (rfl : (1 : ℂ) = 1) (rfl : (0 : ℂ) = 0))
  erw [nativeEntry, sourceEntry]
  cases active <;> cases selected <;> fin_cases rowControl <;>
    simp [NativeFrameControl.step, controlLabel]

private theorem controlled_blocks_of_entries (width : Nat) (Reference : Register) (active : Bool)
    (program : NativeCircuit width)
    (source : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (entries : ∀ (rowControl columnControl : Fin 2)
      (row column : Fin (2 ^ (frameEncoding width).width)),
      program.binaryMatrix (prodEquiv (row, rowControl)) (prodEquiv (column, columnControl)) =
        if rowControl = columnControl then
          if rowControl = controlLabel active then source.binaryMatrix row column
          else if row = column then 1 else 0
        else 0) :
    (nativeJoint width Reference program :
      HilbertOperator (Register.prod (context width).register Reference)) =
      controlBlocks width Reference (fun control =>
        if control = controlLabel active then
          (InPlaceDivisionConjugation.native width Reference source :
            HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference))
        else 1) := by
  ext ⟨row, rowReference⟩ ⟨column, columnReference⟩
  obtain ⟨rowControl, originalRow, rfl⟩ := label_surjective width row
  obtain ⟨columnControl, originalColumn, rfl⟩ := label_surjective width column
  rw [controlBlocks_entry]
  change UnitaryOperator.prodTensor _ _ _ _ = _
  rw [UnitaryOperator.prodTensor_apply]
  have placed : (runtimeProgram width program).matrix
      (label width rowControl originalRow) (label width columnControl originalColumn) =
      program.binaryMatrix
        (prodEquiv (NumeratorMeasurement.frameBasis width originalRow, rowControl))
        (prodEquiv (NumeratorMeasurement.frameBasis width originalColumn, columnControl)) := by
    rw [runtimeProgram_matrix, controlledNativeBasis_label, controlledNativeBasis_label]
    rfl
  erw [placed, entries]
  have equal : NumeratorMeasurement.frameBasis width originalRow =
      NumeratorMeasurement.frameBasis width originalColumn ↔ originalRow = originalColumn :=
    (NumeratorMeasurement.frameBasis width).injective.eq_iff
  by_cases sameControl : rowControl = columnControl
  · subst columnControl
    by_cases enabled : rowControl = controlLabel active
    · simp only [ite_true, if_pos enabled]
      exact (congrArg (fun value : ℂ => value *
        (1 : HilbertOperator Reference) rowReference columnReference)
        (NumeratorRuntime.program_binary_matrix width source originalRow originalColumn)).symm
    · simp only [ite_true, if_neg enabled]
      change (if NumeratorMeasurement.frameBasis width originalRow =
          NumeratorMeasurement.frameBasis width originalColumn then (1 : ℂ) else 0) *
        (if rowReference = columnReference then 1 else 0) =
        if (originalRow, rowReference) = (originalColumn, columnReference) then 1 else 0
      simp only [equal]
      by_cases sameOriginal : originalRow = originalColumn <;>
        by_cases sameReference : rowReference = columnReference <;>
        simp [sameOriginal, sameReference]
  · simp only [if_neg sameControl, zero_mul]

/-- The exact all-label action of an emitted member determines both coherent control sectors. -/
theorem controlled_blocks (width : Nat) (Reference : Register) (active : Bool)
    (program : NativeCircuit width)
    (source : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (step : Frame width → Frame width)
    (actual : UnitaryCircuit.Realizes (NativeFrameControl.encoding width) program
      (NativeFrameControl.step width active step))
    (original : UnitaryCircuit.Realizes (frameEncoding width) source step) :
    (nativeJoint width Reference program :
      HilbertOperator (Register.prod (context width).register Reference)) =
      controlBlocks width Reference (fun control =>
        if control = controlLabel active then
          (InPlaceDivisionConjugation.native width Reference source :
            HilbertOperator (Register.prod (NumeratorMeasurement.context width).register Reference))
        else 1) :=
  controlled_blocks_of_entries width Reference active program source
    (conditional_matrix width active program source step actual original)

private theorem diagonal_binary_entry {Data : Type} (encoding : BinaryLabelEncoding Data)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum) (phase : Data → ℂ)
    (action : ∀ state, program.applyVec
      (NormalizedVector.ket ((QubitLayout.canonical encoding.width).basisEquiv.symm
        (encoding.encode state))).vec =
      phase state • (NormalizedVector.ket
        ((QubitLayout.canonical encoding.width).basisEquiv.symm (encoding.encode state))).vec)
    (row : Fin (2 ^ encoding.width)) (column : Data) :
    program.binaryMatrix row (encoding.encode column) =
      phase column * (if row = encoding.encode column then 1 else 0) := by
  have entry := congrArg
    (fun vector => vector ((QubitLayout.canonical encoding.width).basisEquiv.symm row))
    (action column)
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply] at entry
  have same := (QubitLayout.canonical encoding.width).basisEquiv.symm.injective.eq_iff
    (a := row) (b := encoding.encode column)
  erw [UnitaryCircuit.binaryMatrix_eq_reindex, UnitaryOperator.coe_reindex]
  change program.matrix ((QuantumSignature.qubitsIndexEquiv encoding.width).symm row)
    ((QuantumSignature.qubitsIndexEquiv encoding.width).symm (encoding.encode column)) = _
  have normalized := entry
  simp only [same] at normalized
  simpa only [QubitLayout.basisEquiv] using normalized

private theorem conditional_phase_matrix (width : Nat) (active : Bool)
    (program : NativeCircuit width)
    (source : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (phase : Frame width → ℂ)
    (actual : ∀ state : Frame width × Bool, program.applyVec
      (NormalizedVector.ket ((nativeLayout width).basisEquiv.symm
        ((NativeFrameControl.encoding width).encode state))).vec =
      (if state.2 = active then phase state.1 else 1) •
        (NormalizedVector.ket ((nativeLayout width).basisEquiv.symm
          ((NativeFrameControl.encoding width).encode state))).vec)
    (original : ∀ state : Frame width, source.applyVec
      (NormalizedVector.ket ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
        ((frameEncoding width).encode state))).vec =
      phase state • (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
          ((frameEncoding width).encode state))).vec)
    (rowControl columnControl : Fin 2) (row column : Fin (2 ^ (frameEncoding width).width)) :
    program.binaryMatrix (prodEquiv (row, rowControl)) (prodEquiv (column, columnControl)) =
      if rowControl = columnControl then
        if rowControl = controlLabel active then source.binaryMatrix row column
        else if row = column then 1 else 0
      else 0 := by
  obtain ⟨state, rfl⟩ := ProductPlacement.frame_total width column
  have selected : ∃ selected, controlLabel selected = columnControl := by
    fin_cases columnControl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨selected, rfl⟩ := selected
  have controlledEntry := diagonal_binary_entry (NativeFrameControl.encoding width) program
    (fun state => if state.2 = active then phase state.1 else 1) actual
    (prodEquiv (row, rowControl)) (state, selected)
  have sourceEntry := diagonal_binary_entry (frameEncoding width) source phase original row state
  change program.binaryMatrix (prodEquiv (row, rowControl))
    (prodEquiv ((frameEncoding width).encode state, controlLabel selected)) = _
      at controlledEntry
  have nativeEntry := controlledEntry.trans
    (congrArg (fun coefficient : ℂ =>
      (if selected = active then phase state else 1) * coefficient)
      (if_congr (encoded_pair_eq width row rowControl (state, selected))
        (rfl : (1 : ℂ) = 1) (rfl : (0 : ℂ) = 0)))
  erw [nativeEntry, sourceEntry]
  cases active <;> cases selected <;> fin_cases rowControl <;>
    simp [controlLabel]

private theorem native_blocks_of_entries (width : Nat) (Reference : Register)
    (program : NativeCircuit width)
    (members : Fin 2 → UnitaryCircuit AlgorithmGate.model .empty
      (InverseRuntimeFrame.source width))
    (entries : ∀ (rowControl columnControl : Fin 2)
      (row column : Fin (2 ^ (frameEncoding width).width)),
      program.binaryMatrix (prodEquiv (row, rowControl)) (prodEquiv (column, columnControl)) =
        if rowControl = columnControl then (members rowControl).binaryMatrix row column else 0) :
    (nativeJoint width Reference program :
      HilbertOperator (Register.prod (context width).register Reference)) =
      controlBlocks width Reference (fun control =>
        (InPlaceDivisionConjugation.native width Reference (members control) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context width).register
            Reference))) := by
  ext ⟨row, rowReference⟩ ⟨column, columnReference⟩
  obtain ⟨rowControl, originalRow, rfl⟩ := label_surjective width row
  obtain ⟨columnControl, originalColumn, rfl⟩ := label_surjective width column
  rw [controlBlocks_entry]
  change UnitaryOperator.prodTensor _ _ _ _ = _
  rw [UnitaryOperator.prodTensor_apply]
  have placed : (runtimeProgram width program).matrix
      (label width rowControl originalRow) (label width columnControl originalColumn) =
      program.binaryMatrix
        (prodEquiv (NumeratorMeasurement.frameBasis width originalRow, rowControl))
        (prodEquiv (NumeratorMeasurement.frameBasis width originalColumn, columnControl)) := by
    rw [runtimeProgram_matrix, controlledNativeBasis_label, controlledNativeBasis_label]
    rfl
  erw [placed, entries]
  by_cases sameControl : rowControl = columnControl
  · simp only [if_pos sameControl]
    exact (congrArg (fun value : ℂ => value *
      (1 : HilbertOperator Reference) rowReference columnReference)
      (NumeratorRuntime.program_binary_matrix width (members rowControl)
        originalRow originalColumn)).symm
  · rw [if_neg sameControl, zero_mul, if_neg sameControl]

private theorem uncontrolled_matrix (width : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (rowControl columnControl : Fin 2) (row column : Fin (2 ^ (frameEncoding width).width)) :
    (uncontrolled width program).binaryMatrix
      (prodEquiv (row, rowControl)) (prodEquiv (column, columnControl)) =
      if rowControl = columnControl then program.binaryMatrix row column else 0 := by
  have placed := UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix
    (prefixWidth := (OutputCopy.encoding width).width) 1 program
  have entry := congrArg (fun operator : UnitaryOperator (Qubits
    ((OutputCopy.encoding width).width + 1)) =>
      operator (prodEquiv (row, rowControl)) (prodEquiv (column, columnControl))) placed
  refine entry.trans ?_
  change UnitaryOperator.prodTensor program.binaryMatrix (1 : UnitaryOperator (Qubits 1))
    ((prodEquiv (m := frameWidth width) (n := 1)).symm (prodEquiv (row, rowControl)))
    ((prodEquiv (m := frameWidth width) (n := 1)).symm (prodEquiv (column, columnControl))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, UnitaryOperator.prodTensor_apply]
  change program.binaryMatrix row column *
    (if rowControl = columnControl then (1 : ℂ) else 0) = _
  split <;> simp only [mul_one, mul_zero]

/-- Every unconditional native gate retains the same actual owned control coherently. -/
theorem uncontrolled_blocks (width : Nat) (Reference : Register)
    (program : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    (nativeJoint width Reference (uncontrolled width program) :
      HilbertOperator (Register.prod (context width).register Reference)) =
      controlBlocks width Reference (fun _ =>
        (InPlaceDivisionConjugation.native width Reference program :
          HilbertOperator (Register.prod (NumeratorMeasurement.context width).register
            Reference))) :=
  native_blocks_of_entries width Reference (uncontrolled width program) (fun _ => program)
    (uncontrolled_matrix width program)

private theorem inactive_column (modulus : Nat) (value numerator : Fin (2 ^ modulus.size))
    {Reference : Register} (stored : Store (NumeratorMeasurement.context modulus.size))
    (reference : Reference.Index)
    (row : (Register.prod (NumeratorMeasurement.context modulus.size).register Reference).Index) :
    inactiveOperator modulus.size Reference stored row
      (InPlaceTarget.preparedBasis modulus value numerator, reference) =
      WalshHadamard.invSqrtCard modulus.size *
        (1 : HilbertOperator
          (Register.prod (NumeratorMeasurement.context modulus.size).register Reference)) row
          (InPlaceTarget.preparedBasis modulus value numerator, reference) := by
  have actual := inactive_operator_ket modulus value numerator stored reference
  rw [← InPlaceOperatorAgreement.prepared_vec] at actual
  have entries := congrArg
    (fun vector : HilbertVector
      (Register.prod (NumeratorMeasurement.context modulus.size).register Reference) => vector row)
    actual
  rw [HilbertOperator.applyVec_ket] at entries
  change inactiveOperator modulus.size Reference stored row
    (InPlaceTarget.preparedBasis modulus value numerator, reference) =
      WalshHadamard.invSqrtCard modulus.size *
        (NormalizedVector.ket (R := Register.prod
          (NumeratorMeasurement.context modulus.size).register Reference)
          (InPlaceTarget.preparedBasis modulus value numerator, reference)) row at entries
  rw [NormalizedVector.ket_apply] at entries
  exact entries

/-- The original active arithmetic operators, already derived from their actual stored branches. -/
def activeOperator (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register) (stored : Store (NumeratorMeasurement.context modulus.size)) :
    HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
      Reference) :=
  match operation with
  | .multiplication => InPlaceMultiplicationConjugation.operator modulus prime Reference stored
  | .division => InPlaceDivisionConjugation.operator modulus prime Reference stored

/-- The two actual measured sectors, with the same complete original stored result. -/
def branchOperator (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register) (stored : Store (NumeratorMeasurement.context modulus.size)) :
    HilbertOperator (Register.prod (context modulus.size).register Reference) :=
  controlBlocks modulus.size Reference (fun control => if control = 1 then
    activeOperator operation modulus prime Reference stored else
    inactiveOperator modulus.size Reference stored)

/-- Every allowed complete column shares one coefficient, including cross-control matrix rows. -/
theorem prepared_column (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (control : Fin 2) (value numerator : Fin (2 ^ modulus.size))
    (domain : control = 1 → 0 < value.val ∧ value.val < modulus ∧ numerator.val < modulus)
    {Reference : Register} (stored : Store (NumeratorMeasurement.context modulus.size))
    (reference : Reference.Index)
    (row : (Register.prod (context modulus.size).register Reference).Index) :
    branchOperator operation modulus prime Reference stored row
      (label modulus.size control (InPlaceTarget.preparedBasis modulus value numerator),
        reference) =
      WalshHadamard.invSqrtCard modulus.size *
        target operation modulus prime Reference row
          (label modulus.size control (InPlaceTarget.preparedBasis modulus value numerator),
            reference) := by
  obtain ⟨row, rowReference⟩ := row
  obtain ⟨rowControl, originalRow, rfl⟩ := label_surjective modulus.size row
  have math := congrArg
    (fun matrix : HilbertOperator (Register.prod (context modulus.size).register Reference) =>
      matrix (label modulus.size rowControl originalRow, rowReference)
        (label modulus.size control (InPlaceTarget.preparedBasis modulus value numerator),
          reference))
    (target_blocks operation modulus prime Reference)
  rw [math, branchOperator, controlBlocks_entry, controlBlocks_entry]
  by_cases sameControl : rowControl = control
  · subst rowControl
    simp only [ite_true]
    by_cases active : control = 1
    · rw [if_pos active, if_pos active]
      obtain ⟨positive, bounded, numeratorBound⟩ := domain active
      cases operation
      · exact InPlaceOperatorAgreement.multiplication_column modulus prime value numerator
          positive bounded numeratorBound stored reference (originalRow, rowReference)
      · exact InPlaceOperatorAgreement.division_column modulus prime value numerator
          positive bounded numeratorBound stored reference (originalRow, rowReference)
    · rw [if_neg active, if_neg active]
      exact inactive_column modulus value numerator stored reference (originalRow, rowReference)
  · rw [if_neg sameControl, if_neg sameControl, mul_zero]

/-- Internal prepared support: the inactive input words remain completely unrestricted. -/
def admissible (modulus : Nat) (original : (context modulus.size).register.Index) : Prop :=
  ∃ (control : Fin 2) (value numerator : Fin (2 ^ modulus.size)),
    original = label modulus.size control (InPlaceTarget.preparedBasis modulus value numerator) ∧
      (control = 1 → 0 < value.val ∧ value.val < modulus ∧ numerator.val < modulus)

private instance controlStoreSubsingleton (width : Nat) :
    Subsingleton (Store (controlContext width)) :=
  ⟨fun first second => by
    apply congrArg Store.mk
    exact Subsingleton.elim (α := Unit × Unit) first.cells second.cells⟩

private def emptyControlStore (width : Nat) : Store (controlContext width) := ⟨((), ())⟩

/-- The quantum control contributes a presence marker and no hidden classical outcome. -/
def storeCoordinates (width : Nat) :
    Store (context width) ≃ Store (NumeratorMeasurement.context width) where
  toFun stored := (ContextUnion.storeEquiv (control_disjoint width) stored).1
  invFun stored := (ContextUnion.storeEquiv (control_disjoint width)).symm
    (stored, emptyControlStore width)
  left_inv stored := by
    apply (ContextUnion.storeEquiv (control_disjoint width)).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv stored :=
    congrArg Prod.fst ((ContextUnion.storeEquiv (control_disjoint width)).apply_symm_apply
      (stored, emptyControlStore width))

private theorem history_store_matrix {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History NewHistory : Type} [Fintype History] [Fintype NewHistory]
    (state : State ctx Reference History) (map : History → NewHistory) (stored : Store ctx) :
    ((state.mapHistory map).filterClassical (fun entry => entry.1 =
      stored)).quantumMarginal.matrix =
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix := by
  rw [← BasisSeeded.store_matrix, ← BasisSeeded.store_matrix]
  change (((state.mapClassical (fun entry => (entry.1, map entry.2))).mapClassical
    (fun entry => entry.1)).block stored).matrix = _
  rw [ExecutionState.executionState_mapClassical_comp]
  rfl

private theorem reindex_marginal {Classical : Type} [Fintype Classical] {R S : Register}
    (state : ExecutionState Classical R) (coordinates : R.Index ≃ S.Index) :
    (state.reindex coordinates).quantumMarginal = state.quantumMarginal.reindex coordinates := by
  apply DensityOperator.ext
  ext row column
  simp only [ExecutionState.quantumMarginal, Matrix.sum_apply,
    ExecutionState.reindex_block_entry, DensityOperator.reindex_entry]

private theorem split_marginal (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference History) :
    (ContextUnion.splitState (NumeratorMeasurement.context width) (controlContext width)
      (control_disjoint width) state).quantumMarginal =
      state.quantumMarginal.reindex
        (ContextUnion.referenceBasis (NumeratorMeasurement.context width) (controlContext width)
          (control_disjoint width) Reference) := by
  rw [ContextUnion.splitState, reindex_marginal, ExecutionState.mapClassical_quantumMarginal]

/-- Exact framing coordinates retain each entire stored block, including all reference coherences.
-/
theorem split_store_matrix (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference History) (stored : Store (context
      width)) :
    ((ContextUnion.splitState (NumeratorMeasurement.context width) (controlContext width)
      (control_disjoint width) state).filterClassical
        (fun entry => entry.1 = storeCoordinates width stored)).quantumMarginal.matrix =
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix.submatrix
        (ContextUnion.referenceBasis (NumeratorMeasurement.context width) (controlContext width)
          (control_disjoint width) Reference).symm
        (ContextUnion.referenceBasis (NumeratorMeasurement.context width) (controlContext width)
          (control_disjoint width) Reference).symm := by
  have regroup :
      (ContextUnion.splitState (NumeratorMeasurement.context width) (controlContext width)
        (control_disjoint width) state).mapClassical (fun entry => entry.1) =
      ((state.mapClassical (fun entry => entry.1)).mapClassical (storeCoordinates width)).reindex
        (ContextUnion.referenceBasis (NumeratorMeasurement.context width) (controlContext width)
          (control_disjoint width) Reference) := by
    rw [ContextUnion.splitState, ExecutionState.coordinate_reindex_mapClassical,
      ExecutionState.executionState_mapClassical_comp,
      ExecutionState.executionState_mapClassical_comp]
    rfl
  rw [← BasisSeeded.store_matrix, regroup]
  ext row column
  rw [ExecutionState.reindex_block_entry, ExecutionState.coordinate_mapClassical_block,
    Equiv.symm_apply_apply, BasisSeeded.store_matrix]
  rfl

/-- The actual framed H/Z/read/X operator is the original complete reset operator in exact
coordinates. -/
def framedResetOperator (width : Nat) (Reference : Register) (stored : Store (context width)) :
    HilbertOperator (Register.prod (context width).register Reference) :=
  (NumeratorResetConjugation.operator width (Register.prod (controlContext width).register
    Reference)
    (storeCoordinates width stored)).submatrix
      (ContextUnion.referenceBasis (NumeratorMeasurement.context width) (controlContext width)
        (control_disjoint width) Reference)
      (ContextUnion.referenceBasis (NumeratorMeasurement.context width) (controlContext width)
        (control_disjoint width) Reference)

private theorem pullback_conjugation {R S : Register} (coordinates : R.Index ≃ S.Index)
    (before after : HilbertOperator R) (operator : HilbertOperator S)
    (actual : after.submatrix coordinates.symm coordinates.symm =
      operator * before.submatrix coordinates.symm coordinates.symm * operator.conjTranspose) :
    after = operator.submatrix coordinates coordinates * before *
      (operator.submatrix coordinates coordinates).conjTranspose := by
  have recovered : (before.submatrix coordinates.symm coordinates.symm).submatrix
      coordinates coordinates = before := by
    ext row column
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have pulled := congrArg (fun matrix : HilbertOperator S =>
    matrix.submatrix coordinates coordinates) actual
  have out : (after.submatrix coordinates.symm coordinates.symm).submatrix
      coordinates coordinates = after := by
    ext row column
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [out] at pulled
  refine pulled.trans ?_
  symm
  conv_lhs => rw [← recovered]
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- The real framed H/Z/write/read/X execution has the exact complete stored-block conjugation. -/
theorem reset_matrix (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context width)) :
    (((reset width).execute Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      framedResetOperator width Reference stored * state.quantumMarginal.matrix *
        (framedResetOperator width Reference stored).conjTranspose := by
  let coordinates := ContextUnion.referenceBasis (NumeratorMeasurement.context width)
    (controlContext width) (control_disjoint width) Reference
  let localState := ContextUnion.splitServiceState (NumeratorMeasurement.context width)
    (controlContext width) (control_disjoint width) state
  have natural := ContextUnion.frameLocal_execute (NumeratorReset.code width)
    (reset_local width) (controlContext width) (control_disjoint width) Reference state
  have block := congrArg
    (fun result => (result.filterClassical
      (fun entry => entry.1 = storeCoordinates width stored)).quantumMarginal.matrix) natural
  simp only [ContextUnion.splitServiceState] at block
  rw [history_store_matrix, split_store_matrix, history_store_matrix] at block
  have actual := NumeratorResetConjugation.actual_matrix width localState
    (storeCoordinates width stored)
  have localMarginal : localState.quantumMarginal = state.quantumMarginal.reindex coordinates := by
    dsimp only [localState, ContextUnion.splitServiceState]
    rw [State.mapHistory_quantumMarginal, split_marginal]
  rw [NumeratorStoredFibers.source_eq_marginal, localMarginal] at actual
  have joined := block.trans actual
  exact pullback_conjugation coordinates state.quantumMarginal.matrix
    (((reset width).execute Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
    (NumeratorResetConjugation.operator width
      (Register.prod (controlContext width).register Reference) (storeCoordinates width stored))
        joined

private theorem reference_label (width : Nat) (Reference : Register) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index)
    (reference : Reference.Index) :
    ContextUnion.referenceBasis (NumeratorMeasurement.context width) (controlContext width)
      (control_disjoint width) Reference (label width control original, reference) =
      (original, ((controlBasis width).symm control, reference)) := by
  change
    (((ContextUnion.unionBasisEquiv _ _ (control_disjoint width))
      ((ContextUnion.unionBasisEquiv _ _ (control_disjoint width)).symm
        (original, (controlBasis width).symm control))).1,
      (((ContextUnion.unionBasisEquiv _ _ (control_disjoint width))
        ((ContextUnion.unionBasisEquiv _ _ (control_disjoint width)).symm
          (original, (controlBasis width).symm control))).2, reference)) = _
  rw [Equiv.apply_symm_apply]

private theorem original_reset_entry (width : Nat) (Reference : Register)
    (stored : Store (NumeratorMeasurement.context width))
    (row column : (Register.prod (NumeratorMeasurement.context width).register Reference).Index) :
    NumeratorResetConjugation.operator width Reference stored row column =
      (WalshHadamard.invSqrtCard width *
        WalshHadamard.walshSign
          (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input width)))
          (NumeratorObservation.word width column.1)) *
        if row = (NumeratorBranchAction.replaceWord width column.1 0, column.2) then 1 else 0 := by
  have actual := NumeratorBranchAction.operator_ket width stored column.1 column.2
  have entry := congrArg
    (fun vector : HilbertVector
      (Register.prod (NumeratorMeasurement.context width).register Reference) => vector row) actual
  change HilbertOperator.applyVec (NumeratorResetConjugation.operator width Reference stored)
    (NormalizedVector.ket (R := Register.prod (NumeratorMeasurement.context width).register
      Reference)
      column).vec row = _ at entry
  rw [HilbertOperator.applyVec_ket] at entry
  change NumeratorResetConjugation.operator width Reference stored row column =
    (WalshHadamard.invSqrtCard width *
      WalshHadamard.walshSign
        (NumeratorReset.outcome (stored.read (NumeratorMeasurement.input width)))
        (NumeratorObservation.word width column.1)) *
      (NormalizedVector.ket (R := Register.prod
        (NumeratorMeasurement.context width).register Reference)
        (NumeratorBranchAction.replaceWord width column.1 0, column.2)) row at entry
  rw [NormalizedVector.ket_apply] at entry
  exact entry

/-- The same actual reset acts on both control sectors with every external-reference entry
retained. -/
theorem framedReset_blocks (width : Nat) (Reference : Register) (stored : Store (context width)) :
    framedResetOperator width Reference stored =
      controlBlocks width Reference (fun _ =>
        NumeratorResetConjugation.operator width Reference (storeCoordinates width stored)) := by
  ext ⟨row, rowReference⟩ ⟨column, columnReference⟩
  obtain ⟨rowControl, originalRow, rfl⟩ := label_surjective width row
  obtain ⟨columnControl, originalColumn, rfl⟩ := label_surjective width column
  rw [controlBlocks_entry]
  change NumeratorResetConjugation.operator width
    (Register.prod (controlContext width).register Reference) (storeCoordinates width stored)
      (ContextUnion.referenceBasis _ _ (control_disjoint width) Reference
        (label width rowControl originalRow, rowReference))
      (ContextUnion.referenceBasis _ _ (control_disjoint width) Reference
        (label width columnControl originalColumn, columnReference)) = _
  rw [reference_label, reference_label, original_reset_entry, original_reset_entry]
  have same :
      ((originalRow, ((controlBasis width).symm rowControl, rowReference)) :
        (Register.prod (NumeratorMeasurement.context width).register
          (Register.prod (controlContext width).register Reference)).Index) =
        (NumeratorBranchAction.replaceWord width originalColumn 0,
          ((controlBasis width).symm columnControl, columnReference)) ↔
      rowControl = columnControl ∧
        ((originalRow, rowReference) :
          (Register.prod (NumeratorMeasurement.context width).register Reference).Index) =
          (NumeratorBranchAction.replaceWord width originalColumn 0, columnReference) := by
    change
      ((originalRow, ((controlBasis width).symm rowControl, rowReference)) :
        (NumeratorMeasurement.context width).register.Index ×
          ((controlContext width).register.Index × Reference.Index)) =
        (NumeratorBranchAction.replaceWord width originalColumn 0,
          ((controlBasis width).symm columnControl, columnReference)) ↔
      rowControl = columnControl ∧
        ((originalRow, rowReference) :
          (NumeratorMeasurement.context width).register.Index × Reference.Index) =
          (NumeratorBranchAction.replaceWord width originalColumn 0, columnReference)
    constructor
    · intro equal
      have originalSame := congrArg
        (fun pair : (NumeratorMeasurement.context width).register.Index ×
          ((controlContext width).register.Index × Reference.Index) => pair.1) equal
      have referenceSame := congrArg
        (fun pair : (NumeratorMeasurement.context width).register.Index ×
          ((controlContext width).register.Index × Reference.Index) => pair.2.2) equal
      exact ⟨(controlBasis width).symm.injective (congrArg (fun pair => pair.2.1) equal),
        Prod.ext originalSame referenceSame⟩
    · intro ⟨equalControl, equalOriginal⟩
      subst columnControl
      have originalSame := congrArg
        (fun pair : (NumeratorMeasurement.context width).register.Index × Reference.Index => pair.1)
        equalOriginal
      have referenceSame := congrArg
        (fun pair : (NumeratorMeasurement.context width).register.Index × Reference.Index => pair.2)
        equalOriginal
      exact Prod.ext originalSame (Prod.ext rfl referenceSame)
  have sameOriginal :
      ((originalRow, rowReference) :
        (Register.prod (NumeratorMeasurement.context width).register Reference).Index) =
        (NumeratorBranchAction.replaceWord width originalColumn 0, columnReference) ↔
      originalRow = NumeratorBranchAction.replaceWord width originalColumn 0 ∧
        rowReference = columnReference := by
    simp only [Prod.mk.injEq]
  simp only [same, sameOriginal]
  by_cases sameControl : rowControl = columnControl <;> simp [sameControl]

private theorem oppositeBlocks_mul (width : Nat) (Reference : Register)
    (active inactive : HilbertOperator
      (Register.prod (NumeratorMeasurement.context width).register Reference)) :
    controlBlocks width Reference (fun control => if control = 0 then inactive else 1) *
      controlBlocks width Reference (fun control => if control = 1 then active else 1) =
      controlBlocks width Reference (fun control => if control = 1 then active else inactive) := by
  rw [controlBlocks_mul]
  apply congrArg (controlBlocks width Reference)
  funext control
  fin_cases control <;> simp

private theorem save_blocks (modulus : Nat) (Reference : Register) :
    (nativeJoint modulus.size Reference (save modulus) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control => if control = 1 then
        (InPlaceDivisionConjugation.native modulus.size Reference
          (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)) :
            HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
              Reference))
        else (InPlaceDivisionConjugation.native modulus.size Reference (copy modulus.size) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
            Reference))) := by
  have productRealizes := NativeProductFrame.Controlled.nativeProductControlled_realizes
    modulus.size (InPlaceArithmetic.modulusWord modulus) (nativeLayout modulus.size)
  have selected := productRealizes.congrStep
    (second := NativeFrameControl.step modulus.size true
      (NativeProductFrame.step modulus.size (InPlaceArithmetic.modulusWord modulus)))
    (fun state => by rcases state with ⟨frame, selected⟩; cases selected <;> rfl)
  have productBlocks := controlled_blocks modulus.size Reference true _ _ _ selected
    (NativeProductFrame.nativeProductFrame_realizes modulus.size
      (InPlaceArithmetic.modulusWord modulus))
  have copyBlocks := controlled_blocks modulus.size Reference false _ _ _
    (NativeFrameControl.nativeFrameControl_realizes modulus.size false (copyGates modulus.size)
      (nativeLayout modulus.size))
    (EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty (copyGates modulus.size))
  simp only [controlLabel, ↓reduceIte] at productBlocks copyBlocks
  exact (nativeJoint_seq modulus.size Reference
    (NativeProductFrame.Controlled.program modulus.size (InPlaceArithmetic.modulusWord modulus)
      (nativeLayout modulus.size))
    (controlled modulus.size false (copyGates modulus.size))).trans
      ((congrArg₂ (fun left right => left * right) copyBlocks productBlocks).trans
        (oppositeBlocks_mul _ _ _ _))

private theorem forward_blocks (modulus : Nat) (prime : Nat.Prime modulus) (Reference : Register) :
    (nativeJoint modulus.size Reference (forward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control => if control = 1 then
        (InPlaceDivisionConjugation.native modulus.size Reference (NativeEEAFrame.forward
          modulus prime) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
            Reference))
        else 1) := by
  simpa only [forward, controlLabel, ↓reduceIte] using
    (controlled_blocks modulus.size Reference true _ _ _
    (NativeEEAFrame.Controlled.nativeEEAControlled_forward_realizes modulus prime true
      (nativeLayout modulus.size))
    (NativeEEAFrame.nativeEEAFrame_forward_realizes modulus prime))

private theorem backward_blocks (modulus : Nat) (prime : Nat.Prime modulus) (Reference : Register) :
    (nativeJoint modulus.size Reference (backward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control => if control = 1 then
        (InPlaceDivisionConjugation.native modulus.size Reference (NativeEEAFrame.backward
          modulus prime) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
            Reference))
        else 1) := by
  simpa only [backward, controlLabel, ↓reduceIte] using
    (controlled_blocks modulus.size Reference true _ _ _
    (NativeEEAFrame.Controlled.nativeEEAControlled_backward_realizes modulus prime true
      (nativeLayout modulus.size))
    (NativeEEAFrame.nativeEEAFrame_backward_realizes modulus prime))

private theorem reused_blocks (modulus : Nat) (prime : Nat.Prime modulus) (Reference : Register) :
    (nativeJoint modulus.size Reference (reusedForward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control => if control = 1 then
        (InPlaceDivisionConjugation.native modulus.size Reference (NativeReusedEEA.forward
          modulus prime) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
            Reference))
        else 1) := by
  simpa only [reusedForward, controlLabel, ↓reduceIte] using
    (controlled_blocks modulus.size Reference true _ _ _
    (NativeEEAFrame.Controlled.nativeEEAControlled_reusedForward_realizes modulus prime true
      (nativeLayout modulus.size))
    (NativeReusedEEA.nativeReusedEEA_forward_realizes modulus prime))

private theorem swap_blocks (width : Nat) (Reference : Register) :
    (nativeJoint width Reference (swap width) :
      HilbertOperator (Register.prod (context width).register Reference)) =
      controlBlocks width Reference (fun _ =>
        (InPlaceDivisionConjugation.native width Reference (FrameSwap.program width) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context width).register
            Reference))) :=
  uncontrolled_blocks _ _ _

private def activeBefore (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) :
    HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
      Reference) :=
  match operation with
  | .multiplication => InPlaceDivisionConjugation.native modulus.size Reference
      (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus))
  | .division =>
      (InPlaceDivisionConjugation.native modulus.size Reference
        (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference)) *
      (InPlaceDivisionConjugation.native modulus.size Reference (NativeEEAFrame.forward modulus
        prime) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference))

private def activeAfter (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
      Reference) :=
  match operation with
  | .division =>
      (InPlaceDivisionConjugation.native modulus.size Reference (FrameSwap.program modulus.size) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference)) *
      (InPlaceDivisionConjugation.native modulus.size Reference
        (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus) value) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference)) *
      (InPlaceDivisionConjugation.native modulus.size Reference (NativeEEAFrame.backward modulus
        prime) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference))
  | .multiplication =>
      (InPlaceDivisionConjugation.native modulus.size Reference (FrameSwap.program modulus.size) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference)) *
      (InPlaceDivisionConjugation.native modulus.size Reference (NativeEEAFrame.backward modulus
        prime) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference)) *
      (InPlaceDivisionConjugation.native modulus.size Reference
        (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus) value) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference)) *
      (InPlaceDivisionConjugation.native modulus.size Reference (NativeReusedEEA.forward modulus
        prime) :
        HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
          Reference))

private theorem beforeReset_blocks (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) :
    (nativeJoint modulus.size Reference (beforeReset operation modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control => if control = 1 then
        activeBefore operation modulus prime Reference else
        (InPlaceDivisionConjugation.native modulus.size Reference (copy modulus.size) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
            Reference))) := by
  cases operation
  · exact save_blocks modulus Reference
  · change (nativeJoint modulus.size Reference
      ((forward modulus prime).seq (save modulus)) :
        HilbertOperator (Register.prod (context modulus.size).register Reference)) = _
    rw [nativeJoint_seq, forward_blocks]
    have saveBlocks := save_blocks modulus Reference
    rw [saveBlocks, controlBlocks_mul]
    apply congrArg (controlBlocks modulus.size Reference)
    funext control
    by_cases active : control = 1
    · rw [if_pos active, if_pos active, if_pos active]
      rfl
    · rw [if_neg active, if_neg active, if_neg active, Matrix.mul_one]

private theorem liftedInactiveWord_sign (width : Nat) (state : Frame width × Bool)
    (indices : List (Fin width)) :
    EncodedBit.Word.PhaseCorrection.sign (liftedInactiveWord width) state indices =
      EncodedBit.Word.PhaseCorrection.sign (inactiveWord width) state.1 indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [EncodedBit.Word.PhaseCorrection.sign, EncodedBit.Word.PhaseCorrection.sign, ih]
      rfl

private theorem correction_blocks (modulus : Nat) (Reference : Register)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (nativeJoint modulus.size Reference (correction modulus value) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control => if control = 1 then
        (InPlaceDivisionConjugation.native modulus.size Reference
          (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus) value) :
            HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
              Reference))
        else (InPlaceDivisionConjugation.native modulus.size Reference
          (inactiveMask modulus.size value) :
            HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
              Reference))) := by
  let mask := QubitReadouts.mask value
  have activeBlocks := controlled_blocks_of_entries modulus.size Reference true
    (ReusedProduct.Controlled.program modulus.size (InPlaceArithmetic.modulusWord modulus) true
      mask (nativeLayout modulus.size))
    (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus) value)
    (conditional_phase_matrix modulus.size true _ _
      (fun state => EncodedBit.Word.PhaseCorrection.sign (ReusedProduct.measuredWord modulus.size)
        (ReusedProduct.computeStep modulus.size (InPlaceArithmetic.modulusWord modulus) state)
        (EncodedBit.Word.PhaseCorrection.selected mask))
      (ReusedProduct.Controlled.reusedProductControlled_ket modulus.size
        (InPlaceArithmetic.modulusWord modulus) true mask (nativeLayout modulus.size))
      (Recompute.recompute_phase_ket (QubitLayout.canonical _) _
        (ReusedProduct.reusedProduct_realizes modulus.size (InPlaceArithmetic.modulusWord modulus))
        (ReusedProduct.measuredWord modulus.size) mask))
  have inactiveAction (state : Frame modulus.size × Bool) :=
    EncodedBit.Word.PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_ket
      (nativeLayout modulus.size) .empty (NativeFrameControl.control modulus.size)
      (liftedInactiveWord modulus.size) (inactive_separated modulus.size) false
      (EncodedBit.Word.PhaseCorrection.selected mask) state
  have inactiveBlocks := controlled_blocks_of_entries modulus.size Reference false
    (inactiveCorrection modulus.size value) (inactiveMask modulus.size value)
    (conditional_phase_matrix modulus.size false _ _
      (fun state => EncodedBit.Word.PhaseCorrection.sign (inactiveWord modulus.size) state
        (EncodedBit.Word.PhaseCorrection.selected mask))
      (fun state => by
        have action := inactiveAction state
        rw [liftedInactiveWord_sign] at action
        exact action)
      (EncodedBit.Word.PhaseCorrection.phaseCorrection_sequence_ket (QubitLayout.canonical _)
        .empty (inactiveWord modulus.size) (EncodedBit.Word.PhaseCorrection.selected mask)))
  simp only [controlLabel, ↓reduceIte] at activeBlocks inactiveBlocks
  exact (nativeJoint_seq modulus.size Reference
    (ReusedProduct.Controlled.program modulus.size (InPlaceArithmetic.modulusWord modulus) true
      mask (nativeLayout modulus.size)) (inactiveCorrection modulus.size value)).trans
      ((congrArg₂ (fun left right => left * right) inactiveBlocks activeBlocks).trans
        (oppositeBlocks_mul _ _ _ _))

private theorem suffix_blocks (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (nativeJoint modulus.size Reference (suffix operation modulus prime value) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) =
      controlBlocks modulus.size Reference (fun control => if control = 1 then
        activeAfter operation modulus prime Reference value else
        (InPlaceDivisionConjugation.native modulus.size Reference (FrameSwap.program modulus.size) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
            Reference)) *
        (InPlaceDivisionConjugation.native modulus.size Reference (inactiveMask modulus.size
          value) :
          HilbertOperator (Register.prod (NumeratorMeasurement.context modulus.size).register
            Reference))) := by
  have correctionBlocks := correction_blocks modulus Reference value
  cases operation <;>
    simp only [suffix, nativeJoint_seq, backward_blocks, reused_blocks,
      swap_blocks, correctionBlocks, controlBlocks_mul]
  all_goals
    apply congrArg (controlBlocks modulus.size Reference)
    funext control
    by_cases active : control = 1 <;>
      simp only [active, ite_true, ite_false, Matrix.mul_one, activeAfter,
        Matrix.mul_assoc]

/-- The matrix chain consists of the actual prefix, real framed reset and actual stored suffix. -/
def actualOperator (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register) (stored : Store (context modulus.size)) :
    HilbertOperator (Register.prod (context modulus.size).register Reference) :=
  (nativeJoint modulus.size Reference
    (suffix operation modulus prime (stored.read (resultInput modulus.size))) :
    HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    framedResetOperator modulus.size Reference stored *
    (nativeJoint modulus.size Reference (beforeReset operation modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference))

private theorem nativeCode_marginal (width : Nat) (Reference : Register)
    (program : NativeCircuit width)
    {History : Type} [Fintype History]
    (state : State (context width) Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    ((nativeCode width program).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary (nativeJoint width Reference program) state.quantumMarginal :=
  Circuit.unitary_jointDensity (runtimeProgram width program) state

/-- Every complete stored block is derived from the actual Circuit interpreter in its emitted
order. -/
theorem body_matrix (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime
    modulus)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context
      modulus.size)) :
    (((body operation modulus prime).execute Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      actualOperator operation modulus prime Reference stored * state.quantumMarginal.matrix *
        (actualOperator operation modulus prime Reference stored).conjTranspose := by
  let prefixCode := nativeCode modulus.size (beforeReset operation modulus prime)
  let measured := reset modulus.size
  let selected := selectedSuffix operation modulus prime
  have first := Circuit.seq_store_marginal prefixCode (.seq measured selected) state stored
  refine (congrArg DensityOperator.matrix first).trans ?_
  have second := Circuit.seq_store_marginal measured selected
    (prefixCode.execute Reference state) stored
  refine (congrArg DensityOperator.matrix second).trans ?_
  refine (Circuit.selectedUnitary_store_matrix (resultInput modulus.size)
    (fun value => runtimeProgram modulus.size (suffix operation modulus prime value))
    (measured.execute Reference (prefixCode.execute Reference state)) stored).trans ?_
  dsimp only [measured, prefixCode]
  have measuredBlock := reset_matrix modulus.size
    ((nativeCode modulus.size (beforeReset operation modulus prime)).execute Reference state)
    stored
  rw [DensityOperator.applyUnitary_matrix]
  erw [measuredBlock, nativeCode_marginal, DensityOperator.applyUnitary_matrix]
  simp only [actualOperator, nativeJoint, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Actual matrix composition identifies both coherent sectors with the already proved column
chains. -/
theorem actualOperator_blocks (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) (stored : Store (context modulus.size)) :
    actualOperator operation modulus prime Reference stored =
      branchOperator operation modulus prime Reference (storeCoordinates modulus.size stored) := by
  have storedRead : stored.read (resultInput modulus.size) =
      (storeCoordinates modulus.size stored).read (NumeratorMeasurement.input modulus.size) :=
    resultInput_read modulus.size stored
  rw [actualOperator, branchOperator, storedRead, suffix_blocks, framedReset_blocks,
    beforeReset_blocks,
    controlBlocks_mul, controlBlocks_mul]
  apply congrArg (controlBlocks modulus.size Reference)
  funext control
  by_cases active : control = 1
  · simp only [if_pos active]
    cases operation <;> simp only [activeAfter, activeBefore, activeOperator,
      InPlaceDivisionConjugation.operator, InPlaceMultiplicationConjugation.operator,
      InPlaceDivisionConjugation.native, InPlaceMultiplicationConjugation.native, Matrix.mul_assoc]
  · simp only [if_neg active, inactiveOperator]

private theorem coefficient_normalized (width : Nat) :
    (Fintype.card (Store (context width)) : ℂ) *
      (WalshHadamard.invSqrtCard width * star (WalshHadamard.invSqrtCard width)) = 1 := by
  rw [Fintype.card_congr (storeCoordinates width)]
  exact NumeratorBranchSum.coefficient_normalized width

/-- The actual body preserves arbitrary mixed and entangled control/reference coherences. -/
theorem body_density (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime
    modulus)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ original : (Register.prod (context modulus.size).register Reference).Index,
      ¬admissible modulus original.1 → state.quantumMarginal.matrix original original = 0) :
    ((body operation modulus prime).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary (target operation modulus prime Reference)
        state.quantumMarginal := by
  apply DensityOperator.ext
  apply full_matrix_of_stored_columns state.quantumMarginal _
    (fun original => admissible modulus original.1) (target operation modulus prime Reference)
    (actualOperator operation modulus prime Reference) (WalshHadamard.invSqrtCard modulus.size)
    (coefficient_normalized modulus.size) support
  · intro stored original allowed row
    obtain ⟨original, reference⟩ := original
    obtain ⟨control, value, numerator, rfl, domain⟩ := allowed
    rw [actualOperator_blocks]
    exact prepared_column operation modulus prime control value numerator domain
      (storeCoordinates modulus.size stored) reference row
  · intro stored
    exact body_matrix operation modulus prime state stored

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
