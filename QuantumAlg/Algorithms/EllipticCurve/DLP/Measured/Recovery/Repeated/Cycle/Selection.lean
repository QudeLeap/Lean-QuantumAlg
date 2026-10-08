/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity

/-!
# First-success retention in an actual checked ECC attempt

The physical sample and checked recovery retain an already accepted scalar
in the seven live classical cells. The statement uses the actual named attempt
from the repeated ECDLP run, with arbitrary incoming quantum state, service
history and reference. It is a component of the completed-attempt protocol;
the cycle's initial admission and final packing are separate obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- An accepted selected scalar survives the original reset, sample and
checked classical recovery in every positive actual execution block. -/
theorem persistentCheckedAttempt_preserves_first
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (wanted : (CShape.unsignedWord (orderWidth problem)).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true ∧
        entry.1.read (.storage (persistentSelected _ _ _).toCStorageRef) = wanted)
    (result : Store
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (H × (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
          nontrivial).Path)))
    (positive : 0 < (((persistentCheckedAttempt E fieldTail sameWidth fits odd problem
      points seed nontrivial).execute Reference state).block result).mass) :
    (result.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true ∧
      result.1.read (.storage (persistentSelected _ _ _).toCStorageRef) = wanted := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let round := BitWord.selectForCircuit
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
  let roundLocal := BitWord.selectForCircuit_isLocal _
    (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)
  exact sampledAttempt_preserves_first round roundLocal
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) state wanted holds result positive

/-- One actual measured-and-checked attempt preserves the original bound on
the selected scalar in every positive output block. -/
theorem persistentCheckedAttempt_preserves_selected_lt
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat <
        problem.order)
    (result : Store
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (H × (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
          nontrivial).Path)))
    (positive : 0 < (((persistentCheckedAttempt E fieldTail sameWidth fits odd problem
      points seed nontrivial).execute Reference state).block result).mass) :
    (result.1.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat <
      problem.order := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let round := BitWord.selectForCircuit
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
  let roundLocal := BitWord.selectForCircuit_isLocal _
    (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)
  exact sampledAttempt_preserves_selected_lt round roundLocal
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) state holds result positive

/-- The actual measured and checked attempt preserves the admitted public
points and the equation for every retained accepted scalar. -/
theorem persistentCheckedAttempt_preserves_validity
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
          (orderWidth problem) (PublicInput.terminalBaseRef E (orderWidth problem))))
          problem.generator.toMathlib ∧
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
          (orderWidth problem) (PublicInput.terminalTargetRef E (orderWidth problem))))
          problem.target.toMathlib ∧
      ((entry.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
        (entry.1.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
          problem.generator.toMathlib = problem.target.toMathlib))
    (result : Store
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (H × (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
          nontrivial).Path)))
    (positive : 0 < (((persistentCheckedAttempt E fieldTail sameWidth fits odd problem
      points seed nontrivial).execute Reference state).block result).mass) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (result.1.read (persistentInput (Canonical.Layout.fieldWidth E)
        (orderWidth problem) (PublicInput.terminalBaseRef E (orderWidth problem))))
        problem.generator.toMathlib ∧
    PointRepresents (Canonical.Layout.curveSpec E)
      (result.1.read (persistentInput (Canonical.Layout.fieldWidth E)
        (orderWidth problem) (PublicInput.terminalTargetRef E (orderWidth problem))))
        problem.target.toMathlib ∧
    ((result.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
      (result.1.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
        problem.generator.toMathlib = problem.target.toMathlib) := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let round := BitWord.selectForCircuit
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
  let roundLocal := BitWord.selectForCircuit_isLocal _
    (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)
  have noQuantum :
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  have localPoints : ∀ entry,
      0 < (((underPersistent round roundLocal (Canonical.Layout.fieldWidth E)
        (orderWidth problem)).execute Reference state).block entry).mass →
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
          (orderWidth problem) (PublicInput.terminalBaseRef E (orderWidth problem))))
          problem.generator.toMathlib ∧
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
          (orderWidth problem) (PublicInput.terminalTargetRef E (orderWidth problem))))
          problem.target.toMathlib := by
    intro entry present
    exact PublicInput.persistentProgram_preserves_represents E (orderWidth problem)
      problem (underPersistent round roundLocal (Canonical.Layout.fieldWidth E)
        (orderWidth problem)) noQuantum state
      (fun previous source => ⟨(holds previous source).1, (holds previous source).2.1⟩)
      entry present
  exact sampledAttempt_preserves_validity round roundLocal
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))
    problem.generator.toMathlib problem.target.toMathlib state holds localPoints result positive

/-- The original accepted bit and selected word in the seven persistent cells. -/
def selectedFirstStored
    (wanted : (CShape.unsignedWord (orderWidth problem)).Value)
    (store : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem))) : Prop :=
  (store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true ∧
    store.read (.storage (persistentSelected _ _ _).toCStorageRef) = wanted

/-- A section retains an accepted word in its real persistent output store
for every supported input block and every reference extension. -/
def RetainsFirst
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))) : Prop :=
  ∀ (wanted : (CShape.unsignedWord (orderWidth problem)).Value)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State _ Reference (ClassicalOracleModel.empty.HiddenState × H)),
    (∀ entry, 0 < (state.block entry).mass → selectedFirstStored E problem wanted entry.1) →
      ∀ result, 0 < ((code.execute Reference state).block result).mass →
        selectedFirstStored E problem wanted result.1

omit [Fact p.Prime] in
private theorem retainsFirst_seq
    (first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    (left : RetainsFirst E problem first) (right : RetainsFirst E problem second) :
    RetainsFirst E problem (first.seq second) := by
  intro wanted Reference H _ state holds result positive
  rw [Circuit.execute_seq] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  have kept := right wanted (first.execute Reference state) (left wanted state holds)
    original present
  rw [← equality]
  exact kept

omit [Fact p.Prime] in
private theorem underPersistent_retainsFirst
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)))
    (supported : code.IsLocal) :
    RetainsFirst E problem
      (underPersistent code supported (Canonical.Layout.fieldWidth E) (orderWidth problem)) := by
  intro wanted Reference H _ state holds result positive
  have paired : ∀ entry, 0 < (state.block entry).mass →
      ((entry.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool,
        entry.1.read (.storage (persistentSelected _ _ _).toCStorageRef)) =
          (true, wanted) := by
    intro entry present
    exact Prod.ext (holds entry present).1 (holds entry present).2
  have kept := underPersistent_latches_supported code supported
    (Canonical.Layout.fieldWidth E) (orderWidth problem) state (true, wanted)
    paired result positive
  exact ⟨congrArg Prod.fst kept, congrArg Prod.snd kept⟩

private theorem reset_retainsFirst :
    RetainsFirst E problem
      (persistentSamplingReset E fieldTail sameWidth fits problem seed) := by
  let raw := samplingReset E fieldTail (orderWidth problem) sameWidth fits seed
  let selected := BitWord.selectForCircuit raw
  let supported := BitWord.selectForCircuit_isLocal raw
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  exact underPersistent_retainsFirst E problem selected supported

/-- The terminal checked body keeps the first accepted scalar unchanged. -/
theorem checkedSectionBody_retainsFirst :
    RetainsFirst E problem
      ((persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)) := by
  intro wanted Reference H _ state holds result positive
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let raw := samplingReadout E fieldTail odd problem points
  let selected := BitWord.selectForCircuit raw
  let supported := BitWord.selectForCircuit_isLocal raw
    (samplingReadout_isLocal E fieldTail odd problem points)
  exact sampledAttempt_preserves_first selected supported
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) state wanted holds result positive

/-- The original first completed nonterminal segment retains every already
accepted selected scalar through both real resets and the checked recovery. -/
theorem firstCheckedSection_retainsFirst :
    ∀ {shape : CShape}
      (read : OutputRead
        (persistentCtx (PublicInput.terminal E (orderWidth problem))
          (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape),
    RetainsFirst E problem
      (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial read).code := by
  intro shape read
  exact retainsFirst_seq E problem _ _
    (retainsFirst_seq E problem _ _
      (reset_retainsFirst E fieldTail sameWidth fits problem seed)
      (checkedSectionBody_retainsFirst E fieldTail odd problem points nontrivial))
    (reset_retainsFirst E fieldTail sameWidth fits problem seed)

/-- Every reused nonterminal checked section retains the original first
accepted scalar through its real readout, check and following reset. -/
theorem reusedCheckedSection_retainsFirst :
    ∀ {shape : CShape}
      (read : OutputRead
        (persistentCtx (PublicInput.terminal E (orderWidth problem))
          (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape),
    RetainsFirst E problem
      (reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial read).code := by
  intro shape read
  exact retainsFirst_seq E problem _ _
    (checkedSectionBody_retainsFirst E fieldTail odd problem points nontrivial)
    (reset_retainsFirst E fieldTail sameWidth fits problem seed)

/-- The selected word of a persistent checked section remains below the
declared group order on every supported store block. -/
def SelectedWithinOrder
    (problem : KnownOrderProblem E.GroupPoint)
    (store : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem))) : Prop :=
  (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat < problem.order

/-- An actual persistent section preserves the selected-word range for all
incoming quantum states, histories and external references. -/
def RetainsSelectedBound
    (problem : KnownOrderProblem E.GroupPoint)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))) : Prop :=
  ∀ {Reference : Register} {H : Type} [Fintype H]
    (state : State _ Reference (ClassicalOracleModel.empty.HiddenState × H)),
    (∀ entry, 0 < (state.block entry).mass → SelectedWithinOrder E problem entry.1) →
      ∀ result, 0 < ((code.execute Reference state).block result).mass →
        SelectedWithinOrder E problem result.1

omit [Fact p.Prime] in
private theorem retainsSelectedBound_seq
    (first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    (left : RetainsSelectedBound E problem first)
    (right : RetainsSelectedBound E problem second) :
    RetainsSelectedBound E problem (first.seq second) := by
  intro Reference H _ state holds result positive
  rw [Circuit.execute_seq] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  have kept := right (first.execute Reference state) (left state holds) original present
  rw [← equality]
  exact kept

omit [Fact p.Prime] in
private theorem underPersistent_retainsSelectedBound
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)))
    (supported : code.IsLocal) :
    RetainsSelectedBound E problem
      (underPersistent code supported (Canonical.Layout.fieldWidth E)
        (orderWidth problem)) := by
  intro Reference H _ state holds result positive
  exact underPersistent_selected_property code supported
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
    (fun word => word.toNat < problem.order) state holds result positive

private theorem reset_retainsSelectedBound :
    RetainsSelectedBound E problem
      (persistentSamplingReset E fieldTail sameWidth fits problem seed) := by
  let raw := samplingReset E fieldTail (orderWidth problem) sameWidth fits seed
  let selected : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)) := BitWord.selectForCircuit raw
  have supported : selected.IsLocal := BitWord.selectForCircuit_isLocal raw
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  have sameCode :
      persistentSamplingReset E fieldTail sameWidth fits problem seed =
        underPersistent selected supported (Canonical.Layout.fieldWidth E)
          (orderWidth problem) := by
    rfl
  rw [sameCode]
  unfold RetainsSelectedBound
  intro Reference H _ state holds result positive
  exact underPersistent_selected_property selected supported
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
    (fun word => word.toNat < problem.order) state holds result positive

/-- The terminal checked body preserves the selected scalar's range. -/
theorem checkedSectionBody_retainsSelectedBound :
    RetainsSelectedBound E problem
      ((persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)) := by
  intro Reference H _ state holds result positive
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let raw := samplingReadout E fieldTail odd problem points
  let selected := BitWord.selectForCircuit raw
  let supported := BitWord.selectForCircuit_isLocal raw
    (samplingReadout_isLocal E fieldTail odd problem points)
  exact sampledAttempt_preserves_selected_lt selected supported
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) state holds result positive

/-- The first nonterminal section preserves the selected scalar's range
through its actual initial reset, checked sample and final reset. -/
theorem firstCheckedSection_retainsSelectedBound :
    RetainsSelectedBound E problem
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) := by
  exact retainsSelectedBound_seq E problem _ _
    (retainsSelectedBound_seq E problem _ _
      (reset_retainsSelectedBound E fieldTail sameWidth fits problem seed)
      (checkedSectionBody_retainsSelectedBound E fieldTail odd problem points nontrivial))
    (reset_retainsSelectedBound E fieldTail sameWidth fits problem seed)

/-- Every reused nonterminal section preserves the same selected bound. -/
theorem reusedCheckedSection_retainsSelectedBound :
    RetainsSelectedBound E problem
      (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) := by
  exact retainsSelectedBound_seq E problem _ _
    (checkedSectionBody_retainsSelectedBound E fieldTail odd problem points nontrivial)
    (reset_retainsSelectedBound E fieldTail sameWidth fits problem seed)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
