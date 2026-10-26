/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.FailureLoop
import all QuantumAlg.Core.Execution.Instrument.Recorded
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Correctness.Read.Inputs
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Reset.Instrument
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Fourier.Instrument
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Store
import all QuantumAlg.Core.Execution.Quantum.HistorySelection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store.Phases

/-!
# Protected original observations in the actual feedback program

A complete recorded instrument that preserves an original read commutes
with selecting that same read. The proof retains every actual returned
Store, service state, incoming History, measured Path and Reference entry.
The actual fresh feedback frame supplies point-record protection internally;
in particular, Boolean parity and temporary cells are separated by genuine
allocation freshness, independently of their common storage shape.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution ClassicalWorkspace Locality

open QuantumFourierTransform.Semiclassical.Window.Source
open ClassicalAlgorithms.Modular ClassicalRoutines.EllipticCurve.WindowTables
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma retained_filter_part {Result Value Sum : Type} [Zero Sum]
    [DecidableEq Result] [DecidableEq Value]
    (actual result : Result) (before value : Value) (afterRead : Result → Value)
    (preserved : afterRead actual = before) (part : Sum) :
    (if actual = result then (if before = value then part else 0) else 0) =
      if afterRead result = value then (if actual = result then part else 0) else 0 := by
  by_cases same : actual = result
  · cases same
    cases preserved
    simp only [if_true]
  · by_cases selected : afterRead result = value
    · simp only [if_neg same, if_pos selected]
    · simp only [if_neg same, if_neg selected]

private lemma retained_filter_sum {Original Outcome Result Value Sum : Type}
    [Fintype Original] [Fintype Outcome] [AddCommMonoid Sum]
    [DecidableEq Result] [DecidableEq Value]
    (record : Original → Outcome → Result) (beforeRead : Original → Value)
    (afterRead : Result → Value)
    (preserved : ∀ original outcome, afterRead (record original outcome) = beforeRead original)
    (parts : Original → Outcome → Sum) (result : Result) (value : Value) :
    (∑ original, ∑ outcome, if record original outcome = result then
      (if beforeRead original = value then parts original outcome else 0) else 0) =
      if afterRead result = value then
        ∑ original, ∑ outcome, if record original outcome = result then
          parts original outcome else 0
      else 0 := by
  calc
    _ = ∑ original, ∑ outcome, if afterRead result = value then
        (if record original outcome = result then parts original outcome else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      exact retained_filter_part (record original outcome) result (beforeRead original)
        value afterRead (preserved original outcome) (parts original outcome)
    _ = _ := by simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]

private lemma retained_replace_parts {Original Outcome Result Sum : Type}
    [Fintype Original] [Fintype Outcome] [DecidableEq Result] [AddCommMonoid Sum]
    (record : Original → Outcome → Result) (beforeParts afterParts : Original → Outcome → Sum)
    (same : ∀ original outcome, beforeParts original outcome = afterParts original outcome)
    (result : Result) :
    (∑ original, ∑ outcome, if record original outcome = result then
      beforeParts original outcome else 0) =
      ∑ original, ∑ outcome, if record original outcome = result then
        afterParts original outcome else 0 := by
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  exact congrArg (fun part : Sum => if record original outcome = result then part else 0)
    (same original outcome)

private def retainedSandwich {R : Register} (operator : HilbertOperator R)
    (density : DensityOperator R) : HilbertOperator R := by
  letI : Fintype R.Index := R.fintype
  exact operator * density.matrix * operator.conjTranspose

private lemma retainedSandwich_eq {R : Register} (operator : HilbertOperator R)
    (density : DensityOperator R) :
    retainedSandwich (R := R) operator density =
      operator * density.matrix * operator.conjTranspose := rfl

private lemma selected_density_sandwich {R : Register} (selected : Prop)
    [Decidable selected] (operator : HilbertOperator R) (density : DensityOperator R) :
    operator * (if selected then density else DensityOperator.zero R).matrix *
        operator.conjTranspose =
      if selected then operator * density.matrix * operator.conjTranspose else 0 := by
  by_cases yes : selected
  · simp only [if_pos yes]
  · simp only [if_neg yes, DensityOperator.zero_matrix, Matrix.mul_zero, Matrix.zero_mul]

private lemma selected_state_block_matrix {Original Value : Type} {R : Register}
    [Fintype Original] [DecidableEq Value]
    (state : ExecutionState Original R) (read : Original → Value)
    (value : Value) (original : Original) :
    ((state.selectClassical read value).block original).matrix =
      if read original = value then (state.block original).matrix else 0 := by
  rw [ExecutionState.selectClassical_block]
  by_cases yes : read original = value
  · simp only [if_pos yes]
  · simp only [if_neg yes, DensityOperator.zero_matrix]

private lemma selected_state_sandwich {Original Value : Type} [Fintype Original]
    [DecidableEq Value] {R : Register} (state : ExecutionState Original R)
    (read : Original → Value) (value : Value) (original : Original)
    (operator : HilbertOperator R) :
    operator * ((state.selectClassical read value).block original).matrix *
        operator.conjTranspose =
      if read original = value then
        operator * (state.block original).matrix * operator.conjTranspose else 0 := by
  exact (congrArg
    (fun density : DensityOperator R => operator * density.matrix * operator.conjTranspose)
    (ExecutionState.selectClassical_block state read value original)).trans
      (selected_density_sandwich (read original = value) operator (state.block original))

private lemma selected_retainedSandwich {Original Value : Type}
    [Fintype Original] [DecidableEq Value] {R : Register}
    (state : ExecutionState Original R) (read : Original → Value) (value : Value)
    (original : Original) (operator : HilbertOperator R) :
    retainedSandwich (R := R) operator ((state.selectClassical read value).block original) =
      if read original = value then
        retainedSandwich (R := R) operator (state.block original) else 0 :=
  selected_state_sandwich state read value original operator

private def retainedBlocks {Original Result Outcome : Type}
    [Fintype Original] [Fintype Result] [Fintype Outcome] [DecidableEq Result]
    {R : Register} (transition : ExecutionState Original R → ExecutionState Result R)
    (record : Original → Outcome → Result)
    (operators : Original → Outcome → HilbertOperator R) : Prop :=
  ∀ (state : ExecutionState Original R) (result : Result),
    ((transition state).block result).matrix =
      ∑ original : Original, ∑ outcome : Outcome,
        if record original outcome = result then
          retainedSandwich (R := R) (operators original outcome) (state.block original) else 0

private def selectedTransitionBlock {Original Result Outcome Value : Type}
    [Fintype Original] [Fintype Result] [Fintype Outcome]
    [DecidableEq Result] [DecidableEq Value]
    {R : Register} (transition : ExecutionState Original R → ExecutionState Result R)
    (record : Original → Outcome → Result)
    (operators : Original → Outcome → HilbertOperator R)
    (read : Original → Value) (value : Value) (state : ExecutionState Original R)
    (result : Result) : Prop :=
  ((transition (state.selectClassical read value)).block result).matrix =
    ∑ original : Original, ∑ outcome : Outcome,
      if record original outcome = result then
        (if read original = value then
          retainedSandwich (R := R) (operators original outcome) (state.block original) else 0)
      else 0

private lemma selected_transition_blocks {Original Result Outcome Value : Type}
    [Fintype Original] [Fintype Result] [Fintype Outcome]
    [DecidableEq Result] [DecidableEq Value]
    {R : Register} (transition : ExecutionState Original R → ExecutionState Result R)
    (record : Original → Outcome → Result)
    (operators : Original → Outcome → HilbertOperator R)
    (blocks : retainedBlocks transition record operators)
    (read : Original → Value) (value : Value) (state : ExecutionState Original R)
    (result : Result) :
    selectedTransitionBlock transition record operators read value state result := by
  let beforeParts : Original → Outcome → HilbertOperator R :=
    fun (original : Original) (outcome : Outcome) =>
      retainedSandwich (R := R) (operators original outcome)
        ((state.selectClassical read value).block original)
  let afterParts : Original → Outcome → HilbertOperator R :=
    fun (original : Original) (outcome : Outcome) =>
      if read original = value then
        retainedSandwich (R := R) (operators original outcome) (state.block original) else 0
  have sameParts : ∀ (original : Original) (outcome : Outcome),
      beforeParts original outcome = afterParts original outcome := by
    intro original outcome
    exact selected_retainedSandwich state read value original (operators original outcome)
  have replaced :
      (∑ original, ∑ outcome, if record original outcome = result then
        beforeParts original outcome else 0) =
      ∑ original, ∑ outcome, if record original outcome = result then
        afterParts original outcome else 0 :=
    retained_replace_parts record beforeParts afterParts sameParts result
  have final := (blocks (state.selectClassical read value) result).trans replaced
  exact final


private lemma retained_selected_block {Original Result Outcome Value : Type}
    [Fintype Original] [Fintype Result] [Fintype Outcome]
    [DecidableEq Result] [DecidableEq Value]
    {R : Register} (transition : ExecutionState Original R → ExecutionState Result R)
    (record : Original → Outcome → Result)
    (operators : Original → Outcome → HilbertOperator R)
    (blocks : retainedBlocks transition record operators)
    (beforeRead : Original → Value) (afterRead : Result → Value)
    (preserved : ∀ original outcome,
      afterRead (record original outcome) = beforeRead original)
    (value : Value) (state : ExecutionState Original R) (result : Result) :
    ((transition (state.selectClassical beforeRead value)).block result).matrix =
      (((transition state).selectClassical afterRead value).block result).matrix := by
  let parts : Original → Outcome → HilbertOperator R :=
    fun (original : Original) (outcome : Outcome) =>
      retainedSandwich (R := R) (operators original outcome) (state.block original)
  have selected := selected_transition_blocks transition record operators blocks
    beforeRead value state result
  have filtered := retained_filter_sum record beforeRead afterRead preserved parts result value
  have unselected := (blocks state result).symm
  have final := selected_state_block_matrix (transition state) afterRead value result
  exact selected.trans (filtered.trans
    ((congrArg (fun matrix : HilbertOperator R =>
      if afterRead result = value then matrix else 0) unselected).trans final.symm))

private lemma retained_select_read {Original Result Outcome Value : Type}
    [Fintype Original] [Fintype Result] [Fintype Outcome]
    [DecidableEq Result] [DecidableEq Value] {R : Register}
    (transition : ExecutionState Original R → ExecutionState Result R)
    (record : Original → Outcome → Result)
    (operators : Original → Outcome → HilbertOperator R)
    (blocks : retainedBlocks transition record operators)
    (beforeRead : Original → Value) (afterRead : Result → Value)
    (preserved : ∀ original outcome,
      afterRead (record original outcome) = beforeRead original)
    (value : Value) (state : ExecutionState Original R) :
    transition (state.selectClassical beforeRead value) =
      (transition state).selectClassical afterRead value := by
  apply ExecutionState.ext
  intro result
  exact DensityOperator.ext
    (retained_selected_block transition record operators blocks beforeRead afterRead
      preserved value state result)

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
    {services : ClassicalOracleModel}
    {code : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true}
    {Outcome : Type} [Fintype Outcome]
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment}

/-- An actual protected read can be selected before or after the same full retained execution. -/
lemma recordedInstrument_select_read (actual : RecordedInstrument code Outcome environment)
    {Value : Type} [DecidableEq Value] (read : Store ctx → Value)
    (preserved : ∀ original outcome,
      read (actual.record original outcome).1.1 = read original.1)
    (value : Value) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    code.execute environment Reference
        (state.selectClassical (fun original => read original.1) value) =
      (code.execute environment Reference state).selectClassical
        (fun original => read original.1) value := by
  exact retained_select_read
    (fun input : State ctx Reference (services.HiddenState × History) =>
      code.execute environment Reference input)
    (sourceFullRetainedRecord actual.record)
    (fun original outcome => Execution.Instrument.referenceLift Reference
      (actual.operator (original.1, original.2.1) outcome))
    (by
      intro input result
      exact (actual.blocks Reference input result).trans (sum_condition_decisions _ _ _ _))
    (fun original => read original.1) (fun result => read result.1)
    (fun original outcome => preserved (original.1, original.2.1) outcome) value state

private lemma instrument_select_read {allocation : Bool}
    {code : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx allocation}
    (actual : Instrument code Outcome environment) {Value : Type} [DecidableEq Value]
    (read : Store ctx → Value)
    (preserved : ∀ original outcome, read (actual.record original outcome).1 = read original)
    (value : Value) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    code.execute environment Reference
        (state.selectClassical (fun original => read original.1) value) =
      (code.execute environment Reference state).selectClassical
        (fun original => read original.1) value := by
  exact retained_select_read
    (fun input : State ctx Reference (services.HiddenState × History) =>
      code.execute environment Reference input)
    (sourceFullRetainedRecord (fun original outcome =>
      let next := actual.record original.1 outcome
      ((next.1, original.2), next.2)))
    (fun original outcome => Execution.Instrument.referenceLift Reference (actual.operator
      original.1 outcome))
    (by
      intro input result
      exact (actual.blocks Reference input result).trans (sum_condition_decisions _ _ _ _))
    (fun original => read original.1) (fun result => read result.1)
    (fun original outcome => preserved original.1 outcome) value state

private lemma read_weight_selected_mass {Reference : Register} {Label : Type} [Fintype Label]
    (state : State ctx Reference Label) (read : Store ctx → Bool) (flag : Bool) :
    CheckerTail.readWeight state read flag =
      (state.selectClassical (fun original => read original.1) flag).mass := by
  unfold CheckerTail.readWeight ExecutionState.effectWeight
  rw [ExecutionState.selectClassical_mass]
  apply Finset.sum_congr rfl
  intro original _
  unfold flagEffect
  by_cases selected : read original.1 = flag
  · simp only [selected, if_true, Effect.weight_one]
  · simp only [selected, if_false, Effect.weight_zero]

/-- Protected actual records retain the original flag's subnormalized mass, with any Reference. -/
lemma recordedInstrument_flag_weight (actual : RecordedInstrument code Outcome environment)
    (read : Store ctx → Bool)
    (preserved : ∀ original outcome,
      read (actual.record original outcome).1.1 = read original.1)
    (flag : Bool) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    CheckerTail.readWeight (code.execute environment Reference state) read flag =
      CheckerTail.readWeight state read flag := by
  refine (read_weight_selected_mass _ read flag).trans ?_
  refine (congrArg ExecutionState.mass
    (recordedInstrument_select_read actual read preserved flag state)).symm.trans ?_
  exact (code.execute_mass environment Reference
    (state.selectClassical (fun original => read original.1) flag)).trans
      (read_weight_selected_mass state read flag).symm


private def SelectsRead {allocation : Bool} (read : Store ctx → Bool) (flag : Bool)
    (program : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx allocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    program.execute environment Reference
        (state.selectClassical (fun original => read original.1) flag) =
      (program.execute environment Reference state).selectClassical
        (fun original => read original.1) flag

private lemma selects_read_flag_weight {allocation : Bool} (read : Store ctx → Bool)
    (flag : Bool)
    (program : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx allocation)
    (selected : SelectsRead read flag program environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    CheckerTail.readWeight (program.execute environment Reference state) read flag =
      CheckerTail.readWeight state read flag := by
  refine (read_weight_selected_mass _ read flag).trans ?_
  refine (congrArg ExecutionState.mass (selected state)).symm.trans ?_
  exact (program.execute_mass environment Reference
    (state.selectClassical (fun original => read original.1) flag)).trans
      (read_weight_selected_mass state read flag).symm

private lemma mapped_select_read {Original Result Value : Type}
    [Fintype Original] [Fintype Result] [DecidableEq Result] [DecidableEq Value]
    {R : Register} (state : ExecutionState Original R) (update : Original → Result)
    (beforeRead : Original → Value) (afterRead : Result → Value)
    (preserved : ∀ original, afterRead (update original) = beforeRead original)
    (value : Value) :
    (state.selectClassical beforeRead value).mapClassical update =
      (state.mapClassical update).selectClassical afterRead value := by
  have reads : afterRead ∘ update = beforeRead := funext preserved
  have selected := ExecutionState.mapClassical_selectClassical state update afterRead value
  rw [reads] at selected
  exact selected.symm

private lemma history_select_read {H K : Type} [Fintype H] [Fintype K]
    {Reference : Register} (state : State ctx Reference H) (update : H → K)
    (read : Store ctx → Bool) (flag : Bool) :
    State.mapHistory (ctx := ctx) (Reference := Reference)
        (state.selectClassical (fun original => read original.1) flag) update =
      (State.mapHistory (ctx := ctx) (Reference := Reference) state update).selectClassical
        (fun result => read result.1) flag := by
  unfold State.mapHistory
  exact @mapped_select_read (Store ctx × H) (Store ctx × K) Bool _ _
    _ (inferInstance : DecidableEq Bool)
    (Register.prod ctx.register Reference) state
    (fun original => (original.1, update original.2))
    (fun original => read original.1) (fun result => read result.1) (fun _ => rfl) flag

private lemma mapped_unitary_select_read {Original Result Value : Type}
    [Fintype Original] [Fintype Result] [DecidableEq Result] [DecidableEq Value]
    {R : Register} (state : ExecutionState Original R)
    (operators : Original → UnitaryOperator R) (update : Original → Result)
    (beforeRead : Original → Value) (afterRead : Result → Value)
    (preserved : ∀ original, afterRead (update original) = beforeRead original)
    (value : Value) :
    ((state.selectClassical beforeRead value).applyUnitary operators).mapClassical update =
      ((state.applyUnitary operators).mapClassical update).selectClassical afterRead value := by
  have unitarySelected :=
    (ExecutionState.selectClassical_applyUnitary state operators beforeRead value).symm
  exact (congrArg (fun middle : ExecutionState Original R => middle.mapClassical update)
    unitarySelected).trans
      (mapped_select_read (state.applyUnitary operators) update beforeRead afterRead
        preserved value)

private lemma selects_read_seq {allocation : Bool} (read : Store ctx → Bool) (flag : Bool)
    (first last : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allocation)
    (head : SelectsRead read flag first environment)
    (tail : SelectsRead read flag last environment) :
    SelectsRead read flag (first.seq last) environment := by
  intro Reference History finite state
  have headSelected := @head Reference History finite state
  have tailSelected := @tail Reference (History × first.Path) inferInstance
    (first.execute environment Reference state)
  have both := (congrArg
    (fun middle : State ctx Reference (services.HiddenState × (History × first.Path)) =>
      last.execute environment Reference middle) headSelected).trans tailSelected
  simp only [Circuit.execute_seq]
  exact (congrArg
    (fun final : State ctx Reference
      (services.HiddenState × ((History × first.Path) × last.Path)) =>
      State.mapHistory (ctx := ctx) (Reference := Reference) final
        (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))))
    both).trans (history_select_read (ctx := ctx) (Reference := Reference)
      (last.execute environment Reference (first.execute environment Reference state))
      (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) read flag)

private lemma selects_read_id {allocation : Bool} (read : Store ctx → Bool) (flag : Bool) :
    SelectsRead read flag (Circuit.id
      (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := allocation) ctx) environment := by
  intro Reference History _ state
  simp only [Circuit.execute_id]
  exact @mapped_select_read (Store ctx × (services.HiddenState × History))
    (Store ctx × (services.HiddenState × (History × Unit))) Bool _ _
    _ (inferInstance : DecidableEq Bool)
    (Register.prod ctx.register Reference) state
    (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
    (fun original => read original.1) (fun result => read result.1) (fun _ => rfl) flag

private lemma selects_read_unitary {allocation : Bool} (read : Store ctx → Bool) (flag : Bool)
    (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout) :
    SelectsRead read flag (Circuit.unitary (allowAllocation := allocation)
      (operations := operations) (classicalOracles := services) program) environment := by
  intro Reference History _ state
  rw [Circuit.execute_unitary, Circuit.execute_unitary]
  exact @mapped_unitary_select_read (Store ctx × (services.HiddenState × History))
    (Store ctx × (services.HiddenState × (History × Unit))) Bool _ _
    _ (inferInstance : DecidableEq Bool)
    (Register.prod ctx.register Reference) state
    (fun _ => UnitaryOperator.prodTensor (program.matrix environment.quantum)
      (1 : UnitaryOperator Reference))
    (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
    (fun original => read original.1) (fun result => read result.1) (fun _ => rfl) flag

private lemma selects_read_range {allocation : Bool} (read : Store ctx → Bool) (flag : Bool)
    (count : Nat)
    (body : Fin count → Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allocation) (each : ∀ index, SelectsRead read flag (body index) environment) :
    SelectsRead read flag (Circuit.forRange count body) environment := by
  induction count with
  | zero => exact selects_read_id read flag
  | succ count inductionHypothesis =>
      exact selects_read_seq read flag _ _ (each 0)
        (inductionHypothesis (fun index => body index.succ) (fun index => each index.succ))

private lemma selects_read_identity_embed (read : Store ctx → Bool) (flag : Bool)
    (program : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false)
    (selected : SelectsRead read flag program environment) :
    SelectsRead read flag (Circuit.embed (allowAllocation := true)
      (model := .quantum AlgorithmGate.model .empty operations services)
      (ContextEmbedding.identity ctx) program) environment := by
  intro Reference History _ state
  rw [Circuit.execute_identity_embed, Circuit.execute_identity_embed]
  exact selected state

private def bitRead (observed : CStorageRef ctx .bit) (store : Store ctx) : Bool :=
  (store.read (.storage observed)).toBool

private lemma finite_bit_key_ne {dimension : ℕ+}
    (output : CWriteRef ctx (.finite dimension)) (observed : CStorageRef ctx .bit) :
    output.key ≠ observed.key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key output.toCStorageRef observed same
  cases shapes

private lemma reset_selects_bit (parameters : Cleanup.Parameters ctx) (count : Nat)
    (wires : Fin count → Fin ctx.systemCount) (observed : CStorageRef ctx .bit) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (bitRead observed) flag (parameters.run count wires) environment := by
  apply selects_read_range
  intro index Reference History _ state
  apply instrument_select_read (resetOneInstrument parameters (wires index) environment)
  intro store outcome
  exact congrArg (fun value : CShape.Value .bit => value.toBool)
    (Store.read_write_other store (parameters.outputAt (wires index)) observed
      (.finite outcome) (finite_bit_key_ne _ observed))

/-- The real whole-bank cleanup preserves the mass selected by any existing
Boolean storage cell, for every input state, external reference and history. -/
lemma cleanup_circuit_flag_weight (parameters : Cleanup.Parameters ctx)
    (observed : CStorageRef ctx .bit) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    CheckerTail.readWeight
        ((parameters.circuit (services := services)).execute environment Reference state)
        (fun store => (store.read (.storage observed)).toBool) flag =
      CheckerTail.readWeight state
        (fun store => (store.read (.storage observed)).toBool) flag := by
  have selected : SelectsRead (bitRead observed) flag
      (parameters.circuit (services := services)) environment := by
    change SelectsRead (bitRead observed) flag
      (parameters.run ctx.systemCount id) environment
    exact reset_selects_bit parameters ctx.systemCount id observed flag environment
  change CheckerTail.readWeight
      ((parameters.circuit (services := services)).execute environment Reference state)
      (bitRead observed) flag =
    CheckerTail.readWeight state (bitRead observed) flag
  exact selects_read_flag_weight (bitRead observed) flag
    (parameters.circuit (services := services)) selected state

private lemma reset_embedded_selects_bit (parameters : Cleanup.Parameters ctx) (count : Nat)
    (wires : Fin count → Fin ctx.systemCount) (observed : CStorageRef ctx .bit) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (bitRead observed) flag
      (Circuit.embed (allowAllocation := true)
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (ContextEmbedding.identity ctx) (parameters.run count wires)) environment := by
  intro Reference History _ state
  rw [Circuit.execute_identity_embed, Circuit.execute_identity_embed]
  exact reset_selects_bit parameters count wires observed flag environment state

private lemma fourier_selects_bit {totalBits active : Nat}
    (ports : QuantumFourierTransform.Semiclassical.Window.Ports ctx totalBits active)
    (observed : CStorageRef ctx .bit) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (bitRead observed) flag
      (QuantumFourierTransform.Semiclassical.Window.liftedInverse
        (operations := BitWord.model) (services := services) (allowAllocation := true) ports)
      environment := by
  intro Reference History _ state
  apply instrument_select_read (fourierInstrument ports environment)
  intro store outcome
  apply congrArg (fun value : CShape.Value .bit => value.toBool)
  change (QuantumFourierTransform.Semiclassical.Window.inverseStoreRecord
    (operations := BitWord.model) (services := services) ports store outcome).1.read
      (.storage observed) = store.read (.storage observed)
  rw [QuantumFourierTransform.Semiclassical.Window.inverseStoreRecord_store]
  exact QuantumFourierTransform.Semiclassical.Window.window_outcomeStore_read_untouched
    active ports store outcome observed (fun index => finite_bit_key_ne _ observed)

private lemma sequence_selects_bit (parameters : Parameters ctx)
    (observed : CStorageRef ctx .bit) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (blocks : ∀ index, SelectsRead (bitRead observed) flag (parameters.block index) environment)
    (indices : List WindowIndex) :
    SelectsRead (bitRead observed) flag (parameters.sequence indices) environment := by
  induction indices with
  | nil => exact selects_read_id _ _
  | cons index indices inductionHypothesis =>
      exact selects_read_seq _ _ _ _ (blocks index) inductionHypothesis

private lemma candidate_weight_selected {Reference : Register} {Label : Type} [Fintype Label]
    (state : State ctx Reference Label) (prior current : Store ctx → Bool) :
    candidateWeight state prior current =
      CheckerTail.readWeight
        (state.selectClassical (fun original => prior original.1) false) current true := by
  unfold candidateWeight CheckerTail.readWeight
  rw [ExecutionState.effectWeight_selectClassical]
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro original _
  cases before : prior original.1 <;> cases after : current original.1 <;>
    simp [flagEffect, before, after]

private lemma lifted_write_free {outer inner : RuntimeCtx .quantum}
    (lift : Transport outer inner) {outputShape inputShape : CShape}
    (output : CWriteRef outer outputShape) (input : CInputRef outer inputShape)
    (free : output.key ∉ input.storageKeys) :
    (lift.liftWrite output).key ∉ (lift.liftInput input).storageKeys := by
  simpa only [Transport.liftWrite_key, Transport.liftInput_storageKeys] using free

private def DriverBitSeparation (parameters : Driver.Parameters ctx)
    (observed : CStorageRef ctx .bit) : Prop :=
  (∀ bit, (parameters.output bit).key ≠ observed.key) ∧
    parameters.mask.key ≠ observed.key ∧
      (∀ bit, (parameters.parity bit).key ≠ observed.key) ∧
        parameters.temporary.key ≠ observed.key

private lemma original_bit_key_free {outer inner : RuntimeCtx .quantum}
    (lift : Transport outer inner) {shape : CShape} (output : CWriteRef inner shape)
    (observed : CStorageRef outer .bit)
    (free : output.key ∉ (lift.liftInput (.storage observed)).storageKeys) :
    output.key ≠ (lift.liftStorage observed).key := by
  simpa only [Transport.liftInput_storageKeys, CInputRef.storageKeys,
    List.mem_singleton, Transport.liftStorage_key] using free

private lemma different_of_equal {Value : Type} {left middle right : Value}
    (same : left = middle) (different : middle ≠ right) : left ≠ right :=
  fun matching => different (same.symm.trans matching)

/-- The specified actual Driver retains an original Boolean read in every real record. -/
private lemma named_driver_read_bit (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (observed : CStorageRef ctx .bit)
    (outputFree : ∀ bit, (parameters.output bit).key ≠ observed.key)
    (maskFree : parameters.mask.key ≠ observed.key)
    (parityFree : ∀ bit, (parameters.parity bit).key ≠ observed.key)
    (temporaryFree : parameters.temporary.key ≠ observed.key) :
    NamedDriverPreservesRead parameters frame spec row environment observed := by
  apply namedDriverInstrument_read_separate parameters frame spec row environment observed
    ?_ outputFree maskFree parityFree temporaryFree
  intro key written
  simp only [frameWorkKeys, List.mem_cons, List.not_mem_nil, or_false] at written
  rcases written with rfl | rfl | rfl | rfl
  all_goals exact write_shape_key_ne _ observed (by intro same; cases same)

private lemma named_driver_selects_bit (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (observed : CStorageRef ctx .bit) (flag : Bool)
    (separated : DriverBitSeparation parameters observed) :
    SelectsRead (bitRead observed) flag (Driver.circuit parameters frame spec row)
      environment := by
  let chosen := namedDriverInstrument parameters frame spec row environment
  let _ : Fintype chosen.1 := chosen.2.1
  intro Reference History _ state
  apply recordedInstrument_select_read chosen.2.2
  intro before outcome
  exact congrArg (fun value : CShape.Value .bit => value.toBool)
    (named_driver_read_bit parameters frame spec row environment observed
      separated.1 separated.2.1 separated.2.2.1 separated.2.2.2 before outcome)

namespace Inputs

variable {outer inner final : RuntimeCtx .quantum} (original : Inputs outer)
    (lift : Transport outer inner)
    (same : outer.quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (index : WindowIndex) (tableLift : Transport inner final)
    (tableSame : inner.quantumLayout.wires = final.quantumLayout.wires)
    (arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays final 256
      (2 ^ (index.highRemaining + index.lowWidth + 1)))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

/-- The actual fresh feedback frame protects every original structural read in each point record. -/
lemma fresh_point_record_read {shape : CShape} (observed : CInputRef outer shape) :
    let parameters := Driver.kernelParameters
      ((original.samplerParameters lift same scratch fresh).pointParameters index)
      tableLift tableSame arrays
    Chain.Program.Parameters.InstrumentPreservesRead
      (parameters.pointProgramInstrument environment)
      (tableLift.liftInput (lift.liftInput observed)) := by
  apply Chain.Program.Parameters.pointProgramInstrument_read
  · intro bit
    exact lifted_write_free tableLift _ _ (fresh.output bit observed)
  · exact lifted_write_free tableLift _ _ (fresh.mask observed)
  · intro bit
    exact lifted_write_free tableLift _ _
      (fresh.parity (Fin.castLE index.lowCapacity bit) observed)
  · exact lifted_write_free tableLift _ _ (fresh.temporary observed)

private lemma fresh_point_output_key (original : Inputs outer)
    (lift : Transport outer inner)
    (same : outer.quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (index : WindowIndex) (bit : Fin 256) :
    (((original.samplerParameters lift same scratch fresh).pointParameters index).output bit).key =
      (scratch.output bit).key := rfl

private lemma fresh_point_mask_key (original : Inputs outer)
    (lift : Transport outer inner)
    (same : outer.quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (index : WindowIndex) :
    ((original.samplerParameters lift same scratch fresh).pointParameters index).mask.key =
      scratch.mask.key := rfl

private lemma fresh_point_parity_key (original : Inputs outer)
    (lift : Transport outer inner)
    (same : outer.quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (index : WindowIndex) (bit : Fin (2 ^ index.lowWidth)) :
    (((original.samplerParameters lift same scratch fresh).pointParameters index).parity bit).key =
      (scratch.parity (Fin.castLE index.lowCapacity bit)).key := rfl

private lemma fresh_point_temporary_key (original : Inputs outer)
    (lift : Transport outer inner)
    (same : outer.quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (index : WindowIndex) :
    ((original.samplerParameters lift same scratch fresh).pointParameters index).temporary.key =
      scratch.temporary.key := rfl

private lemma fresh_bit_separation (observed : CStorageRef outer .bit) :
    DriverBitSeparation
      ((original.samplerParameters lift same scratch fresh).pointParameters index)
      (lift.liftStorage observed) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro bit
    exact different_of_equal (fresh_point_output_key original lift same scratch fresh index bit)
      (original_bit_key_free lift (scratch.output bit) observed
        (fresh.output bit (.storage observed)))
  · exact different_of_equal (fresh_point_mask_key original lift same scratch fresh index)
      (original_bit_key_free lift scratch.mask observed (fresh.mask (.storage observed)))
  · intro bit
    exact different_of_equal (fresh_point_parity_key original lift same scratch fresh index bit)
      (original_bit_key_free lift (scratch.parity (Fin.castLE index.lowCapacity bit)) observed
        (fresh.parity (Fin.castLE index.lowCapacity bit) (.storage observed)))
  · exact different_of_equal (fresh_point_temporary_key original lift same scratch fresh index)
      (original_bit_key_free lift scratch.temporary observed
        (fresh.temporary (.storage observed)))

/-- The actual constructed-table Driver retains every original Boolean cell in each full record. -/
lemma fresh_driver_record_read_bit (observed : CStorageRef outer .bit) :
    let sampler := original.samplerParameters lift same scratch fresh
    let chosen := namedDriverInstrument (sampler.pointParameters index)
      sampler.frame sampler.modulus index.row environment
    letI : Fintype chosen.1 := chosen.2.1
    ∀ before outcome, (chosen.2.2.record before outcome).1.1.read
        (.storage (lift.liftStorage observed)) =
      before.1.read (.storage (lift.liftStorage observed)) := by
  let separated := original.fresh_bit_separation lift same scratch fresh index observed
  exact named_driver_read_bit
    ((original.samplerParameters lift same scratch fresh).pointParameters index)
    (original.samplerParameters lift same scratch fresh).frame
    (original.samplerParameters lift same scratch fresh).modulus index.row environment
    (lift.liftStorage observed) separated.1 separated.2.1 separated.2.2.1 separated.2.2.2

private lemma fresh_driver_selects_bit (observed : CStorageRef outer .bit) (flag : Bool) :
    let sampler := original.samplerParameters lift same scratch fresh
    SelectsRead (bitRead (lift.liftStorage observed)) flag
      (Driver.circuit (sampler.pointParameters index) sampler.frame sampler.modulus index.row)
      environment := by
  exact named_driver_selects_bit
    ((original.samplerParameters lift same scratch fresh).pointParameters index)
    (original.samplerParameters lift same scratch fresh).frame
    (original.samplerParameters lift same scratch fresh).modulus index.row environment
    (lift.liftStorage observed) flag
    (original.fresh_bit_separation lift same scratch fresh index observed)

private lemma fresh_block_selects_bit (observed : CStorageRef outer .bit) (flag : Bool) :
    let sampler := original.samplerParameters lift same scratch fresh
    SelectsRead (bitRead (lift.liftStorage observed)) flag (sampler.block index) environment := by
  dsimp only
  unfold Parameters.block
  apply selects_read_seq
  · exact reset_embedded_selects_bit _ (index.lowerWidth + 1) _ _ flag environment
  · apply selects_read_seq
    · exact selects_read_unitary _ _ _
    · apply selects_read_seq
      · exact original.fresh_driver_selects_bit lift same scratch fresh index environment
          observed flag
      · exact fourier_selects_bit _ _ flag environment

/-- The actual thirty-four-window sampler commutes with selecting any original Boolean read. -/
lemma fresh_sampler_selects_bit (observed : CStorageRef outer .bit) (flag : Bool) :
    SelectsRead (bitRead (lift.liftStorage observed)) flag
      (Sampling.circuit (original.samplerParameters lift same scratch fresh)) environment := by
  apply sequence_selects_bit
  intro index
  exact original.fresh_block_selects_bit lift same scratch fresh index environment observed flag

private lemma restart_selects_bit {ctx : RuntimeCtx .quantum} (original : Inputs ctx)
    (output : CWriteRef ctx (.finite 2)) (observed : CStorageRef ctx .bit) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (bitRead observed) flag (original.restart output) environment := by
  dsimp only [restart, Cleanup.Parameters.prepared, Cleanup.Parameters.circuit]
  apply selects_read_identity_embed
  apply selects_read_seq
  · exact reset_selects_bit _ ctx.systemCount id observed flag environment
  · exact selects_read_unitary _ _ _

/-- Real bank restart, paid loader and actual34 sampler retain the same selected flag substate. -/
lemma fresh_preparation_selects_bit (observed : CStorageRef outer .bit) (flag : Bool) :
    let sampler := original.samplerParameters lift same scratch fresh
    SelectsRead (bitRead (lift.liftStorage observed)) flag
      ((original.transport lift same).preparation sampler) environment := by
  unfold preparation
  apply selects_read_seq
  · exact restart_selects_bit _ _ _ flag environment
  · exact original.fresh_sampler_selects_bit lift same scratch fresh environment observed flag

/-- The full actual preparation keeps either original flag mass, without normalization. -/
lemma fresh_preparation_flag_weight (observed : CStorageRef outer .bit) (flag : Bool)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)) :
    let sampler := original.samplerParameters lift same scratch fresh
    CheckerTail.readWeight
        (((original.transport lift same).preparation sampler).execute environment Reference state)
        (bitRead (lift.liftStorage observed)) flag =
      CheckerTail.readWeight state (bitRead (lift.liftStorage observed)) flag :=
  selects_read_flag_weight _ _ _
    (original.fresh_preparation_selects_bit lift same scratch fresh environment observed flag) state

/-- The joint candidate observation is the same preparation on its actual flag-false prefix. -/
lemma fresh_preparation_candidate_weight (observed : CStorageRef outer .bit)
    (current : Store inner → Bool) {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)) :
    let sampler := original.samplerParameters lift same scratch fresh
    candidateWeight
        (((original.transport lift same).preparation sampler).execute environment Reference state)
        (bitRead (lift.liftStorage observed)) current =
      CheckerTail.readWeight
        (((original.transport lift same).preparation sampler).execute environment Reference
          (state.selectClassical
            (fun before => bitRead (lift.liftStorage observed) before.1) false)) current true := by
  refine (candidate_weight_selected _ _ current).trans ?_
  apply congrArg (fun prepared => CheckerTail.readWeight prepared current true)
  exact (original.fresh_preparation_selects_bit lift same scratch fresh environment
    observed false state).symm

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
