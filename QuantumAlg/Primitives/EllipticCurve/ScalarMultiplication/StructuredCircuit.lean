/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.BaseGateRealization
public import QuantumAlg.Primitives.EllipticCurve.PointAddition.StructuredCircuit
public import QuantumAlg.Primitives.EllipticCurve.ScalarMultiplicationEndpoint

/-!
# Encoded base-gate scalar-multiplication witnesses

This module provides the gate-structured fixed-base scalar-multiplication
interfaces.  The trace layer lifts schedule-indexed controlled-ECADD step
programs into one scalar trace circuit.  The endpoint layer keeps the public
certified scalar-action wrapper for a final coordinate-target program.  The
schedule follows the fixed-base controlled-addition route used in
elliptic-curve discrete-log resource estimates [RNSL17,
ECDLP.tex:589-597,650-699], with generic affine point-addition branches from
Proos--Zalka [PZ03, ecc.tex:448-462,525-551].  In both layers, the folded
`Circuit` is the same object used for encoded-basis correctness and resource
accounting.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ScalarMultiplication

namespace TraceCircuitWitness

variable {p : Nat}

noncomputable section

/-- Schedule order used by the scalar-multiplication trace circuit. -/
def stepIndices {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E) :
    List (Fin schedule.length) :=
  List.ofFn fun i : Fin schedule.length => i

/-- Semantic trace updates in schedule order. -/
def stepUpdates (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) :
    List (TraceData E schedule -> TraceData E schedule) :=
  (stepIndices schedule).map fun i =>
    TraceData.controlledEquivAt E schedule i

/-- Folded semantic action of the schedule-ordered controlled-ECADD trace. -/
def sequentialStep (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) :
    TraceData E schedule -> TraceData E schedule :=
  BaseGateProgram.Realizes.stepList (stepUpdates E schedule)

private theorem stepList_eq_foldl
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (l : List (Fin schedule.length))
    (x : TraceData E schedule) :
    BaseGateProgram.Realizes.stepList
        (l.map fun i => TraceData.controlledEquivAt E schedule i) x =
      l.foldl (fun y i => TraceData.controlledEquivAt E schedule i y) x := by
  induction l generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simpa [BaseGateProgram.Realizes.stepList, List.foldl_cons] using
        ih (TraceData.controlledEquivAt E schedule i x)

private theorem traceDataFold_apply_of_nodup
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E)
    (l : List (Fin schedule.length)) (hnodup : l.Nodup)
    (x : TraceData E schedule) (j : Fin schedule.length) :
    (l.foldl (fun y i => TraceData.controlledEquivAt E schedule i y) x) j =
      if j ∈ l then (x j).addIntoTarget else x j := by
  induction l generalizing x j with
  | nil =>
      simp
  | cons i rest ih =>
      have hnot : i ∉ rest := (List.nodup_cons.mp hnodup).1
      have hnodup_tail : rest.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hji : j = i
      · subst j
        have h := ih hnodup_tail (TraceData.controlledEquivAt E schedule i x) i
        simp [hnot] at h
        simpa [hnot] using h
      · have h := ih hnodup_tail (TraceData.controlledEquivAt E schedule i x) j
        by_cases hjmem : j ∈ rest
        · simp [hji, hjmem] at h ⊢
          simpa [TraceData.controlledEquivAt_apply_ne E schedule hji x] using h
        · simp [hji, hjmem] at h ⊢
          simpa [TraceData.controlledEquivAt_apply_ne E schedule hji x] using h

/-- The folded same-Circuit trace step agrees extensionally with the existing
schedule-wide controlled-ECADD trace endpoint. -/
theorem sequentialStep_apply
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (x : TraceData E schedule) :
    sequentialStep E schedule x = TraceData.controlledEquiv E schedule x := by
  funext i
  let indices := stepIndices schedule
  have hfold :=
    stepList_eq_foldl E schedule indices x
  have hnodup : indices.Nodup := by
    dsimp [indices, stepIndices]
    exact List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ indices := by
    dsimp [indices, stepIndices]
    simp
  have hcomponent :=
    traceDataFold_apply_of_nodup E schedule indices hnodup x i
  rw [show (sequentialStep E schedule x) i =
      (indices.foldl
        (fun y i => TraceData.controlledEquivAt E schedule i y) x) i by
        dsimp [sequentialStep, stepUpdates, indices, stepIndices] at hfold
        exact congrArg (fun y => y i) hfold]
  simpa [hmem] using hcomponent

/-- A controlled-ECADD component lifted over the scalar trace register.  The
only accepted trace-step program is obtained by applying `liftProgram` to the
selected lower-level decomposed controlled-ECADD program. -/
structure StepLift (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (encoding : BinaryLabelEncoding (TraceData E schedule))
    (i : Fin schedule.length) where
  /-- Lower-level decomposed controlled-ECADD witness for the selected addend. -/
  controlledWitness :
    ControlledPointAddition.DecomposedWitness E (schedule.addend i)
  /-- Explicit embedding of the selected lower-level program into the scalar
  trace register. -/
  liftProgram :
    BaseGateProgram controlledWitness.encoding.width ->
      BaseGateProgram encoding.width
  /-- The lifted lower-level program updates exactly the selected trace
  component. -/
  realizes :
    BaseGateProgram.Realizes encoding
      (liftProgram controlledWitness.program)
      (TraceData.controlledEquivAt E schedule i)

namespace StepLift

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E}
variable {encoding : BinaryLabelEncoding (TraceData E schedule)}
variable {i : Fin schedule.length}

/-- Lower-level controlled-ECADD program consumed by the scalar trace lift. -/
def sourceProgram (w : StepLift E schedule encoding i) :
    BaseGateProgram w.controlledWitness.encoding.width :=
  w.controlledWitness.program

/-- Lifted base-gate program acting on the full scalar trace register. -/
def program (w : StepLift E schedule encoding i) :
    BaseGateProgram encoding.width :=
  w.liftProgram w.sourceProgram

/-- The lifted scalar trace program is definitionally derived from the
lower-level controlled-ECADD program. -/
theorem program_eq_lifted (w : StepLift E schedule encoding i) :
    w.program = w.liftProgram w.sourceProgram :=
  rfl

/-- The lower-level controlled-ECADD witness consumed by this lift is
base-gate structured. -/
theorem source_structured (w : StepLift E schedule encoding i) :
    (BaseGateSameCircuitWitness.circuit
      w.controlledWitness.sameCircuit).history.IsBaseGateStructured :=
  ControlledPointAddition.DecomposedWitness.structured w.controlledWitness

/-- Encoded-basis action of the lifted selected trace component. -/
theorem apply_ket (w : StepLift E schedule encoding i)
    (x : TraceData E schedule) :
    Circuit.apply (BaseGateProgram.toCircuit w.program).circuit
        ((PureState.ket (R := Qubits encoding.width) (encoding.encode x) :
          PureState (Qubits encoding.width)) :
          StateVector (Qubits encoding.width)) =
      (PureState.ket (R := Qubits encoding.width)
        (encoding.encode (TraceData.controlledEquivAt E schedule i x)) :
        StateVector (Qubits encoding.width)) :=
  by
    simpa [program, sourceProgram] using
      BaseGateProgram.toCircuit_apply_encoded_ket w.realizes x

end StepLift

/-- A scalar trace circuit assembled from schedule-indexed controlled-ECADD
components.  This is the gate-level schedule fold: the final `program` below is
an `appendList` of the lifted controlled-addition step programs, not a supplied
monolithic endpoint permutation. -/
structure ScheduleCompositionWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (schedule : Schedule E) where
  /-- Common scalar-trace encoding used by every lifted step. -/
  encoding : BinaryLabelEncoding (TraceData E schedule)
  /-- One lifted controlled-ECADD witness for each schedule index. -/
  stepLift :
    (i : Fin schedule.length) -> StepLift E schedule encoding i

namespace ScheduleCompositionWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E}

/-- Lifted step programs in schedule order. -/
def stepPrograms (w : ScheduleCompositionWitness E schedule) :
    List (BaseGateProgram w.encoding.width) :=
  (stepIndices schedule).map fun i => (w.stepLift i).program

/-- Folded scalar trace program obtained by appending the lifted step programs. -/
def program (w : ScheduleCompositionWitness E schedule) :
    BaseGateProgram w.encoding.width :=
  BaseGateProgram.appendList w.stepPrograms

/-- The lifted step programs realize the schedule-ordered trace updates. -/
theorem stepRealizes (w : ScheduleCompositionWitness E schedule) :
    List.Forall₂
      (fun program step => BaseGateProgram.Realizes w.encoding program step)
      w.stepPrograms (stepUpdates E schedule) := by
  dsimp [stepPrograms, stepUpdates, stepIndices]
  induction List.ofFn (fun i : Fin schedule.length => i) with
  | nil =>
      constructor
  | cons i rest ih =>
      constructor
      · simpa [StepLift.program, StepLift.sourceProgram] using
          (w.stepLift i).realizes
      · exact ih

/-- Same-Circuit witness for the folded scalar trace schedule. -/
def sequentialSameCircuit (w : ScheduleCompositionWitness E schedule) :
    BaseGateSameCircuitWitness (TraceData E schedule)
      (sequentialStep E schedule) where
  encoding := w.encoding
  program := w.program
  realizes := by
    dsimp [program, stepPrograms, sequentialStep]
    exact
      BaseGateProgram.Realizes.appendList w.encoding
        w.stepPrograms (stepUpdates E schedule) w.stepRealizes

/-- Same-Circuit witness for the schedule-wide controlled-ECADD trace
endpoint. -/
def sameCircuit (w : ScheduleCompositionWitness E schedule) :
    BaseGateSameCircuitWitness (TraceData E schedule)
      (TraceData.controlledEquiv E schedule) :=
  (w.sequentialSameCircuit).congrStep
    (sequentialStep_apply E schedule)

/-- The folded scalar trace circuit history bottoms out in X/CNOT/Toffoli
atoms. -/
theorem structured (w : ScheduleCompositionWitness E schedule) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.sameCircuit

/-- Encoded-basis correctness for the composed scalar trace circuit. -/
theorem apply_ket (w : ScheduleCompositionWitness E schedule)
    (x : TraceData E schedule) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (TraceData.controlledEquiv E schedule x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit x

/-- Certified-run form of the composed trace action: every schedule component
is advanced by its controlled-ECADD endpoint. -/
theorem apply_certified_run (w : ScheduleCompositionWitness E schedule)
    (run : Run E schedule) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode run.controlledTraceData) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode run.updatedTraceData) :
        StateVector (Qubits w.encoding.width)) := by
  have htrace :
      TraceData.controlledEquiv E schedule run.controlledTraceData =
        run.updatedTraceData := by
    funext i
    rfl
  simpa [htrace] using
    apply_ket (E := E) (schedule := schedule) w run.controlledTraceData

/-- Resource counters are projected from the same folded scalar trace circuit
used for correctness. -/
theorem resources_eq (w : ScheduleCompositionWitness E schedule) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Circuit depth is projected from the same folded scalar trace circuit. -/
theorem depth_eq (w : ScheduleCompositionWitness E schedule) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Query depth is projected from the same folded scalar trace circuit. -/
theorem queryDepth_eq (w : ScheduleCompositionWitness E schedule) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

/-- Resource-correct witness for the composed scalar trace schedule. -/
def resourceCorrectWitness (w : ScheduleCompositionWitness E schedule) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ x : TraceData E schedule,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
          ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (TraceData.controlledEquiv E schedule x)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.sameCircuit
  correctness := apply_ket w
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end ScheduleCompositionWitness

end

end TraceCircuitWitness

namespace CertifiedEndpoint

variable {p : Nat}

noncomputable section

namespace ComposedEndpoint

/-- Endpoint data paired with the certified schedule run used by a composed
scalar-multiplication endpoint. -/
structure EndpointRunState (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) where
  /-- Public scalar endpoint data: scalar/start input and coordinate targets. -/
  data : Data E schedule cert
  /-- Certified run supplying the controlled-addition schedule trace. -/
  run : Run E schedule

/-- Composed scalar endpoint state: public endpoint/run data paired with the
controlled-ECADD trace register consumed by the schedule circuit. -/
abbrev State (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :=
  EndpointRunState E schedule cert × TraceData E schedule

/-- Trace-circuit stage of the composed scalar endpoint. -/
def traceStep (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert -> State E schedule cert :=
  fun x => (x.1, TraceData.controlledEquiv E schedule x.2)

/-- Trace-circuit stage before rewriting the schedule fold to the
schedule-wide trace endpoint. -/
def traceSequentialStep (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert -> State E schedule cert :=
  fun x => (x.1, TraceCircuitWitness.sequentialStep E schedule x.2)

/-- Final target-write stage of the composed scalar endpoint.  The update uses
the certified run output after the controlled-addition schedule has been
consumed. -/
def targetStep (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert -> State E schedule cert :=
  fun x =>
    ({ x.1 with
        data :=
          { input := x.1.data.input
            targetX := x.1.data.targetX + x.1.run.outputPoint.x
            targetY := x.1.data.targetY + x.1.run.outputPoint.y
            flag := x.1.data.flag } },
      x.2)

/-- Folded semantic action of the composed scalar endpoint. -/
def fullStep (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert -> State E schedule cert :=
  targetStep E schedule cert ∘ traceStep E schedule cert

/-- Folded semantic action before rewriting the trace fold to the schedule-wide
trace endpoint. -/
def fullSequentialStep (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert -> State E schedule cert :=
  targetStep E schedule cert ∘ traceSequentialStep E schedule cert

/-- Clean composed endpoint execution: a trace initialized from the certified
run is advanced by the schedule circuit, and the endpoint targets receive the
run output. -/
theorem fullStep_clean
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (s : EndpointRunState E schedule cert)
    (houtput : s.run.outputPoint = s.data.outputPoint) :
    fullStep E schedule cert (s, s.run.controlledTraceData) =
      ({ s with data := s.data.addIntoTarget }, s.run.updatedTraceData) := by
  cases s with
  | mk data run =>
      have htrace :
          TraceData.controlledEquiv E schedule run.controlledTraceData =
            run.updatedTraceData := by
        funext i
        rfl
      simp [fullStep, traceStep, targetStep, htrace,
        Data.addIntoTarget, Data.outputPoint, houtput]

/-- Composed same-Circuit witness for the certified scalar endpoint.  The
program first runs the source-bound controlled-ECADD schedule trace circuit,
then runs the supplied final target-write program over the same state
encoding. -/
structure Witness (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) where
  /-- Encoding for the endpoint/run half of the composed state. -/
  endpointRunEncoding : BinaryLabelEncoding (EndpointRunState E schedule cert)
  /-- Source-bound schedule trace circuit assembled from controlled-ECADD steps. -/
  traceWitness : TraceCircuitWitness.ScheduleCompositionWitness E schedule
  /-- Final target-write program over the composed endpoint state. -/
  targetProgram :
    BaseGateProgram
      (BinaryLabelEncoding.prod endpointRunEncoding traceWitness.encoding).width
  /-- Correctness of the final target-write program under the composed
  endpoint encoding. -/
  targetRealizes :
    BaseGateProgram.Realizes
      (BinaryLabelEncoding.prod endpointRunEncoding traceWitness.encoding)
      targetProgram (targetStep E schedule cert)

namespace Witness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E} {cert : CertifiedScalarAction E schedule}

/-- Common encoding used by the composed scalar endpoint circuit. -/
def encoding (w : Witness E schedule cert) :
    BinaryLabelEncoding (State E schedule cert) :=
  BinaryLabelEncoding.prod w.endpointRunEncoding w.traceWitness.encoding

/-- Trace schedule witness lifted over the endpoint/run half of the composed
state. -/
def traceLiftedWitness (w : Witness E schedule cert) :
    BaseGateSameCircuitWitness (State E schedule cert)
      (traceSequentialStep E schedule cert) where
  encoding := w.encoding
  program :=
    BaseGateProgram.prodRight (m := w.endpointRunEncoding.width)
      w.traceWitness.sequentialSameCircuit.program
  realizes := by
    have h :
        BaseGateProgram.Realizes
          (BinaryLabelEncoding.prod w.endpointRunEncoding w.traceWitness.encoding)
          (BaseGateProgram.prodRight (m := w.endpointRunEncoding.width)
            w.traceWitness.sequentialSameCircuit.program)
          (fun x : EndpointRunState E schedule cert × TraceData E schedule =>
            (x.1, TraceCircuitWitness.sequentialStep E schedule x.2)) :=
      BaseGateProgram.Realizes.prodRight
        (left := w.endpointRunEncoding)
        (right := w.traceWitness.encoding)
        w.traceWitness.sequentialSameCircuit.realizes
    change
      BaseGateProgram.Realizes
        (BinaryLabelEncoding.prod w.endpointRunEncoding w.traceWitness.encoding)
        (BaseGateProgram.prodRight (m := w.endpointRunEncoding.width)
          w.traceWitness.sequentialSameCircuit.program)
        (fun x : EndpointRunState E schedule cert × TraceData E schedule =>
          (x.1, TraceCircuitWitness.sequentialStep E schedule x.2))
    exact h

/-- Folded composed scalar endpoint program. -/
def program (w : Witness E schedule cert) :
    BaseGateProgram w.encoding.width :=
  BaseGateProgram.append w.traceLiftedWitness.program w.targetProgram

/-- Same-Circuit witness for the composed scalar endpoint before rewriting the
trace fold to the schedule-wide trace endpoint. -/
def sequentialSameCircuit (w : Witness E schedule cert) :
    BaseGateSameCircuitWitness (State E schedule cert)
      (fullSequentialStep E schedule cert) where
  encoding := w.encoding
  program := w.program
  realizes := by
    have htrace :
        BaseGateProgram.Realizes w.encoding w.traceLiftedWitness.program
          (traceSequentialStep E schedule cert) := by
      simpa [encoding, State, traceLiftedWitness, traceSequentialStep] using
        w.traceLiftedWitness.realizes
    have htarget :
        BaseGateProgram.Realizes w.encoding w.targetProgram
          (targetStep E schedule cert) := by
      simpa [encoding] using w.targetRealizes
    have hfull :
        BaseGateProgram.Realizes w.encoding w.program
          (fun x : State E schedule cert =>
            targetStep E schedule cert
              (traceSequentialStep E schedule cert x)) := by
      simpa [program] using
        BaseGateProgram.Realizes.append
          (firstStep := traceSequentialStep E schedule cert)
          (secondStep := targetStep E schedule cert) htrace htarget
    change
      BaseGateProgram.Realizes w.encoding w.program
        (fun x : State E schedule cert =>
          targetStep E schedule cert
            (traceSequentialStep E schedule cert x))
    exact hfull

/-- Same-Circuit witness for the composed scalar endpoint. -/
def sameCircuit (w : Witness E schedule cert) :
    BaseGateSameCircuitWitness (State E schedule cert)
      (fullStep E schedule cert) :=
  w.sequentialSameCircuit.congrStep (by
    intro x
    change
      targetStep E schedule cert (traceSequentialStep E schedule cert x) =
        targetStep E schedule cert (traceStep E schedule cert x)
    cases x with
    | mk endpointRun trace =>
        simp only [traceSequentialStep, traceStep]
        rw [TraceCircuitWitness.sequentialStep_apply])

/-- The composed scalar endpoint circuit history bottoms out in base gates. -/
theorem structured (w : Witness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.sameCircuit

/-- Encoded-basis correctness for the composed scalar endpoint. -/
theorem apply_ket (w : Witness E schedule cert)
    (x : State E schedule cert) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (fullStep E schedule cert x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit x

/-- Clean encoded-basis correctness for a composed endpoint state whose run
output agrees with the public certified scalar output. -/
theorem apply_clean_ket (w : Witness E schedule cert)
    (s : EndpointRunState E schedule cert)
    (houtput : s.run.outputPoint = s.data.outputPoint) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (s, s.run.controlledTraceData)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ s with data := s.data.addIntoTarget }, s.run.updatedTraceData)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [fullStep_clean E schedule cert s houtput] using
    apply_ket (E := E) (schedule := schedule) (cert := cert) w
      (s, s.run.controlledTraceData)

/-- Clean encoded-basis correctness for a generic-domain input, using the
certified schedule run supplied by the scalar-action certificate. -/
theorem apply_clean_ket_with_certified_run (w : Witness E schedule cert)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    ∃ run : Run E schedule,
      run.startsAt = input.1.2 ∧
        (∀ i : Fin schedule.length,
          run.controls i = bitControl schedule input.1.1 i) ∧
        run.outputPoint = cert.output input.1.1 input.1.2 ∧
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              (({ data :=
                    ({ input := input, targetX := 0, targetY := 0, flag := false } :
                      Data E schedule cert)
                  run := run } : EndpointRunState E schedule cert),
                run.controlledTraceData)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              (({ data :=
                    ({ input := input
                       targetX := (cert.output input.1.1 input.1.2).x
                       targetY := (cert.output input.1.1 input.1.2).y
                       flag := false } : Data E schedule cert)
                  run := run } : EndpointRunState E schedule cert),
                run.updatedTraceData)) :
            StateVector (Qubits w.encoding.width)) := by
  rcases cert.exists_run input.1.1 input.1.2 input.2 with
    ⟨run, hstart, hcontrols, houtput⟩
  let initialData : Data E schedule cert :=
    { input := input, targetX := 0, targetY := 0, flag := false }
  let endpointRun : EndpointRunState E schedule cert :=
    { data := initialData, run := run }
  have hendpoint : endpointRun.run.outputPoint = endpointRun.data.outputPoint := by
    simpa [endpointRun, initialData, Data.outputPoint, Data.scalar,
      Data.startPoint] using houtput
  have happly :=
    apply_clean_ket (E := E) (schedule := schedule) (cert := cert) w
      endpointRun hendpoint
  refine ⟨run, hstart, hcontrols, houtput, ?_⟩
  simpa [endpointRun, initialData, Data.addIntoTarget, Data.outputPoint,
    Data.scalar, Data.startPoint] using happly

/-- Resource counters are projected from the same folded composed endpoint
circuit used for correctness. -/
theorem resources_eq (w : Witness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Circuit depth is projected from the same folded composed endpoint circuit. -/
theorem depth_eq (w : Witness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Query depth is projected from the same folded composed endpoint circuit. -/
theorem queryDepth_eq (w : Witness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

/-- Resource-correct witness for the composed scalar endpoint. -/
def resourceCorrectWitness (w : Witness E schedule cert) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ x : State E schedule cert,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
          ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (fullStep E schedule cert x)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.sameCircuit
  correctness := apply_ket w
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end Witness

end ComposedEndpoint

/-- Semantic update implemented by a gate-structured certified scalar witness. -/
abbrev encodedStep {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {schedule : Schedule E} {cert : CertifiedScalarAction E schedule} :
    Data E schedule cert -> Data E schedule cert :=
  Data.addIntoTarget

/-- Gate-structured encoded certified scalar-multiplication witness. -/
abbrev StructuredCircuitWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule) :=
  BaseGateSameCircuitWitness (Data E schedule cert)
    (encodedStep (E := E) (schedule := schedule) (cert := cert))

namespace StructuredCircuitWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E} {cert : CertifiedScalarAction E schedule}

/-- The structured scalar circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : StructuredCircuitWitness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w

/-- Encoded-basis correctness for all certified scalar endpoint labels. -/
theorem apply_ket (w : StructuredCircuitWitness E schedule cert)
    (x : Data E schedule cert) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addIntoTarget) :
        StateVector (Qubits w.encoding.width)) :=
  by
    simpa [encodedStep] using BaseGateSameCircuitWitness.apply_encoded_ket w x

/-- Clean public-form encoded-basis action for certified scalar multiplication. -/
theorem apply_clean_ket (w : StructuredCircuitWitness E schedule cert)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := input, targetX := 0, targetY := 0, flag := false } :
              Data E schedule cert)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := input
             targetX := (cert.output input.1.1 input.1.2).x
             targetY := (cert.output input.1.1 input.1.2).y
             flag := false } : Data E schedule cert)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [encodedStep, Data.addIntoTarget, Data.outputPoint, Data.scalar,
    Data.startPoint] using
    apply_ket (E := E) (schedule := schedule) (cert := cert) w
      ({ input := input, targetX := 0, targetY := 0, flag := false } :
        Data E schedule cert)

/-- The certified scalar action supplies the schedule run represented by a clean input. -/
theorem clean_input_has_run
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    ∃ run : Run E schedule,
      run.startsAt = input.1.2 ∧
        (∀ i : Fin schedule.length,
          run.controls i = bitControl schedule input.1.1 i) ∧
        run.outputPoint = cert.output input.1.1 input.1.2 :=
  cert.exists_run input.1.1 input.1.2 input.2

/-- Clean encoded-basis action together with the certified schedule run. -/
theorem apply_clean_ket_with_run
    (w : StructuredCircuitWitness E schedule cert)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := input, targetX := 0, targetY := 0, flag := false } :
              Data E schedule cert)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := input
             targetX := (cert.output input.1.1 input.1.2).x
             targetY := (cert.output input.1.1 input.1.2).y
             flag := false } : Data E schedule cert)) :
        StateVector (Qubits w.encoding.width)) ∧
    ∃ run : Run E schedule,
      run.startsAt = input.1.2 ∧
        (∀ i : Fin schedule.length,
          run.controls i = bitControl schedule input.1.1 i) ∧
        run.outputPoint = cert.output input.1.1 input.1.2 :=
  ⟨apply_clean_ket w input, clean_input_has_run (E := E) (schedule := schedule)
    (cert := cert) input⟩

/-- Resource counters are projected from the same structured scalar circuit. -/
theorem resources_eq (w : StructuredCircuitWitness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w).resources =
      (BaseGateSameCircuitWitness.profile w).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w

/-- Circuit depth is projected from the same structured scalar circuit. -/
theorem depth_eq (w : StructuredCircuitWitness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w).depth =
      (BaseGateSameCircuitWitness.profile w).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w

/-- Query depth is projected from the same structured scalar circuit. -/
theorem queryDepth_eq (w : StructuredCircuitWitness E schedule cert) :
    (BaseGateSameCircuitWitness.circuit w).queryDepth =
      (BaseGateSameCircuitWitness.profile w).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w

/-- Resource-correct witness for the encoded certified scalar endpoint. -/
def resourceCorrectWitness (w : StructuredCircuitWitness E schedule cert) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ x : Data E schedule cert,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w)
          ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode x.addIntoTarget) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w).resources =
          (BaseGateSameCircuitWitness.profile w).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w).depth =
          (BaseGateSameCircuitWitness.profile w).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w).queryDepth =
          (BaseGateSameCircuitWitness.profile w).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w
  correctness := apply_ket w
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end StructuredCircuitWitness

end

end CertifiedEndpoint
end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg
