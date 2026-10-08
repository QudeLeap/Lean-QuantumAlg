/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.StructuredCircuit
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Endpoint

/-!
# Encoded scalar-multiplication circuits

This module provides actual fixed-base scalar-multiplication circuits and
proof-only basis realizations.  The
interfaces.  The trace layer lifts schedule-indexed controlled-ECADD step
programs into one scalar trace circuit.  The endpoint layer keeps the public
certified scalar-action wrapper for a final coordinate-target program.  The
schedule follows the fixed-base controlled-addition route used in
elliptic-curve discrete-log resource estimates [RNSL17,
ECDLP.tex:589-597,650-699], with generic affine point-addition branches from
Proos--Zalka [PZ03, ecc.tex:448-462,525-551].  In both layers, the folded
`UnitaryCircuit` is the same object used for encoded-basis correctness and resource
accounting.
-/

section

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
  UnitaryCircuit.Realizes.stepList (stepUpdates E schedule)

private theorem stepList_eq_foldl
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (l : List (Fin schedule.length))
    (x : TraceData E schedule) :
    UnitaryCircuit.Realizes.stepList
        (l.map fun i => TraceData.controlledEquivAt E schedule i) x =
      l.foldl (fun y i => TraceData.controlledEquivAt E schedule i y) x := by
  induction l generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simpa [UnitaryCircuit.Realizes.stepList, List.foldl_cons] using
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
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical controlledWitness.encoding.width).toQuantum ->
      UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical encoding.width).toQuantum
  /-- The lifted lower-level program updates exactly the selected trace
  component. -/
  realizes :
    UnitaryCircuit.Realizes encoding
      (liftProgram controlledWitness.program)
      (TraceData.controlledEquivAt E schedule i)

namespace StepLift

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E}
variable {encoding : BinaryLabelEncoding (TraceData E schedule)}
variable {i : Fin schedule.length}

/-- Lower-level controlled-ECADD program consumed by the scalar trace lift. -/
def sourceProgram (w : StepLift E schedule encoding i) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical w.controlledWitness.encoding.width).toQuantum :=
  w.controlledWitness.program

/-- Lifted base-gate program acting on the full scalar trace register. -/
def program (w : StepLift E schedule encoding i) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical encoding.width).toQuantum :=
  w.liftProgram w.sourceProgram

/-- The lifted scalar trace program is definitionally derived from the
lower-level controlled-ECADD program. -/
theorem program_eq_lifted (w : StepLift E schedule encoding i) :
    w.program = w.liftProgram w.sourceProgram :=
  rfl

/-- Encoded-basis action of the lifted selected trace component. -/
theorem apply_ket (w : StepLift E schedule encoding i)
    (x : TraceData E schedule) :
    w.program.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical encoding.width).basisEquiv.symm (encoding.encode x))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical encoding.width).basisEquiv.symm
        (encoding.encode (TraceData.controlledEquivAt E schedule i x)))) :=
  w.realizes.apply_encoded_ket x

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
    List (UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical w.encoding.width).toQuantum) :=
  (stepIndices schedule).map fun i => (w.stepLift i).program

/-- Folded scalar trace program obtained by appending the lifted step programs. -/
def program (w : ScheduleCompositionWitness E schedule) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical w.encoding.width).toQuantum :=
  w.stepPrograms.foldr UnitaryCircuit.seq
    (UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical w.encoding.width).toQuantum)

/-- The lifted step programs realize the schedule-ordered trace updates. -/
theorem stepRealizes (w : ScheduleCompositionWitness E schedule) :
    List.Forall₂
      (fun program step => UnitaryCircuit.Realizes w.encoding program step)
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

/-- The folded actual circuit realizes the sequential scalar trace schedule. -/
theorem sequential_realizes (w : ScheduleCompositionWitness E schedule) :
    UnitaryCircuit.Realizes w.encoding w.program (sequentialStep E schedule) := by
  dsimp [program, stepPrograms, sequentialStep]
  exact UnitaryCircuit.Realizes.appendList w.encoding
    (QubitLayout.canonical _)
    w.stepPrograms (stepUpdates E schedule) w.stepRealizes

/-- The folded actual circuit realizes the schedule-wide controlled-ECADD
trace endpoint. -/
theorem realizes (w : ScheduleCompositionWitness E schedule) :
    UnitaryCircuit.Realizes w.encoding w.program
      (TraceData.controlledEquiv E schedule) :=
  w.sequential_realizes.congrStep (sequentialStep_apply E schedule)

/-- Encoded-basis correctness for the composed scalar trace circuit. -/
theorem apply_ket (w : ScheduleCompositionWitness E schedule)
    (x : TraceData E schedule) :
    w.program.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm (w.encoding.encode x))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
        (w.encoding.encode (TraceData.controlledEquiv E schedule x)))) :=
  w.realizes.apply_encoded_ket x

/-- Certified-run form of the composed trace action: every schedule component
is advanced by its controlled-ECADD endpoint. -/
theorem apply_certified_run (w : ScheduleCompositionWitness E schedule)
    (run : Run E schedule) :
    w.program.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
          (w.encoding.encode run.controlledTraceData))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
        (w.encoding.encode run.updatedTraceData))) := by
  have htrace :
      TraceData.controlledEquiv E schedule run.controlledTraceData =
        run.updatedTraceData := by
    funext i
    rfl
  simpa [htrace] using
    apply_ket (E := E) (schedule := schedule) w run.controlledTraceData

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

/-- Composed actual-circuit data for the certified scalar endpoint.  The
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
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (BinaryLabelEncoding.prod endpointRunEncoding traceWitness.encoding).width).toQuantum
  /-- Correctness of the final target-write program under the composed
  endpoint encoding. -/
  targetRealizes :
    UnitaryCircuit.Realizes
      (BinaryLabelEncoding.prod endpointRunEncoding traceWitness.encoding)
      targetProgram (targetStep E schedule cert)

namespace Witness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E} {cert : CertifiedScalarAction E schedule}

/-- Common encoding used by the composed scalar endpoint circuit. -/
def encoding (w : Witness E schedule cert) :
    BinaryLabelEncoding (State E schedule cert) :=
  BinaryLabelEncoding.prod w.endpointRunEncoding w.traceWitness.encoding

/-- Trace schedule circuit lifted over the endpoint/run half of the composed
state. -/
def traceLiftedProgram (w : Witness E schedule cert) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical w.encoding.width).toQuantum :=
  UnitaryCircuit.prodRight (m := w.endpointRunEncoding.width) w.traceWitness.program

/-- The lifted trace circuit realizes the sequential schedule update. -/
theorem traceLifted_realizes (w : Witness E schedule cert) :
    UnitaryCircuit.Realizes w.encoding w.traceLiftedProgram
      (traceSequentialStep E schedule cert) := by
  have h := UnitaryCircuit.Realizes.onBinarySuffix
    (left := w.endpointRunEncoding) (right := w.traceWitness.encoding)
    w.traceWitness.sequential_realizes
  have hstep := h.congrStep (second := traceSequentialStep E schedule cert) (by
    intro x
    rfl)
  simpa [encoding, traceLiftedProgram, UnitaryCircuit.prodRight,
    UnitaryCircuit.onCanonicalBinarySuffix] using hstep

/-- Folded composed scalar endpoint program. -/
def program (w : Witness E schedule cert) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical w.encoding.width).toQuantum :=
  UnitaryCircuit.seq w.traceLiftedProgram w.targetProgram

/-- The composed circuit realizes the endpoint before rewriting the trace fold
to the schedule-wide trace endpoint. -/
theorem sequential_realizes (w : Witness E schedule cert) :
    UnitaryCircuit.Realizes w.encoding w.program
      (fullSequentialStep E schedule cert) := by
    have htrace :
        UnitaryCircuit.Realizes w.encoding w.traceLiftedProgram
          (traceSequentialStep E schedule cert) := by
      exact w.traceLifted_realizes
    have htarget :
        UnitaryCircuit.Realizes w.encoding w.targetProgram
          (targetStep E schedule cert) := by
      simpa [encoding] using w.targetRealizes
    have hfull :
        UnitaryCircuit.Realizes w.encoding w.program
          (fun x : State E schedule cert =>
            targetStep E schedule cert
              (traceSequentialStep E schedule cert x)) := by
      simpa [program] using
        UnitaryCircuit.Realizes.seq
          (firstStep := traceSequentialStep E schedule cert)
          (secondStep := targetStep E schedule cert) htrace htarget
    change
      UnitaryCircuit.Realizes w.encoding w.program
        (fun x : State E schedule cert =>
          targetStep E schedule cert
            (traceSequentialStep E schedule cert x))
    exact hfull

/-- The composed actual circuit realizes the certified scalar endpoint. -/
theorem realizes (w : Witness E schedule cert) :
    UnitaryCircuit.Realizes w.encoding w.program (fullStep E schedule cert) :=
  w.sequential_realizes.congrStep (by
    intro x
    change
      targetStep E schedule cert (traceSequentialStep E schedule cert x) =
        targetStep E schedule cert (traceStep E schedule cert x)
    cases x with
    | mk endpointRun trace =>
        simp only [traceSequentialStep, traceStep]
        rw [TraceCircuitWitness.sequentialStep_apply])

/-- Encoded-basis correctness for the composed scalar endpoint. -/
theorem apply_ket (w : Witness E schedule cert)
    (x : State E schedule cert) :
    w.program.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm (w.encoding.encode x))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
        (w.encoding.encode (fullStep E schedule cert x)))) :=
  w.realizes.apply_encoded_ket x

/-- Clean encoded-basis correctness for a composed endpoint state whose run
output agrees with the public certified scalar output. -/
theorem apply_clean_ket (w : Witness E schedule cert)
    (s : EndpointRunState E schedule cert)
    (houtput : s.run.outputPoint = s.data.outputPoint) :
    w.program.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
          (w.encoding.encode (s, s.run.controlledTraceData)))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
        (w.encoding.encode
          ({ s with data := s.data.addIntoTarget }, s.run.updatedTraceData)))) := by
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
        w.program.applyNormalized
          (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
            (w.encoding.encode
              (({ data :=
                    ({ input := input, targetX := 0, targetY := 0, flag := false } :
                      Data E schedule cert)
                  run := run } : EndpointRunState E schedule cert),
                run.controlledTraceData)))) =
          (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
            (w.encoding.encode
              (({ data :=
                    ({ input := input
                       targetX := (cert.output input.1.1 input.1.2).x
                       targetY := (cert.output input.1.1 input.1.2).y
                       flag := false } : Data E schedule cert)
                  run := run } : EndpointRunState E schedule cert),
                run.updatedTraceData)))) := by
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

end Witness

end ComposedEndpoint

/-- Semantic update implemented by a gate-structured certified scalar witness. -/
abbrev encodedStep {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {schedule : Schedule E} {cert : CertifiedScalarAction E schedule} :
    Data E schedule cert -> Data E schedule cert :=
  Data.addIntoTarget

/-- Domain-specific certified scalar witness tied to one actual circuit and
its public endpoint. -/
structure StructuredCircuitWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule) where
  /-- Faithful encoding of certified scalar endpoint labels. -/
  encoding : BinaryLabelEncoding (Data E schedule cert)
  /-- Actual certified scalar circuit. -/
  circuit : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum
  /-- Direct realization of the certified scalar endpoint. -/
  realizes : UnitaryCircuit.Realizes encoding circuit
    (encodedStep (E := E) (schedule := schedule) (cert := cert))

namespace StructuredCircuitWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E} {cert : CertifiedScalarAction E schedule}

/-- Encoded-basis correctness for all certified scalar endpoint labels. -/
theorem apply_ket (w : StructuredCircuitWitness E schedule cert)
    (x : Data E schedule cert) :
    w.circuit.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm (w.encoding.encode x))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
        (w.encoding.encode x.addIntoTarget))) :=
  by
    simpa [encodedStep] using w.realizes.apply_encoded_ket x

/-- Clean public-form encoded-basis action for certified scalar multiplication. -/
theorem apply_clean_ket (w : StructuredCircuitWitness E schedule cert)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    w.circuit.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
          (w.encoding.encode
            ({ input := input, targetX := 0, targetY := 0, flag := false } :
              Data E schedule cert)))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
        (w.encoding.encode
          ({ input := input
             targetX := (cert.output input.1.1 input.1.2).x
             targetY := (cert.output input.1.1 input.1.2).y
             flag := false } : Data E schedule cert)))) := by
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
    w.circuit.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
          (w.encoding.encode
            ({ input := input, targetX := 0, targetY := 0, flag := false } :
              Data E schedule cert)))) =
      (NormalizedVector.ket
          ((QubitLayout.canonical w.encoding.width).basisEquiv.symm
        (w.encoding.encode
          ({ input := input
             targetX := (cert.output input.1.1 input.1.2).x
             targetY := (cert.output input.1.1 input.1.2).y
             flag := false } : Data E schedule cert)))) ∧
    ∃ run : Run E schedule,
      run.startsAt = input.1.2 ∧
        (∀ i : Fin schedule.length,
          run.controls i = bitControl schedule input.1.1 i) ∧
        run.outputPoint = cert.output input.1.1 input.1.2 :=
  ⟨apply_clean_ket w input, clean_input_has_run (E := E) (schedule := schedule)
    (cert := cert) input⟩

end StructuredCircuitWitness

end

end CertifiedEndpoint
end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
