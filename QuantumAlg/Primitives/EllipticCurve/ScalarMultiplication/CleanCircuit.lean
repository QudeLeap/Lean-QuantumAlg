/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.StructuredCircuit

/-!
# Clean scalar-multiplication circuits

The structured scalar endpoint first evaluates the controlled-ECADD schedule
and then writes its certified output into the public target registers.  This
module appends the adjoint of that exact schedule circuit after the target
write.  The resulting actual circuit therefore restores the
complete trace register while retaining the public target update.

This is the compute--copy--uncompute seam consumed by the P-256 DLP oracle
compiler.  Cost and symbolic depth are projections of the one stored circuit;
the interface accepts no independent accounting data.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ScalarMultiplication
namespace CertifiedEndpoint
namespace ComposedEndpoint

variable {p : Nat}

noncomputable section

namespace Witness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E} {cert : CertifiedScalarAction E schedule}

/-- The lifted forward trace circuit realizes the schedule-wide
controlled-ECADD equivalence. -/
theorem traceForward_realizes (w : Witness E schedule cert) :
    UnitaryCircuit.Realizes w.encoding w.traceLiftedProgram
      (traceStep E schedule cert) :=
  w.traceLifted_realizes.congrStep (by
    intro x
    rcases x with ⟨endpointRun, trace⟩
    simp only [traceSequentialStep, traceStep]
    rw [TraceCircuitWitness.sequentialStep_apply])

/-- Semantic inverse of the forward trace update. -/
def traceBackwardStep
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert → State E schedule cert :=
  fun x =>
    (x.1, (TraceData.controlledEquiv E schedule).symm x.2)

/-- The backward trace circuit is the adjoint of the actual forward circuit. -/
def traceBackwardCircuit (w : Witness E schedule cert) :
    UnitaryCircuit (Qubits w.encoding.width) :=
  w.traceLiftedProgram.dagger

/-- The adjoint trace circuit realizes the semantic inverse. -/
theorem traceBackward_realizes (w : Witness E schedule cert) :
    UnitaryCircuit.Realizes w.encoding w.traceBackwardCircuit
      (traceBackwardStep schedule cert) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse w.traceForward_realizes (by
    intro x
    rcases x with ⟨endpointRun, trace⟩
    simp [traceStep, traceBackwardStep])

/-- Compute the scalar trace, write the certified target, and uncompute the
same trace. -/
def cleanStep
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert → State E schedule cert :=
  fun x =>
    traceBackwardStep schedule cert (fullStep E schedule cert x)

/-- Actual compute--copy--uncompute circuit. -/
def cleanCircuit (w : Witness E schedule cert) :
    UnitaryCircuit (Qubits w.encoding.width) :=
  UnitaryCircuit.seq w.program w.traceBackwardCircuit

/-- The actual clean circuit realizes the compute--copy--uncompute action. -/
theorem clean_realizes (w : Witness E schedule cert) :
    UnitaryCircuit.Realizes w.encoding w.cleanCircuit (cleanStep schedule cert) := by
  have h := UnitaryCircuit.Realizes.seq w.realizes w.traceBackward_realizes
  exact h.congrStep (by intro x; rfl)

/-- Compute--copy--uncompute restores the complete trace label for every
input, while retaining the certified target-coordinate update. -/
@[simp] theorem cleanStep_restores_trace
    (endpointRun : EndpointRunState E schedule cert)
    (trace : TraceData E schedule) :
    (cleanStep schedule cert (endpointRun, trace)).2 = trace := by
  simp [cleanStep, fullStep, targetStep, traceStep, traceBackwardStep]

/-- When the supplied certified run computes the endpoint's advertised scalar
action, the clean circuit retains exactly that public target update. -/
theorem cleanStep_apply_of_output
    (endpointRun : EndpointRunState E schedule cert)
    (trace : TraceData E schedule)
    (houtput : endpointRun.run.outputPoint = endpointRun.data.outputPoint) :
    cleanStep schedule cert (endpointRun, trace) =
      ({ endpointRun with data := endpointRun.data.addIntoTarget }, trace) := by
  simp only [cleanStep, fullStep, Function.comp_apply, targetStep, traceStep,
    traceBackwardStep, Equiv.symm_apply_apply]
  rw [houtput]
  rfl

/-- Encoded-basis correctness and trace restoration for the exact circuit used
by every resource projection. -/
theorem cleanCircuit_apply_ket (w : Witness E schedule cert)
    (endpointRun : EndpointRunState E schedule cert)
    (trace : TraceData E schedule)
    (houtput : endpointRun.run.outputPoint = endpointRun.data.outputPoint) :
    w.cleanCircuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (endpointRun, trace))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ endpointRun with data := endpointRun.data.addIntoTarget }, trace)) := by
  have happly := w.clean_realizes.apply_encoded_ket (endpointRun, trace)
  rw [cleanStep_apply_of_output endpointRun trace houtput] at happly
  exact happly

/-- Ordered strict events of the exact clean scalar-multiplication circuit. -/
def cleanEventTrace (w : Witness E schedule cert) :
    List (Resource.Event .quantum) :=
  w.cleanCircuit.eventTrace

/-- Strict event pool of the exact clean scalar-multiplication circuit. -/
def cleanEventCost (w : Witness E schedule cert) : ResourcePool .quantum :=
  w.cleanCircuit.eventCost

/-- Strict symbolic event critical path of the exact clean circuit. -/
def cleanEventDepth (w : Witness E schedule cert) :
    DepthExpr (Resource.Event .quantum) :=
  w.cleanCircuit.eventDepth

/-- Literal depth of one strict event coordinate in the exact clean circuit. -/
def cleanEventQueryDepth (w : Witness E schedule cert)
    (event : Resource.Event .quantum) : Nat :=
  w.cleanCircuit.eventQueryDepth event

/-- Exact multiplicity of one gate coordinate in the clean event pool. -/
def cleanEventGateCount (w : Witness E schedule cert)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) w.cleanCircuit.eventCost



/-- Linearizing clean-circuit strict event depth recovers the exact event
pool. -/
theorem cleanResourcesFromEventDepth_eq_eventCost
    (w : Witness E schedule cert) :
    w.cleanCircuit.resourcesFromEventDepth = w.cleanCircuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.cleanCircuit

/-- Semantic inverse of the clean target update.  It subtracts the run output
that the forward clean circuit added and leaves the restored trace untouched. -/
def cleanUndoStep
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    State E schedule cert → State E schedule cert :=
  fun x =>
    ({ x.1 with
        data :=
          { x.1.data with
            targetX := x.1.data.targetX - x.1.run.outputPoint.x
            targetY := x.1.data.targetY - x.1.run.outputPoint.y } },
      x.2)

@[simp] theorem cleanStep_cleanUndoStep
    (x : State E schedule cert) :
    cleanStep schedule cert (cleanUndoStep schedule cert x) = x := by
  rcases x with ⟨endpointRun, trace⟩
  cases endpointRun with
  | mk data run =>
      cases data
      simp [cleanStep, cleanUndoStep, fullStep, targetStep, traceStep,
        traceBackwardStep]

@[simp] theorem cleanUndoStep_cleanStep
    (x : State E schedule cert) :
    cleanUndoStep schedule cert (cleanStep schedule cert x) = x := by
  rcases x with ⟨endpointRun, trace⟩
  cases endpointRun with
  | mk data run =>
      cases data
      simp [cleanStep, cleanUndoStep, fullStep, targetStep, traceStep,
        traceBackwardStep]

/-- The inverse clean scalar circuit is the adjoint of the exact forward
circuit; no caller-supplied undo program is accepted. -/
def cleanInverseCircuit (w : Witness E schedule cert) :
    UnitaryCircuit (Qubits w.encoding.width) :=
  w.cleanCircuit.dagger

/-- The adjoint clean circuit realizes the semantic undo action. -/
theorem cleanInverse_realizes (w : Witness E schedule cert) :
    UnitaryCircuit.Realizes w.encoding w.cleanInverseCircuit
      (cleanUndoStep schedule cert) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse w.clean_realizes
    cleanStep_cleanUndoStep

end Witness

/-! ## Two-scalar compute--combine--uncompute compiler -/

/-- State acted on by a two-scalar oracle compiler: two private scalar
workspaces and one public workspace. -/
abbrev TwoScalarState
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {leftSchedule rightSchedule : Schedule E}
    {leftCert : CertifiedScalarAction E leftSchedule}
    {rightCert : CertifiedScalarAction E rightSchedule}
    (Workspace : Type) :=
  (State E leftSchedule leftCert × State E rightSchedule rightCert) × Workspace

/-- Compiler inputs for a clean two-scalar oracle.  The only executable data
are three sealed circuit witnesses: the two scalar schedules and the workspace
combiner.  No resource, depth, unitary, or numerical ledger is accepted. -/
structure TwoScalarCompiler
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {leftSchedule rightSchedule : Schedule E}
    {leftCert : CertifiedScalarAction E leftSchedule}
    {rightCert : CertifiedScalarAction E rightSchedule}
    (Workspace : Type) where
  /-- Clean circuit for the first fixed-base scalar multiplication. -/
  left : Witness E leftSchedule leftCert
  /-- Clean circuit for the second fixed-base scalar multiplication. -/
  right : Witness E rightSchedule rightCert
  /-- Binary encoding of the public group workspace. -/
  workspaceEncoding : BinaryLabelEncoding Workspace
  /-- Workspace update computed from the two materialized scalar results. -/
  workspaceUpdate :
    State E leftSchedule leftCert →
      State E rightSchedule rightCert → Workspace → Workspace
  /-- Sealed circuit that copies the two computed results into the public
  workspace while preserving both source workspaces. -/
  combineProgram :
    UnitaryCircuit (Qubits
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod
          left.encoding right.encoding)
        workspaceEncoding).width)
  /-- Basis correctness of the combine circuit on the exact common encoding. -/
  combineRealizes :
    UnitaryCircuit.Realizes
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod
          left.encoding right.encoding)
        workspaceEncoding)
      combineProgram
      (fun x => (x.1, workspaceUpdate x.1.1 x.1.2 x.2))

namespace TwoScalarCompiler

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {leftSchedule rightSchedule : Schedule E}
variable {leftCert : CertifiedScalarAction E leftSchedule}
variable {rightCert : CertifiedScalarAction E rightSchedule}
variable {Workspace : Type}

local notation "Compiler" =>
  TwoScalarCompiler (p := p) (E := E)
    (leftSchedule := leftSchedule) (rightSchedule := rightSchedule)
    (leftCert := leftCert) (rightCert := rightCert) Workspace

local notation "CompilerState" =>
  TwoScalarState (p := p) (E := E)
    (leftSchedule := leftSchedule) (rightSchedule := rightSchedule)
    (leftCert := leftCert) (rightCert := rightCert) Workspace

/-- Common encoding for both scalar workspaces and the public workspace. -/
def encoding (compiler : Compiler) : BinaryLabelEncoding CompilerState :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod
      compiler.left.encoding compiler.right.encoding)
    compiler.workspaceEncoding

/-- Lift the first clean scalar circuit over the second source and workspace. -/
def leftComputeProgram (compiler : Compiler) :
    UnitaryCircuit (Qubits compiler.encoding.width) :=
  UnitaryCircuit.prodLeft (n := compiler.workspaceEncoding.width)
    (UnitaryCircuit.prodLeft (n := compiler.right.encoding.width)
      compiler.left.cleanCircuit)

/-- The lifted first scalar circuit realizes its workspace update. -/
theorem leftCompute_realizes (compiler : Compiler) :
    UnitaryCircuit.Realizes compiler.encoding compiler.leftComputeProgram
      (fun x => ((Witness.cleanStep leftSchedule leftCert x.1.1, x.1.2),
        x.2)) := by
  have hpair := UnitaryCircuit.Realizes.prodLeft
    (right := compiler.right.encoding) compiler.left.clean_realizes
  have hfull := UnitaryCircuit.Realizes.prodLeft
    (right := compiler.workspaceEncoding) hpair
  simpa [encoding, leftComputeProgram] using hfull

/-- Lift the second clean scalar circuit over the first source and workspace. -/
def rightComputeProgram (compiler : Compiler) :
    UnitaryCircuit (Qubits compiler.encoding.width) :=
  UnitaryCircuit.prodLeft (n := compiler.workspaceEncoding.width)
    (UnitaryCircuit.prodRight (m := compiler.left.encoding.width)
      compiler.right.cleanCircuit)

/-- The lifted second scalar circuit realizes its workspace update. -/
theorem rightCompute_realizes (compiler : Compiler) :
    UnitaryCircuit.Realizes compiler.encoding compiler.rightComputeProgram
      (fun x => ((x.1.1,
        Witness.cleanStep rightSchedule rightCert x.1.2), x.2)) := by
  have hpair := UnitaryCircuit.Realizes.prodRight
    (left := compiler.left.encoding) compiler.right.clean_realizes
  have hfull := UnitaryCircuit.Realizes.prodLeft
    (right := compiler.workspaceEncoding) hpair
  simpa [encoding, rightComputeProgram] using hfull

/-- Lift the inverse second scalar circuit over the first source and workspace. -/
def rightUndoProgram (compiler : Compiler) :
    UnitaryCircuit (Qubits compiler.encoding.width) :=
  UnitaryCircuit.prodLeft (n := compiler.workspaceEncoding.width)
    (UnitaryCircuit.prodRight (m := compiler.left.encoding.width)
      compiler.right.cleanInverseCircuit)

/-- The lifted inverse second circuit realizes its undo update. -/
theorem rightUndo_realizes (compiler : Compiler) :
    UnitaryCircuit.Realizes compiler.encoding compiler.rightUndoProgram
      (fun x => ((x.1.1,
        Witness.cleanUndoStep rightSchedule rightCert x.1.2), x.2)) := by
  have hpair := UnitaryCircuit.Realizes.prodRight
    (left := compiler.left.encoding) compiler.right.cleanInverse_realizes
  have hfull := UnitaryCircuit.Realizes.prodLeft
    (right := compiler.workspaceEncoding) hpair
  simpa [encoding, rightUndoProgram] using hfull

/-- Lift the inverse first scalar circuit over the second source and workspace. -/
def leftUndoProgram (compiler : Compiler) :
    UnitaryCircuit (Qubits compiler.encoding.width) :=
  UnitaryCircuit.prodLeft (n := compiler.workspaceEncoding.width)
    (UnitaryCircuit.prodLeft (n := compiler.right.encoding.width)
      compiler.left.cleanInverseCircuit)

/-- The lifted inverse first circuit realizes its undo update. -/
theorem leftUndo_realizes (compiler : Compiler) :
    UnitaryCircuit.Realizes compiler.encoding compiler.leftUndoProgram
      (fun x => ((Witness.cleanUndoStep leftSchedule leftCert x.1.1,
        x.1.2), x.2)) := by
  have hpair := UnitaryCircuit.Realizes.prodLeft
    (right := compiler.right.encoding) compiler.left.cleanInverse_realizes
  have hfull := UnitaryCircuit.Realizes.prodLeft
    (right := compiler.workspaceEncoding) hpair
  simpa [encoding, leftUndoProgram] using hfull

/-- Fixed five-stage execution order of the clean two-scalar compiler. -/
def twoScalarPrograms (compiler : Compiler) :
    List (UnitaryCircuit (Qubits compiler.encoding.width)) :=
  [compiler.leftComputeProgram,
    compiler.rightComputeProgram,
    compiler.combineProgram,
    compiler.rightUndoProgram,
    compiler.leftUndoProgram]

/-- Semantic steps corresponding to the exact five stored programs. -/
def twoScalarSteps (compiler : Compiler) : List (CompilerState → CompilerState) :=
  [fun x => ((Witness.cleanStep leftSchedule leftCert x.1.1, x.1.2), x.2),
    fun x => ((x.1.1, Witness.cleanStep rightSchedule rightCert x.1.2), x.2),
    fun x => (x.1, compiler.workspaceUpdate x.1.1 x.1.2 x.2),
    fun x => ((x.1.1, Witness.cleanUndoStep rightSchedule rightCert x.1.2), x.2),
    fun x => ((Witness.cleanUndoStep leftSchedule leftCert x.1.1, x.1.2), x.2)]

/-- Folded semantic action of the two-scalar compiler. -/
def twoScalarFullStep (compiler : Compiler) : CompilerState → CompilerState :=
  UnitaryCircuit.Realizes.stepList compiler.twoScalarSteps

/-- Each program realizes the corresponding semantic step on the common
encoding. -/
theorem twoScalarPrograms_realize (compiler : Compiler) :
    List.Forall₂
      (fun program step => UnitaryCircuit.Realizes compiler.encoding program step)
      compiler.twoScalarPrograms compiler.twoScalarSteps := by
  constructor
  · exact compiler.leftCompute_realizes
  · constructor
    · exact compiler.rightCompute_realizes
    · constructor
      · exact compiler.combineRealizes
      · constructor
        · exact compiler.rightUndo_realizes
        · constructor
          · exact compiler.leftUndo_realizes
          · constructor

/-- One actual circuit implementing compute-left, compute-right, combine,
uncompute-right, and uncompute-left in that order. -/
def twoScalarCircuit (compiler : Compiler) :
    UnitaryCircuit (Qubits compiler.encoding.width) :=
  compiler.twoScalarPrograms.foldr UnitaryCircuit.seq
    (UnitaryCircuit.identity (Qubits compiler.encoding.width) [] (by simp))

/-- Ordered strict events of the exact five-stage two-scalar circuit. -/
def twoScalarEventTrace (compiler : Compiler) :
    List (Resource.Event .quantum) :=
  compiler.twoScalarCircuit.eventTrace

/-- Strict event pool of the exact five-stage two-scalar circuit. -/
def twoScalarEventCost (compiler : Compiler) : ResourcePool .quantum :=
  compiler.twoScalarCircuit.eventCost

/-- Strict symbolic event critical path of the five-stage circuit. -/
def twoScalarEventDepth (compiler : Compiler) :
    DepthExpr (Resource.Event .quantum) :=
  compiler.twoScalarCircuit.eventDepth

/-- Literal depth of one strict event coordinate in the five-stage circuit. -/
def twoScalarEventQueryDepth (compiler : Compiler)
    (event : Resource.Event .quantum) : Nat :=
  compiler.twoScalarCircuit.eventQueryDepth event

/-- Exact multiplicity of one gate coordinate in the five-stage event pool. -/
def twoScalarEventGateCount (compiler : Compiler)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) compiler.twoScalarCircuit.eventCost

/-- The actual five-stage circuit realizes its folded semantic action. -/
theorem twoScalar_realizes (compiler : Compiler) :
    UnitaryCircuit.Realizes compiler.encoding compiler.twoScalarCircuit
      compiler.twoScalarFullStep := by
  exact UnitaryCircuit.Realizes.appendList compiler.encoding
    compiler.twoScalarPrograms compiler.twoScalarSteps
    compiler.twoScalarPrograms_realize

/-- Both scalar source workspaces, including every trace register, are restored
at the full compiler boundary. -/
theorem twoScalarFullStep_restores_sources
    (compiler : Compiler) (x : CompilerState) :
    (compiler.twoScalarFullStep x).1 = x.1 := by
  rcases x with ⟨⟨leftState, rightState⟩, workspace⟩
  simp [twoScalarFullStep, twoScalarSteps, UnitaryCircuit.Realizes.stepList]



/-- Linearizing the two-scalar circuit's strict event depth recovers its exact
event pool. -/
theorem twoScalarResourcesFromEventDepth_eq_eventCost
    (compiler : Compiler) :
    compiler.twoScalarCircuit.resourcesFromEventDepth =
      compiler.twoScalarCircuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost compiler.twoScalarCircuit

end TwoScalarCompiler

end

end ComposedEndpoint
end CertifiedEndpoint
end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
