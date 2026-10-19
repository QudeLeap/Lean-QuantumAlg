/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Sequence
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import Mathlib.Data.List.OfFn

/-!
# Reset all existing qubits through one actual result cell

The wire list contains each existing physical system once. Every measurement
writes the same finite two-valued cell, and the existing reset circuit reads
that cell to select its declared cyclic correction. Earlier values of this
scratch cell are overwritten; no quantum system or classical cell is allocated.

The complete Output lists the unchanged live context and reads the scratch
cell. An empty bank emits no events and preserves that cell's incoming value.
The independent budget reserves one measurement and one possible native X per
wire. Each actual path executes only its selected correction; zero uses no gate.
-/

namespace QuantumAlg.ZReset.Bank

open Execution

noncomputable section

variable {services : ClassicalOracleModel}

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}

private def resultAt (dimension : ℕ+) (equal : dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) : CWriteRef ctx (.finite dimension) :=
  equal.symm ▸ scratch

private lemma resultAt_key (dimension : ℕ+) (equal : dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) :
    (resultAt dimension equal scratch).key = scratch.key := by
  cases equal
  rfl

/-- Enumerate every physical qubit once, reusing the same writable result cell. -/
def readouts (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) : List (ZReadout ctx) :=
  List.ofFn (fun wire =>
    ⟨wire, resultAt (ctx.quantumLayout.wire wire).dimension (qubits wire) scratch⟩)

/-- Use the native identity or placed-X realization for each selected qubit. -/
def implementations (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (wire : Fin ctx.systemCount) :
    QuditShift.Realizations AlgorithmGate.model oracles ctx.quantumLayout wire :=
  QuditShift.qubitRealizations ctx.quantumLayout wire (qubits wire) oracles

/-- Reset the existing bank using only the actual measurement-and-correction sequence. -/
def code (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    (operations : ClassicalOpModel := .empty)
    (services : ClassicalOracleModel := .empty)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx
      allowAllocation :=
  sequence (allowAllocation := allowAllocation) (services := services)
    (implementations (oracles := oracles) qubits)
    (readouts qubits scratch) operations

/-- Retain every live key and expose the actual final contents of the shared result cell. -/
def output (scratch : CWriteRef ctx (.finite 2)) : Output ctx (.finite 2) :=
  Output.all ctx (.read (.storage scratch.toCStorageRef))

/-- The real reset syntax together with its complete live-resource manifest. -/
def run (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    (services : ClassicalOracleModel := .empty) :
    AlgorithmRun (.quantum AlgorithmGate.model oracles .empty services) ctx ctx (.finite 2) where
  code := code (services := services) (oracles := oracles) qubits scratch
  output := output scratch

/-- Each wire reserves one Z measurement and at most one selected native X. -/
def envelope (width : Nat) (operations : ClassicalOpModel := .empty)
    (services : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
  width • eventEnvelope 2
    (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate AlgorithmGate.Coordinate.singleQubit))

variable {operations : ClassicalOpModel}

/-- The actual readout count is the physical system count, including width zero. -/
lemma zResetBank_readouts_length (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) :
    (readouts qubits scratch).length = ctx.systemCount := by
  exact List.length_ofFn

/-- A positive-width bank reset contains a physical Z measurement on every
actual path; the zero-width reset makes no such claim. -/
lemma zResetBank_measured {allowAllocation : Bool} (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (operations : ClassicalOpModel)
    (positive : 0 < ctx.systemCount)
    (path : (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
        qubits scratch operations).Path) :
    ∃ dimension : ℕ+,
      Resource.Event.measurement
        (model := .quantum AlgorithmGate.model oracles operations services) dimension ∈
        (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
            qubits scratch operations).eventTrace
          path := by
  unfold code at path ⊢
  have nonempty : readouts qubits scratch ≠ [] := by
    intro empty
    have length := zResetBank_readouts_length qubits scratch
    rw [empty] at length
    simp only [List.length_nil] at length
    omega
  exact sequence_measured_of_nonempty (allowAllocation := allowAllocation)
    (implementations (oracles := oracles) qubits)
    (readouts qubits scratch) operations nonempty path

/-- Coverage is proved from the constructed list, rather than supplied by a reset caller. -/
lemma zResetBank_readouts_cover (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (wire : Fin ctx.systemCount) :
    wire ∈ (readouts qubits scratch).map ZReadout.wire := by
  unfold readouts
  rw [List.map_ofFn]
  exact List.mem_ofFn.mpr ⟨wire, rfl⟩

/-- Every actual measurement writes precisely the one shared scratch key. -/
lemma zResetBank_readouts_key (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (item : ZReadout ctx)
    (present : item ∈ readouts qubits scratch) : item.output.key = scratch.key := by
  obtain ⟨wire, rfl⟩ := List.mem_ofFn.mp present
  exact resultAt_key _ (qubits wire) scratch

/-- The dimension-indexed list envelope is exactly the independent width budget. -/
lemma zResetBank_envelope (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) :
    sequenceEnvelope (readouts qubits scratch)
      (fun _ => ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations
        services)
        (.gate AlgorithmGate.Coordinate.singleQubit)) =
        envelope (services := services) (oracles := oracles) ctx.systemCount operations := by
  unfold sequenceEnvelope readouts
  rw [List.map_ofFn]
  change (List.ofFn (fun wire : Fin ctx.systemCount =>
    eventEnvelope (ctx.quantumLayout.wire wire).dimension
      (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate AlgorithmGate.Coordinate.singleQubit)))).sum = _
  simp only [qubits, List.ofFn_const, List.sum_replicate, envelope]

/-- Both qubit correction alternatives fit the same single-X native allowance. -/
private lemma correction_le (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (wire : Fin ctx.systemCount)
    (amount : Fin (ctx.quantumLayout.wire wire).dimension) :
    ResourcePool.ofList
      ((implementations (oracles := oracles) qubits wire amount).circuit.eventTrace operations
        services) ≤
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate AlgorithmGate.Coordinate.singleQubit) := by
  change ResourcePool.ofList
    ((QuditShift.qubitShiftCircuit ctx.quantumLayout wire (qubits wire)
      oracles amount).eventTrace operations services)
      ≤ ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
          (.gate AlgorithmGate.Coordinate.singleQubit)
  rw [QuditShift.qubitShiftCircuit_events ctx.quantumLayout wire (qubits wire)
    oracles amount operations services]
  split <;> simp [ResourcePool.ofList, ResourcePool.singleton]

/-- Both selected correction circuits take at most one unit-duration stage. -/
private lemma correction_depth_le (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (wire : Fin ctx.systemCount)
    (amount : Fin (ctx.quantumLayout.wire wire).dimension) :
    DepthExpr.depthEval (fun _ => 1)
      ((implementations (oracles := oracles) qubits wire amount).circuit.eventDepth operations
        services) ≤
      1 := by
  change DepthExpr.depthEval (fun _ => 1)
    ((QuditShift.qubitShiftCircuit ctx.quantumLayout wire (qubits wire)
      oracles amount).eventDepth operations services) ≤ 1
  by_cases zero : amount = 0
  · simp only [QuditShift.qubitShiftCircuit, if_pos zero]
    exact Nat.zero_le 1
  · simp only [QuditShift.qubitShiftCircuit, if_neg zero]
    exact Nat.le_refl 1

/-- A selected qubit correction emits either zero or one native X event. -/
private lemma correction_length_le (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (wire : Fin ctx.systemCount)
    (amount : Fin (ctx.quantumLayout.wire wire).dimension) :
    ((implementations (oracles := oracles) qubits wire amount).circuit.eventTrace
      operations services).length ≤
      1 := by
  change ((QuditShift.qubitShiftCircuit ctx.quantumLayout wire (qubits wire)
    oracles amount).eventTrace operations services).length ≤ 1
  rw [QuditShift.qubitShiftCircuit_events ctx.quantumLayout wire (qubits wire)
    oracles amount operations services]
  split <;> simp

/-- Every actual path is bounded coordinatewise by the independently repeated envelope. -/
lemma zResetBank_resourcePool_le {allowAllocation : Bool} (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    (path : (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
        qubits scratch operations).Path) :
    (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles) qubits
        scratch operations).resourcePool path ≤
      envelope (services := services) (oracles := oracles) ctx.systemCount operations :=
  (zReset_sequence_resourcePool_le (allowAllocation := allowAllocation) (implementations (oracles :=
      oracles) qubits)
    (readouts qubits scratch) (fun _ => ResourcePool.singleton
      (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate AlgorithmGate.Coordinate.singleQubit))
    (fun item amount => correction_le (operations := operations) qubits item.wire amount)
    path).trans_eq (zResetBank_envelope qubits scratch)

/-- Each actual path contains one measurement and at most one native X per qubit. -/
lemma zResetBank_eventTrace_length_le {allowAllocation : Bool}
    (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    (path : (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
        qubits scratch operations).Path) :
    ((code (allowAllocation := allowAllocation) (services := services) (oracles := oracles) qubits
        scratch operations).eventTrace
      path).length ≤
      2 * ctx.systemCount := by
  have traceBound : ∀ readouts : List (ZReadout ctx),
      ∀ path : (sequence (allowAllocation := allowAllocation) (services := services)
          (implementations (oracles := oracles) qubits)
        readouts operations).Path,
        ((sequence (allowAllocation := allowAllocation) (services := services) (implementations
            (oracles := oracles) qubits) readouts
          operations).eventTrace
          path).length ≤ 2 * readouts.length := by
    intro readouts
    induction readouts with
    | nil => intro path; exact Nat.zero_le _
    | cons head tail ih =>
        intro path
        rw [zReset_sequence_eventTrace_length (allowAllocation := allowAllocation)]
        have correction := correction_length_le (services := services)
          (oracles := oracles) (operations := operations)
          qubits head.wire (-(readOutcome (allowAllocation := allowAllocation) (services :=
              services) (operations := operations)
            head.wire head.output
            (implementations (oracles := oracles) qubits head.wire) path.1))
        have rest := ih path.2
        simp only [List.length_cons]
        omega
  exact (traceBound (readouts qubits scratch) path).trans_eq
    (congrArg (2 * ·) (zResetBank_readouts_length qubits scratch))

/-- Serial unit duration is at most two native events per physical qubit. -/
lemma zResetBank_unitDepth_le {allowAllocation : Bool} (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    (path : (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
        qubits scratch operations).Path) :
    (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles) qubits
        scratch operations).depth (fun _ => 1)
      path ≤
      2 * ctx.systemCount := by
  have depthBound : ∀ readouts : List (ZReadout ctx),
      ∀ path : (sequence (allowAllocation := allowAllocation) (services := services)
          (implementations (oracles := oracles) qubits)
        readouts operations).Path,
        (sequence (allowAllocation := allowAllocation) (services := services) (implementations
            (oracles := oracles) qubits) readouts
          operations).depth
          (fun _ => 1) path ≤ 2 * readouts.length := by
    intro readouts
    induction readouts with
    | nil => intro path; exact Nat.zero_le _
    | cons head tail ih =>
        intro path
        rw [zReset_sequence_unitDepth (allowAllocation := allowAllocation)]
        have correction := correction_depth_le (services := services)
          (oracles := oracles) (operations := operations)
          qubits head.wire (-(readOutcome (allowAllocation := allowAllocation) (services :=
              services) (operations := operations)
            head.wire head.output
            (implementations (oracles := oracles) qubits head.wire) path.1))
        have rest := ih path.2
        simp only [List.length_cons]
        omega
  exact (depthBound (readouts qubits scratch) path).trans_eq
    (congrArg (2 * ·) (zResetBank_readouts_length qubits scratch))

/-- Resident space is exactly the original bank, scratch and earlier retained results. -/
lemma zResetBank_peakResidentSpace {allowAllocation : Bool}
    (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    (path : (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
        qubits scratch operations).Path) :
    (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles) qubits
        scratch operations).peakResidentSpace
      path =
      ctx.residentSpace :=
  zReset_sequence_peakResidentSpace (allowAllocation := allowAllocation) (operations := operations)
    (implementations (oracles := oracles) qubits)
    (readouts qubits scratch) path

/-- Auxiliary accounting preserves the actual original roles without adding a new bank. -/
lemma zResetBank_peakAuxiliarySpace {allowAllocation : Bool}
    (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    (path : (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
        qubits scratch operations).Path) :
    (code (allowAllocation := allowAllocation) (services := services) (oracles := oracles) qubits
        scratch operations).peakAuxiliarySpace
      path =
      ctx.auxiliarySpace :=
  zReset_sequence_peakAuxiliarySpace (allowAllocation := allowAllocation) (operations := operations)
    (implementations (oracles := oracles) qubits)
    (readouts qubits scratch) path

/-- The complete output manifest includes the bank and the actual shared scratch cell. -/
lemma zResetBank_output_listing (scratch : CWriteRef ctx (.finite 2)) :
    (output scratch).listing = ctx.keys := rfl

end

end QuantumAlg.ZReset.Bank
