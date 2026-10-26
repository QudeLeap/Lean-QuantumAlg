/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Resources.Native
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Resources.Placed
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Exceptional.Resources

/-!
# Native point resources with the original zero-width case retained

One enable source is still present at address width zero. Its actual
conjunction is a CNOT, while positive widths use the existing Toffoli
formula. These coordinate distinctions do not select a different program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open EncodedBit GateSpec

attribute [local irreducible] Circuit.depth UnitaryCircuit.evaluatedEventDepth

attribute [local irreducible] ResourcePool.scale Inversion.Seed.program Inversion.program
  Native.BorrowedControl.subtractSquareProgram Normal.program Normal.inverseProgram
  Arithmetic.Reflect.program Window.Enable.program Window.Enable.inverseProgram
  Control.prepareProgram Control.restoreProgram Offset.Placed.program
  Offset.Exceptional.Placed.program Arithmetic.Call.beforeReset Arithmetic.Call.tail

def controlToffoli (width : Nat) : Nat :=
  if width = 0 then 0 else Word.OneDirtyLayout.gateCount (width + 1)

def controlCnot (width : Nat) : Nat := if width = 0 then 1 else 0

def controlSingle (width : Nat) : Nat := 2 * (width + 1) + 1

def controlQuantumTime (width : Nat) : Nat :=
  controlSingle width + Word.OneDirtyLayout.gateCount (width + 1)

/-- The original zero-width selector pays its real three X gates and one CNOT. -/
lemma enable_native_counts (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (Window.Enable.program stream width bounded).eventCost = controlToffoli width ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (Window.Enable.program stream width bounded).eventCost = controlCnot width ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (Window.Enable.program stream width bounded).eventCost = controlSingle width := by
  by_cases zero : width = 0
  · subst width
    have actual := (Window.Enable.layout stream 0 bounded).patternGates_events .empty
      (fun _ => false)
    have masks : (Word.OneDirtyLayout.patternMaskIndices (fun _ : Fin 1 => false)).length = 1 :=
      by simp [Word.OneDirtyLayout.patternMaskIndices]
    rw [masks] at actual
    have events : (Window.Enable.gates stream 0 bounded).map (GateSpec.event .empty) =
        [.gate .singleQubit, .gate .singleQubit, .gate .cnot, .gate .singleQubit] := by
      change .gate .singleQubit ::
        ((Window.Enable.layout stream 0 bounded).patternGates (fun _ => false)).map
          (GateSpec.event .empty) = _
      rw [actual]
      rfl
    simp only [Window.Enable.program, programList_eventCost, events,
      ResourcePool.count_ofList, controlToffoli, controlCnot, controlSingle, if_true]
    simp
  · have actual := Window.Enable.program_native_counts stream width bounded (by omega)
    simpa only [controlToffoli, controlCnot, controlSingle, if_neg zero] using actual

/-- Division retains its extra copied control beside the same real zero-width enable CNOT. -/
lemma transfer_native_counts (kind : Arithmetic.Call.Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (Arithmetic.Call.transferProgram kind stream width bounded).eventCost =
        controlToffoli width ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (Arithmetic.Call.transferProgram kind stream width bounded).eventCost =
        controlCnot width + Arithmetic.Call.transferCnot kind ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (Arithmetic.Call.transferProgram kind stream width bounded).eventCost =
        controlSingle width := by
  have actual := enable_native_counts stream width bounded
  cases kind with
  | multiplication => simpa only [Arithmetic.Call.transferProgram,
      Arithmetic.Call.transferCnot, Nat.add_zero] using actual
  | division =>
      simp only [Window.Enable.program, programList_toffoli_count_eq_sum,
        programList_cnot_count_eq_sum, programList_x_count_eq_sum] at actual
      have paid := And.intro actual.1 (And.intro
        (congrArg (fun amount => 1 + amount) actual.2.1) actual.2.2)
      simpa only [Arithmetic.Call.transferProgram, Arithmetic.Call.transferCnot,
        Control.prepareProgram, programList_toffoli_count_eq_sum,
        programList_cnot_count_eq_sum, programList_x_count_eq_sum, Control.prepareGates,
        List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.map_reverse, List.sum_reverse, Control.copyGate,
        toffoliMultiplicity, cnotMultiplicity, xMultiplicity, Nat.zero_add, Nat.add_zero,
        Nat.add_comm] using paid

/-- Actual native Call Toffolis follow the same producer at every original address width. -/
lemma call_native_toffoli_count_le (kind : Arithmetic.Call.Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (Arithmetic.Call.nativePool kind stream width bounded outcome) ≤
        474737453 + 4 * controlToffoli width := by
  rw [Arithmetic.Call.native_count, Arithmetic.Save.program_toffoli_count,
    Arithmetic.Phase.program_toffoli_count,
    (transfer_native_counts kind stream width bounded).1, Arithmetic.Call.swap_gate_count]
  have resident := Inversion.program_toffoli_count_le
  simp only [reduceCtorEq, if_false]
  omega

lemma call_native_cnot_count_le (kind : Arithmetic.Call.Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (Arithmetic.Call.nativePool kind stream width bounded outcome) ≤
        301982217 + Arithmetic.Phase.selectedCount outcome +
          4 * (controlCnot width + Arithmetic.Call.transferCnot kind) := by
  rw [Arithmetic.Call.native_count, Arithmetic.Save.program_cnot_count,
    Arithmetic.Phase.program_cnot_count,
    (transfer_native_counts kind stream width bounded).2.1, Arithmetic.Call.swap_gate_count]
  have resident := Inversion.program_cnot_count_le
  simp only [if_true]
  omega

lemma call_native_singleQubit_count (kind : Arithmetic.Call.Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (Arithmetic.Call.nativePool kind stream width bounded outcome) =
        125477336 + 3 * Arithmetic.Phase.selectedCount outcome + 4 * controlSingle width := by
  rw [Arithmetic.Call.native_count, Arithmetic.Save.program_x_count,
    Arithmetic.Phase.program_x_count,
    (transfer_native_counts kind stream width bounded).2.2, Arithmetic.Call.swap_gate_count,
    Inversion.program_singleQubit_count]
  simp only [reduceCtorEq, if_false]
  omega

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Program.Parameters ctx)

/-- The entire outside native schedule, including the paid seed and its real adjoint. -/
lemma fixedQuantumTime_le :
    parameters.fixedQuantumTime ≤
      24227108 + 6 * controlQuantumTime (parameters.highRemaining + parameters.lowWidth) := by
  have seed := Inversion.Seed.program_quantumTime_le
  rw [fixedQuantumTime, AlgorithmGate.algorithmGate_emptyAdjoints_quantumTime,
    Window.Enable.program_quantumTime, Window.Enable.inverseProgram_quantumTime,
    Native.BorrowedControl.subtractSquareProgram_quantumTime,
    Normal.program_quantumTime, Normal.inverseProgram_quantumTime,
    Arithmetic.Reflect.program_quantumTime]
  unfold controlQuantumTime controlSingle
  omega

private lemma window_eventCost (stream : Fin 2) (body : Native.Circuit) :
    (Window.program stream body).eventCost = body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Window.program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private lemma suffix_eventCost (body : Native.Circuit) :
    (Window.suffixProgram body).eventCost = body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Window.suffixProgram_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Both actual selector directions surround the original paid offset body. -/
lemma selectedBody_count (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (body : Native.Circuit) (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus
        (Window.QueryInsertion.selectedBody stream width bounded body).eventCost =
      2 * ResourcePool.count focus (Window.Enable.program stream width bounded).eventCost +
        ResourcePool.count focus body.eventCost := by
  rw [Window.QueryInsertion.selectedBody, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ResourcePool.count_add,
    Window.Enable.inverseProgram_count, window_eventCost]
  omega

/-- The exceptional fourth query keeps its own actual arithmetic coordinates. -/
lemma queryBody_native_counts (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (occurrence : Fin 6) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (Window.QueryColumns.body stream width bounded occurrence).eventCost =
        2 * controlToffoli width + (if occurrence.val = 3 then 52348 else 52346) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (Window.QueryColumns.body stream width bounded occurrence).eventCost =
        2 * controlCnot width + (if occurrence.val = 3 then 508 else 510) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (Window.QueryColumns.body stream width bounded occurrence).eventCost =
        2 * controlSingle width + (if occurrence.val = 3 then 4 else 0) := by
  have controls := enable_native_counts stream width bounded
  unfold Window.QueryColumns.body
  by_cases exceptional : occurrence.val = 3
  · simp only [if_pos exceptional, selectedBody_count,
      Offset.Exceptional.Placed.program_toffoli_count,
      Offset.Exceptional.Placed.program_cnot_count, Offset.Exceptional.Placed.program_x_count,
      controls.1, controls.2.1, controls.2.2, true_and]
  · simp only [if_neg exceptional, selectedBody_count, Offset.Placed.program_toffoli_count,
      Offset.Placed.program_cnot_count, Offset.Placed.program_x_count,
      controls.1, controls.2.1, controls.2.2, true_and]

lemma queryBody_quantumTime (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (occurrence : Fin 6) :
    (Window.QueryColumns.body stream width bounded occurrence).evaluatedEventDepth
        Resource.Event.quantumDuration =
      2 * controlQuantumTime width + (if occurrence.val = 3 then 52860 else 52856) := by
  unfold Window.QueryColumns.body
  by_cases exceptional : occurrence.val = 3
  · simp only [if_pos exceptional, Window.QueryInsertion.selectedBody,
      UnitaryCircuit.evaluatedEventDepth_seq, Window.Enable.program_quantumTime,
      Window.Enable.inverseProgram_quantumTime, Window.program_quantumTime,
      Offset.Exceptional.Placed.program_quantumTime, controlQuantumTime, controlSingle]
    omega
  · simp only [if_neg exceptional, Window.QueryInsertion.selectedBody,
      UnitaryCircuit.evaluatedEventDepth_seq, Window.Enable.program_quantumTime,
      Window.Enable.inverseProgram_quantumTime, Window.program_quantumTime,
      Offset.Placed.program_quantumTime, controlQuantumTime, controlSingle]
    omega

/-- The literal supplied table reference and bank determine the original bare query. -/
def queryParameters (occurrence : Fin 6) :=
  Window.QueryDirect.parameters parameters.stream parameters.highRemaining parameters.lowWidth
    parameters.addressBound parameters.lowBound parameters.sameWires
    (parameters.arrays.column (Window.QueryColumns.column occurrence)).toCStorageRef
    parameters.output parameters.mask parameters.parity parameters.temporary

/-- Only the intervening native body is omitted from this actual pair of retained records. -/
def bareQueryPath (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    ((parameters.queryParameters occurrence).circuit (services := services)).Path :=
  Window.QueryInsertion.queryPath (parameters.queryParameters occurrence)
    (Execution.unitaryOfEqualWires _ _ parameters.sameWires
      (Window.QueryColumns.body parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound occurrence)) path

lemma query_gate_count (occurrence : Fin 6) (coordinate : AlgorithmGate.Coordinate)
    (path : (parameters.query (services := services) occurrence).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate coordinate) ((parameters.query occurrence).resourcePool path) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate coordinate) ((parameters.queryParameters occurrence).circuit.resourcePool
          (parameters.bareQueryPath occurrence path)) +
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
        (Window.QueryColumns.body parameters.stream
          (parameters.highRemaining + parameters.lowWidth)
          parameters.addressBound occurrence).eventCost := by
  have actual := Window.QueryInsertion.circuit_gate_count
    (parameters.queryParameters occurrence)
    (Execution.unitaryOfEqualWires _ _ parameters.sameWires
      (Window.QueryColumns.body parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound occurrence))
    coordinate path
  rw [Execution.unitaryOfEqualWires_cost] at actual
  exact actual

lemma query_quantumTime (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    (parameters.query occurrence).depth Resource.Event.quantumDuration path =
      (parameters.queryParameters occurrence).circuit.depth Resource.Event.quantumDuration
        (parameters.bareQueryPath occurrence path) +
      (Window.QueryColumns.body parameters.stream
        (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound occurrence).evaluatedEventDepth
          Resource.Event.quantumDuration := by
  have actual := Window.QueryInsertion.circuit_quantumTime
    (parameters.queryParameters occurrence)
    (Execution.unitaryOfEqualWires _ _ parameters.sameWires
      (Window.QueryColumns.body parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound occurrence)) path
  rw [UnitaryCircuit.evaluatedEventDepth, Execution.unitaryOfEqualWires_depth,
    ← UnitaryCircuit.evaluatedEventDepth] at actual
  exact actual

private lemma contextual_gate_count {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate coordinate) (body.eventCost BitWord.model services) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate) body.eventCost :=
  UnitaryCircuit.unitaryCircuit_event_count_classical_context body BitWord.model services
    (.gate coordinate)

/-- The same trace fixes every outside coordinate, including both seed directions. -/
lemma fixedNativePool_gate_count (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate coordinate) (parameters.fixedNativePool (services := services)) =
      2 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate) Inversion.Seed.program.eventCost +
      6 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate) (Window.Enable.program parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).eventCost +
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate) Native.BorrowedControl.subtractSquareProgram.eventCost +
      2 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate) Normal.program.eventCost +
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate) Arithmetic.Reflect.program.eventCost := by
  simp only [fixedNativePool, ResourcePool.count_add,
    contextual_gate_count, suffix_eventCost,
    Window.Enable.inverseProgram_count, Normal.inverseProgram_count,
    AlgorithmGate.algorithmGate_emptyAdjoints_eventCost]
  omega

private lemma seed_gate_count (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
      Inversion.Seed.program.eventCost =
        if AlgorithmGate.Coordinate.singleQubit = coordinate then
          (Word.constantOneIndices
            (MAU.Inversion.SharedEEA.ResidentSeed.constant
              (MAU.Inversion.SharedEEA.Scanned.ControlledResidentSeed.tail
                modulus))).length else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Inversion.Seed.program_eventTrace,
    ResourcePool.ofList_replicate, ResourcePool.count_scale, ResourcePool.count_singleton]
  cases coordinate <;> simp

lemma fixedNativePool_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) (parameters.fixedNativePool (services := services)) =
        22724636 + 6 * controlToffoli (parameters.highRemaining + parameters.lowWidth) := by
  rw [fixedNativePool_gate_count, seed_gate_count,
    (enable_native_counts parameters.stream _ parameters.addressBound).1,
    Native.BorrowedControl.subtractSquareProgram_toffoli_count,
    Normal.program_native_counts.1, Arithmetic.Reflect.program_toffoli_count]
  simp only [reduceCtorEq, if_false]
  omega

lemma fixedNativePool_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) (parameters.fixedNativePool (services := services)) =
        1242366 + 6 * controlCnot (parameters.highRemaining + parameters.lowWidth) := by
  rw [fixedNativePool_gate_count, seed_gate_count,
    (enable_native_counts parameters.stream _ parameters.addressBound).2.1,
    Native.BorrowedControl.subtractSquareProgram_cnot_count,
    Normal.program_native_counts.2.1, Arithmetic.Reflect.program_cnot_count]
  simp only [reduceCtorEq, if_false]
  omega

lemma fixedNativePool_singleQubit_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) (parameters.fixedNativePool (services := services)) ≤
        260112 + 6 * controlSingle (parameters.highRemaining + parameters.lowWidth) := by
  rw [fixedNativePool_gate_count, seed_gate_count,
    (enable_native_counts parameters.stream _ parameters.addressBound).2.2,
    Native.BorrowedControl.subtractSquareProgram_x_count,
    Normal.program_native_counts.2.2, Arithmetic.Reflect.program_x_count]
  have seed := Inversion.Seed.xCount_le
  simp only [if_true]
  omega

/-- Every original width, including zero, uses this same measured Call and physical reset. -/
lemma arithmetic_toffoli_count_le (kind : Arithmetic.Call.Kind)
    (path : (parameters.arithmetic (services := services) kind).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) ((parameters.arithmetic kind).resourcePool path) ≤
        474737453 + 4 * controlToffoli (parameters.highRemaining + parameters.lowWidth) := by
  have actual := Arithmetic.Call.circuit_gate_count_le parameters.sameWires parameters.output
    parameters.mask kind parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound .toffoli path
  have paid := call_native_toffoli_count_le kind parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask kind
      parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound path)
  simp only [Arithmetic.Call.nativePool, ResourcePool.count_add] at paid
  simp only [reduceCtorEq, if_false, Nat.add_zero] at actual
  exact actual.trans paid

lemma arithmetic_cnot_count_le (kind : Arithmetic.Call.Kind)
    (path : (parameters.arithmetic (services := services) kind).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) ((parameters.arithmetic kind).resourcePool path) ≤
        301982217 + Arithmetic.Phase.selectedCount
          (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask kind
            parameters.stream (parameters.highRemaining + parameters.lowWidth)
            parameters.addressBound path) +
          4 * (controlCnot (parameters.highRemaining + parameters.lowWidth) +
            Arithmetic.Call.transferCnot kind) := by
  have actual := Arithmetic.Call.circuit_gate_count_le parameters.sameWires parameters.output
    parameters.mask kind parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound .cnot path
  have paid := call_native_cnot_count_le kind parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask kind
      parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound path)
  simp only [Arithmetic.Call.nativePool, ResourcePool.count_add] at paid
  simp only [reduceCtorEq, if_false, Nat.add_zero] at actual
  exact actual.trans paid

lemma arithmetic_singleQubit_count_le (kind : Arithmetic.Call.Kind)
    (path : (parameters.arithmetic (services := services) kind).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) ((parameters.arithmetic kind).resourcePool path) ≤
        125477848 + 3 * Arithmetic.Phase.selectedCount
          (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask kind
            parameters.stream (parameters.highRemaining + parameters.lowWidth)
            parameters.addressBound path) +
          4 * controlSingle (parameters.highRemaining + parameters.lowWidth) := by
  have actual := Arithmetic.Call.circuit_gate_count_le parameters.sameWires parameters.output
    parameters.mask kind parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound .singleQubit path
  have paid := call_native_singleQubit_count kind parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask kind
      parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound path)
  simp only [Arithmetic.Call.nativePool, ResourcePool.count_add] at paid
  simp only [if_true] at actual
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.gate .singleQubit) ((parameters.arithmetic kind).resourcePool path) ≤ _ at actual
  omega

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
