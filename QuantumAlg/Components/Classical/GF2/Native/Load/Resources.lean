/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Load
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Native resource allowances for the actual GF(2) matrix loader

The original clear and vector-write events remain on each row. Its decoder
adds one shift and at most one increment per bit. The one-word temporary
scope is reused across rows, independently of the matrix's current values.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- Independent original-row allowance, including its explicit clear and matrix write. -/
def rowEnvelope (kind : ProblemKind) (rowCount width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor width)) +
    (TerminalDecode.envelope width +
      ResourcePool.singleton (.classicalOperation (.vector .write rowCount width)))

/-- The ordered clear, decoder and write retain their original event coordinates. -/
theorem gf2RowBody_pool_le (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (path : (rowBody input row matrix loader).Path) :
    (rowBody input row matrix loader).resourcePool path ≤ rowEnvelope kind rowCount width := by
  change ResourcePool.ofList
    ([.classicalOperation (.wordBinary .bitXor width)] ++
      ((TerminalDecode.into .bigEndian input loader).eventTrace path.2.1 ++
        [.classicalOperation (.vector .write rowCount width)])) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (TerminalDecode.terminalDecode_intoFromBitRefs_pool_le .bigEndian
      (fun index => .bitsGet input index) loader path.2.1) le_rfl)

/-- The original row's duration allowance charges both fixed instructions and every decoder bit. -/
def rowDepthLimit (rowCount width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.wordBinary .bitXor width)) +
    (width * (duration (TerminalDecode.shiftEvent width) +
      duration (TerminalDecode.incrementEvent width)) +
      duration (.classicalOperation (.vector .write rowCount width)))

/-- Arbitrary durations respect the original three-stage dependency order. -/
theorem gf2RowBody_depth_le (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (rowBody input row matrix loader).Path) :
    (rowBody input row matrix loader).depth duration path ≤
      rowDepthLimit rowCount width duration := by
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (TerminalDecode.terminalDecode_intoFromBitRefs_depth_le .bigEndian
      (fun index => .bitsGet input index) loader duration path.2.1) _) _

private theorem decoder_bit_duration (input : CInputRef ctx .bit)
    (loader : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (TerminalDecode.bitRefRoutine input loader).Path) :
    (TerminalDecode.bitRefRoutine input loader).depth duration path =
      (((TerminalDecode.bitRefRoutine input loader).eventTrace path).map duration).sum := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit
      · change duration (TerminalDecode.shiftEvent width) + 0 =
          ([TerminalDecode.shiftEvent width].map duration).sum
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      · change duration (TerminalDecode.shiftEvent width) +
          duration (TerminalDecode.incrementEvent width) =
            ([TerminalDecode.shiftEvent width,
              TerminalDecode.incrementEvent width].map duration).sum
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

private theorem decoder_duration (loader : CWriteRef ctx (.unsignedWord width))
    (inputs : List (CInputRef ctx .bit)) (duration : Resource.Event kind → Nat)
    (path : (TerminalDecode.foldBitRefs loader inputs).Path) :
    (TerminalDecode.foldBitRefs loader inputs).depth duration path =
      (((TerminalDecode.foldBitRefs loader inputs).eventTrace path).map duration).sum := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      change (TerminalDecode.bitRefRoutine input loader).depth duration path.1 +
        (TerminalDecode.foldBitRefs loader rest).depth duration path.2 =
          (((TerminalDecode.bitRefRoutine input loader).eventTrace path.1 ++
            (TerminalDecode.foldBitRefs loader rest).eventTrace path.2).map duration).sum
      rw [List.map_append, List.sum_append, decoder_bit_duration, ih]

/-- The same row path has serial depth equal to the sum of its actually emitted durations. -/
theorem gf2RowBody_duration_eventTrace (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (rowBody input row matrix loader).Path) :
    (rowBody input row matrix loader).depth duration path =
      (((rowBody input row matrix loader).eventTrace path).map duration).sum := by
  change duration (.classicalOperation (.wordBinary .bitXor width)) +
    ((TerminalDecode.into .bigEndian input loader).depth duration path.2.1 +
      duration (.classicalOperation (.vector .write rowCount width))) = _
  change _ = ((([.classicalOperation (.wordBinary .bitXor width)] :
    List (Resource.Event kind)) ++
    ((TerminalDecode.into .bigEndian input loader).eventTrace path.2.1 ++
      ([.classicalOperation (.vector .write rowCount width)] :
        List (Resource.Event kind)))).map duration).sum
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact congrArg (fun value => duration (.classicalOperation (.wordBinary .bitXor width)) +
    (value + duration (.classicalOperation (.vector .write rowCount width))))
    (decoder_duration loader (List.ofFn (fun index => .bitsGet input index)) duration path.2.1)

private theorem rowBody_resident (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (path : (rowBody input row matrix loader).Path) :
    (rowBody input row matrix loader).peakResidentSpace path ≤ ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (.classical (rowClearOp loader))
    (.seq (TerminalDecode.into .bigEndian input loader)
      (.classical (rowWriteOp row matrix loader))) path).le.trans ?_
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_classical]
  exact SpacePool.max_le le_rfl (SpacePool.max_le
    (TerminalDecode.terminalDecode_intoFromBitRefs_resident_le .bigEndian
      (fun index => .bitsGet input index) loader path.2.1) le_rfl)

private theorem rowBody_auxiliary (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (path : (rowBody input row matrix loader).Path) :
    (rowBody input row matrix loader).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (.classical (rowClearOp loader))
    (.seq (TerminalDecode.into .bigEndian input loader)
      (.classical (rowWriteOp row matrix loader))) path).le.trans ?_
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_classical]
  exact SpacePool.max_le le_rfl (SpacePool.max_le
    (TerminalDecode.terminalDecode_intoFromBitRefs_auxiliary_le .bigEndian
      (fun index => .bitsGet input index) loader path.2.1) le_rfl)

/-- Lexical entry and release add no events to the actual row sequence. -/
theorem gf2LoadRow_pool_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (path : (loadRow input matrix row).Path) :
    (loadRow input matrix row).resourcePool path ≤ rowEnvelope kind rowCount width :=
  gf2RowBody_pool_le _ row _ _ path

/-- One real row scope has the unchanged original duration allowance. -/
theorem gf2LoadRow_depth_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (duration : Resource.Event kind → Nat) (path : (loadRow input matrix row).Path) :
    (loadRow input matrix row).depth duration path ≤ rowDepthLimit rowCount width duration :=
  gf2RowBody_depth_le _ row _ _ duration path

/-- Scope operations preserve the same actual serial-duration equation. -/
theorem gf2LoadRow_duration_eventTrace
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (duration : Resource.Event kind → Nat) (path : (loadRow input matrix row).Path) :
    (loadRow input matrix row).depth duration path =
      (((loadRow input matrix row).eventTrace path).map duration).sum :=
  gf2RowBody_duration_eventTrace _ row _ _ duration path

/-- The only additional resident storage is the one actual scoped decoding word. -/
theorem gf2LoadRow_resident_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (path : (loadRow input matrix row).Path) :
    (loadRow input matrix row).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (placedRow input matrix row) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _) (rowBody_resident _ row _ _ path)

/-- The actual temporary word is the sole additional auxiliary allocation. -/
theorem gf2LoadRow_auxiliary_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (path : (loadRow input matrix row).Path) :
    (loadRow input matrix row).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (placedRow input matrix row) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _) (rowBody_auxiliary _ row _ _ path)

/-- The original ordered matrix load adds the actual per-row native allowances. -/
theorem gf2LoadMatrix_pool_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (path : (loadMatrix input matrix).Path) :
    (loadMatrix input matrix).resourcePool path ≤
      ResourcePool.scale rowCount (rowEnvelope kind rowCount width) :=
  Circuit.forRange_pool_le rowCount _ _ (gf2LoadRow_pool_le input matrix) path

/-- Full duration is bounded by the sum of the original per-row dependencies. -/
theorem gf2LoadMatrix_depth_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (duration : Resource.Event kind → Nat) (path : (loadMatrix input matrix).Path) :
    (loadMatrix input matrix).depth duration path ≤
      rowCount * rowDepthLimit rowCount width duration := by
  change (Circuit.forRange rowCount (loadRow input matrix)).depth duration path ≤ _
  simpa only [Finset.sum_const, Finset.card_fin, smul_eq_mul] using
    Circuit.forRange_depth_le_sum rowCount (loadRow input matrix) duration
      (fun _ => rowDepthLimit rowCount width duration)
      (fun row => gf2LoadRow_depth_le input matrix row duration) path

/-- Every actual complete path is serial, with no replayed event ledger. -/
theorem gf2LoadMatrix_duration_eventTrace
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (duration : Resource.Event kind → Nat) (path : (loadMatrix input matrix).Path) :
    (loadMatrix input matrix).depth duration path =
      (((loadMatrix input matrix).eventTrace path).map duration).sum :=
  Circuit.forRange_duration_eventTrace rowCount _ duration
    (fun row => gf2LoadRow_duration_eventTrace input matrix row duration) path

/-- At most two real decoder instructions per bit, plus the original clear and vector write. -/
theorem gf2LoadMatrix_eventCount_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (path : (loadMatrix input matrix).Path) :
    ((loadMatrix input matrix).eventTrace path).length ≤ rowCount * (2 + 2 * width) := by
  have bounded := gf2LoadMatrix_depth_le input matrix (fun _ => 1) path
  rw [gf2LoadMatrix_duration_eventTrace] at bounded
  have one_sum : ∀ events : List (Resource.Event kind),
      (events.map (fun _ => 1)).sum = events.length := by
    intro events
    induction events with
    | nil => rfl
    | cons head tail ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
        ih, Nat.add_comm]
  rw [one_sum] at bounded
  have arithmetic : rowDepthLimit rowCount width (fun _ : Resource.Event kind => 1) =
      2 + 2 * width := by
    change 1 + (width * (1 + 1) + 1) = 2 + 2 * width
    omega
  exact bounded.trans_eq (congrArg (rowCount * ·) arithmetic)

/-- Row-local work is reused; its resident peak is independent of the number of rows. -/
theorem gf2LoadMatrix_resident_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (path : (loadMatrix input matrix).Path) :
    (loadMatrix input matrix).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace :=
  Circuit.forRange_resident_le rowCount _ _ (fun _axis => Nat.le_add_left _ _)
    (gf2LoadRow_resident_le input matrix) path

/-- Releasing each decoder before the next row avoids multiplying its auxiliary storage. -/
theorem gf2LoadMatrix_auxiliary_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (path : (loadMatrix input matrix).Path) :
    (loadMatrix input matrix).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace :=
  Circuit.forRange_auxiliary_le rowCount _ _ (fun _axis => Nat.le_add_left _ _)
    (gf2LoadRow_auxiliary_le input matrix) path

end QuantumAlg.ClassicalRoutines.GF2.Native
