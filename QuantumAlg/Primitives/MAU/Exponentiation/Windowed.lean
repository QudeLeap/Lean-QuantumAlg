/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Primitives.MAU.Multiplication.Windowed.Even
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate

/-!
# Native exponentiation from the exact windowed multiplier

Each exponent wire controls the actual even-width windowed multiplication gate
list through one reusable clean work bit. The executable circuit contains only
the gates required by the selected coefficient. Parameter-independent resource
claims are proved envelopes over those actual lists; no inactive padding gates
are executed to manufacture a common trace.
-/

section

namespace QuantumAlg
namespace MAU.Exponentiation.WindowedCircuit

noncomputable section

open MAU.Multiplication.Windowed
open EncodedBit.GateSpec

/-- Even arithmetic word width represented by `half` two-bit windows. -/
abbrev wordBits (half : Nat) : Nat := Even.width half

/-- Complete full-layout windowed multiplication carrier. -/
abbrev Core (half : Nat) : Type := FullLayout.Registers (wordBits half)

/-- Exponent register, shared windowed multiplier, and one clean control bit. -/
abbrev Registers (m half : Nat) : Type :=
  Fin (2 ^ m) × (Core half × Bool)

/-- Shared arithmetic workspace excluding the exponent register. -/
abbrev Workspace (half : Nat) : Type := Core half × Bool

/-- Encoding of the shared windowed arithmetic workspace. -/
abbrev workspaceEncoding (half : Nat) : BinaryLabelEncoding (Workspace half) :=
  BinaryLabelEncoding.prod (FullLayout.encoding (wordBits half))
    BinaryLabelEncoding.bool

/-- Encoding of exponent plus shared arithmetic workspace. -/
abbrev encoding (m half : Nat) : BinaryLabelEncoding (Registers m half) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity m)
    (workspaceEncoding half)

/-- The `5n+4` multiplier plus one clean control bit occupies `5n+5` qubits. -/
theorem workspaceEncoding_width (half : Nat) :
    (workspaceEncoding half).width = 5 * wordBits half + 5 := by
  simp [workspaceEncoding, wordBits]

/-- Total exponentiation width is exponent width plus the shared workspace. -/
theorem encoding_width (m half : Nat) :
    (encoding m half).width = m + (5 * wordBits half + 5) := by
  simp [encoding]

/-- Canonical fixed-width word occupied by one unit residue. -/
def unitWord (half N : Nat) (_hNgtOne : 1 < N)
    (_hN : N < 2 ^ wordBits half) (unit : (ZMod N)ˣ) :
    PlainAdder.Word (wordBits half) :=
  Even.unitWord half unit

@[simp] theorem unitWord_val (half N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits half) (unit : (ZMod N)ˣ) :
    (unitWord half N hNgtOne hN unit).val = (unit : ZMod N).val := by
  let _ : NeZero N := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hNgtOne)⟩
  unfold unitWord Even.unitWord
  exact ZMod.val_natCast_of_lt (lt_trans (ZMod.val_lt _) hN)

/-- Clean shared workspace containing one unit and no arithmetic garbage. -/
def cleanWorkspace (half N : Nat) (_hNgtOne : 1 < N)
    (_hN : N < 2 ^ wordBits half) (value : (ZMod N)ˣ) : Workspace half :=
  (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
      (wordBits half) N (MAU.Multiplication.cleanInput (value : ZMod N)),
    false)

/-! ## One native controlled multiplier -/

/-- Static unit assigned to one little-endian exponent position. -/
def stageUnit {m N : Nat} (unit : (ZMod N)ˣ) (bit : Fin m) : (ZMod N)ˣ :=
  unit ^ (2 ^ bit.val)

/-- One exponent bit in the complete product encoding. -/
def exponentBit (m half : Nat) (bit : Fin m) :
    EncodedBit (encoding m half) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.finIdentity m) (workspaceEncoding half)
    (BinaryLabelEncoding.finIdentityBit m
      (WireAddress.littleEndianWire bit))

/-- Reusable clean bit for native control decomposition. -/
def controlWorkBit (m half : Nat) : EncodedBit (encoding m half) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.finIdentity m) (workspaceEncoding half)
    (BinaryLabelEncoding.prodRightBit
      (FullLayout.encoding (wordBits half)) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit)

@[simp] theorem exponentBit_get (m half : Nat) (bit : Fin m)
    (state : Registers m half) :
    (exponentBit m half bit).get state = state.1.val.testBit bit.val := by
  change state.1.val.testBit
      (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

@[simp] theorem controlWorkBit_get (m half : Nat) (state : Registers m half) :
    (controlWorkBit m half).get state = state.2.2 :=
  rfl

theorem controlWork_ne (m half : Nat) (bit : Fin m) :
    (exponentBit m half bit).wire ≠ (controlWorkBit m half).wire := by
  simpa [exponentBit, controlWorkBit, encoding, workspaceEncoding] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (BinaryLabelEncoding.finIdentity m) (workspaceEncoding half)
      (BinaryLabelEncoding.prodRightBit
        (FullLayout.encoding (wordBits half)) BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit)
      (BinaryLabelEncoding.finIdentityBit m
        (WireAddress.littleEndianWire bit))).symm

/-- Actual windowed multiplication gates lifted past exponent and work fields. -/
def liftedMultiplierGates (m half N : Nat) (unit : (ZMod N)ˣ)
    (bit : Fin m) : List (EncodedBit.GateSpec (encoding m half)) :=
  ((Even.multiplicationGates half N (stageUnit unit bit)).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodRight (BinaryLabelEncoding.finIdentity m))

theorem liftedMultiplierGates_stepList (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) (state : Registers m half) :
    EncodedBit.GateSpec.stepList (liftedMultiplierGates m half N unit bit)
        state =
      (state.1,
        (Even.multiplicationStep half N (stageUnit unit bit) state.2.1,
          state.2.2)) := by
  unfold liftedMultiplierGates
  rw [EncodedBit.GateSpec.stepList_prodRight,
    EncodedBit.GateSpec.stepList_prodLeft]
  rfl

theorem controlDisjoint (m half N : Nat) (unit : (ZMod N)ˣ)
    (bit : Fin m) : ∀ gate, gate ∈ liftedMultiplierGates m half N unit bit →
    EncodedBit.GateSpec.bitDisjoint (exponentBit m half bit) gate := by
  intro gate hgate
  rw [liftedMultiplierGates] at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, _hinner, rfl⟩
  simpa [exponentBit, encoding] using
    (EncodedBit.GateSpec.bitDisjoint_prodRight_leftBit
      (BinaryLabelEncoding.finIdentity m) (workspaceEncoding half)
      (BinaryLabelEncoding.finIdentityBit m
        (WireAddress.littleEndianWire bit)) innerGate)

theorem workDisjoint (m half N : Nat) (unit : (ZMod N)ˣ)
    (bit : Fin m) : ∀ gate, gate ∈ liftedMultiplierGates m half N unit bit →
    EncodedBit.GateSpec.bitDisjoint (controlWorkBit m half) gate := by
  intro gate hgate
  rw [liftedMultiplierGates] at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, hinner, rfl⟩
  rcases List.mem_map.mp hinner with ⟨sourceGate, _hsource, rfl⟩
  have hinnerDisjoint :=
    EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit
      (FullLayout.encoding (wordBits half)) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit sourceGate
  have houterDisjoint :=
    EncodedBit.GateSpec.bitDisjoint_prodRight_of_bitDisjoint
      (BinaryLabelEncoding.finIdentity m)
      (BinaryLabelEncoding.prodRightBit
        (FullLayout.encoding (wordBits half)) BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit)
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool sourceGate)
      hinnerDisjoint
  simpa [controlWorkBit, encoding, workspaceEncoding] using houterDisjoint

/-- Coefficient-independent source-gate bound for one windowed multiplier. -/
def sourceSlotBound (half : Nat) : Nat :=
  Even.multiplierPrimitiveBound half

theorem sourceSlotBound_eq_multiplierPrimitiveBound (half : Nat) :
    sourceSlotBound half = Even.multiplierPrimitiveBound half := by
  rfl

theorem liftedMultiplierGates_length_le_sourceSlotBound
    (m half N : Nat) (unit : (ZMod N)ˣ) (bit : Fin m) :
    (liftedMultiplierGates m half N unit bit).length ≤
      sourceSlotBound half := by
  simpa [liftedMultiplierGates, sourceSlotBound] using
    Even.multiplicationGates_length_le_multiplierPrimitiveBound
      half N (stageUnit unit bit)

/-- Actual native gate list of one exponent-controlled windowed multiply. -/
def stageGates (m half N : Nat) (unit : (ZMod N)ˣ) (bit : Fin m) :
    List (EncodedBit.GateSpec (encoding m half)) :=
  controlledListWithWorkGates (exponentBit m half bit)
    (controlWorkBit m half) (liftedMultiplierGates m half N unit bit)
    (controlDisjoint m half N unit bit) (workDisjoint m half N unit bit)
    (controlWork_ne m half bit)

/-- Circuit compiled directly from the actual native gate list. -/
def stageProgram (m half N : Nat) (unit : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit (Qubits (encoding m half).width) :=
  EncodedBit.GateSpec.programList
    (stageGates m half N unit bit)

/-- Total basis action of the same native list. -/
def stageStep (m half N : Nat) (unit : (ZMod N)ˣ) (bit : Fin m) :
    Registers m half → Registers m half :=
  EncodedBit.GateSpec.stepList
    (stageGates m half N unit bit)

theorem stageProgram_realizes (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit.Realizes (encoding m half)
      (stageProgram m half N unit bit)
      (stageStep m half N unit bit) :=
  EncodedBit.GateSpec.realizesList _

theorem stageProgram_physical_idx_subset_range (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) :
    (stageProgram m half N unit bit).physical_idx ⊆
      List.range (encoding m half).width :=
  EncodedBit.GateSpec.programList_physical_idx_subset_range _

theorem stageGates_events (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) :
    (stageGates m half N unit bit).map
        EncodedBit.GateSpec.event =
      (liftedMultiplierGates m half N unit bit).flatMap
        controlledEventExpansion := by
  exact map_event_controlledListWithWorkGates _ _ _ _ _ _

/-- One metadata-only resource block dominating the native control expansion
of any single source gate. It is not an executable padding schedule. -/
def sourceSlotEvents : List (Resource.Event .quantum) :=
  [.gate (.builtin "cnot"), .gate (.builtin "toffoli"),
    .gate (.builtin "toffoli"), .gate (.builtin "toffoli")]

/-- Coefficient-independent event envelope for one controlled multiplier. -/
def stageEventEnvelope (half : Nat) : ResourcePool .quantum :=
  ResourcePool.ofList
    (List.replicate (sourceSlotBound half) sourceSlotEvents).flatten

/-- Coefficient-independent serialized depth envelope for one stage. -/
def stageDepthEnvelope (half : Nat) :
    DepthExpr (Resource.Event .quantum) :=
  depthOfEvents
    (List.replicate (sourceSlotBound half) sourceSlotEvents).flatten

private theorem count_controlledEventExpansion_le_sourceSlot
    {Data : Type} {enc : BinaryLabelEncoding Data}
    (focus : Resource.Event .quantum)
    (gate : EncodedBit.GateSpec enc) :
    List.count focus (controlledEventExpansion gate) ≤
      List.count focus sourceSlotEvents := by
  have hsub : List.Sublist (controlledEventExpansion gate) sourceSlotEvents := by
    cases gate <;> simp [controlledEventExpansion, sourceSlotEvents]
  exact hsub.count_le focus

private theorem count_flatMap_controlledEventExpansion_le
    {Data : Type} {enc : BinaryLabelEncoding Data}
    (focus : Resource.Event .quantum) :
    ∀ gates : List (EncodedBit.GateSpec enc),
      List.count focus (gates.flatMap controlledEventExpansion) ≤
        gates.length * List.count focus sourceSlotEvents
  | [] => by simp
  | gate :: rest => by
      simp only [List.flatMap_cons, List.count_append, List.length_cons]
      have hhead := count_controlledEventExpansion_le_sourceSlot focus gate
      have htail := count_flatMap_controlledEventExpansion_le focus rest
      calc
        List.count focus (controlledEventExpansion gate) +
              List.count focus (rest.flatMap controlledEventExpansion) ≤
            List.count focus sourceSlotEvents +
              rest.length * List.count focus sourceSlotEvents :=
          Nat.add_le_add hhead htail
        _ = (rest.length + 1) * List.count focus sourceSlotEvents := by
          rw [Nat.succ_mul]
          omega

private theorem count_replicate_flatten (focus : Resource.Event .quantum)
    (events : List (Resource.Event .quantum)) : ∀ count : Nat,
    List.count focus (List.replicate count events).flatten =
      count * List.count focus events
  | 0 => by simp
  | count + 1 => by
      simp only [List.replicate_succ, List.flatten_cons, List.count_append,
        count_replicate_flatten focus events count]
      rw [Nat.succ_mul]
      omega

private theorem depthEval_depthOfEvents
    (assignment : Resource.Event .quantum → Nat) :
    ∀ events : List (Resource.Event .quantum),
      DepthExpr.depthEval assignment (depthOfEvents events) =
        (events.map assignment).sum
  | [] => rfl
  | event :: rest => by
      simp only [depthOfEvents, DepthExpr.depthEval_seq,
        DepthExpr.depthEval_atom, List.map_cons, List.sum_cons,
        depthEval_depthOfEvents assignment rest]

private theorem sum_controlledEventExpansion_le_sourceSlot
    {Data : Type} {enc : BinaryLabelEncoding Data}
    (assignment : Resource.Event .quantum → Nat)
    (gate : EncodedBit.GateSpec enc) :
    ((controlledEventExpansion gate).map assignment).sum ≤
      (sourceSlotEvents.map assignment).sum := by
  cases gate with
  | x _ => simp [controlledEventExpansion, sourceSlotEvents]
  | cnot _ _ _ =>
      simp [controlledEventExpansion, sourceSlotEvents]
      omega
  | toffoli _ _ _ _ _ _ =>
      simp [controlledEventExpansion, sourceSlotEvents]

private theorem sum_flatMap_controlledEventExpansion_le
    {Data : Type} {enc : BinaryLabelEncoding Data}
    (assignment : Resource.Event .quantum → Nat) :
    ∀ gates : List (EncodedBit.GateSpec enc),
      (((gates.flatMap controlledEventExpansion).map assignment).sum) ≤
        gates.length * (sourceSlotEvents.map assignment).sum
  | [] => by simp
  | gate :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons]
      have hhead := sum_controlledEventExpansion_le_sourceSlot assignment gate
      have htail := sum_flatMap_controlledEventExpansion_le assignment rest
      calc
        ((controlledEventExpansion gate).map assignment).sum +
              ((rest.flatMap controlledEventExpansion).map assignment).sum ≤
            (sourceSlotEvents.map assignment).sum +
              rest.length * (sourceSlotEvents.map assignment).sum :=
          Nat.add_le_add hhead htail
        _ = (rest.length + 1) *
              (sourceSlotEvents.map assignment).sum := by
          rw [Nat.succ_mul]
          omega

private theorem sum_replicate_flatten
    (assignment : Resource.Event .quantum → Nat)
    (events : List (Resource.Event .quantum)) : ∀ count : Nat,
    (((List.replicate count events).flatten.map assignment).sum) =
      count * (events.map assignment).sum
  | 0 => by simp
  | count + 1 => by
      simp only [List.replicate_succ, List.flatten_cons, List.map_append,
        List.sum_append, sum_replicate_flatten assignment events count]
      rw [Nat.succ_mul]
      omega

@[simp] theorem stageDepthEnvelope_unit (half : Nat) :
    DepthExpr.depthEval (fun _event => 1) (stageDepthEnvelope half) =
      4 * sourceSlotBound half := by
  rw [stageDepthEnvelope, depthEval_depthOfEvents, sum_replicate_flatten]
  simp [sourceSlotEvents]
  omega

@[simp] theorem stageEventEnvelope_card (half : Nat) :
    (stageEventEnvelope half).card = 4 * sourceSlotBound half := by
  simp [stageEventEnvelope, ResourcePool.ofList, sourceSlotEvents]
  omega

@[simp] theorem stageEventEnvelope_toffoli_count (half : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
      (stageEventEnvelope half) = 3 * sourceSlotBound half := by
  have hcount :
      List.count (.gate (.builtin "toffoli") : Resource.Event .quantum)
          sourceSlotEvents = 3 := by
    decide
  rw [stageEventEnvelope, ResourcePool.count_ofList,
    count_replicate_flatten, hcount]
  exact Nat.mul_comm _ _

theorem stageEventEnvelope_gate_count_zero_of_ne
    (half : Nat) (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label) (stageEventEnvelope half) = 0 := by
  have hcnotEvent :
      (.gate label : Resource.Event .quantum) ≠
        .gate (.builtin "cnot") := by
    intro equality
    cases equality
    exact hcnot rfl
  have htoffoliEvent :
      (.gate label : Resource.Event .quantum) ≠
        .gate (.builtin "toffoli") := by
    intro equality
    cases equality
    exact htoffoli rfl
  have hnotmem :
      (.gate label : Resource.Event .quantum) ∉ sourceSlotEvents := by
    intro member
    simp only [sourceSlotEvents, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with equality | equality | equality | equality
    · exact hcnotEvent equality
    · exact htoffoliEvent equality
    · exact htoffoliEvent equality
    · exact htoffoliEvent equality
  rw [stageEventEnvelope, ResourcePool.count_ofList,
    count_replicate_flatten]
  rw [List.count_eq_zero_of_not_mem hnotmem]
  simp

theorem stageProgram_eventCost_le (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) :
    (stageProgram m half N unit bit).eventCost ≤
      stageEventEnvelope half := by
  rw [stageProgram, EncodedBit.GateSpec.programList_eventCost,
    ResourcePool.le_iff_count]
  intro focus
  rw [ResourcePool.count_ofList, stageGates_events]
  rw [stageEventEnvelope, ResourcePool.count_ofList,
    count_replicate_flatten]
  exact (count_flatMap_controlledEventExpansion_le focus _).trans
    (Nat.mul_le_mul_right _
      (liftedMultiplierGates_length_le_sourceSlotBound
        m half N unit bit))

theorem stageProgram_eventDepth_le (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m)
    (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment
        (stageProgram m half N unit bit).eventDepth ≤
      DepthExpr.depthEval assignment (stageDepthEnvelope half) := by
  rw [stageProgram, EncodedBit.GateSpec.programList_eventDepth,
    depthEval_depthOfEvents, stageGates_events, stageDepthEnvelope,
    depthEval_depthOfEvents, sum_replicate_flatten]
  exact (sum_flatMap_controlledEventExpansion_le assignment _).trans
    (Nat.mul_le_mul_right _
      (liftedMultiplierGates_length_le_sourceSlotBound
        m half N unit bit))

theorem stageProgram_eventCost_card_le (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) :
    (stageProgram m half N unit bit).eventCost.card ≤
      3 * sourceSlotBound half := by
  rw [stageProgram, EncodedBit.GateSpec.programList_eventCost_card]
  exact (controlledListWithWorkGates_length_le_three_mul _ _ _ _ _ _).trans
    (Nat.mul_le_mul_left 3
      (liftedMultiplierGates_length_le_sourceSlotBound m half N unit bit))

/-- Exact coefficient-sensitive native Toffoli count of one stage. -/
def stageToffoliCount (m half N : Nat) (unit : (ZMod N)ˣ)
    (bit : Fin m) : Nat :=
  ((liftedMultiplierGates m half N unit bit).map cnotMultiplicity).sum +
    3 * ((liftedMultiplierGates m half N unit bit).map
      toffoliMultiplicity).sum

theorem stageProgram_toffoli_count_eq (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (stageProgram m half N unit bit).eventCost =
      stageToffoliCount m half N unit bit := by
  rw [stageProgram, EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    stageGates, controlledListWithWorkGates_toffoliMultiplicity_sum]
  rfl

theorem stageProgram_gate_count_zero_of_ne (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label)
        (stageProgram m half N unit bit).eventCost = 0 := by
  by_cases hx : label = .builtin "x"
  · subst label
    rw [stageProgram, EncodedBit.GateSpec.programList_x_count_eq_sum,
      stageGates, controlledListWithWorkGates_xMultiplicity_sum]
  · exact EncodedBit.GateSpec.programList_gate_count_zero_of_ne _ _
      hx hcnot htoffoli

/-- Unit selected by one exponent bit. -/
def selectedUnit {m N : Nat} (unit : (ZMod N)ˣ)
    (exponent : Fin (2 ^ m)) (bit : Fin m) : (ZMod N)ˣ :=
  if exponent.val.testBit bit.val then stageUnit unit bit else 1

/-- The stage step is exactly the generic clean-work controlled-list action. -/
theorem stageStep_eq_controlledListWithWorkStep (m half N : Nat)
    (unit : (ZMod N)ˣ) (bit : Fin m) (state : Registers m half) :
    stageStep m half N unit bit state =
      EncodedBit.GateSpec.controlledListWithWorkStep
        (exponentBit m half bit) (controlWorkBit m half)
        (liftedMultiplierGates m half N unit bit)
        (controlDisjoint m half N unit bit) (workDisjoint m half N unit bit)
        (controlWork_ne m half bit) state := by
  rfl

/-- Clean endpoint of one actual exponent-controlled windowed multiplier. -/
theorem stageStep_cleanWorkspace (m half N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits half) (unit value : (ZMod N)ˣ)
    (bit : Fin m) (exponent : Fin (2 ^ m)) :
    stageStep m half N unit bit
        (exponent, cleanWorkspace half N hNgtOne hN value) =
      (exponent, cleanWorkspace half N hNgtOne hN
        (selectedUnit unit exponent bit * value)) := by
  rw [stageStep_eq_controlledListWithWorkStep m half N unit bit]
  by_cases hcontrol : exponent.val.testBit bit.val
  · have htrue :
        (exponentBit m half bit).get
          (exponent, cleanWorkspace half N hNgtOne hN value) = true := by
      simpa using hcontrol
    rw [EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (exponentBit m half bit) (controlWorkBit m half)
      (liftedMultiplierGates m half N unit bit)
      (controlDisjoint m half N unit bit) (workDisjoint m half N unit bit)
      (controlWork_ne m half bit) _ htrue (by rfl)]
    rw [liftedMultiplierGates_stepList]
    have hendpoint := Even.multiplicationStep_cleanEndpoint half N
      (stageUnit unit bit) (value : ZMod N)
      (Nat.zero_lt_of_lt hNgtOne) hN
    unfold cleanWorkspace selectedUnit
    rw [if_pos hcontrol]
    simpa [MAU.Multiplication.cleanInput, MAU.Multiplication.cleanOutput]
      using congrArg (fun core => (exponent, (core, false))) hendpoint
  · have hfalse :
        (exponentBit m half bit).get
          (exponent, cleanWorkspace half N hNgtOne hN value) = false := by
      simpa using Bool.eq_false_of_not_eq_true hcontrol
    rw [EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (exponentBit m half bit) (controlWorkBit m half)
      (liftedMultiplierGates m half N unit bit)
      (controlDisjoint m half N unit bit) (workDisjoint m half N unit bit)
      (controlWork_ne m half bit) _ hfalse]
    simp [selectedUnit, hcontrol]

/-! ## Complete exponentiation fold -/

/-- Concatenate actual native stages in little-endian exponent order. -/
def programForBits (m half N : Nat) (unit : (ZMod N)ˣ) :
    List (Fin m) → UnitaryCircuit (Qubits (encoding m half).width)
  | [] => UnitaryCircuit.identity (Qubits (encoding m half).width) [] (by simp)
  | bit :: rest =>
      UnitaryCircuit.seq (stageProgram m half N unit bit)
        (programForBits m half N unit rest)

/-- Total basis action aligned with `programForBits`. -/
def programForBitsStep (m half N : Nat) (unit : (ZMod N)ˣ) :
    List (Fin m) → Registers m half → Registers m half
  | [] => id
  | bit :: rest => fun state =>
      programForBitsStep m half N unit rest
        (stageStep m half N unit bit state)

theorem programForBits_realizes (m half N : Nat) (unit : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      UnitaryCircuit.Realizes (encoding m half)
        (programForBits m half N unit bits)
        (programForBitsStep m half N unit bits)
  | [] => UnitaryCircuit.Realizes.identity (encoding m half)
  | bit :: rest =>
      UnitaryCircuit.Realizes.seq
        (firstStep := stageStep m half N unit bit)
        (secondStep := programForBitsStep m half N unit rest)
        (stageProgram_realizes m half N unit bit)
        (programForBits_realizes m half N unit rest)

theorem programForBits_physical_idx_subset_range (m half N : Nat)
    (unit : (ZMod N)ˣ) : ∀ bits : List (Fin m),
    (programForBits m half N unit bits).physical_idx ⊆
      List.range (encoding m half).width
  | [] => by
      intro index hindex
      simp [programForBits, UnitaryCircuit.identity] at hindex
  | bit :: rest => by
      intro index hindex
      change index ∈ UnitaryCircuit.unionPhysicalIdx
        (stageProgram m half N unit bit).physical_idx
        (programForBits m half N unit rest).physical_idx at hindex
      rcases List.mem_union_iff.mp hindex with hstage | hrest
      · exact stageProgram_physical_idx_subset_range
          m half N unit bit hstage
      · exact programForBits_physical_idx_subset_range
          m half N unit rest hrest

theorem programForBits_eventCost_le (m half N : Nat)
    (unit : (ZMod N)ˣ) : ∀ bits : List (Fin m),
    (programForBits m half N unit bits).eventCost ≤
      bits.length • stageEventEnvelope half
  | [] => by simp [programForBits]
  | bit :: rest => by
      rw [programForBits, UnitaryCircuit.seq_eventCost, List.length_cons]
      calc
        (stageProgram m half N unit bit).eventCost +
              (programForBits m half N unit rest).eventCost ≤
            stageEventEnvelope half +
              rest.length • stageEventEnvelope half :=
          ResourcePool.add_mono
            (stageProgram_eventCost_le m half N unit bit)
            (programForBits_eventCost_le m half N unit rest)
        _ = (rest.length + 1) • stageEventEnvelope half := by
          rw [succ_nsmul]
          ac_rfl

theorem programForBits_eventDepth_le (m half N : Nat)
    (unit : (ZMod N)ˣ) (assignment : Resource.Event .quantum → Nat) :
    ∀ bits : List (Fin m),
      DepthExpr.depthEval assignment
          (programForBits m half N unit bits).eventDepth ≤
        DepthExpr.depthEval assignment
          (.iterate bits.length (stageDepthEnvelope half))
  | [] => by simp [programForBits]
  | bit :: rest => by
      rw [programForBits, UnitaryCircuit.seq_eventDepth,
        DepthExpr.depthEval_seq, List.length_cons,
        DepthExpr.depthEval_iterate]
      calc
        DepthExpr.depthEval assignment
              (stageProgram m half N unit bit).eventDepth +
            DepthExpr.depthEval assignment
              (programForBits m half N unit rest).eventDepth ≤
          DepthExpr.depthEval assignment (stageDepthEnvelope half) +
            rest.length *
              DepthExpr.depthEval assignment (stageDepthEnvelope half) :=
          Nat.add_le_add
            (stageProgram_eventDepth_le m half N unit bit assignment)
            (programForBits_eventDepth_le m half N unit assignment rest)
        _ = (rest.length + 1) *
              DepthExpr.depthEval assignment (stageDepthEnvelope half) := by
          rw [Nat.succ_mul]
          omega

theorem programForBits_eventCost_card_le (m half N : Nat)
    (unit : (ZMod N)ˣ) : ∀ bits : List (Fin m),
    (programForBits m half N unit bits).eventCost.card ≤
      (3 * sourceSlotBound half) * bits.length
  | [] => by simp [programForBits]
  | bit :: rest => by
      rw [programForBits, UnitaryCircuit.seq_eventCost, Multiset.card_add,
        List.length_cons]
      calc
        (stageProgram m half N unit bit).eventCost.card +
              (programForBits m half N unit rest).eventCost.card ≤
            3 * sourceSlotBound half +
              (3 * sourceSlotBound half) * rest.length :=
          Nat.add_le_add
            (stageProgram_eventCost_card_le m half N unit bit)
            (programForBits_eventCost_card_le m half N unit rest)
        _ = (3 * sourceSlotBound half) * (rest.length + 1) := by
          rw [Nat.mul_succ]
          ac_rfl

/-- Exact native Toffoli count of the selected coefficient stages. -/
def programForBitsToffoliCount (m half N : Nat) (unit : (ZMod N)ˣ)
    (bits : List (Fin m)) : Nat :=
  (bits.map (stageToffoliCount m half N unit)).sum

theorem programForBits_toffoli_count_eq (m half N : Nat)
    (unit : (ZMod N)ˣ) : ∀ bits : List (Fin m),
    ResourcePool.count (.gate (.builtin "toffoli"))
        (programForBits m half N unit bits).eventCost =
      programForBitsToffoliCount m half N unit bits
  | [] => by simp [programForBits, programForBitsToffoliCount]
  | bit :: rest => by
      rw [programForBits, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        stageProgram_toffoli_count_eq,
        programForBits_toffoli_count_eq m half N unit rest]
      rfl

theorem programForBits_gate_count_zero_of_ne (m half N : Nat)
    (unit : (ZMod N)ˣ) (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") : ∀ bits : List (Fin m),
    ResourcePool.count (.gate label)
      (programForBits m half N unit bits).eventCost = 0
  | [] => by simp [programForBits]
  | bit :: rest => by
      simp only [programForBits, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        stageProgram_gate_count_zero_of_ne m half N unit bit label
          hcnot htoffoli,
        programForBits_gate_count_zero_of_ne m half N unit label
          hcnot htoffoli rest,
        Nat.zero_add]

theorem programForBitsStep_cleanWorkspace (m half N : Nat)
    (hNgtOne : 1 < N) (hN : N < 2 ^ wordBits half)
    (unit value : (ZMod N)ˣ) (exponent : Fin (2 ^ m)) :
    ∀ bits : List (Fin m),
      programForBitsStep m half N unit bits
          (exponent, cleanWorkspace half N hNgtOne hN value) =
        (exponent, cleanWorkspace half N hNgtOne hN
          ((bits.map (selectedUnit unit exponent)).prod * value))
  | [] => by simp [programForBitsStep]
  | bit :: rest => by
      change programForBitsStep m half N unit rest
        (stageStep m half N unit bit
          (exponent, cleanWorkspace half N hNgtOne hN value)) = _
      rw [stageStep_cleanWorkspace]
      rw [programForBitsStep_cleanWorkspace m half N hNgtOne hN unit
        (selectedUnit unit exponent bit * value) exponent rest]
      apply congrArg (fun updated =>
        (exponent, cleanWorkspace half N hNgtOne hN updated))
      simp only [List.map_cons, List.prod_cons]
      ac_rfl

theorem selectedUnit_product_eq_pow_selectedLowWeight {N : Nat} (m : Nat)
    (unit : (ZMod N)ˣ) (exponent : Nat) :
    (∏ bit : Fin m,
      if exponent.testBit bit.val then stageUnit unit bit else 1) =
      unit ^ Nat.FixedWidth.ModularAccumulate.selectedLowWeight
        exponent m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.prod_univ_castSucc,
        Nat.FixedWidth.ModularAccumulate.selectedLowWeight_succ,
        pow_add]
      have hprefix :
          (∏ bit : Fin m,
            if exponent.testBit bit.castSucc.val then
              stageUnit unit bit.castSucc else 1) =
            unit ^
              Nat.FixedWidth.ModularAccumulate.selectedLowWeight
                exponent m := by
        simpa [stageUnit] using ih
      rw [hprefix]
      cases hbit : exponent.testBit m <;>
        simp [stageUnit, hbit,
          Nat.FixedWidth.ModularAccumulate.selectedBitWeight]

theorem selectedUnit_all_eq_pow {m N : Nat} (unit : (ZMod N)ˣ)
    (exponent : Fin (2 ^ m)) :
    (List.ofFn fun bit : Fin m => selectedUnit unit exponent bit).prod =
      unit ^ exponent.val := by
  rw [List.prod_ofFn]
  simp only [selectedUnit]
  rw [selectedUnit_product_eq_pow_selectedLowWeight m unit exponent.val,
    Nat.FixedWidth.ModularAccumulate.selectedLowWeight_eq_self_of_lt_two_pow
      exponent.isLt]

/-- All exponent wires in increasing little-endian order. -/
def exponentBits (m : Nat) : List (Fin m) :=
  List.ofFn fun bit : Fin m => bit

/-- Complete native windowed exponentiation program. -/
def exponentiationProgram (m half N : Nat) (unit : (ZMod N)ˣ) :
    UnitaryCircuit (Qubits (encoding m half).width) :=
  programForBits m half N unit (exponentBits m)

/-- Basis action aligned with the complete exponentiation circuit. -/
def exponentiationStep (m half N : Nat) (unit : (ZMod N)ˣ) :
    Registers m half → Registers m half :=
  programForBitsStep m half N unit (exponentBits m)

theorem exponentiationProgram_realizes (m half N : Nat)
    (unit : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (encoding m half)
      (exponentiationProgram m half N unit)
      (exponentiationStep m half N unit) :=
  programForBits_realizes m half N unit (exponentBits m)

theorem exponentiationStep_cleanWorkspace (m half N : Nat)
    (hNgtOne : 1 < N) (hN : N < 2 ^ wordBits half)
    (unit value : (ZMod N)ˣ) (exponent : Fin (2 ^ m)) :
    exponentiationStep m half N unit
        (exponent, cleanWorkspace half N hNgtOne hN value) =
      (exponent, cleanWorkspace half N hNgtOne hN
        (unit ^ exponent.val * value)) := by
  unfold exponentiationStep
  rw [programForBitsStep_cleanWorkspace]
  unfold exponentBits
  simp only [List.map_ofFn, Function.comp_def]
  rw [selectedUnit_all_eq_pow]

theorem exponentiationProgram_physical_idx_subset_range (m half N : Nat)
    (unit : (ZMod N)ˣ) :
    (exponentiationProgram m half N unit).physical_idx ⊆
      List.range (encoding m half).width :=
  programForBits_physical_idx_subset_range
    m half N unit (exponentBits m)

/-- Event envelope of one complete `m`-bit exponentiation family. -/
def exponentiationEventEnvelope (m half : Nat) : ResourcePool .quantum :=
  m • stageEventEnvelope half

/-- Serialized depth envelope of one complete exponentiation family. -/
def exponentiationDepthEnvelope (m half : Nat) :
    DepthExpr (Resource.Event .quantum) :=
  .iterate m (stageDepthEnvelope half)

@[simp] theorem exponentiationEventEnvelope_card (m half : Nat) :
    (exponentiationEventEnvelope m half).card =
      (4 * sourceSlotBound half) * m := by
  rw [exponentiationEventEnvelope, Multiset.card_nsmul,
    stageEventEnvelope_card]
  exact Nat.mul_comm _ _

@[simp] theorem exponentiationEventEnvelope_toffoli_count
    (m half : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (exponentiationEventEnvelope m half) =
      (3 * sourceSlotBound half) * m := by
  rw [exponentiationEventEnvelope, ResourcePool.count_nsmul,
    stageEventEnvelope_toffoli_count]
  exact Nat.mul_comm _ _

theorem exponentiationEventEnvelope_gate_count_zero_of_ne
    (m half : Nat) (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label)
        (exponentiationEventEnvelope m half) = 0 := by
  rw [exponentiationEventEnvelope, ResourcePool.count_nsmul,
    stageEventEnvelope_gate_count_zero_of_ne half label hcnot htoffoli]
  simp

@[simp] theorem exponentiationDepthEnvelope_unit (m half : Nat) :
    DepthExpr.depthEval (fun _event => 1)
        (exponentiationDepthEnvelope m half) =
      (4 * sourceSlotBound half) * m := by
  rw [exponentiationDepthEnvelope, DepthExpr.depthEval_iterate,
    stageDepthEnvelope_unit]
  exact Nat.mul_comm _ _

theorem exponentiationProgram_eventCost_le (m half N : Nat)
    (unit : (ZMod N)ˣ) :
    (exponentiationProgram m half N unit).eventCost ≤
      exponentiationEventEnvelope m half := by
  rw [exponentiationProgram]
  simpa [exponentiationEventEnvelope, exponentBits] using
    programForBits_eventCost_le m half N unit (exponentBits m)

theorem exponentiationProgram_eventDepth_le (m half N : Nat)
    (unit : (ZMod N)ˣ) (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment
        (exponentiationProgram m half N unit).eventDepth ≤
      DepthExpr.depthEval assignment
        (exponentiationDepthEnvelope m half) := by
  rw [exponentiationProgram]
  simpa [exponentiationDepthEnvelope, exponentBits] using
    programForBits_eventDepth_le m half N unit assignment (exponentBits m)

theorem exponentiationProgram_eventCost_card_le (m half N : Nat)
    (unit : (ZMod N)ˣ) :
    (exponentiationProgram m half N unit).eventCost.card ≤
      (3 * sourceSlotBound half) * m := by
  rw [exponentiationProgram]
  simpa [exponentBits] using programForBits_eventCost_card_le
    m half N unit (exponentBits m)

/-- Exact coefficient-sensitive native Toffoli count of one exponentiation. -/
def exponentiationToffoliCount (m half N : Nat)
    (unit : (ZMod N)ˣ) : Nat :=
  programForBitsToffoliCount m half N unit (exponentBits m)

theorem exponentiationProgram_toffoli_count_eq (m half N : Nat)
    (unit : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (exponentiationProgram m half N unit).eventCost =
      exponentiationToffoliCount m half N unit := by
  rw [exponentiationProgram]
  exact programForBits_toffoli_count_eq
    m half N unit (exponentBits m)

theorem exponentiationProgram_gate_count_zero_of_ne (m half N : Nat)
    (unit : (ZMod N)ˣ) (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label)
      (exponentiationProgram m half N unit).eventCost = 0 :=
  programForBits_gate_count_zero_of_ne m half N unit label
    hcnot htoffoli (exponentBits m)

theorem exponentiationProgram_applyNormalized_clean_ket (m half N : Nat)
    (hNgtOne : 1 < N) (hN : N < 2 ^ wordBits half)
    (unit value : (ZMod N)ˣ) (exponent : Fin (2 ^ m)) :
    (exponentiationProgram m half N unit).applyNormalized
        (NormalizedVector.ket
          ((encoding m half).encode
            (exponent, cleanWorkspace half N hNgtOne hN value))) =
      NormalizedVector.ket
        ((encoding m half).encode
          (exponent, cleanWorkspace half N hNgtOne hN
            (unit ^ exponent.val * value))) := by
  have hrealizes := (exponentiationProgram_realizes
    m half N unit).apply_encoded_ket
      (exponent, cleanWorkspace half N hNgtOne hN value)
  rw [exponentiationStep_cleanWorkspace] at hrealizes
  exact hrealizes

end


end MAU.Exponentiation.WindowedCircuit
end QuantumAlg

end
