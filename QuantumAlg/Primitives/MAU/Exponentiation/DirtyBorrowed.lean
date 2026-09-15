/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Multiplication.DirtyBorrowed
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate

/-!
# Exponent-controlled HRS modular multiplication

This module controls the literal Häner--Roetteler--Svore in-place constant
multiplier at each exponent bit.  The arithmetic carrier is the proved
`2n+1`-qubit HRS core; one additional clean bit is reused by the mechanical
X/CNOT/Toffoli control decomposition.
-/

section

namespace QuantumAlg
namespace MAU.Exponentiation.DirtyBorrowedCircuit

noncomputable section

open MAU.Multiplication.DirtyBorrowed

/-- HRS word width used by this implementation. -/
abbrev wordBits (interior : Nat) : Nat := (interior + 2).succ

/-- The literal HRS arithmetic carrier. -/
abbrev Core (interior : Nat) : Type :=
  State (wordBits interior) (LiteralBorrowed (wordBits interior))

/-- One exponent register, the HRS core, and one reusable clean control-work
bit. -/
abbrev Registers (m interior : Nat) : Type :=
  Fin (2 ^ m) × (Core interior × Bool)

/-- Binary encoding of the exponent-controlled HRS workspace. -/
abbrev encoding (m interior : Nat) : BinaryLabelEncoding (Registers m interior) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity m)
    (BinaryLabelEncoding.prod (literalR0Encoding (wordBits interior))
      BinaryLabelEncoding.bool)

/-- Shared arithmetic workspace, excluding the exponent register. -/
abbrev Workspace (interior : Nat) : Type := Core interior × Bool

/-- Binary encoding of the shared arithmetic workspace. -/
abbrev workspaceEncoding (interior : Nat) :
    BinaryLabelEncoding (Workspace interior) :=
  BinaryLabelEncoding.prod (literalR0Encoding (wordBits interior))
    BinaryLabelEncoding.bool

/-- The HRS `2n+1` core plus one clean control-work bit uses exactly `2n+2`
workspace qubits. -/
theorem workspaceEncoding_width (interior : Nat) :
    (workspaceEncoding interior).width = 2 * wordBits interior + 2 := by
  simp [workspaceEncoding, wordBits, literalR0Encoding_width]

/-- The exponent-controlled encoding is the exponent width plus the shared
HRS workspace width. -/
theorem encoding_width (m interior : Nat) :
    (encoding m interior).width = m + (2 * wordBits interior + 2) := by
  simp [encoding, wordBits, literalR0Encoding_width]

/-- Canonical `n`-bit word occupied by a unit residue. -/
def unitWord (interior N : Nat) (_hNgtOne : 1 < N)
    (_hN : N < 2 ^ wordBits interior)
    (unit : (ZMod N)ˣ) : PlainAdder.Word (wordBits interior) :=
  ((unit : ZMod N).val : PlainAdder.Word (wordBits interior))

@[simp] theorem unitWord_val (interior N : Nat)
    (hNgtOne : 1 < N) (hN : N < 2 ^ wordBits interior)
    (unit : (ZMod N)ˣ) :
    (unitWord interior N hNgtOne hN unit).val = (unit : ZMod N).val := by
  let _ : NeZero N := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hNgtOne)⟩
  unfold unitWord
  exact ZMod.val_natCast_of_lt (lt_trans (ZMod.val_lt _) hN)

/-- The classical unit and its inverse instantiate the literal HRS
multiplier parameters without adding a trusted inverse witness. -/
def parameters (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    Parameters (wordBits interior) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hNgtOne)⟩
  exact {
  modulus := N
  modulus_pos := Nat.zero_lt_of_lt hNgtOne
  modulus_lt_width := hN
  constant := unitWord interior N hNgtOne hN unit
  constant_lt_modulus := by
    rw [unitWord_val]
    exact ZMod.val_lt _
  inverse := unitWord interior N hNgtOne hN unit⁻¹
  inverse_lt_modulus := by
    rw [unitWord_val]
    exact ZMod.val_lt _
  inverse_mul_constant := by
    have hunit :
        (((unit⁻¹ : (ZMod N)ˣ) : ZMod N) * (unit : ZMod N)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel]
      rfl
    have hcast :
        ((((unit⁻¹ : (ZMod N)ˣ) : ZMod N).val *
            (unit : ZMod N).val : Nat) : ZMod N) =
          ((1 : Nat) : ZMod N) := by
      push_cast
      simpa only [ZMod.natCast_zmod_val] using hunit
    have hmod :=
      (ZMod.natCast_eq_natCast_iff'
        (((unit⁻¹ : (ZMod N)ˣ) : ZMod N).val * (unit : ZMod N).val)
        1 N).mp hcast
    simpa only [unitWord_val, Nat.mod_eq_of_lt hNgtOne] using hmod
  }

@[simp] theorem parameters_word_zero {n : Nat} (params : Parameters n) :
    params.word 0 = 0 := by
  apply ZMod.val_injective
  rw [Parameters.word_val]
  simp

/-- Clean HRS workspace containing one unit and no garbage. -/
def cleanWorkspace (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (value : (ZMod N)ˣ) :
  Workspace interior :=
  (((unitWord interior N hNgtOne hN value,
      (0 : PlainAdder.Word (wordBits interior))),
    (false, 0)), false)

/-! ## One exponent-controlled literal multiplier -/

/-- Static unit selected at one little-endian exponent position. -/
def stageUnit {m N : Nat} (unit : (ZMod N)ˣ) (bit : Fin m) : (ZMod N)ˣ :=
  unit ^ (2 ^ bit.val)

/-- One exponent bit in the complete product encoding. -/
def exponentBit (m interior : Nat) (bit : Fin m) :
    EncodedBit (encoding m interior) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.finIdentity m) (workspaceEncoding interior)
    (BinaryLabelEncoding.finIdentityBit m
      (WireAddress.littleEndianWire bit))

/-- Reusable clean bit for controlling source Toffoli gates. -/
def controlWorkBit (m interior : Nat) : EncodedBit (encoding m interior) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.finIdentity m) (workspaceEncoding interior)
    (BinaryLabelEncoding.prodRightBit
      (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit)

@[simp] theorem exponentBit_get (m interior : Nat) (bit : Fin m)
    (state : Registers m interior) :
    (exponentBit m interior bit).get state =
      state.1.val.testBit bit.val := by
  change state.1.val.testBit
      (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

@[simp] theorem controlWorkBit_get (m interior : Nat)
    (state : Registers m interior) :
    (controlWorkBit m interior).get state = state.2.2 :=
  rfl

/-- Uncontrolled literal HRS multiplier gates lifted into the arithmetic core
of the exponentiation carrier. -/
def liftedMultiplierGates (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    List (EncodedBit.GateSpec (encoding m interior)) :=
  ((literalInPlaceGates interior
      (parameters interior N hNgtOne hN (stageUnit unit bit))).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodRight (BinaryLabelEncoding.finIdentity m))

/-- Lifting changes only wire addresses: the exponent and control-work fields
are preserved, while the HRS core executes the literal multiplier list. -/
theorem liftedMultiplierGates_stepList
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m)
    (state : Registers m interior) :
    EncodedBit.GateSpec.stepList
        (liftedMultiplierGates m interior N hNgtOne hN unit bit) state =
      (state.1,
        (literalInPlacePerm interior
          (parameters interior N hNgtOne hN (stageUnit unit bit)) state.2.1,
        state.2.2)) := by
  unfold liftedMultiplierGates
  rw [EncodedBit.GateSpec.stepList_prodRight,
    EncodedBit.GateSpec.stepList_prodLeft,
    literalInPlaceGates_stepList]

/-- The exponent control is disjoint from every lifted arithmetic gate. -/
theorem controlDisjoint
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ∀ gate, gate ∈ liftedMultiplierGates m interior N hNgtOne hN unit bit →
      EncodedBit.GateSpec.bitDisjoint (exponentBit m interior bit) gate := by
  intro gate hgate
  rw [liftedMultiplierGates] at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, _hinner, rfl⟩
  simpa [exponentBit, encoding, workspaceEncoding] using
    (EncodedBit.GateSpec.bitDisjoint_prodRight_leftBit
      (BinaryLabelEncoding.finIdentity m) (workspaceEncoding interior)
      (BinaryLabelEncoding.finIdentityBit m
        (WireAddress.littleEndianWire bit)) innerGate)

/-- The reusable clean control-work bit is disjoint from every lifted HRS
gate. -/
theorem workDisjoint
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ∀ gate, gate ∈ liftedMultiplierGates m interior N hNgtOne hN unit bit →
      EncodedBit.GateSpec.bitDisjoint (controlWorkBit m interior) gate := by
  intro gate hgate
  rw [liftedMultiplierGates] at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, hinner, rfl⟩
  rcases List.mem_map.mp hinner with ⟨sourceGate, _hsource, rfl⟩
  have hinnerDisjoint :=
    EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit
      (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit sourceGate
  have houterDisjoint :=
    EncodedBit.GateSpec.bitDisjoint_prodRight_of_bitDisjoint
      (BinaryLabelEncoding.finIdentity m)
      (BinaryLabelEncoding.prodRightBit
        (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit)
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool sourceGate)
      hinnerDisjoint
  simpa [controlWorkBit, encoding, workspaceEncoding] using houterDisjoint

/-- The exponent control and clean decomposition work wires are distinct. -/
theorem controlWork_ne (m interior : Nat) (bit : Fin m) :
    (exponentBit m interior bit).wire ≠ (controlWorkBit m interior).wire := by
  simpa [exponentBit, controlWorkBit, encoding, workspaceEncoding] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (BinaryLabelEncoding.finIdentity m) (workspaceEncoding interior)
      (BinaryLabelEncoding.prodRightBit
        (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit)
      (BinaryLabelEncoding.finIdentityBit m
        (WireAddress.littleEndianWire bit))).symm

/-! ### Constant-trace control blocks -/

/-! #### Width-only bound for one literal HRS multiplier -/

private theorem constantBitMultiplicity_le_one {width : Nat}
    (constant : PlainAdder.Word width) (bit : Nat) :
    MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant bit ≤ 1 := by
  unfold MAU.Addition.DirtyBorrowed.constantBitMultiplicity
  split <;> omega

private theorem carryCnotClosedForm_le {width : Nat}
    (constant : PlainAdder.Word width) : ∀ count : Nat,
    MAU.Addition.DirtyBorrowed.carryCnotClosedForm constant count ≤ count
  | 0 => by rfl
  | count + 1 => by
      rw [MAU.Addition.DirtyBorrowed.carryCnotClosedForm]
      have hrest := carryCnotClosedForm_le constant count
      have hbit := constantBitMultiplicity_le_one constant count
      omega

private theorem carryXClosedForm_le {width : Nat}
    (constant : PlainAdder.Word width) : ∀ count : Nat,
    MAU.Addition.DirtyBorrowed.carryXClosedForm constant count ≤ 2 * count
  | 0 => by rfl
  | count + 1 => by
      rw [MAU.Addition.DirtyBorrowed.carryXClosedForm]
      have hrest := carryXClosedForm_le constant count
      have hbit := constantBitMultiplicity_le_one constant (count + 1)
      omega

private theorem sourceControlledHighCnotClosedForm_le {width : Nat}
    (constant : PlainAdder.Word width) : ∀ count : Nat,
    sourceControlledHighCnotClosedForm constant count ≤
      count ^ 2 + 2 * count
  | 0 => by rfl
  | count + 1 => by
      rw [sourceControlledHighCnotClosedForm]
      have hcarry := carryCnotClosedForm_le constant (count + 1)
      have hbit := constantBitMultiplicity_le_one constant (count + 1)
      have hrest := sourceControlledHighCnotClosedForm_le constant count
      calc
        2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
                constant (count + 1) +
              MAU.Addition.DirtyBorrowed.constantBitMultiplicity
                constant (count + 1) +
            sourceControlledHighCnotClosedForm constant count ≤
            2 * (count + 1) + 1 + (count ^ 2 + 2 * count) :=
          Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul_left 2 hcarry) hbit) hrest
        _ = (count + 1) ^ 2 + 2 * (count + 1) := by ring

private theorem sourceControlledHighXClosedForm_le {width : Nat}
    (constant : PlainAdder.Word width) : ∀ count : Nat,
    sourceControlledHighXClosedForm constant count ≤ 2 * count ^ 2
  | 0 => by rfl
  | count + 1 => by
      rw [sourceControlledHighXClosedForm]
      have hcarry := carryXClosedForm_le constant count
      have hrest := sourceControlledHighXClosedForm_le constant count
      calc
        2 * MAU.Addition.DirtyBorrowed.carryXClosedForm constant count +
            sourceControlledHighXClosedForm constant count ≤
            2 * (2 * count) + 2 * count ^ 2 :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 hcarry) hrest
        _ ≤ 2 * (count + 1) ^ 2 := by nlinarith

private theorem selectedCarryToffoliClosedForm_le (interior : Nat)
    (constant : PlainAdder.Word (interior + 2).succ) :
    selectedCarryToffoliClosedForm interior constant ≤
      4 * (interior + 1) + 13 := by
  unfold selectedCarryToffoliClosedForm
  split <;> omega

private theorem selectedCarryCnotClosedForm_le (interior : Nat)
    (constant : PlainAdder.Word (interior + 2).succ) :
    selectedCarryCnotClosedForm interior constant ≤ 2 * (interior + 2) := by
  unfold selectedCarryCnotClosedForm
  exact Nat.mul_le_mul_left 2 (carryCnotClosedForm_le constant (interior + 2))

private theorem controlledAdderCnotClosedForm_le {width : Nat}
    (constant : PlainAdder.Word width) (tail : Nat) :
    controlledAdderCnotClosedForm constant tail ≤
      tail ^ 2 + 2 * tail + 1 := by
  unfold controlledAdderCnotClosedForm
  have hhigh := sourceControlledHighCnotClosedForm_le constant tail
  have hbit := constantBitMultiplicity_le_one constant 0
  omega

private theorem literalControlledModularAddXCount_le
    (interior modulus addend : Nat) :
    literalControlledModularAddXCount interior modulus addend ≤
      4 * (interior + 2) ^ 2 + 8 * (interior + 1) := by
  have hfirst := carryXClosedForm_le
    (overflowComparisonConstant (interior + 2).succ (modulus - addend))
    (interior + 1)
  have hsource := sourceControlledHighXClosedForm_le
    (addend : PlainAdder.Word (interior + 2).succ) (interior + 2)
  have hflag := sourceControlledHighXClosedForm_le
    (overflowComparisonConstant (interior + 2).succ modulus) (interior + 2)
  have hclear := carryXClosedForm_le
    (overflowComparisonConstant (interior + 2).succ addend) (interior + 1)
  unfold literalControlledModularAddXCount
  by_cases haddendZero : addend = 0
  · simp only [if_pos haddendZero, Nat.add_zero]
    nlinarith
  · rw [if_neg haddendZero]
    nlinarith

private theorem literalControlledModularAddCnotCount_le
    (interior modulus addend : Nat) :
    literalControlledModularAddCnotCount interior modulus addend ≤
      2 * (interior + 2) ^ 2 + 8 * (interior + 2) + 3 := by
  have hfirst := selectedCarryCnotClosedForm_le interior
    (overflowComparisonConstant (interior + 2).succ (modulus - addend))
  have hsource := controlledAdderCnotClosedForm_le
    (addend : PlainAdder.Word (interior + 2).succ) (interior + 2)
  have hflag := controlledAdderCnotClosedForm_le
    (overflowComparisonConstant (interior + 2).succ modulus) (interior + 2)
  have hclear := selectedCarryCnotClosedForm_le interior
    (overflowComparisonConstant (interior + 2).succ addend)
  unfold literalControlledModularAddCnotCount
  by_cases haddendZero : addend = 0
  · simp only [if_pos haddendZero, Nat.add_zero]
    omega
  · rw [if_neg haddendZero]
    omega

private theorem literalControlledModularAddToffoliCount_le
    (interior modulus addend : Nat) :
    literalControlledModularAddToffoliCount interior modulus addend ≤
      4 * (interior + 2) ^ 2 + 8 * (interior + 1) + 26 := by
  have hfirst := selectedCarryToffoliClosedForm_le interior
    (overflowComparisonConstant (interior + 2).succ (modulus - addend))
  have hclear := selectedCarryToffoliClosedForm_le interior
    (overflowComparisonConstant (interior + 2).succ addend)
  unfold literalControlledModularAddToffoliCount
  by_cases haddendZero : addend = 0
  · simp only [if_pos haddendZero, Nat.add_zero]
    nlinarith
  · rw [if_neg haddendZero]
    nlinarith

private theorem literalControlledModularAddGates_length_eq
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat) :
    (literalControlledModularAddGates interior pivot modulus addend).length =
      literalControlledModularAddXCount interior modulus addend +
        literalControlledModularAddCnotCount interior modulus addend +
        literalControlledModularAddToffoliCount interior modulus addend := by
  have hprimitive := EncodedBit.GateSpec.primitiveEventCount_programList
    (literalControlledModularAddGates interior pivot modulus addend)
  unfold EncodedBit.GateSpec.primitiveEventCount at hprimitive
  change
    ResourcePool.count (.gate (.builtin "x"))
          (literalControlledModularAddCircuit
            interior pivot modulus addend).eventCost +
        ResourcePool.count (.gate (.builtin "cnot"))
          (literalControlledModularAddCircuit
            interior pivot modulus addend).eventCost +
        ResourcePool.count (.gate (.builtin "toffoli"))
          (literalControlledModularAddCircuit
            interior pivot modulus addend).eventCost = _ at hprimitive
  rw [literalControlledModularAddCircuit_x_count_eq,
    literalControlledModularAddCircuit_cnot_count_eq,
    literalControlledModularAddCircuit_toffoli_count_eq] at hprimitive
  exact hprimitive.symm

/-- Every selected HRS modular-add source list has a quadratic bound in the
actual arithmetic word width. -/
theorem literalControlledModularAddGates_length_le
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat) :
    (literalControlledModularAddGates interior pivot modulus addend).length ≤
      24 * wordBits interior ^ 2 := by
  rw [literalControlledModularAddGates_length_eq]
  have hx := literalControlledModularAddXCount_le interior modulus addend
  have hc := literalControlledModularAddCnotCount_le interior modulus addend
  have ht := literalControlledModularAddToffoliCount_le interior modulus addend
  simp only [wordBits]
  nlinarith

private theorem literalSelectedGates_length_le
    (interior : Nat) (params : Parameters (wordBits interior))
    (subtract : Bool) : ∀ bits : List (Fin (wordBits interior)),
    (literalSelectedGates interior params subtract bits).length ≤
      bits.length * (24 * wordBits interior ^ 2)
  | [] => by simp [literalSelectedGates]
  | bit :: rest => by
      rw [literalSelectedGates, List.length_append]
      have hstage := literalControlledModularAddGates_length_le
        interior bit params.modulus (params.signedStageConstant subtract bit)
      have hrest := literalSelectedGates_length_le interior params subtract rest
      calc
        (literalControlledModularAddGates interior bit params.modulus
              (params.signedStageConstant subtract bit)).length +
            (literalSelectedGates interior params subtract rest).length ≤
            24 * wordBits interior ^ 2 +
              rest.length * (24 * wordBits interior ^ 2) :=
          Nat.add_le_add hstage hrest
        _ = (bit :: rest).length * (24 * wordBits interior ^ 2) := by
          simp only [List.length_cons]
          ring

/-- Width-only primitive bound for one complete literal HRS multiplier. -/
def multiplierPrimitiveBound (interior : Nat) : Nat :=
  48 * wordBits interior ^ 3 + 3 * wordBits interior

/-- The literal compute/swap/inverse-uncompute source list obeys the public
width-only cubic bound. -/
theorem literalInPlaceGates_length_le_multiplierPrimitiveBound
    (interior : Nat) (params : Parameters (wordBits interior)) :
    (literalInPlaceGates interior params).length ≤
      multiplierPrimitiveBound interior := by
  have hforward := literalSelectedGates_length_le interior params false
    (List.ofFn fun bit : Fin (wordBits interior) => bit)
  have hinverse := literalSelectedGates_length_le interior params true
    (List.ofFn fun bit : Fin (wordBits interior) => bit).reverse
  have hforward' :
      (literalSelectedGates interior params false
          (List.ofFn fun bit : Fin (wordBits interior) => bit)).length ≤
        wordBits interior * (24 * wordBits interior ^ 2) := by
    simpa using hforward
  have hinverse' :
      (literalSelectedGates interior params true
          (List.ofFn fun bit : Fin (wordBits interior) => bit).reverse).length ≤
        wordBits interior * (24 * wordBits interior ^ 2) := by
    simpa using hinverse
  have hswap : (literalSwapGates (wordBits interior)).length =
      3 * wordBits interior := by
    exact EncodedBit.Word.swapGates_length
      (literalSourceWord (wordBits interior))
      (literalTargetWord (wordBits interior))
      (literalSourceTargetBit_wire_ne (wordBits interior))
  unfold literalInPlaceGates multiplierPrimitiveBound
  simp only [List.length_append]
  rw [hswap]
  calc
    (literalSelectedGates interior params false
          (List.ofFn fun bit : Fin (wordBits interior) => bit)).length +
        3 * wordBits interior +
        (literalSelectedGates interior params true
          (List.ofFn fun bit : Fin (wordBits interior) => bit).reverse).length ≤
      wordBits interior * (24 * wordBits interior ^ 2) +
        3 * wordBits interior +
        wordBits interior * (24 * wordBits interior ^ 2) := by
          exact Nat.add_le_add (Nat.add_le_add hforward' le_rfl) hinverse'
    _ = 48 * wordBits interior ^ 3 + 3 * wordBits interior := by ring

/-- Maximum literal HRS source-list length over every unit of the fixed
modulus.  It depends only on public layout/modulus data, never on the sampled
runtime unit. -/
def sourceSlotBound (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) : Nat :=
  let _ : Fintype (ZMod N)ˣ := Fintype.ofFinite _
  Finset.univ.sup fun unit : (ZMod N)ˣ =>
    (literalInPlaceGates interior
      (parameters interior N hNgtOne hN unit)).length

/-- Every literal source schedule fits the public unit-independent slot
bound. -/
theorem literalInPlaceGates_length_le_sourceSlotBound
    (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    (literalInPlaceGates interior
        (parameters interior N hNgtOne hN unit)).length ≤
      sourceSlotBound interior N hNgtOne hN := by
  let _ : Fintype (ZMod N)ˣ := Fintype.ofFinite _
  exact Finset.le_sup (f := fun candidate : (ZMod N)ˣ =>
    (literalInPlaceGates interior
      (parameters interior N hNgtOne hN candidate)).length)
    (Finset.mem_univ unit)

/-- The unit-independent fixed-trace slot count is bounded solely by the HRS
word width. -/
theorem sourceSlotBound_le_multiplierPrimitiveBound
    (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) :
    sourceSlotBound interior N hNgtOne hN ≤ multiplierPrimitiveBound interior := by
  let _ : Fintype (ZMod N)ˣ := Fintype.ofFinite _
  unfold sourceSlotBound
  apply Finset.sup_le
  intro unit _hunit
  exact literalInPlaceGates_length_le_multiplierPrimitiveBound interior
    (parameters interior N hNgtOne hN unit)

/-- A fixed source-word wire reserved for semantically inactive padding
gates. -/
def dummySourceBit (m interior : Nat) : EncodedBit (encoding m interior) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.finIdentity m) (workspaceEncoding interior)
    (BinaryLabelEncoding.prodLeftBit
      (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
      (literalSourceBit (wordBits interior) 0))

/-- A distinct fixed target-word wire for inactive padding gates. -/
def dummyTargetBit (m interior : Nat) : EncodedBit (encoding m interior) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.finIdentity m) (workspaceEncoding interior)
    (BinaryLabelEncoding.prodLeftBit
      (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
      (literalTargetBit (wordBits interior) 0))

theorem controlWork_ne_dummySource (m interior : Nat) :
    (controlWorkBit m interior).wire ≠ (dummySourceBit m interior).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne
    (BinaryLabelEncoding.finIdentity m)
  exact EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit (literalSourceBit (wordBits interior) 0)

theorem controlWork_ne_dummyTarget (m interior : Nat) :
    (controlWorkBit m interior).wire ≠ (dummyTargetBit m interior).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne
    (BinaryLabelEncoding.finIdentity m)
  exact EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (literalR0Encoding (wordBits interior)) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit (literalTargetBit (wordBits interior) 0)

theorem dummySource_ne_dummyTarget (m interior : Nat) :
    (dummySourceBit m interior).wire ≠ (dummyTargetBit m interior).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne
    (BinaryLabelEncoding.finIdentity m)
  apply EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
  exact literalSourceTargetBit_wire_ne (wordBits interior) 0

/-- One inactive CNOT event.  Its control is the reusable work bit, so it is
the identity whenever that bit is clean. -/
def dummyCnot (m interior : Nat) :
    EncodedBit.GateSpec (encoding m interior) :=
  EncodedBit.GateSpec.cnot (controlWorkBit m interior)
    (dummySourceBit m interior) (controlWork_ne_dummySource m interior)

/-- One inactive Toffoli event controlled by the same clean work bit. -/
def dummyToffoli (m interior : Nat) :
    EncodedBit.GateSpec (encoding m interior) :=
  EncodedBit.GateSpec.toffoli (controlWorkBit m interior)
    (dummySourceBit m interior) (dummyTargetBit m interior)
    (controlWork_ne_dummySource m interior)
    (controlWork_ne_dummyTarget m interior)
    (dummySource_ne_dummyTarget m interior)

/-- The fixed inactive block has one CNOT and three Toffolis. -/
def dummyBlock (m interior : Nat) :
    List (EncodedBit.GateSpec (encoding m interior)) :=
  [dummyCnot m interior, dummyToffoli m interior,
    dummyToffoli m interior, dummyToffoli m interior]

theorem dummyCnot_step_eq_self (m interior : Nat)
    (state : Registers m interior) (hwork : state.2.2 = false) :
    (dummyCnot m interior).step state = state := by
  change EncodedBit.cnotStep (controlWorkBit m interior)
    (dummySourceBit m interior) state = state
  unfold EncodedBit.cnotStep
  rw [controlWorkBit_get, hwork]
  rfl

theorem dummyToffoli_step_eq_self (m interior : Nat)
    (state : Registers m interior) (hwork : state.2.2 = false) :
    (dummyToffoli m interior).step state = state := by
  change EncodedBit.toffoliStep (controlWorkBit m interior)
    (dummySourceBit m interior) (dummyTargetBit m interior) state = state
  unfold EncodedBit.toffoliStep
  rw [controlWorkBit_get, hwork]
  rfl

/-- A clean work bit makes the whole padding block a semantic no-op. -/
theorem dummyBlock_step_eq_self (m interior : Nat)
    (state : Registers m interior) (hwork : state.2.2 = false) :
    EncodedBit.GateSpec.stepList (dummyBlock m interior) state = state := by
  simp only [dummyBlock, EncodedBit.GateSpec.stepList]
  rw [dummyCnot_step_eq_self m interior state hwork,
    dummyToffoli_step_eq_self m interior state hwork,
    dummyToffoli_step_eq_self m interior state hwork,
    dummyToffoli_step_eq_self m interior state hwork]
  rfl

/-- Every inactive block exposes the same four strict event labels. -/
@[simp] theorem dummyBlock_events (m interior : Nat) :
    (dummyBlock m interior).map EncodedBit.GateSpec.event =
      [.gate (.builtin "cnot"), .gate (.builtin "toffoli"),
        .gate (.builtin "toffoli"), .gate (.builtin "toffoli")] := by
  rfl

/-- Inactive Toffoli suffix used to fill one fixed control block. -/
def dummyToffoliList (m interior count : Nat) :
    List (EncodedBit.GateSpec (encoding m interior)) :=
  List.replicate count (dummyToffoli m interior)

theorem dummyToffoliList_step_eq_self (m interior : Nat) :
    ∀ (count : Nat) (state : Registers m interior),
      state.2.2 = false →
      EncodedBit.GateSpec.stepList
          (dummyToffoliList m interior count) state = state
  | 0, _state, _hwork => rfl
  | count + 1, state, hwork => by
      rw [dummyToffoliList, List.replicate_succ,
        EncodedBit.GateSpec.stepList]
      change EncodedBit.GateSpec.stepList
        (List.replicate count (dummyToffoli m interior))
        ((dummyToffoli m interior).step state) = state
      rw [dummyToffoli_step_eq_self m interior state hwork]
      exact dummyToffoliList_step_eq_self m interior count state hwork

/-- A non-X source gate needs one inactive leading CNOT so every controlled
source slot begins with the same event coordinate. -/
def uniformPrefix (m interior : Nat) :
    EncodedBit.GateSpec (encoding m interior) →
      List (EncodedBit.GateSpec (encoding m interior))
  | .x _target => []
  | .cnot _control _target _hne => [dummyCnot m interior]
  | .toffoli _controlA _controlB _target _hab _ha _hb =>
      [dummyCnot m interior]

/-- Number of inactive trailing Toffolis needed after the standard clean-work
control expansion. -/
def uniformSuffixCount {Data : Type}
    {dataEncoding : BinaryLabelEncoding Data} :
    EncodedBit.GateSpec dataEncoding → Nat
  | .x _target => 3
  | .cnot _control _target _hne => 2
  | .toffoli _controlA _controlB _target _hab _ha _hb => 0

/-- Compile one source gate into the fixed event pattern
`CNOT, Toffoli, Toffoli, Toffoli`.  Inactive coordinates are genuine gates
whose clean-work control is false, so they are semantic no-ops on the clean
endpoint rather than detached resource metadata. -/
def uniformControlledGate (m interior : Nat) (bit : Fin m)
    (gate : EncodedBit.GateSpec (encoding m interior))
    (hcontrol : EncodedBit.GateSpec.bitDisjoint
      (exponentBit m interior bit) gate)
    (hwork : EncodedBit.GateSpec.bitDisjoint
      (controlWorkBit m interior) gate) :
    List (EncodedBit.GateSpec (encoding m interior)) :=
  (uniformPrefix m interior gate ++
    EncodedBit.GateSpec.controlledWithWorkGates
      (exponentBit m interior bit) (controlWorkBit m interior) gate
      hcontrol hwork (controlWork_ne m interior bit)) ++
    dummyToffoliList m interior (uniformSuffixCount gate)

theorem uniformPrefix_step_eq_self (m interior : Nat)
    (gate : EncodedBit.GateSpec (encoding m interior))
    (state : Registers m interior) (hwork : state.2.2 = false) :
    EncodedBit.GateSpec.stepList (uniformPrefix m interior gate) state =
      state := by
  cases gate <;>
    simp only [uniformPrefix, EncodedBit.GateSpec.stepList, id_eq]
  all_goals exact dummyCnot_step_eq_self m interior state hwork

/-- A fixed block is the identity when its exponent control is false. -/
theorem uniformControlledGate_step_eq_self_of_control_false
    (m interior : Nat) (bit : Fin m)
    (gate : EncodedBit.GateSpec (encoding m interior))
    (hcontrol : EncodedBit.GateSpec.bitDisjoint
      (exponentBit m interior bit) gate)
    (hworkDisjoint : EncodedBit.GateSpec.bitDisjoint
      (controlWorkBit m interior) gate)
    (state : Registers m interior)
    (hcontrolFalse : state.1.val.testBit bit.val = false)
    (hwork : state.2.2 = false) :
    EncodedBit.GateSpec.stepList
        (uniformControlledGate m interior bit gate hcontrol hworkDisjoint)
        state = state := by
  unfold uniformControlledGate
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    uniformPrefix_step_eq_self m interior gate state hwork]
  have hactive :=
    EncodedBit.GateSpec.controlledWithWorkStep_eq_self_of_control_false
      (exponentBit m interior bit) (controlWorkBit m interior) gate
      hcontrol hworkDisjoint (controlWork_ne m interior bit) state
      (by simpa using hcontrolFalse)
  change EncodedBit.GateSpec.stepList
    (dummyToffoliList m interior (uniformSuffixCount gate))
    (EncodedBit.GateSpec.controlledWithWorkStep
      (exponentBit m interior bit) (controlWorkBit m interior) gate
      hcontrol hworkDisjoint (controlWork_ne m interior bit) state) = state
  rw [hactive]
  exact dummyToffoliList_step_eq_self m interior
    (uniformSuffixCount gate) state hwork

/-- With a true exponent control and clean work, the same fixed block applies
its source gate and restores the clean work bit. -/
theorem uniformControlledGate_step_eq_gate_of_control_true
    (m interior : Nat) (bit : Fin m)
    (gate : EncodedBit.GateSpec (encoding m interior))
    (hcontrol : EncodedBit.GateSpec.bitDisjoint
      (exponentBit m interior bit) gate)
    (hworkDisjoint : EncodedBit.GateSpec.bitDisjoint
      (controlWorkBit m interior) gate)
    (state : Registers m interior)
    (hcontrolTrue : state.1.val.testBit bit.val = true)
    (hwork : state.2.2 = false) :
    EncodedBit.GateSpec.stepList
        (uniformControlledGate m interior bit gate hcontrol hworkDisjoint)
        state = gate.step state := by
  unfold uniformControlledGate
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    uniformPrefix_step_eq_self m interior gate state hwork]
  have hactive :=
    EncodedBit.GateSpec.controlledWithWorkStep_eq_step_of_control_true
      (exponentBit m interior bit) (controlWorkBit m interior) gate
      hcontrol hworkDisjoint (controlWork_ne m interior bit) state
      (by simpa using hcontrolTrue) (by simpa using hwork)
  change EncodedBit.GateSpec.stepList
    (dummyToffoliList m interior (uniformSuffixCount gate))
    (EncodedBit.GateSpec.controlledWithWorkStep
      (exponentBit m interior bit) (controlWorkBit m interior) gate
      hcontrol hworkDisjoint (controlWork_ne m interior bit) state) =
        gate.step state
  rw [hactive]
  have hworkAfterGet :
      (controlWorkBit m interior).get (gate.step state) = false := by
    rw [EncodedBit.GateSpec.step_get_of_bitDisjoint
      gate (controlWorkBit m interior) hworkDisjoint state]
    simpa using hwork
  have hworkAfter : (gate.step state).2.2 = false := by
    simpa using hworkAfterGet
  exact dummyToffoliList_step_eq_self m interior
    (uniformSuffixCount gate) (gate.step state) hworkAfter

/-- Every fixed block has the same ordered strict event trace. -/
theorem uniformControlledGate_events
    (m interior : Nat) (bit : Fin m)
    (gate : EncodedBit.GateSpec (encoding m interior))
    (hcontrol : EncodedBit.GateSpec.bitDisjoint
      (exponentBit m interior bit) gate)
    (hwork : EncodedBit.GateSpec.bitDisjoint
      (controlWorkBit m interior) gate) :
    (uniformControlledGate m interior bit gate hcontrol hwork).map
        EncodedBit.GateSpec.event =
      [.gate (.builtin "cnot"), .gate (.builtin "toffoli"),
        .gate (.builtin "toffoli"), .gate (.builtin "toffoli")] := by
  cases gate <;>
    simp [uniformControlledGate, uniformPrefix, uniformSuffixCount,
      dummyToffoliList, dummyCnot, dummyToffoli,
      EncodedBit.GateSpec.controlledWithWorkGates,
      EncodedBit.GateSpec.event]

/-- Public, wire-independent strict event block used by every normalized
source slot. -/
def uniformEventBlock : List (Resource.Event .quantum) :=
  [.gate (.builtin "cnot"), .gate (.builtin "toffoli"),
    .gate (.builtin "toffoli"), .gate (.builtin "toffoli")]

theorem uniformControlledGate_events_eq_block
    (m interior : Nat) (bit : Fin m)
    (gate : EncodedBit.GateSpec (encoding m interior))
    (hcontrol : EncodedBit.GateSpec.bitDisjoint
      (exponentBit m interior bit) gate)
    (hwork : EncodedBit.GateSpec.bitDisjoint
      (controlWorkBit m interior) gate) :
    (uniformControlledGate m interior bit gate hcontrol hwork).map
        EncodedBit.GateSpec.event = uniformEventBlock := by
  simpa [uniformEventBlock] using
    uniformControlledGate_events m interior bit gate hcontrol hwork

/-- Normalize a complete source list while retaining its exact clean-work
controlled action. -/
def uniformControlledList (m interior : Nat) (bit : Fin m) :
    (gates : List (EncodedBit.GateSpec (encoding m interior))) →
    (∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint
      (exponentBit m interior bit) gate) →
    (∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint
      (controlWorkBit m interior) gate) →
    List (EncodedBit.GateSpec (encoding m interior))
  | [], _hcontrol, _hwork => []
  | gate :: rest, hcontrol, hwork =>
      uniformControlledGate m interior bit gate
          (hcontrol gate (by simp)) (hwork gate (by simp)) ++
        uniformControlledList m interior bit rest
          (fun next hnext => hcontrol next (by simp [hnext]))
          (fun next hnext => hwork next (by simp [hnext]))

/-- With a false exponent control, a normalized source list is the identity
on a clean work bit. -/
theorem uniformControlledList_step_eq_self_of_control_false
    (m interior : Nat) (bit : Fin m) :
    ∀ (gates : List (EncodedBit.GateSpec (encoding m interior)))
      (hcontrol : ∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint
        (exponentBit m interior bit) gate)
      (hworkDisjoint : ∀ gate, gate ∈ gates →
        EncodedBit.GateSpec.bitDisjoint (controlWorkBit m interior) gate)
      (state : Registers m interior),
      state.1.val.testBit bit.val = false → state.2.2 = false →
      EncodedBit.GateSpec.stepList
        (uniformControlledList m interior bit gates hcontrol hworkDisjoint)
        state = state
  | [], _hcontrol, _hworkDisjoint, _state, _hcontrolFalse, _hwork => rfl
  | gate :: rest, hcontrol, hworkDisjoint, state, hcontrolFalse, hwork => by
      rw [uniformControlledList, EncodedBit.GateSpec.stepList_append,
        uniformControlledGate_step_eq_self_of_control_false
          m interior bit gate (hcontrol gate (by simp))
          (hworkDisjoint gate (by simp)) state hcontrolFalse hwork]
      exact uniformControlledList_step_eq_self_of_control_false
        m interior bit rest
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hworkDisjoint next (by simp [hnext]))
        state hcontrolFalse hwork

/-- With a true exponent control and clean work, a normalized source list has
the exact source-list action and restores the work bit after every slot. -/
theorem uniformControlledList_step_eq_stepList_of_control_true
    (m interior : Nat) (bit : Fin m) :
    ∀ (gates : List (EncodedBit.GateSpec (encoding m interior)))
      (hcontrol : ∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint
        (exponentBit m interior bit) gate)
      (hworkDisjoint : ∀ gate, gate ∈ gates →
        EncodedBit.GateSpec.bitDisjoint (controlWorkBit m interior) gate)
      (state : Registers m interior),
      state.1.val.testBit bit.val = true → state.2.2 = false →
      EncodedBit.GateSpec.stepList
        (uniformControlledList m interior bit gates hcontrol hworkDisjoint)
        state = EncodedBit.GateSpec.stepList gates state
  | [], _hcontrol, _hworkDisjoint, _state, _hcontrolTrue, _hwork => rfl
  | gate :: rest, hcontrol, hworkDisjoint, state, hcontrolTrue, hwork => by
      rw [uniformControlledList, EncodedBit.GateSpec.stepList_append,
        uniformControlledGate_step_eq_gate_of_control_true
          m interior bit gate (hcontrol gate (by simp))
          (hworkDisjoint gate (by simp)) state hcontrolTrue hwork]
      have hcontrolAfterGet :
          (exponentBit m interior bit).get (gate.step state) = true := by
        rw [EncodedBit.GateSpec.step_get_of_bitDisjoint gate
          (exponentBit m interior bit) (hcontrol gate (by simp)) state]
        simpa using hcontrolTrue
      have hcontrolAfter :
          (gate.step state).1.val.testBit bit.val = true := by
        simpa using hcontrolAfterGet
      have hworkAfterGet :
          (controlWorkBit m interior).get (gate.step state) = false := by
        rw [EncodedBit.GateSpec.step_get_of_bitDisjoint gate
          (controlWorkBit m interior) (hworkDisjoint gate (by simp)) state]
        simpa using hwork
      have hworkAfter : (gate.step state).2.2 = false := by
        simpa using hworkAfterGet
      exact uniformControlledList_step_eq_stepList_of_control_true
        m interior bit rest
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hworkDisjoint next (by simp [hnext]))
        (gate.step state) hcontrolAfter hworkAfter

/-- A normalized source list is a repetition of the fixed event block. -/
theorem uniformControlledList_events
    (m interior : Nat) (bit : Fin m) :
    ∀ (gates : List (EncodedBit.GateSpec (encoding m interior)))
      (hcontrol : ∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint
        (exponentBit m interior bit) gate)
      (hwork : ∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint
        (controlWorkBit m interior) gate),
      (uniformControlledList m interior bit gates hcontrol hwork).map
          EncodedBit.GateSpec.event =
        (List.replicate gates.length uniformEventBlock).flatten
  | [], _hcontrol, _hwork => rfl
  | gate :: rest, hcontrol, hwork => by
      rw [uniformControlledList, List.map_append,
        uniformControlledGate_events_eq_block]
      rw [uniformControlledList_events m interior bit rest
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))]
      rfl

/-- A requested number of semantically inactive fixed event blocks. -/
def dummyBlocks (m interior count : Nat) :
    List (EncodedBit.GateSpec (encoding m interior)) :=
  (List.replicate count (dummyBlock m interior)).flatten

theorem dummyBlocks_step_eq_self (m interior : Nat) :
    ∀ (count : Nat) (state : Registers m interior), state.2.2 = false →
      EncodedBit.GateSpec.stepList (dummyBlocks m interior count) state = state
  | 0, _state, _hwork => rfl
  | count + 1, state, hwork => by
      rw [dummyBlocks, List.replicate_succ, List.flatten_cons,
        EncodedBit.GateSpec.stepList_append,
        dummyBlock_step_eq_self m interior state hwork]
      exact dummyBlocks_step_eq_self m interior count state hwork

/-- Padding blocks expose exactly the same repeated strict trace. -/
theorem dummyBlocks_events (m interior : Nat) :
    ∀ count : Nat,
      (dummyBlocks m interior count).map EncodedBit.GateSpec.event =
        (List.replicate count uniformEventBlock).flatten
  | 0 => rfl
  | count + 1 => by
      rw [dummyBlocks, List.replicate_succ, List.flatten_cons,
        List.map_append, dummyBlock_events]
      change uniformEventBlock ++
        (dummyBlocks m interior count).map EncodedBit.GateSpec.event =
          uniformEventBlock ++
            (List.replicate count uniformEventBlock).flatten
      rw [dummyBlocks_events m interior count]

/-- Register lifting does not change the number of literal source gates. -/
theorem liftedMultiplierGates_length_le_sourceSlotBound
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    (liftedMultiplierGates m interior N hNgtOne hN unit bit).length ≤
      sourceSlotBound interior N hNgtOne hN := by
  simpa [liftedMultiplierGates] using
    literalInPlaceGates_length_le_sourceSlotBound
      interior N hNgtOne hN (stageUnit unit bit)

/-- Unit-independent fixed-trace gate list for one exponent-controlled HRS
multiplier.  Every literal source gate occupies one normalized slot and the
remaining public slots are filled by clean-work no-op blocks. -/
def uniformStageGates (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    List (EncodedBit.GateSpec (encoding m interior)) :=
  uniformControlledList m interior bit
      (liftedMultiplierGates m interior N hNgtOne hN unit bit)
      (controlDisjoint m interior N hNgtOne hN unit bit)
      (workDisjoint m interior N hNgtOne hN unit bit) ++
    dummyBlocks m interior
      (sourceSlotBound interior N hNgtOne hN -
        (liftedMultiplierGates m interior N hNgtOne hN unit bit).length)

/-- Fixed-trace circuit for one exponent-controlled HRS multiplier. -/
def uniformStageProgram (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit (Qubits (encoding m interior).width) :=
  EncodedBit.GateSpec.programList
    (uniformStageGates m interior N hNgtOne hN unit bit)

/-- Total basis action of the fixed-trace stage. -/
def uniformStageStep (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    Registers m interior → Registers m interior :=
  EncodedBit.GateSpec.stepList
    (uniformStageGates m interior N hNgtOne hN unit bit)

/-- The fixed-trace list realizes its total basis permutation. -/
theorem uniformStageProgram_realizes
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit.Realizes (encoding m interior)
      (uniformStageProgram m interior N hNgtOne hN unit bit)
      (uniformStageStep m interior N hNgtOne hN unit bit) := by
  exact EncodedBit.GateSpec.witnessList
    (uniformStageGates m interior N hNgtOne hN unit bit)

/-- Every normalized stage gate stays inside its encoded register. -/
theorem uniformStageProgram_physical_idx_subset_range
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    (uniformStageProgram m interior N hNgtOne hN unit bit).physical_idx ⊆
      List.range (encoding m interior).width := by
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The complete normalized stage has a public, unit-independent strict event
trace. -/
theorem uniformStageGates_events
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    (uniformStageGates m interior N hNgtOne hN unit bit).map
        EncodedBit.GateSpec.event =
      (List.replicate (sourceSlotBound interior N hNgtOne hN)
        uniformEventBlock).flatten := by
  unfold uniformStageGates
  rw [List.map_append, uniformControlledList_events,
    dummyBlocks_events]
  rw [← List.flatten_append, ← List.replicate_add]
  rw [Nat.add_sub_of_le
    (liftedMultiplierGates_length_le_sourceSlotBound
      m interior N hNgtOne hN unit bit)]

theorem uniformEventBlock_toffoli_count : ∀ slots : Nat,
    List.count (.gate (.builtin "toffoli"))
        (List.replicate slots uniformEventBlock).flatten = 3 * slots
  | 0 => rfl
  | slots + 1 => by
      rw [List.replicate_succ, List.flatten_cons, List.count_append,
        uniformEventBlock_toffoli_count slots]
      have hblock :
          List.count (.gate (.builtin "toffoli")) uniformEventBlock = 3 := by
        decide
      rw [hblock]
      omega

theorem uniformEventBlock_cnot_count : ∀ slots : Nat,
    List.count (.gate (.builtin "cnot"))
        (List.replicate slots uniformEventBlock).flatten = slots
  | 0 => rfl
  | slots + 1 => by
      rw [List.replicate_succ, List.flatten_cons, List.count_append,
        uniformEventBlock_cnot_count slots]
      have hblock :
          List.count (.gate (.builtin "cnot")) uniformEventBlock = 1 := by
        decide
      rw [hblock]
      omega

theorem uniformEventBlock_x_count : ∀ slots : Nat,
    List.count (.gate (.builtin "x"))
        (List.replicate slots uniformEventBlock).flatten = 0
  | 0 => rfl
  | slots + 1 => by
      rw [List.replicate_succ, List.flatten_cons, List.count_append,
        uniformEventBlock_x_count slots]
      have hblock :
          List.count (.gate (.builtin "x")) uniformEventBlock = 0 := by
        decide
      rw [hblock]

theorem uniformEventBlock_other_count
    (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") : ∀ slots : Nat,
    List.count (.gate label)
        (List.replicate slots uniformEventBlock).flatten = 0
  | 0 => rfl
  | slots + 1 => by
      rw [List.replicate_succ, List.flatten_cons, List.count_append,
        uniformEventBlock_other_count label hcnot htoffoli slots]
      have hcnotEvent :
          (.gate (.builtin "cnot") : Resource.Event .quantum) ≠
            .gate label := by
        intro equality
        exact hcnot (Resource.Event.gate.inj equality).symm
      have htoffoliEvent :
          (.gate (.builtin "toffoli") : Resource.Event .quantum) ≠
            .gate label := by
        intro equality
        exact htoffoli (Resource.Event.gate.inj equality).symm
      have hblock : List.count (.gate label) uniformEventBlock = 0 := by
        simp [uniformEventBlock, hcnotEvent, htoffoliEvent]
      rw [hblock]

/-- Every runtime unit and exponent wire has exactly the same stage event
pool. -/
theorem uniformStageProgram_eventCost_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior)
    (left right : (ZMod N)ˣ) (leftBit rightBit : Fin m) :
    (uniformStageProgram m interior N hNgtOne hN left leftBit).eventCost =
      (uniformStageProgram m interior N hNgtOne hN right rightBit).eventCost := by
  unfold uniformStageProgram
  apply EncodedBit.GateSpec.programList_eventCost_eq_of_events_eq
  rw [uniformStageGates_events, uniformStageGates_events]

/-- Every runtime unit and exponent wire has exactly the same stage event
path. -/
theorem uniformStageProgram_eventDepth_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior)
    (left right : (ZMod N)ˣ) (leftBit rightBit : Fin m) :
    (uniformStageProgram m interior N hNgtOne hN left leftBit).eventDepth =
      (uniformStageProgram m interior N hNgtOne hN right rightBit).eventDepth := by
  unfold uniformStageProgram
  apply EncodedBit.GateSpec.programList_eventDepth_eq_of_events_eq
  rw [uniformStageGates_events, uniformStageGates_events]

/-- Exact primitive-leaf cardinality of one fixed-trace controlled
multiplier. -/
theorem uniformStageProgram_eventCost_card_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    (uniformStageProgram m interior N hNgtOne hN unit bit).eventCost.card =
      4 * sourceSlotBound interior N hNgtOne hN := by
  rw [uniformStageProgram, EncodedBit.GateSpec.programList_eventCost,
    uniformStageGates_events]
  simp [uniformEventBlock, ResourcePool.ofList]
  omega

/-- Exact fixed-trace Toffoli coordinate for one controlled multiplier. -/
theorem uniformStageProgram_toffoli_count_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (uniformStageProgram m interior N hNgtOne hN unit bit).eventCost =
      3 * sourceSlotBound interior N hNgtOne hN := by
  rw [uniformStageProgram, EncodedBit.GateSpec.programList_eventCost,
    ResourcePool.count_ofList, uniformStageGates_events]
  exact uniformEventBlock_toffoli_count
    (sourceSlotBound interior N hNgtOne hN)

/-- Exact fixed-trace CNOT coordinate for one controlled multiplier. -/
theorem uniformStageProgram_cnot_count_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (uniformStageProgram m interior N hNgtOne hN unit bit).eventCost =
      sourceSlotBound interior N hNgtOne hN := by
  rw [uniformStageProgram, EncodedBit.GateSpec.programList_eventCost,
    ResourcePool.count_ofList, uniformStageGates_events]
  exact uniformEventBlock_cnot_count
    (sourceSlotBound interior N hNgtOne hN)

/-- Fixed-trace control uses no physical X leaves. -/
@[simp] theorem uniformStageProgram_x_count_eq_zero
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "x"))
        (uniformStageProgram m interior N hNgtOne hN unit bit).eventCost = 0 := by
  rw [uniformStageProgram, EncodedBit.GateSpec.programList_eventCost,
    ResourcePool.count_ofList, uniformStageGates_events]
  exact uniformEventBlock_x_count
    (sourceSlotBound interior N hNgtOne hN)

/-- No strict gate outside CNOT/Toffoli occurs in a normalized stage. -/
theorem uniformStageProgram_gate_count_zero_of_ne
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m)
    (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label)
        (uniformStageProgram m interior N hNgtOne hN unit bit).eventCost = 0 := by
  rw [uniformStageProgram, EncodedBit.GateSpec.programList_eventCost,
    ResourcePool.count_ofList, uniformStageGates_events]
  exact uniformEventBlock_other_count label hcnot htoffoli
    (sourceSlotBound interior N hNgtOne hN)

/-- A clean fixed-trace stage has the same action as the compact mechanical
control expansion. -/
theorem uniformStageStep_eq_compact_of_clean_work
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m)
    (state : Registers m interior) (hwork : state.2.2 = false) :
    uniformStageStep m interior N hNgtOne hN unit bit state =
      EncodedBit.GateSpec.controlledListWithWorkStep
        (exponentBit m interior bit) (controlWorkBit m interior)
        (liftedMultiplierGates m interior N hNgtOne hN unit bit)
        (controlDisjoint m interior N hNgtOne hN unit bit)
        (workDisjoint m interior N hNgtOne hN unit bit)
        (controlWork_ne m interior bit) state := by
  by_cases hcontrol : state.1.val.testBit bit.val
  · have htrue : state.1.val.testBit bit.val = true := hcontrol
    unfold uniformStageStep uniformStageGates
    rw [EncodedBit.GateSpec.stepList_append,
      uniformControlledList_step_eq_stepList_of_control_true
        m interior bit
        (liftedMultiplierGates m interior N hNgtOne hN unit bit)
        (controlDisjoint m interior N hNgtOne hN unit bit)
        (workDisjoint m interior N hNgtOne hN unit bit)
        state htrue hwork]
    have hworkAfterGet :
        (controlWorkBit m interior).get
          (EncodedBit.GateSpec.stepList
            (liftedMultiplierGates m interior N hNgtOne hN unit bit)
            state) = false := by
      rw [stepList_get_of_forall_bitDisjoint
        (liftedMultiplierGates m interior N hNgtOne hN unit bit)
        (controlWorkBit m interior)
        (workDisjoint m interior N hNgtOne hN unit bit) state]
      simpa using hwork
    have hworkAfter :
        (EncodedBit.GateSpec.stepList
          (liftedMultiplierGates m interior N hNgtOne hN unit bit)
          state).2.2 = false := by
      simpa using hworkAfterGet
    rw [dummyBlocks_step_eq_self m interior _ _ hworkAfter]
    exact (EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
        (exponentBit m interior bit) (controlWorkBit m interior)
        (liftedMultiplierGates m interior N hNgtOne hN unit bit)
        (controlDisjoint m interior N hNgtOne hN unit bit)
        (workDisjoint m interior N hNgtOne hN unit bit)
        (controlWork_ne m interior bit) state (by simpa using htrue)
        (by simpa using hwork)).symm
  · have hfalse : state.1.val.testBit bit.val = false :=
      Bool.eq_false_of_not_eq_true hcontrol
    unfold uniformStageStep uniformStageGates
    rw [EncodedBit.GateSpec.stepList_append,
      uniformControlledList_step_eq_self_of_control_false
        m interior bit
        (liftedMultiplierGates m interior N hNgtOne hN unit bit)
        (controlDisjoint m interior N hNgtOne hN unit bit)
        (workDisjoint m interior N hNgtOne hN unit bit)
        state hfalse hwork,
      dummyBlocks_step_eq_self m interior _ state hwork]
    exact (EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        (exponentBit m interior bit) (controlWorkBit m interior)
        (liftedMultiplierGates m interior N hNgtOne hN unit bit)
        (controlDisjoint m interior N hNgtOne hN unit bit)
        (workDisjoint m interior N hNgtOne hN unit bit)
        (controlWork_ne m interior bit) state (by simpa using hfalse)).symm

/-- Actual X/CNOT/Toffoli list for one exponent-controlled HRS multiplier. -/
def stageGates (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    List (EncodedBit.GateSpec (encoding m interior)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (exponentBit m interior bit) (controlWorkBit m interior)
    (liftedMultiplierGates m interior N hNgtOne hN unit bit)
    (controlDisjoint m interior N hNgtOne hN unit bit)
    (workDisjoint m interior N hNgtOne hN unit bit)
    (controlWork_ne m interior bit)

/-- Actual circuit for one exponent-controlled HRS multiplier. -/
def stageProgram (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit (Qubits (encoding m interior).width) :=
  EncodedBit.GateSpec.programList
    (stageGates m interior N hNgtOne hN unit bit)

/-- Total basis action of the same mechanically controlled gate list. -/
def stageStep (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    Registers m interior → Registers m interior :=
  EncodedBit.GateSpec.controlledListWithWorkStep
    (exponentBit m interior bit) (controlWorkBit m interior)
    (liftedMultiplierGates m interior N hNgtOne hN unit bit)
    (controlDisjoint m interior N hNgtOne hN unit bit)
    (workDisjoint m interior N hNgtOne hN unit bit)
    (controlWork_ne m interior bit)

/-- On the clean endpoint, the fixed-trace and compact stage definitions have
the same basis action. -/
theorem uniformStageStep_eq_stageStep_of_clean_work
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m)
    (state : Registers m interior) (hwork : state.2.2 = false) :
    uniformStageStep m interior N hNgtOne hN unit bit state =
      stageStep m interior N hNgtOne hN unit bit state := by
  exact uniformStageStep_eq_compact_of_clean_work
    m interior N hNgtOne hN unit bit state hwork

/-- The compiled controlled list realizes its total basis permutation. -/
theorem stageProgram_realizes
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit.Realizes (encoding m interior)
      (stageProgram m interior N hNgtOne hN unit bit)
      (stageStep m interior N hNgtOne hN unit bit) :=
  EncodedBit.GateSpec.controlledListWithWorkWitness
    (exponentBit m interior bit) (controlWorkBit m interior)
    (liftedMultiplierGates m interior N hNgtOne hN unit bit)
    (controlDisjoint m interior N hNgtOne hN unit bit)
    (workDisjoint m interior N hNgtOne hN unit bit)
    (controlWork_ne m interior bit)

/-- Register lifting preserves the complete strict source event schedule. -/
theorem liftedMultiplierGates_events_eq_source
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    (liftedMultiplierGates m interior N hNgtOne hN unit bit).map
        EncodedBit.GateSpec.event =
      (literalInPlaceGates interior
        (parameters interior N hNgtOne hN (stageUnit unit bit))).map
          EncodedBit.GateSpec.event := by
  unfold liftedMultiplierGates
  rw [EncodedBit.GateSpec.map_event_prodRight,
    EncodedBit.GateSpec.map_event_prodLeft]

/-- Exact source CNOT coordinate used by the mechanical control expansion. -/
def sourceCnotCount (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) : Nat :=
  ((literalInPlaceGates interior
      (parameters interior N hNgtOne hN unit)).map
    EncodedBit.GateSpec.cnotMultiplicity).sum

/-- Exact source Toffoli coordinate used by the mechanical control expansion. -/
def sourceToffoliCount (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) : Nat :=
  ((literalInPlaceGates interior
      (parameters interior N hNgtOne hN unit)).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum

/-- Exact source X coordinate; these gates become physical CNOTs. -/
def sourceXCount (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) : Nat :=
  ((literalInPlaceGates interior
      (parameters interior N hNgtOne hN unit)).map
    EncodedBit.GateSpec.xMultiplicity).sum

/-- Exact Toffoli equality for one controlled HRS multiplier. -/
theorem stageProgram_toffoli_count_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (stageProgram m interior N hNgtOne hN unit bit).eventCost =
      sourceCnotCount interior N hNgtOne hN (stageUnit unit bit) +
        3 * sourceToffoliCount interior N hNgtOne hN (stageUnit unit bit) := by
  rw [stageProgram, EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  unfold stageGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum]
  have hc := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    (liftedMultiplierGates_events_eq_source
      m interior N hNgtOne hN unit bit)
  have ht := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    (liftedMultiplierGates_events_eq_source
      m interior N hNgtOne hN unit bit)
  simpa [sourceCnotCount, sourceToffoliCount] using congrArg₂ (· + ·)
    hc (congrArg (fun value => 3 * value) ht)

/-- Exact CNOT equality for one controlled HRS multiplier. -/
theorem stageProgram_cnot_count_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (stageProgram m interior N hNgtOne hN unit bit).eventCost =
      sourceXCount interior N hNgtOne hN (stageUnit unit bit) := by
  rw [stageProgram, EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  unfold stageGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum]
  exact EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    (liftedMultiplierGates_events_eq_source
      m interior N hNgtOne hN unit bit)

/-- Mechanical control removes every physical X leaf. -/
@[simp] theorem stageProgram_x_count_eq_zero
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "x"))
        (stageProgram m interior N hNgtOne hN unit bit).eventCost = 0 := by
  rw [stageProgram, EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum
    (exponentBit m interior bit) (controlWorkBit m interior)
    (liftedMultiplierGates m interior N hNgtOne hN unit bit)
    (controlDisjoint m interior N hNgtOne hN unit bit)
    (workDisjoint m interior N hNgtOne hN unit bit)
    (controlWork_ne m interior bit)

/-! ## Clean computational-basis endpoint -/

/-- One controlled stage is the identity when its exponent bit is false. -/
theorem stageStep_eq_self_of_control_false
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m)
    (state : Registers m interior)
    (hcontrol : state.1.val.testBit bit.val = false) :
    stageStep m interior N hNgtOne hN unit bit state = state := by
  exact EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
    (exponentBit m interior bit) (controlWorkBit m interior)
    (liftedMultiplierGates m interior N hNgtOne hN unit bit)
    (controlDisjoint m interior N hNgtOne hN unit bit)
    (workDisjoint m interior N hNgtOne hN unit bit)
    (controlWork_ne m interior bit) state (by simpa using hcontrol)

/-- With a true exponent control and clean decomposition bit, the controlled
stage executes the literal HRS multiplier and restores the decomposition bit. -/
theorem stageStep_eq_lifted_of_control_true
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) (bit : Fin m)
    (state : Registers m interior)
    (hcontrol : state.1.val.testBit bit.val = true)
    (hwork : state.2.2 = false) :
    stageStep m interior N hNgtOne hN unit bit state =
      (state.1,
        (literalInPlacePerm interior
          (parameters interior N hNgtOne hN (stageUnit unit bit)) state.2.1,
        state.2.2)) := by
  rw [stageStep,
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (exponentBit m interior bit) (controlWorkBit m interior)
      (liftedMultiplierGates m interior N hNgtOne hN unit bit)
      (controlDisjoint m interior N hNgtOne hN unit bit)
      (workDisjoint m interior N hNgtOne hN unit bit)
      (controlWork_ne m interior bit) state (by simpa using hcontrol)
      (by simpa using hwork)]
  exact liftedMultiplierGates_stepList
    m interior N hNgtOne hN unit bit state

/-- The HRS reduced product word is exactly the canonical word of the product
unit. -/
theorem parameters_word_mul_unit
    (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (left right : (ZMod N)ˣ) :
    (parameters interior N hNgtOne hN left).word
        ((unitWord interior N hNgtOne hN left).val *
          (unitWord interior N hNgtOne hN right).val) =
      unitWord interior N hNgtOne hN (left * right) := by
  apply ZMod.val_injective
  rw [Parameters.word_val, unitWord_val, unitWord_val, unitWord_val]
  change (left : ZMod N).val * (right : ZMod N).val % N =
    ((left * right : (ZMod N)ˣ) : ZMod N).val
  exact (ZMod.val_mul (left : ZMod N) (right : ZMod N)).symm

/-- Unit selected by one exponent bit. -/
def selectedUnit {m N : Nat} (unit : (ZMod N)ˣ)
    (exponent : Fin (2 ^ m)) (bit : Fin m) : (ZMod N)ˣ :=
  if exponent.val.testBit bit.val then stageUnit unit bit else 1

/-- Clean endpoint of one actual exponent-controlled HRS multiplier. -/
theorem stageStep_cleanWorkspace
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit value : (ZMod N)ˣ)
    (bit : Fin m) (exponent : Fin (2 ^ m)) :
    stageStep m interior N hNgtOne hN unit bit
        (exponent, cleanWorkspace interior N hNgtOne hN value) =
      (exponent, cleanWorkspace interior N hNgtOne hN
        (selectedUnit unit exponent bit * value)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hNgtOne)⟩
  by_cases hcontrol : exponent.val.testBit bit.val
  · have htrue : exponent.val.testBit bit.val = true := hcontrol
    rw [stageStep_eq_lifted_of_control_true
      m interior N hNgtOne hN unit bit _ htrue rfl]
    have hsource :
        (unitWord interior N hNgtOne hN value).val < N := by
      rw [unitWord_val]
      exact ZMod.val_lt _
    have hendpoint := inPlacePerm_clean_endpoint
      (parameters interior N hNgtOne hN (stageUnit unit bit))
      (LiteralBorrowed (wordBits interior))
      (literalForwardAdd interior
        (parameters interior N hNgtOne hN (stageUnit unit bit)))
      (literalWordSwap (wordBits interior))
      (literalInverseAdd interior
        (parameters interior N hNgtOne hN (stageUnit unit bit)))
      (unitWord interior N hNgtOne hN value) 0 hsource
    simp only [parameters_word_zero] at hendpoint
    simp only [cleanWorkspace]
    unfold literalInPlacePerm
    rw [hendpoint]
    unfold selectedUnit
    rw [if_pos hcontrol]
    congr 4
    exact parameters_word_mul_unit interior N hNgtOne hN
      (stageUnit unit bit) value
  · have hfalse : exponent.val.testBit bit.val = false :=
      Bool.eq_false_of_not_eq_true hcontrol
    rw [stageStep_eq_self_of_control_false
      m interior N hNgtOne hN unit bit _ hfalse]
    simp [selectedUnit, hcontrol]

/-- The fixed-trace stage has the same clean multiplication endpoint. -/
theorem uniformStageStep_cleanWorkspace
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit value : (ZMod N)ˣ)
    (bit : Fin m) (exponent : Fin (2 ^ m)) :
    uniformStageStep m interior N hNgtOne hN unit bit
        (exponent, cleanWorkspace interior N hNgtOne hN value) =
      (exponent, cleanWorkspace interior N hNgtOne hN
        (selectedUnit unit exponent bit * value)) := by
  rw [uniformStageStep_eq_stageStep_of_clean_work
    m interior N hNgtOne hN unit bit _ rfl]
  exact stageStep_cleanWorkspace
    m interior N hNgtOne hN unit value bit exponent

/-! ## Complete exponentiation fold -/

/-- Product of the static powers selected by one list of exponent wires. -/
def scheduledUnit {m N : Nat} (unit : (ZMod N)ˣ) (exponent : Nat)
    (bits : List (Fin m)) : (ZMod N)ˣ :=
  (bits.map (selectedUnit unit ⟨exponent % 2 ^ m,
    Nat.mod_lt _ (Nat.two_pow_pos m)⟩)).prod

/-- Concatenate fixed-trace controlled HRS multiplier stages in execution
order. -/
def programForBits (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    List (Fin m) → UnitaryCircuit (Qubits (encoding m interior).width)
  | [] => UnitaryCircuit.identity (Qubits (encoding m interior).width) [] (by simp)
  | bit :: rest =>
      UnitaryCircuit.seq (uniformStageProgram m interior N hNgtOne hN unit bit)
        (programForBits m interior N hNgtOne hN unit rest)

/-- Total basis-state fold aligned with `programForBits`. -/
def programForBitsStep (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    List (Fin m) → Registers m interior → Registers m interior
  | [] => id
  | bit :: rest => fun state =>
      programForBitsStep m interior N hNgtOne hN unit rest
        (uniformStageStep m interior N hNgtOne hN unit bit state)

/-- Every fixed selected-bit schedule stays inside the canonical HRS
exponentiation register. -/
theorem programForBits_physical_idx_subset_range
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m interior N hNgtOne hN unit bits).physical_idx ⊆
        List.range (encoding m interior).width
  | [] => by
      intro index hindex
      simp [programForBits, UnitaryCircuit.identity] at hindex
  | bit :: rest => by
      intro index hindex
      change index ∈ UnitaryCircuit.unionPhysicalIdx
        (uniformStageProgram m interior N hNgtOne hN unit bit).physical_idx
        (programForBits m interior N hNgtOne hN unit rest).physical_idx at hindex
      rcases List.mem_union_iff.mp hindex with hstage | hrest
      · exact uniformStageProgram_physical_idx_subset_range
          m interior N hNgtOne hN unit bit hstage
      · exact programForBits_physical_idx_subset_range
          m interior N hNgtOne hN unit rest hrest

/-- Every selected-bit schedule is realized by its fixed-trace composed
circuit. -/
theorem programForBits_realizes
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      UnitaryCircuit.Realizes (encoding m interior)
        (programForBits m interior N hNgtOne hN unit bits)
        (programForBitsStep m interior N hNgtOne hN unit bits)
  | [] => UnitaryCircuit.Realizes.identity (encoding m interior)
  | bit :: rest =>
      UnitaryCircuit.Realizes.seq
        (firstStep := uniformStageStep m interior N hNgtOne hN unit bit)
        (secondStep := programForBitsStep
          m interior N hNgtOne hN unit rest)
        (uniformStageProgram_realizes m interior N hNgtOne hN unit bit)
        (programForBits_realizes m interior N hNgtOne hN unit rest)

/-- A fixed exponent-bit schedule has an exact event pool independent of the
runtime base unit. -/
theorem programForBits_eventCost_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (left right : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m interior N hNgtOne hN left bits).eventCost =
        (programForBits m interior N hNgtOne hN right bits).eventCost
  | [] => rfl
  | bit :: rest => by
      change
        (uniformStageProgram m interior N hNgtOne hN left bit).eventCost +
            (programForBits m interior N hNgtOne hN left rest).eventCost =
          (uniformStageProgram m interior N hNgtOne hN right bit).eventCost +
            (programForBits m interior N hNgtOne hN right rest).eventCost
      rw [uniformStageProgram_eventCost_eq,
        programForBits_eventCost_eq]

/-- A fixed exponent-bit schedule has an exact event path independent of the
runtime base unit. -/
theorem programForBits_eventDepth_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (left right : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m interior N hNgtOne hN left bits).eventDepth =
        (programForBits m interior N hNgtOne hN right bits).eventDepth
  | [] => rfl
  | bit :: rest => by
      change
        DepthExpr.seq
            (uniformStageProgram m interior N hNgtOne hN left bit).eventDepth
            (programForBits m interior N hNgtOne hN left rest).eventDepth =
          DepthExpr.seq
            (uniformStageProgram m interior N hNgtOne hN right bit).eventDepth
            (programForBits m interior N hNgtOne hN right rest).eventDepth
      rw [uniformStageProgram_eventDepth_eq,
        programForBits_eventDepth_eq]

/-- Exact primitive-leaf cardinality of a fixed exponent-bit schedule. -/
theorem programForBits_eventCost_card_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m interior N hNgtOne hN unit bits).eventCost.card =
        (4 * sourceSlotBound interior N hNgtOne hN) * bits.length
  | [] => by simp [programForBits]
  | bit :: rest => by
      rw [programForBits, UnitaryCircuit.seq_eventCost, Multiset.card_add,
        uniformStageProgram_eventCost_card_eq,
        programForBits_eventCost_card_eq
          m interior N hNgtOne hN unit rest]
      simp only [List.length_cons, Nat.mul_succ]
      omega

/-- No strict gate outside CNOT/Toffoli occurs in a selected-bit schedule. -/
theorem programForBits_gate_count_zero_of_ne
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ)
    (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ∀ bits : List (Fin m),
      ResourcePool.count (.gate label)
        (programForBits m interior N hNgtOne hN unit bits).eventCost = 0
  | [] => by simp [programForBits]
  | bit :: rest => by
      simp only [programForBits, UnitaryCircuit.seq_eventCost,
        ResourcePool.count_add,
        uniformStageProgram_gate_count_zero_of_ne
          m interior N hNgtOne hN unit bit label hcnot htoffoli,
        programForBits_gate_count_zero_of_ne
          m interior N hNgtOne hN unit label hcnot htoffoli rest,
        Nat.zero_add]

/-- A selected-bit schedule multiplies the clean unit value by exactly the
product of its selected static powers, restoring all HRS and control work
after every stage. -/
theorem programForBitsStep_cleanWorkspace
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit value : (ZMod N)ˣ)
    (exponent : Fin (2 ^ m)) :
    ∀ bits : List (Fin m),
      programForBitsStep m interior N hNgtOne hN unit bits
          (exponent, cleanWorkspace interior N hNgtOne hN value) =
        (exponent, cleanWorkspace interior N hNgtOne hN
          ((bits.map (selectedUnit unit exponent)).prod * value))
  | [] => by simp [programForBitsStep]
  | bit :: rest => by
      change programForBitsStep m interior N hNgtOne hN unit rest
          (uniformStageStep m interior N hNgtOne hN unit bit
            (exponent, cleanWorkspace interior N hNgtOne hN value)) = _
      rw [uniformStageStep_cleanWorkspace]
      rw [programForBitsStep_cleanWorkspace m interior N hNgtOne hN unit
        (selectedUnit unit exponent bit * value) exponent rest]
      apply congrArg (fun updated =>
        (exponent, cleanWorkspace interior N hNgtOne hN updated))
      simp only [List.map_cons, List.prod_cons]
      ac_rfl

/-- Product over the first `m` selected powers is the base raised to the
selected low-bit weight. -/
theorem selectedUnit_product_eq_pow_selectedLowWeight
    {N : Nat} (m : Nat) (unit : (ZMod N)ˣ) (exponent : Nat) :
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

/-- Scheduling every exponent wire selects exactly `unit^exponent`. -/
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

/-- Complete fixed-trace exponentiation program on the HRS workspace. -/
def exponentiationProgram (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    UnitaryCircuit (Qubits (encoding m interior).width) :=
  programForBits m interior N hNgtOne hN unit (exponentBits m)

/-- Total basis-state action aligned with the complete fixed-trace
exponentiation circuit. -/
def exponentiationStep (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    Registers m interior → Registers m interior :=
  programForBitsStep m interior N hNgtOne hN unit (exponentBits m)

/-- Complete clean basis action of the fixed-trace exponentiation step. -/
theorem exponentiationStep_cleanWorkspace
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit value : (ZMod N)ˣ)
    (exponent : Fin (2 ^ m)) :
    exponentiationStep m interior N hNgtOne hN unit
        (exponent, cleanWorkspace interior N hNgtOne hN value) =
      (exponent, cleanWorkspace interior N hNgtOne hN
        (unit ^ exponent.val * value)) := by
  unfold exponentiationStep
  rw [programForBitsStep_cleanWorkspace]
  unfold exponentBits
  simp only [List.map_ofFn, Function.comp_def]
  rw [selectedUnit_all_eq_pow]

/-- The complete fixed-trace exponentiation circuit realizes its basis-state
action. -/
theorem exponentiationProgram_realizes
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (encoding m interior)
      (exponentiationProgram m interior N hNgtOne hN unit)
      (exponentiationStep m interior N hNgtOne hN unit) := by
  exact programForBits_realizes
    m interior N hNgtOne hN unit (exponentBits m)

/-- The complete fixed-trace exponentiation circuit stays inside its
canonical flat register. -/
theorem exponentiationProgram_physical_idx_subset_range
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    (exponentiationProgram m interior N hNgtOne hN unit).physical_idx ⊆
      List.range (encoding m interior).width := by
  exact programForBits_physical_idx_subset_range
    m interior N hNgtOne hN unit (exponentBits m)

/-- Complete exponentiation has an exact event pool independent of the
runtime base unit. -/
theorem exponentiationProgram_eventCost_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (left right : (ZMod N)ˣ) :
    (exponentiationProgram m interior N hNgtOne hN left).eventCost =
      (exponentiationProgram m interior N hNgtOne hN right).eventCost := by
  exact programForBits_eventCost_eq
    m interior N hNgtOne hN left right (exponentBits m)

/-- Complete exponentiation has an exact event path independent of the
runtime base unit. -/
theorem exponentiationProgram_eventDepth_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (left right : (ZMod N)ˣ) :
    (exponentiationProgram m interior N hNgtOne hN left).eventDepth =
      (exponentiationProgram m interior N hNgtOne hN right).eventDepth := by
  exact programForBits_eventDepth_eq
    m interior N hNgtOne hN left right (exponentBits m)

/-- Exact primitive-leaf cardinality of complete fixed-trace
exponentiation. -/
theorem exponentiationProgram_eventCost_card_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    (exponentiationProgram m interior N hNgtOne hN unit).eventCost.card =
      (4 * sourceSlotBound interior N hNgtOne hN) * m := by
  rw [exponentiationProgram]
  simpa [exponentBits] using
    programForBits_eventCost_card_eq
      m interior N hNgtOne hN unit (exponentBits m)

/-- Complete fixed-trace exponentiation contains only CNOT and Toffoli
strict gates. -/
theorem exponentiationProgram_gate_count_zero_of_ne
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ)
    (label : Resource.GateLabel)
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label)
        (exponentiationProgram m interior N hNgtOne hN unit).eventCost = 0 := by
  exact programForBits_gate_count_zero_of_ne
    m interior N hNgtOne hN unit label hcnot htoffoli (exponentBits m)

/-- Complete clean computational-basis endpoint of the fixed-trace circuit. -/
theorem exponentiationProgram_applyNormalized_clean_ket
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit value : (ZMod N)ˣ)
    (exponent : Fin (2 ^ m)) :
    (exponentiationProgram m interior N hNgtOne hN unit).applyNormalized
        (NormalizedVector.ket
          ((encoding m interior).encode
            (exponent, cleanWorkspace interior N hNgtOne hN value))) =
      NormalizedVector.ket
        ((encoding m interior).encode
          (exponent, cleanWorkspace interior N hNgtOne hN
            (unit ^ exponent.val * value))) := by
  have hrealizes := (programForBits_realizes
    m interior N hNgtOne hN unit (exponentBits m)).apply_encoded_ket
      (exponent, cleanWorkspace interior N hNgtOne hN value)
  rw [programForBitsStep_cleanWorkspace] at hrealizes
  unfold exponentiationProgram exponentBits
  simp only [exponentBits, List.map_ofFn, Function.comp_def] at hrealizes
  rw [selectedUnit_all_eq_pow] at hrealizes
  exact hrealizes

/-- Exact unit-independent Toffoli coordinate of a fixed selected-bit
schedule. -/
def bitsToffoliCount {m : Nat} (interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (bits : List (Fin m)) : Nat :=
  (3 * sourceSlotBound interior N hNgtOne hN) * bits.length

/-- Exact Toffoli equality of the fixed-trace selected-bit circuit fold. -/
theorem programForBits_toffoli_count_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      ResourcePool.count (.gate (.builtin "toffoli"))
          (programForBits m interior N hNgtOne hN unit bits).eventCost =
        bitsToffoliCount interior N hNgtOne hN bits
  | [] => by simp [programForBits, bitsToffoliCount]
  | bit :: rest => by
      rw [programForBits, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        uniformStageProgram_toffoli_count_eq,
        programForBits_toffoli_count_eq m interior N hNgtOne hN unit rest]
      simp only [bitsToffoliCount, List.length_cons, Nat.mul_succ]
      omega

/-- Exact Toffoli equality of the complete fixed-trace exponentiation
program. -/
theorem exponentiationProgram_toffoli_count_eq
    (m interior N : Nat) (hNgtOne : 1 < N)
    (hN : N < 2 ^ wordBits interior) (unit : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (exponentiationProgram m interior N hNgtOne hN unit).eventCost =
      bitsToffoliCount interior N hNgtOne hN (exponentBits m) := by
  exact programForBits_toffoli_count_eq
    m interior N hNgtOne hN unit (exponentBits m)

end

end MAU.Exponentiation.DirtyBorrowedCircuit
end QuantumAlg

end
