/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

-- Intentional exception: machine-readable source-owner markers keep full module names on one line.
set_option linter.style.longLine false

/-!
# QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Schedule

Public declarations for
`QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Schedule`.
-/
variable [params :
  QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.VariableModularMul.Parameters]

/-!
# Width-parameterized variable modular-multiplication schedule

This module assembles the parameterized selected-addition and source-doubling
blocks and records their carrier, realization, and clean-fold properties.
-/

section

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.VariableModularMul

noncomputable section

set_option exponentiation.threshold 4096 in
/-- Lifting an in-place program through the shared carrier preserves its range certificate. -/
theorem liftInPlaceProgram_physical_idx_subset_range
    (program : UnitaryCircuit (Qubits inPlaceEncoding.width))
    (contained : program.physical_idx ⊆ List.range inPlaceEncoding.width) :
    (liftInPlaceProgram program).physical_idx ⊆ List.range rawEncoding.width := by
  unfold liftInPlaceProgram
  apply UnitaryCircuit.prodRight_physical_idx_subset_range
  apply UnitaryCircuit.prodRight_physical_idx_subset_range
  exact UnitaryCircuit.prodLeft_physical_idx_subset_range program contained

set_option exponentiation.threshold 4096 in
/-- The external-accumulator word exchange stays in the shared carrier. -/
theorem accumulatorSwapCircuit_physical_idx_subset_range :
    accumulatorSwapCircuit.physical_idx ⊆ List.range rawEncoding.width := by
  unfold accumulatorSwapCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

set_option exponentiation.threshold 4096 in
/-- The source-copy word xor stays in the shared carrier. -/
theorem sourceCopyCircuit_physical_idx_subset_range :
    sourceCopyCircuit.physical_idx ⊆ List.range rawEncoding.width := by
  unfold sourceCopyCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

set_option exponentiation.threshold 4096 in
/-- Source unload is the same carrier-local xor program as source copy. -/
theorem sourceUnloadCircuit_physical_idx_subset_range :
    sourceUnloadCircuit.physical_idx ⊆ List.range rawEncoding.width := by
  unfold sourceUnloadCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

set_option exponentiation.threshold 4096 in
/-- One mechanically controlled selected-add stage stays in the shared carrier. -/
theorem stageCircuit_physical_idx_subset_range (bit : Fin params.width) :
    (stageCircuit bit).physical_idx ⊆ List.range rawEncoding.width := by
  unfold stageCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range
    (rawStageGates bit)

set_option exponentiation.threshold 4096 in
/-- The lifted concrete multiplication-by-two program stays in the common carrier. -/
theorem doublingCircuit_physical_idx_subset_range :
    doublingCircuit.physical_idx ⊆ List.range rawEncoding.width := by
  unfold doublingCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

set_option exponentiation.threshold 4096 in
/-- One selected-add routing block stays in the shared carrier. -/
theorem selectedAddCircuit_physical_idx_subset_range (bit : Fin params.width) :
    (selectedAddCircuit bit).physical_idx ⊆ List.range rawEncoding.width := by
  unfold selectedAddCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

set_option exponentiation.threshold 4096 in
/-- A selected-add followed by the lifted source doubling stays in the carrier. -/
theorem roundCircuit_physical_idx_subset_range (bit : Fin params.width) :
    (roundCircuit bit).physical_idx ⊆ List.range rawEncoding.width := by
  unfold roundCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.VariableModularMul

/-! ## Width-indexed schedule assembly -/

/-!
# Gate-level variable modular-multiplication schedule

This module assembles the concrete selected-addition and source-doubling
blocks into the fixed-width schedule. All but the final bit use a selected add
followed by doubling; the final bit uses only its selected add, after which
the inverse doublings restore the stored variable source. It records the
physical schedule and its folded action, but does not yet state a clean
arithmetic endpoint theorem.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

/-! ## Inverse source-doubling block -/

/-- The fixed unit which undoes the source-doubling multiplication. -/
def inverseTwoUnit : (ZMod params.modulus.val)ˣ :=
  VariableModularMul.twoUnit⁻¹

/-- The inverse source-doubling list is the exact reversal of the concrete
shift/reduce doubling list. -/
def inverseDoublingGates :
    List (EncodedBit.GateSpec VariableModularMul.rawEncoding) :=
  VariableModularMul.doublingGates.reverse

set_option exponentiation.threshold 2048 in
/-- Exact inverse of the concrete shift/reduce source-doubling circuit. -/
def inverseDoublingCircuit :
    UnitaryCircuit (Qubits VariableModularMul.rawEncoding.width) :=
  EncodedBit.GateSpec.programList inverseDoublingGates

/-- Raw fold of the exact reversed source list. -/
def rawInverseDoublingStep :
    VariableModularMul.RawRegisters → VariableModularMul.RawRegisters :=
  EncodedBit.GateSpec.stepList inverseDoublingGates

/-- The literal inverse-doubling list has its displayed raw action. -/
theorem inverseDoublingGates_stepList
    (x : VariableModularMul.RawRegisters) :
    EncodedBit.GateSpec.stepList inverseDoublingGates x =
      rawInverseDoublingStep x := by
  rfl

set_option exponentiation.threshold 2048 in
/-- Named action of the actual inverse source-doubling circuit. -/
def inverseDoublingStep :
    VariableModularMul.Registers → VariableModularMul.Registers :=
  fun x => VariableModularMul.registersEquiv.symm
    (rawInverseDoublingStep (VariableModularMul.registersEquiv x))

set_option exponentiation.threshold 2048 in
/-- The reversed concrete source list realizes its displayed inverse fold. -/
theorem inverseDoubling_realizes :
    UnitaryCircuit.Realizes VariableModularMul.encoding inverseDoublingCircuit
      inverseDoublingStep := by
  have raw : UnitaryCircuit.Realizes VariableModularMul.rawEncoding
      inverseDoublingCircuit rawInverseDoublingStep := by
    unfold inverseDoublingCircuit
    exact EncodedBit.GateSpec.realizesList inverseDoublingGates
  exact UnitaryCircuit.Realizes.relabel VariableModularMul.registersEquiv raw

/-! ## Clean source-scaling bridges -/

/-- Semantic update which leaves the multiplier and external accumulator in
place while scaling the stored source residue. -/
def scaleMultiplicand
    (coefficient : ZMod params.modulus.val)
    (x : VariableModularMul.Data) : VariableModularMul.Data where
  multiplier := x.multiplier
  multiplicand := coefficient * x.multiplicand
  accumulator := x.accumulator

/-- Semantic source update induced by the actual multiplication-by-two block. -/
def doubledData (x : VariableModularMul.Data) : VariableModularMul.Data :=
  scaleMultiplicand
    (VariableModularMul.twoUnit : ZMod params.modulus.val) x

/-- Semantic source update induced by the actual inverse-doubling block. -/
def inverseDoubledData
    (x : VariableModularMul.Data) : VariableModularMul.Data :=
  scaleMultiplicand (inverseTwoUnit : ZMod params.modulus.val) x

-- This is the actual shift/reduce multiplication-by-two action on clean data.
set_option exponentiation.threshold 2048 in
theorem doublingStep_cleanEndpoint (x : VariableModularMul.Data) :
    VariableModularMul.doublingStep (VariableModularMul.cleanRegisters x) =
      VariableModularMul.cleanRegisters (doubledData x) := by
  simpa only [doubledData, scaleMultiplicand,
    VariableModularMul.Data.doubleMultiplicand,
    VariableModularMul.twoUnit, ZMod.coe_unitOfCoprime,
    Nat.cast_ofNat] using
    VariableModularMul.doublingStep_cleanEndpoint x

-- This is the exact reverse of the actual shift/reduce doubling action.
set_option exponentiation.threshold 2048 in
theorem inverseDoublingStep_cleanEndpoint (x : VariableModularMul.Data) :
    inverseDoublingStep (VariableModularMul.cleanRegisters x) =
      VariableModularMul.cleanRegisters (inverseDoubledData x) := by
  let y := inverseDoubledData x
  have hunitCancel :
      (VariableModularMul.twoUnit : ZMod params.modulus.val) *
          (inverseTwoUnit : ZMod params.modulus.val) = 1 := by
    rw [← Units.val_mul]
    simp [inverseTwoUnit]
  have hcancel : doubledData y = x := by
    cases x
    simp only [y, doubledData, inverseDoubledData, scaleMultiplicand]
    congr 1
    rw [← mul_assoc, hunitCancel, one_mul]
  have hforward := doublingStep_cleanEndpoint y
  rw [hcancel] at hforward
  have hforwardRaw :
      VariableModularMul.rawDoublingStep
          (VariableModularMul.registersEquiv
            (VariableModularMul.cleanRegisters y)) =
        VariableModularMul.registersEquiv
          (VariableModularMul.cleanRegisters x) := by
    simpa [VariableModularMul.doublingStep] using
      congrArg VariableModularMul.registersEquiv hforward
  apply VariableModularMul.registersEquiv.injective
  change rawInverseDoublingStep
      (VariableModularMul.registersEquiv
        (VariableModularMul.cleanRegisters x)) =
    VariableModularMul.registersEquiv
      (VariableModularMul.cleanRegisters y)
  calc
    rawInverseDoublingStep
        (VariableModularMul.registersEquiv
          (VariableModularMul.cleanRegisters x)) =
        EncodedBit.GateSpec.stepList
          VariableModularMul.doublingGates.reverse
          (VariableModularMul.registersEquiv
            (VariableModularMul.cleanRegisters x)) := by
      rfl
    _ = EncodedBit.GateSpec.stepList
          VariableModularMul.doublingGates.reverse
          (EncodedBit.GateSpec.stepList VariableModularMul.doublingGates
            (VariableModularMul.registersEquiv
              (VariableModularMul.cleanRegisters y))) := by
      rw [VariableModularMul.doublingGates_stepList, hforwardRaw]
    _ = VariableModularMul.registersEquiv
          (VariableModularMul.cleanRegisters y) :=
      EncodedBit.GateSpec.stepList_reverse_stepList
        VariableModularMul.doublingGates _

/-! ## Recursive physical schedule folds -/

/-- Literal primitive list for an explicit selected-add/doubling prefix. -/
def forwardGates : List (Fin params.width) →
    List (EncodedBit.GateSpec VariableModularMul.rawEncoding)
  | [] => []
  | bit :: rest => VariableModularMul.roundGates bit ++ forwardGates rest

/-- The physical forward fold for an explicit list of multiplier-bit rounds. -/
def forwardProgram :
    List (Fin params.width) →
      UnitaryCircuit (Qubits VariableModularMul.rawEncoding.width)
  | [] => UnitaryCircuit.identity (Qubits VariableModularMul.rawEncoding.width) [] (by simp)
  | bit :: rest =>
      UnitaryCircuit.seq (VariableModularMul.roundCircuit bit) (forwardProgram rest)

/-- Left-to-right execution of an indexed step list.  Sharing this fold
between the physical and clean semantics avoids an expensive fixed-width
recursor-conversion proof. -/
def foldSteps {Index State : Type} (next : Index → State → State) :
    List Index → State → State
  | [], x => x
  | index :: rest, x => foldSteps next rest (next index x)

/-- The named forward fold aligned with `forwardProgram` execution order. -/
def forwardStep :
    List (Fin params.width) →
      VariableModularMul.Registers → VariableModularMul.Registers
  | roundBits => foldSteps VariableModularMul.roundStep roundBits

/-- Raw fold aligned with the literal forward primitive list. -/
def rawForwardStep :
    List (Fin params.width) →
      VariableModularMul.RawRegisters → VariableModularMul.RawRegisters
  | roundBits => foldSteps VariableModularMul.rawRoundStep roundBits

/-- The literal forward primitive list has its displayed raw fold. -/
theorem forwardGates_stepList : ∀ bits : List (Fin params.width),
    EncodedBit.GateSpec.stepList (forwardGates bits) = rawForwardStep bits
  | [] => rfl
  | bit :: rest => by
      funext x
      rw [forwardGates, EncodedBit.GateSpec.stepList_append,
        VariableModularMul.roundGates_stepList]
      change EncodedBit.GateSpec.stepList (forwardGates rest)
          (VariableModularMul.rawRoundStep bit x) =
        rawForwardStep rest (VariableModularMul.rawRoundStep bit x)
      rw [forwardGates_stepList rest]

-- Normalize the width-indexed carrier without expanding its exponent.
set_option exponentiation.threshold 2048 in
/-- Every explicit forward list serially realizes its matching named fold. -/
theorem forward_realizes :
    ∀ bits : List (Fin params.width),
      UnitaryCircuit.Realizes VariableModularMul.encoding (forwardProgram bits)
        (forwardStep bits)
  | [] => by
      apply UnitaryCircuit.Realizes.congrStep
        (UnitaryCircuit.Realizes.relabel VariableModularMul.registersEquiv
          (UnitaryCircuit.Realizes.identity VariableModularMul.rawEncoding))
      intro x
      exact VariableModularMul.registersEquiv.symm_apply_apply x
  | bit :: rest => by
      exact UnitaryCircuit.Realizes.seq
        (firstStep := VariableModularMul.roundStep bit)
        (secondStep := forwardStep rest)
        (VariableModularMul.roundCircuit_realizes bit)
        (forward_realizes rest)

/-- The physical source-restoration fold executes one actual inverse-doubling
block for every requested prior doubling. -/
def restoreGates : Nat →
    List (EncodedBit.GateSpec VariableModularMul.rawEncoding)
  | 0 => []
  | rounds + 1 => inverseDoublingGates ++ restoreGates rounds

/-- The physical source-restoration fold executes one actual inverse-doubling
block for every requested prior doubling. -/
def restoreProgram : Nat → UnitaryCircuit (Qubits VariableModularMul.rawEncoding.width)
  | 0 => UnitaryCircuit.identity (Qubits VariableModularMul.rawEncoding.width) [] (by simp)
  | rounds + 1 => UnitaryCircuit.seq inverseDoublingCircuit (restoreProgram rounds)

/-- Repeated execution of one state transformer, shared by the physical and
clean restoration semantics to avoid a concrete fixed-width recursor bridge. -/
def iterateSteps {State : Type} (next : State → State) : Nat → State → State
  | 0, x => x
  | rounds + 1, x => iterateSteps next rounds (next x)

/-- The named source-restoration fold aligned with `restoreProgram`. -/
def restoreStep :
    Nat → VariableModularMul.Registers → VariableModularMul.Registers
  | rounds => iterateSteps inverseDoublingStep rounds

/-- Raw source-restoration fold aligned with the literal primitive list. -/
def rawRestoreStep :
    Nat → VariableModularMul.RawRegisters → VariableModularMul.RawRegisters
  | rounds => iterateSteps rawInverseDoublingStep rounds

/-- The literal restoration primitive list has its displayed raw fold. -/
theorem restoreGates_stepList : ∀ rounds : Nat,
    EncodedBit.GateSpec.stepList (restoreGates rounds) = rawRestoreStep rounds
  | 0 => rfl
  | rounds + 1 => by
      funext x
      rw [restoreGates, EncodedBit.GateSpec.stepList_append]
      rw [inverseDoublingGates_stepList]
      change EncodedBit.GateSpec.stepList (restoreGates rounds)
          (rawInverseDoublingStep x) =
        rawRestoreStep rounds (rawInverseDoublingStep x)
      rw [restoreGates_stepList rounds]

-- Normalize the width-indexed carrier without expanding its exponent.
set_option exponentiation.threshold 2048 in
/-- Every requested source-restoration length serially realizes its named
inverse-doubling fold. -/
theorem restore_realizes :
    ∀ rounds : Nat,
      UnitaryCircuit.Realizes VariableModularMul.encoding (restoreProgram rounds)
        (restoreStep rounds)
  | 0 => by
      apply UnitaryCircuit.Realizes.congrStep
        (UnitaryCircuit.Realizes.relabel VariableModularMul.registersEquiv
          (UnitaryCircuit.Realizes.identity VariableModularMul.rawEncoding))
      intro x
      exact VariableModularMul.registersEquiv.symm_apply_apply x
  | rounds + 1 => by
      exact UnitaryCircuit.Realizes.seq
        (firstStep := inverseDoublingStep)
        (secondStep := restoreStep rounds)
        inverseDoubling_realizes
        (restore_realizes rounds)

/-! ## Width-indexed production schedule -/

/-- The canonical low-to-high list of all multiplier-bit indices. -/
def bits : List (Fin params.width) :=
  List.ofFn (fun bit : Fin params.width => bit)

/-- Final multiplier-bit index at every positive width. -/
def lastBit : Fin params.width :=
  ⟨params.width - 1, Nat.pred_lt params.widthPos.ne'⟩

/-- The raw inverse-doubling action is the packed form of its named action. -/
theorem rawInverseDoublingStep_registersEquiv
    (x : VariableModularMul.Registers) :
    rawInverseDoublingStep (VariableModularMul.registersEquiv x) =
      VariableModularMul.registersEquiv (inverseDoublingStep x) := by
  simp only [inverseDoublingStep, Equiv.apply_symm_apply]

/-- Every literal forward fold is the packed form of the matching named fold. -/
theorem rawForwardStep_registersEquiv :
    ∀ (roundBits : List (Fin params.width)) (x : VariableModularMul.Registers),
      rawForwardStep roundBits (VariableModularMul.registersEquiv x) =
        VariableModularMul.registersEquiv (forwardStep roundBits x)
  | [], _ => rfl
  | bit :: rest, x => by
      change rawForwardStep rest
          (VariableModularMul.rawRoundStep bit
            (VariableModularMul.registersEquiv x)) =
        VariableModularMul.registersEquiv
          (forwardStep rest (VariableModularMul.roundStep bit x))
      rw [VariableModularMul.rawRoundStep_registersEquiv,
        rawForwardStep_registersEquiv]

/-- Every literal restoration fold is the packed form of the matching named fold. -/
theorem rawRestoreStep_registersEquiv :
    ∀ (rounds : Nat) (x : VariableModularMul.Registers),
      rawRestoreStep rounds (VariableModularMul.registersEquiv x) =
        VariableModularMul.registersEquiv (restoreStep rounds x)
  | 0, _ => rfl
  | rounds + 1, x => by
      change rawRestoreStep rounds
          (rawInverseDoublingStep (VariableModularMul.registersEquiv x)) =
        VariableModularMul.registersEquiv
          (restoreStep rounds (inverseDoublingStep x))
      rw [rawInverseDoublingStep_registersEquiv,
        rawRestoreStep_registersEquiv]

/-- Literal primitive source for the full width-indexed multiplication
schedule. -/
def gates : List (EncodedBit.GateSpec VariableModularMul.rawEncoding) :=
  forwardGates (bits.take (params.width - 1)) ++
    VariableModularMul.selectedAddGates lastBit ++
    restoreGates (params.width - 1)

/-- Raw folded action of the full literal multiplication schedule. -/
def rawStep :
    VariableModularMul.RawRegisters → VariableModularMul.RawRegisters :=
  fun x => rawRestoreStep (params.width - 1)
    (VariableModularMul.rawSelectedAddStep lastBit
      (rawForwardStep (bits.take (params.width - 1)) x))

/-- The full literal source list has its displayed raw schedule fold. -/
theorem gates_stepList (x : VariableModularMul.RawRegisters) :
    EncodedBit.GateSpec.stepList gates x = rawStep x := by
  unfold gates rawStep
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [forwardGates_stepList, VariableModularMul.selectedAddGates_stepList,
    restoreGates_stepList]

/-- The width-indexed schedule: all but the last selected-add/doubling rounds,
the last selected add, then the inverse doublings restoring the source. -/
def circuit : UnitaryCircuit (Qubits VariableModularMul.rawEncoding.width) :=
  EncodedBit.GateSpec.programList gates

/-- Folded action of the complete width-indexed physical schedule. -/
def step : VariableModularMul.Registers → VariableModularMul.Registers :=
  fun x => restoreStep (params.width - 1)
    (VariableModularMul.selectedAddStep lastBit
      (forwardStep (bits.take (params.width - 1)) x))

/-- The full raw literal fold is the packed form of the public named step. -/
theorem rawStep_registersEquiv (x : VariableModularMul.Registers) :
    rawStep (VariableModularMul.registersEquiv x) =
      VariableModularMul.registersEquiv (step x) := by
  unfold rawStep step
  rw [rawForwardStep_registersEquiv,
    VariableModularMul.rawSelectedAddStep_registersEquiv,
    rawRestoreStep_registersEquiv]

set_option exponentiation.threshold 2048 in
/-- The complete physical schedule realizes its direct folded action. -/
theorem realizes : UnitaryCircuit.Realizes VariableModularMul.encoding circuit step := by
  have raw : UnitaryCircuit.Realizes VariableModularMul.rawEncoding circuit rawStep := by
    unfold circuit
    exact EncodedBit.GateSpec.realizesList_congrStep gates gates_stepList
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.relabel VariableModularMul.registersEquiv raw)
  intro x
  rw [rawStep_registersEquiv]
  exact VariableModularMul.registersEquiv.symm_apply_apply _

/-! ## Resource projections -/

/-- Strict event pool derived solely from the complete actual schedule. -/
def eventCost : ResourcePool .quantum :=
  circuit.eventCost

/-- Strict event critical path derived solely from the complete actual
schedule. -/
def eventDepth :=
  circuit.eventDepth

/-- Linearizing the actual schedule's strict event-depth tree recovers its
strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost :
    circuit.resourcesFromEventDepth = eventCost := by
  simpa only [eventCost] using
    UnitaryCircuit.resourcesFromEventDepth_eq_eventCost circuit

end

end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Physical schedule footprint -/

/-! # Physical footprint of the variable modular-multiplication schedule -/

section

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.VariableModularMulSchedule

noncomputable section

set_option exponentiation.threshold 4096 in
/-- The lifted inverse source-doubling program stays in the common carrier. -/
theorem inverseDoublingCircuit_physical_idx_subset_range :
    inverseDoublingCircuit.physical_idx ⊆
      List.range VariableModularMul.rawEncoding.width := by
  unfold inverseDoublingCircuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

set_option exponentiation.threshold 4096 in
/-- Every explicit selected-add/doubling prefix stays in the common carrier. -/
theorem forwardProgram_physical_idx_subset_range :
    ∀ bits : List (Fin params.width),
      (forwardProgram bits).physical_idx ⊆
        List.range VariableModularMul.rawEncoding.width
  | [] => by
      simp [forwardProgram, UnitaryCircuit.identity]
  | bit :: rest => by
      change (UnitaryCircuit.seq (VariableModularMul.roundCircuit bit)
        (forwardProgram rest)).physical_idx ⊆
          List.range VariableModularMul.rawEncoding.width
      exact UnitaryCircuit.seq_physical_idx_subset _ _
        (VariableModularMul.roundCircuit_physical_idx_subset_range bit)
        (forwardProgram_physical_idx_subset_range rest)

set_option exponentiation.threshold 4096 in
/-- Every inverse-doubling restoration suffix stays in the common carrier. -/
theorem restoreProgram_physical_idx_subset_range :
    ∀ rounds : Nat, (restoreProgram rounds).physical_idx ⊆
      List.range VariableModularMul.rawEncoding.width
  | 0 => by
      simp [restoreProgram, UnitaryCircuit.identity]
  | rounds + 1 => by
      change (UnitaryCircuit.seq inverseDoublingCircuit (restoreProgram rounds)).physical_idx ⊆
        List.range VariableModularMul.rawEncoding.width
      exact UnitaryCircuit.seq_physical_idx_subset _ _
        inverseDoublingCircuit_physical_idx_subset_range
        (restoreProgram_physical_idx_subset_range rounds)

set_option exponentiation.threshold 4096 in
/-- The complete width-indexed multiplication schedule stays in its carrier. -/
theorem circuit_physical_idx_subset_range :
    circuit.physical_idx ⊆ List.range VariableModularMul.rawEncoding.width := by
  unfold circuit
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.VariableModularMulSchedule

/-! ## Clean restoration semantics -/

/-! # Restoration-fold clean semantics for variable modular multiplication -/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

omit params in
/-- An embedding respected by one abstract step is respected by every finite
iteration count. -/
theorem iterateSteps_cleanEndpoint
    {Data Registers : Type}
    (physical : Registers → Registers)
    (semantic : Data → Data)
    (embed : Data → Registers)
    (hone : ∀ x, physical (embed x) = embed (semantic x)) :
    ∀ (rounds : Nat) (x : Data),
      iterateSteps physical rounds (embed x) =
        embed (iterateSteps semantic rounds x)
  | 0, _ => rfl
  | rounds + 1, x => by
      change iterateSteps physical rounds (physical (embed x)) =
        embed (iterateSteps semantic rounds (semantic x))
      rw [hone]
      exact iterateSteps_cleanEndpoint physical semantic embed hone rounds
        (semantic x)

/-- Pure clean-state action aligned with the inverse-doubling restoration fold. -/
def restoreData : Nat → VariableModularMul.Data → VariableModularMul.Data
  | rounds => iterateSteps inverseDoubledData rounds

-- The restoration induction never unfolds a full common-carrier state.
set_option exponentiation.threshold 2048 in
theorem restoreStep_cleanEndpoint :
    ∀ (rounds : Nat) (x : VariableModularMul.Data),
      restoreStep rounds (VariableModularMul.cleanRegisters x) =
        VariableModularMul.cleanRegisters (restoreData rounds x)
  | rounds, x => by
      simpa only [restoreStep, restoreData] using
        (iterateSteps_cleanEndpoint inverseDoublingStep inverseDoubledData
          VariableModularMul.cleanRegisters inverseDoublingStep_cleanEndpoint
          rounds x)

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Clean round semantics -/

/-! # One-round clean semantics for variable modular multiplication -/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

/-- Pure clean-state action of one selected-add/doubling round. -/
def roundData (bit : Fin params.width)
    (x : VariableModularMul.Data) : VariableModularMul.Data :=
  doubledData (VariableModularMul.Data.addSelected bit x)

-- The one-round clean bridge retains the width-indexed carrier in its type.
set_option exponentiation.threshold 2048 in
theorem roundStep_cleanEndpoint (bit : Fin params.width)
    (x : VariableModularMul.Data) :
    VariableModularMul.roundStep bit (VariableModularMul.cleanRegisters x) =
      VariableModularMul.cleanRegisters (roundData bit x) := by
  simp only [VariableModularMul.roundStep, roundData]
  rw [VariableModularMul.selectedAddStep_cleanEndpoint,
    doublingStep_cleanEndpoint]

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Abstract forward-fold semantics -/

/-! # Abstract forward fold for variable modular multiplication -/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

omit params in
/-- An embedding respected by one abstract step is respected by every finite
left-to-right fold. -/
theorem foldSteps_cleanEndpoint
    {Index Data Registers : Type}
    (physical : Index → Registers → Registers)
    (semantic : Index → Data → Data)
    (embed : Data → Registers)
    (hone : ∀ index x, physical index (embed x) = embed (semantic index x)) :
    ∀ (indices : List Index) (x : Data),
      foldSteps physical indices (embed x) =
        embed (foldSteps semantic indices x)
  | [], _ => rfl
  | index :: rest, x => by
      change foldSteps physical rest (physical index (embed x)) =
        embed (foldSteps semantic rest (semantic index x))
      rw [hone]
      exact foldSteps_cleanEndpoint physical semantic embed hone rest
        (semantic index x)

/-- Pure clean-state action aligned with the forward physical-list fold. -/
def forwardData :
    List (Fin params.width) →
      VariableModularMul.Data → VariableModularMul.Data
  | roundBits => foldSteps roundData roundBits

omit params in
/-- Splitting an indexed step list at append agrees with sequential fold
composition. -/
theorem foldSteps_append {Index State : Type} (next : Index → State → State)
    (first second : List Index) (x : State) :
    foldSteps next (first ++ second) x =
      foldSteps next second (foldSteps next first x) := by
  induction first generalizing x with
  | nil =>
      rfl
  | cons index rest ih =>
      change foldSteps next (rest ++ second) (next index x) =
        foldSteps next second (foldSteps next rest (next index x))
      exact ih (next index x)

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
end
end
end
end
end
