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
blocks and records their carrier, realization, and clean-fold properties.  The
carrier is now part of each circuit's type, so the former `physical_idx`
side-condition layer is obsolete.
-/

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

variable {environment : OracleModel.empty.Interpretation}

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
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (VariableModularMul.rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty inverseDoublingGates

/-- Raw fold of the exact reversed source list. -/
def rawInverseDoublingStep :
    VariableModularMul.RawRegisters → VariableModularMul.RawRegisters :=
  EncodedBit.GateSpec.stepList inverseDoublingGates

/-- The literal inverse-doubling list has its displayed raw action. -/
lemma inverseDoublingGates_stepList
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
lemma inverseDoubling_realizes :
    UnitaryCircuit.Realizes VariableModularMul.encoding inverseDoublingCircuit environment
      inverseDoublingStep := by
  have raw : UnitaryCircuit.Realizes VariableModularMul.rawEncoding
      inverseDoublingCircuit environment rawInverseDoublingStep := by
    unfold inverseDoublingCircuit
    exact EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _)
      .empty
      inverseDoublingGates
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
lemma doublingStep_cleanEndpoint (x : VariableModularMul.Data) :
    VariableModularMul.doublingStep (VariableModularMul.cleanRegisters x) =
      VariableModularMul.cleanRegisters (doubledData x) := by
  simpa only [doubledData, scaleMultiplicand,
    VariableModularMul.Data.doubleMultiplicand,
    VariableModularMul.twoUnit, ZMod.coe_unitOfCoprime,
    Nat.cast_ofNat] using
    VariableModularMul.doublingStep_cleanEndpoint x

-- This is the exact reverse of the actual shift/reduce doubling action.
set_option exponentiation.threshold 2048 in
lemma inverseDoublingStep_cleanEndpoint (x : VariableModularMul.Data) :
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
      UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical (VariableModularMul.rawEncoding.width)).toQuantum
  | [] => UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical VariableModularMul.rawEncoding.width).toQuantum
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
lemma forwardGates_stepList : ∀ bits : List (Fin params.width),
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
lemma forward_realizes :
    ∀ bits : List (Fin params.width),
      UnitaryCircuit.Realizes VariableModularMul.encoding (forwardProgram bits) environment
        (forwardStep bits)
  | [] => by
      apply UnitaryCircuit.Realizes.congrStep
        (UnitaryCircuit.Realizes.relabel VariableModularMul.registersEquiv
          (UnitaryCircuit.Realizes.identityAt (environment := environment) AlgorithmGate.model
            .empty
            VariableModularMul.rawEncoding (QubitLayout.canonical _)))
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
def restoreProgram : Nat → UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (VariableModularMul.rawEncoding.width)).toQuantum
  | 0 => UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical VariableModularMul.rawEncoding.width).toQuantum
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
lemma restoreGates_stepList : ∀ rounds : Nat,
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
lemma restore_realizes :
    ∀ rounds : Nat,
      UnitaryCircuit.Realizes VariableModularMul.encoding (restoreProgram rounds) environment
        (restoreStep rounds)
  | 0 => by
      apply UnitaryCircuit.Realizes.congrStep
        (UnitaryCircuit.Realizes.relabel VariableModularMul.registersEquiv
          (UnitaryCircuit.Realizes.identityAt (environment := environment) AlgorithmGate.model
            .empty
            VariableModularMul.rawEncoding (QubitLayout.canonical _)))
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
lemma rawInverseDoublingStep_registersEquiv
    (x : VariableModularMul.Registers) :
    rawInverseDoublingStep (VariableModularMul.registersEquiv x) =
      VariableModularMul.registersEquiv (inverseDoublingStep x) := by
  simp only [inverseDoublingStep, Equiv.apply_symm_apply]

/-- Every literal forward fold is the packed form of the matching named fold. -/
lemma rawForwardStep_registersEquiv :
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
lemma rawRestoreStep_registersEquiv :
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
lemma gates_stepList (x : VariableModularMul.RawRegisters) :
    EncodedBit.GateSpec.stepList gates x = rawStep x := by
  unfold gates rawStep
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [forwardGates_stepList, VariableModularMul.selectedAddGates_stepList,
    restoreGates_stepList]

/-- The width-indexed schedule: all but the last selected-add/doubling rounds,
the last selected add, then the inverse doublings restoring the source. -/
def circuit : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (VariableModularMul.rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates

/-- Folded action of the complete width-indexed physical schedule. -/
def step : VariableModularMul.Registers → VariableModularMul.Registers :=
  fun x => restoreStep (params.width - 1)
    (VariableModularMul.selectedAddStep lastBit
      (forwardStep (bits.take (params.width - 1)) x))

/-- The full raw literal fold is the packed form of the public named step. -/
lemma rawStep_registersEquiv (x : VariableModularMul.Registers) :
    rawStep (VariableModularMul.registersEquiv x) =
      VariableModularMul.registersEquiv (step x) := by
  unfold rawStep step
  rw [rawForwardStep_registersEquiv,
    VariableModularMul.rawSelectedAddStep_registersEquiv,
    rawRestoreStep_registersEquiv]

set_option exponentiation.threshold 2048 in
/-- The complete physical schedule realizes its direct folded action. -/
lemma realizes : UnitaryCircuit.Realizes VariableModularMul.encoding circuit environment step :=
  by
  have raw : UnitaryCircuit.Realizes VariableModularMul.rawEncoding circuit environment rawStep :=
    by
    unfold circuit
    exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
      (QubitLayout.canonical _) .empty
      gates gates_stepList
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.relabel VariableModularMul.registersEquiv raw)
  intro x
  rw [rawStep_registersEquiv]
  exact VariableModularMul.registersEquiv.symm_apply_apply _

/-! ## Resource projections -/

/-- Strict event pool derived solely from the complete actual schedule. -/
def eventCost : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  circuit.eventCost

/-- Strict event critical path derived solely from the complete actual
schedule. -/
def eventDepth :=
  circuit.eventDepth

/-- Linearizing the actual schedule's strict event-depth tree recovers its
strict event pool. -/
lemma resourcesFromEventDepth_eq_eventCost :
    circuit.resourcesFromEventDepth = eventCost := by
  simpa only [eventCost] using
    UnitaryCircuit.resourcesFromEventDepth_eq_eventCost circuit

end

end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

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
lemma iterateSteps_cleanEndpoint
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
lemma restoreStep_cleanEndpoint :
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
lemma roundStep_cleanEndpoint (bit : Fin params.width)
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
lemma foldSteps_cleanEndpoint
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
lemma foldSteps_append {Index State : Type} (next : Index → State → State)
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
