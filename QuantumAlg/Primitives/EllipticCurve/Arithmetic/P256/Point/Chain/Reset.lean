/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Unlookup
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Matrix
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Actual original-word measurement/reset inside the 854-system point bank

The actual parallel H, chronological MZ writes, paid mask packing and
stored-mask parallel X correction reuse the supplied original word.
Complete incoming Store/history fibers remain in the inherited operator
equation. The mathematical branch labels below grant no executable reset.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Reset

noncomputable section

open Execution EncodedBit.WindowLookup
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

def circuit (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  measuredResetWordCircuit (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask

def zeroOutcome : Fin (2 ^ 256) := ⟨0, Nat.two_pow_pos 256⟩

def namedOutcome (port : WordPort) (value : Fin (2 ^ 256)) (state : Window.Raw) : Window.Raw :=
  resultSetConstant (Window.resultWord port) value state

def resetState (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (store : Store ctx) (state : Window.Raw) : Window.Raw :=
  measuredWordResetStep (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires (Window.resultWord port) output mask store state

/-- Every named physical branch is reset to the same whole label, with that original word zero. -/
lemma resetState_namedOutcome (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits 256)) (store : Store ctx) (value : Fin (2 ^ 256))
    (state : Window.Raw) :
    resetState (services := services) port sameWires output mask store
      (namedOutcome port value state) = namedOutcome port zeroOutcome state :=
  measuredWordResetStep_set_eq_zero (QubitLayout.canonical _) sameWires (Window.resultWord port)
    (Window.resultWord_distinct port) output distinct mask store value state

lemma resetState_bit_zero (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits 256)) (store : Store ctx) (state : Window.Raw) (index : Fin 256) :
    ((Window.resultWord port).bit index).get
      (resetState (services := services) port sameWires output mask store state) = false :=
  measuredWordResetStep_zero (QubitLayout.canonical _) sameWires (Window.resultWord port)
    (Window.resultWord_distinct port) output distinct mask store state index

/-- The actual reset changes no original position outside its measured word. -/
lemma resetState_other (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (store : Store ctx) (observed : EncodedBit Window.encoding)
    (outside : ∀ index, ((Window.resultWord port).bit index).wire ≠ observed.wire)
    (state : Window.Raw) :
    observed.get (resetState (services := services) port sameWires output mask store state) =
      observed.get state :=
  EncodedBit.Word.xorConstantStep_get_observed_of_target_ne (Window.resultWord port) _
    observed outside state

/-- In particular the original numerical Y is zero after its actual physical reset. -/
lemma resetState_numerator_zero
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits 256)) (store : Store ctx) (state : Window.Raw) :
    Frame.numerator
      (resetState (services := services) .numerator sameWires output mask store state).1 = 0 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have zero := resetState_bit_zero (services := services) .numerator sameWires output distinct
    mask store state index
  change (Window.pointBit (Frame.numeratorBit index)).get _ = false at zero
  rw [Window.pointBit_get, Frame.numeratorBit_get] at zero
  exact zero.trans (Nat.zero_testBit index.val).symm

/-- The exact operator identity retains all original Store/history overwrite fibers. -/
lemma circuit_block_matrix (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (circuit (services := services) port sameWires output mask).Path)))
    (row column : (Register.prod ctx.register Reference).Index) :
    (((circuit port sameWires output mask).execute environment Reference state).block result).matrix
        row column =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if measuredWordRecord (oracles := .empty) (services := services)
            (QubitLayout.canonical _) sameWires (Window.resultWord port)
            (Window.resultWord_distinct port) output mask original path = result then
          (measuredWordKraus (oracles := .empty) (services := services)
            (QubitLayout.canonical _) sameWires (Window.resultWord port)
            (Window.resultWord_distinct port) output mask original.1 path
              environment.quantum Reference * (state.block original).matrix *
            (measuredWordKraus (oracles := .empty) (services := services)
              (QubitLayout.canonical _) sameWires (Window.resultWord port)
              (Window.resultWord_distinct port) output mask original.1 path
                environment.quantum Reference).conjTranspose) row column
        else 0 := by
  refine (measuredResetWordCircuit_block_matrix (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask environment state result
      row column).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  by_cases same : measuredWordRecord (oracles := .empty) (services := services)
      (QubitLayout.canonical _) sameWires (Window.resultWord port)
      (Window.resultWord_distinct port) output mask original path = result
  · rw [if_pos same, if_pos same]
  · rw [if_neg same, if_neg same]

end

end Reset

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
