/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stages
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Accumulate

/-!
# Actual all-width modular multiply-accumulate

The source is scanned from least significant to most significant bit. Each
actual stage adds the independently precomputed residue `a * 2^i mod N`.
This combines the proved pivot-flip offset [G17, paper.tex:319-334] with
the binary selected-add recurrence [VBE95, 9511018.tex:333-367]. The source
and target are the only quantum words, and both are retained at the output.
Zero coefficients, even moduli, and modulus one require no special input state.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

/-- Execute the first in-bounds source-bit stages in their actual sequential order. -/
def prefixProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (count : Nat) → count ≤ width → UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum
  | 0, _ => UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum
  | index + 1, within => (prefixProgram width modulus coefficient index (by omega)).seq
      (stageProgram width ⟨index, by omega⟩ modulus
        (accumulateConstant modulus coefficient index))

/-- Independent arithmetic output of an executed prefix. -/
def prefixOutput {width : Nat} (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat)
    (state : Registers width) : Registers width :=
  (state.1, accumulateWordPrefix modulus coefficient state.1 state.2 count)

lemma gidneyAccumulatePrefix_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient count : Nat) (within : count ≤ width) :
    UnitaryCircuit.Realizes (encoding width)
      (prefixProgram width modulus coefficient count within) environment
      (prefixOutput modulus coefficient count) := by
  induction count with
  | zero =>
      apply (UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
        (encoding width) (QubitLayout.canonical (encoding width).width) environment).congrStep
      rintro ⟨source, target⟩
      rfl
  | succ index ih =>
      apply ((ih (by omega)).seq
        (gidneyStage_realizes width ⟨index, by omega⟩ modulus
          (accumulateConstant modulus coefficient index))).congrStep
      rintro ⟨source, target⟩
      rfl

/-- The circuit-facing independent event envelope is linear in the number of scanned bits. -/
lemma gidneyAccumulatePrefix_event_count_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus coefficient count within).eventCost.card ≤
      count * stageEventBound width := by
  induction count with
  | zero =>
      change 0 ≤ 0 * stageEventBound width
      omega
  | succ index ih =>
      change ((prefixProgram width modulus coefficient index (by omega)).seq
        (stageProgram width ⟨index, by omega⟩ modulus
          (accumulateConstant modulus coefficient index))).eventCost.card ≤ _
      rw [UnitaryCircuit.seq_eventCost, Multiset.card_add, Nat.succ_mul]
      have hprefix := ih (by omega)
      have hstage := gidneyStage_event_count_bound width ⟨index, by omega⟩ modulus
        (accumulateConstant modulus coefficient index)
      omega

/-- The complete selected-add sequence on the original two-word carrier. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  prefixProgram width modulus coefficient width (Nat.le_refl width)

/-- Exact all-label coherent action of the actual complete multiply-accumulate program. -/
lemma gidneyAccumulate_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width modulus coefficient) environment
      (prefixOutput modulus coefficient width) :=
  gidneyAccumulatePrefix_realizes width modulus coefficient width (Nat.le_refl width)

/-- The complete carrier is the original source and target, with no external borrowed bit. -/
lemma gidneyAccumulate_interface (width : Nat) :
    (encoding width).width = 2 * width ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (2 * width) :=
  gidneyStage_interface width

/-- Complete source preservation is part of the independent output on every label. -/
lemma gidneyAccumulate_source (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (state : Registers width) :
    (prefixOutput modulus coefficient width state).1 = state.1 := rfl

/-- On canonical accumulators, the exact output is `y + a*x mod N` for every source word. -/
lemma gidneyAccumulate_valid (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (state : Registers width) (valid : state.2.val < modulus.val) :
    (prefixOutput modulus coefficient width state).2.val =
      (state.2.val + coefficient * state.1.val) % modulus.val :=
  accumulateWordPrefix_full modulus coefficient state.1 state.2 valid

/-- The exact extension fixes all noncanonical accumulator labels and preserves the source. -/
lemma gidneyAccumulate_outside (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (state : Registers width) (outside : modulus.val ≤ state.2.val) :
    prefixOutput modulus coefficient width state = state := by
  rcases state with ⟨source, target⟩
  exact congrArg (fun word => (source, word))
    (accumulateWordPrefix_outside modulus coefficient source target outside width)

/-- The actual full program meets the independently stated numerical event envelope. -/
lemma gidneyAccumulate_event_count_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (program width modulus coefficient).eventCost.card ≤ width * stageEventBound width :=
  gidneyAccumulatePrefix_event_count_bound width modulus coefficient width (Nat.le_refl width)

/-- External encoded references are preserved jointly by the exact two-word circuit. -/
lemma gidneyAccumulate_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (layout := QubitLayout.canonical ((encoding width).width + reference.width))
      (UnitaryCircuit.onBinaryPrefix reference.width (program width modulus coefficient))
      environment
      (fun state => (prefixOutput modulus coefficient width state.1, state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (gidneyAccumulate_realizes width modulus coefficient)

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
