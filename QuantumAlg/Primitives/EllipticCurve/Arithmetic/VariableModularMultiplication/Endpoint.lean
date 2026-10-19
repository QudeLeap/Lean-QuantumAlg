/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Schedule
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
-- Intentional exception: machine-readable source-owner markers keep full module names on one line.
set_option linter.style.longLine false

/-!
# QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Endpoint

Public declarations for
`QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Endpoint`.
-/
variable [params :
  QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.VariableModularMul.Parameters]

/-!
# Width-parameterized variable modular-multiplication endpoint

The proofs below identify the actual fixed-schedule gate program with modular
product accumulation for every positive width and odd positive modulus.
-/
/-! ## Forward clean semantics -/

/-! # Forward-fold clean semantics for variable modular multiplication -/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

-- The list induction keeps the physical carrier opaque behind cleanRegisters.
set_option exponentiation.threshold 2048 in
lemma forwardStep_cleanEndpoint :
    ∀ (roundBits : List (Fin params.width))
      (x : VariableModularMul.Data),
      forwardStep roundBits (VariableModularMul.cleanRegisters x) =
        VariableModularMul.cleanRegisters (forwardData roundBits x)
  | roundBits, x => by
      simpa only [forwardStep, forwardData] using
        (foldSteps_cleanEndpoint VariableModularMul.roundStep roundData
          VariableModularMul.cleanRegisters roundStep_cleanEndpoint roundBits x)

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Complete clean semantics -/

/-!
# Clean semantics of the variable modular-multiplication schedule

This aggregate keeps the recursive clean-state proofs separate from the
physical schedule.  The split bounds per-module elaboration memory while
retaining the same concrete circuit and folded step.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Physical endpoint -/

/-!
# Clean endpoint of the variable modular-multiplication schedule

This module connects the complete physical schedule to its exact clean pure
fold.  The subsequent arithmetic theorem identifies that fold with
`VariableModularMul.Data.addProduct`.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

/-- Exact clean-data action of the complete fixed-width physical schedule. -/
def cleanStepData (x : VariableModularMul.Data) : VariableModularMul.Data :=
  restoreData (params.width - 1)
    (VariableModularMul.Data.addSelected (lastBit)
      (forwardData (bits.take (params.width - 1)) x))

-- The fixed carrier remains opaque while the three already-verified clean
-- bridges are composed.
set_option exponentiation.threshold 2048 in
/-- The complete physical schedule maps a clean carrier to its exact pure
forward/final-bit/restoration fold and restores every work register. -/
lemma step_cleanEndpoint_exact (x : VariableModularMul.Data) :
    step (VariableModularMul.cleanRegisters x) =
      VariableModularMul.cleanRegisters (cleanStepData x) := by
  simp only [step, cleanStepData]
  rw [forwardStep_cleanEndpoint,
    VariableModularMul.selectedAddStep_cleanEndpoint,
    restoreStep_cleanEndpoint]

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Binary-prefix semantics -/

/-!
# Binary-prefix semantics of variable modular multiplication

The fixed schedule scans multiplier bits from low to high.  This module states
the closed semantic state after an arbitrary prefix and proves the symbolic
one-round recurrence without unfolding the concrete params.width-round schedule.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

/-- Closed clean state after processing the lowest `rounds` multiplier bits. -/
def prefixData (rounds : Nat) (x : VariableModularMul.Data) :
    VariableModularMul.Data where
  multiplier := x.multiplier
  multiplicand := (2 : ZMod params.modulus.val) ^ rounds *
    x.multiplicand
  accumulator := x.accumulator +
    ((x.multiplier.val % 2 ^ rounds : Nat) :
      ZMod params.modulus.val) *
      x.multiplicand

/-- One actual selected-add/doubling data round advances the closed binary
prefix invariant by one bit. -/
lemma roundData_prefixData (round : Fin params.width)
    (x : VariableModularMul.Data) :
    roundData round (prefixData round.val x) =
      prefixData (round.val + 1) x := by
  cases x with
  | mk multiplier multiplicand accumulator =>
      have hdecompCast :
          (((multiplier.val % 2 ^ (round.val + 1) : Nat) :
              ZMod params.modulus.val)) =
            ((multiplier.val % 2 ^ round.val : Nat) :
              ZMod params.modulus.val) +
              ((multiplier.val.testBit round.val).toNat :
                ZMod params.modulus.val) *
                (2 : ZMod params.modulus.val) ^ round.val := by
        rw [Comparator.mod_two_pow_succ_decomp]
        push_cast
        rfl
      cases hbit : multiplier.val.testBit round.val
      · simp only [roundData, prefixData, doubledData, scaleMultiplicand,
          VariableModularMul.Data.addSelected, hbit, Bool.false_eq_true,
          ↓reduceIte, VariableModularMul.twoUnit, ZMod.coe_unitOfCoprime]
        congr 1
        · rw [pow_succ]
          ring
        · rw [hdecompCast]
          simp [hbit]
      · simp only [roundData, prefixData, doubledData, scaleMultiplicand,
          VariableModularMul.Data.addSelected, hbit, ↓reduceIte,
          VariableModularMul.twoUnit, ZMod.coe_unitOfCoprime]
        congr 1
        · rw [pow_succ]
          ring
        · rw [hdecompCast]
          simp [hbit]
          ring

/-- Processing no multiplier bits leaves the semantic data unchanged. -/
@[simp] lemma prefixData_zero (x : VariableModularMul.Data) :
    prefixData 0 x = x := by
  cases x
  simp [prefixData, Nat.mod_one]

omit params in
/-- The finite index at a valid position is the next element appended to the
corresponding canonical low-to-high prefix. -/
lemma finRange_take_succ {width : Nat} (round : Fin width) :
    (List.finRange width).take (round.val + 1) =
      (List.finRange width).take round.val ++ [round] := by
  have hround :
      round.val < (List.finRange width).length := by
    simpa only [List.length_finRange] using round.isLt
  have hat :
      (List.finRange width)[round.val]'hround = round := by
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  simpa only [hat] using
    (List.take_concat_get'
      (List.finRange width) round.val hround).symm

/-- The clean semantic forward fold over the first `rounds` canonical bit
indices is exactly the closed low-bit prefix state. -/
lemma forwardData_finRange_take :
    ∀ (rounds : Nat), rounds ≤ params.width →
      ∀ x : VariableModularMul.Data,
        forwardData
            ((List.finRange params.width).take rounds) x =
          prefixData rounds x
  | 0, _, x => by
      simp only [List.take_zero, forwardData, foldSteps, prefixData_zero]
  | rounds + 1, hrounds, x => by
      let round : Fin params.width :=
        ⟨rounds, Nat.lt_of_succ_le hrounds⟩
      have hprefix := finRange_take_succ round
      have hinduction := forwardData_finRange_take rounds
        (Nat.le_trans (Nat.le_succ rounds) hrounds) x
      calc
        forwardData
            ((List.finRange params.width).take (rounds + 1)) x =
            forwardData
              ((List.finRange params.width).take rounds ++ [round]) x := by
              simpa only [round, Nat.succ_eq_add_one] using
                congrArg (fun indices => forwardData indices x) hprefix
        _ = roundData round
              (forwardData
                ((List.finRange params.width).take rounds) x) := by
              simp only [forwardData, foldSteps_append, foldSteps]
        _ = roundData round (prefixData rounds x) :=
              congrArg (roundData round) hinduction
        _ = prefixData (rounds + 1) x := by
              simpa only [round, Nat.succ_eq_add_one] using
                roundData_prefixData round x

/-- The schedule's explicit bit list is the canonical finite range. -/
lemma bits_eq_finRange :
    bits = List.finRange params.width := by
  change List.ofFn (fun bit : Fin params.width => bit) = List.finRange params.width
  exact List.ofFn_id params.width

/-- The first (params.width - 1) physical rounds reach the exact closed
(params.width - 1)-bit prefix
state used by the final selected-add stage. -/
lemma forwardData_bits_take_init (x : VariableModularMul.Data) :
    forwardData (bits.take (params.width - 1)) x = prefixData (params.width - 1) x := by
  rw [bits_eq_finRange]
  exact forwardData_finRange_take (params.width - 1) (Nat.sub_le _ _) x

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Final selected-add semantics -/

/-!
# Final selected-add semantics for variable modular multiplication

The first (params.width - 1) rounds establish the low-bit prefix invariant.  This module
shows that the final selected add completes the full params.width-bit product while
leaving the source scaled for the subsequent inverse-doubling restoration.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

/-- Clean state after the final selected add and before source restoration. -/
def preRestoreData (x : VariableModularMul.Data) :
    VariableModularMul.Data where
  multiplier := x.multiplier
  multiplicand :=
    (2 : ZMod params.modulus.val) ^ (params.width - 1) * x.multiplicand
  accumulator := x.accumulator + x.multiplier * x.multiplicand

set_option exponentiation.threshold 2048 in
/-- The last selected add completes the params.width-bit multiplier decomposition. -/
lemma finalSelected_prefixData (x : VariableModularMul.Data) :
    VariableModularMul.Data.addSelected lastBit (prefixData (params.width - 1) x) =
      preRestoreData x := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  have hpos : 0 < params.width := params.widthPos
  have hwidth : params.width - 1 + 1 = params.width := by
    omega
  have hmod :
      x.multiplier.val % 2 ^ params.width = x.multiplier.val := by
    exact Nat.mod_eq_of_lt
      ((ZMod.val_lt x.multiplier).trans
        VariableModularMul.modulus_lt_capacity)
  have hdecompCast :
      (((x.multiplier.val % 2 ^ params.width : Nat) :
          ZMod params.modulus.val)) =
        ((x.multiplier.val % 2 ^ (params.width - 1) : Nat) :
          ZMod params.modulus.val) +
          ((x.multiplier.val.testBit (params.width - 1)).toNat :
            ZMod params.modulus.val) *
            (2 : ZMod params.modulus.val) ^ (params.width - 1) := by
    calc
      (((x.multiplier.val % 2 ^ params.width : Nat) :
          ZMod params.modulus.val)) =
          ((x.multiplier.val % 2 ^ ((params.width - 1) + 1) : Nat) :
            ZMod params.modulus.val) := by rw [hwidth]
      _ = ((x.multiplier.val % 2 ^ (params.width - 1) +
              (x.multiplier.val.testBit (params.width - 1)).toNat * 2 ^ (params.width - 1) : Nat) :
            ZMod params.modulus.val) := by
            rw [Comparator.mod_two_pow_succ_decomp]
      _ = _ := by
            push_cast
            rfl
  have hbinary :
      ((x.multiplier.val % 2 ^ (params.width - 1) : Nat) :
          ZMod params.modulus.val) +
          ((x.multiplier.val.testBit (params.width - 1)).toNat :
            ZMod params.modulus.val) *
            (2 : ZMod params.modulus.val) ^ (params.width - 1) =
        x.multiplier := by
    rw [← hdecompCast, hmod, ZMod.natCast_zmod_val]
  cases x with
  | mk multiplier multiplicand accumulator =>
      cases hbit : multiplier.val.testBit (params.width - 1)
      · simp only [VariableModularMul.Data.addSelected, prefixData,
          preRestoreData, lastBit, hbit, Bool.false_eq_true, ↓reduceIte]
        congr 1
        have hbinaryFalse := hbinary
        simp only [hbit, Bool.toNat_false, Nat.cast_zero, zero_mul, add_zero]
          at hbinaryFalse
        rw [hbinaryFalse]
        simp
      · simp only [VariableModularMul.Data.addSelected, prefixData,
          preRestoreData, lastBit, hbit, ↓reduceIte]
        congr 1
        have hbinaryTrue := hbinary
        simp only [hbit, Bool.toNat_true, Nat.cast_one, one_mul] at hbinaryTrue
        calc
              accumulator +
                ((multiplier.val % 2 ^ (params.width - 1) : Nat) :
                  ZMod params.modulus.val) * multiplicand +
              (2 : ZMod params.modulus.val) ^ (params.width - 1) *
                multiplicand =
              accumulator +
                (((multiplier.val % 2 ^ (params.width - 1) : Nat) :
                    ZMod params.modulus.val) +
                  (2 : ZMod params.modulus.val) ^ (params.width - 1)) *
                    multiplicand := by ring
          _ = accumulator + multiplier * multiplicand := by rw [hbinaryTrue]

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Restoration algebra -/

/-!
# Restoration algebra for variable modular multiplication

This module identifies the inverse-doubling fold with multiplication by a
power of the fixed inverse-two unit.  At the production length of (params.width - 1) rounds,
that power cancels the source scaling left by the forward schedule.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

/-- Closed semantic form of `rounds` inverse source-doubling steps. -/
def inverseScaleData (rounds : Nat) (x : VariableModularMul.Data) :
    VariableModularMul.Data where
  multiplier := x.multiplier
  multiplicand :=
    (inverseTwoUnit : ZMod params.modulus.val) ^ rounds *
      x.multiplicand
  accumulator := x.accumulator

/-- Adding one inverse-doubling before a closed restoration fold increments
its exponent by one. -/
lemma inverseScaleData_after_inverseDoubled (rounds : Nat)
    (x : VariableModularMul.Data) :
    inverseScaleData rounds (inverseDoubledData x) =
      inverseScaleData (rounds + 1) x := by
  cases x
  simp only [inverseScaleData, inverseDoubledData, scaleMultiplicand]
  congr 1
  rw [pow_succ]
  ring

/-- The abstract restoration fold has the expected inverse-power closed form. -/
lemma restoreData_eq_inverseScaleData :
    ∀ (rounds : Nat) (x : VariableModularMul.Data),
      restoreData rounds x = inverseScaleData rounds x
  | 0, x => by
      simp [restoreData, iterateSteps, inverseScaleData]
  | rounds + 1, x => by
      simp only [restoreData, iterateSteps]
      calc
        iterateSteps inverseDoubledData rounds (inverseDoubledData x) =
            inverseScaleData rounds (inverseDoubledData x) := by
              simpa only [restoreData] using
                restoreData_eq_inverseScaleData rounds (inverseDoubledData x)
        _ = inverseScaleData (rounds + 1) x :=
          inverseScaleData_after_inverseDoubled rounds x

set_option exponentiation.threshold 2048 in
/-- The (params.width - 1) inverse doublings exactly restore the scaled source left after the
final selected add, while preserving the completed product accumulation. -/
lemma restoreData_preRestoreData (x : VariableModularMul.Data) :
    restoreData (params.width - 1) (preRestoreData x) =
      VariableModularMul.Data.addProduct x := by
  have htwo :
      (VariableModularMul.twoUnit :
          ZMod params.modulus.val) =
        (2 : ZMod params.modulus.val) := by
    simp only [VariableModularMul.twoUnit, ZMod.coe_unitOfCoprime,
      Nat.cast_ofNat]
  have hcancel :
      (inverseTwoUnit : ZMod params.modulus.val) ^ (params.width - 1) *
          (2 : ZMod params.modulus.val) ^ (params.width - 1) = 1 := by
    rw [← htwo, ← mul_pow]
    simp [inverseTwoUnit]
  rw [restoreData_eq_inverseScaleData]
  cases x with
  | mk multiplier multiplicand accumulator =>
      simp only [inverseScaleData, preRestoreData,
        VariableModularMul.Data.addProduct]
      rw [← mul_assoc, hcancel, one_mul]

end


end VariableModularMulSchedule
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

/-! ## Full-product endpoint -/

/-!
# Complete variable modular-multiplication endpoint

This module joins the physical clean-state endpoint, the low-to-high binary
prefix invariant, the final selected add, and inverse source restoration.  The
result is the exact full-product action of the actual fixed params.width-bit schedule.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMulSchedule

noncomputable section

/-- The exact pure fold of the production schedule is modular product
accumulation with both variable inputs preserved. -/
lemma cleanStepData_eq_addProduct (x : VariableModularMul.Data) :
    cleanStepData x = VariableModularMul.Data.addProduct x := by
  simp only [cleanStepData]
  rw [forwardData_bits_take_init, finalSelected_prefixData,
    restoreData_preRestoreData]

set_option exponentiation.threshold 2048 in
/-- The actual fixed params.width-bit circuit restores all work registers and both
variable inputs while adding their modular product into the accumulator. -/
lemma step_cleanEndpoint (x : VariableModularMul.Data) :
    step (VariableModularMul.cleanRegisters x) =
      VariableModularMul.cleanRegisters
        (VariableModularMul.Data.addProduct x) := by
  rw [step_cleanEndpoint_exact, cleanStepData_eq_addProduct]

set_option exponentiation.threshold 2048 in
/-- Normalized computational-basis form of the complete clean product
endpoint for the same actual schedule whose strict resources are projected. -/
lemma circuit_applyNormalized_clean_ket
    {environment : OracleModel.empty.Interpretation} (x : VariableModularMul.Data) :
    circuit.applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical VariableModularMul.rawEncoding.width).basisEquiv.symm
            (VariableModularMul.encoding.encode
              (VariableModularMul.cleanRegisters x)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical VariableModularMul.rawEncoding.width).basisEquiv.symm
          (VariableModularMul.encoding.encode
            (VariableModularMul.cleanRegisters
              (VariableModularMul.Data.addProduct x)))) := by
  have h := (realizes (environment := environment)).apply_encoded_ket
    (VariableModularMul.cleanRegisters x)
  rw [step_cleanEndpoint x] at h
  exact h

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
end
