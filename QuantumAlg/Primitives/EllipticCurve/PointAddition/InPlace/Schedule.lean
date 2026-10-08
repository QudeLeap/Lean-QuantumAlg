/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.ControlledOperations
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Montgomery.Inversion

/-!
# Seventeen-stage in-place controlled point-addition schedule

This module implements Algorithm 1 on a compact carrier
[RNSL17, ECDLP.tex:514-530].  Both inversion cleanup calls are compiled as the
reverse of the corresponding forward ledger; this is the reversible
implementation of the paper's repeated `inv_modp` call.  All stages share one
`Layout.Registers` carrier.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace Schedule

noncomputable section

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- Classical `3*x2 mod p` used by stage 9. -/
def tripleConstant (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (x2 : Word fieldTail.succ) :
    Word fieldTail.succ :=
  CompactCorrection.modularSumFixedWord fieldTail p hpPos hp x2
    (CompactCorrection.modularSumFixedWord fieldTail p hpPos hp x2 x2)

@[simp] theorem tripleConstant_val (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (x2 : Word fieldTail.succ) :
    (tripleConstant fieldTail p hpPos hp x2).val =
      (x2.val + (x2.val + x2.val) % p) % p :=
  rfl

/-- Exact corrected word written by one forward compact inversion call. -/
def inversionOutput
    (fieldTail counterTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (input target : Word fieldTail.succ) : Word fieldTail.succ :=
  let pWord : Word fieldTail.succ := ⟨p, hp⟩
  let seed := CompactCertificate.compactInitialRegisters
    fieldTail counterTail pWord input target
  let folded := CompactCertificate.compactFoldStep
    fieldTail counterTail hfit seed
  let reduced := CompactCorrection.canonicalResidueWord
    fieldTail p hpPos hp folded.core.rCoeff
  let corrected := CompactCorrection.correctionResiduePrefix
    fieldTail p hpPos hp folded.core.counter.val fieldTail.succ reduced
  CompactCorrection.modularDifferenceWord fieldTail p hpPos hp target
    (CompactCorrection.truncateFixedWord fieldTail.succ corrected)

/-- Exact canonical Montgomery product emitted by the shared multiply
kernel. -/
def productWord
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (multiplier coefficient : Word fieldTail.succ) : Word fieldTail.succ :=
  let coefficientWide :=
    CompactCorrection.widenFixedWord fieldTail.succ coefficient
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficientWide
      target := 0 }
  (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp multiplier
    (List.finRange fieldTail.succ) residues).target

/-- Point-carrier form of the compact inversion endpoint. -/
theorem inversionGates_cleanEndpoint
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p)
    (control : Bool) (mutableY «λ» input target : Word fieldTail.succ)
    (hinput : 0 < input.val) (hcoprime : Nat.Coprime p input.val)
    (htarget : target.val < p) :
    EncodedBit.GateSpec.stepList
        (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
          hwidth)
        (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
          control mutableY «λ» ⟨p, hp⟩ input target) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        control mutableY «λ» ⟨p, hp⟩ input
        (inversionOutput fieldTail counterTail p hpPos hp hfit input target) := by
  have h := MontgomeryInversion.step_cleanEndpoint fieldTail counterTail hfit
    hcapacity hwidth hcounterWidth control mutableY «λ» ⟨p, hp⟩ input
      target (Nat.odd_iff.mp hpOdd) hinput hcoprime htarget
  dsimp only at h
  simpa [MontgomeryInversion.step, MontgomeryInversion.inversionState,
    MontgomeryOperations.cleanState,
    CompactCertificate.compactInitialRegisters, inversionOutput] using h

/-- Clean-output multiplication into `lambda`. -/
theorem t0IntoLambdaGates_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY mutableX t0 : Word fieldTail.succ)
    (ht0 : t0.val < p) :
    EncodedBit.GateSpec.stepList
        (MontgomeryOperations.t0IntoLambdaGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY 0 ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY (productWord fieldTail p hpPos hp mutableY t0) ⟨p, hp⟩
        mutableX t0 := by
  have h := MontgomeryOperations.t0IntoLambdaStep_cleanEndpoint fieldTail
    counterWidth p hpPos hp hpOdd control mutableY mutableX t0 ht0
  dsimp only at h
  simpa [MontgomeryOperations.t0IntoLambdaStep, productWord,
    MontgomeryOperations.cleanState, RegisterRouting.lambdaPort] using h.1

/-- Equal-output multiplication clears `lambda`. -/
theorem t0IntoLambdaGates_equalEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY mutableX t0 : Word fieldTail.succ)
    (ht0 : t0.val < p) :
    EncodedBit.GateSpec.stepList
        (MontgomeryOperations.t0IntoLambdaGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY (productWord fieldTail p hpPos hp mutableY t0) ⟨p, hp⟩
          mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY 0 ⟨p, hp⟩ mutableX t0 := by
  have h := MontgomeryOperations.t0IntoLambdaStep_equalEndpoint fieldTail
    counterWidth p hpPos hp hpOdd control mutableY mutableX t0 ht0
  dsimp only at h
  simpa [MontgomeryOperations.t0IntoLambdaStep, productWord,
    MontgomeryOperations.cleanState, RegisterRouting.lambdaPort] using h.1

/-- Clean-output multiplication into mutable `y1`. -/
theorem xIntoYGates_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) («λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) :
    EncodedBit.GateSpec.stepList
        (MontgomeryOperations.xIntoYGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control 0
          «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        (productWord fieldTail p hpPos hp «λ» mutableX) «λ» ⟨p, hp⟩
        mutableX t0 := by
  have h := MontgomeryOperations.xIntoYStep_cleanEndpoint fieldTail
    counterWidth p hpPos hp hpOdd control «λ» mutableX t0 hx
  dsimp only at h
  simpa [MontgomeryOperations.xIntoYStep, productWord,
    MontgomeryOperations.cleanState, RegisterRouting.mutableYPort] using h.1

/-- Equal-output multiplication clears mutable `y1`. -/
theorem xIntoYGates_equalEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) («λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) :
    EncodedBit.GateSpec.stepList
        (MontgomeryOperations.xIntoYGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          (productWord fieldTail p hpPos hp «λ» mutableX) «λ» ⟨p, hp⟩
          mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control 0
        «λ» ⟨p, hp⟩ mutableX t0 := by
  have h := MontgomeryOperations.xIntoYStep_equalEndpoint fieldTail
    counterWidth p hpPos hp hpOdd control «λ» mutableX t0 hx
  dsimp only at h
  simpa [MontgomeryOperations.xIntoYStep, productWord,
    MontgomeryOperations.cleanState, RegisterRouting.mutableYPort] using h.1

/-- Clean-output Montgomery squaring into `t0`. -/
theorem squareLambdaGates_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY «λ» mutableX : Word fieldTail.succ)
    (hlambda : «λ».val < p) :
    EncodedBit.GateSpec.stepList
        (MontgomeryOperations.squareLambdaGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩ mutableX
        (productWord fieldTail p hpPos hp «λ» «λ») := by
  have h := MontgomeryOperations.squareLambdaStep_cleanEndpoint fieldTail
    counterWidth p hpPos hp hpOdd control mutableY «λ» mutableX hlambda
  dsimp only at h
  simpa [MontgomeryOperations.squareLambdaStep, productWord,
    MontgomeryOperations.cleanState, RegisterRouting.t0Port] using h.1

/-- Equal-output Montgomery squaring clears `t0`. -/
theorem squareLambdaGates_equalEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY «λ» mutableX : Word fieldTail.succ)
    (hlambda : «λ».val < p) :
    EncodedBit.GateSpec.stepList
        (MontgomeryOperations.squareLambdaGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX
          (productWord fieldTail p hpPos hp «λ» «λ»)) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩ mutableX 0 := by
  have h := MontgomeryOperations.squareLambdaStep_equalEndpoint fieldTail
    counterWidth p hpPos hp hpOdd control mutableY «λ» mutableX hlambda
  dsimp only at h
  simpa [MontgomeryOperations.squareLambdaStep, productWord,
    MontgomeryOperations.cleanState, RegisterRouting.t0Port] using h.1

/-- Every emitted Montgomery product is a canonical field residue. -/
theorem productWord_lt
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (multiplier coefficient : Word fieldTail.succ)
    (hcoefficient : coefficient.val < p) :
    (productWord fieldTail p hpPos hp multiplier coefficient).val < p := by
  let coefficientWide :=
    CompactCorrection.widenFixedWord fieldTail.succ coefficient
  let scaled := MontgomeryMultiplication.inverseScaleWord fieldTail p hpPos hp
    fieldTail.succ coefficientWide
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := scaled, target := 0 }
  have hwide : coefficientWide.val < p := by
    simpa [coefficientWide, CompactCorrection.widenFixedWord] using
      hcoefficient
  have hscaled : scaled.val < p :=
    MontgomeryMultiplication.inverseScaleWord_lt fieldTail p hpPos hp hpOdd
      fieldTail.succ coefficientWide hwide
  have hzero : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  exact (MontgomeryMultiplication.residueRounds_bounds fieldTail p hpPos hp
    multiplier (List.finRange fieldTail.succ) residues hscaled hzero).2

/-- Every compact inversion output is a canonical field residue. -/
theorem inversionOutput_lt
    (fieldTail counterTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (input target : Word fieldTail.succ) :
    (inversionOutput fieldTail counterTail p hpPos hp hfit input target).val <
      p := by
  simp [inversionOutput, CompactCorrection.modularDifferenceWord_val,
    Nat.mod_lt _ hpPos]

/-- Public input data for the straight-line schedule. -/
structure Input (fieldTail : Nat) where
  control : Bool
  x1 : Word fieldTail.succ
  y1 : Word fieldTail.succ
  x2 : Word fieldTail.succ
  y2 : Word fieldTail.succ

namespace Input

variable {fieldTail : Nat}

def xAfterSubtract (data : Input fieldTail) (p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) : Word fieldTail.succ :=
  CompactCorrection.modularDifferenceWord fieldTail p hpPos hp data.x1 data.x2

def yAfterSelectedSubtract (data : Input fieldTail) (p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) : Word fieldTail.succ :=
  if data.control then
    CompactCorrection.modularDifferenceWord fieldTail p hpPos hp data.y1 data.y2
  else data.y1

def firstInverse (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  inversionOutput fieldTail counterTail p hpPos hp hfit
    (data.xAfterSubtract p hpPos hp) 0

def slope (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  productWord fieldTail p hpPos hp (data.yAfterSelectedSubtract p hpPos hp)
    (data.firstInverse counterTail p hpPos hp hfit)

def slopeSquare (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  productWord fieldTail p hpPos hp
    (data.slope counterTail p hpPos hp hfit)
    (data.slope counterTail p hpPos hp hfit)

def xAfterSelectedSquareSubtract (data : Input fieldTail)
    (counterTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  if data.control then
    CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
      (data.xAfterSubtract p hpPos hp)
      (data.slopeSquare counterTail p hpPos hp hfit)
  else data.xAfterSubtract p hpPos hp

def xBeforeNegation (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  if data.control then
    CompactCorrection.modularSumFixedWord fieldTail p hpPos hp
      (data.xAfterSelectedSquareSubtract counterTail p hpPos hp hfit)
      (tripleConstant fieldTail p hpPos hp data.x2)
  else data.xAfterSelectedSquareSubtract counterTail p hpPos hp hfit

def yBeforeFinalSubtract (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  productWord fieldTail p hpPos hp
    (data.slope counterTail p hpPos hp hfit)
    (data.xBeforeNegation counterTail p hpPos hp hfit)

def secondInverse (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  inversionOutput fieldTail counterTail p hpPos hp hfit
    (data.xBeforeNegation counterTail p hpPos hp hfit) 0

def xAfterNegation (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  if data.control then
    CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0
      (data.xBeforeNegation counterTail p hpPos hp hfit)
  else data.xBeforeNegation counterTail p hpPos hp hfit

def outputY (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  if data.control then
    CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
      (data.yBeforeFinalSubtract counterTail p hpPos hp hfit) data.y2
  else data.yBeforeFinalSubtract counterTail p hpPos hp hfit

def outputX (data : Input fieldTail) (counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ) : Word fieldTail.succ :=
  CompactCorrection.modularSumFixedWord fieldTail p hpPos hp
    (data.xAfterNegation counterTail p hpPos hp hfit) data.x2

end Input

/-- Arithmetic side conditions needed by the two equal-output cleanup calls
and the two inversion domains.  These are field-level obligations, not claims
about the circuit execution. -/
structure CleanCertificate
    (fieldTail counterTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (data : Input fieldTail) : Prop where
  hpOdd : Odd p
  hx1 : data.x1.val < p
  hy1 : data.y1.val < p
  hx2 : data.x2.val < p
  hy2 : data.y2.val < p
  firstInputPositive : 0 < (data.xAfterSubtract p hpPos hp).val
  firstInputCoprime : Nat.Coprime p (data.xAfterSubtract p hpPos hp).val
  secondInputPositive :
    0 < (data.xBeforeNegation counterTail p hpPos hp hfit).val
  secondInputCoprime : Nat.Coprime p
    (data.xBeforeNegation counterTail p hpPos hp hfit).val
  firstProductClears :
    productWord fieldTail p hpPos hp
        (data.slope counterTail p hpPos hp hfit)
        (data.xAfterSubtract p hpPos hp) =
      data.yAfterSelectedSubtract p hpPos hp
  secondProductClears :
    productWord fieldTail p hpPos hp
        (data.yBeforeFinalSubtract counterTail p hpPos hp hfit)
        (data.secondInverse counterTail p hpPos hp hfit) =
      data.slope counterTail p hpPos hp hfit

/-- Folding a flattened list of stage ledgers agrees with left-to-right stage
execution. -/
private theorem stepList_flatten
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (ledgers : List (List (EncodedBit.GateSpec encoding))) (input : Data) :
    EncodedBit.GateSpec.stepList ledgers.flatten input =
      ledgers.foldl
        (fun state ledger => EncodedBit.GateSpec.stepList ledger state) input := by
  induction ledgers generalizing input with
  | nil => rfl
  | cons ledger rest ih =>
      simp only [List.flatten_cons, List.foldl_cons]
      rw [EncodedBit.GateSpec.stepList_append, ih]

/-- The ordered list of seventeen physical arithmetic ledgers implementing
Algorithm 1 [RNSL17, ECDLP.tex:514-530]. -/
def stageLedgers
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    List (List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ (counterTail + 2)))) :=
  [ ModularOperations.subtractConstantXGates fieldTail (counterTail + 2) p
      hp x2
  , ControlledOperations.subtractConstantYGates fieldTail (counterTail + 2)
      p hp y2
  , MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity hwidth
  , MontgomeryOperations.t0IntoLambdaGates fieldTail (counterTail + 2) p hp
  , MontgomeryOperations.xIntoYGates fieldTail (counterTail + 2) p hp
  , (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
      hwidth).reverse
  , MontgomeryOperations.squareLambdaGates fieldTail (counterTail + 2) p hp
  , ControlledOperations.subtractT0FromXGates fieldTail (counterTail + 2) p hp
  , ControlledOperations.addConstantXGates fieldTail (counterTail + 2) p hp
      (tripleConstant fieldTail p hpPos hp x2)
  , MontgomeryOperations.squareLambdaGates fieldTail (counterTail + 2) p hp
  , MontgomeryOperations.xIntoYGates fieldTail (counterTail + 2) p hp
  , MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity hwidth
  , MontgomeryOperations.t0IntoLambdaGates fieldTail (counterTail + 2) p hp
  , (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
      hwidth).reverse
  , ControlledOperations.negateXGates fieldTail (counterTail + 2) p hp
  , ControlledOperations.subtractConstantYGates fieldTail (counterTail + 2)
      p hp y2
  , ModularOperations.addConstantXGates fieldTail (counterTail + 2) p hp x2 ]

/-- Flattened native X/CNOT/Toffoli ledger for controlled point addition. -/
def gates
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ (counterTail + 2))) :=
  (stageLedgers fieldTail counterTail p hpPos hp hfit hcapacity hwidth
    x2 y2).flatten

/-- Folded semantic action of the complete seventeen-stage ledger. -/
def step
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ (counterTail + 2) →
      Layout.Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (gates fieldTail counterTail p hpPos hp hfit hcapacity hwidth x2 y2)

/-- The complete seventeen-stage ledger returns `lambda`, `t0`, history, and
all arithmetic work to the clean boundary while updating only the two mutable
coordinates. -/
theorem step_cleanEndpoint
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (data : Input fieldTail)
    (certificate : CleanCertificate fieldTail counterTail p hpPos hp hfit data) :
    step fieldTail counterTail p hpPos hp hfit hcapacity hwidth data.x2 data.y2
        (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
          data.control data.y1 0 ⟨p, hp⟩ data.x1 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control
        (data.outputY counterTail p hpPos hp hfit) 0 ⟨p, hp⟩
        (data.outputX counterTail p hpPos hp hfit) 0 := by
  let xA := data.xAfterSubtract p hpPos hp
  let yA := data.yAfterSelectedSubtract p hpPos hp
  let inv1 := data.firstInverse counterTail p hpPos hp hfit
  let slope := data.slope counterTail p hpPos hp hfit
  let square := data.slopeSquare counterTail p hpPos hp hfit
  let xB := data.xAfterSelectedSquareSubtract counterTail p hpPos hp hfit
  let xC := data.xBeforeNegation counterTail p hpPos hp hfit
  let yB := data.yBeforeFinalSubtract counterTail p hpPos hp hfit
  let inv2 := data.secondInverse counterTail p hpPos hp hfit
  let xD := data.xAfterNegation counterTail p hpPos hp hfit
  let yC := data.outputY counterTail p hpPos hp hfit
  let xOut := data.outputX counterTail p hpPos hp hfit
  have hclear1 : productWord fieldTail p hpPos hp slope xA = yA := by
    simpa only [slope, xA, yA] using certificate.firstProductClears
  have hclear2 : productWord fieldTail p hpPos hp yB inv2 = slope := by
    simpa only [slope, yB, inv2] using certificate.secondProductClears
  have hxA : xA.val < p := by
    change (data.x1.val + p - data.x2.val) % p < p
    exact Nat.mod_lt _ hpPos
  have hyA : yA.val < p := by
    simp only [yA, Input.yAfterSelectedSubtract]
    split
    · exact Nat.mod_lt _ hpPos
    · exact certificate.hy1
  have hinv1 : inv1.val < p := by
    exact inversionOutput_lt fieldTail counterTail p hpPos hp hfit xA 0
  have hslope : slope.val < p := by
    exact productWord_lt fieldTail p hpPos hp certificate.hpOdd yA inv1 hinv1
  have hsquare : square.val < p := by
    exact productWord_lt fieldTail p hpPos hp certificate.hpOdd slope slope
      hslope
  have hxB : xB.val < p := by
    simp only [xB, Input.xAfterSelectedSquareSubtract]
    split
    · exact Nat.mod_lt _ hpPos
    · simpa [xA] using hxA
  have htriple :
      (tripleConstant fieldTail p hpPos hp data.x2).val < p := by
    simp [tripleConstant, CompactCorrection.modularSumFixedWord_val,
      Nat.mod_lt _ hpPos]
  have hxC : xC.val < p := by
    simp only [xC, Input.xBeforeNegation]
    split
    · exact Nat.mod_lt _ hpPos
    · simpa [xB] using hxB
  have hyB : yB.val < p := by
    exact productWord_lt fieldTail p hpPos hp certificate.hpOdd slope xC hxC
  have hinv2 : inv2.val < p := by
    exact inversionOutput_lt fieldTail counterTail p hpPos hp hfit xC 0
  have hxD : xD.val < p := by
    simp only [xD, Input.xAfterNegation]
    split
    · exact Nat.mod_lt _ hpPos
    · simpa [xC] using hxC
  have h1 := ModularOperations.subtractConstantXStep_cleanEndpoint fieldTail
    (counterTail + 2) p hpPos hp data.control data.y1 0 data.x1 0 data.x2
      certificate.hx1 certificate.hx2
  have h2 := ControlledOperations.subtractConstantYStep_cleanEndpoint
    fieldTail (counterTail + 2) p hpPos hp data.control data.y1 0 xA data.y2
      certificate.hy1 certificate.hy2
  have h3 := inversionGates_cleanEndpoint fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth certificate.hpOdd data.control yA 0 xA 0
      certificate.firstInputPositive certificate.firstInputCoprime (by
        simpa using hpPos)
  have h4 := t0IntoLambdaGates_cleanEndpoint fieldTail (counterTail + 2) p
    hpPos hp certificate.hpOdd data.control yA xA inv1 hinv1
  have h5 := xIntoYGates_equalEndpoint fieldTail (counterTail + 2) p hpPos hp
    certificate.hpOdd data.control slope xA inv1 hxA
  have h6forward := inversionGates_cleanEndpoint fieldTail counterTail p hpPos
    hp hfit hcapacity hwidth hcounterWidth certificate.hpOdd data.control 0
      slope xA 0 certificate.firstInputPositive certificate.firstInputCoprime
      (by simpa using hpPos)
  have h6 :
      EncodedBit.GateSpec.stepList
          (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
            hwidth).reverse
          (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
            data.control 0 slope ⟨p, hp⟩ xA inv1) =
        MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
          data.control 0 slope ⟨p, hp⟩ xA 0 := by
    rw [show MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xA inv1 =
      EncodedBit.GateSpec.stepList
        (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
          hwidth)
        (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
          data.control 0 slope ⟨p, hp⟩ xA 0) by
      simpa [inv1, Input.firstInverse] using h6forward.symm]
    exact EncodedBit.GateSpec.stepList_reverse_stepList _ _
  have h7 := squareLambdaGates_cleanEndpoint fieldTail (counterTail + 2) p
    hpPos hp certificate.hpOdd data.control 0 slope xA hslope
  have h8 := ControlledOperations.subtractT0FromXStep_cleanEndpoint fieldTail
    (counterTail + 2) p hpPos hp data.control 0 slope xA square hxA hsquare
  have h9 := ControlledOperations.addConstantXStep_cleanEndpoint fieldTail
    (counterTail + 2) p hpPos hp data.control 0 slope xB square
      (tripleConstant fieldTail p hpPos hp data.x2) hxB htriple
  have h10 := squareLambdaGates_equalEndpoint fieldTail (counterTail + 2) p
    hpPos hp certificate.hpOdd data.control 0 slope xC hslope
  have h11 := xIntoYGates_cleanEndpoint fieldTail (counterTail + 2) p hpPos hp
    certificate.hpOdd data.control slope xC 0 hxC
  have h12 := inversionGates_cleanEndpoint fieldTail counterTail p hpPos hp
    hfit hcapacity hwidth hcounterWidth certificate.hpOdd data.control yB
      slope xC 0 certificate.secondInputPositive certificate.secondInputCoprime
      (by simpa using hpPos)
  have h13 := t0IntoLambdaGates_equalEndpoint fieldTail (counterTail + 2) p
    hpPos hp certificate.hpOdd data.control yB xC inv2 hinv2
  have h14forward := inversionGates_cleanEndpoint fieldTail counterTail p hpPos
    hp hfit hcapacity hwidth hcounterWidth certificate.hpOdd data.control yB 0
      xC 0 certificate.secondInputPositive certificate.secondInputCoprime
      (by simpa using hpPos)
  have h14 :
      EncodedBit.GateSpec.stepList
          (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
            hwidth).reverse
          (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
            data.control yB 0 ⟨p, hp⟩ xC inv2) =
        MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
          data.control yB 0 ⟨p, hp⟩ xC 0 := by
    rw [show MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB 0 ⟨p, hp⟩ xC inv2 =
      EncodedBit.GateSpec.stepList
        (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity
          hwidth)
        (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
          data.control yB 0 ⟨p, hp⟩ xC 0) by
      simpa [inv2, Input.secondInverse] using h14forward.symm]
    exact EncodedBit.GateSpec.stepList_reverse_stepList _ _
  have h15 := ControlledOperations.negateXStep_cleanEndpoint fieldTail
    (counterTail + 2) p hpPos hp data.control yB 0 xC hxC
  have h16 := ControlledOperations.subtractConstantYStep_cleanEndpoint
    fieldTail (counterTail + 2) p hpPos hp data.control yB 0 xD data.y2 hyB
      certificate.hy2
  have h17 := ModularOperations.addConstantXStep_cleanEndpoint fieldTail
    (counterTail + 2) p hpPos hp data.control yC 0 xD 0 data.x2 hxD
      certificate.hx2
  rw [step, gates, stepList_flatten]
  simp only [stageLedgers, List.foldl_cons, List.foldl_nil]
  rw [show EncodedBit.GateSpec.stepList
      (ModularOperations.subtractConstantXGates fieldTail (counterTail + 2) p
        hp data.x2)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control data.y1 0 ⟨p, hp⟩ data.x1 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control data.y1 0 ⟨p, hp⟩ xA 0 by
    simpa [ModularOperations.subtractConstantXStep, xA,
      Input.xAfterSubtract] using h1]
  rw [show EncodedBit.GateSpec.stepList
      (ControlledOperations.subtractConstantYGates fieldTail
        (counterTail + 2) p hp data.y2)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control data.y1 0 ⟨p, hp⟩ xA 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yA 0 ⟨p, hp⟩ xA 0 by
    simpa [ControlledOperations.subtractConstantYStep, yA,
      Input.yAfterSelectedSubtract] using h2]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity hwidth)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yA 0 ⟨p, hp⟩ xA 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yA 0 ⟨p, hp⟩ xA inv1 by
    simpa [inv1, Input.firstInverse] using h3]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryOperations.t0IntoLambdaGates fieldTail (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yA 0 ⟨p, hp⟩ xA inv1) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yA slope ⟨p, hp⟩ xA inv1 by
    simpa [slope, Input.slope] using h4]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryOperations.xIntoYGates fieldTail (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yA slope ⟨p, hp⟩ xA inv1) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xA inv1 by
    rw [← hclear1]
    exact h5]
  rw [h6]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryOperations.squareLambdaGates fieldTail (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xA 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xA square by
    simpa [square, Input.slopeSquare] using h7]
  rw [show EncodedBit.GateSpec.stepList
      (ControlledOperations.subtractT0FromXGates fieldTail
        (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xA square) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xB square by
    simpa [ControlledOperations.subtractT0FromXStep, xB,
      Input.xAfterSelectedSquareSubtract] using h8]
  rw [show EncodedBit.GateSpec.stepList
      (ControlledOperations.addConstantXGates fieldTail (counterTail + 2) p hp
        (tripleConstant fieldTail p hpPos hp data.x2))
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xB square) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xC square by
    simpa [ControlledOperations.addConstantXStep, xC,
      Input.xBeforeNegation] using h9]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryOperations.squareLambdaGates fieldTail (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xC square) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xC 0 by
    simpa [square, Input.slopeSquare] using h10]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryOperations.xIntoYGates fieldTail (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control 0 slope ⟨p, hp⟩ xC 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB slope ⟨p, hp⟩ xC 0 by
    simpa [yB, Input.yBeforeFinalSubtract] using h11]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryInversion.gates fieldTail counterTail p hfit hcapacity hwidth)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB slope ⟨p, hp⟩ xC 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB slope ⟨p, hp⟩ xC inv2 by
    simpa [inv2, Input.secondInverse] using h12]
  rw [show EncodedBit.GateSpec.stepList
      (MontgomeryOperations.t0IntoLambdaGates fieldTail (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB slope ⟨p, hp⟩ xC inv2) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB 0 ⟨p, hp⟩ xC inv2 by
    rw [← hclear2]
    exact h13]
  rw [h14]
  rw [show EncodedBit.GateSpec.stepList
      (ControlledOperations.negateXGates fieldTail (counterTail + 2) p hp)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB 0 ⟨p, hp⟩ xC 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB 0 ⟨p, hp⟩ xD 0 by
    simpa [ControlledOperations.negateXStep, xD,
      Input.xAfterNegation] using h15]
  rw [show EncodedBit.GateSpec.stepList
      (ControlledOperations.subtractConstantYGates fieldTail
        (counterTail + 2) p hp data.y2)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yB 0 ⟨p, hp⟩ xD 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yC 0 ⟨p, hp⟩ xD 0 by
    simpa [ControlledOperations.subtractConstantYStep, yC,
      Input.outputY] using h16]
  rw [show EncodedBit.GateSpec.stepList
      (ModularOperations.addConstantXGates fieldTail (counterTail + 2) p hp
        data.x2)
      (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yC 0 ⟨p, hp⟩ xD 0) =
      MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
        data.control yC 0 ⟨p, hp⟩ xOut 0 by
    simpa [ModularOperations.addConstantXStep, xOut, Input.outputX] using h17]

/-- The schedule contains exactly the seventeen paper stages. -/
@[simp] theorem stageLedgers_length
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    (stageLedgers fieldTail counterTail p hpPos hp hfit hcapacity hwidth
      x2 y2).length = 17 := by
  rfl

/-- The flattened base-gate program realizes the complete schedule step. -/
theorem realizes
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (x2 y2 : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ (counterTail + 2))
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _)
        .empty
        (gates fieldTail counterTail p hpPos hp hfit hcapacity hwidth x2 y2))
      (step fieldTail counterTail p hpPos hp hfit hcapacity hwidth x2 y2) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty _

/-- The P-256 specialization uses the already-proved 2587-qubit carrier. -/
theorem p256_encoding_width :
    (Layout.encodingFor 256).width = 2587 :=
  Layout.encodingFor_256_width

end
end Schedule
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
