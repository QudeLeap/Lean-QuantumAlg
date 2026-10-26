/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word6Chunk0 : List Letter := [.s, .s, .t, .h, .t, .h, .s, .t]
private def word6State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word6Step0 :
    word6Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word6State1 := by decide +kernel

private def word6Chunk1 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word6State2 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word6Step1 :
    word6Chunk1.foldl (fun acc a => a.applyPacked acc)
      word6State1 = word6State2 := by decide +kernel

private def word6Chunk2 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word6State3 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word6Step2 :
    word6Chunk2.foldl (fun acc a => a.applyPacked acc)
      word6State2 = word6State3 := by decide +kernel

private def word6Chunk3 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word6State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word6Step3 :
    word6Chunk3.foldl (fun acc a => a.applyPacked acc)
      word6State3 = word6State4 := by decide +kernel

private def word6Chunk4 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word6State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((13 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word6Step4 :
    word6Chunk4.foldl (fun acc a => a.applyPacked acc)
      word6State4 = word6State5 := by decide +kernel

private def word6Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word6State6 : PackedMat2 :=
    ⟨⟨⟨((15 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((17 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-17 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word6Step5 :
    word6Chunk5.foldl (fun acc a => a.applyPacked acc)
      word6State5 = word6State6 := by decide +kernel

private def word6Chunk6 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word6State7 : PackedMat2 :=
    ⟨⟨⟨((-45 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-11 : Dyadic) * half ^ 6),
        ((15 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 6)⟩,
       ⟨((13 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 6),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 6),
        ((17 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word6Step6 :
    word6Chunk6.foldl (fun acc a => a.applyPacked acc)
      word6State6 = word6State7 := by decide +kernel

private def word6Chunk7 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word6State8 : PackedMat2 :=
    ⟨⟨⟨((-71 : Dyadic) * half ^ 7),
        ((31 : Dyadic) * half ^ 7)⟩,
       ⟨((-25 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((79 : Dyadic) * half ^ 7),
        ((21 : Dyadic) * half ^ 7)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-79 : Dyadic) * half ^ 7),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-71 : Dyadic) * half ^ 7),
        ((31 : Dyadic) * half ^ 7)⟩,
       ⟨((25 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word6Step7 :
    word6Chunk7.foldl (fun acc a => a.applyPacked acc)
      word6State7 = word6State8 := by decide +kernel

private def word6Chunk8 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State9 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 6),
        ((-71 : Dyadic) * half ^ 8)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((-39 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-43 : Dyadic) * half ^ 7),
        ((21 : Dyadic) * half ^ 6)⟩,
       ⟨((29 : Dyadic) * half ^ 6),
        ((41 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 7),
        ((-101 : Dyadic) * half ^ 8)⟩,
       ⟨((-83 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((-55 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word6Step8 :
    word6Chunk8.foldl (fun acc a => a.applyPacked acc)
      word6State8 = word6State9 := by decide +kernel

private def word6Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word6State10 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 8),
        ((173 : Dyadic) * half ^ 9)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-23 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 6),
        ((-129 : Dyadic) * half ^ 9)⟩,
       ⟨((13 : Dyadic) * half ^ 8),
        ((271 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 8),
        ((271 : Dyadic) * half ^ 9)⟩,
       ⟨((11 : Dyadic) * half ^ 6),
        ((-129 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 9)⟩,
       ⟨((-5 : Dyadic) * half ^ 8),
        ((-173 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word6Step9 :
    word6Chunk9.foldl (fun acc a => a.applyPacked acc)
      word6State9 = word6State10 := by decide +kernel

private def word6Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word6State11 : PackedMat2 :=
    ⟨⟨⟨((-185 : Dyadic) * half ^ 9),
        ((37 : Dyadic) * half ^ 7)⟩,
       ⟨((255 : Dyadic) * half ^ 9),
        ((139 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((53 : Dyadic) * half ^ 9),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-33 : Dyadic) * half ^ 9),
        ((193 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((225 : Dyadic) * half ^ 9),
        ((-43 : Dyadic) * half ^ 9)⟩,
       ⟨((161 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 9),
        ((-55 : Dyadic) * half ^ 7)⟩,
       ⟨((-287 : Dyadic) * half ^ 9),
        ((-35 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word6Step10 :
    word6Chunk10.foldl (fun acc a => a.applyPacked acc)
      word6State10 = word6State11 := by decide +kernel

private def word6Chunk11 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word6State12 : PackedMat2 :=
    ⟨⟨⟨((-47 : Dyadic) * half ^ 9),
        ((-157 : Dyadic) * half ^ 9)⟩,
       ⟨((-25 : Dyadic) * half ^ 8),
        ((3 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-125 : Dyadic) * half ^ 8),
        ((-257 : Dyadic) * half ^ 10)⟩,
       ⟨((27 : Dyadic) * half ^ 6),
        ((-363 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 6),
        ((363 : Dyadic) * half ^ 10)⟩,
       ⟨((125 : Dyadic) * half ^ 8),
        ((257 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 8),
        ((3 : Dyadic) * half ^ 8)⟩,
       ⟨((-47 : Dyadic) * half ^ 9),
        ((-157 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word6Step11 :
    word6Chunk11.foldl (fun acc a => a.applyPacked acc)
      word6State11 = word6State12 := by decide +kernel

private def word6Chunk12 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word6State13 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 5),
        ((257 : Dyadic) * half ^ 11)⟩,
       ⟨((215 : Dyadic) * half ^ 10),
        ((-157 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-523 : Dyadic) * half ^ 10),
        ((-125 : Dyadic) * half ^ 11)⟩,
       ⟨((-165 : Dyadic) * half ^ 8),
        ((-139 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 8),
        ((-1183 : Dyadic) * half ^ 11)⟩,
       ⟨((7 : Dyadic) * half ^ 10),
        ((137 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 9),
        ((265 : Dyadic) * half ^ 11)⟩,
       ⟨((-207 : Dyadic) * half ^ 10),
        ((695 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word6Step12 :
    word6Chunk12.foldl (fun acc a => a.applyPacked acc)
      word6State12 = word6State13 := by decide +kernel

private def word6Chunk13 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word6State14 : PackedMat2 :=
    ⟨⟨⟨((-55 : Dyadic) * half ^ 7),
        ((-281 : Dyadic) * half ^ 12)⟩,
       ⟨((-311 : Dyadic) * half ^ 11),
        ((-59 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-861 : Dyadic) * half ^ 11),
        ((1229 : Dyadic) * half ^ 12)⟩,
       ⟨((-315 : Dyadic) * half ^ 9),
        ((-629 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((315 : Dyadic) * half ^ 9),
        ((629 : Dyadic) * half ^ 12)⟩,
       ⟨((861 : Dyadic) * half ^ 11),
        ((-1229 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-311 : Dyadic) * half ^ 11),
        ((-59 : Dyadic) * half ^ 12)⟩,
       ⟨((-55 : Dyadic) * half ^ 7),
        ((-281 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word6Step13 :
    word6Chunk13.foldl (fun acc a => a.applyPacked acc)
      word6State13 = word6State14 := by decide +kernel

private def word6Chunk14 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word6State15 : PackedMat2 :=
    ⟨⟨⟨((-135 : Dyadic) * half ^ 11),
        ((105 : Dyadic) * half ^ 11)⟩,
       ⟨((-467 : Dyadic) * half ^ 10),
        ((-651 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((2319 : Dyadic) * half ^ 12),
        ((-571 : Dyadic) * half ^ 11)⟩,
       ⟨((-1601 : Dyadic) * half ^ 12),
        ((-465 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-259 : Dyadic) * half ^ 9),
        ((359 : Dyadic) * half ^ 12)⟩,
       ⟨((-53 : Dyadic) * half ^ 10),
        ((245 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((441 : Dyadic) * half ^ 12),
        ((1069 : Dyadic) * half ^ 12)⟩,
       ⟨((-861 : Dyadic) * half ^ 12),
        ((-799 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word6Step14 :
    word6Chunk14.foldl (fun acc a => a.applyPacked acc)
      word6State14 = word6State15 := by decide +kernel

private def word6Chunk15 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word6State16 : PackedMat2 :=
    ⟨⟨⟨((-121 : Dyadic) * half ^ 9),
        ((461 : Dyadic) * half ^ 13)⟩,
       ⟨((-585 : Dyadic) * half ^ 10),
        ((-423 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2491 : Dyadic) * half ^ 12),
        ((-123 : Dyadic) * half ^ 11)⟩,
       ⟨((31 : Dyadic) * half ^ 9),
        ((1375 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 9),
        ((1375 : Dyadic) * half ^ 12)⟩,
       ⟨((2491 : Dyadic) * half ^ 12),
        ((-123 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((585 : Dyadic) * half ^ 10),
        ((423 : Dyadic) * half ^ 13)⟩,
       ⟨((121 : Dyadic) * half ^ 9),
        ((-461 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word6Step15 :
    word6Chunk15.foldl (fun acc a => a.applyPacked acc)
      word6State15 = word6State16 := by decide +kernel

private def word6Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word6State17 : PackedMat2 :=
    ⟨⟨⟨((1545 : Dyadic) * half ^ 13),
        ((1881 : Dyadic) * half ^ 14)⟩,
       ⟨((-1267 : Dyadic) * half ^ 13),
        ((-2745 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((2061 : Dyadic) * half ^ 12),
        ((-837 : Dyadic) * half ^ 12)⟩,
       ⟨((897 : Dyadic) * half ^ 13),
        ((2067 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-363 : Dyadic) * half ^ 9),
        ((3225 : Dyadic) * half ^ 14)⟩,
       ⟨((-615 : Dyadic) * half ^ 11),
        ((-5019 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-2313 : Dyadic) * half ^ 13),
        ((-703 : Dyadic) * half ^ 12)⟩,
       ⟨((-27 : Dyadic) * half ^ 9),
        ((139 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word6Step16 :
    word6Chunk16.foldl (fun acc a => a.applyPacked acc)
      word6State16 = word6State17 := by decide +kernel

private def word6Chunk17 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word6State18 : PackedMat2 :=
    ⟨⟨⟨((3635 : Dyadic) * half ^ 13),
        ((2487 : Dyadic) * half ^ 15)⟩,
       ⟨((-2097 : Dyadic) * half ^ 14),
        ((-8921 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2895 : Dyadic) * half ^ 13),
        ((-1905 : Dyadic) * half ^ 15)⟩,
       ⟨((11123 : Dyadic) * half ^ 14),
        ((-4299 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((11123 : Dyadic) * half ^ 14),
        ((-4299 : Dyadic) * half ^ 15)⟩,
       ⟨((-2895 : Dyadic) * half ^ 13),
        ((-1905 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((2097 : Dyadic) * half ^ 14),
        ((8921 : Dyadic) * half ^ 15)⟩,
       ⟨((-3635 : Dyadic) * half ^ 13),
        ((-2487 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word6Step17 :
    word6Chunk17.foldl (fun acc a => a.applyPacked acc)
      word6State17 = word6State18 := by decide +kernel

private def word6Chunk18 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word6State19 : PackedMat2 :=
    ⟨⟨⟨((3387 : Dyadic) * half ^ 15),
        ((20187 : Dyadic) * half ^ 15)⟩,
       ⟨((-4753 : Dyadic) * half ^ 15),
        ((1813 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1831 : Dyadic) * half ^ 13),
        ((1043 : Dyadic) * half ^ 15)⟩,
       ⟨((-859 : Dyadic) * half ^ 12),
        ((237 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((1831 : Dyadic) * half ^ 13),
        ((-1043 : Dyadic) * half ^ 15)⟩,
       ⟨((-859 : Dyadic) * half ^ 12),
        ((237 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((3387 : Dyadic) * half ^ 15),
        ((20187 : Dyadic) * half ^ 15)⟩,
       ⟨((4753 : Dyadic) * half ^ 15),
        ((-1813 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word6Step18 :
    word6Chunk18.foldl (fun acc a => a.applyPacked acc)
      word6State18 = word6State19 := by decide +kernel

private def word6Chunk19 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word6State20 : PackedMat2 :=
    ⟨⟨⟨((26281 : Dyadic) * half ^ 16),
        ((-2213 : Dyadic) * half ^ 13)⟩,
       ⟨((38767 : Dyadic) * half ^ 16),
        ((10593 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((26029 : Dyadic) * half ^ 16),
        ((-4783 : Dyadic) * half ^ 16)⟩,
       ⟨((-13825 : Dyadic) * half ^ 16),
        ((-3239 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((26029 : Dyadic) * half ^ 16),
        ((-4783 : Dyadic) * half ^ 16)⟩,
       ⟨((13825 : Dyadic) * half ^ 16),
        ((3239 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-26281 : Dyadic) * half ^ 16),
        ((2213 : Dyadic) * half ^ 13)⟩,
       ⟨((38767 : Dyadic) * half ^ 16),
        ((10593 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word6Step19 :
    word6Chunk19.foldl (fun acc a => a.applyPacked acc)
      word6State19 = word6State20 := by decide +kernel

private def word6Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word6State21 : PackedMat2 :=
    ⟨⟨⟨((-14109 : Dyadic) * half ^ 15),
        ((4793 : Dyadic) * half ^ 16)⟩,
       ⟨((19647 : Dyadic) * half ^ 16),
        ((71 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-713 : Dyadic) * half ^ 15),
        ((71509 : Dyadic) * half ^ 17)⟩,
       ⟨((-7045 : Dyadic) * half ^ 15),
        ((-24851 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-12045 : Dyadic) * half ^ 14),
        ((-1583 : Dyadic) * half ^ 14)⟩,
       ⟨((23329 : Dyadic) * half ^ 16),
        ((-3879 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((4225 : Dyadic) * half ^ 16),
        ((-47865 : Dyadic) * half ^ 17)⟩,
       ⟨((-5361 : Dyadic) * half ^ 16),
        ((8571 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word6Step20 :
    word6Chunk20.foldl (fun acc a => a.applyPacked acc)
      word6State20 = word6State21 := by decide +kernel

private def word6Chunk21 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State22 : PackedMat2 :=
    ⟨⟨⟨((-4423 : Dyadic) * half ^ 14),
        ((-71251 : Dyadic) * half ^ 18)⟩,
       ⟨((-19175 : Dyadic) * half ^ 17),
        ((-15637 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((67921 : Dyadic) * half ^ 17),
        ((-81859 : Dyadic) * half ^ 18)⟩,
       ⟨((3829 : Dyadic) * half ^ 14),
        ((89415 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-3829 : Dyadic) * half ^ 14),
        ((-89415 : Dyadic) * half ^ 18)⟩,
       ⟨((-67921 : Dyadic) * half ^ 17),
        ((81859 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-19175 : Dyadic) * half ^ 17),
        ((-15637 : Dyadic) * half ^ 18)⟩,
       ⟨((-4423 : Dyadic) * half ^ 14),
        ((-71251 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word6Step21 :
    word6Chunk21.foldl (fun acc a => a.applyPacked acc)
      word6State21 = word6State22 := by decide +kernel

private def word6Chunk22 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word6State23 : PackedMat2 :=
    ⟨⟨⟨((-137713 : Dyadic) * half ^ 18),
        ((-8921 : Dyadic) * half ^ 18)⟩,
       ⟨((-54799 : Dyadic) * half ^ 18),
        ((-104077 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-21171 : Dyadic) * half ^ 16),
        ((15659 : Dyadic) * half ^ 17)⟩,
       ⟨((28473 : Dyadic) * half ^ 16),
        ((-37577 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-6259 : Dyadic) * half ^ 18),
        ((3651 : Dyadic) * half ^ 16)⟩,
       ⟨((68895 : Dyadic) * half ^ 18),
        ((-12411 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((56499 : Dyadic) * half ^ 17),
        ((47 : Dyadic) * half ^ 7)⟩,
       ⟨((-23789 : Dyadic) * half ^ 16),
        ((41457 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word6Step22 :
    word6Chunk22.foldl (fun acc a => a.applyPacked acc)
      word6State22 = word6State23 := by decide +kernel

private def word6Chunk23 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word6State24 : PackedMat2 :=
    ⟨⟨⟨((150849 : Dyadic) * half ^ 19),
        ((-71213 : Dyadic) * half ^ 19)⟩,
       ⟨((-430551 : Dyadic) * half ^ 19),
        ((-16201 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((3543 : Dyadic) * half ^ 19),
        ((28485 : Dyadic) * half ^ 18)⟩,
       ⟨((-22125 : Dyadic) * half ^ 19),
        ((154131 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((97161 : Dyadic) * half ^ 19),
        ((-6417 : Dyadic) * half ^ 18)⟩,
       ⟨((211101 : Dyadic) * half ^ 19),
        ((-9291 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-38811 : Dyadic) * half ^ 19),
        ((72675 : Dyadic) * half ^ 17)⟩,
       ⟨((103615 : Dyadic) * half ^ 19),
        ((139851 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word6Step23 :
    word6Chunk23.foldl (fun acc a => a.applyPacked acc)
      word6State23 = word6State24 := by decide +kernel

private def word6Chunk24 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word6State25 : PackedMat2 :=
    ⟨⟨⟨((637373 : Dyadic) * half ^ 20),
        ((2011 : Dyadic) * half ^ 18)⟩,
       ⟨((-597479 : Dyadic) * half ^ 20),
        ((41567 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-245203 : Dyadic) * half ^ 20),
        ((22865 : Dyadic) * half ^ 17)⟩,
       ⟨((387467 : Dyadic) * half ^ 20),
        ((166623 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-245203 : Dyadic) * half ^ 20),
        ((22865 : Dyadic) * half ^ 17)⟩,
       ⟨((-387467 : Dyadic) * half ^ 20),
        ((-166623 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-637373 : Dyadic) * half ^ 20),
        ((-2011 : Dyadic) * half ^ 18)⟩,
       ⟨((-597479 : Dyadic) * half ^ 20),
        ((41567 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word6Step24 :
    word6Chunk24.foldl (fun acc a => a.applyPacked acc)
      word6State24 = word6State25 := by decide +kernel

private def word6Chunk25 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State26 : PackedMat2 :=
    ⟨⟨⟨((-79655 : Dyadic) * half ^ 19),
        ((750735 : Dyadic) * half ^ 21)⟩,
       ⟨((224249 : Dyadic) * half ^ 19),
        ((-180199 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-190835 : Dyadic) * half ^ 19),
        ((-336961 : Dyadic) * half ^ 20)⟩,
       ⟨((-440303 : Dyadic) * half ^ 20),
        ((32249 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((401459 : Dyadic) * half ^ 20),
        ((-58633 : Dyadic) * half ^ 21)⟩,
       ⟨((-272463 : Dyadic) * half ^ 20),
        ((-821973 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((465467 : Dyadic) * half ^ 20),
        ((-9497 : Dyadic) * half ^ 15)⟩,
       ⟨((-71317 : Dyadic) * half ^ 18),
        ((-72297 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word6Step25 :
    word6Chunk25.foldl (fun acc a => a.applyPacked acc)
      word6State25 = word6State26 := by decide +kernel

private def word6Chunk26 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State27 : PackedMat2 :=
    ⟨⟨⟨((288869 : Dyadic) * half ^ 20),
        ((-1236977 : Dyadic) * half ^ 22)⟩,
       ⟨((-595003 : Dyadic) * half ^ 21),
        ((398149 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((885981 : Dyadic) * half ^ 21),
        ((-4249 : Dyadic) * half ^ 22)⟩,
       ⟨((-249549 : Dyadic) * half ^ 20),
        ((-1914079 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((249549 : Dyadic) * half ^ 20),
        ((1914079 : Dyadic) * half ^ 22)⟩,
       ⟨((-885981 : Dyadic) * half ^ 21),
        ((4249 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-595003 : Dyadic) * half ^ 21),
        ((398149 : Dyadic) * half ^ 22)⟩,
       ⟨((288869 : Dyadic) * half ^ 20),
        ((-1236977 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word6Step26 :
    word6Chunk26.foldl (fun acc a => a.applyPacked acc)
      word6State26 = word6State27 := by decide +kernel

private def word6Chunk27 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word6State28 : PackedMat2 :=
    ⟨⟨⟨((254229 : Dyadic) * half ^ 22),
        ((-1783235 : Dyadic) * half ^ 22)⟩,
       ⟨((1686279 : Dyadic) * half ^ 22),
        ((-1007909 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((510459 : Dyadic) * half ^ 21),
        ((474641 : Dyadic) * half ^ 21)⟩,
       ⟨((-572885 : Dyadic) * half ^ 21),
        ((-1033215 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-83933 : Dyadic) * half ^ 22),
        ((-31213 : Dyadic) * half ^ 21)⟩,
       ⟨((1982497 : Dyadic) * half ^ 22),
        ((67709 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((348893 : Dyadic) * half ^ 19),
        ((-485127 : Dyadic) * half ^ 21)⟩,
       ⟨((387663 : Dyadic) * half ^ 21),
        ((716025 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word6Step27 :
    word6Chunk27.foldl (fun acc a => a.applyPacked acc)
      word6State27 = word6State28 := by decide +kernel

private def word6Chunk28 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word6State29 : PackedMat2 :=
    ⟨⟨⟨((-4106979 : Dyadic) * half ^ 23),
        ((2295353 : Dyadic) * half ^ 23)⟩,
       ⟨((-2782507 : Dyadic) * half ^ 23),
        ((-523119 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((4730613 : Dyadic) * half ^ 23),
        ((65389 : Dyadic) * half ^ 19)⟩,
       ⟨((-791283 : Dyadic) * half ^ 23),
        ((-1979723 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-4730613 : Dyadic) * half ^ 23),
        ((-65389 : Dyadic) * half ^ 19)⟩,
       ⟨((-791283 : Dyadic) * half ^ 23),
        ((-1979723 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-4106979 : Dyadic) * half ^ 23),
        ((2295353 : Dyadic) * half ^ 23)⟩,
       ⟨((2782507 : Dyadic) * half ^ 23),
        ((523119 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word6Step28 :
    word6Chunk28.foldl (fun acc a => a.applyPacked acc)
      word6State28 = word6State29 := by decide +kernel

private def word6Chunk29 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State30 : PackedMat2 :=
    ⟨⟨⟨((343779 : Dyadic) * half ^ 20),
        ((-2957575 : Dyadic) * half ^ 24)⟩,
       ⟨((-54165 : Dyadic) * half ^ 20),
        ((-2082875 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2510181 : Dyadic) * half ^ 23),
        ((748725 : Dyadic) * half ^ 21)⟩,
       ⟨((921363 : Dyadic) * half ^ 21),
        ((3020925 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-26025 : Dyadic) * half ^ 23),
        ((-6195633 : Dyadic) * half ^ 24)⟩,
       ⟨((-6015825 : Dyadic) * half ^ 23),
        ((-1175271 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((218675 : Dyadic) * half ^ 22),
        ((-49743 : Dyadic) * half ^ 18)⟩,
       ⟨((-2520225 : Dyadic) * half ^ 23),
        ((144807 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word6Step29 :
    word6Chunk29.foldl (fun acc a => a.applyPacked acc)
      word6State29 = word6State30 := by decide +kernel

private def word6Chunk30 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word6State31 : PackedMat2 :=
    ⟨⟨⟨((-7037 : Dyadic) * half ^ 23),
        ((1593539 : Dyadic) * half ^ 25)⟩,
       ⟨((4352809 : Dyadic) * half ^ 24),
        ((2217635 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1263645 : Dyadic) * half ^ 22),
        ((-14019787 : Dyadic) * half ^ 25)⟩,
       ⟨((3964989 : Dyadic) * half ^ 24),
        ((15443579 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3964989 : Dyadic) * half ^ 24),
        ((15443579 : Dyadic) * half ^ 25)⟩,
       ⟨((1263645 : Dyadic) * half ^ 22),
        ((-14019787 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-4352809 : Dyadic) * half ^ 24),
        ((-2217635 : Dyadic) * half ^ 25)⟩,
       ⟨((7037 : Dyadic) * half ^ 23),
        ((-1593539 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word6Step30 :
    word6Chunk30.foldl (fun acc a => a.applyPacked acc)
      word6State30 = word6State31 := by decide +kernel

private def word6Chunk31 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word6State32 : PackedMat2 :=
    ⟨⟨⟨((11972413 : Dyadic) * half ^ 25),
        ((-1667687 : Dyadic) * half ^ 25)⟩,
       ⟨((2915457 : Dyadic) * half ^ 25),
        ((9659363 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-2287103 : Dyadic) * half ^ 22),
        ((-4850651 : Dyadic) * half ^ 25)⟩,
       ⟨((4648143 : Dyadic) * half ^ 23),
        ((-81473 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((2287103 : Dyadic) * half ^ 22),
        ((4850651 : Dyadic) * half ^ 25)⟩,
       ⟨((4648143 : Dyadic) * half ^ 23),
        ((-81473 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((11972413 : Dyadic) * half ^ 25),
        ((-1667687 : Dyadic) * half ^ 25)⟩,
       ⟨((-2915457 : Dyadic) * half ^ 25),
        ((-9659363 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word6Step31 :
    word6Chunk31.foldl (fun acc a => a.applyPacked acc)
      word6State31 = word6State32 := by decide +kernel

private def word6Chunk32 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word6State33 : PackedMat2 :=
    ⟨⟨⟨((9752871 : Dyadic) * half ^ 26),
        ((16033189 : Dyadic) * half ^ 26)⟩,
       ⟨((-3270887 : Dyadic) * half ^ 26),
        ((23357491 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((4293279 : Dyadic) * half ^ 25),
        ((-8112691 : Dyadic) * half ^ 24)⟩,
       ⟨((-6787087 : Dyadic) * half ^ 25),
        ((-14635915 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((4293279 : Dyadic) * half ^ 25),
        ((-8112691 : Dyadic) * half ^ 24)⟩,
       ⟨((6787087 : Dyadic) * half ^ 25),
        ((14635915 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-9752871 : Dyadic) * half ^ 26),
        ((-16033189 : Dyadic) * half ^ 26)⟩,
       ⟨((-3270887 : Dyadic) * half ^ 26),
        ((23357491 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word6Step32 :
    word6Chunk32.foldl (fun acc a => a.applyPacked acc)
      word6State32 = word6State33 := by decide +kernel

private def word6Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word6State34 : PackedMat2 :=
    ⟨⟨⟨((-31621135 : Dyadic) * half ^ 27),
        ((-21798435 : Dyadic) * half ^ 27)⟩,
       ⟨((99501117 : Dyadic) * half ^ 27),
        ((-794751 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-5502931 : Dyadic) * half ^ 27),
        ((25827583 : Dyadic) * half ^ 26)⟩,
       ⟨((14464733 : Dyadic) * half ^ 27),
        ((-17067665 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((5502931 : Dyadic) * half ^ 27),
        ((-25827583 : Dyadic) * half ^ 26)⟩,
       ⟨((14464733 : Dyadic) * half ^ 27),
        ((-17067665 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-31621135 : Dyadic) * half ^ 27),
        ((-21798435 : Dyadic) * half ^ 27)⟩,
       ⟨((-99501117 : Dyadic) * half ^ 27),
        ((794751 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word6Step33 :
    word6Chunk33.foldl (fun acc a => a.applyPacked acc)
      word6State33 = word6State34 := by decide +kernel

private def word6Chunk34 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word6State35 : PackedMat2 :=
    ⟨⟨⟨((-11105343 : Dyadic) * half ^ 24),
        ((-17256267 : Dyadic) * half ^ 27)⟩,
       ⟨((-51761485 : Dyadic) * half ^ 27),
        ((43843257 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((32728831 : Dyadic) * half ^ 27),
        ((45504725 : Dyadic) * half ^ 28)⟩,
       ⟨((-29923597 : Dyadic) * half ^ 27),
        ((558773 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((1404561 : Dyadic) * half ^ 23),
        ((15663107 : Dyadic) * half ^ 26)⟩,
       ⟨((-23031749 : Dyadic) * half ^ 27),
        ((-1402617 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((15274881 : Dyadic) * half ^ 25),
        ((37081259 : Dyadic) * half ^ 28)⟩,
       ⟨((13293495 : Dyadic) * half ^ 26),
        ((-140604229 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word6Step34 :
    word6Chunk34.foldl (fun acc a => a.applyPacked acc)
      word6State34 = word6State35 := by decide +kernel

private def word6Chunk35 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word6State36 : PackedMat2 :=
    ⟨⟨⟨((1567185 : Dyadic) * half ^ 25),
        ((-259998043 : Dyadic) * half ^ 29)⟩,
       ⟨((-57031729 : Dyadic) * half ^ 28),
        ((152907667 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((59097187 : Dyadic) * half ^ 28),
        ((188355415 : Dyadic) * half ^ 29)⟩,
       ⟨((20715891 : Dyadic) * half ^ 27),
        ((20492329 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1631623 : Dyadic) * half ^ 22),
        ((100528969 : Dyadic) * half ^ 29)⟩,
       ⟨((83931543 : Dyadic) * half ^ 28),
        ((17665405 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((13386297 : Dyadic) * half ^ 26),
        ((44494249 : Dyadic) * half ^ 29)⟩,
       ⟨((206452855 : Dyadic) * half ^ 28),
        ((-69569209 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word6Step35 :
    word6Chunk35.foldl (fun acc a => a.applyPacked acc)
      word6State35 = word6State36 := by decide +kernel

private def word6Chunk36 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word6State37 : PackedMat2 :=
    ⟨⟨⟨((-153695093 : Dyadic) * half ^ 28),
        ((-57090419 : Dyadic) * half ^ 28)⟩,
       ⟨((20378401 : Dyadic) * half ^ 27),
        ((-195863453 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((93378445 : Dyadic) * half ^ 29),
        ((13301949 : Dyadic) * half ^ 28)⟩,
       ⟨((-126863339 : Dyadic) * half ^ 29),
        ((85197047 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-93378445 : Dyadic) * half ^ 29),
        ((-13301949 : Dyadic) * half ^ 28)⟩,
       ⟨((-126863339 : Dyadic) * half ^ 29),
        ((85197047 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-153695093 : Dyadic) * half ^ 28),
        ((-57090419 : Dyadic) * half ^ 28)⟩,
       ⟨((-20378401 : Dyadic) * half ^ 27),
        ((195863453 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word6Step36 :
    word6Chunk36.foldl (fun acc a => a.applyPacked acc)
      word6State36 = word6State37 := by decide +kernel

private def word6Chunk37 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word6State38 : PackedMat2 :=
    ⟨⟨⟨((-62699405 : Dyadic) * half ^ 28),
        ((-153830625 : Dyadic) * half ^ 30)⟩,
       ⟨((94428225 : Dyadic) * half ^ 28),
        ((-134794983 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-805813565 : Dyadic) * half ^ 30),
        ((-63861411 : Dyadic) * half ^ 30)⟩,
       ⟨((306967365 : Dyadic) * half ^ 30),
        ((38397769 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-12731821 : Dyadic) * half ^ 29),
        ((-62355775 : Dyadic) * half ^ 28)⟩,
       ⟨((-25564795 : Dyadic) * half ^ 28),
        ((-556390465 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((423420591 : Dyadic) * half ^ 30),
        ((-7932205 : Dyadic) * half ^ 27)⟩,
       ⟨((-115759341 : Dyadic) * half ^ 30),
        ((78563815 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word6Step37 :
    word6Chunk37.foldl (fun acc a => a.applyPacked acc)
      word6State37 = word6State38 := by decide +kernel

private def word6Chunk38 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word6State39 : PackedMat2 :=
    ⟨⟨⟨((-378406785 : Dyadic) * half ^ 31),
        ((57190115 : Dyadic) * half ^ 31)⟩,
       ⟨((-1595791117 : Dyadic) * half ^ 31),
        ((1250163 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-812403087 : Dyadic) * half ^ 31),
        ((-71827671 : Dyadic) * half ^ 28)⟩,
       ⟨((-478220407 : Dyadic) * half ^ 31),
        ((396936579 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((812403087 : Dyadic) * half ^ 31),
        ((71827671 : Dyadic) * half ^ 28)⟩,
       ⟨((-478220407 : Dyadic) * half ^ 31),
        ((396936579 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-378406785 : Dyadic) * half ^ 31),
        ((57190115 : Dyadic) * half ^ 31)⟩,
       ⟨((1595791117 : Dyadic) * half ^ 31),
        ((-1250163 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word6Step38 :
    word6Chunk38.foldl (fun acc a => a.applyPacked acc)
      word6State38 = word6State39 := by decide +kernel

private def word6Chunk39 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word6State40 : PackedMat2 :=
    ⟨⟨⟨((766243279 : Dyadic) * half ^ 31),
        ((-295934849 : Dyadic) * half ^ 30)⟩,
       ⟨((-257480751 : Dyadic) * half ^ 30),
        ((-852846171 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-222058327 : Dyadic) * half ^ 30),
        ((-222240715 : Dyadic) * half ^ 32)⟩,
       ⟨((21075205 : Dyadic) * half ^ 30),
        ((-1661533941 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-21075205 : Dyadic) * half ^ 30),
        ((1661533941 : Dyadic) * half ^ 32)⟩,
       ⟨((222058327 : Dyadic) * half ^ 30),
        ((222240715 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-257480751 : Dyadic) * half ^ 30),
        ((-852846171 : Dyadic) * half ^ 31)⟩,
       ⟨((766243279 : Dyadic) * half ^ 31),
        ((-295934849 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word6Step39 :
    word6Chunk39.foldl (fun acc a => a.applyPacked acc)
      word6State39 = word6State40 := by decide +kernel

private def word6Chunk40 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word6State41 : PackedMat2 :=
    ⟨⟨⟨((118947753 : Dyadic) * half ^ 29),
        ((4572602763 : Dyadic) * half ^ 33)⟩,
       ⟨((-883157701 : Dyadic) * half ^ 32),
        ((1259501787 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-80775753 : Dyadic) * half ^ 30),
        ((1648789369 : Dyadic) * half ^ 33)⟩,
       ⟨((-1167177919 : Dyadic) * half ^ 32),
        ((2318531763 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1167177919 : Dyadic) * half ^ 32),
        ((2318531763 : Dyadic) * half ^ 33)⟩,
       ⟨((-80775753 : Dyadic) * half ^ 30),
        ((1648789369 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((883157701 : Dyadic) * half ^ 32),
        ((-1259501787 : Dyadic) * half ^ 33)⟩,
       ⟨((-118947753 : Dyadic) * half ^ 29),
        ((-4572602763 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word6Step40 :
    word6Chunk40.foldl (fun acc a => a.applyPacked acc)
      word6State40 = word6State41 := by decide +kernel

private def word6Chunk41 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State42 : PackedMat2 :=
    ⟨⟨⟨((210474123 : Dyadic) * half ^ 32),
        ((-839416531 : Dyadic) * half ^ 33)⟩,
       ⟨((1106922247 : Dyadic) * half ^ 31),
        ((1257578667 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((2038567435 : Dyadic) * half ^ 33),
        ((-1095687003 : Dyadic) * half ^ 32)⟩,
       ⟨((1876153449 : Dyadic) * half ^ 33),
        ((-841578261 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((2778843525 : Dyadic) * half ^ 32),
        ((-978680221 : Dyadic) * half ^ 32)⟩,
       ⟨((-587469519 : Dyadic) * half ^ 32),
        ((-81206993 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1675740803 : Dyadic) * half ^ 33),
        ((2424318617 : Dyadic) * half ^ 33)⟩,
       ⟨((-3354573865 : Dyadic) * half ^ 33),
        ((-2003370371 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word6Step41 :
    word6Chunk41.foldl (fun acc a => a.applyPacked acc)
      word6State41 = word6State42 := by decide +kernel

private def word6Chunk42 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word6State43 : PackedMat2 :=
    ⟨⟨⟨((-4230368601 : Dyadic) * half ^ 34),
        ((-1365130533 : Dyadic) * half ^ 32)⟩,
       ⟨((7489830349 : Dyadic) * half ^ 34),
        ((1396898451 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-10686590449 : Dyadic) * half ^ 34),
        ((2889723145 : Dyadic) * half ^ 34)⟩,
       ⟨((-5115006899 : Dyadic) * half ^ 34),
        ((262097987 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-10686590449 : Dyadic) * half ^ 34),
        ((2889723145 : Dyadic) * half ^ 34)⟩,
       ⟨((5115006899 : Dyadic) * half ^ 34),
        ((-262097987 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((4230368601 : Dyadic) * half ^ 34),
        ((1365130533 : Dyadic) * half ^ 32)⟩,
       ⟨((7489830349 : Dyadic) * half ^ 34),
        ((1396898451 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word6Step42 :
    word6Chunk42.foldl (fun acc a => a.applyPacked acc)
      word6State42 = word6State43 := by decide +kernel

private def word6Chunk43 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word6State44 : PackedMat2 :=
    ⟨⟨⟨((-5456198433 : Dyadic) * half ^ 33),
        ((1136765811 : Dyadic) * half ^ 34)⟩,
       ⟨((-1901049435 : Dyadic) * half ^ 34),
        ((601887499 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1707707377 : Dyadic) * half ^ 33),
        ((-9581055549 : Dyadic) * half ^ 35)⟩,
       ⟨((-4123904771 : Dyadic) * half ^ 33),
        ((-8085383229 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-4123904771 : Dyadic) * half ^ 33),
        ((-8085383229 : Dyadic) * half ^ 35)⟩,
       ⟨((1707707377 : Dyadic) * half ^ 33),
        ((-9581055549 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((1901049435 : Dyadic) * half ^ 34),
        ((-601887499 : Dyadic) * half ^ 32)⟩,
       ⟨((5456198433 : Dyadic) * half ^ 33),
        ((-1136765811 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word6Step43 :
    word6Chunk43.foldl (fun acc a => a.applyPacked acc)
      word6State43 = word6State44 := by decide +kernel

private def word6Chunk44 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word6State45 : PackedMat2 :=
    ⟨⟨⟨((-14525325995 : Dyadic) * half ^ 35),
        ((-23298887985 : Dyadic) * half ^ 36)⟩,
       ⟨((-2149695489 : Dyadic) * half ^ 35),
        ((-11806428875 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((2177441595 : Dyadic) * half ^ 34),
        ((-5620011825 : Dyadic) * half ^ 35)⟩,
       ⟨((-10797547825 : Dyadic) * half ^ 35),
        ((14579939133 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-10099975479 : Dyadic) * half ^ 34),
        ((15152431015 : Dyadic) * half ^ 36)⟩,
       ⟨((-2239981827 : Dyadic) * half ^ 33),
        ((6442664635 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((5746229555 : Dyadic) * half ^ 35),
        ((6187815253 : Dyadic) * half ^ 35)⟩,
       ⟨((-8776329215 : Dyadic) * half ^ 34),
        ((-4168755371 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word6Step44 :
    word6Chunk44.foldl (fun acc a => a.applyPacked acc)
      word6State44 = word6State45 := by decide +kernel

private def word6Chunk45 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State46 : PackedMat2 :=
    ⟨⟨⟨((-9271159029 : Dyadic) * half ^ 36),
        ((37882117369 : Dyadic) * half ^ 37)⟩,
       ⟨((-9722054061 : Dyadic) * half ^ 34),
        ((-21724815959 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-62586381 : Dyadic) * half ^ 29),
        ((9608206905 : Dyadic) * half ^ 37)⟩,
       ⟨((6559699893 : Dyadic) * half ^ 36),
        ((-63517588035 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((6559699893 : Dyadic) * half ^ 36),
        ((-63517588035 : Dyadic) * half ^ 37)⟩,
       ⟨((-62586381 : Dyadic) * half ^ 29),
        ((9608206905 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((9722054061 : Dyadic) * half ^ 34),
        ((21724815959 : Dyadic) * half ^ 37)⟩,
       ⟨((9271159029 : Dyadic) * half ^ 36),
        ((-37882117369 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word6Step45 :
    word6Chunk45.foldl (fun acc a => a.applyPacked acc)
      word6State45 = word6State46 := by decide +kernel

private def word6Chunk46 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word6State47 : PackedMat2 :=
    ⟨⟨⟨((17615937599 : Dyadic) * half ^ 37),
        ((19471160653 : Dyadic) * half ^ 36)⟩,
       ⟨((-39087947157 : Dyadic) * half ^ 37),
        ((-20527295059 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((17751125473 : Dyadic) * half ^ 37),
        ((195576469 : Dyadic) * half ^ 36)⟩,
       ⟨((111814280271 : Dyadic) * half ^ 37),
        ((-13373235761 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-13764388699 : Dyadic) * half ^ 37),
        ((47031577399 : Dyadic) * half ^ 37)⟩,
       ⟨((-12982082823 : Dyadic) * half ^ 37),
        ((8097837859 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((59469616365 : Dyadic) * half ^ 37),
        ((14175971189 : Dyadic) * half ^ 36)⟩,
       ⟨((-18415026247 : Dyadic) * half ^ 37),
        ((10736004779 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word6Step46 :
    word6Chunk46.foldl (fun acc a => a.applyPacked acc)
      word6State46 = word6State47 := by decide +kernel

private def word6Chunk47 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word6State48 : PackedMat2 :=
    ⟨⟨⟨((96377953097 : Dyadic) * half ^ 37),
        ((-1718159815 : Dyadic) * half ^ 37)⟩,
       ⟨((23217509119 : Dyadic) * half ^ 36),
        ((12281191131 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-1198641717 : Dyadic) * half ^ 32),
        ((-13522199517 : Dyadic) * half ^ 38)⟩,
       ⟨((-31165293805 : Dyadic) * half ^ 36),
        ((39604770265 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((31165293805 : Dyadic) * half ^ 36),
        ((-39604770265 : Dyadic) * half ^ 38)⟩,
       ⟨((1198641717 : Dyadic) * half ^ 32),
        ((13522199517 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((23217509119 : Dyadic) * half ^ 36),
        ((12281191131 : Dyadic) * half ^ 36)⟩,
       ⟨((96377953097 : Dyadic) * half ^ 37),
        ((-1718159815 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word6Step47 :
    word6Chunk47.foldl (fun acc a => a.applyPacked acc)
      word6State47 = word6State48 := by decide +kernel

private def word6Chunk48 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word6State49 : PackedMat2 :=
    ⟨⟨⟨((-56100962739 : Dyadic) * half ^ 37),
        ((183235911935 : Dyadic) * half ^ 39)⟩,
       ⟨((107146182677 : Dyadic) * half ^ 38),
        ((75911517329 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((2373369855 : Dyadic) * half ^ 38),
        ((-165442604677 : Dyadic) * half ^ 39)⟩,
       ⟨((-5945607361 : Dyadic) * half ^ 34),
        ((-134747055107 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-37523707473 : Dyadic) * half ^ 36),
        ((-92756347921 : Dyadic) * half ^ 39)⟩,
       ⟨((-15347774785 : Dyadic) * half ^ 38),
        ((97503087631 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-16196714329 : Dyadic) * half ^ 35),
        ((5055742801 : Dyadic) * half ^ 39)⟩,
       ⟨((-53662197303 : Dyadic) * half ^ 38),
        ((219348108155 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word6Step48 :
    word6Chunk48.foldl (fun acc a => a.applyPacked acc)
      word6State48 = word6State49 := by decide +kernel

private def word6Chunk49 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word6State50 : PackedMat2 :=
    ⟨⟨⟨((-66178206035 : Dyadic) * half ^ 37),
        ((-260040983189 : Dyadic) * half ^ 40)⟩,
       ⟨((319790451269 : Dyadic) * half ^ 39),
        ((-251524784467 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-175240913651 : Dyadic) * half ^ 39),
        ((-148248418599 : Dyadic) * half ^ 40)⟩,
       ⟨((64179446033 : Dyadic) * half ^ 38),
        ((-112030781921 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-64179446033 : Dyadic) * half ^ 38),
        ((112030781921 : Dyadic) * half ^ 40)⟩,
       ⟨((175240913651 : Dyadic) * half ^ 39),
        ((148248418599 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((319790451269 : Dyadic) * half ^ 39),
        ((-251524784467 : Dyadic) * half ^ 40)⟩,
       ⟨((-66178206035 : Dyadic) * half ^ 37),
        ((-260040983189 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word6Step49 :
    word6Chunk49.foldl (fun acc a => a.applyPacked acc)
      word6State49 = word6State50 := by decide +kernel

private def word6Chunk50 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word6State51 : PackedMat2 :=
    ⟨⟨⟨((-354985517359 : Dyadic) * half ^ 39),
        ((-162391442699 : Dyadic) * half ^ 40)⟩,
       ⟨((-267173213473 : Dyadic) * half ^ 39),
        ((2373128551 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-20824426837 : Dyadic) * half ^ 40),
        ((-146764336255 : Dyadic) * half ^ 40)⟩,
       ⟨((-283013596211 : Dyadic) * half ^ 40),
        ((346486320471 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((24965248027 : Dyadic) * half ^ 37),
        ((-37979752881 : Dyadic) * half ^ 38)⟩,
       ⟨((-246625328363 : Dyadic) * half ^ 39),
        ((131094584687 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((124421385883 : Dyadic) * half ^ 40),
        ((38884920677 : Dyadic) * half ^ 36)⟩,
       ⟨((200361499515 : Dyadic) * half ^ 40),
        ((43906151943 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word6Step50 :
    word6Chunk50.foldl (fun acc a => a.applyPacked acc)
      word6State50 = word6State51 := by decide +kernel

private def word6Chunk51 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word6State52 : PackedMat2 :=
    ⟨⟨⟨((1243677946365 : Dyadic) * half ^ 41),
        ((-115309929527 : Dyadic) * half ^ 41)⟩,
       ⟨((-793296650381 : Dyadic) * half ^ 41),
        ((-172856411415 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-64991247795 : Dyadic) * half ^ 41),
        ((553531331303 : Dyadic) * half ^ 41)⟩,
       ⟨((662272653105 : Dyadic) * half ^ 41),
        ((-139339341091 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((64991247795 : Dyadic) * half ^ 41),
        ((-553531331303 : Dyadic) * half ^ 41)⟩,
       ⟨((662272653105 : Dyadic) * half ^ 41),
        ((-139339341091 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((1243677946365 : Dyadic) * half ^ 41),
        ((-115309929527 : Dyadic) * half ^ 41)⟩,
       ⟨((793296650381 : Dyadic) * half ^ 41),
        ((172856411415 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word6Step51 :
    word6Chunk51.foldl (fun acc a => a.applyPacked acc)
      word6State51 = word6State52 := by decide +kernel

private def word6Chunk52 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word6State53 : PackedMat2 :=
    ⟨⟨⟨((279425379133 : Dyadic) * half ^ 41),
        ((279218036835 : Dyadic) * half ^ 39)⟩,
       ⟨((121464418839 : Dyadic) * half ^ 39),
        ((-636119265179 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((78220349043 : Dyadic) * half ^ 38),
        ((267175468577 : Dyadic) * half ^ 42)⟩,
       ⟨((-109738855791 : Dyadic) * half ^ 38),
        ((197316686035 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((109738855791 : Dyadic) * half ^ 38),
        ((-197316686035 : Dyadic) * half ^ 42)⟩,
       ⟨((-78220349043 : Dyadic) * half ^ 38),
        ((-267175468577 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((121464418839 : Dyadic) * half ^ 39),
        ((-636119265179 : Dyadic) * half ^ 41)⟩,
       ⟨((279425379133 : Dyadic) * half ^ 41),
        ((279218036835 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word6Step52 :
    word6Chunk52.foldl (fun acc a => a.applyPacked acc)
      word6State52 = word6State53 := by decide +kernel

private def word6Chunk53 : List Letter := [.h, .t, .h, .t, .h]
private def word6State54 : PackedMat2 :=
    ⟨⟨⟨((309249977209 : Dyadic) * half ^ 42),
        ((5774939518199 : Dyadic) * half ^ 43)⟩,
       ⟨((-152494304417 : Dyadic) * half ^ 39),
        ((1420086114529 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-17071696541 : Dyadic) * half ^ 42),
        ((24143024781 : Dyadic) * half ^ 43)⟩,
       ⟨((96837718453 : Dyadic) * half ^ 41),
        ((-273898429571 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((17071696541 : Dyadic) * half ^ 42),
        ((-24143024781 : Dyadic) * half ^ 43)⟩,
       ⟨((96837718453 : Dyadic) * half ^ 41),
        ((-273898429571 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((309249977209 : Dyadic) * half ^ 42),
        ((5774939518199 : Dyadic) * half ^ 43)⟩,
       ⟨((152494304417 : Dyadic) * half ^ 39),
        ((-1420086114529 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word6Step53 :
    word6Chunk53.foldl (fun acc a => a.applyPacked acc)
      word6State53 = word6State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word6_check : check word6 6 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word6 = word6State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word6Chunk0 ++ word6Chunk1 ++ word6Chunk2 ++ word6Chunk3 ++
      word6Chunk4 ++ word6Chunk5 ++ word6Chunk6 ++ word6Chunk7 ++
      word6Chunk8 ++ word6Chunk9 ++ word6Chunk10 ++ word6Chunk11 ++
      word6Chunk12 ++ word6Chunk13 ++ word6Chunk14 ++ word6Chunk15 ++
      word6Chunk16 ++ word6Chunk17 ++ word6Chunk18 ++ word6Chunk19 ++
      word6Chunk20 ++ word6Chunk21 ++ word6Chunk22 ++ word6Chunk23 ++
      word6Chunk24 ++ word6Chunk25 ++ word6Chunk26 ++ word6Chunk27 ++
      word6Chunk28 ++ word6Chunk29 ++ word6Chunk30 ++ word6Chunk31 ++
      word6Chunk32 ++ word6Chunk33 ++ word6Chunk34 ++ word6Chunk35 ++
      word6Chunk36 ++ word6Chunk37 ++ word6Chunk38 ++ word6Chunk39 ++
      word6Chunk40 ++ word6Chunk41 ++ word6Chunk42 ++ word6Chunk43 ++
      word6Chunk44 ++ word6Chunk45 ++ word6Chunk46 ++ word6Chunk47 ++
      word6Chunk48 ++ word6Chunk49 ++ word6Chunk50 ++ word6Chunk51 ++
      word6Chunk52 ++ word6Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word6Step0, word6Step1, word6Step2, word6Step3, word6Step4,
      word6Step5, word6Step6, word6Step7, word6Step8, word6Step9,
      word6Step10, word6Step11, word6Step12, word6Step13, word6Step14,
      word6Step15, word6Step16, word6Step17, word6Step18, word6Step19,
      word6Step20, word6Step21, word6Step22, word6Step23, word6Step24,
      word6Step25, word6Step26, word6Step27, word6Step28, word6Step29,
      word6Step30, word6Step31, word6Step32, word6Step33, word6Step34,
      word6Step35, word6Step36, word6Step37, word6Step38, word6Step39,
      word6Step40, word6Step41, word6Step42, word6Step43, word6Step44,
      word6Step45, word6Step46, word6Step47, word6Step48, word6Step49,
      word6Step50, word6Step51, word6Step52, word6Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
