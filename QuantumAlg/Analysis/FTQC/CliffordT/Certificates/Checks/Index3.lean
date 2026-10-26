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
private def word3Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word3State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word3Step0 :
    word3Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word3State1 := by decide +kernel

private def word3Chunk1 : List Letter := [.h, .s, .h, .s, .s, .s, .h, .t]
private def word3State2 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word3Step1 :
    word3Chunk1.foldl (fun acc a => a.applyPacked acc)
      word3State1 = word3State2 := by decide +kernel

private def word3Chunk2 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word3State3 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word3Step2 :
    word3Chunk2.foldl (fun acc a => a.applyPacked acc)
      word3State2 = word3State3 := by decide +kernel

private def word3Chunk3 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State4 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-7 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word3Step3 :
    word3Chunk3.foldl (fun acc a => a.applyPacked acc)
      word3State3 = word3State4 := by decide +kernel

private def word3Chunk4 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word3State5 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-13 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word3Step4 :
    word3Chunk4.foldl (fun acc a => a.applyPacked acc)
      word3State4 = word3State5 := by decide +kernel

private def word3Chunk5 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word3State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((13 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word3Step5 :
    word3Chunk5.foldl (fun acc a => a.applyPacked acc)
      word3State5 = word3State6 := by decide +kernel

private def word3Chunk6 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word3State7 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((-17 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word3Step6 :
    word3Chunk6.foldl (fun acc a => a.applyPacked acc)
      word3State6 = word3State7 := by decide +kernel

private def word3Chunk7 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word3State8 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 5),
        ((39 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((5 : Dyadic) * half ^ 6),
        ((37 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((41 : Dyadic) * half ^ 7)⟩,
       ⟨((-13 : Dyadic) * half ^ 6),
        ((-51 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((33 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word3Step7 :
    word3Chunk7.foldl (fun acc a => a.applyPacked acc)
      word3State7 = word3State8 := by decide +kernel

private def word3Chunk8 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State9 : PackedMat2 :=
    ⟨⟨⟨((-29 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((13 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-81 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((87 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((87 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((-81 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 6)⟩,
       ⟨((29 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word3Step8 :
    word3Chunk8.foldl (fun acc a => a.applyPacked acc)
      word3State8 = word3State9 := by decide +kernel

private def word3Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word3State10 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((47 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-79 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((19 : Dyadic) * half ^ 6),
        ((-21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 6),
        ((117 : Dyadic) * half ^ 8)⟩,
       ⟨((-25 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 8)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        ((-79 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word3Step9 :
    word3Chunk9.foldl (fun acc a => a.applyPacked acc)
      word3State9 = word3State10 := by decide +kernel

private def word3Chunk10 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word3State11 : PackedMat2 :=
    ⟨⟨⟨((-103 : Dyadic) * half ^ 8),
        ((125 : Dyadic) * half ^ 9)⟩,
       ⟨((19 : Dyadic) * half ^ 7),
        ((31 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-93 : Dyadic) * half ^ 8),
        ((-89 : Dyadic) * half ^ 9)⟩,
       ⟨((-45 : Dyadic) * half ^ 6),
        ((-19 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 9)⟩,
       ⟨((93 : Dyadic) * half ^ 8),
        ((89 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 7),
        ((31 : Dyadic) * half ^ 9)⟩,
       ⟨((-103 : Dyadic) * half ^ 8),
        ((125 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word3Step10 :
    word3Chunk10.foldl (fun acc a => a.applyPacked acc)
      word3State10 = word3State11 := by decide +kernel

private def word3Chunk11 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word3State12 : PackedMat2 :=
    ⟨⟨⟨((83 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 7),
        ((-29 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((79 : Dyadic) * half ^ 7),
        ((65 : Dyadic) * half ^ 9)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-121 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-177 : Dyadic) * half ^ 9),
        ((99 : Dyadic) * half ^ 8)⟩,
       ⟨((307 : Dyadic) * half ^ 9),
        ((59 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 9),
        ((-69 : Dyadic) * half ^ 9)⟩,
       ⟨((-17 : Dyadic) * half ^ 9),
        ((-97 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word3Step11 :
    word3Chunk11.foldl (fun acc a => a.applyPacked acc)
      word3State11 = word3State12 := by decide +kernel

private def word3Chunk12 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word3State13 : PackedMat2 :=
    ⟨⟨⟨((195 : Dyadic) * half ^ 10),
        ((203 : Dyadic) * half ^ 10)⟩,
       ⟨((73 : Dyadic) * half ^ 10),
        ((41 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-255 : Dyadic) * half ^ 10),
        ((307 : Dyadic) * half ^ 10)⟩,
       ⟨((31 : Dyadic) * half ^ 10),
        ((119 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-783 : Dyadic) * half ^ 10),
        ((7 : Dyadic) * half ^ 6)⟩,
       ⟨((169 : Dyadic) * half ^ 10),
        ((143 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((531 : Dyadic) * half ^ 10),
        ((67 : Dyadic) * half ^ 9)⟩,
       ⟨((-125 : Dyadic) * half ^ 10),
        ((61 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word3Step12 :
    word3Chunk12.foldl (fun acc a => a.applyPacked acc)
      word3State12 = word3State13 := by decide +kernel

private def word3Chunk13 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State14 : PackedMat2 :=
    ⟨⟨⟨((-147 : Dyadic) * half ^ 8),
        ((-179 : Dyadic) * half ^ 10)⟩,
       ⟨((411 : Dyadic) * half ^ 10),
        ((19 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((293 : Dyadic) * half ^ 10),
        ((-99 : Dyadic) * half ^ 8)⟩,
       ⟨((93 : Dyadic) * half ^ 9),
        ((-55 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((293 : Dyadic) * half ^ 10),
        ((-99 : Dyadic) * half ^ 8)⟩,
       ⟨((-93 : Dyadic) * half ^ 9),
        ((55 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((147 : Dyadic) * half ^ 8),
        ((179 : Dyadic) * half ^ 10)⟩,
       ⟨((411 : Dyadic) * half ^ 10),
        ((19 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word3Step13 :
    word3Chunk13.foldl (fun acc a => a.applyPacked acc)
      word3State13 = word3State14 := by decide +kernel

private def word3Chunk14 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word3State15 : PackedMat2 :=
    ⟨⟨⟨((-483 : Dyadic) * half ^ 11),
        ((-1435 : Dyadic) * half ^ 12)⟩,
       ⟨((-471 : Dyadic) * half ^ 10),
        ((943 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1233 : Dyadic) * half ^ 11),
        ((-193 : Dyadic) * half ^ 12)⟩,
       ⟨((11 : Dyadic) * half ^ 7),
        ((-243 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 11),
        ((1409 : Dyadic) * half ^ 12)⟩,
       ⟨((-109 : Dyadic) * half ^ 10),
        ((-1057 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1189 : Dyadic) * half ^ 11),
        ((459 : Dyadic) * half ^ 12)⟩,
       ⟨((123 : Dyadic) * half ^ 10),
        ((1425 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word3Step14 :
    word3Chunk14.foldl (fun acc a => a.applyPacked acc)
      word3State14 = word3State15 := by decide +kernel

private def word3Chunk15 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State16 : PackedMat2 :=
    ⟨⟨⟨((211 : Dyadic) * half ^ 12),
        ((295 : Dyadic) * half ^ 10)⟩,
       ⟨((-5 : Dyadic) * half ^ 12),
        ((-1215 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-107 : Dyadic) * half ^ 12),
        ((-257 : Dyadic) * half ^ 12)⟩,
       ⟨((-1381 : Dyadic) * half ^ 12),
        ((209 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1381 : Dyadic) * half ^ 12),
        ((-209 : Dyadic) * half ^ 12)⟩,
       ⟨((107 : Dyadic) * half ^ 12),
        ((257 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 12),
        ((-1215 : Dyadic) * half ^ 11)⟩,
       ⟨((211 : Dyadic) * half ^ 12),
        ((295 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word3Step15 :
    word3Chunk15.foldl (fun acc a => a.applyPacked acc)
      word3State15 = word3State16 := by decide +kernel

private def word3Chunk16 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word3State17 : PackedMat2 :=
    ⟨⟨⟨((2413 : Dyadic) * half ^ 13),
        ((3385 : Dyadic) * half ^ 13)⟩,
       ⟨((-4183 : Dyadic) * half ^ 13),
        ((269 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-383 : Dyadic) * half ^ 13),
        ((-213 : Dyadic) * half ^ 13)⟩,
       ⟨((3921 : Dyadic) * half ^ 13),
        ((-765 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1743 : Dyadic) * half ^ 13),
        ((1769 : Dyadic) * half ^ 13)⟩,
       ⟨((1317 : Dyadic) * half ^ 13),
        ((-269 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-3923 : Dyadic) * half ^ 13),
        ((885 : Dyadic) * half ^ 13)⟩,
       ⟨((-2847 : Dyadic) * half ^ 13),
        ((-1649 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word3Step16 :
    word3Chunk16.foldl (fun acc a => a.applyPacked acc)
      word3State16 = word3State17 := by decide +kernel

private def word3Chunk17 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word3State18 : PackedMat2 :=
    ⟨⟨⟨((-611 : Dyadic) * half ^ 12),
        ((6635 : Dyadic) * half ^ 14)⟩,
       ⟨((421 : Dyadic) * half ^ 13),
        ((4075 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1655 : Dyadic) * half ^ 12),
        ((4701 : Dyadic) * half ^ 14)⟩,
       ⟨((2749 : Dyadic) * half ^ 13),
        ((-3335 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((2749 : Dyadic) * half ^ 13),
        ((-3335 : Dyadic) * half ^ 14)⟩,
       ⟨((1655 : Dyadic) * half ^ 12),
        ((4701 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-421 : Dyadic) * half ^ 13),
        ((-4075 : Dyadic) * half ^ 14)⟩,
       ⟨((611 : Dyadic) * half ^ 12),
        ((-6635 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word3Step17 :
    word3Chunk17.foldl (fun acc a => a.applyPacked acc)
      word3State17 = word3State18 := by decide +kernel

private def word3Chunk18 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word3State19 : PackedMat2 :=
    ⟨⟨⟨((-1701 : Dyadic) * half ^ 13),
        ((4867 : Dyadic) * half ^ 15)⟩,
       ⟨((1951 : Dyadic) * half ^ 14),
        ((14975 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((561 : Dyadic) * half ^ 10),
        ((-607 : Dyadic) * half ^ 15)⟩,
       ⟨((6913 : Dyadic) * half ^ 14),
        ((-1043 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((109 : Dyadic) * half ^ 13),
        ((2063 : Dyadic) * half ^ 15)⟩,
       ⟨((825 : Dyadic) * half ^ 14),
        ((-15889 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((2527 : Dyadic) * half ^ 13),
        ((5353 : Dyadic) * half ^ 15)⟩,
       ⟨((9921 : Dyadic) * half ^ 14),
        ((-1451 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word3Step18 :
    word3Chunk18.foldl (fun acc a => a.applyPacked acc)
      word3State18 = word3State19 := by decide +kernel

private def word3Chunk19 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word3State20 : PackedMat2 :=
    ⟨⟨⟨((-7235 : Dyadic) * half ^ 15),
        ((5291 : Dyadic) * half ^ 14)⟩,
       ⟨((6091 : Dyadic) * half ^ 15),
        ((5539 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2071 : Dyadic) * half ^ 15),
        ((-7505 : Dyadic) * half ^ 14)⟩,
       ⟨((15587 : Dyadic) * half ^ 15),
        ((753 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2071 : Dyadic) * half ^ 15),
        ((-7505 : Dyadic) * half ^ 14)⟩,
       ⟨((-15587 : Dyadic) * half ^ 15),
        ((-753 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((7235 : Dyadic) * half ^ 15),
        ((-5291 : Dyadic) * half ^ 14)⟩,
       ⟨((6091 : Dyadic) * half ^ 15),
        ((5539 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word3Step19 :
    word3Chunk19.foldl (fun acc a => a.applyPacked acc)
      word3State19 = word3State20 := by decide +kernel

private def word3Chunk20 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word3State21 : PackedMat2 :=
    ⟨⟨⟨((2143 : Dyadic) * half ^ 13),
        ((559 : Dyadic) * half ^ 14)⟩,
       ⟨((9715 : Dyadic) * half ^ 15),
        ((8713 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-26421 : Dyadic) * half ^ 15),
        ((3879 : Dyadic) * half ^ 15)⟩,
       ⟨((-13 : Dyadic) * half ^ 7),
        ((-2481 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-795 : Dyadic) * half ^ 12),
        ((23093 : Dyadic) * half ^ 16)⟩,
       ⟨((699 : Dyadic) * half ^ 14),
        ((-29749 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-7595 : Dyadic) * half ^ 15),
        ((-1143 : Dyadic) * half ^ 16)⟩,
       ⟨((-9831 : Dyadic) * half ^ 15),
        ((-18287 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word3Step20 :
    word3Chunk20.foldl (fun acc a => a.applyPacked acc)
      word3State20 = word3State21 := by decide +kernel

private def word3Chunk21 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word3State22 : PackedMat2 :=
    ⟨⟨⟨((35917 : Dyadic) * half ^ 16),
        ((-8665 : Dyadic) * half ^ 16)⟩,
       ⟨((-6317 : Dyadic) * half ^ 15),
        ((-6909 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-6553 : Dyadic) * half ^ 15),
        ((-2587 : Dyadic) * half ^ 15)⟩,
       ⟨((-4551 : Dyadic) * half ^ 16),
        ((-34305 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-6553 : Dyadic) * half ^ 15),
        ((-2587 : Dyadic) * half ^ 15)⟩,
       ⟨((4551 : Dyadic) * half ^ 16),
        ((34305 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-35917 : Dyadic) * half ^ 16),
        ((8665 : Dyadic) * half ^ 16)⟩,
       ⟨((-6317 : Dyadic) * half ^ 15),
        ((-6909 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word3Step21 :
    word3Chunk21.foldl (fun acc a => a.applyPacked acc)
      word3State21 = word3State22 := by decide +kernel

private def word3Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word3State23 : PackedMat2 :=
    ⟨⟨⟨((349 : Dyadic) * half ^ 14),
        ((-3487 : Dyadic) * half ^ 17)⟩,
       ⟨((-18487 : Dyadic) * half ^ 17),
        ((47319 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((51631 : Dyadic) * half ^ 17),
        ((-31913 : Dyadic) * half ^ 17)⟩,
       ⟨((-8945 : Dyadic) * half ^ 14),
        ((-17693 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-51631 : Dyadic) * half ^ 17),
        ((31913 : Dyadic) * half ^ 17)⟩,
       ⟨((-8945 : Dyadic) * half ^ 14),
        ((-17693 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((349 : Dyadic) * half ^ 14),
        ((-3487 : Dyadic) * half ^ 17)⟩,
       ⟨((18487 : Dyadic) * half ^ 17),
        ((-47319 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word3Step22 :
    word3Chunk22.foldl (fun acc a => a.applyPacked acc)
      word3State22 = word3State23 := by decide +kernel

private def word3Chunk23 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word3State24 : PackedMat2 :=
    ⟨⟨⟨((-27893 : Dyadic) * half ^ 17),
        ((-108983 : Dyadic) * half ^ 19)⟩,
       ⟨((100903 : Dyadic) * half ^ 18),
        ((79243 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-18049 : Dyadic) * half ^ 17),
        ((189729 : Dyadic) * half ^ 19)⟩,
       ⟨((31665 : Dyadic) * half ^ 18),
        ((-228225 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-31665 : Dyadic) * half ^ 18),
        ((228225 : Dyadic) * half ^ 19)⟩,
       ⟨((18049 : Dyadic) * half ^ 17),
        ((-189729 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((100903 : Dyadic) * half ^ 18),
        ((79243 : Dyadic) * half ^ 19)⟩,
       ⟨((-27893 : Dyadic) * half ^ 17),
        ((-108983 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word3Step23 :
    word3Chunk23.foldl (fun acc a => a.applyPacked acc)
      word3State23 = word3State24 := by decide +kernel

private def word3Chunk24 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word3State25 : PackedMat2 :=
    ⟨⟨⟨((12255 : Dyadic) * half ^ 19),
        ((285331 : Dyadic) * half ^ 20)⟩,
       ⟨((22035 : Dyadic) * half ^ 16),
        ((-163819 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((345635 : Dyadic) * half ^ 19),
        ((178229 : Dyadic) * half ^ 20)⟩,
       ⟨((33785 : Dyadic) * half ^ 17),
        ((-268025 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-223127 : Dyadic) * half ^ 19),
        ((-210495 : Dyadic) * half ^ 20)⟩,
       ⟨((-22449 : Dyadic) * half ^ 18),
        ((480775 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((224575 : Dyadic) * half ^ 19),
        ((-164025 : Dyadic) * half ^ 20)⟩,
       ⟨((-15189 : Dyadic) * half ^ 17),
        ((-188535 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word3Step24 :
    word3Chunk24.foldl (fun acc a => a.applyPacked acc)
      word3State24 = word3State25 := by decide +kernel

private def word3Chunk25 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word3State26 : PackedMat2 :=
    ⟨⟨⟨((244191 : Dyadic) * half ^ 20),
        ((-4981 : Dyadic) * half ^ 17)⟩,
       ⟨((194071 : Dyadic) * half ^ 20),
        ((102015 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-133191 : Dyadic) * half ^ 20),
        ((561557 : Dyadic) * half ^ 20)⟩,
       ⟨((65355 : Dyadic) * half ^ 20),
        ((81589 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-65355 : Dyadic) * half ^ 20),
        ((-81589 : Dyadic) * half ^ 20)⟩,
       ⟨((133191 : Dyadic) * half ^ 20),
        ((-561557 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((194071 : Dyadic) * half ^ 20),
        ((102015 : Dyadic) * half ^ 18)⟩,
       ⟨((244191 : Dyadic) * half ^ 20),
        ((-4981 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word3Step25 :
    word3Chunk25.foldl (fun acc a => a.applyPacked acc)
      word3State25 = word3State26 := by decide +kernel

private def word3Chunk26 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word3State27 : PackedMat2 :=
    ⟨⟨⟨((-916913 : Dyadic) * half ^ 21),
        ((-129951 : Dyadic) * half ^ 21)⟩,
       ⟨((580343 : Dyadic) * half ^ 21),
        ((31687 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((1425971 : Dyadic) * half ^ 21),
        ((4351 : Dyadic) * half ^ 21)⟩,
       ⟨((-417921 : Dyadic) * half ^ 21),
        ((162993 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((656323 : Dyadic) * half ^ 21),
        ((504025 : Dyadic) * half ^ 21)⟩,
       ⟨((-647621 : Dyadic) * half ^ 21),
        ((460973 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-123545 : Dyadic) * half ^ 21),
        ((168285 : Dyadic) * half ^ 21)⟩,
       ⟨((383447 : Dyadic) * half ^ 21),
        ((187157 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word3Step26 :
    word3Chunk26.foldl (fun acc a => a.applyPacked acc)
      word3State26 = word3State27 := by decide +kernel

private def word3Chunk27 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word3State28 : PackedMat2 :=
    ⟨⟨⟨((-1015017 : Dyadic) * half ^ 21),
        ((-1055757 : Dyadic) * half ^ 22)⟩,
       ⟨((347249 : Dyadic) * half ^ 21),
        ((-49773 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((163985 : Dyadic) * half ^ 18),
        ((-311881 : Dyadic) * half ^ 22)⟩,
       ⟨((39757 : Dyadic) * half ^ 17),
        ((-1014251 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-163985 : Dyadic) * half ^ 18),
        ((311881 : Dyadic) * half ^ 22)⟩,
       ⟨((39757 : Dyadic) * half ^ 17),
        ((-1014251 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1015017 : Dyadic) * half ^ 21),
        ((-1055757 : Dyadic) * half ^ 22)⟩,
       ⟨((-347249 : Dyadic) * half ^ 21),
        ((49773 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word3Step27 :
    word3Chunk27.foldl (fun acc a => a.applyPacked acc)
      word3State27 = word3State28 := by decide +kernel

private def word3Chunk28 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word3State29 : PackedMat2 :=
    ⟨⟨⟨((-1630045 : Dyadic) * half ^ 22),
        ((-1455547 : Dyadic) * half ^ 22)⟩,
       ⟨((-155565 : Dyadic) * half ^ 19),
        ((-447433 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((60659 : Dyadic) * half ^ 18),
        ((-273899 : Dyadic) * half ^ 20)⟩,
       ⟨((-1813137 : Dyadic) * half ^ 22),
        ((1029223 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((60659 : Dyadic) * half ^ 18),
        ((-273899 : Dyadic) * half ^ 20)⟩,
       ⟨((1813137 : Dyadic) * half ^ 22),
        ((-1029223 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1630045 : Dyadic) * half ^ 22),
        ((1455547 : Dyadic) * half ^ 22)⟩,
       ⟨((-155565 : Dyadic) * half ^ 19),
        ((-447433 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word3Step28 :
    word3Chunk28.foldl (fun acc a => a.applyPacked acc)
      word3State28 = word3State29 := by decide +kernel

private def word3Chunk29 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word3State30 : PackedMat2 :=
    ⟨⟨⟨((-1732947 : Dyadic) * half ^ 23),
        ((-3207817 : Dyadic) * half ^ 24)⟩,
       ⟨((-2324865 : Dyadic) * half ^ 22),
        ((-2616453 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1524925 : Dyadic) * half ^ 23),
        ((2757207 : Dyadic) * half ^ 24)⟩,
       ⟨((252319 : Dyadic) * half ^ 19),
        ((-5431941 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((252319 : Dyadic) * half ^ 19),
        ((-5431941 : Dyadic) * half ^ 24)⟩,
       ⟨((1524925 : Dyadic) * half ^ 23),
        ((2757207 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2324865 : Dyadic) * half ^ 22),
        ((2616453 : Dyadic) * half ^ 24)⟩,
       ⟨((1732947 : Dyadic) * half ^ 23),
        ((3207817 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word3Step29 :
    word3Chunk29.foldl (fun acc a => a.applyPacked acc)
      word3State29 = word3State30 := by decide +kernel

private def word3Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word3State31 : PackedMat2 :=
    ⟨⟨⟨((1187407 : Dyadic) * half ^ 22),
        ((7151541 : Dyadic) * half ^ 24)⟩,
       ⟨((2049611 : Dyadic) * half ^ 23),
        ((-2371555 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((180585 : Dyadic) * half ^ 21),
        ((409077 : Dyadic) * half ^ 21)⟩,
       ⟨((-444233 : Dyadic) * half ^ 21),
        ((5417197 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((444233 : Dyadic) * half ^ 21),
        ((-5417197 : Dyadic) * half ^ 24)⟩,
       ⟨((-180585 : Dyadic) * half ^ 21),
        ((-409077 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((2049611 : Dyadic) * half ^ 23),
        ((-2371555 : Dyadic) * half ^ 23)⟩,
       ⟨((1187407 : Dyadic) * half ^ 22),
        ((7151541 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word3Step30 :
    word3Chunk30.foldl (fun acc a => a.applyPacked acc)
      word3State30 = word3State31 := by decide +kernel

private def word3Chunk31 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word3State32 : PackedMat2 :=
    ⟨⟨⟨((4503517 : Dyadic) * half ^ 25),
        ((4897923 : Dyadic) * half ^ 23)⟩,
       ⟨((508063 : Dyadic) * half ^ 25),
        ((-3333969 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((8938729 : Dyadic) * half ^ 25),
        ((-5175357 : Dyadic) * half ^ 24)⟩,
       ⟨((4134619 : Dyadic) * half ^ 25),
        ((1447431 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((8938729 : Dyadic) * half ^ 25),
        ((-5175357 : Dyadic) * half ^ 24)⟩,
       ⟨((-4134619 : Dyadic) * half ^ 25),
        ((-1447431 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-4503517 : Dyadic) * half ^ 25),
        ((-4897923 : Dyadic) * half ^ 23)⟩,
       ⟨((508063 : Dyadic) * half ^ 25),
        ((-3333969 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word3Step31 :
    word3Chunk31.foldl (fun acc a => a.applyPacked acc)
      word3State31 = word3State32 := by decide +kernel

private def word3Chunk32 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word3State33 : PackedMat2 :=
    ⟨⟨⟨((13684699 : Dyadic) * half ^ 26),
        ((3371091 : Dyadic) * half ^ 23)⟩,
       ⟨((5718157 : Dyadic) * half ^ 26),
        ((15967657 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((11229595 : Dyadic) * half ^ 26),
        ((-15016979 : Dyadic) * half ^ 25)⟩,
       ⟨((-16765323 : Dyadic) * half ^ 26),
        ((7342257 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((22691701 : Dyadic) * half ^ 26),
        ((345983 : Dyadic) * half ^ 23)⟩,
       ⟨((37376215 : Dyadic) * half ^ 26),
        ((-13997459 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((42936385 : Dyadic) * half ^ 26),
        ((2425357 : Dyadic) * half ^ 24)⟩,
       ⟨((11001071 : Dyadic) * half ^ 26),
        ((3983271 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word3Step32 :
    word3Chunk32.foldl (fun acc a => a.applyPacked acc)
      word3State32 = word3State33 := by decide +kernel

private def word3Chunk33 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word3State34 : PackedMat2 :=
    ⟨⟨⟨((-27699153 : Dyadic) * half ^ 26),
        ((1230801 : Dyadic) * half ^ 27)⟩,
       ⟨((14044063 : Dyadic) * half ^ 25),
        ((15376535 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((4617763 : Dyadic) * half ^ 26),
        ((-58218093 : Dyadic) * half ^ 27)⟩,
       ⟨((-1371749 : Dyadic) * half ^ 25),
        ((47008801 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((1371749 : Dyadic) * half ^ 25),
        ((-47008801 : Dyadic) * half ^ 27)⟩,
       ⟨((-4617763 : Dyadic) * half ^ 26),
        ((58218093 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((14044063 : Dyadic) * half ^ 25),
        ((15376535 : Dyadic) * half ^ 27)⟩,
       ⟨((-27699153 : Dyadic) * half ^ 26),
        ((1230801 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word3Step33 :
    word3Chunk33.foldl (fun acc a => a.applyPacked acc)
      word3State33 = word3State34 := by decide +kernel

private def word3Chunk34 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word3State35 : PackedMat2 :=
    ⟨⟨⟨((-928597 : Dyadic) * half ^ 26),
        ((-4641805 : Dyadic) * half ^ 24)⟩,
       ⟨((1282459 : Dyadic) * half ^ 25),
        ((-10559011 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-11546011 : Dyadic) * half ^ 25),
        ((9479763 : Dyadic) * half ^ 27)⟩,
       ⟨((-1329063 : Dyadic) * half ^ 25),
        ((-39784977 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-70090191 : Dyadic) * half ^ 27),
        ((-6437537 : Dyadic) * half ^ 25)⟩,
       ⟨((89049717 : Dyadic) * half ^ 27),
        ((-2554237 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((47693451 : Dyadic) * half ^ 27),
        ((-1636321 : Dyadic) * half ^ 27)⟩,
       ⟨((26575429 : Dyadic) * half ^ 27),
        ((3493515 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word3Step34 :
    word3Chunk34.foldl (fun acc a => a.applyPacked acc)
      word3State34 = word3State35 := by decide +kernel

private def word3Chunk35 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word3State36 : PackedMat2 :=
    ⟨⟨⟨((-15325241 : Dyadic) * half ^ 27),
        ((-22010569 : Dyadic) * half ^ 26)⟩,
       ⟨((-11099159 : Dyadic) * half ^ 27),
        ((61178423 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((89183821 : Dyadic) * half ^ 27),
        ((-28045543 : Dyadic) * half ^ 28)⟩,
       ⟨((-11810507 : Dyadic) * half ^ 26),
        ((-19378599 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((105559939 : Dyadic) * half ^ 28),
        ((-65562807 : Dyadic) * half ^ 28)⟩,
       ⟨((-49468853 : Dyadic) * half ^ 28),
        ((-112804835 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-26863853 : Dyadic) * half ^ 28),
        ((-1651525 : Dyadic) * half ^ 24)⟩,
       ⟨((-149220699 : Dyadic) * half ^ 28),
        ((-2113041 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word3Step35 :
    word3Chunk35.foldl (fun acc a => a.applyPacked acc)
      word3State35 = word3State36 := by decide +kernel

private def word3Chunk36 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word3State37 : PackedMat2 :=
    ⟨⟨⟨((-259446173 : Dyadic) * half ^ 29),
        ((-13133049 : Dyadic) * half ^ 28)⟩,
       ⟨((141175217 : Dyadic) * half ^ 29),
        ((2564241 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((18014795 : Dyadic) * half ^ 29),
        ((141153219 : Dyadic) * half ^ 28)⟩,
       ⟨((172559549 : Dyadic) * half ^ 29),
        ((-71061489 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((18014795 : Dyadic) * half ^ 29),
        ((141153219 : Dyadic) * half ^ 28)⟩,
       ⟨((-172559549 : Dyadic) * half ^ 29),
        ((71061489 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((259446173 : Dyadic) * half ^ 29),
        ((13133049 : Dyadic) * half ^ 28)⟩,
       ⟨((141175217 : Dyadic) * half ^ 29),
        ((2564241 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word3Step36 :
    word3Chunk36.foldl (fun acc a => a.applyPacked acc)
      word3State36 = word3State37 := by decide +kernel

private def word3Chunk37 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word3State38 : PackedMat2 :=
    ⟨⟨⟨((354579291 : Dyadic) * half ^ 30),
        ((49634999 : Dyadic) * half ^ 28)⟩,
       ⟨((503186841 : Dyadic) * half ^ 30),
        ((-384482543 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((416627311 : Dyadic) * half ^ 30),
        ((111308217 : Dyadic) * half ^ 29)⟩,
       ⟨((331837917 : Dyadic) * half ^ 30),
        ((91370809 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-313987243 : Dyadic) * half ^ 30),
        ((-187116307 : Dyadic) * half ^ 29)⟩,
       ⟨((-131245625 : Dyadic) * half ^ 30),
        ((-42394697 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-185942547 : Dyadic) * half ^ 30),
        ((214441533 : Dyadic) * half ^ 29)⟩,
       ⟨((583022539 : Dyadic) * half ^ 30),
        ((-74303775 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word3Step37 :
    word3Chunk37.foldl (fun acc a => a.applyPacked acc)
      word3State37 = word3State38 := by decide +kernel

private def word3Chunk38 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word3State39 : PackedMat2 :=
    ⟨⟨⟨((-218972383 : Dyadic) * half ^ 30),
        ((647691025 : Dyadic) * half ^ 31)⟩,
       ⟨((-415506553 : Dyadic) * half ^ 30),
        ((479110403 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((19268181 : Dyadic) * half ^ 26),
        ((-59226041 : Dyadic) * half ^ 31)⟩,
       ⟨((238487055 : Dyadic) * half ^ 29),
        ((752994347 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((19268181 : Dyadic) * half ^ 26),
        ((-59226041 : Dyadic) * half ^ 31)⟩,
       ⟨((-238487055 : Dyadic) * half ^ 29),
        ((-752994347 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((218972383 : Dyadic) * half ^ 30),
        ((-647691025 : Dyadic) * half ^ 31)⟩,
       ⟨((-415506553 : Dyadic) * half ^ 30),
        ((479110403 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word3Step38 :
    word3Chunk38.foldl (fun acc a => a.applyPacked acc)
      word3State38 = word3State39 := by decide +kernel

private def word3Chunk39 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word3State40 : PackedMat2 :=
    ⟨⟨⟨((-27371219 : Dyadic) * half ^ 29),
        ((915308243 : Dyadic) * half ^ 31)⟩,
       ⟨((328140361 : Dyadic) * half ^ 31),
        ((-910412967 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-396580909 : Dyadic) * half ^ 31),
        ((-321600751 : Dyadic) * half ^ 31)⟩,
       ⟨((67862607 : Dyadic) * half ^ 28),
        ((62491827 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((396580909 : Dyadic) * half ^ 31),
        ((321600751 : Dyadic) * half ^ 31)⟩,
       ⟨((67862607 : Dyadic) * half ^ 28),
        ((62491827 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-27371219 : Dyadic) * half ^ 29),
        ((915308243 : Dyadic) * half ^ 31)⟩,
       ⟨((-328140361 : Dyadic) * half ^ 31),
        ((910412967 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word3Step39 :
    word3Chunk39.foldl (fun acc a => a.applyPacked acc)
      word3State39 = word3State40 := by decide +kernel

private def word3Chunk40 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word3State41 : PackedMat2 :=
    ⟨⟨⟨((-975630817 : Dyadic) * half ^ 32),
        ((2870228673 : Dyadic) * half ^ 33)⟩,
       ⟨((-75655301 : Dyadic) * half ^ 28),
        ((1090617291 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-433007539 : Dyadic) * half ^ 32),
        ((-3317576721 : Dyadic) * half ^ 33)⟩,
       ⟨((429185219 : Dyadic) * half ^ 31),
        ((3126765981 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-429185219 : Dyadic) * half ^ 31),
        ((-3126765981 : Dyadic) * half ^ 33)⟩,
       ⟨((433007539 : Dyadic) * half ^ 32),
        ((3317576721 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-75655301 : Dyadic) * half ^ 28),
        ((1090617291 : Dyadic) * half ^ 33)⟩,
       ⟨((-975630817 : Dyadic) * half ^ 32),
        ((2870228673 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word3Step40 :
    word3Chunk40.foldl (fun acc a => a.applyPacked acc)
      word3State40 = word3State41 := by decide +kernel

private def word3Chunk41 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word3State42 : PackedMat2 :=
    ⟨⟨⟨((-4801214249 : Dyadic) * half ^ 33),
        ((-3591037073 : Dyadic) * half ^ 34)⟩,
       ⟨((-6342391 : Dyadic) * half ^ 31),
        ((689175145 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-4113727693 : Dyadic) * half ^ 33),
        ((222666609 : Dyadic) * half ^ 34)⟩,
       ⟨((-19816245 : Dyadic) * half ^ 26),
        ((6429330651 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3103332021 : Dyadic) * half ^ 33),
        ((1577248333 : Dyadic) * half ^ 34)⟩,
       ⟨((1662999315 : Dyadic) * half ^ 32),
        ((-6650207053 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-2140106109 : Dyadic) * half ^ 33),
        ((-4775844685 : Dyadic) * half ^ 34)⟩,
       ⟨((362732741 : Dyadic) * half ^ 31),
        ((4826583813 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word3Step41 :
    word3Chunk41.foldl (fun acc a => a.applyPacked acc)
      word3State41 = word3State42 := by decide +kernel

private def word3Chunk42 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word3State43 : PackedMat2 :=
    ⟨⟨⟨((-3839697601 : Dyadic) * half ^ 33),
        ((-5034468517 : Dyadic) * half ^ 34)⟩,
       ⟨((-24618121 : Dyadic) * half ^ 28),
        ((-2517776713 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((3780180109 : Dyadic) * half ^ 33),
        ((-2766437241 : Dyadic) * half ^ 33)⟩,
       ⟨((1145116697 : Dyadic) * half ^ 33),
        ((-2080558483 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((7613432965 : Dyadic) * half ^ 34),
        ((-2462648403 : Dyadic) * half ^ 33)⟩,
       ⟨((3452315999 : Dyadic) * half ^ 34),
        ((-658765853 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-10070021943 : Dyadic) * half ^ 34),
        ((-4627477473 : Dyadic) * half ^ 34)⟩,
       ⟨((1084909 : Dyadic) * half ^ 34),
        ((-3051917729 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word3Step42 :
    word3Chunk42.foldl (fun acc a => a.applyPacked acc)
      word3State42 = word3State43 := by decide +kernel

private def word3Chunk43 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word3State44 : PackedMat2 :=
    ⟨⟨⟨((-16106810255 : Dyadic) * half ^ 35),
        ((1140727515 : Dyadic) * half ^ 34)⟩,
       ⟨((-21202818053 : Dyadic) * half ^ 35),
        ((-3974964849 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3285960415 : Dyadic) * half ^ 35),
        ((7134198087 : Dyadic) * half ^ 34)⟩,
       ⟨((3398158343 : Dyadic) * half ^ 35),
        ((-190723359 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3285960415 : Dyadic) * half ^ 35),
        ((7134198087 : Dyadic) * half ^ 34)⟩,
       ⟨((-3398158343 : Dyadic) * half ^ 35),
        ((190723359 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((16106810255 : Dyadic) * half ^ 35),
        ((-1140727515 : Dyadic) * half ^ 34)⟩,
       ⟨((-21202818053 : Dyadic) * half ^ 35),
        ((-3974964849 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word3Step43 :
    word3Chunk43.foldl (fun acc a => a.applyPacked acc)
      word3State43 = word3State44 := by decide +kernel

private def word3Chunk44 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word3State45 : PackedMat2 :=
    ⟨⟨⟨((10324160305 : Dyadic) * half ^ 36),
        ((481166645 : Dyadic) * half ^ 31)⟩,
       ⟨((14327195059 : Dyadic) * half ^ 36),
        ((-23261590025 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2889126787 : Dyadic) * half ^ 36),
        ((14459883289 : Dyadic) * half ^ 35)⟩,
       ⟨((-11275743329 : Dyadic) * half ^ 36),
        ((-22868707809 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-6051058769 : Dyadic) * half ^ 36),
        ((3541217529 : Dyadic) * half ^ 35)⟩,
       ⟨((-51788474387 : Dyadic) * half ^ 36),
        ((-4193308271 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-7864257385 : Dyadic) * half ^ 36),
        ((6162838841 : Dyadic) * half ^ 35)⟩,
       ⟨((38658922665 : Dyadic) * half ^ 36),
        ((-2001517377 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word3Step44 :
    word3Chunk44.foldl (fun acc a => a.applyPacked acc)
      word3State44 = word3State45 := by decide +kernel

private def word3Chunk45 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word3State46 : PackedMat2 :=
    ⟨⟨⟨((104197333239 : Dyadic) * half ^ 37),
        ((-10484901319 : Dyadic) * half ^ 37)⟩,
       ⟨((-23578482217 : Dyadic) * half ^ 37),
        ((-13145688649 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((56638834795 : Dyadic) * half ^ 37),
        ((16088178157 : Dyadic) * half ^ 37)⟩,
       ⟨((44173332339 : Dyadic) * half ^ 37),
        ((-620605885 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((6158483997 : Dyadic) * half ^ 37),
        ((50406083567 : Dyadic) * half ^ 37)⟩,
       ⟨((26017872317 : Dyadic) * half ^ 37),
        ((1558187807 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((36776278617 : Dyadic) * half ^ 37),
        ((-40309425511 : Dyadic) * half ^ 37)⟩,
       ⟨((-15806475979 : Dyadic) * half ^ 37),
        ((-3992994233 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word3Step45 :
    word3Chunk45.foldl (fun acc a => a.applyPacked acc)
      word3State45 = word3State46 := by decide +kernel

private def word3Chunk46 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State47 : PackedMat2 :=
    ⟨⟨⟨((-29326945523 : Dyadic) * half ^ 37),
        ((18883783739 : Dyadic) * half ^ 35)⟩,
       ⟨((29254352289 : Dyadic) * half ^ 36),
        ((31174326359 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-4752252025 : Dyadic) * half ^ 35),
        ((-5029394785 : Dyadic) * half ^ 35)⟩,
       ⟨((1408755237 : Dyadic) * half ^ 37),
        ((3134012039 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((4752252025 : Dyadic) * half ^ 35),
        ((5029394785 : Dyadic) * half ^ 35)⟩,
       ⟨((1408755237 : Dyadic) * half ^ 37),
        ((3134012039 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-29326945523 : Dyadic) * half ^ 37),
        ((18883783739 : Dyadic) * half ^ 35)⟩,
       ⟨((-29254352289 : Dyadic) * half ^ 36),
        ((-31174326359 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word3Step46 :
    word3Chunk46.foldl (fun acc a => a.applyPacked acc)
      word3State46 = word3State47 := by decide +kernel

private def word3Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word3State48 : PackedMat2 :=
    ⟨⟨⟨((16543990529 : Dyadic) * half ^ 36),
        ((-141420307101 : Dyadic) * half ^ 39)⟩,
       ⟨((46871262257 : Dyadic) * half ^ 38),
        ((285687931931 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-43002361057 : Dyadic) * half ^ 37),
        ((37281585745 : Dyadic) * half ^ 39)⟩,
       ⟨((100236501371 : Dyadic) * half ^ 38),
        ((-8235888751 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((711210539 : Dyadic) * half ^ 33),
        ((-186241223485 : Dyadic) * half ^ 39)⟩,
       ⟨((-14522848497 : Dyadic) * half ^ 38),
        ((-14231779257 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((53388529879 : Dyadic) * half ^ 36),
        ((-19304699859 : Dyadic) * half ^ 39)⟩,
       ⟨((72133812415 : Dyadic) * half ^ 38),
        ((113047224373 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word3Step47 :
    word3Chunk47.foldl (fun acc a => a.applyPacked acc)
      word3State47 = word3State48 := by decide +kernel

private def word3Chunk48 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word3State49 : PackedMat2 :=
    ⟨⟨⟨((-25571711811 : Dyadic) * half ^ 37),
        ((-47654398361 : Dyadic) * half ^ 38)⟩,
       ⟨((226050197709 : Dyadic) * half ^ 38),
        ((-27956835669 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((1610523245 : Dyadic) * half ^ 38),
        ((-152596931289 : Dyadic) * half ^ 39)⟩,
       ⟨((-70555936561 : Dyadic) * half ^ 38),
        ((-11983335861 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-176563603011 : Dyadic) * half ^ 39),
        ((-17236353329 : Dyadic) * half ^ 37)⟩,
       ⟨((-128630259567 : Dyadic) * half ^ 39),
        ((36083229903 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((123265632391 : Dyadic) * half ^ 39),
        ((-174906774087 : Dyadic) * half ^ 39)⟩,
       ⟨((67351961053 : Dyadic) * half ^ 39),
        ((277193621331 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word3Step48 :
    word3Chunk48.foldl (fun acc a => a.applyPacked acc)
      word3State48 = word3State49 := by decide +kernel

private def word3Chunk49 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word3State50 : PackedMat2 :=
    ⟨⟨⟨((-576287024001 : Dyadic) * half ^ 40),
        ((-289109321929 : Dyadic) * half ^ 40)⟩,
       ⟨((486719631189 : Dyadic) * half ^ 40),
        ((-158458940431 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-82530646591 : Dyadic) * half ^ 40),
        ((-16111085177 : Dyadic) * half ^ 37)⟩,
       ⟨((-565517827483 : Dyadic) * half ^ 40),
        ((88522531961 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((565517827483 : Dyadic) * half ^ 40),
        ((-88522531961 : Dyadic) * half ^ 39)⟩,
       ⟨((82530646591 : Dyadic) * half ^ 40),
        ((16111085177 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((486719631189 : Dyadic) * half ^ 40),
        ((-158458940431 : Dyadic) * half ^ 40)⟩,
       ⟨((-576287024001 : Dyadic) * half ^ 40),
        ((-289109321929 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word3Step49 :
    word3Chunk49.foldl (fun acc a => a.applyPacked acc)
      word3State49 = word3State50 := by decide +kernel

private def word3Chunk50 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word3State51 : PackedMat2 :=
    ⟨⟨⟨((-759004529709 : Dyadic) * half ^ 41),
        ((-20603802313 : Dyadic) * half ^ 36)⟩,
       ⟨((-845048522357 : Dyadic) * half ^ 41),
        ((-126413927777 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((177090083153 : Dyadic) * half ^ 41),
        ((-197769759527 : Dyadic) * half ^ 39)⟩,
       ⟨((719127743613 : Dyadic) * half ^ 41),
        ((-649622812493 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-1440701850601 : Dyadic) * half ^ 41),
        ((448108913383 : Dyadic) * half ^ 41)⟩,
       ⟨((-141456225615 : Dyadic) * half ^ 41),
        ((-135509415115 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((785735601793 : Dyadic) * half ^ 41),
        ((802026526033 : Dyadic) * half ^ 41)⟩,
       ⟨((532907746239 : Dyadic) * half ^ 41),
        ((-10755499081 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word3Step50 :
    word3Chunk50.foldl (fun acc a => a.applyPacked acc)
      word3State50 = word3State51 := by decide +kernel

private def word3Chunk51 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word3State52 : PackedMat2 :=
    ⟨⟨⟨((-149090321161 : Dyadic) * half ^ 39),
        ((17032210561 : Dyadic) * half ^ 42)⟩,
       ⟨((-18576913569 : Dyadic) * half ^ 36),
        ((-713291158265 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-1573167171093 : Dyadic) * half ^ 41),
        ((700298967869 : Dyadic) * half ^ 42)⟩,
       ⟨((-940580035771 : Dyadic) * half ^ 41),
        ((-731272968511 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1573167171093 : Dyadic) * half ^ 41),
        ((-700298967869 : Dyadic) * half ^ 42)⟩,
       ⟨((-940580035771 : Dyadic) * half ^ 41),
        ((-731272968511 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-149090321161 : Dyadic) * half ^ 39),
        ((17032210561 : Dyadic) * half ^ 42)⟩,
       ⟨((18576913569 : Dyadic) * half ^ 36),
        ((713291158265 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word3Step51 :
    word3Chunk51.foldl (fun acc a => a.applyPacked acc)
      word3State51 = word3State52 := by decide +kernel

private def word3Chunk52 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word3State53 : PackedMat2 :=
    ⟨⟨⟨((1033120123617 : Dyadic) * half ^ 42),
        ((916542940667 : Dyadic) * half ^ 42)⟩,
       ⟨((-97001564987 : Dyadic) * half ^ 40),
        ((-1904355745935 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-190586576283 : Dyadic) * half ^ 40),
        ((-2546815853 : Dyadic) * half ^ 35)⟩,
       ⟨((1006651605189 : Dyadic) * half ^ 42),
        ((-1921538713763 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-190586576283 : Dyadic) * half ^ 40),
        ((-2546815853 : Dyadic) * half ^ 35)⟩,
       ⟨((-1006651605189 : Dyadic) * half ^ 42),
        ((1921538713763 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-1033120123617 : Dyadic) * half ^ 42),
        ((-916542940667 : Dyadic) * half ^ 42)⟩,
       ⟨((-97001564987 : Dyadic) * half ^ 40),
        ((-1904355745935 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word3Step52 :
    word3Chunk52.foldl (fun acc a => a.applyPacked acc)
      word3State52 = word3State53 := by decide +kernel

private def word3Chunk53 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word3State54 : PackedMat2 :=
    ⟨⟨⟨((1432038249495 : Dyadic) * half ^ 43),
        ((-221526874885 : Dyadic) * half ^ 42)⟩,
       ⟨((-576985021425 : Dyadic) * half ^ 43),
        ((-349408083327 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((4694089784365 : Dyadic) * half ^ 43),
        ((2166773858505 : Dyadic) * half ^ 43)⟩,
       ⟨((2556890571419 : Dyadic) * half ^ 43),
        ((-4045137541425 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-234795460365 : Dyadic) * half ^ 40),
        ((906372544473 : Dyadic) * half ^ 41)⟩,
       ⟨((3105955699965 : Dyadic) * half ^ 42),
        ((1068599606473 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((920343041539 : Dyadic) * half ^ 42),
        ((-427526614035 : Dyadic) * half ^ 43)⟩,
       ⟨((-477289291769 : Dyadic) * half ^ 42),
        ((-251127908865 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word3Step53 :
    word3Chunk53.foldl (fun acc a => a.applyPacked acc)
      word3State53 = word3State54 := by decide +kernel

private def word3Chunk54 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word3State55 : PackedMat2 :=
    ⟨⟨⟨((1569241204805 : Dyadic) * half ^ 44),
        ((-795819595089 : Dyadic) * half ^ 44)⟩,
       ⟨((-7575137817051 : Dyadic) * half ^ 44),
        ((-522159594417 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-64028937487 : Dyadic) * half ^ 44),
        ((9166753939825 : Dyadic) * half ^ 44)⟩,
       ⟨((-2441606714947 : Dyadic) * half ^ 44),
        ((716022008173 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((64028937487 : Dyadic) * half ^ 44),
        ((-9166753939825 : Dyadic) * half ^ 44)⟩,
       ⟨((-2441606714947 : Dyadic) * half ^ 44),
        ((716022008173 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((1569241204805 : Dyadic) * half ^ 44),
        ((-795819595089 : Dyadic) * half ^ 44)⟩,
       ⟨((7575137817051 : Dyadic) * half ^ 44),
        ((522159594417 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word3Step54 :
    word3Chunk54.foldl (fun acc a => a.applyPacked acc)
      word3State54 = word3State55 := by decide +kernel

private def word3Chunk55 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word3State56 : PackedMat2 :=
    ⟨⟨⟨((15078662189 : Dyadic) * half ^ 37),
        ((6267858594955 : Dyadic) * half ^ 45)⟩,
       ⟨((5288712763577 : Dyadic) * half ^ 43),
        ((-2962947349761 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((3618516154727 : Dyadic) * half ^ 44),
        ((-9133951605551 : Dyadic) * half ^ 45)⟩,
       ⟨((10078482877713 : Dyadic) * half ^ 44),
        ((5188708354347 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((3618516154727 : Dyadic) * half ^ 44),
        ((-9133951605551 : Dyadic) * half ^ 45)⟩,
       ⟨((-10078482877713 : Dyadic) * half ^ 44),
        ((-5188708354347 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-15078662189 : Dyadic) * half ^ 37),
        ((-6267858594955 : Dyadic) * half ^ 45)⟩,
       ⟨((5288712763577 : Dyadic) * half ^ 43),
        ((-2962947349761 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word3Step55 :
    word3Chunk55.foldl (fun acc a => a.applyPacked acc)
      word3State55 = word3State56 := by decide +kernel

private def word3Chunk56 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word3State57 : PackedMat2 :=
    ⟨⟨⟨((-2336945306597 : Dyadic) * half ^ 45),
        ((-6873914162295 : Dyadic) * half ^ 46)⟩,
       ⟨((1532112847595 : Dyadic) * half ^ 43),
        ((33882676372249 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-17559978860667 : Dyadic) * half ^ 45),
        ((14555818242453 : Dyadic) * half ^ 46)⟩,
       ⟨((1677828435179 : Dyadic) * half ^ 42),
        ((2375657382913 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((1677828435179 : Dyadic) * half ^ 42),
        ((2375657382913 : Dyadic) * half ^ 46)⟩,
       ⟨((-17559978860667 : Dyadic) * half ^ 45),
        ((14555818242453 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-1532112847595 : Dyadic) * half ^ 43),
        ((-33882676372249 : Dyadic) * half ^ 46)⟩,
       ⟨((2336945306597 : Dyadic) * half ^ 45),
        ((6873914162295 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word3Step56 :
    word3Chunk56.foldl (fun acc a => a.applyPacked acc)
      word3State56 = word3State57 := by decide +kernel

private def word3Chunk57 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word3State58 : PackedMat2 :=
    ⟨⟨⟨((-3926015884593 : Dyadic) * half ^ 44),
        ((-19805755143083 : Dyadic) * half ^ 46)⟩,
       ⟨((5564532418885 : Dyadic) * half ^ 45),
        ((-16986922698215 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-819237323993 : Dyadic) * half ^ 44),
        ((-3231599253203 : Dyadic) * half ^ 43)⟩,
       ⟨((-33415207221 : Dyadic) * half ^ 40),
        ((8254103088641 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((33415207221 : Dyadic) * half ^ 40),
        ((-8254103088641 : Dyadic) * half ^ 46)⟩,
       ⟨((819237323993 : Dyadic) * half ^ 44),
        ((3231599253203 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((5564532418885 : Dyadic) * half ^ 45),
        ((-16986922698215 : Dyadic) * half ^ 45)⟩,
       ⟨((-3926015884593 : Dyadic) * half ^ 44),
        ((-19805755143083 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word3Step57 :
    word3Chunk57.foldl (fun acc a => a.applyPacked acc)
      word3State57 = word3State58 := by decide +kernel

private def word3Chunk58 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State59 : PackedMat2 :=
    ⟨⟨⟨((20881662216093 : Dyadic) * half ^ 47),
        ((32108933262801 : Dyadic) * half ^ 47)⟩,
       ⟨((-77335779619683 : Dyadic) * half ^ 47),
        ((18866692464335 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-17562309718379 : Dyadic) * half ^ 47),
        ((-16944342476361 : Dyadic) * half ^ 47)⟩,
       ⟨((-34441130509183 : Dyadic) * half ^ 47),
        ((-28310206768203 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-73564756012767 : Dyadic) * half ^ 47),
        ((-26001720113781 : Dyadic) * half ^ 47)⟩,
       ⟨((39676071060045 : Dyadic) * half ^ 47),
        ((4219705197701 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-69842318191471 : Dyadic) * half ^ 47),
        ((28227058701795 : Dyadic) * half ^ 47)⟩,
       ⟨((5624451665869 : Dyadic) * half ^ 47),
        ((-383661882171 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word3Step58 :
    word3Chunk58.foldl (fun acc a => a.applyPacked acc)
      word3State58 = word3State59 := by decide +kernel

private def word3Chunk59 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State60 : PackedMat2 :=
    ⟨⟨⟨((-11367545137523 : Dyadic) * half ^ 47),
        ((-11683829346841 : Dyadic) * half ^ 46)⟩,
       ⟨((51933957771823 : Dyadic) * half ^ 46),
        ((-12706049986131 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((2729649137017 : Dyadic) * half ^ 45),
        ((27557806277491 : Dyadic) * half ^ 46)⟩,
       ⟨((-25530741778047 : Dyadic) * half ^ 47),
        ((-4429296246453 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-2729649137017 : Dyadic) * half ^ 45),
        ((-27557806277491 : Dyadic) * half ^ 46)⟩,
       ⟨((-25530741778047 : Dyadic) * half ^ 47),
        ((-4429296246453 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-11367545137523 : Dyadic) * half ^ 47),
        ((-11683829346841 : Dyadic) * half ^ 46)⟩,
       ⟨((-51933957771823 : Dyadic) * half ^ 46),
        ((12706049986131 : Dyadic) * half ^ 47)⟩⟩⟩
private lemma word3Step59 :
    word3Chunk59.foldl (fun acc a => a.applyPacked acc)
      word3State59 = word3State60 := by decide +kernel

private def word3Chunk60 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word3State61 : PackedMat2 :=
    ⟨⟨⟨((-47000415125045 : Dyadic) * half ^ 46),
        ((17289154927195 : Dyadic) * half ^ 49)⟩,
       ⟨((-109612442650579 : Dyadic) * half ^ 48),
        ((124551175373813 : Dyadic) * half ^ 49)⟩⟩,
     ⟨⟨((49844129104099 : Dyadic) * half ^ 47),
        ((149771933473883 : Dyadic) * half ^ 49)⟩,
       ⟨((-35177382131107 : Dyadic) * half ^ 48),
        ((-56065719127299 : Dyadic) * half ^ 49)⟩⟩,
     ⟨⟨((102918826300591 : Dyadic) * half ^ 48),
        ((134865640339305 : Dyadic) * half ^ 49)⟩,
       ⟨((-11713276793323 : Dyadic) * half ^ 46),
        ((-64510876077091 : Dyadic) * half ^ 49)⟩⟩,
     ⟨⟨((53631010223309 : Dyadic) * half ^ 48),
        ((78389217849601 : Dyadic) * half ^ 49)⟩,
       ⟨((8865020643813 : Dyadic) * half ^ 45),
        ((-297614103150759 : Dyadic) * half ^ 49)⟩⟩⟩
private lemma word3Step60 :
    word3Chunk60.foldl (fun acc a => a.applyPacked acc)
      word3State60 = word3State61 := by decide +kernel

private def word3Chunk61 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word3State62 : PackedMat2 :=
    ⟨⟨⟨((-122394862579001 : Dyadic) * half ^ 49),
        ((304750474460271 : Dyadic) * half ^ 50)⟩,
       ⟨((57268386532003 : Dyadic) * half ^ 48),
        ((-443660478469815 : Dyadic) * half ^ 50)⟩⟩,
     ⟨⟨((193757155363989 : Dyadic) * half ^ 49),
        ((458528800367193 : Dyadic) * half ^ 50)⟩,
       ⟨((-8056302536973 : Dyadic) * half ^ 47),
        ((22588030484623 : Dyadic) * half ^ 50)⟩⟩,
     ⟨⟨((-217970384941285 : Dyadic) * half ^ 49),
        ((-225982365511881 : Dyadic) * half ^ 50)⟩,
       ⟨((60139603856477 : Dyadic) * half ^ 47),
        ((161531945216097 : Dyadic) * half ^ 50)⟩⟩,
     ⟨⟨((374205476465043 : Dyadic) * half ^ 49),
        ((-236931635643007 : Dyadic) * half ^ 50)⟩,
       ⟨((17363750501193 : Dyadic) * half ^ 47),
        ((7858089514995 : Dyadic) * half ^ 50)⟩⟩⟩
private lemma word3Step61 :
    word3Chunk61.foldl (fun acc a => a.applyPacked acc)
      word3State61 = word3State62 := by decide +kernel

private def word3Chunk62 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word3State63 : PackedMat2 :=
    ⟨⟨⟨((164093181038753 : Dyadic) * half ^ 50),
        ((-1265640613849 : Dyadic) * half ^ 43)⟩,
       ⟨((-65828222221871 : Dyadic) * half ^ 50),
        ((225521202157797 : Dyadic) * half ^ 49)⟩⟩,
     ⟨⟨((430643916190231 : Dyadic) * half ^ 50),
        ((-246033050491471 : Dyadic) * half ^ 50)⟩,
       ⟨((535995782942561 : Dyadic) * half ^ 50),
        ((302665402306831 : Dyadic) * half ^ 50)⟩⟩,
     ⟨⟨((-535995782942561 : Dyadic) * half ^ 50),
        ((-302665402306831 : Dyadic) * half ^ 50)⟩,
       ⟨((-430643916190231 : Dyadic) * half ^ 50),
        ((246033050491471 : Dyadic) * half ^ 50)⟩⟩,
     ⟨⟨((-65828222221871 : Dyadic) * half ^ 50),
        ((225521202157797 : Dyadic) * half ^ 49)⟩,
       ⟨((164093181038753 : Dyadic) * half ^ 50),
        ((-1265640613849 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word3Step62 :
    word3Chunk62.foldl (fun acc a => a.applyPacked acc)
      word3State62 = word3State63 := by decide +kernel

private def word3Chunk63 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word3State64 : PackedMat2 :=
    ⟨⟨⟨((-201543423108113 : Dyadic) * half ^ 51),
        ((196370626289555 : Dyadic) * half ^ 51)⟩,
       ⟨((517479536871639 : Dyadic) * half ^ 51),
        ((-70126538542677 : Dyadic) * half ^ 49)⟩⟩,
     ⟨⟨((-1317102289668425 : Dyadic) * half ^ 51),
        ((78846034474959 : Dyadic) * half ^ 51)⟩,
       ⟨((1649019123692159 : Dyadic) * half ^ 51),
        ((87501015410389 : Dyadic) * half ^ 50)⟩⟩,
     ⟨⟨((253848065295737 : Dyadic) * half ^ 51),
        ((165958417011867 : Dyadic) * half ^ 51)⟩,
       ⟨((-96155996345819 : Dyadic) * half ^ 51),
        ((-370765176670073 : Dyadic) * half ^ 49)⟩⟩,
     ⟨⟨((84135527881153 : Dyadic) * half ^ 51),
        ((-157968056881763 : Dyadic) * half ^ 51)⟩,
       ⟨((-476876780460263 : Dyadic) * half ^ 51),
        ((89877869997469 : Dyadic) * half ^ 49)⟩⟩⟩
private lemma word3Step63 :
    word3Chunk63.foldl (fun acc a => a.applyPacked acc)
      word3State63 = word3State64 := by decide +kernel

private def word3Chunk64 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word3State65 : PackedMat2 :=
    ⟨⟨⟨((-720920286980477 : Dyadic) * half ^ 51),
        ((78904382768777 : Dyadic) * half ^ 51)⟩,
       ⟨((-301446856892711 : Dyadic) * half ^ 49),
        ((8419502067819 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-80611476977133 : Dyadic) * half ^ 48),
        ((-844237473389379 : Dyadic) * half ^ 51)⟩,
       ⟨((-224809345577615 : Dyadic) * half ^ 51),
        ((723679501998205 : Dyadic) * half ^ 51)⟩⟩,
     ⟨⟨((80611476977133 : Dyadic) * half ^ 48),
        ((844237473389379 : Dyadic) * half ^ 51)⟩,
       ⟨((-224809345577615 : Dyadic) * half ^ 51),
        ((723679501998205 : Dyadic) * half ^ 51)⟩⟩,
     ⟨⟨((-720920286980477 : Dyadic) * half ^ 51),
        ((78904382768777 : Dyadic) * half ^ 51)⟩,
       ⟨((301446856892711 : Dyadic) * half ^ 49),
        ((-8419502067819 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word3Step64 :
    word3Chunk64.foldl (fun acc a => a.applyPacked acc)
      word3State64 = word3State65 := by decide +kernel

private def word3Chunk65 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word3State66 : PackedMat2 :=
    ⟨⟨⟨((-2412356365729431 : Dyadic) * half ^ 52),
        ((27134375731627 : Dyadic) * half ^ 50)⟩,
       ⟨((-630857323764037 : Dyadic) * half ^ 52),
        ((895472845276055 : Dyadic) * half ^ 51)⟩⟩,
     ⟨⟨((-1539601588595303 : Dyadic) * half ^ 52),
        ((-382396396817015 : Dyadic) * half ^ 52)⟩,
       ⟨((-2165318159006691 : Dyadic) * half ^ 52),
        ((-370811207628403 : Dyadic) * half ^ 52)⟩⟩,
     ⟨⟨((376603802222709 : Dyadic) * half ^ 51),
        ((1852459873800997 : Dyadic) * half ^ 52)⟩,
       ⟨((2896297297153 : Dyadic) * half ^ 50),
        ((-156429142602847 : Dyadic) * half ^ 51)⟩⟩,
     ⟨⟨((949741596739309 : Dyadic) * half ^ 51),
        ((-760803422373367 : Dyadic) * half ^ 51)⟩,
       ⟨((-841204093812801 : Dyadic) * half ^ 51),
        ((-890749520982697 : Dyadic) * half ^ 52)⟩⟩⟩
private lemma word3Step65 :
    word3Chunk65.foldl (fun acc a => a.applyPacked acc)
      word3State65 = word3State66 := by decide +kernel

private def word3Chunk66 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word3State67 : PackedMat2 :=
    ⟨⟨⟨((2900407090463169 : Dyadic) * half ^ 53),
        ((-601959079411075 : Dyadic) * half ^ 51)⟩,
       ⟨((-2047334007493467 : Dyadic) * half ^ 53),
        ((-3574826240000739 : Dyadic) * half ^ 53)⟩⟩,
     ⟨⟨((1280978192683951 : Dyadic) * half ^ 53),
        ((293650848144405 : Dyadic) * half ^ 51)⟩,
       ⟨((503366289730007 : Dyadic) * half ^ 53),
        ((-3654990753541719 : Dyadic) * half ^ 53)⟩⟩,
     ⟨⟨((1280978192683951 : Dyadic) * half ^ 53),
        ((293650848144405 : Dyadic) * half ^ 51)⟩,
       ⟨((-503366289730007 : Dyadic) * half ^ 53),
        ((3654990753541719 : Dyadic) * half ^ 53)⟩⟩,
     ⟨⟨((-2900407090463169 : Dyadic) * half ^ 53),
        ((601959079411075 : Dyadic) * half ^ 51)⟩,
       ⟨((-2047334007493467 : Dyadic) * half ^ 53),
        ((-3574826240000739 : Dyadic) * half ^ 53)⟩⟩⟩
private lemma word3Step66 :
    word3Chunk66.foldl (fun acc a => a.applyPacked acc)
      word3State66 = word3State67 := by decide +kernel

private def word3Chunk67 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word3State68 : PackedMat2 :=
    ⟨⟨⟨((6731762047896621 : Dyadic) * half ^ 54),
        ((3561492443304177 : Dyadic) * half ^ 54)⟩,
       ⟨((-8101550911932917 : Dyadic) * half ^ 54),
        ((1140877830577631 : Dyadic) * half ^ 53)⟩⟩,
     ⟨⟨((9310722909534019 : Dyadic) * half ^ 54),
        ((-3136769380279885 : Dyadic) * half ^ 54)⟩,
       ⟨((-4842879618379339 : Dyadic) * half ^ 54),
        ((-153035438064999 : Dyadic) * half ^ 49)⟩⟩,
     ⟨⟨((8033903398359853 : Dyadic) * half ^ 54),
        ((-558480411394335 : Dyadic) * half ^ 52)⟩,
       ⟨((-1760364637800083 : Dyadic) * half ^ 54),
        ((-7076801263956679 : Dyadic) * half ^ 54)⟩⟩,
     ⟨⟨((5843248104459439 : Dyadic) * half ^ 54),
        ((-171223608004537 : Dyadic) * half ^ 52)⟩,
       ⟨((1279736782148915 : Dyadic) * half ^ 54),
        ((7416656479914769 : Dyadic) * half ^ 54)⟩⟩⟩
private lemma word3Step67 :
    word3Chunk67.foldl (fun acc a => a.applyPacked acc)
      word3State67 = word3State68 := by decide +kernel

private def word3Chunk68 : List Letter := [.t, .h, .s]
private def word3State69 : PackedMat2 :=
    ⟨⟨⟨((8458626461384145 : Dyadic) * half ^ 54),
        ((1446830208284495 : Dyadic) * half ^ 52)⟩,
       ⟨((5418525041435147 : Dyadic) * half ^ 54),
        ((-2176534227683367 : Dyadic) * half ^ 52)⟩⟩,
     ⟨⟨((-855013719124623 : Dyadic) * half ^ 54),
        ((604585998800551 : Dyadic) * half ^ 54)⟩,
       ⟨((-1335641574775791 : Dyadic) * half ^ 54),
        ((944441214758641 : Dyadic) * half ^ 54)⟩⟩,
     ⟨⟨((855013719124623 : Dyadic) * half ^ 54),
        ((-604585998800551 : Dyadic) * half ^ 54)⟩,
       ⟨((-1335641574775791 : Dyadic) * half ^ 54),
        ((944441214758641 : Dyadic) * half ^ 54)⟩⟩,
     ⟨⟨((8458626461384145 : Dyadic) * half ^ 54),
        ((1446830208284495 : Dyadic) * half ^ 52)⟩,
       ⟨((-5418525041435147 : Dyadic) * half ^ 54),
        ((2176534227683367 : Dyadic) * half ^ 52)⟩⟩⟩
private lemma word3Step68 :
    word3Chunk68.foldl (fun acc a => a.applyPacked acc)
      word3State68 = word3State69 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word3_check : check word3 3 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word3 = word3State69.toMatrix := by
    unfold evalRingPacked
    change ((
      word3Chunk0 ++ word3Chunk1 ++ word3Chunk2 ++ word3Chunk3 ++
      word3Chunk4 ++ word3Chunk5 ++ word3Chunk6 ++ word3Chunk7 ++
      word3Chunk8 ++ word3Chunk9 ++ word3Chunk10 ++ word3Chunk11 ++
      word3Chunk12 ++ word3Chunk13 ++ word3Chunk14 ++ word3Chunk15 ++
      word3Chunk16 ++ word3Chunk17 ++ word3Chunk18 ++ word3Chunk19 ++
      word3Chunk20 ++ word3Chunk21 ++ word3Chunk22 ++ word3Chunk23 ++
      word3Chunk24 ++ word3Chunk25 ++ word3Chunk26 ++ word3Chunk27 ++
      word3Chunk28 ++ word3Chunk29 ++ word3Chunk30 ++ word3Chunk31 ++
      word3Chunk32 ++ word3Chunk33 ++ word3Chunk34 ++ word3Chunk35 ++
      word3Chunk36 ++ word3Chunk37 ++ word3Chunk38 ++ word3Chunk39 ++
      word3Chunk40 ++ word3Chunk41 ++ word3Chunk42 ++ word3Chunk43 ++
      word3Chunk44 ++ word3Chunk45 ++ word3Chunk46 ++ word3Chunk47 ++
      word3Chunk48 ++ word3Chunk49 ++ word3Chunk50 ++ word3Chunk51 ++
      word3Chunk52 ++ word3Chunk53 ++ word3Chunk54 ++ word3Chunk55 ++
      word3Chunk56 ++ word3Chunk57 ++ word3Chunk58 ++ word3Chunk59 ++
      word3Chunk60 ++ word3Chunk61 ++ word3Chunk62 ++ word3Chunk63 ++
      word3Chunk64 ++ word3Chunk65 ++ word3Chunk66 ++ word3Chunk67 ++
      word3Chunk68
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word3Step0, word3Step1, word3Step2, word3Step3, word3Step4,
      word3Step5, word3Step6, word3Step7, word3Step8, word3Step9,
      word3Step10, word3Step11, word3Step12, word3Step13, word3Step14,
      word3Step15, word3Step16, word3Step17, word3Step18, word3Step19,
      word3Step20, word3Step21, word3Step22, word3Step23, word3Step24,
      word3Step25, word3Step26, word3Step27, word3Step28, word3Step29,
      word3Step30, word3Step31, word3Step32, word3Step33, word3Step34,
      word3Step35, word3Step36, word3Step37, word3Step38, word3Step39,
      word3Step40, word3Step41, word3Step42, word3Step43, word3Step44,
      word3Step45, word3Step46, word3Step47, word3Step48, word3Step49,
      word3Step50, word3Step51, word3Step52, word3Step53, word3Step54,
      word3Step55, word3Step56, word3Step57, word3Step58, word3Step59,
      word3Step60, word3Step61, word3Step62, word3Step63, word3Step64,
      word3Step65, word3Step66, word3Step67, word3Step68]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
