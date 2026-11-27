(* 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Lists.Streams List Arith Lia ZifyNat ZifyN ZifyBool NArith ZArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

From BusyCoq Require Import PR80Core PR80EntryBlocks PR80MiddleBlocks.

Section Mid2.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

Lemma eMid12_z2_lo_to_M (pM pA u1 pB pC : nat)
  (hinv : InvEmid12 pM pA (u1 + 2) pB pC) (hlo : pC mod 12 < 6) : ReachesInvM (eMid12Cfg pM pA (u1 + 2) pB pC).
Proof.
  destruct hinv as [_ [hA [hM [hB [hC [h12MC [h36M h1060]]]]]]].
  destruct (pC mod 12) as [| [| [| [| [| [| _rem]]]]]] eqn:hrc.
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c0_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 30%N) (symConst 3%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 156%N) (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 31) (4) (12 * u2 + 4 * u3 + (#157)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 31) (4) (12 * u2 + 4 * u3 + (#157)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c0_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 2 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 30%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 32) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + 32) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c1_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z2 (v5 u0 u1 u2 u3 u4) 5 (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 165%N) (6 * u2 + 34) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#166)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + 34) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#166)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c1_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 5 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 31%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 33) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + 33) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c2_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 5 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 31%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 33) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + 33) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c2_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 31%N) (symConst 2%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 161%N) (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 32) (3) (12 * u2 + 4 * u3 + (#162)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 32) (3) (12 * u2 + 4 * u3 + (#162)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c3_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 3 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 32%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 34) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + 34) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c3_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z2 (v5 u0 u1 u2 u3 u4) 3 (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 35) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + 35) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c4_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 32%N) (symOne) (mkSymN 0%N 0%N 12%N 4%N 0%N 162%N) (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 33) (2) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 33) (2) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c4_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 3 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 32%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 34) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + 34) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c5_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z2 (v5 u0 u1 u2 u3 u4) 4 (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 36) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + 36) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c5_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 4 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 35) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + 35) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    fast_lia.
  }
Qed.


Lemma eMid12_z2_hi_to_M (pM pA u1 pB pC : nat)
  (hinv : InvEmid12 pM pA (u1 + 2) pB pC) (hhi : 6 <= pC mod 12) : ReachesInvM (eMid12Cfg pM pA (u1 + 2) pB pC).
Proof.
  destruct hinv as [_ [hA [hM [hB [hC [h12MC [h36M h1060]]]]]]].
  destruct (pC mod 12) as [| [| [| [| [| [| [| [| [| [| [| [| _rem]]]]]]]]]]]] eqn:hrc.
  {
    fast_lia.
  }
  {
    fast_lia.
  }
  {
    fast_lia.
  }
  {
    fast_lia.
  }
  {
    fast_lia.
  }
  {
    fast_lia.
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c6_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 4 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 35) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + 35) (u1 + 2) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c6_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (symZero) (mkSymN 0%N 0%N 12%N 4%N 0%N 167%N) (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 34) (1) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) (u1 + 2) (6 * u2 + 34) (1) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c7_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 0 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 36) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + 36) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c7_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z2 (v5 u0 u1 u2 u3 u4) 0 (mkSymN 0%N 0%N 6%N 0%N 0%N 36%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 37) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + 37) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c8_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 25%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (symConst 5%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 162%N) (u2 + u4 + 26) (u0 + (#50)) (u1 + 2) (6 * u2 + 35) (6) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 26) (u0 + (#50)) (u1 + 2) (6 * u2 + 35) (6) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c8_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 0 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 36) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + 36) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c9_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z2 (v5 u0 u1 u2 u3 u4) 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 37%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 38) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + 38) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c9_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 1 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 37) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + 37) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c10_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 1 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 37) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + 37) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c10_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 25%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (symConst 4%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 167%N) (u2 + u4 + 26) (u0 + (#50)) (u1 + 2) (6 * u2 + 36) (5) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 26) (u0 + (#50)) (u1 + 2) (6 * u2 + 36) (5) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c11_b0) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 2 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 36%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 38) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + 38) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_em_z2_c11_b1) (eval_eMid12_z2 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N) pM pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z2 (v5 u0 u1 u2 u3 u4) 2 (mkSymN 0%N 0%N 6%N 0%N 0%N 38%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 39) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + 39) (u1 + 2) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    fast_lia.
  }
Qed.


Lemma eMid12_to_M (pM pA z pB pC : nat)
  (hinv : InvEmid12 pM pA z pB pC) : ReachesInvM (eMid12Cfg pM pA z pB pC).
Proof.
  destruct z as [| [| u1]].
  - destruct hinv as [hz _]. fast_lia.
  - destruct (Nat.lt_ge_cases (pC mod 12) 6) as [h | h].
    + exact (eMid12_z1_lo_to_M pM pA pB pC hinv h).
    + exact (eMid12_z1_hi_to_M pM pA pB pC hinv h).
  - replace (S (S u1)) with (u1 + 2) in * by fast_lia.
    destruct (Nat.lt_ge_cases (pC mod 12) 6) as [h | h].
    + exact (eMid12_z2_lo_to_M pM pA u1 pB pC hinv h).
    + exact (eMid12_z2_hi_to_M pM pA u1 pB pC hinv h).
Qed.


End Mid2.

Section Tail.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

(* Run the certified symbolic machine to obtain the endpoint. Ltac only
   proposes a closed equality; Coq checks it before it is used by a bridge. *)
Local Notation "'computed_symbolic_certificate' bits start" :=
  (ltac:(
    let lhs := constr:(symRunBits bits start) in
    let rhs := eval vm_compute in lhs in
    exact (lhs = rhs))) (at level 10, bits at level 0, start at level 0).

(* #### Stage 3: `InvEclean` → `ReachesInvM` (12 `rfl` lemmas) *)

Lemma rfl_ec_z1_c0 :
  computed_symbolic_certificate [4; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 281%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z1_c1 :
  computed_symbolic_certificate [5; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 282%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z1_c2 :
  computed_symbolic_certificate [5; 4; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 283%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z1_c3 :
  computed_symbolic_certificate [6; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 284%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z1_c4 :
  computed_symbolic_certificate [6; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 285%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z1_c5 :
  computed_symbolic_certificate [6; 4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 286%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z2_c0 :
  computed_symbolic_certificate [4; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 281%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z2_c1 :
  computed_symbolic_certificate [5; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 282%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z2_c2 :
  computed_symbolic_certificate [5; 4; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 283%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z2_c3 :
  computed_symbolic_certificate [6; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 284%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z2_c4 :
  computed_symbolic_certificate [6; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 285%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ec_z2_c5 :
  computed_symbolic_certificate [6; 4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 286%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


Lemma eClean_to_M (pA z pB pC : nat)
  (hinv : InvEclean pA z pB pC) : ReachesInvM (eCleanCfg pA z pB pC).
Proof.
  destruct hinv as [hz [hA [hB [hC h1060]]]].
  destruct (z) as [| [| u1]] eqn:hz_eq.
  {
    fast_lia.
  }
  {
    destruct (pC mod 6) as [| [| [| [| [| [| _rem]]]]]] eqn:hrc.
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_ec_z1_c0) (eval_eClean_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 281%N) pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 0) 5 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 331%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symConst 3%N) (6 * u2 + u3 + (#333)) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + u3 + (#333)) (1) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_ec_z1_c1) (eval_eClean_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 282%N) pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 0) 3 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 332%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symConst 3%N) (6 * u2 + u3 + (#334)) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + u3 + (#334)) (1) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_ec_z1_c2) (eval_eClean_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 283%N) pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 0) 4 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 333%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symConst 3%N) (6 * u2 + u3 + (#335)) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + u3 + (#335)) (1) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_ec_z1_c3) (eval_eClean_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 284%N) pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 0) 0 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 334%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 47%N) (symConst 3%N) (6 * u2 + u3 + (#336)) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + u3 + (#336)) (1) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_ec_z1_c4) (eval_eClean_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 285%N) pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 0) 1 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 335%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 47%N) (symConst 3%N) (6 * u2 + u3 + (#337)) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + u3 + (#337)) (1) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_ec_z1_c5) (eval_eClean_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 286%N) pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 0) 2 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 336%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 47%N) (symConst 3%N) (6 * u2 + u3 + (#338)) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + u3 + (#338)) (1) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      fast_lia.
    }
  }
  {
    replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
    destruct (pC mod 6) as [| [| [| [| [| [| _rem]]]]]] eqn:hrc.
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_ec_z2_c0) (eval_eClean_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 281%N) pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 0) 5 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 331%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symConst 3%N) (6 * u2 + u3 + (#333)) (u1 + 2) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + u3 + (#333)) (u1 + 2) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_ec_z2_c1) (eval_eClean_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 282%N) pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 0) 3 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 332%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symConst 3%N) (6 * u2 + u3 + (#334)) (u1 + 2) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + u3 + (#334)) (u1 + 2) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_ec_z2_c2) (eval_eClean_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 283%N) pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 0) 4 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 333%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symConst 3%N) (6 * u2 + u3 + (#335)) (u1 + 2) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + u3 + (#335)) (u1 + 2) (u0 + (#50)) (u2 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_ec_z2_c3) (eval_eClean_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 284%N) pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 0) 0 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 334%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 47%N) (symConst 3%N) (6 * u2 + u3 + (#336)) (u1 + 2) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + u3 + (#336)) (u1 + 2) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_ec_z2_c4) (eval_eClean_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 285%N) pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 0) 1 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 335%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 47%N) (symConst 3%N) (6 * u2 + u3 + (#337)) (u1 + 2) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + u3 + (#337)) (u1 + 2) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#282)) / 6) in * || pose (u2 := (pC - (#282)) / 6)).
      (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_ec_z2_c5) (eval_eClean_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 286%N) pA (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 0) 2 (symZero) (mkSymN 0%N 0%N 6%N 1%N 0%N 336%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 47%N) (symConst 3%N) (6 * u2 + u3 + (#338)) (u1 + 2) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + u3 + (#338)) (u1 + 2) (u0 + (#50)) (u2 + 48) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      fast_lia.
    }
  }
Qed.


(* #### Stage 2: `e0111Cfg` & `e0101Cfg` → `ReachesInvM` (6 `rfl` lemmas) *)

Lemma rfl_e0111_z1 :
  computed_symbolic_certificate [6; 5; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (symConst 7%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 107%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_e0111_z2 :
  computed_symbolic_certificate [7; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (symConst 7%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 109%N); sr_pair 2 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_e0111_z3 :
  computed_symbolic_certificate [7; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (symConst 7%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 109%N); sr_pair 2 0 (symConst 2%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_e0111_z4 :
  computed_symbolic_certificate [7; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (symConst 7%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 109%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 3%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_e0101_z1 :
  computed_symbolic_certificate [7; 5; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (symConst 8%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 115%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 12%N 0%N 1%N 0%N 0%N 309%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_e0101_z2 :
  computed_symbolic_certificate [7; 5; 4; 3; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (symConst 8%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 115%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 12%N 0%N 1%N 0%N 0%N 309%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


Lemma e0111_to_M (u0 z pB pC : nat)
  (hz : 1 <= z) (hB : #50 <= pB) (hC : #100 <= pC)
  (h12 : #340 <= 12 * u0 + pC) (h36 : 36 * u0 + #765 <= 3 * pC + 4 * pB)
  (h36_0 : 12 * u0 + #180 <= pC + 4 * pB) (h1060 : #1070 <= pC + pB) :
  ReachesInvM (e0111Cfg (6 * u0 + #110) z pB pC).
Proof.
  destruct (z) as [| [| [| [| u1]]]] eqn:hz_eq.
  {
    fast_lia.
  }
  {
    (set (u2 := pC - (#100)) in * || pose (u2 := pC - (#100))).
    (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_e0111_z1) (eval_e0111_z1 (v5 u0 0 u2 u3 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 107%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) (6 * u0 + (#110)) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMid0 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 18%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 121%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 52%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 93%N) (u0 + 19) (6 * u0 + (#122)) (u3 + (#53)) (u2 + (#94)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (eMid0_to_M (u0 + 19) (6 * u0 + (#122)) (u3 + (#53)) (u2 + (#94)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    (set (u2 := pC - (#100)) in * || pose (u2 := pC - (#100))).
    (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_e0111_z2) (eval_e0111_z2 (v5 u0 0 u2 u3 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 109%N) (symOne) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) (6 * u0 + (#110)) (2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMid12_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 18%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 116%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 92%N) (u0 + 19) (6 * u0 + (#117)) (u3 + (#55)) (u2 + (#93)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (eMid12_to_M (u0 + 19) (6 * u0 + (#117)) 1 (u3 + (#55)) (u2 + (#93)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    (set (u2 := pC - (#100)) in * || pose (u2 := pC - (#100))).
    (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_e0111_z3) (eval_e0111_z2 (v5 u0 0 u2 u3 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 109%N) (symConst 2%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) (6 * u0 + (#110)) (3) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMid12_z2 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 18%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 116%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 92%N) (u0 + 19) (6 * u0 + (#117)) (2) (u3 + (#55)) (u2 + (#93)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (eMid12_to_M (u0 + 19) (6 * u0 + (#117)) (2) (u3 + (#55)) (u2 + (#93)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (S (S (u1))))) with (u1 + 4) in * by fast_lia.
    (set (u2 := pC - (#100)) in * || pose (u2 := pC - (#100))).
    (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_e0111_z4) (eval_e0111_z2 (v5 u0 u1 u2 u3 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 109%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) (6 * u0 + (#110)) (u1 + 4) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMid12_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 18%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 116%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 92%N) (u0 + 19) (6 * u0 + (#117)) (u1 + 3) (u3 + (#55)) (u2 + (#93)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (eMid12_to_M (u0 + 19) (6 * u0 + (#117)) (u1 + 3) (u3 + (#55)) (u2 + (#93)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


Lemma e0101_to_M (u0 z pB pC : nat)
  (hz : 1 <= z) (hB : #50 <= pB) (hC : 12 * u0 + #310 <= pC) (hC560 : #560 <= pC) (h1060 : #1062 <= pC + pB) :
  ReachesInvM (e0101Cfg (6 * u0 + #116) z pB pC).
Proof.
  destruct (z) as [| [| u1]] eqn:hz_eq.
  {
    fast_lia.
  }
  {
    (set (u2 := pC - 12 * u0 - (#310)) in * || pose (u2 := pC - 12 * u0 - (#310))).
    (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_e0101_z1) (eval_e0101_z1 (v5 u0 0 u2 u3 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 115%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 12%N 0%N 1%N 0%N 0%N 309%N) (6 * u0 + (#116)) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMid12_z1 (v5 u0 0 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 19%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 124%N) (mkSymN 12%N 0%N 0%N 1%N 0%N 287%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 69%N) (u0 + 20) (6 * u0 + (#125)) (12 * u0 + u3 + (#288)) (u2 + (#70)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (eMid12_to_M (u0 + 20) (6 * u0 + (#125)) (1) (12 * u0 + u3 + (#288)) (u2 + (#70)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
    (set (u2 := pC - 12 * u0 - (#310)) in * || pose (u2 := pC - 12 * u0 - (#310))).
    (set (u3 := pB - (#50)) in * || pose (u3 := pB - (#50))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_e0101_z2) (eval_e0101_z2 (v5 u0 u1 u2 u3 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 115%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 49%N) (mkSymN 12%N 0%N 1%N 0%N 0%N 309%N) (6 * u0 + (#116)) (u1 + 2) pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMid12_z2 (v5 u0 u1 u2 u3 0) (mkSymN 1%N 0%N 0%N 0%N 0%N 19%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 124%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 12%N 0%N 0%N 1%N 0%N 287%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 69%N) (u0 + 20) (6 * u0 + (#125)) (u1 + 2) (12 * u0 + u3 + (#288)) (u2 + (#70)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (eMid12_to_M (u0 + 20) (6 * u0 + (#125)) (u1 + 2) (12 * u0 + u3 + (#288)) (u2 + (#70)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


End Tail.

Section Closure.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

(* Run the certified symbolic machine to obtain the endpoint. Ltac only
   proposes a closed equality; Coq checks it before it is used by a bridge. *)
Local Notation "'computed_symbolic_certificate' bits start" :=
  (ltac:(
    let lhs := constr:(symRunBits bits start) in
    let rhs := eval vm_compute in lhs in
    exact (lhs = rhs))) (at level 10, bits at level 0, start at level 0).

(* #### Stage 1: `InvM` → `postL11Cfg` → `ReachesInvM` (22 `rfl` lemmas + direct `era_L11_d0_loop`) *)

Lemma rfl_s1_r0_z1 :
  computed_symbolic_certificate [6; 4; 2; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r0_z2 :
  computed_symbolic_certificate [6; 4; 2; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r1_z1 :
  computed_symbolic_certificate [6; 5; 3; 2; 1] (mA, [sl_pair 1 0 (symZero); sl_mid (symZero); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r1_z2 :
  computed_symbolic_certificate [6; 5; 3; 2; 1] (mA, [sl_pair 1 0 (symZero); sl_mid (symZero); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r2_z1 :
  computed_symbolic_certificate [6; 4; 3; 2] (mA, [sl_pair 1 0 (symZero); sl_mid (symOne); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r2_z2 :
  computed_symbolic_certificate [6; 4; 3; 2] (mA, [sl_pair 1 0 (symZero); sl_mid (symOne); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r3_z1 :
  computed_symbolic_certificate [8; 5] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 2%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r3_z2 :
  computed_symbolic_certificate [8; 5] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 2%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r4_z1 :
  computed_symbolic_certificate [7; 5; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 3%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r4_z2 :
  computed_symbolic_certificate [7; 5; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 3%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r5_z1 :
  computed_symbolic_certificate [7; 6; 2] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 4%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r5_z2 :
  computed_symbolic_certificate [7; 6; 2] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 4%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r6_z1 :
  computed_symbolic_certificate [7; 6; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 5%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r6_z2 :
  computed_symbolic_certificate [7; 6; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 5%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r7_z1 :
  computed_symbolic_certificate [7; 6; 5; 2; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 6%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r7_z2 :
  computed_symbolic_certificate [7; 6; 5; 2; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 6%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r8_z1 :
  computed_symbolic_certificate [7; 6; 5; 1] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 7%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r8_z2 :
  computed_symbolic_certificate [7; 6; 5; 1] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 7%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r9_z1 :
  computed_symbolic_certificate [8; 4; 2; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 8%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r9_z2 :
  computed_symbolic_certificate [8; 4; 2; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 8%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r10_z1 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 9%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_s1_r10_z2 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2; 1; 0] (mA, [sl_pair 1 0 (symZero); sl_mid (symConst 9%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 0 0 (symZero); sr_pair 1 1 (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N); sr_pair 1 1 (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


Lemma postL11_to_M (r q k z C0 : nat)
  (hr : r < 11) (hk : k <= 5) (hz : 1 <= z)
  (hC1 : #81 * q + 9 * r + #243 <= C0) (hC2 : #2046 <= C0 + 18 * q) :
  ReachesInvM (postL11Cfg r (6 * q + k) z C0).
Proof.
  (set (u := 6 * q + k) in * || pose (u := 6 * q + k)).
  destruct (r) as [| [| [| [| [| [| [| [| [| [| [| _rem]]]]]]]]]]] eqn:hreq.
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r0_z1) (eval_postL11_r0_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_e0111_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 107%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 55%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 98%N) (6 * (u) + (#110)) (3 * u + (#56)) (u2 + (#99)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (e0111_to_M (u) (1) (3 * u + (#56)) (u2 + (#99)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r0_z2) (eval_postL11_r0_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_e0111_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 109%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 55%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 98%N) (6 * (u) + (#110)) (u1 + 2) (3 * u + (#56)) (u2 + (#99)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (e0111_to_M (u) (u1 + 2) (3 * u + (#56)) (u2 + (#99)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r1_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symZero) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 1 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 118%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 64%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 89%N) (6 * u + (#119)) (3 * u + (#65)) (u2 + (#90)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#119)) (1) (3 * u + (#65)) (u2 + (#90)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r1_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symZero) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 1 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 118%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 64%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 89%N) (6 * u + (#119)) (u1 + 2) (3 * u + (#65)) (u2 + (#90)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#119)) (u1 + 2) (3 * u + (#65)) (u2 + (#90)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r2_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symOne) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 2 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 120%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 62%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 91%N) (6 * u + (#121)) (3 * u + (#63)) (u2 + (#92)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#121)) (1) (3 * u + (#63)) (u2 + (#92)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r2_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symOne) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 2 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 120%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 62%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 91%N) (6 * u + (#121)) (u1 + 2) (3 * u + (#63)) (u2 + (#92)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#121)) (u1 + 2) (3 * u + (#63)) (u2 + (#92)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r3_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 2%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 3 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_e0101_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 115%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 74%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 79%N) (6 * u + (#116)) (3 * u + (#75)) (u2 + (#80)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (e0101_to_M u (1) (3 * u + (#75)) (u2 + (#80)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r3_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 2%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 3 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_e0101_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 115%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 74%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 79%N) (6 * u + (#116)) (u1 + 2) (3 * u + (#75)) (u2 + (#80)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (e0101_to_M u (u1 + 2) (3 * u + (#75)) (u2 + (#80)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r4_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 3%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 4 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 128%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 68%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 85%N) (6 * u + (#129)) (3 * u + (#69)) (u2 + (#86)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#129)) (1) (3 * u + (#69)) (u2 + (#86)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r4_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 3%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 4 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 128%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 68%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 85%N) (6 * u + (#129)) (u1 + 2) (3 * u + (#69)) (u2 + (#86)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#129)) (u1 + 2) (3 * u + (#69)) (u2 + (#86)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r5_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 4%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 5 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 132%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 71%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 82%N) (6 * u + (#133)) (3 * u + (#72)) (u2 + (#83)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#133)) (1) (3 * u + (#72)) (u2 + (#83)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r5_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 4%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 5 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 132%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 71%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 82%N) (6 * u + (#133)) (u1 + 2) (3 * u + (#72)) (u2 + (#83)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#133)) (u1 + 2) (3 * u + (#72)) (u2 + (#83)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r6_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 5%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 6 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 134%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 70%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 83%N) (6 * u + (#135)) (3 * u + (#71)) (u2 + (#84)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#135)) (1) (3 * u + (#71)) (u2 + (#84)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r6_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 5%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 6 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 134%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 70%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 83%N) (6 * u + (#135)) (u1 + 2) (3 * u + (#71)) (u2 + (#84)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#135)) (u1 + 2) (3 * u + (#71)) (u2 + (#84)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r7_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 6%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 7 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 138%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 74%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 79%N) (6 * u + (#139)) (3 * u + (#75)) (u2 + (#80)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#139)) (1) (3 * u + (#75)) (u2 + (#80)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r7_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 6%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 7 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 138%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 74%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 79%N) (6 * u + (#139)) (u1 + 2) (3 * u + (#75)) (u2 + (#80)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#139)) (u1 + 2) (3 * u + (#75)) (u2 + (#80)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r8_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 7%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 8 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 140%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 73%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 80%N) (6 * u + (#141)) (3 * u + (#74)) (u2 + (#81)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#141)) (1) (3 * u + (#74)) (u2 + (#81)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r8_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 7%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 8 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 140%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 73%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 80%N) (6 * u + (#141)) (u1 + 2) (3 * u + (#74)) (u2 + (#81)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#141)) (u1 + 2) (3 * u + (#74)) (u2 + (#81)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r9_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 8%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 9 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_e0111_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 137%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 70%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 83%N) (6 * (u + 5) + (#110)) (3 * u + (#71)) (u2 + (#84)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (e0111_to_M (u + 5) (1) (3 * u + (#71)) (u2 + (#84)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r9_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 8%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 9 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_e0111_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 139%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 70%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 83%N) (6 * (u + 5) + (#110)) (u1 + 2) (3 * u + (#71)) (u2 + (#84)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (e0111_to_M (u + 5) (u1 + 2) (3 * u + (#71)) (u2 + (#84)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia)) (ltac:(fast_lia))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    destruct (z) as [| [| u1]] eqn:hz_eq.
    {
      fast_lia.
    }
    {
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 u2 0 0) rfl_s1_r10_z1) (eval_postL11_r1_z1 (v5 u 0 u2 0 0) (symConst 9%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 112%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 10 u C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z1 (v5 u 0 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 146%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 75%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 78%N) (6 * u + (#147)) (3 * u + (#76)) (u2 + (#79)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#147)) (1) (3 * u + (#76)) (u2 + (#79)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
      (set (u2 := C0 - (#100)) in * || pose (u2 := C0 - (#100))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u u1 u2 0 0) rfl_s1_r10_z2) (eval_postL11_r1_z2 (v5 u u1 u2 0 0) (symConst 9%N) (mkSymN 6%N 0%N 0%N 0%N 0%N 114%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 54%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 99%N) 10 u (u1 + 2) C0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eClean_z2 (v5 u u1 u2 0 0) (mkSymN 6%N 0%N 0%N 0%N 0%N 146%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 3%N 0%N 0%N 0%N 0%N 75%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 78%N) (6 * u + (#147)) (u1 + 2) (3 * u + (#76)) (u2 + (#79)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eClean_to_M (6 * u + (#147)) (u1 + 2) (3 * u + (#76)) (u2 + (#79)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    fast_lia.
  }
Qed.


Lemma invM_step {m z c k : nat} (hinv : InvM m z c k) :
  ReachesInvM (mCfg m z c k).
Proof.
  destruct hinv as [hk [hz [hm [h9m hc2100]]]].
  pose (K := m / 11).
  pose (r := m mod 11).
  pose (q := K - 3).
  assert (hK : 1 <= K) by fast_lia.
  assert (hB : 18 * K <= c) by fast_lia.
  pose (ms := [mi_t (6 * k + 6); mi_z z; mi_t (3 * k + 1)]).
  pose proof (era_L11_d0_loop_plus r ms c ([S0; S1] *> 0inf) K hK hB) as hloop.
  assert (h0 : eraL11Cfg r ms c ([S0; S1] *> 0inf) K 0 = mCfg m z c k).
  { unfold eraL11Cfg, ms, mCfg.
    cbn [encMidR encMidItemR].
    rewrite !Nat.mul_0_r, !Nat.sub_0_r, !lpow_0, !Str_app_nil, list_1011_eq, wT_cons_pow.
    replace (r + 11 * K) with m by fast_lia.
    replace (6 * k + 6 + 1) with (6 * k + 7) by fast_lia.
    reflexivity. }
  assert (hK_cfg : eraL11Cfg r ms c ([S0; S1] *> 0inf) K K =
      postL11Cfg r (6 * q + k) z (c - 18 * K)).
  { unfold eraL11Cfg, ms, postL11Cfg.
    cbn [encMidR encMidItemR].
    rewrite !Nat.sub_diag, Nat.mul_0_r, Nat.add_0_r, list_1011_eq.
    rewrite wT_cons_pow, !pow_append_pow.
    replace (36 * K + 1 + (6 * k + 6)) with (6 * (6 * q + k) + #115) by fast_lia.
    replace (3 * k + 1 + 18 * K) with (3 * (6 * q + k) + #55) by fast_lia.
    reflexivity. }
  rewrite h0, hK_cfg in hloop.
  destruct (postL11_to_M r q k z (c - 18 * K)
      (ltac:(fast_lia)) hk hz (ltac:(fast_lia)) (ltac:(fast_lia)))
    as [m' [z' [c' [k' [hm' hrest]]]]].
  exists m', z', c', k'. split; [exact hm' | exact (ptrans hloop hrest)].
Qed.


(* #### Blank-Tape Entry & Main Theorem *)

End Closure.
