(* 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Lists.Streams List Arith Lia ZifyNat ZifyN ZifyBool NArith ZArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

From BusyCoq Require Import PR80Core PR80EntryBlocks.

Section Entry.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

Lemma convEntry_to_M (i : nat) (hi : i < 6) (pB z pA pM R0 : nat)
  (hinv : InvConvEntry i pB z pA pM R0) : ReachesInvM (convEntryCfg i pB z pA pM R0).
Proof.
  destruct hinv as [hA [hB [hz [hM [hR0 [h9M h2120]]]]]].
  destruct i as [| [| [| [| [| [| _i]]]]]]; [| | | | | | fast_lia].
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      destruct (z) as [| [| [| [| [| [| u1]]]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_0_b0_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 34%N) (symConst 28%N) (symConst 12%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 89%N) (u2 + 35) (u0 + 4 * u3 + u4 + (#90)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 35), (1), (u0 + 4 * u3 + u4 + (#90)), (4). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 0 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_0_b0_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 3 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 36%N) (symConst 30%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 12%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 33%N) (u2 + 37) (u0 + (#51)) (4 * u3 + u4 + 34) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 37), (u0 + (#51)), (4 * u3 + u4 + 34), (4). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_0_b0_z4) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 4 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 36%N) (symConst 22%N) (symConst 9%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 97%N) (u2 + 37) (u0 + 4 * u3 + u4 + (#98)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 37), (1), (u0 + 4 * u3 + u4 + (#98)), (3). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_0_b0_z5) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (5) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 1 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (S (S (u1))))))) with (u1 + 6) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_0_b0_z6) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 6) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 1 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
    {
      destruct (z) as [| [| [| [| u1]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_0_b1_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 34%N) (symConst 36%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 15%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 29%N) (u2 + 35) (u0 + (#51)) (4 * u3 + u4 + 30) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 35), (u0 + (#51)), (4 * u3 + u4 + 30), (5). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 0 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_0_b1_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (3) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 0 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (u1))))) with (u1 + 4) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_0_b1_z4) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 4) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 0 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      destruct (z) as [| [| [| [| [| [| u1]]]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_1_b0_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 36%N) (symConst 22%N) (symConst 9%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 92%N) (u2 + 37) (u0 + 4 * u3 + u4 + (#93)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 37), (1), (u0 + 4 * u3 + u4 + (#93)), (3). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 1 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_1_b0_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 3 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 38%N) (symConst 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 9%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 36%N) (u2 + 39) (u0 + (#51)) (4 * u3 + u4 + 37) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 39), (u0 + (#51)), (4 * u3 + u4 + 37), (3). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_1_b0_z4) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 4 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 38%N) (symConst 16%N) (symConst 6%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 100%N) (u2 + 39) (u0 + 4 * u3 + u4 + (#101)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 39), (1), (u0 + 4 * u3 + u4 + (#101)), (2). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_1_b0_z5) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (5) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 2 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (S (S (u1))))))) with (u1 + 6) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_1_b0_z6) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 6) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 2 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
    {
      destruct (z) as [| [| [| [| u1]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_1_b1_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 36%N) (symConst 30%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 12%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 32%N) (u2 + 37) (u0 + (#51)) (4 * u3 + u4 + 33) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 37), (u0 + (#51)), (4 * u3 + u4 + 33), (4). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 1 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_1_b1_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (3) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 1 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (u1))))) with (u1 + 4) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_1_b1_z4) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 4) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 1 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      destruct (z) as [| [| [| [| [| [| u1]]]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_2_b0_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 38%N) (symConst 16%N) (symConst 6%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 95%N) (u2 + 39) (u0 + 4 * u3 + u4 + (#96)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 39), (1), (u0 + 4 * u3 + u4 + (#96)), (2). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 2 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_2_b0_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 3 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 40%N) (symConst 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 6%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 39%N) (u2 + 41) (u0 + (#51)) (4 * u3 + u4 + 40) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 41), (u0 + (#51)), (4 * u3 + u4 + 40), (2). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_2_b0_z4) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 4 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 40%N) (symConst 10%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 103%N) (u2 + 41) (u0 + 4 * u3 + u4 + (#104)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 41), (1), (u0 + 4 * u3 + u4 + (#104)), (1). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_2_b0_z5) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (5) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 5 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (S (S (u1))))))) with (u1 + 6) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_2_b0_z6) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 6) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 5 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
    {
      destruct (z) as [| [| [| [| u1]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_2_b1_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 38%N) (symConst 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 9%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 35%N) (u2 + 39) (u0 + (#51)) (4 * u3 + u4 + 36) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 39), (u0 + (#51)), (4 * u3 + u4 + 36), (3). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 2 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_2_b1_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (3) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 2 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (u1))))) with (u1 + 4) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_2_b1_z4) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 4) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 2 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      destruct (z) as [| [| [| [| [| [| u1]]]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_3_b0_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 42%N) (symConst 4%N) (symZero) (mkSymN 1%N 0%N 0%N 4%N 1%N 101%N) (u2 + 43) (u0 + 4 * u3 + u4 + (#102)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 43), (1), (u0 + 4 * u3 + u4 + (#102)), (0). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 3 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_3_b0_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 3 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 44%N) (symConst 6%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 45%N) (u2 + 45) (u0 + (#51)) (4 * u3 + u4 + 46) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 45), (u0 + (#51)), (4 * u3 + u4 + 46), (0). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_3_b0_z4) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 4 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 33%N) (symConst 34%N) (symConst 15%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 91%N) (u2 + 34) (u0 + 4 * u3 + u4 + (#92)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 34), (1), (u0 + 4 * u3 + u4 + (#92)), (5). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_3_b0_z5) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (5) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 4 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (S (S (u1))))))) with (u1 + 6) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_3_b0_z6) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 6) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 4 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
    {
      destruct (z) as [| [| [| [| u1]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_3_b1_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 42%N) (symConst 12%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 41%N) (u2 + 43) (u0 + (#51)) (4 * u3 + u4 + 42) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 43), (u0 + (#51)), (4 * u3 + u4 + 42), (1). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 3 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_3_b1_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (3) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 3 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (u1))))) with (u1 + 4) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_3_b1_z4) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 4) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 3 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      destruct (z) as [| [| [| [| [| [| u1]]]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_4_b0_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 33%N) (symConst 34%N) (symConst 15%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 86%N) (u2 + 34) (u0 + 4 * u3 + u4 + (#87)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 34), (1), (u0 + 4 * u3 + u4 + (#87)), (5). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 4 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_4_b0_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 3 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 36%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 15%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 30%N) (u2 + 36) (u0 + (#51)) (4 * u3 + u4 + 31) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 36), (u0 + (#51)), (4 * u3 + u4 + 31), (5). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_4_b0_z4) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 4 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 28%N) (symConst 12%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 94%N) (u2 + 36) (u0 + 4 * u3 + u4 + (#95)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 36), (1), (u0 + 4 * u3 + u4 + (#95)), (4). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_4_b0_z5) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (5) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 47) (1) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 0 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 47) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (S (S (u1))))))) with (u1 + 6) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_4_b0_z6) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 6) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 47) (u1 + 2) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 0 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 47) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
    {
      destruct (z) as [| [| [| [| u1]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_4_b1_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 44%N) (symConst 6%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 44%N) (u2 + 45) (u0 + (#51)) (4 * u3 + u4 + 45) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 45), (u0 + (#51)), (4 * u3 + u4 + 45), (0). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 4 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_4_b1_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (3) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 4 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (u1))))) with (u1 + 4) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_4_b1_z4) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 4) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 4 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      destruct (z) as [| [| [| [| [| [| u1]]]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_5_b0_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 40%N) (symConst 10%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 98%N) (u2 + 41) (u0 + 4 * u3 + u4 + (#99)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 41), (1), (u0 + 4 * u3 + u4 + (#99)), (1). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 5 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_5_b0_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 3 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 42%N) (symConst 12%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 42%N) (u2 + 43) (u0 + (#51)) (4 * u3 + u4 + 43) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 43), (u0 + (#51)), (4 * u3 + u4 + 43), (1). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_5_b0_z4) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 4 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 42%N) (symConst 4%N) (symZero) (mkSymN 1%N 0%N 0%N 4%N 1%N 106%N) (u2 + 43) (u0 + 4 * u3 + u4 + (#107)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 43), (1), (u0 + 4 * u3 + u4 + (#107)), (0). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_5_b0_z5) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (5) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 3 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (S (S (u1))))))) with (u1 + 6) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_5_b0_z6) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 6) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 48%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 49) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 3 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 49) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
    {
      destruct (z) as [| [| [| [| u1]]]] eqn:hz_eq.
      {
        fast_lia.
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_5_b1_z1) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 40%N) (symConst 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 6%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 38%N) (u2 + 41) (u0 + (#51)) (4 * u3 + u4 + 39) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 41), (u0 + (#51)), (4 * u3 + u4 + 39), (2). split; [solve_inv | exact hstep].
      }
      {
        exact (convEntryZ2_to_M 5 (ltac:(fast_lia)) pB pA pM R0 (ltac:(solve_inv))).
      }
      {
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ce_5_b1_z3) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (symOne) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (3) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 u4) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (1) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (1) 5 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
      {
        replace (S (S (S (S (u1))))) with (u1 + 4) in * by fast_lia.
        (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ce_5_b1_z4) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB (u1 + 4) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 u4) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 4%N 1%N 47%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (4 * u3 + u4 + 48) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        destruct (convMLoop_to_M (u1 + 2) 5 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (4 * u3 + u4 + 48) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
        exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
      }
    }
  }
Qed.


End Entry.

Section Extra.
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

(* #### Stage 5: `InvEmidExtraPost` & `InvEmidExtra` → `ReachesInvM` (18 `rfl` lemmas + direct `era_E_loop`) *)

Lemma rfl_ep0_c0 :
  computed_symbolic_certificate [4; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep0_c1 :
  computed_symbolic_certificate [5; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symZero); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep0_c2 :
  computed_symbolic_certificate [5; 4; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep0_c3 :
  computed_symbolic_certificate [6] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 2%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep0_c4 :
  computed_symbolic_certificate [6; 3; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep0_c5 :
  computed_symbolic_certificate [6; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 4%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z1_c0 :
  computed_symbolic_certificate [5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N); sr_pair 1 2 (symZero); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z1_c1 :
  computed_symbolic_certificate [6; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symZero); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z1_c2 :
  computed_symbolic_certificate [6; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z1_c3 :
  computed_symbolic_certificate [6; 4; 3; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 2%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z1_c4 :
  computed_symbolic_certificate [6; 5; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z1_c5 :
  computed_symbolic_certificate [6; 5; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 4%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z2_c0 :
  computed_symbolic_certificate [5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N); sr_pair 1 2 (symZero); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z2_c1 :
  computed_symbolic_certificate [6; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symZero); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z2_c2 :
  computed_symbolic_certificate [6; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z2_c3 :
  computed_symbolic_certificate [6; 4; 3; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 2%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z2_c4 :
  computed_symbolic_certificate [6; 5; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ep12_z2_c5 :
  computed_symbolic_certificate [6; 5; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N); sr_mid (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N); sr_pair 1 2 (symZero); sr_pair 1 1 (symConst 4%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


Lemma eMidExtraPost0_to_M (pM pA Bd rC2 : nat)
  (hinv : InvEmidExtraPost0 pM pA Bd rC2) : ReachesInvM (eMidExtra0Cfg pM pA Bd rC2).
Proof.
  destruct hinv as [hrC2 [hA [hM [hBd [h9M h2120]]]]].
  destruct (rC2) as [| [| [| [| [| [| _rem]]]]]] eqn:hr.
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := Bd - 20) in * || pose (u2 := Bd - 20)).
    (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 0 u4) rfl_ep0_c0) (eval_eMidExtra0_c0 (v5 u0 0 u2 0 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N) pM pA Bd (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 0 u2 0 u4) 5 (symZero) (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N) (symZero) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (symConst 3%N) (u2 + 21) (2) (u0 + (#50)) (u4 + 46) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (convEntryZ2_to_M 5 (ltac:(fast_lia)) (u2 + 21) (u0 + (#50)) (u4 + 46) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := Bd - 20) in * || pose (u2 := Bd - 20)).
    (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 0 u4) rfl_ep0_c1) (eval_eMidExtra0_c1 (v5 u0 0 u2 0 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N) (symZero) pM pA Bd 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 0 u2 0 u4) 3 (symZero) (mkSymN 0%N 0%N 1%N 0%N 0%N 20%N) (symZero) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (symConst 3%N) (u2 + 22) (2) (u0 + (#50)) (u4 + 46) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (convEntryZ2_to_M 3 (ltac:(fast_lia)) (u2 + 22) (u0 + (#50)) (u4 + 46) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := Bd - 20) in * || pose (u2 := Bd - 20)).
    (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 0 u4) rfl_ep0_c2) (eval_eMidExtra0_c1 (v5 u0 0 u2 0 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N) (symOne) pM pA Bd 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 0 u2 0 u4) 4 (symZero) (mkSymN 0%N 0%N 1%N 0%N 0%N 21%N) (symZero) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (symConst 3%N) (u2 + 23) (2) (u0 + (#50)) (u4 + 46) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (convEntryZ2_to_M 4 (ltac:(fast_lia)) (u2 + 23) (u0 + (#50)) (u4 + 46) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := Bd - 20) in * || pose (u2 := Bd - 20)).
    (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 0 u4) rfl_ep0_c3) (eval_eMidExtra0_c1 (v5 u0 0 u2 0 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N) (symConst 2%N) pM pA Bd 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 0 u2 0 u4) 0 (symZero) (mkSymN 0%N 0%N 1%N 0%N 0%N 22%N) (symZero) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (symConst 3%N) (u2 + 24) (2) (u0 + (#50)) (u4 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (convEntryZ2_to_M 0 (ltac:(fast_lia)) (u2 + 24) (u0 + (#50)) (u4 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := Bd - 20) in * || pose (u2 := Bd - 20)).
    (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 0 u4) rfl_ep0_c4) (eval_eMidExtra0_c1 (v5 u0 0 u2 0 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N) (symConst 3%N) pM pA Bd 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 0 u2 0 u4) 1 (symZero) (mkSymN 0%N 0%N 1%N 0%N 0%N 23%N) (symZero) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (symConst 3%N) (u2 + 25) (2) (u0 + (#50)) (u4 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (convEntryZ2_to_M 1 (ltac:(fast_lia)) (u2 + 25) (u0 + (#50)) (u4 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := Bd - 20) in * || pose (u2 := Bd - 20)).
    (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 0 u4) rfl_ep0_c5) (eval_eMidExtra0_c1 (v5 u0 0 u2 0 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 19%N) (symConst 4%N) pM pA Bd 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 0 u2 0 u4) 2 (symZero) (mkSymN 0%N 0%N 1%N 0%N 0%N 24%N) (symZero) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (symConst 3%N) (u2 + 26) (2) (u0 + (#50)) (u4 + 47) (4) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (convEntryZ2_to_M 2 (ltac:(fast_lia)) (u2 + 26) (u0 + (#50)) (u4 + 47) (4) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    fast_lia.
  }
Qed.


Lemma eMidExtraPost12_to_M (pM pA z Bm Bd rC2 : nat)
  (hinv : InvEmidExtraPost12 pM pA z Bm Bd rC2) : ReachesInvM (eMidExtra12Cfg pM pA z Bm Bd rC2).
Proof.
  destruct hinv as [hrC2 [hz [hA [hM [hBm [hBd [hpar [h9M h2120]]]]]]]].
  destruct (z) as [| [| u1]] eqn:hz_eq.
  {
    fast_lia.
  }
  {
    destruct (rC2) as [| [| [| [| [| [| _rem]]]]]] eqn:hr.
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ep12_z1_c0) (eval_eMidExtra12_z1_c0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N) pM pA Bm Bd (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 3 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 52%N) (u3 + 21) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (u3 + 21) (1) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ep12_z1_c1) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N) (symZero) pM pA Bm Bd 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 4 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 52%N) (u3 + 21) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (u3 + 21) (1) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ep12_z1_c2) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N) (symOne) pM pA Bm Bd 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 0 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 56%N) (u3 + 21) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (u3 + 21) (1) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ep12_z1_c3) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N) (symConst 2%N) pM pA Bm Bd 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 1 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 56%N) (u3 + 21) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (u3 + 21) (1) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ep12_z1_c4) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N) (symConst 3%N) pM pA Bm Bd 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 2 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 60%N) (u3 + 21) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (u3 + 21) (1) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_ep12_z1_c5) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N) (symConst 4%N) pM pA Bm Bd 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 5 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 60%N) (u3 + 21) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (u3 + 21) (1) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      fast_lia.
    }
  }
  {
    replace (S (S (u1))) with (u1 + 2) in * by fast_lia.
    destruct (rC2) as [| [| [| [| [| [| _rem]]]]]] eqn:hr.
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ep12_z2_c0) (eval_eMidExtra12_z2_c0 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N) pM pA (u1 + 2) Bm Bd (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 3 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 52%N) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ep12_z2_c1) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N) (symZero) pM pA (u1 + 2) Bm Bd 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 4 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 52%N) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 46) (4 * u2 + (#53)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ep12_z2_c2) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N) (symOne) pM pA (u1 + 2) Bm Bd 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 0 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 56%N) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ep12_z2_c3) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N) (symConst 2%N) pM pA (u1 + 2) Bm Bd 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 1 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 56%N) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#57)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ep12_z2_c4) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 20%N) (symConst 3%N) pM pA (u1 + 2) Bm Bd 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 2 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 60%N) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (Bd - 20) / 2) in * || pose (u2 := (Bd - 20) / 2)).
      (set (u3 := Bm - 20) in * || pose (u3 := Bm - 20)).
      (set (u4 := pM - 46) in * || pose (u4 := pM - 46)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 u4) rfl_ep12_z2_c5) (eval_eMidExtra12_z2_c1 (v5 u0 u1 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 45%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 0%N 2%N 0%N 0%N 19%N) (symConst 4%N) pM pA (u1 + 2) Bm Bd 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z2 (v5 u0 u1 u2 u3 u4) 5 (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 19%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 46%N) (mkSymN 0%N 0%N 4%N 0%N 0%N 60%N) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (u3 + 21) (u1 + 2) (u0 + (#50)) (u4 + 47) (4 * u2 + (#61)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      fast_lia.
    }
  }
Qed.


Lemma eMidExtra0_to_M (pM pA d pC : nat)
  (hinv : InvEmidExtra0 pM pA d pC) : ReachesInvM (eMidExtra0Cfg pM pA d pC).
Proof.
  destruct hinv as [hd [hA [hC [h6MC [h18M h2CA]]]]].
  pose (K := pC / 6).
  pose (rC2 := pC mod 6).
  assert (hK : 1 <= K) by fast_lia.
  pose (ms := [mi_mid pM; mi_t pA; mi_mid 1; mi_z 1; mi_t d]).
  pose (tw := td0 pC [rpair 1 0 0]).
  assert (hmax : 6 * K <= maxReflD01 tw) by (unfold tw; cbn [maxReflD01]; fast_lia).
  pose proof (era_E_loop_plus ms tw I K hK hmax) as hloop.
  assert (h0 : eraECfg ms tw 0 = eMidExtra0Cfg pM pA d pC).
  { unfold eraECfg, ms, tw, eMidExtra0Cfg.
    cbn [encMidR encMidItemR buildAdvTowerD01 Nat.mul].
    rewrite !Nat.sub_0_r, !encR_pushRP.
    cbn [encR].
    rewrite pWord_1_2, pWord_1_1, pWord_1_0, add_one_0, !lpow_0, !lpow_1, !Str_app_nil.
    reflexivity. }
  assert (hK_cfg : eraECfg ms tw K = eMidExtra0Cfg (pM + K) pA (d + 6 * K) rC2).
  { unfold eraECfg, ms, tw, eMidExtra0Cfg.
    cbn [encMidR encMidItemR buildAdvTowerD01].
    rewrite !encR_pushRP.
    cbn [encR].
    rewrite pWord_1_2, pWord_1_1, pWord_1_0, add_one_0, !lpow_1.
    rewrite (pow_append_pow wRM K pM), (pow_append_pow wT d (6 * K)).
    replace (K + pM) with (pM + K) by fast_lia.
    replace (pC - 6 * K) with rC2 by fast_lia.
    reflexivity. }
  rewrite h0, hK_cfg in hloop.
  destruct (eMidExtraPost0_to_M (pM + K) pA (d + 6 * K) rC2 (ltac:(solve_inv)))
    as [m' [z' [c' [k' [hm' hrest]]]]].
  exists m', z', c', k'. split; [exact hm' | exact (ptrans hloop hrest)].
Qed.


Lemma eMidExtra12_to_M (pM pA z Bm d pC : nat)
  (hinv : InvEmidExtra12 pM pA z Bm d pC) : ReachesInvM (eMidExtra12Cfg pM pA z Bm d pC).
Proof.
  destruct hinv as [hd [hz [hA [hBm [hC [h6MC [h18M [h2CBm hpar]]]]]]]].
  pose (K := pC / 6).
  pose (rC2 := pC mod 6).
  assert (hK : 1 <= K) by fast_lia.
  pose (ms := [mi_mid pM; mi_t pA; mi_mid 1; mi_z (z - 1); mi_t Bm; mi_mid 1; mi_z 1; mi_t d]).
  pose (tw := td0 pC [rpair 1 0 0]).
  assert (hmax : 6 * K <= maxReflD01 tw) by (unfold tw; cbn [maxReflD01]; fast_lia).
  pose proof (era_E_loop_plus ms tw I K hK hmax) as hloop.
  assert (h0 : eraECfg ms tw 0 = eMidExtra12Cfg pM pA z Bm d pC).
  { unfold eraECfg, ms, tw, eMidExtra12Cfg.
    cbn [encMidR encMidItemR buildAdvTowerD01 Nat.mul].
    rewrite !Nat.sub_0_r, !encR_pushRP.
    cbn [encR].
    rewrite pWord_1_2, pWord_1_1, pWord_1_0, add_one_0, !lpow_0, !lpow_1, !Str_app_nil.
    reflexivity. }
  assert (hK_cfg : eraECfg ms tw K = eMidExtra12Cfg (pM + K) pA z Bm (d + 6 * K) rC2).
  { unfold eraECfg, ms, tw, eMidExtra12Cfg.
    cbn [encMidR encMidItemR buildAdvTowerD01].
    rewrite !encR_pushRP.
    cbn [encR].
    rewrite pWord_1_2, pWord_1_1, pWord_1_0, add_one_0, !lpow_1.
    rewrite (pow_append_pow wRM K pM), (pow_append_pow wT d (6 * K)).
    replace (K + pM) with (pM + K) by fast_lia.
    replace (pC - 6 * K) with rC2 by fast_lia.
    reflexivity. }
  rewrite h0, hK_cfg in hloop.
  destruct (eMidExtraPost12_to_M (pM + K) pA z Bm (d + 6 * K) rC2 (ltac:(solve_inv)))
    as [m' [z' [c' [k' [hm' hrest]]]]].
  exists m', z', c', k'. split; [exact hm' | exact (ptrans hloop hrest)].
Qed.


End Extra.

Section MidRowsLo0.
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

(* #### Stage 4: `InvEmid0` & `InvEmid12` → `ReachesInvM` (72 `rfl` lemmas) *)

Lemma rfl_em_z0_c0_b0 :
  computed_symbolic_certificate [6; 5; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c0_b1 :
  computed_symbolic_certificate [5; 4; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c1_b0 :
  computed_symbolic_certificate [5; 4; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c1_b1 :
  computed_symbolic_certificate [6; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c2_b0 :
  computed_symbolic_certificate [6; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c2_b1 :
  computed_symbolic_certificate [6; 5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c3_b0 :
  computed_symbolic_certificate [6; 5; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c3_b1 :
  computed_symbolic_certificate [6; 4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c4_b0 :
  computed_symbolic_certificate [7; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c4_b1 :
  computed_symbolic_certificate [6; 5; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c5_b0 :
  computed_symbolic_certificate [6; 5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c5_b1 :
  computed_symbolic_certificate [7; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c6_b0 :
  computed_symbolic_certificate [7; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c6_b1 :
  computed_symbolic_certificate [7; 4; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c7_b0 :
  computed_symbolic_certificate [7; 4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c7_b1 :
  computed_symbolic_certificate [7; 4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c8_b0 :
  computed_symbolic_certificate [7; 6; 5; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c8_b1 :
  computed_symbolic_certificate [7; 5; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c9_b0 :
  computed_symbolic_certificate [7; 5; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c9_b1 :
  computed_symbolic_certificate [7; 5; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c10_b0 :
  computed_symbolic_certificate [7; 6; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c10_b1 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c11_b0 :
  computed_symbolic_certificate [7; 6; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z0_c11_b1 :
  computed_symbolic_certificate [7; 6; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c0_b0 :
  computed_symbolic_certificate [6; 5; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c0_b1 :
  computed_symbolic_certificate [5; 4; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c1_b0 :
  computed_symbolic_certificate [5; 4; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c1_b1 :
  computed_symbolic_certificate [6; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c2_b0 :
  computed_symbolic_certificate [6; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c2_b1 :
  computed_symbolic_certificate [6; 5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c3_b0 :
  computed_symbolic_certificate [6; 5; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c3_b1 :
  computed_symbolic_certificate [6; 4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c4_b0 :
  computed_symbolic_certificate [7; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c4_b1 :
  computed_symbolic_certificate [6; 5; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c5_b0 :
  computed_symbolic_certificate [6; 5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c5_b1 :
  computed_symbolic_certificate [7; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c6_b0 :
  computed_symbolic_certificate [7; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c6_b1 :
  computed_symbolic_certificate [7; 4; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c7_b0 :
  computed_symbolic_certificate [7; 4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c7_b1 :
  computed_symbolic_certificate [7; 4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c8_b0 :
  computed_symbolic_certificate [7; 6; 5; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c8_b1 :
  computed_symbolic_certificate [7; 5; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c9_b0 :
  computed_symbolic_certificate [7; 5; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c9_b1 :
  computed_symbolic_certificate [7; 5; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c10_b0 :
  computed_symbolic_certificate [7; 6; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c10_b1 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c11_b0 :
  computed_symbolic_certificate [7; 6; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z1_c11_b1 :
  computed_symbolic_certificate [7; 6; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c0_b0 :
  computed_symbolic_certificate [6; 5; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c0_b1 :
  computed_symbolic_certificate [5; 4; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c1_b0 :
  computed_symbolic_certificate [5; 4; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c1_b1 :
  computed_symbolic_certificate [6; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c2_b0 :
  computed_symbolic_certificate [6; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c2_b1 :
  computed_symbolic_certificate [6; 5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c3_b0 :
  computed_symbolic_certificate [6; 5; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c3_b1 :
  computed_symbolic_certificate [6; 4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c4_b0 :
  computed_symbolic_certificate [7; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c4_b1 :
  computed_symbolic_certificate [6; 5; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c5_b0 :
  computed_symbolic_certificate [6; 5; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c5_b1 :
  computed_symbolic_certificate [7; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c6_b0 :
  computed_symbolic_certificate [7; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c6_b1 :
  computed_symbolic_certificate [7; 4; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c7_b0 :
  computed_symbolic_certificate [7; 4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c7_b1 :
  computed_symbolic_certificate [7; 4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c8_b0 :
  computed_symbolic_certificate [7; 6; 5; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c8_b1 :
  computed_symbolic_certificate [7; 5; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c9_b0 :
  computed_symbolic_certificate [7; 5; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c9_b1 :
  computed_symbolic_certificate [7; 5; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c10_b0 :
  computed_symbolic_certificate [7; 6; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c10_b1 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c11_b0 :
  computed_symbolic_certificate [7; 6; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_em_z2_c11_b1 :
  computed_symbolic_certificate [7; 6; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_mid (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N); sr_pair 1 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sr_mid (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 0%N); sr_pair 1 1 (symOne); sr_pair 1 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N); sr_pair 1 2 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


Lemma eMid0_lo_to_M (pM pA pB pC : nat)
  (hinv : InvEmid0 pM pA pB pC) (hlo : pC mod 12 < 6) : ReachesInvM (eMid0Cfg pM pA pB pC).
Proof.
  destruct hinv as [hA [hM [hB [hC [h12MC [h36M h2120]]]]]].
  destruct (pC mod 12) as [| [| [| [| [| [| _rem]]]]]] eqn:hrc.
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c0_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra0_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 6%N 0%N 0%N 78%N) (symConst 3%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 156%N) (u2 + u4 + 25) (u0 + 6 * u2 + (#79)) (4) (12 * u2 + 4 * u3 + (#157)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra0_to_M (u2 + u4 + 25) (u0 + 6 * u2 + (#79)) (4) (12 * u2 + 4 * u3 + (#157)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c0_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 2 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 78%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (u0 + 6 * u2 + (#80)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 2 (ltac:(fast_lia)) (u0 + 6 * u2 + (#80)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c1_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_1 (v5 u0 0 u2 u3 u4) 5 (mkSymN 1%N 0%N 6%N 0%N 0%N 81%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 165%N) (u0 + 6 * u2 + (#82)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#166)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 5 (ltac:(fast_lia)) (u0 + 6 * u2 + (#82)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#166)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c1_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 5 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 79%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (u0 + 6 * u2 + (#81)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 5 (ltac:(fast_lia)) (u0 + 6 * u2 + (#81)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c2_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 5 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 79%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (u0 + 6 * u2 + (#81)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 5 (ltac:(fast_lia)) (u0 + 6 * u2 + (#81)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c2_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra0_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 6%N 0%N 0%N 79%N) (symConst 2%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 161%N) (u2 + u4 + 25) (u0 + 6 * u2 + (#80)) (3) (12 * u2 + 4 * u3 + (#162)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra0_to_M (u2 + u4 + 25) (u0 + 6 * u2 + (#80)) (3) (12 * u2 + 4 * u3 + (#162)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c3_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 3 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 80%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (u0 + 6 * u2 + (#82)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 3 (ltac:(fast_lia)) (u0 + 6 * u2 + (#82)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c3_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_1 (v5 u0 0 u2 u3 u4) 3 (mkSymN 1%N 0%N 6%N 0%N 0%N 82%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (u0 + 6 * u2 + (#83)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 3 (ltac:(fast_lia)) (u0 + 6 * u2 + (#83)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c4_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra0_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 6%N 0%N 0%N 80%N) (symOne) (mkSymN 0%N 0%N 12%N 4%N 0%N 162%N) (u2 + u4 + 25) (u0 + 6 * u2 + (#81)) (2) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra0_to_M (u2 + u4 + 25) (u0 + 6 * u2 + (#81)) (2) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c4_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 3 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 80%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (u0 + 6 * u2 + (#82)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 3 (ltac:(fast_lia)) (u0 + 6 * u2 + (#82)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c5_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_1 (v5 u0 0 u2 u3 u4) 4 (mkSymN 1%N 0%N 6%N 0%N 0%N 83%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (u0 + 6 * u2 + (#84)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 4 (ltac:(fast_lia)) (u0 + 6 * u2 + (#84)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c5_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 4 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 81%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (u0 + 6 * u2 + (#83)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 4 (ltac:(fast_lia)) (u0 + 6 * u2 + (#83)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    fast_lia.
  }
Qed.


End MidRowsLo0.

Section Mid0LoHi.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

Lemma eMid0_hi_to_M (pM pA pB pC : nat)
  (hinv : InvEmid0 pM pA pB pC) (hhi : 6 <= pC mod 12) : ReachesInvM (eMid0Cfg pM pA pB pC).
Proof.
  destruct hinv as [hA [hM [hB [hC [h12MC [h36M h2120]]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c6_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 4 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 81%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (u0 + 6 * u2 + (#83)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 4 (ltac:(fast_lia)) (u0 + 6 * u2 + (#83)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c6_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra0_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 6%N 0%N 0%N 81%N) (symZero) (mkSymN 0%N 0%N 12%N 4%N 0%N 167%N) (u2 + u4 + 25) (u0 + 6 * u2 + (#82)) (1) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra0_to_M (u2 + u4 + 25) (u0 + 6 * u2 + (#82)) (1) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c7_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 0 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 82%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (u0 + 6 * u2 + (#84)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 0 (ltac:(fast_lia)) (u0 + 6 * u2 + (#84)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c7_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_1 (v5 u0 0 u2 u3 u4) 0 (mkSymN 1%N 0%N 6%N 0%N 0%N 84%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (u0 + 6 * u2 + (#85)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 0 (ltac:(fast_lia)) (u0 + 6 * u2 + (#85)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c8_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra0_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 25%N) (mkSymN 1%N 0%N 6%N 0%N 0%N 82%N) (symConst 5%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 162%N) (u2 + u4 + 26) (u0 + 6 * u2 + (#83)) (6) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra0_to_M (u2 + u4 + 26) (u0 + 6 * u2 + (#83)) (6) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c8_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 0 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 82%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (u0 + 6 * u2 + (#84)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 0 (ltac:(fast_lia)) (u0 + 6 * u2 + (#84)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c9_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_1 (v5 u0 0 u2 u3 u4) 1 (mkSymN 1%N 0%N 6%N 0%N 0%N 85%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (u0 + 6 * u2 + (#86)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 1 (ltac:(fast_lia)) (u0 + 6 * u2 + (#86)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c9_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 1 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 83%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (u0 + 6 * u2 + (#85)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 1 (ltac:(fast_lia)) (u0 + 6 * u2 + (#85)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c10_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 1 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 83%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (u0 + 6 * u2 + (#85)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 1 (ltac:(fast_lia)) (u0 + 6 * u2 + (#85)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c10_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra0_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 25%N) (mkSymN 1%N 0%N 6%N 0%N 0%N 83%N) (symConst 4%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 167%N) (u2 + u4 + 26) (u0 + 6 * u2 + (#84)) (5) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra0_to_M (u2 + u4 + 26) (u0 + 6 * u2 + (#84)) (5) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c11_b0) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_2 (v5 u0 0 u2 u3 u4) 2 (symZero) (mkSymN 1%N 0%N 6%N 0%N 0%N 84%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (u0 + 6 * u2 + (#86)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 2 (ltac:(fast_lia)) (u0 + 6 * u2 + (#86)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z0_c11_b1) (eval_eMid0 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convSimple_1 (v5 u0 0 u2 u3 u4) 2 (mkSymN 1%N 0%N 6%N 0%N 0%N 86%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (u0 + 6 * u2 + (#87)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convSimple_to_M 2 (ltac:(fast_lia)) (u0 + 6 * u2 + (#87)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    fast_lia.
  }
Qed.


Lemma eMid0_to_M (pM pA pB pC : nat)
  (hinv : InvEmid0 pM pA pB pC) : ReachesInvM (eMid0Cfg pM pA pB pC).
Proof.
  destruct (Nat.lt_ge_cases (pC mod 12) 6) as [h | h].
  - exact (eMid0_lo_to_M pM pA pB pC hinv h).
  - exact (eMid0_hi_to_M pM pA pB pC hinv h).
Qed.


End Mid0LoHi.

Section Mid1.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

Lemma eMid12_z1_lo_to_M (pM pA pB pC : nat)
  (hinv : InvEmid12 pM pA 1 pB pC) (hlo : pC mod 12 < 6) : ReachesInvM (eMid12Cfg pM pA 1 pB pC).
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c0_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 30%N) (symConst 3%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 156%N) (u2 + u4 + 25) (u0 + (#50)) (6 * u2 + 31) (4) (12 * u2 + 4 * u3 + (#157)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) 1 (6 * u2 + 31) (4) (12 * u2 + 4 * u3 + (#157)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c0_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 59%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 2 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 30%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 32) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + 32) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c1_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z1 (v5 u0 0 u2 u3 u4) 5 (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 165%N) (6 * u2 + 34) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#166)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + 34) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#166)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c1_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 60%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 5 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 31%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 33) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + 33) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c2_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 5 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 31%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 33) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 5 (ltac:(fast_lia)) (6 * u2 + 33) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c2_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 61%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 31%N) (symConst 2%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 161%N) (u2 + u4 + 25) (u0 + (#50)) (6 * u2 + 32) (3) (12 * u2 + 4 * u3 + (#162)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) 1 (6 * u2 + 32) (3) (12 * u2 + 4 * u3 + (#162)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c3_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 3 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 32%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 34) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + 34) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c3_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 62%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z1 (v5 u0 0 u2 u3 u4) 3 (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 35) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + 35) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c4_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 32%N) (symOne) (mkSymN 0%N 0%N 12%N 4%N 0%N 162%N) (u2 + u4 + 25) (u0 + (#50)) (6 * u2 + 33) (2) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) 1 (6 * u2 + 33) (2) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c4_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 63%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 3 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 32%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 34) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 3 (ltac:(fast_lia)) (6 * u2 + 34) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c5_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z1 (v5 u0 0 u2 u3 u4) 4 (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 169%N) (6 * u2 + 36) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + 36) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#170)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c5_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 64%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 4 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 35) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + 35) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    fast_lia.
  }
Qed.


Lemma eMid12_z1_hi_to_M (pM pA pB pC : nat)
  (hinv : InvEmid12 pM pA 1 pB pC) (hhi : 6 <= pC mod 12) : ReachesInvM (eMid12Cfg pM pA 1 pB pC).
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c6_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 4 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 23%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 35) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 4 (ltac:(fast_lia)) (6 * u2 + 35) (1) (u0 + (#50)) (u2 + u4 + 24) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c6_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 65%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 33%N) (symZero) (mkSymN 0%N 0%N 12%N 4%N 0%N 167%N) (u2 + u4 + 25) (u0 + (#50)) (6 * u2 + 34) (1) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 25) (u0 + (#50)) 1 (6 * u2 + 34) (1) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c7_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 0 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 36) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + 36) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c7_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 66%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z1 (v5 u0 0 u2 u3 u4) 0 (mkSymN 0%N 0%N 6%N 0%N 0%N 36%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 37) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + 37) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c8_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 25%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (symConst 5%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 162%N) (u2 + u4 + 26) (u0 + (#50)) (6 * u2 + 35) (6) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 26) (u0 + (#50)) 1 (6 * u2 + 35) (6) (12 * u2 + 4 * u3 + (#163)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c8_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 67%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 0 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 34%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 36) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 0 (ltac:(fast_lia)) (6 * u2 + 36) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c9_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z1 (v5 u0 0 u2 u3 u4) 1 (mkSymN 0%N 0%N 6%N 0%N 0%N 37%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 173%N) (6 * u2 + 38) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + 38) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#174)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c9_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 68%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 1 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 37) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + 37) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c10_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 1 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 37) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 1 (ltac:(fast_lia)) (6 * u2 + 37) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c10_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 69%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_eMidExtra12_z1_c1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 1%N 25%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 6%N 0%N 0%N 35%N) (symConst 4%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 167%N) (u2 + u4 + 26) (u0 + (#50)) (6 * u2 + 36) (5) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (eMidExtra12_to_M (u2 + u4 + 26) (u0 + (#50)) 1 (6 * u2 + 36) (5) (12 * u2 + 4 * u3 + (#168)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
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
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c11_b0) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 49%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_2_z1 (v5 u0 0 u2 u3 u4) 2 (symZero) (mkSymN 0%N 0%N 6%N 0%N 0%N 36%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 38) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + 38) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := (pC - (#60)) / 12) in * || pose (u2 := (pC - (#60)) / 12)).
      (set (u3 := (pB - (#50)) / 2) in * || pose (u3 := (pB - (#50)) / 2)).
      (set (u4 := pM - 19) in * || pose (u4 := pM - 19)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_em_z1_c11_b1) (eval_eMid12_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 0%N 0%N 1%N 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 0%N 2%N 0%N 50%N) (mkSymN 0%N 0%N 12%N 0%N 0%N 70%N) pM pA pB pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convEntry_1_z1 (v5 u0 0 u2 u3 u4) 2 (mkSymN 0%N 0%N 6%N 0%N 0%N 38%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 1%N 24%N) (mkSymN 0%N 0%N 12%N 4%N 0%N 177%N) (6 * u2 + 39) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      destruct (convEntry_to_M 2 (ltac:(fast_lia)) (6 * u2 + 39) (1) (u0 + (#50)) (u2 + u4 + 25) (12 * u2 + 4 * u3 + (#178)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
      exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
    }
  }
  {
    fast_lia.
  }
Qed.


End Mid1.
