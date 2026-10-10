(* Exact connection between the physical machine and the abstract clock laws. *)
From BusyCoq Require Import Individual62 Row9Machine Row9Operators.
Require Import Lia List.
Import ListNotations.

Definition lift_step {A : Type} (g : A -> option A) (x : option A) :=
  match x with None => None | Some u => g u end.

Lemma iter_halts_eventually {A : Type} (g : A -> option A) (u : A) :
  iter_halts g u <-> eventually (lift_step g) (Some u).
Proof.
  split.
  - intro E. induction E as [u E | u v E IH [k Hk]].
    + exists 1%nat. cbn [power lift_step]. exact E.
    + exists (S k). rewrite power_succ_r.
      cbn [lift_step]. rewrite E. exact Hk.
  - intros [k E]. revert u E. induction k as [|k IH]; intros u E.
    + discriminate.
    + rewrite power_succ_r in E. cbn [lift_step] in E.
      destruct (g u) as [v|] eqn:G.
      * eapply iter_halts_S; [exact G|]. apply IH,E.
      * apply iter_halts_O,G.
Qed.

Lemma phase3_is_T (u : word) :
  T 3%nat (Some u) = Row9Raw.phase3 u.
Proof.
  unfold T,Z,F,prefix,Row9Raw.phase3.
  cbn [power Row9Eval.bind].
  destruct (f u) as [v|]; [|reflexivity].
  cbn [Row9Eval.bind]. destruct (f v) as [w|]; reflexivity.
Qed.

Lemma lifted_phase3_is_T x :
  lift_step Row9Raw.phase3 x = T 3%nat x.
Proof.
  destruct x as [u|].
  - symmetry. apply phase3_is_T.
  - symmetry. apply T_none.
Qed.

Theorem blank_halts_iff_K :
  halts Row9Raw.tm c0 <-> K 3%nat (Some []).
Proof.
  rewrite Row9Raw.blank_halts_iff,iter_halts_eventually.
  rewrite <-K_T_equiv by lia.
  unfold eventually. split; intros [k E]; exists k.
  - rewrite <-(power_ext _ _ lifted_phase3_is_T). exact E.
  - rewrite (power_ext _ _ lifted_phase3_is_T). exact E.
Qed.
