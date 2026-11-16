From BusyCoq Require Import Individual62.

Require Import ZArith Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3 Longitudinal.

Fixpoint multistep_c' tm n1 n2 n3 c :=
match n1 with
| O => multistep_c tm n3 c
| S n1 =>
  match multistep_c tm n2 c with
  | Some c => multistep_c' tm n1 n2 n3 c
  | None => None
  end
end.

Lemma multistep_c'_spec tm n1 n2 n3 c c':
  multistep_c' tm n1 n2 n3 c = Some c' <-> c -[ tm ]->> (n1*n2+n3) / c'.
Proof.
  gen c c'.
  induction n1; cbn[multistep_c']; intros.
  1: apply multistep_c_spec.
  destruct (multistep_c tm n2 c) eqn:E.
  + apply multistep_c_spec in E.
    rewrite IHn1.
    replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
    split; intro H.
    * eapply multistep_trans; eauto 1.
    * eapply rewind_split in H.
      destruct H as [c'0 [I1 I2]].
      multistep_deterministic.
      eauto 1.
  + split.
    1: congruence.
    replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
    intro H.
    eapply rewind_split in H.
    destruct H as [c'0 [I1 I2]].
    eapply multistep_c_spec in I1.
    congruence.
Qed.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RA_0RA0RC_---1RD_1RE1RB_1LF0LE_0RD0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation v0 := [0].
Notation v1 := [1].
Notation hR := (D,<[0]).
Notation hL := (F,@nil Sym).
Notation hRL := [(hR,hL)].

Definition RC i :=
  ((v1 ++ v0)^^4 ++ (v0 ++ v1)^^3 ++ (v0^^2 ++ (v1 ++ v0)^^3 ++ v0 ++ v1)^^(363+i*128) ++ (v0 ++ v1)^^2 ++ (v0^^2 ++ v1)^^2 ++ (v0 ++ v1)^^2 ++ (v0^^2 ++ (v1 ++ v0)^^3 ++ v0 ++ v1)^^2 ++ (v0 ++ v1)^^2 ++ (v0^^2 ++ v1)^^2 ++ (v0 ++ v1)^^4 ++ v0^^2 ++ v1 ++ v0^^4 ++ (v1 ++ v0)^^4 ++ v0 ++ v1 ++ v0^^2 ++ (v1 ++ v0)^^3 ++ (v0 ++ v1)^^3 ++ ((v0^^2 ++ v1)^^2 ++ (v0 ++ v1)^^2)^^2 ++ (v0 ++ v1)^^4 ++ v0^^2 ++ v1 ++ v0^^4 ++ (v1 ++ v0)^^2 ++ (v0 ++ v1)^^3 ++ ((v0^^2 ++ v1)^^2 ++ (v0 ++ v1)^^2)^^2 ++ (v0 ++ v1)^^2 ++ v0^^2 ++ v1 ++ v0^^4 ++ (v1 ++ v0)^^2 ++ (v0 ++ v1)^^3 ++ ((v0^^2 ++ v1)^^2 ++ (v0 ++ v1)^^2 ++ v0^^2 ++ (v1 ++ v0)^^8 ++ v0 ++ v1 ++ v0^^2 ++ (v1 ++ v0)^^3 ++ (v0 ++ v1)^^48)^^(1+i*3) ++ (v0 ++ v1)^^2 ++ (v0^^2 ++ v1)^^2 ++ (v0 ++ v1)^^4 ++ v0^^2 ++ v1 ++ v0^^4 ++ (v1 ++ v0)^^12 ++ (v0 ++ v1 ++ v0^^2 ++ (v1 ++ v0)^^3)^^2 ++ (v1 ++ v0)^^2 ++ v0 ++ v1 ++ v0^^2 ++ (v1 ++ v0)^^2 ++ v0 ++ v1) *> 0inf.

Lemma RInc i:
  sideRLs tm (hRL^^128) (RC i) (RC (1+i)).
Proof.
  unfold RC.
  repeat rewrite lpow_add.
  repeat rewrite lpow_mul.
  repeat rewrite Str_app_assoc.
  pose (fun s : string => if (s =? "a")%string then i else O) as nmp.
  rw_mp.
  erewrite rw_sideRLs; [| rw_side | rw_side].
  apply vsideRLs_es_spec with (T:=N.to_nat (10^6)) (v:="$l"%string).
  native_check_eq.
  Unshelve.
  apply (fun _=>0inf).
Time Qed.

Definition S' i := 0inf {{{ (hR,R) }}} RC i.

Lemma LIncs k:
  sideRLs (flip tm) ([(hL,hR)]^^k) 0inf 0inf.
Proof.
  eapply sideRLs_wall.
  esx; st; er.
Qed.

Lemma BigStep i:
  S' i -->+
  S' (1+i).
Proof.
  unfold S'.
  eapply @sideRLs_concat_v2 with (ls:=[(hL,hR)]^^128).
  4: apply (RInc i).
  3: apply LIncs.
  1: reflexivity.
  1: cbn; congruence.
Qed.

Lemma init:
  c0 -->* S' 23.
Proof.
  eapply without_counter with (n:=29647*(10^5)+16529).
  eapply multistep_c'_spec.
  native_check_eq.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  eexists; apply BigStep.
Time Qed.

End TM1.


