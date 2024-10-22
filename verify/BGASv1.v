From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.
Require Import List.

Open Scope list.

Module Inductive62 := Inductive BB62.
Import Inductive62.


Lemma progress_rw tm c1 c2:
  progress tm c1 c2 <->
  Compute.TM.progress tm c1 c2.
Proof.
  split; intro H.
  - induction H.
    + constructor.
      destruct H; auto.
    + eapply Compute.TM.progress_step; eauto.
      destruct H; auto.
  - induction H.
    + constructor.
      destruct H; auto.
    + eapply progress_step; eauto.
      destruct H; auto.
Qed.

Lemma seg_arithseq_to_seg_eq ls1 n1 ls2 n2:
  n1 = n2 ->
  ls1 = ls2 ->
  seg_arithseq_to_seg ls1 n1 0 =
  seg_arithseq_to_seg ls2 n2 0.
Proof.
  congruence.
Qed.

Lemma and_True_1 X:
  True /\ X <-> X.
Proof.
  tauto.
Qed.

Lemma and_True_2 X:
  X /\ True <-> X.
Proof.
  tauto.
Qed.

Ltac simpl_to_prop_goal :=
  unfold to_prop',to_prop'',to_prop,to_prop0_list;
  repeat rewrite Forall_cons_iff;
  repeat rewrite Forall_nil_iff;
  cbn[to_prop0];
  unfold to_config,config_WF;
  cbn[to_cconfig];
  cbn[cto_config];
  cbn[cconfig_WF];
  unfold to_side,side_WF;
  cbn[to_cside];
  cbn[cto_side];
  cbn[cside_WF];
  unfold to_seg,seg_WF;
  cbn[to_cseg];
  cbn[cto_seg];
  cbn[cseg_WF];
  unfold to_nat;
  cbv[to_cnat];
  cbv[cto_nat];
  cbn[app];
  repeat (rewrite and_True_1 || rewrite and_True_2);
  unfold multistep'.

Ltac simpl_to_prop H :=
  unfold to_prop',to_prop'',to_prop,to_prop0_list in H;
  repeat rewrite Forall_cons_iff in H;
  repeat rewrite Forall_nil_iff in H;
  cbn[to_prop0] in H;
  unfold to_config,config_WF in H;
  cbn[to_cconfig] in H;
  cbn[cto_config] in H;
  cbn[cconfig_WF] in H;
  unfold to_side,side_WF in H;
  cbn[to_cside] in H;
  cbn[cto_side] in H;
  cbn[cside_WF] in H;
  unfold to_seg,seg_WF in H;
  cbn[to_cseg] in H;
  cbn[cto_seg] in H;
  cbn[cseg_WF] in H;
  unfold to_nat in H;
  cbv[to_cnat] in H;
  cbv[cto_nat] in H;
  cbn[app] in H;
  repeat (rewrite and_True_1 in H || rewrite and_True_2 in H);
  unfold multistep' in H.


Definition mp_default(i:id_t)(t:type_t): to_cexpr_type t :=
match t return to_cexpr_type t with
| nat_t => N0
| seg_t => cseg_nil
| side_t => cside_0inf
end.

Ltac get_rule_from_inductive_decider cfg cfg_WF T tm :=
epose proof (get_rule_spec cfg T tm (cfg_WF tm)) as H;
eassert (get_rule tm cfg T = _) as H0 by (time vm_compute; reflexivity);
rewrite H0 in H;
match goal with
| H0: get_rule _ _ _ = Some (_,_,?A,?B) |- _ =>
  pose (fun mp => to_prop0_list tm mp N0 A) as P;
  pose (fun mp => to_config mp N0 B) as S0
end;
clear H0;
cbn[fst] in H;
unfold to_prop',to_prop'',to_prop,to_prop0_list in H;
destruct H as [H0 H];
eassert (H': forall (mp:id_t->forall t:type_t, to_cexpr_type t),_) by (
  intros mp;
  specialize (H N0 mp);
  simpl_to_prop H;
  exact H
);
clear H;
eassert (H0':_) by (
  pose proof (H0 N0 mp_default) as H;
  simpl_to_prop H;
  exact (H I)
);
clear H0.

Lemma feq{A B}(f1 f2:A->B)(x1 x2:A):
  f1 = f2 ->
  x1 = x2 ->
  f1 x1 = f2 x2.
Proof.
  congruence.
Qed.

Ltac feq1 :=
  apply feq; [reflexivity|].

Ltac feq2 :=
  apply feq; [feq1 |].

Ltac tape_equal :=
match goal with
| |- seg_arithseq_to_seg _ _ _ = seg_arithseq_to_seg _ _ _ => apply seg_arithseq_to_seg_eq; cbn[map]
| |- Str_app _ _ = Str_app _ _ => feq2
| |- Streams.hd _ = Streams.hd _ => feq1
| |- Streams.tl _ = Streams.tl _ => feq1
| |- app _ _ = app _ _ => feq2
| |- lpow _ _ = lpow _ _ => feq2
| |- N.to_nat _ = N.to_nat _ => feq1
| |- (_,_) = (_,_) => feq2
| |- @eq (list Sym) _ _ => reflexivity
| |- @eq cnat_expr _ _ => try reflexivity
| |- @eq N _ _ => try reflexivity
| |- @eq Z _ _ => try reflexivity
| |- @eq Q _ _ => reflexivity
| |- [] = [] => reflexivity
| |- const s0 = const s0 => reflexivity
| |- _::_ = _::_ => feq2
end.

Ltac solve_init H0' S0 mp0 :=
apply multistep_nonhalt with (c':=S0 mp0);
[
  apply progress_evstep;
  rewrite progress_rw;
  rewrite progress_rw in H0';
  follow10 (H0' I);
  apply evstep_refl';
  unfold S0;
  simpl_to_prop_goal
|].

Ltac solve_closure H' S0 P P' mp1 :=
eapply progress_nonhalt_cond with (P:=fun mp => P mp /\ P' mp) (C:=S0);
[
  intros mp HP;
  unfold S0,P,P';
  unfold P,P' in HP;
  destruct HP as [HP HP'];
  simpl_to_prop HP;
  simpl_to_prop_goal;
  exists (mp1 mp);
  unfold mp1;
  split;
  [
    specialize (H' mp HP);
    rewrite progress_rw;
    rewrite progress_rw in H';
    follow10 (H' I);
    apply evstep_refl'
  |
    simpl_to_prop_goal
  ]
|
  unfold P,P';
  simpl_to_prop_goal
].

Open Scope N.

Ltac solve_OE_lia :=
match goal with
| |- N.Odd ?x => exists (x/2); lia
| |- N.Even ?x => exists (x/2); lia
| _ => lia
end.

Opaque N.to_nat.





Module TM61.
Definition tm := Eval compute in (TM_from_str "1RB1RD_0LC1LE_1LD1LB_1RA1LF_---0RC_0LD0RE").

Definition m_config := default_config.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 5988 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t = 0 /\
mp 1%positive nat_t = mp 3%positive nat_t + 1
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 18 in
  let n3 := 17 in
  let m1 := n3*2+12 in
  let m5 := n3*2+10 in
  let m2 := 0 in
  let m4 := n1+9 in
  let m6 := (m4+m5)/3-1 in
  let m3 := m6*2+1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n3 := mp 3%positive nat_t in
  let m1 := n3*2+12 in
  let m5 := n3*2+10 in
  let m2 := 0 in
  let m4 := n1+9 in
  let m6 := (m4+m5)/3-1 in
  let m3 := m6*2+1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.
solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM61.


Module TM60.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC1LF_1RD0LB_0RE1LB_1LE0RD_0LA1LB").

Definition m_config := default_config.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 30347 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t = 0 /\
N.Even (mp 3%positive nat_t) /\
18 <= mp 3%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 4 in
  let n3 := ((524238-38)/4+9)*2 in
  let m2 := 0 in
  let m4 := n1 in
  let m5 := n3/2-9 in
  let m6 := n1 * 8 + 60 in
  let m7 := m6/2 + m5 * 4 + 23 in
  let m1 := m4 + 1 in
  let m3 := m7 + 1 - m1 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n3 := mp 3%positive nat_t in
  let m2 := 0 in
  let m4 := n1 in
  let m5 := n3/2-9 in
  let m6 := n1 * 8 + 60 in
  let m7 := m6/2 + m5 * 4 + 23 in
  let m1 := m4 + 1 in
  let m3 := m7 + 1 - m1 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- destruct HP' as [HP1 [HP2 HP3]].
  destruct HP2 as [n3' Hn3'].
  repeat tape_equal;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM60.


Module TM59.
Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1LD_1LC0RB_0LA1LE_0LF1LD_1LD---").

Definition m_config := default_config.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 26493 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t = 1
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let m2 := 1 in
  let m1 := 3 in
  let m3 := (1048564 - 58 - m2 * 2 - m1 * 4)/4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n3 := mp 3%positive nat_t in
  let m2 := 1 in
  let m1 := n1 + 1 in
  let m3 := n1 * 2 + n3 * 2 + 18 - m1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM59.



Module TM58.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC0RE_1LA0RD_---0LC_1RF1LE_1LD0RB").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 8573 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 2097169 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 2 in
  let m1 := m4 * 2 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 2 in
  let m1 := m4 * 2 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM58.


Module TM57.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0LD_1RD0RA_1LB1RE_0RF---_0RB1RD").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 23332 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 15216514222579967910811 in
  let n2 := 2 in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM57.


Module TM56.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1RC0LD_1RD0RA_1LB1RE_0RF---_0RB1RD").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 23332 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 15216514222579967910811 in
  let n2 := 2 in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM56.

Module TM55.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC0RF_1LA1RD_0RE---_0RA1RC_1RA0LD").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 23228 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 5771781256840677483419 in
  let n2 := 2 in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM55.

Module TM54.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC0RF_1LA1RD_0RE---_0RA1RC_1RA0RA").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 23228 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 5771781256840677483419 in
  let n2 := 2 in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM54.


Module TM53.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1RA0LB_1RC0LE_0RF---_0RC1RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 23297 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 10494147739710322697115 in
  let n2 := 2 in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM53.



Module TM52.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1RA0LB_1RC0RC_0RF---_0RC1RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 23297 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 10494147739710322697115 in
  let n2 := 2 in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 4 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2 + 1 in
  let m6 := n1 - 5 in
  let m8 := m6 * 4 - m2 * 3 - 14 in
  let m7 := m8 * 4 - m2 * 3 - 15 in
  let m1 := m7 * 4 - m2 * 3 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM52.


Module TM51.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC0RA_0LE1LD_1RA0RE_1RD0RF_1LB---").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 8013 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 31381059629 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m5 := n1 - 5 in
  let m3 := 3 in
  let m4 := 1 in
  let m6 := m5 * 3 - m2 * 4 - 7 in
  let m1 := m6 * 3 - m2 * 4 - 12 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m5 := n1 - 5 in
  let m3 := 3 in
  let m4 := 1 in
  let m6 := m5 * 3 - m2 * 4 - 7 in
  let m1 := m6 * 3 - m2 * 4 - 12 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM51.


Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC0RA_0LE1LD_1RA1LD_0RD0RF_1LB---").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 9164 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 3486784419 in
  let n2 := 5 in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m4 := m3 * 3 - m2 * 4 in
  let m1 := m4 * 3 - m2 * 4 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m4 := m3 * 3 - m2 * 4 in
  let m1 := m4 * 3 - m2 * 4 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM50.

Module TM49.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RE_0LD0RB_0LE1LA_0RA0RF_1LC---").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 5074 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 3188658 in
  let n2 := 2 in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m4 := m3 * 3 - m2 * 4 in
  let m1 := m4 * 3 - m2 * 4 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m4 := m3 * 3 - m2 * 4 in
  let m1 := m4 * 3 - m2 * 4 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM49.


Module TM48.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LE_1LD0RB_0LC1LB_1RA0RF_0RE0RC").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18908 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 10750780360492 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m5 := n1 - 7 in
  let m3 := 5 in
  let m4 := 3 in
  let m6 := m5 * 4 - m2 * 4 - 5 in
  let m1 := m6 * 4 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m5 := n1 - 7 in
  let m3 := 5 in
  let m4 := 3 in
  let m6 := m5 * 4 - m2 * 4 - 5 in
  let m1 := m6 * 4 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM48.

Module TM47.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC0RA_0LB1LA_1RE0RF_1RA---_0RD0RB").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18678 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 1954687338284 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m3 := n1 - 7 in
  let m4 := 5 in
  let m5 := 3 in
  let m6 := m3 * 4 - m2 * 4 - 5 in
  let m1 := m6 * 4 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 7 in
  let m4 := 5 in
  let m5 := 3 in
  let m6 := m3 * 4 - m2 * 4 - 5 in
  let m1 := m6 * 4 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM47.


Module TM46.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_1LD1RB_1LA0RE_1LE1RD_1RC---").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 30276 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 83886132 in
  let n2 := 7 in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 4 - 14 in
  let m1 := m4 * 2 - m2 * 4 - 12 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 4 - 14 in
  let m1 := m4 * 2 - m2 * 4 - 12 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM46.

Module TM45.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC1LE_0LE0RD_1RB0RB_0RF1RA_---0LA").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 21526 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 1073741856 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 14 in
  let m1 := m4 * 2 - m2 * 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 14 in
  let m1 := m4 * 2 - m2 * 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM45.

Module TM44.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC1LE_1LA0RD_1RB0RB_0RF1RA_---0LA").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 17872 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 134217757 in
  let n2 := 3 in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m5 := m3 * 2 - m2 * 3 - 11 in
  let m4 := m5 * 2 - m2 * 3 - 13 in
  let m1 := m4 * 2 - m2 * 3 - 6 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m5 := m3 * 2 - m2 * 3 - 11 in
  let m4 := m5 * 2 - m2 * 3 - 13 in
  let m1 := m4 * 2 - m2 * 3 - 6 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM44.

Module TM43.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC1LE_1LB0RD_1RB0RB_0RF1RA_---0LA").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 24142 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 8589934627 in
  let n2 := 5 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 13 in
  let m1 := m4 * 2 - m2 * 3 - 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 13 in
  let m1 := m4 * 2 - m2 * 3 - 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM43.

Module TM42.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC1LE_1LB0RD_1RB0RB_0RF1RA_---0LC").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 24142 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 8589934627 in
  let n2 := 5 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 13 in
  let m1 := m4 * 2 - m2 * 3 - 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 13 in
  let m1 := m4 * 2 - m2 * 3 - 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM42.

Module TM41.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA1LD_1RB0RB_0RF1RE_1LF0RD_---0LA").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 19652 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 1073741856 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 11 in
  let m1 := m4 * 2 - m2 * 3 - 6 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m5 := m3 * 2 - m2 * 3 - 10 in
  let m4 := m5 * 2 - m2 * 3 - 11 in
  let m1 := m4 * 2 - m2 * 3 - 6 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM41.



Module TM40.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_1LE0RD_1LD1RC_1RF0LC_1RB0RA").

Definition m_config := config_arithseq_fixed_block_size 0 2 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 20416 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 3145770 in
  let n2 := 5 in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 10 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 10 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM40.

Module TM39.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LA_0LE0RD_1RB0LF_0RB1RA_0RE---").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 25848 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 34359738405 in
  let n2 := 1 in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 24 in
  let m1 := m7 * 2 - m2 * 3 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 24 in
  let m1 := m7 * 2 - m2 * 3 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM39.

Module TM38.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LD_1RB0RB_1LB1RE_0RF---_0RB1RD").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 22394 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 34359738405 in
  let n2 := 1 in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 25 in
  let m1 := m7 * 2 - m2 * 3 - 20 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 25 in
  let m1 := m7 * 2 - m2 * 3 - 20 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM38.

Module TM37.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LD_1RB0LE_1LB1RE_0RF---_0RB1RD").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 25848 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 34359738405 in
  let n2 := 1 in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 24 in
  let m1 := m7 * 2 - m2 * 3 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 24 in
  let m1 := m7 * 2 - m2 * 3 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM37.

Module TM36.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LA_0LE0RD_1RB0RB_0RB1RA_0RE---").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 22394 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 34359738405 in
  let n2 := 1 in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 25 in
  let m1 := m7 * 2 - m2 * 3 - 20 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m4 := 4 in
  let m5 := 3 in
  let m6 := 1 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m8 := m3 * 2 - m2 * 3 - 24 in
  let m7 := m8 * 2 - m2 * 3 - 25 in
  let m1 := m7 * 2 - m2 * 3 - 20 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM36.



Module TM35.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0LC0LD_0LD1LE_0RE0LF_1RA---_0RA0RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 20680 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 536870965 in
  let n2 := 7 in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2 - 4 in
  let m5 := m4 * 2 - m2 * 2 - 3 in
  let m1 := m5 * 4 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2 - 4 in
  let m5 := m4 * 2 - m2 * 2 - 3 in
  let m1 := m5 * 4 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
  solve_OE_lia.
- repeat split; cbn;
  try lia.
  solve_OE_lia.
Time Qed.
End TM35.



Module TM34.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0RF_1RD1RB_1LD1RE_1LA0RD_1RC---").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 38330 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 524326 in
  let n2 := 0 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m4 := m3 * 2 - m2 * 4 - 26 in
  let m1 := m4 * 2 - m2 * 4 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m4 := m3 * 2 - m2 * 4 - 26 in
  let m1 := m4 * 2 - m2 * 4 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM34.

Module TM33.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RE_0LF0LD_0RA0LE_0RB0RC_0LD1LA").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 20353 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 268435509 in
  let n2 := 7 in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2 - 4 in
  let m5 := m4 * 2 - m2 * 2 - 3 in
  let m1 := m5 * 4 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2 - 4 in
  let m5 := m4 * 2 - m2 * 2 - 3 in
  let m1 := m5 * 4 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
  solve_OE_lia.
- repeat split; cbn;
  try lia.
  solve_OE_lia.
Time Qed.
End TM33.

Module TM32.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1RC0LD_1LA0RA_1LB1RE_0RF---_0RB1RD").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 24222 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Even (mp 1%positive nat_t) /\
N.Odd (mp 2%positive nat_t) /\
mp 2%positive nat_t * 100 + 10000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 5726623098 in
  let n2 := 3 in
  let m2 := n2 + 2 in
  let m3 := n1/2 - 4 in
  let m8 := m3 * 2 - m2/2*3 - 8 in
  let m7 := m8 * 2 - m2/2*3 - 8 in
  let m6 := m7 * 2 - m2/2*3 - 8 in
  let m5 := m6 * 2 - m2/2*3 - 11 in
  let m4 := m5 * 2 - m2/2*3 - 10 in
  let m1 := m4 * 4 - m2 * 3 - 9 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 2 in
  let m3 := n1/2 - 4 in
  let m8 := m3 * 2 - m2/2*3 - 8 in
  let m7 := m8 * 2 - m2/2*3 - 8 in
  let m6 := m7 * 2 - m2/2*3 - 8 in
  let m5 := m6 * 2 - m2/2*3 - 11 in
  let m4 := m5 * 2 - m2/2*3 - 10 in
  let m1 := m4 * 4 - m2 * 3 - 9 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- destruct HP' as [[v1 Hv1] [[v2 Hv2] HP']].
  remember (mp 1%positive nat_t) as c1. clear Heqc1. subst c1.
  remember (mp 2%positive nat_t) as c2. clear Heqc2. subst c2.
  repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM32.

Module TM31.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LA_1RE0RD_1RE---_1RF1RC_1LF1RA").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 38325 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 131110 in
  let n2 := 0 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m4 := m3 * 2 - m2 * 4 - 26 in
  let m1 := m4 * 2 - m2 * 4 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m4 := m3 * 2 - m2 * 4 - 26 in
  let m1 := m4 * 2 - m2 * 4 - 22 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM31.

Module TM30.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0LC0LD_0LD1LE_0RE1LB_1RA---_0RA0RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 17318 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 8388649 in
  let n2 := 6 in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2-5 in
  let m5 := m4 * 2 - m2 * 2 in
  let m1 := m5 * 4 + 9 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2-5 in
  let m5 := m4 * 2 - m2 * 2 in
  let m1 := m5 * 4 + 9 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM30.


Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RE_0LF0LD_0RA1LC_0RB0RC_0LD1LA").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 17027 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 4194345 in
  let n2 := 6 in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2 - 5 in
  let m5 := m4 * 2 - m2 * 2 in
  let m1 := m5 * 4 + 9 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m3 := 3 in
  let m2 := n2 + 1 in
  let m4 := n1/2 - 5 in
  let m5 := m4 * 2 - m2 * 2 in
  let m1 := m5 * 4 + 9 - m2 * 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM29.



Module TM28.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0LC1RA_0LD1LE_0RE0LF_1RA---_0RA0RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 9923 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 2097189 in
  let n2 := 11 in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM28.

Module TM27.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0LC1RA_0LD0LE_0RE0LF_1RA---_0RA0RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 9923 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 2097189 in
  let n2 := 11 in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM27.

Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF1LA_0RA0LD").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 10848 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 4194345 in
  let n2 := 13 in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM26.

Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF0LA_0RA0LD").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 10848 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 4194345 in
  let n2 := 13 in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1/2-3 in
  let m4 := 3 in
  let m1 := m3 * 4 + 3 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM25.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC0RF_1RD1RA_0LE0RB_1LB0LE_1LD1LA").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 35127 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 1073741856 in
  let n2 := 2 in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m6 := m3 * 2 - m2 * 4 - 15 in
  let m5 := m6 * 2 - m2 * 4 - 12 in
  let m4 := m5 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 8 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 6 in
  let m6 := m3 * 2 - m2 * 4 - 15 in
  let m5 := m6 * 2 - m2 * 4 - 12 in
  let m4 := m5 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 8 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM24.

Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC0RF_1RA1LB_1RE1LD_1LF0RA_---0LB").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 11188 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 16777237 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 6 in
  let m1 := m4 * 2 - m2 * 2 - 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 6 in
  let m1 := m4 * 2 - m2 * 2 - 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM23.

Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC0RE_1LA0RD_---0LC_1RF1LE_0LD0RB").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 11248 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 16777239 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 8 in
  let m1 := m4 * 2 - m2 * 2 - 5 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 8 in
  let m1 := m4 * 2 - m2 * 2 - 5 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM22.

Module TM21.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC1LA_1RA0RD_1RE1LD_1LF0RC_---0LA").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 11376 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 8388629 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 6 in
  let m1 := m4 * 2 - m2 * 2 - 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 4 in
  let m4 := m3 * 2 - m2 * 2 - 6 in
  let m1 := m4 * 2 - m2 * 2 - 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM21.

Module TM20.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0LC1RA_0LD0LE_0RE1LB_1RA---_0RA0RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18373 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 1048611 in
  let n2 := 9 in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM20.

Module TM19.
Definition tm := Eval compute in (TM_from_str "1LB0RF_0LC1RA_0LD1LE_0RE1LB_1RA---_0RA0RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18373 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 1048611 in
  let n2 := 9 in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM19.

Module TM18.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RB_0RD0RA_0LE1LB_0LA1LC_1LD---").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 20956 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Even (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 4294967360 in
  let n2 := 3 in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m8 := m3 * 2 - m2 * 4 - 12 in
  let m7 := m8 * 2 - m2 * 4 - 14 in
  let m6 := m7 * 2 - m2 * 4 - 13 in
  let m1 := m6 * 4 - m2 * 8 - 20 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m4 := 3 in
  let m5 := 1 in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m8 := m3 * 2 - m2 * 4 - 12 in
  let m7 := m8 * 2 - m2 * 4 - 14 in
  let m6 := m7 * 2 - m2 * 4 - 13 in
  let m1 := m6 * 4 - m2 * 8 - 20 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | 7%positive => m7
  | 8%positive => m8
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM18.

Module TM17.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF1LA_0RA1LC").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18243 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 524323 in
  let n2 := 9 in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM17.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF0LA_0RA1LC").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18243 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 524323 in
  let n2 := 9 in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1/2-3 in
  let m1 := m3 * 4 + 1 - m2 * 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM16.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1RE_---0RD_1LA1RF_1LA0RB_1RD1LC").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 32220 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 4194349 in
  let n2 := 6 in
  let m2 := n2+1 in
  let m3 := n1-3 in
  let m4 := m3 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1-3 in
  let m4 := m3 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM15.

Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC0LA_1RD1RA_---0RE_1LB1RF_1RE1LD").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 23318 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 65573 in
  let n2 := 4 in
  let m2 := n2+1 in
  let m3 := n1-3 in
  let m4 := m3 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1-3 in
  let m4 := m3 * 2 - m2 * 4 - 12 in
  let m1 := m4 * 2 - m2 * 4 - 11 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM14.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RF_1RD1RA_0LE0RB_1LB0LE_1LE1RF").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 19475 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 33554459 in
  let n2 := 3 in
  let m2 := n2+1 in
  let m3 := n1-6 in
  let m4 := m3 * 2 - m2 * 2 - 12 in
  let m1 := m4 * 2 - m2 * 2 - 7 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1-6 in
  let m4 := m3 * 2 - m2 * 2 - 12 in
  let m1 := m4 * 2 - m2 * 2 - 7 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM13.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC0RF_0LD1LE_0RE0RA_1RF1LE_1RB0RD").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 4964 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 1594335 in
  let n2 := 2 in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m4 := m3 * 3 - m2 * 4 in
  let m1 := m4 * 3 - m2 * 4 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m3 := n1 - 5 in
  let m4 := m3 * 3 - m2 * 4 in
  let m1 := m4 * 3 - m2 * 4 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM12.

Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LA_1RA0RD_1RB0RB_0RF---_0RB1RA").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18236 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 64051194700380398 in
  let n2 := 3 in
  let m2 := n2+1 in
  let m3 := n1-5 in
  let m5 := m3 * 4 - m2 * 3 - 3 in
  let m4 := m5 * 4 - m2 * 3 - 9 in
  let m1 := m4 * 4 - m2 * 3 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1-5 in
  let m5 := m3 * 4 - m2 * 3 - 3 in
  let m4 := m5 * 4 - m2 * 3 - 9 in
  let m1 := m4 * 4 - m2 * 3 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM11.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LA_1RA0RD_1RB0LE_0RF---_0RB1RA").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 18236 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 64051194700380398 in
  let n2 := 3 in
  let m2 := n2+1 in
  let m3 := n1-5 in
  let m5 := m3 * 4 - m2 * 3 - 3 in
  let m4 := m5 * 4 - m2 * 3 - 9 in
  let m1 := m4 * 4 - m2 * 3 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+1 in
  let m3 := n1-5 in
  let m5 := m3 * 4 - m2 * 3 - 3 in
  let m4 := m5 * 4 - m2 * 3 - 9 in
  let m1 := m4 * 4 - m2 * 3 - 1 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM10.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RA_1RD0RA_0LE0RC_0LA1LB_1LD---").

Definition m_config := config_arithseq_fixed_block_size 0 2 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 7728 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 6973568821 in
  let n2 := 4 in
  let m2 := n2 + 1 in
  let m5 := n1 - 3 in
  let m6 := m5 * 3 - m2 * 4 - 13 in
  let m1 := m6 * 3 - m2 * 4 - 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => 3
  | 4%positive => 1
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 1 in
  let m5 := n1 - 3 in
  let m6 := m5 * 3 - m2 * 4 - 13 in
  let m1 := m6 * 3 - m2 * 4 - 4 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => 3
  | 4%positive => 1
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal; cbn;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM9.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC0RD_0LD1RA_1RE0LF_0RB---_1LB1LC").


Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 8944 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Even (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 125269906 in
  let n2 := 6 in
  let m2 := n2+2 in
  let m3 := n1/2-3 in
  let m6 := m3 * 2 - m2 - 2 in
  let m5 := m6 * 2 - m2 - 2 in
  let m4 := m5 * 2 - m2 - 2 in
  let m1 := m4 * 4 - m2 * 2 - 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+2 in
  let m3 := n1/2-3 in
  let m6 := m3 * 2 - m2 - 2 in
  let m5 := m6 * 2 - m2 - 2 in
  let m4 := m5 * 2 - m2 - 2 in
  let m1 := m4 * 4 - m2 * 2 - 2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM8.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB0RC_0LC1RF_1RD0LE_0RA---_1LA1LB_1RA0RB").


Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 5392 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 139829 in
  let n2 := 1 in
  let m2 := n2+2 in
  let m3 := n1/2-2 in
  let m6 := m3 * 2 - m2 - 4 in
  let m5 := m6 * 2 - m2 - 3 in
  let m4 := m5 * 2 - m2 - 4 in
  let m1 := m4 * 4 - m2 * 2 - 5 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2+2 in
  let m3 := n1/2-2 in
  let m6 := m3 * 2 - m2 - 4 in
  let m5 := m6 * 2 - m2 - 3 in
  let m4 := m5 * 2 - m2 - 4 in
  let m1 := m4 * 4 - m2 * 2 - 5 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM7.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD0RA_0LA1RF_1LC1LD_1RC0RD").


Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 5342 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Even (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 55178 in
  let n2 := 2 in
  let m2 := n2 + 2 in
  let m3 := n1/2 - 3 in
  let m6 := m3*2-m2-2 in
  let m5 := m6*2-m2-2 in
  let m4 := m5*2-m2-2 in
  let m1 := m4*4-m2*2-2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 2 in
  let m3 := n1/2 - 3 in
  let m6 := m3*2-m2-2 in
  let m5 := m6*2-m2-2 in
  let m4 := m5*2-m2-2 in
  let m1 := m4*4-m2*2-2 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM6.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1LC_1LC0RD_0LD1RF_1RE0LA_0RB---_1RB0RC").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 9124 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
N.Odd (mp 1%positive nat_t) /\
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := 17895725 in
  let n2 := 6 in
  let m2 := n2 + 2 in
  let m3 := n1 / 2 - 2 in
  let m6 := m3 * 2 - m2 - 3 in
  let m5 := m6 * 2 - m2 - 4 in
  let m4 := m5 * 2 - m2 - 3 in
  let m1 := m4 * 4 - m2 * 2 - 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  let n1 := mp 1%positive nat_t in
  let n2 := mp 2%positive nat_t in
  let m2 := n2 + 2 in
  let m3 := n1 / 2 - 2 in
  let m6 := m3 * 2 - m2 - 3 in
  let m5 := m6 * 2 - m2 - 4 in
  let m4 := m5 * 2 - m2 - 3 in
  let m1 := m4 * 4 - m2 * 2 - 3 in
  match i with
  | 1%positive => m1
  | 2%positive => m2
  | 3%positive => m3
  | 4%positive => m4
  | 5%positive => m5
  | 6%positive => m6
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try solve_OE_lia.
- repeat split; cbn;
  try solve_OE_lia.
Time Qed.
End TM5.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LE_0RD0RB_1RA---_1RF1LA_1RB1RD").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 14628 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive => (5230176645 - 12 - 16)*3 - 12 - 10
  | 2%positive => 3
  | 3%positive => 1743392223 - 8
  | 4%positive => 5230176645 - 12 - 16
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive =>
    ((mp 1%positive nat_t - 8) * 3 - ((mp 2%positive nat_t + 1) * 4 + 16)) * 3 -
    ((mp 2%positive nat_t + 1) * 4 + 10)
  | 2%positive => mp 2%positive nat_t + 1
  | 3%positive => mp 1%positive nat_t - 8
  | 4%positive => (mp 1%positive nat_t - 8) * 3 - ((mp 2%positive nat_t + 1) * 4 + 16)
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.
Time Qed.
End TM4.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RE_1RF0LD_1RE1LB_1RC1RA_0RA0RC").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 14304 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 16 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive => (6392438112 - 12 - 16)*3 - 12 - 10
  | 2%positive => 3
  | 3%positive => 2130812712 - 8
  | 4%positive => 6392438112 - 12 - 16
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive => ((mp 1%positive nat_t - 8) * 3 - ((mp 2%positive nat_t + 1) * 4 + 16))*3 - ((mp 2%positive nat_t + 1) * 4 + 10)
  | 2%positive => mp 2%positive nat_t + 1
  | 3%positive => mp 1%positive nat_t - 8
  | 4%positive => (mp 1%positive nat_t - 8) * 3 - ((mp 2%positive nat_t + 1) * 4 + 16)
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.

Time Qed.
End TM3.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1RC1RE_1RD0LA_0RE0RC_1RF---_1LC0RB").

Definition m_config := config_arithseq_fixed_block_size 0 3 37.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 15753 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 10 + 1000 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive => (78452649069 - 12 - 18)*3 - 12 - 12
  | 2%positive => 3
  | 3%positive => 26150883031-8
  | 4%positive => 4
  | 5%positive => 78452649069 - 12 - 18
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive => ((mp 1%positive nat_t - 8) * 3 - ((mp 2%positive nat_t + 1) * 4 + 18)) * 3 - ((mp 2%positive nat_t + 1) * 4 + 12)
  | 2%positive => mp 2%positive nat_t + 1
  | 3%positive => mp 1%positive nat_t - 8
  | 4%positive => 4
  | 5%positive => (mp 1%positive nat_t - 8) * 3 - ((mp 2%positive nat_t + 1) * 4 + 18)
  | _ => 0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.

Time Qed.

End TM2.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RA_1RD---_1LA0RF_1RF1LD_1RA1RC").

Definition m_config := config_arithseq_fixed_block_size 0 3 0.
Lemma m_config_WF: forall tm, Config_WF tm m_config.
Proof.
  intro tm.
  apply Config_WF_simple.
  reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
get_rule_from_inductive_decider m_config m_config_WF 14372 tm.

pose (fun (mp:id_t->forall t:type_t, to_cexpr_type t) =>
mp 2%positive nat_t * 10 + 100 <= mp 1%positive nat_t
) as P'.

pose (fun (i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive => (8716961043-12-14)*3-12-7
  | 2%positive => 3
  | 3%positive => 2905653681
  | 4%positive => 8716961043-12-14
  | _ => N0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp0.

pose (fun (mp:id_t->forall t, to_cexpr_type t)(i:id_t)(t:type_t) =>
match t return to_cexpr_type t with
| nat_t =>
  match i with
  | 1%positive => ((mp 1%positive nat_t - 9) * 3 - (mp 2%positive nat_t + 1) * 4 - 14) * 3 - ((mp 2%positive nat_t + 1) * 4 + 7)
  | 2%positive => mp 2%positive nat_t + 1
  | 3%positive => mp 1%positive nat_t - 9
  | 4%positive => (mp 1%positive nat_t-9)*3-(mp 2%positive nat_t+1)*4-14
  | _ => N0
  end
| seg_t => cseg_nil
| side_t => cside_0inf
end) as mp1.


solve_init H0' S0 mp0.
1: repeat tape_equal.
solve_closure H' S0 P P' mp1.
- repeat tape_equal;
  try lia.
- repeat split;
  try lia.
- repeat split; cbn;
  try lia.

Time Qed.
End TM1.



