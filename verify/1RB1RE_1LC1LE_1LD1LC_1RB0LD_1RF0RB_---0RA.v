
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1LE_1LD1LC_1RB0LD_1RF0RB_---0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.


Definition a:list Sym := [0;1;1;0;1].
Definition b:list Sym := [0;1;1;0;1;1].
Definition c:list Sym := [0;1;0;1;1].

Definition a':list Sym := [1;1;1;1;1].
Definition b':list Sym := [0;1;1;1;1;1].
Definition c':list Sym := [0;1;1;1;1].

Definition x:list Sym := [0;1].
Definition y:list Sym := [0;1;1].

Notation "l <| r" :=
  (l <{{D}} [0] *> r) (at level 30).
Notation "l <y| r" :=
  (l <* y <{{D}} [0] *> r) (at level 30).
Notation "l <b'| r" :=
  (l <{{D}} [0] *> b' *> r) (at level 30).
Notation "l |> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Lemma ER l r n:
  l |> b'^^n *> r -->*
  l <* b^^n |> r.
Proof.
  shift_rule.
  steps.
Qed.

Lemma DL l r n:
  l <* b^^n <| r -->*
  l <| b'^^n *> r.
Proof.
  shift_rule.
  steps.
Qed.

Lemma DLbba l r n:
  l <* (b++b++a)^^n <| r -->*
  l <| (a'++b'++b')^^n *> r.
Proof.
  shift_rule.
  steps.
Qed.

Lemma DLbab l r n:
  l <* (b++a++b)^^n <| r -->*
  l <| (b'++a'++b')^^n *> r.
Proof.
  shift_rule.
  steps.
Qed.

Lemma ERabb l r n:
  l |> (a'++b'++b')^^n *> r -->*
  l <* (b++a++b)^^n |> r.
Proof.
  shift_rule.
  steps.
Qed.

Lemma ERbab l r n:
  l |> (b'++a'++b')^^n *> r -->*
  l <* (a++b++b)^^n |> r.
Proof.
  shift_rule.
  steps.
Qed.

Lemma LInc r n m:
  const 0 <* a <* (b++b++a)^^n <* b <* b {{A}}> [1;1;0;1;1;1]^^(2+m) *> r -->*
  const 0 <* a <* (b++b++a)^^(1+n) <* b <* b {{A}}> [1;1;0;1;1;1]^^m *> r.
Proof.
  steps.
  follow DLbba.
  steps.
  follow ERabb.
  steps.
  follow DLbab.
  steps.
  follow ERbab.
  steps.
  repeat (rewrite lpow_rotate; cbn).
  finish.
Qed.

Lemma LIncs n m r:
  const 0 <* a <* (b++b++a)^^n <* b <* b {{A}}> [1;1;0;1;1;1]^^(m*2) *> r -->*
  const 0 <* a <* (b++b++a)^^(m+n) <* b <* b {{A}}> r.
Proof.
  gen n.
  induction m; intros.
  - finish.
  - follow LInc.
    follow IHm.
    finish.
Qed.

Lemma b'_rot n r:
  1>>1>>b'^^n *> r =
  [1;1;0;1;1;1]^^n *> 1>>1>>r.
Proof.
  repeat (rewrite lpow_rotate; cbn).
  reflexivity.
Qed.

Lemma LIncs' r n:
  const 0 <* a^^3 <* b^^(n*2) <* a <| r -->*
  const 0 <* a <* (b++b++a)^^n <* b^^3 |> r.
Proof.
  steps.
  follow DL.
  do 3 step.
  rewrite b'_rot.
  steps.
  follow (LIncs 0).
  steps.
Qed.

Definition a_bs n :=
  a ++ b^^(n+1).

Definition a_bs' n :=
  b'^^(n+1) ++ a'.

Definition ba_bs' n :=
  b'^^n ++ a' ++ b'.

Definition bc_bs' n :=
  b'^^n ++ c' ++ b'.

Definition ba_bs n :=
  b ++ a ++ b^^n.

Definition bc_bs n :=
  b ++ c ++ b^^n.

Lemma bs_y n l:
  l <* (b^^n) <* y =
  l <* y <* (b^^n).
Proof.
  unfold b.
  cbn.
  repeat (rewrite lpow_rotate; cbn).
  reflexivity.
Qed.

Lemma a_bs_y n l:
  l <* (a_bs n) <* y =
  l <* y <* (bc_bs n).
Proof.
  cbn.
  unfold b.
  simpl_tape.
  cbn.
  repeat (rewrite lpow_rotate; cbn).
  reflexivity.
Qed.

Lemma a_bs_ys ls l:
  l <* (flat_map a_bs ls) <* y =
  l <* y <* (flat_map bc_bs ls).
Proof.
  gen l.
  induction ls; intros.
  - reflexivity.
  - cbn[flat_map].
    repeat rewrite Str_app_assoc.
    rewrite <-IHls.
    apply a_bs_y.
Qed.

Lemma ER_ba_bs' l r n:
  l |> (ba_bs' n) *> r -->*
  l <* (a_bs n) |> r.
Proof.
  unfold ba_bs',a_bs.
  repeat rewrite Str_app_assoc.
  follow ER.
  steps.
Qed.

Lemma ER_bc_bs' l r n:
  l |> (bc_bs' n) *> r -->*
  l <* (a_bs n) |> r.
Proof.
  unfold bc_bs',a_bs.
  repeat rewrite Str_app_assoc.
  follow ER.
  steps.
Qed.

Lemma ER_a_bs' l r n:
  l |> (a_bs' n) *> r -->*
  l <* b^^(n+2) {{A}}> r.
Proof.
  unfold a_bs'.
  repeat rewrite Str_app_assoc.
  follow ER.
  steps.
  unfold b.
  repeat (rewrite lpow_rotate; cbn).
  finish.
Qed.

Lemma DL_bc_bs l r n:
  l <* (bc_bs n) <| r -->*
  l <| (bc_bs' n) *> r.
Proof.
  unfold bc_bs,bc_bs'.
  repeat rewrite Str_app_assoc.
  steps.
  follow DL.
  steps.
Qed.

Lemma ERs_ba_bs' l r ls:
  l |> (flat_map ba_bs' ls) *> r -->*
  l <* (flat_map a_bs (rev ls)) |> r.
Proof.
  gen l r.
  induction ls; intros.
  - finish.
  - cbn[flat_map].
    rewrite Str_app_assoc.
    follow ER_ba_bs'.
    follow IHls.
    cbn.
    rewrite flat_map_app.
    cbn.
    rewrite app_nil_r.
    repeat rewrite Str_app_assoc.
    finish.
Qed.

Lemma ERs_bc_bs' l r ls:
  l |> (flat_map bc_bs' ls) *> r -->*
  l <* ((flat_map a_bs (rev ls))) |> r.
Proof.
  gen l r.
  induction ls; intros.
  - finish.
  - cbn[flat_map].
    rewrite Str_app_assoc.
    follow ER_bc_bs'.
    follow IHls.
    cbn.
    rewrite flat_map_app.
    cbn.
    rewrite app_nil_r.
    repeat rewrite Str_app_assoc.
    finish.
Qed.

Lemma DLs_bc_bs l r ls:
  l <* (flat_map bc_bs ls) <| r -->*
  l <| (flat_map bc_bs' (rev ls)) *> r.
Proof.
  gen l r.
  induction ls; intros.
  - finish.
  - cbn[flat_map].
    rewrite Str_app_assoc.
    follow DL_bc_bs.
    follow IHls.
    cbn.
    rewrite flat_map_app.
    cbn.
    rewrite app_nil_r.
    repeat rewrite Str_app_assoc.
    finish.
Qed.

Lemma lpow_1(a:list Sym):
  a ^^ 1 = a.
Proof.
  apply app_nil_r.
Qed.

Lemma ba_bs_rot n l:
  (ba_bs n) *> b *> l =
  b *> (a_bs n) *> l.
Proof.
  unfold a_bs,ba_bs.
  rewrite lpow_add,lpow_1.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma ba_bs_rots ls l:
  flat_map ba_bs ls *> b *> l =
  b *> flat_map a_bs ls *> l.
Proof.
  induction ls.
  - reflexivity.
  - cbn[flat_map].
    repeat rewrite Str_app_assoc.
    rewrite IHls.
    apply ba_bs_rot.
Qed.

Lemma DL_ba_bs l r n:
  l <* ba_bs n <| r -->*
  l <| ba_bs' n *> r.
Proof.
  unfold ba_bs,ba_bs'.
  repeat rewrite Str_app_assoc.
  steps.
  follow DL.
  finish.
Qed.

Lemma DLs_ba_bs l r ls:
  l <* flat_map ba_bs ls <| r -->*
  l <| flat_map ba_bs' (rev ls) *> r.
Proof.
  gen l r.
  induction ls; intros.
  - finish.
  - cbn[flat_map].
    rewrite Str_app_assoc.
    follow DL_ba_bs.
    follow IHls.
    cbn.
    rewrite flat_map_app.
    cbn.
    rewrite app_nil_r.
    repeat rewrite Str_app_assoc.
    finish.
Qed.

Lemma DL_a_bs l r n:
  l <* (a_bs n) <| r -->*
  l <| (a_bs' n) *> r.
Proof.
  unfold a_bs,a_bs'.
  repeat rewrite Str_app_assoc.
  steps.
  follow DL.
  steps.
  unfold b'.
  repeat (rewrite lpow_rotate; cbn).
  finish.
Qed.

Lemma DLs_a_bs l r ls:
  l <* (flat_map a_bs ls) <| r -->*
  l <| (flat_map a_bs' (rev ls)) *> r.
Proof.
  gen l r.
  induction ls; intros.
  - finish.
  - cbn[flat_map].
    rewrite Str_app_assoc.
    follow DL_a_bs.
    follow IHls.
    cbn.
    rewrite flat_map_app.
    cbn.
    rewrite app_nil_r.
    repeat rewrite Str_app_assoc.
    finish.
Qed.

Lemma flat_map_lpow{A B} (f:A->list B) ls n:
  flat_map f (ls^^n) = (flat_map f ls)^^n.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    rewrite <-IHn.
    apply flat_map_app.
Qed.


Definition r1 := [0;1;1;1] *> const 0.
Definition r2 := [1;1] *> const 0.

Lemma RL1 l:
  l |> r1 -->*
  l <y| r2.
Proof.
  steps.
Qed.

Lemma RL2 l:
  l |> r2 -->*
  l <| r1.
Proof.
  steps.
Qed.

Lemma RL1_a' l:
  l |> a' *> r1 -->*
  l <y| c' *> r2.
Proof.
  steps.
Qed.

Lemma LR0 n r:
  const 0 <* a^^3 <* (a_bs (n*2+1)) <b'| r -->*
  const 0 <* a^^2 <* (a_bs 1)^^n <* b^^6 |> r.
Proof.
  unfold a_bs.
  replace (n*2+1+1) with ((n+1)*2) by lia.
  repeat rewrite Str_app_assoc.
  follow LIncs'.
  rewrite lpow_add,lpow_1.
  repeat rewrite Str_app_assoc.
  do 2 rewrite lpow_rotate',<-app_assoc.
  rewrite <-(lpow_1 b').
  follow ER.
  finish.
Qed.






Definition M s n :=
  b^^n ++ (flat_map a_bs s).

Definition Ma s n :=
  (flat_map ba_bs' (rev s)) ++ b'^^n.

Definition Mc s n :=
  (flat_map bc_bs' (rev s)) ++ b'^^n.

Lemma RL2_c' l s n:
  l <* M s n |> c' *> r2 -->*
  l <* M s (S n) <| r2.
Proof.
  unfold M.
  simpl_tape.
  steps.
Qed.

Lemma DL_M l r s n:
  l <* M s (S n) <| r -->*
  l <b'| Ma s n *> r.
Proof.
  unfold M,Ma.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add,lpow_1.
  repeat rewrite Str_app_assoc.
  follow DL.
  rewrite <-ba_bs_rots.
  follow DLs_ba_bs.
  steps.
Qed.

Lemma yDL_M l r s n:
  l <* M s n <y| r -->*
  l <y| Mc s n *> r.
Proof.
  unfold M,Mc.
  repeat rewrite Str_app_assoc.
  rewrite bs_y.
  rewrite a_bs_ys.
  follow DL.
  follow DLs_bc_bs.
  finish.
Qed.

Lemma ER_Ma l r s n:
  l |> Ma s n *> r -->*
  l <* M s n |> r.
Proof.
  unfold Ma,M.
  repeat rewrite Str_app_assoc.
  follow ERs_ba_bs'.
  follow ER.
  rewrite rev_involutive.
  finish.
Qed.

Lemma ER_Mc l r s n:
  l |> Mc s n *> r -->*
  l <* M s n |> r.
Proof.
  unfold Mc,M.
  repeat rewrite Str_app_assoc.
  follow ERs_bc_bs'.
  follow ER.
  rewrite rev_involutive.
  finish.
Qed.

Lemma M_app s1 s2 n:
  M (s1++s2) n = M s1 n ++ (flat_map a_bs s2).
Proof.
  unfold M.
  rewrite flat_map_app,app_assoc.
  reflexivity.
Qed.

Definition l1 := const 0 <* a^^3.
Definition l2 := const 0 <* a^^2.

Lemma M_bs n1 n2 n3 ls r:
  M (ls++[n1]) n2 *> b^^n3 *> r =
  M (ls++[n1+n3]) n2 *> r.
Proof.
  unfold M.
  repeat rewrite flat_map_app.
  cbn[flat_map].
  repeat rewrite app_nil_r.
  unfold a_bs.
  replace (n1+n3+1) with (n1+1+n3) by lia.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma M_l1 ls n n0 n1 r:
  l1 <* (M (ls++[n1;n*2+1])%nat (S n0)) <| r -->*
  l2 <* (M (ls++[n1+6]++[1]^^n)%nat n0) |> r.
Proof.
  unfold l1,l2.
  cbn[app].
  replace (ls++[n1;n*2+1])%nat with ((ls++[n1])++[n*2+1])%nat. 2:{
    cbn.
    rewrite <-app_assoc.
    reflexivity.
  }
  rewrite M_app,Str_app_assoc.
  follow DL_M.
  cbn[flat_map].
  rewrite app_nil_r.
  follow LR0.
  follow ER_Ma.
  rewrite M_bs.
  repeat rewrite M_app.
  cbn[flat_map].
  repeat rewrite Str_app_assoc.
  rewrite flat_map_lpow.
  cbn[flat_map].
  rewrite app_nil_r.
  finish.
Qed.

Lemma M_pop n s:
  M (n::s) 0 = a ++ b ++ M s n.
Proof.
  unfold M.
  cbn[flat_map].
  unfold a_bs.
  rewrite (Nat.add_comm n 1).
  rewrite lpow_add,lpow_1.
  repeat rewrite <-app_assoc.
  reflexivity.
Qed.

Lemma DLa l r:
  l <* a <| r -->*
  l <| a' *> r.
Proof.
  steps.
Qed.

Lemma M_b s n r:
  b *> M s n *> r =
  M s (S n) *> r.
Proof.
  unfold M.
  simpl_tape.
  reflexivity.
Qed.

Lemma M_r2_l1_pop ls n n0 n1:
  l1 <* (M ((n0)::ls++[n1;n*2+1])%nat 0) |> r2 -->*
  l2 <* (M (ls++[n1+6]++[1]^^n)%nat n0) |> a' *> r1.
Proof.
  unfold l1,l2.
  cbn[app].
  follow RL2.
  rewrite M_pop.
  repeat rewrite Str_app_assoc.
  follow DLa.
  rewrite M_b.
  follow M_l1.
  finish.
Qed.

Lemma LR2y r:
  l2 <y| r -->+
  l1 |> r.
Proof.
  execute.
Qed.

Lemma M_a_bs s n n0 r:
  M s n *> a_bs n0 *> r =
  M (s++[n0]) n *> r.
Proof.
  unfold M.
  rewrite flat_map_app.
  repeat rewrite Str_app_assoc.
  cbn[flat_map].
  rewrite app_nil_r.
  reflexivity.
Qed.

Ltac simpl_list :=
  repeat (
  rewrite <-app_assoc ||
  rewrite app_nil_r ||
  cbn[app]).

Ltac list_eq := simpl_list; reflexivity.

Definition l3 := const 0 <* x <* (a_bs 1).

Lemma LR2b' r:
  l2 <b'| r -->+
  l3 |> r.
Proof.
  execute.
Qed.

Definition l4 := const 0 <* x <* (a_bs 2).

Lemma LR3y r:
  l3 <y| r -->+
  l4 |> r.
Proof.
  execute.
Qed.

Definition l5 := const 0 <* a^^2 <* (a_bs 2).

Lemma LR4b' r:
  l4 <b'| r -->+
  l5 |> r.
Proof.
  execute.
Qed.

Definition l6 := const 0 <* a^^3 <* (a_bs 2).

Lemma LR5y r:
  l5 <y| r -->+
  l6 |> r.
Proof.
  execute.
Qed.

Ltac steps1 :=
  eapply progress_evstep_trans; [constructor; constructor; reflexivity | steps].

Lemma LR6b' r:
  l6 <b'| r -->+
  l3 <* b^^6 |> r.
Proof.
  execute.
Qed.

Ltac follow' x :=
match goal with
| |- _ -[ _ ]->+ _ => follow10 x
| |- _ -[ _ ]->* _ => follow100 x
end.

Ltac nxt1 x :=
  (follow RL1 || follow RL1_a');
  follow yDL_M;
  follow' x;
  follow ER_Mc.

Ltac nxt2 x :=
  (follow RL2 || follow RL2_c');
  follow DL_M;
  follow' x;
  follow ER_Ma.

Lemma M_pop' l r n s:
  l <* M (n::s) 0 <| r -->*
  l <* M s (S n) <| a' *> r.
Proof.
  rewrite M_pop.
  repeat rewrite Str_app_assoc.
  follow DLa.
  rewrite M_b.
  finish.
Qed.

Lemma l4_r2 s n n0:
  l4 <* M (s++[n0]) (S (S n)) |> r2 -->+
  l4 <* M (s++[n0+6]) n |> r2.
Proof.
  nxt2 LR4b'.
  nxt1 LR5y.
  nxt2 LR6b'.
  rewrite M_bs.
  nxt1 LR3y.
  finish.
Qed.

Lemma LR3b' r:
  l3 <b'| r -->+
  l2 <* a_bs 1 |> r.
Proof.
  execute.
Qed.

Lemma l4_r2_0 s n n0:
  l4 <* M ((S n)::s++[n0]) O |> r2 -->+
  l1 <* M ((s++[n0+6])++[1])%nat n |> r2.
Proof.
  follow RL2.
  follow M_pop'.
  follow DL_M.
  follow' LR4b'.
  follow ER_Ma.
  nxt1 LR5y.
  nxt2 LR6b'.
  rewrite M_bs.

  nxt2 LR3b'.
  rewrite M_a_bs.
  nxt1 LR2y.

  finish.
Qed.

Lemma l4_r2_s s n n0 n1:
  l4 <* M ((S (n0))::s++[n1]) (n*2) |> r2 -->+
  l1 <* M ((s++[n1+n*6+6])++[1])%nat (n0) |> r2.
Proof.
  gen n1.
  induction n; intros.
  - follow' l4_r2_0.
    finish.
  - rewrite app_comm_cons.
    follow' l4_r2.
    follow' IHn.
    finish.
Qed.


Lemma l1_r2 s n0 n1 n2:
  l1 <* M ((s++[n1])++[n2*2+1]) (S n0) |> r2 -->+
  l1 <* M (s++[n1+6]++[1]^^n2)%nat n0 |> r2.
Proof.
  follow RL2.
  rewrite <-app_assoc.
  cbn[app].
  follow M_l1.
  nxt1 LR2y.
  finish.
Qed.

Lemma l1_c'r2 s n0 n1 n2:
  l1 <* M ((s++[n1])++[n2*2+1]) (S (n0)) |> c' *> r2 -->+
  l4 <* M (s++[n1+6]++[1]^^n2)%nat (n0) |> r2.
Proof.
  follow RL2_c'.
  rewrite <-app_assoc.
  cbn[app].
  follow M_l1.
  nxt2 LR2b'.
  nxt1 LR3y.
  finish.
Qed.

Lemma l1_r2_0 s n0 n1 n2:
  l1 <* M (n0::((s++[n1])++[n2*2+1]))%nat O |> r2 -->+
  l1 <* M (s++[n1+6]++[1]^^n2)%nat (n0) |> c' *> r2.
Proof.
  follow RL2.
  follow M_pop'.
  rewrite <-app_assoc.
  cbn[app].
  follow M_l1.
  nxt1 LR2y.
  finish.
Qed.

Inductive config :=
| config_l1_r2(s:list nat)(n0 n1 n2:nat)
| config_l1_c'r2(s:list nat)(n0 n1 n2:nat)
| config_l4_r2_s(s:list nat)(n0 n1 n2:nat)
.

Definition to_config(x:config) :=
match x with
| config_l1_r2 s n0 n1 n2 => l1 <* M ((s++[n1*2+1])++[n2*2+1]) (n0) |> r2
| config_l1_c'r2 s n0 n1 n2 => l1 <* M ((s++[n1*2+1])++[n2*2+1]) (S (n0*2)) |> c' *> r2
| config_l4_r2_s s n0 n1 n2 => l4 <* M (S (n1*2)::s++[n2*2+1]) (n0*2) |> r2
end.

Import Nat.
Close Scope sym.

Definition P(x:config):Prop :=
match x with
| config_l1_r2 s n0 n1 n2 => Forall Odd s /\ (n2 = 0 /\ length s >= 4 \/ n2>=3 /\ length s >= 3)
| config_l1_c'r2 s n0 n1 n2 => Forall Odd s /\ (n2 = 0 /\ length s >= 4 \/ n2>=3 /\ length s >= 2)
| config_l4_r2_s s n0 n1 n2 => Forall Odd s /\ (length s >= 3)
end.

Lemma Forall_lpow{A} (P:A->Prop) a n:
  Forall P a ->
  Forall P (a^^n).
Proof.
  intro H.
  induction n.
  - auto.
  - cbn.
    rewrite Forall_app; split; auto.
Qed.

Lemma lpow_length{A} (s:list A) n:
  Datatypes.length (s^^n) = n*(Datatypes.length s).
Proof.
  induction n.
  - reflexivity.
  - cbn.
    rewrite app_length,IHn.
    reflexivity.
Qed.

Ltac solve_Forall:=
  repeat (
  rewrite Forall_app ||
  rewrite Forall_cons_iff ||
  apply Forall_lpow);
  repeat split; auto.

Theorem nonhalt: ~halts tm c0.
apply multistep_nonhalt with (c':=to_config (config_l1_r2 [1;1;1;1] 5 0 0)%nat).
1: {
  do 79 ((do 100 (eapply evstep_step; [prove_step|])); simpl_tape).
  do 56 (eapply evstep_step; [prove_step|]).
  simpl_tape.
  finish.
}
apply (progress_nonhalt_cond tm _ _ _ P).
2:{
  split.
  - solve_Forall.
    all: exists 0; lia.
  - cbn; lia.
}
intros x HP.
destruct x.
1,2: destruct HP as [H0 [[H1 H2]|[H1 H2]]].
- subst n2.
  destruct s as [|n s].
  1: cbn in H2; lia.
  epose proof (@exists_last _ s _) as H.
  destruct H as [s1 [s2 s3]].
  subst s.
  rewrite Forall_cons_iff,Forall_app,Forall_cons_iff in H0.
  destruct H0 as [H0a [H0b [H0c _]]].
  destruct H0a as [n' Ha]; subst n.
  destruct H0c as [s2' Hs2]; subst s2.
  destruct n0 as [|n0].
  + exists (config_l1_c'r2 s1 n' s2' (n1+3)).
    split.
    * cbn[to_config].
      follow' l1_r2_0.
      simpl_list.
      finish.
    * split; auto 1.
      cbn in H2.
      rewrite app_length in H2.
      cbn in H2.
      lia.
  + exists (config_l1_r2 (2*n'+1 :: s1) n0 s2' (n1+3)).
    split.
    * cbn[to_config].
      follow' l1_r2.
      simpl_list.
      finish.
    * split.
      -- solve_Forall.
        exists n'; reflexivity.
      -- cbn.
        cbn in H2.
        rewrite app_length in H2.
        cbn in H2.
        lia.
- destruct s as [|n s].
  1: cbn in H2; lia.
  rewrite Forall_cons_iff in H0.
  destruct H0 as [H0a H0b].
  destruct H0a as [n' Ha]; subst n.
  destruct n0 as [|n0].
  + eexists (config_l1_c'r2 (s++[n1*2+1+6]++[1]^^(n2-2)) n' 0 0).
    split.
    * cbn[to_config].
      follow' l1_r2_0.
      replace n2 with (n2-2+2) by lia.
      rewrite lpow_add.
      simpl_list.
      finish.
    * split.
      -- repeat rewrite Forall_app.
         repeat split; auto 1.
        ++ solve_Forall.
           exists (n1+3); lia.
        ++ solve_Forall.
           exists 0; reflexivity.
      -- repeat rewrite app_length; cbn.
         cbn in H2.
         rewrite lpow_length. cbn.
         lia.
  + eexists (config_l1_r2 (2*n'+1::s++[n1*2+1+6]++[1]^^(n2-2)) n0 0 0).
    split.
    * cbn[to_config].
      follow' l1_r2.
      replace n2 with (n2-2+2) by lia.
      rewrite lpow_add.
      simpl_list.
      finish.
    * split.
      -- solve_Forall.
        ++ exists n'; lia.
        ++ exists (n1+3); lia.
        ++ solve_Forall.
           exists 0; reflexivity.
      -- repeat (rewrite app_length || cbn).
        cbn in H2.
        lia.
- subst n2.
  destruct s as [|n s].
  1: cbn in H2; lia.
  rewrite Forall_cons_iff in H0.
  destruct H0 as [H0a H0b].
  destruct H0a as [n' Ha]; subst n.
  eexists (config_l4_r2_s s n0 n' (n1+3)).
  split.
  * cbn[to_config].
    follow' l1_c'r2.
    simpl_list.
    finish.
  * split; auto.
    cbn in H2.
    lia.
- destruct s as [|n s].
  1: cbn in H2; lia.
  rewrite Forall_cons_iff in H0.
  destruct H0 as [H0a H0b].
  destruct H0a as [n' Ha]; subst n.
  eexists (config_l4_r2_s (s++(n1*2+1+6)::[1]^^(n2-1)) n0 n' 0).
  split.
  * cbn[to_config].
    follow' l1_c'r2.
    replace n2 with (n2-1+1) by lia.
    rewrite lpow_add.
    simpl_list.
    finish.
  * split.
    -- solve_Forall.
      ++ exists (n1+3); lia.
      ++ solve_Forall.
         exists 0; lia.
    -- cbn in H2.
      rewrite app_length; cbn.
      rewrite lpow_length; cbn.
      lia.
- destruct HP as [Ha Hb].
destruct s as [|n s].
1: cbn in Hb; lia.
destruct s as [|m s].
1: cbn in Hb; lia.
  epose proof (@exists_last _ s _) as H.
  destruct H as [s1 [s2 s3]].
  subst s.
  rewrite Forall_cons_iff,Forall_cons_iff,Forall_app,Forall_cons_iff in Ha.
  destruct Ha as [H0a [H0b [H0c [H0d]]]].
  destruct H0a as [n' Hn]; subst n.
  destruct H0b as [m' Hm]; subst m.
  destruct H0d as [s2' Hs2]; subst s2.

  destruct n1 as [|n1].
  + eexists (config_l4_r2_s (s1++[2*s2'+1+6]++[1]^^(n2+n0*3+5)) n' m' 0).
    split.
    * cbn[to_config].
      follow' l4_r2_s.
      change [1] with [0*2+1].
      follow' l1_r2_0.
      rewrite app_nil_r.
      rewrite (Nat.add_comm (2*n') 1).
      replace (n2*2+1+n0*6+6+6) with ((n2+n0*3+6)*2+1) by lia.
      rewrite app_comm_cons.
      follow' l1_c'r2.
      simpl_list.
      rewrite (Nat.add_comm (2*m') 1).
      replace (n2+n0*3+6) with (n2+n0*3+5+1) by lia.
      simpl_tape.
      finish.
    * split.
      -- solve_Forall.
        ++ exists (s2'+3); lia.
        ++ solve_Forall. exists 0; lia.
      -- repeat rewrite app_length.
        rewrite lpow_length. cbn.
        lia.
  + eexists (config_l1_r2 ((2*n'+1::2*m'+1::s1)++[2*s2'+1+6]++[1]^^(n2+n0*3+4)) (n1*2) 0 0).
    split.
    * cbn[to_config].
      follow' l4_r2_s.
      change [1] with [0*2+1].
      follow' l1_r2. fold add. fold mul.
      rewrite app_nil_r.
      repeat rewrite app_comm_cons.
      replace (n2*2+1+n0*6+6+6) with ((n2+n0*3+6)*2+1) by lia.
      follow' l1_r2.
      replace (n2+n0*3+6) with (n2+n0*3+4+2) by lia.
      simpl_list.
      simpl_tape.
      finish.
    * split.
      -- solve_Forall.
        ++ exists n'; lia.
        ++ exists m'; lia.
        ++ exists (s2'+3); lia.
        ++ solve_Forall.
          exists 0; lia.
      -- cbn.
        rewrite app_length. cbn.
        rewrite lpow_length. cbn.
        lia.
Unshelve.
++ intro; subst; cbn in H2; lia.
++ intro; subst; cbn in Hb; lia.
Qed.

(*
```
1RB1RE_1LC1LE_1LD1LC_1RB0LD_1RF0RB_---0RA

start: A(5,1,1,1,1,1,1)
A(n+1,...,x,2y+1) -> A(n,...,x+6(,1)^y)
A(0,n,...,x,2y+1) -> B(n,...,x+6(,1)^y)
B(n+1,...,x,2y+1) -> C(n,...,x+6(,1)^y)
C(2n,m+1,...,x)   -> A(m,...,x+6n+6,1)

A(n,a[1],a[2],...,a[k]) = 0^inf 10110^3 f(a[k]) ... f(a[2]) f(a[1]) g(n) E> 11 0^inf
B(n,a[1],a[2],...,a[k]) = 0^inf 10110^3 f(a[k]) ... f(a[2]) f(a[1]) g(n) E> 01111 11 0^inf
C(n,a[1],a[2],...,a[k]) = 0^inf 10 f(2) f(a[k]) ... f(a[2]) f(a[1]) g(n) E> 11 0^inf
f(x) = 110110^(x+1) 10110
g(x) = 110110^x 1
```
hard CTL-able machine (current proof is not by CTL)
*)

