(* M-Abozaid M7: BusyCoq translation of the translated-counter level cycle.
   Source and attribution: EXTERNAL_BOUNCER_PROOFS.md.
   All rules, initialization and nonhalting are proved in this file. *)
From BusyCoq Require Import Individual62 ES_v3.
From Coq Require Import String List Arith ZifyNat Lia.
Import ListNotations.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation z4 := [0;0;0;0].

Inductive token := a | b.
Definition tk t : list Sym := match t with a => [1;0] | b => [1;0;0] end.
Definition rr t : list Sym := match t with a => [1;0] | b => [1;1;0] end.
Definition em t : list Sym := match t with a => [1;0] | b => [0;1;0] end.
Fixpoint enc ts := match ts with [] => [] | t::ts => tk t ++ enc ts end.
Fixpoint ems ts := match ts with [] => [] | t::ts => em t ++ ems ts end.
Fixpoint rstack ts l := match ts with [] => l | t::ts => rstack ts (l <* rr t) end.

Lemma enc_app xs ys: enc (xs++ys) = enc xs ++ enc ys.
Proof. induction xs; cbn; congruence || (rewrite IHxs, app_assoc; reflexivity). Qed.
Lemma ems_app xs ys: ems (xs++ys) = ems xs ++ ems ys.
Proof. induction xs; cbn; congruence || (rewrite IHxs, app_assoc; reflexivity). Qed.

Lemma rs_a l r:
  l {{D}}> [1;0;0;1;0;1] *> r -->*
  l <* rr a {{D}}> [1;0;0;1] *> r.
Proof. unfold rr; es' & l r. Qed.
Lemma rs_b l r:
  l {{D}}> [1;0;0;1;0;0] *> r -->*
  l <* rr b {{D}}> [1;0;0] *> r.
Proof. unfold rr; es' & l r. Qed.
Lemma ls t l r:
  l <* rr t <{{D}} z4 *> r -->*
  l <{{D}} z4 *> em t *> r.
Proof. destruct t; unfold rr, em; es' & l r. Qed.
Lemma le1 l r:
  l {{D}}> [0;0;0;0;0;1;0;1] *> r -->*
  l <* [0;1;0;1] {{D}}> [1;0;0;1] *> r.
Proof. es' & l r. Qed.
Lemma le0 l r:
  l {{D}}> [0;0;0;0;0;1;0;0] *> r -->*
  l <* [1;0;1;0;1] {{D}}> [1;0;0] *> r.
Proof. es' & l r. Qed.
Lemma evG l r:
  l {{D}}> [1;0;0;1;1] *> r -->+
  l <{{D}} z4 *> [0] *> r.
Proof. es' & l r. Qed.
Lemma evT l r:
  l <* rr b {{D}}> [1;0;0;0] *> r -->+
  l <{{D}} z4 *> [0;0;1] *> r.
Proof. unfold rr; es' & l r. Qed.
Lemma rsweep ts l r:
  l {{D}}> [1;0;0] *> enc ts *> [1] *> r -->*
  rstack ts l {{D}}> [1;0;0;1] *> r.
Proof.
  revert l r; induction ts as [|t ts IH]; intros; cbn [enc rstack].
  - finish.
  - destruct t.
    + destruct ts as [|t ts].
      * cbn [enc rstack tk rr]; apply rs_a.
      * destruct t; cbn [enc tk]; follow rs_a; apply IH.
    + cbn [tk]; follow rs_b; apply IH.
Qed.

Lemma rsweep_b ts l r:
  l {{D}}> [1;0;0] *> enc (ts++[b]) *> r -->*
  rstack ts l <* rr b {{D}}> [1;0;0] *> r.
Proof.
  rewrite enc_app; cbn [enc tk].
  repeat rewrite app_nil_r. rewrite Str_app_assoc.
  follow rsweep. follow rs_b. finish.
Qed.

Lemma lsweep ts l r:
  rstack ts l <{{D}} z4 *> r -->*
  l <{{D}} z4 *> ems ts *> r.
Proof.
  revert l r; induction ts as [|t ts IH]; intros; cbn [rstack ems].
  - finish.
  - rewrite Str_app_assoc. follow IH. follow (ls t). finish.
Qed.

Lemma sweepG ts l r:
  l {{D}}> [1;0;0] *> enc ts *> [1;1] *> r -->+
  l <{{D}} z4 *> ems ts *> [0] *> r.
Proof.
  eapply evstep_progress_trans; [apply rsweep|].
  eapply progress_evstep_trans; [apply evG|apply lsweep].
Qed.

Lemma sweepT ts l r:
  l {{D}}> [1;0;0] *> enc (ts++[b]) *> [0] *> r -->+
  l <{{D}} z4 *> ems ts *> [0;0;1] *> r.
Proof.
  eapply evstep_progress_trans; [apply rsweep_b|].
  eapply progress_evstep_trans; [apply evT|apply lsweep].
Qed.

Lemma ems_a xs: ems (a::xs) ++ [0] = enc (xs++[b]).
Proof. induction xs as [|t xs IH]; [reflexivity|destruct t; cbn [ems em enc tk app] in *; now rewrite IH]. Qed.

Lemma enc_head ts r: exists r', enc ts *> [1] *> r = [1] *> r'.
Proof. destruct ts as [|t ts]; [eexists; reflexivity|destruct t; eexists; reflexivity]. Qed.
Lemma enc_snoc_head ts t r: exists r', enc (ts++[t]) *> r = [1] *> r'.
Proof. destruct ts as [|x ts]; [destruct t|destruct x]; eexists; reflexivity. Qed.

Lemma trip1G ys l r:
  l {{D}}> [0] *> z4 *> enc (a::ys) *> [1;1] *> r -->+
  l <* [1;0;1] {{D}}> [0] *> z4 *> ems ys *> [0] *> r.
Proof.
  cbn [enc tk]. rewrite Str_app_assoc.
  destruct (enc_head ys ([1] *> r)) as [r' E].
  change ([1;1] *> r) with ([1] *> [1] *> r).
  rewrite E. follow le1.
  change ([1;0;0;1] *> r') with ([1;0;0] *> [1] *> r'). rewrite <-E.
  eapply progress_evstep_trans; [apply sweepG|finish].
Qed.

Lemma trip1T ys l r:
  l {{D}}> [0] *> z4 *> enc (a::(ys++[b])) *> [0] *> r -->+
  l <* [1;0;1] {{D}}> [0] *> z4 *> ems ys *> [0;0;1] *> r.
Proof.
  cbn [enc tk]. rewrite Str_app_assoc.
  destruct (enc_snoc_head ys b ([0] *> r)) as [r' E].
  rewrite E. follow le1.
  change ([1;0;0;1] *> r') with ([1;0;0] *> [1] *> r'). rewrite <-E.
  eapply progress_evstep_trans; [apply sweepT|finish].
Qed.

Lemma enc_pow ts n: enc (ts^^n) = (enc ts)^^n.
Proof. induction n; cbn [lpow enc]; [reflexivity|now rewrite enc_app, IHn]. Qed.
Lemma ems_pow ts n: ems (ts^^n) = (ems ts)^^n.
Proof. induction n; cbn [lpow ems]; [reflexivity|now rewrite ems_app, IHn]. Qed.

Lemma stack_return j r:
  0inf <* [1;0;1]^^j <* [1;0;1;0;1] <{{D}} z4 *> r -->*
  0inf <{{D}} z4 *> [1;0] *> [0;1;0]^^j *> [1;0;1;0] *> r.
Proof. es' j & r. Qed.

(* One end event, independently of the low binary counter. *)
Inductive Ev : list token -> list Sym -> list token -> list Sym -> Prop :=
| EvG ts m: Ev ts ([1;1]++m) (ts++[b]) m
| EvT ts m: Ev (ts++[b]) (0::m) (ts++[b]) (0::1::m).

Lemma Ev_pre p ts m ts' m':
  Ev ts m ts' m' -> Ev (p++ts) m (p++ts') m'.
Proof. destruct 1; rewrite ?app_assoc; constructor. Qed.

Lemma trip1 ts m ts' m' l r:
  Ev ts m ts' m' ->
  l {{D}}> [0] *> z4 *> enc (a::a::ts) *> m *> r -->+
  l <* [1;0;1] {{D}}> [0] *> z4 *> enc ts' *> m' *> r.
Proof.
  destruct 1.
  - rewrite <-ems_a. repeat rewrite Str_app_assoc.
    apply trip1G.
  - rewrite <-ems_a. repeat rewrite Str_app_assoc.
    apply (trip1T (a::ts) l (m *> r)).
Qed.

Lemma trip0 j ts m ts' m' r:
  Ev ts m ts' m' ->
  0inf <* [1;0;1]^^j {{D}}> [0] *> z4 *> enc (b::ts) *> m *> r -->+
  0inf {{D}}> [0] *> z4 *> enc ([b]^^j++[a;a]++ts') *> m' *> r.
Proof.
  destruct 1.
  - cbn [enc tk]. rewrite Str_app_assoc.
    follow le0.
    eapply progress_evstep_trans; [apply sweepG|].
    follow stack_return.
    rewrite !app_assoc, <-ems_a. cbn [ems em]. rewrite !ems_app, ems_pow.
    cbn [ems em app]. repeat first [rewrite Str_app_assoc | progress cbn [Str_app]]. finish.
  - cbn [enc tk]. rewrite Str_app_assoc.
    follow le0.
    eapply progress_evstep_trans; [apply sweepT|].
    follow stack_return.
    rewrite !app_assoc, <-ems_a. cbn [ems em]. rewrite !ems_app, ems_pow.
    cbn [ems em app]. repeat first [rewrite Str_app_assoc | progress cbn [Str_app]]. finish.
Qed.

Fixpoint Evs n ts m ts' m' : Prop :=
  match n with
  | O => ts'=ts /\ m'=m
  | S n => exists ts1 m1, Ev ts m ts1 m1 /\ Evs n ts1 m1 ts' m'
  end.

Lemma Evs_pre n p ts m ts' m':
  Evs n ts m ts' m' -> Evs n (p++ts) m (p++ts') m'.
Proof.
  revert ts m ts' m'; induction n; cbn; intros.
  - intuition congruence.
  - destruct H as [ts1 [m1 [H H1]]].
    exists (p++ts1),m1. split; [apply Ev_pre,H|apply IHn,H1].
Qed.

Lemma Evs_split n k ts m ts' m':
  Evs (n+k) ts m ts' m' ->
  exists ts1 m1, Evs n ts m ts1 m1 /\ Evs k ts1 m1 ts' m'.
Proof.
  revert ts m; induction n; cbn; intros ts m H.
  - eauto.
  - destruct H as [ts0 [m0 [H H0]]].
    destruct (IHn _ _ H0) as [ts1 [m1 [H1 H2]]].
    exists ts1,m1; split; [eauto|assumption].
Qed.

(* t carry trips followed by the first zero.  The high counter digits may be
   included in the event's unchanged token prefix (Evs_pre). *)
Lemma carry t j ts m ts' m' r:
  Evs (1+t) ts m ts' m' ->
  0inf <* [1;0;1]^^j {{D}}> [0] *> z4 *> enc ([a;a]^^t++b::ts) *> m *> r -->+
  0inf {{D}}> [0] *> z4 *> enc ([b]^^(j+t)++[a;a]++ts') *> m' *> r.
Proof.
  revert j ts m ts' m'; induction t; intros j ts m ts' m' H;
    destruct H as [ts1 [m1 [H H1]]].
  - destruct H1 as [-> ->]. rewrite Nat.add_0_r. apply trip0,H.
  - cbn [lpow app].
    eapply progress_trans.
    + apply trip1. change (b::ts) with ([b]++ts).
      rewrite app_assoc. apply Ev_pre,H.
    + rewrite <-app_assoc. applys_eq (IHt (1+j) ts1 m1 ts' m' H1); flia.
Qed.

Lemma Evs_growth n ts k m:
  Evs n ts ([1;1]^^(n+k)++m) (ts++[b]^^n) ([1;1]^^k++m).
Proof.
  revert ts; induction n; intros; cbn [Evs lpow Nat.add].
  - rewrite app_nil_r; auto.
  - exists (ts++[b]), ([1;1]^^(n+k)++m). split.
    + constructor.
    + rewrite app_assoc. apply IHn.
Qed.

Lemma Evs_translate n ts k m:
  Evs n (ts++[b]) (0::([1]^^k++m)) (ts++[b]) (0::([1]^^(n+k)++m)).
Proof.
  revert k; induction n; intros; cbn [Evs Nat.add]; [auto|].
  exists (ts++[b]), (0::1::([1]^^k++m)). split; [constructor|].
  change (1::([1]^^k++m)) with ([1]^^(1+k)++m).
  rewrite <-Nat.add_succ_r. apply IHn.
Qed.

(* Fixed-width binary number, with its population count.  Zero digits are b,
   one digits are aa; these constructors avoid division/modulo in the tape. *)
Inductive Num : nat -> nat -> nat -> list token -> Prop :=
| Num_O: Num 0 0 0 []
| Num_0 w n p xs: Num w n p xs -> Num (1+w) (n*2) p (b::xs)
| Num_1 w n p xs: Num w n p xs -> Num (1+w) (1+n*2) (1+p) (a::a::xs).

Lemma Num_bound w n p xs: Num w n p xs -> n < 2^w /\ p <= w.
Proof. induction 1; cbn [Nat.pow Nat.add]; lia. Qed.

Lemma Num_unique w n p xs:
  Num w n p xs -> forall q ys, Num w n q ys -> p=q /\ xs=ys.
Proof.
  induction 1; intros q ys H'; inversion H' as [|w0 n0 p0 xs0 H0|w0 n0 p0 xs0 H0];
    subst; try lia; auto.
  all: assert (n=n0) by lia; subst n0;
    destruct (IHNum _ _ H0); subst; auto.
Qed.

Lemma Num_app w n p xs v m q ys:
  Num w n p xs -> Num v m q ys ->
  Num (w+v) (n+2^w*m) (p+q) (xs++ys).
Proof.
  induction 1; intros H1; cbn [app].
  - applys_eq H1; flia.
  - applys_eq (Num_0 _ _ _ _ (IHNum H1)); cbn [Nat.pow Nat.add]; try nia; flia.
  - applys_eq (Num_1 _ _ _ _ (IHNum H1)); cbn [Nat.pow Nat.add]; try nia; flia.
Qed.

Lemma Num_zero w: Num w 0 0 ([b]^^w).
Proof. induction w; [apply Num_O|exact (Num_0 _ _ _ _ IHw)]. Qed.

Lemma Num_ones w: Num w (2^w-1) w ([a;a]^^w).
Proof.
  induction w; cbn [lpow]; [apply Num_O|].
  applys_eq (Num_1 _ _ _ _ IHw); cbn [Nat.pow Nat.add]; flia.
Qed.

Lemma Num_inc w n p xs:
  Num w n p xs -> 1+n < 2^w ->
  exists t rest p', xs = [a;a]^^t ++ b::rest /\
    Num w (1+n) p' ([b]^^t++[a;a]++rest) /\ p'+t=1+p.
Proof.
  induction 1; intros Hn; [cbn in Hn; lia| |].
  - exists O,xs,(1+p). cbn [lpow app]. repeat split; auto.
    apply Num_1,H.
  - destruct IHNum as [t [rest [p' [E [H1 H2]]]]].
    + cbn [Nat.pow Nat.add] in Hn. lia.
    + exists (1+t),rest,p'. rewrite E. cbn [lpow app]. repeat split; try lia.
      applys_eq (Num_0 _ _ _ _ H1); flia.
Qed.

Definition ck xs ts m := 0inf {{D}}> [0] *> z4 *> enc (xs++ts) *> m *> 0inf.

Lemma increment w n p xs:
  Num w n p xs -> 1+n < 2^w ->
  exists f p' ys, 0<f /\ Num w (1+n) p' ys /\ f+p'=p+2 /\
    forall ts m ts' m', Evs f ts m ts' m' -> ck xs ts m -->+ ck ys ts' m'.
Proof.
  intros H Hn. destruct (Num_inc _ _ _ _ H Hn) as [t [rest [p' [E [H1 H2]]]]].
  exists (1+t),p',([b]^^t++[a;a]++rest).
  repeat split; try lia; auto.
  intros ts m ts' m' He. unfold ck. rewrite E, <-app_assoc.
  eapply progress_evstep_trans.
  - apply (carry t 0). apply Evs_pre,He.
  - rewrite !app_assoc. finish.
Qed.

Lemma increments k w n p xs:
  Num w n p xs -> n+k < 2^w ->
  exists f q ys, Num w (n+k) q ys /\ k<=f /\ f+q=p+k*2 /\
    forall ts m ts' m', Evs f ts m ts' m' -> ck xs ts m -->* ck ys ts' m'.
Proof.
  revert n p xs; induction k; intros n p xs H Hn.
  - exists O,p,xs. rewrite Nat.add_0_r. repeat split; auto; try lia.
    intros ts m ts' m' [-> ->]. finish.
  - destruct (increment _ _ _ _ H) as [f1 [p1 [xs1 [Hf1 [HN1 [HC1 HS1]]]]]]; [lia|].
    destruct (IHk _ _ _ HN1) as [f2 [q [ys [HN2 [Hf2 [HC2 HS2]]]]]]; [lia|].
    exists (f1+f2),q,ys. repeat split; try lia.
    + applys_eq HN2; flia.
    + intros ts m ts' m' HE.
      destruct (Evs_split _ _ _ _ _ _ HE) as [ts1 [m1 [HE1 HE2]]].
      eapply evstep_trans; [eapply progress_evstep,HS1,HE1|apply HS2,HE2].
Qed.

(* Total number of end events is determined by the two population counts.
   This replaces both division and a separate recursive popcount computation. *)
Lemma count w n k p q xs ys f ts m ts' m':
  Num w n p xs -> Num w (n+k) q ys -> f+q=p+k*2 ->
  Evs f ts m ts' m' -> ck xs ts m -->* ck ys ts' m'.
Proof.
  intros HN HN' HC HE.
  destruct (increments k _ _ _ _ HN) as [f' [q' [ys' [HN1 [HF [HC1 HS]]]]]].
  - apply (Num_bound _ _ _ _ HN').
  - destruct (Num_unique _ _ _ _ HN' _ _ HN1); subst q' ys'.
    assert (f'=f) by lia. subst f'. apply HS,HE.
Qed.

Lemma growth w n k p q xs ys f ts rem m:
  Num w n p xs -> Num w (n+k) q ys -> f+q=p+k*2 ->
  ck xs ts ([1;1]^^(f+rem)++m) -->*
  ck ys (ts++[b]^^f) ([1;1]^^rem++m).
Proof. intros; eapply count; eauto using Evs_growth. Qed.

(* Overflow rules.  O0 and O1 share the same final sweep. *)
Definition OV j ts m :=
  0inf <* [1;0;1]^^j {{D}}> [0] *> z4 *> [0] *> enc ts *> m *> 0inf.

Lemma ems_b0 xs: ems (b::xs) ++ [0] = 0 :: enc (xs++[b]).
Proof. change (0::(ems (a::xs)++[0]) = 0::enc (xs++[b])). now rewrite ems_a. Qed.

Lemma zpair n l r:
  l {{D}}> [0] *> z4 *> [0] *> [1;0;0]^^(2+n*2) *> [0] *> r -->+
  l <* [1;0;1;0;1] {{D}}> [0] *> z4 *> [0] *> [1;0;0]^^(n*2) *> [0;1] *> r.
Proof. es' n & l r. Qed.

Lemma zpairs n l r:
  l {{D}}> [0] *> z4 *> [0] *> [1;0;0]^^(n*2) *> [0] *> r -->*
  l <* [1;0;1;0;1]^^n {{D}}> [0] *> z4 *> [0;0] *> [1]^^n *> r.
Proof.
  revert l r; induction n; intros; [finish|].
  change (S n*2) with (2+n*2).
  eapply evstep_trans; [eapply progress_evstep,zpair|].
  change ([0;1] *> r) with ([0] *> [1] *> r).
  follow IHn.
  change ([1] *> r) with ([1]^^1 *> r).
  change ([1;0;1;0;1] *> l) with ([1;0;1;0;1]^^1 *> l).
  rewrite !lpow_add'. replace (n+1) with (S n) by lia. finish.
Qed.

Lemma oend j k r:
  0inf <* [1;0;1]^^j <* [1;0;1;0;1]^^k {{D}}> [0] *> z4 *> [0;0;1;1] *> r -->+
  0inf {{D}}> [0] *> z4 *> [1;0;0]^^j *> [1;0;1;0;0]^^k *> [1;0;1;0;1;0] *> r.
Proof. es' j k & r. Qed.

Lemma o01 j k p m:
  2<=p+k ->
  OV j ([b]^^(k*2)) (0::([1]^^p++m)) -->+
  ck ([b]^^j) ([a;b]^^k++[a;a;a]) ([1]^^(p+k-2)++m).
Proof.
  intros H. unfold OV,ck. rewrite !enc_app, !enc_pow. cbn [enc tk app].
  repeat rewrite Str_app_assoc.
  eapply evstep_progress_trans; [apply zpairs|].
  rewrite !Str_app_assoc, lpow_add'.
  replace (k+p) with (2+(p+k-2)) by lia. cbn [lpow app].
  apply oend.
Qed.

Lemma o2_start l r:
  l {{D}}> [0] *> z4 *> [0] *> [1;0;1;0;0] *> r -->*
  l <* [1;0;1;1;0;1;0;1] {{D}}> [1;0;0] *> r.
Proof. es' & l r. Qed.
Lemma o2_return j r:
  0inf <* [1;0;1]^^j <* [1;0;1;1;0;1;0;1] <{{D}} z4 *> r -->*
  0inf {{D}}> [0] *> z4 *> [1;0;0]^^j *> enc [a;b;a;a] *> r.
Proof. cbn [enc tk app]. es' j & r. Qed.

Lemma o2 j ts m:
  OV j (a::b::(ts++[b])) (0::m) -->+
  ck ([b]^^j) (a::b::a::(ts++[b])) (0::1::m).
Proof.
  unfold OV,ck. cbn [enc tk]. repeat rewrite Str_app_assoc.
  follow o2_start.
  eapply progress_evstep_trans; [apply sweepT|].
  follow o2_return.
  rewrite enc_app, enc_pow. cbn [enc tk app].
  rewrite <-ems_a. cbn [ems em].
  repeat first [rewrite Str_app_assoc | progress cbn [Str_app]]. finish.
Qed.

Lemma o3_start l r:
  l {{D}}> [0] *> z4 *> [0] *> [1;0;1;0;1] *> r -->*
  l <* [0;1;1;0;1;0;1] {{D}}> [1;0;0;1] *> r.
Proof. es' & l r. Qed.

Lemma o3pass ts l r:
  l {{D}}> [0] *> z4 *> [0] *> enc (a::a::b::(ts++[b])) *> [0] *> r -->+
  l <* [1;1;0;1;0;1] {{D}}> [0] *> z4 *> [0] *> enc (ts++[b]) *> [0;1] *> r.
Proof.
  cbn [enc tk]. repeat rewrite Str_app_assoc. follow o3_start.
  eapply progress_evstep_trans; [apply (sweepT (b::ts))|].
  change ([0] *> enc (ts++[b]) *> [0;1] *> r) with ((0::enc (ts++[b])) *> [0;1] *> r).
  rewrite <-ems_b0. repeat first [rewrite Str_app_assoc | progress cbn [Str_app]]. finish.
Qed.

Lemma o3_return j r:
  0inf <* [1;0;1]^^j <* [1;1;0;1;0;1] <* [1;0;1;1;0;1;0;1] <{{D}} z4 *> r -->*
  0inf {{D}}> [0] *> z4 *> [1;0;0]^^j *> enc [a;b] *> [0] *> enc [a;b;a;a] *> r.
Proof. cbn [enc tk app]. es' j & r. Qed.

Lemma o3 j ts m:
  OV j (a::a::b::a::b::(ts++[b])) (0::m) -->+
  ck ([b]^^j) [a;b] (0::(enc (a::b::a::(ts++[b]))++[0;1;1]++m)).
Proof.
  unfold OV,ck.
  eapply progress_trans; [apply (o3pass (a::b::ts) _ (m *> 0inf))|].
  cbn [enc tk]. repeat rewrite Str_app_assoc. follow o2_start.
  eapply progress_evstep_trans; [apply sweepT|].
  follow o3_return.
  rewrite enc_app, enc_pow. cbn [enc tk app].
  rewrite <-ems_a. cbn [ems em].
  repeat first [rewrite Str_app_assoc | progress cbn [Str_app]]. finish.
Qed.

Definition EndB ts := ts=[] \/ exists us, ts=us++[b].

Lemma Ev_translate_b ts m:
  EndB ts -> Ev (b::ts) (0::m) (b::ts) (0::1::m).
Proof.
  intros [->|[us ->]]; [apply (EvT [] m)|apply (EvT (b::us) m)].
Qed.

Lemma topT ts l r:
  EndB ts ->
  l {{D}}> [0] *> z4 *> enc (a::b::ts) *> [0] *> r -->+
  l <* [1;0;1] {{D}}> [0] *> z4 *> [0] *> enc ts *> [0;1] *> r.
Proof.
  intros [->|[us ->]].
  - apply (trip1T [] l r).
  - change ([0] *> enc (us++[b]) *> [0;1] *> r) with
      ((0::enc (us++[b])) *> [0;1] *> r).
    rewrite <-ems_b0, Str_app_assoc. apply (trip1T (b::us) l r).
Qed.

Lemma ov_run w j ts p m:
  EndB ts ->
  0inf <* [1;0;1]^^j {{D}}> [0] *> z4 *> enc ([a;a]^^w++a::b::ts) *>
    (0::([1]^^p++m)) *> 0inf -->+
  OV (j+w+1) ts (0::([1]^^(w+1+p)++m)).
Proof.
  intros HT. revert j p; induction w; intros j p.
  - unfold OV. cbn [lpow app].
    eapply progress_evstep_trans; [apply topT,HT|].
    change ([1;0;1] *> ([1;0;1]^^j *> 0inf)) with ([1;0;1]^^(1+j) *> 0inf).
    replace (j+0+1) with (1+j) by lia. finish.
  - cbn [lpow app]. eapply progress_trans.
    + apply trip1. change (a::b::ts) with ([a]++(b::ts)).
      rewrite app_assoc. apply Ev_pre,Ev_translate_b,HT.
    + rewrite <-app_assoc. cbn [app].
      applys_eq (IHw (1+j) (1+p)); unfold OV; flia.
Qed.

Lemma overflow w ts p m:
  EndB ts ->
  ck ([a;a]^^w) (a::b::ts) (0::([1]^^p++m)) -->+
  OV (1+w) ts (0::([1]^^(1+w+p)++m)).
Proof. intros HT; unfold ck. applys_eq (ov_run w 0 ts p m HT); unfold OV; flia. Qed.

Lemma Evs_translate_b n ts k m:
  EndB ts ->
  Evs n (a::b::ts) (0::([1]^^k++m)) (a::b::ts) (0::([1]^^(n+k)++m)).
Proof.
  intros [->|[us ->]]; [apply (Evs_translate n [a])|apply (Evs_translate n (a::b::us))].
Qed.

(* Include the overflow itself: the width term in the normal popcount formula
   cancels against the final w+1 trips. *)
Lemma translate_overflow w n p xs ts k m f:
  Num w n p xs -> EndB ts -> f+1+n*2=2^w*2+p ->
  ck xs (a::b::ts) (0::([1]^^k++m)) -->+
  OV (1+w) ts (0::([1]^^(f+k)++m)).
Proof.
  intros HN HT HF. pose proof (Num_bound _ _ _ _ HN) as HB.
  destruct (increments (2^w-1-n) _ _ _ _ HN) as [g [q [ys [HN1 [HG [HC HS]]]]]]; [lia|].
  replace (n+(2^w-1-n)) with (2^w-1) in HN1 by lia.
  destruct (Num_unique _ _ _ _ (Num_ones w) _ _ HN1); subst q ys.
  eapply evstep_progress_trans; [apply HS,Evs_translate_b,HT|].
  applys_eq (overflow w ts (g+k) m HT); unfold OV; flia.
Qed.

Lemma Num_one: Num 1 1 1 [a;a].
Proof. apply (Num_1 _ _ _ _ Num_O). Qed.

Lemma Num_two_bits u v:
  Num (u+v+2) (2^u+2^(u+v+1)) 2 ([b]^^u++[a;a]++[b]^^v++[a;a]).
Proof.
  applys_eq (Num_app _ _ _ _ _ _ _ _ (Num_zero u)
    (Num_app _ _ _ _ _ _ _ _ Num_one
      (Num_app _ _ _ _ _ _ _ _ (Num_zero v) Num_one)));
    rewrite ?Nat.pow_add_r; cbn [Nat.pow]; try nia; flia.
Qed.

Lemma Num_three_high j:
  Num (j+6) (2^j*7) 3 ([b]^^j++[a;a]^^3++[b]^^3).
Proof.
  applys_eq (Num_app _ _ _ _ _ _ _ _ (Num_zero j)
    (Num_app _ _ _ _ _ _ _ _ (Num_ones 3) (Num_zero 3))); flia.
Qed.

Lemma swallow rest ts qs m:
  ck (a::a::b::rest) ts ([1;1]++enc (qs++[b])++[0]++m) -->+
  ck (b::a::a::rest) (ts++[b]++qs++[b]) (0::1::m).
Proof.
  unfold ck. eapply progress_trans.
  - apply trip1,EvG.
  - rewrite !app_assoc. rewrite !enc_app. repeat rewrite Str_app_assoc.
    eapply progress_evstep_trans.
    + applys_eq (trip0 1 _ _ _ _ 0inf (EvT (rest++ts++[b]++qs) m));
        rewrite ?enc_app; cbn [enc tk lpow app];
        repeat first [rewrite enc_app | rewrite Str_app_assoc | progress cbn [enc tk app Str_app]]; reflexivity.
    + rewrite !enc_app. cbn [enc tk lpow app].
      repeat first [rewrite Str_app_assoc | progress cbn [Str_app]]. finish.
Qed.

(* Source Level.lean: the low bits are 1, j+5 zeros, 1. *)
Definition tmpl j ts z rest :=
  ck ([a;a]++[b]^^(j+5)++[a;a]) [a;b]
    ([1]^^(2^(j+6)-4)++[0]++enc ts++[0]++[1]^^z++rest).
Definition Rest0 := enc ([a;a]++[b]^^28) ++ [0] ++ [1]^^741.

Lemma growth_to w n p xs n' q ys f ts rem m:
  Num w n p xs -> Num w n' q ys -> n<=n' -> f+q=p+(n'-n)*2 ->
  ck xs ts ([1]^^((f+rem)*2)++m) -->*
  ck ys (ts++[b]^^f) ([1]^^(rem*2)++m).
Proof.
  intros HN HN' HL HF. rewrite !lpow_mul.
  eapply growth; [apply HN| |apply HF]. applys_eq HN'; flia.
Qed.

Lemma EndB_pow n: EndB ([b]^^n).
Proof.
  destruct n; [left; reflexivity|right; exists ([b]^^n)].
  cbn [lpow]. symmetry; apply lpow_shift.
Qed.

Lemma phaseE0 j q z rest:
  tmpl j q z rest -->+
  ck ([b]^^(j+8)) ([a;b]^^(2^j*16-1)++[a;a;a])
    ([1]^^(2^j*112-2)++enc q++[0]++[1]^^z++rest).
Proof.
  assert (H0: Num (j+7) (1+2^j*64) 2 ([a;a]++[b]^^(j+5)++[a;a])).
  { applys_eq (Num_two_bits 0 (j+5)); rewrite ?Nat.pow_add_r; cbn [Nat.pow]; flia. }
  assert (H1: Num (j+7) (2^j*80) 2 ([b]^^(j+4)++[a;a]++[b]++[a;a])).
  { applys_eq (Num_two_bits (j+4) 1); rewrite ?Nat.pow_add_r; cbn [Nat.pow]; flia. }
  unfold tmpl.
  replace (2^(j+6)-4) with (((2^j*32-2)+0)*2) by (rewrite Nat.pow_add_r; cbn; lia).
  eapply evstep_progress_trans; [eapply growth_to; [apply H0|apply H1|lia|lia]|].
  eapply progress_trans.
  - apply (translate_overflow _ _ _ _ _ 0 _ (2^j*96+1) H1 (EndB_pow _)).
    rewrite Nat.pow_add_r; cbn; lia.
  - replace (1+(j+7)) with (j+8) by lia.
    replace (2^j*32-2) with ((2^j*16-1)*2) by lia.
    applys_eq (o01 (j+8) (2^j*16-1) (2^j*96+1) (enc q++[0]++[1]^^z++rest) ltac:(lia));
      unfold OV,ck; flia.
Qed.

Lemma pow_cons {A} (x:A) n ys: [x]^^n++x::ys = [x]^^(1+n)++ys.
Proof. change ([x]^^n++[x]++ys = [x]^^(1+n)++ys). rewrite app_assoc, lpow_shift. reflexivity. Qed.

Lemma phaseE1 j q z rest:
  ck ([b]^^(j+8)) ([a;b]^^(2^j*16-1)++[a;a;a])
    ([1]^^(2^j*112-2)++enc (q++[b])++[0]++[1]^^z++rest) -->+
  OV (j+9) ([a;b]^^(2^j*16-2)++[a;a;a]++[b]^^(2^j*56-1)++q++[b])
    (0::([1]^^(z+2^j*456)++rest)).
Proof.
  assert (H1: Num (j+8) (2^j*28+1) 4 (a::a::b::([b]^^j++[a;a]^^3++[b]^^3))).
  { applys_eq (Num_1 _ _ _ _ (Num_0 _ _ _ _ (Num_three_high j))); flia. }
  assert (H2: Num (j+8) (2^j*28+2) 4 (b::a::a::([b]^^j++[a;a]^^3++[b]^^3))).
  { applys_eq (Num_0 _ _ _ _ (Num_1 _ _ _ _ (Num_three_high j))); flia. }
  replace (2^j*112-2) with (((2^j*56-2)+1)*2) by lia.
  eapply evstep_progress_trans; [eapply growth_to; [apply Num_zero|apply H1|lia|lia]|].
  eapply progress_trans; [apply swallow|].
  replace (2^j*16-1) with (1+(2^j*16-2)) by lia.
  cbn [Nat.add lpow app].
  repeat rewrite <-app_assoc. cbn [app].
  rewrite (pow_cons b (2^j*56-2)).
  replace (1+(2^j*56-2)) with (2^j*56-1) by lia.
  repeat rewrite <-app_assoc.
  change (1::([1]^^z++rest)) with ([1]^^(1+z)++rest).
  eapply progress_evstep_trans.
  - eapply translate_overflow; [apply H2| |].
    + right; eexists; repeat first [rewrite app_assoc | rewrite app_comm_cons]; reflexivity.
    + instantiate (1:=2^j*456-1). rewrite Nat.pow_add_r; cbn; lia.
  - unfold OV. finish; flia.
Qed.

Definition nq j q :=
  b::a::([a;b]^^(2^j*16-5)++[a;a;a]++[b]^^(2^j*56-1)++q).

Lemma phaseE2 j q y rest:
  OV (j+9) ([a;b]^^(2^j*16-2)++[a;a;a]++[b]^^(2^j*56-1)++q++[b])
    (0::([1]^^y++rest)) -->+
  ck ([b]^^(j+10)) [a;b]
    (0::(enc (a::(nq j q++[b]))++[0]++[1]^^(y+2^j*1024+2)++rest)).
Proof.
  replace (2^j*16-2) with (3+(2^j*16-5)) by lia.
  cbn [Nat.add lpow app].
  repeat first [rewrite app_assoc | rewrite app_comm_cons].
  eapply progress_trans; [apply o2|].
  change (1::([1]^^y++rest)) with ([1]^^(1+y)++rest).
  eapply progress_trans.
  - eapply (translate_overflow _ _ _ _ _ (1+y)); [apply Num_zero| |].
    + right; eexists; repeat rewrite app_comm_cons; reflexivity.
    + instantiate (1:=2^j*1024-1). rewrite Nat.pow_add_r; cbn; lia.
  - replace (1+(j+9)) with (j+10) by lia.
    replace (2^j*1024-1+(1+y)) with (y+2^j*1024) by lia.
    eapply progress_evstep_trans; [apply o3|].
    unfold ck,nq. rewrite !enc_app. cbn [enc tk app].
    repeat first [rewrite enc_app | rewrite Str_app_assoc | progress cbn [enc tk app Str_app]].
    replace (y+2^j*1024+2) with (2+(y+2^j*1024)) by lia. finish.
Qed.

Lemma pend xs ts m:
  ck (b::xs) ts ([1;1]++m) -->+ ck ([a;a]++xs) (ts++[b]) m.
Proof.
  unfold ck. eapply progress_evstep_trans; [apply (trip0 0),EvG|].
  rewrite !app_assoc. finish.
Qed.

Lemma phaseE3 j q z rest:
  ck ([b]^^(j+10)) [a;b]
    (0::(enc (a::(q++[b]))++[0]++[1]^^z++rest)) -->+
  tmpl (j+5) (q++[b]) z rest.
Proof.
  eapply progress_trans.
  - eapply (translate_overflow _ _ _ _ [] 0 _ (2^j*2048-1));
      [apply Num_zero|left; reflexivity|].
    rewrite Nat.pow_add_r; cbn; lia.
  - replace (1+(j+10)) with (j+11) by lia. rewrite Nat.add_0_r.
    eapply progress_trans; [apply (o01 _ 0); lia|].
    replace (2^j*2048-1+0-2) with (2+(2^j*2048-5)) by lia.
    replace (j+11) with (1+(j+10)) by lia.
    eapply progress_evstep_trans; [apply pend|].
    unfold tmpl,ck. rewrite !enc_app. cbn [enc tk app].
    repeat rewrite <-app_assoc. cbn [app].
    rewrite (pow_cons (1:Sym) (2^j*2048-5)).
    replace (1+(2^j*2048-5)) with (2^(j+5+6)-4) by (rewrite !Nat.pow_add_r; cbn; lia).
    replace (j+5+5) with (j+10) by lia.
    repeat first [rewrite enc_app | rewrite Str_app_assoc | progress cbn [lpow enc tk app Str_app]].
    finish; fold (@app Sym);
      repeat first [rewrite Str_app_assoc | progress cbn [Str_app]]; reflexivity.
Qed.

Lemma level j q z rest:
  tmpl j (q++[b]) z rest -->+
  tmpl (j+5) (nq j q++[b]) (z+2^j*1480+2) rest.
Proof.
  eapply progress_trans; [apply phaseE0|].
  eapply progress_trans; [apply phaseE1|].
  eapply progress_trans; [apply phaseE2|].
  replace (z+2^j*456+2^j*1024+2) with (z+2^j*1480+2) by lia.
  apply phaseE3.
Qed.

(* Small-fuel version of Bouncer_v3.multistep_c'.  Kept local because the
   installed Bouncer_v3.vo currently has an incompatible ES_v3 digest. *)
Fixpoint run_blocks n k tail c :=
  match n with
  | O => multistep_c tm tail c
  | S n => match multistep_c tm k c with
           | Some c' => run_blocks n k tail c' | None => None end
  end.
Lemma run_blocks_spec n k tail c c':
  run_blocks n k tail c = Some c' -> c -->* c'.
Proof.
  revert c; induction n; intros c; cbn [run_blocks].
  - intros H; eapply without_counter, multistep_c_spec,H.
  - destruct (multistep_c tm k c) as [c1|] eqn:E; [|congruence].
    intros H. eapply evstep_trans; [|apply IHn,H].
    eapply without_counter, multistep_c_spec,E.
Qed.

Lemma init: c0 -->* tmpl 4 [b] 0 Rest0.
Proof. apply (run_blocks_spec 1000 1132 435). native_check_eq. Qed.

Definition checkpoint '(j,q,z) := tmpl j (q++[b]) z Rest0.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=checkpoint (4,[],O)); [apply init|].
  eapply progress_nonhalt_simple. intros [[j q] z].
  exists (j+5,nq j q,z+2^j*1480+2). apply level.
Qed.

End TM1.
