(** The rule map of 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA, from the raw machine, with exact step counts. *)
From BusyCoq Require Import Individual62.
Require Import Lia String.
Open Scope list.
Open Scope string.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA").
Notation "c -->> n / c'" := (c -[ tm ]->> n / c') (at level 40, n at next level).
Notation "1s" := ([1]) .

Lemma ms_refl c c': c = c' -> c -->> 0 / c'.
Proof. intros ->. constructor. Qed.
Lemma ms_app n m c c' c'': c -->> n / c' -> c' -->> m / c'' -> c -->> (n + m) / c''.
Proof. intros H1 H2. eapply multistep_trans; eauto. Qed.
Lemma ms_eq n N c c': c -->> n / c' -> n = N -> c -->> N / c'.
Proof. intros H <-. exact H. Qed.
Lemma ms_src n c1 c c': c1 = c -> c -->> n / c' -> c1 -->> n / c'.
Proof. intros -> H. exact H. Qed.


Lemma p1 (x:Stream Sym) k: [1;1]^^k *> 1 >> 1 >> x = 1 >> 1 >> [1;1]^^k *> x.
Proof. apply lpow_shift2. Qed.
Lemma p11_add (x:Stream Sym) k m: [1;1]^^k *> [1;1]^^m *> x = [1;1]^^(k+m) *> x.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.
Lemma p01 (x:Stream Sym) k: [0;1]^^k *> 0 >> 1 >> x = 0 >> 1 >> [0;1]^^k *> x.
Proof. apply lpow_shift2. Qed.
Lemma p01_inv (x:Stream Sym) k: [0;1]^^k *> 0 >> 1 >> x = [0;1]^^(S k) *> x.
Proof. rewrite p01. reflexivity. Qed.
Lemma p10 (x:Stream Sym) k: [1;0]^^k *> 1 >> 0 >> x = 1 >> 0 >> [1;0]^^k *> x.
Proof. apply lpow_shift2. Qed.
Lemma ones2 (x:Stream Sym) k: [1]^^(2*k) *> x = [1;1]^^k *> x.
Proof.
  induction k. { reflexivity. }
  replace (2 * S k) with (S (S (2*k))) by lia. cbn [lpow app Str_app]. rewrite IHk. reflexivity.
Qed.
Lemma ones_add (x:Stream Sym) k m: [1]^^k *> [1]^^m *> x = [1]^^(k+m) *> x.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma n11a (x:Stream Sym) k: [1;1]^^k *> 1 >> 1 >> x = [1;1]^^(S k) *> x.
Proof. rewrite lpow_shift2. reflexivity. Qed.
Lemma n11b (x:Stream Sym) k: 1 >> 1 >> [1;1]^^k *> x = [1;1]^^(S k) *> x.
Proof. reflexivity. Qed.
Lemma n01a (x:Stream Sym) k: [0;1]^^k *> 0 >> 1 >> x = [0;1]^^(S k) *> x.
Proof. rewrite lpow_shift2. reflexivity. Qed.
Lemma n01b (x:Stream Sym) k: 0 >> 1 >> [0;1]^^k *> x = [0;1]^^(S k) *> x.
Proof. reflexivity. Qed.
Lemma n10a (x:Stream Sym) k: [1;0]^^k *> 1 >> 0 >> x = [1;0]^^(S k) *> x.
Proof. rewrite lpow_shift2. reflexivity. Qed.
Lemma n10b (x:Stream Sym) k: 1 >> 0 >> [1;0]^^k *> x = [1;0]^^(S k) *> x.
Proof. reflexivity. Qed.
Lemma n1a (x:Stream Sym) k: [1]^^k *> 1 >> x = [1]^^(S k) *> x.
Proof. rewrite lpow_shift1. reflexivity. Qed.
Lemma n1b (x:Stream Sym) k: 1 >> [1]^^k *> x = [1]^^(S k) *> x.
Proof. reflexivity. Qed.
Lemma padd (w:list Sym) (x:Stream Sym) a b: w^^a *> w^^b *> x = w^^(a+b) *> x.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.
Lemma appcons (a:Sym) (w:list Sym) (x:Stream Sym): (a::w) *> x = a >> w *> x.
Proof. reflexivity. Qed.
Lemma appnil (x:Stream Sym): [] *> x = x.
Proof. reflexivity. Qed.
Lemma p0nil (w:list Sym) (x:Stream Sym): w^^0 *> x = x.
Proof. reflexivity. Qed.
Create HintDb pn.
#[export] Hint Rewrite n1a n1b n11a n11b n01a n01b n10a n10b padd appcons appnil p0nil @Str_app_assoc : pn.

Ltac teq := solve [reflexivity | (autorewrite with pn; repeat (reflexivity || lia || f_equal))].
Ltac cstep := eapply multistep_S; [prove_step | simpl_tape].
Ltac cfin := apply ms_refl; teq.
Ltac cexec := repeat (try solve [cfin]; cstep).
(** run a lemma from the current configuration; its source must match up to arithmetic in the exponents *)
Ltac cf H := eapply ms_app; [eapply ms_src; [|exact H]; teq|].
Ltac costs := eapply ms_eq.

(** Shift rules. Left streams list the cell next to the head first. *)
Lemma SA k l r: l {{A}}> [0;1]^^k *> r -->> (2*k) / l <* [1;1]^^k {{A}}> r.
Proof.
  revert l. induction k; intros l. { cfin. }
  costs. { cbn [lpow app Str_app]. cstep. cstep. rewrite <- p1. apply IHk. } lia.
Qed.

Lemma SF k l r: (l <* [1;1]^^k) <{{F}} r -->> (2*k) / l <{{F}} [0;1]^^k *> r.
Proof.
  revert r. induction k; intros r. { cfin. }
  costs. { cbn [lpow app Str_app]. cstep. cstep. rewrite <- p01. apply IHk. } lia.
Qed.

Lemma SA' k l r: (l <* [1;1]^^k) <{{A}} r -->> (2*k) / l <{{A}} [1;0]^^k *> r.
Proof.
  revert r. induction k; intros r. { cfin. }
  costs. { cbn [lpow app Str_app]. cstep. cstep. rewrite <- p10. apply IHk. } lia.
Qed.

Lemma SA'S k l r: (A, (1 >> [1;1]^^k *> l, 1, r)) -->> (2*S k) / l <{{A}} [1;0]^^(S k) *> r.
Proof. exact (SA' (S k) l r). Qed.

Lemma SC k l r: l {{C}}> [1;0]^^k *> r -->> (2*k) / l <* [1;0]^^k {{C}}> r.
Proof.
  revert l. induction k; intros l. { cfin. }
  costs. { cbn [lpow app Str_app]. cstep. cstep. rewrite <- p10. apply IHk. } lia.
Qed.

Lemma SE n l r: (l <* [1]^^n) <{{E}} r -->> n / l <{{E}} [1]^^n *> r.
Proof.
  revert r. induction n; intros r. { cfin. }
  costs. { cbn [lpow app Str_app]. cstep. rewrite <- lpow_shift1. apply IHn. } lia.
Qed.

(** Tape left of the head: [1^6 (01)^j 1^(2k)], as a stream. *)
Definition L6 : side := [1;1;1;1;1;1] *> const 0.
Definition LL j k : side := [1;1]^^k *> [1;0]^^j *> L6.

(** [0 1 (11)^k A> 1 1 r] gives [(11)^(k+2) A> r]. *)
Lemma Ta k l r: [1;1]^^k *> 1 >> 0 >> l {{A}}> [1;1] *> r -->> (4*k+6) / [1;1]^^(k+2) *> l {{A}}> r.
Proof.
  costs.
  { cbn [Str_app]. cstep.
    eapply ms_app. { apply (SF k (1>>0>>l)). }
    cstep. cstep. cstep.
    cf (SA (S k) (1>>1>>l) r). cfin. }
  lia.
Qed.

Lemma rot01 k (x:Stream Sym): [0;1]^^k *> 0 >> x = 0 >> [1;0]^^k *> x.
Proof. apply (lpow_rotate [1] 0 x k). Qed.

(** [(11)^(n+1) A> 1 1 1 r] from the left end, to [1^6 (01)^(n+1) A> r]. *)
Lemma L1 n r: [1;1]^^(S n) *> const 0 {{A}}> [1;1;1] *> r -->> (4*n+19) / LL (S n) 0 {{A}}> r.
Proof.
  costs.
  { cbn [Str_app]. cstep.
    eapply ms_app. { apply (SF (S n) (const 0)). }
    cstep. cbn [lpow app Str_app]. do 11 cstep.
    rewrite rot01. cstep. cstep.
    eapply ms_app. { apply (SC n). }
    cstep. cstep. unfold LL, L6. cfin. }
  lia.
Qed.

Lemma Tb' l r: [1;0] *> l {{A}}> 1 >> 0 >> r -->> 2 / l {{A}}> [0;1;0;0] *> r.
Proof. cexec. Qed.

Lemma Tb k l r: [1;1]^^k *> 1 >> 0 >> l {{A}}> 1 >> 0 >> r -->> (4*k+4) / [1;1]^^(S k) *> l {{A}}> 0 >> 0 >> r.
Proof.
  costs.
  { cstep.
    eapply ms_app. { apply (SF k (1>>0>>l)). }
    do 3 cstep.
    cf (SA k (1>>1>>l) (0>>0>>r)). cfin. }
  lia.
Qed.

Lemma Drain t k j l r: [1;1]^^k *> [1;0]^^(j+t) *> l {{A}}> [1;1]^^t *> r -->> (4*k*t+4*t*t+2*t) / [1;1]^^(k+2*t) *> [1;0]^^j *> l {{A}}> r.
Proof.
  revert k. induction t; intros k.
  { costs. { cfin. } lia. }
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (Ta k ([1;0]^^(j+t) *> l) ([1;1]^^t *> r))].
      replace (j + S t) with (S (j + t)) by lia. teq. }
    eapply ms_app. { apply (IHt (k+2)). }
    cfin. }
  nia.
Qed.

Lemma Z1 l r: l {{A}}> [0;1;0;0;1;1;1;0] *> r -->> 8 / [1;1;1;1] *> l {{A}}> [0;1;0;0] *> r.
Proof. cexec. Qed.

Lemma Zk k l r: l {{A}}> [0;1;0;0] *> [1;1;1;0]^^k *> r -->> (8*k) / [1;1]^^(2*k) *> l {{A}}> [0;1;0;0] *> r.
Proof.
  revert l. induction k; intros l. { cfin. }
  costs.
  { eapply ms_app. { apply (Z1 l ([1;1;1;0]^^k *> r)). }
    eapply ms_app. { apply IHk. }
    cfin. }
  lia.
Qed.

(** [l A> 0 1 0 0 1 1 1 1 r] gives [l (11)^4 A> r]. *)
Lemma Zs l r: l {{A}}> [0;1;0;0;1;1;1;1] *> r -->> 12 / [1;1]^^4 *> l {{A}}> r.
Proof.
  costs.
  { do 6 cstep.
    cf (Ta 0 ([1;1;1;1] *> l) r). cfin. }
  lia.
Qed.

Lemma End1 l: l {{A}}> [0;0;1] *> const 0 -->> 9 / [1;1;1] *> l {{D}}> [0;0;1] *> const 0.
Proof. cexec. Qed.

Lemma EndE k l: [1;1]^^k *> 1 >> 0 >> l {{A}}> [0;1] *> const 0 -->> (2*k+13) / 1 >> l {{D}}> 0 >> [1;0]^^(k+2) *> [0;1] *> const 0.
Proof.
  costs.
  { do 7 cstep.
    eapply ms_app.
    { eapply ms_src; [|apply (SA'S (S k) (1>>0>>l))]. teq. }
    do 2 cstep. cfin. }
  lia.
Qed.

Lemma EndE0 k: [1;1]^^k *> L6 {{A}}> [0;1] *> const 0 -->> (2*k+17) / const 0 {{A}}> [0;1]^^(k+5) *> [0;0;1] *> const 0.
Proof.
  costs.
  { remember (k+5) as m eqn:Em.
    do 7 cstep.
    eapply ms_app.
    { eapply ms_src; [|apply (SA'S (k+4) (const 0))]. unfold L6. teq. }
    apply ms_refl. change ([0;0;1] *> const 0) with (0 >> [0;1] *> const 0). rewrite rot01.
    replace (S (k+4)) with m by lia. reflexivity. }
  lia.
Qed.

Lemma DLs n l r: [1]^^n *> [1;0] *> [1;0] *> l {{D}}> 0 >> r -->> (n+5) / [1] *> l {{D}}> 0 >> 0 >> [1]^^(n+2) *> r.
Proof.
  costs.
  { cstep.
    eapply ms_app. { apply (SE n (1>>0>>1>>0>>l)). }
    do 4 cstep. cfin. }
  lia.
Qed.

Lemma sh1110 k (Y:Stream Sym): [1;1;1;0]^^k *> 1 >> 1 >> 1 >> 0 >> Y = 1 >> 1 >> 1 >> 0 >> [1;1;1;0]^^k *> Y.
Proof. exact (lpow_shift' _ k [1;1;1;0] Y). Qed.

Lemma DLr k l Y: [1] *> [1;0]^^(2*k) *> l {{D}}> 0 >> 0 >> Y -->> (6*k) / [1] *> l {{D}}> 0 >> 0 >> [1;1;1;0]^^k *> Y.
Proof.
  revert Y. induction k; intros Y. { cfin. }
  costs.
  { replace (2 * S k) with (S (S (2 * k))) by lia.
    eapply ms_app.
    { eapply ms_src; [|apply (DLs 1 ([1;0]^^(2*k) *> l) (0>>Y))]. teq. }
    eapply ms_app. { apply IHk. }
    apply ms_refl. cbn. rewrite sh1110. reflexivity. }
  lia.
Qed.

Lemma DL0 n r: [1]^^n *> L6 {{D}}> 0 >> r -->> (n+18) / L6 {{A}}> [1]^^(n+3) *> r.
Proof.
  costs.
  { cstep.
    eapply ms_app. { apply (SE n L6). }
    unfold L6. do 17 cstep. cfin. }
  lia.
Qed.

Lemma DL1 n r: [1]^^n *> 1 >> 0 >> L6 {{D}}> 0 >> r -->> (n+9) / const 0 {{A}}> [0;1;0;1;0;1;0;0] *> [1]^^(n+2) *> r.
Proof.
  costs.
  { cstep.
    eapply ms_app. { apply (SE n (1>>0>>L6)). }
    unfold L6. do 8 cstep. cfin. }
  lia.
Qed.


(** After the left-going pass, by parity of the blocks left. *)
Lemma PO K Y: [1] *> [1;0] *> L6 {{D}}> 0 >> 0 >> [1;1;1;0]^^K *> Y -->> (22+8*K) / [1;1]^^(2*K+4) *> const 0 {{A}}> [0;1;0;0] *> Y.
Proof.
  costs.
  { eapply ms_app. { apply (DL1 1 (0 >> [1;1;1;0]^^K *> Y)). }
    do 4 cstep.
    eapply ms_app.
    { eapply ms_src; [|apply (Zk (S K) (1>>1>>1>>1>>const 0) Y)]. reflexivity. }
    cfin. }
  lia.
Qed.

Lemma PE K Y: [1] *> L6 {{D}}> 0 >> 0 >> [1;1;1;0]^^K *> Y -->> (48+8*K) / [1;1]^^(2*K) *> [1;0]^^2 *> L6 {{A}}> [0;1;0;0] *> Y.
Proof.
  costs.
  { eapply ms_app. { apply (DL0 1 (0 >> [1;1;1;0]^^K *> Y)). }
    eapply ms_app.
    { eapply ms_src; [|apply (L1 2 (1 >> 0 >> [1;1;1;0]^^K *> Y))]. reflexivity. }
    unfold LL.
    eapply ms_app.
    { eapply ms_src; [|apply (Tb' ([1;0]^^2 *> L6))]. reflexivity. }
    eapply ms_app. { apply (Zk K). }
    cfin. }
  lia.
Qed.

Lemma DLo K n r: [1]^^n *> [1;0]^^(2*K+1) *> L6 {{D}}> 0 >> r -->> (n+13+14*K) / [1;1]^^(2*K+2) *> const 0 {{A}}> [0;1;0;0] *> [1]^^(n+2) *> r.
Proof.
  destruct K as [|K].
  { costs.
    { eapply ms_app. { apply (DL1 n r). }
      generalize ([1]^^(n+2) *> r) as Y. intros Y. do 4 cstep. cfin. }
    lia. }
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (DLs n ([1;0]^^(2*K+1) *> L6) r)].
      replace (2 * S K + 1) with (S (S (2*K+1))) by lia. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (DLr K ([1;0] *> L6) ([1]^^(n+2) *> r))].
      replace (2*K+1) with (S (2*K)) by lia. cbn [lpow app Str_app]. rewrite lpow_shift2. teq. }
    eapply ms_app. { apply PO. }
    cfin. }
  lia.
Qed.

Lemma DLe K n r: [1]^^n *> [1;0]^^(2*K+2) *> L6 {{D}}> 0 >> r -->> (n+53+14*K) / [1;1]^^(2*K) *> [1;0]^^2 *> L6 {{A}}> [0;1;0;0] *> [1]^^(n+2) *> r.
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (DLs n ([1;0]^^(2*K) *> L6) r)].
      replace (2*K+2) with (S (S (2*K))) by lia. reflexivity. }
    eapply ms_app. { apply (DLr K L6 ([1]^^(n+2) *> r)). }
    eapply ms_app. { apply PE. }
    cfin. }
  lia.
Qed.

(** Configurations of the map: A(2k,b) and the tape it rests on. *)
Definition R0 : side := [0;1] *> const 0.
Definition AK k b := [1;1]^^k *> const 0 {{A}}> 1 >> [1]^^b *> R0.

(** [J]: the machine after the first pass, with nothing yet drained. *)
Lemma A2J n b: AK (S n) (b+2) -->> (4*n+19) / LL (S n) 0 {{A}}> [1]^^b *> R0.
Proof.
  unfold AK. replace (b+2) with (S (S b)) by lia.
  exact (L1 n ([1]^^b *> R0)).
Qed.

Lemma ones_split k e (x:Stream Sym): [1]^^(2*k+e) *> x = [1;1]^^k *> [1]^^e *> x.
Proof. rewrite lpow_add, Str_app_assoc, ones2. reflexivity. Qed.

Ltac cfinL := unfold L6, LL in *; cfin.
Create HintDb pn1.
#[export] Hint Rewrite <- ones2 : pn1.
Ltac cfin1 := apply ms_refl; unfold R0, L6, LL in *; solve [autorewrite with pn1 pn; repeat (reflexivity || lia || f_equal)].

(** Doubling, for every d: also the path of the halt form, with d = 0. *)
Lemma RuleD n d: AK (S n) (2*n+5+d) -->> (4*n*n+14*n+25) / AK (2*n+5) d.
Proof.
  costs.
  { replace (2*n+5+d) with (2*n+3+d+2) by lia.
    eapply ms_app. { apply A2J. }
    replace (2*n+3+d) with (2*S n + S d) by lia. rewrite ones_split.
    eapply ms_app.
    { eapply ms_src; [|apply (Drain (S n) 0 0 L6 ([1]^^(S d) *> R0))]. reflexivity. }
    unfold AK. cfinL. }
  nia.
Qed.


(** The first branch after the drain, odd [b]: [1^(4t+5)] and a left-going pass. *)
Lemma OddStart t j: AK (j+1+t) (2*t+3) -->> (4*(j+t)+19 + (4*t*t+2*t) + (8*t+4) + 9) / [1]^^(4*t+5) *> [1;0]^^j *> L6 {{D}}> 0 >> R0.
Proof.
  costs.
  { replace (j+1+t) with (S (j+t)) by lia. replace (2*t+3) with (2*t+1+2) by lia.
    eapply ms_app. { apply A2J. }
    rewrite ones_split.
    eapply ms_app.
    { eapply ms_src; [|apply (Drain t 0 (S j) L6 ([1]^^1 *> R0))]. unfold LL. teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (Tb (0+2*t) ([1;0]^^j *> L6) (1 >> const 0))]. reflexivity. }
    eapply ms_app. { apply End1. }
    cfin1. }
  nia.
Qed.

Lemma ones4 m (x:Stream Sym): [1]^^(4+m) *> x = 1 >> 1 >> 1 >> 1 >> [1]^^m *> x.
Proof. reflexivity. Qed.

Lemma RuleT t: AK (t+1) (2*t+3) -->> (4*t*t+18*t+55) / AK 3 (4*t+7).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (OddStart t 0)]. unfold AK. teq. }
    eapply ms_app. { apply (DL0 (4*t+5) R0). }
    unfold AK. cfin1. }
  nia.
Qed.

(** Covers [s] too: [t = 0] is [b = 3] with [a % 4 = 0]. *)
Lemma RuleU t K: AK (2*K+2+t) (2*t+3) -->> (4*t*t+18*t+22*K+66) / AK (2*K+6) (4*t+2).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (OddStart t (2*K+1))]. unfold AK. teq. }
    eapply ms_app. { apply (DLo K (4*t+5) R0). }
    eapply ms_app.
    { eapply ms_src; [|apply (Zs ([1;1]^^(2*K+2) *> const 0) ([1]^^(4*t+3) *> R0))].
      replace (4*t+5+2) with (4+(4*t+3)) by lia. rewrite ones4. reflexivity. }
    unfold AK. cfin1. }
  nia.
Qed.

(** The tail of the [x] branches and of [q]. *)
Lemma X2 m: [1]^^(m+7) *> [1;0]^^2 *> L6 {{D}}> 0 >> R0 -->> (m+124) / AK 11 m.
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (DLe 0 (m+7) R0)]. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (Zs ([1;1]^^(2*0) *> [1;0]^^2 *> L6) ([1]^^(m+5) *> R0))].
      replace (m+7+2) with (4+(m+5)) by lia. rewrite ones4. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (Drain 2 4 0 L6 ([1]^^(m+1) *> R0))].
      replace (m+5) with (2*2+(m+1)) by lia. rewrite ones_split. teq. }
    unfold AK. cfin1. }
  nia.
Qed.

Lemma RuleV t K: AK (2*K+4+t) (2*t+5) -->> (4*t*t+26*t+38*K+184) / AK (2*K+11) (4*t+2).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (OddStart (t+1) (2*K+2))]. unfold AK. teq. }
    eapply ms_app. { apply (DLe K (4*(t+1)+5) R0). }
    eapply ms_app.
    { eapply ms_src; [|apply (Zs ([1;1]^^(2*K) *> [1;0]^^2 *> L6) ([1]^^(4*t+7) *> R0))].
      replace (4*(t+1)+5+2) with (4+(4*t+7)) by lia. rewrite ones4. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (Drain 2 (2*K+4) 0 L6 ([1]^^(4*t+3) *> R0))].
      replace (4*t+7) with (2*2+(4*t+3)) by lia. rewrite ones_split. teq. }
    unfold AK. cfin1. }
  nia.
Qed.

Lemma RuleR K: AK (2*K+3) 3 -->> (42*K+204) / AK 3 (4*K+19).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (OddStart 0 (2*K+2))]. unfold AK. teq. }
    eapply ms_app. { apply (DLe K (4*0+5) R0). }
    eapply ms_app.
    { eapply ms_src; [|apply (Zs ([1;1]^^(2*K) *> [1;0]^^2 *> L6) ([1]^^3 *> R0))].
      reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (Ta (2*K+4) ([1;0] *> L6) (1 >> R0))].
      teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (Tb (2*K+4+2) L6 (1 >> const 0))]. reflexivity. }
    eapply ms_app. { apply End1. }
    eapply ms_app.
    { eapply ms_src; [|apply (DL0 (4*K+17) R0)]. unfold R0. autorewrite with pn1 pn. repeat (reflexivity || lia || f_equal). }
    unfold AK. cfin1. }
  nia.
Qed.

(** Even [b]. *)
Lemma EvenStart t j: AK (j+1+t) (2*t+2) -->> (4*(j+t)+19 + (4*t*t+2*t) + (4*t+13)) / 1 >> [1;0]^^j *> L6 {{D}}> 0 >> [1;0]^^(2*t+2) *> R0.
Proof.
  costs.
  { replace (j+1+t) with (S (j+t)) by lia.
    eapply ms_app. { apply A2J. }
    replace (2*t) with (2*t+0) by lia. rewrite ones_split.
    eapply ms_app.
    { eapply ms_src; [|apply (Drain t 0 (S j) L6 ([1]^^0 *> R0))]. unfold LL. teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (EndE (0+2*t) ([1;0]^^j *> L6))]. reflexivity. }
    cfin. }
  nia.
Qed.

Lemma pairs_S t (x:Stream Sym): [1;0]^^(2*t+2) *> x = 1 >> 0 >> [1;0]^^(2*t+1) *> x.
Proof. replace (2*t+2) with (S (2*t+1)) by lia. reflexivity. Qed.

(** [l A> 0 1 0 0 1 1 1 (10)^(2t+2) 0 1 0inf] runs to [l (11)^(2t+6) 1 1 1 D> ..]. *)
Lemma EvenMid t l: l {{A}}> [0;1;0;0] *> [1]^^(1+2) *> [1;0]^^(2*t+2) *> R0 -->> (12+2*(2*t+1)+9) / [1;1;1] *> [1;1]^^(2*t+1) *> [1;1]^^4 *> l {{D}}> 0 >> R0.
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (Zs l (0 >> [1;0]^^(2*t+1) *> R0))]. rewrite pairs_S. reflexivity. }
    rewrite <- rot01.
    eapply ms_app. { apply (SA (2*t+1) ([1;1]^^4 *> l) (0 >> R0)). }
    eapply ms_app. { apply End1. }
    cfin. }
  lia.
Qed.

Lemma RuleW0 n: AK (S n) (2*n+4) -->> (4*(n+1)*(n+1)+18*(n+1)+76) / AK 3 (4*n+13).
Proof.
  costs.
  { replace (2*n+4) with (2*n+2+2) by lia.
    eapply ms_app. { apply A2J. }
    replace (2*n+2) with (2*S n+0) by lia. rewrite ones_split.
    eapply ms_app.
    { eapply ms_src; [|apply (Drain (S n) 0 0 L6 ([1]^^0 *> R0))]. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (EndE0 (0+2*S n))]. reflexivity. }
    eapply ms_app. { apply (SA (0+2*S n+5)). }
    eapply ms_app. { apply End1. }
    eapply ms_app.
    { eapply ms_src; [|apply (DL0 (4*n+11) R0)]. unfold R0, L6. autorewrite with pn1 pn. repeat (reflexivity || lia || f_equal). }
    unfold AK. cfin1. }
  nia.
Qed.

Lemma RuleW K t: AK (2*K+2+t) (2*t+2) -->> (4*t*t+18*t+26*K+102) / AK 3 (4*K+4*t+13).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (EvenStart t (2*K+1))]. unfold AK. teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (DLo K 1 ([1;0]^^(2*t+2) *> R0))]. reflexivity. }
    eapply ms_app. { apply EvenMid. }
    eapply ms_app.
    { eapply ms_src; [|apply (DL0 (4*K+4*t+11) R0)]. unfold R0, L6. autorewrite with pn1 pn. repeat (reflexivity || lia || f_equal). }
    unfold AK. cfin1. }
  nia.
Qed.

Lemma RuleX K t: AK (2*K+3+t) (2*t+2) -->> (4*t*t+18*t+26*K+247) / AK 11 (4*K+4*t+6).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (EvenStart t (2*K+2))]. unfold AK. teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (DLe K 1 ([1;0]^^(2*t+2) *> R0))]. reflexivity. }
    eapply ms_app. { apply EvenMid. }
    eapply ms_app.
    { eapply ms_src; [|apply (X2 (4*K+4*t+6))]. autorewrite with pn1 pn. repeat (reflexivity || lia || f_equal). }
    cfin. }
  nia.
Qed.

Lemma RuleX0 t: AK (1+t) (2*t+2) -->> (4*t*t+18*t+221) / AK 11 (4*t+2).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (EvenStart t 0)]. unfold AK. teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (DL0 1 ([1;0]^^(2*t+2) *> R0))]. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (L1 2 (1 >> [1;0]^^(2*t+2) *> R0))]. reflexivity. }
    unfold LL.
    eapply ms_app.
    { eapply ms_src; [|apply (Ta 0 ([1;0]^^2 *> L6) (0 >> [1;0]^^(2*t+1) *> R0))].
      rewrite pairs_S. reflexivity. }
    rewrite <- rot01.
    eapply ms_app. { apply (SA (2*t+1)). }
    eapply ms_app. { apply End1. }
    eapply ms_app.
    { eapply ms_src; [|apply (X2 (4*t+2))]. autorewrite with pn1 pn. repeat (reflexivity || lia || f_equal). }
    cfin. }
  nia.
Qed.

(** [b = 1]. *)
Lemma B1start n: AK (S n) 1 -->> (4*n+26) / [1] *> [1;0]^^(S n) *> L6 {{D}}> [0;0;1] *> const 0.
Proof.
  costs.
  { unfold AK, R0. cbn [lpow app Str_app]. cstep.
    eapply ms_app. { apply (SF (S n) (const 0)). }
    cstep. cbn [lpow app Str_app]. do 11 cstep.
    rewrite rot01. cstep. cstep.
    eapply ms_app. { apply (SC n). }
    do 9 cstep. unfold L6. cfin. }
  lia.
Qed.

Lemma RuleP K: AK (2*K+1) 1 -->> (26*K+84) / AK 3 (4*K+9).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (B1start (2*K))]. unfold AK. teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (DLo K 1 ([0;1] *> const 0))].
      replace (2*K+1) with (S (2*K)) by lia. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (Zk 1 ([1;1]^^(2*K+2) *> const 0) (1 >> const 0))]. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (SA 1 ([1;1]^^(2*1) *> [1;1]^^(2*K+2) *> const 0) ([0;0;1] *> const 0))]. reflexivity. }
    eapply ms_app. { apply End1. }
    eapply ms_app.
    { eapply ms_src; [|apply (DL0 (4*K+7) R0)]. unfold R0, L6. autorewrite with pn1 pn. repeat (reflexivity || lia || f_equal). }
    unfold AK. cfin1. }
  lia.
Qed.

Lemma RuleQ K: AK (2*K+2) 1 -->> (26*K+229) / AK 11 (4*K+2).
Proof.
  costs.
  { eapply ms_app.
    { eapply ms_src; [|apply (B1start (2*K+1))]. unfold AK. teq. }
    eapply ms_app.
    { eapply ms_src; [|apply (DLe K 1 ([0;1] *> const 0))].
      replace (2*K+2) with (S (2*K+1)) by lia. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (Zk 1 ([1;1]^^(2*K) *> [1;0]^^2 *> L6) (1 >> const 0))]. reflexivity. }
    eapply ms_app.
    { eapply ms_src; [|apply (SA 1 ([1;1]^^(2*1) *> [1;1]^^(2*K) *> [1;0]^^2 *> L6) ([0;0;1] *> const 0))]. reflexivity. }
    eapply ms_app. { apply End1. }
    eapply ms_app.
    { eapply ms_src; [|apply (X2 (4*K+2))]. unfold R0. autorewrite with pn1 pn. repeat (reflexivity || lia || f_equal). }
    cfin. }
  lia.
Qed.

(** The end: [A(2n+2,0)] stops at state D reading 1. *)
Lemma HaltK n: exists ch, AK (S n) 0 -->> (4*n+18) / ch /\ halted tm ch.
Proof.
  eexists. split.
  { costs.
    { unfold AK, R0. cbn [lpow app Str_app]. cstep.
      eapply ms_app. { apply (SF (S n) (const 0)). }
      cstep. cbn [lpow app Str_app]. do 11 cstep.
      rewrite rot01. cstep. cstep.
      eapply ms_app. { apply (SC n). }
      cstep. apply multistep_0. }
    lia. }
  reflexivity.
Qed.

Lemma Init: c0 -->> 35 / AK 3 1.
Proof.
  unfold c0, tape0, AK, R0. do 35 cstep. apply ms_refl. repeat (rewrite <- const_unfold). reflexivity.
Qed.
