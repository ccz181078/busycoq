From BusyCoq Require Import Individual62 Longitudinal ES_v3 DivModCases.
Require Import ZifyNat Lia ZArith NArith List String.
From Coq Require Import QArith Lqa.
Import ListNotations.
Import List.

Lemma segRLs_phase_addmul tm h s1 s2 a a' n b b' w1 w2:
  segRLs tm (s1++h^^b) (s2++h^^b') w1 w2 ->
  segRLs tm (h^^a) (h^^a') w2 w2 ->
  segRLs tm (s1++h^^(b+n*a)) (s2++h^^(b'+n*a')) w1 w2.
Proof.
  intros H0 H1.
  do 2 rewrite lpow_add; do 2 rewrite app_assoc.
  eapply segRLs_trans; [apply H0|].
  applys_eq (segRLs_addmul_v2 a a' n 0 0); try flia.
  - constructor.
  - apply H1.
Qed.

Ltac esc := apply BoundedConfig.segRLs_c_spec with (T:=1000%nat); reflexivity.

(* Shared abstract scan; no specific machine or nonhalting assumption. *)
Module CCore.
Notation t := [S1;S1;S0;S0].
Notation d0 := [S0;S0].
Notation d1 := [S1;S0].
Notation one := [S1].
Open Scope nat.

Inductive RIncs : nat -> side -> side -> Prop :=
| RIncs_0 r : RIncs 0 r (one*>r)
| RIncs_T n r r' : RIncs ((1+n)*2) r r' ->
    RIncs (1+n) (t*>r) (t*>r')
| RIncs_pair0 n r r' : RIncs (n*2) r r' ->
    RIncs (1+n) (d1*>d0*>r) (t*>r')
| RIncs_pair1 n r r' : RIncs (1+n*2) r r' ->
    RIncs (1+n) (d1*>d1*>r) (t*>r')
| RIncs_short00 n r r' : RIncs (n*2) r r' ->
    RIncs (2+n*4) (d0*>r) (d0*>r')
| RIncs_short01 n r r' : RIncs (1+n*2) r r' ->
    RIncs (2+n*4) (d1*>r) (d0*>r')
| RIncs_short10 n r r' : RIncs (n*2) r r' ->
    RIncs (4+n*4) (d0*>r) (d1*>r')
| RIncs_short11 n r r' : RIncs (1+n*2) r r' ->
    RIncs (4+n*4) (d1*>r) (d1*>r').

Inductive Binary : nat -> nat -> side -> Prop :=
| Binary1 : Binary 1 1 (d1*>0inf)
| Binary0 n H r : Binary (1+n) H r ->
    Binary (2+n*2) (1+H) (d0*>r)
| Binary2 n H r : Binary (1+n) H r ->
    Binary (3+n*2) (1+H) (d1*>r).

Lemma Binary_bounds A H r : Binary A H r ->
  0<A /\ 0<H /\ 2^H<=A*2 /\ A<2^H.
Proof.
  intro I; induction I; cbn[Nat.add Nat.pow] in *; lia.
Qed.

Lemma Binary_ex n : exists H r, Binary (1+n) H r.
Proof.
  induction n using lt_wf_ind.
  destruct n as [|n].
  - exists 1, (d1*>0inf); constructor.
  - destruct (mod2 n); subst n;
      epose proof (H a _) as [H0 [r I]].
    + exists (1+H0), (d0*>r); constructor; apply I.
    + exists (1+H0), (d1*>r); constructor; apply I.
  Unshelve. all: lia.
Qed.

Lemma Binary_RIncs A H r : Binary A H r -> RIncs ((A-1)*2) 0inf r.
Proof.
  intro I; induction I.
  - change (RIncs 0 0inf (S1 >> S0 >> 0inf)).
    rewrite <-const_unfold; apply RIncs_0.
  - do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (RIncs_short00 n); flia.
    applys_eq IHI; flia.
  - do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (RIncs_short10 n); flia.
    applys_eq IHI; flia.
Qed.

Lemma RIncs_blank n : exists r, RIncs (n*2) 0inf r.
Proof.
  destruct (Binary_ex n) as [H [r I]].
  apply Binary_RIncs in I.
  exists r; applys_eq I; flia.
Qed.

Inductive Word := WT | W0 | W1.

(* true requires an even incoming budget; false permits either parity.
   This grammar resolves the long/short ambiguity before evaluating budgets. *)
Inductive Parse : bool -> list Word -> Prop :=
| Parse_nil e : Parse e []
| Parse_T e u : Parse true u -> Parse e (WT::u)
| Parse_short0 u : Parse true u -> Parse true (W0::u)
| Parse_short1 u : Parse false u -> Parse true (W1::u)
| Parse_pair0 e u : Parse true u -> Parse e (W1::W0::u)
| Parse_pair1 e u : Parse false u -> Parse e (W1::W1::u).

Lemma Parse_weaken u : Parse false u -> Parse true u.
Proof. intro I; inversion I; subst; eauto using Parse. Qed.

Lemma Parse_all u : Parse true u /\ (Parse false u \/ Parse false (W1::u)).
Proof.
  induction u as [|w u [I J]].
  - split; [constructor|left; constructor].
  - destruct w.
    + split; [constructor; apply I|left; constructor; apply I].
    + split; [constructor; apply I|right; apply Parse_pair0; apply I].
    + destruct J as [J|J].
      * split; [apply Parse_short1; apply J|right; apply Parse_pair1; apply J].
      * split; [apply Parse_weaken; apply J|left; apply J].
Qed.

Inductive Digits : nat -> nat -> list Word -> Prop :=
| Digits_nil : Digits 0 0 []
| Digits_zero A H u : Digits A H u -> Digits (A*2) (1+H) (W0::u)
| Digits_one A H u : Digits A H u -> Digits (1+A*2) (1+H) (W1::u).

Fixpoint has10 u :=
  match u with
  | W1::W0::_ => true
  | _::v => has10 v
  | [] => false
  end.

Fixpoint cut_ok u :=
  match u with
  | [] => true
  | [W1] => false
  | _::v => cut_ok v
  end.

Lemma cut_ok_tail w u : cut_ok (w::u)=true -> cut_ok u=true.
Proof. destruct u; [reflexivity|destruct w; cbn[cut_ok]; auto]. Qed.

Definition cut_at p q := cut_ok p=true \/ exists r, q=WT::r.

Lemma cut_at_tail w p q : cut_at (w::p) q -> cut_at p q.
Proof. intros [H|H]; [left; eapply cut_ok_tail; apply H|right; apply H]. Qed.

Lemma cut_ok_last u w : cut_ok (u++[w])=cut_ok [w].
Proof.
  induction u as [|a u IH]; [reflexivity|].
  destruct a; destruct u; cbn[app cut_ok] in *; auto.
Qed.

Lemma repeat_snoc (w : Word) n : repeat w (S n)=repeat w n++[w].
Proof. induction n; cbn[repeat app] in *; congruence. Qed.

Lemma trailing_ones u : exists p n, u=p++repeat W1 n /\ cut_ok p=true.
Proof.
  induction u using rev_ind.
  - exists (@nil Word), 0; split; reflexivity.
  - destruct IHu as [p [n [-> P]]]; destruct x.
    + exists ((p++repeat W1 n)++[WT]), 0; rewrite app_nil_r.
      split; [reflexivity|apply cut_ok_last].
    + exists ((p++repeat W1 n)++[W0]), 0; rewrite app_nil_r.
      split; [reflexivity|apply cut_ok_last].
    + exists p, (S n); rewrite repeat_snoc, app_assoc; auto.
Qed.

Fixpoint to_side ws r :=
  match ws with
  | [] => r
  | WT::u => t*>to_side u r
  | W0::u => d0*>to_side u r
  | W1::u => d1*>to_side u r
  end.

Lemma to_side_app u v r : to_side (u++v) r = to_side u (to_side v r).
Proof. induction u; [reflexivity|destruct a; cbn[to_side app]; now rewrite IHu]. Qed.

Lemma Binary_words A H r : Binary A H r ->
  exists u, Digits A H u /\ to_side u 0inf = r.
Proof.
  intro I; induction I.
  - exists [W1]; split; [exact (Digits_one 0 0 [] Digits_nil)|reflexivity].
  - destruct IHI as [u [D <-]].
    exists (W0::u); split; [|reflexivity].
    applys_eq (Digits_zero (1+n) H u); flia; apply D.
  - destruct IHI as [u [D <-]].
    exists (W1::u); split; [|reflexivity].
    applys_eq (Digits_one (1+n) H u); flia; apply D.
Qed.

Lemma Digits_ex H : forall A, A<2^H -> exists u, Digits A H u.
Proof.
  induction H as [|H IH]; intros A B.
  - assert (A=0) by (cbn[Nat.pow] in B; lia); subst A.
    exists (@nil Word); constructor.
  - destruct (mod2 A); subst A;
      assert (a<2^H) as Hn by (cbn[Nat.pow] in B; lia);
      destruct (IH a Hn) as [u I].
    + exists (W0::u); constructor; apply I.
    + exists (W1::u); constructor; apply I.
Qed.

Lemma Digits_app A H u : Digits A H u -> forall B J v,
  Digits B J v -> Digits (A+B*2^H) (H+J) (u++v).
Proof.
  intro I; induction I; intros B J v D; cbn[app Nat.add Nat.pow].
  - applys_eq D; flia.
  - applys_eq (Digits_zero (A+B*2^H) (H+J) (u++v)); flia.
    apply IHI; apply D.
  - applys_eq (Digits_one (A+B*2^H) (H+J) (u++v)); flia.
    apply IHI; apply D.
Qed.

Lemma Digits_prefix_binary A H u : Digits A H u -> forall B J r,
  Binary B J r -> Binary (A+B*2^H) (H+J) (to_side u r).
Proof.
  intro I; induction I; intros B J r D; cbn[to_side Nat.add Nat.pow].
  - applys_eq D; flia.
  - specialize (IHI _ _ _ D).
    pose proof (Binary_bounds _ _ _ IHI).
    applys_eq (Binary0 (A+B*2^H-1) (H+J) (to_side u r)); flia.
    applys_eq IHI; flia.
  - specialize (IHI _ _ _ D).
    pose proof (Binary_bounds _ _ _ IHI).
    applys_eq (Binary2 (A+B*2^H-1) (H+J) (to_side u r)); flia.
    applys_eq IHI; flia.
Qed.

Lemma Binary_high : Binary 191 8 (to_side (repeat W1 6++[W0;W1]) 0inf).
Proof.
  apply (Binary2 94); apply (Binary2 46); apply (Binary2 22);
    apply (Binary2 10); apply (Binary2 4); apply (Binary2 1);
    apply (Binary0 0); apply Binary1.
Qed.

Lemma Digits_ones n : Digits (2^n-1) n (repeat W1 n).
Proof.
  induction n; [constructor|].
  pose proof (Nat.pow_nonzero 2 n).
  applys_eq (Digits_one (2^n-1) n (repeat W1 n)); try (cbn[Nat.pow]; flia).
  apply IHn.
Qed.

Definition low00 ds := exists v, ds=W0::W0::v.
Definition high6 ds := exists v, ds=v++repeat W1 6.
Definition low1 ds := exists w, ds=W1::(repeat W0 6++w).
Definition high15 ds := exists w, ds=w++repeat W1 15.

Lemma Digits_zeroes n : Digits 0 n (repeat W0 n).
Proof. induction n; [constructor|applys_eq (Digits_zero 0 n (repeat W0 n)); flia; apply IHn]. Qed.

Lemma Binary_ones n : Binary (2^(S n)-1) (S n) (to_side (repeat W1 (S n)) 0inf).
Proof.
  rewrite repeat_snoc, to_side_app; cbn[to_side].
  pose proof (Nat.pow_nonzero 2 n).
  applys_eq (Digits_prefix_binary _ _ _ (Digits_ones n) _ _ _ Binary1);
    cbn[Nat.pow]; flia.
Qed.

Lemma C24_tail_window r k : 32767*2^r<=k -> k<32768*2^r ->
  exists ds, Digits (1+k*128) (22+r) ds /\ low1 ds /\ high15 ds /\
    Binary (1+k*128) (22+r) (to_side ds 0inf).
Proof.
  intros L U; set (a:=k-32767*2^r).
  assert (A : a+32767*2^r=k) by (unfold a; lia).
  change (k<(32767+1)*2^r) in U.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l in U.
  destruct (Digits_ex r a) as [v D]; [unfold a; lia|].
  assert (Low : Digits 1 7 (W1::repeat W0 6)).
  { applys_eq (Digits_one 0 6 (repeat W0 6)); flia; apply Digits_zeroes. }
  assert (High : Digits k (r+15) (v++repeat W1 15)).
  { rewrite <-A; apply Digits_app; [apply D|exact (Digits_ones 15)]. }
  assert (HighB : Binary k (r+15) (to_side (v++repeat W1 15) 0inf)).
  { rewrite to_side_app, <-A; apply Digits_prefix_binary; [apply D|exact (Binary_ones 14)]. }
  exists ((W1::repeat W0 6)++(v++repeat W1 15)); split.
  - applys_eq (Digits_app _ _ _ Low _ _ _ High); flia.
  - split; [eexists; reflexivity|].
    split; [exists ((W1::repeat W0 6)++v); rewrite app_assoc; reflexivity|].
    rewrite to_side_app.
    applys_eq (Digits_prefix_binary _ _ _ Low _ _ _ HighB); flia.
Qed.

Lemma tail_from_window r k : 191*2^r<=k*2 -> k*2<192*2^r ->
  exists ds, Digits (k*8-512*2^r) (8+r) ds /\ low00 ds /\ high6 ds /\
    Binary (k*8) (10+r) (to_side ds (d0*>d1*>0inf)).
Proof.
  intros L U; set (a:=k*2-191*2^r).
  assert (A : a+191*2^r=k*2) by (unfold a; lia).
  destruct (Digits_ex r a) as [v D]; [unfold a; lia|].
  exists (W0::W0::(v++repeat W1 6)); split.
  - applys_eq (Digits_zero ((a+63*2^r)*2) (7+r) (W0::(v++repeat W1 6))); try flia.
    applys_eq (Digits_zero (a+63*2^r) (r+6) (v++repeat W1 6)); try flia.
    apply Digits_app; [apply D|exact (Digits_ones 6)].
  - split; [eexists; reflexivity|].
    split; [exists (W0::W0::v); reflexivity|].
    cbn[to_side]; rewrite to_side_app.
    assert (B : Binary (a+191*2^r) (r+8)
      (to_side v (to_side (repeat W1 6++[W0;W1]) 0inf))).
    { apply Digits_prefix_binary; [apply D|apply Binary_high]. }
    rewrite to_side_app in B; cbn[to_side] in B.
    applys_eq (Binary0 (2*(a+191*2^r)-1) (9+r)); try flia.
    applys_eq (Binary0 (a+191*2^r-1) (r+8)); try flia.
    applys_eq B; flia.
Qed.

Lemma pow_three n : 2^(3*n)=8^n.
Proof.
  induction n; [reflexivity|].
  replace (3*S n) with (3+3*n) by lia.
  rewrite Nat.pow_add_r, IHn; reflexivity.
Qed.

Lemma c6_powers n :
  2^(10+3*n)=256*2^(2+3*n) /\ 8^(3+n)=128*2^(2+3*n).
Proof.
  split.
  - change (2^(8+(2+3*n))=256*2^(2+3*n)).
    rewrite Nat.pow_add_r; reflexivity.
  - rewrite (Nat.pow_add_r 8 3 n), (Nat.pow_add_r 2 2 (3*n)), pow_three.
    cbn[Nat.pow]; lia.
Qed.

Section Quantitative.
Local Open Scope Q_scope.

Fixpoint mass u : QArith_base.Q :=
  match u with
  | [] => 0
  | WT::v => mass v*(1#2)
  | _::v => 1+mass v*2
  end.

Fixpoint zeros u : QArith_base.Q :=
  match u with
  | [] => 0
  | WT::v => zeros v*(1#2)
  | W0::v => 1+zeros v*2
  | W1::v => zeros v*2
  end.

Fixpoint ones u : QArith_base.Q :=
  match u with
  | [] => 0
  | WT::v => ones v*(1#2)
  | W0::v => ones v*2
  | W1::v => 1+ones v*2
  end.

Fixpoint scale u : QArith_base.Q :=
  match u with
  | [] => 1
  | WT::v => scale v*(1#2)
  | _::v => scale v*2
  end.

Lemma weights_nonneg u : 0<=mass u /\ 0<=zeros u /\ 0<=ones u.
Proof.
  induction u; [cbn[mass zeros ones]; lra|destruct a; cbn[mass zeros ones]; lra].
Qed.

Lemma mass_split u : mass u == zeros u+ones u.
Proof. induction u; [reflexivity|destruct a; cbn[mass zeros ones]; rewrite IHu; ring]. Qed.

Lemma scale_pos u : 0<scale u.
Proof. induction u; [cbn[scale]; lra|destruct a; cbn[scale]; lra]. Qed.

Lemma mass_app u v : mass (u++v) == mass u+scale u*mass v.
Proof. induction u; [cbn[mass scale app]; ring|destruct a; cbn[mass scale app]; rewrite IHu; ring]. Qed.

Lemma zeros_app u v : zeros (u++v) == zeros u+scale u*zeros v.
Proof. induction u; [cbn[zeros scale app]; ring|destruct a; cbn[zeros scale app]; rewrite IHu; ring]. Qed.

Lemma scale_app u v : scale (u++v) == scale u*scale v.
Proof. induction u; [cbn[scale app]; ring|destruct a; cbn[scale app]; rewrite IHu; ring]. Qed.

Inductive Scan : nat -> list Word -> nat -> list Word -> QArith_base.Q -> Prop :=
| Scan_nil k : Scan k [] k [] 0
| Scan_T n u k v l : Scan ((1+n)*2)%nat u k v l ->
    Scan (1+n)%nat (WT::u) k (WT::v) (l*(1#2))
| Scan_pair0 n u k v l : Scan (n*2)%nat u k v l ->
    Scan (1+n)%nat (W1::W0::u) k (WT::v) ((1+l)*(1#2))
| Scan_pair1 n u k v l : Scan (1+n*2)%nat u k v l ->
    Scan (1+n)%nat (W1::W1::u) k (WT::v) ((1#4)+l*(1#2))
| Scan_short00 n u k v l : Scan (n*2)%nat u k v l ->
    Scan (2+n*4)%nat (W0::u) k (W0::v) (1+l*2)
| Scan_short01 n u k v l : Scan (1+n*2)%nat u k v l ->
    Scan (2+n*4)%nat (W1::u) k (W0::v) (l*2)
| Scan_short10 n u k v l : Scan (n*2)%nat u k v l ->
    Scan (4+n*4)%nat (W0::u) k (W1::v) (1+l*2)
| Scan_short11 n u k v l : Scan (1+n*2)%nat u k v l ->
    Scan (4+n*4)%nat (W1::u) k (W1::v) (l*2).

Lemma Scan_spec a u b v l : Scan a u b v l -> forall r r',
  RIncs b r r' -> RIncs a (to_side u r) (to_side v r').
Proof.
  intro I; induction I; intros; cbn[to_side];
    eauto using RIncs_T, RIncs_pair0, RIncs_pair1,
      RIncs_short00, RIncs_short01, RIncs_short10, RIncs_short11.
Qed.

Lemma Scan_bounds a u b v l : Scan a u b v l ->
  0<=l /\ mass v<=mass u /\ mass v+l<=mass u+zeros u.
Proof.
  intro I; induction I; cbn[mass zeros] in *; try lra;
    pose proof (weights_nonneg v); lra.
Qed.

Definition qnat n := inject_Z (Z.of_nat n).

Lemma qnat_add a b : qnat (a+b)%nat == qnat a+qnat b.
Proof. unfold qnat; rewrite Nat2Z.inj_add, inject_Z_plus; reflexivity. Qed.

Lemma qnat_mul a b : qnat (a*b)%nat == qnat a*qnat b.
Proof. unfold qnat; rewrite Nat2Z.inj_mul, inject_Z_mult; reflexivity. Qed.

Lemma qnat_S n : qnat (S n) == 1+qnat n.
Proof. change (qnat (1+n)%nat == 1+qnat n); rewrite qnat_add; reflexivity. Qed.

Lemma qnat_nonneg n : 0<=qnat n.
Proof. unfold qnat; change (inject_Z 0<=inject_Z (Z.of_nat n)); rewrite <-Zle_Qle; lia. Qed.

Lemma qnat_pos n : (0<n)%nat <-> 0<qnat n.
Proof. unfold qnat; change ((0<n)%nat <-> inject_Z 0<inject_Z (Z.of_nat n)); rewrite <-Zlt_Qlt; lia. Qed.

Lemma qnat_le a b : (a<=b)%nat <-> qnat a<=qnat b.
Proof. unfold qnat; rewrite <-Zle_Qle; lia. Qed.

Lemma qnat_lt a b : (a<b)%nat <-> qnat a<qnat b.
Proof. unfold qnat; rewrite <-Zlt_Qlt; lia. Qed.

Ltac qnorm :=
  repeat (rewrite qnat_add in * || rewrite qnat_mul in * || rewrite qnat_S in *);
  change (qnat 0%nat) with (0%Q) in *;
  change (qnat 1%nat) with (1%Q) in *;
  change (qnat 2%nat) with (2%Q) in *;
  change (qnat 4%nat) with (4%Q) in *.

Lemma Scan_budget a u b v l : Scan a u b v l ->
  qnat a == qnat b*scale v+(ones v+l)*2.
Proof.
  intro I; induction I; cbn[ones scale] in *;
    qnorm; nra.
Qed.

Lemma Scan_ex_mode e u (I : Parse e u) : forall k,
  (e=true -> exists n, k=(n*2)%nat) ->
  (mass u+zeros u)*2<qnat k ->
  exists b v l, Scan k u b v l /\ (0<b)%nat.
Proof.
  induction I; intros k Ek Hk.
  - exists k, (@nil Word), (0%Q); split; [constructor|apply qnat_pos; cbn[mass zeros] in Hk; lra].
  - pose proof (weights_nonneg u) as H0.
    destruct k as [|k]; [cbn[mass zeros] in Hk; qnorm; nra|].
    edestruct (IHI ((1+k)*2)%nat) as [b [v [l [H B]]]].
    + intro; eexists; reflexivity.
    + cbn[mass zeros] in Hk; qnorm; nra.
    + eauto 8 using Scan_T.
  - pose proof (weights_nonneg u) as H0.
    destruct (Ek eq_refl) as [n ->].
    destruct (mod2 n); subst n.
    + destruct a as [|a]; [cbn[mass zeros] in Hk; qnorm; nra|].
      edestruct (IHI (a*2)%nat) as [b [v [l [H B]]]].
      * intro; eexists; reflexivity.
      * cbn[mass zeros] in Hk; qnorm; nra.
      * exists b, (W1::v), (1+l*2); split; [|apply B].
        applys_eq (Scan_short10 a); flia; apply H.
    + edestruct (IHI (a*2)%nat) as [b [v [l [H B]]]].
      * intro; eexists; reflexivity.
      * cbn[mass zeros] in Hk; qnorm; nra.
      * exists b, (W0::v), (1+l*2); split; [|apply B].
        applys_eq (Scan_short00 a); flia; apply H.
  - pose proof (weights_nonneg u) as H0.
    destruct (Ek eq_refl) as [n ->].
    destruct (mod2 n); subst n.
    + destruct a as [|a]; [cbn[mass zeros] in Hk; qnorm; nra|].
      edestruct (IHI (1+a*2)%nat) as [b [v [l [H B]]]].
      * discriminate.
      * cbn[mass zeros] in Hk; qnorm; nra.
      * exists b, (W1::v), (l*2); split; [|apply B].
        applys_eq (Scan_short11 a); flia; apply H.
    + edestruct (IHI (1+a*2)%nat) as [b [v [l [H B]]]].
      * discriminate.
      * cbn[mass zeros] in Hk; qnorm; nra.
      * exists b, (W0::v), (l*2); split; [|apply B].
        applys_eq (Scan_short01 a); flia; apply H.
  - pose proof (weights_nonneg u) as H0.
    destruct k as [|k]; [cbn[mass zeros] in Hk; qnorm; nra|].
    edestruct (IHI (k*2)%nat) as [b [v [l [H B]]]].
    + intro; eexists; reflexivity.
    + cbn[mass zeros] in Hk; qnorm; nra.
    + eauto 8 using Scan_pair0.
  - pose proof (weights_nonneg u) as H0.
    destruct k as [|k]; [cbn[mass zeros] in Hk; qnorm; nra|].
    edestruct (IHI (1+k*2)%nat) as [b [v [l [H B]]]].
    + discriminate.
    + cbn[mass zeros] in Hk; qnorm; nra.
    + eauto 8 using Scan_pair1.
Qed.

Lemma Scan_ex u k : (mass u+zeros u)*2<qnat (k*2)%nat ->
  exists b v l, Scan (k*2)%nat u b v l /\ (0<b)%nat.
Proof.
  intro H; eapply Scan_ex_mode; [apply (proj1 (Parse_all u))| |apply H].
  intro; eexists; reflexivity.
Qed.

Lemma Digits_weights A H u : Digits A H u ->
  scale u == qnat (2^H)%nat /\ mass u+1 == qnat (2^H)%nat /\
  ones u == qnat A.
Proof.
  intro I; induction I; cbn[scale mass ones Nat.add Nat.pow] in *; qnorm; nra.
Qed.

Lemma Digits_zeros A H u : Digits A H u ->
  zeros u+qnat A+1 == qnat (2^H)%nat.
Proof. intro I; pose proof (Digits_weights _ _ _ I); pose proof (mass_split u); nra. Qed.

Lemma Scan_scale a u b v l : Scan a u b v l -> scale v<=scale u.
Proof.
  intro I; induction I; cbn[scale] in *; try lra; pose proof (scale_pos u); lra.
Qed.

Lemma Scan_gain10 a u b v l : Scan a u b v l ->
  has10 u=true -> scale v*8<=scale u.
Proof.
  intro I; induction I; intro E.
  - discriminate.
  - cbn[has10 scale] in *; specialize (IHI E); lra.
  - pose proof (Scan_scale _ _ _ _ _ I); cbn[scale]; lra.
  - pose proof (Scan_scale _ _ _ _ _ I); cbn[scale]; lra.
  - cbn[has10 scale] in *; specialize (IHI E); lra.
  - destruct u as [|w u]; [discriminate|destruct w]; cbn[has10 scale] in *;
      try (specialize (IHI E); lra); inversion I; lia.
  - cbn[has10 scale] in *; specialize (IHI E); lra.
  - destruct u as [|w u]; [discriminate|destruct w]; cbn[has10 scale] in *;
      try (specialize (IHI E); lra); inversion I; lia.
Qed.

Lemma Scan_app a u b v l : Scan a u b v l -> forall w c x m,
  Scan b w c x m -> exists p,
  Scan a (u++w) c (v++x) p /\ p == l+scale v*m.
Proof.
  intro I; induction I; intros w c x m J; cbn[app scale].
  { exists m; split; [apply J|ring]. }
  all: destruct (IHI _ _ _ _ J) as [p [K E]];
    eexists; split; [eauto using Scan_T, Scan_pair0, Scan_pair1,
      Scan_short00, Scan_short01, Scan_short10, Scan_short11|nra].
Qed.

Lemma Scan_cut a u c z l : Scan a u c z l -> forall p q,
  u=p++q -> cut_at p q ->
  exists b v w x y, Scan a p b v x /\ Scan b q c w y /\
    z=v++w /\ l == x+scale v*y.
Proof.
  intro I; induction I; intros p q E P; destruct p as [|s p].
  all: try (cbn[app] in E; subst q;
    eexists _, (@nil Word), _, (0%Q), _;
    split; [constructor|]; split; [eauto using Scan|];
    split; [reflexivity|cbn[scale]; ring]).
  - discriminate.
  - injection E as Es E; subst s; apply cut_at_tail in P.
    destruct (IHI _ _ E P) as [b [v0 [w [x [y [J [K [-> L]]]]]]]].
    eexists _, (WT::v0), w, _, y;
      split; [eauto using Scan_T|]; split; [apply K|];
      split; [reflexivity|cbn[scale]; nra].
  - injection E as Es E; subst s; destruct p as [|s p].
    { cbn[app] in E; subst q; destruct P as [P|[r P]]; discriminate. }
    injection E as Es E; subst s; do 2 apply cut_at_tail in P.
    destruct (IHI _ _ E P) as [b [v0 [w [x [y [J [K [-> L]]]]]]]].
    eexists _, (WT::v0), w, _, y;
      split; [eauto using Scan_pair0|]; split; [apply K|];
      split; [reflexivity|cbn[scale]; nra].
  - injection E as Es E; subst s; destruct p as [|s p].
    { cbn[app] in E; subst q; destruct P as [P|[r P]]; discriminate. }
    injection E as Es E; subst s; do 2 apply cut_at_tail in P.
    destruct (IHI _ _ E P) as [b [v0 [w [x [y [J [K [-> L]]]]]]]].
    eexists _, (WT::v0), w, _, y;
      split; [eauto using Scan_pair1|]; split; [apply K|];
      split; [reflexivity|cbn[scale]; nra].
  - injection E as Es E; subst s; apply cut_at_tail in P.
    destruct (IHI _ _ E P) as [b [v0 [w [x [y [J [K [-> L]]]]]]]].
    eexists _, (W0::v0), w, _, y;
      split; [eauto using Scan_short00|]; split; [apply K|];
      split; [reflexivity|cbn[scale]; nra].
  - injection E as Es E; subst s; apply cut_at_tail in P.
    destruct (IHI _ _ E P) as [b [v0 [w [x [y [J [K [-> L]]]]]]]].
    eexists _, (W0::v0), w, _, y;
      split; [eauto using Scan_short01|]; split; [apply K|];
      split; [reflexivity|cbn[scale]; nra].
  - injection E as Es E; subst s; apply cut_at_tail in P.
    destruct (IHI _ _ E P) as [b [v0 [w [x [y [J [K [-> L]]]]]]]].
    eexists _, (W1::v0), w, _, y;
      split; [eauto using Scan_short10|]; split; [apply K|];
      split; [reflexivity|cbn[scale]; nra].
  - injection E as Es E; subst s; apply cut_at_tail in P.
    destruct (IHI _ _ E P) as [b [v0 [w [x [y [J [K [-> L]]]]]]]].
    eexists _, (W1::v0), w, _, y;
      split; [eauto using Scan_short11|]; split; [apply K|];
      split; [reflexivity|cbn[scale]; nra].
Qed.

Lemma Scan_gain_power a u b v l : Scan a u b v l ->
  exists g, scale u == scale v*qnat (8^g)%nat.
Proof.
  intro I; induction I.
  { exists 0%nat; cbn[scale Nat.pow]; qnorm; ring. }
  all: destruct IHI as [g E].
  all: try (exists g; cbn[scale]; rewrite E; ring).
  all: exists (1+g)%nat; cbn[scale Nat.add Nat.pow]; qnorm; rewrite E; ring.
Qed.

Lemma Scan_loss_pos a u b v l : Scan a u b v l -> has10 u=true -> 0<l.
Proof.
  intro I; induction I; intro E.
  - discriminate.
  - cbn[has10] in E; specialize (IHI E); lra.
  - pose proof (Scan_bounds _ _ _ _ _ I); lra.
  - pose proof (Scan_bounds _ _ _ _ _ I); lra.
  - pose proof (Scan_bounds _ _ _ _ _ I); lra.
  - destruct u as [|w u]; [discriminate|destruct w]; cbn[has10] in *;
      try (specialize (IHI E); lra); inversion I; lia.
  - pose proof (Scan_bounds _ _ _ _ _ I); lra.
  - destruct u as [|w u]; [discriminate|destruct w]; cbn[has10] in *;
      try (specialize (IHI E); lra); inversion I; lia.
Qed.

Lemma Scan_odd_zero n u b v l : ~Scan (1+n*2)%nat (W0::u) b v l.
Proof. intro I; inversion I; lia. Qed.

Lemma Scan_odd_even_ones r : forall n b v l,
  ~Scan (1+n*2)%nat (repeat W1 (r*2)%nat++[W0]) b v l.
Proof.
  induction r; intros n b v l I; cbn[Nat.mul Nat.add repeat app] in I.
  - eapply Scan_odd_zero; apply I.
  - inversion I; subst; try lia; eapply IHr; eassumption.
Qed.

Lemma Scan_ones_odd r : forall a b v l,
  Scan a (repeat W1 (1+r*2)%nat++[W0]) b v l ->
  v=repeat WT (1+r)%nat /\ b=((a-1)*2^(1+r))%nat /\ l==(1#2).
Proof.
  induction r; intros a b v l I; cbn[Nat.mul Nat.add repeat app] in I.
  - inversion I; subst;
      try solve [exfalso; eapply Scan_odd_zero; eassumption].
    match goal with J: Scan _ [] _ _ _ |- _ => inversion J; subst end.
    cbn[repeat Nat.add Nat.sub Nat.pow]; split; [reflexivity|split; [lia|ring]].
  - inversion I; subst;
      try solve [exfalso; eapply (Scan_odd_even_ones (1+r)%nat); eassumption].
    match goal with J: Scan _ _ _ _ _ |- _ =>
      destruct (IHr _ _ _ _ J) as [-> [B L]] end.
    cbn[Nat.add Nat.sub Nat.pow] in B.
    cbn[repeat Nat.add Nat.sub Nat.pow]; split; [reflexivity|split; [nia|lra]].
Qed.

Lemma Scan_ones_even r a b v l :
  Scan a (repeat W1 (2+r*2)%nat++[W0]) b v l ->
  exists d n, v=d::repeat WT (1+r)%nat /\
    b=(n*2^(2+r))%nat /\ l==1.
Proof.
  intro I; cbn[Nat.add repeat app] in I; inversion I; subst;
    try solve [exfalso; eapply (Scan_odd_even_ones r); eassumption].
  all: match goal with J: Scan (1+?n*2)%nat _ _ _ _ |- _ =>
    destruct (Scan_ones_odd r _ _ _ _ J) as [-> [B L]];
    eexists _, n end.
  all: split; [reflexivity|split; [cbn[Nat.add Nat.sub Nat.pow] in *; nia|lra]].
Qed.

Lemma repeat_three_tail r :
  repeat WT (3+r)%nat = repeat WT r++[WT;WT;WT].
Proof.
  change (repeat WT (3+r)%nat = repeat WT r++repeat WT 3).
  rewrite <-repeat_app; f_equal; lia.
Qed.

Lemma Scan_ones_six n a b v l :
  Scan a (repeat W1 (6+n)%nat++[W0]) b v l ->
  exists w k, v=w++[WT;WT;WT] /\ b=(k*8)%nat.
Proof.
  intro I; destruct (mod2 n); subst n.
  - assert (6+a0*2=2+(2+a0)*2)%nat as E by lia; rewrite E in I.
    destruct (Scan_ones_even (2+a0)%nat _ _ _ _ I) as [d [k [-> [B L]]]].
    exists (d::repeat WT a0), (k*2^(1+a0))%nat; split.
    + change (d::repeat WT (3+a0)%nat=(d::repeat WT a0)++[WT;WT;WT]).
      rewrite repeat_three_tail; reflexivity.
    + cbn[Nat.add Nat.pow] in *; nia.
  - assert (6+(1+a0*2)=1+(3+a0)*2)%nat as E by lia; rewrite E in I.
    destruct (Scan_ones_odd (3+a0)%nat _ _ _ _ I) as [-> [B L]].
    exists (repeat WT (1+a0)%nat), ((a-1)*2^(1+a0))%nat; split.
    + change (repeat WT (3+(1+a0))%nat=repeat WT (1+a0)%nat++[WT;WT;WT]).
      apply repeat_three_tail.
    + cbn[Nat.add Nat.pow] in *; nia.
Qed.

Lemma Scan_repeat_T n : forall a b v l,
  Scan a (repeat WT n) b v l ->
  v=repeat WT n /\ b=(a*2^n)%nat /\ l==0.
Proof.
  induction n; intros a b v l I; inversion I; subst.
  - cbn[repeat Nat.pow]; split; [reflexivity|split; [lia|reflexivity]].
  - match goal with J: Scan _ _ _ _ _ |- _ =>
      destruct (IHn _ _ _ _ J) as [-> [B L]] end.
    cbn[repeat Nat.pow]; split; [reflexivity|split; [nia|lra]].
Qed.

Lemma Scan_T3_end a u b v l : Scan a (u++[WT;WT;WT]) b v l ->
  exists w k, v=w++[WT;WT;WT] /\ b=(k*8)%nat.
Proof.
  intro I.
  destruct (Scan_cut _ _ _ _ _ I u [WT;WT;WT] eq_refl)
    as [c [x [y [s [t [J [K [-> E]]]]]]]]; [right; eauto|].
  destruct (Scan_repeat_T 3 _ _ _ _ K) as [-> [B L]].
  exists x, c; auto.
Qed.

Lemma Scan_six_end a u b v l :
  Scan a (u++repeat W1 6++[W0]) b v l ->
  exists w k, v=w++[WT;WT;WT] /\ b=(k*8)%nat.
Proof.
  intro I; destruct (trailing_ones u) as [p [n [-> P]]].
  assert (E : (p++repeat W1 n)++repeat W1 6++[W0] =
    p++(repeat W1 (6+n)%nat++[W0])).
  { replace (6+n)%nat with (n+6)%nat by lia.
    rewrite repeat_app; repeat rewrite app_assoc; reflexivity. }
  rewrite E in I.
  destruct (Scan_cut _ _ _ _ _ I p (repeat W1 (6+n)%nat++[W0]) eq_refl)
    as [c [x [y [s [t [J [K [-> L]]]]]]]]; [left; apply P|].
  destruct (Scan_ones_six n _ _ _ _ K) as [w [k [-> B]]].
  exists (x++w), k; rewrite app_assoc; auto.
Qed.

Lemma has10_app u v : has10 v=true -> has10 (u++v)=true.
Proof.
  induction u as [|w u IH]; [auto|].
  destruct w; cbn[app has10]; auto.
  destruct u as [|w u]; [destruct v as [|w v]; [discriminate|destruct w]; cbn[has10]; auto|].
  destruct w; cbn[app has10] in *; auto.
Qed.

Lemma Scan_low00 n u b v l : Scan (n*8)%nat (W0::W0::u) b v l ->
  has10 v=true.
Proof.
  intro I; inversion I; subst; try lia.
  match goal with J: Scan _ (W0::_) _ _ _ |- _ => inversion J; subst end;
    cbn[has10]; try reflexivity; lia.
Qed.

(* A binary word followed by its explicit terminating zero. The index is the
   zero weight of the binary word, excluding that terminating zero. *)
Inductive TailDigits : list Word -> QArith_base.Q -> Prop :=
| Tail_end : TailDigits [W0] 0
| Tail_zero u z : TailDigits u z -> TailDigits (W0::u) (1+z*2)
| Tail_one u z : TailDigits u z -> TailDigits (W1::u) (z*2).

Lemma Tail_nonneg u z : TailDigits u z -> 0<=z.
Proof. intro I; induction I; lra. Qed.

Lemma Tail_zero_inv u z : TailDigits (W0::u) z ->
  (u=[] /\ z=0) \/ exists y, TailDigits u y /\ z=1+y*2.
Proof. intro I; inversion I; subst; eauto. Qed.

Lemma Tail_one_inv u z : TailDigits (W1::u) z ->
  exists y, TailDigits u y /\ z=y*2.
Proof. intro I; inversion I; subst; eauto. Qed.

Lemma Digits_tail A H u : Digits A H u -> TailDigits (u++[W0]) (zeros u).
Proof. intro I; induction I; cbn[app zeros]; constructor; assumption. Qed.

Lemma Scan_tail_bounds a u b v l : Scan a u b v l -> forall z,
  TailDigits u z ->
  mass v<=1+z*2 /\ l<=1+z*2 /\
  (forall n, a=(1+n*2)%nat -> mass v<=z*2 /\ l<=(1#2)+z*2).
Proof.
  intro I; induction I; intros z Z.
  - inversion Z.
  - inversion Z.
  - destruct (Tail_one_inv _ _ Z) as [y [J ->]].
    destruct (Tail_zero_inv _ _ J) as [[-> ->]|[x [J' ->]]].
    + inversion I; subst; cbn[mass]; repeat split; try lra; intros; split; lra.
    + destruct (IHI _ J') as [M [L O]]; pose proof (Tail_nonneg _ _ J').
      cbn[mass]; repeat split; try lra; intros; split; lra.
  - destruct (Tail_one_inv _ _ Z) as [y [J ->]].
    destruct (Tail_one_inv _ _ J) as [x [J' ->]].
    destruct (IHI _ J') as [_ [_ O]]; specialize (O n eq_refl).
    pose proof (Tail_nonneg _ _ J').
    cbn[mass]; repeat split; try lra; intros; split; lra.
  - destruct (Tail_zero_inv _ _ Z) as [[-> ->]|[x [J ->]]].
    + inversion I; subst; cbn[mass]; repeat split; try lra; intros; lia.
    + destruct (IHI _ J) as [M [L O]].
      cbn[mass]; repeat split; try lra; intros; lia.
  - destruct (Tail_one_inv _ _ Z) as [x [J ->]].
    destruct (IHI _ J) as [_ [_ O]]; specialize (O n eq_refl).
    cbn[mass]; repeat split; try lra; intros; lia.
  - destruct (Tail_zero_inv _ _ Z) as [[-> ->]|[x [J ->]]].
    + inversion I; subst; cbn[mass]; repeat split; try lra; intros; lia.
    + destruct (IHI _ J) as [M [L O]].
      cbn[mass]; repeat split; try lra; intros; lia.
  - destruct (Tail_one_inv _ _ Z) as [x [J ->]].
    destruct (IHI _ J) as [_ [_ O]]; specialize (O n eq_refl).
    cbn[mass]; repeat split; try lra; intros; lia.
Qed.

Lemma Scan_tail_discount a u b v l c ds w m z :
  Scan a u b v l -> has10 u=true ->
  Scan b ds c w m -> TailDigits ds z -> 3<=z ->
  scale v*mass w <= (7#24)*(scale u*z) /\
  scale v*m <= (7#24)*(scale u*z).
Proof.
  intros I E J D Z.
  pose proof (Scan_gain10 _ _ _ _ _ I E).
  pose proof (Scan_tail_bounds _ _ _ _ _ J _ D).
  pose proof (scale_pos v).
  assert (scale v*(1+z*2) <= (7#24)*(scale u*z)) by nra.
  nra.
Qed.

Lemma C6_stage_bounds a u b v l c ds w m z :
  Scan a u b v l -> has10 u=true ->
  Scan b ds c w m -> TailDigits ds z -> 3<=z ->
  mass (v++w) <= mass u+(7#24)*(scale u*z) /\
  mass (v++w)+l+scale v*m <= mass u+zeros u+(7#12)*(scale u*z).
Proof.
  intros I E J D Z.
  pose proof (Scan_bounds _ _ _ _ _ I).
  pose proof (Scan_tail_discount _ _ _ _ _ _ _ _ _ _ I E J D Z).
  rewrite mass_app; lra.
Qed.

Lemma Scan_right_return a u b v l : Scan a u b v l -> (0<b)%nat ->
  exists H r, Binary b H r /\
    RIncs a (to_side u (d1*>0inf)) (to_side v (t*>r)).
Proof.
  intros I B; destruct b as [|n]; [lia|].
  destruct (Binary_ex n) as [H [r D]].
  exists H, r; split; [apply D|].
  eapply Scan_spec; [apply I|].
  do 2 rewrite (const_unfold _ S0) at 1.
  apply RIncs_pair0; applys_eq (Binary_RIncs _ _ _ D); flia.
Qed.

Lemma C6_return u A H ds : Digits A H ds ->
  scale u*qnat (2^H)%nat == (1#2) ->
  mass u*2+zeros u+scale u*zeros ds <= (1#64) ->
  exists b v l J r,
    Scan 6 (u++ds++[W0]) b v l /\ Binary b J r /\
    RIncs 6 (to_side (u++ds) (d0*>d1*>0inf)) (to_side v (t*>r)).
Proof.
  intros D E F.
  destruct (Digits_weights _ _ _ D) as [S [M O]].
  pose proof (weights_nonneg u) as [U _].
  pose proof (scale_pos u) as P.
  edestruct (Scan_ex (u++ds++[W0]) 3%nat) as [b [v [l [I B]]]].
  - repeat rewrite mass_app; repeat rewrite zeros_app; cbn[mass zeros scale].
    rewrite S, <-M; rewrite <-M in E; qnorm; nra.
  - destruct (Scan_right_return _ _ _ _ _ I B) as [J [r [R K]]].
    exists b, v, l, J, r; split; [apply I|split; [apply R|]].
    repeat rewrite to_side_app in *; cbn[to_side] in K; apply K.
Qed.

Definition ends_T3 u := exists p, u=p++[WT;WT;WT].

Lemma has10_extend u v : has10 u=true -> has10 (u++v)=true.
Proof.
  induction u as [|w u IH]; [discriminate|].
  destruct w; cbn[app has10]; auto.
  destruct u as [|w u]; [discriminate|destruct w]; cbn[app has10] in *; auto.
Qed.

Lemma C6_scan u A H ds : Digits A H ds ->
  scale u*qnat (2^H)%nat == (1#2) ->
  mass u*2+zeros u+scale u*zeros ds <= (1#64) ->
  ends_T3 u -> has10 u=true -> low00 ds -> high6 ds ->
  exists k v l g,
    Scan 6 (u++ds++[W0]) (k*8)%nat v l /\
    ends_T3 v /\ has10 v=true /\
    scale v*qnat (8^g)%nat == 1 /\
    mass v <= mass u+(7#24)*(scale u*zeros ds) /\
    mass v+l <= mass u+zeros u+(7#12)*(scale u*zeros ds) /\
    0<ones v+l /\ ones v+l<=(1#64).
Proof.
  intros D Hs F [p U] W Lo Hi.
  destruct (C6_return _ _ _ _ D Hs F) as [b [v [l [J [r [I _]]]]]].
  assert (Cu : cut_at u (ds++[W0])).
  { left; rewrite U; change (cut_ok (p++([WT;WT]++[WT]))=true).
    rewrite app_assoc.
    apply cut_ok_last. }
  destruct (Scan_cut _ _ _ _ _ I u (ds++[W0]) eq_refl Cu)
    as [c [x [y [s [t [I1 [I2 [V L]]]]]]]].
  assert (Hv : has10 v=true).
  { pose proof I1 as J1; rewrite U in J1.
    destruct (Scan_T3_end _ _ _ _ _ J1)
      as [z [k [Z B]]].
    destruct Lo as [w E]; rewrite E in I2; cbn[app] in I2.
    rewrite B in I2; apply Scan_low00 in I2.
    rewrite V; apply has10_app; apply I2. }
  assert (Bv : exists p k, v=p++[WT;WT;WT] /\ b=(k*8)%nat).
  { destruct Hi as [w E].
    assert (I' : Scan 6 ((u++w)++repeat W1 6++[W0]) b v l).
    { rewrite E in I; repeat rewrite app_assoc in *; apply I. }
    apply Scan_six_end in I'; apply I'. }
  destruct Bv as [z [k [Z ->]]].
  destruct (Scan_gain_power _ _ _ _ _ I) as [g G].
  exists k, v, l, g; split; [apply I|].
  split; [exists z; apply Z|].
  split; [apply Hv|].
  assert (S : scale v*qnat (8^g)%nat == 1).
  { destruct (Digits_weights _ _ _ D) as [Ds _].
    repeat rewrite scale_app in G; cbn[scale] in G; rewrite Ds in G; nra. }
  split; [apply S|].
  assert (Zd : 3<=zeros ds).
  { destruct Lo as [w ->]; cbn[zeros]; pose proof (weights_nonneg w); lra. }
  pose proof (C6_stage_bounds _ _ _ _ _ _ _ _ _ _ I1 W I2
    (Digits_tail _ _ _ D) Zd) as [M B].
  rewrite <-V in M, B.
  assert (B' : mass v+l <= mass u+zeros u+(7#12)*(scale u*zeros ds)) by lra.
  split; [apply M|split; [apply B'|]].
  pose proof (weights_nonneg v); pose proof (weights_nonneg u).
  pose proof (weights_nonneg ds); pose proof (scale_pos u).
  pose proof (Scan_loss_pos _ _ _ _ _ I (has10_extend _ _ W)).
  pose proof (mass_split v); nra.
Qed.

Lemma C6_window g k s delta : s*qnat (8^g)%nat == 1 ->
  6 == qnat (k*8)%nat*s+delta*2 -> 0<delta -> delta<=(1#64) ->
  exists n, g=(3+n)%nat /\
    (191*2^(2+3*n)<=k*2)%nat /\ (k*2<192*2^(2+3*n))%nat.
Proof.
  intros S B D U.
  assert (P : 0<qnat (8^g)%nat) by (apply qnat_pos; pose proof (Nat.pow_nonzero 8 g); lia).
  assert (E : qnat (k*8)%nat == (6-delta*2)*qnat (8^g)%nat).
  { assert (T : qnat (k*8)%nat*s == 6-delta*2) by lra.
    rewrite <-T, <-Qmult_assoc, S; ring. }
  assert (L : (191*8^g<=256*k)%nat).
  { apply qnat_le; do 2 rewrite qnat_mul.
    change (qnat 191%nat) with 191; change (qnat 256%nat) with 256.
    rewrite qnat_mul in E; change (qnat 8%nat) with 8 in E; nra. }
  assert (R : (k*8<6*8^g)%nat).
  { apply qnat_lt; rewrite (qnat_mul 6 (8^g)%nat).
    change (qnat 6%nat) with 6; nra. }
  destruct g as [|[|[|n]]]; try (cbn[Nat.pow] in L, R; lia).
  exists n; split; [reflexivity|].
  change (191*8^(3+n)<=256*k)%nat in L.
  change (k*8<6*8^(3+n))%nat in R.
  rewrite (proj2 (c6_powers n)) in L, R; lia.
Qed.

Lemma Scan_return_binary a u b v l H r :
  Scan a u b v l -> Binary b H r ->
  RIncs a (to_side u (d1*>0inf)) (to_side v (t*>r)).
Proof.
  intros I B; pose proof (Binary_bounds _ _ _ B).
  destruct b as [|b]; [lia|].
  eapply Scan_spec; [apply I|].
  do 2 rewrite (const_unfold _ S0) at 1.
  apply RIncs_pair0; applys_eq (Binary_RIncs _ _ _ B); flia.
Qed.

Inductive Good : side -> Prop :=
| Good_intro u A H ds : Digits A H ds ->
    scale u*qnat (2^H)%nat == (1#2) ->
    mass u*2+zeros u+scale u*zeros ds <= (1#64) ->
    ends_T3 u -> has10 u=true -> low00 ds -> high6 ds ->
    Good (to_side (u++ds) (d0*>d1*>0inf)).

Lemma C6_closed r : Good r ->
  exists r', RIncs 6 r r' /\ Good (t*>r').
Proof.
  intros [u A H ds D Hs F U W Lo Hi].
  destruct (C6_scan _ _ _ _ D Hs F U W Lo Hi)
    as [k [v [l [g [I [Tv [V [S [M [L [Pos Bound]]]]]]]]]]].
  pose proof (Scan_budget _ _ _ _ _ I) as B.
  change (qnat 6%nat) with 6 in B.
  destruct (C6_window _ _ _ _ S B Pos Bound) as [n [-> [Kl Ku]]].
  destruct (tail_from_window _ _ Kl Ku) as [ds' [D' [Lo' [Hi' Bin]]]].
  exists (to_side v (t*>to_side ds' (d0*>d1*>0inf))); split.
  - pose proof (Scan_return_binary _ _ _ _ _ _ _ I Bin) as R.
    repeat rewrite to_side_app in *; cbn[to_side] in R; apply R.
  - assert (Out : t*>to_side v (t*>to_side ds' (d0*>d1*>0inf)) =
      to_side ((WT::(v++[WT]))++ds') (d0*>d1*>0inf)).
    { cbn[app to_side]; repeat rewrite to_side_app; reflexivity. }
    rewrite Out; apply (Good_intro _ _ _ _ D').
    + rewrite (proj2 (c6_powers n)) in S.
      rewrite qnat_mul in S; change (qnat 128%nat) with 128 in S.
      cbn[scale]; rewrite scale_app; cbn[scale].
      change (8+(2+3*n))%nat with (10+3*n)%nat.
      rewrite (proj1 (c6_powers n)), qnat_mul.
      change (qnat 256%nat) with 256; nra.
    + pose proof (Digits_zeros _ _ _ D') as Z.
      assert (Aeq : ((k*8-512*2^(2+3*n))+512*2^(2+3*n)=k*8)%nat) by lia.
      apply (f_equal qnat) in Aeq.
      assert (AE : qnat ((k*8-512*2^(2+3*n))+512*2^(2+3*n))%nat == qnat (k*8)%nat)
        by (rewrite Aeq; reflexivity).
      change (8+(2+3*n))%nat with (10+3*n)%nat in Z.
      rewrite (proj1 (c6_powers n)), qnat_mul in Z.
      change (qnat 256%nat) with 256 in Z.
      rewrite qnat_add, qnat_mul in AE; change (qnat 512%nat) with 512 in AE.
      rewrite (proj2 (c6_powers n)), qnat_mul in S.
      change (qnat 128%nat) with 128 in S.
      cbn[mass zeros scale]; rewrite mass_app, zeros_app, scale_app.
      cbn[mass zeros scale].
      pose proof (mass_split v).
      pose proof (weights_nonneg u); pose proof (weights_nonneg ds).
      pose proof (scale_pos u); pose proof (scale_pos v).
      nra.
    + destruct Tv as [w ->].
      exists (WT::(w++[WT])); cbn[app]; repeat rewrite <-app_assoc; reflexivity.
    + cbn[has10]; apply has10_extend; apply V.
    + apply Lo'.
    + apply Hi'.
Qed.

(* The two-pass family uses the same counter, but needs the initial D1 D0
   of its binary tail to be paired before applying a general scan bound. *)
Lemma Scan_pair0_inv a u b v l : Scan a (W1::W0::u) b v l ->
  exists n w s, a=(1+n)%nat /\ Scan (n*2)%nat u b w s /\
    v=WT::w /\ l==(1+s)*(1#2).
Proof.
  intro I; inversion I; subst;
    try solve [exfalso; eapply Scan_odd_zero; eassumption].
  eexists _, _, _; repeat split; eauto.
Qed.

Lemma Tail_pair_discount a ds b v l : Scan a (ds++[W0]) b v l ->
  (exists w, ds=W1::W0::w) ->
  (exists A H, Digits A H ds) -> 126<=zeros ds ->
  mass v<=zeros ds*(1#4) /\ mass v+l<=zeros ds*(127#252).
Proof.
  intros I [w ->] [A [H D]] Z.
  inversion D; subst; match goal with J: Digits _ _ (W0::_) |- _ =>
    inversion J; subst end.
  destruct (Scan_pair0_inv _ _ _ _ _ I) as [n [x [s [_ [J [-> L]]]]]].
  match goal with K: Digits _ _ w |- _ =>
    pose proof (Scan_tail_bounds _ _ _ _ _ J _ (Digits_tail _ _ _ K)) as B end.
  cbn[zeros mass] in *; lra.
Qed.

Lemma Scan_ends_T a p b v l : Scan a (p++[WT]) b v l ->
  exists w n, v=w++[WT] /\ b=(n*2)%nat.
Proof.
  intro I.
  destruct (Scan_cut _ _ _ _ _ I p [WT] eq_refl)
    as [c [x [y [s [t [J [K [-> E]]]]]]]]; [right; eauto|].
  destruct (Scan_repeat_T 1 _ _ _ _ K) as [-> [B L]].
  exists x, c; auto.
Qed.

Lemma C24_prefix_tail m u A H ds : Digits A H ds ->
  scale u*qnat (2^H)%nat == 1 -> (1<=m)%nat ->
  mass u+zeros u < (1#2) ->
  (exists w, ds=W1::W0::w) ->
  exists b x l c y s,
    Scan (m*2)%nat u b x l /\ Scan b (ds++[W0]) c y s /\ (0<c)%nat.
Proof.
  intros D S M F [w W].
  destruct (Scan_ex u m) as [b [x [l [I B]]]].
  { rewrite qnat_mul; change (qnat 2%nat) with 2.
    assert (1<=qnat m) by (change (qnat 1%nat<=qnat m); apply qnat_le; lia).
    lra. }
  assert (Delt : ones x+l<(1#2)).
  { pose proof (Scan_bounds _ _ _ _ _ I); pose proof (mass_split x).
    pose proof (weights_nonneg x); lra. }
  assert (Budget : 1<qnat b*scale x).
  { pose proof (Scan_budget _ _ _ _ _ I) as Eq.
    rewrite qnat_mul in Eq; change (qnat 2%nat) with 2 in Eq.
    assert (1<=qnat m) by (change (qnat 1%nat<=qnat m); apply qnat_le; lia).
    lra. }
  assert (Rest : (mass (w++[W0])+zeros (w++[W0])+2)*scale x<=1).
  { rewrite <-(proj1 (Digits_weights _ _ _ D)) in S.
    rewrite W in D, S; cbn[scale] in S; inversion D; subst.
    match goal with J: Digits _ _ (W0::_) |- _ => inversion J; subst end.
    match goal with J: Digits _ _ w |- _ =>
      pose proof (Digits_weights _ _ _ J) as [Dw Mw] end.
    pose proof (Scan_scale _ _ _ _ _ I).
    pose proof (weights_nonneg w); pose proof (mass_split w).
    pose proof (scale_pos x); pose proof (scale_pos u); pose proof (scale_pos w).
    rewrite mass_app, zeros_app; cbn[mass zeros].
    nra. }
  destruct b as [|b]; [lia|].
  destruct (Scan_ex (w++[W0]) b) as [c [y [s [J C]]]].
  { rewrite qnat_mul; change (qnat 2%nat) with 2.
    rewrite qnat_S in Budget; pose proof (scale_pos x); nra. }
  exists (1+b)%nat, x, l, c, (WT::y), ((1+s)*(1#2)).
  split; [apply I|]. split; [rewrite W; cbn[app]; apply Scan_pair0; apply J|apply C].
Qed.

Lemma Scan_ones_long n r a b v l :
  Scan a (repeat W1 (1+r*2+n)%nat++[W0]) b v l ->
  exists w k, v=w++repeat WT (1+r)%nat /\ b=(k*2^(1+r))%nat.
Proof.
  intro I; destruct (mod2 n); subst n.
  - assert (1+r*2+a0*2=1+(r+a0)*2)%nat as E by lia; rewrite E in I.
    destruct (Scan_ones_odd (r+a0)%nat _ _ _ _ I) as [-> [B L]].
    exists (repeat WT a0), ((a-1)*2^a0)%nat; split.
    + rewrite <-repeat_app; f_equal; lia.
    + replace (1+(r+a0))%nat with (a0+(1+r))%nat in B by lia.
      rewrite Nat.pow_add_r in B; nia.
  - assert (1+r*2+(1+a0*2)=2+(r+a0)*2)%nat as E by lia; rewrite E in I.
    destruct (Scan_ones_even (r+a0)%nat _ _ _ _ I) as [d [k [-> [B L]]]].
    exists (d::repeat WT a0), (k*2^(1+a0))%nat; split.
    + cbn[app]; f_equal; rewrite <-repeat_app; f_equal; lia.
    + replace (2+(r+a0))%nat with ((1+a0)+(1+r))%nat in B by lia.
      rewrite Nat.pow_add_r in B; nia.
Qed.

Lemma Scan_many_end r a u b v l :
  Scan a (u++repeat W1 (1+r*2)%nat++[W0]) b v l ->
  exists w k, v=w++repeat WT (1+r)%nat /\ b=(k*2^(1+r))%nat.
Proof.
  intro I; destruct (trailing_ones u) as [p [n [-> P]]].
  assert (E : (p++repeat W1 n)++repeat W1 (1+r*2)%nat++[W0] =
    p++(repeat W1 (1+r*2+n)%nat++[W0])).
  { replace (1+r*2+n)%nat with (n+(1+r*2))%nat by lia.
    rewrite (repeat_app W1 n (1+r*2)%nat); repeat rewrite app_assoc; reflexivity. }
  rewrite E in I.
  destruct (Scan_cut _ _ _ _ _ I p (repeat W1 (1+r*2+n)%nat++[W0]) eq_refl)
    as [c [x [y [s [t [J [K [-> L]]]]]]]]; [left; apply P|].
  destruct (Scan_ones_long n r _ _ _ _ K) as [w [k [-> B]]].
  exists (x++w), k; rewrite app_assoc; auto.
Qed.

Lemma low1_pair ds : low1 ds -> exists w, ds=W1::W0::w.
Proof. intros [w ->]; eexists; reflexivity. Qed.

Lemma low1_zeros ds : low1 ds -> 126<=zeros ds.
Proof.
  intros [w ->]; cbn[zeros repeat app]; pose proof (weights_nonneg w); lra.
Qed.

Lemma C24_scan m u A H ds : Digits A H ds ->
  scale u*qnat (2^H)%nat == 1 -> (1<=m)%nat ->
  (29#8)*mass u+zeros u+scale u*zeros ds <= (1#32768) ->
  low1 ds -> high15 ds ->
  exists k v l g,
    Scan (m*2)%nat (u++ds++[W0]) (k*256)%nat v l /\
    (exists w, v=w++repeat WT 8) /\
    scale v*qnat (8^g)%nat == 2 /\
    mass v <= mass u+(1#4)*(scale u*zeros ds) /\
    mass v+l <= mass u+zeros u+(127#252)*(scale u*zeros ds) /\
    0<ones v+l /\ ones v+l<=(1#32768).
Proof.
  intros D S M F Lo [w Hi].
  pose proof (weights_nonneg u) as U.
  pose proof (weights_nonneg ds) as Ds.
  pose proof (scale_pos u) as Su.
  assert (Small : mass u+zeros u<(1#2)) by nra.
  destruct (C24_prefix_tail _ _ _ _ _ D S M Small (low1_pair _ Lo))
    as [b [x [s [c [y [t [I1 [I2 C]]]]]]]].
  destruct (Scan_app _ _ _ _ _ I1 _ _ _ _ I2) as [l [I L]].
  assert (End : exists p k, x++y=p++repeat WT 8 /\ c=(k*256)%nat).
  { rewrite Hi in I; repeat rewrite app_assoc in I.
    eapply (Scan_many_end 7 _ (u++w)); rewrite app_assoc; apply I. }
  destruct End as [p [k [E ->]]].
  destruct (Scan_gain_power _ _ _ _ _ I) as [g G].
  exists k, (x++y), l, g; split; [apply I|].
  split; [exists p; apply E|].
  split.
  { repeat rewrite scale_app in G; cbn[scale] in G.
    rewrite (proj1 (Digits_weights _ _ _ D)) in G; rewrite scale_app; nra. }
  pose proof (Scan_bounds _ _ _ _ _ I1) as B1.
  pose proof (Scan_scale _ _ _ _ _ I1) as S1.
  pose proof (Tail_pair_discount _ _ _ _ _ I2 (low1_pair _ Lo)
    (ex_intro _ A (ex_intro _ H D)) (low1_zeros _ Lo)) as B2.
  pose proof (scale_pos x) as Sx.
  assert (Mv : mass (x++y)<=mass u+(1#4)*(scale u*zeros ds)).
  { rewrite mass_app; nra. }
  assert (Bv : mass (x++y)+l<=mass u+zeros u+(127#252)*(scale u*zeros ds)).
  { rewrite mass_app; nra. }
  split; [apply Mv|split; [apply Bv|]].
  assert (W : has10 (u++ds++[W0])=true).
  { apply has10_app; destruct (low1_pair _ Lo) as [z ->]; reflexivity. }
  pose proof (Scan_loss_pos _ _ _ _ _ I W).
  pose proof (weights_nonneg (x++y)); pose proof (mass_split (x++y)); nra.
Qed.

Lemma Scan_blank_binary a u b v l H r : Scan a u (b*2)%nat v l ->
  Binary (1+b)%nat H r -> RIncs a (to_side u 0inf) (to_side v r).
Proof.
  intros I B; eapply Scan_spec; [apply I|].
  applys_eq (Binary_RIncs _ _ _ B); flia.
Qed.

Lemma C24_window m g k s delta : (m=1 \/ m=2)%nat ->
  s*qnat (8^g)%nat == 2 ->
  qnat (m*2)%nat == qnat (k*256)%nat*s+delta*2 ->
  0<delta -> delta<=(1#32768) ->
  exists n, g=(8+n)%nat /\
    (32767*2^(m+3*n)<=k)%nat /\ (k<32768*2^(m+3*n))%nat.
Proof.
  intros M S B Pos Small.
  assert (Mq : 1<=qnat m /\ qnat m<=2).
  { destruct M as [-> | ->]; change (qnat 1%nat) with 1;
      change (qnat 2%nat) with 2; lra. }
  assert (Pow : 0<qnat (8^g)%nat) by
    (apply qnat_pos; pose proof (Nat.pow_nonzero 8 g); lia).
  assert (Eq : qnat (k*256)%nat == (qnat m-delta)*qnat (8^g)%nat).
  { rewrite qnat_mul in B; change (qnat 2%nat) with 2 in B.
    assert (E : qnat (k*256)%nat*s == (qnat m-delta)*2) by lra.
    assert (E' : qnat (k*256)%nat*s*qnat (8^g)%nat ==
      (qnat m-delta)*2*qnat (8^g)%nat) by (rewrite E; reflexivity).
    rewrite <-Qmult_assoc, S in E'; lra. }
  assert (K : (0<k)%nat).
  { destruct k; [|lia]. change (qnat (0*256)%nat) with 0 in Eq; nra. }
  assert (R : (k*256<m*8^g)%nat).
  { apply qnat_lt; rewrite (qnat_mul m (8^g)%nat); nra. }
  destruct g as [|[|[|n]]]; try (destruct M as [-> | ->]; cbn[Nat.pow] in R; lia).
  change (qnat (k*256)%nat == (qnat m-delta)*qnat (8^(3+n))%nat) in Eq.
  rewrite Nat.pow_add_r in Eq; repeat rewrite qnat_mul in Eq.
  change (qnat 256%nat) with 256 in Eq; change (qnat (8^3)%nat) with 512 in Eq.
  assert (Rn : (k+1<=m*2*8^n)%nat).
  { change (k*256<m*8^(3+n))%nat in R.
    rewrite Nat.pow_add_r in R; change (8^3)%nat with 512%nat in R; lia. }
  apply qnat_le in Rn; rewrite qnat_add in Rn; repeat rewrite qnat_mul in Rn.
  change (qnat 1%nat) with 1 in Rn; change (qnat 2%nat) with 2 in Rn.
  assert (P : 16384<=qnat (8^n)%nat) by nra.
  assert (N : (5<=n)%nat).
  { destruct (le_dec 5 n); [lia|].
    assert (Q : (8^n<=8^4)%nat) by (apply Nat.pow_le_mono_r; lia).
    apply qnat_le in Q; change (qnat (8^4)%nat) with 4096 in Q; lra. }
  set (j:=(n-5)%nat).
  assert (NJ : n=(5+j)%nat) by (unfold j; lia).
  exists j; split; [lia|].
  rewrite NJ, Nat.pow_add_r in Eq.
  rewrite qnat_mul in Eq; change (qnat (8^5)%nat) with 32768 in Eq.
  assert (PJ : 0<qnat (8^j)%nat) by
    (apply qnat_pos; pose proof (Nat.pow_nonzero 8 j); lia).
  destruct M as [-> | ->]; split; [apply qnat_le|apply qnat_lt|apply qnat_le|apply qnat_lt];
    rewrite Nat.pow_add_r, pow_three;
    repeat rewrite qnat_mul;
    change (qnat 32767%nat) with 32767;
    change (qnat 32768%nat) with 32768;
    change (qnat (2^1)%nat) with 2;
    change (qnat (2^2)%nat) with 4;
    change (qnat 1%nat) with 1 in Eq;
    change (qnat 2%nat) with 2 in Eq; nra.
Qed.

Lemma C24_weight_step m a u b v l H ds z :
  Scan (m*2)%nat a (b*2)%nat v l -> Digits (1+b)%nat H ds ->
  scale v*scale ds == qnat m ->
  mass v<=mass u+(1#4)*z -> mass v+l<=mass u+zeros u+(127#252)*z -> 0<=z ->
  (29#8)*mass v+zeros (v++ds) <=
    (89#63)*((29#8)*mass u+zeros u+z).
Proof.
  intros I D S M B Z.
  pose proof (Scan_budget _ _ _ _ _ I) as E.
  pose proof (Digits_zeros _ _ _ D) as Dt.
  pose proof (Digits_weights _ _ _ D) as [Ds _].
  pose proof (mass_split v); pose proof (weights_nonneg u); pose proof (scale_pos v).
  repeat rewrite qnat_mul in E; change (qnat 2%nat) with 2 in E.
  rewrite qnat_add in Dt; change (qnat 1%nat) with 1 in Dt.
  rewrite zeros_app; nra.
Qed.

Lemma C24_scale m n s : (m=1 \/ m=2)%nat ->
  s*qnat (8^(8+n))%nat == 2 ->
  s*qnat (2^(22+(m+3*n)))%nat == qnat m.
Proof.
  intros M S.
  change (s*qnat (8^(3+(5+n)))%nat == 2) in S.
  rewrite (Nat.pow_add_r 8 3 (5+n)), (Nat.pow_add_r 8 5 n) in S.
  repeat rewrite qnat_mul in S.
  change (qnat (8^3)%nat) with 512 in S; change (qnat (8^5)%nat) with 32768 in S.
  replace (22+(m+3*n))%nat with (7+(15+(m+3*n)))%nat by lia.
  repeat rewrite Nat.pow_add_r; rewrite pow_three; repeat rewrite qnat_mul.
  change (qnat (2^7)%nat) with 128; change (qnat (2^15)%nat) with 32768.
  destruct M as [-> | ->]; change (qnat (2^1)%nat) with 2;
    change (qnat (2^2)%nat) with 4; change (qnat 1%nat) with 1;
    change (qnat 2%nat) with 2; lra.
Qed.

Inductive C24Good (bound:QArith_base.Q) : side -> Prop :=
| C24Good_intro u A H ds : Digits A H ds ->
    scale u*qnat (2^H)%nat == 1 ->
    (29#8)*mass u+zeros u+scale u*zeros ds <= bound ->
    low1 ds -> high15 ds -> C24Good bound (to_side (u++ds) 0inf).

Lemma C24_step m bound bound' r : (m=1 \/ m=2)%nat -> bound<=(1#32768) ->
  C24Good bound r -> (89#63)*bound<=qnat m*bound' ->
  exists r', RIncs (m*2)%nat r r' /\
    C24Good bound' (to_side (repeat WT (m-1)%nat) r').
Proof.
  intros M Limit [u A H ds D S F Lo Hi] Rate.
  assert (Positive : (1<=m)%nat) by (destruct M as [-> | ->]; lia).
  assert (Small : (29#8)*mass u+zeros u+scale u*zeros ds <= (1#32768)) by lra.
  destruct (C24_scan _ _ _ _ _ D S Positive Small Lo Hi)
    as [k [v [l [g [I [End [Scale [Mv [Bv [Pos Upper]]]]]]]]]].
  pose proof (Scan_budget _ _ _ _ _ I) as Budget.
  destruct (C24_window _ _ _ _ _ M Scale Budget Pos Upper) as [n [-> [Kl Ku]]].
  destruct (C24_tail_window _ _ Kl Ku) as [ds' [D' [Lo' [Hi' Bin]]]].
  assert (Scale' : scale v*scale ds'==qnat m).
  { rewrite (proj1 (Digits_weights _ _ _ D')); apply (C24_scale _ _ _ M Scale). }
  assert (I' : Scan (m*2)%nat (u++ds++[W0]) ((k*128)*2)%nat v l).
  { applys_eq I; flia. }
  pose proof (Scan_blank_binary _ _ _ _ _ _ _ I' Bin) as R.
  assert (R' : RIncs (m*2)%nat (to_side (u++ds) 0inf) (to_side (v++ds') 0inf)).
  { repeat rewrite to_side_app in *; cbn[to_side] in R.
    change (RIncs (m*2)%nat (to_side u (to_side ds (S0 >> S0 >> 0inf)))
      (to_side v (to_side ds' 0inf))) in R.
    repeat rewrite <-const_unfold in R; apply R. }
  assert (Z : 0<=scale u*zeros ds).
  { pose proof (scale_pos u); pose proof (weights_nonneg ds); nra. }
  pose proof (C24_weight_step _ _ _ _ _ _ _ _ _ I' D' Scale' Mv Bv Z) as Weight.
  exists (to_side (v++ds') 0inf); split; [apply R'|].
  rewrite <-to_side_app, app_assoc.
  apply (C24Good_intro bound' (repeat WT (m-1)%nat++v) _ _ _ D').
  - rewrite <-(proj1 (Digits_weights _ _ _ D')).
    rewrite scale_app.
    destruct M as [-> | ->]; cbn[Nat.sub Nat.add repeat scale];
      change (qnat 1%nat) with 1 in Scale'; change (qnat 2%nat) with 2 in Scale'; nra.
  - rewrite mass_app, zeros_app, scale_app; rewrite zeros_app in Weight.
    destruct M as [-> | ->]; cbn[Nat.sub Nat.add repeat mass zeros scale];
      change (qnat 1%nat) with 1 in Rate; change (qnat 2%nat) with 2 in Rate; nra.
  - apply Lo'.
  - apply Hi'.
Qed.

Lemma C24_closed r : C24Good (1#65536) r ->
  exists s r', RIncs 2 r s /\ RIncs 4 s r' /\ C24Good (1#65536) (t*>r').
Proof.
  intro G.
  destruct (C24_step 1 (1#65536) ((89#63)*(1#65536)) r) as [s [R H]].
  - left; reflexivity.
  - lra.
  - apply G.
  - change (qnat 1%nat) with 1; lra.
  - cbn[Nat.sub repeat to_side] in H.
    destruct (C24_step 2 ((89#63)*(1#65536)) (1#65536) s) as [r' [S I]].
    + right; reflexivity.
    + lra.
    + apply H.
    + change (qnat 2%nat) with 2; lra.
    + exists s, r'; split; [apply R|split; [apply S|apply I]].
Qed.

End Quantitative.

(* Finite entrances use binary counters: some budgets already exceed 10^11.
   A code is an untrusted list of constructor choices, checked below. *)
Fixpoint pwords (p : positive) : list Word :=
  match p with
  | xH => [W1]
  | xO q => W0::pwords q
  | xI q => W1::pwords q
  end.

Lemma pwords_spec p : exists H, Binary (Pos.to_nat p) H (to_side (pwords p) 0inf).
Proof.
  induction p; cbn[pwords].
  - destruct IHp as [H I]; exists (1+H).
    rewrite Pos2Nat.inj_xI; pose proof (Pos2Nat.is_pos p).
    applys_eq (Binary2 (Pos.to_nat p-1) H); try flia.
    applys_eq I; flia.
  - destruct IHp as [H I]; exists (1+H).
    rewrite Pos2Nat.inj_xO; pose proof (Pos2Nat.is_pos p).
    applys_eq (Binary0 (Pos.to_nat p-1) H); try flia.
    applys_eq I; flia.
  - exists 1; constructor.
Qed.

Definition nwords (n : N) := match n with N0 => [] | Npos p => pwords p end.

Lemma nwords_return n : RIncs (N.to_nat (n*2)%N) 0inf (to_side (nwords (N.succ n)) 0inf).
Proof.
  assert (B : exists H, Binary (1+N.to_nat n) H (to_side (nwords (N.succ n)) 0inf)).
  { destruct n as [|p].
    - exists 1; constructor.
    - destruct (pwords_spec (Pos.succ p)) as [H I]; exists H.
      rewrite Pos2Nat.inj_succ in I; apply I. }
  destruct B as [H B].
  apply Binary_RIncs in B; rewrite N2Nat.inj_mul; cbn[N.to_nat].
  applys_eq B; flia.
Qed.

Fixpoint strip_words p u :=
  match p, u with
  | [], _ => Some u
  | WT::p, WT::u | W0::p, W0::u | W1::p, W1::u => strip_words p u
  | _, _ => None
  end.

Lemma strip_words_spec p : forall u v, strip_words p u=Some v -> u=p++v.
Proof.
  induction p as [|w p IH]; intros u v E.
  - inversion E; reflexivity.
  - destruct u as [|x u]; [destruct w; discriminate|].
    destruct w, x; cbn[strip_words] in E; try discriminate;
      apply IH in E; subst; reflexivity.
Qed.

Definition is_zero w := match w with W0 => true | _ => false end.

Lemma zero_side u : forallb is_zero u=true -> to_side u 0inf=0inf.
Proof.
  induction u as [|w u IH]; [reflexivity|].
  destruct w; cbn[forallb is_zero to_side]; try discriminate.
  intro E; rewrite (IH E); change (S0 >> S0 >> 0inf=0inf).
  repeat rewrite <-const_unfold; reflexivity.
Qed.

Inductive Choice := CT | CP0 | CP1 | CS00 | CS01 | CS10 | CS11.
Inductive Code := Stop (n:N) | More (ch:Choice) (n:N) (next:Code).

Definition code_in ch n : N :=
  match ch with
  | CT | CP0 | CP1 => (1+n)%N
  | CS00 | CS01 => (2+n*4)%N
  | CS10 | CS11 => (4+n*4)%N
  end.
Definition code_out ch n : N :=
  match ch with
  | CT => ((1+n)*2)%N
  | CP0 | CS00 | CS10 => (n*2)%N
  | CP1 | CS01 | CS11 => (1+n*2)%N
  end.
Definition code_read ch :=
  match ch with
  | CT => [WT] | CP0 => [W1;W0] | CP1 => [W1;W1]
  | CS00 | CS10 => [W0] | CS01 | CS11 => [W1]
  end.
Definition code_write ch :=
  match ch with CT | CP0 | CP1 => WT | CS00 | CS01 => W0 | CS10 | CS11 => W1 end.

Fixpoint run_code c k u : option (list Word) :=
  match c with
  | Stop n => if N.eqb k (n*2)%N then
      if forallb is_zero u then Some (nwords (N.succ n)) else None else None
  | More ch n c => if N.eqb k (code_in ch n) then
      match strip_words (code_read ch) u with
      | None => None
      | Some u => match run_code c (code_out ch n) u with
        | None => None | Some v => Some (code_write ch::v) end
      end else None
  end.

Lemma run_code_spec c : forall k u v, run_code c k u=Some v ->
  RIncs (N.to_nat k) (to_side u 0inf) (to_side v 0inf).
Proof.
  induction c as [n|ch n c IH]; intros k u v E; cbn[run_code] in E.
  - destruct (N.eqb k (n*2)%N) eqn:K; [apply N.eqb_eq in K; subst k|discriminate].
    destruct (forallb is_zero u) eqn:U; [|discriminate].
    inversion E; subst; rewrite (zero_side _ U); apply nwords_return.
  - destruct (N.eqb k (code_in ch n)) eqn:K; [apply N.eqb_eq in K; subst k|discriminate].
    destruct (strip_words (code_read ch) u) as [w|] eqn:U; [|discriminate].
    destruct (run_code c (code_out ch n) w) as [x|] eqn:C; [|discriminate].
    inversion E; subst v; apply strip_words_spec in U; subst u.
    specialize (IH _ _ _ C); destruct ch;
      cbn[code_in code_out code_read code_write to_side app] in *;
      repeat rewrite N2Nat.inj_add in *; repeat rewrite N2Nat.inj_mul in *;
      repeat rewrite N2Nat.inj_add in *;
      change (N.to_nat 1%N) with 1 in *; change (N.to_nat 2%N) with 2 in *;
      change (N.to_nat 4%N) with 4 in *;
      eauto using RIncs_T, RIncs_pair0, RIncs_pair1,
        RIncs_short00, RIncs_short01, RIncs_short10, RIncs_short11.
Qed.

Definition run_round c u :=
  match run_code c 6%N (u++[W0]) with Some v => Some (WT::v) | None => None end.

Lemma run_round_spec c u v : run_round c u=Some v ->
  exists r, RIncs 6 (to_side u 0inf) r /\ to_side v 0inf=t*>r.
Proof.
  unfold run_round; destruct (run_code c 6%N (u++[W0])) as [w|] eqn:E; [|discriminate].
  intro V; inversion V; subst v.
  exists (to_side w 0inf); split; [|reflexivity].
  apply run_code_spec in E; rewrite to_side_app in E; cbn[to_side] in E.
  change (RIncs 6 (to_side u (S0 >> S0 >> 0inf)) (to_side w 0inf)) in E.
  repeat rewrite <-const_unfold in E; apply E.
Qed.

Inductive Rounds : side -> side -> Prop :=
| Rounds_refl r : Rounds r r
| Rounds_next r s t : RIncs 6 r s -> Rounds ([S1;S1;S0;S0]*>s) t -> Rounds r t.

Fixpoint run_rounds cs u :=
  match cs with
  | [] => Some u
  | c::cs => match run_round c u with None => None | Some v => run_rounds cs v end
  end.

Lemma run_rounds_spec cs : forall u v, run_rounds cs u=Some v ->
  Rounds (to_side u 0inf) (to_side v 0inf).
Proof.
  induction cs as [|c cs IH]; intros u v E; cbn[run_rounds] in E.
  - inversion E; constructor.
  - destruct (run_round c u) as [w|] eqn:W; [|discriminate].
    apply run_round_spec in W; destruct W as [r [R W]].
    eapply Rounds_next; [apply R|].
    rewrite <-W; apply IH; apply E.
Qed.

Definition is_digit w := match w with WT => false | _ => true end.

Lemma digit_list ds : forallb is_digit ds=true -> exists A, Digits A (length ds) ds.
Proof.
  induction ds as [|w ds IH].
  - intro; exists 0; constructor.
  - destruct w; cbn[forallb is_digit length]; [discriminate| |];
      intro D; destruct (IH D) as [A I]; eexists; constructor; apply I.
Qed.

Lemma Good_simple u ds : forallb is_digit ds=true ->
  (scale u*scale ds == (1#2))%Q ->
  (mass u*2+zeros u+scale u*zeros ds <= (1#64))%Q ->
  ends_T3 u -> has10 u=true -> low00 ds -> high6 ds ->
  Good (to_side (u++ds) (d0*>d1*>0inf)).
Proof.
  intros D S F U W Lo Hi; destruct (digit_list _ D) as [A I].
  apply (Good_intro _ _ _ _ I); auto.
  rewrite <-(proj1 (Digits_weights _ _ _ I)); apply S.
Qed.


Definition entry2_start := [WT;W1;W1].
Definition entry2_codes := [(More CT 5%N (More CS11 2%N (More CP0 4%N (Stop 4%N))));
  (More CT 5%N (More CT 11%N (More CS11 5%N (More CT 10%N (More CP0 21%N (More CP0 41%N (Stop 41%N)))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CS11 11%N (More CT 22%N (More CT 45%N (More CT 91%N (More CS10 45%N (More CP0 89%N (More CP0 177%N (More CP0 353%N (Stop 353%N))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CS11 23%N (More CT 46%N (More CT 93%N (More CT 187%N (More CS11 93%N (More CT 186%N (More CT 373%N (More CT 747%N (More CS10 373%N (More CP0 745%N (More CS00 372%N (More CS10 185%N (More CS01 92%N (More CP0 184%N (More CP0 367%N (Stop 367%N))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CS11 47%N (More CT 94%N (More CT 189%N (More CT 379%N (More CS11 189%N (More CT 378%N (More CT 757%N (More CT 1515%N (More CS11 757%N (More CT 1514%N (More CS00 757%N (More CP0 1513%N (More CT 3025%N (More CT 6051%N (More CS10 3025%N (More CS00 1512%N (More CS10 755%N (More CS00 377%N (More CP1 753%N (More CP0 1506%N (More CP0 3011%N (Stop 3011%N)))))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CS11 95%N (More CT 190%N (More CT 381%N (More CT 763%N (More CS11 381%N (More CT 762%N (More CT 1525%N (More CT 3051%N (More CS11 1525%N (More CT 3050%N (More CS00 1525%N (More CT 3049%N (More CT 6099%N (More CT 12199%N (More CP0 24399%N (More CP0 48797%N (More CT 97593%N (More CT 195187%N (More CT 390375%N (More CS10 195187%N (More CS00 97593%N (More CP0 195185%N (More CS00 97592%N (More CS10 48795%N (More CS01 24397%N (More CP1 48794%N (More CP0 97588%N (More CP0 195175%N (Stop 195175%N)))))))))))))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CS11 191%N (More CT 382%N (More CT 765%N (More CT 1531%N (More CS11 765%N (More CT 1530%N (More CT 3061%N (More CT 6123%N (More CS11 3061%N (More CT 6122%N (More CS00 3061%N (More CT 6121%N (More CT 12243%N (More CT 24487%N (More CT 48975%N (More CT 97951%N (More CT 195903%N (More CT 391807%N (More CT 783615%N (More CP0 1567231%N (More CT 3134461%N (More CS10 1567230%N (More CP0 3134459%N (More CT 6268917%N (More CT 12537835%N (More CT 25075671%N (More CS10 12537835%N (More CS00 6268917%N (More CS00 3134458%N (More CP0 6268915%N (More CS01 3134457%N (More CP0 6268914%N (More CS10 3134456%N (More CP0 6268911%N (More CP1 12537821%N (More CP1 25075642%N (More CP0 50151284%N (More CP0 100302567%N (Stop 100302567%N))))))))))))))))))))))))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CT 767%N (More CS11 383%N (More CT 766%N (More CT 1533%N (More CT 3067%N (More CS11 1533%N (More CT 3066%N (More CT 6133%N (More CT 12267%N (More CS11 6133%N (More CT 12266%N (More CS00 6133%N (More CT 12265%N (More CT 24531%N (More CT 49063%N (More CT 98127%N (More CT 196255%N (More CT 392511%N (More CT 785023%N (More CT 1570047%N (More CT 3140095%N (More CT 6280191%N (More CS11 3140095%N (More CT 6280190%N (More CT 12560381%N (More CT 25120763%N (More CT 50241527%N (More CP0 100483055%N (More CS00 50241527%N (More CT 100483053%N (More CS10 50241526%N (More CT 100483051%N (More CS11 50241525%N (More CT 100483050%N (More CT 200966101%N (More CT 401932203%N (More CT 803864407%N (More CT 1607728815%N (More CS10 803864407%N (More CS00 401932203%N (More CS00 200966101%N (More CP0 401932201%N (More CP1 803864401%N (More CP0 1607728802%N (More CS11 803864400%N (More CP1 1607728800%N (More CP1 3215457600%N (More CP0 6430915200%N (More CS10 3215457599%N (More CP0 6430915197%N (More CS01 3215457598%N (More CP1 6430915196%N (More CP1 12861830392%N (More CP0 25723660784%N (More CP0 51447321567%N (Stop 51447321567%N)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))].
Definition entry2_u := [WT;WT;WT;WT;WT;WT;WT;WT;WT;W1;WT;WT;WT;W1;WT;WT;WT;W1;WT;W0;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;W1;WT;WT;WT;WT;WT;W0;WT;W1;WT;W1;WT;WT;WT;WT;WT;W1;W0;W0;WT;WT;WT;W1;WT;WT;WT;W1;WT;W0;WT;WT;WT;WT].
Definition entry2_ds := [W0;W0;W0;W0;W0;W1;W1;W1;W1;W1;W0;W0;W1;W0;W1;W1;W1;W1;W1;W1;W1;W1;W1;W0;W0;W1;W0;W1;W1;W1;W1;W1;W1;W1].

Lemma entry2_reach : Rounds (to_side entry2_start 0inf)
  (to_side (entry2_u++entry2_ds) (d0*>d1*>0inf)).
Proof.
  change (Rounds (to_side entry2_start 0inf)
    (to_side (entry2_u++entry2_ds++[W0;W1]) 0inf)).
  apply (run_rounds_spec entry2_codes); vm_compute; reflexivity.
Qed.

Lemma entry2_good : Good (to_side (entry2_u++entry2_ds) (d0*>d1*>0inf)).
Proof.
  apply Good_simple.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; discriminate.
  - exists (firstn (length entry2_u-3) entry2_u); vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exists (skipn 2 entry2_ds); vm_compute; reflexivity.
  - exists (firstn (length entry2_ds-6) entry2_ds); vm_compute; reflexivity.
Qed.


Definition entry3_start := [WT;W0;WT;W0;W1].
Definition entry3_codes := [(More CT 5%N (More CS10 2%N (More CT 3%N (More CS10 1%N (More CP0 1%N (Stop 1%N))))));
  (More CT 5%N (More CT 11%N (More CS11 5%N (More CT 10%N (More CS01 5%N (More CT 10%N (More CS00 5%N (More CP0 9%N (Stop 9%N)))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CS11 11%N (More CT 22%N (More CS00 11%N (More CT 21%N (More CS10 10%N (More CT 19%N (More CS10 9%N (More CP0 17%N (More CP0 33%N (Stop 33%N)))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CS11 23%N (More CT 46%N (More CS00 23%N (More CT 45%N (More CS11 22%N (More CT 44%N (More CS01 22%N (More CT 44%N (More CT 89%N (More CS10 44%N (More CP0 87%N (More CS00 43%N (More CS00 21%N (More CP0 41%N (Stop 41%N)))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CS11 47%N (More CT 94%N (More CS00 47%N (More CT 93%N (More CS11 46%N (More CT 92%N (More CS00 46%N (More CT 91%N (More CT 183%N (More CS11 91%N (More CT 182%N (More CS00 91%N (More CS00 45%N (More CT 89%N (More CS10 44%N (More CP0 87%N (More CP0 173%N (More CP0 345%N (Stop 345%N))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CS11 95%N (More CT 190%N (More CS00 95%N (More CT 189%N (More CS11 94%N (More CT 188%N (More CS00 94%N (More CT 187%N (More CT 375%N (More CS11 187%N (More CT 374%N (More CS00 187%N (More CS00 93%N (More CT 185%N (More CS11 92%N (More CT 184%N (More CT 369%N (More CT 739%N (More CS10 369%N (More CP0 737%N (More CS01 368%N (More CP0 736%N (More CP0 1471%N (More CP0 2941%N (Stop 2941%N)))))))))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CS11 191%N (More CT 382%N (More CS00 191%N (More CT 381%N (More CS11 190%N (More CT 380%N (More CS00 190%N (More CT 379%N (More CT 759%N (More CS11 379%N (More CT 758%N (More CS00 379%N (More CS00 189%N (More CT 377%N (More CS11 188%N (More CT 376%N (More CT 753%N (More CT 1507%N (More CS11 753%N (More CT 1506%N (More CS00 753%N (More CT 1505%N (More CT 3011%N (More CT 6023%N (More CS10 3011%N (More CS01 1505%N (More CP1 3010%N (More CP1 6020%N (More CP0 12040%N (More CS11 6019%N (More CP0 12038%N (More CP0 24075%N (Stop 24075%N))))))))))))))))))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CT 767%N (More CS11 383%N (More CT 766%N (More CS00 383%N (More CT 765%N (More CS11 382%N (More CT 764%N (More CS00 382%N (More CT 763%N (More CT 1527%N (More CS11 763%N (More CT 1526%N (More CS00 763%N (More CS00 381%N (More CT 761%N (More CS11 380%N (More CT 760%N (More CT 1521%N (More CT 3043%N (More CS11 1521%N (More CT 3042%N (More CS00 1521%N (More CT 3041%N (More CT 6083%N (More CT 12167%N (More CP0 24335%N (More CT 48669%N (More CT 97339%N (More CT 194679%N (More CS11 97339%N (More CT 194678%N (More CT 389357%N (More CS10 194678%N (More CS10 97338%N (More CS11 48668%N (More CP0 97336%N (More CS10 48667%N (More CS00 24333%N (More CS00 12166%N (More CS10 6082%N (More CS11 3040%N (More CP1 6080%N (More CP0 12160%N (More CP0 24319%N (Stop 24319%N))))))))))))))))))))))))))))))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CT 767%N (More CT 1535%N (More CS11 767%N (More CT 1534%N (More CS00 767%N (More CT 1533%N (More CS11 766%N (More CT 1532%N (More CS00 766%N (More CT 1531%N (More CT 3063%N (More CS11 1531%N (More CT 3062%N (More CS00 1531%N (More CS00 765%N (More CT 1529%N (More CS11 764%N (More CT 1528%N (More CT 3057%N (More CT 6115%N (More CS11 3057%N (More CT 6114%N (More CS00 3057%N (More CT 6113%N (More CT 12227%N (More CT 24455%N (More CT 48911%N (More CT 97823%N (More CT 195647%N (More CT 391295%N (More CS11 195647%N (More CT 391294%N (More CT 782589%N (More CS11 391294%N (More CP1 782588%N (More CT 1565176%N (More CP0 3130353%N (More CS00 1565176%N (More CP1 3130351%N (More CT 6260702%N (More CT 12521405%N (More CT 25042811%N (More CS10 12521405%N (More CS00 6260702%N (More CS10 3130350%N (More CS10 1565174%N (More CS10 782586%N (More CS10 391292%N (More CS10 195645%N (More CS00 97822%N (More CP1 195643%N (More CP1 391286%N (More CP0 782572%N (More CP0 1565143%N (Stop 1565143%N))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CT 767%N (More CT 1535%N (More CT 3071%N (More CS11 1535%N (More CT 3070%N (More CS00 1535%N (More CT 3069%N (More CS11 1534%N (More CT 3068%N (More CS00 1534%N (More CT 3067%N (More CT 6135%N (More CS11 3067%N (More CT 6134%N (More CS00 3067%N (More CS00 1533%N (More CT 3065%N (More CS11 1532%N (More CT 3064%N (More CT 6129%N (More CT 12259%N (More CS11 6129%N (More CT 12258%N (More CS00 6129%N (More CT 12257%N (More CT 24515%N (More CT 49031%N (More CT 98063%N (More CT 196127%N (More CT 392255%N (More CT 784511%N (More CS11 392255%N (More CT 784510%N (More CT 1569021%N (More CS11 784510%N (More CT 1569020%N (More CT 3138041%N (More CT 6276083%N (More CS10 3138041%N (More CT 6276081%N (More CT 12552163%N (More CT 25104327%N (More CT 50208655%N (More CP0 100417311%N (More CP1 200834621%N (More CP1 401669242%N (More CP0 803338484%N (More CT 1606676967%N (More CT 3213353935%N (More CT 6426707871%N (More CT 12853415743%N (More CS10 6426707871%N (More CS00 3213353935%N (More CS00 1606676967%N (More CS01 803338483%N (More CP0 1606676966%N (More CP1 3213353931%N (More CP0 6426707862%N (More CS10 3213353930%N (More CS10 1606676964%N (More CS10 803338481%N (More CS01 401669240%N (More CP1 803338480%N (More CP1 1606676960%N (More CP0 3213353920%N (More CP0 6426707839%N (Stop 6426707839%N))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))].
Definition entry3_u := [WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;W1;WT;W0;WT;W1;WT;W0;WT;WT;W1;WT;W0;W0;WT;W1;WT;WT;WT;W1;WT;W0;WT;WT;WT;WT;WT;WT;WT;W1;WT;WT;W1;WT;WT;WT;W1;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;W1;W0;W0;W0;WT;WT;WT;W1;W1;W1;W0;WT;WT;WT;WT].
Definition entry3_ds := [W0;W0;W0;W0;W0;W0;W0;W1;W1;W1;W1;W0;W0;W0;W1;W1;W1;W1;W1;W1;W0;W0;W0;W0;W1;W1;W1;W1;W1;W1;W1].

Lemma entry3_reach : Rounds (to_side entry3_start 0inf)
  (to_side (entry3_u++entry3_ds) (d0*>d1*>0inf)).
Proof.
  change (Rounds (to_side entry3_start 0inf)
    (to_side (entry3_u++entry3_ds++[W0;W1]) 0inf)).
  apply (run_rounds_spec entry3_codes); vm_compute; reflexivity.
Qed.

Lemma entry3_good : Good (to_side (entry3_u++entry3_ds) (d0*>d1*>0inf)).
Proof.
  apply Good_simple.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; discriminate.
  - exists (firstn (length entry3_u-3) entry3_u); vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exists (skipn 2 entry3_ds); vm_compute; reflexivity.
  - exists (firstn (length entry3_ds-6) entry3_ds); vm_compute; reflexivity.
Qed.


Definition entry4_start := [WT;WT;W0;W1;W1].
Definition entry4_codes := [(More CT 5%N (More CT 11%N (More CS10 5%N (More CS01 2%N (More CP0 4%N (Stop 4%N))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CP0 47%N (More CT 93%N (More CP0 187%N (More CP0 373%N (Stop 373%N))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CT 767%N (More CS10 383%N (More CS01 191%N (More CP0 382%N (More CP1 763%N (More CP0 1526%N (More CP0 3051%N (Stop 3051%N)))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CT 767%N (More CT 1535%N (More CP0 3071%N (More CT 6141%N (More CT 12283%N (More CT 24567%N (More CT 49135%N (More CS10 24567%N (More CS00 12283%N (More CS01 6141%N (More CP0 12282%N (More CP1 24563%N (More CP1 49126%N (More CP0 98252%N (More CP0 196503%N (Stop 196503%N)))))))))))))))))))))))].
Definition entry4_u := [WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;WT;W1;W0;W0;WT;WT;WT;WT;WT].
Definition entry4_ds := [W0;W0;W0;W1;W1;W0;W0;W1;W1;W1;W1;W1;W1;W1;W1;W1].

Lemma entry4_reach : Rounds (to_side entry4_start 0inf)
  (to_side (entry4_u++entry4_ds) (d0*>d1*>0inf)).
Proof.
  change (Rounds (to_side entry4_start 0inf)
    (to_side (entry4_u++entry4_ds++[W0;W1]) 0inf)).
  apply (run_rounds_spec entry4_codes); vm_compute; reflexivity.
Qed.

Lemma entry4_good : Good (to_side (entry4_u++entry4_ds) (d0*>d1*>0inf)).
Proof.
  apply Good_simple.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; discriminate.
  - exists (firstn (length entry4_u-3) entry4_u); vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exists (skipn 2 entry4_ds); vm_compute; reflexivity.
  - exists (firstn (length entry4_ds-6) entry4_ds); vm_compute; reflexivity.
Qed.


Definition entry5_start := [WT].
Definition entry5_codes := [(More CT 5%N (Stop 6%N));
  (More CT 5%N (More CT 11%N (More CP1 23%N (More CP0 46%N (Stop 46%N)))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CS11 47%N (More CP1 94%N (More CP0 188%N (More CP0 375%N (Stop 375%N))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CS11 95%N (More CT 190%N (More CT 381%N (More CT 763%N (More CS10 381%N (More CS00 190%N (More CS10 94%N (More CS11 46%N (More CP1 92%N (More CP0 184%N (More CP0 367%N (Stop 367%N))))))))))))))))));
  (More CT 5%N (More CT 11%N (More CT 23%N (More CT 47%N (More CT 95%N (More CT 191%N (More CT 383%N (More CS11 191%N (More CT 382%N (More CT 765%N (More CT 1531%N (More CP0 3063%N (More CP1 6125%N (More CT 12250%N (More CT 24501%N (More CT 49003%N (More CS10 24501%N (More CS00 12250%N (More CS10 6124%N (More CS10 3061%N (More CP1 6121%N (More CP0 12242%N (More CP0 24483%N (Stop 24483%N))))))))))))))))))))))))].
Definition entry5_u := [WT;WT;WT;WT;WT;WT;WT;WT;W1;WT;WT;WT;WT;WT;WT;WT;WT;W1;W0;W1;W1;WT;WT;WT].
Definition entry5_ds := [W0;W0;W1;W0;W0;W1;W0;W1;W1;W1;W1;W1;W1].

Lemma entry5_reach : Rounds (to_side entry5_start 0inf)
  (to_side (entry5_u++entry5_ds) (d0*>d1*>0inf)).
Proof.
  change (Rounds (to_side entry5_start 0inf)
    (to_side (entry5_u++entry5_ds++[W0;W1]) 0inf)).
  apply (run_rounds_spec entry5_codes); vm_compute; reflexivity.
Qed.

Lemma entry5_good : Good (to_side (entry5_u++entry5_ds) (d0*>d1*>0inf)).
Proof.
  apply Good_simple.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; discriminate.
  - exists (firstn (length entry5_u-3) entry5_u); vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exists (skipn 2 entry5_ds); vm_compute; reflexivity.
  - exists (firstn (length entry5_ds-6) entry5_ds); vm_compute; reflexivity.
Qed.
Definition c24_start13 := repeat WT 10++[W0]++repeat WT 3++[W1;W0;W0]++repeat W1 9.
Definition c24_start14 := repeat WT 3++[W1;WT;W0;W0;WT;W1;W1].
(* Executable C2/C4 entrance checker. Counters stay binary; the final
   boolean check uses upward-rounded integers, never expanded rationals. *)
Definition digitN (e:bool) n := if e then N.succ_double n else N.double n.
Definition digitW (e:bool) := if e then W1 else W0.

Definition shortN e k : option (Word*N) :=
  match k with
  | Npos (xO q) =>
      match q with
      | xH => Some (W0, digitN e 0%N)
      | xI p => Some (W0, digitN e (Npos p))
      | xO p => Some (W1, digitN e (N.pred (Npos p)))
      end
  | _ => None
  end.

Lemma shortN_spec e k d k' r r' : shortN e k=Some(d,k') ->
  RIncs (N.to_nat k') r r' ->
  RIncs (N.to_nat k) (to_side [digitW e] r) (to_side [d] r').
Proof.
  destruct k as [|[p|p|]]; try discriminate.
  destruct p as [p|p|]; cbn[shortN]; intro E; inversion E; subst d k';
    destruct e; cbn[digitW digitN to_side]; intro I;
    repeat rewrite N2Nat.inj_succ_double in I;
    repeat rewrite N2Nat.inj_double in I;
    repeat rewrite N2Nat.inj_pred in I;
    cbn[N.to_nat] in *; repeat rewrite Pos2Nat.inj_xO;
    repeat rewrite Pos2Nat.inj_xI; try pose proof (Pos2Nat.is_pos p).
  all: first [applys_eq (RIncs_short00 (Pos.to_nat p) r r'); try flia; applys_eq I; flia
             |applys_eq (RIncs_short01 (Pos.to_nat p) r r'); try flia; applys_eq I; flia
             |applys_eq (RIncs_short10 (Nat.pred (Pos.to_nat p)) r r'); try flia; applys_eq I; flia
             |applys_eq (RIncs_short11 (Nat.pred (Pos.to_nat p)) r r'); try flia; applys_eq I; flia
             |apply (RIncs_short00 0 r r' I)
             |apply (RIncs_short01 0 r r' I)].
Qed.

Fixpoint singleN u :=
  match u with [] | W0::_ => true | WT::_ => false | W1::u => negb (singleN u) end.

Fixpoint scanN u k acc {struct u} : option (list Word) :=
  match k with
  | N0 => if forallb is_zero u then Some (rev_append acc [W1]) else None
  | Npos p =>
      match u with
      | [] => match p with
              | xO q => Some (rev_append acc (pwords (Pos.succ q)))
              | _ => None end
      | WT::u => scanN u (Npos (xO p)) (WT::acc)
      | W0::u => match shortN false k with
                 | Some(d,k') => scanN u k' (d::acc) | None => None end
      | W1::u =>
          if match p with xO _ => singleN (W1::u) | _ => false end then
            match shortN true k with
            | Some(d,k') => scanN u k' (d::acc) | None => None end
          else match u with
               | W0::v => scanN v (N.double (N.pred k)) (WT::acc)
               | W1::v => scanN v (N.succ_double (N.pred k)) (WT::acc)
               | _ => None end
      end
  end.

Lemma RIncs_TN p r r' : RIncs (Pos.to_nat (xO p)) r r' ->
  RIncs (Pos.to_nat p) (to_side [WT] r) (to_side [WT] r').
Proof.
  intro I; rewrite Pos2Nat.inj_xO in I; pose proof (Pos2Nat.is_pos p).
  cbn[to_side]; applys_eq (RIncs_T (Pos.to_nat p-1) r r'); try flia.
  applys_eq I; flia.
Qed.

Lemma RIncs_pairN e p r r' :
  RIncs (N.to_nat (digitN e (N.pred (Npos p)))) r r' ->
  RIncs (Pos.to_nat p) (to_side [W1;digitW e] r) (to_side [WT] r').
Proof.
  destruct e; cbn[digitN digitW to_side]; intro I;
    repeat rewrite N2Nat.inj_succ_double in I;
    repeat rewrite N2Nat.inj_double in I; rewrite N2Nat.inj_pred in I;
    cbn[N.to_nat] in I; pose proof (Pos2Nat.is_pos p).
  - applys_eq (RIncs_pair1 (Nat.pred (Pos.to_nat p)) r r'); try flia.
    applys_eq I; flia.
  - applys_eq (RIncs_pair0 (Nat.pred (Pos.to_nat p)) r r'); try flia.
    applys_eq I; flia.
Qed.

Lemma scanN_spec : forall u k acc v, scanN u k acc=Some v ->
  exists w, v=rev_append acc w /\
    RIncs (N.to_nat k) (to_side u 0inf) (to_side w 0inf).
Proof.
  fix IH 1; intros u k acc v E; destruct u as [|x u]; destruct k as [|p].
  - cbn[scanN] in E; inversion E; exists [W1]; split; [reflexivity|].
    apply (nwords_return 0%N).
  - destruct p as [q|q|]; cbn[scanN] in E; try discriminate.
      inversion E; exists (pwords (Pos.succ q)); split; [reflexivity|].
      change (RIncs (N.to_nat (N.double (Npos q))) 0inf
        (to_side (nwords (N.succ (Npos q))) 0inf)).
      rewrite N.double_spec, N.mul_comm; apply nwords_return.
  - change ((if forallb is_zero (x::u) then Some (rev_append acc [W1]) else None)=Some v) in E.
    destruct (forallb is_zero (x::u)) eqn:U; [|discriminate].
    inversion E; exists [W1]; split; [reflexivity|].
    rewrite (zero_side _ U); apply (nwords_return 0%N).
  - destruct x; cbn[scanN] in E.
      * destruct (IH _ _ _ _ E) as [w [V R]].
        exists (WT::w); split; [exact V|apply (RIncs_TN _ _ _ R)].
      * destruct (shortN false (Npos p)) as [[d k']|] eqn:S; [|discriminate].
        destruct (IH _ _ _ _ E) as [w [V R]].
        exists (d::w); split; [exact V|apply (shortN_spec false _ _ _ _ _ S R)].
      * destruct (match p with xO _ => singleN (W1::u) | _ => false end).
        -- destruct (shortN true (Npos p)) as [[d k']|] eqn:S; [|discriminate].
           destruct (IH _ _ _ _ E) as [w [V R]].
           exists (d::w); split; [exact V|apply (shortN_spec true _ _ _ _ _ S R)].
        -- destruct u as [|x u]; [discriminate|].
           destruct x; [discriminate| |];
             destruct (IH _ _ _ _ E) as [w [V R]];
             exists (WT::w); split; try exact V.
           ++ apply (RIncs_pairN false _ _ _ R).
           ++ apply (RIncs_pairN true _ _ _ R).
Qed.

Definition cscan k u := scanN (u++[W0]) k [].

Lemma cscan_spec k u v : cscan k u=Some v ->
  RIncs (N.to_nat k) (to_side u 0inf) (to_side v 0inf).
Proof.
  intro E; destruct (scanN_spec _ _ _ _ E) as [w [V R]]; cbn[rev_append] in V; subst v.
  rewrite to_side_app in R; cbn[to_side] in R.
  change (RIncs (N.to_nat k) (to_side u (S0 >> S0 >> 0inf)) (to_side w 0inf)) in R.
  repeat rewrite <-const_unfold in R; apply R.
Qed.

Definition qN n := inject_Z (Z.of_N n).
Definition half_up n := N.div2 (N.succ n).

Lemma half_up_bound n : (n<=N.double (half_up n))%N.
Proof.
  unfold half_up; rewrite N.double_spec, N.div2_div; lia.
Qed.

Open Scope Q.

Lemma qN_add a b : qN (a+b)%N == qN a+qN b.
Proof. unfold qN; rewrite N2Z.inj_add, inject_Z_plus; reflexivity. Qed.

Lemma qN_double a : qN (N.double a) == 2*qN a.
Proof.
  unfold qN; rewrite N.double_spec, N2Z.inj_mul, inject_Z_mult; reflexivity.
Qed.

Lemma qN_le a b : (a<=b)%N -> qN a<=qN b.
Proof.
  intro H; apply N2Z.inj_le in H; unfold qN, Qle; cbn; lia.
Qed.

Lemma qN_half_up n : qN n<=2*qN (half_up n).
Proof.
  pose proof (qN_le _ _ (half_up_bound n)) as H; rewrite qN_double in H; exact H.
Qed.

Fixpoint rounded c0 c1 u n : N :=
  match u with
  | [] => n
  | WT::u => rounded c0 c1 u (half_up n)
  | W0::u => rounded c0 c1 u (N.double n+c0)%N
  | W1::u => rounded c0 c1 u (N.double n+c1)%N
  end.

Lemma ones_app u v : ones (u++v) == ones u+scale u*ones v.
Proof.
  induction u as [|w u IH]; [cbn[ones scale app]; ring|].
  destruct w; cbn[ones scale app]; rewrite IH; ring.
Qed.

Lemma rounded_spec c0 c1 u : forall n,
  qN c0*zeros (rev u)+qN c1*ones (rev u)+scale (rev u)*qN n <=
  qN (rounded c0 c1 u n).
Proof.
  induction u as [|w u IH]; intro n; [cbn[rev zeros ones scale rounded]; lra|].
  destruct w; cbn[rounded rev];
    rewrite zeros_app, ones_app, scale_app; cbn[zeros ones scale];
    pose proof (scale_pos (rev u)).
  - pose proof (qN_half_up n); specialize (IH (half_up n)); nra.
  - specialize (IH (N.double n+c0)%N); rewrite qN_add, qN_double in IH; nra.
  - specialize (IH (N.double n+c1)%N); rewrite qN_add, qN_double in IH; nra.
Qed.

Lemma rounded_forward c0 c1 u n :
  qN c0*zeros u+qN c1*ones u+scale u*qN n <=
  qN (rounded c0 c1 (rev_append u []) n).
Proof.
  rewrite rev_append_rev, app_nil_r.
  pose proof (rounded_spec c0 c1 (rev u) n) as H.
  rewrite rev_involutive in H; exact H.
Qed.

Fixpoint heightN u h : option nat :=
  match u with
  | [] => Some h
  | WT::u => heightN u (S h)
  | _::u => match h with O => None | S h => heightN u h end
  end.

Lemma heightN_spec u : forall h H, heightN u h=Some H ->
  scale u*qnat (2^H)%nat == qnat (2^h)%nat.
Proof.
  induction u as [|w u IH]; intros h H E.
  - inversion E; cbn[scale]; ring.
  - destruct w; cbn[heightN scale] in *.
    + specialize (IH _ _ E); rewrite Nat.pow_succ_r', qnat_mul in IH.
      change (qnat 2%nat) with 2 in IH; nra.
    + destruct h; [discriminate|]; specialize (IH _ _ E).
      rewrite Nat.pow_succ_r', qnat_mul; change (qnat 2%nat) with 2; nra.
    + destruct h; [discriminate|]; specialize (IH _ _ E).
      rewrite Nat.pow_succ_r', qnat_mul; change (qnat 2%nat) with 2; nra.
Qed.

Fixpoint tail_cut_rev u ds : option (list Word*list Word) :=
  match u with
  | [] => None
  | WT::u => Some (rev_append u [WT], ds)
  | w::u => tail_cut_rev u (w::ds)
  end.

Lemma tail_cut_rev_spec u : forall ds p tail, tail_cut_rev u ds=Some(p,tail) ->
  forallb is_digit ds=true ->
  rev_append u ds=p++tail /\ forallb is_digit tail=true.
Proof.
  induction u as [|w u IH]; intros ds p tail E D; [discriminate|].
  destruct w; cbn[tail_cut_rev] in E.
  - inversion E; subst; split; [|exact D].
    repeat rewrite rev_append_rev; cbn[rev]; rewrite <-app_assoc; reflexivity.
  - apply (IH _ _ _ E); exact D.
  - apply (IH _ _ _ E); exact D.
Qed.

Definition tail_cut u := tail_cut_rev (rev_append u []) [].

Lemma tail_cut_spec u p ds : tail_cut u=Some(p,ds) ->
  u=p++ds /\ forallb is_digit ds=true.
Proof.
  intro E; destruct (tail_cut_rev_spec _ _ _ _ E eq_refl) as [U D].
  repeat rewrite rev_append_rev in U; repeat rewrite app_nil_r in U.
  rewrite rev_involutive in U; auto.
Qed.

Definition c24_weight_check u ds :=
  N.leb (rounded (37*65536)%N (29*65536)%N (rev_append u [])
    (rounded (8*65536)%N 0%N (rev_append ds []) 0%N)) 8%N.

Lemma c24_weight_check_spec u ds : c24_weight_check u ds=true ->
  (29#8)*mass u+zeros u+scale u*zeros ds <= (1#65536).
Proof.
  unfold c24_weight_check; intro E; apply N.leb_le in E; apply qN_le in E.
  pose proof (rounded_forward (8*65536)%N 0%N ds 0%N) as D.
  pose proof (rounded_forward (37*65536)%N (29*65536)%N u
    (rounded (8*65536)%N 0%N (rev_append ds []) 0%N)) as U.
  change (qN 0%N) with 0 in D; change (qN 8%N) with 8 in E.
  change (qN (8*65536)%N) with 524288 in D.
  change (qN (37*65536)%N) with 2424832 in U.
  change (qN (29*65536)%N) with 1900544 in U.
  pose proof (scale_pos u); rewrite mass_split; nra.
Qed.

Definition c24_check u :=
  match tail_cut u with
  | None => false
  | Some(p,ds) =>
    match heightN p 0%nat with
    | None => false
    | Some H => if Nat.eqb H (length ds) then
        match strip_words (W1::repeat W0 6) ds,
              strip_words (repeat W1 15) (rev_append ds []) with
        | Some _, Some _ => c24_weight_check p ds
        | _, _ => false end
      else false
    end
  end.

Lemma c24_check_spec u : c24_check u=true -> C24Good (1#65536) (to_side u 0inf).
Proof.
  unfold c24_check; destruct (tail_cut u) as [[p ds]|] eqn:C; [|discriminate].
  destruct (heightN p 0) as [H|] eqn:U; [|discriminate].
  destruct (Nat.eqb H (length ds)) eqn:L; [apply Nat.eqb_eq in L; subst H|discriminate].
  destruct (strip_words (W1::repeat W0 6) ds) as [lo|] eqn:Lo; [|discriminate].
  destruct (strip_words (repeat W1 15) (rev_append ds [])) as [hi|] eqn:Hi; [|discriminate].
  intro W; destruct (tail_cut_spec _ _ _ C) as [-> D].
  destruct (digit_list _ D) as [A DA].
  apply (C24Good_intro (1#65536) p A (length ds) ds DA).
  - apply heightN_spec in U; exact U.
  - apply c24_weight_check_spec; exact W.
  - apply strip_words_spec in Lo; exists lo; exact Lo.
  - apply strip_words_spec in Hi; unfold high15; exists (rev hi).
    rewrite rev_append_rev, app_nil_r in Hi.
    apply (f_equal (@rev Word)) in Hi.
    rewrite rev_involutive, rev_app_distr, rev_repeat in Hi; exact Hi.
Qed.

Definition c24_roundN u :=
  match cscan 2%N u with
  | None => None
  | Some v => match cscan 4%N v with
              | None => None | Some w => Some (WT::w) end
  end.

Inductive C24Rounds : side -> side -> Prop :=
| C24Rounds_refl r : C24Rounds r r
| C24Rounds_next r s v w : RIncs 2 r s -> RIncs 4 s v ->
    C24Rounds (t*>v) w -> C24Rounds r w.

Fixpoint c24_verify n u :=
  match n with
  | O => c24_check u
  | S n => match c24_roundN u with None => false | Some v => c24_verify n v end
  end.

Lemma c24_verify_spec n : forall u, c24_verify n u=true ->
  exists r, C24Rounds (to_side u 0inf) r /\ C24Good (1#65536) r.
Proof.
  induction n as [|n IH]; intros u E.
  - exists (to_side u 0inf); split; [constructor|apply c24_check_spec; exact E].
  - change ((match c24_roundN u with Some v => c24_verify n v | None => false end)=true) in E.
    unfold c24_roundN in E.
    destruct (cscan 2%N u) as [v|] eqn:V; [|discriminate].
    destruct (cscan 4%N v) as [w|] eqn:W; [|discriminate].
    destruct (IH _ E) as [r [R G]]; exists r; split; [|exact G].
    eapply C24Rounds_next; [apply (cscan_spec _ _ _ V)|apply (cscan_spec _ _ _ W)|exact R].
Qed.

Lemma c24_entry13_check : c24_verify 9 c24_start13=true.
Proof. vm_compute; reflexivity. Qed.

Lemma c24_entry14_check : c24_verify 19 c24_start14=true.
Proof. vm_compute; reflexivity. Qed.

Close Scope Q.
Open Scope nat.


Section Soundness.
Variable tm : TM.
Variables h j p : list (DH0*DH0).

Inductive Num : nat -> list Sym -> list (DH0*DH0) -> Prop :=
| Num0 : Num 0 one []
| Num1 n : Num (1+n*2) [] (p++h^^n)
| Num2 n : Num (2+n*2) [] (j++h^^n).

Definition Counter k r r' :=
  forall w hs, Num k w hs -> sideRLs tm hs (w*>r) r'.

Hypothesis T_odd : forall n,
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.

Hypothesis T_even : forall n,
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.

Hypothesis Pair_00 : segRLs tm p [] (d1++d0) (t++one).

Hypothesis Pair_01 : forall n,
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.

Hypothesis Pair_02 : forall n,
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.

Hypothesis Pair_11 : forall n,
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.

Hypothesis Pair_12 : forall n,
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.

Hypothesis Short_00 : segRLs tm j [] d0 (d0++one).

Hypothesis Short_01 : forall n,
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.

Hypothesis Short_02 : forall n,
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.

Hypothesis Short_10 : segRLs tm (j++h) [] d0 (d1++one).

Hypothesis Short_11 : forall n,
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.

Hypothesis Short_12 : forall n,
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.

Lemma Counter_zero r r' : Counter 0 r r' -> r'=one*>r.
Proof. intro I; specialize (I _ _ Num0); inverts I; reflexivity. Qed.

Lemma Counter_T n r r' :
  Counter ((1+n)*2) r r' -> Counter (1+n) (t*>r) (t*>r').
Proof.
  intros I w hs H; inversion H as [|m|m]; subst; try lia; cbn.
  - eapply (segRLs_sideRLs_concat (T_odd m)).
    apply (I []); applys_eq (Num2 (m*2)); flia.
  - eapply (segRLs_sideRLs_concat (T_even m)).
    apply (I []); applys_eq (Num2 (1+m*2)); flia.
Qed.

Lemma Counter_pair0 n r r' :
  Counter (n*2) r r' -> Counter (1+n) (d1*>d0*>r) (t*>r').
Proof.
  intros I w hs H; inversion H as [|m|m]; subst; try lia.
  - destruct m as [|m].
    + apply Counter_zero in I; subst r'.
      cbn[Nat.add Nat.mul lpow]; repeat rewrite app_nil_r.
      eapply (segRLs_sideRLs_concat Pair_00); constructor.
    + eapply (segRLs_sideRLs_concat (Pair_01 m)).
      apply (I []); applys_eq (Num2 (1+m*2)); flia.
  - eapply (segRLs_sideRLs_concat (Pair_02 m)).
    apply (I []); applys_eq (Num2 (m*2)); flia.
Qed.

Lemma Counter_pair1 n r r' :
  Counter (1+n*2) r r' -> Counter (1+n) (d1*>d1*>r) (t*>r').
Proof.
  intros I w hs H; inversion H as [|m|m]; subst; try lia.
  - eapply (segRLs_sideRLs_concat (Pair_11 m)).
    apply (I []); applys_eq (Num1 (m*2)); flia.
  - eapply (segRLs_sideRLs_concat (Pair_12 m)).
    apply (I []); applys_eq (Num1 (1+m*2)); flia.
Qed.

Lemma Counter_short00 n r r' :
  Counter (n*2) r r' -> Counter (2+n*4) (d0*>r) (d0*>r').
Proof.
  intros I w hs H; inversion H as [|m|m]; subst; try lia.
  assert (m=n*2) by lia; subst m.
  destruct n as [|n].
  - apply Counter_zero in I; subst r'.
    cbn[Nat.add Nat.mul lpow]; repeat rewrite app_nil_r.
    eapply (segRLs_sideRLs_concat Short_00); constructor.
  - eapply (segRLs_sideRLs_concat (Short_01 n)).
    apply (I []); applys_eq (Num2 n); flia.
Qed.

Lemma Counter_short01 n r r' :
  Counter (1+n*2) r r' -> Counter (2+n*4) (d1*>r) (d0*>r').
Proof.
  intros I w hs H; inversion H as [|m|m]; subst; try lia.
  assert (m=n*2) by lia; subst m.
  eapply (segRLs_sideRLs_concat (Short_02 n)).
  apply (I []); constructor.
Qed.

Lemma Counter_short10 n r r' :
  Counter (n*2) r r' -> Counter (4+n*4) (d0*>r) (d1*>r').
Proof.
  intros I w hs H; inversion H as [|m|m]; subst; try lia.
  assert (m=1+n*2) by lia; subst m.
  destruct n as [|n].
  - apply Counter_zero in I; subst r'.
    cbn[Nat.add Nat.mul lpow]; repeat rewrite app_nil_r.
    eapply (segRLs_sideRLs_concat Short_10); constructor.
  - eapply (segRLs_sideRLs_concat (Short_11 n)).
    apply (I []); applys_eq (Num2 n); flia.
Qed.

Lemma Counter_short11 n r r' :
  Counter (1+n*2) r r' -> Counter (4+n*4) (d1*>r) (d1*>r').
Proof.
  intros I w hs H; inversion H as [|m|m]; subst; try lia.
  assert (m=1+n*2) by lia; subst m.
  eapply (segRLs_sideRLs_concat (Short_12 n)).
  apply (I []); constructor.
Qed.

Lemma RIncs_spec k r r' : RIncs k r r' -> Counter k r r'.
Proof.
  intro I; induction I; eauto using Counter_T, Counter_pair0, Counter_pair1,
    Counter_short00, Counter_short01, Counter_short10, Counter_short11.
  intros w hs H; inverts H; try lia; constructor.
Qed.

End Soundness.
End CCore.
Import CCore.
Open Scope nat.

Lemma rounds_sound tm C :
  (forall r r', RIncs 6 r r' -> C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  forall r r', Rounds r r' -> C r -[tm]->* C r'.
Proof.
  intros Step r r' I; induction I; [constructor|].
  eapply evstep_trans; [apply progress_evstep, Step, H|apply IHI].
Qed.

Lemma good_nonhalt tm C :
  (forall r r', RIncs 6 r r' -> C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  forall r, Good r -> ~halts tm (C r).
Proof.
  intros Step r G; eapply progress_nonhalt_cond with (P:=Good); [|apply G].
  intros s I; destruct (C6_closed _ I) as [s' [R G']].
  exists ([S1;S1;S0;S0]*>s'); split; [apply Step, R|apply G'].
Qed.

Lemma c24_good_nonhalt tm C :
  (forall r s r', RIncs 2 r s -> RIncs 4 s r' -> C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  forall r, C24Good (1#65536) r -> ~halts tm (C r).
Proof.
  intros Step r G; eapply progress_nonhalt_cond with (P:=C24Good (1#65536)); [|apply G].
  intros s I; destruct (C24_closed _ I) as [u [s' [A [B G']]]].
  exists ([S1;S1;S0;S0]*>s'); split; [eapply Step; eassumption|apply G'].
Qed.

Lemma c24_rounds_sound tm C :
  (forall r s r', RIncs 2 r s -> RIncs 4 s r' ->
    C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  forall r r', C24Rounds r r' -> C r -[tm]->* C r'.
Proof.
  intros Step r r' I; induction I; [constructor|].
  eapply evstep_trans; [eapply progress_evstep, Step; eassumption|apply IHI].
Qed.

Lemma c24_entry_nonhalt tm C n u :
  (forall r s r', RIncs 2 r s -> RIncs 4 s r' ->
    C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  c0 -[tm]->* C (to_side u 0inf) -> c24_verify n u=true -> ~halts tm c0.
Proof.
  intros Step Init E; destruct (c24_verify_spec _ _ E) as [r [R G]].
  eapply multistep_nonhalt; [apply Init|].
  eapply multistep_nonhalt.
  - apply (c24_rounds_sound tm C Step _ _ R).
  - apply (c24_good_nonhalt tm C Step _ G).
Qed.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [((B,[S1]),hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (A,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>d1*>d1*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry2_reach).
  - apply (good_nonhalt tm Config BigStep _ entry2_good).
Qed.

End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation h := [((C,[S1]),hL)].
Notation j := [((B,[S1;S1]),hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (B,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>d0*>t*>d0*>d1*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry3_reach).
  - apply (good_nonhalt tm Config BigStep _ entry3_good).
Qed.

End TM3.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC1RF_1LA1RC_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (A,[S0]).
Notation hR := (E,[S1]).
Notation h := [((E,[S1]),hL)].
Notation j := [((C,[S1;S1]),hL)].
Notation p := [((C,[S1;S0]),hL)].
Notation aR := (C,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>t*>d0*>d1*>d1*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry4_reach).
  - apply (good_nonhalt tm Config BigStep _ entry4_good).
Qed.

End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (E,[S0]).
Notation hR := (D,[S1]).
Notation h := [((D,[S1]),hL)].
Notation j := [((C,[S1;S1]),hL)].
Notation p := [((C,[S1;S0]),hL)].
Notation aR := (C,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry5_reach).
  - apply (good_nonhalt tm Config BigStep _ entry5_good).
Qed.

End TM5.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC1RF_1LA1RC_1RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (A,[S0]).
Notation hR := (E,[S1]).
Notation h := [((E,[S1]),hL)].
Notation j := [((C,[S1;S1]),hL)].
Notation p := [((C,[S1;S0]),hL)].
Notation aR := (C,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>t*>d0*>d1*>d1*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry4_reach).
  - apply (good_nonhalt tm Config BigStep _ entry4_good).
Qed.

End TM6.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation h := [((C,[S1]),hL)].
Notation j := [((B,[S1;S1]),hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (B,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>d0*>t*>d0*>d1*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry3_reach).
  - apply (good_nonhalt tm Config BigStep _ entry3_good).
Qed.

End TM7.

Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [((B,[S1]),hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (A,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>d1*>d1*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry2_reach).
  - apply (good_nonhalt tm Config BigStep _ entry2_good).
Qed.

End TM8.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (E,[S0]).
Notation hR := (D,[S1]).
Notation h := [((D,[S1]),hL)].
Notation j := [((C,[S1;S1]),hL)].
Notation p := [((C,[S1;S0]),hL)].
Notation aR := (C,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^2) [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r r' : RIncs 6 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I.
  unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 2).
Qed.

Lemma init : c0 -->* Config (t*>0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt.
  - apply (rounds_sound tm Config BigStep _ _ entry5_reach).
  - apply (good_nonhalt tm Config BigStep _ entry5_good).
Qed.

End TM9.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation jR := (A,[S1;S1]).
Notation h := [(hR,hL)].
Notation j := [(jR,hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (A,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm a j [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,jR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r s r' : RIncs 2 r s -> RIncs 4 s r' -> Config r -->+ Config (t*>r').
Proof.
  intros I J; apply RIncs_sound in I, J; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++j).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply @sideRLs_trans with (r2:=t*>s).
    + eapply (segRLs_sideRLs_concat RSend).
      apply (I []); apply (@Num2 h j p 0).
    + eapply (segRLs_sideRLs_concat (T_even 0)).
      apply (J []); apply (@Num2 h j p 1).
Qed.

Lemma init : c0 -->* Config (to_side c24_start13 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply c24_entry_nonhalt; [apply BigStep|apply init|apply c24_entry13_check]. Qed.

End TM13.

Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation jR := (B,[S1;S1]).
Notation h := [(hR,hL)].
Notation j := [(jR,hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (B,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm a j [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,jR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r s r' : RIncs 2 r s -> RIncs 4 s r' -> Config r -->+ Config (t*>r').
Proof.
  intros I J; apply RIncs_sound in I, J; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++j).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply @sideRLs_trans with (r2:=t*>s).
    + eapply (segRLs_sideRLs_concat RSend).
      apply (I []); apply (@Num2 h j p 0).
    + eapply (segRLs_sideRLs_concat (T_even 0)).
      apply (J []); apply (@Num2 h j p 1).
Qed.

Lemma init : c0 -->* Config (to_side c24_start14 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply c24_entry_nonhalt; [apply BigStep|apply init|apply c24_entry14_check]. Qed.

End TM14.

Module TM15.
Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation jR := (B,[S1;S1]).
Notation h := [(hR,hL)].
Notation j := [(jR,hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (B,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm a j [] t.
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,jR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} r.

Lemma BigStep r s r' : RIncs 2 r s -> RIncs 4 s r' -> Config r -->+ Config (t*>r').
Proof.
  intros I J; apply RIncs_sound in I, J; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++j).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply @sideRLs_trans with (r2:=t*>s).
    + eapply (segRLs_sideRLs_concat RSend).
      apply (I []); apply (@Num2 h j p 0).
    + eapply (segRLs_sideRLs_concat (T_even 0)).
      apply (J []); apply (@Num2 h j p 1).
Qed.

Lemma init : c0 -->* Config (to_side c24_start14 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply c24_entry_nonhalt; [apply BigStep|apply init|apply c24_entry14_check]. Qed.

End TM15.

(* The fixed leading T turns two @ calls into the common C2/C4 round. *)
Module TM36.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1LD0LC_0LE0LA_1RF---_1RA1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [(hR,hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (A,<[S1;S1;S0;S1]).
Notation a := [(aR,hL)].

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_odd n :
  segRLs tm (p++h^^n) (j++h^^(n*2)) t t.
Proof. am (p) (j) 1 2 n 0 0. Qed.

Lemma T_even n :
  segRLs tm (j++h^^n) (j++h^^(1+n*2)) t t.
Proof. am (j) (j) 1 2 n 0 1. Qed.

Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma RIncs_sound k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply RIncs_spec;
    eauto using T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend1 : segRLs tm a j t (d0++t).
Proof. esc. Qed.

Lemma RSend2 : segRLs tm a (j++h) (d0++t) (t++t).
Proof. esc. Qed.

Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,aR)] 0inf 0inf.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=[]); reflexivity. Qed.

Definition Config r := 0inf {{{ (hL,L) }}} (t*>r).

Lemma BigStep r s r' : RIncs 2 r s -> RIncs 4 s r' -> Config r -->+ Config (t*>r').
Proof.
  intros I J; apply RIncs_sound in I, J; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++a).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply @sideRLs_trans with (r2:=d0*>t*>s).
    + eapply (segRLs_sideRLs_concat RSend1).
      apply (I []); apply (@Num2 h j p 0).
    + eapply (segRLs_sideRLs_concat RSend2).
      apply (J []); apply (@Num2 h j p 1).
Qed.

Lemma init : c0 -->* Config (to_side c24_start13 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply c24_entry_nonhalt; [apply BigStep|apply init|apply c24_entry13_check]. Qed.

End TM36.

(* The compensated family retains the extra right-hand carry at every T. *)
Module PCore.

(* Pure # calls; the T clause here does NOT generate an extra call. *)
Inductive Sharp : nat -> side -> side -> Prop :=
| Sharp_0 r : Sharp 0 r r
| Sharp_T n r r' : Sharp (n*2) r r' -> Sharp n (t*>r) (t*>r')
| Sharp_00 n r r' : Sharp n r r' -> Sharp (n*2) (d0*>r) (d0*>r')
| Sharp_01 n r r' : Sharp n r r' -> Sharp (1+n*2) (d0*>r) (d1*>r')
| Sharp_10 n r r' : Sharp n r r' -> Sharp (n*2) (d1*>r) (d1*>r')
| Sharp_11 n r r' : Sharp (1+n) r r' -> Sharp (1+n*2) (d1*>r) (d0*>r')
| Sharp_blank : Sharp 1 0inf (d1*>0inf).

Lemma Binary_Sharp A H r : Binary A H r -> Sharp A 0inf r.
Proof.
  intro I; induction I.
  - apply Sharp_blank.
  - do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (Sharp_00 (1+n)); flia; apply IHI.
  - do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (Sharp_01 (1+n)); flia; apply IHI.
Qed.

Lemma Sharp_ex u : forall n, exists v, Sharp n (to_side u 0inf) (to_side v 0inf).
Proof.
  induction u as [|w u IH]; intro n.
  - destruct n as [|n]; [exists (@nil Word); constructor|].
    destruct (Binary_ex n) as [H [r B]].
    destruct (Binary_words _ _ _ B) as [v [D <-]].
    exists v; eapply Binary_Sharp, B.
  - destruct w.
    + destruct (IH (n*2)) as [v I]; exists (WT::v); apply Sharp_T, I.
    + destruct (mod2 n); subst n;
        destruct (IH a) as [v I]; [exists (W0::v)|exists (W1::v)]; constructor; apply I.
    + destruct (mod2 n); subst n.
      * destruct (IH a) as [v I]; exists (W1::v); apply Sharp_10, I.
      * destruct (IH (1+a)) as [v I]; exists (W0::v); apply Sharp_11, I.
Qed.

(* Unlike CCore, T generates a right-hand #, executed BEFORE the new C. *)
Inductive RIncs : nat -> side -> side -> Prop :=
| RIncs_0 r : RIncs 0 r (one*>r)
| RIncs_T1 r s : Sharp 1 r s -> RIncs 1 (t*>r) (t*>S0>>s)
| RIncs_T2 r s : Sharp 1 r s -> RIncs 2 (t*>r) (t*>one*>s)
| RIncs_T n r s r' : Sharp 1 r s -> RIncs (2+n*2) s r' ->
    RIncs (3+n) (t*>r) (t*>r')
| RIncs_pair0 n r r' : RIncs (n*2) r r' ->
    RIncs (1+n) (d1*>d0*>r) (t*>r')
| RIncs_pair1 n r r' : RIncs (1+n*2) r r' ->
    RIncs (1+n) (d1*>d1*>r) (t*>r')
| RIncs_short00 n r r' : RIncs (n*2) r r' ->
    RIncs (2+n*4) (d0*>r) (d0*>r')
| RIncs_short01 n r r' : RIncs (1+n*2) r r' ->
    RIncs (2+n*4) (d1*>r) (d0*>r')
| RIncs_short10 n r r' : RIncs (n*2) r r' ->
    RIncs (4+n*4) (d0*>r) (d1*>r')
| RIncs_short11 n r r' : RIncs (1+n*2) r r' ->
    RIncs (4+n*4) (d1*>r) (d1*>r').

Definition Packet k b r r' := exists s, Sharp b r s /\ RIncs k s r'.

Lemma Packet_zero k r r' : RIncs k r r' -> Packet k 0 r r'.
Proof. intro I; exists r; split; [constructor|apply I]. Qed.

Lemma Binary_RIncs A H r : Binary A H r -> RIncs ((A-1)*2) 0inf r.
Proof.
  intro I; induction I.
  - change (RIncs 0 0inf (S1>>S0>>0inf)); rewrite <-const_unfold; constructor.
  - do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (RIncs_short00 n); flia; applys_eq IHI; flia.
  - do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (RIncs_short10 n); flia; applys_eq IHI; flia.
Qed.

(* Virtual effective input: unlike Sharp, T also adds the emitted #.
   This is a finite-prefix bookkeeping relation, not a physical tape step. *)
Inductive Effective : nat -> list Word -> nat -> list Word -> Prop :=
| Effective_nil n : Effective n [] n []
| Effective_T n u b v : Effective (1+n*2) u b v ->
    Effective n (WT::u) b (WT::v)
| Effective_00 n u b v : Effective n u b v ->
    Effective (n*2) (W0::u) b (W0::v)
| Effective_01 n u b v : Effective n u b v ->
    Effective (1+n*2) (W0::u) b (W1::v)
| Effective_10 n u b v : Effective n u b v ->
    Effective (n*2) (W1::u) b (W1::v)
| Effective_11 n u b v : Effective (1+n) u b v ->
    Effective (1+n*2) (W1::u) b (W0::v).

Lemma Effective_ex u : forall n, exists b v, Effective n u b v.
Proof.
  induction u as [|w u IH]; intro n.
  - exists n, (@nil Word); constructor.
  - destruct w.
    + destruct (IH (1+n*2)) as [b [v I]]; exists b, (WT::v); constructor; apply I.
    + destruct (mod2 n); subst n; destruct (IH a) as [b [v I]];
        [exists b, (W0::v)|exists b, (W1::v)]; constructor; apply I.
    + destruct (mod2 n); subst n.
      * destruct (IH a) as [b [v I]]; exists b, (W1::v); constructor; apply I.
      * destruct (IH (1+a)) as [b [v I]]; exists b, (W0::v); constructor; apply I.
Qed.

Lemma Effective_app n u b v : Effective n u b v -> forall w c x,
  Effective b w c x -> Effective n (u++w) c (v++x).
Proof. intro I; induction I; cbn[app]; intros; eauto using Effective. Qed.

Lemma Effective_length n u b v : Effective n u b v -> length u=length v.
Proof. intro I; induction I; cbn[length]; congruence. Qed.

Lemma Effective_digits n u b v : Effective n u b v -> forall A H,
  Digits A H u -> exists B, Digits B H v /\ A+n=B+b*2^H.
Proof.
  intro I; induction I; intros A H D; inversion D; subst.
  1: { exists 0; split; [constructor|cbn[Nat.pow]; lia]. }
  all: match goal with D':Digits _ _ _ |- _ =>
    destruct (IHI _ _ D') as [B [Bv E]] end.
  - exists (B*2); split; [apply Digits_zero, Bv|cbn[Nat.add Nat.pow]; nia].
  - exists (1+B*2); split; [apply Digits_one, Bv|cbn[Nat.add Nat.pow]; nia].
  - exists (1+B*2); split; [apply Digits_one, Bv|cbn[Nat.add Nat.pow]; nia].
  - exists (B*2); split; [apply Digits_zero, Bv|cbn[Nat.add Nat.pow]; nia].
Qed.

Lemma Effective_digits_Sharp n u b v : Effective n u b v -> forall A H r r',
  Digits A H u -> Sharp b r r' -> Sharp n (to_side u r) (to_side v r').
Proof.
  intro I; induction I; intros A H r r' D S; inversion D; subst; cbn[to_side];
    eauto using Sharp.
Qed.

Lemma Digits_bound A H u : Digits A H u -> A<2^H.
Proof. intro I; induction I; cbn[Nat.add Nat.pow]; lia. Qed.

Lemma Effective_compensate n ds A H B : Digits A H ds ->
  A+n=B+2^H -> B<2^H -> exists v, Digits B H v /\
    Effective n (ds++[W1]) 1 (v++[W0]).
Proof.
  intros D Sum Bound; destruct (Effective_ex ds n) as [b [v E]].
  destruct (Effective_digits _ _ _ _ E _ _ D) as [C [V Eq]].
  pose proof (Digits_bound _ _ _ V).
  assert (b=1) by (destruct b as [|[|b]]; cbn[Nat.mul] in Eq; nia).
  subst b; assert (C=B) by nia; subst C.
  exists v; split; [apply V|].
  eapply Effective_app; [apply E|apply (Effective_11 0); constructor].
Qed.

Section Weights.
Local Open Scope Q_scope.

Ltac qnorm :=
  repeat (rewrite qnat_add in * || rewrite qnat_mul in * || rewrite qnat_S in *);
  change (qnat 0%nat) with 0 in *; change (qnat 1%nat) with 1 in *;
  change (qnat 2%nat) with 2 in *; change (qnat 4%nat) with 4 in *.

Lemma Effective_weights n u b v : Effective n u b v ->
  scale v==scale u /\ mass v==mass u.
Proof. intro I; induction I; cbn[scale mass] in *; lra. Qed.

Lemma Effective_budget n u b v : Effective n u b v ->
  qnat (1+b)%nat*scale u == qnat (1+n)%nat+mass u+ones u-ones v.
Proof.
  intro I; induction I; cbn[scale mass ones] in *; qnorm; nra.
Qed.

Lemma Effective_bounds n u b v : Effective n u b v ->
  qnat (1+n)%nat <= qnat (1+b)%nat*scale u /\
  qnat (1+b)%nat*scale u <= qnat (1+n)%nat+2*mass u.
Proof.
  intro I; pose proof (Effective_budget _ _ _ _ I).
  pose proof (Effective_weights _ _ _ _ I).
  pose proof (mass_split u); pose proof (mass_split v).
  pose proof (weights_nonneg u); pose proof (weights_nonneg v); lra.
Qed.

(* Effective-input scan. Positive and negative budget losses are separate:
   a pair can increase k-4, so the net loss must NOT be assumed monotone. *)
Inductive Scan : nat -> list Word -> nat -> list Word -> QArith_base.Q -> QArith_base.Q -> Prop :=
| Scan_nil k : Scan k [] k [] 0 0
| Scan_T n u k v a b : Scan (2+n*2)%nat u k v a b ->
    Scan (3+n)%nat (WT::u) k (WT::v) (a*(1#2)) (b*(1#2))
| Scan_pair0 n u k v a b : Scan (n*2)%nat u k v a b ->
    Scan (1+n)%nat (W1::W0::u) k (WT::v) (a*(1#2)) ((1+b)*(1#2))
| Scan_pair1 n u k v a b : Scan (1+n*2)%nat u k v a b ->
    Scan (1+n)%nat (W1::W1::u) k (WT::v) (a*(1#2)) ((3#4)+b*(1#2))
| Scan_short00 n u k v a b : Scan (n*2)%nat u k v a b ->
    Scan (2+n*4)%nat (W0::u) k (W0::v) (3+a*2) (b*2)
| Scan_short01 n u k v a b : Scan (1+n*2)%nat u k v a b ->
    Scan (2+n*4)%nat (W1::u) k (W0::v) (2+a*2) (b*2)
| Scan_short10 n u k v a b : Scan (n*2)%nat u k v a b ->
    Scan (4+n*4)%nat (W0::u) k (W1::v) (4+a*2) (b*2)
| Scan_short11 n u k v a b : Scan (1+n*2)%nat u k v a b ->
    Scan (4+n*4)%nat (W1::u) k (W1::v) (3+a*2) (b*2).

Lemma Scan_budget k u k' v a b : Scan k u k' v a b ->
  qnat k-4 == (qnat k'-4)*scale v+2*(a-b).
Proof.
  intro I; induction I; cbn[scale] in *; qnorm; nra.
Qed.

Lemma Scan_bounds k u k' v a b : Scan k u k' v a b ->
  mass v<=mass u /\ 0<=a /\ a<=4*mass u /\ 0<=b /\ b<=mass u*(1#4).
Proof.
  intro I; induction I; cbn[mass] in *;
    try match goal with _:Scan _ ?u _ _ _ _ |- _ => pose proof (weights_nonneg u) end; lra.
Qed.

Lemma Scan_end_positive k u k' v a b : Scan k u k' v a b ->
  8*mass u<qnat k-4 -> (4<k')%nat.
Proof.
  intros I Bound; pose proof (Scan_budget _ _ _ _ _ _ I).
  pose proof (Scan_bounds _ _ _ _ _ _ I); pose proof (scale_pos v).
  apply qnat_lt; change (qnat 4%nat) with 4; nra.
Qed.

Lemma Scan_app k u k' v a b : Scan k u k' v a b -> forall w k'' x c d,
  Scan k' w k'' x c d -> exists a' b',
  Scan k (u++w) k'' (v++x) a' b' /\
  a'==a+scale v*c /\ b'==b+scale v*d.
Proof.
  intro I; induction I; intros w k'' x c d J; cbn[app scale].
  1: { exists c, d; split; [apply J|split; ring]. }
  all: destruct (IHI _ _ _ _ _ J) as [a' [b' [K [A B]]]];
    eexists _, _; split; [econstructor; apply K|split; lra].
Qed.

Lemma Scan_ex_mode e u (I : Parse e u) : forall k,
  (e=true -> exists n, k=(n*2)%nat) -> 8*mass u<qnat k-4 ->
  exists b v lp lm, Scan k u b v lp lm /\ (4<b)%nat.
Proof.
  induction I; intros k Ek Hk.
  - exists k, (@nil Word), 0, 0; split; [constructor|].
    apply qnat_lt; cbn[mass] in Hk; qnorm; lra.
  - pose proof (weights_nonneg u) as Wu.
    destruct k as [|[|[|k]]]; try solve [cbn[mass] in Hk; qnorm; nra].
    edestruct (IHI (2+k*2)%nat) as [b [v [lp [lm [H B]]]]].
    + intro; exists (1+k)%nat; lia.
    + cbn[mass] in Hk; qnorm; nra.
    + exists b, (WT::v), (lp*(1#2)), (lm*(1#2)); split; [apply Scan_T, H|apply B].
  - pose proof (weights_nonneg u) as Wu; destruct (Ek eq_refl) as [n ->].
    destruct (mod2 n); subst n.
    + destruct a as [|a]; [cbn[mass] in Hk; qnorm; nra|].
      edestruct (IHI (a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * intro; eexists; reflexivity.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W1::v), (4+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short10 a); flia; apply H.
    + edestruct (IHI (a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * intro; eexists; reflexivity.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W0::v), (3+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short00 a); flia; apply H.
  - pose proof (weights_nonneg u) as Wu; destruct (Ek eq_refl) as [n ->].
    destruct (mod2 n); subst n.
    + destruct a as [|a]; [cbn[mass] in Hk; qnorm; nra|].
      edestruct (IHI (1+a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * discriminate.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W1::v), (3+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short11 a); flia; apply H.
    + edestruct (IHI (1+a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * discriminate.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W0::v), (2+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short01 a); flia; apply H.
  - pose proof (weights_nonneg u) as Wu.
    destruct k as [|k]; [cbn[mass] in Hk; qnorm; nra|].
    edestruct (IHI (k*2)%nat) as [b [v [lp [lm [H B]]]]].
    + intro; eexists; reflexivity.
    + cbn[mass] in Hk; qnorm; nra.
    + exists b, (WT::v), (lp*(1#2)), ((1+lm)*(1#2)); split; [apply Scan_pair0, H|apply B].
  - pose proof (weights_nonneg u) as Wu.
    destruct k as [|k]; [cbn[mass] in Hk; qnorm; nra|].
    edestruct (IHI (1+k*2)%nat) as [b [v [lp [lm [H B]]]]].
    + discriminate.
    + cbn[mass] in Hk; qnorm; nra.
    + exists b, (WT::v), (lp*(1#2)), ((3#4)+lm*(1#2)); split; [apply Scan_pair1, H|apply B].
Qed.

Lemma Scan_ex u k : 8*mass u<qnat (k*2)%nat-4 ->
  exists b v lp lm, Scan (k*2)%nat u b v lp lm /\ (4<b)%nat.
Proof.
  intro H; eapply Scan_ex_mode; [apply (proj1 (Parse_all u))| |apply H].
  intro; eexists; reflexivity.
Qed.

Lemma Scan_digits_from_core k u k' v l : CCore.Scan k u k' v l -> forall A H,
  Digits A H u -> exists a b, Scan k u k' v a b /\ a<=3*mass v+l /\ b<=3*l.
Proof.
  intro I; induction I; intros A H D; inversion D; subst.
  1: { exists 0, 0; split; [constructor|cbn[mass]; lra]. }
  all: repeat match goal with D:Digits _ _ (_::_) |- _ => inversion D; subst; clear D end.
  all: match goal with D:Digits _ _ _ |- _ =>
    destruct (IHI _ _ D) as [a [b [J [P M]]]] end.
  - exists (a*(1#2)), ((1+b)*(1#2)); split; [apply Scan_pair0, J|cbn[mass]; lra].
  - exists (a*(1#2)), ((3#4)+b*(1#2)); split; [apply Scan_pair1, J|cbn[mass]; lra].
  - exists (3+a*2), (b*2); split; [apply Scan_short00, J|cbn[mass]; lra].
  - exists (2+a*2), (b*2); split; [apply Scan_short01, J|cbn[mass]; lra].
  - exists (4+a*2), (b*2); split; [apply Scan_short10, J|cbn[mass]; lra].
  - exists (3+a*2), (b*2); split; [apply Scan_short11, J|cbn[mass]; lra].
Qed.

Lemma Scan_digits_to_core k u k' v a b : Scan k u k' v a b -> forall A H,
  Digits A H u -> exists l, CCore.Scan k u k' v l /\ a<=3*mass v+l /\ b<=3*l.
Proof.
  intro I; induction I; intros A H D; inversion D; subst.
  1: { exists 0; split; [constructor|cbn[mass]; lra]. }
  all: repeat match goal with D:Digits _ _ (_::_) |- _ => inversion D; subst; clear D end.
  all: match goal with D:Digits _ _ _ |- _ =>
    destruct (IHI _ _ D) as [l [J [P M]]] end.
  - exists ((1+l)*(1#2)); split; [apply CCore.Scan_pair0, J|cbn[mass]; lra].
  - exists ((1#4)+l*(1#2)); split; [apply CCore.Scan_pair1, J|cbn[mass]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short00, J|cbn[mass]; lra].
  - exists (l*2); split; [apply CCore.Scan_short01, J|cbn[mass]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short10, J|cbn[mass]; lra].
  - exists (l*2); split; [apply CCore.Scan_short11, J|cbn[mass]; lra].
Qed.

Lemma TailDigits_digits u z : TailDigits u z -> exists A H, Digits A H u.
Proof.
  intro I; induction I.
  - exists 0%nat, 1%nat; exact (Digits_zero 0 0 _ Digits_nil).
  - destruct IHI as [A [H D]]; eexists _, _; apply Digits_zero, D.
  - destruct IHI as [A [H D]]; eexists _, _; apply Digits_one, D.
Qed.

Lemma Scan_tail_bounds k u k' v a b : Scan k u k' v a b -> forall z,
  TailDigits u z -> mass v<=1+2*z /\ a<=4*(1+2*z) /\ b<=3*(1+2*z).
Proof.
  intros I z D; destruct (TailDigits_digits _ _ D) as [A [H B]].
  destruct (Scan_digits_to_core _ _ _ _ _ _ I _ _ B) as [l [J [P M]]].
  pose proof (CCore.Scan_tail_bounds _ _ _ _ _ J _ D); lra.
Qed.

Lemma Scan_tail_ex u z k : TailDigits u z ->
  2*(mass u+zeros u)<qnat (k*2)%nat -> 8*(1+2*z)<qnat (k*2)%nat-4 ->
  exists k' v a b, Scan (k*2)%nat u k' v a b /\ (4<k')%nat.
Proof.
  intros D Budget Loss; destruct (CCore.Scan_ex u k) as [k' [v [l [I K]]]]; [lra|].
  destruct (TailDigits_digits _ _ D) as [A [H B]].
  destruct (Scan_digits_from_core _ _ _ _ _ I _ _ B) as [a [b [J [P M]]]].
  exists k', v, a, b; split; [apply J|].
  pose proof (Scan_tail_bounds _ _ _ _ _ _ J _ D).
  pose proof (Scan_budget _ _ _ _ _ _ J).
  pose proof (Scan_bounds _ _ _ _ _ _ J); pose proof (scale_pos v).
  apply qnat_lt; change (qnat 4%nat) with 4; nra.
Qed.

Lemma Scan_scale k u k' v a b : Scan k u k' v a b -> scale v<=scale u.
Proof.
  intro I; induction I; cbn[scale] in *; try lra; pose proof (scale_pos u); lra.
Qed.

Lemma Scan_even_end k u k' v a b : Scan k u k' v a b ->
  cut_ok u=true -> u<>[] -> exists n, k'=(n*2)%nat.
Proof.
  intro I; induction I; intros C Ne.
  1: { contradiction. }
  all: destruct u as [|x u].
  all: try solve [inversion I; subst; cbn[cut_ok] in C; try discriminate;
    first [exists n; lia|exists (1+n)%nat; lia]].
  all: apply IHI; [eauto using cut_ok_tail|discriminate].
Qed.

Lemma C12_scan u A H ds : Digits A H ds ->
  scale u*qnat (2^H)%nat == 1 -> cut_ok u=true -> u<>[] ->
  mass u+scale u*(1+zeros ds)<=(1#128) ->
  exists k v a b, Scan 12 (u++ds++[W0]) k v a b /\ (4<k)%nat.
Proof.
  intros D Height Cut Ne Bound.
  pose proof (weights_nonneg u) as Wu; pose proof (weights_nonneg ds) as Wd.
  pose proof (scale_pos u) as Su.
  destruct (Scan_ex u 6) as [k [v [a [b [I K]]]]];
    [change (8*mass u<8); nra|].
  destruct (Scan_even_end _ _ _ _ _ _ I Cut Ne) as [n ->].
  pose proof (Scan_budget _ _ _ _ _ _ I) as Budget.
  pose proof (Scan_bounds _ _ _ _ _ _ I) as Loss.
  pose proof (Scan_scale _ _ _ _ _ _ I) as Sv.
  pose proof (scale_pos v) as Pv.
  change (8 == (qnat (n*2)%nat-4)*scale v+2*(a-b)) in Budget.
  assert (Carry : 7<(qnat (n*2)%nat-4)*scale v) by nra.
  pose proof (Digits_weights _ _ _ D) as [Sd [Md Od]].
  assert (Rest : 2*(mass (ds++[W0])+zeros (ds++[W0]))*scale v<7).
  { rewrite mass_app, zeros_app; cbn[mass zeros].
    assert (scale u*zeros ds<=(1#128)) by nra.
    assert (scale u*(3*scale ds-1+zeros ds)<4) by nra.
    assert (0<=3*scale ds-1+zeros ds) by nra.
    nra. }
  destruct (Scan_tail_ex (ds++[W0]) (zeros ds) n (Digits_tail _ _ _ D))
    as [k [w [c [d [J K']]]]].
  - nra.
  - assert (8*(1+2*zeros ds)*scale v<1) by nra; nra.
  - destruct (Scan_app _ _ _ _ _ _ I _ _ _ _ _ J) as [a' [b' [S _]]].
    exists k, (v++w), a', b'; auto.
Qed.

Lemma qpow_pos n : 0<qnat (2^n)%nat.
Proof. apply qnat_pos; lia. Qed.

Lemma repeat_T_weights n : mass (repeat WT n)==0 /\
  scale (repeat WT n)*qnat (2^n)%nat==1.
Proof.
  induction n; cbn[repeat mass scale Nat.pow]; [split; reflexivity|].
  rewrite qnat_mul; change (qnat 2%nat) with 2; nra.
Qed.

Lemma repeat_T_factor n x : scale (repeat WT n)*x*qnat (2^n)%nat==x.
Proof.
  induction n; cbn[repeat scale Nat.pow].
  - change (qnat 1%nat) with 1; ring.
  - rewrite qnat_mul; change (qnat 2%nat) with 2; nra.
Qed.

(* Split at the first zero; the following tail still includes its final zero. *)
Lemma core_low_odd r a b v l u z :
  CCore.Scan a ((repeat W1 (1+r*2)%nat++[W0])++u) b v l -> TailDigits u z ->
  mass v*qnat (2^(1+r))%nat<=1+2*z /\
  (l-(1#2))*qnat (2^(1+r))%nat<=1+2*z.
Proof.
  intros I Z.
  destruct (CCore.Scan_cut _ _ _ _ _ I _ _ eq_refl)
    as [c [x [y [s [t [J [K [-> L]]]]]]]];
    [left; rewrite cut_ok_last; reflexivity|].
  destruct (CCore.Scan_ones_odd r _ _ _ _ J) as [-> [_ S]].
  pose proof (CCore.Scan_tail_bounds _ _ _ _ _ K _ Z).
  pose proof (repeat_T_weights (1+r)%nat).
  pose proof (repeat_T_factor (1+r)%nat (mass y)).
  pose proof (repeat_T_factor (1+r)%nat t).
  pose proof (qpow_pos (1+r)%nat).
  rewrite mass_app; nra.
Qed.

Lemma core_low_even r a b v l u z :
  CCore.Scan a ((repeat W1 (2+r*2)%nat++[W0])++u) b v l -> TailDigits u z ->
  (mass v-1)*qnat (2^r)%nat<=1+2*z /\
  (l-1)*qnat (2^r)%nat<=1+2*z.
Proof.
  intros I Z.
  destruct (CCore.Scan_cut _ _ _ _ _ I _ _ eq_refl)
    as [c [x [y [s [t [J [K [-> L]]]]]]]];
    [left; rewrite cut_ok_last; reflexivity|].
  destruct (CCore.Scan_ones_even r _ _ _ _ J) as [d [n [-> [_ S]]]].
  pose proof (CCore.Scan_tail_bounds _ _ _ _ _ K _ Z).
  pose proof (repeat_T_weights (1+r)%nat).
  pose proof (repeat_T_factor (1+r)%nat (mass y)).
  pose proof (repeat_T_factor (1+r)%nat t).
  pose proof (qpow_pos r); pose proof (weights_nonneg y).
  rewrite mass_app; cbn[Nat.add Nat.pow] in *;
    rewrite qnat_mul in *; change (qnat 2%nat) with 2 in *.
  destruct d; cbn[mass scale] in *; nra.
Qed.

Lemma core_low_discount c a b v l u z :
  CCore.Scan a ((repeat W1 c++[W0])++u) b v l -> TailDigits u z -> (0<c)%nat ->
  mass v*qnat (2^(c+c/2))%nat <= qnat (2^(c+c/2))%nat+2*qnat (2^c)%nat*(1+2*z) /\
  l*qnat (2^(c+c/2))%nat <= qnat (2^(c+c/2))%nat+2*qnat (2^c)%nat*(1+2*z).
Proof.
  intros I Z C; pose proof (Tail_nonneg _ _ Z).
  destruct (mod2 c); subst c.
  - destruct a0 as [|r]; [lia|].
    replace (S r*2)%nat with (2+r*2)%nat in * by lia.
    pose proof (core_low_even _ _ _ _ _ _ _ I Z).
    assert ((2+r*2+(2+r*2)/2)=(2+r*2)+r+1)%nat as P by lia.
    rewrite P, Nat.pow_add_r, Nat.pow_add_r, !qnat_mul.
    change (qnat (2^1)%nat) with 2.
    pose proof (qpow_pos (2+r*2)%nat); pose proof (qpow_pos r); nra.
  - pose proof (core_low_odd _ _ _ _ _ _ _ I Z).
    assert ((1+a0*2+(1+a0*2)/2)=(1+a0*2)+a0)%nat as P by lia.
    rewrite P, Nat.pow_add_r, qnat_mul.
    cbn[Nat.add Nat.pow] in H0; rewrite qnat_mul in H0; change (qnat 2%nat) with 2 in H0.
    pose proof (qpow_pos (1+a0*2)%nat); pose proof (qpow_pos a0); nra.
Qed.

Lemma Tail_drop_ones c : forall u z, TailDigits (repeat W1 c++u) z ->
  exists z', TailDigits u z' /\ z==qnat (2^c)%nat*z'.
Proof.
  induction c; intros u z I; cbn[repeat app] in I.
  - exists z; split; [apply I|change (z==1*z); ring].
  - destruct (Tail_one_inv _ _ I) as [y [J ->]].
    destruct (IHc _ _ J) as [x [K Eq]]; exists x; split; [apply K|].
    cbn[Nat.pow]; rewrite qnat_mul; change (qnat 2%nat) with 2; nra.
Qed.

Lemma discount_weaken x z p q : 0<p -> p<=q -> 0<=z ->
  x*q<=q+2*z -> x*p<=p+2*z.
Proof. intros; destruct (Qlt_le_dec x 1); nra. Qed.

Lemma core_tail_low_discount s c u A H a b v l :
  Digits A H (repeat W1 c++W0::u) ->
  CCore.Scan a ((repeat W1 c++W0::u)++[W0]) b v l ->
  (0<c)%nat -> (s<=c)%nat ->
  mass v*qnat (2^(s+s/2))%nat <= qnat (2^(s+s/2))%nat+2*zeros (repeat W1 c++W0::u) /\
  l*qnat (2^(s+s/2))%nat <= qnat (2^(s+s/2))%nat+2*zeros (repeat W1 c++W0::u).
Proof.
  intros D I C SC.
  pose proof (Digits_tail _ _ _ D) as Z; rewrite <-app_assoc in Z.
  destruct (Tail_drop_ones c _ _ Z) as [x [U X]].
  destruct (Tail_zero_inv _ _ U) as [[Nil _]|[z [V ->]]].
  { apply app_eq_nil in Nil as [_ N]; discriminate. }
  assert (E : (repeat W1 c++W0::u)++[W0]=
    (repeat W1 c++[W0])++(u++[W0])) by (rewrite <-!app_assoc; reflexivity).
  rewrite E in I.
  destruct (core_low_discount _ _ _ _ _ _ _ I V C) as [M L].
  pose proof (qpow_pos (s+s/2)%nat) as Pos.
  assert (Mono:qnat (2^(s+s/2))%nat<=qnat (2^(c+c/2))%nat).
  { apply qnat_le, Nat.pow_le_mono_r; lia. }
  pose proof (weights_nonneg (repeat W1 c++W0::u)).
  split; eapply discount_weaken; eauto; nra.
Qed.

Lemma Scan_tail_low_discount s ds A H k k' v a b :
  Digits A H ds -> Scan k (ds++[W0]) k' v a b ->
  (exists c u, (0<c /\ s<=c)%nat /\ ds=repeat W1 c++W0::u) ->
  mass v*qnat (2^(s+s/2))%nat <= qnat (2^(s+s/2))%nat+2*zeros ds /\
  a*qnat (2^(s+s/2))%nat <= 4*(qnat (2^(s+s/2))%nat+2*zeros ds) /\
  b*qnat (2^(s+s/2))%nat <= 3*(qnat (2^(s+s/2))%nat+2*zeros ds).
Proof.
  intros D I [c [u [[C SC] ->]]].
  pose proof (Digits_app _ _ _ D _ _ _ (Digits_zero 0 0 _ Digits_nil)) as Full.
  destruct (Scan_digits_to_core _ _ _ _ _ _ I _ _ Full) as [l [J [P N]]].
  pose proof (core_tail_low_discount s _ _ _ _ _ _ _ _ D J C SC).
  pose proof (qpow_pos (s+s/2)%nat); nra.
Qed.

(* cut_at forbids cutting a D1 pair in half. *)
Lemma Scan_cut k u k' v a b : Scan k u k' v a b -> forall p q,
  u=p++q -> cut_at p q ->
  exists m x y a1 b1 a2 b2, Scan k p m x a1 b1 /\ Scan m q k' y a2 b2 /\
    v=x++y /\ a==a1+scale x*a2 /\ b==b1+scale x*b2.
Proof.
  intro I; induction I; intros p q E P; destruct p as [|s p].
  all: try (cbn[app] in E; subst q;
    eexists _, (@nil Word), _, 0, 0, _, _;
    split; [constructor|]; split; [eauto using Scan|];
    split; [reflexivity|cbn[scale]; split; ring]).
  1: { discriminate. }
  all: injection E as Es E; subst s.
  2,3: destruct p as [|s p];
    [cbn[app] in E; subst q; destruct P as [P|[r P]]; discriminate|];
    injection E as Es E; subst s; do 2 apply cut_at_tail in P.
  1,4,5,6,7: apply cut_at_tail in P.
  all: destruct (IHI _ _ E P) as [m [x [y [a1 [b1 [a2 [b2 [J [K [-> [A B]]]]]]]]]]].
  all: eexists _, (_::x), y, _, _, a2, b2;
    split; [eauto using Scan|]; split; [apply K|];
    split; [reflexivity|cbn[scale]; split; nra].
Qed.

Lemma Scan_gain_power k u k' v a b : Scan k u k' v a b ->
  exists g, scale u==scale v*qnat (8^g)%nat.
Proof.
  intro I; induction I.
  1: { exists 0%nat; cbn[scale Nat.pow]; change (qnat 1%nat) with 1; ring. }
  all: destruct IHI as [g E].
  all: try (exists g; cbn[scale]; rewrite E; ring).
  all: exists (1+g)%nat; cbn[scale Nat.add Nat.pow]; rewrite qnat_mul;
    change (qnat 8%nat) with 8; rewrite E; ring.
Qed.

Lemma Scan_many_end r k u k' v a b :
  Scan k (u++repeat W1 (1+r*2)%nat++[W0]) k' v a b ->
  exists w n, v=w++repeat WT (1+r)%nat /\ k'=(n*2^(1+r))%nat.
Proof.
  intro I; destruct (trailing_ones u) as [p [n [-> P]]].
  assert (E : (p++repeat W1 n)++repeat W1 (1+r*2)%nat++[W0]=
    p++(repeat W1 (1+r*2+n)%nat++[W0])).
  { replace (1+r*2+n)%nat with (n+(1+r*2))%nat by lia.
    rewrite (repeat_app W1 n (1+r*2)%nat); rewrite !app_assoc; reflexivity. }
  rewrite E in I.
  destruct (Scan_cut _ _ _ _ _ _ I _ _ eq_refl)
    as [m [x [y [a1 [b1 [a2 [b2 [J [K [-> _]]]]]]]]]]; [left; apply P|].
  pose proof (Digits_app _ _ _ (Digits_ones (1+r*2+n)%nat) _ _ _
    (Digits_zero 0 0 _ Digits_nil)) as D.
  destruct (Scan_digits_to_core _ _ _ _ _ _ K _ _ D) as [l [L _]].
  destruct (CCore.Scan_ones_long _ _ _ _ _ _ L) as [w [q [-> Q]]].
  exists (x++w), q; rewrite app_assoc; auto.
Qed.

Local Open Scope nat_scope.

Lemma Effective_repeat_T p : forall n b v, Effective n (repeat WT p) b v ->
  v=repeat WT p /\ 1+b=(1+n)*2^p.
Proof.
  induction p; intros n b v I; inversion I; subst.
  - cbn[Nat.pow]; split; [reflexivity|lia].
  - match goal with E:Effective _ _ _ _ |- _ =>
      destruct (IHp _ _ _ E) as [-> Eq] end.
    cbn[repeat Nat.pow]; split; [reflexivity|nia].
Qed.

Lemma Effective_many_end u : forall p n b v,
  Effective n (u++repeat WT p) b v ->
  exists w q, v=w++repeat WT p /\ 1+b=q*2^p.
Proof.
  induction u as [|x u IH]; intros p n b v I; cbn[app] in I.
  - destruct (Effective_repeat_T _ _ _ _ I) as [-> Eq].
    exists (@nil Word), (1+n); auto.
  - inversion I; subst.
    all: match goal with E:Effective _ (_++_) _ _ |- _ =>
      destruct (IH _ _ _ _ E) as [w [q [-> Eq]]] end.
    all: eexists (_::w), q; split; [reflexivity|apply Eq].
Qed.

Lemma compensated_low r J k b A B : r<=J ->
  (exists n, k=n*2^r) -> (exists n, 1+b=n*2^r) ->
  A+2^J=k -> B+2^J=A+b -> exists n, 1+B=n*2^r.
Proof.
  intros R [n N] [m M] K Bsum.
  assert (P:2^J=2^(J-r)*2^r).
  { rewrite <-Nat.pow_add_r; f_equal; lia. }
  exists (n+m-2*2^(J-r)); nia.
Qed.

Lemma Digits_low_ones s : forall B H ds,
  Digits B H ds -> s<=H -> (exists n, 1+B=n*2^s) ->
  exists u, ds=repeat W1 s++u.
Proof.
  induction s; intros B H ds D SH [n N].
  - exists ds; reflexivity.
  - inversion D; subst; cbn[Nat.pow] in N; try nia.
    match goal with E:Digits _ _ _ |- _ =>
      edestruct (IHs _ _ _ E) as [w ->]; [lia|exists n; nia|] end.
    exists w; reflexivity.
Qed.

Lemma Effective_prefix_T p : forall n u b v,
  Effective n (repeat WT p++u) b v ->
  exists q w, v=repeat WT p++w /\ 1+q=(1+n)*2^p /\ Effective q u b w.
Proof.
  induction p; intros n u b v I; cbn[repeat app] in I.
  - exists n, v; split; [reflexivity|split; [cbn[Nat.pow]; lia|apply I]].
  - inversion I; subst.
    match goal with E:Effective _ _ _ _ |- _ =>
      destruct (IHp _ _ _ _ E) as [q [w [-> [Eq J]]]] end.
    exists q, w; split; [reflexivity|split; [cbn[Nat.pow]; nia|apply J]].
Qed.

Lemma Effective_start p u b v :
  Effective 0 (repeat WT (1+p)++W1::u) b v ->
  exists w, v=repeat WT (1+p)++W0::w /\ Effective (2^p) u b w.
Proof.
  intro I; destruct (Effective_prefix_T _ _ _ _ _ I) as [q [w [-> [Eq J]]]].
  inversion J; subst; cbn[Nat.add Nat.pow] in Eq; try nia.
  eexists; split; [reflexivity|].
  match goal with E:Effective _ ?u ?b ?w |- Effective _ ?u ?b ?w =>
    applys_eq E; flia end.
Qed.

Local Open Scope Q_scope.

Lemma Scan_repeat_T p : forall k k' v a b, Scan k (repeat WT p) k' v a b ->
  v=repeat WT p /\ (k'+4*2^p=k*2^p+4)%nat /\ a==0 /\ b==0.
Proof.
  induction p; intros k k' v a b I; inversion I; subst.
  - cbn[Nat.pow]; repeat split; try reflexivity; lia.
  - match goal with J:Scan _ _ _ _ _ _ |- _ =>
      destruct (IHp _ _ _ _ _ J) as [-> [Eq [A B]]] end.
    cbn[repeat Nat.pow]; split; [reflexivity|split; [nia|split; lra]].
Qed.

Lemma cut_ok_Ts p : cut_ok (repeat WT p)=true.
Proof. induction p; [reflexivity|destruct p; cbn[repeat cut_ok] in *; auto]. Qed.

Lemma Scan_start p u k v a b : Scan 12 (repeat WT p++W0::u) k v a b ->
  exists w a' b', v=repeat WT p++W1::w /\
    Scan (4*2^p)%nat u k w a' b' /\
    a==scale (repeat WT p)*(4+2*a') /\ b==scale (repeat WT p)*(2*b').
Proof.
  intro I; destruct (Scan_cut _ _ _ _ _ _ I _ _ eq_refl)
    as [m [x [y [a1 [b1 [a2 [b2 [J [K [-> [A B]]]]]]]]]]];
    [left; apply cut_ok_Ts|].
  destruct (Scan_repeat_T _ _ _ _ _ _ J) as [-> [Eq [A1 B1]]].
  inversion K; subst; try lia.
  eexists _, _, _; split; [reflexivity|split].
  - match goal with E:Scan _ ?u ?k ?w _ _ |- Scan _ ?u ?k ?w _ _ =>
      applys_eq E; flia end.
  - split; nra.
Qed.

(* The high run supplies both the main budget divisor and a T suffix.
   Their combination, not either fact alone, regenerates the compensated low bits. *)
Lemma low_ones_regenerated r k u k' v a b carry eff A B J ds :
  Scan k (u++repeat W1 (1+r*2)%nat++[W0]) k' v a b ->
  Effective 0 (WT::(v++[WT])) carry eff ->
  Digits B J ds -> (1+r<=J)%nat ->
  (A+2^J=k')%nat -> (B+2^J=A+carry)%nat ->
  exists w, ds=repeat W1 (1+r)%nat++w.
Proof.
  intros I E D R Asum Bsum.
  destruct (Scan_many_end _ _ _ _ _ _ _ I) as [w [n [-> K]]].
  assert (Eq : WT::((w++repeat WT (1+r)%nat)++[WT])=
    (WT::w)++repeat WT (2+r)%nat).
  { change (WT::((w++repeat WT (1+r)%nat)++[WT])=
      (WT::w)++repeat WT (S (1+r)%nat)).
    rewrite (repeat_snoc WT (1+r)%nat); cbn[app]; rewrite app_assoc; reflexivity. }
  rewrite Eq in E.
  destruct (Effective_many_end _ _ _ _ _ E) as [x [m [_ C]]].
  apply (Digits_low_ones _ _ _ _ D R).
  eapply compensated_low; [apply R|exists n; apply K| |apply Asum|apply Bsum].
  exists (m*2)%nat; change ((1+carry)%nat=(m*2)*2^(1+r))%nat.
  change ((1+carry)%nat=m*(2*2^(1+r)))%nat in C; nia.
Qed.

Lemma scaled_discount x p q s f : 0<p -> 0<=s -> x*p<=q -> s*q<=f*p -> s*x<=f.
Proof. intros; nra. Qed.

Lemma Scan_tail_low_scaled s ds A H k k' v a b sigma f :
  Digits A H ds -> Scan k (ds++[W0]) k' v a b ->
  (exists c u, (0<c /\ s<=c)%nat /\ ds=repeat W1 c++W0::u) ->
  0<=sigma -> sigma*(qnat (2^(s+s/2))%nat+2*zeros ds)<=f*qnat (2^(s+s/2))%nat ->
  sigma*mass v<=f /\ sigma*a<=4*f /\ sigma*b<=3*f.
Proof.
  intros D I Low Sig Bound.
  destruct (Scan_tail_low_discount _ _ _ _ _ _ _ _ _ D I Low) as [M [P N]].
  pose proof (qpow_pos (s+s/2)%nat).
  repeat split; eapply scaled_discount; eauto; nra.
Qed.

(* Delta below is a-b BEFORE the final D1/blank-zero pair. *)
Lemma C12_stage_bounds p u ds A H k v a b s e f :
  Scan 12 (repeat WT p++W0::(u++ds++[W0])) k v a b ->
  Digits A H ds -> cut_ok u=true ->
  (exists c w, (0<c /\ s<=c)%nat /\ ds=repeat W1 c++W0::w) ->
  e==2*scale (repeat WT p)*mass u ->
  (2*scale (repeat WT p)*scale u)*(qnat (2^(s+s/2))%nat+2*zeros ds)<=f*qnat (2^(s+s/2))%nat ->
  exists w, v=repeat WT p++W1::w /\
    mass (WT::(v++[WT]))<=scale (repeat WT p)*(1#2)+(e+f)*(1#2) /\
    4*scale (repeat WT p)-e*(1#4)-3*f<=a-b /\
    a-b<=4*scale (repeat WT p)+4*e+4*f.
Proof.
  intros I D Cut Low Error Bound.
  destruct (Scan_start _ _ _ _ _ _ I) as [w [c [d [-> [J [Pos Neg]]]]]].
  destruct (Scan_cut _ _ _ _ _ _ J u (ds++[W0]) eq_refl)
    as [m [x [y [a1 [b1 [a2 [b2 [K [L [-> [C Dlt]]]]]]]]]]]; [left; apply Cut|].
  pose proof (Scan_bounds _ _ _ _ _ _ K) as Bounds.
  pose proof (Scan_bounds _ _ _ _ _ _ L) as TailBounds.
  pose proof (Scan_scale _ _ _ _ _ _ K) as Scale.
  pose proof (scale_pos u); pose proof (scale_pos x); pose proof (scale_pos (repeat WT p)).
  pose proof (weights_nonneg ds); pose proof (qpow_pos (s+s/2)%nat).
  assert (F : (2*scale (repeat WT p)*scale x)*(qnat (2^(s+s/2))%nat+2*zeros ds)<=
    f*qnat (2^(s+s/2))%nat).
  { eapply Qle_trans; [|apply Bound]; apply Qmult_le_compat_r; nra. }
  destruct (Scan_tail_low_scaled _ _ _ _ _ _ _ _ _ (2*scale (repeat WT p)*scale x) f D L Low)
    as [Mt [Pt Nt]]; [nra|apply F|].
  assert (Pa:0<=2*scale (repeat WT p)*scale x*a2) by
    (apply Qmult_le_0_compat; nra).
  assert (Pb:0<=2*scale (repeat WT p)*scale x*b2) by
    (apply Qmult_le_0_compat; nra).
  pose proof (repeat_T_weights p) as [Mass _].
  exists (x++y); split; [reflexivity|].
  cbn[mass]; rewrite !mass_app; cbn[mass scale]; rewrite ?mass_app.
  rewrite C in Pos; rewrite Dlt in Neg.
  repeat split; nra.
Qed.

Lemma Effective_first_bounds p u b v :
  Effective 0 (repeat WT (1+p)%nat++W1::u) b v ->
  2*scale (repeat WT (1+p)%nat)<=
    qnat (1+b)%nat*scale (repeat WT (1+p)%nat++W1::u)-1 /\
  qnat (1+b)%nat*scale (repeat WT (1+p)%nat++W1::u)-1<=
    2*mass (repeat WT (1+p)%nat++W1::u).
Proof.
  intro I; destruct (Effective_start _ _ _ _ I) as [w [-> E]].
  destruct (Effective_bounds _ _ _ _ E) as [Lo Hi].
  rewrite (qnat_add 1 (2^p)) in Lo, Hi; change (qnat 1%nat) with 1 in Lo, Hi.
  pose proof (scale_pos (repeat WT (1+p)%nat)).
  apply (Qmult_le_compat_r _ _ (2*scale (repeat WT (1+p)%nat))) in Lo, Hi; try lra.
  destruct (repeat_T_weights (1+p)%nat) as [M S].
  cbn[Nat.add Nat.pow] in S; rewrite qnat_mul in S; change (qnat 2%nat) with 2 in S.
  change (scale (repeat WT (1+p)%nat)*(2*qnat (2^p)%nat)==1) in S.
  rewrite mass_app, scale_app; cbn[mass scale].
  nra.
Qed.

Lemma deficit_step alpha e f unit delta R e' :
  0<alpha -> 0<=e -> 0<=f -> 0<=unit ->
  e<=alpha*(1#1024) -> f<=alpha*(1#1024) -> unit<=alpha*(1#1024) ->
  0<=e' -> e'<=(e+f)*(1#2) -> alpha<=R -> R<=alpha+2*e' ->
  4*alpha-e*(1#4)-3*f<=delta -> delta<=4*alpha+4*e+4*f ->
  (3#4)*alpha<=delta*(1#2)-4*unit-R /\
  delta*(1#2)-4*unit-R<=(5#4)*alpha.
Proof. intros; split; lra. Qed.

(* g counts the pairs in Scan, excluding the final pair at the blank boundary. *)
Lemma Scan_output_height u A H ds k k' v a b : Digits A H ds ->
  scale u*qnat (2^H)%nat==1 -> Scan k (u++ds++[W0]) k' v a b ->
  exists g, scale (WT::(v++[WT]))*qnat (2^(1+3*g))%nat==1.
Proof.
  intros D Height I; destruct (Scan_gain_power _ _ _ _ _ _ I) as [g Gain].
  pose proof (Digits_weights _ _ _ D) as [Width _].
  rewrite !scale_app in Gain; cbn[scale] in Gain; rewrite Width in Gain.
  exists g; cbn[scale]; rewrite scale_app; cbn[scale].
  rewrite (Nat.pow_add_r 2 1 (3*g)), pow_three, qnat_mul.
  change (qnat (2^1)%nat) with 2; nra.
Qed.

Lemma Scan_output_budget u k v a b : Scan 12 u k v a b ->
  qnat k*scale (WT::(v++[WT])) ==
    2+4*scale (WT::(v++[WT]))-(a-b)*(1#2).
Proof.
  intro I; pose proof (Scan_budget _ _ _ _ _ _ I) as Eq.
  change (8 == (qnat k-4)*scale v+2*(a-b)) in Eq.
  cbn[scale]; rewrite scale_app; cbn[scale]; nra.
Qed.

Lemma Scan_compensated_deficit u k v a b J A B carry : Scan 12 u k v a b ->
  scale (WT::(v++[WT]))*qnat (2^J)%nat==1 ->
  (A+2^J=k)%nat -> (B+2^J=A+carry)%nat ->
  1-qnat (1+B)%nat*scale (WT::(v++[WT])) ==
    (a-b)*(1#2)-4*scale (WT::(v++[WT]))-
    (qnat (1+carry)%nat*scale (WT::(v++[WT]))-1).
Proof.
  intros I Height Asum Bsum; pose proof (Scan_output_budget _ _ _ _ _ I) as Budget.
  assert (Sum:(B+2^J+2^J=k+carry)%nat) by lia.
  assert (Qsum:qnat (B+2^J+2^J)%nat==qnat (k+carry)%nat) by (rewrite Sum; reflexivity).
  rewrite !qnat_add in Qsum.
  assert (Bq:qnat B==qnat k+qnat carry-2*qnat (2^J)%nat) by lra.
  rewrite !qnat_add; change (qnat 1%nat) with 1; rewrite Bq; nra.
Qed.

Lemma qnat_sub a b : (b<=a)%nat -> qnat (a-b)%nat==qnat a-qnat b.
Proof.
  intro H; unfold qnat; rewrite Nat2Z.inj_sub by lia.
  unfold Z.sub; rewrite inject_Z_plus, inject_Z_opp; reflexivity.
Qed.

(* Construct A,B and prove their widths; do not assume a correct binary split. *)
Lemma compensated_window J k carry alpha unit delta R :
  0<alpha -> alpha<=(1#32) -> 0<unit -> unit<=alpha*(1#1024) ->
  unit*qnat (2^J)%nat==1 ->
  (15#4)*alpha<=delta -> delta<=(17#4)*alpha ->
  alpha<=R -> R<=(5#4)*alpha ->
  qnat k*unit==2+4*unit-delta*(1#2) -> qnat (1+carry)%nat*unit==1+R ->
  exists A B, (A+2^J=k /\ B+2^J=A+carry /\
    2^J<=A*2 /\ A<2^J /\ 2^J<=B*2 /\ B<2^J)%nat.
Proof.
  intros Pos Small Unit Tiny Height Dl Du Rl Ru K C.
  rewrite qnat_add in C; change (qnat 1%nat) with 1 in C.
  assert (Knat:(2^J<=k)%nat) by (apply qnat_le; nra).
  assert (Bnat:(2^J+2^J<=k+carry)%nat) by
    (apply qnat_le; rewrite !qnat_add; nra).
  exists (k-2^J)%nat, (k+carry-(2^J+2^J))%nat.
  repeat split; try lia.
  all: apply qnat_lt || apply qnat_le; rewrite ?qnat_mul;
    change (qnat 2%nat) with 2; rewrite !qnat_sub by lia; rewrite ?qnat_add; nra.
Qed.

(* The shrinking reserve is represented by parity constructors, not a division
   hidden inside arithmetic expressions. *)
Inductive Reserve : nat -> QArith_base.Q -> Prop :=
| Reserve_even n tau : tau*qnat (2^n)%nat==1 -> Reserve (n*2)%nat tau
| Reserve_odd n tau : tau*qnat (2^n)%nat==(3#4) -> Reserve (1+n*2)%nat tau.

Lemma Reserve_next p tau : Reserve p tau ->
  exists tau', Reserve (1+p)%nat tau' /\ tau'<=(3#4)*tau.
Proof.
  intro I; destruct I as [n tau Eq|n tau Eq]; pose proof (qpow_pos n).
  - exists ((3#4)*tau); split; [apply Reserve_odd; nra|lra].
  - exists ((2#3)*tau); split; [|nra].
    applys_eq (Reserve_even (1+n)%nat); flia.
    cbn[Nat.add Nat.pow]; rewrite qnat_mul; change (qnat 2%nat) with 2; nra.
Qed.

Lemma Reserve_small p tau : Reserve p tau -> (32<=p)%nat -> 0<tau /\ tau<=(1#256).
Proof.
  intros I P; destruct I as [n tau Eq|n tau Eq]; pose proof (qpow_pos n).
  all: assert (Bound:256<=qnat (2^n)%nat) by
    (change (qnat (2^8)%nat<=qnat (2^n)%nat); apply qnat_le, Nat.pow_le_mono_r; lia).
  all: split; nra.
Qed.

Lemma reserve_powers p n H s : (16<=n)%nat -> (p=n*2 \/ p=1+n*2)%nat ->
  (s=(p-2)/2)%nat -> (2*p+3<=H)%nat ->
  32*qnat (2^n)%nat<=qnat (2^(s+s/2))%nat /\
  32*qnat (2^p)%nat*qnat (2^n)%nat<=qnat (2^H)%nat.
Proof.
  intros N P S Hbound; split.
  - change (qnat (2^5)%nat*qnat (2^n)%nat<=qnat (2^(s+s/2))%nat).
    rewrite <-qnat_mul, <-Nat.pow_add_r; apply qnat_le, Nat.pow_le_mono_r; lia.
  - change (qnat (2^5)%nat*qnat (2^p)%nat*qnat (2^n)%nat<=qnat (2^H)%nat).
    rewrite <-!qnat_mul, <-!Nat.pow_add_r; apply qnat_le, Nat.pow_le_mono_r; lia.
Qed.

Lemma reserve_scaled alpha unit f t q tau :
  0<t -> 0<=alpha -> 0<=unit -> 32*t*unit<=alpha -> 32*t<=q ->
  f*q<=unit*q+5*alpha -> (3#4)<=tau*t -> f<=alpha*tau*(1#4).
Proof. intros; destruct (Qlt_le_dec f unit); nra. Qed.

Lemma height_unit_bound t q h alpha unit : 0<alpha -> 0<=unit ->
  alpha*q==1 -> unit*h==1 -> 32*q*t<=h -> 32*t*unit<=alpha.
Proof.
  intros A U Aq Uh High; apply (Qmult_le_compat_r _ _ unit) in High; [|apply U].
  set (x:=32*t*unit).
  assert (Bound:q*x<=1) by (unfold x; nra).
  change (x<=alpha); nra.
Qed.

Lemma reserve_tail_bound p H s alpha unit tau f : Reserve p tau ->
  (32<=p)%nat -> (2*p+3<=H)%nat -> (s=(p-2)/2)%nat ->
  0<alpha -> 0<unit -> alpha*qnat (2^p)%nat==1 -> unit*qnat (2^H)%nat==1 ->
  f*qnat (2^(s+s/2))%nat<=unit*qnat (2^(s+s/2))%nat+5*alpha ->
  f<=alpha*tau*(1#4).
Proof.
  intros I P Hbound S A U Ap Uh F; destruct I as [n tau Tau|n tau Tau].
  1: destruct (reserve_powers (n*2)%nat n H s) as [Low High]; try lia.
  2: destruct (reserve_powers (1+n*2)%nat n H s) as [Low High]; try lia.
  all: pose proof (qpow_pos n).
  all: assert (Gap:32*qnat (2^n)%nat*unit<=alpha) by
    (eapply height_unit_bound; eauto; lra).
  all: eapply reserve_scaled; eauto; nra.
Qed.

Lemma pair_height_arith p : (32<=p ->
  2*(p+1)+3<=1+3*(((p-2)/2+1)/2)+3*((p-1)/2))%nat.
Proof. lia. Qed.

Lemma reserve_error_step alpha tau tau' e f e' : 0<=alpha ->
  tau'<=(3#4)*tau -> e<=alpha*((1#1024)-tau) -> f<=alpha*tau*(1#4) ->
  e'<=(e+f)*(1#2) -> e'<=(alpha*(1#2))*((1#1024)-tau').
Proof. intros; nra. Qed.

Lemma Scan_gain_length k u k' v a b : Scan k u k' v a b ->
  exists g, scale u==scale v*qnat (8^g)%nat /\
    (List.length u=List.length v+g)%nat.
Proof.
  intro I; induction I.
  1: { exists 0%nat; cbn[scale List.length Nat.pow]; split;
    [change (qnat 1%nat) with 1; ring|reflexivity]. }
  all: destruct IHI as [g [E L]].
  all: try (exists g; cbn[scale List.length]; split; [rewrite E; ring|lia]).
  all: exists (1+g)%nat; cbn[scale List.length Nat.add Nat.pow]; rewrite qnat_mul;
    change (qnat 8%nat) with 8; split; [rewrite E; ring|lia].
Qed.

Lemma Scan_length k u k' v a b : Scan k u k' v a b ->
  (List.length v<=List.length u)%nat.
Proof. intro I; destruct (Scan_gain_length _ _ _ _ _ _ I) as [g [_ L]]; lia. Qed.

Lemma core_ones_length c k k' v l : (0<c)%nat ->
  CCore.Scan k (repeat W1 c++[W0]) k' v l ->
  (List.length v+(c+1)/2=c+1)%nat.
Proof.
  intros C I; destruct (mod2 c) as [r E|r E]; subst c.
  - destruct r; [lia|].
    change (CCore.Scan k (repeat W1 (2+r*2)%nat++[W0]) k' v l) in I.
    destruct (CCore.Scan_ones_even _ _ _ _ _ I) as [d [n [-> _]]].
    cbn[List.length]; rewrite repeat_length; lia.
  - destruct (CCore.Scan_ones_odd _ _ _ _ _ I) as [-> _].
    rewrite repeat_length; lia.
Qed.

Lemma Scan_ones_length c k k' v a b : (0<c)%nat ->
  Scan k (repeat W1 c++[W0]) k' v a b ->
  (List.length v+(c+1)/2=c+1)%nat.
Proof.
  intros C I; pose proof (Digits_app _ _ _ (Digits_ones c) _ _ _
    (Digits_zero 0 0 _ Digits_nil)) as D.
  destruct (Scan_digits_to_core _ _ _ _ _ _ I _ _ D) as [l [J _]].
  eapply core_ones_length; eauto.
Qed.

Lemma Scan_two_runs_gain k u c mid t k' v a b :
  (0<c)%nat -> (0<t)%nat -> cut_ok u=true -> cut_ok mid=true ->
  Scan k (u++repeat W1 c++W0::(mid++repeat W1 t++[W0])) k' v a b ->
  exists g, scale (u++repeat W1 c++W0::(mid++repeat W1 t++[W0]))==
    scale v*qnat (8^g)%nat /\ ((c+1)/2+(t+1)/2<=g)%nat.
Proof.
  intros C T U M I; destruct (Scan_gain_length _ _ _ _ _ _ I) as [g [G L]].
  exists g; split; [apply G|].
  destruct (Scan_cut _ _ _ _ _ _ I _ _ eq_refl) as
    [m [x [y [a1 [b1 [a2 [b2 [J [K [V _]]]]]]]]]]; [left; apply U|].
  assert (Split:repeat W1 c++W0::(mid++repeat W1 t++[W0])=
    (repeat W1 c++[W0])++(mid++repeat W1 t++[W0])) by
    (rewrite <-app_assoc; reflexivity).
  destruct (Scan_cut _ _ _ _ _ _ K _ _ Split) as
    [m1 [x1 [y1 [a3 [b3 [a4 [b4 [J1 [K1 [V1 _]]]]]]]]]];
    [left; apply cut_ok_last|].
  destruct (Scan_cut _ _ _ _ _ _ K1 _ _ eq_refl) as
    [m2 [x2 [y2 [a5 [b5 [a6 [b6 [J2 [K2 [V2 _]]]]]]]]]]; [left; apply M|].
  pose proof (Scan_length _ _ _ _ _ _ J).
  pose proof (Scan_length _ _ _ _ _ _ J2).
  pose proof (Scan_ones_length _ _ _ _ _ _ C J1).
  pose proof (Scan_ones_length _ _ _ _ _ _ T K2).
  rewrite V, V1, V2, !length_app, !repeat_length in L; cbn[List.length] in L.
  rewrite !length_app, !repeat_length in L; cbn[List.length] in L; lia.
Qed.

Lemma Scan_output_height_large u ds A H k k' v a b p c mid t :
  Digits A H ds -> scale u*qnat (2^H)%nat==1 ->
  Scan k (u++ds++[W0]) k' v a b ->
  cut_ok u=true -> cut_ok mid=true ->
  ds=repeat W1 c++W0::(mid++repeat W1 t) ->
  (32<=p)%nat -> ((p-2)/2<=c)%nat -> (p-2<=t)%nat ->
  exists J, (2*(p+1)+3<=J)%nat /\
    scale (WT::(v++[WT]))*qnat (2^J)%nat==1.
Proof.
  intros D Height I U M Ds P C T.
  assert (Eq:u++ds++[W0]=u++repeat W1 c++W0::(mid++repeat W1 t++[W0])) by
    (rewrite Ds; rewrite <-!app_assoc; cbn[app]; rewrite <-!app_assoc; reflexivity).
  rewrite Eq in I.
  destruct (Scan_two_runs_gain k u c mid t k' v a b ltac:(lia) ltac:(lia) U M I)
    as [g [Gain Count]].
  exists (1+3*g)%nat; split.
  - pose proof (pair_height_arith _ P); lia.
  - rewrite <-Eq in Gain; pose proof (Digits_weights _ _ _ D) as [Width _].
    rewrite !scale_app in Gain; cbn[scale] in Gain; rewrite Width in Gain.
    cbn[scale]; rewrite scale_app; cbn[scale].
    rewrite (Nat.pow_add_r 2 1 (3*g)), pow_three, qnat_mul.
    change (qnat (2^1)%nat) with 2; nra.
Qed.

Lemma output_unit_small p J alpha unit : (32<=p)%nat ->
  (2*(p+1)+3<=J)%nat -> 0<alpha -> 0<unit ->
  alpha*qnat (2^p)%nat==1 -> unit*qnat (2^J)%nat==1 ->
  unit<=alpha*(1#1024).
Proof.
  intros P Jbound A U Ap Uj.
  assert (High:32*qnat (2^p)%nat*32<=qnat (2^J)%nat).
  { setoid_replace (32*qnat (2^p)%nat*32) with (qnat (2^10)%nat*qnat (2^p)%nat)
      by (change (qnat (2^10)%nat) with 1024; ring).
    rewrite <-qnat_mul, <-Nat.pow_add_r; apply qnat_le, Nat.pow_le_mono_r; lia. }
  pose proof (height_unit_bound 32 (qnat (2^p)%nat) (qnat (2^J)%nat)
    alpha unit A ltac:(lra) Ap Uj High); lra.
Qed.

Local Open Scope nat_scope.

Lemma Digits_unique A H u : Digits A H u -> forall v, Digits A H v -> u=v.
Proof.
  intro I; induction I; intros v J; inversion J; subst; try lia.
  all: f_equal; apply IHI; applys_eq H3; flia.
Qed.


Lemma Digits_high_window n t B ds : Digits B (n+t) ds ->
  2^(n+t)<=B+2^n -> exists u, ds=u++repeat W1 t.
Proof.
  intros D L; pose proof (Digits_bound _ _ _ D) as Bound.
  pose proof (Nat.pow_nonzero 2 t) as Pos.
  rewrite Nat.pow_add_r in L, Bound.
  set (a:=B-(2^t-1)*2^n).
  assert (Sum:a+(2^t-1)*2^n=B) by (unfold a; nia).
  destruct (Digits_ex n a) as [u U]; [nia|].
  exists u; eapply Digits_unique; [apply D|].
  rewrite <-Sum; apply Digits_app; [apply U|apply Digits_ones].
Qed.

Local Open Scope Q_scope.

Lemma dyadic_shift p H alpha unit : (p<=H)%nat ->
  alpha*qnat (2^p)%nat==1 -> unit*qnat (2^H)%nat==1 ->
  unit*qnat (2^(H-p))%nat==alpha.
Proof.
  intros PH A U; pose proof (qpow_pos p).
  assert (Eq:(2^H=2^(H-p)*2^p)%nat) by (rewrite <-Nat.pow_add_r; f_equal; lia).
  rewrite Eq, qnat_mul in U; nra.
Qed.

Lemma Digits_high_small p H B ds alpha unit :
  Digits B H ds -> (2<=p)%nat -> (p<=H)%nat ->
  0<alpha -> 0<unit -> unit<=alpha ->
  alpha*qnat (2^p)%nat==1 -> unit*qnat (2^H)%nat==1 ->
  unit*zeros ds<=(5#2)*alpha -> exists u, ds=u++repeat W1 (p-2)%nat.
Proof.
  intros D P PH A U Small Ap Uh Deficit.
  assert (Shift:unit*qnat (2^(H-(p-2)))%nat==4*alpha).
  { replace (H-(p-2))%nat with ((H-p)+2)%nat by lia.
    rewrite Nat.pow_add_r, qnat_mul; change (qnat (2^2)%nat) with 4.
    pose proof (dyadic_shift _ _ _ _ PH Ap Uh); nra. }
  pose proof (Digits_zeros _ _ _ D).
  apply (Digits_high_window (H-(p-2))%nat (p-2)%nat B ds).
  - applys_eq D; flia.
  - replace (H-(p-2)+(p-2))%nat with H by lia.
    apply qnat_le; rewrite qnat_add; nra.
Qed.

Lemma Digits_first_zero B H ds : Digits B H ds -> 0<zeros ds ->
  exists c w, ds=repeat W1 c++W0::w.
Proof.
  intro I; induction I; cbn[zeros]; intro Z.
  - lra.
  - exists 0%nat, u; reflexivity.
  - destruct IHI as [c [w ->]]; [lra|exists (1+c)%nat, w; reflexivity].
Qed.

Local Open Scope nat_scope.

Lemma leading_ones_bound c : forall s u v,
  repeat W1 s++u=repeat W1 c++W0::v -> s<=c.
Proof.
  induction c; intros [|s] u v E; cbn[repeat app] in E; try discriminate; try lia.
  injection E as E; specialize (IHc _ _ _ E); lia.
Qed.

Lemma trailing_ones_bound u v c s : cut_ok u=true ->
  u++repeat W1 c=v++repeat W1 s -> s<=c.
Proof.
  intros C E; destruct (le_dec s c) as [Le|Gt]; [assumption|].
  replace s with ((s-c)+c) in E by lia.
  rewrite repeat_app, app_assoc in E; apply app_inv_tail in E; subst u.
  destruct (s-c) as [|n] eqn:N; [lia|].
  rewrite repeat_snoc, app_assoc, cut_ok_last in C; discriminate.
Qed.

Lemma cut_ok_app_tail u v : cut_ok (u++v)=true -> cut_ok v=true.
Proof. induction u; cbn[app]; intro C; [apply C|apply IHu; eapply cut_ok_tail; apply C]. Qed.

Lemma Effective_end_T n u b v : Effective n u b v ->
  (exists w, u=w++[WT]) -> exists w, v=w++[WT].
Proof.
  intros I [w ->]; change [WT] with (repeat WT 1) in I.
  destruct (Effective_many_end _ _ _ _ _ I) as [x [m [E _]]]; eauto.
Qed.

Local Open Scope Q_scope.

Lemma first_digit_mass p u :
  mass (repeat WT p++W1::u)==scale (repeat WT p)*(1+2*mass u).
Proof. rewrite mass_app; cbn[mass]; destruct (repeat_T_weights p); lra. Qed.

Lemma alpha_small p : (32<=p)%nat -> scale (repeat WT p)<=(1#65536).
Proof.
  intro P; pose proof (proj2 (repeat_T_weights p)).
  pose proof (scale_pos (repeat WT p)).
  assert (B:65536<=qnat (2^p)%nat) by
    (change (qnat (2^16)%nat<=qnat (2^p)%nat); apply qnat_le, Nat.pow_le_mono_r; lia).
  nra.
Qed.

Inductive Good : nat -> list Word -> Prop :=
| Good_intro p H u A da carry eff B db tau :
    (32<=p)%nat -> (2*p+3<=H)%nat ->
    (exists rest, u=repeat WT p++W1::rest) -> (exists rest, u=rest++[WT]) ->
    scale u*qnat (2^H)%nat==1 -> Digits A H da ->
    Effective 0 u carry eff -> (A+carry=B+2^H)%nat -> Digits B H db ->
    Reserve p tau ->
    mass u<=scale (repeat WT p)*(1+(1#1024)-tau) ->
    (3#2)*scale (repeat WT p)<=scale u*zeros db ->
    scale u*zeros db<=(5#2)*scale (repeat WT p) ->
    (exists rest, db=repeat W1 ((p-2)/2)%nat++rest) ->
    Good p (u++da++[W1]).

(* A finite step certificate; its interpretation below uses the already proved
   Scan_return_binary. The leading T is the whole-round left boundary effect. *)
Inductive Step : list Word -> list Word -> Prop :=
| Step_intro orig eff k v a b J A da :
    Effective 0 orig 1 eff -> Scan 12 eff k v a b ->
    Digits A J da -> (A+2^J=k)%nat ->
    Step orig (WT::(v++WT::(da++[W1]))).

Lemma Digits_two_runs B H ds s t : Digits B H ds -> (0<zeros ds)%Q ->
  (exists u, ds=repeat W1 s++u) -> (exists u, ds=u++repeat W1 t) ->
  exists c mid n, ds=repeat W1 c++W0::(mid++repeat W1 n) /\
    cut_ok mid=true /\ (s<=c /\ t<=n)%nat.
Proof.
  intros D Z [lo Lo] [hi Hi].
  destruct (Digits_first_zero _ _ _ D Z) as [c [w E]].
  destruct (trailing_ones w) as [mid [n [W M]]]; subst w.
  exists c, mid, n; split; [apply E|split; [apply M|split]].
  - apply (leading_ones_bound c s lo (mid++repeat W1 n)); congruence.
  - apply (trailing_ones_bound (repeat W1 c++W0::mid) hi n t).
    + destruct mid as [|x mid]; [apply cut_ok_last|].
      clear - M; induction c as [|c IH]; [cbn[repeat app cut_ok]; apply M|].
      destruct c; cbn[repeat app cut_ok] in *; auto.
    + rewrite <-app_assoc; cbn[app]; congruence.
Qed.

Lemma Effective_first_zero p u carry eff : (0<p)%nat ->
  Effective 0 (repeat WT p++W1::u) carry eff ->
  exists v, eff=repeat WT p++W0::v.
Proof.
  destruct p; [lia|]; intros P E.
  destruct (Effective_start p _ _ _ E) as [v [V _]]; eauto.
Qed.

Lemma dyadic_unit_small p H alpha unit : (p+10<=H)%nat ->
  0<alpha -> 0<unit -> alpha*qnat (2^p)%nat==1 -> unit*qnat (2^H)%nat==1 ->
  unit<=alpha*(1#1024).
Proof.
  intros PH A U Ap Uh.
  assert (High:32*qnat (2^p)%nat*32<=qnat (2^H)%nat).
  { setoid_replace (32*qnat (2^p)%nat*32) with (qnat (2^10)%nat*qnat (2^p)%nat)
      by (change (qnat (2^10)%nat) with 1024; ring).
    rewrite <-qnat_mul, <-Nat.pow_add_r; apply qnat_le, Nat.pow_le_mono_r; lia. }
  pose proof (height_unit_bound 32 (qnat (2^p)%nat) (qnat (2^H)%nat)
    alpha unit A ltac:(lra) Ap Uh High); lra.
Qed.

Lemma Good_next p orig : Good p orig ->
  exists out, Step orig out /\ Good (1+p)%nat out.
Proof.
  intro I; destruct I as [q H u A da carry eff B db tau P Hbound [rest Start] End Height DA Eff Sum DB
    Res M Dlo Dhi Low]; rename q into p.
  set (alpha:=scale (repeat WT p)) in *; set (unit:=scale u) in *.
  pose proof (scale_pos (repeat WT p)) as Alpha; fold alpha in Alpha.
  pose proof (scale_pos u) as Unit; fold unit in Unit.
  pose proof (proj2 (repeat_T_weights p)) as Ap; fold alpha in Ap.
  pose proof (alpha_small _ P) as Asmall; fold alpha in Asmall.
  pose proof (Reserve_small _ _ Res P) as [Tau TauSmall].
  assert (Usmall:unit<=alpha*(1#1024)) by
    (eapply (dyadic_unit_small p H alpha unit); eauto; lia).
  destruct (Effective_weights _ _ _ _ Eff) as [EffScale EffMass].
  destruct (Effective_end_T _ _ _ _ Eff End) as [last Elast].
  assert (Cut:cut_ok eff=true) by (rewrite Elast; apply cut_ok_last).
  assert (Ne:eff<>[]) by (rewrite Elast; intro E; apply app_eq_nil in E; destruct E; discriminate).
  assert (EffHeight:scale eff*qnat (2^H)%nat==1) by (rewrite EffScale; apply Height).
  assert (EffBound:mass eff+scale eff*(1+zeros db)<=(1#128)) by
    (rewrite EffScale, EffMass; fold unit; nra).
  destruct (C12_scan _ _ _ _ DB EffHeight Cut Ne EffBound) as [k [v [a [b [Iscan K]]]]].
  assert (Z:0<zeros db) by nra.
  destruct (Digits_high_small p H B db alpha unit DB ltac:(lia) ltac:(lia)
    Alpha Unit ltac:(lra) Ap Height Dhi) as [hi Hi].
  destruct (Digits_two_runs _ _ _ _ _ DB Z Low (ex_intro _ hi Hi))
    as [c [mid [t [Split [MidCut [C T]]]]]].
  destruct (Scan_output_height_large eff db B H 12 k v a b p c mid t DB EffHeight Iscan
    Cut MidCut Split P C T) as [J [Jbound Jheight]].
  set (new:=WT::(v++[WT])) in *.
  set (nu:=scale new) in *.
  pose proof (scale_pos new) as Nu; fold nu in Nu.
  assert (NuSmall:nu<=alpha*(1#1024)) by
    (eapply (output_unit_small p J alpha nu); eauto).
  assert (EffStart:exists w, eff=repeat WT p++W0::w).
  { rewrite Start in Eff; eapply Effective_first_zero; [lia|apply Eff]. }
  destruct EffStart as [w Estart].
  assert (Wcut:cut_ok w=true) by
    (rewrite Estart in Cut; apply cut_ok_app_tail in Cut; eapply cut_ok_tail; apply Cut).
  set (e:=mass u-alpha).
  assert (Eeq:e==2*alpha*mass w).
  { rewrite Estart, mass_app in EffMass; cbn[mass] in EffMass.
    pose proof (proj1 (repeat_T_weights p)); unfold e, alpha; nra. }
  pose proof (weights_nonneg w).
  assert (Epos:0<=e) by nra.
  assert (Ebound:e<=alpha*((1#1024)-tau)) by (unfold e; nra).
  set (s:=((p-2)/2)%nat).
  set (pow:=qnat (2^(s+s/2))%nat).
  pose proof (qpow_pos (s+s/2)%nat) as Pow; fold pow in Pow.
  set (f:=unit+2*unit*zeros db/pow).
  assert (Feq:f*pow==unit*pow+2*unit*zeros db) by
    (unfold f; field; lra).
  assert (Fpos:0<=f) by nra.
  assert (Fbound:f<=alpha*tau*(1#4)).
  { eapply (reserve_tail_bound p H s alpha unit tau f); eauto; try lia; fold pow; nra. }
  assert (Low':exists c w, (0<c /\ s<=c)%nat /\ db=repeat W1 c++W0::w).
  { exists c, (mid++repeat W1 t); split; [unfold s; lia|apply Split]. }
  assert (Factor:2*alpha*scale w==unit).
  { rewrite Estart, scale_app in EffScale; cbn[scale] in EffScale; fold alpha unit in EffScale; nra. }
  assert (ScanStart:Scan 12 (repeat WT p++W0::(w++db++[W0])) k v a b).
  { rewrite Estart in Iscan; rewrite <-app_assoc in Iscan; apply Iscan. }
  destruct (C12_stage_bounds p w db B H k v a b s e f ScanStart DB Wcut Low')
    as [tail [Vstart [Mnext [Dl Du]]]]; [apply Eeq|fold alpha pow; rewrite Factor; nra|].
  fold alpha in Mnext, Dl, Du; fold new in Mnext.
  destruct (Effective_ex new 0) as [carry' [eff' Eff']].
  assert (NewStart:new=repeat WT (1+p)%nat++W1::(tail++[WT])).
  { unfold new; rewrite Vstart, <-app_assoc; reflexivity. }
  pose proof (Effective_first_bounds p (tail++[WT]) carry' eff') as Rbounds.
  rewrite <-NewStart in Rbounds; specialize (Rbounds Eff').
  set (R:=qnat (1+carry')%nat*nu-1) in *.
  change (2*(alpha*(1#2))<=R /\ R<=2*mass new) in Rbounds.
  assert (Rlo:alpha<=R) by lra.
  assert (Enew:0<=mass new-alpha*(1#2)).
  { rewrite NewStart, first_digit_mass; cbn[Nat.add repeat scale]; fold alpha.
    pose proof (weights_nonneg (tail++[WT])); nra. }
  assert (Ftiny:f<=alpha*(1#1024)) by nra.
  assert (Etiny:e<=alpha*(1#1024)) by nra.
  pose proof (Scan_output_budget _ _ _ _ _ Iscan) as Budget; fold new nu in Budget.
  destruct (compensated_window J k carry' alpha nu (a-b) R Alpha ltac:(lra)
    Nu NuSmall Jheight ltac:(lra) ltac:(lra) Rlo ltac:(lra) Budget ltac:(unfold R; ring))
    as [A' [B' [Asum [Bsum [Al [Au [Bl Bu]]]]]]].
    destruct (Digits_ex J A' Au) as [da' DA']; destruct (Digits_ex J B' Bu) as [db' DB'].
    destruct (Reserve_next _ _ Res) as [tau' [Res' TauStep]].
    pose proof (reserve_error_step alpha tau tau' e f (mass new-alpha*(1#2))
      ltac:(lra) TauStep Ebound Fbound ltac:(lra)) as Mkeep.
    pose proof (deficit_step alpha e f nu (a-b) R (mass new-alpha*(1#2))
      Alpha Epos Fpos ltac:(lra) Etiny Ftiny NuSmall Enew ltac:(lra)
      Rlo ltac:(lra) Dl Du) as Dkeep.
    pose proof (Scan_compensated_deficit _ _ _ _ _ J A' B' carry' Iscan Jheight Asum Bsum) as Def.
    fold new nu R in Def.
    pose proof (Digits_zeros _ _ _ DB') as Znew.
    rewrite qnat_add in Def; change (qnat 1%nat) with 1 in Def.
    assert (Dnew:nu*zeros db'==(a-b)*(1#2)-4*nu-R) by nra.
    assert (LowNew:exists rest, db'=repeat W1 (((1+p)-2)/2)%nat++rest).
    { set (r:=((((1+p)-2)/2)-1)%nat).
      assert (Hr:(1+r=(((1+p)-2)/2) /\ 1+r*2<=p-2)%nat) by (unfold r; lia).
      assert (HighEnd:exists z, db=z++repeat W1 (1+r*2)%nat).
      { exists (hi++repeat W1 ((p-2)-(1+r*2))%nat); rewrite Hi, <-app_assoc, <-repeat_app.
        f_equal; f_equal; lia. }
      destruct HighEnd as [z HZ].
      assert (SC:Scan 12 ((eff++z)++repeat W1 (1+r*2)%nat++[W0]) k v a b).
      { rewrite <-!app_assoc; rewrite HZ in Iscan; rewrite <-!app_assoc in Iscan; apply Iscan. }
      destruct (low_ones_regenerated r 12 (eff++z) k v a b carry' eff' A' B' J db'
        SC Eff' DB' ltac:(lia) Asum Bsum) as [z' L].
      exists z'; rewrite (proj1 Hr) in L; apply L. }
    exists (new++da'++[W1]); split.
    + unfold new; cbn[app].
      applys_eq (Step_intro (u++da++[W1]) (eff++db++[W0]) k v a b J A' da');
        try (rewrite <-!app_assoc; reflexivity).
      * destruct (Effective_compensate _ _ _ _ _ DA Sum (Digits_bound _ _ _ DB)) as [d [DD EE]].
        assert (d=db) by (eapply Digits_unique; eauto); subst d.
        eapply Effective_app; eauto.
      * apply Iscan.
      * apply DA'.
      * apply Asum.
    + eapply (Good_intro (1+p)%nat J new A' da' carry' eff' B' db' tau'); eauto; try lia.
      * exists (WT::v); reflexivity.
      * cbn[Nat.add repeat scale]; fold alpha; lra.
      * change ((3#2)*(alpha*(1#2))<=nu*zeros db'); rewrite Dnew; lra.
      * change (nu*zeros db'<=(5#2)*(alpha*(1#2))); rewrite Dnew; lra.
Qed.

Definition Good_side r := exists p ws, Good p ws /\ r=to_side ws 0inf.


(* Copied anchors for the remaining C12 machines. *)
Local Open Scope nat_scope.

(* A copied finite prefix: raw words u, effective words v. No pair step
   occurs; all hypotheses describe finite runs, not infinite behaviour. *)
Inductive Copy : nat -> nat -> list Word -> list Word -> nat -> nat -> Prop :=
| Copy_nil n k : Copy n k [] [] n k
| Copy_T n k u v b k' : Copy (1+n*2) (2+k*2) u v b k' ->
    Copy n (3+k) (WT::u) (WT::v) b k'
| Copy_00 n k u v b k' : Copy n (k*2) u v b k' ->
    Copy (n*2) (2+k*4) (W0::u) (W0::v) b k'
| Copy_01 n k u v b k' : Copy n (1+k*2) u v b k' ->
    Copy (1+n*2) (2+k*4) (W0::u) (W1::v) b k'
| Copy_10 n k u v b k' : Copy n (1+k*2) u v b k' ->
    Copy (n*2) (4+k*4) (W1::u) (W1::v) b k'
| Copy_11 n k u v b k' : Copy (1+n) (k*2) u v b k' ->
    Copy (1+n*2) (4+k*4) (W1::u) (W0::v) b k'.

Lemma Copy_effective n k u v b k' : Copy n k u v b k' -> Effective n u b v.
Proof. intro I; induction I; constructor; apply IHI. Qed.

Lemma Copy_app n k u v b k' : Copy n k u v b k' -> forall w x c k'',
  Copy b k' w x c k'' -> Copy n k (u++w) (v++x) c k''.
Proof. intro I; induction I; cbn[app]; intros; eauto using Copy. Qed.

Lemma Copy_Ts q : forall n k,
  Copy n (4+k) (repeat WT q) (repeat WT q) ((1+n)*2^q-1) (4+k*2^q).
Proof.
  induction q; intros n k; cbn[repeat].
  - applys_eq Copy_nil; flia; cbn[Nat.pow]; lia.
  - applys_eq (Copy_T n (1+k)); flia.
    applys_eq (IHq (1+n*2) (k*2)); cbn[Nat.pow];
      pose proof (Nat.pow_nonzero 2 q); nia.
Qed.

Local Open Scope Q_scope.

Definition copy_loss u v := 3*mass u+ones u-ones v.

Lemma Copy_scan n k u v b k' : Copy n k u v b k' ->
  exists a c, Scan k v k' u a c /\ a==copy_loss u v /\ c==0.
Proof.
  intro I; induction I.
  1: { exists 0, 0; split; [constructor|unfold copy_loss; cbn[mass ones]; split; lra]. }
  all: destruct IHI as [a [c [S [A C]]]].
  all: eexists _, _; split; [econstructor; apply S|].
  all: unfold copy_loss in *; cbn[mass ones]; split; lra.
Qed.

Lemma Copy_ledger n k u v b k' : Copy n k u v b k' ->
  copy_loss u v-(qnat (1+b)%nat*scale u-qnat (1+n)%nat)==2*mass u /\
  0<=qnat (1+b)%nat*scale u-qnat (1+n)%nat /\
  qnat (1+b)%nat*scale u-qnat (1+n)%nat<=2*mass u.
Proof.
  intro I; pose proof (Copy_effective _ _ _ _ _ _ I) as E.
  pose proof (Effective_budget _ _ _ _ E); pose proof (Effective_bounds _ _ _ _ E).
  unfold copy_loss; repeat split; lra.
Qed.

Lemma copy_loss_app u v w x : scale u==scale v ->
  copy_loss (u++w) (v++x)==copy_loss u v+scale u*copy_loss w x.
Proof. intro E; unfold copy_loss; rewrite mass_app, !ones_app, E; ring. Qed.

Lemma repeat_T_ones q : ones (repeat WT q)==0.
Proof. induction q; cbn[repeat ones]; lra. Qed.

Lemma copy_loss_Ts q u v :
  copy_loss (repeat WT q++u) (repeat WT q++v)==scale (repeat WT q)*copy_loss u v.
Proof.
  rewrite copy_loss_app by reflexivity.
  unfold copy_loss at 1; destruct (repeat_T_weights q); ring_simplify; lra.
Qed.

Definition anchor11 := [W1;WT;W1;WT;WT;WT;WT;WT;WT;W1;WT;WT;WT;W1;WT].
Definition effective11 := [W0;WT;W0;WT;WT;WT;WT;WT;WT;W0;WT;WT;WT;W0;WT].
Definition anchor12 := [W1;W1;WT;WT;WT;WT;W1;WT;W1;W1;W1;WT;WT;WT;W1;WT;WT;WT;WT;WT;WT;WT;W1;WT;WT;W1;WT;W1;W1;WT].
Definition effective12 := [W0;W1;WT;WT;WT;WT;W0;WT;W0;W0;W0;WT;WT;WT;W0;WT;WT;WT;WT;WT;WT;WT;W0;WT;WT;W0;WT;W0;W0;WT].
Definition anchor49 := [W1;WT;WT;W1;W1;WT;W0;WT;W0;WT;WT;WT;W1;WT;WT;WT;WT;WT;WT;W1;WT;WT;WT;W1;WT;W1;WT;W1;W1;WT].
Definition effective49 := [W0;WT;WT;W0;W1;WT;W1;WT;W1;WT;WT;WT;W0;WT;WT;WT;WT;WT;WT;W0;WT;WT;WT;W0;WT;W0;WT;W0;W1;WT].
Local Open Scope nat_scope.

Definition bitN (b:bool) : N := if b then 1%N else 0%N.
Definition affine c m n := N.to_nat c+N.to_nat m*n.

Definition copy_digit_ok e f nc nm kc km :=
  if N.eqb (nc mod 2) (bitN (xorb e f)) then
  if N.eqb (nm mod 2) 0 then
  if N.eqb (kc mod 4) (if e then 0 else 2) then
  if N.eqb (km mod 4) 0 then N.leb (if e then 4 else 2) kc
  else false else false else false else false.

Fixpoint copyN u v nc nm kc km :=
  match u,v with
  | [],[] => true
  | WT::u,WT::v =>
      if N.leb 3 kc then
        copyN u v (N.succ_double nc) (N.double nm) (N.double (kc-2)) (N.double km)
      else false
  | w::u,z::v => match w,z with
    | WT,_ | _,WT => false
    | _,_ =>
      let e:=match w with W1 => true | _ => false end in
      let f:=match z with W1 => true | _ => false end in
      if copy_digit_ok e f nc nm kc km then
        copyN u v ((nc+bitN e)/2)%N (nm/2)%N
          (kc/2-(1+bitN e)+bitN f)%N (km/2)%N
      else false end
  | _,_ => false end.

Lemma copy_digit_spec e f nc nm kc km u v b k' n :
  copy_digit_ok e f nc nm kc km=true ->
  Copy (affine ((nc+bitN e)/2)%N (nm/2)%N n)
    (affine (kc/2-(1+bitN e)+bitN f)%N (km/2)%N n) u v b k' ->
  Copy (affine nc nm n) (affine kc km n) (digitW e::u) (digitW f::v) b k'.
Proof.
  unfold copy_digit_ok.
  repeat match goal with |- (if ?x then _ else _)=true -> _ =>
    destruct x eqn:?; [|discriminate] end.
  intro K; apply N.leb_le in K.
  repeat match goal with E:N.eqb _ _=true |- _ => apply N.eqb_eq in E end.
  unfold affine; rewrite ?N2Nat.inj_add, ?N2Nat.inj_sub, ?N2Nat.inj_div.
  destruct e, f; cbn[bitN xorb digitW] in *; intro I.
  - applys_eq (Copy_10 (N.to_nat (nc/2)+N.to_nat (nm/2)*n)
      (N.to_nat (kc/4)-1+N.to_nat (km/4)*n)); try nia.
    applys_eq I; nia.
  - applys_eq (Copy_11 (N.to_nat (nc/2)+N.to_nat (nm/2)*n)
      (N.to_nat (kc/4)-1+N.to_nat (km/4)*n)); try nia.
    applys_eq I; nia.
  - applys_eq (Copy_01 (N.to_nat (nc/2)+N.to_nat (nm/2)*n)
      (N.to_nat (kc/4)+N.to_nat (km/4)*n)); try nia.
    applys_eq I; nia.
  - applys_eq (Copy_00 (N.to_nat (nc/2)+N.to_nat (nm/2)*n)
      (N.to_nat (kc/4)+N.to_nat (km/4)*n)); try nia.
    applys_eq I; nia.
Qed.

Lemma copyN_spec u : forall v nc nm kc km, copyN u v nc nm kc km=true ->
  forall n, exists b k, Copy (affine nc nm n) (affine kc km n) u v b k.
Proof.
  induction u as [|w u IH]; intros v nc nm kc km E n.
  - destruct v; [eexists _, _; constructor|discriminate].
  - destruct v as [|z v]; [destruct w; discriminate|].
    destruct w,z; cbn[copyN] in E; try discriminate.
    + destruct (N.leb 3 kc) eqn:K; [apply N.leb_le in K|discriminate].
      destruct (IH _ _ _ _ _ E n) as [b [k I]].
      exists b,k; unfold affine in *.
      rewrite N2Nat.inj_succ_double, !N2Nat.inj_double, N2Nat.inj_sub in I.
      applys_eq (Copy_T (N.to_nat nc+N.to_nat nm*n) (N.to_nat kc+N.to_nat km*n-3)); try lia.
      applys_eq I; nia.
    + destruct (copy_digit_ok false false nc nm kc km) eqn:C; [|discriminate].
      destruct (IH _ _ _ _ _ E n) as [b [k I]]; exists b,k; eapply (copy_digit_spec false false); eauto.
    + destruct (copy_digit_ok false true nc nm kc km) eqn:C; [|discriminate].
      destruct (IH _ _ _ _ _ E n) as [b [k I]]; exists b,k; eapply (copy_digit_spec false true); eauto.
    + destruct (copy_digit_ok true false nc nm kc km) eqn:C; [|discriminate].
      destruct (IH _ _ _ _ _ E n) as [b [k I]]; exists b,k; eapply (copy_digit_spec true false); eauto.
    + destruct (copy_digit_ok true true nc nm kc km) eqn:C; [|discriminate].
      destruct (IH _ _ _ _ _ E n) as [b [k I]]; exists b,k; eapply (copy_digit_spec true true); eauto.
Qed.

Definition Copies u v := exists b k, Copy 0 12 u v b k.

Lemma copy_lift u v :
  (forall n, exists b k, Copy (31+32*n) (260+256*n) u v b k) ->
  forall q, 5<=q -> Copies (repeat WT q++u) (repeat WT q++v).
Proof.
  intros C q Q.
  assert (Pow:2^q=32*2^(q-5)) by
    (replace q with (5+(q-5)) at 1 by lia; rewrite Nat.pow_add_r; reflexivity).
  destruct (C (2^(q-5)-1)) as [b [k I]].
  exists b, k; eapply Copy_app; [apply (Copy_Ts q 0 8)|].
  applys_eq I; pose proof (Nat.pow_nonzero 2 (q-5)); nia.
Qed.

Lemma anchor11_copies q : 5<=q -> Copies (repeat WT q++anchor11) (repeat WT q++effective11).
Proof. apply copy_lift; apply (copyN_spec _ _ 31 32 260 256); vm_compute; reflexivity. Qed.
Lemma anchor12_copies q : 5<=q -> Copies (repeat WT q++anchor12) (repeat WT q++effective12).
Proof. apply copy_lift; apply (copyN_spec _ _ 31 32 260 256); vm_compute; reflexivity. Qed.
Lemma anchor49_copies q : 5<=q -> Copies (repeat WT q++anchor49) (repeat WT q++effective49).
Proof. apply copy_lift; apply (copyN_spec _ _ 31 32 260 256); vm_compute; reflexivity. Qed.

Local Open Scope Q_scope.

Lemma anchor11_stats : mass anchor11==(261#128) /\
  scale anchor11==(1#128) /\ copy_loss anchor11 effective11==(261#32).
Proof. vm_compute; repeat split; reflexivity. Qed.
Lemma anchor12_stats : mass anchor12==(1347#256) /\
  scale anchor12==(1#256) /\ copy_loss anchor12 effective12==(1219#64).
Proof. vm_compute; repeat split; reflexivity. Qed.
Lemma anchor49_stats : mass anchor49==(2441#512) /\
  scale anchor49==(1#256) /\ copy_loss anchor49 effective49==(3601#256).
Proof. vm_compute; repeat split; reflexivity. Qed.



Lemma Copy_effective_prefix n k u v b k' : Copy n k u v b k' ->
  forall w c x, Effective n (u++w) c x ->
    exists y, x=v++y /\ Effective b w c y.
Proof.
  intro C; induction C; intros w c x E; cbn[app] in E.
  1: { exists x; auto. }
  all: inversion E; subst; try lia.
  all: let IH:=constr:(IHC w c) in
    lazymatch type of IH with forall x, Effective _ ?us _ x -> _ =>
      match goal with J:Effective _ us _ ?z |- _ =>
        edestruct (IH z) as [y [-> Y]]; [applys_eq J; flia|] end end.
  all: eexists; split; [reflexivity|eassumption].
Qed.

Fixpoint short_only u :=
  match u with
  | [] => true
  | W1::v => match v with WT::_ => short_only v | _ => false end
  | _::v => short_only v end.

Lemma Copy_scan_prefix n k u v b k' : Copy n k u v b k' -> short_only v=true ->
  forall w k'' x a c, Scan k (v++w) k'' x a c ->
  exists y a' c', x=u++y /\ Scan k' w k'' y a' c' /\
    a==copy_loss u v+scale u*a' /\ c==scale u*c'.
Proof.
  intro C; induction C; intros Safe w k'' x a c I; cbn[app] in I.
  1: { exists x,a,c; repeat split; auto; unfold copy_loss; cbn[mass ones scale]; ring. }
  all: try match goal with H:short_only (W1::?v)=true |- _ =>
    destruct v as [|[| |] v]; try discriminate end.
  all: inversion I; subst; try lia.
  all: let IH:=constr:(IHC Safe w k'') in
    let T:=type of IH in let T:=eval cbn[app] in T in
    lazymatch T with forall x a c, Scan _ ?us _ x a c -> _ =>
      match goal with J:Scan _ us _ ?z ?a ?c |- _ =>
        edestruct (IH z a c) as [y [a' [c' [-> [Y [A C']]]]]];
          [applys_eq J; flia|] end end.
  all: eexists _,_,_; split; [reflexivity|split; [eassumption|]].
  all: unfold copy_loss in *; cbn[mass ones scale] in *; split; nra.
Qed.

Lemma anchor_short_only : short_only effective11=true /\
  short_only effective12=true /\ short_only effective49=true.
Proof. vm_compute; auto. Qed.

Lemma copied_stage_bounds pre pe carry budget u ds A H k v a b s e f :
  Copy 0 12 pre pe carry budget -> short_only pe=true ->
  Scan 12 (pe++u++ds++[W0]) k v a b ->
  Digits A H ds -> cut_ok u=true ->
  (exists c w, (0<c /\ s<=c)%nat /\ ds=repeat W1 c++W0::w) ->
  e==scale pre*mass u ->
  (scale pre*scale u)*(qnat (2^(s+s/2))%nat+2*zeros ds)<=f*qnat (2^(s+s/2))%nat ->
  exists w, v=pre++w /\
    mass (WT::(v++[WT]))<=mass pre*(1#2)+(e+f)*(1#2) /\
    copy_loss pre pe-e*(1#4)-3*f<=a-b /\
    a-b<=copy_loss pre pe+4*e+4*f.
Proof.
  intros C Safe I D Cut Low Error Bound.
  destruct (Copy_scan_prefix _ _ _ _ _ _ C Safe _ _ _ _ _ I)
    as [w [c [d [-> [J [Pos Neg]]]]]].
  destruct (Scan_cut _ _ _ _ _ _ J u (ds++[W0]) eq_refl)
    as [m [x [y [a1 [b1 [a2 [b2 [K [L [-> [P N]]]]]]]]]]]; [left; apply Cut|].
  pose proof (Scan_bounds _ _ _ _ _ _ K).
  pose proof (Scan_bounds _ _ _ _ _ _ L).
  pose proof (Scan_scale _ _ _ _ _ _ K).
  pose proof (scale_pos pre); pose proof (scale_pos u); pose proof (scale_pos x).
  pose proof (weights_nonneg ds); pose proof (qpow_pos (s+s/2)%nat).
  assert (F : (scale pre*scale x)*(qnat (2^(s+s/2))%nat+2*zeros ds)<=
    f*qnat (2^(s+s/2))%nat).
  { eapply Qle_trans; [|apply Bound]; apply Qmult_le_compat_r; nra. }
  destruct (Scan_tail_low_scaled _ _ _ _ _ _ _ _ _ (scale pre*scale x) f D L Low)
    as [Mt [Pt Nt]]; [nra|apply F|].
  assert (Pa:0<=scale pre*scale x*a2) by (apply Qmult_le_0_compat; nra).
  assert (Pb:0<=scale pre*scale x*b2) by (apply Qmult_le_0_compat; nra).
  exists (x++y); split; [reflexivity|].
  cbn[mass]; rewrite !mass_app; cbn[mass scale].
  rewrite P in Pos; rewrite N in Neg.
  repeat split; nra.
Qed.

Lemma copied_carry_bounds pre pe b k u carry eff : Copy 0 12 pre pe b k ->
  Effective 0 (pre++u) carry eff ->
  copy_loss pre pe-2*mass pre<=qnat (1+carry)%nat*scale (pre++u)-1 /\
  qnat (1+carry)%nat*scale (pre++u)-1<=copy_loss pre pe-2*mass pre+2*scale pre*mass u.
Proof.
  intros C E; destruct (Copy_effective_prefix _ _ _ _ _ _ C _ _ _ E) as [v [_ V]].
  destruct (Effective_bounds _ _ _ _ V) as [Lo Hi].
  pose proof (scale_pos pre).
  apply (Qmult_le_compat_r _ _ (scale pre)) in Lo,Hi; try lra.
  destruct (Copy_ledger _ _ _ _ _ _ C) as [L _].
  change (qnat (1+0)%nat) with 1 in L.
  rewrite scale_app; split; nra.
Qed.

(* a need only lie in the dyadic interval indexed by p. *)
Lemma reserve_tail_interval p H s alpha unit tau f : Reserve p tau ->
  (32<=p)%nat -> (2*p+3<=H)%nat -> (s=(p-2)/2)%nat ->
  0<alpha -> 0<unit -> (1#2)<=alpha*qnat (2^p)%nat -> unit*qnat (2^H)%nat==1 ->
  f*qnat (2^(s+s/2))%nat<=unit*qnat (2^(s+s/2))%nat+5*alpha ->
  f<=alpha*tau*(1#4).
Proof.
  intros I P Hbound S A U Ap Uh F.
  inversion I as [n t Tau|n t Tau]; subst t.
  all: assert (N:(16<=n)%nat) by lia.
  all: assert (Low:32*qnat (2^n)%nat<=qnat (2^(s+s/2))%nat) by
    (change (qnat (2^5)%nat*qnat (2^n)%nat<=qnat (2^(s+s/2))%nat);
     rewrite <-qnat_mul, <-Nat.pow_add_r; apply qnat_le, Nat.pow_le_mono_r; lia).
  all: assert (High:64*qnat (2^p)%nat*qnat (2^n)%nat<=qnat (2^H)%nat) by
    (change (qnat (2^6)%nat*qnat (2^p)%nat*qnat (2^n)%nat<=qnat (2^H)%nat);
     rewrite <-!qnat_mul, <-!Nat.pow_add_r; apply qnat_le, Nat.pow_le_mono_r; lia).
  all: pose proof (qpow_pos n); pose proof (qpow_pos p).
  all: assert (Gap:32*qnat (2^n)%nat*unit<=alpha) by
    (apply (Qmult_le_compat_r _ _ unit) in High; [nra|lra]).
  all: eapply reserve_scaled with (t:=qnat (2^n)%nat) (q:=qnat (2^(s+s/2))%nat); eauto; nra.
Qed.

Lemma unit_interval_small p H alpha unit : (p+11<=H)%nat ->
  0<alpha -> 0<unit -> (1#2)<=alpha*qnat (2^p)%nat -> unit*qnat (2^H)%nat==1 ->
  unit<=alpha*(1#1024).
Proof.
  intros PH A U Ap Uh.
  assert (High:2048*qnat (2^p)%nat<=qnat (2^H)%nat) by
    (change (qnat (2^11)%nat*qnat (2^p)%nat<=qnat (2^H)%nat);
     rewrite <-qnat_mul, <-Nat.pow_add_r; apply qnat_le, Nat.pow_le_mono_r; lia).
  pose proof (qpow_pos p); apply (Qmult_le_compat_r _ _ unit) in High; [nra|lra].
Qed.

Lemma anchor_deficit_step alpha e f unit delta R e' rho :
  0<alpha -> 0<=e -> 0<=f -> 0<=unit ->
  e<=alpha*(1#1024) -> f<=alpha*(1#1024) -> unit<=alpha*(1#1024) ->
  0<=e' -> e'<=(e+f)*(1#2) -> rho*(1#2)<=R -> R<=rho*(1#2)+2*e' ->
  2*alpha+rho-e*(1#4)-3*f<=delta -> delta<=2*alpha+rho+4*e+4*f ->
  (3#4)*alpha<=delta*(1#2)-4*unit-R /\
  delta*(1#2)-4*unit-R<=(5#4)*alpha.
Proof. intros; split; lra. Qed.

Lemma anchor_compensated_window J k carry alpha unit delta R rho :
  0<alpha -> alpha<=(1#32) -> 0<unit -> unit<=alpha*(1#1024) ->
  unit*qnat (2^J)%nat==1 -> 0<=rho -> rho<=2*alpha ->
  (7#4)*alpha+rho<=delta -> delta<=(9#4)*alpha+rho ->
  rho*(1#2)<=R -> R<=rho*(1#2)+alpha*(1#4) ->
  qnat k*unit==2+4*unit-delta*(1#2) -> qnat (1+carry)%nat*unit==1+R ->
  exists A B, (A+2^J=k /\ B+2^J=A+carry /\
    2^J<=A*2 /\ A<2^J /\ 2^J<=B*2 /\ B<2^J)%nat.
Proof.
  intros Pos Small Unit Tiny Height Rho RhoBound Dl Du Rl Ru K C.
  rewrite qnat_add in C; change (qnat 1%nat) with 1 in C.
  assert (Knat:(2^J<=k)%nat) by (apply qnat_le; nra).
  assert (Bnat:(2^J+2^J<=k+carry)%nat) by
    (apply qnat_le; rewrite !qnat_add; nra).
  exists (k-2^J)%nat, (k+carry-(2^J+2^J))%nat.
  repeat split; try lia.
  all: apply qnat_lt || apply qnat_le; rewrite ?qnat_mul;
    change (qnat 2%nat) with 2; rewrite !qnat_sub by lia; rewrite ?qnat_add; nra.
Qed.


Lemma short_only_Ts q v : short_only v=true -> short_only (repeat WT q++v)=true.
Proof. induction q; cbn[repeat app short_only]; auto. Qed.

Inductive AnchorGood (av:list Word) : nat -> nat -> list Word -> Prop :=
| AnchorGood_intro p q H u A da carry eff B db tau alpha :
    (32<=p)%nat -> (5<=q)%nat -> (2*p+3<=H)%nat ->
    (exists rest, u=(repeat WT q++av)++rest) -> (exists rest, u=rest++[WT]) ->
    mass (repeat WT q++av)==alpha ->
    (1#2)<=alpha*qnat (2^p)%nat -> alpha*qnat (2^p)%nat<=1 ->
    scale u*qnat (2^H)%nat==1 -> Digits A H da ->
    Effective 0 u carry eff -> (A+carry=B+2^H)%nat -> Digits B H db ->
    Reserve p tau -> mass u<=alpha*(1+(1#1024)-tau) ->
    (3#2)*alpha<=scale u*zeros db -> scale u*zeros db<=(5#2)*alpha ->
    (exists rest, db=repeat W1 ((p-2)/2)%nat++rest) ->
    AnchorGood av p q (u++da++[W1]).

Lemma AnchorGood_next av ev : short_only ev=true ->
  (forall q, (5<=q)%nat -> Copies (repeat WT q++av) (repeat WT q++ev)) ->
  forall p q orig, AnchorGood av p q orig ->
    exists out, Step orig out /\ AnchorGood av (1+p)%nat (1+q)%nat out.
Proof.
  intros Safe Stable p q orig G.
  destruct G as [p q H u A da carry eff B db tau alpha P Q Hbound [rest Start] End
    Mass ApLow ApHigh Height DA Eff Sum DB Res M Dlo Dhi Low].
  set (pre:=repeat WT q++av) in *; set (pe:=repeat WT q++ev) in *.
  set (unit:=scale u) in *.
  pose proof (qpow_pos p) as PowP.
  assert (Alpha:0<alpha) by nra.
  pose proof (scale_pos u) as Unit; fold unit in Unit.
  set (dyadic:=scale (repeat WT p)).
  pose proof (proj2 (repeat_T_weights p)) as DP; fold dyadic in DP.
  pose proof (scale_pos (repeat WT p)) as Dyadic; fold dyadic in Dyadic.
  assert (Aupper:alpha<=dyadic) by nra.
  pose proof (alpha_small _ P) as Asmall; fold dyadic in Asmall.
  pose proof (Reserve_small _ _ Res P) as [Tau TauSmall].
  assert (Usmall:unit<=alpha*(1#1024)) by
    (eapply (unit_interval_small p H alpha unit); eauto; lia).
  destruct (Stable q Q) as [bc [kc CopyPre]]; fold pre pe in CopyPre.
  assert (SafePre:short_only pe=true) by (apply short_only_Ts, Safe).
  destruct (Copy_ledger _ _ _ _ _ _ CopyPre) as [Ledger [RhoLow RhoHigh]].
  change (qnat (1+0)%nat) with 1 in Ledger,RhoLow,RhoHigh.
  set (rho:=copy_loss pre pe-2*alpha).
  assert (Rho:0<=rho /\ rho<=2*alpha) by (unfold rho; rewrite Mass in *; nra).
  destruct (Effective_weights _ _ _ _ Eff) as [EffScale EffMass].
  destruct (Effective_end_T _ _ _ _ Eff End) as [last Elast].
  assert (Cut:cut_ok eff=true) by (rewrite Elast; apply cut_ok_last).
  assert (Ne:eff<>[]) by (rewrite Elast; intro E; apply app_eq_nil in E; destruct E; discriminate).
  assert (EffHeight:scale eff*qnat (2^H)%nat==1) by (rewrite EffScale; apply Height).
  assert (EffBound:mass eff+scale eff*(1+zeros db)<=(1#128)) by
    (rewrite EffScale, EffMass; fold unit; nra).
  destruct (C12_scan _ _ _ _ DB EffHeight Cut Ne EffBound) as [k [v [a [b [Iscan K]]]]].
  assert (Z:0<zeros db) by nra.
  destruct (Digits_high_small p H B db dyadic unit DB ltac:(lia) ltac:(lia)
    Dyadic Unit ltac:(lra) DP Height ltac:(lra)) as [hi Hi].
  destruct (Digits_two_runs _ _ _ _ _ DB Z Low (ex_intro _ hi Hi))
    as [c [mid [t [Split [MidCut [C T]]]]]].
  destruct (Scan_output_height_large eff db B H 12 k v a b p c mid t DB EffHeight Iscan
    Cut MidCut Split P C T) as [J [Jbound Jheight]].
  set (new:=WT::(v++[WT])) in *; set (nu:=scale new) in *.
  pose proof (scale_pos new) as Nu; fold nu in Nu.
  assert (NuSmall:nu<=alpha*(1#1024)) by
    (eapply (unit_interval_small p J alpha nu); eauto; lia).
  assert (EffRest:exists w, eff=pe++w /\ Effective bc rest carry w).
  { rewrite Start in Eff; eapply Copy_effective_prefix; eauto. }
  destruct EffRest as [w [Estart Ew]].
  destruct (Effective_weights _ _ _ _ Ew) as [Wscale Wmass].
  assert (Wcut:cut_ok w=true) by (rewrite Estart in Cut; apply cut_ok_app_tail in Cut; apply Cut).
  set (e:=mass u-alpha).
  assert (Eeq:e==scale pre*mass w) by (unfold e; rewrite Start, mass_app, <-Wmass, Mass; ring).
  pose proof (weights_nonneg w); pose proof (scale_pos pre).
  assert (Epos:0<=e) by nra.
  assert (Ebound:e<=alpha*((1#1024)-tau)) by (unfold e; nra).
  set (s:=((p-2)/2)%nat); set (pow:=qnat (2^(s+s/2))%nat).
  pose proof (qpow_pos (s+s/2)%nat) as Pow; fold pow in Pow.
  set (f:=unit+2*unit*zeros db/pow).
  assert (Feq:f*pow==unit*pow+2*unit*zeros db) by (unfold f; field; lra).
  assert (Fpos:0<=f) by nra.
  assert (Fbound:f<=alpha*tau*(1#4)).
  { eapply (reserve_tail_interval p H s alpha unit tau f); eauto; try lia; fold pow; nra. }
  assert (Low':exists c w, (0<c /\ s<=c)%nat /\ db=repeat W1 c++W0::w).
  { exists c, (mid++repeat W1 t); split; [unfold s; lia|apply Split]. }
  assert (Factor:scale pre*scale w==unit) by (unfold unit; rewrite Start, scale_app, Wscale; reflexivity).
  assert (ScanStart:Scan 12 (pe++w++db++[W0]) k v a b).
  { rewrite Estart in Iscan; rewrite <-app_assoc in Iscan; apply Iscan. }
  destruct (copied_stage_bounds pre pe bc kc w db B H k v a b s e f CopyPre SafePre
    ScanStart DB Wcut Low') as [tail [Vstart [Mnext [Dl Du]]]];
    [apply Eeq|fold pow; rewrite Factor; nra|].
  fold new in Mnext; rewrite Mass in Mnext.
  assert (Dl':2*alpha+rho-e*(1#4)-3*f<=a-b) by (unfold rho; lra).
  assert (Du':a-b<=2*alpha+rho+4*e+4*f) by (unfold rho; lra).
  destruct (Effective_ex new 0) as [carry' [eff' Eff']].
  assert (NewStart:new=(WT::pre)++(tail++[WT])) by
    (unfold new; rewrite Vstart, <-app_assoc; reflexivity).
  destruct (Stable (1+q)%nat ltac:(lia)) as [bc' [kc' CopyNew]].
  change (Copy 0 12 (WT::pre) (WT::pe) bc' kc') in CopyNew.
  pose proof (copied_carry_bounds _ _ _ _ (tail++[WT]) carry' eff' CopyNew) as Rbounds.
  rewrite <-NewStart in Rbounds; specialize (Rbounds Eff').
  assert (NewMass:mass new==alpha*(1#2)+(scale pre*(1#2))*mass (tail++[WT])).
  { rewrite NewStart, mass_app; cbn[mass scale]; rewrite Mass; ring. }
  cbn[scale mass] in Rbounds; unfold copy_loss in Rbounds; cbn[scale mass ones] in Rbounds.
  fold (copy_loss pre pe) in Rbounds.
  set (R:=qnat (1+carry')%nat*nu-1).
  assert (Rb:rho*(1#2)<=R /\ R<=rho*(1#2)+2*(mass new-alpha*(1#2))).
  { unfold R, nu, rho, copy_loss; rewrite Mass in Rbounds; nra. }
  pose proof (weights_nonneg (tail++[WT])).
  assert (Enew:0<=mass new-alpha*(1#2)) by (clear -NewMass H1 H2; nra).
  assert (Ftiny:f<=alpha*(1#1024)) by (clear -Fbound Alpha TauSmall; nra).
  assert (Etiny:e<=alpha*(1#1024)) by (clear -Ebound Alpha Tau; nra).
  pose proof (Scan_output_budget _ _ _ _ _ Iscan) as Budget; fold new nu in Budget.
  destruct (anchor_compensated_window J k carry' alpha nu (a-b) R rho Alpha ltac:(lra)
    Nu NuSmall Jheight ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)
    ltac:(lra) ltac:(lra) Budget ltac:(unfold R; ring))
    as [A' [B' [Asum [Bsum [Al [Au [Bl Bu]]]]]]].
  destruct (Digits_ex J A' Au) as [da' DA']; destruct (Digits_ex J B' Bu) as [db' DB'].
  destruct (Reserve_next _ _ Res) as [tau' [Res' TauStep]].
  pose proof (reserve_error_step alpha tau tau' e f (mass new-alpha*(1#2))
    ltac:(lra) TauStep Ebound Fbound ltac:(lra)) as Mkeep.
  pose proof (anchor_deficit_step alpha e f nu (a-b) R (mass new-alpha*(1#2)) rho
    Alpha Epos Fpos ltac:(lra) Etiny Ftiny NuSmall Enew ltac:(lra)
    ltac:(lra) ltac:(lra) Dl' Du') as Dkeep.
  pose proof (Scan_compensated_deficit _ _ _ _ _ J A' B' carry' Iscan Jheight Asum Bsum) as Def.
  fold new nu R in Def; pose proof (Digits_zeros _ _ _ DB') as Znew.
  rewrite qnat_add in Def; change (qnat 1%nat) with 1 in Def.
  assert (Dnew:nu*zeros db'==(a-b)*(1#2)-4*nu-R) by
    (clear -Def Znew Jheight; nra).
  assert (LowNew:exists rest, db'=repeat W1 (((1+p)-2)/2)%nat++rest).
  { set (r:=((((1+p)-2)/2)-1)%nat).
    assert (Hr:(1+r=(((1+p)-2)/2) /\ 1+r*2<=p-2)%nat) by (unfold r; lia).
    assert (HighEnd:exists z, db=z++repeat W1 (1+r*2)%nat).
    { exists (hi++repeat W1 ((p-2)-(1+r*2))%nat); rewrite Hi, <-app_assoc, <-repeat_app.
      f_equal; f_equal; lia. }
    destruct HighEnd as [z HZ].
    assert (SC:Scan 12 ((eff++z)++repeat W1 (1+r*2)%nat++[W0]) k v a b).
    { rewrite <-!app_assoc; rewrite HZ in Iscan; rewrite <-!app_assoc in Iscan; apply Iscan. }
    destruct (low_ones_regenerated r 12 (eff++z) k v a b carry' eff' A' B' J db'
      SC Eff' DB' ltac:(lia) Asum Bsum) as [z' L].
    exists z'; rewrite (proj1 Hr) in L; apply L. }
  exists (new++da'++[W1]); split.
  - unfold new; cbn[app].
    applys_eq (Step_intro (u++da++[W1]) (eff++db++[W0]) k v a b J A' da');
      try (rewrite <-!app_assoc; reflexivity).
    + destruct (Effective_compensate _ _ _ _ _ DA Sum (Digits_bound _ _ _ DB)) as [d [DD EE]].
      assert (d=db) by (eapply Digits_unique; eauto); subst d.
      eapply Effective_app; eauto.
    + apply Iscan.
    + apply DA'.
    + apply Asum.
  - eapply (AnchorGood_intro av (1+p)%nat (1+q)%nat J new A' da' carry' eff' B' db' tau'
      (alpha*(1#2))); eauto; try lia.
    + exists (WT::v); reflexivity.
    + change (mass (WT::pre)==alpha*(1#2)); cbn[mass]; rewrite Mass; reflexivity.
    + cbn[Nat.add Nat.pow]; rewrite qnat_mul; change (qnat 2%nat) with 2; nra.
    + cbn[Nat.add Nat.pow]; rewrite qnat_mul; change (qnat 2%nat) with 2; nra.
    + lra.
    + change ((3#2)*(alpha*(1#2))<=nu*zeros db'); rewrite Dnew; lra.
    + change (nu*zeros db'<=(5#2)*(alpha*(1#2))); rewrite Dnew; lra.
Qed.

End Weights.

(* Finite entrance: all runtime counters are binary, and the final check
   returns bool. Soundness reuses Step and the already closed invariant. *)
Local Open Scope nat_scope.

Definition carryN w n : Word*N :=
  match w with
  | WT => (WT, N.succ_double n)
  | _ => let m := match w with W1 => N.succ n | _ => n end in
      (digitW (N.odd m), N.div2 m)
  end.

Lemma carryN_spec w n d m : carryN w n=(d,m) -> forall u b v,
  Effective (N.to_nat m) u b v -> Effective (N.to_nat n) (w::u) b (d::v).
Proof.
  destruct w; destruct n as [|[q|q|]]; cbn[carryN digitW N.odd N.div2 N.succ];
    intros E u b v I; inversion E; subst d m; cbn[N.to_nat] in *;
    rewrite ?N2Nat.inj_succ_double, ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO,
      ?Pos2Nat.inj_succ in *.
  all: first [solve [applys_eq Effective_T; flia; applys_eq I; flia]
             |solve [applys_eq (Effective_00 _ _ _ _ I); flia]
             |solve [applys_eq (Effective_01 _ _ _ _ I); flia]
             |solve [applys_eq (Effective_10 _ _ _ _ I); flia]
             |solve [applys_eq (Effective_11 _ _ _ _ I); flia]].
Qed.

Fixpoint effectiveN u n acc : N*list Word :=
  match u with
  | [] => (n,rev_append acc [])
  | w::u => let '(d,m):=carryN w n in effectiveN u m (d::acc)
  end.

Lemma effectiveN_spec u : forall n acc b out, effectiveN u n acc=(b,out) ->
  exists v, out=rev_append acc v /\ Effective (N.to_nat n) u (N.to_nat b) v.
Proof.
  induction u as [|w u IH]; intros n acc b out E; cbn[effectiveN] in E.
  - inversion E; exists (@nil Word); split; [reflexivity|constructor].
  - destruct (carryN w n) as [d m] eqn:C.
    destruct (IH _ _ _ _ E) as [v [V I]].
    exists (d::v); split; [exact V|eapply carryN_spec; eauto].
Qed.

Fixpoint scanN u k acc {struct u} : option (N*list Word) :=
  match u with
  | [] => Some (k,rev_append acc [])
  | w::u => match k with
    | N0 => None
    | Npos p => match w with
      | WT => if N.leb 3 k then scanN u (N.double (k-2)) (WT::acc) else None
      | W0 => match shortN false k with
        | Some(d,k') => scanN u k' (d::acc) | None => None end
      | W1 => if match p with xO _ => singleN (W1::u) | _ => false end then
          match shortN true k with
          | Some(d,k') => scanN u k' (d::acc) | None => None end
        else match u with
          | W0::v => scanN v (N.double (N.pred k)) (WT::acc)
          | W1::v => scanN v (N.succ_double (N.pred k)) (WT::acc)
          | _ => None end
      end
    end
  end.

Lemma Scan_TN k u k' v a b : (3<=k)%N ->
  Scan (N.to_nat (N.double (k-2))) u k' v a b ->
  exists c d, Scan (N.to_nat k) (WT::u) k' (WT::v) c d.
Proof.
  intros K I; exists (a*(1#2))%Q, (b*(1#2))%Q.
  rewrite N2Nat.inj_double, N2Nat.inj_sub in I; cbn[N.to_nat] in I.
  assert (3<=N.to_nat k) by lia.
  applys_eq (Scan_T (N.to_nat k-3)); flia; applys_eq I; flia.
Qed.

Lemma Scan_pairN e p u k' v a b :
  Scan (N.to_nat (digitN e (N.pred (Npos p)))) u k' v a b ->
  exists c d, Scan (Pos.to_nat p) (W1::digitW e::u) k' (WT::v) c d.
Proof.
  destruct e; cbn[digitN digitW]; intro I;
    rewrite ?N2Nat.inj_succ_double, ?N2Nat.inj_double, N2Nat.inj_pred in I;
    cbn[N.to_nat] in I; pose proof (Pos2Nat.is_pos p).
  - eexists _, _; applys_eq (Scan_pair1 (Pos.to_nat p-1)); flia; applys_eq I; flia.
  - eexists _, _; applys_eq (Scan_pair0 (Pos.to_nat p-1)); flia; applys_eq I; flia.
Qed.

Lemma Scan_shortN e k d k' u c v a b : shortN e k=Some(d,k') ->
  Scan (N.to_nat k') u c v a b ->
  exists x y, Scan (N.to_nat k) (digitW e::u) c (d::v) x y.
Proof.
  destruct k as [|[p|p|]]; try discriminate.
  destruct p as [p|p|]; cbn[shortN]; intro E; inversion E; subst d k';
    destruct e; cbn[digitW digitN]; intro I;
    rewrite ?N2Nat.inj_succ_double, ?N2Nat.inj_double, ?N2Nat.inj_pred in I;
    cbn[N.to_nat] in *; rewrite ?Pos2Nat.inj_xO, ?Pos2Nat.inj_xI;
    try pose proof (Pos2Nat.is_pos p).
  all: eexists _, _;
    first [solve [applys_eq (Scan_short00 (Pos.to_nat p)); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short01 (Pos.to_nat p)); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short10 (Nat.pred (Pos.to_nat p))); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short11 (Nat.pred (Pos.to_nat p))); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short00 0); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short01 0); flia; applys_eq I; flia]].
Qed.

Lemma scanN_spec : forall u k acc k' out, scanN u k acc=Some(k',out) ->
  exists v a b, out=rev_append acc v /\ Scan (N.to_nat k) u (N.to_nat k') v a b.
Proof.
  fix IH 1; intros u k acc k' out E; destruct u as [|w u].
  - inversion E; exists (@nil Word), 0%Q, 0%Q; split; [reflexivity|constructor].
  - destruct k as [|p]; [discriminate|]; destruct w; cbn[scanN] in E.
    + destruct (N.leb 3 (Npos p)) eqn:K; [apply N.leb_le in K|discriminate].
      destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
      destruct (Scan_TN _ _ _ _ _ _ K I) as [c [d S]].
      exists (WT::v), c, d; auto.
    + destruct (shortN false (Npos p)) as [[d m]|] eqn:C; [|discriminate].
      destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
      destruct (Scan_shortN _ _ _ _ _ _ _ _ _ C I) as [x [y S]].
      exists (d::v), x, y; auto.
    + destruct (match p with xO _ => singleN (W1::u) | _ => false end).
      * destruct (shortN true (Npos p)) as [[d m]|] eqn:C; [|discriminate].
        destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
        destruct (Scan_shortN _ _ _ _ _ _ _ _ _ C I) as [x [y S]].
        exists (d::v), x, y; auto.
      * destruct u as [|w u]; [discriminate|]; destruct w; [discriminate| |].
        all: destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
        -- destruct (Scan_pairN false _ _ _ _ _ _ I) as [c [d S]]; exists (WT::v), c, d; auto.
        -- destruct (Scan_pairN true _ _ _ _ _ _ I) as [c [d S]]; exists (WT::v), c, d; auto.
Qed.

Lemma pwords_digits p : exists A H da, pwords p=da++[W1] /\
  Digits A H da /\ A+2^H=Pos.to_nat p.
Proof.
  induction p as [p [A [H [da [E [D Sum]]]]]|p [A [H [da [E [D Sum]]]]]|].
  - exists (1+A*2), (1+H), (W1::da); cbn[pwords]; rewrite E; split; [reflexivity|].
    split; [apply Digits_one, D|rewrite Pos2Nat.inj_xI; cbn[Nat.add Nat.pow]; lia].
  - exists (A*2), (1+H), (W0::da); cbn[pwords]; rewrite E; split; [reflexivity|].
    split; [apply Digits_zero, D|rewrite Pos2Nat.inj_xO; cbn[Nat.add Nat.pow]; lia].
  - exists 0, 0, (@nil Word); split; [reflexivity|split; [constructor|reflexivity]].
Qed.

Definition roundN u :=
  let '(carry,eff):=effectiveN u 0%N [] in
  if N.eqb carry 1 then
    match scanN eff 12%N [] with
    | Some(Npos k,v) => Some(WT::(v++WT::pwords k))
    | _ => None end
  else None.

Lemma roundN_spec u out : roundN u=Some out -> Step u out.
Proof.
  unfold roundN; destruct (effectiveN u 0 []) as [carry eff] eqn:E.
  destruct (N.eqb carry 1) eqn:C; [apply N.eqb_eq in C; subst carry|discriminate].
  destruct (scanN eff 12 []) as [[k v]|] eqn:S; [|discriminate].
  destruct k as [|k]; [discriminate|]; intro O; inversion O; subst out.
  destruct (effectiveN_spec _ _ _ _ _ E) as [w [V I]]; cbn[rev_append] in V; subst w.
  destruct (scanN_spec _ _ _ _ _ S) as [w [a [b [V J]]]]; cbn[rev_append] in V; subst w.
  destruct (pwords_digits k) as [A [H [da [D [DA Sum]]]]]; rewrite D.
  eapply Step_intro; eauto.
Qed.

Lemma reverse_prefix u pre rest : strip_words pre (rev_append u [])=Some rest ->
  u=rev_append rest (rev pre).
Proof.
  intro E; apply strip_words_spec in E; rewrite rev_append_rev, app_nil_r in E.
  apply (f_equal (@rev Word)) in E; rewrite rev_involutive, rev_app_distr in E.
  rewrite rev_append_rev; apply E.
Qed.

Lemma tail_cut_end u p ds : tail_cut u=Some(p,ds) -> exists v, p=v++[WT].
Proof.
  assert (G:forall w d, tail_cut_rev w d=Some(p,ds) -> exists v, p=v++[WT]).
  { induction w as [|x w IH]; intros d E; [discriminate|].
    destruct x; cbn[tail_cut_rev] in E; eauto.
    inversion E; exists (rev w); apply rev_append_rev. }
  apply G.
Qed.

Lemma Digits_only A H u : Digits A H u -> forallb is_digit u=true.
Proof. intro I; induction I; cbn[forallb is_digit]; auto. Qed.

Definition entry_high := [W1;W1;W0]++repeat W1 30.

Local Open Scope Q_scope.

Lemma entry_high_stats : zeros entry_high==4 /\
  scale entry_high*scale (repeat WT 32)==2.
Proof. vm_compute; split; reflexivity. Qed.

Lemma entry_tail_bounds B H db u : Digits B H db ->
  scale u*qnat (2^H)%nat==1 ->
  (exists lo, db=lo++entry_high) ->
  (3#2)*scale (repeat WT 32)<=scale u*zeros db /\
  scale u*zeros db<=(5#2)*scale (repeat WT 32).
Proof.
  intros D Height [lo Eq]; pose proof (Digits_only _ _ _ D) as Dig.
  rewrite Eq, forallb_app in Dig; apply andb_true_iff in Dig; destruct Dig as [Dig _].
  destruct (digit_list _ Dig) as [A DA].
  pose proof (Digits_weights _ _ _ DA) as [Ls [Lm Lo]].
  pose proof (Digits_weights _ _ _ D) as [Ds _].
  pose proof (mass_split lo); pose proof (weights_nonneg lo).
  pose proof (scale_pos u); pose proof (scale_pos lo).
  pose proof (scale_pos entry_high); pose proof (scale_pos (repeat WT 32)).
  destruct entry_high_stats as [Z S].
  rewrite Eq, scale_app in Ds.
  set (x:=scale u*scale lo).
  assert (X:x*scale entry_high==1) by (unfold x; nra).
  assert (Xa:2*x==scale (repeat WT 32)) by nra.
  rewrite Eq, zeros_app, Z; unfold x in Xa; split; nra.
Qed.

Definition entry_mass_check rest :=
  N.leb (rounded (2^16)%N (2^16)%N (rev_append rest []) 0%N) 16%N.

Lemma entry_mass_bound rest : entry_mass_check rest=true -> mass rest<=(1#4096).
Proof.
  unfold entry_mass_check; intro E; apply N.leb_le, qN_le in E.
  pose proof (rounded_forward (2^16)%N (2^16)%N rest 0%N) as R.
  change (qN (2^16)%N) with 65536 in R; change (qN 0%N) with 0 in R.
  change (qN 16%N) with 16 in E; rewrite mass_split; lra.
Qed.

Definition entry_check orig :=
  match tail_cut orig with
  | None => false
  | Some(u,tail) => match strip_words [W1] (rev_append tail []) with
    | None => false
    | Some rd => let da:=rev_append rd [] in
      match strip_words (repeat WT 32++[W1]) u, heightN u 0 with
      | Some rest, Some H =>
        if Nat.leb 67 H then if Nat.eqb H (length da) then
          let '(carry,eff):=effectiveN u 0%N [] in
          let '(last,db):=effectiveN da carry [] in
          if N.eqb last 1 then
            match strip_words (repeat W1 15) db,
              strip_words (rev entry_high) (rev_append db []) with
            | Some _, Some _ => entry_mass_check rest
            | _, _ => false end
          else false
        else false else false
      | _, _ => false end
    end
  end.

Lemma entry_check_spec orig : entry_check orig=true -> Good 32 orig.
Proof.
  unfold entry_check; destruct (tail_cut orig) as [[u tail]|] eqn:C; [|discriminate].
  destruct (strip_words [W1] (rev_append tail [])) as [rd|] eqn:Top; [|discriminate].
  destruct (strip_words (repeat WT 32++[W1]) u) as [rest|] eqn:Start; [|discriminate].
  destruct (heightN u 0) as [H|] eqn:Height; [|discriminate].
  destruct (Nat.leb 67 H) eqn:Hbound; [apply Nat.leb_le in Hbound|discriminate].
  destruct (Nat.eqb H (length (rev_append rd []))) eqn:Width;
    [apply Nat.eqb_eq in Width|discriminate].
  destruct (effectiveN u 0 []) as [carry eff] eqn:E.
  destruct (effectiveN (rev_append rd []) carry []) as [last db] eqn:F.
  destruct (N.eqb last 1) eqn:Last; [apply N.eqb_eq in Last; subst last|discriminate].
  destruct (strip_words (repeat W1 15) db) as [lo|] eqn:Low; [|discriminate].
  destruct (strip_words (rev entry_high) (rev_append db [])) as [hi|] eqn:High; [|discriminate].
  intro Mass; apply entry_mass_bound in Mass.
  destruct (tail_cut_spec _ _ _ C) as [Orig Dig].
  pose proof (tail_cut_end _ _ _ C) as End.
  apply reverse_prefix in Top; cbn[rev] in Top.
  assert (Tail:tail=rev_append rd []++[W1]) by
    (rewrite Top, !rev_append_rev, app_nil_r; reflexivity).
  rewrite Tail, forallb_app in Dig; apply andb_true_iff in Dig; destruct Dig as [Dig _].
  destruct (digit_list _ Dig) as [A DA]; rewrite <-Width in DA.
  destruct (effectiveN_spec _ _ _ _ _ E) as [v [V Eff]]; cbn[rev_append] in V; subst v.
  destruct (effectiveN_spec _ _ _ _ _ F) as [v [V EffD]]; cbn[rev_append] in V; subst v.
  destruct (Effective_digits _ _ _ _ EffD _ _ DA) as [B [DB Sum]].
  apply strip_words_spec in Start; rewrite <-app_assoc in Start; cbn[app] in Start.
  apply heightN_spec in Height; change (qnat (2^0)%nat) with 1 in Height.
  assert (High':exists x, db=x++entry_high).
  { apply reverse_prefix in High; rewrite rev_involutive, rev_append_rev in High; eauto. }
  destruct (entry_tail_bounds _ _ _ _ DB Height High') as [Dlo Dhi].
  rewrite Orig, Tail.
  eapply (Good_intro 32 H u A (rev_append rd []) (N.to_nat carry) eff B db (1#65536));
    eauto; try lia.
  - apply Reserve_even with (n:=16%nat); vm_compute; reflexivity.
  - rewrite Start, first_digit_mass; pose proof (scale_pos (repeat WT 32)); nra.
  - exists lo; apply strip_words_spec, Low.
Qed.

Local Open Scope nat_scope.

Inductive Rounds : list Word -> list Word -> Prop :=
| Rounds_refl u : Rounds u u
| Rounds_next u v w : Step u v -> Rounds v w -> Rounds u w.

Fixpoint verify n u :=
  match n with
  | O => entry_check u
  | S n => match roundN u with None => false | Some v => verify n v end
  end.

Lemma verify_spec n : forall u, verify n u=true ->
  exists v, Rounds u v /\ Good_side (to_side v 0inf).
Proof.
  induction n as [|n IH]; intros u E.
  - exists u; split; [constructor|exists 32, u; split; [apply entry_check_spec, E|reflexivity]].
  - change ((match roundN u with Some v => verify n v | None => false end)=true) in E.
    destruct (roundN u) as [v|] eqn:V; [|discriminate].
    destruct (IH _ E) as [w [R G]]; exists w; split; [eapply Rounds_next|]; eauto using roundN_spec.
Qed.

Definition start := [WT;WT;W1;WT;WT;WT;WT;W0;W1;W0;W1;W0;W1].

Lemma entry_check30 : verify 30 start=true.
Proof. vm_compute; reflexivity. Qed.

Local Open Scope Q_scope.

Lemma anchor_entry_tail_bounds B H db u high alpha : Digits B H db ->
  scale u*qnat (2^H)%nat==1 -> (exists lo, db=lo++high) ->
  (3#2)*alpha*scale high<=zeros high ->
  zeros high+1<=(5#2)*alpha*scale high ->
  (3#2)*alpha<=scale u*zeros db /\ scale u*zeros db<=(5#2)*alpha.
Proof.
  intros D Height [lo Eq] L R; pose proof (Digits_only _ _ _ D) as Dig.
  rewrite Eq, forallb_app in Dig; apply andb_true_iff in Dig; destruct Dig as [Dig _].
  destruct (digit_list _ Dig) as [A DA].
  pose proof (Digits_weights _ _ _ DA) as [Ls [Lm Lo]].
  pose proof (Digits_weights _ _ _ D) as [Ds _].
  pose proof (mass_split lo); pose proof (weights_nonneg lo).
  pose proof (scale_pos u); pose proof (scale_pos lo); pose proof (scale_pos high).
  rewrite Eq, scale_app in Ds.
  set (x:=scale u*scale lo).
  assert (X:x*scale high==1) by (unfold x; nra).
  assert (XP:0<x) by (unfold x; nra).
  assert (XL:(3#2)*alpha<=x*zeros high) by nra.
  assert (XR:x*(zeros high+1)<=(5#2)*alpha) by nra.
  rewrite Eq, zeros_app; unfold x in *; split; nra.
Qed.

Definition anchor_entry_check q av high lim orig :=
  match tail_cut orig with
  | None => false
  | Some(u,tail) => match strip_words [W1] (rev_append tail []) with
    | None => false
    | Some rd => let da:=rev_append rd [] in
      match strip_words (repeat WT q++av) u, heightN u 0 with
      | Some rest, Some H =>
        if Nat.leb 67 H then if Nat.eqb H (length da) then
          let '(carry,eff):=effectiveN u 0%N [] in
          let '(last,db):=effectiveN da carry [] in
          if N.eqb last 1 then
            match strip_words (repeat W1 15) db,
              strip_words (rev high) (rev_append db []) with
            | Some _, Some _ =>
              N.leb (rounded (2^16)%N (2^16)%N (rev_append rest []) 0%N) lim
            | _, _ => false end
          else false
        else false else false
      | _, _ => false end
    end
  end.

Definition AnchorEntry q av high lim :=
  let pre:=repeat WT q++av in let alpha:=mass pre in
  (5<=q)%nat /\ scale (repeat WT 32)*(1#2)<=alpha /\ alpha<=scale (repeat WT 32) /\
  (3#2)*alpha*scale high<=zeros high /\ zeros high+1<=(5#2)*alpha*scale high /\
  scale pre*qN lim<=alpha*63.

Lemma dyadic_interval p alpha : scale (repeat WT p)*(1#2)<=alpha ->
  alpha<=scale (repeat WT p) ->
  (1#2)<=alpha*qnat (2^p)%nat /\ alpha*qnat (2^p)%nat<=1.
Proof.
  intros L R; pose proof (proj2 (repeat_T_weights p)); pose proof (qpow_pos p); split; nra.
Qed.

Lemma anchor_entry_check_spec q av high lim orig : AnchorEntry q av high lim ->
  anchor_entry_check q av high lim orig=true -> AnchorGood av 32 q orig.
Proof.
  intros [Q [AlphaLow [AlphaHigh [Dlow [Dhigh MassLimit]]]]].
  unfold anchor_entry_check; destruct (tail_cut orig) as [[u tail]|] eqn:C; [|discriminate].
  destruct (strip_words [W1] (rev_append tail [])) as [rd|] eqn:Top; [|discriminate].
  destruct (strip_words (repeat WT q++av) u) as [rest|] eqn:Start; [|discriminate].
  destruct (heightN u 0) as [H|] eqn:Height; [|discriminate].
  destruct (Nat.leb 67 H) eqn:Hbound; [apply Nat.leb_le in Hbound|discriminate].
  destruct (Nat.eqb H (length (rev_append rd []))) eqn:Width;
    [apply Nat.eqb_eq in Width|discriminate].
  destruct (effectiveN u 0 []) as [carry eff] eqn:E.
  destruct (effectiveN (rev_append rd []) carry []) as [last db] eqn:F.
  destruct (N.eqb last 1) eqn:Last; [apply N.eqb_eq in Last; subst last|discriminate].
  destruct (strip_words (repeat W1 15) db) as [lo|] eqn:Low; [|discriminate].
  destruct (strip_words (rev high) (rev_append db [])) as [hi|] eqn:High; [|discriminate].
  intro Mass; apply N.leb_le, qN_le in Mass.
  pose proof (rounded_forward (2^16)%N (2^16)%N rest 0%N) as R.
  change (qN (2^16)%N) with 65536 in R; change (qN 0%N) with 0 in R.
  pose proof (mass_split rest); pose proof (scale_pos (repeat WT q++av)).
  assert (MassBound:scale (repeat WT q++av)*mass rest<=mass (repeat WT q++av)*(63#65536)).
  { assert (65536*mass rest<=qN lim) by lra; nra. }
  destruct (tail_cut_spec _ _ _ C) as [Orig Dig].
  pose proof (tail_cut_end _ _ _ C) as End.
  apply reverse_prefix in Top; cbn[rev] in Top.
  assert (Tail:tail=rev_append rd []++[W1]) by
    (rewrite Top, !rev_append_rev, app_nil_r; reflexivity).
  rewrite Tail, forallb_app in Dig; apply andb_true_iff in Dig; destruct Dig as [Dig _].
  destruct (digit_list _ Dig) as [A DA]; rewrite <-Width in DA.
  destruct (effectiveN_spec _ _ _ _ _ E) as [v [V Eff]]; cbn[rev_append] in V; subst v.
  destruct (effectiveN_spec _ _ _ _ _ F) as [v [V EffD]]; cbn[rev_append] in V; subst v.
  destruct (Effective_digits _ _ _ _ EffD _ _ DA) as [B [DB Sum]].
  apply strip_words_spec in Start.
  apply heightN_spec in Height; change (qnat (2^0)%nat) with 1 in Height.
  assert (High':exists x, db=x++high).
  { apply reverse_prefix in High; rewrite rev_involutive, rev_append_rev in High; eauto. }
  destruct (anchor_entry_tail_bounds _ _ _ _ _ _ DB Height High' Dlow Dhigh) as [Dlo Dhi].
  destruct (dyadic_interval _ _ AlphaLow AlphaHigh) as [ApLow ApHigh].
  rewrite Orig, Tail.
  eapply (AnchorGood_intro av 32 q H u A (rev_append rd []) (N.to_nat carry) eff B db
    (1#65536) (mass (repeat WT q++av))).
  - apply Nat.le_refl.
  - apply Q.
  - apply Hbound.
  - exists rest; apply Start.
  - apply End.
  - reflexivity.
  - apply ApLow.
  - apply ApHigh.
  - apply Height.
  - apply DA.
  - apply Eff.
  - clear -Sum; change (A+N.to_nat carry=B+1*2^H)%nat in Sum; lia.
  - apply DB.
  - apply Reserve_even with (n:=16%nat); vm_compute; reflexivity.
  - clear -Start MassBound; rewrite Start, mass_app; lra.
  - apply Dlo.
  - apply Dhi.
  - exists lo; apply strip_words_spec, Low.
Qed.

Local Open Scope nat_scope.
Fixpoint anchor_verify n q av high lim u :=
  match n with
  | O => anchor_entry_check q av high lim u
  | S n => match roundN u with None => false | Some v => anchor_verify n q av high lim v end
  end.

Lemma anchor_verify_spec n q av high lim : AnchorEntry q av high lim ->
  forall u, anchor_verify n q av high lim u=true ->
    exists v, Rounds u v /\ AnchorGood av 32 q v.
Proof.
  intro Entry; induction n as [|n IH]; intros u E.
  - exists u; split; [constructor|eapply anchor_entry_check_spec; eauto].
  - change ((match roundN u with Some v => anchor_verify n q av high lim v | None => false end)=true) in E.
    destruct (roundN u) as [v|] eqn:V; [|discriminate].
    destruct (IH _ E) as [w [R G]]; exists w; split; [eapply Rounds_next|]; eauto using roundN_spec.
Qed.

Definition high11 := [W0;W1;W0;W1;W1;W1;W1;W1;W0]++repeat W1 31.
Definition high12 := [W1;W1;W1;W1;W0;W1;W0;W1;W0]++repeat W1 31.
Definition high49 := [W0;W1;W1;W1;W0;W0;W1;W1;W0]++repeat W1 31.
Lemma anchor_entry11 : AnchorEntry 34 anchor11 high11 11000%N.
Proof. vm_compute; repeat split; try discriminate; lia. Qed.
Lemma anchor_entry12 : AnchorEntry 35 anchor12 high12 4000%N.
Proof. vm_compute; repeat split; try discriminate; lia. Qed.
Lemma anchor_entry49 : AnchorEntry 35 anchor49 high49 12000%N.
Proof. vm_compute; repeat split; try discriminate; lia. Qed.

(* One complete cycle after the early 11/50 start. The final W0 is blank
   padding: it lets the virtual carry exit at 1 without changing the tape. *)
Definition start11 := [WT;WT;W1;WT;W1;WT;W0;W0;WT;W1;W0].
Definition start12 := repeat WT 4++[W1;W1]++repeat WT 4++[W1;WT]++repeat W1 5++[W0;W1].
Definition start49 := repeat WT 4++[W1;WT;WT;W1;W1;WT;W0;WT;W1;W0;W0;W1;W1].

Lemma anchor_check11 : anchor_verify 32 34 anchor11 high11 11000%N start11=true.
Proof. vm_compute; reflexivity. Qed.
Lemma anchor_check12 : anchor_verify 31 35 anchor12 high12 4000%N start12=true.
Proof. vm_compute; reflexivity. Qed.
Lemma anchor_check49 : anchor_verify 31 35 anchor49 high49 12000%N start49=true.
Proof. vm_compute; reflexivity. Qed.

Lemma anchor_entry_nonhalt tm C av ev n q high lim u :
  short_only ev=true ->
  (forall q, 5<=q -> Copies (repeat WT q++av) (repeat WT q++ev)) ->
  AnchorEntry q av high lim ->
  (forall orig out, Step orig out -> C orig -[tm]->+ C out) ->
  c0 -[tm]->* C u -> anchor_verify n q av high lim u=true -> ~halts tm c0.
Proof.
  intros Safe Stable Entry BS Init Check.
  destruct (anchor_verify_spec _ _ _ _ _ Entry _ Check) as [v [R G]].
  eapply multistep_nonhalt; [apply Init|].
  assert (Run:C u -[tm]->* C v).
  { clear -BS R; induction R;
      [constructor|eapply evstep_trans; [apply progress_evstep, BS, H|apply IHR]]. }
  eapply multistep_nonhalt; [apply Run|].
  eapply progress_nonhalt_cond with (P:=fun w=>exists p q, AnchorGood av p q w).
  - intros w [p [q' Good]].
    destruct (AnchorGood_next _ _ Safe Stable _ _ _ Good) as [out [S Good']].
    exists out; split; [apply BS, S|eauto].
  - eauto.
Qed.

(* C8 after an initial # is conjugate to C12 after removing the auxiliary
   highest digit. No signal calls are commuted in this correspondence. *)
Section Lowering.
Local Open Scope Q_scope.
Ltac lower_qnorm :=
  repeat (rewrite qnat_add in * || rewrite qnat_mul in * || rewrite qnat_S in *);
  change (qnat 0%nat) with 0 in *; change (qnat 1%nat) with 1 in *;
  change (qnat 2%nat) with 2 in *; change (qnat 4%nat) with 4 in *.

Lemma heightN_mass u : forall h, mass u<qnat (2^h)%nat ->
  exists H, heightN u h=Some H.
Proof.
  induction u as [|w u IH]; intros h M; [eexists; reflexivity|].
  destruct w; cbn[mass heightN] in *.
  - apply IH; rewrite Nat.pow_succ_r', qnat_mul; change (qnat 2%nat) with 2; lra.
  - destruct h; [pose proof (weights_nonneg u); change (qnat (2^0)%nat) with 1 in M; lra|].
    apply IH; rewrite Nat.pow_succ_r', qnat_mul in M; change (qnat 2%nat) with 2 in M; lra.
  - destruct h; [pose proof (weights_nonneg u); change (qnat (2^0)%nat) with 1 in M; lra|].
    apply IH; rewrite Nat.pow_succ_r', qnat_mul in M; change (qnat 2%nat) with 2 in M; lra.
Qed.

Lemma tail_cut_rev_prefix ds : forall r tail, forallb is_digit ds=true ->
  tail_cut_rev (ds++WT::r) tail=Some(rev_append r [WT],rev_append ds tail).
Proof.
  induction ds as [|w ds IH]; intros r tail D; [reflexivity|].
  destruct w; cbn[forallb is_digit] in D; [discriminate|apply IH,D|apply IH,D].
Qed.

Lemma tail_cut_app u ds : (exists v,u=v++[WT]) -> forallb is_digit ds=true ->
  tail_cut (u++ds)=Some(u,ds).
Proof.
  intros [v ->] D; unfold tail_cut; rewrite rev_append_rev, app_nil_r, !rev_app_distr.
  cbn[rev app]; rewrite tail_cut_rev_prefix.
  - rewrite !rev_append_rev, !rev_involutive, app_nil_r; reflexivity.
  - rewrite forallb_forall in *; intros w W; rewrite <-in_rev in W; apply D,W.
Qed.

Lemma Digits_width A H da : Digits A H da -> length da=H.
Proof. intro D; induction D; cbn[length]; lia. Qed.

Lemma AnchorGood_tail av p q u A H da :
  (exists v,u=v++[WT]) -> Digits A H da -> AnchorGood av p q (u++da++[W1]) ->
  mass u<(1#128) /\ scale u*qnat (2^H)%nat==1.
Proof.
  intros End DA G; remember (u++da++[W1]) as orig eqn:Orig in G.
  destruct G as [pp qq HH uu AA dd carry eff B db tau alpha P Q Hb Start Last
    Mass ApLow ApHigh Height DD Eff Sum DB Res M Dlo Dhi Low].
  assert (Cut:tail_cut (uu++(dd++[W1]))=Some(uu,dd++[W1])) by
    (apply tail_cut_app; [apply Last|rewrite forallb_app, (Digits_only _ _ _ DD); reflexivity]).
  rewrite Orig in Cut; rewrite tail_cut_app in Cut;
    [|apply End|rewrite forallb_app, (Digits_only _ _ _ DA); reflexivity].
  inversion Cut; subst uu.
  assert (dd=da) by (apply app_inv_tail with (l:=[W1]); congruence); subst dd.
  pose proof (Digits_width _ _ _ DD) as Width; pose proof (Digits_width _ _ _ DA) as Width'.
  rewrite <-Width, Width' in Height; split; [|apply Height].
  pose proof (proj2 (repeat_T_weights pp)) as DP; pose proof (qpow_pos pp) as Pow.
  pose proof (alpha_small _ P) as Small.
  pose proof (Reserve_small _ _ Res P) as [Tau _].
  assert (alpha<=scale (repeat WT pp)) by (clear -DP Pow ApHigh; nra).
  pose proof (scale_pos (repeat WT pp)); nra.
Qed.

Lemma heightN_small u H : mass u<1 -> scale u*qnat (2^H)%nat==1 ->
  heightN u 0=Some H.
Proof.
  intros M Height; destruct (heightN_mass u 0 M) as [J E].
  pose proof (heightN_spec _ _ _ E); pose proof (scale_pos u).
  change (qnat (2^0)%nat) with 1 in H0.
  assert ((2^J=2^H)%nat) by (apply Nat.le_antisymm; apply qnat_le; nra).
  assert (J=H) by (apply Nat.pow_inj_r in H2; lia).
  subst J; apply E.
Qed.

Lemma Effective_shift n u b v : Effective n u b v -> forall h H,
  heightN u h=Some H -> Effective (n+2^h)%nat u (b+2^H)%nat v.
Proof.
  intro I; induction I; intros h H E; cbn[heightN] in E.
  - inversion E; constructor.
  - specialize (IHI (S h) H E); rewrite Nat.pow_succ_r' in IHI.
    applys_eq (Effective_T (n+2^h)%nat); flia; applys_eq IHI; flia.
  - destruct h; [discriminate|]; specialize (IHI h H E); rewrite Nat.pow_succ_r'.
    applys_eq (Effective_00 (n+2^h)%nat); flia; apply IHI.
  - destruct h; [discriminate|]; specialize (IHI h H E); rewrite Nat.pow_succ_r'.
    applys_eq (Effective_01 (n+2^h)%nat); flia; apply IHI.
  - destruct h; [discriminate|]; specialize (IHI h H E); rewrite Nat.pow_succ_r'.
    applys_eq (Effective_10 (n+2^h)%nat); flia; apply IHI.
  - destruct h; [discriminate|]; specialize (IHI h H E); rewrite Nat.pow_succ_r'.
    applys_eq (Effective_11 (n+2^h)%nat); flia; applys_eq IHI; flia.
Qed.

Lemma Effective_compensate_two n ds A H B : Digits A H ds ->
  (A+n=B+2^H)%nat -> (B<2^H)%nat -> exists v, Digits B H v /\
    Effective (n+2^H)%nat (ds++[W0]) 1 (v++[W0]).
Proof.
  intros D Sum Bound; destruct (Effective_ex ds (n+2^H)%nat) as [b [v E]].
  destruct (Effective_digits _ _ _ _ E _ _ D) as [C [V Eq]].
  pose proof (Digits_bound _ _ _ V).
  assert (b=2)%nat by (destruct b as [|[|[|b]]]; cbn[Nat.mul] in Eq; nia).
  subst b; assert (C=B) by nia; subst C.
  exists v; split; [apply V|].
  eapply Effective_app; [apply E|apply (Effective_00 1); constructor].
Qed.

Lemma Scan_output_loss k u k' v a b : Scan k u k' v a b -> a<=4*mass v.
Proof. intro I; induction I; cbn[mass]; lra. Qed.

Lemma Scan_lower k u k' v a b : Scan k u k' v a b -> forall h m,
  (k=m+4*2^h)%nat -> mass v<qnat (2^h)%nat -> 8*mass v<qnat m-4 ->
  exists H m', heightN v h=Some H /\ (k'=m'+4*2^H)%nat /\ Scan m u m' v a b.
Proof.
  intro I; induction I; intros h m Eq M Bound.
  { exists h,m; repeat split; auto using Scan_nil. }
  { assert (Pos:(4<m)%nat) by (apply qnat_lt; change (qnat 4%nat) with 4;
      pose proof (weights_nonneg (WT::v)); lra).
    set (n':=(n-4*2^h)%nat).
    assert (N:(n=4*2^h+n')%nat) by (unfold n'; lia).
    assert (E:(m=3+n')%nat) by lia; subst m.
    destruct (IHI (S h) (2+n'*2)%nat) as [H [m' [Ht [K S]]]].
    + rewrite Nat.pow_succ_r'; lia.
    + cbn[mass] in M; rewrite Nat.pow_succ_r', qnat_mul; change (qnat 2%nat) with 2; lra.
    + cbn[mass] in Bound; lower_qnorm; change (qnat 3%nat) with 3 in Bound; lra.
    + exists H,m'; split; [apply Ht|split; [apply K|apply Scan_T,S]]. }
  { assert (Pos:(4<m)%nat) by (apply qnat_lt; change (qnat 4%nat) with 4;
      pose proof (weights_nonneg (WT::v)); lra).
    set (n':=(n-4*2^h)%nat).
    assert (N:(n=4*2^h+n')%nat) by (unfold n'; lia).
    assert (E:(m=1+n')%nat) by lia; subst m.
    destruct (IHI (S h) (n'*2)%nat) as [H [m' [Ht [K S]]]].
    + rewrite Nat.pow_succ_r'; lia.
    + cbn[mass] in M; rewrite Nat.pow_succ_r', qnat_mul; change (qnat 2%nat) with 2; lra.
    + cbn[mass] in Bound; lower_qnorm; lra.
    + exists H,m'; split; [apply Ht|split; [apply K|apply Scan_pair0,S]]. }
  { assert (Pos:(4<m)%nat) by (apply qnat_lt; change (qnat 4%nat) with 4;
      pose proof (weights_nonneg (WT::v)); lra).
    set (n':=(n-4*2^h)%nat).
    assert (N:(n=4*2^h+n')%nat) by (unfold n'; lia).
    assert (E:(m=1+n')%nat) by lia; subst m.
    destruct (IHI (S h) (1+n'*2)%nat) as [H [m' [Ht [K S]]]].
    + rewrite Nat.pow_succ_r'; lia.
    + cbn[mass] in M; rewrite Nat.pow_succ_r', qnat_mul; change (qnat 2%nat) with 2; lra.
    + cbn[mass] in Bound; lower_qnorm; lra.
    + exists H,m'; split; [apply Ht|split; [apply K|apply Scan_pair1,S]]. }
  all: destruct h; [cbn[mass] in M; change (qnat (2^0)%nat) with 1 in M;
    pose proof (weights_nonneg v); lra|].
  all: assert (Pos:(4<m)%nat) by (apply qnat_lt; change (qnat 4%nat) with 4;
    cbn[mass] in Bound; pose proof (weights_nonneg v); lra).
  all: rewrite Nat.pow_succ_r' in Eq.
  all: set (n':=(n-2*2^h)%nat).
  all: assert (N:(n=2*2^h+n')%nat) by (unfold n'; lia).
  - assert (E:(m=2+n'*4)%nat) by lia; subst m.
    destruct (IHI h (n'*2)%nat) as [H [m' [Ht [K S]]]].
    + lia.
    + cbn[mass] in M; rewrite Nat.pow_succ_r', qnat_mul in M; change (qnat 2%nat) with 2 in M; lra.
    + cbn[mass] in Bound; lower_qnorm; lra.
    + exists H,m'; split; [apply Ht|split; [apply K|apply Scan_short00,S]].
  - assert (E:(m=2+n'*4)%nat) by lia; subst m.
    destruct (IHI h (1+n'*2)%nat) as [H [m' [Ht [K S]]]].
    + lia.
    + cbn[mass] in M; rewrite Nat.pow_succ_r', qnat_mul in M; change (qnat 2%nat) with 2 in M; lra.
    + cbn[mass] in Bound; lower_qnorm; lra.
    + exists H,m'; split; [apply Ht|split; [apply K|apply Scan_short01,S]].
  - assert (E:(m=4+n'*4)%nat) by lia; subst m.
    destruct (IHI h (n'*2)%nat) as [H [m' [Ht [K S]]]].
    + lia.
    + cbn[mass] in M; rewrite Nat.pow_succ_r', qnat_mul in M; change (qnat 2%nat) with 2 in M; lra.
    + cbn[mass] in Bound; lower_qnorm; lra.
    + exists H,m'; split; [apply Ht|split; [apply K|apply Scan_short10,S]].
  - assert (E:(m=4+n'*4)%nat) by lia; subst m.
    destruct (IHI h (1+n'*2)%nat) as [H [m' [Ht [K S]]]].
    + lia.
    + cbn[mass] in M; rewrite Nat.pow_succ_r', qnat_mul in M; change (qnat 2%nat) with 2 in M; lra.
    + cbn[mass] in Bound; lower_qnorm; lra.
    + exists H,m'; split; [apply Ht|split; [apply K|apply Scan_short11,S]].
Qed.

Lemma Effective_unique n u b v : Effective n u b v -> forall c w,
  Effective n u c w -> b=c /\ v=w.
Proof.
  intro I; induction I; intros c w J; inversion J; subst; try lia.
  { auto. }
  all: try match goal with E:(?x*2 = ?y*2)%nat |- _ =>
    assert (x=y) by lia; subst end.
  all: try match goal with E:(1+?x*2 = 1+?y*2)%nat |- _ =>
    assert (x=y) by lia; subst end.
  all: match goal with E:Effective _ _ _ _ |- _ =>
    destruct (IHI _ _ E) as [-> ->]; split; reflexivity end.
Qed.

Inductive LowerStep : list Word -> list Word -> Prop :=
| LowerStep_intro orig padding eff k v a b J da :
    Effective 1 (orig++repeat W0 padding) 1 eff -> Scan 8 eff k v a b ->
    (0<k)%nat -> Digits k J da ->
    LowerStep orig (WT::(v++WT::da)).

Lemma Scan_end_output k u k' v a b : Scan k u k' v a b ->
  8*mass v<qnat k-4 -> (4<k')%nat.
Proof.
  intros S Bound; pose proof (Scan_output_loss _ _ _ _ _ _ S).
  pose proof (Scan_budget _ _ _ _ _ _ S); pose proof (Scan_bounds _ _ _ _ _ _ S).
  pose proof (scale_pos v); apply qnat_lt; change (qnat 4%nat) with 4; nra.
Qed.

Lemma AnchorGood_lower_next av ev : short_only ev=true ->
  (forall q, (5<=q)%nat -> Copies (repeat WT q++av) (repeat WT q++ev)) ->
  forall p q w, AnchorGood av p q (w++[W1]) ->
  exists out, LowerStep w out /\ AnchorGood av (1+p)%nat (1+q)%nat (out++[W1]).
Proof.
  intros Safe Stable p q w G.
  destruct (AnchorGood_next _ _ Safe Stable _ _ _ G) as [out [S G']].
  remember (w++[W1]) as whole eqn:Whole in G,S.
  destruct S as [orig eff k v a b J A da E S DA Sum].
  set (new:=WT::(v++[WT])).
  assert (Out:WT::(v++WT::(da++[W1]))=new++da++[W1]) by
    (unfold new; cbn[app]; rewrite <-app_assoc; reflexivity).
  rewrite Out in G'.
  destruct (AnchorGood_tail _ _ _ _ _ _ _ (ex_intro _ (WT::v) eq_refl) DA G') as [M Height].
  change (scale new*qnat (2^J)%nat==1) in Height.
  assert (Mv:mass v<(1#64)).
  { unfold new in M; cbn[mass] in M; rewrite mass_app in M; cbn[mass] in M; lra. }
  destruct (Scan_lower _ _ _ _ _ _ S 0 8 eq_refl ltac:(change (mass v<1); lra)
    ltac:(change (8*mass v<4); lra)) as [Hv [k' [VH [KS SS]]]].
  pose proof (heightN_spec _ _ _ VH) as VHeight.
  change (qnat (2^0)%nat) with 1 in VHeight.
  assert (Scale:scale new==scale v*(1#4)).
  { unfold new; cbn[scale]; rewrite scale_app; cbn[scale]; ring. }
  assert (Power:(2^J=4*2^Hv)%nat).
  { apply Nat.le_antisymm; apply qnat_le; rewrite qnat_mul;
      change (qnat 4%nat) with 4; pose proof (scale_pos v); rewrite Scale in Height; nra. }
  assert (KA:k'=A) by lia; subst k'.
  destruct G as [pp qq H u B ds carry effective C db tau alpha P Q Hb Start End
    Mass ApLow ApHigh Height0 DD Eff Sum0 DB Res M0 Dlo Dhi Low].
  assert (W:w=u++ds) by (apply app_inv_tail with (l:=[W1]); rewrite <-app_assoc; symmetry; apply Whole).
  subst w.
  assert (G0:AnchorGood av pp qq (u++ds++[W1])).
  { econstructor; eauto. }
  destruct (AnchorGood_tail _ _ _ _ _ _ _ End DD G0) as [Mu _].
  assert (UH:heightN u 0=Some H) by (apply heightN_small; [lra|apply Height0]).
  pose proof (Effective_shift _ _ _ _ Eff _ _ UH) as Eff1.
  change (Effective 1 u (carry+2^H)%nat effective) in Eff1.
  destruct (Effective_compensate _ _ _ _ _ DD Sum0 (Digits_bound _ _ _ DB)) as [d [D EE]].
  assert (d=db) by (eapply Digits_unique; eauto); subst d.
  pose proof (Effective_app _ _ _ _ Eff _ _ _ EE) as E0.
  assert (Eeq:eff=effective++db++[W0]).
  { destruct (Effective_unique _ _ _ _ E _ _ E0); assumption. }
  destruct (Effective_compensate_two _ _ _ _ _ DD Sum0 (Digits_bound _ _ _ DB)) as [d [D' EE1]].
  assert (d=db) by (eapply Digits_unique; eauto); subst d.
  exists (new++da); split.
  - unfold new; cbn[app]; rewrite <-app_assoc; cbn[app].
    apply (LowerStep_intro (u++ds) 1 eff A v a b J da); [|apply SS| |apply DA].
    2: { pose proof (Scan_end_output _ _ _ _ _ _ SS ltac:(change (8*mass v<4); lra)); lia. }
    change (Effective 1 ((u++ds)++[W0]) 1 eff).
    rewrite <-app_assoc,Eeq; eapply Effective_app; eauto.
  - rewrite <-app_assoc; apply G'.
Qed.

Lemma Digits_zero_side A H da : Digits A H da -> A=0%nat -> to_side da 0inf=0inf.
Proof.
  intro D; induction D; intro Z; cbn[to_side]; [reflexivity| |lia].
  rewrite IHD by lia; change (S0>>S0>>0inf=0inf); repeat rewrite <-const_unfold; reflexivity.
Qed.

Lemma Digits_RIncs A H da : Digits A H da -> (0<A)%nat ->
  RIncs ((A-1)*2)%nat 0inf (to_side da 0inf).
Proof.
  intro D; induction D; intro Pos; [lia| |].
  - cbn[to_side]; do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (RIncs_short00 (A-1)); flia; apply IHD; lia.
  - destruct A as [|A].
    + cbn[to_side Nat.sub Nat.mul]; rewrite (Digits_zero_side _ _ _ D eq_refl).
      change (RIncs 0 0inf (S1>>S0>>0inf)); rewrite <-const_unfold; constructor.
    + cbn[to_side]; do 2 rewrite (const_unfold _ S0) at 1.
      applys_eq (RIncs_short10 A); flia; applys_eq IHD; flia.
Qed.
End Lowering.

Local Open Scope nat_scope.
Definition lower_scan eff :=
  match scanN eff 8%N [] with
  | Some(Npos k,v) => Some(WT::(v++WT::pwords k))
  | _ => None end.

Definition lower_round u :=
  let '(carry,eff):=effectiveN (u++[W0]) 1%N [] in
  match carry with
  | Npos xH => lower_scan eff
  | Npos (xO xH) => lower_scan (eff++[W0])
  | _ => None end.

Lemma pwords_Digits k : exists J, Digits (Pos.to_nat k) J (pwords k).
Proof.
  destruct (pwords_digits k) as [A [H [da [E [D Sum]]]]]; rewrite E, <-Sum.
  exists (H+1); applys_eq (Digits_app _ _ _ D _ _ _ (Digits_one 0 0 _ Digits_nil)); flia.
Qed.

Lemma lower_scan_spec u padding eff out :
  Effective 1 (u++repeat W0 padding) 1 eff -> lower_scan eff=Some out -> LowerStep u out.
Proof.
  intros E; unfold lower_scan; destruct (scanN eff 8 []) as [[k v]|] eqn:S; [|discriminate].
  destruct k as [|k]; [discriminate|]; intro O; inversion O; subst out.
  destruct (scanN_spec _ _ _ _ _ S) as [w [a [b [V I]]]]; cbn[rev_append] in V; subst w.
  destruct (pwords_Digits k) as [J D].
  eapply LowerStep_intro; [apply E|apply I|apply Pos2Nat.is_pos|apply D].
Qed.

Lemma lower_round_spec u out : lower_round u=Some out -> LowerStep u out.
Proof.
  unfold lower_round; destruct (effectiveN (u++[W0]) 1 []) as [carry eff] eqn:E.
  destruct (effectiveN_spec _ _ _ _ _ E) as [v [V I]]; cbn[rev_append] in V; subst v.
  destruct carry as [|[p|p|]]; try discriminate.
  - destruct p as [p|p|]; try discriminate; intro S.
    eapply lower_scan_spec with (padding:=2); [|apply S].
    change (Effective 1 (u++repeat W0 2) 1 (eff++[W0])).
    change (repeat W0 2) with ([W0]++[W0]); rewrite app_assoc.
    eapply Effective_app; [apply I|apply (Effective_00 1); constructor].
  - intro S; eapply lower_scan_spec with (padding:=1); eauto.
Qed.

Inductive LowerRounds : list Word -> list Word -> Prop :=
| LowerRounds_refl u : LowerRounds u u
| LowerRounds_next u v w : LowerStep u v -> LowerRounds v w -> LowerRounds u w.

Fixpoint lower_verify n q av high lim u :=
  match n with
  | O => anchor_entry_check q av high lim (u++[W1])
  | S n => match lower_round u with None => false | Some v => lower_verify n q av high lim v end
  end.

Lemma lower_verify_spec n q av high lim : AnchorEntry q av high lim ->
  forall u, lower_verify n q av high lim u=true ->
    exists v, LowerRounds u v /\ AnchorGood av 32 q (v++[W1]).
Proof.
  intro Entry; induction n as [|n IH]; intros u E.
  - exists u; split; [constructor|eapply anchor_entry_check_spec; eauto].
  - change ((match lower_round u with Some v => lower_verify n q av high lim v | None => false end)=true) in E.
    destruct (lower_round u) as [v|] eqn:V; [|discriminate].
    destruct (IH _ E) as [w [R G]]; exists w; split; [eapply LowerRounds_next|]; eauto using lower_round_spec.
Qed.

Definition anchor35 := [W1;WT;W1;W1;W1;WT;WT;WT;W1;WT;WT;WT;W1;WT;WT;WT;W1;WT].
Definition effective35 := [W0;WT;W0;W0;W0;WT;WT;WT;W0;WT;WT;WT;W0;WT;WT;WT;W0;WT].
Definition high35 := [W1;W0;W1;W0;W1;W0;W1;W1;W0]++repeat W1 31.

Lemma anchor35_copies q : 5<=q -> Copies (repeat WT q++anchor35) (repeat WT q++effective35).
Proof. apply copy_lift; apply (copyN_spec _ _ 31 32 260 256); vm_compute; reflexivity. Qed.

Lemma anchor_entry35 : AnchorEntry 36 anchor35 high35 9000%N.
Proof. vm_compute; repeat split; try discriminate; lia. Qed.

Definition start35 := repeat WT 6++[W1;WT]++repeat W1 3++repeat WT 3++[W1]++
  repeat WT 3++[W0]++repeat WT 3++[W1;WT;W0;W0]++repeat W1 4++[W0;W1;W1].

Lemma lower_check35 : lower_verify 30 36 anchor35 high35 9000%N start35=true.
Proof. vm_compute; reflexivity. Qed.

Lemma lower_entry_nonhalt tm C av ev n q high lim u :
  short_only ev=true ->
  (forall q, 5<=q -> Copies (repeat WT q++av) (repeat WT q++ev)) ->
  AnchorEntry q av high lim ->
  (forall orig out, LowerStep orig out -> C orig -[tm]->+ C out) ->
  c0 -[tm]->* C u -> lower_verify n q av high lim u=true -> ~halts tm c0.
Proof.
  intros Safe Stable Entry BS Init Check.
  destruct (lower_verify_spec _ _ _ _ _ Entry _ Check) as [v [R G]].
  eapply multistep_nonhalt; [apply Init|].
  assert (Run:C u -[tm]->* C v).
  { clear -BS R; induction R;
      [constructor|eapply evstep_trans; [apply progress_evstep, BS, H|apply IHR]]. }
  eapply multistep_nonhalt; [apply Run|].
  eapply progress_nonhalt_cond with (P:=fun w=>exists p q, AnchorGood av p q (w++[W1])).
  - intros w [p [q' Good]].
    destruct (AnchorGood_lower_next _ _ Safe Stable _ _ _ Good) as [out [S Good']].
    exists out; split; [apply BS,S|eauto].
  - eauto.
Qed.

Fixpoint word_tape u :=
  match u with
  | [] => []
  | WT::u => t++word_tape u
  | W0::u => d0++word_tape u
  | W1::u => d1++word_tape u
  end.

Lemma word_tape_side u r : word_tape u*>r=to_side u r.
Proof. induction u as [|[] u IH]; cbn[word_tape to_side]; cbn; congruence. Qed.

Lemma word_tape_app u v : word_tape (u++v)=word_tape u++word_tape v.
Proof. induction u as [|[] u IH]; cbn[word_tape app]; rewrite ?IH; apply app_assoc || reflexivity. Qed.

Lemma Effective_cut v : forall n u c w, Effective n u c (v++w) ->
  exists u1 u2 b, u=u1++u2 /\ Effective n u1 b v /\ Effective b u2 c w.
Proof.
  induction v as [|x v IH]; intros n u c w E.
  - exists (@nil Word), u, n; split; [reflexivity|split; [constructor|apply E]].
  - cbn[app] in E; inversion E; subst.
    all: match goal with J:Effective _ _ _ (_++_) |- _ =>
        destruct (IH _ _ _ _ J) as [u1 [u2 [b [-> [L R]]]]]
      end.
    all: eexists (_::u1), u2, b; split; [reflexivity|];
        split; [constructor; apply L|apply R].
Qed.

Lemma Num_ex h j p k : 0<k -> exists hs, @Num h j p k [] hs.
Proof.
  intro K; destruct (mod2 k); subst k.
  - destruct a as [|a]; [lia|].
    eexists; applys_eq (@Num2 h j p a); flia.
  - eexists; constructor.
Qed.

Lemma Num_unique h j p k hs hs' :
  @Num h j p k [] hs -> @Num h j p k [] hs' -> hs=hs'.
Proof.
  intros I J; inversion I; inversion J; subst; try lia;
    f_equal; f_equal; lia.
Qed.

Lemma Scan_positive k u k' v a b : Scan k u k' v a b -> 0<k' -> 0<k.
Proof. intros I K; inversion I; lia. Qed.

Section Soundness.
Variable tm : TM.
Variables h j p : list (DH0*DH0).

Hypothesis H_T : forall n, segRLs tm (h^^n) (h^^(n*2)) t t.
Hypothesis H_00 : forall n, segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Hypothesis H_01 : forall n, segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Hypothesis H_10 : forall n, segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Hypothesis H_11 : forall n, segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Hypothesis H_blank : sideRLs tm h 0inf (d1*>0inf).

Lemma Sharp_spec n r r' : Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof.
  intro I; induction I.
  - constructor.
  - eapply (segRLs_sideRLs_concat (H_T n)); apply IHI.
  - eapply (segRLs_sideRLs_concat (H_00 n)); apply IHI.
  - eapply (segRLs_sideRLs_concat (H_01 n)); apply IHI.
  - eapply (segRLs_sideRLs_concat (H_10 n)); apply IHI.
  - eapply (segRLs_sideRLs_concat (H_11 n)); apply IHI.
  - cbn[lpow]; rewrite app_nil_r; apply H_blank.
Qed.

Lemma Sharp_one_spec r r' : Sharp 1 r r' -> sideRLs tm h r r'.
Proof. intro I; rewrite <-(app_nil_r h); apply (Sharp_spec _ _ _ I). Qed.

Hypothesis T_one : segRLs tm p h t (t++[S0]).
Hypothesis T_two : segRLs tm j h t (t++one).
Hypothesis T_odd : forall n,
  segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Hypothesis T_even : forall n,
  segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Hypothesis Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Hypothesis Pair_01 : forall n,
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Hypothesis Pair_02 : forall n,
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Hypothesis Pair_11 : forall n,
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Hypothesis Pair_12 : forall n,
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Hypothesis Short_00 : segRLs tm j [] d0 (d0++one).
Hypothesis Short_01 : forall n,
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Hypothesis Short_02 : forall n,
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Hypothesis Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Hypothesis Short_11 : forall n,
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Hypothesis Short_12 : forall n,
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.

Lemma Effective_digits_seg n u b v : Effective n u b v -> forall A H,
  Digits A H v -> segRLs tm (h^^n) (h^^b) (word_tape u) (word_tape v).
Proof.
  intro I; induction I; intros A H D; inversion D; subst; cbn[word_tape].
  - apply segRLs_nil.
  - eapply segRLs_concat; [apply H_00|eapply IHI; eassumption].
  - eapply segRLs_concat; [apply H_01|eapply IHI; eassumption].
  - eapply segRLs_concat; [apply H_10|eapply IHI; eassumption].
  - eapply segRLs_concat; [apply H_11|eapply IHI; eassumption].
Qed.

Lemma Num_T n hs hs' : Num h j p (3+n) [] hs -> Num h j p (2+n*2) [] hs' ->
  segRLs tm hs (h++hs') t t.
Proof.
  intros I J; inversion I as [|m|m]; inversion J as [|q|q]; subst; try lia;
    destruct m as [|m]; try lia.
  - applys_eq (T_odd m); flia.
  - applys_eq (T_even m); flia.
Qed.

Lemma Num_pair0 n hs hs' : Num h j p (1+n) [] hs -> Num h j p (n*2) [] hs' ->
  segRLs tm hs hs' (d1++d0) t.
Proof.
  intros I J; inversion I as [|m|m]; inversion J as [|q|q]; subst; try lia.
  - destruct m as [|m]; [lia|]; applys_eq (Pair_01 m); flia.
  - applys_eq (Pair_02 m); flia.
Qed.

Lemma Num_pair1 n hs hs' : Num h j p (1+n) [] hs -> Num h j p (1+n*2) [] hs' ->
  segRLs tm hs hs' (d1++d1) t.
Proof.
  intros I J; inversion I as [|m|m]; inversion J as [|q|q]; subst; try lia.
  - applys_eq (Pair_11 m); flia.
  - applys_eq (Pair_12 m); flia.
Qed.

Lemma Num_short00 n hs hs' : Num h j p (2+n*4) [] hs -> Num h j p (n*2) [] hs' ->
  segRLs tm hs hs' d0 d0.
Proof.
  intros I J; inversion I; inversion J; subst; try lia.
  destruct n as [|n]; [lia|]; applys_eq (Short_01 n); flia.
Qed.

Lemma Num_short01 n hs hs' : Num h j p (2+n*4) [] hs -> Num h j p (1+n*2) [] hs' ->
  segRLs tm hs hs' d1 d0.
Proof.
  intros I J; inversion I; inversion J; subst; try lia.
  applys_eq (Short_02 n); flia.
Qed.

Lemma Num_short10 n hs hs' : Num h j p (4+n*4) [] hs -> Num h j p (n*2) [] hs' ->
  segRLs tm hs hs' d0 d1.
Proof.
  intros I J; inversion I; inversion J; subst; try lia.
  destruct n as [|n]; [lia|]; applys_eq (Short_11 n); flia.
Qed.

Lemma Num_short11 n hs hs' : Num h j p (4+n*4) [] hs -> Num h j p (1+n*2) [] hs' ->
  segRLs tm hs hs' d1 d1.
Proof.
  intros I J; inversion I; inversion J; subst; try lia.
  applys_eq (Short_12 n); flia.
Qed.

Lemma Scan_seg k v k' w a b : Scan k v k' w a b -> forall u n n' hs hs',
  Effective n u n' v -> Num h j p k [] hs -> Num h j p k' [] hs' ->
  segRLs tm (h^^n++hs) (h^^n'++hs') (word_tape u) (word_tape w).
Proof.
  intro I; induction I; intros u0 n0 n1 hs hs' E N N'.
  - inversion E; subst; rewrite (Num_unique _ _ _ _ _ _ N N'); apply segRLs_nil.
  - inversion E; subst.
    destruct (Num_ex h j p (2+n*2)) as [hs0 N0]; [lia|].
    cbn[word_tape]; eapply segRLs_concat; [|eapply IHI; eauto].
    replace (1+n0*2) with (n0*2+1) by lia.
    rewrite lpow_add; cbn[lpow]; rewrite app_nil_r, <-app_assoc.
    apply (segRLs_trans (H_T n0) (Num_T _ _ _ N N0)).
  - change (Effective n0 u0 n1 ([W1;W0]++u)) in E.
    destruct (Effective_cut _ _ _ _ _ E) as [u1 [u2 [q [-> [L R]]]]].
    assert (Pos:0<n*2) by (eapply Scan_positive; [apply I|inversion N'; lia]).
    destruct (Num_ex h j p _ Pos) as [hs0 N0].
    rewrite word_tape_app; cbn[word_tape]; eapply segRLs_concat; [|eapply IHI; eauto].
    eapply segRLs_trans; [eapply Effective_digits_seg; [apply L|] |apply (Num_pair0 _ _ _ N N0)].
    exact (Digits_one 0 1 _ (Digits_zero 0 0 _ Digits_nil)).
  - change (Effective n0 u0 n1 ([W1;W1]++u)) in E.
    destruct (Effective_cut _ _ _ _ _ E) as [u1 [u2 [q [-> [L R]]]]].
    destruct (Num_ex h j p (1+n*2)) as [hs0 N0]; [lia|].
    rewrite word_tape_app; cbn[word_tape]; eapply segRLs_concat; [|eapply IHI; eauto].
    eapply segRLs_trans; [eapply Effective_digits_seg; [apply L|] |apply (Num_pair1 _ _ _ N N0)].
    exact (Digits_one 1 1 _ (Digits_one 0 0 _ Digits_nil)).
  - change (Effective n0 u0 n1 ([W0]++u)) in E.
    destruct (Effective_cut _ _ _ _ _ E) as [u1 [u2 [q [-> [L R]]]]].
    assert (Pos:0<n*2) by (eapply Scan_positive; [apply I|inversion N'; lia]).
    destruct (Num_ex h j p _ Pos) as [hs0 N0].
    rewrite word_tape_app; cbn[word_tape]; eapply segRLs_concat; [|eapply IHI; eauto].
    eapply segRLs_trans; [eapply Effective_digits_seg; [apply L|] |apply (Num_short00 _ _ _ N N0)].
    exact (Digits_zero 0 0 _ Digits_nil).
  - change (Effective n0 u0 n1 ([W1]++u)) in E.
    destruct (Effective_cut _ _ _ _ _ E) as [u1 [u2 [q [-> [L R]]]]].
    destruct (Num_ex h j p (1+n*2)) as [hs0 N0]; [lia|].
    rewrite word_tape_app; cbn[word_tape]; eapply segRLs_concat; [|eapply IHI; eauto].
    eapply segRLs_trans; [eapply Effective_digits_seg; [apply L|] |apply (Num_short01 _ _ _ N N0)].
    exact (Digits_one 0 0 _ Digits_nil).
  - change (Effective n0 u0 n1 ([W0]++u)) in E.
    destruct (Effective_cut _ _ _ _ _ E) as [u1 [u2 [q [-> [L R]]]]].
    assert (Pos:0<n*2) by (eapply Scan_positive; [apply I|inversion N'; lia]).
    destruct (Num_ex h j p _ Pos) as [hs0 N0].
    rewrite word_tape_app; cbn[word_tape]; eapply segRLs_concat; [|eapply IHI; eauto].
    eapply segRLs_trans; [eapply Effective_digits_seg; [apply L|] |apply (Num_short10 _ _ _ N N0)].
    exact (Digits_zero 0 0 _ Digits_nil).
  - change (Effective n0 u0 n1 ([W1]++u)) in E.
    destruct (Effective_cut _ _ _ _ _ E) as [u1 [u2 [q [-> [L R]]]]].
    destruct (Num_ex h j p (1+n*2)) as [hs0 N0]; [lia|].
    rewrite word_tape_app; cbn[word_tape]; eapply segRLs_concat; [|eapply IHI; eauto].
    eapply segRLs_trans; [eapply Effective_digits_seg; [apply L|] |apply (Num_short11 _ _ _ N N0)].
    exact (Digits_one 0 0 _ Digits_nil).
Qed.

Lemma Scan_Counter k v k' w a b : Scan k v k' w a b -> forall u n r s r',
  Effective 0 u n v -> 0<k' ->
  sideRLs tm (h^^n) r s -> Counter tm h j p k' s r' ->
  Counter tm h j p k (to_side u r) (to_side w r').
Proof.
  intros I u n r s r' E K S C w0 hs N.
  assert (w0=[]) by (inversion N; subst; [pose proof (Scan_positive _ _ _ _ _ _ I K); lia|reflexivity|reflexivity]); subst w0.
  destruct (Num_ex h j p _ K) as [hs' N'].
  change (sideRLs tm hs (to_side u r) (to_side w r')).
  rewrite <-!word_tape_side.
  eapply segRLs_sideRLs_concat; [apply (Scan_seg _ _ _ _ _ _ I _ _ _ _ _ E N N')|].
  eapply sideRLs_trans; [apply S|apply (C [] _ N')].
Qed.

Lemma Counter_T n r s r' : Sharp 1 r s -> Counter tm h j p (2+n*2) s r' ->
  Counter tm h j p (3+n) (t*>r) (t*>r').
Proof.
  intros S I w hs N; inversion N as [|m|m]; subst; try lia.
  - destruct m as [|m]; [lia|].
    eapply (segRLs_sideRLs_concat (T_odd m)).
    eapply sideRLs_trans.
    + apply Sharp_one_spec, S.
    + apply (I []); applys_eq (@Num2 h j p (m*2)); flia.
  - destruct m as [|m]; [lia|].
    eapply (segRLs_sideRLs_concat (T_even m)).
    eapply sideRLs_trans.
    + apply Sharp_one_spec, S.
    + apply (I []); applys_eq (@Num2 h j p (1+m*2)); flia.
Qed.

Lemma RIncs_spec k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; induction I;
    eauto using Counter_T, CCore.Counter_pair0, CCore.Counter_pair1,
      CCore.Counter_short00, CCore.Counter_short01, CCore.Counter_short10, CCore.Counter_short11.
  - intros w hs N; inverts N; try lia; constructor.
  - intros w hs N; inversion N; subst; try lia.
    assert (n=0) by lia; subst n; cbn[lpow app]; rewrite app_nil_r.
    eapply (segRLs_sideRLs_concat T_one).
    apply Sharp_one_spec, H.
  - intros w hs N; inversion N; subst; try lia.
    assert (n=0) by lia; subst n; cbn[lpow app]; rewrite app_nil_r.
    eapply (segRLs_sideRLs_concat T_two).
    apply Sharp_one_spec, H.
Qed.

Lemma Packet_spec k b r r' : Packet k b r r' ->
  exists s, sideRLs tm (h^^b) r s /\ Counter tm h j p k s r'.
Proof. intros [s [S I]]; exists s; split; [apply Sharp_spec, S|apply RIncs_spec, I]. Qed.

Lemma Scan_Packet k v k' w a b : Scan k v k' w a b -> forall u n r r',
  Effective 0 u n v -> 0<k' -> Packet k' n r r' ->
  Counter tm h j p k (to_side u r) (to_side w r').
Proof.
  intros I u n r r' E K P; destruct (Packet_spec _ _ _ _ P) as [s [S C]].
  eapply Scan_Counter; eauto.
Qed.

Lemma Scan_return_binary k v k' w a b : Scan k v k' w a b -> forall u H r,
  Effective 0 u 1 v -> Binary k' H r ->
  Counter tm h j p k (to_side u 0inf) (to_side w (t*>r)).
Proof.
  intros I u H r E D; pose proof (Binary_bounds _ _ _ D).
  destruct k' as [|n]; [lia|].
  eapply Scan_Packet; [apply I|apply E|lia|].
  exists (d1*>0inf); split; [apply Sharp_blank|].
  do 2 rewrite (const_unfold _ S0) at 1.
  apply RIncs_pair0; applys_eq (Binary_RIncs _ _ _ D); flia.
Qed.

Lemma Scan_right_return k v k' w a b : Scan k v k' w a b -> forall u,
  Effective 0 u 1 v -> 0<k' -> exists H r, Binary k' H r /\
  Counter tm h j p k (to_side u 0inf) (to_side w (t*>r)).
Proof.
  intros I u E K; destruct k' as [|n]; [lia|].
  destruct (Binary_ex n) as [H [r D]]; exists H, r; split; [apply D|].
  eapply Scan_return_binary; eauto.
Qed.

Lemma C12_return orig u A H ds : Digits A H ds ->
  (scale u*qnat (2^H) == 1)%Q -> cut_ok u=true -> u<>[] ->
  (mass u+scale u*(1+zeros ds)<=(1#128))%Q ->
  Effective 0 orig 1 (u++ds++[W0]) ->
  exists k v a b J r, Scan 12 (u++ds++[W0]) k v a b /\
    4<k /\ Binary k J r /\
    Counter tm h j p 12 (to_side orig 0inf) (to_side v (t*>r)).
Proof.
  intros D Height Cut Ne Bound E.
  destruct (C12_scan _ _ _ _ D Height Cut Ne Bound) as [k [v [a [b [I K]]]]].
  destruct (Scan_right_return _ _ _ _ _ _ I _ E) as [J [r [B C]]]; [lia|].
  exists k, v, a, b, J, r; auto.
Qed.

Lemma Step_sound orig out : Step orig out -> exists r,
  Counter tm h j p 12 (to_side orig 0inf) r /\
    to_side out 0inf=[S1;S1;S0;S0]*>r.
Proof.
  intro I; destruct I as [o eff k v a b J A da E S D Sum].
  assert (B:Binary k (J+1) (to_side da ([S1;S0]*>0inf))).
  { rewrite <-Sum; applys_eq (Digits_prefix_binary _ _ _ D _ _ _ Binary1); flia. }
  eexists; split; [eapply Scan_return_binary; eauto|].
  cbn[to_side]; rewrite to_side_app; cbn[to_side]; rewrite to_side_app; reflexivity.
Qed.

Lemma Good_closed r : Good_side r ->
  exists r', Counter tm h j p 12 r r' /\ Good_side ([S1;S1;S0;S0]*>r').
Proof.
  intros [pp [ws [G ->]]].
  destruct (Good_next _ _ G) as [out [I G']].
  destruct (Step_sound _ _ I) as [r' [R E]].
  exists r'; split; [apply R|exists (1+pp)%nat, out; auto].
Qed.

Lemma Good_nonhalt C :
  (forall r r', Counter tm h j p 12 r r' ->
    C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  forall r, Good_side r -> ~halts tm (C r).
Proof.
  intros BS r G; eapply progress_nonhalt_cond with (P:=Good_side); [|apply G].
  intros s I; destruct (Good_closed _ I) as [s' [R G']].
  exists ([S1;S1;S0;S0]*>s'); split; [apply BS, R|apply G'].
Qed.

Lemma rounds_sound C :
  (forall r r', Counter tm h j p 12 r r' ->
    C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  forall u v, Rounds u v -> C (to_side u 0inf) -[tm]->* C (to_side v 0inf).
Proof.
  intros BS u v I; induction I; [constructor|].
  destruct (Step_sound _ _ H) as [r [R E]].
  eapply evstep_trans; [|apply IHI].
  apply progress_evstep; rewrite E; apply BS, R.
Qed.

Lemma entry_nonhalt C n u :
  (forall r r', Counter tm h j p 12 r r' ->
    C r -[tm]->+ C ([S1;S1;S0;S0]*>r')) ->
  c0 -[tm]->* C (to_side u 0inf) -> verify n u=true -> ~halts tm c0.
Proof.
  intros BS Init Check; destruct (verify_spec _ _ Check) as [v [R G]].
  eapply multistep_nonhalt; [apply Init|].
  eapply multistep_nonhalt; [eapply rounds_sound; eauto|eapply Good_nonhalt; eauto].
Qed.

Lemma LowerStep_sound orig out : LowerStep orig out -> exists r,
  sideRLs tm (h++j++h^^3) (to_side orig 0inf) r /\ to_side out 0inf=t*>r.
Proof.
  intro I; destruct I as [orig padding eff k v a b J da E S K D].
  destruct (Num_ex h j p k K) as [hs N].
  pose proof (Scan_seg _ _ _ _ _ _ S _ _ _ _ _ E (@Num2 h j p 3) N) as Seg.
  change (h^^1) with (h++[]) in Seg; rewrite !app_nil_r in Seg.
  assert (Padding:to_side (repeat W0 padding) 0inf=0inf).
  { clear -padding; induction padding; cbn[to_side repeat]; [reflexivity|rewrite IHpadding;
      change (S0>>S0>>0inf=0inf); repeat rewrite <-const_unfold; reflexivity]. }
  exists (to_side v (t*>to_side da 0inf)); split; [|cbn[to_side]; rewrite to_side_app; reflexivity].
  rewrite <-Padding at 1; rewrite <-to_side_app.
  rewrite <-(word_tape_side (orig++repeat W0 padding) 0inf),
    <-(word_tape_side v (t*>to_side da 0inf)).
  eapply (segRLs_sideRLs_concat Seg).
  eapply sideRLs_trans; [apply H_blank|].
  assert (Inc:RIncs k (d1*>0inf) (t*>to_side da 0inf)).
  { do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (RIncs_pair0 (k-1)); flia; apply Digits_RIncs with (H:=J); assumption. }
  apply (RIncs_spec _ _ _ Inc [] _ N).
Qed.

End Soundness.
End PCore.

Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation h := [(hR,hL)].
Notation j := [((B,[S1;S1]),hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (C,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Lemma init : c0 -->* Config (to_side [WT;WT;W1;WT;WT;WT;WT;W0;W1;W0;W1;W0;W1] 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply PCore.entry_nonhalt with (h:=h) (j:=j) (p:=p)
    (C:=Config) (n:=30) (u:=PCore.start);
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12,
      BigStep, init, PCore.entry_check30.
Qed.

End TM10.

Module TM47.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC0RA_1LD0LA_1LE0LD_1LF0LB_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation h := [(hR,hL)].
Notation j := [((B,[S1;S1]),hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (C,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Lemma init : c0 -->* Config (to_side [WT;WT;W1;WT;WT;WT;WT;W0;W1;W0;W1;W0;W1] 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply PCore.entry_nonhalt with (h:=h) (j:=j) (p:=p)
    (C:=Config) (n:=30) (u:=PCore.start);
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12,
      BigStep, init, PCore.entry_check30.
Qed.

End TM47.

Import PCore.

Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC1RF_1LA1RC_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (A,[S0]).
Notation hR := (E,[S1]).
Notation h := [(hR,hL)].
Notation j := [((C,[S1;S1]),hL)].
Notation p := [((C,[S1;S0]),hL)].
Notation aR := (E,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Lemma init : c0 -->* Config (to_side start11 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply anchor_entry_nonhalt with (C:=fun u=>Config (to_side u 0inf))
    (av:=anchor11) (ev:=effective11) (n:=32) (q:=34)
    (high:=high11) (lim:=11000%N) (u:=start11).
  - vm_compute; reflexivity.
  - apply anchor11_copies.
  - apply anchor_entry11.
  - intros orig out S.
    assert (R:exists r, Counter tm h j p 12 (to_side orig 0inf) r /\
      to_side out 0inf=t*>r).
    { eapply PCore.Step_sound; eauto using H_T, H_00, H_01, H_10, H_11, H_blank,
        T_one, T_two, T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
        Short_00, Short_01, Short_02, Short_10, Short_11, Short_12. }
    destruct R as [r [R ->]]; apply BigStep, R.
  - apply init.
  - apply anchor_check11.
Qed.

End TM11.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0LE_1LD0LC_1RA0LA_1RA1RF_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [(hR,hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (B,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Lemma init : c0 -->* Config (to_side start12 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply anchor_entry_nonhalt with (C:=fun u=>Config (to_side u 0inf))
    (av:=anchor12) (ev:=effective12) (n:=31) (q:=35)
    (high:=high12) (lim:=4000%N) (u:=start12).
  - vm_compute; reflexivity.
  - apply anchor12_copies.
  - apply anchor_entry12.
  - intros orig out S.
    assert (R:exists r, Counter tm h j p 12 (to_side orig 0inf) r /\
      to_side out 0inf=t*>r).
    { eapply PCore.Step_sound; eauto using H_T, H_00, H_01, H_10, H_11, H_blank,
        T_one, T_two, T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
        Short_00, Short_01, Short_02, Short_10, Short_11, Short_12. }
    destruct R as [r [R ->]]; apply BigStep, R.
  - apply init.
  - apply anchor_check12.
Qed.

End TM12.

Module TM49.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1LC0LB_0LD0LF_0RE---_1RF1RE_1RA0RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (B,[S0]).
Notation hR := (A,[S1]).
Notation h := [(hR,hL)].
Notation j := [((F,[S1;S1]),hL)].
Notation p := [((F,[S1;S0]),hL)].
Notation aR := (A,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Lemma init : c0 -->* Config (to_side start49 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply anchor_entry_nonhalt with (C:=fun u=>Config (to_side u 0inf))
    (av:=anchor49) (ev:=effective49) (n:=31) (q:=35)
    (high:=high49) (lim:=12000%N) (u:=start49).
  - vm_compute; reflexivity.
  - apply anchor49_copies.
  - apply anchor_entry49.
  - intros orig out S.
    assert (R:exists r, Counter tm h j p 12 (to_side orig 0inf) r /\
      to_side out 0inf=t*>r).
    { eapply PCore.Step_sound; eauto using H_T, H_00, H_01, H_10, H_11, H_blank,
        T_one, T_two, T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
        Short_00, Short_01, Short_02, Short_10, Short_11, Short_12. }
    destruct R as [r [R ->]]; apply BigStep, R.
  - apply init.
  - apply anchor_check49.
Qed.

End TM49.

Module TM50.
Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC0LE_0RD---_1RE1RD_1RF0RD_1LA0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (A,[S0]).
Notation hR := (F,[S1]).
Notation h := [(hR,hL)].
Notation j := [((E,[S1;S1]),hL)].
Notation p := [((E,[S1;S0]),hL)].
Notation aR := (F,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Lemma init : c0 -->* Config (to_side start11 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply anchor_entry_nonhalt with (C:=fun u=>Config (to_side u 0inf))
    (av:=anchor11) (ev:=effective11) (n:=32) (q:=34)
    (high:=high11) (lim:=11000%N) (u:=start11).
  - vm_compute; reflexivity.
  - apply anchor11_copies.
  - apply anchor_entry11.
  - intros orig out S.
    assert (R:exists r, Counter tm h j p 12 (to_side orig 0inf) r /\
      to_side out 0inf=t*>r).
    { eapply PCore.Step_sound; eauto using H_T, H_00, H_01, H_10, H_11, H_blank,
        T_one, T_two, T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
        Short_00, Short_01, Short_02, Short_10, Short_11, Short_12. }
    destruct R as [r [R ->]]; apply BigStep, R.
  - apply init.
  - apply anchor_check11.
Qed.

End TM50.

Module TM51.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1LD0LC_0LE0LA_0RF---_1RA1RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [(hR,hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (B,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (a++h) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR);(hL,hR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a++h).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Lemma init : c0 -->* Config (to_side start12 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply anchor_entry_nonhalt with (C:=fun u=>Config (to_side u 0inf))
    (av:=anchor12) (ev:=effective12) (n:=31) (q:=35)
    (high:=high12) (lim:=4000%N) (u:=start12).
  - vm_compute; reflexivity.
  - apply anchor12_copies.
  - apply anchor_entry12.
  - intros orig out S.
    assert (R:exists r, Counter tm h j p 12 (to_side orig 0inf) r /\
      to_side out 0inf=t*>r).
    { eapply PCore.Step_sound; eauto using H_T, H_00, H_01, H_10, H_11, H_blank,
        T_one, T_two, T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
        Short_00, Short_01, Short_02, Short_10, Short_11, Short_12. }
    destruct R as [r [R ->]]; apply BigStep, R.
  - apply init.
  - apply anchor_check12.
Qed.

End TM51.

Module TM34.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RA0RE_1RD0RF_1LD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (B,[S0]).
Notation hR := (A,[S1]).
Notation h := [(hR,hL)].
Notation j := [((D,[S1;S1]),hL)].
Notation p := [((D,[S1;S0]),hL)].
Notation aR := (D,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (h++a) (j++h^^5) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,hR);(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (w*>r).

Lemma BigStep r r' : Counter tm h j p 12 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=h++a).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 5).
Qed.

Definition start34 := repeat WT 5++[W1;WT;WT;W1;W1;WT;W0;WT;W0;W0;W0;WT;WT;W0;W0;W0;W1;W1].

Lemma check34 : anchor_verify 30 35 anchor49 high49 12000%N start34=true.
Proof. vm_compute; reflexivity. Qed.

Lemma init : c0 -->* Config (to_side start34 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply anchor_entry_nonhalt with (C:=fun u=>Config (to_side u 0inf))
    (av:=anchor49) (ev:=effective49) (n:=30) (q:=35)
    (high:=high49) (lim:=12000%N) (u:=start34).
  - vm_compute; reflexivity.
  - apply anchor49_copies.
  - apply anchor_entry49.
  - intros orig out S.
    assert (R:exists r, Counter tm h j p 12 (to_side orig 0inf) r /\
      to_side out 0inf=t*>r).
    { eapply PCore.Step_sound; eauto using H_T, H_00, H_01, H_10, H_11, H_blank,
        T_one, T_two, T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
        Short_00, Short_01, Short_02, Short_10, Short_11, Short_12. }
    destruct R as [r [R ->]]; apply BigStep, R.
  - apply init.
  - apply check34.
Qed.

End TM34.

Module TM35.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation h := [(hR,hL)].
Notation j := [((B,[S1;S1]),hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (C,<[S1;S1;S0;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1;S0;S1;S1]).
Notation w := t.

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Sharp_sound n r r' : PCore.Sharp n r r' -> sideRLs tm (h^^n) r r'.
Proof. apply PCore.Sharp_spec; auto using H_T, H_00, H_01, H_10, H_11, H_blank. Qed.

Lemma RIncs_sound k r r' : PCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  apply PCore.RIncs_spec;
    auto using H_T, H_00, H_01, H_10, H_11, H_blank, T_one, T_two, T_odd, T_even,
      Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
      Short_00, Short_01, Short_02, Short_10, Short_11, Short_12.
Qed.

Lemma RSend : segRLs tm (j++a) (h++j++h^^3) t (t++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,(B,[S1;S1]));(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (hL,L) }}} (t*>r).

Lemma BigStep r r' : sideRLs tm (h++j++h^^3) r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=j++a).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend); apply I.
Qed.

Lemma init : c0 -->* Config (to_side start35 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply lower_entry_nonhalt with (C:=fun u=>Config (to_side u 0inf))
    (av:=anchor35) (ev:=effective35) (n:=30) (q:=36)
    (high:=high35) (lim:=9000%N) (u:=start35).
  - vm_compute; reflexivity.
  - apply anchor35_copies.
  - apply anchor_entry35.
  - intros orig out S.
    assert (R:exists r, sideRLs tm (h++j++h^^3) (to_side orig 0inf) r /\
      to_side out 0inf=t*>r).
    { eapply PCore.LowerStep_sound with (p:=p); eauto using H_T, H_00, H_01, H_10, H_11, H_blank,
        T_one, T_two, T_odd, T_even, Pair_00, Pair_01, Pair_02, Pair_11, Pair_12,
        Short_00, Short_01, Short_02, Short_10, Short_11, Short_12. }
    destruct R as [r [R ->]]; apply BigStep,R.
  - apply init.
  - apply lower_check35.
Qed.

End TM35.

(* Exponential-budget family: the virtual prefix changes the accounting
   unit, not the physical right-hand carry. *)
Module ECore.
Local Open Scope Q_scope.

Lemma Scan_gain10 k u k' v a b : Scan k u k' v a b ->
  has10 u=true -> scale v*8<=scale u.
Proof.
  intro I; induction I; intro E.
  - discriminate.
  - cbn[has10 scale] in *; specialize (IHI E); lra.
  - pose proof (Scan_scale _ _ _ _ _ _ I); cbn[scale]; lra.
  - pose proof (Scan_scale _ _ _ _ _ _ I); cbn[scale]; lra.
  - cbn[has10 scale] in *; specialize (IHI E); lra.
  - destruct u as [|w u]; [discriminate|destruct w]; cbn[has10 scale] in *;
      try (specialize (IHI E); lra); inversion I; lia.
  - cbn[has10 scale] in *; specialize (IHI E); lra.
  - destruct u as [|w u]; [discriminate|destruct w]; cbn[has10 scale] in *;
      try (specialize (IHI E); lra); inversion I; lia.
Qed.

(* A joint loss bound avoids introducing a second scan just to record the old
   CCore loss at every non-binary input word. *)
Lemma Scan_energy k u k' v a b : Scan k u k' v a b ->
  a-b-ones v<=3*mass u.
Proof.
  intro I; induction I; cbn[mass ones] in *;
    try match goal with _:Scan _ ?u _ _ _ _ |- _ => pose proof (weights_nonneg u) end; lra.
Qed.

Lemma Scan_digits_energy k u k' v a b : Scan k u k' v a b -> forall A H,
  Digits A H u -> exists l, CCore.Scan k u k' v l /\ a-b-ones v<=2*mass v+l.
Proof.
  intro I; induction I; intros A H D; inversion D; subst.
  1: { exists 0; split; [constructor|cbn[mass ones]; lra]. }
  all: repeat match goal with D:Digits _ _ (_::_) |- _ => inversion D; subst; clear D end.
  all: match goal with D:Digits _ _ _ |- _ =>
    destruct (IHI _ _ D) as [l [J L]] end.
  - exists ((1+l)*(1#2)); split; [apply CCore.Scan_pair0,J|cbn[mass ones]; lra].
  - exists ((1#4)+l*(1#2)); split; [apply CCore.Scan_pair1,J|cbn[mass ones]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short00,J|cbn[mass ones]; lra].
  - exists (l*2); split; [apply CCore.Scan_short01,J|cbn[mass ones]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short10,J|cbn[mass ones]; lra].
  - exists (l*2); split; [apply CCore.Scan_short11,J|cbn[mass ones]; lra].
Qed.

Lemma Scan_tail_energy k u k' v a b z : Scan k u k' v a b -> TailDigits u z ->
  a-b-ones v<=3*(1+2*z).
Proof.
  intros I T; destruct (TailDigits_digits _ _ T) as [A [H D]].
  destruct (Scan_digits_energy _ _ _ _ _ _ I _ _ D) as [l [J L]].
  pose proof (CCore.Scan_tail_bounds _ _ _ _ _ J _ T).
  pose proof (Scan_bounds _ _ _ _ _ _ I); lra.
Qed.

(* No physical call is made on the h virtual T's.  Their sole effect here is
   the unit sigma=2^-h and the initial budget 4*2^h. *)
Lemma exp_scan h u B H ds sigma : Digits B H ds ->
  sigma*qnat (2^h)%nat==1 -> scale u*qnat (2^H)%nat==qnat (2^h)%nat ->
  has10 u=true -> cut_ok u=true -> (u<>[]) ->
  7<=zeros ds ->
  4*sigma*mass u+sigma*scale u*zeros ds+2*sigma<=(1#256) ->
  exists k v a b,
    Scan (4*2^h)%nat (u++ds++[W0]) k v a b /\ (4<k)%nat /\
    sigma*mass v<=sigma*mass u+(15#56)*(sigma*scale u*zeros ds) /\
    sigma*(a-b-ones v)<=3*sigma*mass u+(45#56)*(sigma*scale u*zeros ds).
Proof.
  intros Dig Unit Height Pair Cut Ne Z Phi.
  pose proof (qpow_pos h); pose proof (qpow_pos H).
  assert (S:0<sigma) by nra.
  pose proof (scale_pos u) as Su; pose proof (weights_nonneg u) as Mu.
  pose proof (weights_nonneg ds) as Md.
  assert (Dpos:0<=sigma*scale u*zeros ds) by
    (repeat apply Qmult_le_0_compat; lra).
  assert (Small:4*sigma*mass u+2*sigma<=(1#256)) by lra.
  assert (DefSmall:sigma*scale u*zeros ds<=(1#256)) by nra.
  assert (Bound:8*mass u<qnat ((2*2^h)*2)%nat-4).
  { clear - S Unit Small; rewrite !qnat_mul; change (qnat 2%nat) with 2; nra. }
  destruct (Scan_ex u (2*2^h)%nat Bound) as [m [x [a1 [b1 [I Pos]]]]].
  replace ((2*2^h)*2)%nat with (4*2^h)%nat in I by lia.
  destruct (Scan_even_end _ _ _ _ _ _ I Cut Ne) as [n ->].
  pose proof (Scan_gain10 _ _ _ _ _ _ I Pair) as Gain.
  pose proof (Scan_budget _ _ _ _ _ _ I) as Budget.
  pose proof (Scan_bounds _ _ _ _ _ _ I) as Bounds.
  pose proof (scale_pos x) as Sx.
  rewrite qnat_mul in Budget; change (qnat 4%nat) with 4 in Budget.
  set (s:=sigma*scale x).
  assert (Sp:0<s) by (unfold s; nra).
  assert (UnitTail:sigma*scale u*qnat (2^H)%nat==1).
  { setoid_replace (sigma*scale u*qnat (2^H)%nat) with
      (sigma*(scale u*qnat (2^H)%nat)) by ring; rewrite Height; apply Unit. }
  assert (Gs:8*s<=sigma*scale u) by (unfold s; clear - S Gain; nra).
  assert (Ht:s*qnat (2^H)%nat<=(1#8)).
  { apply (Qmult_le_compat_r _ _ (qnat (2^H)%nat)) in Gs; [|lra].
    rewrite UnitTail in Gs; lra. }
  assert (F:s*(1+2*zeros ds)<=(15#56)*(sigma*scale u*zeros ds)).
  { clear - Gs Sp Z; nra. }
  assert (Budget':(qnat (n*2)%nat-4)*s==4-4*sigma-2*sigma*(a1-b1)).
  { unfold s; setoid_replace ((qnat (n*2)%nat-4)*(sigma*scale x)) with
      (sigma*((qnat (n*2)%nat-4)*scale x)) by ring.
    setoid_replace ((qnat (n*2)%nat-4)*scale x) with
      (4*qnat (2^h)%nat-4-2*(a1-b1)) by lra; nra. }
  assert (Carry:3<(qnat (n*2)%nat-4)*s).
  { rewrite Budget'; clear - Bounds Small S; nra. }
  destruct (Digits_weights _ _ _ Dig) as [Sd [Mass Ones]].
  assert (Tail:2*(mass (ds++[W0])+zeros (ds++[W0]))*s<3).
  { clear - Ht F Sp DefSmall Mass Sd;
      rewrite mass_app, zeros_app; cbn[mass zeros]; nra. }
  destruct (Scan_tail_ex (ds++[W0]) (zeros ds) n (Digits_tail _ _ _ Dig))
    as [k [y [a2 [b2 [J K]]]]].
  - clear - Tail Carry Sp; nra.
  - clear - F DefSmall Carry Sp; nra.
  - destruct (Scan_app _ _ _ _ _ _ I _ _ _ _ _ J)
      as [a [b [IJ [A B']]]].
    exists k, (x++y), a, b; split; [apply IJ|split; [apply K|]].
    pose proof (Scan_tail_bounds _ _ _ _ _ _ J _ (Digits_tail _ _ _ Dig)) as TB.
    pose proof (Scan_energy _ _ _ _ _ _ I) as E1.
    pose proof (Scan_tail_energy _ _ _ _ _ _ _ J (Digits_tail _ _ _ Dig)) as E2.
    rewrite mass_app, ones_app, A, B'; split.
    + clear - Bounds TB F S Sp; unfold s in *; nra.
    + clear - E1 E2 F S Sp; unfold s in *; nra.
Qed.

Local Open Scope nat_scope.

(* S<=-5 expressed without signed arithmetic.  Even S automatically improves
   to S<=-6, exactly the strict upper bound needed for the new compensated B. *)
Lemma Scan_barrier k u k' v a b : Scan k u k' v a b ->
  forall h H n n' eff, heightN v h=Some H -> Effective n v n' eff ->
    k+n*2+3<=4*2^h -> k'+n'*2+3<=4*2^H.
Proof.
  intro I; induction I; intros h H n0 n1 eff Height Eff Bound.
  - inversion Height; subst H; inversion Eff; subst; apply Bound.
  - inversion Eff; subst; cbn[heightN] in Height.
    eapply IHI; eauto; cbn[Nat.pow]; nia.
  - inversion Eff; subst; cbn[heightN] in Height.
    eapply IHI; eauto; cbn[Nat.pow]; nia.
  - inversion Eff; subst; cbn[heightN] in Height.
    eapply IHI; eauto; cbn[Nat.pow]; nia.
  - destruct h; [discriminate|]; inversion Eff; subst; cbn[heightN] in Height.
    all: eapply IHI; eauto; cbn[Nat.pow] in Bound; nia.
  - destruct h; [discriminate|]; inversion Eff; subst; cbn[heightN] in Height.
    all: eapply IHI; eauto; cbn[Nat.pow] in Bound; nia.
  - destruct h; [discriminate|]; inversion Eff; subst; cbn[heightN] in Height.
    all: eapply IHI; eauto; cbn[Nat.pow] in Bound; nia.
  - destruct h; [discriminate|]; inversion Eff; subst; cbn[heightN] in Height.
    all: eapply IHI; eauto; cbn[Nat.pow] in Bound; nia.
Qed.

Lemma heightN_app u : forall v h H, heightN (u++v) h=Some H ->
  exists j, heightN u h=Some j /\ heightN v j=Some H.
Proof.
  induction u as [|[] u IH]; intros v h H E; cbn[app heightN] in *.
  - exists h; auto.
  - destruct (IH _ _ _ E) as [j [J K]]; exists j; auto.
  - destruct h; [discriminate|]; apply IH,E.
  - destruct h; [discriminate|]; apply IH,E.
Qed.

Lemma Effective_input_cut u : forall n w b out, Effective n (u++w) b out ->
  exists m v x, out=v++x /\ Effective n u m v /\ Effective m w b x.
Proof.
  induction u as [|s u IH]; intros n w b out E; cbn[app] in E.
  - exists n, (@nil Word), out; split; [reflexivity|split; [constructor|apply E]].
  - inversion E; subst.
    all: match goal with I:Effective _ (_++_) _ _ |- _ =>
      destruct (IH _ _ _ _ I) as [m [v1 [x [-> [A B]]]]] end.
    all: eexists _, (_::v1), x; split; [reflexivity|split; [constructor; apply A|apply B]].
Qed.

Lemma Effective_guard_run n : Effective 1 (repeat W1 n++[WT]) 3 (repeat W0 n++[WT]).
Proof. induction n; [apply Effective_T; constructor|apply (Effective_11 0), IHn]. Qed.

Lemma Scan_guard_run n : forall h k k' v a b,
  Scan k (repeat W0 n++[WT]) k' v a b -> k+4=4*2^h ->
  exists H, v=repeat W1 n++[WT] /\ heightN v h=Some H /\ k'+12=4*2^H.
Proof.
  induction n; intros h k k' v a b I Eq; cbn[repeat app] in I.
  - inversion I; subst.
    match goal with J:Scan _ [] _ _ _ _ |- _ => inversion J; subst end.
    exists (S h); repeat split; cbn[heightN Nat.pow]; lia.
  - destruct h; [inversion I; cbn[Nat.pow] in Eq; lia|].
    inversion I; subst; cbn[Nat.pow] in Eq; try lia.
    match goal with J:Scan _ _ _ _ _ _ |- _ =>
      destruct (IHn h _ _ _ _ _ J ltac:(lia)) as [H [-> [Ht K]]] end.
    exists H; split; [reflexivity|split; [apply Ht|apply K]].
Qed.

Inductive Guard : list Word -> Prop :=
| Guard_T n w : Guard (WT::(repeat W1 n++WT::w))
| Guard_D w : Guard (W1::WT::w).

(* The guard is copied literally.  It establishes the S barrier before any
   arbitrary interior words are scanned. *)
Lemma Scan_guard h orig eff carry k v a b :
  Guard orig -> Effective 0 orig carry eff ->
  Scan (4*2^h) eff k v a b -> (0<k) ->
  exists pre rest j m x a' b' c H,
    v=pre++rest /\ Guard (pre++rest) /\
    heightN pre h=Some H /\ Effective 0 pre c x /\
    Scan j m k rest a' b' /\ j+c*2+3<=4*2^H.
Proof.
  intros G E I Pos; destruct G as [n w|w].
  - assert (Eq:WT::(repeat W1 n++WT::w)=(WT::(repeat W1 n++[WT]))++w) by
      (cbn[app]; rewrite <-app_assoc; reflexivity).
    rewrite Eq in E.
    destruct (Effective_input_cut _ _ _ _ _ E) as [c [pre [tail [-> [EP ET]]]]].
    assert (EG:Effective 0 (WT::(repeat W1 n++[WT])) 3
      (WT::(repeat W0 n++[WT]))) by (apply Effective_T, Effective_guard_run).
    destruct (Effective_unique _ _ _ _ EP _ _ EG) as [-> ->].
    destruct (Scan_cut _ _ _ _ _ _ I _ _ eq_refl)
      as [j [x [y [a1 [b1 [a2 [b2 [SX [SY [V _]]]]]]]]]].
    + left; change (cut_ok ([WT]++repeat W0 n++[WT])=true).
      rewrite app_assoc, cut_ok_last; reflexivity.
    + inversion SX; subst.
      match goal with J:Scan _ (repeat W0 n++[WT]) _ _ _ _ |- _ =>
        destruct (Scan_guard_run n (S h) _ _ _ _ _ J ltac:(cbn[Nat.pow]; lia))
          as [hh [Out [Ht K]]] end.
      subst; eexists (WT::(repeat W1 n++[WT])), y, j, tail, _, _, _, 3, hh.
      repeat split; try reflexivity; try assumption; try lia.
      * cbn[app]; rewrite <-app_assoc; constructor.
      * apply Effective_T, Effective_guard_run.
      * exact SY.
  - inversion E; subst; try lia.
    match goal with Eq:(?n*2=0) |- _ => assert (n=0) by lia; subst n end.
    match goal with E:Effective _ (WT::_) _ _ |- _ => inversion E; subst end.
    inversion I; subst; try lia.
    all: try match goal with I:Scan _ (WT::_) _ _ _ _ |- _ =>
      inversion I; subst; try lia end.
    all: destruct h; cbn[Nat.pow] in *; try lia.
    eexists [W1;WT], _, _, _, _, _, _, 1, (S h).
    repeat split; try reflexivity; try eassumption; try lia.
    + constructor.
    + apply (Effective_10 0), Effective_T; constructor.
    + cbn[Nat.add Nat.mul]; rewrite Nat.pow_succ_r'; lia.
Qed.

Lemma Scan_guard_closed h orig eff carry k v a b H n out :
  Guard orig -> Effective 0 orig carry eff -> Scan (4*2^h) eff k v a b ->
  0<k -> heightN v h=Some H -> Effective 0 v n out ->
  Guard v /\ k+n*2+3<=4*2^H.
Proof.
  intros G E I Pos Height Eff.
  destruct (Scan_guard _ _ _ _ _ _ _ _ G E I Pos)
    as [pre [rest [j [m [x [a' [b' [c [H' [-> [G' [Ht [Ep [J Bound]]]]]]]]]]]]]].
  destruct (heightN_app _ _ _ _ Height) as [hh [Hp Hr]].
  rewrite Ht in Hp; injection Hp as <-.
  destruct (Effective_input_cut _ _ _ _ _ Eff) as [c' [pre' [out' [_ [Ep' Er]]]]].
  destruct (Effective_unique _ _ _ _ Ep _ _ Ep') as [<- _].
  split; [apply G'|eapply Scan_barrier; eauto].
Qed.

Lemma heightN_raise u : forall h H, heightN u h=Some H -> heightN u (S h)=Some(S H).
Proof.
  induction u as [|[] u IH]; intros h H E; cbn[heightN] in *.
  - inversion E; reflexivity.
  - apply IH,E.
  - destruct h; [discriminate|apply IH,E].
  - destruct h; [discriminate|apply IH,E].
Qed.

Lemma heightN_Ts n : forall h, heightN (repeat WT n) h=Some(h+n).
Proof. induction n; intros h; cbn[repeat heightN]; [f_equal; lia|rewrite IHn; f_equal; lia]. Qed.

Lemma heightN_end u n h H : heightN (u++repeat WT n) h=Some H -> n<=H.
Proof.
  intro E; destruct (heightN_app _ _ _ _ E) as [j [_ J]].
  rewrite heightN_Ts in J; injection J as <-; lia.
Qed.

Lemma Effective_no_overflow n ds A H B : Digits A H ds -> A+n=B -> B<2^H ->
  exists v, Digits B H v /\ Effective n ds 0 v.
Proof.
  intros D Sum Bound; destruct (Effective_ex ds n) as [b [v E]].
  destruct (Effective_digits _ _ _ _ E _ _ D) as [C [V Eq]].
  pose proof (Digits_bound _ _ _ V).
  assert (b=0) by nia; subst b; assert (C=B) by nia; subst C; eauto.
Qed.

Lemma Digits_low_zero s : forall B H ds, Digits B H ds -> s<=H ->
  (exists n, B=n*2^s) -> exists rest, ds=repeat W0 s++rest.
Proof.
  induction s; intros B H ds D SH [n N]; [exists ds; reflexivity|].
  inversion D; subst; cbn[Nat.pow] in *; try nia.
  match goal with E:Digits _ _ _ |- _ =>
    destruct (IHs _ _ _ E ltac:(lia) ltac:(exists n; nia)) as [rest ->] end.
  exists rest; reflexivity.
Qed.

Lemma Scan_low000 k u k' v a b : Scan k (W0::W0::W0::u) k' v a b ->
  (exists n, k+12=n*16) -> exists w, v=W1::W1::W0::w.
Proof.
  intros I [n N]; inversion I; subst; try lia.
  all: match goal with J:Scan _ (W0::_) _ _ _ _ |- _ => inversion J; subst; try lia end.
  all: match goal with J:Scan _ (W0::_) _ _ _ _ |- _ => inversion J; subst; try lia end.
  eexists; reflexivity.
Qed.

Lemma Scan_regenerate_shape k u rest k' v a b :
  Scan k ((u++repeat WT 4)++W0::W0::W0::rest) k' v a b ->
  exists x y, v=(x++repeat WT 4)++W1::W1::W0::y.
Proof.
  intro I; destruct (Scan_cut _ _ _ _ _ _ I u (repeat WT 4++W0::W0::W0::rest))
    as [m [x [y [a1 [b1 [a2 [b2 [A [B [V _]]]]]]]]]].
  - rewrite app_assoc; reflexivity.
  - right; eexists; reflexivity.
  - destruct (Scan_cut _ _ _ _ _ _ B _ _ eq_refl)
      as [j [x' [y' [a3 [b3 [a4 [b4 [C [D [V' _]]]]]]]]]];
      [left; apply cut_ok_Ts|].
    destruct (Scan_repeat_T _ _ _ _ _ _ C) as [-> [N _]].
    destruct (Scan_low000 _ _ _ _ _ _ D) as [w ->].
    + exists (m-3); cbn[Nat.pow] in N; lia.
    + exists x, w; rewrite V,V',app_assoc; reflexivity.
Qed.

Lemma Effective_regenerate u rest n eff :
  Effective 0 ((u++repeat WT 4)++W1::W1::W0::rest) n eff -> has10 eff=true.
Proof.
  intro E; destruct (Effective_input_cut _ _ _ _ _ E) as [c [x [y [-> [A B]]]]].
  destruct (Effective_many_end _ _ _ _ _ A) as [z [m [_ C]]].
  inversion B; subst; cbn[Nat.pow] in C; try lia.
  all: match goal with J:Effective _ (W1::_) _ _ |- _ => inversion J; subst; try lia end.
  all: match goal with J:Effective _ (W0::_) _ _ |- _ => inversion J; subst; try lia end.
  apply has10_app; reflexivity.
Qed.

Lemma Guard_app u v : Guard u -> Guard (u++v).
Proof.
  intro G; destruct G; cbn[app]; [rewrite <-app_assoc|]; constructor.
Qed.

Local Open Scope Q_scope.

Lemma exp_deficit h u n v a b c eff sigma :
  Scan (4*2^h)%nat u (n*2)%nat v a b -> Effective 0 v c eff ->
  0<sigma -> sigma*qnat (2^h)%nat==1 ->
  1-qnat (n+c+2)%nat*(sigma*scale v*(1#2)) <=
    (sigma+sigma*(a-b-ones v))*(1#2)-3*(sigma*scale v*(1#2)).
Proof.
  intros I E S Unit.
  pose proof (Scan_budget _ _ _ _ _ _ I) as Budget.
  pose proof (Effective_budget _ _ _ _ E) as Carry.
  destruct (Effective_weights _ _ _ _ E) as [_ Mass].
  pose proof (mass_split eff); pose proof (weights_nonneg eff).
  assert (O:ones eff<=mass v) by lra.
  clear H H0 Mass.
  rewrite !qnat_mul in Budget; change (qnat 4%nat) with 4 in Budget;
    change (qnat 2%nat) with 2 in Budget.
  rewrite !qnat_add in Carry; change (qnat 1%nat) with 1 in Carry;
    change (qnat 0%nat) with 0 in Carry.
  apply (Qmult_comp _ _ (Qeq_refl sigma)) in Budget.
  apply (Qmult_comp _ _ (Qeq_refl sigma)) in Carry.
  rewrite !qnat_add; change (qnat 2%nat) with 2.
  pose proof (scale_pos v); nra.
Qed.

Lemma exp_contraction M D sigma M' D' : 0<=M -> 0<=sigma ->
  M'<=(M+(15#56)*D)*(1#2) ->
  D'<=(sigma+3*M+(45#56)*D)*(1#2) ->
  4*M'+D'+sigma<=(15#16)*(4*M+D+2*sigma).
Proof. intros; lra. Qed.

(* Binary words may contain high zeroes; correctness needs the common width
   and no overflow, not a separate canonical representation of N. *)
Inductive Good : nat -> list Word -> Prop :=
| Good_intro h H u A da carry eff B db sigma :
    heightN u h=Some H -> Guard u -> (exists w,u=w++repeat WT 4) ->
    Digits A H da -> Effective 0 u carry eff -> (A+carry=B)%nat -> Digits B H db ->
    has10 eff=true -> (exists w,db=W0::W0::W0::w) ->
    (exists w,db=w++repeat W1 7) ->
    sigma*qnat (2^h)%nat==1 ->
    4*sigma*mass u+sigma*scale u*zeros db+2*sigma<=(1#256) ->
    Good h (u++da).

Inductive Step : nat -> list Word -> list Word -> Prop :=
| Step_intro h orig eff n v a b J da :
    Effective 0 (orig++[W0]) 0 eff -> Scan (4*2^h)%nat eff (n*2)%nat v a b ->
    (0<n)%nat -> Digits (1+n)%nat J da -> Step h orig (v++da).

Lemma Digits_high7 B H ds unit : Digits B H ds ->
  0<unit -> unit*qnat (2^H)%nat==1 ->
  7<=zeros ds -> unit*zeros ds<=(1#256) ->
  exists rest, ds=rest++repeat W1 7.
Proof.
  intros D U Height Z Small.
  assert (H7:(7<=H)%nat).
  { destruct (le_dec 7 H); [assumption|].
    assert (Pow:qnat (2^H)%nat<=64) by
      (change (qnat (2^H)%nat<=qnat (2^6)%nat); apply qnat_le, Nat.pow_le_mono_r; lia).
    nra. }
  assert (Shift:unit*qnat (2^(H-7))%nat==(1#128)).
  { apply (dyadic_shift 7 H (1#128) unit H7); [reflexivity|apply Height]. }
  pose proof (Digits_zeros _ _ _ D) as Eq.
  apply (Digits_high_window (H-7)%nat 7 B ds).
  - applys_eq D; flia.
  - replace (H-7+7)%nat with H by lia.
    apply qnat_le; rewrite qnat_add; nra.
Qed.

Lemma Good_next h orig : Good h orig ->
  exists out, Step h orig out /\ Good (S h) out.
Proof.
  intro G; destruct G as [h H u A da carry eff B db sigma
    Height GuardU End DA E Sum DB Pair Low High Unit Phi].
  pose proof (heightN_spec _ _ _ Height) as Ht.
  destruct (Effective_weights _ _ _ _ E) as [Se Me].
  assert (Sig:0<sigma) by (pose proof (qpow_pos h); nra).
  pose proof (weights_nonneg u) as Wu; pose proof (weights_nonneg db) as Wdb.
  pose proof (scale_pos u) as Su.
  assert (Dpos:0<=sigma*scale u*zeros db) by (repeat apply Qmult_le_0_compat; lra).
  assert (Mu:0<=sigma*mass u) by (apply Qmult_le_0_compat; lra).
  assert (Z:7<=zeros db).
  { destruct Low as [w ->]; cbn[zeros]; pose proof (weights_nonneg w); lra. }
  assert (Ee:exists p, eff=p++repeat WT 4).
  { destruct End as [p P]; rewrite P in E.
    destruct (Effective_many_end _ _ _ _ _ E) as [w [n [V _]]]; eauto. }
  assert (Cut:cut_ok eff=true) by (destruct Ee as [p ->];
    change (repeat WT 4) with ([WT;WT;WT]++[WT]); rewrite app_assoc,cut_ok_last; reflexivity).
  assert (Ne:eff<>[]) by (destruct Ee as [p ->]; intro Eq; apply app_eq_nil in Eq as [_ Eq]; discriminate).
  destruct (exp_scan h eff B H db sigma DB Unit) as [k [v [a [b [I [Pos [Mass Energy]]]]]]].
  - rewrite Se; apply Ht.
  - apply Pair.
  - apply Cut.
  - apply Ne.
  - apply Z.
  - rewrite Se,Me; apply Phi.
  - rewrite Se,Me in Mass,Energy.
    destruct High as [hi Hi].
    assert (IH:Scan (4*2^h)%nat ((eff++hi)++repeat W1 7++[W0]) k v a b).
    { rewrite Hi in I; rewrite <-!app_assoc in I |- *; apply I. }
    destruct (Scan_many_end 3 _ _ _ _ _ _ IH) as [p [n [V K]]].
    change (k=n*16)%nat in K; subst k.
    assert (I':Scan (4*2^h)%nat (eff++db++[W0]) ((n*8)*2)%nat v a b)
      by (applys_eq I; flia).
    assert (Mv:sigma*mass v<=(1#256)) by (clear -Mass Phi Mu Sig Dpos; lra).
    destruct (heightN_mass v h) as [Hv HeightV]; [clear -Sig Unit Mv; nra|].
    destruct (Effective_ex v 0) as [carry' [eff' E']].
    destruct (Effective_no_overflow _ _ _ _ _ DA Sum (Digits_bound _ _ _ DB))
      as [db0 [DB0 ED]].
    assert (db0=db) by (eapply Digits_unique; eauto); subst db0.
    assert (Full:Effective 0 ((u++da)++[W0]) 0 (eff++db++[W0])).
    { rewrite <-app_assoc; eapply Effective_app; [apply E|].
      eapply Effective_app; [apply ED|apply (Effective_00 0); constructor]. }
    destruct (Scan_guard_closed h _ _ _ _ _ _ _ _ _ _
      (Guard_app _ _ (Guard_app _ _ GuardU)) Full I ltac:(lia) HeightV E')
      as [GuardV Barrier].
    set (J:=S Hv).
    set (A':=(1+n*8)%nat).
    set (B':=(A'+carry')%nat).
    assert (Upper:(B'<2^J)%nat) by (unfold B',A',J; cbn[Nat.pow]; lia).
    destruct (Digits_ex J A') as [da' DA']; [unfold B' in Upper; lia|].
    destruct (Digits_ex J B' Upper) as [db' DB'].
    assert (HeightNew:heightN v (S h)=Some J) by (apply heightN_raise,HeightV).
    set (unit:=sigma*scale v*(1#2)).
    assert (Up:0<unit) by (unfold unit; pose proof (scale_pos v); nra).
    assert (UH:unit*qnat (2^J)%nat==1).
    { pose proof (heightN_spec _ _ _ HeightNew) as HV.
      unfold unit; rewrite Nat.pow_succ_r',qnat_mul in HV;
        change (qnat 2%nat) with 2 in HV.
      setoid_replace (sigma*scale v*(1#2)*qnat (2^J)%nat) with
        (sigma*(scale v*qnat (2^J)%nat)*(1#2)) by ring; rewrite HV; nra. }
    assert (Dnew:unit*zeros db'<=(sigma+3*sigma*mass u+(45#56)*(sigma*scale u*zeros db))*(1#2)).
    { pose proof (exp_deficit _ _ _ _ _ _ _ _ _ I' E' Sig Unit) as Def.
      pose proof (Digits_zeros _ _ _ DB') as Zeros.
      assert (Eq:qnat (n*8+carry'+2)%nat==qnat B'+1).
      { unfold B',A'; rewrite !qnat_add; change (qnat 1%nat) with 1;
          change (qnat 2%nat) with 2; ring. }
      fold unit in Def; rewrite Eq in Def.
      clear - Def Zeros UH Up Energy; nra. }
    assert (PhiNew:4*(sigma*(1#2))*mass v+(sigma*(1#2))*scale v*zeros db'+2*(sigma*(1#2))<=(1#256)).
    { pose proof (exp_contraction (sigma*mass u) (sigma*scale u*zeros db) sigma
        (sigma*mass v*(1#2)) (unit*zeros db') Mu ltac:(lra) ltac:(lra) ltac:(lra)) as Bound.
      clear - Bound Phi; unfold unit in *; lra. }
    assert (PairNew:has10 eff'=true).
    { destruct Ee as [ue Ue]; destruct Low as [lo Lo].
      rewrite Ue,Lo in I; cbn[app] in I.
      destruct (Scan_regenerate_shape _ _ _ _ _ _ _ I) as [x [y Vy]].
      rewrite Vy in E'; eapply Effective_regenerate,E'. }
    assert (J4:(4<=J)%nat).
    { pose proof (heightN_end _ _ _ _ ltac:(rewrite <-V; apply HeightV)); unfold J; lia. }
    assert (LowNew:exists w,db'=W0::W0::W0::w).
    { rewrite V in E'; destruct (Effective_many_end _ _ _ _ _ E') as [w [m [_ Cm]]].
      apply (Digits_low_zero 3 _ _ _ DB' ltac:(lia)).
      exists (n+m*2)%nat; unfold B',A'; cbn[Nat.pow] in *; lia. }
    assert (HighNew:exists w,db'=w++repeat W1 7).
    { eapply Digits_high7; [apply DB'|apply Up|apply UH| |].
      - destruct LowNew as [w ->]; cbn[zeros]; pose proof (weights_nonneg w); lra.
      - pose proof (weights_nonneg v) as Wv; clear - PhiNew Sig Wv; unfold unit; nra. }
    exists (v++da'); split.
    + eapply (Step_intro h (u++da) _ (n*8)%nat); eauto; lia.
    + eapply (Good_intro (S h) J v A' da' carry' eff' B' db' (sigma*(1#2)));
        eauto; try (exists p; apply V).
      rewrite Nat.pow_succ_r',qnat_mul; change (qnat 2%nat) with 2; nra.
Qed.

Local Open Scope nat_scope.

Fixpoint guard_run u := match u with WT::_=>true | W1::u=>guard_run u | _=>false end.
Definition guard_check u := match u with
  | WT::u=>guard_run u | W1::WT::_=>true | _=>false end.

Lemma guard_run_spec u : guard_run u=true -> exists n w, u=repeat W1 n++WT::w.
Proof.
  induction u as [|[] u IH]; try discriminate; intro E.
  - exists 0,u; reflexivity.
  - destruct (IH E) as [n [w ->]]; exists (S n),w; reflexivity.
Qed.

Lemma guard_check_spec u : guard_check u=true -> Guard u.
Proof.
  destruct u as [|[] u]; try discriminate; cbn[guard_check].
  - intro E; destruct (guard_run_spec _ E) as [n [w ->]]; constructor.
  - destruct u as [|[] u]; try discriminate; intro; constructor.
Qed.

Definition check h orig :=
  match tail_cut orig with
  | Some(u,da) => match heightN u h with
    | Some H => if Nat.eqb H (length da) then
      if guard_check u then
        match strip_words (repeat WT 4) (rev_append u []) with
        | Some _ => let '(carry,eff):=effectiveN u 0%N [] in
          let '(last,db):=effectiveN da carry [] in
          if N.eqb last 0 then if has10 eff then
            match strip_words [W0;W0;W0] db,
              strip_words (repeat W1 7) (rev_append db []) with
            | Some _,Some _ =>
                Qle_bool ((4*mass u+scale u*zeros db+2)*scale (repeat WT h)) (1#256)
            | _,_=>false end
          else false else false
        | _=>false end
      else false else false
    | _=>false end
  | _=>false end.

Lemma check_spec h orig : check h orig=true -> Good h orig.
Proof.
  unfold check; destruct (tail_cut orig) as [[u da]|] eqn:Cut; [|discriminate].
  destruct (heightN u h) as [H|] eqn:Height; [|discriminate].
  destruct (Nat.eqb H (length da)) eqn:Width; [apply Nat.eqb_eq in Width|discriminate].
  destruct (guard_check u) eqn:GuardU; [apply guard_check_spec in GuardU|discriminate].
  destruct (strip_words (repeat WT 4) (rev_append u [])) as [last4|] eqn:End; [|discriminate].
  destruct (effectiveN u 0 []) as [carry eff] eqn:E.
  destruct (effectiveN da carry []) as [last db] eqn:D.
  destruct (N.eqb last 0) eqn:Last; [apply N.eqb_eq in Last; subst last|discriminate].
  destruct (has10 eff) eqn:Pair; [|discriminate].
  destruct (strip_words [W0;W0;W0] db) as [lo|] eqn:Low; [|discriminate].
  destruct (strip_words (repeat W1 7) (rev_append db [])) as [hi|] eqn:High; [|discriminate].
  intro Phi; apply Qle_bool_imp_le in Phi.
  destruct (tail_cut_spec _ _ _ Cut) as [Orig Dig].
  destruct (digit_list _ Dig) as [A DA]; rewrite <-Width in DA.
  destruct (effectiveN_spec _ _ _ _ _ E) as [v [V EU]]; cbn[rev_append] in V; subst v.
  destruct (effectiveN_spec _ _ _ _ _ D) as [v [V ED]]; cbn[rev_append] in V; subst v.
  destruct (Effective_digits _ _ _ _ ED _ _ DA) as [B [DB Sum]].
  apply reverse_prefix in End,High; rewrite rev_append_rev in End,High.
  change (rev (repeat WT 4)) with (repeat WT 4) in End.
  change (rev (repeat W1 7)) with (repeat W1 7) in High.
  apply strip_words_spec in Low.
  rewrite Orig; eapply (Good_intro h H u A da (N.to_nat carry) eff B db (scale (repeat WT h)));
    eauto; try lia.
  - exists lo; apply Low.
  - apply repeat_T_weights.
  - lra.
Qed.

Definition round h u :=
  let '(carry,eff):=effectiveN (u++[W0]) 0%N [] in
  if N.eqb carry 0 then
    match scanN eff (N.shiftl 4 (N.of_nat h)) [] with
    | Some(Npos(xO n),v) => Some(v++pwords(Pos.succ n))
    | _=>None end
  else None.

Lemma round_spec h u out : round h u=Some out -> Step h u out.
Proof.
  unfold round; destruct (effectiveN (u++[W0]) 0 []) as [carry eff] eqn:E.
  destruct (N.eqb carry 0) eqn:C; [apply N.eqb_eq in C; subst carry|discriminate].
  destruct (scanN eff (N.shiftl 4 (N.of_nat h)) []) as [[k v]|] eqn:I; [|discriminate].
  destruct k as [|[n|n|]]; try discriminate; intro Eq; inversion Eq; subst out.
  destruct (effectiveN_spec _ _ _ _ _ E) as [w [W EU]]; cbn[rev_append] in W; subst w.
  destruct (scanN_spec _ _ _ _ _ I) as [w [a [b [W S]]]]; cbn[rev_append] in W; subst w.
  destruct (pwords_Digits (Pos.succ n)) as [J D].
  rewrite Pos2Nat.inj_succ in D.
  rewrite N.shiftl_mul_pow2,N2Nat.inj_mul,N2Nat.inj_pow,Nat2N.id in S.
  change (Scan (4*2^h) eff (Pos.to_nat (xO n)) v a b) in S.
  rewrite Pos2Nat.inj_xO in S.
  eapply (Step_intro h u _ (Pos.to_nat n)).
  - apply EU.
  - applys_eq S; flia.
  - apply Pos2Nat.is_pos.
  - applys_eq D; flia.
Qed.

Inductive Rounds : nat -> list Word -> nat -> list Word -> Prop :=
| Rounds_refl h u : Rounds h u h u
| Rounds_next h u v j w : Step h u v -> Rounds (S h) v j w -> Rounds h u j w.

Fixpoint verify n h u := match n with
  | O=>check h u
  | S n=>match round h u with Some v=>verify n (S h) v | _=>false end
  end.

Lemma verify_spec n : forall h u, verify n h u=true ->
  exists j v, Rounds h u j v /\ Good j v.
Proof.
  induction n; intros h u E.
  - exists h,u; split; [constructor|apply check_spec,E].
  - cbn[verify] in E; destruct (round h u) as [v|] eqn:R; [|discriminate].
    destruct (IHn _ _ E) as [j [w [Run G]]]; exists j,w;
      split; [eapply Rounds_next; [apply round_spec,R|apply Run]|apply G].
Qed.

Definition start37 := repeat WT 3++[W1]++repeat WT 3++
  [W1;W1;W0;WT;W0;WT;WT;W1;W0;W0;W0;W1;W0;W1;W1;W1].
Definition start38 := [WT;W1;WT;W1;W1;WT;WT;WT;W1;WT;WT;W0;WT;WT;
  W0;W0;W0;W1;W0;W1;W1;W0;W1].
Definition start39 := [WT;W1;W1;WT;WT;W1;WT;W1;WT;WT;WT;W0;WT;WT;
  W0;W0;W1;W0;W0;W0;W1;W0;W1].
Definition start40 := [W1;W0;W0;W1;W0;W0;W0;W1].
Definition start41 := [W1;W0;W1;W0;W0;WT;W0]++repeat W1 7.
Definition start48 := [WT;WT;W1;WT;W1;W0;WT;W0;W1;W0;W1;W1].
Definition start52 := [W1;WT;W0;W0;W1].
Definition start53 := repeat WT 7++[W0;W1;W0;W1;W0;W0;W0;W0;W1].

Lemma check37 : verify 6 5 start37=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check38 : verify 8 5 start38=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check39 : verify 8 5 start39=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check40 : verify 7 4 start40=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check41 : verify 3 9 start41=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check48 : verify 8 4 start48=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check52 : verify 10 2 start52=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check53 : verify 8 2 start53=true.
Proof. vm_compute; reflexivity. Qed.

Lemma entry_nonhalt tm C n h u :
  (forall h u v, Step h u v -> C (h,u) -[tm]->+ C (S h,v)) ->
  c0 -[tm]->* C (h,u) -> verify n h u=true -> ~halts tm c0.
Proof.
  intros BS Init Check; destruct (verify_spec _ _ _ Check) as [j [v [R G]]].
  assert (Run:C (h,u) -[tm]->* C (j,v)).
  { clear - BS R; induction R;
      [constructor|eapply evstep_trans; [apply progress_evstep,BS,H|apply IHR]]. }
  eapply multistep_nonhalt; [apply Init|].
  eapply multistep_nonhalt; [apply Run|].
  eapply progress_nonhalt_cond with (P:=fun hu=>Good (fst hu) (snd hu)).
  - intros [q w] GoodW; destruct (Good_next _ _ GoodW) as [out [StepW G']].
    exists (S q,out); split; [apply BS,StepW|apply G'].
  - apply G.
Qed.

End ECore.

Module TM37.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD0LF_1LE---_1RF1RE_1RA0RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (B,[S0]).
Notation hR := (A,[S1]).
Notation h := [(hR,hL)].
Notation j := [((F,[S1;S1]),hL)].
Notation p := [((F,[S1;S0]),hL)].
Notation aR := (A,<[S1;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 5 (to_side ECore.start37 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=6) (h:=5) (u:=ECore.start37).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check37.
Qed.

End TM37.

Module TM38.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RB_1RD0RB_1LE1RC_1LF0LE_1LA0LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (E,[S0]).
Notation hR := (D,[S1]).
Notation h := [(hR,hL)].
Notation j := [((C,[S1;S1]),hL)].
Notation p := [((C,[S1;S0]),hL)].
Notation aR := (D,<[S1;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 5 (to_side ECore.start38 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=8) (h:=5) (u:=ECore.start38).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check38.
Qed.

End TM38.

Module TM39.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC0LE_1LD---_1RE1RD_1RF0RD_1LA1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (A,[S0]).
Notation hR := (F,[S1]).
Notation h := [(hR,hL)].
Notation j := [((E,[S1;S1]),hL)].
Notation p := [((E,[S1;S0]),hL)].
Notation aR := (F,<[S1;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 5 (to_side ECore.start39 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=8) (h:=5) (u:=ECore.start39).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check39.
Qed.

End TM39.

Module TM40.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (D,[S0]).
Notation hR := (C,[S1]).
Notation h := [(hR,hL)].
Notation j := [((B,[S1;S1]),hL)].
Notation p := [((B,[S1;S0]),hL)].
Notation aR := (C,<[S1;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 4 (to_side ECore.start40 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=7) (h:=4) (u:=ECore.start40).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check40.
Qed.

End TM40.

Module TM41.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LF---_1RA1RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [(hR,hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (B,<[S1;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).
Notation w := (t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 9 (to_side ECore.start41 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=3) (h:=9) (u:=ECore.start41).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check41.
Qed.

End TM41.

Module TM48.
Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC---_1RD1RC_1RE0RC_1LF0LC_1LA0LF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (F,[S0]).
Notation hR := (E,[S1]).
Notation h := [(hR,hL)].
Notation j := [((D,[S1;S1]),hL)].
Notation p := [((D,[S1;S0]),hL)].
Notation aR := (D,<[S0;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := 0inf.
Notation w := (t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000) (r:=[]) (r':=[]); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 4 (to_side ECore.start48 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=8) (h:=4) (u:=ECore.start48).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check48.
Qed.

End TM48.

Module TM52.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0LF_1LD0LC_0LE0LA_1LF---_1RA1RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [(hR,hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (A,<[S0;S1;S0;S1;S0;S1]).
Notation a := [(aR,hL)].
Notation lh := 0inf.
Notation w := (t++t++[S0]++t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000) (r:=[]) (r':=[]); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 2 (to_side ECore.start52 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=10) (h:=2) (u:=ECore.start52).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check52.
Qed.

End TM52.

Module TM53.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RB_1RD0RB_1LE1RC_1LF0LE_0LA0LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (E,[S0]).
Notation hR := (D,[S1]).
Notation h := [(hR,hL)].
Notation j := [((C,[S1;S1]),hL)].
Notation p := [((C,[S1;S0]),hL)].
Notation aR := (C,<[S0;S1;S0;S1;S0;S1]).
Notation a := [(aR,hL)].
Notation lh := 0inf.
Notation w := (t++t++[S0]++t++t++one).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  cbn[app]; unfold DH0; flia; esc.

Lemma H_T n : segRLs tm (h^^n) (h^^(n*2)) t t.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 1 2 n 0 0. Qed.
Lemma H_00 n : segRLs tm (h^^(n*2)) (h^^n) d0 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_01 n : segRLs tm (h^^(1+n*2)) (h^^n) d0 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 0. Qed.
Lemma H_10 n : segRLs tm (h^^(n*2)) (h^^n) d1 d1.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 0 0. Qed.
Lemma H_11 n : segRLs tm (h^^(1+n*2)) (h^^(1+n)) d1 d0.
Proof. am (@nil (DH0*DH0)) (@nil (DH0*DH0)) 2 1 n 1 1. Qed.
Lemma H_blank : sideRLs tm h 0inf (d1*>0inf).
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=100) (r:=[]) (r':=d1); reflexivity. Qed.

Lemma T_one : segRLs tm p h t (t++[S0]).
Proof. esc. Qed.
Lemma T_two : segRLs tm j h t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (h++j++h^^(n*2)) t t.
Proof. am (p) (h++j) 1 2 n 1 0. Qed.
Lemma T_even n : segRLs tm (j++h^^(1+n)) (h++j++h^^(1+n*2)) t t.
Proof. am (j) (h++j) 1 2 n 1 1. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.
Lemma Pair_01 n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma Pair_02 n : segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_11 n : segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.
Lemma Pair_12 n : segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.
Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.
Lemma Short_01 n : segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.
Lemma Short_02 n : segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.
Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.
Lemma Short_11 n : segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.
Lemma Short_12 n : segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.

Lemma Carry_T n : segRLs tm (h^^n++j++h) (h^^(1+n*2)++j++h) t t.
Proof.
  applys_eq (segRLs_trans (H_T n) (T_even 0)); cbn[lpow app]; flia.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add,<-app_assoc; reflexivity.
Qed.

Lemma Carry_edge_left n : segRLs tm (h^^(1+n*2)) (j++h^^n) (d1++one) d0.
Proof. am (@nil (DH0*DH0)) j 2 1 n 1 0. Qed.

Lemma Carry_edge n : segRLs tm (h^^(1+n*2)++j++h) (j++h^^n)
  (d1++one) (d1++one).
Proof. applys_eq (segRLs_trans (Carry_edge_left n) Short_10); flia; rewrite ?app_nil_r; reflexivity. Qed.

Lemma Carry_Ts q : forall n, segRLs tm (h^^n++j++h)
  (h^^((1+n)*2^q-1)++j++h) (t^^q) (t^^q).
Proof.
  induction q; intro n.
  - cbn[Nat.pow lpow]; replace ((1+n)*1-1) with n by lia; apply segRLs_nil.
  - change (t^^(S q)) with (t++t^^q).
    replace ((1+n)*2^(S q)-1) with ((1+(1+n*2))*2^q-1) by (cbn[Nat.pow]; nia).
    apply (segRLs_concat (Carry_T n) (IHq (1+n*2))).
Qed.

Lemma Counter_prefix q : segRLs tm (j++h) (j++h^^(2^q-1))
  (t^^(1+q)++d1++one) (t^^(1+q)++d1++one).
Proof.
  assert (E:((1+0)*2^(1+q)-1)=1+(2^q-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  pose proof (Carry_Ts (1+q) 0) as T; rewrite E in T; cbn[lpow app] in T.
  applys_eq (segRLs_concat T (Carry_edge (2^q-1))); flia.
Qed.

Lemma Step_sound q orig out : ECore.Step q orig out ->
  Counter tm h j p (4*2^q) (to_side orig 0inf) (to_side out 0inf).
Proof.
  intro S; destruct S as [q orig eff n v a0 b0 J da E I N DA].
  assert (Blank:to_side [W0] 0inf=0inf).
  { change (S0>>S0>>0inf=0inf); rewrite <-!const_unfold; reflexivity. }
  assert (R:PCore.RIncs (n*2) 0inf (to_side da 0inf)).
  { applys_eq (Digits_RIncs _ _ _ DA ltac:(lia)); flia. }
  assert (Pos:0<n*2) by lia.
  rewrite to_side_app.
  assert (Run:Counter tm h j p (4*2^q) (to_side (orig++[W0]) 0inf)
    (to_side v (to_side da 0inf))).
  { eapply PCore.Scan_Packet; eauto using H_T,H_00,H_01,H_10,H_11,H_blank,
      T_one,T_two,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12,PCore.Packet_zero. }
  rewrite to_side_app,Blank in Run; apply Run.
Qed.

Lemma RSend : segRLs tm a (j++h) w (w++t).
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000) (r:=[]) (r':=[]); reflexivity. Qed.

Definition Config q r := lh {{{ (hL,L) }}} ((w++t^^(2+q)++d1++one)*>r).

Lemma RSend_full q : segRLs tm a (j++h^^(2^(1+q)-1))
  (w++t^^(2+q)++d1++one) (w++t^^(2+S q)++d1++one).
Proof.
  applys_eq (segRLs_concat RSend (Counter_prefix (1+q))); flia.
Qed.

Lemma BigStep q r r' : Counter tm h j p (4*2^q) r r' ->
  Config q r -->+ Config (S q) r'.
Proof.
  intro R; unfold Config.
  eapply @sideRLs_concat_v2_L with (ls:=a); [reflexivity|discriminate|apply LSend|].
  eapply (segRLs_sideRLs_concat (RSend_full q)).
  apply (R []); replace (4*2^q) with (2+(2^(1+q)-1)*2) by (cbn[Nat.add Nat.pow]; lia).
  apply Num2.
Qed.

Lemma init : c0 -->* Config 2 (to_side ECore.start53 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply ECore.entry_nonhalt with (C:=fun qr=>Config (fst qr) (to_side (snd qr) 0inf))
    (n:=8) (h:=2) (u:=ECore.start53).
  - intros q u v S; apply BigStep,Step_sound,S.
  - apply init.
  - apply ECore.check53.
Qed.

End TM53.

(* L66 and L66_1: the translated budget k-2.  Unlike CCore/PCore,
   the T step is k -> 2k-2 and emits no extra # call. *)
Module BCore.
Inductive RIncs : nat -> side -> side -> Prop :=
| RIncs_0 r : RIncs 0 r (one*>r)
| RIncs_T n r r' : RIncs (n*2) r r' ->
    RIncs (1+n) (t*>r) (t*>r')
| RIncs_pair0 n r r' : RIncs (n*2) r r' ->
    RIncs (1+n) (d1*>d0*>r) (t*>r')
| RIncs_pair1 n r r' : RIncs (1+n*2) r r' ->
    RIncs (1+n) (d1*>d1*>r) (t*>r')
| RIncs_short00 n r r' : RIncs (n*2) r r' ->
    RIncs (2+n*4) (d0*>r) (d0*>r')
| RIncs_short01 n r r' : RIncs (1+n*2) r r' ->
    RIncs (2+n*4) (d1*>r) (d0*>r')
| RIncs_short10 n r r' : RIncs (n*2) r r' ->
    RIncs (4+n*4) (d0*>r) (d1*>r')
| RIncs_short11 n r r' : RIncs (1+n*2) r r' ->
    RIncs (4+n*4) (d1*>r) (d1*>r').

Local Open Scope Q_scope.
Ltac qnorm :=
  repeat (rewrite qnat_add in * || rewrite qnat_mul in * || rewrite qnat_S in *);
  change (qnat 0%nat) with 0 in *; change (qnat 1%nat) with 1 in *;
  change (qnat 2%nat) with 2 in *; change (qnat 4%nat) with 4 in *.

Inductive Scan : nat -> list Word -> nat -> list Word -> QArith_base.Q -> QArith_base.Q -> Prop :=
| Scan_nil k : Scan k [] k [] 0 0
| Scan_T n u k v a b : Scan (n*2)%nat u k v a b ->
    Scan (1+n)%nat (WT::u) k (WT::v) (a*(1#2)) (b*(1#2))
| Scan_pair0 n u k v a b : Scan (n*2)%nat u k v a b ->
    Scan (1+n)%nat (W1::W0::u) k (WT::v) (a*(1#2)) (b*(1#2))
| Scan_pair1 n u k v a b : Scan (1+n*2)%nat u k v a b ->
    Scan (1+n)%nat (W1::W1::u) k (WT::v) (a*(1#2)) ((1#4)+b*(1#2))
| Scan_short00 n u k v a b : Scan (n*2)%nat u k v a b ->
    Scan (2+n*4)%nat (W0::u) k (W0::v) (2+a*2) (b*2)
| Scan_short01 n u k v a b : Scan (1+n*2)%nat u k v a b ->
    Scan (2+n*4)%nat (W1::u) k (W0::v) (1+a*2) (b*2)
| Scan_short10 n u k v a b : Scan (n*2)%nat u k v a b ->
    Scan (4+n*4)%nat (W0::u) k (W1::v) (3+a*2) (b*2)
| Scan_short11 n u k v a b : Scan (1+n*2)%nat u k v a b ->
    Scan (4+n*4)%nat (W1::u) k (W1::v) (2+a*2) (b*2).

Lemma Scan_budget k u k' v a b : Scan k u k' v a b ->
  qnat k-2 == (qnat k'-2)*scale v+2*(a-b).
Proof.
  intro I; induction I; cbn[scale] in *; qnorm; nra.
Qed.


Lemma Scan_bounds k u k' v a b : Scan k u k' v a b ->
  mass v<=mass u /\ 0<=a /\ a<=2*mass u+zeros u /\ 0<=b /\
  mass v+a-b-ones v<=2*mass u+zeros u.
Proof.
  intro I; induction I; cbn[mass zeros ones] in *;
    try match goal with _:Scan _ ?u _ _ _ _ |- _ =>
      pose proof (weights_nonneg u); pose proof (mass_split u) end; lra.
Qed.
Lemma Scan_app k u k' v a b : Scan k u k' v a b -> forall w k'' x c d,
  Scan k' w k'' x c d -> exists a' b',
  Scan k (u++w) k'' (v++x) a' b' /\
  a'==a+scale v*c /\ b'==b+scale v*d.
Proof.
  intro I; induction I; intros w k'' x c d J; cbn[app scale].
  1: { exists c, d; split; [apply J|split; ring]. }
  all: destruct (IHI _ _ _ _ _ J) as [a' [b' [K [A B]]]];
    eexists _, _; split; [econstructor; apply K|split; lra].
Qed.

Lemma Scan_ex_mode e u (I : Parse e u) : forall k,
  (e=true -> exists n, k=(n*2)%nat) -> 6*mass u<qnat k-2 ->
  exists b v lp lm, Scan k u b v lp lm /\ (2<b)%nat.
Proof.
  induction I; intros k Ek Hk.
  - exists k, (@nil Word), 0, 0; split; [constructor|].
    apply qnat_lt; cbn[mass] in Hk; qnorm; lra.
  - pose proof (weights_nonneg u) as Wu.
    destruct k as [|k]; try solve [cbn[mass] in Hk; qnorm; nra].
    edestruct (IHI (k*2)%nat) as [b [v [lp [lm [H B]]]]].
    + intro; exists k; lia.
    + cbn[mass] in Hk; qnorm; nra.
    + exists b, (WT::v), (lp*(1#2)), (lm*(1#2)); split; [apply Scan_T, H|apply B].
  - pose proof (weights_nonneg u) as Wu; destruct (Ek eq_refl) as [n ->].
    destruct (mod2 n); subst n.
    + destruct a as [|a]; [cbn[mass] in Hk; qnorm; nra|].
      edestruct (IHI (a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * intro; eexists; reflexivity.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W1::v), (3+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short10 a); flia; apply H.
    + edestruct (IHI (a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * intro; eexists; reflexivity.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W0::v), (2+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short00 a); flia; apply H.
  - pose proof (weights_nonneg u) as Wu; destruct (Ek eq_refl) as [n ->].
    destruct (mod2 n); subst n.
    + destruct a as [|a]; [cbn[mass] in Hk; qnorm; nra|].
      edestruct (IHI (1+a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * discriminate.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W1::v), (2+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short11 a); flia; apply H.
    + edestruct (IHI (1+a*2)%nat) as [b [v [lp [lm [H B]]]]].
      * discriminate.
      * cbn[mass] in Hk; qnorm; nra.
      * exists b, (W0::v), (1+lp*2), (lm*2); split; [|apply B].
        applys_eq (Scan_short01 a); flia; apply H.
  - pose proof (weights_nonneg u) as Wu.
    destruct k as [|k]; [cbn[mass] in Hk; qnorm; nra|].
    edestruct (IHI (k*2)%nat) as [b [v [lp [lm [H B]]]]].
    + intro; eexists; reflexivity.
    + cbn[mass] in Hk; qnorm; nra.
    + exists b, (WT::v), (lp*(1#2)), (lm*(1#2)); split; [apply Scan_pair0, H|apply B].
  - pose proof (weights_nonneg u) as Wu.
    destruct k as [|k]; [cbn[mass] in Hk; qnorm; nra|].
    edestruct (IHI (1+k*2)%nat) as [b [v [lp [lm [H B]]]]].
    + discriminate.
    + cbn[mass] in Hk; qnorm; nra.
    + exists b, (WT::v), (lp*(1#2)), ((1#4)+lm*(1#2)); split; [apply Scan_pair1, H|apply B].
Qed.

Lemma Scan_ex u k : 6*mass u<qnat (k*2)%nat-2 ->
  exists b v lp lm, Scan (k*2)%nat u b v lp lm /\ (2<b)%nat.
Proof.
  intro H; eapply Scan_ex_mode; [apply (proj1 (Parse_all u))| |apply H].
  intro; eexists; reflexivity.
Qed.

Lemma Scan_digits_from_core k u k' v l : CCore.Scan k u k' v l -> forall A H,
  Digits A H u -> exists a b, Scan k u k' v a b /\ a<=2*mass v+l /\ b<=l.
Proof.
  intro I; induction I; intros A H D; inversion D; subst.
  1: { exists 0, 0; split; [constructor|cbn[mass]; lra]. }
  all: repeat match goal with D:Digits _ _ (_::_) |- _ => inversion D; subst; clear D end.
  all: match goal with D:Digits _ _ _ |- _ =>
    destruct (IHI _ _ D) as [a [b [J [P M]]]] end.
  - exists (a*(1#2)), (b*(1#2)); split; [apply Scan_pair0, J|cbn[mass]; lra].
  - exists (a*(1#2)), ((1#4)+b*(1#2)); split; [apply Scan_pair1, J|cbn[mass]; lra].
  - exists (2+a*2), (b*2); split; [apply Scan_short00, J|cbn[mass]; lra].
  - exists (1+a*2), (b*2); split; [apply Scan_short01, J|cbn[mass]; lra].
  - exists (3+a*2), (b*2); split; [apply Scan_short10, J|cbn[mass]; lra].
  - exists (2+a*2), (b*2); split; [apply Scan_short11, J|cbn[mass]; lra].
Qed.

Lemma Scan_digits_to_core k u k' v a b : Scan k u k' v a b -> forall A H,
  Digits A H u -> exists l, CCore.Scan k u k' v l /\ a<=2*mass v+l /\ b<=l.
Proof.
  intro I; induction I; intros A H D; inversion D; subst.
  1: { exists 0; split; [constructor|cbn[mass]; lra]. }
  all: repeat match goal with D:Digits _ _ (_::_) |- _ => inversion D; subst; clear D end.
  all: match goal with D:Digits _ _ _ |- _ =>
    destruct (IHI _ _ D) as [l [J [P M]]] end.
  - exists ((1+l)*(1#2)); split; [apply CCore.Scan_pair0, J|cbn[mass]; lra].
  - exists ((1#4)+l*(1#2)); split; [apply CCore.Scan_pair1, J|cbn[mass]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short00, J|cbn[mass]; lra].
  - exists (l*2); split; [apply CCore.Scan_short01, J|cbn[mass]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short10, J|cbn[mass]; lra].
  - exists (l*2); split; [apply CCore.Scan_short11, J|cbn[mass]; lra].
Qed.


Lemma Scan_scale k u k' v a b : Scan k u k' v a b -> scale v<=scale u.
Proof.
  intro I; induction I; cbn[scale] in *; try lra; pose proof (scale_pos u); lra.
Qed.

Lemma Scan_cut k u k' v a b : Scan k u k' v a b -> forall p q,
  u=p++q -> cut_at p q ->
  exists m x y a1 b1 a2 b2, Scan k p m x a1 b1 /\ Scan m q k' y a2 b2 /\
    v=x++y /\ a==a1+scale x*a2 /\ b==b1+scale x*b2.
Proof.
  intro I; induction I; intros p q E P; destruct p as [|s p].
  all: try (cbn[app] in E; subst q;
    eexists _, (@nil Word), _, 0, 0, _, _;
    split; [constructor|]; split; [eauto using Scan|];
    split; [reflexivity|cbn[scale]; split; ring]).
  1: { discriminate. }
  all: injection E as Es E; subst s.
  2,3: destruct p as [|s p];
    [cbn[app] in E; subst q; destruct P as [P|[r P]]; discriminate|];
    injection E as Es E; subst s; do 2 apply cut_at_tail in P.
  1,4,5,6,7: apply cut_at_tail in P.
  all: destruct (IHI _ _ E P) as [m [x [y [a1 [b1 [a2 [b2 [J [K [-> [A B]]]]]]]]]]].
  all: eexists _, (_::x), y, _, _, a2, b2;
    split; [eauto using Scan|]; split; [apply K|];
    split; [reflexivity|cbn[scale]; split; nra].
Qed.

Lemma Scan_many_end r k u k' v a b :
  Scan k (u++repeat W1 (1+r*2)%nat++[W0]) k' v a b ->
  exists w n, v=w++repeat WT (1+r)%nat /\ k'=(n*2^(1+r))%nat.
Proof.
  intro I; destruct (trailing_ones u) as [p [n [-> P]]].
  assert (E : (p++repeat W1 n)++repeat W1 (1+r*2)%nat++[W0]=
    p++(repeat W1 (1+r*2+n)%nat++[W0])).
  { replace (1+r*2+n)%nat with (n+(1+r*2))%nat by lia.
    rewrite (repeat_app W1 n (1+r*2)%nat); rewrite !app_assoc; reflexivity. }
  rewrite E in I.
  destruct (Scan_cut _ _ _ _ _ _ I _ _ eq_refl)
    as [m [x [y [a1 [b1 [a2 [b2 [J [K [-> _]]]]]]]]]]; [left; apply P|].
  pose proof (Digits_app _ _ _ (Digits_ones (1+r*2+n)%nat) _ _ _
    (Digits_zero 0 0 _ Digits_nil)) as D.
  destruct (Scan_digits_to_core _ _ _ _ _ _ K _ _ D) as [l [L _]].
  destruct (CCore.Scan_ones_long _ _ _ _ _ _ L) as [w [q [-> Q]]].
  exists (x++w), q; rewrite app_assoc; auto.
Qed.



Lemma Scan_digits_energy k u k' v a b : Scan k u k' v a b -> forall A H,
  Digits A H u -> exists l, CCore.Scan k u k' v l /\ a-b-ones v<=mass v+l.
Proof.
  intro I; induction I; intros A H D; inversion D; subst.
  1: { exists 0; split; [constructor|cbn[mass ones]; lra]. }
  all: repeat match goal with D:Digits _ _ (_::_) |- _ => inversion D; subst; clear D end.
  all: match goal with D:Digits _ _ _ |- _ =>
    destruct (IHI _ _ D) as [l [J L]] end.
  - exists ((1+l)*(1#2)); split; [apply CCore.Scan_pair0,J|cbn[mass ones]; lra].
  - exists ((1#4)+l*(1#2)); split; [apply CCore.Scan_pair1,J|cbn[mass ones]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short00,J|cbn[mass ones]; lra].
  - exists (l*2); split; [apply CCore.Scan_short01,J|cbn[mass ones]; lra].
  - exists (1+l*2); split; [apply CCore.Scan_short10,J|cbn[mass ones]; lra].
  - exists (l*2); split; [apply CCore.Scan_short11,J|cbn[mass ones]; lra].
Qed.

Lemma core_tail_pair_bounds k ds k' v l : CCore.Scan k (ds++[W0]) k' v l ->
  (exists w,ds=W1::W0::w) -> (exists A H,Digits A H ds) ->
  mass v<=zeros ds*(1#4) /\ mass v+l<=zeros ds*(1#2)+(1#2).
Proof.
  intros I [w ->] [A [H D]]; inversion D; subst.
  match goal with J:Digits _ _ (W0::_) |- _ => inversion J; subst end.
  destruct (CCore.Scan_pair0_inv _ _ _ _ _ I) as [n [x [s [_ [J [-> L]]]]]].
  match goal with K:Digits _ _ w |- _ =>
    pose proof (CCore.Scan_tail_bounds _ _ _ _ _ J _ (Digits_tail _ _ _ K)) as B end.
  cbn[zeros mass] in *; lra.
Qed.

Lemma Scan_tail_pair_bounds k ds k' v a b : Scan k (ds++[W0]) k' v a b ->
  (exists w,ds=W1::W0::w) -> (exists A H,Digits A H ds) ->
  mass v<=zeros ds*(1#4) /\ a<=zeros ds /\
  mass v+a-b-ones v<=zeros ds.
Proof.
  intros I Low [A [H D]].
  pose proof (Digits_app _ _ _ D _ _ _ (Digits_zero 0 0 _ Digits_nil)) as Full.
  destruct (Scan_digits_to_core _ _ _ _ _ _ I _ _ Full) as [l [J [P _]]].
  destruct (Scan_digits_energy _ _ _ _ _ _ I _ _ Full) as [l' [J' E]].
  pose proof (core_tail_pair_bounds _ _ _ _ _ J Low (ex_intro _ A (ex_intro _ H D))).
  pose proof (core_tail_pair_bounds _ _ _ _ _ J' Low (ex_intro _ A (ex_intro _ H D))).
  destruct Low as [w ->]; cbn[zeros] in *; pose proof (weights_nonneg w); lra.
Qed.

(* Existence is established before applying the completed-scan bounds.
   The first D1 D0 pair reduces the cost of the binary suffix enough for
   the existing CCore existence theorem, including its virtual final D0. *)
Lemma C4_scan u A H ds : Digits A H ds ->
  scale u*qnat (2^H)%nat==(1#2) ->
  3*mass u+zeros u+scale u*zeros ds<=(1#64) ->
  (exists w,ds=W1::W0::w) ->
  exists k v a b, Scan 4 (u++ds++[W0]) k v a b /\ (2<k)%nat /\
    a<=2*mass u+zeros u+scale u*zeros ds /\
    mass v<=mass u+scale u*zeros ds*(1#4) /\
    mass v+a-b-ones v<=2*mass u+zeros u+scale u*zeros ds.
Proof.
  intros Dig Height Phi Low.
  pose proof (weights_nonneg u) as Wu; pose proof (weights_nonneg ds) as Wd.
  pose proof (scale_pos u) as Su.
  assert (Small:6*mass u<qnat (2*2)%nat-2) by
    (change (qnat (2*2)%nat) with 4; nra).
  destruct (Scan_ex u 2 Small) as [m [x [a1 [b1 [I Pos]]]]].
  pose proof (Scan_budget _ _ _ _ _ _ I) as Budget.
  pose proof (Scan_bounds _ _ _ _ _ _ I) as Bounds.
  pose proof (Scan_scale _ _ _ _ _ _ I) as Gain.
  pose proof (scale_pos x) as Sx.
  change (2==(qnat m-2)*scale x+2*(a1-b1)) in Budget.
  assert (Carry:1<qnat m*scale x) by nra.
  destruct Low as [w Eq].
  assert (Rest:(mass (w++[W0])+zeros (w++[W0])+2)*scale x<=1).
  { rewrite <-(proj1 (Digits_weights _ _ _ Dig)) in Height.
    rewrite Eq in Dig,Height; cbn[scale] in Height; inversion Dig; subst.
    match goal with J:Digits _ _ (W0::_) |- _ => inversion J; subst end.
    match goal with J:Digits _ _ w |- _ =>
      pose proof (Digits_weights _ _ _ J) as [Dw Mw] end.
    pose proof (weights_nonneg w); pose proof (mass_split w); pose proof (scale_pos w).
    rewrite mass_app,zeros_app; cbn[mass zeros]; nra. }
  destruct m as [|m]; [lia|].
  destruct (CCore.Scan_ex (w++[W0]) m) as [k [y [l [J K]]]].
  - rewrite qnat_mul; change (qnat 2%nat) with 2.
    rewrite qnat_S in Carry; clear - Rest Carry Sx; nra.
  - assert (Core:CCore.Scan (S m) (ds++[W0]) k (WT::y) ((1+l)*(1#2))).
    { rewrite Eq; cbn[app]; apply CCore.Scan_pair0,J. }
    pose proof (Digits_app _ _ _ Dig _ _ _ (Digits_zero 0 0 _ Digits_nil)) as Full.
    destruct (Scan_digits_from_core _ _ _ _ _ Core _ _ Full) as [a2 [b2 [J' _]]].
    destruct (Scan_app _ _ _ _ _ _ I _ _ _ _ _ J') as [a [b [IJ [Ap Bp]]]].
    destruct (Scan_tail_pair_bounds _ _ _ _ _ _ J' ltac:(eauto) ltac:(eauto)) as [Mt [At Et]].
    exists k,(x++WT::y),a,b; split; [apply IJ|].
    assert (Afull:a<=2*mass u+zeros u+scale u*zeros ds).
    { rewrite Ap; clear -Bounds At Gain Sx Wd; nra. }
    assert (Positive:(2<k)%nat).
    { pose proof (Scan_budget _ _ _ _ _ _ IJ) as B.
      pose proof (Scan_bounds _ _ _ _ _ _ IJ) as F.
      pose proof (scale_pos (x++WT::y)) as S.
      change (2==(qnat k-2)*scale (x++WT::y)+2*(a-b)) in B.
      apply qnat_lt; change (qnat 2%nat) with 2; clear -B F S Afull Phi Wu; nra. }
    split; [apply Positive|]; split; [apply Afull|]; rewrite mass_app,ones_app,Ap,Bp; split.
    + clear -Bounds Mt Gain Sx Wd; nra.
    + clear -Bounds Et Gain Sx Wd; nra.
Qed.

Lemma Scan_repeat_T p : forall k k' v a b, Scan k (repeat WT p) k' v a b ->
  v=repeat WT p /\ (k'+2*2^p=k*2^p+2)%nat /\ a==0 /\ b==0.
Proof.
  induction p; intros k k' v a b I; inversion I; subst.
  - cbn[Nat.pow]; repeat split; try reflexivity; lia.
  - match goal with J:Scan _ _ _ _ _ _ |- _ =>
      destruct (IHp _ _ _ _ _ J) as [-> [Eq [A B]]] end.
    cbn[repeat Nat.pow]; split; [reflexivity|split; [nia|split; lra]].
Qed.


Local Open Scope nat_scope.

Lemma Scan_barrier_strict k u k' v a b : Scan k u k' v a b ->
  forall h H, heightN v h=Some H -> k<2^(1+h) -> k'<2^(1+H).
Proof.
  intro I; induction I; intros h H Height Bound; cbn[heightN] in Height.
  1: { inversion Height; subst; apply Bound. }
  1,2,3: eapply IHI; [apply Height|cbn[Nat.add Nat.pow] in *; nia].
  all: destruct h; [discriminate|]; eapply IHI;
    [apply Height|cbn[Nat.add Nat.pow] in *; nia].
Qed.

Lemma Scan_barrier k u k' v a b : Scan k u k' v a b ->
  forall h H, heightN v h=Some H -> u<>[] -> k<=2^(1+h) -> k'<2^(1+H).
Proof.
  intro I; destruct I; intros h H Height Ne Bound.
  1: { contradiction. }
  all: cbn[heightN] in Height.
  1,2,3: eapply Scan_barrier_strict; [eassumption|apply Height|cbn[Nat.add Nat.pow] in *; nia].
  all: destruct h; [discriminate|]; eapply Scan_barrier_strict;
    [eassumption|apply Height|cbn[Nat.add Nat.pow] in *; nia].
Qed.

Definition Guard u := exists p w, u=repeat WT (1+p)++W0::w.

Lemma Guard_app u v : Guard u -> Guard (u++v).
Proof. intros [p [w ->]]; exists p,(w++v); rewrite <-app_assoc; reflexivity. Qed.

Lemma Scan_guard p u k v a b : Scan 4 (repeat WT (1+p)++W0::u) k v a b ->
  exists w a' b', v=repeat WT (1+p)++W0::w /\ Scan (2^(1+p)) u k w a' b'.
Proof.
  intro I; destruct (Scan_cut _ _ _ _ _ _ I _ _ eq_refl)
    as [m [x [y [a1 [b1 [a2 [b2 [J [K [-> _]]]]]]]]]];
    [left; apply PCore.cut_ok_Ts|].
  destruct (Scan_repeat_T _ _ _ _ _ _ J) as [-> [Eq _]].
  inversion K; subst; cbn[Nat.pow Nat.add] in Eq; try nia.
  eexists _, _, _; split; [reflexivity|].
  replace (2^(1+p)) with (n*2) by (cbn[Nat.add Nat.pow]; lia); eassumption.
Qed.

Lemma has10_Ts p u : has10 (repeat WT p++u)=has10 u.
Proof. induction p; cbn[repeat app has10]; auto. Qed.

Lemma Scan_guard_closed orig k v a b J : Scan 4 orig k v a b ->
  Guard orig -> has10 orig=true -> heightN v 0=Some J ->
  Guard (WT::v) /\ k<2^(1+J).
Proof.
  intros I [p [u U]] Pair Height; rewrite U in I.
  destruct (Scan_guard _ _ _ _ _ _ I) as [w [a' [b' [V S]]]].
  split.
  - exists (1+p),w; rewrite V; reflexivity.
  - assert (H:heightN w p=Some J).
    { rewrite V in Height.
      destruct (ECore.heightN_app _ _ _ _ Height) as [h [H1 H2]].
      rewrite ECore.heightN_Ts in H1; injection H1 as <-; apply H2. }
    assert (Ne:u<>[]).
    { intros ->; rewrite U,has10_Ts in Pair; discriminate. }
    eapply Scan_barrier; [apply S|apply H|apply Ne|lia].
Qed.


Lemma Digits_low01 n H ds : Digits (1+n*4) H ds -> 2<=H ->
  exists w,ds=W1::W0::w.
Proof.
  intros D Bound; inversion D; subst; try lia.
  match goal with J:Digits _ _ _ |- _ => inversion J; subst; try lia end.
  eexists; reflexivity.
Qed.

Local Open Scope Q_scope.

Lemma Digits_high6 B H ds unit : Digits B H ds ->
  0<unit -> unit*qnat (2^H)%nat==1 ->
  2<=zeros ds -> unit*(1+zeros ds)<=(1#64) ->
  exists rest,ds=rest++repeat W1 6.
Proof.
  intros D U Height Z Small.
  assert (H6:(6<=H)%nat).
  { destruct (le_dec 6 H); [assumption|].
    assert (Pow:qnat (2^H)%nat<=32) by
      (change (qnat (2^H)%nat<=qnat (2^5)%nat); apply qnat_le,Nat.pow_le_mono_r; lia).
    nra. }
  assert (Shift:unit*qnat (2^(H-6))%nat==(1#64)).
  { apply (PCore.dyadic_shift 6 H (1#64) unit H6); [reflexivity|apply Height]. }
  pose proof (Digits_zeros _ _ _ D) as Eq.
  apply (PCore.Digits_high_window (H-6)%nat 6 B ds).
  - applys_eq D; flia.
  - replace (H-6+6)%nat with H by lia; apply qnat_le; rewrite qnat_add; nra.
Qed.

Inductive Good : list Word -> Prop :=
| Good_intro H u A ds : Digits A H ds ->
    scale u*qnat (2^H)%nat==(1#2) -> Guard u ->
    (exists w,u=w++[WT]) -> (exists w,ds=W1::W0::w) ->
    (exists w,ds=w++repeat W1 6) ->
    3*mass u+zeros u+scale u*zeros ds<=(1#64) ->
    Good (u++ds).

Inductive Step : list Word -> list Word -> Prop :=
| Step_intro orig n v a b J ds : Scan 4 (orig++[W0]) (n*2)%nat v a b ->
    Digits (1+n)%nat J ds -> Step orig (WT::(v++ds)).

Lemma Good_next orig : Good orig ->
  exists out,Step orig out /\ Good out.
Proof.
  intros [H u A ds Dig Height Gu End Low High Phi].
  pose proof (weights_nonneg u) as Wu; pose proof (weights_nonneg ds) as Wd.
  pose proof (scale_pos u) as Su.
  destruct (C4_scan _ _ _ _ Dig Height Phi Low)
    as [k [v [a [b [I [Pos [Ap [Mass Energy]]]]]]]].
  assert (MassSmall:mass v<(1#64)) by (clear -Phi Mass Su Wd Wu; nra).
  destruct (PCore.heightN_mass v 0) as [J Hv]; [change (mass v<1); lra|].
  pose proof (heightN_spec _ _ _ Hv) as Unit; change (qnat (2^0)%nat) with 1 in Unit.
  destruct High as [hi Hi].
  assert (IH:Scan 4 ((u++hi++[W1])++repeat W1 5++[W0]) k v a b).
  { rewrite Hi in I; change (repeat W1 6) with ([W1]++repeat W1 5) in I.
    rewrite <-!app_assoc in I |- *; apply I. }
  destruct (Scan_many_end 2 _ _ _ _ _ _ IH) as [last [n [V K]]].
  change (v=last++repeat WT 3) in V.
  change (k=n*8)%nat in K; subst k.
  assert (J3:(3<=J)%nat).
  { apply (ECore.heightN_end last 3 0 J); rewrite <-V; apply Hv. }
  assert (Pair:has10 (u++ds++[W0])=true).
  { apply has10_app; destruct Low as [w ->]; reflexivity. }
  destruct (Scan_guard_closed _ _ _ _ _ _ I (Guard_app _ _ Gu) Pair Hv)
    as [GuardV Upper].
  assert (Pow:(2^J=8*2^(J-3))%nat).
  { replace J with (3+(J-3))%nat at 1 by lia; rewrite Nat.pow_add_r; reflexivity. }
  assert (Bound:(1+n*4<2^J)%nat) by (rewrite Pow in *; cbn[Nat.add Nat.pow] in Upper; nia).
  destruct (Digits_ex J (1+n*4)%nat Bound) as [ds' D'].
  assert (Low':exists w,ds'=W1::W0::w) by (apply (Digits_low01 _ _ _ D'); lia).
  pose proof (Digits_zeros _ _ _ D') as Def.
  pose proof (Scan_budget _ _ _ _ _ _ I) as Budget.
  change (2==(qnat (n*8)%nat-2)*scale v+2*(a-b)) in Budget.
  rewrite qnat_mul in Budget; change (qnat 8%nat) with 8 in Budget.
  rewrite qnat_add,qnat_mul in Def;
    change (qnat 1%nat) with 1 in Def; change (qnat 4%nat) with 4 in Def.
  assert (Deficit:scale v*zeros ds'==a-b-3*scale v).
  { clear -Def Budget Unit; nra. }
  assert (PhiNew:3*mass (WT::v)+zeros (WT::v)+scale (WT::v)*zeros ds'
      <=(7#8)*(3*mass u+zeros u+scale u*zeros ds)).
  { pose proof (scale_pos v) as Sv; pose proof (mass_split v) as Split.
    cbn[mass zeros scale]; clear -Deficit Mass Energy Wu Su Wd Sv Split; nra. }
  assert (High':exists w,ds'=w++repeat W1 6).
  { eapply Digits_high6; [apply D'|apply scale_pos|apply Unit| |].
    - destruct Low' as [w ->]; cbn[zeros]; pose proof (weights_nonneg w); lra.
    - pose proof (Scan_bounds _ _ _ _ _ _ I) as Bnd; pose proof (scale_pos v) as Sv.
      clear -Deficit Ap Phi Bnd Sv Wu; nra. }
  exists (WT::(v++ds')); split.
  - apply (Step_intro (u++ds) (n*4)%nat v a b J ds'); [|apply D'].
    rewrite <-app_assoc; replace ((n*4)*2)%nat with (n*8)%nat by lia; apply I.
  - change (Good ((WT::v)++ds')); apply (Good_intro J (WT::v) _ _ D').
    + cbn[scale]; clear -Unit; nra.
    + apply GuardV.
    + exists (WT::(last++[WT;WT])); rewrite V; cbn[app]; rewrite <-app_assoc; reflexivity.
    + apply Low'.
    + apply High'.
    + lra.
Qed.

Local Open Scope nat_scope.
Lemma Scan_spec a u b v lp lm : Scan a u b v lp lm -> forall r r',
  RIncs b r r' -> RIncs a (to_side u r) (to_side v r').
Proof.
  intro I; induction I; intros; cbn[to_side];
    eauto using RIncs_T, RIncs_pair0, RIncs_pair1,
      RIncs_short00, RIncs_short01, RIncs_short10, RIncs_short11.
Qed.

Lemma Digits_RIncs A H da : Digits A H da -> 0<A ->
  RIncs ((A-1)*2) 0inf (to_side da 0inf).
Proof.
  intro D; induction D; intro Pos; [lia| |].
  - cbn[to_side]; do 2 rewrite (const_unfold _ S0) at 1.
    applys_eq (RIncs_short00 (A-1)); flia; apply IHD; lia.
  - destruct A as [|A].
    + cbn[to_side Nat.sub Nat.mul]; rewrite (PCore.Digits_zero_side _ _ _ D eq_refl).
      change (RIncs 0 0inf (S1>>S0>>0inf)); rewrite <-const_unfold; constructor.
    + cbn[to_side]; do 2 rewrite (const_unfold _ S0) at 1.
      applys_eq (RIncs_short10 A); flia; applys_eq IHD; flia.
Qed.

Lemma Step_RIncs orig out : Step orig out -> exists r,
  RIncs 4 (to_side orig 0inf) r /\ to_side out 0inf=t*>r.
Proof.
  intro S; destruct S as [orig n v a b J ds I D].
  exists (to_side v (to_side ds 0inf)); split.
  - assert (B:RIncs (n*2) 0inf (to_side ds 0inf)).
    { replace (n*2) with ((1+n-1)*2) by lia; apply (Digits_RIncs _ _ _ D); lia. }
    pose proof (Scan_spec _ _ _ _ _ _ I _ _ B) as R.
    rewrite !to_side_app in R; cbn[to_side] in R.
    change (d0*>0inf) with (S0>>S0>>0inf) in R.
    rewrite <-!const_unfold in R.
    applys_eq R; flia.
  - cbn[to_side]; rewrite to_side_app; reflexivity.
Qed.


Local Open Scope nat_scope.
Fixpoint scanN u k acc {struct u} : option (N*list Word) :=
  match u with
  | [] => Some (k,rev_append acc [])
  | w::u => match k with
    | N0 => None
    | Npos p => match w with
      | WT => scanN u (N.double (N.pred k)) (WT::acc)
      | W0 => match shortN false k with
        | Some(d,k') => scanN u k' (d::acc) | None => None end
      | W1 => if match p with xO _ => singleN (W1::u) | _ => false end then
          match shortN true k with
          | Some(d,k') => scanN u k' (d::acc) | None => None end
        else match u with
          | W0::v => scanN v (N.double (N.pred k)) (WT::acc)
          | W1::v => scanN v (N.succ_double (N.pred k)) (WT::acc)
          | _ => None end
      end
    end
  end.

Lemma Scan_TN k u k' v a b : (1<=k)%N ->
  Scan (N.to_nat (N.double (N.pred k))) u k' v a b ->
  exists c d, Scan (N.to_nat k) (WT::u) k' (WT::v) c d.
Proof.
  intros K I; exists (a*(1#2))%Q, (b*(1#2))%Q.
  rewrite N2Nat.inj_double, N2Nat.inj_pred in I; cbn[N.to_nat] in I.
  assert (1<=N.to_nat k) by lia.
  applys_eq (Scan_T (N.to_nat k-1)); flia; applys_eq I; flia.
Qed.

Lemma Scan_pairN e p u k' v a b :
  Scan (N.to_nat (digitN e (N.pred (Npos p)))) u k' v a b ->
  exists c d, Scan (Pos.to_nat p) (W1::digitW e::u) k' (WT::v) c d.
Proof.
  destruct e; cbn[digitN digitW]; intro I;
    rewrite ?N2Nat.inj_succ_double, ?N2Nat.inj_double, N2Nat.inj_pred in I;
    cbn[N.to_nat] in I; pose proof (Pos2Nat.is_pos p).
  - eexists _, _; applys_eq (Scan_pair1 (Pos.to_nat p-1)); flia; applys_eq I; flia.
  - eexists _, _; applys_eq (Scan_pair0 (Pos.to_nat p-1)); flia; applys_eq I; flia.
Qed.

Lemma Scan_shortN e k d k' u c v a b : shortN e k=Some(d,k') ->
  Scan (N.to_nat k') u c v a b ->
  exists x y, Scan (N.to_nat k) (digitW e::u) c (d::v) x y.
Proof.
  destruct k as [|[p|p|]]; try discriminate.
  destruct p as [p|p|]; cbn[shortN]; intro E; inversion E; subst d k';
    destruct e; cbn[digitW digitN]; intro I;
    rewrite ?N2Nat.inj_succ_double, ?N2Nat.inj_double, ?N2Nat.inj_pred in I;
    cbn[N.to_nat] in *; rewrite ?Pos2Nat.inj_xO, ?Pos2Nat.inj_xI;
    try pose proof (Pos2Nat.is_pos p).
  all: eexists _, _;
    first [solve [applys_eq (Scan_short00 (Pos.to_nat p)); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short01 (Pos.to_nat p)); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short10 (Nat.pred (Pos.to_nat p))); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short11 (Nat.pred (Pos.to_nat p))); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short00 0); flia; applys_eq I; flia]
          |solve [applys_eq (Scan_short01 0); flia; applys_eq I; flia]].
Qed.

Lemma scanN_spec : forall u k acc k' out, scanN u k acc=Some(k',out) ->
  exists v a b, out=rev_append acc v /\ Scan (N.to_nat k) u (N.to_nat k') v a b.
Proof.
  fix IH 1; intros u k acc k' out E; destruct u as [|w u].
  - inversion E; exists (@nil Word), 0%Q, 0%Q; split; [reflexivity|constructor].
  - destruct k as [|p]; [discriminate|]; destruct w; cbn[scanN] in E.
    + assert (K:(1<=Npos p)%N) by lia.
      destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
      destruct (Scan_TN _ _ _ _ _ _ K I) as [c [d S]].
      exists (WT::v), c, d; auto.
    + destruct (shortN false (Npos p)) as [[d m]|] eqn:C; [|discriminate].
      destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
      destruct (Scan_shortN _ _ _ _ _ _ _ _ _ C I) as [x [y S]].
      exists (d::v), x, y; auto.
    + destruct (match p with xO _ => singleN (W1::u) | _ => false end).
      * destruct (shortN true (Npos p)) as [[d m]|] eqn:C; [|discriminate].
        destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
        destruct (Scan_shortN _ _ _ _ _ _ _ _ _ C I) as [x [y S]].
        exists (d::v), x, y; auto.
      * destruct u as [|w u]; [discriminate|]; destruct w; [discriminate| |].
        all: destruct (IH _ _ _ _ _ E) as [v [a [b [V I]]]].
        -- destruct (Scan_pairN false _ _ _ _ _ _ I) as [c [d S]]; exists (WT::v), c, d; auto.
        -- destruct (Scan_pairN true _ _ _ _ _ _ I) as [c [d S]]; exists (WT::v), c, d; auto.
Qed.


Definition round u :=
  match scanN (u++[W0]) 4%N [] with
  | Some(N0,v) => Some(WT::(v++[W1]))
  | Some(Npos(xO n),v) => Some(WT::(v++pwords (Pos.succ n)))
  | _ => None end.

Lemma round_spec u out : round u=Some out -> Step u out.
Proof.
  unfold round; destruct (scanN (u++[W0]) 4 []) as [[k v]|] eqn:I; [|discriminate].
  destruct (scanN_spec _ _ _ _ _ I) as [w [a [b [W S]]]]; cbn[rev_append] in W; subst w.
  destruct k as [|[n|n|]]; try discriminate; intro Eq; inversion Eq; subst out.
  - apply (Step_intro u 0 v a b 1 [W1]); [apply S|].
    exact (Digits_one 0 0 _ Digits_nil).
  - destruct (pwords_Digits (Pos.succ n)) as [J D]; rewrite Pos2Nat.inj_succ in D.
    change (Scan 4 (u++[W0]) (Pos.to_nat (xO n)) v a b) in S.
    rewrite Pos2Nat.inj_xO in S.
    apply (Step_intro u (Pos.to_nat n) v a b J); [applys_eq S; flia|applys_eq D; flia].
Qed.

Fixpoint guard_run u := match u with
  | WT::u => guard_run u | W0::_ => true | _ => false end.
Definition guard_check u := match u with WT::u=>guard_run u | _=>false end.

Lemma guard_run_spec u : guard_run u=true -> exists p w,u=repeat WT p++W0::w.
Proof.
  induction u as [|[] u IH]; try discriminate; intro E.
  - destruct (IH E) as [p [w ->]]; exists (S p),w; reflexivity.
  - exists 0,u; reflexivity.
Qed.

Lemma guard_check_spec u : guard_check u=true -> Guard u.
Proof.
  destruct u as [|[] u]; try discriminate; cbn[guard_check]; intro E.
  destruct (guard_run_spec _ E) as [p [w ->]]; exists p,w; reflexivity.
Qed.

Definition check orig :=
  match tail_cut orig with Some(u,ds) =>
    match heightN u 0 with Some H =>
      if Nat.eqb H (1+length ds) then if guard_check u then
        if match ds with W1::W0::_=>true | _=>false end then
          match strip_words (repeat W1 6) (rev_append ds []) with
          | Some _ => Qle_bool (3*mass u+zeros u+scale u*zeros ds) (1#64)
          | _=>false end
        else false
      else false else false
    | _=>false end
  | _=>false end.

Lemma check_spec orig : check orig=true -> Good orig.
Proof.
  unfold check; destruct (tail_cut orig) as [[u ds]|] eqn:Cut; [|discriminate].
  destruct (heightN u 0) as [H|] eqn:Height; [|discriminate].
  destruct (Nat.eqb H (1+length ds)) eqn:Width; [apply Nat.eqb_eq in Width|discriminate].
  destruct (guard_check u) eqn:Gu; [apply guard_check_spec in Gu|discriminate].
  destruct (match ds with W1::W0::_=>true | _=>false end) eqn:Lo; [|discriminate].
  destruct (strip_words (repeat W1 6) (rev_append ds [])) as [hi|] eqn:High; [|discriminate].
  assert (Low:exists w,ds=W1::W0::w).
  { destruct ds as [|[] [|[] w]]; try discriminate; eauto. }
  intro Phi; destruct Low as [lo L]; rewrite L in Phi; apply Qle_bool_imp_le in Phi.
  destruct (tail_cut_spec _ _ _ Cut) as [Orig Dig].
  destruct (digit_list _ Dig) as [A D].
  pose proof (heightN_spec _ _ _ Height) as Unit; rewrite Width in Unit.
  cbn[Nat.add Nat.pow] in Unit; rewrite qnat_mul in Unit;
    change (qnat 2%nat) with 2%Q in Unit; change (qnat 1%nat) with 1%Q in Unit.
  apply reverse_prefix in High; rewrite rev_append_rev in High.
  change (rev (repeat W1 6)) with (repeat W1 6) in High.
  rewrite Orig; apply (Good_intro (length ds) u A ds D).
  - clear -Unit; nra.
  - apply Gu.
  - eapply tail_cut_end,Cut.
  - eauto.
  - eauto.
  - rewrite L; apply Phi.
Qed.

Inductive Rounds : list Word -> list Word -> Prop :=
| Rounds_refl u : Rounds u u
| Rounds_next u v w : Step u v -> Rounds v w -> Rounds u w.

Fixpoint verify n u := match n with
  | O=>check u
  | S n=>match round u with Some v=>verify n v | _=>false end
  end.

Lemma verify_spec n : forall u,verify n u=true -> exists v,Rounds u v /\ Good v.
Proof.
  induction n; intros u E.
  - exists u; split; [constructor|apply check_spec,E].
  - cbn[verify] in E; destruct (round u) as [v|] eqn:R; [|discriminate].
    destruct (IHn _ E) as [w [Run G]]; exists w;
      split; [eapply Rounds_next; [apply round_spec,R|apply Run]|apply G].
Qed.

Definition start0 : list Word := [].
Definition start1 := [WT;WT;WT;W0;W1;WT].
Lemma check0 : verify 11 start0=true.
Proof. vm_compute; reflexivity. Qed.
Lemma check1 : verify 8 start1=true.
Proof. vm_compute; reflexivity. Qed.

Lemma entry_nonhalt tm C n u :
  (forall orig out,Step orig out -> C orig -[tm]->+ C out) ->
  c0 -[tm]->* C u -> verify n u=true -> ~halts tm c0.
Proof.
  intros BS Init Check; destruct (verify_spec _ _ Check) as [v [R G]].
  assert (Run:C u -[tm]->* C v).
  { clear - BS R; induction R;
      [constructor|eapply evstep_trans; [apply progress_evstep,BS,H|apply IHR]]. }
  eapply multistep_nonhalt; [apply Init|].
  eapply multistep_nonhalt; [apply Run|].
  eapply progress_nonhalt_cond with (P:=Good).
  - intros w Gw; destruct (Good_next _ Gw) as [out [StepW G']].
    exists out; split; [apply BS,StepW|apply G'].
  - apply G.
Qed.


Section Soundness.
Variable tm : TM.
Variables h j p : list (DH0*DH0).
Hypothesis T_one : segRLs tm p [] t (t++one).
Hypothesis T_odd : forall n,segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) t t.
Hypothesis T_even : forall n,segRLs tm (j++h^^n) (j++h^^(n*2)) t t.
Hypothesis Pair_00 : segRLs tm p [] (d1++d0) (t++one).

Hypothesis Pair_01 : forall n,
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.

Hypothesis Pair_02 : forall n,
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.

Hypothesis Pair_11 : forall n,
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.

Hypothesis Pair_12 : forall n,
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.

Hypothesis Short_00 : segRLs tm j [] d0 (d0++one).

Hypothesis Short_01 : forall n,
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.

Hypothesis Short_02 : forall n,
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.

Hypothesis Short_10 : segRLs tm (j++h) [] d0 (d1++one).

Hypothesis Short_11 : forall n,
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.

Hypothesis Short_12 : forall n,
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.


Lemma Counter_T n r r' : Counter tm h j p (n*2) r r' ->
  Counter tm h j p (1+n) (t*>r) (t*>r').
Proof.
  intros I w hs N; inversion N as [|m|m]; subst; try lia.
  - destruct m as [|m].
    + apply CCore.Counter_zero in I; subst r'.
      cbn[lpow Nat.add Nat.mul]; rewrite app_nil_r.
      eapply (segRLs_sideRLs_concat T_one); constructor.
    + eapply (segRLs_sideRLs_concat (T_odd m)).
      apply (I []); applys_eq (@Num2 h j p (1+m*2)); flia.
  - eapply (segRLs_sideRLs_concat (T_even m)).
    apply (I []); applys_eq (@Num2 h j p (m*2)); flia.
Qed.

Lemma RIncs_spec k r r' : RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; induction I; eauto using Counter_T, CCore.Counter_pair0, CCore.Counter_pair1,
    CCore.Counter_short00, CCore.Counter_short01, CCore.Counter_short10, CCore.Counter_short11.
  intros w hs N; inverts N; try lia; constructor.
Qed.
End Soundness.

End BCore.

Module TM0.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (C,[S0]).
Notation hR := (B,[S1]).
Notation h := [(hR,hL)].
Notation j := [((A,[S1;S1]),hL)].
Notation p := [((A,[S1;S0]),hL)].
Notation aR := (A,<[S1;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_one : segRLs tm p [] t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) t t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma T_even n : segRLs tm (j++h^^n) (j++h^^(n*2)) t t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.


Lemma RIncs_sound k r r' : BCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply BCore.RIncs_spec;
    eauto using T_one,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12.
Qed.

Lemma RSend : segRLs tm a (j++h) [] t.
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (aR,R) }}} r.

Lemma BigStep r r' : BCore.RIncs 4 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I; unfold Config.
  eapply @sideRLs_concat_v2 with (ls:=[(hL,aR)]).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 1).
Qed.

Lemma Step_sound orig out : BCore.Step orig out ->
  Config (to_side orig 0inf) -->+ Config (to_side out 0inf).
Proof.
  intro S; destruct (BCore.Step_RIncs _ _ S) as [r [I ->]]; apply BigStep,I.
Qed.

Lemma init : c0 -->* Config (to_side BCore.start0 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply BCore.entry_nonhalt; [apply Step_sound|apply init|apply BCore.check0]. Qed.

End TM0.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RA0RE_1RD1RF_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation hL := (B,[S0]).
Notation hR := (A,[S1]).
Notation h := [(hR,hL)].
Notation j := [((D,[S1;S1]),hL)].
Notation p := [((D,[S1;S0]),hL)].
Notation aR := (D,<[S1;S1;S0;S1;S1;S1]).
Notation a := [(aR,hL)].
Notation lh := (0inf<*<[S1;S0;S1]).

Tactic Notation "am" constr(s1) constr(s2) constr(a) constr(a')
  constr(n) constr(b) constr(b') :=
  applys_eq (segRLs_phase_addmul tm h s1 s2 a a' n b b');
  unfold DH0; flia; esc.

Lemma T_one : segRLs tm p [] t (t++one).
Proof. esc. Qed.
Lemma T_odd n : segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) t t.
Proof. am (p) (j) 1 2 n 1 1. Qed.
Lemma T_even n : segRLs tm (j++h^^n) (j++h^^(n*2)) t t.
Proof. am (j) (j) 1 2 n 0 0. Qed.
Lemma Pair_00 : segRLs tm p [] (d1++d0) (t++one).
Proof. esc. Qed.

Lemma Pair_01 n :
  segRLs tm (p++h^^(1+n)) (j++h^^(1+n*2)) (d1++d0) t.
Proof. am (p) (j) 1 2 n 1 1. Qed.

Lemma Pair_02 n :
  segRLs tm (j++h^^n) (j++h^^(n*2)) (d1++d0) t.
Proof. am (j) (j) 1 2 n 0 0. Qed.

Lemma Pair_11 n :
  segRLs tm (p++h^^n) (p++h^^(n*2)) (d1++d1) t.
Proof. am (p) (p) 1 2 n 0 0. Qed.

Lemma Pair_12 n :
  segRLs tm (j++h^^n) (p++h^^(1+n*2)) (d1++d1) t.
Proof. am (j) (p) 1 2 n 0 1. Qed.

Lemma Short_00 : segRLs tm j [] d0 (d0++one).
Proof. esc. Qed.

Lemma Short_01 n :
  segRLs tm (j++h^^(2+n*2)) (j++h^^n) d0 d0.
Proof. am (j) (j) 2 1 n 2 0. Qed.

Lemma Short_02 n :
  segRLs tm (j++h^^(n*2)) (p++h^^n) d1 d0.
Proof. am (j) (p) 2 1 n 0 0. Qed.

Lemma Short_10 : segRLs tm (j++h) [] d0 (d1++one).
Proof. esc. Qed.

Lemma Short_11 n :
  segRLs tm (j++h^^(3+n*2)) (j++h^^n) d0 d1.
Proof. am (j) (j) 2 1 n 3 0. Qed.

Lemma Short_12 n :
  segRLs tm (j++h^^(1+n*2)) (p++h^^n) d1 d1.
Proof. am (j) (p) 2 1 n 1 0. Qed.


Lemma RIncs_sound k r r' : BCore.RIncs k r r' -> Counter tm h j p k r r'.
Proof.
  intro I; eapply BCore.RIncs_spec;
    eauto using T_one,T_odd,T_even,Pair_00,Pair_01,Pair_02,Pair_11,Pair_12,
      Short_00,Short_01,Short_02,Short_10,Short_11,Short_12.
Qed.

Lemma RSend : segRLs tm a (j++h) [] t.
Proof. esc. Qed.
Lemma LSend : sideRLs (flip tm) [(hL,aR)] lh lh.
Proof. apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity. Qed.

Definition Config r := lh {{{ (aR,R) }}} r.

Lemma BigStep r r' : BCore.RIncs 4 r r' -> Config r -->+ Config (t*>r').
Proof.
  intro I; apply RIncs_sound in I; unfold Config.
  eapply @sideRLs_concat_v2 with (ls:=[(hL,aR)]).
  - reflexivity.
  - discriminate.
  - apply LSend.
  - eapply (segRLs_sideRLs_concat RSend).
    apply (I []); apply (@Num2 h j p 1).
Qed.

Lemma Step_sound orig out : BCore.Step orig out ->
  Config (to_side orig 0inf) -->+ Config (to_side out 0inf).
Proof.
  intro S; destruct (BCore.Step_RIncs _ _ S) as [r [I ->]]; apply BigStep,I.
Qed.

Lemma init : c0 -->* Config (to_side BCore.start1 0inf).
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply BCore.entry_nonhalt; [apply Step_sound|apply init|apply BCore.check1]. Qed.

End TM1.
