(* OTHERS_29_20261020.txt, TM12; original machine, not a state permutation.
   The auxiliary H signal includes one d2 block in its return head.  This
   turns the informal tail-of-G operation into an ordinary sideRLs call.
   Safe has three arithmetic boundary cases; SafeWrap retains the fixed
   columns and their exact input/output stream phases. *)
From BusyCoq Require Import Individual62 Longitudinal ES_v3.
Require Import ZifyNat Lia ZArith String List.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation hL := (A,[0;0;0]).
Notation hF := (E,<[1;1;1]).
Notation hG := (F,<[1;1;1;1;0;1]).
Notation d1 := [0;1;0;1].
Notation d2 := [0;0;1;0;1].
Notation d3 := [0;0;0;1;0;1].
Notation d4 := [1;0;1].
Notation hf := [(hF,hL)].
Notation hg := [(hG,hL)].
Notation hh := [(hG,(A,[0;0;0]++d2))].
Notation wall := (0inf <* <[1;0]).
Notation col := (d2^^3++d4).
Definition cycle := hg++hf^^2.
Definition stream p q := hf^^q++hh++hf^^p.

Local Ltac finite_rule :=
  apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.

Lemma F2: segRLs tm hf hf d2 d2.
Proof. finite_rule. Qed.
Lemma H2: segRLs tm hh hf d2 d4.
Proof. finite_rule. Qed.
Lemma F0: segRLs tm hf hh d4 d2.
Proof. finite_rule. Qed.
Lemma binary_even: segRLs tm hf [] [0;0;0;0] d1.
Proof. finite_rule. Qed.
Lemma binary_odd: segRLs tm hf hf d1 [0;0;0;0].
Proof. finite_rule. Qed.
Lemma H9: segRLs tm hh [] ([0]^^9++d4) (d2^^2).
Proof. finite_rule. Qed.

Lemma column: segRLs tm cycle cycle col col.
Proof. finite_rule. Qed.
Lemma four_cycles:
  segRLs tm (cycle^^4) ((stream 6 0)^^3) d3 (col++d3).
Proof. finite_rule. Qed.

Inductive Num : nat -> side -> Prop :=
| Num0: Num 0 0inf
| Num1 n r: Num n r -> Num (1+n*2) (d1*>r)
| Num2 n r: Num (1+n) r -> Num (2+n*2) ([0;0;0;0]*>r).

Lemma Num_inc [n r]:
  Num n r -> exists r', Num (1+n) r' /\ sideRLs tm hf r r'.
Proof.
  intro H; induction H as [|n r H [r' [HN HR]]|n r H IH].
  - exists (d1*>0inf); split; [apply (Num1 0); constructor|].
    esx.
  - exists ([0;0;0;0]*>r'); split.
    + applys_eq (Num2 n r' HN); flia.
    + eapply segRLs_sideRLs_concat; [apply binary_odd|apply HR].
  - exists (d1*>r); split.
    + applys_eq (Num1 (1+n) r H); flia.
    + eapply segRLs_sideRLs_concat; [apply binary_even|constructor].
Qed.

Lemma Num_ex n: exists r, Num n r.
Proof.
  induction n as [|n [r H]].
  - exists 0inf; constructor.
  - destruct (Num_inc H) as [r' [HN HR]]; eauto.
Qed.

Lemma Num_unique [n r r']:
  Num n r -> Num n r' -> r=r'.
Proof.
  intro H; gen r'; induction H; intros r' H'; inverts H'; try lia.
  - reflexivity.
  - replace n0 with n in * by lia.
    f_equal; auto.
  - replace n0 with n in * by lia.
    f_equal; auto.
Qed.

Lemma Num_add m n r:
  Num n r -> exists r', Num (n+m) r' /\ sideRLs tm (hf^^m) r r'.
Proof.
  gen n r; induction m as [|m IH]; introv H.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (Num_inc H) as [r1 [HN HR]].
    destruct (IH _ _ HN) as [r2 [HN' HR']].
    exists r2; split.
    + applys_eq HN'; flia.
    + change (hf^^(S m)) with (hf++hf^^m).
      eapply sideRLs_trans; eauto.
Qed.

Lemma Num_H9 [k r]:
  Num (4+k*8) r ->
  exists r', Num k r' /\ sideRLs tm hh r (d2^^2*>r').
Proof.
  introv H.
  destruct (Num_ex k) as [r' HN].
  assert (I: Num (4+k*8) (([0;0;0;0]++[0;0;0;0]++d1)*>r')).
  { applys_eq (Num2 (1+k*4)); [flia|].
    applys_eq (Num2 (k*2)); [flia|].
    apply Num1,HN. }
  epose proof (Num_unique H I); subst r.
  exists r'; split; [apply HN|].
  eapply segRLs_sideRLs_concat; [apply H9|constructor].
Qed.

Lemma stream2 p q:
  segRLs tm (stream (1+p) q) (stream p (q+1)) d2 d2.
Proof.
  unfold stream; repeat rewrite lpow_add.
  applys_eq (@segRLs_trans tm (hf^^q) (hf^^q)
    (hh++hf++hf^^p) (hf++hh++hf^^p) d2 d2 d2).
  all: try (cbn [lpow]; repeat rewrite <-app_assoc; reflexivity).
  - apply segRLs_wall'',F2.
  - eapply segRLs_trans; [apply H2|].
    eapply segRLs_trans; [apply F0|].
    apply segRLs_wall'',F2.
Qed.

Lemma stream0 p:
  segRLs tm (stream 0 (1+p)) (stream (1+p) 0) d4 d4.
Proof.
  unfold stream; repeat rewrite lpow_add.
  applys_eq (@segRLs_trans tm hf hh (hf^^p++hh) (hf^^p++hf) d4 d2 d4).
  all: try (cbn [lpow]; repeat rewrite <-app_assoc; try rewrite lpow_shift; reflexivity).
  - apply F0.
  - eapply segRLs_trans; [apply segRLs_wall'',F2|apply H2].
Qed.

Lemma stream22 p q:
  segRLs tm (stream (2+p) q) (stream p (q+2)) (d2^^2) (d2^^2).
Proof.
  applys_eq (@segRLs_concat tm (stream (2+p) q) (stream (1+p) (q+1))
    (stream p (q+1+1)) d2 d2 d2 d2); try flia.
  - apply stream2.
  - apply stream2.
Qed.

Lemma stream_end q:
  segRLs tm (stream 0 q) (hf^^(q+1)) d2 d4.
Proof.
  unfold stream; rewrite lpow_add.
  applys_eq (@segRLs_trans tm (hf^^q) (hf^^q) hh hf d2 d2 d4).
  all: try (cbn [lpow]; repeat rewrite app_nil_r; reflexivity).
  - apply segRLs_wall'',F2.
  - apply H2.
Qed.

Lemma normal_return [k p q r]:
  p+q=2+k*7 -> Num (2+k+p) r ->
  exists r', Num (k+p) r' /\ sideRLs tm (stream p q) r (d2^^2*>r').
Proof.
  introv E HN.
  destruct (Num_add q _ _ HN) as [rq [HQ IQ]].
  assert (HQ': Num (4+k*8) rq) by (applys_eq HQ; flia).
  destruct (Num_H9 HQ') as [rh [HH IH]].
  destruct (Num_add p _ _ HH) as [r' [HP IP]].
  exists r'; split; [apply HP|].
  unfold stream; eapply sideRLs_trans; [apply IQ|].
  eapply sideRLs_trans; [apply IH|].
  change (sideRLs tm (hf^^p) (d2*>d2*>rh) (d2*>d2*>r')).
  eapply segRLs_sideRLs_concat; [eapply segRLs_wall''; apply F2|].
  eapply segRLs_sideRLs_concat; [eapply segRLs_wall''; apply F2|apply IP].
Qed.

Inductive Safe (k:nat) : nat -> nat -> side -> Prop :=
| SafeNum p q r: p+q=2+k*7 -> Num (2+k+p) r -> Safe k p q r
| Safe0 r: Num k r -> Safe k 0 (2+k*7) (d2^^2*>r)
| Safe1 r: Num (1+k) r -> Safe k 0 (2+k*7) (d2*>r)
| SafeWrap p q p' q' w r:
    segRLs tm (stream p q) (stream p' q') w w ->
    Safe k p' q' r -> Safe k p q (w*>r).

Lemma Safe_step [k p q r]:
  Safe k p q r ->
  exists r', sideRLs tm (stream p q) r r' /\ Safe k p q r'.
Proof.
  intro H; induction H as [p q r E HN|r HN|r HN|p q p' q' w r HW HS IH].
  - destruct (normal_return E HN) as [r' [HN' HR]].
    exists (d2^^2*>r'); split; [apply HR|].
    destruct p as [|[|p]].
    + replace q with (2+k*7) by lia.
      apply Safe0; applys_eq HN'; flia.
    + change (Safe k 1 q (d2*>d2*>r')).
      eapply SafeWrap; [apply stream2|].
      replace (q+1) with (2+k*7) by lia.
      apply Safe1; applys_eq HN'; flia.
    + eapply SafeWrap; [apply stream22|].
      apply SafeNum; [lia|applys_eq HN'; flia].
  - destruct (Num_add (3+k*7) _ _ HN) as [r' [HN' HR]].
    exists (d4*>d2*>r'); split.
    + change (sideRLs tm (stream 0 (2+k*7)) (d2*>d2*>r) (d4*>d2*>r')).
      eapply segRLs_sideRLs_concat; [apply stream_end|].
      eapply segRLs_sideRLs_concat; [eapply segRLs_wall''; apply F2|].
      applys_eq HR; flia.
    + eapply SafeWrap; [apply stream0|].
      eapply SafeWrap; [apply stream2|].
      apply SafeNum; [lia|applys_eq HN'; flia].
  - destruct (Num_add (3+k*7) _ _ HN) as [r' [HN' HR]].
    exists (d4*>r'); split.
    + eapply segRLs_sideRLs_concat; [apply stream_end|].
      applys_eq HR; flia.
    + eapply SafeWrap; [apply stream0|].
      apply SafeNum; [lia|applys_eq HN'; flia].
  - destruct IH as [r' [HR HS']].
    exists (w*>r'); split.
    + eapply segRLs_sideRLs_concat; eauto.
    + eapply SafeWrap; eauto.
Qed.

Lemma Safe_steps n [k p q r]:
  Safe k p q r ->
  exists r', sideRLs tm ((stream p q)^^n) r r' /\ Safe k p q r'.
Proof.
  gen r; induction n as [|n IH]; introv H.
  - exists r; split; [constructor|apply H].
  - destruct (Safe_step H) as [r1 [HR HS]].
    destruct (IH _ HS) as [r2 [HR' HS']].
    exists r2; split; [|apply HS'].
    eapply sideRLs_trans; eauto.
Qed.

Lemma columns m n:
  segRLs tm (cycle^^n) (cycle^^n) (col^^m) (col^^m).
Proof.
  induction m; cbn [lpow].
  - apply segRLs_nil.
  - eapply segRLs_concat; [eapply segRLs_wall''; apply column|apply IHm].
Qed.

Notation left_cycle := [(hL,hF);(hL,hF);(hL,hG)].
Lemma left_wall: sideRLs (flip tm) left_cycle wall wall.
Proof. esx. Qed.

Definition Root m r := wall {{{(hG,R)}}} (col^^m*>d3*>r).

Lemma BigStep [k m r]:
  Safe k 6 0 r -> exists r',
  Root m r -->+ Root (1+m) r' /\ Safe k 6 0 r'.
Proof.
  introv H; destruct (Safe_steps 3 H) as [r' [HR HS]].
  exists r'; split; [|apply HS].
  unfold Root.
  eapply @sideRLs_concat_v2 with (ls:=left_cycle^^4).
  - reflexivity.
  - cbn; congruence.
  - apply sideRLs_wall,left_wall.
  - change (sideRLs tm (cycle^^4) (col^^m*>d3*>r) (col^^(1+m)*>d3*>r')).
    replace (col^^(1+m)*>d3*>r') with (col^^m*>(col++d3)*>r')
      by (repeat rewrite <-Str_app_assoc; f_equal;
          rewrite app_assoc,lpow_shift; reflexivity).
    eapply segRLs_sideRLs_concat; [apply columns|].
    eapply segRLs_sideRLs_concat; [apply four_cycles|apply HR].
Qed.

Lemma Num_double [n r]: Num n r -> Num (n*2) ([0;0;0;0]*>r).
Proof.
  introv H; destruct n.
  - inverts H; try lia.
    replace ([0;0;0;0]*>0inf) with 0inf by (st; reflexivity).
    constructor.
  - applys_eq (Num2 n r H); flia.
Qed.

Fixpoint binary p : list Sym :=
  match p with
  | xH => d1
  | xO p => [0;0;0;0]++binary p
  | xI p => d1++binary p
  end.

Lemma Num_binary p: Num (Pos.to_nat p) (binary p*>0inf).
Proof.
  induction p; cbn [binary]; rewrite ?Str_app_assoc.
  - rewrite Pos2Nat.inj_xI; applys_eq (Num1 _ _ IHp); flia.
  - rewrite Pos2Nat.inj_xO; applys_eq (Num_double IHp); flia.
  - apply (Num1 0); constructor.
Qed.

Definition prefix := concat (map (fun n => [0]^^n++d4)
  [2;2;3;2;1;2;3;3;2;3;6;2;3;6;2;2;3;2;1;2;3;3;3;0;2;3;
   2;2;2;2;3;3;3;3;2;1;2;2;1;2;2;2;3;3;3;2;2;3;2;1;2;2;2;
   2;2;3;2;2;3;2;2]%nat).

Lemma prefix_spec:
  segRLs tm (stream 6 0) (stream 62522 970) prefix prefix.
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=10^6).
  native_check_eq.
Qed.

Definition initial_right := prefix*>binary 71594*>0inf.

Lemma initial_safe: Safe 9070 6 0 initial_right.
Proof.
  unfold initial_right.
  eapply SafeWrap; [apply prefix_spec|].
  apply SafeNum; [reflexivity|].
  change (Num (Pos.to_nat 71594) (binary 71594*>0inf)).
  apply Num_binary.
Qed.

(* The small blocked iterator from Bouncer_v3; copied here because that
   library's existing .vo uses an older ES_v3.  No large unary step bound
   is materialized: all three fuel parameters are below 8500. *)
Fixpoint init_run n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm n3 c
  | S n1 =>
      match multistep_c tm n2 c with
      | Some c => init_run n1 n2 n3 c
      | None => None
      end
  end.

Lemma init_run_spec n1 n2 n3 c c':
  init_run n1 n2 n3 c=Some c' <-> c -[tm]->> (n1*n2+n3) / c'.
Proof.
  gen c c'; induction n1; cbn [init_run]; intros.
  - apply multistep_c_spec.
  - destruct (multistep_c tm n2 c) eqn:E.
    + apply multistep_c_spec in E.
      rewrite IHn1.
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      split; intro H.
      * eapply multistep_trans; eauto.
      * apply rewind_split in H; destruct H as [c'0 [I1 I2]].
        multistep_deterministic; eauto.
    + replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      split; [congruence|intro H].
      apply rewind_split in H; destruct H as [c'0 [I1 I2]].
      apply multistep_c_spec in I1; congruence.
Qed.

Lemma init: c0 -->* Root 16 initial_right.
Proof.
  eapply without_counter.
  eapply (proj1 (init_run_spec 8423 8424 7302 _ _)).
  native_check_eq.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with
    (C:=fun '(m,r) => Root m r) (P:=fun '(_,r) => Safe 9070 6 0 r)
    (i0:=(16,initial_right)).
  - intros [m r] H.
    destruct (BigStep (m:=m) H) as [r' [HR HS]].
    exists (1+m,r'); split; assumption.
  - apply initial_safe.
Qed.

End TM12.
