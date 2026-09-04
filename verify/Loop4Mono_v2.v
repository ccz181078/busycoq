From BusyCoq Require Import Individual62.

Require Import ZArith ZifyNat Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal ES_v3.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity).

Ltac es_v3_pre ::= ut.

(* A state renaming does not touch either tape or the remembered direction. *)
Definition rename_config (f:Q -> Q) (c:Q*tape) : Q*tape :=
  let '(q,t) := c in (f q,t).

Definition rename_transition (f:Q -> Q) (t:Sym * dir * Q)
  : Sym * dir * Q :=
  let '(w,d,q) := t in (w,d,f q).

Definition state_renaming (tm_new tm_old:TM) (f:Q -> Q) : Prop :=
  forall q s,
    tm_old (f q,s) = option_map (rename_transition f) (tm_new (q,s)).

Lemma rename_step tm_new tm_old f c c':
  state_renaming tm_new tm_old f ->
  c -[tm_new]-> c' ->
  rename_config f c -[tm_old]-> rename_config f c'.
Proof.
  intros Hrename Hstep.
  destruct Hstep as [q q' s s' l r Htrans|q q' s s' l r Htrans];
    cbn [rename_config]; constructor;
    rewrite Hrename,Htrans; reflexivity.
Qed.

Lemma rename_multistep tm_new tm_old f n c c':
  state_renaming tm_new tm_old f ->
  c -[tm_new]->> n / c' ->
  rename_config f c -[tm_old]->> n / rename_config f c'.
Proof.
  intros Hrename Hrun. induction Hrun.
  - constructor.
  - econstructor; [eapply rename_step; eassumption|exact IHHrun].
Qed.

Lemma rename_halted tm_new tm_old f c:
  state_renaming tm_new tm_old f ->
  halted tm_new c -> halted tm_old (rename_config f c).
Proof.
  destruct c as [q [[l s] r]]. cbn [halted rename_config].
  intros Hrename Hhalt. unfold state_renaming in Hrename.
  specialize (Hrename q s). rewrite Hhalt in Hrename.
  exact Hrename.
Qed.

Lemma rename_halts tm_new tm_old f c:
  state_renaming tm_new tm_old f ->
  halts tm_new c -> halts tm_old (rename_config f c).
Proof.
  intros Hrename [n [ch [Hrun Hhalt]]].
  exists n,(rename_config f ch). split.
  - eapply rename_multistep; eassumption.
  - eapply rename_halted; eassumption.
Qed.

Lemma rename_nonhalt tm_new tm_old f c:
  state_renaming tm_new tm_old f ->
  ~halts tm_old (rename_config f c) ->
  ~halts tm_new c.
Proof. intros Hrename Hnonhalt Hhalt. apply Hnonhalt.
  eapply rename_halts; eassumption.
Qed.
Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC---_1LD0RE_0LA1LD_1RC1RF_0RE1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition h1: list (DH0*DH0) := [((F,<[]),(D,[]));((E,<[]),(C,[0;0;1;1]))].
Definition h3: list (DH0*DH0) := [((F,<[]),(A,[0;1;1]))].

Definition D1 n := [0;1;1]++[0;0;1;1]^^n.
Definition D2 n := [1;1;1]++[0;0;1;1]^^n.
Definition D3 n := [1;1]++[0;0;1;1]^^n.

Lemma D1_Inc11 n:
  segRLs tm h1 h1 (D1 (1+n)) (D1 (1+n)).
Proof.
  unfold D1.
  esx.
Qed.

Lemma D1_Inc33 n:
  segRLs tm h3 h3 (D1 (1+n)) (D2 (1+n)).
Proof.
  unfold D1.
  esx.
Qed.

Lemma D3_Inc3 n:
  segRLs tm h3 [] (D3 (1+n)) (D1 n).
Proof.
  ut; esx.
Qed.

Lemma rh_Inc3:
  sideRLs tm h3 0inf 0inf.
Proof.
  esx.
Qed.

Lemma D1_Ov1 n m:
  sideRLs tm h1 (D1 (1+n) *> D1 0 *> D2 m *> 0inf) (D1 (3+n+m) *> 0inf).
Proof.
  es' n m.
Qed.

Lemma D1_Ov3 n n0 n1 r:
  sideRLs tm h3 (D1 (1+n) *> D1 0 *> D2 n0 *> D2 (1+n1) *> r) (D2 (3+n+n0) *> D3 n1 *> r).
Proof.
  es' n n0 n1 & r.
Qed.

Definition S' '(n,r) :=
  0inf <* <[1;1;0;1;1;1;1] <* <[0;1;0;1]^^(1+n) {{{ (F,[],R) }}} (r:side).

Lemma Inc1 n r r':
  sideRLs tm h1 r r' ->
  S' (n,r) -->+
  S' (2+n,r').
Proof.
  intros H.
  unfold S'.
  inverts H.
  inverts H6.
  inverts H7.
  follow10 H5.
  es; er.
  follow100 H4.
  es.
Qed.

Lemma Inc3 n n0 n1 r r':
  sideRLs tm h3 r (D2 (3+n0) *> D2 (2+n1) *> r') ->
  S' (n,r) -->+
  S' (3, D1 (3+n) *> D1 (2+n0) *> D1 n1 *> r').
Proof.
  unfold S',D2.
  intros H.
  eapply sideRLs_1 in H.
  follow10 H.
  es' n n0 n1 & r'.
Qed.

Lemma init:
  c0 -->*
  S' (3, D1 8 *> D1 5 *> D1 7 *> D2 6 *> 0inf).
Proof.
  esx.
Qed.

Lemma D1_Inc30:
  sideRLs tm h3 (D1 0 *> 0inf) (D2 0 *> 0inf).
Proof.
  esx.
Qed.

Lemma D1_Ov3_0 n n0:
  sideRLs tm h3
    (D1 (1+n) *> D1 0 *> D2 n0 *> D2 0 *> 0inf)
    (D2 (3+n+n0) *> 0inf).
Proof.
  es' n n0.
Qed.

Lemma D3_Inc30:
  sideRLs tm h3 (D3 0 *> 0inf) 0inf.
Proof.
  esx.
Qed.

Lemma h1_normal0 a b r:
  sideRLs tm h1
    (D1 (1+a) *> D2 (2+b) *> r)
    (D1 (2+a) *> D1 b *> r).
Proof.
  es' a b & r.
Qed.

Lemma h1_edge0 a:
  sideRLs tm h1
    (D1 (1+a) *> D2 0 *> 0inf)
    (D1 (2+a) *> 0inf).
Proof.
  es' a.
Qed.

Lemma h1_edge1 a:
  sideRLs tm h1
    (D1 (1+a) *> D2 1 *> 0inf)
    (D1 (2+a) *> 0inf).
Proof.
  es' a.
Qed.

Fixpoint D1s xs :=
  match xs with
  | [] => []
  | x::xs => D1 x ++ D1s xs
  end.

Fixpoint D2s xs :=
  match xs with
  | [] => []
  | x::xs => D2 x ++ D2s xs
  end.

Lemma D1s_Inc11 xs:
  Forall (fun x => 1 <= x) xs ->
  segRLs tm h1 h1 (D1s xs) (D1s xs).
Proof.
  intros H; induction H.
  1: apply segRLs_nil.
  cbn [D1s].
  replace x with (1+(x-1)) by lia.
  eapply segRLs_concat.
  1: apply D1_Inc11.
  exact IHForall.
Qed.

Lemma D1s_Inc33 xs:
  Forall (fun x => 1 <= x) xs ->
  segRLs tm h3 h3 (D1s xs) (D2s xs).
Proof.
  intros H; induction H.
  1: apply segRLs_nil.
  cbn [D1s D2s].
  replace x with (1+(x-1)) by lia.
  eapply segRLs_concat.
  1: apply D1_Inc33.
  exact IHForall.
Qed.

Lemma h1_prefix xs r r':
  Forall (fun x => 1 <= x) xs ->
  sideRLs tm h1 r r' ->
  sideRLs tm h1 (D1s xs *> r) (D1s xs *> r').
Proof.
  intros Hxs Hr.
  eapply segRLs_sideRLs_concat.
  1: apply D1s_Inc11; exact Hxs.
  exact Hr.
Qed.

Lemma h3_prefix xs r r':
  Forall (fun x => 1 <= x) xs ->
  sideRLs tm h3 r r' ->
  sideRLs tm h3 (D1s xs *> r) (D2s xs *> r').
Proof.
  intros Hxs Hr.
  eapply segRLs_sideRLs_concat.
  1: apply D1s_Inc33; exact Hxs.
  exact Hr.
Qed.

Lemma D3_side n r:
  sideRLs tm h3 (D3 (1+n) *> r) (D1 n *> r).
Proof.
  eapply segRLs_sideRLs_concat.
  1: apply D3_Inc3.
  constructor.
Qed.

Import ListNotations.
Inductive packet_type :=
| P2_1 | P4_2 | P5_3 | P9_4 | P9_5 | P12_5 | P12_6
| P17_7 | P17_8 | P18_8 | P20_10 | P25_11 | P25_12
| P26_11 | P26_12 | P27_12 | P41_20 | P42_21 | P43_20
| P44_20 | P52_25 | P68_32.

Definition packet_t (x:packet_type) : nat :=
  match x with
  | P2_1 => 2 | P4_2 => 4 | P5_3 => 5 | P9_4 => 9 | P9_5 => 9
  | P12_5 => 12 | P12_6 => 12 | P17_7 => 17 | P17_8 => 17
  | P18_8 => 18 | P20_10 => 20 | P25_11 => 25 | P25_12 => 25
  | P26_11 => 26 | P26_12 => 26 | P27_12 => 27 | P41_20 => 41
  | P42_21 => 42 | P43_20 => 43 | P44_20 => 44 | P52_25 => 52
  | P68_32 => 68
  end.

Definition packet_d (x:packet_type) : nat :=
  match x with
  | P2_1 => 1 | P4_2 => 2 | P5_3 => 3 | P9_4 => 4 | P9_5 => 5
  | P12_5 => 5 | P12_6 => 6 | P17_7 => 7 | P17_8 => 8
  | P18_8 => 8 | P20_10 => 10 | P25_11 => 11 | P25_12 => 12
  | P26_11 => 11 | P26_12 => 12 | P27_12 => 12 | P41_20 => 20
  | P42_21 => 21 | P43_20 => 20 | P44_20 => 20 | P52_25 => 25
  | P68_32 => 32
  end.

Definition packet_e (x:packet_type) : Z :=
  Z.of_nat (packet_t x) - 2 * Z.of_nat (packet_d x).

Local Open Scope Z_scope.
Definition packet_word (x:packet_type) : list Z :=
  match x with
  | P2_1 => [0;0]
  | P4_2 => [0;0;0;0]
  | P5_3 => [0;0;0;0;0]
  | P9_4 => [0;0;0;0;2;2;2;1;1]
  | P9_5 => [0;0;0;0;0;1;1;0;0]
  | P12_5 => [0;0;0;0;2;2;2;1;1;2;2;1]
  | P12_6 => [0;0;0;0;0;0;0;0;2;1;1;0]
  | P17_7 => [0;0;0;0;2;2;2;3;4;3;2;2;2;1;3;2;2]
  | P17_8 => [0;0;0;0;2;2;2;1;1;0;1;0;1;2;2;1;1]
  | P18_8 => [0;0;0;0;2;2;2;1;1;2;2;1;1;1;3;2;2;1]
  | P20_10 => [0;0;0;0;0;1;1;0;0;(-1)%Z;0;(-1)%Z;0;1;1;0;0;1;1;0]
  | P25_11 => [0;0;0;0;2;2;2;3;4;3;2;2;2;1;3;2;4;3;3;2;2;1;3;2;2]
  | P25_12 => [0;0;0;0;2;2;2;3;3;2;2;1;1;2;2;1;1;0;1;0;1;2;2;1;1]
  | P26_11 => [0;0;0;0;2;2;2;3;4;3;2;2;4;3;3;2;4;4;4;2;3;2;2;3;3;2]
  | P26_12 => [0;0;0;0;2;2;2;3;3;2;2;3;3;2;2;1;1;2;2;1;1;2;3;2;2;1]
  | P27_12 => [0;0;0;0;2;2;2;3;4;3;2;2;4;3;3;2;2;1;3;2;2;1;2;3;3;2;2]
  | P41_20 => [0;0;0;0;2;2;2;3;3;2;2;1;1;2;2;1;1;0;1;0;1;2;2;3;3;2;2;1;1;2;2;1;1;0;1;0;1;2;2;1;1]
  | P42_21 => [0;0;0;0;0;1;1;2;2;1;1;2;2;1;1;0;0;1;1;0;0;1;2;1;3;2;2;1;1;0;2;1;1;0;0;0;0;0;2;1;1;0]
  | P43_20 => [0;0;0;0;2;2;2;3;4;3;2;2;4;3;3;2;2;1;3;2;2;1;2;3;3;4;4;3;3;2;2;3;3;2;2;1;2;1;2;3;3;2;2]
  | P44_20 => [0;0;0;0;2;2;2;3;4;3;2;2;4;3;3;2;4;4;4;2;3;2;2;3;3;4;4;3;3;4;4;3;3;2;2;3;3;2;2;2;4;3;3;2]
  | P52_25 => [0;0;0;0;0;0;0;0;2;1;3;2;2;1;1;0;2;1;3;2;2;1;1;0;2;1;1;0;0;0;0;0;2;1;1;0;0;0;0;0;2;1;3;3;3;1;2;1;1;2;2;1]
  | P68_32 => [0;0;0;0;2;2;2;3;4;3;2;2;4;3;3;2;4;4;4;2;3;2;2;3;3;4;4;3;3;4;4;3;3;2;2;3;3;2;2;2;4;3;5;4;4;3;3;2;4;3;5;4;4;3;3;2;4;3;3;2;2;2;2;2;4;3;3;2]
  end.
Local Close Scope Z_scope.

Definition packet_tail (x:packet_type) : list packet_type :=
  match x with
  | P2_1 => []
  | P4_2 => [P4_2]
  | P5_3 => [P4_2;P2_1]
  | P9_4 => [P12_5]
  | P9_5 => [P12_6;P2_1]
  | P12_5 => [P18_8]
  | P12_6 => [P4_2;P4_2;P9_4;P2_1]
  | P17_7 => [P27_12]
  | P17_8 => [P12_5;P5_3;P9_4;P2_1]
  | P18_8 => [P18_8;P9_4;P2_1]
  | P20_10 => [P12_6;P2_1;P5_3;P17_8]
  | P25_11 => [P43_20]
  | P25_12 => [P17_7;P9_5;P2_1;P5_3;P9_4;P2_1]
  | P26_11 => [P44_20]
  | P26_12 => [P25_11;P20_10]
  | P27_12 => [P26_11;P9_5;P9_4;P2_1]
  | P41_20 => [P17_7;P9_5;P2_1;P5_3;P25_12;P2_1;P5_3;P9_4;P2_1]
  | P42_21 => [P52_25;P9_5;P2_1;P5_3;P9_4;P2_1]
  | P43_20 => [P26_11;P9_5;P25_12;P2_1;P5_3;P9_4;P2_1]
  | P44_20 => [P68_32;P9_4;P2_1]
  | P52_25 => [P4_2;P4_2;P41_20;P2_1;P5_3;P9_4;P2_1;P5_3;P26_12]
  | P68_32 => [P68_32;P41_20;P2_1;P5_3;P9_4;P2_1]
  end.

Definition packet_prod (p:bool) (x:packet_type) : list packet_type :=
  (if p then P5_3 else P4_2) :: packet_tail x.

Fixpoint phase_sum (xs:list packet_type) : Z :=
  match xs with
  | [] => 0
  | x::xs => packet_e x + phase_sum xs
  end.

Fixpoint packet_length (xs:list packet_type) : nat :=
  match xs with
  | [] => 0
  | x::xs => packet_t x + packet_length xs
  end.

Fixpoint packet_growth (xs:list packet_type) : nat :=
  match xs with
  | [] => 0
  | x::xs => packet_d x + packet_growth xs
  end.

Definition packet_next_parity (p:bool) (x:packet_type) : bool :=
  Nat.odd ((if p then 1 else 0) + packet_growth (packet_prod p x)).

Definition valid_packets (xs:list packet_type) : Prop :=
  xs <> [] /\ (phase_sum xs = 0%Z \/ phase_sum xs = 1%Z).

Fixpoint mapi_from {A B} (f:nat->A->B) (i:nat) (xs:list A) : list B :=
  match xs with
  | [] => []
  | x::xs => f i x :: mapi_from f (S i) xs
  end.

Definition baseline (j:nat) : nat := 2*j+3-(j mod 2).

Definition packet_parameter (offset:Z) (j:nat) (h:Z) : nat :=
  Z.to_nat (Z.of_nat (baseline j) + offset - 2*h).

Fixpoint packet_parameters_from
  (prefix_length:nat) (prefix_phase parity:Z) (xs:list packet_type)
  : list nat :=
  match xs with
  | [] => []
  | x::xs =>
      mapi_from
        (packet_parameter
          (2*Z.of_nat prefix_length-prefix_phase+parity))
        0 (packet_word x) ++
      packet_parameters_from
        (prefix_length+packet_t x) (prefix_phase+packet_e x) parity xs
  end.

Definition packet_parameters (xs:list packet_type) : list nat :=
  rev (packet_parameters_from 0 0 (phase_sum xs) xs).

Definition packet_side (xs:list packet_type) : side :=
  let k := packet_length xs in
  D1 (2*k+6) *> D1 (2*k+3) *> D1 (2*k+1) *>
  D2s (packet_parameters xs) *> 0inf.

Definition packet_config (xs:list packet_type) :=
  S' (3,packet_side xs).

Lemma packet_word_length x:
  length (packet_word x) = packet_t x.
Proof. destruct x; reflexivity. Qed.

Lemma packet_prod_nonempty p x:
  packet_prod p x <> [].
Proof. destruct p,x; discriminate. Qed.

Lemma packet_front_positive (p:bool) x:
  Forall (fun n => 3 <= n)
    (mapi_from
      (packet_parameter (if p then 1%Z else 0%Z)) 0 (packet_word x)).
Proof. destruct p,x; vm_compute; repeat constructor; lia. Qed.

Lemma D1s_app xs ys:
  D1s (xs++ys) = D1s xs ++ D1s ys.
Proof. induction xs; cbn; [reflexivity|rewrite IHxs,app_assoc; reflexivity]. Qed.

Lemma D2s_app xs ys:
  D2s (xs++ys) = D2s xs ++ D2s ys.
Proof. induction xs; cbn; [reflexivity|rewrite IHxs,app_assoc; reflexivity]. Qed.

Lemma nil_Str_app (r:side): [] *> r = r.
Proof. reflexivity. Qed.

Lemma h1_next xs a b r:
  Forall (fun x => 1 <= x) xs ->
  sideRLs tm h1
    (D1s xs *> D1 (1+a) *> D2 (2+b) *> r)
    (D1s xs *> D1 (2+a) *> D1 b *> r).
Proof. intros H; apply h1_prefix; [exact H|apply h1_normal0]. Qed.

Lemma Inc1_next n xs a b r:
  Forall (fun x => 1 <= x) xs ->
  S' (n,D1s xs *> D1 (1+a) *> D2 (2+b) *> r) -->+
  S' (2+n,D1s xs *> D1 (2+a) *> D1 b *> r).
Proof. intros H; apply Inc1,h1_next,H. Qed.

Lemma D1s_snoc_side xs z r:
  D1s (xs++[z]) *> r = D1s xs *> D1 z *> r.
Proof.
  rewrite D1s_app. cbn [D1s]. rewrite app_nil_r,Str_app_assoc. reflexivity.
Qed.

Lemma D1s_two_side xs z q r:
  D1s (xs++[z;q]) *> r = D1s xs *> D1 z *> D1 q *> r.
Proof.
  rewrite D1s_app. cbn [D1s].
  rewrite app_nil_r. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma Inc1_next_list n xs z q r:
  Forall (fun x => 1 <= x) xs -> 1 <= z -> 3 <= q ->
  S' (n,D1s (xs++[z]) *> D2 q *> r) -->+
  S' (2+n,D1s (xs++[z+1;q-2]) *> r).
Proof.
  intros Hxs Hz Hq.
  rewrite D1s_snoc_side,D1s_two_side.
  replace z with (1+(z-1)) at 1 by lia.
  replace q with (2+(q-2)) at 1 by lia.
  replace (z+1) with (2+(z-1)) by lia.
  apply Inc1_next; exact Hxs.
Qed.

Lemma finish_h3 n a b xs r r':
  3 <= a -> 2 <= b ->
  Forall (fun x => 1 <= x) xs ->
  sideRLs tm h3 r r' ->
  S' (n,D1 a *> D1 b *> D1s xs *> r) -->+
  S' (3,D1 (3+n) *> D1 (a-1) *> D1 (b-2) *> D2s xs *> r').
Proof.
  intros Ha Hb Hxs Hr.
  assert (Hside: sideRLs tm h3
    (D1s (a::b::xs) *> r) (D2s (a::b::xs) *> r')).
  { apply h3_prefix.
    - constructor; [lia|constructor; [lia|exact Hxs]].
    - exact Hr. }
  cbn [D1s D2s] in Hside.
  repeat rewrite Str_app_assoc in Hside.
  assert (Ea: a=3+(a-3)) by lia.
  assert (Eb: b=2+(b-2)) by lia.
  rewrite Ea,Eb in Hside |- *.
  replace (3+(a-3)-1) with (2+(a-3)) by lia.
  replace (2+(b-2)-2) with (b-2) by lia.
  eapply Inc3.
  exact Hside.
Qed.

Fixpoint scan_values (z:nat) (qs:list nat) : list nat :=
  match qs with
  | [] => [z]
  | q::qs => (z+1)::scan_values (q-2) qs
  end.

Lemma scan_values_positive z qs:
  1 <= z -> Forall (fun q => 3 <= q) qs ->
  Forall (fun x => 1 <= x) (scan_values z qs).
Proof.
  revert z; induction qs; intros z Hz Hq; inverts Hq; cbn.
  - constructor; [lia|constructor].
  - constructor; [lia|apply IHqs; [lia|assumption]].
Qed.

Lemma scan_h1 n xs z qs r:
  Forall (fun x => 1 <= x) xs -> 1 <= z ->
  Forall (fun q => 3 <= q) qs ->
  S' (n,D1s (xs++[z]) *> D2s qs *> r) -->*
  S' (n+2*length qs,D1s (xs++scan_values z qs) *> r).
Proof.
  intros Hxs Hz Hqs; revert n xs z Hxs Hz.
  induction Hqs; intros.
  - cbn [D2s scan_values List.length Nat.mul Nat.add].
    rewrite nil_Str_app,Nat.add_0_r.
    apply evstep_refl.
  - cbn [D2s scan_values length].
    assert (Hone:
      S' (n,D1s (xs++[z]) *> D2 x *> D2s l *> r) -->+
      S' (2+n,D1s (xs++[z+1;x-2]) *> D2s l *> r)).
    { apply Inc1_next_list; assumption. }
    pose proof (IHHqs (2+n) (xs++[z+1]) (x-2)) as Hrest.
    specialize (Hrest ltac:(apply Forall_app; split; [exact Hxs|repeat constructor; lia]) ltac:(lia)).
    repeat rewrite <-app_assoc in Hrest.
    repeat rewrite Str_app_assoc.
    eapply evstep_trans; [apply progress_evstep; exact Hone|].
    replace (n+2*S (length l)) with (2+n+2*length l) by lia.
    exact Hrest.
Qed.

Inductive reset_tail :=
| RTnone
| RTd1 (n:nat)
| RTd3 (n:nat).

Definition reset_tail_side (t:reset_tail) : side :=
  match t with
  | RTnone => 0inf
  | RTd1 n => D1 n *> 0inf
  | RTd3 n => D3 n *> 0inf
  end.

Definition reset_tail_extra (t:reset_tail) : list nat :=
  match t with
  | RTd1 n => [n]
  | _ => []
  end.

Definition reset_tail_next (t:reset_tail) : reset_tail :=
  match t with
  | RTd3 (S n) => RTd1 n
  | _ => RTnone
  end.

Lemma reset_tail_h3 t:
  sideRLs tm h3 (reset_tail_side t)
    (D2s (reset_tail_extra t) *> reset_tail_side (reset_tail_next t)).
Proof.
  destruct t as [|n|n]; cbn [reset_tail_side reset_tail_extra reset_tail_next].
  - rewrite nil_Str_app. exact rh_Inc3.
  - destruct n.
    + exact D1_Inc30.
    + cbn [D2s]. rewrite app_nil_r.
      eapply segRLs_sideRLs_concat; [apply D1_Inc33|exact rh_Inc3].
  - destruct n.
    + rewrite nil_Str_app. exact D3_Inc30.
    + rewrite nil_Str_app. apply D3_side.
Qed.

Lemma reset_positive a b c qs t:
  3 <= a -> 2 <= b -> 1 <= c ->
  Forall (fun q => 3 <= q) qs ->
  S' (3,D1 a *> D1 b *> D1 c *> D2s qs *> reset_tail_side t) -->+
  S' (3,
    D1 (2*length qs+6) *> D1 (a-1) *> D1 (b-2) *>
    D2s (scan_values c qs ++ reset_tail_extra t) *>
    reset_tail_side (reset_tail_next t)).
Proof.
  intros Ha Hb Hc Hqs.
  pose proof (scan_h1 3 [a;b] c qs (reset_tail_side t)) as Hscan.
  specialize (Hscan ltac:(repeat constructor; lia) Hc Hqs).
  repeat rewrite D1s_app in Hscan.
  cbn [D1s] in Hscan.
  repeat rewrite app_nil_r in Hscan.
  repeat rewrite Str_app_assoc in Hscan.
  pose proof (finish_h3 (3+2*length qs) a b (scan_values c qs)
    (reset_tail_side t)
    (D2s (reset_tail_extra t) *> reset_tail_side (reset_tail_next t))) as Hfinish.
  specialize (Hfinish Ha Hb ltac:(apply scan_values_positive; assumption)
    (reset_tail_h3 t)).
  rewrite D2s_app.
  repeat rewrite Str_app_assoc.
  eapply evstep_progress_trans; [exact Hscan|].
  replace (2*length qs+6) with (3+(3+2*length qs)) by lia.
  exact Hfinish.
Qed.

Lemma Inc1_edge n xs z e:
  Forall (fun x => 1 <= x) xs -> 1 <= z -> e <= 1 ->
  S' (n,D1s (xs++[z]) *> D2 e *> 0inf) -->+
  S' (n+2,D1s (xs++[z+1]) *> 0inf).
Proof.
  intros Hxs Hz He.
  repeat rewrite D1s_snoc_side.
  replace z with (1+(z-1)) at 1 by lia.
  replace (z+1) with (2+(z-1)) by lia.
  replace (n+2) with (2+n) by lia.
  apply Inc1,h1_prefix; [exact Hxs|].
  destruct e as [|[|e]]; [apply h1_edge0|apply h1_edge1|lia].
Qed.

Lemma Inc1_zero n xs z r:
  Forall (fun x => 1 <= x) xs -> 1 <= z ->
  S' (n,D1s (xs++[z]) *> D2 2 *> r) -->+
  S' (n+2,D1s (xs++[z+1;(0%nat)]) *> r).
Proof.
  intros Hxs Hz.
  rewrite D1s_snoc_side,D1s_two_side.
  replace z with (1+(z-1)) at 1 by lia.
  replace (z+1) with (2+(z-1)) by lia.
  replace (n+2) with (2+n) by lia.
  apply Inc1_next; exact Hxs.
Qed.

Lemma reset_edge n a b xs z e:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) xs ->
  1 <= z -> e <= 1 ->
  S' (n,D1 a *> D1 b *> D1s xs *> D1 z *> D2 e *> 0inf) -->+
  S' (3,D1 (n+5) *> D1 (a-1) *> D1 (b-2) *>
    D2s (xs++[z+1]) *> 0inf).
Proof.
  intros Ha Hb Hxs Hz He.
  pose proof (Inc1_edge n (a::b::xs) z e) as Hone.
  specialize (Hone ltac:(constructor; [lia|constructor; [lia|exact Hxs]]) Hz He).
  repeat rewrite D1s_app in Hone.
  cbn [D1s] in Hone. repeat rewrite nil_Str_app in Hone.
  repeat rewrite Str_app_assoc in Hone. repeat rewrite nil_Str_app in Hone.
  pose proof (finish_h3 (n+2) a b (xs++[z+1]) 0inf 0inf) as Hfinish.
  specialize (Hfinish Ha Hb ltac:(apply Forall_app; split;
    [exact Hxs|repeat constructor; lia]) rh_Inc3).
  repeat rewrite D1s_app in Hfinish. repeat rewrite D2s_app in Hfinish.
  cbn [D1s D2s] in Hfinish. repeat rewrite app_nil_r in Hfinish.
  repeat rewrite Str_app_assoc in Hfinish. repeat rewrite nil_Str_app in Hfinish.
  rewrite D2s_app. cbn [D2s]. rewrite app_nil_r.
  repeat rewrite Str_app_assoc.
  eapply progress_trans; [exact Hone|].
  replace (n+5) with (3+(n+2)) by lia. exact Hfinish.
Qed.

Lemma reset_two_last n a b xs z:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) xs -> 1 <= z ->
  S' (n,D1 a *> D1 b *> D1s xs *> D1 z *> D2 2 *> 0inf) -->+
  S' (3,D1 (n+5) *> D1 (a-1) *> D1 (b-2) *>
    D2s (xs++[z+1;(0%nat)]) *> 0inf).
Proof.
  intros Ha Hb Hxs Hz.
  pose proof (Inc1_zero n (a::b::xs) z 0inf) as Hone.
  specialize (Hone ltac:(constructor; [lia|constructor; [lia|exact Hxs]]) Hz).
  repeat rewrite D1s_app in Hone.
  cbn [D1s] in Hone. repeat rewrite nil_Str_app in Hone.
  repeat rewrite Str_app_assoc in Hone. repeat rewrite nil_Str_app in Hone.
  pose proof (finish_h3 (n+2) a b (xs++[z+1])
    (D1 0 *> 0inf) (D2 0 *> 0inf)) as Hfinish.
  specialize (Hfinish Ha Hb ltac:(apply Forall_app; split;
    [exact Hxs|repeat constructor; lia]) D1_Inc30).
  repeat rewrite D1s_app in Hfinish. repeat rewrite D2s_app in Hfinish.
  cbn [D1s D2s] in Hfinish. repeat rewrite app_nil_r in Hfinish.
  repeat rewrite Str_app_assoc in Hfinish. repeat rewrite nil_Str_app in Hfinish.
  rewrite D2s_app. cbn [D2s]. rewrite app_nil_r.
  repeat rewrite Str_app_assoc.
  eapply progress_trans; [exact Hone|].
  replace (n+5) with (3+(n+2)) by lia. exact Hfinish.
Qed.

Lemma reset_two_one n a b xs z m:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) xs -> 1 <= z ->
  S' (n,D1 a *> D1 b *> D1s xs *> D1 z *> D2 2 *> D2 m *> 0inf) -->+
  S' (3,D1 (n+7) *> D1 (a-1) *> D1 (b-2) *>
    D2s (xs++[z+m+3]) *> 0inf).
Proof.
  intros Ha Hb Hxs Hz.
  pose proof (Inc1_zero n (a::b::xs) z (D2 m *> 0inf)) as Hzero.
  specialize (Hzero ltac:(constructor; [lia|constructor; [lia|exact Hxs]]) Hz).
  repeat rewrite D1s_app in Hzero.
  cbn [D1s] in Hzero. repeat rewrite nil_Str_app in Hzero.
  repeat rewrite Str_app_assoc in Hzero. repeat rewrite nil_Str_app in Hzero.
  assert (Hmerge:
    S' (n+2,D1 a *> D1 b *> D1s xs *> D1 (z+1) *> D1 0 *> D2 m *> 0inf) -->+
    S' (n+4,D1 a *> D1 b *> D1s xs *> D1 (z+m+3) *> 0inf)).
  { assert (Hov: sideRLs tm h1
      (D1 (z+1) *> D1 0 *> D2 m *> 0inf)
      (D1 (z+m+3) *> 0inf)).
    { replace (z+1) with (1+z) by lia.
      replace (z+m+3) with (3+z+m) by lia.
      apply D1_Ov1. }
    pose proof (h1_prefix (a::b::xs)
      (D1 (z+1) *> D1 0 *> D2 m *> 0inf)
      (D1 (z+m+3) *> 0inf)
      ltac:(constructor; [lia|constructor; [lia|exact Hxs]]) Hov) as Hside.
    repeat rewrite D1s_app in Hside. cbn [D1s] in Hside.
    repeat rewrite Str_app_assoc in Hside. repeat rewrite nil_Str_app in Hside.
    replace (n+4) with (2+(n+2)) by lia. apply Inc1. exact Hside. }
  pose proof (finish_h3 (n+4) a b (xs++[z+m+3]) 0inf 0inf) as Hfinish.
  specialize (Hfinish Ha Hb ltac:(apply Forall_app; split;
    [exact Hxs|repeat constructor; lia]) rh_Inc3).
  repeat rewrite D1s_app in Hfinish. repeat rewrite D2s_app in Hfinish.
  cbn [D1s D2s] in Hfinish. repeat rewrite app_nil_r in Hfinish.
  repeat rewrite Str_app_assoc in Hfinish. repeat rewrite nil_Str_app in Hfinish.
  rewrite D2s_app. cbn [D2s]. rewrite app_nil_r.
  repeat rewrite Str_app_assoc.
  eapply progress_trans; [exact Hzero|].
  eapply progress_trans; [exact Hmerge|].
  replace (n+7) with (3+(n+4)) by lia. exact Hfinish.
Qed.

Definition boundary_tail (z:nat) : reset_tail :=
  match z with O => RTnone | S n => RTd3 n end.

Lemma reset_two_two n a b xs z m u:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) xs -> 1 <= z ->
  S' (n,D1 a *> D1 b *> D1s xs *> D1 z *>
    D2 2 *> D2 m *> D2 u *> 0inf) -->+
  S' (3,D1 (n+5) *> D1 (a-1) *> D1 (b-2) *>
    D2s (xs++[z+m+3]) *> reset_tail_side (boundary_tail u)).
Proof.
  intros Ha Hb Hxs Hz.
  pose proof (Inc1_zero n (a::b::xs) z (D2 m *> D2 u *> 0inf)) as Hzero.
  specialize (Hzero ltac:(constructor; [lia|constructor; [lia|exact Hxs]]) Hz).
  repeat rewrite D1s_app in Hzero.
  cbn [D1s] in Hzero. repeat rewrite nil_Str_app in Hzero.
  repeat rewrite Str_app_assoc in Hzero. repeat rewrite nil_Str_app in Hzero.
  pose proof (finish_h3 (n+2) a b xs
    (D1 (z+1) *> D1 0 *> D2 m *> D2 u *> 0inf)
    (D2 (z+m+3) *> reset_tail_side (boundary_tail u))) as Hfinish.
  specialize (Hfinish Ha Hb Hxs ltac:(destruct u; cbn [boundary_tail reset_tail_side];
    [replace (z+1) with (1+z) by lia;
     replace (z+m+3) with (3+z+m) by lia; apply D1_Ov3_0
    |replace (z+1) with (1+z) by lia;
     replace (z+m+3) with (3+z+m) by lia; apply D1_Ov3])).
  rewrite D2s_app. cbn [D2s]. rewrite app_nil_r.
  repeat rewrite Str_app_assoc.
  eapply progress_trans; [exact Hzero|].
  replace (n+5) with (3+(n+2)) by lia. exact Hfinish.
Qed.

Definition decs (xs:list nat) := map (fun x => x-1) xs.

Fixpoint last_down (xs:list nat) : list nat :=
  match xs with
  | [] => []
  | [x] => [x-2]
  | x::xs => (x-1)::last_down xs
  end.

Fixpoint last_add (d:nat) (xs:list nat) : list nat :=
  match xs with
  | [] => []
  | [x] => [x+d]
  | x::xs => x::last_add d xs
  end.

Lemma last_down_app xs ys:
  ys <> [] -> last_down (xs++ys) = decs xs ++ last_down ys.
Proof.
  intros Hys; induction xs as [|x xs IH]; [reflexivity|].
  destruct xs as [|y xs].
  - destruct ys; [contradiction|reflexivity].
  - change (((x-1)%nat :: last_down ((y::xs)++ys)) =
      ((x-1)%nat :: (decs (y::xs) ++ last_down ys))).
    f_equal. apply IH; assumption.
Qed.

Lemma last_add_app d xs ys:
  ys <> [] -> last_add d (xs++ys) = xs ++ last_add d ys.
Proof.
  intros Hys; induction xs as [|x xs IH]; [reflexivity|].
  destruct xs as [|y xs].
  - destruct ys; [contradiction|reflexivity].
  - change ((x :: last_add d ((y::xs)++ys)) =
      (x :: ((y::xs) ++ last_add d ys))).
    f_equal. apply IH; assumption.
Qed.

Lemma last_add_snoc d xs z:
  last_add d (xs++[z]) = xs++[z+d].
Proof. rewrite last_add_app; [reflexivity|discriminate]. Qed.

Lemma scan_values_cons c x xs:
  Forall (fun q => 2 <= q) (x::xs) ->
  scan_values c (x::xs) = (c+1)::last_down (x::xs).
Proof.
  revert c x; induction xs as [|y xs IH]; intros c x H; [reflexivity|].
  inverts H. inverts H3.
  change ((c+1)::scan_values (x-2) (y::xs) =
    (c+1)::(x-1)::last_down (y::xs)).
  rewrite IH by (constructor; assumption).
  replace (x-2+1) with (x-1) by lia. reflexivity.
Qed.

Lemma scan_values_app c xs ys:
  ys <> [] -> Forall (fun q => 2 <= q) (xs++ys) ->
  scan_values c (xs++ys) = (c+1)::decs xs++last_down ys.
Proof.
  intros Hys H. destruct (xs++ys) eqn:E; [apply app_eq_nil in E; tauto|].
  rewrite scan_values_cons,<-E,last_down_app by assumption. reflexivity.
Qed.

Lemma last_add_one_last_down xs:
  xs <> [] -> Forall (fun x => 3 <= x) xs ->
  last_add 1 (last_down xs) = decs xs.
Proof.
  intros Hne H. apply exists_last in Hne as (ys&z&->).
  rewrite last_down_app,last_add_app by discriminate.
  unfold decs. rewrite map_app. cbn [last_down last_add map].
  apply Forall_app in H as [_ Hz]. inverts Hz.
  replace (z-2+1) with (z-1) by lia. reflexivity.
Qed.

Lemma reset_edge_list n a b vs e:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) vs ->
  vs <> [] -> e <= 1 ->
  S' (n,D1 a *> D1 b *> D1s vs *> D2 e *> 0inf) -->+
  S' (3,D1 (n+5) *> D1 (a-1) *> D1 (b-2) *>
    D2s (last_add 1 vs) *> 0inf).
Proof.
  intros Ha Hb Hvs Hne He. apply exists_last in Hne as (xs&z&->).
  rewrite last_add_snoc.
  rewrite D1s_snoc_side.
  apply reset_edge; try assumption.
  apply Forall_app in Hvs as [Hxs Hz]. exact Hxs.
  apply Forall_app in Hvs as [Hxs Hz]. inverts Hz. assumption.
Qed.

Lemma reset_two_last_list n a b vs:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) vs -> vs <> [] ->
  S' (n,D1 a *> D1 b *> D1s vs *> D2 2 *> 0inf) -->+
  S' (3,D1 (n+5) *> D1 (a-1) *> D1 (b-2) *>
    D2s (last_add 1 vs++[0%nat]) *> 0inf).
Proof.
  intros Ha Hb Hvs Hne. apply exists_last in Hne as (xs&z&->).
  rewrite last_add_snoc.
  rewrite D1s_snoc_side.
  rewrite <-app_assoc. cbn [app].
  apply reset_two_last; try assumption.
  apply Forall_app in Hvs as [Hxs Hz]. exact Hxs.
  apply Forall_app in Hvs as [Hxs Hz]. inverts Hz. assumption.
Qed.

Lemma reset_two_one_list n a b vs m:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) vs -> vs <> [] ->
  S' (n,D1 a *> D1 b *> D1s vs *> D2 2 *> D2 m *> 0inf) -->+
  S' (3,D1 (n+7) *> D1 (a-1) *> D1 (b-2) *>
    D2s (last_add (m+3) vs) *> 0inf).
Proof.
  intros Ha Hb Hvs Hne. apply exists_last in Hne as (xs&z&->).
  rewrite last_add_snoc. replace (z+(m+3)) with (z+m+3) by lia.
  rewrite D1s_snoc_side.
  apply reset_two_one; try assumption.
  apply Forall_app in Hvs as [Hxs Hz]. exact Hxs.
  apply Forall_app in Hvs as [Hxs Hz]. inverts Hz. assumption.
Qed.

Lemma reset_two_two_list n a b vs m u:
  3 <= a -> 2 <= b -> Forall (fun x => 1 <= x) vs -> vs <> [] ->
  S' (n,D1 a *> D1 b *> D1s vs *> D2 2 *> D2 m *> D2 u *> 0inf) -->+
  S' (3,D1 (n+5) *> D1 (a-1) *> D1 (b-2) *>
    D2s (last_add (m+3) vs) *> reset_tail_side (boundary_tail u)).
Proof.
  intros Ha Hb Hvs Hne. apply exists_last in Hne as (xs&z&->).
  rewrite last_add_snoc. replace (z+(m+3)) with (z+m+3) by lia.
  rewrite D1s_snoc_side.
  apply reset_two_two; try assumption.
  apply Forall_app in Hvs as [Hxs Hz]. exact Hxs.
  apply Forall_app in Hvs as [Hxs Hz]. inverts Hz. assumption.
Qed.

Definition push_down c xs := (c+1)::decs xs.

Lemma decs_app xs ys: decs (xs++ys) = decs xs++decs ys.
Proof. unfold decs; apply map_app. Qed.

Lemma scan_values_nonempty c xs: scan_values c xs <> [].
Proof. destruct xs; discriminate. Qed.

Lemma scan_values_finish c xs:
  1 <= c -> Forall (fun x => 3 <= x) xs ->
  last_add 1 (scan_values c xs) = push_down c xs.
Proof.
  intros Hc Hxs. destruct xs as [|x xs].
  - reflexivity.
  - rewrite scan_values_cons by (eapply Forall_impl; [|exact Hxs]; cbn; lia).
    change (last_add 1 ([c+1]++last_down (x::xs)) = push_down c (x::xs)).
    rewrite last_add_app by (destruct xs; discriminate).
    change ((c+1)::last_add 1 (last_down (x::xs)) =
      (c+1)::decs (x::xs)). f_equal.
    apply last_add_one_last_down; [discriminate|exact Hxs].
Qed.

Lemma last_down_nonempty xs: xs <> [] -> last_down xs <> [].
Proof. destruct xs as [|x xs]; [tauto|destruct xs; discriminate]. Qed.

Lemma last_add_push d c ctx ps:
  ps <> [] ->
  last_add d ((c+1)::(decs ctx++last_down ps)) =
  (c+1)::(decs ctx++last_add d (last_down ps)).
Proof.
  intros Hps.
  change (last_add d (((c+1)::decs ctx)++last_down ps) =
    ((c+1)::decs ctx)++last_add d (last_down ps)).
  apply last_add_app,last_down_nonempty,Hps.
Qed.

Lemma frame_positive a b c ctx local t:
  3 <= a -> 2 <= b -> 1 <= c -> local <> [] ->
  Forall (fun x => 3 <= x) ctx -> Forall (fun x => 3 <= x) local ->
  S' (3,D1 a *> D1 b *> D1 c *> D2s (ctx++local) *> reset_tail_side t) -->+
  S' (3,
    D1 (2*(length ctx+length local)+6) *> D1 (a-1) *> D1 (b-2) *>
    D2s ((push_down c ctx++last_down local)++reset_tail_extra t) *>
    reset_tail_side (reset_tail_next t)).
Proof.
  intros Ha Hb Hc Hne Hctx Hlocal.
  pose proof (reset_positive a b c (ctx++local) t Ha Hb Hc) as H.
  specialize (H ltac:(apply Forall_app; tauto)).
  assert (Htwo: Forall (fun x => 2 <= x) (ctx++local)).
  { apply Forall_app; split.
    - eapply Forall_impl; [|exact Hctx]. cbn; lia.
    - eapply Forall_impl; [|exact Hlocal]. cbn; lia. }
  rewrite scan_values_app in H by assumption.
  unfold push_down in H |- *.
  repeat rewrite app_length in H. cbn [length] in H.
  exact H.
Qed.

Lemma frame_edge a b c ctx ps e:
  3 <= a -> 2 <= b -> 1 <= c -> e <= 1 ->
  Forall (fun x => 3 <= x) ctx -> Forall (fun x => 3 <= x) ps ->
  S' (3,D1 a *> D1 b *> D1 c *> D2s (ctx++ps++[e]) *> 0inf) -->+
  S' (3,
    D1 (2*(length ctx+length ps+1)+6) *> D1 (a-1) *> D1 (b-2) *>
    D2s (push_down c ctx++decs ps) *> 0inf).
Proof.
  intros Ha Hb Hc He Hctx Hps.
  pose proof (scan_h1 3 [a;b] c (ctx++ps) (D2 e *> 0inf)) as Hscan.
  specialize (Hscan ltac:(repeat constructor; lia) Hc
    ltac:(apply Forall_app; tauto)).
  pose proof (reset_edge_list (3+2*length (ctx++ps)) a b
    (scan_values c (ctx++ps)) e) as Hedge.
  specialize (Hedge Ha Hb ltac:(apply scan_values_positive; [assumption|apply Forall_app; tauto])
    ltac:(apply scan_values_nonempty) He).
  assert (Hpre: Forall (fun x => 3 <= x) (ctx++ps)) by
    (apply Forall_app; tauto).
  rewrite scan_values_finish in Hedge by assumption.
  unfold push_down in Hedge |- *.
  rewrite decs_app in Hedge.
  repeat rewrite D2s_app. cbn [D2s]. repeat rewrite app_nil_r.
  repeat rewrite D2s_app in Hscan.
  repeat rewrite D1s_app in Hscan. cbn [D1s] in Hscan.
  repeat rewrite D1s_app in Hscan.
  repeat rewrite Str_app_assoc in Hscan. repeat rewrite nil_Str_app in Hscan.
  repeat rewrite app_length in Hedge. cbn [length] in Hedge.
  rewrite length_app in Hscan.
  cbn [D2s] in Hedge. rewrite D2s_app in Hedge.
  repeat rewrite Str_app_assoc in Hedge.
  repeat rewrite Str_app_assoc.
  eapply evstep_progress_trans; [exact Hscan|].
  replace (2*(length ctx+length ps+1)+6)
    with (3+2*(length ctx+length ps)+5) by lia.
  exact Hedge.
Qed.

Lemma frame_two_last a b c ctx ps:
  3 <= a -> 2 <= b -> 1 <= c ->
  Forall (fun x => 3 <= x) ctx -> Forall (fun x => 3 <= x) ps ->
  S' (3,D1 a *> D1 b *> D1 c *> D2s (ctx++ps++[2%nat]) *> 0inf) -->+
  S' (3,
    D1 (2*(length ctx+length ps+1)+6) *> D1 (a-1) *> D1 (b-2) *>
    D2s ((push_down c ctx++decs ps)++[0%nat]) *> 0inf).
Proof.
  intros Ha Hb Hc Hctx Hps.
  pose proof (scan_h1 3 [a;b] c (ctx++ps) (D2 2 *> 0inf)) as Hscan.
  specialize (Hscan ltac:(repeat constructor; lia) Hc
    ltac:(apply Forall_app; tauto)).
  pose proof (reset_two_last_list (3+2*length (ctx++ps)) a b
    (scan_values c (ctx++ps))) as Hedge.
  specialize (Hedge Ha Hb ltac:(apply scan_values_positive; [assumption|apply Forall_app; tauto])
    ltac:(apply scan_values_nonempty)).
  assert (Hpre: Forall (fun x => 3 <= x) (ctx++ps)) by
    (apply Forall_app; tauto).
  rewrite scan_values_finish in Hedge by assumption.
  unfold push_down in Hedge |- *.
  rewrite decs_app in Hedge.
  repeat rewrite D2s_app. cbn [D2s]. repeat rewrite app_nil_r.
  repeat rewrite D2s_app in Hscan.
  repeat rewrite D1s_app in Hscan. cbn [D1s] in Hscan.
  repeat rewrite D1s_app in Hscan.
  repeat rewrite Str_app_assoc in Hscan. repeat rewrite nil_Str_app in Hscan.
  repeat rewrite app_length in Hedge. cbn [length] in Hedge.
  rewrite length_app in Hscan.
  repeat rewrite D2s_app in Hedge. cbn [D2s] in Hedge.
  repeat rewrite D2s_app in Hedge.
  repeat rewrite app_nil_r in Hedge. repeat rewrite Str_app_assoc in Hedge.
  repeat rewrite Str_app_assoc.
  eapply evstep_progress_trans; [exact Hscan|].
  replace (2*(length ctx+length ps+1)+6)
    with (3+2*(length ctx+length ps)+5) by lia.
  exact Hedge.
Qed.

Lemma frame_two_one a b c ctx ps m:
  3 <= a -> 2 <= b -> 1 <= c -> ps <> [] ->
  Forall (fun x => 3 <= x) ctx -> Forall (fun x => 3 <= x) ps ->
  S' (3,D1 a *> D1 b *> D1 c *>
    D2s (ctx++ps++[2%nat;m]) *> 0inf) -->+
  S' (3,
    D1 (2*(length ctx+length ps+2)+6) *> D1 (a-1) *> D1 (b-2) *>
    D2s (push_down c ctx++last_add (m+3) (last_down ps)) *> 0inf).
Proof.
  intros Ha Hb Hc Hne Hctx Hps.
  pose proof (scan_h1 3 [a;b] c (ctx++ps) (D2 2 *> D2 m *> 0inf)) as Hscan.
  specialize (Hscan ltac:(repeat constructor; lia) Hc
    ltac:(apply Forall_app; tauto)).
  pose proof (reset_two_one_list (3+2*length (ctx++ps)) a b
    (scan_values c (ctx++ps)) m) as Hedge.
  specialize (Hedge Ha Hb ltac:(apply scan_values_positive; [assumption|apply Forall_app; tauto])
    ltac:(apply scan_values_nonempty)).
  assert (Hpre2: Forall (fun x => 2 <= x) (ctx++ps)).
  { apply Forall_app; split.
    - eapply Forall_impl; [|exact Hctx]. cbn; lia.
    - eapply Forall_impl; [|exact Hps]. cbn; lia. }
  rewrite scan_values_app in Hedge by assumption.
  rewrite scan_values_app in Hscan by assumption.
  rewrite last_add_push in Hedge by assumption.
  cbn [D1s] in Hedge. rewrite D1s_app in Hedge.
  repeat rewrite Str_app_assoc in Hedge.
  unfold push_down in Hedge |- *.
  repeat rewrite D2s_app. cbn [D2s]. repeat rewrite app_nil_r.
  repeat rewrite D2s_app in Hscan.
  repeat rewrite D1s_app in Hscan. cbn [D1s] in Hscan.
  repeat rewrite D1s_app in Hscan.
  repeat rewrite Str_app_assoc in Hscan. repeat rewrite nil_Str_app in Hscan.
  repeat rewrite app_length in Hedge. cbn [length] in Hedge.
  rewrite length_app in Hscan.
  cbn [D2s] in Hedge. repeat rewrite D2s_app in Hedge.
  repeat rewrite Str_app_assoc in Hedge.
  repeat rewrite Str_app_assoc.
  eapply evstep_progress_trans; [exact Hscan|].
  replace (2*(length ctx+length ps+2)+6)
    with (3+2*(length ctx+length ps)+7) by lia.
  exact Hedge.
Qed.

Lemma frame_two_two a b c ctx ps m u:
  3 <= a -> 2 <= b -> 1 <= c -> ps <> [] ->
  Forall (fun x => 3 <= x) ctx -> Forall (fun x => 3 <= x) ps ->
  S' (3,D1 a *> D1 b *> D1 c *>
    D2s (ctx++ps++[2%nat;m;u]) *> 0inf) -->+
  S' (3,
    D1 (2*(length ctx+length ps+3)+2) *> D1 (a-1) *> D1 (b-2) *>
    D2s (push_down c ctx++last_add (m+3) (last_down ps)) *>
    reset_tail_side (boundary_tail u)).
Proof.
  intros Ha Hb Hc Hne Hctx Hps.
  pose proof (scan_h1 3 [a;b] c (ctx++ps)
    (D2 2 *> D2 m *> D2 u *> 0inf)) as Hscan.
  specialize (Hscan ltac:(repeat constructor; lia) Hc
    ltac:(apply Forall_app; tauto)).
  pose proof (reset_two_two_list (3+2*length (ctx++ps)) a b
    (scan_values c (ctx++ps)) m u) as Hedge.
  specialize (Hedge Ha Hb ltac:(apply scan_values_positive; [assumption|apply Forall_app; tauto])
    ltac:(apply scan_values_nonempty)).
  assert (Hpre2: Forall (fun x => 2 <= x) (ctx++ps)).
  { apply Forall_app; split.
    - eapply Forall_impl; [|exact Hctx]. cbn; lia.
    - eapply Forall_impl; [|exact Hps]. cbn; lia. }
  rewrite scan_values_app in Hedge by assumption.
  rewrite scan_values_app in Hscan by assumption.
  rewrite last_add_push in Hedge by assumption.
  cbn [D1s] in Hedge. rewrite D1s_app in Hedge.
  repeat rewrite Str_app_assoc in Hedge.
  unfold push_down in Hedge |- *.
  repeat rewrite D2s_app. cbn [D2s]. repeat rewrite app_nil_r.
  repeat rewrite D2s_app in Hscan.
  repeat rewrite D1s_app in Hscan. cbn [D1s] in Hscan.
  repeat rewrite D1s_app in Hscan.
  repeat rewrite Str_app_assoc in Hscan. repeat rewrite nil_Str_app in Hscan.
  repeat rewrite app_length in Hedge. cbn [length] in Hedge.
  rewrite length_app in Hscan.
  cbn [D2s] in Hedge. repeat rewrite D2s_app in Hedge.
  repeat rewrite Str_app_assoc in Hedge.
  repeat rewrite Str_app_assoc.
  eapply evstep_progress_trans; [exact Hscan|].
  replace (2*(length ctx+length ps+3)+2)
    with (3+2*(length ctx+length ps)+5) by lia.
  exact Hedge.
Qed.

Definition subns r xs := map (fun x => x-r) xs.

Lemma subns_0 xs: subns 0 xs = xs.
Proof. unfold subns; induction xs; cbn; [reflexivity|f_equal; [lia|assumption]]. Qed.

Lemma subns_next r xs:
  decs (subns r xs) = subns (S r) xs.
Proof.
  unfold decs,subns. rewrite map_map. apply map_ext; intros; cbn.
  rewrite <-Nat.sub_add_distr. replace (r+1) with (S r) by lia. reflexivity.
Qed.

Lemma sym_ctx_length gen r base:
  length (gen++subns r base) = length gen+length base.
Proof. unfold subns. rewrite length_app,length_map. reflexivity. Qed.

Lemma push_sym_ctx c gen r base:
  push_down c (gen++subns r base) =
  ((c+1)::decs gen)++subns (S r) base.
Proof. unfold push_down. rewrite decs_app,subns_next. reflexivity. Qed.

Lemma sym_ctx_positive gen r base:
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => r+3 <= x) base ->
  Forall (fun x => 3 <= x) (gen++subns r base).
Proof.
  intros Hgen Hbase. apply Forall_app; split; [exact Hgen|].
  unfold subns. rewrite Forall_map. eapply Forall_impl; [|exact Hbase].
  cbn; lia.
Qed.

Definition sconfig base a b c gen r local t :=
  S' (3,D1 a *> D1 b *> D1 c *>
    D2s (gen++subns r base++local) *> reset_tail_side t).

Lemma sym_positive base a b c gen r local t:
  3 <= a -> 2 <= b -> 1 <= c -> local <> [] ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => r+3 <= x) base ->
  Forall (fun x => 3 <= x) local ->
  sconfig base a b c gen r local t -->+
  sconfig base
    (2*(length gen+length base+length local)+6) (a-1) (b-2)
    ((c+1)::decs gen) (S r)
    (last_down local++reset_tail_extra t) (reset_tail_next t).
Proof.
  intros Ha Hb Hc Hne Hgen Hbase Hlocal. unfold sconfig.
  pose proof (frame_positive a b c (gen++subns r base) local t
    Ha Hb Hc Hne (sym_ctx_positive gen r base Hgen Hbase) Hlocal) as H.
  rewrite push_sym_ctx in H. rewrite sym_ctx_length in H.
  repeat rewrite <-app_assoc in H.
  exact H.
Qed.

Lemma sym_edge base a b c gen r ps e:
  3 <= a -> 2 <= b -> 1 <= c -> e <= 1 ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => r+3 <= x) base ->
  Forall (fun x => 3 <= x) ps ->
  sconfig base a b c gen r (ps++[e]) RTnone -->+
  sconfig base
    (2*(length gen+length base+length ps+1)+6) (a-1) (b-2)
    ((c+1)::decs gen) (S r) (decs ps) RTnone.
Proof.
  intros Ha Hb Hc He Hgen Hbase Hps. unfold sconfig.
  pose proof (frame_edge a b c (gen++subns r base) ps e
    Ha Hb Hc He (sym_ctx_positive gen r base Hgen Hbase) Hps) as H.
  rewrite push_sym_ctx in H. repeat rewrite sym_ctx_length in H.
  cbn [reset_tail_side] in H |- *. repeat rewrite <-app_assoc in H.
  exact H.
Qed.

Lemma sym_two_last base a b c gen r ps:
  3 <= a -> 2 <= b -> 1 <= c ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => r+3 <= x) base ->
  Forall (fun x => 3 <= x) ps ->
  sconfig base a b c gen r (ps++[2%nat]) RTnone -->+
  sconfig base
    (2*(length gen+length base+length ps+1)+6) (a-1) (b-2)
    ((c+1)::decs gen) (S r) (decs ps++[0%nat]) RTnone.
Proof.
  intros Ha Hb Hc Hgen Hbase Hps. unfold sconfig.
  pose proof (frame_two_last a b c (gen++subns r base) ps
    Ha Hb Hc (sym_ctx_positive gen r base Hgen Hbase) Hps) as H.
  rewrite push_sym_ctx in H. repeat rewrite sym_ctx_length in H.
  cbn [reset_tail_side] in H |- *. repeat rewrite <-app_assoc in H.
  exact H.
Qed.

Lemma sym_two_one base a b c gen r ps m:
  3 <= a -> 2 <= b -> 1 <= c -> ps <> [] ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => r+3 <= x) base ->
  Forall (fun x => 3 <= x) ps ->
  sconfig base a b c gen r (ps++[2%nat;m]) RTnone -->+
  sconfig base
    (2*(length gen+length base+length ps+2)+6) (a-1) (b-2)
    ((c+1)::decs gen) (S r) (last_add (m+3) (last_down ps)) RTnone.
Proof.
  intros Ha Hb Hc Hne Hgen Hbase Hps. unfold sconfig.
  pose proof (frame_two_one a b c (gen++subns r base) ps m
    Ha Hb Hc Hne (sym_ctx_positive gen r base Hgen Hbase) Hps) as H.
  rewrite push_sym_ctx in H. repeat rewrite sym_ctx_length in H.
  cbn [reset_tail_side] in H |- *. repeat rewrite <-app_assoc in H.
  exact H.
Qed.

Lemma sym_two_two base a b c gen r ps m u:
  3 <= a -> 2 <= b -> 1 <= c -> ps <> [] ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => r+3 <= x) base ->
  Forall (fun x => 3 <= x) ps ->
  sconfig base a b c gen r (ps++[2%nat;m;u]) RTnone -->+
  sconfig base
    (2*(length gen+length base+length ps+3)+2) (a-1) (b-2)
    ((c+1)::decs gen) (S r) (last_add (m+3) (last_down ps))
    (boundary_tail u).
Proof.
  intros Ha Hb Hc Hne Hgen Hbase Hps. unfold sconfig.
  pose proof (frame_two_two a b c (gen++subns r base) ps m u
    Ha Hb Hc Hne (sym_ctx_positive gen r base Hgen Hbase) Hps) as H.
  rewrite push_sym_ctx in H. repeat rewrite sym_ctx_length in H.
  repeat rewrite <-app_assoc in H.
  exact H.
Qed.

Lemma Forall_ge_weaken k l xs:
  k <= l -> Forall (fun x => l <= x) xs -> Forall (fun x => k <= x) xs.
Proof. intros Hkl H; eapply Forall_impl; [|exact H]; cbn; lia. Qed.

Definition phase_bit (p:bool) : Z := if p then 1%Z else 0%Z.

Definition packet_output (p:bool) (x:packet_type) : list nat :=
  let p' := packet_next_parity p x in
  rev (packet_parameters_from 0 (phase_bit p-packet_e x)
    (phase_bit p') (packet_prod p x)).

Definition packet_local0 (x:packet_type) : list nat :=
  match x with
  | P2_1 => [4;3]
  | P4_2 => [8;7;4;3]
  | P5_3 => [11;8;7;4;3]
  | P9_4 => [17;14;11;8;7;8;7;4;3]
  | P9_5 => [19;16;13;10;11;8;7;4;3]
  | P12_5 => [22;19;16;17;14;11;8;7;8;7;4;3]
  | P12_6 => [24;21;18;15;16;15;12;11;8;7;4;3]
  | P17_7 => [31;28;25;26;23;20;19;14;11;10;11;8;7;8;7;4;3]
  | P17_8 => [33;30;27;24;25;24;21;20;17;14;11;8;7;8;7;4;3]
  | P18_8 => [34;31;28;25;26;25;22;19;16;17;14;11;8;7;8;7;4;3]
  | P20_10 => [40;37;34;35;32;29;26;27;26;23;22;19;16;13;10;11;8;7;4;3]
  | P25_11 => [47;44;41;42;39;36;33;30;27;28;25;26;23;20;19;14;11;10;11;8;7;8;7;4;3]
  | P25_12 => [49;46;43;40;41;40;37;36;33;30;27;24;25;22;19;16;13;10;11;8;7;8;7;4;3]
  | P26_11 => [48;45;42;43;40;37;36;31;28;27;28;25;22;19;20;19;14;11;10;11;8;7;8;7;4;3]
  | P26_12 => [50;47;44;41;40;41;38;35;32;33;30;27;24;21;18;19;16;13;10;11;8;7;8;7;4;3]
  | P27_12 => [51;48;45;42;43;42;39;36;33;34;31;28;25;22;19;20;19;14;11;10;11;8;7;8;7;4;3]
  | P41_20 => [81;78;75;72;73;72;69;68;65;62;59;56;57;54;51;48;45;42;43;40;41;40;37;36;33;30;27;24;25;22;19;16;13;10;11;8;7;8;7;4;3]
  | P42_21 => [84;81;78;75;76;75;72;71;68;65;62;59;60;57;54;51;48;45;46;43;42;43;40;37;34;35;32;29;26;23;20;21;18;15;12;13;10;11;8;7;4;3]
  | P43_20 => [83;80;77;74;75;74;71;70;67;64;61;58;59;56;53;50;47;44;45;42;43;42;39;36;33;34;31;28;25;22;19;20;19;14;11;10;11;8;7;8;7;4;3]
  | P44_20 => [84;81;78;75;76;75;72;69;66;67;64;61;58;55;52;53;50;47;44;45;42;43;40;37;36;31;28;27;28;25;22;19;20;19;14;11;10;11;8;7;8;7;4;3]
  | P52_25 => [102;99;96;97;94;91;90;85;82;81;82;79;80;79;76;75;72;69;66;63;64;63;60;59;56;53;50;47;48;45;42;39;36;33;34;31;32;29;26;23;20;17;18;15;16;15;12;11;8;7;4;3]
  | P68_32 => [132;129;126;123;124;123;120;119;116;113;110;107;108;105;102;99;96;93;94;91;92;89;86;83;80;77;78;75;76;75;72;69;66;67;64;61;58;55;52;53;50;47;44;45;42;43;40;37;36;31;28;27;28;25;22;19;20;19;14;11;10;11;8;7;8;7;4;3]
  end.

Definition packet_local_nat (p:bool) x :=
  if p then map S (packet_local0 x) else packet_local0 x.

Definition zshift (z:Z) (n:nat) : nat :=
  match z with
  | Z0 => n
  | Zpos q => n+Pos.to_nat q
  | Zneg q => n-Pos.to_nat q
  end.

Definition shift_local z xs := map (zshift z) xs.

Fixpoint packet_output_from_nat (prefix:nat) (phase parity:Z)
    (xs:list packet_type) : list nat :=
  match xs with
  | [] => []
  | x::xs =>
      packet_output_from_nat (prefix+packet_t x) (phase+packet_e x) parity xs ++
      shift_local (2*Z.of_nat prefix-phase+parity) (packet_local0 x)
  end.

Definition packet_output_nat p x :=
  packet_output_from_nat 0 (phase_bit p-packet_e x)
    (phase_bit (packet_next_parity p x)) (packet_prod p x).

Definition shifted_output_nat n p x :=
  map (fun q => 2*n+q) (packet_output_nat p x).

Record sym_state := SymState {
  ss_a : nat;
  ss_b : nat;
  ss_c : nat;
  ss_gen : list nat;
  ss_r : nat;
  ss_local : list nat;
  ss_tail : reset_tail
}.

Definition lift_gen n xs := map (fun q => 2*n+q) xs.

Definition state_config base s :=
  sconfig base
    (2*length base+ss_a s)
    (2*length base+ss_b s)
    (2*length base+ss_c s)
    (lift_gen (length base) (ss_gen s))
    (ss_r s) (ss_local s) (ss_tail s).

Fixpoint all_ge (k:nat) (xs:list nat) : bool :=
  match xs with
  | [] => true
  | x::xs => (k <=? x) && all_ge k xs
  end.

Fixpoint low_split (xs:list nat) : list nat * list nat :=
  match xs with
  | [] => ([],[])
  | x::xs =>
      if x <=? 2 then ([],x::xs)
      else let '(pre,rest) := low_split xs in (x::pre,rest)
  end.

Definition state_ok limit s :=
  andb (3 <=? ss_a s)
    (andb (2 <=? ss_b s)
      (andb (1 <=? ss_c s)
        (andb (ss_r s <? limit) (all_ge 3 (ss_gen s))))).

Definition positive_next s :=
  SymState
    (2*(length (ss_gen s)+length (ss_local s))+6)
    (ss_a s-1) (ss_b s-2)
    ((ss_c s+1)::decs (ss_gen s)) (S (ss_r s))
    (last_down (ss_local s)++reset_tail_extra (ss_tail s))
    (reset_tail_next (ss_tail s)).

Definition edge_next s pre :=
  SymState
    (2*(length (ss_gen s)+length pre+1)+6)
    (ss_a s-1) (ss_b s-2)
    ((ss_c s+1)::decs (ss_gen s)) (S (ss_r s))
    (decs pre) RTnone.

Definition two_last_next s pre :=
  SymState
    (2*(length (ss_gen s)+length pre+1)+6)
    (ss_a s-1) (ss_b s-2)
    ((ss_c s+1)::decs (ss_gen s)) (S (ss_r s))
    (decs pre++[0%nat]) RTnone.

Definition two_one_next s pre m :=
  SymState
    (2*(length (ss_gen s)+length pre+2)+6)
    (ss_a s-1) (ss_b s-2)
    ((ss_c s+1)::decs (ss_gen s)) (S (ss_r s))
    (last_add (m+3) (last_down pre)) RTnone.

Definition two_two_next s pre m u :=
  SymState
    (2*(length (ss_gen s)+length pre+3)+2)
    (ss_a s-1) (ss_b s-2)
    ((ss_c s+1)::decs (ss_gen s)) (S (ss_r s))
    (last_add (m+3) (last_down pre)) (boundary_tail u).

Definition sym_step limit s : option sym_state :=
  if state_ok limit s then
    let '(pre,rest) := low_split (ss_local s) in
    match rest with
    | [] => match ss_local s with
            | [] => None
            | _::_ => Some (positive_next s)
            end
    | [0%nat] => match ss_tail s with
                 | RTnone => Some (edge_next s pre)
                 | _ => None
                 end
    | [1%nat] => match ss_tail s with
                 | RTnone => Some (edge_next s pre)
                 | _ => None
                 end
    | [2%nat] => match ss_tail s with
                 | RTnone => Some (two_last_next s pre)
                 | _ => None
                 end
    | [2%nat;m] =>
        match pre,ss_tail s with
        | _::_,RTnone => Some (two_one_next s pre m)
        | _,_ => None
        end
    | [2%nat;m;u] =>
        match pre,ss_tail s with
        | _::_,RTnone => Some (two_two_next s pre m u)
        | _,_ => None
        end
    | _ => None
    end
  else None.

Fixpoint sym_run (n limit:nat) (s:sym_state) : option sym_state :=
  match n with
  | O => Some s
  | Datatypes.S n =>
      match sym_step limit s with
      | Some s' => sym_run n limit s'
      | None => None
      end
  end.

Lemma all_ge_spec k xs:
  all_ge k xs = true <-> Forall (fun x => k <= x) xs.
Proof.
  induction xs; cbn.
  - split; constructor.
  - rewrite Bool.andb_true_iff,IHxs,Nat.leb_le. split.
    + intros [??]. constructor; assumption.
    + intros H. inversion H; tauto.
Qed.

Lemma low_split_spec xs pre rest:
  low_split xs = (pre,rest) ->
  xs = pre++rest /\ Forall (fun x => 3 <= x) pre /\
  (rest = [] \/ exists x tail, rest = x::tail /\ x <= 2).
Proof.
  revert pre rest. induction xs as [|x xs IH]; intros pre rest H; cbn in H.
  - inversion H; subst. split; [reflexivity|].
    split; [constructor|left; reflexivity].
  - destruct (x <=? 2) eqn:Hx.
    + inversion H; subst. split; [reflexivity|].
      split; [constructor|]. right. exists x,xs.
      split; [reflexivity|apply Nat.leb_le; assumption].
    + destruct (low_split xs) as [pre' rest'] eqn:Hs.
      inversion H; subst. specialize (IH _ _ eq_refl) as [Heq [Hpre Hrest]].
      split; [cbn; f_equal; assumption|]. split.
      * constructor; [apply Nat.leb_gt in Hx; lia|exact Hpre].
      * exact Hrest.
Qed.

Lemma lift_gen_length n xs:
  length (lift_gen n xs) = length xs.
Proof. unfold lift_gen; apply length_map. Qed.

Lemma lift_gen_forall n k xs:
  Forall (fun x => k <= x) xs ->
  Forall (fun x => k <= x) (lift_gen n xs).
Proof.
  intros H. unfold lift_gen. rewrite Forall_map.
  eapply Forall_impl; [|exact H]. cbn; lia.
Qed.

Lemma lift_gen_decs n xs:
  Forall (fun x => 1 <= x) xs ->
  decs (lift_gen n xs) = lift_gen n (decs xs).
Proof.
  intros H. induction H; cbn [decs lift_gen map].
  - reflexivity.
  - f_equal; [lia|assumption].
Qed.

Lemma base_for_step limit r base:
  r < limit -> Forall (fun x => limit+3 <= x) base ->
  Forall (fun x => r+3 <= x) base.
Proof. intros Hr H. eapply Forall_ge_weaken; [|exact H]; lia. Qed.

Lemma offset_positive limit base a b c gen r local tail:
  3 <= a -> 2 <= b -> 1 <= c -> r < limit -> local <> [] ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => 3 <= x) local ->
  Forall (fun x => limit+3 <= x) base ->
  state_config base (SymState a b c gen r local tail) -->+
  state_config base (positive_next (SymState a b c gen r local tail)).
Proof.
  intros Ha Hb Hc Hr Hne Hgen Hlocal Hbase.
  pose proof (sym_positive base
    (2*length base+a) (2*length base+b) (2*length base+c)
    (lift_gen (length base) gen) r local tail) as H.
  specialize (H ltac:(lia) ltac:(lia) ltac:(lia) Hne
    ltac:(apply lift_gen_forall; assumption)
    ltac:(eapply base_for_step; eassumption) Hlocal).
  unfold state_config,positive_next. cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail].
  rewrite lift_gen_length in H.
  rewrite lift_gen_decs in H by
    (eapply Forall_impl; [|exact Hgen]; cbn; lia).
  cbn [lift_gen map] in H |- *.
  applys_eq H; flia.
Qed.

Definition phase_nat (p:bool) : nat := if p then 1 else 0.

Definition packet_inc x := packet_t x + 2*packet_d x.

Definition packet_block_nat offset x :=
  map (fun q => offset+q)
    (mapi_from (packet_parameter 0%Z) 0 (packet_word x)).

Fixpoint packet_nat_from offset xs :=
  match xs with
  | [] => []
  | x::xs =>
      packet_block_nat offset x ++ packet_nat_from (offset+packet_inc x) xs
  end.

Lemma packet_parameter_shift n j h:
  (0 <= Z.of_nat (baseline j)-2*h)%Z ->
  packet_parameter (Z.of_nat n) j h = n+packet_parameter 0%Z j h.
Proof.
  intros Hz. unfold packet_parameter.
  replace (Z.of_nat (baseline j) + Z.of_nat n - 2*h)%Z with
    (Z.of_nat n+(Z.of_nat (baseline j)-2*h))%Z by ring.
  rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id.
  replace (Z.of_nat (baseline j)+0-2*h)%Z with
    (Z.of_nat (baseline j)-2*h)%Z by ring. reflexivity.
Qed.

Lemma packet_parameter_nonnegative j h:
  1 <= packet_parameter 0%Z j h ->
  (0 <= Z.of_nat (baseline j)-2*h)%Z.
Proof.
  unfold packet_parameter. intros H.
  replace (Z.of_nat (baseline j)+0-2*h)%Z with
    (Z.of_nat (baseline j)-2*h)%Z in H by ring.
  set (z := (Z.of_nat (baseline j)-2*h)%Z) in *.
  destruct z; cbn in *; lia.
Qed.

Lemma mapi_packet_shift n i hs:
  Forall (fun q => 1 <= q)
    (mapi_from (packet_parameter 0%Z) i hs) ->
  mapi_from (packet_parameter (Z.of_nat n)) i hs =
  map (fun q => n+q) (mapi_from (packet_parameter 0%Z) i hs).
Proof.
  revert i. induction hs as [|h hs IH]; intros i H; cbn; [reflexivity|].
  inversion H; subst. f_equal.
  - apply packet_parameter_shift,packet_parameter_nonnegative. assumption.
  - apply IH. assumption.
Qed.

Lemma packet_block_shift n x:
  mapi_from (packet_parameter (Z.of_nat n)) 0 (packet_word x) =
  packet_block_nat n x.
Proof.
  unfold packet_block_nat. apply mapi_packet_shift.
  eapply Forall_impl; [|apply packet_front_positive with (p:=false)].
  cbn; lia.
Qed.

Lemma packet_offset_next prefix phase parity offset x:
  (2*Z.of_nat prefix-phase+parity = Z.of_nat offset)%Z ->
  (2*Z.of_nat (prefix+packet_t x)-(phase+packet_e x)+parity =
    Z.of_nat (offset+packet_inc x))%Z.
Proof.
  intros H. unfold packet_e,packet_inc in *. zify; lia.
Qed.

Lemma packet_parameters_from_nat xs prefix phase parity offset:
  (2*Z.of_nat prefix-phase+parity = Z.of_nat offset)%Z ->
  packet_parameters_from prefix phase parity xs = packet_nat_from offset xs.
Proof.
  revert prefix phase offset. induction xs as [|x xs IH];
    intros prefix phase offset Hoffset; cbn.
  - reflexivity.
  - change
      (mapi_from
        (packet_parameter (2*Z.of_nat prefix-phase+parity)) 0 (packet_word x) ++
       packet_parameters_from (prefix+packet_t x) (phase+packet_e x) parity xs =
       packet_block_nat offset x ++
       packet_nat_from (offset+packet_inc x) xs).
    rewrite Hoffset,packet_block_shift.
    rewrite (IH ((prefix+packet_t x)%nat)
      ((phase+packet_e x)%Z)
      ((offset+packet_inc x)%nat)) by
      (eapply packet_offset_next; exact Hoffset).
    reflexivity.
Qed.

Lemma mapi_from_length {A B} (f:nat->A->B) i xs:
  length (mapi_from f i xs) = length xs.
Proof.
  revert i. induction xs as [|x xs IH]; intros; cbn; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma packet_block_length offset x:
  length (packet_block_nat offset x) = packet_t x.
Proof.
  unfold packet_block_nat. rewrite length_map,mapi_from_length,packet_word_length.
  reflexivity.
Qed.

Lemma packet_nat_from_length offset xs:
  length (packet_nat_from offset xs) = packet_length xs.
Proof.
  revert offset. induction xs; intros; cbn; [reflexivity|].
  rewrite length_app,packet_block_length,IHxs. reflexivity.
Qed.

Lemma packet_block_lower offset x:
  Forall (fun q => offset+3 <= q) (packet_block_nat offset x).
Proof.
  unfold packet_block_nat. rewrite Forall_map.
  eapply Forall_impl; [|apply packet_front_positive with (p:=false)].
  cbn; lia.
Qed.

Lemma packet_nat_from_lower k offset xs:
  k <= offset ->
  Forall (fun q => k+3 <= q) (packet_nat_from offset xs).
Proof.
  revert offset. induction xs as [|x xs IH]; intros offset Hko; cbn.
  - constructor.
  - apply Forall_app; split.
    + eapply Forall_impl; [|apply packet_block_lower]. cbn; lia.
    + apply IH. unfold packet_inc. lia.
Qed.

Lemma packet_block_add k offset x:
  packet_block_nat (k+offset) x =
  map (fun q => k+q) (packet_block_nat offset x).
Proof.
  unfold packet_block_nat. rewrite map_map. apply map_ext; cbn; intros; lia.
Qed.

Lemma packet_nat_from_add k offset xs:
  packet_nat_from (k+offset) xs =
  map (fun q => k+q) (packet_nat_from offset xs).
Proof.
  revert offset. induction xs as [|x xs IH]; intros offset; cbn.
  - reflexivity.
  - rewrite packet_block_add,map_app.
    replace (k+offset+packet_inc x) with (k+(offset+packet_inc x)) by lia.
    rewrite IH. reflexivity.
Qed.

Lemma subns_add k xs:
  subns k (map (fun q => k+q) xs) = xs.
Proof.
  unfold subns. rewrite map_map. replace xs with (map (fun q => q) xs) at 2
    by (rewrite map_id; reflexivity).
  apply map_ext; cbn; intros; lia.
Qed.

Lemma subns_rev k xs:
  subns k (rev xs) = rev (subns k xs).
Proof. unfold subns. apply map_rev. Qed.

Lemma phase_bit_nat p:
  phase_bit p = Z.of_nat (phase_nat p).
Proof. destruct p; reflexivity. Qed.

Lemma packet_local_nat_block p x:
  packet_local_nat p x = rev (packet_block_nat (phase_nat p) x).
Proof. destruct p,x; vm_compute; reflexivity. Qed.

Lemma packet_output_nat_eq p x:
  packet_output_nat p x = packet_output p x.
Proof. destruct p,x; vm_compute; reflexivity. Qed.

Lemma packet_output_nat_positive p x:
  Forall (fun q => 1 <= q) (packet_output_nat p x).
Proof. destruct p,x; vm_compute; repeat constructor; lia. Qed.

Lemma packet_parameter_shift_Z n offset j h:
  1 <= packet_parameter offset j h ->
  packet_parameter (Z.of_nat n+offset) j h =
  n+packet_parameter offset j h.
Proof.
  unfold packet_parameter. intros H.
  set (z := (Z.of_nat (baseline j)+offset-2*h)%Z) in *.
  assert (Hz: (0 <= z)%Z).
  { destruct z; cbn in *; lia. }
  replace (Z.of_nat (baseline j)+(Z.of_nat n+offset)-2*h)%Z with
    (Z.of_nat n+z)%Z by (unfold z; ring).
  rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma mapi_packet_shift_Z n offset i hs:
  Forall (fun q => 1 <= q) (mapi_from (packet_parameter offset) i hs) ->
  mapi_from (packet_parameter (Z.of_nat n+offset)) i hs =
  map (fun q => n+q) (mapi_from (packet_parameter offset) i hs).
Proof.
  revert i. induction hs as [|h hs IH]; intros i H; cbn; [reflexivity|].
  inversion H; subst. f_equal.
  - apply packet_parameter_shift_Z. assumption.
  - apply IH. assumption.
Qed.

Lemma packet_parameters_from_shift n xs prefix phase parity:
  Forall (fun q => 1 <= q) (packet_parameters_from prefix phase parity xs) ->
  packet_parameters_from (n+prefix) phase parity xs =
  map (fun q => 2*n+q) (packet_parameters_from prefix phase parity xs).
Proof.
  revert prefix phase. induction xs as [|x xs IH];
    intros prefix phase Hpos; cbn in Hpos |- *; [reflexivity|].
  apply Forall_app in Hpos as [Hblock Htail].
  change
    (mapi_from
      (packet_parameter
        (2*Z.of_nat (n+prefix)-phase+parity)) 0 (packet_word x) ++
     packet_parameters_from (n+prefix+packet_t x)
       (phase+packet_e x) parity xs =
     map (fun q => 2*n+q)
       (mapi_from
         (packet_parameter (2*Z.of_nat prefix-phase+parity))
         0 (packet_word x) ++
        packet_parameters_from (prefix+packet_t x)
          (phase+packet_e x) parity xs)).
  replace (2*Z.of_nat (n+prefix)-phase+parity)%Z with
    (Z.of_nat (2*n)+(2*Z.of_nat prefix-phase+parity))%Z by (zify; lia).
  rewrite mapi_packet_shift_Z by exact Hblock.
  replace (n+prefix+packet_t x) with (n+(prefix+packet_t x)) by lia.
  rewrite IH by exact Htail. rewrite map_app. reflexivity.
Qed.

Lemma Forall_rev' {A} (P:A->Prop) xs:
  Forall P xs -> Forall P (rev xs).
Proof.
  intros H. induction H; cbn; [constructor|].
  rewrite Forall_app. split; [assumption|constructor; [assumption|constructor]].
Qed.

Definition packet_base p x xs :=
  rev (packet_nat_from
    (packet_length (packet_prod p x)+phase_nat (packet_next_parity p x)) xs).

Lemma packet_base_length p x xs:
  length (packet_base p x xs) = packet_length xs.
Proof.
  unfold packet_base. rewrite length_rev,packet_nat_from_length. reflexivity.
Qed.

Lemma packet_base_lower p x xs:
  Forall (fun q => packet_length (packet_prod p x)+3 <= q)
    (packet_base p x xs).
Proof.
  unfold packet_base. apply Forall_rev',packet_nat_from_lower. lia.
Qed.

Lemma packet_service_offset p x:
  (2*Z.of_nat (packet_t x)-packet_e x+phase_bit p =
    Z.of_nat
      (packet_length (packet_prod p x)+phase_nat (packet_next_parity p x)))%Z.
Proof. destruct p,x; vm_compute; reflexivity. Qed.

Lemma packet_parameters_cons p x xs:
  phase_sum (x::xs) = phase_bit p ->
  packet_parameters (x::xs) =
    packet_base p x xs ++ packet_local_nat p x.
Proof.
  intros Hphase. unfold packet_parameters,packet_base.
  rewrite Hphase. cbn [packet_parameters_from]. rewrite rev_app_distr.
  replace (0+packet_t x) with (packet_t x) by lia.
  replace (0+packet_e x)%Z with (packet_e x) by ring.
  replace (2*Z.of_nat 0-0+phase_bit p)%Z with (phase_bit p) by ring.
  rewrite (packet_parameters_from_nat xs (packet_t x) (packet_e x)
    (phase_bit p)
    (packet_length (packet_prod p x)+phase_nat (packet_next_parity p x)))
    by apply packet_service_offset.
  rewrite phase_bit_nat,packet_block_shift.
  rewrite packet_local_nat_block. reflexivity.
Qed.

Lemma packet_config_cons p x xs:
  phase_sum (x::xs) = phase_bit p ->
  packet_config (x::xs) =
  sconfig (packet_base p x xs)
    (2*(length (packet_base p x xs)+packet_t x)+6)
    (2*(length (packet_base p x xs)+packet_t x)+3)
    (2*(length (packet_base p x xs)+packet_t x)+1)
    [] 0 (packet_local_nat p x) RTnone.
Proof.
  intros Hphase. unfold packet_config,packet_side,sconfig.
  rewrite (packet_parameters_cons p x xs Hphase).
  rewrite packet_base_length,subns_0. cbn [packet_length length app D2s].
  repeat rewrite D2s_app. repeat rewrite app_nil_r.
  repeat rewrite Str_app_assoc. f_equal; flia.
Qed.

Lemma phase_sum_app xs ys:
  phase_sum (xs++ys) = (phase_sum xs+phase_sum ys)%Z.
Proof. induction xs; cbn; [ring|rewrite IHxs; ring]. Qed.

Lemma packet_length_app xs ys:
  packet_length (xs++ys) = packet_length xs+packet_length ys.
Proof. induction xs; cbn; [reflexivity|rewrite IHxs; lia]. Qed.

Lemma packet_parameters_from_app xs ys prefix phase parity:
  packet_parameters_from prefix phase parity (xs++ys) =
  packet_parameters_from prefix phase parity xs ++
  packet_parameters_from (prefix+packet_length xs)
    (phase+phase_sum xs) parity ys.
Proof.
  revert prefix phase. induction xs as [|x xs IH]; intros prefix phase; cbn.
  - replace (prefix+0) with prefix by lia.
    replace (phase+0)%Z with phase by ring. reflexivity.
  - rewrite IH. repeat rewrite app_assoc.
    replace (prefix+packet_t x+packet_length xs)
      with (prefix+(packet_t x+packet_length xs)) by lia.
    replace (phase+packet_e x+phase_sum xs)%Z
      with (phase+(packet_e x+phase_sum xs))%Z by ring.
    reflexivity.
Qed.

Lemma packet_output_phase p x:
  phase_sum (packet_prod p x) =
    (packet_e x-phase_bit p+phase_bit (packet_next_parity p x))%Z.
Proof. destruct p,x; vm_compute; reflexivity. Qed.

Lemma packet_successor_phase p x xs:
  phase_sum (x::xs) = phase_bit p ->
  phase_sum (xs++packet_prod p x) = phase_bit (packet_next_parity p x).
Proof.
  intros H. rewrite phase_sum_app,packet_output_phase. cbn [phase_sum] in H.
  lia.
Qed.

Lemma packet_base_after p x xs:
  subns (packet_length (packet_prod p x)) (packet_base p x xs) =
  rev (packet_nat_from (phase_nat (packet_next_parity p x)) xs).
Proof.
  unfold packet_base.
  rewrite packet_nat_from_add,subns_rev,subns_add. reflexivity.
Qed.

Lemma rev_map' {A B} (f:A->B) xs:
  rev (map f xs) = map f (rev xs).
Proof.
  induction xs; cbn; [reflexivity|].
  rewrite IHxs,map_app. reflexivity.
Qed.

Lemma packet_output_forward_positive p x:
  Forall (fun q => 1 <= q)
    (packet_parameters_from 0 (phase_bit p-packet_e x)
      (phase_bit (packet_next_parity p x)) (packet_prod p x)).
Proof.
  pose proof (Forall_rev' _ _ (packet_output_nat_positive p x)) as H.
  rewrite packet_output_nat_eq in H. unfold packet_output in H.
  rewrite rev_involutive in H. exact H.
Qed.

Lemma packet_generated_parameters p x xs:
  phase_sum (x::xs) = phase_bit p ->
  rev (packet_parameters_from (packet_length xs) (phase_sum xs)
    (phase_bit (packet_next_parity p x)) (packet_prod p x)) =
  shifted_output_nat (packet_length xs) p x.
Proof.
  intros Hphase.
  assert (Hxs: phase_sum xs = (phase_bit p-packet_e x)%Z).
  { cbn [phase_sum] in Hphase. lia. }
  rewrite Hxs.
  pose proof (packet_parameters_from_shift (packet_length xs)
    (packet_prod p x) 0 (phase_bit p-packet_e x)
    (phase_bit (packet_next_parity p x))
    (packet_output_forward_positive p x)) as Hshift.
  replace (packet_length xs+0) with (packet_length xs) in Hshift by lia.
  rewrite Hshift,rev_map'. unfold shifted_output_nat.
  rewrite packet_output_nat_eq. unfold packet_output. reflexivity.
Qed.

Lemma packet_suffix_parameters p x xs:
  rev (packet_parameters_from 0 0
    (phase_bit (packet_next_parity p x)) xs) =
  subns (packet_length (packet_prod p x)) (packet_base p x xs).
Proof.
  rewrite (packet_parameters_from_nat xs 0 0
    (phase_bit (packet_next_parity p x))
    (phase_nat (packet_next_parity p x))).
  - symmetry. apply packet_base_after.
  - rewrite phase_bit_nat. cbn [Z.of_nat]. ring.
Qed.

Lemma packet_parameters_successor p x xs:
  phase_sum (x::xs) = phase_bit p ->
  packet_parameters (xs++packet_prod p x) =
    shifted_output_nat (packet_length xs) p x ++
    subns (packet_length (packet_prod p x)) (packet_base p x xs).
Proof.
  intros Hphase. unfold packet_parameters.
  rewrite (packet_successor_phase p x xs Hphase).
  rewrite packet_parameters_from_app,rev_app_distr.
  replace (0+packet_length xs) with (packet_length xs) by lia.
  replace (0+phase_sum xs)%Z with (phase_sum xs) by ring.
  rewrite (packet_generated_parameters p x xs Hphase).
  rewrite packet_suffix_parameters. reflexivity.
Qed.

Lemma packet_config_successor p x xs:
  phase_sum (x::xs) = phase_bit p ->
  packet_config (xs++packet_prod p x) =
  sconfig (packet_base p x xs)
    (2*(length (packet_base p x xs)+packet_length (packet_prod p x))+6)
    (2*(length (packet_base p x xs)+packet_length (packet_prod p x))+3)
    (2*(length (packet_base p x xs)+packet_length (packet_prod p x))+1)
    (shifted_output_nat (length (packet_base p x xs)) p x)
    (packet_length (packet_prod p x)) [] RTnone.
Proof.
  intros Hphase. unfold packet_config,packet_side,sconfig.
  rewrite packet_length_app,(packet_parameters_successor p x xs Hphase).
  rewrite packet_base_length. cbn [length app D2s].
  repeat rewrite D2s_app. cbn [D2s]. repeat rewrite app_nil_r.
  repeat rewrite Str_app_assoc. f_equal; flia.
Qed.

Lemma offset_edge limit base a b c gen r pre e:
  3 <= a -> 2 <= b -> 1 <= c -> r < limit -> e <= 1 ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => 3 <= x) pre ->
  Forall (fun x => limit+3 <= x) base ->
  state_config base (SymState a b c gen r (pre++[e]) RTnone) -->+
  state_config base (edge_next (SymState a b c gen r (pre++[e]) RTnone) pre).
Proof.
  intros Ha Hb Hc Hr He Hgen Hpre Hbase.
  pose proof (sym_edge base
    (2*length base+a) (2*length base+b) (2*length base+c)
    (lift_gen (length base) gen) r pre e) as H.
  specialize (H ltac:(lia) ltac:(lia) ltac:(lia) He
    ltac:(apply lift_gen_forall; assumption)
    ltac:(eapply base_for_step; eassumption) Hpre).
  unfold state_config,edge_next. cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail].
  rewrite lift_gen_length in H.
  rewrite lift_gen_decs in H by
    (eapply Forall_impl; [|exact Hgen]; cbn; lia).
  cbn [lift_gen map] in H |- *. applys_eq H; flia.
Qed.

Lemma offset_two_last limit base a b c gen r pre:
  3 <= a -> 2 <= b -> 1 <= c -> r < limit ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => 3 <= x) pre ->
  Forall (fun x => limit+3 <= x) base ->
  state_config base (SymState a b c gen r (pre++[2%nat]) RTnone) -->+
  state_config base
    (two_last_next (SymState a b c gen r (pre++[2%nat]) RTnone) pre).
Proof.
  intros Ha Hb Hc Hr Hgen Hpre Hbase.
  pose proof (sym_two_last base
    (2*length base+a) (2*length base+b) (2*length base+c)
    (lift_gen (length base) gen) r pre) as H.
  specialize (H ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(apply lift_gen_forall; assumption)
    ltac:(eapply base_for_step; eassumption) Hpre).
  unfold state_config,two_last_next.
  cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail].
  rewrite lift_gen_length in H.
  rewrite lift_gen_decs in H by
    (eapply Forall_impl; [|exact Hgen]; cbn; lia).
  cbn [lift_gen map] in H |- *. applys_eq H; flia.
Qed.

Lemma offset_two_one limit base a b c gen r pre m:
  3 <= a -> 2 <= b -> 1 <= c -> r < limit -> pre <> [] ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => 3 <= x) pre ->
  Forall (fun x => limit+3 <= x) base ->
  state_config base (SymState a b c gen r (pre++[2%nat;m]) RTnone) -->+
  state_config base
    (two_one_next (SymState a b c gen r (pre++[2%nat;m]) RTnone) pre m).
Proof.
  intros Ha Hb Hc Hr Hne Hgen Hpre Hbase.
  pose proof (sym_two_one base
    (2*length base+a) (2*length base+b) (2*length base+c)
    (lift_gen (length base) gen) r pre m) as H.
  specialize (H ltac:(lia) ltac:(lia) ltac:(lia) Hne
    ltac:(apply lift_gen_forall; assumption)
    ltac:(eapply base_for_step; eassumption) Hpre).
  unfold state_config,two_one_next.
  cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail].
  rewrite lift_gen_length in H.
  rewrite lift_gen_decs in H by
    (eapply Forall_impl; [|exact Hgen]; cbn; lia).
  cbn [lift_gen map] in H |- *. applys_eq H; flia.
Qed.

Lemma offset_two_two limit base a b c gen r pre m u:
  3 <= a -> 2 <= b -> 1 <= c -> r < limit -> pre <> [] ->
  Forall (fun x => 3 <= x) gen ->
  Forall (fun x => 3 <= x) pre ->
  Forall (fun x => limit+3 <= x) base ->
  state_config base (SymState a b c gen r (pre++[2%nat;m;u]) RTnone) -->+
  state_config base
    (two_two_next (SymState a b c gen r (pre++[2%nat;m;u]) RTnone) pre m u).
Proof.
  intros Ha Hb Hc Hr Hne Hgen Hpre Hbase.
  pose proof (sym_two_two base
    (2*length base+a) (2*length base+b) (2*length base+c)
    (lift_gen (length base) gen) r pre m u) as H.
  specialize (H ltac:(lia) ltac:(lia) ltac:(lia) Hne
    ltac:(apply lift_gen_forall; assumption)
    ltac:(eapply base_for_step; eassumption) Hpre).
  unfold state_config,two_two_next.
  cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail].
  rewrite lift_gen_length in H.
  rewrite lift_gen_decs in H by
    (eapply Forall_impl; [|exact Hgen]; cbn; lia).
  cbn [lift_gen map] in H |- *. applys_eq H; flia.
Qed.

Lemma state_ok_spec limit s:
  state_ok limit s = true ->
  3 <= ss_a s /\ 2 <= ss_b s /\ 1 <= ss_c s /\
  ss_r s < limit /\ Forall (fun x => 3 <= x) (ss_gen s).
Proof.
  unfold state_ok. intros H.
  repeat rewrite Bool.andb_true_iff in H.
  rewrite Nat.leb_le,Nat.leb_le,Nat.leb_le,Nat.ltb_lt,all_ge_spec in H.
  exact H.
Qed.

Lemma sym_step_sound limit base s s':
  Forall (fun x => limit+3 <= x) base ->
  sym_step limit s = Some s' ->
  state_config base s -->+ state_config base s'.
Proof.
  intros Hbase Hstep. destruct s as [a b c gen r local tail].
  unfold sym_step in Hstep. cbn [ss_local] in Hstep.
  destruct (state_ok limit (SymState a b c gen r local tail)) eqn:Hok;
    [|discriminate].
  pose proof (state_ok_spec _ _ Hok) as [Ha [Hb [Hc [Hr Hgen]]]].
  destruct (low_split local) as [pre rest] eqn:Hsplit.
  pose proof (low_split_spec _ _ _ Hsplit) as [Hlocal [Hpre Hrest]].
  destruct rest as [|x xs].
  - destruct local as [|y ys]; cbn in Hstep; [discriminate|].
    inversion Hstep; subst s'.
    eapply offset_positive; eauto.
    + discriminate.
    + rewrite Hlocal,app_nil_r. exact Hpre.
  - destruct x as [|x].
    + destruct xs; [|discriminate]. destruct tail; cbn in Hstep; try discriminate.
      inversion Hstep; subst s'. rewrite Hlocal.
      eapply offset_edge; eauto; lia.
    + destruct x as [|x].
      * destruct xs; [|discriminate]. destruct tail; cbn in Hstep; try discriminate.
        inversion Hstep; subst s'. rewrite Hlocal.
        eapply offset_edge; eauto; lia.
      * destruct x as [|x].
        -- destruct xs as [|m xs].
           ++ destruct tail; cbn in Hstep; try discriminate.
              inversion Hstep; subst s'. rewrite Hlocal.
              eapply offset_two_last; eauto.
           ++ destruct xs as [|u xs].
              ** destruct pre as [|z pre']; destruct tail; cbn in Hstep;
                   try discriminate.
                 inversion Hstep; subst s'. rewrite Hlocal.
                 eapply offset_two_one; eauto; discriminate.
              ** destruct xs; [|discriminate].
                 destruct pre as [|z pre']; destruct tail; cbn in Hstep;
                   try discriminate.
                 inversion Hstep; subst s'. rewrite Hlocal.
                 eapply offset_two_two; eauto; discriminate.
        -- discriminate.
Qed.

Lemma sym_run_S_sound n limit base s s':
  Forall (fun x => limit+3 <= x) base ->
  sym_run (Datatypes.S n) limit s = Some s' ->
  state_config base s -->+ state_config base s'.
Proof.
  revert s. induction n as [|n IH]; intros s Hbase Hrun.
  - cbn [sym_run] in Hrun.
    destruct (sym_step limit s) as [s1|] eqn:Hstep; [|discriminate].
    inversion Hrun; subst. eapply sym_step_sound; eassumption.
  - cbn [sym_run] in Hrun.
    destruct (sym_step limit s) as [s1|] eqn:Hstep; [|discriminate].
    eapply progress_trans.
    + eapply sym_step_sound; eassumption.
    + eapply IH; eassumption.
Qed.

Definition service_start p x :=
  SymState (2*packet_t x+6) (2*packet_t x+3) (2*packet_t x+1)
    [] 0 (packet_local_nat p x) RTnone.

Definition service_end p x :=
  let k := packet_length (packet_prod p x) in
  SymState (2*k+6) (2*k+3) (2*k+1)
    (packet_output_nat p x) k [] RTnone.

Lemma packet_run_certificate p x:
  sym_run (packet_length (packet_prod p x))
    (packet_length (packet_prod p x)) (service_start p x) =
  Some (service_end p x).
Proof. destruct p,x; vm_compute; reflexivity. Qed.

Lemma packet_prod_length_positive p x:
  0 < packet_length (packet_prod p x).
Proof. destruct p,x; vm_compute; lia. Qed.

Lemma packet_service_symbolic p x base:
  Forall (fun q => packet_length (packet_prod p x)+3 <= q) base ->
  sconfig base
    (2*(length base+packet_t x)+6)
    (2*(length base+packet_t x)+3)
    (2*(length base+packet_t x)+1)
    [] 0 (packet_local_nat p x) RTnone -->+
  sconfig base
    (2*(length base+packet_length (packet_prod p x))+6)
    (2*(length base+packet_length (packet_prod p x))+3)
    (2*(length base+packet_length (packet_prod p x))+1)
    (shifted_output_nat (length base) p x)
    (packet_length (packet_prod p x)) [] RTnone.
Proof.
  intros Hbase.
  pose proof (packet_prod_length_positive p x) as Hpos.
  assert (HL: Datatypes.S (Nat.pred (packet_length (packet_prod p x))) =
    packet_length (packet_prod p x)) by lia.
  pose proof (sym_run_S_sound
    (Nat.pred (packet_length (packet_prod p x)))
    (packet_length (packet_prod p x)) base
    (service_start p x) (service_end p x) Hbase) as H.
  specialize (H ltac:(rewrite HL; apply packet_run_certificate)).
  unfold state_config,service_start,service_end in H.
  cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail] in H.
  unfold lift_gen,shifted_output_nat in H |- *.
  applys_eq H; flia.
Qed.

Lemma packet_transition p x xs:
  phase_sum (x::xs) = phase_bit p ->
  packet_config (x::xs) -->+ packet_config (xs++packet_prod p x).
Proof.
  intros Hphase.
  rewrite (packet_config_cons p x xs Hphase).
  rewrite (packet_config_successor p x xs Hphase).
  apply packet_service_symbolic,packet_base_lower.
Qed.

Lemma packet_successor_valid p x xs:
  phase_sum (x::xs) = phase_bit p ->
  valid_packets (xs++packet_prod p x).
Proof.
  intros Hphase. split.
  - intros Hnil. apply app_eq_nil in Hnil as [_ Hprod].
    apply (packet_prod_nonempty p x Hprod).
  - rewrite (packet_successor_phase p x xs Hphase).
    destruct (packet_next_parity p x); cbn [phase_bit]; tauto.
Qed.

Lemma valid_packet_progress ys:
  valid_packets ys ->
  exists ys', valid_packets ys' /\ packet_config ys -->+ packet_config ys'.
Proof.
  intros [Hne [Hphase|Hphase]].
  - destruct ys as [|x xs]; [contradiction|].
    exists (xs++packet_prod false x). split.
    + apply packet_successor_valid. exact Hphase.
    + apply packet_transition. exact Hphase.
  - destruct ys as [|x xs]; [contradiction|].
    exists (xs++packet_prod true x). split.
    + apply packet_successor_valid. exact Hphase.
    + apply packet_transition. exact Hphase.
Qed.

Definition flatten_state s :=
  SymState (ss_a s) (ss_b s) (ss_c s) [] (ss_r s)
    (ss_gen s++ss_local s) (ss_tail s).

Definition empty_next s :=
  SymState 6 (ss_a s-1) (ss_b s-2) [] (S (ss_r s))
    ([ss_c s]++reset_tail_extra (ss_tail s))
    (reset_tail_next (ss_tail s)).

Definition initial_step limit s : option sym_state :=
  match ss_gen s with
  | _::_ => None
  | [] =>
      match ss_local s with
      | [] => if state_ok limit s then Some (empty_next s) else None
      | _::_ =>
          match sym_step limit s with
          | Some s' => Some (flatten_state s')
          | None => None
          end
      end
  end.

Fixpoint initial_run (n limit:nat) s : option sym_state :=
  match n with
  | O => Some s
  | Datatypes.S n =>
      match initial_step limit s with
      | Some s' => initial_run n limit s'
      | None => None
      end
  end.

Lemma flatten_state_config s:
  state_config [] (flatten_state s) = state_config [] s.
Proof.
  destruct s. unfold state_config,flatten_state,sconfig.
  cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail lift_gen subns map
    length Nat.mul Nat.add]. rewrite map_id.
  repeat rewrite D2s_app. cbn [D2s]. repeat rewrite app_nil_r.
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma initial_empty_sound limit a b c r tail:
  3 <= a -> 2 <= b -> 1 <= c -> r < limit ->
  state_config [] (SymState a b c [] r [] tail) -->+
  state_config [] (empty_next (SymState a b c [] r [] tail)).
Proof.
  intros Ha Hb Hc Hr.
  pose proof (reset_positive a b c [] tail Ha Hb Hc ltac:(constructor)) as H.
  unfold state_config,empty_next,sconfig.
  cbn [ss_a ss_b ss_c ss_gen ss_r ss_local ss_tail lift_gen subns map
    length scan_values last_down].
  repeat rewrite app_nil_r in H |- *. applys_eq H; flia.
Qed.

Lemma initial_step_sound limit s s':
  initial_step limit s = Some s' ->
  state_config [] s -->+ state_config [] s'.
Proof.
  destruct s as [a b c gen r local tail]. intros Hstep.
  unfold initial_step in Hstep. cbn [ss_gen ss_local] in Hstep.
  destruct gen as [|g gen]; [|discriminate]. destruct local as [|q local].
  - destruct (state_ok limit (SymState a b c [] r [] tail)) eqn:Hok;
      [|discriminate].
    inversion Hstep; subst s'.
    pose proof (state_ok_spec _ _ Hok) as [Ha [Hb [Hc [Hr _]]]].
    eapply initial_empty_sound; eassumption.
  - destruct (sym_step limit (SymState a b c [] r (q::local) tail))
      as [s1|] eqn:Hsym; [|discriminate].
    inversion Hstep; subst s'. rewrite flatten_state_config.
    eapply sym_step_sound; [constructor|exact Hsym].
Qed.

Lemma initial_run_S_sound n limit s s':
  initial_run (Datatypes.S n) limit s = Some s' ->
  state_config [] s -->+ state_config [] s'.
Proof.
  revert s. induction n as [|n IH]; intros s Hrun.
  - cbn [initial_run] in Hrun.
    destruct (initial_step limit s) as [s1|] eqn:Hstep; [|discriminate].
    inversion Hrun; subst. eapply initial_step_sound; eassumption.
  - cbn [initial_run] in Hrun.
    destruct (initial_step limit s) as [s1|] eqn:Hstep; [|discriminate].
    eapply progress_trans.
    + eapply initial_step_sound; eassumption.
    + eapply IH; eassumption.
Qed.

Definition initial_reset_state :=
  SymState 8 5 7 [] 0 [6] RTnone.

Definition first_packet_state :=
  SymState 90 87 85 [] 80 (packet_local0 P42_21) RTnone.

Lemma initial_reset_certificate:
  initial_run 80 80 initial_reset_state = Some first_packet_state.
Proof. vm_compute; reflexivity. Qed.

Lemma initial_reset_bridge:
  state_config [] initial_reset_state -->+ state_config [] first_packet_state.
Proof.
  eapply initial_run_S_sound with (n:=79) (limit:=80).
  exact initial_reset_certificate.
Qed.

Lemma initial_reset_config:
  S' (3,D1 8 *> D1 5 *> D1 7 *> D2 6 *> 0inf) =
  state_config [] initial_reset_state.
Proof. reflexivity. Qed.

Lemma first_packet_config:
  state_config [] first_packet_state = packet_config [P42_21].
Proof. vm_compute; reflexivity. Qed.

Lemma packet_nonhalt:
  ~halts tm (packet_config [P42_21]).
Proof.
  apply progress_nonhalt_cond with
    (i0:=[P42_21]) (C:=packet_config) (P:=valid_packets).
  - intros ys Hvalid. destruct (valid_packet_progress ys Hvalid)
      as [ys' [Hvalid' Hprogress]].
    exists ys'. split; assumption.
  - split; [discriminate|]. left. vm_compute. reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [|exact packet_nonhalt].
  eapply evstep_trans; [exact init|].
  apply progress_evstep.
  rewrite initial_reset_config,<-first_packet_config.
  exact initial_reset_bridge.
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0LC1LB_1RD0LA_1RA---_1RA1RF_0RE1RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition to_old_state (q:Q) : Q :=
  match q with
  | A => C | B => D | C => A | D => B | E => E | F => F
  end.

Lemma tm_state_renaming: state_renaming tm TM1.tm to_old_state.
Proof. intros q s. destruct q,s; reflexivity. Qed.

Definition bridge_config : Q*tape :=
  TM1.S' (3,TM1.D1 6 *> TM1.D1 5 *> TM1.D1 7 *> TM1.D2 7 *> 0inf).

Lemma init: c0 -->* bridge_config.
Proof. unfold bridge_config. esx. Qed.

Definition reset_state := TM1.SymState 6 5 7 [] 0 [7] TM1.RTnone.
Definition packets : list TM1.packet_type := [TM1.P17_8;TM1.P2_1].
Definition packet_state :=
  TM1.SymState 44 41 39 [] 35 (TM1.packet_parameters packets) TM1.RTnone.

Lemma reset_certificate:
  TM1.initial_run 35 35 reset_state = Some packet_state.
Proof. vm_compute. reflexivity. Qed.

Lemma reset_bridge:
  TM1.state_config [] reset_state -[TM1.tm]->+ TM1.state_config [] packet_state.
Proof. eapply TM1.initial_run_S_sound with (n:=34) (limit:=35).
  exact reset_certificate.
Qed.

Lemma reset_config:
  bridge_config = TM1.state_config [] reset_state.
Proof. reflexivity. Qed.

Lemma packet_config:
  TM1.state_config [] packet_state = TM1.packet_config packets.
Proof. vm_compute. reflexivity. Qed.

Lemma packets_valid: TM1.valid_packets packets.
Proof. split; [discriminate|]. right. vm_compute. reflexivity. Qed.

Lemma packets_nonhalt xs:
  TM1.valid_packets xs -> ~halts TM1.tm (TM1.packet_config xs).
Proof.
  intros Hvalid.
  apply progress_nonhalt_cond with
    (i0:=xs) (C:=TM1.packet_config) (P:=TM1.valid_packets).
  - intros ys Hyvalid. destruct (TM1.valid_packet_progress ys Hyvalid)
      as [ys' [Hyvalid' Hprogress]].
    exists ys'. split; assumption.
  - exact Hvalid.
Qed.

Lemma old_bridge_nonhalt: ~halts TM1.tm bridge_config.
Proof.
  eapply multistep_nonhalt; [|apply packets_nonhalt,packets_valid].
  apply progress_evstep.
  rewrite reset_config,<-packet_config.
  exact reset_bridge.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init|].
  eapply rename_nonhalt; [exact tm_state_renaming|].
  change (~halts TM1.tm bridge_config).
  exact old_bridge_nonhalt.
Qed.

End TM2.
