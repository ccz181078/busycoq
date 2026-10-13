(* The 23 completed proofs for BEC.txt: 22 nonhalting machines and TM5,
   which halts.  Machine numbers follow BEC.txt; TM4 is proved separately
   in BusyCoq.BECv9 and is not part of this file.
   Each tm is the original machine or its left/right mirror, without
   permuting states.  Only existing BusyCoq and standard libraries are used. *)
From BusyCoq Require Import Individual62 Longitudinal LongitudinalHalt
  ES_v3 DivModCases Eqb FastRev.
Require Import ZifyNat Lia Arith List String NArith PArith ZArith
  Wellfounded.Inverse_Image.

(* BEC.txt TM1/TM2; see BEC_LONG13_ANALYSIS.txt. *)

Unset Implicit Arguments.

Module Long13.
Inductive digit := U | Z | O.
Definition word d : list Sym :=
  match d with U => [1;1;0] | Z => [0;0] | O => [1;0] end.
Fixpoint tape r : side :=
  match r with [] => 0inf | d::r => word d *> tape r end.
Fixpoint potential r : nat :=
  match r with
  | [] => 0
  | U::r => Nat.max 2 (potential r - 2)
  | Z::r => potential r * 2
  | O::r => 1 + potential r * 2
  end.
Definition prepend k r := repeat U k ++ r.
Notation hR := (A,<[1]).
Notation hL := (E,[0]).
Notation h := [(hR,hL)].
Definition left1 a b := 0inf <* <[1] <* <[1;1;1]^^a <* <[1;0;1]^^b.
Definition left2 a b := 0inf <* <[1;1] <* <[1;1;1]^^a <* <[1;0;1]^^b.
Definition state n r := left1 0 n {{{ (hL,L) }}} tape r.

Record Rules (tm:TM) : Prop := {
  rule_U: segRLs tm h h (word U) (word U);
  rule_Z: segRLs tm h [] (word Z) (word O);
  rule_O: segRLs tm h h (word O) (word Z);
  rule_nil: sideRLs tm h 0inf (word O *> 0inf);
  rule_shiftZ: forall k, segRLs tm (h^^2) (h^^(1+k))
    ([0] ++ word U^^k ++ [0]) (word Z ++ word U^^k);
  rule_shiftO: forall k, segRLs tm (h^^2) (h^^(1+k))
    ([0] ++ word U^^k ++ word O) (word U^^(1+k));
  rule_shortO: segRLs tm h [] ([0] ++ word O) (word U);
  rule_L1: forall a b r, left1 (1+a) b {{{ (hL,L) }}} r -[tm]->*
    left1 a (1+b) {{{ (hR,R) }}} r;
  rule_L2: forall a b r, left2 (1+a) b {{{ (hL,L) }}} r -[tm]->*
    left2 a (1+b) {{{ (hR,R) }}} r;
  rule_L20: forall b r, left2 0 b {{{ (hL,L) }}} r -[tm]->*
    left1 0 b {{{ (hR,R) }}} r;
  rule_LZ: forall b k r,
    left1 0 b {{{ (hL,L) }}} word U^^k *> word Z *> r -[tm]->*
    left1 (1+k+b) 0 {{{ (hR,R) }}} [0] *> r;
  rule_LO: forall b k r,
    left1 0 b {{{ (hL,L) }}} word U^^k *> word O *> r -[tm]->*
    left2 (1+k+b) 0 {{{ (hR,R) }}} r
}.

Lemma tape_prepend k r: tape (prepend k r) = word U^^k *> tape r.
Proof.
  unfold prepend; induction k; cbn[repeat app tape lpow]; [reflexivity|].
  rewrite Str_app_assoc, IHk; reflexivity.
Qed.

Lemma potential_prepend k r:
  potential (prepend (1+k) r) = Nat.max 2 (potential r - (1+k)*2).
Proof.
  induction k; [reflexivity|].
  change (Nat.max 2 (potential (prepend (1+k) r)-2) =
    Nat.max 2 (potential r - (1+S k)*2)).
  rewrite IHk; lia.
Qed.

Lemma potential_bound k r:
  potential r <= potential (prepend k r) + k*2.
Proof. destruct k; [cbn[prepend repeat app]; lia|rewrite potential_prepend; lia]. Qed.

Lemma prepend_U k r: prepend k (U::r) = prepend (1+k) r.
Proof. unfold prepend; induction k; cbn[Nat.add repeat app] in *; congruence. Qed.

Inductive Inc : list digit -> list digit -> Prop :=
| Inc_nil: Inc [] [O]
| Inc_Z r: Inc (Z::r) (O::r)
| Inc_O r r': Inc r r' -> Inc (O::r) (Z::r')
| Inc_U r r': Inc r r' -> Inc (U::r) (U::r').

Lemma Inc_total r: exists r', Inc r r' /\
  potential r' <= 1+potential r /\ In O r'.
Proof.
  induction r as [|d r [r' [I [V B]]]].
  - exists [O]; repeat split; [constructor|cbn[potential]; lia|left; reflexivity].
  - destruct d.
    + exists (U::r'); repeat split; [constructor; assumption|cbn[potential]; lia|right; assumption].
    + exists (O::r); repeat split; [constructor|cbn[potential]; lia|left; reflexivity].
    + exists (Z::r'); repeat split; [constructor; assumption|cbn[potential]; lia|right; assumption].
Qed.

(* The unbounded family is a finite forward scan, k left emissions, and
   a finite return scan. The words here are stored nearest to the head first. *)
Lemma emissions tm
  (step: forall a b s, segLR tm hL hR
    (<[1;0;1]^^b ++ <[1;1;1]^^(1+a) ++ s)
    (<[1;0;1]^^(1+b) ++ <[1;1;1]^^a ++ s)) a:
  forall b s, segLRs tm ([(hL,hR)]^^a)
    (<[1;0;1]^^b ++ <[1;1;1]^^a ++ s)
    (<[1;0;1]^^(a+b) ++ s).
Proof.
  induction a; intros b s.
  - cbn[Nat.add lpow app]; constructor.
  - replace (S a+b) with (a+(1+b)) by lia.
    cbn[lpow app]; econstructor; [apply step|apply IHa].
Qed.

Lemma bounce tm k w1 w2 w3 w4:
  segRR tm hR hR w1 w3 ->
  segLRs tm ([(hL,hR)]^^k) w3 w4 ->
  segLL tm hL hL w4 w2 -> segRLs tm h (h^^(1+k)) w1 w2.
Proof.
  intros RR LR LL.
  rewrite <-lrcons_lpow1 by lia.
  replace (1+k-1) with k by lia.
  epose proof (@segRLs_lrcons tm ([(hL,hR)]^^k) [] []
    w1 w2 w3 w4 w2 hR hL hR hL RR LL LR (segRLs_O tm w2)) as H.
  rewrite app_nil_r in H; exact H.
Qed.

Ltac shift_rule_body tm0 k ending base :=
  cbn[word];
  eapply segRLs_S with (w2:=[1] ++ [1;1;0]^^k ++ ending);
  [ intros l r; es |
    eapply bounce with (w3:=<[1;1;1]^^k ++ base) (w4:=<[1;0;1]^^k ++ base);
    [ intros l r; es |
      let L := fresh "L" in
      assert (L: forall a b s, segLR tm0 hL hR
        (<[1;0;1]^^b ++ <[1;1;1]^^(1+a) ++ s)
        (<[1;0;1]^^(1+b) ++ <[1;1;1]^^a ++ s)) by
        (intros a b s l r; es);
      applys_eq (emissions tm0 L k 0%nat base); flia |
      intros l r; es ] ].

Section Machine.
Context {tm:TM} (rules:Rules tm).
Local Hint Resolve rule_U rule_Z rule_O rule_nil rule_shiftZ rule_shiftO
  rule_shortO : core.

Lemma Inc_spec r r': Inc r r' -> sideRLs tm h (tape r) (tape r').
Proof.
  intro H; induction H; cbn[tape].
  - eauto.
  - eapply segRLs_sideRLs_concat; [eauto|constructor].
  - eapply segRLs_sideRLs_concat; eauto.
  - eapply segRLs_sideRLs_concat; eauto.
Qed.

Lemma incs_total m r: exists r', sideRLs tm (h^^m) (tape r) (tape r') /\
  potential r' <= m+potential r /\ (0<m -> In O r').
Proof.
  induction m.
  - exists r; repeat split; [constructor|lia|lia].
  - destruct IHm as [r' [H [V B]]].
    destruct (Inc_total r') as [r'' [I [V' B']]].
    exists r''; repeat split; [|lia|auto].
    eapply sideRLs_trans_S; [eassumption|apply Inc_spec; assumption].
Qed.

Lemma U_pass n k: segRLs tm (h^^n) (h^^n) (word U^^k) (word U^^k).
Proof.
  induction k; cbn[lpow]; [apply segRLs_nil|].
  eapply segRLs_concat; [eapply segRLs_wall''; eauto|assumption].
Qed.

Lemma Z_even n: segRLs tm (h^^(n*2)) (h^^n) (word Z) (word Z).
Proof.
  induction n; [constructor|].
  cbn[Nat.mul]; rewrite lpow_add; cbn[lpow].
  eapply segRLs_trans; [|apply IHn].
  apply (@segRLs_trans tm h [] h h (word Z) (word O) (word Z)); eauto.
Qed.

Lemma Z_odd n: segRLs tm (h^^(1+n*2)) (h^^n) (word Z) (word O).
Proof.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add.
  replace (h^^n) with (h^^n++[]) by apply app_nil_r.
  eapply segRLs_trans; [apply Z_even|cbn; eauto].
Qed.

Lemma shiftZ_even k n:
  segRLs tm (h^^(2+n*2)) (h^^(1+k+n))
    ([0] ++ word U^^k ++ [0]) (word Z ++ word U^^k).
Proof.
  eapply segRLs_trans_add; [eauto|].
  eapply segRLs_concat; [apply Z_even|apply U_pass].
Qed.

Lemma shiftZ_odd k n:
  segRLs tm (h^^(3+n*2)) (h^^(1+k+n))
    ([0] ++ word U^^k ++ [0]) (word O ++ word U^^k).
Proof.
  change (3+n*2) with (2+(1+n*2)).
  eapply segRLs_trans_add; [eauto|].
  eapply segRLs_concat; [apply Z_odd|apply U_pass].
Qed.

Lemma shiftO k n:
  segRLs tm (h^^(2+n)) (h^^(1+k+n))
    ([0] ++ word U^^k ++ word O) (word U^^(1+k)).
Proof. eapply segRLs_trans_add; [eauto|apply U_pass]. Qed.

Definition Normalized r m := exists r',
  sideRLs tm (h^^m) ([0] *> tape r) (tape r') /\
  potential r' <= m+potential r.

Lemma normalize_empty m: Normalized [] m.
Proof.
  destruct (incs_total m []) as [r' [H [V B]]]; exists r'; split; [|exact V].
  cbn[tape Str_app]; rewrite <-const_unfold; exact H.
Qed.

Lemma normalize_Z r:
  (forall m, potential r <= m -> Normalized r m) ->
  forall k m, potential (prepend k (Z::r)) <= m ->
  Normalized (prepend k (Z::r)) m.
Proof.
  intros IH k m B; destruct k as [|k].
  - cbn[prepend repeat app potential] in B.
    destruct (mod2 m) as [q E|q E]; subst m;
      destruct (IH q) as [r' [H V]]; try lia.
    + exists (Z::r'); split; [|cbn[prepend repeat app potential]; lia].
      change (sideRLs tm (h^^(q*2)) (word Z *> [0] *> tape r) (word Z *> tape r')).
      eapply segRLs_sideRLs_concat; [apply Z_even|assumption].
    + exists (O::r'); split; [|cbn[prepend repeat app potential]; lia].
      change (sideRLs tm (h^^(1+q*2)) (word Z *> [0] *> tape r) (word O *> tape r')).
      eapply segRLs_sideRLs_concat; [apply Z_odd|assumption].
  - rewrite potential_prepend in B.
    destruct (sub m 2) as [p E|E]; [subst m|lia].
    destruct (mod2 p) as [q E|q E]; subst p;
      destruct (IH (1+(1+k)+q)) as [r' [H V]]; cbn[potential] in B; try lia.
    + exists (Z::prepend (1+k) r'); split.
      * rewrite tape_prepend; cbn[tape]; rewrite tape_prepend.
        applys_eq (segRLs_sideRLs_concat (shiftZ_even (1+k) q) H); st; reflexivity.
      * cbn[potential]; rewrite !potential_prepend; cbn[potential]; lia.
    + exists (O::prepend (1+k) r'); split.
      * rewrite tape_prepend; cbn[tape]; rewrite tape_prepend.
        applys_eq (segRLs_sideRLs_concat (shiftZ_odd (1+k) q) H); st; reflexivity.
      * cbn[potential]; rewrite !potential_prepend; cbn[potential]; lia.
Qed.

Lemma normalize_O r k m:
  potential (prepend k (O::r)) <= m -> Normalized (prepend k (O::r)) m.
Proof.
  intro B; destruct k as [|k].
  - cbn[prepend repeat app potential] in B; destruct m as [|m]; [lia|].
    destruct (incs_total m r) as [r' [H [V I]]].
    exists (U::r'); split; [|cbn[prepend repeat app potential]; lia].
    change (h^^(S m)) with (h++h^^m).
    eapply @sideRLs_trans with (r2:=word U *> tape r).
    + change (sideRLs tm h (([0]++word O) *> tape r) (word U *> tape r)).
      eapply segRLs_sideRLs_concat; [eauto|constructor].
    + cbn[tape]; eapply segRLs_sideRLs_concat; [eapply segRLs_wall''; eauto|assumption].
  - rewrite potential_prepend in B.
    destruct (sub m 2) as [p E|E]; [subst m|lia].
    destruct (incs_total (1+(1+k)+p) r) as [r' [H [V I]]].
    exists (prepend (1+(1+k)) r'); split.
    + rewrite !tape_prepend; cbn[tape].
      applys_eq (segRLs_sideRLs_concat (shiftO (1+k) p) H); st; reflexivity.
    + rewrite !potential_prepend; cbn[potential] in *; lia.
Qed.

Lemma normalize r: forall k m, potential (prepend k r) <= m ->
  Normalized (prepend k r) m.
Proof.
  induction r as [|d r IH]; intros k m B.
  - assert (H: Normalized (prepend k [Z]) m).
    { apply normalize_Z; [intros; apply normalize_empty|].
      destruct k; [cbn[prepend repeat app potential] in *; lia|].
      rewrite potential_prepend in *; cbn[potential] in *; lia. }
    destruct H as [r' [H V]]; exists r'; split.
    + rewrite tape_prepend in *; cbn[tape word Str_app] in H |- *.
      repeat rewrite <-const_unfold in H; exact H.
    + destruct k; [exact V|].
      rewrite potential_prepend in *; cbn[potential] in *; exact V.
  - destruct d.
    + rewrite prepend_U in *; apply IH; assumption.
    + apply normalize_Z; [apply (IH 0%nat)|assumption].
    + apply normalize_O; assumption.
Qed.

Lemma normalize_positive r m: potential r < m -> exists r',
  sideRLs tm (h^^m) ([0] *> tape r) (tape r') /\
  potential r' <= m+potential r /\ In O r'.
Proof.
  intro B; destruct m as [|m]; [lia|].
  destruct (normalize r 0%nat m) as [r' [H V]]; [cbn[prepend repeat app]; lia|].
  cbn[prepend repeat app] in H,V.
  destruct (Inc_total r') as [r'' [I [V' B']]].
  exists r''; repeat split; [|lia|assumption].
  eapply sideRLs_trans_S; [exact H|apply Inc_spec; assumption].
Qed.

Lemma left1_calls a: forall b r r', sideRLs tm (h^^a) r r' ->
  left1 a b {{{ (hL,L) }}} r -[tm]->*
  left1 0 (b+a) {{{ (hL,L) }}} r'.
Proof.
  induction a; intros b r r' H.
  - inversion H; subst; rewrite Nat.add_0_r; finish.
  - change (h^^(S a)) with (h++h^^a) in H.
    destruct (sideRLs_split H) as [s [H1 Ha]].
    replace (b+S a) with (1+b+a) by lia.
    follow (rule_L1 _ rules a b r).
    follow100 (sideRLs_1 _ _ _ _ _ H1 (left1 a (1+b))).
    apply IHa; assumption.
Qed.

Lemma left2_calls a: forall b r r', sideRLs tm (h^^(1+a)) r r' ->
  left2 a b {{{ (hL,L) }}} r -[tm]->*
  left1 0 (b+a) {{{ (hL,L) }}} r'.
Proof.
  induction a; intros b r r' H.
  - rewrite Nat.add_0_r; follow (rule_L20 _ rules b r).
    apply progress_evstep, sideRLs_1; exact H.
  - change (h^^(1+S a)) with (h++h^^(1+a)) in H.
    destruct (sideRLs_split H) as [s [H1 Ha]].
    replace (b+S a) with (1+b+a) by lia.
    follow (rule_L2 _ rules a b r).
    follow100 (sideRLs_1 _ _ _ _ _ H1 (left2 a (1+b))).
    apply IHa; assumption.
Qed.

Lemma left1_send a b r r': sideRLs tm (h^^(1+a)) r r' ->
  left1 a b {{{ (hR,R) }}} r -[tm]->+
  left1 0 (b+a) {{{ (hL,L) }}} r'.
Proof.
  intro H; change (h^^(1+a)) with (h++h^^a) in H.
  destruct (sideRLs_split H) as [s [H1 Ha]].
  follow10 (sideRLs_1 _ _ _ _ _ H1 (left1 a b)).
  apply left1_calls; assumption.
Qed.

Lemma left2_send a b r r': sideRLs tm (h^^(2+a)) r r' ->
  left2 a b {{{ (hR,R) }}} r -[tm]->+
  left1 0 (b+a) {{{ (hL,L) }}} r'.
Proof.
  intro H; change (h^^(2+a)) with (h++h^^(1+a)) in H.
  destruct (sideRLs_split H) as [s [H1 Ha]].
  follow10 (sideRLs_1 _ _ _ _ _ H1 (left2 a b)).
  apply left2_calls; assumption.
Qed.

Lemma first_digit r: In O r -> exists k d t,
  r=prepend k (d::t) /\ (d=Z \/ d=O).
Proof.
  induction r as [|d r IH]; intro H; [contradiction|].
  destruct d.
  - destruct H as [H|H]; [discriminate|].
    destruct (IH H) as [k [d [t [E D]]]].
    exists (1+k),d,t; split; [cbn[prepend repeat app]; rewrite E; reflexivity|assumption].
  - exists 0%nat,Z,r; split; [reflexivity|auto].
  - exists 0%nat,O,r; split; [reflexivity|auto].
Qed.

Lemma next n r: In O r -> potential r <= n*2 -> exists n' r',
  state n r -[tm]->+ state n' r' /\ In O r' /\ potential r' <= n'*2.
Proof.
  intros I B; destruct (first_digit r I) as [k [d [t [E D]]]]; subst r.
  pose proof (potential_bound k (d::t)) as V.
  destruct D as [D|D]; subst d; cbn[potential] in V.
  - destruct (normalize_positive t (2+k+n)) as [r' [H [V' I']]]; [lia|].
    exists (1+k+n),r'; repeat split; [|assumption|lia].
    unfold state; rewrite tape_prepend; cbn[tape].
    eapply evstep_progress_trans; [apply (rule_LZ _ rules)|].
    apply (left1_send (1+k+n) 0%nat); exact H.
  - destruct (incs_total (3+k+n) t) as [r' [H [V' I']]].
    exists (1+k+n),r'; repeat split; [|apply I'; lia|lia].
    unfold state; rewrite tape_prepend; cbn[tape].
    eapply evstep_progress_trans; [apply (rule_LO _ rules)|].
    apply (left2_send (1+k+n) 0%nat); exact H.
Qed.

Lemma nonhalt_from n r: In O r -> potential r <= n*2 -> ~halts tm (state n r).
Proof.
  intros I B.
  eapply progress_nonhalt_cond with
    (i0:=(n,r)) (C:=fun '(n,r) => state n r)
    (P:=fun '(n,r) => In O r /\ potential r<=n*2).
  - intros [a s] [I' B']; destruct (next a s I' B') as [a' [s' H]].
    exists (a',s'); exact H.
  - split; assumption.
Qed.

End Machine.
End Long13.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LE_1RA1RD_1RA1RF_0LB1LA_1RC---").
Import Long13.
Lemma rules: Rules tm.
Proof.
  constructor; intros.
  - esx.
  - esx.
  - esx.
  - esx.
  - shift_rule_body tm k [0] <[1;0].
  - shift_rule_body tm k [1;0] <[1;0;1].
  - esx.
  - unfold left1; es.
  - unfold left2; es.
  - unfold left1,left2; es.
  - unfold left1; cbn[word]; es.
  - unfold left1,left2; cbn[word]; es.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state 1 [U;O]).
  - unfold state,left1; cbn[tape word]; esx.
  - apply (nonhalt_from rules); cbn; auto.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LE_1RA1RD_1RA1RB_0LF1LA_---0LE").
Import Long13.
Lemma rules: Rules tm.
Proof.
  constructor; intros.
  - esx.
  - esx.
  - esx.
  - esx.
  - shift_rule_body tm k [0] <[1;0].
  - shift_rule_body tm k [1;0] <[1;0;1].
  - esx.
  - unfold left1; es.
  - unfold left2; es.
  - unfold left1,left2; es.
  - unfold left1; cbn[word]; es.
  - unfold left1,left2; cbn[word]; es.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state 1 [U;O]).
  - unfold state,left1; cbn[tape word]; esx.
  - apply (nonhalt_from rules); cbn; auto.
Qed.
End TM2.

(* BEC.txt TM5, not the older BEC5[a-f] family. *)
Set Implicit Arguments.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1LC0LA_0RD0LB_1RA0RE_1RC1RF_0RC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation U := [1;0;0].
Notation Z := [0;0;0].
Notation O := [1;0;1].
Notation P := [0;0;1].
Notation h := [((C,[0]),(C,[1]))].
Notation g := [((E,[0;0]),(C,[1]))].
Notation j := [((D,[0;0]),(C,[1]))].
Notation e := [((E,[0;0;0]),(C,[1]))].
Notation q := [((D,[0]),(C,[1]))].
Notation qb := [((D,[0]),(B,[1]))].

Ltac sr := apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Lemma H0: segRLs tm h j [0] []. Proof. sr. Qed.
Lemma H1: segRLs tm h [] [1] [0]. Proof. sr. Qed.
Lemma J1: segRLs tm j e [1] []. Proof. sr. Qed.
Lemma QB00: segRLs tm qb [] [0;0] [0;1]. Proof. sr. Qed.
Lemma Q01: segRLs tm q h [0;1] [0;1]. Proof. sr. Qed.
Lemma QU: segRLs tm q q U U. Proof. sr. Qed.
Lemma QUB: segRLs tm q qb U O. Proof. sr. Qed.
Lemma QO: segRLs tm q [] O U. Proof. sr. Qed.
Lemma Q110: segRLs tm q h [1;1;0] U. Proof. sr. Qed.
Lemma GU: segRLs tm g j U U. Proof. sr. Qed.
Lemma JU: segRLs tm j (q++j) U U. Proof. sr. Qed.
Lemma JO: segRLs tm j j O U. Proof. sr. Qed.
Lemma J110: segRLs tm j (h++j) [1;1;0] U. Proof. sr. Qed.


Lemma G11 l r: halts tm (l <* [0;0] {{E}}> [1;1] *> r).
Proof. esx. Qed.
Lemma L11 l r: halts tm (l <* [0;0;0] {{E}}> [1;1] *> r).
Proof. esx. Qed.
Lemma Q111 l r: halts tm (l <* [0] {{D}}> [1;1;1] *> r).
Proof. esx. Qed.

Lemma Qrun a: segRLs tm q q (U^^a) (U^^a).
Proof. induction a; [apply segRLs_nil|cbn[lpow]; eapply segRLs_concat; eauto using QU]. Qed.
Lemma Qrun01 a: segRLs tm q h (U^^a++[0;1]) (U^^a++[0;1]).
Proof. eapply segRLs_concat; eauto using Qrun,Q01. Qed.
Lemma T01 a: segRLs tm j (h^^(1+a)) (U^^a++[0;1]) (U^^(1+a)).
Proof.
  induction a; [sr|].
  change (segRLs tm j (h++h^^(1+a)) (U++(U^^a++[0;1])) (U++U^^(1+a))).
  eapply segRLs_concat; [apply JU|].
  eapply segRLs_trans; [apply Qrun01|exact IHa].
Qed.

Lemma QrunO a: segRLs tm q [] (U^^a++O) (U^^(1+a)).
Proof. applys_eq (segRLs_concat (Qrun a) QO); symmetry; apply lpow_shift. Qed.
Lemma Qrun00 a: segRLs tm q [] (U^^(1+a)++[0;0]) (U^^a++O++[0;1]).
Proof.
  replace (U^^(1+a)) with (U^^a++U) by (apply lpow_shift).
  rewrite <-app_assoc.
  eapply segRLs_concat; [apply Qrun|].
  exact (segRLs_concat QUB QB00).
Qed.

Inductive result (X:Type) := Failed | Stopped | Returned (x:X).
Arguments Failed {X}. Arguments Stopped {X}. Arguments Returned {X} _.
Definition map_result {X Y} (f:X->Y) (o:result X):result Y := match o with
  | Failed=>Failed | Stopped=>Stopped | Returned x=>Returned (f x) end.
Definition then_result {X Y} (o:result X) (f:X->result Y):result Y := match o with
  | Failed=>Failed | Stopped=>Stopped | Returned x=>f x end.
Definition Spec {X} (den:X->side) hs r (o:result X) := match o with
  | Failed=>True | Stopped=>sideRLs_halt tm hs r
  | Returned x=>sideRLs tm hs r (den x) end.

Lemma rule_spec {X} (den:X->side) hs hs' w v r o:
  segRLs tm hs hs' w v -> Spec den hs' r o ->
  Spec (fun x=>v *> den x) hs (w *> r) o.
Proof.
  intros R H; destruct o; cbn[Spec] in *;
    eauto using segRLs_sideRLs_concat,segRLs_sideRLs_halt_concat.
Qed.

Lemma lift_rule {X Y} (dx:X->side) (dy:Y->side) hs hs' w v r o f:
  segRLs tm hs hs' w v -> (forall x,dy(f x)=v *> dx x) ->
  Spec dx hs' r o -> Spec dy hs (w *> r) (map_result f o).
Proof.
  intros R F H; destruct o; cbn[Spec map_result] in *; [trivial| |].
  - eapply segRLs_sideRLs_halt_concat; eauto.
  - rewrite F; eapply segRLs_sideRLs_concat; eauto.
Qed.
Lemma bind_spec {X Y} (dx:X->side) (dy:Y->side) hs hs' r o f:
  Spec dx hs r o -> (forall x,Spec dy hs' (dx x) (f x)) ->
  Spec dy (hs++hs') r (then_result o f).
Proof.
  intros H F; destruct o; cbn[Spec then_result] in *; [trivial| |].
  - apply sideRLs_halt_app_left,H.
  - specialize (F x); destruct (f x); cbn[Spec] in *; eauto using sideRLs_halt_app_right,sideRLs_trans.
Qed.

Lemma TO {X} (den:X->side) a r o:
  Spec den j (U^^a *> r) o ->
  Spec (fun x=>U *> den x) j (U^^a *> O *> r) o.
Proof.
  destruct a as [|a]; intro H.
  - change (Spec (fun x=>U *> den x) j (O *> r) o).
    eapply rule_spec; [apply JO|exact H].
  - rewrite <-Str_app_assoc.
    change (Spec (fun x=>U *> den x) j (U *> (U^^a++O) *> r) o).
    assert (Q:sideRLs tm q ((U^^a++O) *> r) (U^^(1+a) *> r)).
    { exact (segRLs_sideRLs_concat (QrunO a) (sideRLseq_O tm r)). }
    destruct o; cbn[Spec] in *; [trivial| |].
    + eapply segRLs_sideRLs_halt_concat; [apply JU|].
      eapply sideRLs_halt_app_right; eauto.
    + eapply segRLs_sideRLs_concat; [apply JU|].
      eapply sideRLs_trans; eauto.
Qed.

Lemma after_spec {X} (den:X->side) hs hs' r s o:
  sideRLs tm hs r s -> Spec den hs' s o -> Spec den (hs++hs') r o.
Proof. destruct o; cbn[Spec]; eauto using sideRLs_trans,sideRLs_halt_app_right. Qed.

Lemma T00 {X} (den:X->side) a r o:
  Spec den (h^^(1+a)) r o ->
  Spec (fun x=>U^^(3+a) *> den x) j (U^^(2+a) *> [0;0] *> r) o.
Proof.
  intro H.
  pose proof (@rule_spec X den _ _ _ _ _ _ (T01 a) H) as T.
  rewrite Str_app_assoc in T.
  pose proof (@TO X _ a _ o T) as T'.
  assert (Q:sideRLs tm q ((U^^(1+a)++[0;0]) *> r) ((U^^a++O++[0;1]) *> r)).
  { exact (segRLs_sideRLs_concat (Qrun00 a) (sideRLseq_O tm r)). }
  rewrite <-Str_app_assoc.
  change (Spec (fun x=>U *> U^^(2+a) *> den x) j (U *> (U^^(1+a)++[0;0]) *> r) o).
  eapply rule_spec; [apply JU|].
  eapply after_spec; [exact Q|].
  rewrite !Str_app_assoc; exact T'.
Qed.

Lemma T00zero: segRLs tm j [] [0;0] O. Proof. sr. Qed.
Lemma T00one: segRLs tm j [] (U++[0;0]) (U++P). Proof. sr. Qed.
Lemma Qrun110 a: segRLs tm q h (U^^a++[1;1;0]) (U^^(1+a)).
Proof. applys_eq (segRLs_concat (Qrun a) Q110); symmetry; apply lpow_shift. Qed.

Lemma T110_return {X} (den:X->side) a r s o:
  sideRLs tm h r s -> Spec den j (U^^a *> s) o ->
  Spec (fun x=>U *> den x) j (U^^a *> [1;1;0] *> r) o.
Proof.
  intros H T; destruct a as [|a].
  - change (Spec (fun x=>U *> den x) j ([1;1;0] *> r) o).
    eapply rule_spec; [apply J110|eapply after_spec; eauto].
  - rewrite <-Str_app_assoc.
    change (Spec (fun x=>U *> den x) j (U *> (U^^a++[1;1;0]) *> r) o).
    eapply rule_spec; [apply JU|eapply after_spec; [|exact T]].
    exact (segRLs_sideRLs_concat (Qrun110 a) H).
Qed.
Lemma T110_halt a r: sideRLs_halt tm h r ->
  sideRLs_halt tm j (U^^a *> [1;1;0] *> r).
Proof.
  intro H; destruct a as [|a].
  - change (sideRLs_halt tm j ([1;1;0] *> r)).
    eapply segRLs_sideRLs_halt_concat; [apply J110|apply sideRLs_halt_app_left,H].
  - rewrite <-Str_app_assoc.
    change (sideRLs_halt tm j (U *> (U^^a++[1;1;0]) *> r)).
    eapply segRLs_sideRLs_halt_concat; [apply JU|apply sideRLs_halt_app_left].
    eapply segRLs_sideRLs_halt_concat; eauto using Qrun110.
Qed.
Lemma T111 a r: sideRLs_halt tm j (U^^a *> [1;1;1] *> r).
Proof.
  destruct a as [|a].
  - change (sideRLs_halt tm j ([1] *> [1;1] *> r)).
    eapply segRLs_sideRLs_halt_concat; [apply J1|].
    constructor; intro l; apply L11.
  - change (sideRLs_halt tm j (U *> U^^a *> [1;1;1] *> r)).
    eapply segRLs_sideRLs_halt_concat; [apply JU|apply sideRLs_halt_app_left].
    eapply segRLs_sideRLs_halt_concat; [apply Qrun|].
    constructor; intro l; apply Q111.
Qed.

Definition digit (p:nat):list Sym := match p with
  | 0%nat=>U | 1%nat=>Z | 2%nat=>O | _=>P end.
Lemma digit_cycle p: p<4 -> segRLs tm (h^^4) h (digit p) (digit p).
Proof. destruct p as [|[|[|[|p]]]]; intro E; try lia; sr. Qed.
Lemma digit_short p n: p<4 -> n<4 ->
  segRLs tm (h^^n) (h^^((p+n)/4)) (digit p) (digit ((p+n) mod 4)).
Proof.
  destruct p as [|[|[|[|p]]]], n as [|[|[|[|n]]]]; intros; try lia; sr.
Qed.
Lemma digit_count p n: p<4 ->
  segRLs tm (h^^n) (h^^((p+n)/4)) (digit p) (digit ((p+n) mod 4)).
Proof.
  intro Hp.
  pose proof (@digit_short p (n mod 4) Hp ltac:(lia)) as Hs.
  pose proof (@digit_cycle ((p+n mod 4) mod 4) ltac:(lia)) as Hc.
  pose proof (Nat.div_mod n 4 ltac:(lia)).
  pose proof (Nat.div_mod (p+n) 4 ltac:(lia)).
  pose proof (Nat.div_mod (p+n mod 4) 4 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (p+n) 4 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (p+n mod 4) 4 ltac:(lia)).
  applys_eq (@segRLs_addmul_v2 4 1 (n/4) (n mod 4) ((p+n mod 4)/4)
    tm h _ _ Hs Hc); flia.
  all: apply (f_equal (lpow h)); lia.
Qed.

Definition bits (w:list Sym):side := w *> 0inf.
Definition pop (w:list Sym):Sym*list Sym := match w with []=>(0,[]) | b::w=>(b,w) end.
Lemma pop_spec w: bits w=fst(pop w) >> bits(snd(pop w)).
Proof. destruct w; [unfold bits; cbn; apply const_unfold|reflexivity]. Qed.
Fixpoint strip u w:option (list Sym) := match u with
  | []=>Some w
  | b::u=>let '(c,w):=pop w in if Eqb.eqb b c then strip u w else None end.
Lemma strip_spec u w v: strip u w=Some v -> bits w=u *> bits v.
Proof.
  gen w; induction u as [|b u IH]; intros w E; cbn[strip] in E.
  - injection E as <-; reflexivity.
  - pose proof (pop_spec w) as H; destruct(pop w) as [c w']; cbn[fst snd] in H.
    destruct b,c; cbn in E; try discriminate;
      rewrite H; cbn[fst snd]; rewrite (IH _ E); reflexivity.
Qed.

Inductive tag := Gs | Js | Ls.
Inductive job := Hs (n:N) | Small (t:tag).
Definition signals c := match c with Hs n=>h^^N.to_nat n
  | Small Gs=>g | Small Js=>j | Small Ls=>e end.
Fixpoint calls cs := match cs with []=>[] | c::cs=>signals c++calls cs end.
Definition entry := (list Sym * option (list Sym * list job))%type.
Definition basic t:list entry := match t with
  | Gs=>[([0;1],Some(U,[]));([1;0],Some(U,[Hs 1]));([1;1],None);
         (P,Some(U,[Small Gs]));([0;0;0;0],Some([1;0;1;0;1],[]));
         ([0;0;0;1],Some([1;0;0;0;1],[Hs 1]))]
  | Js=>[([0;0],Some(O,[]));([0;1],Some(U,[Hs 1]));([1],Some([],[Small Ls]))]
  | Ls=>[([0;1],Some(U,[Small Js]));([1;0],Some(U,[Hs 1;Small Js]));
         ([1;1],None);(P,Some(U,[Small Gs;Small Js]));
         ([0;0;0;0],Some([1;0;0;0;0;1],[]));([0;0;0;1],Some(U++U,[Hs 2]))]
  end.
Definition entry_spec t (e0:entry) := let '(u,out):=e0 in match out with
  | None=>forall r, sideRLs_halt tm (signals(Small t)) (u *> r)
  | Some(v,cs)=>segRLs tm (signals(Small t)) (calls cs) u v end.
Lemma basic_spec t: Forall (entry_spec t) (basic t).
Proof.
  destruct t; cbn[basic]; repeat (apply Forall_cons || apply Forall_nil);
    cbn[entry_spec calls signals]; try solve [sr].
  all: intro r; constructor; intro l; first [apply G11|apply L11].
Qed.
Fixpoint select rs w:option (entry*list Sym) := match rs with
  | []=>None | ((u,o) as r)::rs=>match strip u w with
    | Some v=>Some(r,v) | None=>select rs w end end.
Lemma select_spec rs w u o v: select rs w=Some((u,o),v) ->
  In (u,o) rs /\ bits w=u *> bits v.
Proof.
  induction rs as [|[u' o'] rs IH]; cbn[select]; [discriminate|].
  destruct(strip u' w) as [v'|] eqn:E.
  - intro H; injection H as <- <- <-; split; [left; reflexivity|apply strip_spec,E].
  - intro H; destruct(IH H); split; [right|]; assumption.
Qed.
Fixpoint sequence (f:job->list Sym->result(list Sym)) cs w := match cs with
  | []=>Returned w | c::cs=>then_result (f c w) (sequence f cs) end.
Lemma sequence_spec f:
  (forall c w,Spec bits (signals c) (bits w) (f c w)) ->
  forall cs w,Spec bits (calls cs) (bits w) (sequence f cs w).
Proof.
  intro H; induction cs; intro w; cbn[sequence calls]; [constructor|].
  eapply bind_spec; eauto.
Qed.
Definition basic_eval f t w := match select (basic t) w with
  | None=>Failed | Some((u,None),r)=>Stopped
  | Some((u,Some(v,cs)),r)=>map_result (app v) (sequence f cs r) end.
Lemma basic_eval_spec f:
  (forall c w,Spec bits (signals c) (bits w) (f c w)) ->
  forall t w,Spec bits (signals(Small t)) (bits w) (basic_eval f t w).
Proof.
  intros H t w; unfold basic_eval.
  destruct(select (basic t) w) as [[[u [[v cs]|]] r]|] eqn:E; [| |exact I];
    apply select_spec in E as [E ->];
    pose proof (proj1 (Forall_forall _ _) (basic_spec t) _ E) as R.
  - eapply lift_rule; [exact R| |apply sequence_spec,H].
    intro x; unfold bits; apply Str_app_assoc.
  - exact (R (bits r)).
Qed.

Fixpoint evaluate fuel c w:result(list Sym) := match fuel with
  | Datatypes.O=>Failed
  | S fuel=>match c with
    | Small t=>basic_eval (evaluate fuel) t w
    | Hs N0=>Returned w
    | Hs n=>let '(b,x):=pop w in let '(c,y):=pop x in let '(d,z):=pop y in
      if Eqb.eqb c 1 then if Eqb.eqb b 1 then evaluate fuel (Hs(N.pred n)) (0::1::y)
        else sequence (evaluate fuel) [Small Ls;Hs(N.pred n)] y
      else let p:=if Eqb.eqb b 1 then if Eqb.eqb d 1 then 2%N else 0%N else if Eqb.eqb d 1 then 3%N else 1%N in
        map_result (app (digit (N.to_nat ((p+n) mod 4))))
          (evaluate fuel (Hs ((p+n)/4)) z)
    end end.

Lemma digit_countN p n: (p<4)%N ->
  segRLs tm (h^^N.to_nat n) (h^^N.to_nat((p+n)/4))
    (digit(N.to_nat p)) (digit(N.to_nat((p+n) mod 4))).
Proof.
  intro H; rewrite N2Nat.inj_div,N2Nat.inj_mod,!N2Nat.inj_add.
  apply digit_count; lia.
Qed.
Lemma normal_eval f n p w:
  (forall c w,Spec bits (signals c) (bits w) (f c w)) -> (p<4)%N ->
  Spec bits (h^^N.to_nat n) (digit(N.to_nat p) *> bits w)
    (map_result (app (digit(N.to_nat((p+n) mod 4)))) (f (Hs((p+n)/4)) w)).
Proof.
  intros H Hp; eapply lift_rule; [apply digit_countN,Hp| |apply H].
  intro x; unfold bits; apply Str_app_assoc.
Qed.
Lemma H01rest n: segRLs tm (h++h^^n) (e++h^^n) [0;1] [].
Proof. exact (segRLs_trans (segRLs_concat H0 J1) (@segRLs_nil tm (h^^n))). Qed.

Lemma evaluate_spec fuel c w: Spec bits (signals c) (bits w) (evaluate fuel c w).
Proof.
  gen c w; induction fuel; intros c w; [exact I|].
  destruct c as [[|n]|t]; [constructor| |apply basic_eval_spec,IHfuel].
  cbn[evaluate].
  pose proof(pop_spec w) as E1; destruct(pop w) as [b x]; cbn[fst snd] in E1.
  pose proof(pop_spec x) as E2; destruct(pop x) as [c y]; cbn[fst snd] in E2.
  pose proof(pop_spec y) as E3; destruct(pop y) as [d z]; cbn[fst snd] in E3.
  assert (En:N.to_nat(Npos n)=1+N.to_nat(N.pred(Npos n)))
    by (rewrite N2Nat.inj_pred; cbn[N.to_nat]; pose proof (Pos2Nat.is_pos n); lia).
  destruct b,c; cbn[Eqb.eqb].
  - rewrite E1,E2,E3; destruct d; cbn[Eqb.eqb].
    + apply (@normal_eval _ _ 1%N); [apply IHfuel|reflexivity].
    + apply (@normal_eval _ _ 3%N); [apply IHfuel|reflexivity].
  - rewrite E1,E2; unfold signals; rewrite En; cbn[lpow].
    eapply (@rule_spec _ bits _ _ [0;1] [] (bits y)); [apply H01rest|].
    pose proof (sequence_spec _ IHfuel [Small Ls;Hs(N.pred(Npos n))] y) as H.
    cbn[calls signals] in H; rewrite app_nil_r in H; exact H.
  - rewrite E1,E2,E3; destruct d; cbn[Eqb.eqb].
    + apply (@normal_eval _ _ 0%N); [apply IHfuel|reflexivity].
    + apply (@normal_eval _ _ 2%N); [apply IHfuel|reflexivity].
  - rewrite E1,E2; unfold signals; rewrite En; cbn[lpow].
    eapply after_spec; [|apply (IHfuel (Hs(N.pred(Npos n))) (0::1::y))].
    exact (segRLs_sideRLs_concat H1 (sideRLseq_O tm (1 >> bits y))).
Qed.

Definition unary (a:N) r := U^^N.to_nat a *> r.
Definition pair := (N*list Sym)%type.
Definition pair_side (x:pair) := unary (fst x) (bits(snd x)).
Definition add_unary (b:N) (x:pair):pair := ((b+fst x)%N,snd x).
Lemma add_unary_spec b x: pair_side(add_unary b x)=unary b (pair_side x).
Proof. unfold pair_side,add_unary,unary; cbn[fst snd]; rewrite N2Nat.inj_add,lpow_add,Str_app_assoc; reflexivity. Qed.

Fixpoint collect w:pair := match w with
  | 1::0::0::w=>add_unary 1 (collect w)
  | _=>(0%N,w) end.
Lemma collect_spec: forall w, pair_side(collect w)=bits w.
Proof.
  fix IH 1; intro w; destruct w as [|b [|c [|d w]]];
    try destruct b; try destruct c; try destruct d; try reflexivity.
  cbn[collect]; rewrite add_unary_spec,(IH w); reflexivity.
Qed.

Fixpoint tcall fuel efuel (a:N) w:result pair := match fuel with
  | Datatypes.O=>Failed
  | S fuel=>let '(b,x):=pop w in let '(c,y):=pop x in let '(d,z):=pop y in
    match b,c,d with
    | 0,0,_=>if (a=?0)%N then Returned(0%N,O++y)
      else if (a=?1)%N then Returned(1%N,P++y)
      else map_result (fun s=>((a+1)%N,s)) (evaluate efuel (Hs(a-1)) y)
    | 0,1,_=>map_result (fun s=>((a+1)%N,s)) (evaluate efuel (Hs(a+1)) y)
    | 1,0,0=>tcall fuel efuel (a+1) z
    | 1,0,1=>map_result (add_unary 1) (tcall fuel efuel a z)
    | 1,1,0=>map_result (add_unary 1)
        (then_result (evaluate efuel (Hs 1) z) (tcall fuel efuel a))
    | 1,1,1=>Stopped end end.
Definition normalize (x:pair):pair := add_unary (fst x) (collect(snd x)).
Lemma normalize_spec x: pair_side(normalize x)=pair_side x.
Proof. unfold normalize; rewrite add_unary_spec,collect_spec; reflexivity. Qed.
Definition round fuel efuel (x:pair) :=
  map_result normalize (if (fst x=?0)%N then
    map_result (fun w=>(0%N,w)) (evaluate efuel (Small Gs) (snd x))
    else map_result (add_unary 1) (tcall fuel efuel (fst x-1) (snd x))).
Fixpoint run fuel tfuel efuel (x:pair):result pair := match fuel with
  | Datatypes.O=>Returned x
  | S fuel=>then_result (round tfuel efuel x) (run fuel tfuel efuel) end.

Lemma map_spec {X Y} (dx:X->side) (dy:Y->side) hs r o f:
  (forall x,dy(f x)=dx x) -> Spec dx hs r o -> Spec dy hs r (map_result f o).
Proof. intros E H; destruct o; cbn[Spec map_result] in *; trivial; rewrite E; exact H. Qed.
Lemma T00N {X} (den:X->side) a r o:
  (2<=a)%N -> Spec den (h^^N.to_nat(a-1)) r o ->
  Spec (fun x=>unary (a+1) (den x)) j (unary a ([0;0] *> r)) o.
Proof.
  intros Ha H; unfold unary.
  assert (Ea:N.to_nat a=2+N.to_nat(a-2)) by (rewrite N2Nat.inj_sub; lia).
  assert (Eo:N.to_nat(a+1)=3+N.to_nat(a-2)) by (rewrite N2Nat.inj_add,N2Nat.inj_sub; lia).
  assert (Eh:N.to_nat(a-1)=1+N.to_nat(a-2)) by (rewrite !N2Nat.inj_sub; lia).
  rewrite Ea,Eo; apply T00; rewrite <-Eh; exact H.
Qed.
Lemma T01N {X} (den:X->side) a r o:
  Spec den (h^^N.to_nat(a+1)) r o ->
  Spec (fun x=>unary (a+1) (den x)) j (unary a ([0;1] *> r)) o.
Proof.
  unfold unary; rewrite N2Nat.inj_add; change (N.to_nat 1) with 1%nat.
  rewrite (Nat.add_comm _ 1),<-Str_app_assoc; apply rule_spec,T01.
Qed.

Lemma tcall_spec fuel efuel a w:
  Spec pair_side j (unary a (bits w)) (tcall fuel efuel a w).
Proof.
  gen a w; induction fuel; intros a w; [exact I|].
  cbn[tcall].
  pose proof(pop_spec w) as E1; destruct(pop w) as [b x]; cbn[fst snd] in E1.
  pose proof(pop_spec x) as E2; destruct(pop x) as [c y]; cbn[fst snd] in E2.
  pose proof(pop_spec y) as E3; destruct(pop y) as [d z]; cbn[fst snd] in E3.
  destruct b,c.
  - rewrite E1,E2; destruct d; destruct (N.eqb_spec a 0) as [->|Ha];
      [|destruct (N.eqb_spec a 1) as [->|Ha1]| |destruct (N.eqb_spec a 1) as [->|Ha1]].
    all: try solve [exact (segRLs_sideRLs_concat T00zero (sideRLseq_O tm (bits y)))].
    all: try solve [exact (segRLs_sideRLs_concat T00one (sideRLseq_O tm (bits y)))].
    all: eapply map_spec; [reflexivity|apply T00N; [lia|apply evaluate_spec]].
  - rewrite E1,E2; destruct d;
      eapply map_spec; [reflexivity|apply T01N,evaluate_spec|reflexivity|apply T01N,evaluate_spec].
  - rewrite E1,E2,E3; destruct d.
    + applys_eq (IHfuel (a+1)%N z).
      unfold unary; rewrite N2Nat.inj_add,lpow_add,Str_app_assoc; reflexivity.
    + eapply map_spec with (dx:=fun p=>U *> pair_side p).
      * intro p; rewrite add_unary_spec; reflexivity.
      * apply TO,IHfuel.
  - rewrite E1,E2,E3; destruct d.
    + eapply map_spec with (dx:=fun p=>U *> pair_side p).
      * intro p; rewrite add_unary_spec; reflexivity.
      * pose proof(evaluate_spec efuel (Hs 1) z) as H.
        destruct(evaluate efuel (Hs 1) z) as [| |v]; cbn[then_result]; [exact I| |].
        -- apply T110_halt,H.
        -- eapply T110_return; [exact H|apply IHfuel].
    + apply T111.
Qed.

Lemma unary_pos a r: a<>0%N -> unary a r=U *> unary (a-1) r.
Proof.
  intro Ha; unfold unary.
  replace (N.to_nat a) with (1+N.to_nat(a-1)) by (rewrite N2Nat.inj_sub; lia).
  reflexivity.
Qed.
Lemma round_spec fuel efuel x:
  Spec pair_side g (pair_side x) (round fuel efuel x).
Proof.
  unfold round; eapply map_spec; [apply normalize_spec|].
  destruct x as [a w]; cbn[fst snd]; destruct (N.eqb_spec a 0) as [->|Ha].
  - eapply map_spec with (dx:=bits); [reflexivity|apply evaluate_spec].
  - eapply map_spec with (dx:=fun p=>U *> pair_side p).
    + intro p; rewrite add_unary_spec; reflexivity.
    + unfold pair_side; cbn[fst snd]; rewrite unary_pos by exact Ha.
      eapply rule_spec; [apply GU|apply tcall_spec].
Qed.

Definition root x := 0inf <{{C}} [1] *> pair_side x.
Lemma emit r: 0inf <{{C}} [1] *> r -->+ 0inf <* [0;0] {{E}}> r.
Proof. esx. Qed.
Lemma init: c0 -->* root (0%N,[1]).
Proof. unfold root,pair_side,unary,bits; esx. Qed.
Definition machine_spec x (o:result pair) := match o with
  | Failed=>True | Stopped=>halts tm (root x)
  | Returned y=>root x -->* root y end.
Lemma round_machine fuel efuel x: machine_spec x (round fuel efuel x).
Proof.
  pose proof (round_spec fuel efuel x) as H.
  destruct(round fuel efuel x); cbn[Spec machine_spec] in *; [exact I| |].
  - eapply halts_evstep; [exact (sideRLs_halt_single _ _ _ _ H 0inf)|].
    apply progress_evstep,emit.
  - unfold root; apply progress_evstep.
    eapply progress_trans; [apply emit|exact (sideRLs_1 _ _ _ _ _ H 0inf)].
Qed.
Lemma machine_then x o f:
  machine_spec x o -> (forall y,machine_spec y (f y)) ->
  machine_spec x (then_result o f).
Proof.
  intros H F; destruct o; cbn[machine_spec then_result] in *; [exact I|exact H|].
  specialize (F x0); destruct(f x0); cbn[machine_spec] in *; eauto using halts_evstep,evstep_trans.
Qed.
Lemma run_spec fuel tfuel efuel x: machine_spec x (run fuel tfuel efuel x).
Proof.
  gen x; induction fuel; intro x; cbn[run]; [apply evstep_refl|].
  apply machine_then; [apply round_machine|apply IHfuel].
Qed.

Definition chunk := run 1000 256 2048.
Fixpoint batches n x:result pair := match n with
  | Datatypes.O=>Returned x | S n=>then_result (chunk x) (batches n) end.
Lemma batches_spec n x: machine_spec x (batches n x).
Proof.
  gen x; induction n; intro x; cbn[batches]; [apply evstep_refl|].
  apply machine_then; [apply run_spec|apply IHn].
Qed.
Definition check n := match batches n (0%N,[1]) with Stopped=>true | _=>false end.
Lemma check_spec n: check n=true -> halts tm c0.
Proof.
  unfold check; pose proof (batches_spec n (0%N,[1])) as H.
  destruct(batches n (0%N,[1])); try discriminate.
  intros _; eapply halts_evstep; [exact H|apply init].
Qed.

Theorem halt: halts tm c0.
Proof. apply (@check_spec 700); native_check_eq. Qed.

End TM5.

(* BEC.txt TM10.  Local accelerators for the finite prefix and its final
   absorbing counter region.  The finite prefix is not confined to K. *)
Set Implicit Arguments.

Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1LC0RD_1LD0LA_1RE0RC_1RB0RE_0LC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation U := [1;1;0].
Notation Z := [0;0;0].
Notation O := [1;0;0].
Notation V := [0;1;1].
Notation I := [0;1;0].
Notation W := [0;0;1;0;1;0].
Notation P := [1;0;0;0;1;0].
Notation Qw := [0;0;0;1;0;1].
Notation W1 := [0;0;1;0;0;1].
Notation J := [1;0;1;1;0;0].
Notation h := [((B,[]),(C,[]))].
Notation g := [((E,[]),(A,[]))].

Definition K a r := 0inf <{{C}} U^^a *> r.

Lemma absorbing k:
  K (2+k*2) (Z *> O *> 0inf) -->+ K (4+k*2) (Z *> O *> 0inf).
Proof. unfold K; es' k. Qed.

Lemma absorbing_nonhalt k: ~halts tm (K (2+k*2) (Z *> O *> 0inf)).
Proof.
  eapply progress_nonhalt_simple with (C:=fun k => K (2+k*2) (Z *> O *> 0inf)).
  intro n; exists (1+n); applys_eq (absorbing n); flia.
Qed.

Lemma s_down b l:
  l <* (rev P)^^b {{D}}> [1;0;0;0;0;1] *> 0inf -->+
  l <{{B}} [1;0;1;1;0;1]^^b *> [1;0;1;1;0;0;0;0;1;0;0;0] *> 0inf.
Proof. es' b & l. Qed.

Lemma s_across b l:
  l <* (rev W) <{{B}} [1;0;1;1;0;1]^^b *> [1;0;1;1;0;0;0;0;1;0;0;0] *> 0inf -->*
  l <* <[0;0;0;1;0;0] <* <[0;1;0;1;0;0]^^b <{{B}} [1;0;1;1;0;1;1;0;0;0;0;1] *> 0inf.
Proof. es' b & l. Qed.

Lemma s_back b l r:
  l <* <[0;0;0;1;0;0] <* <[0;1;0;1;0;0]^^b <{{B}} r -->*
  l <* (rev P) {{D}}> [1;0;1;1;0;1]^^b *> r.
Proof. es' b & l r. Qed.

Lemma s_scan b l r:
  l {{D}}> [1;0;1;1;0;1]^^b *> r -->*
  l <* (rev P)^^b {{D}}> r.
Proof. es' b & l r. Qed.

Lemma s_up b l:
  l <* (rev W) <{{B}} [1;0;1;1;0;1]^^b *> [1;0;1;1;0;0;0;0;1;0;0;0] *> 0inf -->*
  l <* (rev P)^^(2+b) {{D}}> [1;0;0;0;0;1] *> 0inf.
Proof.
  follow (s_across b l).
  follow (s_back b l ([1;0;1;1;0;1;1;0;0;0;0;1] *> 0inf)).
  follow (s_scan b (l <* (rev P)) ([1;0;1;1;0;1;1;0;0;0;0;1] *> 0inf)).
  st; es' b & l.
Qed.

Lemma s_cycle b l:
  l <* (rev W) <* (rev P)^^b {{D}}> [1;0;0;0;0;1] *> 0inf -->+
  l <* (rev P)^^(2+b) {{D}}> [1;0;0;0;0;1] *> 0inf.
Proof. follow10 (s_down b (l <* (rev W))); apply s_up. Qed.

Lemma s_batch k b l:
  l <* (rev W)^^k <* (rev P)^^b {{D}}> [1;0;0;0;0;1] *> 0inf -->*
  l <* (rev P)^^(b+k*2) {{D}}> [1;0;0;0;0;1] *> 0inf.
Proof.
  gen b; induction k; intro b; [finish|].
  eapply evstep_trans; [apply progress_evstep; applys_eq (s_cycle b (l <* (rev W)^^k)); st; reflexivity|].
  applys_eq (IHk (2+b)); flia.
Qed.

Inductive Num (one:list Sym): nat -> side -> Prop :=
| Num_nil: Num one 0 0inf
| Num_zero n r: Num one n r -> Num one (n*2) (Z *> r)
| Num_one n r: Num one n r -> Num one (1+n*2) (one *> r).

Lemma Num_zero_tape one r: Num one 0 r -> r=0inf.
Proof.
  remember 0%nat as n; intro H; induction H; try lia; [reflexivity|].
  rewrite IHNum; [st; reflexivity|lia].
Qed.

Lemma Num_unique one n r s: Num one n r -> Num one n s -> r=s.
Proof.
  intro H; gen s; induction H; intros s Ns.
  - symmetry; apply Num_zero_tape in Ns; assumption.
  - inversion Ns; subst; try lia.
    + assert (n=0%nat) by lia; subst; rewrite (Num_zero_tape H); st; reflexivity.
    + f_equal; apply IHNum; applys_eq H1; flia.
  - inversion Ns; subst; try lia.
    f_equal; apply IHNum; applys_eq H1; flia.
Qed.

(* Binary values in the executable layer use N, never unary-sized tapes. *)
Fixpoint digits_pos (one:list Sym) p : list Sym := match p with
  | xH => one
  | xO p => Z ++ digits_pos one p
  | xI p => one ++ digits_pos one p
  end.
Definition digits one n := match n with N0 => [] | Npos p => digits_pos one p end.

Lemma digits_spec one n: Num one (N.to_nat n) (digits one n *> 0inf).
Proof.
  destruct n as [|p]; [constructor|].
  unfold digits; induction p; cbn [digits_pos]; rewrite ?Str_app_assoc.
  - applys_eq (Num_one IHp); cbn [N.to_nat]; lia.
  - applys_eq (Num_zero IHp); cbn [N.to_nat]; lia.
  - applys_eq (Num_one (Num_nil one)); flia.
Qed.

Lemma h_carry: segRLs tm h h O Z.
Proof. apply BoundedConfig.segRLs_c_spec with (T:=20); reflexivity. Qed.
Lemma g_carry: segRLs tm g g I Z.
Proof. apply BoundedConfig.segRLs_c_spec with (T:=20); reflexivity. Qed.

Lemma increment n r: Num O n r -> exists s, Num O (1+n) s /\ sideRLs tm h r s.
Proof.
  intro N; induction N as [|n r N IH|n r N [s [Ns Hs]]].
  - exists (O *> 0inf); split; [exact (Num_one (Num_nil O))|esx].
  - exists (O *> r); split; [constructor; assumption|esx].
  - exists (Z *> s); split.
    + applys_eq (Num_zero Ns); flia.
    + eapply segRLs_sideRLs_concat; [apply h_carry|exact Hs].
Qed.

Lemma rotated_increment n r: Num I n r -> exists s, Num I (1+n) s /\ sideRLs tm g r s.
Proof.
  intro N; induction N as [|n r N IH|n r N [s [Ns Hs]]].
  - exists (I *> 0inf); split; [exact (Num_one (Num_nil I))|esx].
  - exists (I *> r); split; [constructor; assumption|esx].
  - exists (Z *> s); split.
    + applys_eq (Num_zero Ns); flia.
    + eapply segRLs_sideRLs_concat; [apply g_carry|exact Hs].
Qed.

Lemma rotated_even j l r:
  l {{E}}> [1;1;1] *> V^^(j*2) *> Z *> r -->+
  l <{{D}} [1;1;1] *> V^^(j*2) *> I *> r.
Proof. es' j & l r. Qed.

Lemma rotated_odd_enter j l r:
  l {{E}}> [1;1;1] *> V^^(j*2) *> I *> r -->*
  l <* (rev Qw)^^(1+j) {{E}}> r.
Proof. es' j & l r. Qed.

Lemma rotated_odd_leave j l r:
  l <* (rev Qw)^^(1+j) <{{A}} r -->*
  l <{{D}} [1;1;1] *> V^^(j*2) *> Z *> r.
Proof. es' j & l r. Qed.

Lemma rotated_return j n r: Num I n r -> exists s, Num I (1+n) s /\ forall l,
  l {{E}}> [1;1;1] *> V^^(j*2) *> r -->+
  l <{{D}} [1;1;1] *> V^^(j*2) *> s.
Proof.
  intro N; destruct N as [|n r N|n r N].
  - exists (I *> 0inf); split; [exact (Num_one (Num_nil I))|intro l].
    applys_eq (rotated_even j l 0inf); st; reflexivity.
  - exists (I *> r); split; [constructor; assumption|intro l; apply rotated_even].
  - destruct (rotated_increment N) as [s [Ns Hs]].
    exists (Z *> s); split; [applys_eq (Num_zero Ns); flia|intro l].
    eapply evstep_progress_trans; [apply rotated_odd_enter|].
    follow10 (sideRLs_1 _ _ _ _ _ Hs (l <* (rev Qw)^^(1+j))).
    cbn[to_DH_config]; apply rotated_odd_leave.
Qed.

Lemma t_cycle j n r: Num I n r -> exists s, Num I (2+n) s /\ forall l,
  l <* (rev W)^^2 <{{A}} V^^(1+j*2) *> r -->+
  l <* (rev W) <{{A}} V^^(3+j*2) *> s.
Proof.
  intro N; destruct (rotated_return j N) as [r1 [N1 H1]].
  destruct (rotated_return (1+j) N1) as [s [Ns Hs]].
  exists s; split; [applys_eq Ns; flia|intro l].
  do 5 step1.
  follow100 (H1 (l <* (rev W) <* (rev W1))).
  do 11 step1.
  follow100 (Hs (l <* <[0;0;1;0;1;1])).
  es' j & l s.
Qed.

Lemma t_batch k j n r: Num I n r -> exists s, Num I (n+k*2) s /\ forall l,
  l <* (rev W)^^(1+k) <{{A}} V^^(1+j*2) *> r -->*
  l <* (rev W) <{{A}} V^^(1+j*2+k*2) *> s.
Proof.
  gen j n r; induction k; intros j n r N.
  - exists r; split; [applys_eq N; flia|intro l; finish].
  - destruct (t_cycle j N) as [r1 [N1 H1]].
    destruct (IHk (1+j) _ _ N1) as [s [Ns Hs]].
    exists s; split; [applys_eq Ns; flia|intro l].
    eapply evstep_trans; [apply progress_evstep; applys_eq (H1 (l <* (rev W)^^k)); st; reflexivity|].
    applys_eq (Hs l); flia; st; simpl_rotate; reflexivity.
Qed.

Lemma left_counter c l r:
  l <* (rev W) <* (rev W1) <* (rev Qw)^^c <{{A}} r -->*
  l <* (rev W1) <* (rev Qw)^^(1+c) {{E}}> r.
Proof. es' c & l r. Qed.

Lemma right_counter j n r: Num I n r -> exists s, Num I (1+n) s /\ forall l,
  l <* (rev J) {{C}}> V^^(1+j*2) *> r -->+
  l <* (rev J) <{{A}} V^^(1+j*2) *> s.
Proof.
  intro N; destruct (rotated_return j N) as [s [Ns Hs]].
  exists s; split; [assumption|intro l].
  do 2 step1.
  follow100 (Hs (l <* <[1;0;1;1;0;1])).
  es' j & l s.
Qed.

Lemma coupled_cycle c j n r: Num I n r -> exists s, Num I (1+n) s /\ forall l,
  l <* (rev W)^^2 <* (rev W1) <* (rev Qw)^^c <* (rev J) <{{A}} V^^(1+j*2) *> r -->+
  l <* (rev W1) <* (rev Qw)^^(2+c) <* (rev J) <{{A}} V^^(1+j*2) *> s.
Proof.
  intro N; destruct (right_counter j N) as [s [Ns Hs]].
  exists s; split; [assumption|intro l].
  do 6 step1.
  follow (left_counter c (l <* (rev W)) ([0;0;0;0;1;1] *> V^^(1+j*2) *> r)).
  do 3 step1.
  follow (left_counter (1+c) l ([0;1;0;0;1;1] *> V^^(1+j*2) *> r)).
  do 6 step1.
  follow100 (Hs (l <* (rev W1) <* (rev Qw)^^(2+c))).
  finish.
Qed.

Lemma coupled_batch k c j n r: Num I n r -> exists s, Num I (n+k) s /\ forall l,
  l <* (rev W)^^(k*2) <* (rev W1) <* (rev Qw)^^c <* (rev J) <{{A}} V^^(1+j*2) *> r -->*
  l <* (rev W1) <* (rev Qw)^^(c+k*2) <* (rev J) <{{A}} V^^(1+j*2) *> s.
Proof.
  gen c n r; induction k; intros c n r N.
  - exists r; split; [applys_eq N; flia|intro l; finish].
  - destruct (coupled_cycle c j N) as [r1 [N1 H1]].
    destruct (IHk (2+c) _ _ N1) as [s [Ns Hs]].
    exists s; split; [applys_eq Ns; flia|intro l].
    eapply evstep_trans; [apply progress_evstep; applys_eq (H1 (l <* (rev W)^^(k*2))); st; reflexivity|].
    applys_eq (Hs l); flia.
Qed.

Lemma carry_right b l r:
  l {{E}}> [1;1;1;0;1;1] *> [0;1;1;0;1;1]^^b *> r -->*
  l <* (rev Qw)^^b {{E}}> [1;1;1;0;1;1] *> r.
Proof.
  gen l; induction b; intro l; [finish|].
  do 8 step1; follow (IHb (l <* (rev Qw))); finish; st; simpl_rotate; reflexivity.
Qed.

Lemma carry_left b l r:
  l <* (rev Qw)^^b <{{D}} [1;1;1;0;1;1] *> r -->*
  l <{{D}} [1;1;1;0;1;1] *> [0;1;1;0;1;1]^^b *> r.
Proof. es' b & l r. Qed.

Lemma emit r: 0inf <{{C}} r -->+ 0inf <* <[1;0] {{E}}> r.
Proof. esx. Qed.

Lemma root_odd_enter k r:
  K (1+k*2) r -->+
  0inf <* <[1;0] <* (rev W)^^k <* <[0;0;1] {{B}}> r.
Proof. unfold K; es' k & r. Qed.

Lemma root_odd_leave k r:
  0inf <* <[1;0] <* (rev W)^^k <* <[0;0;1] <{{C}} r -->*
  K (2+k*2) r.
Proof. unfold K; es' k & r. Qed.

Lemma root_odd k n r: Num O n r -> exists s, Num O (1+n) s /\
  K (1+k*2) r -->+ K (2+k*2) s.
Proof.
  intro N; destruct (increment N) as [s [Ns Hs]].
  exists s; split; [assumption|].
  follow10 (root_odd_enter k r).
  follow100 (sideRLs_1 _ _ _ _ _ Hs (0inf <* <[1;0] <* (rev W)^^k <* <[0;0;1])).
  cbn[to_DH_config]; apply root_odd_leave.
Qed.

Lemma root_even_bridge: segRLs tm [((E,rev W),(C,[]))] h Z (U^^3).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=80); reflexivity. Qed.

Lemma root_even_enter k r:
  K (2+k*2) (Z *> r) -->+
  0inf <* <[1;0] <* (rev W)^^k <* (rev W) {{E}}> Z *> r.
Proof. unfold K; es' k & r. Qed.

Lemma root_even_leave k r:
  0inf <* <[1;0] <* (rev W)^^k <{{C}} U^^3 *> r -->*
  K (4+k*2) r.
Proof. unfold K; es' k & r. Qed.

Lemma root_even k n r: Num O n r -> exists s, Num O (1+n) s /\
  K (2+k*2) (Z *> r) -->+ K (4+k*2) s.
Proof.
  intro N; destruct (increment N) as [s [Ns Hs]].
  exists s; split; [assumption|].
  follow10 (root_even_enter k r).
  pose proof (segRLs_sideRLs_concat root_even_bridge Hs) as H.
  follow100 (sideRLs_1 _ _ _ _ _ H (0inf <* <[1;0] <* (rev W)^^k)).
  cbn[to_DH_config]; apply root_even_leave.
Qed.

Lemma s_enter k:
  K (2+k*2) (O *> 0inf) -->+
  0inf <* <[1;0] <* (rev W)^^k <* (rev P) {{D}}> [1;0;0;0;0;1] *> 0inf.
Proof. unfold K; es' k. Qed.

Lemma s_leave b:
  0inf <* <[1;0] <* (rev P)^^b {{D}}> [1;0;0;0;0;1] *> 0inf -->*
  K (3+b*2) (Z *> O *> 0inf).
Proof.
  follow100 (s_down b (0inf <* <[1;0])).
  do 4 step1; unfold K; finish; st; simpl_rotate.
  rewrite lpow_mul; reflexivity.
Qed.

Lemma root_unit k:
  K (2+k*2) (O *> 0inf) -->+ K (5+k*4) (Z *> O *> 0inf).
Proof.
  follow10 (s_enter k).
  follow (s_batch k 1 (0inf <* <[1;0])).
  applys_eq (s_leave (1+k*2)); flia.
Qed.

Lemma binary_E0 l r: l {{E}}> Z *> r -->+ l <{{A}} I *> r.
Proof. esx. Qed.
Lemma binary_E1 l r: l {{E}}> O *> r -->+ l <{{B}} [1;0;1] *> r.
Proof. esx. Qed.
Lemma binary_D0 l r: l {{D}}> Z *> r -->+ l <{{F}} [0;0;1] *> r.
Proof. esx. Qed.
Lemma binary_D1 l r: l {{D}}> O *> Z *> r -->+ l <{{B}} [1;0;1;1;0;1] *> r.
Proof. esx. Qed.
Lemma binary_D3_bridge: segRLs tm [((D,[]),(C,[]))] (h++h) (O++O) (U++U).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=80); reflexivity. Qed.

Lemma binary_D3 n r: Num O n r -> exists s, Num O (2+n) s /\ forall l,
  l {{D}}> O *> O *> r -->+ l <{{C}} U *> U *> s.
Proof.
  intro N; destruct (increment N) as [r1 [N1 H1]].
  destruct (increment N1) as [s [Ns Hs]].
  exists s; split; [applys_eq Ns; flia|intro l].
  pose proof (sideRLs_trans H1 Hs) as H.
  pose proof (segRLs_sideRLs_concat binary_D3_bridge H) as H'.
  exact (sideRLs_1 _ _ _ _ _ H' l).
Qed.

(* A small generator replaces the 768 concrete six-cell rules.  It may
   also return an interior configuration; only an unchanged exiting head
   licenses iteration over a complete RLE run. *)
Definition block q d w := BoundedConfig.steps1 tm 30 (BoundedConfig.Build_T [] w q d).

Lemma block_spec q d w c:
  block q d w=Some (c,true) -> forall l r,
  BoundedConfig.to_config (BoundedConfig.Build_T [] w q d) l r -->+
  BoundedConfig.to_config c l r.
Proof.
  intro H; pose proof (BoundedConfig.steps1_spec tm 30 (BoundedConfig.Build_T [] w q d)) as Hs.
  fold (block q d w) in Hs.
  rewrite H in Hs; exact Hs.
Qed.

Lemma block_right q w v k:
  block q R w=Some (BoundedConfig.Build_T v [] q R,true) -> forall l r,
  l {{q}}> w^^k *> r -->* l <* v^^k {{q}}> r.
Proof.
  intros H; induction k; intros l r; [finish|].
  eapply evstep_trans; [apply progress_evstep; applys_eq (@block_spec q R w _ H l (w^^k *> r)); cbn[BoundedConfig.to_config]; st; reflexivity|].
  cbn[BoundedConfig.to_config]; follow (IHk (l <* v) r).
  finish; st; simpl_rotate; reflexivity.
Qed.

Lemma block_left q w v k:
  block q L w=Some (BoundedConfig.Build_T v [] q L,true) -> forall l r,
  l <* w^^k <{{q}} r -->* l <{{q}} v^^k *> r.
Proof.
  intros H; induction k; intros l r; [finish|].
  eapply evstep_trans; [apply progress_evstep; applys_eq (@block_spec q L w _ H (l <* w^^k) r); cbn[BoundedConfig.to_config]; st; reflexivity|].
  cbn[BoundedConfig.to_config]; follow (IHk l (v *> r)).
  finish; st; simpl_rotate; reflexivity.
Qed.

Module Runs.
Unset Implicit Arguments.
Definition t := list (list Sym*N).
Fixpoint denote (xs:t) : side := match xs with
  | [] => 0inf
  | (w,n)::xs => w^^N.to_nat n *> denote xs
  end.

Definition push (w:list Sym) (n:N) (xs:t) : t :=
  match w,n with
  | [],_ | _,N0 => xs
  | _,_ => match xs with
    | (v,m)::ys => if Eqb.eqb w v then (w,(n+m)%N)::ys else (w,n)::xs
    | [] => [(w,n)] end
  end.

Lemma nil_power {T} n: (@nil T)^^n=[].
Proof. induction n; cbn; congruence. Qed.

Lemma push_spec w n xs: denote (push w n xs)=w^^N.to_nat n *> denote xs.
Proof.
  destruct w as [|b w].
  - cbn[push]; rewrite nil_power; reflexivity.
  - destruct n as [|n]; [reflexivity|].
    destruct xs as [|[v m] xs]; cbn[push denote]; [reflexivity|].
    destruct (Eqb.eqb_spec (b::w) v); subst; cbn[denote]; [|reflexivity].
    rewrite N2Nat.inj_add,lpow_add,Str_app_assoc; reflexivity.
Qed.

Fixpoint pop (xs:t) : Sym*t := match xs with
  | [] => (0,[])
  | ([],_)::xs | (_,N0)::xs => pop xs
  | ((b::w),Npos n)::xs => (b,push w 1 (push (b::w) (N.pred (Npos n)) xs))
  end.

Lemma pop_spec xs: denote xs=fst (pop xs) >> denote (snd (pop xs)).
Proof.
  induction xs as [|[[|b w] [|n]] xs IH]; cbn[pop denote].
  - apply const_unfold.
  - exact IH.
  - rewrite nil_power; exact IH.
  - exact IH.
  - cbn[fst snd]; rewrite !push_spec.
    change (N.to_nat 1) with 1%nat; cbn[lpow app Str_app].
    replace (N.to_nat (Npos n)) with (1+N.to_nat (N.pred (Npos n))) by lia.
    cbn[Nat.add lpow app Str_app]; rewrite app_nil_r,Str_app_assoc; reflexivity.
Qed.

Fixpoint take n xs: list Sym*t := match n with
  | Datatypes.O => ([],xs)
  | S n => let '(b,ys):=pop xs in let '(w,zs):=take n ys in (b::w,zs)
  end.

Lemma take_spec n xs: denote xs=fst (take n xs) *> denote (snd (take n xs)).
Proof.
  gen xs; induction n; intro xs; [reflexivity|].
  cbn[take]; pose proof (pop_spec xs) as H.
  destruct (pop xs) as [b ys]; cbn in H; rewrite H,IHn.
  destruct (take n ys); reflexivity.
Qed.

Fixpoint blank (xs:t): bool := match xs with
  | [] => true
  | (w,n)::xs => if (n=?0)%N then blank xs else
      if BoundedConfig.all0 w then blank xs else false
  end.

Lemma blank_spec xs: blank xs=true -> denote xs=0inf.
Proof.
  induction xs as [|[w n] xs IH]; cbn[blank denote]; [reflexivity|].
  destruct (N.eqb_spec n 0); subst; [exact IH|].
  destruct (BoundedConfig.all0 w) eqn:E; [|discriminate].
  intro H; rewrite (IH H).
  apply BoundedConfig.all0_spec in E.
  induction (N.to_nat n) as [|k IHk]; [reflexivity|].
  cbn[lpow]; rewrite Str_app_assoc,IHk; exact E.
Qed.
Fixpoint remove (w:list Sym) (xs:t) : option t := match w with
  | [] => Some xs
  | b::w => let '(c,ys) := pop xs in
    if Eqb.eqb b c then remove w ys else None
  end.

Lemma remove_spec w xs ys : remove w xs=Some ys -> denote xs=w *> denote ys.
Proof.
  gen xs. induction w; intros xs H; cbn [remove] in H.
  - inverts H. reflexivity.
  - pose proof (pop_spec xs) as E. destruct (pop xs) as [b zs]; cbn in E.
    destruct (Eqb.eqb_spec a b); try discriminate. subst.
    rewrite E,(IHw _ H). reflexivity.
Qed.

Lemma commute_power (x v w:list Sym) a b k :
  x++v^^a=w^^b++x -> x++v^^(k*a)=w^^(k*b)++x.
Proof.
  intros H. induction k.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn [Nat.mul]. rewrite !lpow_add,app_assoc,H,<-app_assoc,IHk,app_assoc.
    reflexivity.
Qed.

(* Check one short periodic identity, then move an arbitrary number of
   groups. This also handles rotated and differently sized RLE words. *)
Definition skip_block w limit x v m ys : option (N*t) :=
  let a := N.of_nat (List.length w) in let b := N.of_nat (List.length v) in
  let k := N.min (limit/b) (m/a) in
  if (0<?k)%N then
  if (k*b<=?limit)%N then if (k*a<=?m)%N then
  if Eqb.eqb (x++v^^List.length w) (w^^List.length v++x) then
    Some ((k*b)%N,push x 1 (push v (m-k*a) ys))
  else None else None else None else None.

Lemma skip_block_spec w limit x v m ys n zs :
  skip_block w limit x v m ys=Some (n,zs) ->
  (n<=limit)%N /\ x *> v^^N.to_nat m *> denote ys = w^^N.to_nat n *> denote zs.
Proof.
  unfold skip_block.
  generalize (N.min (limit/N.of_nat (List.length v)) (m/N.of_nat (List.length w))) as k.
  intros k H. destruct (N.ltb_spec 0 k); try discriminate.
  destruct (N.leb_spec (k*N.of_nat (List.length v)) limit); try discriminate.
  destruct (N.leb_spec (k*N.of_nat (List.length w)) m); try discriminate.
  destruct (Eqb.eqb_spec (x++v^^List.length w) (w^^List.length v++x)); inverts H.
  split; [assumption|]. rewrite !push_spec.
  change (N.to_nat 1) with 1%nat. cbn [lpow]. rewrite app_nil_r.
  rewrite N2Nat.inj_mul,Nat2N.id.
  replace (N.to_nat m) with
    (N.to_nat k*List.length w+N.to_nat (m-k*N.of_nat (List.length w))) by lia.
  rewrite lpow_add,!Str_app_assoc.
  rewrite <-Str_app_assoc,(commute_power x v w _ _ _ e),!Str_app_assoc.
  reflexivity.
Qed.

Definition skip_periodic w n xs := match xs with
  | (x,Npos xH)::(v,m)::ys => skip_block w n x v m ys
  | (v,m)::ys => skip_block w n [] v m ys
  | [] => None end.

Lemma skip_periodic_spec w n xs k ys : skip_periodic w n xs=Some (k,ys) ->
  (k<=n)%N /\ denote xs=w^^N.to_nat k *> denote ys.
Proof.
  unfold skip_periodic. destruct xs as [|[x [|[p|p|]]] xs]; try discriminate;
    try (apply skip_block_spec).
  destruct xs as [|[v m] xs]; [apply skip_block_spec|].
  cbn [denote]. change (N.to_nat 1) with 1%nat.
  cbn [lpow]. rewrite app_nil_r. apply skip_block_spec.
Qed.

(* The common aligned case needs no division or periodic-word comparison. *)
Definition skip w n xs := match xs with
  | (v,m)::ys=>if Eqb.eqb w v then
      let k:=N.min n m in Some(k,push v (m-k) ys)
    else skip_periodic w n xs
  | []=>None end.
Lemma skip_spec w n xs k ys : skip w n xs=Some(k,ys) ->
  (k<=n)%N /\ denote xs=w^^N.to_nat k *> denote ys.
Proof.
  destruct xs as [|[v m] xs]; cbn [skip]; [discriminate|].
  destruct(Eqb.eqb_spec w v); subst; [|apply skip_periodic_spec].
  intros H; inverts H. split; [apply N.le_min_l|].
  cbn [denote]. rewrite push_spec,<-Str_app_assoc,<-lpow_add.
  f_equal; f_equal; lia.
Qed.

Fixpoint remove_fast fuel w n xs : option t :=
  if (n=?0)%N then Some xs else match fuel with
  | Datatypes.O => None
  | S fuel => match skip w n xs with
    | Some (k,ys) => remove_fast fuel w (n-k)%N ys
    | None => match remove w xs with
      | Some ys => remove_fast fuel w (N.pred n) ys
      | None => None end
    end
  end.

Lemma remove_fast_spec fuel w n xs ys : remove_fast fuel w n xs=Some ys ->
  denote xs=w^^N.to_nat n *> denote ys.
Proof.
  gen n xs ys. induction fuel; intros n xs ys H; cbn [remove_fast] in H;
    destruct (N.eqb_spec n 0); try discriminate; subst; try solve [inverts H; reflexivity].
  destruct (skip w n xs) as [[k zs]|] eqn:E.
  - destruct (skip_spec _ _ _ _ _ E) as [Hk E1].
    rewrite E1,(IHfuel _ _ _ H),<-Str_app_assoc,<-lpow_add.
    f_equal; f_equal; lia.
  - destruct (remove w xs) as [zs|] eqn:E1; try discriminate.
    rewrite (remove_spec _ _ _ E1),(IHfuel _ _ _ H).
    replace (N.to_nat n) with (1+N.to_nat (N.pred n)) by lia.
    cbn [Nat.add lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Fixpoint equal fuel (xs ys:t): bool := match xs with
  | [] => blank ys
  | (w,n)::xs => match remove_fast fuel w n ys with
    | Some zs => equal fuel xs zs | None => false end
  end.

Lemma equal_spec fuel xs ys: equal fuel xs ys=true -> denote xs=denote ys.
Proof.
  gen ys; induction xs as [|[w n] xs IH]; intros ys H.
  - symmetry; apply blank_spec; assumption.
  - change (match remove_fast fuel w n ys with Some zs => equal fuel xs zs | None => false end=true) in H.
    cbn[denote].
    destruct (remove_fast fuel w n ys) as [zs|] eqn:E; [|discriminate].
    rewrite (remove_fast_spec _ _ _ _ _ E), (IH _ H); reflexivity.
Qed.
End Runs.
Set Implicit Arguments.

Record config := Cfg { left: Runs.t; right: Runs.t; state: Q; direction: dir }.
Definition denote c := match direction c with
  | L => Runs.denote (left c) <{{state c}} Runs.denote (right c)
  | R => Runs.denote (left c) {{state c}}> Runs.denote (right c)
  end.

Definition equal_config fuel c d :=
  if Eqb.eqb (state c) (state d) then
  if Eqb.eqb (direction c) (direction d) then
  if Runs.equal fuel (left c) (left d) then Runs.equal fuel (right c) (right d)
  else false else false else false.

Lemma equal_config_spec fuel c d: equal_config fuel c d=true -> denote c=denote d.
Proof.
  destruct c as [l r q s], d as [l' r' q' s']; unfold equal_config; cbn[left right state direction].
  destruct (Eqb.eqb_spec q q'); [subst|discriminate].
  destruct (Eqb.eqb_spec s s'); [subst|discriminate].
  destruct (Runs.equal fuel l l') eqn:E; [|discriminate].
  intro H; apply Runs.equal_spec in E; apply Runs.equal_spec in H.
  destruct s'; cbn[denote left right state direction]; congruence.
Qed.

Definition rn one n: Runs.t := [(digits one n,1%N)].
Definition rk a n := Cfg [] ((U,a)::rn O n) C L.

Lemma Num_digits_eq one m n r: Num one m r -> m=N.to_nat n -> r=digits one n *> 0inf.
Proof. intros H ->; eapply Num_unique; [exact H|apply digits_spec]. Qed.

Inductive action :=
| RootOdd (k n:N) | RootEven (k n:N) | RootUnit (k:N)
| SBatch (k b:N) (l:Runs.t)
| TBatch (k j n:N) (l:Runs.t)
| CBatch (k c j n:N) (l:Runs.t)
| Inc (n:N) (l:Runs.t)
| EZero (n:N) (l:Runs.t) | EOne (n:N) (l:Runs.t)
| DZero (n:N) (l:Runs.t) | DOne (n:N) (l:Runs.t) | DThree (n:N) (l:Runs.t)
| CarryR (k:N) (l r:Runs.t) | CarryL (k:N) (l r:Runs.t)
| Emit (r:Runs.t).

Definition kernel a: config*config := match a with
| RootOdd k n => (rk (1+k*2) n, rk (2+k*2) (1+n))
| RootEven k n => (Cfg [] ((U,(2+k*2)%N)::(Z,1%N)::rn O n) C L, rk (4+k*2) (1+n))
| RootUnit k => (rk (2+k*2) 1, rk (5+k*4) 2)
| SBatch k b l =>
    (Cfg ((rev P,b)::(rev W,k)::l) [([1;0;0;0;0;1],1%N)] D R,
     Cfg ((rev P,(b+k*2)%N)::l) [([1;0;0;0;0;1],1%N)] D R)
| TBatch k j n l =>
    (Cfg ((rev W,(1+k)%N)::l) ((V,(1+j*2)%N)::rn I n) A L,
     Cfg ((rev W,1%N)::l) ((V,(1+j*2+k*2)%N)::rn I (n+k*2)) A L)
| CBatch k c j n l =>
    (Cfg ((rev J,1%N)::(rev Qw,c)::(rev W1,1%N)::(rev W,(k*2)%N)::l)
       ((V,(1+j*2)%N)::rn I n) A L,
     Cfg ((rev J,1%N)::(rev Qw,(c+k*2)%N)::(rev W1,1%N)::l)
       ((V,(1+j*2)%N)::rn I (n+k)) A L)
| Inc n l => (Cfg l (rn O n) B R, Cfg l (rn O (1+n)) C L)
| EZero n l => (Cfg l ((Z,1%N)::rn O n) E R, Cfg l ((I,1%N)::rn O n) A L)
| EOne n l => (Cfg l ((O,1%N)::rn O n) E R, Cfg l (([1;0;1],1%N)::rn O n) B L)
| DZero n l => (Cfg l ((Z,1%N)::rn O n) D R, Cfg l (([0;0;1],1%N)::rn O n) F L)
| DOne n l => (Cfg l ((O,1%N)::(Z,1%N)::rn O n) D R, Cfg l (([1;0;1;1;0;1],1%N)::rn O n) B L)
| DThree n l => (Cfg l ((O,1%N)::(O,1%N)::rn O n) D R, Cfg l ((U,2%N)::rn O (2+n)) C L)
| CarryR k l r =>
    (Cfg l (([1;1;1;0;1;1],1%N)::([0;1;1;0;1;1],k)::r) E R,
     Cfg ((rev Qw,k)::l) (([1;1;1;0;1;1],1%N)::r) E R)
| CarryL k l r =>
    (Cfg ((rev Qw,k)::l) (([1;1;1;0;1;1],1%N)::r) D L,
     Cfg l (([1;1;1;0;1;1],1%N)::([0;1;1;0;1;1],k)::r) D L)
| Emit r => (Cfg [] r C L, Cfg [(<[1;0],1%N)] r E R)
end.

Ltac ds := cbn[kernel fst snd rk rn denote left right state direction Runs.denote];
  change (N.to_nat 1) with 1%nat; cbn[lpow app]; rewrite ?app_nil_r.

Lemma kernel_spec a: denote (fst (kernel a)) -->* denote (snd (kernel a)).
Proof.
  destruct a.
  - destruct (root_odd (N.to_nat k) (digits_spec O n)) as [s [Ns H]].
    assert (E:s=digits O (1+n) *> 0inf) by (eapply Num_digits_eq; [exact Ns|lia]).
    subst s; ds; apply progress_evstep; applys_eq H; unfold K; flia.
  - destruct (root_even (N.to_nat k) (digits_spec O n)) as [s [Ns H]].
    assert (E:s=digits O (1+n) *> 0inf) by (eapply Num_digits_eq; [exact Ns|lia]).
    subst s; ds; apply progress_evstep; applys_eq H; unfold K; flia.
  - ds; apply progress_evstep; applys_eq (root_unit (N.to_nat k)); unfold K; flia.
  - ds; applys_eq (s_batch (N.to_nat k) (N.to_nat b) (Runs.denote l)); flia.
  - destruct (t_batch (N.to_nat k) (N.to_nat j) (digits_spec I n)) as [s [Ns H]].
    assert (E:s=digits I (n+k*2) *> 0inf) by (eapply Num_digits_eq; [exact Ns|lia]).
    subst s; ds; applys_eq (H (Runs.denote l)); flia.
  - destruct (coupled_batch (N.to_nat k) (N.to_nat c) (N.to_nat j) (digits_spec I n)) as [s [Ns H]].
    assert (E:s=digits I (n+k) *> 0inf) by (eapply Num_digits_eq; [exact Ns|lia]).
    subst s; ds; applys_eq (H (Runs.denote l)); flia.
  - destruct (increment (digits_spec O n)) as [s [Ns H]].
    assert (E:s=digits O (1+n) *> 0inf) by (eapply Num_digits_eq; [exact Ns|lia]).
    subst s; ds; apply progress_evstep; exact (sideRLs_1 _ _ _ _ _ H (Runs.denote l)).
  - ds; apply progress_evstep; apply binary_E0.
  - ds; apply progress_evstep; apply binary_E1.
  - ds; apply progress_evstep; apply binary_D0.
  - ds; apply progress_evstep; apply binary_D1.
  - destruct (binary_D3 (digits_spec O n)) as [s [Ns H]].
    assert (E:s=digits O (2+n) *> 0inf) by (eapply Num_digits_eq; [exact Ns|lia]).
    subst s; ds; apply progress_evstep; apply H.
  - ds; apply carry_right.
  - ds; apply carry_left.
  - ds; apply progress_evstep; apply emit.
Qed.

Definition apply_action fuel a c: option config :=
  let '(src,dst):=kernel a in if equal_config fuel c src then Some dst else None.

Lemma apply_action_spec fuel a c d: apply_action fuel a c=Some d -> denote c -->* denote d.
Proof.
  unfold apply_action; pose proof (kernel_spec a) as H.
  destruct (kernel a) as [src dst]; cbn[fst snd] in H.
  destruct (equal_config fuel c src) eqn:E; [|discriminate].
  intro G; inverts G; apply equal_config_spec in E; rewrite E; exact H.
Qed.

(* Representation changes are proposals too: only the checked result is
   used.  Thus a failed budget/heuristic cannot change the represented tape. *)
Fixpoint feed (bs:list Sym) acc: list Sym*Runs.t := match bs with
  | a::b::c::d::e::f::bs => feed bs (Runs.push [a;b;c;d;e;f] 1 acc)
  | _ => (bs,acc)
  end.

Definition feed_six p w n acc := match n with
  | N0 => (p,acc)
  | Npos _ => let '(p,acc):=feed (p++w) acc in
      (p,Runs.push (firstn 6 (p++w)) (N.pred n) acc)
  end.

Definition feed_run p w n acc: option (list Sym*Runs.t) :=
  if (n=?0)%N then Some (p,acc) else
  match w with
  | [] => Some (p,acc)
  | [_;_;_;_;_;_] => Some (feed_six p w n acc)
  | [_;_;_] => let '(p,acc):=feed_six p (w++w) (N.div2 n) acc in
      Some (if N.odd n then feed (p++w) acc else (p,acc))
  | _ => if (n=?1)%N then Some (feed (p++w) acc) else None
  end.

Fixpoint trim (xs:Runs.t) := match xs with
  | (w,n)::xs' => if BoundedConfig.all0 w then trim xs' else xs
  | [] => []
  end.
Fixpoint pack_aux xs p acc: option Runs.t := match xs with
  | [] => Some (fast_rev (trim (Runs.push (p++repeat 0 (6-List.length p)) 1 acc)))
  | (w,n)::xs => match feed_run p w n acc with
    | Some (p,acc) => pack_aux xs p acc | None => None end
  end.
Definition repack fuel xs := match pack_aux xs [] [] with
  | Some ys => if Runs.equal fuel xs ys then ys else xs
  | None => xs end.

Lemma repack_spec fuel xs: Runs.denote (repack fuel xs)=Runs.denote xs.
Proof.
  unfold repack; destruct (pack_aux xs [] []) as [ys|]; [|reflexivity].
  destruct (Runs.equal fuel xs ys) eqn:E; [symmetry; apply Runs.equal_spec in E; assumption|reflexivity].
Qed.

Definition normalize fuel c := Cfg (repack fuel (left c)) (repack fuel (right c)) (state c) (direction c).
Lemma normalize_spec fuel c: denote (normalize fuel c)=denote c.
Proof. destruct c as [l r q []]; cbn[normalize denote left right state direction]; rewrite !repack_spec; reflexivity. Qed.

Definition embed l r x := match x with
  | BoundedConfig.Build_T a b q L => Cfg (Runs.push b 1 l) (Runs.push a 1 r) q L
  | BoundedConfig.Build_T a b q R => Cfg (Runs.push a 1 l) (Runs.push b 1 r) q R
  end.
Lemma embed_spec l r x: denote (embed l r x)=BoundedConfig.to_config x (Runs.denote l) (Runs.denote r).
Proof.
  destruct x as [a b q []]; cbn[embed denote left right state direction BoundedConfig.to_config];
    rewrite !Runs.push_spec; change (N.to_nat 1) with 1%nat;
    cbn[lpow app]; rewrite ?app_nil_r; reflexivity.
Qed.

Definition at_root (flag:bool) (x:BoundedConfig.T) := if flag then match x with
  | BoundedConfig.Build_T _ w C L => BoundedConfig.all0 w
  | _ => false end else false.
Fixpoint small_core fuel flag x := match fuel with
  | Datatypes.O => x
  | S fuel => if at_root flag x then x else match BoundedConfig.step tm x with
    | Some y => small_core fuel flag y | None => x end
  end.

Lemma small_core_spec fuel flag x: forall l r,
  BoundedConfig.to_config x l r -->* BoundedConfig.to_config (small_core fuel flag x) l r.
Proof.
  gen x; induction fuel; intros x l r; [finish|].
  cbn[small_core]; destruct (at_root flag x); [finish|].
  pose proof (BoundedConfig.step_spec tm x) as H.
  destruct (BoundedConfig.step tm x) as [y|]; [|finish].
  eapply evstep_step; [apply H|apply IHfuel].
Qed.

Definition small fuel c :=
  let '(w,l,r):=match direction c with
    | L => let '(w,l):=Runs.take 6 (left c) in (w,l,right c)
    | R => let '(w,r):=Runs.take 6 (right c) in (w,left c,r)
    end in
  embed l r (small_core fuel (Runs.blank l) (BoundedConfig.Build_T [] w (state c) (direction c))).

Lemma small_spec fuel c: denote c -->* denote (small fuel c).
Proof.
  destruct c as [l r q []]; unfold small; cbn[left right state direction].
  - pose proof (Runs.take_spec 6 l) as H; destruct (Runs.take 6 l) as [w xs]; cbn in H.
    rewrite embed_spec; cbn[denote left right state direction]; rewrite H.
    exact (small_core_spec fuel (Runs.blank xs) (BoundedConfig.Build_T [] w q L) (Runs.denote xs) (Runs.denote r)).
  - pose proof (Runs.take_spec 6 r) as H; destruct (Runs.take 6 r) as [w xs]; cbn in H.
    rewrite embed_spec; cbn[denote left right state direction]; rewrite H.
    exact (small_core_spec fuel (Runs.blank l) (BoundedConfig.Build_T [] w q R) (Runs.denote l) (Runs.denote xs)).
Qed.

Definition shift c: option config :=
  let xs:=match direction c with L=>left c | R=>right c end in
  match xs with
  | (w,n)::xs => match block (state c) (direction c) w with
    | Some (BoundedConfig.Build_T v [] q d,true) =>
      if Eqb.eqb q (state c) then if Eqb.eqb d (direction c) then
        Some (match d with
          | L => Cfg xs (Runs.push v n (right c)) q L
          | R => Cfg (Runs.push v n (left c)) xs q R end)
      else None else None
    | _ => None end
  | [] => None end.

Lemma shift_spec c c': shift c=Some c' -> denote c -->* denote c'.
Proof.
  destruct c as [l r q d]; unfold shift; cbn[left right state direction].
  destruct d.
  - destruct l as [|[w n] xs]; [discriminate|].
    destruct (block q L w) as [[[v [|b bs] q' d'] p]|] eqn:E; try discriminate.
    destruct p; [|discriminate].
    destruct (Eqb.eqb_spec q' q); [subst|discriminate].
    destruct (Eqb.eqb_spec d' L); [subst|discriminate].
    intro H; inverts H; cbn[denote left right state direction Runs.denote]; rewrite Runs.push_spec.
    exact (@block_left q w v (N.to_nat n) E (Runs.denote xs) (Runs.denote r)).
  - destruct r as [|[w n] xs]; [discriminate|].
    destruct (block q R w) as [[[v [|b bs] q' d'] p]|] eqn:E; try discriminate.
    destruct p; [|discriminate].
    destruct (Eqb.eqb_spec q' q); [subst|discriminate].
    destruct (Eqb.eqb_spec d' R); [subst|discriminate].
    intro H; inverts H; cbn[denote left right state direction Runs.denote]; rewrite Runs.push_spec.
    exact (@block_right q w v (N.to_nat n) E (Runs.denote l) (Runs.denote xs)).
Qed.

Fixpoint parse_num fuel one xs: option N :=
  if Runs.blank xs then Some 0%N else match fuel with
  | Datatypes.O => None
  | S fuel => let '(w,ys):=Runs.take 3 xs in
    if Eqb.eqb w Z then match parse_num fuel one ys with
      | Some n => Some (n*2)%N | None => None end
    else if Eqb.eqb w one then match parse_num fuel one ys with
      | Some n => Some (1+n*2)%N | None => None end else None
  end.

Definition params fuel u one xs: option (N*N) :=
  let '(a,xs):=match xs with
    | (w,k)::ys => if Eqb.eqb w (u++u) then ((k*2)%N,ys) else (0%N,xs)
    | [] => (0%N,[]) end in
  let '(w,ys):=Runs.take 3 xs in
  let '(a,xs):=if Eqb.eqb w u then ((1+a)%N,ys) else (a,xs) in
  match parse_num fuel one xs with Some n=>Some (a,n) | None=>None end.

Definition guess_root fuel r := match params fuel U O r with
  | Some (a,n) => if (0<?a)%N then
    if N.odd a then RootOdd (N.div2 a) n else
    if N.even n then RootEven (N.pred (N.div2 a)) (N.div2 n) else
    if (n=?1)%N then RootUnit (N.pred (N.div2 a)) else Emit r
    else Emit r
  | None => Emit r end.

Definition guess_C fuel l r := match l with
  | ([0;0;1;1;0;1],Npos xH)::l =>
    let '(c,l):=match l with
      | ([1;0;1;0;0;0],c)::l => (c,l) | _ => (0%N,l) end in
    match l with
    | ([1;0;0;1;0;0],Npos xH)::([0;1;0;1;0;0],k)::l =>
      if (1<?k)%N then match params fuel V I r with
      | Some (b,n) => if N.odd b then
        Some (CBatch (N.div2 k) c (N.div2 b) n (Runs.push (rev W) (N.modulo k 2) l))
        else None
      | None => None end else None
    | _ => None end
  | _ => None end.

Definition guess_T fuel l r := match l with
  | ([0;1;0;1;0;0],k)::l => if (1<?k)%N then match params fuel V I r with
    | Some (b,n) => if N.odd b then Some (TBatch (N.pred k) (N.div2 b) n l) else None
    | None => None end else None
  | _ => None end.

Definition guess_S l r := match l,r with
  | ([0;1;0;0;0;1],b)::([0;1;0;1;0;0],k)::l,[([1;0;0;0;0;1],Npos xH)] => Some (SBatch k b l)
  | _,_ => None end.

Definition guess_binary fuel q l r := match params fuel U O r with
  | Some (N0,n) => match q with
    | B => Some (Inc n l)
    | E => Some (if N.odd n then EOne (N.div2 n) l else EZero (N.div2 n) l)
    | D => Some (if N.even n then DZero (N.div2 n) l else
        if N.odd (N.div2 n) then DThree (N.div2 (N.div2 n)) l else DOne (N.div2 (N.div2 n)) l)
    | _ => None end
  | _ => None end.

Definition guess_carry q d l r := match q,d,l,r with
  | E,R,_,([1;1;1;0;1;1],Npos xH)::([0;1;1;0;1;1],k)::r => Some (CarryR k l r)
  | D,L,([1;0;1;0;0;0],k)::l,([1;1;1;0;1;1],Npos xH)::r => Some (CarryL k l r)
  | _,_,_,_ => None end.

Definition propose fuel c := let l:=left c in let r:=right c in
  match state c,direction c with
  | C,L => if Runs.blank l then Some (guess_root fuel r) else None
  | A,L => match guess_C fuel l r with Some a=>Some a | None=>guess_T fuel l r end
  | D,R => match guess_S l r with Some a=>Some a | None=>guess_binary fuel D l r end
  | B,R => guess_binary fuel B l r
  | E,R => match guess_binary fuel E l r with Some a=>Some a | None=>guess_carry E R l r end
  | D,L => guess_carry D L l r
  | _,_ => None end.

Definition next (guess:config->option action) mfuel bfuel c :=
  normalize mfuel (match guess c with
    | Some a => match apply_action mfuel a c with
      | Some d => d
      | None => match shift c with Some d=>d | None=>small bfuel c end end
    | None => match shift c with Some d=>d | None=>small bfuel c end
    end).

Lemma next_spec guess mfuel bfuel c: denote c -->* denote (next guess mfuel bfuel c).
Proof.
  unfold next; rewrite normalize_spec.
  destruct (guess c) as [a|]; [destruct (apply_action mfuel a c) as [d|] eqn:E|].
  - eapply apply_action_spec; exact E.
  - destruct (shift c) as [d|] eqn:F; [eapply shift_spec; exact F|apply small_spec].
  - destruct (shift c) as [d|] eqn:F; [eapply shift_spec; exact F|apply small_spec].
Qed.

Definition guess_loop fuel c := match params fuel U O (right c) with
  | Some (a,n) => if (n=?2)%N then if (1<?a)%N then
      if N.even a then Some (N.pred (N.div2 a)) else None else None else None
  | None => None end.
Definition done (guess:config->option N) fuel c := match guess c with
  | Some k => equal_config fuel c (rk (2+k*2) 2)
  | None => false end.

Lemma done_spec guess fuel c: done guess fuel c=true -> ~halts tm (denote c).
Proof.
  unfold done; destruct (guess c) as [k|]; [|discriminate].
  intro H; apply equal_config_spec in H; rewrite H.
  ds; applys_eq (absorbing_nonhalt (N.to_nat k)); unfold K; flia.
Qed.

Fixpoint run fuel guess terminal mfuel bfuel c :=
  if done terminal mfuel c then c else match fuel with
  | Datatypes.O => c
  | S fuel => run fuel guess terminal mfuel bfuel (next guess mfuel bfuel c)
  end.

Lemma run_spec fuel guess terminal mfuel bfuel c:
  denote c -->* denote (run fuel guess terminal mfuel bfuel c).
Proof.
  gen c; induction fuel; intro c; cbn[run]; destruct (done terminal mfuel c); try solve [finish].
  eapply evstep_trans; [apply next_spec|apply IHfuel].
Qed.

Definition start := Cfg [] [] A R.
Definition chunk := run 1000 (propose 128) (guess_loop 128) 32 30.
Definition finish_run c := done (guess_loop 128) 32 c.

Fixpoint batches n c := if finish_run c then c else match n with
  | Datatypes.O => c
  | S n => batches n (chunk c)
  end.
Lemma batches_spec n c: denote c -->* denote (batches n c).
Proof.
  gen c; induction n; intro c; cbn[batches]; destruct (finish_run c); try solve [finish].
  eapply evstep_trans; [apply run_spec|apply IHn].
Qed.

Definition check n := finish_run (batches n start).
Lemma check_spec n: check n=true -> ~halts tm c0.
Proof.
  intro H; change (~halts tm (denote start)).
  eapply multistep_nonhalt; [apply batches_spec|].
  apply (@done_spec (guess_loop 128) 32); exact H.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. apply (@check_spec 700); native_check_eq. Qed.

End TM10.

(* BEC.txt TM11/TM12: shared counter semantics.  The final invariant is
   described in BEC_PAIR1112_NONHALTING.txt. *)
Set Implicit Arguments.

Module PairCounter.

(* H is the left counter's return, not ordinary binary addition. *)
Inductive H : nat -> nat -> Prop :=
| H_even n: H (n*2) (1+n*2)
| H_carry j x y: H x y ->
    H (x*2^(2+j)+(2^(1+j)-1)) (y*2^(2+j)).

Inductive Steps : nat -> nat -> nat -> Prop :=
| Steps_zero x: Steps 0 x x
| Steps_next n x y z: H x y -> Steps n y z -> Steps (1+n) x z.

Lemma steps_one x y: H x y -> Steps 1 x y.
Proof. intro I; econstructor; [exact I|constructor]. Qed.
Lemma steps_trans n m x y z: Steps n x y -> Steps m y z -> Steps (n+m) x z.
Proof. intros I J; induction I; [exact J|econstructor; eauto]. Qed.
Lemma H_even_inv x y: H (x*2) y -> y=1+x*2.
Proof. intro I; inversion I; cbn[Nat.pow Nat.add] in *; nia. Qed.
Lemma steps_drop_even a x y: 0<a -> Steps a (x*2) y -> Steps (a-1) (1+x*2) y.
Proof.
  intros A I; inversion I as [|n x' u y' J K]; subst; try lia.
  rewrite (H_even_inv x J) in K; applys_eq K; flia.
Qed.
Lemma H_four x y: H x y -> H (1+x*4) (y*4).
Proof. intro I; applys_eq (H_carry 0 I); cbn[Nat.pow]; flia. Qed.
Lemma H_eight x y: H x y -> H (3+x*8) (y*8).
Proof. intro I; applys_eq (H_carry 1 I); cbn[Nat.pow]; flia. Qed.
Lemma H_zero4 x: H (x*4) (1+x*4).
Proof. applys_eq (H_even (x*2)); flia. Qed.
Lemma pair_zero x y: H x y -> Steps 2 (x*4) (y*4).
Proof.
  intro I; econstructor; [applys_eq (H_even (x*2)); flia|].
  apply steps_one; applys_eq (H_four I); flia.
Qed.
Lemma pair_two x y: H x y -> Steps 2 (2+x*8) (y*2*4).
Proof.
  intro I; econstructor; [applys_eq (H_even (1+x*4)); flia|].
  apply steps_one; applys_eq (H_eight I); flia.
Qed.
Lemma steps_four n x y: Steps n x y -> Steps (n*2) (x*4) (y*4).
Proof.
  intro I; induction I; [constructor|].
  applys_eq (steps_trans (pair_zero H0) IHI); flia.
Qed.
Lemma steps_zeros k n x y: Steps n x y ->
  Steps (n*2^k) (x*4^k) (y*4^k).
Proof.
  intro I; induction k; [cbn[Nat.pow]; applys_eq I; flia|].
  applys_eq (steps_four IHk); cbn[Nat.pow]; flia.
Qed.

(* Low k quaternary digits are 0/1, their binary value is z; the arbitrary
   high part w is deliberately not required to be normal. *)
Inductive Field : nat -> nat -> nat -> nat -> Prop :=
| Field_nil w: Field 0 0 w w
| Field_zero k z w x: Field k z w x -> Field (1+k) (z*2) w (x*4)
| Field_one k z w x: Field k z w x -> Field (1+k) (1+z*2) w (1+x*4).

Lemma field_bound k z w x: Field k z w x -> z<2^k.
Proof. intro I; induction I; cbn[Nat.pow Nat.add]; nia. Qed.
Lemma field_zeros k w: Field k 0 w (w*4^k).
Proof.
  induction k; [cbn[Nat.pow]; applys_eq (Field_nil w); flia|].
  applys_eq (Field_zero IHk); cbn[Nat.pow]; flia.
Qed.

Lemma field_exists k z w: z<2^k -> exists x, Field k z w x.
Proof.
  gen z; induction k; intros z B.
  - cbn[Nat.pow] in B; assert (z=0%nat) by lia; subst; eexists; constructor.
  - destruct (mod2 z) as [u ->|u ->];
      destruct (IHk u) as [x F]; try (cbn[Nat.pow] in B; lia).
    + exists (x*4); apply Field_zero, F.
    + exists (1+x*4); apply Field_one, F.
Qed.

Lemma field_unique k z w x: Field k z w x -> forall y, Field k z w y -> x=y.
Proof.
  intro I; induction I; intros y J; inversion J; subst; try lia.
  all: assert (z0=z) by lia; subst z0; rewrite (IHI _ H2); reflexivity.
Qed.

Lemma field_compose k z w x j v y:
  Field k z w x -> Field j v x y -> Field (k+j) (z*2^j+v) w y.
Proof.
  intros I J; induction J.
  - cbn[Nat.pow]; applys_eq I; flia.
  - applys_eq (Field_zero (IHJ I)); cbn[Nat.pow Nat.add]; flia.
  - applys_eq (Field_one (IHJ I)); cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma field_fill k z w x: Field k z w x -> Steps z (w*4^k) x.
Proof.
  intro I; induction I.
  - cbn[Nat.pow]; replace (w*1) with w by lia; constructor.
  - applys_eq (steps_four IHI); cbn[Nat.pow Nat.add]; flia.
  - applys_eq (steps_trans (steps_four IHI) (steps_one (H_zero4 x)));
      cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma field_inc k z w x: Field k z w x -> 1+z<2^k ->
  exists y, Field k (1+z) w y /\ H x y.
Proof.
  intro I; induction I; intro B.
  - cbn[Nat.pow] in B; lia.
  - exists (1+x*4); split; [constructor; assumption|apply H_zero4].
  - destruct IHI as [y [F J]]; [cbn[Nat.pow Nat.add] in B; lia|].
    exists (y*4); split; [applys_eq (Field_zero F); flia|apply H_four; assumption].
Qed.

Lemma field_carry k z w x y: Field k z w x -> 1+z=2^k ->
  H w y -> H x (y*4^k).
Proof.
  intro I; induction I; intros B J.
  - cbn[Nat.pow]; applys_eq J; flia.
  - cbn[Nat.pow Nat.add] in B; lia.
  - applys_eq (H_four (IHI ltac:(cbn[Nat.pow Nat.add] in B; lia) J));
      cbn[Nat.pow Nat.add]; flia.
Qed.

(* An offset counter normalizes exactly when the low part first wraps.
   This is the unbounded part of the packed formula; the high part is arbitrary. *)
Lemma normalize k z w x y: Field k z w x -> 0<z -> H w y ->
  Steps ((2^k-z)*2) (x*2) (y*2*4^k).
Proof.
  gen z w x y; induction k; intros z w x y F Z J;
    inversion F as [w0|k0 z0 w0 x0 I|k0 z0 w0 x0 I]; subst.
  - lia.
  - applys_eq (steps_four (IHk _ _ _ _ I ltac:(lia) J));
      cbn[Nat.pow Nat.add]; flia.
  - pose proof (field_bound I).
    destruct (Nat.eq_dec (1+z0) (2^k)) as [E|E].
    + applys_eq (pair_two (field_carry I E J));
        cbn[Nat.pow Nat.add]; flia.
    + destruct (field_inc I ltac:(lia)) as [u [U K]].
      applys_eq (steps_trans (pair_two K)
        (steps_four (IHk _ _ _ _ U ltac:(lia) J)));
        cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma packed_positive k z w x y n q r y':
  Field k z w x -> 0<z -> H w y -> Steps q (y*2) y' ->
  n=(2^k-z)*2+q*2^k+r -> r<2^k -> exists x',
  Field k r y' x' /\ Steps n (x*2) x'.
Proof.
  intros F Z J K -> B; destruct (field_exists k y' B) as [x' F'].
  exists x'; split; [assumption|].
  eapply steps_trans; [eapply steps_trans; [eapply normalize; eauto|]|].
  - apply steps_zeros, K.
  - apply field_fill, F'.
Qed.

Lemma packed_short w k z x a h: Field k z w x -> 0<z -> H w h ->
  2*2^k<=a+z*2 -> a+z*2<4*2^k -> exists q r u,
  q<=1 /\ r<2^k /\ a+z*2=(2+q)*2^k+r /\
  Field k r (h*2+q) u /\ Steps a (x*2) u.
Proof.
  intros F Z I B C; pose proof (field_bound F).
  destruct (le_dec (3*2^k) (a+z*2)).
  - destruct (@packed_positive k z w x h a 1 (a+z*2-3*2^k) (1+h*2)
      F Z I (steps_one (H_even h)) ltac:(lia) ltac:(lia)) as [u [U J]].
    exists 1%nat,(a+z*2-3*2^k),u; repeat split; try assumption; try lia.
    applys_eq U; flia.
  - destruct (@packed_positive k z w x h a 0 (a+z*2-2*2^k) (h*2)
      F Z I (Steps_zero (h*2)) ltac:(lia) ltac:(lia)) as [u [U J]].
    exists 0%nat,(a+z*2-2*2^k),u; repeat split; try assumption; try lia.
    applys_eq U; flia.
Qed.

Lemma field_low k z w x: Field k z w x -> 0<z -> exists t j v y,
  k=t+1+j /\ z=(1+v*2)*2^t /\ x=(1+y*4)*4^t /\ Field j v w y.
Proof.
  intro I; induction I; intro Z; [lia| |].
  - destruct IHI as [t [j [v [y [K [E [V F]]]]]]]; [lia|].
    exists (1+t),j,v,y; repeat split; cbn[Nat.pow Nat.add]; try nia; assumption.
  - exists 0%nat,k,z,x; repeat split; cbn[Nat.pow]; try lia; assumption.
Qed.

(* The two normal top alphabets.  Constructors encode division by two
   implicitly, including the growing top of the E counter. *)
Inductive Normal : bool -> nat -> nat -> Prop :=
| Normal_D: Normal false 0 0
| Normal_E2: Normal true 2 2
| Normal_E3: Normal true 3 3
| Normal_zero e n x: Normal e n x -> Normal e (n*2) (x*4)
| Normal_one e n x: Normal e n x -> Normal e (1+n*2) (1+x*4).

Lemma normal_step e n x: Normal e n x -> exists y,
  Normal e (1+n) y /\ H x y.
Proof.
  intro I; induction I as [| | |e n x I [y [N J]]|e n x I [y [N J]]].
  - exists 1%nat; split; [exact (Normal_one Normal_D)|exact (H_even 0)].
  - exists 3%nat; split; [constructor|exact (H_even 1)].
  - exists 8%nat; split; [exact (Normal_zero Normal_E2)|].
    applys_eq (H_eight (H_even 0)); flia.
  - exists (1+x*4); split; [constructor; assumption|].
    applys_eq (H_even (x*2)); flia.
  - exists (y*4); split; [applys_eq (Normal_zero N); flia|apply H_four; assumption].
Qed.
Lemma normal_steps e n x a: Normal e n x -> exists y,
  Normal e (n+a) y /\ Steps a x y.
Proof.
  gen n x; induction a; intros n x N.
  - exists x; split; [applys_eq N; flia|constructor].
  - destruct (normal_step N) as [y [Ny I]].
    destruct (IHa _ _ Ny) as [z [Nz J]].
    exists z; split; [applys_eq Nz; flia|econstructor; eauto].
Qed.

Lemma field_normal k z w x: Field k z w x -> forall e n,
  Normal e n w -> Normal e (n*2^k+z) x.
Proof.
  intro I; induction I; intros e n N.
  - cbn[Nat.pow]; applys_eq N; flia.
  - applys_eq (Normal_zero (IHI _ _ N)); cbn[Nat.pow Nat.add]; flia.
  - applys_eq (Normal_one (IHI _ _ N)); cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma packed_normal k z w x y j u e v a:
  Field k z w x -> 0<z -> H w y -> Steps j (y*2) u -> Normal e v u ->
  (2^k-z)*2+j*2^k<=a -> exists x',
  Normal e (v*2^k+(a-((2^k-z)*2+j*2^k))) x' /\ Steps a (x*2) x'.
Proof.
  intros F Z J K N B.
  destruct (normal_steps (a-((2^k-z)*2+j*2^k))
    (field_normal (field_zeros k u) N)) as [x' [N' I]].
  exists x'; split; [applys_eq N'; flia|].
  applys_eq (steps_trans (steps_trans (normalize F Z J) (steps_zeros k K)) I); flia.
Qed.

Lemma packed_zero k w j u e v a: Steps j (w*2) u -> Normal e v u ->
  j*2^k<=a -> exists x',
  Normal e (v*2^k+(a-j*2^k)) x' /\ Steps a (w*4^k*2) x'.
Proof.
  intros J N B; destruct (normal_steps (a-j*2^k)
    (field_normal (field_zeros k u) N)) as [x' [N' I]].
  exists x'; split; [applys_eq N'; flia|].
  applys_eq (steps_trans (steps_zeros k J) I); flia.
Qed.

Lemma packed_zero_affine k w j u e v a: Steps j (w*2) u ->
  Normal e (v+j) u -> j*2^k<=a -> exists x',
  Normal e (a+v*2^k) x' /\ Steps a (w*4^k*2) x'.
Proof.
  intros I N B; destruct (@packed_zero k w j u e (v+j) a I N B) as [x' [N' J]].
  exists x'; split; [applys_eq N'; nia|assumption].
Qed.

Lemma packed_positive_affine k z w x y j u e v a:
  Field k z w x -> 0<z -> H w y -> Steps j (y*2) u ->
  Normal e (v+j+2) u -> (j+2)*2^k<=a+z*2 -> exists x',
  Normal e (a+z*2+v*2^k) x' /\ Steps a (x*2) x'.
Proof.
  intros F Z I J N B; pose proof (field_bound F).
  destruct (@packed_normal k z w x y j u e (v+j+2) a F Z I J N ltac:(nia))
    as [x' [N' K]].
  exists x'; split; [applys_eq N'; nia|assumption].
Qed.

Lemma normal_zero_value e x: Normal e 0 x -> e=false /\ x=0%nat.
Proof.
  intro I; remember 0%nat as n; induction I; try solve [split; reflexivity]; try lia.
  assert (n=0%nat) by lia; subst; destruct IHI as [-> ->]; auto.
Qed.

(* A positive normal counter has one of just three top digits.  In
   particular D uses top 1, avoiding a separate power-of-two subcase. *)
Lemma normal_top e n x: Normal e n x -> 0<n -> exists k z w,
  Field k z w x /\ n=w*2^k+z /\
  ((e=false /\ w=1%nat) \/ (e=true /\ (w=2 \/ w=3))).
Proof.
  intro I; induction I; intro Z; try lia.
  - exists 0%nat,0%nat,2%nat; split; [constructor|]; split; [reflexivity|auto].
  - exists 0%nat,0%nat,3%nat; split; [constructor|]; split; [reflexivity|auto].
  - destruct IHI as [k [z [w [F [E T]]]]]; [lia|].
    exists (1+k),(z*2),w; split; [constructor; assumption|].
    split; [cbn[Nat.pow Nat.add]; nia|assumption].
  - destruct (Nat.eq_dec n 0) as [->|N].
    + destruct (normal_zero_value I) as [-> ->].
      exists 0%nat,0%nat,1%nat; split; [constructor|]; split; [reflexivity|auto].
    + destruct IHI as [k [z [w [F [E T]]]]]; [lia|].
      exists (1+k),(1+z*2),w; split; [constructor; assumption|].
      split; [cbn[Nat.pow Nat.add]; nia|assumption].
Qed.

Inductive View : bool -> nat -> nat -> Prop :=
| View_low e v x t: Normal e v x ->
    View e ((1+v*2)*2^t) ((1+x*4)*4^t)
| View_two t: View true (2*2^t) (2*4^t)
| View_three t: View true (3*2^t) (3*4^t).

Lemma normal_view e n x: Normal e n x -> 0<n -> View e n x.
Proof.
  intro I; induction I; intro Z; try lia.
  - applys_eq (View_two 0); cbn[Nat.pow]; flia.
  - applys_eq (View_three 0); cbn[Nat.pow]; flia.
  - destruct (IHI ltac:(lia)).
    + applys_eq (View_low (1+t) H0); cbn[Nat.pow Nat.add]; flia.
    + applys_eq (View_two (1+t)); cbn[Nat.pow Nat.add]; flia.
    + applys_eq (View_three (1+t)); cbn[Nat.pow Nat.add]; flia.
  - applys_eq (View_low 0 I); cbn[Nat.pow]; flia.
Qed.

Inductive Return : nat -> nat -> nat -> nat -> nat -> Prop :=
| Return_odd t x y a: H x y -> Return ((1+x*2)*4^t) a y (a+t) 0
| Return_power t a: Return (2*4^t) a 1 1 (a+t).

Lemma field_return k z w x a: Field k z w x -> 0<z -> exists t j v y,
  Field j v w y /\ k=t+1+j /\ z=(1+v*2)*2^t /\
  Return x a (1+y*2) (a+t) 0.
Proof.
  intros F Z; destruct (field_low F Z) as [t [j [v [y [K [E [-> J]]]]]]].
  exists t,j,v,y; repeat split; try assumption.
  applys_eq (Return_odd t a (H_even y)); flia.
Qed.

Definition Round x a b y a' b' := exists u,
  Steps (a-1) x u /\ Return u (a+b+1) y a' b'.

Definition Budget a v := v<a /\ (a mod 2=1%nat -> v*2<a).
Inductive Safe : nat -> nat -> nat -> Prop :=
| Safe_main e v x a: Normal e v x -> Budget a v -> Safe (1+x*2) a 0
| Safe_high w k z x a: (w=6 \/ w=7) -> Field k z w x ->
    Budget a (w*2^k+z) -> Safe (1+x*2) a 0
| Safe_raw x a: (x=4 \/ x=8 \/ x=16) -> 0<a -> Safe x a 0
| Safe_weak e v x: Normal e v x -> 0<v -> Safe (1+x*2) (v*2-1) 0
| Safe_near w k z x a: (w=10 \/ w=11) -> Field k z w x ->
    8*2^k<=a -> Safe (1+x*2) a 0
| Safe_reset a b: 0<a -> 0<b -> Safe 1 a b.

Lemma budget_strong a v: v*2<a -> Budget a v.
Proof. unfold Budget; lia. Qed.
Lemma safe_positive x a b: Safe x a b -> 0<a.
Proof. intro I; destruct I; unfold Budget in *; lia. Qed.

Lemma budget_return a n t v: n=(1+v*2)*2^t ->
  ((a mod 2=1%nat /\ n mod 2=1%nat /\ n<=a*2+1) \/
   (a mod 2=0%nat /\ n mod 2=0%nat /\ n<=a*3-2)) -> Budget (a+1+t) v.
Proof.
  intros -> [[A [N B]]|[A [N B]]].
  - destruct t; cbn[Nat.pow] in *; unfold Budget; nia.
  - destruct t as [|[|t]]; cbn[Nat.pow] in *; unfold Budget; nia.
Qed.

Lemma normal_return e n x a: Normal e n x -> 0<n ->
  (forall t v, n=(1+v*2)*2^t -> Budget (a+1+t) v) ->
  exists y b c, Return x (a+1) y b c /\ Safe y b c.
Proof.
  intros N P B; destruct (normal_view N P) as [e' v u t Nv|t|t].
  - exists (1+u*2),(a+1+t),0%nat; split.
    + applys_eq (Return_odd t (a+1) (H_even u)); flia.
    + eapply Safe_main; [eassumption|apply B; reflexivity].
  - exists 1%nat,1%nat,(a+1+t); split; [constructor|constructor; lia].
  - exists 4%nat,(a+1+t),0%nat; split.
    + applys_eq (Return_odd t (a+1) (H_four (H_even 0))); flia.
    + constructor; auto; lia.
Qed.

Lemma normal_return_strong e n x a: Normal e n x -> 0<n -> n<=a+1 ->
  exists y b c, Return x (a+1) y b c /\ Safe y b c.
Proof.
  intros N P B; apply (normal_return a N P); intros t v E.
  apply budget_strong; nia.
Qed.

Lemma reset_closed a b: 0<a -> 0<b -> exists y a' b',
  Round 1 a b y a' b' /\ Safe y a' b'.
Proof.
  intros A B; destruct (normal_steps (a-1) (Normal_one Normal_D)) as [u [N I]].
  destruct (@normal_return_strong false (1+(a-1)) u (a+b) N ltac:(lia) ltac:(lia))
    as [y [a' [b' [J S]]]].
  exists y,a',b'; split; [exists u; split; assumption|assumption].
Qed.

Lemma normal_raw_return e n x a: Normal e n x -> n=a+3 -> 0<a ->
  exists y b c, Return x (a+1) y b c /\ Safe y b c.
Proof.
  intros N E A; destruct (normal_view N ltac:(lia)) as [e' v u t Nv|t|t].
  - exists (1+u*2),(a+1+t),0%nat; split.
    + applys_eq (Return_odd t (a+1) (H_even u)); flia.
    + destruct t; cbn[Nat.pow] in E.
      * applys_eq (Safe_weak Nv ltac:(lia)); flia.
      * eapply Safe_main; [exact Nv|apply budget_strong; nia].
  - exists 1%nat,1%nat,(a+1+t); split; [constructor|constructor; lia].
  - exists 4%nat,(a+1+t),0%nat; split.
    + applys_eq (Return_odd t (a+1) (H_four (H_even 0))); flia.
    + constructor; auto; lia.
Qed.

Lemma raw_closed x a: (x=4 \/ x=8 \/ x=16) -> 0<a -> exists y a' b',
  Round x a 0 y a' b' /\ Safe y a' b'.
Proof.
  intros [-> | [-> | ->]] A.
  - destruct (normal_steps (a-1) (Normal_zero (Normal_one Normal_D))) as [u [N I]].
    destruct (@normal_return_strong false _ _ a N ltac:(lia) ltac:(lia))
      as [y [a' [b' [J S]]]].
    exists y,a',b'; split; [exists u; split; [exact I|applys_eq J; flia]|exact S].
  - destruct (normal_steps (a-1) (Normal_zero Normal_E2)) as [u [N I]].
    destruct (@normal_raw_return true _ _ a N ltac:(lia) A)
      as [y [a' [b' [J S]]]].
    exists y,a',b'; split; [exists u; split; [exact I|applys_eq J; flia]|exact S].
  - destruct (normal_steps (a-1) (Normal_zero (Normal_zero (Normal_one Normal_D))))
      as [u [N I]].
    destruct (@normal_raw_return false _ _ a N ltac:(lia) A)
      as [y [a' [b' [J S]]]].
    exists y,a',b'; split; [exists u; split; [exact I|applys_eq J; flia]|exact S].
Qed.

Lemma two22: Steps 2 22 64.
Proof.
  eapply Steps_next; [exact (H_even 11)|apply steps_one].
  applys_eq (H_carry 2 (H_four (H_even 0))); reflexivity.
Qed.

Lemma two6: Steps 2 6 16.
Proof.
  eapply Steps_next; [exact (H_even 3)|apply steps_one].
  applys_eq (H_carry 2 (H_even 0)); reflexivity.
Qed.

Lemma weak_count e v x: Normal e v x -> 0<v -> exists n y,
  Normal (negb e) n y /\ Steps (v*2-1) (x*2) y /\
  0<n /\ n<=v*4-1 /\ n mod 2=1%nat.
Proof.
  intros N V; destruct (normal_top N V) as [k [z [w [F [E T]]]]].
  pose proof (field_bound F) as Z.
  assert (N2: Normal false 2 4) by exact (Normal_zero (Normal_one Normal_D)).
  assert (N4: Normal false 4 16) by exact (Normal_zero N2).
  destruct T as [[-> ->] | [-> [-> | ->]]].
  - destruct (Nat.eq_dec z 0) as [->|P].
    + rewrite (field_unique F (field_zeros k 1)).
      destruct (@packed_zero_affine k 1 0 2 true 2 (v*2-1)
        (Steps_zero 2) Normal_E2 ltac:(lia)) as [y [N' J]].
      exists (v*2-1+2*2^k),y; repeat split; try assumption; cbn[negb]; lia.
    + destruct (@packed_positive_affine k z 1 x 4 0 8 true 2 (v*2-1)
        F ltac:(lia) (H_four (H_even 0)) (Steps_zero 8)
        (Normal_zero Normal_E2) ltac:(lia)) as [y [N' J]].
      exists (v*2-1+z*2+2*2^k),y; repeat split; try assumption; cbn[negb]; lia.
  - destruct (Nat.eq_dec z 0) as [->|P].
    + rewrite (field_unique F (field_zeros k 2)).
      destruct (@packed_zero_affine k 2 0 4 false 2 (v*2-1)
        (Steps_zero 4) N2 ltac:(lia)) as [y [N' J]].
      exists (v*2-1+2*2^k),y; repeat split; try assumption; cbn[negb]; lia.
    + destruct (@packed_positive_affine k z 2 x 3 2 16 false 0 (v*2-1)
        F ltac:(lia) (H_even 1) two6 N4 ltac:(lia)) as [y [N' J]].
      exists (v*2-1+z*2),y; repeat split; try assumption; cbn[negb]; try lia.
      applys_eq N'; flia.
  - destruct (Nat.eq_dec z 0) as [->|P].
    + rewrite (field_unique F (field_zeros k 3)).
      destruct (@packed_zero_affine k 3 2 16 false 2 (v*2-1)
        two6 N4 ltac:(lia)) as [y [N' J]].
      exists (v*2-1+2*2^k),y; repeat split; try assumption; cbn[negb]; lia.
    + destruct (@packed_positive_affine k z 3 x 8 0 16 false 2 (v*2-1)
        F ltac:(lia) (H_eight (H_even 0)) (Steps_zero 16) N4 ltac:(lia))
        as [y [N' J]].
      exists (v*2-1+z*2+2*2^k),y; repeat split; try assumption; cbn[negb]; lia.
Qed.

Lemma weak_closed e v x: Normal e v x -> 0<v -> exists y a' b',
  Round (1+x*2) (v*2-1) 0 y a' b' /\ Safe y a' b'.
Proof.
  intros N V; destruct (weak_count N V) as [n [u [N' [I [P [B O]]]]]].
  destruct (@normal_return (negb e) n u (v*2-1) N' P) as [y [a' [b' [J S]]]].
  { intros t w E; apply (@budget_return (v*2-1) n t w E); left; repeat split; lia. }
  exists y,a',b'; split; [exists u; split|exact S].
  - apply (@steps_drop_even (v*2-1) x u); [lia|exact I].
  - applys_eq J; flia.
Qed.

Lemma normal_count_closed v x a e n u:
  Budget a v -> Normal e n u -> Steps a (x*2) u ->
  0<n -> n<=a+v*2 -> n mod 2=a mod 2 -> exists y a' b',
  Round (1+x*2) a 0 y a' b' /\ Safe y a' b'.
Proof.
  intros B N I P U O.
  destruct (@normal_return e n u a N P) as [y [a' [b' [J S]]]].
  { intros t w E; apply (@budget_return a n t w E).
    unfold Budget in B; destruct (mod2 a) as [q A|q A];
      [right|left]; repeat split; lia. }
  exists y,a',b'; split; [exists u; split|exact S].
  - apply (@steps_drop_even a x u); [unfold Budget in B; lia|exact I].
  - applys_eq J; flia.
Qed.

Lemma two14: Steps 2 14 32.
Proof.
  eapply Steps_next; [exact (H_even 7)|apply steps_one].
  applys_eq (H_carry 3 (H_even 0)); reflexivity.
Qed.

Lemma main_regular_count w k z x a:
  (w=1%nat \/ w=2 \/ w=3 \/ w=6 \/ w=7) -> Field k z w x -> Budget a (w*2^k+z) ->
  (w=1%nat -> 0<z -> 2*2^k<=a+z*2) ->
  (w=2 -> 0<z -> 4*2^k<=a+z*2) -> exists e n y,
  Normal e n y /\ Steps a (x*2) y /\
    a<=n /\ n<=a+(w*2^k+z)*2 /\ n mod 2=a mod 2.
Proof.
  intros W F B P1 P2; pose proof (field_bound F) as Z; unfold Budget in B.
  assert (N2: Normal false 2 4) by exact (Normal_zero (Normal_one Normal_D)).
  assert (N4: Normal false 4 16) by exact (Normal_zero N2).
  assert (E4: Normal true 4 8) by exact (Normal_zero Normal_E2).
  assert (E6: Normal true 6 12) by exact (Normal_zero Normal_E3).
  assert (E8: Normal true 8 32) by exact (Normal_zero E4).
  destruct (Nat.eq_dec z 0) as [->|P].
  - rewrite (field_unique F (field_zeros k w)).
    destruct W as [-> | [-> | [-> | [-> | ->]]]].
    + destruct (@packed_zero_affine k 1 0 2 true 2 a
        (Steps_zero 2) Normal_E2 ltac:(lia)) as [y [N J]].
      exists true,(a+2*2^k),y; repeat split; try assumption; lia.
    + destruct (@packed_zero_affine k 2 0 4 false 2 a
        (Steps_zero 4) N2 ltac:(lia)) as [y [N J]].
      exists false,(a+2*2^k),y; repeat split; try assumption; lia.
    + destruct (@packed_zero_affine k 3 2 16 false 2 a
        two6 N4 ltac:(lia)) as [y [N J]].
      exists false,(a+2*2^k),y; repeat split; try assumption; lia.
    + destruct (@packed_zero_affine k 6 0 12 true 6 a
        (Steps_zero 12) E6 ltac:(lia)) as [y [N J]].
      exists true,(a+6*2^k),y; repeat split; try assumption; lia.
    + destruct (@packed_zero_affine k 7 2 32 true 6 a
        two14 E8 ltac:(lia)) as [y [N J]].
      exists true,(a+6*2^k),y; repeat split; try assumption; lia.
  - destruct W as [-> | [-> | [-> | [-> | ->]]]].
    + destruct (@packed_positive_affine k z 1 x 4 0 8 true 2 a
        F ltac:(lia) (H_four (H_even 0)) (Steps_zero 8) E4 ltac:(apply P1; lia)) as [y [N J]].
      exists true,(a+z*2+2*2^k),y; repeat split; try assumption; lia.
    + destruct (@packed_positive_affine k z 2 x 3 2 16 false 0 a
        F ltac:(lia) (H_even 1) two6 N4 ltac:(apply P2; lia)) as [y [N J]].
      exists false,(a+z*2),y; repeat split; try assumption; try lia.
      applys_eq N; flia.
    + destruct (@packed_positive_affine k z 3 x 8 0 16 false 2 a
        F ltac:(lia) (H_eight (H_even 0)) (Steps_zero 16) N4 ltac:(lia)) as [y [N J]].
      exists false,(a+z*2+2*2^k),y; repeat split; try assumption; lia.
    + destruct (@packed_positive_affine k z 6 x 7 2 32 true 4 a
        F ltac:(lia) (H_even 3) two14 E8 ltac:(lia)) as [y [N J]].
      exists true,(a+z*2+4*2^k),y; repeat split; try assumption; lia.
    + assert (J7: H 7 16) by (applys_eq (H_carry 2 (H_even 0)); reflexivity).
      destruct (@packed_positive_affine k z 7 x 16 0 32 true 6 a
        F ltac:(lia) J7 (Steps_zero 32) E8 ltac:(lia)) as [y [N J]].
      exists true,(a+z*2+6*2^k),y; repeat split; try assumption; lia.
Qed.

Lemma main_regular_closed w k z x a:
  (w=1%nat \/ w=2 \/ w=3 \/ w=6 \/ w=7) -> Field k z w x -> Budget a (w*2^k+z) ->
  (w=1%nat -> 0<z -> 2*2^k<=a+z*2) ->
  (w=2 -> 0<z -> 4*2^k<=a+z*2) -> exists y a' b',
  Round (1+x*2) a 0 y a' b' /\ Safe y a' b'.
Proof.
  intros W F B P1 P2; destruct (main_regular_count W F B P1 P2)
    as [e [n [u [N [I [L [U O]]]]]]].
  eapply normal_count_closed; eauto; unfold Budget in B; lia.
Qed.

Lemma high_return w k z u a v: (w=6 \/ w=7) -> Field k z w u -> 0<z ->
  Budget a v -> w*2^k+z<=a+v*2 -> (w*2^k+z) mod 2=a mod 2 ->
  exists y b c, Return u (a+1) y b c /\ Safe y b c.
Proof.
  intros W F Z B U P.
  destruct (field_return (a+1) F Z) as [t [j [v' [y [F' [K [E J]]]]]]].
  exists (1+y*2),(a+1+t),0%nat; split; [exact J|].
  eapply Safe_high; [exact W|exact F'|].
  apply (@budget_return a (w*2^k+z) t (w*2^j+v')).
  - rewrite K, E, !Nat.pow_add_r; cbn[Nat.pow]; nia.
  - unfold Budget in B; destruct (mod2 a) as [q A|q A];
      [right|left]; repeat split; lia.
Qed.

Lemma main_short2 k z x a: Field k z 2 x -> 0<z -> Budget a (2*2^k+z) ->
  a+z*2<4*2^k -> exists y a' b', Round (1+x*2) a 0 y a' b' /\ Safe y a' b'.
Proof.
  intros F Z B P; destruct B as [B B']; pose proof (field_bound F).
  destruct (@packed_short 2 k z x a 3 F Z (H_even 1) ltac:(lia) P)
    as [q [r [u [Q [R [E [U I]]]]]]].
  assert (A: 0<a) by lia.
  assert (V: (6+q)*2^k+r=a+(2*2^k+z)*2) by nia.
  assert (W: 6+q=6 \/ 6+q=7) by lia.
  destruct (Nat.eq_dec r 0) as [->|R0].
  - assert (q=1%nat) by nia; subst q.
    rewrite (field_unique U (field_zeros k 7)) in I.
    exists 8%nat,(a+1+k),0%nat; split; [exists (7*4^k); split|constructor; auto; lia].
    + apply (@steps_drop_even a x); assumption.
    + applys_eq (Return_odd k (a+1) (H_eight (H_even 0))); flia.
  - destruct (@high_return (6+q) k r u a (2*2^k+z)
      W U ltac:(lia) ltac:(split; assumption) ltac:(lia) ltac:(rewrite V; lia))
      as [y [a' [b' [J S]]]].
    exists y,a',b'; split; [exists u; split|exact S].
    + apply (@steps_drop_even a x); assumption.
    + applys_eq J; flia.
Qed.

Lemma near_return w k z u a: (w=10 \/ w=11) -> Field k z w u -> 0<z ->
  z mod 2=0%nat -> 2*2^k<a -> exists y b c,
  Return u (a+1) y b c /\ Safe y b c.
Proof.
  intros W F Z P B.
  destruct (field_return (a+1) F Z) as [t [j [v [y [F' [K [E J]]]]]]].
  exists (1+y*2),(a+1+t),0%nat; split; [exact J|].
  eapply Safe_near; [exact W|exact F'|].
  destruct t; [cbn[Nat.pow] in E; lia|].
  rewrite K, !Nat.pow_add_r in B; cbn[Nat.pow] in B; nia.
Qed.

Lemma main_short1 k z x a: Field k z 1 x -> 0<z -> Budget a (2^k+z) ->
  a+z*2<2*2^k -> exists y a' b', Round (1+x*2) a 0 y a' b' /\ Safe y a' b'.
Proof.
  intros F Z [B B'] P; pose proof (field_bound F) as V.
  assert (A: a mod 2=0%nat) by (destruct (mod2 a); lia).
  destruct k as [|k]; [cbn[Nat.pow] in V; lia|].
  cbn[Nat.pow] in B, B', P, V.
  destruct (@field_exists k z 4 ltac:(lia)) as [x' F'].
  assert (x=x') as ->.
  { apply (field_unique F); applys_eq (field_compose (Field_zero (Field_nil 1)) F'); flia. }
  destruct (@packed_short 4 k z x' a 5 F' Z (H_even 2) ltac:(lia) ltac:(lia))
    as [q [r [u [Q [R [E [U I]]]]]]].
  assert (W: 10+q=10 \/ 10+q=11) by lia.
  destruct (Nat.eq_dec r 0) as [->|R0].
  - assert (q=1%nat) by nia; subst q.
    rewrite (field_unique U (field_zeros k 11)) in I.
    exists 16%nat,(a+1+k),0%nat; split; [exists (11*4^k); split|constructor; auto; lia].
    + apply (@steps_drop_even a x'); [lia|assumption].
    + applys_eq (Return_odd k (a+1) (H_four (H_four (H_even 0)))); flia.
  - assert (RP: r mod 2=0%nat).
    { destruct k; [cbn[Nat.pow] in R; lia|cbn[Nat.pow] in E; nia]. }
    destruct (@near_return (10+q) k r u a W U ltac:(lia) RP ltac:(lia))
      as [y [a' [b' [J S]]]].
    exists y,a',b'; split; [exists u; split|exact S].
    + apply (@steps_drop_even a x'); [lia|assumption].
    + applys_eq J; flia.
Qed.

Lemma near_count w k z x a: (w=10 \/ w=11) -> Field k z w x -> 8*2^k<=a ->
  exists n y, Normal false n y /\ Steps a (x*2) y /\
    a<=n /\ n<a+8*2^k /\ n mod 2=a mod 2.
Proof.
  intros W F B; pose proof (field_bound F) as Z.
  assert (N8: Normal false 8 64) by
    exact (Normal_zero (Normal_zero (Normal_zero (Normal_one Normal_D)))).
  assert (N6: Normal false 6 20) by
    exact (Normal_zero (Normal_one (Normal_one Normal_D))).
  destruct (Nat.eq_dec z 0) as [->|P].
  - rewrite (field_unique F (field_zeros k w)).
    destruct W as [-> | ->].
    + destruct (@packed_zero_affine k 10 0 20 false 6 a
        (Steps_zero 20) N6 ltac:(lia)) as [y [N J]].
      exists (a+6*2^k),y; repeat split; try assumption; lia.
    + destruct (@packed_zero_affine k 11 2 64 false 6 a
        two22 N8 ltac:(lia)) as [y [N J]].
      exists (a+6*2^k),y; repeat split; try assumption; lia.
  - destruct W as [-> | ->].
    + destruct (@packed_positive_affine k z 10 x 11 2 64 false 4 a
        F ltac:(lia) (H_even 5) two22 N8 ltac:(lia)) as [y [N J]].
      exists (a+z*2+4*2^k),y; repeat split; try assumption; lia.
    + assert (J11: H 11 32) by (applys_eq (H_eight (H_four (H_even 0))); reflexivity).
      destruct (@packed_positive_affine k z 11 x 32 0 64 false 6 a
        F ltac:(lia) J11 (Steps_zero 64) N8 ltac:(lia)) as [y [N J]].
      exists (a+z*2+6*2^k),y; repeat split; try assumption; lia.
Qed.

Lemma near_closed w k z x a: (w=10 \/ w=11) -> Field k z w x -> 8*2^k<=a ->
  exists y a' b', Round (1+x*2) a 0 y a' b' /\ Safe y a' b'.
Proof.
  intros W F B; destruct (near_count W F B) as [n [u [N [I [L [U P]]]]]].
  destruct (@normal_return false n u a N ltac:(lia)) as [y [a' [b' [J S]]]].
  { intros t v E; apply (@budget_return a n t v E).
    destruct (mod2 a) as [q A|q A]; [right|left]; repeat split; lia. }
  exists y,a',b'; split; [exists u; split|exact S].
  - apply (@steps_drop_even a x u); [lia|exact I].
  - applys_eq J; flia.
Qed.

Lemma main_closed w k z x a:
  (w=1%nat \/ w=2 \/ w=3 \/ w=6 \/ w=7) -> Field k z w x -> Budget a (w*2^k+z) ->
  exists y a' b', Round (1+x*2) a 0 y a' b' /\ Safe y a' b'.
Proof.
  intros W F B; destruct (Nat.eq_dec z 0) as [->|Z].
  - eapply main_regular_closed; eauto; intros; lia.
  - destruct (Nat.eq_dec w 1) as [->|W1].
    + destruct (le_dec (2*2^k) (a+z*2)).
      * eapply main_regular_closed; eauto; intros; lia.
      * eapply main_short1; eauto; unfold Budget in *; lia.
    + destruct (Nat.eq_dec w 2) as [->|W2].
      * destruct (le_dec (4*2^k) (a+z*2)).
        -- eapply main_regular_closed; eauto; intros; lia.
        -- eapply main_short2; eauto; lia.
      * eapply main_regular_closed; eauto; intros; lia.
Qed.

Lemma closed x a b: Safe x a b -> exists y a' b',
  Round x a b y a' b' /\ Safe y a' b'.
Proof.
  intro S; destruct S.
  - destruct (Nat.eq_dec v 0) as [->|V].
    + destruct (normal_zero_value H0) as [-> ->].
      destruct (normal_steps a Normal_D) as [u [N I]].
      eapply (@normal_count_closed 0 0 a false a u); eauto;
        unfold Budget in *; lia.
    + destruct (normal_top H0 ltac:(lia)) as [k [z [w [F [E W]]]]].
      apply (@main_closed w k z x a); [destruct W as [[_ ->]|[_ [-> | ->]]]; auto|exact F|].
      rewrite <-E; assumption.
  - eapply main_closed; eauto.
  - apply raw_closed; assumption.
  - eapply weak_closed; eauto.
  - eapply near_closed; eauto.
  - apply reset_closed; assumption.
Qed.

Inductive Num : nat -> side -> Prop :=
| Num_nil: Num 0 0inf
| Num_zero n l: Num n l -> Num (n*2) (l <* <[0])
| Num_one n l: Num n l -> Num (1+n*2) (l <* <[1]).

Lemma Num_even n l: Num (n*2) l -> exists s, l=s <* <[0] /\ Num n s.
Proof.
  intro I; inversion I; subst.
  - exists 0inf; split; [st; reflexivity|applys_eq Num_nil; flia].
  - eexists; split; [reflexivity|applys_eq H1; flia].
  - lia.
Qed.
Lemma Num_odd n l: Num (1+n*2) l -> exists s, l=s <* <[1] /\ Num n s.
Proof.
  intro I; inversion I; subst; try lia.
  eexists; split; [reflexivity|applys_eq H1; flia].
Qed.
Lemma Num_zeros k n l: Num n l -> Num (n*2^k) (l <* <[0]^^k).
Proof.
  intro I; induction k; [cbn[Nat.pow lpow]; applys_eq I; flia|].
  applys_eq (Num_zero IHk); st; cbn[Nat.pow]; flia.
Qed.
Lemma Num_zero_inv l: Num 0 l -> l=0inf.
Proof.
  intro I; remember 0%nat as n; induction I; try lia.
  - reflexivity.
  - assert (n=0%nat) by lia; subst; rewrite IHI by reflexivity; st; reflexivity.
Qed.
Lemma Num_unique n l s: Num n l -> Num n s -> l=s.
Proof.
  intro I; gen s; induction I; intros s J.
  - symmetry; apply Num_zero_inv, J.
  - destruct (Num_even _ J) as [s' [-> N]]; rewrite (IHI _ N); reflexivity.
  - destruct (Num_odd _ J) as [s' [-> N]]; rewrite (IHI _ N); reflexivity.
Qed.
Lemma Num_pairs k n l: Num (n*4^k) l -> exists s,
  Num n s /\ l=s <* <[0;0]^^k.
Proof.
  gen l; induction k; intros l N.
  - exists l; split; [applys_eq N; cbn[Nat.pow]; flia|reflexivity].
  - destruct (Num_even (n*4^k*2) (l:=l)) as [u [-> U]];
      [applys_eq N; cbn[Nat.pow]; flia|].
    destruct (Num_even _ U) as [v [-> V]].
    destruct (IHk _ V) as [s [Ns ->]].
    exists s; split; [assumption|st; reflexivity].
Qed.
Lemma Num_run j n l: Num (n*2^(1+j)+(2^j-1)) l ->
  exists s, l=s <* <[0] <* <[1]^^j /\ Num n s.
Proof.
  gen n l; induction j; intros n l I.
  - cbn[Nat.pow Nat.add] in I |- *; apply Num_even; applys_eq I; flia.
  - assert (J: Num (1+(n*2^(1+j)+(2^j-1))*2) l).
    { applys_eq I; cbn[Nat.pow Nat.add]; flia. }
    destruct (Num_odd _ J) as [l' [-> N]].
    destruct (IHj _ _ N) as [s [-> Ns]].
    exists s; split; [st; reflexivity|assumption].
Qed.

Section Machine.
Context (tm:TM) (q h g:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l |> r" := (l {{q}}> r) (at level 30).
Notation "l <| r" := (l <{{h}} r) (at level 30).
Notation "l <@ r" := (l <{{g}} r) (at level 30).

Record Rules : Prop := {
  left_zero: forall l r, l <* <[0] <| r -->* l <* <[1] |> r;
  left_carry: forall l r j,
    l <* <[0] <* <[1]^^(1+j) <| r -->* l <| [1]^^(2+j) *> r;
  scan_right: forall l r j, l |> [1]^^j *> r -->* l <* <[0]^^j |> r;
  right_inc: forall l r n,
    l |> [1] *> [1;0]^^(2+n) *> [0] *> r -->*
    l <| [1] *> [1;0]^^(1+n) *> [0;1;0] *> r;
  right_overflow: forall l r, l |> [1;1;0;0] *> r -->+ l <@ [1;0;1;0] *> r;
  scan_overflow: forall l r j, l <* <[0;0]^^j <@ r -->* l <@ [1;0]^^j *> r;
  overflow_one: forall l r, l <* <[1] <@ r -->* l <| [1] *> r;
  overflow_two: forall l r, l <* <[0;1;0] <@ r -->* l <| [0;0;0] *> r;
  overflow_resume: forall l r, l |> [0;0;0] *> r -->* l <@ [1;0;0] *> r
}.
Context (rules:Rules).

Lemma H_spec x y: H x y -> forall l, Num x l -> exists l',
  Num y l' /\ forall r, l <| r -->* l' |> r.
Proof.
  intro I; induction I as [n|j x y I IH]; intros l N.
  - destruct (Num_even _ N) as [s [-> Ns]].
    exists (s <* <[1]); split; [constructor; assumption|apply (left_zero rules)].
  - destruct (Num_run (1+j) x N) as [s [-> Ns]].
    destruct (IH _ Ns) as [s' [Ny J]].
    exists (s' <* <[0]^^(2+j)); split; [apply Num_zeros; assumption|intro r].
    follow (left_carry rules s r j).
    follow (J ([1]^^(2+j) *> r)).
    follow (scan_right rules s' r (2+j)); finish.
Qed.

Definition right a b := [1] *> [1;0]^^a *> [0] *> [1;0]^^b *> 0inf.

Lemma count_spec n x y: Steps n x y -> forall l, Num x l -> exists l',
  Num y l' /\ forall a b, l |> right (1+n+a) b -->*
    l' |> right (1+a) (n+b).
Proof.
  intro I; induction I as [x|n x y z J I IH]; intros l N.
  - exists l; split; [assumption|intros; finish].
  - destruct (H_spec J N) as [l' [N' K]].
    destruct (IH _ N') as [l'' [N'' M]].
    exists l''; split; [assumption|intros a b].
    unfold right; follow (right_inc rules l ([1;0]^^b *> 0inf) (n+a)).
    follow (K ([1] *> [1;0]^^(1+n+a) *> [0] *> [1;0]^^(1+b) *> 0inf)).
    follow (M a (1+b)); unfold right; finish; flia.
Qed.

Lemma overflow_spec n x y: Steps n x y -> forall l, Num x l -> exists l',
  Num y l' /\ forall b, l |> right (1+n) b -->+
    l' <@ [1;0]^^(2+n+b) *> 0inf.
Proof.
  intros I l N; destruct (count_spec I N) as [l' [N' K]].
  exists l'; split; [assumption|intro b].
  follow (K 0%nat b); unfold right.
  follow10 (right_overflow rules l' ([1;0]^^(n+b) *> 0inf)); finish.
Qed.

Lemma return_odd t x y: H x y -> forall l, Num ((1+x*2)*4^t) l ->
  exists l', Num y l' /\ forall a,
  l <@ [1;0]^^a *> 0inf -->* l' |> right (a+t) 0.
Proof.
  intros I l N; destruct (Num_pairs t (1+x*2) N) as [s [Ns ->]].
  destruct (Num_odd _ Ns) as [s' [-> N']].
  destruct (H_spec I N') as [s'' [N'' K]].
  exists s''; split; [assumption|intro a].
  follow (scan_overflow rules (s' <* <[1]) ([1;0]^^a *> 0inf) t).
  follow (overflow_one rules s' ([1;0]^^t *> [1;0]^^a *> 0inf)).
  follow (K ([1] *> [1;0]^^t *> [1;0]^^a *> 0inf)).
  unfold right; rewrite (Nat.add_comm a t); finish; st; reflexivity.
Qed.

Lemma return_power t a l: Num (2*4^t) l ->
  l <@ [1;0]^^a *> 0inf -->* 0inf <* <[1] |> right 1 (a+t).
Proof.
  intro N; destruct (Num_pairs t 2 N) as [s [Ns ->]].
  assert (s=0inf <* <[1;0]) as ->.
  { apply (Num_unique Ns (Num_zero (Num_one Num_nil))). }
  follow (scan_overflow rules (0inf <* <[1;0]) ([1;0]^^a *> 0inf) t).
  eapply evstep_trans; [applys_eq (overflow_two rules 0inf
    ([1;0]^^t *> [1;0]^^a *> 0inf)); st; reflexivity|].
  eapply evstep_trans; [applys_eq (left_zero rules 0inf
    ([0;0;0] *> [1;0]^^t *> [1;0]^^a *> 0inf)); st; reflexivity|].
  follow (overflow_resume rules (0inf <* <[1]) ([1;0]^^t *> [1;0]^^a *> 0inf)).
  follow (overflow_one rules 0inf ([1;0;0] *> [1;0]^^t *> [1;0]^^a *> 0inf)).
  eapply evstep_trans; [applys_eq (left_zero rules 0inf
    ([1;1;0;0] *> [1;0]^^t *> [1;0]^^a *> 0inf)); st; reflexivity|].
  unfold right; rewrite (Nat.add_comm a t); finish; st; reflexivity.
Qed.

Lemma Return_spec x a y b c: Return x a y b c -> forall l, Num x l ->
  exists l', Num y l' /\ l <@ [1;0]^^a *> 0inf -->* l' |> right b c.
Proof.
  intro I; destruct I; intros l N.
  - destruct (return_odd t H0 N) as [l' [N' K]]; exists l'; auto.
  - exists (0inf <* <[1]); split; [exact (Num_one Num_nil)|].
    apply return_power, N.
Qed.

Lemma Round_spec x a b y a' b': Round x a b y a' b' -> 0<a ->
  forall l, Num x l -> exists l', Num y l' /\
  l |> right a b -->+ l' |> right a' b'.
Proof.
  intros [u [I J]] A l N; destruct (overflow_spec I N) as [s [Ns K]].
  destruct (Return_spec J Ns) as [l' [N' M]].
  exists l'; split; [assumption|].
  eapply progress_evstep_trans; [applys_eq (K b); flia|applys_eq M; flia].
Qed.

Lemma nonhalt_from x a b l: Safe x a b -> Num x l -> ~halts tm (l |> right a b).
Proof.
  intros S N; eapply progress_nonhalt_cond with (i0:=(l,a,b))
    (C:=fun '(l,a,b) => l |> right a b)
    (P:=fun '(l,a,b) => exists x, Num x l /\ Safe x a b).
  - intros [[l0 a0] b0] [x0 [N0 S0]].
    destruct (closed S0) as [y [a' [b' [J S']]]].
    destruct (Round_spec J (safe_positive S0) N0) as [l' [N' K]].
    exists (l',a',b'); split; [exact K|exists y; auto].
  - exists x; auto.
Qed.

End Machine.
End PairCounter.

Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC1LA_0RD0RC_0LE1LB_1LD0LF_0LB---").
Lemma rules: PairCounter.Rules tm C B D.
Proof. constructor; intros; es. Qed.
Lemma init: c0 -[tm]->* 0inf <* <[1] {{C}}> PairCounter.right 1 1.
Proof. unfold PairCounter.right; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (PairCounter.nonhalt_from rules (x:=1%nat)).
  - constructor; lia.
  - exact (PairCounter.Num_one PairCounter.Num_nil).
Qed.
End TM11.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LF").
Lemma rules: PairCounter.Rules tm B A C.
Proof. constructor; intros; es. Qed.
Lemma init: c0 -[tm]->* 0inf <* <[1] {{B}}> PairCounter.right 1 0.
Proof. unfold PairCounter.right; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (PairCounter.nonhalt_from rules (x:=1%nat)).
  - apply (@PairCounter.Safe_main false 0 0 1 PairCounter.Normal_D).
    unfold PairCounter.Budget; lia.
  - exact (PairCounter.Num_one PairCounter.Num_nil).
Qed.
End TM12.

(* BEC.txt TM15.  The four returning branches are derived from local rules;
   the exceptional branch includes a bounded, overlapped binary counter. *)
Set Implicit Arguments.

Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LE_1RF1LD_1RE0LD_0LB0RA_---0RC").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation Z := [0;0].
Notation U := [0;1].
Notation V := [1;0].
Notation O := [1;1].
Notation h := [((A,[]),(D,[]))].

Inductive Num : nat -> side -> Prop :=
| Num_nil: Num 0 0inf
| Num_zero n r: Num n r -> Num (n*2) (Z *> r)
| Num_one n r: Num n r -> Num (1+n*2) (O *> r).

Lemma Num_even n r: Num (n*2) r -> exists s, r=Z *> s /\ Num n s.
Proof.
  intro H; inversion H; subst.
  - exists 0inf; split; [st; reflexivity|applys_eq Num_nil; flia].
  - eexists; split; [reflexivity|applys_eq H1; flia].
  - lia.
Qed.
Lemma Num_odd n r: Num (1+n*2) r -> exists s, r=O *> s /\ Num n s.
Proof.
  intro H; inversion H; subst; try lia.
  eexists; split; [reflexivity|applys_eq H1; flia].
Qed.

Lemma carry: segRLs tm h h O Z.
Proof.
  eapply segRLs_RR_LLs with (w3:=O); [solve_seg|].
  eapply segLLs_LL_RLs with (w3:=Z); [solve_seg|constructor].
Qed.

Lemma increment n r: Num n r -> exists s, Num (1+n) s /\ sideRLs tm h r s.
Proof.
  intro H; induction H as [|n r N IH|n r N [s [Ns Hs]]].
  - exists (O *> 0inf); split; [exact (Num_one Num_nil)|esx].
  - exists (O *> r); split; [constructor; assumption|esx].
  - exists (Z *> s); split.
    + applys_eq (Num_zero Ns); flia.
    + eapply segRLs_sideRLs_concat; [apply carry|exact Hs].
Qed.

(* Two ordinary right calls, including the intervening left return. *)
Lemma pair n r: Num (1+n*2) r -> exists s, Num (1+n) s /\ forall l q,
  l <* <[1;0]^^(1+q) {{A}}> r -->+
  l <{{E}} V^^(1+q) *> O *> s.
Proof.
  intro N; destruct (increment N) as [r' [N' H]].
  destruct (Num_even (1+n) (r:=r')) as [s [-> Ns]]; [applys_eq N'; flia|].
  exists s; split; [assumption|intros l q].
  follow10 (sideRLs_1 _ _ _ _ _ H (l <* <[1;0]^^(1+q))).
  cbn[to_DH_config]; es' q & l s.
Qed.

Definition S0 (l:side) a q (r:side) := l <* <[0;1]^^a <* <[1;0]^^q {{A}}> r.
Definition S1 (l:side) a q (r:side) := l <* <[0;1]^^a <* <[0;0] <* <[1;0]^^q {{A}}> r.

Lemma scanV q l r:
  l {{A}}> V^^q *> 1 >> r -->* l <* <[1;0]^^q {{A}}> 1 >> r.
Proof.
  gen l; induction q; intro l; [finish|].
  destruct q; cbn[lpow]; do 4 step1;
    applys_eq (IHq (l <* <[1;0])); st; simpl_rotate; reflexivity.
Qed.

Lemma resume0 a q l r:
  l <* <[0;1]^^(1+a) <{{E}} V^^q *> 1 >> r -->*
  l <* <[0;1]^^a <* <[0;0] <* <[1;0]^^q {{A}}> 1 >> r.
Proof. cbn[lpow]; step1; apply scanV. Qed.

Lemma resume1 a q l r:
  l <* <[0;1]^^(1+a) <* <[0;0] <{{E}} V^^q *> 1 >> r -->*
  l <* <[0;1]^^a <* <[1;0]^^(2+q) {{A}}> 1 >> r.
Proof.
  cbn[lpow]; do 5 step1.
  applys_eq (scanV (1+q) (l <* <[0;1]^^a <* <[1;0]) r); st; simpl_rotate; reflexivity.
Qed.

Lemma count0 l a q n r: Num (1+n*2) r -> exists s,
  Num (3+n*2) s /\ S0 l (1+a) (1+q) r -->+ S1 l a (1+q) s.
Proof.
  intro N; destruct (pair n N) as [s [Ns H]].
  exists (O *> s); split; [applys_eq (Num_one Ns); flia|].
  unfold S0,S1; follow10 H; apply resume0.
Qed.

Lemma count1 l a q n r: Num (1+n*2) r -> exists s,
  Num (3+n*2) s /\ S1 l (1+a) (1+q) r -->+ S0 l a (3+q) s.
Proof.
  intro N; destruct (pair n N) as [s [Ns H]].
  exists (O *> s); split; [applys_eq (Num_one Ns); flia|].
  unfold S0,S1; follow10 H; applys_eq (resume1 a (1+q) l (1>>s)); flia.
Qed.

Lemma counts l a a0 q n r: Num (1+n*2) r -> exists s,
  Num (1+n*2+a*4) s /\ S0 l (a*2+a0) (1+q) r -->* S0 l a0 (1+q+a*2) s.
Proof.
  gen q n r; induction a; intros q n r N.
  - exists r; split; [applys_eq N; flia|unfold S0; finish].
  - destruct (count0 l (1+a*2+a0) q n N) as [r1 [N1 H1]].
    destruct (@count1 l (a*2+a0) q (1+n) r1) as [r2 [N2 H2]];
      [applys_eq N1; flia|].
    destruct (IHa (2+q) (2+n) r2) as [s [Ns Hs]]; [applys_eq N2; flia|].
    exists s; split; [applys_eq Ns; flia|].
    eapply evstep_trans; [apply progress_evstep; applys_eq H1; flia|].
    eapply evstep_trans; [apply progress_evstep; exact H2|applys_eq Hs; flia].
Qed.

Definition K b r := S0 0inf 0 b r.

Lemma overflow b n r: Num (1+n*2) r -> exists s, Num (1+n) s /\
  K (1+b) r -->+ S0 0inf (3+b) 1 s.
Proof.
  intro N; destruct (pair n N) as [s [Ns H]].
  exists s; split; [assumption|].
  unfold K,S0; follow10 (H 0inf b); es' b & s.
Qed.

Lemma counts_end a q n r: Num (1+n*2) r -> exists b s,
  Num (1+n*2+a*2) s /\ a+q<=b /\ 1<=b /\ S0 0inf a (1+q) r -->* K b s.
Proof.
  intro N; destruct (mod2 a) as [k ->|k ->].
  - destruct (counts 0inf k 0 q n N) as [s [Ns Hs]].
    exists (1+q+k*2),s; repeat split; try lia.
    + applys_eq Ns; flia.
    + unfold K; applys_eq Hs; flia.
  - destruct (counts 0inf k 1 q n N) as [s [Ns Hs]].
    destruct (@count0 0inf 0 (q+k*2) (n+k*2) s) as [t [Nt Ht]];
      [applys_eq Ns; flia|].
    exists (1+q+k*2),t; repeat split; try lia.
    + applys_eq Nt; flia.
    + eapply evstep_trans; [applys_eq Hs; flia|].
      eapply evstep_trans; [apply progress_evstep; exact Ht|].
      unfold K,S0,S1; finish; st; flia.
Qed.

Inductive Bits : nat -> nat -> list Sym -> Prop :=
| Bits_nil: Bits 0 0 []
| Bits_zero j n w: Bits j n w -> Bits (1+j) (n*2) (Z++w)
| Bits_one j n w: Bits j n w -> Bits (1+j) (1+n*2) (O++w).

Lemma finite_increment j n w: Bits j n w -> 1+n<2^j -> exists w',
  Bits j (1+n) w' /\ segRLs tm h [] (1::w) (0::w').
Proof.
  intro H; induction H; intro B.
  - cbn in B; lia.
  - exists (O++w); split; [constructor; assumption|].
    change (segRLs tm h [] ([1;0;0]++w) ([0;1;1]++w)).
    eapply segRLs_concat; [esx|constructor].
  - destruct IHBits as [w' [N I]]; [cbn[Nat.add Nat.pow] in B; lia|].
    exists (Z++w'); split; [applys_eq (Bits_zero N); flia|].
    change (segRLs tm h [] (O++1::w) (Z++0::w')).
    eapply segRLs_concat; [apply carry|exact I].
Qed.

Lemma wrap d l r:
  l <* <[0;1]^^(2+d) <{{D}} 0 >> r -->*
  l <{{B}} U^^(2+d) *> 1 >> r.
Proof. es' d & l r. Qed.

Lemma internal_inc j n w: Bits j n w -> 1+n<2^j -> exists w',
  Bits j (1+n) w' /\ forall l d r,
  l <* <[0;1]^^(2+d) {{A}}> 1 >> w *> 0 >> r -->+
  l <{{B}} U^^(2+d) *> 1 >> w' *> 0 >> r.
Proof.
  intros N B; destruct (finite_increment N B) as [w' [N' H]].
  exists w'; split; [assumption|intros l d r].
  assert (Hr: sideRLs tm h ((1::w) *> 0 >> r) ((0::w') *> 0 >> r)) by
    (eapply segRLs_sideRLs_concat; [exact H|constructor]).
  follow10 (sideRLs_1 _ _ _ _ _ Hr (l <* <[0;1]^^(2+d))).
  apply wrap.
Qed.

Lemma resumeB2 d l r:
  l <* <[1;0]^^2 <{{B}} U^^d *> r -->*
  l <* <[1;1] <* <[0;1]^^(1+d) {{A}}> r.
Proof. es' d & l r. Qed.

Lemma resumeBO d l r:
  l <* <[1;1] <{{B}} U^^d *> r -->*
  l <* <[0;1]^^(1+d) {{A}}> r.
Proof. es' d & l r. Qed.

Definition Internal (l:side) c d w (r:side) :=
  l <* <[1;0]^^c <* <[0;1]^^d {{A}}> 1 >> w *> 0 >> r.

Lemma internal_pair j n w: Bits j n w -> 2+n<2^j -> exists w',
  Bits j (2+n) w' /\ forall l c d r,
  Internal l (2+c) (2+d) w r -->+ Internal l c (4+d) w' r.
Proof.
  intros N B; destruct (internal_inc N) as [w1 [N1 H1]]; [lia|].
  destruct (internal_inc N1) as [w2 [N2 H2]]; [lia|].
  exists w2; split; [applys_eq N2; flia|intros l c d r].
  unfold Internal.
  follow10 H1.
  follow (resumeB2 (2+d) (l <* <[1;0]^^c) (1 >> w1 *> 0 >> r)).
  follow100 (H2 (l <* <[1;0]^^c <* <[1;1]) (1+d) r).
  follow (resumeBO (3+d) (l <* <[1;0]^^c) (1 >> w2 *> 0 >> r)).
  finish.
Qed.

Lemma internal_pairs k j n w: Bits j n w -> n+k*2<2^j -> exists w',
  Bits j (n+k*2) w' /\ forall l c d r,
  Internal l (k*2+c) (2+d) w r -->* Internal l c (2+d+k*2) w' r.
Proof.
  gen n w; induction k; intros n w N B.
  - exists w; split; [applys_eq N; flia|intros; unfold Internal; finish].
  - destruct (internal_pair N) as [w1 [N1 H1]]; [cbn[Nat.mul] in B; lia|].
    destruct (IHk _ _ N1) as [w2 [N2 H2]]; [cbn[Nat.mul] in B; lia|].
    exists w2; split; [applys_eq N2; cbn[Nat.mul]; flia|intros l c d r].
    eapply evstep_trans; [apply progress_evstep; applys_eq (H1 l (k*2+c) d r); flia|].
    applys_eq (H2 l c (2+d) r); cbn[Nat.mul]; flia.
Qed.

Lemma Bits_zeros j: Bits j 0 (Z^^j).
Proof. induction j; [constructor|applys_eq (Bits_zero IHj); flia]. Qed.

Lemma Bits_ones j w: Bits j (2^j-1) w -> w=O^^j.
Proof.
  remember (2^j-1) as n; intro H; induction H; [reflexivity| |].
  - cbn[Nat.add Nat.pow] in Heqn; pose proof (Nat.pow_nonzero 2 j); lia.
  - cbn[Nat.add Nat.pow] in Heqn; rewrite IHBits; [reflexivity|].
    pose proof (Nat.pow_nonzero 2 j); lia.
Qed.

Lemma enter b j r:
  K (1+b) (O *> O *> Z *> O^^(1+j) *> Z *> r) -->+
  0inf <{{B}} U^^(5+b) *> O *> V *> Z^^j *> O *> r.
Proof. unfold K,S0; es' b j & r. Qed.

Lemma start_internal b j r:
  0inf <{{B}} U^^(5+b) *> O *> V *> Z^^(1+j) *> O *> r -->*
  Internal 0inf (5+b) 2 (O++Z^^j) (O *> r).
Proof.
  mid (0inf <* <[1;0]^^(5+b) <* <[0;1]^^2 {{A}}> O *> V *> Z^^j *> O *> r).
  - es' b j & r.
  - unfold Internal; finish; st; simpl_rotate; reflexivity.
Qed.

Lemma clear_one n r: Num (1+n*2) r -> exists s,
  Num (3+n*2) s /\ forall l q,
  l <* <[1;1] <* <[1;0]^^(1+q) {{A}}> r -->+
  l <* <[1;0]^^(2+q) {{A}}> s.
Proof.
  intro N; destruct (pair n N) as [s [Ns H]].
  exists (O *> s); split; [applys_eq (Num_one Ns); flia|intros l q].
  follow10 H; step1.
  applys_eq (scanV (1+q) (l <* <[1;0]) (1>>s)); st; simpl_rotate; reflexivity.
Qed.

Lemma clear_ones j n r: Num (1+n*2) r -> exists s,
  Num (1+n*2+j*2) s /\ forall l q,
  l <* <[1;1]^^j <* <[1;0]^^(1+q) {{A}}> r -->*
  l <* <[1;0]^^(1+q+j) {{A}}> s.
Proof.
  gen n r; induction j; intros n r N.
  - exists r; split; [applys_eq N; flia|intros; finish].
  - destruct (clear_one n N) as [r1 [N1 H1]].
    destruct (IHj (1+n) r1) as [s [Ns Hs]]; [applys_eq N1; flia|].
    exists s; split; [applys_eq Ns; flia|intros l q].
    eapply evstep_trans.
    + apply progress_evstep; applys_eq (H1 (l <* <[1;1]^^j) q); st; simpl_rotate; reflexivity.
    + applys_eq (Hs l (1+q)); flia.
Qed.

Definition Safe b r := 1<=b /\ exists n, Num (1+n*2) r /\ n<=b*2.
Definition Returns b r := exists b' r', Safe b' r' /\ K b r -->+ K b' r'.

Lemma branch1 b m r: Num (1+m*4) r -> m<=1+b -> Returns (1+b) r.
Proof.
  intros N B; destruct (@overflow b (m*2) r) as [s [Ns Hs]]; [applys_eq N; flia|].
  destruct (counts_end (3+b) 0 m Ns) as [b' [t [Nt [B1 [B2 Ht]]]]].
  exists b',t; split.
  - split; [assumption|exists (m+3+b); split; [applys_eq Nt; flia|lia]].
  - follow10 Hs; exact Ht.
Qed.

Lemma bridge2 l a r: S0 l a 1 (Z *> Z *> r) -->* S0 l a 2 (O *> r).
Proof. unfold S0; es' a & l r. Qed.
Lemma bridge3 l a r: S0 l a 1 (Z *> O *> Z *> r) -->* S0 l (2+a) 1 (O *> r).
Proof. unfold S0; es' a & l r. Qed.

Lemma branch2 b m r: Num (7+m*8) r -> m<=1+b -> Returns (1+b) r.
Proof.
  intros N B; destruct (@overflow b (3+m*4) r) as [s [Ns Hs]]; [applys_eq N; flia|].
  destruct (Num_even (2+m*2) (r:=s)) as [s1 [-> N1]]; [applys_eq Ns; flia|].
  destruct (Num_even (1+m) N1) as [s2 [-> N2]].
  destruct (counts_end (3+b) 1 (1+m) (Num_one N2)) as [b' [t [Nt [B1 [B2 Ht]]]]].
  exists b',t; split.
  - split; [assumption|exists (m+4+b); split; [applys_eq Nt; flia|lia]].
  - follow10 Hs; follow bridge2; exact Ht.
Qed.

Lemma branch3 b m r: Num (3+m*16) r -> m<=1+b -> Returns (1+b) r.
Proof.
  intros N B; destruct (@overflow b (1+m*8) r) as [s [Ns Hs]]; [applys_eq N; flia|].
  destruct (Num_even (1+m*4) (r:=s)) as [s1 [-> N1]]; [applys_eq Ns; flia|].
  destruct (Num_odd (m*2) (r:=s1)) as [s2 [-> N2]]; [applys_eq N1; flia|].
  destruct (Num_even m N2) as [s3 [-> N3]].
  destruct (counts_end (5+b) 0 m (Num_one N3)) as [b' [t [Nt [B1 [B2 Ht]]]]].
  exists b',t; split.
  - split; [assumption|exists (m+5+b); split; [applys_eq Nt; flia|lia]].
  - follow10 Hs; follow bridge3; exact Ht.
Qed.

Lemma zeros_after_one j r: 1 >> O^^j *> 0 >> r = O^^j *> V *> r.
Proof. st; simpl_rotate; reflexivity. Qed.

Lemma scanO j l r: l {{A}}> O^^j *> r -->* l <* <[1;1]^^j {{A}}> r.
Proof. es. Qed.

Lemma exit_internal j l r:
  l {{A}}> 1 >> O^^j *> 0 >> O *> r -->*
  l <* <[1;1]^^j <* <[1;0] {{A}}> O *> r.
Proof.
  rewrite zeros_after_one.
  mid (l <* <[1;1]^^j {{A}}> V *> O *> r).
  - apply scanO.
  - apply (scanV 1 (l <* <[1;1]^^j) (1>>r)).
Qed.

Lemma start_zero b r:
  0inf <{{B}} U^^(5+b) *> O *> V *> O *> r -->*
  S0 (0inf <* <[1;0]^^(5+b) <* <[1;1]) 1 1 (O *> r).
Proof. unfold S0; es' b & r. Qed.

Lemma cleanup l r:
  l <* <[1;0] <* <[1;1] <* <[0;0] <{{E}} V *> O *> r -->*
  S0 l 2 2 (O *> r).
Proof. unfold S0; esx. Qed.

Lemma fourth_zero b m r: Num m r -> m+4<=(8+b)*2 ->
  Returns (1+b) (O *> O *> Z *> O *> Z *> r).
Proof.
  intros N B.
  destruct (count0 (0inf <* <[1;0]^^(5+b) <* <[1;1]) 0 0 m (Num_one N))
    as [s [Ns Hs]].
  destruct (@pair (1+m) s) as [t [Nt Ht]]; [applys_eq Ns; flia|].
  destruct (counts (0inf <* <[1;0]^^(4+b)) 1 0 1 (2+m) (Num_one Nt))
    as [s' [Ns' Hs']].
  exists (8+b),s'; split.
  - split; [lia|exists (4+m); split; [applys_eq Ns'; flia|lia]].
  - follow10 (enter b 0 r); follow start_zero.
    follow100 Hs.
    unfold S1 in *; follow100 (Ht (0inf <* <[1;0]^^(5+b) <* <[1;1] <* <[0;0]) 0%nat).
    follow (cleanup (0inf <* <[1;0]^^(4+b)) t).
    follow Hs'; unfold S0,K; finish; st; simpl_rotate; flia.
Qed.

Lemma index_power j: j<=2^j.
Proof. induction j; cbn[Nat.pow] in *; lia. Qed.

Lemma fourth_positive b j m r: Num m r -> 4*2^(1+j)*(1+m*2)<=2+b ->
  Returns (1+b) (O *> O *> Z *> O^^(2+j) *> Z *> r).
Proof.
  intros N B.
  pose proof (Nat.pow_nonzero 2 j) as P.
  pose proof (index_power j) as J.
  assert (Budget: 2^j*2<=7+b) by (cbn[Nat.add Nat.pow] in *; nia).
  destruct (internal_pairs (2^j-1) (Bits_one (Bits_zeros j))) as [w [Nw Hw]].
  - cbn[Nat.add Nat.pow]; lia.
  - assert (Ew: w=O^^(1+j)) by
      (apply Bits_ones; applys_eq Nw; cbn[Nat.add Nat.pow]; flia).
    subst w.
    destruct (clear_ones (1+j) m (Num_one N)) as [s [Ns Hs]].
    destruct (@counts (0inf <* <[1;0]^^(7+b-2^(1+j))) (2^j) 0 (1+j) (m+1+j) s)
      as [t [Nt Ht]]; [applys_eq Ns; flia|].
    exists (9+b+j),t; split.
    + split; [lia|exists (m+1+j+2^(1+j)); split].
      * applys_eq Nt; cbn[Nat.add Nat.pow]; flia.
      * cbn[Nat.add Nat.pow] in *; nia.
    + follow10 (enter b (1+j) r); follow (start_internal b j r).
      eapply evstep_trans.
      * applys_eq (Hw 0inf (7+b-2^(1+j)) 0%nat (O *> r));
          cbn[Nat.add Nat.pow]; flia.
      * unfold Internal.
        follow (exit_internal (1+j)
          (0inf <* <[1;0]^^(7+b-2^(1+j)) <* <[0;1]^^(2^j*2)) r).
        follow (Hs (0inf <* <[1;0]^^(7+b-2^(1+j)) <* <[0;1]^^(2^j*2)) 0%nat).
        eapply evstep_trans; [applys_eq Ht; unfold S0; flia|].
        replace (9+b+j) with (1+(1+j)+2^j*2+(7+b-2^(1+j))) by
          (cbn[Nat.add Nat.pow] in *; lia).
        unfold K,S0; finish; st; reflexivity.
Qed.

Lemma Num_run n r: Num n r -> exists j m s,
  r=O^^j *> Z *> s /\ Num m s /\ 1+n=2^j*(1+m*2).
Proof.
  intro H; induction H as [|n r N IH|n r N [j [m [s [-> [Ns E]]]]]].
  - exists 0%nat,0%nat,0inf; repeat split; [st; reflexivity|constructor].
  - exists 0%nat,n,r; repeat split; auto; cbn[Nat.pow]; lia.
  - exists (1+j),m,s; repeat split; auto.
    cbn[Nat.add Nat.pow]; nia.
Qed.

Lemma closed b r: Safe b r -> Returns b r.
Proof.
  intros [B [n [N Vb]]]; destruct b as [|b]; [lia|].
  destruct (mod2 n) as [m E|k E].
  - apply (@branch1 b m r); [applys_eq N; flia|lia].
  - destruct (mod2 k) as [u E'|m E'].
    + destruct (mod2 u) as [m E''|v E''].
      * apply (@branch3 b m r); [applys_eq N; flia|lia].
      * destruct (Num_odd n N) as [r1 [-> N1]].
        destruct (Num_odd k (r:=r1)) as [r2 [-> N2]]; [applys_eq N1; flia|].
        destruct (Num_even u (r:=r2)) as [r3 [-> N3]]; [applys_eq N2; flia|].
        destruct (Num_odd v (r:=r3)) as [r4 [-> N4]]; [applys_eq N3; flia|].
        destruct (Num_run N4) as [j [m [s [-> [Ns F]]]]].
        destruct j.
        -- apply (@fourth_zero b m s Ns); cbn[Nat.pow] in F; lia.
        -- applys_eq (@fourth_positive b j m s Ns); cbn[Nat.add Nat.pow] in *; nia.
    + apply (@branch2 b m r); [applys_eq N; flia|lia].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=K 1 (O *> 0inf)); [unfold K,S0; esx|].
  eapply progress_nonhalt_cond with (i0:=(1%nat,O *> 0inf))
    (C:=fun br => K (fst br) (snd br)) (P:=fun br => Safe (fst br) (snd br)).
  - intros [b r] H; destruct (closed H) as [b' [r' [H' E]]].
    exists (b',r'); split; assumption.
  - cbn[fst snd]; split; [lia|exists 0%nat; split; [exact (Num_one Num_nil)|lia]].
Qed.

End TM15.

(* BEC.txt TM22--24, TM28--34, TM38--40: pre-increment counters.
   The credit invariant and termination order are shared by all machines. *)
Set Implicit Arguments.

Module PreCounter.
Local Notation length := List.length.

(* Segment ranks are stored leftmost first, but compared rightmost first. *)
Definition pair_lt (p q:nat*nat) :=
  fst p < fst q \/ (fst p = fst q /\ snd p < snd q).

Lemma pair_lt_wf: well_founded pair_lt.
Proof.
  intros [a b]; gen b; induction a using lt_wf_ind; intro b; induction b using lt_wf_ind.
  constructor; intros [c d] E; unfold pair_lt in E; cbn in E.
  destruct E as [E|[-> E]]; auto.
Qed.

Inductive colex : list (nat*nat) -> list (nat*nat) -> Prop :=
| colex_head p q r: pair_lt p q -> colex (p::r) (q::r)
| colex_tail p q r s: colex r s -> colex (p::r) (q::s).

Lemma colex_length r s: colex r s -> length r = length s.
Proof. intro H; induction H; cbn; congruence. Qed.

Lemma colex_wf: well_founded colex.
Proof.
  intro r; induction r as [|p r IH].
  - constructor; intros x H; inversion H.
  - gen p; induction IH as [r HR IH]; intro p.
    induction (pair_lt_wf p) as [p HP IP].
    constructor; intros x H; inversion H; subst; eauto.
Qed.

Lemma pair_lt_trans p q r: pair_lt p q -> pair_lt q r -> pair_lt p r.
Proof. unfold pair_lt; lia. Qed.

Lemma colex_trans r s t: colex r s -> colex s t -> colex r t.
Proof.
  intro H; gen t; induction H; intros t H'; inversion H'; subst;
    eauto using colex_head, colex_tail, pair_lt_trans.
Qed.

Definition smaller r s := length r < length s \/ colex r s.

Lemma smaller_wf: well_founded smaller.
Proof.
  intro r; remember (length r) as n; gen r.
  induction n using lt_wf_ind; intros r E.
  induction (colex_wf r) as [r HR IH].
  constructor; intros s [L|L].
  - apply (H (length s)); auto; lia.
  - apply IH; auto; pose proof (colex_length L); lia.
Qed.

Lemma smaller_trans r s t: smaller r s -> smaller s t -> smaller r t.
Proof.
  intros [H|H] [H'|H']; unfold smaller;
    try (left; pose proof (colex_length H); lia);
    try (left; pose proof (colex_length H'); lia).
  - left; lia.
  - right; eapply colex_trans; eauto.
Qed.

(* Ignore the bit count of the first segment.  H may extend that count,
   but cannot increase its U count unless a more significant rank falls. *)
Inductive loose : list (nat*nat) -> list (nat*nat) -> Prop :=
| loose_short r s: length r < length s -> loose r s
| loose_tail p q r s: colex r s -> loose (p::r) (q::s)
| loose_head a b c d r: a <= c -> loose ((a,b)::r) ((c,d)::r).

Definition bump (u b:nat) r :=
  match r with [] => [] | (a,c)::r => (u+a,b+c)::r end.

Lemma bump_length u b r: length (bump u b r) = length r.
Proof. destruct r as [|[a c] r]; reflexivity. Qed.

Lemma loose_bump u b r s: loose r s -> loose (bump u b r) (bump u b s).
Proof.
  intro H; destruct H.
  - apply loose_short; rewrite !bump_length; assumption.
  - destruct p,q; cbn[bump]; constructor; assumption.
  - cbn[bump]; constructor; lia.
Qed.

Lemma loose_U r s: s<>[] -> loose r s -> smaller r (bump 1 0 s).
Proof.
  intros N H; destruct H; unfold smaller.
  - left; rewrite bump_length; assumption.
  - destruct q; right; cbn[bump]; constructor; assumption.
  - right; cbn[bump]; apply colex_head; unfold pair_lt; cbn; lia.
Qed.

Lemma bump_smaller u b r: r<>[] -> 0<u+b -> smaller r (bump u b r).
Proof.
  destruct r as [|[a c] r]; intros N H; [contradiction|].
  right; cbn[bump]; apply colex_head; unfold pair_lt; cbn; lia.
Qed.

Lemma loose_Q p q r s: smaller r s -> loose (p::r) (q::s).
Proof.
  intros [H|H]; [apply loose_short; cbn; lia|constructor; assumption].
Qed.

Lemma loose_refl r: r<>[] -> loose r r.
Proof. destruct r as [|[a b] r]; intro H; [contradiction|constructor; lia]. Qed.

Inductive digit := U | Z | O | Q.
Fixpoint rank r : list (nat*nat) :=
  match r with
  | [] => [(0%nat,0%nat)]
  | U::r => bump 1 0 (rank r)
  | Z::r | O::r => bump 0 1 (rank r)
  | Q::r => (0%nat,0%nat)::rank r
  end.
Lemma rank_nonempty r: rank r<>[].
Proof. induction r as [|d r IH]; [discriminate|]; destruct d; cbn[rank];
  destruct (rank r) as [|[a b] s]; cbn[bump] in *; congruence. Qed.

Lemma rank_tail d r: smaller (rank r) (rank (d::r)).
Proof.
  destruct d; cbn[rank]; try (apply bump_smaller; [apply rank_nonempty|lia]).
  left; cbn; lia.
Qed.

Fixpoint value r : nat :=
  match r with
  | [] => 0
  | U::r => value r
  | Z::r => value r*2
  | O::r => 1+value r*2
  | Q::r => 1
  end.
Fixpoint credit r : BinNums.Z :=
  match r with
  | [] => 0%Z
  | U::r => (1+credit r)%Z
  | Z::r => (credit r*2)%Z
  | O::r => (1+credit r*2)%Z
  | Q::r => (1-Z.of_nat (value r)*2)%Z
  end.
Fixpoint balanced r : Prop :=
  match r with
  | [] => True
  | U::r | Z::r => balanced r /\ 0<value r
  | O::r => balanced r
  | Q::r => balanced r /\ 0<value r /\ (0<=credit r)%Z
  end.
Definition Good r := balanced r /\ (0<=credit r)%Z.
Definition us n r := repeat U n ++ r.

Lemma us_value n r: value (us n r) = value r.
Proof. induction n; cbn[us repeat app value] in *; assumption || reflexivity. Qed.
Lemma us_credit n r: credit (us n r) = (Z.of_nat n+credit r)%Z.
Proof.
  induction n; [reflexivity|].
  change (1+credit (us n r)=Z.of_nat (S n)+credit r)%Z; rewrite IHn; lia.
Qed.
Lemma us_balanced n r: balanced r -> 0<value r -> balanced (us n r).
Proof.
  intros B V; induction n; [exact B|].
  change (balanced (us n r) /\ 0<value (us n r)).
  split; [assumption|rewrite us_value; assumption].
Qed.
Lemma us_rank n r: rank (us n r) = bump n 0 (rank r).
Proof.
  induction n.
  - change (rank r=bump 0 0 (rank r)); destruct (rank r) as [|[a b] s]; reflexivity.
  - change (bump 1 0 (rank (us n r))=bump (S n) 0 (rank r)).
    rewrite IHn; destruct (rank r) as [|[a b] s]; reflexivity.
Qed.

Inductive Result r : nat -> list digit -> Prop :=
| result_done n: Result r n [O]
| result_pending n z:
    Good z -> 0<value z -> value z*2 <= n+value r ->
    smaller (rank z) (rank r) -> Result r n (Q::z).

Lemma result_lift r r' n n' z: Result r n z -> smaller (rank r) (rank r') ->
  n+value r <= n'+value r' -> Result r' n' z.
Proof.
  intros H L V; inversion H; subst; constructor; auto; try lia.
  eapply smaller_trans; eauto.
Qed.

Lemma result_tail r n z: Result r n z ->
  balanced (us n z) /\ value (us n z)=1%nat /\
  (2-Z.of_nat (value r)*2 <= credit (Z::us n z))%Z /\
  loose (rank (Z::us n z)) (rank (Q::r)).
Proof.
  intro H; inversion H; subst; cbn[rank credit]; rewrite us_value, us_credit, us_rank.
  - repeat split; try (apply us_balanced; cbn[balanced value]; auto; lia);
      cbn[value credit]; try lia.
    apply loose_short; rewrite bump_length; cbn.
    pose proof (rank_nonempty r) as N; destruct (rank r); [contradiction|cbn; lia].
  - destruct H0 as [B C]; repeat split.
    + apply us_balanced; cbn[balanced value]; auto.
    + cbn[credit]; lia.
    + cbn[rank bump]; apply loose_Q; assumption.
Qed.

Section Machine.
Context {tm:TM} (uw:list Sym) (hR hL:DH0) (gR:bool->DH0) (left:side).
Definition word d := match d with U=>uw | Z=>[0;0;0] | O=>[0;1;0] | Q=>[0;1] end.
Fixpoint tape r : side := match r with []=>0inf | d::r=>word d *> tape r end.
Notation h := [(hR,hL)].
Notation g m := [(gR m,hL)].
Definition prefix (m:bool) := if m then word U else word Z.
Record Rules : Prop := {
  rule_U: segRLs tm h h (word U) (word U);
  rule_Z: segRLs tm h [] (word Z) (word O);
  rule_O: segRLs tm h h (word O) (word Z);
  rule_nil: sideRLs tm h 0inf (word O *> 0inf);
  rule_Q: segRLs tm h (g false) (word Q) [];
  rule_mU: forall m, segRLs tm (g m) (h++g true) (word U) (prefix m);
  rule_mZ: forall m, segRLs tm (g m) [] (word Z) (prefix m++word Q);
  rule_mO: forall m, segRLs tm (g m) (g true) (word O) (prefix m);
  rule_mnil: forall m, sideRLs tm (g m) 0inf (prefix m *> word O *> 0inf);
  rule_reset: forall r, left {{{ (hL,L) }}} r -[tm]->*
    left {{{ (gR true,R) }}} r
}.
Context (rules:Rules).
Local Hint Resolve rule_U rule_Z rule_O rule_nil rule_Q rule_mU rule_mZ
  rule_mO rule_mnil : core.
Definition Call r z := forall m, sideRLs tm (g m) (tape r) (prefix m *> tape z).

Lemma Call_nil: Call [] [O].
Proof. intro m; cbn[tape]; eauto. Qed.
Lemma Call_Z r: Call (Z::r) (Q::r).
Proof.
  intro m; cbn[tape]; rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat; [eauto|constructor].
Qed.
Lemma Call_O r z: Call r z -> Call (O::r) (U::z).
Proof. intros C m; cbn[tape]; eapply segRLs_sideRLs_concat; [eauto|apply (C true)]. Qed.
Lemma Call_U r r' z: sideRLs tm h (tape r) (tape r') ->
  Call r' z -> Call (U::r) (U::z).
Proof.
  intros H C m; cbn[tape]; eapply segRLs_sideRLs_concat; [eauto|].
  eapply sideRLs_trans; [exact H|apply (C true)].
Qed.

Lemma total r:
  (balanced r -> exists r', sideRLs tm h (tape r) (tape r') /\
    balanced r' /\ value r'=1+value r /\
    (1+credit r<=credit r')%Z /\ loose (rank r') (rank r)) /\
  (Good r -> exists n z, Result r n z /\ Call r (us n z)).
Proof.
  induction r using (well_founded_induction
    (wf_inverse_image _ _ smaller rank smaller_wf)).
  rename H into IH; split.
  - intro B; destruct r as [|d r].
    + exists [O]; repeat split; cbn[tape balanced value credit rank];
        eauto; try lia; constructor; lia.
    + destruct d; cbn[balanced] in B.
      * destruct B as [B V].
        destruct (proj1 (IH r (rank_tail U r)) B) as [s [Hs [Bs [Vs [Cs Rs]]]]].
        exists (U::s); cbn[tape balanced value credit rank]; repeat split; try lia; auto.
        -- eapply segRLs_sideRLs_concat; eauto.
        -- apply loose_bump; assumption.
      * destruct B as [B V].
        exists (O::r); cbn[tape balanced value credit rank]; repeat split; try lia; auto.
        -- eapply segRLs_sideRLs_concat; [eauto|constructor].
        -- apply loose_refl; exact (rank_nonempty (Z::r)).
      * destruct (proj1 (IH r (rank_tail O r)) B) as [s [Hs [Bs [Vs [Cs Rs]]]]].
        exists (Z::s); cbn[tape balanced value credit rank]; repeat split; try lia; auto.
        -- eapply segRLs_sideRLs_concat; eauto.
        -- apply loose_bump; assumption.
      * destruct B as [B [V C]].
        destruct (proj2 (IH r (rank_tail Q r)) (conj B C)) as [n [z [R Hs]]].
        destruct (result_tail R) as [B' [V' [C' L]]].
        exists (Z::us n z); repeat split.
        -- cbn[tape]; eapply @segRLs_sideRLs_concat with (w2:=[]); [eauto|apply (Hs false)].
        -- exact B'.
        -- lia.
        -- cbn[value]; lia.
        -- cbn[credit] in *; lia.
        -- exact L.
  - intros [B C]; destruct r as [|d r].
    + exists 0%nat,[O]; split; [constructor|apply Call_nil].
    + destruct d; cbn[balanced] in B; cbn[credit] in C.
      * destruct B as [B V].
        destruct (proj1 (IH r (rank_tail U r)) B) as [s [Hs [Bs [Vs [Cs Rs]]]]].
        assert (L: smaller (rank s) (rank (U::r))) by
          (apply loose_U; [apply rank_nonempty|exact Rs]).
        destruct (proj2 (IH s L)) as [n [z [R Gs]]]; [split; auto; lia|].
        exists (1+n),z; split.
        -- eapply result_lift; [exact R|exact L|cbn[value]; lia].
        -- cbn[us repeat app]; eapply Call_U; eauto.
      * destruct B as [B V].
        exists 0%nat,(Q::r); split; [|apply Call_Z].
        constructor; [split; auto; lia|assumption|cbn[value]; lia|apply rank_tail].
      * destruct (proj2 (IH r (rank_tail O r))) as [n [z [R Gs]]]; [split; auto; lia|].
        exists (1+n),z; split.
        -- eapply result_lift; [exact R|apply rank_tail|cbn[value]; lia].
        -- cbn[us repeat app]; apply Call_O; assumption.
      * destruct B as [B [V C']]; lia.
Qed.

Lemma closed r: Good r -> value r=1%nat -> exists r',
  sideRLs tm (g true) (tape r) (tape r') /\ Good r' /\ value r'=1%nat.
Proof.
  intros B V; destruct (proj2 (total r) B) as [n [z [R C]]].
  destruct (result_tail R) as [B' [V' [C' L]]].
  exists (U::us n z); split; [apply (C true)|].
  unfold Good; cbn[balanced value credit] in *; repeat split; auto; lia.
Qed.

Definition state r := left {{{ (hL,L) }}} tape r.

Lemma nonhalt_from r: Good r -> value r=1%nat -> ~halts tm (state r).
Proof.
  intros B V; eapply progress_nonhalt_cond with
    (P:=fun r => Good r /\ value r=1%nat); [|split; assumption].
  intros r0 [B0 V0]; destruct (closed B0 V0) as [r' [H [B' V']]].
  exists r'; split; [|split; assumption].
  unfold state; eapply evstep_progress_trans.
  - apply rule_reset; assumption.
  - apply sideRLs_1; assumption.
Qed.

End Machine.
Arguments Rules : clear implicits.
End PreCounter.

Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_0RD---_0RD0LB").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (A,<[1]).
Definition hL : DH0 := (C,[0]).
Definition gR (m:bool) : DH0 :=
  (D,if m then <[1;1;0] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf (us 3 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM22.

Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1RE_1LD1RA_1LA0LD_0RA0LF_1LD---").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (B,<[1]).
Definition hL : DH0 := (D,[0]).
Definition gR (m:bool) : DH0 :=
  (A,if m then <[1;1;0] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf ([O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM23.

Module TM24.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RD_1RE1RD_0RB0LF_1LA1RB_1LA---").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (C,<[1]).
Definition hL : DH0 := (A,[0]).
Definition gR (m:bool) : DH0 :=
  (B,if m then <[1;1;0] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf (us 1 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM24.

Module TM28.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RA---_0RA0LB").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (B,<[1]).
Definition hL : DH0 := (D,[0]).
Definition gR (m:bool) : DH0 :=
  (A,if m then <[1;0;1] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf ([O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM28.

Module TM29.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RF_1RE0RD_1RB---_1LA1RB_0RB0LC").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (C,<[1]).
Definition hL : DH0 := (A,[0]).
Definition gR (m:bool) : DH0 :=
  (B,if m then <[1;0;1] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf (us 1 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM29.

Module TM30.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1RD---_0RD0LA").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (A,<[1]).
Definition hL : DH0 := (C,[0]).
Definition gR (m:bool) : DH0 :=
  (D,if m then <[1;0;1] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf (us 3 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM30.

Module TM31.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1RD0RA_1LE1RB_1LB0LE_0RB0LC").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (C,<[1]).
Definition hL : DH0 := (E,[0]).
Definition gR (m:bool) : DH0 :=
  (B,if m then <[1;0;1] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf (us 4 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM31.

Module TM32.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RD_1RE1RD_0RB0LE_1LF1RB_---0LA").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (C,<[1]).
Definition hL : DH0 := (A,[0]).
Definition gR (m:bool) : DH0 :=
  (B,if m then <[1;1;0] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf (us 1 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM32.

Module TM33.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RE_---0LD_1LE0LD_1RA0RF_0RE0LB").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (A,<[1]).
Definition hL : DH0 := (D,[0]).
Definition gR (m:bool) : DH0 :=
  (E,if m then <[1;1;0] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf (us 3 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM33.

Module TM34.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RF_1LD1RA_---0LE_1LA0LE_0RA0LC").
Import PreCounter.
Definition uw : list Sym := [1;0;0].
Definition hR : DH0 := (B,<[1]).
Definition hL : DH0 := (E,[0]).
Definition gR (m:bool) : DH0 :=
  (A,if m then <[1;1;0] else <[1;1;1]).
Lemma rules: Rules tm uw hR hL gR 0inf.
Proof. constructor; intros; try destruct m; cbn[word prefix uw hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL 0inf ([O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM34.

Module TM38.
Definition tm := Eval compute in (TM_from_str "1LB0RA_0RC0LB_1LA0LD_1RE0RD_1RF---_1RA1RC").
Import PreCounter.
Definition uw : list Sym := [1;1;0].
Definition hR : DH0 := (F,[]).
Definition hL : DH0 := (B,[]).
Definition gR (m:bool) : DH0 :=
  (A,if m then <[0;0] else <[1;0]).
Lemma rules: Rules tm uw hR hL gR (0inf <* <[1;1]).
Proof.
  constructor; intros; try destruct m; unfold word, prefix, uw, hR, hL, gR; cbn; esx.
  eapply segLLs_LL_RLs with (w3:=[]); [unfold segLL; intros; finish|constructor].
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL (0inf <* <[1;1]) ([O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM38.

Module TM39.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RE_1LD0RC_0RE0LD_1LC0LF_1RA0RF").
Import PreCounter.
Definition uw : list Sym := [1;1;0].
Definition hR : DH0 := (B,[]).
Definition hL : DH0 := (D,[]).
Definition gR (m:bool) : DH0 :=
  (C,if m then <[0;0] else <[1;0]).
Lemma rules: Rules tm uw hR hL gR (0inf <* <[1;1]).
Proof.
  constructor; intros; try destruct m; unfold word, prefix, uw, hR, hL, gR; cbn; esx.
  eapply segLLs_LL_RLs with (w3:=[]); [unfold segLL; intros; finish|constructor].
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL (0inf <* <[1;1]) (us 15 [Q;O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM39.

Module TM40.
Definition tm := Eval compute in (TM_from_str "1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RA---").
Import PreCounter.
Definition uw : list Sym := [1;1;0].
Definition hR : DH0 := (A,[]).
Definition hL : DH0 := (C,[]).
Definition gR (m:bool) : DH0 :=
  (B,if m then <[0;0] else <[1;0]).
Lemma rules: Rules tm uw hR hL gR (0inf <* <[1;1]).
Proof.
  constructor; intros; try destruct m; unfold word, prefix, uw, hR, hL, gR; cbn; esx.
  eapply segLLs_LL_RLs with (w3:=[]); [unfold segLL; intros; finish|constructor].
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state uw hL (0inf <* <[1;1]) (us 1 [O])).
  - cbn[state tape word uw hL us repeat app]; esx.
  - apply (nonhalt_from rules).
    + repeat split; cbn[us repeat app value credit]; lia.
    + reflexivity.
Qed.
End TM40.

(* BEC.txt TM25--27: post-increment counters.
   Shared budget proof: BEC_POST70_NONHALTING.txt. *)

Unset Implicit Arguments.

Module PostCounter.
Inductive digit := U | Z | O.
Definition word d : list Sym :=
  match d with U => [1;0;0] | Z => [0;0;0] | O => [0;1;0] end.
Fixpoint tape r : side :=
  match r with [] => 0inf | d::r => word d *> tape r end.
Fixpoint budget r : nat :=
  match r with
  | [] => 0
  | U::r => budget r - 1
  | Z::r => 1 + budget r * 2
  | O::r => budget r
  end.
Inductive mode := G | J | K.
Definition prefix m :=
  match m with G => word U | J => word Z | K => [0] end.

Record Rules (tm:TM) (hR hL:DH0) (gR:mode->DH0) : Prop := {
  rule_U: segRLs tm [(hR,hL)] [(hR,hL)] (word U) (word U);
  rule_Z: segRLs tm [(hR,hL)] [] (word Z) (word O);
  rule_O: segRLs tm [(hR,hL)] [(hR,hL)] (word O) (word Z);
  rule_nil: sideRLs tm [(hR,hL)] 0inf (word O *> 0inf);
  rule_Q: segRLs tm [(hR,hL)] [(gR J,hL)] [0;1] [];
  rule_G0: segRLs tm [(gR G,hL)] [(hR,hL)] [0] (word U);
  rule_mU: forall m, segRLs tm [(gR m,hL)] [(gR K,hL);(gR G,hL)]
    (word U) (prefix m);
  rule_mZ: forall m, segRLs tm [(gR m,hL)] []
    (word Z) (prefix m ++ [0;1]);
  rule_mO: forall m, segRLs tm [(gR m,hL)] [(gR G,hL)]
    (word O) (prefix m);
  rule_mnil: forall m, sideRLs tm [(gR m,hL)] 0inf
    (prefix m *> word O *> 0inf);
  rule_reset: forall r, 0inf {{{ (hL,L) }}} r -[tm]->*
    0inf {{{ (gR G,R) }}} r
}.
Arguments Rules : clear implicits.

(* Num k r describes the binary number k+1, without a division function. *)
Inductive Num : nat -> list digit -> Prop :=
| Num_one: Num 0 [O]
| Num_even k r: Num k r -> Num (1+k*2) (Z::r)
| Num_odd k r: Num k r -> Num (2+k*2) (O::r).

Lemma Num_total k: exists r, Num k r /\ budget r <= k.
Proof.
  induction k using lt_wf_ind.
  destruct k as [|k].
  - exists [O]; split; [constructor|cbn; lia].
  - destruct (mod2 k) as [q E|q E]; subst k;
      destruct (H q) as [r [Hr B]]; try lia.
    + exists (Z::r); split; [constructor; assumption|cbn; lia].
    + exists (O::r); split; [constructor; assumption|cbn; lia].
Qed.

Section Machine.
Context {tm:TM} {hR hL:DH0} {gR:mode->DH0} (rules:Rules tm hR hL gR).
Notation h := [(hR,hL)].
Notation g m := [(gR m,hL)].
Local Hint Resolve rule_U rule_Z rule_O rule_nil rule_Q rule_G0
  rule_mU rule_mZ rule_mO rule_mnil : core.

Lemma U_pass n: segRLs tm (h^^n) (h^^n) (word U) (word U).
Proof. eapply segRLs_wall''; eauto. Qed.

Lemma Z_even n: segRLs tm (h^^(n*2)) (h^^n) (word Z) (word Z).
Proof.
  induction n; [constructor|].
  cbn[Nat.mul]; rewrite lpow_add; cbn[lpow].
  eapply segRLs_trans; [|apply IHn].
  apply (@segRLs_trans tm h [] h h (word Z) (word O) (word Z)); eauto.
Qed.

Lemma Z_odd n: segRLs tm (h^^(1+n*2)) (h^^n) (word Z) (word O).
Proof.
  replace (1+n*2) with (n*2+1) by lia; rewrite lpow_add.
  replace (h^^n) with (h^^n++[]) by apply app_nil_r.
  eapply segRLs_trans; [apply Z_even|cbn; eauto].
Qed.

Lemma O_even n: segRLs tm (h^^(n*2)) (h^^n) (word O) (word O).
Proof.
  induction n; [constructor|].
  cbn[Nat.mul]; rewrite lpow_add; cbn[lpow].
  eapply segRLs_trans; [|apply IHn].
  apply (@segRLs_trans tm h h h [] (word O) (word Z) (word O)); eauto.
Qed.

Lemma Num_spec k r: Num k r -> sideRLs tm (h^^k) (word O *> 0inf) (tape r).
Proof.
  intro H; induction H; cbn[tape].
  - constructor.
  - rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=word Z *> word O *> 0inf).
    + cbn[lpow app]; eapply segRLs_sideRLs_concat; eauto.
    + eapply segRLs_sideRLs_concat; [apply Z_even|assumption].
  - rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=word O *> word O *> 0inf).
    + change (h^^2) with (h++h).
      eapply @sideRLs_trans with (r2:=word Z *> word O *> 0inf).
      * eapply segRLs_sideRLs_concat; eauto.
      * eapply segRLs_sideRLs_concat; [eauto|constructor].
    + eapply segRLs_sideRLs_concat; [apply O_even|assumption].
Qed.

(* The intermediate suffix may contain Q; only the final suffix is normal.
   Keeping all three entering heads together avoids assuming a recursive
   call returns before the induction hypothesis has supplied its execution. *)
Definition Call r z := forall m,
  sideRLs tm (g m) (tape r) (prefix m *> z).

Lemma Call_U r z z':
  Call r z -> sideRLs tm h z z' -> Call (U::r) (word U *> z').
Proof.
  intros C H m; cbn[tape].
  eapply segRLs_sideRLs_concat; [eauto|].
  change [(gR K,hL);(gR G,hL)] with (g K++g G).
  eapply sideRLs_trans; [apply (C K)|].
  eapply segRLs_sideRLs_concat; eauto.
Qed.

Lemma Call_O r z: Call r z -> Call (O::r) (word U *> z).
Proof.
  intros C m; cbn[tape].
  eapply segRLs_sideRLs_concat; [eauto|apply (C G)].
Qed.

Lemma Call_Z r: Call (Z::r) ([0;1] *> tape r).
Proof.
  intro m; cbn[tape]; rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat; [eauto|constructor].
Qed.

Lemma Call_nil: Call [] (word O *> 0inf).
Proof. intro m; cbn[tape]; eauto. Qed.

Lemma normalize r k: budget r <= k -> exists z r',
  Call r z /\ sideRLs tm (h^^k) z (tape r') /\ budget r' <= k.
Proof.
  gen k; induction r as [|d r IH]; intros k B; cbn[budget] in B.
  - destruct (Num_total k) as [r' [N B']].
    exists (word O *> 0inf),r'; repeat split; auto using Call_nil, Num_spec.
  - destruct d.
    + destruct (IH (1+k)) as [z [r' [C [H B']]]]; [cbn[budget] in B; lia|].
      change (h^^(1+k)) with (h++h^^k) in H.
      destruct (sideRLs_split H) as [z' [H1 Hk]].
      exists (word U *> z'),(U::r'); repeat split.
      * apply Call_U with (z:=z); assumption.
      * cbn[tape]; eapply segRLs_sideRLs_concat; [apply U_pass|assumption].
      * cbn[budget]; lia.
    + cbn[budget] in B; destruct k as [|k]; [lia|].
      destruct (mod2 k) as [q E|q E]; subst k;
        destruct (IH q) as [z [r' [C [H B']]]]; try lia.
      * exists ([0;1] *> tape r),(Z::r'); repeat split.
        -- apply Call_Z.
        -- change (h^^(S (q*2))) with (h++h^^(q*2)).
           eapply @sideRLs_trans with (r2:=word Z *> z).
           ++ eapply @segRLs_sideRLs_concat with (w2:=[]); [eauto|apply (C J)].
           ++ cbn[tape]; eapply segRLs_sideRLs_concat; [apply Z_even|assumption].
        -- cbn[budget]; lia.
      * exists ([0;1] *> tape r),(O::r'); repeat split.
        -- apply Call_Z.
        -- change (h^^(S (1+q*2))) with (h++h^^(1+q*2)).
           eapply @sideRLs_trans with (r2:=word Z *> z).
           ++ eapply @segRLs_sideRLs_concat with (w2:=[]); [eauto|apply (C J)].
           ++ cbn[tape]; eapply segRLs_sideRLs_concat; [apply Z_odd|assumption].
        -- cbn[budget]; lia.
    + destruct (IH k) as [z [r' [C [H B']]]]; [assumption|].
      exists (word U *> z),(U::r'); repeat split.
      * apply Call_O; assumption.
      * cbn[tape]; eapply segRLs_sideRLs_concat; [apply U_pass|assumption].
      * cbn[budget]; lia.
Qed.

Lemma closed r: budget r=0%nat -> exists r',
  sideRLs tm (g G) (tape r) (tape r') /\ budget r'=0%nat.
Proof.
  intros B; destruct (normalize r 0%nat) as [z [r' [C [H B']]]]; [lia|].
  inversion H; subst. exists (U::r'); split; [apply (C G)|cbn[budget]; lia].
Qed.

Definition state r := 0inf {{{ (hL,L) }}} tape r.

Lemma nonhalt_from r: budget r=0%nat -> ~halts tm (state r).
Proof.
  intro B; eapply progress_nonhalt_cond with (P:=fun r => budget r=0%nat); [|exact B].
  intros r0 B0; destruct (closed r0 B0) as [r' [H B']].
  exists r'; split; [|assumption].
  unfold state; eapply evstep_progress_trans.
  - apply (rule_reset _ _ _ _ rules).
  - apply sideRLs_1; assumption.
Qed.

End Machine.
End PostCounter.

Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1RD0RA_1LE1RB_1LB0LE_0RA0LC").
Import PostCounter.
Definition hR : DH0 := (C,<[1]).
Definition hL : DH0 := (E,[0]).
Definition gR m : DH0 :=
  match m with G => (B,<[1;0;1]) | J => (B,<[1;1;1]) | K => (B,<[1]) end.
Lemma rules: Rules tm hR hL gR.
Proof. constructor; intros; try destruct m; cbn [word prefix hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state (hL:=hL) [U;Z;O]).
  - cbn [state tape word hL]; esx.
  - apply (nonhalt_from rules); reflexivity.
Qed.
End TM25.

Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RA---_0RE0LB").
Import PostCounter.
Definition hR : DH0 := (B,<[1]).
Definition hL : DH0 := (D,[0]).
Definition gR m : DH0 :=
  match m with G => (A,<[1;0;1]) | J => (A,<[1;1;1]) | K => (A,<[1]) end.
Lemma rules: Rules tm hR hL gR.
Proof. constructor; intros; try destruct m; cbn [word prefix hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state (hL:=hL) [O]).
  - cbn [state tape word hL]; esx.
  - apply (nonhalt_from rules); reflexivity.
Qed.
End TM26.

Module TM27.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RF_1RE0RD_1RB---_1LA1RB_0RD0LC").
Import PostCounter.
Definition hR : DH0 := (C,<[1]).
Definition hL : DH0 := (A,[0]).
Definition gR m : DH0 :=
  match m with G => (B,<[1;0;1]) | J => (B,<[1;1;1]) | K => (B,<[1]) end.
Lemma rules: Rules tm hR hL gR.
Proof. constructor; intros; try destruct m; cbn [word prefix hR hL gR]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=state (hL:=hL) [U;O]).
  - cbn [state tape word hL]; esx.
  - apply (nonhalt_from rules); reflexivity.
Qed.
End TM27.

