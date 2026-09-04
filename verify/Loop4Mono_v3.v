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
Definition tm := Eval compute in (TM_from_str "1LB1RB_1RC0LE_1RE0RD_1RA---_1LF1LB_0RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition h3: list (DH0*DH0) := [((C,<[0;1;1;1]),(F,[]))].
Definition h1: list (DH0*DH0) := (h3^^2).
Definition h2: list (DH0*DH0) := [((A,<[]),(B,[]));((A,<[]),(B,[1;0]))].

Definition D1 n := [0;1;0;1;0] ++ [1;0;1;0]^^n.
Definition D2 n := [0;1;0] ++ [1;0;1;0]^^n.

Lemma D1_Inc11 n:
  segRLs tm h1 h1 (D1 n) (D1 n).
Proof.
  ut; esx.
Qed.

Lemma D1_Inc2 n:
  segRLs tm h2 [] (D1 n) (D2 n).
Proof.
  ut; esx.
Qed.

Lemma D2_Inc12 n:
  segRLs tm h1 h2 (D2 n) (D1 (2+n)).
Proof.
  ut; esx.
Qed.

Lemma D1_Inc33 n:
  segRLs tm h3 h3 (D1 n) (D1 n).
Proof.
  ut; esx.
Qed.

Lemma D1_rh_Inc3 n:
  sideRLs tm h3 (D1 n *> 0inf) (D1 (1+n) *> D2 0 *> 0inf).
Proof.
  ut; esx.
Qed.

Lemma D2_rh_Inc3 n:
  sideRLs tm h3 (D2 n *> 0inf) (D1 (1+n) *> 0inf).
Proof.
  ut; es' n.
Qed.

Lemma D20_rh_Inc2:
  sideRLs tm h2 (D2 0 *> 0inf) 0inf.
Proof.
  ut; esx; st; er.
Qed.

Definition S' '(n,r) := 0inf {{{ (F,[],L) }}} [1;0;1;0]^^n *> r.

Lemma Inc n r r':
  sideRLs tm h3 r r' ->
  S' (1+n,r) -->+
  S' (n,r').
Proof.
  unfold S'.
  intros H.
  eapply sideRLs_1 in H.
  es; er.
  follow100 H.
  es.
Qed.

Lemma Ov n n0 r:
  S' (O,D1 n *> D1 n0 *> r) -->+
  S' (2+n, D2 n0 *> r).
Proof.
  es' n n0 & r.
Qed.

Lemma init:
  c0 -->*
  S' (O, D1 3 *> D1 2 *> D1 2 *> D1 1 *> 0inf).
Proof.
  esx.
Qed.




Import ListNotations.

Inductive rword := R1 (n:nat) | R2 (n:nat).

Fixpoint rside (xs:list rword) : side :=
  match xs with
  | [] => 0inf
  | R1 n::xs => D1 n *> rside xs
  | R2 n::xs => D2 n *> rside xs
  end.

Definition rconfig (xs:list rword) := S' (O,rside xs).

Fixpoint pair_step (xs:list rword) : option (list rword) :=
  match xs with
  | [] => None
  | R1 n::[] => Some [R1 (n+1);R1 1]
  | R1 n::xs => option_map (cons (R1 n)) (pair_step xs)
  | R2 n::[] => Some [R1 (n+2);R2 0]
  | R2 n::R2 0::[] => Some [R1 (n+2)]
  | R2 n::R1 m::xs => Some (R1 (n+2)::R2 m::xs)
  | _ => None
  end.

Lemma pair_step_sound xs ys:
  pair_step xs = Some ys ->
  sideRLs tm h1 (rside xs) (rside ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys H; [discriminate|].
  destruct x as [n|n].
  - destruct xs as [|z xs].
    + inversion H; subst; cbn [rside].
      replace (n+1) with (1+n) by lia.
      unfold h1. change (sideRLs tm (h3++h3)
        (D1 n *> 0inf) (D1 (1+n) *> D1 1 *> 0inf)).
      eapply @sideRLs_trans with
        (r2:=D1 (1+n) *> D2 0 *> 0inf).
      * apply D1_rh_Inc3.
      * eapply segRLs_sideRLs_concat; [apply D1_Inc33|].
        apply D2_rh_Inc3.
    + change (option_map (cons (R1 n)) (pair_step (z::xs)) = Some ys) in H.
      destruct (pair_step (z::xs)) as [zs|] eqn:E; cbn in H;
        [|discriminate].
      inversion H; subst; cbn [rside].
      eapply segRLs_sideRLs_concat; [apply D1_Inc11|].
      apply IH; reflexivity.
  - destruct xs as [|x xs].
    + inversion H; subst; cbn [rside].
      unfold h1. change (sideRLs tm (h3++h3)
        (D2 n *> 0inf) (D1 (n+2) *> D2 0 *> 0inf)).
      eapply @sideRLs_trans with (r2:=D1 (1+n) *> 0inf).
      * apply D2_rh_Inc3.
      * replace (n+2) with (1+(1+n)) by lia. apply D1_rh_Inc3.
    + destruct x as [m|m].
      * inversion H; subst; cbn [rside].
        replace (n+2) with (2+n) by lia.
        eapply segRLs_sideRLs_concat; [apply D2_Inc12|].
        eapply segRLs_sideRLs_concat; [apply D1_Inc2|constructor].
      * destruct m; destruct xs; inversion H; subst; cbn [rside].
        replace (n+2) with (2+n) by lia.
        eapply segRLs_sideRLs_concat; [apply D2_Inc12|exact D20_rh_Inc2].
Qed.

Fixpoint single_step (xs:list rword) : option (list rword) :=
  match xs with
  | [] => None
  | R1 n::[] => Some [R1 (n+1);R2 0]
  | R1 n::xs => option_map (cons (R1 n)) (single_step xs)
  | R2 n::[] => Some [R1 (n+1)]
  | R2 _::_ => None
  end.

Lemma single_step_sound xs ys:
  single_step xs = Some ys ->
  sideRLs tm h3 (rside xs) (rside ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys H; [discriminate|].
  destruct x as [n|n]; destruct xs as [|z xs].
  - inversion H; subst; cbn [rside].
    replace (n+1) with (1+n) by lia. apply D1_rh_Inc3.
  - change (option_map (cons (R1 n)) (single_step (z::xs)) = Some ys) in H.
    destruct (single_step (z::xs)) as [zs|] eqn:E; cbn in H;
      [|discriminate].
    inversion H; subst; cbn [rside].
    eapply segRLs_sideRLs_concat; [apply D1_Inc33|].
    apply IH; reflexivity.
  - inversion H; subst; cbn [rside].
    replace (n+1) with (1+n) by lia. apply D2_rh_Inc3.
  - discriminate.
Qed.

Fixpoint pair_run (k:nat) (xs:list rword) : option (list rword) :=
  match k with
  | O => Some xs
  | S k =>
      match pair_step xs with
      | Some ys => pair_run k ys
      | None => None
      end
  end.

Lemma pair_run_sound k xs ys:
  pair_run k xs = Some ys ->
  sideRLs tm (h1^^k) (rside xs) (rside ys).
Proof.
  revert xs; induction k; intros xs H.
  - inversion H; subst; constructor.
  - cbn [pair_run] in H.
    destruct (pair_step xs) as [zs|] eqn:E; [|discriminate].
    cbn [lpow]. eapply sideRLs_trans.
    + apply pair_step_sound,E.
    + apply IHk,H.
Qed.

Definition service (calls:nat) (xs:list rword) : option (list rword) :=
  match pair_run (calls/2) xs with
  | None => None
  | Some ys => if Nat.odd calls then single_step ys else Some ys
  end.

Lemma h1_pow k:
  h1^^k = h3^^(2*k).
Proof.
  induction k; [reflexivity|].
  change (h1 ++ h1^^k = h3^^(2*S k)). rewrite IHk.
  replace (2*S k) with (2+2*k) by lia.
  rewrite lpow_add. unfold h1,h3. reflexivity.
Qed.

Lemma odd_div n:
  Nat.odd n = true -> n = 2*(n/2)+1.
Proof.
  rewrite Nat.odd_spec. intros [m ->].
  replace ((2*m+1)/2) with m.
  - reflexivity.
  - replace (2*m+1) with (Nat.b2n true+2*m) by (cbn; lia).
    symmetry; apply Nat.add_b2n_double_div2.
Qed.

Lemma even_div n:
  Nat.odd n = false -> n = 2*(n/2).
Proof.
  intros Ho. assert (He:Nat.even n=true).
  { rewrite <-Nat.negb_odd,Ho. reflexivity. }
  rewrite Nat.even_spec in He. destruct He as [m ->].
  replace ((2*m)/2) with m.
  - reflexivity.
  - replace (2*m) with (Nat.b2n false+2*m) by (cbn; lia).
    symmetry; apply Nat.add_b2n_double_div2.
Qed.

Lemma service_sound calls xs ys:
  service calls xs = Some ys ->
  sideRLs tm (h3^^calls) (rside xs) (rside ys).
Proof.
  unfold service.
  destruct (pair_run (calls/2) xs) as [zs|] eqn:E; [|discriminate].
  pose proof (pair_run_sound _ _ _ E) as Hp.
  rewrite h1_pow in Hp.
  destruct (Nat.odd calls) eqn:Ho.
  - intros Hs. pose proof (single_step_sound _ _ Hs) as Hsingle.
    rewrite (odd_div _ Ho).
    rewrite lpow_add. cbn [lpow]. rewrite app_nil_r.
    eapply sideRLs_trans; eassumption.
  - intros H; inversion H; subst.
    rewrite (even_div _ Ho).
    exact Hp.
Qed.

Definition reset_step (xs:list rword) : option (list rword) :=
  match xs with
  | R1 a::R1 b::xs => service (a+2) (R2 b::xs)
  | _ => None
  end.

Lemma Incs k n r r':
  sideRLs tm (h3^^k) r r' ->
  S' (k+n,r) -->* S' (n,r').
Proof.
  revert n r r'; induction k; intros n r r' H.
  - cbn [lpow] in H. inverts H. apply evstep_refl.
  - cbn [lpow] in H.
    destruct (sideRLs_split H) as [r0 [Hone Hrest]].
    eapply evstep_trans.
    + apply progress_evstep,Inc. exact Hone.
    + replace (S k+n-1) with (k+n) by lia.
      apply IHk,Hrest.
Qed.

Lemma reset_step_sound xs ys:
  reset_step xs = Some ys -> rconfig xs -->+ rconfig ys.
Proof.
  destruct xs as [|x xs]; [discriminate|].
  destruct x as [a|a]; [|discriminate].
  destruct xs as [|x xs]; [discriminate|].
  destruct x as [b|b]; [|discriminate].
  cbn [reset_step rconfig rside]. intros H.
  pose proof (service_sound _ _ _ H) as Hservice.
  eapply progress_evstep_trans; [apply Ov|].
  replace (2+a) with ((a+2)+O) by lia.
  apply (Incs (a+2) O),Hservice.
Qed.

(* The finite alphabet used by the generation transducer. *)
Inductive letter :=
| LA | LB | LC | LD | LE | LF | LG | LH | LI | LJ | LK.

Definition lphase (x:letter) : bool :=
  match x with LH | LI | LJ | LK => true | _ => false end.

Definition lvalue (x:letter) : nat :=
  match x with
  | LA => 0 | LB => 1 | LC => 2 | LD => 3 | LE => 4 | LF => 5
  | LG => 6 | LH => 3 | LI => 4 | LJ => 5 | LK => 6
  end.

Definition ldelta (x:letter) : Z :=
  match x with
  | LA | LB => 2
  | LC | LD | LH | LI => 0
  | LE | LF | LJ | LK => -2
  | LG => -4
  end.

Definition next_phase (x:letter) : bool :=
  xorb (lphase x) (Nat.odd (lvalue x)).

Definition letter_eqb (x y:letter) : bool :=
  match x,y with
  | LA,LA | LB,LB | LC,LC | LD,LD | LE,LE | LF,LF | LG,LG
  | LH,LH | LI,LI | LJ,LJ | LK,LK => true
  | _,_ => false
  end.

Definition flow (x edge:letter)
  : option (nat*nat*(letter*list letter)) :=
  match x,edge with
  | LA,LC => Some (1%nat,2%nat,(LB,[]))
  | LA,LE => Some (1%nat,2%nat,(LD,[]))
  | LB,LI => Some (1%nat,3%nat,(LI,[]))
  | LC,LC => Some (1%nat,1%nat,(LC,[LC]))
  | LC,LE => Some (1%nat,1%nat,(LE,[LC]))
  | LC,LI => Some (1%nat,1%nat,(LI,[LI]))
  | LD,LB => Some (2%nat,2%nat,(LB,[LH]))
  | LD,LD => Some (2%nat,2%nat,(LD,[LH]))
  | LD,LE => Some (1%nat,2%nat,(LE,[LD]))
  | LD,LI => Some (1%nat,2%nat,(LI,[LJ]))
  | LE,LA => Some (1%nat,1%nat,(LA,[LD;LI]))
  | LE,LE => Some (1%nat,1%nat,(LE,[LD;LI]))
  | LE,LI => Some (1%nat,1%nat,(LI,[LJ;LE]))
  | LG,LA => Some (1%nat,1%nat,(LA,[LD;LJ;LE]))
  | LH,LB => Some (2%nat,1%nat,(LC,[LA]))
  | LH,LF => Some (2%nat,1%nat,(LG,[LA]))
  | LI,LB => Some (2%nat,2%nat,(LC,[LB]))
  | LI,LD => Some (2%nat,2%nat,(LE,[LB]))
  | LI,LF => Some (2%nat,2%nat,(LG,[LB]))
  | LI,LH => Some (2%nat,2%nat,(LI,[LH]))
  | LI,LI => Some (3%nat,2%nat,(LJ,[LB]))
  | LI,LJ => Some (2%nat,2%nat,(LK,[LH]))
  | LJ,LH => Some (2%nat,1%nat,(LI,[LH;LE]))
  | LJ,LJ => Some (2%nat,1%nat,(LK,[LH;LE]))
  | LK,LH => Some (2%nat,2%nat,(LI,[LH;LF]))
  | _,_ => None
  end.

Fixpoint phase_tail (x:letter) (w:list letter) : Prop :=
  match w with
  | [] => True
  | y::w => lphase y = next_phase x /\ phase_tail y w
  end.

Definition phase_ok (w:list letter) : Prop :=
  match w with [] => True | x::w => phase_tail x w end.

Inductive ParametersN : Z -> nat -> list letter -> list nat -> Prop :=
| ParametersN_nil offset tail : ParametersN offset tail [] []
| ParametersN_cons offset tail x w n ns :
    Z.of_nat n =
      (2*Z.of_nat (S (length w)+tail)-5+
        Z.of_nat (lvalue x)-offset)%Z ->
    ParametersN (offset+ldelta x)%Z tail w ns ->
    ParametersN offset tail (x::w) (n::ns).

Definition Parameters offset w ns := ParametersN offset O w ns.

Definition rtail (q:bool) : list rword :=
  if q then [R2 0] else [].

Definition physical (w:list letter) (ns:list nat) : list rword :=
  map R1 ns ++ rtail (match w with [] => false | x::_ => lphase x end).

Definition represents (w:list letter) (xs:list rword) : Prop :=
  exists ns, Parameters 0 w ns /\ xs = physical w ns.

Definition r1s (ns:list nat) : list rword := map R1 ns.
Definition add2s (ns:list nat) : list nat := map (fun n => n+2) ns.

Lemma pair_step_cons n xs ys:
  pair_step xs = Some ys ->
  pair_step (R1 n::xs) = Some (R1 n::ys).
Proof.
  destruct xs as [|x xs]; intros H; [discriminate|].
  change (option_map (cons (R1 n)) (pair_step (x::xs)) =
    Some (R1 n::ys)).
  rewrite H. reflexivity.
Qed.

Lemma pair_step_prefix ns xs ys:
  pair_step xs = Some ys ->
  pair_step (r1s ns++xs) = Some (r1s ns++ys).
Proof.
  induction ns; intros H; [exact H|].
  apply pair_step_cons,IHns,H.
Qed.

Lemma single_step_cons n xs ys:
  single_step xs = Some ys ->
  single_step (R1 n::xs) = Some (R1 n::ys).
Proof.
  destruct xs as [|x xs]; intros H; [discriminate|].
  change (option_map (cons (R1 n)) (single_step (x::xs)) =
    Some (R1 n::ys)).
  rewrite H. reflexivity.
Qed.

Lemma single_step_prefix ns xs ys:
  single_step xs = Some ys ->
  single_step (r1s ns++xs) = Some (r1s ns++ys).
Proof.
  induction ns; intros H; [exact H|].
  apply single_step_cons,IHns,H.
Qed.

Lemma pair_run_prefix k ns xs ys:
  pair_run k xs = Some ys ->
  pair_run k (r1s ns++xs) = Some (r1s ns++ys).
Proof.
  revert xs ys; induction k; intros xs ys H.
  - inversion H; reflexivity.
  - cbn [pair_run] in H |- *.
    destruct (pair_step xs) as [zs|] eqn:E; [|discriminate].
    rewrite (pair_step_prefix _ _ _ E).
    apply IHk,H.
Qed.

Lemma pair_run_add a b xs:
  pair_run (a+b) xs =
  match pair_run a xs with
  | Some ys => pair_run b ys
  | None => None
  end.
Proof.
  revert xs; induction a; intros xs; [reflexivity|].
  cbn [pair_run Nat.add].
  destruct (pair_step xs) as [ys|]; [apply IHa|reflexivity].
Qed.

Definition marked (ns:list nat) (tail:list rword) : list rword :=
  match ns with
  | [] => tail
  | n::ns => R2 n::r1s ns++tail
  end.

Lemma pair_step_marked p pre z tail:
  pair_step (marked ((p::pre)++[z]) tail) =
  Some (R1 (p+2)::marked (pre++[z]) tail).
Proof. destruct pre; reflexivity. Qed.

Lemma pair_run_cross pre z tail:
  pair_run (length pre) (marked (pre++[z]) tail) =
  Some (r1s (add2s pre)++R2 z::tail).
Proof.
  induction pre as [|p pre IH].
  - reflexivity.
  - cbn [length pair_run]. rewrite pair_step_marked.
    change (pair_run (length pre)
      (r1s [p+2]++marked (pre++[z]) tail) =
      Some (r1s [p+2]++(r1s (add2s pre)++R2 z::tail))).
    apply pair_run_prefix,IH.
Qed.

Lemma service_cross pre z tail k edge:
  service k (R2 z::tail) = Some edge ->
  service (2*length pre+k) (marked (pre++[z]) tail) =
  Some (r1s (add2s pre)++edge).
Proof.
  intros Hedge. unfold service in Hedge |- *.
  replace ((2*length pre+k)/2) with (length pre+k/2).
  2:{ replace (2*length pre+k) with (k+length pre*2) by lia.
      rewrite Nat.div_add by discriminate. lia. }
  rewrite pair_run_add,pair_run_cross.
  destruct (pair_run (k/2) (R2 z::tail)) as [ys|] eqn:E.
  2:{ cbn in Hedge; discriminate. }
  rewrite (pair_run_prefix _ _ _ _ E).
  replace (Nat.odd (2*length pre+k)) with (Nat.odd k).
  2:{ rewrite Nat.add_comm,Nat.odd_add_mul_2. reflexivity. }
  destruct (Nat.odd k).
  - cbn in Hedge |- *.
    rewrite (single_step_prefix (add2s pre) ys edge Hedge). reflexivity.
  - inversion Hedge; reflexivity.
Qed.

Lemma flow_delta x edge zin zout replacement emitted:
  flow x edge = Some (zin,zout,(replacement,emitted)) ->
  (ldelta x = 2-2*Z.of_nat (length emitted))%Z.
Proof. destruct x,edge; cbn [flow ldelta]; intros H; try discriminate;
  inversion H; reflexivity. Qed.

Lemma flow_phase x edge zin zout replacement emitted:
  flow x edge = Some (zin,zout,(replacement,emitted)) ->
  phase_ok (replacement::emitted).
Proof. destruct x,edge; cbn [flow]; intros H; try discriminate;
  injection H; intros; subst;
  cbv [phase_ok phase_tail lphase next_phase lvalue];
  repeat split; reflexivity. Qed.

Definition edge_parameters (x:letter) (zin:nat) : list nat :=
  match x with
  | LA => [zin+1]
  | LB => [zin+2]
  | LC => [zin+2;1%nat]
  | LD => [zin+2;2%nat]
  | LE => [zin+2;2%nat;1%nat]
  | LF => []
  | LG => [zin+2;2%nat;2%nat;1%nat]
  | LH => [zin+3;1%nat]
  | LI => [zin+3;2%nat]
  | LJ => [zin+3;2%nat;1%nat]
  | LK => [zin+3;2%nat;2%nat]
  end.

Lemma edge_certificate x edge zin zout replacement emitted oldoff:
  flow x edge = Some (zin,zout,(replacement,emitted)) ->
  oldoff =
    (Z.of_nat (lvalue edge)-3-Z.of_nat zin)%Z ->
  exists ns,
    service (lvalue x+1) (R2 zin::rtail (lphase x)) =
      Some (r1s ns++rtail (next_phase x)) /\
    Parameters
      (oldoff+2*Z.of_nat (length emitted)-2)%Z
      (replacement::emitted) ns /\
    last ns O = zout.
Proof.
  set (ns := edge_parameters x zin).
  destruct x,edge; cbn [flow]; intros H E; try discriminate;
    inversion H; subst; cbn [lvalue lphase rtail] in *;
    exists ns; unfold ns,edge_parameters,Parameters; repeat split.
  all: try reflexivity.
  all: repeat lazymatch goal with
    | |- ParametersN _ _ [] [] => apply ParametersN_nil
    | |- ParametersN _ _ (_::_) (_::_) =>
        eapply ParametersN_cons; [cbn [lvalue ldelta length]; lia|]
    end.
  all: vm_compute; reflexivity.
Qed.

Fixpoint delta_sum (w:list letter) : Z :=
  match w with [] => 0 | x::w => (ldelta x+delta_sum w)%Z end.

Lemma ParametersN_length offset tail w ns:
  ParametersN offset tail w ns -> length ns = length w.
Proof. intros H; induction H; cbn; congruence. Qed.

Lemma ParametersN_app offset tail w1 w2 ns1 ns2:
  ParametersN offset (length w2+tail) w1 ns1 ->
  ParametersN (offset+delta_sum w1)%Z tail w2 ns2 ->
  ParametersN offset tail (w1++w2) (ns1++ns2).
Proof.
  revert offset ns1; induction w1 as [|x w1 IH]; intros offset ns1 H1 H2.
  - inversion H1; subst. cbn [delta_sum app] in H2 |- *.
    applys_eq H2; lia.
  - inversion H1; subst.
    cbn [delta_sum app length] in H2 |- *.
    eapply ParametersN_cons.
    + rewrite app_length. lia.
    + apply IH; [assumption|]. applys_eq H2; lia.
Qed.

Lemma ParametersN_app_inv offset tail w1 w2 ns:
  ParametersN offset tail (w1++w2) ns ->
  exists ns1 ns2,
    ns = ns1++ns2 /\
    ParametersN offset (length w2+tail) w1 ns1 /\
    ParametersN (offset+delta_sum w1)%Z tail w2 ns2.
Proof.
  revert offset ns; induction w1 as [|x w1 IH]; intros offset ns H.
  - exists ([]:list nat),ns. cbn [delta_sum].
    split; [reflexivity|]. split; [constructor|].
    cbn [app] in H. applys_eq H; lia.
  - cbn [app] in H.
    inversion H as [|offset' tail' x' w' n' ns' Heq Htail]; subst.
    destruct (IH _ _ Htail) as [ns1 [ns2 [E [Hpre Hsuf]]]].
    exists (n'::ns1),ns2. subst ns'. repeat split; try reflexivity.
    + cbn [length]. eapply ParametersN_cons.
      * rewrite length_app in Heq. cbn [length] in Heq. applys_eq Heq; lia.
      * exact Hpre.
    + cbn [delta_sum]. applys_eq Hsuf; lia.
Qed.

Lemma ParametersN_shift oldoff newoff t pre ps:
  newoff = (oldoff+2*Z.of_nat t-2)%Z ->
  ParametersN oldoff 1 pre ps ->
  ParametersN newoff (1+t) pre (add2s ps).
Proof.
  intros E H; revert newoff E; induction H; intros newoff E.
  - constructor.
  - cbn [add2s]. eapply ParametersN_cons.
    + cbn [length] in H |- *. zify. lia.
    + apply IHParametersN. lia.
Qed.

Lemma ParametersN_app_known offset tail w1 w2 ns1 ns2:
  length ns1 = length w1 ->
  ParametersN offset tail (w1++w2) (ns1++ns2) ->
  ParametersN offset (length w2+tail) w1 ns1 /\
  ParametersN (offset+delta_sum w1)%Z tail w2 ns2.
Proof.
  revert offset ns1; induction w1 as [|x w1 IH];
    intros offset ns1 E H.
  - destruct ns1; [|cbn in E; discriminate].
    cbn [delta_sum app] in H |- *. split; [constructor|].
    applys_eq H; lia.
  - destruct ns1 as [|n ns1]; [cbn in E; discriminate|].
    cbn [app] in H. inversion H as
      [|offset' tail' x' w' n' ns' Heq Htail]; subst.
    cbn [length] in E. injection E; intros E1.
    destruct (IH _ _ E1 Htail) as [Hpre Hsuf]. split.
    + eapply ParametersN_cons.
      * rewrite length_app in Heq. cbn [length] in Heq |- *.
        applys_eq Heq; lia.
      * exact Hpre.
    + cbn [delta_sum]. applys_eq Hsuf; lia.
Qed.

Lemma local_reset x p pre edge a q ps zin zout replacement emitted:
  phase_ok (x::p::pre++[edge]) ->
  flow x edge = Some (zin,zout,(replacement,emitted)) ->
  Parameters 0 (x::p::pre++[edge])
    (a::q::ps++[zin]) ->
  exists ens,
    Parameters 0 (p::pre++replacement::emitted)
      ((q+2)::add2s ps++ens) /\
    reset_step
      (physical (x::p::pre++[edge]) (a::q::ps++[zin])) =
      Some (physical (p::pre++replacement::emitted)
        ((q+2)::add2s ps++ens)).
Proof.
  intros Hphase Hflow Hparameters.
  unfold Parameters in Hparameters.
  inversion Hparameters as
    [|offset0 tail0 x0 w0 a0 ns0 Heada Hrest]; subst.
  cbn [Z.add_0_l] in Hrest.
  assert (Elen:length (q::ps)=length (p::pre)).
  { pose proof (ParametersN_length _ _ _ _ Hrest) as Eall.
    cbn [length] in Eall. repeat rewrite length_app in Eall.
    cbn [length] in Eall |- *. injection Eall as Eall.
    apply Nat.add_cancel_r in Eall. rewrite Eall. reflexivity. }
  destruct (ParametersN_app_known
    (ldelta x) 0 (p::pre) [edge] (q::ps) [zin] Elen Hrest)
    as [Hprefix Hedge].
  inversion Hedge as
    [|oldoff tail1 edge0 w1 zin0 ns1 Heqedge Hnil]; subst.
  assert (Eold:
    (ldelta x+delta_sum (p::pre))%Z =
    (Z.of_nat (lvalue edge)-3-Z.of_nat zin)%Z).
  { cbn [length] in Heqedge. zify. lia. }
  destruct (edge_certificate _ _ _ _ _ _ _ Hflow Eold)
    as [ens [Hservice [Hedgeout Hlast]]].
  exists ens. split.
  - unfold Parameters.
    change (ParametersN 0 0 ((p::pre)++(replacement::emitted))
      (add2s (q::ps)++ens)).
    eapply ParametersN_app with
      (w1:=p::pre) (w2:=replacement::emitted).
    + cbn [length] in Hprefix |- *.
      rewrite Nat.add_0_r.
      apply (ParametersN_shift (ldelta x) 0 (length emitted)
        (p::pre) (q::ps)).
      * pose proof (flow_delta _ _ _ _ _ _ Hflow). lia.
      * exact Hprefix.
    + pose proof (flow_delta _ _ _ _ _ _ Hflow).
      applys_eq Hedgeout; lia.
  - assert (Ecount:
      a+2 = 2*length (q::ps)+(lvalue x+1)).
    { cbn [length] in Heada. rewrite length_app in Heada.
      cbn [length] in Heada. rewrite Nat.add_0_r in Heada.
      cbn [length] in Elen |- *. zify. lia. }
    pose proof (service_cross (q::ps) zin (rtail (lphase x))
      (lvalue x+1) (r1s ens++rtail (next_phase x)) Hservice)
      as Hcross.
    assert (Ephase:lphase p=next_phase x).
    { cbn [phase_ok phase_tail] in Hphase.
      destruct Hphase as [Ephase _]. exact Ephase. }
    unfold physical,reset_step.
    cbn [map app r1s add2s].
    rewrite Ecount.
    replace (R2 q::map R1 (ps++[zin])++rtail (lphase x)) with
      (marked ((q::ps)++[zin]) (rtail (lphase x))) by reflexivity.
    rewrite Hcross,Ephase. repeat rewrite map_app.
    cbn [r1s add2s]. repeat rewrite app_assoc.
    reflexivity.
Qed.

Inductive symbolic_step : list letter -> list letter -> Prop :=
| symbolic_step_intro x p pre edge zin zout replacement emitted :
    phase_ok (x::p::pre++[edge]) ->
    flow x edge = Some (zin,zout,(replacement,emitted)) ->
    Z.of_nat zin =
      (Z.of_nat (lvalue edge)-3-delta_sum (x::p::pre))%Z ->
    symbolic_step (x::p::pre++[edge])
      (p::pre++replacement::emitted).

Inductive symbolic_step_z : list letter -> nat -> list letter -> nat -> Prop :=
| symbolic_step_z_intro x p pre edge zin zout replacement emitted :
    phase_ok (x::p::pre++[edge]) ->
    flow x edge = Some (zin,zout,(replacement,emitted)) ->
    Z.of_nat zin =
      (Z.of_nat (lvalue edge)-3-delta_sum (x::p::pre))%Z ->
    symbolic_step_z (x::p::pre++[edge]) zin
      (p::pre++replacement::emitted) zout.

Lemma symbolic_step_z_step w z w' z':
  symbolic_step_z w z w' z' -> symbolic_step w w'.
Proof.
  intros H; inversion H as
    [x p pre edge zin zout replacement emitted Hphase Hflow Hedge]; subst.
  econstructor; eassumption.
Qed.

Lemma symbolic_step_sound w w' xs:
  symbolic_step w w' -> represents w xs ->
  exists ys, reset_step xs = Some ys /\ represents w' ys.
Proof.
  intros Hstep [ns [Hparameters ->]].
  inversion Hstep as
    [x p pre edge zin zout replacement emitted Hphase Hflow Hedge]; subst.
  unfold Parameters in Hparameters.
  inversion Hparameters as
    [|offset0 tail0 x0 rest0 a restns Heada Hrest]; subst.
  inversion Hrest as
    [|offset1 tail1 p0 rest1 q tailns Headaq Htail]; subst.
  destruct (ParametersN_app_inv
    (0+ldelta x+ldelta p)%Z 0 pre [edge] tailns Htail)
    as [ps [edge_ns [Ens [Hpre HedgeParameters]]]].
  inversion HedgeParameters as
    [|oldoff tail2 edge0 w0 z ns0 Heqz Hnil]; subst.
  assert (z=zin).
  { apply Nat2Z.inj. cbn [delta_sum length] in Hedge.
    cbn [delta_sum length] in Heqz.
    zify. lia. }
  subst z.
  inversion Hnil; subst.
  destruct (local_reset _ _ _ _ _ _ _ _ _ _ _
    Hphase Hflow Hparameters) as [ens [Hout Ereset]].
  exists (physical (p::pre++replacement::emitted)
    ((q+2)::add2s ps++ens)). split; [exact Ereset|].
  exists ((q+2)::add2s ps++ens). auto.
Qed.

Lemma delta_sum_app xs ys:
  delta_sum (xs++ys) = (delta_sum xs+delta_sum ys)%Z.
Proof.
  induction xs; [reflexivity|].
  cbn [delta_sum app]. rewrite IHxs. lia.
Qed.

Lemma flow_replacement_phase x edge zin zout replacement emitted:
  flow x edge = Some (zin,zout,(replacement,emitted)) ->
  lphase replacement = lphase edge.
Proof. destruct x,edge; cbn [flow]; intros H; try discriminate;
  inversion H; reflexivity. Qed.

Lemma phase_replace_last pre edge replacement emitted:
  phase_ok (pre++[edge]) ->
  lphase replacement = lphase edge ->
  phase_ok (replacement::emitted) ->
  phase_ok (pre++replacement::emitted).
Proof.
  induction pre as [|x pre IH]; intros Hword Ephase Hsuffix.
  - exact Hsuffix.
  - destruct pre as [|y pre].
    + cbn [app phase_ok phase_tail] in Hword |- *.
      destruct Hword as [Hedge _]. split.
      * rewrite Ephase. exact Hedge.
      * exact Hsuffix.
    + cbn [app phase_ok phase_tail] in Hword |- *.
      destruct Hword as [Hxy Hrest]. split; [exact Hxy|].
      apply IH; assumption.
Qed.

Lemma flow_edge_output x p pre edge zin zout replacement emitted:
  flow x edge = Some (zin,zout,(replacement,emitted)) ->
  Z.of_nat zin =
    (Z.of_nat (lvalue edge)-3-delta_sum (x::p::pre))%Z ->
  Z.of_nat zout =
    (Z.of_nat (lvalue (last (replacement::emitted) LA))-3-
      (delta_sum (p::pre)+
       delta_sum (removelast (replacement::emitted))))%Z.
Proof.
  destruct x,edge; cbn [flow]; intros Hflow Hedge; try discriminate;
    inversion Hflow; subst;
    cbn [lvalue ldelta delta_sum last removelast] in Hedge |- *;
    lia.
Qed.

Definition zvalid (front:list letter) (edge:letter) (z:nat) : Prop :=
  phase_ok (front++[edge]) /\
  Z.of_nat z =
    (Z.of_nat (lvalue edge)-3-delta_sum front)%Z.

Lemma symbolic_step_z_valid w zin w' zout:
  symbolic_step_z w zin w' zout ->
  exists front edge,
    w' = front++[edge] /\ zvalid front edge zout.
Proof.
  intros Hstep. destruct Hstep as
    [x p pre edge zin zout replacement emitted Hphase Hflow Hedge].
  assert (Enonempty:replacement::emitted<>[]) by discriminate.
  assert (Esnoc:
    replacement::emitted =
      removelast (replacement::emitted)++
      [last (replacement::emitted) LA]).
  { apply app_removelast_last. exact Enonempty. }
  exists ((p::pre)++removelast (replacement::emitted)),
    (last (replacement::emitted) LA). split.
  { rewrite <-app_assoc,<-Esnoc. reflexivity. }
  split.
  - rewrite <-app_assoc,<-Esnoc.
    apply phase_replace_last with (edge:=edge).
    + cbn [app phase_ok phase_tail] in Hphase.
      destruct Hphase as [_ Hphase]. exact Hphase.
    + apply flow_replacement_phase in Hflow. exact Hflow.
    + apply flow_phase in Hflow. exact Hflow.
  - rewrite delta_sum_app.
    apply flow_edge_output with (x:=x) (edge:=edge) (zin:=zin)
      (replacement:=replacement) (emitted:=emitted); assumption.
Qed.

Fixpoint unsnoc {A} (xs:list A) : option (list A*A) :=
  match xs with
  | [] => None
  | x::xs =>
      match unsnoc xs with
      | None => Some ([],x)
      | Some (pre,edge) => Some (x::pre,edge)
      end
  end.

Lemma unsnoc_sound {A} (xs pre:list A) edge:
  unsnoc xs = Some (pre,edge) -> xs=pre++[edge].
Proof.
  revert pre edge; induction xs as [|x xs IH]; intros pre edge H;
    [discriminate|].
  cbn [unsnoc] in H. destruct (unsnoc xs) as [[rest last]|] eqn:E.
  - inversion H; subst. cbn [app]. f_equal. apply IH. reflexivity.
  - inversion H; subst. destruct xs as [|y ys]; [reflexivity|].
    change
      (match unsnoc ys with
       | None => Some ([],y)
       | Some (rest,last) => Some (y::rest,last)
       end = None) in E.
    destruct (unsnoc ys) as [[rest last]|]; discriminate.
Qed.

Lemma unsnoc_complete {A} (pre:list A) edge:
  unsnoc (pre++[edge]) = Some (pre,edge).
Proof.
  induction pre as [|x pre IH]; [reflexivity|].
  cbn [app unsnoc]. rewrite IH. reflexivity.
Qed.

Record zconfig := {
  zfront : list letter;
  zedge : letter;
  zparameter : nat;
}.

Definition zword (s:zconfig) := zfront s++[zedge s].

Definition zstep (s:zconfig) : option zconfig :=
  match zfront s with
  | x::p::pre =>
      match flow x (zedge s) with
      | Some (zin,zout,(replacement,emitted)) =>
          if Nat.eqb (zparameter s) zin then
            match unsnoc ((p::pre)++replacement::emitted) with
            | Some (front,edge) =>
                Some {| zfront:=front; zedge:=edge; zparameter:=zout |}
            | None => None
            end
          else None
      | None => None
      end
  | _ => None
  end.

Lemma snoc_injective {A} (xs ys:list A) x y:
  xs++[x] = ys++[y] -> xs=ys /\ x=y.
Proof. apply app_inj_tail. Qed.

Lemma zstep_sound s s':
  zvalid (zfront s) (zedge s) (zparameter s) ->
  zstep s = Some s' ->
  symbolic_step_z (zword s) (zparameter s)
    (zword s') (zparameter s') /\
  zvalid (zfront s') (zedge s') (zparameter s').
Proof.
  destruct s as [front edge z]. destruct s' as [front' edge' z'].
  cbn [zfront zedge zparameter zword zstep].
  destruct front as [|x [|p pre]]; intros Hvalid Hstep; try discriminate.
  cbn [zstep zfront zedge zparameter] in Hstep.
  destruct (flow x edge) as [result|] eqn:Hflow; [|discriminate].
  destruct result as [[zin zout] [replacement emitted]].
  destruct (Nat.eqb z zin) eqn:Ez; [|discriminate].
  destruct (unsnoc ((p::pre)++replacement::emitted))
    as [[outfront outedge]|] eqn:Eunsnoc; [|discriminate].
  inversion Hstep; subst outfront outedge z'.
  apply Nat.eqb_eq in Ez. subst z.
  destruct Hvalid as [Hphase Hedge].
  assert (Hsymbolic:symbolic_step_z
    ((x::p::pre)++[edge]) zin
    ((p::pre)++replacement::emitted) zout).
  { constructor; assumption. }
  assert (Eword:
    (p::pre)++replacement::emitted = front'++[edge']).
  { apply unsnoc_sound in Eunsnoc. exact Eunsnoc. }
  split.
  - unfold zword. cbn [zfront zedge zparameter].
    rewrite <-Eword. exact Hsymbolic.
  - destruct (symbolic_step_z_valid _ _ _ _ Hsymbolic)
      as [canonical [last' [Ecanonical Hcanonical]]].
    destruct (snoc_injective _ _ _ _ (eq_trans (eq_sym Eword) Ecanonical))
      as [-> ->]. exact Hcanonical.
Qed.

Inductive symbolic_run : nat -> list letter -> list letter -> Prop :=
| symbolic_run_refl w : symbolic_run 0 w w
| symbolic_run_cons n w1 w2 w3 :
    symbolic_step w1 w2 -> symbolic_run n w2 w3 ->
    symbolic_run (S n) w1 w3.

Fixpoint zrun (n:nat) (s:zconfig) : option zconfig :=
  match n with
  | O => Some s
  | S n =>
      match zstep s with
      | Some s' => zrun n s'
      | None => None
      end
  end.

Lemma zrun_sound n s s':
  zvalid (zfront s) (zedge s) (zparameter s) ->
  zrun n s = Some s' ->
  symbolic_run n (zword s) (zword s') /\
  zvalid (zfront s') (zedge s') (zparameter s').
Proof.
  revert s; induction n; intros s Hvalid Hrun.
  - inversion Hrun; subst. split; [constructor|exact Hvalid].
  - cbn [zrun] in Hrun.
    destruct (zstep s) as [next|] eqn:Estep; [|discriminate].
    destruct (zstep_sound _ _ Hvalid Estep) as [Hone Hnext].
    destruct (IHn _ Hnext Hrun) as [Hmore Hfinal].
    split; [econstructor; [apply symbolic_step_z_step in Hone; exact Hone|exact Hmore]
           |exact Hfinal].
Qed.

Lemma symbolic_run_sound k w w' xs:
  symbolic_run k w w' -> represents w xs ->
  exists ys, rconfig xs -->* rconfig ys /\ represents w' ys.
Proof.
  intros Hrun; revert xs; induction Hrun; intros xs Hrep.
  - exists xs. split; [apply evstep_refl|exact Hrep].
  - destruct (symbolic_step_sound _ _ _ H Hrep)
      as [ys [Ereset Hrep']].
    destruct (IHHrun _ Hrep') as [zs [Hsteps Hfinal]].
    exists zs. split; [|exact Hfinal].
    eapply evstep_trans; [|exact Hsteps].
    apply progress_evstep,reset_step_sound,Ereset.
Qed.

Definition zgen (s:zconfig) := zrun (length (zword s)) s.

Fixpoint zgens (n:nat) (s:zconfig) : option zconfig :=
  match n with
  | O => Some s
  | S n =>
      match zgen s with
      | Some s' => zgens n s'
      | None => None
      end
  end.

Inductive symbolic_generations : nat -> list letter -> list letter -> Prop :=
| symbolic_generations_refl w : symbolic_generations 0 w w
| symbolic_generations_cons n w1 w2 w3 :
    symbolic_run (length w1) w1 w2 ->
    symbolic_generations n w2 w3 ->
    symbolic_generations (S n) w1 w3.

Lemma zgens_sound n s s':
  zvalid (zfront s) (zedge s) (zparameter s) ->
  zgens n s = Some s' ->
  symbolic_generations n (zword s) (zword s') /\
  zvalid (zfront s') (zedge s') (zparameter s').
Proof.
  revert s; induction n; intros s Hvalid Hrun.
  - inversion Hrun; subst. split; [constructor|exact Hvalid].
  - cbn [zgens] in Hrun.
    destruct (zgen s) as [next|] eqn:Egen; [|discriminate].
    destruct (zrun_sound _ _ _ Hvalid Egen) as [Hone Hnext].
    destruct (IHn _ Hnext Hrun) as [Hmore Hfinal].
    split; [econstructor; eassumption|exact Hfinal].
Qed.

Lemma symbolic_generations_sound n w w' xs:
  symbolic_generations n w w' -> represents w xs ->
  exists ys, rconfig xs -->* rconfig ys /\ represents w' ys.
Proof.
  intros Hgens; revert xs; induction Hgens; intros xs Hrep.
  - exists xs. split; [apply evstep_refl|exact Hrep].
  - destruct (symbolic_run_sound _ _ _ _ H Hrep)
      as [ys [Hsteps Hrep']].
    destruct (IHHgens _ Hrep') as [zs [Hmore Hfinal]].
    exists zs. split; [eapply evstep_trans; eassumption|exact Hfinal].
Qed.

Definition generation0 : zconfig :=
  {| zfront:=[LD;LI;LH]; zedge:=LE; zparameter:=1 |}.

Definition boundary0 : zconfig :=
  {| zfront:=[LH;LE;LC;LB;LI;LH;LE;LC;LB;LI;
               LH;LE;LE;LC;LC;LA;LD;LJ;LC];
     zedge:=LB; zparameter:=2 |}.

Lemma generation0_valid:
  zvalid (zfront generation0) (zedge generation0)
    (zparameter generation0).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma generation0_to_boundary0:
  zgens 17 generation0 = Some boundary0.
Proof. vm_compute. reflexivity. Qed.

Lemma generation0_boundary_run:
  symbolic_generations 17 (zword generation0) (zword boundary0).
Proof.
  apply (proj1 (zgens_sound _ _ _ generation0_valid
    generation0_to_boundary0)).
Qed.

Definition initial_words := [R1 3;R1 2;R1 2;R1 1].
Definition generation0_words := [R1 6;R1 5;R1 2;R1 1].

Lemma generation0_represents:
  represents (zword generation0) generation0_words.
Proof.
  exists ([6%nat;5%nat;2%nat;1%nat]:list nat). split; [|reflexivity].
  unfold Parameters. repeat constructor; reflexivity.
Qed.

Lemma init_to_generation0:
  c0 -->* rconfig generation0_words.
Proof.
  eapply evstep_trans; [exact init|].
  change (rconfig initial_words -->* rconfig generation0_words).
  eapply evstep_trans.
  { apply progress_evstep,reset_step_sound. reflexivity. }
  eapply evstep_trans.
  { apply progress_evstep,reset_step_sound. reflexivity. }
  apply progress_evstep,reset_step_sound. reflexivity.
Qed.

Lemma init_to_boundary0:
  exists xs,
    c0 -->* rconfig xs /\ represents (zword boundary0) xs.
Proof.
  destruct (symbolic_generations_sound _ _ _ _
    generation0_boundary_run generation0_represents)
    as [xs [Hrun Hrep]].
  exists xs. split.
  - eapply evstep_trans; [exact init_to_generation0|exact Hrun].
  - exact Hrep.
Qed.
Import ListNotations.
Inductive bitpair := BP10 | BP01 | BP00.

Definition hblock (b:bitpair) : list letter :=
  match b with
  | BP10 => [LH;LE;LB;LI;LI]
  | BP01 => [LH;LE;LC;LB;LI]
  | BP00 => [LH;LE;LC;LB;LI;LI]
  end.

Definition ablock (b:bitpair) : list letter :=
  match b with
  | BP10 => [LA;LD;LJ;LC;LC]
  | BP01 => [LA;LD;LI;LJ;LC]
  | BP00 => [LA;LD;LI;LJ;LC;LC]
  end.

Definition hnext (x y:bitpair) : Prop :=
  match x,y with
  | BP10,BP10 | BP10,BP01 | BP01,BP01 | BP01,BP00 | BP00,BP10 => True
  | _,_ => False
  end.

Definition anext (x y:bitpair) : Prop :=
  match x,y with
  | BP10,BP10 | BP10,BP01 | BP01,BP01 | BP01,BP00 | BP00,BP10 => True
  | _,_ => False
  end.

Fixpoint chain (R:bitpair->bitpair->Prop) (xs:list bitpair) : Prop :=
  match xs with
  | [] => True
  | x::rest =>
      match rest with
      | [] => True
      | y::_ => R x y /\ chain R rest
      end
  end.

Inductive block_mode :=
| M0
| M1 (x:bitpair)
| M2 (first last:bitpair).

Definition mode_matches (m:block_mode) (xs:list bitpair) : Prop :=
  match m with
  | M0 => xs=[]
  | M1 x => xs=[x]
  | M2 first last =>
      exists middle, xs=first::middle++[last]
  end.

Fixpoint blocks (f:bitpair->list letter) (xs:list bitpair) : list letter :=
  match xs with
  | [] => []
  | x::xs => f x++blocks f xs
  end.

Record boundary_context := BC {
  bc_generations : nat;
  bc_edge_parameter : nat;
  bc_hmode : block_mode;
  bc_bridge : list letter;
  bc_amode : block_mode;
  bc_suffix : list letter;
}.

Definition context_word c hs as_ :=
  blocks hblock hs++bc_bridge c++blocks ablock as_++bc_suffix c.

Fixpoint letters_eqb (xs ys:list letter) : bool :=
  match xs,ys with
  | [],[] => true
  | x::xs,y::ys => andb (letter_eqb x y) (letters_eqb xs ys)
  | _,_ => false
  end.

Definition parse_hblock xs : option bitpair :=
  if letters_eqb xs (hblock BP10) then Some BP10 else
  if letters_eqb xs (hblock BP01) then Some BP01 else
  if letters_eqb xs (hblock BP00) then Some BP00 else None.

Definition parse_ablock xs : option bitpair :=
  if letters_eqb xs (ablock BP10) then Some BP10 else
  if letters_eqb xs (ablock BP01) then Some BP01 else
  if letters_eqb xs (ablock BP00) then Some BP00 else None.

Definition hnextb x y :=
  match x,y with
  | BP10,BP10 | BP10,BP01 | BP01,BP01 | BP01,BP00 | BP00,BP10 => true
  | _,_ => false
  end.

Definition anextb x y :=
  match x,y with
  | BP10,BP10 | BP10,BP01 | BP01,BP01 | BP01,BP00 | BP00,BP10 => true
  | _,_ => false
  end.

Definition mode_add (next:bitpair->bitpair->bool)
  (m:block_mode) (x:bitpair) : option block_mode :=
  match m with
  | M0 => Some (M1 x)
  | M1 first => if next first x then Some (M2 first x) else None
  | M2 first last => if next last x then Some (M2 first x) else None
  end.

Inductive parser_stage := PStart | PHZone | PAZone.

Record word_parser := WP {
  wp_stage : parser_stage;
  wp_current : list letter;
  wp_hmode : block_mode;
  wp_bridge : list letter;
  wp_amode : block_mode
}.

Definition parser_initial := WP PStart [] M0 [] M0.

Definition parser_feed (p:word_parser) (x:letter) : option word_parser :=
  match wp_stage p with
  | PStart =>
      if letter_eqb x LH then Some (WP PHZone [LH] M0 [] M0)
      else None
  | PHZone =>
      if letter_eqb x LH then
        match parse_hblock (wp_current p) with
        | Some b =>
            match mode_add hnextb (wp_hmode p) b with
            | Some mode => Some (WP PHZone [LH] mode [] M0)
            | None => None
            end
        | None => None
        end
      else if letter_eqb x LA then
        Some (WP PAZone [LA] (wp_hmode p) (wp_current p) M0)
      else Some (WP PHZone (wp_current p++[x]) (wp_hmode p) [] M0)
  | PAZone =>
      if letter_eqb x LH then None
      else if letter_eqb x LA then
        match parse_ablock (wp_current p) with
        | Some b =>
            match mode_add anextb (wp_amode p) b with
            | Some mode =>
                Some (WP PAZone [LA] (wp_hmode p) (wp_bridge p) mode)
            | None => None
            end
        | None => None
        end
      else Some (WP PAZone (wp_current p++[x])
        (wp_hmode p) (wp_bridge p) (wp_amode p))
  end.

Record raw_context := RC {
  rc_hmode : block_mode;
  rc_bridge : list letter;
  rc_amode : block_mode;
  rc_suffix : list letter
}.

Definition parser_finish p : option raw_context :=
  match wp_stage p with
  | PAZone => Some (RC (wp_hmode p) (wp_bridge p)
                      (wp_amode p) (wp_current p))
  | _ => None
  end.

Definition decode_bitpair (n:nat) :=
  if Nat.eqb n 0%nat then BP10 else
  if Nat.eqb n 1%nat then BP01 else BP00.

Definition decode_amode (n:nat) :=
  nth n [M0;M1 BP01;M1 BP10;M1 BP00;
    M2 BP01 BP01;M2 BP01 BP10;M2 BP01 BP00;
    M2 BP10 BP01;M2 BP10 BP10;M2 BP10 BP00;
    M2 BP00 BP01;M2 BP00 BP10;M2 BP00 BP00] M0.

Definition odd_bridges :=
  [[LH;LG];[LH;LE;LE;LC;LC];[LH;LG;LC];[LH;LE;LD;LJ;LC;LC];
   [LH;LE;LD;LI;LJ;LC];[LH;LE;LD;LJ;LC];[LH;LE;LE;LC];
   [LH;LE;LD;LI;LJ;LC;LC]].

Definition decode_context '(first,last,bridge,amode,suffix) :=
  BC (if Nat.eqb first 0 then 8 else 6) 2
    (M2 (decode_bitpair first) (decode_bitpair last))
    (nth bridge odd_bridges []) (decode_amode amode)
    (if Nat.eqb suffix 0 then [LA;LD;LJ;LC;LB]
     else [LA;LD;LI;LJ;LC;LB]).

Local Open Scope nat_scope.

Definition context_codes : list (nat*nat*nat*nat*nat) := [
  (0,0,4,1,1); (0,0,4,3,0); (0,0,4,4,1); (0,0,4,6,0); (0,0,4,5,0);
  (0,0,4,10,1); (0,0,4,12,0); (0,0,4,11,0); (0,0,7,7,1); (0,0,7,9,0);
  (0,0,7,8,0); (0,0,3,4,1); (0,0,3,6,0); (0,0,3,5,0); (0,0,3,7,1);
  (0,0,3,9,0); (0,0,3,8,0); (0,0,0,4,1); (0,0,0,6,0); (0,0,0,5,0);
  (0,0,0,7,1); (0,0,0,9,0); (0,0,0,8,0); (0,1,5,0,1); (0,1,5,4,1);
  (0,1,5,6,0); (0,1,5,5,0); (0,1,5,10,1); (0,1,5,12,0); (0,1,5,11,0);
  (0,1,3,2,0); (0,1,3,7,1); (0,1,3,9,0); (0,1,3,8,0); (0,1,6,4,1);
  (0,1,6,6,0); (0,1,6,5,0); (0,1,6,10,1); (0,1,6,12,0); (0,1,6,11,0);
  (0,1,1,4,1); (0,1,1,6,0); (0,1,1,5,0); (0,1,1,7,1); (0,1,1,9,0);
  (0,1,1,8,0); (0,2,0,3,0); (0,2,0,4,1); (0,2,0,6,0); (0,2,0,5,0);
  (0,2,0,10,1); (0,2,0,12,0); (0,2,0,11,0); (0,2,2,1,1); (0,2,2,4,1);
  (0,2,2,6,0); (0,2,2,5,0); (0,2,2,7,1); (0,2,2,9,0); (0,2,2,8,0);
  (1,0,4,3,0); (1,0,4,6,0); (1,0,4,5,0); (1,0,4,12,0); (1,0,4,11,0);
  (1,0,7,9,0); (1,0,7,8,0); (1,0,3,6,0); (1,0,3,5,0); (1,0,3,9,0);
  (1,0,3,8,0); (1,0,0,6,0); (1,0,0,5,0); (1,0,0,9,0); (1,0,0,8,0);
  (1,1,5,6,0); (1,1,5,5,0); (1,1,5,12,0); (1,1,5,11,0); (1,1,3,2,0);
  (1,1,3,9,0); (1,1,3,8,0); (1,1,6,6,0); (1,1,6,5,0); (1,1,6,12,0);
  (1,1,6,11,0); (1,1,1,0,0); (1,1,1,6,0); (1,1,1,5,0); (1,1,1,9,0);
  (1,1,1,8,0); (1,2,0,3,0); (1,2,0,6,0); (1,2,0,5,0); (1,2,0,12,0);
  (1,2,0,11,0); (1,2,2,6,0); (1,2,2,5,0); (1,2,2,9,0); (1,2,2,8,0)
].

Definition all_contexts := map decode_context context_codes.

(* A streaming presentation of one [zgen].  [sm_final] is the input
   symbol which is consumed last, [sm_edge] is the current right edge, and
   the list returned by [sm_feed] consists exactly of the newly stable
   output symbols (the new edge is retained in the machine). *)
Record smachine := SM {
  sm_final : letter;
  sm_edge : letter;
  sm_started : bool;
  sm_parameter : nat
}.

Definition sm_initial edge z := SM edge edge false z.

Definition sm_feed (m:smachine) (x:letter)
  : option (smachine*list letter) :=
  match flow x (sm_edge m) with
  | Some (zin,zout,(replacement,emitted)) =>
      if Nat.eqb (sm_parameter m) zin then
        match emitted with
        | [] =>
            Some (SM
              (if sm_started m then sm_final m else replacement)
              replacement (sm_started m) zout, [])
        | y::ys =>
            let stable :=
              (if sm_started m then [replacement] else []) ++
              removelast (y::ys) in
            Some (SM
              (if sm_started m then sm_final m else replacement)
              (last (y::ys) y) true zout, stable)
        end
      else None
  | None => None
  end.

Fixpoint sm_fold (xs:list letter) (m:smachine)
  : option (smachine*list letter) :=
  match xs with
  | [] => Some (m,[])
  | x::xs =>
      match sm_feed m x with
      | None => None
      | Some (m',out) =>
          match sm_fold xs m' with
          | None => None
          | Some (m'',more) => Some (m'',out++more)
          end
      end
  end.

Definition sm_close (m:smachine) : option (smachine*list letter) :=
  match sm_feed m (sm_final m) with
  | None => None
  | Some (m',out) => Some (m',out++[sm_edge m'])
  end.

Definition sm_generation (s:zconfig) : option zconfig :=
  match sm_fold (zfront s) (sm_initial (zedge s) (zparameter s)) with
  | None => None
  | Some (m,out) =>
      if sm_started m then
        match out with
        | [] => None
        | _::_ =>
            match sm_close m with
            | None => None
            | Some (m',tail) =>
                match unsnoc (out++tail) with
                | None => None
                | Some (front,edge) =>
                    Some {| zfront:=front; zedge:=edge;
                            zparameter:=sm_parameter m' |}
                end
            end
        end
      else None
  end.

Definition sm_inv (m:smachine) : Prop :=
  sm_started m = false -> sm_edge m = sm_final m.

Definition sm_config (rest stable:list letter) (m:smachine) : zconfig :=
  if sm_started m then
    {| zfront:=rest++sm_final m::stable;
       zedge:=sm_edge m; zparameter:=sm_parameter m |}
  else
    {| zfront:=rest; zedge:=sm_final m;
       zparameter:=sm_parameter m |}.

Lemma sm_initial_inv edge z: sm_inv (sm_initial edge z).
Proof. unfold sm_inv,sm_initial; cbn. reflexivity. Qed.

Lemma sm_feed_inv m x m' out:
  sm_inv m -> sm_feed m x = Some (m',out) -> sm_inv m'.
Proof.
  destruct m as [final edge started parameter].
  destruct m' as [final' edge' started' parameter'].
  unfold sm_inv,sm_feed; cbn [sm_started sm_edge sm_final sm_parameter].
  destruct (flow x edge) as [[[zin zout] [replacement emitted]]|]
    eqn:Eflow; [|discriminate].
  destruct (Nat.eqb parameter zin); [|discriminate].
  destruct emitted as [|y ys]; cbn.
  - destruct started; cbn; intros H E; inversion E; subst; cbn; congruence.
  - intros H E. inversion E; subst. discriminate.
Qed.

Lemma unsnoc_app_nonempty {A} (prefix:list A) y ys:
  unsnoc (prefix++y::ys) =
  Some (prefix++removelast (y::ys),last (y::ys) y).
Proof.
  assert (El:y::ys = removelast (y::ys)++[last (y::ys) y]).
  { apply app_removelast_last. discriminate. }
  rewrite El at 1. rewrite app_assoc. apply unsnoc_complete.
Qed.

Lemma snoc_then {A} (xs:list A) x ys:
  (xs++[x])++ys = xs++x::ys.
Proof. induction xs; cbn; congruence. Qed.

Lemma sm_feed_step_false x p pre stable m m' out:
  sm_started m = false -> sm_inv m ->
  sm_feed m x = Some (m',out) ->
  zstep (sm_config (x::p::pre) stable m) =
    Some (sm_config (p::pre) out m').
Proof.
  destruct m as [final edge started parameter].
  cbn [sm_started]. intros Efalse Hinv Hfeed; subst started.
  unfold sm_inv in *. cbn [sm_started sm_edge sm_final] in *.
  specialize (Hinv eq_refl). subst edge.
  unfold sm_feed in Hfeed.
  cbn [sm_edge sm_parameter sm_started sm_final] in Hfeed.
  destruct (flow x final) as [[[zin zout] [replacement emitted]]|]
    eqn:Eflow.
  2:{ discriminate Hfeed. }
  destruct (Nat.eqb parameter zin) eqn:Ezin.
  2:{ discriminate Hfeed. }
  destruct emitted as [|y ys].
  - inversion Hfeed; subst. cbn [sm_config sm_started sm_final sm_parameter].
    unfold zstep. cbn [zfront zedge zparameter].
    rewrite Eflow,Ezin,unsnoc_complete. reflexivity.
  - inversion Hfeed; subst. cbn [sm_config sm_started sm_final sm_parameter].
    unfold zstep. cbn [zfront zedge zparameter].
    rewrite Eflow,Ezin.
    assert (Eu:unsnoc ((p::pre)++replacement::y::ys) =
      Some ((p::pre)++replacement::removelast (y::ys),last (y::ys) y)).
    { rewrite <- (snoc_then (p::pre) replacement (y::ys)) at 1.
      rewrite unsnoc_app_nonempty,snoc_then. reflexivity. }
    rewrite Eu. cbn. reflexivity.
Qed.

Lemma sm_feed_step_true_raw x p pre m m' out:
  sm_started m = true ->
  sm_feed m x = Some (m',out) ->
  zstep {| zfront:=x::p::pre; zedge:=sm_edge m;
           zparameter:=sm_parameter m |} =
    Some {| zfront:=(p::pre)++out; zedge:=sm_edge m';
            zparameter:=sm_parameter m' |}.
Proof.
  destruct m as [final edge started parameter].
  cbn [sm_started]. intros Etrue Hfeed; subst started.
  destruct x,edge;
    cbn [sm_feed flow sm_edge sm_parameter sm_started sm_final] in Hfeed;
    try discriminate.
  all: repeat lazymatch type of Hfeed with
    | context [Nat.eqb ?z ?n] =>
        destruct (Nat.eqb z n) eqn:?; [|discriminate]
    end.
  all: inversion Hfeed; subst;
    cbn [zstep flow zfront zedge zparameter unsnoc sm_edge sm_parameter];
    repeat lazymatch goal with
      | H: Nat.eqb _ _ = true |- _ => rewrite H
    end;
    cbn [unsnoc];
    try rewrite unsnoc_app_nonempty;
    try rewrite unsnoc_complete;
    repeat rewrite app_nil_r; reflexivity.
Qed.

Lemma sm_feed_step_true_raw_nonempty x tail m m' out:
  tail<>[] -> sm_started m = true ->
  sm_feed m x = Some (m',out) ->
  zstep {| zfront:=x::tail; zedge:=sm_edge m;
           zparameter:=sm_parameter m |} =
    Some {| zfront:=tail++out; zedge:=sm_edge m';
            zparameter:=sm_parameter m' |}.
Proof.
  intros Hnonempty Hstarted Hfeed.
  destruct tail as [|p pre]; [contradiction|].
  apply sm_feed_step_true_raw; assumption.
Qed.

Lemma sm_feed_step_true x rest stable m m' out:
  sm_started m = true ->
  sm_feed m x = Some (m',out) ->
  zstep (sm_config (x::rest) stable m) =
    Some (sm_config rest (stable++out) m').
Proof.
  intros Hstarted Hfeed.
  assert (Hfields:
    sm_started m'=true /\ sm_final m'=sm_final m).
  { destruct m as [final edge started parameter].
    cbn in Hstarted. subst started.
    unfold sm_feed in Hfeed.
    cbn [sm_edge sm_parameter sm_started sm_final] in Hfeed.
    destruct (flow x edge) as [[[zin zout] [replacement emitted]]|];
      [|discriminate].
    destruct (Nat.eqb parameter zin); [|discriminate].
    destruct emitted; inversion Hfeed; auto. }
  destruct Hfields as [Hstarted' Hfinal].
  unfold sm_config. rewrite Hstarted,Hstarted'.
  cbv beta iota zeta delta [zfront zedge zparameter].
  rewrite Hfinal.
  cbn [app].
  assert (Hnonempty:rest++sm_final m::stable<>[]).
  { intros Hnil. apply app_eq_nil in Hnil as [_ Hnil]. discriminate. }
  pose proof (sm_feed_step_true_raw_nonempty x
    (rest++sm_final m::stable) m m' out
    Hnonempty Hstarted Hfeed) as Hraw.
  applys_eq Hraw.
  assert (Elist:
    rest++(sm_final m::(stable++out)) =
    (rest++(sm_final m::stable))++out).
  { change (rest++((sm_final m::stable)++out) =
      (rest++(sm_final m::stable))++out).
    apply app_assoc. }
  rewrite Elist. reflexivity.
Qed.

Definition sm_stable (m:smachine) (stable:list letter) : Prop :=
  sm_started m = false -> stable=[].

Lemma sm_initial_stable edge z: sm_stable (sm_initial edge z) [].
Proof. unfold sm_stable,sm_initial; cbn. reflexivity. Qed.

Lemma sm_feed_stable m x m' out stable:
  sm_stable m stable ->
  sm_feed m x = Some (m',out) ->
  sm_stable m' (stable++out).
Proof.
  destruct m as [final edge started parameter].
  unfold sm_stable,sm_feed.
  cbn [sm_started sm_edge sm_parameter sm_final].
  destruct (flow x edge) as [[[zin zout] [replacement emitted]]|];
    [|discriminate].
  destruct (Nat.eqb parameter zin); [|discriminate].
  destruct emitted as [|y ys].
  - destruct started.
    + cbn. intros Hstable Hfeed Hfalse.
      inversion Hfeed; subst. discriminate.
    + cbn. intros Hstable Hfeed Hfalse.
      inversion Hfeed; subst. rewrite app_nil_r. apply Hstable. reflexivity.
  - intros Hstable Hfeed Hfalse. inversion Hfeed; subst. discriminate.
Qed.

Fixpoint sm_fold_safe (xs:list letter) (m:smachine) : Prop :=
  match xs with
  | [] => True
  | x::xs =>
      match sm_feed m x with
      | None => False
      | Some (m',_) =>
          (sm_started m=true \/ xs<>[]) /\ sm_fold_safe xs m'
      end
  end.

Lemma sm_fold_sound xs m m' out stable:
  sm_inv m -> sm_stable m stable ->
  sm_fold_safe xs m ->
  sm_fold xs m = Some (m',out) ->
  zrun (length xs) (sm_config xs stable m) =
    Some (sm_config [] (stable++out) m').
Proof.
  revert m m' out stable.
  induction xs as [|x xs IH]; intros m m' out stable
    Hinv Hstable Hsafe Hfold.
  - inversion Hfold; subst. cbn [zrun]. rewrite app_nil_r. reflexivity.
  - cbn [sm_fold sm_fold_safe] in Hfold,Hsafe.
    destruct (sm_feed m x) as [[next first]|] eqn:Efeed;
      [|contradiction].
    destruct (sm_fold xs next) as [[last more]|] eqn:Efold;
      [|discriminate].
    inversion Hfold; subst. destruct Hsafe as [Hhead Htail].
    cbn [length zrun].
    assert (Estep:
      zstep (sm_config (x::xs) stable m) =
      Some (sm_config xs (stable++first) next)).
    { destruct (sm_started m) eqn:Estarted.
      - apply sm_feed_step_true; assumption.
      - destruct Hhead as [Hbad|Hnonempty]; [discriminate|].
        destruct xs as [|p pre]; [contradiction|].
        pose proof (sm_feed_step_false x p pre stable m next first
          Estarted Hinv Efeed) as Hfalse.
        assert (Estable:stable=[]). { apply Hstable,Estarted. }
        subst stable. cbn [app] in Hfalse |- *. exact Hfalse. }
    rewrite Estep.
    pose proof (IH next m' more (stable++first)
      (sm_feed_inv _ _ _ _ Hinv Efeed)
      (sm_feed_stable _ _ _ _ _ Hstable Efeed)
      Htail Efold) as Hmore.
    assert (Eout:
      (stable++first)++more = stable++(first++more)) by
      (symmetry; apply app_assoc).
    rewrite Eout in Hmore. exact Hmore.
Qed.

Lemma sm_close_core_sound m m' out stable:
  sm_started m=true -> stable<>[] ->
  sm_feed m (sm_final m) = Some (m',out) ->
  zstep (sm_config [] stable m) =
    Some {| zfront:=stable++out; zedge:=sm_edge m';
            zparameter:=sm_parameter m' |}.
Proof.
  intros Hstarted Hstable Hfeed.
  unfold sm_config. rewrite Hstarted.
  destruct stable as [|p pre]; [contradiction|].
  cbn [app].
  applys_eq (sm_feed_step_true_raw
    (sm_final m) p pre m m' out Hstarted Hfeed).
Qed.

Lemma zrun_add a b s:
  zrun (a+b) s =
  match zrun a s with
  | Some s' => zrun b s'
  | None => None
  end.
Proof.
  revert s; induction a; intros s; [reflexivity|].
  cbn [Nat.add zrun]. destruct (zstep s) as [next|];
    [apply IHa|reflexivity].
Qed.

Lemma sm_generation_sound s s':
  sm_fold_safe (zfront s) (sm_initial (zedge s) (zparameter s)) ->
  sm_generation s = Some s' ->
  zgen s = Some s'.
Proof.
  unfold sm_generation.
  destruct (sm_fold (zfront s)
    (sm_initial (zedge s) (zparameter s))) as [[m stable]|] eqn:Efold;
    [|discriminate].
  destruct (sm_started m) eqn:Estarted; [|discriminate].
  destruct stable as [|u stable]; [discriminate|].
  destruct (sm_close m) as [[m' tail]|] eqn:Eclose;
    [|discriminate].
  destruct (unsnoc ((u::stable)++tail)) as [[front edge]|] eqn:Eunsnoc;
    [|discriminate].
  intros Hsafe Hresult. inversion Hresult; subst s'.
  unfold sm_close in Eclose.
  destruct (sm_feed m (sm_final m)) as [[closed core]|] eqn:Ecore;
    [|discriminate].
  inversion Eclose; subst closed tail.
  assert (Eunsnoc':
    unsnoc ((u::stable)++core++[sm_edge m']) =
    Some ((u::stable)++core,sm_edge m')).
  { rewrite app_assoc. apply unsnoc_complete. }
  rewrite Eunsnoc' in Eunsnoc. inversion Eunsnoc; subst front edge.
  pose proof (sm_fold_sound (zfront s)
    (sm_initial (zedge s) (zparameter s)) m (u::stable) []
    (sm_initial_inv _ _) (sm_initial_stable _ _)
    Hsafe Efold) as Hfoldrun.
  assert (Einitial:
    sm_config (zfront s) []
      (sm_initial (zedge s) (zparameter s)) = s).
  { destruct s. reflexivity. }
  rewrite Einitial in Hfoldrun.
  pose proof (sm_close_core_sound m m' core (u::stable)
    Estarted ltac:(discriminate) Ecore) as Hcloserun.
  unfold zgen,zword. rewrite app_length. cbn [length].
  rewrite zrun_add,Hfoldrun.
  change (zrun 1 (sm_config [] (u::stable) m) =
    Some {| zfront:=u::stable++core; zedge:=sm_edge m';
            zparameter:=sm_parameter m' |}).
  change
    ((match zstep (sm_config [] (u::stable) m) with
      | Some next => Some next
      | None => None
      end) = Some {| zfront:=u::stable++core; zedge:=sm_edge m';
                     zparameter:=sm_parameter m' |}).
  rewrite Hcloserun. reflexivity.
Qed.

Record slayer := SL {
  sl_guess : letter;
  sl_guess_parameter : nat;
  sl_machine : smachine;
  sl_buffer : option letter;
  sl_last_safe : bool;
  sl_output_nonempty : bool
}.

Definition sl_initial '(edge,z) :=
  SL edge z (sm_initial edge z) None false false.

Fixpoint sl_initials (guesses:list (letter*nat)) : list slayer :=
  match guesses with
  | [] => []
  | guess::guesses => sl_initial guess::sl_initials guesses
  end.

Definition nonemptyb {A} (xs:list A) : bool :=
  match xs with [] => false | _::_ => true end.

Section Pipeline.
Context {sink:Type} (sink_feed:sink->letter->option sink).

Fixpoint pipeline_sink_run (xs:list letter) (s:sink) : option sink :=
  match xs with
  | [] => Some s
  | x::xs =>
      match sink_feed s x with
      | None => None
      | Some s' => pipeline_sink_run xs s'
      end
  end.

Definition sl_feed (layer:slayer) (symbol:letter)
  : option (slayer*list letter) :=
  match sl_buffer layer with
  | None =>
      Some (SL (sl_guess layer) (sl_guess_parameter layer)
        (sl_machine layer) (Some symbol) (sl_last_safe layer)
        (sl_output_nonempty layer),[])
  | Some buffered =>
      match sm_feed (sl_machine layer) buffered with
      | None => None
      | Some (machine',out) =>
          Some (SL (sl_guess layer) (sl_guess_parameter layer)
            machine' (Some symbol) (sm_started (sl_machine layer))
            (orb (sl_output_nonempty layer) (nonemptyb out)),out)
      end
  end.

Fixpoint sl_feed_many (input:list letter) (layer:slayer)
  : option (slayer*list letter) :=
  match input with
  | [] => Some (layer,[])
  | symbol::input =>
      match sl_feed layer symbol with
      | None => None
      | Some (layer',out) =>
          match sl_feed_many input layer' with
          | None => None
          | Some (layer'',more) => Some (layer'',out++more)
          end
      end
  end.

Fixpoint pipe_action (fuel:nat) (input:list letter)
  (layers:list slayer) (s:sink) {struct fuel}
  : option (list slayer*sink) :=
  match fuel,layers with
  | O,[] =>
      option_map (fun s' => ([],s')) (pipeline_sink_run input s)
  | S fuel,layer::tail =>
      match sl_feed_many input layer with
      | None => None
      | Some (layer',out) =>
          match pipe_action fuel out tail s with
          | None => None
          | Some (tail',s') => Some (layer'::tail',s')
          end
      end
  | _,_ => None
  end.

Fixpoint pipe_close_full (fuel:nat) (layers:list slayer) (s:sink)
  (last_parameter:nat) : option (sink*nat) :=
  match fuel,layers with
  | O,[] => Some (s,last_parameter)
  | S fuel,layer::tail =>
      match sl_buffer layer with
      | Some buffered =>
          if andb (letter_eqb buffered (sl_guess layer))
             (andb (sl_last_safe layer) (sl_output_nonempty layer)) then
            match sm_feed (sl_machine layer) (sm_final (sl_machine layer)) with
            | None => None
            | Some (machine',out) =>
                match pipe_action fuel (out++[sm_edge machine']) tail s with
                | None => None
                | Some (tail',s') =>
                    match tail' with
                    | [] => pipe_close_full fuel [] s' (sm_parameter machine')
                    | next::_ =>
                        if Nat.eqb (sl_guess_parameter next)
                          (sm_parameter machine') then
                          pipe_close_full fuel tail' s'
                            (sm_parameter machine')
                        else None
                    end
                end
            end
          else None
      | None => None
      end
  | _,_ => None
  end.

End Pipeline.

Definition boundary0_guesses6 :=
  [(LB,2%nat);(LC,1%nat);(LI,3%nat);
   (LE,1%nat);(LI,1%nat);(LH,2%nat)].

Definition boundary_guesses8 :=
  [(LB,2%nat);(LC,1%nat);(LI,3%nat);(LE,1%nat);
   (LI,1%nat);(LE,1%nat);(LI,1%nat);(LH,2%nat)].

Definition bitpair_eqb x y :=
  match x,y with
  | BP10,BP10 | BP01,BP01 | BP00,BP00 => true
  | _,_ => false
  end.

Definition block_mode_eqb x y :=
  match x,y with
  | M0,M0 => true
  | M1 a,M1 b => bitpair_eqb a b
  | M2 a b,M2 c d => andb (bitpair_eqb a c) (bitpair_eqb b d)
  | _,_ => false
  end.

Definition parser_stage_eqb x y :=
  match x,y with
  | PStart,PStart | PHZone,PHZone | PAZone,PAZone => true
  | _,_ => false
  end.

Definition word_parser_eqb x y :=
  andb (parser_stage_eqb (wp_stage x) (wp_stage y))
  (andb (letters_eqb (wp_current x) (wp_current y))
  (andb (block_mode_eqb (wp_hmode x) (wp_hmode y))
  (andb (letters_eqb (wp_bridge x) (wp_bridge y))
        (block_mode_eqb (wp_amode x) (wp_amode y))))).

Definition option_letter_eqb x y :=
  match x,y with
  | None,None => true
  | Some a,Some b => letter_eqb a b
  | _,_ => false
  end.

Definition smachine_eqb x y :=
  andb (letter_eqb (sm_final x) (sm_final y))
  (andb (letter_eqb (sm_edge x) (sm_edge y))
  (andb (Bool.eqb (sm_started x) (sm_started y))
        (Nat.eqb (sm_parameter x) (sm_parameter y)))).

Definition slayer_eqb x y :=
  andb (letter_eqb (sl_guess x) (sl_guess y))
  (andb (Nat.eqb (sl_guess_parameter x) (sl_guess_parameter y))
  (andb (smachine_eqb (sl_machine x) (sl_machine y))
  (andb (option_letter_eqb (sl_buffer x) (sl_buffer y))
  (andb (Bool.eqb (sl_last_safe x) (sl_last_safe y))
        (Bool.eqb (sl_output_nonempty x) (sl_output_nonempty y)))))).

Fixpoint slayers_eqb xs ys :=
  match xs,ys with
  | [],[] => true
  | x::xs,y::ys => andb (slayer_eqb x y) (slayers_eqb xs ys)
  | _,_ => false
  end.

Record qstate := QS {
  qs_layers : list slayer;
  qs_parser : word_parser
}.

Definition qstate_eqb x y :=
  andb (slayers_eqb (qs_layers x) (qs_layers y))
       (word_parser_eqb (qs_parser x) (qs_parser y)).

Definition qtag_eqb (x y:qstate*bitpair) :=
  andb (qstate_eqb (fst x) (fst y)) (bitpair_eqb (snd x) (snd y)).

Definition qaction (chunk:list letter) (q:qstate) : option qstate :=
  match pipe_action parser_feed (length (qs_layers q)) chunk
    (qs_layers q) (qs_parser q) with
  | Some (layers,p) => Some (QS layers p)
  | None => None
  end.

Fixpoint add_new {A} (eqb:A->A->bool) (xs new:list A) : list A :=
  match new with
  | [] => xs
  | x::new =>
      add_new eqb (if existsb (eqb x) xs then xs else x::xs) new
  end.

Definition all_bitpairs := [BP10;BP01;BP00].

Definition qsuccessors (next:bitpair->bitpair->bool)
  (block:bitpair->list letter) (tag:qstate*bitpair) :=
  flat_map (fun b =>
    if next (snd tag) b then
      match qaction (block b) (fst tag) with
      | Some q => [(q,b)]
      | None => []
      end
    else []) all_bitpairs.

Fixpoint qclosure (fuel:nat) (next:bitpair->bitpair->bool)
  (block:bitpair->list letter) (states:list (qstate*bitpair)) :=
  match fuel with
  | O => states
  | S fuel =>
      qclosure fuel next block
        (add_new qtag_eqb states
          (flat_map (qsuccessors next block) states))
  end.

Definition qclosedb (next:bitpair->bitpair->bool)
  (block:bitpair->list letter) (states:list (qstate*bitpair)) :=
  forallb (fun tag =>
    forallb (fun b =>
      if next (snd tag) b then
        match qaction (block b) (fst tag) with
        | Some q => existsb (qtag_eqb (q,b)) states
        | None => false
        end
      else true) all_bitpairs) states.

Fixpoint qactions (chunk:list letter) (states:list qstate)
  : option (list qstate) :=
  match states with
  | [] => Some []
  | q::states =>
      match qaction chunk q,qactions chunk states with
      | Some q',Some states' => Some (q'::states')
      | _,_ => None
      end
  end.

Definition qends (next:bitpair->bitpair->bool)
  (block:bitpair->list letter) (last:bitpair)
  (states:list (qstate*bitpair)) :=
  qactions (block last)
    (map fst (filter (fun tag => next (snd tag) last) states)).

Definition qmode (next:bitpair->bitpair->bool)
  (block:bitpair->list letter) (m:block_mode) (states:list qstate) :=
  match m with
  | M0 => Some states
  | M1 first => qactions (block first) states
  | M2 first last =>
      match qactions (block first) states with
      | None => None
      | Some seeded =>
          let reached := qclosure 32 next block
            (map (fun q => (q,first)) seeded) in
          if qclosedb next block reached then qends next block last reached
          else None
      end
  end.

Definition raw_of_context c :=
  RC (bc_hmode c) (bc_bridge c) (bc_amode c) (bc_suffix c).

Definition raw_context_eqb x y :=
  andb (block_mode_eqb (rc_hmode x) (rc_hmode y))
  (andb (letters_eqb (rc_bridge x) (rc_bridge y))
  (andb (block_mode_eqb (rc_amode x) (rc_amode y))
        (letters_eqb (rc_suffix x) (rc_suffix y)))).

Fixpoint find_context raw contexts :=
  match contexts with
  | [] => None
  | c::contexts =>
      if raw_context_eqb raw (raw_of_context c) then Some c
      else find_context raw contexts
  end.

Definition qfinish q : option boundary_context :=
  match pipe_close_full parser_feed (length (qs_layers q))
    (qs_layers q) (qs_parser q) 0%nat with
  | Some (p,z) =>
      match parser_finish p with
      | Some raw =>
          match find_context raw all_contexts with
          | Some c => if Nat.eqb z (bc_edge_parameter c) then Some c else None
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Fixpoint qfinishes states :=
  match states with
  | [] => Some []
  | q::states =>
      match qfinish q,qfinishes states with
      | Some c,Some contexts => Some (c::contexts)
      | _,_ => None
      end
  end.

Definition context_guesses c :=
  if Nat.eqb (bc_generations c) 6%nat
  then boundary0_guesses6 else boundary_guesses8.

Definition macro_outputs c :=
  let q0 := QS (sl_initials (context_guesses c)) parser_initial in
  match qmode hnextb hblock (bc_hmode c) [q0] with
  | None => None
  | Some hs =>
      match qactions (bc_bridge c) hs with
      | None => None
      | Some bridge =>
          match qmode anextb ablock (bc_amode c) bridge with
          | None => None
          | Some as_ =>
              match qactions (bc_suffix c) as_ with
              | None => None
              | Some suffix => qfinishes suffix
              end
          end
      end
  end.

Definition macro_ok c :=
  match macro_outputs c with
  | Some (_::_) => true
  | _ => false
  end.

Definition context_goodb c :=
  andb (Nat.eqb (length (context_guesses c)) (bc_generations c))
    (match context_guesses c with
     | [] => false
     | guess::_ => Nat.eqb (snd guess) (bc_edge_parameter c)
     end).

Definition boundary0_context :=
  BC 6 2 (M2 BP01 BP01) [LH;LE;LE;LC;LC] M0 [LA;LD;LJ;LC;LB].

Lemma boundary0_context_list: In boundary0_context all_contexts.
Proof. vm_compute. tauto. Qed.

Lemma letter_eqb_eq x y:
  letter_eqb x y = true -> x=y.
Proof. destruct x,y; cbn [letter_eqb]; intros H; try discriminate; reflexivity. Qed.

Lemma letters_eqb_eq xs ys:
  letters_eqb xs ys=true -> xs=ys.
Proof.
  revert ys. induction xs; intros [|y ys] H; try discriminate; [reflexivity|].
  cbn [letters_eqb] in H. apply Bool.andb_true_iff in H as [Hxy Hrest].
  apply letter_eqb_eq in Hxy. apply IHxs in Hrest. congruence.
Qed.

Lemma bitpair_eqb_eq x y: bitpair_eqb x y=true -> x=y.
Proof. destruct x,y; cbn [bitpair_eqb]; intros H; try discriminate; reflexivity. Qed.

Lemma block_mode_eqb_eq x y: block_mode_eqb x y=true -> x=y.
Proof.
  destruct x,y; cbn [block_mode_eqb]; intros H; try discriminate.
  - reflexivity.
  - apply bitpair_eqb_eq in H. congruence.
  - apply Bool.andb_true_iff in H as [H1 H2].
    apply bitpair_eqb_eq in H1,H2. congruence.
Qed.

Lemma raw_context_eqb_eq x y: raw_context_eqb x y=true -> x=y.
Proof.
  destruct x as [hx brx ax sx]. destruct y as [hy bry ay sy].
  unfold raw_context_eqb; cbn. intros H.
  apply Bool.andb_true_iff in H as [Hh H].
  apply Bool.andb_true_iff in H as [Hb H].
  apply Bool.andb_true_iff in H as [Ha Hs].
  apply block_mode_eqb_eq in Hh,Ha.
  apply letters_eqb_eq in Hb,Hs. congruence.
Qed.

Lemma find_context_sound raw contexts c:
  find_context raw contexts=Some c ->
  In c contexts /\ raw=raw_of_context c.
Proof.
  induction contexts as [|first contexts IH]; [discriminate|].
  cbn [find_context].
  destruct (raw_context_eqb raw (raw_of_context first)) eqn:E.
  - intros H; inversion H; subst. split; [now left|].
    now apply raw_context_eqb_eq.
  - intros H. destruct (IH H) as [Hin Heq]. split; [now right|exact Heq].
Qed.

Lemma parser_stage_eqb_eq x y: parser_stage_eqb x y=true -> x=y.
Proof. destruct x,y; cbn [parser_stage_eqb]; intros H; try discriminate; reflexivity. Qed.

Lemma word_parser_eqb_eq x y: word_parser_eqb x y=true -> x=y.
Proof.
  destruct x as [sx cx hx bx ax]. destruct y as [sy cy hy bry ay].
  unfold word_parser_eqb; cbn.
  intros H. apply Bool.andb_true_iff in H as [Hs H].
  apply Bool.andb_true_iff in H as [Hc H].
  apply Bool.andb_true_iff in H as [Hh H].
  apply Bool.andb_true_iff in H as [Hb Ha].
  apply parser_stage_eqb_eq in Hs. apply letters_eqb_eq in Hc.
  apply block_mode_eqb_eq in Hh. apply letters_eqb_eq in Hb.
  apply block_mode_eqb_eq in Ha. congruence.
Qed.

Lemma option_letter_eqb_eq x y: option_letter_eqb x y=true -> x=y.
Proof.
  destruct x,y; cbn [option_letter_eqb]; intros H; try discriminate;
    try reflexivity. apply letter_eqb_eq in H. congruence.
Qed.

Lemma smachine_eqb_eq x y: smachine_eqb x y=true -> x=y.
Proof.
  destruct x as [fx ex sx px]. destruct y as [fy ey sy py].
  unfold smachine_eqb; cbn. intros H.
  apply Bool.andb_true_iff in H as [Hf H].
  apply Bool.andb_true_iff in H as [He H].
  apply Bool.andb_true_iff in H as [Hs Hp].
  apply letter_eqb_eq in Hf. apply letter_eqb_eq in He.
  apply Nat.eqb_eq in Hp. subst fy ey py.
  destruct sx,sy; cbn in Hs; try discriminate; reflexivity.
Qed.

Lemma slayer_eqb_eq x y: slayer_eqb x y=true -> x=y.
Proof.
  destruct x as [gx px mx bx sx ox]. destruct y as [gy py my b_y sy oy].
  unfold slayer_eqb; cbn. intros H.
  apply Bool.andb_true_iff in H as [Hg H].
  apply Bool.andb_true_iff in H as [Hp H].
  apply Bool.andb_true_iff in H as [Hm H].
  apply Bool.andb_true_iff in H as [Hb H].
  apply Bool.andb_true_iff in H as [Hs Ho].
  apply letter_eqb_eq in Hg. apply Nat.eqb_eq in Hp.
  apply smachine_eqb_eq in Hm. apply option_letter_eqb_eq in Hb.
  subst gy py my b_y. destruct sx,sy; cbn in Hs; try discriminate;
    destruct ox,oy; cbn in Ho; try discriminate; reflexivity.
Qed.

Lemma slayers_eqb_eq xs ys: slayers_eqb xs ys=true -> xs=ys.
Proof.
  revert ys. induction xs; intros [|y ys] H; try discriminate; [reflexivity|].
  cbn [slayers_eqb] in H. apply Bool.andb_true_iff in H as [Hxy Hrest].
  apply slayer_eqb_eq in Hxy. apply IHxs in Hrest. congruence.
Qed.

Lemma qstate_eqb_eq x y: qstate_eqb x y=true -> x=y.
Proof.
  destruct x as [lx px]. destruct y as [ly py]. unfold qstate_eqb; cbn.
  intros H. apply Bool.andb_true_iff in H as [Hl Hp].
  apply slayers_eqb_eq in Hl. apply word_parser_eqb_eq in Hp. congruence.
Qed.

Lemma qtag_eqb_eq x y: qtag_eqb x y=true -> x=y.
Proof.
  destruct x as [qx bx]. destruct y as [qy b_y]. unfold qtag_eqb; cbn.
  intros H. apply Bool.andb_true_iff in H as [Hq Hb].
  apply qstate_eqb_eq in Hq. apply bitpair_eqb_eq in Hb. congruence.
Qed.

Lemma sm_fold_app xs ys m:
  sm_fold (xs++ys) m =
  match sm_fold xs m with
  | None => None
  | Some (m',out) =>
      match sm_fold ys m' with
      | None => None
      | Some (m'',more) => Some (m'',out++more)
      end
  end.
Proof.
  revert m; induction xs; intros m.
  - cbn [app sm_fold].
    destruct (sm_fold ys m) as [[m' out]|]; reflexivity.
  - cbn [app sm_fold]. destruct (sm_feed m a) as [[m' out]|];
      [|reflexivity].
    rewrite IHxs.
    destruct (sm_fold xs m') as [[m'' more]|]; [|reflexivity].
    destruct (sm_fold ys m'') as [[last tail]|]; [|reflexivity].
    cbn. rewrite app_assoc. reflexivity.
Qed.

Lemma sl_feed_many_app xs ys layer:
  sl_feed_many (xs++ys) layer =
  match sl_feed_many xs layer with
  | None => None
  | Some (layer',out) =>
      match sl_feed_many ys layer' with
      | None => None
      | Some (layer'',more) => Some (layer'',out++more)
      end
  end.
Proof.
  revert layer. induction xs; intros layer.
  - cbn [app sl_feed_many].
    destruct (sl_feed_many ys layer) as [[layer' out]|]; reflexivity.
  - cbn [app sl_feed_many].
    destruct (sl_feed layer a) as [[next emitted]|]; [|reflexivity].
    rewrite IHxs.
    destruct (sl_feed_many xs next) as [[middle more]|]; [|reflexivity].
    destruct (sl_feed_many ys middle) as [[last tail]|]; [|reflexivity].
    cbn. rewrite app_assoc. reflexivity.
Qed.

Lemma pipeline_sink_run_app {sink} (sink_feed:sink->letter->option sink)
  xs ys s:
  pipeline_sink_run sink_feed (xs++ys) s =
  match pipeline_sink_run sink_feed xs s with
  | None => None
  | Some s' => pipeline_sink_run sink_feed ys s'
  end.
Proof.
  revert s. induction xs; intros s; [reflexivity|].
  cbn [app pipeline_sink_run]. destruct (sink_feed s a) as [s'|];
    [apply IHxs|reflexivity].
Qed.

Lemma pipe_action_app {sink} (sink_feed:sink->letter->option sink)
  fuel layers s xs ys:
  pipe_action sink_feed fuel (xs++ys) layers s =
  match pipe_action sink_feed fuel xs layers s with
  | None => None
  | Some (layers',s') => pipe_action sink_feed fuel ys layers' s'
  end.
Proof.
  revert layers s xs ys. induction fuel;
    intros layers s xs ys; destruct layers as [|layer tail];
    try reflexivity.
  - cbn [pipe_action]. rewrite pipeline_sink_run_app.
    destruct (pipeline_sink_run sink_feed xs s); reflexivity.
  - cbn [pipe_action]. rewrite sl_feed_many_app.
    destruct (sl_feed_many xs layer) as [[middle first]|]; [|reflexivity].
    destruct (sl_feed_many ys middle) as [[last second]|] eqn:Esecond.
    + rewrite IHfuel.
      destruct (pipe_action sink_feed fuel first tail s)
        as [[tail' current]|]; [|reflexivity].
      rewrite Esecond. reflexivity.
    + destruct (pipe_action sink_feed fuel first tail s)
        as [[tail' current]|]; [rewrite Esecond|]; reflexivity.
Qed.

Lemma pipe_action_length {sink} (sink_feed:sink->letter->option sink)
  fuel input layers s layers' s':
  pipe_action sink_feed fuel input layers s=Some (layers',s') ->
  length layers'=length layers.
Proof.
  revert input layers s layers' s'. induction fuel;
    intros input layers s layers' s' Haction;
    destruct layers as [|layer tail]; cbn [pipe_action] in Haction;
    try discriminate.
  - destruct (pipeline_sink_run sink_feed input s); inversion Haction.
    reflexivity.
  - destruct (sl_feed_many input layer) as [[layer' out]|]; [|discriminate].
    destruct (pipe_action sink_feed fuel out tail s)
      as [[tail' last]|] eqn:Eaction; [|discriminate].
    inversion Haction; subst. cbn. f_equal. eapply IHfuel; exact Eaction.
Qed.

Lemma qaction_app xs ys q:
  qaction (xs++ys) q =
  match qaction xs q with
  | None => None
  | Some q' => qaction ys q'
  end.
Proof.
  destruct q as [layers parser]. unfold qaction; cbn.
  rewrite pipe_action_app.
  destruct (pipe_action parser_feed (length layers) xs layers parser)
    as [[layers' parser']|] eqn:Eaction; [|reflexivity].
  pose proof (pipe_action_length parser_feed _ _ _ _ _ _ Eaction) as Elength.
  cbn. rewrite Elength. reflexivity.
Qed.

Lemma pipe_action_nil {sink} (sink_feed:sink->letter->option sink) layers s:
  pipe_action sink_feed (length layers) [] layers s=Some (layers,s).
Proof.
  induction layers as [|layer layers IH]; [reflexivity|].
  cbn [length pipe_action sl_feed_many]. rewrite IH. reflexivity.
Qed.

Lemma qaction_nil q: qaction [] q=Some q.
Proof.
  destruct q as [layers parser]. unfold qaction; cbn.
  rewrite pipe_action_nil. reflexivity.
Qed.

Lemma all_bitpairs_complete b: In b all_bitpairs.
Proof. destruct b; cbn; tauto. Qed.

Lemma add_new_contains {A} (eqb:A->A->bool) xs new x:
  In x xs -> In x (add_new eqb xs new).
Proof.
  revert xs. induction new; intros xs Hin; [exact Hin|].
  cbn [add_new]. apply IHnew.
  destruct (existsb (eqb a) xs); [exact Hin|now right].
Qed.

Lemma qclosure_contains fuel next block states tag:
  In tag states -> In tag (qclosure fuel next block states).
Proof.
  revert states. induction fuel; intros states Hin; [exact Hin|].
  cbn [qclosure]. apply IHfuel,add_new_contains. exact Hin.
Qed.

Lemma qclosedb_sound next block states tag b:
  qclosedb next block states=true ->
  In tag states -> next (snd tag) b=true ->
  exists q,
    qaction (block b) (fst tag)=Some q /\ In (q,b) states.
Proof.
  intros Hclosed Hin Hnext.
  apply forallb_forall with (x:=tag) in Hclosed; [|exact Hin].
  apply forallb_forall with (x:=b) in Hclosed;
    [|apply all_bitpairs_complete].
  rewrite Hnext in Hclosed.
  destruct (qaction (block b) (fst tag)) as [q|] eqn:Eaction;
    [|discriminate].
  apply existsb_exists in Hclosed as [tag' [Hin' Heq]].
  apply qtag_eqb_eq in Heq. subst tag'. exists q. auto.
Qed.

Lemma qactions_pointwise chunk states outputs q:
  qactions chunk states=Some outputs -> In q states ->
  exists q', qaction chunk q=Some q' /\ In q' outputs.
Proof.
  revert outputs. induction states; intros outputs Hrun Hin; [contradiction|].
  cbn [qactions] in Hrun.
  destruct (qaction chunk a) as [a'|] eqn:Ea; [|discriminate].
  destruct (qactions chunk states) as [tail|] eqn:Etail; [|discriminate].
  inversion Hrun; subst outputs. destruct Hin as [<-|Hin].
  - exists a'. split; [exact Ea|now left].
  - destruct (IHstates tail eq_refl Hin) as [q' [Eq' Hin']].
    exists q'. split; [exact Eq'|now right].
Qed.

Lemma blocks_app f xs ys:
  blocks f (xs++ys)=blocks f xs++blocks f ys.
Proof.
  induction xs; [reflexivity|]. cbn [app blocks].
  rewrite IHxs,app_assoc. reflexivity.
Qed.

Lemma hnextb_sound x y: hnext x y -> hnextb x y=true.
Proof. destruct x,y; cbn [hnext hnextb]; tauto. Qed.

Lemma anextb_sound x y: anext x y -> anextb x y=true.
Proof. destruct x,y; cbn [anext anextb]; tauto. Qed.

Lemma chain_cons_inv R x y ys:
  chain R (x::y::ys) -> R x y /\ chain R (y::ys).
Proof.
  destruct ys; cbn [chain]; tauto.
Qed.

Lemma qmiddle_sound next block (R:bitpair->bitpair->Prop) states
  previous middle last q:
  qclosedb next block states=true ->
  (forall x y, R x y -> next x y=true) ->
  In (q,previous) states ->
  chain R (previous::(middle++[last])) ->
  exists q' previous',
    qaction (blocks block middle) q=Some q' /\
    In (q',previous') states /\ next previous' last=true.
Proof.
  intros Hclosed Hnext. revert previous q.
  induction middle as [|b middle IH]; intros previous q Hin Hchain.
  - cbn [app chain blocks] in Hchain.
    destruct Hchain as [Hlast _]. exists q,previous.
    split; [apply qaction_nil|]. split; [exact Hin|now apply Hnext].
  - destruct (chain_cons_inv R previous b (middle++[last]) Hchain)
      as [Hstep Hchain'].
    destruct (qclosedb_sound next block states (q,previous) b
      Hclosed Hin (Hnext _ _ Hstep)) as [q1 [Efirst Hin1]].
    cbn in Efirst.
    destruct (IH b q1 Hin1 Hchain') as [q' [previous' [Erest Hrest]]].
    exists q',previous'. split; [|exact Hrest].
    cbn [blocks]. rewrite qaction_app,Efirst. exact Erest.
Qed.

Opaque qclosure.

Lemma qmode_sound next block (R:bitpair->bitpair->Prop) mode states outputs
  xs q:
  (forall x y, R x y -> next x y=true) ->
  mode_matches mode xs -> chain R xs ->
  qmode next block mode states=Some outputs -> In q states ->
  exists q', qaction (blocks block xs) q=Some q' /\ In q' outputs.
Proof.
  intros Hnext Hmode Hchain Hrun Hin.
  destruct mode as [|first|first last].
  - cbn [mode_matches] in Hmode. subst xs.
    cbn [qmode] in Hrun. inversion Hrun; subst.
    exists q. split; [apply qaction_nil|exact Hin].
  - cbn [mode_matches] in Hmode. subst xs.
    cbn [qmode blocks] in Hrun.
    cbn [blocks]. rewrite app_nil_r.
    eapply qactions_pointwise; [exact Hrun|exact Hin].
  - cbn [mode_matches] in Hmode.
    destruct Hmode as [middle Hxs]. subst xs.
    unfold qmode in Hrun.
    destruct (qactions (block first) states) as [seeded|] eqn:Eseed;
      [|discriminate].
    set (reached:=qclosure 32 next block
      (map (fun q0 => (q0,first)) seeded)) in *.
    destruct (qclosedb next block reached) eqn:Hclosed; [|discriminate].
    destruct (qactions_pointwise (block first) states seeded q Eseed Hin)
      as [qseed [Efirst Hinseed]].
    assert (Hintag:In (qseed,first) reached).
    { unfold reached. apply qclosure_contains.
      apply in_map_iff. exists qseed. split; [reflexivity|exact Hinseed]. }
    destruct (qmiddle_sound next block R reached first middle last qseed
      Hclosed Hnext Hintag Hchain)
      as [qbefore [previous [Emiddle [Hinbefore Hlast]]]].
    assert (Hsource:In qbefore
      (map fst (filter (fun tag => next (snd tag) last) reached))).
    { apply in_map_iff. exists (qbefore,previous). split; [reflexivity|].
      apply filter_In. auto. }
    unfold qends in Hrun.
    destruct (qactions_pointwise (block last)
      (map fst (filter (fun tag => next (snd tag) last) reached))
      outputs qbefore Hrun Hsource) as [q' [Elast Hout]].
    exists q'. split; [|exact Hout].
    cbn [blocks]. rewrite blocks_app. cbn [blocks].
    rewrite qaction_app,Efirst,qaction_app,Emiddle,app_nil_r. exact Elast.
Qed.

Lemma qfinishes_pointwise states outputs q:
  qfinishes states=Some outputs -> In q states ->
  exists c, qfinish q=Some c /\ In c outputs.
Proof.
  revert outputs. induction states; intros outputs Hrun Hin; [contradiction|].
  cbn [qfinishes] in Hrun.
  destruct (qfinish a) as [c|] eqn:Efinish; [|discriminate].
  destruct (qfinishes states) as [tail|] eqn:Etail; [|discriminate].
  inversion Hrun; subst outputs. destruct Hin as [<-|Hin].
  - exists c. split; [exact Efinish|now left].
  - destruct (IHstates tail eq_refl Hin) as [c' [Efinish' Hin']].
    exists c'. split; [exact Efinish'|now right].
Qed.

Lemma macro_outputs_sound c hs as_ outputs:
  mode_matches (bc_hmode c) hs -> chain hnext hs ->
  mode_matches (bc_amode c) as_ -> chain anext as_ ->
  macro_outputs c=Some outputs ->
  exists q c',
    qaction (context_word c hs as_)
      (QS (sl_initials (context_guesses c)) parser_initial)=Some q /\
    qfinish q=Some c' /\ In c' outputs.
Proof.
  intros Hhmode Hhchain Hamode Hachain Hrun.
  unfold macro_outputs in Hrun.
  remember (QS (sl_initials (context_guesses c)) parser_initial) as q0.
  destruct (qmode hnextb hblock (bc_hmode c) [q0]) as [hstates|]
    eqn:Ehstates; [|discriminate].
  destruct (qactions (bc_bridge c) hstates) as [bstates|]
    eqn:Ebstates; [|discriminate].
  destruct (qmode anextb ablock (bc_amode c) bstates) as [astates|]
    eqn:Eastates; [|discriminate].
  destruct (qactions (bc_suffix c) astates) as [sstates|]
    eqn:Esstates; [|discriminate].
  destruct (qmode_sound hnextb hblock hnext (bc_hmode c)
    [q0] hstates hs q0 hnextb_sound Hhmode Hhchain Ehstates
    ltac:(now left)) as [qh [Eh Hinh]].
  destruct (qactions_pointwise (bc_bridge c) hstates bstates qh
    Ebstates Hinh) as [qb [Eb Hinb]].
  destruct (qmode_sound anextb ablock anext (bc_amode c)
    bstates astates as_ qb anextb_sound Hamode Hachain Eastates Hinb)
    as [qa [Ea Hina]].
  destruct (qactions_pointwise (bc_suffix c) astates sstates qa
    Esstates Hina) as [qs [Es Hins]].
  destruct (qfinishes_pointwise sstates outputs qs Hrun Hins)
    as [c' [Efinish Hinc]].
  exists qs,c'. split; [|auto].
  unfold context_word. rewrite qaction_app,Eh,qaction_app,Eb.
  rewrite qaction_app,Ea. exact Es.
Qed.

Transparent qclosure.

Lemma all_contexts_certificate:
  forallb (fun c => andb (macro_ok c) (context_goodb c)) all_contexts=true.
Proof. native_compute. reflexivity. Qed.

Lemma context_certificate c:
  In c all_contexts ->
  macro_ok c=true /\
  length (context_guesses c)=bc_generations c /\
  match context_guesses c with
  | [] => False
  | guess::_ => snd guess=bc_edge_parameter c
  end.
Proof.
  intros Hin. pose proof all_contexts_certificate as Hcert.
  apply forallb_forall with (x:=c) in Hcert; [|exact Hin].
  apply Bool.andb_true_iff in Hcert as [Hmacro Hgood].
  unfold context_goodb in Hgood.
  apply Bool.andb_true_iff in Hgood as [Hlength Hfirst].
  apply Nat.eqb_eq in Hlength. split; [exact Hmacro|]. split; [exact Hlength|].
  destruct (context_guesses c) as [|guess guesses]; [discriminate|].
  now apply Nat.eqb_eq.
Qed.

Lemma hnextb_complete x y: hnextb x y=true -> hnext x y.
Proof. destruct x,y; cbn [hnext hnextb]; intros H; try discriminate; exact I. Qed.

Lemma anextb_complete x y: anextb x y=true -> anext x y.
Proof. destruct x,y; cbn [anext anextb]; intros H; try discriminate; exact I. Qed.

Lemma chain_extend R first middle last b:
  chain R (first::(middle++[last])) -> R last b ->
  chain R (first::(middle++[last;b])).
Proof.
  revert first. induction middle as [|x middle IH]; intros first Hchain Hlast.
  - destruct (chain_cons_inv R first last [] Hchain) as [Hfirst _].
    change (R first last /\ chain R [last;b]). split; [exact Hfirst|].
    change (R last b /\ True). auto.
  - destruct (chain_cons_inv R first x (middle++[last]) Hchain)
      as [Hfirst Htail].
    change (R first x /\ chain R (x::(middle++[last;b]))).
    split; [exact Hfirst|]. eapply IH; eassumption.
Qed.

Lemma mode_add_sound next R mode xs b mode':
  (forall x y, next x y=true -> R x y) ->
  mode_matches mode xs -> chain R xs ->
  mode_add next mode b=Some mode' ->
  mode_matches mode' (xs++[b]) /\ chain R (xs++[b]).
Proof.
  intros Hnext Hmode Hchain Hadd. destruct mode as [|first|first last].
  - cbn [mode_matches] in Hmode. subst xs.
    inversion Hadd; subst mode'. cbn [mode_matches chain]. auto.
  - cbn [mode_matches] in Hmode. subst xs.
    cbn [mode_add] in Hadd. destruct (next first b) eqn:E; [|discriminate].
    inversion Hadd; subst mode'. split.
    + cbn [mode_matches]. exists ([]:list bitpair). reflexivity.
    + change (R first b /\ True). auto.
  - cbn [mode_matches] in Hmode. destruct Hmode as [middle Hxs]. subst xs.
    cbn [mode_add] in Hadd. destruct (next last b) eqn:E; [|discriminate].
    inversion Hadd; subst mode'. split.
    + cbn [mode_matches]. exists (middle++[last]).
      reflexivity.
    + assert (Elist:
        ((first::(middle++[last]))++[b]) = first::(middle++[last;b])).
      { cbn [app]. f_equal. symmetry.
        change (middle++([last]++[b])=(middle++[last])++[b]).
        apply app_assoc. }
      rewrite Elist. eapply chain_extend; [exact Hchain|auto].
Qed.

Lemma parse_hblock_sound xs b:
  parse_hblock xs=Some b -> xs=hblock b.
Proof.
  unfold parse_hblock.
  destruct (letters_eqb xs (hblock BP10)) eqn:E10.
  - intros H; inversion H; subst. now apply letters_eqb_eq.
  - destruct (letters_eqb xs (hblock BP01)) eqn:E01.
    + intros H; inversion H; subst. now apply letters_eqb_eq.
    + destruct (letters_eqb xs (hblock BP00)) eqn:E00;
        [|discriminate].
      intros H; inversion H; subst. now apply letters_eqb_eq.
Qed.

Lemma parse_ablock_sound xs b:
  parse_ablock xs=Some b -> xs=ablock b.
Proof.
  unfold parse_ablock.
  destruct (letters_eqb xs (ablock BP10)) eqn:E10.
  - intros H; inversion H; subst. now apply letters_eqb_eq.
  - destruct (letters_eqb xs (ablock BP01)) eqn:E01.
    + intros H; inversion H; subst. now apply letters_eqb_eq.
    + destruct (letters_eqb xs (ablock BP00)) eqn:E00;
        [|discriminate].
      intros H; inversion H; subst. now apply letters_eqb_eq.
Qed.

Inductive parser_rep : word_parser -> list letter -> Prop :=
| parser_rep_start:
    parser_rep parser_initial []
| parser_rep_h hs current mode:
    mode_matches mode hs -> chain hnext hs ->
    parser_rep (WP PHZone current mode [] M0)
      (blocks hblock hs++current)
| parser_rep_a hs as_ current hmode bridge amode:
    mode_matches hmode hs -> chain hnext hs ->
    mode_matches amode as_ -> chain anext as_ ->
    parser_rep (WP PAZone current hmode bridge amode)
      (blocks hblock hs++bridge++blocks ablock as_++current).

Lemma parser_feed_sound p input x p':
  parser_rep p input ->
  parser_feed p x=Some p' ->
  parser_rep p' (input++[x]).
Proof.
  intros Hrep Hfeed. inversion Hrep; subst; clear Hrep.
  - cbn [parser_feed parser_initial] in Hfeed.
    destruct x; cbn [letter_eqb] in Hfeed; try discriminate.
    inversion Hfeed; subst.
    replace ([]++[LH]) with (blocks hblock []++[LH]) by reflexivity.
    constructor; cbn [mode_matches chain]; reflexivity.
  - change
      ((if letter_eqb x LH then
         match parse_hblock current with
         | Some b =>
             match mode_add hnextb mode b with
             | Some mode' => Some (WP PHZone [LH] mode' [] M0)
             | None => None
             end
         | None => None
         end
       else if letter_eqb x LA
         then Some (WP PAZone [LA] mode current M0)
         else Some (WP PHZone (current++[x]) mode [] M0)) = Some p')
      in Hfeed.
    destruct (letter_eqb x LH) eqn:Exh.
    + apply letter_eqb_eq in Exh. subst x.
      destruct (parse_hblock current) as [b|] eqn:Eblock.
      2:{ discriminate Hfeed. }
      destruct (mode_add hnextb mode b) as [mode'|] eqn:Eadd.
      2:{ discriminate Hfeed. }
      inversion Hfeed; subst.
      apply parse_hblock_sound in Eblock. subst current.
      destruct (mode_add_sound hnextb hnext mode hs b mode'
        hnextb_complete H H0 Eadd) as [Hmode Hchain].
      replace ((blocks hblock hs++hblock b)++[LH]) with
        (blocks hblock (hs++[b])++[LH])
        by (rewrite blocks_app; cbn [blocks]; rewrite app_nil_r; reflexivity).
      constructor; assumption.
    + destruct (letter_eqb x LA) eqn:Exa.
      * apply letter_eqb_eq in Exa. subst x.
        inversion Hfeed; subst.
        replace ((blocks hblock hs++current)++[LA]) with
          (blocks hblock hs++current++blocks ablock []++[LA])
          by (cbn [blocks]; rewrite app_assoc; reflexivity).
        constructor; try assumption; cbn [mode_matches chain]; reflexivity.
      * inversion Hfeed; subst.
        replace ((blocks hblock hs++current)++[x]) with
          (blocks hblock hs++(current++[x])) by apply app_assoc.
        constructor; assumption.
  - change
      ((if letter_eqb x LH then None
       else if letter_eqb x LA then
         match parse_ablock current with
         | Some b =>
             match mode_add anextb amode b with
             | Some mode' => Some (WP PAZone [LA] hmode bridge mode')
             | None => None
             end
         | None => None
         end
       else Some (WP PAZone (current++[x]) hmode bridge amode)) = Some p')
      in Hfeed.
    destruct (letter_eqb x LH) eqn:Exh.
    { discriminate Hfeed. }
    destruct (letter_eqb x LA) eqn:Exa.
    + apply letter_eqb_eq in Exa. subst x.
      destruct (parse_ablock current) as [b|] eqn:Eblock.
      2:{ discriminate Hfeed. }
      destruct (mode_add anextb amode b) as [mode'|] eqn:Eadd.
      2:{ discriminate Hfeed. }
      inversion Hfeed; subst.
      apply parse_ablock_sound in Eblock. subst current.
      destruct (mode_add_sound anextb anext amode as_ b mode'
        anextb_complete H1 H2 Eadd) as [Hmode Hchain].
      replace
        ((blocks hblock hs++bridge++blocks ablock as_++ablock b)++[LA])
        with
        (blocks hblock hs++bridge++blocks ablock (as_++[b])++[LA])
        by (rewrite blocks_app; cbn [blocks]; rewrite app_nil_r;
            repeat rewrite app_assoc; reflexivity).
      constructor; assumption.
    + inversion Hfeed; subst.
      replace
        ((blocks hblock hs++bridge++blocks ablock as_++current)++[x])
        with (blocks hblock hs++bridge++blocks ablock as_++(current++[x]))
        by (repeat rewrite app_assoc; reflexivity).
      constructor; assumption.
Qed.

Lemma parser_finish_sound p input raw:
  parser_rep p input -> parser_finish p=Some raw ->
  exists hs as_,
    mode_matches (rc_hmode raw) hs /\ chain hnext hs /\
    mode_matches (rc_amode raw) as_ /\ chain anext as_ /\
    input = blocks hblock hs++rc_bridge raw++
      blocks ablock as_++rc_suffix raw.
Proof.
  intros Hrep Hfinish. inversion Hrep; subst; clear Hrep;
    cbn [parser_finish] in Hfinish; try discriminate.
  inversion Hfinish; subst. exists hs,as_. repeat split; assumption.
Qed.

Lemma qfinish_sound q c:
  qfinish q=Some c ->
  exists p z,
    pipe_close_full parser_feed (length (qs_layers q))
      (qs_layers q) (qs_parser q) 0 = Some (p,z) /\
    parser_finish p=Some (raw_of_context c) /\
    In c all_contexts /\ z=bc_edge_parameter c.
Proof.
  unfold qfinish.
  destruct (pipe_close_full parser_feed (length (qs_layers q))
    (qs_layers q) (qs_parser q) 0) as [[p z]|] eqn:Eclose;
    [|discriminate].
  destruct (parser_finish p) as [raw|] eqn:Efinish; [|discriminate].
  destruct (find_context raw all_contexts) as [found|] eqn:Efind;
    [|discriminate].
  destruct (Nat.eqb z (bc_edge_parameter found)) eqn:Ez; [|discriminate].
  intros H; inversion H; subst found.
  destruct (find_context_sound raw all_contexts c Efind) as [Hin Eraw].
  apply Nat.eqb_eq in Ez. subst z.
  exists p,(bc_edge_parameter c). repeat split; try assumption.
  now rewrite <-Eraw.
Qed.

Lemma sm_fold_snoc xs x m m' m'' out more:
  sm_fold xs m = Some (m',out) ->
  sm_feed m' x = Some (m'',more) ->
  sm_fold (xs++[x]) m = Some (m'',out++more).
Proof.
  intros Hfold Hfeed. rewrite sm_fold_app,Hfold.
  cbn [sm_fold]. rewrite Hfeed,app_nil_r. reflexivity.
Qed.

Lemma sm_fold_safe_snoc xs x m m' out m'' more:
  sm_fold xs m = Some (m',out) ->
  sm_feed m' x = Some (m'',more) ->
  sm_started m'=true ->
  sm_fold_safe (xs++[x]) m.
Proof.
  revert m m' out; induction xs as [|y xs IH];
    intros m m' out Hfold Hfeed Hstarted.
  - inversion Hfold; subst. cbn [app sm_fold_safe].
    rewrite Hfeed,Hstarted. auto.
  - cbn [sm_fold] in Hfold.
    destruct (sm_feed m y) as [[next first]|] eqn:Efirst;
      [|discriminate].
    destruct (sm_fold xs next) as [[last tail]|] eqn:Etail;
      [|discriminate].
    inversion Hfold; subst.
    cbn [app sm_fold_safe]. rewrite Efirst. split.
    + right. intros Hnil. apply app_eq_nil in Hnil as [_ Hnil].
      discriminate Hnil.
    + eapply IH; eassumption.
Qed.

Inductive layer_rep (guess:letter*nat)
  : list letter -> slayer -> list letter -> Prop :=
| layer_rep_empty:
    layer_rep guess [] (sl_initial guess) []
| layer_rep_nonempty front buffered machine output last_safe output_nonempty:
    sm_fold front (sl_machine (sl_initial guess)) = Some (machine,output) ->
    (last_safe=true ->
      sm_fold_safe front (sl_machine (sl_initial guess))) ->
    (last_safe=true -> sm_started machine=true) ->
    (output_nonempty=true -> output<>[]) ->
    layer_rep guess (front++[buffered])
      (SL (fst guess) (snd guess) machine (Some buffered)
        last_safe output_nonempty) output.

Lemma layer_rep_guess_parameter guess input layer output:
  layer_rep guess input layer output ->
  sl_guess_parameter layer = snd guess.
Proof.
  intros H; destruct H; [destruct guess|]; reflexivity.
Qed.

Lemma sm_feed_started m x m' out:
  sm_started m=true ->
  sm_feed m x=Some (m',out) ->
  sm_started m'=true.
Proof.
  destruct m as [final edge started parameter].
  destruct m' as [final' edge' started' parameter'].
  cbn [sm_started]. intros Hstarted. subst started.
  unfold sm_feed. cbn [sm_edge sm_parameter sm_started sm_final].
  destruct (flow x edge) as [[[zin zout] [replacement emitted]]|];
    [|discriminate].
  destruct (Nat.eqb parameter zin); [|discriminate].
  destruct emitted; intros H; inversion H; reflexivity.
Qed.

Lemma sl_feed_buffered guess machine buffered last_safe output_nonempty symbol
  layer' more:
  sl_feed
    (SL (fst guess) (snd guess) machine (Some buffered)
      last_safe output_nonempty) symbol = Some (layer',more) ->
  exists machine',
    sm_feed machine buffered = Some (machine',more) /\
    layer' = SL (fst guess) (snd guess) machine' (Some symbol)
      (sm_started machine) (orb output_nonempty (nonemptyb more)).
Proof.
  destruct (sm_feed machine buffered)
    as [[machine' emitted]|] eqn:Efeed.
  - intros Hfeed. unfold sl_feed in Hfeed. cbn in Hfeed.
    rewrite Efeed in Hfeed. cbn in Hfeed. inversion Hfeed; subst.
    exists machine'.
    split; reflexivity.
  - intros Hfeed. unfold sl_feed in Hfeed. cbn in Hfeed.
    rewrite Efeed in Hfeed. discriminate.
Qed.

Lemma sl_feed_sound guess input layer output symbol layer' more:
  layer_rep guess input layer output ->
  sl_feed layer symbol = Some (layer',more) ->
  layer_rep guess (input++[symbol]) layer' (output++more).
Proof.
  intros Hrep Hfeed. destruct Hrep.
  - destruct guess as [edge z].
    cbn [sl_initial sl_feed] in Hfeed |- *. inversion Hfeed; subst.
    constructor.
    + reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
  - destruct (sl_feed_buffered guess machine buffered last_safe
      output_nonempty symbol layer' more Hfeed)
      as [machine' [Efeed ->]].
    econstructor.
    + eapply sm_fold_snoc; eassumption.
    + intros Hstarted. eapply sm_fold_safe_snoc; eassumption.
    + intros Hstarted. eapply sm_feed_started; eassumption.
    + intros Hnonempty Hnil. apply app_eq_nil in Hnil as [Hout Hemitted].
      apply Bool.orb_true_iff in Hnonempty as [Hnonempty|Hnonempty].
      * eapply H2; eassumption.
      * destruct more; discriminate.
Qed.

Lemma sl_feed_many_sound guess input layer output extra layer' more:
  layer_rep guess input layer output ->
  sl_feed_many extra layer = Some (layer',more) ->
  layer_rep guess (input++extra) layer' (output++more).
Proof.
  revert input layer output layer' more.
  induction extra as [|symbol extra IH];
    intros input layer output layer' more Hrep Hfeed.
  - cbn [sl_feed_many] in Hfeed. inversion Hfeed; subst.
    now rewrite !app_nil_r.
  - cbn [sl_feed_many] in Hfeed.
    destruct (sl_feed layer symbol) as [[next emitted]|] eqn:Eone;
      [|discriminate].
    destruct (sl_feed_many extra next) as [[last tail]|] eqn:Etail;
      [|discriminate].
    inversion Hfeed; subst layer' more.
    replace (input++symbol::extra) with ((input++[symbol])++extra)
      by (rewrite <-app_assoc; reflexivity).
    replace (output++emitted++tail) with ((output++emitted)++tail)
      by (rewrite <-app_assoc; reflexivity).
    eapply IH; [|exact Etail].
    eapply sl_feed_sound; eassumption.
Qed.

Fixpoint sink_run {sink} (sink_feed:sink->letter->option sink)
  (xs:list letter) (s:sink) : option sink :=
  match xs with
  | [] => Some s
  | x::xs =>
      match sink_feed s x with
      | None => None
      | Some s' => sink_run sink_feed xs s'
      end
  end.

Lemma sink_run_app {sink} (sink_feed:sink->letter->option sink)
  xs ys s:
  sink_run sink_feed (xs++ys) s =
  match sink_run sink_feed xs s with
  | None => None
  | Some s' => sink_run sink_feed ys s'
  end.
Proof.
  revert s; induction xs; intros s; [reflexivity|].
  cbn [app sink_run]. destruct (sink_feed s a) as [s'|];
    [apply IHxs|reflexivity].
Qed.

Lemma sink_run_parser_sound_from xs p input p':
  parser_rep p input ->
  sink_run parser_feed xs p=Some p' ->
  parser_rep p' (input++xs).
Proof.
  revert p input p'. induction xs as [|x xs IH];
    intros p input p' Hrep Hrun.
  - inversion Hrun; subst. now rewrite app_nil_r.
  - cbn [sink_run] in Hrun.
    destruct (parser_feed p x) as [next|] eqn:Efeed; [|discriminate].
    replace (input++x::xs) with ((input++[x])++xs)
      by (rewrite <-app_assoc; reflexivity).
    eapply IH; [eapply parser_feed_sound; eassumption|exact Hrun].
Qed.

Lemma sink_run_parser_sound xs p:
  sink_run parser_feed xs parser_initial=Some p -> parser_rep p xs.
Proof.
  intros Hrun. change (parser_rep p ([]++xs)).
  eapply sink_run_parser_sound_from; [constructor|exact Hrun].
Qed.

Fixpoint pipe_rep {sink} (sink_feed:sink->letter->option sink)
  (guesses:list (letter*nat)) (input:list letter)
  (layers:list slayer) (sink0 current:sink) : Prop :=
  match guesses,layers with
  | [],[] => sink_run sink_feed input sink0 = Some current
  | guess::guesses,layer::layers =>
      exists output,
        layer_rep guess input layer output /\
        pipe_rep sink_feed guesses output layers sink0 current
  | _,_ => False
  end.

Lemma pipe_rep_initial {sink} (sink_feed:sink->letter->option sink)
  guesses s:
  pipe_rep sink_feed guesses [] (sl_initials guesses) s s.
Proof.
  induction guesses as [|guess guesses IH]; [reflexivity|].
  cbn [pipe_rep sl_initials]. exists ([]:list letter). split.
  - constructor.
  - exact IH.
Qed.

Lemma pipeline_sink_run_eq {sink} (sink_feed:sink->letter->option sink)
  xs s:
  pipeline_sink_run sink_feed xs s = sink_run sink_feed xs s.
Proof.
  revert s. induction xs; intros s; [reflexivity|].
  cbn [pipeline_sink_run sink_run].
  destruct (sink_feed s a) as [s'|]; [apply IHxs|reflexivity].
Qed.

Lemma pipe_action_sound {sink} (sink_feed:sink->letter->option sink)
  guesses input layers sink0 current extra layers' current':
  pipe_rep sink_feed guesses input layers sink0 current ->
  pipe_action sink_feed (length guesses) extra layers current =
    Some (layers',current') ->
  pipe_rep sink_feed guesses (input++extra) layers' sink0 current'.
Proof.
  revert input layers sink0 current extra layers' current'.
  induction guesses as [|guess guesses IH];
    intros input layers sink0 current extra layers' current' Hrep Haction.
  - destruct layers; [|contradiction].
    cbn [length pipe_action] in Haction.
    destruct (pipeline_sink_run sink_feed extra current) as [last|]
      eqn:Erun; [|discriminate].
    inversion Haction; subst layers' current'.
    cbn [pipe_rep] in Hrep |- *. rewrite sink_run_app,Hrep.
    rewrite <-pipeline_sink_run_eq,Erun. reflexivity.
  - destruct layers as [|layer layers]; [contradiction|].
    cbn [pipe_rep] in Hrep. destruct Hrep as [output [Hlayer Htail]].
    cbn [length pipe_action] in Haction.
    destruct (sl_feed_many extra layer) as [[layer' more]|]
      eqn:Efeed; [|discriminate].
    destruct (pipe_action sink_feed (length guesses) more layers current)
      as [[tail' last]|] eqn:Eaction; [|discriminate].
    inversion Haction; subst layers' current'.
    cbn [pipe_rep]. exists (output++more). split.
    + eapply sl_feed_many_sound; eassumption.
    + eapply IH; eassumption.
Qed.

Lemma layer_close_sound guess z layer output buffered closed core:
  layer_rep guess (zword z) layer output ->
  sl_buffer layer = Some buffered ->
  letter_eqb buffered (sl_guess layer) = true ->
  sl_last_safe layer = true ->
  sl_output_nonempty layer = true ->
  sm_feed (sl_machine layer) (sm_final (sl_machine layer)) =
    Some (closed,core) ->
  snd guess = zparameter z ->
  exists next,
    zgen z = Some next /\
    zword next = output++core++[sm_edge closed] /\
    zparameter next = sm_parameter closed.
Proof.
  intros Hrep Hbuffer Hedge Hsafe Hnonempty Hclose Hparameter.
  remember (zword z) as input eqn:Einput in Hrep.
  destruct Hrep as
    [|front last machine output last_safe output_nonempty
       Hfold Hsafe_imp Hstarted_imp Hnonempty_imp].
  - unfold zword in Einput. symmetry in Einput.
    apply app_eq_nil in Einput as [_ E]. discriminate.
  - unfold zword in Einput.
  cbn [sl_buffer sl_guess sl_last_safe sl_output_nonempty sl_machine]
    in Hbuffer,Hedge,Hsafe,Hnonempty,Hclose.
  inversion Hbuffer; subst buffered.
  apply letter_eqb_eq in Hedge.
  apply app_inj_tail in Einput as [Hfront Hedge']. subst front last.
  destruct guess as [guess_edge guess_parameter].
  cbn [fst snd] in *. subst guess_edge guess_parameter.
  cbn [sl_initial sl_machine] in Hfold,Hsafe_imp.
  specialize (Hsafe_imp Hsafe). specialize (Hstarted_imp Hsafe).
  specialize (Hnonempty_imp Hnonempty).
  exists {| zfront:=output++core; zedge:=sm_edge closed;
            zparameter:=sm_parameter closed |}.
  split; [|split].
  2: unfold zword; symmetry; apply app_assoc.
  2: reflexivity.
  eapply sm_generation_sound; [exact Hsafe_imp|].
  unfold sm_generation. rewrite Hfold.
  rewrite Hstarted_imp. destruct output as [|first output]; [contradiction|].
  unfold sm_close. rewrite Hclose.
  assert (Eunsnoc:
    unsnoc ((first::output)++core++[sm_edge closed]) =
      Some ((first::output)++core,sm_edge closed)).
  { rewrite app_assoc. apply unsnoc_complete. }
  rewrite Eunsnoc. reflexivity.
Qed.

Lemma pipe_close_full_sound {sink} (sink_feed:sink->letter->option sink)
  guesses z layers sink0 current last_parameter final final_parameter:
  pipe_rep sink_feed guesses (zword z) layers sink0 current ->
  (match guesses with
   | [] => True
   | guess::_ => snd guess = zparameter z
   end) ->
  (match guesses with
   | [] => last_parameter=zparameter z
   | _::_ => True
   end) ->
  pipe_close_full sink_feed (length guesses) layers current last_parameter =
    Some (final,final_parameter) ->
  exists z',
    zgens (length guesses) z = Some z' /\
    sink_run sink_feed (zword z') sink0 = Some final /\
    zparameter z'=final_parameter.
Proof.
  revert z layers sink0 current last_parameter final final_parameter.
  induction guesses as [|guess guesses IH];
    intros z layers sink0 current last_parameter final final_parameter
      Hrep Hparameter Hlast Hclose.
  - destruct layers; [|contradiction].
    cbn [length pipe_close_full zgens] in Hclose. inversion Hclose; subst.
    exists z. repeat split; try reflexivity. exact Hrep.
  - destruct layers as [|layer tail]; [contradiction|].
    cbn [pipe_rep] in Hrep. destruct Hrep as [output [Hlayer Htail]].
    cbn [length pipe_close_full] in Hclose.
    destruct (sl_buffer layer) as [buffered|] eqn:Ebuffer;
      [|discriminate].
    destruct (andb (letter_eqb buffered (sl_guess layer))
      (andb (sl_last_safe layer) (sl_output_nonempty layer)))
      eqn:Echecks; [|discriminate].
    destruct (sm_feed (sl_machine layer) (sm_final (sl_machine layer)))
      as [[closed core]|] eqn:Ecore; [|discriminate].
    destruct (pipe_action sink_feed (length guesses)
      (core++[sm_edge closed]) tail current)
      as [[tail' current']|] eqn:Eaction; [|discriminate].
    apply Bool.andb_true_iff in Echecks as [Hedge Hchecks].
    apply Bool.andb_true_iff in Hchecks as [Hsafe Hnonempty].
    destruct (layer_close_sound guess z layer output buffered closed core
      Hlayer Ebuffer Hedge Hsafe Hnonempty Ecore Hparameter)
      as [next [Egen [Eword Eparameter]]].
    pose proof (pipe_action_sound sink_feed guesses output tail sink0 current
      (core++[sm_edge closed]) tail' current' Htail Eaction) as Htail'.
    rewrite <-Eword in Htail'.
    destruct guesses as [|next_guess guesses].
    + destruct tail'; [|contradiction].
      cbn [pipe_close_full] in Hclose. inversion Hclose; subst.
      exists next. repeat split.
      * change (zgens 1 z=Some next). cbn [zgens]. rewrite Egen. reflexivity.
      * exact Htail'.
      * exact Eparameter.
    + destruct tail' as [|next_layer tail']; [contradiction|].
      destruct (Nat.eqb (sl_guess_parameter next_layer)
        (sm_parameter closed)) eqn:Eparameter_check; [|discriminate].
      apply Nat.eqb_eq in Eparameter_check.
      assert (Hnext_parameter:snd next_guess=zparameter next).
      { cbn [pipe_rep] in Htail'. destruct Htail' as [next_output [Hnext _]].
        pose proof (layer_rep_guess_parameter _ _ _ _ Hnext) as Eguess.
        congruence. }
      destruct (IH next (next_layer::tail') sink0 current'
        (sm_parameter closed) final final_parameter
        Htail' Hnext_parameter I Hclose)
        as [last [Egens [Hsink Efinal]]].
      exists last. repeat split.
      * change (zgens (S (length (next_guess::guesses))) z=Some last).
        cbn [zgens]. rewrite Egen. exact Egens.
      * exact Hsink.
      * exact Efinal.
Qed.

Lemma sl_initials_length guesses:
  length (sl_initials guesses)=length guesses.
Proof. induction guesses; cbn [sl_initials length]; congruence. Qed.

Lemma qaction_inv chunk layers parser q:
  qaction chunk (QS layers parser)=Some q ->
  exists layers' parser',
    pipe_action parser_feed (length layers) chunk layers parser =
      Some (layers',parser') /\ q=QS layers' parser'.
Proof.
  unfold qaction. cbn [qs_layers qs_parser].
  destruct (pipe_action parser_feed (length layers) chunk layers parser)
    as [[layers' parser']|] eqn:Eaction; [|discriminate].
  intros H; inversion H; subst. exists layers',parser'. auto.
Qed.

Definition boundary_inv (z:zconfig) : Prop :=
  zvalid (zfront z) (zedge z) (zparameter z) /\
  exists c hs as_,
    In c all_contexts /\
    zparameter z=bc_edge_parameter c /\
    zword z=context_word c hs as_ /\
    mode_matches (bc_hmode c) hs /\ chain hnext hs /\
    mode_matches (bc_amode c) as_ /\ chain anext as_.

Lemma boundary_macro_step z:
  boundary_inv z ->
  exists n z', 0<n /\ zgens n z=Some z' /\ boundary_inv z'.
Proof.
  intros [Hvalid Hinv].
  destruct Hinv as [c [hs [as_ Hinv]]].
  destruct Hinv as [Hcontext [Hparameter [Hword
    [Hhmode [Hhchain [Hamode Hachain]]]]]].
  destruct (context_certificate c Hcontext)
    as [Hmacro [Elength Hfirst]].
  unfold macro_ok in Hmacro.
  destruct (macro_outputs c) as [[|first outputs]|] eqn:Eoutputs;
    try discriminate.
  destruct (macro_outputs_sound c hs as_ (first::outputs)
    Hhmode Hhchain Hamode Hachain Eoutputs)
    as [q [c' [Eqaction [Eqfinish Houtput]]]].
  rewrite <-Hword in Eqaction.
  destruct (qaction_inv (zword z) (sl_initials (context_guesses c))
    parser_initial q Eqaction) as [layers [parser [Eaction ->]]].
  rewrite sl_initials_length in Eaction.
  pose proof (pipe_action_sound parser_feed (context_guesses c) []
    (sl_initials (context_guesses c)) parser_initial parser_initial
    (zword z) layers parser
    (pipe_rep_initial parser_feed (context_guesses c) parser_initial)
    Eaction) as Hrep.
  cbn [app] in Hrep.
  assert (Elayers:length layers=length (context_guesses c)).
  { rewrite <-sl_initials_length.
    eapply pipe_action_length; exact Eaction. }
  destruct (qfinish_sound (QS layers parser) c' Eqfinish)
    as [final [final_parameter [Eclose [Efinish [Hcontext' Eparameter']]]]].
  cbn [qs_layers qs_parser] in Eclose. rewrite Elayers in Eclose.
  assert (Hguess:
    match context_guesses c with
    | [] => True
    | guess::_ => snd guess=zparameter z
    end).
  { destruct (context_guesses c); cbn in Hfirst |- *;
      [contradiction|congruence]. }
  assert (Hlast:
    match context_guesses c with
    | [] => 0=zparameter z
    | _::_ => True
    end).
  { destruct (context_guesses c); cbn in Hfirst |- *;
      [contradiction|exact I]. }
  destruct (pipe_close_full_sound parser_feed (context_guesses c) z
    layers parser_initial parser 0 final final_parameter
    Hrep Hguess Hlast Eclose)
    as [z' [Egens [Hparser Eparameter]]].
  destruct (zgens_sound _ _ _ Hvalid Egens) as [_ Hvalid'].
  pose proof (sink_run_parser_sound _ _ Hparser) as Hparser_rep.
  destruct (parser_finish_sound final (zword z')
    (raw_of_context c') Hparser_rep Efinish)
    as [hs' [as' [Hhmode' [Hhchain' [Hamode' [Hachain' Hword']]]]]].
  cbn [raw_of_context rc_hmode rc_bridge rc_amode rc_suffix] in
    Hhmode',Hamode',Hword'.
  exists (bc_generations c),z'. split.
  - destruct (context_guesses c); cbn [length] in Elength,Hfirst; lia.
  - split; [now rewrite <-Elength|]. split; [exact Hvalid'|].
    exists c',hs',as'. repeat split; try assumption.
    + rewrite Eparameter,Eparameter'. reflexivity.
Qed.

Lemma boundary0_valid:
  zvalid (zfront boundary0) (zedge boundary0) (zparameter boundary0).
Proof.
  exact (proj2 (zgens_sound _ _ _ generation0_valid
    generation0_to_boundary0)).
Qed.

Lemma boundary0_inv: boundary_inv boundary0.
Proof.
  split; [exact boundary0_valid|].
  exists boundary0_context,[BP01;BP01],([]:list bitpair).
  split; [exact boundary0_context_list|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exists ([]:list bitpair); reflexivity|].
  split; [cbn [chain hnext]; tauto|].
  split; [reflexivity|exact I].
Qed.

Lemma zword_nonempty z: zword z<>[].
Proof.
  destruct z as [front edge parameter]. unfold zword; cbn.
  intros H. apply app_eq_nil in H as [_ H]. discriminate.
Qed.

Lemma symbolic_run_progress k w w' xs:
  0<k -> symbolic_run k w w' -> represents w xs ->
  exists ys, rconfig xs -->+ rconfig ys /\ represents w' ys.
Proof.
  intros Hpositive Hrun Hrep. destruct Hrun; [lia|].
  destruct (symbolic_step_sound _ _ _ H Hrep)
    as [ys [Ereset Hrep']].
  destruct (symbolic_run_sound _ _ _ _ Hrun Hrep')
    as [zs [Hmore Hfinal]].
  exists zs. split; [|exact Hfinal].
  eapply progress_evstep_trans; [apply reset_step_sound,Ereset|exact Hmore].
Qed.

Lemma symbolic_generations_progress n w w' xs:
  0<n -> w<>[] ->
  symbolic_generations n w w' -> represents w xs ->
  exists ys, rconfig xs -->+ rconfig ys /\ represents w' ys.
Proof.
  intros Hpositive Hnonempty Hgens Hrep. destruct Hgens; [lia|].
  assert (Hlength:0<length w1).
  { destruct w1; [contradiction|cbn; lia]. }
  destruct (symbolic_run_progress _ _ _ _
    Hlength H Hrep)
    as [ys [Hfirst Hrep']].
  destruct (symbolic_generations_sound _ _ _ _ Hgens Hrep')
    as [zs [Hmore Hfinal]].
  exists zs. split; [|exact Hfinal].
  eapply progress_evstep_trans; eassumption.
Qed.

Definition macro_state := (zconfig*list rword)%type.
Definition macro_config (s:macro_state) := rconfig (snd s).
Definition macro_inv (s:macro_state) :=
  boundary_inv (fst s) /\ represents (zword (fst s)) (snd s).

Lemma macro_actual_step s:
  macro_inv s -> exists s',
    macro_config s -->+ macro_config s' /\ macro_inv s'.
Proof.
  destruct s as [z xs]. intros [Hinv Hrep].
  destruct (boundary_macro_step z Hinv)
    as [n [z' [Hpositive [Egens Hinv']]]].
  destruct Hinv as [Hvalid _].
  destruct (zgens_sound _ _ _ Hvalid Egens) as [Hsymbolic _].
  destruct (symbolic_generations_progress _ _ _ _ Hpositive
    (zword_nonempty z) Hsymbolic Hrep) as [ys [Hrun Hrep']].
  exists (z',ys). split; [exact Hrun|]. split; assumption.
Qed.

Lemma boundary_inv_nonhalt z xs:
  boundary_inv z -> represents (zword z) xs -> ~halts tm (rconfig xs).
Proof.
  intros Hinv Hrep.
  eapply (progress_nonhalt_cond tm macro_state (z,xs)
    macro_config macro_inv).
  - exact macro_actual_step.
  - split; assumption.
Qed.

Lemma boundary_nonhalt xs:
  represents (zword boundary0) xs -> ~halts tm (rconfig xs).
Proof. apply boundary_inv_nonhalt,boundary0_inv. Qed.

(* The state E blank start represents the initial configuration of [TM2]
   after applying its state renaming. *)
Definition variant_start : Q*tape := E;;tape0.
Definition variant_initial_words := [R1 2;R1 1].
Definition variant_generation0_words := [R1 5;R1 2;R1 2;R2 0].

Lemma variant_init:
  variant_start -->* rconfig variant_initial_words.
Proof. unfold variant_start,variant_initial_words,rconfig,rside,S',tape0.
  esx.
Qed.

Lemma variant_init_to_generation0:
  variant_start -->* rconfig variant_generation0_words.
Proof.
  eapply evstep_trans; [exact variant_init|].
  unfold variant_initial_words,variant_generation0_words.
  do 3 (eapply evstep_trans;
    [apply progress_evstep,reset_step_sound; reflexivity|]).
  apply evstep_refl.
Qed.

Definition variant_generation0 : zconfig :=
  {| zfront:=[LI;LH]; zedge:=LF; zparameter:=2 |}.

Lemma variant_generation0_valid:
  zvalid (zfront variant_generation0) (zedge variant_generation0)
    (zparameter variant_generation0).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma variant_generation0_represents:
  represents (zword variant_generation0) variant_generation0_words.
Proof. exists ([5%nat;2%nat;2%nat]:list nat). split; [|reflexivity].
  unfold Parameters. repeat constructor; reflexivity.
Qed.

Definition variant_hs :=
  [BP01;BP00;BP10;BP10;BP01;BP01;BP00].
Definition variant_as := [BP00;BP10].
Definition variant_context := decode_context (1,2,0,11,0).
Definition variant_boundary_word :=
  context_word variant_context variant_hs variant_as.
Definition variant_boundary : zconfig :=
  {| zfront:=removelast variant_boundary_word;
     zedge:=last variant_boundary_word LA; zparameter:=2 |}.

Lemma variant_generation0_to_boundary:
  zgens 52 variant_generation0 = Some variant_boundary.
Proof. vm_compute. reflexivity. Qed.

Lemma variant_generation0_boundary_run:
  symbolic_generations 52
    (zword variant_generation0) (zword variant_boundary).
Proof. apply (proj1 (zgens_sound _ _ _ variant_generation0_valid
  variant_generation0_to_boundary)).
Qed.

Lemma variant_context_list: In variant_context all_contexts.
Proof. vm_compute. tauto. Qed.

Lemma variant_boundary_valid:
  zvalid (zfront variant_boundary) (zedge variant_boundary)
    (zparameter variant_boundary).
Proof. exact (proj2 (zgens_sound _ _ _ variant_generation0_valid
  variant_generation0_to_boundary)).
Qed.

Lemma variant_boundary_inv: boundary_inv variant_boundary.
Proof.
  split; [exact variant_boundary_valid|].
  exists variant_context,variant_hs,variant_as.
  split; [exact variant_context_list|].
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [exists [BP00;BP10;BP10;BP01;BP01]; reflexivity|].
  split; [vm_compute; tauto|].
  split; [exists ([]:list bitpair); reflexivity|].
  vm_compute; tauto.
Qed.

Lemma variant_init_to_boundary:
  exists xs,
    variant_start -->* rconfig xs /\
    represents (zword variant_boundary) xs.
Proof.
  destruct (symbolic_generations_sound _ _ _ _
    variant_generation0_boundary_run variant_generation0_represents)
    as [xs [Hrun Hrep]].
  exists xs. split.
  - eapply evstep_trans; [exact variant_init_to_generation0|exact Hrun].
  - exact Hrep.
Qed.

Theorem variant_old_nonhalt: ~halts tm variant_start.
Proof.
  destruct variant_init_to_boundary as [xs [Hinit Hrep]].
  eapply multistep_nonhalt; [exact Hinit|].
  eapply boundary_inv_nonhalt; [exact variant_boundary_inv|exact Hrep].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  destruct init_to_boundary0 as [xs [Hinit Hrep]].
  eapply multistep_nonhalt; [exact Hinit|].
  now apply boundary_nonhalt.
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1LF_0RC0LB_1RA0RD_1RE---_1LF1RF_1RC0LA").

Definition to_old_state (q:Q) : Q :=
  match q with
  | A => E | B => F | C => C | D => D | E => A | F => B
  end.

Lemma tm_state_renaming: state_renaming tm TM1.tm to_old_state.
Proof. intros q s. destruct q,s; reflexivity. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply rename_nonhalt; [exact tm_state_renaming|].
  change (~halts TM1.tm TM1.variant_start).
  exact TM1.variant_old_nonhalt.
Qed.

End TM2.
