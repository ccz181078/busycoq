From BusyCoq Require Import BBinf Individual62.
Require Import Ascii String List PeanoNat NArith ZifyNat Lia.
From BusyCoq Require Import CTL.
Module TMinf := TM.TM BBinf.
Module Permute_inf := Permute.Permute BBinf.

Module CTLDecider_inf := CTLDecider BBinf.
Export CTLDecider_inf.

Ltac solve_cert cert :=
  rewrite TMinf.halts_halts';
  eapply (decide_nonhalt_spec _ cert);
  vm_compute;
  reflexivity.

Section perm_inf.
Import Permute_inf.
Lemma Permute_halts_iff tm tm' f q t:
  Permute_inf.Perm tm tm' f ->
  TMinf.halts tm (q,t) <->
  TMinf.halts tm' (f q,t).
Proof.
  repeat rewrite TMinf.halts_halts'.
  repeat rewrite <-halts_halts'.
  intro H.
  split; intro.
  - eapply perm_halts; eauto.
  - eapply perm_halts'; eauto.
Qed.
End perm_inf.

Section eqv_inf.
Import TMinf.
Hypothesis tm0 tm1 tm2: TM.
Hypothesis mp:Q->Q.
Hypothesis qn:Q.
Hypothesis sn:Sym.

Open Scope N.
Hypothesis tm1_spec:
  forall q:Q,
  q<=qn ->
  forall s:Sym,
  s<=sn ->
  match tm1 (q,s) with
  | Some (s',d,q') =>
    tm0 (mp q,s) = Some (s',d,mp q') /\
    tm2 (q,s) = Some (s',d,q') /\
    q'<=qn /\ s'<=sn
  | None =>
    match tm0 (mp q,s) with
    | None => True
    | _ => tm2 (q,s) = None
    end
  end.

Inductive P0: tape->Prop :=
| P0_intro l m r:
  m<=sn ->
  (forall n, Str_nth n l <= sn) ->
  (forall n, Str_nth n r <= sn) ->
  P0 ((l,m,r)).

Inductive P: (Q*tape)->Prop :=
| P_intro q t:
  q<=qn ->
  P0 t ->
  P (q,t).

Definition move d (t:tape) :=
match d with
| L => move_left t 
| R => move_right t 
end.

Lemma move_step tm q l m r s' d q':
  tm (q,m) = Some (s',d,q') ->
  (q,(l,m,r)) -[ tm ]-> (q',move d (l,s',r)).
Proof.
  intros.
  destruct d; cbn; econstructor; eauto.
Qed.

Lemma step_P0 [tm q l m r c' m' d q']:
  P0 ((l,m,r)) ->
  (q,(l,m,r)) -[ tm ]-> c' ->
  tm (q,m) = Some (m',d,q') ->
  m'<=sn ->
  c'=(q',move d (l,m',r)) /\ P0 (move d (l,m',r)).
Proof.
  intros.
  inverts H.
  rewrite <-step_c_spec in H0.
  inverts H0.
  rewrite H1 in H3.
  destruct d.
  - destruct l as [l0 l].
    inverts H3.
    split.
    1: reflexivity.
    econstructor.
    + apply (H7 O).
    + intro n; apply (H7 (S n)).
    + intro n; destruct n; [cbn; assumption|apply H8].
  - destruct r as [r0 r].
    inverts H3.
    split.
    1: reflexivity.
    econstructor.
    + apply (H8 O).
    + intro n; destruct n; [cbn; assumption|apply H7].
    + intro n; apply (H8 (S n)).
Qed.

Lemma halts_iff_nh q0 t0:
  P (q0,t0) ->
  (~halts tm2 (q0,t0)) ->
  halts tm0 (mp q0,t0) <-> halts tm1 (q0,t0).
Proof.
  intros I1.
  split; intro I2.
  - destruct I2 as [n [c [I2 I3]]].
    gen q0 t0.
    induction n; intros.
    + inverts I2.
      inverts I1.
      inverts H3.
      cbn in I3.
      epose proof (tm1_spec _ H2 _ H0) as I4.
      remember (tm1 (q2,m)) as v1.
      unfold Q,Sym in *.
      rewrite I3 in I4.
      rewrite <-Heqv1 in I4.
      destruct v1 as [[[s' d] q']|]; subst.
      1: destruct I4; congruence.
      eapply halted_halts.
      unfold halted.
      unfold Q,Sym in *.
      congruence.
    + inverts I2.
      inverts I1.
      pose proof H5 as I1'.
      inverts H5.
      epose proof (tm1_spec _ H4 _ H0) as I4.
      remember (tm1 (q2,m)) as v1.
      unfold Q,Sym in *.
      rewrite <-Heqv1 in I4.
      destruct v1 as [[[s' d] q']|]; subst.
      * destruct I4 as [I4 [I4a [I4b I4c]]].
        epose proof (step_P0 I1' H1 I4 I4c) as [I5 I6]. 
        subst c'.
        eapply halts_step.
        1: eapply IHn.
        3: eapply H2.
        1: solve[econstructor; eauto].
        2: apply move_step; unfold Q,Sym in *; congruence.
        erewrite <-halts_step_iff.
        1: apply H.
        apply move_step,I4a.
      * destruct (tm0 (mp q2,m)) eqn:E.
        1:{
          assert False by (apply H,halted_halts,I4).
          tauto.
        }
        inverts H1; unfold Q,Sym in *; congruence.
  - destruct I2 as [n [c [I2 I3]]].
    gen q0 t0.
    induction n; intros.
    + inverts I2.
      inverts I1.
      inverts H3.
      cbn in I3.
      epose proof (tm1_spec _ H2 _ H0) as I4.
      rewrite I3 in I4.
      remember (tm0 (mp q2,m)) as v1.
      unfold Q,Sym in *.
      rewrite <-Heqv1 in I4.
      destruct v1.
      1:{
        assert False by (apply H,halted_halts,I4).
        tauto.
      }
      eapply halted_halts.
      cbn.
      unfold Q,Sym in *; congruence.
    + inverts I2.
      inverts I1.
      pose proof H5 as I1'.
      inverts H5.
      epose proof (tm1_spec _ H4 _ H0) as I4.
      remember (tm1 (q2,m)) as v1.
      unfold Q,Sym in *.
      rewrite <-Heqv1 in I4.
      destruct v1 as [[[s' d] q']|]; subst.
      * destruct I4 as [I4 [I4a [I4b I4c]]].
        symmetry in Heqv1.
        epose proof (step_P0 I1' H1 Heqv1 I4c) as [I5 I6]. 
        subst c'.
        eapply halts_step.
        1: eapply IHn.
        3: eapply H2.
        1: solve[econstructor; eauto].
        2: apply move_step; unfold Q,Sym in *; congruence.
        erewrite <-halts_step_iff.
        1: apply H.
        apply move_step,I4a.
      * destruct (tm0 (mp q2,m)) eqn:E.
        1:{
          assert False by (apply H,halted_halts,I4).
          tauto.
        }
        inverts H1; unfold Q,Sym in *; congruence.
Qed.

End eqv_inf.

Section BackSymbol.
Hypothesis tm:TM.
Hypothesis tm':TMinf.TM.
Hypothesis n:nat.

Definition Config:Type := (list Sym)*(list Sym)*N.
Definition Config_WF(x:Config):Prop :=
  let '(l,r,q):=x in
  (q<=(N.of_nat (6*2*(2^n))%nat-1))%N.

Definition N_split(x:N)(len:nat):N*N :=
let d:=(2^N.of_nat len)%N in
(x/d,x mod d)%N.

Definition id_to_Q(x:N):Q:=
(match x with
| 0 => A
| 1 => B
| 2 => C
| 3 => D
| 4 => E
| _ => F
end)%N.

Definition id_to_dir(x:N):dir:=
(match x with
| 0 => R
| _ => L
end)%N.

Definition id_to_sym(x:N):Sym:=
(match x with
| 0 => S0
| _ => S1
end)%N.

Fixpoint id_to_list_Sym(x:N)(n:nat):list Sym :=
match n with
| O => []
| S n0 =>
  let (x1,x2):=N_split x 1 in
  id_to_sym x2 :: id_to_list_Sym x1 n0
end.

Definition id_to_back_symbol(x:N):Q*dir*(list Sym) :=
let (x1,x2):=N_split x n in
let (x3,x4):=N_split x1 1 in
(id_to_Q x3,id_to_dir x4,id_to_list_Sym x2 n).

Definition C(x:Config):Q*tape :=
  let '(l,r,q):=x in
  let '(q0,d,w):=id_to_back_symbol q in
  0inf <* l {{{ (q0,w,d) }}} r *> 0inf.

Definition to_sym'(x:Sym):BBinf.Sym :=
(match x with
| S0 => 0
| S1 => 1
end)%N.

Definition from_sym'(x:BBinf.Sym):Sym :=
match x with
| 0%N => S0
| _ => S1
end.

Definition to_side'(x:list Sym):TMinf.side := map to_sym' x *> const 0%N.

Definition C'(x:Config):BBinf.Q*TMinf.tape :=
  let '(l,r,q):=x in
  let '(q0,d,w):=id_to_back_symbol q in
  match d with
  | R => to_side' l {{q}}> to_side' r
  | L => to_side' l <{{q}} to_side' r
  end.

Definition f(x:Config):option Config :=
  let '(l,r,q):=x in
  let '(q0,d,w):=id_to_back_symbol q in
  match d with
  | R =>
    match tm' (q,to_sym' (hd 0 r)) with
    | None => None
    | Some (s',R,q') => Some (from_sym' s'::l,tl r,q')
    | Some (s',L,q') => Some (l,from_sym' s'::tl r,q')
    end
  | L =>
    match tm' (q,to_sym' (hd 0 l)) with
    | None => None
    | Some (s',L,q') => Some (tl l,from_sym' s'::r,q')
    | Some (s',R,q') => Some (from_sym' s'::tl l,r,q')
    end
  end.

Definition cfg0:Config := ([],[],0%N).

Lemma cfg0_WF: Config_WF cfg0.
Proof.
  unfold cfg0,Config_WF.
  lia.
Qed.

Hypothesis HC:
forall i : Config,
Config_WF i ->
match f i with
| Some i' => C i -[ tm ]->+ C i' /\ Config_WF i'
| None => halts tm (C i)
end.

Hypothesis HC':
forall i : Config,
Config_WF i ->
match f i with
| Some i' => TMinf.progress tm' (C' i) (C' i') /\ Config_WF i'
| None => TMinf.halts tm' (C' i)
end.

Lemma id_to_list_Sym_0 n0:
  id_to_list_Sym 0 n0 *> 0inf = 0inf.
Proof.
  induction n0.
  - reflexivity.
  - cbn.
    rewrite IHn0.
    solve_const0_eq.
Qed.

Lemma halts_iff_back_symbol:
  (halts tm c0 <-> TMinf.halts tm' TMinf.c0).
Proof.
  epose proof (halts_iff tm _ _ f C Config_WF _ cfg0_WF) as I1.
  cbn in I1.
  rewrite id_to_list_Sym_0 in I1.
  rewrite I1.
  epose proof (TMinf.halts_iff tm' _ _ f C' Config_WF _ cfg0_WF) as I2.
  cbn in I2.
  rewrite I2.
  tauto.
  Unshelve.
  all: assumption.
Qed.

End BackSymbol.

Definition Q'_from_char(x:ascii):BBinf.Q :=
((N_of_ascii x)-(N_of_ascii "A"%char))%N.

Definition Sym'_from_char(x:ascii):BBinf.Sym :=
((N_of_ascii x)-(N_of_ascii "0"%char))%N.

Definition trans'_from_char(c0 c1 c2:ascii):option (BBinf.Sym * dir * BBinf.Q) :=
  match (Sym'_from_char c0),(dir_from_char c1),(Q'_from_char c2) with
  | o, Some d, s => Some (o,d,s)
  | _,_,_ => None
  end.

Definition trans'_from_str(x:string): string*(option (BBinf.Sym * dir * BBinf.Q)) :=
match x with
| (String c0 (String c1 (String c2 x0))) =>
  (x0,trans'_from_char c0 c1 c2)
| _ => (x,None)
end.

Definition skip_sep(x:string): option string :=
match x with
| String ("_"%char) x0 => Some x0
| _ => None
end.

Fixpoint TM'_from_str_rec(x:string)(T:nat)(q s:N):=
match T with
| O => None
| S T0 =>
  match q with
  | N0 =>
    match skip_sep x with
    | Some x0 => None
    | None =>
    match s with
    | N0 => let (x0,tr):=trans'_from_str x in tr
    | _ => let (x0,tr):=trans'_from_str x in TM'_from_str_rec x0 T0 q (N.pred s)
    end
    end
  | _ =>
    match skip_sep x with
    | Some x0 =>
      TM'_from_str_rec x0 T0 (N.pred q) s
    | None =>
      let (x0,tr):=trans_from_str x in
      TM'_from_str_rec x0 T0 q s
    end
  end
end.

Definition TM'_from_str(x:string):TMinf.TM :=
  fun '(q,s)=>
  TM'_from_str_rec x (S (String.length x)) q s.

Fixpoint mp_from_str(x:string)(n:BBinf.Q):BBinf.Q :=
match x with
| EmptyString => N0
| String x0 x1 =>
  match n with
  | N0 => Q'_from_char x0
  | _ => mp_from_str x1 (N.pred n)
  end
end.

Lemma N_le_S x n:
  (x<=Npos n ->
  (x<=N.pred (Npos n) \/ x=Npos n))%N.
Proof.
  lia.
Qed.
  
Lemma N_le_O x:
  (x<=N0 ->
  x=N0)%N.
Proof.
  lia.
Qed.

Ltac N_le_cases :=
repeat
match goal with
| [H:(?a <= ?b)%N |- _] =>
  is_var a;
  match b with
  | Npos ?b0 =>
    apply N_le_S in H;
    cbn in H;
    destruct H; [ | subst a ]
  | N0 =>
    apply N_le_O in H;
    subst a
  end
end.

Ltac ccg := vm_compute; repeat split; congruence.

Lemma Str_nth_S{A}(h:A) t n:
  Str_nth (S n) (h>>t) = Str_nth n t.
Proof.
  reflexivity.
Qed.

Lemma Str_nth_const{A}(a:A) n:
  Str_nth n (const a) = a.
Proof.
  induction n.
  - reflexivity.
  - rewrite const_unfold.
    rewrite Str_nth_S.
    apply IHn.
Qed.

Ltac solve_Str_nth_le :=
  intros n; cbn;
  repeat (destruct n as [|n]; [ccg|rewrite Str_nth_S]);
  rewrite Str_nth_const; ccg.

Ltac solve_P0 :=
  econstructor;
  [ ccg | solve_Str_nth_le | solve_Str_nth_le ].

Ltac solve_P :=
  econstructor; [ ccg | solve_P0 ].

Ltac solve_bs n :=
  intros [[l r] q] H;
  cbn in H;
  N_le_cases;
  match goal with
  | [ |- match _ _ _ (_,_,?a) with _ => _ end] =>
    epose (let '(_,d,_):=(id_to_back_symbol n a) in d) as v1;
    vm_compute in v1;
    match goal with
    | [ v1 := R |- _] =>
      clear v1;
      destruct r as [|[|] r]
    | [ v1 := L |- _] =>
      clear v1;
      destruct l as [|[|] l]
    end
  end;
  cbn; solve[ split; [es|ccg] | esx].

Ltac step1_TMinf :=
  eapply TMinf.progress_intro; [|apply TMinf.evstep_refl];
  econstructor; reflexivity.

Ltac halted_TMinf :=
  eapply TMinf.halted_halts;
  reflexivity.

Ltac solve_bs' n :=
  intros [[l r] q] H;
  cbn in H;
  N_le_cases;
  match goal with
  | [ |- match _ _ _ (_,_,?a) with _ => _ end] =>
    epose (let '(_,d,_):=(id_to_back_symbol n a) in d) as v1;
    vm_compute in v1;
    match goal with
    | [ v1 := R |- _] =>
      clear v1;
      destruct r as [|[|] r]
    | [ v1 := L |- _] =>
      clear v1;
      destruct l as [|[|] l]
    end
  end;
  cbn; solve[ split; [step1_TMinf|ccg] | halted_TMinf].

Definition TM_init_tape(tm:TMinf.TM)(ls:list N):TMinf.TM :=
(let n:=N.of_nat (length ls) in
fun '(q,s) =>
if q<?n then
Some (nth (N.to_nat q) ls N0,R,N.succ q)
else
match tm (q-n,s) with
| None => None
| Some (s',d,q') => Some (s',d,n+q')
end)%N.

Ltac flia := repeat (lia||f_equal).

Lemma TM_init_tape_halts_iff tm ls t:
  TMinf.halts tm (0,t)%N <->
  TMinf.halts (TM_init_tape tm ls) (N.of_nat (length ls),t).
Proof.
  erewrite (Permute_halts_iff tm _ (N.add (N.of_nat (length ls)))).
  1: rewrite N.add_0_r; reflexivity.
  split; intros; cbn.
  - remember (N.of_nat (length ls)) as n.
    destruct (N.ltb_spec (n+q) n)%N.
    1: lia.
    replace (n+q-n)%N with q by lia.
    unfold BBinf.Q,BBinf.Sym in *.
    rewrite H.
    reflexivity.
  - remember (N.of_nat (length ls)) as n.
    destruct (N.ltb_spec (n+q) n)%N.
    1: lia.
    replace (n+q-n)%N with q by lia.
    unfold BBinf.Q,BBinf.Sym in *.
    rewrite H.
    reflexivity.
Qed.

Ltac solve_evstep T :=
  eapply TMinf.without_counter;
  eapply TMinf.multistep_c_spec with (n:=T);
  vm_compute;
  reflexivity.

Ltac solve_v1 tm tm0 n :=
  let I1 := fresh "I1'" in
  unshelve epose proof (halts_iff_back_symbol tm tm0 n _ _) as I1;
  [ time solve_bs n
  | time solve_bs' n
  | ].

Ltac solve_v2 tm0 tm1 tm2 mp qn t0 l0 cert T :=
  let I2 := fresh "I2'" in
  unshelve epose proof (halts_iff_nh tm0 tm1 tm2 mp qn 1%N _ N0 t0 _ _) as I2;
  [ intros; N_le_cases; ccg
  | solve_P
  |
    rewrite (TM_init_tape_halts_iff _ l0);
    rewrite <-(TMinf.halts_evstep_iff _ TMinf.c0);
    [ | solve_evstep 8 ];
    solve_cert cert
  | ];
  rewrite <-(TMinf.halts_evstep_iff _ TMinf.c0) in I2 by solve_evstep T.

Ltac solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' qn l0 cert T T' :=
  solve_v1 tm tm0 2;
  solve_v1 tm' tm0' 2;
  solve_v2 tm0 tm1 tm2 mp qn (const 0<*(rev l0),0,const 0)%N l0 cert T;
  solve_v2 tm0' tm1 tm2 mp' qn (const 0<*(rev l0),0,const 0)%N l0 cert T'.



Module TM1.
Definition tm := TM_from_str "1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE".
Definition tm' := TM_from_str "1RB---_0RC0RF_0RD0RA_1RE0RD_1LF0LE_1RC0LE".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1RY---_1RR---_1RA---_0Lg---_0RQ0Ri_0RS0Rk_1RQ1Ri_1RS1Rk_0Rb0R[_0RJ0Ln_0RY0RC_---1Ln_0RY0RA_0R[0RC_1RY1RA_1R[1RC_1Ln0RS_0Rb---_0Ln0Rk_0RY---_0Rb0RY_0Rd0RR_1Rb1RY_1Rd1RR_0Lg0LM_0Le0LO_1Lg1LM_1Le1LO_0RC1RJ_1Ln0Ln_1RC0Lg_1Le0Le_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_0RR1RJ_0RT0Ln_1RR0Lg_1RT0Le_1Rb0Le_1RJ0Lg_1RY1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1RY---_1RR---_1RA---_0Lg---_0RQ0Ri_0RS0Rk_1RQ1Ri_1RS1Rk_0Rb0R[_0RJ0Ln_0RY0RC_---1Ln_0RY0RA_0R[0RC_1RY1RA_1R[1RC_1Ln0RS_0Rb---_0Ln0Rk_0RY---_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lg1Ln_0Le0Rb_1Lg0Ln_1Le0RY_0RC1RJ_1Ln0Ln_1RC0Lg_1Le0Le_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_0RR1RJ_0RT0Ln_1RR0Lg_1RT0Le_1Rb0Le_1RJ0Lg_1RY1Le_---1Lg".
Definition tm1 := TM'_from_str "1LB0LB_1RE0LC_1LB1LD_0LB0LD_0RF0RH_1RL1RG_0RE---_1RI0LC_0RK0RJ_1RE---_1RA1RL_0RA0RL".
Definition tm2 := TM'_from_str "1LB0LB_1RE0LC_1LB1LD_0LB0LD_0RF0RH_1RL1RG_0RE1RM_1RI0LC_0RK0RJ_1RE1RM_1RA1RL_0RA0RL_1RM1RM".
Definition l0 := [0;0;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "bngeJSAkRC[Y".
Definition mp' := mp_from_str "bngeJSAkRC[Y".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 10 10.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM1.


Module TM2.
Definition tm := TM_from_str "1LB0LA_1RC0LA_0RF0RD_1RE---_0RC0RB_1RA0RF".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_0RF0RD_1RE---_0RC0RB_1RA0LE".
Definition tm0 := TM'_from_str "0R[1Rb_1LN0LN_1R[0LG_1LE0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR1Rb_0RT0LN_1RR0LG_1RT0LE_1RB0LE_1Rb0LG_1Ri1LE_---1LG_0Ri0RY_0Rk0R[_1Ri1RY_1Rk1R[_1LN0RS_0RB---_0LN0RK_0Ri---_0Rb---_0Rd---_1Rb---_1Rd---_1Ri---_1RR---_1RY---_0LG---_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0RB0Rk_0Rb0LN_0Ri0R[_---1LN_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0LG1LN_0LE0RB_1LG0LN_1LE0Ri".
Definition tm0' := TM'_from_str "0R[1Rb_1LN0LN_1R[0LG_1LE0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR1Rb_0RT0LN_1RR0LG_1RT0LE_1RB0LE_1Rb0LG_1Ri1LE_---1LG_0Ri0RY_0Rk0R[_1Ri1RY_1Rk1R[_1LN0RS_0RB---_0LN0RK_0Ri---_0Rb---_0Rd---_1Rb---_1Rd---_1Ri---_1RR---_1RY---_0LG---_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0RB0Rk_0Rb0LN_0Ri0R[_---1LN_0RB0Ri_0RD0RR_1RB1Ri_1RD1RR_0LG0Le_0LE0Lg_1LG1Le_1LE1Lg".
Definition tm1 := TM'_from_str "1RB1RI_1LC0LC_1RF0LD_1LC1LE_0LC0LE_0RJ0RG_1RH0LD_0RA0RK_0RB0RI_1RI1RL_1RF---_0RF---".
Definition tm2 := TM'_from_str "1RB1RI_1LC0LC_1RF0LD_1LC1LE_0LC0LE_0RJ0RG_1RH0LD_0RA0RK_0RB0RI_1RI1RL_1RF1RM_0RF1RM_1RM1RM".
Definition l0 := [0;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "kBNGEbKRiS[Y".
Definition mp' := mp_from_str "kBNGEbKRiS[Y".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 10 10.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM2.


Module TM3.
Definition tm := TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LB_1LC---".
Definition tm' := TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LO1LV_1RB0RJ_1LO0Rc_0LO0RA_1LF0Ra_1LV0Rc_1Ln1Ra_0RC1Rc_0LV0RL_0LX0LV_1LV0RC_1LX1LV_1RB0L__0LX0RB_0RJ0LO_---1RB_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rc1L__0RA---_1Rc1LO_1RA---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RB0L__0RD0RB_1RB0LO_1RD1RB_0RC0LM_1RJ0LO_1Rc1LM_1RA1LO_1LF---_1LV---_1Ln---_0RC---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LO1LV_1RB0RJ_1LO0Rc_0LO0RA_1LF0Ra_1LV0Rc_1Ln1Ra_0RC1Rc_0LV0RL_0LX0LV_1LV0RC_1LX1LV_1RB0L__0LX0RB_0RJ0LO_---1RB_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rc1L__0RA---_1Rc1LO_1RA---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RB0L__0RD---_1RB0LO_1RD---_0RC0Lm_1RJ0Lo_1Rc1Lm_1RA1Lo_1LF---_1LV---_1Ln---_0RC---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RJ_0LD0LC_1LB0RI_1LG1LE_0LF---_1LD1LC_1RH0RA_0RL0RI_1RA1RK_1RH0LC_0RA0RK_0RI1RJ".
Definition tm2 := TM'_from_str "1LB0RJ_0LD0LC_1LB0RI_1LG1LE_0LF1RM_1LD1LC_1RH0RA_0RL0RI_1RA1RK_1RH0LC_0RA0RK_0RI1RJ_1RM1RM".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "JVO_nXFBCcAL".
Definition mp' := mp_from_str "JVO_nXFBCcAL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM3.


Module TM4.
Definition tm := TM_from_str "1RB0RD_1RC---_1LD1LC_1LE0LC_1RF0RC_1RA0RF".
Definition tm' := TM_from_str "1RB0RD_1RC---_1LD1LC_1LE0LC_1RF1LD_1RA0RF".
Definition tm0 := TM'_from_str "0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_1LV1RB_---0L^_1LX1Ri_---1L^_0RR---_0RT---_1RR---_1RT---_0LW---_0LX---_1LW---_1LX---_1Ri1Lh_1L^1L`_1L`1LW_1LV1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0Rk0Lh_1Lh0L`_1Rk0LW_1LW0LX_0Lf0LU_0Lh0LW_1Lf1LU_1Lh1LW_0Rj0RQ_0Rl0RS_1Rj1RQ_1Rl1RS_1RL0Lh_1RB0L`_1R[1Lh_1Ri1L`_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1RT0RL_1Rk0RB_---0R[_0LW0Ri".
Definition tm0' := TM'_from_str "0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_1LV1RB_---0L^_1LX1Ri_---1L^_0RR---_0RT---_1RR---_1RT---_0LW---_0LX---_1LW---_1LX---_1Ri1Lh_1L^1L`_1L`1LW_1LV1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0Rk0Lh_1Lh0L`_1Rk0LW_1LW0LX_0Lf0LU_0Lh0LW_1Lf1LU_1Lh1LW_0Rj1Ri_0Rl1L^_1Rj1L`_1Rl1LV_1RL0L^_1RB0L`_1R[1L^_1Ri1L`_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1RT0RL_1Rk0RB_---0R[_0LW0Ri".
Definition tm1 := TM'_from_str "1LB1LC_0LD0LC_1LD1LC_1LF1LE_1LJ1LB_1RG1LD_0RH0RG_0RL0RI_1RK0LE_0LF0LE_1RH1RG_1RA---".
Definition tm2 := TM'_from_str "1LB1LC_0LD0LC_1LD1LC_1LF1LE_1LJ1LB_1RG1LD_0RH0RG_0RL0RI_1RK0LE_0LF0LE_1RH1RG_1RA1RM_1RM1RM".
Definition l0 := [1;0;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "TVX`WhiB[^kL".
Definition mp' := mp_from_str "TVX`WhiB[^kL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM4.


Module TM5.
Definition tm := TM_from_str "1RB1RF_1LC0LB_1RE0LD_1LB0RC_0RA0RC_1RE---".
Definition tm' := TM_from_str "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1RC_0LM---_1L_1RS_1LM---_0RS1Rb_1LN0LV_1RS0L__0RS0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0Rb0LX_0Rd0Rb_1Rb0LO_1Rd1Rb_1RJ0L]_1Rb0L__1Rj1L]_0LO1L__0LO0RQ_1LV0RS_1L_1RQ_1LM1RS_0LN0RC_0LP0LN_1LN0RS_1LP1LN_0RA0RQ_0RC0RS_1RA1RQ_1RC1RS_1LN0RC_0Rd0LN_0LV0RS_---1LN_0Rb---_0Rd---_1Rb---_1Rd---_1RJ---_1Rb---_1Rj---_0LO---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1RC_0LM---_1L_1RS_1LM---_0RS1Rb_1LN0LV_1RS0L__0RS0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0Rb0LX_0Rd0Rb_1Rb0LO_1Rd1Rb_1RJ0L]_1Rb0L__1Rj1L]_0LO1L__0LO0Ri_1LV0Rk_1L_1Ri_1LM1Rk_0LN0RC_0LP---_1LN0RS_1LP---_0RA0RQ_0RC0RS_1RA1RQ_1RC1RS_1LN0RC_0Rd0LN_0LV0RS_---1LN_0Rb---_0Rd---_1Rb---_1Rd---_1RJ---_1Rb---_1Rj---_0LO---".
Definition tm1 := TM'_from_str "1LB0LE_0LG0LC_1LE1LD_0LE0LD_1RH0LF_1LB0RI_0LC1LF_0RJ0RI_1RH0LC_1RA1RK_0RL---_1RJ1RI".
Definition tm2 := TM'_from_str "1LB0LE_0LG0LC_1LE1LD_0LE0LD_1RH0LF_1LB0RI_0LC1LF_0RJ0RI_1RH0LC_1RA1RK_0RL1RM_1RJ1RI_1RM1RM".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "JNOMV_XbSCjd".
Definition mp' := mp_from_str "JNOMV_XbSCjd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM5.


Module TM6.
Definition tm := TM_from_str "1LB1RC_1RA1LB_1RD0RA_1LE0RF_1RF0LE_1RA---".
Definition tm' := TM_from_str "1LB1RC_1RA1LB_1RD0RA_1LE0RF_1RB0LE_1RA---".
Definition tm0 := TM'_from_str "0RT0RR_1RC0RT_1RT1RR_1LP1RT_0LN1Le_0LP1RT_1LN1Rk_1LP1RR_0RB0RT_0RD1RC_1RB1RT_1RD1LP_0LP0LN_1R\0LP_1LP1LN_1RC1LP_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_0Lg1R\_1RB0R\_1Lg1RC_---0RC_---0Ri_1RT0Rk_---1Ri_1Le1Rk_0Lf1RC_0Lh---_1Lf0RT_1Lh---_0Rj0RD_0Rl1LP_1Rj1RD_1Rl0Le_1LP0Le_---0Lg_1RT1Le_---1Lg_0RB---_0RD---_1RB---_1RD---_0LP---_1R\---_1LP---_1RC---".
Definition tm0' := TM'_from_str "0RT0RR_1RC0RT_1RT1RR_1LP1RT_0LN1Le_0LP1RT_1LN1Rk_1LP1RR_0RB0RT_0RD1RC_1RB1RT_1RD1LP_0LP0LN_1R\0LP_1LP1LN_1RC1LP_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_0Lg1R\_1RB0R\_1Lg1RC_---0RC_1RC0Ri_1RT0Rk_1LP1Ri_1Le1Rk_0Lf1RC_0Lh---_1Lf0RT_1Lh---_0RJ0RD_0RL1LP_1RJ1RD_1RL0Le_1LP0Le_0LP0Lg_1RT1Le_1LP1Lg_0RB---_0RD---_1RB---_1RD---_0LP---_1R\---_1LP---_1RC---".
Definition tm1 := TM'_from_str "1LB1RF_1LC0LB_1RD1LC_1RH1RE_0RA0RD_1RG---_1RD0RH_1RA1RD".
Definition tm2 := TM'_from_str "1LB1RF_1LC0LB_1RD1LC_1RH1RE_0RA0RD_1RG1RI_1RD0RH_1RA1RD_1RI1RI".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "\ePCRkBT".
Definition mp' := mp_from_str "\ePCRkBT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM6.


Module TM7.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RA".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1RA".
Definition tm0 := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RD---_1RR---_0Rj1LW_0Rl0RC_1Rj1LO_1Rl1RC_1LM0LF_1LM0LH_1RT1LF_1RT1LH_0RB0RB_0RD0RD_1RB1RB_1RD1RD_0LO0LO_1R\1R\_1LO1LO_1RC1RC".
Definition tm0' := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RD---_1RR---_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1LM0LW_1LM0R\_1RT1LW_1RT0RC_0RB0RB_0RD0RD_1RB1RB_1RD1RD_0LO0LO_1R\1R\_1LO1LO_1RC1RC".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH---_1RI1RE_1RA1RA_1RG1RE".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH1RK_1RI1RE_1RA1RA_1RG1RE_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "DMUWCR\dlT".
Definition mp' := mp_from_str "DMUWCR\dlT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM7.


Module TM8.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1RC".
Definition tm0 := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RT---_1RR---_0Rj1LW_0Rl0RC_1Rj1LO_1Rl1RC_1LM0LF_1R\0LH_1RT1LF_1RC1LH_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LO1Rd_1R\1LW_1LO---_1RC1RR".
Definition tm0' := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RT---_1RR---_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1LM0LW_1R\0R\_1RT1LW_1RC0RC_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LO1Rd_1R\1LW_1LO---_1RC1RR".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH---_1RI1RE_1RA1RJ_1RG1RE".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH1RK_1RI1RE_1RA1RJ_1RG1RE_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "DMUWCR\dlT".
Definition mp' := mp_from_str "DMUWCR\dlT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM8.


Module TM9.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1RC".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LF_1RA1RC".
Definition tm0 := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RT---_1RR---_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1LM0LW_1R\0R\_1RT1LW_1RC0RC_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LO1Rd_1R\1LW_1LO---_1RC1RR".
Definition tm0' := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RT---_1RR---_0Rj0RT_0Rl0RC_1Rj1RT_1Rl1RC_1LM0Ln_1R\0Lp_1RT1Ln_1RC1Lp_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LO1Rd_1R\1LW_1LO---_1RC1RR".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH---_1RI1RE_1RA1RJ_1RG1RE".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH1RK_1RI1RE_1RA1RJ_1RG1RE_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "DMUWCR\dlT".
Definition mp' := mp_from_str "DMUWCR\dlT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM9.


Module TM10.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA0RB".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA0RB".
Definition tm0 := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RK---_1RR---_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1LM0LW_1Rd0R\_1RT1LW_0LW0RC_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0LO1Rl_1R\0LU_1LO1RC_1RC1LU".
Definition tm0' := TM'_from_str "1RC0RR_1LU0RT_1LW1RR_1LM1RT_0LN1Rd_0LP1LW_1LN---_1LP1RR_0Rd1Rl_1RC0LU_1Rd0LW_1LW0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LW_---0R\_1RC1LW_---0RC_0Rb---_0Rd---_1Rb---_1Rd---_1RD---_1LW---_1RK---_1RR---_0Rj1LW_0Rl0RC_1Rj1LO_1Rl1RC_1LM0LF_1Rd0LH_1RT1LF_0LW1LH_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0LO1Rl_1R\0LU_1LO1RC_1RC1LU".
Definition tm1 := TM'_from_str "1LB1RK_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH---_1RI1RE_1RA1RJ_1RH0LD_1RG1RE".
Definition tm2 := TM'_from_str "1LB1RK_0LC0LB_1RI0LD_1RE1LD_1LD1RF_0RG0RE_1RH1RL_1RI1RE_1RA1RJ_1RH0LD_1RG1RE_1RL1RL".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "DMUWCR\dlKT".
Definition mp' := mp_from_str "DMUWCR\dlKT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM10.


Module TM11.
Definition tm := TM_from_str "1LB1RC_0RA0LE_0RD1RB_1RE1RF_1LB0LB_1RC---".
Definition tm' := TM_from_str "1RB---_0RC1RE_1RD1RA_1LE0LE_0RF0LD_1RB0LE".
Definition tm0 := TM'_from_str "0RR0RR_1LN0RT_1RR1RR_1LM1RT_0LN1Rb_0LP1RC_1LN1Rj_1LP0Le_0RA0R[_0RC0R[_1RA0Lg_1RC0Le_0R[0Le_0R[0Lg_0RL1Le_0RL1Lg_0RY0RJ_0R[0RL_1RY1RJ_1R[1RL_1LN1RR_0RT0LM_0LN1RR_---1LM_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0Lg1R[_0Le---_1Lg1RL_1Le---_0RR0RR_1LN0LN_1RR1RR_1LM0LM_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RR---_0RT---_1RR---_1RT---_1Rb---_1RC---_1Rj---_0Le---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1RZ---_1Rk---_1RB---_0L]---_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_1Lf1RJ_0RL0Le_0Lf1RJ_---1Le_0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_0L_1RS_0L]---_1L_1Rd_1L]---_0RJ0RJ_1Lf0Lf_1RJ1RJ_1Le0Le_0Lf0Le_0Lh0Lg_1Lf1Le_1Lh1Lg_0Ri0RS_0Rk0RS_1Ri0L__1Rk0L]_0RS0L]_0RS0L__0Rd1L]_0Rd1L__0RJ0RJ_0RL0Lf_1RJ1RJ_1RL0Le_1RZ0Le_1Rk0Lg_1RB1Le_0L]1Lg".
Definition tm1 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH---_1RF1RI_1RJ0LE_1RK1RK_0RF0RI".
Definition tm2 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH1RL_1RF1RI_1RJ0LE_1RK1RK_0RF0RI_1RL1RL".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "bNgMe[jTLCR".
Definition mp' := mp_from_str "Zf_e]SBLdkJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM11.


Module TM12.
Definition tm := TM_from_str "1RB---_0RC1RE_1RD1RA_1LE0LE_0RF0LD_1RB0LE".
Definition tm' := TM_from_str "1RB0LF_0RC1RE_1RD1RA_1LE0LE_0RA0LD_0RA---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1RZ---_1Rk---_1RB---_0L]---_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_1Lf1RJ_0RL0Le_0Lf1RJ_---1Le_0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_0L_1RS_0L]---_1L_1Rd_1L]---_0RJ0RJ_1Lf0Lf_1RJ1RJ_1Le0Le_0Lf0Le_0Lh0Lg_1Lf1Le_1Lh1Lg_0Ri0RS_0Rk0RS_1Ri0L__1Rk0L]_0RS0L]_0RS0L__0Rd1L]_0Rd1L__0RJ0RJ_0RL0Lf_1RJ1RJ_1RL0Le_1RZ0Le_1Rk0Lg_1RB1Le_0L]1Lg".
Definition tm0' := TM'_from_str "0RJ0RJ_0RL---_1RJ1RJ_1RL---_1RZ0Lm_1RC0Lo_1RB1Lm_0L]1Lo_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_1Lf1RJ_0RL0Le_0Lf1RJ_---1Le_0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_0L_1RS_0L]---_1L_1Rd_1L]---_0RJ0RJ_1Lf0Lf_1RJ1RJ_1Le0Le_0Lf0Le_0Lh0Lg_1Lf1Le_1Lh1Lg_0RA0RS_0RC0RS_1RA0L__1RC0L]_0RS0L]_0RS0L__0Rd1L]_0Rd1L__0RA---_0RC---_1RA---_1RC---_0RS---_0RS---_0Rd---_0Rd---".
Definition tm1 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH---_1RF1RI_1RJ0LE_1RK1RK_0RF0RI".
Definition tm2 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH1RL_1RF1RI_1RJ0LE_1RK1RK_0RF0RI_1RL1RL".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "Zf_e]SBLdkJ".
Definition mp' := mp_from_str "Zf_e]SBLdCJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM12.


Module TM13.
Definition tm := TM_from_str "1RB0LF_0RC1RE_1RD1RA_1LE0LE_0RA0LD_0RA---".
Definition tm' := TM_from_str "1LB0LB_0RC0LA_1RE1LD_0RA---_0RF1RB_1RA1RC".
Definition tm0 := TM'_from_str "0RJ0RJ_0RL---_1RJ1RJ_1RL---_1RZ0Lm_1RC0Lo_1RB1Lm_0L]1Lo_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_1Lf1RJ_0RL0Le_0Lf1RJ_---1Le_0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_0L_1RS_0L]---_1L_1Rd_1L]---_0RJ0RJ_1Lf0Lf_1RJ1RJ_1Le0Le_0Lf0Le_0Lh0Lg_1Lf1Le_1Lh1Lg_0RA0RS_0RC0RS_1RA0L__1RC0L]_0RS0L]_0RS0L__0Rd1L]_0Rd1L__0RA---_0RC---_1RA---_1RC---_0RS---_0RS---_0Rd---_0Rd---".
Definition tm0' := TM'_from_str "0Rb0Rb_1LN0LN_1Rb1Rb_1LM0LM_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RQ0Rk_0RS0Rk_1RQ0LG_1RS0LE_0Rk0LE_0Rk0LG_0RL1LE_0RL1LG_0Rb0Rb_0Rd---_1Rb1Rb_1Rd---_1RB0L^_1RS0L`_1RR1L^_0LE1L`_0RA---_0RC---_1RA---_1RC---_0Rk---_0Rk---_0RL---_0RL---_0Ri0RJ_0Rk0RL_1Ri1RJ_1Rk1RL_1LN1Rb_0Rd0LM_0LN1Rb_---1LM_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LG1Rk_0LE---_1LG1RL_1LE---".
Definition tm1 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH---_1RF1RI_1RJ0LE_1RK1RK_0RF0RI".
Definition tm2 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH1RL_1RF1RI_1RJ0LE_1RK1RK_0RF0RI_1RL1RL".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "Zf_e]SBLdCJ".
Definition mp' := mp_from_str "BNGMEkRdLSb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM13.


Module TM14.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RE1LD_0RA---_0RF1RB_1RA1RC".
Definition tm' := TM_from_str "1LB0LC_0RA0LA_0RD0LA_1RE---_0RF1RB_1RA1RD".
Definition tm0 := TM'_from_str "0Rb0Rb_1LN0LN_1Rb1Rb_1LM0LM_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RQ0Rk_0RS0Rk_1RQ0LG_1RS0LE_0Rk0LE_0Rk0LG_0RL1LE_0RL1LG_0Rb0Rb_0Rd---_1Rb1Rb_1Rd---_1RB0L^_1RS0L`_1RR1L^_0LE1L`_0RA---_0RC---_1RA---_1RC---_0Rk---_0Rk---_0RL---_0RL---_0Ri0RJ_0Rk0RL_1Ri1RJ_1Rk1RL_1LN1Rb_0Rd0LM_0LN1Rb_---1LM_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LG1Rk_0LE---_1LG1RL_1LE---".
Definition tm0' := TM'_from_str "0Rb0Rb_1LN0LN_1Rb1Rb_1LU0LU_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RA0Rk_0RC0Rk_1RA0LG_1RC0LE_0Rk0LE_0Rk0LG_0RL1LE_0RL1LG_0RY0Rk_0R[0Rk_1RY0LG_1R[0LE_0Rk0LE_---0LG_0RL1LE_---1LG_0Rb---_0Rd---_1Rb---_1Rd---_1RB---_1RC---_1RZ---_0LE---_0Ri0RJ_0Rk0RL_1Ri1RJ_1Rk1RL_1LN1Rb_0Rd0LU_0LN1Rb_---1LU_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0LG1Rk_0LE---_1LG1RL_1LE---".
Definition tm1 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH---_1RF1RI_1RJ0LE_1RK1RK_0RF0RI".
Definition tm2 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH1RL_1RF1RI_1RJ0LE_1RK1RK_0RF0RI_1RL1RL".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "BNGMEkRdLSb".
Definition mp' := mp_from_str "BNGUEkZdLCb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM14.


Module TM15.
Definition tm := TM_from_str "1LB0LC_0RA0LA_0RD0LA_1RE---_0RF1RB_1RA1RD".
Definition tm' := TM_from_str "1LB0LB_0RC0LA_1RD1RD_0RE1RB_1RA1RF_1RD---".
Definition tm0 := TM'_from_str "0Rb0Rb_1LN0LN_1Rb1Rb_1LU0LU_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RA0Rk_0RC0Rk_1RA0LG_1RC0LE_0Rk0LE_0Rk0LG_0RL1LE_0RL1LG_0RY0Rk_0R[0Rk_1RY0LG_1R[0LE_0Rk0LE_---0LG_0RL1LE_---1LG_0Rb---_0Rd---_1Rb---_1Rd---_1RB---_1RC---_1RZ---_0LE---_0Ri0RJ_0Rk0RL_1Ri1RJ_1Rk1RL_1LN1Rb_0Rd0LU_0LN1Rb_---1LU_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0LG1Rk_0LE---_1LG1RL_1LE---".
Definition tm0' := TM'_from_str "0RZ0RZ_1LN0LN_1RZ1RZ_1LM0LM_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RQ0Rc_0RS0Rc_1RQ0LG_1RS0LE_0Rc0LE_0Rc0LG_0RL1LE_0RL1LG_0RZ0RZ_0R\0R\_1RZ1RZ_1R\1R\_1RB1RB_1RS1RS_1Rj1Rj_0LE0LE_0Ra0RJ_0Rc0RL_1Ra1RJ_1Rc1RL_1LN1RZ_0R\0LM_0LN1RZ_---1LM_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LG1Rc_0LE---_1LG1RL_1LE---_0RZ---_0R\---_1RZ---_1R\---_1RB---_1RS---_1Rj---_0LE---".
Definition tm1 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH---_1RF1RI_1RJ0LE_1RK1RK_0RF0RI".
Definition tm2 := TM'_from_str "1LB0LB_0RF0LC_1LB1LD_0RF0LE_0LB0LD_1RA1RG_0RH1RL_1RF1RI_1RJ0LE_1RK1RK_0RF0RI_1RL1RL".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "BNGUEkZdLCb".
Definition mp' := mp_from_str "BNGMEcj\LSZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM15.


Module TM16.
Definition tm := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE1RF_0LE1LA_1RC---".
Definition tm' := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RF_0LE1LA_0LA---".
Definition tm0 := TM'_from_str "0RJ0RT_0RL1R[_1RJ1RT_1RL0LE_1R[0LE_1RL0LG_1RK1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1LF1RT_1RR0LE_1Rj1RD_1RB1LE_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0Lg0R[_0RT0RL_1Lg0RK_---1R[_1Le0Rj_0LE0Rl_1LF1Rj_1LG1Rl_0Lf1R[_0Lh---_1Lf1RK_1Lh---_0Le0RD_1RL1RK_0LF1RD_0LG1LE_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_0RR---_0RT---_1RR---_1RT---_1LF---_1RR---_1Rj---_1RB---".
Definition tm0' := TM'_from_str "0RJ0RT_0RL1R[_1RJ1RT_1RL0LE_1R[0LE_1RL0LG_1RK1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1LF1RT_1RR0LE_1Ri1RD_1RB1LE_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0Lg0R[_0RT0RL_1Lg0RK_---1R[_1Le0Ri_0LE0Rk_1LF1Ri_1LG1Rk_0Lf1R[_0Lh---_1Lf1RK_1Lh---_0Le0RD_1RL1RK_0LF1RD_0LG1LE_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_0RT---_1R[---_1RT---_0LE---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1RB1RJ_1RC1RG_1LD1RK_1RA0LE_1RG1LF_1RC0LF_1RH1RI_0RC0RG_0RA1RC_1RA0LF_0RB---".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RG_1LD1RK_1RA0LE_1RG1LF_1RC0LF_1RH1RI_0RC0RG_0RA1RC_1RA0LF_0RB1RL_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LT[FGEKRBDj".
Definition mp' := mp_from_str "LT[FGEKRBDi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM16.


Module TM17.
Definition tm := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RF_0LE1LA_0LA---".
Definition tm' := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RE_0LF---_1RB1LA".
Definition tm0 := TM'_from_str "0RJ0RT_0RL1R[_1RJ1RT_1RL0LE_1R[0LE_1RL0LG_1RK1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1LF1RT_1RR0LE_1Ri1RD_1RB1LE_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0Lg0R[_0RT0RL_1Lg0RK_---1R[_1Le0Ri_0LE0Rk_1LF1Ri_1LG1Rk_0Lf1R[_0Lh---_1Lf1RK_1Lh---_0Le0RD_1RL1RK_0LF1RD_0LG1LE_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_0RT---_1R[---_1RT---_0LE---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ0RT_0RL1R[_1RJ1RT_1RL0LE_1R[0LE_1RL0LG_1RK1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1LF1RT_1RR0LE_1Ra1RD_1RB1LE_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0Lo0R[_0RT0RL_1Lo0RK_---1R[_1RK0Ra_---0Rc_1LF1Ra_---1Rc_0Lf1R[_0Lh---_1Lf1RK_1Lh---_0RT---_1RL---_1RT---_0LG---_0Lm---_0Lo---_1Lm---_1Lo---_0RJ0RD_0RL1RK_1RJ1RD_1RL1LE_1R[0LF_1RL0LH_1RK1LF_0LE1LH".
Definition tm1 := TM'_from_str "1RB1RJ_1RC1RG_1LD1RK_1RA0LE_1RG1LF_1RC0LF_1RH1RI_0RC0RG_0RA1RC_1RA0LF_0RB---".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RG_1LD1RK_1RA0LE_1RG1LF_1RC0LF_1RH1RI_0RC0RG_0RA1RC_1RA0LF_0RB1RL_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LT[FGEKRBDi".
Definition mp' := mp_from_str "LT[FGEKRBDa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM17.


Module TM18.
Definition tm := TM_from_str "1RB0LD_0RC0RE_1RD0RC_1LA0LD_1RF---_0RB0RA".
Definition tm' := TM_from_str "1RB0LD_0RC0RE_1RD0LF_1LA0LD_1RF---_0RB0RA".
Definition tm0 := TM'_from_str "0RJ1Rj_0RL0LF_1RJ0L__1RL0L]_1RZ0L]_1Rj0L__1RQ1L]_---1L__0RQ0Ra_0RS0Rc_1RQ1Ra_1RS1Rc_1LF0RK_0RZ---_0LF0RC_0RQ---_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0L_1LF_0L]0RZ_1L_0LF_1L]0RQ_0Rc1Rj_1LF0LF_1Rc0L__1L]0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0Rj---_0Rl---_1Rj---_1Rl---_1RQ---_1RJ---_1Ra---_0L_---_0RI0RA_0RK0RC_1RI1RA_1RK1RC_0RZ0RS_0Rj0LF_0RQ0Rc_---1LF".
Definition tm0' := TM'_from_str "0RJ1Rj_0RL0LF_1RJ0L__1RL0L]_1RZ0L]_1Rj0L__1RQ1L]_---1L__0RQ0Ra_0RS0Rc_1RQ1Ra_1RS1Rc_1LF0RK_0RZ---_0LF0RC_0RQ---_0RZ0RQ_0R\0RJ_1RZ1RQ_1R\1RJ_0L_0Lm_0L]0Lo_1L_1Lm_1L]1Lo_0Rc1Rj_1LF0LF_1Rc0L__1L]0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0Rj---_0Rl---_1Rj---_1Rl---_1RQ---_1RJ---_1Ra---_0L_---_0RI0RA_0RK0RC_1RI1RA_1RK1RC_0RZ0RS_0Rj0LF_0RQ0Rc_---1LF".
Definition tm1 := TM'_from_str "1LB0LB_1RC0LG_0RK0RD_1RE0LG_0RF0RI_1RA1RJ_1LB1LH_0LB0LH_1RC---_0RA0RJ_1RJ1RL_0RC---".
Definition tm2 := TM'_from_str "1LB0LB_1RC0LG_0RK0RD_1RE0LG_0RF0RI_1RA1RJ_1LB1LH_0LB0LH_1RC1RM_0RA0RJ_1RJ1RL_0RC1RM_1RM1RM".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "ZFjCJS_]cQKa".
Definition mp' := mp_from_str "ZFjCJS_]cQKa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM18.


Module TM19.
Definition tm := TM_from_str "1LB0RA_1RC0LE_1RE1RD_0RC0LA_1LD1RF_0RD---".
Definition tm' := TM_from_str "1LB1RB_1RC0LE_0RD0LA_1RE1RC_1LC1RF_0RC---".
Definition tm0 := TM'_from_str "0R\0RA_1L^0RC_1R\1RA_0Lg1RC_0LN1RS_0LP0R\_1LN1R\_1LP0RA_0RR0RS_0RT0R[_1RR0LG_1RT1R[_1R\0Le_1RS0Lg_1Rl1Le_1R\1Lg_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0LG1Rb_1R[1RS_1LG1RZ_---1R\_0RQ1RS_0RS0R\_1RQ0Lg_1RS1R\_1LN0LE_0RS0LG_0Rl1LE_0R\1LG_0RZ0Rj_1LN0Rl_1RZ1Rj_1R\1Rl_0L^1RQ_0L`---_1L^0Lg_1L`---_0RY---_0R[---_1RY---_1R[---_0Rb---_0LN---_0RZ---_1LN---".
Definition tm0' := TM'_from_str "0RT0RJ_1LV0RL_1RT1RJ_0Lg1RL_0LN1R[_0LP1RY_1LN1RT_1LP0Lg_0RR0R[_0RT0RS_1RR0LG_1RT1RS_1Rb0Le_1R[0Lg_1RR1Le_1RT1Lg_0RY1R[_0R[0RT_1RY0Lg_1R[1RT_1LN0LE_0R[0LG_0Rl1LE_0RT1LG_0Rb0RR_0Rd0RT_1Rb1RR_1Rd1RT_0LG1Rb_1RS1R[_1LG1RR_---1RT_0RR0Rj_1LN0Rl_1RR1Rj_1RT1Rl_0LV1RY_0LX---_1LV0Lg_1LX---_0RQ---_0RS---_1RQ---_1RS---_0Rb---_0LN---_0RR---_1LN---".
Definition tm1 := TM'_from_str "1LB0RI_1RC0LE_1RA1RD_0RC0RH_1LF0LE_0RC0LG_1LB1RH_1RC1RH_1RJ---_1RK0LE_0RA0RD".
Definition tm2 := TM'_from_str "1LB0RI_1RC0LE_1RA1RD_0RC0RH_1LF0LE_0RC0LG_1LB1RH_1RC1RH_1RJ1RL_1RK0LE_0RA0RD_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "bNSZg^G\l[Q".
Definition mp' := mp_from_str "bN[RgVGTlSY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM19.


Module TM20.
Definition tm := TM_from_str "1RB0RA_1RC0RE_1RD---_1LE1LD_1LF0LD_1RA0RD".
Definition tm' := TM_from_str "1RB0RA_1RC0RE_1RD---_1LE1LD_1LF0LD_1RA1LE".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1R\0RT_1RC0RJ_---0Rc_0L_0RA_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1L^1RJ_---0Lf_1L`1RA_---1Lf_0RZ---_0R\---_1RZ---_1R\---_0L_---_0L`---_1L_---_1L`---_1RA1Lp_1Lf1Lh_1Lh1L__1L^1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_0RC0Lp_1Lp0Lh_1RC0L__1L_0L`_0Ln0L]_0Lp0L__1Ln1L]_1Lp1L__0RB0RY_0RD0R[_1RB1RY_1RD1R[_1RT0Lp_1RJ0Lh_1Rc1Lp_1RA1Lh".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1R\0RT_1RC0RJ_---0Rc_0L_0RA_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1L^1RJ_---0Lf_1L`1RA_---1Lf_0RZ---_0R\---_1RZ---_1R\---_0L_---_0L`---_1L_---_1L`---_1RA1Lp_1Lf1Lh_1Lh1L__1L^1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_0RC0Lp_1Lp0Lh_1RC0L__1L_0L`_0Ln0L]_0Lp0L__1Ln1L]_1Lp1L__0RB1RA_0RD1Lf_1RB1Lh_1RD1L^_1RT0Lf_1RJ0Lh_1Rc1Lf_1RA1Lh".
Definition tm1 := TM'_from_str "1RB---_1LC1LD_0LE0LD_1LE1LD_1LG1LF_1LK1LC_1RH1LE_0RI0RH_0RA0RJ_1RL0LF_0LG0LF_1RI1RH".
Definition tm2 := TM'_from_str "1RB1RM_1LC1LD_0LE0LD_1LE1LD_1LG1LF_1LK1LC_1RH1LE_0RI0RH_0RA0RJ_1RL0LF_0LG0LF_1RI1RH_1RM1RM".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "T\^`h_pAJcfC".
Definition mp' := mp_from_str "T\^`h_pAJcfC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM20.


Module TM21.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_1LB---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RE---".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lo_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LN0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1RY_0LG---_0L_0L__1LN---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_0RS---_1Lf---_1RS---_1RQ---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lo_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LN0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1RY_0LG---_0L_0L__1LN---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_0Ra---_0Rc---_1Ra---_1Rc---_0LN---_0LN---_1LN---_1LN---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQo".
Definition mp' := mp_from_str "YN_fGUASQo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM21.


Module TM22.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RE---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0RD---".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lo_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LN0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1RY_0LG---_0L_0L__1LN---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_0Ra---_0Rc---_1Ra---_1Rc---_0LN---_0LN---_1LN---_1LN---".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LN0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY0RA_0LG---_0L_1RA_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_0RY---_0R[---_1RY---_1R[---_0LG---_0RS---_1LG---_1LN---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQo".
Definition mp' := mp_from_str "YN_fGUASQp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM22.


Module TM23.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0RE1LF_0LA---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0RA---".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LG0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_0Ra1LN_0Rc---_1Ra1LU_1Rc---_0Ra0Ln_0LG0Lp_1LN1Ln_1LG1Lp_1RY---_0LG---_0L_---_1LN---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LG0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1LN_0LG---_0L_1LU_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_0RA---_0RC---_1RA---_1RC---_1RY---_0LG---_1RQ---_1LG---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQp".
Definition mp' := mp_from_str "YN_fGUASQp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM23.


Module TM24.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0RA---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RD---".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LG0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1LN_0LG---_0L_1LU_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_0RA---_0RC---_1RA---_1RC---_1RY---_0LG---_1RQ---_1LG---".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lo_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LG0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1LN_0LG---_0L_1LU_1LN---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_0RY---_0R[---_1RY---_1R[---_0LG---_0RS---_1LG---_1LN---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQp".
Definition mp' := mp_from_str "YN_fGUASQo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM24.


Module TM25.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RD---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0LA---".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lo_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LG0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1LN_0LG---_0L_1LU_1LN---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_0RY---_0R[---_1RY---_1R[---_0LG---_0RS---_1LG---_1LN---".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1LG0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY1LN_0LG---_0L_1LU_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_1RY---_0LG---_0L_---_1LN---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQo".
Definition mp' := mp_from_str "YN_fGUASQp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM25.


Module TM26.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RC---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RA---".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lo_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_0RA0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY0RY_0LG---_0L_1RY_1LN---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_0RQ---_0RS---_1RQ---_1RS---_1LN---_0RY---_0RA---_0RQ---".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_0RA0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY0RY_0LG---_0L_1RY_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_0RB---_0RD---_1RB---_1RD---_0L_---_1LN---_1L_---_0RA---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_0RG---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_0RG1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQo".
Definition mp' := mp_from_str "YN_fGUASQp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM26.


Module TM27.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RC---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RB---".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1RQ0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY0RS_0LG---_0L_1RS_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_0RR---_0RT---_1RR---_1RT---_1LU---_1RY---_1RA---_1RQ---".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1RQ0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY0RS_0LG---_0L_1RS_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_0RJ---_0RL---_1RJ---_1RL---_1R[---_1RY---_1RS---_1RQ---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQp".
Definition mp' := mp_from_str "YN_fGUASQp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM27.


Module TM28.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RB---".
Definition tm' := TM_from_str "1LB0LE_0RC0LF_0LA1LD_1RE---_0RF0RE_1LC0RA".
Definition tm0 := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lp_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1RQ0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY0RS_0LG---_0L_1RS_1LN---_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_0RJ---_0RL---_1RJ---_1RL---_1R[---_1RY---_1RS---_1RQ---".
Definition tm0' := TM'_from_str "0Rc1LN_1LV0Ri_1Rc1Le_1Ra1Ri_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RQ0LG_0RS0Rc_1RQ0L`_1RS1Rc_0LN0Lm_1Ri0Lo_1LN1Lm_1Ra1Lo_1Ri0Rc_0LG---_0Lo1Rc_1LN---_0LE0L^_0LG0L`_1LE1L^_1LG1L`_0Rb---_0Rd---_1Rb---_1Rd---_1Le---_1Ri---_1RA---_1Ra---_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0LG1LN_0Rc0Ri_1LG0RA_1LN0Ra_1LN0RA_1Ra0RC_1Le1RA_---1RC_0LV1Ri_0LX0LG_1LV1Ra_1LX1LG".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "YN_fGUASQp".
Definition mp' := mp_from_str "iNoVGeAca`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM28.


Module TM29.
Definition tm := TM_from_str "1LB0LE_0RC0LF_0LA1LD_1RE---_0RF0RE_1LC0RA".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RA---".
Definition tm0 := TM'_from_str "0Rc1LN_1LV0Ri_1Rc1Le_1Ra1Ri_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RQ0LG_0RS0Rc_1RQ0L`_1RS1Rc_0LN0Lm_1Ri0Lo_1LN1Lm_1Ra1Lo_1Ri0Rc_0LG---_0Lo1Rc_1LN---_0LE0L^_0LG0L`_1LE1L^_1LG1L`_0Rb---_0Rd---_1Rb---_1Rd---_1Le---_1Ri---_1RA---_1Ra---_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0LG1LN_0Rc0Ri_1LG0RA_1LN0Ra_1LN0RA_1Ra0RC_1Le1RA_---1RC_0LV1Ri_0LX0LG_1LV1Ra_1LX1LG".
Definition tm0' := TM'_from_str "0RS1LN_1Lf0RY_1RS1LU_1RQ1RY_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR0LG_0RT0RS_1RR0Lo_1RT1RS_1LU0L]_1RY0L__1RA1L]_1RQ1L__0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LG1LN_0RS0RY_1LG0RA_1LN0RQ_1LN0RA_1RQ0RC_1LU1RA_---1RC_0Lf1RY_0Lh0LG_1Lf1RQ_1Lh1LG_1RY0RS_0LG---_0L_1RS_1LN---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_0RA---_0RC---_1RA---_1RC---_1RY---_0LG---_1RQ---_1LG---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "iNoVGeAca`".
Definition mp' := mp_from_str "YN_fGUASQo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM29.


Module TM30.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RF_1RB0LD_0RD---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0LB---".
Definition tm0 := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Rj0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0R[0RJ_1LP0RK_---0LP_1Ra0Rj_1LN0Rl_1LF1Rj_1LE1Rl_0LF1LF_0LH---_1LF1Rj_1LH---_0RJ0LP_0RL0R[_1RJ0LG_1RL1R[_1R[0L]_1RJ0L__1RK1L]_0LG1L__0RY---_0R[---_1RY---_1R[---_0LP---_0R[---_1LP---".
Definition tm0' := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Ri0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0R[0RJ_1LP0RK_---0LP_1Ra0Ri_1LN0Rk_1LF1Ri_1LE1Rk_0LF1LF_0LH---_1LF1Ri_1LH---_0RJ0LP_0RL0R[_1RJ0LG_1RL1R[_1R[0L]_1RJ0L__1RK1L]_0LG1L__0R[---_0RJ---_1R[---_1RJ---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_0RA---".
Definition tm2 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_0RA1RN_1RN1RN".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "[FGNPaJcTKREj".
Definition mp' := mp_from_str "[FGNPaJcTKREi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM30.


Module TM31.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0LB---".
Definition tm' := TM_from_str "1LB0LA_1RC0RF_0LD0RB_1LA1RE_0RD---_1RB0LD".
Definition tm0 := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Ri0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0R[0RJ_1LP0RK_---0LP_1Ra0Ri_1LN0Rk_1LF1Ri_1LE1Rk_0LF1LF_0LH---_1LF1Ri_1LH---_0RJ0LP_0RL0R[_1RJ0LG_1RL1R[_1R[0L]_1RJ0L__1RK1L]_0LG1L__0R[---_0RJ---_1R[---_1RJ---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1LF0RT_1RR0LF_1Rb0Rk_1Ri1LF_0LP0RI_0R[0RK_0LG1RI_1R[1RK_0L]0R[_0L_0RJ_1L]0RK_1L_0LP_1Ri0Rb_1LN0Rd_1LF1Rb_1LE1Rd_0LF1LF_0LH---_1LF1Rb_1LH---_0RY---_0R[---_1RY---_1R[---_0LP---_0R[---_1LP---_------_0RJ0LP_0RL0R[_1RJ0LG_1RL1R[_1R[0L]_1RJ0L__1RK1L]_0LG1L_".
Definition tm1 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_0RA---".
Definition tm2 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_0RA1RN_1RN1RN".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "[FGNPaJcTKREi".
Definition mp' := mp_from_str "[FGNPiJkTKREb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM31.


Module TM32.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_1LA---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LF_1LA---".
Definition tm0 := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Ri0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_1Ra0RJ_1LP0RK_---0LP_1Ra0Ri_1LN0Rk_1LF1Ri_1LE1Rk_0LF0LP_0LH---_1LF1LP_1LH---_0RJ0LP_0RL1Ra_1RJ0LG_1RL1LF_1R[0L]_1RJ0L__1RK1L]_0LG1L__1Ra---_1LN---_1LF---_1LE---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Ri0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_1Ra0RJ_1LP0RK_---0LP_1Ra0Ri_1LN0Rk_1LF1Ri_1LE1Rk_0LF0LP_0LH---_1LF1LP_1LH---_0RJ0LP_0RL---_1RJ0LG_1RL---_1R[0Lm_1RJ0Lo_1RK1Lm_0LG1Lo_1Ra---_1LN---_1LF---_1LE---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_1RF---".
Definition tm2 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_1RF1RN_1RN1RN".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "[FGNPaJcTKREi".
Definition mp' := mp_from_str "[FGNPaJcTKREi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM32.


Module TM33.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LF_1LA---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0LC---".
Definition tm0 := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Ri0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_1Ra0RJ_1LP0RK_---0LP_1Ra0Ri_1LN0Rk_1LF1Ri_1LE1Rk_0LF0LP_0LH---_1LF1LP_1LH---_0RJ0LP_0RL---_1RJ0LG_1RL---_1R[0Lm_1RJ0Lo_1RK1Lm_0LG1Lo_1Ra---_1LN---_1LF---_1LE---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Ri0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_1Ra0RJ_1LP0RK_---0LP_1Ra0Ri_1LN0Rk_1LF1Ri_1LE1Rk_0LF0LP_0LH---_1LF1LP_1LH---_0RJ0LP_0RL1Ra_1RJ0LG_1RL1LF_1R[0L]_1RJ0L__1RK1L]_0LG1L__1Ra---_0RR---_1LF---_1RR---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_1RF---".
Definition tm2 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_1RF1RN_1RN1RN".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "[FGNPaJcTKREi".
Definition mp' := mp_from_str "[FGNPaJcTKREi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM33.


Module TM34.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RE_1RB0LF_1LA---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RF_1RB0LD_1RB---".
Definition tm0 := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Rb0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0RL0RJ_1LP0RK_---0LP_1Ra0Rb_1LN0Rd_1LF1Rb_1LE1Rd_0LF1RT_0LH---_1LF1Rc_1LH---_0RJ0LP_0RL---_1RJ0LG_1RL---_1R[0Lm_1RJ0Lo_1RK1Lm_0LG1Lo_1Ra---_1LN---_1LF---_1LE---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LF0RT_1RR0LF_1Rj0Rc_1Ra1LF_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0RL0RJ_1LP0RK_---0LP_1Ra0Rj_1LN0Rl_1LF1Rj_1LE1Rl_0LF1RT_0LH---_1LF1Rc_1LH---_0RJ0LP_0RL0RL_1RJ0LG_1RL1RL_1R[0L]_1RJ0L__1RK1L]_0LG1L__0RJ---_0RL---_1RJ---_1RL---_1R[---_1RJ---_1RK---_0LG---".
Definition tm1 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_0RN---_1RI1RH".
Definition tm2 := TM'_from_str "1LB1RM_0LE0LC_1LD1LL_1RK0LB_1RF1LB_0RG0LE_0RI0RH_1RG0LC_1RA1RJ_1RK1RF_0RA0RJ_0LD0LL_0RN1RO_1RI1RH_1RO1RO".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "[FGNPaJcTKREbL".
Definition mp' := mp_from_str "[FGNPaJcTKREjL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM34.


Module TM35.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RD---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1LF0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1RQ_0Lg---_0LW0LW_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RK---_1L^---_1RK---_1RI---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1LF0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1RQ_0Lg---_0LW0LW_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RY---_0R[---_1RY---_1R[---_0LF---_0LF---_1LF---_1LF---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIo".
Definition mp' := mp_from_str "QFW^gMaKIo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM35.


Module TM36.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RD---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RC---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1LF0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1RQ_0Lg---_0LW0LW_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RY---_0R[---_1RY---_1R[---_0LF---_0LF---_1LF---_1LF---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1LF0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0Ra_0Lg---_0LW1Ra_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RQ---_0RS---_1RQ---_1RS---_0Lg---_0RK---_1Lg---_1LF---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIo".
Definition mp' := mp_from_str "QFW^gMaKIp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM36.


Module TM37.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RC---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1Lg0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1LF_0Lg---_0LW1LM_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0Ra---_0Rc---_1Ra---_1Rc---_1RQ---_0Lg---_1RI---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1Lg0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1LF_0Lg---_0LW1LM_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RQ---_0RS---_1RQ---_1RS---_0Lg---_0RK---_1Lg---_1LF---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIp".
Definition mp' := mp_from_str "QFW^gMaKIo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM37.


Module TM38.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RC---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LE---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1Lg0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1LF_0Lg---_0LW1LM_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RQ---_0RS---_1RQ---_1RS---_0Lg---_0RK---_1Lg---_1LF---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1Lg0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1LF_0Lg---_0LW1LM_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1RQ---_0Lg---_0LW---_1LF---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIo".
Definition mp' := mp_from_str "QFW^gMaKIp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM38.


Module TM39.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LE---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RF_0RD1LE_0LF---_1LA0LB".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1Lg0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1LF_0Lg---_0LW1LM_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1RQ---_0Lg---_0LW---_1LF---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0Lo_0RL0RK_1RJ0Lh_1RL1RK_1LM0LU_1RQ0LW_1Ri1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lo1LF_0RK0RQ_1Lo0Ri_1LF0RI_1LF0Ri_1Lo0Rk_1LM1Ri_---1Rk_0L^1RQ_0L`0Lo_1L^1RI_1L`1Lo_0RY1LF_0R[---_1RY1LM_1R[---_0RY0Lf_0Lo0Lh_1LF1Lf_1Lo1Lh_1RQ---_0Lo---_0LW---_1LF---_0Lm---_0Lo---_1Lm---_1Lo---_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LE1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIp".
Definition mp' := mp_from_str "QFW^oMiKIh".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM39.


Module TM40.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RE---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_0Ra0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RQ_0Lg---_0LW1RQ_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RI---_0RK---_1RI---_1RK---_1LF---_0RQ---_0Ra---_0RI---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_0Ra0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RQ_0Lg---_0LW1RQ_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0Rb---_0Rd---_1Rb---_1Rd---_0LW---_1LF---_1LW---_0Ra---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_0RG---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_0RG1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIo".
Definition mp' := mp_from_str "QFW^gMaKIp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM40.


Module TM41.
Definition tm := TM_from_str "1RB---_0RC0RB_1LD0RE_0LE1LA_1LF0LB_0RD0LC".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1LM---_1RQ---_1Ra---_1RI---_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1Ln_0RK0RQ_1Lg0Ra_1Ln0RI_1Ln0Ra_1RI0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RK_0Lg---_0LW1RK_1Ln---_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_0RK1Ln_1L^0RQ_1RK1LM_1RI1RQ_0Ln0LM_0Lp0LO_1Ln1LM_1Lp1LO_0RY0Lg_0R[0RK_1RY0LH_1R[1RK_0Ln0LU_1RQ0LW_1Ln1LU_1RI1LW".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1RI0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RK_0Lg---_0LW1RK_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RJ---_0RL---_1RJ---_1RL---_1LM---_1RQ---_1Ra---_1RI---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QnW^gMaKIH".
Definition mp' := mp_from_str "QFW^gMaKIp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM41.


Module TM42.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RB---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1RI0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RK_0Lg---_0LW1RK_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RJ---_0RL---_1RJ---_1RL---_1LM---_1RQ---_1Ra---_1RI---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1RI0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RK_0Lg---_0LW1RK_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0Ra---_0Rc---_1Ra---_1Rc---_1RQ---_0Lg---_1RI---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIp".
Definition mp' := mp_from_str "QFW^gMaKIo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM42.


Module TM43.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RA---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1RI0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RK_0Lg---_0LW1RK_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0Ra---_0Rc---_1Ra---_1Rc---_1RQ---_0Lg---_1RI---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1RI0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0RK_0Lg---_0LW1RK_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RB---_0RD---_1RB---_1RD---_1RS---_1RQ---_1RK---_1RI---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1RI1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIo".
Definition mp' := mp_from_str "QFW^gMaKIp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM43.


Module TM44.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0LE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LC0RD_1RA---_0RF0LA_0LA1RC".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0RQ_1RQ0Lg_1RS1RQ_0LN0LE_0RB0LG_1LN1LE_0Ri1LG_1RB---_0LN---_0Lg---_1RB---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RR_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1LN0Le_1RB0Lg_0Rc1Le_---1Lg_0LU0RY_0RB0R[_1LN1RY_1RB1R[_0LU1LN_0LW---_1LU0Rc_1LW---_0RB---_0RD---_1RB---_1RD---_0Lg---_1Ri---_1Lg---_0Lg---_0Ri1RB_0Rk0Ri_1Ri0Lg_1Rk1Ri_0LN0LE_0RB0LG_1LN1LE_0R[1LG_1RB0RR_0Ri0RT_0Lg1RR_1Ri1RT_0LE1LN_0LG1RB_1LE0Rc_1LG---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgEcQYi".
Definition mp' := mp_from_str "BNgEciR[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM44.


Module TM45.
Definition tm := TM_from_str "1LB0RF_1RC0LF_0LA1RD_0LD0RE_1RA---_0RC0LF".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LA---".
Definition tm0 := TM'_from_str "0R\0Ri_1LN0Rk_1R\1Ri_1Lm1Rk_0LN1RB_0LP0LN_1LN0RZ_1LP1LN_0RR1RB_0RT0LN_1RR0Lo_1RT0Lm_1RB0Lm_1RB0Lo_0RZ1Lm_1Rc1Lo_1RB0RZ_0RQ0R\_0Lo1RZ_1RQ1R\_0LE1LN_0LG1RB_1LE0Rk_1LG---_0L]0Ra_0RB0Rc_1LN1Ra_1RB1Rc_0L]1LN_0L_---_1L]0Rk_1L_---_0RB---_0RD---_1RB---_1RD---_0Lo---_1RQ---_1Lo---_0Lo---_0RQ1RB_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0RB0Lo_1LN1Lm_0Rc1Lo".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_1Rj---_1RB---_1Lg---_0Lg---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNomkQZc".
Definition mp' := mp_from_str "BNgecQYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM45.


Module TM46.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LA---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LE---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_1Rj---_1RB---_1Lg---_0Lg---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Ri1Lg_1RB---_0LN---_0Lg---_0Le---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgecQYj".
Definition mp' := mp_from_str "BNgecQYi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM46.


Module TM47.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LA---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Ri1Lg_1RB---_0LN---_0Lg---_0Le---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Ri1Lg_1RB---_0RQ---_0Lg---_1RQ---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgecQYi".
Definition mp' := mp_from_str "BNgecQYi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM47.


Module TM48.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LA---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LC0RD_1RA---_0RF0LE_0LA1RC".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Ri1Lg_1RB---_0RQ---_0Lg---_1RQ---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RR_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1LN0Le_1RB0Lg_0Rc1Le_---1Lg_0LU0RY_0RB0R[_1LN1RY_1RB1R[_0LU1LN_0LW---_1LU0Rc_1LW---_0RB---_0RD---_1RB---_1RD---_0Lg---_1Ri---_1Lg---_0Lg---_0Ri1RB_0Rk0LN_1Ri0Lg_1Rk0Le_0LN0Le_0RB0Lg_1LN1Le_0R[1Lg_1RB0RR_0Ri0RT_0Lg1RR_1Ri1RT_0LE1LN_0LG1RB_1LE0Rc_1LG---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgecQYi".
Definition mp' := mp_from_str "BNgeciR[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM48.


Module TM49.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0LB---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0LN_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LE_1RQ---_1Lg1LE_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Ri1Lg_0LN---_0RB---_1RB---_1RB---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0LN_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Le_1RQ---_1Lg1Le_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0RQ---_0LN---_1RQ---_0Le---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgecQYi".
Definition mp' := mp_from_str "BNgecQYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM49.


Module TM50.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LB0RF_0RC0LF".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LF0RF_0RC0LF".
Definition tm0 := TM'_from_str "0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT0Lm_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0Lo0Lo_1RQ---_1Lo1Lo_0Lo---_0R[0Ri_1LN0Rk_1R[1Ri_1Lm1Rk_0LN1Rb_0LP0LN_1LN0RY_1LP1LN_0RQ1Rb_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0Rb0Lo_1LN1Lm_0RB1Lo".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT0Lm_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0Lo0Lo_1RQ---_1Lo1Lo_0Lo---_0RY0Ri_1LN0Rk_1RY1Ri_1Lm1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0Rb0Lo_1LN1Lm_0RB1Lo".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "bNomkQYB".
Definition mp' := mp_from_str "bNomkQYB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM50.


Module TM51.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LF0RF_0RC0LF".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LB---".
Definition tm0 := TM'_from_str "0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT0Lm_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0Lo0Lo_1RQ---_1Lo1Lo_0Lo---_0RY0Ri_1LN0Rk_1RY1Ri_1Lm1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0Rb0Lo_1LN1Lm_0RB1Lo".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1LN_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1Lg_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0R[---_1LN---_1R[---_1Le---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "bNomkQYB".
Definition mp' := mp_from_str "BNgecQYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM51.


Module TM52.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_0LD0RF_0RC0LF".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1LN_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1Lg_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0R[---_1LN---_1R[---_1Le---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT0Lm_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0Lo0Lo_1RQ---_1Lo1Lo_0Lo---_1LN0Ri_1LN0Rk_1Lm1Ri_1Lm1Rk_0L]1Rb_0L_0LN_1L]0RY_1L_1LN_0RQ1Rb_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0Rb0Lo_1LN1Lm_0RB1Lo".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgecQYj".
Definition mp' := mp_from_str "bNomkQYB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM52.


Module TM53.
Definition tm := TM_from_str "1LB0LD_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RE---".
Definition tm0 := TM'_from_str "0R[1LN_1LN0Rc_1R[1Le_1Le1Rc_0LN0L]_0LP0L__1LN1L]_1LP1L__0RR1RB_0RT0LN_1RR0Lg_1RT0Le_0L]0Le_1RB0Lg_1L]1Le_1Rj1Lg_1RB0RY_0Lg0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0Rc_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg1RQ_1RQ---_1Lg0Lg_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0Ra---_0Rc---_1Ra---_1Rc---_1RB---_0LN---_0RY---_1LN---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0Rc_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg1RQ_1RQ---_1Lg0Lg_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0Ra---_0Rc---_1Ra---_1Rc---_1RB---_0LN---_0RY---_1LN---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_0RE---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_0RE1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgecQYj".
Definition mp' := mp_from_str "BNgecQYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM53.


Module TM54.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1LB_0RC1LF_0RB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1LB_1LB0RF_0RC0LA".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Ln1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1R[1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG1R[_0RB0R[_0RD1LN_1RB1R[_1RD1Ln_0Lg0LN_1RQ0LP_1Lg1LN_0Lg1LP_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Ln_0RB0Lp_1LN1Ln_0R[1Lp_0RI---_0RK---_1RI---_1RK---_0RQ---_0LN---_0R[---_1LN---".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1R[1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1Rb_1LE0Rk_1LG1R[_0Rb0R[_0Rd1LN_1Rb1R[_1Rd1LE_0Lo0LN_1RQ0LP_1Lo1LN_0Lo1LP_0R[0Ri_1LN0Rk_1R[1Ri_1LE1Rk_0LN1Rb_0LP0LN_1LN0RY_1LP1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0R[1LG".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RI_1RF0LC_1RA0RG_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgncQY[".
Definition mp' := mp_from_str "bNoEkQY[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM54.


Module TM55.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1LB_1LB0RF_0RC0LA".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1LB_1LF0RF_0RC0LA".
Definition tm0 := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1R[1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1Rb_1LE0Rk_1LG1R[_0Rb0R[_0Rd1LN_1Rb1R[_1Rd1LE_0Lo0LN_1RQ0LP_1Lo1LN_0Lo1LP_0R[0Ri_1LN0Rk_1R[1Ri_1LE1Rk_0LN1Rb_0LP0LN_1LN0RY_1LP1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0R[1LG".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1R[1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1Rb_1LE0Rk_1LG1R[_0Rb0R[_0Rd1LN_1Rb1R[_1Rd1LE_0LG0LN_1RQ0LP_1LG1LN_0Lo1LP_0RY0Ri_1LN0Rk_1RY1Ri_---1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0R[1LG".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RI_1RF0LC_1RA0RG_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "bNoEkQY[".
Definition mp' := mp_from_str "bNoEkQY[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM55.


Module TM56.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1LB_1LF0RF_0RC0LA".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LE0RD_1RE1LB_1LB0RF_0RC0LA".
Definition tm0 := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1R[1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1Rb_1LE0Rk_1LG1R[_0Rb0R[_0Rd1LN_1Rb1R[_1Rd1LE_0LG0LN_1RQ0LP_1LG1LN_0Lo1LP_0RY0Ri_1LN0Rk_1RY1Ri_---1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0R[1LG".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_1Rb0Lm_1Rb0Lo_0RY1Lm_1R[1Lo_1Rb0RY_0RQ0R[_0Lo1RY_1RQ1R[_0Le1LN_0Lg1Rb_1Le0Rk_1Lg1R[_0Rb0R[_0Rd1LN_1Rb1R[_1Rd1LE_0Lo0LN_1RQ0LP_1Lo1LN_0Lo1LP_0R[0Ri_1LN0Rk_1R[1Ri_1LE1Rk_0LN1Rb_0LP0LN_1LN0RY_1LP1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0R[1LG".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RI_1RF0LC_1RA0RG_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "bNoEkQY[".
Definition mp' := mp_from_str "bNoEkQY[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM56.


Module TM57.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LF_1LB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LF0RD_1RA1RF_0RC0LF_1LB---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1LN_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1Lg_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rj1Lo_0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_---0Le_1RB0Lg_---1Le_1Rj1Lg_1RB0RY_---0R[_0Lg1RY_---1R[_0Lm1LN_0Lo1LN_1Lm0Rc_1Lo---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1Lg_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rj1Lo_0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RI_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgmcQYj".
Definition mp' := mp_from_str "BNgmcQYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM57.


Module TM58.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LF0RD_1RA1RF_0RC0LF_1LB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_0LD0RF_0RC0LA".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_---0Le_1RB0Lg_---1Le_1Rj1Lg_1RB0RY_---0R[_0Lg1RY_---1R[_0Lm1LN_0Lo1LN_1Lm0Rc_1Lo---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1Lg_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rj1Lo_0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0Lo0Lo_1RQ---_1Lo1Lo_0Lo---_1LN0Ri_1LN0Rk_1LE1Ri_1LE1Rk_0L]1Rb_0L_0LN_1L]0RY_1L_1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0RB1LG".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RI_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgmcQYj".
Definition mp' := mp_from_str "bNoEkQYB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM58.


Module TM59.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_0LD0RF_0RC0LA".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LF0RF_0RC0LA".
Definition tm0 := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0Lo0Lo_1RQ---_1Lo1Lo_0Lo---_1LN0Ri_1LN0Rk_1LE1Ri_1LE1Rk_0L]1Rb_0L_0LN_1L]0RY_1L_1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0RB1LG".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0LG0Lo_1RQ---_1LG1Lo_0Lo---_0RY0Ri_1LN0Rk_1RY1Ri_---1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0RB1LG".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RI_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "bNoEkQYB".
Definition mp' := mp_from_str "bNoEkQYB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM59.


Module TM60.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RF_1LB0RF_0RC0LA".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RF_1LF0RF_0RC0LA".
Definition tm0 := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1Rj1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG0RS_1LE0Rk_1LG---_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0Lo0Lo_1RQ---_1Lo1RY_0Lo---_0R[0Ri_1LN0Rk_1R[1Ri_1LE1Rk_0LN1Rb_0LP0LN_1LN0RY_1LP1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0Rj1LG".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1Rj1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG0RS_1LE0Rk_1LG---_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0LG0Lo_1RQ---_1LG1RY_0Lo---_0RY0Ri_1LN0Rk_1RY1Ri_---1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0Rj1LG".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0LC1RG".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RJ_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0LC1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "bNoEkQYjS".
Definition mp' := mp_from_str "bNoEkQYjS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM60.


Module TM61.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RF_1LF0RF_0RC0LA".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC0LF_1LB---".
Definition tm0 := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1Rj1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG0RS_1LE0Rk_1LG---_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0LG0Lo_1RQ---_1LG1RY_0Lo---_0RY0Ri_1LN0Rk_1RY1Ri_---1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0Rj1LG".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rb1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rb1Lo_0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0LC1RG".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RJ_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0LC1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "bNoEkQYjS".
Definition mp' := mp_from_str "BNgmcQYbS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM61.


Module TM62.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC0LF_1LB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LF_0RC---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rb1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rb1Lo_0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rj1Lo_0RQ---_0RS---_1RQ---_1RS---_0LN---_0RB---_1LN---_0Rj---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0LC1RG".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RJ_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0LC1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgmcQYbS".
Definition mp' := mp_from_str "BNgmcQYjS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM62.


Module TM63.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LF_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC0LF_0RC---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rj1Lo_0RQ---_0RS---_1RQ---_1RS---_0LN---_0RB---_1LN---_0Rj---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rb1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rb1Lo_0RQ---_0RS---_1RQ---_1RS---_0LN---_0RB---_1LN---_0Rb---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0LC1RG".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RJ_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0LC1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgmcQYjS".
Definition mp' := mp_from_str "BNgmcQYbS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM63.


Module TM64.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC0LF_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC1LF_0RB---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rb1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rb1Lo_0RQ---_0RS---_1RQ---_1RS---_0LN---_0RB---_1LN---_0Rb---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Ln1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rb1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Ln_0RB0Lp_1LN1Ln_0Rb1Lp_0RI---_0RK---_1RI---_1RK---_0RQ---_0LN---_0R[---_1LN---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0LC1RG".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RJ_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0LC1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgmcQYbS".
Definition mp' := mp_from_str "BNgncQYbS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM64.


Module TM65.
Definition tm := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LB_1RA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0RB_1RA---".
Definition tm0 := TM'_from_str "0RJ0R\_0RL1RK_1RJ1R\_1RL1LH_0LW0LF_1Rd0LH_1LW1LF_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1Rl_0LX1LH_1LV1RK_1LX1RZ_0R\1Rd_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_1RD0LH_1LH0Rd_---1LH_1RZ0RK_0Rj1LH_0Rl0RK_1Rj1LW_1Rl1RK_1RL0LN_---0LP_1LH1LN_---1LP_0RB---_0RD---_1RB---_1RD---_1LU---_0LH---_1R\---_1LH---".
Definition tm0' := TM'_from_str "0RJ0R\_0RL1RK_1RJ1R\_1RL1LH_0LW0LF_1Rd0LH_1LW1LF_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1Rl_0LX1LH_1LV1RK_1LX1RZ_0R\1Rd_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_1RD0LH_1LH0Rd_---1LH_1RZ0RK_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_1RL0LH_---0Rd_1LH1LH_---0RK_0RB---_0RD---_1RB---_1RD---_1LU---_0LH---_1R\---_1LH---".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RH1RE_1RI---_1RA1LD_1RG1RE".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RH1RE_1RI1RK_1RA1LD_1RG1RE_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "LUFHKZdlD\".
Definition mp' := mp_from_str "LUFHKZdlD\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM65.


Module TM66.
Definition tm := TM_from_str "1RB0RE_0RC1RA_1LD1LA_1LB0LC_1RF1RC_---1RB".
Definition tm' := TM_from_str "1RB0RE_0RC1RA_1LD1LA_1LB0LC_1RF1RC_---0LB".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1RR---_1RL1L^_1RD0RL_1Rc0RR_0RQ0RB_0RS0RD_1RQ1RB_1RS1RD_0LP1RS_1RL1Rj_1LP1RD_1Rc1RR_1Rc0RD_1L^0RR_1RR1RD_1LF1RR_0L^0LF_0L`0LH_1L^1LF_1L`1LH_0RD0LP_0Rc1RL_1RD0LW_1Rc1L^_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0Rj0RR_0Rl0RT_1Rj1RR_1Rl1RT_---0LW_1RS1L^_---1LW_1RD0RR_---0RJ_---0RL_---1RJ_---1RL_---1RR_---1RL_---1RD_---1Rc".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1RR---_1RL1L^_1RD0RL_1Rc0RR_0RQ0RB_0RS0RD_1RQ1RB_1RS1RD_0LP1RS_1RL1Rj_1LP1RD_1Rc1RR_1Rc0RD_1L^0RR_1RR1RD_1LF1RR_0L^0LF_0L`0LH_1L^1LF_1L`1LH_0RD0LP_0Rc1RL_1RD0LW_1Rc1L^_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0Rj0RR_0Rl0RT_1Rj1RR_1Rl1RT_---0LW_1RS1L^_---1LW_1RD0RR_---1Rc_---0RL_---1RR_---1RL_---0LM_---0LO_---1LM_---1LO".
Definition tm1 := TM'_from_str "1LB0RA_0LJ0LC_1LB1LD_1RE1LB_1RI1RF_1RE1RG_1RH1RA_---0RE_1RA1RF_1RG1RA".
Definition tm2 := TM'_from_str "1LB0RA_0LJ0LC_1LB1LD_1RE1LB_1RI1RF_1RE1RG_1RH1RA_1RK0RE_1RA1RF_1RG1RA_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "R^WFLDcjSP".
Definition mp' := mp_from_str "R^WFLDcjSP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM66.


Module TM67.
Definition tm := TM_from_str "1LB1RE_1RC1LE_1RE1RD_1RC0RA_1LF0RA_---0LA".
Definition tm' := TM_from_str "1LB1RE_1RC1LE_1RE1RD_1RC1LA_1LF0RA_---0LA".
Definition tm0 := TM'_from_str "0R\0Rb_1Lp0Rd_1R\1Rb_0RC1Rd_0LN0LG_0LP1R\_1LN1LG_1LP1Rb_0RR---_0RT0Rb_1RR1LG_1RT1Rb_1LG0Lf_1RT0Lh_1RC1Lf_1RC1Lh_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0LG1Rd_1R\1R\_1LG1R\_1Rb1Rb_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1LG1RT_1RT1LN_1RC1RC_1RC0RC_---0RA_1LN0RC_---1RA_1LG1RC_0Ln1RT_0Lp1LN_1Ln1RC_1Lp0RC_---1RT_---1LN_---0Lh_---1LG_---0LE_---0LG_---1LE_---1LG".
Definition tm0' := TM'_from_str "0R\0Rb_1Lp0Rd_1R\1Rb_0RC1Rd_0LN0LG_0LP1R\_1LN1LG_1LP1Rb_0RR---_0RT0Rb_1RR1LG_1RT1Rb_1LG0Lf_1RT0Lh_1RC1Lf_1RC1Lh_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0LG1Rd_1R\1R\_1LG1R\_1Rb1Rb_0RR1RC_0RT0RC_1RR1Lh_1RT1RC_1LG0LF_1RT0LH_1RC1LF_1RC1LH_---0RA_1LN0RC_---1RA_1LG1RC_0Ln1RT_0Lp1LN_1Ln1RC_1Lp0RC_---1RT_---1LN_---0Lh_---1LG_---0LE_---0LG_---1LE_---1LG".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LB_1RH0LD_1LI0RE_1RF1RG_1RH1RE_1LC0RE_1RA1RF_---1LB".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LB_1RH0LD_1LI0RE_1RF1RG_1RH1RE_1LC0RE_1RA1RF_1RJ1LB_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "dGNhC\bTp".
Definition mp' := mp_from_str "dGNhC\bTp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM67.


Module TM68.
Definition tm := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LA_1RA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LD_1RA---".
Definition tm0 := TM'_from_str "0RJ0R\_0RL1RK_1RJ1R\_1RL1LH_0LW0LF_1Rd0LH_1LW1LF_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1Rl_0LX1LH_1LV1LH_1LX1RZ_0R\1Rd_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_1RD0LH_0LH0Rd_---1LH_1LH0RK_0Rj0R\_0Rl1RK_1Rj1R\_1Rl1LH_1RL0LF_---0LH_1LH1LF_---1LH_0RB---_0RD---_1RB---_1RD---_1LU---_0LH---_1R\---_1LH---".
Definition tm0' := TM'_from_str "0RJ0R\_0RL1RK_1RJ1R\_1RL1LH_0LW0LF_1Rd0LH_1LW1LF_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1Rl_0LX1LH_1LV1LH_1LX1RZ_0R\1Rd_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_1RD0LH_0LH0Rd_---1LH_1LH0RK_0Rj0Rl_0Rl1RK_1Rj1Rl_1Rl1LH_1RL0L]_---0L__1LH1L]_---1L__0RB---_0RD---_1RB---_1RD---_1LU---_0LH---_1R\---_1LH---".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RH1LD_1RI---_1RA1LD_1RG1RE".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RH1LD_1RI1RK_1RA1LD_1RG1RE_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "LUFHKZdlD\".
Definition mp' := mp_from_str "LUFHKZdlD\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM68.


Module TM69.
Definition tm := TM_from_str "1RB0RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_0LC---".
Definition tm' := TM_from_str "1RB1RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_1LD---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1LU0L^_1RD---_1RA1L^_1RJ---_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_0Lg1RL_0RJ0RS_1Lg1Rk_0Ri0Rd_1Rd0RA_0Lg0RC_1LU1RA_0L^1RC_0L^0RS_0L`0Lg_1L^0Rd_1L`---_0RL0Ra_0L^0Rc_1RL1Ra_0RS1Rc_0Le0RL_0Lg0L^_1Le0Rk_1Lg1L^_0RB0Lg_0RD0RJ_1RB0L^_1RD1RJ_1RS0LU_0L^0LW_1Rd1LU_---1LW_0Lg---_0RJ---_0L^---_1RJ---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_1LU0L^_1RD---_1RA1L^_1RJ---_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_0Lg1RL_0RJ0RS_1Lg1Rl_0Rj0Rd_1Rd0RA_0Lg0RC_1LU1RA_0L^1RC_0L^0RS_0L`0Lg_1L^0Rd_1L`---_0RL0Ra_0L^0Rc_1RL1Ra_0RS1Rc_0Le0RL_0Lg0L^_1Le0Rl_1Lg1L^_0RB0Lg_0RD0RJ_1RB0L^_1RD1RJ_1RS0LU_0L^0LW_1Rd1LU_---1LW_1Rd---_0Lg---_1LU---_0L^---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "0RB0RK_0RC0RG_1LD1RA_0LE0RC_0LF0LE_1RG1LD_1RH1RB_1RI1RJ_1RC1RG_0LE---_0LF---".
Definition tm2 := TM'_from_str "0RB0RK_0RC0RG_1LD1RA_0LE0RC_0LF0LE_1RG1LD_1RH1RB_1RI1RJ_1RC1RG_0LE1RL_0LF1RL_1RL1RL".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "AJSU^gdDLki".
Definition mp' := mp_from_str "AJSU^gdDLlj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM69.


Module TM70.
Definition tm := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1RE0LC_0RA1RC_1RE---".
Definition tm' := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1RE1RE_0RA1RC_1RE---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LO1RC_0LM---_1LO1RT_1LM---_0Rb0Rb_1LV0LV_1Rb1Rb_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rb0Rb_0Rd0LV_1Rb1Rb_1Rd0LU_1RJ0LU_1R[0LW_1Rj1LU_0LM1LW_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rb_0Rd0LU_0LV1Rb_---1LU_0Rb---_0Rd---_1Rb---_1Rd---_1RJ---_1R[---_1Rj---_0LM---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LO1RC_0LM---_1LO1RT_1LM---_0Rb0Rb_1LV0LV_1Rb1Rb_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rb0Rb_0Rd0Rd_1Rb1Rb_1Rd1Rd_1RJ1RJ_1R[1R[_1Rj1Rj_0LM0LM_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rb_0Rd0LU_0LV1Rb_---1LU_0Rb---_0Rd---_1Rb---_1Rd---_1RJ---_1R[---_1Rj---_0LM---".
Definition tm1 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI---_1RB1RJ_1RK0LG_1RA1RA".
Definition tm2 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI1RL_1RB1RJ_1RK0LG_1RA1RA_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "bCJVOUMjdT[".
Definition mp' := mp_from_str "bCJVOUMjdT[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM70.


Module TM71.
Definition tm := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1RE1RE_0RA1RC_1RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LO1RC_0LM---_1LO1RT_1LM---_0Rb0Rb_1LV0LV_1Rb1Rb_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rb0Rb_0Rd0Rd_1Rb1Rb_1Rd1Rd_1RJ1RJ_1R[1R[_1Rj1Rj_0LM0LM_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rb_0Rd0LU_0LV1Rb_---1LU_0Rb---_0Rd---_1Rb---_1Rd---_1RJ---_1R[---_1Rj---_0LM---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LO1RC_0LM---_1LO1RT_1LM---_0Rj0Rj_1LV0LV_1Rj1Rj_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rj0Rj_0Rl---_1Rj1Rj_1Rl---_1RJ0Le_1R[0Lg_1RZ1Le_0LM1Lg_0RY---_0R[---_1RY---_1R[---_0RC---_0RC---_0RT---_0RT---_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rj_0Rl0LU_0LV1Rj_---1LU".
Definition tm1 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI---_1RB1RJ_1RK0LG_1RA1RA".
Definition tm2 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI1RL_1RB1RJ_1RK0LG_1RA1RA_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "bCJVOUMjdT[".
Definition mp' := mp_from_str "jCJVOUMZlT[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM71.


Module TM72.
Definition tm := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC".
Definition tm' := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1LC1RE_0RA1RC_1RE---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LO1RC_0LM---_1LO1RT_1LM---_0Rj0Rj_1LV0LV_1Rj1Rj_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rj0Rj_0Rl---_1Rj1Rj_1Rl---_1RJ0Le_1R[0Lg_1RZ1Le_0LM1Lg_0RY---_0R[---_1RY---_1R[---_0RC---_0RC---_0RT---_0RT---_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rj_0Rl0LU_0LV1Rj_---1LU".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LO1RC_0LM---_1LO1RT_1LM---_0Rb0Rb_1LV0LV_1Rb1Rb_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rb0Rb_1LV0Rd_1Rb1Rb_1LU1Rd_0LV1RJ_0LX1R[_1LV1Rj_1LX0LM_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rb_0Rd0LU_0LV1Rb_---1LU_0Rb---_0Rd---_1Rb---_1Rd---_1RJ---_1R[---_1Rj---_0LM---".
Definition tm1 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI---_1RB1RJ_1RK0LG_1RA1RA".
Definition tm2 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI1RL_1RB1RJ_1RK0LG_1RA1RA_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "jCJVOUMZlT[".
Definition mp' := mp_from_str "bCJVOUMjdT[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM72.


Module TM73.
Definition tm := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1LC1RE_0RA1RC_1RE---".
Definition tm' := TM_from_str "1RB1RE_1LC0LD_0RB0LB_0RE0LB_1RF---_0RA1RC".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LO1RC_0LM---_1LO1RT_1LM---_0Rb0Rb_1LV0LV_1Rb1Rb_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rb0Rb_1LV0Rd_1Rb1Rb_1LU1Rd_0LV1RJ_0LX1R[_1LV1Rj_1LX0LM_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rb_0Rd0LU_0LV1Rb_---1LU_0Rb---_0Rd---_1Rb---_1Rd---_1RJ---_1R[---_1Rj---_0LM---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LO1RC_0LM---_1LO1RT_1LM---_0Rj0Rj_1LV0LV_1Rj1Rj_1L]0L]_0LV0L]_0LX0L__1LV1L]_1LX1L__0RI0RC_0RK0RC_1RI0LO_1RK0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Ra0RC_0Rc0RC_1Ra0LO_1Rc0LM_0RC0LM_---0LO_0RT1LM_---1LO_0Rj---_0Rl---_1Rj---_1Rl---_1RJ---_1RK---_1Rb---_0LM---_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rj_0Rl0L]_0LV1Rj_---1L]".
Definition tm1 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI---_1RB1RJ_1RK0LG_1RA1RA".
Definition tm2 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI1RL_1RB1RJ_1RK0LG_1RA1RA_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "bCJVOUMjdT[".
Definition mp' := mp_from_str "jCJVO]MblTK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM73.


Module TM74.
Definition tm := TM_from_str "1RB1RE_1LC0LD_0RB0LB_0RE0LB_1RF---_0RA1RC".
Definition tm' := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1LE_0RB---_0RA1RC".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LO1RC_0LM---_1LO1RT_1LM---_0Rj0Rj_1LV0LV_1Rj1Rj_1L]0L]_0LV0L]_0LX0L__1LV1L]_1LX1L__0RI0RC_0RK0RC_1RI0LO_1RK0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Ra0RC_0Rc0RC_1Ra0LO_1Rc0LM_0RC0LM_---0LO_0RT1LM_---1LO_0Rj---_0Rl---_1Rj---_1Rl---_1RJ---_1RK---_1Rb---_0LM---_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rj_0Rl0L]_0LV1Rj_---1L]".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LO1RC_0LM---_1LO1RT_1LM---_0Rj0Rj_1LV0LV_1Rj1Rj_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW_0RY0RC_0R[0RC_1RY0LO_1R[0LM_0RC0LM_0RC0LO_0RT1LM_0RT1LO_0Rj0Rj_0Rl---_1Rj1Rj_1Rl---_1RJ0Lf_1R[0Lh_1RZ1Lf_0LM1Lh_0RI---_0RK---_1RI---_1RK---_0RC---_0RC---_0RT---_0RT---_0RA0RR_0RC0RT_1RA1RR_1RC1RT_1LV1Rj_0Rl0LU_0LV1Rj_---1LU".
Definition tm1 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI---_1RB1RJ_1RK0LG_1RA1RA".
Definition tm2 := TM'_from_str "0RB0RJ_1RC1RH_1LD0LD_0RB0LE_1LD1LF_0RB0LG_0LD0LF_0RI1RL_1RB1RJ_1RK0LG_1RA1RA_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "jCJVO]MblTK".
Definition mp' := mp_from_str "jCJVOUMZlT[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM74.


Module TM75.
Definition tm := TM_from_str "1LB0RE_1LC0RF_0RD0LC_1LA1RD_1RB0RE_---0LE".
Definition tm' := TM_from_str "1LB0RE_1LC1RF_0RD0LC_1LA1RD_1RB0RE_---1LC".
Definition tm0 := TM'_from_str "0R\0Ra_1LP0Rc_1LW1Ra_1LU1Rc_0LN1LP_0LP0RJ_1LN0Rk_1LP0Ra_0RZ0Ri_1LP0Rk_1RZ1Ri_1LU1Rk_0LV---_0LX0LW_1LV---_1LX1LW_0RY1LX_0R[0LP_1RY1LW_1R[0LU_0LP0LU_0Ra0LW_1LP1LU_0R\1LW_1LX0RZ_0Ra0R\_1LW1RZ_1Ra1R\_0LF0RJ_0LH1Ra_1LF0Ra_1LH1R\_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1LP_---0RJ_1LW0Rk_1LU0Ra_---1LP_---0RJ_---1LU_---1RJ_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0R\0Ra_1LP0Rc_1LW1Ra_1LU1Rc_0LN1LP_0LP0RJ_1LN0Rl_1LP0Ra_0RZ0Rj_1LP0Rl_1RZ1Rj_1LU1Rl_0LV---_0LX0LW_1LV---_1LX1LW_0RY1LX_0R[0LP_1RY1LW_1R[0LU_0LP0LU_0Ra0LW_1LP1LU_0R\1LW_1LX0RZ_0Ra0R\_1LW1RZ_1Ra1R\_0LF0RJ_0LH1Ra_1LF0Ra_1LH1R\_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1LP_---0RJ_1LW0Rl_1LU0Ra_---0RZ_---1LP_---1RZ_---1LU_---0LV_---0LX_---1LV_---1LX".
Definition tm1 := TM'_from_str "1LB0RH_1LC1LD_0RF1LD_1LB1LE_0LB0LE_1RG1RF_0RA0RG_---1LE".
Definition tm2 := TM'_from_str "1LB0RH_1LC1LD_0RF1LD_1LB1LE_0LB0LE_1RG1RF_0RA0RG_1RI1LE_1RI1RI".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "JPXWU\ak".
Definition mp' := mp_from_str "JPXWU\al".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM75.


Module TM76.
Definition tm := TM_from_str "1LB0LE_1LC0RC_1RD1LF_1RE0RD_1LA0LB_0LE---".
Definition tm' := TM_from_str "1LB0LE_1LC0RC_1RD0LF_1RE0RD_1LA0LB_1RE---".
Definition tm0 := TM'_from_str "1RY0LP_1LF0LV_1Lp0Lg_1LM0Rd_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0R[0RQ_1Lg0RS_1R[1RQ_---1RS_0LV0Rd_0LX0Lg_1LV0R[_1LX1Lg_0RZ1LF_0R\---_1RZ1LM_1R\---_1LM0Ln_1Rb0Lp_1RZ1Ln_1RY1Lp_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lg1LF_0Rd0Rb_1Lg0RZ_0R[0RY_1LX1Rb_1LF0RZ_1Lg0Lp_1LM1RZ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0LP---_0LV---_0Lg---_0Rd---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "1RY0LP_1LF0LV_1Lo0Lg_1LM0Rd_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0R[0RQ_1Lg0RS_1R[1RQ_---1RS_0LV0Rd_0LX0Lg_1LV0R[_1LX1Lg_0RZ1LF_0R\---_1RZ1LM_1R\---_1LM0Lm_1Rb0Lo_1RZ1Lm_1RY1Lo_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lg1LF_0Rd0Rb_1Lg0RZ_0R[0RY_1LX1Rb_1LF0RZ_1Lg0Lo_1LM1RZ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0Rb---_0Rd---_1Rb---_1Rd---_0Lg---_0Rd---_1Lg---_0R[---".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0RA_1RD0LL_1LE0RJ_0LG0LF_1LE1LB_1LH1LF_1RI1LL_0RD0RI_0RA0RK_1RD1RI_1LF---".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0RA_1RD0LL_1LE0RJ_0LG0LF_1LE1LB_1LH1LF_1RI1LL_0RD0RI_0RA0RK_1RD1RI_1LF1RM_1RM1RM".
Definition l0 := [1;0;0;0;0;1;0;0]%N.
Definition mp := mp_from_str "dMVbFgPXYZ[p".
Definition mp' := mp_from_str "dMVbFgPXYZ[o".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM76.


Module TM77.
Definition tm := TM_from_str "1LB0LE_1LC0RC_1RD0LF_1RE0RD_1LA0LB_1RE---".
Definition tm' := TM_from_str "1LB0RC_1LC0RC_1RD1LF_1RE0RD_1LA0LB_0LE---".
Definition tm0 := TM'_from_str "1RY0LP_1LF0LV_1Lo0Lg_1LM0Rd_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0R[0RQ_1Lg0RS_1R[1RQ_---1RS_0LV0Rd_0LX0Lg_1LV0R[_1LX1Lg_0RZ1LF_0R\---_1RZ1LM_1R\---_1LM0Lm_1Rb0Lo_1RZ1Lm_1RY1Lo_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lg1LF_0Rd0Rb_1Lg0RZ_0R[0RY_1LX1Rb_1LF0RZ_1Lg0Lo_1LM1RZ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0Rb---_0Rd---_1Rb---_1Rd---_0Lg---_0Rd---_1Lg---_0R[---".
Definition tm0' := TM'_from_str "1RY0RQ_1LF0RS_1Lp1RQ_1LM1RS_0LN0Rd_0LP0Lg_1LN0R[_1LP1Lg_0R[0RQ_1Lg0RS_1R[1RQ_---1RS_0LV0Rd_0LX0Lg_1LV0R[_1LX1Lg_0RZ1LF_0R\---_1RZ1LM_1R\---_1LM0Ln_1Rb0Lp_1RZ1Ln_1RY1Lp_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lg1LF_0Rd0Rb_1Lg0RZ_0R[0RY_1LX1Rb_1LF0RZ_1Lg0Lp_1LM1RZ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0LP---_0LV---_0Lg---_0Rd---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0RA_1RD0LL_1LE0RJ_0LG0LF_1LE1LB_1LH1LF_1RI1LL_0RD0RI_0RA0RK_1RD1RI_1LF---".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0RA_1RD0LL_1LE0RJ_0LG0LF_1LE1LB_1LH1LF_1RI1LL_0RD0RI_0RA0RK_1RD1RI_1LF1RM_1RM1RM".
Definition l0 := [1;0;0;0;0;1;0;0]%N.
Definition mp := mp_from_str "dMVbFgPXYZ[o".
Definition mp' := mp_from_str "dMVbFgPXYZ[p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM77.


Module TM78.
Definition tm := TM_from_str "1LB0LE_1RC1LA_1RD0RC_1RA0RA_1LA0LF_1RE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_0LE---".
Definition tm0 := TM'_from_str "0RS0LP_1LP0Lg_1RS0Lg_1Lg---_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1RQ_0RT1LF_1RR1LH_1RT1Lm_1RD0LF_1RZ0LH_1RC1LF_1RQ1LH_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_1Lg0RD_1RS0RZ_---0RC_0Lg0RQ_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0LH1RZ_0Lm0LF_1LH1RQ_1Lm1LF_1RQ1LF_1LF---_1LH1Lm_1Lm---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0Lg---_------_1Lg---".
Definition tm0' := TM'_from_str "0RJ1RI_0RL1L^_1RJ1L`_1RL1Ln_1R\0L^_1RR0L`_1R[1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Lg0R\_1RK0RR_---0R[_0Lg0RI_0RZ0RY_0R\0R[_1RZ1RY_1R\1R[_0L`1RR_0Ln0L^_1L`1RI_1Ln1L^_0RK0LH_1LH0Lg_1RK0Lg_1Lg---_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI1L^_1L^---_1L`1Ln_1Ln---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0LH---_0Lg---_0Lg---_------_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB---_1LC1LI_0LD0LB_1RE1LH_0RF0RE_0RA0RG_1RJ0LB_1LD1LB_0LB---_1RF1RE".
Definition tm2 := TM'_from_str "1LB1RK_1LC1LI_0LD0LB_1RE1LH_0RF0RE_0RA0RG_1RJ0LB_1LD1LB_0LB1RK_1RF1RE_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;0]%N.
Definition mp := mp_from_str "DgFPQZCHmS".
Definition mp' := mp_from_str "\g^HIR[`nK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM78.


Module TM79.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_0LE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_1RA---".
Definition tm0 := TM'_from_str "0RJ1RI_0RL1L^_1RJ1L`_1RL1Ln_1R\0L^_1RR0L`_1R[1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Lg0R\_1RK0RR_---0R[_0Lg0RI_0RZ0RY_0R\0R[_1RZ1RY_1R\1R[_0L`1RR_0Ln0L^_1L`1RI_1Ln1L^_0RK0LH_1LH0Lg_1RK0Lg_1Lg---_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI1L^_1L^---_1L`1Ln_1Ln---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0LH---_0Lg---_0Lg---_------_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ1RI_0RL1L^_1RJ1L`_1RL1Ln_1R\0L^_1RR0L`_1R[1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Lg0R\_1RK0RR_---0R[_0Lg0RI_0RZ0RY_0R\0R[_1RZ1RY_1R\1R[_0L`1RR_0Ln0L^_1L`1RI_1Ln1L^_0RK0LH_1LH0Lg_1RK0Lg_1Lg---_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI1L^_1L^---_1L`1Ln_1Ln---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0RB---_0RD---_1RB---_1RD---_1RT---_0Lg---_1RK---_1Lg---".
Definition tm1 := TM'_from_str "1LB---_1LC1LI_0LD0LB_1RE1LH_0RF0RE_0RA0RG_1RJ0LB_1LD1LB_0LB---_1RF1RE".
Definition tm2 := TM'_from_str "1LB1RK_1LC1LI_0LD0LB_1RE1LH_0RF0RE_0RA0RG_1RJ0LB_1LD1LB_0LB1RK_1RF1RE_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;0]%N.
Definition mp := mp_from_str "\g^HIR[`nK".
Definition mp' := mp_from_str "\g^HIR[`nK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM79.


Module TM80.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RA1LC_1LA0RC_0LF---_0RD1LB".
Definition tm' := TM_from_str "1LB0RD_1RC1LE_1RA1LC_1LA0RC_0LF---_0RD1LB".
Definition tm0 := TM'_from_str "1RQ0RY_1Lo0R[_1LX1RY_---1R[_0LN0LP_0LP0RB_1LN1LP_1LP0R[_0R[1LP_1RQ---_1R[1LN_1LX---_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RB0R[_0RD1RQ_1RB1R[_1RD1LX_0Lh0LV_1Lh0LX_1Lh1LV_1RQ1LX_1LX0RQ_0RQ0RS_1Lh1RQ_1RQ1RS_0LF1Lo_0LH1Lh_1LF0R[_1LH1RQ_1LX---_0LX---_1Lh---_0Lh---_0Lm---_0Lo---_1Lm---_1Lo---_0RY1RQ_0R[1Lo_1RY1LX_1R[---_0LP0LN_0RB0LP_1LP1LN_0R[1LP".
Definition tm0' := TM'_from_str "1RQ0RY_1Lo0R[_1LX1RY_---1R[_0LN0LP_0LP0RB_1LN1LP_1LP0R[_0RR1LP_0RT---_1RR1LN_1RT---_---0Lf_0LX0Lh_1R[1Lf_1LX1Lh_0RB0R[_0RD1RQ_1RB1R[_1RD1LX_0Lh0LV_1Lh0LX_1Lh1LV_1RQ1LX_1LX0RQ_0RQ0RS_1Lh1RQ_1RQ1RS_0LF1Lo_0LH1Lh_1LF0R[_1LH1RQ_1LX---_0LX---_1Lh---_0Lh---_0Lm---_0Lo---_1Lm---_1Lo---_0RY1RQ_0R[1Lo_1RY1LX_1R[---_0LP0LN_0RB0LP_1LP1LN_0R[1LP".
Definition tm1 := TM'_from_str "1LB0RH_1LC1LE_1LF1LD_1LB---_0LF0LD_1RG1LF_0RA0RH_1LD1RG".
Definition tm2 := TM'_from_str "1LB0RH_1LC1LE_1LF1LD_1LB1RI_0LF0LD_1RG1LF_0RA0RH_1LD1RG_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "BoPhNXQ[".
Definition mp' := mp_from_str "BoPhNXQ[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM80.


Module TM81.
Definition tm := TM_from_str "1RB---_0RC0RA_0LD0RE_1RE0LE_0RF0LC_1LC1RB".
Definition tm' := TM_from_str "1LB---_0RC0LE_1LE1RD_0RE0RA_0LF0RB_1RB0LB".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1Rk---_1RJ---_1Ra---_------_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_1Le0RS_0Ri---_1RJ0RC_1Le---_0Rk0Ra_0L_0Rc_1Rk1Ra_0LU1Rc_0L]1RJ_0L_0L]_1L]0RJ_1L_1L]_0Rb1RJ_0Rd0L]_1Rb1Le_1Rd1RJ_1Le0Le_1RJ0Lg_1RJ1Le_0RJ1Lg_0Ri1Le_0Rk0Ri_1Ri0Le_1Rk1Ri_0L_0LU_0RS0LW_1L_1LU_0RC1LW_1RJ0RJ_1Le0RL_1Le1RJ_0Le1RL_0LV1Rk_0LX1RJ_1LV1Ra_1LX---".
Definition tm0' := TM'_from_str "0RZ---_1Lm---_1RZ---_0RZ---_0LN---_0LP---_1LN---_1LP---_0RQ1LM_0RS0RQ_1RQ0LM_1RS1RQ_0Lo0Le_0Rc0Lg_1Lo1Le_0RC1Lg_1RZ0RZ_1LM0R\_1LM1RZ_0LM1R\_0Lf1RS_0Lh1RZ_1Lf1RI_1Lh---_0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_1LM0Rc_0RQ---_1RZ0RC_1LM---_0RS0RI_0Lo0RK_1RS1RI_0Le1RK_0Lm1RZ_0Lo0Lm_1Lm0RZ_1Lo1Lm_0RJ1RZ_0RL0Lm_1RJ1LM_1RL1RZ_1LM0LM_1RZ0LO_1RZ1LM_0RZ1LO".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RG_0LF0LD_0LE1RG_1LC0LC_1RG1LC_0RA0RJ_0RI1LC_1RG0RG_1RG---".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RG_0LF0LD_0LE1RG_1LC0LC_1RG1LC_0RA0RJ_0RI1LC_1RG0RG_1RG1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "SkeU]_JaiC".
Definition mp' := mp_from_str "cSMemoZIQC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM81.


Module TM82.
Definition tm := TM_from_str "1LB---_0LC0RD_1RD1RA_0RE0LE_1LB1RF_0RB1RC".
Definition tm' := TM_from_str "1LB1RE_0LC0RD_1RD0RF_0RA0LA_0RB1RC_0LA---".
Definition tm0 := TM'_from_str "1Rj---_0LW---_1LN---_0LN---_0LN---_0LP---_1LN---_1LP---_0Rc0RY_0LW0R[_1Rc1RY_0LN1R[_0LU1Rj_0LW0LN_1LU0Rj_1LW1LN_0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_1LN0LN_1Rc---_1Rj1LN_1RY---_0Ra0LW_0Rc0RK_1Ra0LN_1Rc1RK_0LW0Le_0RK0Lg_1LW1Le_0RT1Lg_1Rj0Rj_0LW0Rl_1LN1Rj_0LN1Rl_0LN1Rc_0LP1R\_1LN1RY_1LP1RD_0RI0RR_0RK0RT_1RI1RR_1RK1RT_1LN1Rc_0Ra0LN_1Rj1RK_0LW---".
Definition tm0' := TM'_from_str "1Rb0Rb_0LW0Rd_1LN1Rb_0LN1Rd_0LN1RC_0LP1R\_1LN1RY_1LP1Rk_0RC0RY_0LW0R[_1RC1RY_0LN1R[_0LU1Rb_0LW0LN_1LU0Rb_1LW1LN_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1LN0LN_1RC---_1Rb1LN_1RY---_0RA0LW_0RC0RK_1RA0LN_1RC1RK_0LW0LE_0RK0LG_1LW1LE_0RT1LG_0RI0RR_0RK0RT_1RI1RR_1RK1RT_1LN1RC_0RA0LN_1Rb1RK_0LW---_0LW---_0RK---_0LN---_1RK---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_0RE0RH_1RA1RF_0RG0LC_1RD0RD_1RI1RJ_1RA1RE_0LB---".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_0RE0RH_1RA1RF_0RG0LC_1RD0RD_1RI1RJ_1RA1RE_0LB1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "cNWjKYaT\D".
Definition mp' := mp_from_str "CNWbKYAT\k".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM82.


Module TM83.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LC---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1RR_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0LF_1RI---_1L_1LF_0L_---_1RR---_0RI---_0L_---_1RI---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1RR_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0LF_1RI---_1L_1LF_0L_---_1Rj---_1RR---_1L_---_0L_---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Iai".
Definition mp' := mp_from_str "RF_U[Iaj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM83.


Module TM84.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LC---".
Definition tm' := TM_from_str "1RB0LD_0LC1RE_1LA0RD_0RB0LC_0LE0RF_1RC---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1RR_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0LF_1RI---_1L_1LF_0L_---_1Rj---_1RR---_1L_---_0L_---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Rb1L]_1Rk1L__1RR0Rb_0RI0Rd_0L_1Rb_1RI1Rd_0LU1LF_0LW1RR_1LU0R[_1LW---_0Rd0RY_1LF0R[_1Rd1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Rb_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rk1LW_0Le0Ri_0RR0Rk_1LF1Ri_1RR1Rk_0Le1LF_0Lg---_1Le0R[_1Lg---_0RR---_0RT---_1RR---_1RT---_0L_---_1RI---_1L_---_0L_---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Iaj".
Definition mp' := mp_from_str "RF_U[Ibk".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM84.


Module TM85.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_0LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LB---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW0LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0LU_1RI---_1L_1LU_0L_---_1RR---_0LF---_0L_---_1RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW0LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0LU_1RI---_1L_1LU_0L_---_0LF---_0RR---_1RR---_1RR---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Iaj".
Definition mp' := mp_from_str "RF_U[Iai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM85.


Module TM86.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_1LB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LA---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0LW_1RI---_1L_1LW_0L_---_1LF---_0Ri---_0Ra---_1Ri---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0L__1RI---_1L_1L__0L_---_0Rc---_1LF---_1Rc---_1LU---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Iai".
Definition mp' := mp_from_str "RF_U[Iaj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM86.


Module TM87.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LA---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LD---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0L__1RI---_1L_1L__0L_---_0Rc---_1LF---_1Rc---_1LU---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0LW_1RI---_1L_1LW_0L_---_0Ra---_1LF---_1Ra---_0Ra---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Iaj".
Definition mp' := mp_from_str "RF_U[Iaj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM87.


Module TM88.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LE---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0LW_1RI---_1L_1LW_0L_---_0Ra---_1LF---_1Ra---_0Ra---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0L__1RI---_1L_1L__0L_---_1LF---_1LF---_1LU---_1LU---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Iaj".
Definition mp' := mp_from_str "RF_U[Iai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM88.


Module TM89.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_0LE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1LD---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Ri1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0L__1RI---_1L_1L__0L_---_1LF---_1LF---_1L]---_1L]---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Rj1L__0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0L__1RI---_1L_1L__0L_---_0Ra---_1LF---_1Ra---_1L]---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_][Iai".
Definition mp' := mp_from_str "RF_][Iaj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM89.


Module TM90.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_1LB---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Rj1L__0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0L__1RI---_1L_1L__0L_---_0Ra---_1LF---_1Ra---_1L]---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Ri1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0LW_1RI---_1L_1LW_0L_---_1LF---_0Ri---_0Ra---_1Ri---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_][Iaj".
Definition mp' := mp_from_str "RF_][Iai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM90.


Module TM91.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_0LB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RD---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0RL1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0RL_1RS---_0Ri0RJ_1LE0RL_1Ri1RJ_1Ri1RL_0LN1RZ_0LP1RZ_1LN1Ri_1LP1Ri_0RS0RJ_1LE0RL_1RS1RJ_0Le1RL_0LE1RZ_0LG1RZ_1LE1Ri_1LG1Ri_0RZ---_0LE---_1RZ---_1RZ---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0RL1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0RL_1RS---_0Ri0RJ_1LE0RL_1Ri1RJ_1Ri1RL_0LN1RZ_0LP1RZ_1LN1Ri_1LP1Ri_0RS0Ra_1LE0Rc_1RS1Ra_0Le1Rc_0LE1RZ_0LG0RS_1LE1Ri_1LG0Ra_0RZ---_0R\---_1RZ---_1R\---_0Lg---_1RS---_1Lg---_1RS---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RF_1RA1RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RF_1RA1RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMeLSi".
Definition mp' := mp_from_str "ZEMeLSi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM91.


Module TM92.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RD---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_0LB---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0RL1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0RL_1RS---_0Ri0RJ_1LE0RL_1Ri1RJ_1Ri1RL_0LN1RZ_0LP1RZ_1LN1Ri_1LP1Ri_0RS0Ra_1LE0Rc_1RS1Ra_0Le1Rc_0LE1RZ_0LG0RS_1LE1Ri_1LG0Ra_0RZ---_0R\---_1RZ---_1R\---_0Lg---_1RS---_1Lg---_1RS---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0RL1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0RL_1RS---_0Ri0RJ_1LE0RL_1Ri1RJ_1Ri1RL_0LN1RZ_0LP1RZ_1LN1Ri_1LP1Ri_0RS0Ra_1LE0Rc_1RS1Ra_0Le1Rc_0LE1RZ_0LG0RS_1LE1Ri_1LG0Ra_0RZ---_0LE---_1RZ---_1RZ---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RF_1RA1RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RF_1RA1RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMeLSi".
Definition mp' := mp_from_str "ZEMeLSi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM92.


Module TM93.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_0LB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RD---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0RL1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0RL_1RS---_0Ri0RJ_1LE0RL_1Ri1RJ_1Ri1RL_0LN1RZ_0LP1RZ_1LN1Ri_1LP1Ri_0RS0Ra_1LE0Rc_1RS1Ra_0Le1Rc_0LE1RZ_0LG0RS_1LE1Ri_1LG0Ra_0RZ---_0LE---_1RZ---_1RZ---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0RL1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0RL_1RS---_0Ri0RJ_1LE0RL_1Ri1RJ_1Ri1RL_0LN1RZ_0LP1RZ_1LN1Ri_1LP1Ri_0RS0RJ_1LE0RL_1RS1RJ_0Le1RL_0LE1RZ_0LG1RZ_1LE1Ri_1LG1Ri_0RZ---_0R\---_1RZ---_1R\---_0Lg---_1RS---_1Lg---_1RS---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RF_1RA1RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RF_1RA1RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMeLSi".
Definition mp' := mp_from_str "ZEMeLSi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM93.


Module TM94.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA0RF_0LA---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0RC---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1RQ1LM_1RQ1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_0RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1LE_1RS0RZ_1Lg0Rc_1Ri0RQ_0RQ0Ra_1LE0Rc_1RQ1Ra_1RQ1Rc_0LN1RZ_0LP0RS_1LN1RQ_1LP---_0RS0Ri_1LE0Rk_1RS1Ri_0Le1Rk_0LE1RZ_0LG---_1LE1RQ_1LG---_0RS---_1LE---_1RS---_0Le---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1RQ1LM_1RQ1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_0RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1LE_1RS0RZ_1Lg0Rc_1Rj0RQ_0RQ0Ra_1LE0Rc_1RQ1Ra_1RQ1Rc_0LN1RZ_0LP0RS_1LN1RQ_1LP---_0RS0Rj_1LE0Rl_1RS1Rj_0Le1Rl_0LE1RZ_0LG---_1LE1RQ_1LG---_0RQ---_0RS---_1RQ---_1RS---_1LE---_0RZ---_0Rc---_0RQ---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA0RG_0RF---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA0RG_0RF1RI_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMecSQi".
Definition mp' := mp_from_str "ZEMecSQj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM94.


Module TM95.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0RC---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0LD---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1RQ1LM_1RQ1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_0RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1LE_1RS0RZ_1Lg0Rc_1Rj0RQ_0RQ0Ra_1LE0Rc_1RQ1Ra_1RQ1Rc_0LN1RZ_0LP0RS_1LN1RQ_1LP---_0RS0Rj_1LE0Rl_1RS1Rj_0Le1Rl_0LE1RZ_0LG---_1LE1RQ_1LG---_0RQ---_0RS---_1RQ---_1RS---_1LE---_0RZ---_0Rc---_0RQ---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1RQ1LM_1RQ1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_0RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1LE_1RS0RZ_1Lg0Rc_1Rj0RQ_0RQ0Ra_1LE0Rc_1RQ1Ra_1RQ1Rc_0LN1RZ_0LP0RS_1LN1RQ_1LP---_0RS0Rj_1LE0Rl_1RS1Rj_0Le1Rl_0LE1RZ_0LG---_1LE1RQ_1LG---_0RZ---_0RS---_0Lg---_1RS---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA0RG_0RF---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA0RG_0RF1RI_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMecSQj".
Definition mp' := mp_from_str "ZEMecSQj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM95.


Module TM96.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0LD---".
Definition tm' := TM_from_str "1RB0LE_0RC---_1RD0RC_1LE0RF_0RC0LF_0LA1RB".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1RQ1LM_1RQ1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_0RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1LE_1RS0RZ_1Lg0Rc_1Rj0RQ_0RQ0Ra_1LE0Rc_1RQ1Ra_1RQ1Rc_0LN1RZ_0LP0RS_1LN1RQ_1LP---_0RS0Rj_1LE0Rl_1RS1Rj_0Le1Rl_0LE1RZ_0LG---_1LE1RQ_1LG---_0RZ---_0RS---_0Lg---_1RS---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0Le_---0Lg_1RQ1Le_---1Lg_0RQ---_0RS---_1RQ---_1RS---_1LE---_0RZ---_0Rk---_0RQ---_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lo1LE_1RS0RZ_1Lo0Rk_1RJ0RQ_0RQ0Ri_1LE0Rk_1RQ1Ri_1RQ1Rk_0Lf1RZ_0Lh0RS_1Lf1RQ_1Lh---_0RQ1RZ_0RS0RS_1RQ0Le_1RS1RS_1LE0Lm_0RZ0Lo_0Rk1Lm_0RQ1Lo_0RS0RJ_1LE0RL_1RS1RJ_0Lm1RL_0LE1RZ_0LG---_1LE1RQ_1LG---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA0RG_0RF---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA0RG_0RF1RI_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMecSQj".
Definition mp' := mp_from_str "ZEemkSQJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM96.


Module TM97.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA1RB_1RD---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA1RB_0LB---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0Rc_1RJ---_0Ri0Ra_1LE0Rc_1Ri1Ra_1Ri1Rc_0LN1RZ_0LP0RS_1LN1Ri_1LP0RS_0RS0RJ_1LE0RL_1RS1RJ_0Le1RL_0LE1RZ_0LG1RZ_1LE1Ri_1LG1Ri_0RZ---_0R\---_1RZ---_1R\---_0Lg---_1RS---_1Lg---_1RJ---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0Rc_1RJ---_0Ri0Ra_1LE0Rc_1Ri1Ra_1Ri1Rc_0LN1RZ_0LP0RS_1LN1Ri_1LP0RS_0RS0RJ_1LE0RL_1RS1RJ_0Le1RL_0LE1RZ_0LG1RZ_1LE1Ri_1LG1Ri_0RZ---_0LE---_1RZ---_1RZ---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA---_0RF0RF".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA1RI_0RF0RF_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMecSiJ".
Definition mp' := mp_from_str "ZEMecSiJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM97.


Module TM98.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA0RE_0LB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA0RE_1RD---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0Rc_1Ra---_0Ri0Ra_1LE0Rc_1Ri1Ra_1Ri1Rc_0LN1RZ_0LP0RS_1LN1Ri_1LP0Ra_0RS0Ra_1LE0Rc_1RS1Ra_0Le1Rc_0LE1RZ_0LG0RS_1LE1Ri_1LG0Ra_0RZ---_0LE---_1RZ---_1RZ---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LE_1RJ1RZ_1RL1RZ_1RZ0LM_1RZ0LO_1Ri1LM_1Ri1LO_0RQ1RZ_0RS0RS_1RQ0LM_1RS1RS_1LE0Le_0RZ0Lg_0Rc1Le_---1Lg_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1LE_1RS---_1Lg0Rc_1Ra---_0Ri0Ra_1LE0Rc_1Ri1Ra_1Ri1Rc_0LN1RZ_0LP0RS_1LN1Ri_1LP0Ra_0RS0Ra_1LE0Rc_1RS1Ra_0Le1Rc_0LE1RZ_0LG0RS_1LE1Ri_1LG0Ra_0RZ---_0R\---_1RZ---_1R\---_0Lg---_1RS---_1Lg---_1Ra---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA---_0RF0RH".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RA_1RF1RH_1RA1RG_0RA1RI_0RF0RH_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ZEMecSia".
Definition mp' := mp_from_str "ZEMecSia".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM98.


Module TM99.
Definition tm := TM_from_str "1LB1RF_1LC1RD_1RB1RE_1RE0RD_0RA0LE_1LD---".
Definition tm' := TM_from_str "1LB0RF_1LC1RD_1RB1RE_1RE0RD_0RA0LE_0RD---".
Definition tm0 := TM'_from_str "1R[0Rj_0R[0Rl_1Le1Rj_1R[1Rl_0LN0Rb_0LP---_1LN0RY_1LP---_0R\0RZ_0LX0R\_1R\1RZ_0Le1R\_0LV1RC_0LX1Rb_1LV0Le_1LX1RY_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0Le1Le_1Rd0Le_1Le1Rj_1R[1Le_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1Le0RC_0Le0Rb_1Rj0LX_1Le0RY_0RA1R[_0RC0LX_1RA1Le_1RC0Le_0LX0Le_0RY0Lg_1LX1Le_---1Lg_0LX---_0RY---_0Le---_1RY---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "1R[0Ri_0R[0Rk_1Le1Ri_1R[1Rk_0LN0Rb_0LP---_1LN0RY_1LP---_0R\0RZ_0LX0R\_1R\1RZ_0Le1R\_0LV1RC_0LX1Rb_1LV0Le_1LX1RY_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0Le1Le_1Rd0Le_1Le1Ri_1R[1Le_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1Le0RC_0Le0Rb_1Ri0LX_1Le0RY_0RA1R[_0RC0LX_1RA1Le_1RC0Le_0LX0Le_0RY0Lg_1LX1Le_---1Lg_0RY---_0R[---_1RY---_1R[---_0RC---_0Rb---_0LX---_0RY---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RD1LB_1RE1RG_0RA0LC_0RG---_0RE0RG".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RD1LB_1RE1RG_0RA0LC_0RG1RH_0RE0RG_1RH1RH".
Definition l0 := [1;1;0;1;0;0;0;0]%N.
Definition mp := mp_from_str "CeX[bjY".
Definition mp' := mp_from_str "CeX[biY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM99.


Module TM100.
Definition tm := TM_from_str "1RB0RF_0RC0LB_1RD---_1RE0LD_1LA0RA_1LD1LF".
Definition tm' := TM_from_str "1RB0RF_0RC1RE_1RD---_1RE0LD_1LA0RA_1LD1LF".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1RZ1RJ_0LM0L`_---1Ri_1LM1L`_0RQ0RZ_0RS0Rd_1RQ1RZ_1RS0LM_0Rd0LM_---0LO_0L`1LM_---1LO_0RZ---_0R\---_1RZ---_1R\---_1L_---_0L]---_1RC---_1L]---_0Rb1Ri_0Rd0L`_1Rb1L__1Rd0L]_0L`0L]_1RJ0L__1L`1L]_1Ri1L__0Rd0RA_1Ri0RC_0LM1RA_1L_1RC_0LF0RS_0LH0RC_1LF0Rd_1LH1Ri_0RC1Ri_1L`1L`_1RC1L__1L]1Lp_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1RZ1RJ_1L_0L`_---1Ri_1RC1L`_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_0Rd0L`_---1RJ_0L`1L`_---1Ri_0RZ---_0R\---_1RZ---_1R\---_1L_---_0L]---_1RC---_1L]---_0Rb1Ri_0Rd0L`_1Rb1L__1Rd0L]_0L`0L]_1RJ0L__1L`1L]_1Ri1L__0Rd0RA_1Ri0RC_1Rd1RA_1L_1RC_0LF0RS_0LH0RC_1LF0Rd_1LH1Ri_0RC1Ri_1L`1L`_1RC1L__1L]1Lp_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp".
Definition tm1 := TM'_from_str "1RB---_0RC0LE_1LD1RH_1LE1LF_1RG1LD_0LE0LF_0RH1RG_1RI1RG_0RA0RC".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0LE_1LD1RH_1LE1LF_1RG1LD_0LE0LF_0RH1RG_1RI1RG_0RA0RC_1RJ1RJ".
Definition l0 := [1;1;1;1;1;0;1;0]%N.
Definition mp := mp_from_str "SZd_`]iCJ".
Definition mp' := mp_from_str "SZd_`]iCJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM100.


Module TM101.
Definition tm := TM_from_str "1LB0RB_1RC1RB_1LD1RA_1RF0LE_0LA1LF_---1LD".
Definition tm' := TM_from_str "1LB0RB_1RC1RB_1LD1RA_0LE0LE_0LA1LF_---1LD".
Definition tm0 := TM'_from_str "0RD0RI_0RL0RK_1RD1RI_1RL1RK_0LN1LE_0LP0RT_1LN0RD_1LP0RL_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0Lg1Ln_1RL1RT_1Lg1RD_1RK1RL_1LE0RB_1LE0RD_1Ln1RB_1Ln1RD_0L^1RT_0L`1RR_1L^1RL_1L`1RJ_0Rj0LN_0Rl---_1Rj1LE_1Rl0L`_---0Le_0Lg0Lg_---1Le_1Lg1Lg_1RL---_0RR1Lg_1RT---_1RR1Lg_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_---1LE_---1LE_---1Ln_---1Ln_---0L^_---0L`_---1L^_---1L`".
Definition tm0' := TM'_from_str "0RD0RI_0RL0RK_1RD1RI_1RL1RK_0LN1LE_0LP0RT_1LN0RD_1LP0RL_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0Lg1Ln_1RL1RT_1Lg1RD_1RK1RL_1LE0RB_1LE0RD_1Ln1RB_1Ln1RD_0L^1RT_0L`1RR_1L^1RL_1L`1RJ_0LN0LN_------_1LE1LE_0L`0L`_0Le0Le_0Lg0Lg_1Le1Le_1Lg1Lg_1RL---_0RR1Lg_1RT---_1RR1Lg_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_---1LE_---1LE_---1Ln_---1Ln_---0L^_---0L`_---1L^_---1L`".
Definition tm1 := TM'_from_str "1LB1RH_---0LC_1LD1LD_1LE1LB_0LF1LE_1RG1RA_1RA1RG_1RG1RI_1RK1RJ_0RA0RG_1LE0RH".
Definition tm2 := TM'_from_str "1LB1RH_1RL0LC_1LD1LD_1LE1LB_0LF1LE_1RG1RA_1RA1RG_1RG1RI_1RK1RJ_0RA0RG_1LE0RH_1RL1RL".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "Tn`gENLDKJR".
Definition mp' := mp_from_str "Tn`gENLDKJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM101.


Module TM102.
Definition tm := TM_from_str "1LB0RB_1RC1RB_1LD1RA_0LE0LE_0LA1LF_---1LD".
Definition tm' := TM_from_str "1LB0RB_1RC1RB_1LD1RA_0LF0RE_---1LD_0LA1LE".
Definition tm0 := TM'_from_str "0RD0RI_0RL0RK_1RD1RI_1RL1RK_0LN1LE_0LP0RT_1LN0RD_1LP0RL_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0Lg1Ln_1RL1RT_1Lg1RD_1RK1RL_1LE0RB_1LE0RD_1Ln1RB_1Ln1RD_0L^1RT_0L`1RR_1L^1RL_1L`1RJ_0LN0LN_------_1LE1LE_0L`0L`_0Le0Le_0Lg0Lg_1Le1Le_1Lg1Lg_1RL---_0RR1Lg_1RT---_1RR1Lg_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_---1LE_---1LE_---1Ln_---1Ln_---0L^_---0L`_---1L^_---1L`".
Definition tm0' := TM'_from_str "0RD0RI_0RL0RK_1RD1RI_1RL1RK_0LN1LE_0LP0RT_1LN0RD_1LP0RL_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0Lo1Lf_1RL1RT_1Lo1RD_1RK1RL_1LE0RB_1LE0RD_1Lf1RB_1Lf1RD_0L^1RT_0L`1RR_1L^1RL_1L`1RJ_0LN0Ra_---0Rc_1LE1Ra_0L`1Rc_0Lm---_0Lo0Lo_1Lm---_1Lo1Lo_---1LE_---1LE_---1Lf_---1Lf_---0L^_---0L`_---1L^_---1L`_1RL---_0RR1Lo_1RT---_1RR1Lo_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh".
Definition tm1 := TM'_from_str "1LB1RH_---0LC_1LD1LD_1LE1LB_0LF1LE_1RG1RA_1RA1RG_1RG1RI_1RK1RJ_0RA0RG_1LE0RH".
Definition tm2 := TM'_from_str "1LB1RH_1RL0LC_1LD1LD_1LE1LB_0LF1LE_1RG1RA_1RA1RG_1RG1RI_1RK1RJ_0RA0RG_1LE0RH_1RL1RL".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "Tn`gENLDKJR".
Definition mp' := mp_from_str "Tf`oENLDKJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM102.


Module TM103.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF0LF_0RB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_0RB---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RI_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk---_1Ri1LH_1Rk---_1RK0Lm_---0Lo_0RZ1Lm_---1Lo_0RI---_0RK---_1RI---_1RK---_0LH---_0RD---_1LH---_0RK---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RI_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk1LF_1Ri1LH_1Rk1LU_1RK0LV_---0LX_0RZ1LV_---1LX_0RI---_0RK---_1RI---_1RK---_0LH---_0RD---_1LH---_0RK---".
Definition tm1 := TM'_from_str "1RB1RI_1LC1RH_0LD0LC_1RA0LE_1RF1LE_1LE1RG_0RA0RF_1RA1RF_1RJ1LE_0RK---_1RF0RG".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RH_0LD0LC_1RA0LE_1RF1LE_1LE1RG_0RA0RF_1RA1RF_1RJ1LE_0RK1RL_1RF0RG_1RL1RL".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "DLUFHKZ\ciI".
Definition mp' := mp_from_str "DLUFHKZ\ciI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM103.


Module TM104.
Definition tm := TM_from_str "1RB0RE_1RC0RB_1RD0RF_1RE---_1LF1LE_1LA0LE".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LE_1LA0LE".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1R\0LH_1RR0Lp_1Rk1LH_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Rd0R\_1RK0RR_---0Rk_0Lg0RI_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lf1RR_---0Ln_1Lh1RI_---1Ln_0Rb---_0Rd---_1Rb---_1Rd---_0Lg---_0Lh---_1Lg---_1Lh---_1RI1LH_1Ln1Lp_1Lp1Lg_1Lf1Lh_0Ln0Lf_0Lp0Lh_1Ln1Lf_1Lp1Lh_0RK0LH_1LH0Lp_1RK0Lg_1Lg0Lh_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg".
Definition tm0' := TM'_from_str "0RJ1RI_0RL1Ln_1RJ1Lp_1RL1Lf_1R\0Ln_1RR0Lp_1Rk1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Rd0R\_1RK0RR_---0Rk_0Lg0RI_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lf1RR_---0Ln_1Lh1RI_---1Ln_0Rb---_0Rd---_1Rb---_1Rd---_0Lg---_0Lh---_1Lg---_1Lh---_1RI1LH_1Ln1Lp_1Lp1Lg_1Lf1Lh_0Ln0Lf_0Lp0Lh_1Ln1Lf_1Lp1Lh_0RK0LH_1LH0Lp_1RK0Lg_1Lg0Lh_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg".
Definition tm1 := TM'_from_str "0RB0RJ_1RC---_1LD1LE_0LF0LE_1LF1LE_1LH1LG_1LK1LD_1RI1LF_0RA0RI_1RL0LG_0LH0LG_1RA1RI".
Definition tm2 := TM'_from_str "0RB0RJ_1RC1RM_1LD1LE_0LF0LE_1LF1LE_1LH1LG_1LK1LD_1RI1LF_0RA0RI_1RL0LG_0LH0LG_1RA1RI_1RM1RM".
Definition l0 := [1;0;0;0;0;0;1;1]%N.
Definition mp := mp_from_str "R\dfhpgHIknK".
Definition mp' := mp_from_str "R\dfhpgHIknK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM104.


Module TM105.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LF_0LD0LD_0LC---".
Definition tm' := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RD_0LD0LD".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1Lm_1R\1Lm_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA1Lf_0RC---_1RA0Lf_1RC---_0LW0Lm_0RC0Lo_1LW1Lm_0RY1Lo_1RI1RI_0LU0LU_1Lf1Lf_------_0L]0L]_0L_0L__1L]1L]_1L_1L__0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\1LM_1Ln0Ln_---0Lp_1Ra1Ln_---1Lp_0RA1Ln_0RC---_1RA0Ln_1RC---_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_1Ra1Ra_0LU0LU_1Ln1Ln_------_0L]0L]_0L_0L__1L]1L]_1L_1L_".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF---_1LC0LC_1RA1LC_0RI1LC_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF1RJ_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_mUWYA".
Definition mp' := mp_from_str "aCn_MUWYA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM105.


Module TM106.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RD_0LD0LD".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LF_0LD0RC_0LC---".
Definition tm0 := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\1LM_1Ln0Ln_---0Lp_1Ra1Ln_---1Lp_0RA1Ln_0RC---_1RA0Ln_1RC---_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_1Ra1Ra_0LU0LU_1Ln1Ln_------_0L]0L]_0L_0L__1L]1L]_1L_1L_".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1Lm_1R\1Lm_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA1Lf_0RC---_1RA0Lf_1RC---_0LW0Lm_0RC0Lo_1LW1Lm_0RY1Lo_1RI0RQ_0LU0RS_1Lf1RQ_---1RS_0L]0RC_0L_0L__1L]---_1L_1L__0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF---_1LC0LC_1RA1LC_0RI1LC_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF1RJ_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "aCn_MUWYA".
Definition mp' := mp_from_str "ICf_mUWYA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM106.


Module TM107.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LF_0LD0RC_0LC---".
Definition tm' := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RD_1RC0LD".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1Lm_1R\1Lm_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA1Lf_0RC---_1RA0Lf_1RC---_0LW0Lm_0RC0Lo_1LW1Lm_0RY1Lo_1RI0RQ_0LU0RS_1Lf1RQ_---1RS_0L]0RC_0L_0L__1L]---_1L_1L__0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\1LM_1Ln0Ln_---0Lp_1Ra1Ln_---1Lp_0RA1Ln_0RC---_1RA0Ln_1RC---_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_0RR1Ra_0RT0LU_1RR1Ln_1RT---_1RC0L]_0L_0L__---1L]_1L_1L_".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF---_1LC0LC_1RA1LC_0RI1LC_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF1RJ_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_mUWYA".
Definition mp' := mp_from_str "aCn_MUWYA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM107.


Module TM108.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RD_1RC0LD".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LF_1RC0LD_0LC---".
Definition tm0 := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\1LM_1Ln0Ln_---0Lp_1Ra1Ln_---1Lp_0RA1Ln_0RC---_1RA0Ln_1RC---_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_0RR1Ra_0RT0LU_1RR1Ln_1RT---_1RC0L]_0L_0L__---1L]_1L_1L_".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1Lm_1R\1Lm_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA1Lf_0RC---_1RA0Lf_1RC---_0LW0Lm_0RC0Lo_1LW1Lm_0RY1Lo_0RR1RI_0RT0LU_1RR1Lf_1RT---_1RC0L]_0L_0L__---1L]_1L_1L__0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF---_1LC0LC_1RA1LC_0RI1LC_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF1RJ_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "aCn_MUWYA".
Definition mp' := mp_from_str "ICf_mUWYA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM108.


Module TM109.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LF_1RC0LD_0LC---".
Definition tm' := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RD_0LD0RC".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1Lm_1R\1Lm_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA1Lf_0RC---_1RA0Lf_1RC---_0LW0Lm_0RC0Lo_1LW1Lm_0RY1Lo_0RR1RI_0RT0LU_1RR1Lf_1RT---_1RC0L]_0L_0L__---1L]_1L_1L__0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0L_---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\1LM_1Ln0Ln_---0Lp_1Ra1Ln_---1Lp_0RA1Ln_0RC---_1RA0Ln_1RC---_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0RC0RY_0L_0R[_1RC1RY_0L_1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_1Ra0RQ_0LU0RS_1Ln1RQ_---1RS_0L]0RC_0L_0L__1L]---_1L_1L_".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF---_1LC0LC_1RA1LC_0RI1LC_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LD_1LG1LE_0LF1RJ_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_mUWYA".
Definition mp' := mp_from_str "aCn_MUWYA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM109.


Module TM110.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD0LF_1RD---".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD0LF_0RB---".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lo1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1RI_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI0RC_0LU---_1Lf1RC_1RI---_0L]0Lm_0L_0Lo_1L]1Lm_1L_1Lo_0RZ---_0R\---_1RZ---_1R\---_1Lf---_1RI---_1RI---_0RI---".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lo1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1RI_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI0RC_0LU---_1Lf1RC_1RI---_0L]0Lm_0L_0Lo_1L]1Lm_1L_1Lo_0RI---_0RK---_1RI---_1RK---_1Lf---_0RA---_1RI---_1Lf---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1RA---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1RA1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_MUWYAo".
Definition mp' := mp_from_str "ICf_MUWYAo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM110.


Module TM111.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD1LF_0LD---".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD1LF_0RC---".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lp1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1L__1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI1LW_0LU---_1Lf1LM_1RI---_0L]0Ln_0L_0Lp_1L]1Ln_1L_1Lp_1RI---_0LU---_1Lf---_1RI---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lp1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1L__1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI1LW_0LU---_1Lf1LM_1RI---_0L]0Ln_0L_0Lp_1L]1Ln_1L_1Lp_0RQ---_0RS---_1RQ---_1RS---_0RC---_0L_---_0RA---_1L_---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LD---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LD1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_MUWYAp".
Definition mp' := mp_from_str "ICf_MUWYAp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM111.


Module TM112.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD1LF_0RC---".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0RE1LF_0LD---".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lp1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1L__1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI1LW_0LU---_1Lf1LM_1RI---_0L]0Ln_0L_0Lp_1L]1Ln_1L_1Lp_0RQ---_0RS---_1RQ---_1RS---_0RC---_0L_---_0RA---_1L_---".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lp1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1L__1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0Ra1LW_0Rc---_1Ra1LM_1Rc---_0Ra0Ln_0L_0Lp_1LW1Ln_1L_1Lp_1RI---_0LU---_1Lf---_1RI---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LD---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LD1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_MUWYAp".
Definition mp' := mp_from_str "ICf_MUWYAp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM112.


Module TM113.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD0LF_0RE---".
Definition tm' := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LE_0LC0RD_0LD1LB".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lo1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI1RI_0LU---_1Lf1Lf_1RI---_0L]0Lm_0L_0Lo_1L]1Lm_1L_1Lo_0Ra---_0Rc---_1Ra---_1Rc---_0LW---_0LW---_1LW---_1LW---".
Definition tm0' := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0LP---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1Le_1R\---_1Ln0Ln_1Ra0Lp_1Ra1Ln_0Ra1Lp_0RA1Ln_0RC0RA_1RA0Ln_1RC1RA_0LW0Le_0RC0Lg_1LW1Le_0RY1Lg_0RC0RY_0L_0R[_1RC1RY_0LP1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_1Ra1Ra_0LU---_1Ln1Ln_1Ra---_0L]0LN_0L_0LP_1L]1LN_1L_1LP".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_MUWYAo".
Definition mp' := mp_from_str "aCn_eUWYAP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM113.


Module TM114.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LE_0LC0RD_0LD1LB".
Definition tm' := TM_from_str "1LB0RB_0LC0RF_1RD1LE_0RA---_0LF0LD_0RA0LB".
Definition tm0 := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0LP---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1Le_1R\---_1Ln0Ln_1Ra0Lp_1Ra1Ln_0Ra1Lp_0RA1Ln_0RC0RA_1RA0Ln_1RC1RA_0LW0Le_0RC0Lg_1LW1Le_0RY1Lg_0RC0RY_0L_0R[_1RC1RY_0LP1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_1Ra1Ra_0LU---_1Ln1Ln_1Ra---_0L]0LN_0L_0LP_1L]1LN_1L_1LP".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0Ri_0Lo0Rk_1RC1Ri_0L_1Rk_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0Ri---_1RI1RI_0LU---_1Lf1Lf_1RI---_0Lm0L]_0Lo0L__1Lm1L]_1Lo1L__0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0Ri1LO".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "aCn_eUWYAP".
Definition mp' := mp_from_str "ICfoMUWiA_".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM114.


Module TM115.
Definition tm := TM_from_str "1LB0RB_0LC0RF_1RD1LE_0RA---_0LF0LD_0RA0LB".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD0LF_0RA---".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0Ri_0Lo0Rk_1RC1Ri_0L_1Rk_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0Ri---_1RI1RI_0LU---_1Lf1Lf_1RI---_0Lm0L]_0Lo0L__1Lm1L]_1Lo1L__0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0Ri1LO".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lo1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI1RI_0LU---_1Lf1Lf_1RI---_0L]0Lm_0L_0Lo_1L]1Lm_1L_1Lo_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0RY---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICfoMUWiA_".
Definition mp' := mp_from_str "ICf_MUWYAo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM115.


Module TM116.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD0LF_0RA---".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LB_0LD1LF_0LC---".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lo1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI1RI_0LU---_1Lf1Lf_1RI---_0L]0Lm_0L_0Lo_1L]1Lm_1L_1Lo_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0RY---".
Definition tm0' := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lp1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO_1RI1RI_0LU---_1Lf1Lf_1RI---_0L]0Ln_0L_0Lp_1L]1Ln_1L_1Lp_0RC---_0L_---_1RC---_0Lp---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_MUWYAo".
Definition mp' := mp_from_str "ICf_MUWYAp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM116.


Module TM117.
Definition tm := TM_from_str "1LB0RB_0LC0RF_1RD1LE_0RA0LB_0LD0LF_0RA---".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA---_0LF0LD_0RA0LB".
Definition tm0 := TM'_from_str "1RI0RI_---0RK_1Lf1RI_---1RK_0LN1Lf_0LP0RA_1LN1RI_1LP---_0RC0Ri_0L_0Rk_1RC1Ri_0Lo1Rk_0LU1RI_0LW---_1LU0RI_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0Ri1LO_1RI1RI_0LU---_1Lf1Lf_1RI---_0L]0Lm_0L_0Lo_1L]1Lm_1L_1Lo_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0Ri---".
Definition tm0' := TM'_from_str "1RI0RI_---0RK_1Lf1RI_---1RK_0LN1Lf_0LP0RA_1LN1RI_1LP---_0RC0RY_0Lo0R[_1RC1RY_0L_1R[_0LU1RI_0LW---_1LU0RI_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0RY---_1RI1RI_0LU---_1Lf1Lf_1RI---_0Lm0L]_0Lo0L__1Lm1L]_1Lo1L__0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI---_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1RK_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_MUWiAo".
Definition mp' := mp_from_str "ICfoMUWYA_".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM117.


Module TM118.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA---_0LF0LD_0RA0LB".
Definition tm' := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA---_0LF1LB_0RA0LB".
Definition tm0 := TM'_from_str "1RI0RI_---0RK_1Lf1RI_---1RK_0LN1Lf_0LP0RA_1LN1RI_1LP---_0RC0RY_0Lo0R[_1RC1RY_0L_1R[_0LU1RI_0LW---_1LU0RI_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0RY---_1RI1RI_0LU---_1Lf1Lf_1RI---_0Lm0L]_0Lo0L__1Lm1L]_1Lo1L__0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO".
Definition tm0' := TM'_from_str "1RI0RI_---0RK_1Lf1RI_---1RK_0LN1Lf_0LP0RA_1LN1RI_1LP---_0RC0RY_0Lo0R[_1RC1RY_0LP1R[_0LU1RI_0LW---_1LU0RI_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0RY---_1RI1RI_0LU---_1Lf1Lf_1RI---_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI---_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1RK_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICfoMUWYA_".
Definition mp' := mp_from_str "ICfoMUWYAP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM118.


Module TM119.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA---_0LF1LB_0RA0LB".
Definition tm' := TM_from_str "1LB0RB_0LC0RF_1RD1LE_0RA0LB_0LD1LB_0RA---".
Definition tm0 := TM'_from_str "1RI0RI_---0RK_1Lf1RI_---1RK_0LN1Lf_0LP0RA_1LN1RI_1LP---_0RC0RY_0Lo0R[_1RC1RY_0LP1R[_0LU1RI_0LW---_1LU0RI_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0RY---_1RI1RI_0LU---_1Lf1Lf_1RI---_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0RY1LO".
Definition tm0' := TM'_from_str "1RI0RI_---0RK_1Lf1RI_---1RK_0LN1Lf_0LP0RA_1LN1RI_1LP---_0RC0Ri_0L_0Rk_1RC1Ri_0LP1Rk_0LU1RI_0LW---_1LU0RI_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Lf0Lf_1RI0Lh_1RI1Lf_0RI1Lh_0RA1Lf_0RC0RA_1RA0Lf_1RC1RA_0LW0LM_0RC0LO_1LW1LM_0Ri1LO_1RI1RI_0LU---_1Lf1Lf_1RI---_0L]0LN_0L_0LP_1L]1LN_1L_1LP_0RA---_0RC---_1RA---_1RC---_0LW---_0RC---_1LW---_0Ri---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI---_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RA_1LC0LC_1RA1LC_0RI1RK_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICfoMUWYAP".
Definition mp' := mp_from_str "ICf_MUWiAP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM119.


Module TM120.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LF_0LD1LB_0LC---".
Definition tm' := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RD_0LD1LE".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0LP1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1Lm_1R\1LU_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA1Lf_0RC---_1RA0Lf_1RC---_0LW0Lm_0RC0Lo_1LW1Lm_0RY1Lo_1RI1RI_0LU1Lf_1Lf1Lf_---0Lf_0L]0LN_0L_0LP_1L]1LN_1L_1LP_0RC---_0L_---_1RC---_0LP---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0Lh---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\1LU_1Ln0Ln_---0Lp_1Ra1Ln_---1Lp_0RA1Ln_0RC---_1RA0Ln_1RC---_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0RC0RY_0L_0R[_1RC1RY_0Lh1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_1Ra1Ra_0LU1Ln_1Ln1Ln_---0Ln_0L]0Lf_0L_0Lh_1L]1Lf_1L_1Lh".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF---_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG1LF".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RK_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG1LF_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_mUWYAP".
Definition mp' := mp_from_str "aCn_MUWYAh".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM120.


Module TM121.
Definition tm := TM_from_str "1LB0RB_0LC0RD_1RD1LE_0RA0LF_0LD1LF_0LC---".
Definition tm' := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RD_0LD1LB".
Definition tm0 := TM'_from_str "1RI0RI_1Lf0RK_1Lf1RI_0Lf1RK_0LN1Lf_0LP0RA_1LN1RI_1LP1Lf_0RC0RY_0L_0R[_1RC1RY_0Lp1R[_0LU1RI_0LW0LU_1LU0RI_1LW1LU_0RZ1LW_0R\1LW_1RZ1Lm_1R\---_1Lf0Lf_---0Lh_1RI1Lf_---1Lh_0RA1Lf_0RC---_1RA0Lf_1RC---_0LW0Lm_0RC0Lo_1LW1Lm_0RY1Lo_1RI1RI_0LU---_1Lf1Lf_------_0L]0Ln_0L_0Lp_1L]1Ln_1L_1Lp_0RC---_0L_---_1RC---_0Lp---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "1Ra0Ra_---0Rc_1Ln1Ra_---1Rc_0LN1Ln_0LP0RA_1LN1Ra_1LP1Ln_0RC---_0L_---_1RC---_0LP---_0LU---_0LW---_1LU---_1LW---_0RZ1LW_0R\1LW_1RZ1LM_1R\---_1Ln0Ln_---0Lp_1Ra1Ln_---1Lp_0RA1Ln_0RC---_1RA0Ln_1RC---_0LW0LM_0RC0LO_1LW1LM_0RY1LO_0RC0RY_0L_0R[_1RC1RY_0LP1R[_0LU1Ra_0LW0LU_1LU0Ra_1LW1LU_1Ra1Ra_0LU---_1Ln1Ln_------_0L]0LN_0L_0LP_1L]1LN_1L_1LP".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF---_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LJ_1LG1LE_0LF1RK_1LC0LC_1RA1LC_0RI1LC_1RA0RA_1LG1RK_1RK1RK".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "ICf_mUWYAp".
Definition mp' := mp_from_str "aCn_MUWYAP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM121.


Module TM122.
Definition tm := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_1LB---".
Definition tm' := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0RA---".
Definition tm0 := TM'_from_str "0RJ0LH_0RL0RA_1RJ0L`_1RL1RA_1L`0LU_1RL0LW_1Rc1LU_1RA1LW_0RR0RB_0RT0RD_1RR1RB_1RT1RD_0L`1RT_1RA0RJ_1L`1RD_1Rj0LH_1RA0Ra_1LH0Rc_1LW1Ra_1L`1Rc_0L^0RJ_0L`0RA_1L^0LH_1L`---_0RD1RA_1L^1LH_1RD1LW_0LH1L`_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RA0Rj_0RC0Rl_1RA1Rj_1RC1Rl_0RT0RJ_0L^---_0RD0LH_1L^---_0Rc---_0RA---_1Rc---_1RA---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ0LH_0RL0RA_1RJ0L`_1RL1RA_1L`0LU_1RL0LW_1Rc1LU_1RA1LW_0RR0RB_0RT0RD_1RR1RB_1RT1RD_0L`1RT_1RA0RJ_1L`1RD_1Ri0LH_1RA0Ra_1LH0Rc_1LW1Ra_1L`1Rc_0L^0RJ_0L`0RA_1L^0LH_1L`---_0RD1RA_1L^1LH_1RD1LW_0LH1L`_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0RT0RJ_0L^---_0RD0LH_1L^---_0RA---_0RC---_1RA---_1RC---_0RT---_0L^---_0RD---_1L^---".
Definition tm1 := TM'_from_str "1LB1RJ_1LC1LB_1RD1LE_0RF0LC_1LI0LC_0RA0RG_1RH1RD_1RA1RG_0LC0LB_1RD1RK_0RD---".
Definition tm2 := TM'_from_str "1LB1RJ_1LC1LB_1RD1LE_0RF0LC_1LI0LC_0RA0RG_1RH1RD_1RA1RG_0LC0LB_1RD1RK_0RD1RL_1RL1RL".
Definition l0 := [1;0;0;1;0;0;1;1]%N.
Definition mp := mp_from_str "T`HAWJDL^cj".
Definition mp' := mp_from_str "T`HAWJDL^ci".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM122.


Module TM123.
Definition tm := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0RA---".
Definition tm' := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---".
Definition tm0 := TM'_from_str "0RJ0LH_0RL0RA_1RJ0L`_1RL1RA_1L`0LU_1RL0LW_1Rc1LU_1RA1LW_0RR0RB_0RT0RD_1RR1RB_1RT1RD_0L`1RT_1RA0RJ_1L`1RD_1Ri0LH_1RA0Ra_1LH0Rc_1LW1Ra_1L`1Rc_0L^0RJ_0L`0RA_1L^0LH_1L`---_0RD1RA_1L^1LH_1RD1LW_0LH1L`_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0RT0RJ_0L^---_0RD0LH_1L^---_0RA---_0RC---_1RA---_1RC---_0RT---_0L^---_0RD---_1L^---".
Definition tm0' := TM'_from_str "0RJ0LH_0RL0RA_1RJ0L`_1RL1RA_1L`0LU_1RL0LW_1Rc1LU_1RA1LW_0RR0RB_0RT0RD_1RR1RB_1RT1RD_0L`1RT_1RA0RJ_1L`1RD_1Rj0LH_1RA0Ra_1LH0Rc_1LW1Ra_1L`1Rc_0L^0RJ_0L`0RA_1L^0LH_1L`---_0RD1RA_1L^1LH_1RD1LW_0LH1L`_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RA0Rj_0RC0Rl_1RA1Rj_1RC1Rl_0RT0RJ_0L^---_0RD0LH_1L^---_0LH---_0RA---_0L`---_1RA---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB1RJ_1LC1LB_1RD1LE_0RF0LC_1LI0LC_0RA0RG_1RH1RD_1RA1RG_0LC0LB_1RD1RK_0RD---".
Definition tm2 := TM'_from_str "1LB1RJ_1LC1LB_1RD1LE_0RF0LC_1LI0LC_0RA0RG_1RH1RD_1RA1RG_0LC0LB_1RD1RK_0RD1RL_1RL1RL".
Definition l0 := [1;0;0;1;0;0;1;1]%N.
Definition mp := mp_from_str "T`HAWJDL^ci".
Definition mp' := mp_from_str "T`HAWJDL^cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM123.


Module TM124.
Definition tm := TM_from_str "1LB---_1LC0LD_1RD1LF_0RF0RE_1RD0RE_0LB0LA".
Definition tm' := TM_from_str "1LB---_1LC0LE_1RD1LF_1RE0RD_0RF0RD_0LB0LA".
Definition tm0 := TM'_from_str "1Ra---_1LV---_1Lp---_0Rc---_0LN---_0LP---_1LN---_1LP---_0Rc1RZ_1LO0RZ_1Rc0Lp_1LG1RZ_0LV0L]_0LX0L__1LV1L]_1LX1L__0RZ1LV_0R\1LN_1RZ1L]_1R\---_0Lp0Ln_1RZ0Lp_0L_1Ln_1Ra1Lp_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0LV0Rk_0LN0RZ_1LV0Rc_1LN0Ra_0RZ0Ra_0R\0Rc_1RZ1Ra_1R\1Rc_0Lp0Rk_1RZ0RZ_0L_0Rc_1Ra0Ra_1RZ0LX_0LV---_0Lp0L__0Rk---_0LM0LE_0LO0LG_1LM1LE_1LO1LG".
Definition tm0' := TM'_from_str "1RY---_1LV---_1Lp---_0R[---_0LN---_0LP---_1LN---_1LP---_0R[1Rb_1LO0Rb_1R[0Lp_1LG1Rb_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ1LV_0R\1LN_1RZ1Le_1R\---_1Rk0Ln_1Rb0Lp_1R[1Ln_1RY1Lp_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lp0Rk_1Rb0Rb_0Lg0R[_1RY0RY_0Ri0RY_0Rk0R[_1Ri1RY_1Rk1R[_0LV0Rk_0LN0Rb_1LV0R[_1LN0RY_1Rb0LX_0LV---_0Lp0Lg_0Rk---_0LM0LE_0LO0LG_1LM1LE_1LO1LG".
Definition tm1 := TM'_from_str "0LB0LG_1LC1LJ_1LD1LE_1RF0LB_0LD0RA_0RA0RH_1LD0RH_1RF1RI_0RF0RI_1LK---_0LL0LG_1RI1LB".
Definition tm2 := TM'_from_str "0LB0LG_1LC1LJ_1LD1LE_1RF0LB_0LD0RA_0RA0RH_1LD0RH_1RF1RI_0RF0RI_1LK1RM_0LL0LG_1RI1LB_1RM1RM".
Definition l0 := [1;0;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "kpOV]Z_caGNX".
Definition mp' := mp_from_str "kpOVebg[YGNX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM124.


Module TM125.
Definition tm := TM_from_str "1RB1LE_1LC0RD_---1RB_0RE1RC_1RF0LF_1LA1LF".
Definition tm' := TM_from_str "1RB1LD_0RC0LF_0RD1RF_1RE0LE_1LA1LE_---1RB".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1LF_1RJ1Lp_1RL1Ln_1Ra0Lf_1Ra0Lh_1RR1Lf_1RR1Lh_---0RY_0R[0R[_---1RY_1R[1R[_0LV0Rj_0LX---_1LV1Ra_1LX0RL_---0RJ_---0RL_---1RJ_---1RL_---1Ra_---1Ra_---1RR_---1RR_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_1Lp---_0LF1R[_1LH---_1LF1R[_0Rj1Ra_0Rl0LH_1Rj0Lh_1Rl0Lp_0Lh0Lm_0Lp0Lo_1Lh1Lm_1Lp1Lo_0R[1RR_1Lp1LH_1R[1Lh_1Lo1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1LF_1RJ1Lh_1RL1Lf_1RY0L^_1RY0L`_1Rj1L^_1Rj1L`_0RQ---_0RS0RS_1RQ---_1RS1RS_0Rb0Lm_---0Lo_1RY1Lm_0RL1Lo_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_1Lh---_0LF1RS_1LH---_1LF1RS_0Rb1RY_0Rd0LH_1Rb0L`_1Rd0Lh_0L`0Le_0Lh0Lg_1L`1Le_1Lh1Lg_0RS1Rj_1Lh1LH_1RS1L`_1Lg1Lh_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_---0RJ_---0RL_---1RJ_---1RL_---1RY_---1RY_---1Rj_---1Rj".
Definition tm1 := TM'_from_str "1LB1LC_1LC1LB_1RG1LD_1LB1LE_1LF1LK_1RJ0LD_---0RH_1RI1RI_1RJ1RG_0RA1RJ_0LC0LB".
Definition tm2 := TM'_from_str "1LB1LC_1LC1LB_1RG1LD_1LB1LE_1LF1LK_1RJ0LD_1RL0RH_1RI1RI_1RJ1RG_0RA1RJ_0LC0LB_1RL1RL".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "jpHhoFRL[an".
Definition mp' := mp_from_str "bhH`gFjLSYf".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM125.


Module TM126.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1RE1RD_0RC---_1RF0RB_1LA0RD".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_1RE1RD_0RC---_1RF0RB_1LB0RD".
Definition tm0 := TM'_from_str "0R\1RS_1LN0LN_1R\0LG_1LE0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR1RS_0RT0LN_1RR0LG_1RT0LE_1Rl0LE_1RS0LG_1RK1LE_---1LG_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_1LE1Rb_1RR---_1R[1RZ_0LG---_0RQ---_0RS---_1RQ---_1RS---_0Rl---_0RS---_0RK---_------_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_0LG0Rd_1RQ0LN_1LG0R\_---1LN_---0RY_1LN0R[_1LG1RY_1LE1R[_0LF0Rb_0LH---_1LF0RZ_1LH---".
Definition tm0' := TM'_from_str "0R\1RS_1LN0LN_1R\0LG_1LE0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR1RS_0RT0LN_1RR0LG_1RT0LE_1Rl0LE_1RS0LG_1RK1LE_---1LG_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_1LE1Rb_1RR---_1R[1RZ_0LG---_0RQ---_0RS---_1RQ---_1RS---_0Rl---_0RS---_0RK---_------_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_0LG0Rd_1RQ0LN_1LG0R\_---1LN_0R\0RY_1LN0R[_1R\1RY_1LE1R[_0LN0Rb_0LP---_1LN0RZ_1LP---".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RK_0LD0LC_1RF0LE_1LD1LC_1RG1RM_0RB0RH_1RI0LE_0RA0RJ_1RF---_1RL---_0RG0RM_0RF---".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RK_0LD0LC_1RF0LE_1LD1LC_1RG1RM_0RB0RH_1RI0LE_0RA0RJ_1RF1RN_1RL1RN_0RG0RM_0RF1RN_1RN1RN".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "dlENGSbKR\[QZ".
Definition mp' := mp_from_str "dlENGSbKR\[QZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM126.


Module TM127.
Definition tm := TM_from_str "1LB0RE_0LC0LE_1RD1LA_0RA1LF_0LC0LD_0RC---".
Definition tm' := TM_from_str "1LB0RE_0LC0LE_1RD1LA_0RA1LF_0LC0LD_1LB---".
Definition tm0 := TM'_from_str "1Ra0Ra_1LU0Rc_1LF1Ra_1L]1Rc_0LN1LF_0LP0LW_1LN1Ra_1LP1LW_0RC1LF_0LP0LW_1RC0LF_0LW0Ln_0LU0Le_0LW0Lg_1LU1Le_1LW1Lg_0RZ1LW_0R\1Ra_1RZ1Lg_1R\1LF_1LF0LF_---0LH_1Ra1LF_---1LH_0RA1LW_0RC---_1RA1Lg_1RC---_0LW0Ln_0RC0Lp_1LW1Ln_1Ra1Lp_0RC1Ra_0LP0LP_1RC1LF_0LW---_0LU0L]_0LW0L__1LU1L]_1LW1L__0RQ---_0RS---_1RQ---_1RS---_0RC---_0LP---_------_1LP---".
Definition tm0' := TM'_from_str "1Ra0Ra_1LU0Rc_1LF1Ra_1L]1Rc_0LN1LF_0LP0LW_1LN1Ra_1LP1LW_0RC1LF_0LP0LW_1RC0LF_0LW0Ln_0LU0Le_0LW0Lg_1LU1Le_1LW1Lg_0RZ1LW_0R\1Ra_1RZ1Lg_1R\1LF_1LF0LF_---0LH_1Ra1LF_---1LH_0RA1LW_0RC---_1RA1Lg_1RC---_0LW0Ln_0RC0Lp_1LW1Ln_1Ra1Lp_0RC1Ra_0LP0LP_1RC1LF_0LW---_0LU0L]_0LW0L__1LU1L]_1LW1L__1Ra---_1LU---_1LF---_1L]---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "0RB1RA_1LC1RA_0LD0LG_1LG1LE_1LF1LH_1LC0LC_1RA1LC_0LG0LI_0LD---".
Definition tm2 := TM'_from_str "0RB1RA_1LC1RA_0LD0LG_1LG1LE_1LF1LH_1LC0LC_1RA1LC_0LG0LI_0LD1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "aCFPgUW]n".
Definition mp' := mp_from_str "aCFPgUW]n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM127.


Module TM128.
Definition tm := TM_from_str "1LB0LC_0RC1RD_1LA1LD_1RB0RE_1RF1RC_---1RB".
Definition tm' := TM_from_str "1LB0LC_0RC1RD_1LA1LD_1RB0RE_1RF1RC_---0LB".
Definition tm0 := TM'_from_str "0R\0LP_0Rc1RL_1R\0LW_1Rc1LF_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RQ0RZ_0RS0R\_1RQ1RZ_1RS1R\_0LP1RS_1RL1Rj_1LP1R\_1Rc1RR_1Rc0R\_1LF0RR_1RR1R\_1L^1RR_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1RR---_1RL1LF_1R\0RL_1Rc0RR_0Rj0RR_0Rl0RT_1Rj1RR_1Rl1RT_---0LW_1RS1LF_---1LW_1R\0RR_---0RJ_---0RL_---1RJ_---1RL_---1RR_---1RL_---1R\_---1Rc".
Definition tm0' := TM'_from_str "0R\0LP_0Rc1RL_1R\0LW_1Rc1LF_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RQ0RZ_0RS0R\_1RQ1RZ_1RS1R\_0LP1RS_1RL1Rj_1LP1R\_1Rc1RR_1Rc0R\_1LF0RR_1RR1R\_1L^1RR_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1RR---_1RL1LF_1R\0RL_1Rc0RR_0Rj0RR_0Rl0RT_1Rj1RR_1Rl1RT_---0LW_1RS1LF_---1LW_1R\0RR_---1Rc_---0RL_---1RR_---1RL_---0LM_---0LO_---1LM_---1LO".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RB_0LF0LD_1LC1LE_1RG1LC_1RI1RB_1RA1RH_1RG1RI_1RJ1RB_---0RG".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RB_0LF0LD_1LC1LE_1RG1LC_1RI1RB_1RA1RH_1RG1RI_1RJ1RB_1RK0RG_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "SRFW^PL\cj".
Definition mp' := mp_from_str "SRFW^PL\cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM128.


Module TM129.
Definition tm := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_0LB0RA_1RD---".
Definition tm' := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1RD0RA_0LA---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1R\1RJ_1LW1L`_---1Rb_1RC0Rj_1L^0Rl_1L`1Rj_1LU1Rl_0LV1RD_0LX---_1LV1L`_1LX---_0Rd1R\_1RC0L^_1Rd0L`_1L`0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Rd_0RD1RC_1RB1Rd_1RD1L`_1LU0L^_1R\0L`_1Rl1L^_1RC1L`_0L`0RA_0R\0RC_0LW1RA_1R\1RC_0LM1L^_0LO0R\_1LM0Rl_1LO0RC_0RZ---_0R\---_1RZ---_1R\---_1RL---_0L`---_1Rd---_1L`---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1R\1RJ_1LW1L`_---1Rb_1RC0Rj_1L^0Rl_1L`1Rj_1LU1Rl_0LV1RD_0LX---_1LV1L`_1LX---_0Rd1R\_1RC0L^_1Rd0L`_1L`0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Rd_0RD1RC_1RB1Rd_1RD1L`_1LU0L^_1R\0L`_1Rl1L^_1RC1L`_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1RL1L^_0L`0R\_1Rd0Rl_1L`0RC_1L^---_0R\---_1LU---_1R\---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB1RK_0LC0LB_1RG0LD_1RE1LD_1RI1RF_0RG0RE_1RH1LD_1RA1RJ_1LC0RK_1RG1RE_1RG---".
Definition tm2 := TM'_from_str "1LB1RK_0LC0LB_1RG0LD_1RE1LD_1RI1RF_0RG0RE_1RH1LD_1RA1RJ_1LC0RK_1RG1RE_1RG1RL_1RL1RL".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "LU^`Cb\DJdl".
Definition mp' := mp_from_str "LU^`Cb\DJdl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM129.


Module TM130.
Definition tm := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1RD0RA_0LA---".
Definition tm' := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1RD0RA_1RD---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1R\1RJ_1LW1L`_---1Rb_1RC0Rj_1L^0Rl_1L`1Rj_1LU1Rl_0LV1RD_0LX---_1LV1L`_1LX---_0Rd1R\_1RC0L^_1Rd0L`_1L`0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Rd_0RD1RC_1RB1Rd_1RD1L`_1LU0L^_1R\0L`_1Rl1L^_1RC1L`_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1RL1L^_0L`0R\_1Rd0Rl_1L`0RC_1L^---_0R\---_1LU---_1R\---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1R\1RJ_1LW1L`_---1Rb_1RC0Rj_1L^0Rl_1L`1Rj_1LU1Rl_0LV1RD_0LX---_1LV1L`_1LX---_0Rd1R\_1RC0L^_1Rd0L`_1L`0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Rd_0RD1RC_1RB1Rd_1RD1L`_1LU0L^_1R\0L`_1Rl1L^_1RC1L`_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1RL1L^_0L`0R\_1Rd0Rl_1L`0RC_0RZ---_0R\---_1RZ---_1R\---_1RL---_0L`---_1Rd---_1L`---".
Definition tm1 := TM'_from_str "1LB1RK_0LC0LB_1RG0LD_1RE1LD_1RI1RF_0RG0RE_1RH1LD_1RA1RJ_1LC0RK_1RG1RE_1RG---".
Definition tm2 := TM'_from_str "1LB1RK_0LC0LB_1RG0LD_1RE1LD_1RI1RF_0RG0RE_1RH1LD_1RA1RJ_1LC0RK_1RG1RE_1RG1RL_1RL1RL".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "LU^`Cb\DJdl".
Definition mp' := mp_from_str "LU^`Cb\DJdl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM130.


Module TM131.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1LB---_1RA1RF".
Definition tm' := TM_from_str "1LB---_0RC0LB_1RE0RD_1RA1RC_1RF0LD_1LB1LF".
Definition tm0 := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Rb0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Rb0RR_0Rd0RT_1Rb1RR_1Rd1RT_0LO1RD_---1Rb_1LO1Rl_---1RR_0RY---_0Rl---_1RY---_1LM---_0LN---_0LP---_1LN---_1LP---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LO1LM_0LH1RD_1LO1LH_1LH1Rl".
Definition tm0' := TM'_from_str "0RY---_0Rd---_1RY---_1LM---_0LN---_0LP---_1LN---_1LP---_0RQ0Rb_0RS0Rl_1RQ1Rb_1RS0LM_0Rl0LM_0RB0LO_0Rd1LM_0RR1LO_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1LM0Rd_1Rl0Rd_1Lp---_1Rd0R[_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LO1Rl_---1RB_1LO1Rd_---1RR_0Rj0Rd_0Rl0Rd_1Rj1LM_1Rl1Rd_0LO0L]_0Lp0L__1LO1L]_1Lp1L__0RY0RR_0Rd1LP_1RY1LO_1LM1Lp_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF1RJ_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "DMHPOlR[b".
Definition mp' := mp_from_str "lMpPOdR[B".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM131.


Module TM132.
Definition tm := TM_from_str "1LB---_0RC0LB_1RE0RD_1RA1RC_1RF0LD_1LB1LF".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LF---_1RA1RF".
Definition tm0 := TM'_from_str "0RY---_0Rd---_1RY---_1LM---_0LN---_0LP---_1LN---_1LP---_0RQ0Rb_0RS0Rl_1RQ1Rb_1RS0LM_0Rl0LM_0RB0LO_0Rd1LM_0RR1LO_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1LM0Rd_1Rl0Rd_1Lp---_1Rd0R[_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LO1Rl_---1RB_1LO1Rd_---1RR_0Rj0Rd_0Rl0Rd_1Rj1LM_1Rl1Rd_0LO0L]_0Lp0L__1LO1L]_1Lp1L__0RY0RR_0Rd1LP_1RY1LO_1LM1Lp_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp".
Definition tm0' := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Ra0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_0LO1RD_---1Ra_1LO1Rl_---1RR_0Rl---_0RD---_1LM---_1RD---_0Lm---_0Lo---_1Lm---_1Lo---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LO1LM_0LH1RD_1LO1LH_1LH1Rl".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF1RJ_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "lMpPOdR[B".
Definition mp' := mp_from_str "DMHPOlR[a".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM132.


Module TM133.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LF---_1RA1RF".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_1LC---_1RA0LD".
Definition tm0 := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Ra0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_0LO1RD_---1Ra_1LO1Rl_---1RR_0Rl---_0RD---_1LM---_1RD---_0Lm---_0Lo---_1Lm---_1Lo---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LO1LM_0LH1RD_1LO1LH_1LH1Rl".
Definition tm0' := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Ra0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_1RD1RD_---1Ra_1Rl1Rl_---1RR_0Rl---_0RR---_1Rl---_1RR---_0LV---_0LX---_1LV---_1LX---_0RB0Rl_0RD0Rl_1RB1Rl_1RD1Rl_0LO0L]_0LH0L__1LO1L]_1LH1L_".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF1RJ_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "DMHPOlR[a".
Definition mp' := mp_from_str "DMHPOlR[a".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM133.


Module TM134.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_1LC---_1RA0LD".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LD---_1RA1RF".
Definition tm0 := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Ra0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_1RD1RD_---1Ra_1Rl1Rl_---1RR_0Rl---_0RR---_1Rl---_1RR---_0LV---_0LX---_1LV---_1LX---_0RB0Rl_0RD0Rl_1RB1Rl_1RD1Rl_0LO0L]_0LH0L__1LO1L]_1LH1L_".
Definition tm0' := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Rb0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Rb0RR_0Rd0RT_1Rb1RR_1Rd1RT_1RD1RD_---1Rb_1Rl1Rl_---1RR_0Rl---_0Rl---_1Rl---_1Rl---_0L]---_0L_---_1L]---_1L_---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LO1LM_0LH1RD_1LO1LH_1LH1Rl".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF1RJ_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "DMHPOlR[a".
Definition mp' := mp_from_str "DMHPOlR[b".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM134.


Module TM135.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LD---_1RA1RF".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LF---_1RA0LD".
Definition tm0 := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Rb0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Rb0RR_0Rd0RT_1Rb1RR_1Rd1RT_1RD1RD_---1Rb_1Rl1Rl_---1RR_0Rl---_0Rl---_1Rl---_1Rl---_0L]---_0L_---_1L]---_1L_---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LO1LM_0LH1RD_1LO1LH_1LH1Rl".
Definition tm0' := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Ra0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_0LO1RD_---1Ra_1LO1Rl_---1RR_0Rl---_0LO---_1LM---_1RD---_0Lm---_0Lo---_1Lm---_1Lo---_0RB0Rl_0RD0Rl_1RB1LM_1RD1Rl_0LO0L]_0LH0L__1LO1L]_1LH1L_".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF1RJ_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "DMHPOlR[b".
Definition mp' := mp_from_str "DMHPOlR[a".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM135.


Module TM136.
Definition tm := TM_from_str "1LB0RC_1LC0LA_0RD0LA_1RA1RE_0LE0RF_0LC---".
Definition tm' := TM_from_str "1LB0RC_1LC0LA_0RD0LA_0LB1RE_0LE0RF_1RA---".
Definition tm0 := TM'_from_str "0Rk0RQ_1LN0RS_1LG1RQ_0Rb1RS_0LN0RB_0LP0LN_1LN0Rb_1LP1LN_0Rb0LX_1LN0RY_1Rb0LG_0Rb1RY_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RY0LX_0R[0RY_1RY0LG_1R[1RY_1LN0LE_0RB0LG_0RS1LE_0Rk1LG_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0LG1LN_1RY1RB_1LG0RS_0LG---_0Le0Ri_0RB0Rk_1LN1Ri_1RB1Rk_0Le1LN_0Lg---_1Le0RS_1Lg---_0RB---_0LN---_1RB---_0RB---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0Rk0RQ_1LN0RS_1LG1RQ_0Rb1RS_0LN0RB_0LP0LN_1LN0Rb_1LP1LN_0Rb0LX_1LN0RY_1Rb0LG_0Rb1RY_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RY0LX_0R[0RY_1RY0LG_1R[1RY_0LV0LE_0RB0LG_1LV1LE_0Rk1LG_0RB0Rb_0LN0Rd_0LG1Rb_0RB1Rd_0LM1LN_0LO1RB_1LM0RS_1LO---_0Le0Ri_0RB0Rk_1LN1Ri_1RB1Rk_0Le1LN_0Lg---_1Le0RS_1Lg---_0RB---_0RD---_1RB---_1RD---_0LG---_1RY---_1LG---_0LG---".
Definition tm1 := TM'_from_str "0RB0RH_1LC0RG_0LD0LE_0RF1LE_1LC0RH_1RB---_1RA0LE_0RB0RF".
Definition tm2 := TM'_from_str "0RB0RH_1LC0RG_0LD0LE_0RF1LE_1LC0RH_1RB1RI_1RA0LE_0RB0RF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "YBNXGkSb".
Definition mp' := mp_from_str "YBNXGkSb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM136.


Module TM137.
Definition tm := TM_from_str "1LB0RC_1LC0LA_0RD0LA_0LB1RE_0LE0RF_1RA---".
Definition tm' := TM_from_str "1LB0RC_1LC0LA_0RD0LA_1RA1RE_0LE0RF_1RA---".
Definition tm0 := TM'_from_str "0Rk0RQ_1LN0RS_1LG1RQ_0Rb1RS_0LN0RB_0LP0LN_1LN0Rb_1LP1LN_0Rb0LX_1LN0RY_1Rb0LG_0Rb1RY_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RY0LX_0R[0RY_1RY0LG_1R[1RY_0LV0LE_0RB0LG_1LV1LE_0Rk1LG_0RB0Rb_0LN0Rd_0LG1Rb_0RB1Rd_0LM1LN_0LO1RB_1LM0RS_1LO---_0Le0Ri_0RB0Rk_1LN1Ri_1RB1Rk_0Le1LN_0Lg---_1Le0RS_1Lg---_0RB---_0RD---_1RB---_1RD---_0LG---_1RY---_1LG---_0LG---".
Definition tm0' := TM'_from_str "0Rk0RQ_1LN0RS_1LG1RQ_0Rb1RS_0LN0RB_0LP0LN_1LN0Rb_1LP1LN_0Rb0LX_1LN0RY_1Rb0LG_0Rb1RY_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RY0LX_0R[0RY_1RY0LG_1R[1RY_1LN0LE_0RB0LG_0RS1LE_0Rk1LG_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0LG1LN_1RY1RB_1LG0RS_0LG---_0Le0Ri_0RB0Rk_1LN1Ri_1RB1Rk_0Le1LN_0Lg---_1Le0RS_1Lg---_0RB---_0RD---_1RB---_1RD---_0LG---_1RY---_1LG---_0LG---".
Definition tm1 := TM'_from_str "0RB0RH_1LC0RG_0LD0LE_0RF1LE_1LC0RH_1RB---_1RA0LE_0RB0RF".
Definition tm2 := TM'_from_str "0RB0RH_1LC0RG_0LD0LE_0RF1LE_1LC0RH_1RB1RI_1RA0LE_0RB0RF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "YBNXGkSb".
Definition mp' := mp_from_str "YBNXGkSb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM137.


Module TM138.
Definition tm := TM_from_str "1RB1RE_1RC1LB_0RD1RA_1LA---_1LF0RC_0RD0LF".
Definition tm' := TM_from_str "1RB1RE_1RC1LB_1RD1RA_1LB---_1LF0RC_1RD0LF".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1R[0Lo_0LP1RY_1RD1Lo_1LP1RB_0RR0RD_0RT1Rd_1RR1RD_1RT1LP_1LP0LN_1RL0LP_---1LN_1Rd1LP_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0LP1RT_---1Lm_1LP1LP_---1RS_1Rd---_0RS---_1LP---_1RS---_0LF---_0LH---_1LF---_1LH---_---0RQ_1LP0RS_---1RQ_1Lm1RS_0Ln1Rd_0Lp0RL_1Ln---_1Lp0Rd_0RY1Rd_0R[0LP_1RY1LP_1R[0Lm_0LP0Lm_---0Lo_1LP1Lm_---1Lo".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1R\0Lo_0LP1RZ_1RD1Lo_1LP1RB_0RR0RD_0RT1Rd_1RR1RD_1RT1LP_1LP0LN_1RL0LP_---1LN_1Rd1LP_0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_0LP1RT_---1Lm_1LP1LP_---1RS_0RD---_1Rd---_1RD---_1LP---_0LN---_0LP---_1LN---_1LP---_---0RQ_1LP0RS_---1RQ_1Lm1RS_0Ln1Rd_0Lp0RL_1Ln---_1Lp0Rd_0RZ1Rd_0R\0LP_1RZ1LP_1R\0Lm_0LP0Lm_---0Lo_1LP1Lm_---1Lo".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RA1LC_1RI1RE_0RF0RA_1RG1LC_1RH1RJ_1LC---_1RA---_1RF1RA".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RA1LC_1RI1RE_0RF0RA_1RG1LC_1RH1RJ_1LC1RK_1RA1RK_1RF1RA_1RK1RK".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "dmPSBLT[YD".
Definition mp' := mp_from_str "dmPSBLT\ZD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM138.


Module TM139.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD0RA_1RE0RD_1RF0RB_1RA---".
Definition tm' := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_1RF0RB_1RA---".
Definition tm0 := TM'_from_str "1RY1LX_1LN1LP_1LP1LG_1LF1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0R[0LX_1LX0LP_1R[0LG_1LG0LH_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Rl0LX_1Rb0LP_1RK1LX_1RY1LP_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1RD0Rl_1R[0Rb_---0RK_0LG0RY_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_1LF1Rb_---0LN_1LH1RY_---1LN_0RB---_0RD---_1RB---_1RD---_0LG---_0LH---_1LG---_1LH---".
Definition tm0' := TM'_from_str "1RY1LX_1LN1LP_1LP1LG_1LF1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0R[0LX_1LX0LP_1R[0LG_1LG0LH_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RZ1RY_0R\1LN_1RZ1LP_1R\1LF_1Rl0LN_1Rb0LP_1RK1LN_1RY1LP_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1RD0Rl_1R[0Rb_---0RK_0LG0RY_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_1LF1Rb_---0LN_1LH1RY_---1LN_0RB---_0RD---_1RB---_1RD---_0LG---_0LH---_1LG---_1LH---".
Definition tm1 := TM'_from_str "1RB1RJ_0RC0RK_1RD---_1LE1LF_0LG0LF_1LG1LF_1LI1LH_1LL1LE_1RJ1LG_0RB0RJ_1RA0LH_0LI0LH".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0RK_1RD1RM_1LE1LF_0LG0LF_1LG1LF_1LI1LH_1LL1LE_1RJ1LG_0RB0RJ_1RA0LH_0LI0LH_1RM1RM".
Definition l0 := [1;0;0;0;0;0;0;1]%N.
Definition mp := mp_from_str "[blDFHPGXYKN".
Definition mp' := mp_from_str "[blDFHPGXYKN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM139.


Module TM140.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1LD0LE_1LE0LC_1LA0RA_0LC---".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_1LD0LE_1LE0LC_1LA0RA_1RC---".
Definition tm0 := TM'_from_str "0RJ1L^_0RL---_1RJ1Le_1RL---_1Le0Ln_1RR0Lp_1RJ1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1LH1RR_1L^0RJ_1LW0Lp_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_1RI0Lh_1L^0LF_1Lp0LW_1Le0RT_0Lf0LU_0Lh0LW_1Lf1LU_1Lh1LW_0RK0RA_1LW0RC_1RK1RA_---1RC_0LF0RT_0LH0LW_1LF0RK_1LH1LW_0Lh---_0LF---_0LW---_0RT---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ1L^_0RL---_1RJ1Le_1RL---_1Le0Lm_1RR0Lo_1RJ1Lm_1RI1Lo_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1LH1RR_1L^0RJ_1LW0Lo_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_1RI0Lh_1L^0LF_1Lo0LW_1Le0RT_0Lf0LU_0Lh0LW_1Lf1LU_1Lh1LW_0RK0RA_1LW0RC_1RK1RA_---1RC_0LF0RT_0LH0LW_1LF0RK_1LH1LW_0RR---_0RT---_1RR---_1RT---_0LW---_0RT---_1LW---_0RK---".
Definition tm1 := TM'_from_str "1LB0RG_0LD0LC_1LB1LI_1LE1LC_1RF1LK_0RA0RF_0RH0RL_1LI1RG_0LJ0RH_1RA0LK_1LC---_1RA1RF".
Definition tm2 := TM'_from_str "1LB0RG_0LD0LC_1LB1LI_1LE1LC_1RF1LK_0RA0RF_0RH0RL_1LI1RG_0LJ0RH_1RA0LK_1LC1RM_1RA1RF_1RM1RM".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "R^WhHIJTeFpK".
Definition mp' := mp_from_str "R^WhHIJTeFoK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM140.


Module TM141.
Definition tm := TM_from_str "1RB0LF_1RC0RB_1LD0LE_1LE0LC_1LA0RA_1RC---".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1LD0LF_1LF0RA_0LC---_1LA0RA".
Definition tm0 := TM'_from_str "0RJ1L^_0RL---_1RJ1Le_1RL---_1Le0Lm_1RR0Lo_1RJ1Lm_1RI1Lo_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1LH1RR_1L^0RJ_1LW0Lo_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_1RI0Lh_1L^0LF_1Lo0LW_1Le0RT_0Lf0LU_0Lh0LW_1Lf1LU_1Lh1LW_0RK0RA_1LW0RC_1RK1RA_---1RC_0LF0RT_0LH0LW_1LF0RK_1LH1LW_0RR---_0RT---_1RR---_1RT---_0LW---_0RT---_1LW---_0RK---".
Definition tm0' := TM'_from_str "0RJ1L^_0RL---_1RJ1Lm_1RL---_1Lm0Lf_1RR0Lh_1RJ1Lf_1RI1Lh_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1LH1RR_1L^0RJ_1LW0Lh_1Lm1RJ_0L^0Lm_0L`0Lo_1L^1Lm_1L`1Lo_1RI0RA_1L^0RC_1Lh1RA_1Lm1RC_0Ln0RT_0Lp0LW_1Ln0RK_1Lp1LW_0Lp---_0LF---_0LW---_0RT---_0LU---_0LW---_1LU---_1LW---_0RK0RA_1LW0RC_1RK1RA_---1RC_0LF0RT_0LH0LW_1LF0RK_1LH1LW".
Definition tm1 := TM'_from_str "1LB0RG_0LD0LC_1LB1LI_1LE1LC_1RF1LK_0RA0RF_0RH0RL_1LI1RG_0LJ0RH_1RA0LK_1LC---_1RA1RF".
Definition tm2 := TM'_from_str "1LB0RG_0LD0LC_1LB1LI_1LE1LC_1RF1LK_0RA0RF_0RH0RL_1LI1RG_0LJ0RH_1RA0LK_1LC1RM_1RA1RF_1RM1RM".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "R^WhHIJTeFoK".
Definition mp' := mp_from_str "R^WpHIJTmFhK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM141.


Module TM142.
Definition tm := TM_from_str "1LB---_0LC1LA_0RD0LE_1LE1RC_0LF0RF_1RC1LB".
Definition tm' := TM_from_str "1LB---_0LC1LA_0RD0LE_1LE1LF_0LF0RF_1RC1LB".
Definition tm0 := TM'_from_str "1Lo---_1LP---_1Le---_------_0LN---_0LP---_1LN---_1LP---_1RR1LW_0Lm---_1LN1LH_0R[---_0LU0LF_0LW0LH_1LU1LF_1LW1LH_0RY1LN_0R[0RR_1RY0LN_1R[1RR_0Lo0Le_0R[0Lg_1Lo1Le_0RR1Lg_1RR0RR_1Lo0RT_1LN1RR_1Le1RT_0Lf1LN_0Lh0R[_1Lf1RR_1Lh0RR_0R[0Ri_0LW0Rk_1R[1Ri_0LH1Rk_0Lm0R[_0Lo0LW_1Lm0RR_1Lo1LW_0RR1Lo_0RT1LP_1RR1Le_1RT---_1LN0LN_0R[0LP_1RR1LN_0RR1LP".
Definition tm0' := TM'_from_str "1Lo---_1LP---_1Le---_------_0LN---_0LP---_1LN---_1LP---_1RR1LW_0Lm---_1LN1LH_0R[---_0LU0LF_0LW0LH_1LU1LF_1LW1LH_0RY1LN_0R[0RR_1RY0LN_1R[1RR_0Lo0Le_0R[0Lg_1Lo1Le_0RR1Lg_1RR0RR_1Lo1LW_1LN1RR_1Le1LH_0Lf0Ln_0Lh0Lp_1Lf1Ln_1Lh1Lp_0R[0Ri_0LW0Rk_1R[1Ri_0LH1Rk_0Lm0R[_0Lo0LW_1Lm0RR_1Lo1LW_0RR1Lo_0RT1LP_1RR1Le_1RT---_1LN0LN_0R[0LP_1RR1LN_0RR1LP".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LF_1LH1LD_0LE0RA_1LB0LB_1LG---_1LC1LF_1RI1LB_0RA0RI".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LF_1LH1LD_0LE0RA_1LB0LB_1LG1RJ_1LC1LF_1RI1LB_0RA0RI_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;1;0]%N.
Definition mp := mp_from_str "[NWemHPoR".
Definition mp' := mp_from_str "[NWemHPoR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM142.


Module TM143.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RD0RA_1LE1RA_0LF---_1LA1RB".
Definition tm' := TM_from_str "1LB0RD_1LC1LE_1RD0RA_1LB1RA_0LF---_1LA1RB".
Definition tm0 := TM'_from_str "1R[0RY_1Lo0R[_0RB1RY_---1R[_0LN0Lo_0LP1Lo_1LN1Lo_1LP0R[_0RD1LF_0RY---_1RD0RB_1RY---_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_---0LX_---1LF_---1LX_1R[0RB_1LF0RB_---0RD_0RB1RB_---1RD_0Lf0Lh_0Lh0RB_1Lf1Lh_1Lh1RB_0LP---_0RY---_1Lo---_1RY---_0Lm---_0Lo---_1Lm---_1Lo---_1LX0RJ_0RB0RL_1Lh1RJ_1RB1RL_0LF1LF_0LH---_1LF0RB_1LH---".
Definition tm0' := TM'_from_str "1R[0RY_1Lo0R[_0RB1RY_---1R[_0LN0LX_0LP1Lo_1LN1LX_1LP0R[_0RD1LF_0RY---_1RD0RB_1RY---_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_0Lh0LX_---1R[_1Lh1LX_1R[0RB_1R[0RB_1Lo0RD_0RB1RB_---1RD_0LN0Lh_0LP0RB_1LN1Lh_1LP1RB_0LP---_0RY---_1Lo---_1RY---_0Lm---_0Lo---_1Lm---_1Lo---_1LX0RJ_0RB0RL_1Lh1RJ_1RB1RL_0LF1R[_0LH---_1LF0RB_1LH---".
Definition tm1 := TM'_from_str "1LB0RF_1LC0RA_0LD1LB_1LG1LE_1LB---_0RA1RA_1RF0RA".
Definition tm2 := TM'_from_str "1LB0RF_1LC0RA_0LD1LB_1LG1LE_1LB1RH_0RA1RA_1RF0RA_1RH1RH".
Definition l0 := [1;0;0;1;0;1;0;0]%N.
Definition mp := mp_from_str "BoFPh[X".
Definition mp' := mp_from_str "BoFPh[X".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM143.


Module TM144.
Definition tm := TM_from_str "1LB0LF_1RC1LA_1RD0RC_0RE0RA_1RF---_1LA1LF".
Definition tm' := TM_from_str "1LB0LF_1RC0RF_1RD0RC_0RE0RA_1RF---_1LA1LF".
Definition tm0 := TM'_from_str "0RS0LP_1LP0LH_1RS0Lo_1Lo0Lp_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RR1RQ_0RT1LF_1RR1LH_1RT1Ln_1Rc0LF_1RZ0LH_1RC1LF_1RQ1LH_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_1Rj0Rc_1RS0RZ_---0RC_0Lo0RQ_0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_1LF1RZ_---0LF_1LH1RQ_---1LF_0Rj---_0Rl---_1Rj---_1Rl---_0Lo---_0Lp---_1Lo---_1Lp---_1RQ1LP_1LF1LH_1LH1Lo_1Ln1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm0' := TM'_from_str "0RS0LP_1LP0LH_1RS0Lo_1Lo0Lp_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1Rc0LP_1RZ0LH_1RC1LP_1RQ1LH_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_1Rj0Rc_1RS0RZ_---0RC_0Lo0RQ_0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_1LF1RZ_---0LF_1LH1RQ_---1LF_0Rj---_0Rl---_1Rj---_1Rl---_0Lo---_0Lp---_1Lo---_1Lp---_1RQ1LP_1LF1LH_1LH1Lo_1Ln1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm1 := TM'_from_str "1RB1RJ_0RC0RK_1RD---_1LE1LH_0LI0LF_1LE1LG_0LH0LL_1LI1LF_1RJ1LH_0RB0RJ_1RA0LF_1LH1LL".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0RK_1RD1RM_1LE1LH_0LI0LF_1LE1LG_0LH0LL_1LI1LF_1RJ1LH_0RB0RJ_1RA0LF_1LH1LL_1RM1RM".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "SZcjFonHPQCp".
Definition mp' := mp_from_str "SZcjFonHPQCp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM144.


Module TM145.
Definition tm := TM_from_str "1RB0RC_1LC0LB_1RD1LD_1LA0RE_1RF0RE_0RC---".
Definition tm' := TM_from_str "1RB1LA_1LC0LB_1RD1LD_1LA0RE_1RF0RE_0RC---".
Definition tm0 := TM'_from_str "0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_0L`1LM_0LM0LH_1L`0Rc_1LM1LH_0Rc1Rj_1LH0LV_1Rc0L`_0Ra0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ1LM_0R\0Ra_1RZ1LH_1R\1Ra_0LH0L^_1Rj0L`_1LH1L^_1Ra1L`_0LV0Ra_1LM0Rc_0LM1Ra_1LH1Rc_0LF0RS_0LH0Rj_1LF---_1LH0Ra_0Rj0Ra_0Rl0Rc_1Rj1Ra_1Rl1Rc_1RZ0RS_---0Rj_1LH---_---0Ra_0RQ---_0RS---_1RQ---_1RS---_1LM---_0LH---_0Rc---_1LH---".
Definition tm0' := TM'_from_str "0RJ0LV_0RL1LM_1RJ0LM_1RL1LH_0L`0LF_0LM0LH_1L`1LF_1LM1LH_0Rc1Rj_1LH0LV_1Rc0L`_0Ra0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ1LM_0R\0Ra_1RZ1LH_1R\1Ra_0LH0L^_1Rj0L`_1LH1L^_1Ra1L`_0LV0Ra_1LM0Rc_0LM1Ra_1LH1Rc_0LF0RS_0LH0Rj_1LF---_1LH0Ra_0Rj0Ra_0Rl0Rc_1Rj1Ra_1Rl1Rc_1RZ0RS_---0Rj_1LH---_---0Ra_0RQ---_0RS---_1RQ---_1RS---_1LM---_0LH---_0Rc---_1LH---".
Definition tm1 := TM'_from_str "1RB1LH_1LC0RF_0LD0LC_1RE0LG_0RA---_1RE1RI_1LH0RI_1LC1LH_0RE0RI".
Definition tm2 := TM'_from_str "1RB1LH_1LC0RF_0LD0LC_1RE0LG_0RA1RJ_1RE1RI_1LH0RI_1LC1LH_0RE0RI_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;0;0]%N.
Definition mp := mp_from_str "SZMVjc`Ha".
Definition mp' := mp_from_str "SZMVjc`Ha".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM145.


Module TM146.
Definition tm := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LE_0LB0RF_1RB1RD".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LE_0LB0RF_1RB0RF".
Definition tm0 := TM'_from_str "0RJ1Le_0RL---_1RJ1Lf_1RL---_0LX0LV_1RJ0LX_1LX1LV_1RZ1LX_0Rk0Ri_1L_0Rk_1Rk1Ri_---1Rk_0LF1L__0LH0RJ_1LF0Rk_1LH0RZ_0LM---_0LO---_1L_---_0RJ---_0L]---_0L_---_1L]---_1L_---_0LF1LF_0RJ0RZ_1L_0Rk_1RJ1RZ_0Le0Lf_0Lg0Lh_1Le1Lf_1Lg1Lh_1RJ0Ri_0RJ0Rk_0LX1Ri_1RJ1Rk_0LM1L__0LO0RJ_1LM0Rk_1LO0RZ_0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LX1L__1RJ0RJ_1LX0Rk_1RZ0RZ".
Definition tm0' := TM'_from_str "0RJ1Le_0RL---_1RJ1Lf_1RL---_0LX0LV_1RJ0LX_1LX1LV_1Ri1LX_0R\0RZ_1L_0R\_1R\1RZ_---1R\_0LF1L__0LH0RJ_1LF0R\_1LH0Ri_0LM---_0LO---_1L_---_0RJ---_0L]---_0L_---_1L]---_1L_---_0LF1LF_0RJ0Ri_1L_0R\_1RJ1Ri_0Le0Lf_0Lg0Lh_1Le1Lf_1Lg1Lh_1RJ0Ri_0RJ0Rk_0LX1Ri_1RJ1Rk_0LM1L__0LO0RJ_1LM0R\_1LO0Ri_0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LX1L__1RJ0RJ_1LX0R\_1Ri0Ri".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "ZJ_eMFfOkX".
Definition mp' := mp_from_str "iJ_eMFfO\X".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM146.


Module TM147.
Definition tm := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LE_0LB0RF_1RB0RF".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LF_0LB0RA_0LB0RB".
Definition tm0 := TM'_from_str "0RJ1Le_0RL---_1RJ1Lf_1RL---_0LX0LV_1RJ0LX_1LX1LV_1Ri1LX_0R\0RZ_1L_0R\_1R\1RZ_---1R\_0LF1L__0LH0RJ_1LF0R\_1LH0Ri_0LM---_0LO---_1L_---_0RJ---_0L]---_0L_---_1L]---_1L_---_0LF1LF_0RJ0Ri_1L_0R\_1RJ1Ri_0Le0Lf_0Lg0Lh_1Le1Lf_1Lg1Lh_1RJ0Ri_0RJ0Rk_0LX1Ri_1RJ1Rk_0LM1L__0LO0RJ_1LM0R\_1LO0Ri_0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LX1L__1RJ0RJ_1LX0R\_1Ri0Ri".
Definition tm0' := TM'_from_str "0RJ1Le_0RL---_1RJ1Ln_1RL---_0LX0LV_1RJ0LX_1LX1LV_1RZ1LX_0R\0RZ_1L_0R\_1R\1RZ_---1R\_0LF1L__0LH0RJ_1LF0R\_1LH0RZ_0LM---_0LO---_1L_---_0RJ---_0L]---_0L_---_1L]---_1L_---_0LF1LF_0RJ0RZ_1L_0R\_1RJ1RZ_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_1RJ0RA_0RJ0RC_0LX1RA_1RJ1RC_0LM1L__0LO0L__1LM0R\_1LO1L__1RJ0RI_0RJ0RK_0LX1RI_1RJ1RK_0LM1RJ_0LO0RJ_1LM1RZ_1LO0RZ".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "iJ_eMFfO\X".
Definition mp' := mp_from_str "ZJ_eMFnO\X".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM147.


Module TM148.
Definition tm := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LF_0LB0RA_0LB0RB".
Definition tm' := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ1Le_0RL---_1RJ1Ln_1RL---_0LX0LV_1RJ0LX_1LX1LV_1RZ1LX_0R\0RZ_1L_0R\_1R\1RZ_---1R\_0LF1L__0LH0RJ_1LF0R\_1LH0RZ_0LM---_0LO---_1L_---_0RJ---_0L]---_0L_---_1L]---_1L_---_0LF1LF_0RJ0RZ_1L_0R\_1RJ1RZ_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_1RJ0RA_0RJ0RC_0LX1RA_1RJ1RC_0LM1L__0LO0L__1LM0R\_1LO1L__1RJ0RI_0RJ0RK_0LX1RI_1RJ1RK_0LM1RJ_0LO0RJ_1LM1RZ_1LO0RZ".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0Rd_1RA0RA_0RC0Rb_1Lg0Rd_1RC1Rb_---1Rd_0LV1Lg_0LX0RJ_1LV0Rd_1LX0RA_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1Rd1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0Rd_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0Rd_1LO0RA".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "ZJ_eMFnO\X".
Definition mp' := mp_from_str "AJgmMVnOd`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM148.


Module TM149.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1RE_1LC1RE_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0Rd_1RA0RA_0RC0Rb_1Lg0Rd_1RC1Rb_---1Rd_0LV1Lg_0LX0RJ_1LV0Rd_1LX0RA_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1Rd1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0Rd_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0Rd_1LO0RA".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L`1Lg_1RJ0RJ_1L`0Rd_1Rb0Rb_0Rd0Rb_1Lg0Rd_1Rd1Rb_---1Rd_0LV1Lg_0LX0RJ_1LV0Rd_1LX0Rb_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1Rd1L^_1Rb1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0Rb_1Lg0Rd_1RJ1Rb_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0Rd_1LO0Rb".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "AJgmMVnOd`".
Definition mp' := mp_from_str "bJgmMVnOd`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM149.


Module TM150.
Definition tm := TM_from_str "1RB1RE_1LC1RE_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L`1Lg_1RJ0RJ_1L`0Rd_1Rb0Rb_0Rd0Rb_1Lg0Rd_1Rd1Rb_---1Rd_0LV1Lg_0LX0RJ_1LV0Rd_1LX0Rb_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1Rd1L^_1Rb1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0Rb_1Lg0Rd_1RJ1Rb_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0Rd_1LO0Rb".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L`1Lg_1RJ0RJ_1L`0RC_1Rb0Rb_0Rd0RA_1Lg0RC_1Rd1RA_---1RC_0LV1Lg_0LX0RJ_1LV0RC_1LX0Rb_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1RC1L^_1Rb1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0Rb_1Lg0RC_1RJ1Rb_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0RC_1LO0Rb".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "bJgmMVnOd`".
Definition mp' := mp_from_str "bJgmMVnOC`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM150.


Module TM151.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L`1Lg_1RJ0RJ_1L`0RC_1Rb0Rb_0Rd0RA_1Lg0RC_1Rd1RA_---1RC_0LV1Lg_0LX0RJ_1LV0RC_1LX0Rb_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1RC1L^_1Rb1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0Rb_1Lg0RC_1RJ1Rb_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0RC_1LO0Rb".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0RC_1RA0RA_0RC0RA_1Lg0RC_1RC1RA_---1RC_0LV1Lg_0LX0RJ_1LV0RC_1LX0RA_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1RC1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0RC_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0RC_1LO0RA".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "bJgmMVnOC`".
Definition mp' := mp_from_str "AJgmMVnOC`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM151.


Module TM152.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0RC_1RA0RA_0RC0RA_1Lg0RC_1RC1RA_---1RC_0LV1Lg_0LX0RJ_1LV0RC_1LX0RA_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1RC1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0RC_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0RC_1LO0RA".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0RC_1RA0RA_0RC0RA_1Lg0RC_1RC1RA_---1RC_0LV1Lg_0LX0RJ_1LV0RC_1LX0RA_0RJ1Lm_0RL---_1RJ1Ln_1RL---_0L`0L^_1RJ0L`_1L`1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0RC_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0RC_1LO0RA".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "AJgmMVnOC`".
Definition mp' := mp_from_str "AJgmMVnOC`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM152.


Module TM153.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1RE_1LC1RE_1RB1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0RC_1RA0RA_0RC0RA_1Lg0RC_1RC1RA_---1RC_0LV1Lg_0LX0RJ_1LV0RC_1LX0RA_0RJ1Lm_0RL---_1RJ1Ln_1RL---_0L`0L^_1RJ0L`_1L`1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0RC_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0RC_1LO0RA".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L`1Lg_1RJ0RJ_1L`0Rd_1Rb0Rb_0Rd0Rb_1Lg0Rd_1Rd1Rb_---1Rd_0LV1Lg_0LX0RJ_1LV0Rd_1LX0Rb_0RJ1Lm_0RL---_1RJ1Ln_1RL---_0L`0L^_1RJ0L`_1L`1L^_1Rb1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0Rb_1Lg0Rd_1RJ1Rb_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0Rd_1LO0Rb".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "AJgmMVnOC`".
Definition mp' := mp_from_str "bJgmMVnOd`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM153.


Module TM154.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LD_0LA1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LA_0LA1RF_0RA1RB".
Definition tm0 := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0LN_1LN0Rj_1LP1LN_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_---0Lm_0L]0Lo_1Rj1Lm_1L]1Lo_0Ra0LW_0Rc0LN_1Ra---_1Rc0L]_0LN0L]_0RC0L__1LN1L]_0RL1L__0LW0Rj_0Ra0Rl_---1Rj_1Ra1Rl_0LE1Lm_0LG0Lm_1LE1RY_1LG---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_0LW---".
Definition tm0' := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0LN_1LN0Rj_1LP1LN_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_---0Lm_0LW0Lo_1Rj1Lm_0Rj1Lo_0Ra0LW_0Rc0Ra_1Ra---_1Rc1Ra_0LN0LE_0RC0LG_1LN1LE_0RL1LG_0LW0Rj_0Ra0Rl_---1Rj_1Ra1Rl_0LE1Lm_0LG0Lm_1LE1RY_1LG---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_0LW---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "aWjCmYL".
Definition mp' := mp_from_str "aWjCmYL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM154.


Module TM155.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1RF_0LA1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC1LA_1RD0LE_1RB1RE_0RA0RF_0LD---".
Definition tm0 := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0RC_1LN0Rj_1LP0RL_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_---0Lm_1RC0Lo_1Rj1Lm_1RL1Lo_0Ra0Rj_0Rc0Rl_1Ra1Rj_1Rc1Rl_0LN1Lm_0RC0Lm_1LN1RY_0RL---_0LW0Rj_0Ra0Rl_---1Rj_1Ra1Rl_0LE1Lm_0LG0Lm_1LE1RY_1LG---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_0Rj---".
Definition tm0' := TM'_from_str "1Rb0RY_1LP0R[_1Le1RY_0Rk1R[_0LN0LW_0LP0RC_1LN0Rb_1LP0Rk_0RL1LW_0LW0Rb_1RL1LH_0Le1Rb_0LU0LF_0LW0LH_1LU1LF_1LW1LH_0RZ1Rb_0R\0LW_1RZ1Le_1R\0Le_0Le0Le_1RC0Lg_1Rb1Le_1Rk1Lg_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0Le1Le_0RC0Le_1Le1RY_0Rk---_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LW0Le_0RJ---_1LW1Le_0Rb---_0LW---_0RC---_0Le---_1RC---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0RC_0LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0RC_0LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "aWjCmYL".
Definition mp' := mp_from_str "JWbCeYk".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM155.


Module TM156.
Definition tm := TM_from_str "1LB0RD_0LC1LA_1RD0LE_1RB1RE_0RA0RF_0LD---".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1LD_0LA1RF_0RA1RB".
Definition tm0 := TM'_from_str "1Rb0RY_1LP0R[_1Le1RY_0Rk1R[_0LN0LW_0LP0RC_1LN0Rb_1LP0Rk_0RL1LW_0LW0Rb_1RL1LH_0Le1Rb_0LU0LF_0LW0LH_1LU1LF_1LW1LH_0RZ1Rb_0R\0LW_1RZ1Le_1R\0Le_0Le0Le_1RC0Lg_1Rb1Le_1Rk1Lg_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0Le1Le_0RC0Le_1Le1RY_0Rk---_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LW0Le_0RJ---_1LW1Le_0Rb---_0LW---_0RC---_0Le---_1RC---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0RC_1LN0Rj_1LP0RL_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_---0Lm_0L`0Lo_1Rj1Lm_1L`1Lo_0Ra0Rj_0Rc0RL_1Ra1Rj_1Rc1L`_0LN0L^_0RC0L`_1LN1L^_0RL1L`_0LW0Rj_0Ra0Rl_---1Rj_1Ra1Rl_0LE1Lm_0LG0Lm_1LE1RY_1LG---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_0Rj---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0RC_0LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0RC_0LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JWbCeYk".
Definition mp' := mp_from_str "aWjCmYL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM156.


Module TM157.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LF_0LA1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LF_1LC1RF_0RA1RB".
Definition tm0 := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0LW_1LN0Rj_1LP1LW_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_---0Lm_0Lm0Lo_1Rj1Lm_1Lm1Lo_0Ra1Rj_0Rc0LW_1Ra1Lm_1Rc0Lm_0LN0Lm_0RC0Lo_1LN1Lm_0RL1Lo_0LW0Rj_0Ra0Rl_---1Rj_1Ra1Rl_0LE1Lm_0LG0Lm_1LE1RY_1LG---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_1Rj---".
Definition tm0' := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0LW_1LN0Rj_1LP1LW_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_0Lm0Lm_0Lm0Lo_1Rj1Lm_1Lm1Lo_0Ra1Rj_0Rc0LW_1Ra1Lm_1Rc0Lm_0Lm0Lm_0RC0Lo_1Lm1Lm_0RL1Lo_0LW0Rj_1LW0Rl_0Lm1Rj_1Lm1Rl_0LV1Lm_0LX0Lm_1LV1RY_1LX---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_1Rj---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA1RC_0LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA1RC_0LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "aWjCmYL".
Definition mp' := mp_from_str "aWjCmYL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM157.


Module TM158.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LF_1LC1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1LB_0LA1RF_0RA1RB".
Definition tm0 := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0LW_1LN0Rj_1LP1LW_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_0Lm0Lm_0Lm0Lo_1Rj1Lm_1Lm1Lo_0Ra1Rj_0Rc0LW_1Ra1Lm_1Rc0Lm_0Lm0Lm_0RC0Lo_1Lm1Lm_0RL1Lo_0LW0Rj_1LW0Rl_0Lm1Rj_1Lm1Rl_0LV1Lm_0LX0Lm_1LV1RY_1LX---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_1Rj---".
Definition tm0' := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0LW_1LN0Rj_1LP1LW_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_---0Lm_---0Lo_1Rj1Lm_---1Lo_0Ra1Rj_0Rc---_1Ra1Lm_1Rc---_0LN0LN_0RC0LP_1LN1LN_0RL1LP_0LW0Rj_0Ra0Rl_---1Rj_1Ra1Rl_0LE1Lm_0LG0Lm_1LE1RY_1LG---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_1Rj---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA1RC_0LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA1RC_0LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "aWjCmYL".
Definition mp' := mp_from_str "aWjCmYL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM158.


Module TM159.
Definition tm := TM_from_str "1LB1LF_1LC1LE_1RD---_0RF0RE_0LA1RD_1LA0RF".
Definition tm' := TM_from_str "1LB1LF_1LC1LD_1RB---_0LA1RE_0RF0RD_1LA0RF".
Definition tm0 := TM'_from_str "1RZ1LP_1LG0Ri_---1Lp_1RZ1Ri_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0Rc1LN_---0Rc_1Rc1Ln_---1Rc_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RZ---_0R\---_1RZ---_1R\---_1Lh---_0Lh---_1Ri---_1RZ---_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0LP0LN_1LX0Rk_1LP1LN_0Ri0Rc_0LX0RZ_0LH0R\_0Lh1RZ_1LX1R\_0LE1Lh_0LG0Lh_1LE1Ri_1LG1RZ_1LX0Ri_1LH0Rk_1Lh1Ri_0Ri1Rk_0LF0LP_0LH1LX_1LF1LP_1LH0Ri".
Definition tm0' := TM'_from_str "1Rb1LP_1LG0Ri_---1Lp_1Rb1Ri_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0R[1LN_---0R[_1R[1Ln_---1R[_0LV0L^_0LX0L`_1LV1L^_1LX1L`_0RJ---_0RL---_1RJ---_1RL---_------_0L`---_------_1Rb---_0LX0Rb_0LH0Rd_0L`1Rb_1LX1Rd_0LE1L`_0LG0L`_1LE1Ri_1LG1Rb_0Ri0RY_0Rk0R[_1Ri1RY_1Rk1R[_0LP0LN_1LX0Rk_1LP1LN_0Ri0R[_1LX0Ri_1LH0Rk_1L`1Ri_0Ri1Rk_0LF0LP_0LH1LX_1LF1LP_1LH0Ri".
Definition tm1 := TM'_from_str "0LB1RI_1LC1RI_1LL1LD_0LE1LH_1LG1LF_1LE0RK_1LH1LB_1RI---_0RJ0RA_1LB1RK_1LH0RK_0LH0LB".
Definition tm2 := TM'_from_str "0LB1RI_1LC1RI_1LL1LD_0LE1LH_1LG1LF_1LE0RK_1LH1LB_1RI1RM_0RJ0RA_1LB1RK_1LH0RK_0LH0LB_1RM1RM".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "chGnHpPXZkiN".
Definition mp' := mp_from_str "[`GnHpPXbkiN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM159.


Module TM160.
Definition tm := TM_from_str "1LB0LF_1RC1LE_0RE0RD_0RB0LD_1LA0RD_0LB---".
Definition tm' := TM_from_str "1LB0LF_1RC1LE_0RE0RD_0RB1RC_1LA0RD_0LB---".
Definition tm0 := TM'_from_str "0R[1Lh_1LH---_1R[0Lf_0R[---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RR1LP_0RT0RR_1RR1Lo_1RT1RR_1Lh0Lf_1RI0Lh_1RY1Lf_1RR1Lh_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP0RR_0RI0Rc_1LP1LP_0RR0R[_0RI0RR_0RK0Rc_1RI1RR_1RK0L]_0Rc0L]_0LH0L__0R[1L]_1LH1L__1RR0RY_1LM0R[_1Lh1RY_---1R[_0LF0RR_0LH0Rc_1LF1LP_1LH0R[_0Rc---_0LH---_1Rc---_0Rc---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0R[1Lh_1LH---_1R[0Lf_0R[---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RR1LP_0RT0RR_1RR1Lo_1RT1RR_1Lh0Lf_1RI0Lh_1RY1Lf_1RR1Lh_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP0RR_0RI0Rc_1LP1LP_0RR0R[_0RI0RR_0RK0RT_1RI1RR_1RK1RT_0Rc1Lh_0LH1RI_0R[1RY_1LH1RR_1RR0RY_1LM0R[_1Lh1RY_---1R[_0LF0RR_0LH0Rc_1LF1LP_1LH0R[_0Rc---_0LH---_1Rc---_0Rc---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB---_1LC0RI_1LG1LD_1LE---_1LB0LF_0LC0RA_1RH1LB_0RA0RI_1RJ1RH_0RH1LG".
Definition tm2 := TM'_from_str "1LB---_1LC0RI_1LG1LD_1LE1RK_1LB0LF_0LC0RA_1RH1LB_0RA0RI_1RJ1RH_0RH1LG_1RK1RK".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "chHoMfPR[I".
Definition mp' := mp_from_str "chHoMfPR[I".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM160.


Module TM161.
Definition tm := TM_from_str "1LB0LF_1RC1LC_0RE0RD_0RB0LD_1LA1LE_0LB---".
Definition tm' := TM_from_str "1LB0LF_1RC1LC_0RE0RD_0RB1RC_1LA1LE_0LB---".
Definition tm0 := TM'_from_str "0R[1LX_1LH---_1R[0LV_0R[---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RR1LP_0RT0RR_1RR1Lo_1RT1RR_1LX0LV_1RI0LX_1Lo1LV_1RR1LX_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP0RR_0LH0Rc_1LP1LP_1LH0R[_0RI0RR_0RK0Rc_1RI1RR_1RK0L]_0Rc0L]_0LH0L__0R[1L]_1LH1L__1RR1LP_1LM1LH_1LX1Lo_---1Lh_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0Rc---_0LH---_1Rc---_0Rc---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0R[1LX_1LH---_1R[0LV_0R[---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RR1LP_0RT0RR_1RR1Lo_1RT1RR_1LX0LV_1RI0LX_1Lo1LV_1RR1LX_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP0RR_0LH0Rc_1LP1LP_1LH0R[_0RI0RR_0RK0RT_1RI1RR_1RK1RT_0Rc1LX_0LH1RI_0R[1Lo_1LH1RR_1RR1LP_1LM1LH_1LX1Lo_---1Lh_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0Rc---_0LH---_1Rc---_0Rc---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB1LD_1LC0RI_1LG1LD_1LE---_1LB0LF_0LC0RA_1RH1LB_0RA0RI_1RJ1RH_0RH1LG".
Definition tm2 := TM'_from_str "1LB1LD_1LC0RI_1LG1LD_1LE1RK_1LB0LF_0LC0RA_1RH1LB_0RA0RI_1RJ1RH_0RH1LG_1RK1RK".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "cXHoMVPR[I".
Definition mp' := mp_from_str "cXHoMVPR[I".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM161.


Module TM162.
Definition tm := TM_from_str "1LB0RF_1LC0LA_0LD0LB_1RE0LF_1RB0RE_1RE---".
Definition tm' := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_1RE---".
Definition tm0 := TM'_from_str "1L_0Ri_1LN0Rk_1LO1Ri_0Rc1Rk_0LN0RL_0LP---_1LN0Rc_1LP---_1Rb0LX_1LV0Rb_1Lm0LG_1LE1Rb_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0L__1LE0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb0RL_0Rd---_1Rb1RL_1Rd---_1LE0Lm_1RJ0Lo_1Rb1Lm_1Ra1Lo_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_0Rb---_0Rd---_1Rb---_1Rd---_1LE---_1RJ---_1Rb---_1Ra---".
Definition tm0' := TM'_from_str "1L_0RY_1LN0R[_1LO1RY_0Rc1R[_0LN0RL_0LP1LE_1LN0Rc_1LP1Rb_1Rb0LX_1LV0Rb_1Lm0LG_1LE1Rb_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0L__1LE0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb0RL_0Rd---_1Rb1RL_1Rd---_1LE0Lm_1RJ0Lo_1Rb1Lm_1Ra1Lo_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_0Rb---_0Rd---_1Rb---_1Rd---_1LE---_1RJ---_1Rb---_1Ra---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_1LB---".
Definition tm2 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_1LB1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "LENGX_bcJOVam".
Definition mp' := mp_from_str "LENGX_bcJOVam".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM162.


Module TM163.
Definition tm := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_1RE---".
Definition tm' := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_0RC---".
Definition tm0 := TM'_from_str "1L_0RY_1LN0R[_1LO1RY_0Rc1R[_0LN0RL_0LP1LE_1LN0Rc_1LP1Rb_1Rb0LX_1LV0Rb_1Lm0LG_1LE1Rb_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0L__1LE0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb0RL_0Rd---_1Rb1RL_1Rd---_1LE0Lm_1RJ0Lo_1Rb1Lm_1Ra1Lo_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_0Rb---_0Rd---_1Rb---_1Rd---_1LE---_1RJ---_1Rb---_1Ra---".
Definition tm0' := TM'_from_str "1L_0RY_1LN0R[_1LO1RY_0Rc1R[_0LN0RL_0LP1LE_1LN0Rc_1LP1Rb_1Rb0LX_1LV0Rb_1Lm0LG_1LE1Rb_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0L__1LE0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb0RL_0Rd---_1Rb1RL_1Rd---_1LE0Lm_1RJ0Lo_1Rb1Lm_1Ra1Lo_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_0RQ---_0RS---_1RQ---_1RS---_1LE---_0LV---_1Rb---_1LV---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_1LB---".
Definition tm2 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_1LB1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "LENGX_bcJOVam".
Definition mp' := mp_from_str "LENGX_bcJOVam".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM163.


Module TM164.
Definition tm := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_0RB---".
Definition tm' := TM_from_str "1LB0RD_1LC0LA_0RD0LB_1RF1LE_0LD---_1RB0RF".
Definition tm0 := TM'_from_str "1L_0RY_1LN0R[_1LO1RY_0Rc1R[_0LN0RL_0LP0L__1LN0Rc_1LP1L__1Rb0LX_1LV0Rb_1Lm0LG_1LE1Rb_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0L__0L_0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb1Rb_0Rd---_1Rb1Lm_1Rd---_1LE0Lm_1RJ0Lo_1Rb1Lm_1Ra1Lo_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_0RI---_0RK---_1RI---_1RK---_0L_---_0LN---_1L_---_1LN---".
Definition tm0' := TM'_from_str "1L_0RY_1LN0R[_1LO1RY_0Rk1R[_0LN0RL_0LP0L__1LN0Rk_1LP1L__1Rj0LX_1LV0Rj_1Lf0LG_1LE1Rj_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RY0L__0R[0LN_1RY0LO_1R[0RL_0RL0LM_0L_0LO_0Rk1LM_1L_1LO_0Rj1Rj_0Rl---_1Rj1Lf_1Rl---_1LE0Lf_1RJ0Lh_1Rj1Lf_1Ri1Lh_0RL---_0L_---_1RL---_------_0L]---_0L_---_1L]---_1L_---_0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LO1LV_0RL0RJ_1LO0Rj_0Rk0Ri".
Definition tm1 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_0LF---".
Definition tm2 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_0LF1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "LENGX_bcJOVam".
Definition mp' := mp_from_str "LENGX_jkJOVif".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM164.


Module TM165.
Definition tm := TM_from_str "1LB0RD_1LC0LA_0RD0LB_1RF1LE_0LD---_1RB0RF".
Definition tm' := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE1LF_1RB0RE_0LD---".
Definition tm0 := TM'_from_str "1L_0RY_1LN0R[_1LO1RY_0Rk1R[_0LN0RL_0LP0L__1LN0Rk_1LP1L__1Rj0LX_1LV0Rj_1Lf0LG_1LE1Rj_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RY0L__0R[0LN_1RY0LO_1R[0RL_0RL0LM_0L_0LO_0Rk1LM_1L_1LO_0Rj1Rj_0Rl---_1Rj1Lf_1Rl---_1LE0Lf_1RJ0Lh_1Rj1Lf_1Ri1Lh_0RL---_0L_---_1RL---_------_0L]---_0L_---_1L]---_1L_---_0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LO1LV_0RL0RJ_1LO0Rj_0Rk0Ri".
Definition tm0' := TM'_from_str "1L_0RY_1LN0R[_1LO1RY_0Rc1R[_0LN0RL_0LP0L__1LN0Rc_1LP1L__1Rb0LX_1LV0Rb_1Ln0LG_1LE1Rb_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0L__0L_0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb1Rb_0Rd---_1Rb1Ln_1Rd---_1LE0Ln_1RJ0Lp_1Rb1Ln_1Ra1Lp_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_0RL---_0L_---_1RL---_------_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_0LF---".
Definition tm2 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_0LF1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "LENGX_jkJOVif".
Definition mp' := mp_from_str "LENGX_bcJOVan".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM165.


Module TM166.
Definition tm := TM_from_str "1LB0RF_1LC0LA_0LD0LB_1RE1LA_1RB0RE_1RE---".
Definition tm' := TM_from_str "1LB---_1LC0LF_0LD0LB_1RE1LA_1RB0RE_1LB0RD".
Definition tm0 := TM'_from_str "1L_0Ri_1LN0Rk_1LO1Ri_0Rc1Rk_0LN0RL_0LP---_1LN0Rc_1LP---_1Rb0LX_1LV0Rb_1LF0LG_1LE1Rb_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0L__0LP0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb1LX_0Rd---_1Rb1LG_1Rd---_1LE0LF_1RJ0LH_1Rb1LF_1Ra1LH_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_0Rb---_0Rd---_1Rb---_1Rd---_1LE---_1RJ---_1Rb---_1Ra---".
Definition tm0' := TM'_from_str "1L_---_1LN---_1LO---_0Rc---_0LN---_0LP---_1LN---_1LP---_1Rb0LX_1LV0Rb_1LF0Lo_1Lm1Rb_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0RL0L__0LP0LN_1RL0LO_---0RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rb1LX_0Rd---_1Rb1Lo_1Rd---_1Lm0LF_1RJ0LH_1Rb1LF_1Ra1LH_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO1LV_0RL0RJ_1LO0Rb_0Rc0Ra_1L_0RY_1LN0R[_1LO1RY_0Rc1R[_0LN0RL_0LP0LP_1LN0Rc_1LP1LP".
Definition tm1 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_0LN---_1LE1LD".
Definition tm2 := TM'_from_str "1LB1RG_0LC0RA_0LE0LD_1LC0RH_1LF1LJ_1RG1LM_0RA0RH_1RI1RL_1LK0RG_1LK1LB_0LF0LJ_0RI0RL_0LN1RO_1LE1LD_1RO1RO".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "LENGX_bcJOVaFP".
Definition mp' := mp_from_str "LmNoX_bcJOVaFP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM166.


Module TM167.
Definition tm := TM_from_str "1RB0RF_1LC0LF_1LD0LC_1LE0LA_1LF---_1RA1RF".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LF---_1RA1RF".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW0RL_1RL0RD_1LW0Rk_1Rk0Rl_1Lh0RL_1L^0RD_1LG1RL_1LU1RD_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_1Lp0Lh_1LW0L^_---0LG_0Rk0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_1Rj1L^_---0RB_1Rl1LU_---1RB_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG_0Rk---_0Rl---_1Rk---_1Rl---_0Ln---_0Lp---_1Ln---_1Lp---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LU1RL_1RB1RD_1RD1Rk_1Rj1Rl".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW0RL_1RL0RD_1LW0Rk_1Rk0Rl_1Lh0RB_1L^0RD_1LG1RB_1LU1RD_0LV1LU_0LX1RB_1LV1RD_1LX1Rj_1Lp0Lh_1LW0L^_---0LG_0Rk0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_1Rj1L^_---0RB_1Rl1LU_---1RB_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG_0Rk---_0Rl---_1Rk---_1Rl---_0Ln---_0Lp---_1Ln---_1Lp---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LU1RL_1RB1RD_1RD1Rk_1Rj1Rl".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_0LF0LD_1LE0RK_1LC1LB_1LG---_1RH1RI_0RJ0RI_1RJ1RI_1RA1RK_1RL1RH_0RA0RK".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_0LF0LD_1LE0RK_1LC1LB_1LG1RM_1RH1RI_0RJ0RI_1RJ1RI_1RA1RK_1RL1RH_0RA0RK_1RM1RM".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "LU^GWhpjlDkB".
Definition mp' := mp_from_str "LU^GWhpjlDkB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM167.


Module TM168.
Definition tm := TM_from_str "1RB0RC_1LC1LD_1RD0LB_1LF1RE_1RA0RE_---0LB".
Definition tm' := TM_from_str "1RB0RC_1LC1LD_1RD0LB_0LF1RE_1RA0RE_---1RB".
Definition tm0 := TM'_from_str "0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_0LO1LV_1RB0LV_1LO0Rd_1Ra1LV_0Rd---_1LV0Rc_1Rd1LO_1L^1Rc_0LV0L^_0LX0L`_1LV1L^_1LX1L`_0RZ1RD_0R\0Lp_1RZ0LO_1R\1RB_0LO0LM_1RD0LO_1LO1LM_1Rc1LO_---0Rb_1LV0Rd_---1Rb_1L^1Rd_0Ln1RL_0Lp1RB_1Ln1RS_1Lp1Ra_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1L^0RL_1RZ0RB_1Rc0RS_0LO0Ra_---1RD_---0Lp_---0LO_---1RB_---0LM_---0LO_---1LM_---1LO".
Definition tm0' := TM'_from_str "0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_0LO1LV_1RB0LV_1LO0Rd_1Ra1LV_0Rd---_1LV0Rc_1Rd1LO_1L^1Rc_0LV0L^_0LX0L`_1LV1L^_1LX1L`_0RZ1RD_0R\0Lo_1RZ0LO_1R\1RB_0LO0LM_1RD0LO_1LO1LM_1Rc1LO_---0Rb_1LV0Rd_---1Rb_1L^1Rd_0Lm1RL_0Lo1RB_1Lm1RS_1Lo1Ra_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1L^0RL_1RZ0RB_1Rc0RS_0LO0Ra_---0RJ_---0RL_---1RJ_---1RL_---0LO_---1RB_---1LO_---1Ra".
Definition tm1 := TM'_from_str "1LB0RH_1RF0LC_1LB1LD_0LE1RJ_---1LC_1RK1RG_1RA0LC_1RF1RI_1RJ1RL_0RK0RG_1LD1RI_0RJ0RL".
Definition tm2 := TM'_from_str "1LB0RH_1RF0LC_1LB1LD_0LE1RJ_1RM1LC_1RK1RG_1RA0LC_1RF1RI_1RJ1RL_0RK0RG_1LD1RI_0RJ0RL_1RM1RM".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "ZVO^pDSdcBLa".
Definition mp' := mp_from_str "ZVO^oDSdcBLa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM168.


Module TM169.
Definition tm := TM_from_str "1LB---_1RC1RB_1RD0RB_1LE1RC_1LF0LE_1LA0LC".
Definition tm' := TM_from_str "1LB---_1RC1RB_1RD0RB_1LE0LB_1LF0LE_1LA0LC".
Definition tm0 := TM'_from_str "0RK---_0RL---_1RK---_1RL---_0LN---_0LP---_1LN---_1LP---_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_1Le1R\_1RR1RT_1RT1RK_1RJ1RL_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0Lg0R\_1R\0RT_1Lg0RK_1RK0RL_1LH0RR_1Ln0RT_1LW1RR_1Le1RT_0Lf1Le_0Lh1RR_1Lf1RT_1Lh1RJ_1LP0LH_1Lg0Ln_---0LW_0RK0Le_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_1RJ1Ln_---0RR_1RL1Le_---1RR_0LF0LU_0LH0LW_1LF1LU_1LH1LW".
Definition tm0' := TM'_from_str "0RK---_0RL---_1RK---_1RL---_0LN---_0LP---_1LN---_1LP---_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_1Le1R\_1RR1RT_1RT1RK_1RJ1RL_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0Lg0R\_1R\0RT_1Lg0RK_1RK0RL_1LH0R\_1Ln0RT_1LW1R\_1Le1RT_0Lf0LM_0Lh0LO_1Lf1LM_1Lh1LO_1LP0LH_1Lg0Ln_---0LW_0RK0Le_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_1RJ1Ln_---0RR_1RL1Le_---1RR_0LF0LU_0LH0LW_1LF1LU_1LH1LW".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_0LI0LE_1LH0RF_1RG1RK_0RB0RF_1LD1LC_1LJ---_1RK1RL_0RA0RL_1RA1RL".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_0LI0LE_1LH0RF_1RG1RK_0RB0RF_1LD1LC_1LJ1RM_1RK1RL_0RA0RL_1RA1RL_1RM1RM".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "T\enWKRgHPJL".
Definition mp' := mp_from_str "T\enWKRgHPJL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM169.


Module TM170.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RC1RE_0RF0RA_1LD---".
Definition tm' := TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RC1RE_1RF0RA_0LE---".
Definition tm0 := TM'_from_str "1Rd0RZ_1LV0R\_1Lg1RZ_1LM1R\_0LN1RD_0LP1Rk_1LN1Lg_1LP1RC_0R\1RT_1LX0LV_1R\0Lg_1LX0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RB1Rd_0RD1Rd_1RB1Lg_1RD1Lg_0LO0Le_1RT0Lg_1LO1Le_1Rd1Lg_0RR0Rb_0RT0Rd_1RR1Rb_1RT1Rd_1LM1Lg_0LX1Lg_1R\---_1LX1RZ_0Ri0RA_0Rk0RC_1Ri1RA_1Rk1RC_0LX0LX_---0RT_1LX1LX_---0Rd_1Rd---_0RC---_1Lg---_1RC---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "1Rd0RZ_1LV0R\_1Lg1RZ_1LM1R\_0LN1RD_0LP1Rl_1LN1Lg_1LP1RC_0R\1RT_1LX0LV_1R\0Lg_1LX0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RB1Rd_0RD1Rd_1RB1Lg_1RD1Lg_0LO0Le_1RT0Lg_1LO1Le_1Rd1Lg_0RR0Rb_0RT0Rd_1RR1Rb_1RT1Rd_1LM1Lg_0LX1Lg_1R\---_1LX1RZ_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_0LX0LX_---0RT_1LX1LX_---0Rd_1Rd---_1Rd---_1Lg---_1Lg---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB1RK_0LC0LB_1RI0LD_1LE1LE_1RF1LD_1RJ1RG_1LD1RH_0RI0RF_1RA1LD_1LD---_1RI1RF".
Definition tm2 := TM'_from_str "1LB1RK_0LC0LB_1RI0LD_1LE1LE_1RF1LD_1RJ1RG_1LD1RH_0RI0RF_1RA1LD_1LD1RL_1RI1RF_1RL1RL".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "DMVgXdCZTk\".
Definition mp' := mp_from_str "DMVgXdCZTl\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM170.


Module TM171.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RC1RE_1RF0RA_0LE---".
Definition tm' := TM_from_str "1LB---_1LC0LB_1RD0LF_1LB1RE_1RC1RF_0RA0RD".
Definition tm0 := TM'_from_str "1Rd0RZ_1LV0R\_1Lg1RZ_1LM1R\_0LN1RD_0LP1Rl_1LN1Lg_1LP1RC_0R\1RT_1LX0LV_1R\0Lg_1LX0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RB1Rd_0RD1Rd_1RB1Lg_1RD1Lg_0LO0Le_1RT0Lg_1LO1Le_1Rd1Lg_0RR0Rb_0RT0Rd_1RR1Rb_1RT1Rd_1LM1Lg_0LX1Lg_1R\---_1LX1RZ_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_0LX0LX_---0RT_1LX1LX_---0Rd_1Rd---_1Rd---_1Lg---_1Lg---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "1Rl---_1LV---_1Lo---_1LM---_0LN---_0LP---_1LN---_1LP---_0Rd1RT_1LX0LV_1Rd0Lo_1LX0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ1Rl_0R\1Rl_1RZ1Lo_1R\1Lo_0LO0Lm_1RT0Lo_1LO1Lm_1Rl1Lo_1Rl0Rb_1LV0Rd_1Lo1Rb_1LM1Rd_0LN1R\_0LP1RC_1LN1Lo_1LP1R[_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_1LM1Lo_0LX1Lo_1Rd---_1LX1Rb_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LX0LX_---0RT_1LX1LX_---0Rl".
Definition tm1 := TM'_from_str "1LB1RK_0LC0LB_1RI0LD_1LE1LE_1RF1LD_1RJ1RG_1LD1RH_0RI0RF_1RA1LD_1LD---_1RI1RF".
Definition tm2 := TM'_from_str "1LB1RK_0LC0LB_1RI0LD_1LE1LE_1RF1LD_1RJ1RG_1LD1RH_0RI0RF_1RA1LD_1LD1RL_1RI1RF_1RL1RL".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "DMVgXdCZTl\".
Definition mp' := mp_from_str "\MVoXl[bTCd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM171.


Module TM172.
Definition tm := TM_from_str "1RB0RF_1LC1RA_0LE0LD_0LB1LC_1RA0RA_0RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_0LE0LD_0LB0RD_1RA0RA_0RE---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0RB_1RL---_1L_0RA_1Rk---_1RD0RB_1LM0RD_0RD1RB_1LV1RD_0LV1LV_0LX1Ra_1LV1RD_1LX---_0RL0LV_0RJ0Lg_1RL1LV_1RJ0L__0Le0L]_0Lg0L__1Le1L]_1Lg1L__0Lg1RD_0RL1LM_0L_0RD_1RL1LV_0LM0LV_0LO0LX_1LM1LV_1LO1LX_0RB0RA_0RD0RC_1RB1RA_1RD1RC_1LV1LM_1Ra0Ra_1RD0RD_------_0Ra---_0Rc---_1Ra---_1Rc---_0RL---_0RJ---_0Rk---_0Ri---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0RB_1RL---_1L_0RA_1Rk---_1RD0RB_1LM0RD_0RD1RB_1LV1RD_0LV1LV_0LX1Ra_1LV1RD_1LX---_0RL0LV_0RJ0Lg_1RL1LV_1RJ0L__0Le0L]_0Lg0L__1Le1L]_1Lg1L__0Lg0RY_0RL0R[_0L_1RY_1RL1R[_0LM0LV_0LO0Lg_1LM1LV_1LO0RY_0RB0RA_0RD0RC_1RB1RA_1RD1RC_1LV1LM_1Ra0Ra_1RD0RD_------_0Ra---_0Rc---_1Ra---_1Rc---_0RL---_0RJ---_0Rk---_0Ri---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LF_1RE0RE_1RB1RH_1LG1LC_0LC1LC_1RI---_0RA0RJ_0RK0RL_1LG0RE_0RI---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LF_1RE0RE_1RB1RH_1LG1LC_0LC1LC_1RI1RM_0RA0RJ_0RK0RL_1LG0RE_0RI1RM_1RM1RM".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "BLVgD_MkaAJi".
Definition mp' := mp_from_str "BLVgD_MkaAJi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM172.


Module TM173.
Definition tm := TM_from_str "1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD".
Definition tm' := TM_from_str "1RB---_1LB0LC_0LD0RA_0LE1RA_0RF0LC_1RE1RC".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Le---_1L_---_0RJ---_0RZ0LU_1Le0RJ_1RZ0RJ_0RJ1RJ_0LV0L]_0LX0L__1LV1L]_1LX1L__0Ri0LU_0Rk0RJ_1Ri0RJ_1Rk1RJ_0Rk0L]_0RL0L__0RJ1L]_0RC1L__0Rk0RA_0RL0RC_0L]1RA_1RL1RC_0Le1Le_0Lg---_1Le0RJ_1Lg---_0RR0RB_0Le0RD_1RR1RB_1Le1RD_0LU0RJ_0LW---_1LU1RJ_1LW---_0RR0RZ_0RT0R\_1RR1RZ_1RT1R\_1RR0RJ_1Le1RJ_1RZ1RJ_0RJ---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1L]---_1LW---_0RJ---_1LP0Le_1L]0RJ_1LW0RJ_0RJ1RJ_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0Rk0RA_0RL0RC_0LU1RA_1RL1RC_0L]1L]_0L_---_1L]0RJ_1L_---_0Rb0RB_0L]0RD_1Rb1RB_1L]1RD_0Le0RJ_0Lg---_1Le1RJ_1Lg---_0Ri0Le_0Rk0RJ_1Ri0RJ_1Rk1RJ_0Rk0LU_0RL0LW_0RJ1LU_0RC1LW_0Rb0RR_0Rd0RT_1Rb1RR_1Rd1RT_1Rb0RJ_1L]1RJ_1RR1RJ_0RJ---".
Definition tm1 := TM'_from_str "1LB0RA_0LC0RA_0RD0LF_1RE1RG_0RD0RA_0LB1LB_0RH0RI_0RA1RA_1RA---".
Definition tm2 := TM'_from_str "1LB0RA_0LC0RA_0RD0LF_1RE1RG_0RD0RA_0LB1LB_0RH0RI_0RA1RA_1RA1RJ_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;0;0]%N.
Definition mp := mp_from_str "JeUkR]ZLC".
Definition mp' := mp_from_str "J]ekbURLC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM173.


Module TM174.
Definition tm := TM_from_str "1LB1RA_1LC0RE_1LD1RF_0RA0LD_1RC0RE_---1LD".
Definition tm' := TM_from_str "1LB1RA_1LC0RE_1LD0RF_0RA0LD_1RC0RE_---0LE".
Definition tm0 := TM'_from_str "1L`0RB_0Ra0RD_1L_1RB_1Ra1RD_0LN0RR_0LP1Ra_1LN0Ra_1LP1RD_0RD0Ra_1LX0Rc_1L_1Ra_1L]1Rc_0LV1LX_0LX0RR_1LV0Rl_1LX0Ra_0RB0Rj_1LX0Rl_1RB1Rj_1L]1Rl_0L^---_0L`0L__1L^---_1L`1L__0RA1L`_0RC0LX_1RA1L__1RC0L]_0LX0L]_0Ra0L__1LX1L]_0RD1L__0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0L_1LX_---0RR_1L_0Rl_1L]0Ra_---0RB_---1LX_---1RB_---1L]_---0L^_---0L`_---1L^_---1L`".
Definition tm0' := TM'_from_str "1L`0RB_0Ra0RD_1L_1RB_1Ra1RD_0LN0RR_0LP1Ra_1LN0Ra_1LP1RD_0RD0Ra_1LX0Rc_1L_1Ra_1L]1Rc_0LV1LX_0LX0RR_1LV0Rk_1LX0Ra_0RB0Ri_1LX0Rk_1RB1Ri_1L]1Rk_0L^---_0L`0L__1L^---_1L`1L__0RA1L`_0RC0LX_1RA1L__1RC0L]_0LX0L]_0Ra0L__1LX1L]_0RD1L__0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0L_1LX_---0RR_1L_0Rk_1L]0Ra_---1LX_---0RR_---1L]_---1RR_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1LB0RH_1LC1LF_0RD1LF_1RE1RD_0RA0RE_1LB1LG_0LB0LG_---1LG".
Definition tm2 := TM'_from_str "1LB0RH_1LC1LF_0RD1LF_1RE1RD_0RA0RE_1LB1LG_0LB0LG_1RI1LG_1RI1RI".
Definition l0 := [0;1;1;0;0;0;0;0]%N.
Definition mp := mp_from_str "RX`Da_]l".
Definition mp' := mp_from_str "RX`Da_]k".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM174.


Module TM175.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF0RF_0LB---".
Definition tm' := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_0LB---".
Definition tm0 := TM'_from_str "0RS0LO_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Ln0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1RD0Ri_---0Rk_1L^1Ri_---1Rk_0Ln1LO_0Lp---_1Ln1RD_1Lp---_0RD---_0LH---_1RD---_0LO---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RS0LO_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Ln0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1RD0RR_---0RT_1L^1RR_---1RT_0Ln1LO_0Lp1RB_1Ln1RD_1Lp1RQ_0RD---_0LH---_1RD---_0LO---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LI_1RG1LF_1LD1LB_0RH0RG_1LD0RA_1LJ1RA_0LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LI_1RG1LF_1LD1LB_0RH0RG_1LD0RA_1LJ1RA_0LB1RK_1RK1RK".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "DO^HP`QBgn".
Definition mp' := mp_from_str "DO^HP`QBgn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM175.


Module TM176.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_0LB---".
Definition tm' := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_1RB---".
Definition tm0 := TM'_from_str "0RS0LO_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Ln0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1RD0RR_---0RT_1L^1RR_---1RT_0Ln1LO_0Lp1RB_1Ln1RD_1Lp1RQ_0RD---_0LH---_1RD---_0LO---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RS0LO_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Ln0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1RD0RR_---0RT_1L^1RR_---1RT_0Ln1LO_0Lp1RB_1Ln1RD_1Lp1RQ_0RJ---_0RL---_1RJ---_1RL---_1RD---_0LO---_1RS---_1LO---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LI_1RG1LF_1LD1LB_0RH0RG_1LD0RA_1LJ1RA_0LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LI_1RG1LF_1LD1LB_0RH0RG_1LD0RA_1LJ1RA_0LB1RK_1RK1RK".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "DO^HP`QBgn".
Definition mp' := mp_from_str "DO^HP`QBgn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM176.


Module TM177.
Definition tm := TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE0LF_0LA1LC_0RA---".
Definition tm' := TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE1LF_0LA1LC_1RB---".
Definition tm0 := TM'_from_str "0RJ0LG_0RL0RS_1RJ0LX_1RL---_1LX0L]_0RS0L__1RA1L]_0RJ1L__0RQ0Lh_0RS0RJ_1RQ0Lo_1RS1RJ_0Lh0LU_0RJ0LW_1Lh1LU_0LG1LW_1LG0RA_0RJ0RC_1LX1RA_---1RC_0L^0RS_0L`0Lf_1L^0RJ_1L`1Lf_1RA0RJ_1L`---_1L]1RJ_1Lf---_0Lf0Lm_0Lh0Lo_1Lf1Lm_1Lh1Lo_0RS1Lh_0Lf0LG_1RS1Lo_0Lm0LX_0LE0LV_0LG0LX_1LE1LV_1LG1LX_0RA---_0RC---_1RA---_1RC---_0RS---_0Lf---_0RJ---_1Lf---".
Definition tm0' := TM'_from_str "0RJ0LG_0RL0RS_1RJ0LX_1RL---_1LX0L]_0RS0L__1RA1L]_0RJ1L__0RQ0Lh_0RS0RJ_1RQ0Lp_1RS1RJ_0Lh0LU_0RJ0LW_1Lh1LU_0LG1LW_1LG0RA_0RJ0RC_1LX1RA_---1RC_0L^0RS_0L`0Lf_1L^0RJ_1L`1Lf_1RA0RJ_1L`---_1L]1RJ_1Lf---_0Lf0Ln_0Lh0Lp_1Lf1Ln_1Lh1Lp_0RS1Lh_0Lf0LG_1RS1Lp_0Ln0LX_0LE0LV_0LG0LX_1LE1LV_1LG1LX_0RJ---_0RL---_1RJ---_1RL---_1LX---_0RS---_1RA---_0RJ---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RG_1LD1LI_1LE1LK_1LF1LC_1RG1LH_0RA0LF_0LI0LJ_0LF0LC_0RB---_0RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RG_1LD1LI_1LE1LK_1LF1LC_1RG1LH_0RA0LF_0LI0LJ_0LF0LC_0RB1RL_0RA1RL_1RL1RL".
Definition l0 := [1;0;0;1;0;0;0;0]%N.
Definition mp := mp_from_str "JSX`hGA]fmo".
Definition mp' := mp_from_str "JSX`hGA]fnp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM177.


Module TM178.
Definition tm := TM_from_str "1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LA---".
Definition tm' := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB1RF_0RB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1L]1RR_1RR---_1RC1RI_1RI---_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L_1Lf_1RJ0RR_1L_0RC_1Ri0RI_1RI0RA_1Lf0RC_1LW1RA_1L]1RC_0L^0RT_0L`0RK_1L^0RK_1L`---_0RK1RR_1L^0Lf_1RK0LW_0RK0L]_0Lf0L]_0Lh0L__1Lf1L]_1Lh1L__0RJ0Lh_0RL0RJ_1RJ0L__1RL1RJ_1L]0LU_1RR0LW_1RC1LU_1RI1LW_0RK---_------_1RK---_------_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0LH_0RL0RJ_1RJ0L__1RL1RJ_1L]0LU_1RR0LW_1Rc1LU_1RI1LW_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L_1LF_1RJ0RR_1L_0Rc_1Rj0RI_1RI0Ra_1LF0Rc_1LW1Ra_1L]1Rc_0L^0RT_0L`0RK_1L^0RK_1L`---_0RK1RR_1L^0LF_1RK0LW_0RK0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_1L]1RR_1RR---_1Rc1RI_1RI---_0RI---_0RK---_1RI---_1RK---_1LF---_0RR---_0Rc---_0RI---".
Definition tm1 := TM'_from_str "1RB1RL_0RC0RM_1LD1RA_0LE0LD_1RK0LF_1LG0RM_0LI0LH_1LE1LD_1RJ1LF_0RK0RJ_1LE0RA_0RM---_1RK1RJ".
Definition tm2 := TM'_from_str "1RB1RL_0RC0RM_1LD1RA_0LE0LD_1RK0LF_1LG0RM_0LI0LH_1LE1LD_1RJ1LF_0RK0RJ_1LE0RA_0RM1RN_1RK1RJ_1RN1RN".
Definition l0 := [1;0;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "CJT]fW^_hIRiK".
Definition mp' := mp_from_str "cJT]FW^_HIRjK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM178.


Module TM179.
Definition tm := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB1RF_0RB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB0RF_1LA---".
Definition tm0 := TM'_from_str "0RJ0LH_0RL0RJ_1RJ0L__1RL1RJ_1L]0LU_1RR0LW_1Rc1LU_1RI1LW_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L_1LF_1RJ0RR_1L_0Rc_1Rj0RI_1RI0Ra_1LF0Rc_1LW1Ra_1L]1Rc_0L^0RT_0L`0RK_1L^0RK_1L`---_0RK1RR_1L^0LF_1RK0LW_0RK0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_1L]1RR_1RR---_1Rc1RI_1RI---_0RI---_0RK---_1RI---_1RK---_1LF---_0RR---_0Rc---_0RI---".
Definition tm0' := TM'_from_str "0RJ0LH_0RL0RJ_1RJ0L__1RL1RJ_1L]0LU_1RR0LW_1Rc1LU_1RI1LW_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L_1LF_1RJ0RR_1L_0Rc_1Ri0RI_1RI0Ra_1LF0Rc_1LW1Ra_1L]1Rc_0L^0RT_0L`0RK_1L^0RK_1L`---_0RK1RR_1L^0LF_1RK0LW_0RK0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1L]1RR_1RR---_1Rc1RI_1RI---_0RK---_1L^---_1RK---_0RK---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1RB1RL_0RC0RM_1LD1RA_0LE0LD_1RK0LF_1LG0RM_0LI0LH_1LE1LD_1RJ1LF_0RK0RJ_1LE0RA_0RM---_1RK1RJ".
Definition tm2 := TM'_from_str "1RB1RL_0RC0RM_1LD1RA_0LE0LD_1RK0LF_1LG0RM_0LI0LH_1LE1LD_1RJ1LF_0RK0RJ_1LE0RA_0RM1RN_1RK1RJ_1RN1RN".
Definition l0 := [1;0;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "cJT]FW^_HIRjK".
Definition mp' := mp_from_str "cJT]FW^_HIRiK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM179.


Module TM180.
Definition tm := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1RD_0LD---".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC1RF_0LF---_0LB1LB".
Definition tm0 := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1L_0Ln_1RR0Lp_0R\1Ln_1RZ1Lp_1RR0Ra_0RR0Rc_0Lp1Ra_1RR1Rc_0LU1L__0LW0RR_1LU0R\_1LW0RZ_0Rc0RZ_1L_0R\_1Rc1RZ_---1R\_0LF1L__0LH0RR_1LF0R\_1LH0RZ_0LF1LF_0RR0RZ_1L_0R\_1RR1RZ_0LM0LN_0LO0LP_1LM1LN_1LO1LP_0RR0RZ_0RT0R\_1RR1RZ_1RT1R\_0Lp1L__1RR0RR_1Lp0R\_1RZ0RZ_0LU---_0LW---_1L_---_0RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1Lo0Lf_1RR0Lh_0R[1Lf_1Rj1Lh_1RR0RY_0RR0R[_0Lh1RY_1RR1R[_0LU1Lo_0LW0RR_1LU0R[_1LW0Rj_0R[0RY_1Lo0R[_1R[1RY_---1R[_0LF1Lo_0LH0RR_1LF0R[_1LH0Rj_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0Lh1Lo_1RR0RR_1Lh0R[_1Rj0Rj_0LU---_0LW---_1Lo---_0RR---_0Lm---_0Lo---_1Lm---_1Lo---_0LF1LF_0RR0Rj_1Lo0R[_1RR1Rj_0LM0LN_0LO0LP_1LM1LN_1LO1LP".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "ZR_MUFNW\p".
Definition mp' := mp_from_str "jRoMUFNW[h".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM180.


Module TM181.
Definition tm := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC1RF_0LF---_0LB1LB".
Definition tm' := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC0RE_0LD---".
Definition tm0 := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1Lo0Lf_1RR0Lh_0R[1Lf_1Rj1Lh_1RR0RY_0RR0R[_0Lh1RY_1RR1R[_0LU1Lo_0LW0RR_1LU0R[_1LW0Rj_0R[0RY_1Lo0R[_1R[1RY_---1R[_0LF1Lo_0LH0RR_1LF0R[_1LH0Rj_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0Lh1Lo_1RR0RR_1Lh0R[_1Rj0Rj_0LU---_0LW---_1Lo---_0RR---_0Lm---_0Lo---_1Lm---_1Lo---_0LF1LF_0RR0Rj_1Lo0R[_1RR1Rj_0LM0LN_0LO0LP_1LM1LN_1LO1LP".
Definition tm0' := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1L_0Ln_1RR0Lp_0R\1Ln_1Ra1Lp_1RR0Ra_0RR0Rc_0Lp1Ra_1RR1Rc_0LU1L__0LW0RR_1LU0R\_1LW0Ra_0Rc0RZ_1L_0R\_1Rc1RZ_---1R\_0LF1L__0LH0RR_1LF0R\_1LH0Ra_0LF1LF_0RR0Ra_1L_0R\_1RR1Ra_0LM0LN_0LO0LP_1LM1LN_1LO1LP_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0Lp1L__1RR0RR_1Lp0R\_1Ra0Ra_0LU---_0LW---_1L_---_0RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "jRoMUFNW[h".
Definition mp' := mp_from_str "aR_MUFNW\p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM181.


Module TM182.
Definition tm := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC0RE_0LD---".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC0RD_0LF---_0LB1LB".
Definition tm0 := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1L_0Ln_1RR0Lp_0R\1Ln_1Ra1Lp_1RR0Ra_0RR0Rc_0Lp1Ra_1RR1Rc_0LU1L__0LW0RR_1LU0R\_1LW0Ra_0Rc0RZ_1L_0R\_1Rc1RZ_---1R\_0LF1L__0LH0RR_1LF0R\_1LH0Ra_0LF1LF_0RR0Ra_1L_0R\_1RR1Ra_0LM0LN_0LO0LP_1LM1LN_1LO1LP_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0Lp1L__1RR0RR_1Lp0R\_1Ra0Ra_0LU---_0LW---_1L_---_0RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1Lo0Lf_1RR0Lh_0R[1Lf_1RY1Lh_1RR0RY_0RR0R[_0Lh1RY_1RR1R[_0LU1Lo_0LW0RR_1LU0R[_1LW0RY_0R[0RY_1Lo0R[_1R[1RY_---1R[_0LF1Lo_0LH0RR_1LF0R[_1LH0RY_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0Lh1Lo_1RR0RR_1Lh0R[_1RY0RY_0LU---_0LW---_1Lo---_0RR---_0Lm---_0Lo---_1Lm---_1Lo---_0LF1LF_0RR0RY_1Lo0R[_1RR1RY_0LM0LN_0LO0LP_1LM1LN_1LO1LP".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "aR_MUFNW\p".
Definition mp' := mp_from_str "YRoMUFNW[h".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM182.


Module TM183.
Definition tm := TM_from_str "1LB---_0LC0LE_1LD1LA_1RE0RD_1LB0RF_1RD0LE".
Definition tm' := TM_from_str "1LB0RE_0LC0LA_1LD1LF_1RA0RD_1RD0LF_1LB---".
Definition tm0 := TM'_from_str "1L^---_1LN---_1LF---_0R[---_0LN---_0LP---_1LN---_1LP---_1RZ0LW_0LP0RZ_0Rb0Lg_---1RZ_0LU0Le_0LW0Lg_1LU1Le_1LW1Lg_0Rk1LW_0RY---_1Rk1Lg_1RY---_0L^0LF_0L`0LH_1L^1LF_1L`1LH_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lg1LN_1RZ0Rb_1Lg0Rk_0Lg0RY_1L^0Ri_1LN0Rk_1LF1Ri_0R[1Rk_0LN0Rd_0LP0LN_1LN0R[_1LP1LN_0RZ0LW_0R\0RZ_1RZ0Lg_1R\1RZ_0R[0Le_1Rb0Lg_1Rk1Le_1RY1Lg".
Definition tm0' := TM'_from_str "1L^0Ra_1LN0Rc_1Ln1Ra_0R[1Rc_0LN0RD_0LP0LN_1LN0R[_1LP1LN_1RZ0LW_0LP0RZ_0RB0LG_---1RZ_0LU0LE_0LW0LG_1LU1LE_1LW1LG_0Rc1LW_0RY---_1Rc1LG_1RY---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0LG1LN_1RZ0RB_1LG0Rc_0LG0RY_0RZ0LW_0R\---_1RZ0LG_1R\---_0R[0Lm_1RB0Lo_1Rc1Lm_1RY1Lo_1L^---_1LN---_1Ln---_0R[---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1RB0LG_0RC0RD_0RD1RA_1RE1RL_1LF0RA_0LH0LG_1LF0RD_1LK1LI_0LJ---_1LH1LG_1RB0RE_0RE0RL".
Definition tm2 := TM'_from_str "1RB0LG_0RC0RD_0RD1RA_1RE1RL_1LF0RA_0LH0LG_1LF0RD_1LK1LI_0LJ1RM_1LH1LG_1RB0RE_0RE0RL_1RM1RM".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "kZd[bNgWFP^Y".
Definition mp' := mp_from_str "cZD[BNGWnP^Y".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM183.


Module TM184.
Definition tm := TM_from_str "1RB1RE_1LC1LB_1RD0LC_0RA---_0LF0RF_0RA1RA".
Definition tm' := TM_from_str "1RB0RF_1LC1LB_1RD0LC_0RE---_1RB1RA_0RE1RE".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LU_0LP1RA_1LW1LP_1LP1RB_------_1Rb1LX_---1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RZ0RC_0R\1RJ_1RZ1RC_1R\0LU_1RJ0LU_---0LW_1Rb1LU_---1LW_0RA---_0RC---_1RA---_1RC---_1Rb---_0RL---_1LX---_0Rk---_0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0Lm0RJ_0Lo0RL_1Lm0Rb_1Lo0Rd_0RA0RB_0RC0RD_1RA1RB_1RC1RD_1Rb1LU_0RL1RL_1LX1LP_0Rk1Rk".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW0RJ_0LP0RL_1LW0RB_1LP0RD_------_1RB1LX_---1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RZ0Rc_0R\1RJ_1RZ1Rc_1R\0LU_1RJ0LU_---0LW_1RB1LU_---1LW_0Ra---_0Rc---_1Ra---_1Rc---_1RB---_0RL---_1LX---_0Rk---_0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1Ra_1LW1LP_1LP1Rb_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_1RB1LU_0RL1RL_1LX1LP_0Rk1Rk".
Definition tm1 := TM'_from_str "0RB0RG_1LC1LK_1RD0LC_1RA1LE_---1LF_1RA1LC_1RJ1RH_0RB0RI_1RB1RG_0RD0RA_1LE1LK".
Definition tm2 := TM'_from_str "0RB0RG_1LC1LK_1RD0LC_1RA1LE_1RL1LF_1RA1LC_1RJ1RH_0RB0RI_1RB1RG_0RD0RA_1LE1LK_1RL1RL".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "bLUJXWkBdAP".
Definition mp' := mp_from_str "BLUJXWkbDaP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM184.


Module TM185.
Definition tm := TM_from_str "1RB0RF_1LC1LB_1RD0LC_0RE---_1RB1RA_0RE1RE".
Definition tm' := TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_1RB0RE".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW0RJ_0LP0RL_1LW0RB_1LP0RD_------_1RB1LX_---1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RZ0Rc_0R\1RJ_1RZ1Rc_1R\0LU_1RJ0LU_---0LW_1RB1LU_---1LW_0Ra---_0Rc---_1Ra---_1Rc---_1RB---_0RL---_1LX---_0Rk---_0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1Ra_1LW1LP_1LP1Rb_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_1RB1LU_0RL1RL_1LX1LP_0Rk1Rk".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1L]_0LP1RA_1L_1LP_1LP1RB_------_1Rj1LX_---1L__1L]1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_---0RC_---1RJ_---1RC_---0L]_---0L]_---0L__---1L]_---1L__0Rb0RC_0Rd1RJ_1Rb1RC_1Rd0L]_1RJ0L]_1RL0L__1Rj1L]_1Rl1L__0RA0RB_0RC0RD_1RA1RB_1RC1RD_1Rj1L]_0RL1RL_1LX1LP_0Rc1Rc_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L_0RJ_0LP0RL_1L_0Rj_1LP0Rl".
Definition tm1 := TM'_from_str "0RB0RG_1LC1LK_1RD0LC_1RA1LE_---1LF_1RA1LC_1RJ1RH_0RB0RI_1RB1RG_0RD0RA_1LE1LK".
Definition tm2 := TM'_from_str "0RB0RG_1LC1LK_1RD0LC_1RA1LE_1RL1LF_1RA1LC_1RJ1RH_0RB0RI_1RB1RG_0RD0RA_1LE1LK_1RL1RL".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "BLUJXWkbDaP".
Definition mp' := mp_from_str "jL]JX_cBlAP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM185.


Module TM186.
Definition tm := TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_1RB0RE".
Definition tm' := TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_0LE0RE".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1L]_0LP1RA_1L_1LP_1LP1RB_------_1Rj1LX_---1L__1L]1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_---0RC_---1RJ_---1RC_---0L]_---0L]_---0L__---1L]_---1L__0Rb0RC_0Rd1RJ_1Rb1RC_1Rd0L]_1RJ0L]_1RL0L__1Rj1L]_1Rl1L__0RA0RB_0RC0RD_1RA1RB_1RC1RD_1Rj1L]_0RL1RL_1LX1LP_0Rc1Rc_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L_0RJ_0LP0RL_1L_0Rj_1LP0Rl".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1L]_0LP1RA_1L_1LP_1LP1RB_------_1Rj1LX_---1L__1L]1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_---0RC_---1RJ_---1RC_---0L]_---0L]_---0L__---1L]_---1L__0Rb0RC_0Rd1RJ_1Rb1RC_1Rd0L]_1RJ0L]_1RL0L__1Rj1L]_1Rl1L__0RA0RB_0RC0RD_1RA1RB_1RC1RD_1Rj1L]_0RL1RL_1LX1LP_0Rc1Rc_0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0Le0RJ_0Lg0RL_1Le0Rj_1Lg0Rl".
Definition tm1 := TM'_from_str "0RB0RG_1LC1LK_1RD0LC_1RA1LE_---1LF_1RA1LC_1RJ1RH_0RB0RI_1RB1RG_0RD0RA_1LE1LK".
Definition tm2 := TM'_from_str "0RB0RG_1LC1LK_1RD0LC_1RA1LE_1RL1LF_1RA1LC_1RJ1RH_0RB0RI_1RB1RG_0RD0RA_1LE1LK_1RL1RL".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "jL]JX_cBlAP".
Definition mp' := mp_from_str "jL]JX_cBlAP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM186.


Module TM187.
Definition tm := TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1LC0RA".
Definition tm0 := TM'_from_str "0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_1R\0Lp_---0RL_1LX1Lp_---0R[_0RR---_0RT---_1RR---_1RT---_1Le---_0LX---_1RD---_1LX---_0RZ0RD_0R\1R[_1RZ1RD_1R\1LX_0Lg0LV_1RL0LX_1Lg1LV_1R[1LX_1LX0RB_1Ln0RD_0RB1RB_1Le1RD_0Lf1RT_0Lh0RB_1Lf---_1Lh1RB_1R[0LX_0RY0Ln_1LX1LX_1RY0Le_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1Le0RT_0LX1LX_1RD---_1LX0RB".
Definition tm0' := TM'_from_str "0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_1R\0Lp_---0RL_1LX1Lp_---0R[_0RR---_0RT---_1RR---_1RT---_1Le---_0LX---_1RD---_1LX---_0RZ0RD_0R\1R[_1RZ1RD_1R\1LX_0Lg0LV_1RL0LX_1Lg1LV_1R[1LX_1LX0RB_1Ln0RD_0RB1RB_1Le1RD_0Lf1RT_0Lh0RB_1Lf---_1Lh1RB_1R[0LX_0RY0Ln_1LX1LX_1RY0Le_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_0RD0RA_1R[0RC_1RD1RA_1LX1RC_0LV0RT_0LX1LX_1LV---_1LX0RB".
Definition tm1 := TM'_from_str "1RB1LE_1LC1RI_0LD0LC_0LE1LE_1RF1LE_0RG1RG_0RH0RF_1RA---_1RH1RF".
Definition tm2 := TM'_from_str "1RB1LE_1LC1RI_0LD0LC_0LE1LE_1RF1LE_0RG1RG_0RH0RF_1RA1RJ_1RH1RF_1RJ1RJ".
Definition l0 := [1;0;1;1;0;0;0;1]%N.
Definition mp := mp_from_str "T\enX[BLD".
Definition mp' := mp_from_str "T\enX[BLD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM187.


Module TM188.
Definition tm := TM_from_str "1LB0LD_0LC1LF_1RD---_0RE1RE_1LA1RD_1RD0RF".
Definition tm' := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA1RD_1RD0RF".
Definition tm0 := TM'_from_str "1RZ1LW_1R\1LP_---1Lp_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_1Lp---_1L_---_1RZ---_1R\---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1L_1R\_0LF1Lp_0LH1L__1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lp0Rc_1L_0RZ_1RZ0Rd_1R\0Ri".
Definition tm0' := TM'_from_str "1RZ1LW_1R\1LP_---1Lp_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_1Lp---_1LH---_1RZ---_1R\---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1LH1R\_0LF1Lp_0LH1LH_1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lp0Rc_1LH0RZ_1RZ0Rd_1R\0Ri".
Definition tm1 := TM'_from_str "1LB1RD_1RE0RC_0RD0RC_0RA0RF_1RA1RF_1LG1RE_1LH1LG_1LI1LB_1RD---".
Definition tm2 := TM'_from_str "1LB1RD_1RE0RC_0RD0RC_0RA0RF_1RA1RF_1LG1RE_1LH1LG_1LI1LB_1RD1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "cpiZ\d_PW".
Definition mp' := mp_from_str "cpiZ\dHPW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM188.


Module TM189.
Definition tm := TM_from_str "1LB1LA_0LC1LC_1RD0RF_0RE1RE_1LA1RD_---0RC".
Definition tm' := TM_from_str "1LB0LD_0LC1LC_1RD0RF_0RE1RE_1LA1RD_---0RC".
Definition tm0 := TM'_from_str "1RZ1LW_1R\1LP_---1LX_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0RQ_1Rc1Rd_---1RQ_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1LX---_1LH0RZ_1RZ---_1R\0Ri_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RZ_1LP0R\_1LX1RZ_1LH1R\_0LF1LX_0LH1LH_1LF1RZ_1LH1R\_---0RQ_---0RS_---1RQ_---1RS_---0Rc_------_---0Rd_---0RQ".
Definition tm0' := TM'_from_str "1RZ1LW_1R\1LP_---1LX_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0RQ_1Rc1Rd_---1RQ_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1LX---_1L_0RZ_1RZ---_1R\0Ri_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RZ_1LP0R\_1LX1RZ_1L_1R\_0LF1LX_0LH1L__1LF1RZ_1LH1R\_---0RQ_---0RS_---1RQ_---1RS_---0Rc_------_---0Rd_---0RQ".
Definition tm1 := TM'_from_str "1LB1RE_1RF0RC_---0RD_0RE0RC_0RA0RG_1RA1RG_1LH1RF_1LI1LH_1LJ1LB_1RE---".
Definition tm2 := TM'_from_str "1LB1RE_1RF0RC_1RK0RD_0RE0RC_0RA0RG_1RA1RG_1LH1RF_1LI1LH_1LJ1LB_1RE1RK_1RK1RK".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "cXiQZ\dHPW".
Definition mp' := mp_from_str "cXiQZ\d_PW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM189.


Module TM190.
Definition tm := TM_from_str "1LB0LD_0LC1LF_1RD---_0RE1RE_1LA0RB_1RD0RF".
Definition tm' := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA0RB_1RD0RF".
Definition tm0 := TM'_from_str "1RI1LW_1RK1LP_---1Lp_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_1Lp---_1L_---_1RI---_1RK---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RI_1LP0RK_1Lp1RI_1L_1RK_0LF1Lp_0LH1L__1LF1RI_1LH1RK_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lp0Rc_1L_0RZ_1RI0Rd_1RK0Ri".
Definition tm0' := TM'_from_str "1RI1LW_1RK1LP_---1Lp_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_1Lp---_1LH---_1RI---_1RK---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RI_1LP0RK_1Lp1RI_1LH1RK_0LF1Lp_0LH1LH_1LF1RI_1LH1RK_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lp0Rc_1LH0RZ_1RI0Rd_1RK0Ri".
Definition tm1 := TM'_from_str "1LB1RJ_1RE0RC_0RD0RC_0RA0RF_1RA1RF_1LG1RE_1LH1LG_1LI1LB_1RJ---_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RJ_1RE0RC_0RD0RC_0RA0RF_1RA1RF_1LG1RE_1LH1LG_1LI1LB_1RJ1RK_0RA0RF_1RK1RK".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "cpiZKd_PWI".
Definition mp' := mp_from_str "cpiZKdHPWI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM190.


Module TM191.
Definition tm := TM_from_str "1LB1LA_0LC1LC_1RD0RF_0RE1RE_1LA0RB_---0RC".
Definition tm' := TM_from_str "1LB0LD_0LC1LC_1RD0RF_0RE1RE_1LA0RB_---0RC".
Definition tm0 := TM'_from_str "1RI1LW_1RK1LP_---1LX_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0RQ_1Rc1Rd_---1RQ_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1LX---_1LH0RZ_1RI---_1RK0Ri_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RI_1LP0RK_1LX1RI_1LH1RK_0LF1LX_0LH1LH_1LF1RI_1LH1RK_---0RQ_---0RS_---1RQ_---1RS_---0Rc_------_---0Rd_---0RQ".
Definition tm0' := TM'_from_str "1RI1LW_1RK1LP_---1LX_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0RQ_1Rc1Rd_---1RQ_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1LX---_1L_0RZ_1RI---_1RK0Ri_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RI_1LP0RK_1LX1RI_1L_1RK_0LF1LX_0LH1L__1LF1RI_1LH1RK_---0RQ_---0RS_---1RQ_---1RS_---0Rc_------_---0Rd_---0RQ".
Definition tm1 := TM'_from_str "1LB1RK_1RF0RC_---0RD_0RE0RC_0RA0RG_1RA1RG_1LH1RF_1LI1LH_1LJ1LB_1RK---_0RA0RG".
Definition tm2 := TM'_from_str "1LB1RK_1RF0RC_1RL0RD_0RE0RC_0RA0RG_1RA1RG_1LH1RF_1LI1LH_1LJ1LB_1RK1RL_0RA0RG_1RL1RL".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "cXiQZKdHPWI".
Definition mp' := mp_from_str "cXiQZKd_PWI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM191.


Module TM192.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF0LE_0LD---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LF_1LA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl0LH_1Rj1LH_1Rl0Le_0LH0Le_---0Lg_1LH1Le_---1Lg_0RL---_1RK---_1RL---_1LH---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl---_1Rj1LH_1Rl---_0LH0Ln_---0Lp_1LH1Ln_---1Lp_0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\cj".
Definition mp' := mp_from_str "LUFHKZD\cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM192.


Module TM193.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LF_1LA---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl---_1Rj1LH_1Rl---_0LH0Ln_---0Lp_1LH1Ln_---1Lp_0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LH0LV_---0LX_1LH1LV_---1LX_0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\cj".
Definition mp' := mp_from_str "LUFHKZD\cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM193.


Module TM194.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LA---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0LD---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LH0LV_---0LX_1LH1LV_---1LX_0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LH0LV_---0LX_1LH1LV_---1LX_0RL---_1RK---_1RL---_1LH---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\cj".
Definition mp' := mp_from_str "LUFHKZD\cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM194.


Module TM195.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0LD---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0RB---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LH0LV_---0LX_1LH1LV_---1LX_0RL---_1RK---_1RL---_1LH---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_1LH0L]_---0L__1RZ1L]_---1L__0RI---_0RK---_1RI---_1RK---_0LH---_0RD---_1LH---_0RK---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\cj".
Definition mp' := mp_from_str "LUFHKZD\dl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM195.


Module TM196.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0RB---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LB---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_1LH0L]_---0L__1RZ1L]_---1L__0RI---_0RK---_1RI---_1RK---_0LH---_0RD---_1LH---_0RK---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_1LH0L]_---0L__1RZ1L]_---1L__1LH---_0RK---_1LW---_1RK---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\dl".
Definition mp' := mp_from_str "LUFHKZD\dl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM196.


Module TM197.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF0LE_1LC---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_1LH0L]_---0L__1RZ1L]_---1L__1LH---_0RK---_1LW---_1RK---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk0LH_1Ri1LH_1Rk0Le_0LH0Le_---0Lg_1LH1Le_---1Lg_1RK---_1LF---_1LH---_1LU---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\dl".
Definition mp' := mp_from_str "LUFHKZD\ci".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM197.


Module TM198.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF0LE_1LC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_1LC---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk0LH_1Ri1LH_1Rk0Le_0LH0Le_---0Lg_1LH1Le_---1Lg_1RK---_1LF---_1LH---_1LU---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk1LF_1Ri1LH_1Rk1LU_0LH0LV_---0LX_1LH1LV_---1LX_1RK---_1LF---_1LH---_1LU---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\ci".
Definition mp' := mp_from_str "LUFHKZD\ci".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM198.


Module TM199.
Definition tm := TM_from_str "1LB0LA_1RC0RD_1RD0RB_1RE0LE_1LA0RF_1LB---".
Definition tm' := TM_from_str "1LB0LA_1RC0RF_1RF0LD_1LA1RE_0RB---_1RD0LD".
Definition tm0 := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0RY_0RT0R[_1RR1RY_1RT1R[_1Rd1LN_1RR0LF_1RK0Rk_1RY1LF_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1LE0R\_1RR0Rb_1Rk0RK_1RY0LP_0Rb0LP_0Rd0RK_1Rb0LG_1Rd1RK_0LG0Le_1RK0Lg_1LG1Le_---1Lg_1RY0Ri_1LN0Rk_1LF1Ri_1LE1Rk_0LF1RR_0LH---_1LF1RY_1LH---_0RK---_0LP---_1RK---_0LG---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1R\1LN_1RR0LF_1RK0Rd_1Ri1LF_0Rj0LP_0Rl0RK_1Rj0LG_1Rl1RK_1LE0L]_1RR0L__1Rd1L]_1Ri1L__1Ri0Rb_1LN0Rd_1LF1Rb_1LE1Rd_0LF1RR_0LH---_1LF1Ri_1LH---_0RI---_0RK---_1RI---_1RK---_0Rl---_0RZ---_0RK---_0LP---_0RZ0LP_0R\0RK_1RZ0LG_1R\1RK_0LG0L]_1RK0L__1LG1L]_---1L_".
Definition tm1 := TM'_from_str "1RB1RI_1LC1RL_0LD0LC_1RH0LE_0LG0LF_1LD1LC_1RJ1LE_0RA0RI_1RH1RJ_0RK0LG_1LD0RL_1RI---".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RL_0LD0LC_1RH0LE_0LG0LF_1LD1LC_1RJ1LE_0RA0RI_1RH1RJ_0RK0LG_1LD0RL_1RI1RM_1RM1RM".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "\dENFGPRKYbk".
Definition mp' := mp_from_str "l\ENFGPRKiZd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM199.


Module TM200.
Definition tm := TM_from_str "1LB0LA_1RC0RF_1RF0LD_1LA1RE_0RB---_1RD0LD".
Definition tm' := TM_from_str "1LB0LA_1RC0RD_1RD0RB_1RE0LE_1LA1RF_0RB---".
Definition tm0 := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1R\1LN_1RR0LF_1RK0Rd_1Ri1LF_0Rj0LP_0Rl0RK_1Rj0LG_1Rl1RK_1LE0L]_1RR0L__1Rd1L]_1Ri1L__1Ri0Rb_1LN0Rd_1LF1Rb_1LE1Rd_0LF1RR_0LH---_1LF1Ri_1LH---_0RI---_0RK---_1RI---_1RK---_0Rl---_0RZ---_0RK---_0LP---_0RZ0LP_0R\0RK_1RZ0LG_1R\1RK_0LG0L]_1RK0L__1LG1L]_---1L_".
Definition tm0' := TM'_from_str "0RK1RR_0LP0LN_1RK0LF_0LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0RY_0RT0R[_1RR1RY_1RT1R[_1Rd1LN_1RR0LF_1RK0Rl_1RY1LF_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1LE0R\_1RR0Rb_1Rl0RK_1RY0LP_0Rb0LP_0Rd0RK_1Rb0LG_1Rd1RK_0LG0Le_1RK0Lg_1LG1Le_---1Lg_1RY0Rj_1LN0Rl_1LF1Rj_1LE1Rl_0LF1RR_0LH---_1LF1RY_1LH---_0RI---_0RK---_1RI---_1RK---_0R\---_0Rb---_0RK---_0LP---".
Definition tm1 := TM'_from_str "1RB1RI_1LC1RL_0LD0LC_1RH0LE_0LG0LF_1LD1LC_1RJ1LE_0RA0RI_1RH1RJ_0RK0LG_1LD0RL_1RI---".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RL_0LD0LC_1RH0LE_0LG0LF_1LD1LC_1RJ1LE_0RA0RI_1RH1RJ_0RK0LG_1LD0RL_1RI1RM_1RM1RM".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "l\ENFGPRKiZd".
Definition mp' := mp_from_str "\dENFGPRKYbl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM200.


Module TM201.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LE---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0LD---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_0L_0L]_---0L__1L_1L]_---1L__------_1R\---_------_1LH---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_0LH0L]_---0L__1LH1L]_---1L__0RL---_1RK---_1RL---_1LH---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\dl".
Definition mp' := mp_from_str "LUFHKZD\dl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM201.


Module TM202.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0LD---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_0RF0LD_1LC---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_0LH0L]_---0L__1LH1L]_---1L__0RL---_1RK---_1RL---_1LH---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rk0RD_1R\1LH_1LH0RK_0Ri0RL_0Rk1RK_1Ri1RL_1Rk1LH_0LH0L]_---0L__1LH1L]_---1L__1RK---_1LF---_1LH---_1LU---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\dl".
Definition mp' := mp_from_str "LUFHKZD\dk".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM202.


Module TM203.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_0RF0LD_1LC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_1LB---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rk0RD_1R\1LH_1LH0RK_0Ri0RL_0Rk1RK_1Ri1RL_1Rk1LH_0LH0L]_---0L__1LH1L]_---1L__1RK---_1LF---_1LH---_1LU---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk1LF_1Ri1LH_1Rk1LU_0LX0LV_---0LX_1LX1LV_---1LX_1LH---_0RK---_1LW---_1RK---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\dk".
Definition mp' := mp_from_str "LUFHKZD\ci".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM203.


Module TM204.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_1LB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LE---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk1LF_1Ri1LH_1Rk1LU_0LX0LV_---0LX_1LX1LV_---1LX_1LH---_0RK---_1LW---_1RK---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LX0LV_---0LX_1LX1LV_---1LX_------_1LH---_------_1LW---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\ci".
Definition mp' := mp_from_str "LUFHKZD\cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM204.


Module TM205.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LE---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LX0LV_---0LX_1LX1LV_---1LX_------_1LH---_------_1LW---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_0LH0L]_---0L__1LH1L]_---1L__0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\cj".
Definition mp' := mp_from_str "LUFHKZD\dl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM205.


Module TM206.
Definition tm := TM_from_str "1LB1LB_0LC0LA_1LD0LC_1RE0RD_1LB1RF_1RD---".
Definition tm' := TM_from_str "1LB1RE_0LC0LF_1LD0LC_1RA0RD_1RD---_1RF1LB".
Definition tm0 := TM'_from_str "1L^1L^_1LN1LN_1LU1LU_1LN1LN_0LN0LN_0LP0LP_1LN1LN_1LP1LP_1R\0LW_0L^0LW_0Rb0LG_0LU0LG_0LU0LE_0LW0LG_1LU1LE_1LW1LG_0Rl1R\_0RY0L^_1Rl0Rb_1RY0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0LG1LN_1R\0Rb_1LG0Rl_---0RY_1L^0Rj_1LN0Rl_1LU1Rj_1LN1Rl_0LN1Rd_0LP---_1LN1R[_1LP---_0RZ---_0R\---_1RZ---_1R\---_1LN---_1Rb---_1Rl---_1RY---".
Definition tm0' := TM'_from_str "1L^0Rb_1LN0Rd_1LU1Rb_1LN1Rd_0LN1RD_0LP---_1LN1R[_1LP---_1R\0Rl_0L^0LW_0RB1Rl_0LU0Lo_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0Rd1R\_0RY0L^_1Rd0RB_1RY0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0Lo1LN_1R\0RB_1Lo0Rd_---0RY_0RZ---_0R\---_1RZ---_1R\---_1LN---_1RB---_1Rd---_1RY---_0Rj1L^_0Rl1LN_1Rj1LU_1Rl1LN_1Rl0LN_0Lo0LP_1LN1LN_1Lo1LP".
Definition tm1 := TM'_from_str "1RB---_1RC1RJ_1LD1RA_0LF0LE_1LD1LD_1LH1LG_0LH0LG_1RB0RI_1LD0RA_1RI1RK_0RI0RK".
Definition tm2 := TM'_from_str "1RB1RL_1RC1RJ_1LD1RA_0LF0LE_1LD1LD_1LH1LG_0LH0LG_1RB0RI_1LD0RA_1RI1RK_0RI0RK_1RL1RL".
Definition l0 := [1;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "l\dNGWU^b[Y".
Definition mp' := mp_from_str "d\DNoWU^B[Y".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM206.


Module TM207.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1RA0LD_1LC0LE_0LF0RA_---1RC".
Definition tm' := TM_from_str "1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L_1RL_1RJ1RJ_1L_1Rd_1Rb1Rb_0Rd0RA_1LV0RC_1Rd1RA_1Le1RC_0LV1LV_0LX0RD_1LV0RC_1LX0RC_0RB1RD_0RD0Lm_1RB0L__1RD1LV_1Le0L]_1RD0L__1RC1L]_1RC1L__0Rd---_1LV0RJ_1Rd1RL_1Le1RJ_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_---0RA_0RD0RC_---1RA_1RD1RC_0Lm1LV_0Lo0RD_1Lm0RC_1Lo0RC_---0RR_---0RT_---1RR_---1RT_---1RL_---0Le_---1Rd_---1Le".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L_1RL_1RJ1RJ_1L_1Rd_1Rb1Rb_0Rd0RC_1LV0RC_1Rd1RC_1Le1RC_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0RB1RD_0RD0Lm_1RB0L__1RD1LV_1Le0L]_1RD0L__1RC1L]_1RC1L__0Rd---_1LV0RJ_1Rd1RL_1Le1RJ_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_---0RA_0RD0RC_---1RA_1RD1RC_0Lm1LV_0Lo0RD_1Lm0RC_1Lo0RC_---0RR_---0RT_---1RR_---1RT_---1RL_---0Le_---1Rd_---1Le".
Definition tm1 := TM'_from_str "1LB1RF_0LI1LC_1RD0LH_1RA1RE_1RD1RF_1RG1RJ_1LC0RF_1LC1LB_---1RA_0RD0RF".
Definition tm2 := TM'_from_str "1LB1RF_0LI1LC_1RD0LH_1RA1RE_1RD1RF_1RG1RJ_1LC0RF_1LC1LB_1RK1RA_0RD0RF_1RK1RK".
Definition l0 := [1;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "LeVDdCJ_mb".
Definition mp' := mp_from_str "LeVDdCJ_mb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM207.


Module TM208.
Definition tm := TM_from_str "1LB0RD_0LC0LF_0LD0LA_1RE0LD_1RF---_0RA1RA".
Definition tm' := TM_from_str "1LB0RD_0LC1LB_0LD0LA_1RE0LD_1RF---_0RA1RA".
Definition tm0 := TM'_from_str "1L]0RY_1LW0R[_1LE1RY_1Lo1R[_0LN0Rl_0LP1RC_1LN---_1LP1RD_1RC1L]_0LN1LW_0L]1LE_0Rl1Lo_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0Rl0LW_1RC0Rb_1Rl0Lo_0L]1Rb_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Rb0Rl_0Rd1RC_1Rb1Rl_1Rd0L]_1RC0L]_---0L__1RD1L]_---1L__0Rj---_0Rl---_1Rj---_1Rl---_1LE---_1Lo---_1RY---_1R[---_0RA0RB_0RC0RD_1RA1RB_1RC1RD_0LW0Lo_0Rb1Rb_1LW1Lo_0Rl1Rl".
Definition tm0' := TM'_from_str "1L]0RY_1LW0R[_1LE1RY_1LP1R[_0LN0Rl_0LP1RC_1LN---_1LP1RD_1RC1L]_0LN1LW_0L]1LE_0Rl1LP_0LU0LN_0LW0LP_1LU1LN_1LW1LP_0Rl0LW_1RC0Rb_1Rl0LP_0L]1Rb_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Rb0Rl_0Rd1RC_1Rb1Rl_1Rd0L]_1RC0L]_---0L__1RD1L]_---1L__0Rj---_0Rl---_1Rj---_1Rl---_1LE---_1LP---_1RY---_1R[---_0RA0RB_0RC0RD_1RA1RB_1RC1RD_0LW0LP_0Rb1Rb_1LW1LP_0Rl1Rl".
Definition tm1 := TM'_from_str "0RB---_1RC1RE_1LD1RJ_0LK0RB_1LF1RI_1LG1LF_1LH1LD_1RC0LH_1RA1RB_0RA0RB_0LG0LF".
Definition tm2 := TM'_from_str "0RB1RL_1RC1RE_1LD1RJ_0LK0RB_1LF1RI_1LG1LF_1LH1LD_1RC0LH_1RA1RB_0RA0RB_0LG0LF_1RL1RL".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "blCEDoW][YN".
Definition mp' := mp_from_str "blCEDPW][YN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM208.


Module TM209.
Definition tm := TM_from_str "1LB1LA_1RC0LB_1LD0RD_1RE0RA_0RF0LE_1RB---".
Definition tm' := TM_from_str "1LB1LA_1RC0LB_1LD0RD_1RE0RA_0RF1RC_1RB---".
Definition tm0 := TM'_from_str "0R[1RA_1LP1LP_1R[1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RR1RA_0RT0LP_1RR1LO_1RT0LM_0LP0LM_1Rb0LO_1LP1LM_1RA1LO_0RT0RY_1RA0R[_0Le1RY_1LO1R[_0L^0Rk_0L`0R[_1L^0RT_1L`1RA_0Rb0RA_0Rd0RC_1Rb1RA_1Rd1RC_1RJ1Rb_0Le0LP_---1RA_1Le1LP_0Ri0RJ_0Rk0RT_1Ri1RJ_1Rk0Le_0RT0Le_---0Lg_0LP1Le_---1Lg_0RJ---_0RL---_1RJ---_1RL---_1LO---_0LM---_1R[---_1LM---".
Definition tm0' := TM'_from_str "0R[1RA_1LP1LP_1R[1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RR1RA_0RT0LP_1RR1LO_1RT0LM_0LP0LM_1Rb0LO_1LP1LM_1RA1LO_0RT0RY_1RA0R[_1RT1RY_1LO1R[_0L^0Rk_0L`0R[_1L^0RT_1L`1RA_0Rb0RA_0Rd0RC_1Rb1RA_1Rd1RC_1RJ1Rb_1LO0LP_---1RA_1R[1LP_0Ri0RR_0Rk0RT_1Ri1RR_1Rk1RT_0RT0LP_---1Rb_0LP1LP_---1RA_0RJ---_0RL---_1RJ---_1RL---_1LO---_0LM---_1R[---_1LM---".
Definition tm1 := TM'_from_str "1RB1RI_0RC0RE_1RD---_0RE0LG_1LF1RA_1LG1LH_1RI1LF_0LG0LH_0RA1RI".
Definition tm2 := TM'_from_str "1RB1RI_0RC0RE_1RD1RJ_0RE0LG_1LF1RA_1LG1LH_1RI1LF_0LG0LH_0RA1RI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "[bkJTOPMA".
Definition mp' := mp_from_str "[bkJTOPMA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM209.


Module TM210.
Definition tm := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_1LD0RC_---0LA".
Definition tm' := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_0RC0RC_---0LA".
Definition tm0 := TM'_from_str "0R\1Rd_1RL1LP_1R\1LN_0LN1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LH---_1RL0LN_1LH---_1Rd1LN_1Rd0RZ_1LP0R\_1LN1RZ_1LH1R\_0LF1RT_0LH1RS_1LF1Rk_1LH1RS_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1LH1LN_---1LN_1R\1RZ_0LN1RZ_0Rk0RQ_0RS0RS_1Rk1RQ_1RS1RS_0L^0LP_0L`0RL_1L^1LP_1L`0Rd_---1RL_---0LP_---0LN_---0LH_---0LE_---0LG_---1LE_---1LG".
Definition tm0' := TM'_from_str "0R\1Rd_1RL1LP_1R\1LN_0LN1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LH---_1RL0LN_1LH---_1Rd1LN_1Rd0RZ_1LP0R\_1LN1RZ_1LH1R\_0LF1RT_0LH1RS_1LF1Rk_1LH1RS_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1LH1LN_---1LN_1R\1RZ_0LN1RZ_0RQ0RQ_0RS0RS_1RQ1RQ_1RS1RS_0LP0LP_0RL0RL_1LP1LP_0Rd0Rd_---1RL_---0LP_---0LN_---0LH_---0LE_---0LG_---1LE_---1LG".
Definition tm1 := TM'_from_str "1LB1RI_1LC1LB_1RD1LG_1RE1RE_1LG1RF_0RH0RD_1RH0LG_1RA1RJ_1RH1RD_---0LG".
Definition tm2 := TM'_from_str "1LB1RI_1LC1LB_1RD1LG_1RE1RE_1LG1RF_0RH0RD_1RH0LG_1RA1RJ_1RH1RD_1RK0LG_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "THPdSZNL\k".
Definition mp' := mp_from_str "THPdSZNL\k".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM210.


Module TM211.
Definition tm := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_0RC0RC_---0LA".
Definition tm' := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_0RC0LD_---0LA".
Definition tm0 := TM'_from_str "0R\1Rd_1RL1LP_1R\1LN_0LN1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LH---_1RL0LN_1LH---_1Rd1LN_1Rd0RZ_1LP0R\_1LN1RZ_1LH1R\_0LF1RT_0LH1RS_1LF1Rk_1LH1RS_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1LH1LN_---1LN_1R\1RZ_0LN1RZ_0RQ0RQ_0RS0RS_1RQ1RQ_1RS1RS_0LP0LP_0RL0RL_1LP1LP_0Rd0Rd_---1RL_---0LP_---0LN_---0LH_---0LE_---0LG_---1LE_---1LG".
Definition tm0' := TM'_from_str "0R\1Rd_1RL1LP_1R\1LN_0LN1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LH---_1RL0LN_1LH---_1Rd1LN_1Rd0RZ_1LP0R\_1LN1RZ_1LH1R\_0LF1RT_0LH1RS_1LF1Rk_1LH1RS_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1LH1LN_---1LN_1R\1RZ_0LN1RZ_0RQ0RT_0RS0RS_1RQ1RT_1RS1RS_0LP0L]_0RL0L__1LP1L]_0Rd1L__---1RL_---0LP_---0LN_---0LH_---0LE_---0LG_---1LE_---1LG".
Definition tm1 := TM'_from_str "1LB1RI_1LC1LB_1RD1LG_1RE1RE_1LG1RF_0RH0RD_1RH0LG_1RA1RJ_1RH1RD_---0LG".
Definition tm2 := TM'_from_str "1LB1RI_1LC1LB_1RD1LG_1RE1RE_1LG1RF_0RH0RD_1RH0LG_1RA1RJ_1RH1RD_1RK0LG_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "THPdSZNL\k".
Definition mp' := mp_from_str "THPdSZNL\k".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM211.


Module TM212.
Definition tm := TM_from_str "1LB1RC_0LC0LE_0RD0RF_1RA0RB_1LB0LE_1RD---".
Definition tm' := TM_from_str "1LB0LA_0LC0LA_0RD0RF_1RE0RB_1LA1RC_1RD---".
Definition tm0 := TM'_from_str "0RT0RR_1LN0RT_0RK1RR_1Le1RT_0LN1RB_0LP1RZ_1LN1RI_1LP---_0RB0LW_0RZ0LN_1RB0Lg_1RZ0Le_0LU0Le_0LW0Lg_1LU1Le_1LW1Lg_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_1LN0RD_0RB---_0RT0RK_0LW---_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0Lg1LN_1R[0LN_1Lg0RT_1Rk1LN_0RT0LW_1LN0LN_0RK0Lg_1Le0Le_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RZ---_0R\---_1RZ---_1R\---_1Le---_1RB---_1RT---_0Lg---".
Definition tm0' := TM'_from_str "0RT0LW_1LN0LN_0RK0LG_1LE0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0Rb0LW_0RZ0LN_1Rb0LG_1RZ0LE_0LU0LE_0LW0LG_1LU1LE_1LW1LG_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_1LN0Rd_0Rb---_0RT0RK_0LW---_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_0LG1LN_1R[0LN_1LG0RT_1Rk1LN_1LW0RR_1LN0RT_1LG1RR_1LE1RT_0LF1Rb_0LH1RZ_1LF1RI_1LH---_0RZ---_0R\---_1RZ---_1R\---_1LE---_1Rb---_1RT---_0LG---".
Definition tm1 := TM'_from_str "1RB1RJ_1RC1RH_1LD0RA_0LG0LE_1LD1LF_0LD0LF_0RA0RI_0RC0LG_1RC0LE_1RK---_0RL0RI_1LF1RA".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RH_1LD0RA_0LG0LE_1LD1LF_0LD0LF_0RA0RI_0RC0LG_1RC0LE_1RK1RM_0RL0RI_1LF1RA_1RM1RM".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "T[BNgeWIKkZD".
Definition mp' := mp_from_str "T[bNGEWIKkZd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM212.


Module TM213.
Definition tm := TM_from_str "1RB1RC_1LA---_0RE1LD_1RF0LC_1RA1RF_1RE0LF".
Definition tm' := TM_from_str "1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0LW1RB_---0LW_1LW1Rj_---1LW_------_0RT---_------_1L^---_0LF---_0LH---_1LF---_1LH---_0Ra1RL_0Rc0RT_1Ra0Lm_1Rc1L^_0RL0L^_0Rd0L`_0RT1L^_1RL1L`_0Rj0RB_0Rl0Lm_1Rj1RB_1Rl0LW_1RD0LU_0Lm0LW_1Rl1LU_1Lm1LW_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1L^1RD_1Rc0Lm_---1Rl_1L^1Lm_0Rb0RD_0Rd1RL_1Rb1RD_1Rd0Lm_1RL0Lm_1Rd0Lo_1RT1Lm_0Lm1Lo".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_1RB_---0L__1L_1Rj_---1L__1RL---_0R\---_0Lm---_1LV---_0LV---_0LX---_1LV---_1LX---_0Rj0RB_0Rl0Lm_1Rj1RB_1Rl0L__1RD0L]_0Lm0L__1Rl1L]_1Lm1L__0Ra1RL_0Rc0R\_1Ra0Lm_1Rc1LV_0RL0LV_0Rd0LX_0R\1LV_1RL1LX_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LV1RD_1Rc0Lm_---1Rl_1LV1Lm_0Rb0RD_0Rd1RL_1Rb1RD_1Rd0Lm_1RL0Lm_1Rd0Lo_1R\1Lm_0Lm1Lo".
Definition tm1 := TM'_from_str "0RB0RF_1LC---_0LD0LE_1RB0LD_0RF1LC_1RG1LC_1RA1RH_0RI1RB_1RK1RJ_1RI0LD_1RB1RF".
Definition tm2 := TM'_from_str "0RB0RF_1LC1RL_0LD0LE_1RB0LD_0RF1LC_1RG1LC_1RA1RH_0RI1RB_1RK1RJ_1RI0LD_1RB1RF_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "BL^mWTcjdlD".
Definition mp' := mp_from_str "BLVm_\cjdlD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM213.


Module TM214.
Definition tm := TM_from_str "1LB0RC_0LC0LF_1LD0LE_1RE0LA_0RA0RE_0RC---".
Definition tm' := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_1RE---".
Definition tm0 := TM'_from_str "1L^0RQ_1Ra0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0Rc_0LW---_0LG1Rc_1L^---_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lo_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RQ---_0RS---_1RQ---_1RS---_1RA---_0LW---_1Ra---_1LW---".
Definition tm0' := TM'_from_str "1L^0RQ_1Ra0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0Rc_0LW---_0LG1Rc_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0Rb---_0Rd---_1Rb---_1Rd---_1Le---_1RA---_1RQ---_1Ra---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1RA1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWeo".
Definition mp' := mp_from_str "aA^QcGNWep".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM214.


Module TM215.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_1RE---".
Definition tm' := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_1RD---".
Definition tm0 := TM'_from_str "1L^0RQ_1Ra0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0Rc_0LW---_0LG1Rc_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0Rb---_0Rd---_1Rb---_1Rd---_1Le---_1RA---_1RQ---_1Ra---".
Definition tm0' := TM'_from_str "1L^0RQ_1Ra0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0Rc_0LW---_0LG1Rc_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RZ---_0R\---_1RZ---_1R\---_1RC---_1RA---_1Rc---_1Ra---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1RA1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWep".
Definition mp' := mp_from_str "aA^QcGNWep".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM215.


Module TM216.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_1RD---".
Definition tm' := TM_from_str "1LB0RC_0LC1LE_1LD0LF_0RB0LA_1RF---_0RA0RF".
Definition tm0 := TM'_from_str "1L^0RQ_1Ra0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0Rc_0LW---_0LG1Rc_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RZ---_0R\---_1RZ---_1R\---_1RC---_1RA---_1Rc---_1Ra---".
Definition tm0' := TM'_from_str "1L^0RQ_1Ri0RS_1Lm1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ri_1LP1LW_1RA0Rk_0LW---_0LG1Rk_1L^---_0LU0Lf_0LW0Lh_1LU1Lf_1LW1Lh_0Rk1L^_1LN0RA_1Rk1Lm_1Ri1RA_0L^0Lm_0L`0Lo_1L^1Lm_1L`1Lo_0RI0LW_0RK0Rk_1RI0Lh_1RK1Rk_0L^0LE_1RA0LG_1L^1LE_1Ri1LG_0Rj---_0Rl---_1Rj---_1Rl---_1Lm---_1RA---_1RQ---_1Ri---_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LW1L^_0Rk0RA_1LW0RQ_1L^0Ri".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1RA1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWep".
Definition mp' := mp_from_str "iA^QkGNWmh".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM216.


Module TM217.
Definition tm := TM_from_str "1LB0RC_0LC0LF_1LD0LE_1RE0LA_0RA0RE_1LD---".
Definition tm' := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_0RA---".
Definition tm0 := TM'_from_str "1L^0RQ_1L^0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA1RA_0LW---_0LG0LG_1L^---_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lo_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0Rc---_1LN---_1Rc---_1Ra---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "1L^0RQ_1L^0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0RQ_0LW---_0LG1RQ_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RA---_0RC---_1RA---_1RC---_0LW---_0Rc---_1LW---_1L^---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LC1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWeo".
Definition mp' := mp_from_str "aA^QcGNWep".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM217.


Module TM218.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_0RA---".
Definition tm' := TM_from_str "1LB0RC_0LC0LF_1LD0LE_1RE0LA_0RA0RE_0RB---".
Definition tm0 := TM'_from_str "1L^0RQ_1L^0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0RQ_0LW---_0LG1RQ_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RA---_0RC---_1RA---_1RC---_0LW---_0Rc---_1LW---_1L^---".
Definition tm0' := TM'_from_str "1L^0RQ_1L^0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA1RA_0LW---_0LG0LG_1L^---_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lo_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RI---_0RK---_1RI---_1RK---_0L^---_0L^---_1L^---_1L^---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LC1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWep".
Definition mp' := mp_from_str "aA^QcGNWeo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM218.


Module TM219.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_1RC---".
Definition tm' := TM_from_str "1LB0RC_0LC0LF_1LD0LE_1RE0LA_0RA0RE_0RE---".
Definition tm0 := TM'_from_str "1L^0RQ_0RQ0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0RA_0LW---_0LG1RA_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RR---_0RT---_1RR---_1RT---_0LG---_1L^---_1LG---_0RQ---".
Definition tm0' := TM'_from_str "1L^0RQ_0RQ0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA0RA_0LW---_0LG1RA_1L^---_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lo_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0Ra---_0Rc---_1Ra---_1Rc---_1L^---_0RA---_0RQ---_0Ra---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_0RD---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_0RD1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWep".
Definition mp' := mp_from_str "aA^QcGNWeo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM219.


Module TM220.
Definition tm := TM_from_str "1LB0RC_0LC0LF_1LD0LE_1RE0LA_0RA0RE_0RA---".
Definition tm' := TM_from_str "1LB0RD_0RB1LC_0LD---_1LE0LF_1RF0LA_0RA0RF".
Definition tm0 := TM'_from_str "1L^0RQ_1LW0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA1L^_0LW---_0LG1Le_1L^---_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lo_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RA---_0RC---_1RA---_1RC---_0LW---_0Rc---_1LW---_1L^---".
Definition tm0' := TM'_from_str "1Lf0RY_1L_0R[_1Lm1RY_---1R[_0LN1RA_0LP0L__1LN1Ri_1LP1L__0RI1Lf_0RK---_1RI1Lm_1RK---_0RI0LV_0L_0LX_1Lf1LV_1L_1LX_1RA---_0L_---_0LG---_1Lf---_0L]---_0L_---_1L]---_1L_---_0Rk1Lf_1LN0RA_1Rk1Lm_1Ri1RA_0Lf0Lm_0Lh0Lo_1Lf1Lm_1Lh1Lo_0Rj0L__0Rl0Rk_1Rj0LX_1Rl1Rk_1Lm0LE_1RA0LG_1RY1LE_1Ri1LG_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0L_1Lf_0Rk0RA_1L_0RY_1Lf0Ri".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LH---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LH1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWeo".
Definition mp' := mp_from_str "iAfYkGN_mX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM220.


Module TM221.
Definition tm := TM_from_str "1LB0RD_0RB1LC_0LD---_1LE0LF_1RF0LA_0RA0RF".
Definition tm' := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_0RC---".
Definition tm0 := TM'_from_str "1Lf0RY_1L_0R[_1Lm1RY_---1R[_0LN1RA_0LP0L__1LN1Ri_1LP1L__0RI1Lf_0RK---_1RI1Lm_1RK---_0RI0LV_0L_0LX_1Lf1LV_1L_1LX_1RA---_0L_---_0LG---_1Lf---_0L]---_0L_---_1L]---_1L_---_0Rk1Lf_1LN0RA_1Rk1Lm_1Ri1RA_0Lf0Lm_0Lh0Lo_1Lf1Lm_1Lh1Lo_0Rj0L__0Rl0Rk_1Rj0LX_1Rl1Rk_1Lm0LE_1RA0LG_1RY1LE_1Ri1LG_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0L_1Lf_0Rk0RA_1L_0RY_1Lf0Ri".
Definition tm0' := TM'_from_str "1L^0RQ_1LW0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA1L^_0LW---_0LG1Le_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RQ---_0RS---_1RQ---_1RS---_1RA---_0LW---_1Ra---_1LW---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LH---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LH1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "iAfYkGN_mX".
Definition mp' := mp_from_str "aA^QcGNWep".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM221.


Module TM222.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_0RC---".
Definition tm' := TM_from_str "1LB0RC_0LC1LF_1LD0LE_1RE0LA_0RA0RE_0LC---".
Definition tm0 := TM'_from_str "1L^0RQ_1LW0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA1L^_0LW---_0LG1Le_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_0RQ---_0RS---_1RQ---_1RS---_1RA---_0LW---_1Ra---_1LW---".
Definition tm0' := TM'_from_str "1L^0RQ_1LW0RS_1Le1RQ_---1RS_0LN1RA_0LP0LW_1LN1Ra_1LP1LW_1RA1L^_0LW---_0LG1Le_1L^---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Rc1L^_1LN0RA_1Rc1Le_1Ra1RA_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0Rb0LW_0Rd0Rc_1Rb0Lp_1Rd1Rc_1Le0LE_1RA0LG_1RQ1LE_1Ra1LG_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1L^_0Rc0RA_1LW0RQ_1L^0Ra_1RA---_0LW---_0LG---_1L^---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LH---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RD_1RB0LF_0RE1LC_1RB1RA_1LG1RA_0LH0LJ_1LC1LI_0LH1LC_1LH1RK_1RK1RK".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "aA^QcGNWep".
Definition mp' := mp_from_str "aA^QcGNWep".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM222.


Module TM223.
Definition tm := TM_from_str "1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0LC---".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---".
Definition tm0 := TM'_from_str "0RJ0Rc_0RL1RA_1RJ1Rc_1RL1LH_0LN0LF_1RR0LH_1LN1LF_1RA1LH_1RJ0Ra_0LW0Rc_0Lp1Ra_0RJ1Rc_0LU1LW_0LW0RJ_1LU0RA_1LW0Rc_0RC1L^_1LW0RA_1RC1LN_---1RA_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0Rb1L^_0Rd---_1Rb1LN_1Rd---_---0Ln_1RJ0Lp_1RA1Ln_1Rc1Lp_0RR0RA_0RT0RC_1RR1RA_1RT1RC_0Lp0LW_0RJ1RR_1Lp0Rc_0Rc1RA_1RJ---_0LW---_0Lp---_0RJ---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ0Rc_0RL1RA_1RJ1Rc_1RL1LH_0LN0LF_1RR0LH_1LN1LF_1RA1LH_1RJ0Ra_0LW0Rc_0Lp1Ra_0RJ1Rc_0LU1LW_0LW0RJ_1LU0RA_1LW0Rc_0RC1L^_1LW0RA_1RC1LN_---1RA_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0Rb1L^_0Rd---_1Rb1LN_1Rd---_---0Ln_1RJ0Lp_1RA1Ln_1Rc1Lp_0RR0RA_0RT0RC_1RR1RA_1RT1RC_0Lp0LW_0RJ1RR_1Lp0Rc_0Rc1RA_0RQ---_0RS---_1RQ---_1RS---_1RJ---_0LW---_1Rc---_1LW---".
Definition tm1 := TM'_from_str "0LB0RE_1LC1LH_1RA0LD_1LB---_1RG1RF_0RA0RE_1LB0RF_0LB0RA".
Definition tm2 := TM'_from_str "0LB0RE_1LC1LH_1RA0LD_1LB1RI_1RG1RF_0RA0RE_1LB0RF_0LB0RA_1RI1RI".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "JW^pcARN".
Definition mp' := mp_from_str "JW^pcARN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM223.


Module TM224.
Definition tm := TM_from_str "1RB1RC_0LC1LF_0RF1RD_0LE---_1RA0LC_1LD0RA".
Definition tm' := TM_from_str "1RB1RD_0LC1LE_1RA0LD_0RE1RF_1LB0RA_0LC---".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0LU1LU_0Rk0LU_1LU1RA_0R\---_1RR1Lg_0Lg0RR_1LU---_0LU1RR_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0Ri0RZ_0Rk0R\_1Ri1RZ_1Rk1R\_0Lg0LU_0RJ---_1Lg1LU_0RR---_0RL---_0Lg---_1RL---_0LU---_0Le---_0Lg---_1Le---_1Lg---_0RB1RR_0RD0Lg_1RB1LU_1RD0LU_0LU0LU_1Rk0LW_1RR1LU_1R\1LW_1RR0RA_---0RC_1LU1RA_---1RC_0L^0Lg_0L`0Rk_1L^0RR_1L`0R\".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L]1L]_0Rc0L]_1L]1RA_0Rl---_0RL1LW_0LW0RZ_1RL1Lh_0L]1RZ_0LU0Lf_0LW0Lh_1LU1Lf_1LW1Lh_0RB1RZ_0RD0LW_1RB1L]_1RD0L]_0L]0L]_1Rc0L__1RZ1L]_1Rl1L__0Ra0Rj_0Rc0Rl_1Ra1Rj_1Rc1Rl_0LW0L]_0RJ---_1LW1L]_0RZ---_1RZ0RA_1LP0RC_1L]1RA_0Rl1RC_0LN0LW_0LP0Rc_1LN0RZ_1LP0Rl_0RL---_0LW---_1RL---_0L]---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0RC_0LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0RC_0LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JgRkUA\".
Definition mp' := mp_from_str "JWZc]Al".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM224.


Module TM225.
Definition tm := TM_from_str "1RB0RA_0RC0RF_1RD1LD_1LE---_1LF1LE_1RA0LE".
Definition tm' := TM_from_str "1RB0RA_0RC0RF_1RD0LC_1LE---_1LF1LE_1RA0LE".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1RZ0RS_1RB0RJ_1Lh0Rk_0Lg0RA_0RQ0Ri_0RS0Rk_1RQ1Ri_1RS1Rk_1Lp0RL_0Lh0Ln_---0RC_1Lh1Ln_0RZ1Lp_0R\---_1RZ1Lh_1R\---_0Lh0L^_---0L`_1Lh1L^_---1L`_1RA---_1Lp---_1Lg---_1Lh---_0Lf---_0Lh---_1Lf---_1Lh---_0RC1RA_1Ln1Lp_1RC1Lg_1Lf1Lh_0Ln0Lf_0Lp0Lh_1Ln1Lf_1Lp1Lh_0RB1RJ_0RD0Lp_1RB0Lg_1RD0Lh_1RS0Le_1RJ0Lg_1Rk1Le_1RA1Lg".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1RZ0RS_1RB0RJ_1Lh0Rk_0Lg0RA_0RQ0Ri_0RS0Rk_1RQ1Ri_1RS1Rk_1Lp0RL_0Lh0Ln_---0RC_1Lh1Ln_0RZ1Lp_0R\0Lh_1RZ1Lh_1R\0LU_0Lh0LU_---0LW_1Lh1LU_---1LW_1RA---_1Lp---_1Lg---_1Lh---_0Lf---_0Lh---_1Lf---_1Lh---_0RC1RA_1Ln1Lp_1RC1Lg_1Lf1Lh_0Ln0Lf_0Lp0Lh_1Ln1Lf_1Lp1Lh_0RB1RJ_0RD0Lp_1RB0Lg_1RD0Lh_1RS0Le_1RJ0Lg_1Rk1Le_1RA1Lg".
Definition tm1 := TM'_from_str "1RB1RI_1RC1LM_1LD---_1RL1LE_1LG1LF_0LD0LM_1RH0LE_0RB0RI_1RJ0LE_0RA0RK_1RH1RL_0RH0RL_1LD1LM".
Definition tm2 := TM'_from_str "1RB1RI_1RC1LM_1LD1RN_1RL1LE_1LG1LF_0LD0LM_1RH0LE_0RB0RI_1RJ0LE_0RA0RK_1RH1RL_0RH0RL_1LD1LM_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "LSZpgfnJkBCAh".
Definition mp' := mp_from_str "LSZpgfnJkBCAh".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM225.


Module TM226.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LD---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LB_0LB1RF_0LF0RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0LV---_0L_---_1RJ---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rj1RJ_0Rl0LV_1Rj0L__1Rl1RJ_1LV0L]_1RJ0L__0R[1L]_---1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0RC1LO_1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAi".
Definition mp' := mp_from_str "JV[a_MjC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM226.


Module TM227.
Definition tm := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LB_0LB1RF_0LF0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rj1RJ_0Rl0LV_1Rj0L__1Rl1RJ_1LV0L]_1RJ0L__0R[1L]_---1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0RC1LO_1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0Ra---_0L_---_1Ra---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MjC".
Definition mp' := mp_from_str "JV[a_MAi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM227.


Module TM228.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LB---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0Ra---_0L_---_1Ra---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1Rj---_1RJ---_1L_---_0L_---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAi".
Definition mp' := mp_from_str "JV[a_MAj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM228.


Module TM229.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LB_0LB1RF_0LF0RA".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1Rj---_1RJ---_1L_---_0L_---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rl0RY_1LV0R[_1Rl1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0Rj1L]_1RC1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0RC1LO_1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAj".
Definition mp' := mp_from_str "JV[a_MjC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM229.


Module TM230.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LE---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0LM_1Ra---_1L_1LM_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_1RJ---_0LV---_0L_---_1RJ---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LM_1Ra---_1L_1LM_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0LV---_0RJ---_1RJ---_1RJ---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAj".
Definition mp' := mp_from_str "JV[a_MAi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM230.


Module TM231.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LC---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LM_1Ra---_1L_1LM_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0LV---_0RJ---_1RJ---_1RJ---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L]_1Ra---_1L_1L]_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0Ra---_0LV---_1Ra---_0LM---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAi".
Definition mp' := mp_from_str "JV[a_MAj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM231.


Module TM232.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LA---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_0RC---_1LV---_1RC---_1LM---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_1LV---_1LM---_1LM---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAj".
Definition mp' := mp_from_str "JV[a_MAi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM232.


Module TM233.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LA---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LD---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_1LV---_1LM---_1LM---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0LO_1Ra---_1L_1LO_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_0RA---_1LV---_1RA---_0RA---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAi".
Definition mp' := mp_from_str "JV[a_MAj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM233.


Module TM234.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LD---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0LO_1Ra---_1L_1LO_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_0RA---_1LV---_1RA---_0RA---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_---0L]_1RJ0L__---1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo1LV_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1LM---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAj".
Definition mp' := mp_from_str "JV[a_MAj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM234.


Module TM235.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LE---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_---0L]_1RJ0L__---1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo1LV_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1LM---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LO_1Ra---_1L_1LO_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_0Ri---_0RA---_1Ri---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAj".
Definition mp' := mp_from_str "JV[a_MAi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM235.


Module TM236.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_1LF0RA_0RD---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RD---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_---0L]_1RJ0L__---1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_---0RC_0L_1RA_---1RC_0Ln1LV_0Lp0R[_1Ln0R[_1Lp---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0R[_1LM0R[_1LO---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0RC---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0RC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAj".
Definition mp' := mp_from_str "JV[a_MAj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM236.


Module TM237.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LA---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0R[_1LM0R[_1LO---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0R[_1LM0R[_1LO---_0R[---_------_1R[---_------_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0RC---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0RC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAj".
Definition mp' := mp_from_str "JV[a_MAi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM237.


Module TM238.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_1LF0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RD---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0Ra_1Ra---_1L_1RJ_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_---0L]_1RJ0L__---1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_---0RC_0L_1RA_---1RC_0Ln1LV_0Lp0RY_1Ln0R[_1Lp---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0Ra_1Ra---_1L_1RJ_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0RY_1LM0R[_1LO---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0RI---_0RD1RA".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_0RI1RJ_0RD1RA_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAiY".
Definition mp' := mp_from_str "JV[a_MAiY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM238.


Module TM239.
Definition tm := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LD_0LB1RF_0LF0RA".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rj1RJ_0Rl0LV_1Rj0L__1Rl0L]_1LV0L]_1RJ0L__0R[1L]_---1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0RC1L__1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1Rj---_1RJ---_1L_---_0L_---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]jC".
Definition mp' := mp_from_str "JV[a_]Aj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM239.


Module TM240.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LD_0LB1RF_0LF0RA".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1Rj---_1RJ---_1L_---_0L_---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rl0RY_1LV0R[_1Rl1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0Rj1L]_1RC1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0RC1L__1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Aj".
Definition mp' := mp_from_str "JV[a_]jC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM240.


Module TM241.
Definition tm := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LD_0LB1RF_0LF0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rl0RY_1LV0R[_1Rl1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0Rj1L]_1RC1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0RC1L__1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0Ra---_0L_---_1Ra---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]jC".
Definition mp' := mp_from_str "JV[a_]Ai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM241.


Module TM242.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LB---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LD---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0Ra---_0L_---_1Ra---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0LV---_0L_---_0L]---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Ai".
Definition mp' := mp_from_str "JV[a_]Ai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM242.


Module TM243.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LC---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LM_1Ra---_1L_1LM_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0LV---_0RJ---_1RJ---_1RJ---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L]_1Ra---_1L_1L]_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0Ra---_0LV---_1Ra---_0L]---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Ai".
Definition mp' := mp_from_str "JV[a_]Aj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM243.


Module TM244.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LC---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LD---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L]_1Ra---_1L_1L]_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0Ra---_0LV---_1Ra---_0L]---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L]_1Ra---_1L_1L]_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_1RJ---_0LV---_0L_---_0L]---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Aj".
Definition mp' := mp_from_str "JV[a_]Aj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM244.


Module TM245.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LO_1Ra---_1L_1LO_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_0Ri---_0RA---_1Ri---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_---0L]_1RJ0L__---1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo1LV_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1L]---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Ai".
Definition mp' := mp_from_str "JV[a_]Aj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM245.


Module TM246.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_---0L]_1RJ0L__---1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo1LV_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1L]---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_0RC---_1LV---_1RC---_1L]---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Aj".
Definition mp' := mp_from_str "JV[a_]Aj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM246.


Module TM247.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB1RC_0LA0RE_1LD---_1RF0LE_0RF0LE_0LC0RA".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_0RC---_1LV---_1RC---_1L]---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0Lg0Lg_1Ri---_1Lg1Lg_0Lg---_1L^0Ra_1L^0Rc_1Le1Ra_1Le1Rc_0LE1RJ_0LG0L^_1LE0RA_1LG1L^_0RC---_1L^---_1RC---_1Le---_0L^---_0L`---_1L^---_1L`---_0Rj1RJ_0Rl0L^_1Rj0Lg_1Rl0Le_---0Le_1RJ0Lg_---1Le_1RR1Lg_0Ri1RJ_0Rk0L^_1Ri0Lg_1Rk0Le_0L^0Le_0RJ0Lg_1L^1Le_0RR1Lg_1RJ0RA_---0RC_0Lg1RA_---1RC_0LU1L^_0LW1L^_1LU0Rc_1LW---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Aj".
Definition mp' := mp_from_str "J^cigeAR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM247.


Module TM248.
Definition tm := TM_from_str "1RB1RC_0LA0RE_1LD---_1RF0LE_0RF0LE_0LC0RA".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RD0LC_0LE0RA_1LF---_1RD0LC".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0Lg0Lg_1Ri---_1Lg1Lg_0Lg---_1L^0Ra_1L^0Rc_1Le1Ra_1Le1Rc_0LE1RJ_0LG0L^_1LE0RA_1LG1L^_0RC---_1L^---_1RC---_1Le---_0L^---_0L`---_1L^---_1L`---_0Rj1RJ_0Rl0L^_1Rj0Lg_1Rl0Le_---0Le_1RJ0Lg_---1Le_1RR1Lg_0Ri1RJ_0Rk0L^_1Ri0Lg_1Rk0Le_0L^0Le_0RJ0Lg_1L^1Le_0RR1Lg_1RJ0RA_---0RC_0Lg1RA_---1RC_0LU1L^_0LW1L^_1LU0Rc_1LW---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW0LW_1RY---_1LW1LW_0LW---_0RA0RQ_1Ln0RS_1RA1RQ_1LU1RS_0LV1RJ_0LX0Ln_1LV0RA_1LX1Ln_0RY1RJ_0R[0Ln_1RY0LW_1R[0LU_0Ln0LU_0RJ0LW_1Ln1LU_0Rb1LW_1RJ0RA_---0RC_0LW1RA_---1RC_0Le1Ln_0Lg1Ln_1Le0RS_1Lg---_0RC---_1Ln---_1RC---_1LU---_0Ln---_0Lp---_1Ln---_1Lp---_0RZ1RJ_0R\0Ln_1RZ0LW_1R\0LU_---0LU_1RJ0LW_---1LU_1Rb1LW".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "J^cigeAR".
Definition mp' := mp_from_str "JnSYWUAb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM248.


Module TM249.
Definition tm := TM_from_str "1RB1RE_1LC0RC_0RD0LC_0LE0RA_1LF---_1RD0LC".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LA---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW0LW_1RY---_1LW1LW_0LW---_0RA0RQ_1Ln0RS_1RA1RQ_1LU1RS_0LV1RJ_0LX0Ln_1LV0RA_1LX1Ln_0RY1RJ_0R[0Ln_1RY0LW_1R[0LU_0Ln0LU_0RJ0LW_1Ln1LU_0Rb1LW_1RJ0RA_---0RC_0LW1RA_---1RC_0Le1Ln_0Lg1Ln_1Le0RS_1Lg---_0RC---_1Ln---_1RC---_1LU---_0Ln---_0Lp---_1Ln---_1Lp---_0RZ1RJ_0R\0Ln_1RZ0LW_1R\0LU_---0LU_1RJ0LW_---1LU_1Rb1LW".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_1LV---_1L]---_1L]---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JnSYWUAb".
Definition mp' := mp_from_str "JV[a_]Ai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM249.


Module TM250.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LA---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RD---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0R[_1LM0R[_1LO---_0R[---_------_1R[---_------_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0R[_1LM0R[_1LO---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0RC---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0RC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Ai".
Definition mp' := mp_from_str "JV[a_]Aj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM250.


Module TM251.
Definition tm := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm' := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm0 := TM'_from_str "0RJ0RC_0RL1LV_1RJ1RC_1RL1Lm_0L_0LV_1Ra0LX_1L_1LV_0L_1LX_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RC1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RC1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO1RC_0Ra---_0Rc---_1Ra---_1Rc---_0LV---_0RJ---_1LV---_0RC---".
Definition tm0' := TM'_from_str "0RJ0RC_0RL1LV_1RJ1RC_1RL1Ln_0L_0LV_1Ra0LX_1L_1LV_0L_1LX_0RC0RY_1LV0R[_1RC1RY_1Ln1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RC1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Ln_0RJ0Lp_1LV1Ln_0RC1Lp_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO1RC_0RQ---_0RS---_1RQ---_1RS---_0Ra---_0LV---_0RC---_1LV---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RI_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_mAC".
Definition mp' := mp_from_str "JV[a_nAC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM251.


Module TM252.
Definition tm := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm' := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0RC_0RL1LV_1RJ1RC_1RL1Ln_0L_0LV_1Ra0LX_1L_1LV_0L_1LX_0RC0RY_1LV0R[_1RC1RY_1Ln1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RC1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Ln_0RJ0Lp_1LV1Ln_0RC1Lp_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO1RC_0RQ---_0RS---_1RQ---_1RS---_0Ra---_0LV---_0RC---_1LV---".
Definition tm0' := TM'_from_str "0RJ0RC_0RL1LV_1RJ1RC_1RL1Lm_0L_0LV_1Ra0LX_1L_1LV_0L_1LX_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RC1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RC1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO1RC_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RI_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_nAC".
Definition mp' := mp_from_str "JV[a_mAC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM252.


Module TM253.
Definition tm := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0RC_0RL1LV_1RJ1RC_1RL1Lm_0L_0LV_1Ra0LX_1L_1LV_0L_1LX_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RC1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RC1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO1RC_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0RC_0RL1LV_1RJ1RC_1RL1Lm_0L_0LV_1Ra0LX_1L_1LV_0L_1LX_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_---0L]_1RJ0L__---1L]_1RC1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RC1Lo_1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo1RJ_1Lm0R[_1Lo1RC_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RI_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_mAC".
Definition mp' := mp_from_str "JV[a_mAC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM253.


Module TM254.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0Rj1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_---0L]_1RJ0L__---1L]_1Rj1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0Rj1Lo_1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo1LV_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RI_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_mAj".
Definition mp' := mp_from_str "JV[a_mAj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM254.


Module TM255.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_0RF0LD_1LE---_1RF0LC_0LD0RA".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_---0L]_1RJ0L__---1L]_1Rj1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0Rj1Lo_1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo1LV_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0LW_1Ri---_1L_1LW_0LW---_0RA0RQ_1Lf0RS_1RA1RQ_---1RS_0LV1RJ_0LX0Lf_1LV0RA_1LX1Lf_0Ri1RJ_0Rk---_1Ri0LW_1Rk---_0Lf0L]_0RJ0L__1Lf1L]_0RZ1L__0RC---_1Lf---_1RC---_1L]---_0Lf---_0Lh---_1Lf---_1Lh---_0Rj1RJ_0Rl0Lf_1Rj0LW_1Rl---_---0LU_1RJ0LW_---1LU_1RZ1LW_1RJ0RA_---0RC_0LW1RA_---1RC_0L]1Lf_0L_1Lf_1L]0RS_1L_---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RI_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_mAj".
Definition mp' := mp_from_str "JfSiW]AZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM255.


Module TM256.
Definition tm := TM_from_str "1RB1RD_1LC0RC_0RF0LD_1LE---_1RF0LC_0LD0RA".
Definition tm' := TM_from_str "1RB1RC_0LA0RE_1LD---_1RF0LE_0RF0LC_0LC0RA".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0LW_1Ri---_1L_1LW_0LW---_0RA0RQ_1Lf0RS_1RA1RQ_---1RS_0LV1RJ_0LX0Lf_1LV0RA_1LX1Lf_0Ri1RJ_0Rk---_1Ri0LW_1Rk---_0Lf0L]_0RJ0L__1Lf1L]_0RZ1L__0RC---_1Lf---_1RC---_1L]---_0Lf---_0Lh---_1Lf---_1Lh---_0Rj1RJ_0Rl0Lf_1Rj0LW_1Rl---_---0LU_1RJ0LW_---1LU_1RZ1LW_1RJ0RA_---0RC_0LW1RA_---1RC_0L]1Lf_0L_1Lf_1L]0RS_1L_---".
Definition tm0' := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0Lg0Lg_1Ri---_1Lg1Lg_0Lg---_1L^0Ra_1L^0Rc_1LU1Ra_1LU1Rc_0LE1RJ_0LG0L^_1LE0RA_1LG1L^_0RC---_1L^---_1RC---_1LU---_0L^---_0L`---_1L^---_1L`---_0Rj1RJ_0Rl0L^_1Rj0Lg_1Rl---_---0Le_1RJ0Lg_---1Le_1RR1Lg_0Ri1RJ_0Rk---_1Ri0Lg_1Rk---_0L^0LU_0RJ0LW_1L^1LU_0RR1LW_1RJ0RA_---0RC_0Lg1RA_---1RC_0LU1L^_0LW1L^_1LU0Rc_1LW---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RI_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JfSiW]AZ".
Definition mp' := mp_from_str "J^cigUAR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM256.


Module TM257.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RZ1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RZ1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0Ra---_0Rc---_1Ra---_1Rc---_0LV---_0RJ---_1LV---_0RZ---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RZ1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RZ1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI---_0LE1RG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RJ_0RA0RH_0RI1RJ_0LE1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_mAZc".
Definition mp' := mp_from_str "JV[a_mAZc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM257.


Module TM258.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RZ1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RZ1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Ln1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RZ1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Ln_0RJ0Lp_1LV1Ln_0RZ1Lp_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0RQ---_0RS---_1RQ---_1RS---_0Ra---_0LV---_0RC---_1LV---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI---_0LE1RG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RJ_0RA0RH_0RI1RJ_0LE1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_mAZc".
Definition mp' := mp_from_str "JV[a_nAZc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM258.


Module TM259.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Ln1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1RZ1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Ln_0RJ0Lp_1LV1Ln_0RZ1Lp_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0RQ---_0RS---_1RQ---_1RS---_0Ra---_0LV---_0RC---_1LV---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_---0L]_1RJ0L__---1L]_1RZ1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RZ1Lo_1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo0Rc_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI---_0LE1RG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RJ_0RA0RH_0RI1RJ_0LE1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_nAZc".
Definition mp' := mp_from_str "JV[a_mAZc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM259.


Module TM260.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_---0L]_1RJ0L__---1L]_1RZ1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0RZ1Lo_1RJ0RA_---0RC_0L_1RA_---1RC_0Lm1LV_0Lo0Rc_1Lm0R[_1Lo---_0RC---_1LV---_1RC---_1Lm---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1Lm1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd---_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc---_1Ra0L__1Rc---_0LV0Lm_0RJ0Lo_1LV1Lm_0Rj1Lo_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0Ra---_0Rc---_1Ra---_1Rc---_0LV---_0RJ---_1LV---_0Rj---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI---_0LE1RG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RJ_0RA0RH_0RI1RJ_0LE1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_mAZc".
Definition mp' := mp_from_str "JV[a_mAjc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM260.


Module TM261.
Definition tm := TM_from_str "1RB0RA_1LC0RD_---1RD_1LF1LE_1RE0LD_1RA1LB".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RF0LD".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Ln_1RC0RJ_1L_0R[_0L_0RA_---0RY_1Ln0R[_---1RY_1Lf1R[_0LV1RJ_0LX0Lf_1LV1RA_1LX1Lf_---0RZ_---0R\_---1RZ_---1R\_---0LP_---0L__---1LP_---1L__0RC0Lf_1LX1Ln_1RC0L__1Lf1Lf_0Ln0Lf_0Lp0Lh_1Ln1Lf_1Lp1Lh_0Rb1RJ_0Rd0Lf_1Rb0LP_1Rd0L__1Rd0L]_0Lf0L__0L_1L]_1Lf1L__0RB---_0RD0Lf_1RB1L__1RD0L__1Lf0LN_1RJ0LP_1R[1LN_1RA1LP".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Lf_1RC0RJ_1L_0R[_0L_0RA_---0RY_1Lf0R[_---1RY_1Ln1R[_0LV1RJ_0LX0Ln_1LV1RA_1LX1Ln_---1RJ_---0Ln_---0LP_---0L__---0L]_---0L__---1L]_---1L__0RC0Ln_1LX1Lf_1RC0L__1Ln1Ln_0Lf0Ln_0Lh0Lp_1Lf1Ln_1Lh1Lp_0RB---_0RD0Ln_1RB1L__1RD0L__1Ln0LN_1RJ0LP_1R[1LN_1RA1LP_0Rj1RJ_0Rl0Ln_1Rj0LP_1Rl0L__1Rl0L]_0Ln0L__0L_1L]_1Ln1L_".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LG_1RA1RH_1LI1LF_0LF0LG_1LB1LF_0RA0RH_---1LG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LG_1RA1RH_1LI1LF_0LF0LG_1LB1LF_0RA0RH_1RJ1LG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "Jn[CPf_AX".
Definition mp' := mp_from_str "Jf[CPn_AX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM261.


Module TM262.
Definition tm := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RF0LD".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RC0LD".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Lf_1RC0RJ_1L_0R[_0L_0RA_---0RY_1Lf0R[_---1RY_1Ln1R[_0LV1RJ_0LX0Ln_1LV1RA_1LX1Ln_---1RJ_---0Ln_---0LP_---0L__---0L]_---0L__---1L]_---1L__0RC0Ln_1LX1Lf_1RC0L__1Ln1Ln_0Lf0Ln_0Lh0Lp_1Lf1Ln_1Lh1Lp_0RB---_0RD0Ln_1RB1L__1RD0L__1Ln0LN_1RJ0LP_1R[1LN_1RA1LP_0Rj1RJ_0Rl0Ln_1Rj0LP_1Rl0L__1Rl0L]_0Ln0L__0L_1L]_1Ln1L_".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Lf_1RC0RJ_1L_0R[_0L_0RA_---0RY_1Lf0R[_---1RY_1Ln1R[_0LV1RJ_0LX0Ln_1LV1RA_1LX1Ln_---1RJ_---0Ln_---0LP_---0L__---0L]_---0L__---1L]_---1L__0RC0Ln_1LX1Lf_1RC0L__1Ln1Ln_0Lf0Ln_0Lh0Lp_1Lf1Ln_1Lh1Lp_0RB---_0RD0Ln_1RB1L__1RD0L__1Ln0LN_1RJ0LP_1R[1LN_1RA1LP_0RR1RJ_0RT0Ln_1RR0LP_1RT0L__---0L]_0Ln0L__---1L]_1Ln1L_".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LG_1RA1RH_1LI1LF_0LF0LG_1LB1LF_0RA0RH_---1LG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LG_1RA1RH_1LI1LF_0LF0LG_1LB1LF_0RA0RH_1RJ1LG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "Jf[CPn_AX".
Definition mp' := mp_from_str "Jf[CPn_AX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM262.


Module TM263.
Definition tm := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RC0LD".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE0LF_1RA1LB_0LF1RB".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Lf_1RC0RJ_1L_0R[_0L_0RA_---0RY_1Lf0R[_---1RY_1Ln1R[_0LV1RJ_0LX0Ln_1LV1RA_1LX1Ln_---1RJ_---0Ln_---0LP_---0L__---0L]_---0L__---1L]_---1L__0RC0Ln_1LX1Lf_1RC0L__1Ln1Ln_0Lf0Ln_0Lh0Lp_1Lf1Ln_1Lh1Lp_0RB---_0RD0Ln_1RB1L__1RD0L__1Ln0LN_1RJ0LP_1R[1LN_1RA1LP_0RR1RJ_0RT0Ln_1RR0LP_1RT0L__---0L]_0Ln0L__---1L]_1Ln1L_".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Lf_1RC0RJ_1L_0R[_0L_0RA_---0RY_1Lf0R[_---1RY_1Lm1R[_0LV1RJ_0LX0Lm_1LV1RA_1LX1Lm_---1RJ_---0Lm_---0LP_---0L__---0L]_---0L__---1L]_---1L__0RC0Lm_1LX1Lf_1RC0L__1Lm1Lm_0Lf0Lm_0Lh0Lo_1Lf1Lm_1Lh1Lo_0RB---_0RD0Lm_1RB1L__1RD0L__1Lm0LN_1RJ0LP_1R[1LN_1RA1LP_0Lm0RJ_1Lf0RL_0L_1RJ_1Lm1RL_0Lm0L__0Lo1RC_1Lm1L__1Lo0L_".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LG_1RA1RH_1LI1LF_0LF0LG_1LB1LF_0RA0RH_---1LG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LG_1RA1RH_1LI1LF_0LF0LG_1LB1LF_0RA0RH_1RJ1LG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "Jf[CPn_AX".
Definition mp' := mp_from_str "Jf[CPm_AX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM263.


Module TM264.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RB---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RL_1RL0RL_1LW0Rc_1Rc---_1Rj0RB_1L^0RD_1LG1RB_1LU1RD_0LV1LU_0LX1RB_1LV1RD_1LX1Rj_0Rc1RB_1LW0L^_1Rc0LG_0Rc0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB1L^_0RD0RB_1RB1LU_1RD1RB_1LU0LE_1RB0LG_1RD1LE_1Rj1LG_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LU1LU_1RB---_1RD1RD_1Rj---_0L`---_0RL---_0LW---_1RL---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RL_1RL0RL_1LW0Rc_1Rc---_1Rj0RB_1L^0RD_1LG1RB_1LU1RD_0LV1LU_0LX1RB_1LV1RD_1LX1Rj_0Rc1RB_1LW0L^_1Rc0LG_0Rc0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB1L^_0RD0RB_1RB1LU_1RD1RB_1LU0LE_1RB0LG_1RD1LE_1Rj1LG_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LU1LU_1RB---_1RD1RD_1Rj---_0RJ---_0RL---_1RJ---_1RL---_0LW---_1RL---_1LW---_1Rc---".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LB_1RF0LD_1LG0RE_1RF1RH_0RA0RE_1LC1LB_0RA---_1RA1RE".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LB_1RF0LD_1LG0RE_1RF1RH_0RA0RE_1LC1LB_0RA1RJ_1RA1RE_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "LU^GcBWjD".
Definition mp' := mp_from_str "LU^GcBWjD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM264.


Module TM265.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RA---".
Definition tm' := TM_from_str "1RB0RE_1LC0LE_1LD0LC_1RA0LA_1RA1RF_1RA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RL_1RL0RD_1LW0Rc_1Rc---_1Rj0RB_1L^0RD_1LG1RB_1LU1RD_0LV1LU_0LX1RB_1LV1RD_1LX1Rj_0Rc1RB_1LW0L^_1Rc0LG_0Rc0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB1L^_0RD0RB_1RB1LU_1RD1RB_1LU0LE_1RB0LG_1RD1LE_1Rj1LG_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LU1RL_1RB---_1RD1Rc_1Rj---_0RB---_0RD---_1RB---_1RD---_1LU---_1RB---_1RD---_1Rj---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RL_1RL0RD_1LW0Rc_1Rc---_1Rj0RL_1L^0RD_1LG1RL_1LU1RD_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0Rc1RB_1LW0L^_1Rc0LG_0Rc0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB1L^_0RD0RB_1RB1LU_1RD1RB_1LU0LE_1RB0LG_1RD1LE_1Rj1LG_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LU1RL_1RB---_1RD1Rc_1Rj---_0RB---_0RD---_1RB---_1RD---_1LU---_1RB---_1RD---_1Rj---".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LB_1RF0LD_1LG0RE_1RF1RH_0RA0RE_1LC1LB_0RI---_1RA1RE".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LB_1RF0LD_1LG0RE_1RF1RH_0RA0RE_1LC1LB_0RI1RJ_1RA1RE_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "LU^GcBWjD".
Definition mp' := mp_from_str "LU^GcBWjD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM265.


Module TM266.
Definition tm := TM_from_str "1RB0RE_1LC0LE_1LD0LC_1RA0LA_1RA1RF_1RA---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA0RF_1LA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RL_1RL0RD_1LW0Rc_1Rc---_1Rj0RL_1L^0RD_1LG1RL_1LU1RD_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0Rc1RB_1LW0L^_1Rc0LG_0Rc0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB1L^_0RD0RB_1RB1LU_1RD1RB_1LU0LE_1RB0LG_1RD1LE_1Rj1LG_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LU1RL_1RB---_1RD1Rc_1Rj---_0RB---_0RD---_1RB---_1RD---_1LU---_1RB---_1RD---_1Rj---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RL_1RL0RD_1LW0Rc_1Rc---_1Ri0RB_1L^0RD_1LG1RB_1LU1RD_0LV1LU_0LX1RB_1LV1RD_1LX1Ri_0Rc1RB_1LW0L^_1Rc0LG_0Rc0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB1L^_0RD0RB_1RB1LU_1RD1RB_1LU0LE_1RB0LG_1RD1LE_1Ri1LG_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1LU1RL_1RB---_1RD1Rc_1Ri---_0RD---_0Ri---_1RD---_1Ri---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LB_1RF0LD_1LG0RE_1RF1RH_0RA0RE_1LC1LB_0RI---_1RA1RE".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LB_1RF0LD_1LG0RE_1RF1RH_0RA0RE_1LC1LB_0RI1RJ_1RA1RE_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "LU^GcBWjD".
Definition mp' := mp_from_str "LU^GcBWiD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM266.


Module TM267.
Definition tm := TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_1RD---".
Definition tm' := TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0LA---".
Definition tm0 := TM'_from_str "1RR0RR_---0RT_1Le1RR_---1RT_0LN1RC_0LP1Le_1LN1Rc_1LP1RR_0RC0Rj_0LW0Rl_1RC1Rj_1Le1Rl_0LU1RC_0LW---_1LU1Rc_1LW---_0RZ1RR_0R\0RC_1RZ1Le_1R\1RC_1Le0Le_1RA0Lg_1RR1Le_1RI1Lg_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1RR_0R\0RC_1LW0RR_0RC0Rj_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LW1Le_0R\0R\_1LW1RR_0RC---_0RZ---_0R\---_1RZ---_1R\---_1Le---_1RA---_1RR---_1RI---".
Definition tm0' := TM'_from_str "1RR0RR_---0RT_1Le1RR_---1RT_0LN1RC_0LP1Le_1LN1Rc_1LP1RR_0RC0Rj_0LW0Rl_1RC1Rj_1Le1Rl_0LU1RC_0LW---_1LU1Rc_1LW---_0RZ1RR_0R\0RC_1RZ1Le_1R\1RC_1Le0Le_1RA0Lg_1RR1Le_1RI1Lg_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1RR_0R\0RC_1LW0RR_0RC0Rj_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LW1Le_0R\0R\_1LW1RR_0RC---_0LW---_0R\---_------_1R\---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1RB0RB_0RC0RD_1RD1RG_1LE1RB_0LF1LE_1RB1LE_1RA1RH_0RD0RI_0RC---".
Definition tm2 := TM'_from_str "1RB0RB_0RC0RD_1RD1RG_1LE1RB_0LF1LE_1RB1LE_1RA1RH_0RD0RI_0RC1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "AR\CeWcIj".
Definition mp' := mp_from_str "AR\CeWcIj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM267.


Module TM268.
Definition tm := TM_from_str "1LB1RC_0LC0RF_1RD0LE_0RA0RE_0RA0RB_0LA---".
Definition tm' := TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0LC---".
Definition tm0 := TM'_from_str "1RR0RR_---0RT_1Le1RR_---1RT_0LN1RC_0LP1Le_1LN1Rc_1LP1RR_0RC0Ri_0LW0Rk_1RC1Ri_1Le1Rk_0LU0LN_0LW---_1LU1LN_1LW---_0RZ1RR_0R\0RC_1RZ1Le_1R\1RC_1Le0Le_1RA0Lg_1RR1Le_1RI1Lg_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1RR_0R\0RC_1LW0RR_0RC0Ri_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LW1Le_0R\0LW_1LW1RR_0RC---_0LW---_0R\---_------_1R\---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "1RR0RR_---0RT_1Le1RR_---1RT_0LN1RC_0LP1Le_1LN1Rc_1LP1RR_0RC0Rj_0LW0Rl_1RC1Rj_1Le1Rl_0LU0Le_0LW---_1LU1Le_1LW---_0RZ1RR_0R\0RC_1RZ1Le_1R\1RC_1Le0Le_1RA0Lg_1RR1Le_1RI1Lg_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1RR_0R\0RC_1LW0RR_0RC0Rj_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LW1Le_0R\0LW_1LW1RR_0RC---_0RC---_0LW---_1RC---_1Le---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1RB0RB_0RC0RD_1RD1RG_1LE1RB_0LF1LE_1RB1LE_1RA1RH_0RD0RI_0LF---".
Definition tm2 := TM'_from_str "1RB0RB_0RC0RD_1RD1RG_1LE1RB_0LF1LE_1RB1LE_1RA1RH_0RD0RI_0LF1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "AR\CeWcIi".
Definition mp' := mp_from_str "AR\CeWcIj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM268.


Module TM269.
Definition tm := TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0LC---".
Definition tm' := TM_from_str "1LB1RC_0LC---_1RD0LE_0RA0RE_0RA0RF_0LC1RB".
Definition tm0 := TM'_from_str "1RR0RR_---0RT_1Le1RR_---1RT_0LN1RC_0LP1Le_1LN1Rc_1LP1RR_0RC0Rj_0LW0Rl_1RC1Rj_1Le1Rl_0LU0Le_0LW---_1LU1Le_1LW---_0RZ1RR_0R\0RC_1RZ1Le_1R\1RC_1Le0Le_1RA0Lg_1RR1Le_1RI1Lg_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1RR_0R\0RC_1LW0RR_0RC0Rj_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LW1Le_0R\0LW_1LW1RR_0RC---_0RC---_0LW---_1RC---_1Le---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "1RR0RR_---0RT_1Le1RR_---1RT_0LN1RC_0LP1Le_1LN1Rc_1LP1RR_0RC---_0LW---_1RC---_1Le---_0LU---_0LW---_1LU---_1LW---_0RZ1RR_0R\0RC_1RZ1Le_1R\1RC_1Le0Le_1RA0Lg_1RR1Le_1Ri1Lg_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_0LW1RR_0R\0RC_1LW0RR_0RC0RJ_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LW1Le_0R\0LW_1LW1RR_0RC---_0RC0RJ_0LW0RL_1RC1RJ_1Le1RL_0LU0Le_0LW---_1LU1Le_1LW---".
Definition tm1 := TM'_from_str "1RB0RB_0RC0RD_1RD1RG_1LE1RB_0LF1LE_1RB1LE_1RA1RH_0RD0RI_0LF---".
Definition tm2 := TM'_from_str "1RB0RB_0RC0RD_1RD1RG_1LE1RB_0LF1LE_1RB1LE_1RA1RH_0RD0RI_0LF1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "AR\CeWcIj".
Definition mp' := mp_from_str "AR\CeWciJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM269.


Module TM270.
Definition tm := TM_from_str "1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_0RD0RA_1RE1LE_1LF---_1LA1LF".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LH_1RJ0Lo_1RL0Lp_1R[0Lm_1RR0Lo_1RC1Lm_1RI1Lo_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Rb0R[_1RJ0RR_1Lp0RC_0Lo0RI_0RY0RA_0R[0RC_1RY1RA_1R[1RC_1LH0RT_0Lp0LF_---0RK_1Lp1LF_0Rb1LH_0Rd0Lp_1Rb1Lp_1Rd0L]_0Lp0L]_---0L__1Lp1L]_---1L__1RI---_1LH---_1Lo---_1Lp---_0Ln---_0Lp---_1Ln---_1Lp---_0RK1RI_1LF1LH_1RK1Lo_1Ln1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LH_1RJ0Lo_1RL0Lp_1R[0Lm_1RR0Lo_1RC1Lm_1RI1Lo_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Rb0R[_1RJ0RR_1Lp0RC_0Lo0RI_0RY0RA_0R[0RC_1RY1RA_1R[1RC_1LH0RT_0Lp0LF_---0RK_1Lp1LF_0Rb1LH_0Rd---_1Rb1Lp_1Rd---_0Lp0Lf_---0Lh_1Lp1Lf_---1Lh_1RI---_1LH---_1Lo---_1Lp---_0Ln---_0Lp---_1Ln---_1Lp---_0RK1RI_1LF1LH_1RK1Lo_1Ln1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm1 := TM'_from_str "1LB---_1RF1LC_1LD1LE_1RG0LC_0LB0LM_0RG0RF_0RK0RH_1RI0LC_0RL0RJ_1RG1RF_1RA1LM_1RK1RH_1LB1LM".
Definition tm2 := TM'_from_str "1LB1RN_1RF1LC_1LD1LE_1RG0LC_0LB0LM_0RG0RF_0RK0RH_1RI0LC_0RL0RJ_1RG1RF_1RA1LM_1RK1RH_1LB1LM_1RN1RN".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "bHoFnIRCJK[Tp".
Definition mp' := mp_from_str "bHoFnIRCJK[Tp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM270.


Module TM271.
Definition tm := TM_from_str "1RB1RD_1LC0RF_1RA1LD_0RE0LB_---1RC_1RA1RC".
Definition tm' := TM_from_str "1RB1RD_1LC0RF_1RA1LD_1RE0LB_---1LB_1RA1RC".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1RB0RL_1L`1RR_1RR0R\_0R\0Ri_1LV0Rk_1R\1Ri_1LO1Rk_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rc0L`_1Rk1L^_1RB1L`_0Ra1Rc_0Rc0RB_1Ra0L`_1Rc1RB_---0LM_0RD0LO_---1LM_1LV1LO_---0RR_---0RT_---1RR_---1RT_---1RL_---0LO_---1R\_---1LO_0RB0RR_0RD0RT_1RB1RR_1RD1RT_1LO1RL_1Rc0LO_1Rk1R\_1RB1LO".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1RB0RL_1L`1RR_1RR0R\_0R\0Ri_1LV0Rk_1R\1Ri_1LO1Rk_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rd0L`_1Rk1L^_1RB1L`_0Rb1Rd_0Rd0RB_1Rb0L`_1Rd1RB_---0LM_0RD0LO_---1LM_1LV1LO_---1RB_---0RR_---1L`_---1RR_---0LN_---0LP_---1LN_---1LP_0RB0RR_0RD0RT_1RB1RR_1RD1RT_1LO1RL_1Rd0LO_1Rk1R\_1RB1LO".
Definition tm1 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_---1RH".
Definition tm2 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_1RK1RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "LOV`\BkRDc".
Definition mp' := mp_from_str "LOV`\BkRDd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM271.


Module TM272.
Definition tm := TM_from_str "1RB1RD_1LC0RF_1RA1LD_1RE0LB_---1LB_1RA1RC".
Definition tm' := TM_from_str "1RB1RA_1LC0RC_1RF1LD_0RE0LB_---1RC_0LA1RD".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1RB0RL_1L`1RR_1RR0R\_0R\0Ri_1LV0Rk_1R\1Ri_1LO1Rk_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rd0L`_1Rk1L^_1RB1L`_0Rb1Rd_0Rd0RB_1Rb0L`_1Rd1RB_---0LM_0RD0LO_---1LM_1LV1LO_---1RB_---0RR_---1L`_---1RR_---0LN_---0LP_---1LN_---1LP_0RB0RR_0RD0RT_1RB1RR_1RD1RT_1LO1RL_1Rd0LO_1Rk1R\_1RB1LO".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0L`1LO_1Rj1RL_1L`1RS_1RR1RD_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0Rl_1LV0R\_1LX1LV_0Rj0RR_0Rl1LV_1Rj1RR_1Rl0R\_1LO0L^_1Rc0L`_1RS1L^_1Rj1L`_0Ra1Rc_0Rc0Rj_1Ra0L`_1Rc1Rj_---0LM_0Rl0LO_---1LM_1LV1LO_---0RR_---0RT_---1RR_---1RT_---1RL_---0LO_---1R\_---1LO_1LV0RZ_0RL0R\_1LO1RZ_1RL1R\_0LE---_0LG0RL_1LE1RR_1LG0R\".
Definition tm1 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_---1RH".
Definition tm2 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_1RK1RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "LOV`\BkRDd".
Definition mp' := mp_from_str "LOV`\jSRlc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM272.


Module TM273.
Definition tm := TM_from_str "1RB1RA_1LC0RC_1RF1LD_0RE0LB_---1RC_0LA1RD".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_1RE0LB_---0LF_1RC0RF".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0L`1LO_1Rj1RL_1L`1RS_1RR1RD_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0Rl_1LV0R\_1LX1LV_0Rj0RR_0Rl1LV_1Rj1RR_1Rl0R\_1LO0L^_1Rc0L`_1RS1L^_1Rj1L`_0Ra1Rc_0Rc0Rj_1Ra0L`_1Rc1Rj_---0LM_0Rl0LO_---1LM_1LV1LO_---0RR_---0RT_---1RR_---1RT_---1RL_---0LO_---1R\_---1LO_1LV0RZ_0RL0R\_1LO1RZ_1RL1R\_0LE---_0LG0RL_1LE1RR_1LG0R\".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1RB0RL_1L`1RR_1RR0R\_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rd0L`_1RS1L^_1RB1L`_0Rb1Rd_0Rd0RB_1Rb0L`_1Rd1RB_---0LM_0RD0LO_---1LM_1LV1LO_---0RD_---0RR_---1RD_---1RR_---0Lm_---0Lo_---1Lm_---1Lo_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1RL0RD_0LO0RR_1R\1LV_1LO0Ri".
Definition tm1 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_---1RH".
Definition tm2 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_1RK1RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "LOV`\jSRlc".
Definition mp' := mp_from_str "LOV`\BSRDd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM273.


Module TM274.
Definition tm := TM_from_str "1RB1RD_1LC0RC_1RA1LD_1RE0LB_---0LF_1RC0RF".
Definition tm' := TM_from_str "1RB---_1LC0RC_1RF1LD_0RE0LB_---1RC_1RB1RD".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1RB0RL_1L`1RR_1RR0R\_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rd0L`_1RS1L^_1RB1L`_0Rb1Rd_0Rd0RB_1Rb0L`_1Rd1RB_---0LM_0RD0LO_---1LM_1LV1LO_---0RD_---0RR_---1RD_---1RR_---0Lm_---0Lo_---1Lm_---1Lo_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1RL0RD_0LO0RR_1R\1LV_1LO0Ri".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L`---_1Rj---_1L`---_1RR---_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0Rl_1LV0R\_1LX1LV_0Rj0RR_0Rl1LV_1Rj1RR_1Rl0R\_1LO0L^_1Rc0L`_1RS1L^_1Rj1L`_0Ra1Rc_0Rc0Rj_1Ra0L`_1Rc1Rj_---0LM_0Rl0LO_---1LM_1LV1LO_---0RR_---0RT_---1RR_---1RT_---1RL_---0LO_---1R\_---1LO_0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1Rj0RL_1L`1RR_1RR0R\".
Definition tm1 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_---1RH".
Definition tm2 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_1RK1RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "LOV`\BSRDd".
Definition mp' := mp_from_str "LOV`\jSRlc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM274.


Module TM275.
Definition tm := TM_from_str "1RB---_1LC0RC_1RF1LD_0RE0LB_---1RC_1RB1RD".
Definition tm' := TM_from_str "1RB0LF_1LC0RC_1RA1LD_0RE0LB_---1RC_1RD1RF".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L`---_1Rj---_1L`---_1RR---_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0Rl_1LV0R\_1LX1LV_0Rj0RR_0Rl1LV_1Rj1RR_1Rl0R\_1LO0L^_1Rc0L`_1RS1L^_1Rj1L`_0Ra1Rc_0Rc0Rj_1Ra0L`_1Rc1Rj_---0LM_0Rl0LO_---1LM_1LV1LO_---0RR_---0RT_---1RR_---1RT_---1RL_---0LO_---1R\_---1LO_0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1Rj0RL_1L`1RR_1RR0R\".
Definition tm0' := TM'_from_str "0RJ0Rc_0RL0R\_1RJ1Rc_1RL1R\_0L`0Lm_1RB0Lo_1L`1Lm_1RR1Lo_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rc0L`_1RS1L^_1RB1L`_0Ra1Rc_0Rc0RB_1Ra0L`_1Rc1RB_---0LM_0RD0LO_---1LM_1LV1LO_---0RR_---0RT_---1RR_---1RT_---1RL_---0LO_---1R\_---1LO_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_---1Rc_0RL1R\_1RR1RB_0R\1Rl".
Definition tm1 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_---1RH".
Definition tm2 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_1RK1RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "LOV`\jSRlc".
Definition mp' := mp_from_str "LOV`\BSRDc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM275.


Module TM276.
Definition tm := TM_from_str "1RB0LF_1LC0RC_1RA1LD_0RE0LB_---1RC_1RD1RF".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1LF_0RF1RC".
Definition tm0 := TM'_from_str "0RJ0Rc_0RL0R\_1RJ1Rc_1RL1R\_0L`0Lm_1RB0Lo_1L`1Lm_1RR1Lo_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rc0L`_1RS1L^_1RB1L`_0Ra1Rc_0Rc0RB_1Ra0L`_1Rc1RB_---0LM_0RD0LO_---1LM_1LV1LO_---0RR_---0RT_---1RR_---1RT_---1RL_---0LO_---1R\_---1LO_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_---1Rc_0RL1R\_1RR1RB_0R\1Rl".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L`---_1RB0RL_1L`1RR_1RR0R\_0R\0RQ_1LV0RS_1R\1RQ_1LO1RS_0LV0RL_0LX0RD_1LV0R\_1LX1LV_0RB0RR_0RD1LV_1RB1RR_1RD0R\_1LO0L^_1Rc0L`_1RS1L^_1RB1L`_0Ra1Rc_0Rc0RB_1Ra0L`_1Rc1RB_---0LM_0RD0LO_---1LM_1LV1LO_---0RR_---1LV_---1RR_---0R\_---0Ln_---0Lp_---1Ln_---1Lp_0Ri0RR_0Rk0RT_1Ri1RR_1Rk1RT_0Ri1RL_0RD0LO_0RR1R\_1LV1LO".
Definition tm1 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_---1RH".
Definition tm2 := TM'_from_str "1LB1RG_1LC0RE_1RJ0LD_1LC1LB_1RJ1RF_0RA0RE_1RF1RH_0RI1LC_1RA1RE_1RK1RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "LOV`\BSRDc".
Definition mp' := mp_from_str "LOV`\BSRDc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM276.


Module TM277.
Definition tm := TM_from_str "1RB0LD_1LC1RE_0RA0LD_1LA0LD_0RF---_0RC1RC".
Definition tm' := TM_from_str "1RB1LD_1LC1RF_1LA1LD_0RE1RE_0RA0LC_0RD---".
Definition tm0 := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0L__1RL0L]_0L_0L]_1Rk0L__1L_1L]_---1L__1Rk0Rb_1LF0Rd_0L_1Rb_1L]1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0L__1RC0L]_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0L__1L]0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0L]_1Rk0L__1LF1L]".
Definition tm0' := TM'_from_str "0RJ1R[_0RL0LF_1RJ0L`_1RL0L^_0L`0L^_1R[0L`_1L`1L^_---1L`_---0Rj_1LF0Rl_1L`1Rj_1L^1Rl_0LV1Ra_0LX---_1LV1Rb_1LX---_0Rl1R[_1LF0LF_1Rl0L`_1L^0L^_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0RJ1RJ_0LF0L^_1R[0L`_1LF1L^_0RA1R[_0RC0LF_1RA0L`_1RC0L^_1LF0LU_0LF0LW_0Rl1LU_1LF1LW_0RY---_0R[---_1RY---_1R[---_0RA---_0RC---_1R[---_0LF---".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QAJFkRC_]d".
Definition mp' := mp_from_str "aAJF[bC`^l".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM277.


Module TM278.
Definition tm := TM_from_str "1RB1LD_1LC1RF_1LA1LD_0RE1RE_0RA0LC_0RD---".
Definition tm' := TM_from_str "1RB1LF_1LC1RE_0RA0LD_1LA1LF_0RF---_0RC1RC".
Definition tm0 := TM'_from_str "0RJ1R[_0RL0LF_1RJ0L`_1RL0L^_0L`0L^_1R[0L`_1L`1L^_---1L`_---0Rj_1LF0Rl_1L`1Rj_1L^1Rl_0LV1Ra_0LX---_1LV1Rb_1LX---_0Rl1R[_1LF0LF_1Rl0L`_1L^0L^_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0RJ1RJ_0LF0L^_1R[0L`_1LF1L^_0RA1R[_0RC0LF_1RA0L`_1RC0L^_1LF0LU_0LF0LW_0Rl1LU_1LF1LW_0RY---_0R[---_1RY---_1R[---_0RA---_0RC---_1R[---_0LF---".
Definition tm0' := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0Lp_1RL0Ln_0L_0Ln_1Rk0Lp_1L_1Ln_---1Lp_1Rk0Rb_1LF0Rd_0Lp1Rb_1Ln1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0Lp_1RC0Ln_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0Lp_1Ln0Ln_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0Ln_1Rk0Lp_1LF1Ln".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "aAJF[bC`^l".
Definition mp' := mp_from_str "QAJFkRCpnd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM278.


Module TM279.
Definition tm := TM_from_str "1RB1LF_1LC1RE_0RA0LD_1LA1LF_0RF---_0RC1RC".
Definition tm' := TM_from_str "1RB1LF_1LC1RE_0RA0LD_1LA0LD_0RF---_0RC1RC".
Definition tm0 := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0Lp_1RL0Ln_0L_0Ln_1Rk0Lp_1L_1Ln_---1Lp_1Rk0Rb_1LF0Rd_0Lp1Rb_1Ln1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0Lp_1RC0Ln_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0Lp_1Ln0Ln_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0Ln_1Rk0Lp_1LF1Ln".
Definition tm0' := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0Lp_1RL0L]_0L_0Ln_1Rk0Lp_1L_1Ln_---1Lp_1Rk0Rb_1LF0Rd_0Lp1Rb_1L]1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0Lp_1RC0L]_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0Lp_1L]0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0L]_1Rk0Lp_1LF1L]".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QAJFkRCpnd".
Definition mp' := mp_from_str "QAJFkRCp]d".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM279.


Module TM280.
Definition tm := TM_from_str "1RB1LF_1LC1RE_0RA0LD_1LA0LD_0RF---_0RC1RC".
Definition tm' := TM_from_str "1RB0LD_1LC1RE_0RA0LD_1LA1LF_0RF---_0RC1RC".
Definition tm0 := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0Lp_1RL0L]_0L_0Ln_1Rk0Lp_1L_1Ln_---1Lp_1Rk0Rb_1LF0Rd_0Lp1Rb_1L]1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0Lp_1RC0L]_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0Lp_1L]0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0L]_1Rk0Lp_1LF1L]".
Definition tm0' := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0L__1RL0Ln_0L_0L]_1Rk0L__1L_1L]_---1L__1Rk0Rb_1LF0Rd_0L_1Rb_1Ln1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0L__1RC0Ln_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0L__1Ln0Ln_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0Ln_1Rk0L__1LF1Ln".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QAJFkRCp]d".
Definition mp' := mp_from_str "QAJFkRC_nd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM280.


Module TM281.
Definition tm := TM_from_str "1RB0LD_1LC1RE_0RA0LD_1LA1LF_0RF---_0RC1RC".
Definition tm' := TM_from_str "1RB0LC_1LA1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm0 := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0L__1RL0Ln_0L_0L]_1Rk0L__1L_1L]_---1L__1Rk0Rb_1LF0Rd_0L_1Rb_1Ln1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0L__1RC0Ln_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0L__1Ln0Ln_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0Ln_1Rk0L__1LF1Ln".
Definition tm0' := TM'_from_str "0RJ1Rc_0RL0LF_1RJ0LW_1RL0LU_0LW0LU_1Rc0LW_1LW1LU_---1LW_0R\0RZ_1LF0R\_1R\1RZ_1LU1R\_0LF1Ri_0LH---_1LF1Rj_1LH---_0R\1Rc_1LF0LF_1R\0LW_1LU0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Ra---_0Rc---_1Ra---_1Rc---_0RA---_0RC---_1Rc---_0LF---_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RJ1RJ_0LF0LU_1Rc0LW_1LF1LU_0RA1Rc_0RC0LF_1RA0LW_1RC0LU_1LF0LU_0LF0LW_0R\1LU_1LF1LW".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QAJFkRC_nd".
Definition mp' := mp_from_str "iAJFcjCWU\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM281.


Module TM282.
Definition tm := TM_from_str "1RB0LC_1LA1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm' := TM_from_str "1RB0LC_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm0 := TM'_from_str "0RJ1Rc_0RL0LF_1RJ0LW_1RL0LU_0LW0LU_1Rc0LW_1LW1LU_---1LW_0R\0RZ_1LF0R\_1R\1RZ_1LU1R\_0LF1Ri_0LH---_1LF1Rj_1LH---_0R\1Rc_1LF0LF_1R\0LW_1LU0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Ra---_0Rc---_1Ra---_1Rc---_0RA---_0RC---_1Rc---_0LF---_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RJ1RJ_0LF0LU_1Rc0LW_1LF1LU_0RA1Rc_0RC0LF_1RA0LW_1RC0LU_1LF0LU_0LF0LW_0R\1LU_1LF1LW".
Definition tm0' := TM'_from_str "0RJ1Rc_0RL0LF_1RJ0LW_1RL0LU_0LW0LU_1Rc0LW_1LW1LU_---1LW_---0RZ_1LF0R\_1LW1RZ_1LU1R\_0LV1Ri_0LX---_1LV1Rj_1LX---_0R\1Rc_1LF0LF_1R\0LW_1LU0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Ra---_0Rc---_1Ra---_1Rc---_0RA---_0RC---_1Rc---_0LF---_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RJ1RJ_0LF0LU_1Rc0LW_1LF1LU_0RA1Rc_0RC0LF_1RA0LW_1RC0LU_1LF0LU_0LF0LW_0R\1LU_1LF1LW".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "iAJFcjCWU\".
Definition mp' := mp_from_str "iAJFcjCWU\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM282.


Module TM283.
Definition tm := TM_from_str "1RB0LC_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm' := TM_from_str "1RB0LC_1LC1RF_1LA1LD_0RE1RE_0RA0LC_0RD---".
Definition tm0 := TM'_from_str "0RJ1Rc_0RL0LF_1RJ0LW_1RL0LU_0LW0LU_1Rc0LW_1LW1LU_---1LW_---0RZ_1LF0R\_1LW1RZ_1LU1R\_0LV1Ri_0LX---_1LV1Rj_1LX---_0R\1Rc_1LF0LF_1R\0LW_1LU0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Ra---_0Rc---_1Ra---_1Rc---_0RA---_0RC---_1Rc---_0LF---_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RJ1RJ_0LF0LU_1Rc0LW_1LF1LU_0RA1Rc_0RC0LF_1RA0LW_1RC0LU_1LF0LU_0LF0LW_0R\1LU_1LF1LW".
Definition tm0' := TM'_from_str "0RJ1R[_0RL0LF_1RJ0LW_1RL0L^_0L`0LU_1R[0LW_1L`1LU_---1LW_---0Rj_1LF0Rl_1LW1Rj_1L^1Rl_0LV1Ra_0LX---_1LV1Rb_1LX---_0Rl1R[_1LF0LF_1Rl0LW_1L^0L^_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0RJ1RJ_0LF0L^_1R[0LW_1LF1L^_0RA1R[_0RC0LF_1RA0LW_1RC0L^_1LF0LU_0LF0LW_0Rl1LU_1LF1LW_0RY---_0R[---_1RY---_1R[---_0RA---_0RC---_1R[---_0LF---".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "iAJFcjCWU\".
Definition mp' := mp_from_str "aAJF[bCW^l".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM283.


Module TM284.
Definition tm := TM_from_str "1RB0LC_1LC1RF_1LA1LD_0RE1RE_0RA0LC_0RD---".
Definition tm' := TM_from_str "1RB1LE_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm0 := TM'_from_str "0RJ1R[_0RL0LF_1RJ0LW_1RL0L^_0L`0LU_1R[0LW_1L`1LU_---1LW_---0Rj_1LF0Rl_1LW1Rj_1L^1Rl_0LV1Ra_0LX---_1LV1Rb_1LX---_0Rl1R[_1LF0LF_1Rl0LW_1L^0L^_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0RJ1RJ_0LF0L^_1R[0LW_1LF1L^_0RA1R[_0RC0LF_1RA0LW_1RC0L^_1LF0LU_0LF0LW_0Rl1LU_1LF1LW_0RY---_0R[---_1RY---_1R[---_0RA---_0RC---_1R[---_0LF---".
Definition tm0' := TM'_from_str "0RJ1Rc_0RL0LF_1RJ0Lh_1RL0LU_0LW0Lf_1Rc0Lh_1LW1Lf_---1Lh_---0RZ_1LF0R\_1Lh1RZ_1LU1R\_0LV1Ri_0LX---_1LV1Rj_1LX---_0R\1Rc_1LF0LF_1R\0Lh_1LU0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Ra---_0Rc---_1Ra---_1Rc---_0RA---_0RC---_1Rc---_0LF---_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RJ1RJ_0LF0LU_1Rc0Lh_1LF1LU_0RA1Rc_0RC0LF_1RA0Lh_1RC0LU_1LF0LU_0LF0LW_0R\1LU_1LF1LW".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "aAJF[bCW^l".
Definition mp' := mp_from_str "iAJFcjChU\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM284.


Module TM285.
Definition tm := TM_from_str "1RB1LE_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm' := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---".
Definition tm0 := TM'_from_str "0RJ1Rc_0RL0LF_1RJ0Lh_1RL0LU_0LW0Lf_1Rc0Lh_1LW1Lf_---1Lh_---0RZ_1LF0R\_1Lh1RZ_1LU1R\_0LV1Ri_0LX---_1LV1Rj_1LX---_0R\1Rc_1LF0LF_1R\0Lh_1LU0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Ra---_0Rc---_1Ra---_1Rc---_0RA---_0RC---_1Rc---_0LF---_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RJ1RJ_0LF0LU_1Rc0Lh_1LF1LU_0RA1Rc_0RC0LF_1RA0Lh_1RC0LU_1LF0LU_0LF0LW_0R\1LU_1LF1LW".
Definition tm0' := TM'_from_str "0RJ1RS_0RL0LF_1RJ0LX_1RL0Le_0LX0LV_1RS0LX_1LX1LV_---1LX_0Rl0Rj_1LF0Rl_1Rl1Rj_1Le1Rl_0LF1RY_0LH---_1LF1RZ_1LH---_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0RJ1RJ_0LF0Le_1RS0LX_1LF1Le_0RA1RS_0RC0LF_1RA0LX_1RC0Le_1LF0Le_0LF0Lg_0Rl1Le_1LF1Lg_0Rl1RS_1LF0LF_1Rl0LX_1Le0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RQ---_0RS---_1RQ---_1RS---_0RA---_0RC---_1RS---_0LF---".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "iAJFcjChU\".
Definition mp' := mp_from_str "YAJFSZCXel".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM285.


Module TM286.
Definition tm := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---".
Definition tm' := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA1LC_0RC---".
Definition tm0 := TM'_from_str "0RJ1RS_0RL0LF_1RJ0LX_1RL0Le_0LX0LV_1RS0LX_1LX1LV_---1LX_0Rl0Rj_1LF0Rl_1Rl1Rj_1Le1Rl_0LF1RY_0LH---_1LF1RZ_1LH---_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0RJ1RJ_0LF0Le_1RS0LX_1LF1Le_0RA1RS_0RC0LF_1RA0LX_1RC0Le_1LF0Le_0LF0Lg_0Rl1Le_1LF1Lg_0Rl1RS_1LF0LF_1Rl0LX_1Le0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RQ---_0RS---_1RQ---_1RS---_0RA---_0RC---_1RS---_0LF---".
Definition tm0' := TM'_from_str "0RJ1RS_0RL0LF_1RJ0LX_1RL0LV_0LX0LV_1RS0LX_1LX1LV_---1LX_0Rl0Rj_1LF0Rl_1Rl1Rj_1LV1Rl_0LF1RY_0LH---_1LF1RZ_1LH---_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0RJ1RJ_0LF0LV_1RS0LX_1LF1LV_0RA1RS_0RC0LF_1RA0LX_1RC0LV_1LF0Le_0LF0Lg_0Rl1Le_1LF1Lg_0Rl1RS_1LF0LF_1Rl0LX_1LV0LV_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0RQ---_0RS---_1RQ---_1RS---_0RA---_0RC---_1RS---_0LF---".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "YAJFSZCXel".
Definition mp' := mp_from_str "YAJFSZCXVl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM286.


Module TM287.
Definition tm := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA1LC_0RC---".
Definition tm' := TM_from_str "1RB1LC_1LA1RE_0RD1RF_0RA0LB_0RC---_0RA0LA".
Definition tm0 := TM'_from_str "0RJ1RS_0RL0LF_1RJ0LX_1RL0LV_0LX0LV_1RS0LX_1LX1LV_---1LX_0Rl0Rj_1LF0Rl_1Rl1Rj_1LV1Rl_0LF1RY_0LH---_1LF1RZ_1LH---_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0RJ1RJ_0LF0LV_1RS0LX_1LF1LV_0RA1RS_0RC0LF_1RA0LX_1RC0LV_1LF0Le_0LF0Lg_0Rl1Le_1LF1Lg_0Rl1RS_1LF0LF_1Rl0LX_1LV0LV_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0RQ---_0RS---_1RQ---_1RS---_0RA---_0RC---_1RS---_0LF---".
Definition tm0' := TM'_from_str "0RJ1RS_0RL0LF_1RJ0LX_1RL0LV_0LX0LV_1RS0LX_1LX1LV_---1LX_0Rd0Rb_1LF0Rd_1Rd1Rb_1LV1Rd_0LF1RY_0LH---_1LF1Rj_1LH---_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_0RJ1RJ_0LF0LV_1RS0LX_1LF1LV_0RA1RS_0RC0RS_1RA0LX_1RC1RS_1LF0LM_0LF0LO_0Rd1LM_1LF1LO_0RQ---_0RS---_1RQ---_1RS---_0RA---_0RC---_1RS---_0LF---_0RA1LF_0RC0LF_1RA1LV_1RC0LV_1LF0LE_0LF0LG_0Rd1LE_1LF1LG".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "YAJFSZCXVl".
Definition mp' := mp_from_str "YAJFSjCXVd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM287.


Module TM288.
Definition tm := TM_from_str "1RB1LC_1LA1RE_0RD1RF_0RA0LB_0RC---_0RA0LA".
Definition tm' := TM_from_str "1RB0LC_1LA1RD_1LA1LE_0RE---_0RF1RF_0RA0LC".
Definition tm0 := TM'_from_str "0RJ1RS_0RL0LF_1RJ0LX_1RL0LV_0LX0LV_1RS0LX_1LX1LV_---1LX_0Rd0Rb_1LF0Rd_1Rd1Rb_1LV1Rd_0LF1RY_0LH---_1LF1Rj_1LH---_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_0RJ1RJ_0LF0LV_1RS0LX_1LF1LV_0RA1RS_0RC0RS_1RA0LX_1RC1RS_1LF0LM_0LF0LO_0Rd1LM_1LF1LO_0RQ---_0RS---_1RQ---_1RS---_0RA---_0RC---_1RS---_0LF---_0RA1LF_0RC0LF_1RA1LV_1RC0LV_1LF0LE_0LF0LG_0Rd1LE_1LF1LG".
Definition tm0' := TM'_from_str "0RJ1Rc_0RL0LF_1RJ0LW_1RL0Lf_0LW0LU_1Rc0LW_1LW1LU_---1LW_0R\0RZ_1LF0R\_1R\1RZ_1Lf1R\_0LF1Ri_0LH---_1LF1Rj_1LH---_0R\1Rc_1LF0LF_1R\0LW_1Lf0Lf_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0Ra---_0Rc---_1Ra---_1Rc---_0RA---_0RC---_1Rc---_0LF---_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RJ1RJ_0LF0Lf_1Rc0LW_1LF1Lf_0RA1Rc_0RC0LF_1RA0LW_1RC0Lf_1LF0LU_0LF0LW_0R\1LU_1LF1LW".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "YAJFSjCXVd".
Definition mp' := mp_from_str "iAJFcjCWf\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM288.


Module TM289.
Definition tm := TM_from_str "1LB0RF_1RC0LE_0RD1RC_1RA---_0LB1LA_1RC1RF".
Definition tm' := TM_from_str "1LB0RD_1RC0LF_0RE0LD_1RC1RD_1RA---_0LB1LA".
Definition tm0 := TM'_from_str "0RT0Ri_1LM0Rk_1RT1Ri_1LF1Rk_0LN0R[_0LP0RT_1LN0RT_1LP0Rl_0RR1RB_0RT0LP_1RR0Le_1RT0RT_1RB0Le_1R[0Lg_---1Le_1RT1Lg_0RY0RR_0R[0RT_1RY1RR_1R[1RT_1LM1RB_---1R[_0Rk---_---1RT_0RB---_0RD---_1RB---_1RD---_0Lg---_1RR---_1Lg---_1Rj---_0R[1RT_0LM0Rj_1R[1Lg_0LF1Rj_0LM0LF_0LO0LH_1LM1LF_1LO1LH_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_1RB1R[_1R[1RT_---1RT_1RT1Rl".
Definition tm0' := TM'_from_str "0RT0RY_1LM0R[_1RT1RY_1LF1R[_0LN0Rc_0LP0RT_1LN0RT_1LP0R\_0RR1RB_0RT0LP_1RR0Lm_1RT0RT_1RB0Lm_1Rc0Lo_---1Lm_1RT1Lo_0Ra0Rc_0Rc0RT_1Ra1Rc_1Rc1RT_1LM0L]_---0L__0R[1L]_---1L__0RR0RZ_0RT0R\_1RR1RZ_1RT1R\_1RB1Rc_1Rc1RT_---1RT_1RT1R\_0RB---_0RD---_1RB---_1RD---_0Lo---_1RR---_1Lo---_1RZ---_0Rc1RT_0LM0RZ_1Rc1Lo_0LF1RZ_0LM0LF_0LO0LH_1LM1LF_1LO1LH".
Definition tm1 := TM'_from_str "1LB0RI_1RA0LC_0LB0LD_0LE0RG_1RG1LF_1LB1LD_1RH1RG_1RA---_1RL1RJ_0RG0RK_1RG1RK_0RH0RG".
Definition tm2 := TM'_from_str "1LB0RI_1RA0LC_0LB0LD_0LE0RG_1RG1LF_1LB1LD_1RH1RG_1RA1RM_1RL1RJ_0RG0RK_1RG1RK_0RH0RG_1RM1RM".
Definition l0 := [0;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BMeFPgT[kjlR".
Definition mp' := mp_from_str "BMmFPoTc[Z\R".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM289.


Module TM290.
Definition tm := TM_from_str "1RB0RA_0RC0RE_1LD---_1LE0LA_1LF0LD_1RA1LE".
Definition tm' := TM_from_str "1RB0RA_1RC0RE_1LD---_1RA1LE_1LD0LF_1LE0LA".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1L_0RS_1RC0RJ_---0Rc_0L_0RA_0RQ0Ra_0RS0Rc_1RQ1Ra_1RS1Rc_0Lh1RJ_---0Lf_1Lh1RA_---1Lf_1Lp---_------_1L_---_0Rc---_0L^---_0L`---_1L^---_1L`---_1RA0RS_1Lf0RJ_1Lh1RS_1LE1RJ_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG_0RC0Lp_1Lp1L__1RC0L__1L_0RS_0Ln0L]_0Lp0L__1Ln1L]_1Lp1L__0RB1RA_0RD1Lf_1RB1Lh_1RD1LE_1RS0Lf_1RJ0Lh_1Rc1Lf_1RA1Lh".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1Lo0RT_1RC0RJ_---0Rc_0Lo0RA_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0Lh1RJ_---0Lf_1Lh1RA_---1Lf_0RC---_1L`---_1RC---_1Lo---_0L^---_0L`---_1L^---_1L`---_0RB1RA_0RD1Lf_1RB1Lh_1RD1LE_1RT0Lf_1RJ0Lh_1Rc1Lf_1RA1Lh_0RC0L`_1L`1Lo_1RC0Lo_1Lo0RT_0L^0Lm_0L`0Lo_1L^1Lm_1L`1Lo_1RA0RT_1Lf0RJ_1Lh1RT_1LE1RJ_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG".
Definition tm1 := TM'_from_str "1LB---_1LC1LD_0LE0LB_1LB0RA_1RF1LI_0RG0RF_0RA0RH_1RJ0LB_1LE1LB_1RG1RF".
Definition tm2 := TM'_from_str "1LB1RK_1LC1LD_0LE0LB_1LB0RA_1RF1LI_0RG0RF_0RA0RH_1RJ0LB_1LE1LB_1RG1RF_1RK1RK".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "S_fEpAJchC".
Definition mp' := mp_from_str "TofE`AJchC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM290.


Module TM291.
Definition tm := TM_from_str "1LB0RE_1RC0LB_0LD1RA_0RA1RE_0RF---_0LA1RD".
Definition tm' := TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0RD---".
Definition tm0 := TM'_from_str "0RD0Ra_1RZ0Rc_1RD1Ra_1LM1Rc_0LN1LM_0LP---_1LN0RZ_1LP---_0RR0Rk_0RT0LO_1RR1Rk_1RT0LM_0LO0LM_1LM0LO_1RZ1LM_1Rc1LO_0RD0RB_0Rk0RD_1RD1RB_1Rk1RD_0L]0LO_0L_1Ri_1L]1LO_1L_---_0RA0Rb_0RC0Rd_1RA1Rb_1RC1Rd_1LM0LO_0Ri---_1Rc1RZ_------_0Ri---_0Rk---_1Ri---_1Rk---_0LN---_0RC---_1LN---_0Rd---_1LM0RZ_0Ri0R\_0LO1RZ_1Ri1R\_0LE1RD_0LG1Rk_1LE1Ra_1LG---".
Definition tm0' := TM'_from_str "0RD0Ri_1Rb0Rk_1RD1Ri_1LM1Rk_0LN1LM_0LP---_1LN0Rb_1LP---_0RR0R[_0RT0LO_1RR1R[_1RT0LM_0LO0LM_1LM0LO_1Rb1LM_1Rk1LO_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0LN0LO_0RC1RY_1LN1LO_0Rl---_1LM0Rb_0RY0Rd_0LO1Rb_1RY1Rd_0LE1RD_0LG1R[_1LE1Ri_1LG---_0RA0Rj_0RC0Rl_1RA1Rj_1RC1Rl_1LM0LO_0RY---_1Rk1Rb_------_0RY---_0R[---_1RY---_1R[---_0LN---_0RC---_1LN---_0Rl---".
Definition tm1 := TM'_from_str "1LB0RD_0LC0LB_1RD1LB_0RE0RI_1RG1RF_0RA---_1LB1RH_1RA---_1RJ---_0LC1RD".
Definition tm2 := TM'_from_str "1LB0RD_0LC0LB_1RD1LB_0RE0RI_1RG1RF_0RA1RK_1LB1RH_1RA1RK_1RJ1RK_0LC1RD_1RK1RK".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "iMOZCaDcdk".
Definition mp' := mp_from_str "YMObCiDkl[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM291.


Module TM292.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA0RE_1RF0RB_1RA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1LD0LC_1LA0RE_1RF0RB_1RA---".
Definition tm0 := TM'_from_str "0RJ0Rd_0RL1RK_1RJ1Rd_1RL1LH_0LW0LF_1Rl0LH_1LW1LF_1RK1LH_1LH0Rb_1L^0Rd_0Rb1Rb_1LU1Rd_0LV1RD_0LX0Rb_1LV---_1LX1Rb_1RK0LH_0RI0L^_1LH1LH_1RI0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RD_0LH1LH_1Rd---_1LH0Rb_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_1RL0L`_---0Rl_1LH1L`_---0RK_0RB---_0RD---_1RB---_1RD---_1LU---_0LH---_1Rd---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Rd_0RL1RK_1RJ1Rd_1RL1LH_0LW0LF_1Rl0LH_1LW1LF_1RK1LH_1LH0Rb_1L^0Rd_0Rb1Rb_1LU1Rd_0LV1RD_0LX0Rb_1LV---_1LX1Rb_1RK0LH_0RI0L^_1LH1LH_1RI0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0Rd0Ra_1RK0Rc_1Rd1Ra_1LH1Rc_0LF0RD_0LH1LH_1LF---_1LH0Rb_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_1RL0L`_---0Rl_1LH1L`_---0RK_0RB---_0RD---_1RB---_1RD---_1LU---_0LH---_1Rd---_1LH---".
Definition tm1 := TM'_from_str "1RB1RH_1RC---_1RD1LG_1LE1RA_0LF0LE_0LG1LG_1RH1LG_0RI1RI_0RB0RH".
Definition tm2 := TM'_from_str "1RB1RH_1RC1RJ_1RD1LG_1LE1RA_0LF0LE_0LG1LG_1RH1LG_0RI1RI_0RB0RH_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;1;1]%N.
Definition mp := mp_from_str "dlDLU^HKb".
Definition mp' := mp_from_str "dlDLU^HKb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM292.


Module TM293.
Definition tm := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_0LC---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0LE1RF_0RD---".
Definition tm0 := TM'_from_str "0RJ0RS_0RL0LG_1RJ1RS_1RL0LE_0LG0LE_0LG0LG_1Rb1LE_1LG1LG_0RQ1Rb_0RS1Rb_1RQ1LE_1RS1LE_0LF0LF_0R[0LH_1LF1LF_0Rl1LH_0LG0Rb_0RQ0Rd_0LG1Rb_1RQ1Rd_0L]1LE_0L_1R[_1L]1RI_1L_---_1Rb0RI_1Rb0RK_1LE1RI_1LE1RK_0LF0LG_0LH0LG_1LF0Rb_1LH1LG_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_0LG1LE_0RQ---_1LG1RI_1Rb---_0LF---_0R[---_0LG---_1R[---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ0RS_0RL0LG_1RJ1RS_1RL0LE_0LG0LE_0LG0LG_1Rb1LE_1LG1LG_0RQ1Rb_0RS1Rb_1RQ1LE_1RS1LE_0LF0LF_0R[0LH_1LF1LF_0Rl1LH_0LG0Rb_0RQ0Rd_0LG1Rb_1RQ1Rd_0L]1LE_0L_1R[_1L]1RI_1L_---_1Rb0RI_1Rb0RK_1LE1RI_1LE1RK_0LF0LG_0LH0LG_1LF0Rb_1LH1LG_0Le0Rj_0R[0Rl_1LE1Rj_1R[1Rl_0Le1LE_0Lg---_1Le1RI_1Lg---_0RY---_0R[---_1RY---_1R[---_0LG---_0RQ---_1LG---_1Rb---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA1RC_1RD---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA1RC_1RD1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "QGb[EIl".
Definition mp' := mp_from_str "QGb[EIl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM293.


Module TM294.
Definition tm := TM_from_str "1LB1RE_0LC0RB_1RD0LA_0RA0RD_0RF0LB_1RD---".
Definition tm' := TM_from_str "1LB1RE_0LC0RB_1RD0LA_0RA0RD_0RF0RA_1RD---".
Definition tm0 := TM'_from_str "1Rb0Rb_0RI0Rd_1LE1Rb_1RI1Rd_0LN1RZ_0LP1LE_1LN---_1LP1Rb_0RC0RI_0LN0RK_1RC1RI_1RZ1RK_0LU1LE_0LW0RC_1LU1Rb_1LW0RI_0RZ0LW_0R\0Rk_1RZ0RC_1R\1Rk_1LE0LE_1RA0LG_1Rb1LE_1RY1LG_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LW1Rb_0Rk0RA_1LW0Rb_0RC0RY_0Ri1LE_0Rk0RC_1Ri0LE_1Rk1RC_0RC0LM_---0LO_0R[1LM_---1LO_0RZ---_0R\---_1RZ---_1R\---_1LE---_1RA---_1Rb---_1RY---".
Definition tm0' := TM'_from_str "1Rb0Rb_0RI0Rd_1LE1Rb_1RI1Rd_0LN1RZ_0LP1LE_1LN---_1LP1Rb_0RC0RI_0LN0RK_1RC1RI_1RZ1RK_0LU1LE_0LW0RC_1LU1Rb_1LW0RI_0RZ0LW_0R\0Rk_1RZ0RC_1R\1Rk_1LE0LE_1RA0LG_1Rb1LE_1RY1LG_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LW1Rb_0Rk0RA_1LW0Rb_0RC0RY_0Ri0RA_0Rk0RC_1Ri1RA_1Rk1RC_0RC0LW_---0Rk_0R[1LW_---0RC_0RZ---_0R\---_1RZ---_1R\---_1LE---_1RA---_1Rb---_1RY---".
Definition tm1 := TM'_from_str "0RB0RD_1RC---_0RD0RH_1LE1RA_0LF1RC_0LG0RD_1RA1LE_1RJ1RI_0RJ0RI_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RD_1RC1RK_0RD0RH_1LE1RA_0LF1RC_0LG0RD_1RA1LE_1RJ1RI_0RJ0RI_1RA0RA_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "bkZCENW[YA".
Definition mp' := mp_from_str "bkZCENW[YA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM294.


Module TM295.
Definition tm := TM_from_str "1LB1RE_0LC0RB_1RD0LA_0RA0RD_0RF0RA_1RD---".
Definition tm' := TM_from_str "1LB1RE_0LC0RE_1RD0LA_0RA0RD_0RF0LE_1RD---".
Definition tm0 := TM'_from_str "1Rb0Rb_0RI0Rd_1LE1Rb_1RI1Rd_0LN1RZ_0LP1LE_1LN---_1LP1Rb_0RC0RI_0LN0RK_1RC1RI_1RZ1RK_0LU1LE_0LW0RC_1LU1Rb_1LW0RI_0RZ0LW_0R\0Rk_1RZ0RC_1R\1Rk_1LE0LE_1RA0LG_1Rb1LE_1RY1LG_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LW1Rb_0Rk0RA_1LW0Rb_0RC0RY_0Ri0RA_0Rk0RC_1Ri1RA_1Rk1RC_0RC0LW_---0Rk_0R[1LW_---0RC_0RZ---_0R\---_1RZ---_1R\---_1LE---_1RA---_1Rb---_1RY---".
Definition tm0' := TM'_from_str "1Rb0Rb_0RZ0Rd_1LE1Rb_1RZ1Rd_0LN1RZ_0LP0Le_1LN---_1LP1Le_0RC0Ra_0LN0Rc_1RC1Ra_1RZ1Rc_0LU0RZ_0LW0RC_1LU---_1LW0R[_0RZ0LW_0R\0Rk_1RZ0RC_1R\1Rk_1LE0LE_1RA0LG_1Rb1LE_1RY1LG_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LW1Rb_0Rk0RA_1LW0Rb_0RC0RY_0Ri0RZ_0Rk0RC_1Ri1RZ_1Rk0Le_0RC0Le_---0Lg_0R[1Le_---1Lg_0RZ---_0R\---_1RZ---_1R\---_1LE---_1RA---_1Rb---_1RY---".
Definition tm1 := TM'_from_str "0RB0RD_1RC---_0RD0RH_1LE1RA_0LF1RC_0LG0RD_1RA1LE_1RJ1RI_0RJ0RI_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RD_1RC1RK_0RD0RH_1LE1RA_0LF1RC_0LG0RD_1RA1LE_1RJ1RI_0RJ0RI_1RA0RA_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "bkZCENW[YA".
Definition mp' := mp_from_str "bkZCENW[YA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM295.


Module TM296.
Definition tm := TM_from_str "1LB1RE_0LC0RE_1RD0LA_0RA0RD_0RF0LE_1RD---".
Definition tm' := TM_from_str "1LB1RE_0LC0RB_1RD0LA_0RA0RD_0RF0LE_1RD---".
Definition tm0 := TM'_from_str "1Rb0Rb_0RZ0Rd_1LE1Rb_1RZ1Rd_0LN1RZ_0LP0Le_1LN---_1LP1Le_0RC0Ra_0LN0Rc_1RC1Ra_1RZ1Rc_0LU0RZ_0LW0RC_1LU---_1LW0R[_0RZ0LW_0R\0Rk_1RZ0RC_1R\1Rk_1LE0LE_1RA0LG_1Rb1LE_1RY1LG_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LW1Rb_0Rk0RA_1LW0Rb_0RC0RY_0Ri0RZ_0Rk0RC_1Ri1RZ_1Rk0Le_0RC0Le_---0Lg_0R[1Le_---1Lg_0RZ---_0R\---_1RZ---_1R\---_1LE---_1RA---_1Rb---_1RY---".
Definition tm0' := TM'_from_str "1Rb0Rb_0RI0Rd_1LE1Rb_1RI1Rd_0LN1RZ_0LP0Le_1LN---_1LP1Le_0RC0RI_0LN0RK_1RC1RI_1RZ1RK_0LU1LE_0LW0RC_1LU1Rb_1LW0RI_0RZ0LW_0R\0Rk_1RZ0RC_1R\1Rk_1LE0LE_1RA0LG_1Rb1LE_1RY1LG_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LW1Rb_0Rk0RA_1LW0Rb_0RC0RY_0Ri0RZ_0Rk0RC_1Ri1RZ_1Rk0Le_0RC0Le_---0Lg_0R[1Le_---1Lg_0RZ---_0R\---_1RZ---_1R\---_1LE---_1RA---_1Rb---_1RY---".
Definition tm1 := TM'_from_str "0RB0RD_1RC---_0RD0RH_1LE1RA_0LF1RC_0LG0RD_1RA1LE_1RJ1RI_0RJ0RI_1RA0RA".
Definition tm2 := TM'_from_str "0RB0RD_1RC1RK_0RD0RH_1LE1RA_0LF1RC_0LG0RD_1RA1LE_1RJ1RI_0RJ0RI_1RA0RA_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "bkZCENW[YA".
Definition mp' := mp_from_str "bkZCENW[YA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM296.


Module TM297.
Definition tm := TM_from_str "1LB---_0LC1LC_1RD0LD_0RE0RF_1LA1RD_1LB1RE".
Definition tm' := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA0RB_---1RD".
Definition tm0 := TM'_from_str "1RZ---_1Rb---_1L]---_1L_---_0LN---_0LP---_1LN---_1LP---_0Rc0Rk_0LP1LP_1Rc1Rk_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RZ_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RZ1L]_1Rb1L__0Ra0Ri_0Rc0Rk_1Ra1Ri_1Rc1Rk_0LP0LW_0Rc---_1LP1LW_0Rk0R\_1LW0RZ_---0R\_1LX1RZ_---1R\_0LF1LX_0LH1L]_1LF1RZ_1LH1Rb_1RZ0Rb_1Rb0Rd_1L]1Rb_1L_1Rd_0LN---_0LP1Rc_1LN---_1LP1Rk".
Definition tm0' := TM'_from_str "1RI0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RI_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RI1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0R\_1LW0RI_0R\0RK_1LX1RI_1R\1RK_0LF1LX_0LH1L]_1LF1RI_1LH1Rj_---0RZ_---0R\_---1RZ_---1R\_---1LX_---1L]_---1RI_---1Rj".
Definition tm1 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_---0RH_1RE1RA_1LJ1LC_1LC1LF".
Definition tm2 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_1RK0RH_1RE1RA_1LJ1LC_1LC1LF_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "k]WZcXb\_P".
Definition mp' := mp_from_str "C]WIcXj\_P".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM297.


Module TM298.
Definition tm := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA0RB_---1RD".
Definition tm' := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA1RD_---1RD".
Definition tm0 := TM'_from_str "1RI0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RI_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RI1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0R\_1LW0RI_0R\0RK_1LX1RI_1R\1RK_0LF1LX_0LH1L]_1LF1RI_1LH1Rj_---0RZ_---0R\_---1RZ_---1R\_---1LX_---1L]_---1RI_---1Rj".
Definition tm0' := TM'_from_str "1RZ0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RZ_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RZ1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0R\_1LW0RZ_0R\0R\_1LX1RZ_1R\1R\_0LF1LX_0LH1L]_1LF1RZ_1LH1Rj_---0RZ_---0R\_---1RZ_---1R\_---1LX_---1L]_---1RZ_---1Rj".
Definition tm1 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_---0RH_1RE1RA_1LJ1LC_1LC1LF".
Definition tm2 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_1RK0RH_1RE1RA_1LJ1LC_1LC1LF_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "C]WIcXj\_P".
Definition mp' := mp_from_str "C]WZcXj\_P".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM298.


Module TM299.
Definition tm := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA1RD_---1RD".
Definition tm' := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA0RB_---0RB".
Definition tm0 := TM'_from_str "1RZ0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RZ_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RZ1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0R\_1LW0RZ_0R\0R\_1LX1RZ_1R\1R\_0LF1LX_0LH1L]_1LF1RZ_1LH1Rj_---0RZ_---0R\_---1RZ_---1R\_---1LX_---1L]_---1RZ_---1Rj".
Definition tm0' := TM'_from_str "1RI0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RI_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RI1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0RK_1LW0RI_0RK0RK_1LX1RI_1RK1RK_0LF1LX_0LH1L]_1LF1RI_1LH1Rj_---0RI_---0RK_---1RI_---1RK_---1LX_---1L]_---1RI_---1Rj".
Definition tm1 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_---0RH_1RE1RA_1LJ1LC_1LC1LF".
Definition tm2 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_1RK0RH_1RE1RA_1LJ1LC_1LC1LF_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "C]WZcXj\_P".
Definition mp' := mp_from_str "C]WIcXjK_P".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM299.


Module TM300.
Definition tm := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA0RB_---0RB".
Definition tm' := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA1RD_---0RB".
Definition tm0 := TM'_from_str "1RI0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RI_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RI1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0RK_1LW0RI_0RK0RK_1LX1RI_1RK1RK_0LF1LX_0LH1L]_1LF1RI_1LH1Rj_---0RI_---0RK_---1RI_---1RK_---1LX_---1L]_---1RI_---1Rj".
Definition tm0' := TM'_from_str "1RZ0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RZ_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RZ1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0RK_1LW0RZ_0RK0R\_1LX1RZ_1RK1R\_0LF1LX_0LH1L]_1LF1RZ_1LH1Rj_---0RI_---0RK_---1RI_---1RK_---1LX_---1L]_---1RZ_---1Rj".
Definition tm1 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_---0RH_1RE1RA_1LJ1LC_1LC1LF".
Definition tm2 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_1RK0RH_1RE1RA_1LJ1LC_1LC1LF_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "C]WIcXjK_P".
Definition mp' := mp_from_str "C]WZcXjK_P".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM300.


Module TM301.
Definition tm := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA1RD_---0RB".
Definition tm' := TM_from_str "1LB1RE_0LC1LC_1RD0LD_0RE0RA_1LF0RB_1LB---".
Definition tm0 := TM'_from_str "1RZ0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RZ_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RZ1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0RK_1LW0RZ_0RK0R\_1LX1RZ_1RK1R\_0LF1LX_0LH1L]_1LF1RZ_1LH1Rj_---0RI_---0RK_---1RI_---1RK_---1LX_---1L]_---1RZ_---1Rj".
Definition tm0' := TM'_from_str "1RI0Rb_1Rb0Rd_1L]1Rb_1L_1Rd_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RI_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RI1L]_1Rb1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0RK_1LW0RI_---0RK_1LX1RI_---1RK_0Ln1LX_0Lp1L]_1Ln1RI_1Lp1Rb_1RI---_1Rb---_1L]---_1L_---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_---0RH_1RE1RA_1LJ1LC_1LC1LF".
Definition tm2 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_1RK0RH_1RE1RA_1LJ1LC_1LC1LF_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "C]WZcXjK_P".
Definition mp' := mp_from_str "C]WIcXbK_P".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM301.


Module TM302.
Definition tm := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA1RD_1LD0RF".
Definition tm' := TM_from_str "1LB0LD_0LC1LF_1RD---_0RE1RE_1LA1RD_1LD0RF".
Definition tm0 := TM'_from_str "1RZ1LW_1L`1LP_---1Lp_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_1Lp---_1LH---_1RZ---_1R\---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1LH1R\_0LF1Lp_0LH1LH_1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0L^0Rc_0L`0RZ_1L^0Rd_1L`0Ri".
Definition tm0' := TM'_from_str "1RZ1LW_1L`1LP_---1Lp_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_1Lp---_1L_---_1RZ---_1R\---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1L_1R\_0LF1Lp_0LH1L__1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0L^0Rc_0L`0RZ_1L^0Rd_1L`0Ri".
Definition tm1 := TM'_from_str "1LB1RD_1LE0RC_0RD0RC_0RA0RF_0RF1RF_1LH1RG_1RA1RF_1LI1LH_1LJ1LB_1RD---".
Definition tm2 := TM'_from_str "1LB1RD_1LE0RC_0RD0RC_0RA0RF_0RF1RF_1LH1RG_1RA1RF_1LI1LH_1LJ1LB_1RD1RK_1RK1RK".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "cpiZ`d\HPW".
Definition mp' := mp_from_str "cpiZ`d\_PW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM302.


Module TM303.
Definition tm := TM_from_str "1LB0RC_1RC0LD_1RF1RA_1RB1LE_1LB1RE_---0RE".
Definition tm' := TM_from_str "1LB1RA_1RC0LE_1RF1RD_0LA0RC_1RB1LA_---0RA".
Definition tm0 := TM'_from_str "0RD0RQ_1RD0RS_1RD1RQ_1Lf1RS_0LN---_0LP1RD_1LN0Rc_1LP0RS_0RR0RT_0RT0LP_1RR1RT_1RT1Lf_---0L]_1Lf0L__1Rc1L]_1RS1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_---0L__1RD1Rj_---1L__1Rb1RB_0RJ1RS_0RL0Rd_1RJ1L__1RL1Rd_1Rl0Lf_0Lf0Lh_1RD1Lf_1Lf1Lh_0RD0Rb_1RD0Rd_1RD1Rb_1Lf1Rd_0LN0L__0LP1Lf_1LN1L__1LP1Rd_---0Ra_---0Rc_---1Ra_---1Rc_---1Lf_---1RD_---1RS_---0Rd".
Definition tm0' := TM'_from_str "0R\0RB_1R\0RD_1R\1RB_1LF1RD_0LN0Lg_0LP1LF_1LN1Lg_1LP1RD_0RR0RT_0RT0LP_1RR1RT_1RT1LF_---0Le_1LF0Lg_1RC1Le_1RS1Lg_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_---0Lg_1R\1Rj_---1Lg_1RB1RZ_1LF0RQ_1R\0RS_0Lg1RQ_1LF1RS_0LE---_0LG1R\_1LE0RC_1LG0RS_0RJ1RS_0RL0RD_1RJ1Lg_1RL1RD_1Rl0LF_0LF0LH_1R\1LF_1LF1LH_---0RA_---0RC_---1RA_---1RC_---1LF_---1R\_---1RS_---0RD".
Definition tm1 := TM'_from_str "1LB1RE_0LC1LB_1RE1LD_1RA1LB_1RF1RI_---0RG_1RA1RH_1RA0RJ_1RA0RE_1LB1RJ".
Definition tm2 := TM'_from_str "1LB1RE_0LC1LB_1RE1LD_1RA1LB_1RF1RI_1RK0RG_1RA1RH_1RA0RJ_1RA0RE_1LB1RJ_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "DfP_SjcbBd".
Definition mp' := mp_from_str "\FPgSjCBZD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM303.


Module TM304.
Definition tm := TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC".
Definition tm' := TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0RB_---0LC".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LX---_1RD0LF_1LX---_1Rd1LF_1Rd0RZ_1LH0R\_1LF1RZ_1LX1R\_0LV1RL_0LX1RK_1LV1Rk_1LX1RK_0R\1Rd_1RD1LH_1R\1LF_0LF1LX_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_1LX1LF_---1LF_1R\1RZ_0LF1RZ_0RI0RL_0RK0RK_1RI1RL_1RK1RK_0LH0L]_0RD0L__1LH1L]_0Rd1L__---1RD_---0LH_---0LF_---0LX_---0LU_---0LW_---1LU_---1LW".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LX---_1RD0LF_1LX---_1Rd1LF_1Rd0RZ_1LH0R\_1LF1RZ_1LX1R\_0LV1RL_0LX1RK_1LV1Rk_1LX1RK_0R\1Rd_1RD1LH_1R\1LF_0LF1LX_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_1LX1LF_---1LF_1R\1RZ_0LF1RZ_0RI0RI_0RK0RK_1RI1RI_1RK1RK_0LH0LH_0RD0RD_1LH1LH_0Rd0Rd_---1RD_---0LH_---0LF_---0LX_---0LU_---0LW_---1LU_---1LW".
Definition tm1 := TM'_from_str "1LB1RF_1LC1LB_1RG1LD_1RE0LD_1RA1RJ_1RE1RG_1RH1RH_1LD1RI_0RE0RG_---0LD".
Definition tm2 := TM'_from_str "1LB1RF_1LC1LB_1RG1LD_1RE0LD_1RA1RJ_1RE1RG_1RH1RH_1LD1RI_0RE0RG_1RK0LD_1RK1RK".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "LXHFD\dKZk".
Definition mp' := mp_from_str "LXHFD\dKZk".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM304.


Module TM305.
Definition tm := TM_from_str "1LB1RF_1RC1LB_1RE1RD_1RB0LD_1RF---_1RA0RA".
Definition tm' := TM_from_str "1LB1RF_1RC1LB_0RE1RD_1RB0LD_1LF---_1RA0RA".
Definition tm0 := TM'_from_str "0R\0Rj_0L]0Rl_1R\1Rj_1LP1Rl_0LN1LP_0LP1R\_1LN1Rl_1LP1Rj_0RR0R\_0RT0L]_1RR1R\_1RT1LP_1Rl0LN_1RL0LP_---1LN_0L]1LP_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_1RD1RT_---0L]_1RC1LP_---1L]_0RJ0RT_0RL1Rd_1RJ1RT_1RL0L]_1Rd0L]_0LP0L__1R\1L]_1LP1L__0Rj---_0Rl---_1Rj---_1Rl---_1LP---_1R\---_1Rl---_1Rj---_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0LP1RL_1RD0RD_1LP0L]_1RC0RC".
Definition tm0' := TM'_from_str "0R\0Rj_0L]0Rl_1R\1Rj_1LP1Rl_0LN1LP_0LP1R\_1LN1Rl_1LP1Rj_0RR0R\_0RT0L]_1RR1R\_1RT1LP_1Rl0LN_1RL0LP_---1LN_0L]1LP_0Ra0RZ_0Rc0R\_1Ra1RZ_1Rc1R\_1RD1RT_---0L]_1RC1LP_---1L]_0RJ0RT_0RL1Rc_1RJ1RT_1RL0L]_1Rc0L]_0LP0L__1R\1L]_1LP1L__0Rl---_0Rj---_1Rl---_1Rj---_0Ln---_0Lp---_1Ln---_1Lp---_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0LP1RL_1RD0RD_1LP0L]_1RC0RC".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RF_0LD1LC_1RE0LD_1RF---_1RB1RG_1RH1RA_1RI0LD_1RJ1LC_1RE1RH".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RF_0LD1LC_1RE0LD_1RF1RK_1RB1RG_1RH1RA_1RI0LD_1RJ1LC_1RE1RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "jDP]dlC\LT".
Definition mp' := mp_from_str "jDP]clC\LT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM305.


Module TM306.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_0LD---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_1RB0RF_1RD0RB_1RA1LC".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW0RL_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Ri0RD_1R\1LH_1LH0RK_0Ri1RK_0Rk1LF_1Ri1LH_1Rk1LU_1LU0LV_---0LX_1R\1LV_---1LX_0RL---_1RK---_1RL---_1LH---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1R\---_1LW---_1RK---_1RK0Rb_1L^0Rd_1L`1Rb_1LU1Rd_0LV1RL_0LX1L`_1LV1Rk_1LX1Rb_0Rd1R\_1RK0L^_1Rd0L`_1L`0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW0RL_1R\0L`_1LW---_1RK1L`_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1LU0L`_1RB0R\_1Rd1L`_1L`0RK_0RB1RK_0RD1L^_1RB1L`_1RD1LU_1LU0LV_---0LX_1Rd1LV_---1LX".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_0RA---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_0RA1RK_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "LUFHKZD\ci".
Definition mp' := mp_from_str "LU^`Kb\dkB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM306.


Module TM307.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RE0LE_1RA1LD_1RB---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1L^_1RD---_1LW0Rd_1L^---_1Lg0Rb_1L^0Rd_1Lg1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1Rk_1LX1Lg_1Rd0Lg_1Rd0L^_1L^0Lg_1L^0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0Rb0RL_0Rd0Lg_1Rb1RL_1Rd0Lg_1RL0Le_0Lg0Lg_1Rk1Le_1Lg1Lg_0RB1Rd_0RD1Rd_1RB1L^_1RD1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ---_0RL---_1RJ---_1RL---_0LW---_1RD---_1LW---_1L^---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1L^_1RD---_1LW0Rd_1L^---_1Lg0Rb_1L^0Rd_1Lg1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1Rk_1LX1Lg_1Rd0Lg_1Rd0L^_1L^0Lg_1L^0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RL0Ra_0Lg0Rc_1RL1Ra_0Lg1Rc_0Le0RL_0Lg0Lg_1Le0Rk_1Lg1Lg_0RB1Rd_0RD1Rd_1RB1L^_1RD1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ---_0RL---_1RJ---_1RL---_0LW---_1RD---_1LW---_1L^---".
Definition tm1 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA---_1LH1RD_0LB0LH".
Definition tm2 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA1RI_1LH1RD_0LB0LH_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "J^gdDkLU".
Definition mp' := mp_from_str "J^gdDkLU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM307.


Module TM308.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1L^_1RD---_1LW0Rd_1L^---_1Lg0Rb_1L^0Rd_1Lg1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1Rk_1LX1Lg_1Rd0Lg_1Rd0L^_1L^0Lg_1L^0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RL0Ra_0Lg0Rc_1RL1Ra_0Lg1Rc_0Le0RL_0Lg0Lg_1Le0Rk_1Lg1Lg_0RB1Rd_0RD1Rd_1RB1L^_1RD1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ---_0RL---_1RJ---_1RL---_0LW---_1RD---_1LW---_1L^---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1Rl---_1LW---_1L^---_1Lg0Rb_1L^0Rd_1Lg1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1RC_1LX1Lg_1Rd0Lg_1Rd0L^_1L^0Lg_1L^0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RL0RL_0Lg0Lg_1RL1RL_0Lg0Lg_0Le0Le_0Lg0Lg_1Le1Le_1Lg1Lg_0Rj1Rd_0Rl1Rd_1Rj1L^_1Rl1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LW1L^_1Rl---_1LW0Rd_1L^---".
Definition tm1 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA---_1LH1RD_0LB0LH".
Definition tm2 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA1RI_1LH1RD_0LB0LH_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "J^gdDkLU".
Definition mp' := mp_from_str "J^gdlCLU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM308.


Module TM309.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm' := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1Rl---_1LW---_1L^---_1Lg0Rb_1L^0Rd_1Lg1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1RC_1LX1Lg_1Rd0Lg_1Rd0L^_1L^0Lg_1L^0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RL0RL_0Lg0Lg_1RL1RL_0Lg0Lg_0Le0Le_0Lg0Lg_1Le1Le_1Lg1Lg_0Rj1Rd_0Rl1Rd_1Rj1L^_1Rl1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LW1L^_1Rl---_1LW0Rd_1L^---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1Rl---_1LW---_1L^---_0Lg0Rb_1L^0Rd_0Lg1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1RC_1LX1Lg_0RZ0Lg_0R\0L^_1RZ0Lg_1R\0LU_0L^0LU_0L^0LW_1L^1LU_1L^1LW_0RL0RL_0Lg0Lg_1RL1RL_0Lg0Lg_0Le0Le_0Lg0Lg_1Le1Le_1Lg1Lg_0Rj1Rd_0Rl1Rd_1Rj1L^_1Rl1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LW1L^_1Rl---_1LW0Rd_1L^---".
Definition tm1 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA---_1LH1RD_0LB0LH".
Definition tm2 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA1RI_1LH1RD_0LB0LH_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "J^gdlCLU".
Definition mp' := mp_from_str "J^gdlCLU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM309.


Module TM310.
Definition tm := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm' := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0RE_1RF1LD_1RB0RA".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1Rl---_1LW---_1L^---_0Lg0Rb_1L^0Rd_0Lg1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1RC_1LX1Lg_0RZ0Lg_0R\0L^_1RZ0Lg_1R\0LU_0L^0LU_0L^0LW_1L^1LU_1L^1LW_0RL0RL_0Lg0Lg_1RL1RL_0Lg0Lg_0Le0Le_0Lg0Lg_1Le1Le_1Lg1Lg_0Rj1Rd_0Rl1Rd_1Rj1L^_1Rl1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LW1L^_1Rl---_1LW0Rd_1L^---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1Rl---_1LW---_1L^---_0Rc0Rb_1L^0Rd_1Rc1Rb_1LU1Rd_0LV1RL_0LX0Lg_1LV1RC_1LX1Lg_0RZ0Lg_0R\0L^_1RZ0Lg_1R\0LU_0L^0LU_1Rj0LW_1L^1LU_1L^1LW_0RL0Ra_0Lg0Rc_1RL1Ra_0Lg1Rc_0Le0RL_0Lg0Lg_1Le0RC_1Lg1Lg_0Rj1Rd_0Rl1Rd_1Rj1L^_1Rl1L^_1LU0L^_1RJ0L`_1Rd1L^_---1L`_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LW1L^_1Rl---_1LW0Rd_1L^---".
Definition tm1 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA---_1LH1RD_0LB0LH".
Definition tm2 := TM'_from_str "1LB0RD_0LC0LC_1RD1LB_1RE1LB_1RG1RF_1RA1RI_1LH1RD_0LB0LH_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "J^gdlCLU".
Definition mp' := mp_from_str "J^gdlCLU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM310.


Module TM311.
Definition tm := TM_from_str "1LB1RF_1LC1LD_1RB0LF_---1LE_1RA0LB_1RE0RA".
Definition tm' := TM_from_str "1LB1RE_1LC1LF_1LD0LE_1RA0LB_1RD0RA_---1LD".
Definition tm0 := TM'_from_str "1Lh0Rj_---0Rl_1Lo1Rj_1Lh1Rl_0LN1RD_0LP1Lo_1LN0Lh_1LP1Rj_1RC---_1Rl1RC_1LO---_1LX1LO_0LV0L^_0LX0L`_1LV1L^_1LX1L`_0RJ0RD_0RL1Lh_1RJ1RD_1RL1Lo_0Lo0Lm_0Lh0Lo_1Lo1Lm_1Lh1Lo_---0Rl_---1LV_---1Rl_---1L^_---0Lf_---0Lh_---1Lf_---1Lh_0RB0Lh_0RD---_1RB0Lo_1RD0Lh_0L`0LM_1Rd0LO_1L`1LM_1RC1LO_0Rb0RA_0Rd0RC_1Rb1RA_1Rd1RC_1Lh0LX_0L^0Rd_1Rl1LX_1L^0RC".
Definition tm0' := TM'_from_str "1L`0Rb_---0Rd_1Lg1Rb_1L`1Rd_0LN1RD_0LP1Lg_1LN0L`_1LP1Rb_1RC---_1Rd1RC_1LO---_1LX1LO_0LV0Ln_0LX0Lp_1LV1Ln_1LX1Lp_0Rd0RD_1LV1L`_1Rd1RD_1Ln1Lg_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RB0L`_0RD---_1RB0Lg_1RD0L`_0Lp0LM_1R\0LO_1Lp1LM_1RC1LO_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1L`0LX_0Ln0R\_1Rd1LX_1Ln0RC_---0Rd_---1LV_---1Rd_---1Ln_---0L^_---0L`_---1L^_---1L`".
Definition tm1 := TM'_from_str "1RB0LC_1LC1RG_1RI1LD_1LE1LH_0LC0LF_1RG1LJ_1RA1RI_---0LC_1LF1RK_1LC1LF_0RA0RI".
Definition tm2 := TM'_from_str "1RB0LC_1LC1RG_1RI1LD_1LE1LH_0LC0LF_1RG1LJ_1RA1RI_1RL0LC_1LF1RK_1LC1LF_0RA0RI_1RL1RL".
Definition l0 := [1;1;1;1;1;0;1;0]%N.
Definition mp := mp_from_str "dDhOVol^CXj".
Definition mp' := mp_from_str "\D`OVgdnCXb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM311.


Module TM312.
Definition tm := TM_from_str "1RB1LF_1LC1RA_1RD0RC_1LE0RC_0RA0LD_0LE---".
Definition tm' := TM_from_str "1RB1LF_1LC1RA_1LE0RD_1RC0RD_0RA0LC_0LE---".
Definition tm0 := TM'_from_str "0RJ0RD_0RL---_1RJ1L]_1RL---_0RZ0Ln_1RL0Lp_0RQ1Ln_---1Lp_0RS0RB_0RQ0RD_1RS1RB_1RQ1RD_0LV1RQ_0LX---_1LV1RD_1LX---_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0L_1Lf_1RZ0RZ_1L_0RS_1RQ0RQ_0RD0RQ_1Lf0RS_1L]1RQ_0RS1RS_0Lf1Lf_0Lh0RZ_1Lf0RS_1Lh0RQ_0RA0Lg_0RC0RZ_1RA0L__1RC1RZ_0RQ0L]_0Lg0L__0RD1L]_1Lg1L__0RJ---_0Lf---_1RJ---_1Lf---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0RD_0RL---_1RJ1LU_1RL---_0RR0Ln_1RL0Lp_0RY1Ln_---1Lp_1Lg0RB_0RY0RD_1LW1RB_1RY1RD_0LV1RY_0LX---_1LV1RD_1LX---_0RD0RY_1Lf0R[_1LU1RY_0R[1R[_0Lf1Lf_0Lh0RR_1Lf0R[_1Lh0RY_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LW1Lf_1RR0RR_1LW0R[_1RY0RY_0RA0Lg_0RC0RR_1RA0LW_1RC1RR_0RY0LU_0Lg0LW_0RD1LU_1Lg1LW_0RJ---_0Lf---_1RJ---_1Lf---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1RB1RI_1LC0RA_0LE0LD_1LC0RA_0RG1LF_0LC1LC_1RH---_1RI1RG_0RB0RI".
Definition tm2 := TM'_from_str "1RB1RI_1LC0RA_0LE0LD_1LC0RA_0RG1LF_0LC1LC_1RH1RJ_1RI1RG_0RB0RI_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;0]%N.
Definition mp := mp_from_str "SZf_g]DLQ".
Definition mp' := mp_from_str "[RfWgUDLY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM312.


Module TM313.
Definition tm := TM_from_str "1RB1LF_1LC1RA_1LE0RD_1RC0RD_0RA0LC_0LE---".
Definition tm' := TM_from_str "1RB---_1LC1RA_1LE0RD_1RC0RD_0LF0LC_0RA0LC".
Definition tm0 := TM'_from_str "0RJ0RD_0RL---_1RJ1LU_1RL---_0RR0Ln_1RL0Lp_0RY1Ln_---1Lp_1Lg0RB_0RY0RD_1LW1RB_1RY1RD_0LV1RY_0LX---_1LV1RD_1LX---_0RD0RY_1Lf0R[_1LU1RY_0R[1R[_0Lf1Lf_0Lh0RR_1Lf0R[_1Lh0RY_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LW1Lf_1RR0RR_1LW0R[_1RY0RY_0RA0Lg_0RC0RR_1RA0LW_1RC1RR_0RY0LU_0Lg0LW_0RD1LU_1Lg1LW_0RJ---_0Lf---_1RJ---_1Lf---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0RR---_1RL---_0RY---_------_1Lo0RB_0RY0RD_1LW1RB_1RY1RD_0LV1RY_0LX---_1LV1RD_1LX---_0RD0RY_1Lf0R[_1LU1RY_0R[1R[_0Lf1Lf_0Lh0RR_1Lf0R[_1Lh0RY_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LW1Lf_1RR0RR_1LW0R[_1RY0RY_0RJ0Lo_0Lf0RR_1RJ0LW_1Lf1RR_0Lm0LU_0Lo0LW_1Lm1LU_1Lo1LW_0RA0Lo_0RC0RR_1RA0LW_1RC1RR_0RY0LU_---0LW_0RD1LU_---1LW".
Definition tm1 := TM'_from_str "1RB1RI_1LC0RA_0LE0LD_1LC0RA_0RG1LF_0LC1LC_1RH---_1RI1RG_0RB0RI".
Definition tm2 := TM'_from_str "1RB1RI_1LC0RA_0LE0LD_1LC0RA_0RG1LF_0LC1LC_1RH1RJ_1RI1RG_0RB0RI_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;0]%N.
Definition mp := mp_from_str "[RfWgUDLY".
Definition mp' := mp_from_str "[RfWoUDLY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM313.


Module TM314.
Definition tm := TM_from_str "1LB1LA_0LC1LF_1LD---_0RE1RE_1LA1RD_1RD0RF".
Definition tm' := TM_from_str "1LB0LD_0LC1LF_1LD---_0RE1RE_1LA1RD_1RD0RF".
Definition tm0 := TM'_from_str "1L^1LW_1R\1LP_---1Lp_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_0L^---_0L`---_1L^---_1L`---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1LH1R\_0LF1Lp_0LH1LH_1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lp0Rc_1LH0RZ_1RZ0Rd_1R\0Ri".
Definition tm0' := TM'_from_str "1L^1LW_1R\1LP_---1Lp_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_0L^---_0L`---_1L^---_1L`---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1L_1R\_0LF1Lp_0LH1L__1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1Lp0Rc_1L_0RZ_1RZ0Rd_1R\0Ri".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RE_1RA0RD_0RE0RD_0RB0RF_1LG1RA_1LH1LG_1LI1LC_1LJ---_0RB1RB".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RE_1RA0RD_0RE0RD_0RB0RF_1LG1RA_1LH1LG_1LI1LC_1LJ1RK_0RB1RB_1RK1RK".
Definition l0 := [0;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "\cpiZdHPW^".
Definition mp' := mp_from_str "\cpiZd_PW^".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM314.


Module TM315.
Definition tm := TM_from_str "1LB0RB_0RC0LF_1RA1RD_0LD1RE_0RB---_1LA0LF".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB0RF_1LA0LE_1LC---".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS0Lm_1LF0Lm_0RK0Lo_0RK1Lm_0Rd1Lo_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lo1RQ_1RQ1RK_1Lo0LF_0LF---_0L]0Rb_0RK0Rd_1RQ1Rb_1RK1Rd_0L]1RQ_0L_---_1L]0LF_1L_---_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RZ---_1LF---_0Rd0LP_0LP0LF_1Lo0LF_0LF0Lm_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Le1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS0Le_1LF0Le_0RK0Lg_0RK1Le_0Rk1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Ri_0RK0Rk_1RI1Ri_1RK1Rk_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rk0LP_0LP0LF_1Lg0LF_0LF0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RK---_0Rk---_1RK---_1Rk---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD0LG_1RA---_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD0LG_1RA1RJ_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPomdZ".
Definition mp' := mp_from_str "KQBFPgekZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM315.


Module TM316.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB0RF_1LA0LE_1LC---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA0LE_0LC---".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Le1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS0Le_1LF0Le_0RK0Lg_0RK1Le_0Rk1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Ri_0RK0Rk_1RI1Ri_1RK1Rk_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rk0LP_0LP0LF_1Lg0LF_0LF0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RK---_0Rk---_1RK---_1Rk---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Le1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS0Le_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP0LF_1Lg0LF_0LF0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1LF---_0RK---_1Le---_1RK---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD0LG_1RA---_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD0LG_1RA1RJ_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgekZ".
Definition mp' := mp_from_str "KQBFPgelZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM316.


Module TM317.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA0LE_0LC---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA0LE_0RB---".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Le1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS0Le_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP0LF_1Lg0LF_0LF0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1LF---_0RK---_1Le---_1RK---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Le1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS0Le_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP0LF_1Lg0LF_0LF0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RZ---_1LF---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD0LG_1RA---_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD0LG_1RA1RJ_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgelZ".
Definition mp' := mp_from_str "KQBFPgelZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM317.


Module TM318.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA0LF_1RE---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA0LF_1LA---".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0R\1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF1R\_0RI0RZ_0RK0R\_1RI1RZ_1RK1R\_0RB1RQ_0LF1RK_0RZ0LF_1LF1R\_0R\0LP_0LP---_1Lg0LF_0LF---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0LF---_------_1LF---".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0R\1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF1R\_0RI0RZ_0RK0R\_1RI1RZ_1RK1R\_0RB1RQ_0LF1RK_0RZ0LF_1LF1R\_0R\0LP_0LP---_1Lg0LF_0LF---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0R\---_0LP---_1Lg---_0LF---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA1RH_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RH_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgm\Z".
Definition mp' := mp_from_str "KQBFPgm\Z".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM318.


Module TM319.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA0LF_1LA---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1LA---".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0R\1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF1R\_0RI0RZ_0RK0R\_1RI1RZ_1RK1R\_0RB1RQ_0LF1RK_0RZ0LF_1LF1R\_0R\0LP_0LP---_1Lg0LF_0LF---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0R\---_0LP---_1Lg---_0LF---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RR0RI_1LF0RK_1RR1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RR_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0RT1Lg_0RB0RR_0RK0RT_1RB1RR_1RK1RT_0L^1RQ_0L`1RK_1L^0LF_1L`1RT_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0RY0Lg_1LF1RQ_0RB1Lg_0RK0LF_0RT0LP_0LP---_1Lg0LF_0LF---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0RT---_0LP---_1Lg---_0LF---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA1RH_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RH_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgm\Z".
Definition mp' := mp_from_str "KQBFPgmTR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM319.


Module TM320.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1LA---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1RE---".
Definition tm0 := TM'_from_str "0RR0RI_1LF0RK_1RR1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RR_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0RT1Lg_0RB0RR_0RK0RT_1RB1RR_1RK1RT_0L^1RQ_0L`1RK_1L^0LF_1L`1RT_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0RY0Lg_1LF1RQ_0RB1Lg_0RK0LF_0RT0LP_0LP---_1Lg0LF_0LF---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0RT---_0LP---_1Lg---_0LF---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RR0RI_1LF0RK_1RR1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RR_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0RT1Lg_0RB0RR_0RK0RT_1RB1RR_1RK1RT_0L^1RQ_0L`1RK_1L^0LF_1L`1RT_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0RY0Lg_1LF1RQ_0RB1Lg_0RK0LF_0RT0LP_0LP---_1Lg0LF_0LF---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0LF---_------_1LF---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA1RH_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RH_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgmTR".
Definition mp' := mp_from_str "KQBFPgmTR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM320.


Module TM321.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1RE---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA1LF_0RB---".
Definition tm0 := TM'_from_str "0RR0RI_1LF0RK_1RR1RI_1Lm1RK_0LN0RB_0LP0LF_1LN0RR_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0RT1Lg_0RB0RR_0RK0RT_1RB1RR_1RK1RT_0L^1RQ_0L`1RK_1L^0LF_1L`1RT_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0RY0Lg_1LF1RQ_0RB1Lg_0RK0LF_0RT0LP_0LP---_1Lg0LF_0LF---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0LF---_------_1LF---".
Definition tm0' := TM'_from_str "0RR0RI_1LF0RK_1RR1RI_1Ln1RK_0LN0RB_0LP0LF_1LN0RR_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0RT1Lg_0RB0RR_0RK0RT_1RB1RR_1RK1RT_0L^1RQ_0L`1RK_1L^0LF_1L`1RT_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0RY0Lg_1LF1RQ_0RB1Lg_0RK0LF_0RT0LP_0LP---_1Lg0LF_0LF---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RR---_1LF---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA1RH_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RH_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgmTR".
Definition mp' := mp_from_str "KQBFPgnTR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM321.


Module TM322.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA1LF_0RB---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA1LF_0RB---".
Definition tm0 := TM'_from_str "0RR0RI_1LF0RK_1RR1RI_1Ln1RK_0LN0RB_0LP0LF_1LN0RR_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0RT1Lg_0RB0RR_0RK0RT_1RB1RR_1RK1RT_0L^1RQ_0L`1RK_1L^0LF_1L`1RT_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0RY0Lg_1LF1RQ_0RB1Lg_0RK0LF_0RT0LP_0LP---_1Lg0LF_0LF---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RR---_1LF---".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Ln1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0R\1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF1R\_0RI0RZ_0RK0R\_1RI1RZ_1RK1R\_0RB1RQ_0LF1RK_0RZ0LF_1LF1R\_0R\0LP_0LP---_1Lg0LF_0LF---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RZ---_1LF---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA1RH_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RH_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgnTR".
Definition mp' := mp_from_str "KQBFPgn\Z".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM322.


Module TM323.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LD_0RB---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LD_0LC---".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1L^1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP---_1Lg0LF_0LF---_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RZ---_1LF---".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1L^1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP---_1Lg0LF_0LF---_0LF0L^_0LH0L`_1LF1L^_1LH1L`_1LF---_0RK---_1L^---_1RK---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA---_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RJ_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPg^lZ".
Definition mp' := mp_from_str "KQBFPg^lZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM323.


Module TM324.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LD_0LC---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LF_0RB---".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1L^1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP---_1Lg0LF_0LF---_0LF0L^_0LH0L`_1LF1L^_1LH1L`_1LF---_0RK---_1L^---_1RK---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Ln1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP---_1Lg0LF_0LF---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RZ---_1LF---".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA---_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RJ_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPg^lZ".
Definition mp' := mp_from_str "KQBFPgnlZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM324.


Module TM325.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LF_0RB---".
Definition tm' := TM_from_str "1LB0RB_0RC0LF_1RA1RD_0LD1RE_0RB---_1LA1LE".
Definition tm0 := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Ln1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Le_0RK0Lg_0RK1Le_0Rl1Lg_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lg1RQ_1RQ1RK_1Lg0LF_0LF---_0RI0Rj_0RK0Rl_1RI1Rj_1RK1Rl_0RB1RQ_0LF---_0RZ0LF_1LF---_0Rl0LP_0LP---_1Lg0LF_0LF---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RZ---_1LF---".
Definition tm0' := TM'_from_str "0RZ0RI_1LF0RK_1RZ1RI_1Lf1RK_0LN0RB_0LP0LF_1LN0RZ_1LP1LF_0RQ0LP_0RS0LF_1RQ0LF_1RS---_1LF0Lm_0RK0Lo_0RK1Lm_0Rd1Lo_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lo1RQ_1RQ1RK_1Lo0LF_0LF---_0L]0Rb_0RK0Rd_1RQ1Rb_1RK1Rd_0L]1RQ_0L_---_1L]0LF_1L_---_0RI---_0RK---_1RI---_1RK---_0RB---_0LF---_0RZ---_1LF---_0Rd0LP_0LP---_1Lo0LF_0LF---_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh".
Definition tm1 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD---_1RA---_0RA0RH".
Definition tm2 := TM'_from_str "1RB0LD_0RC0RI_1LD0RA_0LE0LD_0RH1LF_1LD1LG_0LD1RJ_1RA1RJ_0RA0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "KQBFPgnlZ".
Definition mp' := mp_from_str "KQBFPofdZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM325.


Module TM326.
Definition tm := TM_from_str "1RB0RF_1LC0RD_---1LD_0LE1LD_1LA1LB_1RA1RF".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_---1RD_0LE1LD_1LA1LB_1RA1RF".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L`0RL_0RD0RD_1L`0Rk_1LN0Rl_---0RY_1Lg0R[_---1RY_1L`1R[_0LV0LF_0LX0Lg_1LV1LF_1LX1Lg_---1LF_---1Lg_---1LN_---1L`_---0L^_---0L`_---1L^_---1L`_0RD1LF_0LX1Lg_0RD1LN_0Lg1L`_0Le0L^_0Lg0L`_1Le1L^_1Lg1L`_0R[---_0Rj1LF_1R[1L`_1Rj1LN_0LF0LN_0LH0LP_1LF1LN_1LH1LP_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1L`1RL_1RB1RD_1R[1Rk_1Rj1Rl".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L`0RL_0RD0RD_1L`0Rk_1LN0Rl_---0RY_1Lg0R[_---1RY_1L`1R[_0LV0LF_0LX0Lg_1LV1LF_1LX1Lg_---0RZ_---0R\_---1RZ_---1R\_---0LN_---0L`_---1LN_---1L`_0RD1LF_0LX1Lg_0RD1LN_0Lg1L`_0Le0L^_0Lg0L`_1Le1L^_1Lg1L`_0R[---_0Rj1LF_1R[1L`_1Rj1LN_0LF0LN_0LH0LP_1LF1LN_1LH1LP_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1L`1RL_1RB1RD_1R[1Rk_1Rj1Rl".
Definition tm1 := TM'_from_str "1RB1RH_1LC---_1LD1LC_1LG1LE_0LF0LD_---1LC_0RA0RA_1RK1RI_0RA0RJ_1RA1RJ_0RB0RH".
Definition tm2 := TM'_from_str "1RB1RH_1LC---_1LD1LC_1LG1LE_0LF0LD_1RL1LC_0RA0RA_1RK1RI_0RA0RJ_1RA1RJ_0RB0RH_1RL1RL".
Definition l0 := [0;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "DL`gNXFkjlB".
Definition mp' := mp_from_str "DL`gNXFkjlB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM326.


Module TM327.
Definition tm := TM_from_str "1RB0LA_0RC1RC_1RD1RF_1LE1LD_---0LA_1RD0RB".
Definition tm' := TM_from_str "1RB0LA_0RC---_1RD1RE_1LA1LD_0LF0RF_0RC1RC".
Definition tm0 := TM'_from_str "0RJ0RS_0RL1RZ_1RJ1RS_1RL0LE_1RZ0LE_1R\0LG_1Rj1LE_1Rl1LG_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_1Rj1LE_0R\1R\_1Lh1L`_0RK1RK_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_0LG1LE_0L`1RQ_1LG1L`_1L`1RR_------_1Rj1Lh_---1LG_1LE1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_---0RS_---1RZ_---1RS_---0LE_---0LE_---0LG_---1LE_---1LG_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0LG0RZ_0L`0R\_1LG0Rj_1L`0Rl".
Definition tm0' := TM'_from_str "0RJ0RS_0RL1RZ_1RJ1RS_1RL0LE_1RZ0LE_---0LG_1Rb1LE_---1LG_0RQ---_0RS---_1RQ---_1RS---_1Rb---_0R\---_1LH---_0Rk---_0RZ0Rb_0R\0Rd_1RZ1Rb_1R\1Rd_0LG1LE_0L`1RQ_1LG1L`_1L`1RR_------_1Rb1LH_---1LG_1LE1L`_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lm0RZ_0Lo0R\_1Lm0Rb_1Lo0Rd_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_1Rb1LE_0R\1R\_1LH1L`_0Rk1Rk".
Definition tm1 := TM'_from_str "1RB1RJ_0RC0RD_1RD1LG_0RE0RA_1LF1LI_1RC0LF_---1LH_1RD1LF_1LG1LI_0RE0RK_1RE1RA".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0RD_1RD1LG_0RE0RA_1LF1LI_1RC0LF_1RL1LH_1RD1LF_1LG1LI_0RE0RK_1RE1RA_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "KQZj\EhG`Rl".
Definition mp' := mp_from_str "kQZb\EHG`Rd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM327.


Module TM328.
Definition tm := TM_from_str "1RB0LA_0RC---_1RD1RE_1LA1LD_0LF0RF_0RC1RC".
Definition tm' := TM_from_str "1RB0LA_0RC1RC_1RD1RF_1LE1LD_---0LA_0LB0RB".
Definition tm0 := TM'_from_str "0RJ0RS_0RL1RZ_1RJ1RS_1RL0LE_1RZ0LE_---0LG_1Rb1LE_---1LG_0RQ---_0RS---_1RQ---_1RS---_1Rb---_0R\---_1LH---_0Rk---_0RZ0Rb_0R\0Rd_1RZ1Rb_1R\1Rd_0LG1LE_0L`1RQ_1LG1L`_1L`1RR_------_1Rb1LH_---1LG_1LE1L`_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lm0RZ_0Lo0R\_1Lm0Rb_1Lo0Rd_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_1Rb1LE_0R\1R\_1LH1L`_0Rk1Rk".
Definition tm0' := TM'_from_str "0RJ0RS_0RL1RZ_1RJ1RS_1RL0LE_1RZ0LE_1R\0LG_1Rj1LE_1Rl1LG_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_1Rj1LE_0R\1R\_1Lh1L`_0RK1RK_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_0LG1LE_0L`1RQ_1LG1L`_1L`1RR_------_1Rj1Lh_---1LG_1LE1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_---0RS_---1RZ_---1RS_---0LE_---0LE_---0LG_---1LE_---1LG_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0LM0RZ_0LO0R\_1LM0Rj_1LO0Rl".
Definition tm1 := TM'_from_str "1RB1RJ_0RC0RD_1RD1LG_0RE0RA_1LF1LI_1RC0LF_---1LH_1RD1LF_1LG1LI_0RE0RK_1RE1RA".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0RD_1RD1LG_0RE0RA_1LF1LI_1RC0LF_1RL1LH_1RD1LF_1LG1LI_0RE0RK_1RE1RA_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "kQZb\EHG`Rd".
Definition mp' := mp_from_str "KQZj\EhG`Rl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM328.


Module TM329.
Definition tm := TM_from_str "1RB0LA_0RC1RC_1RD1RF_1LE1LD_---0LA_0LB0RB".
Definition tm' := TM_from_str "1RB0LA_0RC---_1RD1RE_1LA1LD_1RD0RF_0RC1RC".
Definition tm0 := TM'_from_str "0RJ0RS_0RL1RZ_1RJ1RS_1RL0LE_1RZ0LE_1R\0LG_1Rj1LE_1Rl1LG_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_1Rj1LE_0R\1R\_1Lh1L`_0RK1RK_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_0LG1LE_0L`1RQ_1LG1L`_1L`1RR_------_1Rj1Lh_---1LG_1LE1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_---0RS_---1RZ_---1RS_---0LE_---0LE_---0LG_---1LE_---1LG_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0LM0RZ_0LO0R\_1LM0Rj_1LO0Rl".
Definition tm0' := TM'_from_str "0RJ0RS_0RL1RZ_1RJ1RS_1RL0LE_1RZ0LE_---0LG_1Rb1LE_---1LG_0RQ---_0RS---_1RQ---_1RS---_1Rb---_0R\---_1LH---_0Rk---_0RZ0Rb_0R\0Rd_1RZ1Rb_1R\1Rd_0LG1LE_0L`1RQ_1LG1L`_1L`1RR_------_1Rb1LH_---1LG_1LE1L`_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0LG0RZ_0L`0R\_1LG0Rb_1L`0Rd_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_1Rb1LE_0R\1R\_1LH1L`_0Rk1Rk".
Definition tm1 := TM'_from_str "1RB1RJ_0RC0RD_1RD1LG_0RE0RA_1LF1LI_1RC0LF_---1LH_1RD1LF_1LG1LI_0RE0RK_1RE1RA".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0RD_1RD1LG_0RE0RA_1LF1LI_1RC0LF_1RL1LH_1RD1LF_1LG1LI_0RE0RK_1RE1RA_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "KQZj\EhG`Rl".
Definition mp' := mp_from_str "kQZb\EHG`Rd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM329.


Module TM330.
Definition tm := TM_from_str "1RB1RA_1RC1LB_1LD0RA_0RA0LE_---0LF_0RC0LB".
Definition tm' := TM_from_str "1RB1RA_1RC1LB_1LD0RA_1LC0LE_---0LF_1RD0LB".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lm1RT_0LP1RL_1RC1LP_1LP1RD_0RR0RC_0RT1RB_1RR1RC_1RT1LP_0Lg0LN_1RJ0LP_1Lg1LN_1RB1LP_0RB0RA_---0RC_1RB1RA_1Lm1RC_0L^0RT_0L`0RL_1L^1RB_1L`0RD_0RA---_0RC0RL_1RA---_1RC0LM_0RT0Le_0RL0Lg_1RB1Le_0RD1Lg_---0RB_---0Lg_---1RB_---0LN_---0Lm_---0Lo_---1Lm_---1Lo_0RQ---_0RS1RJ_1RQ1Lm_1RS0LP_0RL0LM_0RJ0LO_0RD1LM_0RB1LO".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lm1RT_0LP1RL_1RC1LP_1LP1RD_0RR0RC_0RT1RB_1RR1RC_1RT1LP_0Lg0LN_1RJ0LP_1Lg1LN_1RB1LP_1L`0RA_---0RC_0RD1RA_1Lm1RC_0L^0RT_0L`0RL_1L^1RB_1L`0RD_1LX---_0RB0RL_1Lg---_1RB0LM_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_---0RB_---0Lg_---1RB_---0LN_---0Lm_---0Lo_---1Lm_---1Lo_0RZ---_0R\1RJ_1RZ1Lm_1R\0LP_0RL0LM_0Lm0LO_0RD1LM_1Lm1LO".
Definition tm1 := TM'_from_str "1LB1RJ_0RG0LC_0LH0LD_1RK0LE_1RF1LE_0RG0RI_1RA1LE_---1LB_1RG1RI_1RK1RF_0RA1RF".
Definition tm2 := TM'_from_str "1LB1RJ_0RG0LC_0LH0LD_1RK0LE_1RF1LE_0RG0RI_1RA1LE_1RL1LB_1RG1RI_1RK1RF_0RA1RF_1RL1RL".
Definition l0 := [0;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "TmMNPBLgDCJ".
Definition mp' := mp_from_str "TmMNPBLgDCJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM330.


Module TM331.
Definition tm := TM_from_str "1RB1RA_1RC1LB_1LD0RA_1LC0LE_---0LF_1RD0LB".
Definition tm' := TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lm1RT_0LP1RL_1RC1LP_1LP1RD_0RR0RC_0RT1RB_1RR1RC_1RT1LP_0Lg0LN_1RJ0LP_1Lg1LN_1RB1LP_1L`0RA_---0RC_0RD1RA_1Lm1RC_0L^0RT_0L`0RL_1L^1RB_1L`0RD_1LX---_0RB0RL_1Lg---_1RB0LM_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_---0RB_---0Lg_---1RB_---0LN_---0Lm_---0Lo_---1Lm_---1Lo_0RZ---_0R\1RJ_1RZ1Lm_1R\0LP_0RL0LM_0Lm0LO_0RD1LM_1Lm1LO".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lm1RT_0LP1RL_1RC1LP_1LP1RD_0RR0RC_0RT1RB_1RR1RC_1RT1LP_0Lg0LN_1RJ0LP_1Lg1LN_1RB1LP_0RD0RA_---0RC_1RD1RA_1Lm1RC_0L^0RT_0L`0RL_1L^1RB_1L`0RD_0RB---_0RD0RL_1RB---_1RD0LM_1RT0Le_1RL0Lg_1LP1Le_1RD1Lg_---0RB_---0Lg_---1RB_---0LN_---0Lm_---0Lo_---1Lm_---1Lo_0RY---_0R[1RJ_1RY1Lm_1R[0LP_0RL0LM_---0LO_0RD1LM_---1LO".
Definition tm1 := TM'_from_str "1LB1RJ_0RG0LC_0LH0LD_1RK0LE_1RF1LE_0RG0RI_1RA1LE_---1LB_1RG1RI_1RK1RF_0RA1RF".
Definition tm2 := TM'_from_str "1LB1RJ_0RG0LC_0LH0LD_1RK0LE_1RF1LE_0RG0RI_1RA1LE_1RL1LB_1RG1RI_1RK1RF_0RA1RF_1RL1RL".
Definition l0 := [0;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "TmMNPBLgDCJ".
Definition mp' := mp_from_str "TmMNPBLgDCJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM331.


Module TM332.
Definition tm := TM_from_str "1RB0LB_0RC1RB_1LD0RE_0LA0LD_0RF---_1RC1RF".
Definition tm' := TM_from_str "1RB0LB_0RC0RD_1LD0RE_0LA0LD_0RF---_1RC1RF".
Definition tm0 := TM'_from_str "0RJ1Ra_0RL0RS_1RJ1LM_1RL1RS_1LM0LM_1RS0LO_1Ra1LM_1RL1LO_0RQ0RJ_0RS0RL_1RQ1RJ_1RS1RL_0LG1LM_0Ri1RS_1LG1Ra_---1RL_1Ra0Ra_1LE0Rc_1LM1Ra_1L]1Rc_0L^0RR_0L`---_1L^0Rj_1L`---_0RS1LM_0LG0LE_1RS0LM_1LM0L]_0LE0L]_0LG0L__1LE1L]_1LG1L__0Ri---_0Rk---_1Ri---_1Rk---_1LE---_0RT---_0Rc---_0Rl---_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_1L]_1Ri1RT_1L_1Rc_---1Rl".
Definition tm0' := TM'_from_str "0RJ1Ra_0RL0RS_1RJ1LM_1RL1RS_1LM0LM_1RS0LO_1Ra1LM_0LM1LO_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0LG1LM_0Ri0LE_1LG1Ra_---1LE_1Ra0Ra_1LE0Rc_1LM1Ra_1L]1Rc_0L^0RR_0L`---_1L^0Rj_1L`---_0RS1LM_0LG0LE_1RS0LM_1LM0L]_0LE0L]_0LG0L__1LE1L]_1LG1L__0Ri---_0Rk---_1Ri---_1Rk---_1LE---_0RT---_0Rc---_0Rl---_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_1L]_1Ri1RT_1L_1Rc_---1Rl".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_1LD0LD_0LE1LD_1RF1LD_0RG---_0RK0RH_0RA0RI_1RA1RI_1RG---_1LC0RJ".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_1LD0LD_0LE1LD_1RF1LD_0RG1RL_0RK0RH_0RA0RI_1RA1RI_1RG1RL_1LC0RJ_1RL1RL".
Definition l0 := [1;0;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "T]EMGaijlcR".
Definition mp' := mp_from_str "T]EMGaijlcR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM332.


Module TM333.
Definition tm := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0RA---".
Definition tm' := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0RE---".
Definition tm0 := TM'_from_str "1RY0RI_1LN0RK_1LP1RI_1Lm1RK_0LN1RB_0LP0LN_1LN1RY_1LP1LN_0R[0LX_1LX0LX_1R[0Lg_1Lg---_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ1RY_0R\1LN_1RZ1LP_1R\1Lm_1Lm0LN_1RB0LP_1RK1LN_1RY1LP_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0Lg1LN_1R[0RB_1Lg0RK_0Lg0RY_1RY1RY_1LN---_1LP1LP_1Lm---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RA---_0RC---_1RA---_1RC---_0LX---_0R[---_1LX---_0LX---".
Definition tm0' := TM'_from_str "1RY0RI_1LN0RK_1LP1RI_1Lm1RK_0LN1RB_0LP0LN_1LN1RY_1LP1LN_0R[0LX_1LX0LX_1R[0Lg_1Lg---_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ1RY_0R\1LN_1RZ1LP_1R\1Lm_1Lm0LN_1RB0LP_1RK1LN_1RY1LP_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0Lg1LN_1R[0RB_1Lg0RK_0Lg0RY_1RY1RY_1LN---_1LP1LP_1Lm---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0Ra---_0Rc---_1Ra---_1Rc---_0LX---_0LX---_1LX---_1LX---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LD---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LD1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;1;1]%N.
Definition mp := mp_from_str "YBNXPgK[m".
Definition mp' := mp_from_str "YBNXPgK[m".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM333.


Module TM334.
Definition tm := TM_from_str "1LB---_1LC1LB_1RD0LB_1RE0RD_0RF0RC_1RA1LA".
Definition tm' := TM_from_str "1LB---_1LC1LB_1RD0LB_1RE0RD_0RF0RC_1RA0LF".
Definition tm0 := TM'_from_str "1RY---_1LX---_1LO---_1LP---_0LN---_0LP---_1LN---_1LP---_0R[1RY_1LV1LX_1R[1LO_1LN1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RZ1Rb_0R\0LX_1RZ0LO_1R\0LP_1Rk0LM_1Rb0LO_1RS1LM_1RY1LO_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1RB0Rk_1RZ0Rb_1LP0RS_0LO0RY_0Ri0RQ_0Rk0RS_1Ri1RQ_1Rk1RS_1LX0Rd_0LP0LV_---0R[_1LP1LV_0RB1LX_0RD---_1RB1LP_1RD---_0LP0LF_---0LH_1LP1LF_---1LH".
Definition tm0' := TM'_from_str "1RY---_1LX---_1LO---_1LP---_0LN---_0LP---_1LN---_1LP---_0R[1RY_1LV1LX_1R[1LO_1LN1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RZ1Rb_0R\0LX_1RZ0LO_1R\0LP_1Rk0LM_1Rb0LO_1RS1LM_1RY1LO_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1RB0Rk_1RZ0Rb_1LP0RS_0LO0RY_0Ri0RQ_0Rk0RS_1Ri1RQ_1Rk1RS_1LX0Rd_0LP0LV_---0R[_1LP1LV_0RB1LX_0RD0LP_1RB1LP_1RD0Lm_0LP0Lm_---0Lo_1LP1Lm_---1Lo".
Definition tm1 := TM'_from_str "0RB0RK_1RC1RJ_1RD1LM_1LE---_1RL1LF_1LH1LG_0LE0LM_1RI0LF_0RC0RJ_1RA0LF_1RI1RL_0RI0RL_1LE1LM".
Definition tm2 := TM'_from_str "0RB0RK_1RC1RJ_1RD1LM_1LE1RN_1RL1LF_1LH1LG_0LE0LM_1RI0LF_0RC0RJ_1RA0LF_1RI1RL_0RI0RL_1LE1LM_1RN1RN".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "ZdkBXONVbS[YP".
Definition mp' := mp_from_str "ZdkBXONVbS[YP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM334.


Module TM335.
Definition tm := TM_from_str "1RB0RF_1LC1LE_1RA1LD_0RB---_0LB0RA_1RE1LF".
Definition tm' := TM_from_str "1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L`0LO_0Rb1RJ_1L`0RC_0RC1Ri_0Rk1LV_1LO0Ri_1Rk1Lf_---1Ri_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RB1LV_0RD---_1RB1Lf_1RD---_---0L^_1Rb0L`_1Ri1L^_1RC1L`_0RI---_0RK---_1RI---_1RK---_1Rb---_0LO---_1RC---_1LO---_1Rb0RA_0LO0RC_0L`1RA_0Rb1RC_0LM1LO_0LO0Rb_1LM0Ri_1LO0RC_0Rb0RC_0Rd1Ri_1Rb1RC_1Rd1Lp_0Lf0Ln_1RJ0Lp_1Lf1Ln_1Ri1Lp".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L`0LO_0Rj1RJ_1L`0RC_0RC1Ra_0Rc1LV_1LO0Ra_1Rc1Ln_---1Ra_0LV0Ln_0LX0Lp_1LV1Ln_1LX1Lp_0RB1LV_0RD---_1RB1Ln_1RD---_---0L^_1Rj0L`_1Ra1L^_1RC1L`_1Rj---_0LO---_0L`---_0Rj---_0LM---_0LO---_1LM---_1LO---_0Rj0RC_0Rl1Ra_1Rj1RC_1Rl1Lh_0Ln0Lf_1RJ0Lh_1Ln1Lf_1Ra1Lh_1Rj0RA_0LO0RC_0L`1RA_0Rj1RC_0LM1LO_0LO0Rj_1LM0Ra_1LO0RC".
Definition tm1 := TM'_from_str "0LB0RD_1LC1LF_1RA0LH_1RE1RG_1LB0RG_0LB0RA_0RA0RD_1LB---".
Definition tm2 := TM'_from_str "0LB0RD_1LC1LF_1RA0LH_1RE1RG_1LB0RG_0LB0RA_0RA0RD_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "bOVCJfi`".
Definition mp' := mp_from_str "jOVCJna`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM335.


Module TM336.
Definition tm := TM_from_str "1LB0LD_1RC1LE_1RD0RC_0RE0RC_0LA0LF_1LA---".
Definition tm' := TM_from_str "1LB0LC_1RC1LE_0RE0RD_1RC0RD_0LA0LF_1LA---".
Definition tm0 := TM'_from_str "0RS1RZ_1LG0RZ_1RS0Lh_1Lo1RZ_0LN0L]_0LP0L__1LN1L]_1LP1L__0RR1LN_0RT1LF_1RR1L]_1RT---_1Rc0Lf_1RZ0Lh_1RS1Lf_1RQ1Lh_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lh0Rc_1RZ0RZ_0L_0RS_1RQ0RQ_0Ra0RQ_0Rc0RS_1Ra1RQ_1Rc1RS_0LN0Rc_0LF0RZ_1LN0RS_1LF0RQ_1RZ0LP_0LN---_0Lh0L__0Rc---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_1RQ---_1LN---_1Lh---_0RS---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0R[1RR_1LG0RR_1R[0Lh_1Lo1RR_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RR1LN_0RT1LF_1RR1LU_1RT---_0Lh0Lf_1RR0Lh_0LW1Lf_1RY1Lh_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LN0Rc_0LF0RR_1LN0R[_1LF0RY_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0Lh0Rc_1RR0RR_0LW0R[_1RY0RY_1RR0LP_0LN---_0Lh0LW_0Rc---_0LE0Lm_0LG0Lo_1LE1Lm_1LG1Lo_1RY---_1LN---_1Lh---_0R[---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "0RB0RH_0LC0LG_1LD1LJ_1LF1LE_0LF0RB_1RA0LC_1LF0RH_1RA1RI_0RA0RI_1LK---_0LL0LG_1RI1LC".
Definition tm2 := TM'_from_str "0RB0RH_0LC0LG_1LD1LJ_1LF1LE_0LF0RB_1RA0LC_1LF0RH_1RA1RI_0RA0RI_1LK1RM_0LL0LG_1RI1LC_1RM1RM".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "ZchG]N_SQoFP".
Definition mp' := mp_from_str "RchGUNW[YoFP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM336.


Module TM337.
Definition tm := TM_from_str "1LB0LD_1LC0LA_1RD1LB_1RE0RD_1RF0RB_1LC---".
Definition tm' := TM_from_str "1LB0LD_1LC0LA_1RD1LB_1RE0RD_0RF0RB_1LA---".
Definition tm0 := TM'_from_str "1RY0Rl_1LN0Rb_1LP1Rl_1L]1Rb_0LN0L]_0LP0L__1LN1L]_1LP1L__0R[0LX_1LX1LG_1R[0LG_1LG0Rl_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RZ1RY_0R\1LN_1RZ1LP_1R\1L]_1Rl0LN_1Rb0LP_1RK1LN_1RY1LP_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1LG0Rl_1R[0Rb_---0RK_0LG0RY_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_0LP1Rb_---0LN_1LP1RY_---1LN_0R[---_1LX---_1R[---_1LG---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "1RY0Rk_1LN0Rb_1LP1Rk_1L]1Rb_0LN0L]_0LP0L__1LN1L]_1LP1L__0R[0LX_1LX1LG_1R[0LG_1LG0Rk_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RZ1RY_0R\1LN_1RZ1LP_1R\1L]_1Rk0LN_1Rb0LP_1RK1LN_1RY1LP_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1LG0Rk_1R[0Rb_---0RK_0LG0RY_0Ri0RI_0Rk0RK_1Ri1RI_1Rk1RK_0LP1Rb_---0LN_1LP1RY_---1LN_1LX---_------_1LG---_0RK---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB---_1LC1LD_0LE0LB_1LB0RA_1RF1LJ_0RG0RF_0RA0RH_1RI0LB_1RG1RF_1LE1LB".
Definition tm2 := TM'_from_str "1LB1RK_1LC1LD_0LE0LB_1LB0RA_1RF1LJ_0RG0RF_0RA0RH_1RI0LB_1RG1RF_1LE1LB_1RK1RK".
Definition l0 := [1;0;1;0;0;1;1;0]%N.
Definition mp := mp_from_str "lGN]XYbK[P".
Definition mp' := mp_from_str "kGN]XYbK[P".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM337.


Module TM338.
Definition tm := TM_from_str "1LB0RC_1LC0LB_1RD0LA_0RE0RC_1RB1RF_1RD---".
Definition tm' := TM_from_str "1LB0RF_1LC0LB_1RD0LA_0RE0RC_1RB1RF_1RD---".
Definition tm0 := TM'_from_str "0LO0RQ_1LV0RS_1LG1RQ_1LM1RS_0LN0Rc_0LP0LN_1LN0RS_1LP1LN_0RS1RZ_1LN0LV_1RS0LG_0RS0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ0LX_0R\0RZ_1RZ0LO_1R\1RZ_1RJ0LE_1RZ0LG_1Rj1LE_0LO1LG_0Ra0RQ_0Rc0RS_1Ra1RQ_1Rc1RS_1LN0Rc_0R\0LN_0LV0RS_---1LN_0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LG1Rc_0LM---_1LG1RS_1LM---_0RZ---_0R\---_1RZ---_1R\---_1RJ---_1RZ---_1Rj---_0LO---".
Definition tm0' := TM'_from_str "0LO0Ri_1LV0Rk_1LG1Ri_1LM1Rk_0LN0Rc_0LP---_1LN0RS_1LP---_0RS1RZ_1LN0LV_1RS0LG_0RS0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ0LX_0R\0RZ_1RZ0LO_1R\1RZ_1RJ0LE_1RZ0LG_1Rj1LE_0LO1LG_0Ra0RQ_0Rc0RS_1Ra1RQ_1Rc1RS_1LN0Rc_0R\0LN_0LV0RS_---1LN_0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LG1Rc_0LM---_1LG1RS_1LM---_0RZ---_0R\---_1RZ---_1R\---_1RJ---_1RZ---_1Rj---_0LO---".
Definition tm1 := TM'_from_str "1RB0LF_0RC0RA_1RD1RJ_1LE0LG_0LI0LF_1LG1LL_1RB0LH_1LE0RA_0LF1LH_0RK---_1RC1RA_0LG0LL".
Definition tm2 := TM'_from_str "1RB0LF_0RC0RA_1RD1RJ_1LE0LG_0LI0LF_1LG1LL_1RB0LH_1LE0RA_0LF1LH_0RK1RM_1RC1RA_0LG0LL_1RM1RM".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "SZcJNOVGXj\M".
Definition mp' := mp_from_str "SZcJNOVGXj\M".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM338.


Module TM339.
Definition tm := TM_from_str "1RB0LF_1LC0LB_1RD0LB_0RA0RE_1RF---_0RD0RC".
Definition tm' := TM_from_str "1RB0RA_1LC0LB_1RD0LB_0RA0RE_1RF---_0RD0RC".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RZ_1RJ1RA_1RL1RZ_0LO0Lm_0LM0Lo_1LO1Lm_1LM1Lo_0Rc1Rj_1LV0LV_1Rc0LO_1LM0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ1Rj_0R\0LV_1RZ0LO_1R\0LM_1RJ0LM_1Rj0LO_1RA1LM_---1LO_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_1LV0R[_0RJ---_0LV0RS_0RA---_0Rj---_0Rl---_1Rj---_1Rl---_1RA---_1RZ---_1Ra---_0LO---_0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0RJ0RC_0Rj0LV_0RA0Rc_---1LV".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LO1LV_0LM0RJ_1LO0LV_1LM0RA_0Rc1Rj_1LV0LV_1Rc0LO_1LM0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ1Rj_0R\0LV_1RZ0LO_1R\0LM_1RJ0LM_1Rj0LO_1RA1LM_---1LO_0RA0Ra_0RC0Rc_1RA1Ra_1RC1Rc_1LV0R[_0RJ---_0LV0RS_0RA---_0Rj---_0Rl---_1Rj---_1Rl---_1RA---_1RZ---_1Ra---_0LO---_0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0RJ0RC_0Rj0LV_0RA0Rc_---1LV".
Definition tm1 := TM'_from_str "1RB---_0RC0RG_1RD1RL_0RE0RD_1LF0LF_1RB0LJ_1RH0LJ_0RI0RA_1RE1RD_1LF1LK_0LF0LK_0RB---".
Definition tm2 := TM'_from_str "1RB1RM_0RC0RG_1RD1RL_0RE0RD_1LF0LF_1RB0LJ_1RH0LJ_0RI0RA_1RE1RD_1LF1LK_0LF0LK_0RB1RM_1RM1RM".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "cj[AJVSZCOMa".
Definition mp' := mp_from_str "cj[AJVSZCOMa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM339.


Module TM340.
Definition tm := TM_from_str "1RB0RF_0LC0RA_1LE1RD_0RC---_1LA0LE_1RA0LC".
Definition tm' := TM_from_str "1RB0RE_0RC0RA_1LD1RF_1LA0LD_1RA0LC_0RC---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1Lf0RL_1RJ0Lf_1RZ0Rk_1Ri1Lf_0LH0RA_0RS0RC_0Lg1RA_1RS1RC_0LU0RS_0LW0RB_1LU0RC_1LW0LH_1Ri0RZ_1LF0R\_1Lf1RZ_1Le1R\_0Lf1Lf_0Lh---_1Lf1RZ_1Lh---_0RQ---_0RS---_1RQ---_1RS---_0LH---_0RS---_1LH---_------_0RC1RJ_0LH0LF_1RC0Lf_0Lg0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RB0LH_0RD0RS_1RB0Lg_1RD1RS_1RS0LU_1RB0LW_1RC1LU_0Lg1LW".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L^0RL_1RJ0L^_1Rj0Rc_1Ra1L^_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0LH0RS_0RS0RB_1LH0RC_---0LH_1Ra0Rj_1LF0Rl_1L^1Rj_1L]1Rl_0L^1L^_0L`---_1L^1Rj_1L`---_0RC1RJ_0LH0LF_1RC0L^_0L_0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RB0LH_0RD0RS_1RB0L__1RD1RS_1RS0LU_1RB0LW_1RC1LU_0L_1LW_0RQ---_0RS---_1RQ---_1RS---_0LH---_0RS---_1LH---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RI_0LD0LE_1RJ1LC_1LF1LH_1RA0LC_1RA1RJ_0LF0LH_0RB---_0RK0LD_0RM0RL_1RK0LE_1RB1RG".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RI_0LD0LE_1RJ1LC_1LF1LH_1RA0LC_1RA1RJ_0LF0LH_0RB1RN_0RK0LD_0RM0RL_1RK0LE_1RB1RG_1RN1RN".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "JSfHgFCeZiBkL".
Definition mp' := mp_from_str "JS^H_FC]jaBcL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM340.


Module TM341.
Definition tm := TM_from_str "1RB0RE_0RC0RA_1LD1RF_1LA0LD_1RA0LC_0RC---".
Definition tm' := TM_from_str "1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_0LA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L^0RL_1RJ0L^_1Rj0Rc_1Ra1L^_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0LH0RS_0RS0RB_1LH0RC_---0LH_1Ra0Rj_1LF0Rl_1L^1Rj_1L]1Rl_0L^1L^_0L`---_1L^1Rj_1L`---_0RC1RJ_0LH0LF_1RC0L^_0L_0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RB0LH_0RD0RS_1RB0L__1RD1RS_1RS0LU_1RB0LW_1RC1LU_0L_1LW_0RQ---_0RS---_1RQ---_1RS---_0LH---_0RS---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L^0RL_1RJ0L^_1Ri0Rc_1Ra1L^_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0LH0RS_0RS0RB_1LH0RC_---0LH_1Ra0Ri_1LF0Rk_1L^1Ri_1L]1Rk_0L^1L^_0L`---_1L^1Ri_1L`---_0RC1RJ_0LH0LF_1RC0L^_0L_0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RB0LH_0RD0RS_1RB0L__1RD1RS_1RS0LU_1RB0LW_1RC1LU_0L_1LW_0RS---_0RB---_1RS---_1RB---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RI_0LD0LE_1RJ1LC_1LF1LH_1RA0LC_1RA1RJ_0LF0LH_0RB---_0RK0LD_0RM0RL_1RK0LE_1RB1RG".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RI_0LD0LE_1RJ1LC_1LF1LH_1RA0LC_1RA1RJ_0LF0LH_0RB1RN_0RK0LD_0RM0RL_1RK0LE_1RB1RG_1RN1RN".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "JS^H_FC]jaBcL".
Definition mp' := mp_from_str "JS^H_FC]iaBcL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM341.


Module TM342.
Definition tm := TM_from_str "1RB0RE_0RC0RA_1LD1RE_1LA0LD_1RA0LF_1LD---".
Definition tm' := TM_from_str "1RB0RE_0RC0RA_1LD1RF_1LA0LD_1RA0LC_1RA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L^0RL_1RJ0L^_1Rb0Rc_1Ra1L^_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0LH0RS_0RD0RB_1LH0RC_---0LH_1Ra0Rb_1LF0Rd_1L^1Rb_1L]1Rd_0L^1RL_0L`---_1L^1Rc_1L`---_0RC1RJ_0LH0LF_1RC0L^_0L_0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RB0LH_0RD---_1RB0L__1RD---_1RS0Lm_1RB0Lo_1RC1Lm_0L_1Lo_1Ra---_1LF---_1L^---_1L]---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L^0RL_1RJ0L^_1Rj0Rc_1Ra1L^_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0LH0RS_0RD0RB_1LH0RC_---0LH_1Ra0Rj_1LF0Rl_1L^1Rj_1L]1Rl_0L^1RL_0L`---_1L^1Rc_1L`---_0RC1RJ_0LH0LF_1RC0L^_0L_0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0RB0LH_0RD0RD_1RB0L__1RD1RD_1RS0LU_1RB0LW_1RC1LU_0L_1LW_0RB---_0RD---_1RB---_1RD---_1RS---_1RB---_1RC---_0L_---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RI_0LD0LE_1RN1LC_1LF1LH_1RA0LC_1RA1RN_0LF0LH_0RJ---_1RM1RK_1RL0LE_0RM0RK_1RB1RG_0RL0LD".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RI_0LD0LE_1RN1LC_1LF1LH_1RA0LC_1RA1RN_0LF0LH_0RJ1RO_1RM1RK_1RL0LE_0RM0RK_1RB1RG_0RL0LD_1RO1RO".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "JS^H_FC]bDcBLa".
Definition mp' := mp_from_str "JS^H_FC]jDcBLa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM342.


Module TM343.
Definition tm := TM_from_str "1RB1LF_0LC1RD_---1LA_0RE1RE_1RF0LB_1RB1LD".
Definition tm' := TM_from_str "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB".
Definition tm0 := TM'_from_str "0RJ0R\_0RL1LU_1RJ1R\_1RL0LF_0LF0Ln_1Rc0Lp_1LF1Ln_1Rd1Lp_---0RZ_1Rc0R\_---1RZ_0Lp1R\_0LU1Rj_0LW1Rl_1LU0LF_1LW1Rc_---0R\_---1Rd_---1R\_---1L`_---0LF_---0LH_---1LF_---1LH_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0RL1RL_0LU1Rj_0Rc1Rc_1LU0LF_0Rj---_0Rl0Rc_1Rj0LF_1Rl1Rc_0Lp0LM_1Rj0LO_1R\1LM_0LF1LO_0RJ---_0RL0Rc_1RJ0LF_1RL1Rc_0LF0L^_1Rc0L`_1LF1L^_1Rd1L`".
Definition tm0' := TM'_from_str "0RJ---_0RL0Rk_1RJ0L^_1RL1Rk_0L^0Lf_1Rk0Lh_1L^1Lf_1Rl1Lh_---0Rb_1Rk0Rd_---1Rb_0LH1Rd_0LU1RB_0LW1RD_1LU0L^_1LW1Rk_---0Rd_---1Rl_---1Rd_---1Lh_---0L^_---0L`_---1L^_---1L`_0RY0Rd_0R[1LU_1RY1Rd_1R[0L^_0RY0LF_1Rk0LH_0Rd1LF_1Rl1LH_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RL1RL_0LU1RB_0Rk1Rk_1LU0L^_0RB---_0RD0Rk_1RB0L^_1RD1Rk_0LH0LM_1RB0LO_1Rd1LM_0L^1LO".
Definition tm1 := TM'_from_str "0RB0RI_0LC1RH_1RD1LF_1RE1RI_1RB1RI_1LJ0LG_1RI0LC_1RI1RD_1RA0LG_---0LG".
Definition tm2 := TM'_from_str "0RB0RI_0LC1RH_1RD1LF_1RE1RI_1RB1RI_1LJ0LG_1RI0LC_1RI1RD_1RA0LG_1RK0LG_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "jLpdl`F\cU".
Definition mp' := mp_from_str "BLHlDh^dkU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM343.


Module TM344.
Definition tm := TM_from_str "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB".
Definition tm' := TM_from_str "1RB0LB_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB".
Definition tm0 := TM'_from_str "0RJ---_0RL0Rk_1RJ0L^_1RL1Rk_0L^0Lf_1Rk0Lh_1L^1Lf_1Rl1Lh_---0Rb_1Rk0Rd_---1Rb_0LH1Rd_0LU1RB_0LW1RD_1LU0L^_1LW1Rk_---0Rd_---1Rl_---1Rd_---1Lh_---0L^_---0L`_---1L^_---1L`_0RY0Rd_0R[1LU_1RY1Rd_1R[0L^_0RY0LF_1Rk0LH_0Rd1LF_1Rl1LH_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RL1RL_0LU1RB_0Rk1Rk_1LU0L^_0RB---_0RD0Rk_1RB0L^_1RD1Rk_0LH0LM_1RB0LO_1Rd1LM_0L^1LO".
Definition tm0' := TM'_from_str "0RJ---_0RL0Rk_1RJ0L^_1RL1Rk_0L^0LM_1Rk0LO_1L^1LM_1Rl1LO_---0Rb_1Rk0Rd_---1Rb_0LH1Rd_0LU1RB_0LW1RD_1LU0L^_1LW1Rk_---0Rd_---1Rl_---1Rd_---1LO_---0L^_---0L`_---1L^_---1L`_0RY0Rd_0R[1LU_1RY1Rd_1R[0L^_0RY0LF_1Rk0LH_0Rd1LF_1Rl1LH_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RL1RL_0LU1RB_0Rk1Rk_1LU0L^_0RB---_0RD0Rk_1RB0L^_1RD1Rk_0LH0LM_1RB0LO_1Rd1LM_0L^1LO".
Definition tm1 := TM'_from_str "0RB0RI_0LC1RH_1RD1LF_1RE1RI_1RB1RI_1LJ0LG_1RI0LC_1RI1RD_1RA0LG_---0LG".
Definition tm2 := TM'_from_str "0RB0RI_0LC1RH_1RD1LF_1RE1RI_1RB1RI_1LJ0LG_1RI0LC_1RI1RD_1RA0LG_1RK0LG_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "BLHlDh^dkU".
Definition mp' := mp_from_str "BLHlDO^dkU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM344.


Module TM345.
Definition tm := TM_from_str "1RB0LB_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB".
Definition tm' := TM_from_str "1RB0LB_0LC1RE_---1LD_1RB1LA_0RF1RF_1RA0LB".
Definition tm0 := TM'_from_str "0RJ---_0RL0Rk_1RJ0L^_1RL1Rk_0L^0LM_1Rk0LO_1L^1LM_1Rl1LO_---0Rb_1Rk0Rd_---1Rb_0LH1Rd_0LU1RB_0LW1RD_1LU0L^_1LW1Rk_---0Rd_---1Rl_---1Rd_---1LO_---0L^_---0L`_---1L^_---1L`_0RY0Rd_0R[1LU_1RY1Rd_1R[0L^_0RY0LF_1Rk0LH_0Rd1LF_1Rl1LH_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RL1RL_0LU1RB_0Rk1Rk_1LU0L^_0RB---_0RD0Rk_1RB0L^_1RD1Rk_0LH0LM_1RB0LO_1Rd1LM_0L^1LO".
Definition tm0' := TM'_from_str "0RJ---_0RL0Rk_1RJ0L^_1RL1Rk_0L^0LM_1Rk0LO_1L^1LM_1Rl1LO_---0Rb_1Rk0Rd_---1Rb_0LH1Rd_0LU1RB_0LW1RD_1LU0L^_1LW1Rk_---0Rd_---1Rl_---1Rd_---1LO_---0L^_---0L`_---1L^_---1L`_0RJ0Rd_0RL1LU_1RJ1Rd_1RL0L^_0L^0LF_1Rk0LH_1L^1LF_1Rl1LH_0Ri0Rj_0Rk0Rl_1Ri1Rj_1Rk1Rl_0RL1RL_0LU1RB_0Rk1Rk_1LU0L^_0RB---_0RD0Rk_1RB0L^_1RD1Rk_0LH0LM_1RB0LO_1Rd1LM_0L^1LO".
Definition tm1 := TM'_from_str "0RB0RI_0LC1RH_1RD1LF_1RE1RI_1RB1RI_1LJ0LG_1RI0LC_1RI1RD_1RA0LG_---0LG".
Definition tm2 := TM'_from_str "0RB0RI_0LC1RH_1RD1LF_1RE1RI_1RB1RI_1LJ0LG_1RI0LC_1RI1RD_1RA0LG_1RK0LG_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "BLHlDO^dkU".
Definition mp' := mp_from_str "BLHlDO^dkU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM345.


Module TM346.
Definition tm := TM_from_str "1LB0RD_1RC0RF_1LF0RD_0LE1RB_1LC---_1RD0LA".
Definition tm' := TM_from_str "1LB1LC_1RC0RF_1LF0RD_1LE1RB_1RF---_1RD0LA".
Definition tm0 := TM'_from_str "0R[0RY_0RT0R[_1R[1RY_0LN1R[_0LN0LV_0LP0RT_1LN1LV_1LP0Rk_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LG---_0RT0LN_1LG0RL_1RJ1LN_0RL0RY_1LN0R[_1RL1RY_1LV1R[_0Ln0LV_0Lp0RT_1Ln1LV_1Lp0Rk_0Lp0RJ_---0RL_0RT1RJ_---1RL_0Le1LV_0Lg1RZ_1Le1R[_1Lg0LN_1Rk---_0RJ---_1LG---_1RJ---_0LV---_0LX---_1LV---_1LX---_0RZ0RT_0R\0Lp_1RZ0LN_1R\0RT_---0LE_1RT0LG_---1LE_1Rk1LG".
Definition tm0' := TM'_from_str "0R[1Rk_0RT0RJ_1R[1LG_0LN1RJ_0LN0LV_0LP0LX_1LN1LV_1LP1LX_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LG---_0RT0LN_1LG0RL_1RJ1LN_0RL0RY_1LN0R[_1RL1RY_1LV1R[_0Ln0LV_0Lp0RT_1Ln1LV_1Lp0Rk_0Lp0RJ_---0RL_0RT1RJ_---1RL_0Lf1LV_0Lh1RZ_1Lf1R[_1Lh0LN_0Rj---_0Rl---_1Rj---_1Rl---_------_0LV---_1RL---_1LV---_0RZ0RT_0R\0Lp_1RZ0LN_1R\0RT_---0LE_1RT0LG_---1LE_1Rk1LG".
Definition tm1 := TM'_from_str "1LB1RI_0LC0RA_1RF1LD_1LE1LB_0RA0LE_1RG0LE_---0RH_1RA1RF_0RA1RJ_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RI_0LC0RA_1RF1LD_1LE1LB_0RA0LE_1RG0LE_1RK0RH_1RA1RF_0RA1RJ_0RA0RF_1RK1RK".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "TVpGNkZL[J".
Definition mp' := mp_from_str "TVpGNkZL[J".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM346.


Module TM347.
Definition tm := TM_from_str "1LB1LC_1RC0RF_1LF0RD_1LE1RB_1RF---_1RD0LA".
Definition tm' := TM_from_str "1LB1LC_1RC0RF_1LF0RD_0LE1RB_1LC---_1RD0LA".
Definition tm0 := TM'_from_str "0R[1Rk_0RT0RJ_1R[1LG_0LN1RJ_0LN0LV_0LP0LX_1LN1LV_1LP1LX_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LG---_0RT0LN_1LG0RL_1RJ1LN_0RL0RY_1LN0R[_1RL1RY_1LV1R[_0Ln0LV_0Lp0RT_1Ln1LV_1Lp0Rk_0Lp0RJ_---0RL_0RT1RJ_---1RL_0Lf1LV_0Lh1RZ_1Lf1R[_1Lh0LN_0Rj---_0Rl---_1Rj---_1Rl---_------_0LV---_1RL---_1LV---_0RZ0RT_0R\0Lp_1RZ0LN_1R\0RT_---0LE_1RT0LG_---1LE_1Rk1LG".
Definition tm0' := TM'_from_str "0R[1Rk_0RT0RJ_1R[1LG_0LN1RJ_0LN0LV_0LP0LX_1LN1LV_1LP1LX_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LG---_0RT0LN_1LG0RL_1RJ1LN_0RL0RY_1LN0R[_1RL1RY_1LV1R[_0Ln0LV_0Lp0RT_1Ln1LV_1Lp0Rk_0Lp0RJ_---0RL_0RT1RJ_---1RL_0Le1LV_0Lg1RZ_1Le1R[_1Lg0LN_1Rk---_0RJ---_1LG---_1RJ---_0LV---_0LX---_1LV---_1LX---_0RZ0RT_0R\0Lp_1RZ0LN_1R\0RT_---0LE_1RT0LG_---1LE_1Rk1LG".
Definition tm1 := TM'_from_str "1LB1RI_0LC0RA_1RF1LD_1LE1LB_0RA0LE_1RG0LE_---0RH_1RA1RF_0RA1RJ_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RI_0LC0RA_1RF1LD_1LE1LB_0RA0LE_1RG0LE_1RK0RH_1RA1RF_0RA1RJ_0RA0RF_1RK1RK".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "TVpGNkZL[J".
Definition mp' := mp_from_str "TVpGNkZL[J".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM347.


Module TM348.
Definition tm := TM_from_str "1RB1LC_0LC1RE_1RD1LD_1LA0LC_0RF0RA_---0RE".
Definition tm' := TM_from_str "1RB1LD_1LC1RC_0RF0RA_1RE1LE_1LA0LD_---0RC".
Definition tm0 := TM'_from_str "0RJ0LH_0RL1LH_1RJ0LW_1RL1LW_0L^0LV_1Rk0LX_1L^1LV_1RC1LX_1L^0Rb_0LH0Rd_1L`1Rb_0LW1Rd_0LU---_0LW1RJ_1LU1Ra_1LW0LW_0RZ1RC_0R\1LX_1RZ1LX_1R\1L^_0LX0L^_0L^0L`_1LX1L^_1L^1L`_0Rd1L^_1L^0LH_1Rd1L`_1L`0LW_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0Ri0RA_0Rk0RC_1Ri1RA_1Rk1RC_---0LH_0Ri0L^_---0Rd_0RA1L^_---0Ra_---0Rc_---1Ra_---1Rc_------_---0RJ_---0Ra_---0LH".
Definition tm0' := TM'_from_str "0RJ0LH_0RL1LH_1RJ0L__1RL1L__0Lf0L^_1Rk0L`_1Lf1L^_1RC1L`_0RQ0RR_0LH0RT_1RQ1RR_0L_1RT_0LV---_0LX1RJ_1LV1RQ_1LX0L__0Ri0RA_0Rk0RC_1Ri1RA_1Rk1RC_---0LH_0Ri0Lf_---0RT_0RA1Lf_0Rb1RC_0Rd1L`_1Rb1L`_1Rd1Lf_0L`0Lf_0Lf0Lh_1L`1Lf_1Lf1Lh_0RT1Lf_1Lf0LH_1RT1Lh_1Lh0L__0LF0L]_0LH0L__1LF1L]_1LH1L__---0RQ_---0RS_---1RQ_---1RS_------_---0RJ_---0RQ_---0LH".
Definition tm1 := TM'_from_str "0LB0RH_1RE1LC_1LG1LD_1LB1LF_1RA0LF_1LC1LG_0LB0LF_1RI1RE_---1RJ_0RL0RK_0RA0LB_---0RJ".
Definition tm2 := TM'_from_str "0LB0RH_1RE1LC_1LG1LD_1LB1LF_1RA0LF_1LC1LG_0LB0LF_1RI1RE_1RM1RJ_0RL0RK_0RA0LB_1RM0RJ_1RM1RM".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "JHX`CW^dkaAi".
Definition mp' := mp_from_str "JH`hC_fTkQAi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM348.


Module TM349.
Definition tm := TM_from_str "1RB1LD_1RC0RF_1RD0RB_0LE1LA_---1LA_1LB0LA".
Definition tm' := TM_from_str "1RB1LD_1RC1RF_1RD0LB_0LE1LA_---1LA_0RB1RC".
Definition tm0 := TM'_from_str "0RJ---_0RL1RT_1RJ1LF_1RL1L`_1R\0L^_1RK0L`_1RK1L^_1RT1L`_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L`1RR_1RR1R\_1LH1Ri_1Ri1RK_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0LF0R\_0L`0RK_1LF0RK_1L`0RT_---0Rk_1RK1Lg_---1Rk_0L`1LH_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_---0Rk_---1Lg_---1Rk_---1LH_---0LF_---0LH_---1LF_---1LH_0RK0RT_0RT0Lg_1RK1RT_1RT0LH_0LN0LE_0LP0LG_1LN1LE_1LP1LG".
Definition tm0' := TM'_from_str "0RJ---_0RL1RT_1RJ1LF_1RL1L`_1R\0L^_1RK0L`_1RK1L^_1RT1L`_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L`1RR_1RR1R\_1LH1Rj_1Rj1RK_0RZ0R\_0R\0RK_1RZ1R\_1R\1RK_0LF0LM_0L`0LO_1LF1LM_1L`1LO_---0Rl_1RK1Lg_---1Rl_0L`1LH_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_---0Rl_---1Lg_---1Rl_---1LH_---0LF_---0LH_---1LF_---1LH_0RI0RR_0RK0RT_1RI1RR_1RK1RT_0R\0L`_0RK1RR_0RK1LH_0RT1Rj".
Definition tm1 := TM'_from_str "0LB1LH_1LC1LH_---1LD_1RE0LB_1RI1RF_0RE0RG_1RA1RE_1RG1LB_0RA0RE".
Definition tm2 := TM'_from_str "0LB1LH_1LC1LH_1RJ1LD_1RE0LB_1RI1RF_0RE0RG_1RA1RE_1RG1LB_0RA0RE_1RJ1RJ".
Definition l0 := [1;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "\`gFKiTHR".
Definition mp' := mp_from_str "\`gFKjTHR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM349.


Module TM350.
Definition tm := TM_from_str "1RB1LD_1RC1RF_1RD0LB_0LE1LA_---1LA_0RB1RC".
Definition tm' := TM_from_str "1RB1LD_1RC1RF_1RD0RB_0LE1LA_---1LA_1LF1RC".
Definition tm0 := TM'_from_str "0RJ---_0RL1RT_1RJ1LF_1RL1L`_1R\0L^_1RK0L`_1RK1L^_1RT1L`_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L`1RR_1RR1R\_1LH1Rj_1Rj1RK_0RZ0R\_0R\0RK_1RZ1R\_1R\1RK_0LF0LM_0L`0LO_1LF1LM_1L`1LO_---0Rl_1RK1Lg_---1Rl_0L`1LH_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_---0Rl_---1Lg_---1Rl_---1LH_---0LF_---0LH_---1LF_---1LH_0RI0RR_0RK0RT_1RI1RR_1RK1RT_0R\0L`_0RK1RR_0RK1LH_0RT1Rj".
Definition tm0' := TM'_from_str "0RJ---_0RL1RT_1RJ1LF_1RL1L`_1R\0L^_1RK0L`_1RK1L^_1RT1L`_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L`1RR_1RR1R\_1LH1Rj_1Rj1RK_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0LF0R\_0L`0RK_1LF0RK_1L`0RT_---0Rl_1RK1Lg_---1Rl_0L`1LH_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_---0Rl_---1Lg_---1Rl_---1LH_---0LF_---0LH_---1LF_---1LH_1Lp0RR_0RK0RT_1Rj1RR_1RK1RT_0Ln0L`_0Lp1RR_1Ln1LH_1Lp1Rj".
Definition tm1 := TM'_from_str "0LB1LH_1LC1LH_---1LD_1RE0LB_1RI1RF_0RE0RG_1RA1RE_1RG1LB_0RA0RE".
Definition tm2 := TM'_from_str "0LB1LH_1LC1LH_1RJ1LD_1RE0LB_1RI1RF_0RE0RG_1RA1RE_1RG1LB_0RA0RE_1RJ1RJ".
Definition l0 := [1;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "\`gFKjTHR".
Definition mp' := mp_from_str "\`gFKjTHR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM350.


Module TM351.
Definition tm := TM_from_str "1RB1LD_1RC1RF_1RD0RB_0LE1LA_---1LA_1LF1RC".
Definition tm' := TM_from_str "1RB1LD_1RC1RF_1RD0RB_0LE1LA_---1LA_0RB1RC".
Definition tm0 := TM'_from_str "0RJ---_0RL1RT_1RJ1LF_1RL1L`_1R\0L^_1RK0L`_1RK1L^_1RT1L`_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L`1RR_1RR1R\_1LH1Rj_1Rj1RK_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0LF0R\_0L`0RK_1LF0RK_1L`0RT_---0Rl_1RK1Lg_---1Rl_0L`1LH_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_---0Rl_---1Lg_---1Rl_---1LH_---0LF_---0LH_---1LF_---1LH_1Lp0RR_0RK0RT_1Rj1RR_1RK1RT_0Ln0L`_0Lp1RR_1Ln1LH_1Lp1Rj".
Definition tm0' := TM'_from_str "0RJ---_0RL1RT_1RJ1LF_1RL1L`_1R\0L^_1RK0L`_1RK1L^_1RT1L`_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L`1RR_1RR1R\_1LH1Rj_1Rj1RK_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_0LF0R\_0L`0RK_1LF0RK_1L`0RT_---0Rl_1RK1Lg_---1Rl_0L`1LH_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_---0Rl_---1Lg_---1Rl_---1LH_---0LF_---0LH_---1LF_---1LH_0RI0RR_0RK0RT_1RI1RR_1RK1RT_0R\0L`_0RK1RR_0RK1LH_0RT1Rj".
Definition tm1 := TM'_from_str "0LB1LH_1LC1LH_---1LD_1RE0LB_1RI1RF_0RE0RG_1RA1RE_1RG1LB_0RA0RE".
Definition tm2 := TM'_from_str "0LB1LH_1LC1LH_1RJ1LD_1RE0LB_1RI1RF_0RE0RG_1RA1RE_1RG1LB_0RA0RE_1RJ1RJ".
Definition l0 := [1;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "\`gFKjTHR".
Definition mp' := mp_from_str "\`gFKjTHR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM351.


Module TM352.
Definition tm := TM_from_str "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA".
Definition tm0 := TM'_from_str "0RJ1LX_0RL1RC_1RJ1Ln_1RL1Lp_1R\0Ln_1L`0Lp_1LX1Ln_1RC1Lp_0RQ0RZ_0RS0R\_1RQ1RZ_1RS1R\_1L`0LX_0Lh1RJ_1RC1LX_1Lh1Ln_0R\---_1LG1LX_1R\1LX_1LH1Ln_0LF0L^_0LH0L`_1LF1L^_1LH1L`_---0RA_1LH0RC_---1RA_1L`1RC_0Lf0RS_0Lh0LG_1Lf0R\_1Lh1LG_---1RC_---1Lh_---1Lp_---1LG_---0LV_---0LX_---1LV_---1LX_0RS0Ra_0LG0Rc_1RS1Ra_0LH1Rc_0LE---_0LG0LH_1LE---_1LG1LH".
Definition tm0' := TM'_from_str "0RJ1LX_0RL1RC_1RJ1Ln_1RL1Lp_1R\0Ln_1L`0Lp_1LX1Ln_1RC1Lp_0RQ0RZ_0RS0R\_1RQ1RZ_1RS1R\_1L`0LX_0Lh1RJ_1RC1LX_1Lh1Ln_0R\---_1LG1LX_1R\1LX_1LH1Ln_0LF0L^_0LH0L`_1LF1L^_1LH1L`_---0RA_1LH0RC_---1RA_1L`1RC_0Lf0RS_0Lh0LG_1Lf0R\_1Lh1LG_---1RC_---1Lh_---1Lp_---1LG_---0LV_---0LX_---1LV_---1LX_0RS0R\_0LG1LG_1RS1R\_0LH1LH_0LE0LF_0LG0LH_1LE1LF_1LG1LH".
Definition tm1 := TM'_from_str "1RB1LE_1LC1RH_1LJ1LD_1LE1LF_1LG1LC_0LD0LG_1RH1LK_1RI1LF_0RA0RB_---1LE_1LD1LG".
Definition tm2 := TM'_from_str "1RB1LE_1LC1RH_1LJ1LD_1LE1LF_1LG1LC_0LD0LG_1RH1LK_1RI1LF_0RA0RB_1RL1LE_1LD1LG_1RL1RL".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "S\`GXnHCJhp".
Definition mp' := mp_from_str "S\`GXnHCJhp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM352.


Module TM353.
Definition tm := TM_from_str "1RB0LD_1RC0RF_0RD1RA_1LE0RB_0LA0RA_0LD---".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_0RD1RA_1LE0RB_0LA0RA_1LE---".
Definition tm0 := TM'_from_str "0RJ0LG_0RL0RR_1RJ0Lf_1RL1RR_1R[0L]_0Lf0L__1RD1L]_---1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1L]0Lf_1RL---_1RI1Lf_1RR---_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0LG1RT_0RR0R[_1LG1Rk_0Ri0RD_1RD0RI_0LG0RK_1L]1RI_0Lf1RK_0Lf0R[_0Lh0LG_1Lf0RD_1Lh---_0RT0RA_0Lf0RC_1RT1RA_0R[1RC_0LE0RT_0LG0Lf_1LE0Rk_1LG1Lf_0LG---_0RR---_0Lf---_1RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0LG_0RL0RR_1RJ0Lf_1RL1RR_1R[0L]_0Lf0L__1RD1L]_---1L__0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_1L]0Lf_1RL---_1RI1Lf_1RR---_0RY0RB_0R[0RD_1RY1RB_1R[1RD_0LG1RT_0RR0R[_1LG1Rl_0Rj0RD_1RD0RI_0LG0RK_1L]1RI_0Lf1RK_0Lf0R[_0Lh0LG_1Lf0RD_1Lh---_0RT0RA_0Lf0RC_1RT1RA_0R[1RC_0LE0RT_0LG0Lf_1LE0Rl_1LG1Lf_1RD---_0LG---_1L]---_0Lf---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm1 := TM'_from_str "1RB1RK_1RC1RI_1LD1RE_0LG0RC_0RF0RJ_0RC0RI_0LH0LG_1RI1LD_1RA1RF_0LH---_0LG---".
Definition tm2 := TM'_from_str "1RB1RK_1RC1RI_1LD1RE_0LG0RC_0RF0RJ_0RC0RI_0LH0LG_1RI1LD_1RA1RF_0LH1RL_0LG1RL_1RL1RL".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "LT[]IRfGDik".
Definition mp' := mp_from_str "LT[]IRfGDjl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM353.


Module TM354.
Definition tm := TM_from_str "1LB0LA_1LC0LE_1LD1RF_1RB---_1LA0RF_1RE1RF".
Definition tm' := TM_from_str "1LB0LA_1LC0LF_0LD1RE_0RE---_1RF1RE_1LA0RC".
Definition tm0 := TM'_from_str "1L`0LX_1LF0LN_1Rl0Lg_0Rk0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0Rk0LP_0Rl0Rb_---0LG_1Rl1Rb_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0Rb0Rj_---0Rl_1Rb1Rj_---1Rl_0L^1LE_0L`1Rd_1L^1Rk_1L`1Rl_0RJ---_0RL---_1RJ---_1RL---_1Rd---_1LN---_1Rl---_0Rk---_1LX0Ri_1LN0Rk_1Lg1Ri_1LE1Rk_0LF1LN_0LH0Rd_1LF0Rk_1LH0Rl_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0LG1LE_1Rb1Rd_1LG1Rk_1Rj1Rl".
Definition tm0' := TM'_from_str "1L_0LX_1LF0LN_1Rd0Lo_0RS0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RS0LP_0Rd0Rj_---0LG_1Rd1Rj_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0Rj0Rb_---0Rd_1Rj1Rb_---1Rd_0L]1LE_0L_1Rl_1L]1RS_1L_1Rd_0Ra---_0Rc---_1Ra---_1Rc---_1LN---_0Rl---_0RS---_0Rd---_0Rj0Rb_0Rl0Rd_1Rj1Rb_1Rl1Rd_0LG1LE_1Rj1Rl_1LG1RS_1Rb1Rd_1LX0RQ_1LN0RS_1Lo1RQ_1LE1RS_0LF1LN_0LH0Rl_1LF0RS_1LH0Rd".
Definition tm1 := TM'_from_str "0RB0RM_1LC1RJ_0LD0LC_0LH0LE_1LF0RJ_0LL0LG_1LD1LC_1LI1RM_0RJ---_1RK1RA_1LD0RJ_1LH1LE_1RB1RM".
Definition tm2 := TM'_from_str "0RB0RM_1LC1RJ_0LD0LC_0LH0LE_1LF0RJ_0LL0LG_1LD1LC_1LI1RM_0RJ1RN_1RK1RA_1LD0RJ_1LH1LE_1RB1RM_1RN1RN".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "jdENgFGX`kbPl".
Definition mp' := mp_from_str "blENoFGX_SjPd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM354.


Module TM355.
Definition tm := TM_from_str "1LB0LA_1LC0LF_0LD1RE_0RE---_1RF1RE_1LA0RC".
Definition tm' := TM_from_str "1LB0LA_1LC0LF_0LD1RE_0RE---_1RF1RE_1LA0RE".
Definition tm0 := TM'_from_str "1L_0LX_1LF0LN_1Rd0Lo_0RS0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RS0LP_0Rd0Rj_---0LG_1Rd1Rj_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0Rj0Rb_---0Rd_1Rj1Rb_---1Rd_0L]1LE_0L_1Rl_1L]1RS_1L_1Rd_0Ra---_0Rc---_1Ra---_1Rc---_1LN---_0Rl---_0RS---_0Rd---_0Rj0Rb_0Rl0Rd_1Rj1Rb_1Rl1Rd_0LG1LE_1Rj1Rl_1LG1RS_1Rb1Rd_1LX0RQ_1LN0RS_1Lo1RQ_1LE1RS_0LF1LN_0LH0Rl_1LF0RS_1LH0Rd".
Definition tm0' := TM'_from_str "1L_0LX_1LF0LN_1Rd0Lo_0Rc0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0Rc0LP_0Rd0Rj_---0LG_1Rd1Rj_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0Rj0Rb_---0Rd_1Rj1Rb_---1Rd_0L]1LE_0L_1Rl_1L]1Rc_1L_1Rd_0Ra---_0Rc---_1Ra---_1Rc---_1LN---_0Rl---_0Rc---_0Rd---_0Rj0Rb_0Rl0Rd_1Rj1Rb_1Rl1Rd_0LG1LE_1Rj1Rl_1LG1Rc_1Rb1Rd_1LX0Ra_1LN0Rc_1Lo1Ra_1LE1Rc_0LF1LN_0LH0Rl_1LF0Rc_1LH0Rd".
Definition tm1 := TM'_from_str "0RB0RM_1LC1RJ_0LD0LC_0LH0LE_1LF0RJ_0LL0LG_1LD1LC_1LI1RM_0RJ---_1RK1RA_1LD0RJ_1LH1LE_1RB1RM".
Definition tm2 := TM'_from_str "0RB0RM_1LC1RJ_0LD0LC_0LH0LE_1LF0RJ_0LL0LG_1LD1LC_1LI1RM_0RJ1RN_1RK1RA_1LD0RJ_1LH1LE_1RB1RM_1RN1RN".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "blENoFGX_SjPd".
Definition mp' := mp_from_str "blENoFGX_cjPd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM355.


Module TM356.
Definition tm := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_1RC---".
Definition tm' := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LC---".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1LV_1RC0RJ_1L_0RS_0L_0RA_1RA0RQ_1LV0RS_1LX1RQ_1Lm1RS_0LV1RJ_0LX0LV_1LV1RA_1LX1LV_0RC0Lh_1Lh0LX_1RC0L__1L_---_0Lf0L]_0Lh0L__1Lf1L]_1Lh1L__1RA1Lh_1LV---_1LX1L__1Lm---_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0RB1RA_0RD1LV_1RB1LX_1RD1Lm_1Lm0LV_1RJ0LX_1RS1LV_1RA1LX_0RR---_0RT---_1RR---_1RT---_0LX---_0Lm---_1LX---_1Lm---".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1LV_1RC0RJ_1L_0RS_0L_0RA_1RA0RQ_1LV0RS_1LX1RQ_1Ln1RS_0LV1RJ_0LX0LV_1LV1RA_1LX1LV_0RC0Lh_1Lh0LX_1RC0L__1L_---_0Lf0L]_0Lh0L__1Lf1L]_1Lh1L__1RA1Lh_1LV---_1LX1L__1Ln---_0LV0Ln_0LX0Lp_1LV1Ln_1LX1Lp_0RB1RA_0RD1LV_1RB1LX_1RD1Ln_1Ln0LV_1RJ0LX_1RS1LV_1RA1LX_1RA---_1LV---_1LX---_1Ln---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE1RJ_1RJ1RJ".
Definition l0 := [1;0;0;0;0;0;1;1]%N.
Definition mp := mp_from_str "AJVhX_SCm".
Definition mp' := mp_from_str "AJVhX_SCn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM356.


Module TM357.
Definition tm := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LC---".
Definition tm' := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA0RD_1LC---".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1LV_1RC0RJ_1L_0RS_0L_0RA_1RA0RQ_1LV0RS_1LX1RQ_1Ln1RS_0LV1RJ_0LX0LV_1LV1RA_1LX1LV_0RC0Lh_1Lh0LX_1RC0L__1L_---_0Lf0L]_0Lh0L__1Lf1L]_1Lh1L__1RA1Lh_1LV---_1LX1L__1Ln---_0LV0Ln_0LX0Lp_1LV1Ln_1LX1Lp_0RB1RA_0RD1LV_1RB1LX_1RD1Ln_1Ln0LV_1RJ0LX_1RS1LV_1RA1LX_1RA---_1LV---_1LX---_1Ln---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1LV_1RC0RJ_1L_0RS_0L_0RA_1RA0RQ_1LV0RS_1LX1RQ_1Ln1RS_0LV1RJ_0LX0LV_1LV1RA_1LX1LV_0RC0Lh_1Lh0LX_1RC0L__1L_---_0Lf0L]_0Lh0L__1Lf1L]_1Lh1L__1RA1Lh_1LV---_1LX1L__1Ln---_0LV0Ln_0LX0Lp_1LV1Ln_1LX1Lp_0RB0RY_0RD0R[_1RB1RY_1RD1R[_1Ln0Lh_1RJ0LX_1RS1Lh_1RA1LX_1RA---_1LV---_1LX---_1Ln---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE1RJ_1RJ1RJ".
Definition l0 := [1;0;0;0;0;0;1;1]%N.
Definition mp := mp_from_str "AJVhX_SCn".
Definition mp' := mp_from_str "AJVhX_SCn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM357.


Module TM358.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_0LA---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1LD0LE_0RA0LC_1LC0RA_0LA---".
Definition tm0 := TM'_from_str "0RJ1RJ_0RL---_1RJ1Ln_1RL---_1Le0Ln_1RR0Lp_1RJ1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Ln0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0LG_0LG0LV_1RT0LW_---0RT_0LE0LU_0LG0LW_1LE1LU_1LG1LW_1LG0RA_1LV0RC_1LW1RA_0RK1RC_0LV0RT_0LX0LG_1LV0RK_1LX1LG_0RT---_0LG---_1RT---_------_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ1RJ_0RL---_1RJ1Ln_1RL---_1Le0Ln_1RR0Lp_1RJ1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Ln0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RA0LG_0RC0LV_1RA0LW_1RC0RT_0RT0LU_0LG0LW_0RK1LU_1LG1LW_1LG0RA_1LV0RC_1LW1RA_0RK1RC_0LV0RT_0LX0LG_1LV0RK_1LX1LG_0RT---_0LG---_1RT---_------_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_0LE---".
Definition tm2 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_0LE1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "KR^WGJTeVg`In".
Definition mp' := mp_from_str "KR^WGJTeVg`In".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM358.


Module TM359.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1LD0LE_0RA0LC_1LC0RA_0LA---".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_0RC---".
Definition tm0 := TM'_from_str "0RJ1RJ_0RL---_1RJ1Ln_1RL---_1Le0Ln_1RR0Lp_1RJ1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Ln0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RA0LG_0RC0LV_1RA0LW_1RC0RT_0RT0LU_0LG0LW_0RK1LU_1LG1LW_1LG0RA_1LV0RC_1LW1RA_0RK1RC_0LV0RT_0LX0LG_1LV0RK_1LX1LG_0RT---_0LG---_1RT---_------_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ1RJ_0RL---_1RJ1Lm_1RL---_1Le0Lm_1RR0Lo_1RJ1Lm_1RI1Lo_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Lm0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0LG_0LG0LV_1RT0LW_---0RT_0LE0LU_0LG0LW_1LE1LU_1LG1LW_1LG0RA_1LV0RC_1LW1RA_0RK1RC_0LV0RT_0LX0LG_1LV0RK_1LX1LG_0RQ---_0RS---_1RQ---_1RS---_0LG---_0LV---_1LG---_1LV---".
Definition tm1 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_0LE---".
Definition tm2 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_0LE1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "KR^WGJTeVg`In".
Definition mp' := mp_from_str "KR^WGJTeVg`Im".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM359.


Module TM360.
Definition tm := TM_from_str "1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_0RD---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0LE_0LF0LC_1LC0RF_1RB0LA".
Definition tm0 := TM'_from_str "0RJ0RT_0RL---_1RJ1RT_1RL---_1Le0Lm_1RR0Lo_1RJ1Lm_1RI1Lo_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Lm0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0LG_1Le0LV_1RT0LW_---0RT_0LE0LU_0LG0LW_1LE1LU_1LG1LW_1LG0RA_1LV0RC_1LW1RA_0RK1RC_0LV0RT_0LX1Le_1LV0RK_1LX1RJ_0RY---_0R[---_1RY---_1R[---_1Le---_0L^---_1RJ---_1L^---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1Le---_1RR---_1RJ---_1RI---_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1LE0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0Lo_1Le0LV_1RT0LW_---0RT_0Lm0LU_0Lo0LW_1Lm1LU_1Lo1LW_1Lo0Ri_1LV0Rk_1LW1Ri_0RK1Rk_0LV0RT_0LX1Le_1LV0RK_1LX1RJ_0RJ0RT_0RL---_1RJ1RT_1RL---_1Le0LE_1RR0LG_1RJ1LE_1RI1LG".
Definition tm1 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_1LH---".
Definition tm2 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_1LH1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "KR^WGJTeVg`Im".
Definition mp' := mp_from_str "KR^WoJTeVg`IE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM360.


Module TM361.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD0LE_0LF0LC_1LC0RF_1RB0LA".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RF_1RB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1Le---_1RR---_1RJ---_1RI---_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1LE0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0Lo_1Le0LV_1RT0LW_---0RT_0Lm0LU_0Lo0LW_1Lm1LU_1Lo1LW_1Lo0Ri_1LV0Rk_1LW1Ri_0RK1Rk_0LV0RT_0LX1Le_1LV0RK_1LX1RJ_0RJ0RT_0RL---_1RJ1RT_1RL---_1Le0LE_1RR0LG_1RJ1LE_1RI1LG".
Definition tm0' := TM'_from_str "0RJ0RT_0RL---_1RJ1RT_1RL---_1Le0Lm_1RR0Lo_1RJ1Lm_1RI1Lo_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Lm0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0LG_1Le0LV_1RT0LW_---0RT_0LE0LU_0LG0LW_1LE1LU_1LG1LW_1LG0Ri_1LV0Rk_1LW1Ri_0RK1Rk_0LV0RT_0LX---_1LV0RK_1LX---_0RJ---_0RL---_1RJ---_1RL---_1Le---_1RR---_1RJ---_1RI---".
Definition tm1 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_1LH---".
Definition tm2 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_1LH1RN_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "KR^WoJTeVg`IE".
Definition mp' := mp_from_str "KR^WGJTeVg`Im".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM361.


Module TM362.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_1LC---".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1LD0LE_0LA0LC_1LC0RF_1RB---".
Definition tm0 := TM'_from_str "0RJ1L`_0RL---_1RJ1Lg_1RL---_1Le0Ln_1RR0Lp_1RJ1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Ln0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0LG_0LX0LV_1RT0LW_---0RT_0LE0LU_0LG0LW_1LE1LU_1LG1LW_1LG0RA_1LV0RC_1LW1RA_0RK1RC_0LV0RT_0LX0LX_1LV0RK_1LX1LX_1LG---_1LV---_1LW---_0RK---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ1L`_0RL---_1RJ1Lg_1RL---_1Le0Lf_1RR0Lh_1RJ1Lf_1RI1Lh_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0LW1L^_0RT0RR_1LW0RJ_0RK0RI_1RJ0L`_1L^0RJ_1Lf0Lg_1Le1RJ_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RT0LG_0LX0LV_1RT0LW_---0RT_0LE0LU_0LG0LW_1LE1LU_1LG1LW_1LG0Ri_1LV0Rk_1LW1Ri_0RK1Rk_0LV0RT_0LX---_1LV0RK_1LX---_0RJ---_0RL---_1RJ---_1RL---_1Le---_1RR---_1RJ---_1RI---".
Definition tm1 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_0LN---_1LK1LJ".
Definition tm2 := TM'_from_str "1RB1RL_1LC0RF_0LE0LD_1LC1LH_1RF1LM_0RG0RA_1LH1RF_0LI0RG_0LK0LJ_1LI0RA_1LE1LD_0RB0RL_0LN1RO_1LK1LJ_1RO1RO".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "KR^WGJTeVg`InX".
Definition mp' := mp_from_str "KR^WGJTeVg`IfX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM362.


Module TM363.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD0LF_1RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LD---".
Definition tm0 := TM'_from_str "0RJ1RI_0RL1L^_1RJ1L`_1RL1Lm_1Lm0L^_1RR0L`_1R[1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lg1L^_1RK0RR_1Lg0R[_0Lg0RI_1RI0RY_1L^0R[_1L`1RY_1Lm1R[_0L^1RR_0L`0L^_1L^1RI_1L`1L^_0RK0LH_1LH0L`_1RK0Lg_1Lg---_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI1LH_1L^---_1L`1Lg_1Lm---_0L^0Lm_0L`0Lo_1L^1Lm_1L`1Lo_0RZ---_0R\---_1RZ---_1R\---_0L`---_0Lm---_1L`---_1Lm---".
Definition tm0' := TM'_from_str "0RJ1RI_0RL1L^_1RJ1L`_1RL1Ln_1Ln0L^_1RR0L`_1R[1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lg1L^_1RK0RR_1Lg0R[_0Lg0RI_1RI0RY_1L^0R[_1L`1RY_1Ln1R[_0L^1RR_0L`0L^_1L^1RI_1L`1L^_0RK0LH_1LH0L`_1RK0Lg_1Lg---_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI1LH_1L^---_1L`1Lg_1Ln---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_1RI---_1L^---_1L`---_1Ln---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1LB0RG_0LC0LE_1RF1LD_1LC1LE_1LB1LH_0RA0RF_1RI0LE_0LD---_1RA1RF".
Definition tm2 := TM'_from_str "1LB0RG_0LC0LE_1RF1LD_1LC1LE_1LB1LH_0RA0RF_1RI0LE_0LD1RJ_1RA1RF_1RJ1RJ".
Definition l0 := [1;1;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "R^H`gI[mK".
Definition mp' := mp_from_str "R^H`gI[nK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM363.


Module TM364.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LD---".
Definition tm' := TM_from_str "1RB0RE_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LD---".
Definition tm0 := TM'_from_str "0RJ1RI_0RL1L^_1RJ1L`_1RL1Ln_1Ln0L^_1RR0L`_1R[1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lg1L^_1RK0RR_1Lg0R[_0Lg0RI_1RI0RY_1L^0R[_1L`1RY_1Ln1R[_0L^1RR_0L`0L^_1L^1RI_1L`1L^_0RK0LH_1LH0L`_1RK0Lg_1Lg---_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI1LH_1L^---_1L`1Lg_1Ln---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_1RI---_1L^---_1L`---_1Ln---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1Ln0LH_1RR0L`_1R[1LH_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lg1L^_1RK0RR_1Lg0R[_0Lg0RI_1RI0RY_1L^0R[_1L`1RY_1Ln1R[_0L^1RR_0L`0L^_1L^1RI_1L`1L^_0RK0LH_1LH0L`_1RK0Lg_1Lg---_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI1LH_1L^---_1L`1Lg_1Ln---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_1RI---_1L^---_1L`---_1Ln---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1LB0RG_0LC0LE_1RF1LD_1LC1LE_1LB1LH_0RA0RF_1RI0LE_0LD---_1RA1RF".
Definition tm2 := TM'_from_str "1LB0RG_0LC0LE_1RF1LD_1LC1LE_1LB1LH_0RA0RF_1RI0LE_0LD1RJ_1RA1RF_1RJ1RJ".
Definition l0 := [1;1;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "R^H`gI[nK".
Definition mp' := mp_from_str "R^H`gI[nK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM364.


Module TM365.
Definition tm := TM_from_str "1LB1RC_1RA1RD_1RD0RC_0RE0LD_1LA0RF_0RC---".
Definition tm' := TM_from_str "1LB1RC_1RA1RD_1RD0RC_0RE0LD_1LA1RF_1LC---".
Definition tm0 := TM'_from_str "0RT0RR_0LP0RT_1RT1RR_0L]1RT_0LN1Rc_0LP1RZ_1LN0L]_1LP1RQ_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0L]1L]_1R\0L]_1L]1Ri_1RS1L]_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_1L]0Rc_0L]0RZ_1Ri0LP_1L]0RQ_0Ra1RS_0Rc0LP_1Ra1L]_1Rc0L]_0LP0L]_0RQ0L__1LP1L]_---1L__1RS0Ri_0RS0Rk_1L]1Ri_1RS1Rk_0LF0RZ_0LH---_1LF0RQ_1LH---_0RQ---_0RS---_1RQ---_1RS---_0Rc---_0RZ---_0LP---_0RQ---".
Definition tm0' := TM'_from_str "0RT0RR_0LP0RT_1RT1RR_0L]1RT_0LN1Rc_0LP1RZ_1LN0L]_1LP1RQ_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0L]1L]_1R\0L]_1L]1Rj_1RS1L]_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_1L]0Rc_0L]0RZ_1Rj0LP_1L]0RQ_0Ra1RS_0Rc0LP_1Ra1L]_1Rc0L]_0LP0L]_0RQ0L__1LP1L]_---1L__1RS0Rj_0RS0Rl_1L]1Rj_1RS1Rl_0LF0RZ_0LH---_1LF0RQ_1LH---_0LP---_0RQ---_0L]---_1RQ---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "0RB0LD_1LC1RF_0LD0LC_1RE1LC_1RA1RG_0RG---_0RA0RG".
Definition tm2 := TM'_from_str "0RB0LD_1LC1RF_0LD0LC_1RE1LC_1RA1RG_0RG1RH_0RA0RG_1RH1RH".
Definition l0 := [1;1;0;1;0;0;0;0]%N.
Definition mp := mp_from_str "Zc]PSiQ".
Definition mp' := mp_from_str "Zc]PSjQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM365.


Module TM366.
Definition tm := TM_from_str "1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---".
Definition tm' := TM_from_str "1RB1LE_0RC0RA_0RD0RF_1LD1LA_0LA0LE_1RB---".
Definition tm0 := TM'_from_str "0RJ1Rj_0RL1LE_1RJ1Lf_1RL1Le_1RY0Lf_1RJ0Lh_1Rj1Lf_1Lf1Lh_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_1L`0RS_0RJ0LG_0RC0RC_---1LG_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_0L`0RS_1RJ---_1L`0RC_1Lf---_1L`0RC_1Lf1LG_1LH1RC_1Lh1Lg_0L^0LF_0L`0LH_1L^1LF_1L`1LH_0RS1RY_0LG0LE_1RS0Lf_0Lg0Le_0LE0Le_0LG0Lg_1LE1Le_1LG1Lg_0RY---_0RJ---_1RY---_1RJ---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ1Ri_0RL1LE_1RJ1Lf_1RL1Le_1RY0Lf_1RJ0Lh_1Ri1Lf_1Lf1Lh_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_1L`0RS_0RJ0LG_0RC0RC_---1LG_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_0L`0RS_1RJ---_1L`0RC_1Lf---_1L`0RC_1Lf1LG_1LH1RC_1Lh1Lg_0L^0LF_0L`0LH_1L^1LF_1L`1LH_0RS1RY_0LG0LE_1RS0Lf_0Lg0Le_0LE0Le_0LG0Lg_1LE1Le_1LG1Lg_0RJ---_0RL---_1RJ---_1RL---_1RY---_1RJ---_1Ri---_1Lf---".
Definition tm1 := TM'_from_str "1LB0RG_1LB1LC_1LD1LM_0LI0LE_1LF1LJ_1RA0LD_1RH1LD_0RL0RG_1RK1LD_0LF0LJ_0RH---_1RA1RK_1LI1LE".
Definition tm2 := TM'_from_str "1LB0RG_1LB1LC_1LD1LM_0LI0LE_1LF1LJ_1RA0LD_1RH1LD_0RL0RG_1RK1LD_0LF0LJ_0RH1RN_1RA1RK_1LI1LE_1RN1RN".
Definition l0 := [1;1;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "Y`HfgECJGejSh".
Definition mp' := mp_from_str "Y`HfgECJGeiSh".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM366.


Module TM367.
Definition tm := TM_from_str "1LB1LE_1RC0RB_1RD1RC_0LA1LF_1LD1LE_---1RB".
Definition tm' := TM_from_str "1LB1LF_1RC0RB_1RE0LD_---1RB_0LA1LD_1LE1LF".
Definition tm0 := TM'_from_str "0RT1LG_0RI1L`_1RT1Lp_1RI1Lh_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh0R\_1R\0RR_1RK0RT_1RT0RI_0RZ0RR_0R\0RT_1RZ1RR_1R\1RT_0Lf0Lh_1RR1R\_1Lf1RK_1RI1RT_1R\---_0L`0RK_0RR---_0Lh1RK_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp_1LN1LG_---1L`_1Lf1Lp_1RI1Lh_0L^0Lf_0L`0Lh_1L^1Lf_1L`1Lh_---0RJ_---0RL_---1RJ_---1RL_---1R\_---1RR_---1RT_---1RI".
Definition tm0' := TM'_from_str "0RT1LG_0RI1Lh_1RT1L`_1RI1Lp_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lp0Rd_1Rd0RR_1RK0RT_1RT0RI_0Rb---_0Rd0RT_1Rb---_1Rd1RT_0Ln0L]_1RR0L__1Ln1L]_1RI1L__---0RJ_---0RL_---1RJ_---1RL_---1Rd_---1RR_---1RT_---1RI_1Rd---_0Lh0RK_0RR---_0Lp1RK_0LE0L^_0LG0L`_1LE1L^_1LG1L`_1LN1LG_---1Lh_1Ln1L`_1RI1Lp_0Lf0Ln_0Lh0Lp_1Lf1Ln_1Lh1Lp".
Definition tm1 := TM'_from_str "0RB0RG_0LC1RI_1LD1LC_1LE1LK_1LF1LH_1RB0RA_1RB1RG_0LD0LC_1RA1RJ_0RA0RJ_---1RJ".
Definition tm2 := TM'_from_str "0RB0RG_0LC1RI_1LD1LC_1LE1LK_1LF1LH_1RB0RA_1RB1RG_0LD0LC_1RA1RJ_0RA0RJ_1RL1RJ_1RL1RL".
Definition l0 := [1;1;1;1;1;1;0;0]%N.
Definition mp := mp_from_str "R\h`GNTfKIp".
Definition mp' := mp_from_str "RdphGNTnKI`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM367.


Module TM368.
Definition tm := TM_from_str "1RB1RA_1LC0RC_---0LD_0LE0LF_1RE0RA_0LF1LB".
Definition tm' := TM_from_str "1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0L_1Lm_---1RL_1L_1RS_1Le1RD_---0RQ_1Le0RS_---1RQ_1Lm1RS_0LV---_0LX0Le_1LV---_1LX1Le_---1Rd_---0Lm_---1Le_---0LN_---0L]_---0L__---1L]_---1L__0Rd0Lm_0RJ0LX_1Rd0LN_1RJ0Le_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0Rb0RA_0Rd0RC_1Rb1RA_1Rd1RC_1Rd1Le_1RJ0RL_1RC0RS_1RB0RD_0Lm---_0LX1Rd_0LN1L__0Le1Le_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0L_1Lm_---1RL_1L_1RS_1Le1RD_---0RQ_1Le0RS_---1RQ_1Lm1RS_0LV---_0LX0Le_1LV---_1LX1Le_---1Rd_---0Lm_---1Le_---0LN_---0L]_---0L__---1L]_---1L__0Rd0Ri_0RJ0Rk_1Rd1Ri_1RJ1Rk_0Le0Lm_0Lg0LX_1Le1Lm_1Lg1LX_0Rb0RA_0Rd0RC_1Rb1RA_1Rd1RC_1Rd1Le_1RJ0RL_1RC0RS_1RB0RD_0Lm---_0LX1Rd_0LN1L__0Le1Le_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP".
Definition tm1 := TM'_from_str "1LB0RL_1RC1LB_1RC1RD_1RA1RE_0RG0RF_1RG1RF_1LH1RL_0LH0LI_0LJ0LB_---1LK_1LB1LH_---1LB".
Definition tm2 := TM'_from_str "1LB0RL_1RC1LB_1RC1RD_1RA1RE_0RG0RF_1RG1RF_1LH1RL_0LH0LI_0LJ0LB_1RM1LK_1LB1LH_1RM1LB_1RM1RM".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JedCBDLmNX_S".
Definition mp' := mp_from_str "JedCBDLmNX_S".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM368.


Module TM369.
Definition tm := TM_from_str "1RB1RA_0RC0RD_1LD1LE_0LE---_0RA0LF_1LE0LE".
Definition tm' := TM_from_str "1RB1RA_0RC0RD_1LD1RA_0LE---_0RA0LF_1LE0LE".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lm1RS_1RJ1RL_1RB1R[_---1RD_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0Lg0RS_0RL---_1Lg0R[_0RD---_0R[0RB_---1Lf_1Lm1RB_---1Le_0L^0Lf_0L`0Lh_1L^1Lf_1L`1Lh_0RJ---_0Lf---_1RJ---_0Le---_0Le---_0Lg---_1Le---_1Lg---_0RA0RL_0RC0RS_1RA0Lo_1RC0Lm_0RS0Lm_0RL0Lo_0R[1Lm_0RD1Lo_0RB0RJ_1Lf0Lf_1RB1RJ_1Le0Le_0Lf0Le_0Lh0Lg_1Lf1Le_1Lh1Lg".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lm1RS_1RJ1RL_1RB1R[_---1RD_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0Lg0RS_0RL---_1Lg0R[_0RD---_0R[0RB_---0RD_1Lm1RB_---1RD_0L^1RS_0L`1RL_1L^1R[_1L`1RD_0RJ---_0Lf---_1RJ---_0Le---_0Le---_0Lg---_1Le---_1Lg---_0RA0RL_0RC0RS_1RA0Lo_1RC0Lm_0RS0Lm_0RL0Lo_0R[1Lm_0RD1Lo_0RB0RJ_1Lf0Lf_1RB1RJ_1Le0Le_0Lf0Le_0Lh0Lg_1Lf1Le_1Lh1Lg".
Definition tm1 := TM'_from_str "1LB1RF_0LD0LC_0RA0LB_0RG0LE_1LD1LC_0RG0RJ_1RA1RH_1RI---_0RA0RH_1RG1RJ".
Definition tm2 := TM'_from_str "1LB1RF_0LD0LC_0RA0LB_0RG0LE_1LD1LC_0RG0RJ_1RA1RH_1RI1RK_0RA0RH_1RG1RJ_1RK1RK".
Definition l0 := [0;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "SmefoBL[JD".
Definition mp' := mp_from_str "SmefoBL[JD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM369.


Module TM370.
Definition tm := TM_from_str "1LB0LD_0LC1LF_1LD---_0RE1RE_1LA1RD_1LD0RF".
Definition tm' := TM_from_str "1LB1LA_0LC1LF_1LD---_0RE1RE_1LA1RD_1LD0RF".
Definition tm0 := TM'_from_str "1L^1LW_1L`1LP_---1Lp_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_0L^---_0L`---_1L^---_1L`---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1L_1R\_0LF1Lp_0LH1L__1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0L^0Rc_0L`0RZ_1L^0Rd_1L`0Ri".
Definition tm0' := TM'_from_str "1L^1LW_1L`1LP_---1Lp_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0Ri_1Rc1Rd_---1Ri_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ---_0R\---_1RZ---_1R\---_0L^---_0L`---_1L^---_1L`---_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RZ_1LP0R\_1Lp1RZ_1LH1R\_0LF1Lp_0LH1LH_1LF1RZ_1LH1R\_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0L^0Rc_0L`0RZ_1L^0Rd_1L`0Ri".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_1LF0RD_0RE0RD_0RB0RG_0RG1RG_1LH1RA_1LI1LH_1LJ1LC_1LK---_0RB1RB".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_1LF0RD_0RE0RD_0RB0RG_0RG1RG_1LH1RA_1LI1LH_1LJ1LC_1LK1RL_0RB1RB_1RL1RL".
Definition l0 := [0;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "\cpiZ`d_PW^".
Definition mp' := mp_from_str "\cpiZ`dHPW^".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM370.


Module TM371.
Definition tm := TM_from_str "1LB1LA_0LC1LC_1LD0RF_0RE1RE_1LA1RD_---0RC".
Definition tm' := TM_from_str "1LB0LD_0LC1LC_1LD0RF_0RE1RE_1LA1RD_---0RC".
Definition tm0 := TM'_from_str "1L^1LW_1L`1LP_---1LX_0Ri1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0Rc0Rd_---0RQ_1Rc1Rd_---1RQ_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0L^---_0L`0RZ_1L^---_1L`0Ri_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0LH_0Rc1Rc_1LP1LH_0Rd1Rd_1LW0RZ_1LP0R\_1LX1RZ_1LH1R\_0LF1LX_0LH1LH_1LF1RZ_1LH1R\_---0RQ_---0RS_---1RQ_---1RS_---0Rc_------_---0Rd_---0RQ".
Definition tm0' := TM'_from_str "1L^1LW_1L`1LP_---1LX_0Ri1L__0LN0L]_0LP0L__1LN1L]_1LP1L__0Rc0Rd_---0RQ_1Rc1Rd_---1RQ_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0L^---_0L`0RZ_1L^---_1L`0Ri_0Ra0Rb_0Rc0Rd_1Ra1Rb_1Rc1Rd_0LP0L__0Rc1Rc_1LP1L__0Rd1Rd_1LW0RZ_1LP0R\_1LX1RZ_1L_1R\_0LF1LX_0LH1L__1LF1RZ_1LH1R\_---0RQ_---0RS_---1RQ_---1RS_---0Rc_------_---0Rd_---0RQ".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RF_1LG0RD_---0RE_0RF0RD_0RB0RH_0RH1RH_1LI1RA_1LJ1LI_1LK1LC_1LL---_0RB1RB".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RF_1LG0RD_1RM0RE_0RF0RD_0RB0RH_0RH1RH_1LI1RA_1LJ1LI_1LK1LC_1LL1RM_0RB1RB_1RM1RM".
Definition l0 := [0;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "\cXiQZ`dHPW^".
Definition mp' := mp_from_str "\cXiQZ`d_PW^".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM371.


Module TM372.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1RD0RE_1LA---_1LA0LF_1LE0LB".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0RD0RF_1LE---_1LF0LB_1LA0LE".
Definition tm0 := TM'_from_str "0RJ1RI_0RL1Lf_1RJ1Lh_1RL1LM_1R\0Lf_1RR0Lh_1Rc1Lf_1RI1Lh_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Lo0R\_1RK0RR_---0Rc_0Lo0RI_0RZ0Ra_0R\0Rc_1RZ1Ra_1R\1Rc_0Lh1RR_---0Lf_1Lh1RI_---1Lf_0RK---_1LH---_1RK---_1Lo---_0LF---_0LH---_1LF---_1LH---_0RK0LH_1LH1Lo_1RK0Lo_1Lo0R\_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_1RI0R\_1Lf0RR_1Lh1R\_1LM1RR_0Lf0LM_0Lh0LO_1Lf1LM_1Lh1LO".
Definition tm0' := TM'_from_str "0RJ1RI_0RL1Ln_1RJ1Lp_1RL1LM_1R[0Ln_1RR0Lp_1Rk1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_1Lg0R[_1RK0RR_---0Rk_0Lg0RI_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_0Lp1RR_---0Ln_1Lp1RI_---1Ln_1LH---_------_1Lg---_0Rk---_0Lf---_0Lh---_1Lf---_1Lh---_1RI0R[_1Ln0RR_1Lp1R[_1LM1RR_0Ln0LM_0Lp0LO_1Ln1LM_1Lp1LO_0RK0LH_1LH1Lg_1RK0Lg_1Lg0R[_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg".
Definition tm1 := TM'_from_str "0RB0RA_0RC0RG_1LD---_1LE1LI_0LF0LD_1RA1LH_1RJ0LD_1LF1LD_1LD0RC_1RB1RA".
Definition tm2 := TM'_from_str "0RB0RA_0RC0RG_1LD1RK_1LE1LI_0LF0LD_1RA1LH_1RJ0LD_1LF1LD_1LD0RC_1RB1RA_1RK1RK".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "IR\ofHchMK".
Definition mp' := mp_from_str "IR[gnHkpMK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM372.


Module TM373.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1LD1RC_1LA1LE_0RA0LD_1LC---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1LD1RC_1LA1LE_1LC0LD_1LC---".
Definition tm0 := TM'_from_str "0RJ1L`_0RL---_1RJ1RT_1RL---_1L_0Ln_1RR0Lp_1RT1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh1LX_1L_0RR_1Lh0RT_1RT0RI_1RI0RR_1LX0RT_1Lp1RR_1L_1RT_0L^0Lh_0L`1L__1L^1Lh_1L`1RT_0RK1L`_1LX1LF_1RK1RT_---1Lf_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0RA1RR_0RC0LX_1RA0Lp_1RC0L__0RT0L]_0LX0L__0RK1L]_1LX1L__1LH---_0RT---_1Lh---_1RT---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ1L`_0RL---_1RJ1RT_1RL---_1L_0Ln_1RR0Lp_1RT1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh1LX_1L_0RR_1Lh0RT_1RT0RI_1RI0RR_1LX0RT_1Lp1RR_1L_1RT_0L^0Lh_0L`1L__1L^1Lh_1L`1RT_0RK1L`_1LX1LF_1RK1RT_---1Lf_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1LH1RR_0RT0LX_1Lh0Lp_1RT0L__0LV0L]_0LX0L__1LV1L]_1LX1L__1LH---_0RT---_1Lh---_1RT---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB1RA_1LI1LC_0LD0LB_1LE1RA_1LF1LJ_1RG1LK_0RH0RG_1LD0RA_1RH0LK_1LD1LB_1LD---".
Definition tm2 := TM'_from_str "1LB1RA_1LI1LC_0LD0LB_1LE1RA_1LF1LJ_1RG1LK_0RH0RG_1LD0RA_1RH0LK_1LD1LB_1LD1RL_1RL1RL".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "T_fX`HIRFhp".
Definition mp' := mp_from_str "T_fX`HIRFhp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM373.


Module TM374.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1LD1RC_1LA1LE_1LC0LD_1LC---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1LD1RC_1LA1LE_1LC0LD_0RD---".
Definition tm0 := TM'_from_str "0RJ1L`_0RL---_1RJ1RT_1RL---_1L_0Ln_1RR0Lp_1RT1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh1LX_1L_0RR_1Lh0RT_1RT0RI_1RI0RR_1LX0RT_1Lp1RR_1L_1RT_0L^0Lh_0L`1L__1L^1Lh_1L`1RT_0RK1L`_1LX1LF_1RK1RT_---1Lf_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1LH1RR_0RT0LX_1Lh0Lp_1RT0L__0LV0L]_0LX0L__1LV1L]_1LX1L__1LH---_0RT---_1Lh---_1RT---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ1L`_0RL---_1RJ1RT_1RL---_1L_0Ln_1RR0Lp_1RT1Ln_1RI1Lp_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh1LX_1L_0RR_1Lh0RT_1RT0RI_1RI0RR_1LX0RT_1Lp1RR_1L_1RT_0L^0Lh_0L`1L__1L^1Lh_1L`1RT_0RK1L`_1LX1LF_1RK1RT_---1Lf_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1LH1RR_0RT0LX_1Lh0Lp_1RT0L__0LV0L]_0LX0L__1LV1L]_1LX1L__0RY---_0R[---_1RY---_1R[---_1RR---_0LX---_1RI---_1LX---".
Definition tm1 := TM'_from_str "1LB1RA_1LI1LC_0LD0LB_1LE1RA_1LF1LJ_1RG1LK_0RH0RG_1LD0RA_1RH0LK_1LD1LB_1LD---".
Definition tm2 := TM'_from_str "1LB1RA_1LI1LC_0LD0LB_1LE1RA_1LF1LJ_1RG1LK_0RH0RG_1LD0RA_1RH0LK_1LD1LB_1LD1RL_1RL1RL".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "T_fX`HIRFhp".
Definition mp' := mp_from_str "T_fX`HIRFhp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM374.


Module TM375.
Definition tm := TM_from_str "1RB1RA_1LC0RF_0LD0LC_1RE0LE_0RB1RE_0RA---".
Definition tm' := TM_from_str "1RB1RA_1LC0RF_0LD0LC_1RE0LE_0RB0RC_0RA---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_1RA1RL_1LW1Rk_---1RD_1Ri0Ri_1L]0Rk_1Le1Ri_1LU1Rk_0LV0RJ_0LX---_1LV0RB_1LX---_0RK1Le_0L_0L]_1RK0Le_1Le0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0Rb1Ri_0Rd0RK_1Rb1Le_1Rd1RK_1Le0Le_1RK0Lg_1Ri1Le_1Rd1Lg_0RI0Rb_0RK0Rd_1RI1Rb_1RK1Rd_0L_1Le_0RA1RK_1L_1Ri_---1Rd_0RA---_0RC---_1RA---_1RC---_1L]---_0RL---_0Rk---_0RD---".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_1RA1RL_1LW1Rk_---1RD_1Ri0Ri_1L]0Rk_1Le1Ri_1LU1Rk_0LV0RJ_0LX---_1LV0RB_1LX---_0RK1Le_0L_0L]_1RK0Le_1Le0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0Rb1Ri_0Rd0RK_1Rb1Le_1Rd1RK_1Le0Le_1RK0Lg_1Ri1Le_0Le1Lg_0RI0RQ_0RK0RS_1RI1RQ_1RK1RS_0L_1Le_0RA0L]_1L_1Ri_---1L]_0RA---_0RC---_1RA---_1RC---_1L]---_0RL---_0Rk---_0RD---".
Definition tm1 := TM'_from_str "1RB---_0RC0RH_1LD0RA_1LE0LE_0LF1LE_1RG1LE_0RB---_0RJ0RI_1RJ1RI_1LK1RA_0LD0LK".
Definition tm2 := TM'_from_str "1RB1RL_0RC0RH_1LD0RA_1LE0LE_0LF1LE_1RG1LE_0RB1RL_0RJ0RI_1RJ1RI_1LK1RA_0LD0LK_1RL1RL".
Definition l0 := [1;0;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "kAJ]e_iBDLU".
Definition mp' := mp_from_str "kAJ]e_iBDLU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM375.


Module TM376.
Definition tm := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_1RB---".
Definition tm' := TM_from_str "1LB1LF_1LC0LA_1RD0RA_1RE0RD_1LB0RB_1LB---".
Definition tm0 := TM'_from_str "1RY0RI_1LN0RK_1LP1RI_1Lm1RK_0LN1RB_0LP0LN_1LN1RY_1LP1LN_0R[0LX_1LX0LP_1R[0Lg_1Lg---_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ1RY_0R\1LN_1RZ1LP_1R\1Lm_1Lm0LN_1RB0LP_1RK1LN_1RY1LP_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0Lg1LN_1R[0RB_1Lg0RK_0Lg0RY_1RY1LX_1LN---_1LP1Lg_1Lm---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RJ---_0RL---_1RJ---_1RL---_0LP---_0Lm---_1LP---_1Lm---".
Definition tm0' := TM'_from_str "1RY1LX_1LN---_1LP1LG_1Ln---_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0R[0LX_1LX0LP_1R[0LG_1LG---_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Ln0LX_1Rb0LP_1RK1LX_1RY1LP_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0LG1LN_1R[0Rb_1LG0RK_0LG0RY_1RY0RI_1LN0RK_1LP1RI_1Ln1RK_0LN1Rb_0LP0LN_1LN1RY_1LP1LN_1RY---_1LN---_1LP---_1Ln---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;0;0;1;1]%N.
Definition mp := mp_from_str "YBNXPgK[m".
Definition mp' := mp_from_str "YbNXPGK[n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM376.


Module TM377.
Definition tm := TM_from_str "1LB1LF_1LC0LA_1RD0RA_1RE0RD_1LB0RB_1LB---".
Definition tm' := TM_from_str "1LB---_1LC0LF_1RD1LB_1RE0RD_1LB0RB_1LB1LA".
Definition tm0 := TM'_from_str "1RY1LX_1LN---_1LP1LG_1Ln---_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0R[0LX_1LX0LP_1R[0LG_1LG---_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Ln0LX_1Rb0LP_1RK1LX_1RY1LP_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0LG1LN_1R[0Rb_1LG0RK_0LG0RY_1RY0RI_1LN0RK_1LP1RI_1Ln1RK_0LN1Rb_0LP0LN_1LN1RY_1LP1LN_1RY---_1LN---_1LP---_1Ln---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "1RY---_1LN---_1LP---_1LF---_0LN---_0LP---_1LN---_1LP---_0R[0LX_1LX0LP_1R[0Lo_1Lo---_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0RZ1RY_0R\1LN_1RZ1LP_1R\1LF_1LF0LN_1Rb0LP_1RK1LN_1RY1LP_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Lo1LN_1R[0Rb_1Lo0RK_0Lo0RY_1RY0RI_1LN0RK_1LP1RI_1LF1RK_0LN1Rb_0LP0LN_1LN1RY_1LP1LN_1RY1LX_1LN---_1LP1Lo_1LF---_0LN0LF_0LP0LH_1LN1LF_1LP1LH".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RG_0LD0LF_1RA1LE_1LD1LF_1LC1LI_1RH0LF_1RB1RA_0LE1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;0;0;1;1]%N.
Definition mp := mp_from_str "YbNXPGK[n".
Definition mp' := mp_from_str "YbNXPoK[F".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM377.


Module TM378.
Definition tm := TM_from_str "1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA".
Definition tm' := TM_from_str "1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA1LF".
Definition tm0 := TM'_from_str "0RJ0RS_0RL1RY_1RJ1RS_1RL0LE_1RY0LE_---0LG_1Ri1LE_---1LG_0RQ---_0RS---_1RQ---_1RS---_1L`---_0RA---_1RY---_0RS---_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_0L`0RJ_0LE1RY_1L`0RS_1LE1Ri_1L`1RY_1LE0LG_1Lg0LE_1Lf0Lh_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RS1Ri_1RY1LG_1RS1LE_0LE1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_0RA0RS_0RC1RY_1RA1RS_1RC0LE_0RS0LE_1RY0LG_---1LE_1Ri1LG".
Definition tm0' := TM'_from_str "0RJ0RS_0RL1RY_1RJ1RS_1RL0LE_1RY0LE_---0LG_1Ri1LE_---1LG_0RQ---_0RS---_1RQ---_1RS---_1L`---_0RA---_1RY---_0RS---_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_0L`0RJ_0LE1RY_1L`0RS_1LE1Ri_1L`1RY_1LE0LG_1Lg0LE_1Lf0Lh_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RS1Ri_1RY1LG_1RS1LE_0LE1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_0RA0RS_0RC1Ri_1RA1RS_1RC1Lp_0RS0Ln_1RY0Lp_---1Ln_1Ri1Lp".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1LD1LE_1RA0LD_0LF0LJ_1RG1LD_0RH0RI_0RK0RI_1RA1RG_1LF1LJ_0RI---".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1LD1LE_1RA0LD_0LF0LJ_1RG1LD_0RH0RI_0RK0RI_1RA1RG_1LF1LJ_0RI1RL_1RL1RL".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "Y`gEfGiAShJ".
Definition mp' := mp_from_str "Y`gEfGiAShJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM378.


Module TM379.
Definition tm := TM_from_str "1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB".
Definition tm' := TM_from_str "1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---0RA".
Definition tm0 := TM'_from_str "0RJ0RS_0RL1RY_1RJ1RS_1RL0LE_1RY0LE_---0LG_1RA1LE_1RA1LG_0RQ0Ri_0RS0Rk_1RQ1Ri_1RS1Rk_1L`---_0RJ0RJ_1RY---_0RS0RS_0RY0RA_0R[0RC_1RY1RA_1R[1RC_0L`0RS_0LE1RY_1L`0Rk_1LE1RA_1L`1RY_1LE0LG_1Lg0LE_1Lf0Lh_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RS1RA_1RY1LG_1RS1LE_0LE1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_---0RA_---0RA_---1RA_---1RA_---0LN_---0LP_---1LN_---1LP".
Definition tm0' := TM'_from_str "0RJ0RS_0RL1RY_1RJ1RS_1RL0LE_1RY0LE_---0LG_1RA1LE_1RA1LG_0RQ0Ri_0RS0Rk_1RQ1Ri_1RS1Rk_1L`---_0RJ0RJ_1RY---_0RS0RS_0RY0RA_0R[0RC_1RY1RA_1R[1RC_0L`0RS_0LE1RY_1L`0Rk_1LE1RA_1L`1RY_1LE0LG_1Lg0LE_1Lf0Lh_0L^0Le_0L`0Lg_1L^1Le_1L`1Lg_0RS1RA_1RY1LG_1RS1LE_0LE1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_---0RA_---0RC_---1RA_---1RC_---0RS_---1RY_---0Rk_---1RA".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1LD1LE_1RA0LD_0LF0LK_1RG1LD_0RH0RJ_0RJ0RI_---1RG_1RA1RG_1LF1LK".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1LD1LE_1RA0LD_0LF0LK_1RG1LD_0RH0RJ_0RJ0RI_1RL1RG_1RA1RG_1LF1LK_1RL1RL".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "Y`gEfGAJkSh".
Definition mp' := mp_from_str "Y`gEfGAJkSh".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM379.


Module TM380.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RA0LB_0RF0LE_0RC---_0LA0RA".
Definition tm' := TM_from_str "1LB0RD_1LC1LE_1RA0LB_0RF1RA_0RC---_0LA0RA".
Definition tm0 := TM'_from_str "1RB0RY_1LV0R[_1LO1RY_---1R[_0LN0LX_0LP1LV_1LN0RA_1LP0R[_0R[1Ri_1LV---_1R[0LO_1Lf---_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RB1Ri_0RD0LV_1RB0LO_1RD---_0Lh0LM_1Ri0LO_1Lh1LM_1RB1LO_0Ri0RB_0Rk---_1Ri1RB_1Rk---_0LN0Le_1RB0Lg_1LN1Le_0RY1Lg_0RQ---_0RS---_1RQ---_1RS---_1LV---_0LV---_0R[---_1LV---_0LX0RA_0Ri0RC_0Lh1RA_1Ri1RC_0LE0LX_0LG0Ri_1LE1LX_1LG0RB".
Definition tm0' := TM'_from_str "1RB0RY_1LV0R[_1LO1RY_---1R[_0LN0LX_0LP1LV_1LN0RA_1LP0R[_0R[1Ri_1LV---_1R[0LO_1Lf---_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RB1Ri_0RD0LV_1RB0LO_1RD---_0Lh0LM_1Ri0LO_1Lh1LM_1RB1LO_0Ri0RB_0Rk0RD_1Ri1RB_1Rk1RD_0LN0Lh_1RB1Ri_1LN1Lh_0RY1RB_0RQ---_0RS---_1RQ---_1RS---_1LV---_0LV---_0R[---_1LV---_0LX0RA_0Ri0RC_0Lh1RA_1Ri1RC_0LE0LX_0LG0Ri_1LE1LX_1LG0RB".
Definition tm1 := TM'_from_str "0LB0RF_1RC1LE_1LD0RG_1RA0LE_1LD1LH_1RC0RI_1RA1RC_0LD---_0RA0RC".
Definition tm2 := TM'_from_str "0LB0RF_1RC1LE_1LD0RG_1RA0LE_1LD1LH_1RC0RI_1RA1RC_0LD1RJ_0RA0RC_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;0;0]%N.
Definition mp := mp_from_str "iXBVOA[fY".
Definition mp' := mp_from_str "iXBVOA[fY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM380.


Module TM381.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RA0LB_0RF1RA_0RC---_0LA0RA".
Definition tm' := TM_from_str "1LB0RD_1LC0LE_1RA0LB_0RF1RA_1LC---_0LA0RA".
Definition tm0 := TM'_from_str "1RB0RY_1LV0R[_1LO1RY_---1R[_0LN0LX_0LP1LV_1LN0RA_1LP0R[_0R[1Ri_1LV---_1R[0LO_1Lf---_0LV0Lf_0LX0Lh_1LV1Lf_1LX1Lh_0RB1Ri_0RD0LV_1RB0LO_1RD---_0Lh0LM_1Ri0LO_1Lh1LM_1RB1LO_0Ri0RB_0Rk0RD_1Ri1RB_1Rk1RD_0LN0Lh_1RB1Ri_1LN1Lh_0RY1RB_0RQ---_0RS---_1RQ---_1RS---_1LV---_0LV---_0R[---_1LV---_0LX0RA_0Ri0RC_0Lh1RA_1Ri1RC_0LE0LX_0LG0Ri_1LE1LX_1LG0RB".
Definition tm0' := TM'_from_str "1RB0RY_1LV0R[_1LO1RY_---1R[_0LN0LX_0LP1LV_1LN0RA_1LP0R[_0R[1Ri_1LV---_1R[0LO_1Le---_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RB1Ri_0RD0LV_1RB0LO_1RD---_0Lg0LM_1Ri0LO_1Lg1LM_1RB1LO_0Ri0RB_0Rk0RD_1Ri1RB_1Rk1RD_0LN0Lg_1RB1Ri_1LN1Lg_0RY1RB_0R[---_1LV---_1R[---_1Le---_0LV---_0LX---_1LV---_1LX---_0LX0RA_0Ri0RC_0Lg1RA_1Ri1RC_0LE0LX_0LG0Ri_1LE1LX_1LG0RB".
Definition tm1 := TM'_from_str "0LB0RF_1RC1LE_1LD0RG_1RA0LE_1LD1LH_1RC0RI_1RA1RC_0LD---_0RA0RC".
Definition tm2 := TM'_from_str "0LB0RF_1RC1LE_1LD0RG_1RA0LE_1LD1LH_1RC0RI_1RA1RC_0LD1RJ_0RA0RC_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;0;0]%N.
Definition mp := mp_from_str "iXBVOA[fY".
Definition mp' := mp_from_str "iXBVOA[eY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM381.


Module TM382.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1RD0RE_1RA1LD_1RF0RA_1RD---".
Definition tm' := TM_from_str "1LB1RE_1LC0LB_1LD0RE_1RA1LD_1RF0RA_1RD---".
Definition tm0 := TM'_from_str "1L`0Rb_1LV0Rd_0Rb1Rb_1LM1Rd_0LN1R\_0LP0Rb_1LN---_1LP1Rb_1RC0L`_0RA0LV_1L`1L`_1RA0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ0Ra_0R\0Rc_1RZ1Ra_1R\1Rc_1LM0R\_0L`1L`_1Rd---_1L`0Rb_0RB0Rd_0RD1RC_1RB1Rd_1RD1L`_0LO0L^_1Rl0L`_1LO1L^_1RC1L`_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1RD0LX_---0Rl_1L`1LX_---0RC_0RZ---_0R\---_1RZ---_1R\---_1LM---_0L`---_1Rd---_1L`---".
Definition tm0' := TM'_from_str "1L`0Rb_1LV0Rd_0Rb1Rb_1LM1Rd_0LN1R\_0LP0Rb_1LN---_1LP1Rb_1RC0L`_0RA0LV_1L`1L`_1RA0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0Rd0Ra_1RC0Rc_1Rd1Ra_1L`1Rc_0L^0R\_0L`1L`_1L^---_1L`0Rb_0RB0Rd_0RD1RC_1RB1Rd_1RD1L`_0LO0L^_1Rl0L`_1LO1L^_1RC1L`_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1RD0LX_---0Rl_1L`1LX_---0RC_0RZ---_0R\---_1RZ---_1R\---_1LM---_0L`---_1Rd---_1L`---".
Definition tm1 := TM'_from_str "0RB0RH_1RC---_1RD1LG_1LE1RI_0LF0LE_0LG1LG_1RH1LG_0RA1RA_1RB1RH".
Definition tm2 := TM'_from_str "0RB0RH_1RC1RJ_1RD1LG_1LE1RI_0LF0LE_0LG1LG_1RH1LG_0RA1RA_1RB1RH_1RJ1RJ".
Definition l0 := [1;1;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "bl\DMV`Cd".
Definition mp' := mp_from_str "bl\DMV`Cd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM382.


Module TM383.
Definition tm := TM_from_str "1LB---_1RC0RA_1RD0RC_1LE0RB_1LF0LE_1RC0LD".
Definition tm' := TM_from_str "1LB---_1RC0LD_1RD0RC_1LE0RF_1LB0LE_1RC0RA".
Definition tm0 := TM'_from_str "0RS---_------_1RS---_------_0LN---_0LP---_1LN---_1LP---_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1Le1RZ_1RZ---_1RK1RQ_1RQ---_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1Ln_1RR0RZ_1Lg0RK_1RA0RQ_1RQ0RI_1Ln0RK_1L_1RI_1Le1RK_0Lf0R\_0Lh0RS_1Lf0RS_1Lh---_0RS1RZ_1Lf0Ln_1RS0L__0RS0Le_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_0RR0Lp_0RT0RR_1RR0Lg_1RT1RR_1Le0L]_1RZ0L__1RK1L]_1RQ1L_".
Definition tm0' := TM'_from_str "0RS---_1Lf---_1RS---_0RS---_0LN---_0LP---_1LN---_1LP---_0RR0LP_0RT0RR_1RR0Lg_1RT1RR_1Le0L]_1RZ0L__1Rk1L]_1RQ1L__0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1LN_1RR0RZ_1Lg0Rk_1RA0RQ_1RQ0Ri_1LN0Rk_1L_1Ri_1Le1Rk_0Lf0R\_0Lh0RS_1Lf0RS_1Lh---_0RS1RZ_1Lf0LN_1RS0L__0RS0Le_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1Le1RZ_1RZ---_1Rk1RQ_1RQ---".
Definition tm1 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF0RL_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA1RM_1RH1RJ_0RL---".
Definition tm2 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF0RL_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA1RM_1RH1RJ_0RL1RN_1RN1RN".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "R\en_fgZpQKSA".
Definition mp' := mp_from_str "R\eN_fgZPQkSA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM383.


Module TM384.
Definition tm := TM_from_str "1LB---_1RC0LD_1RD0RC_1LE0RF_1LB0LE_1RC0RA".
Definition tm' := TM_from_str "1LB0LA_1RC0LD_1RD0RC_1LA0RE_1RC1RF_0RC---".
Definition tm0 := TM'_from_str "0RS---_1Lf---_1RS---_0RS---_0LN---_0LP---_1LN---_1LP---_0RR0LP_0RT0RR_1RR0Lg_1RT1RR_1Le0L]_1RZ0L__1Rk1L]_1RQ1L__0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0Lg1LN_1RR0RZ_1Lg0Rk_1RA0RQ_1RQ0Ri_1LN0Rk_1L_1Ri_1Le1Rk_0Lf0R\_0Lh0RS_1Lf0RS_1Lh---_0RS1RZ_1Lf0LN_1RS0L__0RS0Le_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1Le1RZ_1RZ---_1Rk1RQ_1RQ---".
Definition tm0' := TM'_from_str "0RS1RZ_1LF0LN_1RS0L__0RS0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0RR_1RR0LG_1RT1RR_1LE0L]_1RZ0L__1Rc1L]_1RQ1L__0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0LG1LN_1RR0RZ_1LG0Rc_1Rj0RQ_1RQ0Ra_1LN0Rc_1L_1Ra_1LE1Rc_0LF0R\_0LH0RS_1LF0RS_1LH---_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_1LE1RZ_1RZ---_1Rc1RQ_1RQ---_0RQ---_0RS---_1RQ---_1RS---_1LN---_0RZ---_0Rc---_0RQ---".
Definition tm1 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF0RL_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA1RM_1RH1RJ_0RL---".
Definition tm2 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF0RL_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA1RM_1RH1RJ_0RL1RN_1RN1RN".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "R\eN_fgZPQkSA".
Definition mp' := mp_from_str "R\EN_FGZPQcSj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM384.


Module TM385.
Definition tm := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA0LF_1RD---".
Definition tm' := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA0LF_1RE---".
Definition tm0 := TM'_from_str "0RS1RZ_1LF0LN_1RS0Lg_1Lm0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0LG_1RR0LG_1RT---_1LE0Le_1RZ0Lg_1RK1Le_1RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0LG1LN_1RR0RZ_1LG0RK_0LG0RQ_1RQ0RI_1LN0RK_1Lg1RI_1LE1RK_0LF0R\_0LH0LF_1LF0RS_1LH1LF_1RQ1LN_1LN---_1Lg1LE_1LE---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0RZ---_0R\---_1RZ---_1R\---_0LG---_1RR---_1LG---_0LG---".
Definition tm0' := TM'_from_str "0RS1RZ_1LF0LN_1RS0Lg_1Lm0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0LG_1RR0LG_1RT---_1LE0Le_1RZ0Lg_1RK1Le_1RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0LG1LN_1RR0RZ_1LG0RK_0LG0RQ_1RQ0RI_1LN0RK_1Lg1RI_1LE1RK_0LF0R\_0LH0LF_1LF0RS_1LH1LF_1RQ1LN_1LN---_1Lg1LE_1LE---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0LG---_------_1LG---".
Definition tm1 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF1LM_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA0LG_1RH1RJ_0LG---".
Definition tm2 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF1LM_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA0LG_1RH1RJ_0LG1RN_1RN1RN".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "R\ENgFGZPQKSm".
Definition mp' := mp_from_str "R\ENgFGZPQKSm".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM385.


Module TM386.
Definition tm := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA0LF_1RE---".
Definition tm' := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA1LF_0LA---".
Definition tm0 := TM'_from_str "0RS1RZ_1LF0LN_1RS0Lg_1Lm0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0LG_1RR0LG_1RT---_1LE0Le_1RZ0Lg_1RK1Le_1RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0LG1LN_1RR0RZ_1LG0RK_0LG0RQ_1RQ0RI_1LN0RK_1Lg1RI_1LE1RK_0LF0R\_0LH0LF_1LF0RS_1LH1LF_1RQ1LN_1LN---_1Lg1LE_1LE---_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0LG---_------_1LG---".
Definition tm0' := TM'_from_str "0RS1RZ_1LF0LN_1RS0Lg_1Ln0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0LG_1RR0LG_1RT---_1LE0Le_1RZ0Lg_1RK1Le_1RQ1Lg_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_0LG1LN_1RR0RZ_1LG0RK_0LG0RQ_1RQ0RI_1LN0RK_1Lg1RI_1LE1RK_0LF0R\_0LH0LF_1LF0RS_1LH1LF_1RQ1LN_1LN---_1Lg1LE_1LE---_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_1RZ---_0LN---_0Lg---_0LE---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF1LM_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA0LG_1RH1RJ_0LG---".
Definition tm2 := TM'_from_str "0RB0RL_1LC1RK_0LD0LC_1RH0LE_1LF1LM_0LI0LG_1LD1LC_1LD0RK_1RJ1LE_0RH0RJ_1RA0LG_1RH1RJ_0LG1RN_1RN1RN".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "R\ENgFGZPQKSm".
Definition mp' := mp_from_str "R\ENgFGZPQKSn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM386.


Module TM387.
Definition tm := TM_from_str "1LB---_1RC1LB_1LE1RD_1RB0RC_1RF0LE_1LB0RA".
Definition tm' := TM_from_str "1LB1RF_1RC1LB_1LE1RD_1RB0RC_1RA0LE_1RD---".
Definition tm0 := TM'_from_str "0R\---_1RS---_1R\---_1LP---_0LN---_0LP---_1LN---_1LP---_0RR0R\_0RT1RS_1RR1R\_1RT1LP_0Lg0LN_1RL0LP_1Lg1LN_1RS1LP_0RC0RZ_1LP0R\_1RC1RZ_1Le1R\_0Lf1RT_0Lh1RC_1Lf1LP_1Lh1RZ_0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_1Le1R\_0LP0RL_1R\---_1LP0RS_0Rj1RS_0Rl0LP_1Rj1LP_1Rl0Le_0LP0Le_1R\0Lg_1LP1Le_---1Lg_0R\0RA_1RS0RC_1R\1RA_1LP1RC_0LN1RL_0LP---_1LN1RS_1LP---".
Definition tm0' := TM'_from_str "0R\0Rj_1RS0Rl_1R\1Rj_1LP1Rl_0LN1RL_0LP---_1LN1RS_1LP---_0RR0R\_0RT1RS_1RR1R\_1RT1LP_0Lg0LN_1RL0LP_1Lg1LN_1RS1LP_0Rl0RZ_1LP0R\_1Rl1RZ_1Le1R\_0Lf1RT_0Lh1Rl_1Lf1LP_1Lh1RZ_0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_1Le1R\_0LP0RL_1R\---_1LP0RS_0RB1RS_0RD0LP_1RB1LP_1RD0Le_0LP0Le_1R\0Lg_1LP1Le_---1Lg_0RZ---_0R\---_1RZ---_1R\---_1RT---_1Rl---_1LP---_1RZ---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LB_1RD1LC_1RH1RE_0RF0RD_1RA1LC_1RF1RD_1RG---".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LB_1RD1LC_1RH1RE_0RF0RD_1RA1LC_1RF1RD_1RG1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "TePSZL\C".
Definition mp' := mp_from_str "TePSZL\l".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM387.


Module TM388.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1LB0LE_0LF1LB_---0LE".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_1RA0RA_0RF0LE_0LD1LB_---1LA".
Definition tm0 := TM'_from_str "0RT0RR_1LP0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RC_0RD1Lm_1RB1L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0RT---_1LP1RD_1RT0Le_1Lg0L`_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_---0RT_0Lm1LP_---1RT_0LN1Lg_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP_------_---1RD_---0Le_---0L`_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RT0RR_1LP0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RC_0RD1L]_1RB1L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Ri---_0Rk1RD_1Ri0Le_1Rk0L`_---0Le_0LP0Lg_---1Le_1LP1Lg_---0RT_0L]1LP_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_---1RC_---0RC_---1L`_---1RC_---0LF_---0LH_---1LF_---1LH".
Definition tm1 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_---0LE_0LD0LF_1RB0LG_1LJ1LC_1RB1RI_1RH1RA_1RI1LG".
Definition tm2 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_1RK0LE_0LD0LF_1RB0LG_1LJ1LC_1RB1RI_1RH1RA_1RI1LG_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "RDgmeN`TCP".
Definition mp' := mp_from_str "RDg]eN`TCP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM388.


Module TM389.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_0RF0LE_0LD1LB_---1LA".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RF0LE_0LD1LB_---1LE".
Definition tm0 := TM'_from_str "0RT0RR_1LP0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RC_0RD1L]_1RB1L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Ri---_0Rk1RD_1Ri0Le_1Rk0L`_---0Le_0LP0Lg_---1Le_1LP1Lg_---0RT_0L]1LP_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_---1RC_---0RC_---1L`_---1RC_---0LF_---0LH_---1LF_---1LH".
Definition tm0' := TM'_from_str "0RT0RR_1LP0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RC_0RD1L]_1RB1L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Rj---_0Rl1RD_1Rj0Le_1Rl0L`_---0Le_0LP0Lg_---1Le_1LP1Lg_---0RT_0L]1LP_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_------_---1RC_---1Le_---1L`_---0Lf_---0Lh_---1Lf_---1Lh".
Definition tm1 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_---0LE_0LD0LF_1RB0LG_1LJ1LC_1RB1RI_1RH1RA_1RI1LG".
Definition tm2 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_1RK0LE_0LD0LF_1RB0LG_1LJ1LC_1RB1RI_1RH1RA_1RI1LG_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "RDg]eN`TCP".
Definition mp' := mp_from_str "RDg]eN`TCP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM389.


Module TM390.
Definition tm := TM_from_str "1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_0LE0LE".
Definition tm0 := TM'_from_str "0RJ0RL_0RL1RS_1RJ1RL_1RL1LH_1L]0Le_0Lg0Lg_1Rd1Le_1Lg1Lg_0RR1LP_0RT1LP_1RR1LP_1RT1LP_0L_0LF_1Rl0LH_1L_1LF_1RS1LH_1RS0Rb_1LN0Rd_1LH1Rb_1L]1Rd_0L^1RL_0L`1LH_1L^---_1L`1Rb_0Rd1Rl_1Lg0LN_1Rd0LH_1Lg0L]_0LN0L]_0LP0L__1LN1L]_1LP1L__0Rj0RQ_0Rl0RS_1Rj1RQ_1Rl1RS_1RT0LP_---0Rl_1LP1LP_---0RS_0RJ---_0RL---_1RJ---_1RL---_1L]---_0Lg---_1Rd---_1Lg---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1L]---_0Lg---_1Rd---_1Lg---_0RR1LP_0RT1LP_1RR1LP_1RT1LP_0L_0Ln_1RD0Lp_1L_1Ln_1RS1Lp_1RS0Rb_1LN0Rd_1Lp1Rb_1L]1Rd_0L^1RL_0L`1Lp_1L^---_1L`1Rb_0Rd1RD_1Lg0LN_1Rd0Lp_1Lg0L]_0LN0L]_0LP0L__1LN1L]_1LP1L__0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_1RT0LP_---0RD_1LP1LP_---0RS_0RL0RL_1RS1RS_1RL1RL_1Lp1Lp_0Le0Le_0Lg0Lg_1Le1Le_1Lg1Lg".
Definition tm1 := TM'_from_str "1RB1LG_1LC1RK_0LD0LC_1RJ0LE_1LF1LF_1LG1LG_1RH1LE_1LE1RI_0RJ0RH_1RA---_1RJ1RH".
Definition tm2 := TM'_from_str "1RB1LG_1LC1RK_0LD0LC_1RJ0LE_1LF1LF_1LG1LG_1RH1LE_1LE1RI_0RJ0RH_1RA1RL_1RJ1RH_1RL1RL".
Definition l0 := [1;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "LT]NHgPSbld".
Definition mp' := mp_from_str "LT]NpgPSbDd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM390.


Module TM391.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RF0LE_0LD1LB_---0LE".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RD0LE_0LF1LB_---0LE".
Definition tm0 := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1L]_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Rj---_0Rl1RD_1Rj0Le_1Rl0L`_---0Le_0LN0Lg_---1Le_1LN1Lg_---0RT_0L]1LN_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_------_---1RD_---0Le_---0L`_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1Lm_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0RZ---_0R\1RD_1RZ0Le_1R\0L`_1R\0Le_0LN0Lg_0L`1Le_1LN1Lg_---0RT_0Lm1LN_---1RT_0LN1Lg_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP_------_---1RD_---0Le_---0L`_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_---0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA".
Definition tm2 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_1RJ0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "RDg]eN`TC".
Definition mp' := mp_from_str "RDgmeN`TC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM391.


Module TM392.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RD0LE_0LF1LB_---0LE".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RF0LE_0LF1LB_---0LE".
Definition tm0 := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1Lm_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0RZ---_0R\1RD_1RZ0Le_1R\0L`_1R\0Le_0LN0Lg_0L`1Le_1LN1Lg_---0RT_0Lm1LN_---1RT_0LN1Lg_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP_------_---1RD_---0Le_---0L`_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1Lm_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Rj---_0Rl1RD_1Rj0Le_1Rl0L`_---0Le_0LN0Lg_---1Le_1LN1Lg_---0RT_0Lm1LN_---1RT_0LN1Lg_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP_------_---1RD_---0Le_---0L`_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_---0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA".
Definition tm2 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_1RJ0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "RDgmeN`TC".
Definition mp' := mp_from_str "RDgmeN`TC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM392.


Module TM393.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RF0LE_0LF1LB_---0LE".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RF0LE_0LD1LB_---1RB".
Definition tm0 := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1Lm_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Rj---_0Rl1RD_1Rj0Le_1Rl0L`_---0Le_0LN0Lg_---1Le_1LN1Lg_---0RT_0Lm1LN_---1RT_0LN1Lg_0Lm0LN_0Lo0LP_1Lm1LN_1Lo1LP_------_---1RD_---0Le_---0L`_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB0RL_0RD1L]_1RB1RL_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Rj---_0Rl1RD_1Rj0Le_1Rl0L`_---0Le_1RD0Lg_---1Le_1LN1Lg_---0RT_0L]1LN_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_---0RJ_---0RL_---1RJ_---1RL_---1Lg_---0Lg_---1RT_---1Lg".
Definition tm1 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_---0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA".
Definition tm2 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_1RJ0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "RDgmeN`TC".
Definition mp' := mp_from_str "RDg]eN`TC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM393.


Module TM394.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RF0LE_0LD1LB_---1RB".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_1RA0RA_0RF0LE_0LD1LB_---0LA".
Definition tm0 := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB0RL_0RD1L]_1RB1RL_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Rj---_0Rl1RD_1Rj0Le_1Rl0L`_---0Le_1RD0Lg_---1Le_1LN1Lg_---0RT_0L]1LN_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_---0RJ_---0RL_---1RJ_---1RL_---1Lg_---0Lg_---1RT_---1Lg".
Definition tm0' := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1L]_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Ri---_0Rk1RD_1Ri0Le_1Rk0L`_---0Le_0LN0Lg_---1Le_1LN1Lg_---0RT_0L]1LN_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_---1RD_---0RD_---0L`_---1RD_---0LE_---0LG_---1LE_---1LG".
Definition tm1 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_---0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA".
Definition tm2 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_1RJ0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "RDg]eN`TC".
Definition mp' := mp_from_str "RDg]eN`TC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM394.


Module TM395.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_0RF0LE_0LD1LB_---0LA".
Definition tm' := TM_from_str "1LB1RC_1RA1LE_0LD0RA_---1RB_1RD0LF_0LE1LB".
Definition tm0 := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1L]_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Ri---_0Rk1RD_1Ri0Le_1Rk0L`_---0Le_0LN0Lg_---1Le_1LN1Lg_---0RT_0L]1LN_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_---1RD_---0RD_---0L`_---1RD_---0LE_---0LG_---1LE_---1LG".
Definition tm0' := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lo1RT_0LN1Lo_0LP1RT_1LN1RT_1LP1RR_0RB0RL_0RD1Le_1RB1RL_1RD1LN_0Lh0Lf_1RD0Lh_1Lh1Lf_1RC1Lh_---0RA_0RD0RC_---1RA_1RD1RC_0L]1RD_0L_0RD_1L]1RC_1L_0RC_---0RJ_---0RL_---1RJ_---1RL_---1Lo_---0Lo_---1RT_---1Lo_0RZ---_0R\1RD_1RZ0Lm_1R\0Lh_---0Lm_1RD0Lo_---1Lm_1LN1Lo_---0RT_0Le1LN_---1RT_0LN1Lo_0Le0LN_0Lg0LP_1Le1LN_1Lg1LP".
Definition tm1 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_---0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA".
Definition tm2 := TM'_from_str "0RB0RI_1LC1RH_1LD1LF_1RJ0LE_0LD0LF_1RB0LG_1LF1LC_1RB1RI_1RH1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "RDg]eN`TC".
Definition mp' := mp_from_str "RDoemNhTC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM395.


Module TM396.
Definition tm := TM_from_str "1LB0LC_1LC0RA_0RD1LE_1RB1RD_1LF0LB_---1RD".
Definition tm' := TM_from_str "1LB1RB_1LC0RA_0RD1LF_---1RE_1RB1RE_1LD0LB".
Definition tm0 := TM'_from_str "0R\0RJ_0RJ0Lp_1Lh1RJ_1RJ0LO_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RZ0RA_1Lp0RC_1RZ1RA_1LO1RC_0LV0LX_0LX1Lp_1LV1LX_1LX0RC_0RY---_0R[1LV_1RY1R\_1R[1LX_1Lp0Lf_0RL0Lh_0RC1Lf_0R\1Lh_0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0Lh1LO_1Lh1RL_1Lh1RC_1RJ1R\_---0RL_0R\0R\_---0Lh_1R\1Lh_0Ln0LM_0Lp0LO_1Ln1LM_1Lp1LO_---0RZ_---0R\_---1RZ_---1R\_---1LO_---1RL_---1RC_---1R\".
Definition tm0' := TM'_from_str "0Rd0RJ_0RJ0RL_1Lp1RJ_1RJ1RL_0LN0Lp_0LP1Lp_1LN1Lp_1LP1RJ_0Rb0RA_1L`0RC_1Rb1RA_1LO1RC_0LV0LX_0LX1L`_1LV1LX_1LX0RC_0RY---_0R[1LV_1RY1Rd_1R[1LX_---0Ln_0RL0Lp_---1Ln_0Rd1Lp_---0Rb_---0Rd_---1Rb_---1Rd_---1LO_---1RL_---1RC_---1Rd_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0Lp1LO_1Lp1RL_1Lp1RC_1RJ1Rd_---0RL_0Rd0Rd_---0Lp_1Rd1Lp_0L^0LM_0L`0LO_1L^1LM_1L`1LO".
Definition tm1 := TM'_from_str "1LB1RG_1LF1LC_0RE1LD_1LI1LB_1RA1RE_0RA0LD_1LD1RH_1LI0RG_---1RE".
Definition tm2 := TM'_from_str "1LB1RG_1LF1LC_0RE1LD_1LI1LB_1RA1RE_0RA0LD_1LD1RH_1LI0RG_1RJ1RE_1RJ1RJ".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LOXh\VCJp".
Definition mp' := mp_from_str "LOXpdVCJ`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM396.


Module TM397.
Definition tm := TM_from_str "1LB1RB_1LC0RA_0RD1LF_---1RE_1RB1RE_1LD0LB".
Definition tm' := TM_from_str "1LB1RB_1LC0RA_0RD1LE_1RB1RD_1LF0LB_---1RD".
Definition tm0 := TM'_from_str "0Rd0RJ_0RJ0RL_1Lp1RJ_1RJ1RL_0LN0Lp_0LP1Lp_1LN1Lp_1LP1RJ_0Rb0RA_1L`0RC_1Rb1RA_1LO1RC_0LV0LX_0LX1L`_1LV1LX_1LX0RC_0RY---_0R[1LV_1RY1Rd_1R[1LX_---0Ln_0RL0Lp_---1Ln_0Rd1Lp_---0Rb_---0Rd_---1Rb_---1Rd_---1LO_---1RL_---1RC_---1Rd_0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0Lp1LO_1Lp1RL_1Lp1RC_1RJ1Rd_---0RL_0Rd0Rd_---0Lp_1Rd1Lp_0L^0LM_0L`0LO_1L^1LM_1L`1LO".
Definition tm0' := TM'_from_str "0R\0RJ_0RJ0RL_1Lh1RJ_1RJ1RL_0LN0Lh_0LP1Lh_1LN1Lh_1LP1RJ_0RZ0RA_1Lp0RC_1RZ1RA_1LO1RC_0LV0LX_0LX1Lp_1LV1LX_1LX0RC_0RY---_0R[1LV_1RY1R\_1R[1LX_1Lp0Lf_0RL0Lh_0RC1Lf_0R\1Lh_0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0Lh1LO_1Lh1RL_1Lh1RC_1RJ1R\_---0RL_0R\0R\_---0Lh_1R\1Lh_0Ln0LM_0Lp0LO_1Ln1LM_1Lp1LO_---0RZ_---0R\_---1RZ_---1R\_---1LO_---1RL_---1RC_---1R\".
Definition tm1 := TM'_from_str "1LB1RG_1LF1LC_0RE1LD_1LI1LB_1RA1RE_0RA0LD_1LD1RH_1LI0RG_---1RE".
Definition tm2 := TM'_from_str "1LB1RG_1LF1LC_0RE1LD_1LI1LB_1RA1RE_0RA0LD_1LD1RH_1LI0RG_1RJ1RE_1RJ1RJ".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LOXpdVCJ`".
Definition mp' := mp_from_str "LOXh\VCJp".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM397.


Module TM398.
Definition tm := TM_from_str "1LB0LF_0RC1LF_0RD1RC_0LE0RA_0RF---_1LA1LD".
Definition tm' := TM_from_str "1LB0LF_0RC1LF_0RD1RC_1LE0RA_1LB---_1LA1LD".
Definition tm0 := TM'_from_str "0RR0LP_1LH0Lg_1RR0Lo_1L`0LF_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ1LP_0RS1Lg_1RQ1Lo_1RS1LF_0RT0Ln_0R[0Lp_0RA1Ln_0RT1Lp_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lp_0RR1R[_1LP1RA_0LP1RT_0RT0RA_---0RC_1Lp1RA_---1RC_0Le0R[_0Lg0LF_1Le0RT_1Lg1LF_0Ri---_0Rk---_1Ri---_1Rk---_0LP---_0Lg---_1LP---_1Lg---_0RT1LP_1LF0LP_1Lp---_1L^0Lo_0LF0L^_0LH0L`_1LF1L^_1LH1L`".
Definition tm0' := TM'_from_str "0RR0LP_1LH0Lh_1RR0Lo_1L`0LF_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ1LP_0RS1Lh_1RQ1Lo_1RS1LF_0RT0Ln_0R[0Lp_0RA1Ln_0RT1Lp_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lp_0RR1R[_1LP1RA_0LP1RT_0RT0RA_---0RC_1Lp1RA_---1RC_0Lf0R[_0Lh0LF_1Lf0RT_1Lh1LF_0RR---_1LH---_1RR---_1L`---_0LN---_0LP---_1LN---_1LP---_0RT1LP_1LF0LP_1Lp---_1L^0Lo_0LF0L^_0LH0L`_1LF1L^_1LH1L`".
Definition tm1 := TM'_from_str "1RB1RA_1LC1RH_1LL1LD_1LI1LE_0LG0LF_1LE1LK_0RA1LC_0RJ0LG_1LG---_0RB0RA_0LI0LE_1LG1LF".
Definition tm2 := TM'_from_str "1RB1RA_1LC1RH_1LL1LD_1LI1LE_0LG0LF_1LE1LK_0RA1LC_0RJ0LG_1LG1RM_0RB0RA_0LI0LE_1LG1LF_1RM1RM".
Definition l0 := [0;1;1;1;0;0;1;1]%N.
Definition mp := mp_from_str "T[p`FoPAgR^H".
Definition mp' := mp_from_str "T[p`FoPAhR^H".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM398.


Module TM399.
Definition tm := TM_from_str "1LB1RA_1RC0LE_---0RD_1LE0RF_1LA1LE_1RA0RB".
Definition tm' := TM_from_str "1LB1RA_1RC0LF_---0RD_1LE0RE_1RA0RB_1LA1LF".
Definition tm0 := TM'_from_str "0R[0RB_1LF0RD_1R[1RB_1Lf1RD_0LN0Lg_0LP1Lf_1LN1Lg_1LP1RD_0RR0LP_0RT0LH_1RR1Lf_1RT0Lh_---0Le_1RD0Lg_---1Le_1Ri1Lg_---0RY_---0R[_---1RY_---1R[_---0LH_---0RB_---1LH_---0RI_1LP0Ri_1LH0Rk_1RD1Ri_1Lh1Rk_0Lf1LF_0Lh0RR_1Lf0RD_1Lh0LP_1Ri1LP_0RD1LH_1Lg1RD_1RD1Lh_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0Lg---_1Lf0LF_1Lg0R[_1RD1LF".
Definition tm0' := TM'_from_str "0R[0RB_1LF0RD_1R[1RB_1Ln1RD_0LN0Lo_0LP1Ln_1LN1Lo_1LP1RD_0RR0LP_0RT0LH_1RR1Ln_1RT0Lp_---0Lm_1RD0Lo_---1Lm_1Ra1Lo_---0RY_---0R[_---1RY_---1R[_---1Ln_---0RB_---1RD_---0RI_0RD0Ra_0LP0Rc_1RD1Ra_1Ln1Rc_0Lf1LF_0Lh0RR_1Lf0RD_1Lh0LP_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0Lo---_1Ln0LF_1Lo0R[_1RD1LF_1Ra1LP_0RD1LH_1Lo1RD_1RD1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm1 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1LE1RA_1RH1LF_1LG1LB_0LE1LB_0RI0RJ_1LG0RA_0RK0LE_---0RL_1RA1RH".
Definition tm2 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1LE1RA_1RH1LF_1LG1LB_0LE1LB_0RI0RJ_1LG0RA_0RK0LE_1RM0RL_1RA1RH_1RM1RM".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "DfhHPgFiBIR[".
Definition mp' := mp_from_str "DnpHPoFaBIR[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM399.


Module TM400.
Definition tm := TM_from_str "1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RE".
Definition tm' := TM_from_str "1RB0RA_1RC1RF_1LD0LC_0RD1LE_1RA0LC_---0RE".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1LW0RT_---0RJ_0LU0Rl_1Rc0RA_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0Lh---_0LU1RB_1Lh---_1LU0Lh_0RC1RJ_1RA0L^_1RC0Lh_1LW0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0RC_0RD1L^_1RB1RC_1RD1LU_1RT0Lf_1RJ0Lh_1Rl1Lf_1RA1Lh_0RB1RJ_0RD0L^_1RB0Lh_1RD0LU_1RT0LU_1RJ0LW_1Rl1LU_1RA1LW_---0Ra_---0Rc_---1Ra_---1Rc_---0RL_---0L^_---0RC_---1L^".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1LW0RT_---0RJ_0LU0Rl_1Rc0RA_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0Lh---_0LU1RB_1Lh---_1LU0Lh_0RC1RJ_1RA0L^_1RC0Lh_1LW0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RY0RC_0R[1L^_1RY1RC_1R[1LU_0RY0Lf_1RJ0Lh_0RC1Lf_1RA1Lh_0RB1RJ_0RD0L^_1RB0Lh_1RD0LU_1RT0LU_1RJ0LW_1Rl1LU_1RA1LW_---0Ra_---0Rc_---1Ra_---1Rc_---0RL_---0L^_---0RC_---1L^".
Definition tm1 := TM'_from_str "1RB0LH_0RC0RK_1RD1RJ_1LE0LF_1LG1LF_0LG0LF_1RI0LH_1RL1LE_0RD0RJ_---1RA_1RI1RL_0RI0RL".
Definition tm2 := TM'_from_str "1RB0LH_0RC0RK_1RD1RJ_1LE0LF_1LG1LF_0LG0LF_1RI0LH_1RL1LE_0RD0RJ_1RM1RA_1RI1RL_0RI0RL_1RM1RM".
Definition l0 := [1;0;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "cBLTWU^hJlCA".
Definition mp' := mp_from_str "cBLTWU^hJlCA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM400.


Module TM401.
Definition tm := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---".
Definition tm' := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD1RF_0LB---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LX1RL_1RY0RB_1LX1R\_1Ri0L`_1RY0Ra_1L`0Rc_1LO1Ra_1LX1Rc_0LV0RB_0LX0RY_1LV0L`_1LX---_0R\1RY_1LV1L`_1R\1LO_0L`1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RB0L`_0RD0RY_1RB0LX_1RD1RY_1LX0LM_1RD0LO_1Rc1LM_1RY1LO_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_0RL0RB_0LV---_0R\0L`_1LV---_0RY---_0R[---_1RY---_1R[---_0RL---_0LV---_0R\---_1LV---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LX1RL_1RY0RB_1LX1R\_1Rj0L`_1RY0Ra_1L`0Rc_1LO1Ra_1LX1Rc_0LV0RB_0LX0RY_1LV0L`_1LX---_0R\1RY_1LV1L`_1R\1LO_0L`1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RB0L`_0RD0RY_1RB0LX_1RD1RY_1LX0LM_1RD0LO_1Rc1LM_1RY1LO_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_0RL0RB_0LV---_0R\0L`_1LV---_0L`---_0RY---_0LX---_1RY---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RJ_1LD1LC_1RE1LF_0RG0LD_1LI0LD_0RB0RH_1RA1RE_0LD0LC_1RE1RK_0RE---".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RJ_1LD1LC_1RE1LF_0RG0LD_1LI0LD_0RB0RH_1RA1RE_0LD0LC_1RE1RK_0RE1RL_1RL1RL".
Definition l0 := [1;0;1;0;0;1;1;1]%N.
Definition mp := mp_from_str "DLX`YOB\Vci".
Definition mp' := mp_from_str "DLX`YOB\Vcj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM401.


Module TM402.
Definition tm := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD1RF_0LB---".
Definition tm' := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD1RF_1LA---".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LX1RL_1RY0RB_1LX1R\_1Rj0L`_1RY0Ra_1L`0Rc_1LO1Ra_1LX1Rc_0LV0RB_0LX0RY_1LV0L`_1LX---_0R\1RY_1LV1L`_1R\1LO_0L`1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RB0L`_0RD0RY_1RB0LX_1RD1RY_1LX0LM_1RD0LO_1Rc1LM_1RY1LO_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_0RL0RB_0LV---_0R\0L`_1LV---_0L`---_0RY---_0LX---_1RY---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LX1RL_1RY0RB_1LX1R\_1Rj0L`_1RY0Ra_1L`0Rc_1LO1Ra_1LX1Rc_0LV0RB_0LX0RY_1LV0L`_1LX---_0R\1RY_1LV1L`_1R\1LO_0L`1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RB0L`_0RD0RY_1RB0LX_1RD1RY_1LX0LM_1RD0LO_1Rc1LM_1RY1LO_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_0RL0RB_0LV---_0R\0L`_1LV---_0Rc---_0RY---_1Rc---_1RY---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RJ_1LD1LC_1RE1LF_0RG0LD_1LI0LD_0RB0RH_1RA1RE_0LD0LC_1RE1RK_0RE---".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RJ_1LD1LC_1RE1LF_0RG0LD_1LI0LD_0RB0RH_1RA1RE_0LD0LC_1RE1RK_0RE1RL_1RL1RL".
Definition l0 := [1;0;1;0;0;1;1;1]%N.
Definition mp := mp_from_str "DLX`YOB\Vcj".
Definition mp' := mp_from_str "DLX`YOB\Vcj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM402.


Module TM403.
Definition tm := TM_from_str "1LB1LC_1RC1LF_0LA0RD_1RE0LD_1LA0RB_0LC---".
Definition tm' := TM_from_str "1LB1LC_1RC1LF_0LA0RD_1RE1LE_1LC0RB_0LC---".
Definition tm0 := TM'_from_str "0R[1LN_1LW1LG_1R[1LV_---1LX_0LN0LV_0LP0LX_1LN1LV_1LP1LX_0RR1LE_0RT---_1RR0RK_1RT---_0LV0Ln_1Rb0Lp_1LV1Ln_1LX1Lp_1Rb0RY_0LG0R[_0Lp1RY_0LX1R[_0LE1LG_0LG0LX_1LE0RK_1LG1LX_0Rb1LG_0Rd0LX_1Rb1LX_1Rd0L]_0LX0L]_1RR0L__1LX1L]_0RK1L__1LX0RI_1LG0RK_1Lp1RI_1LX1RK_0LF0LG_0LH0LW_1LF0R[_1LH1LW_0LN---_0Rb---_0LV---_1Rb---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0R[1LN_1LW1LG_1R[1LV_---1LX_0LN0LV_0LP0LX_1LN1LV_1LP1LX_0RR1LE_0RT---_1RR0RK_1RT---_0LV0Ln_1Rb0Lp_1LV1Ln_1LX1Lp_1Rb0RY_0LG0R[_0Lp1RY_0LX1R[_0LE1LG_0LG0LX_1LE0RK_1LG1LX_0Rb1LG_0Rd1LE_1Rb1LX_1Rd0RK_0LX0Lf_1RR0Lh_1LX1Lf_0RK1Lh_1LN0RI_1LG0RK_1LV1RI_1LX1RK_0LV0LG_0LX0LW_1LV0R[_1LX1LW_0LN---_0Rb---_0LV---_1Rb---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1RB0RA_0LC0RG_1LE1LD_0LC0LH_1RF0LI_1LC0RA_1RF1LH_1LC1LH_1LJ---_1LK0RA_0LE0LD".
Definition tm2 := TM'_from_str "1RB0RA_0LC0RG_1LE1LD_0LC0LH_1RF0LI_1LC0RA_1RF1LH_1LC1LH_1LJ1RL_1LK0RA_0LE0LD_1RL1RL".
Definition l0 := [1;0;1;0;1;0;0;0]%N.
Definition mp := mp_from_str "KRGVNb[XpWE".
Definition mp' := mp_from_str "KRGVNb[XpWE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM403.


Module TM404.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA0RE_1RF---_0LD1RB".
Definition tm' := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA0RE_1RF---_1LF1RB".
Definition tm0 := TM'_from_str "0RK1RR_1LF0LN_1RK0L__0RL0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0Rj_1RR0LG_1RT1Rj_1L_0L]_1RR0L__1Ra1L]_0LG1L__0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0Rj0LF_1LP0RK_---1LF_0LG0Ra_1LN0Rc_1L_1Ra_1LE1Rc_0LF0Rj_0LH---_1LF0RL_1LH---_0Rj---_0Rl---_1Rj---_1Rl---_0Rj---_1RT---_0RL---_1Rj---_0LP0RJ_0Rj0RL_0LG1RJ_1Rj1RL_0L]1R[_0L_0Rj_1L]1RK_1L_0RL".
Definition tm0' := TM'_from_str "0RK1RR_1LF0LN_1RK0L__0RL0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0Rj_1RR0LG_1RT1Rj_1L_0L]_1RR0L__1Ra1L]_0LG1L__0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0Rj0LF_1LP0RK_---1LF_0LG0Ra_1LN0Rc_1L_1Ra_1LE1Rc_0LF0Rj_0LH---_1LF0RL_1LH---_0Rj---_0Rl---_1Rj---_1Rl---_0Rj---_1RT---_0RL---_1Rj---_1Lp0RJ_0Rj0RL_0RL1RJ_1Rj1RL_0Ln1R[_0Lp0Rj_1Ln1RK_1Lp0RL".
Definition tm1 := TM'_from_str "1LB1RI_1LC0RK_0LF0LD_1LE1LM_1RG0LB_0LD1LB_0RA0RH_1RG0LD_0RJ---_0RJ0RK_1RL1RJ_1RA1RH_0LE0LM".
Definition tm2 := TM'_from_str "1LB1RI_1LC0RK_0LF0LD_1LE1LM_1RG0LB_0LD1LB_0RA0RH_1RG0LD_0RJ1RN_0RJ0RK_1RL1RJ_1RA1RH_0LE0LM_1RN1RN".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "[_FGNPRKajLTE".
Definition mp' := mp_from_str "[_FGNPRKajLTE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM404.


Module TM405.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0LE1RF_0RC---".
Definition tm' := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0RC1RF_0RC---".
Definition tm0 := TM'_from_str "0RK1RR_1LF0LN_1RK0L__1RI0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0RS_1RR0LG_1RT1RS_1L_0L]_1RR0L__1Rb1L]_0LG1L__0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0RS0LF_1LP0RK_0Rl1LF_0LG0Rb_1LN0Rd_1L_1Rb_1LE1Rd_0LF1RY_0LH1RS_1LF1RI_1LH---_0Le0Rj_0RS0Rl_1RY1Rj_1RS1Rl_0Le1RY_0Lg---_1Le1RI_1Lg---_0RQ---_0RS---_1RQ---_1RS---_0LG---_0RR---_0Rb---_0LP---".
Definition tm0' := TM'_from_str "0RK1RR_1LF0LN_1RK0L__1RI0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0RS_1RR0LG_1RT1RS_1L_0L]_1RR0L__1Rb1L]_0LG1L__0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0RS0LF_1LP0RK_0Rl1LF_0LG0Rb_1LN0Rd_1L_1Rb_1LE1Rd_0LF1RY_0LH1RS_1LF1RI_1LH---_0RQ0Rj_0RS0Rl_1RQ1Rj_1RS1Rl_0LG1RY_0RR---_0Rb1RI_0LP---_0RQ---_0RS---_1RQ---_1RS---_0LG---_0RR---_0Rb---_0LP---".
Definition tm1 := TM'_from_str "1LB1RI_1LC1RK_0LF0LD_1LE1LN_1RG0LB_0LD1LB_0RA0RH_1RG0LD_0RJ0RL_1RM1RK_0RG0LF_1RJ---_0LD0RI_0LE0LN".
Definition tm2 := TM'_from_str "1LB1RI_1LC1RK_0LF0LD_1LE1LN_1RG0LB_0LD1LB_0RA0RH_1RG0LD_0RJ0RL_1RM1RK_0RG0LF_1RJ1RO_0LD0RI_0LE0LN_1RO1RO".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "[_FGNPRKbSIlYE".
Definition mp' := mp_from_str "[_FGNPRKbSIlYE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM405.


Module TM406.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0RC1RF_0RC---".
Definition tm' := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0RC1RF_0LD---".
Definition tm0 := TM'_from_str "0RK1RR_1LF0LN_1RK0L__1RI0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0RS_1RR0LG_1RT1RS_1L_0L]_1RR0L__1Rb1L]_0LG1L__0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0RS0LF_1LP0RK_0Rl1LF_0LG0Rb_1LN0Rd_1L_1Rb_1LE1Rd_0LF1RY_0LH1RS_1LF1RI_1LH---_0RQ0Rj_0RS0Rl_1RQ1Rj_1RS1Rl_0LG1RY_0RR---_0Rb1RI_0LP---_0RQ---_0RS---_1RQ---_1RS---_0LG---_0RR---_0Rb---_0LP---".
Definition tm0' := TM'_from_str "0RK1RR_1LF0LN_1RK0L__1RI0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0LP_0RT0RS_1RR0LG_1RT1RS_1L_0L]_1RR0L__1Rb1L]_0LG1L__0RY0RI_0R[0RK_1RY1RI_1R[1RK_0LP0R[_0RS0LF_1LP0RK_0Rl1LF_0LG0Rb_1LN0Rd_1L_1Rb_1LE1Rd_0LF1RY_0LH1RS_1LF1RI_1LH---_0RQ0Rj_0RS0Rl_1RQ1Rj_1RS1Rl_0LG1RY_0RR---_0Rb1RI_0LP---_0LP---_0RS---_0LG---_1RS---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB1RI_1LC1RK_0LF0LD_1LE1LN_1RG0LB_0LD1LB_0RA0RH_1RG0LD_0RJ0RL_1RM1RK_0RG0LF_1RJ---_0LD0RI_0LE0LN".
Definition tm2 := TM'_from_str "1LB1RI_1LC1RK_0LF0LD_1LE1LN_1RG0LB_0LD1LB_0RA0RH_1RG0LD_0RJ0RL_1RM1RK_0RG0LF_1RJ1RO_0LD0RI_0LE0LN_1RO1RO".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "[_FGNPRKbSIlYE".
Definition mp' := mp_from_str "[_FGNPRKbSIlYE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM406.


Module TM407.
Definition tm := TM_from_str "1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA".
Definition tm' := TM_from_str "1RB0LE_1LB1RC_1RF1RD_1LA0RA_1LC1LD_---1RA".
Definition tm0 := TM'_from_str "0RJ1RL_0RL0LH_1RJ1RJ_1RL0Lf_1LV0L]_1Rl0L__1RC1L]_1RT1L__0RR0Rb_0RT0Rd_1RR1Rb_1RT1Rd_0L_---_1RJ1LV_1L_1RD_1RJ1RC_0Rd0RA_1Lf0RC_1Rd1RA_1LV1RC_0LF0RT_0LH0Lf_1LF0Rd_1LH1Lf_0RD1RT_0RC1RL_1RD1L__1RC1RJ_0Lf0LV_0Lh0LX_1Lf1LV_1Lh1LX_0Rj0RR_0Rl0RT_1Rj1RR_1Rl1RT_---0L__1RL1RJ_---1L__0Lf1RJ_---0RB_---0RD_---1RB_---1RD_---1RT_---0LV_---1Rd_---1LV".
Definition tm0' := TM'_from_str "0RJ1RL_0RL0LH_1RJ1RJ_1RL0LV_1L^0Le_1Rl0Lg_1RC1Le_1R\1Lg_1LP0RR_0R\0RT_1RC1RR_1R\1RT_0LN---_0LP1L^_1LN1RD_1LP1RC_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_---0Lg_1RL1RJ_---1Lg_0LV1RJ_0RT0RA_1LV0RC_1RT1RA_1L^1RC_0LF0R\_0LH0LV_1LF0RT_1LH1LV_0RD1R\_0RC1RL_1RD1Lg_1RC1RJ_0LV0L^_0LX0L`_1LV1L^_1LX1L`_---0RB_---0RD_---1RB_---1RD_---1R\_---0L^_---1RT_---1L^".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LE_1RA1LD_1LE1LB_1RF1RH_1RA1RG_1RJ1RA_0RA0RG_1RH1RH_---1RK_1RF0LE".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LE_1RA1LD_1LE1LB_1RF1RH_1RA1RG_1RJ1RA_0RA0RG_1RH1RH_1RL1RK_1RF0LE_1RL1RL".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "TVH_fLdJClD".
Definition mp' := mp_from_str "\^HgVLTJClD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM407.


Module TM408.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RA0RE_1RD1RF_0LA---".
Definition tm' := TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RA0RE_1RD1RF_1RA---".
Definition tm0 := TM'_from_str "1Rj0RZ_1LV0R\_1L_1RZ_1LM1R\_0LN1LM_0LP1RZ_1LN1R\_1LP1Rj_0Rc1RZ_1LO0LV_1Rc0L__0Rc0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ1LV_0R\0RZ_1RZ1LM_1R\1RZ_1LM0L]_1RZ0L__1R\1L]_1Rj1L__0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_0LO0RD_1RD0RD_1LO0Rc_1Rc---_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_1LM1LM_1RZ---_1R\1R\_1Rj---_0LX---_0RD---_0LO---_1RD---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "1Rj0RZ_1LV0R\_1L_1RZ_1LM1R\_0LN1LM_0LP1RZ_1LN1R\_1LP1Rj_0Rc1RZ_1LO0LV_1Rc0L__0Rc0LM_0LV0LM_0LX0LO_1LV1LM_1LX1LO_0RZ1LV_0R\0RZ_1RZ1LM_1R\1RZ_1LM0L]_1RZ0L__1R\1L]_1Rj1L__0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_0LO0RD_1RD0RD_1LO0Rc_1Rc---_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_1LM1LM_1RZ---_1R\1R\_1Rj---_0RB---_0RD---_1RB---_1RD---_0LO---_1RD---_1LO---_1Rc---".
Definition tm1 := TM'_from_str "1RB1RI_0RC0RA_1LD1RG_0LE0LD_1RB0LF_1LH0RA_1RC1RA_1LE1LD_0RC---".
Definition tm2 := TM'_from_str "1RB1RI_0RC0RA_1LD1RG_0LE0LD_1RB0LF_1LH0RA_1RC1RA_1LE1LD_0RC1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "cZDMV_\Oj".
Definition mp' := mp_from_str "cZDMV_\Oj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM408.


Module TM409.
Definition tm := TM_from_str "1RB1RE_0RC0RA_1LD1RF_0LD1LE_1RA0LE_1RB---".
Definition tm' := TM_from_str "1RB1RE_0RC0RA_1LD0RF_0LD1LE_1RA0LE_0LE---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1Lf1RL_1RJ0Le_1Rj1Rd_1Rb1Le_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0L_0RS_0RL0RD_1L_0RC_---1RS_1L]0Rj_0Le0Rl_1Lf1Rj_1Lg1Rl_0L^1RS_0L`---_1L^1RC_1L`---_0L]0Rd_1RD1RC_0Lf1Rd_0Lg1Le_0L]0Lf_0L_0Lh_1L]1Lf_1L_1Lh_0RB0RL_0RD1RS_1RB1RL_1RD0Le_1RS0Le_1RD0Lg_1RC1Le_0Le1Lg_0RJ---_0RL---_1RJ---_1RL---_1Lf---_1RJ---_1Rj---_1Rb---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1Lf1RL_1RJ0Le_1Ri1Rd_1Rb1Le_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0L_0RS_0RL0RD_1L_0RC_---1RS_1L]0Ri_0Le0Rk_1Lf1Ri_1Lg1Rk_0L^1RS_0L`---_1L^1RC_1L`---_0L]0Rd_1RD1RC_0Lf1Rd_0Lg1Le_0L]0Lf_0L_0Lh_1L]1Lf_1L_1Lh_0RB0RL_0RD1RS_1RB1RL_1RD0Le_1RS0Le_1RD0Lg_1RC1Le_0Le1Lg_0RL---_1RS---_1RL---_0Le---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1RB1RK_0RC0RA_1LD1RJ_1RE0LH_1RG1RF_1RE0LI_1RC1RA_1RA1LI_1RC0LI_0RG---_0RE1RC".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RA_1LD1RJ_1RE0LH_1RG1RF_1RE0LI_1RC1RA_1RA1LI_1RC0LI_0RG1RL_0RE1RC_1RL1RL".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "CJSfDdLgejb".
Definition mp' := mp_from_str "CJSfDdLgeib".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM409.


Module TM410.
Definition tm := TM_from_str "1RB1RE_0RC0RA_1LD0RF_0LD1LE_1RA0LE_0LE---".
Definition tm' := TM_from_str "1RB1RF_0RC0RA_1LD0RD_0LE---_1RA1LF_1RA0LF".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1Lf1RL_1RJ0Le_1Ri1Rd_1Rb1Le_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0L_0RS_0RL0RD_1L_0RC_---1RS_1L]0Ri_0Le0Rk_1Lf1Ri_1Lg1Rk_0L^1RS_0L`---_1L^1RC_1L`---_0L]0Rd_1RD1RC_0Lf1Rd_0Lg1Le_0L]0Lf_0L_0Lh_1L]1Lf_1L_1Lh_0RB0RL_0RD1RS_1RB1RL_1RD0Le_1RS0Le_1RD0Lg_1RC1Le_0Le1Lg_0RL---_1RS---_1RL---_0Le---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_1Ln1RL_1RJ0Lm_1RY1Rl_1Rj1Lm_0RQ0RA_0RS0RC_1RQ1RA_1RS1RC_0Lg0RS_0RL0RD_1Lg0RC_---1RS_1RC0RY_---0R[_1Ln1RY_---1R[_0L^1RS_0L`---_1L^1RC_1L`---_0RL---_1RD---_1RL---_0Lo---_0Le---_0Lg---_1Le---_1Lg---_0RB0Rl_0RD1RC_1RB1Rl_1RD1Lm_1RS0Ln_1RD0Lp_1RC1Ln_0Lm1Lp_0RB0RL_0RD1RS_1RB1RL_1RD0Lm_1RS0Lm_1RD0Lo_1RC1Lm_0Lm1Lo".
Definition tm1 := TM'_from_str "1RB1RK_0RC0RA_1LD1RJ_1RE0LH_1RG1RF_1RE0LI_1RC1RA_1RA1LI_1RC0LI_0RG---_0RE1RC".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RA_1LD1RJ_1RE0LH_1RG1RF_1RE0LI_1RC1RA_1RA1LI_1RC0LI_0RG1RL_0RE1RC_1RL1RL".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "CJSfDdLgeib".
Definition mp' := mp_from_str "CJSnDlLomYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM410.


Module TM411.
Definition tm := TM_from_str "1RB0LA_1RC---_0LD1RD_0RB0RE_0RF1RC_1LF0LA".
Definition tm' := TM_from_str "1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA".
Definition tm0 := TM'_from_str "0RJ0RT_0RL1Ri_1RJ1RT_1RL0LE_1Ri0LE_---0LG_1R\1LE_---1LG_0RR---_0RT---_1RR---_1RT---_1Lp---_1RK---_0RT---_1Rc---_0RR0RZ_0Ri0R\_1RR1RZ_1Ri1R\_0L]1RR_0L_1Ri_1L]---_1L_1RR_0RI0Ra_0RK0Rc_1RI1Ra_1RK1Rc_0Ri1Lp_---0Ri_0R\0RT_---0R\_0Ri0RR_0Rk0RT_1Ri1RR_1Rk1RT_0Lp1Lp_1Ri1RK_1Lp0RT_1R\1Rc_1Lp0RT_1R\1Ri_1LG1RT_1LE0LE_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG".
Definition tm0' := TM'_from_str "0RJ0RT_0RL1Ri_1RJ1RT_1RL0LE_1Ri0LE_---0LG_1R\1LE_---1LG_0RR---_0RT---_1RR---_1RT---_1Lp---_1RK---_0RT---_1Rc---_0RR0RZ_0Ri0R\_1RR1RZ_1Ri1R\_0L]1RR_0L_1Ri_1L]---_1L_1RR_0RI0Ra_0RK0Rc_1RI1Ra_1RK1Rc_0Ri1Lp_---0Ri_0R\0RT_---0R\_0Ri0RR_0Rk0Ri_1Ri1RR_1Rk1Ri_0Lp0L]_1Ri0L__1Lp1L]_1R\1L__1Lp0RT_1R\1Ri_1LG1RT_1LE0LE_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG".
Definition tm1 := TM'_from_str "1RB---_0RC0RH_1LD0RG_1LD1LE_1RH1LF_1RC0LF_1RC1RH_1RA1RI_1RC1RB".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0RH_1LD0RG_1LD1LE_1RH1LF_1RC0LF_1RC1RH_1RA1RI_1RC1RB_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "KRipGET\c".
Definition mp' := mp_from_str "KRipGET\c".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM411.


Module TM412.
Definition tm := TM_from_str "1RB0RD_1RC---_0LA1RA_0RE1RC_1LE0LF_1RB0LF".
Definition tm' := TM_from_str "1RB0RD_1RC---_0LA1RA_0RE1RC_1LE0LF_0RC0LF".
Definition tm0 := TM'_from_str "0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_1Ra1Lh_---0Ra_1RD0RT_---0RD_0RR---_0RT---_1RR---_1RT---_1Lh---_1RL---_0RT---_1R[---_0RT0RB_0Ra0RD_1RT1RB_1Ra1RD_0LE1RT_0LG1Ra_1LE---_1LG1RR_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_0Lh1Lh_1Ra1RL_1Lh0RT_1RD1R[_1Lh0RT_1RD1Ra_1Lo1RT_1Lm0Lm_0Lf0Lm_0Lh0Lo_1Lf1Lm_1Lh1Lo_0RJ0RT_0RL1Ra_1RJ1RT_1RL0Lm_1Ra0Lm_---0Lo_1RD1Lm_---1Lo".
Definition tm0' := TM'_from_str "0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_1Ra1Lh_---0Ra_1RD0RT_---0RD_0RR---_0RT---_1RR---_1RT---_1Lh---_1RL---_0RT---_1R[---_0RT0RB_0Ra0RD_1RT1RB_1Ra1RD_0LE1RT_0LG1Ra_1LE---_1LG1RR_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_0Lh1Lh_1Ra1RL_1Lh0RT_1RD1R[_1Lh0RT_1RD1Ra_1Lo1RT_1Lm0Lm_0Lf0Lm_0Lh0Lo_1Lf1Lm_1Lh1Lo_0RQ0RT_0RS1Ra_1RQ1RT_1RS0Lm_1Ra0Lm_0RL0Lo_1RD1Lm_0R[1Lo".
Definition tm1 := TM'_from_str "1RB---_1RC1RG_1LD0RB_1LD1LE_1RG1LF_1RC0LF_1RA1RH_1RC1RI_0RC0RG".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RG_1LD0RB_1LD1LE_1RG1LF_1RC0LF_1RA1RH_1RC1RI_0RC0RG_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "LTahomD[R".
Definition mp' := mp_from_str "LTahomD[R".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM412.


Module TM413.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1RD1LE_0RA1RA_0LC1LC_---1LA".
Definition tm' := TM_from_str "1LB0RC_0RC1LF_1RE1LD_0LC1LC_0RA1RA_---1LA".
Definition tm0 := TM'_from_str "1RQ0RQ_---0RS_1Lf1RQ_1LH1RS_0LN0RC_0LP0LW_1LN0RD_1LP1LW_0RC---_0LW1LP_1RC---_0LX1LW_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ1RQ_0R\1RS_1RZ1Lf_1R\1Lh_1Lf0Lf_1LH0Lh_1RQ1Lf_1RS1Lh_0RA0RB_0RC0RD_1RA1RB_1RC1RD_0LW0Lp_0RZ1RZ_1LW1Lp_1RQ1Lf_0RC0RD_0LW1LW_1RC1RD_0LX1LX_0LU0LV_0LW0LX_1LU1LV_1LW1LX_---1LW_---1RQ_---1Lp_---1Lf_---0LF_---0LH_---1LF_---1LH".
Definition tm0' := TM'_from_str "1RQ0RQ_---0RS_1L^1RQ_1LH1RS_0LN0RC_0LP0LW_1LN0RD_1LP1LW_0RQ---_0RS1LP_1RQ---_1RS1LW_0RC0Ln_0LW0Lp_0RD1Ln_1LW1Lp_0Rb1RQ_0Rd1RS_1Rb1L^_1Rd1L`_1L^0L^_1LH0L`_1RQ1L^_1RS1L`_0RC0RD_0LW1LW_1RC1RD_0LX1LX_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RA0RB_0RC0RD_1RA1RB_1RC1RD_0LW0Lp_0Rb1Rb_1LW1Lp_1RQ1L^_---1LW_---1RQ_---1Lp_---1L^_---0LF_---0LH_---1LF_---1LH".
Definition tm1 := TM'_from_str "1LB1RL_0LC0LD_1RL1LB_1RE1LK_1RF1LB_0RA0RG_1LH1RE_1LI1LC_1LC1LJ_---1LH_1LC1LD_0RF1RL".
Definition tm2 := TM'_from_str "1LB1RL_0LC0LD_1RL1LB_1RE1LK_1RF1LB_0RA0RG_1LH1RE_1LI1LC_1LC1LJ_1RM1LH_1LC1LD_0RF1RL_1RM1RM".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "CfWXSZDHPphQ".
Definition mp' := mp_from_str "C^WXSbDHPp`Q".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM413.


Module TM414.
Definition tm := TM_from_str "1LB0RC_0RC1LF_1RE1LD_0LC1LC_0RA1RA_---1LA".
Definition tm' := TM_from_str "1LB0RD_1RC1LC_---1LA_1RF1LE_0LD1LD_0RA1RA".
Definition tm0 := TM'_from_str "1RQ0RQ_---0RS_1L^1RQ_1LH1RS_0LN0RC_0LP0LW_1LN0RD_1LP1LW_0RQ---_0RS1LP_1RQ---_1RS1LW_0RC0Ln_0LW0Lp_0RD1Ln_1LW1Lp_0Rb1RQ_0Rd1RS_1Rb1L^_1Rd1L`_1L^0L^_1LH0L`_1RQ1L^_1RS1L`_0RC0RD_0LW1LW_1RC1RD_0LX1LX_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RA0RB_0RC0RD_1RA1RB_1RC1RD_0LW0Lp_0Rb1Rb_1LW1Lp_1RQ1L^_---1LW_---1RQ_---1Lp_---1L^_---0LF_---0LH_---1LF_---1LH".
Definition tm0' := TM'_from_str "1RY0RY_---0R[_1Lf1RY_1LH1R[_0LN0RC_0LP0L__1LN0RD_1LP1L__0RR---_0RT1LP_1RR---_1RT1L__---0LV_0L_0LX_---1LV_1L_1LX_---1L__---1RY_---1LX_---1Lf_---0LF_---0LH_---1LF_---1LH_0Rj1RY_0Rl1R[_1Rj1Lf_1Rl1Lh_1Lf0Lf_1LH0Lh_1RY1Lf_1R[1Lh_0RC0RD_0L_1L__1RC1RD_0L`1L`_0L]0L^_0L_0L`_1L]1L^_1L_1L`_0RA0RB_0RC0RD_1RA1RB_1RC1RD_0L_0LX_0Rj1Rj_1L_1LX_1RY1Lf".
Definition tm1 := TM'_from_str "1LB1RL_0LC0LD_1RL1LB_1RE1LK_1RF1LB_0RA0RG_1LH1RE_1LI1LC_1LC1LJ_---1LH_1LC1LD_0RF1RL".
Definition tm2 := TM'_from_str "1LB1RL_0LC0LD_1RL1LB_1RE1LK_1RF1LB_0RA0RG_1LH1RE_1LI1LC_1LC1LJ_1RM1LH_1LC1LD_0RF1RL_1RM1RM".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "C^WXSbDHPp`Q".
Definition mp' := mp_from_str "Cf_`[jDHPXhY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM414.


Module TM415.
Definition tm := TM_from_str "1LB1RE_0LC1LF_1RD1LD_1RA0RB_1LC0RD_0LC---".
Definition tm' := TM_from_str "1LB1RE_0LC0LF_1RD1LD_1RA0RB_1LC0RD_0RA---".
Definition tm0 := TM'_from_str "1Rd0Rb_1LW0Rd_1L^1Rb_---1Rd_0LN0L`_0LP1RB_1LN1L`_1LP1RI_0RD1Rd_1LW---_1RD1L^_0LW---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ0Rd_0R\1Rd_1RZ1Rd_1R\1L^_---0L^_1RD0L`_1Rd1L^_1L^1L`_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0Lp---_1LW0LW_1Lp1Rd_1R[1LW_0RK0RY_1R[0R[_1RK1RY_1LW1R[_0LV1LW_0LX0RD_1LV0Rd_1LX1Rd_0RD---_1LW---_1RD---_0LW---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "1Rd0Rb_1LW0Rd_1L^1Rb_---1Rd_0LN0L`_0LP1RB_1LN1L`_1LP1RI_0RD1Rd_1LW---_1RD1L^_0LW---_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0RZ0Rd_0R\1Rd_1RZ1Rd_1R\1L^_---0L^_1RD0L`_1Rd1L^_1L^1L`_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0Lo---_1LW0LW_1Lo1Rd_1R[1LW_0RK0RY_1R[0R[_1RK1RY_1LW1R[_0LV1LW_0LX0RD_1LV0Rd_1LX1Rd_0RA---_0RC---_1RA---_1RC---_0LW---_1R[---_1LW---_0R[---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_---1RE".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_1RH1RE_1RH1RH".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "[BW^dID".
Definition mp' := mp_from_str "[BW^dID".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM415.


Module TM416.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LC---_1RA1RF".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LB---_1RA1RF".
Definition tm0 := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Ra0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0RD_1RD0Rl_1LH---_1Rl0R[_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_1LM1RD_---1Ra_1LH1Rl_---1RR_0RD---_0Ra---_1RD---_1Ra---_0LU---_0LW---_1LU---_1LW---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LO1LM_0LH1RD_1LO1LH_1LH1Rl".
Definition tm0' := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Rb0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0RD_1RD0Rl_1LH---_1Rl0R[_0Rb0RR_0Rd0RT_1Rb1RR_1Rd1RT_0LM1RD_---1Rb_1LM1Rl_---1RR_0Rj---_0RD---_1Rj---_0LM---_0LM---_0LO---_1LM---_1LO---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LO1LM_0LH1RD_1LO1LH_1LH1Rl".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RE1LH_0RG0RF_1RI1RE_1RA1RG_0RG1LB_0RA---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RE1LH_0RG0RF_1RI1RE_1RA1RG_0RG1LB_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "DMHPR[lOa".
Definition mp' := mp_from_str "DMHPR[lOb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM416.


Module TM417.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LA---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LC---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_1LU1RL_---1Rj_1LP1RD_---1RZ_0RD---_0RL---_1LU---_1RL---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_0LU1RL_---1Rj_1LU1RD_---1RZ_0RB---_0RL---_1RB---_0LU---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LUPXWDZcj".
Definition mp' := mp_from_str "LUPXWDZcj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM417.


Module TM418.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LC---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_0LU1RL_---1Rj_1LU1RD_---1RZ_0RB---_0RL---_1RB---_0LU---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Ri0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Ri0RZ_0Rk0R\_1Ri1RZ_1Rk1R\_1LU1RL_---1Ri_1LP1RD_---1RZ_0RL---_0Ri---_1RL---_1Ri---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LUPXWDZcj".
Definition mp' := mp_from_str "LUPXWDZci".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM418.


Module TM419.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LC---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Ri0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Ri0RZ_0Rk0R\_1Ri1RZ_1Rk1R\_1LU1RL_---1Ri_1LP1RD_---1RZ_0RL---_0Ri---_1RL---_1Ri---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0RL_0RL0RD_1RJ0LU_1RL1RD_0LW0Le_0LP0Lg_1LW1Le_1LP1Lg_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_0LU1RL_---1Rj_1LU1RD_---1RZ_0RB---_0RL---_1RB---_0LU---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LUPXWDZci".
Definition mp' := mp_from_str "LUPXWDZcj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM419.


Module TM420.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LC---".
Definition tm' := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE0RF_1RB0LF_1RA1RD".
Definition tm0 := TM'_from_str "0RJ0RL_0RL0RD_1RJ0LU_1RL1RD_0LW0Le_0LP0Lg_1LW1Le_1LP1Lg_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_0LU1RL_---1Rj_1LU1RD_---1RZ_0RB---_0RL---_1RB---_0LU---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_0LP---_1LW---_1LP---_0Ri0RZ_0Rd1LX_1Ri1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0Rb_0R[0RL_1RY1Rb_1R[0LU_0RL0LU_0RB0LW_0Rd1LU_0RZ1LW_0Rb0Ri_0Rd0Rk_1Rb1Ri_1Rd1Rk_1LU0RL_1RL0Rd_1LP---_1Rd0Rk_0RJ0RL_0RL0Rd_1RJ1RL_1RL1Rd_0LW0Lm_0LP0Lo_1LW1Lm_1LP1Lo_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_1LU1RL_---1RB_1LP1Rd_---1RZ".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LUPXWDZcj".
Definition mp' := mp_from_str "LUPXWdZkB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM420.


Module TM421.
Definition tm := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE0RF_1RB0LF_1RA1RD".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_0LP---_1LW---_1LP---_0Ri0RZ_0Rd1LX_1Ri1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0Rb_0R[0RL_1RY1Rb_1R[0LU_0RL0LU_0RB0LW_0Rd1LU_0RZ1LW_0Rb0Ri_0Rd0Rk_1Rb1Ri_1Rd1Rk_1LU0RL_1RL0Rd_1LP---_1Rd0Rk_0RJ0RL_0RL0Rd_1RJ1RL_1RL1Rd_0LW0Lm_0LP0Lo_1LW1Lm_1LP1Lo_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_1LU1RL_---1RB_1LP1Rd_---1RZ".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_1LU1RL_---1Rj_1LP1RD_---1RZ_0RJ---_0RL---_1RJ---_1RL---_0LW---_0LP---_1LW---_1LP---".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LUPXWdZkB".
Definition mp' := mp_from_str "LUPXWDZcj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM421.


Module TM422.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RB---".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_1LU1RL_---1Rj_1LP1RD_---1RZ_0RJ---_0RL---_1RJ---_1RL---_0LW---_0LP---_1LW---_1LP---".
Definition tm0' := TM'_from_str "0RJ0RL_0RL0RD_1RJ1RL_1RL1RD_0LW0Le_0LP0Lg_1LW1Le_1LP1Lg_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Ri0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Ri0RZ_0Rk0R\_1Ri1RZ_1Rk1R\_1LU1RL_---1Ri_1LP1RD_---1RZ_0RL---_0Ri---_1RL---_1Ri---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LUPXWDZcj".
Definition mp' := mp_from_str "LUPXWDZci".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM422.


Module TM423.
Definition tm := TM_from_str "1RB1RA_1RC0RA_1LD0RE_---1RE_0LF1LE_1LB1LC".
Definition tm' := TM_from_str "1RB1RA_1RC0RA_1LD0RE_---1LE_0LF1LE_1LB1LC".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lh1RT_1RJ1RL_1Rc1RC_1RB1RD_0RR0RA_0RT0RC_1RR1RA_1RT1RC_0Lh0RT_0RL0RL_1Lh0RC_1LV0RD_---0Ra_1Lo0Rc_---1Ra_1Lh1Rc_0L^0LN_0L`0Lo_1L^1LN_1L`1Lo_---0Rb_---0Rd_---1Rb_---1Rd_---0LV_---0Lh_---1LV_---1Lh_0RL1LN_0L`1Lo_0RL1LV_0Lo1Lh_0Lm0Lf_0Lo0Lh_1Lm1Lf_1Lo1Lh_0Rc---_0RB1LN_1Rc1Lh_1RB1LV_0LN0LV_0LP0LX_1LN1LV_1LP1LX".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_1Lh1RT_1RJ1RL_1Rc1RC_1RB1RD_0RR0RA_0RT0RC_1RR1RA_1RT1RC_0Lh0RT_0RL0RL_1Lh0RC_1LV0RD_---0Ra_1Lo0Rc_---1Ra_1Lh1Rc_0L^0LN_0L`0Lo_1L^1LN_1L`1Lo_---1LN_---1Lo_---1LV_---1Lh_---0Lf_---0Lh_---1Lf_---1Lh_0RL1LN_0L`1Lo_0RL1LV_0Lo1Lh_0Lm0Lf_0Lo0Lh_1Lm1Lf_1Lo1Lh_0Rc---_0RB1LN_1Rc1Lh_1RB1LV_0LN0LV_0LP0LX_1LN1LV_1LP1LX".
Definition tm1 := TM'_from_str "1RB1RA_1RC1RI_1LD---_1LE1LD_1LH1LF_0LG0LE_---1LD_0RB0RB_1RK1RJ_0RB0RA_0RC0RI".
Definition tm2 := TM'_from_str "1RB1RA_1RC1RI_1LD---_1LE1LD_1LH1LF_0LG0LE_1RL1LD_0RB0RB_1RK1RJ_0RB0RA_0RC0RI_1RL1RL".
Definition l0 := [0;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "DLThoV`NCBJ".
Definition mp' := mp_from_str "DLThoV`NCBJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM423.


Module TM424.
Definition tm := TM_from_str "1LB1LE_1RC1LF_1RA0RD_1RE1LD_0LA0RC_0LA---".
Definition tm' := TM_from_str "1LB1LE_1RC1LF_1RA0RD_1RE1LD_0LA0RC_0RA---".
Definition tm0 := TM'_from_str "0R[1LN_1LG0RY_1R[1Lf_---1RY_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0RR1LN_0RT---_1RR1Lf_1RT---_---0Ln_1Rb0Lp_1RY1Ln_1RS1Lp_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0Lp0LG_0Rb1RB_1Lp0RS_0RS1RY_0Rb0RS_0Rd1RY_1Rb1RS_1Rd1L`_0Lf0L^_1RB0L`_1Lf1L^_1RY1L`_1Rb0RQ_0LG0RS_0Lp1RQ_0Rb1RS_0LE1LG_0LG0Rb_1LE0RY_1LG0RS_1Rb---_0LG---_0Lp---_0Rb---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0R[1LN_1LG0RY_1R[1Lf_---1RY_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0RR1LN_0RT---_1RR1Lf_1RT---_---0Ln_1Rb0Lp_1RY1Ln_1RS1Lp_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0Lp0LG_0Rb1RB_1Lp0RS_0RS1RY_0Rb0RS_0Rd1RY_1Rb1RS_1Rd1L`_0Lf0L^_1RB0L`_1Lf1L^_1RY1L`_1Rb0RQ_0LG0RS_0Lp1RQ_0Rb1RS_0LE1LG_0LG0Rb_1LE0RY_1LG0RS_0RA---_0RC---_1RA---_1RC---_1Rb---_0LG---_1RS---_1LG---".
Definition tm1 := TM'_from_str "1LB0RH_1LD1LC_0LB0RF_1RF0LE_1LB---_0LB0RG_1RA1RH_0RF0RG".
Definition tm2 := TM'_from_str "1LB0RH_1LD1LC_0LB0RF_1RF0LE_1LB1RI_0LB0RG_1RA1RH_0RF0RG_1RI1RI".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "BGfNpbSY".
Definition mp' := mp_from_str "BGfNpbSY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM424.


Module TM425.
Definition tm := TM_from_str "1LB1RB_1LC0RB_1RA0LD_---0LE_0LF0RF_1RA1LB".
Definition tm' := TM_from_str "1LB1RB_1LC0RB_1RA0LD_---0LE_0LF0RC_1RA1LB".
Definition tm0 := TM'_from_str "1RK0RJ_0RI0RL_1L_1RJ_1RI1RL_0LN0L__0LP1RL_1LN1L__1LP1RI_0RL0RI_---0RK_1RL1RI_1Le1RK_0LV1Le_0LX0RL_1LV1RK_1LX0RI_0RB---_0RD0Lm_1RB---_1RD0RI_0RL0L]_1Le0L__0RI1L]_1RK1L__---0RL_---0RB_---0LN_---1RB_---0Le_---0Lg_---1Le_---1Lg_0RI0Ri_0LX0Rk_1RI1Ri_0RL1Rk_0Lm0RI_0Lo0LX_1Lm0RL_1Lo1LX_0RB1RK_0RD0RI_1RB1L__1RD1RI_0RL0LN_1Le0LP_0RI1LN_1RK1LP".
Definition tm0' := TM'_from_str "1RK0RJ_0RI0RL_1L_1RJ_1RI1RL_0LN0L__0LP1RL_1LN1L__1LP1RI_0RL0RI_---0RK_1RL1RI_1Le1RK_0LV1Le_0LX0RL_1LV1RK_1LX0RI_0RB---_0RD0Lm_1RB---_1RD0RI_0RL0L]_1Le0L__0RI1L]_1RK1L__---0RL_---0RB_---0LN_---1RB_---0Le_---0Lg_---1Le_---1Lg_0RI0RQ_0LX0RS_1RI1RQ_0RL1RS_0Lm0RI_0Lo---_1Lm0RL_1Lo---_0RB1RK_0RD0RI_1RB1L__1RD1RI_0RL0LN_1Le0LP_0RI1LN_1RK1LP".
Definition tm1 := TM'_from_str "1LB1RF_0LC0RG_0RA0LD_0LE0RA_1RF1LH_1RA1RG_0RA0RG_---1LB".
Definition tm2 := TM'_from_str "1LB1RF_0LC0RG_0RA0LD_0LE0RA_1RF1LH_1RA1RG_0RA0RG_1RI1LB_1RI1RI".
Definition l0 := [1;0;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "LemNXKI_".
Definition mp' := mp_from_str "LemNXKI_".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM425.


Module TM426.
Definition tm := TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC0RF_1LA1RC_0LD---".
Definition tm' := TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC0RF_1LA1RC_0LB---".
Definition tm0 := TM'_from_str "0R[1RR_1LG0LN_1R[0LW_0R[0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR1LN_0RT0RR_1RR1LE_1RT1RR_1LE0LU_1RR0LW_1RT1LU_1Ri1LW_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0LG0Rd_1Rd0Rd_1LG0R[_1R[---_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1LE1LE_1RR---_1RT1RT_1Ri---_1Ri0RR_1LN0RT_1LW1RR_1LE1RT_0LF1LE_0LH1RR_1LF1RT_1LH1Ri_0Rd---_0Rd---_1Rd---_1Rd---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0R[1RR_1LG0LN_1R[0LW_0R[0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR1LN_0RT0RR_1RR1LE_1RT1RR_1LE0LU_1RR0LW_1RT1LU_1Ri1LW_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0LG0Rd_1Rd0Rd_1LG0R[_1R[---_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_1LE1LE_1RR---_1RT1RT_1Ri---_1Ri0RR_1LN0RT_1LW1RR_1LE1RT_0LF1LE_0LH1RR_1LF1RT_1LH1Ri_0Rd---_0LG---_1Rd---_0Rd---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1RB1RI_0RC0RA_1LD1RG_0LE0LD_1RB0LF_1LH0RA_1RC1RA_1LE1LD_0RC---".
Definition tm2 := TM'_from_str "1RB1RI_0RC0RA_1LD1RG_0LE0LD_1RB0LF_1LH0RA_1RC1RA_1LE1LD_0RC1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "[RdENWTGi".
Definition mp' := mp_from_str "[RdENWTGi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM426.


Module TM427.
Definition tm := TM_from_str "1LB0LA_1RC1LE_1RD0RC_1RA1RF_1RC0LA_---0RE".
Definition tm' := TM_from_str "1LB0LA_0RB1LC_1RD0LA_1RE0RD_1RA1RF_---0RC".
Definition tm0 := TM'_from_str "0RS1RZ_1RQ0LN_1RS0Lh_1LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0RS_0RT1LN_1RR1RS_1RT1LE_1RD0Lf_1RZ0Lh_1Rl1Lf_1RQ1Lh_0RZ0RQ_0R\0RS_1RZ1RQ_1R\1RS_1LG0RD_---0RZ_0LE0Rl_1Rc0RQ_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lh---_0LE1RR_1Lh---_1LE0Lh_0RR1RZ_0RT0LN_1RR0Lh_1RT0LE_1RD0LE_1RZ0LG_1Rl1LE_1RQ1LG_---0Ra_---0Rc_---1Ra_---1Rc_---0R\_---0LN_---0RS_---1LN".
Definition tm0' := TM'_from_str "0R[1Rb_1RY0LN_1R[0LX_1LG0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RI0R[_0RK1LN_1RI1R[_1RK1LE_0RI0LV_1Rb0LX_0R[1LV_1RY1LX_0RZ1Rb_0R\0LN_1RZ0LX_1R\0LE_1RD0LE_1Rb0LG_1Rl1LE_1RY1LG_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1LG0RD_---0Rb_0LE0Rl_1RS0RY_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0LX---_0LE1RZ_1LX---_1LE0LX_---0RQ_---0RS_---1RQ_---1RS_---0Rd_---0LN_---0R[_---1LN".
Definition tm1 := TM'_from_str "1RB0LH_0RC0RK_1RD1RJ_1LE0LF_1LG1LF_0LG0LF_1RI0LH_1RL1LE_0RD0RJ_---1RA_1RI1RL_0RI0RL".
Definition tm2 := TM'_from_str "1RB0LH_0RC0RK_1RD1RJ_1LE0LF_1LG1LF_0LG0LF_1RI0LH_1RL1LE_0RD0RJ_1RM1RA_1RI1RL_0RI0RL_1RM1RM".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "cR\DGENhZlSQ".
Definition mp' := mp_from_str "SZdDGENXbl[Y".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM427.


Module TM428.
Definition tm := TM_from_str "1LB0RD_0LC1RF_1RD1LC_1RE0LF_---1RA_1RF0RA".
Definition tm' := TM_from_str "1LB0RD_0LC1LA_1RD1LC_1RE0LF_---1RA_1RF0RA".
Definition tm0 := TM'_from_str "1RD0RY_0RC0R[_1LV1RY_1RC1R[_0LN---_0LP1Rl_1LN0RD_1LP1RC_0Rd0Rj_0LW0Rl_1Rd1Rj_0LX1Rl_0LU1Rl_0LW1LV_1LU1RC_1LW1RY_0RZ1RD_0R\1LW_1RZ1LV_1R\1LX_---0LV_0LW0LX_1RD1LV_1LW1LX_0Rb0Rl_0Rd1RD_1Rb1Rl_1Rd1LV_---0Lm_1RC0Lo_---1Lm_1R[1Lo_---0RB_---0RD_---1RB_---1RD_---1LV_---1Rb_---1RY_---1Rl_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1Rl0LW_1LV0Rb_1RC1LW_1RY0Rl".
Definition tm0' := TM'_from_str "1RD0RY_1LP0R[_1LV1RY_1RC1R[_0LN---_0LP1Rl_1LN0RD_1LP1RC_0Rd1LW_0LW0Rl_1Rd1LH_0LX1Rl_0LU0LF_0LW0LH_1LU1LF_1LW1LH_0RZ1RD_0R\1LW_1RZ1LV_1R\1LX_---0LV_0LW0LX_1RD1LV_1LW1LX_0Rb0Rl_0Rd1RD_1Rb1Rl_1Rd1LV_---0Lm_1RC0Lo_---1Lm_1R[1Lo_---0RB_---0RD_---1RB_---1RD_---0LH_---1Rb_---1LH_---1Rl_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1Rl0LW_1LV0Rb_1RC1LW_1RY0Rl".
Definition tm1 := TM'_from_str "1LB1RH_0LD0LC_1LD1LC_1RE1LB_1RA1RF_1RI1RG_1RG1RA_0RI0RG_---0RE".
Definition tm2 := TM'_from_str "1LB1RH_0LD0LC_1LD1LC_1RE1LB_1RA1RF_1RI1RG_1RG1RA_0RI0RG_1RJ0RE_1RJ1RJ".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "CVXWD[lYb".
Definition mp' := mp_from_str "CVXWD[lYb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM428.


Module TM429.
Definition tm := TM_from_str "1LB0LA_0LC0RB_1RD0LF_1RE1LA_1LD1LB_0LA---".
Definition tm' := TM_from_str "1LB0LA_0LC0RB_1RD1LF_1RE1LA_1LD1LB_1RA---".
Definition tm0 := TM'_from_str "1RI0LW_0RI0LN_1Lm0Rd_1RI0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0Rd0RI_0LE0RK_1Rd1RI_---1RK_0LU1LG_0LW0Rd_1LU1RI_1LW0RI_0RZ0LN_0R\---_1RZ0LE_1R\---_1LG0Lm_0LG0Lo_1RI1Lm_1LG1Lo_0Rb1LW_0Rd1LN_1Rb0RI_1Rd1LE_0LH0LF_0Rd0LH_1LH1LF_0RI1LH_0RI1RI_1LP0RI_1RI1Lm_1LG1RI_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0LW---_0LN---_0Rd---_0LE---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "1RI0LW_0RI0LN_1Ln0Rd_1RI0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0Rd0RI_0LE0RK_1Rd1RI_---1RK_0LU1LG_0LW0Rd_1LU1RI_1LW0RI_0RZ0LN_0R\---_1RZ0LE_1R\---_1LG0Ln_0LG0Lp_1RI1Ln_1LG1Lp_0Rb1LW_0Rd1LN_1Rb0RI_1Rd1LE_0LH0LF_0Rd0LH_1LH1LF_0RI1LH_0RI1RI_1LP0RI_1RI1Ln_1LG1RI_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0RB---_0RD---_1RB---_1RD---_0Rd---_0LE---_0RI---_1LE---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RA_1LD1LG_0LE0RB_1RA1LF_0LG---_0LD0LG".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RA_1LD1LG_0LE0RB_1RA1LF_0LG1RH_0LD0LG_1RH1RH".
Definition l0 := [0;1;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "IdGNWmE".
Definition mp' := mp_from_str "IdGNWnE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM429.


Module TM430.
Definition tm := TM_from_str "1RB1RF_1LC0RA_1RA0LD_0LE0RF_0RC0LC_0LB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1Le_1RJ---_1L_0RC_1Rj---_0Rl0RA_1Le0RC_1Rl1RA_1LV1RC_0LV1Le_0LX0RJ_1LV0RC_1LX---_0RB0RL_0RD1RJ_1RB0LU_1RD0L__1LV0L]_1RJ0L__1RC1L]_---1L__0RB0Ri_1LV0Rk_1RB1Ri_0L]1Rk_0Le0LV_0Lg---_1Le1LV_1Lg---_0RQ0RL_0RS0Le_1RQ1RL_1RS0LV_0RL0LU_0Le0LW_0Rl1LU_1Le1LW_1RJ---_0RJ---_0L_---_1RJ---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1RJ---_1L_---_1RA---_0RC0Ri_1Le0Rk_1RC1Ri_1LV1Rk_0LV1Le_0LX0RJ_1LV0Rk_1LX---_0Rj0RL_0Rl1RJ_1Rj0LU_1Rl0L__1LV0L]_1RJ0L__1Rk1L]_---1L__0Rj0RC_1LV1Le_1Rj1RC_0L]1LV_0Le0LV_0Lg0LX_1Le1LV_1Lg1LX_0RQ0RL_0RS0Le_1RQ1RL_1RS0LV_0RL0LU_0Le0LW_0RC1LU_1Le1LW_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Le_1RJ---_1L_0Rk_1RA---".
Definition tm1 := TM'_from_str "1LB0RD_0RC0LE_1LG1RD_1RA1RI_1LG0LF_0LB0LG_1RA0LH_1LB1LG_0RA---".
Definition tm2 := TM'_from_str "1LB0RD_0RC0LE_1LG1RD_1RA1RI_1LG0LF_0LB0LG_1RA0LH_1LB1LG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JeLCU]V_j".
Definition mp' := mp_from_str "JeLkU]V_A".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM430.


Module TM431.
Definition tm := TM_from_str "1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA".
Definition tm' := TM_from_str "1RB1RF_1LC0RA_1RA0LD_0LE1LC_0RC0LC_0LB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1RJ---_1L_---_1RA---_0RC0Ri_1Le0Rk_1RC1Ri_1LV1Rk_0LV1Le_0LX0RJ_1LV0Rk_1LX---_0Rj0RL_0Rl1RJ_1Rj0LU_1Rl0L__1LV0L]_1RJ0L__1Rk1L]_---1L__0Rj0RC_1LV1Le_1Rj1RC_0L]1LV_0Le0LV_0Lg0LX_1Le1LV_1Lg1LX_0RQ0RL_0RS0Le_1RQ1RL_1RS0LV_0RL0LU_0Le0LW_0RC1LU_1Le1LW_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1Le_1RJ---_1L_0Rk_1RA---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_1Le_1RJ---_1L_0RC_1Rj---_0Rl0RA_1Le0RC_1Rl1RA_1LV1RC_0LV1Le_0LX0RJ_1LV0RC_1LX---_0RB0RL_0RD1RJ_1RB0LU_1RD0L__1LV0L]_1RJ0L__1RC1L]_---1L__0RB0Rl_1LV1Le_1RB1Rl_0L]1LV_0Le0LV_0Lg0LX_1Le1LV_1Lg1LX_0RQ0RL_0RS0Le_1RQ1RL_1RS0LV_0RL0LU_0Le0LW_0Rl1LU_1Le1LW_1RJ---_0RJ---_0L_---_1RJ---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RD_0RC0LE_1LG1RD_1RA1RI_1LG0LF_0LB0LG_1RA0LH_1LB1LG_0RA---".
Definition tm2 := TM'_from_str "1LB0RD_0RC0LE_1LG1RD_1RA1RI_1LG0LF_0LB0LG_1RA0LH_1LB1LG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JeLkU]V_A".
Definition mp' := mp_from_str "JeLCU]V_j".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM431.


Module TM432.
Definition tm := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LF_0RD---".
Definition tm' := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LP1LM_1RB1RL_1LP1R[_0RL1RD_1RD0RY_1LX0R[_1Lg1RY_1LM1R[_0LV0RL_0LX0LM_1LV0RD_1LX1LM_0RD1L`_1LM0LV_1RD1LP_1Ln0RL_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0RB0LV_0RD0LM_1RB0RL_1RD---_1LM0Le_1RL0Lg_1R[1Le_1RD1Lg_0L`0LV_0RB---_0LP0RL_1RB---_0LM0Ln_0LO0Lp_1LM1Ln_1LO1Lp_0RY---_0R[---_1RY---_1R[---_0RL---_0LM---_0RD---_1LM---".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LP1LM_1RB1RL_1LP1R[_0RL1RD_1RD0RY_1LX0R[_1Lg1RY_1LM1R[_0LV0RL_0LX0LM_1LV0RD_1LX1LM_0RD1L`_1LM0LV_1RD1LP_1Lm0RL_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0RB0LV_0RD0LM_1RB0RL_1RD---_1LM0Le_1RL0Lg_1R[1Le_1RD1Lg_0L`0LV_0RB---_0LP0RL_1RB---_0LM0Lm_0LO0Lo_1LM1Lm_1LO1Lo_0L`---_0RB---_0LP---_1RB---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1RB0RC_0RC0RH_1LD1RA_0LE0RC_0LG0LF_1LI1LD_1RH1LJ_1RC1RH_1LG1LF_1LD1LK_0LD---".
Definition tm2 := TM'_from_str "1RB0RC_0RC0RH_1LD1RA_0LE0RC_0LG0LF_1LI1LD_1RH1LJ_1RC1RH_1LG1LF_1LD1LK_0LD1RL_1RL1RL".
Definition l0 := [0;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "[BLMVP`DXgn".
Definition mp' := mp_from_str "[BLMVP`DXgm".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM432.


Module TM433.
Definition tm := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---".
Definition tm' := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LF_1RC---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LP1LM_1RB1RL_1LP1R[_0RL1RD_1RD0RY_1LX0R[_1Lg1RY_1LM1R[_0LV0RL_0LX0LM_1LV0RD_1LX1LM_0RD1L`_1LM0LV_1RD1LP_1Lm0RL_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0RB0LV_0RD0LM_1RB0RL_1RD---_1LM0Le_1RL0Lg_1R[1Le_1RD1Lg_0L`0LV_0RB---_0LP0RL_1RB---_0LM0Lm_0LO0Lo_1LM1Lm_1LO1Lo_0L`---_0RB---_0LP---_1RB---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LP1LM_1RB1RL_1LP1R[_0RL1RD_1RD0RY_1LX0R[_1Lg1RY_1LM1R[_0LV0RL_0LX0LM_1LV0RD_1LX1LM_0RD1L`_1LM0LV_1RD1LP_1Ln0RL_0L^0LN_0L`0LP_1L^1LN_1L`1LP_0RB0LV_0RD0LM_1RB0RL_1RD---_1LM0Le_1RL0Lg_1R[1Le_1RD1Lg_0L`0LV_0RB---_0LP0RL_1RB---_0LM0Ln_0LO0Lp_1LM1Ln_1LO1Lp_0RR---_0RT---_1RR---_1RT---_0Lg---_0LM---_1Lg---_1LM---".
Definition tm1 := TM'_from_str "1RB0RC_0RC0RH_1LD1RA_0LE0RC_0LG0LF_1LI1LD_1RH1LJ_1RC1RH_1LG1LF_1LD1LK_0LD---".
Definition tm2 := TM'_from_str "1RB0RC_0RC0RH_1LD1RA_0LE0RC_0LG0LF_1LI1LD_1RH1LJ_1RC1RH_1LG1LF_1LD1LK_0LD1RL_1RL1RL".
Definition l0 := [0;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "[BLMVP`DXgm".
Definition mp' := mp_from_str "[BLMVP`DXgn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM433.


Module TM434.
Definition tm := TM_from_str "1LB1RE_1LC1LA_0RD0RB_1RB1RD_1LF0RA_---0LE".
Definition tm' := TM_from_str "1LB1RE_1LC1LA_0RD1LB_1RB1RD_1LF0RA_---0LE".
Definition tm0 := TM'_from_str "0R\0Rb_1LP0Rd_1LP1Rb_1Rb1Rd_0LN0Lg_0LP1LP_1LN1Lg_1LP1Rb_0RZ1LX_1LX0RC_1RZ1LH_1LH1RC_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0RY0RI_0R[0RK_1RY1RI_1R[1RK_1LX0RL_0RL0LP_0RC0R\_0R\1LP_0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LP1LH_1LP1RL_1LP1RC_1Rb1R\_---0RA_1Ln0RC_---1RA_1LX1RC_0Ln0LX_0Lp1Ln_1Ln1LX_1Lp0RC_------_---0R\_---0Lg_---1LP_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0R\0Rb_1LP0Rd_1LP1Rb_1Rb1Rd_0LN0Lg_0LP1LP_1LN1Lg_1LP1Rb_0RZ1LX_1LX0RC_1RZ1LH_1LH1RC_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0RY0R\_0R[1LP_1RY1LP_1R[1Rb_1LX0LN_0RL0LP_0RC1LN_0R\1LP_0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LP1LH_1LP1RL_1LP1RC_1Rb1R\_---0RA_1Ln0RC_---1RA_1LX1RC_0Ln0LX_0Lp1Ln_1Ln1LX_1Lp0RC_------_---0R\_---0Lg_---1LP_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1LB0RH_---0LC_1LB1LD_0RF1LE_1LD1LI_1RG1RF_1LI1RH_1LE1RA_1LE1RA".
Definition tm2 := TM'_from_str "1LB0RH_1RJ0LC_1LB1LD_0RF1LE_1LD1LI_1RG1RF_1LI1RH_1LE1RA_1LE1RA_1RJ1RJ".
Definition l0 := [0;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "bngXP\LCH".
Definition mp' := mp_from_str "bngXP\LCH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM434.


Module TM435.
Definition tm := TM_from_str "1LB---_1RC1LE_0RE0RD_0LB0RC_1LA0LF_0RD1LB".
Definition tm' := TM_from_str "1LB---_1RC1LF_0RF0RD_0LE0RC_1RC1LB_1LA0LE".
Definition tm0 := TM'_from_str "0R[---_1LH---_1R[---_1Lo---_0LN---_0LP---_1LN---_1LP---_0RR1LP_0RT1Rc_1RR---_1RT1LN_1Lh0Lf_1Rc0Lh_1Rc1Lf_1RQ1Lh_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP1Lh_1Lh0Ra_1LP1Rc_1Rc0RY_0Rc0RQ_0LH0RS_1Rc1RQ_0Lo1RS_0LM1RQ_0LO0Rc_1LM0Rc_1LO0RQ_1RQ0Rc_---1Rc_1Lh1Rc_---0Lh_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0RY0R[_0R[1LH_1RY1R[_1R[1Lo_1Lh0LN_0Ra0LP_1Rc1LN_0RY1LP".
Definition tm0' := TM'_from_str "0R[---_1LH---_1R[---_1Lg---_0LN---_0LP---_1LN---_1LP---_0RR1LP_0RT1Rk_1RR---_1RT1LN_1Lp0Ln_1Rk0Lp_1Rk1Ln_1RQ1Lp_0Ri0RY_0Rk0R[_1Ri1RY_1Rk1R[_0LP1Lp_1Lp0Ri_1LP1Rk_1Rk0RY_0Rk0RQ_1Rk0RS_1Rk1RQ_0Lp1RS_0Le1RQ_0Lg0Rk_1Le0Rk_1Lg0RQ_0RR0R[_0RT1LH_1RR1R[_1RT1Lg_1Lp0LN_1Rk0LP_1Rk1LN_1RQ1LP_1RQ0Rk_---1Rk_1Lp1Rk_---0Lp_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg".
Definition tm1 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF---_1RG1LB_0RI0RH_0RA0RG_1RG0RA".
Definition tm2 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF1RJ_1RG1LB_0RI0RH_0RA0RG_1RG0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "choNHPQYa".
Definition mp' := mp_from_str "kpgNHPQYi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM435.


Module TM436.
Definition tm := TM_from_str "1LB---_1RC1LF_0RF0RD_0LE0RC_1RC1LB_1LA0LE".
Definition tm' := TM_from_str "1LB---_1RC1LE_0RE0RD_0LB0RC_1LA0LF_1RC1LB".
Definition tm0 := TM'_from_str "0R[---_1LH---_1R[---_1Lg---_0LN---_0LP---_1LN---_1LP---_0RR1LP_0RT1Rk_1RR---_1RT1LN_1Lp0Ln_1Rk0Lp_1Rk1Ln_1RQ1Lp_0Ri0RY_0Rk0R[_1Ri1RY_1Rk1R[_0LP1Lp_1Lp0Ri_1LP1Rk_1Rk0RY_0Rk0RQ_1Rk0RS_1Rk1RQ_0Lp1RS_0Le1RQ_0Lg0Rk_1Le0Rk_1Lg0RQ_0RR0R[_0RT1LH_1RR1R[_1RT1Lg_1Lp0LN_1Rk0LP_1Rk1LN_1RQ1LP_1RQ0Rk_---1Rk_1Lp1Rk_---0Lp_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg".
Definition tm0' := TM'_from_str "0R[---_1LH---_1R[---_1Lo---_0LN---_0LP---_1LN---_1LP---_0RR1LP_0RT1Rc_1RR---_1RT1LN_1Lh0Lf_1Rc0Lh_1Rc1Lf_1RQ1Lh_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP1Lh_1Lh0Ra_1LP1Rc_1Rc0RY_0Rc0RQ_0LH0RS_1Rc1RQ_0Lo1RS_0LM1RQ_0LO0Rc_1LM0Rc_1LO0RQ_1RQ0Rc_---1Rc_1Lh1Rc_---0Lh_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0RR0R[_0RT1LH_1RR1R[_1RT1Lo_1Lh0LN_1Rc0LP_1Rc1LN_1RQ1LP".
Definition tm1 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF---_1RG1LB_0RI0RH_0RA0RG_1RG0RA".
Definition tm2 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF1RJ_1RG1LB_0RI0RH_0RA0RG_1RG0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "kpgNHPQYi".
Definition mp' := mp_from_str "choNHPQYa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM436.


Module TM437.
Definition tm := TM_from_str "1LB---_1RC1LE_0RE0RD_0LB0RC_1LA0LF_1RC1LB".
Definition tm' := TM_from_str "1LB---_1RC1LE_0RE0RD_1LC0RC_1LA0LF_1RC1LB".
Definition tm0 := TM'_from_str "0R[---_1LH---_1R[---_1Lo---_0LN---_0LP---_1LN---_1LP---_0RR1LP_0RT1Rc_1RR---_1RT1LN_1Lh0Lf_1Rc0Lh_1Rc1Lf_1RQ1Lh_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP1Lh_1Lh0Ra_1LP1Rc_1Rc0RY_0Rc0RQ_0LH0RS_1Rc1RQ_0Lo1RS_0LM1RQ_0LO0Rc_1LM0Rc_1LO0RQ_1RQ0Rc_---1Rc_1Lh1Rc_---0Lh_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0RR0R[_0RT1LH_1RR1R[_1RT1Lo_1Lh0LN_1Rc0LP_1Rc1LN_1RQ1LP".
Definition tm0' := TM'_from_str "0R[---_1LH---_1R[---_1Lo---_0LN---_0LP---_1LN---_1LP---_0RR1LP_0RT1Rc_1RR---_1RT1LN_1Lh0Lf_1Rc0Lh_1Rc1Lf_1RQ1Lh_0Ra0RY_0Rc0R[_1Ra1RY_1Rc1R[_0LP1Lh_1Lh0Ra_1LP1Rc_1Rc0RY_0Rc0RQ_0RQ0RS_1Rc1RQ_1RQ1RS_0LV1RQ_0LX0Rc_1LV0Rc_1LX0RQ_1RQ0Rc_---1Rc_1Lh1Rc_---0Lh_0LF0Lm_0LH0Lo_1LF1Lm_1LH1Lo_0RR0R[_0RT1LH_1RR1R[_1RT1Lo_1Lh0LN_1Rc0LP_1Rc1LN_1RQ1LP".
Definition tm1 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF---_1RG1LB_0RI0RH_0RA0RG_1RG0RA".
Definition tm2 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF1RJ_1RG1LB_0RI0RH_0RA0RG_1RG0RA_1RJ1RJ".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "choNHPQYa".
Definition mp' := mp_from_str "choNHPQYa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM437.


Module TM438.
Definition tm := TM_from_str "1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA".
Definition tm' := TM_from_str "1RB0LD_0RC---_0LD0RF_1LE1LD_0LA1LE_0RB1RA".
Definition tm0 := TM'_from_str "0RJ0LG_0RL0Lh_1RJ0Lh_1RL0L`_0Lh0L]_---0L__1Ri1L]_---1L__0RQ---_0RS---_1RQ---_1RS---_0Lf---_0RI---_1Lf---_0RB---_0LG0Ri_0Lh0Rk_0Lh1Ri_0L`1Rk_0L]0RQ_0L_0RL_1L]---_1L_0Lh_1Ri1LG_1LG1Lh_1L]1Lh_1Lh1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_0RS0RY_0Lf0R[_1RS1RY_0L^1R[_0LE0LG_0LG0Lh_1LE1LG_1LG1Lh_0RI0RB_0RK0RD_1RI1RB_1RK1RD_0LG1RS_---0L^_0Ri---_---1L^".
Definition tm0' := TM'_from_str "0RJ0LG_0RL0Lh_1RJ0Lh_1RL0L`_0Lh0L]_---0L__1Ri1L]_---1L__0RQ---_0RS---_1RQ---_1RS---_0Lf---_0RI---_1Lf---_0RB---_0LG0Ri_0Lh0Rk_0Lh1Ri_0L`1Rk_0L]0RQ_0L_0RL_1L]---_1L_0Lh_1Ri1LG_1LG1Lh_1L]1Lh_1Lh1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_0RS1Ri_0Lf1LG_1RS1L]_0L^1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_0RI0RB_0RK0RD_1RI1RB_1RK1RD_0LG1RS_---0L^_0Ri---_---1L^".
Definition tm1 := TM'_from_str "0LB1RD_1LC1LB_1RD1LF_0RJ0RE_0RL0LB_0LI0LG_0LB0LH_1LB1LH_0LC0LB_0RK---_0LC0RD_1RA---".
Definition tm2 := TM'_from_str "0LB1RD_1LC1LB_1RD1LF_0RJ0RE_0RL0LB_0LI0LG_0LB0LH_1LB1LH_0LC0LB_0RK1RM_0LC0RD_1RA1RM_1RM1RM".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "ShGiB]^`fIQL".
Definition mp' := mp_from_str "ShGiB]^`fIQL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM438.


Module TM439.
Definition tm := TM_from_str "1RB0LE_1RC0RA_1RD0RF_1LA0RC_1LB1LA_0LA---".
Definition tm' := TM_from_str "1RB0LE_1RC0RA_1RD1RF_1LA0RC_1LB1LA_1RC---".
Definition tm0 := TM'_from_str "0RJ1RT_0RL1RJ_1RJ0LN_1RL0Lg_1R\0Le_1RJ0Lg_1Rk1Le_0LN1Lg_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1LF0RT_1RT0LN_1RS0RC_---1LN_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0Lg1R\_1RZ---_1Lg1Rk_1Ri---_0RC0RQ_1LN0RS_1RC1RQ_1LF1RS_0LF1LN_0LH0RT_1LF0RS_1LH---_0Rk0RC_1RT1LN_1Rk1RC_0LN1LF_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RT---_0LN---_1RT---_0LF---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ1RT_0RL1RJ_1RJ0LN_1RL0Lg_1R\0Le_1RJ0Lg_1Rl1Le_0LN1Lg_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1LF0RT_1RT0LN_1RS0RC_---1LN_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_0Lg1R\_1RZ---_1Lg1Rl_1Rj---_0RC0RQ_1LN0RS_1RC1RQ_1LF1RS_0LF1LN_0LH0RT_1LF0RS_1LH---_0Rl0RC_1RT1LN_1Rl1RC_0LN1LF_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RR---_0RT---_1RR---_1RT---_1LF---_1RT---_1RS---".
Definition tm1 := TM'_from_str "1RB0LG_0RC0RA_1RD1RJ_1LE1RH_1RB0LF_1LG1LE_1RC0LG_1RI1RK_1LG0RH_1RC---_0RC---".
Definition tm2 := TM'_from_str "1RB0LG_0RC0RA_1RD1RJ_1LE1RH_1RB0LF_1LG1LE_1RC0LG_1RI1RK_1LG0RH_1RC1RL_0RC1RL_1RL1RL".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "CJT\FgNSZki".
Definition mp' := mp_from_str "CJT\FgNSZlj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM439.


Module TM440.
Definition tm := TM_from_str "1LB1RD_1RC0LA_1LC1LA_0RF0RE_1RA0RB_---1RC".
Definition tm' := TM_from_str "1LB1RD_1RC0LA_1LC1LA_1RF0RE_1RA0RB_---0LE".
Definition tm0 := TM'_from_str "0Rc0RZ_1LN0R\_1Rc1RZ_1RR1R\_0LN---_0LP1RB_1LN1RR_1LP1RI_0RR1RB_0RT0Rk_1RR0LG_1RT1Rk_0LH0LE_1RB0LG_1LH1LE_1RI1LG_1LX1RI_1LP0Rc_1LH1LG_1RI1Rc_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_---1LN_1LP0RR_---0R\_0Rc1RB_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0LG1LP_1Rk0LN_1LG0Rc_1Rc1LN_---0RR_---0RT_---1RR_---1RT_---0LH_---1RB_---1LH_---1RI".
Definition tm0' := TM'_from_str "0Rc0RZ_1LN0R\_1Rc1RZ_1RR1R\_0LN---_0LP1RB_1LN1RR_1LP1RI_0RR1RB_0RT0Rl_1RR0LG_1RT1Rl_0LH0LE_1RB0LG_1LH1LE_1RI1LG_1LX1RI_1LP0Rc_1LH1LG_1RI1Rc_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Rj0Ra_0Rl0Rc_1Rj1Ra_1Rl1Rc_---1LN_1LP0RR_---0R\_0Rc1RB_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0LG1LP_1Rl0LN_1LG0Rc_1Rc1LN_---1LN_---0RR_---1RR_---1RR_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1LB0RF_1RA0LC_1LB1RD_1LE0RH_1RI1LC_1RG1RH_---1RD_1RA1RI_0RD1RA".
Definition tm2 := TM'_from_str "1LB0RF_1RA0LC_1LB1RD_1LE0RH_1RI1LC_1RG1RH_1RJ1RD_1RA1RI_0RD1RA_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNGRP\kcI".
Definition mp' := mp_from_str "BNGRP\lcI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM440.


Module TM441.
Definition tm := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LD1RC".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO0LV_1RJ0LO_1LO1LV_1Ra1LO_0RT0RA_1LV0RC_1RT1RA_0RC1RC_0LV1LV_0LX1Rl_1LV0RC_1LX1LV_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_0Lh---_1Rl0LO_1Lh---_1R[1LO_---1LV_---1LO_---0RC_---1Lh_---0Lf_---0Lh_---1Lf_---1Lh_1Rl1LV_0RJ1LO_0LO0RC_1RJ1Lh_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_---0RR_1LO0RT_---1RR_1Lh1RT_0L^1Lh_0L`---_1L^1RT_1L`0RC".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO0LV_1RJ0LO_1LO1LV_1Ra1LO_0RT0RA_1LV0RC_1RT1RA_0RC1RC_0LV1LV_0LX1Rl_1LV0RC_1LX1LV_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_0Lh---_1Rl0LO_1Lh---_1R[1LO_---1LV_---1LO_---0RC_---1Lh_---0Lf_---0Lh_---1Lf_---1Lh_1Rl1LV_0RJ1LO_0LO0RC_1RJ1Lh_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_1LV0RR_1LO0RT_0RC1RR_1Lh1RT_0Lf1Lh_0Lh---_1Lf1RT_1Lh0RC".
Definition tm1 := TM'_from_str "1LB1RG_1LC1LB_1LF0RD_1RI1RE_1RA1LF_1RA0LC_1RA1RH_---0RD_1LF0RD".
Definition tm2 := TM'_from_str "1LB1RG_1LC1LB_1LF0RD_1RI1RE_1RA1LF_1RA0LC_1RA1RH_1RJ0RD_1LF0RD_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "lhOCaVT[J".
Definition mp' := mp_from_str "lhOCaVT[J".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM441.


Module TM442.
Definition tm := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RF1RD_---1LA_0LB1LE_1LE1RC".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO0LV_1RJ0LO_1LO1LV_1Ra1LO_0RT0RA_1LV0RC_1RT1RA_0RC1RC_0LV1LV_0LX1Rl_1LV0RC_1LX1LV_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_0Lh---_1Rl0LO_1Lh---_1R[1LO_---1LV_---1LO_---0RC_---1Lh_---0Lf_---0Lh_---1Lf_---1Lh_1Rl1LV_0RJ1LO_0LO0RC_1RJ1Lh_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_1LV0RR_1LO0RT_0RC1RR_1Lh1RT_0Lf1Lh_0Lh---_1Lf1RT_1Lh0RC".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LO0LV_1RJ0LO_1LO1LV_1Ra1LO_0RT0RA_1LV0RC_1RT1RA_0RC1RC_0LV1LV_0LX1Rl_1LV0RC_1LX1LV_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_0Lh---_1Rl0LO_1Lh---_1R\1LO_---0RC_---1LV_---1RC_---0RC_---0LF_---0LH_---1LF_---1LH_1Rl1LV_0RJ1LO_0LO0RC_1RJ1Lh_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_1LV0RR_1LO0RT_0RC1RR_1Lh1RT_0Lf1Lh_0Lh---_1Lf1RT_1Lh0RC".
Definition tm1 := TM'_from_str "1LB1RG_1LC1LB_1LF0RD_1RI1RE_1RA1LF_1RA0LC_1RA1RH_---0RD_1LF0RD".
Definition tm2 := TM'_from_str "1LB1RG_1LC1LB_1LF0RD_1RI1RE_1RA1LF_1RA0LC_1RA1RH_1RJ0RD_1LF0RD_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "lhOCaVT[J".
Definition mp' := mp_from_str "lhOCaVT\J".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM442.


Module TM443.
Definition tm := TM_from_str "1LB1RE_0LC1RE_0LD1RC_1RD0RA_---1RF_1LB0RF".
Definition tm' := TM_from_str "1LB1RE_0LC1RE_0LD0RA_1RD0RA_---1RF_1LB0RF".
Definition tm0 := TM'_from_str "1L]0Rb_0Rl0Rd_1LW1Rb_1Rl1Rd_0LN---_0LP1Rl_1LN---_1LP1Rk_1R\0Rb_1L]0Rd_0LW1Rb_1LW1Rd_0LU---_0LW1Rl_1LU---_1LW1Rk_0R\0RR_1L]0RT_1R\1RR_1LW1RT_0L]0LW_0L_1LW_1L]1LW_1L_1RT_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1R\0LW_1LW---_1RC1LW_1Rb0Rl_---0Rj_---0Rl_---1Rj_---1Rl_---1Rl_---1LW_---1Rk_---1Ri_1L]0Ri_0Rl0Rk_1LW1Ri_1Rl1Rk_0LN0LW_0LP1L]_1LN1LW_1LP0Ri".
Definition tm0' := TM'_from_str "1L]0Rb_0Rl0Rd_1LW1Rb_1Rl1Rd_0LN---_0LP1Rl_1LN---_1LP1Rk_1R\0Rb_1L]0Rd_0LW1Rb_1LW1Rd_0LU---_0LW1Rl_1LU---_1LW1Rk_0R\0RA_1L]0RC_1R\1RA_1LW1RC_0L]0LW_0L_---_1L]1LW_1L_0Rl_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1R\0LW_1LW---_1RC1LW_1Rb0Rl_---0Rj_---0Rl_---1Rj_---1Rl_---1Rl_---1LW_---1Rk_---1Ri_1L]0Ri_0Rl0Rk_1LW1Ri_1Rl1Rk_0LN0LW_0LP1L]_1LN1LW_1LP0Ri".
Definition tm1 := TM'_from_str "1LB0RA_1RC0LE_1RC1RD_1LE1RF_1LB1LE_---0RG_1RG1RH_1LE1RA".
Definition tm2 := TM'_from_str "1LB0RA_1RC0LE_1RC1RD_1LE1RF_1LB1LE_1RI0RG_1RG1RH_1LE1RA_1RI1RI".
Definition l0 := [1;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "i]\CWblk".
Definition mp' := mp_from_str "i]\CWblk".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM443.


Module TM444.
Definition tm := TM_from_str "1LB1RE_0LC1RE_0LD0RA_1RD0RA_---1RF_1LB0RF".
Definition tm' := TM_from_str "1LB0RA_0LC1RF_0LD0RA_1RD0RE_1LB1RF_---1RA".
Definition tm0 := TM'_from_str "1L]0Rb_0Rl0Rd_1LW1Rb_1Rl1Rd_0LN---_0LP1Rl_1LN---_1LP1Rk_1R\0Rb_1L]0Rd_0LW1Rb_1LW1Rd_0LU---_0LW1Rl_1LU---_1LW1Rk_0R\0RA_1L]0RC_1R\1RA_1LW1RC_0L]0LW_0L_---_1L]1LW_1L_0Rl_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1R\0LW_1LW---_1RC1LW_1Rb0Rl_---0Rj_---0Rl_---1Rj_---1Rl_---1Rl_---1LW_---1Rk_---1Ri_1L]0Ri_0Rl0Rk_1LW1Ri_1Rl1Rk_0LN0LW_0LP1L]_1LN1LW_1LP0Ri".
Definition tm0' := TM'_from_str "1L]0RA_0RD0RC_1LW1RA_1RD1RC_0LN0LW_0LP1L]_1LN1LW_1LP0RA_1R\0Rj_1L]0Rl_0LW1Rj_1LW1Rl_0LU---_0LW1RD_1LU---_1LW1RC_0R\0RA_1L]0RC_1R\1RA_1LW1RC_0L]0LW_0L_1L]_1L]1LW_1L_0RA_0RZ0Ra_0R\0Rc_1RZ1Ra_1R\1Rc_1R\0LW_1LW---_1Rc1LW_1Rj0RD_1L]0Rj_0RD0Rl_1LW1Rj_1RD1Rl_0LN---_0LP1RD_1LN---_1LP1RC_---0RB_---0RD_---1RB_---1RD_---1RD_---1LW_---1RC_---1RA".
Definition tm1 := TM'_from_str "1LB0RA_1RC0LE_1RC1RD_1LE1RF_1LB1LE_---0RG_1RG1RH_1LE1RA".
Definition tm2 := TM'_from_str "1LB0RA_1RC0LE_1RC1RD_1LE1RF_1LB1LE_1RI0RG_1RG1RH_1LE1RA_1RI1RI".
Definition l0 := [1;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "i]\CWblk".
Definition mp' := mp_from_str "A]\cWjDC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM444.


Module TM445.
Definition tm := TM_from_str "1LB0RE_0LC1LC_0LD1RA_1RD0RA_0RF1RC_---1LD".
Definition tm' := TM_from_str "1LB0RE_0LC1LC_0LD1RA_1RD0RA_1RF1RC_---0RA".
Definition tm0 := TM'_from_str "1L]0Ra_1L_0Rc_1LX1Ra_1RR1Rc_0LN---_0LP1L]_1LN0RC_1LP0RD_1R\1RC_1L_0Rc_0LW1LW_1RR1Rc_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0R\0RB_1L]0RD_1R\1RB_1LX1RD_0L]0LX_0L_1Ri_1L]1LX_1L_1RR_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1R\0LW_1LX0Ri_1RC1LW_1Ra0RR_0Ri0RR_0Rk0RT_1Ri1RR_1Rk1RT_---0LW_1LX1RR_---1LW_1Ra1Rc_---0RC_---0Ra_---1RC_---1Ra_---0L^_---0L`_---1L^_---1L`".
Definition tm0' := TM'_from_str "1L]0Ra_1L_0Rc_1LX1Ra_1RR1Rc_0LN---_0LP1L]_1LN0RC_1LP0RD_1R\1RC_1L_0Rc_0LW1LW_1RR1Rc_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0R\0RB_1L]0RD_1R\1RB_1LX1RD_0L]0LX_0L_1Rj_1L]1LX_1L_1RR_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1R\0LW_1LX0Rj_1RC1LW_1Ra0RR_0Rj0RR_0Rl0RT_1Rj1RR_1Rl1RT_---0LW_1LX1RR_---1LW_1Ra1Rc_---0RA_---0RC_---1RA_---1RC_---0LW_---0Rj_---1LW_---0RR".
Definition tm1 := TM'_from_str "1LB0RF_1RC0LG_1RC1RD_1LE1RK_1LJ1RA_1RA1RH_1LB1LE_1RI1RA_---0RD_1RD1LG_0RI0RA".
Definition tm2 := TM'_from_str "1LB0RF_1RC0LG_1RC1RD_1LE1RK_1LJ1RA_1RA1RH_1LB1LE_1RI1RA_1RL0RD_1RD1LG_0RI0RA_1RL1RL".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "R]\CXDWci_a".
Definition mp' := mp_from_str "R]\CXDWcj_a".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM445.


Module TM446.
Definition tm := TM_from_str "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE".
Definition tm' := TM_from_str "1RB1LE_1RC1RA_0LD0LB_1LE1LD_1RF0LA_---0RE".
Definition tm0 := TM'_from_str "0RJ0Rc_0RL1RL_1RJ1Rc_1RL1Lf_0L`0Lf_1RL0Lh_1RL1Lf_1Lf1Lh_0RR0RB_0RT0RD_1RR1RB_1RT1RD_0L^1RT_1RT0LG_1L^1RD_1RD1LG_1Rj0RJ_0Lh0RL_0LG1RJ_0L`1RL_0L]0L`_0L_1RL_1L]1RL_1L_1Lf_0Rc1RT_1RL1Lh_1Rc1LG_1Lf1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_0Rj0RT_0Rl1Rj_1Rj1RT_1Rl0LG_---0LE_1Rj0LG_---1LE_1RT1LG_---0Ra_---0Rc_---1Ra_---1Rc_------_---0L`_---0Rc_---1RL".
Definition tm0' := TM'_from_str "0RJ0Rc_0RL1RL_1RJ1Rc_1RL1Lf_0L`0Lf_1RL0Lh_1RL1Lf_1Lf1Lh_0RR0RB_0RT0RD_1RR1RB_1RT1RD_0L^1RT_1RT0LG_1L^1RD_1RD1LG_1Rj0Lh_0Lh0RL_0LG0L`_0L`1RL_0L]0LM_0L_0LO_1L]1LM_1L_1LO_0Rc1RT_1RL1Lh_1Rc1LG_1Lf1L`_0Lf0L^_0Lh0L`_1Lf1L^_1Lh1L`_0Rj0RT_0Rl1Rj_1Rj1RT_1Rl0LG_---0LE_1Rj0LG_---1LE_1RT1LG_---0Ra_---0Rc_---1Ra_---1Rc_------_---0L`_---0Rc_---1RL".
Definition tm1 := TM'_from_str "0LB1RD_1LC1LB_1RA1LG_1RA1RE_1RD1LF_1RH0LG_1RD1LF_---0RI_1RH1RA".
Definition tm2 := TM'_from_str "0LB1RD_1LC1LB_1RA1LG_1RA1RE_1RD1LF_1RH0LG_1RD1LF_1RJ0RI_1RH1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "T`hLDfGjc".
Definition mp' := mp_from_str "T`hLDfGjc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM446.


Module TM447.
Definition tm := TM_from_str "1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---".
Definition tm' := TM_from_str "1RB0LD_0LB1RC_1RD---_1LA0LE_0LF0RA_0RC1LE".
Definition tm0 := TM'_from_str "0RJ1RT_0RL0Le_1RJ0LW_1RL0RT_1L]0LU_1RT0LW_1RJ1LU_---1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LW1L]_0RT---_1LW1RJ_0Rk---_0Rk1LF_1LF0RJ_1Rk0L^_1L]1RJ_0LF0L]_0LH0L__1LF1L]_1LH1L__0RR0RA_0Lg0RC_1RR1RA_0LF1RC_0Le0RT_0Lg0LF_1Le0Rk_1Lg1LF_0RI0RJ_0RK1RT_1RI1L^_1RK0LW_1LF0L^_0RT0L`_0RJ1L^_---1L`_0RT---_0LF---_1RT---_0L]---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ1R\_0RL0Lm_1RJ0L__1RL0R\_1Le0L]_1R\0L__1RJ1L]_---1L__0LM0RR_0R\0RT_1Le1RR_1R\1RT_0LM1Le_0LO---_1LM1RJ_1LO---_0RZ---_0R\---_1RZ---_1R\---_0L_---_0R\---_1L_---_0RT---_0RT1LF_1LF0RJ_1RT0Lf_1Le1RJ_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RZ0RA_0Lo0RC_1RZ1RA_0LF1RC_0Lm0R\_0Lo0LF_1Lm0RT_1Lo1LF_0RQ0RJ_0RS1R\_1RQ1Lf_1RS0L__1LF0Lf_---0Lh_0RJ1Lf_---1Lh".
Definition tm1 := TM'_from_str "1LB1RF_0LC0RA_1LG0LD_0LE0LG_0RF1LD_0RA0RI_1RA0LH_1LG1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0RA_1LG0LD_0LE0LG_0RF1LD_0RA0RI_1RA0LH_1LG1LB_1RA1RJ_1RJ1RJ".
Definition l0 := [0;1;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "T]e^gJFWk".
Definition mp' := mp_from_str "\emfoJF_T".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM447.


Module TM448.
Definition tm := TM_from_str "1RB0LD_0LB1RC_1RD---_1LA0LE_0LF0RA_0RC1LE".
Definition tm' := TM_from_str "1RB0LC_1RC1RF_1LA0LD_0LE0RA_0RB1LD_1RC---".
Definition tm0 := TM'_from_str "0RJ1R\_0RL0Lm_1RJ0L__1RL0R\_1Le0L]_1R\0L__1RJ1L]_---1L__0LM0RR_0R\0RT_1Le1RR_1R\1RT_0LM1Le_0LO---_1LM1RJ_1LO---_0RZ---_0R\---_1RZ---_1R\---_0L_---_0R\---_1L_---_0RT---_0RT1LF_1LF0RJ_1RT0Lf_1Le1RJ_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RZ0RA_0Lo0RC_1RZ1RA_0LF1RC_0Lm0R\_0Lo0LF_1Lm0RT_1Lo1LF_0RQ0RJ_0RS1R\_1RQ1Lf_1RS0L__1LF0Lf_---0Lh_0RJ1Lf_---1Lh".
Definition tm0' := TM'_from_str "0RJ1RT_0RL0Le_1RJ0LW_1RL0RT_1L]0LU_1RT0LW_1RJ1LU_---1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0LW1L]_0RT---_1LW1RJ_0Rl---_0Rl1LF_1LF0RJ_1Rl0L^_1L]1RJ_0LF0L]_0LH0L__1LF1L]_1LH1L__0RR0RA_0Lg0RC_1RR1RA_0LF1RC_0Le0RT_0Lg0LF_1Le0Rl_1Lg1LF_0RI0RJ_0RK1RT_1RI1L^_1RK0LW_1LF0L^_0RT0L`_0RJ1L^_---1L`_0RR---_0RT---_1RR---_1RT---_0LW---_0RT---_1LW---_0Rl---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0RA_1LG0LD_0LE0LG_0RF1LD_0RA0RI_1RA0LH_1LG1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0RA_1LG0LD_0LE0LG_0RF1LD_0RA0RI_1RA0LH_1LG1LB_1RA1RJ_1RJ1RJ".
Definition l0 := [0;1;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "\emfoJF_T".
Definition mp' := mp_from_str "T]e^gJFWl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM448.


Module TM449.
Definition tm := TM_from_str "1RB0LC_1RC1RF_1LA0LD_0LE0RA_0RB1LD_1RC---".
Definition tm' := TM_from_str "1RB0LC_1RC1RF_1LA0LD_0LE0RA_0RF1LD_1RC---".
Definition tm0 := TM'_from_str "0RJ1RT_0RL0Le_1RJ0LW_1RL0RT_1L]0LU_1RT0LW_1RJ1LU_---1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0LW1L]_0RT---_1LW1RJ_0Rl---_0Rl1LF_1LF0RJ_1Rl0L^_1L]1RJ_0LF0L]_0LH0L__1LF1L]_1LH1L__0RR0RA_0Lg0RC_1RR1RA_0LF1RC_0Le0RT_0Lg0LF_1Le0Rl_1Lg1LF_0RI0RJ_0RK1RT_1RI1L^_1RK0LW_1LF0L^_0RT0L`_0RJ1L^_---1L`_0RR---_0RT---_1RR---_1RT---_0LW---_0RT---_1LW---_0Rl---".
Definition tm0' := TM'_from_str "0RJ1RT_0RL0Le_1RJ0LW_1RL0RT_1L]0LU_1RT0LW_1RJ1LU_---1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0LW1L]_0RT---_1LW1RJ_0Rl---_0Rl1LF_1LF0RJ_1Rl0L^_1L]1RJ_0LF0L]_0LH0L__1LF1L]_1LH1L__0RR0RA_0Lg0RC_1RR1RA_0LF1RC_0Le0RT_0Lg0LF_1Le0Rl_1Lg1LF_0Ri0RJ_0Rk1RT_1Ri1L^_1Rk0LW_1LF0L^_---0L`_0RJ1L^_---1L`_0RR---_0RT---_1RR---_1RT---_0LW---_0RT---_1LW---_0Rl---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0RA_1LG0LD_0LE0LG_0RF1LD_0RA0RI_1RA0LH_1LG1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0RA_1LG0LD_0LE0LG_0RF1LD_0RA0RI_1RA0LH_1LG1LB_1RA1RJ_1RJ1RJ".
Definition l0 := [0;1;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "T]e^gJFWl".
Definition mp' := mp_from_str "T]e^gJFWl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM449.


Module TM450.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_1LB---".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB1LF_0RB0LE_0RC---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L_1Le_1RJ0Le_1L_1RA_1Rb1Le_1Rb0RA_1LN0RC_1Le1RA_1Lm1RC_0LV1LN_0LX0RK_1LV0RC_1LX0LH_0RC0LX_0LH0LN_1RC0RK_0Le---_0LF0L]_0LH0L__1LF1L]_1LH1L__1LH0LX_0Rb---_1L_0RK_1Rb---_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RI1Rb_0RK0LH_1RI1Le_1RK0Le_0LH0Le_0RJ0Lg_1LH1Le_0Rb1Lg_1LH---_0Rb---_1L_---_1Rb---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0L_1Le_1RJ0Le_1L_1RA_1Rb1Le_1Rb0RA_1LN0RC_1Le1RA_1Ln1RC_0LV1LN_0LX0RK_1LV0RC_1LX0LH_0RC0LX_0LH0LN_1RC0RK_0Le---_0LF0L]_0LH0L__1LF1L]_1LH1L__1LH0LX_0Rb---_1L_0RK_1Rb---_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0RI1Rb_0RK0LH_1RI1Le_1RK0Le_0LH0Le_0RJ0Lg_1LH1Le_0Rb1Lg_0RQ---_0RS---_1RQ---_1RS---_1RJ---_0LN---_1Rb---_1LN---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0RJ_0LD0RF_1LH1LE_1LC1LK_1LI1RA_0RF0LH_1RG1LI_0LH0LI_1RB1RG_0LC---".
Definition tm2 := TM'_from_str "0RB0RG_1LC0RJ_0LD0RF_1LH1LE_1LC1LK_1LI1RA_0RF0LH_1RG1LI_0LH0LI_1RB1RG_0LC1RL_1RL1RL".
Definition l0 := [0;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "AJNX_KbHeCm".
Definition mp' := mp_from_str "AJNX_KbHeCn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM450.


Module TM451.
Definition tm := TM_from_str "1LB1LE_0RC0LE_1LD1RC_---1RA_1LA0RF_0LC1RE".
Definition tm' := TM_from_str "1LB1LF_0RC0LF_1LD1RC_---0RE_0LC1RF_1LA0RE".
Definition tm0 := TM'_from_str "0RR1LP_1LF0Rb_1RR1Lh_1L^1Rb_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0RQ0LP_0RS---_1RQ0Lh_1RS1LH_---0Le_0Rb0Lg_---1Le_0RT1Lg_---0RR_0Rb0RT_---1RR_1Rb1RT_0L^1LH_0L`1Rb_1L^0Rk_1L`1RT_---0RB_---0RD_---1RB_---1RD_---0Lg_---1LH_---1Lg_---0Rk_0RT0Ri_1LH0Rk_1Lg1Ri_0Rk1Rk_0LF0L^_0LH1LH_1LF1L^_1LH0Rk_---0Rb_0Rb0Rd_1LH1Rb_1Rb1Rd_0LU0Lh_0LW1LH_1LU1Lh_1LW1Rb".
Definition tm0' := TM'_from_str "0RR1LP_1LF0Rj_1RR1Lp_1L^1Rj_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0RQ0LP_0RS---_1RQ0Lp_1RS1LH_---0Lm_0Rj0Lo_---1Lm_0RT1Lo_---0RR_0Rj0RT_---1RR_1Rj1RT_0L^1LH_0L`1Rj_1L^0Rc_1L`1RT_---0Ra_---0Rc_---1Ra_---1Rc_---0L^_---1LH_---1L^_---0Rc_---0Rj_0Rj0Rl_1LH1Rj_1Rj1Rl_0LU0Lp_0LW1LH_1LU1Lp_1LW1Rj_0RT0Ra_1LH0Rc_1Lo1Ra_0Rc1Rc_0LF0L^_0LH1LH_1LF1L^_1LH0Rc".
Definition tm1 := TM'_from_str "1LB0RD_1LE1LC_1LB0RD_1LB1RA_0RH1LF_1LG1LI_0LE0LC_1RA1RH_---1LB".
Definition tm2 := TM'_from_str "1LB0RD_1LE1LC_1LB0RD_1LB1RA_0RH1LF_1LG1LI_0LE0LC_1RA1RH_1RJ1LB_1RJ1RJ".
Definition l0 := [0;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "bHhkPgFT^".
Definition mp' := mp_from_str "jHpcPoFT^".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM451.


Module TM452.
Definition tm := TM_from_str "1LB1RD_0LC1LB_1LD1LF_1RE0RD_0LC1LA_0LE---".
Definition tm' := TM_from_str "1LB1RD_0LC0RE_1LD1LF_1RE0RD_0LC1LA_0LE---".
Definition tm0 := TM'_from_str "1L^0RZ_1LW0R\_1Ln1RZ_1LP1R\_0LN---_0LP1Rb_1LN1R[_1LP1RY_1Rb1L^_0Lg1LW_0Rb1Ln_---1LP_0LU0LN_0LW0LP_1LU1LN_1LW1LP_0R[1LU_0RY---_1R[1LF_1RY---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Ln0Lg_1Rb0Rb_1Ln0R[_1RY0RY_1Rb1LW_0Lg0R[_0Rb1LP_---1R[_0LU0LF_0LW0LH_1LU1LF_1LW1LH_0L^---_0LP---_0Ln---_1Rb---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "1L^0RZ_1LW0R\_1Ln1RZ_1LP1R\_0LN---_0LP1Rb_1LN1R[_1LP1RY_1Rb0Ra_0Lg0Rc_0Rb1Ra_---1Rc_0LU0L^_0LW0LP_1LU1L^_1LW1LP_0R[1LU_0RY---_1R[1LF_1RY---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_0Ln0Lg_1Rb0Rb_1Ln0R[_1RY0RY_1Rb1LW_0Lg0R[_0Rb1LP_---1R[_0LU0LF_0LW0LH_1LU1LF_1LW1LH_0L^---_0LP---_0Ln---_1Rb---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "0LB0RI_1LG1LC_0LD1RA_1LE1LD_1LH1LF_0LB---_0LH0LF_1RA0RA_1RA1RJ_0RA0RJ".
Definition tm2 := TM'_from_str "0LB0RI_1LG1LC_0LD1RA_1LE1LD_1LH1LF_0LB1RK_0LH0LF_1RA0RA_1RA1RJ_0RA0RJ_1RK1RK".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "bgFPWnU^[Y".
Definition mp' := mp_from_str "bgFPWnU^[Y".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM452.


Module TM453.
Definition tm := TM_from_str "1RB1RE_1RC1LD_0RD0RC_1LE0LF_1LB---_1RC0LA".
Definition tm' := TM_from_str "1RB1RE_1RC0LA_0RD0RC_1LE0LB_1LF---_1RC1LD".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1R[0L`_0Lo---_1RS1L`_1Lo---_0RR1LP_0RT1R[_1RR---_1RT1LE_1L`0L^_1RY0L`_1R[1L^_1RQ1L`_0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0LP1RQ_1L`0RY_1LP0R[_1R[0RQ_1RQ0R[_---1R[_1L`1R[_---0L`_0Lf0Lm_0Lh0Lo_1Lf1Lm_1Lh1Lo_0RS---_1Lh---_1RS---_1Lo---_0LN---_0LP---_1LN---_1LP---_0RR0RT_0RT1Lh_1RR1RT_1RT1Lo_1L`0LE_1RY0LG_1R[1LE_1RQ1LG".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1R[0L`_0L`---_1RS1L`_1L`---_0RR0RT_0RT1Lh_1RR1RT_1RT1LO_1L`0LE_1RY0LG_1R[1LE_1RQ1LG_0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0Lp1RQ_1L`0RY_1Lp0R[_1R[0RQ_1RQ0R[_---1R[_1L`1R[_---0L`_0Lf0LM_0Lh0LO_1Lf1LM_1Lh1LO_0RS---_1Lh---_1RS---_1LO---_0Ln---_0Lp---_1Ln---_1Lp---_0RR1Lp_0RT1R[_1RR---_1RT1LE_1L`0L^_1RY0L`_1R[1L^_1RQ1L`".
Definition tm1 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF---_1RG1LB_0RH0RG_1RG0RA".
Definition tm2 := TM'_from_str "1LB1RA_1LE1LC_1RA1LD_1RA0LB_1LF1RI_1RG1LB_0RH0RG_1RG0RA_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "[`oEhPQY".
Definition mp' := mp_from_str "[`OEhpQY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM453.


Module TM454.
Definition tm := TM_from_str "1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF".
Definition tm' := TM_from_str "1RB0RF_1RC1LC_1LD1RA_---0LE_1RB0LB_1RE0LF".
Definition tm0 := TM'_from_str "0RJ1Rd_0RL0L`_1RJ1LM_1RL1RB_1LM0LM_1RB0LO_1Rd1LM_1RL1LO_0RR---_0RT0Rk_1RR1LG_1RT1Rk_0LG0LV_1RL0LX_1LG1LV_1Rk1LX_---0Rb_1Rd0Rd_---1Rb_1LM1Rd_0L^1RT_0L`1RB_1L^1Rk_1L`1RL_---0RT_---0LG_---1RT_---0LV_---0LE_---0LG_---1LE_---1LG_1Lh0Ri_0RL0Rk_1Rk1Ri_1RL1Rk_0Lf0RL_0Lh1RT_1Lf0L`_1Lh1Rk_0RB0RL_0RD1RT_1RB1RL_1RD0Lm_1RT0Lm_0LV0Lo_1Rk1Lm_1LV1Lo".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1LM0RL_1Rb1RT_1RD0L`_1RL1Rk_0RR---_0RT0Rk_1RR1Lg_1RT1Rk_0Lg0LV_1RL0LX_1Lg1LV_1Rk1LX_---0RB_1RD0RD_---1RB_1LM1RD_0L^1RT_0L`1Rb_1L^1Rk_1L`1RL_---0RT_---0Lg_---1RT_---0LV_---0Le_---0Lg_---1Le_---1Lg_0RJ1RD_0RL0L`_1RJ1LM_1RL1Rb_1LM0LM_1Rb0LO_1RD1LM_1RL1LO_0Rb0RL_0Rd1RT_1Rb1RL_1Rd0Lm_1RT0Lm_0LV0Lo_1Rk1Lm_1LV1Lo".
Definition tm1 := TM'_from_str "1LB1RI_0LH0LC_0LG1RD_0RE0LG_1RA1RF_1RD1RE_---1LH_1RI1LB_1RE1RF".
Definition tm2 := TM'_from_str "1LB1RI_0LH0LC_0LG1RD_0RE0LG_1RA1RF_1RD1RE_1RJ1LH_1RI1LB_1RE1RF_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "TMVBLk`Gd".
Definition mp' := mp_from_str "TMVbLk`gD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM454.


Module TM455.
Definition tm := TM_from_str "1RB0RF_1RC1LC_1LD1RA_---0LE_1RB0LB_1RE0LF".
Definition tm' := TM_from_str "1RB0LB_1RC1LC_1LD1RE_---0LA_1LB0RF_1RA0LF".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_1LM0RL_1Rb1RT_1RD0L`_1RL1Rk_0RR---_0RT0Rk_1RR1Lg_1RT1Rk_0Lg0LV_1RL0LX_1Lg1LV_1Rk1LX_---0RB_1RD0RD_---1RB_1LM1RD_0L^1RT_0L`1Rb_1L^1Rk_1L`1RL_---0RT_---0Lg_---1RT_---0LV_---0Le_---0Lg_---1Le_---1Lg_0RJ1RD_0RL0L`_1RJ1LM_1RL1Rb_1LM0LM_1Rb0LO_1RD1LM_1RL1LO_0Rb0RL_0Rd1RT_1Rb1RL_1Rd0Lm_1RT0Lm_0LV0Lo_1Rk1Lm_1LV1Lo".
Definition tm0' := TM'_from_str "0RJ1Rd_0RL0L`_1RJ1LM_1RL1RB_1LM0LM_1RB0LO_1Rd1LM_1RL1LO_0RR---_0RT0Rk_1RR1LG_1RT1Rk_0LG0LV_1RL0LX_1LG1LV_1Rk1LX_---0Rb_1Rd0Rd_---1Rb_1LM1Rd_0L^0LX_0L`1RB_1L^1LX_1L`1RL_---0RT_---0LG_---1RT_---0LV_---0LE_---0LG_---1LE_---1LG_0Rd0Ri_1L`0Rk_1Rd1Ri_1RL1Rk_0LN0RL_0LP1RT_1LN0L`_1LP1Rk_0RB0RL_0RD1RT_1RB1RL_1RD0Lm_1RT0Lm_0LV0Lo_1Rk1Lm_1LV1Lo".
Definition tm1 := TM'_from_str "1LB1RI_0LH0LC_0LG1RD_0RE0LG_1RA1RF_1RD1RE_---1LH_1RI1LB_1RE1RF".
Definition tm2 := TM'_from_str "1LB1RI_0LH0LC_0LG1RD_0RE0LG_1RA1RF_1RD1RE_1RJ1LH_1RI1LB_1RE1RF_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "TMVbLk`gD".
Definition mp' := mp_from_str "TMVBLk`Gd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM455.


Module TM456.
Definition tm := TM_from_str "1LB0RC_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---0RC".
Definition tm' := TM_from_str "1LB0RC_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm0 := TM'_from_str "1L_0RQ_0RS0RS_1L`1RQ_1RS1RS_0LN1L`_0LP1Le_1LN1RQ_1LP1Rj_1RQ0Rj_1Rj0Rl_1Le1Rj_1Lg1Rl_0LV---_0LX1RC_1LV---_1LX1RK_0RC0RK_0LX1LX_1RC1RK_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1RQ_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1RQ1Le_1Rj1Lg_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LX0L__0RC---_1LX1L__0RK0RS_---0RQ_---0RS_---1RQ_---1RS_---1L`_---1Le_---1RQ_---1Rj".
Definition tm0' := TM'_from_str "1L_0RQ_---0RS_1L`1RQ_---1RS_0LN1L`_0LP1Le_1LN1RQ_1LP1RB_1RQ---_1RB---_1Le---_1Lg---_0LV---_0LX---_1LV---_1LX---_0RC0Rk_0LX1LX_1RC1Rk_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1RQ_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1RQ1Le_1RB1Lg_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LX0L__0RC---_1LX1L__0Rk0RS_1RQ0RB_1RB0RD_1Le1RB_1Lg1RD_0LV---_0LX1RC_1LV---_1LX1Rk".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_---0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_1RK0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "SC`gXjK_Qe".
Definition mp' := mp_from_str "SC`gXBk_Qe".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM456.


Module TM457.
Definition tm := TM_from_str "1LB0RC_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm' := TM_from_str "1LB0RC_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE".
Definition tm0 := TM'_from_str "1L_0RQ_---0RS_1L`1RQ_---1RS_0LN1L`_0LP1Le_1LN1RQ_1LP1RB_1RQ---_1RB---_1Le---_1Lg---_0LV---_0LX---_1LV---_1LX---_0RC0Rk_0LX1LX_1RC1Rk_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1RQ_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1RQ1Le_1RB1Lg_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LX0L__0RC---_1LX1L__0Rk0RS_1RQ0RB_1RB0RD_1Le1RB_1Lg1RD_0LV---_0LX1RC_1LV---_1LX1Rk".
Definition tm0' := TM'_from_str "1L_0RQ_0Rd0RS_1L`1RQ_1Rd1RS_0LN1L`_0LP1Le_1LN1RQ_1LP1Rj_1RQ0Rj_1Rj0Rl_1Le1Rj_1Lg1Rl_0LV---_0LX1RC_1LV---_1LX1RK_0RC0RK_0LX1LX_1RC1RK_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1RQ_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1RQ1Le_1Rj1Lg_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LX0L__0RC---_1LX1L__0RK0Rd_---0Rb_---0Rd_---1Rb_---1Rd_---1L`_---1Le_---1RQ_---1Rj".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_---0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_1RK0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "SC`gXBk_Qe".
Definition mp' := mp_from_str "dC`gXjK_Qe".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM457.


Module TM458.
Definition tm := TM_from_str "1LB0RC_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE".
Definition tm' := TM_from_str "1LB1RE_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE".
Definition tm0 := TM'_from_str "1L_0RQ_0Rd0RS_1L`1RQ_1Rd1RS_0LN1L`_0LP1Le_1LN1RQ_1LP1Rj_1RQ0Rj_1Rj0Rl_1Le1Rj_1Lg1Rl_0LV---_0LX1RC_1LV---_1LX1RK_0RC0RK_0LX1LX_1RC1RK_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1RQ_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1RQ1Le_1Rj1Lg_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LX0L__0RC---_1LX1L__0RK0Rd_---0Rb_---0Rd_---1Rb_---1Rd_---1L`_---1Le_---1RQ_---1Rj".
Definition tm0' := TM'_from_str "1L_0Rb_0Rd0Rd_1L`1Rb_1Rd1Rd_0LN1L`_0LP1Le_1LN1Rb_1LP1Rj_1Rb0Rj_1Rj0Rl_1Le1Rj_1Lg1Rl_0LV---_0LX1RC_1LV---_1LX1RK_0RC0RK_0LX1LX_1RC1RK_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1Rb_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1Rb1Le_1Rj1Lg_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LX0L__0RC---_1LX1L__0RK0Rd_---0Rb_---0Rd_---1Rb_---1Rd_---1L`_---1Le_---1Rb_---1Rj".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_---0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_1RK0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "dC`gXjK_Qe".
Definition mp' := mp_from_str "dC`gXjK_be".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM458.


Module TM459.
Definition tm := TM_from_str "1LB1RE_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE".
Definition tm' := TM_from_str "1LB1RE_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm0 := TM'_from_str "1L_0Rb_0Rd0Rd_1L`1Rb_1Rd1Rd_0LN1L`_0LP1Le_1LN1Rb_1LP1Rj_1Rb0Rj_1Rj0Rl_1Le1Rj_1Lg1Rl_0LV---_0LX1RC_1LV---_1LX1RK_0RC0RK_0LX1LX_1RC1RK_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1Rb_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1Rb1Le_1Rj1Lg_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LX0L__0RC---_1LX1L__0RK0Rd_---0Rb_---0Rd_---1Rb_---1Rd_---1L`_---1Le_---1Rb_---1Rj".
Definition tm0' := TM'_from_str "1L_0Rb_---0Rd_1L`1Rb_---1Rd_0LN1L`_0LP1Le_1LN1Rb_1LP1RB_1Rb---_1RB---_1Le---_1Lg---_0LV---_0LX---_1LV---_1LX---_0RC0Rk_0LX1LX_1RC1Rk_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1Rb_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1Rb1Le_1RB1Lg_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LX0L__0RC---_1LX1L__0Rk0Rd_1Rb0RB_1RB0RD_1Le1RB_1Lg1RD_0LV---_0LX1RC_1LV---_1LX1Rk".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_---0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_1RK0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "dC`gXjK_be".
Definition mp' := mp_from_str "dC`gXBk_be".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM459.


Module TM460.
Definition tm := TM_from_str "1LB1RE_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm' := TM_from_str "1LB1RE_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---0RC".
Definition tm0 := TM'_from_str "1L_0Rb_---0Rd_1L`1Rb_---1Rd_0LN1L`_0LP1Le_1LN1Rb_1LP1RB_1Rb---_1RB---_1Le---_1Lg---_0LV---_0LX---_1LV---_1LX---_0RC0Rk_0LX1LX_1RC1Rk_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1Rb_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1Rb1Le_1RB1Lg_0RA0Ri_0RC0Rk_1RA1Ri_1RC1Rk_0LX0L__0RC---_1LX1L__0Rk0Rd_1Rb0RB_1RB0RD_1Le1RB_1Lg1RD_0LV---_0LX1RC_1LV---_1LX1Rk".
Definition tm0' := TM'_from_str "1L_0Rb_0RS0Rd_1L`1Rb_1RS1Rd_0LN1L`_0LP1Le_1LN1Rb_1LP1Rj_1Rb0Rj_1Rj0Rl_1Le1Rj_1Lg1Rl_0LV---_0LX1RC_1LV---_1LX1RK_0RC0RK_0LX1LX_1RC1RK_0L_1L__0L]0L^_0L_0L`_1L]1L^_1L_1L`_0Rb1L__0Rd1Rb_1Rb1L`_1Rd1Le_1L`0Le_1Le0Lg_1Rb1Le_1Rj1Lg_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LX0L__0RC---_1LX1L__0RK0RS_---0RQ_---0RS_---1RQ_---1RS_---1L`_---1Le_---1Rb_---1Rj".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_---0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RI_1RF1LD_1LE1LH_1LH1LC_1RK0RA_1LJ1RF_1RI1LJ_0RB0RG_0LE0LH_1RK1RK".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "dC`gXBk_be".
Definition mp' := mp_from_str "SC`gXjK_be".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM460.


Module TM461.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1RD---_1LC1RB".
Definition tm' := TM_from_str "1RB1RE_1LC0LF_1LD0LC_1RA0RB_1RD---_0RA1RE".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1RD---_1LW1Rk_1Rk---_---0RZ_1L^0R\_0R\1RZ_1LU1R\_0LV1RL_0LX0R\_1LV1Rd_1LX1RJ_0Rd1R\_0RJ0L^_1Rd1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1LU0L`_1R\1L^_1R\1L`_---0R\_0RZ---_0R\---_1RZ---_1R\---_1RL---_0R\---_1Rd---_1RJ---_---0RJ_1L^0RL_0R\1RJ_1LU1RL_0LV0LW_0LX1RD_1LV1LW_1LX1Rk".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1RD---_1LW1RK_1RK---_---0RJ_1L^0R\_0R\1RJ_1LU1R\_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0Rd1R\_0RJ0L^_1Rd1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L`_1R\1L^_1R\1L`_---0R\_0RZ---_0R\---_1RZ---_1R\---_1RL---_0R\---_1Rd---_1RJ---_0RA0Rb_0RC0Rd_1RA1Rb_1RC1Rd_1L^1RD_0R\---_0R\1RK".
Definition tm1 := TM'_from_str "1RB---_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB".
Definition tm2 := TM'_from_str "1RB1RI_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB_1RI1RI".
Definition l0 := [1;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "d\DLU^kJ".
Definition mp' := mp_from_str "d\DLU^KJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM461.


Module TM462.
Definition tm := TM_from_str "1RB1RE_1LC0LF_1LD0LC_1RA0RB_1RD---_0RA1RE".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1LF---_1LC1RB".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1RD---_1LW1RK_1RK---_---0RJ_1L^0R\_0R\1RJ_1LU1R\_0LV0Lm_0LX0Lo_1LV1Lm_1LX1Lo_0Rd1R\_0RJ0L^_1Rd1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L`_1R\1L^_1R\1L`_---0R\_0RZ---_0R\---_1RZ---_1R\---_1RL---_0R\---_1Rd---_1RJ---_0RA0Rb_0RC0Rd_1RA1Rb_1RC1Rd_1L^1RD_0R\---_0R\1RK".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1RD---_1LW1Rk_1Rk---_---0RZ_1L^0R\_0R\1RZ_1LU1R\_0LV1RL_0LX0R\_1LV1Rd_1LX1RJ_0Rd1R\_0RJ0L^_1Rd1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1LU0L`_1R\1L^_1R\1L`_---0R\_1L`---_0R\---_1LW---_1R\---_0Ln---_0Lp---_1Ln---_1Lp---_---0RJ_1L^0RL_0R\1RJ_1LU1RL_0LV0LW_0LX1RD_1LV1LW_1LX1Rk".
Definition tm1 := TM'_from_str "1RB---_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB".
Definition tm2 := TM'_from_str "1RB1RI_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB_1RI1RI".
Definition l0 := [1;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "d\DLU^KJ".
Definition mp' := mp_from_str "d\DLU^kJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM462.


Module TM463.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1LF---_1LC1RB".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1LA---_1LC1RB".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1RD---_1LW1Rk_1Rk---_---0RZ_1L^0R\_0R\1RZ_1LU1R\_0LV1RL_0LX0R\_1LV1Rd_1LX1RJ_0Rd1R\_0RJ0L^_1Rd1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1LU0L`_1R\1L^_1R\1L`_---0R\_1L`---_0R\---_1LW---_1R\---_0Ln---_0Lp---_1Ln---_1Lp---_---0RJ_1L^0RL_0R\1RJ_1LU1RL_0LV0LW_0LX1RD_1LV1LW_1LX1Rk".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RD_1RD---_1LW1Rk_1Rk---_---0RZ_1L^0R\_0R\1RZ_1LU1R\_0LV1RL_0LX0R\_1LV1Rc_1LX1RJ_0Rc1R\_0RJ0L^_1Rc1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1LU0L`_1R\1L^_1R\1L`_---0R\_0R\---_------_1R\---_------_0LF---_0LH---_1LF---_1LH---_---0RJ_1L^0RL_0R\1RJ_1LU1RL_0LV0LW_0LX1RD_1LV1LW_1LX1Rk".
Definition tm1 := TM'_from_str "1RB---_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB".
Definition tm2 := TM'_from_str "1RB1RI_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB_1RI1RI".
Definition l0 := [1;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "d\DLU^kJ".
Definition mp' := mp_from_str "c\DLU^kJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM463.


Module TM464.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1LA---_1LC1RB".
Definition tm' := TM_from_str "1RB1RE_1LC0LA_1LD0LC_1RA0RF_1RD---_1LC1RB".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RD_1RD---_1LW1Rk_1Rk---_---0RZ_1L^0R\_0R\1RZ_1LU1R\_0LV1RL_0LX0R\_1LV1Rc_1LX1RJ_0Rc1R\_0RJ0L^_1Rc1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1LU0L`_1R\1L^_1R\1L`_---0R\_0R\---_------_1R\---_------_0LF---_0LH---_1LF---_1LH---_---0RJ_1L^0RL_0R\1RJ_1LU1RL_0LV0LW_0LX1RD_1LV1LW_1LX1Rk".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RD_1RD---_1LW1Rk_1Rk---_---1L^_1L^0R\_0R\1LU_1LU1R\_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0Rd1R\_0RJ0L^_1Rd1L^_1RJ0LU_0L^0LU_0L`0LW_1L^1LU_1L`1LW_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_1LU0L`_1R\1L^_1R\1L`_---0R\_0RZ---_0R\---_1RZ---_1R\---_1RL---_0R\---_1Rd---_1RJ---_---0RJ_1L^0RL_0R\1RJ_1LU1RL_0LV0LW_0LX1RD_1LV1LW_1LX1Rk".
Definition tm1 := TM'_from_str "1RB---_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB".
Definition tm2 := TM'_from_str "1RB1RI_1RC1RG_1RD1RA_1LE1RB_0LF0LE_1RB1LF_0RB1RH_1LF0RB_1RI1RI".
Definition l0 := [1;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "c\DLU^kJ".
Definition mp' := mp_from_str "d\DLU^kJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM464.


Module TM465.
Definition tm := TM_from_str "1LB0RC_1RC0LF_1RA1RD_0LE0RC_---1RB_1LB0LD".
Definition tm' := TM_from_str "1LB0LD_1RC0LA_1RF1RD_0LE0RC_---1RB_1LB1LC".
Definition tm0 := TM'_from_str "0R\0RQ_1LN0RS_1R\1RQ_1L]1RS_0LN1LN_0LP0RT_1LN0RS_1LP0RS_0RR1RT_0RT0Le_1RR0Lo_1RT1LN_1L]0Lm_1RT0Lo_1RS1Lm_1RS1Lo_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_0Lo1RD_1RB1RB_1Lo1R\_1RZ1RZ_---0RQ_0RT0RS_---1RQ_1RT1RS_0Le1LN_0Lg0RT_1Le0RS_1Lg0RS_---0RJ_---0RL_---1RJ_---1RL_---1RD_---0L]_---1R\_---1L]_0R\---_1LN0RB_1R\1RD_1L]1RB_0LN0L]_0LP0L__1LN1L]_1LP1L_".
Definition tm0' := TM'_from_str "0R\---_1LN0Rj_1R\1Rl_1L]1Rj_0LN0L]_0LP0L__1LN1L]_1LP1L__0RR1RT_0RT0Le_1RR0LG_1RT1LN_1L]0LE_1RT0LG_1RS1LE_1RS1LG_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_0LG1Rl_1Rj1Rj_1LG1R\_1RZ1RZ_---0RQ_0RT0RS_---1RQ_1RT1RS_0Le1LN_0Lg0RT_1Le0RS_1Lg0RS_---0RJ_---0RL_---1RJ_---1RL_---1Rl_---0L]_---1R\_---1L]_0R\0RS_1LN0RS_1R\1RS_1L]1RS_0LN0LV_0LP0LX_1LN1LV_1LP1LX".
Definition tm1 := TM'_from_str "1RB1RH_1RC1RA_1LD1RH_0LG1LE_1RB0LF_1LE1LD_---1RC_1RJ1RI_0RB0RH_1LE0RH".
Definition tm2 := TM'_from_str "1RB1RH_1RC1RA_1LD1RH_0LG1LE_1RB0LF_1LE1LD_1RK1RC_1RJ1RI_0RB0RH_1LE0RH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "\TD]NoeSZB".
Definition mp' := mp_from_str "\Tl]NGeSZj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM465.


Module TM466.
Definition tm := TM_from_str "1RB0LA_1RC1LB_1LB1RD_1RE0RC_1LA0RF_1RC---".
Definition tm' := TM_from_str "1RB0LA_1RC---_1LD1RE_1RC1LD_1RF0RC_1LA0RB".
Definition tm0 := TM'_from_str "0RJ0RT_0RL1LP_1RJ1RT_1RL0LE_1LP0LE_0LP0LG_1R\1LE_1LP1LG_0RR0R\_0RT1RS_1RR1R\_1RT1LP_0LP0LN_1Rd0LP_1LP1LN_1RS1LP_0R\0RZ_1RS0R\_1R\1RZ_1LP1R\_0LN1LE_0LP1R\_1LN1Rk_1LP1RZ_0Rb0RQ_0Rd0RS_1Rb1RQ_1Rd1RS_0LG1Rd_1RR0Rd_1LG1RS_---0RS_1RS0Ri_1R\0Rk_1LP1Ri_1LE1Rk_0LF1RS_0LH---_1LF0R\_1LH---_0RR---_0RT---_1RR---_1RT---_0LP---_1Rd---_1LP---_1RS---".
Definition tm0' := TM'_from_str "0RJ0RT_0RL1L`_1RJ1RT_1RL0LE_1L`0LE_---0LG_1Rd1LE_---1LG_0RR---_0RT---_1RR---_1RT---_0L`---_1Rl---_1L`---_1RS---_0Rd0Rb_1RS0Rd_1Rd1Rb_1L`1Rd_0L^1LE_0L`1Rd_1L^1RK_1L`1Rb_0RR0Rd_0RT1RS_1RR1Rd_1RT1L`_0L`0L^_1Rl0L`_1L`1L^_1RS1L`_0Rj0RQ_0Rl0RS_1Rj1RQ_1Rl1RS_0LG1Rl_1RR0Rl_1LG1RS_---0RS_---0RI_1Rd0RK_---1RI_1LE1RK_0LF1RS_0LH---_1LF0Rd_1LH---".
Definition tm1 := TM'_from_str "1RB---_1RC0RD_1RD1RH_1RE1RC_1LF1RA_1LG0LF_1RC1LG_0RE0RC".
Definition tm2 := TM'_from_str "1RB1RI_1RC0RD_1RD1RH_1RE1RC_1LF1RA_1LG0LF_1RC1LG_0RE0RC_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "kRS\dEPZ".
Definition mp' := mp_from_str "KRSdlE`b".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM466.


Module TM467.
Definition tm := TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---".
Definition tm' := TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0LC---".
Definition tm0 := TM'_from_str "0RJ0L^_0RL0LU_1RJ0RT_1RL---_1LU0Le_1RT0Lg_1RC1Le_1RL1Lg_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0LX1LU_1RJ1RT_1LX1RC_0RT1RL_1RL0RA_1L`0RC_1Lg1RA_1LU1RC_0L^0RT_0L`0LU_1L^0RL_1L`1LU_0RL1LH_1LU0L^_1RL1LX_1Ln0RT_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0LH0L^_0RJ---_0LX0RT_1RJ---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RA---_0RC---_1RA---_1RC---_0RT---_0LU---_0RL---_1LU---".
Definition tm0' := TM'_from_str "0RJ0L^_0RL0LU_1RJ0RT_1RL---_1LU0Le_1RT0Lg_1RC1Le_1RL1Lg_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0LX1LU_1RJ1RT_1LX1RC_0RT1RL_1RL0RA_1L`0RC_1Lg1RA_1LU1RC_0L^0RT_0L`0LU_1L^0RL_1L`1LU_0RL1LH_1LU0L^_1RL1LX_1Lm0RT_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0LH0L^_0RJ---_0LX0RT_1RJ---_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0LH---_0RJ---_0LX---_1RJ---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0RA_0LH0LD_1LE1LB_1LH1LD_1RG0RA_0RA0RI_1RI1LJ_1RA1RI_1LB1LK_0LB---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0RA_0LH0LD_1LE1LB_1LH1LD_1RG0RA_0RA0RI_1RI1LJ_1RA1RI_1LB1LK_0LB1RL_1RL1RL".
Definition l0 := [1;1;1;1;1;0;1;0]%N.
Definition mp := mp_from_str "TU^X`CJHLgn".
Definition mp' := mp_from_str "TU^X`CJHLgm".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM467.


Module TM468.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LA0LD_0RE1LC_1LC1RA_0RE---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LA0LD_0RE1LC_1LC1RF_1RB0RD".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1RD_1LV---_1L_0RB_1RD---_1RD0Rb_1LH0Rd_---1Rb_1LV1Rd_0LV0L__0LX1RL_1LV1L__1LX1Rk_0Rd1RD_---0LH_1Rd---_---0L__0LF0L]_0LH0L__1LF1L]_1LH1L__0Ra1RD_0Rc1LH_1Ra---_1Rc1LV_0LH0LV_0RL0LX_1LH1LV_0Rk1LX_1RD0RB_1LH0RD_---1RB_1LV1RD_0LV1LV_0LX1Ra_1LV1Rd_1LX---_0Ra---_0Rc---_1Ra---_1Rc---_0LH---_0RL---_1LH---_0Rk---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1LV---_1L_---_1Rl---_1Rl0Rb_1LH0Rd_---1Rb_1LV1Rd_0LV0L__0LX1RL_1LV1L__1LX1R[_0Rd1Rl_---0LH_1Rd---_---0L__0LF0L]_0LH0L__1LF1L]_1LH1L__0Ra1Rl_0Rc1LH_1Ra---_1Rc1LV_0LH0LV_0RL0LX_1LH1LV_0R[1LX_1Rl0Rj_1LH0Rl_---1Rj_1LV1Rl_0LV1LV_0LX1Ra_1LV1Rd_1LX---_0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_0L_1Rl_1LV0LH_1L_0Rj_1Rl1LH".
Definition tm1 := TM'_from_str "1RB---_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC---_0RD0RA_1LE1RC".
Definition tm2 := TM'_from_str "1RB1RJ_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC1RJ_0RD0RA_1LE1RC_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;0]%N.
Definition mp := mp_from_str "kaDLV_HBd".
Definition mp' := mp_from_str "[alLV_Hjd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM468.


Module TM469.
Definition tm := TM_from_str "1RB---_1LC1RE_1LA0LD_0RE1LC_1LC1RF_1RB0RD".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LA0LD_0RB1LC_1LC1RA_0RE---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1LV---_1L_---_1Rl---_1Rl0Rb_1LH0Rd_---1Rb_1LV1Rd_0LV0L__0LX1RL_1LV1L__1LX1R[_0Rd1Rl_---0LH_1Rd---_---0L__0LF0L]_0LH0L__1LF1L]_1LH1L__0Ra1Rl_0Rc1LH_1Ra---_1Rc1LV_0LH0LV_0RL0LX_1LH1LV_0R[1LX_1Rl0Rj_1LH0Rl_---1Rj_1LV1Rl_0LV1LV_0LX1Ra_1LV1Rd_1LX---_0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_0L_1Rl_1LV0LH_1L_0Rj_1Rl1LH".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1RD_1LV---_1L_0RB_1RD---_1RD0Rb_1LH0Rd_---1Rb_1LV1Rd_0LV0L__0LX1RL_1LV1L__1LX1Rk_0Rd1RD_---0LH_1Rd---_---0L__0LF0L]_0LH0L__1LF1L]_1LH1L__0RI1RD_0RK1LH_1RI---_1RK1LV_0LH0LV_1LH0LX_1LH1LV_0RD1LX_1RD0RB_1LH0RD_---1RB_1LV1RD_0LV1LV_0LX1Ra_1LV1Rd_1LX---_0Ra---_0Rc---_1Ra---_1Rc---_0LH---_0RL---_1LH---_0Rk---".
Definition tm1 := TM'_from_str "1RB---_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC---_0RD0RA_1LE1RC".
Definition tm2 := TM'_from_str "1RB1RJ_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC1RJ_0RD0RA_1LE1RC_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;0]%N.
Definition mp := mp_from_str "[alLV_Hjd".
Definition mp' := mp_from_str "kaDLV_HBd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM469.


Module TM470.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LA0LD_0RB1LC_1LC1RA_0RE---".
Definition tm' := TM_from_str "1RB0RF_0LB1RC_1LD1RA_1LA0LE_0RC1LD_0RC---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1RD_1LV---_1L_0RB_1RD---_1RD0Rb_1LH0Rd_---1Rb_1LV1Rd_0LV0L__0LX1RL_1LV1L__1LX1Rk_0Rd1RD_---0LH_1Rd---_---0L__0LF0L]_0LH0L__1LF1L]_1LH1L__0RI1RD_0RK1LH_1RI---_1RK1LV_0LH0LV_1LH0LX_1LH1LV_0RD1LX_1RD0RB_1LH0RD_---1RB_1LV1RD_0LV1LV_0LX1Ra_1LV1Rd_1LX---_0Ra---_0Rc---_1Ra---_1Rc---_0LH---_0RL---_1LH---_0Rk---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0Lg1RD_1L^---_1Lg0RB_1RD---_0LM0RR_1LH0RT_0Lg1RR_1L^1RT_0LM0Lg_0LO1RL_1LM1Lg_1LO1Rk_1RD0RB_1LH0RD_---1RB_1L^1RD_0L^1L^_0L`1RQ_1L^1RT_1L`---_0RT1RD_---0LH_1RT---_---0Lg_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RQ1RD_0RS1LH_1RQ---_1RS1L^_0LH0L^_0RL0L`_1LH1L^_0Rk1L`_0RQ---_0RS---_1RQ---_1RS---_0LH---_0RL---_1LH---_0Rk---".
Definition tm1 := TM'_from_str "1RB---_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC---_0RD0RA_1LE1RC".
Definition tm2 := TM'_from_str "1RB1RJ_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC1RJ_0RD0RA_1LE1RC_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;0]%N.
Definition mp := mp_from_str "kaDLV_HBd".
Definition mp' := mp_from_str "kQDL^gHBT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM470.


Module TM471.
Definition tm := TM_from_str "1RB0RF_0LB1RC_1LD1RA_1LA0LE_0RC1LD_0RC---".
Definition tm' := TM_from_str "1RB0RE_0LB1RC_1LD1RA_1LF0LE_0RC1LD_1RB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0Lg1RD_1L^---_1Lg0RB_1RD---_0LM0RR_1LH0RT_0Lg1RR_1L^1RT_0LM0Lg_0LO1RL_1LM1Lg_1LO1Rk_1RD0RB_1LH0RD_---1RB_1L^1RD_0L^1L^_0L`1RQ_1L^1RT_1L`---_0RT1RD_---0LH_1RT---_---0Lg_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RQ1RD_0RS1LH_1RQ---_1RS1L^_0LH0L^_0RL0L`_1LH1L^_0Rk1L`_0RQ---_0RS---_1RQ---_1RS---_0LH---_0RL---_1LH---_0Rk---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0Lg1RD_1L^0Lp_1Lg0RB_1RD1Lp_0LM0RR_1Lp0RT_0Lg1RR_1L^1RT_0LM0Lg_0LO1RL_1LM1Lg_1LO1Rc_1RD0RB_1Lp0RD_---1RB_1L^1RD_0L^1L^_0L`1RQ_1L^1RT_1L`---_0RT1RD_---0Lp_1RT---_---0Lg_0Ln0Le_0Lp0Lg_1Ln1Le_1Lp1Lg_0RQ1RD_0RS1Lp_1RQ---_1RS1L^_0Lp0L^_0RL0L`_1Lp1L^_0Rc1L`_0RJ---_0RL---_1RJ---_1RL---_0Lg---_1L^---_1Lg---_1RD---".
Definition tm1 := TM'_from_str "1RB---_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC---_0RD0RA_1LE1RC".
Definition tm2 := TM'_from_str "1RB1RJ_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC1RJ_0RD0RA_1LE1RC_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;0]%N.
Definition mp := mp_from_str "kQDL^gHBT".
Definition mp' := mp_from_str "cQDL^gpBT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM471.


Module TM472.
Definition tm := TM_from_str "1RB1LB_1RC0RD_0LA1RE_1RF1LC_1LA0RB_---1LB".
Definition tm' := TM_from_str "1RB1LB_1RC0RD_0LA1RF_0RE1LD_---1LC_1LA0RB".
Definition tm0 := TM'_from_str "0RJ0Rd_0RL1Rd_1RJ1Rd_1RL1LN_0LG0LN_1Rj0LP_1Rd1LN_1LN1LP_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LN---_1LG0LG_1LN1Rd_1RK1LG_0RT0Rb_1LG0Rd_1RT1Rb_0LG1Rd_0LE0LP_0LG1RR_1LE1LP_1LG1RY_0Rj1Rd_0Rl0RK_1Rj1LN_1Rl1RK_---0LV_0LG0LX_---1LV_1LG1LX_0R[0RI_1RK0RK_1R[1RI_1LG1RK_0LF1LG_0LH0Rj_1LF0Rd_1LH1Rd_---0Rd_---1Rd_---1Rd_---1LN_---0LN_---0LP_---1LN_---1LP".
Definition tm0' := TM'_from_str "0RJ0Rl_0RL1Rl_1RJ1Rl_1RL1LN_0LG0LN_1Ra0LP_1Rl1LN_1LN1LP_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LN---_1LG0LG_1LN1Rl_1RK1LG_0RT0Rj_1LG0Rl_1RT1Rj_0LG1Rl_0LE0LP_0LG1RR_1LE1LP_1LG1RY_0Ra1Rl_0Rc1LG_1Ra1LN_1Rc1L`_---0L^_0LG0L`_---1L^_1LG1L`_---1Rl_---0RK_---1LN_---1RK_---0LV_---0LX_---1LV_---1LX_0R[0RI_1RK0RK_1R[1RI_1LG1RK_0LF1LG_0LH0Ra_1LF0Rl_1LH1Rl".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_---1RE".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_1RH1RE_1RH1RH".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "KRGNdYj".
Definition mp' := mp_from_str "KRGNlYa".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM472.


Module TM473.
Definition tm := TM_from_str "1RB1LB_1RC0RD_0LA1RF_0RE1LD_---1LC_1LA0RB".
Definition tm' := TM_from_str "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC".
Definition tm0 := TM'_from_str "0RJ0Rl_0RL1Rl_1RJ1Rl_1RL1LN_0LG0LN_1Ra0LP_1Rl1LN_1LN1LP_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LN---_1LG0LG_1LN1Rl_1RK1LG_0RT0Rj_1LG0Rl_1RT1Rj_0LG1Rl_0LE0LP_0LG1RR_1LE1LP_1LG1RY_0Ra1Rl_0Rc1LG_1Ra1LN_1Rc1L`_---0L^_0LG0L`_---1L^_1LG1L`_---1Rl_---0RK_---1LN_---1RK_---0LV_---0LX_---1LV_---1LX_0R[0RI_1RK0RK_1R[1RI_1LG1RK_0LF1LG_0LH0Ra_1LF0Rl_1LH1Rl".
Definition tm0' := TM'_from_str "0RJ0Rd_0RL1Rd_1RJ1Rd_1RL1LN_0LG0LN_1Ri0LP_1Rd1LN_1LN1LP_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LN---_1LG0LG_1LN1Rd_1RK1LG_0RT0Rb_1LG0Rd_1RT1Rb_0LG1Rd_0LE0LP_0LG1RR_1LE1LP_1LG1RY_0Ri1Rd_0Rk0RK_1Ri1LN_1Rk1RK_---0LV_0LG0LX_---1LV_1LG1LX_0R[0RI_1RK0RK_1R[1RI_1LG1RK_0LF1LG_0LH0Ri_1LF0Rd_1LH1Rd_---1Rd_---0RK_---1LN_---1RK_---0LV_---0LX_---1LV_---1LX".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_---1RE".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_1RH1RE_1RH1RH".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "KRGNlYa".
Definition mp' := mp_from_str "KRGNdYi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM473.


Module TM474.
Definition tm := TM_from_str "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC".
Definition tm' := TM_from_str "1RB1LB_1RC0RD_0LA1RE_1RF1LC_1LF0RB_---1LB".
Definition tm0 := TM'_from_str "0RJ0Rd_0RL1Rd_1RJ1Rd_1RL1LN_0LG0LN_1Ri0LP_1Rd1LN_1LN1LP_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LN---_1LG0LG_1LN1Rd_1RK1LG_0RT0Rb_1LG0Rd_1RT1Rb_0LG1Rd_0LE0LP_0LG1RR_1LE1LP_1LG1RY_0Ri1Rd_0Rk0RK_1Ri1LN_1Rk1RK_---0LV_0LG0LX_---1LV_1LG1LX_0R[0RI_1RK0RK_1R[1RI_1LG1RK_0LF1LG_0LH0Ri_1LF0Rd_1LH1Rd_---1Rd_---0RK_---1LN_---1RK_---0LV_---0LX_---1LV_---1LX".
Definition tm0' := TM'_from_str "0RJ0Rd_0RL1Rd_1RJ1Rd_1RL1LN_0LG0LN_1Rj0LP_1Rd1LN_1LN1LP_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LN---_1LG0LG_1LN1Rd_1RK1LG_0RT0Rb_1LG0Rd_1RT1Rb_0LG1Rd_0LE0LP_0LG1RR_1LE1LP_1LG1RY_0Rj1Rd_0Rl0RK_1Rj1LN_1Rl1RK_---0LV_0LG0LX_---1LV_1LG1LX_---0RI_1RK0RK_---1RI_1LG1RK_0Ln1LG_0Lp0Rj_1Ln0Rd_1Lp1Rd_---0Rd_---1Rd_---1Rd_---1LN_---0LN_---0LP_---1LN_---1LP".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_---1RE".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RE_1RE1LD_1LC0LC_1LC1RA_0RG1RE_1RH1RE_1RH1RH".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "KRGNdYi".
Definition mp' := mp_from_str "KRGNdYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM474.


Module TM475.
Definition tm := TM_from_str "1RB1LD_1LC1RA_0LD0LC_0RE1RB_1RD0RF_0RB---".
Definition tm' := TM_from_str "1RB1RA_1LC1RA_0LD0LC_0RE1RB_1RD0RF_0RB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0RD_1RJ1Ri_1RL1RD_0LW0L^_1RL0L`_1LW1L^_1RD1L`_0RL0RB_1L]0RD_1LW1RB_1LU1RD_0LV1LU_0LX1RL_1LV1RD_1LX1RD_0RZ0Rc_1L]0L]_1RZ0LW_1LU0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0Ra0RJ_0Rc0RL_1Ra1RJ_1Rc1RL_0Rc0LW_0RI1RL_0RL1LW_---1RD_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1RZ0RL_1LU---_1Ri0RB_1RD---_0RI---_0RK---_1RI---_1RK---_0L_---_0RL---_1L_---_0RD---".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_1RL1RL_1LW1RD_1RD1RD_0RL0RB_1L]0RD_1LW1RB_1LU1RD_0LV1LU_0LX1RL_1LV1RD_1LX1RD_0RZ0Rc_1L]0L]_1RZ0LW_1LU0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0Ra0RJ_0Rc0RL_1Ra1RJ_1Rc1RL_0Rc0LW_0RI1RL_0RL1LW_---1RD_0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_1RZ0RL_1LU---_1Ri0RB_1RD---_0RI---_0RK---_1RI---_1RK---_0L_---_0RL---_1L_---_0RD---".
Definition tm1 := TM'_from_str "1LB1RJ_0LC0LB_0RE0LD_1LC1LB_1RH1RF_0RG---_0RA0RI_0RE0RA_0RA0RJ_1RA1RJ".
Definition tm2 := TM'_from_str "1LB1RJ_0LC0LB_0RE0LD_1LC1LB_1RH1RF_0RG1RK_0RA0RI_0RE0RA_0RA0RJ_1RA1RJ_1RK1RK".
Definition l0 := [0;1;0;0;1;0;1;1]%N.
Definition mp := mp_from_str "LU]WciIZBD".
Definition mp' := mp_from_str "LU]WciIZBD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM475.


Module TM476.
Definition tm := TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_0LA---".
Definition tm' := TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_0RC---".
Definition tm0 := TM'_from_str "0RJ0RS_0RL0LG_1RJ1RS_1RL0LE_0LG0LE_1LE0LG_1Rb1LE_1RK1LG_0RQ0RZ_0RS0R\_1RQ1RZ_1RS1R\_0LF0LG_0R[1RQ_1LF1LG_0Rk1RZ_1LE0Rb_0RQ0Rd_0LG1Rb_1RQ1Rd_0L]1R\_0L_1RS_1L]1RI_1L_---_0R\0RI_1Rb0RK_1R\1RI_1LE1RK_0LF1LE_0LH1Rb_1LF0Rb_1LH0RK_0RY0Ri_0R[0Rk_1RY1Ri_1R[1Rk_1LE0LG_0RQ---_1RK1Rb_0RZ---_0RS---_0LG---_1RS---_0LE---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ0RS_0RL0LG_1RJ1RS_1RL0LE_0LG0LE_1LE0LG_1Rb1LE_1RK1LG_0RQ0RZ_0RS0R\_1RQ1RZ_1RS1R\_0LF0LG_0R[1RQ_1LF1LG_0Rl1RZ_1LE0Rb_0RQ0Rd_0LG1Rb_1RQ1Rd_0L]1R\_0L_1RS_1L]1RI_1L_---_0R\0RI_1Rb0RK_1R\1RI_1LE1RK_0LF1LE_0LH1Rb_1LF0Rb_1LH0RK_0RY0Rj_0R[0Rl_1RY1Rj_1R[1Rl_1LE0LG_0RQ---_1RK1Rb_0RZ---_0RQ---_0RS---_1RQ---_1RS---_0LF---_0R[---_1LF---_0Rl---".
Definition tm1 := TM'_from_str "1RB0RI_0RC0RJ_1RD1RG_1LE1RI_0LF0LE_1RB1LE_0RH0RA_1LE0RB_1RH1RA_1RK---_0LF1RB".
Definition tm2 := TM'_from_str "1RB0RI_0RC0RJ_1RD1RG_1LE1RI_0LF0LE_1RB1LE_0RH0RA_1LE0RB_1RH1RA_1RK1RL_0LF1RB_1RL1RL".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "Zb[\EGIQKkS".
Definition mp' := mp_from_str "Zb[\EGIQKlS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM476.


Module TM477.
Definition tm := TM_from_str "1RB---_1RC0LD_1RD0RF_1LB1LE_0LB0RE_1RB0RA".
Definition tm' := TM_from_str "1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LC---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1R\---_0Lf---_1Rk---_1Lf---_0RR1RJ_0RT0LO_1RR0L__1RT0R\_1Lf0L]_1RJ0L__1Ra1L]_1RA1L__0RZ0Ri_0R\0Rk_1RZ1Ri_1R\1Rk_0L_0RT_0R\0RJ_1L_0LO_0Ra---_0Rk1Ra_1LN0Ra_1Rk1L]_1Lf1Ra_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0R\0Ra_0LN0Rc_1R\1Ra_0Lf1Rc_0LM1Lf_0LO0R\_1LM1Ra_1LO0Ra_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_1R\0RT_0Lf---_1Rk0LO_1Lf---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_1R\0RT_0Lf---_1RC0LO_1Lf---_0RR1RJ_0RT0LO_1RR0L__1RT0R\_1Lf0L]_1RJ0L__1Ra1L]_1Rj1L__0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_0L_0RT_0R\0RJ_1L_0LO_0Ra---_0RC1Ra_1LN0Ra_1RC1L]_1Lf1Ra_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0R\0Ra_0LN0Rc_1R\1Ra_0Lf1Rc_0LM1Lf_0LO0R\_1LM1Ra_1LO0Ra_1LN---_0RJ---_1Lf---_1RJ---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1RB1RI_1LC1RD_0LE0RB_0RB0RD_1RD1LF_0LG0LC_1RH0LJ_0RA0LE_1RH1RK_1LG1LC_0RH---".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RD_0LE0RB_0RB0RD_1RD1LF_0LG0LC_1RH0LJ_0RA0LE_1RH1RK_1LG1LC_0RH1RL_1RL1RL".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "T\faO]NJk_A".
Definition mp' := mp_from_str "T\faO]NJC_j".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM477.


Module TM478.
Definition tm := TM_from_str "1LB1LF_1RC1RF_---1RD_1RE0LA_1RF1RB_1LD0RD".
Definition tm' := TM_from_str "1LB1LF_1RC1RF_---1RD_1RE0LA_1LE1RB_1LD0RD".
Definition tm0 := TM'_from_str "0R\1Rl_0R[1Rd_1R\1LG_1R[1Rb_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_---0LG_1Rd1Rb_---1LG_0LN1Rb_---0RZ_---0R\_---1RZ_---1R\_---1Rl_---0Ln_---1RL_---1Ln_0Rb1Rd_0Rd0L`_1Rb1Rb_1Rd0LN_1Ln0LE_1RT0LG_1R[1LE_1Rl1LG_0Rj0RJ_0Rl0RL_1Rj1RJ_1Rl1RL_0LG---_1Rb1Ln_1LG1R\_1Rb1R[_0RL0RY_1LN0R[_1RL1RY_1Ln1R[_0L^0Rl_0L`0LN_1L^0RL_1L`1LN".
Definition tm0' := TM'_from_str "0R\1Rl_0R[1Rd_1R\1LG_1R[1Rb_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_---0LG_1Rd1Rb_---1LG_0LN1Rb_---0RZ_---0R\_---1RZ_---1R\_---1Rl_---0Ln_---1RL_---1Ln_0Rb1Rd_0Rd0L`_1Rb1Rb_1Rd0LN_1Ln0LE_1RT0LG_1R[1LE_1Rl1LG_1Lh0RJ_0Rl0RL_1R[1RJ_1Rl1RL_0Lf---_0Lh1Ln_1Lf1R\_1Lh1R[_0RL0RY_1LN0R[_1RL1RY_1Ln1R[_0L^0Rl_0L`0LN_1L^0RL_1L`1LN".
Definition tm1 := TM'_from_str "1RB0LE_1RC1RJ_1LD1RG_0LH0LE_1RB1RF_0RC0RJ_1RF1RF_1RC1LI_1LE1LD_1RK1RC_---1RA".
Definition tm2 := TM'_from_str "1RB0LE_1RC1RJ_1LD1RG_0LH0LE_1RB1RF_0RC0RJ_1RF1RF_1RC1LI_1LE1LD_1RK1RC_1RL1RA_1RL1RL".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "\dlnNb[`GLT".
Definition mp' := mp_from_str "\dlnNb[`GLT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM478.


Module TM479.
Definition tm := TM_from_str "1RB0RB_1LC1RA_0LE1LD_0RE1LF_---1LA_1LD0LC".
Definition tm' := TM_from_str "1RB1LF_1LC1RD_0LE1LA_1RB0RB_---1LD_1LA0LC".
Definition tm0 := TM'_from_str "0RJ0RI_0RL0RK_1RJ1RI_1RL1RK_0L`0Lg_1RL0RL_1L`1Lg_1RK0RK_---0RB_1RK0RD_1LF1RB_1Lp1RD_0LV1Lp_0LX1LF_1LV1RD_1LX1RB_---0RD_1RL1L`_---1RD_0RL1LW_0Le0L^_0Lg0L`_1Le1L^_1Lg1L`_0Ra1RK_0Rc1Le_1Ra1Lp_1Rc1L^_---0Ln_1RL0Lp_---1Ln_1RK1Lp_---0RD_---0RB_---1RD_---1RB_---0LF_---0LH_---1LF_---1LH_0RD---_1L`1RL_1RD0LF_1LW0Lp_0L^0LU_0L`0LW_1L^1LU_1L`1LW".
Definition tm0' := TM'_from_str "0RJ1RK_0RL1Le_1RJ1Lp_1RL1LF_0LH0Ln_1RL0Lp_1LH1Ln_1RK1Lp_---0RZ_1RK0R\_1L^1RZ_1Lp1R\_0LV1Lp_0LX1L^_1LV1R\_1LX1RZ_---0R\_1RL1LH_---1R\_0RL1LW_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_0RJ0RI_0RL0RK_1RJ1RI_1RL1RK_0LH0Lg_1RL0RL_1LH1Lg_1RK0RK_---0R\_---0RZ_---1R\_---1RZ_---0L^_---0L`_---1L^_---1L`_0R\---_1LH1RL_1R\0L^_1LW0Lp_0LF0LU_0LH0LW_1LF1LU_1LH1LW".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RG_1LD1LE_1RH1LC_1LJ1LF_1RB0LC_1RB1RH_1LI1RA_1RB0RB_---0LI".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RG_1LD1LE_1RH1LC_1LJ1LF_1RB0LC_1RB1RH_1LI1RA_1RB0RB_1RK0LI_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "BLp`W^DKFe".
Definition mp' := mp_from_str "ZLpHWF\K^e".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM479.


Module TM480.
Definition tm := TM_from_str "1LB1RC_0RB1LC_1RD0LE_1LA1RE_1LF0RD_---1LD".
Definition tm' := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_1RC0LD".
Definition tm0 := TM'_from_str "0Rd0RR_1R[0RT_1Rd1RR_1Lg1RT_0LN1LX_0LP0LP_1LN1Rd_1LP1LP_0RI0Rd_0RK1Ln_1RI1Rd_1RK1LP_0RI0LV_1Rb0LX_0Rd1LV_1R[1LX_0RZ---_0R\1R[_1RZ0L`_1R\1LX_0LP0Le_1Rb0Lg_1LP1Le_1R[1Lg_1R[0Rb_1R[0Rd_1LX1Rb_1LX1Rd_0LF0L`_0LH1LX_1LF1L`_1LH1Rb_---0RY_1LH0R[_---1RY_1Rb1R[_0Ln0LP_0Lp1LH_1Ln1LP_1Lp0R[_---1LP_---0R[_---1LP_---1R[_---0L^_---0L`_---1L^_---1L`".
Definition tm0' := TM'_from_str "0R\0R\_1RS1RS_1R\1R\_1L_1L__0LN0LN_0LP0LP_1LN1LN_1LP1LP_0RR0R\_0RT1Lf_1RR1R\_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RR---_0RT1RS_1RR0LX_1RT1Lp_0LP0L]_1RZ0L__1LP1L]_1RS1L_".
Definition tm1 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_---0LH_1LB1RA".
Definition tm2 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_1RI0LH_1LB1RA_1RI1RI".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "bHPXg[n`".
Definition mp' := mp_from_str "ZHPp_SfX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM480.


Module TM481.
Definition tm := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_1RC0LD".
Definition tm' := TM_from_str "1LB1LB_0RB1LC_1RD0LE_1LA1RE_1LF0RD_---1LD".
Definition tm0 := TM'_from_str "0R\0R\_1RS1RS_1R\1R\_1L_1L__0LN0LN_0LP0LP_1LN1LN_1LP1LP_0RR0R\_0RT1Lf_1RR1R\_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RR---_0RT1RS_1RR0LX_1RT1Lp_0LP0L]_1RZ0L__1LP1L]_1RS1L_".
Definition tm0' := TM'_from_str "0Rd0Rd_1R[1R[_1Rd1Rd_1Lg1Lg_0LN0LN_0LP0LP_1LN1LN_1LP1LP_0RI0Rd_0RK1Ln_1RI1Rd_1RK1LP_0RI0LV_1Rb0LX_0Rd1LV_1R[1LX_0RZ---_0R\1R[_1RZ0L`_1R\1LX_0LP0Le_1Rb0Lg_1LP1Le_1R[1Lg_1R[0Rb_1R[0Rd_1LX1Rb_1LX1Rd_0LF0L`_0LH1LX_1LF1L`_1LH1Rb_---0RY_1LH0R[_---1RY_1Rb1R[_0Ln0LP_0Lp1LH_1Ln1LP_1Lp0R[_---1LP_---0R[_---1LP_---1R[_---0L^_---0L`_---1L^_---1L`".
Definition tm1 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_---0LH_1LB1RA".
Definition tm2 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_1RI0LH_1LB1RA_1RI1RI".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "ZHPp_SfX".
Definition mp' := mp_from_str "bHPXg[n`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM481.


Module TM482.
Definition tm := TM_from_str "1LB1LB_0RB1LC_1RD0LE_1LA1RE_1LF0RD_---1LD".
Definition tm' := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_0RA0LD".
Definition tm0 := TM'_from_str "0Rd0Rd_1R[1R[_1Rd1Rd_1Lg1Lg_0LN0LN_0LP0LP_1LN1LN_1LP1LP_0RI0Rd_0RK1Ln_1RI1Rd_1RK1LP_0RI0LV_1Rb0LX_0Rd1LV_1R[1LX_0RZ---_0R\1R[_1RZ0L`_1R\1LX_0LP0Le_1Rb0Lg_1LP1Le_1R[1Lg_1R[0Rb_1R[0Rd_1LX1Rb_1LX1Rd_0LF0L`_0LH1LX_1LF1L`_1LH1Rb_---0RY_1LH0R[_---1RY_1Rb1R[_0Ln0LP_0Lp1LH_1Ln1LP_1Lp0R[_---1LP_---0R[_---1LP_---1R[_---0L^_---0L`_---1L^_---1L`".
Definition tm0' := TM'_from_str "0R\0R\_1RS1RS_1R\1R\_1L_1L__0LN0LN_0LP0LP_1LN1LN_1LP1LP_0RR0R\_0RT1Lf_1RR1R\_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RA---_0RC1RS_1RA0LX_1RC1Lp_1RZ0L]_1RZ0L__1RS1L]_1RS1L_".
Definition tm1 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_---0LH_1LB1RA".
Definition tm2 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_1RI0LH_1LB1RA_1RI1RI".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "bHPXg[n`".
Definition mp' := mp_from_str "ZHPp_SfX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM482.


Module TM483.
Definition tm := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_0RA0LD".
Definition tm' := TM_from_str "1LB1RF_1RC1LF_1LA1RD_1LE0RC_---1LC_0RA0LD".
Definition tm0 := TM'_from_str "0R\0R\_1RS1RS_1R\1R\_1L_1L__0LN0LN_0LP0LP_1LN1LN_1LP1LP_0RR0R\_0RT1Lf_1RR1R\_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RA---_0RC1RS_1RA0LX_1RC1Lp_1RZ0L]_1RZ0L__1RS1L]_1RS1L_".
Definition tm0' := TM'_from_str "0R\0Rj_1RS0Rl_1R\1Rj_1L_1Rl_0LN1R\_0LP0LP_1LN1Rj_1LP1LP_0RR0Rj_0RT1Lf_1RR1Rj_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RA---_0RC1RS_1RA0LX_1RC1Lp_1RZ0L]_0RC0L__1RS1L]_1RS1L_".
Definition tm1 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_---0LH_1LB1RA".
Definition tm2 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_1RI0LH_1LB1RA_1RI1RI".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "ZHPp_SfX".
Definition mp' := mp_from_str "ZHPp_SfX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM483.


Module TM484.
Definition tm := TM_from_str "1LB1RF_1RC1LF_1LA1RD_1LE0RC_---1LC_0RA0LD".
Definition tm' := TM_from_str "1LB1RF_1RC1LF_1LA1RD_1LE0RC_---1LC_1RC0LD".
Definition tm0 := TM'_from_str "0R\0Rj_1RS0Rl_1R\1Rj_1L_1Rl_0LN1R\_0LP0LP_1LN1Rj_1LP1LP_0RR0Rj_0RT1Lf_1RR1Rj_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RA---_0RC1RS_1RA0LX_1RC1Lp_1RZ0L]_0RC0L__1RS1L]_1RS1L_".
Definition tm0' := TM'_from_str "0R\0Rj_1RS0Rl_1R\1Rj_1L_1Rl_0LN1Lp_0LP0LP_1LN1R\_1LP1LP_0RR0R\_0RT1Lf_1RR1R\_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RR---_0RT1RS_1RR0LX_1RT1Lp_0LP0L]_1RZ0L__1LP1L]_1RS1L_".
Definition tm1 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_---0LH_1LB1RA".
Definition tm2 := TM'_from_str "1LB0RF_1LC1LC_1RF1LD_1RF1LE_1LG1LC_1LD1RA_1RI0LH_1LB1RA_1RI1RI".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "ZHPp_SfX".
Definition mp' := mp_from_str "ZHPp_SfX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM484.


Module TM485.
Definition tm := TM_from_str "1RB1RC_1LC0RA_1RA0LD_1LC0LE_0RE0RF_0LB---".
Definition tm' := TM_from_str "1RB1RC_1LC0RA_1RA0LD_0RE0LF_0LB---_0RF0RE".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0L_1RL_1RJ0Le_1L_1RT_1RR1Le_0RT0RA_1LV0RC_1RT1RA_1Le1RC_0LV1LV_0LX0RD_1LV0RC_1LX0Ra_0RB1RD_0RD0Ra_1RB0L__1RD0LV_1Le0L]_1RD0L__1RC1L]_0LV1L__0RT0Ra_1LV1RD_1RT1Ra_1Le0L__0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0Ra0Ri_0Rc0Rk_1Ra1Ri_1Rc1Rk_0Ra0LV_1RD---_0Ri1LV_------_1RD---_0RJ---_0L_---_1RJ---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0L_1RL_1RJ0Lm_1L_1RT_1RR1Lm_0RT0RA_1LV0RC_1RT1RA_1Lm1RC_0LV1LV_0LX0RD_1LV0RC_1LX0Ri_0RB1RD_0RD0Ri_1RB0L__1RD0LV_1Lm0L]_1RD0L__1RC1L]_0LV1L__0Ra0Ri_0Rc1RD_1Ra1Ri_1Rc0L__0LV0Lm_---0Lo_1LV1Lm_---1Lo_1RD---_0RJ---_0L_---_1RJ---_0LM---_0LO---_1LM---_1LO---_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0Ri0LV_1RD---_0Ra1LV".
Definition tm1 := TM'_from_str "0RB0RI_1RC1RK_1LD1RF_0RI0LE_1RB0LH_1RG1RA_1LE0RF_1LE1LD_0RI0RJ_1RB---_1RB0LE".
Definition tm2 := TM'_from_str "0RB0RI_1RC1RK_1LD1RF_0RI0LE_1RB0LH_1RG1RA_1LE0RF_1LE1LD_0RI0RJ_1RB1RL_1RB0LE_1RL1RL".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "RDLeVCJ_aiT".
Definition mp' := mp_from_str "RDLmVCJ_iaT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM485.


Module TM486.
Definition tm := TM_from_str "1RB1RC_1LC0RA_1RA0LD_0RE0LF_0LB---_0RF0RE".
Definition tm' := TM_from_str "1RB1RC_1LC0RA_1RA0LD_1LC0LE_0RE0RF_0LD---".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0L_1RL_1RJ0Lm_1L_1RT_1RR1Lm_0RT0RA_1LV0RC_1RT1RA_1Lm1RC_0LV1LV_0LX0RD_1LV0RC_1LX0Ri_0RB1RD_0RD0Ri_1RB0L__1RD0LV_1Lm0L]_1RD0L__1RC1L]_0LV1L__0Ra0Ri_0Rc1RD_1Ra1Ri_1Rc0L__0LV0Lm_---0Lo_1LV1Lm_---1Lo_1RD---_0RJ---_0L_---_1RJ---_0LM---_0LO---_1LM---_1LO---_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0Ri0LV_1RD---_0Ra1LV".
Definition tm0' := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0L_1RL_1RJ0Le_1L_1RT_1RR1Le_0RT0RA_1LV0RC_1RT1RA_1Le1RC_0LV1LV_0LX0RD_1LV0RC_1LX0Ra_0RB1RD_0RD0Ra_1RB0L__1RD0LV_1Le0L]_1RD0L__1RC1L]_0LV1L__0RT0Ra_1LV1RD_1RT1Ra_1Le0L__0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0Ra0Ri_0Rc0Rk_1Ra1Ri_1Rc1Rk_0Ra0LV_1RD---_0Ri1LV_------_1RD---_0Ra---_0L_---_0LV---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "0RB0RI_1RC1RK_1LD1RF_0RI0LE_1RB0LH_1RG1RA_1LE0RF_1LE1LD_0RI0RJ_1RB---_1RB0LE".
Definition tm2 := TM'_from_str "0RB0RI_1RC1RK_1LD1RF_0RI0LE_1RB0LH_1RG1RA_1LE0RF_1LE1LD_0RI0RJ_1RB1RL_1RB0LE_1RL1RL".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "RDLmVCJ_iaT".
Definition mp' := mp_from_str "RDLeVCJ_aiT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM486.


Module TM487.
Definition tm := TM_from_str "1RB1RC_0LA---_1RD0RA_1RE0LA_1LF1LE_0RC0LF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1Rd1Rd_---1RJ_1R\1R\_---1RR_0R\---_0R\---_1R\---_1R\---_0LE---_0LG---_1LE---_1LG---_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Lm0R\_1Rd0R\_1Lh---_1R\0RC_0Rb0R\_0Rd0R\_1Rb1R\_1Rd1R\_0Lo0LE_0Lh0LG_1Lo1LE_1Lh1LG_0RA0RR_0R\1Lp_1RA1Lo_1Lm1Lh_0Ln0Lf_0Lp0Lh_1Ln1Lf_1Lp1Lh_0RQ0RZ_0RS0Rd_1RQ1RZ_1RS0Lm_0Rd0Lm_0RJ0Lo_0R\1Lm_0RR1Lo".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RD_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_1RL1RL_---1Rj_1RD1RD_---1RZ_0RB---_0RD---_1RB---_1RD---_1LU---_1RL---_1LP---_1RD---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RB0LC_1LE1LD_0RG1LF_0RA1LC_0RA0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RB0LC_1LE1LD_0RG1LF_0RA1LC_0RA0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "\dmhpoRCJ".
Definition mp' := mp_from_str "DLUPXWZcj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM487.


Module TM488.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1LA---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RD_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_1RL1RL_---1Rj_1RD1RD_---1RZ_0RB---_0RD---_1RB---_1RD---_1LU---_1RL---_1LP---_1RD---".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RD_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_1RL1RL_---1Rj_1RD1RD_---1RZ_1LX---_0RD---_1LP---_1RD---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RB0LC_1LE1LD_0RG1LF_0RA1LC_0RA0RH_1RI1RG_0RA---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RB0LC_1LE1LD_0RG1LF_0RA1LC_0RA0RH_1RI1RG_0RA1RJ_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "DLUPXWZcj".
Definition mp' := mp_from_str "DLUPXWZcj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM488.


Module TM489.
Definition tm := TM_from_str "1LB1LD_0LC1LE_1RD0LE_1RB---_0LA1RF_0RE0RF".
Definition tm' := TM_from_str "1LB1LD_0LC1LF_1RD0LF_1RE---_0RF0RE_0LA1RE".
Definition tm0 := TM'_from_str "1Rk0Rk_1LG---_1Le1Rk_1Ri---_0LN0L^_0LP0L`_1LN1L^_1LP1L`_0RL1LN_0LE0Rk_1RL1L^_0Lh1Rk_0LU0Lf_0LW0Lh_1LU1Lf_1LW1Lh_0RZ0LN_0R\0Rc_1RZ0L^_1R\1Rc_0Lh0Le_---0Lg_1Rk1Le_---1Lg_0RJ---_0RL---_1RJ---_1RL---_0Le---_1Ra---_1Le---_1Ri---_0LW0Rj_1Ra0Rl_0Lh1Rj_---1Rl_0LE0Lh_0LG1Ra_1LE1Rj_1LG1Ri_0Ra0Ri_0Rc0Rk_1Ra1Ri_1Rc1Rk_0LN0LW_0Rc0Ra_1LN0Rj_0Rk0Ri".
Definition tm0' := TM'_from_str "1Rc0Rc_1LG---_1Lm1Rc_1Ra---_0LN0L^_0LP0L`_1LN1L^_1LP1L`_0Rd1LN_0LE0Rc_1Rd1L^_0Lp1Rc_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ0LN_0R\0Rk_1RZ0L^_1R\1Rk_1Rk0Lm_---0Lo_1Rc1Lm_---1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0Lp---_1Ri---_1Rb---_1Ra---_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0LN0LW_0Rk0Ri_1LN0Rb_0Rc0Ra_0LW0Rb_1Ri0Rd_0Lp1Rb_---1Rd_0LE0Lp_0LG1Ri_1LE1Rb_1LG1Ra".
Definition tm1 := TM'_from_str "0LB0RI_1RH1LC_0LD0LF_0LE0LL_0LB0LF_1LG1RK_1LE1LL_1RA1RK_0RJ0RH_0LF1RI_0RA0RK_1RA---".
Definition tm2 := TM'_from_str "0LB0RI_1RH1LC_0LD0LF_0LE0LL_0LB0LF_1LG1RK_1LE1LL_1RA1RK_0RJ0RH_0LF1RI_0RA0RK_1RA1RM_1RM1RM".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "aWeENhGkjci^".
Definition mp' := mp_from_str "iWmENpGcbka^".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM489.


Module TM490.
Definition tm := TM_from_str "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LC1RE".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L`1RJ_1RJ0LV_1L`0Rb_1Ra1LV_1Ra0RA_1LH0RC_1LV1RA_---1RC_0LV1LH_0LX0Ri_1LV0RC_1LX0LH_0RC1Ra_0LH---_1RC1LV_0L`---_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RC---_0LH---_1RC---_0L`---_0LF---_0LH---_1LF---_1LH---_0Ri0LH_0Rk0RJ_1Ri0L`_1Rk1RJ_0LF0LM_0Rk0LO_1LF1LM_0RJ1LO_1RJ0Rb_---0Rd_0LV1Rb_---1Rd_0L]0LV_0L_1LH_1L]1Rb_1L_0RC".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L`1RJ_1RJ0LV_1L`0Rb_1Ra1LV_1Ra0RA_1LH0RC_1LV1RA_---1RC_0LV1LH_0LX0Ri_1LV0RC_1LX0LH_0RC1Ra_0LH---_1RC1LV_0L`---_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RC---_0LH---_1RC---_0L`---_0LF---_0LH---_1LF---_1LH---_0Ri0LH_0Rk0RJ_1Ri0L`_1Rk1RJ_0LF0LM_0Rk0LO_1LF1LM_0RJ1LO_1RJ0Rb_0LH0Rd_0LV1Rb_---1Rd_0LU0LV_0LW1LH_1LU1Rb_1LW0RC".
Definition tm1 := TM'_from_str "1LB0RI_1RC1LD_0RF0LB_0LB0LE_1LB---_1RA0RG_0RH0RA_0LD1RG_1RA1RC".
Definition tm2 := TM'_from_str "1LB0RI_1RC1LD_0RF0LB_0LB0LE_1LB1RJ_1RA0RG_0RH0RA_0LD1RG_1RA1RC_1RJ1RJ".
Definition l0 := [1;0;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "JHaV`ibkC".
Definition mp' := mp_from_str "JHaV`ibkC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM490.


Module TM491.
Definition tm := TM_from_str "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LC1RE".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1LA0LD_0RB---_0RF0LB_0LC1RE".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L`1RJ_1RJ0LV_1L`0Rb_1Ra1LV_1Ra0RA_1LH0RC_1LV1RA_---1RC_0LV1LH_0LX0Ri_1LV0RC_1LX0LH_0RC1Ra_0LH---_1RC1LV_0L`---_0LF0L^_0LH0L`_1LF1L^_1LH1L`_0RC---_0LH---_1RC---_0L`---_0LF---_0LH---_1LF---_1LH---_0Ri0LH_0Rk0RJ_1Ri0L`_1Rk1RJ_0LF0LM_0Rk0LO_1LF1LM_0RJ1LO_1RJ0Rb_0LH0Rd_0LV1Rb_---1Rd_0LU0LV_0LW1LH_1LU1Rb_1LW0RC".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L_1RJ_1RJ0LV_1L_0Rb_1Ra1LV_1Ra0RA_1LH0RC_1LV1RA_---1RC_0LV1LH_0LX0Ri_1LV0RC_1LX0LH_0RC1Ra_0LH---_1RC1LV_0L_---_0LF0L]_0LH0L__1LF1L]_1LH1L__0RI---_0RK---_1RI---_1RK---_0LH---_0RJ---_1LH---_0Ra---_0Ri0LH_0Rk0RJ_1Ri0L__1Rk1RJ_0LF0LM_0Rk0LO_1LF1LM_0RJ1LO_1RJ0Rb_0LH0Rd_0LV1Rb_---1Rd_0LU0LV_0LW1LH_1LU1Rb_1LW0RC".
Definition tm1 := TM'_from_str "1LB0RI_1RC1LD_0RF0LB_0LB0LE_1LB---_1RA0RG_0RH0RA_0LD1RG_1RA1RC".
Definition tm2 := TM'_from_str "1LB0RI_1RC1LD_0RF0LB_0LB0LE_1LB1RJ_1RA0RG_0RH0RA_0LD1RG_1RA1RC_1RJ1RJ".
Definition l0 := [1;0;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "JHaV`ibkC".
Definition mp' := mp_from_str "JHaV_ibkC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM491.


Module TM492.
Definition tm := TM_from_str "1RB0RE_1LC0RA_1LA0LD_0RB---_0RF0LB_0LC1RE".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_0RC1LD_1LA---_0RF0LB_0LD1RE".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L_1RJ_1RJ0LV_1L_0Rb_1Ra1LV_1Ra0RA_1LH0RC_1LV1RA_---1RC_0LV1LH_0LX0Ri_1LV0RC_1LX0LH_0RC1Ra_0LH---_1RC1LV_0L_---_0LF0L]_0LH0L__1LF1L]_1LH1L__0RI---_0RK---_1RI---_1RK---_0LH---_0RJ---_1LH---_0Ra---_0Ri0LH_0Rk0RJ_1Ri0L__1Rk1RJ_0LF0LM_0Rk0LO_1LF1LM_0RJ1LO_1RJ0Rb_0LH0Rd_0LV1Rb_---1Rd_0LU0LV_0LW1LH_1LU1Rb_1LW0RC".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0L`1RJ_1RJ0LV_1L`0Rb_1Ra1LV_1Ra0RA_1LH0RC_1LV1RA_---1RC_0LV1LH_0LX0Ri_1LV0RC_1LX0LH_0RQ1Ra_0RS---_1RQ1LV_1RS---_0RQ0L^_0LH0L`_1Ra1L^_1LH1L`_0RC---_0LH---_1RC---_0L`---_0LF---_0LH---_1LF---_1LH---_0Ri0LH_0Rk0RJ_1Ri0L`_1Rk1RJ_0LF0LM_0Rk0LO_1LF1LM_0RJ1LO_1RJ0Rb_---0Rd_0LV1Rb_---1Rd_0L]0LV_0L_1LH_1L]1Rb_1L_0RC".
Definition tm1 := TM'_from_str "1LB0RI_1RC1LD_0RF0LB_0LB0LE_1LB---_1RA0RG_0RH0RA_0LD1RG_1RA1RC".
Definition tm2 := TM'_from_str "1LB0RI_1RC1LD_0RF0LB_0LB0LE_1LB1RJ_1RA0RG_0RH0RA_0LD1RG_1RA1RC_1RJ1RJ".
Definition l0 := [1;0;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "JHaV_ibkC".
Definition mp' := mp_from_str "JHaV`ibkC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM492.


Module TM493.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_1LD---".
Definition tm' := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_0LF1RC_1RA---".
Definition tm0 := TM'_from_str "0RS0L`_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Ln0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1LH0RR_---0RT_1LO1RR_---1RT_0Ln1LO_0Lp1RB_1Ln1RD_1Lp1RQ_1LP---_1RD---_1Lg---_1L^---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RS0L`_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Lm0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1LH0RR_---0RT_1LO1RR_---1RT_0Lm1LO_0Lo1RB_1Lm1RD_1Lo1RQ_0RB---_0RD---_1RB---_1RD---_0L`---_1LO---_1L`---_1RD---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LH_1RF1LI_0RG0RF_1LD0RA_1LJ1RA_1LD1LB_0LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LH_1RF1LI_0RG0RF_1LD0RA_1LJ1RA_1LD1LB_0LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "DO^HPQBg`n".
Definition mp' := mp_from_str "DO^HPQBg`m".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM493.


Module TM494.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_0LF1RC_1RA---".
Definition tm' := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_0LF1RF_1RA---".
Definition tm0 := TM'_from_str "0RS0L`_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Lm0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1LH0RR_---0RT_1LO1RR_---1RT_0Lm1LO_0Lo1RB_1Lm1RD_1Lo1RQ_0RB---_0RD---_1RB---_1RD---_0L`---_1LO---_1L`---_1RD---".
Definition tm0' := TM'_from_str "0RS0L`_1LH0RD_1RS---_1LO1RD_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg_0RR1LP_0RT1RD_1RR1Lg_1RT1L^_1LO0L^_1RB0L`_1RD1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1LO0RB_1L`0RD_1RD0RQ_1RQ0RD_1Lm0LH_1L`1RD_1RD0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO_1LH0Rj_---0Rl_1LO1Rj_---1Rl_0Lm1LO_0Lo---_1Lm1RD_1Lo---_0RB---_0RD---_1RB---_1RD---_0L`---_1LO---_1L`---_1RD---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LH_1RF1LI_0RG0RF_1LD0RA_1LJ1RA_1LD1LB_0LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LH_1RF1LI_0RG0RF_1LD0RA_1LJ1RA_1LD1LB_0LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "DO^HPQBg`m".
Definition mp' := mp_from_str "DO^HPQBg`m".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM494.


Module TM495.
Definition tm := TM_from_str "1LB0LD_1RC1LF_0RD0RC_0LE0LB_1RA---_1LA0LB".
Definition tm' := TM_from_str "1LB0LD_1RC1LF_0RD0RC_1LE0LB_1LF---_1LA0LB".
Definition tm0 := TM'_from_str "0RS0Lp_1LH1LO_1RS---_1LO0Ln_0LN0L]_0LP0L__1LN1L]_1LP1L__0RR1LP_0RT1R[_1RR1L__1RT1Ln_1LO0Ln_1RY0Lp_1R[1Ln_1RQ1Lp_0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0Lp1LH_1LO0RY_1Lp0R[_1R[0RQ_1LH0R[_---0LH_1LO1R[_---0LO_0Le0LM_0Lg0LO_1Le1LM_1Lg1LO_0RB---_0RD---_1RB---_1RD---_0Lp---_0LM---_1Lp---_1LM---_1RQ0R[_1Le0LH_1Lp1R[_1LM0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO".
Definition tm0' := TM'_from_str "0RS0Lp_1LH1LO_1RS---_1LO0Ln_0LN0L]_0LP0L__1LN1L]_1LP1L__0RR1LP_0RT1R[_1RR1L__1RT1Ln_1LO0Ln_1RY0Lp_1R[1Ln_1RQ1Lp_0RY0RQ_0R[0RS_1RY1RQ_1R[1RS_0Lp1LH_1LO0RY_1Lp0R[_1R[0RQ_1LH0R[_---0LH_1LO1R[_---0LO_0Lf0LM_0Lh0LO_1Lf1LM_1Lh1LO_1LP---_1R[---_1L_---_1Ln---_0Ln---_0Lp---_1Ln---_1Lp---_1RQ0R[_1Lf0LH_1Lp1R[_1LM0LO_0LF0LM_0LH0LO_1LF1LM_1LH1LO".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LH_1RF1LJ_0RG0RF_1LD0RA_1LK1LI_1LB0LC_1LD1LB_0LJ---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LE1LH_1RF1LJ_0RG0RF_1LD0RA_1LK1LI_1LB0LC_1LD1LB_0LJ1RL_1RL1RL".
Definition l0 := [1;1;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "[OnHPQY_Mpe".
Definition mp' := mp_from_str "[OnHPQY_Mpf".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM495.


Module TM496.
Definition tm := TM_from_str "1LB1RD_0LC0LF_1RC0RA_0RE1RD_1RA---_0LB0LC".
Definition tm' := TM_from_str "1LB1RD_0LC0LF_1RC0RA_0RE1RD_1RA---_0LB0RF".
Definition tm0 := TM'_from_str "1RC0RZ_1LM0R\_1LW1RZ_1LU1R\_0LN1RB_0LP1Rc_1LN---_1LP1R\_0RT0LU_1RC1RT_1RT0Lm_1LW0LW_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1RT0LW_1LW0Rc_1RC1LW_1RZ0R\_0Ra0RZ_0Rc0R\_1Ra1RZ_1Rc1R\_1LM1RB_---1Rc_0R\---_---1R\_0RB---_0RD---_1RB---_1RD---_0Lo---_1Rc---_1Lo---_1R\---_1RT0RT_0LM1RC_0LW1RT_0LU1LW_0LM0LU_0LO0LW_1LM1LU_1LO1LW".
Definition tm0' := TM'_from_str "1RC0RZ_1LM0R\_1LW1RZ_1LU1R\_0LN1RB_0LP1Rc_1LN---_1LP1R\_0RT0LU_1RC1RT_1RT0Lm_1LW0LW_0LU0Lm_0LW0Lo_1LU1Lm_1LW1Lo_0RR0RA_0RT0RC_1RR1RA_1RT1RC_1RT0LW_1LW0Rc_1RC1LW_1RZ0R\_0Ra0RZ_0Rc0R\_1Ra1RZ_1Rc1R\_1LM1RB_---1Rc_0R\---_---1R\_0RB---_0RD---_1RB---_1RD---_0Lo---_1Rc---_1Lo---_1R\---_1RT0Ri_0LM0Rk_0LW1Ri_0LU1Rk_0LM0LU_0LO1RT_1LM1LU_1LO0Ri".
Definition tm1 := TM'_from_str "1RB1RA_1RC---_1LD0RA_0LF0LE_0LD0LF_1RJ0LG_1RH1LG_1LG1RI_0RB0RA_1RJ1RH".
Definition tm2 := TM'_from_str "1RB1RA_1RC1RK_1LD0RA_0LF0LE_0LD0LF_1RJ0LG_1RH1LG_1LG1RI_0RB0RA_1RJ1RH_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "\cBMmUWCZT".
Definition mp' := mp_from_str "\cBMmUWCZT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM496.


Module TM497.
Definition tm := TM_from_str "1RB1LA_1RC1LD_1LA0RE_1RF0LA_0LA0RD_---0RD".
Definition tm' := TM_from_str "1RB1LA_1RC1LD_1LA0RE_1RE0LA_0LF0RD_1RB---".
Definition tm0 := TM'_from_str "0RJ1Rc_0RL1LG_1RJ1LF_1RL1LH_1LH0LF_0LG0LH_1Rc1LF_1LG1LH_0RR0R[_0RT1Rc_1RR1R[_1RT1LF_0LH0L^_1RT0L`_1LH1L^_1RY1L`_1Rc0Ra_1LG0Rc_1LF1Ra_1LH1Rc_0LF1LH_0LH0Rj_1LF1Rc_1LH0RT_0Rj0RT_0Rl0LG_1Rj1RT_1Rl0LH_---0LE_1Rj0LG_---1LE_1RT1LG_0RT0RY_0LG0R[_1RT1RY_0LH1R[_0LE---_0LG1LH_1LE0R[_1LG1Rc_---0RY_---0R[_---1RY_---1R[_------_---1LH_---0R[_---1Rc".
Definition tm0' := TM'_from_str "0RJ1Rc_0RL1LG_1RJ1LF_1RL1LH_1LH0LF_0LG0LH_1Rc1LF_1LG1LH_0RR0R[_0RT1Rc_1RR1R[_1RT1LF_0LH0L^_1RT0L`_1LH1L^_1RY1L`_1Rc0Ra_1LG0Rc_1LF1Ra_1LH1Rc_0LF1LH_0LH0Rb_1LF1Rc_1LH0RT_0Rb0RT_0Rd0LG_1Rb1RT_1Rd0LH_---0LE_1Rb0LG_---1LE_1RT1LG_0RT0RY_---0R[_1RT1RY_---1R[_0Lm---_0Lo1LH_1Lm0R[_1Lo1Rc_0RJ---_0RL---_1RJ---_1RL---_1LH---_0LG---_1Rc---_1LG---".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LB_1RE1LD_0LC0LB_1RA1RF_0RG0RA_---0RH_1RG1RA".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LB_1RE1LD_0LC0LB_1RA1RF_0RG0RA_1RI0RH_1RG1RA_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "THGFcYj[".
Definition mp' := mp_from_str "THGFcYb[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM497.


Module TM498.
Definition tm := TM_from_str "1LB1RC_1LC0RE_1LD1LF_1RE0RB_1LF1RB_0LA---".
Definition tm' := TM_from_str "1LB1RC_1LC0RE_1LD1LF_1RE0RB_0LD1RB_0LA---".
Definition tm0 := TM'_from_str "1L`0RR_0RJ0RT_1Lp1RR_1RJ1RT_0LN1LN_0LP---_1LN0RJ_1LP---_1Rc0Ra_1LG0Rc_0RJ1Ra_---1Rc_0LV0LG_0LX1LG_1LV1LG_1LX0Rc_0RL1LN_0Ra---_1RL0RJ_1Ra---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_---0L`_---1LN_---1L`_1Rc0RJ_1LN0RJ_---0RL_0RJ1RJ_---1RL_0Ln0Lp_0Lp0RJ_1Ln1Lp_1Lp1RJ_0LX---_0Ra---_1LG---_1Ra---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "1L`0RR_0RJ0RT_1Lp1RR_1RJ1RT_0LN1Rc_0LP---_1LN0RJ_1LP---_1Rc0Ra_1LG0Rc_0RJ1Ra_---1Rc_0LV0L`_0LX1LG_1LV1L`_1LX0Rc_0RL1LN_0Ra---_1RL0RJ_1Ra---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_0L`0L`_---1Rc_1L`1L`_1Rc0RJ_1Rc0RJ_1Rc0RL_0RJ1RJ_0RJ1RL_0L]0Lp_0L_0RJ_1L]1Lp_1L_1RJ_0LX---_0Ra---_1LG---_1Ra---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "0RB1RB_1LC0RA_1LD0RB_0LE1LC_1LG1LF_1LC---_1RA0RB".
Definition tm2 := TM'_from_str "0RB1RB_1LC0RA_1LD0RB_0LE1LC_1LG1LF_1LC1RH_1RA0RB_1RH1RH".
Definition l0 := [0;0;0;1;0;0;1;0]%N.
Definition mp := mp_from_str "cJGNXp`".
Definition mp' := mp_from_str "cJGNXp`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM498.


Module TM499.
Definition tm := TM_from_str "1LB1RD_0LC---_0RD0LF_1RE1RD_0RA0RB_1LC0LC".
Definition tm' := TM_from_str "1LB1LC_0LC---_0RD0LF_1RE1RD_0RA0RB_1LC0LC".
Definition tm0 := TM'_from_str "0RK0RZ_---0R\_1Lm1RZ_---1R\_0LN1RC_0LP1Rd_1LN1RK_1LP1R\_0Rb---_0LV---_1Rb---_0LU---_0LU---_0LW---_1LU---_1LW---_0RY0Rd_0R[0RC_1RY0Lo_1R[0Lm_0RC0Lm_0Rd0Lo_0RK1Lm_0R\1Lo_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_1Lm1RC_1Rb1Rd_1RZ1RK_---1R\_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LW0RC_0Rd---_1LW0RK_0R\---_0RZ0Rb_1LV0LV_1RZ1Rb_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW".
Definition tm0' := TM'_from_str "0RK0RZ_---1LV_1Lm1RZ_---1LU_0LN0LV_0LP0LX_1LN1LV_1LP1LX_0Rb---_0LV---_1Rb---_0LU---_0LU---_0LW---_1LU---_1LW---_0RY0Rd_0R[0RC_1RY0Lo_1R[0Lm_0RC0Lm_0Rd0Lo_0RK1Lm_0R\1Lo_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_1Lm1RC_1Rb1Rd_1RZ1RK_---1R\_0RA0RI_0RC0RK_1RA1RI_1RC1RK_0LW0RC_0Rd---_1LW0RK_0R\---_0RZ0Rb_1LV0LV_1RZ1Rb_1LU0LU_0LV0LU_0LX0LW_1LV1LU_1LX1LW".
Definition tm1 := TM'_from_str "1RB1RA_1RC1RI_1LD1RH_0LF0LE_0RC0LD_0RB0LG_1LF1LE_0RB0RA_1RJ---_0RC0RI".
Definition tm2 := TM'_from_str "1RB1RA_1RC1RI_1LD1RH_0LF0LE_0RC0LD_0RB0LG_1LF1LE_0RB0RA_1RJ1RK_0RC0RI_1RK1RK".
Definition l0 := [0;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "\dCmUVoZKb".
Definition mp' := mp_from_str "\dCmUVoZKb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM499.


Module TM500.
Definition tm := TM_from_str "1RB---_1LC0LE_1RD0LB_1RB1RA_0LF0RC_0RA1LE".
Definition tm' := TM_from_str "1RB---_1LC0LE_1RD0LB_0LD1RA_0LF0RC_0RA1LE".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LO---_0RL---_1LO---_0RD---_0RD1LV_1LV0RZ_1RD0Lf_1Le1RZ_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ1RL_0R\0Lm_1RZ0LO_1R\0RL_1Le0LM_1RL0LO_1RZ1LM_---1LO_0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LO1Le_0RL---_1LO1RZ_0RD---_0RJ0RQ_0Lo0RS_1RJ1RQ_0LV1RS_0Lm0RL_0Lo0LV_1Lm0RD_1Lo1LV_0RA0RZ_0RC1RL_1RA1Lf_1RC0LO_1LV0Lf_---0Lh_0RZ1Lf_---1Lh".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LO---_0RL---_1LO---_0RD---_0RD1LV_1LV0RZ_1RD0Lf_1Le1RZ_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ1RL_0R\0Lm_1RZ0LO_1R\0RL_1Le0LM_1RL0LO_1RZ1LM_---1LO_0L]0RB_0RL0RD_1Le1RB_1RL1RD_0L]1Le_0L_---_1L]1RZ_1L_---_0RJ0RQ_0Lo0RS_1RJ1RQ_0LV1RS_0Lm0RL_0Lo0LV_1Lm0RD_1Lo1LV_0RA0RZ_0RC1RL_1RA1Lf_1RC0LO_1LV0Lf_---0Lh_0RZ1Lf_---1Lh".
Definition tm1 := TM'_from_str "1LB1RC_0LD0RA_0RA0RI_1LG0LE_0LF0LG_0RC1LE_1RA0LH_1LG1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RC_0LD0RA_0RA0RI_1LG0LE_0LF0LG_0RC1LE_1RA0LH_1LG1LB_1RA1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LeZmfoVOD".
Definition mp' := mp_from_str "LeZmfoVOD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM500.


Module TM501.
Definition tm := TM_from_str "1RB---_1LC0LE_1RD0LB_0LD1RA_0LF0RC_0RA1LE".
Definition tm' := TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LO---_0RL---_1LO---_0RD---_0RD1LV_1LV0RZ_1RD0Lf_1Le1RZ_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ1RL_0R\0Lm_1RZ0LO_1R\0RL_1Le0LM_1RL0LO_1RZ1LM_---1LO_0L]0RB_0RL0RD_1Le1RB_1RL1RD_0L]1Le_0L_---_1L]1RZ_1L_---_0RJ0RQ_0Lo0RS_1RJ1RQ_0LV1RS_0Lm0RL_0Lo0LV_1Lm0RD_1Lo1LV_0RA0RZ_0RC1RL_1RA1Lf_1RC0LO_1LV0Lf_---0Lh_0RZ1Lf_---1Lh".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LO1Le_0RL---_1LO1RB_0R\---_0R\1LV_1LV0RB_1R\0Lf_1Le1RB_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RB1RL_0RD0Lm_1RB0LO_1RD0RL_1Le0LM_1RL0LO_1RB1LM_---1LO_0RJ---_0RL---_1RJ---_1RL---_0LO---_0RL---_1LO---_0R\---_0RJ0RQ_0Lo0RS_1RJ1RQ_0LV1RS_0Lm0RL_0Lo0LV_1Lm0R\_1Lo1LV_0RA0RB_0RC1RL_1RA1Lf_1RC0LO_1LV0Lf_0RL0Lh_0RB1Lf_---1Lh".
Definition tm1 := TM'_from_str "1LB1RC_0LD0RA_0RA0RI_1LG0LE_0LF0LG_0RC1LE_1RA0LH_1LG1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RC_0LD0RA_0RA0RI_1LG0LE_0LF0LG_0RC1LE_1RA0LH_1LG1LB_1RA1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LeZmfoVOD".
Definition mp' := mp_from_str "LeBmfoVO\".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM501.


Module TM502.
Definition tm := TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE".
Definition tm' := TM_from_str "1RB0RD_1LC0LE_1RA0LB_0LC---_0LF0RC_0RA1LE".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LO1Le_0RL---_1LO1RB_0R\---_0R\1LV_1LV0RB_1R\0Lf_1Le1RB_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RB1RL_0RD0Lm_1RB0LO_1RD0RL_1Le0LM_1RL0LO_1RB1LM_---1LO_0RJ---_0RL---_1RJ---_1RL---_0LO---_0RL---_1LO---_0R\---_0RJ0RQ_0Lo0RS_1RJ1RQ_0LV1RS_0Lm0RL_0Lo0LV_1Lm0R\_1Lo1LV_0RA0RB_0RC1RL_1RA1Lf_1RC0LO_1LV0Lf_0RL0Lh_0RB1Lf_---1Lh".
Definition tm0' := TM'_from_str "0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_0LO1Le_0RL---_1LO1RB_0R[---_0R[1LV_1LV0RB_1R[0Lf_1Le1RB_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RB1RL_0RD0Lm_1RB0LO_1RD0RL_1Le0LM_1RL0LO_1RB1LM_---1LO_0RL---_0LV---_1RL---_0Le---_0LU---_0LW---_1LU---_1LW---_0RJ0RQ_0Lo0RS_1RJ1RQ_0LV1RS_0Lm0RL_0Lo0LV_1Lm0R[_1Lo1LV_0RA0RB_0RC1RL_1RA1Lf_1RC0LO_1LV0Lf_0RL0Lh_0RB1Lf_---1Lh".
Definition tm1 := TM'_from_str "1LB1RC_0LD0RA_0RA0RI_1LG0LE_0LF0LG_0RC1LE_1RA0LH_1LG1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RC_0LD0RA_0RA0RI_1LG0LE_0LF0LG_0RC1LE_1RA0LH_1LG1LB_1RA1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LeBmfoVO\".
Definition mp' := mp_from_str "LeBmfoVO[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM502.


Module TM503.
Definition tm := TM_from_str "1RB0RC_1LC0RE_1RE0LD_1LA1LB_0LF1RA_1LB---".
Definition tm' := TM_from_str "1RB0RC_1LC0RE_1RE0LD_1LA0RE_0LF1RA_1LB---".
Definition tm0 := TM'_from_str "0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_0L_---_0RL0LF_1L_0RD_1RB1LF_0RD0Ra_1LF0Rc_1RD1Ra_1LN1Rc_0LV0LN_0LX0RL_1LV1LN_1LX0RS_0Rb0RL_0Rd0LX_1Rb0LF_1Rd0RL_---0L]_1RL0L__---1L]_1RS1L__0Rc1RS_0RL0RB_1Rc1L__0LF1RB_0LF0LN_0LH0LP_1LF1LN_1LH1LP_0LX0RB_---0RD_0RL1RB_---1RD_0Lm1LN_0Lo1Rb_1Lm1Rc_1Lo0LF_1RS---_0RB---_1L_---_1RB---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_0L_---_0RL0LF_1L_0RD_1RB1LF_0RD0Ra_1LF0Rc_1RD1Ra_1LN1Rc_0LV0LN_0LX0RL_1LV1LN_1LX0RS_0Rb0RL_0Rd0LX_1Rb0LF_1Rd0RL_---0L]_1RL0L__---1L]_1RS1L__0Rc0Ra_0RL0Rc_1Rc1Ra_0LF1Rc_0LF0LN_0LH0RL_1LF1LN_1LH0RS_0LX0RB_---0RD_0RL1RB_---1RD_0Lm1LN_0Lo1Rb_1Lm1Rc_1Lo0LF_1RS---_0RB---_1L_---_1RB---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "0RB1RJ_1LC1RA_0LD0RB_1RG1LE_1LF1LC_0RB0LF_1RH0LF_---0RI_1RB1RG_0RB0RG".
Definition tm2 := TM'_from_str "0RB1RJ_1LC1RA_0LD0RB_1RG1LE_1LF1LC_0RB0LF_1RH0LF_1RK0RI_1RB1RG_0RB0RG_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "cLNX_FSbDB".
Definition mp' := mp_from_str "cLNX_FSbDB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM503.


Module TM504.
Definition tm := TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0LA_1LD---".
Definition tm' := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0LA_0RB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rk_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB1L]_0RD0RK_1RB1LU_1RD1RK_1LU0LE_1RK0LG_1Rd1LE_---1LG_0RK---_0Rb---_1RK---_1Rb---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB1L]_0RD0RK_1RB1LU_1RD1RK_1LU0LE_1RK0LG_1Rd1LE_---1LG_0RI---_0RK---_1RI---_1RK---_0L_---_0RD---_1L_---_0RK---".
Definition tm1 := TM'_from_str "1RB---_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB".
Definition tm2 := TM'_from_str "1RB1RJ_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "kK_bDLU]d".
Definition mp' := mp_from_str "lK_bDLU]d".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM504.


Module TM505.
Definition tm := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0LA_0RB---".
Definition tm' := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB1L]_0RD0RK_1RB1LU_1RD1RK_1LU0LE_1RK0LG_1Rd1LE_---1LG_0RI---_0RK---_1RI---_1RK---_0L_---_0RD---_1L_---_0RK---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RK0RD_1Rd1L__---0RK_0RI---_0RK---_1RI---_1RK---_0L_---_0RD---_1L_---_0RK---".
Definition tm1 := TM'_from_str "1RB---_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB".
Definition tm2 := TM'_from_str "1RB1RJ_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "lK_bDLU]d".
Definition mp' := mp_from_str "lK_bDLU]d".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM505.


Module TM506.
Definition tm := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LD---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RK0RD_1Rd1L__---0RK_0RI---_0RK---_1RI---_1RK---_0L_---_0RD---_1L_---_0RK---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rk_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RK0RD_1Rd1L__---0RK_0RK---_0Rb---_1RK---_1Rb---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1RB---_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB".
Definition tm2 := TM'_from_str "1RB1RJ_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "lK_bDLU]d".
Definition mp' := mp_from_str "kK_bDLU]d".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM506.


Module TM507.
Definition tm := TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LD---".
Definition tm' := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rk_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RK0RD_1Rd1L__---0RK_0RK---_0Rb---_1RK---_1Rb---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1L__1RD---_1LW1Rb_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RK0RD_1Rd1L__---0RK_1L_---_0RK---_1LW---_1RK---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1RB---_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB".
Definition tm2 := TM'_from_str "1RB1RJ_1LC1RD_1RB1LC_0RE0RB_1RF1RA_1LG1RI_0LH0LG_---0LC_1RE1RB_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "kK_bDLU]d".
Definition mp' := mp_from_str "lK_bDLU]d".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM507.


Module TM508.
Definition tm := TM_from_str "1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LE---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1Rl---_1LW---_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1RD_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0Rl_1RK1L__1Rb0RK_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_1LU0L__1RL0Rl_1Rd1L__---0RK_0Lm0RB_0RL0RD_1LU1RB_1RL1RD_0Lm1LU_0Lo---_1Lm1Rd_1Lo---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1LU_1RD---_1LW1Rd_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rk_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RL0RD_1Rd1L__---0RK_0RL---_1RK---_1RL---_1L_---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1RB---_1LC1RI_0LD0LC_---0LE_1RF1LE_1LE1RG_0RH0RF_1RB1RA_1RH1RF".
Definition tm2 := TM'_from_str "1RB1RJ_1LC1RI_0LD0LC_---0LE_1RF1LE_1LE1RG_0RH0RF_1RB1RA_1RH1RF_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "DLU]_Kbld".
Definition mp' := mp_from_str "kLU]_KbDd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM508.


Module TM509.
Definition tm := TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LE---".
Definition tm' := TM_from_str "1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RB1RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1LU_1RD---_1LW1Rd_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rk_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RL0RD_1Rd1L__---0RK_0RL---_1RK---_1RL---_1L_---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0LW---_1Rl---_1LW---_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1RD_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0Rl_1RK1L__1Rb0RK_0Rj0RI_0Rl0RK_1Rj1RI_1Rl1RK_1LU0L__1RL0Rl_1Rd1L__---0RK_0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_1Rl---_1LW1Rd_1RK---".
Definition tm1 := TM'_from_str "1RB---_1LC1RI_0LD0LC_---0LE_1RF1LE_1LE1RG_0RH0RF_1RB1RA_1RH1RF".
Definition tm2 := TM'_from_str "1RB1RJ_1LC1RI_0LD0LC_---0LE_1RF1LE_1LE1RG_0RH0RF_1RB1RA_1RH1RF_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "kLU]_KbDd".
Definition mp' := mp_from_str "DLU]_Kbld".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM509.


Module TM510.
Definition tm := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LB---".
Definition tm' := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1RL_1RD---_1LW1Rl_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RD0RD_1Rd1L__---0RK_0L_---_0RD---_0LW---_1RD---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1RL_1RD---_1LW1Rl_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RD0RD_1Rd1L__---0RK_0RB---_0RD---_1RB---_1RD---_1LU---_1RD---_1Rd---".
Definition tm1 := TM'_from_str "1RB---_1RC1RA_1LD1RI_0LE0LD_---0LF_1RG1LF_1LF1RH_0RB0RG_1RB1RG".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RA_1LD1RI_0LE0LD_---0LF_1RG1LF_1LF1RH_0RB0RG_1RB1RG_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "lDLU]_Kbd".
Definition mp' := mp_from_str "lDLU]_Kbd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM510.


Module TM511.
Definition tm := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---".
Definition tm' := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_0LA0RB_1RA---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1RL_1RD---_1LW1Rl_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1RD0RD_1Rd1L__---0RK_0RB---_0RD---_1RB---_1RD---_1LU---_1RD---_1Rd---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1RL_1RD---_1LW1Rl_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_1L]0RI_0RD0RK_1LU1RI_1RD1RK_0LE0L__0LG0RD_1LE1L__1LG0RK_0RB---_0RD---_1RB---_1RD---_1LU---_1RD---_1Rd---".
Definition tm1 := TM'_from_str "1RB---_1RC1RA_1LD1RI_0LE0LD_---0LF_1RG1LF_1LF1RH_0RB0RG_1RB1RG".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RA_1LD1RI_0LE0LD_---0LF_1RG1LF_1LF1RH_0RB0RG_1RB1RG_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "lDLU]_Kbd".
Definition mp' := mp_from_str "lDLU]_Kbd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM511.


Module TM512.
Definition tm := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LA---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0LW1RD_1RD---_1LW1RK_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rl_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1Rd0RD_1Rd1L__---0RK_0Rb---_0Rd---_1Rb---_1Rd---_1RL---_1L_---_1Rl---_1Rb---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LW1RD_1RD---_1LW1RK_1RK---_1RK0Rb_1L]0Rd_1L_1Rb_1LU1Rd_0LV1RL_0LX1L__1LV1Rk_1LX1Rb_0R\1R\_1RK0L]_1R\0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0RZ0RI_0R\0RK_1RZ1RI_1R\1RK_1R\0L__1L_0RD_1RK1L__1Rb0RK_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0L__1Rd0RD_1Rd1L__---0RK_0Rd---_------_1Rd---_------_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1RB---_1RC1RH_1RD1RA_1LE1RB_0LF0LE_---0LG_1RH1LG_1LG1RI_0RC0RH".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RH_1RD1RA_1LE1RB_0LF0LE_---0LG_1RH1LG_1LG1RI_0RC0RH_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "ldDLU]_Kb".
Definition mp' := mp_from_str "kdDLU]_Kb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM512.


Module TM513.
Definition tm := TM_from_str "1LB0LB_1RB0RC_1LD1RC_1LE0LA_1LF0LB_---1RB".
Definition tm' := TM_from_str "1LB0LB_1RB0RC_1LD1RC_1LE0LA_0LF0LB_---0RA".
Definition tm0 := TM'_from_str "0RS0RL_0RR1Lp_1RS1RL_1RR1LO_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_1RL0Lh_1LO1LN_1RS1Lh_1RR0RT_1Lp0RR_1LN0RT_1LO1RR_1LM1RT_0L^0LG_0L`1LM_1L^1LG_1L`1RT_---1LO_1RS1RL_1RR1LN_1Lh0Lh_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG_---0RL_0RS1Lp_---1RL_1RS1LO_0Ln0LM_0Lp0LO_1Ln1LM_1Lp1LO_---0RJ_---0RL_---1RJ_---1RL_---1RL_---1LO_---1RS_---1RR".
Definition tm0' := TM'_from_str "0RS0RL_0RR1Lo_1RS1RL_1RR1LO_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RJ0RQ_0RL0RS_1RJ1RQ_1RL1RS_1RL0Lh_1LO1LN_1RS1Lh_1RR0RT_1Lo0RR_1LN0RT_1LO1RR_1LM1RT_0L^0LG_0L`1LM_1L^1LG_1L`1RT_---1LO_1RS1RL_1RR1LN_1Lh0Lh_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG_---0RL_0RS1Lo_---1RL_1RS1LO_0Lm0LM_0Lo0LO_1Lm1LM_1Lo1LO_---0RA_---0RC_---1RA_---1RC_---1LO_---1RL_---1RR_---1RS".
Definition tm1 := TM'_from_str "1LB1RA_1RH0LC_1LE1LD_1RG1LC_---1RF_1LI0RA_1LD1RF_1RH1RG_1LD1LI".
Definition tm2 := TM'_from_str "1LB1RA_1RH0LC_1LE1LD_1RG1LC_1RJ1RF_1LI0RA_1LD1RF_1RH1RG_1LD1LI_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "TMhOpRSLN".
Definition mp' := mp_from_str "TMhOoRSLN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM513.


Module TM514.
Definition tm := TM_from_str "1LB---_1RC0RA_1RD0LD_0LE0RB_1LC1LF_0LD1LF".
Definition tm' := TM_from_str "1RB---_1RC0LC_0LD0RF_1RE1LD_0LE1LB_1RB0RA".
Definition tm0 := TM'_from_str "0RR---_------_1RR---_------_0LN---_0LP---_1LN---_1LP---_0RR0RA_0RT0RC_1RR1RA_1RT1RC_0Lp0R\_0R\---_1RK0RR_0RR---_0RZ0LV_0R\0RR_1RZ0Ln_1R\1RR_0Ln0L]_1RR0L__1Ln1L]_1RA1L__1RR0RI_0L_0RK_0L_1RI_0Lp1RK_0Le0R\_0Lg0RR_1Le0RR_1Lg---_0RK1Le_1Le1L__1RK0RR_0RR1Lp_0LV0Ln_0LX0Lp_1LV1Ln_1LX1Lp_0LV1Le_0RR1L__0Ln0RR_1RR1Lp_0L]0Ln_0L_0Lp_1L]1Ln_1L_1Lp".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L`---_0RT---_1Rk---_0RJ---_0RR0LN_0RT0RJ_1RR0L^_1RT1RJ_0L^0LU_1RJ0LW_1L^1LU_1RA1LW_1RJ0Ri_0LW0Rk_0LW1Ri_0L`1Rk_0L]0RT_0L_0RJ_1L]0RJ_1L_---_0Rb1L]_0Rd1LW_1Rb0RJ_1Rd1L`_0LN0L^_0LW0L`_1LN1L^_1LW1L`_0Le0Rk_1RJ1L]_0LN1Rk_0LW0RJ_0Le0LN_0Lg0LP_1Le1LN_1Lg1LP_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`0RT_0RT---_1Rk0RJ_0RJ---".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF---_0LC0LB".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF1RJ_0LC0LB_1RJ1RJ".
Definition l0 := [1;0;1;1;0;0;0;0]%N.
Definition mp := mp_from_str "\p_eVRKAn".
Definition mp' := mp_from_str "T`W]NJkA^".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM514.


Module TM515.
Definition tm := TM_from_str "1RB---_1RC0LC_0LD0RF_1RE1LD_0LE1LB_1RB0RA".
Definition tm' := TM_from_str "1RB---_1RC0LC_0LD0RF_1LB1LE_0LC1LE_1RB0RA".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L`---_0RT---_1Rk---_0RJ---_0RR0LN_0RT0RJ_1RR0L^_1RT1RJ_0L^0LU_1RJ0LW_1L^1LU_1RA1LW_1RJ0Ri_0LW0Rk_0LW1Ri_0L`1Rk_0L]0RT_0L_0RJ_1L]0RJ_1L_---_0Rb1L]_0Rd1LW_1Rb0RJ_1Rd1L`_0LN0L^_0LW0L`_1LN1L^_1LW1L`_0Le0Rk_1RJ1L]_0LN1Rk_0LW0RJ_0Le0LN_0Lg0LP_1Le1LN_1Lg1LP_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`0RT_0RT---_1Rk0RJ_0RJ---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0Lh---_0RT---_1Rk---_0RJ---_0RR0LN_0RT0RJ_1RR0Lf_1RT1RJ_0Lf0LU_1RJ0LW_1Lf1LU_1RA1LW_1RJ0Ri_0LW0Rk_0LW1Ri_0Lh1Rk_0L]0RT_0L_0RJ_1L]0RJ_1L_---_0Rk1L]_1L]1LW_1Rk0RJ_0RJ1Lh_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0LN1L]_0RJ1LW_0Lf0RJ_1RJ1Lh_0LU0Lf_0LW0Lh_1LU1Lf_1LW1Lh_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0Lh0RT_0RT---_1Rk0RJ_0RJ---".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF---_0LC0LB".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF1RJ_0LC0LB_1RJ1RJ".
Definition l0 := [1;0;1;1;0;0;0;0]%N.
Definition mp := mp_from_str "T`W]NJkA^".
Definition mp' := mp_from_str "ThW]NJkAf".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM515.


Module TM516.
Definition tm := TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RA".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LD_0RE1LA_---0RA".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0Lf_1RJ0LH_1RL0L]_1R\0L]_1RR0L__1Rl1L]_1RI1L__0RR0RI_0RT0RK_1RR1RI_1RT1RK_1L_0R\_---0RR_0L]0Rl_1RC0RI_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_0LH---_0L]1RJ_1LH---_1L]0LH_0RK1RR_1RI0Lf_1RK0LH_1L_0L]_0Lf0L]_0Lh0L__1Lf1L]_1Lh1L__0RJ0RK_0RL1Lf_1RJ1RK_1RL1L]_1R\0LF_1RR0LH_1Rl1LF_1RI1LH_---0RA_---0RC_---1RA_---1RC_---0RT_---0Lf_---0RK_---1Lf".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0Lf_1RJ0LH_1RL0L]_1R\0L]_1RR0L__1Rl1L]_1RI1L__0RR0RI_0RT0RK_1RR1RI_1RT1RK_1L_0R\_---0RR_0L]0Rl_1RC0RI_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_0LH---_0L]1RJ_1LH---_1L]0LH_0RK1RR_1RI0Lf_1RK0LH_1L_0L]_0Lf0L]_0Lh0L__1Lf1L]_1Lh1L__0Ra0RK_0Rc1Lf_1Ra1RK_1Rc1L]_0Ra0LF_1RR0LH_0RK1LF_1RI1LH_---0RA_---0RC_---1RA_---1RC_---0RT_---0Lf_---0RK_---1Lf".
Definition tm1 := TM'_from_str "1LB0LI_1LC1LI_1RD0LJ_0RA0RE_---1RF_1RG0LJ_0RH0RL_1RA1RE_0LC0LI_1RK1LB_0RD0RK_1RD1RK".
Definition tm2 := TM'_from_str "1LB0LI_1LC1LI_1RD0LJ_0RA0RE_1RM1RF_1RG0LJ_0RH0RL_1RA1RE_0LC0LI_1RK1LB_0RD0RK_1RD1RK_1RM1RM".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "\_fRlCJT]HIK".
Definition mp' := mp_from_str "\_fRlCJT]HIK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM516.


Module TM517.
Definition tm := TM_from_str "1LB1RE_1RB1RC_1LD0RE_---0LB_1LF1RA_0LA0LD".
Definition tm' := TM_from_str "1LB1RE_1RB1RC_1LD0RE_---0LB_1LF1RA_1LF0LD".
Definition tm0 := TM'_from_str "0RT0Rb_0Rc0Rd_1RT1Rb_1Rc1Rd_0LN0L__0LP1Rc_1LN1L__1LP1Rd_0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1RL0LO_1LO1L__1RT1LO_1Rc1RB_---0Ra_1RT0Rc_---1Ra_1LO1Rc_0L^0LG_0L`0Rc_1L^1LG_1L`0Rd_---0RL_---1RT_---1RL_---1LO_---0LM_---0LO_---1LM_---1LO_1LN0RB_---0RD_1L_1RB_1LM1RD_0Ln1L__0Lp1LM_1Ln1RB_1Lp1RD_1LO---_---1RL_1L_---_1LM0LO_0LE0L]_0LG0L__1LE1L]_1LG1L_".
Definition tm0' := TM'_from_str "0RT0Rb_0Rc0Rd_1RT1Rb_1Rc1Rd_0LN0L__0LP1Rc_1LN1L__1LP1Rd_0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1RL0LO_1LO1L__1RT1LO_1Rc1RB_---0Ra_1RT0Rc_---1Ra_1LO1Rc_0L^0Lp_0L`0Rc_1L^1Lp_1L`0Rd_---0RL_---1RT_---1RL_---1LO_---0LM_---0LO_---1LM_---1LO_1Lp0RB_---0RD_1L_1RB_1LM1RD_0Ln1L__0Lp1LM_1Ln1RB_1Lp1RD_1Lp---_---1RL_1L_---_1LM0LO_0Ln0L]_0Lp0L__1Ln1L]_1Lp1L_".
Definition tm1 := TM'_from_str "1LB1RI_1RG0LC_1RD1LC_1LC1RE_1LH1RF_0RE0RA_1RG1RD_---1LB_1RE1RA".
Definition tm2 := TM'_from_str "1LB1RI_1RG0LC_1RD1LC_1LC1RE_1LH1RF_0RE0RA_1RG1RD_1RJ1LB_1RE1RA_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "dMOTcBL_D".
Definition mp' := mp_from_str "dMOTcBL_D".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM517.


Module TM518.
Definition tm := TM_from_str "1LB0RD_1RC0LE_1RA0LD_1RC1RD_---0LF_0LB1LA".
Definition tm' := TM_from_str "1LB0RF_1RC0LD_1RA1RC_---0LE_0LB1LA_1RC1RF".
Definition tm0 := TM'_from_str "0RT0RY_---0R[_1RT1RY_1Lm1R[_0LN0RD_0LP0RT_1LN0RT_1LP0R\_0RR---_0RT0LM_1RR---_1RT0LF_1Lm0Le_1RD0Lg_1R[1Le_1RT1Lg_0RB0RD_0RD0RT_1RB1RD_1RD1RT_0Lg0L]_1RR0L__1Lg1L]_1RZ1L__0RR0RZ_0RT0R\_1RR1RZ_1RT1R\_1Lm1RD_1RD1RT_1R[1RT_1RT1R\_---1Lm_---0LP_---0Le_---0RT_---0Lm_---0Lo_---1Lm_---1Lo_0RD1RT_---0RZ_1RD1Lg_0Lm1RZ_0LM0LF_0LO0LH_1LM1LF_1LO1LH".
Definition tm0' := TM'_from_str "0RT0Ri_---0Rk_1RT1Ri_1Le1Rk_0LN0RD_0LP0RT_1LN0RT_1LP0Rl_0RR---_0RT0LM_1RR---_1RT0LF_1Le0L]_1RD0L__1Rk1L]_1RT1L__0RB0RR_0RD0RT_1RB1RR_1RD1RT_0L_1Le_1RR1RD_1L_1Rk_1Rj1RT_---1Le_---0LP_---0L]_---0RT_---0Le_---0Lg_---1Le_---1Lg_0RD1RT_---0Rj_1RD1L__0Le1Rj_0LM0LF_0LO0LH_1LM1LF_1LO1LH_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_1Le1RD_1RD1RT_1Rk1RT_1RT1Rl".
Definition tm1 := TM'_from_str "1RB1RJ_0RC0RH_1LD1RA_0LE0LG_1LD0LF_---0LD_0LI0RH_1RC1RH_1RH1LK_0RH0RL_---1LD_1RH1RL".
Definition tm2 := TM'_from_str "1RB1RJ_0RC0RH_1LD1RA_0LE0LG_1LD0LF_1RM0LD_0LI0RH_1RC1RH_1RH1LK_0RH0RL_1RM1LD_1RH1RL_1RM1RM".
Definition l0 := [0;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "[RDmMeFTPZg\".
Definition mp' := mp_from_str "kRDeM]FTPj_l".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM518.


Module TM519.
Definition tm := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB1LE_---1LE".
Definition tm' := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB1LE_---0LC".
Definition tm0 := TM'_from_str "0RZ---_1LP0LO_1RZ---_1Lo0Lh_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ0RT_0RS---_1RQ1LH_1RS1Lf_0RR0LF_1LO0LH_0RR1LF_0RT1LH_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0LO0Lh_0R[1R[_1LO1Lh_0R\1R\_0RR0RR_1LO0RT_1LF1RR_1Lh1RT_0Lf1LF_0Lh1Lh_1Lf1RR_1Lh1RT_0RY0RR_0LP1LO_1RY1LF_0Lo1Lh_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_---0RR_---1LO_---1LF_---1Lh_---0Lf_---0Lh_---1Lf_---1Lh".
Definition tm0' := TM'_from_str "0RZ---_1LP0LO_1RZ---_1Lo0Lh_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ0RT_0RS---_1RQ1LH_1RS1LU_0RR0LF_1LO0LH_0RR1LF_0RT1LH_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0LO0Lh_0R[1R[_1LO1Lh_0R\1R\_0RR0RR_1LO0RT_1LF1RR_1Lh1RT_0Lf1LF_0Lh1Lh_1Lf1RR_1Lh1RT_0RY0RR_0LP1LO_1RY1LF_0Lo1Lh_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_---0RR_---1LO_---1LF_---1Lh_---0LU_---0LW_---1LU_---1LW".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LE_0RK1LD_1LC1LE_---1LF_0LH0LG_1LH1LG_0RI1LB_0RA0RJ_1LG1RK_1RA1RJ".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LE_0RK1LD_1LC1LE_1RL1LF_0LH0LG_1LH1LG_0RI1LB_0RA0RJ_1LG1RK_1RA1RJ_1RL1RL".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "[FPHofhOR\T".
Definition mp' := mp_from_str "[FPHoUhOR\T".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM519.


Module TM520.
Definition tm := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB1LE_---0LC".
Definition tm' := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB0LC_---1LE".
Definition tm0 := TM'_from_str "0RZ---_1LP0LO_1RZ---_1Lo0Lh_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ0RT_0RS---_1RQ1LH_1RS1LU_0RR0LF_1LO0LH_0RR1LF_0RT1LH_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0LO0Lh_0R[1R[_1LO1Lh_0R\1R\_0RR0RR_1LO0RT_1LF1RR_1Lh1RT_0Lf1LF_0Lh1Lh_1Lf1RR_1Lh1RT_0RY0RR_0LP1LO_1RY1LF_0Lo1Lh_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_---0RR_---1LO_---1LF_---1Lh_---0LU_---0LW_---1LU_---1LW".
Definition tm0' := TM'_from_str "0RZ---_1LP0LO_1RZ---_1Lo0LW_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ0RT_0RS---_1RQ1LH_1RS1Lf_0RR0LF_1LO0LH_0RR1LF_0RT1LH_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0LO0LW_0R[1R[_1LO1LW_0R\1R\_0RR0RR_1LO0RT_1LF1RR_1LW1RT_0Lf1LF_0Lh1LW_1Lf1RR_1Lh1RT_0RY0RR_0LP1LO_1RY1LF_0Lo1LW_0LM0LU_0LO0LW_1LM1LU_1LO1LW_---0RR_---1LO_---1LF_---1LW_---0Lf_---0Lh_---1Lf_---1Lh".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LE_0RK1LD_1LC1LE_---1LF_0LH0LG_1LH1LG_0RI1LB_0RA0RJ_1LG1RK_1RA1RJ".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LE_0RK1LD_1LC1LE_1RL1LF_0LH0LG_1LH1LG_0RI1LB_0RA0RJ_1LG1RK_1RA1RJ_1RL1RL".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "[FPHoUhOR\T".
Definition mp' := mp_from_str "[FPHofWOR\T".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM520.


Module TM521.
Definition tm := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB0LC_---1LE".
Definition tm' := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB0LC_---0LC".
Definition tm0 := TM'_from_str "0RZ---_1LP0LO_1RZ---_1Lo0LW_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ0RT_0RS---_1RQ1LH_1RS1Lf_0RR0LF_1LO0LH_0RR1LF_0RT1LH_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0LO0LW_0R[1R[_1LO1LW_0R\1R\_0RR0RR_1LO0RT_1LF1RR_1LW1RT_0Lf1LF_0Lh1LW_1Lf1RR_1Lh1RT_0RY0RR_0LP1LO_1RY1LF_0Lo1LW_0LM0LU_0LO0LW_1LM1LU_1LO1LW_---0RR_---1LO_---1LF_---1LW_---0Lf_---0Lh_---1Lf_---1Lh".
Definition tm0' := TM'_from_str "0RZ---_1LP0LO_1RZ---_1Lo0LW_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RQ0RT_0RS---_1RQ1LH_1RS1LU_0RR0LF_1LO0LH_0RR1LF_0RT1LH_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0LO0LW_0R[1R[_1LO1LW_0R\1R\_0RR0RR_1LO0RT_1LF1RR_1LW1RT_0Lf1LF_0Lh1LW_1Lf1RR_1Lh1RT_0RY0RR_0LP1LO_1RY1LF_0Lo1LW_0LM0LU_0LO0LW_1LM1LU_1LO1LW_---0RR_---1LO_---1LF_---1LW_---0LU_---0LW_---1LU_---1LW".
Definition tm1 := TM'_from_str "1LB1RI_0LC0LE_0RK1LD_1LC1LE_---1LF_0LH0LG_1LH1LG_0RI1LB_0RA0RJ_1LG1RK_1RA1RJ".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LE_0RK1LD_1LC1LE_1RL1LF_0LH0LG_1LH1LG_0RI1LB_0RA0RJ_1LG1RK_1RA1RJ_1RL1RL".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "[FPHofWOR\T".
Definition mp' := mp_from_str "[FPHoUWOR\T".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM521.


Module TM522.
Definition tm := TM_from_str "1RB0LE_0RC1RB_1LC1RD_0RF0LA_0RD1LE_1LA---".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL1Le_1RJ1Ri_1RL0Lh_1Le0Le_1RS0Lg_1RZ1Le_1RL1Lg_0RQ0RJ_0RS0RL_1RQ1RJ_1RS1RL_0LX1Le_0Rk1RS_1LX1RZ_0RL1RL_1LX0RZ_0RL0R\_1Le1RZ_0Lf1R\_0LV1RL_0LX0Le_1LV---_1LX1Le_0Ri0RS_0Rk0RL_1Ri1RS_1Rk0Lf_1RS0LE_---0LG_1RL1LE_---1LG_0RY0RS_0R[1RZ_1RY1RS_1R[1Lh_0RL0Lf_1Le0Lh_---1Lf_1RZ1Lh_0RL---_------_1RL---_1Lf---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL1Le_1RJ1Rj_1RL0Lh_1Le0Le_1RS0Lg_1RZ1Le_1RL1Lg_0RQ0RJ_0RS0RL_1RQ1RJ_1RS1RL_0LX1Le_0Rl1RS_1LX1RZ_0RL1RL_1LX0RZ_0RL0R\_1Le1RZ_0Lf1R\_0LV1RL_0LX0Le_1LV---_1LX1Le_0Rj0RS_0Rl0RL_1Rj1RS_1Rl0Lf_1RS0LE_---0LG_1RL1LE_---1LG_0RY0RS_0R[1RZ_1RY1RS_1R[1Lh_0RL0Lf_1Le0Lh_---1Lf_1RZ1Lh_0RZ---_0RL---_1RZ---_1RL---_0LN---_0LP---_1LN---_1LP---".
Definition tm1 := TM'_from_str "1LB1RE_0RF0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF---".
Definition tm2 := TM'_from_str "1LB1RE_0RF0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "SefhZLk".
Definition mp' := mp_from_str "SefhZLl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM522.


Module TM523.
Definition tm := TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB---".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL1Le_1RJ1Rj_1RL0Lh_1Le0Le_1RS0Lg_1RZ1Le_1RL1Lg_0RQ0RJ_0RS0RL_1RQ1RJ_1RS1RL_0LX1Le_0Rl1RS_1LX1RZ_0RL1RL_1LX0RZ_0RL0R\_1Le1RZ_0Lf1R\_0LV1RL_0LX0Le_1LV---_1LX1Le_0Rj0RS_0Rl0RL_1Rj1RS_1Rl0Lf_1RS0LE_---0LG_1RL1LE_---1LG_0RY0RS_0R[1RZ_1RY1RS_1R[1Lh_0RL0Lf_1Le0Lh_---1Lf_1RZ1Lh_0RZ---_0RL---_1RZ---_1RL---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL1Le_1RJ1Rj_1RL0Lh_1Le0Le_1RS0Lg_1RZ1Le_1RL1Lg_0RQ0RJ_0RS0RL_1RQ1RJ_1RS1RL_0LX1Le_0Rl1RS_1LX1RZ_0RL1RL_1LX0RZ_0RL0R\_1Le1RZ_0Lf1R\_0LV1RL_0LX0Le_1LV---_1LX1Le_0Rj0RS_0Rl0RL_1Rj1RS_1Rl0Lf_1RS0LE_---0LG_1RL1LE_---1LG_0RY0RS_0R[1RZ_1RY1RS_1R[1Lh_0RL0Lf_1Le0Lh_---1Lf_1RZ1Lh_0RJ---_0RL---_1RJ---_1RL---_1Le---_1RS---_1RZ---_1RL---".
Definition tm1 := TM'_from_str "1LB1RE_0RF0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF---".
Definition tm2 := TM'_from_str "1LB1RE_0RF0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "SefhZLl".
Definition mp' := mp_from_str "SefhZLl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM523.


Module TM524.
Definition tm := TM_from_str "1LB0LA_1RC0RE_1RD1LC_1LA1RE_1RF0RD_1RC---".
Definition tm' := TM_from_str "1LB0LA_1LC0RE_1RD1LC_1LA1RE_1RF0RD_1RC---".
Definition tm0 := TM'_from_str "1R[0LX_0RY0LN_1LX1LX_1RY0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_1LE0RT_0LX1LX_1Rd---_1LX0Rb_0RZ0Rd_0R\1R[_1RZ1Rd_1R\1LX_0LG0LV_1Rl0LX_1LG1LV_1R[1LX_1LX0Rb_1LN0Rd_0Rb1Rb_1LE1Rd_0LF1RT_0LH0Rb_1LF---_1LH1Rb_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1R\0LP_---0Rl_1LX1LP_---0R[_0RR---_0RT---_1RR---_1RT---_1LE---_0LX---_1Rd---_1LX---".
Definition tm0' := TM'_from_str "1R[0LX_0RY0LN_1LX1LX_1RY0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0Rd0Ra_1R[0Rc_1Rd1Ra_1LX1Rc_0LV0RT_0LX1LX_1LV---_1LX0Rb_0RZ0Rd_0R\1R[_1RZ1Rd_1R\1LX_0LG0LV_1Rl0LX_1LG1LV_1R[1LX_1LX0Rb_1LN0Rd_0Rb1Rb_1LE1Rd_0LF1RT_0LH0Rb_1LF---_1LH1Rb_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1R\0LP_---0Rl_1LX1LP_---0R[_0RR---_0RT---_1RR---_1RT---_1LE---_0LX---_1Rd---_1LX---".
Definition tm1 := TM'_from_str "0RB0RH_1RC---_1RD1LG_1LE1RI_0LF0LE_0LG1LG_1RH1LG_0RA1RA_1RB1RH".
Definition tm2 := TM'_from_str "0RB0RH_1RC1RJ_1RD1LG_1LE1RI_0LF0LE_0LG1LG_1RH1LG_0RA1RA_1RB1RH_1RJ1RJ".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "blT\ENX[d".
Definition mp' := mp_from_str "blT\ENX[d".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM524.


Module TM525.
Definition tm := TM_from_str "1LB1RD_1RC---_1LE0LA_1RC0RD_1RD1LF_1LC0LE".
Definition tm' := TM_from_str "1LB1RB_1RC---_1LD0LA_1RF1LE_1LC0LD_1RC0RF".
Definition tm0 := TM'_from_str "0RT0RZ_---0R\_1RT1RZ_---1R\_0LN1Lg_0LP1RR_1LN1RT_1LP1RY_0RR---_0RT---_1RR---_1RT---_0Lp---_1Lg---_1Lp---_1RT---_0R[1Lg_1LX0RT_1R[---_1Lg1RT_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0Lp1LX_1Lg0RR_1Lp0RT_1RT0RY_0RZ1Lh_0R\1RT_1RZ1LG_1R\1Ln_1Lg0Ln_1RR0Lp_1RT1Ln_1RY1Lp_1RY0RT_1LN0LX_1Lp1RT_1RT0Lg_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg".
Definition tm0' := TM'_from_str "0RT0RJ_---0RL_1RT1RJ_---1RL_0LN1L__0LP---_1LN1RT_1LP---_0RR---_0RT---_1RR---_1RT---_0Lh---_1L_---_1Lh---_1RT---_0Rk1L__1LX0RT_1Rk---_1L_1RT_0L^0LE_0L`0LG_1L^1LE_1L`1LG_0Rj1L`_0Rl1RT_1Rj1LG_1Rl1Lf_1L_0Lf_1RR0Lh_1RT1Lf_1Ri1Lh_1Ri0RT_1LN0LX_1Lh1RT_1RT0L__0LV0L]_0LX0L__1LV1L]_1LX1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0Lh1LX_1L_0RR_1Lh0RT_1RT0Ri".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TgnXGhYRpN".
Definition mp' := mp_from_str "T_fXG`iRhN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM525.


Module TM526.
Definition tm := TM_from_str "1RB0RA_1LC1RF_0LD0LC_0RE0RB_1LA---_1RA1RD".
Definition tm' := TM_from_str "1RB0RA_1LC1RF_0LD0LC_1RE0RB_1RF---_1RA1RD".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LW1L]_1RD0RJ_1LW0Rl_1R\0RA_1R\0Rj_1L]0Rl_1L_1Rj_1LU1Rl_0LV1RL_0LX1Rc_1LV1RC_1LX1RK_0Rl1RD_1R\0L]_1Rl0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0Ra0RI_0Rc0RK_1Ra1RI_1Rc1RK_1RD0L__---0RD_1R\1L__---0R\_0Rl---_0RA---_1Rl---_1RA---_0LF---_0LH---_1LF---_1LH---_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_1LU1Rl_1RJ1L__1Rl---_1RA1Rj".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0LW1L]_1RD0RJ_1LW0Rl_1R\0RA_1R\0Rj_1L]0Rl_1L_1Rj_1LU1Rl_0LV1RL_0LX1Rd_1LV1RC_1LX1RK_0Rl1RD_1R\0L]_1Rl0L__1L_0LU_0L]0LU_0L_0LW_1L]1LU_1L_1LW_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_1RD0L__---0RD_1R\1L__---0R\_0Rj---_0Rl---_1Rj---_1Rl---_1RL---_1Rd---_1RC---_1RK---_0RB0RZ_0RD0R\_1RB1RZ_1RD1R\_1LU1Rl_1RJ1L__1Rl---_1RA1Rj".
Definition tm1 := TM'_from_str "1LB1RD_1RC1LB_1RJ1RA_0RE0RC_1RF1RK_1LG1RI_0LH0LG_1RE0LB_1RE1RC_1RI---_1RM1RL_0RM0RL_1LH0RI".
Definition tm2 := TM'_from_str "1LB1RD_1RC1LB_1RJ1RA_0RE0RC_1RF1RK_1LG1RI_0LH0LG_1RE0LB_1RE1RC_1RI1RN_1RM1RL_0RM0RL_1LH0RI_1RN1RN".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "K_\jDLU]lcCAJ".
Definition mp' := mp_from_str "K_\jDLU]ldCAJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM526.


Module TM527.
Definition tm := TM_from_str "1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA".
Definition tm' := TM_from_str "1RB0LB_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L^1Lf_1Rk0RL_1L^0Rk_1RZ0Rk_---0Rb_0Lh0Rd_---1Rb_0LO1Rd_0LU1RZ_0LW0LM_1LU1RB_1LW1LM_---0Rk_---1LU_---1L__---1RB_---0L^_---0L`_---1L^_---1L`_0RB---_1Lf0Rk_1RB0L^_1LM1Rk_0Lf0LM_0Lh0LO_1Lf1LM_1Lh1LO_0Ri0RL_0Rk0LU_1Ri0L__1Rk1RZ_1Lf0L]_0RL0L__0Rk1L]_0Rk1L__0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_0L_0LO_1RZ1RZ_1L_1Rd_1RB1RB".
Definition tm0' := TM'_from_str "0RJ---_0RL0Rk_1RJ0L^_1RL1Rk_0L^0LM_1Rk0LO_1L^1LM_1RZ1LO_---0Rb_0Lh0Rd_---1Rb_0LO1Rd_0LU1RZ_0LW0LM_1LU1RB_1LW1LM_---0Rk_---1LU_---1L__---1RB_---0L^_---0L`_---1L^_---1L`_0RB---_1Lf0Rk_1RB0L^_1LM1Rk_0Lf0LM_0Lh0LO_1Lf1LM_1Lh1LO_0Ri0RL_0Rk0LU_1Ri0L__1Rk1RZ_1Lf0L]_0RL0L__0Rk1L]_0Rk1L__0RZ0RB_0R\0RD_1RZ1RB_1R\1RD_0L_0LO_1RZ1RZ_1L_1Rd_1RB1RB".
Definition tm1 := TM'_from_str "1LB0RE_0RF0LC_1LB1LD_0LJ1RA_1RA1RH_0LI1RG_1RE1RA_0RF0RE_1LJ1RH_---0LK_0LL0LI_0RE1LC".
Definition tm2 := TM'_from_str "1LB0RE_0RF0LC_1LB1LD_0LJ1RA_1RA1RH_0LI1RG_1RE1RA_0RF0RE_1LJ1RH_1RM0LK_0LL0LI_0RE1LC_1RM1RM".
Definition l0 := [0;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "Zf_MkLdBOU^h".
Definition mp' := mp_from_str "Zf_MkLdBOU^h".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM527.


Module TM528.
Definition tm := TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LF".
Definition tm' := TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1RC".
Definition tm0 := TM'_from_str "0RJ1RI_0RL1LH_1RJ1Lp_1RL1Lp_0LH0Ln_1RQ0Lp_1RK1Ln_1RI1Lp_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0LV0L__1RQ0RQ_1LV0RK_1RI0RI_0L_0RK_0LE1LH_0LH1RK_---1Lp_0L]0LF_0L_0LH_1L]1LF_1L_1LH_1LV0LH_1RI---_1Le0Ln_1Lp---_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RS---_0LH---_1RS---_0Lp---_0LE---_0LG---_1LE---_1LG---_0RK1RI_1LH1LH_1RK1Lp_1Lp1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm0' := TM'_from_str "0RJ1RI_0RL1LH_1RJ1Lp_1RL1Lp_0LH0Ln_1RQ0Lp_1RK1Ln_1RI1Lp_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0LV0L__1RQ0RQ_1LV0RK_1RI0RI_0L_0RK_0LE1LH_0LH1RK_---1Lp_0L]0LF_0L_0LH_1L]1LF_1L_1LH_1LV0LH_1RI---_1Le0Ln_1Lp---_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RS---_0LH---_1RS---_0Lp---_0LE---_0LG---_1LE---_1LG---_0RK0RR_1LH0RT_1RK1RR_1Lp1RT_0LF0Le_0LH0Lp_1LF1Le_1LH1Lp".
Definition tm1 := TM'_from_str "0LB0RJ_1LI1LC_0LD---_0LF0LE_0LF0LG_1RH1LG_1LF1LG_0RA0RH_0LB0LF_1RA1RH".
Definition tm2 := TM'_from_str "0LB0RJ_1LI1LC_0LD1RK_0LF0LE_0LF0LG_1RH1LG_1LF1LG_0RA0RH_0LB0LF_1RA1RH_1RK1RK".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "Q_eEnHpIVK".
Definition mp' := mp_from_str "Q_eEnHpIVK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM528.


Module TM529.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RD---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0RJ_---0RL_1RL1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RB---_0RD---_1RB---_1RD---_1RT---_0LG---_1RK---_1LG---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0RY_---0R[_1RT1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`m".
Definition mp' := mp_from_str "TG^XhHIR`p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM529.


Module TM530.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1RE---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0RY_---0R[_1RT1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0R[0RY_---0R[_1R[1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0Rb---_0Rd---_1Rb---_1Rd---_------_1L`---_------_1RT---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XhHIR`p".
Definition mp' := mp_from_str "TG^XhHIR`p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM530.


Module TM531.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1RE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RE---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0R[0RY_---0R[_1R[1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0Rb---_0Rd---_1Rb---_1Rd---_------_1L`---_------_1RT---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0RJ_---0RL_1RL1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0Rb---_0Rd---_1Rb---_1Rd---_------_1RT---_------_1RK---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XhHIR`p".
Definition mp' := mp_from_str "TG^XgHIR`n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM531.


Module TM532.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1RB---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RL0RJ_---0RL_1RL1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0Rb---_0Rd---_1Rb---_1Rd---_------_1RT---_------_1RK---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RT_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lo0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0RY_---0R[_1RT1RY_---1R[_0Lm0LH_0Lo1LG_1Lm1LH_1Lo1RT_0RJ---_0RL---_1RJ---_1RL---_1LG---_1RR---_1RT---_1RI---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RA1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "TG^XhHIR`o".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM532.


Module TM533.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0LA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0RJ_---0RL_1L^1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RB---_0RD---_1RB---_1RD---_1RT---_0LG---_1RK---_1LG---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0RJ_---0RL_1L^1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "TG^XgHIR`n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM533.


Module TM534.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0LA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF0RF_0LA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0RJ_---0RL_1L^1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0Ri_---0Rk_1L^1Ri_---1Rk_0Ln1LG_0Lp---_1Ln1RT_1Lp---_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "TG^XgHIR`n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM534.


Module TM535.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RB---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0RJ_---0RL_1RT1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RJ---_0RL---_1RJ---_1RL---_1LG---_1RR---_1RT---_1RI---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0RY_---0R[_1L^1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`m".
Definition mp' := mp_from_str "TG^XhHIR`p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM535.


Module TM536.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RD---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0RY_---0R[_1L^1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0RJ_---0RL_1RT1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XhHIR`p".
Definition mp' := mp_from_str "TG^XgHIR`n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM536.


Module TM537.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RD---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_0LA0RF".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0RJ_---0RL_1RT1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1L_---_1RR---_1RT---_1RI---_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh1LX_1L_0RR_1Lh0RT_1RT0RI_0RK1L__1LX0RT_1RK---_1L_1RT_0L^0Lm_0L`0Lo_1L^1Lm_1L`1Lo_0RJ1L`_0RL1RT_1RJ1Lo_1RL1Lf_1L_0Lf_1RR0Lh_1RT1Lf_1RI1Lh_1RI0RT_1LE0LX_1Lh1RT_1RT0L__0LV0L]_0LX0L__1LV1L]_1LX1L__0RT0Ri_---0Rk_1RT1Ri_---1Rk_0LE1L__0LG0RT_1LE1RT_1LG0Ri".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "T_fXo`IRhE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM537.


Module TM538.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_0LA0RF".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF0RE_0RD---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1L_---_1RR---_1RT---_1RI---_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh1LX_1L_0RR_1Lh0RT_1RT0RI_0RK1L__1LX0RT_1RK---_1L_1RT_0L^0Lm_0L`0Lo_1L^1Lm_1L`1Lo_0RJ1L`_0RL1RT_1RJ1Lo_1RL1Lf_1L_0Lf_1RR0Lh_1RT1Lf_1RI1Lh_1RI0RT_1LE0LX_1Lh1RT_1RT0L__0LV0L]_0LX0L__1LV1L]_1LX1L__0RT0Ri_---0Rk_1RT1Ri_---1Rk_0LE1L__0LG0RT_1LE1RT_1LG0Ri".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0Ra_---0Rc_1RT1Ra_---1Rc_0Ln1LG_0Lp0RT_1Ln1RT_1Lp0Ra_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "T_fXo`IRhE".
Definition mp' := mp_from_str "TG^XgHIR`n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM538.


Module TM539.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF0RE_0RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1RA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0Ra_---0Rc_1RT1Ra_---1Rc_0Ln1LG_0Lp0RT_1Ln1RT_1Lp0Ra_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0RY_---0R[_1L^1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RB---_0RD---_1RB---_1RD---_1RT---_0LG---_1RK---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LB1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "TG^XhHIR`p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM539.


Module TM540.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1LD---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0L^_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0LX0RJ_---0RL_0LG1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RZ---_0R\---_1RZ---_1R\---_0Lg---_0L^---_1Lg---_1L^---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0L^_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0LX0RJ_---0RL_0LG1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_1LH---_1RT---_1Lg---_1L^---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LC---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LC1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "TG^XgHIR`m".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM540.


Module TM541.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LX_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LH0RJ_---0RL_1Lg1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_1RI---_1Ln---_1L`---_1RT---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LX_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LH0RJ_---0RL_1Lg1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RA---_0RC---_1RA---_1RC---_0RT---_0LX---_0RK---_1LX---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LD---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LD1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "TG^XgHIR`n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM541.


Module TM542.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0RB---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LX_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RR0RJ_---0RL_1RR1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RI---_0RK---_1RI---_1RK---_1LX---_0RR---_0RT---_0RI---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LX_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LH0RY_---0R[_1Lh1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RA---_0RC---_1RA---_1RC---_0RT---_0LX---_0RK---_1LX---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LD---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`m".
Definition mp' := mp_from_str "TG^XhHIR`p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM542.


Module TM543.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1LC---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LX_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LH0RY_---0R[_1Lh1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RA---_0RC---_1RA---_1RC---_0RT---_0LX---_0RK---_1LX---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LX_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LH0RY_---0R[_1Lh1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_1RI---_1Lp---_1L`---_1RT---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LD---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XhHIR`p".
Definition mp' := mp_from_str "TG^XhHIR`p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM543.


Module TM544.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1LA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0RD---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LH_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RI0RJ_---0RL_1L`1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RK---_1LX---_1RK---_1LG---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LH_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RI0RJ_---0RL_1L`1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LF---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LF1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`n".
Definition mp' := mp_from_str "TG^XgHIR`m".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM544.


Module TM545.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1LF_1RB1LE_1LC0LD_1LA0RE".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_0RC---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1L_---_1RR---_1RT---_1RI---_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0Lh1LX_1L_0RR_1Lh0RT_1RT0RI_0RK1RI_1LX0RT_1RK---_1L_1RT_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0RJ1L`_0RL1RT_1RJ1Lp_1RL1Lf_1L_0Lf_1RR0Lh_1RT1Lf_1RI1Lh_1RI0RT_1LH0LX_1Lh1RT_1RT0L__0LV0L]_0LX0L__1LV1L]_1LX1L__0RK0Ra_---0Rc_1RK1Ra_---1Rc_0LF0L`_0LH1L__1LF1L`_1LH1RT".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1RI_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lo0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RK0RY_---0R[_1RK1RY_---1R[_0Lm0LH_0Lo1LG_1Lm1LH_1Lo1RT_0RQ---_0RS---_1RQ---_1RS---_1RR---_0Lo---_1RI---_1Lo---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RG---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1RG1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "T_fXp`IRhH".
Definition mp' := mp_from_str "TG^XhHIR`o".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM545.


Module TM546.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RF_1RC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RC---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0L`_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LX0Rj_---0Rl_1LG1Rj_---1Rl_0Lm1LG_0Lo---_1Lm1RT_1Lo---_0RR---_0RT---_1RR---_1RT---_0L`---_1LG---_1L`---_1RT---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0L`_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LX0RJ_---0RL_1LG1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RR---_0RT---_1RR---_1RT---_0L`---_1LG---_1L`---_1RT---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`m".
Definition mp' := mp_from_str "TG^XgHIR`m".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM546.


Module TM547.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1LD---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0L`_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LX0RJ_---0RL_1LG1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RR---_0RT---_1RR---_1RT---_0L`---_1LG---_1L`---_1RT---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0L`_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LX0RJ_---0RL_1LG1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_1LH---_1RT---_1Lg---_1L^---_0L^---_0L`---_1L^---_1L`---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`m".
Definition mp' := mp_from_str "TG^XgHIR`n".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM547.


Module TM548.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1LD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1RC---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1L`_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LX0RY_---0R[_1LG1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_1LH---_1RT---_1Lh---_1L^---_0L^---_0L`---_1L^---_1L`---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1L`_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lo0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LX0RY_---0R[_1LG1RY_---1R[_0Lm0LH_0Lo1LG_1Lm1LH_1Lo1RT_0RR---_0RT---_1RR---_1RT---_0L`---_1LG---_1L`---_1RT---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XhHIR`p".
Definition mp' := mp_from_str "TG^XhHIR`o".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM548.


Module TM549.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF0RF_0LA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0LA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LE_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LG0Ri_---0Rk_0L^1Ri_---1Rk_0Lm1LG_0Lo---_1Lm1RT_1Lo---_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK0LE_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LG0RJ_---0RL_0L^1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LK---_1LB0LC".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_0LK1RL_1LB0LC_1RL1RL".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XgHIR`mE".
Definition mp' := mp_from_str "TG^XgHIR`mE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM549.


Module TM550.
Definition tm := TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA1LC_1LE0LA".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA1LC".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LX_1RL1Ln_1LG0Ln_1RQ0Lp_1RS1Ln_1RI1Lp_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lp1Lh_1LG0RQ_1Lp0RS_1RS0RI_1Lh0RS_---0Lh_1LG1RS_---0LG_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Rb---_0Rd---_1Rb---_1Rd---_0Lp---_0LG---_1Lp---_1LG---_0RK1Lp_1Lh1RS_1RK---_1LG1Ln_0LF0LV_0LH0LX_1LF1LV_1LH1LX_1RI0RS_1L_0Lh_1Lp1RS_1LG0LG_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LX_1RL1Lf_1LG0Lf_1RQ0Lh_1RS1Lf_1RI1Lh_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lh1Lp_1LG0RQ_1Lh0RS_1RS0RI_1Lp0RS_---0Lp_1LG1RS_---0LG_0L^0LE_0L`0LG_1L^1LE_1L`1LG_1LH---_1RS---_1LX---_1Lf---_0Lf---_0Lh---_1Lf---_1Lh---_1RI0RS_1L`0Lp_1Lh1RS_1LG0LG_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_0RK1Lh_1Lp1RS_1RK---_1LG1Lf_0LF0LV_0LH0LX_1LF1LV_1LH1LX".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1LB_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1LB_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "SGnhXHIQp_".
Definition mp' := mp_from_str "SGfpXHIQh`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM550.


Module TM551.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA1LC".
Definition tm' := TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA1LC_1LE1RE".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LX_1RL1Lf_1LG0Lf_1RQ0Lh_1RS1Lf_1RI1Lh_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lh1Lp_1LG0RQ_1Lh0RS_1RS0RI_1Lp0RS_---0Lp_1LG1RS_---0LG_0L^0LE_0L`0LG_1L^1LE_1L`1LG_1LH---_1RS---_1LX---_1Lf---_0Lf---_0Lh---_1Lf---_1Lh---_1RI0RS_1L`0Lp_1Lh1RS_1LG0LG_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_0RK1Lh_1Lp1RS_1RK---_1LG1Lf_0LF0LV_0LH0LX_1LF1LV_1LH1LX".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LX_1RL1Ln_1LG0Ln_1RQ0Lp_1RS1Ln_1RI1Lp_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lp1Lh_1LG0RQ_1Lp0RS_1RS0RI_1Lh0RS_---0Lh_1LG1RS_---0LG_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Rb---_0Rd---_1Rb---_1Rd---_0Lp---_0LG---_1Lp---_1LG---_0RK1Lp_1Lh1RS_1RK---_1LG1Ln_0LF0LV_0LH0LX_1LF1LV_1LH1LX_1RI0Rb_1L_0Rd_1Lp1Rb_1LG1Rd_0Lf0Lp_0Lh0LG_1Lf1Lp_1Lh1LG".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1LB_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1LB_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "SGfpXHIQh`".
Definition mp' := mp_from_str "SGnhXHIQp_".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM551.


Module TM552.
Definition tm := TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA1LC_1LE1RE".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF1RF_1LA1LC".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LX_1RL1Ln_1LG0Ln_1RQ0Lp_1RS1Ln_1RI1Lp_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lp1Lh_1LG0RQ_1Lp0RS_1RS0RI_1Lh0RS_---0Lh_1LG1RS_---0LG_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Rb---_0Rd---_1Rb---_1Rd---_0Lp---_0LG---_1Lp---_1LG---_0RK1Lp_1Lh1RS_1RK---_1LG1Ln_0LF0LV_0LH0LX_1LF1LV_1LH1LX_1RI0Rb_1L_0Rd_1Lp1Rb_1LG1Rd_0Lf0Lp_0Lh0LG_1Lf1Lp_1Lh1LG".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LX_1RL1Lf_1LG0Lf_1RQ0Lh_1RS1Lf_1RI1Lh_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lh1Lp_1LG0RQ_1Lh0RS_1RS0RI_1Lp0RS_---0Lp_1LG1RS_---0LG_0L^0LE_0L`0LG_1L^1LE_1L`1LG_1LH---_1RS---_1LX---_1Lf---_0Lf---_0Lh---_1Lf---_1Lh---_1RI0Rj_1L`0Rl_1Lh1Rj_1LG1Rl_0Ln0Lh_0Lp0LG_1Ln1Lh_1Lp1LG_0RK1Lh_1Lp1RS_1RK---_1LG1Lf_0LF0LV_0LH0LX_1LF1LV_1LH1LX".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1LB_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1LB_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LI1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "SGnhXHIQp_".
Definition mp' := mp_from_str "SGfpXHIQh`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM552.


Module TM553.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LC".
Definition tm' := TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA0LC_1LE0LA".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LW_1RL1Lf_1LG0Lf_1RQ0Lh_1RS1Lf_1RI1Lh_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lh1Lp_1LG0RQ_1Lh0RS_1RS0RI_1Lp0RS_---0Lp_1LG1RS_---0LG_0L^0LE_0L`0LG_1L^1LE_1L`1LG_1LH---_1RS---_1LW---_1Lf---_0Lf---_0Lh---_1Lf---_1Lh---_1RI0RS_1L^0Lp_1Lh1RS_1LE0LG_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_0RK0Lh_1Lp1LG_1RK---_1LG0Lf_0LF0LU_0LH0LW_1LF1LU_1LH1LW".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RS_1RJ1LW_1RL1Ln_1LG0Ln_1RQ0Lp_1RS1Ln_1RI1Lp_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lp1Lh_1LG0RQ_1Lp0RS_1RS0RI_1Lh0RS_---0Lh_1LG1RS_---0LG_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Rb---_0Rd---_1Rb---_1Rd---_0Lp---_0LE---_1Lp---_1LE---_0RK0Lp_1Lh1LG_1RK---_1LG0Ln_0LF0LU_0LH0LW_1LF1LU_1LH1LW_1RI0RS_1L]0Lh_1Lp1RS_1LE0LG_0Lf0LE_0Lh0LG_1Lf1LE_1Lh1LG".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LG1LE_1LK1LF_1LB0LC_1RH1LJ_0RI0RH_1LD0RA_1LD1LB_0LJ---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LG1LE_1LK1LF_1LB0LC_1RH1LJ_0RI0RH_1LD0RA_1LD1LB_0LJ1RL_1RL1RL".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "SGfpWEHIQh^".
Definition mp' := mp_from_str "SGnhWEHIQp]".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM553.


Module TM554.
Definition tm := TM_from_str "1RB0RB_1LC0LE_0RF1LD_1RA0LB_1RA0RE_---0RC".
Definition tm' := TM_from_str "1RB0RB_1LC0LE_0RF1LD_1RA0LB_1RA0RD_---0RC".
Definition tm0 := TM'_from_str "0RJ0RI_0RL0RK_1RJ1RI_1RL1RK_0L`0Ri_0RL1LO_1L`0RK_0RK1RB_0RQ0RL_1RL0RB_1RQ1RL_1LO1RB_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0Ri0RK_0Rk1LV_1Ri1RK_1Rk1Le_---0L^_0Ri0L`_---1L^_0RK1L`_0RB0Ri_0RD1LO_1RB0L`_1RD0RL_1LO0LM_1RQ0LO_1RB1LM_1RL1LO_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LO0RL_1RQ0RB_1RB0RK_1RL0Ra_---0RQ_---0RS_---1RQ_---1RS_------_---1RQ_---0RQ_---1RL".
Definition tm0' := TM'_from_str "0RJ0RI_0RL0RK_1RJ1RI_1RL1RK_0L`0Ri_0RL1LO_1L`0RK_0RK1RB_0RQ0RL_1RL0RB_1RQ1RL_1LO1RB_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0Ri0RK_0Rk1LV_1Ri1RK_1Rk1Le_---0L^_0Ri0L`_---1L^_0RK1L`_0RB0Ri_0RD1LO_1RB0L`_1RD0RL_1LO0LM_1RQ0LO_1RB1LM_1RL1LO_0RB0RY_0RD0R[_1RB1RY_1RD1R[_1LO0RL_1RQ0LV_1RB0RK_1RL1LV_---0RQ_---0RS_---1RQ_---1RS_------_---1RQ_---0RQ_---1RL".
Definition tm1 := TM'_from_str "1LB1RD_1LF1LC_1LB0RA_0RA0RE_1RI1RA_0RH0LG_1RA1LB_---0RI_0RH0RE".
Definition tm2 := TM'_from_str "1LB1RD_1LF1LC_1LB0RA_0RA0RE_1RI1RA_0RH0LG_1RA1LB_1RJ0RI_0RH0RE_1RJ1RJ".
Definition l0 := [0;0;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "LOeBKV`iQ".
Definition mp' := mp_from_str "LOeBKV`iQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM554.


Module TM555.
Definition tm := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_1LF0LB_0RE---".
Definition tm' := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_0LF0LB_1RD---".
Definition tm0 := TM'_from_str "0RS0Ra_1LH0Rc_1RS1Ra_1Lh1Rc_0LN1Lh_0LP1Lh_1LN1Rc_1LP1Rc_0RR1LP_0RT1Lp_1RR1Rc_1RT1LO_1Lh0L^_1RB0L`_1Rc1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1RD0RB_1L`0Rc_1RD0RQ_1RQ1Rc_0RD1Rc_1L`---_1RD1L^_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0RD0RD_---0LH_1RD1RD_---0Lh_0Ln0LM_0Lp0LO_1Ln1LM_1Lp1LO_0Ra---_0Rc---_1Ra---_1Rc---_1Lh---_1Lh---_1Rc---_1Rc---".
Definition tm0' := TM'_from_str "0RS0Ra_1LH0Rc_1RS1Ra_1Lh1Rc_0LN1Lh_0LP1Lh_1LN1Rc_1LP1Rc_0RR1LP_0RT1Lo_1RR1Rc_1RT1LO_1Lh0L^_1RB0L`_1Rc1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1RD0RB_1L`0Rc_1RD0RQ_1RQ1Rc_0RD1Rc_1L`---_1RD1L^_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0RD0RD_---0LH_1RD1RD_---0Lh_0Lm0LM_0Lo0LO_1Lm1LM_1Lo1LO_0RZ---_0R\---_1RZ---_1R\---_1Lh---_0LO---_1Rc---_1LO---".
Definition tm1 := TM'_from_str "1LB1RI_1LK1LC_1RI1LD_0LE0LB_1LF1RI_1RG1LJ_0RH0RG_1LE0RI_1RA1RA_1LE1LB_1RI---".
Definition tm2 := TM'_from_str "1LB1RI_1LK1LC_1RI1LD_0LE0LB_1LF1RI_1RG1LJ_0RH0RG_1LE0RI_1RA1RA_1LE1LB_1RI1RL_1RL1RL".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "DhO^HPQBc`p".
Definition mp' := mp_from_str "DhO^HPQBc`o".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM555.


Module TM556.
Definition tm := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_0LF0LB_1RD---".
Definition tm' := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_0LF0LB_1RC---".
Definition tm0 := TM'_from_str "0RS0Ra_1LH0Rc_1RS1Ra_1Lh1Rc_0LN1Lh_0LP1Lh_1LN1Rc_1LP1Rc_0RR1LP_0RT1Lo_1RR1Rc_1RT1LO_1Lh0L^_1RB0L`_1Rc1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1RD0RB_1L`0Rc_1RD0RQ_1RQ1Rc_0RD1Rc_1L`---_1RD1L^_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0RD0RD_---0LH_1RD1RD_---0Lh_0Lm0LM_0Lo0LO_1Lm1LM_1Lo1LO_0RZ---_0R\---_1RZ---_1R\---_1Lh---_0LO---_1Rc---_1LO---".
Definition tm0' := TM'_from_str "0RS0Ra_1LH0Rc_1RS1Ra_1Lh1Rc_0LN1Lh_0LP1Lh_1LN1Rc_1LP1Rc_0RR1LP_0RT1Lo_1RR1Rc_1RT1LO_1Lh0L^_1RB0L`_1Rc1L^_1RQ1L`_0RB0RQ_0RD0RS_1RB1RQ_1RD1RS_0L`1LH_1RD0RB_1L`0Rc_1RD0RQ_1RQ1Rc_0RD1Rc_1L`---_1RD1L^_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0RD0RD_---0LH_1RD1RD_---0Lh_0Lm0LM_0Lo0LO_1Lm1LM_1Lo1LO_0RR---_0RT---_1RR---_1RT---_1Lh---_1RB---_1Rc---_1RQ---".
Definition tm1 := TM'_from_str "1LB1RI_1LK1LC_1RI1LD_0LE0LB_1LF1RI_1RG1LJ_0RH0RG_1LE0RI_1RA1RA_1LE1LB_1RI---".
Definition tm2 := TM'_from_str "1LB1RI_1LK1LC_1RI1LD_0LE0LB_1LF1RI_1RG1LJ_0RH0RG_1LE0RI_1RA1RA_1LE1LB_1RI1RL_1RL1RL".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "DhO^HPQBc`o".
Definition mp' := mp_from_str "DhO^HPQBc`o".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM556.


Module TM557.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RD1RC_0RE0RF_1LF1LB_0LB---".
Definition tm' := TM_from_str "1LB0LB_0RC0LA_1RD1RC_0RE0RF_1LF1RC_0LB---".
Definition tm0 := TM'_from_str "0RR0RZ_1LN0LN_1RR1RZ_1LM0LM_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RQ0R\_0RS0Rc_1RQ0LG_1RS0LE_0Rc0LE_0R\0LG_0Rk1LE_0RT1LG_0RZ0RR_0R\0RT_1RZ1RR_1R\1RT_1LE1Rc_1RZ1R\_1RR1Rk_---1RT_0Ra0Ri_0Rc0Rk_1Ra1Ri_1Rc1Rk_0LO0Rc_0R\---_1LO0Rk_0RT---_0Rk0RR_---1LN_1LE1RR_---1LM_0Ln0LN_0Lp0LP_1Ln1LN_1Lp1LP_0RZ---_0LN---_1RZ---_0LM---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RR0RZ_1LN0LN_1RR1RZ_1LM0LM_0LN0LM_0LP0LO_1LN1LM_1LP1LO_0RQ0R\_0RS0Rc_1RQ0LG_1RS0LE_0Rc0LE_0R\0LG_0Rk1LE_0RT1LG_0RZ0RR_0R\0RT_1RZ1RR_1R\1RT_1LE1Rc_1RZ1R\_1RR1Rk_---1RT_0Ra0Ri_0Rc0Rk_1Ra1Ri_1Rc1Rk_0LO0Rc_0R\---_1LO0Rk_0RT---_0Rk0RR_---0RT_1LE1RR_---1RT_0Ln1Rc_0Lp1R\_1Ln1Rk_1Lp1RT_0RZ---_0LN---_1RZ---_0LM---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1RB---_0RC0RA_1LD1RH_0LE0LG_0RI0LF_1LE1LG_0RC0LD_0RI0RJ_1RC1RA_1RI1RJ".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RA_1LD1RH_0LE0LG_0RI0LF_1LE1LG_0RC0LD_0RI0RJ_1RC1RA_1RI1RJ_1RK1RK".
Definition l0 := [0;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "kZcENGMR\T".
Definition mp' := mp_from_str "kZcENGMR\T".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 39 39.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM557.


Module TM558.
Definition tm := TM_from_str "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LD---_0RC1LA".
Definition tm' := TM_from_str "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0LM_1RJ1RZ_1RL0Lo_1R\0Lm_0LM0Lo_1RL1Lm_1LM1Lo_0RR0R\_0RT1Rd_1RR1R\_1RT0LM_1Rd0LM_1RT0LO_1Rl1LM_0LM1LO_0RZ0RJ_0R\0RL_1RZ1RJ_1R\1RL_1LF1R\_1RS0LM_---1RL_1LF1LM_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0Lo1RZ_---0Lo_1Lo1RJ_---1Lo_------_0Rl---_------_1LF---_0L^---_0L`---_1L^---_1L`---_0RQ1Rd_0RS0Rl_1RQ0LM_1RS1LF_0Rd0LF_0RT0LH_0Rl1LF_1Rd1LH".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0LM_1RJ1RZ_1RL0Lo_1R\0Lm_0LM0Lo_1RL1Lm_1LM1Lo_0RR0R\_0RT1Rd_1RR1R\_1RT0LM_1Rd0LM_1RT0LO_1Rl1LM_0LM1LO_0RZ0RJ_0R\0RL_1RZ1RJ_1R\1RL_1LF1R\_1RS0LM_---1RL_1LF1LM_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0Lo1RZ_---0Lo_1Lo1RJ_---1Lo_1Rd---_0Rl---_0LM---_1LF---_0LF---_0LH---_1LF---_1LH---_0RQ1Rd_0RS0Rl_1RQ0LM_1RS1LF_0Rd0LF_0RT0LH_0Rl1LF_1Rd1LH".
Definition tm1 := TM'_from_str "1LB---_0LD0LC_0RE1LB_1RA0LD_1RF1LB_1RK1RG_0RH1RA_1RI1RJ_1RA1RE_1RH0LD_0RA0RE".
Definition tm2 := TM'_from_str "1LB1RL_0LD0LC_0RE1LB_1RA0LD_1RF1LB_1RK1RG_0RH1RA_1RI1RJ_1RA1RE_1RH0LD_0RA0RE_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "dFoMlSJT\LZ".
Definition mp' := mp_from_str "dFoMlSJT\LZ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 39 39.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM558.


Module TM559.
Definition tm := TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LD---".
Definition tm' := TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC0RF_1LE---".
Definition tm0 := TM'_from_str "0RJ1LE_0RL1L__1RJ0RR_1RL1LH_0LV0LF_0L_0LH_1LV1LF_1L_1LH_0LM0Rc_1RR1LE_0LV1Rc_0L_0RR_0LM0LV_0LO0LX_1LM1LV_1LO1LX_0RZ0LV_0R\0RR_1RZ0LF_1R\1RR_0LF0L]_1RR0L__1LF1L]_1Rj1L__1RR0Ra_0L_0Rc_0L_1Ra_0LH1Rc_0LE0R\_0LG0RR_1LE0RR_1LG---_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0LH0R\_0R\---_1Rc0RR_0RR---_0LV---_0RR---_0LF---_1RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ1LE_0RL1L__1RJ0RR_1RL1LH_0LV0LF_0L_0LH_1LV1LF_1L_1LH_0LM0Rc_1RR1LE_0LV1Rc_0L_0RR_0LM0LV_0LO0LX_1LM1LV_1LO1LX_0RZ0LV_0R\0RR_1RZ0LF_1R\1RR_0LF0L]_1RR0L__1LF1L]_1Ri1L__1RR0Ra_0L_0Rc_0L_1Ra_0LH1Rc_0LE0R\_0LG0RR_1LE0RR_1LG---_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LH0R\_0R\---_1Rc0RR_0RR---_0RR---_------_1RR---_------_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF---_0LC0LB".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF1RJ_0LC0LB_1RJ1RJ".
Definition l0 := [1;0;1;1;0;0;0;0]%N.
Definition mp := mp_from_str "\H_EVRcjF".
Definition mp' := mp_from_str "\H_EVRciF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 39 39.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM559.


Module TM560.
Definition tm := TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC0RF_1LE---".
Definition tm' := TM_from_str "1LB1LE_1RC0LC_0LA0RD_1RB1RF_0LC1LE_0LC---".
Definition tm0 := TM'_from_str "0RJ1LE_0RL1L__1RJ0RR_1RL1LH_0LV0LF_0L_0LH_1LV1LF_1L_1LH_0LM0Rc_1RR1LE_0LV1Rc_0L_0RR_0LM0LV_0LO0LX_1LM1LV_1LO1LX_0RZ0LV_0R\0RR_1RZ0LF_1R\1RR_0LF0L]_1RR0L__1LF1L]_1Ri1L__1RR0Ra_0L_0Rc_0L_1Ra_0LH1Rc_0LE0R\_0LG0RR_1LE0RR_1LG---_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LH0R\_0R\---_1Rc0RR_0RR---_0RR---_------_1RR---_------_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm0' := TM'_from_str "0R[1LE_1LE1LW_1R[0RJ_0RJ1Lh_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0RR0LN_0RT0RJ_1RR0Lf_1RT1RJ_0Lf0LU_1RJ0LW_1Lf1LU_1Rj1LW_1RJ0RY_0LW0R[_0LW1RY_0Lh1R[_0LE0RT_0LG0RJ_1LE0RJ_1LG---_0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0Lh0RT_0RT---_1R[0RJ_0RJ---_0LN1LE_0RJ1LW_0Lf0RJ_1RJ1Lh_0LU0Lf_0LW0Lh_1LU1Lf_1LW1Lh_0LN---_0RJ---_0Lf---_1RJ---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF---_0LC0LB".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF1RJ_0LC0LB_1RJ1RJ".
Definition l0 := [1;0;1;1;0;0;0;0]%N.
Definition mp := mp_from_str "\H_EVRciF".
Definition mp' := mp_from_str "ThWENJ[jf".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 39 39.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM560.


Module TM561.
Definition tm := TM_from_str "1RB1RD_1LC---_0LF0LD_0RE1LC_1RA1RF_1RE0LF".
Definition tm' := TM_from_str "1RB1RC_1LA---_0RE1LD_0LF0LC_1RA1RF_1RE0LF".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0L_1RB_---0L__1L_1Rj_---1L__1R\---_0R\---_1Lm---_1LV---_0LV---_0LX---_1LV---_1LX---_0RD0RB_1RL0Lo_1RD1RB_0Lm0L__0Lm0L]_0Lo0L__1Lm1L]_1Lo1L__0Ra1R\_0Rc0R\_1Ra1Lm_1Rc1LV_0RL0LV_0Rd0LX_0R\1LV_1RL1LX_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1LV1RD_1Rc0Lm_---1Rl_1LV1Lm_0Rb0RD_0Rd1RL_1Rb1RD_1Rd0Lm_1RL0Lm_1Rd0Lo_1R\1Lm_0Lm1Lo".
Definition tm0' := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_0LW1RB_---0LW_1LW1Rj_---1LW_------_0RT---_------_1L^---_0LF---_0LH---_1LF---_1LH---_0Ra1RT_0Rc0RT_1Ra1Lm_1Rc1L^_0RL0L^_0Rd0L`_0RT1L^_1RL1L`_0RD0RB_1RL0Lo_1RD1RB_0Lm0LW_0Lm0LU_0Lo0LW_1Lm1LU_1Lo1LW_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_1L^1RD_1Rc0Lm_---1Rl_1L^1Lm_0Rb0RD_0Rd1RL_1Rb1RD_1Rd0Lm_1RL0Lm_1Rd0Lo_1RT1Lm_0Lm1Lo".
Definition tm1 := TM'_from_str "1LB---_0LD0LC_0RF1LB_1RF1LE_1RA0LE_1RG1LB_1RL1RH_0RI1RA_1RK1RJ_1RI0LE_1RA1RF_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RM_0LD0LC_0RF1LB_1RF1LE_1RA0LE_1RG1LB_1RL1RH_0RI1RA_1RK1RJ_1RI0LE_1RA1RF_0RA0RF_1RM1RM".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LV_om\cjdlDB".
Definition mp' := mp_from_str "L^WomTcjdlDB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 40 40.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM561.


Module TM562.
Definition tm := TM_from_str "1RB1RC_1LA0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm' := TM_from_str "1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1R\1Lm_0Lm1R\_1RT1RC_1Lm1RT_0Lg---_0RT0Lg_0Ln---_1RT0Ln_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RZ0RR_0R\0RT_1RZ1RR_1R\1RT_0Lg1Lm_1RJ1R\_1Lg1RC_1RR1RT_1Lm0RA_---0RC_1RT1RA_1Lm1RC_0LN0RT_0LP0R\_1LN0Lg_1LP0RT_------_---1RJ_---1Lm_---0Lp_---0Lm_---0Lo_---1Lm_---1Lo_0RZ0RC_0R\1RR_1RZ1RC_1R\1Lp_0Lg0Ln_1RJ0Lp_1Lg1Ln_1RR1Lp".
Definition tm0' := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1R\1Lm_0Lm1R\_1RT1RC_1Lm1RT_0RC---_0RT0Lg_1RC---_1RT0Ln_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ0RR_0R\0RT_1RZ1RR_1R\1RT_0Lg1Lm_1RJ1R\_1Lg1RC_1RR1RT_1RR0RA_---0RC_1RT1RA_1Lm1RC_0LN0RT_0LP0R\_1LN0Lg_1LP0RT_------_---1RJ_---1Lm_---0Lp_---0Lm_---0Lo_---1Lm_---1Lo_0RZ0RC_0R\1RR_1RZ1RC_1R\1Lp_0Lg0Ln_1RJ0Lp_1Lg1Ln_1RR1Lp".
Definition tm1 := TM'_from_str "1RB1RH_0RC0LI_1RD1RC_1LE1RA_0LI0LF_1RB0LG_1RH1LG_0RD0RC_---1LE".
Definition tm2 := TM'_from_str "1RB1RH_0RC0LI_1RD1RC_1LE1RA_0LI0LF_1RB0LG_1RH1LG_0RD0RC_1RJ1LE_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "CJT\mnpRg".
Definition mp' := mp_from_str "CJT\mnpRg".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 42 42.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM562.


Module TM563.
Definition tm := TM_from_str "1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm' := TM_from_str "1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1R\1Lm_0Lm1R\_1RT1RC_1Lm1RT_0RC---_0RT0Lg_1RC---_1RT0Ln_0LV0Le_0LX0Lg_1LV1Le_1LX1Lg_0RZ0RR_0R\0RT_1RZ1RR_1R\1RT_0Lg1Lm_1RJ1R\_1Lg1RC_1RR1RT_1RR0RA_---0RC_1RT1RA_1Lm1RC_0LN0RT_0LP0R\_1LN0Lg_1LP0RT_------_---1RJ_---1Lm_---0Lp_---0Lm_---0Lo_---1Lm_---1Lo_0RZ0RC_0R\1RR_1RZ1RC_1R\1Lp_0Lg0Ln_1RJ0Lp_1Lg1Ln_1RR1Lp".
Definition tm0' := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1R\1Lm_0Lm1R\_1RT1RC_1Lm1RT_0RR---_0RT0Lg_1RR---_1RT0Ln_1Lm0Le_1R\0Lg_1RC1Le_1RT1Lg_0RZ0RR_0R\0RT_1RZ1RR_1R\1RT_0Lg1Lm_1RJ1R\_1Lg1RC_1RR1RT_0RT0RA_---0RC_1RT1RA_1Lm1RC_0LN0RT_0LP0R\_1LN0Lg_1LP0RT_------_---1RJ_---1Lm_---0Lp_---0Lm_---0Lo_---1Lm_---1Lo_0RZ0RC_0R\1RR_1RZ1RC_1R\1Lp_0Lg0Ln_1RJ0Lp_1Lg1Ln_1RR1Lp".
Definition tm1 := TM'_from_str "1RB1RH_0RC0LI_1RD1RC_1LE1RA_0LI0LF_1RB0LG_1RH1LG_0RD0RC_---1LE".
Definition tm2 := TM'_from_str "1RB1RH_0RC0LI_1RD1RC_1LE1RA_0LI0LF_1RB0LG_1RH1LG_0RD0RC_1RJ1LE_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "CJT\mnpRg".
Definition mp' := mp_from_str "CJT\mnpRg".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 42 42.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM563.


Module TM564.
Definition tm := TM_from_str "1LB0RD_1LC---_0RA1RD_0RF1LE_0LD0LE_1RC1RB".
Definition tm' := TM_from_str "1LB---_0LC0LB_0RD1LB_1RE1RA_0RF1RC_1LA0RC".
Definition tm0 := TM'_from_str "0R\0RY_---0R[_1Lg1RY_---1R[_0LN0RR_0LP0L__1LN0RJ_1LP1L__0RY---_1L]---_1RY---_1Le---_0LV---_0LX---_1LV---_1LX---_0RA0RZ_0RC0R\_1RA1RZ_1RC1R\_0LX1RR_0Ri0Lg_1LX1RJ_0R\1Lg_0Ri0R\_0Rk1L]_1Ri1Lf_1Rk1Le_0RC0Lf_1L]0Lh_0R\1Lf_---1Lh_0RR0RC_0L_0L]_1RR0Lf_0Lg0Le_0L]0Le_0L_0Lg_1L]1Le_1L_1Lg_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_1Lg0Lg_1Rk---_1RY1Lg_1Le---".
Definition tm0' := TM'_from_str "0RT---_1LU---_1LN---_1LM---_0LN---_0LP---_1LN---_1LP---_0Rb0Rk_0LW0LU_1Rb0LN_0LO0LM_0LU0LM_0LW0LO_1LU1LM_1LW1LO_0RY0RT_0R[1LU_1RY1LN_1R[1LM_0Rk0LN_1LU0LP_0RT1LN_---1LP_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_1LO0LO_1R[---_1RQ1LO_1LM---_0Ri0RR_0Rk0RT_1Ri1RR_1Rk1RT_0LP1Rb_0RY0LO_1LP1RB_0RT1LO_1LW0RQ_---0RS_1LO1RQ_---1RS_0LF0Rb_0LH0LW_1LF0RB_1LH1LW".
Definition tm1 := TM'_from_str "1RB1LJ_1RC1RL_0RD0RA_1LE1RH_1LF1LJ_0RD0LG_0LK0LE_0RI0RA_0RC0RL_0LF0LJ_0RA1LG_1LF---".
Definition tm2 := TM'_from_str "1RB1LJ_1RC1RL_0RD0RA_1LE1RH_1LF1LJ_0RD0LG_0LK0LE_0RI0RA_0RC0RL_0LF0LJ_0RA1LG_1LF1RM_1RM1RM".
Definition l0 := [0;1;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "\kRCg]fYie_J".
Definition mp' := mp_from_str "T[bkOUNQYMWB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM564.


Module TM565.
Definition tm := TM_from_str "1RB---_1LC0RC_0RE0LD_0RE1LB_0LB1RF_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RC_0RE0LD_1LC1LB_0LD1RA_1RB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rj0RQ_1LV0RS_1Rj1RQ_1LN1RS_0LV0RL_0LX0LV_1LV0Rj_1LX1LV_0Ra0RL_0Rc0LX_1Ra0L__1Rc0LV_0LV0L]_0RL0L__1LV1L]_0RC1L__0Ra0RC_0Rc0RL_1Ra1L__1Rc0L__0LV0LN_0RL0LP_1LV1LN_0RC1LP_0RL0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LN_0LO1RJ_1LM1RS_1LO---_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1LV_1Ra---_1L_0RS_0L_---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1LV_1Ra---_1L_0RS_0L_---_0RB0RQ_1LV0RS_1RB1RQ_1LN1RS_0LV0RL_0LX0LV_1LV0RB_1LX1LV_0Ra0RL_0Rc0LX_1Ra0L__1Rc0LV_0LV0L]_0RL0L__1LV1L]_0Rk1L__0RB0Rk_1LV0RL_1RB1L__1LN0L__0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RL0RB_0LX0RD_0L_1RB_0LV1RD_0L]1LN_0L_1RJ_1L]1RS_1L_---_0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---".
Definition tm1 := TM'_from_str "0RB0RJ_1LC1RH_0LD0LI_0RF1LE_1LI1LC_1RG---_1LI0RH_1RA0LE_0RB0LE_0RB0RF".
Definition tm2 := TM'_from_str "0RB0RJ_1LC1RH_0LD0LI_0RF1LE_1LI1LC_1RG1RK_1LI0RH_1RA0LE_0RB0LE_0RB0RF_1RK1RK".
Definition l0 := [0;1;0;1;0;0;1;1]%N.
Definition mp := mp_from_str "aLNX_CJSVj".
Definition mp' := mp_from_str "aLNX_kJSVB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM565.


Module TM566.
Definition tm := TM_from_str "1RB0RF_1LC0RC_0RE0LD_1LC1LB_0LD1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RE0LD_1LC1LB_0LB1RF_1RB0RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1LV_1Ra---_1L_0RS_0L_---_0RB0RQ_1LV0RS_1RB1RQ_1LN1RS_0LV0RL_0LX0LV_1LV0RB_1LX1LV_0Ra0RL_0Rc0LX_1Ra0L__1Rc0LV_0LV0L]_0RL0L__1LV1L]_0Rk1L__0RB0Rk_1LV0RL_1RB1L__1LN0L__0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RL0RB_0LX0RD_0L_1RB_0LV1RD_0L]1LN_0L_1RJ_1L]1RS_1L_---_0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rj0RQ_1LV0RS_1Rj1RQ_1LN1RS_0LV0RL_0LX0LV_1LV0Rj_1LX1LV_0Ra0RL_0Rc0LX_1Ra0L__1Rc0LV_0LV0L]_0RL0L__1LV1L]_0RC1L__0Rj0RC_1LV0RL_1Rj1L__1LN0L__0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RL0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LN_0LO1RJ_1LM1RS_1LO---_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L_1LV_1Ra---_1L_0RS_0L_---".
Definition tm1 := TM'_from_str "0RB0RJ_1LC1RH_0LD0LI_0RF1LE_1LI1LC_1RG---_1LI0RH_1RA0LE_0RB0LE_0RB0RF".
Definition tm2 := TM'_from_str "0RB0RJ_1LC1RH_0LD0LI_0RF1LE_1LI1LC_1RG1RK_1LI0RH_1RA0LE_0RB0LE_0RB0RF_1RK1RK".
Definition l0 := [0;1;0;1;0;0;1;1]%N.
Definition mp := mp_from_str "aLNX_kJSVB".
Definition mp' := mp_from_str "aLNX_CJSVj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM566.


Module TM567.
Definition tm := TM_from_str "1RB1RD_0LC0LA_1RA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm' := TM_from_str "1RB1RD_0LC1RA_1RA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LV1RL_1RL0L__1LV1R\_1R\1L__0RL1RD_1RD0RD_1RL0LX_0LX1RD_0LU0LE_0LW0LG_1LU1LE_1LW1LG_0RB0R\_0RD1Lf_1RB1R\_1RD1LX_0LX0LV_1RD0LX_1RD1LV_1Lf1LX_0RB0Rc_0RD1RD_1RB1Rc_1RD1Lf_0LX0Lf_1RD0Lh_1RD1Lf_1Lf1Lh_0Rj0RL_0Rl1Rj_1Rj1RL_1Rl0L__---0L]_1Rj0L__---1L]_1RL1L__---0Ra_---0Rc_---1Ra_---1Rc_------_---0LX_---0Rc_---1RD".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LV1RL_1RL0L__1LV1R\_1R\1L__0RL0RB_1RD0RD_1RL1RB_0LX1RD_0LU0LX_0LW1RD_1LU1RD_1LW1Lf_0RB0R\_0RD1Lf_1RB1R\_1RD1LX_0LX0LV_1RD0LX_1RD1LV_1Lf1LX_0RB0Rc_0RD1RD_1RB1Rc_1RD1Lf_0LX0Lf_1RD0Lh_1RD1Lf_1Lf1Lh_0Rj0RL_0Rl1Rj_1Rj1RL_1Rl0L__---0L]_1Rj0L__---1L]_1RL1L__---0Ra_---0Rc_---1Ra_---1Rc_------_---0LX_---0Rc_---1RD".
Definition tm1 := TM'_from_str "1RB1RF_0LC1RA_1LD1LC_1RG0LE_1RA1LD_1RA1LD_---0RH_1RG1RB".
Definition tm2 := TM'_from_str "1RB1RF_0LC1RA_1LD1LC_1RG0LE_1RA1LD_1RA1LD_1RI0RH_1RG1RB_1RI1RI".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "DLXf_\jc".
Definition mp' := mp_from_str "DLXf_\jc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM567.


Module TM568.
Definition tm := TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB".
Definition tm' := TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RA_1RF1RA_---0LA".
Definition tm0 := TM'_from_str "0RJ0RI_0RL0RK_1RJ1RI_1RL1RK_0LW0LP_0LV1Rk_1LW1LP_1LV1RD_1LP0Rd_1RD1RJ_1LW1Rd_1LV0LX_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RZ0RC_0R\1RI_1RZ1RC_1R\1LX_1Rk0LV_1RJ0LX_1RD1LV_1RI1LX_0Rb0RA_0Rd0RC_1Rb1RA_1Rd1RC_---1RD_1RL1LP_1LW1RJ_1RK0Rd_0Ri0RB_0Rk0RD_1Ri1RB_1Rk1RD_---1LV_0LP1LW_---0LX_1LP1Rd_---1LP_---1RD_---1LW_---1LV_---0LN_---0LP_---1LN_---1LP".
Definition tm0' := TM'_from_str "0RJ0RI_0RL0RK_1RJ1RI_1RL1RK_0LW0LP_0LV1Rl_1LW1LP_1LV1RD_1LP0Rd_1RD1RJ_1LW1Rd_1LV0LX_0LN0LU_0LP0LW_1LN1LU_1LP1LW_0RZ0RC_0R\1RI_1RZ1RC_1R\1LX_1Rl0LV_1RJ0LX_1RD1LV_1RI1LX_0Rb0RA_0Rd0RC_1Rb1RA_1Rd1RC_---1RD_1RL1LP_1LW1RJ_1RK0Rd_0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_---1LV_0LP1LW_---0LX_1LP1Rd_---1RD_---1LP_---1LV_---1LW_---0LE_---0LG_---1LE_---1LG".
Definition tm1 := TM'_from_str "1LB0LC_1RJ0LC_1RD1LC_1LK0RE_1RH1RF_1RA1RG_1LI1RE_---1LI_1RF1LB_1RF1RJ_1LK1LI".
Definition tm2 := TM'_from_str "1LB0LC_1RJ0LC_1RD1LC_1LK0RE_1RH1RF_1RA1RG_1LI1RE_1RL1LI_1RF1LB_1RF1RJ_1LK1LI_1RL1RL".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "LVXIdDKkWJP".
Definition mp' := mp_from_str "LVXIdDKlWJP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM568.


Module TM569.
Definition tm := TM_from_str "1LB1RA_0LC1RE_0RC0LD_1RE1LD_1RF0RA_1RB---".
Definition tm' := TM_from_str "1RB0LC_0LA1RD_1RD1LC_1RE0RF_1RB---_1LB1RF".
Definition tm0 := TM'_from_str "0Rl0RB_0RC0RD_1L]1RB_1RC1RD_0LN1L]_0LP1RC_1LN1RB_1LP1RD_0RQ0Rb_1RL0Rd_1RQ1Rb_0L^1Rd_0LU1RL_0LW1L]_1LU---_1LW1RB_0RQ0Rl_0RS1L]_1RQ1Rl_1RS0L`_0RQ0L]_1RL0L__0Rl1L]_---1L__0Rb0RC_0Rd1RB_1Rb1RC_1Rd1L`_1RL0L^_1L]0L`_---1L^_1RB1L`_0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_0L^0LW_---0RC_1Rd1LW_---0RD_0RJ---_0RL---_1RJ---_1RL---_0L]---_1Rl---_1L]---_1RC---".
Definition tm0' := TM'_from_str "0RJ0Rd_0RL1LU_1RJ1Rd_1RL0LX_0LU0LU_1Rd0LW_1LU1LU_1Rk1LW_1RL0RZ_1RL0R\_0LV1RZ_0LV1R\_0LE1RL_0LG1LU_1LE---_1LG1Rj_0RZ0Rk_0R\1Rj_1RZ1Rk_1R\1LX_1RL0LV_1LU0LX_---1LV_1Rj1LX_0Rb0Ri_0Rd0Rk_1Rb1Ri_1Rd1Rk_0LV0LG_---0Rk_1R\1LG_---0Rl_0RJ---_0RL---_1RJ---_1RL---_0LU---_1Rd---_1LU---_1Rk---_1LU0Rj_0Rk0Rl_1LU1Rj_1Rk1Rl_0LN1LU_0LP1Rk_1LN1Rj_1LP1Rl".
Definition tm1 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC---_1LB0LG_1RH1LG_0RA0RI_1RA1RI".
Definition tm2 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC1RJ_1LB0LG_1RH1LG_0RA0RI_1RA1RI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "C]Ldl^`BD".
Definition mp' := mp_from_str "kUL\dVXjl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM569.


Module TM570.
Definition tm := TM_from_str "1RB0LC_0LA1RD_1RD1LC_1RE0RF_1RB---_1LB1RF".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD0RB_1RE1LD_1RA0RF_1LB1RF".
Definition tm0 := TM'_from_str "0RJ0Rd_0RL1LU_1RJ1Rd_1RL0LX_0LU0LU_1Rd0LW_1LU1LU_1Rk1LW_1RL0RZ_1RL0R\_0LV1RZ_0LV1R\_0LE1RL_0LG1LU_1LE---_1LG1Rj_0RZ0Rk_0R\1Rj_1RZ1Rk_1R\1LX_1RL0LV_1LU0LX_---1LV_1Rj1LX_0Rb0Ri_0Rd0Rk_1Rb1Ri_1Rd1Rk_0LV0LG_---0Rk_1R\1LG_---0Rl_0RJ---_0RL---_1RJ---_1RL---_0LU---_1Rd---_1LU---_1Rk---_1LU0Rj_0Rk0Rl_1LU1Rj_1Rk1Rl_0LN1LU_0LP1Rk_1LN1Rj_1LP1Rl".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L]---_1RD---_1L]---_1Rk---_1RL0Rb_1RL0Rd_0L^1Rb_0L^1Rd_0LU1RL_0LW1L]_1LU---_1LW1Rj_0RD0RI_1L]0RK_1RD1RI_0L`1RK_0L]0L]_0L_0RD_1L]1L]_1L_0Rk_0Rb0Rk_0Rd1Rj_1Rb1Rk_1Rd1L`_1RL0L^_1L]0L`_---1L^_1Rj1L`_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0L^0LW_---0Rk_1Rd1LW_---0Rl_1L]0Rj_0Rk0Rl_1L]1Rj_1Rk1Rl_0LN1L]_0LP1Rk_1LN1Rj_1LP1Rl".
Definition tm1 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC---_1LB0LG_1RH1LG_0RA0RI_1RA1RI".
Definition tm2 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC1RJ_1LB0LG_1RH1LG_0RA0RI_1RA1RI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "kUL\dVXjl".
Definition mp' := mp_from_str "k]LdD^`jl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM570.


Module TM571.
Definition tm := TM_from_str "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm' := TM_from_str "1RB1RD_0LC0LA_0RA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LV1RL_1RL0L__1LV1R\_1R\1L__0RJ0RB_0RD0RD_1RJ1RB_0LX1RD_0LU0LX_0LW1RD_1LU1RD_1LW1Lf_0RA0RZ_0RC1RD_1RA1RZ_1RC1LX_0RD0LV_0RD0LX_0RD1LV_1RD1LX_0RB0Rc_0RD1RD_1RB1Rc_1RD1Lf_0LX0Lf_1RD0Lh_1RD1Lf_1Lf1Lh_0Rj0RL_0Rl1Rj_1Rj1RL_1Rl0L__---0L]_1Rj0L__---1L]_1RL1L__---0Ra_---0Rc_---1Ra_---1Rc_------_---0LX_---0Rc_---1RD".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LV1RL_1RL0L__1LV1R\_1R\1L__0RJ0RD_0RD0RD_1RJ0LX_0LX1RD_0LU0LE_0LW0LG_1LU1LE_1LW1LG_0RA0RZ_0RC1RD_1RA1RZ_1RC1LX_0RD0LV_0RD0LX_0RD1LV_1RD1LX_0RB0Rc_0RD1RD_1RB1Rc_1RD1Lf_0LX0Lf_1RD0Lh_1RD1Lf_1Lf1Lh_0Rj0RL_0Rl1Rj_1Rj1RL_1Rl0L__---0L]_1Rj0L__---1L]_1RL1L__---0Ra_---0Rc_---1Ra_---1Rc_------_---0LX_---0Rc_---1RD".
Definition tm1 := TM'_from_str "1RB1RD_0LC1RA_1RA1LC_1RA1LE_1RG0LF_1RA1LE_---0RH_1RG1RB".
Definition tm2 := TM'_from_str "1RB1RD_0LC1RA_1RA1LC_1RA1LE_1RG0LF_1RA1LE_1RI0RH_1RG1RB_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "DLX\f_jc".
Definition mp' := mp_from_str "DLX\f_jc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM571.


Module TM572.
Definition tm := TM_from_str "1LB0RF_1RC1RE_1LD1RB_0LA1LD_---1LF_1RA0RD".
Definition tm' := TM_from_str "1LB0RF_1RC0RE_1LD1RB_0LA1LD_---1LD_1RA0RD".
Definition tm0 := TM'_from_str "0RL0Ri_1LN0Rk_1RL1Ri_0Rk1Rk_0LN1LN_0LP1RT_1LN0Rk_1LP1LN_0RR0Rb_0RT0Rd_1RR1Rb_1RT1Rd_0L`---_1RT0LG_1L`---_1Rd1LG_1LN0RJ_1LG0RL_0Rk1RJ_1L`1RL_0L^1L`_0L`---_1L^1RL_1L`0Rk_1RT1LN_0RB1LG_0LG0Rk_1RB1L`_0LE0L^_0LG0L`_1LE1L^_1LG1L`_---0Rk_---1LN_---1Rk_---0Rk_---0Ln_---0Lp_---1Ln_---1Lp_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0LG0LN_1RB0LG_1LG1LN_1RY1LG".
Definition tm0' := TM'_from_str "0RL0Ri_1LN0Rk_1RL1Ri_0Rk1Rk_0LN1LN_0LP1RT_1LN0Rk_1LP1LN_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0L`---_1RT0LG_1L`---_1Rc1LG_1LN0RJ_1LG0RL_0Rk1RJ_1L`1RL_0L^1L`_0L`---_1L^1RL_1L`0Rk_1RT1LN_0RB1LG_0LG0Rk_1RB1L`_0LE0L^_0LG0L`_1LE1L^_1LG1L`_---1LN_---1LG_---0Rk_---1L`_---0L^_---0L`_---1L^_---1L`_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0LG0LN_1RB0LG_1LG1LN_1RY1LG".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RA_1LD1LC_1LE0RG_1RB0LD_---0RG_1RI1RH_1RB1LE_1LE0RG".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RA_1LD1LC_1LE0RG_1RB0LD_1RJ0RG_1RI1RH_1RB1LE_1LE0RG_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "LT`GNdkYB".
Definition mp' := mp_from_str "LT`GNckYB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM572.


Module TM573.
Definition tm := TM_from_str "1LB0RF_1RC0RE_1LD1RB_0LA1LD_---1LD_1RA0RD".
Definition tm' := TM_from_str "1LB0RF_1RC0RD_1LD1RB_---1LE_0LA1LE_1RA0RE".
Definition tm0 := TM'_from_str "0RL0Ri_1LN0Rk_1RL1Ri_0Rk1Rk_0LN1LN_0LP1RT_1LN0Rk_1LP1LN_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0L`---_1RT0LG_1L`---_1Rc1LG_1LN0RJ_1LG0RL_0Rk1RJ_1L`1RL_0L^1L`_0L`---_1L^1RL_1L`0Rk_1RT1LN_0RB1LG_0LG0Rk_1RB1L`_0LE0L^_0LG0L`_1LE1L^_1LG1L`_---1LN_---1LG_---0Rk_---1L`_---0L^_---0L`_---1L^_---1L`_0RB0RY_0RD0R[_1RB1RY_1RD1R[_0LG0LN_1RB0LG_1LG1LN_1RY1LG".
Definition tm0' := TM'_from_str "0RL0Ri_1LN0Rk_1RL1Ri_0Rk1Rk_0LN1LN_0LP1RT_1LN0Rk_1LP1LN_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0Lh---_1RT0LG_1Lh---_1R[1LG_---0RJ_1LG0RL_---1RJ_1Lh1RL_0L^1Lh_0L`---_1L^1RL_1L`0Rk_---1LN_---1LG_---0Rk_---1Lh_---0Lf_---0Lh_---1Lf_---1Lh_1RT1LN_0RB1LG_0LG0Rk_1RB1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_0LG0LN_1RB0LG_1LG1LN_1Ra1LG".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RA_1LD1LC_1LE0RG_1RB0LD_---0RG_1RI1RH_1RB1LE_1LE0RG".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RA_1LD1LC_1LE0RG_1RB0LD_1RJ0RG_1RI1RH_1RB1LE_1LE0RG_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "LT`GNckYB".
Definition mp' := mp_from_str "LThGN[kaB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 43 43.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM573.


Module TM574.
Definition tm := TM_from_str "1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF".
Definition tm' := TM_from_str "1RB0LE_1RC0RF_1RD---_0LA1RB_1RB1LE_1LD1RF".
Definition tm0 := TM'_from_str "0RJ0Rk_0RL1Rj_1RJ1Rk_1RL1LH_1R\0LF_1LE0LH_---1LF_1Rj1LH_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LF0Lg_---0Rk_1RL1Lg_---0Rl_0RZ---_0R\---_1RZ---_1R\---_0LE---_1RT---_1LE---_1Rk---_---0RJ_1R\0RL_---1RJ_0LF1RL_0Le1R\_0Lg1LE_1Le---_1Lg1Rj_---0RT_---1LE_---1RT_---0LH_---0LE_---0LG_---1LE_---1LG_---0Rj_0Rk0Rl_1LE1Rj_1Rk1Rl_0L^1LE_0L`1Rk_1L^1Rj_1L`1Rl".
Definition tm0' := TM'_from_str "0RJ0RT_0RL1Le_1RJ1RT_1RL0Lh_1R\0Le_1Le0Lg_---1Le_1Rj1Lg_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0Lf0LG_---0Rk_1RL1LG_---0Rl_0RZ---_0R\---_1RZ---_1R\---_0Le---_1RT---_1Le---_1Rk---_0RT0RJ_1R\0RL_1RT1RJ_0Lf1RL_0LE1R\_0LG1Le_1LE---_1LG1Rj_0RJ0Rk_0RL1Rj_1RJ1Rk_1RL1Lh_1R\0Lf_1Le0Lh_---1Lf_1Rj1Lh_---0Rj_0Rk0Rl_1Le1Rj_1Rk1Rl_0L^1Le_0L`1Rk_1L^1Rj_1L`1Rl".
Definition tm1 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC---_1LB0LG_1RH1LG_0RA0RI_1RA1RI".
Definition tm2 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC1RJ_1LB0LG_1RH1LG_0RA0RI_1RA1RI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "kE\LTFHjl".
Definition mp' := mp_from_str "ke\LTfhjl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 44 44.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM574.


Module TM575.
Definition tm := TM_from_str "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0LB_---0LD".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0L^0Lh_1RJ1RL_1L^1RC_1RB1RD_0RT0RA_0LO0RC_1RT1RA_0Lh1RC_0LU0LO_0LW0RL_1LU0RC_1LW0RD_0RR1LU_0RT1Lp_1RR0RC_1RT1LO_1RT0L^_0Lh0L`_1LO1L^_1Lh1L`_1RT---_0RJ1LU_0L^1L__1RJ0RC_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_---0RQ_1LM0RS_---1RQ_1Lf1RS_0Ln0RT_0Lp0LO_1Ln1Lp_1Lp1LO_---0LU_---0Lp_---0LO_---0LO_---0L]_---0L__---1L]_---1L_".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0L^0Lh_1RJ1RL_1L^1RC_1RB1RD_0RT0RA_0LO0RC_1RT1RA_0Lh1RC_0LU0LO_0LW0RL_1LU0RC_1LW0RD_0RR1LU_0RT1Lp_1RR0RC_1RT1LO_1RT0L^_0Lh0L`_1LO1L^_1Lh1L`_1RT---_0RJ1LU_0L^1L__1RJ0RC_0LM0Lf_0LO0Lh_1LM1Lf_1LO1Lh_---1RT_1LM0RJ_---0L^_1Lf1RJ_0Ln0LM_0Lp0LO_1Ln1LM_1Lp1LO_---0LU_---0Lp_---0LO_---0LO_---0L]_---0L__---1L]_---1L_".
Definition tm1 := TM'_from_str "0LB1RF_1LI1LC_1LD0RF_1RL0LE_0LC0LB_1RG1RH_0LC0RF_0RA0RM_---1LJ_1LK1LN_0LD0LC_1RL1LC_1RA1RM_0LI0LC".
Definition tm2 := TM'_from_str "0LB1RF_1LI1LC_1LD0RF_1RL0LE_0LC0LB_1RG1RH_0LC0RF_0RA0RM_1RO1LJ_1LK1LN_0LD0LC_1RL1LC_1RA1RM_0LI0LC_1RO1RO".
Definition l0 := [0;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LhOU^CJBp_MTDf".
Definition mp' := mp_from_str "LhOU^CJBp_MTDf".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 45 45.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM575.


Module TM576.
Definition tm := TM_from_str "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm' := TM_from_str "1RB1RD_0LC0LA_1LA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm0 := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LV1RL_1RL0L__1LV1R\_1R\1L__1RL0RB_0LH0RD_0L_1RB_0LX1RD_0LU0LX_0LW1RD_1LU1RD_1LW1Lf_0RD1R\_1RD1LH_1RD1L__1Lf1LX_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0RB0Rc_0RD1RD_1RB1Rc_1RD1Lf_0LX0Lf_1RD0Lh_1RD1Lf_1Lf1Lh_0Rj0RL_0Rl1Rj_1Rj1RL_1Rl0L__---0L]_1Rj0L__---1L]_1RL1L__---0Ra_---0Rc_---1Ra_---1Rc_------_---0LX_---0Rc_---1RD".
Definition tm0' := TM'_from_str "0RJ0RZ_0RL0R\_1RJ1RZ_1RL1R\_0LV1RL_1RL0L__1LV1R\_1R\1L__1RL0LH_0LH0RD_0L_0LX_0LX1RD_0LU0LE_0LW0LG_1LU1LE_1LW1LG_0RD1R\_1RD1LH_1RD1L__1Lf1LX_0LF0LV_0LH0LX_1LF1LV_1LH1LX_0RB0Rc_0RD1RD_1RB1Rc_1RD1Lf_0LX0Lf_1RD0Lh_1RD1Lf_1Lf1Lh_0Rj0RL_0Rl1Rj_1Rj1RL_1Rl0L__---0L]_1Rj0L__---1L]_1RL1L__---0Ra_---0Rc_---1Ra_---1Rc_------_---0LX_---0Rc_---1RD".
Definition tm1 := TM'_from_str "1RB1RE_0LC1RA_1LD1LC_1RE1LG_1RA1LF_1RH0LG_1RA1LF_---0RI_1RH1RB".
Definition tm2 := TM'_from_str "1RB1RE_0LC1RA_1LD1LC_1RE1LG_1RA1LF_1RH0LG_1RA1LF_1RJ0RI_1RH1RB_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "DLXH\f_jc".
Definition mp' := mp_from_str "DLXH\f_jc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 46 46.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM576.


Module TM577.
Definition tm := TM_from_str "1RB1LA_1RC1RE_1LD1RC_1LC0LA_1RF0RC_---0RB".
Definition tm' := TM_from_str "1RB1LA_0RC1RE_1LD0LA_0LA0RC_1RF0RD_---0RB".
Definition tm0 := TM'_from_str "0RJ0Rd_0RL1RS_1RJ1Rd_1RL1LH_1LF0LF_1Rl0LH_1RT1LF_1RS1LH_0RR0Rb_0RT0Rd_1RR1Rb_1RT1Rd_0LG---_1LF1RT_1LG1RK_1RT1RR_1L`0RR_1RT0RT_1RT1RR_1LF1RT_0L^0LG_0L`1LF_1L^1LG_1L`1RT_1LX0RT_0RT1Rl_1LG1RT_1RT0LH_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0Rj0RQ_0Rl0RS_1Rj1RQ_1Rl1RS_---0LX_1RR1RT_---1LX_1Rb0RT_---0RI_---0RK_---1RI_---1RK_---1RT_---0Rl_---0RT_---0RS".
Definition tm0' := TM'_from_str "0RJ0Rd_0RL1R[_1RJ1Rd_1RL1LH_1LF0LF_1Rl0LH_1RS1LF_1R[1LH_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_0LG---_1LF1RS_1LG1RK_1RS1RQ_1RS0RS_0RS1Rl_1LF1RS_1RS0LH_0L^0LE_0L`0LG_1L^1LE_1L`1LG_0RS0RQ_1Rl0RS_1RS1RQ_0LH1RS_0LE0LG_0LG1LF_1LE1LG_1LG1RS_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_---1LF_1RQ1RS_---1RS_1Rb0RS_---0RI_---0RK_---1RI_---1RK_---1RS_---0Rl_---0RS_---0R[".
Definition tm1 := TM'_from_str "1RB1RE_1LC1RB_1RF0LD_1RA1LD_1RB0RB_---1RG_1RE1RH_0RF0RA".
Definition tm2 := TM'_from_str "1RB1RE_1LC1RB_1RF0LD_1RA1LD_1RB0RB_1RI1RG_1RE1RH_0RF0RA_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "STFHRlKb".
Definition mp' := mp_from_str "[SFHQlKb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 47 47.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM577.


Module TM578.
Definition tm := TM_from_str "1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1LB0LE".
Definition tm' := TM_from_str "1RB0LA_1RC1RA_1RD1RF_1LE---_1LB0LF_0RB1LE".
Definition tm0 := TM'_from_str "0RJ0RT_0RL1R\_1RJ1RT_1RL0LE_1R\0LE_1RL0LG_1Rd1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1Ln1RT_1RK0LE_---1RD_1Ln1LE_0RZ0Rb_0R\0Rd_1RZ1Rb_1R\1Rd_0Lg1RR_---0Lg_1Lg1RB_---1Lg_------_0Rd---_------_1Ln---_0LV---_0LX---_1LV---_1LX---_0RI1Ln_0RK0Rd_1RI1LE_1RK1Ln_0R\0Ln_0RL0Lp_0Rd1Ln_1R\1Lp_0Rd0RR_1R\0LP_1Rd1RR_0LE0Lg_0LN0Le_0LP0Lg_1LN1Le_1LP1Lg".
Definition tm0' := TM'_from_str "0RJ0RT_0RL1R\_1RJ1RT_1RL0LE_1R\0LE_1RL0LG_1Rl1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1Lf1RT_1RK0LE_---1RD_1Lf1LE_0RZ0Rj_0R\0Rl_1RZ1Rj_1R\1Rl_0Lo1RR_---0Lo_1Lo1RB_---1Lo_1Lf---_0Rl---_1LE---_1Lf---_0Lf---_0Lh---_1Lf---_1Lh---_0Rl0RR_1R\0LP_1Rl1RR_0LE0Lo_0LN0Lm_0LP0Lo_1LN1Lm_1LP1Lo_0RI1Lf_0RK0Rl_1RI1LE_1RK1Lf_0R\0Lf_0RL0Lh_0Rl1Lf_1R\1Lh".
Definition tm1 := TM'_from_str "1RB1LE_1RC1RI_0RD0RA_1LE---_0LF0LH_1LE1LG_1RD0LG_0RA1LE_0RJ1RD_1RL1RK_1RJ0LG_1RD1RA".
Definition tm2 := TM'_from_str "1RB1LE_1RC1RI_0RD0RA_1LE1RM_0LF0LH_1LE1LG_1RD0LG_0RA1LE_0RJ1RD_1RL1RK_1RJ0LG_1RD1RA_1RM1RM".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "dKR\nPEgBLDT".
Definition mp' := mp_from_str "lKR\fPEoBLDT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 48 48.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM578.


Module TM579.
Definition tm := TM_from_str "1RB1LA_0RC0RD_1LC1RA_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_1LC0RD_1LA1RC_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RB1LF_1RZ1LH_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0LX1Ln_0RL0Rd_1LX1Rb_1RZ0R\_1LX0RB_1RZ0RD_1LH1RB_1LH1RD_0LV1RS_0LX0LH_1LV1R[_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RS_1Ln1Rb_---1RS_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RT1LF_1RZ1LH_1RZ0RY_0RT0R[_1LH1RY_1RT1R[_0LV1Ln_0LX0Rd_1LV1Rb_1LX0R\_0R[0RR_1RZ0RT_1R[1RR_1LH1RT_0LF0LH_0LH1LH_1LF1LH_1LH1RT_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_---0LI_1LH1LC".
Definition tm2 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_1RJ0LI_1LH1LC_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "\dEFHZbng".
Definition mp' := mp_from_str "\dEFHZbng".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM579.


Module TM580.
Definition tm := TM_from_str "1RB1LA_1LC0RD_1LA1RC_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_1RC0RD_1LA---_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RT1LF_1RZ1LH_1RZ0RY_0RT0R[_1LH1RY_1RT1R[_0LV1Ln_0LX0Rd_1LV1Rb_1LX0R\_0R[0RR_1RZ0RT_1R[1RR_1LH1RT_0LF0LH_0LH1LH_1LF1LH_1LH1RT_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_---1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_---0Rd_1LH1Rb_---0R\_0R[---_1RZ---_1R[---_1LH---_0LF---_0LH---_1LF---_1LH---_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_---0LI_1LH1LC".
Definition tm2 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_1RJ0LI_1LH1LC_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "\dEFHZbng".
Definition mp' := mp_from_str "\dEFHZbng".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM580.


Module TM581.
Definition tm := TM_from_str "1RB1LA_1RC0RD_1LA---_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_1RC0RD_1LC1RA_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_---1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_---0Rd_1LH1Rb_---0R\_0R[---_1RZ---_1R[---_1LH---_0LF---_0LH---_1LF---_1LH---_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RD1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_1RL0Rd_1LH1Rb_1LH0R\_1LX0RB_1RZ0RD_1LH1RB_1LH1RD_0LV1RT_0LX0LH_1LV1R[_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_---0LI_1LH1LC".
Definition tm2 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_1RJ0LI_1LH1LC_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "\dEFHZbng".
Definition mp' := mp_from_str "\dEFHZbng".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM581.


Module TM582.
Definition tm := TM_from_str "1RB1LA_1RC0RD_1LC1RA_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LB_1RC1LB_1LB0RD_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RD1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_1RL0Rd_1LH1Rb_1LH0R\_1LX0RB_1RZ0RD_1LH1RB_1LH1RD_0LV1RT_0LX0LH_1LV1R[_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LP_1LP0LN_0LP0LP_1R[1LN_1LP1LP_0RR0R[_0RT1RZ_1RR1R[_1RT1LP_0LP0LN_1Rb0LP_1LP1LN_1RZ1LP_0R[0RY_1RZ0R[_1R[1RY_1LP1R[_0LN1Ln_0LP0Rd_1LN1Rb_1LP0R\_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LN1Rd_1Lg0LP_1LN1R\_---0RT_1Ln1Rb_---1RT_1LE0LP_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LP_---0Lg_---0LN_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_---0LI_1LH1LC".
Definition tm2 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_1RJ0LI_1LH1LC_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "\dEFHZbng".
Definition mp' := mp_from_str "\dENPZbng".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM582.


Module TM583.
Definition tm := TM_from_str "1RB1LB_1RC1LB_1LB0RD_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LP_1LP0LN_0LP0LP_1R[1LN_1LP1LP_0RR0R[_0RT1RZ_1RR1R[_1RT1LP_0LP0LN_1Rb0LP_1LP1LN_1RZ1LP_0R[0RY_1RZ0R[_1R[1RY_1LP1R[_0LN1Ln_0LP0Rd_1LN1Rb_1LP0R\_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LN1Rd_1Lg0LP_1LN1R\_---0RT_1Ln1Rb_---1RT_1LE0LP_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LP_---0Lg_---0LN_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1R[1LF_1RZ1LH_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0LX1Ln_1Rb0Rd_1LX1Rb_1RZ0R\_1LX0R[_1RZ1RZ_1LH1R[_1LH1LH_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RS_1Ln1Rb_---1RS_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_---0LI_1LH1LC".
Definition tm2 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_1RJ0LI_1LH1LC_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "\dENPZbng".
Definition mp' := mp_from_str "\dEFHZbng".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM583.


Module TM584.
Definition tm := TM_from_str "1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LB_1RC1LB_1LA0RD_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1R[1LF_1RZ1LH_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0LX1Ln_1Rb0Rd_1LX1Rb_1RZ0R\_1LX0R[_1RZ1RZ_1LH1R[_1LH1LH_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RS_1Ln1Rb_---1RS_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LP_1LP0LN_0LP0LP_1R[1LN_1LP1LP_0RR0R[_0RT1RZ_1RR1R[_1RT1LP_0LP0LN_1Rb0LP_1LP1LN_1RZ1LP_1RZ0RY_1RZ0R[_1LP1RY_1LP1R[_0LF1Ln_0LH0Rd_1LF1Rb_1LH0R\_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LN1Rd_1Lg0LP_1LN1R\_---0RT_1Ln1Rb_---1RT_1LE0LP_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LP_---0Lg_---0LN_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_---0LI_1LH1LC".
Definition tm2 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_1RJ0LI_1LH1LC_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "\dEFHZbng".
Definition mp' := mp_from_str "\dENPZbng".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM584.


Module TM585.
Definition tm := TM_from_str "1RB1LB_1RC1LB_1LA0RD_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_1RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LP_1LP0LN_0LP0LP_1R[1LN_1LP1LP_0RR0R[_0RT1RZ_1RR1R[_1RT1LP_0LP0LN_1Rb0LP_1LP1LN_1RZ1LP_1RZ0RY_1RZ0R[_1LP1RY_1LP1R[_0LF1Ln_0LH0Rd_1LF1Rb_1LH0R\_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LN1Rd_1Lg0LP_1LN1R\_---0RT_1Ln1Rb_---1RT_1LE0LP_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LP_---0Lg_---0LN_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1LH1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_0LH0Rd_1LH1Rb_1LH0R\_1LX0R[_1RZ1RZ_1LH1R[_1LH1LH_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm1 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_---0LI_1LH1LC".
Definition tm2 := TM'_from_str "1RB1RA_1LC0LE_1LE0LD_1RG0LE_1RF1LE_0RB0RA_1LH1RG_1RJ0LI_1LH1LC_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "\dENPZbng".
Definition mp' := mp_from_str "\dEFHZbng".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM585.


Module TM586.
Definition tm := TM_from_str "1RB1LC_1RC---_0LD1RF_0LE1LE_0LA1LE_0RC0RB".
Definition tm' := TM_from_str "1RB1LC_1RC---_0LD1RF_0LE1RD_0LA1LE_0RC0RB".
Definition tm0 := TM'_from_str "0RJ1Le_0RL0RK_1RJ1Lf_1RL1RK_0Lh0LV_---0LX_1Rl1LV_---1LX_0RR---_0RT---_1RR---_1RT---_0Lf---_1RS---_1Lf---_1RK---_0LE0Rj_0LG0Rl_0Lf1Rj_0Lh1Rl_0L]0Lf_0L_1RR_1L]1Rj_1L_---_0Lh1Rl_0LG1LG_0LV1LV_0Lh1Lh_0Le0Lf_0Lg0Lh_1Le1Lf_1Lg1Lh_0RT1Rl_0L_1LG_1RT1LV_1RR1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Le0LG_0RS---_1Le0Rl_0RK---".
Definition tm0' := TM'_from_str "0RJ1Le_0RL0RK_1RJ1Lf_1RL1RK_0Lh0LV_---0LX_1Rl1LV_---1LX_0RR---_0RT---_1RR---_1RT---_0Lf---_1RS---_1Lf---_1RK---_0LE0Rj_0LG0Rl_0Lf1Rj_0Lh1Rl_0L]0Lf_0L_1RR_1L]1Rj_1L_---_0Lh0RZ_0LG0R\_0LV1RZ_0Lh1R\_0Le0Lf_0Lg0Lh_1Le1Lf_1Lg1R\_0RT1Rl_0L_1LG_1RT1LV_1RR1Lh_0LE0Lf_0LG0Lh_1LE1Lf_1LG1Lh_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Le0LG_0RS---_1Le0Rl_0RK---".
Definition tm1 := TM'_from_str "0LB1RJ_0LC0LF_1RH1LD_0LE1RG_1LK1LB_1LC1LF_0LC0RH_1RA1RI_1RG---_0RA0RI_0LL0LB_0LF0LD".
Definition tm2 := TM'_from_str "0LB1RJ_0LC0LF_1RH1LD_0LE1RG_1LK1LB_1LC1LF_0LC0RH_1RA1RI_1RG1RM_0RA0RI_0LL0LB_0LF0LD_1RM1RM".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "SfGV_hRlKjeE".
Definition mp' := mp_from_str "SfGV_hRlKjeE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 52 52.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM586.


Module TM587.
Definition tm := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1RB_0RF0LA_0LB1LF".
Definition tm' := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_0RE1LA_0LB0LA".
Definition tm0 := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Lf_1RS---_0RT0Lf_0R[0Lh_0RJ1Lf_0RT1Lh_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lh_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_---0RL_1Lh1RJ_---1RL_0LF1RY_0LH0LG_1LF1RR_1LH1LG_0Ri0R[_0Rk---_1Ri0Lh_1Rk---_0RT0LE_0LO0LG_0RJ1LE_1LO1LG_0RY0RJ_0LO1LO_1RY1Lf_0LG1Lp_0LM0Ln_0LO0Lp_1LM1Ln_1LO1Lp".
Definition tm0' := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Ln_1RS---_0RT0Ln_0R[0Lp_0RJ1Ln_0RT1Lp_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lp_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_1LP0RL_1Lp1RJ_---1RL_0Lf1RY_0Lh0LG_1Lf1RR_1Lh1LG_0Ra0RT_0Rc---_1Ra1Lp_1Rc---_0Ra0LF_0LP0LH_0RT1LF_1LP1LH_0RY0R[_0LO---_1RY0Lp_0LG---_0LM0LE_0LO0LG_1LM1LE_1LO1LG".
Definition tm1 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG---_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG1RL_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "SYT[hGNOfJR".
Definition mp' := mp_from_str "SYT[pGNOnJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 56 56.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM587.


Module TM588.
Definition tm := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_0RE1LA_0LB0LA".
Definition tm' := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1RB_0LB0RF_0LA1LF".
Definition tm0 := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Ln_1RS---_0RT0Ln_0R[0Lp_0RJ1Ln_0RT1Lp_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lp_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_1LP0RL_1Lp1RJ_---1RL_0Lf1RY_0Lh0LG_1Lf1RR_1Lh1LG_0Ra0RT_0Rc---_1Ra1Lp_1Rc---_0Ra0LF_0LP0LH_0RT1LF_1LP1LH_0RY0R[_0LO---_1RY0Lp_0LG---_0LM0LE_0LO0LG_1LM1LE_1LO1LG".
Definition tm0' := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Lf_1RS---_0RT0Lf_0R[0Lh_0RJ1Lf_0RT1Lh_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lh_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_---0RL_1Lh1RJ_---1RL_0LF1RY_0LH0LG_1LF1RR_1LH1LG_0RY0Ri_0LO0Rk_1RY1Ri_0LG1Rk_0LM0LN_0LO0LG_1LM1LN_1LO1LG_0R[1LN_---1LG_0Lh---_---1Lp_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp".
Definition tm1 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG---_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG1RL_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "SYT[pGNOnJR".
Definition mp' := mp_from_str "SYT[hGNOfJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 56 56.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM588.


Module TM589.
Definition tm := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1RB_0LB0RF_0LA1LF".
Definition tm' := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1LF_0LB0LA_0RF1RB".
Definition tm0 := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Lf_1RS---_0RT0Lf_0R[0Lh_0RJ1Lf_0RT1Lh_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lh_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_---0RL_1Lh1RJ_---1RL_0LF1RY_0LH0LG_1LF1RR_1LH1LG_0RY0Ri_0LO0Rk_1RY1Ri_0LG1Rk_0LM0LN_0LO0LG_1LM1LN_1LO1LG_0R[1LN_---1LG_0Lh---_---1Lp_0LE0Ln_0LG0Lp_1LE1Ln_1LG1Lp".
Definition tm0' := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Lf_1RS---_0RT0Lf_0R[0Lh_0RJ1Lf_0RT1Lh_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lh_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_---1LN_1Lh1RJ_------_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RY0R[_0LO---_1RY0Lh_0LG---_0LM0LE_0LO0LG_1LM1LE_1LO1LG_0Ri0RJ_0Rk0RL_1Ri1RJ_1Rk1RL_0Ri1RY_0RS0LG_0RJ1RR_1LN1LG".
Definition tm1 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG---_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG1RL_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "SYT[hGNOfJR".
Definition mp' := mp_from_str "SYT[hGNOfJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 56 56.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM589.


Module TM590.
Definition tm := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1LF_0LB0LA_0RF1RB".
Definition tm' := TM_from_str "1RB---_0RC1RB_1LD1RE_1LE---_0RB1LF_0LE0LD".
Definition tm0 := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Lf_1RS---_0RT0Lf_0R[0Lh_0RJ1Lf_0RT1Lh_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lh_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_---1LN_1Lh1RJ_------_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp_0RY0R[_0LO---_1RY0Lh_0LG---_0LM0LE_0LO0LG_1LM1LE_1LO1LG_0Ri0RJ_0Rk0RL_1Ri1RJ_1Rk1RL_0Ri1RY_0RS0LG_0RJ1RR_1LN1LG".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1Lp---_1RS---_1Rb---_1RL---_0RQ0RJ_0RS0RL_1RQ1RJ_1RS1RL_0Lh1Lp_0RK1RS_1Lh1Rb_1Lf1RL_0RL0Rb_---0Rd_1Lp1Rb_---1Rd_0L^1RQ_0L`0L__1L^1RJ_1L`1L__0RJ---_1Lg---_1RJ---_1L_---_0Lf---_0Lh---_1Lf---_1Lh---_0RI0Rb_0RK1Lf_1RI1Ln_1RK---_0RL0Ln_0RS0Lp_0Rb1Ln_0RL1Lp_0RQ0RS_0Lg---_1RQ0Lp_0L_---_0Le0L]_0Lg0L__1Le1L]_1Lg1L_".
Definition tm1 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG---_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG1RL_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "SYT[hGNOfJR".
Definition mp' := mp_from_str "KQLSp_fgnbJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 56 56.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM590.


Module TM591.
Definition tm := TM_from_str "1RB---_0RC1RB_1LD1RE_1LE---_0RB1LF_0LE0LD".
Definition tm' := TM_from_str "1LB0LA_0RC1LE_0RD1RC_1LA1RB_0LB1LF_0RA---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_1Lp---_1RS---_1Rb---_1RL---_0RQ0RJ_0RS0RL_1RQ1RJ_1RS1RL_0Lh1Lp_0RK1RS_1Lh1Rb_1Lf1RL_0RL0Rb_---0Rd_1Lp1Rb_---1Rd_0L^1RQ_0L`0L__1L^1RJ_1L`1L__0RJ---_1Lg---_1RJ---_1L_---_0Lf---_0Lh---_1Lf---_1Lh---_0RI0Rb_0RK1Lf_1RI1Ln_1RK---_0RL0Ln_0RS0Lp_0Rb1Ln_0RL1Lp_0RQ0RS_0Lg---_1RQ0Lp_0L_---_0Le0L]_0Lg0L__1Le1L]_1Lg1L_".
Definition tm0' := TM'_from_str "0RR0R[_1LO0LN_1RR0Lh_1Lp0LE_0LN0LE_0LP0LG_1LN1LE_1LP1LG_0RQ0RJ_0RS1LN_1RQ1Lf_1RS---_0RT0Lf_0R[0Lh_0RJ1Lf_0RT1Lh_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0LP1Lh_0RS1R[_1LP1RJ_1LN1RT_0RT0RJ_1LN0RL_1Lh1RJ_1LE1RL_0LF1RY_0LH0Lp_1LF1RR_1LH1Lp_0RY0R[_0LO---_1RY0Lh_0Lp---_0LM0Ln_0LO0Lp_1LM1Ln_1LO1Lp_0RA---_0RC---_1RA---_1RC---_0R[---_0LN---_0RT---_1LN---".
Definition tm1 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG---_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC".
Definition tm2 := TM'_from_str "1RB1RK_0RC0RJ_1RD1RC_1LE1RJ_1LH1LF_1LG1RL_0RD0LE_0RJ1LI_0LH0LF_0RA1LG_0RD0RC_1RL1RL".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "KQLSp_fgnbJ".
Definition mp' := mp_from_str "SYT[hpNOfJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 56 56.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM591.


Module TM592.
Definition tm := TM_from_str "1LB---_0RC1LD_0RE1LD_0LC0LA_0RF1RE_1LA1RC".
Definition tm' := TM_from_str "1LB---_0RB1LC_0LD0LA_0RE1LC_0RF1RE_1LA1RD".
Definition tm0 := TM'_from_str "0RR---_1LW---_1L^---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RR_0RS1LN_1RQ1L^_1RS---_0Ri0L^_0LW0L`_0Rb1L^_1LW1L`_0Ra0RR_0Rc1LN_1Ra1L^_1Rc---_1LW0L^_0Rk0L`_0RR1L^_0Rd1L`_0Ri0LW_0LW---_1Ri0L`_0LG---_0LU0LE_0LW0LG_1LU1LE_1LW1LG_0Ri0Rb_0Rk0Rd_1Ri1Rb_1Rk1Rd_0LP1L`_0Rc1Rk_1LP1RR_1LN1Rd_1LW0RR_---0RT_1L`1RR_---1RT_0LF1Ri_0LH0LG_1LF1Rb_1LH1LG".
Definition tm0' := TM'_from_str "0RZ---_1L_---_1LV---_1LG---_0LN---_0LP---_1LN---_1LP---_0RI0RZ_0RK1LN_1RI1LV_1RK---_0RI0LV_0L_0LX_0RZ1LV_1L_1LX_0Ri0L__0L_---_1Ri0LX_0LG---_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Ra0RZ_0Rc1LN_1Ra1LV_1Rc---_1L_0LV_0Rk0LX_0RZ1LV_0Rd1LX_0Ri0Rb_0Rk0Rd_1Ri1Rb_1Rk1Rd_0LP1LX_0Rc1Rk_1LP1RZ_1LN1Rd_1L_0RZ_---0R\_1LX1RZ_---1R\_0LF1Ri_0LH0LG_1LF1Rb_1LH1LG".
Definition tm1 := TM'_from_str "0RB0RJ_1LC1RH_1LD1LF_0RH1LE_0LD0LF_1LG---_0LD0LC_0RI1LG_1RK1RA_1RB1RJ_1LD0RH".
Definition tm2 := TM'_from_str "0RB0RJ_1LC1RH_1LD1LF_0RH1LE_0LD0LF_1LG1RL_0LD0LC_0RI1LG_1RK1RA_1RB1RJ_1LD0RH_1RL1RL".
Definition l0 := [0;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "bk`W^GNRcdi".
Definition mp' := mp_from_str "bkX_VGNZcdi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 62 62.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM592.


Module TM593.
Definition tm := TM_from_str "1LB---_0RB1LC_0LD0LA_0RE1LC_0RF1RE_1LA1RD".
Definition tm' := TM_from_str "1LB---_0LC1LF_0RD1LF_0RE1RD_1LA1RC_0LC0LA".
Definition tm0 := TM'_from_str "0RZ---_1L_---_1LV---_1LG---_0LN---_0LP---_1LN---_1LP---_0RI0RZ_0RK1LN_1RI1LV_1RK---_0RI0LV_0L_0LX_0RZ1LV_1L_1LX_0Ri0L__0L_---_1Ri0LX_0LG---_0L]0LE_0L_0LG_1L]1LE_1L_1LG_0Ra0RZ_0Rc1LN_1Ra1LV_1Rc---_1L_0LV_0Rk0LX_0RZ1LV_0Rd1LX_0Ri0Rb_0Rk0Rd_1Ri1Rb_1Rk1Rd_0LP1LX_0Rc1Rk_1LP1RZ_1LN1Rd_1L_0RZ_---0R\_1LX1RZ_---1R\_0LF1Ri_0LH0LG_1LF1Rb_1LH1LG".
Definition tm0' := TM'_from_str "0RR---_1LW---_1Ln---_1LG---_0LN---_0LP---_1LN---_1LP---_0Ra0RR_0LW1LN_1Ra1Ln_0LG---_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RY0RR_0R[1LN_1RY1Ln_1R[---_1LW0Ln_0Rc0Lp_0RR1Ln_0R\1Lp_0Ra0RZ_0Rc0R\_1Ra1RZ_1Rc1R\_0LP1Lp_0R[1Rc_1LP1RR_1LN1R\_1LW0RR_---0RT_1Lp1RR_---1RT_0LF1Ra_0LH0LG_1LF1RZ_1LH1LG_0Ra0LW_0LW---_1Ra0Lp_0LG---_0LU0LE_0LW0LG_1LU1LE_1LW1LG".
Definition tm1 := TM'_from_str "0RB0RJ_1LC1RH_1LD1LF_0RH1LE_0LD0LF_1LG---_0LD0LC_0RI1LG_1RK1RA_1RB1RJ_1LD0RH".
Definition tm2 := TM'_from_str "0RB0RJ_1LC1RH_1LD1LF_0RH1LE_0LD0LF_1LG1RL_0LD0LC_0RI1LG_1RK1RA_1RB1RJ_1LD0RH_1RL1RL".
Definition l0 := [0;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "bkX_VGNZcdi".
Definition mp' := mp_from_str "ZcpWnGNR[\a".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 62 62.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM593.


Module TM594.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LC---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LC---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0L`_1RT0RL_1LX---_1RL0Rc_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0L_1L]_0LX1RT_1L_1LX_1LX1RL_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_0LV1RT_---1Rj_1LV1RL_---1RB_0Rj---_0L`---_0L_---_0LX---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0L`_1RT0RL_1LX---_1RL0Rc_0RR0L`_0RT0RL_1RR0LX_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_0LV1RT_---1Rj_1LV1RL_---1RB_0Rj---_0L`---_0L_---_0LX---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1RB1RI_0LC---_0RI1LD_0RE1LG_1RF1RE_1LG1LH_0RF0LG_1LC1LH_0RE0RA".
Definition tm2 := TM'_from_str "1RB1RI_0LC1RJ_0RI1LD_0RE1LG_1RF1RE_1LG1LH_0RF0LG_1LC1LH_0RE0RA_1RJ1RJ".
Definition l0 := [0;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "cj`_LT]XB".
Definition mp' := mp_from_str "cj`_LT]XB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 70 70.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM594.


Module TM595.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LB---".
Definition tm' := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RT_1RT0RL_1LX---_1RL0Rc_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0L_1L]_0LX1RT_1L_1LX_1LX1RL_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_1L]1RT_---1Rj_1LX1RL_---1RB_0RL---_0RT---_1L]---_1RT---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1L]1RT_---1RJ_1LX1Rl_---1Rb_0RR---_0RT---_1RR---_1RT---_0L_---_0LX---_1L_---_1LX---_0RA0Rb_0Rl1L`_1RA1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0Ra0Rj_0Rc0RT_1Ra1Rj_1Rc0L]_0RT0L]_0RJ0L__0Rl1L]_0Rb1L__0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1L]0RT_1RT0Rl_1LX---_1Rl0RC_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_1L]_0LX1RT_1L_1LX_1LX1Rl".
Definition tm1 := TM'_from_str "1RB1RI_0RC---_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA".
Definition tm2 := TM'_from_str "1RB1RI_0RC1RJ_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA_1RJ1RJ".
Definition l0 := [0;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "cjT]X`_LB".
Definition mp' := mp_from_str "CJT]X`_lb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 70 70.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM595.


Module TM596.
Definition tm := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LD---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_1L]1RT_---1RJ_1LX1Rl_---1Rb_0RR---_0RT---_1RR---_1RT---_0L_---_0LX---_1L_---_1LX---_0RA0Rb_0Rl1L`_1RA1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0Ra0Rj_0Rc0RT_1Ra1Rj_1Rc0L]_0RT0L]_0RJ0L__0Rl1L]_0Rb1L__0Rj0RA_0Rl0RC_1Rj1RA_1Rl1RC_1L]0RT_1RT0Rl_1LX---_1Rl0RC_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_1L]_0LX1RT_1L_1LX_1LX1Rl".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RT_1RT0RL_1LX---_1RL0Rc_0RR0RT_0RT0RL_1RR0L]_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_0L]1RT_---1Rj_1L]1RL_---1RB_0RJ---_0RT---_1RJ---_0L]---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1RB1RI_0RC---_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA".
Definition tm2 := TM'_from_str "1RB1RI_0RC1RJ_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA_1RJ1RJ".
Definition l0 := [0;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "CJT]X`_lb".
Definition mp' := mp_from_str "cjT]X`_LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 70 70.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM596.


Module TM597.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LD---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RC---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RT_1RT0RL_1LX---_1RL0Rc_0RR0RT_0RT0RL_1RR0L]_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_0L]1RT_---1Rj_1L]1RL_---1RB_0RJ---_0RT---_1RJ---_0L]---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RT_1RT0RL_1LX---_1RL0Rc_0RR0RT_0RT0RL_1RR1RT_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_1L]1RT_---1Rj_1LX1RL_---1RB_0RR---_0RT---_1RR---_1RT---_0L_---_0LX---_1L_---_1LX---".
Definition tm1 := TM'_from_str "1RB1RI_0RC---_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA".
Definition tm2 := TM'_from_str "1RB1RI_0RC1RJ_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA_1RJ1RJ".
Definition l0 := [0;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "cjT]X`_LB".
Definition mp' := mp_from_str "cjT]X`_LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 70 70.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM597.


Module TM598.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RC---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_0RF1RA_0LA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RT_1RT0RL_1LX---_1RL0Rc_0RR0RT_0RT0RL_1RR1RT_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_1L]1RT_---1Rj_1LX1RL_---1RB_0RR---_0RT---_1RR---_1RT---_0L_---_0LX---_1L_---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RT_1RT0RL_1LX---_1RL0Rc_0RR0RT_0RT0RL_1RR1RT_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Ri0L__0RL1L]_0RB1L__0Ri0RB_0Rk0RD_1Ri1RB_1Rk1RD_1L]1RT_---1Ri_1LX1RL_---1RB_0RT---_0Ri---_1RT---_1Ri---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1RB1RI_0RC---_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA".
Definition tm2 := TM'_from_str "1RB1RI_0RC1RJ_1LD1LE_0RC0LD_1LF1LE_0RI1LG_0RH1LD_1RC1RH_0RH0RA_1RJ1RJ".
Definition l0 := [0;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "cjT]X`_LB".
Definition mp' := mp_from_str "ciT]X`_LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 70 70.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM598.


Module TM599.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1RA---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RA---".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RD_1RT0RL_1LX---_1RL0Rc_0RR0RJ_0RT0RL_1RR1RJ_1RT1RL_0L_1L]_0LX1RT_1L_1LX_1LX1RL_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_1RL1RT_---1Rj_1Rc1RL_---1RB_0RB---_0RD---_1RB---_1RD---_1RT---_1Rj---_1RL---_1RB---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RD_1RT0RL_1LX---_1RL0Rc_0RR0RD_0RT0RL_1RR1RD_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_1RL1RT_---1Rj_1Rc1RL_---1RB_0RB---_0RD---_1RB---_1RD---_1RT---_1Rj---_1RL---_1RB---".
Definition tm1 := TM'_from_str "1RB1RJ_0RC---_1RD1RA_1RE1RD_1LF1LG_0RE0LF_1LH1LG_0RJ1LI_0RD1LF_0RD0RA".
Definition tm2 := TM'_from_str "1RB1RJ_0RC1RK_1RD1RA_1RE1RD_1LF1LG_0RE0LF_1LH1LG_0RJ1LI_0RD1LF_0RD0RA_1RK1RK".
Definition l0 := [0;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "cjDLT]X`_B".
Definition mp' := mp_from_str "cjDLT]X`_B".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 70 70.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM599.


