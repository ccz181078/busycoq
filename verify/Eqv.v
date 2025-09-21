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
Definition tm := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RE_0LF---_1RB1LA".
Definition tm' := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RF_0LE1LA_0LA---".
Definition tm0 := TM'_from_str "0RJ0RT_0RL1R[_1RJ1RT_1RL0LE_1R[0LE_1RL0LG_1RK1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1LF1RT_1RR0LE_1Ra1RD_1RB1LE_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0Lo0R[_0RT0RL_1Lo0RK_---1R[_1RK0Ra_---0Rc_1LF1Ra_---1Rc_0Lf1R[_0Lh---_1Lf1RK_1Lh---_0RT---_1RL---_1RT---_0LG---_0Lm---_0Lo---_1Lm---_1Lo---_0RJ0RD_0RL1RK_1RJ1RD_1RL1LE_1R[0LF_1RL0LH_1RK1LF_0LE1LH".
Definition tm0' := TM'_from_str "0RJ0RT_0RL1R[_1RJ1RT_1RL0LE_1R[0LE_1RL0LG_1RK1LE_0LE1LG_0RR0RB_0RT0RD_1RR1RB_1RT1RD_1LF1RT_1RR0LE_1Ri1RD_1RB1LE_0RY0RI_0R[0RK_1RY1RI_1R[1RK_0Lg0R[_0RT0RL_1Lg0RK_---1R[_1Le0Ri_0LE0Rk_1LF1Ri_1LG1Rk_0Lf1R[_0Lh---_1Lf1RK_1Lh---_0Le0RD_1RL1RK_0LF1RD_0LG1LE_0Le0LF_0Lg0LH_1Le1LF_1Lg1LH_0RT---_1R[---_1RT---_0LE---_0LE---_0LG---_1LE---_1LG---".
Definition tm1 := TM'_from_str "1RB1RJ_1RC1RG_1LD1RK_1RA0LE_1RG1LF_1RC0LF_1RH1RI_0RC0RG_0RA1RC_1RA0LF_0RB---".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1RG_1LD1RK_1RA0LE_1RG1LF_1RC0LF_1RH1RI_0RC0RG_0RA1RC_1RA0LF_0RB1RL_1RL1RL".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "LT[FGEKRBDa".
Definition mp' := mp_from_str "LT[FGEKRBDi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM1.


Module TM2.
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
End TM2.


Module TM3.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RC---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---".
Definition tm0 := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lp_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1LF0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ0Ra_0Lg---_0LW1Ra_1LF---_0Le0Ln_0Lg0Lp_1Le1Ln_1Lg1Lp_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RQ---_0RS---_1RQ---_1RS---_0Lg---_0RK---_1Lg---_1LF---".
Definition tm0' := TM'_from_str "0RJ0Lg_0RL0RK_1RJ0Lo_1RL1RK_1LM0LU_1RQ0LW_1Ra1LU_1RI1LW_0RQ0RI_0RS0RK_1RQ1RI_1RS1RK_0Lg1LF_0RK0RQ_1Lg0Ra_1LF0RI_1LF0Ra_1LF0Rc_1LM1Ra_---1Rc_0L^1RQ_0L`0Lg_1L^1RI_1L`1Lg_1RQ1RQ_0Lg---_0LW0LW_1LF---_0Le0Lm_0Lg0Lo_1Le1Lm_1Lg1Lo_0RK1LF_1L^0RQ_1RK1LM_1RI1RQ_0LF0LM_0LH0LO_1LF1LM_1LH1LO_0RK---_1L^---_1RK---_1RI---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB---".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1RI_0LE0LJ_1LB1LF_0LE1LB_0RH1LB_1RA1RI_0RA0RI_1LB1RK_1RK1RK".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QFW^gMaKIp".
Definition mp' := mp_from_str "QFW^gMaKIo".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM3.


Module TM4.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LC0RD_1RA---_0RF0LA_0LA1RC".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0LE---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RR_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1LN0Le_1RB0Lg_0Rc1Le_---1Lg_0LU0RY_0RB0R[_1LN1RY_1RB1R[_0LU1LN_0LW---_1LU0Rc_1LW---_0RB---_0RD---_1RB---_1RD---_0Lg---_1Ri---_1Lg---_0Lg---_0Ri1RB_0Rk0Ri_1Ri0Lg_1Rk1Ri_0LN0LE_0RB0LG_1LN1LE_0R[1LG_1RB0RR_0Ri0RT_0Lg1RR_1Ri1RT_0LE1LN_0LG1RB_1LE0Rc_1LG---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0RQ_1RQ0Lg_1RS1RQ_0LN0LE_0RB0LG_1LN1LE_0Ri1LG_1RB---_0LN---_0Lg---_1RB---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgEciR[".
Definition mp' := mp_from_str "BNgEcQYi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM4.


Module TM5.
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
End TM5.


Module TM6.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LC0RD_1RA---_0RF0LE_0LA1RC".
Definition tm' := TM_from_str "1LB0RF_1RC0LF_0LA1RD_0LD0RE_1RA---_0RC0LF".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RR_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1LN0Le_1RB0Lg_0Rc1Le_---1Lg_0LU0RY_0RB0R[_1LN1RY_1RB1R[_0LU1LN_0LW---_1LU0Rc_1LW---_0RB---_0RD---_1RB---_1RD---_0Lg---_1Ri---_1Lg---_0Lg---_0Ri1RB_0Rk0LN_1Ri0Lg_1Rk0Le_0LN0Le_0RB0Lg_1LN1Le_0R[1Lg_1RB0RR_0Ri0RT_0Lg1RR_1Ri1RT_0LE1LN_0LG1RB_1LE0Rc_1LG---".
Definition tm0' := TM'_from_str "0R\0Ri_1LN0Rk_1R\1Ri_1Lm1Rk_0LN1RB_0LP0LN_1LN0RZ_1LP1LN_0RR1RB_0RT0LN_1RR0Lo_1RT0Lm_1RB0Lm_1RB0Lo_0RZ1Lm_1Rc1Lo_1RB0RZ_0RQ0R\_0Lo1RZ_1RQ1R\_0LE1LN_0LG1RB_1LE0Rk_1LG---_0L]0Ra_0RB0Rc_1LN1Ra_1RB1Rc_0L]1LN_0L_---_1L]0Rk_1L_---_0RB---_0RD---_1RB---_1RD---_0Lo---_1RQ---_1Lo---_0Lo---_0RQ1RB_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0RB0Lo_1LN1Lm_0Rc1Lo".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgeciR[".
Definition mp' := mp_from_str "BNomkQZc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM6.


Module TM7.
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
End TM7.


Module TM8.
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
End TM8.


Module TM9.
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
End TM9.


Module TM10.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC0LF_0RC---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RF_1LF0RF_0RC0LA".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Lm1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT---_1RB0Le_1RB0Lg_0RY1Le_1Rb1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rb_0RD0Rd_1RB1Rb_1RD1Rd_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS---_1RQ0Lg_1RS---_0LN0Lm_0RB0Lo_1LN1Lm_0Rb1Lo_0RQ---_0RS---_1RQ---_1RS---_0LN---_0RB---_1LN---_0Rb---".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT---_---0Lm_1Rb0Lo_---1Lm_1Rj1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG0RS_1LE0Rk_1LG---_0Rb0Rj_0Rd0Rl_1Rb1Rj_1Rd1Rl_0LG0Lo_1RQ---_1LG1RY_0Lo---_0RY0Ri_1LN0Rk_1RY1Ri_---1Rk_0Ln1Rb_0Lp0LN_1Ln0RY_1Lp1LN_0RQ1Rb_0RS---_1RQ0Lo_1RS---_0LN0LE_0Rb0LG_1LN1LE_0Rj1LG".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0LC1RG".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RJ_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0LC1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgmcQYbS".
Definition mp' := mp_from_str "bNoEkQYjS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM10.


Module TM11.
Definition tm := TM_from_str "1RB0LD_0LC1RE_1LA0RD_0RB0LC_0LE0RF_1RC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LC---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Rb1L]_1Rk1L__1RR0Rb_0RI0Rd_0L_1Rb_1RI1Rd_0LU1LF_0LW1RR_1LU0R[_1LW---_0Rd0RY_1LF0R[_1Rd1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Rb_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rk1LW_0Le0Ri_0RR0Rk_1LF1Ri_1RR1Rk_0Le1LF_0Lg---_1Le0R[_1Lg---_0RR---_0RT---_1RR---_1RT---_0L_---_1RI---_1L_---_0L_---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1RR_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0LF_1RI---_1L_1LF_0L_---_1Rj---_1RR---_1L_---_0L_---_0LV---_0LX---_1LV---_1LX---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Ibk".
Definition mp' := mp_from_str "RF_U[Iaj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM11.


Module TM12.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_1LB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LE---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0LW_1RI---_1L_1LW_0L_---_1LF---_0Ri---_0Ra---_1Ri---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0L__1RI---_1L_1L__0L_---_1LF---_1LF---_1LU---_1LU---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB1RA_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_U[Iai".
Definition mp' := mp_from_str "RF_U[Iai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM12.


Module TM13.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_1LB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_0LE---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Ri1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0LW_1RI---_1L_1LW_0L_---_1LF---_0Ri---_0Ra---_1Ri---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Ri1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0L__1RI---_1L_1L__0L_---_1LF---_1LF---_1L]---_1L]---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB0LD_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_][Iai".
Definition mp' := mp_from_str "RF_][Iai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM13.


Module TM14.
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
End TM14.


Module TM15.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_1LC---_1RA0LD".
Definition tm' := TM_from_str "1LB---_0RC0LB_1RE0RD_1RA1RC_1RF0LD_1LB1LF".
Definition tm0 := TM'_from_str "0RY0RR_0Rl1LP_1RY1LO_1LM1LH_0LN0LF_0LP0LH_1LN1LF_1LP1LH_0RQ0Rj_0RS0RD_1RQ1Rj_1RS0LM_0RD0LM_0Ra0LO_0Rl1LM_0RR1LO_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_1LM0Rl_1RD0Rl_1LH---_1Rl0R[_0Ra0RR_0Rc0RT_1Ra1RR_1Rc1RT_1RD1RD_---1Ra_1Rl1Rl_---1RR_0Rl---_0RR---_1Rl---_1RR---_0LV---_0LX---_1LV---_1LX---_0RB0Rl_0RD0Rl_1RB1Rl_1RD1Rl_0LO0L]_0LH0L__1LO1L]_1LH1L_".
Definition tm0' := TM'_from_str "0RY---_0Rd---_1RY---_1LM---_0LN---_0LP---_1LN---_1LP---_0RQ0Rb_0RS0Rl_1RQ1Rb_1RS0LM_0Rl0LM_0RB0LO_0Rd1LM_0RR1LO_0Rb0RY_0Rd0R[_1Rb1RY_1Rd1R[_1LM0Rd_1Rl0Rd_1Lp---_1Rd0R[_0RB0RR_0RD0RT_1RB1RR_1RD1RT_0LO1Rl_---1RB_1LO1Rd_---1RR_0Rj0Rd_0Rl0Rd_1Rj1LM_1Rl1Rd_0LO0L]_0Lp0L__1LO1L]_1Lp1L__0RY0RR_0Rd1LP_1RY1LO_1LM1Lp_0LN0Ln_0LP0Lp_1LN1Ln_1LP1Lp".
Definition tm1 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF---".
Definition tm2 := TM'_from_str "1LB1LC_0RA0LB_1LD1LC_0RG1LE_0RF1LB_1RA1RF_0RF0RH_1RI1RG_0RF1RJ_1RJ1RJ".
Definition l0 := [0;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "DMHPOlR[a".
Definition mp' := mp_from_str "lMpPOdR[B".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM15.


Module TM16.
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
End TM16.


Module TM17.
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
End TM17.


Module TM18.
Definition tm := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LE_0LB0RF_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ1Le_0RL---_1RJ1Lf_1RL---_0LX0LV_1RJ0LX_1LX1LV_1Ri1LX_0R\0RZ_1L_0R\_1R\1RZ_---1R\_0LF1L__0LH0RJ_1LF0R\_1LH0Ri_0LM---_0LO---_1L_---_0RJ---_0L]---_0L_---_1L]---_1L_---_0LF1LF_0RJ0Ri_1L_0R\_1RJ1Ri_0Le0Lf_0Lg0Lh_1Le1Lf_1Lg1Lh_1RJ0Ri_0RJ0Rk_0LX1Ri_1RJ1Rk_0LM1L__0LO0RJ_1LM0R\_1LO0Ri_0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0LX1L__1RJ0RJ_1LX0R\_1Ri0Ri".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0Rd_1RA0RA_0RC0Rb_1Lg0Rd_1RC1Rb_---1Rd_0LV1Lg_0LX0RJ_1LV0Rd_1LX0RA_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1Rd1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0Rd_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0Rd_1LO0RA".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "iJ_eMFfO\X".
Definition mp' := mp_from_str "AJgmMVnOd`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM18.


Module TM19.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RA1LD_0LE---_0LF1LF_0LB0RA".
Definition tm0 := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0Rd_1RA0RA_0RC0Rb_1Lg0Rd_1RC1Rb_---1Rd_0LV1Lg_0LX0RJ_1LV0Rd_1LX0RA_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1Rd1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0Rd_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0Rd_1LO0RA".
Definition tm0' := TM'_from_str "0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0L`1Lg_1RJ0RJ_1L`0RC_1RA0RA_0RC0RA_1Lg0RC_1RC1RA_---1RC_0LV1Lg_0LX0RJ_1LV0RC_1LX0RA_0RB1Lm_0RD---_1RB1Ln_1RD---_---0L^_1RJ0L`_1RC1L^_1RA1L`_0LM---_0LO---_1Lg---_0RJ---_0Le---_0Lg---_1Le---_1Lg---_0LV1LV_0RJ0RA_1Lg0RC_1RJ1RA_0Lm0Ln_0Lo0Lp_1Lm1Ln_1Lo1Lp_1RJ0RA_0RJ0RC_0L`1RA_1RJ1RC_0LM1Lg_0LO0RJ_1LM0RC_1LO0RA".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "AJgmMVnOd`".
Definition mp' := mp_from_str "AJgmMVnOC`".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM19.


Module TM20.
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
End TM20.


Module TM21.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1LB_0LA1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LF_1LC1RF_0RA1RB".
Definition tm0 := TM'_from_str "1Rj0RY_---0R[_1Lm1RY_---1R[_0LN0LW_0LP0LW_1LN0Rj_1LP1LW_0Rc---_0LW---_1Rc---_0Lm---_0LU---_0LW---_1LU---_1LW---_0RZ1Rj_0R\0LW_1RZ1Lm_1R\0Lm_---0Lm_---0Lo_1Rj1Lm_---1Lo_0Ra1Rj_0Rc---_1Ra1Lm_1Rc---_0LN0LN_0RC0LP_1LN1LN_0RL1LP_0LW0Rj_0Ra0Rl_---1Rj_1Ra1Rl_0LE1Lm_0LG0Lm_1LE1RY_1LG---_0RA0RJ_0RC0RL_1RA1RJ_1RC1RL_0LW0Lm_0Ra---_1LW1Lm_1Rj---".
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
End TM21.


Module TM22.
Definition tm := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC1RF_0LF---_0LB1LB".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC0RD_0LF---_0LB1LB".
Definition tm0 := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1Lo0Lf_1RR0Lh_0R[1Lf_1Rj1Lh_1RR0RY_0RR0R[_0Lh1RY_1RR1R[_0LU1Lo_0LW0RR_1LU0R[_1LW0Rj_0R[0RY_1Lo0R[_1R[1RY_---1R[_0LF1Lo_0LH0RR_1LF0R[_1LH0Rj_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0Lh1Lo_1RR0RR_1Lh0R[_1Rj0Rj_0LU---_0LW---_1Lo---_0RR---_0Lm---_0Lo---_1Lm---_1Lo---_0LF1LF_0RR0Rj_1Lo0R[_1RR1Rj_0LM0LN_0LO0LP_1LM1LN_1LO1LP".
Definition tm0' := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1Lo0Lf_1RR0Lh_0R[1Lf_1RY1Lh_1RR0RY_0RR0R[_0Lh1RY_1RR1R[_0LU1Lo_0LW0RR_1LU0R[_1LW0RY_0R[0RY_1Lo0R[_1R[1RY_---1R[_0LF1Lo_0LH0RR_1LF0R[_1LH0RY_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0Lh1Lo_1RR0RR_1Lh0R[_1RY0RY_0LU---_0LW---_1Lo---_0RR---_0Lm---_0Lo---_1Lm---_1Lo---_0LF1LF_0RR0RY_1Lo0R[_1RR1RY_0LM0LN_0LO0LP_1LM1LN_1LO1LP".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "jRoMUFNW[h".
Definition mp' := mp_from_str "YRoMUFNW[h".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM22.


Module TM23.
Definition tm := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC0RD_0LF---_0LB1LB".
Definition tm' := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC0RE_0LD---".
Definition tm0 := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1Lo0Lf_1RR0Lh_0R[1Lf_1RY1Lh_1RR0RY_0RR0R[_0Lh1RY_1RR1R[_0LU1Lo_0LW0RR_1LU0R[_1LW0RY_0R[0RY_1Lo0R[_1R[1RY_---1R[_0LF1Lo_0LH0RR_1LF0R[_1LH0RY_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0Lh1Lo_1RR0RR_1Lh0R[_1RY0RY_0LU---_0LW---_1Lo---_0RR---_0Lm---_0Lo---_1Lm---_1Lo---_0LF1LF_0RR0RY_1Lo0R[_1RR1RY_0LM0LN_0LO0LP_1LM1LN_1LO1LP".
Definition tm0' := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1L_0Ln_1RR0Lp_0R\1Ln_1Ra1Lp_1RR0Ra_0RR0Rc_0Lp1Ra_1RR1Rc_0LU1L__0LW0RR_1LU0R\_1LW0Ra_0Rc0RZ_1L_0R\_1Rc1RZ_---1R\_0LF1L__0LH0RR_1LF0R\_1LH0Ra_0LF1LF_0RR0Ra_1L_0R\_1RR1Ra_0LM0LN_0LO0LP_1LM1LN_1LO1LP_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0Lp1L__1RR0RR_1Lp0R\_1Ra0Ra_0LU---_0LW---_1L_---_0RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "YRoMUFNW[h".
Definition mp' := mp_from_str "aR_MUFNW\p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM23.


Module TM24.
Definition tm := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC0RE_0LD---".
Definition tm' := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1RD_0LD---".
Definition tm0 := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1L_0Ln_1RR0Lp_0R\1Ln_1Ra1Lp_1RR0Ra_0RR0Rc_0Lp1Ra_1RR1Rc_0LU1L__0LW0RR_1LU0R\_1LW0Ra_0Rc0RZ_1L_0R\_1Rc1RZ_---1R\_0LF1L__0LH0RR_1LF0R\_1LH0Ra_0LF1LF_0RR0Ra_1L_0R\_1RR1Ra_0LM0LN_0LO0LP_1LM1LN_1LO1LP_0RR0Ra_0RT0Rc_1RR1Ra_1RT1Rc_0Lp1L__1RR0RR_1Lp0R\_1Ra0Ra_0LU---_0LW---_1L_---_0RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ1LM_0RL---_1RJ1LN_1RL---_1L_0Ln_1RR0Lp_0R\1Ln_1RZ1Lp_1RR0Ra_0RR0Rc_0Lp1Ra_1RR1Rc_0LU1L__0LW0RR_1LU0R\_1LW0RZ_0Rc0RZ_1L_0R\_1Rc1RZ_---1R\_0LF1L__0LH0RR_1LF0R\_1LH0RZ_0LF1LF_0RR0RZ_1L_0R\_1RR1RZ_0LM0LN_0LO0LP_1LM1LN_1LO1LP_0RR0RZ_0RT0R\_1RR1RZ_1RT1R\_0Lp1L__1RR0RR_1Lp0R\_1RZ0RZ_0LU---_0LW---_1L_---_0RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1LG_0LE1LC_0LF1LC_1RB0LJ_0LH0RB_1LF0RI_1RB1RA_1LC1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "aR_MUFNW\p".
Definition mp' := mp_from_str "ZR_MUFNW\p".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM24.


Module TM25.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0RB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LA---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_1LH0L]_---0L__1RZ1L]_---1L__0RI---_0RK---_1RI---_1RK---_0LH---_0RD---_1LH---_0RK---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1RK_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LH0LV_---0LX_1LH1LV_---1LX_0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1RE1RK_1RK1RK".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\dl".
Definition mp' := mp_from_str "LUFHKZD\cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM25.


Module TM26.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LE---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LA---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_0L_0L]_---0L__1L_1L]_---1L__------_1R\---_------_1LH---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm0' := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_0LH0L]_---0L__1LH1L]_---1L__0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
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
End TM26.


Module TM27.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LA---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LE---".
Definition tm0 := TM'_from_str "0RJ0Rb_0RL0Rd_1RJ1Rb_1RL1Rd_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rd_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rl0RD_1R\1LH_1LH0RK_0Rj0RL_0Rl1RK_1Rj1RL_1Rl1LH_0LH0L]_---0L__1LH1L]_---1L__0R\---_1RK---_1R\---_1LH---_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_0LW1LH_1RD0LH_1LW---_1RK1LH_1RK0RZ_1LF0R\_1LH1RZ_1LU1R\_0LV1RL_0LX1LH_1LV1Rc_1LX1RZ_0R\1RD_1RK0LF_1R\0LH_1LH0LU_0LF0LU_0LH0LW_1LF1LU_1LH1LW_0RB0RI_0RD0RK_1RB1RI_1RD1RK_1LU0LH_1Rj0RD_1R\1LH_1LH0RK_0Rj1RK_0Rl1LF_1Rj1LH_1Rl1LU_0LX0LV_---0LX_1LX1LV_---1LX_------_1LH---_------_1LW---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RG0LD_1RE1LD_1LD1RF_0RG0RE_1RA1RI_1RG1RE_1RJ1LD_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "LUFHKZD\dl".
Definition mp' := mp_from_str "LUFHKZD\cj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM27.


Module TM28.
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
End TM28.


Module TM29.
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
End TM29.


Module TM30.
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
End TM30.


Module TM31.
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
End TM31.


Module TM32.
Definition tm := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LB_0LB1RF_0LF0RA".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LB_0LB1RF_0LF0RA".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rj1RJ_0Rl0LV_1Rj0L__1Rl1RJ_1LV0L]_1RJ0L__0R[1L]_---1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0RC1LO_1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rl0RY_1LV0R[_1Rl1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0Rj1L]_1RC1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0RC1LO_1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB1RA_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MjC".
Definition mp' := mp_from_str "JV[a_MjC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM32.


Module TM33.
Definition tm := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LB_0LB1RF_0LF0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LB---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rl0RY_1LV0R[_1Rl1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0Rj1L]_1RC1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0RC1LO_1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
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
End TM33.


Module TM34.
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
End TM34.


Module TM35.
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
End TM35.


Module TM36.
Definition tm := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LD_0LB1RF_0LF0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LD---".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0Rl0RY_1LV0R[_1Rl1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0Rj1L]_1RC1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0RC1L__1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0LV---_0L_---_0L]---_0L]---_0L_---_1L]---_1L_---".
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
End TM36.


Module TM37.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LD---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LD_0LB1RF_0LF0RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0LV---_0L_---_0L]---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rj1RJ_0Rl0LV_1Rj0L__1Rl0L]_1LV0L]_1RJ0L__0R[1L]_---1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0RC1L__1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Ai".
Definition mp' := mp_from_str "JV[a_]jC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM37.


Module TM38.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LE---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L]_1Ra---_1L_1L]_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0Ra---_0LV---_1Ra---_0L]---_0LU---_0LW---_1LU---_1LW---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LM_1Ra---_1L_1LM_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0LV---_0RJ---_1RJ---_1RJ---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Aj".
Definition mp' := mp_from_str "JV[a_]Ai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM38.


Module TM39.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LE---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_0RC---_1LV---_1RC---_1L]---_0LV---_0LX---_1LV---_1LX---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LO_1Ra---_1L_1LO_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_0Ri---_0RA---_1Ri---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB0LF_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Aj".
Definition mp' := mp_from_str "JV[a_]Ai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM39.


Module TM40.
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
End TM40.


Module TM41.
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
End TM41.


Module TM42.
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
End TM42.


Module TM43.
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
End TM43.


Module TM44.
Definition tm := TM_from_str "1RB1LF_1LC1RE_0RA0LD_1LA0LD_0RF---_0RC1RC".
Definition tm' := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---".
Definition tm0 := TM'_from_str "0RJ1Rk_0RL0LF_1RJ0Lp_1RL0L]_0L_0Ln_1Rk0Lp_1L_1Ln_---1Lp_1Rk0Rb_1LF0Rd_0Lp1Rb_1L]1Rd_0LV1RQ_0LX---_1LV1RR_1LX---_0RA1Rk_0RC0LF_1RA0Lp_1RC0L]_1LF0L]_0LF0L__0Rd1L]_1LF1L__0Rd1Rk_1LF0LF_1Rd0Lp_1L]0L]_0LF0L]_0LH0L__1LF1L]_1LH1L__0Ri---_0Rk---_1Ri---_1Rk---_0RA---_0RC---_1Rk---_0LF---_0RQ0RR_0RS0RT_1RQ1RR_1RS1RT_0RJ1RJ_0LF0L]_1Rk0Lp_1LF1L]".
Definition tm0' := TM'_from_str "0RJ1RS_0RL0LF_1RJ0LX_1RL0Le_0LX0LV_1RS0LX_1LX1LV_---1LX_0Rl0Rj_1LF0Rl_1Rl1Rj_1Le1Rl_0LF1RY_0LH---_1LF1RZ_1LH---_0RY0RZ_0R[0R\_1RY1RZ_1R[1R\_0RJ1RJ_0LF0Le_1RS0LX_1LF1Le_0RA1RS_0RC0LF_1RA0LX_1RC0Le_1LF0Le_0LF0Lg_0Rl1Le_1LF1Lg_0Rl1RS_1LF0LF_1Rl0LX_1Le0Le_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RQ---_0RS---_1RQ---_1RS---_0RA---_0RC---_1RS---_0LF---".
Definition tm1 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE---".
Definition tm2 := TM'_from_str "0RB1RE_0RC1RE_1LD0RJ_1RE0LH_1RA1RF_0RG0LD_1RC0LH_1LD1LI_0LD0LI_1RE1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QAJFkRCp]d".
Definition mp' := mp_from_str "YAJFSZCXel".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM44.


Module TM45.
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
End TM45.


Module TM46.
Definition tm := TM_from_str "1LB1RE_0LC0RB_1RD0LA_0RA0RD_0RF0LE_1RD---".
Definition tm' := TM_from_str "1LB1RE_0LC0RB_1RD0LA_0RA0RD_0RF0RA_1RD---".
Definition tm0 := TM'_from_str "1Rb0Rb_0RI0Rd_1LE1Rb_1RI1Rd_0LN1RZ_0LP0Le_1LN---_1LP1Le_0RC0RI_0LN0RK_1RC1RI_1RZ1RK_0LU1LE_0LW0RC_1LU1Rb_1LW0RI_0RZ0LW_0R\0Rk_1RZ0RC_1R\1Rk_1LE0LE_1RA0LG_1Rb1LE_1RY1LG_0RA0RY_0RC0R[_1RA1RY_1RC1R[_0LW1Rb_0Rk0RA_1LW0Rb_0RC0RY_0Ri0RZ_0Rk0RC_1Ri1RZ_1Rk0Le_0RC0Le_---0Lg_0R[1Le_---1Lg_0RZ---_0R\---_1RZ---_1R\---_1LE---_1RA---_1Rb---_1RY---".
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
End TM46.


Module TM47.
Definition tm := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA0RB_---0RB".
Definition tm' := TM_from_str "1LB1RF_0LC1LC_1RD0LD_0RE0RA_1LA0RB_---1RD".
Definition tm0 := TM'_from_str "1RI0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RI_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RI1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0RK_1LW0RI_0RK0RK_1LX1RI_1RK1RK_0LF1LX_0LH1L]_1LF1RI_1LH1Rj_---0RI_---0RK_---1RI_---1RK_---1LX_---1L]_---1RI_---1Rj".
Definition tm0' := TM'_from_str "1RI0Rj_1Rj0Rl_1L]1Rj_1L_1Rl_0LN---_0LP1Rc_1LN---_1LP1RC_0Rc0RC_0LP1LP_1Rc1RC_0LW1LW_0LU0LV_0LW0LX_1LU1LV_1LW1LX_0RZ1LW_0R\1RI_1RZ1LX_1R\1L]_1LX0L]_1L]0L__1RI1L]_1Rj1L__0Ra0RA_0Rc0RC_1Ra1RA_1Rc1RC_0LP0LW_0Rc---_1LP1LW_0RC0R\_1LW0RI_0R\0RK_1LX1RI_1R\1RK_0LF1LX_0LH1L]_1LF1RI_1LH1Rj_---0RZ_---0R\_---1RZ_---1R\_---1LX_---1L]_---1RI_---1Rj".
Definition tm1 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_---0RH_1RE1RA_1LJ1LC_1LC1LF".
Definition tm2 := TM'_from_str "1LB1RG_0LJ0LC_1RD1LB_0RE0RA_1LF1RD_1RG1LI_1RK0RH_1RE1RA_1LJ1LC_1LC1LF_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "C]WIcXjK_P".
Definition mp' := mp_from_str "C]WIcXj\_P".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM47.


Module TM48.
Definition tm := TM_from_str "1LB1RC_1RA1LD_1RA0RA_1RF0LE_0LD1LB_---0LE".
Definition tm' := TM_from_str "1LB1RC_1RA1LE_0LD0RA_---1RB_1RD0LF_0LE1LB".
Definition tm0 := TM'_from_str "0RT0RR_1LN0RT_1RT1RR_1Lg1RT_0LN1Lg_0LP1RT_1LN1RT_1LP1RR_0RB1RD_0RD1L]_1RB0L`_1RD1LN_0L`0L^_1RD0L`_1L`1L^_1RC1L`_0RB0RA_0RD0RC_1RB1RA_1RD1RC_0L`1RD_1RD0RD_1L`1RC_1RC0RC_0Rj---_0Rl1RD_1Rj0Le_1Rl0L`_---0Le_0LN0Lg_---1Le_1LN1Lg_---0RT_0L]1LN_---1RT_0LN1Lg_0L]0LN_0L_0LP_1L]1LN_1L_1LP_------_---1RD_---0Le_---0L`_---0Le_---0Lg_---1Le_---1Lg".
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
End TM48.


Module TM49.
Definition tm := TM_from_str "1LB1RA_1RC0LF_---0RD_1LE0RE_1RA0RB_1LA1LF".
Definition tm' := TM_from_str "1LB1RA_1RC0LE_---0RD_1LE0RF_1LA1LE_1RA0RB".
Definition tm0 := TM'_from_str "0R[0RB_1LF0RD_1R[1RB_1Ln1RD_0LN0Lo_0LP1Ln_1LN1Lo_1LP1RD_0RR0LP_0RT0LH_1RR1Ln_1RT0Lp_---0Lm_1RD0Lo_---1Lm_1Ra1Lo_---0RY_---0R[_---1RY_---1R[_---1Ln_---0RB_---1RD_---0RI_0RD0Ra_0LP0Rc_1RD1Ra_1Ln1Rc_0Lf1LF_0Lh0RR_1Lf0RD_1Lh0LP_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0Lo---_1Ln0LF_1Lo0R[_1RD1LF_1Ra1LP_0RD1LH_1Lo1RD_1RD1Lp_0LF0Ln_0LH0Lp_1LF1Ln_1LH1Lp".
Definition tm0' := TM'_from_str "0R[0RB_1LF0RD_1R[1RB_1Lf1RD_0LN0Lg_0LP1Lf_1LN1Lg_1LP1RD_0RR0LP_0RT0LH_1RR1Lf_1RT0Lh_---0Le_1RD0Lg_---1Le_1Ri1Lg_---0RY_---0R[_---1RY_---1R[_---0LH_---0RB_---1LH_---0RI_1LP0Ri_1LH0Rk_1RD1Ri_1Lh1Rk_0Lf1LF_0Lh0RR_1Lf0RD_1Lh0LP_1Ri1LP_0RD1LH_1Lg1RD_1RD1Lh_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_0RB0RI_0RD0RK_1RB1RI_1RD1RK_0Lg---_1Lf0LF_1Lg0R[_1RD1LF".
Definition tm1 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1LE1RA_1RH1LF_1LG1LB_0LE1LB_0RI0RJ_1LG0RA_0RK0LE_---0RL_1RA1RH".
Definition tm2 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1LE1RA_1RH1LF_1LG1LB_0LE1LB_0RI0RJ_1LG0RA_0RK0LE_1RM0RL_1RA1RH_1RM1RM".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "DnpHPoFaBIR[".
Definition mp' := mp_from_str "DfhHPgFiBIR[".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM49.


Module TM50.
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
End TM50.


Module TM51.
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
End TM51.


Module TM52.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LC---".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---".
Definition tm0 := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RL_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_0LU1RL_---1Rj_1LU1RD_---1RZ_0RB---_0RL---_1RB---_0LU---_0LU---_0LW---_1LU---_1LW---".
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
End TM52.


Module TM53.
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
End TM53.


Module TM54.
Definition tm := TM_from_str "1RB0LB_1RC1LC_1LD1RE_---0LA_1LB0RF_1RA0LF".
Definition tm' := TM_from_str "1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF".
Definition tm0 := TM'_from_str "0RJ1Rd_0RL0L`_1RJ1LM_1RL1RB_1LM0LM_1RB0LO_1Rd1LM_1RL1LO_0RR---_0RT0Rk_1RR1LG_1RT1Rk_0LG0LV_1RL0LX_1LG1LV_1Rk1LX_---0Rb_1Rd0Rd_---1Rb_1LM1Rd_0L^0LX_0L`1RB_1L^1LX_1L`1RL_---0RT_---0LG_---1RT_---0LV_---0LE_---0LG_---1LE_---1LG_0Rd0Ri_1L`0Rk_1Rd1Ri_1RL1Rk_0LN0RL_0LP1RT_1LN0L`_1LP1Rk_0RB0RL_0RD1RT_1RB1RL_1RD0Lm_1RT0Lm_0LV0Lo_1Rk1Lm_1LV1Lo".
Definition tm0' := TM'_from_str "0RJ1Rd_0RL0L`_1RJ1LM_1RL1RB_1LM0LM_1RB0LO_1Rd1LM_1RL1LO_0RR---_0RT0Rk_1RR1LG_1RT1Rk_0LG0LV_1RL0LX_1LG1LV_1Rk1LX_---0Rb_1Rd0Rd_---1Rb_1LM1Rd_0L^1RT_0L`1RB_1L^1Rk_1L`1RL_---0RT_---0LG_---1RT_---0LV_---0LE_---0LG_---1LE_---1LG_1Lh0Ri_0RL0Rk_1Rk1Ri_1RL1Rk_0Lf0RL_0Lh1RT_1Lf0L`_1Lh1Rk_0RB0RL_0RD1RT_1RB1RL_1RD0Lm_1RT0Lm_0LV0Lo_1Rk1Lm_1LV1Lo".
Definition tm1 := TM'_from_str "1LB1RI_0LH0LC_0LG1RD_0RE0LG_1RA1RF_1RD1RE_---1LH_1RI1LB_1RE1RF".
Definition tm2 := TM'_from_str "1LB1RI_0LH0LC_0LG1RD_0RE0LG_1RA1RF_1RD1RE_1RJ1LH_1RI1LB_1RE1RF_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "TMVBLk`Gd".
Definition mp' := mp_from_str "TMVBLk`Gd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM54.


Module TM55.
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
End TM55.


Module TM56.
Definition tm := TM_from_str "1RB0RF_0LB1RC_1LD1RA_1LA0LE_0RC1LD_0RC---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LA0LD_0RE1LC_1LC1RF_1RB0RD".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0Lg1RD_1L^---_1Lg0RB_1RD---_0LM0RR_1LH0RT_0Lg1RR_1L^1RT_0LM0Lg_0LO1RL_1LM1Lg_1LO1Rk_1RD0RB_1LH0RD_---1RB_1L^1RD_0L^1L^_0L`1RQ_1L^1RT_1L`---_0RT1RD_---0LH_1RT---_---0Lg_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_0RQ1RD_0RS1LH_1RQ---_1RS1L^_0LH0L^_0RL0L`_1LH1L^_0Rk1L`_0RQ---_0RS---_1RQ---_1RS---_0LH---_0RL---_1LH---_0Rk---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1LV---_1L_---_1Rl---_1Rl0Rb_1LH0Rd_---1Rb_1LV1Rd_0LV0L__0LX1RL_1LV1L__1LX1R[_0Rd1Rl_---0LH_1Rd---_---0L__0LF0L]_0LH0L__1LF1L]_1LH1L__0Ra1Rl_0Rc1LH_1Ra---_1Rc1LV_0LH0LV_0RL0LX_1LH1LV_0R[1LX_1Rl0Rj_1LH0Rl_---1Rj_1LV1Rl_0LV1LV_0LX1Ra_1LV1Rd_1LX---_0RJ0RY_0RL0R[_1RJ1RY_1RL1R[_0L_1Rl_1LV0LH_1L_0Rj_1Rl1LH".
Definition tm1 := TM'_from_str "1RB---_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC---_0RD0RA_1LE1RC".
Definition tm2 := TM'_from_str "1RB1RJ_1RC0RH_1RD1RA_1LE1RI_0LG0LF_1LG1LE_1RC1RJ_0RD0RA_1LE1RC_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;0]%N.
Definition mp := mp_from_str "kQDL^gHBT".
Definition mp' := mp_from_str "[alLV_Hjd".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM56.


Module TM57.
Definition tm := TM_from_str "1LB1RF_1RC1LF_1LA1RD_1LE0RC_---1LC_0RA0LD".
Definition tm' := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_1RC0LD".
Definition tm0 := TM'_from_str "0R\0Rj_1RS0Rl_1R\1Rj_1L_1Rl_0LN1R\_0LP0LP_1LN1Rj_1LP1LP_0RR0Rj_0RT1Lf_1RR1Rj_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RA---_0RC1RS_1RA0LX_1RC1Lp_1RZ0L]_0RC0L__1RS1L]_1RS1L_".
Definition tm0' := TM'_from_str "0R\0R\_1RS1RS_1R\1R\_1L_1L__0LN0LN_0LP0LP_1LN1LN_1LP1LP_0RR0R\_0RT1Lf_1RR1R\_1RT1LP_0LP0Ln_1RZ0Lp_1LP1Ln_1RS1Lp_1RS0RZ_1RS0R\_1Lp1RZ_1Lp1R\_0LF0LX_0LH1Lp_1LF1LX_1LH1RZ_---0RQ_1LH0RS_---1RQ_1RZ1RS_0Lf0LP_0Lh1LH_1Lf1LP_1Lh0RS_---1LP_---0RS_---1LP_---1RS_---0LV_---0LX_---1LV_---1LX_0RR---_0RT1RS_1RR0LX_1RT1Lp_0LP0L]_1RZ0L__1LP1L]_1RS1L_".
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
End TM57.


Module TM58.
Definition tm := TM_from_str "1RB1RC_0LA---_1RD0RA_1RE0LA_1LF1LE_0RC0LF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1LA---".
Definition tm0 := TM'_from_str "0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1Rd1Rd_---1RJ_1R\1R\_---1RR_0R\---_0R\---_1R\---_1R\---_0LE---_0LG---_1LE---_1LG---_0RZ0RA_0R\0RC_1RZ1RA_1R\1RC_1Lm0R\_1Rd0R\_1Lh---_1R\0RC_0Rb0R\_0Rd0R\_1Rb1R\_1Rd1R\_0Lo0LE_0Lh0LG_1Lo1LE_1Lh1LG_0RA0RR_0R\1Lp_1RA1Lo_1Lm1Lh_0Ln0Lf_0Lp0Lh_1Ln1Lf_1Lp1Lh_0RQ0RZ_0RS0Rd_1RQ1RZ_1RS0Lm_0Rd0Lm_0RJ0Lo_0R\1Lm_0RR1Lo".
Definition tm0' := TM'_from_str "0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0LW1LU_0LP1RL_1LW1LP_1LP1RD_0Ra0RZ_0RD1LX_1Ra1LW_1LU1LP_0LV0LN_0LX0LP_1LV1LN_1LX1LP_0RY0RB_0R[0RL_1RY1RB_1R[0LU_0RL0LU_0Rj0LW_0RD1LU_0RZ1LW_0RB0Ra_0RD0Rc_1RB1Ra_1RD1Rc_1LU0RD_1RL0RD_1LP---_1RD0Rc_0Rj0RZ_0Rl0R\_1Rj1RZ_1Rl1R\_1RL1RL_---1Rj_1RD1RD_---1RZ_1LX---_0RD---_1LP---_1RD---_0LF---_0LH---_1LF---_1LH---".
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
End TM58.


Module TM59.
Definition tm := TM_from_str "1LB1LD_0LC1LF_1RD0LF_1RE---_0RF0RE_0LA1RE".
Definition tm' := TM_from_str "1LB1LD_0LC1LE_1RD0LE_1RB---_0LA1RF_0RE0RF".
Definition tm0 := TM'_from_str "1Rc0Rc_1LG---_1Lm1Rc_1Ra---_0LN0L^_0LP0L`_1LN1L^_1LP1L`_0Rd1LN_0LE0Rc_1Rd1L^_0Lp1Rc_0LU0Ln_0LW0Lp_1LU1Ln_1LW1Lp_0RZ0LN_0R\0Rk_1RZ0L^_1R\1Rk_1Rk0Lm_---0Lo_1Rc1Lm_---1Lo_0Rb---_0Rd---_1Rb---_1Rd---_0Lp---_1Ri---_1Rb---_1Ra---_0Ri0Ra_0Rk0Rc_1Ri1Ra_1Rk1Rc_0LN0LW_0Rk0Ri_1LN0Rb_0Rc0Ra_0LW0Rb_1Ri0Rd_0Lp1Rb_---1Rd_0LE0Lp_0LG1Ri_1LE1Rb_1LG1Ra".
Definition tm0' := TM'_from_str "1Rk0Rk_1LG---_1Le1Rk_1Ri---_0LN0L^_0LP0L`_1LN1L^_1LP1L`_0RL1LN_0LE0Rk_1RL1L^_0Lh1Rk_0LU0Lf_0LW0Lh_1LU1Lf_1LW1Lh_0RZ0LN_0R\0Rc_1RZ0L^_1R\1Rc_0Lh0Le_---0Lg_1Rk1Le_---1Lg_0RJ---_0RL---_1RJ---_1RL---_0Le---_1Ra---_1Le---_1Ri---_0LW0Rj_1Ra0Rl_0Lh1Rj_---1Rl_0LE0Lh_0LG1Ra_1LE1Rj_1LG1Ri_0Ra0Ri_0Rc0Rk_1Ra1Ri_1Rc1Rk_0LN0LW_0Rc0Ra_1LN0Rj_0Rk0Ri".
Definition tm1 := TM'_from_str "0LB0RI_1RH1LC_0LD0LF_0LE0LL_0LB0LF_1LG1RK_1LE1LL_1RA1RK_0RJ0RH_0LF1RI_0RA0RK_1RA---".
Definition tm2 := TM'_from_str "0LB0RI_1RH1LC_0LD0LF_0LE0LL_0LB0LF_1LG1RK_1LE1LL_1RA1RK_0RJ0RH_0LF1RI_0RA0RK_1RA1RM_1RM1RM".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "iWmENpGcbka^".
Definition mp' := mp_from_str "aWeENhGkjci^".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM59.


Module TM60.
Definition tm := TM_from_str "1LB1RC_1LC0RE_1LD1LF_1RE0RB_0LD1RB_0LA---".
Definition tm' := TM_from_str "1LB1RC_1LC0RE_1LD1LF_1RE0RB_1LF1RB_0LA---".
Definition tm0 := TM'_from_str "1L`0RR_0RJ0RT_1Lp1RR_1RJ1RT_0LN1Rc_0LP---_1LN0RJ_1LP---_1Rc0Ra_1LG0Rc_0RJ1Ra_---1Rc_0LV0L`_0LX1LG_1LV1L`_1LX0Rc_0RL1LN_0Ra---_1RL0RJ_1Ra---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_0L`0L`_---1Rc_1L`1L`_1Rc0RJ_1Rc0RJ_1Rc0RL_0RJ1RJ_0RJ1RL_0L]0Lp_0L_0RJ_1L]1Lp_1L_1RJ_0LX---_0Ra---_1LG---_1Ra---_0LE---_0LG---_1LE---_1LG---".
Definition tm0' := TM'_from_str "1L`0RR_0RJ0RT_1Lp1RR_1RJ1RT_0LN1LN_0LP---_1LN0RJ_1LP---_1Rc0Ra_1LG0Rc_0RJ1Ra_---1Rc_0LV0LG_0LX1LG_1LV1LG_1LX0Rc_0RL1LN_0Ra---_1RL0RJ_1Ra---_0L^0Ln_0L`0Lp_1L^1Ln_1L`1Lp_0Rb0RI_0Rd0RK_1Rb1RI_1Rd1RK_---0L`_---1LN_---1L`_1Rc0RJ_1LN0RJ_---0RL_0RJ1RJ_---1RL_0Ln0Lp_0Lp0RJ_1Ln1Lp_1Lp1RJ_0LX---_0Ra---_1LG---_1Ra---_0LE---_0LG---_1LE---_1LG---".
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
End TM60.


Module TM61.
Definition tm := TM_from_str "1RB---_1RC0LC_0LD0RF_1LB1LE_0LC1LE_1RB0RA".
Definition tm' := TM_from_str "1LB---_1RC0RA_1RD0LD_0LE0RB_1LC1LF_0LD1LF".
Definition tm0 := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0Lh---_0RT---_1Rk---_0RJ---_0RR0LN_0RT0RJ_1RR0Lf_1RT1RJ_0Lf0LU_1RJ0LW_1Lf1LU_1RA1LW_1RJ0Ri_0LW0Rk_0LW1Ri_0Lh1Rk_0L]0RT_0L_0RJ_1L]0RJ_1L_---_0Rk1L]_1L]1LW_1Rk0RJ_0RJ1Lh_0LN0Lf_0LP0Lh_1LN1Lf_1LP1Lh_0LN1L]_0RJ1LW_0Lf0RJ_1RJ1Lh_0LU0Lf_0LW0Lh_1LU1Lf_1LW1Lh_0RJ0RA_0RL0RC_1RJ1RA_1RL1RC_0Lh0RT_0RT---_1Rk0RJ_0RJ---".
Definition tm0' := TM'_from_str "0RR---_------_1RR---_------_0LN---_0LP---_1LN---_1LP---_0RR0RA_0RT0RC_1RR1RA_1RT1RC_0Lp0R\_0R\---_1RK0RR_0RR---_0RZ0LV_0R\0RR_1RZ0Ln_1R\1RR_0Ln0L]_1RR0L__1Ln1L]_1RA1L__1RR0RI_0L_0RK_0L_1RI_0Lp1RK_0Le0R\_0Lg0RR_1Le0RR_1Lg---_0RK1Le_1Le1L__1RK0RR_0RR1Lp_0LV0Ln_0LX0Lp_1LV1Ln_1LX1Lp_0LV1Le_0RR1L__0Ln0RR_1RR1Lp_0L]0Ln_0L_0Lp_1L]1Ln_1L_1Lp".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF---_0LC0LB".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LB_1LD0RF_0LE0LI_1RF0LC_0RA0RF_1RF1RH_0RF1RJ_0LC0LB_1RJ1RJ".
Definition l0 := [1;0;1;1;0;0;0;0]%N.
Definition mp := mp_from_str "ThW]NJkAf".
Definition mp' := mp_from_str "\p_eVRKAn".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM61.


Module TM62.
Definition tm := TM_from_str "1LB1RE_1RB1RC_1LD0RE_---0LB_1LF1RA_1LF0LD".
Definition tm' := TM_from_str "1LB1RE_1RB1RC_1LD0RE_---0LB_1LF1RA_0LA0LD".
Definition tm0 := TM'_from_str "0RT0Rb_0Rc0Rd_1RT1Rb_1Rc1Rd_0LN0L__0LP1Rc_1LN1L__1LP1Rd_0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1RL0LO_1LO1L__1RT1LO_1Rc1RB_---0Ra_1RT0Rc_---1Ra_1LO1Rc_0L^0Lp_0L`0Rc_1L^1Lp_1L`0Rd_---0RL_---1RT_---1RL_---1LO_---0LM_---0LO_---1LM_---1LO_1Lp0RB_---0RD_1L_1RB_1LM1RD_0Ln1L__0Lp1LM_1Ln1RB_1Lp1RD_1Lp---_---1RL_1L_---_1LM0LO_0Ln0L]_0Lp0L__1Ln1L]_1Lp1L_".
Definition tm0' := TM'_from_str "0RT0Rb_0Rc0Rd_1RT1Rb_1Rc1Rd_0LN0L__0LP1Rc_1LN1L__1LP1Rd_0RJ0RR_0RL0RT_1RJ1RR_1RL1RT_1RL0LO_1LO1L__1RT1LO_1Rc1RB_---0Ra_1RT0Rc_---1Ra_1LO1Rc_0L^0LG_0L`0Rc_1L^1LG_1L`0Rd_---0RL_---1RT_---1RL_---1LO_---0LM_---0LO_---1LM_---1LO_1LN0RB_---0RD_1L_1RB_1LM1RD_0Ln1L__0Lp1LM_1Ln1RB_1Lp1RD_1LO---_---1RL_1L_---_1LM0LO_0LE0L]_0LG0L__1LE1L]_1LG1L_".
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
End TM62.


Module TM63.
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
End TM63.


Module TM64.
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
End TM64.


Module TM65.
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
End TM65.


Module TM66.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LA---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Ln0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RT0RJ_---0RL_1RT1RJ_---1RL_0Ln1LG_0Lp1RR_1Ln1RT_1Lp1RI_0RY---_0R[---_1RY---_1R[---_0LH---_1LG---_1LH---_1RT---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LG_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1RT0RY_---0R[_1L^1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RT---_0LX---_1RT---_0LG---_0LE---_0LG---_1LE---_1LG---".
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
End TM66.


Module TM67.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0RB---".
Definition tm0 := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lh_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LX_1LX0RT_1RK---_1LG1RT_0LF0Lf_0LH0Lh_1LF1Lf_1LH1Lh_1RI0RT_1Lp0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_1LH0RY_---0R[_1Lh1RY_---1R[_0Ln0LH_0Lp1LG_1Ln1LH_1Lp1RT_0RA---_0RC---_1RA---_1RC---_0RT---_0LX---_0RK---_1LX---".
Definition tm0' := TM'_from_str "0RJ1LH_0RL1RT_1RJ1Lg_1RL1L^_1LG0L^_1RR0L`_1RT1L^_1RI1L`_0RR0RI_0RT0RK_1RR1RI_1RT1RK_0L`1LX_1LG0RR_1L`0RT_1RT0RI_0RK1LX_1LX0RT_1RK---_1LG1RT_0LF0Le_0LH0Lg_1LF1Le_1LH1Lg_1RI0RT_1Lm0LX_1L`1RT_1RT0LG_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0RR0RJ_---0RL_1RR1RJ_---1RL_0Lm1LG_0Lo1RR_1Lm1RT_1Lo1RI_0RI---_0RK---_1RI---_1RK---_1LX---_0RR---_0RT---_0RI---".
Definition tm1 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LD---".
Definition tm2 := TM'_from_str "1LB1RA_1RA1LC_0LD0LB_1LF1LE_1LJ1RA_1RG1LI_0RH0RG_1LD0RA_1LD1LB_1LD1RK_1RK1RK".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "TG^XhHIR`p".
Definition mp' := mp_from_str "TG^XgHIR`m".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM67.


Module TM68.
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
End TM68.


Module TM69.
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
End TM69.


Module TM70.
Definition tm := TM_from_str "1RB0LE_1RC0RF_1RD---_0LA1RB_1RB1LE_1LD1RF".
Definition tm' := TM_from_str "1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF".
Definition tm0 := TM'_from_str "0RJ0RT_0RL1Le_1RJ1RT_1RL0Lh_1R\0Le_1Le0Lg_---1Le_1Rj1Lg_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0Lf0LG_---0Rk_1RL1LG_---0Rl_0RZ---_0R\---_1RZ---_1R\---_0Le---_1RT---_1Le---_1Rk---_0RT0RJ_1R\0RL_1RT1RJ_0Lf1RL_0LE1R\_0LG1Le_1LE---_1LG1Rj_0RJ0Rk_0RL1Rj_1RJ1Rk_1RL1Lh_1R\0Lf_1Le0Lh_---1Lf_1Rj1Lh_---0Rj_0Rk0Rl_1Le1Rj_1Rk1Rl_0L^1Le_0L`1Rk_1L^1Rj_1L`1Rl".
Definition tm0' := TM'_from_str "0RJ0Rk_0RL1Rj_1RJ1Rk_1RL1LH_1R\0LF_1LE0LH_---1LF_1Rj1LH_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0LF0Lg_---0Rk_1RL1Lg_---0Rl_0RZ---_0R\---_1RZ---_1R\---_0LE---_1RT---_1LE---_1Rk---_---0RJ_1R\0RL_---1RJ_0LF1RL_0Le1R\_0Lg1LE_1Le---_1Lg1Rj_---0RT_---1LE_---1RT_---0LH_---0LE_---0LG_---1LE_---1LG_---0Rj_0Rk0Rl_1LE1Rj_1Rk1Rl_0L^1LE_0L`1Rk_1L^1Rj_1L`1Rl".
Definition tm1 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC---_1LB0LG_1RH1LG_0RA0RI_1RA1RI".
Definition tm2 := TM'_from_str "1LB1RH_1RC0LF_0LF1RD_1RE1RA_1RC1RJ_1LB0LG_1RH1LG_0RA0RI_1RA1RI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "ke\LTfhjl".
Definition mp' := mp_from_str "kE\LTFHjl".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 44 44.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM70.


Module TM71.
Definition tm := TM_from_str "1RB1LA_0RC1RE_1LD0LA_0LA0RC_1RF0RD_---0RB".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD1RC_1LC0LA_1RF0RC_---0RB".
Definition tm0 := TM'_from_str "0RJ0Rd_0RL1R[_1RJ1Rd_1RL1LH_1LF0LF_1Rl0LH_1RS1LF_1R[1LH_0RQ0Rb_0RS0Rd_1RQ1Rb_1RS1Rd_0LG---_1LF1RS_1LG1RK_1RS1RQ_1RS0RS_0RS1Rl_1LF1RS_1RS0LH_0L^0LE_0L`0LG_1L^1LE_1L`1LG_0RS0RQ_1Rl0RS_1RS1RQ_0LH1RS_0LE0LG_0LG1LF_1LE1LG_1LG1RS_0Rj0RY_0Rl0R[_1Rj1RY_1Rl1R[_---1LF_1RQ1RS_---1RS_1Rb0RS_---0RI_---0RK_---1RI_---1RK_---1RS_---0Rl_---0RS_---0R[".
Definition tm0' := TM'_from_str "0RJ0Rd_0RL1RS_1RJ1Rd_1RL1LH_1LF0LF_1Rl0LH_1RT1LF_1RS1LH_0RR0Rb_0RT0Rd_1RR1Rb_1RT1Rd_0LG---_1LF1RT_1LG1RK_1RT1RR_1L`0RR_1RT0RT_1RT1RR_1LF1RT_0L^0LG_0L`1LF_1L^1LG_1L`1RT_1LX0RT_0RT1Rl_1LG1RT_1RT0LH_0LV0LE_0LX0LG_1LV1LE_1LX1LG_0Rj0RQ_0Rl0RS_1Rj1RQ_1Rl1RS_---0LX_1RR1RT_---1LX_1Rb0RT_---0RI_---0RK_---1RI_---1RK_---1RT_---0Rl_---0RT_---0RS".
Definition tm1 := TM'_from_str "1RB1RE_1LC1RB_1RF0LD_1RA1LD_1RB0RB_---1RG_1RE1RH_0RF0RA".
Definition tm2 := TM'_from_str "1RB1RE_1LC1RB_1RF0LD_1RA1LD_1RB0RB_1RI1RG_1RE1RH_0RF0RA_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "[SFHQlKb".
Definition mp' := mp_from_str "STFHRlKb".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 47 47.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM71.


Module TM72.
Definition tm := TM_from_str "1RB1LA_1RC0RD_1LA---_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_1LC0RD_1LA1RC_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_---1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_---0Rd_1LH1Rb_---0R\_0R[---_1RZ---_1R[---_1LH---_0LF---_0LH---_1LF---_1LH---_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
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
End TM72.


Module TM73.
Definition tm := TM_from_str "1RB1LA_1LC0RD_1LA1RC_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_1RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RT1LF_1RZ1LH_1RZ0RY_0RT0R[_1LH1RY_1RT1R[_0LV1Ln_0LX0Rd_1LV1Rb_1LX0R\_0R[0RR_1RZ0RT_1R[1RR_1LH1RT_0LF0LH_0LH1LH_1LF1LH_1LH1RT_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1LH1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_0LH0Rd_1LH1Rb_1LH0R\_1LX0R[_1RZ1RZ_1LH1R[_1LH1LH_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
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
End TM73.


Module TM74.
Definition tm := TM_from_str "1RB1LA_1RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LB_1RC1LB_1LB0RD_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1LH1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_0LH0Rd_1LH1Rb_1LH0R\_1LX0R[_1RZ1RZ_1LH1R[_1LH1LH_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
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
End TM74.


Module TM75.
Definition tm := TM_from_str "1RB1LB_1RC1LB_1LB0RD_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_0RC0RD_1LC1RA_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LP_1LP0LN_0LP0LP_1R[1LN_1LP1LP_0RR0R[_0RT1RZ_1RR1R[_1RT1LP_0LP0LN_1Rb0LP_1LP1LN_1RZ1LP_0R[0RY_1RZ0R[_1R[1RY_1LP1R[_0LN1Ln_0LP0Rd_1LN1Rb_1LP0R\_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LN1Rd_1Lg0LP_1LN1R\_---0RT_1Ln1Rb_---1RT_1LE0LP_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LP_---0Lg_---0LN_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RB1LF_1RZ1LH_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0LX1Ln_0RL0Rd_1LX1Rb_1RZ0R\_1LX0RB_1RZ0RD_1LH1RB_1LH1RD_0LV1RS_0LX0LH_1LV1R[_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RS_1Ln1Rb_---1RS_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
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
End TM75.


Module TM76.
Definition tm := TM_from_str "1RB1LA_0RC0RD_1LC1RA_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_1RC0RD_1LC1RA_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RB1LF_1RZ1LH_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0LX1Ln_0RL0Rd_1LX1Rb_1RZ0R\_1LX0RB_1RZ0RD_1LH1RB_1LH1RD_0LV1RS_0LX0LH_1LV1R[_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RS_1Ln1Rb_---1RS_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
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
End TM76.


Module TM77.
Definition tm := TM_from_str "1RB1LA_1RC0RD_1LC1RA_1RE1RD_1LF0LA_---0LE".
Definition tm' := TM_from_str "1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".
Definition tm0 := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1RD1LF_1RZ1LH_0RR0RY_0RT0R[_1RR1RY_1RT1R[_0LH1Ln_1RL0Rd_1LH1Rb_1LH0R\_1LX0RB_1RZ0RD_1LH1RB_1LH1RD_0LV1RT_0LX0LH_1LV1R[_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RT_1Ln1Rb_---1RT_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
Definition tm0' := TM'_from_str "0RJ0R[_0RL1RZ_1RJ1R[_1RL1LH_1LH0LF_1Rb0LH_1R[1LF_1RZ1LH_0RQ0RY_0RS0R[_1RQ1RY_1RS1R[_0LX1Ln_1Rb0Rd_1LX1Rb_1RZ0R\_1LX0R[_1RZ1RZ_1LH1R[_1LH1LH_0LV0LF_0LX0LH_1LV1LF_1LX1LH_0Rb0RZ_0Rd0R\_1Rb1RZ_1Rd1R\_0Lg1LE_0LF1Rd_1Lg0LH_1LF1R\_---0RS_1Ln1Rb_---1RS_1LE0LH_0Ln0LE_0Lp0LG_1Ln1LE_1Lp1LG_------_---1LH_---0Lg_---0LF_---0Le_---0Lg_---1Le_---1Lg".
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
End TM77.


Module TM78.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LD---".
Definition tm' := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Definition tm0 := TM'_from_str "0RJ0Ra_0RL0Rc_1RJ1Ra_1RL1Rc_1L]0RT_1RT0RL_1LX---_1RL0Rc_0RR0RT_0RT0RL_1RR0L]_1RT1RL_0L_0Le_0LX0Lg_1L_1Le_1LX1Lg_0Ra0RB_0RL1L`_1Ra1L__1L]1LX_0L^0LV_0L`0LX_1L^1LV_1L`1LX_0RA0RJ_0RC0RT_1RA1RJ_1RC0L]_0RT0L]_0Rj0L__0RL1L]_0RB1L__0Rj0RB_0Rl0RD_1Rj1RB_1Rl1RD_0L]1RT_---1Rj_1L]1RL_---1RB_0RJ---_0RT---_1RJ---_0L]---_0L]---_0L_---_1L]---_1L_---".
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
End TM78.


Module TM79.
Definition tm := TM_from_str "1LB0RF_1RC0LF_0LA1RD_0LD0RE_1RA---_0RC0LF".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0LE---".
Definition tm0 := TM'_from_str "0R\0Ri_1LN0Rk_1R\1Ri_1Lm1Rk_0LN1RB_0LP0LN_1LN0RZ_1LP1LN_0RR1RB_0RT0LN_1RR0Lo_1RT0Lm_1RB0Lm_1RB0Lo_0RZ1Lm_1Rc1Lo_1RB0RZ_0RQ0R\_0Lo1RZ_1RQ1R\_0LE1LN_0LG1RB_1LE0Rk_1LG---_0L]0Ra_0RB0Rc_1LN1Ra_1RB1Rc_0L]1LN_0L_---_1L]0Rk_1L_---_0RB---_0RD---_1RB---_1RD---_0Lo---_1RQ---_1Lo---_0Lo---_0RQ1RB_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0RB0Lo_1LN1Lm_0Rc1Lo".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1RB0Le_1RB0Lg_0RY1Le_1Ri1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG1RB_1LE0Rc_1LG---_0RB0Ri_0RD0Rk_1RB1Ri_1RD1Rk_0Lg0LN_1RQ---_1Lg1LN_0Lg---_0RQ1RB_0RS0RQ_1RQ0Lg_1RS1RQ_0LN0LE_0RB0LG_1LN1LE_0Ri1LG_1RB---_0LN---_0Lg---_1RB---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNomkQZc".
Definition mp' := mp_from_str "BNgEcQYi".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM79.


Module TM80.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0LB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0LB---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0LN_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Le_1RQ---_1Lg1Le_0Lg---_0RQ1RB_0RS0RQ_1RQ0Lg_1RS1RQ_0LN0LE_0RB0LG_1LN1LE_0Rj1LG_0RQ---_0LN---_1RQ---_0LE---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0LN_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Le_1RQ---_1Lg1Le_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0RQ---_0LN---_1RQ---_0Le---_0LM---_0LO---_1LM---_1LO---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgEcQYj".
Definition mp' := mp_from_str "BNgecQYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM80.


Module TM81.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LF0RD_1RA1RF_0RC0LA_1LB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LB0RF_0RC0LF".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_---0Le_1RB0Lg_---1Le_1Rj1Lg_1RB0RY_---0R[_0Lg1RY_---1R[_0Lm1LN_0Lo1LN_1Lm0Rc_1Lo---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1Lg_0Lg---_0RQ1RB_0RS0RQ_1RQ0Lg_1RS1RQ_0LN0LE_0RB0LG_1LN1LE_0Rj1LG_0R[---_1LN---_1R[---_1LE---_0LN---_0LP---_1LN---_1LP---".
Definition tm0' := TM'_from_str "0R[---_1LN---_1R[---_1Lm---_0LN---_0LP---_1LN---_1LP---_0RR1Rb_0RT0LN_1RR0Lo_1RT0Lm_---0Lm_1Rb0Lo_---1Lm_1RB1Lo_1Rb0RY_---0R[_0Lo1RY_---1R[_0LE1LN_0LG1LN_1LE0Rk_1LG---_0Rb0RB_0Rd0RD_1Rb1RB_1Rd1RD_0Lo0Lo_1RQ---_1Lo1Lo_0Lo---_0R[0Ri_1LN0Rk_1R[1Ri_1Lm1Rk_0LN1Rb_0LP0LN_1LN0RY_1LP1LN_0RQ1Rb_0RS0LN_1RQ0Lo_1RS0Lm_0LN0Lm_0Rb0Lo_1LN1Lm_0RB1Lo".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgEcQYj".
Definition mp' := mp_from_str "bNomkQYB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM81.


Module TM82.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0RE---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0Rc_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg1RQ_1RQ---_1Lg0Lg_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0Ra---_0Rc---_1Ra---_1Rc---_1RB---_0LN---_0RY---_1LN---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0Rc_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg1RQ_1RQ---_1Lg0Lg_0Lg---_0RQ1RB_0RS0RQ_1RQ0Lg_1RS1RQ_0LN0LE_0RB0LG_1LN1LE_0Rj1LG_0Ra---_0Rc---_1Ra---_1Rc---_1RB---_0LN---_0RY---_1LN---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RE---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RE1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgecQYj".
Definition mp' := mp_from_str "BNgEcQYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM82.


Module TM83.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RC---".
Definition tm0 := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1LE1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT1RB_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS0RQ_1RQ0Lg_1RS1RQ_0LN0LE_0RB0LG_1LN1LE_0Rj1LG_0RQ---_0RS---_1RQ---_1RS---_0LN---_0RB---_1LN---_0Rj---".
Definition tm0' := TM'_from_str "0R[0Ra_1LN0Rc_1R[1Ra_1Le1Rc_0LN1RB_0LP0LN_1LN0RY_1LP1LN_0RR1RB_0RT0LN_1RR0Lg_1RT0Le_1RB0Le_1RB0Lg_0RY1Le_1Rj1Lg_1RB0RY_0RQ0R[_0Lg1RY_1RQ1R[_0LE1LN_0LG0RS_1LE0Rc_1LG---_0RB0Rj_0RD0Rl_1RB1Rj_1RD1Rl_0Lg0Lg_1RQ---_1Lg1RY_0Lg---_0RQ1RB_0RS0LN_1RQ0Lg_1RS0Le_0LN0Le_0RB0Lg_1LN1Le_0Rj1Lg_0RQ---_0RS---_1RQ---_1RS---_0LN---_0RB---_1LN---_0Rj---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0LC1RG".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0LC1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BNgEcQYjS".
Definition mp' := mp_from_str "BNgecQYjS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM83.


Module TM84.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_0LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_0LD---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW0LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Rj1L__0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0L]_1RI---_1L_1L]_0L_---_1RR---_0LF---_0L_---_0L]---_0L]---_0L_---_1L]---_1L_---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Rj1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW0LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0L_0LU_1RI---_1L_1LU_0L_---_1RR---_0LF---_0L_---_1RR---_0L]---_0L_---_1L]---_1L_---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_][Iaj".
Definition mp' := mp_from_str "RF_U[Iaj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM84.


Module TM85.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_0LE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LE---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Ri1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0L__1RI---_1L_1L__0L_---_1LF---_1LF---_1L]---_1L]---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW1LF_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0L__1RI---_1L_1L__0L_---_1LF---_1LF---_1LU---_1LU---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_][Iai".
Definition mp' := mp_from_str "RF_U[Iai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM85.


Module TM86.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_0RD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0RD---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL0L]_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW0RY_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1L]1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0LF_1RI0L__1RK0L]_0LF0L]_0RR0L__1LF1L]_0Ri1L__0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0RI_1RI---_1L_1RR_0L_---_0RY---_0R[---_1RY---_1R[---_1RR---_0LF---_0Ra---_1LF---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0L__1RL1RR_1RR0L]_1RR0L__0Ra1L]_1Ri1L__1RR0Ra_0RI0Rc_0L_1Ra_1RI1Rc_0LU1LF_0LW0RY_1LU0R[_1LW---_0Rc0RY_1LF0R[_1Rc1RY_1LU1R[_0LF1RR_0LH0LF_1LF0Ra_1LH1LF_0RI1RR_0RK0RI_1RI0L__1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Ri1LW_0RR0Ri_0RT0Rk_1RR1Ri_1RT1Rk_0L_0RI_1RI---_1L_1RR_0L_---_0RY---_0R[---_1RY---_1R[---_1RR---_0LF---_0Ra---_1LF---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI---_0RF1RA".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB1LD_0LB---_1RF0LC_1RA0RG_0RA0RH_0RI1RJ_0RF1RA_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RF_][IaiY".
Definition mp' := mp_from_str "RF_U[IaiY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM86.


Module TM87.
Definition tm := TM_from_str "1LB---_1LC0RF_1RD0LF_0LB0RE_1RB1RA_0RD0LF".
Definition tm' := TM_from_str "1LB---_1LC0RF_1RD0LF_0LB0RE_1RB1RA_0RD0LB".
Definition tm0 := TM'_from_str "1RB---_1RJ---_1Lo---_0Lo---_0LN---_0LP---_1LN---_1LP---_0Rc0Ri_1LV0Rk_1Rc1Ri_1Lm1Rk_0LV1RJ_0LX0LV_1LV0Ra_1LX1LV_0RZ1RJ_0R\0LV_1RZ0Lo_1R\0Lm_1RJ0Lm_1RJ0Lo_0Ra1Lm_1RB1Lo_1RJ0Ra_0RY0Rc_0Lo1Ra_1RY1Rc_0LM1LV_0LO1RJ_1LM0Rk_1LO---_0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0Lo0LV_1RY---_1Lo1LV_0Lo---_0RY1RJ_0R[0LV_1RY0Lo_1R[0Lm_0LV0Lm_0RJ0Lo_1LV1Lm_0RB1Lo".
Definition tm0' := TM'_from_str "1RB---_1RJ---_1Lo---_0Lo---_0LN---_0LP---_1LN---_1LP---_0Rc0Ri_1LV0Rk_1Rc1Ri_1LM1Rk_0LV1RJ_0LX0LV_1LV0Ra_1LX1LV_0RZ1RJ_0R\0LV_1RZ0Lo_1R\1RJ_1RJ0Lm_1RJ0Lo_0Ra1Lm_1RB1Lo_1RJ0Ra_0RY0Rc_0Lo1Ra_1RY1Rc_0LM1LV_0LO1RJ_1LM0Rk_1LO---_0RJ0RB_0RL0RD_1RJ1RB_1RL1RD_0Lo0LV_1RY---_1Lo1LV_0Lo---_0RY1RJ_0R[0RY_1RY0Lo_1R[1RY_0LV0LM_0RJ0LO_1LV1LM_0RB1LO".
Definition tm1 := TM'_from_str "1RB0RG_1LC0RF_1RB0LD_1LC1LE_0LC---_1RA0LD_0RB0RH_1RB---".
Definition tm2 := TM'_from_str "1RB0RG_1LC0RF_1RB0LD_1LC1LE_0LC---_1RA0LD_0RB0RH_1RB1RI_1RI1RI".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "YJVomkaB".
Definition mp' := mp_from_str "YJVoMkaB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM87.


Module TM88.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LD_0LB1RF_0LF0RA".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LV_1Ra---_1L_1LV_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1RJ_1LM0R[_1LO---_1RJ---_0Ra---_0L_---_1Ra---_0LM---_0LO---_1LM---_1LO---".
Definition tm0' := TM'_from_str "0RJ---_0RL---_1RJ---_1RL---_0L_---_1Ra---_1L_---_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0Rj_1LX1LV_0Rj1RJ_0Rl0LV_1Rj0L__1Rl0L]_1LV0L]_1RJ0L__0R[1L]_---1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0RC1L__1RJ0Rj_0Ra0Rl_0L_1Rj_1Ra1Rl_0LM1LV_0LO1RJ_1LM0R[_1LO---_0Lm0RA_0RJ0RC_1LV1RA_1RJ1RC_0Lm1LV_0Lo---_1Lm0R[_1Lo---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1RA---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAi".
Definition mp' := mp_from_str "JV[a_]jC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM88.


Module TM89.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LC---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LM_1Ra---_1L_1LM_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0LV---_0RJ---_1RJ---_1RJ---_0Le---_0Lg---_1Le---_1Lg---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L]_1Ra---_1L_1L]_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0LV_1LM0R[_1LO---_0Ra---_0LV---_1Ra---_0LM---_0LU---_0LW---_1LU---_1LW---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Ai".
Definition mp' := mp_from_str "JV[a_MAj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM89.


Module TM90.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LE---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LE---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LO_1Ra---_1L_1LO_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_0Ri---_0RA---_1Ri---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0LO_1Ra---_1L_1LO_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO1LV_1LM0R[_1LO---_1LV---_0Ri---_0RA---_1Ri---_0Lf---_0Lh---_1Lf---_1Lh---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1LB---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAi".
Definition mp' := mp_from_str "JV[a_]Ai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM90.


Module TM91.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LA---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LA---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0R[_1LM0R[_1LO---_0R[---_------_1R[---_------_0LF---_0LH---_1LF---_1LH---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_1Ra_1Ra---_1L_0L__0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0R[_1LM0R[_1LO---_0R[---_------_1R[---_------_0LF---_0LH---_1LF---_1LH---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RC---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAi".
Definition mp' := mp_from_str "JV[a_]Ai".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM91.


Module TM92.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RD---".
Definition tm0 := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0Ra_1Ra---_1L_1RJ_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Ri1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0RY_1LM0R[_1LO---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm0' := TM'_from_str "0RJ0Ri_0RL0Rk_1RJ1Ri_1RL1Rk_0L_0Ra_1Ra---_1L_1RJ_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Ri1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Ri1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0RY_1LM0R[_1LO---_0RY---_0R[---_1RY---_1R[---_1RJ---_0LV---_0RA---_1LV---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI---_0RD1RA".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI1RJ_0RD1RA_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_MAiY".
Definition mp' := mp_from_str "JV[a_]AiY".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM92.


Module TM93.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RE---".
Definition tm0 := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1L]1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd0L]_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0LV_1Ra0L__1Rc0L]_0LV0L]_0RJ0L__1LV1L]_0Rj1L__1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0Ra---_0Rc---_1Ra---_1Rc---_0LV---_0RJ---_1LV---_0Rj---".
Definition tm0' := TM'_from_str "0RJ0Rj_0RL0Rl_1RJ1Rj_1RL1Rl_0L_0L__1Ra---_1L_1RA_0L_---_0RC0RY_1LV0R[_1RC1RY_1LM1R[_0LV1RJ_0LX0LV_1LV0RA_1LX1LV_0Rb1RJ_0Rd0LV_1Rb0L__1Rd1RJ_1RJ0L]_1RJ0L__0RA1L]_1Rj1L__0Ra1RJ_0Rc0Ra_1Ra0L__1Rc1Ra_0LV0LM_0RJ0LO_1LV1LM_0Rj1LO_1RJ0RA_0Ra0RC_0L_1RA_1Ra1RC_0LM1LV_0LO0Rc_1LM0R[_1LO---_0Ra---_0Rc---_1Ra---_1Rc---_0LV---_0RJ---_1LV---_0Rj---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI---_0LE1RG".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RI1RJ_0LE1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JV[a_]Ajc".
Definition mp' := mp_from_str "JV[a_MAjc".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM93.


Module TM94.
Definition tm := TM_from_str "1RB0LE_0LC0RD_1LA0LD_1RC1RF_0RB0LC_0RE---".
Definition tm' := TM_from_str "1RB0LE_0LC0RD_1LA0LD_1RC1RF_0RB0LE_0RE---".
Definition tm0 := TM'_from_str "0RJ1RR_0RL0LF_1RJ0Lg_1RL0L]_0L]0Le_1RR0Lg_1L]1Le_1Rj1Lg_1RR0RY_0Lg0R[_0Lg1RY_1RI1R[_0LU1LF_0LW0Rc_1LU0Rc_1LW---_0R[1LF_1LF0Rc_1R[1LU_1LU1Rc_0LF0L]_0LH0L__1LF1L]_1LH1L__0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0Lg1RI_1RI---_1Lg0Lg_0Lg---_0RI1RR_0RK0Lg_1RI0Lg_1RK1RI_0LF0LU_0RR0LW_1LF1LU_0Rj1LW_0Ra---_0Rc---_1Ra---_1Rc---_1RR---_0LF---_0RY---_1LF---".
Definition tm0' := TM'_from_str "0RJ1RR_0RL0LF_1RJ0Lg_1RL0Le_0L]0Le_1RR0Lg_1L]1Le_1Rj1Lg_1RR0RY_0Lg0R[_0Lg1RY_1RI1R[_0LU1LF_0LW0Rc_1LU0Rc_1LW---_0R[1LF_1LF0Rc_1R[1Le_1Le1Rc_0LF0L]_0LH0L__1LF1L]_1LH1L__0RR0Rj_0RT0Rl_1RR1Rj_1RT1Rl_0Lg1RI_1RI---_1Lg0Lg_0Lg---_0RI1RR_0RK0LF_1RI0Lg_1RK0Le_0LF0Le_0RR0Lg_1LF1Le_0Rj1Lg_0Ra---_0Rc---_1Ra---_1Rc---_1RR---_0LF---_0RY---_1LF---".
Definition tm1 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RC---".
Definition tm2 := TM'_from_str "1LB0RC_1RA0LE_1RD0LE_1RA0RG_1LB1LF_0LB---_0RA0RH_0RC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "RFcIgUYj".
Definition mp' := mp_from_str "RFcIgeYj".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM94.


Module TM95.
Definition tm := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_1LD0RF_0LB0LA".
Definition tm' := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_1LD0RD_0LB0LA".
Definition tm0 := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Ln_1RS---_1Lh0Ln_0R[0Lp_0RJ1Ln_0RT1Lp_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0L`1LG_0RS1R[_1L`1RJ_1LN1RT_1Lh0RJ_0R[0RL_1LG1RJ_0Lp1RL_0Lf1RY_0Lh0LG_1Lf1RR_1Lh1LG_1L`0Ri_1LN0Rk_1LN1Ri_---1Rk_0L^1Lh_0L`0LN_1L^0RJ_1L`1LN_0RY0R[_0LO---_1RY0Lp_0LG---_0LM0LE_0LO0LG_1LM1LE_1LO1LG".
Definition tm0' := TM'_from_str "0RR---_1LO---_1RR---_1LG---_0LN---_0LP---_1LN---_1LP---_0RQ0RJ_0RS1LN_1RQ1Ln_1RS---_1Lh0Ln_0R[0Lp_0RJ1Ln_0RT1Lp_0RY0RR_0R[0RT_1RY1RR_1R[1RT_0L`1LG_0RS1R[_1L`1RJ_1LN1RT_1Lh0RJ_0RJ0RL_1LG1RJ_1RJ1RL_0Lf1RY_0Lh0LG_1Lf1RR_1Lh1LG_1L`0RY_1LN0R[_1LN1RY_---1R[_0L^0L`_0L`0RS_1L^1L`_1L`1LN_0RY0R[_0LO---_1RY0Lp_0LG---_0LM0LE_0LO0LG_1LM1LE_1LO1LG".
Definition tm1 := TM'_from_str "1RB1RK_1LC---_---1LD_0RE0LG_1LJ1RF_0RA1LD_1LH1LJ_0RF1LI_0LH0LJ_1LD---_0RE0RL_1RE---".
Definition tm2 := TM'_from_str "1RB1RK_1LC---_---1LD_0RE0LG_1LJ1RF_0RA1LD_1LH1LJ_0RF1LI_0LH0LJ_1LD1RM_0RE0RL_1RE---_1RM1RM".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "SYhN[JpOnGRT".
Definition mp' := mp_from_str "SYhN[JpOnGRT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 true) 44 44.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM95.


