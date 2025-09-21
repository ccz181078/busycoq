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
    [ | solve_evstep (length l0) ];
    solve_cert cert
  | ];
  rewrite <-(TMinf.halts_evstep_iff _ TMinf.c0) in I2 by solve_evstep T.

Ltac solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' qn l0 cert T T' :=
  solve_v1 tm tm0 1%nat;
  solve_v1 tm' tm0' 1%nat;
  solve_v2 tm0 tm1 tm2 mp qn (const 0<*(rev l0),0,const 0)%N l0 cert T;
  solve_v2 tm0' tm1 tm2 mp' qn (const 0<*(rev l0),0,const 0)%N l0 cert T'.


Module TM1.
Definition tm := TM_from_str "1RB---_0RC0RF_0RD0RA_1RE0RD_1LF0LE_1RC0LE".
Definition tm' := TM_from_str "1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RI---_1RU---_0RI0RU_1RI1RU_0RM0RJ_0RA0LX_0RM0RA_1RM1RA_0RR0RF_0RM---_0RR0RM_1RR1RM_1LS0RR_0LS0RM_1RA0LX_1LS0LS_0LX0LS_1LX1LS_0RJ0LX_1RJ0LS_1RM0LS_1RA1LS".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RI---_1RU---_0RI0RU_1RI1RU_0RM0RJ_0RA0LX_0RM0RA_1RM1RA_0RR0RF_0RM---_0RR0RM_1RR0RJ_1LS0LG_0LS1LG_1RA0LX_1LS0LS_0LX0LS_1LX1LS_0RJ0LX_1RJ0LS_1RM0LS_1RA1LS".
Definition tm1 := TM'_from_str "1LB0LB_0LC0LB_1RD1LB_0RE---_1RF1RG_0RI0RD_0RH0LC_1RI1RD_0RA0RI".
Definition tm2 := TM'_from_str "1LB0LB_0LC0LB_1RD1LB_0RE1RJ_1RF1RG_0RI0RD_0RH0LC_1RI1RD_0RA0RI_1RJ1RJ".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "RSXAFIUJM".
Definition mp' := mp_from_str "RSXAFIUJM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM1.


Module TM2.
Definition tm := TM_from_str "1RB---_1LC1LB_1LD0LB_1RE0RB_1RF0RE_0RA0RC".
Definition tm' := TM_from_str "1RB---_1LC1LB_1LD0LB_1RE1LC_1RF0RE_0RA0RC".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LG---_1LH---_1LP1LL_1LG1LH_0LL0LH_1LL1LH_1RQ0LL_1LL0LH_0LP0LG_1LP1LG_0RR0RE_1RR1RE_1RV1LP_1RQ1LL_0RV0RQ_1RV1RQ_1RA0RV_1RI0RQ_0RA0RI_1RA1RI_0RF1RQ_---0LL".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LG---_1LH---_1LP1LL_1LG1LH_0LL0LH_1LL1LH_1RQ0LL_1LL0LH_0LP0LG_1LP1LG_0RR1LP_1RR1LG_1RV0LL_1RQ1LL_0RV0RQ_1RV1RQ_1RA0RV_1RI0RQ_0RA0RI_1RA1RI_0RF1RQ_---0LL".
Definition tm1 := TM'_from_str "1LB1LD_0LC0LD_1LE1LB_1LC1LD_1RF1LC_0RG0RF_1RI1RH_1RF0LC_0RA---".
Definition tm2 := TM'_from_str "1LB1LD_0LC0LD_1LE1LB_1LC1LD_1RF1LC_0RG0RF_1RI1RH_1RF0LC_0RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "FGLHPQVIA".
Definition mp' := mp_from_str "FGLHPQVIA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM2.


Module TM3.
Definition tm := TM_from_str "1RB---_1LC1LB_1LD0LB_1RE0RB_1RF0RE_1RA0RC".
Definition tm' := TM_from_str "1RB---_1LC1LB_1LD0LB_1RE1LC_1RF0RE_1RA0RC".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LG---_1LH---_1LP1LL_1LG1LH_0LL0LH_1LL1LH_1RQ0LL_1LL0LH_0LP0LG_1LP1LG_0RR0RE_1RR1RE_1RV1LP_1RQ1LL_0RV0RQ_1RV1RQ_1RB0RV_1RI0RQ_0RB0RI_1RB1RI_1RF1RQ_---0LL".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LG---_1LH---_1LP1LL_1LG1LH_0LL0LH_1LL1LH_1RQ0LL_1LL0LH_0LP0LG_1LP1LG_0RR1LP_1RR1LG_1RV0LL_1RQ1LL_0RV0RQ_1RV1RQ_1RB0RV_1RI0RQ_0RB0RI_1RB1RI_1RF1RQ_---0LL".
Definition tm1 := TM'_from_str "1LB1LC_0LD0LC_1LD1LC_1LE1LB_1RF1LD_0RG0RF_1RI1RH_1RF0LD_1RA---".
Definition tm2 := TM'_from_str "1LB1LC_0LD0LC_1LD1LC_1LE1LB_1RF1LD_0RG0RF_1RI1RH_1RF0LD_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "FGHLPQVIB".
Definition mp' := mp_from_str "FGHLPQVIB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM3.


Module TM4.
Definition tm := TM_from_str "1LB0LA_1RC0LA_0RF0RD_1RE---_0RC0RB_1RA0RF".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_0RF0RD_1RE---_0RC0RB_1RA0LE".
Definition tm0 := TM'_from_str "1RM0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1RU0LC_1RM1LC_0RU0RM_1RU1RM_0RB0RR_0RU---_0RR---_1RR---_1RI---_1RE---_0RI0RE_1RI1RE_0RU0RJ_0RM0LH_0RB0RU_1RB1RU_1LC0RB_0LC0RU".
Definition tm0' := TM'_from_str "1RM0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1RU0LC_1RM1LC_0RU0RM_1RU1RM_0RB0RR_0RU---_0RR---_1RR---_1RI---_1RE---_0RI0RE_1RI1RE_0RU0RJ_0RM0LH_0RB0RU_1RB0RJ_1LC0LS_0LC1LS".
Definition tm1 := TM'_from_str "0RB0RA_1LC0LC_0LD0LC_1RE1LC_0RF---_1RI1RG_0RH0LD_1RA1RE_0RA0RE".
Definition tm2 := TM'_from_str "0RB0RA_1LC0LC_0LD0LC_1RE1LC_0RF1RJ_1RI1RG_0RH0LD_1RA1RE_0RA0RE_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "UBCHMREJI".
Definition mp' := mp_from_str "UBCHMREJI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM4.


Module TM5.
Definition tm := TM_from_str "1LB1LE_1RC1LE_1LB1RD_0RE---_0RF1RF_0RB0LA".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_0RD---_0RE1RF_0RB0LA_0RB0LB".
Definition tm0 := TM'_from_str "1RN0LH_1LT0LT_0LH0LT_1LH1LT_0RJ0LH_1RJ0LT_1LT0LT_1RN1LT_1RN0RN_1LT1RN_0LH1RQ_1LH---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LT_0RE0LH_1RE0LT_0RJ0LC_0LH1LC".
Definition tm0' := TM'_from_str "1RJ0RJ_1LP1RJ_0LH1RM_1LH---_0RB0LH_1RB0LP_1LP0LP_1RJ1LP_0RM---_1RM---_0RQ---_0RV---_0RQ0RV_1RQ1RV_0RE1RE_0LH0LP_0RE0LH_1RE1RM_0RB0LC_0LH1LC_0RE1LP_1RE0LP_0RB0LG_0LH1LG".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE---_0RF0RH_0RG0LC_0RA0LC_1RG0LB".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE1RI_0RF0RH_0RG0LC_0RA0LC_1RG0LB_1RI1RI".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "JTHNQUEV".
Definition mp' := mp_from_str "BPHJMQEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM5.


Module TM6.
Definition tm := TM_from_str "1LB1RC_1RA1LD_0RD---_0RE1RF_0RB0LA_0RB0LB".
Definition tm' := TM_from_str "1LB1LE_1RC1LE_1LA1RD_0RE---_0RF1RF_0RB0LA".
Definition tm0 := TM'_from_str "1RJ0RJ_1LP1RJ_0LH1RM_1LH---_0RB0LH_1RB0LP_1LP0LP_1RJ1LP_0RM---_1RM---_0RQ---_0RV---_0RQ0RV_1RQ1RV_0RE1RE_0LH0LP_0RE0LH_1RE1RM_0RB0LC_0LH1LC_0RE1LP_1RE0LP_0RB0LG_0LH1LG".
Definition tm0' := TM'_from_str "1RN0LH_1LT0LT_0LH0LT_1LH1LT_0RJ0LH_1RJ0LT_1LT0LT_1RN1LT_1LH0RN_1LT1RN_0LD1RQ_1LD---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LT_0RE0LH_1RE0LT_0RJ0LC_0LH1LC".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE---_0RF0RH_0RG0LC_0RA0LC_1RG0LB".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE1RI_0RF0RH_0RG0LC_0RA0LC_1RG0LB_1RI1RI".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "BPHJMQEV".
Definition mp' := mp_from_str "JTHNQUEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM6.


Module TM7.
Definition tm := TM_from_str "1LB1LE_1RC1LE_1LA1RD_0RE---_0RF1RF_0RB0LA".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_1LB1RD_0RE---_0RF1RF_0RB0LA".
Definition tm0 := TM'_from_str "1RN0LH_1LT0LT_0LH0LT_1LH1LT_0RJ0LH_1RJ0LT_1LT0LT_1RN1LT_1LH0RN_1LT1RN_0LD1RQ_1LD---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LT_0RE0LH_1RE0LT_0RJ0LC_0LH1LC".
Definition tm0' := TM'_from_str "1RN0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1LC0LC_1RN1LC_1RN0RN_1LC1RN_0LH1RQ_1LH---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LC_0RE0LH_1RE0LC_0RJ0LC_0LH1LC".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE---_0RF0RH_0RG0LC_0RA0LC_1RG0LB".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE1RI_0RF0RH_0RG0LC_0RA0LC_1RG0LB_1RI1RI".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "JTHNQUEV".
Definition mp' := mp_from_str "JCHNQUEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM7.


Module TM8.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1LB1RD_0RE---_0RF1RF_0RB0LA".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_1LA1RD_0RE---_0RF1RF_0RB0LA".
Definition tm0 := TM'_from_str "1RN0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1LC0LC_1RN1LC_1RN0RN_1LC1RN_0LH1RQ_1LH---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LC_0RE0LH_1RE0LC_0RJ0LC_0LH1LC".
Definition tm0' := TM'_from_str "1RN0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1LC0LC_1RN1LC_1LH0RN_1LC1RN_0LD1RQ_1LD---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LC_0RE0LH_1RE0LC_0RJ0LC_0LH1LC".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE---_0RF0RH_0RG0LC_0RA0LC_1RG0LB".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE1RI_0RF0RH_0RG0LC_0RA0LC_1RG0LB_1RI1RI".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "JCHNQUEV".
Definition mp' := mp_from_str "JCHNQUEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM8.


Module TM9.
Definition tm := TM_from_str "1LB1LE_1RC0LA_1LA1RD_0RE---_0RF1RF_0RB0LA".
Definition tm' := TM_from_str "1LB0LA_1RC1LE_1LA1RD_0RE---_0RF1RF_0RB0LA".
Definition tm0 := TM'_from_str "1RN0LH_1LC0LT_0LH0LT_1LH1LT_0RJ0LH_1RJ0LT_1LT0LC_1RN1LC_1LH0RN_1LT1RN_0LD1RQ_1LD---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LT_0RE0LH_1RE0LT_0RJ0LC_0LH1LC".
Definition tm0' := TM'_from_str "1RN0LH_1LT0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1LC0LT_1RN1LT_1LH0RN_1LC1RN_0LD1RQ_1LD---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LC_0RE0LH_1RE0LC_0RJ0LC_0LH1LC".
Definition tm1 := TM'_from_str "1LB1RE_0LC0LB_1RE1LD_0LC0LB_1RF---_0RG0RI_0RH0LC_0RA0LC_1RH0LB".
Definition tm2 := TM'_from_str "1LB1RE_0LC0LB_1RE1LD_0LC0LB_1RF1RJ_0RG0RI_0RH0LC_0RA0LC_1RH0LB_1RJ1RJ".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "JTHCNQUEV".
Definition mp' := mp_from_str "JCHTNQUEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM9.


Module TM10.
Definition tm := TM_from_str "1LB1RC_1RA0LF_0RD---_0RE1RE_0RB0LF_1LB1LD".
Definition tm' := TM_from_str "1LB1RC_1RA1LD_0RD---_0RE1RE_0RB0LF_1LB0LF".
Definition tm0 := TM'_from_str "1RJ0RJ_1LW1RJ_0LH1RM_1LH---_0RB0LH_1RB0LP_1LW0LW_1RJ1LW_0RM---_1RM---_0RQ---_0RR---_0RQ0RR_1RQ1RR_0RE1RE_0LH0LP_0RE0LH_1RE0LP_0RB0LW_0LH1LW_1RJ0LH_1LW0LP_0LH0LP_1LH1LP".
Definition tm0' := TM'_from_str "1RJ0RJ_1LP1RJ_0LH1RM_1LH---_0RB0LH_1RB0LW_1LP0LP_1RJ1LP_0RM---_1RM---_0RQ---_0RR---_0RQ0RR_1RQ1RR_0RE1RE_0LH0LW_0RE0LH_1RE0LW_0RB0LW_0LH1LW_1RJ0LH_1LP0LW_0LH0LW_1LH1LW".
Definition tm1 := TM'_from_str "1LB1RE_0LC0LD_1RE1LB_0LC0LD_1RF---_0RG0RI_0RH0LC_0RA0LC_1RH0LD".
Definition tm2 := TM'_from_str "1LB1RE_0LC0LD_1RE1LB_0LC0LD_1RF1RJ_0RG0RI_0RH0LC_0RA0LC_1RH0LD_1RJ1RJ".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "BWHPJMQER".
Definition mp' := mp_from_str "BPHWJMQER".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM10.


Module TM11.
Definition tm := TM_from_str "1LB0RD_0LC0RC_1RD0LA_1RE1RF_0RA1RC_1LB---".
Definition tm' := TM_from_str "1LB0RD_0LC0RC_1RD0LA_1RE0RF_0RA1RC_0LA---".
Definition tm0 := TM'_from_str "1LK0RM_0LH1RM_0LH0RR_1LH0RV_1RR0RI_0LC1RI_0LK0RN_1LK0LH_0RN0LH_1RN0RR_1RR0LC_1RV1LC_0RR0RV_1RR1RV_1RA0LH_1RJ---_0RA0RJ_1RA1RJ_1LK1RN_0RM0RR_1LK---_0LH---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1LK0RM_0LH1RM_0LH0RR_1LH0RU_1RR0RI_0LC1RI_0LK0RN_1LK0LH_0RN0LH_1RN0RR_1RR0LC_1RU1LC_0RR0RU_1RR1RU_1RA0LH_1RJ---_0RA0RJ_1RA1RJ_1LK1RN_0RM0RR_0LH---_0RR---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB0RH_1RE0LC_0LD0RE_1LB0LD_1RA1RF_1RG0RE_1RE1RI_0RE0RI_0LD---".
Definition tm2 := TM'_from_str "1LB0RH_1RE0LC_0LD0RE_1LB0LD_1RA1RF_1RG0RE_1RE1RI_0RE0RI_0LD1RJ_1RJ1RJ".
Definition l0 := [1;1;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "AKCHRJNMV".
Definition mp' := mp_from_str "AKCHRJNMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 13 13.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM11.


Module TM12.
Definition tm := TM_from_str "1RB0RD_1RC---_1LD1LC_1LE0LC_1RF1LD_1RA0RF".
Definition tm' := TM_from_str "1RB0RD_1RC---_1LD1LC_1LE0LC_1RF0RC_1RA0RF".
Definition tm0 := TM'_from_str "0RF0RM_1RF1RM_1RJ1RU_---0LP_0RJ---_1RJ---_1LK---_1LL---_1LT1LP_1LK1LL_0LP0LL_1LP1LL_1RU0LP_1LP0LL_0LT0LK_1LT1LK_0RV1LT_1RV1LK_1RB0LP_1RU1LP_0RB0RU_1RB1RU_1RF0RB_1RM0RU".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1RJ1RU_---0LP_0RJ---_1RJ---_1LK---_1LL---_1LT1LP_1LK1LL_0LP0LL_1LP1LL_1RU0LP_1LP0LL_0LT0LK_1LT1LK_0RV0RI_1RV1RI_1RB1LT_1RU1LP_0RB0RU_1RB1RU_1RF0RB_1RM0RU".
Definition tm1 := TM'_from_str "1RB---_1LC1LD_0LE0LD_1LE1LD_1LF1LC_1RG1LE_0RH0RG_1RA1RI_1RG0LE".
Definition tm2 := TM'_from_str "1RB1RJ_1LC1LD_0LE0LD_1LE1LD_1LF1LC_1RG1LE_0RH0RG_1RA1RI_1RG0LE_1RJ1RJ".
Definition l0 := [1;0;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "FJKLPTUBM".
Definition mp' := mp_from_str "FJKLPTUBM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM12.


Module TM13.
Definition tm := TM_from_str "1RB0RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_0LC---".
Definition tm' := TM_from_str "1RB1RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_1LD---".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1RI0LP_1RR---_0RI0RR_1RI1RR_1LS1RB_0RA0RF_1LS0RA_0LP1RA_0LP0RF_1LP0RU_1RF0RQ_0LK1RQ_0LS0RB_1LS0LP_0RB0LP_1RB0RF_1RF0LK_1RU1LK_0LP---_0RF---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1RI0LP_1RR---_0RI0RR_1RI1RR_1LS1RB_0RA0RF_1LS0RA_0LP1RA_0LP0RF_1LP0RV_1RF0RQ_0LK1RQ_0LS0RB_1LS0LP_0RB0LP_1RB0RF_1RF0LK_1RV1LK_1LS---_0LP---_0LP---_1LP---".
Definition tm1 := TM'_from_str "1LB0RE_1RD0LC_0LF0RD_1RA1RG_0RD0RI_1LB0LF_1RH0RD_1RD1RI_0LF---".
Definition tm2 := TM'_from_str "1LB0RE_1RD0LC_0LF0RD_1RA1RG_0RD0RI_1LB0LF_1RH0RD_1RD1RI_0LF1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "ISKFAPRBU".
Definition mp' := mp_from_str "ISKFAPRBV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 14 14.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM13.


Module TM14.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RD1RD_0RE1RB_1RA1RF_1RD---".
Definition tm' := TM_from_str "1RB---_0RC1RE_1RD1RA_1LE0LE_0RF0LD_1RB0LE".
Definition tm0 := TM'_from_str "0RN0RN_1LC0LC_0LH0LG_1LH1LG_0RI0LH_1RI0LG_0RN0LC_0RN1LC_0RN0RN_1RN1RN_1RQ1RQ_1RF1RF_0RQ0RF_1RQ1RF_0RB1RI_0RV0LG_0RB0RV_1RB1RV_1LC1RN_0LC---_0RN---_1RN---_1RQ---_1RF---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RI---_1RR---_0RI0RR_1RI1RR_0RN1RU_0RB0LS_0RN0RB_1RN1RB_1LO1RF_0LO---_0RF0RF_1LO0LO_0LT0LS_1LT1LS_0RU0LT_1RU0LS_0RF0LO_0RF1LO_0RF0RF_1RF0LO_1RI0LS_1RR1LS".
Definition tm1 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF---_1RI0LE_0RF0RF".
Definition tm2 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF1RJ_1RI0LE_0RF0RF_1RJ1RJ".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "QBCHGNVFI".
Definition mp' := mp_from_str "INOTSFBRU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM14.


Module TM15.
Definition tm := TM_from_str "1RB---_0RC1RE_1RD1RA_1LE0LE_0RF0LD_1RB0LE".
Definition tm' := TM_from_str "1RB0LF_0RC1RE_1RD1RA_1LE0LE_0RA0LD_0RA---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RI---_1RR---_0RI0RR_1RI1RR_0RN1RU_0RB0LS_0RN0RB_1RN1RB_1LO1RF_0LO---_0RF0RF_1LO0LO_0LT0LS_1LT1LS_0RU0LT_1RU0LS_0RF0LO_0RF1LO_0RF0RF_1RF0LO_1RI0LS_1RR1LS".
Definition tm0' := TM'_from_str "0RF0RF_1RF---_1RI0LW_1RR1LW_0RI0RR_1RI1RR_0RN1RA_0RB0LS_0RN0RB_1RN1RB_1LO1RF_0LO---_0RF0RF_1LO0LO_0LT0LS_1LT1LS_0RA0LT_1RA0LS_0RF0LO_0RF1LO_0RA---_1RA---_0RF---_0RF---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF---_1RI0LE_0RF0RF".
Definition tm2 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF1RJ_1RI0LE_0RF0RF_1RJ1RJ".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "INOTSFBRU".
Definition mp' := mp_from_str "INOTSFBRA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM15.


Module TM16.
Definition tm := TM_from_str "1RB0LF_0RC1RE_1RD1RA_1LE0LE_0RA0LD_0RA---".
Definition tm' := TM_from_str "1LB1RC_0RA0LE_0RD1RB_1RE1RF_1LB0LB_1RC---".
Definition tm0 := TM'_from_str "0RF0RF_1RF---_1RI0LW_1RR1LW_0RI0RR_1RI1RR_0RN1RA_0RB0LS_0RN0RB_1RN1RB_1LO1RF_0LO---_0RF0RF_1LO0LO_0LT0LS_1LT1LS_0RA0LT_1RA0LS_0RF0LO_0RF1LO_0RA---_1RA---_0RF---_0RF---".
Definition tm0' := TM'_from_str "0RJ0RJ_1LS1RJ_0LH1RM_1LH1RF_0RA0LH_1RA0LG_0RJ0LS_0RJ1LS_0RM0RF_1RM1RF_0RR1RA_0RV0LG_0RR0RV_1RR1RV_1LS1RJ_0LS---_0RJ0RJ_1LS0LS_0LH0LG_1LH1LG_0RJ---_1RJ---_1RM---_1RF---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF---_1RI0LE_0RF0RF".
Definition tm2 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF1RJ_1RI0LE_0RF0RF_1RJ1RJ".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "INOTSFBRA".
Definition mp' := mp_from_str "MRSHGJVFA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM16.


Module TM17.
Definition tm := TM_from_str "1LB1RC_0RA0LE_0RD1RB_1RE1RF_1LB0LB_1RC---".
Definition tm' := TM_from_str "1LB0LB_0RC0LA_1RE1LD_0RA---_0RF1RB_1RA1RC".
Definition tm0 := TM'_from_str "0RJ0RJ_1LS1RJ_0LH1RM_1LH1RF_0RA0LH_1RA0LG_0RJ0LS_0RJ1LS_0RM0RF_1RM1RF_0RR1RA_0RV0LG_0RR0RV_1RR1RV_1LS1RJ_0LS---_0RJ0RJ_1LS0LS_0LH0LG_1LH1LG_0RJ---_1RJ---_1RM---_1RF---".
Definition tm0' := TM'_from_str "0RR0RR_1LC0LC_0LH0LG_1LH1LG_0RI0LH_1RI0LG_0RR0LC_0RR1LC_0RR0RR_1RR---_1RU0LP_1RF1LP_0RA---_1RA---_0RR---_0RR---_0RU0RF_1RU1RF_0RB1RI_0RJ0LG_0RB0RJ_1RB1RJ_1LC1RR_0LC---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF---_1RI0LE_0RF0RF".
Definition tm2 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF1RJ_1RI0LE_0RF0RF_1RJ1RJ".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "MRSHGJVFA".
Definition mp' := mp_from_str "UBCHGRJFI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM17.


Module TM18.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RE1LD_0RA---_0RF1RB_1RA1RC".
Definition tm' := TM_from_str "1LB0LC_0RA0LA_0RD0LA_1RE---_0RF1RB_1RA1RD".
Definition tm0 := TM'_from_str "0RR0RR_1LC0LC_0LH0LG_1LH1LG_0RI0LH_1RI0LG_0RR0LC_0RR1LC_0RR0RR_1RR---_1RU0LP_1RF1LP_0RA---_1RA---_0RR---_0RR---_0RU0RF_1RU1RF_0RB1RI_0RJ0LG_0RB0RJ_1RB1RJ_1LC1RR_0LC---".
Definition tm0' := TM'_from_str "0RR0RR_1LC0LC_0LH0LK_1LH1LK_0RA0LH_1RA0LK_0RR0LC_0RR1LC_0RM0LH_1RM0LK_0RR0LC_---1LC_0RR---_1RR---_1RU---_1RF---_0RU0RF_1RU1RF_0RB1RA_0RN0LK_0RB0RN_1RB1RN_1LC1RR_0LC---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF---_1RI0LE_0RF0RF".
Definition tm2 := TM'_from_str "0RB0RG_1LC0LC_0LD0LE_0RF1LC_0RF0LC_1RA1RH_1RF1RJ_1RI0LE_0RF0RF_1RJ1RJ".
Definition l0 := [0;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "UBCHGRJFI".
Definition mp' := mp_from_str "UBCHKRNFA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM18.


Module TM19.
Definition tm := TM_from_str "1RB0RE_1RC0RA_0RD0LC_1LE1RF_1LC---_0LF1RA".
Definition tm' := TM_from_str "1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_1RB0RE".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RA---_0RJ0RA_1RJ1RA_1RM0RF_0LK0RQ_0RM1LL_1RM0LK_1LL0LK_0RV1LK_1LL0RV_---1RV_0LT1RF_1LT1RB_0RV---_1LK---_0LL---_1LL---_0LW0RB_1RF1RB_0LW1RF_1LW1RQ".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1RJ1RF_1RU1RQ_0RJ0RU_1RJ1RU_1RM0RF_0LK0RQ_0RM1LL_1RM0LK_1LL0LK_0RB1LK_1LL0RB_---1RB_0LT1RF_1LT1RV_0RB---_1LK---_0LL---_1LL---_0RF0RQ_1RF1RQ_1RJ0RB_1RU---".
Definition tm1 := TM'_from_str "1RB0LD_1LC0RE_0RE1LD_1LC0LD_1RG1RF_1RG1RH_1RA1RI_0RE---_0RG0RH".
Definition tm2 := TM'_from_str "1RB0LD_1LC0RE_0RE1LD_1LC0LD_1RG1RF_1RG1RH_1RA1RI_0RE1RJ_0RG0RH_1RJ1RJ".
Definition l0 := [0;1;1;1;0;0;1;1]%N.
Definition mp := mp_from_str "JMLKVBFQA".
Definition mp' := mp_from_str "JMLKBVFQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM19.


Module TM20.
Definition tm := TM_from_str "1RB0RA_1RC0RE_1RD1LF_1LB---_1RA0LF_1LE1LF".
Definition tm' := TM_from_str "1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LE".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_1RQ0RA_0RJ0RQ_1RJ1RQ_1RN0RB_1LX0LT_0RN1LT_1RN1LX_0LT0LX_---1LX_1LX---_0LT---_0LH---_1LH---_0RB0LT_1RB0LX_1RF0LW_1RA1LW_1RA1LT_1LW1LX_0LT0LX_1LT1LX".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_1RU0RA_0RJ0RU_1RJ1RU_1RM0RB_1LT0LX_0RM1LX_1RM1LT_0LX0LT_---1LT_0LX---_0LT---_0LS---_1LS---_1RA1LX_1LS1LT_0LX0LT_1LX1LT_0RB0LX_1RB0LT_1RF0LS_1RA1LS".
Definition tm1 := TM'_from_str "0LB---_1RE1LC_0LB0LD_1LB1LD_0RF0RE_1RI1RG_0RH0LB_1RF1RE_1RA1LD".
Definition tm2 := TM'_from_str "0LB1RJ_1RE1LC_0LB0LD_1LB1LD_0RF0RE_1RI1RG_0RH0LB_1RF1RE_1RA1LD_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "NTWXAFQBJ".
Definition mp' := mp_from_str "MXSTAFUBJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM20.


Module TM21.
Definition tm := TM_from_str "1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LE".
Definition tm' := TM_from_str "1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_1RU0RA_0RJ0RU_1RJ1RU_1RM0RB_1LT0LX_0RM1LX_1RM1LT_0LX0LT_---1LT_0LX---_0LT---_0LS---_1LS---_1RA1LX_1LS1LT_0LX0LT_1LX1LT_0RB0LX_1RB0LT_1RF0LS_1RA1LS".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_1RU0RA_0RJ0RU_1RJ1RU_1RM0RB_1LT0LX_0RM1LX_1RM1LT_0LX0LT_---1LT_0LX---_0LT---_0LS---_1LS---_1RA1LX_1LK1LT_0LX0LT_1LX1LT_0RB0LX_1RB0LT_1RF0LK_1RA1LK".
Definition tm1 := TM'_from_str "0LB---_1RE1LC_0LB0LD_1LB1LD_0RF0RE_1RI1RG_0RH0LB_1RF1RE_1RA1LD".
Definition tm2 := TM'_from_str "0LB1RJ_1RE1LC_0LB0LD_1LB1LD_0RF0RE_1RI1RG_0RH0LB_1RF1RE_1RA1LD_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "MXSTAFUBJ".
Definition mp' := mp_from_str "MXKTAFUBJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM21.


Module TM22.
Definition tm := TM_from_str "1LB0LA_0RB1LC_1RD0LA_1RE0RD_1RA1RF_---0RC".
Definition tm' := TM_from_str "1LB0LA_1RC1LE_1RD0RC_1RA1RF_1RC0LA_---0RE".
Definition tm0 := TM'_from_str "1RM0LH_1LL0LC_0LH0LC_1LH1LC_0RE1RM_1RE1LC_0RE0LL_1RM1LL_0RN0LH_1RN0LC_1RR0LC_1RM1LC_0RR0RM_1RR1RM_1RB0RR_1RV0RM_0RB0RV_1RB1RV_1LL---_0LC1RI_---0RI_---1RI_---0RN_---0LH".
Definition tm0' := TM'_from_str "1RI0LH_1LT0LC_0LH0LC_1LH1LC_0RJ1RI_1RJ1LC_1RN0LT_1RI1LT_0RN0RI_1RN1RI_1RB0RN_1RV0RI_0RB0RV_1RB1RV_1LT---_0LC1RQ_0RJ0LH_1RJ0LC_1RN0LC_1RI1LC_---0RQ_---1RQ_---0RJ_---0LH".
Definition tm1 := TM'_from_str "1LB0LC_1RE1LC_0LD0LC_1RE1LB_0RF0RE_1RA1RG_---1RH_0RI0LD_1RF1RE".
Definition tm2 := TM'_from_str "1LB0LC_1RE1LC_0LD0LC_1RE1LB_0RF0RE_1RA1RG_1RJ1RH_0RI0LD_1RF1RE_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "BLCHMRVIN".
Definition mp' := mp_from_str "BTCHINVQJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM22.


Module TM23.
Definition tm := TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LB_1LC---".
Definition tm' := TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1LG0RF_1RQ0RA_1LO0RQ_1LG1RQ_0LL0RB_1LL0LL_0LD0LL_0LX0RB_0LO0LG_1LO1LG_1RQ1LL_0RA---_0LD0LX_1LD1LX_0RB0LL_1RB0RB_1RF0LG_1RA1LG_1LO---_1LG---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1LG0RF_1RQ0RA_1LO0RQ_1LG1RQ_0LL0RB_1LL0LL_0LD0LL_0LX0RB_0LO0LG_1LO1LG_1RQ1LL_0RA---_0LD0LX_1LD1LX_0RB0LL_1RB---_1RF0LW_1RA1LW_1LO---_1LG---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RH_0LD0RI_1LE1LC_0LG0LF_1LD---_1RH0RA_0RI0LD_1RB1RA".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RH_0LD0RI_1LE1LC_0LG0LF_1LD1RJ_1RH0RA_0RI0LD_1RB1RA_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "AFGLOXDQB".
Definition mp' := mp_from_str "AFGLOXDQB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM23.


Module TM24.
Definition tm := TM_from_str "1RB0LD_0RC0RE_1RD0LF_1LA0LD_1RF---_0RB0RA".
Definition tm' := TM_from_str "1RB0LD_0RC0RE_1RD0RC_1LA0LD_1RF---_0RB0RA".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LO_1RI0LO_1RQ1LO_0RI0RQ_1RI1RQ_0RN0RV_0RI---_0RN0RI_1RN0RF_1LO0LW_0LO1LW_1RQ0LD_1LO0LO_0LD0LO_1LD1LO_0RV---_1RV---_1RE---_1RA---_0RE0RA_1RE1RA_0RI0RF_0RQ0LD".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LO_1RI0LO_1RQ1LO_0RI0RQ_1RI1RQ_0RN0RV_0RI---_0RN0RI_1RN1RI_1LO0RN_0LO0RI_1RQ0LD_1LO0LO_0LD0LO_1LD1LO_0RV---_1RV---_1RE---_1RA---_0RE0RA_1RE1RA_0RI0RF_0RQ0LD".
Definition tm1 := TM'_from_str "0RB0RA_1LC0LC_0LD0LC_1RE1LC_0RF---_1RI1RG_0RH0LD_1RA1RE_0RA0RE".
Definition tm2 := TM'_from_str "0RB0RA_1LC0LC_0LD0LC_1RE1LC_0RF1RJ_1RI1RG_0RH0LD_1RA1RE_0RA0RE_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "INODQVAFE".
Definition mp' := mp_from_str "INODQVAFE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM24.


Module TM25.
Definition tm := TM_from_str "1RB---_0RC0RE_1RD1RA_1LE0LD_1RB0LF_1LD0RE".
Definition tm' := TM_from_str "1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RI---_1RQ---_0RI0RQ_1RI1RQ_0RN0RF_0RB0LP_0RN0RB_1RN1RB_1LW1RF_0LO---_1RQ0LT_1LW0LO_0LT0LO_1LT1LO_0RF0LP_1RF0RF_1RI0LW_1RQ1LW_1LT0RQ_1LO1RQ_0LP0RF_1LP0LP".
Definition tm0' := TM'_from_str "0RF0LP_1RF0RF_1RI0LS_1RA1LS_0RI0RA_1RI1RA_0RN0RF_0RV0LP_0RN0RV_1RN1RV_1LS1RF_0LO---_1RA0LD_1LS0LO_0LD0LO_1LD1LO_1LD0RU_1LO1RU_0LP0RF_1LP---_0RF---_1RF---_1RI---_1RA---".
Definition tm1 := TM'_from_str "1LB0LD_0LC0RG_1LE1LD_0LE0LD_1RF1LB_0RG0LC_1RH1RF_0RA0RI_1RG---".
Definition tm2 := TM'_from_str "1LB0LD_0LC0RG_1LE1LD_0LE0LD_1RF1LB_0RG0LC_1RH1RF_0RA0RI_1RG1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NWPOTQFIB".
Definition mp' := mp_from_str "NSPODAFIV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM25.


Module TM26.
Definition tm := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_1LC0RD".
Definition tm' := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD0LC".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_---1RV_0LP1RM_1LP1RM_1RI0RE_0LS1RE_0LC0RI_1LC---_0RI0LC_1RI0RI_1LC0LO_0RV1LO_1LP0RM_1RM1RM_0LL1RI_1LL0RE".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_---1RV_0LP1RM_1LP1RM_1RI0RE_0LS1RE_0LC0RI_1LC---_0RI0LC_1RI0RI_1LC0LO_0RV1LO_0RM0LP_1RM1RM_1RI0LK_0RE1LK".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICSOVME".
Definition mp' := mp_from_str "ICSOVME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM26.


Module TM27.
Definition tm := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD0LC".
Definition tm' := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD0RD".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_---1RV_0LP1RM_1LP1RM_1RI0RE_0LS1RE_0LC0RI_1LC---_0RI0LC_1RI0RI_1LC0LO_0RV1LO_0RM0LP_1RM1RM_1RI0LK_0RE1LK".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_---1RV_0LP1RM_1LP1RM_1RI0RE_0LS1RE_0LC0RI_1LC---_0RI0LC_1RI0RI_1LC0LO_0RV1LO_0RM0RM_1RM1RM_1RI1RI_0RE0RE".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICSOVME".
Definition mp' := mp_from_str "ICSOVME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM27.


Module TM28.
Definition tm := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD0RD".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0RD_0RC---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_---1RV_0LP1RM_1LP1RM_1RI0RE_0LS1RE_0LC0RI_1LC---_0RI0LC_1RI0RI_1LC0LO_0RV1LO_0RM0RM_1RM1RM_1RI1RI_0RE0RE".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RM_1LP1RM_1RI0RU_0LG1RU_0LC0RI_1LC---_0RM0RM_1RM1RM_1RI1RI_0RU0RU_0RI---_1RI---_1LC---_0RR---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICSOVME".
Definition mp' := mp_from_str "ICGORMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM28.


Module TM29.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0RD_0RC---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1LC0RD_0RC---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RM_1LP1RM_1RI0RU_0LG1RU_0LC0RI_1LC---_0RM0RM_1RM1RM_1RI1RI_0RU0RU_0RI---_1RI---_1LC---_0RR---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RM_1LP1RM_1RI0RU_0LG1RU_0LC0RI_1LC---_1LP0RM_1RM1RM_0LL1RI_1LL0RU_0RI---_1RI---_1LC---_0RR---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORMU".
Definition mp' := mp_from_str "ICGORMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM29.


Module TM30.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1LC0RD_0RC---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RM_1LP1RM_1RI0RU_0LG1RU_0LC0RI_1LC---_1LP0RM_1RM1RM_0LL1RI_1LL0RU_0RI---_1RI---_1LC---_0RR---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RM_1LP1RM_1RI0RU_0LG1RU_0LC0RI_1LC---_0RM0LP_1RM1RM_1RI0LK_0RU1LK_0RI---_1RI---_1LC---_0RR---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RF_1RA0RG_0RA1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORMU".
Definition mp' := mp_from_str "ICGORMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM30.


Module TM31.
Definition tm := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RE_0RC0LD_0RD1RB".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0LE---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_0LC1RV_0LP1RM_1LP1RF_1RI0RQ_0LS1RQ_0LC0RI_1LC0LC_0RI0LC_1RI0RI_1LC0LO_0RV1LO_0RM0RF_1RM1RF_1RI1RI_0RQ---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RU_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RU_1RM1RU_1RI1RI_0RE---_1RI---_1RI---_0LS---_1LS---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICSOVMQF".
Definition mp' := mp_from_str "ICGORMEU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM31.


Module TM32.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0LE---".
Definition tm' := TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA---_0RF0RD_0LA0RB".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RU_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RU_1RM1RU_1RI1RI_0RE---_1RI---_1RI---_0LS---_1LS---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LW_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LW_0RR1LW_1LC0RR_---1RR_0LP1RU_1LP1RM_1RI---_0LG---_0LC---_1LC---_0RU0RM_1RU1RM_1RI1RI_0RE---_1RI0RE_0LG1RE_0LC0RI_1LC0LC".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORMEU".
Definition mp' := mp_from_str "ICGWRUEM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM32.


Module TM33.
Definition tm := TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA---_0RF0RD_0LA0RB".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0RC---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LW_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LW_0RR1LW_1LC0RR_---1RR_0LP1RU_1LP1RM_1RI---_0LG---_0LC---_1LC---_0RU0RM_1RU1RM_1RI1RI_0RE---_1RI0RE_0LG1RE_0LC0RI_1LC0LC".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RV_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RV_1RM1RV_1RI1RI_0RE---_0RI---_1RI---_1LC---_0RR---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGWRUEM".
Definition mp' := mp_from_str "ICGORMEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM33.


Module TM34.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0RC---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0LA---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RV_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RV_1RM1RV_1RI1RI_0RE---_0RI---_1RI---_1LC---_0RR---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RU_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RU_1RM1RU_1RI1RI_0RE---_1RI---_0LG---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORMEV".
Definition mp' := mp_from_str "ICGORMEU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM34.


Module TM35.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1LD---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0LB---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RU_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RU_1RM1RU_1RI1LC_0RE---_1LC---_0LC---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RU_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RU_1RM1RU_1RI1LC_0RE---_1LC---_0LO---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1LB---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORMEU".
Definition mp' := mp_from_str "ICGORMEU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM35.


Module TM36.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0LC---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0LE1RF_0RD---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RV_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RV_1RM1RV_1RI1RM_0RE---_0LP---_1RM---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RV_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0LS0RV_1RM1RV_0LS1RM_1LS---_0RM---_1RM---_1RI---_0RE---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RF---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RF1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORMEV".
Definition mp' := mp_from_str "ICGORMEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM36.


Module TM37.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0LE1RF_0RD---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0RD---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RV_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0LS0RV_1RM1RV_0LS1RM_1LS---_0RM---_1RM---_1RI---_0RE---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_0LC1RR_0LP1RM_1LP1RV_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RV_1RM1RV_1RI1RM_0RE---_0RM---_1RM---_1RI---_0RE---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RF---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA0LB_1RF1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORMEV".
Definition mp' := mp_from_str "ICGORMEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM37.


Module TM38.
Definition tm := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD1RE".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_---1RV_0LP1RM_1LP1RR_1RI0RE_0LS1RE_0LC0RI_1LC---_0RI0LC_1RI0RI_1LC0LO_0RV1LO_0RM0RR_1RM1RR_1RI1RI_0RE0RI".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RM_1LP1RF_1RI0RU_0LG1RU_0LC0RI_1LC---_0RM0RF_1RM1RF_1RI1RI_0RU0RI_0RI---_1RI---_1LC---_0RR---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA---_1RA0RA".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA1RI_1RA0RA_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICSOVMER".
Definition mp' := mp_from_str "ICGORMUF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM38.


Module TM39.
Definition tm := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD1RB".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LS_---1LS_0RI---_1RI---_1LC---_0RV---_1LC0RV_---1RV_0LP1RM_1LP1RF_1RI0RE_0LS1RE_0LC0RI_1LC---_0RI0LC_1RI0RI_1LC0LO_0RV1LO_0RM0RF_1RM1RF_1RI1RI_0RE---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_0RI1LG_0RI0LC_1RI0RI_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RM_1LP1RV_1RI0RU_0LG1RU_0LC0RI_1LC---_0RM0RV_1RM1RV_1RI1RI_0RU---_0RI---_1RI---_1LC---_0RR---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA---_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB0RA_1RF1RH_1RA0RG_0RA1RI_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICSOVMEF".
Definition mp' := mp_from_str "ICGORMUV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM39.


Module TM40.
Definition tm := TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LA---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_0RF0RD_0LA0RB".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LW_1RI0LG_---1LG_0RI0LC_1RI---_1LC0LW_0RR1LW_1LC0RR_0LC1RR_0LP1RM_1LP1RF_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RF_1RM1RF_1RI1RI_0RE---_1RI---_0LG---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_---1LG_0RI0LC_1RI---_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RU_1LP1RM_1RI---_0LG---_0LC---_1LC---_0RU0RM_1RU1RM_1RI1RI_0RE---_1RI0RE_0LG1RE_0LC0RI_1LC0LC".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB---_1RF1RH_1RA0RG_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RI_1RF1RH_1RA0RG_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGWRMEF".
Definition mp' := mp_from_str "ICGORUEM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM40.


Module TM41.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_0RF0RD_0LA0RB".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_0RF1RB_0LA0RB".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_---1LG_0RI0LC_1RI---_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RU_1LP1RM_1RI---_0LG---_0LC---_1LC---_0RU0RM_1RU1RM_1RI1RI_0RE---_1RI0RE_0LG1RE_0LC0RI_1LC0LC".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_---1LG_0RI0LC_1RI---_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RU_1LP1RF_1RI---_0LG---_0LC---_1LC---_0RU0RF_1RU1RF_1RI1RI_0RE---_1RI0RE_0LG1RE_0LC0RI_1LC0LC".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB---_1RF1RH_1RA0RG_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RI_1RF1RH_1RA0RG_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORUEM".
Definition mp' := mp_from_str "ICGORUEF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM41.


Module TM42.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_0RF1RB_0LA0RB".
Definition tm' := TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LO_1RI0LG_---1LG_0RI0LC_1RI---_1LC0LO_0RR1LO_1LC0RR_---1RR_0LP1RU_1LP1RF_1RI---_0LG---_0LC---_1LC---_0RU0RF_1RU1RF_1RI1RI_0RE---_1RI0RE_0LG1RE_0LC0RI_1LC0LC".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LW_1RI0LG_---1LG_0RI0LC_1RI---_1LC0LW_0RR1LW_1LC0RR_0LC1RR_0LP1RM_1LP1RU_1RI0RE_0LG1RE_0LC0RI_1LC0LC_0RM0RU_1RM1RU_1RI1RI_0RE---_1RI---_0LG---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB---_1RF1RH_1RA0RG_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "1LB0RE_1RA0LC_1LB0LD_0LB1RI_1RF1RH_1RA0RG_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGORUEF".
Definition mp' := mp_from_str "ICGWRMEU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM42.


Module TM43.
Definition tm := TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_0LC---".
Definition tm' := TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_1RB---".
Definition tm0 := TM'_from_str "0RF1LC_1RF1RI_1RI0LS_1RQ1LS_0RI0RQ_1RI1RQ_1LC0RI_0RB0RM_1LC0RB_---1RB_0LP1RF_1LP1RI_1RI0RV_0LS1RV_0LC1RF_1LC---_0RI0RM_1RI1RM_1LC1RI_0RB0RV_0LP---_1RF---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF1LC_1RF1RI_1RI0LS_1RQ1LS_0RI0RQ_1RI1RQ_1LC0RI_0RB0RM_1LC0RB_---1RB_0LP1RF_1LP1RI_1RI0RV_0LS1RV_0LC1RF_1LC---_0RI0RM_1RI1RM_1LC1RI_0RB0RV_0RF---_1RF---_1RI---_1RQ---".
Definition tm1 := TM'_from_str "1LB0RD_1RA0LC_1LB1RA_1RE1RA_1RA1RF_0RA0RG_1RA0RH_1RE---".
Definition tm2 := TM'_from_str "1LB0RD_1RA0LC_1LB1RA_1RE1RA_1RA1RF_0RA0RG_1RA0RH_1RE1RI_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ICSBFQMV".
Definition mp' := mp_from_str "ICSBFQMV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM43.


Module TM44.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF0LF_0RB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LB---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV---_1RE0LW_---1LW_0RE---_1RE---_1LD---_0RN---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV1LK_1RE0LL_---1LL_1LL---_1RE---_0LH---_1LH---".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LC_1RF1RE_1LC0RD_1RA1RG_0RH1LC_1RE---".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LC_1RF1RE_1LC0RD_1RA1RG_0RH1LC_1RE1RI_1RI1RI".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "FKDNEBQV".
Definition mp' := mp_from_str "FKDNEBQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM44.


Module TM45.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0RB---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV1LK_1RE0LL_---1LL_1LL---_1RE---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV1LK_1RE0LL_---1LL_0RE---_1RE---_1LD---_0RN---".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LC_1RF1RE_1LC0RD_1RA1RG_0RH1LC_1RE---".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LC_1RF1RE_1LC0RD_1RA1RG_0RH1LC_1RE1RI_1RI1RI".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "FKDNEBQV".
Definition mp' := mp_from_str "FKDNEBQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM45.


Module TM46.
Definition tm := TM_from_str "1LB0LF_1RC1RE_1LA1RD_0LB---_0RB0LA_1LE1RF".
Definition tm' := TM_from_str "1LB0LE_1RC1RF_1LA1RD_0RB---_1LF1RE_0RB0LA".
Definition tm0 := TM'_from_str "1RN0LT_0LW1LC_0LH0LW_1LH1LW_0RJ0RR_1RJ1RR_1LW1RE_1RN0LW_1LH0RN_1LW1RN_0LD1RE_1LD---_1LW---_1RE---_0LG---_1LG---_0RE0LH_1RE0LW_0RJ0LC_0RR1LC_0RR0RV_1LC1RV_0LT1LC_1LT1RV".
Definition tm0' := TM'_from_str "1RN0LX_0LS1LC_0LH0LS_1LH1LS_0RJ0RV_1RJ1RV_1LS1RE_1RN0LS_1LH0RN_1LS1RN_0LD1RE_1LD---_0RE---_1RE---_0RJ---_0RV---_0RV0RR_1LC1RR_0LX1LC_1LX1RR_0RE0LH_1RE0LS_0RJ0LC_0RV1LC".
Definition tm1 := TM'_from_str "1LB1RH_0LC1LD_0RF1LD_0LE0LB_1RH0LB_1RG0LB_0RA0RF_1RG---".
Definition tm2 := TM'_from_str "1LB1RH_0LC1LD_0RF1LD_0LE0LB_1RH0LB_1RG0LB_0RA0RF_1RG1RI_1RI1RI".
Definition l0 := [0;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "JWTCHREN".
Definition mp' := mp_from_str "JSXCHVEN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM46.


Module TM47.
Definition tm := TM_from_str "1RB0RA_1RC0RE_1RD---_1LE1LD_1LF0LD_1RA0RD".
Definition tm' := TM_from_str "1RB0RA_1RC0RE_1RD---_1LE1LD_1LF0LD_1RA1LE".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_1RQ0RA_0RJ0RQ_1RJ1RQ_1RN1RA_---0LT_0RN---_1RN---_1LO---_1LP---_1LX1LT_1LO1LP_0LT0LP_1LT1LP_1RA0LT_1LT0LP_0LX0LO_1LX1LO_0RB0RM_1RB1RM_1RF1LX_1RA1LT".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_1RQ0RA_0RJ0RQ_1RJ1RQ_1RN1RA_---0LT_0RN---_1RN---_1LO---_1LP---_1LX1LT_1LO1LP_0LT0LP_1LT1LP_1RA0LT_1LT0LP_0LX0LO_1LX1LO_0RB1LX_1RB1LO_1RF0LT_1RA1LT".
Definition tm1 := TM'_from_str "1RB1RI_1RC---_1LD1LE_0LF0LE_1LF1LE_1LG1LD_1RH1LF_0RA0RH_1RH0LF".
Definition tm2 := TM'_from_str "1RB1RI_1RC1RJ_1LD1LE_0LF0LE_1LF1LE_1LG1LD_1RH1LF_0RA0RH_1RH0LF_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "FJNOPTXAQ".
Definition mp' := mp_from_str "FJNOPTXAQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM47.


Module TM48.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1LD0LC_1LA0RE_1RF0RB_1RA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA0RE_1RF0RB_1RA---".
Definition tm0 := TM'_from_str "0RF1RR_1RF1LD_1LK0LD_1RR1LD_1LP0RR_1LK1RR_0LL1RV_1LL1RE_1LD0LP_0RE0LK_0LP0LK_1LP1LK_1RR0RQ_1LD1RQ_0LD0RV_1LD0RE_0RV0RE_1RV1RE_1RB1LP_---0RR_0RB---_1RB---_1RF---_1LD---".
Definition tm0' := TM'_from_str "0RF1RR_1RF1LD_1LK0LD_1RR1LD_1LP0RR_1LK1RR_0LL1RV_1LL1RE_1LD0LP_0RE0LK_0LP0LK_1LP1LK_0RB0RQ_1RB1RQ_1RF0RV_1LD0RE_0RV0RE_1RV1RE_1RB1LP_---0RR_0RB---_1RB---_1RF---_1LD---".
Definition tm1 := TM'_from_str "1LB1RE_0LC0LB_1LD0RF_1RE1LD_1RG1RF_1LC0RE_1RH---_1RA1LD".
Definition tm2 := TM'_from_str "1LB1RE_0LC0LB_1LD0RF_1RE1LD_1RG1RF_1LC0RE_1RH1RI_1RA1LD_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "FKPDREVB".
Definition mp' := mp_from_str "FKPDREVB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM48.


Module TM49.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1RD0RE_1LC---_1LA0LF_1LE1LF".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1RD0RE_0LA---_1LA0LF_1LE1LF".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LW_1RJ0LT_1RE1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RQ0RE_0RN0RQ_1RN1RQ_0LT1RE_---0LT_------_0LT---_0LL---_1LL---_1RE0LT_1LT0LX_0LD0LW_1LD1LW_1LD1LT_1LW1LX_0LT0LX_1LT1LX".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LW_1RJ0LT_1RE1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RQ0RE_0RN0RQ_1RN1RQ_0LT1RE_---0LT_1RJ---_0LT---_0LC---_1LC---_1RE0LT_1LT0LX_0LD0LW_1LD1LW_1LD1LT_1LW1LX_0LT0LX_1LT1LX".
Definition tm1 := TM'_from_str "0LB---_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB".
Definition tm2 := TM'_from_str "0LB1RI_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB_1RI1RI".
Definition l0 := [1;0;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "NTWXDEJQ".
Definition mp' := mp_from_str "NTWXDEJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM49.


Module TM50.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1RD0RE_0LA---_1LA0LF_1LE1LF".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0RD0RF_0LE---_1LF1LE_1LA0LE".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LW_1RJ0LT_1RE1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RQ0RE_0RN0RQ_1RN1RQ_0LT1RE_---0LT_1RJ---_0LT---_0LC---_1LC---_1RE0LT_1LT0LX_0LD0LW_1LD1LW_1LD1LT_1LW1LX_0LT0LX_1LT1LX".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LS_1RJ0LX_1RE1LX_0RJ0RE_1RJ1RE_1RM0RJ_1RU0RE_0RM0RU_1RM1RU_0LX1RE_---0LX_0LX---_0LT---_0LS---_1LS---_1LD1LX_1LS1LT_0LX0LT_1LX1LT_1RE0LX_1LX0LT_0LD0LS_1LD1LS".
Definition tm1 := TM'_from_str "0LB---_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB".
Definition tm2 := TM'_from_str "0LB1RI_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB_1RI1RI".
Definition l0 := [1;0;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "NTWXDEJQ".
Definition mp' := mp_from_str "MXSTDEJU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM50.


Module TM51.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0RD0RF_0LE---_1LF1LE_1LA0LE".
Definition tm' := TM_from_str "1RB0RF_1RC0RB_1RD0RE_1LC---_1LA0LF_1LE1LF".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LS_1RJ0LX_1RE1LX_0RJ0RE_1RJ1RE_1RM0RJ_1RU0RE_0RM0RU_1RM1RU_0LX1RE_---0LX_0LX---_0LT---_0LS---_1LS---_1LD1LX_1LS1LT_0LX0LT_1LX1LT_1RE0LX_1LX0LT_0LD0LS_1LD1LS".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1RJ1LD_1RE1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RQ0RE_0RN0RQ_1RN1RQ_0LT1RE_---0LT_------_0LT---_0LL---_1LL---_1RE0LT_1LT0LX_0LD0LW_1LD1LW_1LD1LT_1LW1LX_0LT0LX_1LT1LX".
Definition tm1 := TM'_from_str "0LB---_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB".
Definition tm2 := TM'_from_str "0LB1RI_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB_1RI1RI".
Definition l0 := [1;0;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "MXSTDEJU".
Definition mp' := mp_from_str "NTWXDEJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM51.


Module TM52.
Definition tm := TM_from_str "1RB0RF_1RC0RB_1RD0RE_1LC---_1LA0LF_1LE1LF".
Definition tm' := TM_from_str "1RB0RE_1RC0RB_0RD0RF_0LE---_1LF1LE_1LA0LE".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1RJ1LD_1RE1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RQ0RE_0RN0RQ_1RN1RQ_0LT1RE_---0LT_------_0LT---_0LL---_1LL---_1RE0LT_1LT0LX_0LD0LW_1LD1LW_1LD1LT_1LW1LX_0LT0LX_1LT1LX".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ1LD_1RE1LX_0RJ0RE_1RJ1RE_1RM0RJ_1RU0RE_0RM0RU_1RM1RU_0LX1RE_---0LX_0LX---_0LT---_0LS---_1LS---_1LD1LX_1LS1LT_0LX0LT_1LX1LT_1RE0LX_1LX0LT_0LD0LS_1LD1LS".
Definition tm1 := TM'_from_str "0LB---_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB".
Definition tm2 := TM'_from_str "0LB1RI_1LE1LC_0LB0LD_1LB1LD_1RF1LB_0RG0RF_1RA1RH_1RF0LB_1RI1RI".
Definition l0 := [1;0;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "NTWXDEJQ".
Definition mp' := mp_from_str "MXSTDEJU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM52.


Module TM53.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RC---".
Definition tm' := TM_from_str "1LB0LE_0RC0LF_0LA1LD_1RE---_0RF0RE_1LC0RA".
Definition tm0 := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH1RI_0LK---_0LC0LX_1LC1LX_0RJ---_1RJ---_1RM---_1RI---".
Definition tm0' := TM'_from_str "1RQ1LC_1LW0RU_0LH0LS_1LH1LS_0RI0LL_1RI1RQ_0LH0LW_1RQ1LW_0LH1RQ_0LS---_0LC0LP_1LC1LP_0RR---_1RR---_1RU---_1RQ---_0RU0RQ_1RU1RQ_1LC0RU_0RA0RQ_1LC0RA_1LP1RA_0LL1RQ_1LL1LC".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "IMCHOTKAX".
Definition mp' := mp_from_str "QUCHWLSAP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM53.


Module TM54.
Definition tm := TM_from_str "1LB0LE_0RC0LF_0LA1LD_1RE---_0RF0RE_1LC0RA".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RB---".
Definition tm0 := TM'_from_str "1RQ1LC_1LW0RU_0LH0LS_1LH1LS_0RI0LL_1RI1RQ_0LH0LW_1RQ1LW_0LH1RQ_0LS---_0LC0LP_1LC1LP_0RR---_1RR---_1RU---_1RQ---_0RU0RQ_1RU1RQ_1LC0RU_0RA0RQ_1LC0RA_1LP1RA_0LL1RQ_1LL1LC".
Definition tm0' := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH1RI_0LK---_0LC0LX_1LC1LX_0RF---_1RF---_1RJ---_1RI---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "QUCHWLSAP".
Definition mp' := mp_from_str "IMCHOTKAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM54.


Module TM55.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RB---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RA---".
Definition tm0 := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH1RI_0LK---_0LC0LX_1LC1LX_0RF---_1RF---_1RJ---_1RI---".
Definition tm0' := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LW1RA_0LT1RI_1LT1LC_0LH1RI_0LK---_0LC0LW_1LC1LW_0RA---_1RA---_1RI---_1LC---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "IMCHOTKAX".
Definition mp' := mp_from_str "IMCHOTKAW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM55.


Module TM56.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_1RA---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RC---".
Definition tm0 := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH0RM_0LK---_0LC0LX_1LC1LX_0RB---_1RB---_1LO---_0RM---".
Definition tm0' := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LW1RA_0LT1RI_1LT1LC_0LH0RM_0LK---_0LC0LW_1LC1LW_0RI---_1RI---_0RM---_0RI---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0RB---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0RB1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "IMCHOTKAX".
Definition mp' := mp_from_str "IMCHOTKAW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM56.


Module TM57.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RD---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0LA---".
Definition tm0 := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LW1RA_0LT1RI_1LT1LC_0LH1LC_0LK---_0LC0LW_1LC1LW_0RM---_1RM---_1LC---_0RA---".
Definition tm0' := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH1LC_0LK---_0LC0LX_1LC1LX_0LH---_0LK---_0LC---_1LC---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "IMCHOTKAW".
Definition mp' := mp_from_str "IMCHOTKAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM57.


Module TM58.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0LA---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0RA---".
Definition tm0 := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH1LC_0LK---_0LC0LX_1LC1LX_0LH---_0LK---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH1LC_0LK---_0LC0LX_1LC1LX_0RA---_1RA---_1RI---_1LC---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "IMCHOTKAX".
Definition mp' := mp_from_str "IMCHOTKAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM58.


Module TM59.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA1LF_0RA---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0RE1LF_0LA---".
Definition tm0 := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0LH1LC_0LK---_0LC0LX_1LC1LX_0RA---_1RA---_1RI---_1LC---".
Definition tm0' := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LX1RA_0LT1RI_1LT1LC_0RQ1LC_1RQ---_0RQ0LX_1LC1LX_0LH---_0LK---_0LC---_1LC---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "IMCHOTKAX".
Definition mp' := mp_from_str "IMCHOTKAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM59.


Module TM60.
Definition tm := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_1LB---".
Definition tm' := TM_from_str "1LB0LC_1RC0LD_0RD0RC_1LE0RA_0LA0LF_0RE---".
Definition tm0 := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LW1RA_0LT1RI_1LT1LC_0LH0LH_0LK---_0LC0LW_1LC1LW_1RI---_1LO---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RI1LC_1LO0RM_0LH0LK_1LH1LK_0RJ0LT_1RJ1RI_1RM0LO_1RI1LO_0RM0RI_1RM1RI_1LC0RM_0RA0RI_1LC0RA_1LW1RA_0LT1RI_1LT1LC_0LH0LH_0LK---_0LC0LW_1LC1LW_0RQ---_1RQ---_0LH---_0LH---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0LD---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0LD1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "IMCHOTKAW".
Definition mp' := mp_from_str "IMCHOTKAW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM60.


Module TM61.
Definition tm := TM_from_str "1LB0LA_1RC0RF_0LD0RB_1LA1RE_0RD---_1RB0LD".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RF_1RB0LD_0RD---".
Definition tm0 := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RU_1RJ1RU_1RM0RF_1RE0LD_0LD0RE_1RM1RE_0LO0RJ_1LO0RU_1LH0RR_1LC1RR_0LD1RM_1LD---_0RM---_1RM---_1LH---_0RR---_0RF0LD_1RF1RM_1RJ0LO_1RU1LO".
Definition tm0' := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RV0RQ_1LH0RV_1LC1RV_0LD1RM_1LD---_0RF0LD_1RF1RM_1RJ0LO_1RQ1LO_0RM---_1RM---_1LH---_0RV---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1RB---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1RB1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JMHDCEUFR".
Definition mp' := mp_from_str "JMHDCEQFV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM61.


Module TM62.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RF_1RB0LD_0RD---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0LB---".
Definition tm0 := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RV0RQ_1LH0RV_1LC1RV_0LD1RM_1LD---_0RF0LD_1RF1RM_1RJ0LO_1RQ1LO_0RM---_1RM---_1LH---_0RV---".
Definition tm0' := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RU0RQ_1LH0RU_1LC1RU_0LD1RM_1LD---_0RF0LD_1RF1RM_1RJ0LO_1RQ1LO_1RM---_0RF---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1RB---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1RB1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JMHDCEQFV".
Definition mp' := mp_from_str "JMHDCEQFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM62.


Module TM63.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LF_1LA---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_1LA---".
Definition tm0 := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RU0RQ_1LH0RU_1LC1RU_0LD1LH_1LD---_0RF0LD_1RF---_1RJ0LW_1RQ1LW_1LH---_1LC---_0LD---_1LD---".
Definition tm0' := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RU0RQ_1LH0RU_1LC1RU_0LD1LH_1LD---_0RF0LD_1RF1LH_1RJ0LO_1RQ1LO_1LH---_1LC---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1LC---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JMHDCEQFU".
Definition mp' := mp_from_str "JMHDCEQFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM63.


Module TM64.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_1LA---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0LC---".
Definition tm0 := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RU0RQ_1LH0RU_1LC1RU_0LD1LH_1LD---_0RF0LD_1RF1LH_1RJ0LO_1RQ1LO_1LH---_1LC---_0LD---_1LD---".
Definition tm0' := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RU0RQ_1LH0RU_1LC1RU_0LD1LH_1LD---_0RF0LD_1RF1LH_1RJ0LO_1RQ1LO_1LH---_0RJ---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1LC---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JMHDCEQFU".
Definition mp' := mp_from_str "JMHDCEQFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM64.


Module TM65.
Definition tm := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RF_1RB0LD_1RB---".
Definition tm' := TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RE_1RB0LF_1LA---".
Definition tm0 := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RV0RQ_1LH0RV_1LC1RV_0LD1RF_1LD---_0RF0LD_1RF1RF_1RJ0LO_1RQ1LO_0RF---_1RF---_1RJ---_1RQ---".
Definition tm0' := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RQ_1RJ1RQ_1RM0RF_1RE0LD_0RM0RE_1RM1RE_1LH0RJ_0RR0RQ_1LH0RR_1LC1RR_0LD1RF_1LD---_0RF0LD_1RF---_1RJ0LW_1RQ1LW_1LH---_1LC---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1RH---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RI_1RF0LD_1LC1LE_0LC0LE_0RA0RG_0RH0LD_1RA1RG_1RH1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JMHDCEQFV".
Definition mp' := mp_from_str "JMHDCEQFR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM65.


Module TM66.
Definition tm := TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LB---".
Definition tm' := TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RD---".
Definition tm0 := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RU1LK_0RI0RU_1RI1RU_0RN0RN_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_0RN---_0RN---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RU1LK_0RI0RU_1RI1RU_0RN0RN_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_0RN---_1RN---_1LS---_1RA---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_0RA---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_0RA1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NSCKIAFQU".
Definition mp' := mp_from_str "NSCKIAFQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM66.


Module TM67.
Definition tm := TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LC---".
Definition tm' := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LE---".
Definition tm0 := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RU1LK_0RI0RU_1RI1RU_0RN1LS_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1LS---_1RI---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN1LS_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1LC---_1LS---_0LT---_1LT---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1LB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NSCKIAFQU".
Definition mp' := mp_from_str "NSCKIAFQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM67.


Module TM68.
Definition tm := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LE---".
Definition tm' := TM_from_str "1RB0LC_0RC1RE_1RD0RF_0LB0RA_1LF---_0LA0LF".
Definition tm0 := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN1LS_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1LC---_1LS---_0LT---_1LT---".
Definition tm0' := TM'_from_str "0RF1LW_1RF1RI_1RI0LK_1RR1LK_0RI0RR_1RI1RR_0RN1LW_0RU---_0RN0RU_1RN1RU_1LW1RI_1RA0LC_0RN0RA_1LW1RA_0LG0RF_1LG1LW_1LC---_1LW---_0LX---_1LX---_1RI0LC_0LK0LW_0LC0LW_1LC1LW".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1LB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NSCKIAFQV".
Definition mp' := mp_from_str "NWCKIAFUR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM68.


Module TM69.
Definition tm := TM_from_str "1RB0LC_0RC1RE_1RD0RF_0LB0RA_1LF---_0LA0LF".
Definition tm' := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---".
Definition tm0 := TM'_from_str "0RF1LW_1RF1RI_1RI0LK_1RR1LK_0RI0RR_1RI1RR_0RN1LW_0RU---_0RN0RU_1RN1RU_1LW1RI_1RA0LC_0RN0RA_1LW1RA_0LG0RF_1LG1LW_1LC---_1LW---_0LX---_1LX---_1RI0LC_0LK0LW_0LC0LW_1LC1LW".
Definition tm0' := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN1LS_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1LT---_1LS---_0LP---_1LP---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1LB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NWCKIAFUR".
Definition mp' := mp_from_str "NSCKIAFQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM69.


Module TM70.
Definition tm := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LC---".
Definition tm' := TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---".
Definition tm0 := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN0LC_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1RA---_0LC---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RU1LK_0RI0RU_1RI1RU_0RN0LC_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_0LC---_0LS---_0LS---_1LS---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_0LC---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_0LC1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NSCKIAFQV".
Definition mp' := mp_from_str "NSCKIAFQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM70.


Module TM71.
Definition tm := TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LA---".
Definition tm' := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RC---".
Definition tm0 := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RU1LK_0RI0RU_1RI1RU_0RN1RI_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1RI---_0LK---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN1RI_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_0RI---_1RI---_0RN---_0RQ---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1RE---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1RE1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NSCKIAFQU".
Definition mp' := mp_from_str "NSCKIAFQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM71.


Module TM72.
Definition tm := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RC---".
Definition tm' := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LC---".
Definition tm0 := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN1RI_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_0RI---_1RI---_0RN---_0RQ---".
Definition tm0' := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN1RI_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1LS---_1RI---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1RE---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1RE1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NSCKIAFQV".
Definition mp' := mp_from_str "NSCKIAFQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM72.


Module TM73.
Definition tm := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LC---".
Definition tm' := TM_from_str "1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF".
Definition tm0 := TM'_from_str "0RF1LS_1RF1RI_1RI0LK_1RV1LK_0RI0RV_1RI1RV_0RN1RI_0RQ---_0RN0RQ_1RN1RQ_1LS1RI_1RA0LC_1LC0RA_1LS1RA_0LT0RF_1LT1LS_1RI0LC_0LK0LS_0LC0LS_1LC1LS_1LS---_1RI---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF1LW_1RF1RM_1RM0LO_1RJ1LO_0LG0RJ_1RM1RJ_0LG1RM_1LG---_0RM---_1RM---_0RR---_0RU---_0RR0RU_1RR1RU_1LW1RM_1RA0LC_1LC0RA_1LW1RA_0LX0RF_1LX1LW_1RM0LC_0LO0LW_0LC0LW_1LC1LW".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1RE---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE0LD_1LB1RE_0RA0RH_0RG1LB_1RE1RI_1RE0LC_1RE1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NSCKIAFQV".
Definition mp' := mp_from_str "RWCOMAFUJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM73.


Module TM74.
Definition tm := TM_from_str "1LB0LA_1RC0RB_1LD0RB_0LA0LE_1LF---_0LD0LC".
Definition tm' := TM_from_str "1LB0RF_1RC0RB_1LD0RB_0LA0LE_1LF---_0LD0LC".
Definition tm0 := TM'_from_str "1RE0LH_0RE0LC_0LH0LC_1LH1LC_0RJ0RE_1RJ1RE_1LS0RJ_1RE0RE_1LC0RE_1LS1RE_0LP0RJ_1LP0RE_0LH0LX_0LC---_0LC0LS_1LC1LS_1LO---_1LK---_0LX---_1LX---_0LC0LP_0LS0RJ_0LO0LK_1LO1LK".
Definition tm0' := TM'_from_str "1RE0RU_0RE1RU_0LH0LC_1LH0LP_0RJ0RE_1RJ1RE_1LS0RJ_1RE0RE_1LC0RE_1LS1RE_0LP0RJ_1LP0RE_0LH0LX_0LC---_0LC0LS_1LC1LS_1LO---_1LK---_0LX---_1LX---_0LC0LP_0LS0RJ_0LO0LK_1LO1LK".
Definition tm1 := TM'_from_str "1LB1RI_0LC---_1LF1LD_0LE0RA_1LG1LB_0LG0LB_0LH0LG_1RI0RI_0RA0RI".
Definition tm2 := TM'_from_str "1LB1RI_0LC1RJ_1LF1LD_0LE0RA_1LG1LB_0LG0LB_0LH0LG_1RI0RI_0RA0RI_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JSXKPOCHE".
Definition mp' := mp_from_str "JSXKPOCHE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM74.


Module TM75.
Definition tm := TM_from_str "1RB1RF_1LC0LB_1RE0LD_1LB0RC_0RA0RC_1RE---".
Definition tm' := TM_from_str "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RR_0LG---_1RI0LL_1LO0LG_0LL0LG_1LL1LG_0RR0LH_1RR0RR_1RA0LO_1RI1LO_1LL0RI_1LG1RI_0LH0RR_1LH0LH_0RA0RI_1RA1RI_0RF0RR_0RV0LH_0RR---_1RR---_1RA---_1RI---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1RR_0LG---_1RI0LL_1LO0LG_0LL0LG_1LL1LG_0RR0LH_1RR0RR_1RA0LO_1RI1LO_1LL0RU_1LG1RU_0LH0RR_1LH---_0RA0RI_1RA1RI_0RF0RR_0RV0LH_0RR---_1RR---_1RA---_1RI---".
Definition tm1 := TM'_from_str "0RB0RI_1LC0LE_0LD0RH_1LF1LE_0LF0LE_1RG1LC_0RH0LD_1RA1RG_1RH---".
Definition tm2 := TM'_from_str "0RB0RI_1LC0LE_0LD0RH_1LF1LE_0LF0LE_1RG1LC_0RH0LD_1RA1RG_1RH1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "AFOHGLIRV".
Definition mp' := mp_from_str "AFOHGLIRV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM75.


Module TM76.
Definition tm := TM_from_str "1LB1LF_1RC0RB_1RE0LD_---1RB_0LA1LD_1LE1LF".
Definition tm' := TM_from_str "1LB1LE_1RC0RB_1RD1RC_0LA1LF_1LD1LE_---1RB".
Definition tm0 := TM'_from_str "1RJ1LT_0RE1LX_0LH0LX_1LH1LX_0RJ0RE_1RJ1RE_1RR0RJ_1RJ0RE_0RR---_1RR1RJ_0LX0LO_1RE1LO_---0RF_---1RF_---1RJ_---1RE_0LH---_0LX1RE_0LC0LP_1LC1LP_1LC1LT_1LP1LX_0LT0LX_1LT1LX".
Definition tm0' := TM'_from_str "1RJ1LP_0RE1LT_0LH0LT_1LH1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RJ0RE_0RN0RJ_1RN1RJ_0LT1RN_1RE1RJ_0LH---_0LT1RE_0LC0LX_1LC1LX_1LC1LP_1LX1LT_0LP0LT_1LP1LT_---0RF_---1RF_---1RJ_---1RE".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LB_1LD1LH_0LE0LB_1RF0RG_1RA1RF_0RF0RG_---1RG".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LB_1LD1LH_0LE0LB_1RF0RG_1RA1RF_0RF0RG_1RI1RG_1RI1RI".
Definition l0 := [1;1;1;0;0;0;0;1]%N.
Definition mp := mp_from_str "RXTCHJEP".
Definition mp' := mp_from_str "NTPCHJEX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM76.


Module TM77.
Definition tm := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---".
Definition tm' := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LF_0RD---".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LH1RF_1RM1RB_1LP0RM_1LH1RM_0LL0RB_1LL0LG_1RB1LL_1LS0LG_0LP0LH_1LP1LH_0RB0LG_1RB0LW_1RF0LS_1RB1LS_0LL0LG_0RB---_0LG0LW_1LG1LW_0LL---_0RB---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LH1RF_1RM1RB_1LP0RM_1LH1RM_0LL0RB_1LL0LG_1RB1LL_1LS0LG_0LP0LH_1LP1LH_0RB0LG_1RB0LX_1RF0LS_1RB1LS_0LL0LG_0RB---_0LG0LX_1LG1LX_0RM---_1RM---_0RB---_0LG---".
Definition tm1 := TM'_from_str "1LB1RF_1LD0LC_0LD0RE_1LG1LB_1RA1RE_0RE0LC_1RE1LH_0LC0LI_0LC---".
Definition tm2 := TM'_from_str "1LB1RF_1LD0LC_0LD0RE_1LG1LB_1RA1RE_0RE0LC_1RE1LH_0LC0LI_0LC1RJ_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "FHGLBMPSW".
Definition mp' := mp_from_str "FHGLBMPSX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM77.


Module TM78.
Definition tm := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LF_0RD---".
Definition tm' := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LF_1RC---".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LH1RF_1RM1RB_1LP0RM_1LH1RM_0LL0RB_1LL0LG_1RB1LL_1LS0LG_0LP0LH_1LP1LH_0RB0LG_1RB0LX_1RF0LS_1RB1LS_0LL0LG_0RB---_0LG0LX_1LG1LX_0RM---_1RM---_0RB---_0LG---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LH1RF_1RM1RB_1LP0RM_1LH1RM_0LL0RB_1LL0LG_1RB1LL_1LS0LG_0LP0LH_1LP1LH_0RB0LG_1RB0LX_1RF0LS_1RB1LS_0LL0LG_0RB---_0LG0LX_1LG1LX_0RJ---_1RJ---_1LS---_0LG---".
Definition tm1 := TM'_from_str "1LB1RF_1LD0LC_0LD0RE_1LG1LB_1RA1RE_0RE0LC_1RE1LH_0LC0LI_0LC---".
Definition tm2 := TM'_from_str "1LB1RF_1LD0LC_0LD0RE_1LG1LB_1RA1RE_0RE0LC_1RE1LH_0LC0LI_0LC1RJ_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "FHGLBMPSX".
Definition mp' := mp_from_str "FHGLBMPSX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM78.


Module TM79.
Definition tm := TM_from_str "1LB1RE_1RC1LE_1RE1RD_1RC1LA_1LF0RA_---0LA".
Definition tm' := TM_from_str "1LB1RE_1RC1LE_1RE1RD_1RC0RA_1LF0RA_---0LA".
Definition tm0 := TM'_from_str "1RN0RR_1LT1RR_0LH1LC_1LH1RA_0RJ1LX_1RJ0RR_1RR0LT_1RN1LT_0RR0RN_1RR1RN_1LC1RJ_1RA1RA_0RJ1LH_1RJ1RA_1RR0LD_1RN1LD_---0RA_1LC1RA_0LX1RN_1LX0RR_---0LH_---1LC_---0LC_---1LC".
Definition tm0' := TM'_from_str "1RN0RR_1LT1RR_0LH1LC_1LH1RA_0RJ1LX_1RJ0RR_1RR0LT_1RN1LT_0RR0RN_1RR1RN_1LC1RJ_1RA1RA_0RJ0RA_1RJ1RA_1RR1RN_1RN0RR_---0RA_1LC1RA_0LX1RN_1LX0RR_---0LH_---1LC_---0LC_---1LC".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RF_0LD1LC_1RG1LE_1LH0RB_1RG0RB_1RA1RF_---1LC".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RF_0LD1LC_1RG1LE_1LH0RB_1RG0RB_1RA1RF_1RI1LC_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "JRCHTANX".
Definition mp' := mp_from_str "JRCHTANX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM79.


Module TM80.
Definition tm := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_1RB---".
Definition tm' := TM_from_str "1LB1LF_1LC0LA_1RD0RA_1RE0RD_1LB0RB_1LB---".
Definition tm0 := TM'_from_str "1LL0RE_1LS1RE_0LH1RM_1LH0LH_1RM0LH_1LH0LW_0LL0LS_1LL1LS_0RN1LL_1RN1LS_1RB0LH_1RM1LH_0RB0RM_1RB1RM_1LS0RB_1RE0RM_1LL1LH_1LS---_0LH0LW_1LH1LW_0RF---_1RF---_1LH---_0LW---".
Definition tm0' := TM'_from_str "1LL1LH_1LC---_0LH0LX_1LH1LX_1RM0LH_1LH0LX_0LL0LC_1LL1LC_0RN0RA_1RN1RA_1RR1LL_1RM1LH_0RR0RM_1RR1RM_1LC0RR_1RE0RM_1LL0RE_1LC1RE_0LH1RM_1LH0LH_1LL---_1LC---_0LH---_1LH---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LC---_1RF1LC_0RA0RF_1RF0LC".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LC1RH_1RF1LC_0RA0RF_1RF0LC_1RH1RH".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "BSHWLME".
Definition mp' := mp_from_str "RCHXLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM80.


Module TM81.
Definition tm := TM_from_str "1LB1LF_1LC0LA_1RD0RA_1RE0RD_1LB0RB_1LB---".
Definition tm' := TM_from_str "1LB---_1LC0LF_1RD1LB_1RE0RD_1LB0RB_1LB1LA".
Definition tm0 := TM'_from_str "1LL1LH_1LC---_0LH0LX_1LH1LX_1RM0LH_1LH0LX_0LL0LC_1LL1LC_0RN0RA_1RN1RA_1RR1LL_1RM1LH_0RR0RM_1RR1RM_1LC0RR_1RE0RM_1LL0RE_1LC1RE_0LH1RM_1LH0LH_1LL---_1LC---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1LL---_1LW---_0LH---_1LH---_1RM0LH_1LH0LD_0LL0LW_1LL1LW_0RN1LL_1RN1LW_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1LW0RR_1RE0RM_1LL0RE_1LW1RE_0LH1RM_1LH0LH_1LL1LH_1LW---_0LH0LD_1LH1LD".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LC---_1RF1LC_0RA0RF_1RF0LC".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LC1RH_1RF1LC_0RA0RF_1RF0LC_1RH1RH".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "RCHXLME".
Definition mp' := mp_from_str "RWHDLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM81.


Module TM82.
Definition tm := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0RE---".
Definition tm' := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0RA---".
Definition tm0 := TM'_from_str "1LL0RE_1LS1RE_0LH1RM_1LH0LH_1RM0LH_1LH0LW_0LL0LS_1LL1LS_0RN1LL_1RN1LS_1RB0LH_1RM1LH_0RB0RM_1RB1RM_1LS0RB_1RE0RM_1LL1LL_1LS---_0LH0LW_1LH1LW_0RQ---_1RQ---_1LL---_1LL---".
Definition tm0' := TM'_from_str "1LL0RE_1LS1RE_0LH1RM_1LH0LH_1RM0LH_1LH0LW_0LL0LS_1LL1LS_0RN1LL_1RN1LS_1RB0LH_1RM1LH_0RB0RM_1RB1RM_1LS0RB_1RE0RM_1LL1LL_1LS---_0LH0LW_1LH1LW_0RA---_1RA---_1LL---_0RE---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LE---_1RF1LC_0RA0RF_1RF0LC".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LE1RH_1RF1LC_0RA0RF_1RF0LC_1RH1RH".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "BSHWLME".
Definition mp' := mp_from_str "BSHWLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM82.


Module TM83.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_1LD---".
Definition tm' := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_0LF1RC_1RA---".
Definition tm0 := TM'_from_str "1RI0LX_1LP1RB_0LH0LS_1LH1LS_0RJ1LD_1RJ1LG_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RB0RI_1LH1RB_1LS0LP_0LD0LG_1LD1LG_1LP0RJ_---1RJ_0LX1RB_1LX1RI_1LD---_1LG---_0LP---_1LP---".
Definition tm0' := TM'_from_str "1RI0LW_1LP1RB_0LH0LS_1LH1LS_0RJ1LD_1RJ1LG_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RB0RI_1LH1RB_1LS0LP_0LD0LG_1LD1LG_1LP0RJ_---1RJ_0LW1RB_1LW1RI_0RB---_1RB---_1LP---_1RB---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "BPGDHISX".
Definition mp' := mp_from_str "BPGDHISW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM83.


Module TM84.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_0LF1RC_1RA---".
Definition tm' := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_0LF1RF_1RA---".
Definition tm0 := TM'_from_str "1RI0LW_1LP1RB_0LH0LS_1LH1LS_0RJ1LD_1RJ1LG_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RB0RI_1LH1RB_1LS0LP_0LD0LG_1LD1LG_1LP0RJ_---1RJ_0LW1RB_1LW1RI_0RB---_1RB---_1LP---_1RB---".
Definition tm0' := TM'_from_str "1RI0LW_1LP1RB_0LH0LS_1LH1LS_0RJ1LD_1RJ1LG_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RB0RI_1LH1RB_1LS0LP_0LD0LG_1LD1LG_1LP0RV_---1RV_0LW1RB_1LW---_0RB---_1RB---_1LP---_1RB---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "BPGDHISW".
Definition mp' := mp_from_str "BPGDHISW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM84.


Module TM85.
Definition tm := TM_from_str "1LB0LD_1RC1LF_0RD0RC_0LE0LB_1RA---_1LA0LB".
Definition tm' := TM_from_str "1LB0LD_1RC1LF_0RD0RC_1LE0LB_1LF---_1LA0LB".
Definition tm0 := TM'_from_str "1RI0LS_1LX0LG_0LH0LO_1LH1LO_0RJ1LD_1RJ1LG_1RM0LX_1RI1LX_0RM0RI_1RM1RI_1LX0RM_1RM0RI_1LX1RM_---0LX_0LS0LG_1LS1LG_0RB---_1RB---_1LX---_0LG---_1LH1RM_1LO0LX_0LD0LG_1LD1LG".
Definition tm0' := TM'_from_str "1RI0LT_1LX0LG_0LH0LO_1LH1LO_0RJ1LD_1RJ1LG_1RM0LX_1RI1LX_0RM0RI_1RM1RI_1LX0RM_1RM0RI_1LX1RM_---0LX_0LT0LG_1LT1LG_1LD---_1LG---_0LX---_1LX---_1LH1RM_1LO0LX_0LD0LG_1LD1LG".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH0LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH0LC_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "MXGDHIOS".
Definition mp' := mp_from_str "MXGDHIOT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM85.


Module TM86.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_0LE---".
Definition tm' := TM_from_str "1LB0LE_1RC1LA_1RD0RC_1RA0RA_1LA0LF_1RE---".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LS_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1RN0RJ_1RM0RE_0RN0RM_1RN1RM_1LP1RE_0LX0LP_1RE0LP_1LP0LX_0LD0LS_1LD1LS_1LD1LS_1LS---_0LP0LX_1LP1LX_0LP---_0LX---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1RI0LD_1LD0LW_0LH0LS_1LH1LS_0RJ1LH_1RJ1LS_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RB0RN_1RA0RI_0RB0RA_1RB1RA_1LD1RI_0LW0LD_1LH1LS_1LS---_0LD0LW_1LD1LW_0RR---_1RR---_1LS---".
Definition tm1 := TM'_from_str "1RB1RG_1LC0LH_1LE1LD_0LC0LH_1RF1LC_0RA0RF_1RF0LC_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0LH_1LE1LD_0LC0LH_1RF1LC_0RA0RF_1RF0LC_1LD1RI_1RI1RI".
Definition l0 := [1;0;0;1;1;0;0;0]%N.
Definition mp := mp_from_str "JNPSDEMX".
Definition mp' := mp_from_str "NBDSHIAW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM86.


Module TM87.
Definition tm := TM_from_str "1LB0LE_1RC1LA_1RD0RC_1RA0RA_1LA0LF_1RE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_1RA---".
Definition tm0 := TM'_from_str "1RI0LD_1LD0LW_0LH0LS_1LH1LS_0RJ1LH_1RJ1LS_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RB0RN_1RA0RI_0RB0RA_1RB1RA_1LD1RI_0LW0LD_1LH1LS_1LS---_0LD0LW_1LD1LW_0RR---_1RR---_1LS---".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LS_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1RN0RJ_1RM0RE_0RN0RM_1RN1RM_1LP1RE_0LX0LP_1RE0LP_1LP0LX_0LD0LS_1LD1LS_1LD1LS_1LS---_0LP0LX_1LP1LX_0RB---_1RB---_1RF---_1LS---".
Definition tm1 := TM'_from_str "1RB1RG_1LC0LH_1LE1LD_0LC0LH_1RF1LC_0RA0RF_1RF0LC_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0LH_1LE1LD_0LC0LH_1RF1LC_0RA0RF_1RF0LC_1LD1RI_1RI1RI".
Definition l0 := [1;0;0;1;1;0;0;0]%N.
Definition mp := mp_from_str "NBDSHIAW".
Definition mp' := mp_from_str "JNPSDEMX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM87.


Module TM88.
Definition tm := TM_from_str "1LB0LF_1RC0RF_1RD0RC_1RE0RA_1LD---_1LA1LF".
Definition tm' := TM_from_str "1LB0LF_1RC1LA_1RD0RC_1RE0RA_1LD---_1LA1LF".
Definition tm0 := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ0RU_1RJ1RU_1RN1LH_1RI1LD_0RN0RI_1RN1RI_1RR0RN_1RA0RI_0RR0RA_1RR1RA_0LD1RI_---0LD_------_0LD---_0LP---_1LP---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm0' := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ1LH_1RJ1LW_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RR0RN_1RA0RI_0RR0RA_1RR1RA_0LD1RI_---0LD_------_0LD---_0LP---_1LP---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm1 := TM'_from_str "0LB---_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH".
Definition tm2 := TM'_from_str "0LB1RI_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH_1RI1RI".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "RDWHINAX".
Definition mp' := mp_from_str "RDWHINAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM88.


Module TM89.
Definition tm := TM_from_str "1LB0LF_1RC1LA_1RD0RC_1RE0RA_1LD---_1LA1LF".
Definition tm' := TM_from_str "1LB0LF_1RC0RF_1RD0RC_0RE0RA_0LF---_1LA1LF".
Definition tm0 := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ1LH_1RJ1LW_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RR0RN_1RA0RI_0RR0RA_1RR1RA_0LD1RI_---0LD_------_0LD---_0LP---_1LP---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm0' := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ0RU_1RJ1RU_1RN1LH_1RI1LD_0RN0RI_1RN1RI_1RQ0RN_1RA0RI_0RQ0RA_1RQ1RA_0LD1RI_---0LD_0LD---_0LX---_0LW---_1LW---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm1 := TM'_from_str "0LB---_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH".
Definition tm2 := TM'_from_str "0LB1RI_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH_1RI1RI".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "RDWHINAX".
Definition mp' := mp_from_str "QDWHINAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM89.


Module TM90.
Definition tm := TM_from_str "1LB0LF_1RC0RF_1RD0RC_0RE0RA_0LF---_1LA1LF".
Definition tm' := TM_from_str "1LB0LF_1RC1LA_1RD0RC_1RE0RA_0LB---_1LA1LF".
Definition tm0 := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ0RU_1RJ1RU_1RN1LH_1RI1LD_0RN0RI_1RN1RI_1RQ0RN_1RA0RI_0RQ0RA_1RQ1RA_0LD1RI_---0LD_0LD---_0LX---_0LW---_1LW---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm0' := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ1LH_1RJ1LW_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RR0RN_1RA0RI_0RR0RA_1RR1RA_0LD1RI_---0LD_1RN---_0LD---_0LG---_1LG---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm1 := TM'_from_str "0LB---_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH".
Definition tm2 := TM'_from_str "0LB1RI_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH_1RI1RI".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "QDWHINAX".
Definition mp' := mp_from_str "RDWHINAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM90.


Module TM91.
Definition tm := TM_from_str "1LB0LF_1RC1LA_1RD0RC_1RE0RA_0LB---_1LA1LF".
Definition tm' := TM_from_str "1LB0LF_1RC1LA_1RD0RC_0RE0RA_0LF---_1LA1LF".
Definition tm0 := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ1LH_1RJ1LW_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RR0RN_1RA0RI_0RR0RA_1RR1RA_0LD1RI_---0LD_1RN---_0LD---_0LG---_1LG---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm0' := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ1LH_1RJ1LW_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RQ0RN_1RA0RI_0RQ0RA_1RQ1RA_0LD1RI_---0LD_0LD---_0LX---_0LW---_1LW---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm1 := TM'_from_str "0LB---_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH".
Definition tm2 := TM'_from_str "0LB1RI_1LD1LC_0LB0LH_1RE1LB_0RF0RE_1RA1RG_1RE0LB_1LB1LH_1RI1RI".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "RDWHINAX".
Definition mp' := mp_from_str "QDWHINAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM91.


Module TM92.
Definition tm := TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC1RF_1LA0LD_1RC---".
Definition tm' := TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC0RF_1LA1RC_1LC---".
Definition tm0 := TM'_from_str "1RM0LH_1LK0LC_0LH0LC_1LH1LC_0RJ1LC_1RJ0RJ_1RR0LK_1RM1LK_0RR0RM_1RR1RM_1LC0RJ_1RJ0RV_0RJ0RV_1RJ1RV_1RR1RJ_1RM---_1LH1RR_1LC1RJ_0LD0LO_1LD1LO_0RJ---_1RJ---_1RR---_1RM---".
Definition tm0' := TM'_from_str "1RM0LH_1LK0LC_0LH0LC_1LH1LC_0RJ1LC_1RJ0RJ_1RR0LK_1RM1LK_0RR0RM_1RR1RM_1LC0RJ_1RJ0RU_0RJ0RU_1RJ1RU_1RR1RJ_1RM---_1LH0RJ_1LC1RJ_0LD1RR_1LD1RM_1RJ---_0RU---_0LL---_1LL---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE1LD_1LB0RF_0RF0RG_1RA1RE_1RF---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE1LD_1LB0RF_0RF0RG_1RA1RE_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "RCHKMJV".
Definition mp' := mp_from_str "RCHKMJU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM92.


Module TM93.
Definition tm := TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC0RF_1LA1RC_1LC---".
Definition tm' := TM_from_str "1LB0LA_1RC0LC_1RE0RD_1RC1RF_1LA1RC_1RC---".
Definition tm0 := TM'_from_str "1RM0LH_1LK0LC_0LH0LC_1LH1LC_0RJ1LC_1RJ0RJ_1RR0LK_1RM1LK_0RR0RM_1RR1RM_1LC0RJ_1RJ0RU_0RJ0RU_1RJ1RU_1RR1RJ_1RM---_1LH0RJ_1LC1RJ_0LD1RR_1LD1RM_1RJ---_0RU---_0LL---_1LL---".
Definition tm0' := TM'_from_str "1RM0LH_1LK0LC_0LH0LC_1LH1LC_0RJ1LC_1RJ0RJ_1RR0LK_1RM1LK_0RR0RM_1RR1RM_1LC0RJ_1RJ0RV_0RJ0RV_1RJ1RV_1RR1RJ_1RM---_1LH0RJ_1LC1RJ_0LD1RR_1LD1RM_0RJ---_1RJ---_1RR---_1RM---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1RE1LD_1LB0RF_0RF0RG_1RA1RE_1RF---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1RE1LD_1LB0RF_0RF0RG_1RA1RE_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "RCHKMJU".
Definition mp' := mp_from_str "RCHKMJV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM93.


Module TM94.
Definition tm := TM_from_str "1LB1RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_0RA---".
Definition tm' := TM_from_str "1LB1RF_1LC0LB_1RD0RE_0LA0RC_1RC0LA_0RA---".
Definition tm0 := TM'_from_str "1LL0RV_1LG1RV_0LH1RA_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0RA0RI_1RA1RI_1LL0RN_0RV0RQ_0RJ0LH_1RJ1RA_1RN0LC_1RQ1LC_0RA---_1RA---_1LL---_0RV---".
Definition tm0' := TM'_from_str "1LL0RV_1LG1RV_0LH1RA_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0LH0RI_1RA1RI_0LC0RN_1LC0RQ_0RJ0LH_1RJ1RA_1RN0LC_1RQ1LC_0RA---_1RA---_1LL---_0RV---".
Definition tm1 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1RA---".
Definition tm2 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1RA1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "ALHGINQJV".
Definition mp' := mp_from_str "ALHGINQJV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM94.


Module TM95.
Definition tm := TM_from_str "1LB1RF_1LC0LB_1RD0RE_0LA0RC_1RC0LA_0RA---".
Definition tm' := TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_0LC---".
Definition tm0 := TM'_from_str "1LL0RV_1LG1RV_0LH1RA_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0LH0RI_1RA1RI_0LC0RN_1LC0RQ_0RJ0LH_1RJ1RA_1RN0LC_1RQ1LC_0RA---_1RA---_1LL---_0RV---".
Definition tm0' := TM'_from_str "1LL0RU_1LG1RU_0LH1RA_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0RA0RI_1RA1RI_1LL0RN_0RU0RQ_0RJ0LH_1RJ1RA_1RN0LC_1RQ1LC_1RA---_0RJ---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1RA---".
Definition tm2 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1RA1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "ALHGINQJV".
Definition mp' := mp_from_str "ALHGINQJU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM95.


Module TM96.
Definition tm := TM_from_str "1LB---_1LC0LB_1RD0RE_0RF0RC_1RC0LF_1LB0RA".
Definition tm' := TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LF_1LB---".
Definition tm0 := TM'_from_str "1LL---_1LG---_0LH---_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RU0RJ_1RI0LH_0RU0RI_1RU1RI_1LL0RN_0RA0RQ_0RJ0LH_1RJ1LL_1RN0LW_1RQ1LW_1LL0RA_1LG1RA_0LH1LL_1LH---".
Definition tm0' := TM'_from_str "1LL0RU_1LG1RU_0LH1LL_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0RA0RI_1RA1RI_1LL0RN_0RU0RQ_0RJ0LH_1RJ---_1RN0LW_1RQ1LW_1LL---_1LG---_0LH---_1LH---".
Definition tm1 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1LB---".
Definition tm2 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1LB1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "ULHGINQJA".
Definition mp' := mp_from_str "ALHGINQJU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM96.


Module TM97.
Definition tm := TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LF_1LB---".
Definition tm' := TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_0LD---".
Definition tm0 := TM'_from_str "1LL0RU_1LG1RU_0LH1LL_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0RA0RI_1RA1RI_1LL0RN_0RU0RQ_0RJ0LH_1RJ---_1RN0LW_1RQ1LW_1LL---_1LG---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1LL0RU_1LG1RU_0LH1LL_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0RA0RI_1RA1RI_1LL0RN_0RU0RQ_0RJ0LH_1RJ1LL_1RN0LC_1RQ1LC_1LL---_0RN---_0LO---_1LO---".
Definition tm1 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1LB---".
Definition tm2 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1LB1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "ALHGINQJU".
Definition mp' := mp_from_str "ALHGINQJU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM97.


Module TM98.
Definition tm := TM_from_str "1LB1RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_1RC---".
Definition tm' := TM_from_str "1LB1RE_1LC0LB_1RD0RE_0RA0RC_1RC0LF_1LB---".
Definition tm0 := TM'_from_str "1LL0RV_1LG1RV_0LH1RJ_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0RA0RI_1RA1RI_1LL0RN_0RV0RQ_0RJ0LH_1RJ1RJ_1RN0LC_1RQ1LC_0RJ---_1RJ---_1RN---_1RQ---".
Definition tm0' := TM'_from_str "1LL0RR_1LG1RR_0LH1RJ_1LH---_1RI0LL_0LH0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RA0RJ_1RI0LH_0RA0RI_1RA1RI_1LL0RN_0RR0RQ_0RJ0LH_1RJ---_1RN0LW_1RQ1LW_1LL---_1LG---_0LH---_1LH---".
Definition tm1 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1RH---".
Definition tm2 := TM'_from_str "1LB0RI_1RE0LC_1LB1LD_0LB0LD_0RF0RG_1RA1RE_0RH0LC_1RF1RG_1RH1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "ALHGINQJV".
Definition mp' := mp_from_str "ALHGINQJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM98.


Module TM99.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RE_0RD0LF_1LC---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_0RD---_0RD0LB".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1RM_1RN---_1LP0RN_1LK1RN_0LL1RB_1LL1RQ_1RR0LP_0LL0LK_0LP0LK_1LP1LK_0RB0RQ_1RB1RQ_1RF0RM_1RR0LL_0RM0LL_1RM---_0RB0LW_0RQ1LW_1LP---_1LK---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LK1RM_1RN---_1LP0RN_1LK1RN_0LL1RB_1LL1RU_1RR0LP_0LL0LK_0LP0LK_1LP1LK_0RB0RU_1RB1RU_1RF0RM_1RR0LL_0RM---_1RM---_0RB---_0RU---_0RM0LL_1RM1RB_0RB0LG_0RU1LG".
Definition tm1 := TM'_from_str "0RB0RH_1RC1RG_1LD1RI_0LE0LD_1RG0LF_1LE1LD_1RA---_0RA0LF_1RB1RH".
Definition tm2 := TM'_from_str "0RB0RH_1RC1RG_1LD1RI_0LE0LD_1RG0LF_1LE1LD_1RA1RJ_0RA0LF_1RB1RH_1RJ1RJ".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "MBFKPLRQN".
Definition mp' := mp_from_str "MBFKPLRUN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM99.


Module TM100.
Definition tm := TM_from_str "1LB0RB_1RC1RB_1LD1RA_0LF0RE_---1LD_0LA1LE".
Definition tm' := TM_from_str "1LB0RB_1RC1RB_1LD1RA_1RF0LE_0LA1LF_---1LD".
Definition tm0 := TM'_from_str "1RB0RE_1RF1RE_0LH0RJ_1LH0RF_0RJ0RF_1RJ1RF_1LW1RJ_1RB1RF_1LW0RB_1LW1RB_0LP1RF_1LP1RE_0LC0RQ_0LT1RQ_0LW---_1LW1LW_---1LW_---1LW_---0LP_---1LP_0LH---_0RJ1LP_0LC0LT_1LC1LT".
Definition tm0' := TM'_from_str "1RB0RE_1RF1RE_0LH0RJ_1LH0RF_0RJ0RF_1RJ1RF_1LS1RJ_1RB1RF_1LS0RB_1LS1RB_0LP1RF_1LP1RE_0RV0LC_1RV0LX_---0LS_1LS1LS_0LH---_0RJ1LP_0LC0LX_1LC1LX_---1LS_---1LS_---0LP_---1LP".
Definition tm1 := TM'_from_str "1RB1RA_1LC1RH_0LF0LD_---1LE_1LC1LC_0LG0RB_1RH1RA_1RA1RI_0RB0RA".
Definition tm2 := TM'_from_str "1RB1RA_1LC1RH_0LF0LD_1RJ1LE_1LC1LC_0LG0RB_1RH1RA_1RA1RI_0RB0RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "FJWTPCHBE".
Definition mp' := mp_from_str "FJSXPCHBE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM100.


Module TM101.
Definition tm := TM_from_str "1LB0RB_1RC1RB_1LD1RA_1RF0LE_0LA1LF_---1LD".
Definition tm' := TM_from_str "1LB0RB_1RC1RB_1LD1RA_0LE0LE_0LA1LF_---1LD".
Definition tm0 := TM'_from_str "1RB0RE_1RF1RE_0LH0RJ_1LH0RF_0RJ0RF_1RJ1RF_1LS1RJ_1RB1RF_1LS0RB_1LS1RB_0LP1RF_1LP1RE_0RV0LC_1RV0LX_---0LS_1LS1LS_0LH---_0RJ1LP_0LC0LX_1LC1LX_---1LS_---1LS_---0LP_---1LP".
Definition tm0' := TM'_from_str "1RB0RE_1RF1RE_0LH0RJ_1LH0RF_0RJ0RF_1RJ1RF_1LS1RJ_1RB1RF_1LS0RB_1LS1RB_0LP1RF_1LP1RE_0LC0LC_0LX0LX_0LS0LS_1LS1LS_0LH---_0RJ1LP_0LC0LX_1LC1LX_---1LS_---1LS_---0LP_---1LP".
Definition tm1 := TM'_from_str "1RB1RA_1LC1RH_0LF0LD_---1LE_1LC1LC_0LG0RB_1RH1RA_1RA1RI_0RB0RA".
Definition tm2 := TM'_from_str "1RB1RA_1LC1RH_0LF0LD_1RJ1LE_1LC1LC_0LG0RB_1RH1RA_1RA1RI_0RB0RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "FJSXPCHBE".
Definition mp' := mp_from_str "FJSXPCHBE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM101.


Module TM102.
Definition tm := TM_from_str "1RB1LF_1LC1RB_0LE1LD_1LB0RD_1RF---_1LA0LA".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LC_1LP0LX_1RF1LX_1LS0RF_1LP1RF_0LL1LP_1LL1RF_1LX1LH_---0RM_0LS0LP_1LS1LP_1LL0RM_1RF1RM_0LH1LL_1LH0RM_0RV---_1RV---_1LX---_0LX---_1RF1LP_1LX0LX_0LD0LC_1LD1LC".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LC_1LP0LX_1RF1LX_1LT0RF_1LP1RF_0LL1LP_1LL1RF_1LX1LH_---0RM_0LT0LP_1LT1LP_1LL0RM_1RF1RM_0LH1LL_1LH0RM_1LD---_1LC---_0LX---_1LX---_1RF1LP_1LX0LX_0LD0LC_1LD1LC".
Definition tm1 := TM'_from_str "1LB0RA_1LC1LH_1LD---_1LF1LE_1LH0LD_1RG1LD_1LH1RG_1LI0RA_1LB1RG".
Definition tm2 := TM'_from_str "1LB0RA_1LC1LH_1LD1RJ_1LF1LE_1LH0LD_1RG1LD_1LH1RG_1LI0RA_1LB1RG_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;0]%N.
Definition mp := mp_from_str "MLSXCDFPH".
Definition mp' := mp_from_str "MLTXCDFPH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM102.


Module TM103.
Definition tm := TM_from_str "1LB0RA_1RC0LE_1RE1RD_0RC0LA_1LD1RF_0RD---".
Definition tm' := TM_from_str "1LB1RB_1RC0LE_0RD0LA_1RE1RC_1LC1RF_0RC---".
Definition tm0 := TM'_from_str "1RN0RA_1LS1RA_0LH1RN_1LH0RA_0RJ0LP_1RJ1RM_1RR0LS_1RN1LS_0RR0RN_1RR1RN_1LC1RI_1RV1RN_0RI0LH_1RI1RN_0RR0LC_0RN1LC_0RN0RV_1LC1RV_0LP1RM_1LP---_0RM---_1RM---_0RI---_0LH---".
Definition tm0' := TM'_from_str "1RJ0RF_1LS1RF_0LH1RJ_1LH1RI_0RJ0LL_1RJ1RI_1RM0LS_1RJ1LS_0RM0LH_1RM1RJ_0RR0LC_0RJ1LC_0RR0RJ_1RR1RJ_1LC1RM_1RV1RJ_0RJ0RV_1LC1RV_0LL1RI_1LL---_0RI---_1RI---_0RM---_0LH---".
Definition tm1 := TM'_from_str "0RB0RE_1LC1RI_0LD1RE_1RE1LF_1RA1RE_0LG1RH_0RE1LC_0RA0LD_1RH---".
Definition tm2 := TM'_from_str "0RB0RE_1LC1RI_0LD1RE_1RE1LF_1RA1RE_0LG1RH_0RE1LC_0RA0LD_1RH1RJ_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "IRCHNSPMV".
Definition mp' := mp_from_str "MRCHJSLIV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM103.


Module TM104.
Definition tm := TM_from_str "1RB0RC_1LC1RE_0LE0LD_1LC0LD_0RA0RF_1RA---".
Definition tm' := TM_from_str "1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---".
Definition tm0 := TM'_from_str "0RF0RI_1RF1RI_1LO0RF_1RR0LL_1LS0RR_1LO1RR_0LL1RA_1LL1RU_0RF0LL_0RB0LO_0LS0LO_1LS1LO_1LS0LL_1LO0LO_0LL0LO_1LL1LO_0RA0RU_1RA1RU_0RF0RB_0RI---_0RB---_1RB---_1RF---_1RI---".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1LK0RF_1RR0LP_1LP0RR_1LK1RR_0LL1RA_1LL1RU_1LS0LP_1LK0LK_0LP0LK_1LP1LK_0RF0LP_0RB0LK_0LS0LK_1LS1LK_0RA0RU_1RA1RU_0RF0RB_0RM---_0RB---_1RB---_1RF---_1RM---".
Definition tm1 := TM'_from_str "1LB1RE_0LC0LB_1LD1LB_0RA0RH_1RF1RI_0RA0RG_0RA0LC_1RA1RG_0RH---".
Definition tm2 := TM'_from_str "1LB1RE_0LC0LB_1LD1LB_0RA0RH_1RF1RI_0RA0RG_0RA0LC_1RA1RG_0RH1RJ_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FOLSRAIBU".
Definition mp' := mp_from_str "FKPSRAMBU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM104.


Module TM105.
Definition tm := TM_from_str "1LB1LC_0LC---_0RD0LF_1RE1RD_0RA0RB_1LC0LC".
Definition tm' := TM_from_str "1LB1RD_0LC---_0RD0LF_1RE1RD_0RA0RB_1LC0LC".
Definition tm0 := TM'_from_str "1LK0RN_---1LW_0LH0LL_1LH1LL_0RR---_0LW---_0LK---_1LK---_0RM0LL_1RM0LK_0RR0LW_0RN1LW_0RR0RN_1RR1RN_1RA1RR_1RE1RN_0RA0RE_1RA1RE_1LK0RR_0RN---_0RN0RR_1LW0LW_0LL0LK_1LL1LK".
Definition tm0' := TM'_from_str "1LK0RN_---1RN_0LH1RR_1LH1RN_0RR---_0LW---_0LK---_1LK---_0RM0LL_1RM0LK_0RR0LW_0RN1LW_0RR0RN_1RR1RN_1RA1RR_1RE1RN_0RA0RE_1RA1RE_1LK0RR_0RN---_0RN0RR_1LW0LW_0LL0LK_1LL1LK".
Definition tm1 := TM'_from_str "1LB0RF_0RD0LC_0LE0LB_1RA1RG_0RF1LC_1RD1RF_0RD---".
Definition tm2 := TM'_from_str "1LB0RF_0RD0LC_0LE0LB_1RA1RG_0RF1LC_1RD1RF_0RD1RH_1RH1RH".
Definition l0 := [0;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "AKWRLNE".
Definition mp' := mp_from_str "AKWRLNE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM105.


Module TM106.
Definition tm := TM_from_str "1RB0RE_1RC0RB_1RD0RF_1RE---_1LF1LE_1LA0LE".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LE_1LA0LE".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ1LD_1RE1LX_0RJ0RE_1RJ1RE_1RN0RJ_1RU0RE_0RN0RU_1RN1RU_1RR1RE_---0LX_0RR---_1RR---_1LS---_1LT---_1LD1LX_1LS1LT_0LX0LT_1LX1LT_1RE0LX_1LX0LT_0LD0LS_1LD1LS".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LS_1RJ0LX_1RE1LX_0RJ0RE_1RJ1RE_1RN0RJ_1RU0RE_0RN0RU_1RN1RU_1RR1RE_---0LX_0RR---_1RR---_1LS---_1LT---_1LD1LX_1LS1LT_0LX0LT_1LX1LT_1RE0LX_1LX0LT_0LD0LS_1LD1LS".
Definition tm1 := TM'_from_str "0RB0RA_1RC1RI_1RD---_1LE1LF_0LG0LF_1LG1LF_1LH1LE_1RA1LG_1RA0LG".
Definition tm2 := TM'_from_str "0RB0RA_1RC1RI_1RD1RJ_1LE1LF_0LG0LF_1LG1LF_1LH1LE_1RA1LG_1RA0LG_1RJ1RJ".
Definition l0 := [1;0;0;0;0;0;1;1]%N.
Definition mp := mp_from_str "EJNRSTXDU".
Definition mp' := mp_from_str "EJNRSTXDU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM106.


Module TM107.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RA---".
Definition tm' := TM_from_str "1RB---_0RC0RB_1LD0RE_0LE1LA_1LF0LB_0RD0LC".
Definition tm0 := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LX1RQ_0LP1RE_1LP1LS_0LD1RE_0LG---_0LS0LX_1LS1LX_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RB---_1RB---_1RF---_1RE---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RI---_1RE---_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LD1RQ_0LP1RE_1LP1LS_0LX1RE_0LG---_0LS0LD_1LS1LD_1RE1LS_1LK0RI_0LX0LG_1LX1LG_0RM0LP_1RM1RE_0LX0LK_1RE1LK".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EISDKPGQX".
Definition mp' := mp_from_str "EISXKPGQD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM107.


Module TM108.
Definition tm := TM_from_str "1RB---_0RC0RB_1LD0RE_0LE1LA_1LF0LB_0RD0LC".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RB---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RI---_1RE---_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LD1RQ_0LP1RE_1LP1LS_0LX1RE_0LG---_0LS0LD_1LS1LD_1RE1LS_1LK0RI_0LX0LG_1LX1LG_0RM0LP_1RM1RE_0LX0LK_1RE1LK".
Definition tm0' := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LX1RQ_0LP1RE_1LP1LS_0LD1RE_0LG---_0LS0LX_1LS1LX_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RF---_1RF---_1RI---_1RE---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EISXKPGQD".
Definition mp' := mp_from_str "EISDKPGQX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM108.


Module TM109.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RB---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---".
Definition tm0 := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LX1RQ_0LP1RE_1LP1LS_0LD1RE_0LG---_0LS0LX_1LS1LX_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RF---_1RF---_1RI---_1RE---".
Definition tm0' := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LW1RQ_0LP1RE_1LP1LS_0LD1RE_0LG---_0LS0LW_1LS1LW_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RQ---_1RQ---_1RE---_1LS---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EISDKPGQX".
Definition mp' := mp_from_str "EISDKPGQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM109.


Module TM110.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RE---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---".
Definition tm0 := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LX1RQ_0LP1RE_1LP1LS_0LD0RI_0LG---_0LS0LX_1LS1LX_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RR---_1RR---_1LK---_0RI---".
Definition tm0' := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LW1RQ_0LP1RE_1LP1LS_0LD0RI_0LG---_0LS0LW_1LS1LW_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RE---_1RE---_0RI---_0RE---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0RB---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0RB1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EISDKPGQX".
Definition mp' := mp_from_str "EISDKPGQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM110.


Module TM111.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RC---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RF_0RD1LE_0LF---_1LA0LB".
Definition tm0 := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LW1RQ_0LP1RE_1LP1LS_0LD1LS_0LG---_0LS0LW_1LS1LW_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RI---_1RI---_1LS---_0RQ---".
Definition tm0' := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LW0RI_0RU0RE_1LW0RU_1LT1RU_0LP1RE_1LP1LW_0RM1LW_1RM---_0RM0LT_1LW1LT_0LD---_0LG---_0LW---_1LW---_1RE1LW_1LK0RI_0LD0LG_1LD1LG".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EISDKPGQW".
Definition mp' := mp_from_str "EIWDKPGUT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM111.


Module TM112.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RF_0RD1LE_0LF---_1LA0LB".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LE---".
Definition tm0 := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LW0RI_0RU0RE_1LW0RU_1LT1RU_0LP1RE_1LP1LW_0RM1LW_1RM---_0RM0LT_1LW1LT_0LD---_0LG---_0LW---_1LW---_1RE1LW_1LK0RI_0LD0LG_1LD1LG".
Definition tm0' := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LX1RQ_0LP1RE_1LP1LS_0LD1LS_0LG---_0LS0LX_1LS1LX_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0LD---_0LG---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EIWDKPGUT".
Definition mp' := mp_from_str "EISDKPGQX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM112.


Module TM113.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LE---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---".
Definition tm0 := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LX1RQ_0LP1RE_1LP1LS_0LD1LS_0LG---_0LS0LX_1LS1LX_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0LD---_0LG---_0LS---_1LS---".
Definition tm0' := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LX1RQ_0LP1RE_1LP1LS_0LD1LS_0LG---_0LS0LX_1LS1LX_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RQ---_1RQ---_1RE---_1LS---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EISDKPGQX".
Definition mp' := mp_from_str "EISDKPGQX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM113.


Module TM114.
Definition tm := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RD---".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---".
Definition tm0 := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LW1RQ_0LP1RE_1LP1LS_0LD0LD_0LG---_0LS0LW_1LS1LW_1RE1LS_1LK0RI_0LD0LG_1LD1LG_0RM---_1RM---_0LD---_0LD---".
Definition tm0' := TM'_from_str "0RF0LP_1RF1RE_1RI0LK_1RE1LK_0RI0RE_1RI1RE_1LS0RI_0RQ0RE_1LS0RQ_1LW1RQ_0LP1RE_1LP1LS_0LD0LD_0LG---_0LS0LW_1LS1LW_1RE1LS_1LK0RI_0LD0LG_1LD1LG_1RE---_1LK---_0LD---_1LD---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0LD---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RH_0LD0LG_1RA1LE_0LF1RA_1LC1LI_1LC0RB_1RA1LC_0LD1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "EISDKPGQW".
Definition mp' := mp_from_str "EISDKPGQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM114.


Module TM115.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1LB_1LB0RF_0RC0LA".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1LB_0RC1LF_0RB---".
Definition tm0 := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LC_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC1RM_0RR1RM_1RR1LW_1LW0LH_1RU1LH_1RM0RU_1LW1RU_0LH0RI_1LH0LH_0RI0LH_1RI---_0LH0LC_0RM1LC".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LX_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC1RM_0RB1RM_1RB1LS_1LS0LH_1RQ1LH_0RI0LH_1RI---_0LH0LX_0RM1LX_0RE---_1RE---_0RJ---_0LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD1RC_1LE1RG_0LB0LF_0LB---_0RA0LB".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD1RC_1LE1RG_0LB0LF_0LB1RH_0RA0LB_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMRWCU".
Definition mp' := mp_from_str "IHMBSXQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM115.


Module TM116.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1LB_0RC1LF_0RB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LE0RD_1RE1LB_1LB0RF_0RC0LA".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LX_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC1RM_0RB1RM_1RB1LS_1LS0LH_1RQ1LH_0RI0LH_1RI---_0LH0LX_0RM1LX_0RE---_1RE---_0RJ---_0LH---".
Definition tm0' := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LC_0RI0LW_1RM1LW_0LH0RM_0RI1RM_0LS0RR_1LS1RM_0RR1RM_1RR1LW_1LW0LH_1RU1LH_1RM0RU_1LW1RU_0LH0RI_1LH0LH_0RI0LH_1RI---_0LH0LC_0RM1LC".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD1RC_1LE1RG_0LB0LF_0LB---_0RA0LB".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD1RC_1LE1RG_0LB0LF_0LB1RH_0RA0LB_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSXQ".
Definition mp' := mp_from_str "IHMRWCU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM116.


Module TM117.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LA---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LE---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS0LH_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_1LH---_0LH---_0LD---_1LD---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RU_0RB0RU_1RB1RU_1LS0LH_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0LH---_0LS---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LB---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LB1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSQV".
Definition mp' := mp_from_str "IHMBSQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM117.


Module TM118.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LA---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RU_0RB0RU_1RB1RU_1LS0LH_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0LH---_0LS---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RU_0RB0RU_1RB1RU_1LS0LH_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0LH---_0RI---_0LC---_1LC---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LB---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LB1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSQU".
Definition mp' := mp_from_str "IHMBSQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM118.


Module TM119.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LF0RF_0RC0LF".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1LS_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_1RM---_1LS---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LW_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RB_0RR0RB_1RR1RB_1LW1LW_1RU---_0RM0RU_1LW1RU_0LX0RI_1LX0LH_0RI0LH_1RI0LW_0LH0LW_0RM1LW".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSQV".
Definition mp' := mp_from_str "IHMRWUB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM119.


Module TM120.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LF0RF_0RC0LF".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_0LD0RF_0RC0LF".
Definition tm0 := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LW_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RB_0RR0RB_1RR1RB_1LW1LW_1RU---_0RM0RU_1LW1RU_0LX0RI_1LX0LH_0RI0LH_1RI0LW_0LH0LW_0RM1LW".
Definition tm0' := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LW_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RB_0RR0RB_1RR1RB_1LW1LW_1RU---_1LW0RU_1LW1RU_0LO0RI_1LO0LH_0RI0LH_1RI0LW_0LH0LW_0RM1LW".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMRWUB".
Definition mp' := mp_from_str "IHMRWUB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM120.


Module TM121.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_0LD0RF_0RC0LF".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LB0RF_0RC0LF".
Definition tm0 := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LW_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RB_0RR0RB_1RR1RB_1LW1LW_1RU---_1LW0RU_1LW1RU_0LO0RI_1LO0LH_0RI0LH_1RI0LW_0LH0LW_0RM1LW".
Definition tm0' := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LW_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RB_0RR0RB_1RR1RB_1LW1LW_1RU---_1RM0RU_1LW1RU_0LH0RI_1LH0LH_0RI0LH_1RI0LW_0LH0LW_0RM1LW".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMRWUB".
Definition mp' := mp_from_str "IHMRWUB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM121.


Module TM122.
Definition tm := TM_from_str "1LB0LD_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RE---".
Definition tm0 := TM'_from_str "1RM1LS_1LS1RQ_0LH0LO_1LH1LO_0RJ0LH_1RJ0LS_0LO0LS_1RM1LS_0LH0RM_0LO1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1RQ_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0RQ---_1RQ---_0RI---_0LH---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1RQ_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0RQ---_1RQ---_0RI---_0LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1RF---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSQV".
Definition mp' := mp_from_str "IHMBSQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM122.


Module TM123.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC0LF_1LB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LF_0RC---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RR_0RB0RR_1RB1RR_1LS1RI_1RQ---_0RI0LH_1RI---_0LH0LW_0RM1LW_1RM---_1LS---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1RI_1RQ---_0RI0LH_1RI---_0LH0LW_0RM1LW_0RI---_1RI---_0LH---_0RM---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB1RI_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSWQR".
Definition mp' := mp_from_str "IHMBSWQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM123.


Module TM124.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LF_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC1LF_0RB---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1RI_1RQ---_0RI0LH_1RI---_0LH0LW_0RM1LW_0RI---_1RI---_0LH---_0RM---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LX_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RR_0RB0RR_1RB1RR_1LS1RI_1RQ---_0RI0LH_1RI---_0LH0LX_0RM1LX_0RE---_1RE---_0RJ---_0LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB1RI_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSWQV".
Definition mp' := mp_from_str "IHMBSXQR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM124.


Module TM125.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC1LF_0RB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RF_1LB0RF_0RC0LA".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LX_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RR_0RB0RR_1RB1RR_1LS1RI_1RQ---_0RI0LH_1RI---_0LH0LX_0RM1LX_0RE---_1RE---_0RJ---_0LH---".
Definition tm0' := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LC_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RV_0RR0RV_1RR1RV_1LW1RI_1RU---_1RM0RU_1LW1RU_0LH0RI_1LH0LH_0RI0LH_1RI---_0LH0LC_0RM1LC".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB1RI_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSXQR".
Definition mp' := mp_from_str "IHMRWCUV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM125.


Module TM126.
Definition tm := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RF_1LB0RF_0RC0LA".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RE_0RC0LF_0RC---".
Definition tm0 := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LC_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RV_0RR0RV_1RR1RV_1LW1RI_1RU---_1RM0RU_1LW1RU_0LH0RI_1LH0LH_0RI0LH_1RI---_0LH0LC_0RM1LC".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RR_0RB0RR_1RB1RR_1LS1RI_1RQ---_0RI0LH_1RI---_0LH0LW_0RM1LW_0RI---_1RI---_0LH---_0RM---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1RA---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB1RI_0RA0LB_1RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMRWCUV".
Definition mp' := mp_from_str "IHMBSWQR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM126.


Module TM127.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LF_1LB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LF0RD_1RA1RF_0RC0LF_1LB---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1LS_1RQ---_0RI0LH_1RI---_0LH0LW_0RM1LW_1RM---_1LS---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_---0LS_1RM1LS_0LH0RM_---1RM_0LW0RB_1LW0RV_0RB0RV_1RB1RV_1LS1LS_1RQ---_0RI0LH_1RI---_0LH0LW_0RM1LW_1RM---_1LS---_0LH---_1LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB1RI_0RA0LB_1LE1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSWQV".
Definition mp' := mp_from_str "IHMBSWQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM127.


Module TM128.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LF0RD_1RA1RF_0RC0LF_1LB---".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_0LD0RF_0RC0LA".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_---0LS_1RM1LS_0LH0RM_---1RM_0LW0RB_1LW0RV_0RB0RV_1RB1RV_1LS1LS_1RQ---_0RI0LH_1RI---_0LH0LW_0RM1LW_1RM---_1LS---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM---_1LW---_0LH---_1LH---_0RJ0LH_1RJ0LC_---0LW_1RM1LW_0LH0RM_---1RM_0LC0RR_1LC0RB_0RR0RB_1RR1RB_1LW1LW_1RU---_1LW0RU_1LW1RU_0LO0RI_1LO0LH_0RI0LH_1RI---_0LH0LC_0RM1LC".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB1RI_0RA0LB_1LE1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSWQV".
Definition mp' := mp_from_str "IHMRWCUB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM128.


Module TM129.
Definition tm := TM_from_str "1LB0LE_0RB1LC_1RD1LA_1RF0RE_0LC1RD_1LB---".
Definition tm' := TM_from_str "1LB---_1RC1LE_1RA0RD_0LE1RC_1RC1LF_1LB0LD".
Definition tm0 := TM'_from_str "1RQ0LK_1LL1RV_0LH0LS_1LH1LS_0RE1RQ_1RE1LD_0RE0LL_1RQ1LL_0RN1LH_1RN1LS_1RV0LD_1RQ1LD_0RV0RQ_1RV1RQ_1LL1RV_---0RN_1RV0RN_0LD1RN_0LK1RV_1LK1RQ_1RQ---_1LL---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM---_1LT---_0LH---_1LH---_0RJ1RM_1RJ1LX_1RB0LT_1RM1LT_0RB0RM_1RB1RM_1LT1RB_---0RJ_1RB0RJ_0LX1RJ_0LS1RB_1LS1RM_0RJ1LH_1RJ1LO_1RB0LX_1RM1LX_1RM0LS_1LT1RB_0LH0LO_1LH1LO".
Definition tm1 := TM'_from_str "1LB---_1RG1LC_1LF1LD_0LE1RA_1RA0LC_1RG1LB_1RA0RH_1RA1RG".
Definition tm2 := TM'_from_str "1LB1RI_1RG1LC_1LF1LD_0LE1RA_1RA0LC_1RG1LB_1RA0RH_1RA1RG_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "VLDSKHQN".
Definition mp' := mp_from_str "BTXOSHMJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM129.


Module TM130.
Definition tm := TM_from_str "1LB0LF_1RC1LE_1RA0RD_0LB1RC_1RC1LA_0LE---".
Definition tm' := TM_from_str "1LB0LF_1RC1LE_1RA0RD_0LE1RC_1RC1LA_0LE---".
Definition tm0 := TM'_from_str "1RM0LS_1LT---_0LH0LW_1LH1LW_0RJ1RM_1RJ1LD_1RB0LT_1RM1LT_0RB0RM_1RB1RM_1LT1RB_---0RJ_1RB0RJ_0LT1RJ_0LG1RB_1LG1RM_0RJ1LH_1RJ1LW_1RB0LD_1RM1LD_1RB---_0LD---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1RM0LS_1LT---_0LH0LW_1LH1LW_0RJ1RM_1RJ1LD_1RB0LT_1RM1LT_0RB0RM_1RB1RM_1LT1RB_---0RJ_1RB0RJ_0LD1RJ_0LS1RB_1LS1RM_0RJ1LH_1RJ1LW_1RB0LD_1RM1LD_1RB---_0LD---_0LS---_1LS---".
Definition tm1 := TM'_from_str "1LB---_1RG1LC_1LF1LD_0LE---_1RA0LC_1RG1LB_1RA0RH_1RA1RG".
Definition tm2 := TM'_from_str "1LB1RI_1RG1LC_1LF1LD_0LE1RI_1RA0LC_1RG1LB_1RA0RH_1RA1RG_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BTDWSHMJ".
Definition mp' := mp_from_str "BTDWSHMJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM130.


Module TM131.
Definition tm := TM_from_str "1LB0LF_1RC1LE_1RA0RD_0LE1RC_1RC1LA_0LE---".
Definition tm' := TM_from_str "1LB0LF_0RB1LC_1RD1LA_1RA0RE_0LC1RD_0LC---".
Definition tm0 := TM'_from_str "1RM0LS_1LT---_0LH0LW_1LH1LW_0RJ1RM_1RJ1LD_1RB0LT_1RM1LT_0RB0RM_1RB1RM_1LT1RB_---0RJ_1RB0RJ_0LD1RJ_0LS1RB_1LS1RM_0RJ1LH_1RJ1LW_1RB0LD_1RM1LD_1RB---_0LD---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1RQ0LK_1LL---_0LH0LW_1LH1LW_0RE1RQ_1RE1LD_0RE0LL_1RQ1LL_0RN1LH_1RN1LW_1RB0LD_1RQ1LD_0RB0RQ_1RB1RQ_1LL1RB_---0RN_1RB0RN_0LD1RN_0LK1RB_1LK1RQ_1RB---_0LD---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1LB---_1RG1LC_1LF1LD_0LE---_1RA0LC_1RG1LB_1RA0RH_1RA1RG".
Definition tm2 := TM'_from_str "1LB1RI_1RG1LC_1LF1LD_0LE1RI_1RA0LC_1RG1LB_1RA0RH_1RA1RG_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BTDWSHMJ".
Definition mp' := mp_from_str "BLDWKHQN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM131.


Module TM132.
Definition tm := TM_from_str "1RB1LD_0RC0LF_0RD1RF_1RE0LE_1LA1LE_---1RB".
Definition tm' := TM_from_str "1RB1LE_1LC0RD_---1RB_0RE1RC_1RF0LF_1LA1LF".
Definition tm0 := TM'_from_str "0RF1LT_1RF1LS_1RI0LP_1RI1LP_0RI---_1RI1RI_0RM0LW_0RV1LW_0RM0RV_1RM1RV_0RR---_0LD1RF_0RR0LD_1RR0LT_1LP0LS_1LT1LS_1RI1LD_1LP1LT_0LD0LT_1LD1LT_---0RF_---1RF_---1RI_---1RI".
Definition tm0' := TM'_from_str "0RF1LX_1RF1LW_1RM0LT_1RM1LT_---0RM_1RM1RM_0LL0RQ_1LL0RJ_---0RF_---1RF_---1RM_---1RM_0RQ0RJ_1RQ1RJ_0RV---_0LD1RF_0RV0LD_1RV0LX_1LT0LW_1LX1LW_1RM1LD_1LT1LX_0LD0LX_1LD1LX".
Definition tm1 := TM'_from_str "0RB0LE_1LC1LD_1LD1LF_1LE1LD_1RG1LC_0LE0LD_0RA0RH_---1RI_1RG1RG".
Definition tm2 := TM'_from_str "0RB0LE_1LC1LD_1LD1LF_1LE1LD_1RG1LC_0LE0LD_0RA0RH_1RJ1RI_1RG1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "MRPTDSIVF".
Definition mp' := mp_from_str "QVTXDWMJF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM132.


Module TM133.
Definition tm := TM_from_str "1LB0LA_1RC0RF_1RE1RD_0RB---_1LA1RB_0RB0LE".
Definition tm' := TM_from_str "1LB0LA_1RC0RD_1RE1RD_0RB0LF_1LA1RB_1LA---".
Definition tm0 := TM'_from_str "1RN0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RU_1RJ1RU_1RR0RE_1RN0LD_0RR0RN_1RR1RN_1LC1RE_1RF---_0RE---_1RE---_0RJ---_0RU---_1LH0RF_1LC1RF_0LD1RJ_1LD1RU_0RE0LD_1RE1RJ_0RJ0LS_0RU1LS".
Definition tm0' := TM'_from_str "1RN0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RM_1RJ1RM_1RR0RE_1RN0LD_0RR0RN_1RR1RN_1LC1RE_1RF---_0RE0LD_1RE---_0RJ0LW_0RM1LW_1LH0RF_1LC1RF_0LD1RJ_1LD1RM_1LH---_1LC---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RE_1LC1RI_0LD0LC_1RE0LG_1RF---_0RA0RH_1LD1LC_0RF0LG_1RA1RH".
Definition tm2 := TM'_from_str "1RB1RE_1LC1RI_0LD0LC_1RE0LG_1RF1RJ_0RA0RH_1LD1LC_0RF0LG_1RA1RH_1RJ1RJ".
Definition l0 := [1;1;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "JRCHNEDUF".
Definition mp' := mp_from_str "JRCHNEDMF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM133.


Module TM134.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1RE1RD_0RC---_1RF0RB_1LA0RD".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_1RE1RD_0RC---_1RF0RB_1LB0RD".
Definition tm0 := TM'_from_str "1RN0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1RR0LC_1RN1LC_0RR0RN_1RR1RN_1RV1RI_1RE---_0RI---_1RI---_0RR---_0RN---_0RV0RE_1RV1RE_1LC0RJ_1RM0LH_1LH0RM_1LC1RM_0LD0RI_1LD---".
Definition tm0' := TM'_from_str "1RN0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1RR0LC_1RN1LC_0RR0RN_1RR1RN_1RV1RI_1RE---_0RI---_1RI---_0RR---_0RN---_0RV0RE_1RV1RE_1LC0RJ_1RM0LH_1RN0RM_1LC1RM_0LH0RI_1LH---".
Definition tm1 := TM'_from_str "1RB1RF_1RC1RH_1LD1RI_0LE0LD_1RF1LD_1RG---_0RB0RF_0RA0LE_0RG---".
Definition tm2 := TM'_from_str "1RB1RF_1RC1RH_1LD1RI_0LE0LD_1RF1LD_1RG1RJ_0RB0RF_0RA0LE_0RG1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "JRVCHNIEM".
Definition mp' := mp_from_str "JRVCHNIEM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM134.


Module TM135.
Definition tm := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LB_1RA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0RB_1RA---".
Definition tm0 := TM'_from_str "0RF1RN_1RF1LD_1LK0LD_1RN1LD_1LD0RN_1LK1RN_0LL1RR_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RR0RE_1RR1RE_1RV1LD_1RE0RN_0RV1LL_1RV1RE_1RB0LH_---1LH_0RB---_1RB---_1RF---_1LD---".
Definition tm0' := TM'_from_str "0RF1RN_1RF1LD_1LK0LD_1RN1LD_1LD0RN_1LK1RN_0LL1RR_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RR0RE_1RR1RE_1RV1LD_1RE0RN_0RV0RE_1RV1RE_1RB1LD_---0RN_0RB---_1RB---_1RF---_1LD---".
Definition tm1 := TM'_from_str "1RB1LD_1LC1RE_0LD0LC_1RE1LD_1RG1RF_1LD0RE_1RH1RF_1RA---".
Definition tm2 := TM'_from_str "1RB1LD_1LC1RE_0LD0LC_1RE1LD_1RG1RF_1LD0RE_1RH1RF_1RA1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "BFKDNERV".
Definition mp' := mp_from_str "BFKDNERV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM135.


Module TM136.
Definition tm := TM_from_str "1RB0RE_0RC1RA_1LD1LA_1LB0LC_1RF1RC_---0LB".
Definition tm' := TM_from_str "1RB0RE_0RC1RA_1LD1LA_1LB0LC_1RF1RC_---1RB".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RI0RV_1RB0RJ_0RI0RB_1RI1RB_1LH1RF_1RB1RQ_1LH1RB_1LK0RJ_0LP0LD_1LP1LD_1RB0LP_1RQ0LD_0LH0LK_1LH1LK_0RV0RJ_1RV1RJ_---1LK_1RF0RJ_---1LH_---1RF_---0LG_---1LG".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RI0RV_1RB0RJ_0RI0RB_1RI1RB_1LH1RF_1RB1RQ_1LH1RB_1LK0RJ_0LP0LD_1LP1LD_1RB0LP_1RQ0LD_0LH0LK_1LH1LK_0RV0RJ_1RV1RJ_---1LK_1RF0RJ_---0RF_---1RF_---1RI_---1RB".
Definition tm1 := TM'_from_str "1LB1RH_1RH1RC_0RJ0RD_1LE0RD_0LF0LG_1LB1LE_1RH0RD_1RI1RC_1RA1RH_---1RI".
Definition tm2 := TM'_from_str "1LB1RH_1RH1RC_0RJ0RD_1LE0RD_0LF0LG_1LB1LE_1RH0RD_1RI1RC_1RA1RH_1RK1RI_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "IHQJKPDBFV".
Definition mp' := mp_from_str "IHQJKPDBFV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM136.


Module TM137.
Definition tm := TM_from_str "1LB1RC_1RA1LB_1RD0RA_1LE0RF_1RB0LE_1RA---".
Definition tm' := TM_from_str "1LB1RC_1RA1LB_1RD0RA_1LE0RF_1RF0LE_1RA---".
Definition tm0 := TM'_from_str "1RJ0RJ_1LH1RJ_0LH1RN_1LH1RA_0RB1RJ_1RB1LH_1LH0LH_1RJ1LH_0RN0RA_1RN1RA_1LS1RJ_1RU0RJ_1LH0RU_1LS1RU_0LT0RB_1LT---_0RF1RB_1RF0LS_1RB0LS_1LH1LS_0RB---_1RB---_1LH---_1RJ---".
Definition tm0' := TM'_from_str "1RJ0RJ_1LH1RJ_0LH1RN_1LH1RA_0RB1RJ_1RB1LH_1LH0LH_1RJ1LH_0RN0RA_1RN1RA_1LS1RJ_1RU0RJ_---0RU_1LS1RU_0LT0RB_1LT---_0RV1RB_1RV0LS_1RB0LS_---1LS_0RB---_1RB---_1LH---_1RJ---".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_1RD0LC_1LE1RA_1RA1LE_1RA0RA_0RD---".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_1RD0LC_1LE1RA_1RA1LE_1RA0RA_0RD1RH_1RH1RH".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "JNSBHAU".
Definition mp' := mp_from_str "JNSBHAU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM137.


Module TM138.
Definition tm := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE1RF_0LE1LA_1RC---".
Definition tm' := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RF_0LE1LA_0LA---".
Definition tm0 := TM'_from_str "0RF1RJ_1RF0LC_1RJ0LC_1RB1LC_0RJ0RB_1RJ1RB_1RM1RF_1RE0LC_0RM0RE_1RM1RE_1LS0RJ_0RV0RB_1LS0RV_1LD1RV_0LT1RJ_1LT---_0LS1RB_0LD1LC_0LS0LD_1LS1LD_0RJ---_1RJ---_1RM---_1RE---".
Definition tm0' := TM'_from_str "0RF1RJ_1RF0LC_1RJ0LC_1RB1LC_0RJ0RB_1RJ1RB_1RM1RF_1RE0LC_0RM0RE_1RM1RE_1LS0RJ_0RU0RB_1LS0RU_1LD1RU_0LT1RJ_1LT---_0LS1RB_0LD1LC_0LS0LD_1LS1LD_1RJ---_0LC---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1RB1RH_1RC1RG_1LD0RI_0LD0LE_1RH1LF_1RB0LF_0RB0RH_1RA0LF_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_1RC1RG_1LD0RI_0LD0LE_1RH1LF_1RB0LF_0RB0RH_1RA0LF_1RB1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "FJMSDCEBV".
Definition mp' := mp_from_str "FJMSDCEBU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM138.


Module TM139.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1RA".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RA".
Definition tm0 := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV0RA_1RV1RA_1RB1LK_1RB0RJ_0RB0RB_1RB1RB_1LG1LG_1RJ1RJ".
Definition tm0' := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV1LH_1RV1RA_1RB0LD_1RB1LD_0RB0RB_1RB1RB_1LG1LG_1RJ1RJ".
Definition tm1 := TM'_from_str "1RB1RB_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE---".
Definition tm2 := TM'_from_str "1RB1RB_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "VBGKRAJN".
Definition mp' := mp_from_str "VBGKRAJN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM139.


Module TM140.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LF_1RA1RC".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1RC".
Definition tm0 := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV1RJ_1RV1RA_1RB0LX_1RJ1LX_0RB0RJ_1RB1RJ_1LG1RN_1RJ1RA".
Definition tm0' := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV0RA_1RV1RA_1RB1LK_1RJ0RJ_0RB0RJ_1RB1RJ_1LG1RN_1RJ1RA".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "VBGKRAJN".
Definition mp' := mp_from_str "VBGKRAJN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM140.


Module TM141.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1RC".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC".
Definition tm0 := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV0RA_1RV1RA_1RB1LK_1RJ0RJ_0RB0RJ_1RB1RJ_1LG1RN_1RJ1RA".
Definition tm0' := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV1LH_1RV1RA_1RB0LD_1RJ1LD_0RB0RJ_1RB1RJ_1LG1RN_1RJ1RA".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "VBGKRAJN".
Definition mp' := mp_from_str "VBGKRAJN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM141.


Module TM142.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA0RB".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA0RB".
Definition tm0 := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV1LH_1RV1RA_1RB0LD_1RE1LD_0RB0RE_1RB1RE_1LG1RR_1RJ0LK".
Definition tm0' := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV0RA_1RV1RA_1RB1LK_1RE0RJ_0RB0RE_1RB1RE_1LG1RR_1RJ0LK".
Definition tm1 := TM'_from_str "1RB1RI_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE---_1RE0LD".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE1RJ_1RE0LD_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "VBGKRAJNE".
Definition mp' := mp_from_str "VBGKRAJNE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM142.


Module TM143.
Definition tm := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF1LE_0RB---_0RA1RC".
Definition tm' := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1RE0LC_0RA1RC_1RE---".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LG1RV_0LG---_0RV0RV_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RV0LG_0RV1LG_0RV0RV_1RV---_1RA0LT_1RJ1LT_0RE---_1RE---_0RV---_0RV---_0RA0RJ_1RA1RJ_0RF1RM_0RN0LK".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LG1RR_0LG---_0RR0RR_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RR0LG_0RR1LG_0RR0RR_1RR0LG_1RA0LK_1RJ1LK_0RA0RJ_1RA1RJ_0RF1RM_0RV0LK_0RR---_1RR---_1RA---_1RJ---".
Definition tm1 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB---_1RA0LG".
Definition tm2 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB1RJ_1RA0LG_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "MVAFGLKNJ".
Definition mp' := mp_from_str "MRAFGLKVJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM143.


Module TM144.
Definition tm := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1RE0LC_0RA1RC_1RE---".
Definition tm' := TM_from_str "1RB1RE_1LC0LD_0RB0LB_0RE0LB_1RF---_0RA1RC".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LG1RR_0LG---_0RR0RR_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RR0LG_0RR1LG_0RR0RR_1RR0LG_1RA0LK_1RJ1LK_0RA0RJ_1RA1RJ_0RF1RM_0RV0LK_0RR---_1RR---_1RA---_1RJ---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LG1RV_0LG---_0RV0RV_1LG0LG_0LL0LO_1LL1LO_0RE0LL_1RE0LO_0RV0LG_0RV1LG_0RQ0LL_1RQ0LO_0RV0LG_---1LG_0RV---_1RV---_1RA---_1RJ---_0RA0RJ_1RA1RJ_0RF1RE_0RR0LO".
Definition tm1 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB---_1RA0LG".
Definition tm2 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB1RJ_1RA0LG_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "MRAFGLKVJ".
Definition mp' := mp_from_str "EVAFGLORJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM144.


Module TM145.
Definition tm := TM_from_str "1RB1RE_1LC0LD_0RB0LB_0RE0LB_1RF---_0RA1RC".
Definition tm' := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1LC1RE_0RA1RC_1RE---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LG1RV_0LG---_0RV0RV_1LG0LG_0LL0LO_1LL1LO_0RE0LL_1RE0LO_0RV0LG_0RV1LG_0RQ0LL_1RQ0LO_0RV0LG_---1LG_0RV---_1RV---_1RA---_1RJ---_0RA0RJ_1RA1RJ_0RF1RE_0RR0LO".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LG1RR_0LG---_0RR0RR_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RR0LG_0RR1LG_0RR0RR_1LG1RR_0LL1RA_1LL1RJ_0RA0RJ_1RA1RJ_0RF1RM_0RV0LK_0RR---_1RR---_1RA---_1RJ---".
Definition tm1 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB---_1RA0LG".
Definition tm2 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB1RJ_1RA0LG_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "EVAFGLORJ".
Definition mp' := mp_from_str "MRAFGLKVJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM145.


Module TM146.
Definition tm := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1LC1RE_0RA1RC_1RE---".
Definition tm' := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1RE1RE_0RA1RC_1RE---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LG1RR_0LG---_0RR0RR_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RR0LG_0RR1LG_0RR0RR_1LG1RR_0LL1RA_1LL1RJ_0RA0RJ_1RA1RJ_0RF1RM_0RV0LK_0RR---_1RR---_1RA---_1RJ---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LG1RR_0LG---_0RR0RR_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RR0LG_0RR1LG_0RR0RR_1RR1RR_1RA1RA_1RJ1RJ_0RA0RJ_1RA1RJ_0RF1RM_0RV0LK_0RR---_1RR---_1RA---_1RJ---".
Definition tm1 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB---_1RA0LG".
Definition tm2 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB1RJ_1RA0LG_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "MRAFGLKVJ".
Definition mp' := mp_from_str "MRAFGLKVJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM146.


Module TM147.
Definition tm := TM_from_str "1RB1RF_1LC0LC_0RD0LB_1RE1RE_0RA1RC_1RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LG1RR_0LG---_0RR0RR_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RR0LG_0RR1LG_0RR0RR_1RR1RR_1RA1RA_1RJ1RJ_0RA0RJ_1RA1RJ_0RF1RM_0RV0LK_0RR---_1RR---_1RA---_1RJ---".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LG1RV_0LG---_0RV0RV_1LG0LG_0LL0LK_1LL1LK_0RM0LL_1RM0LK_0RV0LG_0RV1LG_0RV0RV_1RV---_1RA0LS_1RJ1LS_0RM---_1RM---_0RV---_0RV---_0RA0RJ_1RA1RJ_0RF1RM_0RN0LK".
Definition tm1 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB---_1RA0LG".
Definition tm2 := TM'_from_str "0RB0RB_1RC1RI_0RD0RH_1LE0LE_0LF0LG_0RB1LE_0RB0LE_1RB1RJ_1RA0LG_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "MRAFGLKVJ".
Definition mp' := mp_from_str "MVAFGLKNJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM147.


Module TM148.
Definition tm := TM_from_str "1LB1RC_0LC0LE_0RD0RF_1RA0RB_1LB0LE_1RD---".
Definition tm' := TM_from_str "1LB0LA_0LC0LA_0RD0RF_1RE0RB_1LA1RC_1RD---".
Definition tm0 := TM'_from_str "1LK0RJ_1LS1RJ_0LH1RM_1LH1RU_0RB0LH_0RN0LS_0LK0LS_1LK1LS_0RM0RU_1RM1RU_0RB0RN_0RE---_0RB0RE_1RB1RE_1LS0RB_1RJ0LH_1LK0LH_1LS0LS_0LH0LS_1LH1LS_0RN---_1RN---_1RB---_1RE---".
Definition tm0' := TM'_from_str "1LK0LH_1LC0LC_0LH0LC_1LH1LC_0RR0LH_0RN0LC_0LK0LC_1LK1LC_0RM0RU_1RM1RU_0RR0RN_0RE---_0RR0RE_1RR1RE_1LC0RR_1RJ0LH_1LH0RJ_1LC1RJ_0LD1RM_1LD1RU_0RN---_1RN---_1RR---_1RE---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LB_1LD1LB_0RA0RE_1RA1RF_0RA0LC_1RH1RI_0RA0RF_0RE---".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LB_1LD1LB_0RA0RE_1RA1RF_0RA0LC_1RH1RI_0RA0RF_0RE1RJ_1RJ1RJ".
Definition l0 := [0;1;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "BSHKNEJMU".
Definition mp' := mp_from_str "RCHKNEJMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM148.


Module TM149.
Definition tm := TM_from_str "1LB0RE_1LC1RF_0RD0LC_1LA1RD_1RB0RE_---1LC".
Definition tm' := TM_from_str "1LB0RE_1LC0RF_0RD0LC_1LA1RD_1RB0RE_---0LE".
Definition tm0 := TM'_from_str "1LL0RQ_1LK1RQ_0LH0RF_1LH0RQ_0RN0RV_1LK1RV_0LL---_1LL1LK_0RM1LH_1RM0LK_1LH0LK_0RN1LK_1LH0RN_0RQ1RN_0LD0RQ_1LD1RN_0RF0RQ_1RF1RQ_1LK0RF_1RV0RQ_---0RN_---1LK_---0LL_---1LL".
Definition tm0' := TM'_from_str "1LL0RQ_1LK1RQ_0LH0RF_1LH0RQ_0RN0RU_1LK1RU_0LL---_1LL1LK_0RM1LH_1RM0LK_1LH0LK_0RN1LK_1LH0RN_0RQ1RN_0LD0RQ_1LD1RN_0RF0RQ_1RF1RQ_1LK0RF_1RU0RQ_---1LK_---0RF_---0LS_---1LS".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RG_1LD0LC_1LE1LC_0RF1LC_0RA1RF_---1LC".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RG_1LD0LC_1LE1LC_0RF1LC_0RA1RF_1RH1LC_1RH1RH".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "QFKHLNV".
Definition mp' := mp_from_str "QFKHLNU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM149.


Module TM150.
Definition tm := TM_from_str "1LB0LE_1LC0RC_1RD1LF_1RE0RD_1LA0LB_0LE---".
Definition tm' := TM_from_str "1LB0RC_1LC0RC_1RD1LF_1RE0RD_1LA0LB_0LE---".
Definition tm0 := TM'_from_str "1LL0LD_1LS0LG_0LH0LS_1LH1LS_1RM0RI_1LX1RI_0LL0RN_1LL1LS_0RN1LS_1RN---_1RR0LX_1RM1LX_0RR0RM_1RR1RM_1LS0RR_0RN0RM_1LH0LL_1LS0RN_0LD0LG_1LD1LG_0LD---_0LG---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1LL0RI_1LS1RI_0LH0RN_1LH1LS_1RM0RI_1LX1RI_0LL0RN_1LL1LS_0RN1LS_1RN---_1RR0LX_1RM1LX_0RR0RM_1RR1RM_1LS0RR_0RN0RM_1LH0LL_1LS0RN_0LD0LG_1LD1LG_0LD---_0LG---_0LS---_1LS---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RA_0LG0LD_0LE0RA_1RF1LI_0RB0RF_1LH1LC_1LE1LC_1LC---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RA_0LG0LD_0LE0RA_1RF1LI_0RB0RF_1LH1LC_1LE1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;0]%N.
Definition mp := mp_from_str "NRSGLMDHX".
Definition mp' := mp_from_str "NRSGLMDHX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM150.


Module TM151.
Definition tm := TM_from_str "1LB0RC_1LC0RC_1RD1LF_1RE0RD_1LA0LB_0LE---".
Definition tm' := TM_from_str "1LB0LE_1LC0RC_1RD0LF_1RE0RD_1LA0LB_1RE---".
Definition tm0 := TM'_from_str "1LL0RI_1LS1RI_0LH0RN_1LH1LS_1RM0RI_1LX1RI_0LL0RN_1LL1LS_0RN1LS_1RN---_1RR0LX_1RM1LX_0RR0RM_1RR1RM_1LS0RR_0RN0RM_1LH0LL_1LS0RN_0LD0LG_1LD1LG_0LD---_0LG---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1LL0LD_1LS0LG_0LH0LS_1LH1LS_1RM0RI_1LW1RI_0LL0RN_1LL1LS_0RN1LS_1RN---_1RR0LW_1RM1LW_0RR0RM_1RR1RM_1LS0RR_0RN0RM_1LH0LL_1LS0RN_0LD0LG_1LD1LG_0RR---_1RR---_1LS---_0RN---".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RA_0LG0LD_0LE0RA_1RF1LI_0RB0RF_1LH1LC_1LE1LC_1LC---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RA_0LG0LD_0LE0RA_1RF1LI_0RB0RF_1LH1LC_1LE1LC_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;0]%N.
Definition mp := mp_from_str "NRSGLMDHX".
Definition mp' := mp_from_str "NRSGLMDHW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM151.


Module TM152.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD0RA_1RE0RD_0RF0RB_0LA---".
Definition tm' := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_1RF0RB_0LC---".
Definition tm0 := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN0RA_1RN1RA_1RR1LL_1RM1LH_0RR0RM_1RR1RM_1RU0RR_1RE0RM_0RU0RE_1RU1RE_0LH1RM_---0LH_0LH---_0LD---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_0LH1RM_---0LH_1RR---_0LH---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1RB1RH_0LC---_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC".
Definition tm2 := TM'_from_str "1RB1RH_0LC1RI_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "RUHCDLME".
Definition mp' := mp_from_str "RVHCDLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM152.


Module TM153.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_1RF0RB_0LC---".
Definition tm' := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_0RF0RB_0LA---".
Definition tm0 := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_0LH1RM_---0LH_1RR---_0LH---_0LK---_1LK---".
Definition tm0' := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RU0RR_1RE0RM_0RU0RE_1RU1RE_0LH1RM_---0LH_0LH---_0LD---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1RB1RH_0LC---_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC".
Definition tm2 := TM'_from_str "1RB1RH_0LC1RI_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "RVHCDLME".
Definition mp' := mp_from_str "RUHCDLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM153.


Module TM154.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_0RF0RB_0LA---".
Definition tm' := TM_from_str "1LB1LA_1LC0LA_1RD0RA_1RE0RD_1RF0RB_1LE---".
Definition tm0 := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RU0RR_1RE0RM_0RU0RE_1RU1RE_0LH1RM_---0LH_0LH---_0LD---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN0RA_1RN1RA_1RR1LL_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_0LH1RM_---0LH_------_0LH---_0LT---_1LT---".
Definition tm1 := TM'_from_str "1RB1RH_0LC---_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC".
Definition tm2 := TM'_from_str "1RB1RH_0LC1RI_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "RUHCDLME".
Definition mp' := mp_from_str "RVHCDLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM154.


Module TM155.
Definition tm := TM_from_str "1LB0LF_1LC1LE_1RD1LA_1RA0RD_0LA---_0LA0RC".
Definition tm' := TM_from_str "1LB0LE_1LC1LE_1RD1LA_1RA0RD_0LA0RF_1RD---".
Definition tm0 := TM'_from_str "1LL0LC_1LT0RN_0LH0LW_1LH1LW_1RM1LC_1LD---_0LL0LT_1LL1LT_0RN1LH_1RN1LW_1RB0LD_1RM1LD_0RB0RM_1RB1RM_1LT0RB_0RN0RM_0LH---_0LW---_0LC---_1LC---_0LH0RI_0LW1RI_0LC0RN_1LC1LH".
Definition tm0' := TM'_from_str "1LL0LC_1LT0RN_0LH0LS_1LH1LS_1RM1LC_1LD---_0LL0LT_1LL1LT_0RN1LH_1RN1LS_1RB0LD_1RM1LD_0RB0RM_1RB1RM_1LT0RB_0RN0RM_0LH0RU_0LS1RU_0LC0RN_1LC---_0RN---_1RN---_1RB---_1RM---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RI_1LD---_0LF0LE_0LD0RI_1LG1LC_1RA1LH_1LF1LE_1RB1RA".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RI_1LD1RJ_0LF0LE_0LD0RI_1LG1LC_1RA1LH_1LF1LE_1RB1RA_1RJ1RJ".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "MBTCWHLDN".
Definition mp' := mp_from_str "MBTCSHLDN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM155.


Module TM156.
Definition tm := TM_from_str "1LB0LF_1RC1LA_1RD0RC_0RE0RA_1RF---_1LA1LF".
Definition tm' := TM_from_str "1LB0LF_1RC0RF_1RD0RC_0RE0RA_1RF---_1LA1LF".
Definition tm0 := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ1LH_1RJ1LW_1RN0LD_1RI1LD_0RN0RI_1RN1RI_1RQ0RN_1RA0RI_0RQ0RA_1RQ1RA_0RV1RI_---0LD_0RV---_1RV---_1LW---_1LX---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm0' := TM'_from_str "1RI0LD_1LD0LX_0LH0LW_1LH1LW_0RJ0RU_1RJ1RU_1RN1LH_1RI1LD_0RN0RI_1RN1RI_1RQ0RN_1RA0RI_0RQ0RA_1RQ1RA_0RV1RI_---0LD_0RV---_1RV---_1LW---_1LX---_1LH1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm1 := TM'_from_str "1RB0LG_0RC0RB_1RD1RA_0RE---_1LF1LH_0LG0LH_1LI1LF_1LG1LH_1RB1LG".
Definition tm2 := TM'_from_str "1RB0LG_0RC0RB_1RD1RA_0RE1RJ_1LF1LH_0LG0LH_1LI1LF_1LG1LH_1RB1LG_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "AINQVWDXH".
Definition mp' := mp_from_str "AINQVWDXH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM156.


Module TM157.
Definition tm := TM_from_str "1LB1LF_1LC1LD_1RB---_0LA1RE_0RF0RD_1LA0RF".
Definition tm' := TM_from_str "1LB1LF_1LC1LE_1RD---_0RF0RE_0LA1RD_1LA0RF".
Definition tm0 := TM'_from_str "1LL1LD_1LP0RU_0LH0LX_1LH1LX_1RM1LC_---1RM_0LL0LP_1LL1LP_0RF---_1RF---_------_1RM---_0LH0RR_0LX1RR_0LC1RU_1LC1RM_0RU0RM_1RU1RM_1LH0LH_0RU0RR_1LH0RU_1LX1RU_0LD1LH_1LD0RU".
Definition tm0' := TM'_from_str "1LL1LD_1LT0RU_0LH0LX_1LH1LX_1RQ1LC_---1RQ_0LL0LT_1LL1LT_0RN---_1RN---_1RU---_1RQ---_0RU0RQ_1RU1RQ_1LH0LH_0RU0RN_0LH0RN_0LX1RN_0LC1RU_1LC1RQ_1LH0RU_1LX1RU_0LD1LH_1LD0RU".
Definition tm1 := TM'_from_str "1LB0RA_1LC1LF_1RD---_0LB0RE_1RA1RD_1LG1RD_0LB0LH_1LI0RA_1LB1LH".
Definition tm2 := TM'_from_str "1LB0RA_1LC1LF_1RD1RJ_0LB0RE_1RA1RD_1LG1RD_0LB0LH_1LI0RA_1LB1LH_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;0;0]%N.
Definition mp := mp_from_str "UHLMRPCXD".
Definition mp' := mp_from_str "UHLQNTCXD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM157.


Module TM158.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RA1LC_1LA0RC_0LF---_0RD1LB".
Definition tm' := TM_from_str "1LB0RD_1RC1LE_1RA1LC_1LA0RC_0LF---_0RD1LB".
Definition tm0 := TM'_from_str "1LL0RM_1LT1RM_0LH1LH_1LH0RI_1RM1LW_1LL---_0LL0LT_1LL1LT_0RB1RM_1RB1LL_1LT0LL_1RM1LL_1LH0RI_0RI1RI_0LD0RB_1LD1RM_1LH---_0LH---_0LW---_1LW---_0RM1LL_1RM1LT_1LH0LH_0RI1LH".
Definition tm0' := TM'_from_str "1LL0RM_1LT1RM_0LH1LH_1LH0RI_0RJ1LW_1RJ---_1RB0LT_1LL1LT_0RB1RM_1RB1LL_1LT0LL_1RM1LL_1LH0RI_0RI1RI_0LD0RB_1LD1RM_1LH---_0LH---_0LW---_1LW---_0RM1LL_1RM1LT_1LH0LH_0RI1LH".
Definition tm1 := TM'_from_str "0RB1RG_1LC1RG_1LD---_1LE0LE_1LF1LC_1RG1LF_1LE0RA".
Definition tm2 := TM'_from_str "0RB1RG_1LC1RG_1LD1RH_1LE0LE_1LF1LC_1RG1LF_1LE0RA_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IBTWHLM".
Definition mp' := mp_from_str "IBTWHLM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM158.


Module TM159.
Definition tm := TM_from_str "1LB0LF_1RC1LC_0RE0RD_0RB1RC_1LA1LE_0LB---".
Definition tm' := TM_from_str "1LB0LF_1RC1LC_0RE0RD_0RB0LD_1LA1LE_0LB---".
Definition tm0 := TM'_from_str "1RM0LG_1LL---_0LH0LW_1LH1LW_0RJ1LD_1RJ0RJ_1RQ0LL_1RM1LL_0RQ0RM_1RQ1RM_1LH0RE_1LD0RJ_0RE0RJ_1RE1RJ_0RJ1RQ_1LD1RM_1LH1LD_1LW1LT_0LD0LT_1LD1LT_1RQ---_0LL---_0LG---_1LG---".
Definition tm0' := TM'_from_str "1RM0LG_1LL---_0LH0LW_1LH1LW_0RJ1LD_1RJ0RJ_1RQ0LL_1RM1LL_0RQ0RM_1RQ1RM_1LH0RE_1LD0RJ_0RE0RJ_1RE0LO_0RJ0LO_1LD1LO_1LH1LD_1LW1LT_0LD0LT_1LD1LT_1RQ---_0LL---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1RB1RH_1LC1LE_1RH1LD_1LE0RA_1LC1LF_0LG---_1RB0LD_0RI0RA_0RA1LE".
Definition tm2 := TM'_from_str "1RB1RH_1LC1LE_1RH1LD_1LE0RA_1LC1LF_0LG1RJ_1RB0LD_0RI0RA_0RA1LE_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JQHLDWGME".
Definition mp' := mp_from_str "JQHLDWGME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM159.


Module TM160.
Definition tm := TM_from_str "1LB0LF_1RC1LE_0RE0RD_0RB1RC_1LA0RD_0LB---".
Definition tm' := TM_from_str "1LB0LF_1RC1LE_0RE0RD_0RB0LD_1LA0RD_0LB---".
Definition tm0 := TM'_from_str "1RM0LG_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ0RJ_1RQ0LT_1RM1LT_0RQ0RM_1RQ1RM_1LH0RE_0RM0RJ_0RE0RJ_1RE1RJ_0RJ1RQ_1LD1RM_1LH0RM_1LW1RM_0LD0RE_1LD0RJ_1RQ---_0LT---_0LG---_1LG---".
Definition tm0' := TM'_from_str "1RM0LG_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ0RJ_1RQ0LT_1RM1LT_0RQ0RM_1RQ1RM_1LH0RE_0RM0RJ_0RE0RJ_1RE0LO_0RJ0LO_1LD1LO_1LH0RM_1LW1RM_0LD0RE_1LD0RJ_1RQ---_0LT---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RH_1RH1LD_1LE0RA_1LC1LF_0LG---_1RB0LD_0RI0RA_0RA1LE".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RH_1RH1LD_1LE0RA_1LC1LF_0LG1RJ_1RB0LD_0RI0RA_0RA1LE_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JQHTDWGME".
Definition mp' := mp_from_str "JQHTDWGME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM160.


Module TM161.
Definition tm := TM_from_str "1RB1LE_0RC0LB_1LD0RA_0LA0LD_0LF0RB_1LD---".
Definition tm' := TM_from_str "1RB1LE_0RC0LB_1LD0RA_0LA0LD_0LF0LA_1LD---".
Definition tm0 := TM'_from_str "0RF1LW_1RF1LC_1RI0LT_0LG1LT_0RI1LC_1RI0LG_1LC0LG_0RA1LG_1LC0RA_1LO1RA_0LP0RF_1LP1LW_1RI0LC_0LT0LO_0LC0LO_1LC1LO_0LP0RE_---1RE_0LW0RI_1LW1LC_1LC---_1LO---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF1LW_1RF1LC_1RI0LT_0LG1LT_0RI1LC_1RI0LG_1LC0LG_0RA1LG_1LC0RA_1LO1RA_0LP0RF_1LP1LW_1RI0LC_0LT0LO_0LC0LO_1LC1LO_0LP1RI_---0LT_0LW0LC_1LW1LC_1LC---_1LO---_0LP---_1LP---".
Definition tm1 := TM'_from_str "1LB0RG_1RA0LC_1LD1LB_0LE---_1LB1LF_0LB0LF_0RH1LD_1RA0LI_1LB0LI".
Definition tm2 := TM'_from_str "1LB0RG_1RA0LC_1LD1LB_0LE1RJ_1LB1LF_0LB0LF_0RH1LD_1RA0LI_1LB0LI_1RJ1RJ".
Definition l0 := [1;1;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "ICTWPOAFG".
Definition mp' := mp_from_str "ICTWPOAFG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM161.


Module TM162.
Definition tm := TM_from_str "1LB0LA_1LC1LF_1RD0RC_0LD1RE_1LA0RC_---0LE".
Definition tm' := TM_from_str "1LB0LA_1LC1LF_1RD0RC_1LA1RE_1LA0RC_---0LE".
Definition tm0 := TM'_from_str "1LL0LH_1LX0LC_0LH0LC_1LH1LC_1RR---_0RI1LS_0LL0LX_1LL1LX_0RN0RI_1RN1RI_1LC0RN_1RR0RI_0LO0RR_1LC1RR_0LO1LC_1LO1RI_1LH0RI_1LC1RI_0LD0RN_1LD0RI_---0LD_---0RN_---0LS_---1LS".
Definition tm0' := TM'_from_str "1LL0LH_1LX0LC_0LH0LC_1LH1LC_1RR---_0RI1LS_0LL0LX_1LL1LX_0RN0RI_1RN1RI_1LC0RN_1RR0RI_1LH0RR_1LC1RR_0LD1LC_1LD1RI_1LH0RI_1LC1RI_0LD0RN_1LD0RI_---0LD_---0RN_---0LS_---1LS".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1LG1LD_---1LE_0LF0RI_1LC1LB_1RA0RH_0RI0RH_1LB1RA".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1LG1LD_1RJ1LE_0LF0RI_1LC1LB_1RA0RH_0RI0RH_1LB1RA_1RJ1RJ".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "RCHXSDLIN".
Definition mp' := mp_from_str "RCHXSDLIN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM162.


Module TM163.
Definition tm := TM_from_str "1LB0RF_1LC1RD_1RB1RE_1RE0RD_0RA0LE_0RD---".
Definition tm' := TM_from_str "1LB1RF_1LC1RD_1RB1RE_1RE0RD_0RA0LE_1LD---".
Definition tm0 := TM'_from_str "1LL0RU_1RM1RU_0LH0RM_1LH---_1RN0RN_0LS1RN_0LL1RR_1LL1RM_0RF0RR_1RF1RR_0LS1RA_1RN0LS_0RR0RM_1RR1RM_1RA0RR_0LS0RM_0RA1LL_1RA0LS_1LL0LS_0RU1LS_0RM---_1RM---_0RR---_0RM---".
Definition tm0' := TM'_from_str "1LL0RV_1RM1RV_0LH0RM_1LH---_1RN0RN_0LS1RN_0LL1RR_1LL1RM_0RF0RR_1RF1RR_0LS1RA_1RN0LS_0RR0RM_1RR1RM_1RA0RR_0LS0RM_0RA1LL_1RA0LS_1LL0LS_0RV1LS_0LS---_0RM---_0LP---_1LP---".
Definition tm1 := TM'_from_str "1RB0LD_1LC0RG_1RE0LD_1LC0LD_1RA1RF_0RA0RF_0RF---".
Definition tm2 := TM'_from_str "1RB0LD_1LC0RG_1RE0LD_1LC0LD_1RA1RF_0RA0RF_0RF1RH_1RH1RH".
Definition l0 := [1;1;0;1;0;0;0;0]%N.
Definition mp := mp_from_str "RALSNMU".
Definition mp' := mp_from_str "RALSNMV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM163.


Module TM164.
Definition tm := TM_from_str "1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA1LD_---1LD".
Definition tm' := TM_from_str "1RB1LE_0RC1RC_1LD0RD_0LE0LA_1RF0LB_1RB---".
Definition tm0 := TM'_from_str "0RF---_1RF1LP_1RI0LX_1RJ1LX_0RI0RJ_1RI1RJ_1LS1LC_0RM1RM_1LS0RM_1LC1RM_0LP1RF_1LP1RI_1RF1RI_0LP0LX_0LS0LC_1LS1LC_0RB1LS_1RB1LC_1RF0LP_1LP1LP_---1LS_---1LC_---0LP_---1LP".
Definition tm0' := TM'_from_str "0RF---_1RF1LG_1RI0LT_1RJ1LT_0RI0RJ_1RI1RJ_1LS1LC_0RM1RM_1LS0RM_1LC1RM_0LP1RF_1LP1RI_1RF1RI_0LG0LT_0LS0LC_1LS1LC_0RV1LS_1RV1LC_1RF0LG_---1LG_0RF---_1RF---_1RI---_1RJ---".
Definition tm1 := TM'_from_str "1LB0RF_1RG0LC_1LB1LD_1RA0LE_---1LC_1RG1RA_1RA1RH_1LD1RF".
Definition tm2 := TM'_from_str "1LB0RF_1RG0LC_1LB1LD_1RA0LE_1RI1LC_1RG1RA_1RA1RH_1LD1RF_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "ISPCXMFJ".
Definition mp' := mp_from_str "ISGCTMFJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM164.


Module TM165.
Definition tm := TM_from_str "1RB1LE_0RC1RC_1LD0RD_0LE0LA_1RF0LB_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RC_1LD0RD_0LE0LF_1RA1LD_1RB1LE".
Definition tm0 := TM'_from_str "0RF---_1RF1LG_1RI0LT_1RJ1LT_0RI0RJ_1RI1RJ_1LS1LC_0RM1RM_1LS0RM_1LC1RM_0LP1RF_1LP1RI_1RF1RI_0LG0LT_0LS0LC_1LS1LC_0RV1LS_1RV1LC_1RF0LG_---1LG_0RF---_1RF---_1RI---_1RJ---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RI---_1RJ---_0RI0RJ_1RI1RJ_1LS1LW_0RM1RM_1LS0RM_1LW1RM_0LP1RF_1LP1RI_1RF1RI_0LP0LT_0LS0LW_1LS1LW_0RB1LS_1RB1LW_1RF0LP_---1LP_0RF---_1RF1LP_1RI0LT_1RJ1LT".
Definition tm1 := TM'_from_str "1LB0RF_1RG0LC_1LB1LD_1RA0LE_---1LC_1RG1RA_1RA1RH_1LD1RF".
Definition tm2 := TM'_from_str "1LB0RF_1RG0LC_1LB1LD_1RA0LE_1RI1LC_1RG1RA_1RA1RH_1LD1RF_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "ISGCTMFJ".
Definition mp' := mp_from_str "ISPWTMFJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM165.


Module TM166.
Definition tm := TM_from_str "1RB---_0RC1RC_1LD0RD_0LE0LF_1RA1LD_1RB1LE".
Definition tm' := TM_from_str "1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---0LB".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RI---_1RJ---_0RI0RJ_1RI1RJ_1LS1LW_0RM1RM_1LS0RM_1LW1RM_0LP1RF_1LP1RI_1RF1RI_0LP0LT_0LS0LW_1LS1LW_0RB1LS_1RB1LW_1RF0LP_---1LP_0RF---_1RF1LP_1RI0LT_1RJ1LT".
Definition tm0' := TM'_from_str "0RF---_1RF1LG_1RI0LX_1RJ1LX_0RI0RJ_1RI1RJ_1LS1LC_0RM1RM_1LS0RM_1LC1RM_0LP1RF_1LP1RI_1RF1RI_0LG0LX_0LS0LC_1LS1LC_0RB1LS_1RB1LC_1RF0LG_1LG1LG_---1LS_---1LC_---0LG_---1LG".
Definition tm1 := TM'_from_str "1LB0RF_1RG0LC_1LB1LD_1RA0LE_---1LC_1RG1RA_1RA1RH_1LD1RF".
Definition tm2 := TM'_from_str "1LB0RF_1RG0LC_1LB1LD_1RA0LE_1RI1LC_1RG1RA_1RA1RH_1LD1RF_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "ISPWTMFJ".
Definition mp' := mp_from_str "ISGCXMFJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM166.


Module TM167.
Definition tm := TM_from_str "1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA1LD_---0LB".
Definition tm' := TM_from_str "1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD".
Definition tm0 := TM'_from_str "0RF---_1RF1LG_1RI0LX_1RJ1LX_0RI0RJ_1RI1RJ_1LS1LC_0RM1RM_1LS0RM_1LC1RM_0LP1RF_1LP1RI_1RF1RI_0LP0LX_0LS0LC_1LS1LC_0RB1LS_1RB1LC_1RF0LP_1LG1LP_---1LS_---1LC_---0LG_---1LG".
Definition tm0' := TM'_from_str "0RF---_1RF1LP_1RI0LX_1RJ1LX_0RI0RJ_1RI1RJ_1LS1LC_0RM1RM_1LS0RM_1LC1RM_0LP1RF_1LP1RI_1RF1RI_0LG0LX_0LS0LC_1LS1LC_0RB1LS_1RB1LC_1RF0LG_1LP1LG_---1LS_---1LC_---0LP_---1LP".
Definition tm1 := TM'_from_str "1LB0RG_1RH0LC_1LB1LD_1RA0LE_---1LF_1LB1LD_1RH1RA_1RA1RI_1LD1RG".
Definition tm2 := TM'_from_str "1LB0RG_1RH0LC_1LB1LD_1RA0LE_1RJ1LF_1LB1LD_1RH1RA_1RA1RI_1LD1RG_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "ISPCXGMFJ".
Definition mp' := mp_from_str "ISGCXPMFJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM167.


Module TM168.
Definition tm := TM_from_str "1LB0LA_0LC0LE_0RD---_1RE1RD_1RF0RD_1LA1RE".
Definition tm' := TM_from_str "1LB0LA_1LC0LD_1RB---_1RF0RE_1RD1RE_1LA1RD".
Definition tm0 := TM'_from_str "1LK0LH_1LS0LC_0LH0LC_1LH1LC_0RR1LC_---0RR_0LK0LS_1LK1LS_0RM---_1RM---_0RR---_0RN---_0RR0RN_1RR1RN_1RV1RR_1RM1RN_0RV0RM_1RV1RM_1LC0RR_1RR0RN_1LH0RR_1LC1RR_0LD1RV_1LD1RM".
Definition tm0' := TM'_from_str "1LL0LH_1LO0LC_0LH0LC_1LH1LC_0RN1LC_---0RN_0LL0LO_1LL1LO_0RF---_1RF---_------_0RN---_0RV0RQ_1RV1RQ_1LC0RN_1RN0RR_0RN0RR_1RN1RR_1RV1RN_1RQ1RR_1LH0RN_1LC1RN_0LD1RV_1LD1RQ".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA---_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA1RI_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "RVCHSKMN".
Definition mp' := mp_from_str "NVCHOLQR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM168.


Module TM169.
Definition tm := TM_from_str "1LB0LA_1LC0LD_1RB---_1RF0RE_1RD1RE_1LA1RD".
Definition tm' := TM_from_str "1LB0LA_1LC0LE_0RD---_1LA1RE_1RD0RF_1RE1RF".
Definition tm0 := TM'_from_str "1LL0LH_1LO0LC_0LH0LC_1LH1LC_0RN1LC_---0RN_0LL0LO_1LL1LO_0RF---_1RF---_------_0RN---_0RV0RQ_1RV1RQ_1LC0RN_1RN0RR_0RN0RR_1RN1RR_1RV1RN_1RQ1RR_1LH0RN_1LC1RN_0LD1RV_1LD1RQ".
Definition tm0' := TM'_from_str "1LL0LH_1LS0LC_0LH0LC_1LH1LC_0RR1LC_---0RR_0LL0LS_1LL1LS_0RM---_1RM---_1LH---_0RR---_1LH0RR_1LC1RR_0LD1RN_1LD1RU_0RN0RU_1RN1RU_1LC0RR_1RR0RV_0RR0RV_1RR1RV_1RN1RR_1RU1RV".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA---_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA1RI_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "NVCHOLQR".
Definition mp' := mp_from_str "RNCHSLUV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM169.


Module TM170.
Definition tm := TM_from_str "1LB0LA_1LC0LE_0RD---_1LA1RE_1RD0RF_1RE1RF".
Definition tm' := TM_from_str "1LB0LA_1LC0LD_1RB---_1RF0RE_1RD1RE_1LA0LE".
Definition tm0 := TM'_from_str "1LL0LH_1LS0LC_0LH0LC_1LH1LC_0RR1LC_---0RR_0LL0LS_1LL1LS_0RM---_1RM---_1LH---_0RR---_1LH0RR_1LC1RR_0LD1RN_1LD1RU_0RN0RU_1RN1RU_1LC0RR_1RR0RV_0RR0RV_1RR1RV_1RN1RR_1RU1RV".
Definition tm0' := TM'_from_str "1LL0LH_1LO0LC_0LH0LC_1LH1LC_0RN1LC_---0RN_0LL0LO_1LL1LO_0RF---_1RF---_------_0RN---_0RV0RQ_1RV1RQ_1LC0RN_1RN0RR_0RN0RR_1RN1RR_1RV1RN_1RQ1RR_1LH1RV_1LC1RN_0LD0LS_1LD1LS".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA---_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA1RI_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "RNCHSLUV".
Definition mp' := mp_from_str "NVCHOLQR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM170.


Module TM171.
Definition tm := TM_from_str "1LB0LA_1LC0LD_1RB---_1RF0RE_1RD1RE_1LA0LE".
Definition tm' := TM_from_str "1LB0LA_0LC0LE_0RD---_1RE1RD_1RF0RD_1LA0LD".
Definition tm0 := TM'_from_str "1LL0LH_1LO0LC_0LH0LC_1LH1LC_0RN1LC_---0RN_0LL0LO_1LL1LO_0RF---_1RF---_------_0RN---_0RV0RQ_1RV1RQ_1LC0RN_1RN0RR_0RN0RR_1RN1RR_1RV1RN_1RQ1RR_1LH1RV_1LC1RN_0LD0LS_1LD1LS".
Definition tm0' := TM'_from_str "1LK0LH_1LS0LC_0LH0LC_1LH1LC_0RR1LC_---0RR_0LK0LS_1LK1LS_0RM---_1RM---_0RR---_0RN---_0RR0RN_1RR1RN_1RV1RR_1RM1RN_0RV0RM_1RV1RM_1LC0RR_1RR0RN_1LH1RV_1LC1RR_0LD0LO_1LD1LO".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA---_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RA_0LD0LC_1LF1LE_1LC0RA_0RA1RI_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "NVCHOLQR".
Definition mp' := mp_from_str "RVCHSKMN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM171.


Module TM172.
Definition tm := TM_from_str "1LB1LC_1RC0RE_1LF0RD_0LA1LD_1RB1RE_---1RD".
Definition tm' := TM_from_str "1LB1LC_1RC0RE_1LF0RD_0LA1LD_1RB1RE_---1LD".
Definition tm0 := TM'_from_str "1RM1LX_0RR1LC_0LH0LL_1LH1LL_0RJ0RQ_1RJ1RQ_1LP0RF_1RM0RR_---0RM_1LP1RM_0LX0LH_1LX1LC_0LH1LC_0LL1LP_0LC0LP_1LC1LP_0RF0RR_1RF1RR_1RJ1RF_1RQ1RR_---0RN_---1RN_---0LL_---1LP".
Definition tm0' := TM'_from_str "1RM1LX_0RR1LC_0LH0LL_1LH1LL_0RJ0RQ_1RJ1RQ_1LP0RF_1RM0RR_---0RM_1LP1RM_0LX0LH_1LX1LC_0LH1LC_0LL1LP_0LC0LP_1LC1LP_0RF0RR_1RF1RR_1RJ1RF_1RQ1RR_---1LC_---1LP_---0LP_---1LP".
Definition tm1 := TM'_from_str "1LB1RF_1LC1LB_0LE0LD_1LJ1LC_1RF0RG_0LE1LC_1RH1RG_1RA1RI_0RH0RG_---1LB".
Definition tm2 := TM'_from_str "1LB1RF_1LC1LB_0LE0LD_1LJ1LC_1RF0RG_0LE1LC_1RH1RG_1RA1RI_0RH0RG_1RK1LB_1RK1RK".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLHMRFQX".
Definition mp' := mp_from_str "JPCLHMRFQX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM172.


Module TM173.
Definition tm := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_1LB---".
Definition tm' := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0RA---".
Definition tm0 := TM'_from_str "0RF0LP_1RF0RA_1RJ0LK_1RB1LK_0RJ0RB_1RJ1RB_1LP1RF_1RQ0RA_1LD0RQ_1LP1RQ_0LP0RA_1LP0RV_1RB1LD_1LK1LP_0LD0LP_1LD1LP_0RA0RV_1RA1RV_0RF0RA_0LP---_1RQ---_0RA---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0LP_1RF0RA_1RJ0LK_1RB1LK_0RJ0RB_1RJ1RB_1LP1RF_1RQ0RA_1LD0RQ_1LP1RQ_0LP0RA_1LP0RU_1RB1LD_1LK1LP_0LD0LP_1LD1LP_0RA0RU_1RA1RU_0RF0RA_0LP---_0RA---_1RA---_0RF---_0LP---".
Definition tm1 := TM'_from_str "1RB1RE_1LC1RH_1LD1LC_1RE1LG_1RA0RF_0RA0LC_0LC0RF_0RF0RI_0RF---".
Definition tm2 := TM'_from_str "1RB1RE_1LC1RH_1LD1LC_1RE1LG_1RA0RF_0RA0LC_0LC0RF_0RF0RI_0RF1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;1;1]%N.
Definition mp := mp_from_str "FJPDBAKQV".
Definition mp' := mp_from_str "FJPDBAKQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM173.


Module TM174.
Definition tm := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0RA---".
Definition tm' := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---".
Definition tm0 := TM'_from_str "0RF0LP_1RF0RA_1RJ0LK_1RB1LK_0RJ0RB_1RJ1RB_1LP1RF_1RQ0RA_1LD0RQ_1LP1RQ_0LP0RA_1LP0RU_1RB1LD_1LK1LP_0LD0LP_1LD1LP_0RA0RU_1RA1RU_0RF0RA_0LP---_0RA---_1RA---_0RF---_0LP---".
Definition tm0' := TM'_from_str "0RF0LP_1RF0RA_1RJ0LK_1RB1LK_0RJ0RB_1RJ1RB_1LP1RF_1RQ0RA_1LD0RQ_1LP1RQ_0LP0RA_1LP0RV_1RB1LD_1LK1LP_0LD0LP_1LD1LP_0RA0RV_1RA1RV_0RF0RA_0LP---_0LP---_0RA---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1RB1RE_1LC1RH_1LD1LC_1RE1LG_1RA0RF_0RA0LC_0LC0RF_0RF0RI_0RF---".
Definition tm2 := TM'_from_str "1RB1RE_1LC1RH_1LD1LC_1RE1LG_1RA0RF_0RA0LC_0LC0RF_0RF0RI_0RF1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;1;1]%N.
Definition mp := mp_from_str "FJPDBAKQU".
Definition mp' := mp_from_str "FJPDBAKQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM174.


Module TM175.
Definition tm := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB0RF_1LA---".
Definition tm' := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB1RF_0RB---".
Definition tm0 := TM'_from_str "0RF0LP_1RF0RF_1RJ0LK_1RE1LK_0RJ0RE_1RJ1RE_1LO0RJ_1RQ0RE_1LD0RQ_1LO1RQ_0LP0RF_1LP0RU_1RE0LD_1LK0LO_0LD0LO_1LD1LO_0RF0RU_1RF1RU_1RJ1RE_1RE---_1RE---_1LK---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RF0LP_1RF0RF_1RJ0LK_1RE1LK_0RJ0RE_1RJ1RE_1LO0RJ_1RQ0RE_1LD0RQ_1LO1RQ_0LP0RF_1LP0RV_1RE0LD_1LK0LO_0LD0LO_1LD1LO_0RF0RV_1RF1RV_1RJ1RE_1RE---_0RE---_1RE---_0RJ---_0RE---".
Definition tm1 := TM'_from_str "1LB1RE_0LC0LB_1RD1LG_0RA0RD_0RF0RI_1RA1RD_0LH0RF_1LC1LB_1RD---".
Definition tm2 := TM'_from_str "1LB1RE_0LC0LB_1RD1LG_0RA0RD_0RF0RI_1RA1RD_0LH0RF_1LC1LB_1RD1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;0]%N.
Definition mp := mp_from_str "JODEQFKPU".
Definition mp' := mp_from_str "JODEQFKPV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM175.


Module TM176.
Definition tm := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB1RF_0RB---".
Definition tm' := TM_from_str "1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LA---".
Definition tm0 := TM'_from_str "0RF0LP_1RF0RF_1RJ0LK_1RE1LK_0RJ0RE_1RJ1RE_1LO0RJ_1RQ0RE_1LD0RQ_1LO1RQ_0LP0RF_1LP0RV_1RE0LD_1LK0LO_0LD0LO_1LD1LO_0RF0RV_1RF1RV_1RJ1RE_1RE---_0RE---_1RE---_0RJ---_0RE---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1RJ1RE_1RE---_0RJ0RE_1RJ1RE_1LO0RJ_1RA0RE_1LT0RA_1LO1RA_0LP0RF_1LP0RU_1RE0LT_1LK0LO_0LT0LO_1LT1LO_0RF0LP_1RF0RF_1RJ0LK_1RE1LK_1RE---_------_0LD---_1LD---".
Definition tm1 := TM'_from_str "1LB1RE_0LC0LB_1RD1LG_0RA0RD_0RF0RI_1RA1RD_0LH0RF_1LC1LB_1RD---".
Definition tm2 := TM'_from_str "1LB1RE_0LC0LB_1RD1LG_0RA0RD_0RF0RI_1RA1RD_0LH0RF_1LC1LB_1RD1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;0]%N.
Definition mp := mp_from_str "JODEQFKPV".
Definition mp' := mp_from_str "JOTEAFKPU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM176.


Module TM177.
Definition tm := TM_from_str "1LB---_1LC0LE_1RD1LF_1RE0RD_0RF0RD_0LB0LA".
Definition tm' := TM_from_str "1LB---_1LC0LD_1RD1LF_0RF0RE_1RD0RE_0LB0LA".
Definition tm0 := TM'_from_str "1LL---_1LS---_0LH---_1LH---_1RM0LL_1LX0RR_0LL0LS_1LL1LS_0RN1LG_1RN1LC_1RR0LX_1RM1LX_0RR0RM_1RR1RM_1RU0RR_1RM0RM_0RU0RM_1RU1RM_0LL0RR_0LH0RM_0LL0LH_0LS---_0LG0LC_1LG1LC".
Definition tm0' := TM'_from_str "1LL---_1LO---_0LH---_1LH---_1RQ0LL_1LX0RN_0LL0LO_1LL1LO_0RN1LG_1RN1LC_1RU0LX_1RQ1LX_0RU0RQ_1RU1RQ_0LL0RN_0LH0RQ_0RN0RQ_1RN1RQ_1RU0RN_1RQ0RQ_0LL0LH_0LO---_0LG0LC_1LG1LC".
Definition tm1 := TM'_from_str "1RB1RG_0LC0LH_1RG1LD_1LE1LI_0LC0LF_0LC0RA_0RA0RG_1LC1LF_0LH---".
Definition tm2 := TM'_from_str "1RB1RG_0LC0LH_1RG1LD_1LE1LI_0LC0LF_0LC0RA_0RA0RG_1LC1LF_0LH1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "RULXGSMHC".
Definition mp' := mp_from_str "NULXGOQHC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM177.


Module TM178.
Definition tm := TM_from_str "1RB0LC_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---".
Definition tm0 := TM'_from_str "0RF0LP_1RF0RF_1RJ0LK_1RE1LK_0RJ0RE_1RJ1RE_1LK0RJ_1RA0RE_1LS0RA_1LK1RA_0LP0RF_1LP0LP_0LH0LP_0LX0RF_0LS0LK_1LS1LK_1RA1LP_0RE---_0LH0LX_1LH1LX_1LS---_1LK---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF0LP_1RF---_1RJ0LW_1RE1LW_0RJ0RE_1RJ1RE_1LK0RJ_1RA0RE_1LS0RA_1LK1RA_0LP0RF_1LP0LP_0LH0LP_0LX0RF_0LS0LK_1LS1LK_1RA1LP_0RE---_0LH0LX_1LH1LX_1LS---_1LK---_0LP---_1LP---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0RG_1LD1LB_0LE0LI_1RF0RH_0RG0LC_1RA1RH_0RA0RH_1LC---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0RG_1LD1LB_0LE0LI_1RF0RH_0RG0LC_1RA1RH_0RA0RH_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JKPSHAFEX".
Definition mp' := mp_from_str "JKPSHAFEX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM178.


Module TM179.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1LD0LE_1RA---_1RA0RF_1RE0RB".
Definition tm' := TM_from_str "1LB1RF_1LC0LB_0LD0LF_1RE---_1RF0RB_1RA0RE".
Definition tm0 := TM'_from_str "1LL0RR_1LG1RR_0LH1RB_1LH1RU_1LP0LL_1LS0LG_0LL0LG_1LL1LG_1RR1LG_---0RR_0LP0LS_1LP1LS_0RB---_1RB---_1LG---_1RR---_0RB0RU_1RB1RU_1LG0RR_1RR0RE_0RR0RE_1RR1RE_1RB1LP_1RU0LL".
Definition tm0' := TM'_from_str "1LL0RV_1LG1RV_0LH1RB_1LH1RQ_1LO0LL_1LW0LG_0LL0LG_1LL1LG_1RV1LG_---0RV_0LO0LW_1LO1LW_0RR---_1RR---_1RV---_1RE---_0RV0RE_1RV1RE_1RB1LO_1RQ0LL_0RB0RQ_1RB1RQ_1LG0RV_1RV0RE".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LB_1LE1LD_1LB0RF_1RF---_1RA1RG_0RF0RH_1LE0LC".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LB_1LE1LD_1LB0RF_1RF1RI_1RA1RG_0RF0RH_1LE0LC_1RI1RI".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "BGLSPRUE".
Definition mp' := mp_from_str "BGLWOVQE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM179.


Module TM180.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RE".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LA_0LF0RE_0RD1RB_---0RA".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD0RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_1LP0RQ_0RF1RQ_0LP0RU_1LP0RF_0RU0RF_1RU1RF_---1LL_0RQ1RN_---0RQ_---1RQ_---0RU_---0RF".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD0RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_0RF1RQ_0LW0RM_1LW0RF_0RM0RF_1RM1RF_---1LL_0RQ1RN_---0RA_---1RA_---0RF_---1LD".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_0RA1RF_0RG0RA_---0RF".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_0RA1RF_0RG0RA_1RH0RF_1RH1RH".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "FLDCNQU".
Definition mp' := mp_from_str "FLDCNQM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM180.


Module TM181.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA0LA_0LF0RE_0RD1RB_---0RA".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LF0RE_0RF1RB_---0RE".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD0RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_0RF1RQ_0LW0RM_1LW0RF_0RM0RF_1RM1RF_---1LL_0RQ1RN_---0RA_---1RA_---0RF_---1LD".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD0RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_0RF1RQ_0LX0RU_1LX0RF_0RU0RF_1RU1RF_---1LL_0RQ1RN_---0RQ_---1RQ_---0RU_---0RF".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_0RA1RF_0RG0RA_---0RF".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_0RA1RF_0RG0RA_1RH0RF_1RH1RH".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "FLDCNQM".
Definition mp' := mp_from_str "FLDCNQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM181.


Module TM182.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LF0RE_0RF1RB_---0RE".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LF0RE_0RD1RB_---0RE".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD0RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_0RF1RQ_0LX0RU_1LX0RF_0RU0RF_1RU1RF_---1LL_0RQ1RN_---0RQ_---1RQ_---0RU_---0RF".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD0RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_0RF1RQ_0LX0RM_1LX0RF_0RM0RF_1RM1RF_---1LL_0RQ1RN_---0RQ_---1RQ_---0RM_---0RF".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_0RA1RF_0RG0RA_---0RF".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_0RA1RF_0RG0RA_1RH0RF_1RH1RH".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "FLDCNQU".
Definition mp' := mp_from_str "FLDCNQM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM182.


Module TM183.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1RB0RE_0RF1RB_---0RE".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LF0RE_0RD1RB_---1RE".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD1RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_0RF0RQ_1RF1RQ_1LL0RU_1RN0RF_0RU0RF_1RU1RF_---1LL_0RQ1RN_---0RQ_---1RQ_---0RU_---0RF".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD1RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_1RF1RQ_0LX0RM_1LX0RF_0RM0RF_1RM1RF_---1LL_0RQ1RN_---0RR_---1RR_---1RM_---1RF".
Definition tm1 := TM'_from_str "1LB1RE_1LD1LC_1LB0LB_1RE1LB_1RA1RF_0RG0RA_---0RF".
Definition tm2 := TM'_from_str "1LB1RE_1LD1LC_1LB0LB_1RE1LB_1RA1RF_0RG0RA_1RH0RF_1RH1RH".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "FLCDNQU".
Definition mp' := mp_from_str "FLCDNQM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM183.


Module TM184.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LF0RE_0RD1RB_---1RE".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LA_0LF0RE_0RD1RB_---1RA".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD1RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_1RF1RQ_0LX0RM_1LX0RF_0RM0RF_1RM1RF_---1LL_0RQ1RN_---0RR_---1RR_---1RM_---1RF".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD1RF_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_1RF1RQ_0LW0RM_1LW0RF_0RM0RF_1RM1RF_---1LL_0RQ1RN_---0RB_---1RB_---1RF_---1LC".
Definition tm1 := TM'_from_str "1LB1RE_1LD1LC_1LB0LB_1RE1LB_1RA1RF_0RG0RA_---0RF".
Definition tm2 := TM'_from_str "1LB1RE_1LD1LC_1LB0LB_1RE1LB_1RA1RF_0RG0RA_1RH0RF_1RH1RH".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "FLCDNQM".
Definition mp' := mp_from_str "FLCDNQM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM184.


Module TM185.
Definition tm := TM_from_str "1LB1RF_1LC0LB_1RD1LC_1RA1RE_1RC0RD_0LD---".
Definition tm' := TM_from_str "1LB1RF_1LC0LB_1RD1LC_1RA1RE_1RC0RD_1RC---".
Definition tm0 := TM'_from_str "1LL0RV_1LG1RV_0LH1RJ_1LH---_1RR0LL_1LL0LG_0LL0LG_1LL1LG_0RN1RR_1RN1LL_1RB0LL_1RR1LL_0RB0RR_1RB1RR_1LG1RJ_1RV1RM_0RJ0RM_1RJ1RM_1RN0RB_1LL0RR_1LG---_1RJ---_0LO---_1LO---".
Definition tm0' := TM'_from_str "1LL0RV_1LG1RV_0LH1RJ_1LH---_1RR0LL_1LL0LG_0LL0LG_1LL1LG_0RN1RR_1RN1LL_1RB0LL_1RR1LL_0RB0RR_1RB1RR_1LG1RJ_1RV1RM_0RJ0RM_1RJ1RM_1RN0RB_1LL0RR_0RJ---_1RJ---_1RN---_1LL---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RD1LC_1RF1RE_0RA0RD_1RG1LC_1RA1RD_1RF---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RD1LC_1RF1RE_0RA0RD_1RG1LC_1RA1RD_1RF1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "BGLRMJNV".
Definition mp' := mp_from_str "BGLRMJNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM185.


Module TM186.
Definition tm := TM_from_str "1LB1RF_1LC0LB_1RD1LC_1RA1RE_1RC0RD_1RC---".
Definition tm' := TM_from_str "1LB1RF_1LC0LB_1RD1LC_1RA1RE_0LA0RD_1RC---".
Definition tm0 := TM'_from_str "1LL0RV_1LG1RV_0LH1RJ_1LH---_1RR0LL_1LL0LG_0LL0LG_1LL1LG_0RN1RR_1RN1LL_1RB0LL_1RR1LL_0RB0RR_1RB1RR_1LG1RJ_1RV1RM_0RJ0RM_1RJ1RM_1RN0RB_1LL0RR_0RJ---_1RJ---_1RN---_1LL---".
Definition tm0' := TM'_from_str "1LL0RV_1LG1RV_0LH1RJ_1LH---_1RR0LL_1LL0LG_0LL0LG_1LL1LG_0RN1RR_1RN1LL_1RB0LL_1RR1LL_0RB0RR_1RB1RR_1LG1RJ_1RV1RM_0LH0RM_1RJ1RM_0LC0RB_1LC0RR_0RJ---_1RJ---_1RN---_1LL---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_1RD1LC_1RF1RE_0RA0RD_1RG1LC_1RA1RD_1RF---".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_1RD1LC_1RF1RE_0RA0RD_1RG1LC_1RA1RD_1RF1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "BGLRMJNV".
Definition mp' := mp_from_str "BGLRMJNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM186.


Module TM187.
Definition tm := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LD_1RA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LA_1RA---".
Definition tm0 := TM'_from_str "0RF1RN_1RF1LD_1LK0LD_1RN1LD_1LD0RN_1LK1RN_0LL1RR_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RR0RE_1RR1RE_1RV1LD_1LD0RN_0RV1RV_1RV1LD_1RB0LO_---1LO_0RB---_1RB---_1RF---_1LD---".
Definition tm0' := TM'_from_str "0RF1RN_1RF1LD_1LK0LD_1RN1LD_1LD0RN_1LK1RN_0LL1RR_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RR0RE_1RR1RE_1RV1LD_1LD0RN_0RV1RN_1RV1LD_1RB0LD_---1LD_0RB---_1RB---_1RF---_1LD---".
Definition tm1 := TM'_from_str "1RB1LD_1LC1RE_0LD0LC_1RE1LD_1RG1RF_1LD0RE_1RH1LD_1RA---".
Definition tm2 := TM'_from_str "1RB1LD_1LC1RE_0LD0LC_1RE1LD_1RG1RF_1LD0RE_1RH1LD_1RA1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "BFKDNERV".
Definition mp' := mp_from_str "BFKDNERV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM187.


Module TM188.
Definition tm := TM_from_str "1RB1RA_0RC1RF_1RD---_0LE1LE_1RA1LD_1LD0LF".
Definition tm' := TM_from_str "1RB0RD_0RC1RF_1RD---_0LE1LE_1RA1LD_1LD0LF".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1RI1RF_1RV1RB_0RI0RV_1RI1RV_0RN1LT_---0LW_0RN---_1RN---_0LP---_1LP---_1RF1RB_0LP1LP_0LS0LT_1LS1LT_0RB1LS_1RB1LT_1RF0LP_1RB1LP_1LS0LP_1LT0LW_0LP0LW_1LP1LW".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1RI1RF_1RV1RM_0RI0RV_1RI1RV_0RN1LT_---0LW_0RN---_1RN---_0LP---_1LP---_1RF1RM_0LP1LP_0LS0LT_1LS1LT_0RB1LS_1RB1LT_1RF0LP_1RM1LP_1LS0LP_1LT0LW_0LP0LW_1LP1LW".
Definition tm1 := TM'_from_str "0LB1LB_1LC1LD_1RE0LB_1RH1LB_1RI1RF_1LD0LG_0LB0LG_1RE1RH_0RA---".
Definition tm2 := TM'_from_str "0LB1LB_1LC1LD_1RE0LB_1RH1LB_1RI1RF_1LD0LG_0LB0LG_1RE1RH_0RA1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "NPSTFVWBI".
Definition mp' := mp_from_str "NPSTFVWMI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM188.


Module TM189.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD0RA_1RE0RD_1RF0RB_1RA---".
Definition tm' := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_1RF0RB_1RA---".
Definition tm0 := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN0RA_1RN1RA_1RR1LL_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_1RB1RM_---0LH_0RB---_1RB---_1LC---_1LD---".
Definition tm0' := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_1RB1RM_---0LH_0RB---_1RB---_1LC---_1LD---".
Definition tm1 := TM'_from_str "1RB0LH_0RC0RB_1RD1RA_1RE---_1LF1LG_0LH0LG_1LH1LG_1LI1LF_1RB1LH".
Definition tm2 := TM'_from_str "1RB0LH_0RC0RB_1RD1RA_1RE1RJ_1LF1LG_0LH0LG_1LH1LG_1LI1LF_1RB1LH_1RJ1RJ".
Definition l0 := [1;0;0;0;0;0;0;1]%N.
Definition mp := mp_from_str "EMRVBCDHL".
Definition mp' := mp_from_str "EMRVBCDHL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM189.


Module TM190.
Definition tm := TM_from_str "1RB0LF_1RC0RB_1LD0LE_1LE0LC_1LA0RA_1RC---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1LD0LE_1LE0LC_1LA0RA_0LC---".
Definition tm0 := TM'_from_str "0RF1LK_1RF---_1RJ0LW_1RE1LW_0RJ0RE_1RJ1RE_1LK0RJ_0RF0RE_1LT0LD_1LK0RF_0LP0LS_1LP1LS_1LD0LP_1LK0LS_0LT0LK_1LT1LK_1RE0RA_1LW1RA_0LD0RF_1LD1LK_0RJ---_1RJ---_1LK---_0RF---".
Definition tm0' := TM'_from_str "0RF1LK_1RF---_1RJ0LX_1RE1LX_0RJ0RE_1RJ1RE_1LK0RJ_0RF0RE_1LT0LD_1LK0RF_0LP0LS_1LP1LS_1LD0LP_1LK0LS_0LT0LK_1LT1LK_1RE0RA_1LX1RA_0LD0RF_1LD1LK_0LP---_0LS---_0LK---_1LK---".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RG_0LD0LH_1LE1LC_1LF1LC_1RA1LI_1RB1RA_0LF0RG_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RG_0LD0LH_1LE1LC_1LF1LC_1RA1LI_1RB1RA_0LF0RG_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "EJKPTDFSW".
Definition mp' := mp_from_str "EJKPTDFSX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM190.


Module TM191.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1LD0LE_1LE0LC_1LA0RA_0LC---".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1LD0LF_1LF0RA_0LC---_1LA0RA".
Definition tm0 := TM'_from_str "0RF1LK_1RF---_1RJ0LX_1RE1LX_0RJ0RE_1RJ1RE_1LK0RJ_0RF0RE_1LT0LD_1LK0RF_0LP0LS_1LP1LS_1LD0LP_1LK0LS_0LT0LK_1LT1LK_1RE0RA_1LX1RA_0LD0RF_1LD1LK_0LP---_0LS---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF1LK_1RF---_1RJ0LT_1RE1LT_0RJ0RE_1RJ1RE_1LK0RJ_0RF0RE_1LX0LD_1LK0RF_0LP0LW_1LP1LW_1LD0RA_1LK1RA_0LX0RF_1LX1LK_0LP---_0LW---_0LK---_1LK---_1RE0RA_1LT1RA_0LD0RF_1LD1LK".
Definition tm1 := TM'_from_str "0RB0RA_1LC0RG_0LD0LH_1LE1LC_1LF1LC_1RA1LI_1RB1RA_0LF0RG_1LC---".
Definition tm2 := TM'_from_str "0RB0RA_1LC0RG_0LD0LH_1LE1LC_1LF1LC_1RA1LI_1RB1RA_0LF0RG_1LC1RJ_1RJ1RJ".
Definition l0 := [1;0;0;0;0;1;0;1]%N.
Definition mp := mp_from_str "EJKPTDFSX".
Definition mp' := mp_from_str "EJKPXDFWT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM191.


Module TM192.
Definition tm := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_0LF0LB_1RD---".
Definition tm' := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_1LF0LB_0RE---".
Definition tm0 := TM'_from_str "1RI0RQ_1LP1RQ_0LH1RB_1LH1RB_0RJ1LD_1RJ1LT_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RQ0RI_1LH1LW_1RB1LG_0LD0LT_1LD1LT_1RB1RB_---0LP_0LW0LG_1LW1LG_0RN---_1RN---_1RB---_1LG---".
Definition tm0' := TM'_from_str "1RI0RQ_1LP1RQ_0LH1RB_1LH1RB_0RJ1LD_1RJ1LT_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RQ0RI_1LH1LX_1RB1LG_0LD0LT_1LD1LT_1RB1RB_---0LP_0LX0LG_1LX1LG_0RQ---_1RQ---_1RB---_1RB---".
Definition tm1 := TM'_from_str "1LB1RF_1LG1LC_1LE1LD_1RA0LB_1RA---_1RA1RA_1LH1RA_1RI1LB_0RA0RI".
Definition tm2 := TM'_from_str "1LB1RF_1LG1LC_1LE1LD_1RA0LB_1RA1RJ_1RA1RA_1LH1RA_1RI1LB_0RA0RI_1RJ1RJ".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "BPTGWQDHI".
Definition mp' := mp_from_str "BPTGXQDHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM192.


Module TM193.
Definition tm := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_1LF0LB_0RE---".
Definition tm' := TM_from_str "1LB0RE_1RC1LD_1RA0RC_1LA1LE_0LF0LB_1RC---".
Definition tm0 := TM'_from_str "1RI0RQ_1LP1RQ_0LH1RB_1LH1RB_0RJ1LD_1RJ1LT_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RQ0RI_1LH1LX_1RB1LG_0LD0LT_1LD1LT_1RB1RB_---0LP_0LX0LG_1LX1LG_0RQ---_1RQ---_1RB---_1RB---".
Definition tm0' := TM'_from_str "1RI0RQ_1LP1RQ_0LH1RB_1LH1RB_0RJ1LD_1RJ1LT_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RQ0RI_1LH1LW_1RB1LG_0LD0LT_1LD1LT_1RB1RB_---0LP_0LW0LG_1LW1LG_0RJ---_1RJ---_1RB---_1RI---".
Definition tm1 := TM'_from_str "1LB1RF_1LG1LC_1LE1LD_1RA0LB_1RA---_1RA1RA_1LH1RA_1RI1LB_0RA0RI".
Definition tm2 := TM'_from_str "1LB1RF_1LG1LC_1LE1LD_1RA0LB_1RA1RJ_1RA1RA_1LH1RA_1RI1LB_0RA0RI_1RJ1RJ".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "BPTGXQDHI".
Definition mp' := mp_from_str "BPTGWQDHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM193.


Module TM194.
Definition tm := TM_from_str "1LB---_0LC1LA_0RD0LE_1LE1LF_0LF0RF_1RC1LB".
Definition tm' := TM_from_str "1LB---_0LC1LA_0RD0LE_1LE1RC_0LF0RF_1RC1LB".
Definition tm0 := TM'_from_str "1LK---_1LD---_0LH---_1LH---_1LW1LH_0LS---_0LK0LD_1LK1LD_0RM0LW_1RM0RJ_1LW0LS_0RJ1LS_1LW0RJ_1LK1LH_0LT0LX_1LT1LX_1RM0RU_0LH1RU_0LW0RJ_1LW1LK_0RJ1LK_1RJ1LD_1RM0LH_0RJ1LH".
Definition tm0' := TM'_from_str "1LK---_1LD---_0LH---_1LH---_1LW1LH_0LS---_0LK0LD_1LK1LD_0RM0LW_1RM0RJ_1LW0LS_0RJ1LS_1LW0RJ_1LK1RJ_0LT1RM_1LT0RJ_1RM0RU_0LH1RU_0LW0RJ_1LW1LK_0RJ1LK_1RJ1LD_1RM0LH_0RJ1LH".
Definition tm1 := TM'_from_str "1RB0RA_1LC0RA_1RB0LD_1LE1LG_1LC0LF_0LC0RA_1LD---".
Definition tm2 := TM'_from_str "1RB0RA_1LC0RA_1RB0LD_1LE1LG_1LC0LF_0LC0RA_1LD1RH_1RH1RH".
Definition l0 := [1;0;0;1;0;0;1;0]%N.
Definition mp := mp_from_str "JMWHKSD".
Definition mp' := mp_from_str "JMWHKSD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM194.


Module TM195.
Definition tm := TM_from_str "1LB1RD_0LC1LB_1LD1LF_1RE0RD_0LC1LA_0LE---".
Definition tm' := TM_from_str "1LB1RD_0LC0RE_1LD1LF_1RE0RD_0LC1LA_0LE---".
Definition tm0 := TM'_from_str "1LK0RN_1LH1RN_0LH1RR_1LH1RM_0LP1LK_0LX1LH_0LK0LH_1LK1LH_1RM1LS_0RM---_0LP0LX_1LP1LX_0RR0RM_1RR1RM_0LX0RR_1RM0RM_0LP1LH_0LX1RM_0LK0LD_1LK1LD_0LK---_0LD---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1LK0RN_1LH1RN_0LH1RR_1LH1RM_0LP0RQ_0LX1RQ_0LK0LP_1LK1LH_1RM1LS_0RM---_0LP0LX_1LP1LX_0RR0RM_1RR1RM_0LX0RR_1RM0RM_0LP1LH_0LX1RM_0LK0LD_1LK1LD_0LK---_0LD---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0LB1RH_1LC---_0LF0LD_1LE1RH_1LF1LE_0LG0LB_1RH0RH_0RA0RH".
Definition tm2 := TM'_from_str "0LB1RH_1LC1RI_0LF0LD_1LE1RH_1LF1LE_0LG0LB_1RH0RH_0RA0RH_1RI1RI".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "RXSDHKPM".
Definition mp' := mp_from_str "RXSDHKPM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM195.


Module TM196.
Definition tm := TM_from_str "1LB1RD_0LC1LE_1LD1LF_1RE0RD_0LC1LA_0LE---".
Definition tm' := TM_from_str "1LB1RE_0RB1LC_0LD1LA_1LE1LF_1RC0RE_0LC---".
Definition tm0 := TM'_from_str "1LK0RN_1LT1RN_0LH1RR_1LH1RM_0LP1LK_0LX1LD_0LK0LT_1LK1LT_1RM1LS_0RM---_0LP0LX_1LP1LX_0RR0RM_1RR1RM_0LX0RR_1RM0RM_0LP1LH_0LX1RM_0LK0LD_1LK1LD_0LK---_0LD---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1LO0RR_1LL1RR_0LH1RJ_1LH1RQ_0RE1LO_1RE1LD_0RE0LL_1LO1LL_0LT1LH_0LX1RQ_0LO0LD_1LO1LD_1RQ1LK_0RQ---_0LT0LX_1LT1LX_0RJ0RQ_1RJ1RQ_0LX0RJ_1RQ0RQ_0LO---_0LD---_0LK---_1LK---".
Definition tm1 := TM'_from_str "0LB1RH_1LC---_0LF0LD_1LE1RH_1LF1LI_0LG0LB_1RH0RH_0RA0RH_1LF1LD".
Definition tm2 := TM'_from_str "0LB1RH_1LC1RJ_0LF0LD_1LE1RH_1LF1LI_0LG0LB_1RH0RH_0RA0RH_1LF1LD_1RJ1RJ".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "RXSDHKPMT".
Definition mp' := mp_from_str "JXKDHOTQL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM196.


Module TM197.
Definition tm := TM_from_str "1LB1LE_0LC0LA_1RD1LF_0RD1RE_1LA0RE_1LB---".
Definition tm' := TM_from_str "1LB1LE_0LC0LA_1RD0LF_0RD1RE_1LA0RE_0RE---".
Definition tm0 := TM'_from_str "1LK1LD_1LC0RQ_0LH0LT_1LH1LT_1RM0LH_0LX0LT_0LK0LC_1LK1LC_0RN1LH_1RN---_1RM0LX_1RR1LX_0RM0RR_1RM1RR_0RM1LT_0RR1RQ_1LH0RQ_1LT1RQ_0LD1LH_1LD0RQ_1LK---_1LC---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1LK1LD_1LC0RQ_0LH0LT_1LH1LT_1RM0LH_0LW0LT_0LK0LC_1LK1LC_0RN1LH_1RN---_1RM0LW_1RR1LW_0RM0RR_1RM1RR_0RM1LT_0RR1RQ_1LH0RQ_1LT1RQ_0LD1LH_1LD0RQ_0RQ---_1RQ---_1LH---_0RQ---".
Definition tm1 := TM'_from_str "1LB0RA_1LD1LC_0LB0LH_1RF0LE_1LB---_0RF0RG_1LH1RA_1LI0RA_1LB1LH".
Definition tm2 := TM'_from_str "1LB0RA_1LD1LC_0LB0LH_1RF0LE_1LB1RJ_0RF0RG_1LH1RA_1LI0RA_1LB1LH_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "QHCKXMRTD".
Definition mp' := mp_from_str "QHCKWMRTD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM197.


Module TM198.
Definition tm := TM_from_str "1RB0RC_1LC0LB_1RD1LD_1LA0RE_1RF0RE_0RC---".
Definition tm' := TM_from_str "1RB1LA_1LC0LB_1RD1LD_1LA0RE_1RF0RE_0RC---".
Definition tm0 := TM'_from_str "0RF0RI_1RF1RI_1LP0RN_0LG1LD_1RQ0LL_1LP0LG_0LL0LG_1LL1LG_0RN1LD_1RN0RQ_1LD0LP_1RQ1LP_0LG0RQ_1LD1RQ_0LD0RV_1LD0RQ_0RV0RQ_1RV1RQ_1RI0RV_---0RQ_0RI---_1RI---_0RN---_1LD---".
Definition tm0' := TM'_from_str "0RF0LG_1RF1LD_1LP0LD_0LG1LD_1RQ0LL_1LP0LG_0LL0LG_1LL1LG_0RN1LD_1RN0RQ_1LD0LP_1RQ1LP_0LG0RQ_1LD1RQ_0LD0RV_1LD0RQ_0RV0RQ_1RV1RQ_1RI0RV_---0RQ_0RI---_1RI---_0RN---_1LD---".
Definition tm1 := TM'_from_str "1RB---_0RC1LD_1LD1RG_0LE1LD_0LF0LE_1RG1LH_0RA0RG_1LD0RG".
Definition tm2 := TM'_from_str "1RB1RI_0RC1LD_1LD1RG_0LE1LD_0LF0LE_1RG1LH_0RA0RG_1LD0RG_1RI1RI".
Definition l0 := [1;0;1;0;1;0;0;0]%N.
Definition mp := mp_from_str "VINDGLQP".
Definition mp' := mp_from_str "VINDGLQP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM198.


Module TM199.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_0LE---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LO_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RV_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0LO_0LD0LO_0RQ1LO_0RJ0RV_1RJ1RV_1LO1LO_1RM---_0RQ---_1LO---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LO_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RU_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0LO_0LD0LO_0RQ1LO_0RJ0RU_1RJ1RU_1LO1LO_1RM---_1LO---_1LO---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "EDQJOMV".
Definition mp' := mp_from_str "EDQJOMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM199.


Module TM200.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LC---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RU_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RU_1RJ1RU_1LO0LD_1RM---_0LD---_0RE---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RV_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RV_1RJ1RV_1LO0LD_1RM---_1LD---_0LD---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_0LB---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "EDQJOKMU".
Definition mp' := mp_from_str "EDQJOKMV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM200.


Module TM201.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LA---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LE---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RV_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RV_1RJ1RV_1LO1LO_1RM---_1RQ---_1LO---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RU_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RU_1RJ1RU_1LO1LO_1RM---_1LO---_1LO---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_1LE1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "EDQJOKMV".
Definition mp' := mp_from_str "EDQJOKMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM201.


Module TM202.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_0LD---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RU_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RU_1RJ1RU_1LO0LK_1RM---_0LK---_0RJ---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RV_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RV_1RJ1RV_1LO0LK_1RM---_0LD---_0LK---_0LO---_1LO---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_0LF---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_0LF1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "EDQJOKMU".
Definition mp' := mp_from_str "EDQJOKMV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM202.


Module TM203.
Definition tm := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_1LB---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RV_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RV_1RJ1RV_1LO1LK_1RM---_0RQ---_1LK---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LK_0RE0LO_1RQ1LO_0LD0RQ_0RE1RQ_0LK0RJ_1LK0RU_1RQ0RM_1LO1RM_0LD0RE_1LD0LD_0RE0LD_1RE0RE_0LD0LK_0RQ1LK_0RJ0RU_1RJ1RU_1LO1LK_1RM---_1LK---_0RU---_0LH---_1LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_1LF---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB0RA_0RA0LB_1LF1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "EDQJOKMV".
Definition mp' := mp_from_str "EDQJOKMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM203.


Module TM204.
Definition tm := TM_from_str "1LB0RE_1LC0LA_1LD1LF_1RA0LC_1RB1RA_1LC---".
Definition tm' := TM_from_str "1LB0RE_1LC0LA_1LD0LF_1RA0LC_1RB1RA_0RA---".
Definition tm0 := TM'_from_str "1LL0RQ_1LC1RQ_0LH0RF_1LH0RB_1LP0LH_1LX0RF_0LL0LC_1LL1LC_1RQ1LL_1LK---_0LP0LX_1LP1LX_0RB0LP_1RB0LX_1LC0LK_1RQ1LK_0RF0RB_1RF1RB_1LX1LC_0RF1RQ_1LP---_1LX---_0LL---_1LL---".
Definition tm0' := TM'_from_str "1LL0RQ_1LC1RQ_0LH0RF_1LH0RB_1LP0LH_1LW0RF_0LL0LC_1LL1LC_1RQ1LL_1LK---_0LP0LW_1LP1LW_0RB0LP_1RB0LW_1LC0LK_1RQ1LK_0RF0RB_1RF1RB_1LW1LC_0RF1RQ_0RA---_1RA---_1LL---_0RQ---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0RG_1LD1LB_1LE1LH_1RF1LI_0RG0RA_1LH0RG_1LD---_0LE0LH".
Definition tm2 := TM'_from_str "1LB1RF_0LC0RG_1LD1LB_1LE1LH_1RF1LI_0RG0RA_1LH0RG_1LD1RJ_0LE0LH_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "BCHLPQFXK".
Definition mp' := mp_from_str "BCHLPQFWK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM204.


Module TM205.
Definition tm := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_0RC---".
Definition tm' := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_1RE---".
Definition tm0 := TM'_from_str "1LL0RM_1LC1RM_0LH0RR_1LH1RF_1LO0LH_1LG0RR_0LL0LC_1LL1LC_1RF0LL_0LW0LC_0LO0LG_1LO1LG_0RR1RF_1RR---_1RF0LW_1RQ1LW_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_0RI---_1RI---_1RF---_0LL---".
Definition tm0' := TM'_from_str "1LL0RM_1LC1RM_0LH0RR_1LH1RF_1LO0LH_1LG0RR_0LL0LC_1LL1LC_1RF0LL_0LW0LC_0LO0LG_1LO1LG_0RR1RF_1RR---_1RF0LW_1RQ1LW_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_0RR---_1RR---_1RF---_1RQ---".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1RB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "RFGCHLOQW".
Definition mp' := mp_from_str "RFGCHLOQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM205.


Module TM206.
Definition tm := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_1RE---".
Definition tm' := TM_from_str "1LB0RF_1LC0LA_0LD0LB_1RE0LF_1RB0RE_1RE---".
Definition tm0 := TM'_from_str "1LL0RM_1LC1RM_0LH0RR_1LH1RF_1LO0LH_1LG0RR_0LL0LC_1LL1LC_1RF0LL_0LW0LC_0LO0LG_1LO1LG_0RR1RF_1RR---_1RF0LW_1RQ1LW_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_0RR---_1RR---_1RF---_1RQ---".
Definition tm0' := TM'_from_str "1LL0RU_1LC1RU_0LH0RR_1LH---_1LO0LH_1LG0RR_0LL0LC_1LL1LC_1RF0LL_0LW0LC_0LO0LG_1LO1LG_0RR1RF_1RR---_1RF0LW_1RQ1LW_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_0RR---_1RR---_1RF---_1RQ---".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1RB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "RFGCHLOQW".
Definition mp' := mp_from_str "RFGCHLOQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM206.


Module TM207.
Definition tm := TM_from_str "1LB---_1LC0LF_0LD0LB_1RE1LA_1RB0RE_1LB0RD".
Definition tm' := TM_from_str "1LB0RF_1LC0LA_0LD0LB_1RE1LA_1RB0RE_1RE---".
Definition tm0 := TM'_from_str "1LL---_1LW---_0LH---_1LH---_1LO0LH_1LG0RR_0LL0LW_1LL1LW_1RF0LL_0LD0LW_0LO0LG_1LO1LG_0RR1LH_1RR---_1RF0LD_1RQ1LD_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_1LL0RM_1LW1RM_0LH0RR_1LH1LH".
Definition tm0' := TM'_from_str "1LL0RU_1LC1RU_0LH0RR_1LH---_1LO0LH_1LG0RR_0LL0LC_1LL1LC_1RF0LL_0LD0LC_0LO0LG_1LO1LG_0RR1LH_1RR---_1RF0LD_1RQ1LD_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_0RR---_1RR---_1RF---_1RQ---".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1LE---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1LE1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "RFGWHLOQD".
Definition mp' := mp_from_str "RFGCHLOQD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM207.


Module TM208.
Definition tm := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE1LF_1RB0RE_0LD---".
Definition tm' := TM_from_str "1LB0RD_1LC0LA_0RD0LB_1RF1LE_0LD---_1RB0RF".
Definition tm0 := TM'_from_str "1LL0RM_1LC1RM_0LH0RR_1LH1LO_1LO0LH_1LG0RR_0LL0LC_1LL1LC_1RF0LL_0LX0LC_0LO0LG_1LO1LG_0RR1LO_1RR---_1RF0LX_1RQ1LX_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_1RF---_0LX---_0LO---_1LO---".
Definition tm0' := TM'_from_str "1LL0RM_1LC1RM_0LH0RV_1LH1LO_1LO0LH_1LG0RV_0LL0LC_1LL1LC_0RM0LL_1RM0LC_0RV0LG_1LO1LG_0RV1LO_1RV---_1RF0LT_1RU1LT_1RF---_0LT---_0LO---_1LO---_0RF0RU_1RF1RU_1LG0RF_0RV0RU".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1LG---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1LG1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "RFGCHLOQX".
Definition mp' := mp_from_str "VFGCHLOUT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM208.


Module TM209.
Definition tm := TM_from_str "1LB0RD_1LC0LA_0RD0LB_1RF1LE_0LD---_1RB0RF".
Definition tm' := TM_from_str "1LB0RD_1LC0LA_0LD0LB_1RE0LF_1RB0RE_0RB---".
Definition tm0 := TM'_from_str "1LL0RM_1LC1RM_0LH0RV_1LH1LO_1LO0LH_1LG0RV_0LL0LC_1LL1LC_0RM0LL_1RM0LC_0RV0LG_1LO1LG_0RV1LO_1RV---_1RF0LT_1RU1LT_1RF---_0LT---_0LO---_1LO---_0RF0RU_1RF1RU_1LG0RF_0RV0RU".
Definition tm0' := TM'_from_str "1LL0RM_1LC1RM_0LH0RR_1LH1LO_1LO0LH_1LG0RR_0LL0LC_1LL1LC_1RF0LL_0LW0LC_0LO0LG_1LO1LG_0RR1LO_1RR---_1RF0LW_1RQ1LW_0RF0RQ_1RF1RQ_1LG0RF_0RR0RQ_0RE---_1RE---_1LO---_0LH---".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1LG---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LF0LD_0LE0RA_1LF1LD_1LG1LC_1RB0LI_0RB0RH_1LG1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "VFGCHLOUT".
Definition mp' := mp_from_str "RFGCHLOQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM209.


Module TM210.
Definition tm := TM_from_str "1LB---_0RC0LE_1LE1RD_0RE0RA_0LF0RB_1RB0LB".
Definition tm' := TM_from_str "1RB---_0RC0RA_0LD0RE_1RE0LE_0RF0LC_1LC1RB".
Definition tm0 := TM'_from_str "0RN---_1LS---_0LH---_1LH---_0RI0LW_1RI0RI_1LW0LS_0RN1LS_1LW0RN_0LW1RN_0LT1RQ_1LT1RA_0RQ0RA_1RQ1RA_1RI0RN_0RE---_1RI0RE_0LG1RE_0LW0RI_1LW0LW_0RF1LW_1RF0LS_1RI0LG_0RI1LG".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RI---_1RA---_0RI0RA_1RI1RA_1RU0RF_0RQ---_1RU0RQ_0LS1RQ_0LO0RU_1LO0LO_0RR1LO_1RR0LK_1RU0LS_0RU1LS_0RU0LO_1RU0RU_1LO0LK_0RF1LK_1LO0RF_0LO1RF_0LL1RI_1LL1RA".
Definition tm1 := TM'_from_str "1RB1RH_1RC0RG_1LD0RA_1RC0LE_1LD0LF_0LD0RC_0RC0LD_0RA---".
Definition tm2 := TM'_from_str "1RB1RH_1RC0RG_1LD0RA_1RC0LE_1LD0LF_0LD0RC_0RC0LD_0RA1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "NQIWGSEA".
Definition mp' := mp_from_str "FIUOSKQA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM210.


Module TM211.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0RF_0RA0LA_0RB1RC_0LA---".
Definition tm' := TM_from_str "1LB---_0LC0RD_1RD1RA_0RE0LE_1LB1RF_0RB1RC".
Definition tm0 := TM'_from_str "1LK0RR_0LH1RR_0LH1RE_1LH1RJ_1RA0RM_0LH1RM_0LK0RA_1LK0LH_0RN0RU_1RN1RU_1RA0LH_1RE---_0RA0LH_1RA1RE_1LK0LC_0RR1LC_0RE0RJ_1RE1RJ_1RA1RN_0RM1RU_0LH---_1RE---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1LK---_0LH---_0LH---_1LH---_1RQ0RM_0LH1RM_0LK0RQ_1LK0LH_0RN0RB_1RN1RB_1RQ0LH_1RE---_0RQ0LH_1RQ1RE_1LK0LS_0RV1LS_1LK0RV_0LH1RV_0LH1RE_1LH1RJ_0RE0RJ_1RE1RJ_1RQ1RN_0RM1RB".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RE_1RB0LD_1LC0LD_1RF1RH_1RB0RG_0RB0LD_1RA1RI_0LD---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RE_1RB0LD_1LC0LD_1RF1RH_1RB0RG_0RB0LD_1RA1RI_0LD1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "NAKHREMJU".
Definition mp' := mp_from_str "NQKHVEMJB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM211.


Module TM212.
Definition tm := TM_from_str "1RB0RF_1LC0LF_1LD0LC_1LE0LA_1LF---_1RA1RF".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LF---_1RA1RF".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LK0RB_1RB0RV_1LP1RF_1LK1RB_0LL0LW_1LL1LW_1LT0LP_1LC0LK_0LP0LK_1LP1LK_1LX1LK_---0RB_0LT0LC_1LT1LC_1RU---_1RV---_0LX---_1LX---_0RB0RV_1RB1RV_1RF1RB_1RU1RV".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LK0RB_1RB0RV_1LP0RB_1LK1RB_0LL1RF_1LL1RU_1LT0LP_1LC0LK_0LP0LK_1LP1LK_1LX1LK_---0RB_0LT0LC_1LT1LC_1RU---_1RV---_0LX---_1LX---_0RB0RV_1RB1RV_1RF1RB_1RU1RV".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RA_0LD0LC_1LF1LE_1LC0RA_1LG---_1RH1RI_0RA0RI_1RA1RI".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RA_0LD0LC_1LF1LE_1LC0RA_1LG1RJ_1RH1RI_0RA0RI_1RA1RI_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BFKPCTXUV".
Definition mp' := mp_from_str "BFKPCTXUV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM212.


Module TM213.
Definition tm := TM_from_str "1RB1RF_1LC1LF_---1LD_1LE0RA_1LF1LB_1RD0LD".
Definition tm' := TM_from_str "1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LP1RN_1LO0RF_---1RA_1LP1LO_0LL0LX_1LL1LX_---1LT_---0RV_---0LP_---1LP_1LX0RA_1LH1RA_0LT0RF_1LT0RV_1RA1LL_1LO1LX_0LX0LH_1LX1LH_0RN0LT_1RN0RF_1LH0LO_1RA1LO".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LP1RN_1LO0RF_---1RA_1LP1LO_0LL0LX_1LL1LX_---1LT_---0RV_---0LP_---1LP_1LX0RA_1LH1RA_0LT0RF_1LT0RV_0RR1LL_1RR1LX_1RR0LH_1LX1LH_0RN0LT_1RN0RF_1LH0LO_1RA1LO".
Definition tm1 := TM'_from_str "1LB1LH_1LC0RG_1LE1LD_1LI1LE_1RF1LH_0RA0RG_1RJ0RA_0LC0RA_---1LB_1LD1RF".
Definition tm2 := TM'_from_str "1LB1LH_1LC0RG_1LE1LD_1LI1LE_1RF1LH_0RA0RG_1RJ0RA_0LC0RA_1RK1LB_1LD1RF_1RK1RK".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "FPTHXAVOLN".
Definition mp' := mp_from_str "FPTHXAVOLN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM213.


Module TM214.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA0RF_0LA---".
Definition tm' := TM_from_str "1RB0LE_0RC---_1RD0RC_1LE0RF_0RC0LF_0LA1RB".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RI1LS_0RN0RI_1RN1RI_1LS0RN_1RQ0RI_0RI0RQ_1LS1RQ_0LH1RI_1LH0RU_1RI0RU_0LG1RU_0LC1RI_1LC---_1RI---_0LG---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LW_1RI0LS_---1LS_0RI---_1RI---_0RN---_0RI---_0RN0RI_1RN1RI_1LW0RN_1RU0RI_0RI0RU_1LW1RU_0LT1RI_1LT0RF_0RI0LC_1RI1RI_0RN0LW_0RI1LW_1RI0RF_0LS1RF_0LC1RI_1LC---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RG_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RG_1RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INSCGQU".
Definition mp' := mp_from_str "INWCSUF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM214.


Module TM215.
Definition tm := TM_from_str "1RB0LE_0RC---_1RD0RC_1LE0RF_0RC0LF_0LA1RB".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0RC---".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LW_1RI0LS_---1LS_0RI---_1RI---_0RN---_0RI---_0RN0RI_1RN1RI_1LW0RN_1RU0RI_0RI0RU_1LW1RU_0LT1RI_1LT0RF_0RI0LC_1RI1RI_0RN0LW_0RI1LW_1RI0RF_0LS1RF_0LC1RI_1LC---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RI1LS_0RN0RI_1RN1RI_1LS0RN_1RQ0RI_0RI0RQ_1LS1RQ_0LH1RI_1LH0RV_1RI0RV_0LG1RV_0LC1RI_1LC---_0RI---_1RI---_0RN---_0RI---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RG_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RG_1RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INWCSUF".
Definition mp' := mp_from_str "INSCGQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM215.


Module TM216.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0RC---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0LD---".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RI1LS_0RN0RI_1RN1RI_1LS0RN_1RQ0RI_0RI0RQ_1LS1RQ_0LH1RI_1LH0RV_1RI0RV_0LG1RV_0LC1RI_1LC---_0RI---_1RI---_0RN---_0RI---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RI1LS_0RN0RI_1RN1RI_1LS0RN_1RQ0RI_0RI0RQ_1LS1RQ_0LH1RI_1LH0RV_1RI0RV_0LG1RV_0LC1RI_1LC---_0LH---_1RI---_0LO---_1LO---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RG_1RA---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RG_1RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INSCGQV".
Definition mp' := mp_from_str "INSCGQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM216.


Module TM217.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RD---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_0LB---".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RF---_0RU0RF_1LS1RF_0LH1RI_1LH1RI_1RI0RQ_0LG1RQ_0LC1RI_1LC0RQ_0RN---_1RN---_1LS---_1RF---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RF---_0RU0RF_1LS1RF_0LH1RI_1LH1RI_1RI0RF_0LG1RF_0LC1RI_1LC1RI_0RN---_0LS---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA1RA_0RB---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA1RA_0RB1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INSCGFU".
Definition mp' := mp_from_str "INSCGFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM217.


Module TM218.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_0LB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_0LB---".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RF---_0RU0RF_1LS1RF_0LH1RI_1LH1RI_1RI0RF_0LG1RF_0LC1RI_1LC1RI_0RN---_0LS---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RF---_0RU0RF_1LS1RF_0LH1RI_1LH1RI_1RI0RQ_0LG1RQ_0LC1RI_1LC0RQ_0RN---_0LS---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA1RA_0RB---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA1RA_0RB1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INSCGFU".
Definition mp' := mp_from_str "INSCGFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM218.


Module TM219.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_0LB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RD---".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RF---_0RU0RF_1LS1RF_0LH1RI_1LH1RI_1RI0RQ_0LG1RQ_0LC1RI_1LC0RQ_0RN---_0LS---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RF---_0RU0RF_1LS1RF_0LH1RI_1LH1RI_1RI0RF_0LG1RF_0LC1RI_1LC1RI_0RN---_1RN---_1LS---_1RF---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA1RA_0RB---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA1RA_0RB1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INSCGFU".
Definition mp' := mp_from_str "INSCGFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM219.


Module TM220.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA0RE_1RD---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA0RE_0LB---".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RQ---_0RU0RQ_1LS1RQ_0LH1RI_1LH0RQ_1RI0RQ_0LG1RQ_0LC1RI_1LC0RQ_0RN---_1RN---_1LS---_1RQ---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RQ---_0RU0RQ_1LS1RQ_0LH1RI_1LH0RQ_1RI0RQ_0LG1RQ_0LC1RI_1LC0RQ_0RN---_0LS---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RF_0RB---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RF_0RB1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INSCGQU".
Definition mp' := mp_from_str "INSCGQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM220.


Module TM221.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA1RB_1RD---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA1RB_0LB---".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RQ---_0RU0RQ_1LS1RQ_0LH1RI_1LH0RF_1RI0RF_0LG1RF_0LC1RI_1LC1RI_0RN---_1RN---_1LS---_1RQ---".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LS_1RI0LG_1RI1LG_0RI0LC_1RI1RI_0RN0LS_0RU1LS_0RN0RU_1RN1RU_1LS0RN_1RQ---_0RU0RQ_1LS1RQ_0LH1RI_1LH0RF_1RI0RF_0LG1RF_0LC1RI_1LC1RI_0RN---_0LS---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RH_0RB---_1RA1RA".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RF_0LD1RA_1RA0LE_0RB0LC_1RA0RH_0RB1RI_1RA1RA_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "INSCGQUF".
Definition mp' := mp_from_str "INSCGQUF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM221.


Module TM222.
Definition tm := TM_from_str "1LB0RC_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---0RC".
Definition tm' := TM_from_str "1LB0RC_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm0 := TM'_from_str "1LL0RI_1RI1RI_0LH1RA_1LH1RE_1LO0RV_1LP1RV_0LL---_1LL1RI_1RA1RE_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RE1LS_0RA0RE_1RA1RE_1LL1LO_0RI0RV_---0RI_---1RI_---1RA_---1RE".
Definition tm0' := TM'_from_str "1LL0RI_---1RI_0LH1RA_1LH1RU_1LO---_1LP---_0LL---_1LL---_1RA1RU_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RU1LS_0RA0RU_1RA1RU_1LL1LO_0RI0RB_1LO0RB_1LP1RB_0LL---_1LL1RI".
Definition tm1 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_---1RF".
Definition tm2 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_1RI1RF_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ALPSOIEV".
Definition mp' := mp_from_str "ALPSOIUB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM222.


Module TM223.
Definition tm := TM_from_str "1LB0RC_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm' := TM_from_str "1LB1RE_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm0 := TM'_from_str "1LL0RI_---1RI_0LH1RA_1LH1RU_1LO---_1LP---_0LL---_1LL---_1RA1RU_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RU1LS_0RA0RU_1RA1RU_1LL1LO_0RI0RB_1LO0RB_1LP1RB_0LL---_1LL1RI".
Definition tm0' := TM'_from_str "1LL0RR_---1RR_0LH1RA_1LH1RU_1LO---_1LP---_0LL---_1LL---_1RA1RU_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RU1LS_0RA0RU_1RA1RU_1LL1LO_0RR0RB_1LO0RB_1LP1RB_0LL---_1LL1RR".
Definition tm1 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_---1RF".
Definition tm2 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_1RI1RF_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ALPSOIUB".
Definition mp' := mp_from_str "ALPSORUB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM223.


Module TM224.
Definition tm := TM_from_str "1LB1RE_1LC---_0LD1LD_1RE0LE_0RA0RF_1LC1RA".
Definition tm' := TM_from_str "1LB1RE_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE".
Definition tm0 := TM'_from_str "1LL0RR_---1RR_0LH1RA_1LH1RU_1LO---_1LP---_0LL---_1LL---_1RA1RU_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RU1LS_0RA0RU_1RA1RU_1LL1LO_0RR0RB_1LO0RB_1LP1RB_0LL---_1LL1RR".
Definition tm0' := TM'_from_str "1LL0RR_1RR1RR_0LH1RA_1LH1RE_1LO0RV_1LP1RV_0LL---_1LL1RR_1RA1RE_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RE1LS_0RA0RE_1RA1RE_1LL1LO_0RR0RV_---0RR_---1RR_---1RA_---1RE".
Definition tm1 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_---1RF".
Definition tm2 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_1RI1RF_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ALPSORUB".
Definition mp' := mp_from_str "ALPSOREV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM224.


Module TM225.
Definition tm := TM_from_str "1LB1RE_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---0RC".
Definition tm' := TM_from_str "1LB0RC_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE".
Definition tm0 := TM'_from_str "1LL0RR_1RI1RR_0LH1RA_1LH1RE_1LO0RV_1LP1RV_0LL---_1LL1RI_1RA1RE_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RE1LS_0RA0RE_1RA1RE_1LL1LO_0RR0RV_---0RI_---1RI_---1RA_---1RE".
Definition tm0' := TM'_from_str "1LL0RI_1RR1RI_0LH1RA_1LH1RE_1LO0RV_1LP1RV_0LL---_1LL1RR_1RA1RE_0LS1LS_0LO0LP_1LO1LP_0RR1LL_1RR1LO_1RA0LS_1RE1LS_0RA0RE_1RA1RE_1LL1LO_0RI0RV_---0RR_---1RR_---1RA_---1RE".
Definition tm1 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_---1RI_1RA1RG".
Definition tm2 := TM'_from_str "1LB0RF_1LE1LC_1RG1LD_1LB1LE_1RA0LD_1RA1RG_1LE0RH_1RJ1RI_1RA1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ALPSOREVI".
Definition mp' := mp_from_str "ALPSOIEVR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM225.


Module TM226.
Definition tm := TM_from_str "1RB0RA_0RC0LB_1LD0RF_1LE1RA_1RD1RB_0RA---".
Definition tm' := TM_from_str "1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RI0RF_0LG0RA_0RI1LT_1RI0LG_1LT0LG_0RU1LG_1LT0RU_1RA1RU_0LP0RA_1LP---_1RB0RB_0LG1RB_0LT1RF_1LT1RA_0RN0RF_1RN1RF_0LG1RI_1RB0LG_0RA---_1RA---_0RF---_0RA---".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RI0RF_0LG0RA_0RI1LT_1RI0LG_1LT0LG_0RV1LG_1LT0RV_1RA1RV_0LP0RA_1LP---_1RB0RB_0LG1RB_0LT1RF_1LT1RA_0RN0RF_1RN1RF_0LG1RI_1RB0LG_0LG---_0RA---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1LB0RG_1RD0LC_1LB0LC_1RF1RE_0RF0RE_1RA0LC_0RE---".
Definition tm2 := TM'_from_str "1LB0RG_1RD0LC_1LB0LC_1RF1RE_0RF0RE_1RA0LC_0RE1RH_1RH1RH".
Definition l0 := [1;1;0;1;0;0;0;1]%N.
Definition mp := mp_from_str "ITGBAFU".
Definition mp' := mp_from_str "ITGBAFV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM226.


Module TM227.
Definition tm := TM_from_str "1RB1RC_1LC1RF_0RA0LD_1LE0RD_1RA0LB_0RC---".
Definition tm' := TM_from_str "1RB1RC_1LC1RF_0RA0LD_1LE1RE_1RC0LB_0RC---".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_1LO1RA_1RV1RJ_0RJ0RV_1LO1RV_0LL1RI_1LL---_0RA0LT_1RA1RJ_0RF0LO_0RJ1LO_1RJ0RM_1LG1RM_0LT1RJ_1LT0RM_0RB0LL_1RB1RI_1RF0LG_1RJ1LG_0RI---_1RI---_0RA---_0LT---".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1LO1RA_1RV1RJ_0RJ0RV_1LO1RV_0LL1RI_1LL---_0RA0LT_1RA1RJ_0RF0LO_0RJ1LO_1RJ0RR_1LG1RR_0LT1RJ_1LT1RI_0RJ0LL_1RJ1RI_1RA0LG_1RJ1LG_0RI---_1RI---_0RA---_0LT---".
Definition tm1 := TM'_from_str "1LB1RI_0LC1RG_1RG1LD_0LE1RF_0RG1LB_0RH0LC_1RH1RG_0RA0RG_1RF---".
Definition tm2 := TM'_from_str "1LB1RI_0LC1RG_1RG1LD_0LE1RF_0RG1LB_0RH0LC_1RH1RG_0RA0RG_1RF1RJ_1RJ1RJ".
Definition l0 := [1;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "FOTGLIJAV".
Definition mp' := mp_from_str "FOTGLIJAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM227.


Module TM228.
Definition tm := TM_from_str "1RB0RF_0LC1RF_0LD1LC_0RE0LA_0LF---_1RA1RD".
Definition tm' := TM_from_str "1RB0RF_0LC1RF_0LD1LC_1RE0LA_1RB---_1RA1RD".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_0LL0RB_1RV0RN_0LO0RV_0LL1RV_0LK1RB_1LK1RN_1RF1LO_0LC1LL_0LO0LL_1LO1LL_0RQ0LL_1RQ0RB_1RF0LC_---1LC_1RF---_1RQ---_0LW---_1LW---_0RB0RN_1RB1RN_1RF1RQ_1RU0RB".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_0LL0RB_1RV0RN_0LO0RV_0LL1RV_0LK1RB_1LK1RN_1RF1LO_0LC1LL_0LO0LL_1LO1LL_0RR0LL_1RR0RB_1RF0LC_---1LC_0RF---_1RF---_0LL---_1RV---_0RB0RN_1RB1RN_1RF1RR_1RU0RB".
Definition tm1 := TM'_from_str "0LB1RE_1LC1LB_1RA0LD_0LB0RG_1RG1RF_1RI0RG_1RA1RH_0RG0RF_1RA---".
Definition tm2 := TM'_from_str "0LB1RE_1LC1LB_1RA0LD_0LB0RG_1RG1RF_1RI0RG_1RA1RH_0RG0RF_1RA1RJ_1RJ1RJ".
Definition l0 := [1;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "FLOCVNBUQ".
Definition mp' := mp_from_str "FLOCVNBUR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM228.


Module TM229.
Definition tm := TM_from_str "1RB0RF_1LC1RA_0LE0LD_0LB1LC_1RA0RA_0RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_0LE0LD_0LB0RD_1RA0RA_0RE---".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LO0RQ_1RB---_1LS0RB_1LO1RB_0LL1RF_1LL1RU_1RF0LG_0RF0LL_0LS0LO_1LS1LO_0LL1LS_1RF1LO_0LG0LL_1LG1LL_0RB0RA_1RB1RA_1RF0RF_1RU0RU_0RQ---_1RQ---_0RB---_0RA---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO0RQ_1RB---_1LS0RB_1LO1RB_0LL1RF_1LL1RU_1RF0LG_0RF0LL_0LS0LO_1LS1LO_0LL0RM_1RF1RM_0LG0LL_1LG0RM_0RB0RA_1RB1RA_1RF0RF_1RU0RU_0RQ---_1RQ---_0RB---_0RA---".
Definition tm1 := TM'_from_str "0RB0RI_1RC1RH_1LD1RB_0LG0LE_1LF1LD_1RC0RC_0LE1RC_0RA---_0RC0RH".
Definition tm2 := TM'_from_str "0RB0RI_1RC1RH_1LD1RB_0LG0LE_1LF1LD_1RC0RC_0LE1RC_0RA1RJ_0RC0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "QBFOLSGUA".
Definition mp' := mp_from_str "QBFOLSGUA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 21 21.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM229.


Module TM230.
Definition tm := TM_from_str "1RB---_1LB0LC_0LD0RA_0LE1RA_0RF0LC_1RE1RC".
Definition tm' := TM_from_str "1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LK---_0RF---_1LH0LO_1LK0RF_0LH0LK_1LH1LK_0LS0RA_1RF1RA_0LO0RF_1LO---_0RR0RB_0LK1RB_0LS1RF_1LS---_0RU0LO_1RU0RF_0RR0LK_0RJ1LK_0RR0RJ_1RR1RJ_1RU1RF_0RF1RA".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LO---_0RF---_0RN0LS_1LO0RF_0LL0LO_1LL1LO_0RU0LS_1RU0RF_0RJ0LO_0RN1LO_0LK0RA_1RF1RA_0LS0RF_1LS---_0RJ0RB_0LO1RB_0LK1RF_1LK---_0RJ0RN_1RJ1RN_1RU1RF_0RF1RA".
Definition tm1 := TM'_from_str "1LB0RA_0LC0RA_0LD1RA_0RE0LB_1RF0RA_0RE0RG_1RA1RH_0RA---".
Definition tm2 := TM'_from_str "1LB0RA_0LC0RA_0LD1RA_0RE0LB_1RF0RA_0RE0RG_1RA1RH_0RA1RI_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "FKOSRUJA".
Definition mp' := mp_from_str "FOSKJUNA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM230.


Module TM231.
Definition tm := TM_from_str "1LB1RA_1LC0RE_1LD1RF_0RA0LD_1RC0RE_---1LD".
Definition tm' := TM_from_str "1LB1RA_1LC0RE_1LD0RF_0RA0LD_1RC0RE_---0LE".
Definition tm0 := TM'_from_str "1LL0RB_0RQ1RB_0LH0RQ_1LH1RB_1LP0RQ_1LO1RQ_0LL0RJ_1LL0RQ_0RB0RV_1LO1RV_0LP---_1LP1LO_0RA1LL_1RA0LO_1LL0LO_0RB1LO_0RJ0RQ_1RJ1RQ_1LO0RJ_1RV0RQ_---0RB_---1LO_---0LP_---1LP".
Definition tm0' := TM'_from_str "1LL0RB_0RQ1RB_0LH0RQ_1LH1RB_1LP0RQ_1LO1RQ_0LL0RJ_1LL0RQ_0RB0RU_1LO1RU_0LP---_1LP1LO_0RA1LL_1RA0LO_1LL0LO_0RB1LO_0RJ0RQ_1RJ1RQ_1LO0RJ_1RU0RQ_---1LO_---0RJ_---0LS_---1LS".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RG_1LD0LC_1LE1LC_0RF1LC_0RA1RF_---1LC".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RG_1LD0LC_1LE1LC_0RF1LC_0RA1RF_1RH1LC_1RH1RH".
Definition l0 := [0;1;1;0;0;0;0;0]%N.
Definition mp := mp_from_str "QJOLPBV".
Definition mp' := mp_from_str "QJOLPBU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM231.


Module TM232.
Definition tm := TM_from_str "1LB1LA_1RC0LF_0RD0RC_1LE0RE_0LB1LE_0LA---".
Definition tm' := TM_from_str "1LB1LA_1RC0LF_0RD0RC_1LE0RE_0LB0LC_0LA---".
Definition tm0 := TM'_from_str "1RI1LH_1LW1LD_0LH0LD_1LH1LD_0RJ0LC_1RJ---_1RM0LW_1RI1LW_0RM0RI_1RM1RI_1LG0RM_0RQ0RI_1LG0RQ_1LT1RQ_0LT1RM_1LT1LG_1RM1LG_0LW1LT_0LG0LT_1LG1LT_0LH---_0LD---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1RI1LH_1LW1LD_0LH0LD_1LH1LD_0RJ0LC_1RJ---_1RM0LW_1RI1LW_0RM0RI_1RM1RI_1LG0RM_0RQ0RI_1LG0RQ_1LK1RQ_0LT1RM_1LT1LG_1RM1LG_0LW0RM_0LG0LK_1LG1LK_0LH---_0LD---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB0RH_1RA0LC_0LD---_0LF0LE_1LF1LE_1RG1LC_0RA0RG_1RA1LB".
Definition tm2 := TM'_from_str "1LB0RH_1RA0LC_0LD1RI_0LF0LE_1LF1LE_1RG1LC_0RA0RG_1RA1LB_1RI1RI".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "MGWCDHIQ".
Definition mp' := mp_from_str "MGWCDHIQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM232.


Module TM233.
Definition tm := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_0RB---".
Definition tm' := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_0RD---".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RI0RA_1LT0RI_1LO1RI_0LL1RA_1LL0LL_1RA0LL_1LL0LW_0LT0LO_1LT1LO_1LT1LT_1LO---_0LL0LW_1LL1LW_0RB1LT_1RB1LO_1RF0LL_1RA1LL_0RE---_1RE---_1LT---_0RI---".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RI0RA_1LT0RI_1LO1RI_0LL1RA_1LL0LL_1RA0LL_1LL0LW_0LT0LO_1LT1LO_1LT1LT_1LO---_0LL0LW_1LL1LW_0RB1LT_1RB1LO_1RF0LL_1RA1LL_0RM---_1RM---_1LT---_1LT---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LG_1LD1LB_1RE1LC_0RA0RE_1RE0LC_1LD---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LG_1LD1LB_1RE1LC_0RA0RE_1RE0LC_1LD1RH_1RH1RH".
Definition l0 := [1;1;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "FOLTAIW".
Definition mp' := mp_from_str "FOLTAIW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM233.


Module TM234.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LB---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0RB---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RR0RN_0RV1RF_1RV1LD_1RE0LO_---1LO_1LL---_1RE---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LK1RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RR0RN_0RV1RF_1RV1LD_1RE0LO_---1LO_0RE---_1RE---_1LD---_0RN---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_1RH1LD_1RF---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_1RH1LD_1RF1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFKDNERV".
Definition mp' := mp_from_str "BFKDNERV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM234.


Module TM235.
Definition tm := TM_from_str "1LB0LA_1RC0RD_1RD0RB_1RE0LE_1LA0RF_1LB---".
Definition tm' := TM_from_str "1LB0LA_1RC0RF_1RF0LD_1LA1RE_0RB---_1RD0LD".
Definition tm0 := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RM_1RJ1RM_1RN0RR_1RE0LD_0RN0RE_1RN1RE_1RR0RJ_1RE0RM_0RR0LD_1RR1RE_1LC0LS_1RU1LS_1LH0RU_1LC1RU_0LD1RE_1LD---_1RE---_0LD---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RU_1RJ1RU_1RV0RN_1RE0LD_0RV0LD_1RV1RE_1RN0LO_1RE1LO_1LH0RR_1LC1RR_0LD1RE_1LD---_0RE---_1RE---_0RJ---_0RU---_0RN0LD_1RN1RE_1LC0LO_1RR1LO".
Definition tm1 := TM'_from_str "1RB1RG_1RC1RG_1LD1RI_0LE0LD_1RG0LF_1LE1LD_0RA0RH_0RC0LF_1RG---".
Definition tm2 := TM'_from_str "1RB1RG_1RC1RG_1LD1RI_0LE0LD_1RG0LF_1LE1LD_0RA0RH_0RC0LF_1RG1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "JNRCHDEMU".
Definition mp' := mp_from_str "JVNCHDEUR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM235.


Module TM236.
Definition tm := TM_from_str "1LB0LA_1RC0RF_1RF0LD_1LA1RE_0RB---_1RD0LD".
Definition tm' := TM_from_str "1LB0LA_1RC0RD_1RD0RB_1RE0LE_1LA1RF_0RB---".
Definition tm0 := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RU_1RJ1RU_1RV0RN_1RE0LD_0RV0LD_1RV1RE_1RN0LO_1RE1LO_1LH0RR_1LC1RR_0LD1RE_1LD---_0RE---_1RE---_0RJ---_0RU---_0RN0LD_1RN1RE_1LC0LO_1RR1LO".
Definition tm0' := TM'_from_str "1RE0LH_0LD0LC_0LH0LC_1LH1LC_0RJ0RM_1RJ1RM_1RN0RR_1RE0LD_0RN0RE_1RN1RE_1RR0RJ_1RE0RM_0RR0LD_1RR1RE_1LC0LS_1RV1LS_1LH0RV_1LC1RV_0LD1RE_1LD---_0RE---_1RE---_0RJ---_0RM---".
Definition tm1 := TM'_from_str "1RB1RG_1RC1RG_1LD1RI_0LE0LD_1RG0LF_1LE1LD_0RA0RH_0RC0LF_1RG---".
Definition tm2 := TM'_from_str "1RB1RG_1RC1RG_1LD1RI_0LE0LD_1RG0LF_1LE1LD_0RA0RH_0RC0LF_1RG1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "JVNCHDEUR".
Definition mp' := mp_from_str "JNRCHDEMV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM236.


Module TM237.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LF0RE_0RD1RB_---1LB".
Definition tm' := TM_from_str "1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RN1LL_1RN0RN_1LL1RN_0LD1LH_1LD1RQ_1RN1LL_1LL0LL_0LD0LC_1LD1LC_---0RQ_1LH1RQ_0LX0RM_1LX0RF_0RM0RF_1RM1RF_---1LL_0RQ1RN_---1LD_---1RQ_---0LH_---1LH".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LC_1LL0LL_1RR1LL_1RR0RR_1LL1RR_0LD1LH_1LD1RU_0RM1LL_1RM0LL_---0LC_1LD1LC_---1LD_---1RU_---0LH_---1LH_---0RU_1LH1RU_0LP0RQ_1LP0RF_0RQ0RF_1RQ1RF_---1LL_0RU1RR".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_1LH1RF_0RG0RA_---0RF_1LC1RF".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LD_1RE1LB_1LB0LB_1LH1RF_0RG0RA_1RI0RF_1LC1RF_1RI1RI".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "FLDCNQMH".
Definition mp' := mp_from_str "FLDCRUQH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM237.


Module TM238.
Definition tm := TM_from_str "1LB0LC_0RC1RD_1LA1LD_1RB0RE_1RF1RC_---1RB".
Definition tm' := TM_from_str "1LB0LC_0RC1RD_1LA1LD_1RB0RE_1RF1RC_---0LB".
Definition tm0 := TM'_from_str "1RN0LD_1RQ0LP_0LH0LK_1LH1LK_0RI0RN_1RI1RN_1LH1RF_1RN1RQ_1LH1RN_1LK0RJ_0LD0LP_1LD1LP_0RF0RQ_1RF1RQ_1RI0RV_1RN0RJ_0RV0RJ_1RV1RJ_---1LK_1RF0RJ_---0RF_---1RF_---1RI_---1RN".
Definition tm0' := TM'_from_str "1RN0LD_1RQ0LP_0LH0LK_1LH1LK_0RI0RN_1RI1RN_1LH1RF_1RN1RQ_1LH1RN_1LK0RJ_0LD0LP_1LD1LP_0RF0RQ_1RF1RQ_1RI0RV_1RN0RJ_0RV0RJ_1RV1RJ_---1LK_1RF0RJ_---1LH_---1RF_---0LG_---1LG".
Definition tm1 := TM'_from_str "1RB1RI_1LC1RI_1RI1RD_0RJ0RE_1LF0RE_0LG0LH_1LC1LF_1RI0RE_1RA1RD_---1RA".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RI_1RI1RD_0RJ0RE_1LF0RE_0LG0LH_1LC1LF_1RI0RE_1RA1RD_1RK1RA_1RK1RK".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "FIHQJKDPNV".
Definition mp' := mp_from_str "FIHQJKDPNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM238.


Module TM239.
Definition tm := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_0LB0RA_1RD---".
Definition tm' := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1RD0RA_1RD---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1RN_1RV1RA_1LP0RV_1LK1RV_0LL1RN_1LL---_1RR0LP_1LP0LK_0LP0LK_1LP1LK_0RB1RR_1RB1LP_1RF0LP_1RR1LP_0LL0RA_1RN1RA_0LG0RF_1LG0RR_0RN---_1RN---_1RB---_1LP---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LK1RN_1RV1RA_1LP0RV_1LK1RV_0LL1RN_1LL---_1RR0LP_1LP0LK_0LP0LK_1LP1LK_0RB1RR_1RB1LP_1RF0LP_1RR1LP_0RN0RA_1RN1RA_1RB0RF_1LP0RR_0RN---_1RN---_1RB---_1LP---".
Definition tm1 := TM'_from_str "1RB1RE_1LC1RH_0LD0LC_1RE1LD_1RG1RF_0RB0RE_1RA1LD_1RG---".
Definition tm2 := TM'_from_str "1RB1RE_1LC1RH_0LD0LC_1RE1LD_1RG1RF_0RB0RE_1RA1LD_1RG1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "BFKPRANV".
Definition mp' := mp_from_str "BFKPRANV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM239.


Module TM240.
Definition tm := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1RD0RA_1RD---".
Definition tm' := TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1RD0RA_0LA---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1RN_1RV1RA_1LP0RV_1LK1RV_0LL1RN_1LL---_1RR0LP_1LP0LK_0LP0LK_1LP1LK_0RB1RR_1RB1LP_1RF0LP_1RR1LP_0RN0RA_1RN1RA_1RB0RF_1LP0RR_0RN---_1RN---_1RB---_1LP---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LK1RN_1RV1RA_1LP0RV_1LK1RV_0LL1RN_1LL---_1RR0LP_1LP0LK_0LP0LK_1LP1LK_0RB1RR_1RB1LP_1RF0LP_1RR1LP_0RN0RA_1RN1RA_1RB0RF_1LP0RR_1LK---_1RN---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1RB1RE_1LC1RH_0LD0LC_1RE1LD_1RG1RF_0RB0RE_1RA1LD_1RG---".
Definition tm2 := TM'_from_str "1RB1RE_1LC1RH_0LD0LC_1RE1LD_1RG1RF_0RB0RE_1RA1LD_1RG1RI_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "BFKPRANV".
Definition mp' := mp_from_str "BFKPRANV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM240.


Module TM241.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD0LE_---1LE_0RF1RE_1RB1RC".
Definition tm' := TM_from_str "1LB1LA_1LC0LA_1RD0LE_---1RE_0RF1RE_1RB1RC".
Definition tm0 := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RR0LH_1LS0LD_0LL0LC_1LL1LC_0RN0RF_1RN1RU_---0LS_1RR1LS_---0RJ_---1RR_---0LT_---1LT_0RU0RR_1RU1RR_0RF1RU_0RJ1RR_0RF0RJ_1RF1RJ_1LS1RN_0LD1RU".
Definition tm0' := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RR0LH_1LS0LD_0LL0LC_1LL1LC_0RN0RF_1RN1RU_---0LS_1RR1LS_---0RR_---1RR_---1RU_---1RR_0RU0RR_1RU1RR_0RF1RU_0RJ1RR_0RF0RJ_1RF1RJ_1LS1RN_0LD1RU".
Definition tm1 := TM'_from_str "1LB0LC_0RA1RH_1LD1LC_1LF1LE_0LD0LC_1RG1LB_1RH1RG_0RA0RI_1RJ1RH_---1RG".
Definition tm2 := TM'_from_str "1LB0LC_0RA1RH_1LD1LC_1LF1LE_0LD0LC_1RG1LB_1RH1RG_0RA0RI_1RJ1RH_1RK1RG_1RK1RK".
Definition l0 := [1;1;1;1;1;0;1;0]%N.
Definition mp := mp_from_str "FSDHCLRUJN".
Definition mp' := mp_from_str "FSDHCLRUJN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM241.


Module TM242.
Definition tm := TM_from_str "1RB1RE_1RC1LB_0RD1RA_1LA---_1LF0RC_0RD0LF".
Definition tm' := TM_from_str "1RB1RE_1RC1LB_1RD1RA_1LB---_1LF0RC_1RD0LF".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1RJ1LW_1LH1RI_0RJ1RB_1RJ1LH_1RM0LH_1RB1LH_0RM0RB_1RM1RB_1LH1RF_---1RR_1LH---_1RI---_0LD---_1LD---_---0RI_1LW1RI_0LX0RM_1LX0RB_0RM1LH_1RM0LW_1LH0LW_---1LW".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1RJ1LW_1LH1RI_0RJ1RB_1RJ1LH_1RN0LH_1RB1LH_0RN0RB_1RN1RB_1LH1RF_---1RR_1RB---_1LH---_0LH---_1LH---_---0RI_1LW1RI_0LX0RN_1LX0RB_0RN1LH_1RN0LW_1LH0LW_---1LW".
Definition tm1 := TM'_from_str "1LB1RE_1LC0LB_1RD1LC_1RF1RA_0RH0RD_1RG1LC_1RH1RD_1LC---".
Definition tm2 := TM'_from_str "1LB1RE_1LC0LB_1RD1LC_1RF1RA_0RH0RD_1RG1LC_1RH1RD_1LC1RI_1RI1RI".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "RWHBIFJM".
Definition mp' := mp_from_str "RWHBIFJN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM242.


Module TM243.
Definition tm := TM_from_str "1RB1RA_0RC1RF_1RD---_0LE1LE_1RA1LD_1RD0LF".
Definition tm' := TM_from_str "1RB0RD_0RC1RF_1RD---_0LE1LE_1RA1LD_1RD0LF".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1RI1RF_1RV1RB_0RI0RV_1RI1RV_0RN1RN_---0LW_0RN---_1RN---_0LP---_1LP---_1RF1RB_0LP1LP_0LS0LT_1LS1LT_0RB1LS_1RB1LT_1RF0LP_1RB1LP_0RN0LP_1RN0LW_0LP0LW_1LP1LW".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1RI1RF_1RV1RM_0RI0RV_1RI1RV_0RN1RN_---0LW_0RN---_1RN---_0LP---_1LP---_1RF1RM_0LP1LP_0LS0LT_1LS1LT_0RB1LS_1RB1LT_1RF0LP_1RM1LP_0RN0LP_1RN0LW_0LP0LW_1LP1LW".
Definition tm1 := TM'_from_str "0LB1LB_1LC1LD_1RE0LB_1RH1LB_1RI1RF_1RA0LG_0LB0LG_1RE1RH_0RA---".
Definition tm2 := TM'_from_str "0LB1LB_1LC1LD_1RE0LB_1RH1LB_1RI1RF_1RA0LG_0LB0LG_1RE1RH_0RA1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "NPSTFVWBI".
Definition mp' := mp_from_str "NPSTFVWMI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM243.


Module TM244.
Definition tm := TM_from_str "1RB0RD_0RC1RC_1RD0LF_0LE1LE_1RA1LD_---0LC".
Definition tm' := TM_from_str "1RB1RA_0RC1RC_1RD0LF_0LE1LE_1RA1LD_---0LC".
Definition tm0 := TM'_from_str "0RF0RM_1RF1RM_1RI1RF_1RJ1RM_0RI0RJ_1RI1RJ_0RN1RN_---0LK_0RN---_1RN0LK_0LP0LW_1LP1LW_1RF1RM_0LP1LP_0LS0LT_1LS1LT_0RB1LS_1RB1LT_1RF0LP_1RM1LP_---0LP_---0LW_---0LK_---1LK".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1RI1RF_1RJ1RB_0RI0RJ_1RI1RJ_0RN1RN_---0LK_0RN---_1RN0LK_0LP0LW_1LP1LW_1RF1RB_0LP1LP_0LS0LT_1LS1LT_0RB1LS_1RB1LT_1RF0LP_1RB1LP_---0LP_---0LW_---0LK_---1LK".
Definition tm1 := TM'_from_str "0LB1LB_1LC1LD_1RE0LB_1RI1LB_1RJ1RF_1RA0LG_0LB0LH_---0LG_1RE1RI_0RA---".
Definition tm2 := TM'_from_str "0LB1LB_1LC1LD_1RE0LB_1RI1LB_1RJ1RF_1RA0LG_0LB0LH_1RK0LG_1RE1RI_0RA1RK_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "NPSTFJKWMI".
Definition mp' := mp_from_str "NPSTFJKWBI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM244.


Module TM245.
Definition tm := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_1LD0RC_---0LA".
Definition tm' := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_0RC0RC_---0LA".
Definition tm0 := TM'_from_str "1RN1LH_0LH1LD_0LH0LD_1LH1LD_0RJ0RU_1RJ1RU_1LD---_1RN0LH_1LH0RN_1LD1RN_0LD1RF_1LD1RR_0RF0RR_1RF1RR_1RJ1RI_1RU1RI_1RU0RI_1RI1RI_0LP1LH_1LP0RN_---0LH_---0LD_---0LC_---1LC".
Definition tm0' := TM'_from_str "1RN1LH_0LH1LD_0LH0LD_1LH1LD_0RJ0RU_1RJ1RU_1LD---_1RN0LH_1LH0RN_1LD1RN_0LD1RF_1LD1RR_0RF0RR_1RF1RR_1RJ1RI_1RU1RI_0RI0RI_1RI1RI_1LH1LH_0RN0RN_---0LH_---0LD_---0LC_---1LC".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RE_1LD1LC_1RE0LD_1RA1RF_1RG1RG_1LD0RE_---0LD".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RE_1LD1LC_1RE0LD_1RA1RF_1RG1RG_1LD0RE_1RI0LD_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "FJDHNRIU".
Definition mp' := mp_from_str "FJDHNRIU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM245.


Module TM246.
Definition tm := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_0RC0RC_---0LA".
Definition tm' := TM_from_str "1LB1LA_1RC0RF_1LA1RD_1RB1RE_0RC0LD_---0LA".
Definition tm0 := TM'_from_str "1RN1LH_0LH1LD_0LH0LD_1LH1LD_0RJ0RU_1RJ1RU_1LD---_1RN0LH_1LH0RN_1LD1RN_0LD1RF_1LD1RR_0RF0RR_1RF1RR_1RJ1RI_1RU1RI_0RI0RI_1RI1RI_1LH1LH_0RN0RN_---0LH_---0LD_---0LC_---1LC".
Definition tm0' := TM'_from_str "1RN1LH_0LH1LD_0LH0LD_1LH1LD_0RJ0RU_1RJ1RU_1LD---_1RN0LH_1LH0RN_1LD1RN_0LD1RF_1LD1RR_0RF0RR_1RF1RR_1RJ1RI_1RU1RI_0RI1RJ_1RI1RI_1LH0LO_0RN1LO_---0LH_---0LD_---0LC_---1LC".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RE_1LD1LC_1RE0LD_1RA1RF_1RG1RG_1LD0RE_---0LD".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RE_1LD1LC_1RE0LD_1RA1RF_1RG1RG_1LD0RE_1RI0LD_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "FJDHNRIU".
Definition mp' := mp_from_str "FJDHNRIU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM246.


Module TM247.
Definition tm := TM_from_str "1LB0RD_0LC---_0RD0LF_1RE1RD_0RA1RE_0LB1LA".
Definition tm' := TM_from_str "1LB0RD_0LC---_0RD0LF_1RE1RD_0RA0LD_0LB1LA".
Definition tm0 := TM'_from_str "1LK0RM_---1RM_0LH0RR_1LH0RN_0RR---_0LW---_0LK---_1LK---_0RM0LG_1RM0LD_0RR0LW_0RN1LW_0RR0RN_1RR1RN_1RA1RR_1RR1RN_0RA0RR_1RA1RR_1LK1RA_0RM1RR_0LK1LH_---0RN_0LG0LD_1LG1LD".
Definition tm0' := TM'_from_str "1LK0RM_---1RM_0LH0RR_1LH0RN_0RR---_0LW---_0LK---_1LK---_0RM0LG_1RM0LD_0RR0LW_0RN1LW_0RR0RN_1RR1RN_1RA1RR_1RR1RN_0RA1RA_1RA1RR_1LK0LO_0RM1LO_0LK1LH_---0RN_0LG0LD_1LG1LD".
Definition tm1 := TM'_from_str "1LB0RH_0RF0LC_0LI0LD_1LE0RG_1LB---_1RA1RF_1RF1RG_0RF0RG_0LB---".
Definition tm2 := TM'_from_str "1LB0RH_0RF0LC_0LI0LD_1LE0RG_1LB1RJ_1RA1RF_1RF1RG_0RF0RG_0LB1RJ_1RJ1RJ".
Definition l0 := [0;0;1;1;0;0;1;1]%N.
Definition mp := mp_from_str "AKWDHRNMG".
Definition mp' := mp_from_str "AKWDHRNMG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM247.


Module TM248.
Definition tm := TM_from_str "1LB0RC_1LC0LA_0RD0LA_1RA1RE_0LE0RF_1RA---".
Definition tm' := TM_from_str "1LB0RC_1LC0LA_0RD0LA_1RA1RE_0LE0RF_0LC---".
Definition tm0 := TM'_from_str "1LL0RI_1LC1RI_0LH0RM_1LH0LH_0RR0LH_1LC0RM_0LL0LC_1LL1LC_0RM0LH_1RM0RM_0RB0LC_0RR1LC_0RB0RR_1RB1RR_1LC0RB_1RI1RU_0LS0RU_0RB1RU_0LS0RB_1LS---_0RB---_1RB---_1LC---_1RI---".
Definition tm0' := TM'_from_str "1LL0RI_1LC1RI_0LH0RM_1LH0LH_0RR0LH_1LC0RM_0LL0LC_1LL1LC_0RM0LH_1RM0RM_0RB0LC_0RR1LC_0RB0RR_1RB1RR_1LC0RB_1RI1RU_0LS0RU_0RB1RU_0LS0RB_1LS---_0RB---_0LC---_0LK---_1LK---".
Definition tm1 := TM'_from_str "0RB0LE_0RC0RG_1LD1RA_0LE0RB_1LF1LD_0RG1LD_0RC1RH_0RC---".
Definition tm2 := TM'_from_str "0RB0LE_0RC0RG_1LD1RA_0LE0RB_1LF1LD_0RG1LD_0RC1RH_0RC1RI_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "IMBCHLRU".
Definition mp' := mp_from_str "IMBCHLRU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM248.


Module TM249.
Definition tm := TM_from_str "1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0LC---".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---".
Definition tm0 := TM'_from_str "0RF1RQ_1RF1LD_0LH0LD_1RQ1LD_0LP0RQ_0LH1RQ_0LK0RJ_1LK0RA_1RA1LK_1LX0RA_0LP0LH_1LP1LH_0RR1LK_1RR---_1RJ0LX_1RA1LX_0RJ0RA_1RJ1RA_1LX0RF_0RA1RQ_0LP---_0LH---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF1RQ_1RF1LD_0LH0LD_1RQ1LD_0LP0RQ_0LH1RQ_0LK0RJ_1LK0RA_1RA1LK_1LX0RA_0LP0LH_1LP1LH_0RR1LK_1RR---_1RJ0LX_1RA1LX_0RJ0RA_1RJ1RA_1LX0RF_0RA1RQ_0RI---_1RI---_1RA---_1LK---".
Definition tm1 := TM'_from_str "0RB1RG_0LC1RG_1LD0RA_0LE0LC_1RA1LF_1LD---_0RH0RA_1LF0RA".
Definition tm2 := TM'_from_str "0RB1RG_0LC1RG_1LD0RA_0LE0LC_1RA1LF_1LD1RI_0RH0RA_1LF0RA_1RI1RI".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "AFHKPXQJ".
Definition mp' := mp_from_str "AFHKPXQJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM249.


Module TM250.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LD_0LA1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LA_0LA1RF_0RA1RB".
Definition tm0 := TM'_from_str "1LK0RM_---1RM_0LH0RQ_1LH0LH_1RQ---_0LW---_0LK---_1LK---_0RN1LK_1RN0LW_1RQ0LW_0LO1LW_0RQ0LH_1RQ0LO_0LH0LO_0RV1LO_0LH0RV_0RQ1RV_0LC1RA_1LC1RF_0RA0RF_1RA1RF_1LK0LW_0RM---".
Definition tm0' := TM'_from_str "1LK0RM_---1RM_0LH0RQ_1LH0LH_1RQ---_0LW---_0LK---_1LK---_0RN1LK_1RN0LW_1RQ0LW_0RQ1LW_0RQ0LH_1RQ0RQ_0LH0LC_0RV1LC_0LH0RV_0RQ1RV_0LC1RA_1LC1RF_0RA0RF_1RA1RF_1LK0LW_0RM---".
Definition tm1 := TM'_from_str "0RB0LC_0LC0RE_1LD---_1RB0LG_1RF1RH_1LD0RA_1LD0LG_0LG---".
Definition tm2 := TM'_from_str "0RB0LC_0LC0RE_1LD1RI_1RB0LG_1RF1RH_1LD0RA_1LD0LG_0LG1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "MQHKVAWF".
Definition mp' := mp_from_str "MQHKVAWF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM250.


Module TM251.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE0LF_0LA1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1LB_0LA1RF_0RA1RB".
Definition tm0 := TM'_from_str "1LK0RM_---1RM_0LH0RQ_1LH1LK_1RQ---_0LW---_0LK---_1LK---_0RN1LK_1RN0LW_1RQ0LW_0LW1LW_0RQ1LK_1RQ0LW_0LH0LW_0RV1LW_0LH0RV_0RQ1RV_0LC1RA_1LC1RF_0RA0RF_1RA1RF_1LK0LW_0RM---".
Definition tm0' := TM'_from_str "1LK0RM_---1RM_0LH0RQ_1LH1LK_1RQ---_0LW---_0LK---_1LK---_0RN1LK_1RN0LW_1RQ0LW_---1LW_0RQ1LK_1RQ---_0LH0LH_0RV1LH_0LH0RV_0RQ1RV_0LC1RA_1LC1RF_0RA0RF_1RA1RF_1LK0LW_0RM---".
Definition tm1 := TM'_from_str "0RB1LD_0LC0RE_1LD---_1RB0LG_1RF1RH_1LD0RA_1LD0LG_0LG---".
Definition tm2 := TM'_from_str "0RB1LD_0LC0RE_1LD1RI_1RB0LG_1RF1RH_1LD0RA_1LD0LG_0LG1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "MQHKVAWF".
Definition mp' := mp_from_str "MQHKVAWF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM251.


Module TM252.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1RF_0LA1RF_0RA1RB".
Definition tm' := TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1LD_0LA1RF_0RA1RB".
Definition tm0 := TM'_from_str "1LK0RM_---1RM_0LH0RQ_1LH0RV_1RQ---_0LW---_0LK---_1LK---_0RN1LK_1RN0LW_1RQ0LW_1RV1LW_0RQ0RV_1RQ1RV_0LH1RA_0RV1RF_0LH0RV_0RQ1RV_0LC1RA_1LC1RF_0RA0RF_1RA1RF_1LK0LW_0RM---".
Definition tm0' := TM'_from_str "1LK0RM_---1RM_0LH0RQ_1LH0RV_1RQ---_0LW---_0LK---_1LK---_0RN1LK_1RN0LW_1RQ0LW_1LP1LW_0RQ0RV_1RQ1LP_0LH0LP_0RV1LP_0LH0RV_0RQ1RV_0LC1RA_1LC1RF_0RA0RF_1RA1RF_1LK0LW_0RM---".
Definition tm1 := TM'_from_str "0RB0RE_0LC0RE_1LD---_1RB0LG_1RF1RH_1LD0RA_1LD0LG_0LG---".
Definition tm2 := TM'_from_str "0RB0RE_0LC0RE_1LD1RI_1RB0LG_1RF1RH_1LD0RA_1LD0LG_0LG1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "MQHKVAWF".
Definition mp' := mp_from_str "MQHKVAWF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM252.


Module TM253.
Definition tm := TM_from_str "1RB0RA_0RC0RF_1RD0LC_1LE---_1LF1LE_1RA0LE".
Definition tm' := TM_from_str "1RB0RA_0RC0RF_1RD1LD_1LE---_1LF1LE_1RA0LE".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RI0RF_1RU0RA_0RI0RU_1RI1RU_0RN0RB_1LT0LX_0RN1LT_1RN0LK_1LT0LK_---1LK_1LX---_1LT---_0LT---_1LT---_1RA1LX_1LS1LT_0LX0LT_1LX1LT_0RB0LX_1RB0LT_1RF0LS_1RA1LS".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RI0RF_1RU0RA_0RI0RU_1RI1RU_0RN0RB_1LT0LX_0RN1LT_1RN---_1LT0LP_---1LP_1LX---_1LT---_0LT---_1LT---_1RA1LX_1LS1LT_0LX0LT_1LX1LT_0RB0LX_1RB0LT_1RF0LS_1RA1LS".
Definition tm1 := TM'_from_str "1RB1RH_1RC1RI_0RD1LE_1LE---_1LF1LE_1RH1LG_0LF0LE_0RB0RH_0RA0LF".
Definition tm2 := TM'_from_str "1RB1RH_1RC1RI_0RD1LE_1LE1RJ_1LF1LE_1RH1LG_0LF0LE_0RB0RH_0RA0LF_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "BFINTXSAU".
Definition mp' := mp_from_str "BFINTXSAU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM253.


Module TM254.
Definition tm := TM_from_str "1RB0RC_1LC1LD_1RD0LB_1LF1RE_1RA0RE_---0LB".
Definition tm' := TM_from_str "1RB0RC_1LC1LD_1RD0LB_0LF1RE_1RA0RE_---1RB".
Definition tm0 := TM'_from_str "0RF0RI_1RF1RI_1LG0RN_1RQ0LL_1RR1LX_1LG1RQ_0LL0LP_1LL1LP_0RN0LL_1RN0LP_1LG0LG_1RR1LG_---0RR_1LG1RR_0LX1RB_1LX1RQ_0RB0RQ_1RB1RQ_1RF0RB_1RI0RQ_---0LL_---0LP_---0LG_---1LG".
Definition tm0' := TM'_from_str "0RF0RI_1RF1RI_1LG0RN_1RQ0LL_1RR1LW_1LG1RQ_0LL0LP_1LL1LP_0RN0LL_1RN0LP_1LG0LG_1RR1LG_---0RR_1LG1RR_0LW1RB_1LW1RQ_0RB0RQ_1RB1RQ_1RF0RB_1RI0RQ_---0RF_---1RF_---1LG_---1RQ".
Definition tm1 := TM'_from_str "0RB0LD_1LC1RG_0LD0LE_1RG1LC_1LF1RI_---1LC_1RH1RI_1RJ1RA_0RH0RI_1LC1RI".
Definition tm2 := TM'_from_str "0RB0LD_1LC1RG_0LD0LE_1RG1LC_1LF1RI_1RK1LC_1RH1RI_1RJ1RA_0RH0RI_1LC1RI_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "INGLPXRBQF".
Definition mp' := mp_from_str "INGLPWRBQF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM254.


Module TM255.
Definition tm := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE0LF_1RA1LB_0LF1RB".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_---1RD_1LF1LE_1RE0LD_1RA1LB".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RM0RA_---0RM_1LO1RM_0LL1RA_1LL0LW_---0LT_---0LW_---0LO_---1LO_1RA0LW_1LH1LO_0LT0LW_1LT1LW_0RB1LL_1RB0LW_1RF0LH_1RA1LH_0LW0RF_1LO1RF_0LW1LO_1LW1RM".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RM0RA_---0RM_1LO1RM_0LL1RA_1LL0LT_---0RN_---1RN_---1LH_---1LO_1RA0LT_1LH1LO_0LX0LT_1LX1LT_0RR0LX_1RR0LT_1RR0LO_0LT1LO_0RB1LL_1RB0LT_1RF0LH_1RA1LH".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RE_0LD0LG_1RA1LF_1RA0LG_1LH0LG_0LG1LC_---1LC".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RE_0LD0LG_1RA1LF_1RA0LG_1LH0LG_0LG1LC_1RI1LC_1RI1RI".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "AFOTMHWL".
Definition mp' := mp_from_str "AFOXMHTL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM255.


Module TM256.
Definition tm := TM_from_str "1RB0RA_1LC0RD_---1RD_1LF1LE_1RE0LD_1RA1LB".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RF0LD".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RM0RA_---0RM_1LO1RM_0LL1RA_1LL0LT_---0RN_---1RN_---1LH_---1LO_1RA0LT_1LH1LO_0LX0LT_1LX1LT_0RR0LX_1RR0LT_1RR0LO_0LT1LO_0RB1LL_1RB0LT_1RF0LH_1RA1LH".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RM0RA_---0RM_1LO1RM_0LL1RA_1LL0LX_---0LT_---0LX_---0LO_---1LO_1RA0LX_1LH1LO_0LT0LX_1LT1LX_0RB1LL_1RB0LX_1RF0LH_1RA1LH_0RV0LT_1RV0LX_1RV0LO_0LX1LO".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RE_0LD0LG_1RA1LF_1RA0LG_1LH0LG_0LG1LC_---1LC".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RE_0LD0LG_1RA1LF_1RA0LG_1LH0LG_0LG1LC_1RI1LC_1RI1RI".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "AFOXMHTL".
Definition mp' := mp_from_str "AFOTMHXL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM256.


Module TM257.
Definition tm := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RF0LD".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RC0LD".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RM0RA_---0RM_1LO1RM_0LL1RA_1LL0LX_---0LT_---0LX_---0LO_---1LO_1RA0LX_1LH1LO_0LT0LX_1LT1LX_0RB1LL_1RB0LX_1RF0LH_1RA1LH_0RV0LT_1RV0LX_1RV0LO_0LX1LO".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RM0RA_---0RM_1LO1RM_0LL1RA_1LL0LX_---0LT_---0LX_---0LO_---1LO_1RA0LX_1LH1LO_0LT0LX_1LT1LX_0RB1LL_1RB0LX_1RF0LH_1RA1LH_0RJ0LT_1RJ0LX_---0LO_0LX1LO".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RE_0LD0LG_1RA1LF_1RA0LG_1LH0LG_0LG1LC_---1LC".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RE_0LD0LG_1RA1LF_1RA0LG_1LH0LG_0LG1LC_1RI1LC_1RI1RI".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "AFOTMHXL".
Definition mp' := mp_from_str "AFOTMHXL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM257.


Module TM258.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA0RF_1LA---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RA---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RB_1RB0RU_1LP0RB_1LK1RB_0LL1RF_1LL1RQ_1RQ0LP_1LC0LK_0LP0LK_1LP1LK_0RB1LK_1RB0RB_1RF0LC_1RQ1LC_0RB0RU_1RB1RU_1RF1RB_1RQ---_1RB---_0RU---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RB_1RB0RV_1LP0RB_1LK1RB_0LL1RF_1LL1RQ_1RQ0LP_1LC0LK_0LP0LK_1LP1LK_0RB1LK_1RB0RB_1RF0LC_1RQ1LC_0RB0RV_1RB1RV_1RF1RB_1RQ---_0RB---_1RB---_1RF---_1RQ---".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_1RF1LE_1LC0RA_0RA0RG_1RA---".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_1RF1LE_1LC0RA_0RA0RG_1RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "BFKPCQU".
Definition mp' := mp_from_str "BFKPCQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM258.


Module TM259.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RA---".
Definition tm' := TM_from_str "1RB0RE_1LC0LE_1LD0LC_1RA0LA_1RA1RF_1RA---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RB_1RB0RV_1LP0RB_1LK1RB_0LL1RF_1LL1RQ_1RQ0LP_1LC0LK_0LP0LK_1LP1LK_0RB1LK_1RB0RB_1RF0LC_1RQ1LC_0RB0RV_1RB1RV_1RF1RB_1RQ---_0RB---_1RB---_1RF---_1RQ---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RB_1RB0RV_1LP1RF_1LK1RB_0LL0LS_1LL1LS_1RQ0LP_1LC0LK_0LP0LK_1LP1LK_0RB1LK_1RB0RB_1RF0LC_1RQ1LC_0RB0RV_1RB1RV_1RF1RB_1RQ---_0RB---_1RB---_1RF---_1RQ---".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_1RF1LE_1LC0RA_0RA0RG_1RA---".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_1RF1LE_1LC0RA_0RA0RG_1RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "BFKPCQV".
Definition mp' := mp_from_str "BFKPCQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM259.


Module TM260.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LB---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RB_1RB0RV_1LP0RB_1LK1RB_0LL1RF_1LL1RQ_1RQ0LP_1LC0LK_0LP0LK_1LP1LK_0RB1LK_1RB0RB_1RF0LC_1RQ1LC_0RB0RV_1RB1RV_1RF1RF_1RQ---_0RF---_1RF---_1LK---_1RB---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RB_1RB0RV_1LP0RB_1LK1RB_0LL1RF_1LL1RQ_1RQ0LP_1LC0LK_0LP0LK_1LP1LK_0RB1LK_1RB0RB_1RF0LC_1RQ1LC_0RB0RV_1RB1RV_1RF1RF_1RQ---_0LL---_1RF---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_1RF1LE_1LC0RA_0RA0RG_1RB---".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RA_0LD0LC_1RF1LE_1LC0RA_0RA0RG_1RB1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "BFKPCQV".
Definition mp' := mp_from_str "BFKPCQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM260.


Module TM261.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LA---".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LS_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LS0RJ_1RM0RE_1LD0RM_1LS1RM_0LP1RE_1LP0LP_1RE0LP_1LP0LX_0LD0LS_1LD1LS_1LD1LD_1LS---_0LP0LX_1LP1LX_0RA---_1RA---_0RF---_1LD---".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LS_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LS0RJ_1RM0RE_1LD0RM_1LS1RM_0LP1RE_1LP0LP_1RE0LP_1LP0LX_0LD0LS_1LD1LS_1LD1LD_1LS---_0LP0LX_1LP1LX_1RE---_1LP---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LG_1LD1LB_1RE1LC_0RA0RE_1RE0LC_1LD---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LG_1LD1LB_1RE1LC_0RA0RE_1RE0LC_1LD1RH_1RH1RH".
Definition l0 := [1;1;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "JSPDEMX".
Definition mp' := mp_from_str "JSPDEMX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM261.


Module TM262.
Definition tm := TM_from_str "1RB1LA_1RC1LD_1LA0RE_1RF0LA_0LA0RD_---0RD".
Definition tm' := TM_from_str "1RB1LA_1RC1LD_1LA0RE_1RE0LA_0LF0RD_1RB---".
Definition tm0 := TM'_from_str "0RF1LC_1RF1LD_1RJ0LD_1LC1LD_0RJ1RM_1RJ1LC_1LD0LP_1RQ1LP_1LC0RQ_1LD1RQ_0LD1RJ_1LD0RM_0RV1RJ_1RV0LD_---0LC_1RM1LC_1RJ0RM_0LD1RM_0LC0RV_1LC1RJ_---0RM_---1RM_---0RV_---1RJ".
Definition tm0' := TM'_from_str "0RF1LC_1RF1LD_1RJ0LD_1LC1LD_0RJ1RM_1RJ1LC_1LD0LP_1RQ1LP_1LC0RQ_1LD1RQ_0LD1RJ_1LD0RM_0RR1RJ_1RR0LD_---0LC_1RM1LC_1RJ0RM_---1RM_0LW0RR_1LW1RJ_0RF---_1RF---_1RJ---_1LC---".
Definition tm1 := TM'_from_str "1LB1RD_1LC1LB_1RA0LB_1RA0RE_0RF1RA_---1RE".
Definition tm2 := TM'_from_str "1LB1RD_1LC1LB_1RA0LB_1RA0RE_0RF1RA_1RG1RE_1RG1RG".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JDCQMV".
Definition mp' := mp_from_str "JDCQMR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 5%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM262.


Module TM263.
Definition tm := TM_from_str "1RB0LF_1RC0RB_0RD0RA_1RE1LE_1LF---_1LA1LF".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LX_1RJ0LW_1RE1LW_0RJ0RE_1RJ1RE_1RM0RJ_1RA0RE_0RM0RA_1RM1RA_0RR0RF_1LX0LD_0RR1LX_1RR---_1LX0LT_---1LT_1LD---_1LX---_0LX---_1LX---_1RE1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LX_1RJ0LW_1RE1LW_0RJ0RE_1RJ1RE_1RM0RJ_1RA0RE_0RM0RA_1RM1RA_0RR0RF_1LX0LD_0RR1LX_1RR0LO_1LX0LO_---1LO_1LD---_1LX---_0LX---_1LX---_1RE1LD_1LW1LX_0LD0LX_1LD1LX".
Definition tm1 := TM'_from_str "0RB1LC_1LC---_1LD1LC_1RF1LE_0LD0LC_0RG0RF_1RA1RH_0RI0LD_1RG1RF".
Definition tm2 := TM'_from_str "0RB1LC_1LC1RJ_1LD1LC_1RF1LE_0LD0LC_0RG0RF_1RA1RH_0RI0LD_1RG1RF_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "MRXDWEJAF".
Definition mp' := mp_from_str "MRXDWEJAF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM263.


Module TM264.
Definition tm := TM_from_str "1RB0LA_1RC1LB_1LB1RD_1RE0RC_1LA0RF_1RC---".
Definition tm' := TM_from_str "1RB0LA_1RC---_1LD1RE_1RC1LD_1RF0RC_1LA0RB".
Definition tm0 := TM'_from_str "0RF1RJ_1RF0LC_1RJ0LC_1LH1LC_0RJ1RN_1RJ1LH_1LH0LH_1RN1LH_1RN0RN_1LH1RN_0LH1RR_1LH1RI_0RR0RI_1RR1RI_1LC1RN_1RU0RN_1LH0RU_1LC1RU_0LD0RJ_1LD---_0RJ---_1RJ---_1LH---_1RN---".
Definition tm0' := TM'_from_str "0RF1RJ_1RF0LC_1RJ0LC_---1LC_0RJ---_1RJ---_1LP---_1RR---_1RR0RR_1LP1RR_0LP1RV_1LP1RI_0RJ1RR_1RJ1LP_1LP0LP_1RR1LP_0RV0RI_1RV1RI_1LC1RR_1RE0RR_---0RE_1LC1RE_0LD0RJ_1LD---".
Definition tm1 := TM'_from_str "1LB1RG_1RC0LB_1LD1RE_1RE1LD_1RA1RF_1RE0RE_0RC---".
Definition tm2 := TM'_from_str "1LB1RG_1RC0LB_1LD1RE_1RE1LD_1RA1RF_1RE0RE_0RC1RH_1RH1RH".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "RCJHNIU".
Definition mp' := mp_from_str "VCJPRIE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM264.


Module TM265.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RC1RE_0RF0RA_1LD---".
Definition tm' := TM_from_str "1LB---_1LC0LB_1RD0LF_1LB1RE_1RC1RF_0RA0RD".
Definition tm0 := TM'_from_str "1LL0RN_1LG1RN_0LH1RJ_1LH1RR_1RN0LL_1LS0LG_0LL0LG_1LL1LG_0RB1LL_1RB1LL_1LG0LS_1RN1LS_0RJ0RR_1RJ1RR_1RB1RU_1LL1RA_0RU0RA_1RU1RA_1LL1LL_---0RN_1LL---_1RA---_0LP---_1LP---".
Definition tm0' := TM'_from_str "1LL---_1LG---_0LH---_1LH---_1RR0LL_1LW0LG_0LL0LG_1LL1LG_0RN1LL_1RN1LL_1LG0LW_1RR1LW_1LL0RR_1LG1RR_0LH1RJ_1LH1RV_0RJ0RV_1RJ1RV_1RN1RA_1LL1RM_0RA0RM_1RA1RM_1LL1LL_---0RR".
Definition tm1 := TM'_from_str "1RB1LD_1LC1RF_0LD0LC_1RF1LE_1LD1LD_1RA1RG_1RI1RH_1LD0RF_1LD---".
Definition tm2 := TM'_from_str "1RB1LD_1LC1RF_0LD0LC_1RF1LE_1LD1LD_1RA1RG_1RI1RH_1LD0RF_1LD1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "JBGLSNRAU".
Definition mp' := mp_from_str "JNGLWRVMA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM265.


Module TM266.
Definition tm := TM_from_str "1LB---_1LC0LB_1RD0LF_1LB1RE_1RC1RF_0RA0RD".
Definition tm' := TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RC1RE_1RF0RA_0LE---".
Definition tm0 := TM'_from_str "1LL---_1LG---_0LH---_1LH---_1RR0LL_1LW0LG_0LL0LG_1LL1LG_0RN1LL_1RN1LL_1LG0LW_1RR1LW_1LL0RR_1LG1RR_0LH1RJ_1LH1RV_0RJ0RV_1RJ1RV_1RN1RA_1LL1RM_0RA0RM_1RA1RM_1LL1LL_---0RR".
Definition tm0' := TM'_from_str "1LL0RN_1LG1RN_0LH1RJ_1LH1RR_1RN0LL_1LS0LG_0LL0LG_1LL1LG_0RB1LL_1RB1LL_1LG0LS_1RN1LS_0RJ0RR_1RJ1RR_1RB1RV_1LL1RA_0RV0RA_1RV1RA_1LL1LL_---0RN_1LL---_1LL---_0LS---_1LS---".
Definition tm1 := TM'_from_str "1RB1LD_1LC1RF_0LD0LC_1RF1LE_1LD1LD_1RA1RG_1RI1RH_1LD0RF_1LD---".
Definition tm2 := TM'_from_str "1RB1LD_1LC1RF_0LD0LC_1RF1LE_1LD1LD_1RA1RG_1RI1RH_1LD0RF_1LD1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "JNGLWRVMA".
Definition mp' := mp_from_str "JBGLSNRAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM266.


Module TM267.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF0LF_0RB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_0RB---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU---_0RE0LW_---1LW_0RE---_1RE---_1LD---_0RN---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU1LK_0RE0LL_---1LL_0RE---_1RE---_1LD---_0RN---".
Definition tm1 := TM'_from_str "1RB1RF_1RC1RG_1LD1RA_0LE0LD_1RA1LE_1LE0RA_0RH1LE_0RF---".
Definition tm2 := TM'_from_str "1RB1RF_1RC1RG_1LD1RA_0LE0LD_1RA1LE_1LE0RA_0RH1LE_0RF1RI_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "NBFKDEQU".
Definition mp' := mp_from_str "NBFKDEQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM267.


Module TM268.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LD---_1RA1RF".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_1LC---_1RA0LD".
Definition tm0 := TM'_from_str "0RM1LH_1LG1LD_0LH0LD_1LH1LD_0RI0RV_1RI0LG_0RV0LG_0RM1LG_0RV0RM_1RV1RM_1RB0RR_1RV0RJ_0RR0RJ_1RR1RJ_1RV1RV_---1RM_1RV---_1RV---_0LO---_1LO---_0RB0RV_1RB1RV_1LG1RB_1LD1RV".
Definition tm0' := TM'_from_str "0RM1LH_1LG1LD_0LH0LD_1LH1LD_0RI0RV_1RI0LG_0RV0LG_0RM1LG_0RV0RM_1RV1RM_1RB0RQ_1RV0RJ_0RQ0RJ_1RQ1RJ_1RV1RV_---1RM_1RV---_0RJ---_0LL---_1LL---_0RB1RV_1RB1RV_1LG0LO_1LD1LO".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BGVDHMJR".
Definition mp' := mp_from_str "BGVDHMJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM268.


Module TM269.
Definition tm := TM_from_str "1RB0LD_1RC0RE_1LA0RB_0LF1LA_1RC---_0RA0LA".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LA0RB_0LF0RE_0LC---_0RA0LA".
Definition tm0 := TM'_from_str "0RF0LW_1RF0LD_1RJ0LO_1RQ1LO_0RJ0RQ_1RJ1RQ_1LO0RJ_1RE---_1RQ0RE_1LO1RE_0LD0RJ_1LD0RQ_0RF1RQ_0LC1LO_0LW0LD_1LW1LD_0RJ---_1RJ---_1LO---_1RE---_0RA1RJ_1RA0LO_0RF0LC_0LW1LC".
Definition tm0' := TM'_from_str "0RF0LW_1RF0LD_1RJ0LO_1RR1LO_0RJ0RR_1RJ1RR_1LO0RJ_1RE---_1RR0RE_1LO1RE_0LD0RJ_1LD0RR_0RF0RQ_0LC1RQ_0LW0LD_1LW---_0LD---_0RJ---_0LK---_1LK---_0RA1RJ_1RA0LO_0RF0LC_0LW1LC".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LE_0RF0LD_1RA0LB_1RG1LB_1RA1RG_0RA---_0RA0RG".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LE_0RF0LD_1RA0LB_1RG1LB_1RA1RG_0RA1RI_0RA0RG_1RI1RI".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JOWCDFQE".
Definition mp' := mp_from_str "JOWCDFRE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM269.


Module TM270.
Definition tm := TM_from_str "1RB0LD_1RC1RE_1LA0RB_0LF0RE_0LC---_0RA0LA".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LA0RB_0LF1LA_0LC---_0RA0LA".
Definition tm0 := TM'_from_str "0RF0LW_1RF0LD_1RJ0LO_1RR1LO_0RJ0RR_1RJ1RR_1LO0RJ_1RE---_1RR0RE_1LO1RE_0LD0RJ_1LD0RR_0RF0RQ_0LC1RQ_0LW0LD_1LW---_0LD---_0RJ---_0LK---_1LK---_0RA1RJ_1RA0LO_0RF0LC_0LW1LC".
Definition tm0' := TM'_from_str "0RF0LW_1RF0LD_1RJ0LO_1RR1LO_0RJ0RR_1RJ1RR_1LO0RJ_1RE---_1RR0RE_1LO1RE_0LD0RJ_1LD0RR_0RF1RR_0LC1LO_0LW0LD_1LW1LD_0LD---_0RJ---_0LK---_1LK---_0RA1RJ_1RA0LO_0RF0LC_0LW1LC".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LE_0RF0LD_1RA0LB_1RG1LB_1RA1RG_0RA---_0RA0RG".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LE_0RF0LD_1RA0LB_1RG1LB_1RA1RG_0RA1RI_0RA0RG_1RI1RI".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JOWCDFRE".
Definition mp' := mp_from_str "JOWCDFRE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM270.


Module TM271.
Definition tm := TM_from_str "1LB0RD_1RC0LF_0RE0LD_1RC1RD_1RA---_0LB1LA".
Definition tm' := TM_from_str "1LB0RF_1RC0LE_0RD1RC_1RA---_0LB1LA_1RC1RF".
Definition tm0 := TM'_from_str "1RJ0RM_1LW1RM_0LH0RJ_1LH0RN_0RJ0LG_1RJ0LD_1RQ0LW_1RJ1LW_0RQ1RQ_1RQ1RJ_0RB0LO_---1LO_0RJ0RN_1RJ1RN_1RQ1RJ_1RJ1RN_0RB---_1RB---_1LW---_1RM---_1RQ1LH_0LW0RN_0LG0LD_1LG1LD".
Definition tm0' := TM'_from_str "1RJ0RU_1LS1RU_0LH0RJ_1LH0RV_0RJ0LG_1RJ0LD_1RM0LS_1RJ1LS_0RM0RJ_1RM1RJ_0RB1RM_---1RJ_0RB---_1RB---_1LS---_1RU---_1RM1LH_0LS0RV_0LG0LD_1LG1LD_0RJ0RV_1RJ1RV_1RM1RJ_1RJ1RV".
Definition tm1 := TM'_from_str "0RB---_1LC1RI_0LD0LE_1RA0LC_1LF0RH_1RG1LC_1RA1RG_1RG1RH_0RG0RH".
Definition tm2 := TM'_from_str "0RB1RJ_1LC1RI_0LD0LE_1RA0LC_1LF0RH_1RG1LC_1RA1RG_1RG1RH_0RG0RH_1RJ1RJ".
Definition l0 := [0;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "QBWGDHJNM".
Definition mp' := mp_from_str "MBSGDHJVU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM271.


Module TM272.
Definition tm := TM_from_str "1RB0RA_1RC0RE_1LD---_1RA1LE_1LD0LF_1LE0LA".
Definition tm' := TM_from_str "1RB0RA_0RC0RE_1LD---_1LE0LA_1LF0LD_1RA1LE".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_1RQ0RA_0RJ0RQ_1RJ1RQ_1LT1RA_---0LT_1RA---_1LT---_0LP---_1LP---_0RB1LP_1RB1LW_1RF0LT_1RA1LT_1RA0LT_1LT0LC_0LP0LW_1LP1LW_1LP1RJ_1LW0RF_0LT0LC_1LT1LC".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RI0RF_1RQ0RA_0RI0RQ_1RI1RQ_1LT1RA_---0LT_1LT---_1LC---_0LP---_1LP---_1LX1RI_1LO0RF_0LT0LC_1LT1LC_1RA0LT_1LT0LC_0LX0LO_1LX1LO_0RB1LX_1RB1LO_1RF0LT_1RA1LT".
Definition tm1 := TM'_from_str "1RB1RH_1LC---_1LF1LD_0LC0LE_1RB0RA_1RG1LC_0RA0RG_1RG0LC".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RI_1LF1LD_0LC0LE_1RB0RA_1RG1LC_0RA0RG_1RG0LC_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "FJTWCPAQ".
Definition mp' := mp_from_str "FITOCXAQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM272.


Module TM273.
Definition tm := TM_from_str "1LB---_1RC1LE_0RE0RD_0LB0RC_1LA0LF_1RC1LB".
Definition tm' := TM_from_str "1LB---_1RC1LE_0RE0RD_0LB0RC_1LA0LF_0RD1LB".
Definition tm0 := TM'_from_str "1RM---_1LT---_0LH---_1LH---_0RJ1LD_1RJ1LW_1RQ0LT_1RM1LT_0RQ0RM_1RQ1RM_1LH1RQ_1RQ0RI_1RQ0RI_0LT1RI_0LG0RQ_1LG0RM_1LH1RQ_---0LH_0LD0LW_1LD1LW_0RJ1RM_1RJ1LT_1RQ0LH_1RM1LH".
Definition tm0' := TM'_from_str "1RM---_1LT---_0LH---_1LH---_0RJ1LD_1RJ1LW_1RQ0LT_1RM1LT_0RQ0RM_1RQ1RM_1LH1RQ_1RQ0RI_1RQ0RI_0LT1RI_0LG0RQ_1LG0RM_1LH1RQ_---0LH_0LD0LW_1LD1LW_0RM1RM_1RM1LT_1RQ0LH_0RI1LH".
Definition tm1 := TM'_from_str "1LB1RA_1RE1LC_1LF1LD_1RA0LB_1RA0RG_1LB---_0RA0RE".
Definition tm2 := TM'_from_str "1LB1RA_1RE1LC_1LF1LD_1RA0LB_1RA0RG_1LB1RH_0RA0RE_1RH1RH".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "QHTWMDI".
Definition mp' := mp_from_str "QHTWMDI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM273.


Module TM274.
Definition tm := TM_from_str "1LB---_1RC1LE_0RE0RD_0LB0RC_1LA0LF_0RD1LB".
Definition tm' := TM_from_str "1LB---_1RC1LE_0RE0RD_1LC0RC_1LA0LF_1RC1LB".
Definition tm0 := TM'_from_str "1RM---_1LT---_0LH---_1LH---_0RJ1LD_1RJ1LW_1RQ0LT_1RM1LT_0RQ0RM_1RQ1RM_1LH1RQ_1RQ0RI_1RQ0RI_0LT1RI_0LG0RQ_1LG0RM_1LH1RQ_---0LH_0LD0LW_1LD1LW_0RM1RM_1RM1LT_1RQ0LH_0RI1LH".
Definition tm0' := TM'_from_str "1RM---_1LT---_0LH---_1LH---_0RJ1LD_1RJ1LW_1RQ0LT_1RM1LT_0RQ0RM_1RQ1RM_1LH1RQ_1RQ0RI_1RQ0RI_0RI1RI_0LL0RQ_1LL0RM_1LH1RQ_---0LH_0LD0LW_1LD1LW_0RJ1RM_1RJ1LT_1RQ0LH_1RM1LH".
Definition tm1 := TM'_from_str "1LB1RA_1RE1LC_1LF1LD_1RA0LB_1RA0RG_1LB---_0RA0RE".
Definition tm2 := TM'_from_str "1LB1RA_1RE1LC_1LF1LD_1RA0LB_1RA0RG_1LB1RH_0RA0RE_1RH1RH".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "QHTWMDI".
Definition mp' := mp_from_str "QHTWMDI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM274.


Module TM275.
Definition tm := TM_from_str "1LB---_1RC1LE_0RE0RD_1LC0RC_1LA0LF_1RC1LB".
Definition tm' := TM_from_str "1LB---_1RC1LF_0RF0RD_0LE0RC_1RC1LB_1LA0LE".
Definition tm0 := TM'_from_str "1RM---_1LT---_0LH---_1LH---_0RJ1LD_1RJ1LW_1RQ0LT_1RM1LT_0RQ0RM_1RQ1RM_1LH1RQ_1RQ0RI_1RQ0RI_0RI1RI_0LL0RQ_1LL0RM_1LH1RQ_---0LH_0LD0LW_1LD1LW_0RJ1RM_1RJ1LT_1RQ0LH_1RM1LH".
Definition tm0' := TM'_from_str "1RM---_1LX---_0LH---_1LH---_0RJ1LD_1RJ1LS_1RU0LX_1RM1LX_0RU0RM_1RU1RM_1LH1RU_1RU0RI_1RU0RI_0LH1RI_0LS0RU_1LS0RM_0RJ1RM_1RJ1LX_1RU0LH_1RM1LH_1LH1RU_---0LH_0LD0LS_1LD1LS".
Definition tm1 := TM'_from_str "1LB1RA_1RE1LC_1LF1LD_1RA0LB_1RA0RG_1LB---_0RA0RE".
Definition tm2 := TM'_from_str "1LB1RA_1RE1LC_1LF1LD_1RA0LB_1RA0RG_1LB1RH_0RA0RE_1RH1RH".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "QHTWMDI".
Definition mp' := mp_from_str "UHXSMDI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM275.


Module TM276.
Definition tm := TM_from_str "1LB0RE_1LC1LB_1RD0LA_1RA1RC_0RC0RF_0RC---".
Definition tm' := TM_from_str "1LB0RE_1LC1LB_1RD0LA_1RA1RC_0RC1RF_0LA---".
Definition tm0 := TM'_from_str "1LL0RQ_1LH1RQ_0LH0RI_1LH0RU_1RJ1LL_1LC1LH_0LL0LH_1LL1LH_0RN0LH_1RN0RI_1RB0LC_1RJ1LC_0RB0RJ_1RB1RJ_1LH1RN_1RQ0RI_0RI0RU_1RI1RU_0RN0RI_0LH---_0RI---_1RI---_0RN---_0LH---".
Definition tm0' := TM'_from_str "1LL0RQ_1LH1RQ_0LH0RI_1LH0RV_1RJ1LL_1LC1LH_0LL0LH_1LL1LH_0RN0LH_1RN0RI_1RB0LC_1RJ1LC_0RB0RJ_1RB1RJ_1LH1RN_1RQ0RI_0RI0RV_1RI1RV_0RN0RI_0LH---_0LH---_0RI---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1RH_1LC1LB_1RD1LF_1RG0RE_0RG0LB_0LB0RE_1RA1RD_0RE0RI_0RE---".
Definition tm2 := TM'_from_str "1LB1RH_1LC1LB_1RD1LF_1RG0RE_0RG0LB_0LB0RE_1RA1RD_0RE0RI_0RE1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "BHLJICNQU".
Definition mp' := mp_from_str "BHLJICNQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM276.


Module TM277.
Definition tm := TM_from_str "1LB0RA_1LC1LA_1LD1LE_1RC---_0LB1RF_1RB0RE".
Definition tm' := TM_from_str "1LB0RA_1LC1LA_1LD1LF_1RE---_1RB0RF_0LB1RE".
Definition tm0 := TM'_from_str "1LL0RA_1LD1RA_0LH1LL_1LH0RA_1LP1LH_1LT0RA_0LL0LD_1LL1LD_1RQ1LG_---1RQ_0LP0LT_1LP1LT_0RJ---_1RJ---_------_1RQ---_0LL0RV_0LD1RV_0LG1RF_1LG1RQ_0RF0RQ_1RF1RQ_1LT0LL_0RA0RV".
Definition tm0' := TM'_from_str "1LL0RA_1LD1RA_0LH1LL_1LH0RA_1LP1LH_1LX0RA_0LL0LD_1LL1LD_1RU1LG_---1RU_0LP0LX_1LP1LX_0RR---_1RR---_1RF---_1RU---_0RF0RU_1RF1RU_1LX0LL_0RA0RR_0LL0RR_0LD1RR_0LG1RF_1LG1RU".
Definition tm1 := TM'_from_str "0LB0RH_1LG1LC_1LD1RA_0LB0LE_1LI0RF_1LB0RF_1RA---_1RJ1RA_1LB1LE_1LC0RF".
Definition tm2 := TM'_from_str "0LB0RH_1LG1LC_1LD1RA_0LB0LE_1LI0RF_1LB0RF_1RA1RK_1RJ1RA_1LB1LE_1LC0RF_1RK1RK".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "QLTGDAPVHF".
Definition mp' := mp_from_str "ULXGDAPRHF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM277.


Module TM278.
Definition tm := TM_from_str "1LB0LD_0LC1LF_1RD---_0RE1RE_1LA1RD_1RD0RF".
Definition tm' := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA1RD_1RD0RF".
Definition tm0 := TM'_from_str "1LK1LH_1LX1LO_0LH0LO_1LH1LO_1RQ1RR_---0RU_0LK0LX_1LK1LX_0RN---_1RN---_1RQ---_1RR---_0RQ0RR_1RQ1RR_1LH1LO_0RN1RN_1LH0RN_1LO1RN_0LD1RQ_1LD1RR_0RN0RU_1RN1RU_1RQ0RN_1RR0RU".
Definition tm0' := TM'_from_str "1LK1LH_1LX1LD_0LH0LD_1LH1LD_1RQ1RR_---0RU_0LK0LX_1LK1LX_0RN---_1RN---_1RQ---_1RR---_0RQ0RR_1RQ1RR_1LH1LD_0RN1RN_1LH0RN_1LD1RN_0LD1RQ_1LD1RR_0RN0RU_1RN1RU_1RQ0RN_1RR0RU".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RA_1LH1LD_1RF0RE_0RA0RE_1LG1RA_1LC1LG_1RB---".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RA_1LH1LD_1RF0RE_0RA0RE_1LG1RA_1LC1LG_1RB1RI_1RI1RI".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "NQHXUROK".
Definition mp' := mp_from_str "NQHXURDK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM278.


Module TM279.
Definition tm := TM_from_str "1LB0LD_0LC1LC_1RD0RF_0RE1RE_1LA1RD_---0RC".
Definition tm' := TM_from_str "1LB1LA_0LC1LC_1RD0RF_0RE1RE_1LA1RD_---0RC".
Definition tm0 := TM'_from_str "1LK1LH_1LL1LO_0LH0LO_1LH1LO_1RQ1RR_---0RI_0LK0LL_1LK1LL_0RN0RU_1RN1RU_1RQ---_1RR0RI_0RQ0RR_1RQ1RR_1LH1LO_0RN1RN_1LH0RN_1LO1RN_0LD1RQ_1LD1RR_---0RI_---1RI_---0RN_---0RU".
Definition tm0' := TM'_from_str "1LK1LH_1LL1LD_0LH0LD_1LH1LD_1RQ1RR_---0RI_0LK0LL_1LK1LL_0RN0RU_1RN1RU_1RQ---_1RR0RI_0RQ0RR_1RQ1RR_1LH1LD_0RN1RN_1LH0RN_1LD1RN_0LD1RQ_1LD1RR_---0RI_---1RI_---0RN_---0RU".
Definition tm1 := TM'_from_str "1RB1RG_1LC0RA_1LI1LD_1RG0RE_0RA0RF_---0RE_1LH1RA_1LC1LH_1RB---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RA_1LI1LD_1RG0RE_0RA0RF_1RJ0RE_1LH1RA_1LC1LH_1RB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "NQHLIUROK".
Definition mp' := mp_from_str "NQHLIURDK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM279.


Module TM280.
Definition tm := TM_from_str "1LB0LD_0LC1LF_1RD---_0RE1RE_1LA0RB_1RD0RF".
Definition tm' := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA0RB_1RD0RF".
Definition tm0 := TM'_from_str "1LK1LH_1LX1LO_0LH0LO_1LH1LO_1RQ1RR_---0RU_0LK0LX_1LK1LX_0RN---_1RN---_1RQ---_1RR---_0RQ0RR_1RQ1RR_1LH1LO_0RE1RE_1LH0RE_1LO1RE_0LD1RQ_1LD1RR_0RN0RU_1RN1RU_1RQ0RN_1RR0RU".
Definition tm0' := TM'_from_str "1LK1LH_1LX1LD_0LH0LD_1LH1LD_1RQ1RR_---0RU_0LK0LX_1LK1LX_0RN---_1RN---_1RQ---_1RR---_0RQ0RR_1RQ1RR_1LH1LD_0RE1RE_1LH0RE_1LD1RE_0LD1RQ_1LD1RR_0RN0RU_1RN1RU_1RQ0RN_1RR0RU".
Definition tm1 := TM'_from_str "1RB1RG_1LC0RA_1LI1LD_1RG0RE_0RF0RE_1RB1RG_1LH1RA_1LC1LH_1RB---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RA_1LI1LD_1RG0RE_0RF0RE_1RB1RG_1LH1RA_1LC1LH_1RB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "EQHXUNROK".
Definition mp' := mp_from_str "EQHXUNRDK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM280.


Module TM281.
Definition tm := TM_from_str "1LB0LD_0LC1LC_1RD0RF_0RE1RE_1LA0RB_---0RC".
Definition tm' := TM_from_str "1LB1LA_0LC1LC_1RD0RF_0RE1RE_1LA0RB_---0RC".
Definition tm0 := TM'_from_str "1LK1LH_1LL1LO_0LH0LO_1LH1LO_1RQ1RR_---0RI_0LK0LL_1LK1LL_0RN0RU_1RN1RU_1RQ---_1RR0RI_0RQ0RR_1RQ1RR_1LH1LO_0RE1RE_1LH0RE_1LO1RE_0LD1RQ_1LD1RR_---0RI_---1RI_---0RN_---0RU".
Definition tm0' := TM'_from_str "1LK1LH_1LL1LD_0LH0LD_1LH1LD_1RQ1RR_---0RI_0LK0LL_1LK1LL_0RN0RU_1RN1RU_1RQ---_1RR0RI_0RQ0RR_1RQ1RR_1LH1LD_0RE1RE_1LH0RE_1LD1RE_0LD1RQ_1LD1RR_---0RI_---1RI_---0RN_---0RU".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_1LJ1LD_1RH0RE_0RG0RF_---0RE_1RB1RH_1LI1RA_1LC1LI_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_1LJ1LD_1RH0RE_0RG0RF_1RK0RE_1RB1RH_1LI1RA_1LC1LI_1RB1RK_1RK1RK".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "EQHLIUNROK".
Definition mp' := mp_from_str "EQHLIUNRDK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM281.


Module TM282.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0LD---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_1LC---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV1LK_1LD0LL_---1LL_1RF---_1LD---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU1LK_1LD0LL_---1LL_1LD---_1LK---_0LL---_1LL---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFKDNEQV".
Definition mp' := mp_from_str "BFKDNEQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM282.


Module TM283.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_1LC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF0LE_0LD---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU1LK_1LD0LL_---1LL_1LD---_1LK---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV0LS_1LD0LS_---1LS_1RF---_1LD---_0LO---_1LO---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFKDNEQU".
Definition mp' := mp_from_str "BFKDNEQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM283.


Module TM284.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF0LE_0LD---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF0LE_1LC---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV0LS_1LD0LS_---1LS_1RF---_1LD---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU0LS_1LD0LS_---1LS_1LD---_1LK---_0LL---_1LL---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFKDNEQV".
Definition mp' := mp_from_str "BFKDNEQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM284.


Module TM285.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF0LE_1LC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LF_1LA---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU0LS_1LD0LS_---1LS_1LD---_1LK---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV---_1LD0LX_---1LX_1RN---_1LD---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFKDNEQU".
Definition mp' := mp_from_str "BFKDNEQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM285.


Module TM286.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LF_1LA---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LA---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV---_1LD0LX_---1LX_1RN---_1LD---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV1LK_1LD0LL_---1LL_1RN---_1LD---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LD1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFKDNEQV".
Definition mp' := mp_from_str "BFKDNEQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM286.


Module TM287.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_1LB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LE---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU1LK_1LL0LL_---1LL_1LL---_1RE---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RV1LD_1RV1LK_1LL0LL_---1LL_------_1LL---_0LT---_1LT---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LI---_1LD1LC".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_0RH1LD_1LI1RJ_1LD1LC_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "BFKDNEQUL".
Definition mp' := mp_from_str "BFKDNEQVL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM287.


Module TM288.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_0RF0LD_1LC---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0LD---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RR0RN_0RU1RF_1RU1LD_1LD0LO_---1LO_1LD---_1LK---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LK1RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RR0RN_0RV1RF_1RV1LD_1LD0LO_---1LO_1RF---_1LD---_0LO---_1LO---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_1RH1LD_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_1RH1LD_1LD1RI_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "BFKDNERU".
Definition mp' := mp_from_str "BFKDNERV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM288.


Module TM289.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0LD---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LA---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RR0RN_0RV1RF_1RV1LD_1LD0LO_---1LO_1RF---_1LD---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LK1RV_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RR0RN_0RV1RF_1RV1LD_1LD0LO_---1LO_1RN---_1LD---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_1RH1LD_1LD---".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RE_0LD0LC_1RE1LD_1RA1RF_1LD0RE_1RH1LD_1LD1RI_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "BFKDNERV".
Definition mp' := mp_from_str "BFKDNERV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM289.


Module TM290.
Definition tm := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0RE_1RF1LD_1RB0RA".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LK---_1RR---_1RQ0RR_1LK1RR_0LL1RV_1LL1LS_0RN0LP_1RN0LK_0LP0LK_1RQ1LK_1RF0RQ_0LP1RQ_0LS0RV_1LS1LS_0RV1LS_1RV1LS_1RF0LP_1RA1LP_0RF0RA_1RF1RA_1LK0RF_1RR---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LK---_1RR---_1LP0RR_1LK1RR_0LL1RV_1LL1LS_1LS0LP_1LS0LK_0LP0LK_1LP1LK_1RF1RF_0LP0LP_0LS0LS_1LS1LS_0RV1LS_1RV1LS_1RF0LP_1RA1LP_0RF0RA_1RF1RA_1LK0RF_1RR---".
Definition tm1 := TM'_from_str "0RB---_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA".
Definition tm2 := TM'_from_str "0RB1RH_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA_1RH1RH".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "AFKPSRV".
Definition mp' := mp_from_str "AFKPSRV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM290.


Module TM291.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RE0LE_1RA1LD_1RB---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LK---_1RR---_1LP0RR_1LK1RR_0LL1RV_1LL1LS_1LS0LP_1LS0LK_0LP0LK_1LP1LK_1RF1RF_0LP0LP_0LS0LS_1LS1LS_0RV1LS_1RV1LS_1RF0LP_1RA1LP_0RF0RA_1RF1RA_1LK0RF_1RR---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LK0RF_1RR---_1LP0RR_1LK1RR_0LL1RB_1LL1LS_1LS0LP_1LS0LK_0LP0LK_1LP1LK_0RR1RF_1RR0LP_1RB0LS_1LS1LS_0RB1LS_1RB1LS_1RF0LP_1RU1LP_0RF---_1RF---_1LK---_1RR---".
Definition tm1 := TM'_from_str "0RB---_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA".
Definition tm2 := TM'_from_str "0RB1RH_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA_1RH1RH".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "AFKPSRV".
Definition mp' := mp_from_str "UFKPSRB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM291.


Module TM292.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RE0LE_1RA1LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LK0RF_1RR---_1LP0RR_1LK1RR_0LL1RB_1LL1LS_1LS0LP_1LS0LK_0LP0LK_1LP1LK_0RR1RF_1RR0LP_1RB0LS_1LS1LS_0RB1LS_1RB1LS_1RF0LP_1RU1LP_0RF---_1RF---_1LK---_1RR---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LK---_1RR---_0LP0RR_1LK1RR_0LL1RV_1LL1LS_0RN0LP_1RN0LK_0LP0LK_0LP1LK_1RF1RF_0LP0LP_0LS0LS_1LS1LS_0RV1LS_1RV1LS_1RF0LP_1RA1LP_0RF0RA_1RF1RA_1LK0RF_1RR---".
Definition tm1 := TM'_from_str "0RB---_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA".
Definition tm2 := TM'_from_str "0RB1RH_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA_1RH1RH".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "UFKPSRB".
Definition mp' := mp_from_str "AFKPSRV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM292.


Module TM293.
Definition tm := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0LE_1RF1LD_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LK---_1RR---_0LP0RR_1LK1RR_0LL1RV_1LL1LS_0RN0LP_1RN0LK_0LP0LK_0LP1LK_1RF1RF_0LP0LP_0LS0LS_1LS1LS_0RV1LS_1RV1LS_1RF0LP_1RA1LP_0RF0RA_1RF1RA_1LK0RF_1RR---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LK0RF_1RR---_1LP0RR_1LK1RR_0LL1RB_1LL1LS_1LS0LP_1LS0LK_0LP0LK_1LP1LK_1RF0RQ_0LP1RQ_0LS0RB_1LS1LS_0RB1LS_1RB1LS_1RF0LP_1RU1LP_0RF---_1RF---_1LK---_1RR---".
Definition tm1 := TM'_from_str "0RB---_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA".
Definition tm2 := TM'_from_str "0RB1RH_1LC1RF_0LD0LC_1LE1LE_1RB0LD_1RG1LE_1RB1RA_1RH1RH".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "AFKPSRV".
Definition mp' := mp_from_str "UFKPSRB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM293.


Module TM294.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1LA---".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RB1RB_---1RQ_0RB---_1RB---_1RF---_1RB---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RB1RB_---1RQ_1LH---_1RB---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "FKBHLQNV".
Definition mp' := mp_from_str "FKBHLQNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM294.


Module TM295.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA1LF_0RB---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1RE---".
Definition tm0 := TM'_from_str "0RJ0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LX_0RB0LS_0RJ1LS_0RB0RJ_1RE1RJ_0LP1RE_1LP1RJ_0RM0RB_1RM1RB_0RM1LS_0RB1RE_1LH0LD_0LD---_0LD0LX_1LD1LX_0RE---_1RE---_0RI---_0LD---".
Definition tm0' := TM'_from_str "0RJ0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LS_0RJ1LS_0RB0RJ_1RE1RJ_0LP1RE_1LP1RJ_0RM0RB_1RM1RB_0RM1LS_0RB1RE_1LH0LD_0LD---_0LD0LW_1LD1LW_0RR---_1RR---_0LD---".
Definition tm1 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---".
Definition tm2 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "JEIBSDHX".
Definition mp' := mp_from_str "JEIBSDHW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM295.


Module TM296.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1RE---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA1LF_0RB---".
Definition tm0 := TM'_from_str "0RJ0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LS_0RJ1LS_0RB0RJ_1RE1RJ_0LP1RE_1LP1RJ_0RM0RB_1RM1RB_0RM1LS_0RB1RE_1LH0LD_0LD---_0LD0LW_1LD1LW_0RR---_1RR---_0LD---".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LX_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RN_0RE0RN_1RE1RN_0RI1RE_0LD1RN_1LH0LD_0LD---_0LD0LX_1LD1LX_0RE---_1RE---_0RI---_0LD---".
Definition tm1 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---".
Definition tm2 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "JEIBSDHW".
Definition mp' := mp_from_str "NEIBSDHX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM296.


Module TM297.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA1LF_0RB---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1LA---".
Definition tm0 := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LX_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RN_0RE0RN_1RE1RN_0RI1RE_0LD1RN_1LH0LD_0LD---_0LD0LX_1LD1LX_0RE---_1RE---_0RI---_0LD---".
Definition tm0' := TM'_from_str "0RJ0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LS_0RJ1LS_0RB0RJ_1RE1RJ_0LP1RE_1LP1RJ_0RM0RB_1RM1RB_0RM1LS_0RB1RE_1LH0LD_0LD---_0LD0LW_1LD1LW_1LH---_0LD---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---".
Definition tm2 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBSDHX".
Definition mp' := mp_from_str "JEIBSDHW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM297.


Module TM298.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1LD1RC_0RD1RA_1LA0LF_1LA---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA0LF_1RE---".
Definition tm0 := TM'_from_str "0RJ0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LS_0RJ1LS_0RB0RJ_1RE1RJ_0LP1RE_1LP1RJ_0RM0RB_1RM1RB_0RM1LS_0RB1RE_1LH0LD_0LD---_0LD0LW_1LD1LW_1LH---_0LD---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RN_0RE0RN_1RE1RN_0RI1RE_0LD1RN_1LH0LD_0LD---_0LD0LW_1LD1LW_0RR---_1RR---_0LD---".
Definition tm1 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---".
Definition tm2 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "JEIBSDHW".
Definition mp' := mp_from_str "NEIBSDHW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM298.


Module TM299.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA0LF_1RE---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RD_1LA0LF_1LA---".
Definition tm0 := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RN_0RE0RN_1RE1RN_0RI1RE_0LD1RN_1LH0LD_0LD---_0LD0LW_1LD1LW_0RR---_1RR---_0LD---".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RN_0RE0RN_1RE1RN_0RI1RE_0LD1RN_1LH0LD_0LD---_0LD0LW_1LD1LW_1LH---_0LD---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---".
Definition tm2 := TM'_from_str "1RB1RA_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBSDHW".
Definition mp' := mp_from_str "NEIBSDHW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM299.


Module TM300.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB0RF_1LA0LE_1LC---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA0LE_0RB---".
Definition tm0 := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LS_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RU_0RE0RU_1RE1RU_0RI1RE_0LD---_1LH0LD_0LD0LS_0LD0LS_1LD1LS_1RE---_1RU---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LS_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD0LS_0LD0LS_1LD1LS_0RE---_1RE---_0RI---_0LD---".
Definition tm1 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBSDHU".
Definition mp' := mp_from_str "NEIBSDHV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM300.


Module TM301.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA0LE_0RB---".
Definition tm' := TM_from_str "1LB0RB_0RC0LF_1RA1RD_0LD1RE_0RB---_1LA0LF".
Definition tm0 := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LS_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD0LS_0LD0LS_1LD1LS_0RE---_1RE---_0RI---_0LD---".
Definition tm0' := TM'_from_str "0RN0RE_1LW1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LW_0RN1LW_0RB0RN_1RB1RN_1LW1RE_1RE1RR_0LO0RR_1RE1RR_0LO1RE_1LO---_0RE---_1RE---_0RI---_0LD---_1LH0LD_0LD0LW_0LD0LW_1LD1LW".
Definition tm1 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBSDHV".
Definition mp' := mp_from_str "NEIBWDHR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM301.


Module TM302.
Definition tm := TM_from_str "1LB0RB_0RC0LF_1RA1RD_0LD1RE_0RB---_1LA0LF".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA0LE_0LC---".
Definition tm0 := TM'_from_str "0RN0RE_1LW1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LW_0RB0LW_0RN1LW_0RB0RN_1RB1RN_1LW1RE_1RE1RR_0LO0RR_1RE1RR_0LO1RE_1LO---_0RE---_1RE---_0RI---_0LD---_1LH0LD_0LD0LW_0LD0LW_1LD1LW".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LS_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD0LS_0LD0LS_1LD1LS_1LS---_1RE---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBWDHR".
Definition mp' := mp_from_str "NEIBSDHV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM302.


Module TM303.
Definition tm := TM_from_str "1LB0RB_0RC0LF_1RA1RD_0LD1RE_0RB---_1LA1LE".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LD_0LC---".
Definition tm0 := TM'_from_str "0RN0RE_1LW1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LT_0RB0LW_0RN1LW_0RB0RN_1RB1RN_1LW1RE_1RE1RR_0LO0RR_1RE1RR_0LO1RE_1LO---_0RE---_1RE---_0RI---_0LD---_1LH0LD_0LD---_0LD0LT_1LD1LT".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LP_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD---_0LD0LP_1LD1LP_1LS---_1RE---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---_1RB---".
Definition tm2 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RJ_1RB1RJ_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBWDHTR".
Definition mp' := mp_from_str "NEIBSDHPV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM303.


Module TM304.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LD_0LC---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LF_0RB---".
Definition tm0 := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LP_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD---_0LD0LP_1LD1LP_1LS---_1RE---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LX_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD---_0LD0LX_1LD1LX_0RE---_1RE---_0RI---_0LD---".
Definition tm1 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---_1RB---".
Definition tm2 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RJ_1RB1RJ_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBSDHPV".
Definition mp' := mp_from_str "NEIBSDHXV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM304.


Module TM305.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LF_0RB---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LD_0RB---".
Definition tm0 := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LX_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD---_0LD0LX_1LD1LX_0RE---_1RE---_0RI---_0LD---".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LP_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD---_0LD0LP_1LD1LP_0RE---_1RE---_0RI---_0LD---".
Definition tm1 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---_1RB---".
Definition tm2 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RJ_1RB1RJ_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBSDHXV".
Definition mp' := mp_from_str "NEIBSDHPV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM305.


Module TM306.
Definition tm := TM_from_str "1RB1RC_1LA---_0RE1LD_1RF0LC_1RA1RF_1RE0LF".
Definition tm' := TM_from_str "1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_1LK1RQ_---1LK_------_1LK---_0LD---_1LD---_0RQ0LW_1RQ1LK_0RB0LP_0RV1LP_0RV0RB_1RV0LP_1RR0LK_0LW1LK_0RB0RV_1RB1RV_1RF1RR_1RJ0LW_0RR1RB_1RR0LW_1RB0LW_1RV1LW".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_---1LO_0LW---_1LO---_0LL---_1LL---_0RV0RB_1RV0LL_1RR0LO_0LW1LO_0RQ0LW_1RQ1LO_0RB0LL_0RV1LL_0RB0RV_1RB1RV_1RF1RR_1RN0LW_0RR1RB_1RR0LW_1RB0LW_1RV1LW".
Definition tm1 := TM'_from_str "0RB0RH_1RC1RG_1LD---_0RB0LE_0LF1LD_1RB0LF_1RA1LD_1RI0LF_1RB1RH".
Definition tm2 := TM'_from_str "0RB0RH_1RC1RG_1LD1RJ_0RB0LE_0LF1LD_1RB0LF_1RA1LD_1RI0LF_1RB1RH_1RJ1RJ".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "QBFKPWJVR".
Definition mp' := mp_from_str "QBFOLWNVR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM306.


Module TM307.
Definition tm := TM_from_str "1RB1RE_1RC1LD_0RD0RC_1LE0LF_1LB---_1RC0LA".
Definition tm' := TM_from_str "1RB1RE_1RC0LA_0RD0RC_1LE0LB_1LF---_1RC1LD".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1RJ1LP_1LW---_0RJ1LT_1RJ1LW_1RM0LP_1RI1LP_0RM0RI_1RM1RI_1LH0RM_1RM0RI_1LH1RM_---0LC_0LT0LW_1LT1LW_1RI---_1LP---_0LH---_1LH---_0RJ1RJ_1RJ1LP_1RM0LC_1RI1LC".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1RJ1LP_1LP---_0RJ1RJ_1RJ1LP_1RM0LC_1RI1LC_0RM0RI_1RM1RI_1LX0RM_1RM0RI_1LX1RM_---0LC_0LT0LG_1LT1LG_1RI---_1LP---_0LX---_1LX---_0RJ1LT_1RJ1LG_1RM0LP_1RI1LP".
Definition tm1 := TM'_from_str "1LB1RA_1RH1LC_1LG1LD_1RA0LE_1RF1LC_1RA1RH_1LB---_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1RH1LC_1LG1LD_1RA0LE_1RF1LC_1RA1RH_1LB1RI_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "MHPWCJTI".
Definition mp' := mp_from_str "MXPGCJTI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM307.


Module TM308.
Definition tm := TM_from_str "1LB1RD_1RC---_1LE0LA_1RC0RD_1RD1LF_1LC0LE".
Definition tm' := TM_from_str "1LB1RB_1RC---_1LD0LA_1RF1LE_1LC0LD_1RC0RF".
Definition tm0 := TM'_from_str "1RJ0RN_---1RN_0LH1RJ_1LH1RM_0RJ---_1RJ---_1LX---_1RJ---_1RM0LH_1LX1RJ_0LT0LC_1LT1LC_0RJ0RM_1RJ1RM_1LX0RJ_1RJ0RM_0RN1LL_1RN1LS_1RJ0LX_1RM1LX_1LT1RJ_1LC0LX_0LL0LS_1LL1LS".
Definition tm0' := TM'_from_str "1RJ0RF_---1RF_0LH1RJ_1LH---_0RJ---_1RJ---_1LT---_1RJ---_1RU0LH_1LT1RJ_0LP0LC_1LP1LC_0RV1LL_1RV1LO_1RJ0LT_1RU1LT_1LP1RJ_1LC0LT_0LL0LO_1LL1LO_0RJ0RU_1RJ1RU_1LT0RJ_1RJ0RU".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JXSLTMCH".
Definition mp' := mp_from_str "JTOLPUCH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM308.


Module TM309.
Definition tm := TM_from_str "1RB1RC_0LC1LF_0RF1RD_0LE---_1RA0LC_1LD0RA".
Definition tm' := TM_from_str "1RB1RD_0LC1LE_1RA0LD_0RE1RF_1LB0RA_0LC---".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_0LK1RU_0RJ1RN_1LS1LP_0LK0RJ_0LK0LX_1LK1LX_0RU0RN_1RU1RN_1LS0LK_0RA---_1RF---_0LK---_0LS---_1LS---_0RB1LS_1RB0LK_1RF0LK_1RJ1LK_1LS0RA_---1RA_0LP0RF_1LP0RJ".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_0LO1RQ_0RN1RV_1RF1LH_0LO0RN_0LK0LT_1LK1LT_0RB1LK_1RB0LO_1RF0LO_1RN1LO_0RQ0RV_1RQ1RV_1LK0LO_0RA---_1LK0RA_1LT1RA_0LH0RF_1LH0RN_1RF---_0LO---_0LK---_1LK---".
Definition tm1 := TM'_from_str "0RB0RE_0LC0RE_1LD0LC_1RB0LC_1RF1RG_1LD0RA_0LC---".
Definition tm2 := TM'_from_str "0RB0RE_0LC0RE_1LD0LC_1RB0LC_1RF1RG_1LD0RA_0LC1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "AFKSJUN".
Definition mp' := mp_from_str "AFOKNQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM309.


Module TM310.
Definition tm := TM_from_str "1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_0LA---".
Definition tm' := TM_from_str "1RB0RE_0RC0RA_1LD1RF_1LA0LD_1RA0LC_0RC---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RI0RB_1RA0LP_0RI0RA_1RI1RA_1LD0RF_0RU0RQ_1LD0RU_1LO1RU_0LP1RI_1LP---_1RA0LD_0LP0LO_0LD0LO_1LD1LO_0RB0LP_1RB1RI_1RF0LK_1RQ1LK_1RI---_0RB---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RI0RB_1RA0LP_0RI0RA_1RI1RA_1LD0RF_0RV0RQ_1LD0RV_1LO1RV_0LP1RI_1LP---_1RA0LD_0LP0LO_0LD0LO_1LD1LO_0RB0LP_1RB1RI_1RF0LK_1RQ1LK_0RI---_1RI---_1LD---_0RV---".
Definition tm1 := TM'_from_str "0RB0RH_1RC1RA_1LD0RG_1RA0LE_1LD1LF_0LD0LF_1RC---_0RI0LE_1RB1RH".
Definition tm2 := TM'_from_str "0RB0RH_1RC1RA_1LD0RG_1RA0LE_1LD1LF_0LD0LF_1RC1RJ_0RI0LE_1RB1RH_1RJ1RJ".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "AFIDPOUQB".
Definition mp' := mp_from_str "AFIDPOVQB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM310.


Module TM311.
Definition tm := TM_from_str "1RB0RE_0RC0RA_1LD1RF_1LA0LD_1RA0LC_0RC---".
Definition tm' := TM_from_str "1RB0RF_0LC0RA_1LE1RD_0RC---_1LA0LE_1RA0LC".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RI0RB_1RA0LP_0RI0RA_1RI1RA_1LD0RF_0RV0RQ_1LD0RV_1LO1RV_0LP1RI_1LP---_1RA0LD_0LP0LO_0LD0LO_1LD1LO_0RB0LP_1RB1RI_1RF0LK_1RQ1LK_0RI---_1RI---_1LD---_0RV---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1RI0RB_1RA0LT_0LT0RA_1RI1RA_0LK0RF_1LK0RU_1LD0RN_1LS1RN_0LT1RI_1LT---_0RI---_1RI---_1LD---_0RN---_1RA0LD_0LT0LS_0LD0LS_1LD1LS_0RB0LT_1RB1RI_1RF0LK_1RU1LK".
Definition tm1 := TM'_from_str "0RB0RH_1RC1RA_1LD0RG_1RA0LE_1LD1LF_0LD0LF_1RC---_0RI0LE_1RB1RH".
Definition tm2 := TM'_from_str "0RB0RH_1RC1RA_1LD0RG_1RA0LE_1LD1LF_0LD0LF_1RC1RJ_0RI0LE_1RB1RH_1RJ1RJ".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "AFIDPOVQB".
Definition mp' := mp_from_str "AFIDTSNUB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM311.


Module TM312.
Definition tm := TM_from_str "1RB0RE_0RC0RA_1LD1RF_1LA0LD_1RA0LC_1RA---".
Definition tm' := TM_from_str "1RB0RE_0RC0RA_1LD1RE_1LA0LD_1RA0LF_1LD---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RI0RB_1RA0LP_0RI0RA_1RI1RA_1LD0RF_0RV0RQ_1LD0RV_1LO1RV_0LP1RB_1LP---_1RA0LD_0LP0LO_0LD0LO_1LD1LO_0RB0LP_1RB1RB_1RF0LK_1RQ1LK_0RB---_1RB---_1RF---_1RQ---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RI0RB_1RA0LP_0RI0RA_1RI1RA_1LD0RF_0RR0RQ_1LD0RR_1LO1RR_0LP1RB_1LP---_1RA0LD_0LP0LO_0LD0LO_1LD1LO_0RB0LP_1RB---_1RF0LW_1RQ1LW_1LD---_1LO---_0LP---_1LP---".
Definition tm1 := TM'_from_str "0RB0RI_1RC1RA_1LD0RG_1RA0LE_1LD1LF_0LD0LF_1RH---_1RB1RI_0RH0LE".
Definition tm2 := TM'_from_str "0RB0RI_1RC1RA_1LD0RG_1RA0LE_1LD1LF_0LD0LF_1RH1RJ_1RB1RI_0RH0LE_1RJ1RJ".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "AFIDPOVBQ".
Definition mp' := mp_from_str "AFIDPORBQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM312.


Module TM313.
Definition tm := TM_from_str "1LB1LC_1RC0LA_1LA0RD_1RC0RE_0LE0LF_0RB---".
Definition tm' := TM_from_str "1LB1LC_1RC0LA_1LA0RD_1RC0RE_0LE0LF_0RD---".
Definition tm0 := TM'_from_str "1RM1LD_1LC0RQ_0LH0LL_1LH1LL_0RJ0LH_1RJ0LL_1LL0LC_1RM1LC_1LH0RM_1LL1RM_0LD0RJ_1LD0RQ_0RJ0RQ_1RJ1RQ_1LL0LS_1RM0RJ_0LS0RJ_0LW---_0LS0LW_1LS1LW_0RE---_1RE---_0RJ---_0LH---".
Definition tm0' := TM'_from_str "1RM1LD_1LC0RQ_0LH0LL_1LH1LL_0RJ0LH_1RJ0LL_1LL0LC_1RM1LC_1LH0RM_1LL1RM_0LD0RJ_1LD0RQ_0RJ0RQ_1RJ1RQ_1LL0LS_1RM0RJ_0LS0RJ_0LW---_0LS0LW_1LS1LW_0RM---_1RM---_0RJ---_0RQ---".
Definition tm1 := TM'_from_str "1LB1RF_1LC0RG_1LD1LB_1RF1LE_0LD0LB_0RA0RG_0LH0RA_0LH0LI_0RA---".
Definition tm2 := TM'_from_str "1LB1RF_1LC0RG_1LD1LB_1RF1LE_0LD0LB_0RA0RG_0LH0RA_0LH0LI_0RA1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;0;1;0]%N.
Definition mp := mp_from_str "JLDHCMQSW".
Definition mp' := mp_from_str "JLDHCMQSW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM313.


Module TM314.
Definition tm := TM_from_str "1LB1LC_1RC0LA_1LA0RD_1RC0RE_0LE0LF_0RD---".
Definition tm' := TM_from_str "1LB1LC_1RC0LA_1LA0RD_0LE0RF_0RB---_0LF0LE".
Definition tm0 := TM'_from_str "1RM1LD_1LC0RQ_0LH0LL_1LH1LL_0RJ0LH_1RJ0LL_1LL0LC_1RM1LC_1LH0RM_1LL1RM_0LD0RJ_1LD0RQ_0RJ0RQ_1RJ1RQ_1LL0LS_1RM0RJ_0LS0RJ_0LW---_0LS0LW_1LS1LW_0RM---_1RM---_0RJ---_0RQ---".
Definition tm0' := TM'_from_str "1RM1LD_1LC0RU_0LH0LL_1LH1LL_0RJ0LH_1RJ0LL_1LL0LC_1RM1LC_1LH0RM_1LL1RM_0LD0RJ_1LD0RU_0RJ0RU_---1RU_0LS0LW_1LS0RJ_0RE---_1RE---_0RJ---_0LH---_0LW0RJ_0LS---_0LW0LS_1LW1LS".
Definition tm1 := TM'_from_str "1LB1RF_1LC0RG_1LD1LB_1RF1LE_0LD0LB_0RA0RG_0LH0RA_0LH0LI_0RA---".
Definition tm2 := TM'_from_str "1LB1RF_1LC0RG_1LD1LB_1RF1LE_0LD0LB_0RA0RG_0LH0RA_0LH0LI_0RA1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;0;1;0]%N.
Definition mp := mp_from_str "JLDHCMQSW".
Definition mp' := mp_from_str "JLDHCMUWS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM314.


Module TM315.
Definition tm := TM_from_str "1RB1LC_0LC1RE_1RD1LD_1LA0LC_0RF0RA_---0RE".
Definition tm' := TM_from_str "1RB1LD_1LC1RC_0RF0RA_1RE1LE_1LA0LD_---0RC".
Definition tm0 := TM'_from_str "0RF0LP_1RF1LP_0LP0LL_1RR1LL_1LL0RR_0LP1RR_0LK1RU_1LK1RA_0RN1LD_1RN1LK_1LL0LP_0LP1LP_1RR1LL_1LL0LP_0LD0LK_1LD1LK_0RU0RA_1RU1RA_---0RF_0RQ0LP_---0RQ_---1RQ_---0RU_---0RA".
Definition tm0' := TM'_from_str "0RF0LT_1RF1LT_0LT0LP_1RJ1LP_0RI0RJ_0LT1RJ_0LL1RU_1LL1RA_0RU0RA_1RU1RA_---0RF_0RI0LT_0RR1LD_1RR1LO_1LP0LT_0LT1LT_1RJ1LP_1LP0LT_0LD0LO_1LD1LO_---0RI_---1RI_---0RU_---0RA".
Definition tm1 := TM'_from_str "0LB1RD_1LC1LG_1RD1LF_1RH1RE_0RA0LB_0LB1LB_1LF0LB_---0RI_0RH0RE".
Definition tm2 := TM'_from_str "0LB1RD_1LC1LG_1RD1LF_1RH1RE_0RA0LB_0LB1LB_1LF0LB_1RJ0RI_0RH0RE_1RJ1RJ".
Definition l0 := [1;1;0;1;1;0;0;0]%N.
Definition mp := mp_from_str "FPDRALKUQ".
Definition mp' := mp_from_str "FTDJAPOUI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM315.


Module TM316.
Definition tm := TM_from_str "1RB1LD_1RC1RF_1RD0LB_0LE1LA_---1LA_0RB1RC".
Definition tm' := TM_from_str "1RB1LD_1RC0RF_1RD0RB_0LE1LA_---1LA_1LB0LA".
Definition tm0 := TM'_from_str "0RF1LS_1RF1LD_1RJ0LP_1RV1LP_0RJ0RV_1RJ1RV_1RN1RE_1RE1RJ_0RN1RN_1RN1RE_0LD0LG_1LP1LG_---1RV_0LD1LP_0LS0LD_1LS1LD_---1RV_---1LP_---0LD_---1LD_0RE0RJ_1RE1RJ_0RJ1RN_0RV1RE".
Definition tm0' := TM'_from_str "0RF1LS_1RF1LD_1RJ0LP_1RU1LP_0RJ0RU_1RJ1RU_1RN1RE_1RE1RJ_0RN0RE_1RN1RE_0LD0RJ_1LP0RU_---1RU_0LD1LP_0LS0LD_1LS1LD_---1RU_---1LP_---0LD_---1LD_1RE1RJ_1RJ0LP_0LH0LC_1LH1LC".
Definition tm1 := TM'_from_str "1RB1RG_0LC1LD_1RF1LD_1LE1LC_---0LC_1RG1RA_0RA0RF".
Definition tm2 := TM'_from_str "1RB1RG_0LC1LD_1RF1LD_1LE1LC_1RH0LC_1RG1RA_0RA0RF_1RH1RH".
Definition l0 := [1;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JNDPSVE".
Definition mp' := mp_from_str "JNDPSUE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM316.


Module TM317.
Definition tm := TM_from_str "1RB1LD_1RC0RF_1RD0RB_0LE1LA_---1LA_1LB0LA".
Definition tm' := TM_from_str "1RB1LD_1RC1RF_1RD0RB_0LE1LA_---1LA_0RB1RC".
Definition tm0 := TM'_from_str "0RF1LS_1RF1LD_1RJ0LP_1RU1LP_0RJ0RU_1RJ1RU_1RN1RE_1RE1RJ_0RN0RE_1RN1RE_0LD0RJ_1LP0RU_---1RU_0LD1LP_0LS0LD_1LS1LD_---1RU_---1LP_---0LD_---1LD_1RE1RJ_1RJ0LP_0LH0LC_1LH1LC".
Definition tm0' := TM'_from_str "0RF1LS_1RF1LD_1RJ0LP_1RV1LP_0RJ0RV_1RJ1RV_1RN1RE_1RE1RJ_0RN0RE_1RN1RE_0LD0RJ_1LP0RV_---1RV_0LD1LP_0LS0LD_1LS1LD_---1RV_---1LP_---0LD_---1LD_0RE0RJ_1RE1RJ_0RJ1RN_0RV1RE".
Definition tm1 := TM'_from_str "1RB1RG_0LC1LD_1RF1LD_1LE1LC_---0LC_1RG1RA_0RA0RF".
Definition tm2 := TM'_from_str "1RB1RG_0LC1LD_1RF1LD_1LE1LC_1RH0LC_1RG1RA_0RA0RF_1RH1RH".
Definition l0 := [1;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JNDPSUE".
Definition mp' := mp_from_str "JNDPSVE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM317.


Module TM318.
Definition tm := TM_from_str "1RB1LD_1RC1RF_1RD0RB_0LE1LA_---1LA_0RB1RC".
Definition tm' := TM_from_str "1RB1LD_1RC1RF_1RD0RB_0LE1LA_---1LA_1LF1RC".
Definition tm0 := TM'_from_str "0RF1LS_1RF1LD_1RJ0LP_1RV1LP_0RJ0RV_1RJ1RV_1RN1RE_1RE1RJ_0RN0RE_1RN1RE_0LD0RJ_1LP0RV_---1RV_0LD1LP_0LS0LD_1LS1LD_---1RV_---1LP_---0LD_---1LD_0RE0RJ_1RE1RJ_0RJ1RN_0RV1RE".
Definition tm0' := TM'_from_str "0RF1LS_1RF1LD_1RJ0LP_1RV1LP_0RJ0RV_1RJ1RV_1RN1RE_1RE1RJ_0RN0RE_1RN1RE_0LD0RJ_1LP0RV_---1RV_0LD1LP_0LS0LD_1LS1LD_---1RV_---1LP_---0LD_---1LD_1LX0RJ_1RE1RJ_0LX1RN_1LX1RE".
Definition tm1 := TM'_from_str "1RB1RG_0LC1LD_1RF1LD_1LE1LC_---0LC_1RG1RA_0RA0RF".
Definition tm2 := TM'_from_str "1RB1RG_0LC1LD_1RF1LD_1LE1LC_1RH0LC_1RG1RA_0RA0RF_1RH1RH".
Definition l0 := [1;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JNDPSVE".
Definition mp' := mp_from_str "JNDPSVE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM318.


Module TM319.
Definition tm := TM_from_str "1RB1LE_0RC1LE_0RD1LC_1LD0LA_---1LF_1RB0LF".
Definition tm' := TM_from_str "1RB1LE_0RC1LE_0RD0LA_1LD0LA_---1LF_1RB0LF".
Definition tm0 := TM'_from_str "0RF---_1RF1LX_1RI0LT_1LX1LT_0RI---_1RI1LX_0RM0LT_1RI1LT_0RM1RI_1RM1LL_1LP0LL_1RI1LL_1LP1RI_1LC0LT_0LP0LC_1LP1LC_---1LX_---1LW_---0LX_---1LX_0RF1RI_1RF0LW_1RI0LW_1LX1LW".
Definition tm0' := TM'_from_str "0RF---_1RF1LX_1RI0LT_1LX1LT_0RI---_1RI1LX_0RM0LT_1RI1LT_0RM1RI_1RM0LT_1LP0LC_1RI1LC_1LP1RI_1LC0LT_0LP0LC_1LP1LC_---1LX_---1LW_---0LX_---1LX_0RF1RI_1RF0LW_1RI0LW_1LX1LW".
Definition tm1 := TM'_from_str "1LB1RG_1LB1LC_1RG0LD_---1LE_1LE1LF_1RG0LF_0RA1RG".
Definition tm2 := TM'_from_str "1LB1RG_1LB1LC_1RG0LD_1RH1LE_1LE1LF_1RG0LF_0RA1RG_1RH1RH".
Definition l0 := [1;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "MPCTXWI".
Definition mp' := mp_from_str "MPCTXWI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM319.


Module TM320.
Definition tm := TM_from_str "1RB1LE_0RC1LE_0RD0LA_1LD0LA_---1LF_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA".
Definition tm0 := TM'_from_str "0RF---_1RF1LX_1RI0LT_1LX1LT_0RI---_1RI1LX_0RM0LT_1RI1LT_0RM1RI_1RM0LT_1LP0LC_1RI1LC_1LP1RI_1LC0LT_0LP0LC_1LP1LC_---1LX_---1LW_---0LX_---1LX_0RF1RI_1RF0LW_1RI0LW_1LX1LW".
Definition tm0' := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1LD1LC_0RI---_1RI1LD_0RM0LX_1RI1LX_0RM1RI_1RM0LC_1LP0LC_1RI1LC_1LP1RI_1LS0LX_0LP0LS_1LP1LS_0RF---_1RF1LD_1RI0LX_1LD1LX_---1LD_---1LC_---0LD_---1LD".
Definition tm1 := TM'_from_str "1LB1RG_1LB1LC_1RG0LD_---1LE_1LE1LF_1RG0LF_0RA1RG".
Definition tm2 := TM'_from_str "1LB1RG_1LB1LC_1RG0LD_1RH1LE_1LE1LF_1RG0LF_0RA1RG_1RH1RH".
Definition l0 := [1;1;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "MPCTXWI".
Definition mp' := mp_from_str "MPSXDCI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM320.


Module TM321.
Definition tm := TM_from_str "1RB0LD_1RC0RF_0RD1RA_1LE0RB_0LA0RA_0LD---".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_0RD1RA_1LE0RB_0LA0RA_1LE---".
Definition tm0 := TM'_from_str "0RF0LT_1RF0RJ_1RJ0LO_1RU1LO_0RJ0RU_1RJ1RU_1RM0LT_1RB---_0RM0RB_1RM1RB_1LC1RF_0RE0RJ_1LC0RE_0LT1RE_0LT0RJ_1LT0RU_1RJ0RA_0LO1RA_0LC0RF_1LC0LT_0LT---_0RJ---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF0LT_1RF0RJ_1RJ0LO_1RV1LO_0RJ0RV_1RJ1RV_1RM0LT_1RB---_0RM0RB_1RM1RB_1LC1RF_0RE0RJ_1LC0RE_0LT1RE_0LT0RJ_1LT0RV_1RJ0RA_0LO1RA_0LC0RF_1LC0LT_1LC---_0LT---_0LT---_1LT---".
Definition tm1 := TM'_from_str "1RB0RC_1RC1RI_1RD1RA_1LE0RG_1RC0LF_0LH0RC_0RC0RI_1LE0LH_0LH---".
Definition tm2 := TM'_from_str "1RB0RC_1RC1RI_1RD1RA_1LE0RG_1RC0LF_0LH0RC_0RC0RI_1LE0LH_0LH1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "BFJMCOETU".
Definition mp' := mp_from_str "BFJMCOETV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM321.


Module TM322.
Definition tm := TM_from_str "1LB1RE_1LC1LA_0RD0RB_1RB1RD_1LF0RA_---0LE".
Definition tm' := TM_from_str "1LB1RE_1LC1LA_0RD1LB_1RB1RD_1LF0RA_---0LE".
Definition tm0 := TM'_from_str "1LL0RR_1LD1RR_0LH1LS_1LH1RA_0RN1LH_1LH1RA_0LL0LD_1LL1LD_0RM0RE_1RM1RE_0RF0RN_0RN1LH_0RF0RN_1RF1RN_1LH1RF_1RA1RN_---0RA_1LS1RA_0LX1LL_1LX0RR_---0LX_---1LL_---0LS_---1LS".
Definition tm0' := TM'_from_str "1LL0RR_1LD1RR_0LH1LS_1LH1RA_0RN1LH_1LH1RA_0LL0LD_1LL1LD_0RM1LL_1RM1LD_0RF0LH_0RN1LH_0RF0RN_1RF1RN_1LH1RF_1RA1RN_---0RA_1LS1RA_0LX1LL_1LX0RR_---0LX_---1LL_---0LS_---1LS".
Definition tm1 := TM'_from_str "1LB0RE_0RH1LC_1LB1LD_1LC1RA_1LF1RA_0LG1LB_---1LF_1RI1RH_1LC1RA".
Definition tm2 := TM'_from_str "1LB0RE_0RH1LC_1LB1LD_1LC1RA_1LF1RA_0LG1LB_1RJ1LF_1RI1RH_1LC1RA_1RJ1RJ".
Definition l0 := [0;1;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "ALHDRSXNF".
Definition mp' := mp_from_str "ALHDRSXNF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM322.


Module TM323.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF0RE_0RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RB---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1RJ0RQ_---1RQ_0LX1RJ_1LX0RQ_0RM---_1RM---_1LD---_1RJ---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1RJ0RF_---1RF_0LW1RJ_1LW1RE_0RF---_1RF---_1RJ---_1RE---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESX".
Definition mp' := mp_from_str "JPCLDESW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM323.


Module TM324.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_0LA0RF".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1RJ0RF_---1RF_0LW1RJ_1LW1RE_0RF---_1RF---_1RJ---_1RE---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RJ---_1RE---_0RJ0RE_1RJ1RE_1LT0RJ_1RJ0RE_1RE0LC_1LT1RJ_0LP0LW_1LP1LW_0RF1LL_1RF1LO_1RJ0LT_1RE1LT_1LP1RJ_1LW0LT_0LL0LO_1LL1LO_1RJ0RU_---1RU_0LC1RJ_1LC0RU".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESW".
Definition mp' := mp_from_str "JTOLPEWC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM324.


Module TM325.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_0LA0RF".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RD---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RJ---_1RE---_0RJ0RE_1RJ1RE_1LT0RJ_1RJ0RE_1RE0LC_1LT1RJ_0LP0LW_1LP1LW_0RF1LL_1RF1LO_1RJ0LT_1RE1LT_1LP1RJ_1LW0LT_0LL0LO_1LL1LO_1RJ0RU_---1RU_0LC1RJ_1LC0RU".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1RJ0RF_---1RF_0LX1RJ_1LX1RE_0RM---_1RM---_1LD---_1RJ---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JTOLPEWC".
Definition mp' := mp_from_str "JPCLDESX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM325.


Module TM326.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1LD---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_0LP0RF_---1RF_0LX1RJ_1LX1RE_0RN---_1RN---_1LS---_0LP---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_0LP0RF_---1RF_0LW1RJ_1LW1RE_1LL---_1LC---_0LP---_1LP---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_0LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_0LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESX".
Definition mp' := mp_from_str "JPCLDESW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM326.


Module TM327.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RF_1RC---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LP0RF_---1RF_0LW1RJ_1LW1RE_0RJ---_1RJ---_1LP---_1RJ---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LP0RV_---1RV_0LW1RJ_1LW---_0RJ---_1RJ---_1LP---_1RJ---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESW".
Definition mp' := mp_from_str "JPCLDESW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM327.


Module TM328.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RF_1RC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1LD---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LP0RV_---1RV_0LW1RJ_1LW---_0RJ---_1RJ---_1LP---_1RJ---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LP0RF_---1RF_0LX1RJ_1LX1RE_1LL---_1LC---_0LP---_1LP---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESW".
Definition mp' := mp_from_str "JPCLDESX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM328.


Module TM329.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF0RF_0LA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0LA---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_0LC0RU_---1RU_0LW1RJ_1LW---_1RJ---_0LP---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_0LC0RF_---1RF_0LW1RJ_1LW1RE_1RJ---_0LP---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_0LC---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_0LC1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESW".
Definition mp' := mp_from_str "JPCLDESW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM329.


Module TM330.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF0RF_0LA---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LC0RF_---1RF_0LX1RJ_1LX1RE_0RB---_1RB---_1RF---_1LC---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LC0RU_---1RU_0LX1RJ_1LX---_1RJ---_0LP---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LC---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LC1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESX".
Definition mp' := mp_from_str "JPCLDESX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM330.


Module TM331.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF0RF_0LA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0LA---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LC0RU_---1RU_0LX1RJ_1LX---_1RJ---_0LP---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LC0RF_---1RF_0LX1RJ_1LX1RE_1RJ---_0LP---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LC---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LC1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESX".
Definition mp' := mp_from_str "JPCLDESX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM331.


Module TM332.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RA---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LL0RF_---1RF_0LX1RJ_1LX1RE_1LD---_1LS---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LL0RF_---1RF_0LX1RJ_1LX1RE_0RA---_1RA---_0RF---_1LL---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LD---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LD1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESX".
Definition mp' := mp_from_str "JPCLDESX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM332.


Module TM333.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1LA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0RD---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LD0RF_---1RF_0LX1RJ_1LX1RE_1RE---_1LP---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1LD0RF_---1RF_0LW1RJ_1LW1RE_0RM---_1RM---_1LD---_1RJ---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LE---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1LE1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESX".
Definition mp' := mp_from_str "JPCLDESW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM333.


Module TM334.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RA---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LX_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1RF0RF_---1RF_0LX1RJ_1LX1RE_0RR---_1RR---_------_1RF---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE0LW_1LP1RJ_0LD0LS_1LD1LS_1LD1RJ_1LS0LP_0LL0LC_1LL1LC_1RF0RF_---1RF_0LW1RJ_1LW1RE_0RB---_1RB---_1RF---_1LC---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RI---_1RA1RF".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RI1RJ_1RA1RF_1RJ1RJ".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDESXF".
Definition mp' := mp_from_str "JPCLDESWF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM334.


Module TM335.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LC".
Definition tm' := TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA0LC_1LE0LA".
Definition tm0 := TM'_from_str "0RF1LX_1RF1LC_1RI0LT_1RE1LT_0RI0RE_1RI1RE_1LT0RI_1RI0RE_1LT1RI_---0LT_0LP0LC_1LP1LC_1LX---_1LC---_0LT---_1LT---_1LD1RI_1LK0LT_0LX0LC_1LX1LC_1RE0LP_1LT0LC_0LD0LK_1LD1LK".
Definition tm0' := TM'_from_str "0RF1LT_1RF1LC_1RI0LX_1RE1LX_0RI0RE_1RI1RE_1LX0RI_1RI0RE_1LX1RI_---0LX_0LO0LC_1LO1LC_0RR---_1RR---_1LX---_0LC---_1RE0LO_1LX0LC_0LD0LK_1LD1LK_1LD1RI_1LK0LX_0LT0LC_1LT1LC".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH0LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH0LC_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "ITCXDEKP".
Definition mp' := mp_from_str "IXCTDEKO".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM335.


Module TM336.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1RB---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RD---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LW_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1RJ0RM_---1RM_0LW1LD_1LW1RJ_0RF---_1RF---_1RJ---_1RE---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LX_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1RJ0RM_---1RM_0LX1LD_1LX1RJ_0RM---_1RM---_1LD---_1RJ---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1RA1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDETW".
Definition mp' := mp_from_str "JPCLDETX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM336.


Module TM337.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1LD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1RC---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LX_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1LP0RM_---1RM_0LX1LD_1LX1RJ_1LL---_1LC---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LW_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1LP0RM_---1RM_0LW1LD_1LW1RJ_0RJ---_1RJ---_1LP---_1RJ---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDETX".
Definition mp' := mp_from_str "JPCLDETW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM337.


Module TM338.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LA---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LX_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1LC0RM_---1RM_0LX1LD_1LX1RJ_0RB---_1RB---_1RF---_1LC---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LX_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1LC0RM_---1RM_0LX1LD_1LX1RJ_1RJ---_0LP---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1LC---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1LC1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDETX".
Definition mp' := mp_from_str "JPCLDETX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM338.


Module TM339.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RA---".
Definition tm0 := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LX_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1LL0RM_---1RM_0LX1LD_1LX1RJ_1LD---_1LT---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LX_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1LL0RM_---1RM_0LX1LD_1LX1RJ_0RA---_1RA---_0RF---_1LL---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1LD---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1LD1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JPCLDETX".
Definition mp' := mp_from_str "JPCLDETX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM339.


Module TM340.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1LF_1RB1LE_1LC0LD_1LA0RE".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_0RC---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RJ---_1RE---_0RJ0RE_1RJ1RE_1LT0RJ_1RJ0RE_1RE1LD_1LT1RJ_0LP0LX_1LP1LX_0RF1LL_1RF1LO_1RJ0LT_1RE1LT_1LP1RJ_1LX0LT_0LL0LO_1LL1LO_1RE0RQ_---1RQ_0LD1LP_1LD1RJ".
Definition tm0' := TM'_from_str "0RF1LL_1RF1LC_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LP0RJ_1RJ0RE_1RE1LW_1LP1RJ_0LD0LT_1LD1LT_1LD1RJ_1LT0LP_0LL0LC_1LL1LC_1RE0RM_---1RM_0LW1LD_1LW1RJ_0RI---_1RI---_1RE---_1LW---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1RF---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1RF1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JTOLPEXD".
Definition mp' := mp_from_str "JPCLDETW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM340.


Module TM341.
Definition tm := TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA1LC_1LE0LA".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA1LC".
Definition tm0 := TM'_from_str "0RF1LT_1RF1LC_1RI0LX_1RE1LX_0RI0RE_1RI1RE_1LX0RI_1RI0RE_1LX1RI_---0LX_0LO0LC_1LO1LC_0RR---_1RR---_1LX---_1LC---_1RE1LO_1LX1LC_0LD0LL_1LD1LL_1LD1RI_1LL0LX_0LT0LC_1LT1LC".
Definition tm0' := TM'_from_str "0RF1LX_1RF1LC_1RI0LT_1RE1LT_0RI0RE_1RI1RE_1LT0RI_1RI0RE_1LT1RI_---0LT_0LP0LC_1LP1LC_1LX---_1LC---_0LT---_1LT---_1LD1RI_1LL0LT_0LX0LC_1LX1LC_1RE1LP_1LT1LC_0LD0LL_1LD1LL".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1LC_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "IXCTDELO".
Definition mp' := mp_from_str "ITCXDELP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM341.


Module TM342.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA1LC".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF1RF_1LA1LC".
Definition tm0 := TM'_from_str "0RF1LX_1RF1LC_1RI0LT_1RE1LT_0RI0RE_1RI1RE_1LT0RI_1RI0RE_1LT1RI_---0LT_0LP0LC_1LP1LC_1LX---_1LC---_0LT---_1LT---_1LD1RI_1LL0LT_0LX0LC_1LX1LC_1RE1LP_1LT1LC_0LD0LL_1LD1LL".
Definition tm0' := TM'_from_str "0RF1LX_1RF1LC_1RI0LT_1RE1LT_0RI0RE_1RI1RE_1LT0RI_1RI0RE_1LT1RI_---0LT_0LP0LC_1LP1LC_1LX---_1LC---_0LT---_1LT---_1LD0RV_1LL1RV_0LX1LT_1LX1LC_1RE1LP_1LT1LC_0LD0LL_1LD1LL".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1LC_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "ITCXDELP".
Definition mp' := mp_from_str "ITCXDELP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM342.


Module TM343.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF1RF_1LA1LC".
Definition tm' := TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA1LC_1LE1RE".
Definition tm0 := TM'_from_str "0RF1LX_1RF1LC_1RI0LT_1RE1LT_0RI0RE_1RI1RE_1LT0RI_1RI0RE_1LT1RI_---0LT_0LP0LC_1LP1LC_1LX---_1LC---_0LT---_1LT---_1LD0RV_1LL1RV_0LX1LT_1LX1LC_1RE1LP_1LT1LC_0LD0LL_1LD1LL".
Definition tm0' := TM'_from_str "0RF1LT_1RF1LC_1RI0LX_1RE1LX_0RI0RE_1RI1RE_1LX0RI_1RI0RE_1LX1RI_---0LX_0LO0LC_1LO1LC_0RR---_1RR---_1LX---_1LC---_1RE1LO_1LX1LC_0LD0LL_1LD1LL_1LD0RR_1LL1RR_0LT1LX_1LT1LC".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1LC_1LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1LC_1LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "ITCXDELP".
Definition mp' := mp_from_str "IXCTDELO".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM343.


Module TM344.
Definition tm := TM_from_str "1RB1RE_1LC1LB_1RD0LC_0RA---_0LF0RF_0RA1RA".
Definition tm' := TM_from_str "1RB0RF_1LC1LB_1RD0LC_0RE---_1RB1RA_0RE1RE".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1RF_1LH1RU_---1LL_1LK1LH_0LL0LH_1LL1LH_0RN1RA_1RN0LK_1RA0LK_---1LK_0RA---_1RA---_0RF---_0RR---_0RF0RU_1RF1RU_0LW0RA_1LW0RB_0RA0RB_1RA1RB_0RF1RF_0RR1RR".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LK0RQ_1LH0RR_---1LL_1LK1LH_0LL0LH_1LL1LH_0RN1RQ_1RN0LK_1RQ0LK_---1LK_0RQ---_1RQ---_0RF---_0RB---_0RF0RB_1RF1RB_1LK1RF_1LH1RU_0RQ0RR_1RQ1RR_0RF1RF_0RB1RB".
Definition tm1 := TM'_from_str "1LB1LE_1RC0LB_0RA0RD_1RA1RG_1LF1LE_---1LB_0RC0RH_1RA1RD".
Definition tm2 := TM'_from_str "1LB1LE_1RC0LB_0RA0RD_1RA1RG_1LF1LE_1RI1LB_0RC0RH_1RA1RD_1RI1RI".
Definition l0 := [1;0;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "FKARHLUB".
Definition mp' := mp_from_str "FKQBHLUR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM344.


Module TM345.
Definition tm := TM_from_str "1RB0RF_1LC1LB_1RD0LC_0RE---_1RB1RA_0RE1RE".
Definition tm' := TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_1RB0RE".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LK0RQ_1LH0RR_---1LL_1LK1LH_0LL0LH_1LL1LH_0RN1RQ_1RN0LK_1RQ0LK_---1LK_0RQ---_1RQ---_0RF---_0RB---_0RF0RB_1RF1RB_1LK1RF_1LH1RU_0RQ0RR_1RQ1RR_0RF1RF_0RB1RB".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1RF_1LH1RQ_---1LL_1LO1LH_0LL0LH_1LL1LH_---1RA_---0LO_---0LO_---1LO_0RR1RA_1RR0LO_1RA0LO_1RB1LO_0RA0RB_1RA1RB_0RF1RF_0RV1RV_0RF0RQ_1RF1RQ_1LO0RA_1LH0RB".
Definition tm1 := TM'_from_str "1LB1LE_1RC0LB_0RA0RD_1RA1RG_1LF1LE_---1LB_0RC0RH_1RA1RD".
Definition tm2 := TM'_from_str "1LB1LE_1RC0LB_0RA0RD_1RA1RG_1LF1LE_1RI1LB_0RC0RH_1RA1RD_1RI1RI".
Definition l0 := [1;0;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "FKQBHLUR".
Definition mp' := mp_from_str "FOAVHLQB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM345.


Module TM346.
Definition tm := TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_1RB0RE".
Definition tm' := TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_0LE0RE".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RF_1LH1RQ_---1LL_1LO1LH_0LL0LH_1LL1LH_---1RA_---0LO_---0LO_---1LO_0RR1RA_1RR0LO_1RA0LO_1RB1LO_0RA0RB_1RA1RB_0RF1RF_0RV1RV_0RF0RQ_1RF1RQ_1LO0RA_1LH0RB".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1RF_1LH1RQ_---1LL_1LO1LH_0LL0LH_1LL1LH_---1RA_---0LO_---0LO_---1LO_0RR1RA_1RR0LO_1RA0LO_1RB1LO_0RA0RB_1RA1RB_0RF1RF_0RV1RV_0RF0RQ_1RF1RQ_0LS0RA_1LS0RB".
Definition tm1 := TM'_from_str "1LB1LE_1RC0LB_0RA0RD_1RA1RG_1LF1LE_---1LB_0RC0RH_1RA1RD".
Definition tm2 := TM'_from_str "1LB1LE_1RC0LB_0RA0RD_1RA1RG_1LF1LE_1RI1LB_0RC0RH_1RA1RD_1RI1RI".
Definition l0 := [1;0;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "FOAVHLQB".
Definition mp' := mp_from_str "FOAVHLQB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM346.


Module TM347.
Definition tm := TM_from_str "1LB1RD_1RC0LA_1LC1LA_1RF0RE_1RA0RB_---0LE".
Definition tm' := TM_from_str "1LB1RD_1RC0LA_1LC1LA_0RF0RE_1RA0RB_---1RC".
Definition tm0 := TM'_from_str "1RQ0RN_1LC1RN_0LH1RV_1LH1RQ_0RJ0LH_1RJ1RV_1LD0LC_1RQ1LC_1LL1LH_1LD1RQ_0LL0LD_1LL1LD_0RV0RQ_1RV1RQ_---0RB_0RJ0RE_0RB0RE_1RB1RE_1LC0RJ_1RN0LH_---1LC_---0RJ_---0LS_---1LS".
Definition tm0' := TM'_from_str "1RQ0RN_1LC1RN_0LH1RU_1LH1RQ_0RJ0LH_1RJ1RU_1LD0LC_1RQ1LC_1LL1LH_1LD1RQ_0LL0LD_1LL1LD_0RU0RQ_1RU1RQ_---0RB_0RJ0RE_0RB0RE_1RB1RE_1LC0RJ_1RN0LH_---0RJ_---1RJ_---1LD_---1RQ".
Definition tm1 := TM'_from_str "1LB1RI_0LC1RD_1RG1LB_---0RE_1LF1RG_1LC1RG_0RA0RH_0RE0LC_1RD1RG".
Definition tm2 := TM'_from_str "1LB1RI_0LC1RD_1RG1LB_1RJ0RE_1LF1RG_1LC1RG_0RA0RH_0RE0LC_1RD1RG_1RJ1RJ".
Definition l0 := [1;0;1;0;1;1;1;0]%N.
Definition mp := mp_from_str "BCHVJDQEN".
Definition mp' := mp_from_str "BCHUJDQEN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM347.


Module TM348.
Definition tm := TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1LC0RA".
Definition tm' := TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1RC0RA".
Definition tm0 := TM'_from_str "0RF0RM_1RF1RM_1RJ1LX_---0RB_0RJ---_1RJ---_1RN---_1LL---_0RN1RB_1RN1LL_1LS0LL_1RB1LL_1LX0RB_1LS1RB_0LT1RF_1LT1RM_1LL0LX_0RM0LS_0LX0LS_1LX1LS_1RB0RA_1LL1RA_0LL0RF_1LL0RM".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1RJ1LX_---0RB_0RJ---_1RJ---_1RN---_1LL---_0RN1RB_1RN1LL_1LS0LL_1RB1LL_1LX0RB_1LS1RB_0LT1RF_1LT1RM_1LL0LX_0RM0LS_0LX0LS_1LX1LS_0RJ0RA_1RJ1RA_1RN0RF_1LL0RM".
Definition tm1 := TM'_from_str "1RB---_1RC1LF_1LD1RG_0LE0LD_1LF0RH_1RG1LF_1RA1RH_1LE0RG".
Definition tm2 := TM'_from_str "1RB1RI_1RC1LF_1LD1RG_0LE0LD_1LF0RH_1RG1LF_1RA1RH_1LE0RG_1RI1RI".
Definition l0 := [1;0;1;1;0;0;0;1]%N.
Definition mp := mp_from_str "FJNSXLBM".
Definition mp' := mp_from_str "FJNSXLBM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM348.


Module TM349.
Definition tm := TM_from_str "1LB0LD_0LC1LF_1RD---_0RE1RE_1LA1RD_1LD0RF".
Definition tm' := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA1RD_1LD0RF".
Definition tm0 := TM'_from_str "1LK1LH_1LX1LO_0LH0LO_1LH1LO_1RQ1LP_---0RU_0LK0LX_1LK1LX_0RN---_1RN---_1RQ---_1RR---_0RQ0RR_1RQ1RR_1LH1LO_0RN1RN_1LH0RN_1LO1RN_0LD1RQ_1LD1RR_0RN0RU_1RN1RU_0LP0RN_1LP0RU".
Definition tm0' := TM'_from_str "1LK1LH_1LX1LD_0LH0LD_1LH1LD_1RQ1LP_---0RU_0LK0LX_1LK1LX_0RN---_1RN---_1RQ---_1RR---_0RQ0RR_1RQ1RR_1LH1LD_0RN1RN_1LH0RN_1LD1RN_0LD1RQ_1LD1RR_0RN0RU_1RN1RU_0LP0RN_1LP0RU".
Definition tm1 := TM'_from_str "1RB1RG_1LC0RA_1LI1LD_1LF0RE_0RA0RE_0RA1RA_1LH1RA_1LC1LH_1RB---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RA_1LI1LD_1LF0RE_0RA0RE_0RA1RA_1LH1RA_1LC1LH_1RB1RJ_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "NQHXUPROK".
Definition mp' := mp_from_str "NQHXUPRDK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM349.


Module TM350.
Definition tm := TM_from_str "1RB0RE_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LD---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ1LD_1RE1LP_0RJ0RE_1RJ1RE_1LS0RJ_1RM0RE_1LD0RM_1LS1RM_0LP1RE_1LP0LP_1RE0LP_1LP0LX_0LD0LS_1LD1LS_1LD1LP_1LS---_0LP0LX_1LP1LX_1LD---_1LS---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LS_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LS0RJ_1RM0RE_1LD0RM_1LS1RM_0LP1RE_1LP0LP_1RE0LP_1LP0LX_0LD0LS_1LD1LS_1LD1LP_1LS---_0LP0LX_1LP1LX_1LD---_1LS---_0LP---_1LP---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RF_0LD0LG_1LE1LC_1RA1LD_1RA0LD_1LD---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RF_0LD0LG_1LE1LC_1RA1LD_1RA0LD_1LD1RH_1RH1RH".
Definition l0 := [1;1;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "EJSPDMX".
Definition mp' := mp_from_str "EJSPDMX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM350.


Module TM351.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD0LF_1RD---".
Definition tm0 := TM'_from_str "0RF1LD_1RF1LS_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LS0RJ_1RM0RE_1LD0RM_1LS1RM_0LP1RE_1LP0LP_1RE0LP_1LP0LX_0LD0LS_1LD1LS_1LD1LP_1LS---_0LP0LX_1LP1LX_1LD---_1LS---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF1LD_1RF1LS_1RJ0LP_1RE1LP_0RJ0RE_1RJ1RE_1LS0RJ_1RM0RE_1LD0RM_1LS1RM_0LP1RE_1LP0LP_1RE0LP_1LP0LW_0LD0LS_1LD1LS_1LD1LP_1LS---_0LP0LW_1LP1LW_0RN---_1RN---_1LP---_0LW---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RF_0LD0LG_1LE1LC_1RA1LD_1RA0LD_1LD---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RF_0LD0LG_1LE1LC_1RA1LD_1RA0LD_1LD1RH_1RH1RH".
Definition l0 := [1;1;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "EJSPDMX".
Definition mp' := mp_from_str "EJSPDMW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM351.


Module TM352.
Definition tm := TM_from_str "1LB1RC_1RA1RD_1RD0RC_0RE0LD_1LA0RF_0RC---".
Definition tm' := TM_from_str "1LB1RC_1RA1RD_1RD0RC_0RE0LD_1LA1RF_1LC---".
Definition tm0 := TM'_from_str "1RJ0RJ_0LO1RJ_0LH1RN_1LH1RI_0RB0RN_1RB1RN_0LO1RQ_1RJ0LO_0RN0RI_1RN1RI_1RQ0RN_0LO0RI_0RQ1LH_1RQ0LO_1LH0LO_0RU1LO_1LH0RU_1RI1RU_0LD0RI_1LD---_0RI---_1RI---_0RN---_0RI---".
Definition tm0' := TM'_from_str "1RJ0RJ_0LO1RJ_0LH1RN_1LH1RI_0RB0RN_1RB1RN_0LO1RQ_1RJ0LO_0RN0RI_1RN1RI_1RQ0RN_0LO0RI_0RQ1LH_1RQ0LO_1LH0LO_0RV1LO_1LH0RV_1RI1RV_0LD0RI_1LD---_0LO---_0RI---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RA_1RC0LE_1LD0RG_1RF0LE_1LD0LE_1RB1RA_0RA---".
Definition tm2 := TM'_from_str "0RB0RA_1RC0LE_1LD0RG_1RF0LE_1LD0LE_1RB1RA_0RA1RH_1RH1RH".
Definition l0 := [1;1;0;1;0;0;0;0]%N.
Definition mp := mp_from_str "INQHOJU".
Definition mp' := mp_from_str "INQHOJV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM352.


Module TM353.
Definition tm := TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0RB_---0LC".
Definition tm' := TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LL---_1RN0LD_1LD0RN_1LL1RN_0LL1RB_1LL1RR_1RN1LD_0LD1LL_0LD0LL_1LD1LL_0RB0RR_1RB1RR_1RF1RE_1RU1RE_0RE0RE_1RE1RE_1LD1LD_0RN0RN_---0LD_---0LL_---0LK_---1LK".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LL---_1RN0LD_1LD0RN_1LL1RN_0LL1RB_1LL1RR_1RN1LD_0LD1LL_0LD0LL_1LD1LL_0RB0RR_1RB1RR_1RF1RE_1RU1RE_0RE1RF_1RE1RE_1LD0LO_0RN1LO_---0LD_---0LL_---0LK_---1LK".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RE_1LD1LC_1RE0LD_1RA1RF_1RG1RG_1LD0RE_---0LD".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RE_1LD1LC_1RE0LD_1RA1RF_1RG1RG_1LD0RE_1RI0LD_1RI1RI".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "BFLDNREU".
Definition mp' := mp_from_str "BFLDNREU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM353.


Module TM354.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1RA0LD_1LC0LE_0LF0RA_---1RC".
Definition tm' := TM_from_str "1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LO1RB_1RA1RA_1RR0RA_1LO1RA_0LL0RF_1LL0RR_0RB0LL_1RB0LS_1RF0LO_1RR1LO_1RR0LW_1LO0RF_0LL0LS_1LL1LS_---0RA_1RB1RA_0LW0RF_1LW0RR_---0RJ_---1RJ_---1RB_---0LS".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LO1RB_1RA1RA_1RR1RA_1LO1RA_0LL0LD_1LL1LD_0RB0LL_1RB0LS_1RF0LO_1RR1LO_1RR0LW_1LO0RF_0LL0LS_1LL1LS_---0RA_1RB1RA_0LW0RF_1LW0RR_---0RJ_---1RJ_---1RB_---0LS".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0LE0LD_0LH0RB_1RF1LC_1RA1RG_0RB0RF_---1RA".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0LE0LD_0LH0RB_1RF1LC_1RA1RG_0RB0RF_1RI1RA_1RI1RI".
Definition l0 := [1;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFOSLRAW".
Definition mp' := mp_from_str "BFOSLRAW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM354.


Module TM355.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_0LD---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_1RB0RF_1RD0RB_1RA1LC".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LK0RU_1RN1LD_1LD0RN_1LK1RN_0LL1RB_1LL1RE_1RN0LD_1LD0LK_0LD0LK_1LD1LK_0RB0RE_1RB1RE_1RF1LD_1RQ0RN_0RU1LD_1RU1LK_1RF0LL_---1LL_1RF---_1LD---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LK---_1RR---_1LP0RR_1LK1RR_0LL1RN_1LL1RE_1RR0LP_1LP0LK_0LP0LK_1LP1LK_0RF0RU_1RF1RU_1LK0RB_1RR1LP_0RN0RE_1RN1RE_1RF1LP_1RU0RR_0RB1LP_1RB1LK_1RF0LL_---1LL".
Definition tm1 := TM'_from_str "1RB---_1LC1RE_0LD0LC_1RE1LD_1RG1RF_1LD0RE_1RB1RH_0RA1LD".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RE_0LD0LC_1RE1LD_1RG1RF_1LD0RE_1RB1RH_0RA1LD_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "UFKDNEBQ".
Definition mp' := mp_from_str "BFKPRENU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM355.


Module TM356.
Definition tm := TM_from_str "1LB1RF_1LC1LD_1RB0LF_---1LE_1RA0LB_1RE0RA".
Definition tm' := TM_from_str "1LB1RE_1LC1LF_1LD0LE_1RA0LB_1RD0RA_---1LD".
Definition tm0 := TM'_from_str "1LL0RV_1LP1RV_0LH1RR_1LH1RA_1LT---_1LW1LT_0LL0LP_1LL1LP_0RF1RB_1RF1LL_1LW0LW_1LT1LW_---1RV_---1LG_---0LT_---1LT_0RB0LL_1RB0LP_1LP0LG_1RV1LG_0RR0RA_1RR1RA_1RB1LL_0LP0RV".
Definition tm0' := TM'_from_str "1LL0RR_1LX1RR_0LH1RN_1LH1RA_1LP---_1LS1LP_0LL0LX_1LL1LX_1RR1RB_1LG1LL_0LP0LS_1LP1LS_0RB0LL_1RB0LX_1LX0LG_1RR1LG_0RN0RA_1RN1RA_1RB1LL_0LX0RR_---1RR_---1LG_---0LP_---1LP".
Definition tm1 := TM'_from_str "1RB1RI_1RC0LD_1LD1RA_---1LE_1RA1LF_0LG0LD_1LE1LH_1RC1LG_1LG0RA".
Definition tm2 := TM'_from_str "1RB1RI_1RC0LD_1LD1RA_1RJ1LE_1RA1LF_0LG0LD_1LE1LH_1RC1LG_1LG0RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;0;1;0]%N.
Definition mp := mp_from_str "VRBPTGLWA".
Definition mp' := mp_from_str "RNBXPGLSA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM356.


Module TM357.
Definition tm := TM_from_str "1LB0RE_0LC---_1RC0LD_0LB1LA_1RF1RE_0RA0LE".
Definition tm' := TM_from_str "1LB0RE_0LC---_1RC0LD_0LB1LA_1RF1RE_0RA1RF".
Definition tm0 := TM'_from_str "1LK0RQ_---1RQ_0LH0RV_1LH0RR_1RJ---_0LO---_0LK---_1LK---_0RJ0LG_1RJ0LD_1RJ0LO_0LD1LO_0LK1LH_---0RR_0LG0LD_1LG1LD_0RV0RR_1RV1RR_1RA1RV_1RV1RR_0RA1RA_1RA1RV_1LK0LS_0RQ1LS".
Definition tm0' := TM'_from_str "1LK0RQ_---1RQ_0LH0RV_1LH0RR_1RJ---_0LO---_0LK---_1LK---_0RJ0LG_1RJ0LD_1RJ0LO_0LD1LO_0LK1LH_---0RR_0LG0LD_1LG1LD_0RV0RR_1RV1RR_1RA1RV_1RV1RR_0RA0RV_1RA1RV_1LK1RA_0RQ1RV".
Definition tm1 := TM'_from_str "1LB0RI_1RF0LC_0LJ0LD_1LE0RG_1LB---_1RF0LD_1RH1RG_1RA1RH_0RH0RG_0LB---".
Definition tm2 := TM'_from_str "1LB0RI_1RF0LC_0LJ0LD_1LE0RG_1LB1RK_1RF0LD_1RH1RG_1RA1RH_0RH0RG_0LB1RK_1RK1RK".
Definition l0 := [0;0;1;1;0;0;1;1]%N.
Definition mp := mp_from_str "AKODHJRVQG".
Definition mp' := mp_from_str "AKODHJRVQG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM357.


Module TM358.
Definition tm := TM_from_str "1RB0LB_0RC0RD_1LD0RE_0LA0LD_0RF---_1RC1RF".
Definition tm' := TM_from_str "1RB0LB_0RC1RB_1LD0RE_0LA0LD_0RF---_1RC1RF".
Definition tm0 := TM'_from_str "0RF1LC_1RF1RI_1RI0LG_1RM1LG_0RI0RM_1RI1RM_1LC1RI_0RQ0LC_1LC0RQ_1LO1RQ_0LP0RU_1LP---_1RI0LC_0LG0LO_0LC0LO_1LC1LO_0RU---_1RU---_0RJ---_0RV---_0RJ0RV_1RJ1RV_1LO1RJ_1RQ1RV".
Definition tm0' := TM'_from_str "0RF1LC_1RF1RI_1RI0LG_1RF1LG_0RI0RF_1RI1RF_1LC1RI_0RQ1RF_1LC0RQ_1LO1RQ_0LP0RU_1LP---_1RI0LC_0LG0LO_0LC0LO_1LC1LO_0RU---_1RU---_0RJ---_0RV---_0RJ0RV_1RJ1RV_1LO1RJ_1RQ1RV".
Definition tm1 := TM'_from_str "1RB1RA_1LC1RG_0LD0LC_1RE0LF_1LD0RG_1LD1RE_0RH---_0RB0RA".
Definition tm2 := TM'_from_str "1RB1RA_1LC1RG_0LD0LC_1RE0LF_1LD0RG_1LD1RE_0RH1RI_0RB0RA_1RI1RI".
Definition l0 := [1;0;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "VJOCIGQU".
Definition mp' := mp_from_str "VJOCIGQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM358.


Module TM359.
Definition tm := TM_from_str "1LB---_1LC1LB_1RD0LB_1RE0RD_0RF0RC_1RA0LF".
Definition tm' := TM_from_str "1LB---_1LC1LB_1RD0LB_1RE0RD_0RF0RC_1RA1LA".
Definition tm0 := TM'_from_str "1LL---_1LH---_0LH---_1LH---_1RM1LL_1LG1LH_0LL0LH_1LL1LH_0RN0LL_1RN0LH_1RR0LG_1RM1LG_0RR0RM_1RR1RM_1RU0RR_1RI0RM_0RU0RI_1RU1RI_0RB0RN_1LH0LL_0RB1LH_1RB0LW_1LH0LW_---1LW".
Definition tm0' := TM'_from_str "1LL---_1LH---_0LH---_1LH---_1RM1LL_1LG1LH_0LL0LH_1LL1LH_0RN0LL_1RN0LH_1RR0LG_1RM1LG_0RR0RM_1RR1RM_1RU0RR_1RI0RM_0RU0RI_1RU1RI_0RB0RN_1LH0LL_0RB1LH_1RB---_1LH0LD_---1LD".
Definition tm1 := TM'_from_str "0RB0LG_1RC1RI_1RD1RA_0RE1LF_1LF---_1LG1LF_1RI1LH_0LG0LF_0RC0RI".
Definition tm2 := TM'_from_str "0RB0LG_1RC1RI_1RD1RA_0RE1LF_1LF1RJ_1LG1LF_1RI1LH_0LG0LF_0RC0RI_1RJ1RJ".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "INRUBHLGM".
Definition mp' := mp_from_str "INRUBHLGM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM359.


Module TM360.
Definition tm := TM_from_str "1LB0LD_1LC0LA_1RD1LB_1RE0RD_1RF0RB_1LC---".
Definition tm' := TM_from_str "1LB0LD_1LC0LA_1RD1LB_1RE0RD_0RF0RB_1LA---".
Definition tm0 := TM'_from_str "1LL1RV_1LC0RR_0LH0LO_1LH1LO_1RM0LH_1LH0LO_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_1LH1RM_---0LH_1RM---_1LH---_0LL---_1LL---".
Definition tm0' := TM'_from_str "1LL1RU_1LC0RR_0LH0LO_1LH1LO_1RM0LH_1LH0LO_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RU0RR_1RE0RM_0RU0RE_1RU1RE_1LH1RM_---0LH_1LH---_1LO---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RH_1LC---_1LF1LD_0LC0LE_1RB0RA_1RG1LC_0RA0RG_1RG0LC".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RI_1LF1LD_0LC0LE_1RB0RA_1RG1LC_0RA0RG_1RG0LC_1RI1RI".
Definition l0 := [1;0;1;0;0;1;1;0]%N.
Definition mp := mp_from_str "RVHCOLME".
Definition mp' := mp_from_str "RUHCOLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM360.


Module TM361.
Definition tm := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm' := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm0 := TM'_from_str "0RF1RA_1RF1LO_1LO0LL_1RM1LL_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG1RA_0RQ---_1RQ---_0LL---_0RA---".
Definition tm0' := TM'_from_str "0RF1RA_1RF1LO_1LO0LL_1RM1LL_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG1RA_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB1RA_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---".
Definition tm2 := TM'_from_str "0RB1RA_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQW".
Definition mp' := mp_from_str "AFOLMQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM361.


Module TM362.
Definition tm := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RF1RA_1RF1LO_1LO0LL_1RM1LL_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG1RA_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF1RA_1RF1LO_1LO0LL_1RM1LL_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_---0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_---1RA_0LW0RF_1LW1RA_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB1RA_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---".
Definition tm2 := TM'_from_str "0RB1RA_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQW".
Definition mp' := mp_from_str "AFOLMQW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM362.


Module TM363.
Definition tm := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1LC_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm0 := TM'_from_str "0RF1RA_1RF1LO_1LO0LL_1RM1LL_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_---0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_---1RA_0LW0RF_1LW1RA_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF1RA_1RF1LO_1LO0LL_1RM1LL_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LX_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LX_0RA1LX_0LL0RA_0RQ1RA_0LG0RF_1LG1RA_0RI---_1RI---_0RR---_0LL---".
Definition tm1 := TM'_from_str "0RB1RA_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---".
Definition tm2 := TM'_from_str "0RB1RA_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQW".
Definition mp' := mp_from_str "AFOLMQX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM363.


Module TM364.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LD---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LC---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO0LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0LL---_0LO---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO0LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0RQ---_0LO---_0LK---_1LK---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_0LC---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_0LC1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQV".
Definition mp' := mp_from_str "AFOLMQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM364.


Module TM365.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LA---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RD0LC_0LE0RA_1LF---_1RD0LC".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1LO---_1LO---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LK1LK_1RI---_0RA0RI_1LK1RI_0LL0RM_1LL0LX_0RM0LX_1RM0LK_0LX0LK_0RA1LK_0LX0RA_---1RA_0LS0RF_1LS0RR_1RA---_1LK---_0LX---_1LX---_0RN0LX_1RN0LK_---0LK_1RA1LK".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQU".
Definition mp' := mp_from_str "AFKXIMR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM365.


Module TM366.
Definition tm := TM_from_str "1RB1RE_1LC0RC_0RD0LC_0LE0RA_1LF---_1RD0LC".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LK1LK_1RI---_0RA0RI_1LK1RI_0LL0RM_1LL0LX_0RM0LX_1RM0LK_0LX0LK_0RA1LK_0LX0RA_---1RA_0LS0RF_1LS0RR_1RA---_1LK---_0LX---_1LX---_0RN0LX_1RN0LK_---0LK_1RA1LK".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_---0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_---1RA_0LW0RF_1LW0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFKXIMR".
Definition mp' := mp_from_str "AFOLMQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM366.


Module TM367.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1RC_0LA0RE_1LD---_1RF0LE_0RF0LE_0LC0RA".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_---0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_---1RA_0LW0RF_1LW0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1LS1LS_1RQ---_1LS0RQ_1LS1RQ_0LC0RU_1LC0LP_1RA---_1LS---_0LP---_1LP---_0RV0LP_1RV0LS_---0LS_1RA1LS_0RU0LP_1RU0LS_0LP0LS_0RA1LS_0LP0RA_---1RA_0LK0RF_1LK0RJ".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQV".
Definition mp' := mp_from_str "AFSPQUJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM367.


Module TM368.
Definition tm := TM_from_str "1RB1RC_0LA0RE_1LD---_1RF0LE_0RF0LE_0LC0RA".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_1LS1LS_1RQ---_1LS0RQ_1LS1RQ_0LC0RU_1LC0LP_1RA---_1LS---_0LP---_1LP---_0RV0LP_1RV0LS_---0LS_1RA1LS_0RU0LP_1RU0LS_0LP0LS_0RA1LS_0LP0RA_---1RA_0LK0RF_1LK0RJ".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFSPQUJ".
Definition mp' := mp_from_str "AFOLMQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM368.


Module TM369.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LB---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LB---".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_0LL---_0RQ---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_1LL---_0LL---_0LH---_1LH---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_0LD---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_0LD1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQU".
Definition mp' := mp_from_str "AFOLMQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM369.


Module TM370.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LB---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0LD---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_1LL---_0LL---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_0LL---_0LO---_0LO---_1LO---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_0LD---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_0LD1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQV".
Definition mp' := mp_from_str "AFOLMQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM370.


Module TM371.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LA---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0RM---_1RM---_0RQ---_0LL---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1RM---_------_0LD---_1LD---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1RE---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1RE1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQV".
Definition mp' := mp_from_str "AFOLMQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM371.


Module TM372.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LA---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1LO---_1LO---_0LC---_1LC---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1LC---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1LC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGV".
Definition mp' := mp_from_str "AFOLMQGU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM372.


Module TM373.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LA---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1LO---_1LO---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_---0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_---1RA_0LW0RF_1LW0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1LC---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1LC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGU".
Definition mp' := mp_from_str "AFOLMQGV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM373.


Module TM374.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LD---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LB---".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_0LL---_0LG---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_1LL---_0LL---_0LH---_1LH---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0LD---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0LD1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGU".
Definition mp' := mp_from_str "AFOLMQGV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM374.


Module TM375.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LB---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LB---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_1LL---_0LL---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO0LL_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_0LL---_0RQ---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0LD---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0LD1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGV".
Definition mp' := mp_from_str "AFOLMQGU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM375.


Module TM376.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_1LF0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RD---".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LO0RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_---0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_---1RA_0LX0RF_1LX0RU_0RM---_1RM---_0RQ---_0LL---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO0RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_0RM---_1RM---_0RQ---_0LL---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0RE---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0RE1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGU".
Definition mp' := mp_from_str "AFOLMQGU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM376.


Module TM377.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RD---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_1LF0RA_0RD---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0RM---_1RM---_0RQ---_0LL---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_---0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_---1RA_0LX0RF_1LX0RV_0RM---_1RM---_0RQ---_0LL---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1RE---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1RE1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGV".
Definition mp' := mp_from_str "AFOLMQGV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM377.


Module TM378.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_1LF0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LA---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_---0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_---1RA_0LX0RF_1LX0RV_0RM---_1RM---_0RQ---_0LL---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1RM---_------_0LD---_1LD---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1RE---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1RE1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGV".
Definition mp' := mp_from_str "AFOLMQGU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM378.


Module TM379.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LE---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO0LG_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0LL---_0LG---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO0LG_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_0LG---_0RF---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_0LG1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGV".
Definition mp' := mp_from_str "AFOLMQGU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM379.


Module TM380.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LE---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1LG_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0RA---_1LG---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO1LG_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1LG---_0RU---_0LT---_1LT---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1LG---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD0RF_1LG1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQGV".
Definition mp' := mp_from_str "AFOLMQGU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM380.


Module TM381.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_---0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_---1RA_0LW0RF_1LW0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---_1LC---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RI_1LC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQWV".
Definition mp' := mp_from_str "AFOLMQWV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM381.


Module TM382.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1RC_0LA0RE_1LD---_1RF0LE_0RF0LC_0LC0RA".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_---0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_---1RA_0LW0RF_1LW0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1LS1LS_1RQ---_1LS0RQ_1LS1RQ_0LC0RU_1LC0LP_1RA---_1LS---_0LP---_1LP---_0RV0LP_1RV0LK_---0LS_1RA1LS_0RU0LP_1RU---_0LP0LK_0RA1LK_0LP0RA_---1RA_0LK0RF_1LK0RJ".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---_1LC---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RI_1LC1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQWV".
Definition mp' := mp_from_str "AFSPQUKJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM382.


Module TM383.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_1LC---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG0RN_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG0RN_0RQ---_1RQ---_0LL---_0RA---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---_1RF---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RI_1RF1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQWN".
Definition mp' := mp_from_str "AFOLMQWN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM383.


Module TM384.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG0RN_0RQ---_1RQ---_0LL---_0RA---".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_---0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_---1RA_0LW0RF_1LW0RN_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---_1RF---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RI_1RF1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQWN".
Definition mp' := mp_from_str "AFOLMQWN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM384.


Module TM385.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_---0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_---1RA_0LW0RF_1LW0RN_1RA---_1LO---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0RQ---_1RQ---_0LL---_0RA---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---_1RF---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RI_1RF1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQWN".
Definition mp' := mp_from_str "AFOLMQWV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM385.


Module TM386.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LW_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LW_0RA1LW_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0RQ---_1RQ---_0LL---_0RA---".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LX_0RQ0LO_1RA1LO_0RQ0LL_1RQ---_0LL0LX_0RA1LX_0LL0RA_0RQ1RA_0LG0RF_1LG0RN_0RI---_1RI---_0RR---_0LL---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD---_1RF---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RE_0LD0LG_1RA1LC_0RF0LD_0LD0RA_0LD1RI_1RF1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQWV".
Definition mp' := mp_from_str "AFOLMQXN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM386.


Module TM387.
Definition tm := TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_1RD---".
Definition tm' := TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0LA---".
Definition tm0 := TM'_from_str "1LK0RJ_---1RJ_0LH1RN_1LH1RA_1RA0RV_0LS1RV_0LK1RN_1LK---_0RN1LK_1RN1RA_1RA0LS_1RQ1LS_0RA0RQ_1RA1RQ_1LK0RA_0RJ0RE_0RA0RE_1RA1RE_1LK1RA_0RJ0RV_0RN---_1RN---_1RA---_1RQ---".
Definition tm0' := TM'_from_str "1LK0RJ_---1RJ_0LH1RN_1LH1RA_1RA0RV_0LS1RV_0LK1RN_1LK---_0RN1LK_1RN1RA_1RA0LS_1RQ1LS_0RA0RQ_1RA1RQ_1LK0RA_0RJ0RE_0RA0RE_1RA1RE_1LK1RA_0RJ0RV_0LH---_1RN---_0LC---_1LC---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0RD_1RB0LF_1RE1RB_1RB1RA_1LC1RB_1RB0RH_1RE---".
Definition tm2 := TM'_from_str "0RB0RG_1LC0RD_1RB0LF_1RE1RB_1RB1RA_1LC1RB_1RB0RH_1RE1RI_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "QAKJNSEV".
Definition mp' := mp_from_str "QAKJNSEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM387.


Module TM388.
Definition tm := TM_from_str "1LB1RC_0LC---_1RD0LE_0RA0RE_0RA0RF_0LC1RB".
Definition tm' := TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0LC---".
Definition tm0 := TM'_from_str "1LK0RJ_---1RJ_0LH1RN_1LH1RA_1RA---_0LS---_0LK---_1LK---_0RN1LK_1RN1RA_1RA0LS_1RQ1LS_0RA0RQ_1RA1RQ_1LK0RA_0RJ0RU_0RA0RU_1RA1RU_1LK1RA_0RJ0RF_1RA0RF_0LS1RF_0LK0LS_1LK---".
Definition tm0' := TM'_from_str "1LK0RJ_---1RJ_0LH1RN_1LH1RA_1RA0RV_0LS1RV_0LK0LS_1LK---_0RN1LK_1RN1RA_1RA0LS_1RQ1LS_0RA0RQ_1RA1RQ_1LK0RA_0RJ0RE_0RA0RE_1RA1RE_1LK1RA_0RJ0RV_1RA---_0LS---_0LK---_1LK---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0RD_1RB0LF_1RE1RB_1RB1RA_1LC1RB_1RB0RH_0LF---".
Definition tm2 := TM'_from_str "0RB0RG_1LC0RD_1RB0LF_1RE1RB_1RB1RA_1LC1RB_1RB0RH_0LF1RI_1RI1RI".
Definition l0 := [1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "QAKJNSUF".
Definition mp' := mp_from_str "QAKJNSEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM388.


Module TM389.
Definition tm := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA1LF_0LA---".
Definition tm' := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA0LF_1RD---".
Definition tm0 := TM'_from_str "1RI0LH_1LS0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ0LX_1RN0LS_1RI1LS_0RN0RI_1RN1RI_1LC0RN_1RE0RI_1LH0RE_1LC1RE_0LD0RJ_1LD0LD_1LH1LC_1LC---_0LD0LX_1LD1LX_0LH---_0LC---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1RI0LH_1LS0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ0LW_1RN0LS_1RI1LS_0RN0RI_1RN1RI_1LC0RN_1RE0RI_1LH0RE_1LC1RE_0LD0RJ_1LD0LD_1LH1LC_1LC---_0LD0LW_1LD1LW_0RN---_1RN---_1LC---_1RE---".
Definition tm1 := TM'_from_str "0RB0LG_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0LI_1LE1LD_0RC0RH_1LD---".
Definition tm2 := TM'_from_str "0RB0LG_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0LI_1LE1LD_0RC0RH_1LD1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "EJNCHSDIX".
Definition mp' := mp_from_str "EJNCHSDIW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM389.


Module TM390.
Definition tm := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA0LF_1RD---".
Definition tm' := TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA0RB_1LA0LF_1RE---".
Definition tm0 := TM'_from_str "1RI0LH_1LS0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ0LW_1RN0LS_1RI1LS_0RN0RI_1RN1RI_1LC0RN_1RE0RI_1LH0RE_1LC1RE_0LD0RJ_1LD0LD_1LH1LC_1LC---_0LD0LW_1LD1LW_0RN---_1RN---_1LC---_1RE---".
Definition tm0' := TM'_from_str "1RI0LH_1LS0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ0LW_1RN0LS_1RI1LS_0RN0RI_1RN1RI_1LC0RN_1RE0RI_1LH0RE_1LC1RE_0LD0RJ_1LD0LD_1LH1LC_1LC---_0LD0LW_1LD1LW_0RR---_1RR---_1LC---".
Definition tm1 := TM'_from_str "0RB0LG_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0LI_1LE1LD_0RC0RH_1LD---".
Definition tm2 := TM'_from_str "0RB0LG_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0LI_1LE1LD_0RC0RH_1LD1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "EJNCHSDIW".
Definition mp' := mp_from_str "EJNCHSDIW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM390.


Module TM391.
Definition tm := TM_from_str "1LB0LA_1RC0LD_1RD0RC_1LA0RE_1RC1RF_0RC---".
Definition tm' := TM_from_str "1LB---_1RC0LD_1RD0RC_1LE0RF_1LB0LE_1RC0RA".
Definition tm0 := TM'_from_str "1RI0LH_1LO0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ0RJ_1RN0LO_1RI1LO_0RN0RI_1RN1RI_1LC0RN_1RQ0RI_1LH0RQ_1LC1RQ_0LD0RJ_1LD0RV_0RJ0RV_1RJ1RV_1RN1RI_1RI---_0RI---_1RI---_0RN---_0RI---".
Definition tm0' := TM'_from_str "1RI---_1LO---_0LH---_1LH---_0RJ0LT_1RJ0RJ_1RN0LO_1RI1LO_0RN0RI_1RN1RI_1LS0RN_1RU0RI_1LH0RU_1LS1RU_0LT0RJ_1LT0RA_1RI0LH_1LO0LS_0LH0LS_1LH1LS_0RJ0RA_1RJ1RA_1RN1RI_1RI---".
Definition tm1 := TM'_from_str "0RB0RI_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0RB_1LE1LD_0RC0RH_1RH---".
Definition tm2 := TM'_from_str "0RB0RI_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0RB_1LE1LD_0RC0RH_1RH1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "QJNCHODIV".
Definition mp' := mp_from_str "UJNSHOTIA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM391.


Module TM392.
Definition tm := TM_from_str "1LB---_1RC0LD_1RD0RC_1LE0RF_1LB0LE_1RC0RA".
Definition tm' := TM_from_str "1LB---_1RC0RA_1RD0RC_1LE0RB_1LF0LE_1RC0LD".
Definition tm0 := TM'_from_str "1RI---_1LO---_0LH---_1LH---_0RJ0LT_1RJ0RJ_1RN0LO_1RI1LO_0RN0RI_1RN1RI_1LS0RN_1RU0RI_1LH0RU_1LS1RU_0LT0RJ_1LT0RA_1RI0LH_1LO0LS_0LH0LS_1LH1LS_0RJ0RA_1RJ1RA_1RN1RI_1RI---".
Definition tm0' := TM'_from_str "1RI---_------_0LH---_1LH---_0RJ0RA_1RJ1RA_1RN1RI_1RI---_0RN0RI_1RN1RI_1LS0RN_1RE0RI_1LX0RE_1LS1RE_0LT0RJ_1LT0RA_1RI0LX_1LO0LS_0LX0LS_1LX1LS_0RJ0LT_1RJ0RJ_1RN0LO_1RI1LO".
Definition tm1 := TM'_from_str "0RB0RI_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0RB_1LE1LD_0RC0RH_1RH---".
Definition tm2 := TM'_from_str "0RB0RI_1RC1RH_1LD1RA_0LE0LD_1RH1LF_0LG0RB_1LE1LD_0RC0RH_1RH1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "UJNSHOTIA".
Definition mp' := mp_from_str "EJNSXOTIA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM392.


Module TM393.
Definition tm := TM_from_str "1LB---_1RC1LB_1LE1RD_1RB0RC_1RF0LE_1LB0RA".
Definition tm' := TM_from_str "1LB1RF_1RC1LB_1LE1RD_1RB0RC_1RA0LE_1RD---".
Definition tm0 := TM'_from_str "1RN---_1LH---_0LH---_1LH---_0RJ1RN_1RJ1LH_1LS0LH_1RN1LH_1RA0RN_1LS1RN_0LT1RF_1LT1RI_0RF0RI_1RF1RI_1RJ1RA_1LH0RN_0RV1LH_1RV0LS_1LH0LS_1RA1LS_1RN0RA_1LH1RA_0LH1RN_1LH---".
Definition tm0' := TM'_from_str "1RN0RV_1LH1RV_0LH1RN_1LH---_0RJ1RN_1RJ1LH_1LS0LH_1RN1LH_1RV0RN_1LS1RN_0LT1RF_1LT1RI_0RF0RI_1RF1RI_1RJ1RV_1LH0RN_0RB1LH_1RB0LS_1LH0LS_1RV1LS_0RN---_1RN---_1RF---_1RI---".
Definition tm1 := TM'_from_str "1RB1LD_1LC1RE_1LD0LC_1RE1LD_1RA1RF_1RG0RE_1RE---".
Definition tm2 := TM'_from_str "1RB1LD_1LC1RE_1LD0LC_1RE1LD_1RA1RF_1RG0RE_1RE1RH_1RH1RH".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "FJSHNIA".
Definition mp' := mp_from_str "FJSHNIV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM393.


Module TM394.
Definition tm := TM_from_str "1LB1RF_1RC1LD_0RE1RA_1LB0LB_---1RD_1RA0RC".
Definition tm' := TM_from_str "1LB0LB_1RC1LA_0RE1RD_0LE1RF_---1RA_1RD0RC".
Definition tm0 := TM'_from_str "1RB0RV_1LP1RV_0LH1RB_1LH1RI_0RJ1LH_1RJ1LG_1RQ0LP_1RB1LP_0RQ0RB_1RQ1RB_---1LP_0RN1RV_1RB1RQ_1LP0LP_0LH0LG_1LH1LG_---0RN_---1RN_---1LP_---0LP_0RB0RI_1RB1RI_1LP0RQ_1RV0RB".
Definition tm0' := TM'_from_str "1RN1RQ_1LD0LD_0LH0LG_1LH1LG_0RJ1LH_1RJ1LG_1RQ0LD_1RN1LD_0RQ0RN_1RQ1RN_---1LD_0RB1RV_---0RV_1LD1RV_0LS1RN_1LS1RI_---0RB_---1RB_---1LD_---0LD_0RN0RI_1RN1RI_1LD0RQ_1RV0RN".
Definition tm1 := TM'_from_str "1LB1RE_1LD1LC_1RG0LB_1RA1LB_1RA1RF_0RG0RA_---0RH_1LB0LB".
Definition tm2 := TM'_from_str "1LB1RE_1LD1LC_1RG0LB_1RA1LB_1RA1RF_0RG0RA_1RI0RH_1LB0LB_1RI1RI".
Definition l0 := [1;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "BPGHVIQN".
Definition mp' := mp_from_str "NDGHVIQB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM394.


Module TM395.
Definition tm := TM_from_str "1RB1LF_1LC1RA_1LE0RD_1RC0RD_0RA0LC_0LE---".
Definition tm' := TM_from_str "1RB1LF_1LC1RA_1RD0RC_1LE0RC_0RA0LD_0LE---".
Definition tm0 := TM'_from_str "0RF1LS_1RF---_0RM0LX_1RB1LX_1LT0RB_0RM1RB_0LL1RF_1LL---_1LS0RM_1LK1RM_0LT0RJ_1LT0RM_0RJ0RM_1RJ1RM_1LK0RJ_1RM0RM_0RA0LT_1RA0RJ_0RF0LK_1LS1LK_0RF---_0LK---_0LS---_1LS---".
Definition tm0' := TM'_from_str "0RF1LS_1RF---_0RI0LX_1RB1LX_1RI0RB_0RI1RB_0LL1RF_1LL---_0RN0RI_1RN1RI_1LO0RN_1RI0RI_1LS0RI_1LO1RI_0LT0RN_1LT0RI_0RA0LT_1RA0RN_0RF0LO_1LS1LO_0RF---_0LO---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RA_0LD0RB_1LE1LC_0RF0LC_0RA1RG_1RF---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RA_0LD0RB_1LE1LC_0RF0LC_0RA1RG_1RF1RH_1RH1RH".
Definition l0 := [0;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "MJKTSFB".
Definition mp' := mp_from_str "INOTSFB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM395.


Module TM396.
Definition tm := TM_from_str "1RB1LF_1LC1RA_1RD0RC_1LE0RC_0RA0LD_0LE---".
Definition tm' := TM_from_str "1RB---_1LC1RA_1LE0RD_1RC0RD_0LF0LC_0RA0LC".
Definition tm0 := TM'_from_str "0RF1LS_1RF---_0RI0LX_1RB1LX_1RI0RB_0RI1RB_0LL1RF_1LL---_0RN0RI_1RN1RI_1LO0RN_1RI0RI_1LS0RI_1LO1RI_0LT0RN_1LT0RI_0RA0LT_1RA0RN_0RF0LO_1LS1LO_0RF---_0LO---_0LS---_1LS---".
Definition tm0' := TM'_from_str "0RF---_1RF---_0RM---_1RB---_1LT0RB_0RM1RB_0LL1RF_1LL---_1LW0RM_1LK1RM_0LT0RJ_1LT0RM_0RJ0RM_1RJ1RM_1LK0RJ_1RM0RM_0RF0LT_0LK0RJ_0LW0LK_1LW1LK_0RA0LT_1RA0RJ_0RF0LK_---1LK".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RA_0LD0RB_1LE1LC_0RF0LC_0RA1RG_1RF---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RA_0LD0RB_1LE1LC_0RF0LC_0RA1RG_1RF1RH_1RH1RH".
Definition l0 := [0;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "INOTSFB".
Definition mp' := mp_from_str "MJKTWFB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM396.


Module TM397.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LF---_1RA0LD".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1LB---_1RA1RF".
Definition tm0 := TM'_from_str "0RM1LH_1LG1LD_0LH0LD_1LH1LD_0RI0RV_1RI0LG_0RV0LG_0RM1LG_0RV0RM_1RV1RM_1RB0RQ_1RV0RJ_0RQ0RJ_1RQ1RJ_1LG1RV_---1RM_1LG---_0LO---_0LW---_1LW---_0RB1LG_1RB1RV_1LG0LO_1LD1LO".
Definition tm0' := TM'_from_str "0RM1LH_1LG1LD_0LH0LD_1LH1LD_0RI0RV_1RI0LG_0RV0LG_0RM1LG_0RV0RM_1RV1RM_1RB0RR_1RV0RJ_0RR0RJ_1RR1RJ_1LG1RV_---1RM_0RM---_1LG---_0LH---_1LH---_0RB0RV_1RB1RV_1LG1RB_1LD1RV".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LB---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LB1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BGVDHMJQ".
Definition mp' := mp_from_str "BGVDHMJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM397.


Module TM398.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1LB---_1RA1RF".
Definition tm' := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LF---_1RA1RF".
Definition tm0 := TM'_from_str "0RM1LH_1LG1LD_0LH0LD_1LH1LD_0RI0RV_1RI0LG_0RV0LG_0RM1LG_0RV0RM_1RV1RM_1RB0RR_1RV0RJ_0RR0RJ_1RR1RJ_1LG1RV_---1RM_0RM---_1LG---_0LH---_1LH---_0RB0RV_1RB1RV_1LG1RB_1LD1RV".
Definition tm0' := TM'_from_str "0RM1LH_1LG1LD_0LH0LD_1LH1LD_0RI0RV_1RI0LG_0RV0LG_0RM1LG_0RV0RM_1RV1RM_1RB0RQ_1RV0RJ_0RQ0RJ_1RQ1RJ_1LG1RV_---1RM_1LG---_1RB---_0LW---_1LW---_0RB0RV_1RB1RV_1LG1RB_1LD1RV".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LB---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LB1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BGVDHMJR".
Definition mp' := mp_from_str "BGVDHMJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM398.


Module TM399.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LF---_1RA1RF".
Definition tm' := TM_from_str "1LB---_0RC0LB_1RE0RD_1RA1RC_1RF0LD_1LB1LF".
Definition tm0 := TM'_from_str "0RM1LH_1LG1LD_0LH0LD_1LH1LD_0RI0RV_1RI0LG_0RV0LG_0RM1LG_0RV0RM_1RV1RM_1RB0RQ_1RV0RJ_0RQ0RJ_1RQ1RJ_1LG1RV_---1RM_1LG---_1RB---_0LW---_1LW---_0RB0RV_1RB1RV_1LG1RB_1LD1RV".
Definition tm0' := TM'_from_str "0RM---_1LG---_0LH---_1LH---_0RI0RR_1RI0LG_0RR0LG_0RM1LG_0RR0RM_1RR1RM_1RV0RB_1RR0RJ_0RB0RJ_1RB1RJ_1LG1RR_---1RM_0RV1LG_1RV1RR_1LG0LO_1LX1LO_0RM1LH_1LG1LX_0LH0LX_1LH1LX".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LB---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LB1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BGVDHMJQ".
Definition mp' := mp_from_str "VGRXHMJB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM399.


Module TM400.
Definition tm := TM_from_str "1LB1LD_0RC0RA_1RA1RC_1LA1RE_1LF0RD_---0LE".
Definition tm' := TM_from_str "1LB1LD_0RC1LA_1RA1RC_1LA1RE_1LF0RD_---0LE".
Definition tm0 := TM'_from_str "0RJ1LD_1LD1RM_0LH0LP_1LH1LP_0RI0RA_1RI1RA_0RB0RJ_0RJ1LD_0RB0RJ_1RB1RJ_1LD1RB_1RM1RJ_1LH0RR_1LP1RR_0LD1LS_1LD1RM_---0RM_1LS1RM_0LX1LH_1LX0RR_---0LX_---1LH_---0LS_---1LS".
Definition tm0' := TM'_from_str "0RJ1LD_1LD1RM_0LH0LP_1LH1LP_0RI1LH_1RI1LP_0RB0LD_0RJ1LD_0RB0RJ_1RB1RJ_1LD1RB_1RM1RJ_1LH0RR_1LP1RR_0LD1LS_1LD1RM_---0RM_1LS1RM_0LX1LH_1LX0RR_---0LX_---1LH_---0LS_---1LS".
Definition tm1 := TM'_from_str "1LB1RG_0LC1LD_---1LB_0RE1LH_1RF1RE_1LH1RG_1LD0RA_1LD1LI_1LH1RG".
Definition tm2 := TM'_from_str "1LB1RG_0LC1LD_1RJ1LB_0RE1LH_1RF1RE_1LH1RG_1LD0RA_1LD1LI_1LH1RG_1RJ1RJ".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "RSXHJBMDP".
Definition mp' := mp_from_str "RSXHJBMDP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM400.


Module TM401.
Definition tm := TM_from_str "1RB0LD_1LC0RE_1LA0RD_1LC1LD_---0RF_0RB1RA".
Definition tm' := TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_0RB1RA_1LC1LF".
Definition tm0 := TM'_from_str "0RF0LL_1RF0LP_1LL0LO_1RQ1LO_1LD0RQ_1LL1RQ_0LL---_1LL0RU_1RQ0RM_1LO1RM_0LD1LD_1LD1LL_1LD1LL_1LL1LP_0LL0LP_1LL1LP_---0RU_---1RU_---0RE_---0RB_0RE0RB_1RE1RB_1LD1RF_0RQ0LP".
Definition tm0' := TM'_from_str "0RF0LL_1RF0LX_1LL0LW_1RM1LW_1LD0RM_1LL1RM_0LL---_1LL0RQ_1RM1LD_1LW1LL_0LD0LL_1LD1LL_---0RQ_---1RQ_---0RE_---0RB_0RE0RB_1RE1RB_1LD1RF_0RM0LX_1LD1LL_1LL1LX_0LL0LX_1LL1LX".
Definition tm1 := TM'_from_str "1LB1RD_1LC1LB_1RD1LH_---0RE_0RI0RF_1RA0LG_1LB1LG_0LB0LG_1LC0RD".
Definition tm2 := TM'_from_str "1LB1RD_1LC1LB_1RD1LH_1RJ0RE_0RI0RF_1RA0LG_1LB1LG_0LB0LG_1LC0RD_1RJ1RJ".
Definition l0 := [1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_str "FLDQUBPOE".
Definition mp' := mp_from_str "FLDMQBXWE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM401.


Module TM402.
Definition tm := TM_from_str "1LB0LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_1RD---".
Definition tm' := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0RA_0LB---".
Definition tm0 := TM'_from_str "1RI1LG_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LW0LT_0LD0LG_1LD1LG_0RN---_1RN---_1LG---_0LT---".
Definition tm0' := TM'_from_str "1RI1LG_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH0RA_1LX1RA_0LD1RI_1LD1LG_1RM---_0LT---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDWHI".
Definition mp' := mp_from_str "MPGTDXHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM402.


Module TM403.
Definition tm := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0RA_0LB---".
Definition tm' := TM_from_str "1LB0LF_1RC1LE_0RD0RC_1LD0LB_1LA0RA_1RD---".
Definition tm0 := TM'_from_str "1RI1LG_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH0RA_1LX1RA_0LD1RI_1LD1LG_1RM---_0LT---_0LG---_1LG---".
Definition tm0' := TM'_from_str "1RI1LG_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH0RA_1LW1RA_0LD1RI_1LD1LG_0RN---_1RN---_1LG---_0LT---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDXHI".
Definition mp' := mp_from_str "MPGTDWHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM403.


Module TM404.
Definition tm := TM_from_str "1LB0LF_1RC1LE_0RD0RC_1LD0LB_1LA0RA_1RD---".
Definition tm' := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_0LB---".
Definition tm0 := TM'_from_str "1RI1LG_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH0RA_1LW1RA_0LD1RI_1LD1LG_0RN---_1RN---_1LG---_0LT---".
Definition tm0' := TM'_from_str "1RI1LG_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LX0LT_0LD0LG_1LD1LG_1RM---_0LT---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDWHI".
Definition mp' := mp_from_str "MPGTDXHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM404.


Module TM405.
Definition tm := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_0LB---".
Definition tm' := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_1RB---".
Definition tm0 := TM'_from_str "1RI1LG_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LX0LT_0LD0LG_1LD1LG_1RM---_0LT---_0LG---_1LG---".
Definition tm0' := TM'_from_str "1RI1LG_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LX0LT_0LD0LG_1LD1LG_0RF---_1RF---_1RJ---_1LG---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LC1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDXHI".
Definition mp' := mp_from_str "MPGTDXHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM405.


Module TM406.
Definition tm := TM_from_str "1LB0LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_1RA---".
Definition tm' := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_1LE---".
Definition tm0 := TM'_from_str "1RI1LT_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LW0LT_0LD0LG_1LD1LG_0RB---_1RB---_1LT---".
Definition tm0' := TM'_from_str "1RI1LT_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LX0LT_0LD0LG_1LD1LG_1LD---_1LG---_0LT---_1LT---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LD---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LD1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDWHI".
Definition mp' := mp_from_str "MPGTDXHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM406.


Module TM407.
Definition tm := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_0RB---".
Definition tm' := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_0RA0LB_1LA---".
Definition tm0 := TM'_from_str "1RI1LD_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LX0LT_0LD0LG_1LD1LG_0RE---_1RE---_0RJ---_1LD---".
Definition tm0' := TM'_from_str "1RI1LD_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_0RA1RM_1RA0LT_1RI0LG_1LD1LG_1LH---_1LX---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LE---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LE1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDXHI".
Definition mp' := mp_from_str "MPGTDXHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM407.


Module TM408.
Definition tm := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_0RA0LB_1LA---".
Definition tm' := TM_from_str "1LB1LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_1LA---".
Definition tm0 := TM'_from_str "1RI1LD_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_0RA1RM_1RA0LT_1RI0LG_1LD1LG_1LH---_1LX---_0LD---_1LD---".
Definition tm0' := TM'_from_str "1RI1LD_1LT---_0LH0LX_1LH1LX_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LX0LT_0LD0LG_1LD1LG_1LH---_1LX---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LE---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LE1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDXHI".
Definition mp' := mp_from_str "MPGTDXHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM408.


Module TM409.
Definition tm := TM_from_str "1LB---_1RC1LE_0RD0RC_1LD0LB_1LF0LB_1LB1LA".
Definition tm' := TM_from_str "1LB0LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_0RE---".
Definition tm0 := TM'_from_str "1RI---_1LT---_0LH---_1LH---_0RJ1LX_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LD0LT_0LX0LG_1LX1LG_1RI1LH_1LT---_0LH0LD_1LH1LD".
Definition tm0' := TM'_from_str "1RI1LH_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LW0LT_0LD0LG_1LD1LG_0RQ---_1RQ---_1LH---_1RM---".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LG---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LG1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTXDHI".
Definition mp' := mp_from_str "MPGTDWHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM409.


Module TM410.
Definition tm := TM_from_str "1LB0LF_1RC1LE_0RD0RC_1LD0LB_1LA0LB_0RE---".
Definition tm' := TM_from_str "1LB---_1RC1LE_0RD0RC_1LD0LB_1LF0LB_0RF1LA".
Definition tm0 := TM'_from_str "1RI1LH_1LT---_0LH0LW_1LH1LW_0RJ1LD_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LW0LT_0LD0LG_1LD1LG_0RQ---_1RQ---_1LH---_1RM---".
Definition tm0' := TM'_from_str "1RI---_1LT---_0LH---_1LH---_0RJ1LX_1RJ1LG_1RM0LT_1RI1LT_0RM0RI_1RM1RI_1LP0RM_1RM0RI_1LP1RM_1LG0LT_0LP0LG_1LP1LG_1LH1RM_1LD0LT_0LX0LG_1LX1LG_0RU1LH_1RU---_0RU0LD_1LH1LD".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LG---_1RH1LD_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LC_1LG1LF_1LG1RI_1RH1LD_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MPGTDWHI".
Definition mp' := mp_from_str "MPGTXDHI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM410.


Module TM411.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1RD0LF_1LA0LC_1LD0LA_---1RB".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE".
Definition tm0 := TM'_from_str "0RF1LP_1RF1LC_1RJ0LT_1RE1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RJ0RE_0RN---_1RN1RJ_1LT0LW_0LW1LW_1RE1LT_1LT0LW_0LD0LK_1LD1LK_1LD1RJ_1LK0LT_0LP0LC_1LP1LC_---0RF_---1RF_---1RJ_---1RE".
Definition tm0' := TM'_from_str "0RF1LP_1RF1LC_1RJ0LT_1RE1LT_0RJ0RE_1RJ1RE_1RN0RJ_1RJ0RE_0RN---_1RN1RJ_1LT0LX_0LX1LX_1RE1LT_1LT0LX_0LD0LK_1LD1LK_1LD1RJ_1LK0LT_0LP0LC_1LP1LC_---0RQ_---1RQ_---1LD_---1RJ".
Definition tm1 := TM'_from_str "1LB0LE_1LF1LC_1RD0LB_1RA1RD_---1RD_1LH1LG_1LB0LE_1RI1LB_0RD0RI".
Definition tm2 := TM'_from_str "1LB0LE_1LF1LC_1RD0LB_1RA1RD_1RJ1RD_1LH1LG_1LB0LE_1RI1LB_0RD0RI_1RJ1RJ".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "NTCJWPKDE".
Definition mp' := mp_from_str "NTCJXPKDE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM411.


Module TM412.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA0RE_1RF---_1LF1RB".
Definition tm' := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA0RE_1RF---_0LD1RB".
Definition tm0 := TM'_from_str "1RE0LH_1LO0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ0RV_1RM0LO_1RE1LO_0RM0RE_1RM1RE_1LH0RJ_0RQ0LD_1LH0RQ_1LC1RQ_0LD0RV_1LD---_0RV---_1RV---_0RV---_1RF---_1LX0RF_0RV1RF_0LX1RJ_1LX0RV".
Definition tm0' := TM'_from_str "1RE0LH_1LO0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ0RV_1RM0LO_1RE1LO_0RM0RE_1RM1RE_1LH0RJ_0RQ0LD_1LH0RQ_1LC1RQ_0LD0RV_1LD---_0RV---_1RV---_0RV---_1RF---_0LD0RF_0RV1RF_0LO1RJ_1LO0RV".
Definition tm1 := TM'_from_str "1RB1RG_1LC0RH_1RG1LD_0LE0RI_1LC1LF_0LC0LF_0RA0LE_0RI---_0RI1RJ_1RA0RI".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RH_1RG1LD_0LE0RI_1LC1LF_0LC0LF_0RA0LE_0RI1RK_0RI1RJ_1RA0RI_1RK1RK".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JMHODCEQVF".
Definition mp' := mp_from_str "JMHODCEQVF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM412.


Module TM413.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0LE1RF_0RC---".
Definition tm' := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0RC1RF_0LD---".
Definition tm0 := TM'_from_str "1RE0LH_1LO0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ1RI_1RM0LO_1RE1LO_0RM0RE_1RM1RE_1LH0RJ_0RR0LD_1LH0RR_1LC1RR_0LD1RI_1LD1RV_0LS0RV_1RI1RV_0LS1RI_1LS---_0RI---_1RI---_0RM---_0RE---".
Definition tm0' := TM'_from_str "1RE0LH_1LO0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ1RI_1RM0LO_1RE1LO_0RM0RE_1RM1RE_1LH0RJ_0RR0LD_1LH0RR_1LC1RR_0LD1RI_1LD1RV_0RI0RV_1RI1RV_0RM1RI_0RE---_0LD---_1RI---_0LO---_1LO---".
Definition tm1 := TM'_from_str "1RB1RG_1LC0RH_1RG1LD_0LE1RI_1LC1LF_0LC0LF_0RA0LE_1RI1RJ_0RB0RG_1RI---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RH_1RG1LD_0LE1RI_1LC1LF_0LC0LF_0RA0LE_1RI1RJ_0RB0RG_1RI1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JMHODCERIV".
Definition mp' := mp_from_str "JMHODCERIV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM413.


Module TM414.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0RC1RF_0LD---".
Definition tm' := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA1RE_0RC1RF_0RC---".
Definition tm0 := TM'_from_str "1RE0LH_1LO0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ1RI_1RM0LO_1RE1LO_0RM0RE_1RM1RE_1LH0RJ_0RR0LD_1LH0RR_1LC1RR_0LD1RI_1LD1RV_0RI0RV_1RI1RV_0RM1RI_0RE---_0LD---_1RI---_0LO---_1LO---".
Definition tm0' := TM'_from_str "1RE0LH_1LO0LC_0LH0LC_1LH1LC_0RJ0LD_1RJ1RI_1RM0LO_1RE1LO_0RM0RE_1RM1RE_1LH0RJ_0RR0LD_1LH0RR_1LC1RR_0LD1RI_1LD1RV_0RI0RV_1RI1RV_0RM1RI_0RE---_0RI---_1RI---_0RM---_0RE---".
Definition tm1 := TM'_from_str "1RB1RG_1LC0RH_1RG1LD_0LE1RI_1LC1LF_0LC0LF_0RA0LE_1RI1RJ_0RB0RG_1RI---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RH_1RG1LD_0LE1RI_1LC1LF_0LC0LF_0RA0LE_1RI1RJ_0RB0RG_1RI1RK_1RK1RK".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "JMHODCERIV".
Definition mp' := mp_from_str "JMHODCERIV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM414.


Module TM415.
Definition tm := TM_from_str "1LB1RA_1RC0LE_1RF1RD_0LA0RC_1RB1LA_---0RA".
Definition tm' := TM_from_str "1LB0RC_1RC0LD_1RF1RA_1RB1LE_1LB1RE_---0RE".
Definition tm0 := TM'_from_str "1RN0RB_1LS1RB_0LH1LS_1LH1RB_0RJ1RJ_1RJ0LD_1RV0LS_1RN1LS_0RV0RN_1RV1RN_---1LS_1RA1RI_0LH0RI_1LS1RI_0LC0RV_1LC0RN_0RF1LH_1RF1RB_1RJ0LD_0LD1LD_---0RA_---1RA_---1RN_---0RB".
Definition tm0' := TM'_from_str "1RB0RI_1LO1RI_0LH0RV_1LH0RB_0RJ1RJ_1RJ0LT_1RV0LO_1RB1LO_0RV0RB_1RV1RB_---1LO_1RQ1RI_0RF1LH_1RF1RR_1RJ0LT_0LT1LT_1RB0RR_1LO1RR_0LH1LO_1LH1RR_---0RQ_---1RQ_---1RB_---0RR".
Definition tm1 := TM'_from_str "1LB1RG_1RC0LD_1RH1RA_1LF1RE_1LB1RE_1RA1LB_0RH0RA_---1RI_1RA0RE".
Definition tm2 := TM'_from_str "1LB1RG_1RC0LD_1RH1RA_1LF1RE_1LB1RE_1RA1LB_0RH0RA_1RJ1RI_1RA0RE_1RJ1RJ".
Definition l0 := [1;1;0;1;1;1;1;0]%N.
Definition mp := mp_from_str "NSJDBHIVA".
Definition mp' := mp_from_str "BOJTRHIVQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM415.


Module TM416.
Definition tm := TM_from_str "1RB1RE_0LC0RE_1RD1LC_---1LA_1RA0LF_0RC1LE".
Definition tm' := TM_from_str "1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_0LL1RB_1RQ0LT_---0RQ_0LL1RQ_0LK0RB_1LK0RN_0RN0LT_1RN1LL_---0LL_0LT1LL_---1RQ_---0LT_---0LD_---1LD_0RB0RN_1RB0LT_1RF0LW_1RR1LW_0RI1RR_1RI1LW_0RN0LT_0LT1LT".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_0LL1RB_1RU0LX_---0RU_0LL1RU_0LK0RB_1LK0RN_0RN0LX_1RN1LL_---0LL_0LX1LL_---0RN_---0LX_---0LS_---1LS_0RI1RV_1RI1LS_0RN0LX_0LX1LX_0RB0RN_1RB0LX_1RF0LS_1RV1LS".
Definition tm1 := TM'_from_str "0LB1RH_0LC1LB_1RE1LD_0RG0LC_1RF0LC_1RA1RE_---0LC_0RF0RG".
Definition tm2 := TM'_from_str "0LB1RH_0LC1LB_1RE1LD_0RG0LC_1RF0LC_1RA1RE_1RI0LC_0RF0RG_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "FLTWRBNQ".
Definition mp' := mp_from_str "FLXSVBNU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM416.


Module TM417.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_1LB---".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB1LF_0RB0LE_0RC---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LO1RE_1RA0LS_1LD0RA_1LO1RA_0LL0RF_1LL0RR_1RA0LH_0LS0LW_0LD0LO_1LD1LO_1LL0LH_0RR---_0LH0LW_1LH1LW_0RE1LD_1RE0LS_1LD0LS_0RA1LS_1LL---_0RR---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LO1RE_1RA0LS_1LD0RA_1LO1RA_0LL0RF_1LL0RR_1RA0LH_0LS0LX_0LD0LO_1LD1LO_1LL0LH_0RR---_0LH0LX_1LH1LX_0RE1LD_1RE0LS_1LD0LS_0RA1LS_0RI---_1RI---_1RA---_0LH---".
Definition tm1 := TM'_from_str "1LB0RD_1RD0LC_1LB0LC_0RF0RE_1RA0LC_1LG1RD_0LH0LJ_1LI0RE_1LB1LG_0LH---".
Definition tm2 := TM'_from_str "1LB0RD_1RD0LC_1LB0LC_0RF0RE_1RA0LC_1LG1RD_0LH0LJ_1LI0RE_1LB1LG_0LH1RK_1RK1RK".
Definition l0 := [0;1;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "EDSARFOHLW".
Definition mp' := mp_from_str "EDSARFOHLX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM417.


Module TM418.
Definition tm := TM_from_str "1RB1RA_0RC0RD_1LD1RA_0LE---_0RA0LF_1LE0LE".
Definition tm' := TM_from_str "1RB1RA_0RC0RD_1LD1LE_0LE---_0RA0LF_1LE0LE".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1RI1RF_1RM1RB_0RI0RM_1RI1RM_1LS0RF_0RB---_1LS0RB_---1RB_0LP1RF_1LP1RB_0RF---_0LW---_0LS---_1LS---_0RA0LT_1RA0LS_0RF0LW_0RB1LW_0RB0RF_1LW0LW_0LT0LS_1LT1LS".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1RI1RF_1RM1RB_0RI0RM_1RI1RM_1LS0RF_0RB---_1LS0RB_---1LW_0LP0LT_1LP1LT_0RF---_0LW---_0LS---_1LS---_0RA0LT_1RA0LS_0RF0LW_0RB1LW_0RB0RF_1LW0LW_0LT0LS_1LT1LS".
Definition tm1 := TM'_from_str "1RB1RG_1LC0RF_0RA0LD_0LE0LC_0RF1LD_1RA1RF_0RA---".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RF_0RA0LD_0LE0LC_0RF1LD_1RA1RF_0RA1RH_1RH1RH".
Definition l0 := [0;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "FISWTBM".
Definition mp' := mp_from_str "FISWTBM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM418.


Module TM419.
Definition tm := TM_from_str "1RB0RF_1LC0RD_---1LD_0LE1LD_1LA1LB_1RA1RF".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_---1RD_0LE1LD_1LA1LB_1RA1RF".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LP0RB_1RM0RV_---0RM_1LP1RM_0LL0LD_1LL1LS_---1LS_---1LP_---0LP_---1LP_0LD1LS_0LH1LP_0LS0LP_1LS1LP_1RM1LL_0RV1LS_0LD0LH_1LD1LH_0RB0RV_1RB1RV_1RF1RB_1RU1RV".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LP0RB_1RM0RV_---0RM_1LP1RM_0LL0LD_1LL1LS_---0RN_---1RN_---0LH_---1LP_0LD1LS_0LH1LP_0LS0LP_1LS1LP_1RM1LL_0RV1LS_0LD0LH_1LD1LH_0RB0RV_1RB1RV_1RF1RB_1RU1RV".
Definition tm1 := TM'_from_str "1RB1RA_1RC1RJ_1LD1RI_1LE1LD_0LH0LF_1LG1LE_---1LD_1RI0RA_0LH1LE_0RB0RA".
Definition tm2 := TM'_from_str "1RB1RA_1RC1RJ_1LD1RI_1LE1LD_0LH0LF_1LG1LE_1RK1LD_1RI0RA_0LH1LE_0RB0RA_1RK1RK".
Definition l0 := [0;1;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "VBFPSHLDMU".
Definition mp' := mp_from_str "VBFPSHLDMU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM419.


Module TM420.
Definition tm := TM_from_str "1LB---_1LC0RC_0RD0LF_1LE1RD_0RE1RB_1LB0LA".
Definition tm' := TM_from_str "1LB---_1LC0RC_0RD0LF_1RB1RE_0RC1RE_1LB0LA".
Definition tm0 := TM'_from_str "1LL---_0LH---_0LH---_1LH---_0RN0RI_1LW1RI_0LL0RM_1LL0LH_0RM0LH_1RM0LC_0RF0LW_0RN1LW_0RF0RN_1RI1RN_0LT1RI_1LT1RN_0RQ0RF_1RQ1RF_0RQ1LW_0RF1RI_1LL0LH_0LH---_0LH0LC_1LH1LC".
Definition tm0' := TM'_from_str "1LL---_0LH---_0LH---_1LH---_0RR0RI_1LW1RI_0LL0RM_1LL0LH_0RM0LH_1RM0LC_0RF0LW_0RR1LW_0RF0RR_1RF1RR_1LW1RI_1RI1RR_0RI0RR_1RI1RR_0RM1RI_0LH1RR_1LL0LH_0LH---_0LH0LC_1LH1LC".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC---_1RG1RF_0RH0LC_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC1RI_1RG1RF_0RH0LC_0RA0RF_1RI1RI".
Definition l0 := [0;1;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "FWHLCNIM".
Definition mp' := mp_from_str "FWHLCRIM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM420.


Module TM421.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD1LC_1RB0LC_0RF1RB_---1RE".
Definition tm' := TM_from_str "1RB0LC_1LC1RD_1LA1LC_1LF0RE_0RF1RB_---1RE".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LL0RU_1RB0RF_1LP0RB_1LL1RB_0LL1RF_1LL1RQ_1RB1LP_1LK1LL_0LP0LL_1LP1LL_0RF0LP_1RF0LL_1LL0LK_1RB1LK_0RU0RF_1RU1RF_---1LL_0RR1RB_---0RR_---1RR_---1RU_---1RF".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LL_1LL0LK_1RN1LK_1LD0RN_1LL1RN_0LL1RF_1LL1RQ_1RN1LD_1LK1LL_0LD0LL_1LD1LL_---0RQ_1RF1RQ_0LX0RU_1LX0RF_0RU0RF_1RU1RF_---1LL_0RR1RN_---0RR_---1RR_---1RU_---1RF".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LB_1RE1LD_0LC0LB_1RA1RF_0RG0RA_---0RH_1RG1RA".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LB_1RE1LD_0LC0LB_1RA1RF_0RG0RA_1RI0RH_1RG1RA_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "FLPKBQUR".
Definition mp' := mp_from_str "FLDKNQUR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM421.


Module TM422.
Definition tm := TM_from_str "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA".
Definition tm0 := TM'_from_str "0RF1LC_1RF1LD_1RI0LX_1RN1LX_0RI0RN_1RI1RN_1RN1LL_1LT1RA_1RN1LT_1LX1LC_0LD0LP_1LD1LP_---0RA_1LL1RA_0LT0RF_1LT1LC_---1LD_---1LP_---0LL_---1LL_1RI0RQ_0LX1RQ_0LC---_1LC1LD".
Definition tm0' := TM'_from_str "0RF1LC_1RF1LD_1RI0LX_1RN1LX_0RI0RN_1RI1RN_1RN1LL_1LT1RA_1RN1LT_1LX1LC_0LD0LP_1LD1LP_---0RA_1LL1RA_0LT0RF_1LT1LC_---1LD_---1LP_---0LL_---1LL_1RI1RN_0LX1LX_0LC0LD_1LC1LD".
Definition tm1 := TM'_from_str "1RB1RC_1RC1LG_1LD1RJ_1LI1LE_1LG1LF_1RB0LH_---1LD_1LF1LI_1RC1LH_0RA1LF".
Definition tm2 := TM'_from_str "1RB1RC_1RC1LG_1LD1RJ_1LI1LE_1LG1LF_1RB0LH_1RK1LD_1LF1LI_1RC1LH_0RA1LF_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "FINLPCTXDA".
Definition mp' := mp_from_str "FINLPCTXDA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM422.


Module TM423.
Definition tm := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1LF_0RF1RC".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_1RE0LB_---0LF_1RC0RF".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LP1RQ_1RI0RB_1RN0RI_1LP1RI_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RB_---0LG_0RJ1LG_---0RJ_---1LG_---0LX_---1LX_0RU0RJ_1RU1RJ_0RU1RB_0RJ1LG".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LP1RR_1RI0RB_1RN0RI_1LP1RI_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RR0LL_1RR0RB_---0LG_0RJ1LG_---1RB_---0RJ_---0LW_---1LW_0RJ0RU_1RJ1RU_1RB0RJ_1LG0RU".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_---0RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_1RJ0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "BFPGLNIJQ".
Definition mp' := mp_from_str "BFPGLNIJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM423.


Module TM424.
Definition tm := TM_from_str "1RB1RD_1LC0RC_1RA1LD_1RE0LB_---0LF_1RC0RF".
Definition tm' := TM_from_str "1RB---_1LC0RC_1RF1LD_0RE0LB_---1RC_1RB1RD".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LP1RR_1RI0RB_1RN0RI_1LP1RI_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RR0LL_1RR0RB_---0LG_0RJ1LG_---1RB_---0RJ_---0LW_---1LW_0RJ0RU_1RJ1RU_1RB0RJ_1LG0RU".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LP---_1RI---_1RN0RI_1LP1RI_0LL0RV_1LL0RJ_0RV0RJ_1RV1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RV_---0LG_0RJ1LG_---0RJ_---1RJ_---1RV_---1LG_0RF0RN_1RF1RN_1LP1RQ_1RI0RV".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_---0RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_1RJ0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "BFPGLNIJR".
Definition mp' := mp_from_str "VFPGLNIJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM424.


Module TM425.
Definition tm := TM_from_str "1RB---_1LC0RC_1RF1LD_0RE0LB_---1RC_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_1LC0RF_1RA1LD_1RE0LB_---1LB_1RA1RC".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LP---_1RI---_1RN0RI_1LP1RI_0LL0RV_1LL0RJ_0RV0RJ_1RV1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RV_---0LG_0RJ1LG_---0RJ_---1RJ_---1RV_---1LG_0RF0RN_1RF1RN_1LP1RQ_1RI0RV".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LP1RR_1RU0RB_1RN0RU_1LP1RU_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RR0LL_1RR0RB_---0LG_0RJ1LG_---1LL_---0RJ_---0LH_---1LH_0RB0RJ_1RB1RJ_1RF1RB_1RN1LG".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_---0RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_1RJ0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "VFPGLNIJQ".
Definition mp' := mp_from_str "BFPGLNUJR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM425.


Module TM426.
Definition tm := TM_from_str "1RB1RD_1LC0RF_1RA1LD_1RE0LB_---1LB_1RA1RC".
Definition tm' := TM_from_str "1RB0LF_1LC0RC_1RA1LD_0RE0LB_---1RC_1RD1RF".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LP1RR_1RU0RB_1RN0RU_1LP1RU_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RR0LL_1RR0RB_---0LG_0RJ1LG_---1LL_---0RJ_---0LH_---1LH_0RB0RJ_1RB1RJ_1RF1RB_1RN1LG".
Definition tm0' := TM'_from_str "0RF1RQ_1RF1RN_1LP0LW_1RI1LW_1RN0RI_1LP1RI_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RB_---0LG_0RJ1LG_---0RJ_---1RJ_---1RB_---1LG_0RN0RV_1RN1RV_1RQ1RN_0RB1RV".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_---0RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_1RJ0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "BFPGLNUJR".
Definition mp' := mp_from_str "BFPGLNIJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM426.


Module TM427.
Definition tm := TM_from_str "1RB0LF_1LC0RC_1RA1LD_0RE0LB_---1RC_1RD1RF".
Definition tm' := TM_from_str "1RB1RD_1LC0RF_1RA1LD_0RE0LB_---1RC_1RA1RC".
Definition tm0 := TM'_from_str "0RF1RQ_1RF1RN_1LP0LW_1RI1LW_1RN0RI_1LP1RI_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RB_---0LG_0RJ1LG_---0RJ_---1RJ_---1RB_---1LG_0RN0RV_1RN1RV_1RQ1RN_0RB1RV".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LP1RQ_1RU0RB_1RN0RU_1LP1RU_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RB_---0LG_0RJ1LG_---0RJ_---1RJ_---1RB_---1LG_0RB0RJ_1RB1RJ_1RF1RB_1RN1LG".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_---0RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_1RJ0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "BFPGLNIJQ".
Definition mp' := mp_from_str "BFPGLNUJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM427.


Module TM428.
Definition tm := TM_from_str "1RB1RD_1LC0RF_1RA1LD_0RE0LB_---1RC_1RA1RC".
Definition tm' := TM_from_str "1RB1RA_1LC0RC_1RF1LD_0RE0LB_---1RC_0LA1RD".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LP1RQ_1RU0RB_1RN0RU_1LP1RU_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RB_---0LG_0RJ1LG_---0RJ_---1RJ_---1RB_---1LG_0RB0RJ_1RB1RJ_1RF1RB_1RN1LG".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LP1RF_1RI1RB_1RN0RI_1LP1RI_0LL0RV_1LL0RJ_0RV0RJ_1RV1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RV_---0LG_0RJ1LG_---0RJ_---1RJ_---1RV_---1LG_1LP0RN_1RF1RN_0LC1RQ_1LC0RV".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_---0RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_1RJ0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "BFPGLNUJQ".
Definition mp' := mp_from_str "VFPGLNIJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM428.


Module TM429.
Definition tm := TM_from_str "1RB0LC_1LA1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm' := TM_from_str "1RB1LC_1LA1RE_0RD1RF_0RA0LB_0RC---_0RA0LA".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LK_1LK0LK_1RN1LK_1RN0RN_1LK1RN_0LD1RQ_1LD---_1RN0LD_1LK0LK_0LD0LK_1LD1LK_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RA1RA_0LD0LK_0RA0LD_1RA0LK_0RF0LK_0LD1LK".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LL_1LL0LL_1RR1LL_1RR0RR_1LL1RR_0LD1RI_1LD---_0RM0RV_1RM1RV_0RA1RA_0LD0LL_0RA0LD_1RA1RI_0RF0LG_0LD1LG_0RI---_1RI---_0RM---_0RV---_0RA1LL_1RA0LL_0RF0LC_0LD1LC".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA---_1RC0LE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA1RI_1RC0LE_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QUAFKDNV".
Definition mp' := mp_from_str "IMAFLDRV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM429.


Module TM430.
Definition tm := TM_from_str "1RB1LC_1LA1RE_0RD1RF_0RA0LB_0RC---_0RA0LA".
Definition tm' := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA1LC_0RC---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LL_1LL0LL_1RR1LL_1RR0RR_1LL1RR_0LD1RI_1LD---_0RM0RV_1RM1RV_0RA1RA_0LD0LL_0RA0LD_1RA1RI_0RF0LG_0LD1LG_0RI---_1RI---_0RM---_0RV---_0RA1LL_1RA0LL_0RF0LC_0LD1LC".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LL_1LL0LL_1RV1LL_1RV0RV_1LL1RV_0LD1RI_1LD---_0RM0RN_1RM1RN_0RA1RA_0LD0LL_0RA0LD_1RA0LL_0RF0LS_0LD1LS_1RV0LD_1LL0LL_0LD0LL_1LD1LL_0RI---_1RI---_0RM---_0RN---".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA---_1RC0LE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA1RI_1RC0LE_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "IMAFLDRV".
Definition mp' := mp_from_str "IMAFLDVN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM430.


Module TM431.
Definition tm := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA1LC_0RC---".
Definition tm' := TM_from_str "1RB0LC_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LL_1LL0LL_1RV1LL_1RV0RV_1LL1RV_0LD1RI_1LD---_0RM0RN_1RM1RN_0RA1RA_0LD0LL_0RA0LD_1RA0LL_0RF0LS_0LD1LS_1RV0LD_1LL0LL_0LD0LL_1LD1LL_0RI---_1RI---_0RM---_0RN---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LK_1LK0LK_1RN1LK_1LD0RN_1LK1RN_0LL1RQ_1LL---_1RN0LD_1LK0LK_0LD0LK_1LD1LK_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RA1RA_0LD0LK_0RA0LD_1RA0LK_0RF0LK_0LD1LK".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA---_1RC0LE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA1RI_1RC0LE_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "IMAFLDVN".
Definition mp' := mp_from_str "QUAFKDNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM431.


Module TM432.
Definition tm := TM_from_str "1RB0LC_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm' := TM_from_str "1RB0LD_1LC1RE_0RA0LD_1LA0LD_0RF---_0RC1RC".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LK_1LK0LK_1RN1LK_1LD0RN_1LK1RN_0LL1RQ_1LL---_1RN0LD_1LK0LK_0LD0LK_1LD1LK_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RA1RA_0LD0LK_0RA0LD_1RA0LK_0RF0LK_0LD1LK".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LO_1LO0LO_1RR1LO_0LD0RR_1LO1RR_0LL1RU_1LL---_0RA0LD_1RA0LO_0RF0LO_0LD1LO_1RR0LD_1LO0LO_0LD0LO_1LD1LO_0RU---_1RU---_0RI---_0RJ---_0RI0RJ_1RI1RJ_0RA1RA_0LD0LO".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA---_1RC0LE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA1RI_1RC0LE_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QUAFKDNV".
Definition mp' := mp_from_str "UIAFODRJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM432.


Module TM433.
Definition tm := TM_from_str "1RB0LD_1LC1RE_0RA0LD_1LA0LD_0RF---_0RC1RC".
Definition tm' := TM_from_str "1RB1LD_1LC1RF_1LA1LD_0RE1RE_0RA0LC_0RD---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LO_1LO0LO_1RR1LO_0LD0RR_1LO1RR_0LL1RU_1LL---_0RA0LD_1RA0LO_0RF0LO_0LD1LO_1RR0LD_1LO0LO_0LD0LO_1LD1LO_0RU---_1RU---_0RI---_0RJ---_0RI0RJ_1RI1RJ_0RA1RA_0LD0LO".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LP_1LP0LP_1RV1LP_1LD0RV_1LP1RV_0LL1RM_1LL---_1RV0LD_1LP0LP_0LD0LP_1LD1LP_0RQ0RR_1RQ1RR_0RA1RA_0LD0LP_0RA0LD_1RA0LP_0RF0LK_0LD1LK_0RM---_1RM---_0RQ---_0RR---".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA---_1RC0LE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LE_1RA1RI_1RC0LE_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "UIAFODRJ".
Definition mp' := mp_from_str "MQAFPDVR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM433.


Module TM434.
Definition tm := TM_from_str "1RB0LC_1LC1RF_1LA1LD_0RE1RE_0RA0LC_0RD---".
Definition tm' := TM_from_str "1RB1LE_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LP_1LP0LK_1RV1LK_1LD0RV_1LP1RV_0LL1RM_1LL---_1RV0LD_1LK0LP_0LD0LP_1LD1LP_0RQ0RR_1RQ1RR_0RA1RA_0LD0LP_0RA0LD_1RA0LP_0RF0LK_0LD1LK_0RM---_1RM---_0RQ---_0RR---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LK_1LK0LT_1RN1LT_1LD0RN_1LK1RN_0LL1RQ_1LL---_1RN0LD_1LT0LK_0LD0LK_1LD1LK_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RA1RA_0LD0LK_0RA0LD_1RA0LK_0RF0LK_0LD1LK".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LI_1RA---_1RC0LE_0LF0LE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LI_1RA1RJ_1RC0LE_0LF0LE_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "MQAFPDVRK".
Definition mp' := mp_from_str "QUAFKDNVT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM434.


Module TM435.
Definition tm := TM_from_str "1RB1LE_1LC1RD_1LA0LC_0RE---_0RF1RF_0RA0LC".
Definition tm' := TM_from_str "1RB1LF_1LC1RE_0RA0LD_1LA0LD_0RF---_0RC1RC".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LK_1LK0LT_1RN1LT_1LD0RN_1LK1RN_0LL1RQ_1LL---_1RN0LD_1LT0LK_0LD0LK_1LD1LK_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RA1RA_0LD0LK_0RA0LD_1RA0LK_0RF0LK_0LD1LK".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LO_1LO0LX_1RR1LX_0LD0RR_1LO1RR_0LL1RU_1LL---_0RA0LD_1RA0LO_0RF0LO_0LD1LO_1RR0LD_1LX0LO_0LD0LO_1LD1LO_0RU---_1RU---_0RI---_0RJ---_0RI0RJ_1RI1RJ_0RA1RA_0LD0LO".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LI_1RA---_1RC0LE_0LF0LE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LE_1RG1LI_1RA1RJ_1RC0LE_0LF0LE_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QUAFKDNVT".
Definition mp' := mp_from_str "UIAFODRJX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM435.


Module TM436.
Definition tm := TM_from_str "1RB0LD_1LC1RE_0RA0LD_1LA1LF_0RF---_0RC1RC".
Definition tm' := TM_from_str "1RB0LC_1LA1RD_1LA1LE_0RE---_0RF1RF_0RA0LC".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LX_1LO0LO_1RR1LO_0LD0RR_1LO1RR_0LL1RU_1LL---_0RA0LD_1RA0LX_0RF0LO_0LD1LO_1RR0LD_1LO0LX_0LD0LX_1LD1LX_0RU---_1RU---_0RI---_0RJ---_0RI0RJ_1RI1RJ_0RA1RA_0LD0LX".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LT_1LK0LK_1RN1LK_1RN0RN_1LK1RN_0LD1RQ_1LD---_1RN0LD_1LK0LT_0LD0LT_1LD1LT_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RA1RA_0LD0LT_0RA0LD_1RA0LT_0RF0LK_0LD1LK".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LI_1RG1LE_1RA---_1RC0LI_0LF0LI".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LI_1RG1LE_1RA1RJ_1RC0LI_0LF0LI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "UIAFODRJX".
Definition mp' := mp_from_str "QUAFKDNVT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM436.


Module TM437.
Definition tm := TM_from_str "1RB0LC_1LA1RD_1LA1LE_0RE---_0RF1RF_0RA0LC".
Definition tm' := TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LT_1LK0LK_1RN1LK_1RN0RN_1LK1RN_0LD1RQ_1LD---_1RN0LD_1LK0LT_0LD0LT_1LD1LT_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RA1RA_0LD0LT_0RA0LD_1RA0LT_0RF0LK_0LD1LK".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LS_1LL0LL_1RV1LL_1RV0RV_1LL1RV_0LD1RI_1LD---_0RM0RN_1RM1RN_0RA1RA_0LD0LS_0RA0LD_1RA0LS_0RF0LS_0LD1LS_1RV0LD_1LL0LS_0LD0LS_1LD1LS_0RI---_1RI---_0RM---_0RN---".
Definition tm1 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LI_1RG1LE_1RA---_1RC0LI_0LF0LI".
Definition tm2 := TM'_from_str "0RB0RH_0RC0LF_0RD0LF_1LE1RG_0LF0LI_1RG1LE_1RA1RJ_1RC0LI_0LF0LI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "QUAFKDNVT".
Definition mp' := mp_from_str "IMAFLDVNS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM437.


Module TM438.
Definition tm := TM_from_str "1RB0LC_1LC0RF_1LA1LD_0RE0LC_---1LB_1RB0RD".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LP_1LP0LK_1RU1LK_1LD0RU_1LP1RU_0LL0RF_1LL0RM_1RU1LL_1LK1LK_0LD0LP_1LD1LP_0RQ0LD_1RQ0LP_---0LK_1LL1LK_---1LL_---0RM_---0LH_---1LH_0RF0RM_1RF1RM_1LP0RQ_1RU0LD".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1LP0RQ_1RA0LX_1LX0RA_1LP1RA_0LL0RF_1LL0RM_1RA1LL_1LK1LK_0LX0LP_1LX1LP_0RQ0LX_1RQ0LP_---0LK_1LL1LK_---1LL_---0RM_---0LH_---1LH_0RF0RJ_1RF1RJ_1LP1LK_1RA1LK".
Definition tm1 := TM'_from_str "1LB1RF_1LC1LD_1LE1LB_0LE0LB_1RF1LD_0RA0RG_0RH0LE_---1LC".
Definition tm2 := TM'_from_str "1LB1RF_1LC1LD_1LE1LB_0LE0LB_1RF1LD_0RA0RG_0RH0LE_1RI1LC_1RI1RI".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "FPLKDUMQ".
Definition mp' := mp_from_str "FPLKXAMQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM438.


Module TM439.
Definition tm := TM_from_str "1LB0RF_1RC0LD_1RA1RC_---0LE_1RA1LE_0RA1RC".
Definition tm' := TM_from_str "1LB0RC_1RC0LE_0RA1RD_1RA1RD_---0LF_1RA1LF".
Definition tm0 := TM'_from_str "1RJ0RU_1LO1RU_0LH0RA_1LH0RJ_0RJ---_1RJ0LS_1RB0LO_1RJ1LO_0RB0RJ_1RB1RJ_1LO1RB_1RU1RJ_---1LO_---0LT_---0LS_---1LS_0RB1RU_1RB1LT_1LO0LT_1RU1LT_0RA0RJ_1RA1RJ_1RJ1RB_0RU1RJ".
Definition tm0' := TM'_from_str "1RN0RI_1LS1RI_0LH0RA_1LH0RN_0RJ---_1RJ0LW_1RA0LS_1RN1LS_0RA0RN_1RA1RN_1RN1RB_0RI1RN_0RB0RN_1RB1RN_1LS1RB_1RI1RN_---1LS_---0LX_---0LW_---1LW_0RB1RI_1RB1LX_1LS0LX_1RI1LX".
Definition tm1 := TM'_from_str "1LB1RE_---0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF0RE".
Definition tm2 := TM'_from_str "1LB1RE_1RH0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF0RE_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "BOSTUJA".
Definition mp' := mp_from_str "BSWXINA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM439.


Module TM440.
Definition tm := TM_from_str "1LB0LE_1RC0LA_1RA1RD_1RA---_0LF0RB_0RC1LE".
Definition tm' := TM_from_str "1LB0LE_1RC0LA_0LC1RD_1RA---_0LF0RB_0RD1LE".
Definition tm0 := TM'_from_str "1RN0LW_1LC0RJ_0LH0LS_1LH1LS_0RJ0LH_1RJ0LS_1RB0LC_1RN1LC_0RB0RN_1RB1RN_1LC1RB_0RJ---_0RB---_1RB---_1LC---_0RJ---_0RB0RE_0LT1RE_0LW0RJ_1LW0LH_0RI1LW_1RI0LH_0RB0LT_0RN1LT".
Definition tm0' := TM'_from_str "1RN0LW_1LC0RJ_0LH0LS_1LH1LS_0RJ0LH_1RJ0LS_1RB0LC_1RN1LC_0LK0RN_1RB1RN_0LK1RB_1LK---_0RB---_1RB---_1LC---_0RJ---_0RB0RE_0LT1RE_0LW0RJ_1LW0LH_0RM1LW_1RM0LH_0RB0LT_---1LT".
Definition tm1 := TM'_from_str "1LB0RH_0LF0LC_0LD0RH_0RA0LE_1LD0LF_1RG1LB_1RA---_1RA1RG".
Definition tm2 := TM'_from_str "1LB0RH_0LF0LC_0LD0RH_0RA0LE_1LD0LF_1RG1LB_1RA1RI_1RA1RG_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BCSWTHNJ".
Definition mp' := mp_from_str "BCSWTHNJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM440.


Module TM441.
Definition tm := TM_from_str "1LB0LE_1RC0LA_0LC1RD_1RA---_0LF0RB_0RD1LE".
Definition tm' := TM_from_str "1LB0LE_1RC0LA_1RA0RD_0LB---_0LF0RB_0RC1LE".
Definition tm0 := TM'_from_str "1RN0LW_1LC0RJ_0LH0LS_1LH1LS_0RJ0LH_1RJ0LS_1RB0LC_1RN1LC_0LK0RN_1RB1RN_0LK1RB_1LK---_0RB---_1RB---_1LC---_0RJ---_0RB0RE_0LT1RE_0LW0RJ_1LW0LH_0RM1LW_1RM0LH_0RB0LT_---1LT".
Definition tm0' := TM'_from_str "1RM0LW_1LC0RJ_0LH0LS_1LH1LS_0RJ0LH_1RJ0LS_1RB0LC_1RM1LC_0RB0RM_1RB1RM_1LC1RB_0RJ---_1RB---_0LC---_0LG---_1LG---_0RB0RE_0LT1RE_0LW0RJ_1LW0LH_0RI1LW_1RI0LH_0RB0LT_0RM1LT".
Definition tm1 := TM'_from_str "1LB0RH_0LF0LC_0LD0RH_0RA0LE_1LD0LF_1RG1LB_1RA---_1RA1RG".
Definition tm2 := TM'_from_str "1LB0RH_0LF0LC_0LD0RH_0RA0LE_1LD0LF_1RG1LB_1RA1RI_1RA1RG_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BCSWTHNJ".
Definition mp' := mp_from_str "BCSWTHMJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM441.


Module TM442.
Definition tm := TM_from_str "1LB0LE_1RC0LA_1RA0RD_0LB---_0LF0RB_0RC1LE".
Definition tm' := TM_from_str "1LB0LE_1RC0LA_1RA1RD_1RA---_0LF0RB_0RD1LE".
Definition tm0 := TM'_from_str "1RM0LW_1LC0RJ_0LH0LS_1LH1LS_0RJ0LH_1RJ0LS_1RB0LC_1RM1LC_0RB0RM_1RB1RM_1LC1RB_0RJ---_1RB---_0LC---_0LG---_1LG---_0RB0RE_0LT1RE_0LW0RJ_1LW0LH_0RI1LW_1RI0LH_0RB0LT_0RM1LT".
Definition tm0' := TM'_from_str "1RN0LW_1LC0RJ_0LH0LS_1LH1LS_0RJ0LH_1RJ0LS_1RB0LC_1RN1LC_0RB0RN_1RB1RN_1LC1RB_0RJ---_0RB---_1RB---_1LC---_0RJ---_0RB0RE_0LT1RE_0LW0RJ_1LW0LH_0RM1LW_1RM0LH_0RB0LT_---1LT".
Definition tm1 := TM'_from_str "1LB0RH_0LF0LC_0LD0RH_0RA0LE_1LD0LF_1RG1LB_1RA---_1RA1RG".
Definition tm2 := TM'_from_str "1LB0RH_0LF0LC_0LD0RH_0RA0LE_1LD0LF_1RG1LB_1RA1RI_1RA1RG_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BCSWTHMJ".
Definition mp' := mp_from_str "BCSWTHNJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM442.


Module TM443.
Definition tm := TM_from_str "1RB1LE_0RC0RA_0RD0RF_1LD1LA_0LA0LE_1RB---".
Definition tm' := TM_from_str "1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---".
Definition tm0 := TM'_from_str "0RF1LC_1RF1LS_1RI0LT_1RA1LT_0RI0RA_1RI1RA_0RM0RF_0RU1LC_0RM0RU_1RM1RU_1LP0RF_1RA---_1LP1RA_1LD1LT_0LP0LD_1LP1LD_1RI0LC_0LT0LS_0LC0LS_1LC1LS_0RF---_1RF---_1RI---_1RA---".
Definition tm0' := TM'_from_str "0RF1LC_1RF1LS_1RI0LT_1RA1LT_0RI0RA_1RI1RA_0RM0RF_0RV1LC_0RM0RV_1RM1RV_1LP0RF_1RA---_1LP1RA_1LD1LT_0LP0LD_1LP1LD_1RI0LC_0LT0LS_0LC0LS_1LC1LS_0RM---_0RF---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB0RJ_1LC1RE_1LC1LD_1RE1LG_0RI1LF_1RA0LG_1LF1LH_0LF0LH_1RA1RE_0RI---".
Definition tm2 := TM'_from_str "0RB0RJ_1LC1RE_1LC1LD_1RE1LG_0RI1LF_1RA0LG_1LF1LH_0LF0LH_1RA1RE_0RI1RK_1RK1RK".
Definition l0 := [1;1;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "IMPDACTSFU".
Definition mp' := mp_from_str "IMPDACTSFV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM443.


Module TM444.
Definition tm := TM_from_str "1RB0LA_1RC---_0LD1RD_0RB0RE_0RF1RC_1LF0LA".
Definition tm' := TM_from_str "1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA".
Definition tm0 := TM'_from_str "0RF1RJ_1RF0LC_1RJ0LC_---1LC_0RJ---_1RJ---_0RU---_1RN---_0RJ0RN_0RU1RN_0LO1RE_1LO1RQ_0RE0RQ_1RE1RQ_0RJ0RU_---0RJ_0RU0RJ_1RU1RJ_1LX0RU_1RJ1RN_1LX1RJ_1LC0LC_0LX0LC_1LX1LC".
Definition tm0' := TM'_from_str "0RF1RJ_1RF0LC_1RJ0LC_---1LC_0RJ---_1RJ---_0RU---_1RN---_0RJ0RN_0RU1RN_0LO1RE_1LO1RQ_0RE0RQ_1RE1RQ_0RJ0RU_---0RJ_0RU0RJ_1RU0RU_1LX0LO_1RJ1LO_1LX1RJ_1LC0LC_0LX0LC_1LX1LC".
Definition tm1 := TM'_from_str "1RB1RG_0RC---_0RD1RA_1LE1RC_1LE1LF_1RC0LF_0RD0RC".
Definition tm2 := TM'_from_str "1RB1RG_0RC1RH_0RD1RA_1LE1RC_1LE1LF_1RC0LF_0RD0RC_1RH1RH".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "NEJUXCQ".
Definition mp' := mp_from_str "NEJUXCQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM444.


Module TM445.
Definition tm := TM_from_str "1RB0RD_1RC---_0LA1RA_0RE1RC_1LE0LF_1RB0LF".
Definition tm' := TM_from_str "1RB0RD_1RC---_0LA1RA_0RE1RC_1LE0LF_0RC0LF".
Definition tm0 := TM'_from_str "0RF0RM_1RF1RM_1RJ0RQ_---0RJ_0RJ---_1RJ---_0RQ---_1RB---_1RJ0RB_0RQ1RB_0LC1RF_1LC1RM_0RQ0RJ_1RQ1RJ_1LT0RQ_1RJ1RB_1LT1RJ_1LW0LW_0LT0LW_1LT1LW_0RF1RJ_1RF0LW_1RJ0LW_---1LW".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1RJ0RQ_---0RJ_0RJ---_1RJ---_0RQ---_1RB---_1RJ0RB_0RQ1RB_0LC1RF_1LC1RM_0RQ0RJ_1RQ1RJ_1LT0RQ_1RJ1RB_1LT1RJ_1LW0LW_0LT0LW_1LT1LW_0RI1RJ_1RI0LW_1RJ0LW_0RB1LW".
Definition tm1 := TM'_from_str "1RB1RG_1RC---_0RD1RA_1LE1RC_1LE1LF_1RC0LF_0RD0RC".
Definition tm2 := TM'_from_str "1RB1RG_1RC1RH_0RD1RA_1LE1RC_1LE1LF_1RC0LF_0RD0RC_1RH1RH".
Definition l0 := [1;1;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "BFJQTWM".
Definition mp' := mp_from_str "BFJQTWM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM445.


Module TM446.
Definition tm := TM_from_str "1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0RC".
Definition tm' := TM_from_str "1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF".
Definition tm0 := TM'_from_str "0RF1LS_1RF1LP_1RI0LP_1RU1LP_0RI0RU_1RI1RU_1LL0RE_1RI0RI_1LL1RI_1LC0LP_0LL0LC_1LL1LC_0LD1LS_---1LP_0LS0LP_1LS1LP_1RU---_1LP---_0LD---_1LD---_0RE0RI_1RE1RI_0RI1LL_0RU1RI".
Definition tm0' := TM'_from_str "0RF1LS_1RF1LP_1RI0LP_1RU1LP_0RI0RU_1RI1RU_1LL0RE_1RI0RI_1LL1RI_1LC0LP_0LL0LC_1LL1LC_0LD1LS_---1LP_0LS0LP_1LS1LP_1RU---_1LP---_0LD---_1LD---_0RE0RI_1RE0LW_0RI0LW_0RU1LW".
Definition tm1 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LD_0LF---_1RG1LD_0RH0RA_0RA0RG".
Definition tm2 := TM'_from_str "1LB1RA_1LB1LC_1RA0LD_1LE1LD_0LF1RI_1RG1LD_0RH0RA_0RA0RG_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "ILCPSDUE".
Definition mp' := mp_from_str "ILCPSDUE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM446.


Module TM447.
Definition tm := TM_from_str "1RB0RB_1LC0LE_0RF1LD_1RA0LB_1RA0RE_---0RC".
Definition tm' := TM_from_str "1RB0RB_1LC0LE_0RF1LD_1RA0LB_1RA0RD_---0RC".
Definition tm0 := TM'_from_str "0RF0RE_1RF1RE_1LP0RI_0RB1RF_0RI1RF_1LP0RB_0LL0LS_1LL1LS_0RU1RE_1RU1LG_---0LP_0RI1LP_0RB0LL_1RB0LS_1RF0LG_1RE1LG_0RB0RQ_1RB1RQ_1RF0RB_1RE0RQ_---0RI_---1RI_---0RU_---1RE".
Definition tm0' := TM'_from_str "0RF0RE_1RF1RE_1LP0RI_0RB1RF_0RI1RF_1LP0RB_0LL0LS_1LL1LS_0RU1RE_1RU1LG_---0LP_0RI1LP_0RB0LL_1RB0LS_1RF0LG_1RE1LG_0RB0RM_1RB1RM_1RF0RB_1RE0LL_---0RI_---1RI_---0RU_---1RE".
Definition tm1 := TM'_from_str "1LB0RI_1RH1LC_0LE0LD_1RA0RI_0RF1LB_0RG1RH_---0RF_0RF1RA_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RI_1RH1LC_0LE0LD_1RA0RI_0RF1LB_0RG1RH_1RJ0RF_0RF1RA_1RA1RH_1RJ1RJ".
Definition l0 := [0;0;0;0;1;0;1;1]%N.
Definition mp := mp_from_str "FPGSLIUEB".
Definition mp' := mp_from_str "FPGSLIUEB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM447.


Module TM448.
Definition tm := TM_from_str "1LB1LE_1RC1LF_1RA0RD_1RE1LD_0LA0RC_0LA---".
Definition tm' := TM_from_str "1LB1LE_1RC1LF_1RA0RD_1RE1LD_0LA0RC_0RA---".
Definition tm0 := TM'_from_str "1RM1LC_1LX0RM_0LH0LT_1LH1LT_0RJ1LC_1RJ---_1RB0LX_1RM1LX_0RB0RM_1RB1RM_1LX0RR_0RM1RI_0RR1RI_1RR1LP_0LT0LP_1RI1LP_0LH0RI_0LT1RI_0LC0RB_1LC0RM_0LH---_0LT---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1RM1LC_1LX0RM_0LH0LT_1LH1LT_0RJ1LC_1RJ---_1RB0LX_1RM1LX_0RB0RM_1RB1RM_1LX0RR_0RM1RI_0RR1RI_1RR1LP_0LT0LP_1RI1LP_0LH0RI_0LT1RI_0LC0RB_1LC0RM_0RA---_1RA---_1RM---_1LC---".
Definition tm1 := TM'_from_str "0RB0RG_1LC0RG_1LD---_0LF0LE_1LD0RG_1RG1LC_0RH1RA_0LE1RA".
Definition tm2 := TM'_from_str "0RB0RG_1LC0RG_1LD1RI_0LF0LE_1LD0RG_1RG1LC_0RH1RA_0LE1RA_1RI1RI".
Definition l0 := [1;0;0;0;1;0;0;1]%N.
Definition mp := mp_from_str "IBXCTHMR".
Definition mp' := mp_from_str "IBXCTHMR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM448.


Module TM449.
Definition tm := TM_from_str "1RB1RC_1LA0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm' := TM_from_str "1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_1RJ1RN_0LW1RJ_0LW---_1RJ0LW_0LD0LS_1LD1LS_0RN0RJ_1RN1RJ_1LS1RN_1RA1RJ_1LD0RA_1LS1RA_0LH0RF_1LH0RJ_---1LS_---0LX_---0LW_---1LW_0RN1RA_1RN1LX_1LS0LX_1RA1LX".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1RJ1RN_0LW1RJ_0RJ---_1RJ0LW_1RN0LS_1RJ1LS_0RN0RJ_1RN1RJ_1LS1RN_1RA1RJ_1RJ0RA_1LS1RA_0LH0RF_1LH0RJ_---1LS_---0LX_---0LW_---1LW_0RN1RA_1RN1LX_1LS0LX_1RA1LX".
Definition tm1 := TM'_from_str "1LB1RE_---0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF0LC".
Definition tm2 := TM'_from_str "1LB1RE_1RH0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF0LC_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "NSWXAJF".
Definition mp' := mp_from_str "NSWXAJF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM449.


Module TM450.
Definition tm := TM_from_str "1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm' := TM_from_str "1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_1RJ1RN_0LW1RJ_0RJ---_1RJ0LW_1RN0LS_1RJ1LS_0RN0RJ_1RN1RJ_1LS1RN_1RA1RJ_1RJ0RA_1LS1RA_0LH0RF_1LH0RJ_---1LS_---0LX_---0LW_---1LW_0RN1RA_1RN1LX_1LS0LX_1RA1LX".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1RJ1RN_0LW1RJ_1RA---_1RJ0LW_0LL0LS_1LL1LS_0RN0RJ_1RN1RJ_1LS1RN_1RA1RJ_1LL0RA_1LS1RA_0LH0RF_1LH0RJ_---1LS_---0LX_---0LW_---1LW_0RN1RA_1RN1LX_1LS0LX_1RA1LX".
Definition tm1 := TM'_from_str "1LB1RE_---0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF0LC".
Definition tm2 := TM'_from_str "1LB1RE_1RH0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF0LC_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "NSWXAJF".
Definition mp' := mp_from_str "NSWXAJF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM450.


Module TM451.
Definition tm := TM_from_str "1RB0LB_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB".
Definition tm' := TM_from_str "1RB0LB_0LC1RE_---1LD_1RB1LA_0RF1RF_1RA0LB".
Definition tm0 := TM'_from_str "0RF0LK_1RF1RU_0LP0LG_1RR1LG_---0RR_0LP1RR_0LK1RU_1LK1RV_---1RR_---1LD_---0LP_---1LP_0RM1RR_1RM1LG_0RM0LD_1RR1LD_0RU0RV_1RU1RV_0RB1RB_0LK1RU_0RB0LK_1RB1RU_1RF0LG_1RU1LG".
Definition tm0' := TM'_from_str "0RF0LK_1RF1RU_0LP0LG_1RR1LG_---0RR_0LP1RR_0LK1RU_1LK1RV_---1RR_---1LD_---0LP_---1LP_0RF1RR_1RF1LG_0LP0LD_1RR1LD_0RU0RV_1RU1RV_0RB1RB_0LK1RU_0RB0LK_1RB1RU_1RF0LG_1RU1LG".
Definition tm1 := TM'_from_str "0RB0LI_1RC1RA_0LD1RF_1RF1LE_1RF1LH_1RA1RG_1RB1RA_0LI1RA_---0LD".
Definition tm2 := TM'_from_str "0RB0LI_1RC1RA_0LD1RF_1RF1LE_1RF1LH_1RA1RG_1RB1RA_0LI1RA_1RJ0LD_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "UBFPDRVGK".
Definition mp' := mp_from_str "UBFPDRVGK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM451.


Module TM452.
Definition tm := TM_from_str "1RB0LB_0LC1RE_---1LD_1RB1LA_0RF1RF_1RA0LB".
Definition tm' := TM_from_str "1RB1LF_0LC1RD_---1LA_0RE1RE_1RF0LB_1RB1LD".
Definition tm0 := TM'_from_str "0RF0LK_1RF1RU_0LP0LG_1RR1LG_---0RR_0LP1RR_0LK1RU_1LK1RV_---1RR_---1LD_---0LP_---1LP_0RF1RR_1RF1LG_0LP0LD_1RR1LD_0RU0RV_1RU1RV_0RB1RB_0LK1RU_0RB0LK_1RB1RU_1RF0LG_1RU1LG".
Definition tm0' := TM'_from_str "0RF1RN_1RF1LP_0LD0LX_1RN1LX_---0RN_0LD1RN_0LK1RQ_1LK1RR_---1RN_---1LX_---0LD_---1LD_0RQ0RR_1RQ1RR_0RV1RV_0LK1RQ_0RV0LK_1RV1RQ_1RF0LG_1RQ1LG_0RF0LK_1RF1RQ_0LD0LP_1RN1LP".
Definition tm1 := TM'_from_str "0RB0LI_1RC1RA_0LD1RF_1RF1LE_1RF1LH_1RA1RG_1RB1RA_0LI1RA_---0LD".
Definition tm2 := TM'_from_str "0RB0LI_1RC1RA_0LD1RF_1RF1LE_1RF1LH_1RA1RG_1RB1RA_0LI1RA_1RJ0LD_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "UBFPDRVGK".
Definition mp' := mp_from_str "QVFDXNRPK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM452.


Module TM453.
Definition tm := TM_from_str "1RB1LF_0LC1RD_---1LA_0RE1RE_1RF0LB_1RB1LD".
Definition tm' := TM_from_str "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB".
Definition tm0 := TM'_from_str "0RF1RN_1RF1LP_0LD0LX_1RN1LX_---0RN_0LD1RN_0LK1RQ_1LK1RR_---1RN_---1LX_---0LD_---1LD_0RQ0RR_1RQ1RR_0RV1RV_0LK1RQ_0RV0LK_1RV1RQ_1RF0LG_1RQ1LG_0RF0LK_1RF1RQ_0LD0LP_1RN1LP".
Definition tm0' := TM'_from_str "0RF0LK_1RF1RU_0LP0LT_1RR1LT_---0RR_0LP1RR_0LK1RU_1LK1RV_---1RR_---1LD_---0LP_---1LP_0RM1RR_1RM1LT_0RM0LD_1RR1LD_0RU0RV_1RU1RV_0RB1RB_0LK1RU_0RB0LK_1RB1RU_1RF0LG_1RU1LG".
Definition tm1 := TM'_from_str "0RB0LI_1RC1RA_0LD1RF_1RF1LE_1RF1LH_1RA1RG_1RB1RA_0LI1RA_---0LD".
Definition tm2 := TM'_from_str "0RB0LI_1RC1RA_0LD1RF_1RF1LE_1RF1LH_1RA1RG_1RB1RA_0LI1RA_1RJ0LD_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "QVFDXNRPK".
Definition mp' := mp_from_str "UBFPDRVTK".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM453.


Module TM454.
Definition tm := TM_from_str "1RB1LE_0RC0RF_1LD1RD_1LA0LB_1RC0LD_0LA---".
Definition tm' := TM_from_str "1RB1LE_0RC1RF_1LD1RD_1LA0LB_1RC0LD_0RC---".
Definition tm0 := TM'_from_str "0RF1RN_1RF1LO_1RI0LT_1RU1LT_0RI0RU_1RI1RU_1LD1RI_0RN---_1LD0RN_1LG1RN_0LP1LT_1LP1RI_1RU1LD_1LT1RI_0LD0LG_1LD1LG_0RJ0LD_1RJ0LG_1LG0LO_1RN1LO_1RI---_0LT---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF1RN_1RF1LO_1RI0LT_1RV1LT_0RI0RV_1RI1RV_1LD1RI_0RN---_1LD0RN_1LG1RN_0LP1LT_1LP1RI_1RV1LD_1LT1RI_0LD0LG_1LD1LG_0RJ0LD_1RJ0LG_1LG0LO_1RN1LO_0RI---_1RI---_1LD---_0RN---".
Definition tm1 := TM'_from_str "1LB0RG_1RF1LC_1RG1LD_0LB0LE_1LB1RA_1RA---_1LC1RA".
Definition tm2 := TM'_from_str "1LB0RG_1RF1LC_1RG1LD_0LB0LE_1LB1RA_1RA1RH_1LC1RA_1RH1RH".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "IDTOGUN".
Definition mp' := mp_from_str "IDTOGVN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM454.


Module TM455.
Definition tm := TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_0LE0LE".
Definition tm' := TM_from_str "1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RJ---_1LS---_0RJ1LS_1RJ1LS_1LO0LX_1RR1LX_1LH0RR_1LO1RR_0LP1RB_1LP1RI_1RR0LH_1LX0LO_0LH0LO_1LH1LO_0RB0RI_1RB1RI_1RF1LH_---0RR_1RF1RF_1LH1LH_0LS0LS_1LS1LS".
Definition tm0' := TM'_from_str "0RF1RF_1RF1LH_1RJ0LS_1LS1LS_0RJ1LS_1RJ1LS_1LO0LD_1RR1LD_1LH0RR_1LO1RR_0LP1RV_1LP1RI_1RR0LH_1LD0LO_0LH0LO_1LH1LO_0RV0RI_1RV1RI_1RF1LH_---0RR_0RF---_1RF---_1RJ---_1LS---".
Definition tm1 := TM'_from_str "1RB---_1RC1LG_1LD1RH_0LE0LD_1RH1LF_1LG1LG_1RB1LE_1RA1RI_1LE0RH".
Definition tm2 := TM'_from_str "1RB1RJ_1RC1LG_1LD1RH_0LE0LD_1RH1LF_1LG1LG_1RB1LE_1RA1RI_1LE0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFJOHXSRI".
Definition mp' := mp_from_str "VFJOHDSRI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 31 31.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM455.


Module TM456.
Definition tm := TM_from_str "1LB1RB_1LC0RA_0RD1LF_---1RE_1RB1RE_1LD0LB".
Definition tm' := TM_from_str "1LB0LC_1LC0RA_0RD1LE_1RB1RD_1LF0LB_---1RD".
Definition tm0 := TM'_from_str "1LL0RF_0RF1RF_0LH1LX_1LH1RA_0RR0RA_1LX1RA_0LL1LL_1LL0RF_0RM1LP_1RM1LG_---0LX_0RR1LX_---0RR_---1RR_---1RF_---1RR_0RF0RR_1RF1RR_1LX1RF_1RA1RR_---0LL_1RR1LL_0LP0LG_1LP1LG".
Definition tm0' := TM'_from_str "1LL0RF_0RF0LT_0LH0LK_1LH1LK_0RN0RA_1LT1RA_0LL1LL_1LL0RF_0RM1LX_1RM1LG_0RF0LT_0RN1LT_0RF0RN_1RF1RN_1LT1RF_1RA1RN_---0LL_1RN1LL_0LX0LG_1LX1LG_---0RN_---1RN_---1RF_---1RN".
Definition tm1 := TM'_from_str "1RB1RA_1LC1RF_1LG1LD_0LE1LE_0RA1LC_1LE0RB_---1RA".
Definition tm2 := TM'_from_str "1RB1RA_1LC1RF_1LG1LD_0LE1LE_0RA1LC_1LE0RB_1RH1RA_1RH1RH".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "RFXGLAP".
Definition mp' := mp_from_str "NFTGLAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM456.


Module TM457.
Definition tm := TM_from_str "1LB0LC_1LC0RA_0RD1LE_1RB1RD_1LF0LB_---1RD".
Definition tm' := TM_from_str "1LB1RB_1LC0RA_0RD1LE_1RB1RD_1LF0LB_---1RD".
Definition tm0 := TM'_from_str "1LL0RF_0RF0LT_0LH0LK_1LH1LK_0RN0RA_1LT1RA_0LL1LL_1LL0RF_0RM1LX_1RM1LG_0RF0LT_0RN1LT_0RF0RN_1RF1RN_1LT1RF_1RA1RN_---0LL_1RN1LL_0LX0LG_1LX1LG_---0RN_---1RN_---1RF_---1RN".
Definition tm0' := TM'_from_str "1LL0RF_0RF1RF_0LH1LT_1LH1RA_0RN0RA_1LT1RA_0LL1LL_1LL0RF_0RM1LX_1RM1LG_0RF0LT_0RN1LT_0RF0RN_1RF1RN_1LT1RF_1RA1RN_---0LL_1RN1LL_0LX0LG_1LX1LG_---0RN_---1RN_---1RF_---1RN".
Definition tm1 := TM'_from_str "1RB1RA_1LC1RF_1LG1LD_0LE1LE_0RA1LC_1LE0RB_---1RA".
Definition tm2 := TM'_from_str "1RB1RA_1LC1RF_1LG1LD_0LE1LE_0RA1LC_1LE0RB_1RH1RA_1RH1RH".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "NFTGLAX".
Definition mp' := mp_from_str "NFTGLAX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM457.


Module TM458.
Definition tm := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0LE1RF_0RD---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_0LC---".
Definition tm0 := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1LC1LC_0RI1LC_1RI1LC_0LD0LD_0RR1LD_0LD0RR_0RI1RR_0LO1RM_1LO1RV_1LC0RE_1LC1RE_0LD0RI_1LD1LC_0LS0RV_1RM1RV_0LS1RM_1LS---_0RM---_1RM---_1LC---_0RE---".
Definition tm0' := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1LC1LC_0RI1LC_1RI1LC_0LD0LD_0RR1LD_0LD0RR_0RI1RR_0LO1RM_1LO1RV_1LC0RE_1LC1RE_0LD0RI_1LD1LC_0RM0RV_1RM1RV_1LC1RM_0RE---_0LO---_1RM---_0LK---_1LK---".
Definition tm1 := TM'_from_str "0RB1LD_0LC0RE_1LD1LD_1RB0LD_1RF1RG_1LD0RA_1RF---".
Definition tm2 := TM'_from_str "0RB1LD_0LC0RE_1LD1LD_1RB0LD_1RF1RG_1LD0RA_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "EIDCRMV".
Definition mp' := mp_from_str "EIDCRMV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM458.


Module TM459.
Definition tm := TM_from_str "1RB0RA_1RC0LE_1LD1RC_1RA1LE_1LF0LD_1LC---".
Definition tm' := TM_from_str "1RB0RA_1LC0LE_1LD1RC_1RA1LE_1LF0LD_1LC---".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_0LO0RA_0RJ0LX_1RJ0LO_1LT0LS_1RJ1LS_1RA0RJ_1LT1RJ_0LP1LT_1LP1RJ_0RB1LX_1RB1LO_1RF0LT_1RA1LT_1LL1RF_---0LT_0LX0LO_1LX1LO_1LP---_1RJ---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_0LO0RA_1LP0LX_1RJ0LO_0LL0LS_1LL1LS_1RA0RJ_1LT1RJ_0LP1LT_1LP1RJ_0RB1LX_1RB1LO_1RF0LT_1RA1LT_1LL1RF_---0LT_0LX0LO_1LX1LO_1LP---_1RJ---_0LL---_1LL---".
Definition tm1 := TM'_from_str "1LB1RA_1LE1LC_1RD0LB_1RA0LC_1LF---_1LG1RA_1RH1LB_0RD0RH".
Definition tm2 := TM'_from_str "1LB1RA_1LE1LC_1RD0LB_1RA0LC_1LF1RI_1LG1RA_1RH1LB_0RD0RH_1RI1RI".
Definition l0 := [1;1;0;0;0;1;1;1]%N.
Definition mp := mp_from_str "JTOFXLPA".
Definition mp' := mp_from_str "JTOFXLPA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM459.


Module TM460.
Definition tm := TM_from_str "1LB1RB_1LC0LD_0RA1LF_0LE1RD_---1RC_1RA0LB".
Definition tm' := TM_from_str "1LB1RB_1LC0LD_0RA1LE_1LF1RC_1RF0LB_---1RB".
Definition tm0 := TM'_from_str "1LL0RF_1LO1RF_0LH1LX_1LH1RA_0RF0LS_1LX1RA_0LL0LO_1LL1LO_0RA1RF_1RA1LG_1LL0LX_0RF1LX_---0RN_1RA1RN_0LS1RA_1LS1RN_---0RJ_---1RJ_---1RA_---1LG_0RB0LL_1RB0LO_1LO0LG_1RF1LG".
Definition tm0' := TM'_from_str "1LL0RF_1LO1RF_0LH1LT_1LH1RA_0RF0LX_1LT1RA_0LL0LO_1LL1LO_0RA1RF_1RA1LG_1LL0LT_0RF1LT_---0RJ_1RA1RJ_0LX1RA_1LX1LG_0RV0LL_1RV0LO_---0LG_1RF1LG_---0RF_---1RF_---1LT_---1RA".
Definition tm1 := TM'_from_str "1LB0RF_0RF1LC_1RF1LD_0LB0LE_0LG1RA_1LC1RA_---1RA".
Definition tm2 := TM'_from_str "1LB0RF_0RF1LC_1RF1LD_0LB0LE_0LG1RA_1LC1RA_1RH1RA_1RH1RH".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "ALXGOFS".
Definition mp' := mp_from_str "ALTGOFX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM460.


Module TM461.
Definition tm := TM_from_str "1LB1RB_1LC0LD_0RA1LE_1LF1RC_1RF0LB_---1RB".
Definition tm' := TM_from_str "1LB1RB_1LC0LD_0RA1LE_1LF1RC_1RA0LB_---1RB".
Definition tm0 := TM'_from_str "1LL0RF_1LO1RF_0LH1LT_1LH1RA_0RF0LX_1LT1RA_0LL0LO_1LL1LO_0RA1RF_1RA1LG_1LL0LT_0RF1LT_---0RJ_1RA1RJ_0LX1RA_1LX1LG_0RV0LL_1RV0LO_---0LG_1RF1LG_---0RF_---1RF_---1LT_---1RA".
Definition tm0' := TM'_from_str "1LL0RF_1LO1RF_0LH1LT_1LH1RA_0RF0LX_1LT1RA_0LL0LO_1LL1LO_0RA1RF_1RA1LG_1LL0LT_0RF1LT_---0RJ_1RA1RJ_0LX1RA_1LX1LG_0RB0LL_1RB0LO_1LO0LG_1RF1LG_---0RF_---1RF_---1LT_---1RA".
Definition tm1 := TM'_from_str "1LB0RF_0RF1LC_1RF1LD_0LB0LE_0LG1RA_1LC1RA_---1RA".
Definition tm2 := TM'_from_str "1LB0RF_0RF1LC_1RF1LD_0LB0LE_0LG1RA_1LC1RA_1RH1RA_1RH1RH".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "ALTGOFX".
Definition mp' := mp_from_str "ALTGOFX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM461.


Module TM462.
Definition tm := TM_from_str "1LB1RB_1LC0LD_0RA1LE_1LF1RC_1RA0LB_---1RB".
Definition tm' := TM_from_str "1LB1RB_1LC0LD_0RA1LE_0LF1RC_1RA0LB_---1RC".
Definition tm0 := TM'_from_str "1LL0RF_1LO1RF_0LH1LT_1LH1RA_0RF0LX_1LT1RA_0LL0LO_1LL1LO_0RA1RF_1RA1LG_1LL0LT_0RF1LT_---0RJ_1RA1RJ_0LX1RA_1LX1LG_0RB0LL_1RB0LO_1LO0LG_1RF1LG_---0RF_---1RF_---1LT_---1RA".
Definition tm0' := TM'_from_str "1LL0RF_1LO1RF_0LH1LT_1LH1RA_0RF0LW_1LT1RA_0LL0LO_1LL1LO_0RA1RF_1RA1LG_1LL0LT_0RF1LT_---0RJ_1RA1RJ_0LW1RA_1LW1LG_0RB0LL_1RB0LO_1LO0LG_1RF1LG_---0RJ_---1RJ_---1RA_---1LG".
Definition tm1 := TM'_from_str "1LB0RF_0RF1LC_1RF1LD_0LB0LE_0LG1RA_1LC1RA_---1RA".
Definition tm2 := TM'_from_str "1LB0RF_0RF1LC_1RF1LD_0LB0LE_0LG1RA_1LC1RA_1RH1RA_1RH1RH".
Definition l0 := [1;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "ALTGOFX".
Definition mp' := mp_from_str "ALTGOFW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM462.


Module TM463.
Definition tm := TM_from_str "1RB1RA_1RC1LB_1LD0RA_0RA0LE_---0LF_0RC0LB".
Definition tm' := TM_from_str "1RB1RA_1RC1LB_1LD0RA_1LC0LE_---0LF_1RD0LB".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1RJ1RF_1LH1RB_0RJ1RA_1RJ1LH_1LS0LH_1RA1LH_0RB0RA_1LS1RA_0LP0RF_1LP0RB_0RA---_1RA0LW_0RF0LS_0RB1LS_---0RB_---0LG_---0LW_---1LW_0RI1LS_1RI0LH_0RB0LG_0RA1LG".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1RJ1RF_1LH1RB_0RJ1RA_1RJ1LH_1LS0LH_1RA1LH_1LL0RA_1LS1RA_0LP0RF_1LP0RB_1LP---_0RB0LW_0LL0LS_1LL1LS_---0RB_---0LG_---0LW_---1LW_0RN1LS_1RN0LH_0RB0LG_0LW1LG".
Definition tm1 := TM'_from_str "1LB1RF_---0LC_0RG0LD_1LB0LE_1RF1LE_0RH0RG_1RH1RG_1RA1LE".
Definition tm2 := TM'_from_str "1LB1RF_1RI0LC_0RG0LD_1LB0LE_1RF1LE_0RH0RG_1RH1RG_1RA1LE_1RI1RI".
Definition l0 := [1;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "JSWGHABF".
Definition mp' := mp_from_str "JSWGHABF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM463.


Module TM464.
Definition tm := TM_from_str "1RB1RA_1RC1LB_1LD0RA_1LC0LE_---0LF_1RD0LB".
Definition tm' := TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1RJ1RF_1LH1RB_0RJ1RA_1RJ1LH_1LS0LH_1RA1LH_1LL0RA_1LS1RA_0LP0RF_1LP0RB_1LP---_0RB0LW_0LL0LS_1LL1LS_---0RB_---0LG_---0LW_---1LW_0RN1LS_1RN0LH_0RB0LG_0LW1LG".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1RJ1RF_1LH1RB_0RJ1RA_1RJ1LH_1LS0LH_1RA1LH_1RB0RA_1LS1RA_0LP0RF_1LP0RB_0RB---_1RB0LW_1RF0LS_1RB1LS_---0RB_---0LG_---0LW_---1LW_0RM1LS_1RM0LH_0RB0LG_---1LG".
Definition tm1 := TM'_from_str "1LB1RF_---0LC_0RG0LD_1LB0LE_1RF1LE_0RH0RG_1RH1RG_1RA1LE".
Definition tm2 := TM'_from_str "1LB1RF_1RI0LC_0RG0LD_1LB0LE_1RF1LE_0RH0RG_1RH1RG_1RA1LE_1RI1RI".
Definition l0 := [1;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "JSWGHABF".
Definition mp' := mp_from_str "JSWGHABF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM464.


Module TM465.
Definition tm := TM_from_str "1LB0RD_1RC1LC_---1LA_1RF1LE_0LD1LD_0RA1RA".
Definition tm' := TM_from_str "1LB0RC_0LC1LF_1RD1LE_0RA1RA_0LC1LC_---1LA".
Definition tm0 := TM'_from_str "1LO0RM_1LL1RM_0LH0RV_1LH1LO_0RJ---_1RJ1LD_---0LL_1LO1LL_---1LH_---1LO_---0LD_---1LD_0RV1LO_1RV1LP_1RA0LT_1RB1LT_1RA1RB_0LT1LT_0LO0LP_1LO1LP_0RA0RB_1RA1RB_1LO1LL_0RM1RM".
Definition tm0' := TM'_from_str "1LK0RI_1LX1RI_0LH0RN_1LH1LK_1RA---_0LT1LD_0LK0LX_1LK1LX_0RN1LK_1RN1LL_1RA0LT_1RB1LT_0RA0RB_1RA1RB_1LK1LX_0RI1RI_1RA1RB_0LT1LT_0LK0LL_1LK1LL_---1LH_---1LK_---0LD_---1LD".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RG_1RB0LD_1LC1LE_1RF1LD_1LH1RG_0RA1LC_---1LI_1LJ1LC_1LC1LH".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RG_1RB0LD_1LC1LE_1RF1LD_1LH1RG_0RA1LC_1RK1LI_1LJ1LC_1LC1LH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "VAOTPBMLDH".
Definition mp' := mp_from_str "NAKTLBIXDH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM465.


Module TM466.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1RD1LE_0RA1RA_0LC1LC_---1LA".
Definition tm' := TM_from_str "1LB0RC_0RC1LF_1RE1LD_0LC1LC_0RA1RA_---1LA".
Definition tm0 := TM'_from_str "1LK0RI_1LX1RI_0LH0RN_1LH1LK_1RA---_0LT1LD_0LK0LX_1LK1LX_0RN1LK_1RN1LL_1RA0LT_1RB1LT_0RA0RB_1RA1RB_1LK1LX_0RI1RI_1RA1RB_0LT1LT_0LK0LL_1LK1LL_---1LH_---1LK_---0LD_---1LD".
Definition tm0' := TM'_from_str "1LK0RI_1LX1RI_0LH0RR_1LH1LK_0RI---_1RI1LD_0RR0LX_1LK1LX_0RR1LK_1RR1LL_1RA0LP_1RB1LP_1RA1RB_0LP1LP_0LK0LL_1LK1LL_0RA0RB_1RA1RB_1LK1LX_0RI1RI_---1LH_---1LK_---0LD_---1LD".
Definition tm1 := TM'_from_str "1RB1RF_1LC0RG_1RB0LD_1LC1LE_1RF1LD_1LH1RG_0RA1LC_---1LI_1LJ1LC_1LC1LH".
Definition tm2 := TM'_from_str "1RB1RF_1LC0RG_1RB0LD_1LC1LE_1RF1LD_1LH1RG_0RA1LC_1RK1LI_1LJ1LC_1LC1LH_1RK1RK".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "NAKTLBIXDH".
Definition mp' := mp_from_str "RAKPLBIXDH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM466.


Module TM467.
Definition tm := TM_from_str "1LB0RE_0LC1LC_0LD1RA_1RD0RA_0RF1RC_---1LD".
Definition tm' := TM_from_str "1LB0RE_0LC1LC_0LD1RA_1RD0RA_1RF1RC_---0RA".
Definition tm0 := TM'_from_str "1LK0RQ_1LL1RQ_0LH0RU_1LH0RJ_0LO1LO_1LL1RQ_0LK0LL_1LK1LL_1RN0RB_1LK1RB_0LO1LL_1LO1RQ_0RN0RA_1RN1RA_1RN1LK_1RA0RQ_0RU0RJ_1RU1RJ_---1LK_1RA1RB_---1RA_---0RQ_---0LP_---1LP".
Definition tm0' := TM'_from_str "1LK0RQ_1LL1RQ_0LH0RV_1LH0RJ_0LO1LO_1LL1RQ_0LK0LL_1LK1LL_1RN0RB_1LK1RB_0LO1LL_1LO1RQ_0RN0RA_1RN1RA_1RN1LK_1RA0RQ_0RV0RJ_1RV1RJ_---1LK_1RA1RB_---0RA_---1RA_---1LK_---0RQ".
Definition tm1 := TM'_from_str "1LB0RF_0LD1LC_1LD1RF_1RE1LB_1RE1RA_0RI0RG_1LB1RH_1LC1RF_---1RA".
Definition tm2 := TM'_from_str "1LB0RF_0LD1LC_1LD1RF_1RE1LB_1RE1RA_0RI0RG_1LB1RH_1LC1RF_1RJ1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;0;0;1]%N.
Definition mp := mp_from_str "AKLONQJBU".
Definition mp' := mp_from_str "AKLONQJBV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM467.


Module TM468.
Definition tm := TM_from_str "1LB0LA_1RC1LF_0RD0RC_0LE0LB_1RA---_1LA1LD".
Definition tm' := TM_from_str "1LB0LA_1RC1LF_0RD0RC_1LE0LB_1LF---_1LA1LD".
Definition tm0 := TM'_from_str "1RI0LH_1LX0LC_0LH0LC_1LH1LC_0RJ1LD_1RJ1LP_1RM0LX_1RI1LX_0RM0RI_1RM1RI_1LX0RM_1RM0RI_1LX1RM_---0LX_0LS0LG_1LS1LG_0RB---_1RB---_1LX---_0LC---_1LH1LS_1LC1LG_0LD0LP_1LD1LP".
Definition tm0' := TM'_from_str "1RI0LH_1LX0LC_0LH0LC_1LH1LC_0RJ1LD_1RJ1LP_1RM0LX_1RI1LX_0RM0RI_1RM1RI_1LX0RM_1RM0RI_1LX1RM_---0LX_0LT0LG_1LT1LG_1LD---_1LP---_0LX---_1LX---_1LH1LT_1LC1LG_0LD0LP_1LD1LP".
Definition tm1 := TM'_from_str "1LB1RA_1LE1LC_1LH1LD_1RA0LB_1LF1LI_1RG1LB_0RA0RG_1LB---_0LF0LI".
Definition tm2 := TM'_from_str "1LB1RA_1LE1LC_1LH1LD_1RA0LB_1LF1LI_1RG1LB_0RA0RG_1LB1RJ_0LF0LI_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "MXPGDHISC".
Definition mp' := mp_from_str "MXPGDHITC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM468.


Module TM469.
Definition tm := TM_from_str "1RB1LE_1RC1RA_0LD0LB_1LE1LD_1RF0LA_---0RE".
Definition tm' := TM_from_str "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE".
Definition tm0 := TM'_from_str "0RF1RQ_1RF1LC_1RJ0LT_1RB1LT_0RJ0RB_1RJ1RB_0LP1RF_1RF1LC_0LT0LP_0LP1RF_0LO0LG_1LO1LG_1RQ1LT_1LC1LP_0LT0LP_1LT1LP_0RV1RJ_1RV0LT_---0LC_1RQ1LC_---0RQ_---1RQ_---0RV_---1RJ".
Definition tm0' := TM'_from_str "0RF1RQ_1RF1LC_1RJ0LT_1RB1LT_0RJ0RB_1RJ1RB_0LP1RF_1RF1LC_0LT0RF_0LP1RF_0LO1RJ_1LO1RB_1RQ1LT_1LC1LP_0LT0LP_1LT1LP_0RV1RJ_1RV0LT_---0LC_1RQ1LC_---0RQ_---1RQ_---0RV_---1RJ".
Definition tm1 := TM'_from_str "1RB1RF_0LC1RA_1LD1LC_1RE1LG_0RH1RB_1RA1LG_1RB0LD_---1RE".
Definition tm2 := TM'_from_str "1RB1RF_0LC1RA_1LD1LC_1RE1LG_0RH1RB_1RA1LG_1RB0LD_1RI1RE_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "FJPTQBCV".
Definition mp' := mp_from_str "FJPTQBCV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM469.


Module TM470.
Definition tm := TM_from_str "1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---0RA".
Definition tm' := TM_from_str "1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB".
Definition tm0 := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1RU1LC_0RI0RU_1RI1RU_0RM---_0RA0RA_0RM0RA_1RM1RA_1LP0RF_0LC1RI_1LP0LC_1LS0LT_0LP0LS_1LP1LS_1RI1LC_0LC1LT_0LC0LT_1LC1LT_---0RA_---1RA_---0RF_---1RI".
Definition tm0' := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1RU1LC_0RI0RU_1RI1RU_0RM---_0RA0RA_0RM0RA_1RM1RA_1LP0RF_0LC1RI_1LP0LC_1LS0LT_0LP0LS_1LP1LS_1RI1LC_0LC1LT_0LC0LT_1LC1LT_---0RA_---0RA_---0LH_---1LH".
Definition tm1 := TM'_from_str "0RB0RG_1LC0LE_1LC1LD_0LE0LF_1RA0LE_1LE1LF_0RH1RA_1RA1RI_---0RG".
Definition tm2 := TM'_from_str "0RB0RG_1LC0LE_1LC1LD_0LE0LF_1RA0LE_1LE1LF_0RH1RA_1RA1RI_1RJ0RG_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "IMPSCTAFU".
Definition mp' := mp_from_str "IMPSCTAFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM470.


Module TM471.
Definition tm := TM_from_str "1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA1LF".
Definition tm' := TM_from_str "1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA".
Definition tm0 := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_---1LC_0RI---_1RI---_0RM---_0RU---_0RM0RU_1RM1RU_1LP0RA_0LC1RI_1LP0LC_1LS0LT_0LP0LS_1LP1LS_1RI1LC_0LC1LT_0LC0LT_1LC1LT_0RA1RI_1RA1LX_0RF0LX_1RI1LX".
Definition tm0' := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_---1LC_0RI---_1RI---_0RM---_0RU---_0RM0RU_1RM1RU_1LP0RA_0LC1RI_1LP0LC_1LS0LT_0LP0LS_1LP1LS_1RI1LC_0LC1LT_0LC0LT_1LC1LT_0RA1RI_1RA0LC_0RF0LC_1RI1LC".
Definition tm1 := TM'_from_str "0RB0RG_1LC0LE_1LC1LD_0LE0LF_1RA0LE_1LE1LF_0RH1RA_0RI1RA_1RA---".
Definition tm2 := TM'_from_str "0RB0RG_1LC0LE_1LC1LD_0LE0LF_1RA0LE_1LE1LF_0RH1RA_0RI1RA_1RA1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "IMPSCTUAF".
Definition mp' := mp_from_str "IMPSCTUAF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM471.


Module TM472.
Definition tm := TM_from_str "1RB0RF_1RC1LC_1LD1RA_---0LE_1RB0LB_1RE0LF".
Definition tm' := TM_from_str "1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1RJ0RR_1RU1RF_0RJ1LP_1RJ1RU_1LS0LL_1RB1LL_---0RB_1LS1RB_0LP1RF_1LP1RU_---1RJ_---0LG_---0LS_---1LS_0RF1LS_1RF0LL_1RJ0LG_1RU1LG_0RR1RF_1RR0LW_1RF0LW_0LL1LW".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LL_1RJ0LG_1RU1LG_0RJ1LP_1RJ1RU_1LC0LL_1RR1LL_---0RR_1LC1RR_0LP1RF_1LP1RU_---1RJ_---0LG_---0LC_---1LC_1LT0RU_1RF1RU_0LT0RB_1LT1RF_0RB1RF_1RB0LW_1RF0LW_0LL1LW".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RI_1RB0LD_1LC0LE_1LH1RF_0RG1RA_1RA0LE_---1LC_1RA1RF".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RI_1RB0LD_1LC0LE_1LH1RF_0RG1RA_1RA0LE_1RJ1LC_1RA1RF_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "FJSGLURPB".
Definition mp' := mp_from_str "FJCGLUBPR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM472.


Module TM473.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1LD0RE_1RA1LD_1RF0RA_1RD---".
Definition tm' := TM_from_str "1LB1RE_1LC0LB_1RD0RE_1RA1LD_1RF0RA_1RD---".
Definition tm0 := TM'_from_str "1LL0RR_1LG1RR_0LH1RV_1LH1RA_1LP0LL_0RA0LG_0LL0LG_1LL1LG_1RR0RQ_1LP1RQ_0LP0RV_1LP0RA_0RB1RR_1RB1LP_1LG0LP_1RR1LP_0RV0RA_1RV1RA_1RN1LL_---0RR_0RN---_1RN---_1RB---_1LP---".
Definition tm0' := TM'_from_str "1LL0RR_1LG1RR_0LH1RV_1LH1RA_1LP0LL_0RA0LG_0LL0LG_1LL1LG_0RN0RQ_1RN1RQ_1RB0RV_1LP0RA_0RB1RR_1RB1LP_1LG0LP_1RR1LP_0RV0RA_1RV1RA_1RN1LL_---0RR_0RN---_1RN---_1RB---_1LP---".
Definition tm1 := TM'_from_str "1LB0RC_1LH0RA_1RD1RA_1RE---_1RF1LH_1LG1RC_0LB0LG_1RC1LH".
Definition tm2 := TM'_from_str "1LB0RC_1LH0RA_1RD1RA_1RE1RI_1RF1LH_1LG1RC_0LB0LG_1RC1LH_1RI1RI".
Definition l0 := [1;1;0;0;1;1;0;1]%N.
Definition mp := mp_from_str "ALRVNBGP".
Definition mp' := mp_from_str "ALRVNBGP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM473.


Module TM474.
Definition tm := TM_from_str "1LB1LC_1RC0RF_1LF0RD_1LE1RB_1RF---_1RD0LA".
Definition tm' := TM_from_str "1LB0RD_1RC0RF_1LF0RD_0LE1RB_1LC---_1RD0LA".
Definition tm0 := TM'_from_str "1RM1LX_0LH0RF_0LH0LL_1LH1LL_0RJ0RU_1RJ1RU_1LC0RN_1RM0LH_1RF0RM_1LC1RM_0LX0LL_1LX0RF_0LL0RF_---1RF_0LT1RJ_1LT1RU_0RV---_1RV---_1RN---_0LL---_0RN0LH_1RN0LL_---0LC_1RF1LC".
Definition tm0' := TM'_from_str "1RM0RM_0LH1RM_0LH0LL_1LH0RF_0RJ0RU_1RJ1RU_1LC0RN_1RM0LH_1RF0RM_1LC1RM_0LX0LL_1LX0RF_0LL0RF_---1RF_0LS1RJ_1LS1RU_1LX---_0RF---_0LL---_1LL---_0RN0LH_1RN0LL_---0LC_1RF1LC".
Definition tm1 := TM'_from_str "0LB0RC_1LF0RC_1RD1RH_1LE1RA_0LG0LB_1RC1LE_1RA0LG_0RI0LG_---1RC".
Definition tm2 := TM'_from_str "0LB0RC_1LF0RC_1RD1RH_1LE1RA_0LG0LB_1RC1LE_1RA0LG_0RI0LG_1RJ1RC_1RJ1RJ".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "MLFJCXHUN".
Definition mp' := mp_from_str "MLFJCXHUN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM474.


Module TM475.
Definition tm := TM_from_str "1LB0RD_1RC0RF_1LF0RD_0LE1RB_1LC---_1RD0LA".
Definition tm' := TM_from_str "1LB1LC_1RC0RF_1LF0RD_0LE1RB_1LC---_1RD0LA".
Definition tm0 := TM'_from_str "1RM0RM_0LH1RM_0LH0LL_1LH0RF_0RJ0RU_1RJ1RU_1LC0RN_1RM0LH_1RF0RM_1LC1RM_0LX0LL_1LX0RF_0LL0RF_---1RF_0LS1RJ_1LS1RU_1LX---_0RF---_0LL---_1LL---_0RN0LH_1RN0LL_---0LC_1RF1LC".
Definition tm0' := TM'_from_str "1RM1LX_0LH0RF_0LH0LL_1LH1LL_0RJ0RU_1RJ1RU_1LC0RN_1RM0LH_1RF0RM_1LC1RM_0LX0LL_1LX0RF_0LL0RF_---1RF_0LS1RJ_1LS1RU_1LX---_0RF---_0LL---_1LL---_0RN0LH_1RN0LL_---0LC_1RF1LC".
Definition tm1 := TM'_from_str "0LB0RC_1LF0RC_1RD1RH_1LE1RA_0LG0LB_1RC1LE_1RA0LG_0RI0LG_---1RC".
Definition tm2 := TM'_from_str "0LB0RC_1LF0RC_1RD1RH_1LE1RA_0LG0LB_1RC1LE_1RA0LG_0RI0LG_1RJ1RC_1RJ1RJ".
Definition l0 := [1;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "MLFJCXHUN".
Definition mp' := mp_from_str "MLFJCXHUN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 33 33.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM475.


Module TM476.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA0RF_0LB---".
Definition tm' := TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0RD---".
Definition tm0 := TM'_from_str "1RB0RI_1LG1RI_0LH0RM_1LH0RB_0RJ1RM_1RJ0LG_1RM0LG_1RB1LG_0RM0RB_1RM1RB_0LH1LG_0RR1RI_0LH0RR_0RM1RR_0LC1RA_1LC1RU_0RA0RU_1RA1RU_1RB1RM_0RI---_1RM---_0LG---_0LG---_1LG---".
Definition tm0' := TM'_from_str "1RB0RI_1LG1RI_0LH0RM_1LH0RB_0RJ1RM_1RJ0LG_1RM0LG_1RB1LG_0RM0RB_1RM1RB_0LH1LG_0RR1RI_0LH0RR_0RM1RR_0LC1RA_1LC1RV_0RA0RV_1RA1RV_1RB1RM_0RI---_0RM---_1RM---_0LH---_0RR---".
Definition tm1 := TM'_from_str "0RB0RD_0LC0RF_1RD1LE_1LE1RA_1RB0LE_1RG1RH_1RD0RA_1RB---".
Definition tm2 := TM'_from_str "0RB0RD_0LC0RF_1RD1LE_1LE1RA_1RB0LE_1RG1RH_1RD0RA_1RB1RI_1RI1RI".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "IMHBGRAU".
Definition mp' := mp_from_str "IMHBGRAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM476.


Module TM477.
Definition tm := TM_from_str "1LB0RE_1RC0LB_0LD1RA_0RA1RE_0RF---_0LA1RD".
Definition tm' := TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0RD---".
Definition tm0 := TM'_from_str "1RB0RQ_1LG1RQ_0LH0RU_1LH---_0RJ1RU_1RJ0LG_1RU0LG_1RB1LG_1RB0RB_1RU1RB_0LO1LG_1LO1RQ_0RA0RR_1RA1RR_1RB1RU_0RQ---_0RU---_1RU---_0LH---_0RN---_0LH0RN_0RU1RN_0LC1RA_1LC1RR".
Definition tm0' := TM'_from_str "1RB0RU_1LG1RU_0LH0RM_1LH---_0RJ1RM_1RJ0LG_1RM0LG_1RB1LG_0RM0RB_1RM1RB_0LH1LG_0RR1RU_0LH0RR_0RM1RR_0LC1RA_1LC1RV_0RA0RV_1RA1RV_1RB1RM_0RU---_0RM---_1RM---_0LH---_0RR---".
Definition tm1 := TM'_from_str "0RB---_0LC0RF_1RD1LE_1LE1RA_1RB0LE_1RG1RH_1RD0RA_1RB---".
Definition tm2 := TM'_from_str "0RB1RI_0LC0RF_1RD1LE_1LE1RA_1RB0LE_1RG1RH_1RD0RA_1RB1RI_1RI1RI".
Definition l0 := [1;0;1;0;0;0;1;0]%N.
Definition mp := mp_from_str "QUHBGNAR".
Definition mp' := mp_from_str "UMHBGRAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM477.


Module TM478.
Definition tm := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD1RF_0LB---".
Definition tm' := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD1RF_1LA---".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LL1RB_1RQ0RM_1LP0RQ_1LL1RQ_0LL0RM_1LL0RV_1RN1LP_1LG1LL_0LP0LL_1LP1LL_0RB0LL_1RB0RM_1RF0LG_1RN1LG_0RM0RV_1RM1RV_0RB0RM_0LL---_0LL---_0RM---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LL1RB_1RQ0RM_1LP0RQ_1LL1RQ_0LL0RM_1LL0RV_1RN1LP_1LG1LL_0LP0LL_1LP1LL_0RB0LL_1RB0RM_1RF0LG_1RN1LG_0RM0RV_1RM1RV_0RB0RM_0LL---_1RQ---_0RM---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB0RF_1RC1RA_1LD1RH_1LE1LD_1RA1LG_0RB0LD_0LD0RF_0RF0RI_0RF---".
Definition tm2 := TM'_from_str "1RB0RF_1RC1RA_1LD1RH_1LE1LD_1RA1LG_0RB0LD_0LD0RF_0RF0RI_0RF1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;1;1]%N.
Definition mp := mp_from_str "NBFLPMGQV".
Definition mp' := mp_from_str "NBFLPMGQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM478.


Module TM479.
Definition tm := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD1RF_1LA---".
Definition tm' := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LL1RB_1RQ0RM_1LP0RQ_1LL1RQ_0LL0RM_1LL0RV_1RN1LP_1LG1LL_0LP0LL_1LP1LL_0RB0LL_1RB0RM_1RF0LG_1RN1LG_0RM0RV_1RM1RV_0RB0RM_0LL---_1RQ---_0RM---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LL1RB_1RQ0RM_1LP0RQ_1LL1RQ_0LL0RM_1LL0RU_1RN1LP_1LG1LL_0LP0LL_1LP1LL_0RB0LL_1RB0RM_1RF0LG_1RN1LG_0RM0RU_1RM1RU_0RB0RM_0LL---_0RM---_1RM---_0RB---_0LL---".
Definition tm1 := TM'_from_str "1RB0RF_1RC1RA_1LD1RH_1LE1LD_1RA1LG_0RB0LD_0LD0RF_0RF0RI_0RF---".
Definition tm2 := TM'_from_str "1RB0RF_1RC1RA_1LD1RH_1LE1LD_1RA1LG_0RB0LD_0LD0RF_0RF0RI_0RF1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;1;1]%N.
Definition mp := mp_from_str "NBFLPMGQV".
Definition mp' := mp_from_str "NBFLPMGQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM479.


Module TM480.
Definition tm := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LD1RC".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RF1RD_---1LA_0LB1LE_1LE1RC".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LG0LL_1RA1LG_1RJ0RA_1LG1RA_0LL0RF_1LL0RQ_0RV0RM_1RV1RM_1LT---_1RJ1LG_---1LG_---1LT_---0LT_---1LT_0LL1LG_0RF1LT_0LG0LT_1LG1LT_---0RJ_1LT1RJ_0LP1RV_1LP1RM".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LG0LL_1RA1LG_1RJ0RA_1LG1RA_0LL0RF_1LL0RQ_0RV0RN_1RV1RN_1LT---_1RJ1LG_---1RA_---1LG_---0LD_---1LD_0LL1LG_0RF1LT_0LG0LT_1LG1LT_1LG0RJ_1LT1RJ_0LT1RV_1LT1RN".
Definition tm1 := TM'_from_str "0LB1LF_1RC1LF_1RD1RI_1LE1RC_1LF1LE_0LB0RG_1LF1RH_0RG0RA_---1LF".
Definition tm2 := TM'_from_str "0LB1LF_1RC1LF_1RD1RI_1LE1RC_1LF1LE_0LB0RG_1LF1RH_0RG0RA_1RJ1LF_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "QLJVTGFAM".
Definition mp' := mp_from_str "QLJVTGFAN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM480.


Module TM481.
Definition tm := TM_from_str "1RB0RE_1LC0RA_1RF1RD_---1LA_0LB1LE_1LE1RC".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LG0LL_1RA1LG_1RJ0RA_1LG1RA_0LL0RF_1LL0RQ_0RV0RN_1RV1RN_1LT---_1RJ1LG_---1RA_---1LG_---0LD_---1LD_0LL1LG_0RF1LT_0LG0LT_1LG1LT_1LG0RJ_1LT1RJ_0LT1RV_1LT1RN".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LG0LL_1RA1LG_1RJ0RA_1LG1RA_0LL0RF_1LL0RQ_0RV0RM_1RV1RM_1LT---_1RJ1LG_---1LG_---1LT_---0LT_---1LT_0LL1LG_0RF1LT_0LG0LT_1LG1LT_1LG0RJ_1LT1RJ_0LT1RV_1LT1RM".
Definition tm1 := TM'_from_str "0LB1LF_1RC1LF_1RD1RI_1LE1RC_1LF1LE_0LB0RG_1LF1RH_0RG0RA_---1LF".
Definition tm2 := TM'_from_str "0LB1LF_1RC1LF_1RD1RI_1LE1RC_1LF1LE_0LB0RG_1LF1RH_0RG0RA_1RJ1LF_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "QLJVTGFAN".
Definition mp' := mp_from_str "QLJVTGFAM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM481.


Module TM482.
Definition tm := TM_from_str "1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LC---".
Definition tm' := TM_from_str "1RB---_1RC0LD_1RD0RF_1LB1LE_0LB0RE_1RB0RA".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1RJ0RF_0LT---_0RJ0LH_1RJ0LT_1RN0LO_1RA1LO_0RN0RA_1RN1RA_1LO0RF_0RQ0RV_1RA1LG_1LO0RQ_0LH0LT_1LH1LT_1RN0RQ_0LO1RQ_0LG1RN_1LG0RQ_1LO---_0RF---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RJ---_0LT---_0RJ0LH_1RJ0LT_1RN0LO_1RU1LO_0RN0RU_1RN1RU_1LO0RF_0RQ0RA_1RU1LG_1LO0RQ_0LH0LT_1LH1LT_1RN0RQ_0LO1RQ_0LG1RN_1LG0RQ_0RF0RA_1RF1RA_1RJ0RF_0LT---".
Definition tm1 := TM'_from_str "1RB0LE_1RC1RI_1LD0RF_0LH0LE_1LG0RF_1RC0RF_1RC0LD_1RI1LD_0RA0RJ_0RA---".
Definition tm2 := TM'_from_str "1RB0LE_1RC1RI_1LD0RF_0LH0LE_1LG0RF_1RC0RF_1RC0LD_1RI1LD_0RA0RJ_0RA1RK_1RK1RK".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "FJNOTQGHAV".
Definition mp' := mp_from_str "FJNOTQGHUA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM482.


Module TM483.
Definition tm := TM_from_str "1RB0LE_1LB1RC_1RF1RD_1LA0RA_1LC1LD_---1RA".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA".
Definition tm0 := TM'_from_str "0RF0LL_1RF0LP_1RN0LS_1RJ1LS_1LH0RJ_1RN1RJ_0LH1RV_1LH1RN_0RV0RN_1RV1RN_---1LS_1RB1RA_1RJ0RA_1LS1RA_0LD0RF_1LD0LL_1RB1LD_1RA0LL_0LL0LP_1LL1LP_---0RB_---1RB_---1RF_---0LP".
Definition tm0' := TM'_from_str "0RF0LT_1RF0LL_1RJ0LO_1RR1LO_0RJ0RR_1RJ1RR_1LO1RV_1RA1RJ_1RR0RA_1LO1RA_0LD0RF_1LD0LT_1RB1LD_1RA0LT_0LT0LL_1LT1LL_0RV0RJ_1RV1RJ_---1LO_1RB1RA_---0RB_---1RB_---1RF_---0LL".
Definition tm1 := TM'_from_str "1RB1RH_1LC1RI_0LF0LD_1LE0LF_1RH1LC_1RG1RI_1RA0LD_1RJ1RB_0RA0LF_---1RG".
Definition tm2 := TM'_from_str "1RB1RH_1LC1RI_0LF0LD_1LE0LF_1RH1LC_1RG1RI_1RA0LD_1RJ1RB_0RA0LF_1RK1RG_1RK1RK".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "FNSPDLBJAV".
Definition mp' := mp_from_str "FJOLDTBRAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM483.


Module TM484.
Definition tm := TM_from_str "1RB0LA_0RC---_1RD1RE_1LA1LD_0LF0RF_0RC1RC".
Definition tm' := TM_from_str "1RB0LA_0RC1RC_1RD1RF_1LE1LD_---0LA_0LB0RB".
Definition tm0 := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_---1LC_0RI---_1RI---_0RN---_0RR---_0RN0RR_1RN1RR_1LC1RN_1LP1RU_---1LD_1LC1LP_0LD0LP_1LD1LP_0RN0RU_1RN1RU_0LW0RI_1LW0RJ_0RI0RJ_1RI1RJ_0RN1RN_0RR1RR".
Definition tm0' := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1RJ1LC_0RI0RJ_1RI1RJ_0RN1RN_0RV1RV_0RN0RV_1RN1RV_1LC1RN_1LP1RE_---1LT_1LC1LP_0LT0LP_1LT1LP_---1RI_---0LC_---0LC_---1LC_0RN0RE_1RN1RE_0LG0RI_1LG0RJ".
Definition tm1 := TM'_from_str "0RB0RH_0RC0RE_1LD1LF_1RB0LD_1RC1RA_1LG1LF_---1LD_1RC1RE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0RE_1LD1LF_1RB0LD_1RC1RA_1LG1LF_1RI1LD_1RC1RE_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "UINCRPDJ".
Definition mp' := mp_from_str "EINCVPTJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM484.


Module TM485.
Definition tm := TM_from_str "1RB0LA_0RC1RC_1RD1RF_1LE1LD_---0LA_0LB0RB".
Definition tm' := TM_from_str "1RB0LA_0RC1RC_1RD1RF_1LE1LD_---0LA_1RD0RB".
Definition tm0 := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1RJ1LC_0RI0RJ_1RI1RJ_0RN1RN_0RV1RV_0RN0RV_1RN1RV_1LC1RN_1LP1RE_---1LT_1LC1LP_0LT0LP_1LT1LP_---1RI_---0LC_---0LC_---1LC_0RN0RE_1RN1RE_0LG0RI_1LG0RJ".
Definition tm0' := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1RJ1LC_0RI0RJ_1RI1RJ_0RN1RN_0RV1RV_0RN0RV_1RN1RV_1LC1RN_1LP1RE_---1LT_1LC1LP_0LT0LP_1LT1LP_---1RI_---0LC_---0LC_---1LC_0RN0RE_1RN1RE_1LC0RI_1LP0RJ".
Definition tm1 := TM'_from_str "0RB0RH_0RC0RE_1LD1LF_1RB0LD_1RC1RA_1LG1LF_---1LD_1RC1RE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0RE_1LD1LF_1RB0LD_1RC1RA_1LG1LF_1RI1LD_1RC1RE_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "EINCVPTJ".
Definition mp' := mp_from_str "EINCVPTJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM485.


Module TM486.
Definition tm := TM_from_str "1RB0LA_0RC1RC_1RD1RF_1LE1LD_---0LA_1RD0RB".
Definition tm' := TM_from_str "1RB0LA_0RC---_1RD1RE_1LA1LD_1RD0RF_0RC1RC".
Definition tm0 := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_1RJ1LC_0RI0RJ_1RI1RJ_0RN1RN_0RV1RV_0RN0RV_1RN1RV_1LC1RN_1LP1RE_---1LT_1LC1LP_0LT0LP_1LT1LP_---1RI_---0LC_---0LC_---1LC_0RN0RE_1RN1RE_1LC0RI_1LP0RJ".
Definition tm0' := TM'_from_str "0RF1RI_1RF0LC_1RI0LC_---1LC_0RI---_1RI---_0RN---_0RR---_0RN0RR_1RN1RR_1LC1RN_1LP1RU_---1LD_1LC1LP_0LD0LP_1LD1LP_0RN0RU_1RN1RU_1LC0RI_1LP0RJ_0RI0RJ_1RI1RJ_0RN1RN_0RR1RR".
Definition tm1 := TM'_from_str "0RB0RH_0RC0RE_1LD1LF_1RB0LD_1RC1RA_1LG1LF_---1LD_1RC1RE".
Definition tm2 := TM'_from_str "0RB0RH_0RC0RE_1LD1LF_1RB0LD_1RC1RA_1LG1LF_1RI1LD_1RC1RE_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "EINCVPTJ".
Definition mp' := mp_from_str "UINCRPDJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM486.


Module TM487.
Definition tm := TM_from_str "1RB1RA_1LC0RC_---0LD_0LE0LF_1RE0RA_0LF1LB".
Definition tm' := TM_from_str "1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LO1RF_1RI1RB_---0RI_1LO1RI_0LL---_1LL0LS_---0LS_---0LW_---0LO_---1LO_1RR0LW_0RF0LH_0LS0LW_1LS1LW_0RR0RA_1RR1RA_1RR0RF_1RA0RB_0LW1LL_0LH0LS_0LW0LH_1LW1LH".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LO1RF_1RI1RB_---0RI_1LO1RI_0LL---_1LL0LS_---0LS_---0LW_---0LO_---1LO_1RR0RU_0RF1RU_0LS0LW_1LS1LL_0RR0RA_1RR1RA_1RR0RF_1RA0RB_0LW1LL_0LH0LS_0LW0LH_1LW1LH".
Definition tm1 := TM'_from_str "0RB0RF_1LC1RJ_0LD0LG_1RE0RB_1RE1RA_1RB1RF_0LG0LH_1LI0LD_---1LC_---0LD".
Definition tm2 := TM'_from_str "0RB0RF_1LC1RJ_0LD0LG_1RE0RB_1RE1RA_1RB1RF_0LG0LH_1LI0LD_1RK1LC_1RK0LD_1RK1RK".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "AFOSRBWHLI".
Definition mp' := mp_from_str "AFOSRBWHLI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM487.


Module TM488.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RC---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_0RF1RA_0LA---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ1RJ_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1RJ1RF_---1RQ_0RJ---_1RJ---_1LO---_1LL---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RU_1RF0RB_0RJ1RJ_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RU0RB_1RU1RB_1RJ1RF_---1RQ_1RJ---_0RU---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBV".
Definition mp' := mp_from_str "JOFLPQBU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM488.


Module TM489.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_0RF1RA_0LA---".
Definition tm' := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LB---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RU_1RF0RB_0RJ1RJ_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RU0RB_1RU1RB_1RJ1RF_---1RQ_1RJ---_0RU---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1RJ1RF_---1RQ_1LO---_1RJ---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBU".
Definition mp' := mp_from_str "JOFLPQBV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM489.


Module TM490.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LB---".
Definition tm' := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1RJ1RF_---1RQ_1LO---_1RJ---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1RJ1RV_---1RA_0RJ---_1RJ---_1LO---_1LL---_0RA1LP_1LO1LL_0LP0LL_1LP1LL_0RQ0RV_1RQ0LO_0RV0LO_0RA1LO_0RV0RA_1RV1RA_1RJ0RF_1RV0RR_0RJ0RV_1RJ1RV_1LO1RJ_1LL1RV".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBV".
Definition mp' := mp_from_str "JOVLPARF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM490.


Module TM491.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LC---".
Definition tm' := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LC---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ0LL_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_0LL1RF_---1RQ_0LP---_0LL---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_0LL1RF_---1RQ_0LP---_0LL---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_0LD---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_0LD1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBV".
Definition mp' := mp_from_str "JOFLPQBV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM491.


Module TM492.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RA---".
Definition tm' := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1RA---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ1RB_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1RB1RF_---1RQ_0RB---_1RB---_1RF---_1RQ---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1RB1RF_---1RQ_0RB---_1RB---_1RF---_1RQ---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RG---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RG1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBV".
Definition mp' := mp_from_str "JOFLPQBV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM492.


Module TM493.
Definition tm := TM_from_str "1LB1RF_0LC0LB_0RD1RA_1RC0RE_0RA---_1RA1LC".
Definition tm' := TM_from_str "1LB1RF_0LC0LB_0RD1RA_1RC0RE_0RA---_1RA1RF".
Definition tm0 := TM'_from_str "1LK0RV_1LG1RV_0LH1RB_1LH1RV_0RJ0LK_1LG0LG_0LK0LG_1LK1LG_0RM0RB_1RM1RB_0RJ1LG_0RQ1RV_0RJ0RQ_1RJ1RQ_1RM0RA_1RB---_0RA---_1RA---_1LK---_0RV---_0RB0RQ_1RB1RV_1LG0LL_1RV1LL".
Definition tm0' := TM'_from_str "1LK0RV_1LG1RV_0LH1RB_1LH1RV_0RJ0LK_1LG0LG_0LK0LG_1LK1LG_0RM0RB_1RM1RB_0RJ1LG_0RQ1RV_0RJ0RQ_1RJ1RQ_1RM0RA_1RB---_0RA---_1RA---_1LK---_0RV---_0RB0RV_1RB1RV_1LG1RB_1RV1RV".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LB_0RD1LB_1RE1RA_0RD0RF_0RG---_1LC0RH_1RA1RH".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LB_0RD1LB_1RE1RA_0RD0RF_0RG1RI_1LC0RH_1RA1RH_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BGKJMQAV".
Definition mp' := mp_from_str "BGKJMQAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM493.


Module TM494.
Definition tm := TM_from_str "1LB0RB_0RC1LE_---1RD_1RE0RB_0LF0RD_1LD1LA".
Definition tm' := TM_from_str "1LB0LF_0RC1LE_---1RD_1RE0RB_0LF0RD_1LD1LA".
Definition tm0 := TM'_from_str "0RN0RE_1LT1RE_0LH0RI_1LH1LW_0RI1LW_1RI0RE_---0LT_0RN1LT_---0RN_---1RN_---1RR_---1RE_0RR0RE_1RR1RE_0LD0RI_1RM1LW_0LP0RM_0LD1RM_0LW0RR_1LW0RE_1RM1LH_1LW1LW_0LP0LD_1LP1LD".
Definition tm0' := TM'_from_str "0RN0LP_1LT0LD_0LH0LW_1LH1LW_0RI1LW_1RI0RE_---0LT_0RN1LT_---0RN_---1RN_---1RR_---1RE_0RR0RE_1RR1RE_0LD0RI_1RM1LW_0LP0RM_0LD1RM_0LW0RR_1LW0RE_1RM1LH_1LW1LW_0LP0LD_1LP1LD".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LE_0RI1LD_1LE0RH_0LF0LB_1RG1LE_0RA0RH_0RJ1LE_1RA1RH_---0RI".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LE_0RI1LD_1LE0RH_0LF0LB_1RG1LE_0RA0RH_0RJ1LE_1RA1RH_1RK0RI_1RK1RK".
Definition l0 := [0;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "RDHTWPMENI".
Definition mp' := mp_from_str "RDHTWPMENI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM494.


Module TM495.
Definition tm := TM_from_str "1LB0LB_1RB0RC_1LD1RC_1LE0LA_1LF1LA_---0RA".
Definition tm' := TM_from_str "1LB0LB_1RB0RC_1LD1RC_1LE0LA_0LF1LA_---1RB".
Definition tm0 := TM'_from_str "1RI1RF_0RJ1LT_0LH0LG_1LH1LG_0RF0RI_1RF1RI_1RF1LT_1RI0RJ_1LT0RJ_1LC1RJ_0LP1LC_1LP1RJ_1LX0LH_1LD0LG_0LT0LC_1LT1LC_---1LH_1RF1LG_0LX0LD_1LX1LD_---0RA_---1RA_---1RI_---1RF".
Definition tm0' := TM'_from_str "1RI1RF_0RJ1LT_0LH0LG_1LH1LG_0RF0RI_1RF1RI_1RF1LT_1RI0RJ_1LT0RJ_1LC1RJ_0LP1LC_1LP1RJ_1LW0LH_1LD0LG_0LT0LC_1LT1LC_---1LH_1RF1LG_0LW0LD_1LW1LD_---0RF_---1RF_---1RF_---1RI".
Definition tm1 := TM'_from_str "1LB1RA_0LF0LC_1RI1LD_1LH1LE_1LF1LC_1RG0RA_1LD0RA_---1RI_1RI1RG".
Definition tm2 := TM'_from_str "1LB1RA_0LF0LC_1RI1LD_1LH1LE_1LF1LC_1RG0RA_1LD0RA_1RJ1RI_1RI1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JCGTDHIXF".
Definition mp' := mp_from_str "JCGTDHIWF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM495.


Module TM496.
Definition tm := TM_from_str "1RB1RF_1LC0RA_1RA0LD_0LE1LC_0RC0LC_0LB---".
Definition tm' := TM_from_str "1RB1RF_1LC0RA_1RA0LD_0LE0RF_0RC0LC_0LB---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO0RF_1RA---_1RV0RA_1LO1RA_0LL0RF_1LL0RV_0RB0LS_1RB0LL_1RF0LO_1RV1LO_0RB1RV_0LK1LO_0LS0LL_1LS1LL_0RI1RF_1RI0LO_0RB0LK_0LS1LK_0LL---_0RF---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO0RF_1RA---_1RV0RA_1LO1RA_0LL0RF_1LL0RV_0RB0LS_1RB0LL_1RF0LO_1RV1LO_0RB0RU_0LK1RU_0LS0LL_1LS---_0RI1RF_1RI0LO_0RB0LK_0LS1LK_0LL---_0RF---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB---_1LC1RF_0LD0LH_0RE0LG_1RB1RA_0RB0RA_1RB0LC_1RA1LC".
Definition tm2 := TM'_from_str "0RB1RI_1LC1RF_0LD0LH_0RE0LG_1RB1RA_0RB0RA_1RB0LC_1RA1LC_1RI1RI".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "VFOSBAKL".
Definition mp' := mp_from_str "VFOSBAKL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM496.


Module TM497.
Definition tm := TM_from_str "1RB1RF_1LC0RA_1RA0LD_0LE0RF_0RC0LC_0LB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO0RF_1RA---_1RV0RA_1LO1RA_0LL0RF_1LL0RV_0RB0LS_1RB0LL_1RF0LO_1RV1LO_0RB0RU_0LK1RU_0LS0LL_1LS---_0RI1RF_1RI0LO_0RB0LK_0LS1LK_0LL---_0RF---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LO---_1RU---_1RA0RU_1LO1RU_0LL0RF_1LL0RA_0RV0LS_1RV0LL_1RF0LO_1RA1LO_0RV1RA_0LK1LO_0LS0LL_1LS1LL_0RI1RF_1RI0LO_0RV0LK_0LS1LK_0RF0RA_1RF1RA_1LO0RF_1RU---".
Definition tm1 := TM'_from_str "0RB---_1LC1RF_0LD0LH_0RE0LG_1RB1RA_0RB0RA_1RB0LC_1RA1LC".
Definition tm2 := TM'_from_str "0RB1RI_1LC1RF_0LD0LH_0RE0LG_1RB1RA_0RB0RA_1RB0LC_1RA1LC_1RI1RI".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "VFOSBAKL".
Definition mp' := mp_from_str "AFOSVUKL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM497.


Module TM498.
Definition tm := TM_from_str "1LB1LE_1RC0RA_1RD0RC_1LA0LF_1LD---_1RC1LB".
Definition tm' := TM_from_str "1LB1LE_1RC1LD_1RD0RC_1LA0LF_1LD---_1RC1LB".
Definition tm0 := TM'_from_str "1RI1LP_1LP---_0LH0LT_1LH1LT_0RJ0RA_1RJ1RA_1RN1RI_1RI1LP_0RN0RI_1RN1RI_1LT0RN_0LH0RI_1LH1RN_1LT0LH_0LD0LW_1LD1LW_1LD---_1LW---_0LP---_1LP---_0RJ1RI_1RJ1LP_1RN0LH_1RI1LH".
Definition tm0' := TM'_from_str "1RI1LP_1LP---_0LH0LT_1LH1LT_0RJ1LD_1RJ1LW_1RN0LP_1RI1LP_0RN0RI_1RN1RI_1LT0RN_0LH0RI_1LH1RN_1LT0LH_0LD0LW_1LD1LW_1LD---_1LW---_0LP---_1LP---_0RJ1RI_1RJ1LP_1RN0LH_1RI1LH".
Definition tm1 := TM'_from_str "1LB0LE_1LC---_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG".
Definition tm2 := TM'_from_str "1LB0LE_1LC1RH_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG_1RH1RH".
Definition l0 := [1;0;0;1;1;1;1;0]%N.
Definition mp := mp_from_str "NTPWHDI".
Definition mp' := mp_from_str "NTPWHDI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM498.


Module TM499.
Definition tm := TM_from_str "1LB1LE_1RC1LD_1RD0RC_1LA0LF_1LD---_1RC1LB".
Definition tm' := TM_from_str "1LB1LE_1RC1LD_1RD0RC_1LA0LF_1RF---_1RC1LB".
Definition tm0 := TM'_from_str "1RI1LP_1LP---_0LH0LT_1LH1LT_0RJ1LD_1RJ1LW_1RN0LP_1RI1LP_0RN0RI_1RN1RI_1LT0RN_0LH0RI_1LH1RN_1LT0LH_0LD0LW_1LD1LW_1LD---_1LW---_0LP---_1LP---_0RJ1RI_1RJ1LP_1RN0LH_1RI1LH".
Definition tm0' := TM'_from_str "1RI1LP_1LP---_0LH0LT_1LH1LT_0RJ1LD_1RJ1LW_1RN0LP_1RI1LP_0RN0RI_1RN1RI_1LT0RN_0LH0RI_1LH1RN_1LT0LH_0LD0LW_1LD1LW_0RV---_1RV---_1RJ---_1LP---_0RJ1RI_1RJ1LP_1RN0LH_1RI1LH".
Definition tm1 := TM'_from_str "1LB0LE_1LC---_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG".
Definition tm2 := TM'_from_str "1LB0LE_1LC1RH_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG_1RH1RH".
Definition l0 := [1;0;0;1;1;1;1;0]%N.
Definition mp := mp_from_str "NTPWHDI".
Definition mp' := mp_from_str "NTPWHDI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM499.


Module TM500.
Definition tm := TM_from_str "1LB1LE_1RC1LD_1RD0RC_1LA0LF_1RF---_1RC1LB".
Definition tm' := TM_from_str "1LB0LE_1RC1LD_1RD0RC_1LA0LF_1RA---_1RC1LB".
Definition tm0 := TM'_from_str "1RI1LP_1LP---_0LH0LT_1LH1LT_0RJ1LD_1RJ1LW_1RN0LP_1RI1LP_0RN0RI_1RN1RI_1LT0RN_0LH0RI_1LH1RN_1LT0LH_0LD0LW_1LD1LW_0RV---_1RV---_1RJ---_1LP---_0RJ1RI_1RJ1LP_1RN0LH_1RI1LH".
Definition tm0' := TM'_from_str "1RI1LP_1LP---_0LH0LS_1LH1LS_0RJ1LD_1RJ1LW_1RN0LP_1RI1LP_0RN0RI_1RN1RI_1LS0RN_0LH0RI_1LH1RN_1LS0LH_0LD0LW_1LD1LW_0RB---_1RB---_1LP---_------_0RJ1RI_1RJ1LP_1RN0LH_1RI1LH".
Definition tm1 := TM'_from_str "1LB0LE_1LC---_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG".
Definition tm2 := TM'_from_str "1LB0LE_1LC1RH_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG_1RH1RH".
Definition l0 := [1;0;0;1;1;1;1;0]%N.
Definition mp := mp_from_str "NTPWHDI".
Definition mp' := mp_from_str "NSPWHDI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM500.


Module TM501.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RD0RC_1LA0LF_1RA---_1RC1LB".
Definition tm' := TM_from_str "1LB1LE_1RC0RF_1RD0RC_1LA0LB_1LD---_0LA1LE".
Definition tm0 := TM'_from_str "1RI1LP_1LP---_0LH0LS_1LH1LS_0RJ1LD_1RJ1LW_1RN0LP_1RI1LP_0RN0RI_1RN1RI_1LS0RN_0LH0RI_1LH1RN_1LS0LH_0LD0LW_1LD1LW_0RB---_1RB---_1LP---_------_0RJ1RI_1RJ1LP_1RN0LH_1RI1LH".
Definition tm0' := TM'_from_str "1RI1LP_1LP---_0LH0LT_1LH1LT_0RJ0RU_1RJ1RU_1RN0LH_1RI1LP_0RN0RI_1RN1RI_1LT0RN_0LH0RI_1LH1RN_1LT0LH_0LD0LG_1LD1LG_1LD---_1LG---_0LP---_1LP---_0LH1LP_0LT---_0LC0LT_1LC1LT".
Definition tm1 := TM'_from_str "1LB0LE_1LC---_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG".
Definition tm2 := TM'_from_str "1LB0LE_1LC1RH_1LF1LD_1RA0LE_1RG1LC_1LE1LB_0RA0RG_1RH1RH".
Definition l0 := [1;0;0;1;1;1;1;0]%N.
Definition mp := mp_from_str "NSPWHDI".
Definition mp' := mp_from_str "NTPGHDI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM501.


Module TM502.
Definition tm := TM_from_str "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0LB_---0LD".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_0LP1RF_1RA1RB_1RJ0RA_0LP1RA_0LK0RF_1LK0RB_0RJ1LG_1RJ1LT_1RJ0LP_1LT1LP_0LK1LX_0RF1LG_0LG0LT_1LG1LT_---0LK_1LO0RF_0LX0LG_1LX1LG_---0LG_---0LT_---0LO_---1LO".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_0LP1RF_1RA1RB_1RJ0RA_0LP1RA_0LK0RF_1LK0RB_0RJ1LG_1RJ1LT_1RJ0LP_1LT1LP_0LK1LX_0RF1LG_0LG0LT_1LG1LT_---0RI_1LO1RI_0LX0RJ_1LX1LG_---0LG_---0LT_---0LO_---1LO".
Definition tm1 := TM'_from_str "0LB1RH_1LF1LC_1LD1LF_---1LE_0LF0LC_0LG0RA_1RJ0LB_0RA0RI_1RA1RI_1RJ1LC".
Definition tm2 := TM'_from_str "0LB1RH_1LF1LC_1LD1LF_1RK1LE_0LF0LC_0LG0RA_1RJ0LB_0RA0RI_1RA1RI_1RJ1LC_1RK1RK".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "FPTXOGKABJ".
Definition mp' := mp_from_str "FPTXOGKABJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM502.


Module TM503.
Definition tm := TM_from_str "1LB1LB_0RB1LC_1RD0LE_1LA1RE_1LF0RD_---1LD".
Definition tm' := TM_from_str "1LB1RC_0RB1LC_1RD0LE_1LA1RE_1LF0RD_---1LD".
Definition tm0 := TM'_from_str "1RR1RR_1LL1LL_0LH0LH_1LH1LH_0RE1RR_1RE1LS_0RE0LL_1RR1LL_0RN0LX_1RN1LH_1LH0LS_1RR1LS_1LH0RR_1LH1RR_0LD1LP_1LD1RM_---0RM_1LP1RM_0LX1LH_1LX0RR_---1LD_---1RM_---0LP_---1LP".
Definition tm0' := TM'_from_str "1RR0RJ_1LL1RJ_0LH1RN_1LH1LH_0RE1RR_1RE1LS_0RE0LL_1RR1LL_0RN0LX_1RN1LH_1LH0LS_1RR1LS_1LH0RR_1LH1RR_0LD1LP_1LD1RM_---0RM_1LP1RM_0LX1LH_1LX0RR_---1LD_---1RM_---0LP_---1LP".
Definition tm1 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_---1LE".
Definition tm2 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_1RI1LE_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "MHLRPDSX".
Definition mp' := mp_from_str "MHLRPDSX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM503.


Module TM504.
Definition tm := TM_from_str "1LB1RC_0RB1LC_1RD0LE_1LA1RE_1LF0RD_---1LD".
Definition tm' := TM_from_str "1LB1RF_1RC1LF_1LA1RD_1LE0RC_---1LC_1RC0LD".
Definition tm0 := TM'_from_str "1RR0RJ_1LL1RJ_0LH1RN_1LH1LH_0RE1RR_1RE1LS_0RE0LL_1RR1LL_0RN0LX_1RN1LH_1LH0LS_1RR1LS_1LH0RR_1LH1RR_0LD1LP_1LD1RM_---0RM_1LP1RM_0LX1LH_1LX0RR_---1LD_---1RM_---0LP_---1LP".
Definition tm0' := TM'_from_str "1RN0RV_1LX1RV_0LH1RJ_1LH1LH_0RJ1RN_1RJ1LO_1LH0LX_1RN1LX_1LH0RN_1LH1RN_0LD1LL_1LD1RI_---0RI_1LL1RI_0LT1LH_1LT0RN_---1LD_---1RI_---0LL_---1LL_0RJ0LT_1RJ1LH_1LH0LO_1RN1LO".
Definition tm1 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_---1LE".
Definition tm2 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_1RI1LE_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "MHLRPDSX".
Definition mp' := mp_from_str "IHXNLDOT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM504.


Module TM505.
Definition tm := TM_from_str "1LB1RF_1RC1LF_1LA1RD_1LE0RC_---1LC_1RC0LD".
Definition tm' := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_0RA0LD".
Definition tm0 := TM'_from_str "1RN0RV_1LX1RV_0LH1RJ_1LH1LH_0RJ1RN_1RJ1LO_1LH0LX_1RN1LX_1LH0RN_1LH1RN_0LD1LL_1LD1RI_---0RI_1LL1RI_0LT1LH_1LT0RN_---1LD_---1RI_---0LL_---1LL_0RJ0LT_1RJ1LH_1LH0LO_1RN1LO".
Definition tm0' := TM'_from_str "1RN1RN_1LX1LX_0LH0LH_1LH1LH_0RJ1RN_1RJ1LO_1LH0LX_1RN1LX_1LH0RN_1LH1RN_0LD1LL_1LD1RI_---0RI_1LL1RI_0LT1LH_1LT0RN_---1LD_---1RI_---0LL_---1LL_0RA0LT_1RA1LH_1RN0LO_1RN1LO".
Definition tm1 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_---1LE".
Definition tm2 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_1RI1LE_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "IHXNLDOT".
Definition mp' := mp_from_str "IHXNLDOT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM505.


Module TM506.
Definition tm := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_0RA0LD".
Definition tm' := TM_from_str "1LB1LB_1RC1LF_1LA1RD_1LE0RC_---1LC_1RC0LD".
Definition tm0 := TM'_from_str "1RN1RN_1LX1LX_0LH0LH_1LH1LH_0RJ1RN_1RJ1LO_1LH0LX_1RN1LX_1LH0RN_1LH1RN_0LD1LL_1LD1RI_---0RI_1LL1RI_0LT1LH_1LT0RN_---1LD_---1RI_---0LL_---1LL_0RA0LT_1RA1LH_1RN0LO_1RN1LO".
Definition tm0' := TM'_from_str "1RN1RN_1LX1LX_0LH0LH_1LH1LH_0RJ1RN_1RJ1LO_1LH0LX_1RN1LX_1LH0RN_1LH1RN_0LD1LL_1LD1RI_---0RI_1LL1RI_0LT1LH_1LT0RN_---1LD_---1RI_---0LL_---1LL_0RJ0LT_1RJ1LH_1LH0LO_1RN1LO".
Definition tm1 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_---1LE".
Definition tm2 := TM'_from_str "1LB0RD_1RD1LC_1RD1LG_1LE1RA_1LF1RA_1LB1LB_0LH1LB_1RI1LE_1RI1RI".
Definition l0 := [1;1;0;1;1;1;0;1]%N.
Definition mp := mp_from_str "IHXNLDOT".
Definition mp' := mp_from_str "IHXNLDOT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 36 36.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM506.


Module TM507.
Definition tm := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE0RF_1RB0LF_1RA1RD".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LA---".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LK---_1LH---_0RU1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RR_1RM0LK_0RR0LK_0RU1LK_0RR0RU_1RR1RU_1RF0RB_1RR0RN_0RF1RF_1RF1RR_1LK0LW_1LH1LW_0RB0RN_1RB1RN_1RF1RR_---1RU".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RF1RB_---1RQ_1LK---_1RF---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "RFKHLUNB".
Definition mp' := mp_from_str "BFKHLQNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM507.


Module TM508.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LA---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RB---".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RF1RB_---1RQ_1LK---_1RF---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RF1RB_---1RQ_0RF---_1RF---_1LK---_1LH---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "BFKHLQNV".
Definition mp' := mp_from_str "BFKHLQNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM508.


Module TM509.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RB---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RF1RB_---1RQ_0RF---_1RF---_1LK---_1LH---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RU_1RB0RN_0RU0RN_1RU1RN_1RF1RB_---1RQ_1RF---_0RU---_0LO---_1LO---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "BFKHLQNV".
Definition mp' := mp_from_str "BFKHLQNU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM509.


Module TM510.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RU_1RB0RN_0RU0RN_1RU1RN_1RF1RB_---1RQ_1RF---_0RU---_0LO---_1LO---".
Definition tm0' := TM'_from_str "0RF1RF_1RF1RB_1LK0LS_1LH1LS_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RU_1RB0RN_0RU0RN_1RU1RN_1RF1RB_---1RQ_1RF---_0RU---_0LO---_1LO---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RB1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "BFKHLQNU".
Definition mp' := mp_from_str "BFKHLQNU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM510.


Module TM511.
Definition tm := TM_from_str "1RB0LC_1RC1RF_1LA0LD_0LE0RA_0RF1LD_1RC---".
Definition tm' := TM_from_str "1RB0LC_1RC1RF_1LA0LD_0LE0RA_0RB1LD_1RC---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LO_1RJ0LK_1RV1LK_0RJ0RV_1RJ1RV_1LK1RJ_0RF---_1RV0LS_1LK0RF_0LD0LO_1LD1LO_0RJ0RA_0LP1RA_0LS0RF_1LS0LD_0RU1LS_1RU0LD_0RJ0LP_---1LP_0RJ---_1RJ---_1LK---_0RF---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LO_1RJ0LK_1RV1LK_0RJ0RV_1RJ1RV_1LK1RJ_0RF---_1RV0LS_1LK0RF_0LD0LO_1LD1LO_0RJ0RA_0LP1RA_0LS0RF_1LS0LD_0RE1LS_1RE0LD_0RJ0LP_0RV1LP_0RJ---_1RJ---_1LK---_0RF---".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LG0LD_0LE0RA_0RB0LF_1LE0LG_1RH1LC_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LG0LD_0LE0RA_0RB0LF_1LE0LG_1RH1LC_1RB1RI_1RI1RI".
Definition l0 := [0;1;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "FJKOSPDV".
Definition mp' := mp_from_str "FJKOSPDV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM511.


Module TM512.
Definition tm := TM_from_str "1RB0LC_1RC1RF_1LA0LD_0LE0RA_0RB1LD_1RC---".
Definition tm' := TM_from_str "1RB0LD_0LB1RC_1RD---_1LA0LE_0LF0RA_0RC1LE".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LO_1RJ0LK_1RV1LK_0RJ0RV_1RJ1RV_1LK1RJ_0RF---_1RV0LS_1LK0RF_0LD0LO_1LD1LO_0RJ0RA_0LP1RA_0LS0RF_1LS0LD_0RE1LS_1RE0LD_0RJ0LP_0RV1LP_0RJ---_1RJ---_1LK---_0RF---".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LS_1RN0LO_1RJ1LO_0LG0RJ_1RN1RJ_0LG1RN_1LG---_0RN---_1RN---_1LO---_0RF---_1RJ0LW_1LO0RF_0LD0LS_1LD1LS_0RN0RA_0LT1RA_0LW0RF_1LW0LD_0RI1LW_1RI0LD_0RN0LT_---1LT".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LG0LD_0LE0RA_0RB0LF_1LE0LG_1RH1LC_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LG0LD_0LE0RA_0RB0LF_1LE0LG_1RH1LC_1RB1RI_1RI1RI".
Definition l0 := [0;1;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "FJKOSPDV".
Definition mp' := mp_from_str "FNOSWTDJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM512.


Module TM513.
Definition tm := TM_from_str "1RB0LD_0LB1RC_1RD---_1LA0LE_0LF0RA_0RC1LE".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LS_1RN0LO_1RJ1LO_0LG0RJ_1RN1RJ_0LG1RN_1LG---_0RN---_1RN---_1LO---_0RF---_1RJ0LW_1LO0RF_0LD0LS_1LD1LS_0RN0RA_0LT1RA_0LW0RF_1LW0LD_0RI1LW_1RI0LD_0RN0LT_---1LT".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LO_1RJ0LK_1RU1LK_0RJ0RU_1RJ1RU_1LK1RJ_0RF---_1RU0LS_1LK0RF_0LD0LO_1LD1LO_0RJ0RA_0LP1RA_0LS0RF_1LS0LD_0RE1LS_1RE0LD_0RJ0LP_0RU1LP_1RJ---_0LK---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0LG0LD_0LE0RA_0RB0LF_1LE0LG_1RH1LC_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0LG0LD_0LE0RA_0RB0LF_1LE0LG_1RH1LC_1RB1RI_1RI1RI".
Definition l0 := [0;1;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "FNOSWTDJ".
Definition mp' := mp_from_str "FJKOSPDU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM513.


Module TM514.
Definition tm := TM_from_str "1LB1LD_0RC0RA_1LA1RC_1LA1RE_1LF0RD_---0LE".
Definition tm' := TM_from_str "1LB1LD_0RC1LA_1LA1RC_1LA1RE_1LF0RD_---0LE".
Definition tm0 := TM'_from_str "0RJ1LD_1LD1RM_0LH0LP_1LH1LP_0RI0RA_1RI1RA_1LH0RJ_0RJ1LD_1LH0RJ_1LP1RJ_0LD1LP_1LD1RJ_1LH0RR_1LP1RR_0LD1LS_1LD1RM_---0RM_1LS1RM_0LX1LH_1LX0RR_---0LX_---1LH_---0LS_---1LS".
Definition tm0' := TM'_from_str "0RJ1LD_1LD1RM_0LH0LP_1LH1LP_0RI1LH_1RI1LP_1LH0LD_0RJ1LD_1LH0RJ_1LP1RJ_0LD1LP_1LD1RJ_1LH0RR_1LP1RR_0LD1LS_1LD1RM_---0RM_1LS1RM_0LX1LH_1LX0RR_---0LX_---1LH_---0LS_---1LS".
Definition tm1 := TM'_from_str "1LB1RG_0LC1LD_---1LB_0RE1LH_1LF1RE_1LH1RG_1LD0RA_1LD1LF".
Definition tm2 := TM'_from_str "1LB1RG_0LC1LD_1RI1LB_0RE1LH_1LF1RE_1LH1RG_1LD0RA_1LD1LF_1RI1RI".
Definition l0 := [0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "RSXHJPMD".
Definition mp' := mp_from_str "RSXHJPMD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM514.


Module TM515.
Definition tm := TM_from_str "1LB---_0RC0LB_1LA1RD_1RE1RF_1RB0RF_1RE0RA".
Definition tm' := TM_from_str "1LB---_0RC0LB_1LA1RD_0LD1RE_1RF0RA_1RB0RE".
Definition tm0 := TM'_from_str "0RN---_1LG---_0LH---_1LH---_0RI1LH_1RI0LG_1LH0LG_0RN1LG_1LH0RN_---1RN_0LD1RR_1LD1RV_0RR0RV_1RR1RV_1RF1RR_1RU1RA_0RF0RU_1RF1RU_1RI0RR_0LG0RA_0RR0RA_1RR1RA_1RF0RN_1RU---".
Definition tm0' := TM'_from_str "0RN---_1LG---_0LH---_1LH---_0RI1LH_1RI0LG_1LH0LG_0RN1LG_1LH0RN_---1RN_0LD1RV_1LD1RR_0LO0RR_1RV1RR_0LO1RV_1LO1RA_0RV0RA_1RV1RA_1RF0RN_1RQ---_0RF0RQ_1RF1RQ_1RI0RV_0LG0RA".
Definition tm1 := TM'_from_str "0RB---_1RC1RH_1RD1RI_1RE0LG_1LF0RB_0RB1LG_1LF0LG_1RC1RA_0RC0RA".
Definition tm2 := TM'_from_str "0RB1RJ_1RC1RH_1RD1RI_1RE0LG_1LF0RB_0RB1LG_1LF0LG_1RC1RA_0RC0RA_1RJ1RJ".
Definition l0 := [0;1;1;1;1;0;1;1]%N.
Definition mp := mp_from_str "ANRFIHGVU".
Definition mp' := mp_from_str "ANVFIHGRQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM515.


Module TM516.
Definition tm := TM_from_str "1LB1RB_1LC0RB_1RA0LD_---0LE_0LF0RC_1RA1LB".
Definition tm' := TM_from_str "1LB1RB_1LC0RB_1RA0LD_---0LE_0LF0RF_1RA1LB".
Definition tm0 := TM'_from_str "1LL0RF_0RE1RF_0LH1LO_1LH1RE_1RF0RE_1LO1RE_0LL1RF_1LL0RE_0RB---_1RB0LS_0RE0LO_1RF1LO_---0LW_---0RB_---0LS_---1LS_0RE0RI_0LH1RI_0LW0RB_1LW---_0RB1LL_1RB0RE_0RE0LH_1RF1LH".
Definition tm0' := TM'_from_str "1LL0RF_0RE1RF_0LH1LO_1LH1RE_1RF0RE_1LO1RE_0LL1RF_1LL0RE_0RB---_1RB0LS_0RE0LO_1RF1LO_---0LW_---0RB_---0LS_---1LS_0RE0RU_0LH1RU_0LW0RB_1LW1LL_0RB1LL_1RB0RE_0RE0LH_1RF1LH".
Definition tm1 := TM'_from_str "1RB0RA_1LC1RA_---0LD_0LE0RH_0RA0LF_1LG0RA_1RB1LC_0RA1RB".
Definition tm2 := TM'_from_str "1RB0RA_1LC1RA_1RI0LD_0LE0RH_0RA0LF_1LG0RA_1RB1LC_0RA1RB_1RI1RI".
Definition l0 := [1;0;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "EFOSWHLB".
Definition mp' := mp_from_str "EFOSWHLB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM516.


Module TM517.
Definition tm := TM_from_str "1LB0RA_0LC1LD_0RD1LE_1RA0LB_0LD1LF_0LC---".
Definition tm' := TM_from_str "1LB0RA_0LC1LD_0RD1LE_1RA0LB_0LD0LF_0RA---".
Definition tm0 := TM'_from_str "1LK0RA_1LP1RA_0LH1LK_1LH0RA_0RB1RA_0LT1LG_0LK0LP_1LK1LP_0RM1LO_1RM1LX_0RB0LT_0LK1LT_0RB0LK_1RB0LP_1LP0LG_1RA1LG_1LP1LK_0LG---_0LO0LX_1LO1LX_0RB---_0LT---_0LK---_1LK---".
Definition tm0' := TM'_from_str "1LK0RA_1LP1RA_0LH1LK_1LH0RA_0RB1RA_0LT1LG_0LK0LP_1LK1LP_0RM1LO_1RM1LW_0RB0LT_0LK1LT_0RB0LK_1RB0LP_1LP0LG_1RA1LG_1LP1LK_0LG---_0LO0LW_1LO1LW_0RA---_1RA---_1LK---_0RA---".
Definition tm1 := TM'_from_str "1LB0RA_0RG0LC_1LD1LH_1LF0LE_0LB0LF_1RA1LE_1LF1RA_1LB---".
Definition tm2 := TM'_from_str "1LB0RA_0RG0LC_1LD1LH_1LF0LE_0LB0LF_1RA1LE_1LF1RA_1LB1RI_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "AKTOGPBX".
Definition mp' := mp_from_str "AKTOGPBW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM517.


Module TM518.
Definition tm := TM_from_str "1RB1RA_1LC1RA_0LD0LC_0RE1RB_1RD0RF_0RB---".
Definition tm' := TM_from_str "1RB1LD_1LC1RA_0LD0LC_0RE1RB_1RD0RF_0RB---".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1RB1RB_1LO0RB_1LK1RB_0LL1RF_1LL1RB_0RN0LO_1LK0LK_0LO0LK_1LO1LK_0RQ0RF_1RQ1RF_0RN1LK_0RU1RB_0RN0RU_1RN1RU_1RQ0RE_1RF---_0RE---_1RE---_1LO---_0RB---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RB_1LK0LP_1RB1LP_1LO0RB_1LK1RB_0LL1RF_1LL1RB_0RN0LO_1LK0LK_0LO0LK_1LO1LK_0RQ0RF_1RQ1RF_0RN1LK_0RU1RB_0RN0RU_1RN1RU_1RQ0RE_1RF---_0RE---_1RE---_1LO---_0RB---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1RA_0LD0LC_0RE1LC_1RF1RB_0RE0RG_0RH---_1LD0RA".
Definition tm2 := TM'_from_str "1RB1RA_1LC1RA_0LD0LC_0RE1LC_1RF1RB_0RE0RG_0RH1RI_1LD0RA_1RI1RI".
Definition l0 := [0;1;0;0;1;0;1;1]%N.
Definition mp := mp_from_str "BFKONQUE".
Definition mp' := mp_from_str "BFKONQUE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 38 38.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM518.


Module TM519.
Definition tm := TM_from_str "1RB1RD_0LC0LA_0RA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm' := TM_from_str "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_0LL1RB_1RB1LO_0RF0LL_0LL1RB_0LK0LC_1LK1LC_0RA0RN_1RA1LL_0RF0LL_0RN1LL_0RB1RQ_1RB1LO_1RF0LT_1RN1LT_0RV1RF_1RV0LT_---0LO_1RQ1LO_---0RQ_---1RQ_---0RV_---1RF".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_0LL1RB_1RB1LO_0RF0RB_0LL1RB_0LK1RF_1LK1RN_0RA0RN_1RA1LL_0RF0LL_0RN1LL_0RB1RQ_1RB1LO_1RF0LT_1RN1LT_0RV1RF_1RV0LT_---0LO_1RQ1LO_---0RQ_---1RQ_---0RV_---1RF".
Definition tm1 := TM'_from_str "0LB1RE_0RC1LB_1RE1LD_1RA0LF_1RA1RC_1RG1LD_0RH1RA_---1RG".
Definition tm2 := TM'_from_str "0LB1RE_0RC1LB_1RE1LD_1RA0LF_1RA1RC_1RG1LD_0RH1RA_1RI1RG_1RI1RI".
Definition l0 := [1;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "FLNOBTQV".
Definition mp' := mp_from_str "FLNOBTQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 38 38.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM519.


Module TM520.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LC---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LC---".
Definition tm0 := TM'_from_str "0RF0LK_1RF1RB_1LK0LS_1LH1LS_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_0LK1RB_---1RQ_0RB---_0LK---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_0LK1RB_---1RQ_0RB---_0LK---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_0LC---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_0LC1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "BFKHLQNV".
Definition mp' := mp_from_str "BFKHLQNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 39 39.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM520.


Module TM521.
Definition tm := TM_from_str "1LB1RA_0RB1RC_1LD0RD_0RA0LE_1LC0LF_1RE---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LF_0RC1RE_0RC---".
Definition tm0 := TM'_from_str "0RJ0RB_1RM1RB_0LH1RM_1LH1RB_0RE0RJ_1RE1RJ_0RE1LS_0RJ1RM_0RB0RM_1LS1RM_0LP0RA_1LP0LL_0RA0LL_1RA0LW_0RJ0LS_0RB1LS_1LP0LL_0LL---_0LL0LW_1LL1LW_0RR---_1RR---_0LL---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1LO1RI_1RI1RR_0RR0RI_1LO1RI_0LL0RA_1LL0LH_0RA0LH_1RA0LX_0RF0LO_0RR1LO_1LL0LH_0LH---_0LH0LX_1LH1LX_0RI0RR_1RI1RR_0RA1RI_0LH1RR_0RI---_1RI---_0RA---_0LH---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC---_1RG1RF_0RH0LC_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC1RI_1RG1RF_0RH0LC_0RA0RF_1RI1RI".
Definition l0 := [0;1;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "JSLPWBMA".
Definition mp' := mp_from_str "FOHLXRIA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 39 39.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM521.


Module TM522.
Definition tm := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LF_0RC1RE_0RC---".
Definition tm' := TM_from_str "1LB1RA_0RB1RC_1LD0RD_0RA0LE_1LC1LF_0RD---".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1LO1RI_1RI1RR_0RR0RI_1LO1RI_0LL0RA_1LL0LH_0RA0LH_1RA0LX_0RF0LO_0RR1LO_1LL0LH_0LH---_0LH0LX_1LH1LX_0RI0RR_1RI1RR_0RA1RI_0LH1RR_0RI---_1RI---_0RA---_0LH---".
Definition tm0' := TM'_from_str "0RJ0RB_1RM1RB_0LH1RM_1LH1RB_0RE0RJ_1RE1RJ_0RE1LS_0RJ1RM_0RB0RM_1LS1RM_0LP0RA_1LP0LL_0RA0LL_1RA0LX_0RJ0LS_0RB1LS_1LP0LL_0LL---_0LL0LX_1LL1LX_0RM---_1RM---_0RA---_0LL---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC---_1RG1RF_0RH0LC_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC1RI_1RG1RF_0RH0LC_0RA0RF_1RI1RI".
Definition l0 := [0;1;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "FOHLXRIA".
Definition mp' := mp_from_str "JSLPXBMA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 39 39.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM522.


Module TM523.
Definition tm := TM_from_str "1LB1RC_1LC---_0RD1LF_0RE1LD_0RA1RE_0LC0LB".
Definition tm' := TM_from_str "1LB1RC_1LC---_0RD1LF_0RE1RE_0RA1RE_0LC0LB".
Definition tm0 := TM'_from_str "1LL0RJ_---1RJ_0LH1RM_1LH1LG_0RR---_1LX---_0LL---_1LL---_0RM1LK_1RM1LG_0RQ0LX_0RR1LX_0RQ0RR_1RQ1LP_0RA0LP_0RR1LP_0RA0RR_1RA1RR_1LL1RA_0RJ1RR_0RQ0LL_0LX---_0LK0LG_1LK1LG".
Definition tm0' := TM'_from_str "1LL0RJ_---1RJ_0LH1RM_1LH1LG_0RR---_1LX---_0LL---_1LL---_0RM1LK_1RM1LG_0RQ0LX_0RR1LX_0RQ0RR_1RQ1RR_0RA1RA_0RR1RR_0RA0RR_1RA1RR_1LL1RA_0RJ1RR_0RQ0LL_0LX---_0LK0LG_1LK1LG".
Definition tm1 := TM'_from_str "1LB0RG_0RF1LC_1LD1LE_0RI0LC_0LB---_1RA1RF_1RH1LE_0RI0RF_0RA0RF".
Definition tm2 := TM'_from_str "1LB0RG_0RF1LC_1LD1LE_0RI0LC_0LB1RJ_1RA1RF_1RH1LE_0RI0RF_0RA0RF_1RJ1RJ".
Definition l0 := [0;0;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "ALXKGRJMQ".
Definition mp' := mp_from_str "ALXKGRJMQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 40 40.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM523.


Module TM524.
Definition tm := TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RA".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LD_0RE1LA_---0RA".
Definition tm0 := TM'_from_str "0RF0LT_1RF0LO_1RJ0LO_1RE1LO_0RJ0RE_1RJ1RE_1RN0RJ_1RV0RE_0RN0RV_1RN1RV_1LD---_0LO1RA_1RE0LT_1LD0LO_0LT0LO_1LT1LO_0RF1RE_1RF1LO_1RJ0LD_1RE1LD_---0RA_---1RA_---0RF_---0LT".
Definition tm0' := TM'_from_str "0RF0LT_1RF0LO_1RJ0LO_1RE1LO_0RJ0RE_1RJ1RE_1RN0RJ_1RV0RE_0RN0RV_1RN1RV_1LD---_0LO1RA_1RE0LT_1LD0LO_0LT0LO_1LT1LO_0RQ1RE_1RQ1LO_0RQ0LD_1RE1LD_---0RA_---1RA_---0RF_---0LT".
Definition tm1 := TM'_from_str "1RB1RG_1LC0LD_1RF1LD_0LE0LD_1RF1LC_0RA0RF_---1RH_0RI0LE_1RA1RF".
Definition tm2 := TM'_from_str "1RB1RG_1LC0LD_1RF1LD_0LE0LD_1RF1LC_0RA0RF_1RJ1RH_0RI0LE_1RA1RF_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "JNDOTEVAF".
Definition mp' := mp_from_str "JNDOTEVAF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 40 40.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM524.


Module TM525.
Definition tm := TM_from_str "1LB0LC_1RC0LE_1LE0RD_1RA1RB_0RF1LA_1RB---".
Definition tm' := TM_from_str "1LB0LC_1RC0LE_1LE0RD_1RA0LE_0RF1LA_1RB---".
Definition tm0 := TM'_from_str "1RM0LT_1LS0RB_0LH0LK_1LH1LK_0RJ0RF_1RJ0LD_1LD0LS_1RM1LS_---0RM_1LD1RM_0LT0RB_1LT0RF_0RB0RF_1RB1RF_1LS1RJ_0RB0LD_0RU1LH_1RU1LK_0RF0LD_---1LD_0RF---_1RF---_1RJ---_0LD---".
Definition tm0' := TM'_from_str "1RM0LT_1LS0RB_0LH0LK_1LH1LK_0RJ0RF_1RJ0LD_1LD0LS_1RM1LS_---0RM_1LD1RM_0LT0RB_1LT0RF_0RB0RF_1RB0LD_1LS0LS_0RB1LS_0RU1LH_1RU1LK_0RF0LD_---1LD_0RF---_1RF---_1RJ---_0LD---".
Definition tm1 := TM'_from_str "1LB1RH_1LE1LC_0LD0RI_---1LB_1RH1LF_0RG0LB_1RA0LB_0RI0RG_1LF0RI".
Definition tm2 := TM'_from_str "1LB1RH_1LE1LC_0LD0RI_1RJ1LB_1RH1LF_0RG0LB_1RA0LB_0RI0RG_1LF0RI_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "JDKTHSFMB".
Definition mp' := mp_from_str "JDKTHSFMB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 40 40.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM525.


Module TM526.
Definition tm := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB1LE_---1LE".
Definition tm' := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB0LC_---0LC".
Definition tm0 := TM'_from_str "0RN---_1LD0LT_0LH0LW_1LH1LW_0RI1LH_1RI1LW_0RM0LD_0RN1LD_0RM0RN_1RM1RN_1LG1LT_0RJ1RJ_1LG0RJ_1LT1RJ_0LT1RM_1LT1RN_0RM1LG_0LD1LT_0LG0LT_1LG1LT_---1LG_---1LT_---0LT_---1LT".
Definition tm0' := TM'_from_str "0RN---_1LD0LK_0LH0LW_1LH1LW_0RI1LH_1RI1LW_0RM0LD_0RN1LD_0RM0RN_1RM1RN_1LG1LK_0RJ1RJ_1LG0RJ_1LK1RJ_0LT1RM_1LT1RN_0RM1LG_0LD1LK_0LG0LK_1LG1LK_---1LG_---1LK_---0LK_---1LK".
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_0RB0LD_1LE1LF_0RH1LD_---0LG_1LC1LG_1LG1RA".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_0RB0LD_1LE1LF_0RH1LD_1RI0LG_1LC1LG_1LG1RA_1RI1RI".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "JMGDHWTN".
Definition mp' := mp_from_str "JMGDHWKN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 41 41.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM526.


Module TM527.
Definition tm := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB1LE_---0LC".
Definition tm' := TM_from_str "1LB0LF_0RC1LA_0RD1RD_1LE1RC_0LB0LC_---1LE".
Definition tm0 := TM'_from_str "0RN---_1LD0LK_0LH0LW_1LH1LW_0RI1LH_1RI1LW_0RM0LD_0RN1LD_0RM0RN_1RM1RN_1LG1LT_0RJ1RJ_1LG0RJ_1LT1RJ_0LT1RM_1LT1RN_0RM1LG_0LD1LT_0LG0LT_1LG1LT_---1LG_---1LT_---0LK_---1LK".
Definition tm0' := TM'_from_str "0RN---_1LD0LT_0LH0LW_1LH1LW_0RI1LH_1RI1LW_0RM0LD_0RN1LD_0RM0RN_1RM1RN_1LG1LK_0RJ1RJ_1LG0RJ_1LK1RJ_0LT1RM_1LT1RN_0RM1LG_0LD1LK_0LG0LK_1LG1LK_---1LG_---1LK_---0LT_---1LT".
Definition tm1 := TM'_from_str "1RB1RI_1LC0RA_0RB0LD_1LE1LF_0RI1LD_---0LG_1LC1LH_1LC1LH_1LH1RA".
Definition tm2 := TM'_from_str "1RB1RI_1LC0RA_0RB0LD_1LE1LF_0RI1LD_1RJ0LG_1LC1LH_1LC1LH_1LH1RA_1RJ1RJ".
Definition l0 := [0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "JMGDHWKTN".
Definition mp' := mp_from_str "JMGDHWTKN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 41 41.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM527.


Module TM528.
Definition tm := TM_from_str "1RB0RB_0LC0RA_1LD1LC_0LE0LF_1RF1LC_0RB---".
Definition tm' := TM_from_str "1RB0RB_0LC0RA_1LD1LC_0LE0LF_1RF1RB_0RB---".
Definition tm0 := TM'_from_str "0RF0RE_1RF1RE_0LL0LP_1RA0RA_0LP0RA_0LL1RA_0LK0RF_1LK0RE_1LS1LP_1LW1LL_0LP0LL_1LP1LL_1RE0LP_0LL---_0LS0LW_1LS1LW_0RV1LP_1RV1LL_1RE0LL_---1LL_0RE---_1RE---_0LP---_0RA---".
Definition tm0' := TM'_from_str "0RF0RE_1RF1RE_0LL0LP_1RA0RA_0LP0RA_0LL1RA_0LK0RF_1LK0RE_1LS1LP_1LW1LL_0LP0LL_1LP1LL_1RE0LP_0LL---_0LS0LW_1LS1LW_0RV0RF_1RV1RF_1RE0LL_---1RA_0RE---_1RE---_0LP---_0RA---".
Definition tm1 := TM'_from_str "0LB1RG_1LC1LB_1LE1LD_0LC---_1RF0LB_0LC0RG_0RA0RF".
Definition tm2 := TM'_from_str "0LB1RG_1LC1LB_1LE1LD_0LC1RH_1RF0LB_0LC0RG_0RA0RF_1RH1RH".
Definition l0 := [1;0;1;1;0;0;1;0]%N.
Definition mp := mp_from_str "FLPWSEA".
Definition mp' := mp_from_str "FLPWSEA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 41 41.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM528.


Module TM529.
Definition tm := TM_from_str "1RB---_1LC0LE_1RD0LB_0LD1RA_0LF0RC_0RA1LE".
Definition tm' := TM_from_str "1RB---_1LC0LE_1RD0LB_1RB1RA_0LF0RC_0RA1LE".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LG---_0RN---_1RB0LW_1LG0RN_0LL0LS_1LL1LS_0RN0LL_1RN0LS_1RF0LG_1RB1LG_0LO0RB_1RF1RB_0LO1RF_1LO---_0RF0RI_0LT1RI_0LW0RN_1LW0LL_0RA1LW_1RA0LL_0RF0LT_---1LT".
Definition tm0' := TM'_from_str "0RF---_1RF---_1LG---_0RN---_1RB0LW_1LG0RN_0LL0LS_1LL1LS_0RN0LL_1RN0LS_1RF0LG_1RB1LG_0RF0RB_1RF1RB_1LG1RF_0RN---_0RF0RI_0LT1RI_0LW0RN_1LW0LL_0RA1LW_1RA0LL_0RF0LT_---1LT".
Definition tm1 := TM'_from_str "1RB---_1LC0RE_0LH0LD_0LF0RE_1RB1RA_0RB0LG_1LF0LH_1RA1LC".
Definition tm2 := TM'_from_str "1RB1RI_1LC0RE_0LH0LD_0LF0RE_1RB1RA_0RB0LG_1LF0LH_1RA1LC_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFGSNWTL".
Definition mp' := mp_from_str "BFGSNWTL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 42 42.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM529.


Module TM530.
Definition tm := TM_from_str "1RB---_1LC0LE_1RD0LB_1RB1RA_0LF0RC_0RA1LE".
Definition tm' := TM_from_str "1RB0RD_1LC0LE_1RA0LB_0LC---_0LF0RC_0RA1LE".
Definition tm0 := TM'_from_str "0RF---_1RF---_1LG---_0RN---_1RB0LW_1LG0RN_0LL0LS_1LL1LS_0RN0LL_1RN0LS_1RF0LG_1RB1LG_0RF0RB_1RF1RB_1LG1RF_0RN---_0RF0RI_0LT1RI_0LW0RN_1LW0LL_0RA1LW_1RA0LL_0RF0LT_---1LT".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1LG1RF_0RB---_1RM0LW_1LG0RB_0LL0LS_1LL1LS_0RB0LL_1RB0LS_1RF0LG_1RM1LG_1RF---_0LG---_0LK---_1LK---_0RF0RI_0LT1RI_0LW0RB_1LW0LL_0RA1LW_1RA0LL_0RF0LT_0RM1LT".
Definition tm1 := TM'_from_str "1RB---_1LC0RE_0LH0LD_0LF0RE_1RB1RA_0RB0LG_1LF0LH_1RA1LC".
Definition tm2 := TM'_from_str "1RB1RI_1LC0RE_0LH0LD_0LF0RE_1RB1RA_0RB0LG_1LF0LH_1RA1LC_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "BFGSNWTL".
Definition mp' := mp_from_str "MFGSBWTL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 42 42.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM530.


Module TM531.
Definition tm := TM_from_str "1RB0RD_1LC0LE_1RA0LB_0LC---_0LF0RC_0RA1LE".
Definition tm' := TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE".
Definition tm0 := TM'_from_str "0RF0RM_1RF1RM_1LG1RF_0RB---_1RM0LW_1LG0RB_0LL0LS_1LL1LS_0RB0LL_1RB0LS_1RF0LG_1RM1LG_1RF---_0LG---_0LK---_1LK---_0RF0RI_0LT1RI_0LW0RB_1LW0LL_0RA1LW_1RA0LL_0RF0LT_0RM1LT".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LG1RF_0RB---_1RN0LW_1LG0RB_0LL0LS_1LL1LS_0RB0LL_1RB0LS_1RF0LG_1RN1LG_0RF---_1RF---_1LG---_0RB---_0RF0RI_0LT1RI_0LW0RB_1LW0LL_0RA1LW_1RA0LL_0RF0LT_0RN1LT".
Definition tm1 := TM'_from_str "1RB---_1LC0RE_0LH0LD_0LF0RE_1RB1RA_0RB0LG_1LF0LH_1RA1LC".
Definition tm2 := TM'_from_str "1RB1RI_1LC0RE_0LH0LD_0LF0RE_1RB1RA_0RB0LG_1LF0LH_1RA1LC_1RI1RI".
Definition l0 := [1;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "MFGSBWTL".
Definition mp' := mp_from_str "NFGSBWTL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 42 42.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM531.


Module TM532.
Definition tm := TM_from_str "1LB0LF_1RC0LC_0LE0RD_1RC1RB_0RD1LA_1LB---".
Definition tm' := TM_from_str "1LB---_1RC0LC_0LE0RD_1RC1RB_0RB1LF_1LB0LA".
Definition tm0 := TM'_from_str "1RM0LH_1LK---_0LH0LW_1LH1LW_0RJ0LS_1RJ0RJ_0LD0LK_1RM1LK_0RJ0RM_0LD1RM_0LS0RJ_1LS0RF_0RJ0RF_1RJ1RF_0LD1RJ_1RM0RJ_0RM1LH_1RM1LW_0RJ0LD_0RF1LD_1RM---_1LK---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM---_1LK---_0LH---_1LH---_0RJ0LS_1RJ0RJ_0LX0LK_1RM1LK_0RJ0RM_0LX1RM_0LS0RJ_1LS0RF_0RJ0RF_1RJ1RF_0LX1RJ_1RM0RJ_0RE1LH_1RE1LC_0RJ0LX_0LS1LX_1RM0LH_1LK---_0LH0LC_1LH1LC".
Definition tm1 := TM'_from_str "0LB1RG_1LD1LC_0LD---_1RG1LE_0LF0RA_0RA0LB_0RA0RH_1RA0RA".
Definition tm2 := TM'_from_str "0LB1RG_1LD1LC_0LD1RI_1RG1LE_0LF0RA_0RA0LB_0RA0RH_1RA0RA_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JDWHKSMF".
Definition mp' := mp_from_str "JXCHKSMF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 45 45.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM532.


Module TM533.
Definition tm := TM_from_str "1LB---_1RC0LC_0LE0RD_1RC1RB_0RB1LF_1LB0LA".
Definition tm' := TM_from_str "1LB---_1RC0LC_0LE0RD_0LE1RB_0RB1LF_1LB0LA".
Definition tm0 := TM'_from_str "1RM---_1LK---_0LH---_1LH---_0RJ0LS_1RJ0RJ_0LX0LK_1RM1LK_0RJ0RM_0LX1RM_0LS0RJ_1LS0RF_0RJ0RF_1RJ1RF_0LX1RJ_1RM0RJ_0RE1LH_1RE1LC_0RJ0LX_0LS1LX_1RM0LH_1LK---_0LH0LC_1LH1LC".
Definition tm0' := TM'_from_str "1RM---_1LK---_0LH---_1LH---_0RJ0LS_1RJ0RJ_0LX0LK_1RM1LK_0RJ0RM_0LX1RM_0LS0RJ_1LS0RF_0RJ0RF_0LX1RF_0LS1RJ_1LS0RJ_0RE1LH_1RE1LC_0RJ0LX_0LS1LX_1RM0LH_1LK---_0LH0LC_1LH1LC".
Definition tm1 := TM'_from_str "0LB1RG_1LD1LC_0LD---_1RG1LE_0LF0RA_0RA0LB_0RA0RH_1RA0RA".
Definition tm2 := TM'_from_str "0LB1RG_1LD1LC_0LD1RI_1RG1LE_0LF0RA_0RA0LB_0RA0RH_1RA0RA_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JXCHKSMF".
Definition mp' := mp_from_str "JXCHKSMF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 45 45.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM533.


Module TM534.
Definition tm := TM_from_str "1LB0LF_1RC0LC_0LE0RD_1RC1RD_0RD1LA_1LB---".
Definition tm' := TM_from_str "1LB0LF_1RC0LC_0LE0RD_1RC1RD_0RB1LA_1LB---".
Definition tm0 := TM'_from_str "1RM0LH_1LK---_0LH0LW_1LH1LW_0RJ0LS_1RJ0RJ_0LD0LK_1RM1LK_0RJ0RM_0LD1RM_0LS0RJ_1LS0RN_0RJ0RN_1RJ1RN_0LD1RJ_1RM1RN_0RM1LH_1RM1LW_0RJ0LD_0RN1LD_1RM---_1LK---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM0LH_1LK---_0LH0LW_1LH1LW_0RJ0LS_1RJ0RJ_0LD0LK_1RM1LK_0RJ0RM_0LD1RM_0LS0RJ_1LS0RN_0RJ0RN_1RJ1RN_0LD1RJ_1RM1RN_0RE1LH_1RE1LW_0RJ0LD_0LS1LD_1RM---_1LK---_0LH---_1LH---".
Definition tm1 := TM'_from_str "0LB1RG_1LD1LC_0LD---_1RG1LE_0LF0RA_0RA0LB_0RA0RH_1RA1RH".
Definition tm2 := TM'_from_str "0LB1RG_1LD1LC_0LD1RI_1RG1LE_0LF0RA_0RA0LB_0RA0RH_1RA1RH_1RI1RI".
Definition l0 := [0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "JDWHKSMN".
Definition mp' := mp_from_str "JDWHKSMN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 45 45.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM534.


Module TM535.
Definition tm := TM_from_str "1RB0LF_1LC0LE_1RD1LB_0RA1RD_---1RD_1LA0LD".
Definition tm' := TM_from_str "1RB0LF_1LC1LE_1RD1LB_0RA1RD_---1RF_1LA0LD".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LO_1LH0LW_1RA1LW_1RN---_1LH1RA_0LL0LS_1LL1LS_0RN1LL_1RN1LS_1RA0LH_1RN1LH_0RA0RN_1RA1RN_0RF1RA_0LD1RN_---0RN_---1RN_---1RA_---1RN_1RA0RF_1LW1RA_0LD0LO_1LD1LO".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LO_1LH0LW_1RA1LW_1RN---_1LH1RA_0LL0LT_1LL1LT_0RN1LL_1RN1LT_1RA0LH_1RN1LH_0RA0RN_1RA1RN_0RF1RA_0LD1RN_---0RV_---1RV_---1LW_---1RA_1RA0RF_1LW1RA_0LD0LO_1LD1LO".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LF_1RD1LB_1RE1RD_0RA0LG_---1RE_1RE1LH_0LG0LI_0RA1RE".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LF_1RD1LB_1RE1RD_0RA0LG_1RJ1RE_1RE1LH_0LG0LI_0RA1RE_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "FHLNASDWO".
Definition mp' := mp_from_str "FHLNATDWO".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 47 47.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM535.


Module TM536.
Definition tm := TM_from_str "1RB0LF_1LC1LE_1RD1LB_0RA1RD_---1RF_1LA0LD".
Definition tm' := TM_from_str "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE".
Definition tm0 := TM'_from_str "0RF0LD_1RF0LO_1LH0LW_1RA1LW_1RN---_1LH1RA_0LL0LT_1LL1LT_0RN1LL_1RN1LT_1RA0LH_1RN1LH_0RA0RN_1RA1RN_0RF1RA_0LD1RN_---0RV_---1RV_---1LW_---1RA_1RA0RF_1LW1RA_0LD0LO_1LD1LO".
Definition tm0' := TM'_from_str "0RF0LD_1RF0LS_1LH0LW_1RA1LW_1RR---_1LH1RA_0LL0LO_1LL1LO_0RN1LL_1RN1LO_---0LH_1RR1LH_---0RR_---1RR_---1RA_---1RR_0RA0RR_1RA1RR_0RF1RA_0LD1RR_1RA0RF_1LW1RA_0LD0LS_1LD1LS".
Definition tm1 := TM'_from_str "1LB1RE_1LC1LF_1RD1LB_1RE1RD_0RA0LG_---1RE_1RE1LH_0LG0LI_0RA1RE".
Definition tm2 := TM'_from_str "1LB1RE_1LC1LF_1RD1LB_1RE1RD_0RA0LG_1RJ1RE_1RE1LH_0LG0LI_0RA1RE_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "FHLNATDWO".
Definition mp' := mp_from_str "FHLRAODWS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 47 47.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM536.


Module TM537.
Definition tm := TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB---".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LC1RD_0RF0LA_0RD1LE_1LA---".
Definition tm0 := TM'_from_str "0RF0RV_1RF0LT_1RI0LS_1RF1LS_0RI0RF_1RI1RF_1LL1RI_0RN1RF_1LL0RN_0LS1RN_0LL1RV_1LL0LS_0RV1RI_1RV0LS_1RF0LC_---1LC_0RM1RI_1RM1LT_0RV0LT_1RI1LT_0RN---_1RF---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RU_1RF0LT_1RI0LS_1RF1LS_0RI0RF_1RI1RF_1LL1RI_0RN1RF_1LL0RN_0LS1RN_0LL1RU_1LL0LS_0RU1RI_1RU0LS_1RF0LC_---1LC_0RM1RI_1RM1LT_0RU0LT_1RI1LT_1RF---_1LS---_0LD---_1LD---".
Definition tm1 := TM'_from_str "1RB1RA_1LC0RF_1LC0LD_0RG0LE_1RB1LE_1RG0LD_1RA---".
Definition tm2 := TM'_from_str "1RB1RA_1LC0RF_1LC0LD_0RG0LE_1RB1LE_1RG0LD_1RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "FILSTNV".
Definition mp' := mp_from_str "FILSTNU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 47 47.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM537.


Module TM538.
Definition tm := TM_from_str "1RB0LE_0RC1RB_1LC1RD_0RF0LA_0RD1LE_1LA---".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB---".
Definition tm0 := TM'_from_str "0RF0RU_1RF0LT_1RI0LS_1RF1LS_0RI0RF_1RI1RF_1LL1RI_0RN1RF_1LL0RN_0LS1RN_0LL1RU_1LL0LS_0RU1RI_1RU0LS_1RF0LC_---1LC_0RM1RI_1RM1LT_0RU0LT_1RI1LT_1RF---_1LS---_0LD---_1LD---".
Definition tm0' := TM'_from_str "0RF0RV_1RF0LT_1RI0LS_1RF1LS_0RI0RF_1RI1RF_1LL1RI_0RN1RF_1LL0RN_0LS1RN_0LL1RV_1LL0LS_0RV1RI_1RV0LS_1RF0LC_---1LC_0RM1RI_1RM1LT_0RV0LT_1RI1LT_0RF---_1RF---_1RI---_1RF---".
Definition tm1 := TM'_from_str "1RB1RA_1LC0RF_1LC0LD_0RG0LE_1RB1LE_1RG0LD_1RA---".
Definition tm2 := TM'_from_str "1RB1RA_1LC0RF_1LC0LD_0RG0LE_1RB1LE_1RG0LD_1RA1RH_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "FILSTNU".
Definition mp' := mp_from_str "FILSTNV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 47 47.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM538.


Module TM539.
Definition tm := TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF0RB_---0LA".
Definition tm' := TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RA_1RF0RB_---1LB".
Definition tm0 := TM'_from_str "0RF0RE_1RF1RE_1LK1LH_0LL1RR_1LH1RR_1LK0LL_0LH0LK_1LH1LK_0RN1RA_1RN1LL_1RR0LL_1RA1LL_0RR0RA_1RR1RA_1RU0RF_1RE0RE_0RU0RE_1RU1RE_---1LH_1LK1RR_---1LK_---1LH_---0LC_---1LC".
Definition tm0' := TM'_from_str "0RF0RE_1RF1RE_1LK1LH_0LL1RR_1LH1RR_1LK0LL_0LH0LK_1LH1LK_0RN1RA_1RN1LL_1RR0LL_1RA1LL_0RR0RA_1RR1RA_1RV0RF_1RE0RE_0RV0RE_1RV1RE_---1LH_1LK1RR_---1LH_---1LK_---0LH_---1LH".
Definition tm1 := TM'_from_str "1LB1RF_1LB1LC_1RF0LD_1RE1LD_0RH0RA_1RG1RA_---1LC_1LC0LD".
Definition tm2 := TM'_from_str "1LB1RF_1LB1LC_1RF0LD_1RE1LD_0RH0RA_1RG1RA_1RI1LC_1LC0LD_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "EHKLARUF".
Definition mp' := mp_from_str "EHKLARVF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 48 48.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM539.


Module TM540.
Definition tm := TM_from_str "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LD---_0RC1LA".
Definition tm' := TM_from_str "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA".
Definition tm0 := TM'_from_str "0RF0RN_1RF0LD_1RJ0LW_0LG1LW_0RJ1RN_1RJ0LG_1RN0LG_1RF1LG_0RN0RF_1RN1RF_1RR1RJ_1RV0LG_0RR0RV_1RR1RV_1LW1RI_---1LW_------_1LW---_0LP---_1LP---_0RI0LG_1RI1LW_0RN0LD_0RF1LD".
Definition tm0' := TM'_from_str "0RF0RN_1RF0LD_1RJ0LW_0LG1LW_0RJ1RN_1RJ0LG_1RN0LG_1RF1LG_0RN0RF_1RN1RF_1RR1RJ_1RV0LG_0RR0RV_1RR1RV_1LW1RI_---1LW_0LG---_1LW---_0LD---_1LD---_0RI0LG_1RI1LW_0RN0LD_0RF1LD".
Definition tm1 := TM'_from_str "1RB1RF_1LC---_0RA0LD_0LE1LC_1RA0LE_1RG1LC_0RA0RH_1RI0LE_1RA1RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RJ_0RA0LD_0LE1LC_1RA0LE_1RG1LC_0RA0RH_1RI0LE_1RA1RH_1RJ1RJ".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "NRWDGVIFJ".
Definition mp' := mp_from_str "NRWDGVIFJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM540.


Module TM541.
Definition tm := TM_from_str "1RB1RD_1LC---_0LF0LD_0RE1LC_1RA1RF_1RE0LF".
Definition tm' := TM_from_str "1RB1RC_1LA---_0RE1LD_0LF0LC_1RA1RF_1RE0LF".
Definition tm0 := TM'_from_str "0RF0RN_1RF1RN_1LO1RQ_---1LO_1LW---_1LO---_0LL---_1LL---_1RB0RB_0LW0LL_0LW0LO_1LW1LO_0RQ1LW_1RQ1LO_0RB0LL_0RV1LL_0RB0RV_1RB1RV_1RF1RR_1RN0LW_0RR1RB_1RR0LW_1RB0LW_1RV1LW".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1LK1RQ_---1LK_------_1LK---_0LD---_1LD---_0RQ1LW_1RQ1LK_0RB0LP_0RV1LP_1RB0RB_0LW0LP_0LW0LK_1LW1LK_0RB0RV_1RB1RV_1RF1RR_1RJ0LW_0RR1RB_1RR0LW_1RB0LW_1RV1LW".
Definition tm1 := TM'_from_str "1RB1RF_1LC---_0RA0LD_1LE1LC_1RA0LE_1RG1LC_0RA0RH_1RI0LE_1RA1RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RJ_0RA0LD_1LE1LC_1RA0LE_1RG1LC_0RA0RH_1RI0LE_1RA1RH_1RJ1RJ".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "BFOLWNQVR".
Definition mp' := mp_from_str "BFKPWJQVR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 53 53.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM541.


Module TM542.
Definition tm := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_1LD0RB_0LB0LA".
Definition tm' := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_1LD0LB_0LB0LA".
Definition tm0 := TM'_from_str "0RJ---_1LX---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LX_0RJ1LX_0RM0RJ_1RM1RJ_1LP1RM_0RF1RJ_1LP0RF_1LG1RF_0LT1RI_1LT1LC_1LT0RE_1LC1RE_0LP0RI_1LP1LG_0RM0LH_0LX---_0LG0LC_1LG1LC".
Definition tm0' := TM'_from_str "0RJ---_1LX---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LX_0RJ1LX_0RM0RJ_1RM1RJ_1LP1RM_0RF1RJ_1LP0RF_1LG1RF_0LT1RI_1LT1LC_1LT0RM_1LC0LX_0LP0LG_1LP1LG_0RM0LH_0LX---_0LG0LC_1LG1LC".
Definition tm1 := TM'_from_str "1RB1LG_0RC0RI_1LD0RA_1LE1LG_1LD1LF_0RC0LJ_0LH---_0RI1LJ_1RC1RI_1LF1LG".
Definition tm2 := TM'_from_str "1RB1LG_0RC0RI_1LD0RA_1LE1LG_1LD1LF_0RC0LJ_0LH1RK_0RI1LJ_1RC1RI_1LF1LG_1RK1RK".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FIMPTGCHJX".
Definition mp' := mp_from_str "FIMPTGCHJX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 55 55.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM542.


Module TM543.
Definition tm := TM_from_str "1RB---_0LC1RE_0LD0RB_1RE1LD_1RA0RF_1LB1RF".
Definition tm' := TM_from_str "1RB0LC_0LA1RD_1RD1LC_1RE0RF_1RB---_1LB1RF".
Definition tm0 := TM'_from_str "0RF---_1RF---_0LO---_1RR---_0LO0RR_0LO1RR_0LK1RB_1LK1RU_1RB0RE_0LP1RE_0LO0LO_1LO0RR_0RR1RU_1RR1LP_1RB0LP_1RU1LP_0RB0RU_1RB1RU_1RF1LK_---0RV_1LK0RV_1RU1RV_0LH1RU_1LH1RV".
Definition tm0' := TM'_from_str "0RF1RR_1RF0LL_0LK0LK_1RN1LK_0LK0RN_0LK1RN_0LC1RR_1LC1RU_0RN1RU_1RN1LL_1RR0LL_1RU1LL_0RR0RU_1RR1RU_1RF1LC_---0RV_0RF---_1RF---_0LK---_1RN---_1LC0RV_1RU1RV_0LH1RU_1LH1RV".
Definition tm1 := TM'_from_str "1RB1RA_1LC0RA_0LD0LD_1RE0LH_1RF---_0LD1RG_1RE1RB_1RB1LH".
Definition tm2 := TM'_from_str "1RB1RA_1LC0RA_0LD0LD_1RE0LH_1RF1RI_0LD1RG_1RE1RB_1RB1LH_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "VUKOBFRP".
Definition mp' := mp_from_str "VUCKRFNL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 56 56.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM543.


Module TM544.
Definition tm := TM_from_str "1RB---_0LC1RD_0LE1RD_0RC0RA_0LF1LE_1RA1LC".
Definition tm' := TM_from_str "1RB---_0LB1RC_0RD0RA_0LE1RC_0LF1LE_1RA1LD".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RI---_1RN---_0LS0RN_1RI1RN_0LK1RI_1LK1RA_0LW0RN_0LT1RN_0LS1RI_1LS1RA_0RI0RA_1RI1RA_0LW0RF_0RN---_1RF1LW_0LL1LT_0LW0LT_1LW1LT_0RB1LS_1RB1RA_1RF0LL_---1LL".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RM---_1RJ---_0LG0RJ_1RM1RJ_0LG1RM_1LG1RA_0RM0RA_1RM1RA_0LW0RF_0RJ---_0LW0RJ_0LT1RJ_0LS1RM_1LS1RA_1RF1LW_0LP1LT_0LW0LT_1LW1LT_0RB1LS_1RB1RA_1RF0LP_---1LP".
Definition tm1 := TM'_from_str "0LB0RH_1RG0LC_1LD1RF_0LB0LE_1LB1LE_0RG---_1RA1RH_1RA1RF".
Definition tm2 := TM'_from_str "0LB0RH_1RG0LC_1LD1RF_0LB0LE_1LB1LE_0RG1RI_1RA1RH_1RA1RF_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "IWLSTAFN".
Definition mp' := mp_from_str "MWPSTAFJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 58 58.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM544.


Module TM545.
Definition tm := TM_from_str "1RB---_0LB1RC_0RD0RA_0LE1RC_0LF1LE_1RA1LD".
Definition tm' := TM_from_str "1RB---_0RC1RF_0LD1RF_0LE1LD_1RA1LC_0RC0RA".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RM---_1RJ---_0LG0RJ_1RM1RJ_0LG1RM_1LG1RA_0RM0RA_1RM1RA_0LW0RF_0RJ---_0LW0RJ_0LT1RJ_0LS1RM_1LS1RA_1RF1LW_0LP1LT_0LW0LT_1LW1LT_0RB1LS_1RB1RA_1RF0LP_---1LP".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RI---_1RV---_0RI0RV_1RI1RV_0LS1RI_0RV1RA_0LS0RV_0LP1RV_0LO1RI_1LO1RA_1RF1LS_0LL1LP_0LS0LP_1LS1LP_0RB1LO_1RB1RA_1RF0LL_---1LL_0RI0RA_1RI1RA_0LS0RF_0RV---".
Definition tm1 := TM'_from_str "0LB0RH_1RG0LC_1LD1RF_0LB0LE_1LB1LE_0RG---_1RA1RH_1RA1RF".
Definition tm2 := TM'_from_str "0LB0RH_1RG0LC_1LD1RF_0LB0LE_1LB1LE_0RG1RI_1RA1RH_1RA1RF_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "MWPSTAFJ".
Definition mp' := mp_from_str "ISLOPAFV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 58 58.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM545.


Module TM546.
Definition tm := TM_from_str "1LB1RB_1LC1RB_1RA0LD_1LE1LD_1RF0RA_---0RE".
Definition tm' := TM_from_str "1LB1RB_1LC1RB_1RB0LD_1LE1LD_1RF0RA_---0RE".
Definition tm0 := TM'_from_str "1LL0RF_1RF1RF_0LH1LO_1LH1RF_1RF0RF_1LO1RF_0LL1LO_1LL1RF_0RB0LT_1RB0LP_1RF0LO_1RF1LO_1RQ1LT_0RF1LP_0LT0LP_1LT1LP_0RV0RA_1RV1RA_---1LL_1RQ0RF_---0RQ_---1RQ_---0RV_---0RA".
Definition tm0' := TM'_from_str "1LL0RF_1RF1RF_0LH1LO_1LH1RF_1RF0RF_1LO1RF_0LL1LO_1LL1RF_0RF0LT_1RF0LP_1LO0LO_1RF1LO_1RQ1LT_0RF1LP_0LT0LP_1LT1LP_0RV0RA_1RV1RA_---1LL_1RQ0RF_---0RQ_---1RQ_---0RV_---0RA".
Definition tm1 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1RE0RA_0RG0RF_1LH0RA_---1RE_1RA1LB".
Definition tm2 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1RE0RA_0RG0RF_1LH0RA_1RI1RE_1RA1LB_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "FOPTQAVL".
Definition mp' := mp_from_str "FOPTQAVL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 58 58.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM546.


Module TM547.
Definition tm := TM_from_str "1LB1RA_0LC0LF_1RD0RA_1RE0RC_---1RA_1LC1LF".
Definition tm' := TM_from_str "1LB1RA_0LC0LF_1RD0RA_1RE0RC_---1LA_1LC1LF".
Definition tm0 := TM'_from_str "1LK0RB_1LW1RB_0LH1LW_1LH1RB_1RR0LL_1LK0LX_0LK0LW_1LK1LW_0RN0RA_1RN1RA_1RR1LK_1RI0RB_0RR0RI_1RR1RI_---0RN_1RB0RA_---0RB_---1RB_---1LW_---1RB_1RI1LL_0RB1LX_0LL0LX_1LL1LX".
Definition tm0' := TM'_from_str "1LK0RB_1LW1RB_0LH1LW_1LH1RB_1RR0LL_1LK0LX_0LK0LW_1LK1LW_0RN0RA_1RN1RA_1RR1LK_1RI0RB_0RR0RI_1RR1RI_---0RN_1RB0RA_---1LH_---1RB_---0LD_---1LD_1RI1LL_0RB1LX_0LL0LX_1LL1LX".
Definition tm1 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1RE0RA_0RG0RF_1LH0RA_1RI1RE_1RI1LH_---1RA".
Definition tm2 := TM'_from_str "1LB1RA_0LD0LC_1LD1LC_1RE0RA_0RG0RF_1LH0RA_1RI1RE_1RI1LH_1RJ1RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "BWXLIANKR".
Definition mp' := mp_from_str "BWXLIANKR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 58 58.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM547.


Module TM548.
Definition tm := TM_from_str "1LB1RA_1LC0LE_1RD0RA_---1RC_1RC1LF_1LC1LE".
Definition tm' := TM_from_str "1LB1RA_0RC0LC_1RE1LD_1LE1LC_1RF0RA_---1RE".
Definition tm0 := TM'_from_str "1LL0RB_1LS1RB_0LH1LS_1LH1RB_1RJ1RN_0RB0LX_0LL0LS_1LL1LS_0RN0RA_1RN1RA_---1LL_1RJ0RB_---0RJ_---1RJ_---1RN_---1RA_0RJ1LL_1RJ1LT_1RN0LX_1RA1LX_1RJ1RA_0RB1LX_0LL0LT_1LL1LT".
Definition tm0' := TM'_from_str "1LT0RB_1LK1RB_0LH1LK_1LH1RB_0RI1RV_1RI0LP_0RR0LK_1LT1LK_0RR1LT_1RR1LL_1RV0LP_1RA1LP_1RR1RA_0RB1LP_0LT0LL_1LT1LL_0RV0RA_1RV1RA_---1LT_1RR0RB_---0RR_---1RR_---1RV_---1RA".
Definition tm1 := TM'_from_str "1LB1RA_1RF0LC_1LH1LD_1RE1LC_1LH0RA_---1RG_1RF1RE_1RG0RA".
Definition tm2 := TM'_from_str "1LB1RA_1RF0LC_1LH1LD_1RE1LC_1LH0RA_1RI1RG_1RF1RE_1RG0RA_1RI1RI".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "BSXTANJL".
Definition mp' := mp_from_str "BKPLAVRT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 62 62.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM548.


Module TM549.
Definition tm := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1RB_0LB0RF_0LA1LF".
Definition tm' := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1RB_0RF0LA_0LB1LF".
Definition tm0 := TM'_from_str "0RJ---_1LT---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_---1RF_0LD1RI_1LD1LC_0RM0RU_0LT1RU_0LG0LH_1LG1LC_0LH1LC_---1LX_0LC0LX_1LC1LX".
Definition tm0' := TM'_from_str "0RJ---_1LT---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_---1RF_0LD1RI_1LD1LC_0RU0LH_1RU---_0RM0LC_1LG1LC_0RM1LG_0LT1LX_0LG0LX_1LG1LX".
Definition tm1 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD---_0RC0LF".
Definition tm2 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD1RI_0RC0LF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FIMHJTCG".
Definition mp' := mp_from_str "FIMHJTCG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM549.


Module TM550.
Definition tm := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1RB_0RF0LA_0LB1LF".
Definition tm' := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1LF_0LB0LA_0RF1RB".
Definition tm0 := TM'_from_str "0RJ---_1LT---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_---1RF_0LD1RI_1LD1LC_0RU0LH_1RU---_0RM0LC_1LG1LC_0RM1LG_0LT1LX_0LG0LX_1LG1LX".
Definition tm0' := TM'_from_str "0RJ---_1LT---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_---1LC_0LD0LX_1LD1LX_0RM0LH_0LT---_0LG0LC_1LG1LC_0RU0RF_1RU1RF_0RU1RI_0RF1LC".
Definition tm1 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD---_0RC0LF".
Definition tm2 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD1RI_0RC0LF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FIMHJTCG".
Definition mp' := mp_from_str "FIMHJTCG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM550.


Module TM551.
Definition tm := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1LF_0LB0LA_0RF1RB".
Definition tm' := TM_from_str "1LB0LA_0RC1LE_0RD1RC_1LA1RB_0LB1LF_0RA---".
Definition tm0 := TM'_from_str "0RJ---_1LT---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_---1LC_0LD0LX_1LD1LX_0RM0LH_0LT---_0LG0LC_1LG1LC_0RU0RF_1RU1RF_0RU1RI_0RF1LC".
Definition tm0' := TM'_from_str "0RJ0LH_1LT0LC_0LH0LC_1LH1LC_0RI1LG_1RI1LX_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_1LC1RF_0LD1RI_1LD1LX_0RM0LH_0LT---_0LG0LX_1LG1LX_0RA---_1RA---_0RJ---_0LH---".
Definition tm1 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD---_0RC0LF".
Definition tm2 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD1RI_0RC0LF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FIMHJTCG".
Definition mp' := mp_from_str "FIMHJTXG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM551.


Module TM552.
Definition tm := TM_from_str "1LB0LA_0RC1LE_0RD1RC_1LA1RB_0LB1LF_0RA---".
Definition tm' := TM_from_str "1RB---_0RC1RB_1LD1RE_1LE---_0RB1LF_0LE0LD".
Definition tm0 := TM'_from_str "0RJ0LH_1LT0LC_0LH0LC_1LH1LC_0RI1LG_1RI1LX_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_1LC1RF_0LD1RI_1LD1LX_0RM0LH_0LT---_0LG0LX_1LG1LX_0RA---_1RA---_0RJ---_0LH---".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RI---_1RF---_0RI0RF_1RI1RF_1LT1RI_0RR1RF_1LT0RR_---1RR_0LP1RE_1LP1LO_0RF---_1LX---_0LT---_1LT---_0RE1LS_1RE1LO_0RI0LX_0RF1LX_0RI0LT_0LX---_0LS0LO_1LS1LO".
Definition tm1 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD---_0RC0LF".
Definition tm2 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD1RI_0RC0LF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FIMHJTXG".
Definition mp' := mp_from_str "REITFXOS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM552.


Module TM553.
Definition tm := TM_from_str "1RB---_0RC1RB_1LD1RE_1LE---_0RB1LF_0LE0LD".
Definition tm' := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_0RE1LA_0LB0LA".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RI---_1RF---_0RI0RF_1RI1RF_1LT1RI_0RR1RF_1LT0RR_---1RR_0LP1RE_1LP1LO_0RF---_1LX---_0LT---_1LT---_0RE1LS_1RE1LO_0RI0LX_0RF1LX_0RI0LT_0LX---_0LS0LO_1LS1LO".
Definition tm0' := TM'_from_str "0RJ---_1LX---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LX_0RJ1LX_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_1LD1RF_0LT1RI_1LT1LC_0RQ1LH_1RQ---_0RQ0LD_1LH1LD_0RM0LH_0LX---_0LG0LC_1LG1LC".
Definition tm1 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD---_0RC0LF".
Definition tm2 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD1RI_0RC0LF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "REITFXOS".
Definition mp' := mp_from_str "FIMHJXCG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM553.


Module TM554.
Definition tm := TM_from_str "1LB0RF_0RC---_0RA0LD_1LE0RC_1RA0LC_1RD1RB".
Definition tm' := TM_from_str "1LB0RF_0RC---_0RA0LD_1LE0LF_1RA0LC_1RD1RB".
Definition tm0 := TM'_from_str "0LT0RU_---1RU_0LH0RN_1LH0RF_0RI---_1RI---_0RA---_0LT---_0RA0LT_1RA0RA_0LT0LO_0RU1LO_1RU0RI_1LK1RI_0LT0RA_1LT0LT_0RB0LT_1RB0LO_---0LK_1RU1LK_0RN0RF_1RN1RF_1LK1RI_1RI---".
Definition tm0' := TM'_from_str "0LT0RU_---1RU_0LH0RN_1LH0RF_0RI---_1RI---_0RA---_0LT---_0RA0LT_1RA0LW_0LT0LO_0RU1LO_1RU1LK_1LK1RI_0LT0LW_1LT1LW_0RB0LT_1RB0LO_---0LK_1RU1LK_0RN0RF_1RN1RF_1LK1RI_1RI---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LD_1RE1LB_0LC---_0RA0RH_0RG0LC_0LC0RE_1RF---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LD_1RE1LB_0LC---_0RA0RH_0RG0LC_0LC0RE_1RF1RI_1RI1RI".
Definition l0 := [1;0;1;0;0;0;1;1;0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "NKTOUIAF".
Definition mp' := mp_from_str "NKTOUIAF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 57 57.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM554.


Module TM555.
Definition tm := TM_from_str "1RB1RF_1LC0LA_1RE0LD_0RE0LB_1LF0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LA---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RM_1RM---_1RA1LO_1LO1RM_0LL0LC_1LL1LC_0RR0LL_1RR0LG_---0LO_1RA1LO_0RQ0LL_1RQ0LC_0LL0LG_0RA1LG_0LL0RA_---1RA_0LX0RF_1LX0RV_0RM---_1RM---_0RQ---_0LL---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LG_0RQ0LO_1RA1LO_0RQ0LL_1RQ0RQ_0LL0LG_0RA1LG_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1RM---_------_0LD---_1LD---".
Definition tm1 := TM'_from_str "1LB1RE_0LC0LG_1RD1LB_0RA0RH_0RF0LC_0LC0RD_0LC---_1RE---".
Definition tm2 := TM'_from_str "1LB1RE_0LC0LG_1RD1LB_0RA0RH_0RF0LC_0LC0RD_0LC---_1RE1RI_1RI1RI".
Definition l0 := [1;0;1;1;0;1;0;0;0;1;1;0;1;0;0;0]%N.
Definition mp := mp_from_str "FOLAMQGV".
Definition mp' := mp_from_str "FOLAMQGU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM555.


Module TM556.
Definition tm := TM_from_str "1RB0RF_1LC1RE_0LE0LD_0LB0RD_1RA0LD_0RB---".
Definition tm' := TM_from_str "1RB0RF_1LC1RC_0LE0LD_0LB0RD_1RA1RE_0RB---".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1LO0RE_1RR---_1LS0RR_1LO1RR_0LL1RB_1LL0LL_1RF0LG_0LO0LL_0LS0LO_1LS1LO_0LL0RM_1RB1RM_0LG0LL_1LG0RM_0RB0LG_1RB0LL_1RF0LO_1RU1LO_0RE---_1RE---_1LS---_0RR---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO0RE_1RJ---_1LS0RJ_1LO1RJ_0LL1RB_1LL0LL_1RF0LG_1RB0LL_0LS0LO_1LS1LO_0LL0RM_1RB1RM_0LG0LL_1LG0RM_0RB0RR_1RB1RR_1RF1RB_1RU1RR_0RE---_1RE---_1LS---_0RJ---".
Definition tm1 := TM'_from_str "1LB1RF_0LD0LC_1LE1LB_0LC---_1RA---_1RG0LC_1RA1RH_0RI---_1LE0RF".
Definition tm2 := TM'_from_str "1LB1RF_0LD0LC_1LE1LB_0LC---_1RA---_1RG0LC_1RA1RH_0RI1RJ_1LE0RF_1RJ1RJ".
Definition l0 := [1;1;1;1;0;0;1;1;1;1;1;1;0;0;1;1]%N.
Definition mp := mp_from_str "FOLGSRBUE".
Definition mp' := mp_from_str "FOLGSJBUE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 91 91.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM556.


Module TM557.
Definition tm := TM_from_str "1RB1RE_1RC0RD_0LC1LD_1RA1LE_0RF0LB_---1RD".
Definition tm' := TM_from_str "1RB1RF_1RC0RE_0LD1RE_---1LE_1RA1LF_0RC0LB".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1RJ1RU_1RM0RB_0RJ0RM_1RJ1RM_0LP0RB_1LT0RN_0LK1RR_0LP1LT_0LK0LP_1LK1LP_0RB0RN_1RB1LG_1RF0LT_1RR1LT_0RU0LP_1RU0RB_---0LG_0RN1LG_---0RN_---1RN_---1RB_---1LG".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1RJ1RI_1RQ0RB_0RJ0RQ_1RJ1RQ_0LT0RB_1RR0RR_---0RR_0LT1RR_0LO1RB_1LO1LG_---1RV_---1LX_---0LT_---1LT_0RB0RR_1RB1LG_1RF0LX_1RV1LX_0RI0LT_1RI0RB_---0LG_0RR1LG".
Definition tm1 := TM'_from_str "1RB1RJ_0LC---_1RG1LD_0RH1LE_0LC0RF_1RA1RG_1RI0RF_1RF1LE_---0RH_0RF0RH".
Definition tm2 := TM'_from_str "1RB1RJ_0LC---_1RG1LD_0RH1LE_0LC0RF_1RA1RG_1RI0RF_1RF1LE_1RK0RH_0RF0RH_1RK1RK".
Definition l0 := [1;1;0;0;1;0;1;1;0;1;0;1;1;0;1;1]%N.
Definition mp := mp_from_str "FJPTGBRNUM".
Definition mp' := mp_from_str "FJTXGBVRIQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 99 99.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM557.


Module TM558.
Definition tm := TM_from_str "1LB0RC_1LC0LA_0RD0LB_1RA0RE_1RC1RF_0RC---".
Definition tm' := TM_from_str "1LB0LE_1LC0LA_0RD0LB_1RA0RE_1RC1RF_0RC---".
Definition tm0 := TM'_from_str "1LL0RI_1LC1RI_0LH0RM_1LH0LL_0RQ0LH_1LG0RM_0LL0LC_1LL1LC_0RM0LL_1RM0LC_0RB0LG_0RQ1LG_0RB0RQ_1RB1RQ_1LC0RJ_1RI0RV_0RJ0RV_1RJ1RV_1RM1RI_0LC---_0RI---_1RI---_0RM---_0LL---".
Definition tm0' := TM'_from_str "1LL1RM_1LC1RI_0LH0LS_1LH1LS_0RQ0LH_1LG0LS_0LL0LC_1LL1LC_0RM0LL_1RM0LC_0RB0LG_0RQ1LG_0RB0RQ_1RB1RQ_1LC0RJ_1RI0RV_0RJ0RV_1RJ1RV_1RM1RI_0LC---_0RI---_1RI---_0RM---_0LL---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RJ_0LD---_1LE1LC_0RG1LF_0LE---_0RH0RI_1RA0LC_1RJ---_0RA0LE".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RJ_0LD---_1LE1LC_0RG1LF_0LE---_0RH0RI_1RA0LC_1RJ1RK_0RA0LE_1RK1RK".
Definition l0 := [0;0;1;0;0;1;0;0;1;0;0;0;1;0;1;0]%N.
Definition mp := mp_from_str "MBCHLGQJVI".
Definition mp' := mp_from_str "MBCHLGQJVI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 true) 233 233.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM558.


Module TM559.
Definition tm := TM_from_str "1RB0LF_0LC---_0LA0RD_1RE0RF_1LA0RC_1LD1LB".
Definition tm' := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC0LF_1RE---".
Definition tm0 := TM'_from_str "0RF0LP_1RF0LH_0RR0LW_---1LW_0LC---_0RR---_0LK---_1LK---_0RR0RM_0LW1RM_0LC0RR_1LC0RU_0RR0RU_1RR1RU_1LW1RI_1RI1LK_---0RI_1LW1RI_0LD0RR_1LD0RM_1RI1LK_1LK---_0LP0LH_1LP1LH".
Definition tm0' := TM'_from_str "0LG0RM_1LS1RM_0LH0RB_1LH0RI_0RI0LL_1RI0LW_0RB0LS_0LG1LS_0RB0LG_1RB0RB_1LS0LO_1RM1LO_0RB0RI_0LS1RI_0LG0RB_1LG0LG_1RM1LO_1LO---_0LL0LW_1LL1LW_0RR---_1RR---_1LO---".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_0LD0LG_1RA1LE_0LF0RB_0RB0LC_1LE---_0RB---".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_0LD0LG_1RA1LE_0LF0RB_0RB0LC_1LE1RI_0RB---_1RI1RI".
Definition l0 := [1;0;1;1;0;0;1;0;1;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "IRWPKCHM".
Definition mp' := mp_from_str "MBSLOGWI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 631 631.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM559.


Module TM560.
Definition tm := TM_from_str "1RB1RA_1LC0RC_1RF1LD_0RE0LB_---1RC_0LA1RD".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC_------".
Definition tm0 := TM'_from_str "0RF0RB_1RF1RB_1LP1RF_1RI1RB_1RN0RI_1LP1RI_0LL0RV_1LL0RJ_0RV0RJ_1RV1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RV_---0LG_0RJ1LG_---0RJ_---1RJ_---1RV_---1LG_1LP0RN_1RF1RN_0LC1RQ_1LC0RV".
Definition tm0' := TM'_from_str "0RF0RN_1RF1RN_1LP1RQ_1RI0RB_1RN0RI_1LP1RI_0LL0RB_1LL0RJ_0RB0RJ_1RB1LG_1RF0LP_1RN1LP_0RQ0LL_1RQ0RB_---0LG_0RJ1LG_---0RJ_---1RJ_---1RB_---1LG".
Definition tm1 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_---0RH".
Definition tm2 := TM'_from_str "1RB1RF_1LC1RG_0RH1LD_0LE0RA_1RF1LC_1RI0RA_0RA0RH_1RA1LD_1RJ0RH_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "VFPGLNIJQ".
Definition mp' := mp_from_str "BFPGLNIJQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM560.


Module TM561.
Definition tm := TM_from_str "1LB---_0RC1LF_0RD1RC_1LE1RB_0RE1LA_0LB0LA".
Definition tm' := TM_from_str "1LB---_0RC1LE_0RD1RC_1LA1RB_0LB0LA_------".
Definition tm0 := TM'_from_str "0RJ---_1LX---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LX_0RJ1LX_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_1LD1RF_0LT1RI_1LT1LC_0RQ1LH_1RQ---_0RQ0LD_1LH1LD_0RM0LH_0LX---_0LG0LC_1LG1LC".
Definition tm0' := TM'_from_str "0RJ---_1LT---_0LH---_1LH---_0RI1LG_1RI1LC_0RM0LT_0RJ1LT_0RM0RJ_1RM1RJ_1LH1RM_0RF1RJ_1LH0RF_---1RF_0LD1RI_1LD1LC_0RM0LH_0LT---_0LG0LC_1LG1LC".
Definition tm1 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD---_0RC0LF".
Definition tm2 := TM'_from_str "1RB1LG_0RC0RE_1LD0RA_0RE1LF_1RC1RE_1LH1LG_0LD1RI_0RC0LF_1RI1RI".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FIMHJXCG".
Definition mp' := mp_from_str "FIMHJTCG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM561.


Module TM562.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1LA1RD_0RE---_0RF1RF_0RB0LA".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_1LF1RD_0RE---_0RF1RF_0RB0LA".
Definition tm0 := TM'_from_str "1RN0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1LC0LC_1RN1LC_1LH0RN_1LC1RN_0LD1RQ_1LD---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LC_0RE0LH_1RE0LC_0RJ0LC_0LH1LC".
Definition tm0' := TM'_from_str "1RN0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1LC0LC_1RN1LC_0LH0RN_1LC1RN_0LX1RQ_1LX---_0RQ---_1RQ---_0RU---_0RV---_0RU0RV_1RU1RV_0RE1RE_0LH0LC_0RE0LH_1RE0LC_0RJ0LC_0LH1LC".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE---_0RF0RH_0RG0LC_0RA0LC_1RG0LB".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_1RE1RI_0RF0RH_0RG0LC_0RA0LC_1RG0LB_1RI1RI".
Definition l0 := [1;1;0;1;1;0;1;0]%N.
Definition mp := mp_from_str "JCHNQUEV".
Definition mp' := mp_from_str "JCHNQUEV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 12 12.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM562.


Module TM563.
Definition tm := TM_from_str "1RB---_1LC1RF_1RD1RC_0LE1RF_0LF1LE_1RA0RD".
Definition tm' := TM_from_str "1RB---_1RC1RF_1RD1RC_0LE1RF_0LF1LE_1RA0RD".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RJ---_1RV---_1RV0RV_1RJ1RV_0LL1RB_1LL1RM_0RN0RJ_1RN1RJ_0LT1RN_1RV1RJ_0LW0RV_0LT1RV_0LS1RB_1LS1RM_1RF1LW_0LW1LT_0LW0LT_1LW1LT_0RB0RM_1RB1RM_1RF0LW_---0RV".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RJ---_1RV---_0RJ0RV_1RJ1RV_1RN1RB_1RJ1RM_0RN0RJ_1RN1RJ_0LT1RN_1RV1RJ_0LW0RV_0LT1RV_0LS1RB_1LS1RM_1RF1LW_0LW1LT_0LW0LT_1LW1LT_0RB0RM_1RB1RM_1RF0LW_---0RV".
Definition tm1 := TM'_from_str "0LB1RF_1LC1LB_1RD0LC_1RE1RF_1RA1RE_1RH1RG_0LC0RF_1RD---".
Definition tm2 := TM'_from_str "0LB1RF_1LC1LB_1RD0LC_1RE1RF_1RA1RE_1RH1RG_0LC0RF_1RD1RI_1RI1RI".
Definition l0 := [1;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "NTWFJVMB".
Definition mp' := mp_from_str "NTWFJVMB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM563.


Module TM564.
Definition tm := TM_from_str "1LB1LA_0RC1LD_0RD1RC_1LE0LB_1LF---_1RA1LD".
Definition tm' := TM_from_str "1LB1LA_0RC1LD_0RD1RC_1LE0LB_1LF---_1LA1LD".
Definition tm0 := TM'_from_str "0RJ1LH_1LP1LD_0LH0LD_1LH1LD_0RI1LT_1RI1LG_0RM0LP_0RJ1LP_0RM0RJ_1RM1RJ_1LX1RM_0RM1RJ_1LX0RM_---0LP_0LT0LG_1LT1LG_1LD---_1LP---_0LX---_1LX---_0RB1LT_1RB1LG_1LP0LP_1LD1LP".
Definition tm0' := TM'_from_str "0RJ1LH_1LP1LD_0LH0LD_1LH1LD_0RI1LT_1RI1LG_0RM0LP_0RJ1LP_0RM0RJ_1RM1RJ_1LX1RM_0RM1RJ_1LX0RM_---0LP_0LT0LG_1LT1LG_1LD---_1LP---_0LX---_1LX---_1LH1LT_1LD1LG_0LD0LP_1LD1LP".
Definition tm1 := TM'_from_str "1LB0RA_1LF1LC_1LE1LD_0RA0LC_1LB---_1LG1LF_0RH1LC_1RA1RH".
Definition tm2 := TM'_from_str "1LB0RA_1LF1LC_1LE1LD_0RA0LC_1LB1RI_1LG1LF_0RH1LC_1RA1RH_1RI1RI".
Definition l0 := [0;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "MXPGTDHJ".
Definition mp' := mp_from_str "MXPGTDHJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM564.


Module TM565.
Definition tm := TM_from_str "1LB0RE_0RC0LB_0LA1LD_1RA0RF_1RD1RE_0RA---".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_1LB0RD_1RE1RD_1RC0RF_0RC---".
Definition tm0 := TM'_from_str "1RQ0RQ_1LG1RQ_0LH0RN_1LH0RR_0RI0LH_1RI0LG_0LH0LG_1RQ1LG_0LH1RQ_0RN---_0LC0LP_1LC1LP_0RB0RU_1RB1RU_1LG0RA_1RQ---_0RN0RR_1RN1RR_1RB1RN_1RU1RR_0RA---_1RA---_1RQ---_0RQ---".
Definition tm0' := TM'_from_str "1RM0LH_1LC0LC_0LH0LC_1LH1LC_0RJ0LH_1RJ0LC_1LC0LC_1RM1LC_1RM0RM_1LC1RM_0LH0RR_1LH0RN_0RR0RN_1RR1RN_1RJ1RR_1RU1RN_0RJ0RU_1RJ1RU_1LC0RI_1RM---_0RI---_1RI---_1RM---_0RM---".
Definition tm1 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_0RE0RH_1RA1RF_0RG---_1RD0RD_1RE1RH".
Definition tm2 := TM'_from_str "1LB1RD_0LC0LB_1RD1LB_0RE0RH_1RA1RF_0RG1RI_1RD0RD_1RE1RH_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "BGHQNUAR".
Definition mp' := mp_from_str "JCHMRUIN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 16 16.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM565.


Module TM566.
Definition tm := TM_from_str "1RB0RC_1LC1RA_0RE1RD_1LF0RB_---1RD_1LB0LD".
Definition tm' := TM_from_str "1RB0RC_1LC1RA_1RE1RD_1LF0RB_---1LA_1LB0LD".
Definition tm0 := TM'_from_str "0RF0RI_1RF1RI_1RE0RQ_1RB0RN_0RN0RB_1RE1RB_0LL1RF_1LL1RI_0RQ0RN_1RQ1RN_---1LO_0RN1RE_1LH0RE_1LO1RE_0LX0RN_1LX0RB_---0RN_---1RN_---1LO_---1RE_1LL0LX_1RI0RN_0LH0LO_1LH1LO".
Definition tm0' := TM'_from_str "0RF0RI_1RF1RI_1RE0RR_1RB0RN_0RN0RB_1RE1RB_0LL1RF_1LL1RI_0RR0RN_1RR1RN_---1LO_0RN1RE_1LH0RE_1LO1RE_0LX0RN_1LX0RB_---1RB_---0RN_---0LD_---1LD_1LL0LX_1RI0RN_0LH0LO_1LH1LO".
Definition tm1 := TM'_from_str "1RB1RI_0RC0RI_1LD1RB_0LE0RC_1LF1LD_1LH1RG_0RJ0RC_0RC---_1RA1RG_---0RC".
Definition tm2 := TM'_from_str "1RB1RI_0RC0RI_1LD1RB_0LE0RC_1LF1LD_1LH1RG_0RJ0RC_0RC---_1RA1RG_1RK0RC_1RK1RK".
Definition l0 := [0;1;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "FENOXHILBQ".
Definition mp' := mp_from_str "FENOXHILBR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 true) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM566.


Module TM567.
Definition tm := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0RE---".
Definition tm' := TM_from_str "1LB0RB_1LC0LE_1RD1LB_1RA0RD_1LB1LF_0RC---".
Definition tm0 := TM'_from_str "1LL0RE_1LS1RE_0LH1RM_1LH0LH_1RM0LH_1LH0LW_0LL0LS_1LL1LS_0RN1LL_1RN1LS_1RB0LH_1RM1LH_0RB0RM_1RB1RM_1LS0RB_1RE0RM_1LL1LL_1LS---_0LH0LW_1LH1LW_0RQ---_1RQ---_1LL---_1LL---".
Definition tm0' := TM'_from_str "1LL0RE_1LS1RE_0LH1RM_1LH0LH_1RM0LH_1LH0LX_0LL0LS_1LL1LS_0RN1LL_1RN1LS_1RB0LH_1RM1LH_0RB0RM_1RB1RM_1LS0RB_1RE0RM_1LL1LL_1LS---_0LH0LX_1LH1LX_0RI---_1RI---_0RN---_1LL---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LE---_1RF1LC_0RA0RF_1RF0LC".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LD_1LE1LB_1LE1RH_1RF1LC_0RA0RF_1RF0LC_1RH1RH".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "BSHWLME".
Definition mp' := mp_from_str "BSHXLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM567.


Module TM568.
Definition tm := TM_from_str "1LB1LE_1RC1LD_1RA0RC_1LA0LB_0LF0RD_1LD---".
Definition tm' := TM_from_str "1LB1LE_1RC1LD_1RA0RC_1LA0LB_1LF0RD_1RD---".
Definition tm0 := TM'_from_str "1RI1LW_1LP1RB_0LH0LT_1LH1LT_0RJ1LD_1RJ1LG_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RB0RI_1LH1RB_1LT0LP_0LD0LG_1LD1LG_0LP0RM_---1RM_0LW1LH_1LW1RB_1LD---_1LG---_0LP---_1LP---".
Definition tm0' := TM'_from_str "1RI1LX_1LP1RB_0LH0LT_1LH1LT_0RJ1LD_1RJ1LG_1RB0LP_1RI1LP_0RB0RI_1RB1RI_1LP0RB_1RB0RI_1LH1RB_1LT0LP_0LD0LG_1LD1LG_0LP0RM_---1RM_0LX1LH_1LX1RB_0RN---_1RN---_1LT---_0LP---".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_0LB---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_0LB1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "BPGDHITW".
Definition mp' := mp_from_str "BPGDHITX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM568.


Module TM569.
Definition tm := TM_from_str "1LB0LF_1RC0LE_1LB0RD_1RC0RD_1LA1LE_0LB---".
Definition tm' := TM_from_str "1LB0LF_1RC0LE_0LD0RC_0RB1RA_1LA1LE_0LB---".
Definition tm0 := TM'_from_str "1RM0LG_1LS---_0LH0LW_1LH1LW_0RJ0LD_1RJ0LT_1LS0LS_1RM1LS_1RM0RM_1LS1RM_0LH0RJ_1LH0RM_0RJ0RM_1RJ1RM_1LS0RJ_1RM0RM_1LH1LD_1LW1LT_0LD0LT_1LD1LT_1LS---_0LS---_0LG---_1LG---".
Definition tm0' := TM'_from_str "1RI0LG_1LS---_0LH0LW_1LH1LW_0RJ0LD_1RJ0LT_1LS0LS_1RI1LS_0RJ0RI_1LS1RI_0LO0RJ_1LO0RI_0RE0RB_1RE1RB_0RJ1LS_0LD---_1LH1LD_1LW1LT_0LD0LT_1LD1LT_1LS---_0LS---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RA_0LD0LG_1LH1LE_0LF---_1LC0LC_1LD1LG_1RA1LC".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RA_0LD0LG_1LH1LE_0LF1RI_1LC0LC_1LD1LG_1RA1LC_1RI1RI".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "MJSDWGTH".
Definition mp' := mp_from_str "IJSDWGTH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM569.


Module TM570.
Definition tm := TM_from_str "1LB1LA_1RC1LF_0RE0LD_---1RC_0RF1RD_1RA0LA".
Definition tm' := TM_from_str "1LB1LA_1RC1LE_0RD0RD_0RE1RF_1RA0LA_---1RC".
Definition tm0 := TM'_from_str "1RQ1LH_1LX1LD_0LH0LD_1LH1LD_0RJ1LD_1RJ1LC_1RQ0LX_1RQ1LX_0RQ---_1RQ1RQ_0RU0LO_0RN1LO_---0RJ_---1RJ_---1RQ_---1RQ_0RU0RN_1RU1RN_0RB---_0LH1RJ_0RB0LH_1RB0LD_1LX0LC_1LD1LC".
Definition tm0' := TM'_from_str "1RM1LH_1LT1LD_0LH0LD_1LH1LD_0RJ1LD_1RJ1LC_1RM0LT_1RM1LT_0RM0RM_1RM1RM_0RQ0RQ_0RV0RV_0RQ0RV_1RQ1RV_0RB---_0LH1RJ_0RB0LH_1RB0LD_1LT0LC_1LD1LC_---0RJ_---1RJ_---1RM_---1RM".
Definition tm1 := TM'_from_str "0RB0LE_1LC1LD_1LD1LF_1LE1LD_1RG1LC_0LE0LD_0RA0RH_---1RI_1RG1RG".
Definition tm2 := TM'_from_str "0RB0LE_1LC1LD_1LD1LF_1LE1LD_1RG1LC_0LE0LD_0RA0RH_1RJ1RI_1RG1RG_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_str "UBXDHCQNJ".
Definition mp' := mp_from_str "QBTDHCMVJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM570.


Module TM571.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1LE_1RF0RA_0LD0RC_1RC---".
Definition tm' := TM_from_str "1LB1RD_1LC0LB_1RA1LE_1RF0RA_0LD0LD_1RC---".
Definition tm0 := TM'_from_str "1LL0RN_1LG1RN_0LH1RV_1LH1RA_1RN0LL_1LT0LG_0LL0LG_1LL1LG_0RB1LO_1RB1LO_1LG0LT_1RN1LT_0RV0RA_1RV1RA_1RJ1LL_---0RN_1RJ0RI_1LL1RI_0LO0RB_1LO1LO_0RJ---_1RJ---_1RB---_1LO---".
Definition tm0' := TM'_from_str "1LL0RN_1LG1RN_0LH1RV_1LH1RA_1RN0LL_1LT0LG_0LL0LG_1LL1LG_0RB1LO_1RB1LO_1LG0LT_1RN1LT_0RV0RA_1RV1RA_1RJ1LL_---0RN_1RJ1RJ_1LL1LL_0LO0LO_1LO1LO_0RJ---_1RJ---_1RB---_1LO---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LB_1RG1LD_1LE1LE_1RF1LC_1RA1LE_1RI1RH_1LC0RG_1RF---".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LB_1RG1LD_1LE1LE_1RF1LC_1RA1LE_1RI1RH_1LC0RG_1RF1RJ_1RJ1RJ".
Definition l0 := [1;1;0;1;0;1;1;1]%N.
Definition mp := mp_from_str "BGLTOJNAV".
Definition mp' := mp_from_str "BGLTOJNAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 17 17.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM571.


Module TM572.
Definition tm := TM_from_str "1LB1LA_1LC0LF_1RD0LA_0LE0RD_0RC1RB_0LC---".
Definition tm' := TM_from_str "1LB1LA_1LC0LF_1RD0LA_1LC0RE_1RD0RE_0LC---".
Definition tm0 := TM'_from_str "1LL1LH_1LW1LD_0LH0LD_1LH1LD_1RM0LK_1LC---_0LL0LW_1LL1LW_0RN0LH_1RN0LD_1LC0LC_1RM1LC_0RN0RM_1LC1RM_0LS0RN_1LS0RM_0RI0RF_1RI1RF_0RN1LC_0LH---_1LC---_0LC---_0LK---_1LK---".
Definition tm0' := TM'_from_str "1LL1LH_1LW1LD_0LH0LD_1LH1LD_1RQ0LK_1LC---_0LL0LW_1LL1LW_0RN0LH_1RN0LD_1LC0LC_1RQ1LC_1RQ0RQ_1LC1RQ_0LL0RN_1LL0RQ_0RN0RQ_1RN1RQ_1LC0RN_1RQ0RQ_1LC---_0LC---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1LB1RH_0LC0LF_1LG1LD_0LE---_1LB0LB_1LC1LF_1RH1LB_0RA0RH".
Definition tm2 := TM'_from_str "1LB1RH_0LC0LF_1LG1LD_0LE1RI_1LB0LB_1LC1LF_1RH1LB_0RA0RH_1RI1RI".
Definition l0 := [1;0;0;1;0;0;1;0]%N.
Definition mp := mp_from_str "NCHWKDLM".
Definition mp' := mp_from_str "NCHWKDLQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM572.


Module TM573.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1LB_0RC0LF_1LB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1LB_0RC0LF_0RC---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC1RM_0RB1RM_1RB1LS_1LS0LH_1RQ1LH_0RI0LH_1RI---_0LH0LW_0RM1LW_1RM---_1LS---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LW_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC1RM_0RB1RM_1RB1LS_1LS0LH_1RQ1LH_0RI0LH_1RI---_0LH0LW_0RM1LW_0RI---_1RI---_0LH---_0RM---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD1RC_1LE1RG_0LB0LF_0LB---_0RA0LB".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD1RC_1LE1RG_0LB0LF_0LB1RH_0RA0LB_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSWQ".
Definition mp' := mp_from_str "IHMBSWQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM573.


Module TM574.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0LE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0LB---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS0LS_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0LH---_0LS---_0LS---_1LS---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS0LS_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0RI---_0LS---_0LG---_1LG---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_0LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSQV".
Definition mp' := mp_from_str "IHMBSQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM574.


Module TM575.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LE---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1LS_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_1RM---_1LS---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1LS_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0RM---_1LS---_0LT---_1LT---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1LE1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSQV".
Definition mp' := mp_from_str "IHMBSQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM575.


Module TM576.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_1LD---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RE---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RU_0RB0RU_1RB1RU_1LS1RQ_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_1RQ---_------_0LP---_1LP---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LS_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1RQ_1RQ---_0RI0LH_1RI0LS_0LH0LS_0RM1LS_0RQ---_1RQ---_0RI---_0LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1RF---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RG_1LE1RF_0LB0LE_0RA0LB_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSQU".
Definition mp' := mp_from_str "IHMBSQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM576.


Module TM577.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_1LA---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0LE---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LC_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS0LH_1RQ---_0RI0LH_1RI0RI_0LH0LC_0RM1LC_1LH---_0LH---_0LD---_1LD---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LC_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RU_0RB0RU_1RB1RU_1LS0LH_1RQ---_0RI0LH_1RI0RI_0LH0LC_0RM1LC_0LH---_0LC---_0LS---_1LS---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_0LB---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_0LB1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSCQV".
Definition mp' := mp_from_str "IHMBSCQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM577.


Module TM578.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0RE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_1LF0RD_1RA0RF_0RC0LA_0RE---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LC_0RI0LS_1RM1LS_0LH0RM_0RI1RM_0LC0RB_1LC0RU_0RB0RU_1RB1RU_1LS0RQ_1RQ---_0RI0LH_1RI0RI_0LH0LC_0RM1LC_0RQ---_1RQ---_0RI---_0LH---".
Definition tm0' := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LC_---0LS_1RM1LS_0LH0RM_---1RM_0LX0RB_1LX0RU_0RB0RU_1RB1RU_1LS0RQ_1RQ---_0RI0LH_1RI0RI_0LH0LC_0RM1LC_0RQ---_1RQ---_0RI---_0LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_0RG---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_0RG1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSCQU".
Definition mp' := mp_from_str "IHMBSCQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM578.


Module TM579.
Definition tm := TM_from_str "1LB0RE_1RC0LE_1LF0RD_1RA1RF_0RC0LA_0RE---".
Definition tm' := TM_from_str "1LB0LD_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0RE---".
Definition tm0 := TM'_from_str "1RM0RQ_1LS1RQ_0LH0RI_1LH0LH_0RJ0LH_1RJ0LC_---0LS_1RM1LS_0LH0RM_---1RM_0LX0RB_1LX0RV_0RB0RV_1RB1RV_1LS1RQ_1RQ---_0RI0LH_1RI0RI_0LH0LC_0RM1LC_0RQ---_1RQ---_0RI---_0LH---".
Definition tm0' := TM'_from_str "1RM1LS_1LS1RQ_0LH0LO_1LH1LO_0RJ0LH_1RJ0LC_0LO0LS_1RM1LS_0LH0RM_0LO1RM_0LC0RB_1LC0RV_0RB0RV_1RB1RV_1LS1RQ_1RQ---_0RI0LH_1RI0LO_0LH0LC_0RM1LC_0RQ---_1RQ---_0RI---_0LH---".
Definition tm1 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1RG---".
Definition tm2 := TM'_from_str "0LB0RC_1RC1LE_0RD0RH_1LE1RG_0LB0LF_0LB---_0RA0LB_1RG1RI_1RI1RI".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IHMBSCQV".
Definition mp' := mp_from_str "IHMBSCQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM579.


Module TM580.
Definition tm := TM_from_str "1RB0RA_1RC---_1LD1RF_1RF1LE_0LC0LE_1RF0RA".
Definition tm' := TM_from_str "1RB0RA_1RC---_1LD1RF_1RA1LE_0LC0LE_1RF0RA".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_---0RA_0RJ---_1RJ---_1LT---_1RV---_1RA0RV_1LT1RV_0LP1RV_1LP1RA_0RV1LK_1RV1LS_1RV0LT_1RA1LT_0LP0LK_1RV0LS_0LK0LS_1LK1LS_0RV0RA_1RV1RA_1RV0RF_1RA0RA".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_---0RA_0RJ---_1RJ---_1LT---_1RV---_1RA0RV_1LT1RV_0LP1RV_1LP1RA_0RB1LK_1RB1LS_1RF0LT_1RA1LT_0LP0LK_1RV0LS_0LK0LS_1LK1LS_0RV0RA_1RV1RA_1RV0RF_1RA0RA".
Definition tm1 := TM'_from_str "0RB0RA_1RC---_1LD1RH_---1LE_0LF0LE_0LG1RH_1RA1LD_1RH1RA".
Definition tm2 := TM'_from_str "0RB0RA_1RC1RI_1LD1RH_---1LE_0LF0LE_0LG1RH_1RA1LD_1RH1RA_1RI1RI".
Definition l0 := [1;0;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "AFJTSKPV".
Definition mp' := mp_from_str "AFJTSKPV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM580.


Module TM581.
Definition tm := TM_from_str "1RB0RA_1RC---_1LD1RF_1RA1LE_0LC0LE_1RF0RA".
Definition tm' := TM_from_str "1RB0RA_1RC---_1LD0RF_1RA1LE_0LC0LE_1LB1LD".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_---0RA_0RJ---_1RJ---_1LT---_1RV---_1RA0RV_1LT1RV_0LP1RV_1LP1RA_0RB1LK_1RB1LS_1RF0LT_1RA1LT_0LP0LK_1RV0LS_0LK0LS_1LK1LS_0RV0RA_1RV1RA_1RV0RF_1RA0RA".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1RJ0RF_---0RA_0RJ---_1RJ---_1LT---_1RU---_1RA0RU_1LT1RU_0LP1RU_1LP1RA_0RB1LK_1RB1LS_1RF0LT_1RA1LT_0LP0LK_1RU0LS_0LK0LS_1LK1LS_1RU1RA_---1LT_0LH0LP_1LH1LP".
Definition tm1 := TM'_from_str "0RB0RA_1RC---_1LD1RH_---1LE_0LF0LE_0LG1RH_1RA1LD_1RH1RA".
Definition tm2 := TM'_from_str "0RB0RA_1RC1RI_1LD1RH_---1LE_0LF0LE_0LG1RH_1RA1LD_1RH1RA_1RI1RI".
Definition l0 := [1;0;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "AFJTSKPV".
Definition mp' := mp_from_str "AFJTSKPU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 true) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM581.


Module TM582.
Definition tm := TM_from_str "1LB0RD_0LC1RD_1RA0LE_0RA0RB_0LB0LF_---0RE".
Definition tm' := TM_from_str "1LB0RD_0LC1RD_1RA0LE_0RA0RB_0LB0LF_---0LC".
Definition tm0 := TM'_from_str "1LK0RM_1RE1RM_0LH0RA_1LH0RE_1RE0RN_0LS1RN_0LK1RA_1LK1RE_0RB0LG_1RB0LW_1RE0LS_1RM1LS_0RA0RE_1RA1RE_1LK1RE_0RM0RN_0LK---_1RA0LK_0LG0LW_1LG1LW_---0RQ_---1RQ_---0LK".
Definition tm0' := TM'_from_str "1LK0RM_1RE1RM_0LH0RA_1LH0RE_1RE0RN_0LS1RN_0LK1RA_1LK1RE_0RB0LG_1RB0LW_1RE0LS_1RM1LS_0RA0RE_1RA1RE_1LK1RE_0RM0RN_0LK---_1RA0LK_0LG0LW_1LG1LW_---1RE_---0LS_---0LK_---1LK".
Definition tm1 := TM'_from_str "1LB0RH_1RC0LE_1RC0RD_1RA---_0LF0LG_0LB1RA_---0LB_0RA---".
Definition tm2 := TM'_from_str "1LB0RH_1RC0LE_1RC0RD_1RA---_0LF0LG_0LB1RA_1RI0LB_0RA---_1RI1RI".
Definition l0 := [1;1;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AKENSGWM".
Definition mp' := mp_from_str "AKENSGWM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (RWL_mod 1001 1000 1000 1 3200 2 2 2 0) 20 20.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM582.


Module TM583.
Definition tm := TM_from_str "1LB---_1RC0RD_1RE0LD_0RA1RB_1LF1LE_0RB0LF".
Definition tm' := TM_from_str "1LB---_1RC0RF_1RD1RC_1LE1LD_0RB0LE_0RA1RB".
Definition tm0 := TM'_from_str "1RJ---_0RF---_0LH---_1LH---_0RJ0RM_1RJ1RM_1RR0RA_1RJ0RF_0RR1RJ_1RR1RJ_1LW0LO_1LT1LO_0RA0RF_1RA1RF_1RJ1RJ_---1RM_0RM1LX_1LW1LT_0LX0LT_1LX1LT_0RE0RJ_1RE0LW_0RJ0LW_0RM1LW".
Definition tm0' := TM'_from_str "1RJ---_0RF---_0LH---_1LH---_0RJ0RU_1RJ1RU_1RN0RA_1RJ0RF_0RN0RJ_1RN1RJ_1LS1RN_1LP1RJ_0RU1LT_1LS1LP_0LT0LP_1LT1LP_0RE0RJ_1RE0LS_0RJ0LS_0RU1LS_0RA0RF_1RA1RF_1RJ1RJ_---1RU".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RWJTXMFA".
Definition mp' := mp_from_str "NSJPTUFA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM583.


Module TM584.
Definition tm := TM_from_str "1RB0RF_0RC0RF_1RD---_1LE0RA_0LB0LE_1LD1RA".
Definition tm' := TM_from_str "1RB0RF_0RC0RF_1RD---_1LE0RB_0LB0LE_1LD1RA".
Definition tm0 := TM'_from_str "0RF0RU_1RF1RU_1RI1LT_1RU0RB_0RI0RU_1RI1RU_0RN1LT_---0RB_0RN---_1RN---_1LS---_1RA---_1LG0RA_1LS1RA_0LT0RF_1LT0RU_0RN0LG_1LT0LS_0LG0LS_1LG1LS_1LT0RB_0RU1RB_0LP1RF_1LP1RU".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1RI1LT_1RU0RB_0RI0RU_1RI1RU_0RN1LT_---0RB_0RN---_1RN---_1LS---_1RE---_1LG0RE_1LS1RE_0LT0RI_1LT0RU_0RN0LG_1LT0LS_0LG0LS_1LG1LS_1LT0RB_0RU1RB_0LP1RF_1LP1RU".
Definition tm1 := TM'_from_str "0RB---_1LC1RF_0LD0LC_0RB1LE_1LD1LC_---0RG_1LE0RH_1RI1RG_1RA1RG".
Definition tm2 := TM'_from_str "0RB1RJ_1LC1RF_0LD0LC_0RB1LE_1LD1LC_---0RG_1LE0RH_1RI1RG_1RA1RG_1RJ1RJ".
Definition l0 := [0;1;0;0;1;0;1;1]%N.
Definition mp := mp_from_str "INSGTAUBF".
Definition mp' := mp_from_str "INSGTEUBF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 true) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM584.


Module TM585.
Definition tm := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_0RB---".
Definition tm' := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_0RE---".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RI0RA_1LT0RI_1LO1RI_0LL1RA_1LL0LL_1RA0LL_1LL0LW_0LT0LO_1LT1LO_1LT1LT_1LO---_0LL0LW_1LL1LW_0RB1LT_1RB1LO_1RF0LL_1RA1LL_0RE---_1RE---_1LT---_0RI---".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1LO0RF_1RI0RA_1LT0RI_1LO1RI_0LL1RA_1LL0LL_1RA0LL_1LL0LX_0LT0LO_1LT1LO_1LT1LT_1LO---_0LL0LX_1LL1LX_0RB1LT_1RB1LO_1RF0LL_1RA1LL_0RQ---_1RQ---_0RB---_1LT---".
Definition tm1 := TM'_from_str "1LB1RF_0LC0LG_1LD1LB_1RE1LC_0RA0RE_1RE0LC_1LD---".
Definition tm2 := TM'_from_str "1LB1RF_0LC0LG_1LD1LB_1RE1LC_0RA0RE_1RE0LC_1LD1RH_1RH1RH".
Definition l0 := [1;1;0;0;1;1;0;0]%N.
Definition mp := mp_from_str "FOLTAIW".
Definition mp' := mp_from_str "FOLTAIX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 22 22.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM585.


Module TM586.
Definition tm := TM_from_str "1RB1RC_0LA---_1RD0RA_1RE0LA_1LF1LE_0RC0LF".
Definition tm' := TM_from_str "1RB1RF_1RC---_1RD0LA_1LE1LD_0RF0LE_1RC0RA".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_1RN1RN_---1RA_1RN---_1RN---_0LC---_1LC---_0RN0RA_1RN1RA_1RR0RF_1RN0RJ_0RR1RN_1RR1RN_1LW0LC_1LT1LC_0RA1LX_1LW1LT_0LX0LT_1LX1LT_0RI0RN_1RI0LW_0RN0LW_0RA1LW".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1RJ1RJ_---1RA_0RJ---_1RJ---_1RN---_1RJ---_0RN1RJ_1RN1RJ_1LS0LC_1LP1LC_0RA1LT_1LS1LP_0LT0LP_1LT1LP_0RU0RJ_1RU0LS_0RJ0LS_0RA1LS_0RJ0RA_1RJ1RA_1RN0RF_1RJ0RV".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "RWNTXAJF".
Definition mp' := mp_from_str "NSJPTAVF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM586.


Module TM587.
Definition tm := TM_from_str "1RB1RF_1RC---_1RD0LA_1LE1LD_0RF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB1RF_1LC---_1RD1RC_1LE1LD_0RF0LE_1RC0RA".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1RJ1RJ_---1RA_0RJ---_1RJ---_1RN---_1RJ---_0RN1RJ_1RN1RJ_1LS0LC_1LP1LC_0RA1LT_1LS1LP_0LT0LP_1LT1LP_0RU0RJ_1RU0LS_0RJ0LS_0RA1LS_0RJ0RA_1RJ1RA_1RN0RF_1RJ0RV".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1RJ1RJ_---1RA_1LP---_1RJ---_0LL---_1LL---_0RN0RJ_1RN1RJ_1LS1RN_1LP1RJ_0RA1LT_1LS1LP_0LT0LP_1LT1LP_0RU0RJ_1RU0LS_0RJ0LS_0RA1LS_0RJ0RA_1RJ1RA_1RN0RF_1RJ0RV".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "NSJPTAVF".
Definition mp' := mp_from_str "NSJPTAVF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM587.


Module TM588.
Definition tm := TM_from_str "1RB1RF_1LC---_1RD1RC_1LE1LD_0RF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB1RC_0LA---_1RD0RA_1RE1RD_1LF1LE_0RC0LF".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1RJ1RJ_---1RA_1LP---_1RJ---_0LL---_1LL---_0RN0RJ_1RN1RJ_1LS1RN_1LP1RJ_0RA1LT_1LS1LP_0LT0LP_1LT1LP_0RU0RJ_1RU0LS_0RJ0LS_0RA1LS_0RJ0RA_1RJ1RA_1RN0RF_1RJ0RV".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1RN1RN_---1RA_1RN---_1RN---_0LC---_1LC---_0RN0RA_1RN1RA_1RR0RF_1RN0RJ_0RR0RN_1RR1RN_1LW1RR_1LT1RN_0RA1LX_1LW1LT_0LX0LT_1LX1LT_0RI0RN_1RI0LW_0RN0LW_0RA1LW".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RC1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "NSJPTAVF".
Definition mp' := mp_from_str "RWNTXAJF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM588.


Module TM589.
Definition tm := TM_from_str "1RB---_1RC0RF_1RD1RC_1LE1LD_0RB0LE_1RA1RB".
Definition tm' := TM_from_str "1RB---_1RC0RF_1RD0LF_1LE1LD_0RB0LE_1RA1RB".
Definition tm0 := TM'_from_str "0RF---_1RF---_1RJ---_1RU---_0RJ0RU_1RJ1RU_1RN0RB_1RJ0RF_0RN0RJ_1RN1RJ_1LS1RN_1LP1RJ_0RU1LT_1LS1LP_0LT0LP_1LT1LP_0RE0RJ_1RE0LS_0RJ0LS_0RU1LS_0RB0RF_1RB1RF_1RF1RJ_---1RU".
Definition tm0' := TM'_from_str "0RF---_1RF---_1RJ---_1RU---_0RJ0RU_1RJ1RU_1RN0RB_1RJ0RF_0RN1RF_1RN1RJ_1LS0LW_1LP1LW_0RU1LT_1LS1LP_0LT0LP_1LT1LP_0RE0RJ_1RE0LS_0RJ0LS_0RU1LS_0RB0RF_1RB1RF_1RF1RJ_---1RU".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RG---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RG1RI_1RI1RI".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "JNSPTUFB".
Definition mp' := mp_from_str "JNSPTUFB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM589.


Module TM590.
Definition tm := TM_from_str "1RB1LA_1RC1LD_1LA0RE_1RF0LA_0LA0RD_---0RD".
Definition tm' := TM_from_str "1RB1LA_1RC1LD_1LA0RE_1RE0LA_1LF0RD_0RD---".
Definition tm0 := TM'_from_str "0RF1LC_1RF1LD_1RJ0LD_1LC1LD_0RJ1RM_1RJ1LC_1LD0LP_1RQ1LP_1LC0RQ_1LD1RQ_0LD1RJ_1LD0RM_0RV1RJ_1RV0LD_---0LC_1RM1LC_1RJ0RM_0LD1RM_0LC0RV_1LC1RJ_---0RM_---1RM_---0RV_---1RJ".
Definition tm0' := TM'_from_str "0RF1LC_1RF1LD_1RJ0LD_1LC1LD_0RJ1RM_1RJ1LC_1LD0LP_1RQ1LP_1LC0RQ_1LD1RQ_0LD1RJ_1LD0RM_0RR1RJ_1RR0LD_---0LC_1RM1LC_1RJ0RM_---1RM_0LX0RR_1LX1RJ_0RM---_1RM---_0RR---_1RJ---".
Definition tm1 := TM'_from_str "1LB1RD_1LC1LB_1RA0LB_1RA0RE_0RF1RA_---1RE".
Definition tm2 := TM'_from_str "1LB1RD_1LC1LB_1RA0LB_1RA0RE_0RF1RA_1RG1RE_1RG1RG".
Definition l0 := [1;1;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JDCQMV".
Definition mp' := mp_from_str "JDCQMR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 5%N l0 (NG 0 1000 1000 1 1 0 0 false) 23 23.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM590.


Module TM591.
Definition tm := TM_from_str "1LB---_1RC1RF_1LD0RD_0RB0LE_1LC0LE_0LF0RA".
Definition tm' := TM_from_str "1LB---_1RC1RF_1LD0RD_0RB0LE_1LC0LE_0RD0RA".
Definition tm0 := TM'_from_str "1RM---_1RA---_0LH---_1LH---_0RJ0RV_1RJ1RV_1LS1RM_1RM1RA_0RV0RM_1LS1RM_0LP0RE_1LP0LL_0RE0LL_1RE0LS_0RJ0LS_0RV1LS_1LP0LL_0LL0LS_0LL0LS_1LL1LS_0LW0RA_1RM1RA_0LW1RM_1LW---".
Definition tm0' := TM'_from_str "1RM---_1RA---_0LH---_1LH---_0RJ0RV_1RJ1RV_1LS1RM_1RM1RA_0RV0RM_1LS1RM_0LP0RE_1LP0LL_0RE0LL_1RE0LS_0RJ0LS_0RV1LS_1LP0LL_0LL0LS_0LL0LS_1LL1LS_0RM0RA_1RM1RA_0RE1RM_0LL---".
Definition tm1 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB---".
Definition tm2 := TM'_from_str "1RB1RH_0RC0LF_0RD0RA_1LE1RB_0LF0LE_1LG0LF_0RA1LE_1RB1RI_1RI1RI".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "VMEJSLPA".
Definition mp' := mp_from_str "VMEJSLPA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM591.


Module TM592.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB0RF_1LA1LD_1LC---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LF_0RB---".
Definition tm0 := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LP_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RU_0RE0RU_1RE1RU_0RI1RE_0LD---_1LH0LD_0LD---_0LD0LP_1LD1LP_1RE---_1RU---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RN0RE_1LS1RE_0LH0RI_1LH0LD_0RI0LD_1RI0LX_0RB0LS_0RN1LS_0RB0RN_1RB1RN_1LS1RE_1RE1RV_0RE0RV_1RE1RV_0RI1RE_0LD---_1LH0LD_0LD---_0LD0LX_1LD1LX_0RE---_1RE---_0RI---_0LD---".
Definition tm1 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF---_1RB---".
Definition tm2 := TM'_from_str "1RB1RI_0RC0LF_0RD0RA_1LE1RB_0LF0LH_1LG0LF_0RA1LE_0LF1RJ_1RB1RJ_1RJ1RJ".
Definition l0 := [0;1;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "NEIBSDHPU".
Definition mp' := mp_from_str "NEIBSDHXV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM592.


Module TM593.
Definition tm := TM_from_str "1LB1RE_0RC---_1LF0LD_1RE1LC_1RF0RE_1LD0LA".
Definition tm' := TM_from_str "1LB1RB_1RC---_1LD0LA_1RF1LE_1LC0LD_1RC0RF".
Definition tm0 := TM'_from_str "1RV0RR_---1RR_0LH1RV_1LH1RQ_0RI---_1RI---_1LP---_1RV---_1LP1RV_1LC0LL_0LX0LO_1LX1LO_0RR1LX_1RR1LO_1RV0LL_1RQ1LL_0RV0RQ_1RV1RQ_1LL0RV_1RV0RQ_1RQ0LH_1LL1RV_0LP0LC_1LP1LC".
Definition tm0' := TM'_from_str "1RJ0RF_---1RF_0LH1RJ_1LH---_0RJ---_1RJ---_1LT---_1RJ---_1RU0LH_1LT1RJ_0LP0LC_1LP1LC_0RV1LL_1RV1LO_1RJ0LT_1RU1LT_1LP1RJ_1LC0LT_0LL0LO_1LL1LO_0RJ0RU_1RJ1RU_1LT0RJ_1RJ0RU".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_0LH1RA_1RA1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "VLOXPQCH".
Definition mp' := mp_from_str "JTOLPUCH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM593.


Module TM594.
Definition tm := TM_from_str "1LB0RC_0RC---_1LF0LD_1RE1LC_1RF0RE_1LD1LA".
Definition tm' := TM_from_str "1LB0RD_1RC---_1LE1LA_1LC0LE_1RF1LD_1RC0RF".
Definition tm0 := TM'_from_str "1RV0RI_---1RI_0LH1LP_1LH1RV_0RI---_1RI---_1LP---_1RV---_1LP1RV_1LD0LL_0LX0LO_1LX1LO_0RR1LX_1RR1LO_1RV0LL_1RQ1LL_0RV0RQ_1RV1RQ_1LL0RV_1RV0RQ_1RQ1LH_1LL1RV_0LP0LD_1LP1LD".
Definition tm0' := TM'_from_str "1RJ0RM_---1RM_0LH1LT_1LH1RJ_0RJ---_1RJ---_1LP---_1RJ---_1RU1LH_1LP1RJ_0LT0LD_1LT1LD_1LT1RJ_1LD0LP_0LL0LS_1LL1LS_0RV1LL_1RV1LS_1RJ0LP_1RU1LP_0RJ0RU_1RJ1RU_1LP0RJ_1RJ0RU".
Definition tm1 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1RA---".
Definition tm2 := TM'_from_str "1LB1RA_1LD1LC_1RA0LB_1LE1LG_1RF1LB_0RA0RF_1LH1RA_1RA1RI_1RI1RI".
Definition l0 := [1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "VLOXPQDH".
Definition mp' := mp_from_str "JPSLTUDH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM594.


Module TM595.
Definition tm := TM_from_str "1LB0RD_0RC1LE_---1LD_1RA1RB_1LF0LE_0RF0LA".
Definition tm' := TM_from_str "1LB0RD_1RC1LE_---0RD_1RA1RB_1LF0LE_0RF0LA".
Definition tm0 := TM'_from_str "1RM0RM_1LT1RM_0LH0RB_1LH0RF_0RI1LX_1RI1LS_---0LT_1RM1LT_---1RM_---1LS_---0LP_---1LP_0RB0RF_1RB1RF_1LT1RI_1RM1LS_0LH0LX_1LC0LS_0LX0LS_1LX1LS_0RU0LH_1RU0RB_0RU0LC_0LH1LC".
Definition tm0' := TM'_from_str "1RM0RM_1LT1RM_0LH0RB_1LH0RF_0RJ1LX_1RJ1LS_---0LT_1RM1LT_---0RM_---1RM_---0RB_---0RF_0RB0RF_1RB1RF_1LT1RJ_1RM1LS_0LH0LX_1LC0LS_0LX0LS_1LX1LS_0RU0LH_1RU0RB_0RU0LC_0LH1LC".
Definition tm1 := TM'_from_str "0RB0RH_1LC1RA_1LD1LG_0LF1LE_0LF0RB_1RA1LC_0LD0LG_1RI1LG_---1RA".
Definition tm2 := TM'_from_str "0RB0RH_1LC1RA_1LD1LG_0LF1LE_0LF0RB_1RA1LC_0LD0LG_1RI1LG_1RJ1RA_1RJ1RJ".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "MBTXCHSFI".
Definition mp' := mp_from_str "MBTXCHSFJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM595.


Module TM596.
Definition tm := TM_from_str "1RB0RA_1LC0RA_0LD0LB_0RE0LB_1RF---_1LA1RE".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_0LD0LB_0RE0LB_1RF---_1LB1RE".
Definition tm0 := TM'_from_str "0RF0RA_1RF1RA_1LG0RF_1RA0RA_1LO0RA_1LG1RA_0LL0RF_1LL0RA_0RV0LL_0LG0RF_0LO0LG_1LO1LG_0RQ0LL_1RQ0RF_0RV0LG_---1LG_0RV---_1RV---_0RA---_1RR---_1RA0RR_0RA1RR_0LD1RV_1LD---".
Definition tm0' := TM'_from_str "0RF0RA_1RF1RA_1LG0RF_1RA0RA_1LO0RA_1LG1RA_0LL0RF_1LL0RA_0RV0LL_0LG0RF_0LO0LG_1LO1LG_0RQ0LL_1RQ0RF_0RV0LG_---1LG_0RV---_1RV---_0RA---_1RR---_1LL0RR_0RA1RR_0LH1RV_1LH---".
Definition tm1 := TM'_from_str "0RB0RA_1LC1RA_0LD0RB_1LE1LC_0RF0LC_0RA1RG_1RF---".
Definition tm2 := TM'_from_str "0RB0RA_1LC1RA_0LD0RB_1LE1LC_0RF0LC_0RA1RG_1RF1RH_1RH1RH".
Definition l0 := [0;0;1;0;1;0;0;1]%N.
Definition mp := mp_from_str "AFGLOVR".
Definition mp' := mp_from_str "AFGLOVR".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM596.


Module TM597.
Definition tm := TM_from_str "1LB1RE_1LC1LF_1LD0LE_1RA0LB_1RD0RA_---1LD".
Definition tm' := TM_from_str "1LB1RE_1LC0LF_1LD0LE_1RA0LB_1RD0RA_---0RB".
Definition tm0 := TM'_from_str "1LL0RR_1LX1RR_0LH1RN_1LH1RA_1LP---_1LS1LP_0LL0LX_1LL1LX_1RR1RB_1LG1LL_0LP0LS_1LP1LS_0RB0LL_1RB0LX_1LX0LG_1RR1LG_0RN0RA_1RN1RA_1RB1LL_0LX0RR_---1RR_---1LG_---0LP_---1LP".
Definition tm0' := TM'_from_str "1LL0RR_1LW1RR_0LH1RN_1LH1RA_1LP---_1LS1LP_0LL0LW_1LL1LW_1RR1RB_1LG1LL_0LP0LS_1LP1LS_0RB0LL_1RB0LW_1LW0LG_1RR1LG_0RN0RA_1RN1RA_1RB1LL_0LW0RR_---0RE_---1RE_---1LP".
Definition tm1 := TM'_from_str "1RB1RI_1RC0LD_1LD1RA_---1LE_1RA1LF_0LG0LD_1LE1LH_1RC1LG_1LG0RA".
Definition tm2 := TM'_from_str "1RB1RI_1RC0LD_1LD1RA_1RJ1LE_1RA1LF_0LG0LD_1LE1LH_1RC1LG_1LG0RA_1RJ1RJ".
Definition l0 := [1;1;1;1;1;0;1;0]%N.
Definition mp := mp_from_str "RNBXPGLSA".
Definition mp' := mp_from_str "RNBWPGLSA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 26 26.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM597.


Module TM598.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RD0RA_0LC1RA_0LF---_1LA1RB".
Definition tm' := TM_from_str "1LB0RD_1LC1LE_1RD0RA_1LB1RA_0LF---_1LA1RB".
Definition tm0 := TM'_from_str "1LL0RM_1LT1RM_0LH1LL_1LH0RB_1RB1LW_0RM---_0LL0LT_1LL1LT_0RN0RA_1RN1RA_1LL1LL_1RB0RM_1LL0RB_1LL1RB_0LK1LT_1LK1RM_0LD---_0RM---_0LW---_1LW---_1LH0RF_0RB1RF_0LD0RM_1LD---".
Definition tm0' := TM'_from_str "1LL0RM_1LT1RM_0LH1LL_1LH0RB_1RB1LW_0RM---_0LL0LT_1LL1LT_0RN0RA_1RN1RA_1LT1LL_1RB0RM_1LL0RB_1LT1RB_0LH1LT_1LH1RM_0LD---_0RM---_0LW---_1LW---_1LH0RF_0RB1RF_0LD0RM_1LD---".
Definition tm1 := TM'_from_str "1LB0RC_1RC0RA_1LD1RA_1LE---_0LF0RA_1LG0RC_1LB1LD".
Definition tm2 := TM'_from_str "1LB0RC_1RC0RA_1LD1RA_1LE1RH_0LF0RA_1LG0RC_1LB1LD_1RH1RH".
Definition l0 := [1;0;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "MLBTWDH".
Definition mp' := mp_from_str "MLBTWDH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM598.


Module TM599.
Definition tm := TM_from_str "1LB0RA_1RC1LC_0RD1LD_1LE0LB_1LF---_1RA1RB".
Definition tm' := TM_from_str "1LB0RA_1RC1LC_0RD1LD_1LE0LB_1LF---_1RA1LD".
Definition tm0 := TM'_from_str "1LG0RA_1LL1RA_0LH1LG_1LH0RA_0RJ1RM_1RJ1LP_1RM0LL_1LG1LL_0RM1LT_1RM1LG_1LX0LP_1RM1LP_1LX1RM_---0LL_0LT0LG_1LT1LG_1RA---_1LP---_0LX---_1LX---_0RB0RF_1RB1RF_1LL1RJ_1RA1LP".
Definition tm0' := TM'_from_str "1LG0RA_1LL1RA_0LH1LG_1LH0RA_0RJ1RM_1RJ1LP_1RM0LL_1LG1LL_0RM1LT_1RM1LG_1LX0LP_1RM1LP_1LX1RM_---0LL_0LT0LG_1LT1LG_1RA---_1LP---_0LX---_1LX---_0RB1LT_1RB1LG_1LL0LP_1RA1LP".
Definition tm1 := TM'_from_str "1LB1RA_1RG1LC_1LF1LD_1RA0LE_1RA1LC_1LB---_1LD0RG".
Definition tm2 := TM'_from_str "1LB1RA_1RG1LC_1LF1LD_1RA0LE_1RA1LC_1LB1RH_1LD0RG_1RH1RH".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "MXPGLTA".
Definition mp' := mp_from_str "MXPGLTA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM599.


Module TM600.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LD---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LF0RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RV_0RA---_1LO---_0LP---_1LP---".
Definition tm0' := TM'_from_str "0RF0RV_1RF1RV_1LO1LO_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_---0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_---1RA_0LW0RF_1LW0RV_1RA---_1LO---_0LL---_1LL---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1LC1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQV".
Definition mp' := mp_from_str "AFOLMQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM600.


Module TM601.
Definition tm := TM_from_str "1RB1RF_1LC0LA_1RE0LD_0RE0LD_0LB0RA_0RD---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LA---".
Definition tm0 := TM'_from_str "0RF0RV_1RF1RV_1LO1RM_1RM---_1RA1LO_1LO1RM_0LL0LC_1LL1LC_0RR0LL_1RR0LO_0LC0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0LC1RA_0LG0RF_1LG0RV_0RM---_1RM---_0RQ---_0LL---".
Definition tm0' := TM'_from_str "0RF0RU_1RF1RU_1LO1RM_1RM---_1RA0RM_1LO1RM_0LL0RQ_1LL0LL_0RR0LL_1RR0LO_0RQ0LO_1RA1LO_0RQ0LL_1RQ0LO_0LL0LO_0RA1LO_0LL0RA_0RQ1RA_0LG0RF_1LG0RU_1RM---_------_0LD---_1LD---".
Definition tm1 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1RE---".
Definition tm2 := TM'_from_str "0RB0RG_1LC1RE_0LD0LC_1RA1LC_0RF0LD_0LD0RA_1RE1RH_1RH1RH".
Definition l0 := [1;0;1;1;0;1;0;0]%N.
Definition mp := mp_from_str "AFOLMQV".
Definition mp' := mp_from_str "AFOLMQU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 27 27.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM601.


Module TM602.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LD1RA_0RF0RB_0LB---".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RA_0RF0RB_0LB---".
Definition tm0 := TM'_from_str "0RF1RR_1RF1LD_1LK0LD_1RR1LD_1RB0RR_1LK1RR_0LL1RU_1LL1RE_0RN1LD_1RN0LK_1LD0LK_1RB1LK_1LP0RB_1LD1RB_0LP1RF_1LP1LD_0RU0RE_1RU1RE_0LL1RB_---0RR_0LL---_1RU---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF1RR_1RF1LD_1LK0LD_1RR1LD_1RB0RR_1LK1RR_0LL1RU_1LL1RE_0RN1LD_1RN0LK_1LD0LK_1RB1LK_1RR0RB_1LD1RB_0LD1RF_1LD1LD_0RU0RE_1RU1RE_0LL1RB_---0RR_0LL---_1RU---_0LG---_1LG---".
Definition tm1 := TM'_from_str "1LB1RD_1LC0LB_1RD1LC_1RG1RE_1RF0RD_1RA1LC_0LH---_---1LB".
Definition tm2 := TM'_from_str "1LB1RD_1LC0LB_1RD1LC_1RG1RE_1RF0RD_1RA1LC_0LH1RI_---1LB_1RI1RI".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "FKDREBUL".
Definition mp' := mp_from_str "FKDREBUL".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 28 28.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM602.


Module TM603.
Definition tm := TM_from_str "1LB0LF_1LC0RC_0RD0LA_1RB1RE_0RC1RE_1RA---".
Definition tm' := TM_from_str "1LB1LF_1LC0RC_0RD0LA_1RB1RE_0RC1RE_0RC---".
Definition tm0 := TM'_from_str "1LL0LH_0LH---_0LH0LW_1LH1LW_0RR0RI_1LC1RI_0LL0RM_1LL0LH_0RM0LH_1RM0LW_0RF0LC_0RR1LC_0RF0RR_1RF1RR_1LC1RI_1RI1RR_0RI0RR_1RI1RR_0RM1RI_0LH1RR_0RB---_1RB---_0LH---".
Definition tm0' := TM'_from_str "1LL0LH_0LH---_0LH0LX_1LH1LX_0RR0RI_1LC1RI_0LL0RM_1LL0LH_0RM0LH_1RM0LX_0RF0LC_0RR1LC_0RF0RR_1RF1RR_1LC1RI_1RI1RR_0RI0RR_1RI1RR_0RM1RI_0LH1RR_0RI---_1RI---_0RM---_0LH---".
Definition tm1 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC---_1RG1RF_0RH0LC_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LE_1LD0LC_0RF1LB_0LC1RI_1RG1RF_0RH0LC_0RA0RF_1RI1RI".
Definition l0 := [0;1;1;0;1;1;0;0]%N.
Definition mp := mp_from_str "FCHLWRIM".
Definition mp' := mp_from_str "FCHLXRIM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM603.


Module TM604.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0LE1RF_0RA---".
Definition tm' := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_0RA---".
Definition tm0 := TM'_from_str "1LG0RI_1LG1RI_0LH0RM_1LH1LG_0RJ1RM_1RJ0LG_1RM0LG_1LG1LG_0RM1LG_1RM1LG_0LH0LH_0RR1LH_0LH0RR_0RM1RR_0LC1RA_1LC1RV_0LS0RV_1RA1RV_0LS1RA_1LS---_0RA---_1RA---_1LG---_0RI---".
Definition tm0' := TM'_from_str "1LG0RI_1LG1RI_0LH0RM_1LH1LG_0RJ1RM_1RJ0LG_1RM0LG_1LG1LG_0RM1LG_1RM1LG_0LH0LH_0RR1LH_0LH0RR_0RM1RR_0LC1RA_1LC1RV_0RA0RV_1RA1RV_1LG1RA_0RI---_0RA---_1RA---_1LG---_0RI---".
Definition tm1 := TM'_from_str "0RB1LD_0LC0RE_1LD1LD_1RB0LD_1RF1RG_1LD0RA_1RF---".
Definition tm2 := TM'_from_str "0RB1LD_0LC0RE_1LD1LD_1RB0LD_1RF1RG_1LD0RA_1RF1RH_1RH1RH".
Definition l0 := [1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "IMHGRAV".
Definition mp' := mp_from_str "IMHGRAV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 29 29.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM604.


Module TM605.
Definition tm := TM_from_str "1LB0RC_1LC0LA_0RD0LB_1RA0RE_1RC0RF_1LD---".
Definition tm' := TM_from_str "1LB0LE_1LC0LA_0RD0LB_1RA0RE_1RC1RF_0RC---".
Definition tm0 := TM'_from_str "1LL0RI_1LC1RI_0LH0RM_1LH0LL_0RQ0LH_1LG0RM_0LL0LC_1LL1LC_0RM0LL_1RM0LC_0RB0LG_0RQ1LG_0RB0RQ_1RB1RQ_1LC0RJ_1RI0RU_0RJ0RU_1RJ1RU_1RM1RI_0LC---_1RI---_0RU---_0LP---_1LP---".
Definition tm0' := TM'_from_str "1LL1RM_1LC1RI_0LH0LS_1LH1LS_0RQ0LH_1LG0LS_0LL0LC_1LL1LC_0RM0LL_1RM0LC_0RB0LG_0RQ1LG_0RB0RQ_1RB1RQ_1LC0RJ_1RI0RV_0RJ0RV_1RJ1RV_1RM1RI_0LC---_0RI---_1RI---_0RM---_0LL---".
Definition tm1 := TM'_from_str "1LB1RI_0LC---_1LD1LB_0RF1LE_0LD---_0RG0RH_1RJ0LB_1RI---_0RJ0LD_0RA0RF".
Definition tm2 := TM'_from_str "1LB1RI_0LC---_1LD1LB_0RF1LE_0LD---_0RG0RH_1RJ0LB_1RI1RK_0RJ0LD_0RA0RF_1RK1RK".
Definition l0 := [0;0;1;0;0;1;0;0]%N.
Definition mp := mp_from_str "BCHLGQJUIM".
Definition mp' := mp_from_str "BCHLGQJVIM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 true) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM605.


Module TM606.
Definition tm := TM_from_str "1LB0RF_1RC0LD_1RA1RC_---0LE_1RA1LE_0RA1RC".
Definition tm' := TM_from_str "1LB0RF_1RC0LD_1RA1RC_---0LE_1RA1LE_1RB1RC".
Definition tm0 := TM'_from_str "1RJ0RU_1LO1RU_0LH0RA_1LH0RJ_0RJ---_1RJ0LS_1RB0LO_1RJ1LO_0RB0RJ_1RB1RJ_1LO1RB_1RU1RJ_---1LO_---0LT_---0LS_---1LS_0RB1RU_1RB1LT_1LO0LT_1RU1LT_0RA0RJ_1RA1RJ_1RJ1RB_0RU1RJ".
Definition tm0' := TM'_from_str "1RJ0RU_1LO1RU_0LH0RF_1LH0RJ_0RJ---_1RJ0LS_1RB0LO_1RJ1LO_0RB0RJ_1RB1RJ_1LO1RB_1RU1RJ_---1LO_---0LT_---0LS_---1LS_0RB1RU_1RB1LT_1LO0LT_1RU1LT_0RF0RJ_1RF1RJ_1RJ1RB_0LS1RJ".
Definition tm1 := TM'_from_str "1LB1RE_---0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF---".
Definition tm2 := TM'_from_str "1LB1RE_1RH0LC_1LB0LD_1RE1LD_0RG0RF_1RA1RF_1RF---_1RH1RH".
Definition l0 := [1;0;1;1;1;1;0;1]%N.
Definition mp := mp_from_str "BOSTUJA".
Definition mp' := mp_from_str "BOSTUJF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 0 2 0 true) 30 30.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM606.


Module TM607.
Definition tm := TM_from_str "1LB1RD_1LC1LE_0RD1LA_1RA0RA_1LF0LB_---1RB".
Definition tm' := TM_from_str "1LB1RD_1LC1LE_0RD1LA_1RA0RA_1LF0LB_---0LB".
Definition tm0 := TM'_from_str "1LL0RN_1LT1RN_0LH1RB_1LH1RA_0RA1LX_1LD1LG_0LL0LT_1LL1LT_0RM1LH_1RM1RA_0RB0LD_0RA1LD_0RB0RA_1RB1RA_1LT1LL_1RN0RN_---0LL_1LG0LT_0LX0LG_1LX1LG_---0RF_---1RF_---1LD_---1LG".
Definition tm0' := TM'_from_str "1LL0RN_1LT1RN_0LH1RB_1LH1RA_0RA1LX_1LD1LG_0LL0LT_1LL1LT_0RM1LH_1RM1RA_0RB0LD_0RA1LD_0RB0RA_1RB1RA_1LT1LL_1RN0RN_---0LL_1LG0LT_0LX0LG_1LX1LG_---0LL_---0LT_---0LG_---1LG".
Definition tm1 := TM'_from_str "1LB0RG_0RA1LC_1LD1RA_1LB1LE_1LI1LF_0LB0LE_1RH1RA_1LE1RG_---1LF".
Definition tm2 := TM'_from_str "1LB0RG_0RA1LC_1LD1RA_1LB1LE_1LI1LF_0LB0LE_1RH1RA_1LE1RG_1RJ1LF_1RJ1RJ".
Definition l0 := [0;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "ALDHTGNBX".
Definition mp' := mp_from_str "ALDHTGNBX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM607.


Module TM608.
Definition tm := TM_from_str "1LB1RC_1LC0RE_1LD1LF_1RE0RB_1LC1RB_0LA---".
Definition tm' := TM_from_str "1LB1RC_1LC0RE_1LD1LF_1RE0RB_0LD1RB_0LA---".
Definition tm0 := TM'_from_str "1LL0RJ_0RF1RJ_0LH0RQ_1LH---_1LP0RQ_1LX1RQ_0LL1LP_1LL0RF_1RF1LC_0RQ---_0LP0LX_1LP1LX_0RR0RE_1RR1RE_1LX1LP_1RF0RQ_1LP0RF_1LX1RF_0LL1LX_1LL1RQ_0LH---_0RQ---_0LC---_1LC---".
Definition tm0' := TM'_from_str "1LL0RJ_0RF1RJ_0LH0RQ_1LH---_1LP0RQ_1LX1RQ_0LL1LP_1LL0RF_1RF1LC_0RQ---_0LP0LX_1LP1LX_0RR0RE_1RR1RE_1LP1LP_1RF0RQ_1LP0RF_1LP1RF_0LO1LX_1LO1RQ_0LH---_0RQ---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1RG_1LC---_0LD0RG_1LE0RA_1LF1LB_1RA0RG_1LF0RA".
Definition tm2 := TM'_from_str "1LB1RG_1LC1RH_0LD0RG_1LE0RA_1LF1LB_1RA0RG_1LF0RA_1RH1RH".
Definition l0 := [0;0;0;0;0;0;0;0]%N.
Definition mp := mp_from_str "FXCHLPQ".
Definition mp' := mp_from_str "FXCHLPQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM608.


Module TM609.
Definition tm := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_0LF0LA_---1RB".
Definition tm' := TM_from_str "1RB1LA_1LC0RD_---1LA_1LE1RD_0LE1LF_1LC0LA".
Definition tm0 := TM'_from_str "0RF1RI_1RF1LD_1LD0LD_1RI1LD_1RI0RI_1LD1RI_0LD1LO_1LD0RJ_1LO0RJ_1LT1RJ_0LP1LT_1LP1RJ_0LO1LW_0LT1LC_0LO0LT_1LO1LT_---1LD_1LD0LD_0LW0LC_1LW1LC_---0RF_---1RF_---1LD_---1RI".
Definition tm0' := TM'_from_str "0RF1RM_1RF1LD_1LD0LD_1RM1LD_---0RM_1LD1RM_0LL1LS_1LL0RN_---1RM_---1LD_---0LD_---1LD_1LS0RN_1LX1RN_0LT1LX_1LT1RN_0LS1LL_0LX1LC_0LS0LX_1LS1LX_---1LD_1LD0LD_0LL0LC_1LL1LC".
Definition tm1 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_---1LD_---0LB".
Definition tm2 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_1RH1LD_---0LB_1RH1RH".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JTCDIWO".
Definition mp' := mp_from_str "NXCDMLS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM609.


Module TM610.
Definition tm := TM_from_str "1RB1LA_1LC0RD_---1LA_1LE1RD_0LE1LF_1LC0LA".
Definition tm' := TM_from_str "1RB1LA_1LC0RD_---1RA_1LE1RD_0LE1LF_1LC0LA".
Definition tm0 := TM'_from_str "0RF1RM_1RF1LD_1LD0LD_1RM1LD_---0RM_1LD1RM_0LL1LS_1LL0RN_---1RM_---1LD_---0LD_---1LD_1LS0RN_1LX1RN_0LT1LX_1LT1RN_0LS1LL_0LX1LC_0LS0LX_1LS1LX_---1LD_1LD0LD_0LL0LC_1LL1LC".
Definition tm0' := TM'_from_str "0RF1RM_1RF1LD_1LD0LD_1RM1LD_---0RM_1LD1RM_0LL1LS_1LL0RN_---0RB_---1RB_---1RF_---1LD_1LS0RN_1LX1RN_0LT1LX_1LT1RN_0LS1LL_0LX1LC_0LS0LX_1LS1LX_---1LD_1LD0LD_0LL0LC_1LL1LC".
Definition tm1 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_---1LD_---0LB".
Definition tm2 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_1RH1LD_---0LB_1RH1RH".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "NXCDMLS".
Definition mp' := mp_from_str "NXCDMLS".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM610.


Module TM611.
Definition tm := TM_from_str "1RB1LA_1LC0RD_---1RA_1LE1RD_0LE1LF_1LC0LA".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---1RA".
Definition tm0 := TM'_from_str "0RF1RM_1RF1LD_1LD0LD_1RM1LD_---0RM_1LD1RM_0LL1LS_1LL0RN_---0RB_---1RB_---1RF_---1LD_1LS0RN_1LX1RN_0LT1LX_1LT1RN_0LS1LL_0LX1LC_0LS0LX_1LS1LX_---1LD_1LD0LD_0LL0LC_1LL1LC".
Definition tm0' := TM'_from_str "0RF1RI_1RF1LD_1LD0LD_1RI1LD_1RI0RI_1LD1RI_0LD1LO_1LD0RJ_1LO0RJ_1LT1RJ_0LP1LT_1LP1RJ_0LO1LX_0LT1LC_0LO0LT_1LO1LT_---1LD_1LD0LD_0LX0LC_1LX1LC_---0RB_---1RB_---1RF_---1LD".
Definition tm1 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_---1LD_---0LB".
Definition tm2 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_1RH1LD_---0LB_1RH1RH".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "NXCDMLS".
Definition mp' := mp_from_str "JTCDIXO".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM611.


Module TM612.
Definition tm := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---1RA".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---0RE".
Definition tm0 := TM'_from_str "0RF1RI_1RF1LD_1LD0LD_1RI1LD_1RI0RI_1LD1RI_0LD1LO_1LD0RJ_1LO0RJ_1LT1RJ_0LP1LT_1LP1RJ_0LO1LX_0LT1LC_0LO0LT_1LO1LT_---1LD_1LD0LD_0LX0LC_1LX1LC_---0RB_---1RB_---1RF_---1LD".
Definition tm0' := TM'_from_str "0RF1RI_1RF1LD_1LD0LD_1RI1LD_1RI0RI_1LD1RI_0LD1LO_1LD0RJ_1LO0RJ_1LT1RJ_0LP1LT_1LP1RJ_0LO1LX_0LT1LC_0LO0LT_1LO1LT_---1LD_1LD0LD_0LX0LC_1LX1LC_---0RQ_---1RQ_------_---1LD".
Definition tm1 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_---1LD_---0LB".
Definition tm2 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_1RH1LD_---0LB_1RH1RH".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JTCDIXO".
Definition mp' := mp_from_str "JTCDIXO".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM612.


Module TM613.
Definition tm := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---0RE".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---1LA".
Definition tm0 := TM'_from_str "0RF1RI_1RF1LD_1LD0LD_1RI1LD_1RI0RI_1LD1RI_0LD1LO_1LD0RJ_1LO0RJ_1LT1RJ_0LP1LT_1LP1RJ_0LO1LX_0LT1LC_0LO0LT_1LO1LT_---1LD_1LD0LD_0LX0LC_1LX1LC_---0RQ_---1RQ_------_---1LD".
Definition tm0' := TM'_from_str "0RF1RI_1RF1LD_1LD0LD_1RI1LD_1RI0RI_1LD1RI_0LD1LO_1LD0RJ_1LO0RJ_1LT1RJ_0LP1LT_1LP1RJ_0LO1LX_0LT1LC_0LO0LT_1LO1LT_---1LD_1LD0LD_0LX0LC_1LX1LC_---1RI_---1LD_---0LD_---1LD".
Definition tm1 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_---1LD_---0LB".
Definition tm2 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LG0RA_1RH1LD_---0LB_1RH1RH".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JTCDIXO".
Definition mp' := mp_from_str "JTCDIXO".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 34 34.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM613.


Module TM614.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_0RF1RA_0LA---".
Definition tm' := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RU_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RU0RB_1RU1RB_1RJ1RF_---1RQ_1RJ---_0RU---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF0RR_1RF1RR_1RJ1RV_---1RA_0RJ---_1RJ---_1LO---_1LL---_0RA1LP_1LO1LL_0LP0LL_1LP1LL_0RQ0RV_1RQ0LO_0RV0LO_0RA1LO_0RV0RA_1RV1RA_1RJ0RF_1RV0RR_0RJ0RV_1RJ1RV_1LO1RJ_1LL1RV".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1RA1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBU".
Definition mp' := mp_from_str "JOVLPARF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM614.


Module TM615.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_0RF1RA_1LB---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_0RF1RA_1LB---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RU_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RU0RB_1RU1RB_1LL1RF_---1RQ_1LL---_1RF---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RU_1RF0RB_0RJ1LL_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RU0RB_1RU1RB_1LL1RF_---1RQ_1LL---_1LS---_0LH---_1LH---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LD---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LD1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBU".
Definition mp' := mp_from_str "JOFLPQBU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM615.


Module TM616.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_0RF1RA_1LB---".
Definition tm' := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RU_1RF0RB_0RJ1LL_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RU0RB_1RU1RB_1LL1RF_---1RQ_1LL---_1LS---_0LH---_1LH---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1LL1RF_---1RQ_1LP---_1LL---_0LL---_1LL---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LD---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LD1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBU".
Definition mp' := mp_from_str "JOFLPQBV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM616.


Module TM617.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1LC---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1LC---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ0RF_1RJ1RF_1LO1RJ_1LL1RF_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1LL1RF_---1RQ_1LP---_1LL---_0LL---_1LL---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RJ0RV_1RF0RB_0RJ1LL_1RJ1RF_1LO0LS_1LL1LS_0RQ1LP_1LO1LL_0LP0LL_1LP1LL_0RA0RF_1RA0LO_0RF0LO_0RQ1LO_0RV0RB_1RV1RB_1LL1RF_---1RQ_1LP---_1LL---_0LL---_1LL---".
Definition tm1 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LD---".
Definition tm2 := TM'_from_str "1LB1LD_0RC0LB_1RA1RC_1LE1LD_0RF1LB_0RH0RG_1RC1RF_1LD1RI_1RI1RI".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JOFLPQBV".
Definition mp' := mp_from_str "JOFLPQBV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 35 35.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM617.


Module TM618.
Definition tm := TM_from_str "1LB1RA_1LC1LE_1RD1LC_1LC0RA_1LF0LC_---0LB".
Definition tm' := TM_from_str "1LB1RA_1LC1LE_1RD1LC_0LD0RA_1LF0LC_---0LB".
Definition tm0 := TM'_from_str "1LL0RB_1LT1RB_0LH1LT_1LH1RB_1RA1LX_1LL1LK_0LL0LT_1LL1LT_0RN1RA_1RN1LL_1LL0LL_1RA1LL_1RA0RA_1LL1RA_0LL1LL_1LL0RB_---1LL_1LG0LL_0LX0LK_1LX1LK_---0LL_---0LT_---0LG_---1LG".
Definition tm0' := TM'_from_str "1LL0RB_1LT1RB_0LH1LT_1LH1RB_1RA1LX_1LL1LK_0LL0LT_1LL1LT_0RN1RA_1RN1LL_1LL0LL_1RA1LL_0LO0RA_1LL1RA_0LO1LL_1LO0RB_---1LL_1LG0LL_0LX0LK_1LX1LK_---0LL_---0LT_---0LG_---1LG".
Definition tm1 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LD0RA_---1LG_0LD0LB".
Definition tm2 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LD0RA_1RH1LG_0LD0LB_1RH1RH".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "BTKLAXG".
Definition mp' := mp_from_str "BTKLAXG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM618.


Module TM619.
Definition tm := TM_from_str "1LB1RA_1LC1LE_1RD1LC_0LD0RA_1LF0LC_---0LB".
Definition tm' := TM_from_str "1LB1RA_0LC1LE_1RD0RA_0RA0LC_1LF0LD_---0LB".
Definition tm0 := TM'_from_str "1LL0RB_1LT1RB_0LH1LT_1LH1RB_1RA1LX_1LL1LK_0LL0LT_1LL1LT_0RN1RA_1RN1LL_1LL0LL_1RA1LL_0LO0RA_1LL1RA_0LO1LL_1LO0RB_---1LL_1LG0LL_0LX0LK_1LX1LK_---0LL_---0LT_---0LG_---1LG".
Definition tm0' := TM'_from_str "1LK0RB_1LT1RB_0LH1LT_1LH1RB_1RA1LX_1LK1LO_0LK0LT_1LK1LT_0RN0RA_1RN1RA_1RA1LK_1LK0RB_0RA1RA_1RA1LK_1LK0LK_0RB1LK_---1LK_1LG0LK_0LX0LO_1LX1LO_---0LK_---0LT_---0LG_---1LG".
Definition tm1 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LD0RA_---1LG_0LD0LB".
Definition tm2 := TM'_from_str "1LB1RA_1LF1LC_1LD0LD_1RE1LD_1LD0RA_1RH1LG_0LD0LB_1RH1RH".
Definition l0 := [1;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "BTKLAXG".
Definition mp' := mp_from_str "BTOKAXG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 37 37.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM619.


Module TM620.
Definition tm := TM_from_str "1LB0LC_1RC0LE_1LE0RD_1RA1RB_0RF1LA_1RB---".
Definition tm' := TM_from_str "1LB0LC_1RC0LE_1LE0RD_1RA1RB_1RF1LA_1LC---".
Definition tm0 := TM'_from_str "1RM0LT_1LS0RB_0LH0LK_1LH1LK_0RJ0RF_1RJ0LD_1LD0LS_1RM1LS_---0RM_1LD1RM_0LT0RB_1LT0RF_0RB0RF_1RB1RF_1LS1RJ_0RB0LD_0RU1LH_1RU1LK_0RF0LD_---1LD_0RF---_1RF---_1RJ---_0LD---".
Definition tm0' := TM'_from_str "1RM0LT_1LS0RB_0LH0LK_1LH1LK_0RJ0RF_1RJ0LD_1LD0LS_1RM1LS_---0RM_1LD1RM_0LT0RB_1LT0RF_0RB0RF_1RB1RF_1LS1RJ_0RB0LD_0RV1LH_1RV1LK_0RF0LD_---1LD_1LT---_0RF---_0LL---_1LL---".
Definition tm1 := TM'_from_str "1LB1RH_1LE1LC_0LD0RI_---1LB_1RH1LF_0RG0LB_1RA0LB_0RI0RG_1LF0RI".
Definition tm2 := TM'_from_str "1LB1RH_1LE1LC_0LD0RI_1RJ1LB_1RH1LF_0RG0LB_1RA0LB_0RI0RG_1LF0RI_1RJ1RJ".
Definition l0 := [1;0;1;1;0;1;0;1]%N.
Definition mp := mp_from_str "JDKTHSFMB".
Definition mp' := mp_from_str "JDKTHSFMB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 40 40.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM620.


Module TM621.
Definition tm := TM_from_str "1RB1LA_1RC0RF_1RD---_0LE1RB_0LA0RD_1LD1RF".
Definition tm' := TM_from_str "1RB0LE_1RC0RF_1RD---_0LA1RB_1RB1LE_1LD1RF".
Definition tm0 := TM'_from_str "0RF1RU_1RF1LD_1RJ0LD_1RU1LD_0RJ0RU_1RJ1RU_1RN1LS_---0RV_0RN---_1RN---_0LC---_1RF---_0LC0RF_0LC1RF_0LS1RJ_1LS1RU_1RJ0RM_0LD1RM_0LC0LC_1LC0RF_1LS0RV_1RU1RV_0LP1RU_1LP1RV".
Definition tm0' := TM'_from_str "0RF1RJ_1RF0LT_1RJ0LS_1RU1LS_0RJ0RU_1RJ1RU_1RN1LC_---0RV_0RN---_1RN---_0LS---_1RF---_1RJ0RF_0LS1RF_0LC1RJ_1LC1RU_0RF1RU_1RF1LT_1RJ0LT_1RU1LT_1LC0RV_1RU1RV_0LP1RU_1LP1RV".
Definition tm1 := TM'_from_str "1RB1RA_1LC0RA_---0LD_1RE0LH_1RF---_0LD1RG_1RE1RB_1RB1LH".
Definition tm2 := TM'_from_str "1RB1RA_1LC0RA_---0LD_1RE0LH_1RF1RI_0LD1RG_1RE1RB_1RB1LH_1RI1RI".
Definition l0 := [1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_str "VUSCJNFD".
Definition mp' := mp_from_str "VUCSJNFT".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 55 55.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM621.


Module TM622.
Definition tm := TM_from_str "1RB1RE_0RC0LB_1LD1RF_0LA0RB_0LB---_0RD1RA".
Definition tm' := TM_from_str "1RB0RE_0RC0LB_1LD1RF_0LA0RB_1LA---_0RD1RA".
Definition tm0 := TM'_from_str "0RF0RR_1RF1RR_1RI0LG_0LG---_0RI1LC_1RI0LG_1LC0LG_0RV1LG_1LC0RV_1LC1RV_0LP1RM_1LP1RB_1RI0RE_0LG1RE_0LC0RI_1LC1LC_1LC---_0LG---_0LG---_1LG---_0RM0RB_1RM1RB_1RI1RF_0RE1RR".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1RI0LG_0LG---_0RI1LC_1RI0LG_1LC0LG_0RV1LG_1LC0RV_1LC1RV_0LP1RM_1LP1RB_1RI0RE_0LG1RE_0LC0RI_1LC1LC_0LG---_------_0LD---_1LD---_0RM0RB_1RM1RB_1RI1RF_0RE1RQ".
Definition tm1 := TM'_from_str "1LB0RD_1RA0LC_1LB0LC_1RE1RG_1RA0RF_0RA1LB_1RH1RI_1RA0LC_0LC---".
Definition tm2 := TM'_from_str "1LB0RD_1RA0LC_1LB0LC_1RE1RG_1RA0RF_0RA1LB_1RH1RI_1RA0LC_0LC1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGVMEBFR".
Definition mp' := mp_from_str "ICGVMEBFQ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM622.


Module TM623.
Definition tm := TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD1RA_0LA---".
Definition tm' := TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RA_0LA0RB".
Definition tm0 := TM'_from_str "0RF1LC_1RF0LG_1RI0LG_1RV1LG_0RI0RV_1RI1RV_1LC0LG_0RR---_1LC0RR_0RV1RR_0LP1RM_1LP1RB_1RI0RE_0LG1RE_0LC0RI_1LC0RV_0RM0RB_1RM1RB_1RI1RF_0RE0LG_1RI---_0LG---_0LC---_1LC---".
Definition tm0' := TM'_from_str "0RF1LC_1RF0LG_1RI0LG_1RN1LG_0RI0RN_1RI1RN_1LC0LG_0RR---_1LC0RR_---1RR_0LP1RU_1LP1RB_1RI---_0LG---_0LC---_1LC---_0RU0RB_1RU1RB_1RI1RF_0RE0LG_1RI0RE_0LG1RE_0LC0RI_1LC0RN".
Definition tm1 := TM'_from_str "1LB0RD_1RA0LC_1LB0LC_1RE1RG_1RA0RF_0RA0RI_1RH0LC_1RA1RI_0LC---".
Definition tm2 := TM'_from_str "1LB0RD_1RA0LC_1LB0LC_1RE1RG_1RA0RF_0RA0RI_1RH0LC_1RA1RI_0LC1RJ_1RJ1RJ".
Definition l0 := [1;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "ICGRMEBFV".
Definition mp' := mp_from_str "ICGRUEBFN".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 15 15.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM623.


Module TM624.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1RB".
Definition tm' := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RB".
Definition tm0 := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV0RA_1RV1RA_1RB1LK_1RF0RJ_0RB0RF_1RB1RF_1LG1LK_1RJ0LG".
Definition tm0' := TM'_from_str "1LK0RJ_1LG1RJ_0LH1RN_1LH1RA_1RR0LK_1LK0LG_0LK0LG_1LK1LG_0RN0RA_1RN1RA_1RR1LK_---0RJ_0RR---_1RR---_1RV---_1RA---_0RV1LH_1RV1RA_1RB0LD_1RF1LD_0RB0RF_1RB1RF_1LG1LK_1RJ0LG".
Definition tm1 := TM'_from_str "1RB1RI_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE---_1LD0LC".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RG_0LD0LC_1RE1LD_1RA1RF_1LD0RG_1RH1RF_1RE1RJ_1LD0LC_1RJ1RJ".
Definition l0 := [1;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_str "VBGKRAJNF".
Definition mp' := mp_from_str "VBGKRAJNF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 18 18.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM624.


Module TM625.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_1RF0RB_1LE---".
Definition tm' := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_1RF0RB_0LC---".
Definition tm0 := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_0LH1RM_---0LH_------_0LH---_0LT---_1LT---".
Definition tm0' := TM'_from_str "1LL1LH_1LC1LD_0LH0LD_1LH1LD_1RM0LH_1LH0LD_0LL0LC_1LL1LC_0RN1LL_1RN1LC_1RR0LH_1RM1LH_0RR0RM_1RR1RM_1RV0RR_1RE0RM_0RV0RE_1RV1RE_0LH1RM_---0LH_1RR---_0LH---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1RB1RH_0LC---_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC".
Definition tm2 := TM'_from_str "1RB1RH_0LC1RI_1LF1LD_0LC0LE_1LC1LE_1RG1LC_0RA0RG_1RG0LC_1RI1RI".
Definition l0 := [1;0;0;0;0;1;1;0]%N.
Definition mp := mp_from_str "RVHCDLME".
Definition mp' := mp_from_str "RVHCDLME".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 19 19.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM625.


Module TM626.
Definition tm := TM_from_str "1LB0RE_1LC1LB_1RD0LA_1RA1RC_0RC1RF_1LD---".
Definition tm' := TM_from_str "1LB0RE_1LC1LB_1RD0LA_1RA1RC_0RC1RF_0LA---".
Definition tm0 := TM'_from_str "1LL0RQ_1LH1RQ_0LH0RI_1LH0RV_1RJ1LL_1LC1LH_0LL0LH_1LL1LH_0RN0LH_1RN0RI_1RB0LC_1RJ1LC_0RB0RJ_1RB1RJ_1LH1RN_1RQ0RI_0RI0RV_1RI1RV_0RN0RI_0LH---_1RQ---_0RI---_0LP---_1LP---".
Definition tm0' := TM'_from_str "1LL0RQ_1LH1RQ_0LH0RI_1LH0RV_1RJ1LL_1LC1LH_0LL0LH_1LL1LH_0RN0LH_1RN0RI_1RB0LC_1RJ1LC_0RB0RJ_1RB1RJ_1LH1RN_1RQ0RI_0RI0RV_1RI1RV_0RN0RI_0LH---_0LH---_0RI---_0LC---_1LC---".
Definition tm1 := TM'_from_str "1LB1RH_1LC1LB_1RD1LF_1RG0RE_0RG0LB_0LB0RE_1RA1RD_0RE0RI_0RE---".
Definition tm2 := TM'_from_str "1LB1RH_1LC1LB_1RD1LF_1RG0RE_0RG0LB_0LB0RE_1RA1RD_0RE0RI_0RE1RJ_1RJ1RJ".
Definition l0 := [1;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "BHLJICNQV".
Definition mp' := mp_from_str "BHLJICNQV".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM626.


Module TM627.
Definition tm := TM_from_str "1LB0RA_1LC1LA_1LD1LF_1RE---_1LA0RF_0LB1RE".
Definition tm' := TM_from_str "1LB0RA_1LC1LA_1LD1LE_1RC---_0LB1RF_1LA0RE".
Definition tm0 := TM'_from_str "1LL0RA_1LD1RA_0LH1LL_1LH0RA_1LP1LH_1LX0RA_0LL0LD_1LL1LD_1RU1LG_---1RU_0LP0LX_1LP1LX_0RR---_1RR---_0RA---_1RU---_1LH0RU_0RA1RU_0LD0LL_1LD0RR_0LL0RR_0LD1RR_0LG0RA_1LG1RU".
Definition tm0' := TM'_from_str "1LL0RA_1LD1RA_0LH1LL_1LH0RA_1LP1LH_1LT0RA_0LL0LD_1LL1LD_1RQ1LG_---1RQ_0LP0LT_1LP1LT_0RJ---_1RJ---_------_1RQ---_0LL0RV_0LD1RV_0LG0RA_1LG1RQ_1LH0RQ_0RA1RQ_0LD0LL_1LD0RV".
Definition tm1 := TM'_from_str "0LB0RH_1LG1LC_1LD1RA_0LB0LE_1LF0RI_1LB1LE_1RA---_0RI1RA_1LB0RI".
Definition tm2 := TM'_from_str "0LB0RH_1LG1LC_1LD1RA_0LB0LE_1LF0RI_1LB1LE_1RA1RJ_0RI1RA_1LB0RI_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;0;1]%N.
Definition mp := mp_from_str "ULXGDHPRA".
Definition mp' := mp_from_str "QLTGDHPVA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM627.


Module TM628.
Definition tm := TM_from_str "1LB0RA_1LC1LA_1LD1LE_1RC---_0LB1RF_0RA0RE".
Definition tm' := TM_from_str "1LB0RA_1LC1LA_1LD1LF_1RE---_0RA0RF_0LB1RE".
Definition tm0 := TM'_from_str "1LL0RA_1LD1RA_0LH1LL_1LH0RA_1LP1LH_1LT0RA_0LL0LD_1LL1LD_1RQ1LG_---1RQ_0LP0LT_1LP1LT_0RJ---_1RJ---_------_1RQ---_0LL0RV_0LD1RV_0LG1RA_1LG1RQ_0RA0RQ_1RA1RQ_1LL0LL_0RA0RV".
Definition tm0' := TM'_from_str "1LL0RA_1LD1RA_0LH1LL_1LH0RA_1LP1LH_1LX0RA_0LL0LD_1LL1LD_1RU1LG_---1RU_0LP0LX_1LP1LX_0RR---_1RR---_1RA---_1RU---_0RA0RU_1RA1RU_1LL0LL_0RA0RR_0LL0RR_0LD1RR_0LG1RA_1LG1RU".
Definition tm1 := TM'_from_str "0LB0RH_1LG1LC_1LD1RA_0LB0LE_1LI0RF_1LB0RF_1RA---_1RF1RA_1LB1LE".
Definition tm2 := TM'_from_str "0LB0RH_1LG1LC_1LD1RA_0LB0LE_1LI0RF_1LB0RF_1RA1RJ_1RF1RA_1LB1LE_1RJ1RJ".
Definition l0 := [1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_str "QLTGDAPVH".
Definition mp' := mp_from_str "ULXGDAPRH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 24 24.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM628.


Module TM629.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RD---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RD---".
Definition tm0 := TM'_from_str "0RF1RM_1RF1RB_1LK0LS_1LH1LS_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RM1RB_---1RQ_0RM---_1RM---_0RB---_0RQ---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RM1RB_---1RQ_0RM---_1RM---_0RB---_0RQ---".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RI---_0RA0RF".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RI1RJ_0RA0RF_1RJ1RJ".
Definition l0 := [0;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_str "BFKHLQNVM".
Definition mp' := mp_from_str "BFKHLQNVM".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM629.


Module TM630.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RC---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RC---".
Definition tm0 := TM'_from_str "0RF1RJ_1RF1RB_1LK0LS_1LH1LS_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RJ1RB_---1RQ_0RJ---_1RJ---_1RM---_0LK---".
Definition tm0' := TM'_from_str "0RF0RB_1RF1RB_1LK1RF_1LH1RB_0RQ1LL_1LK1LH_0LL0LH_1LL1LH_0RM0RB_1RM0LK_0RB0LK_0RQ1LK_0RB0RQ_1RB1RQ_1RF0RV_1RB0RN_0RV0RN_1RV1RN_1RJ1RB_---1RQ_0RJ---_1RJ---_1RM---_0LK---".
Definition tm1 := TM'_from_str "0RB0RG_1RC1RB_1LD1LE_0RB0LD_1LF1LE_0RG1LD_0RI0RH_1RB1RG_1RJ---_1RA0LD".
Definition tm2 := TM'_from_str "0RB0RG_1RC1RB_1LD1LE_0RB0LD_1LF1LE_0RG1LD_0RI0RH_1RB1RG_1RJ1RK_1RA0LD_1RK1RK".
Definition l0 := [0;0;1;0;1;0;1;1]%N.
Definition mp := mp_from_str "MBFKHLQNVJ".
Definition mp' := mp_from_str "MBFKHLQNVJ".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 25 25.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM630.


Module TM631.
Definition tm := TM_from_str "1LB0LD_1RC1RF_1RE1RD_0RB1LA_1LC---_1RB0LF".
Definition tm' := TM_from_str "1LB0LD_1RC1RF_1RE1RD_0RB1LA_1LA---_1RB0LF".
Definition tm0 := TM'_from_str "1RN0RJ_0LW0LD_0LH0LO_1LH1LO_0RJ0RV_1RJ1RV_1RR1RF_1RN0LW_0RR0RN_1RR1RN_1LO1RE_---1LO_0RE1LH_1RE1LO_0RJ0LD_0RV1LD_------_1LO---_0LL---_1LL---_0RF1RJ_1RF0LW_1RJ0LW_1RV1LW".
Definition tm0' := TM'_from_str "1RN0RJ_0LW0LD_0LH0LO_1LH1LO_0RJ0RV_1RJ1RV_1RR1RF_1RN0LW_0RR0RN_1RR1RN_1LO1RE_---1LO_0RE1LH_1RE1LO_0RJ0LD_0RV1LD_1LH---_1LO---_0LD---_1LD---_0RF1RJ_1RF0LW_1RJ0LW_1RV1LW".
Definition tm1 := TM'_from_str "1RB1RG_1LC---_0RA0LD_1LE1LC_1RG0LF_1RA0LF_1RH1LC_0RA0RI_1RJ0LF_1RA1RI".
Definition tm2 := TM'_from_str "1RB1RG_1LC1RK_0RA0LD_1LE1LC_1RG0LF_1RA0LF_1RH1LC_0RA0RI_1RJ0LF_1RA1RI_1RK1RK".
Definition l0 := [0;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_str "JRODHWNEVF".
Definition mp' := mp_from_str "JRODHWNEVF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 false) 50 50.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM631.


Module TM632.
Definition tm := TM_from_str "1RB1RC_0RC---_1RD0RA_1RE0LA_1LF1LE_0RC0LF".
Definition tm' := TM_from_str "1RB1RC_0RC---_1RD0RA_1RE1RD_1LF1LE_0RC0LF".
Definition tm0 := TM'_from_str "0RF0RJ_1RF1RJ_1RI1RN_---1RA_0RI---_1RI---_0RN---_0RA---_0RN0RA_1RN1RA_1RR0RF_1RN0RJ_0RR1RI_1RR1RN_1LW0LC_1LT1LC_0RA1LX_1LW1LT_0LX0LT_1LX1LT_0RI0RN_1RI0LW_0RN0LW_0RA1LW".
Definition tm0' := TM'_from_str "0RF0RJ_1RF1RJ_1RI1RN_---1RA_0RI---_1RI---_0RN---_0RA---_0RN0RA_1RN1RA_1RR0RF_1RN0RJ_0RR0RN_1RR1RN_1LW1RR_1LT1RN_0RA1LX_1LW1LT_0LX0LT_1LX1LT_0RI0RN_1RI0LW_0RN0LW_0RA1LW".
Definition tm1 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RI---_0RA0RF".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LD_0RA0LC_1LE1LD_0RF1LC_0RH0RG_1RA1RF_1RI1RJ_0RA0RF_1RJ1RJ".
Definition l0 := [0;0;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "NRWTXAJFI".
Definition mp' := mp_from_str "NRWTXAJFI".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 59 59.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM632.


Module TM633.
Definition tm := TM_from_str "1LB---_0RC1LF_0RE1RD_0RE1RC_1LA1RB_0LB0LA".
Definition tm' := TM_from_str "1LB---_0RC1LF_0RE1RD_0LD1RC_1LA1RB_0LB0LA".
Definition tm0 := TM'_from_str "0RN---_1LX---_0LH---_1LH---_0RI1LG_1RI1LC_0RQ0LX_0RN1LX_0RQ0RN_1RQ1RN_1LH1RQ_0RF1RJ_0RQ0RJ_1RQ1RJ_1LH1RQ_0RF1RN_1LH0RF_---1RF_0LD1RI_1LD1LC_0RQ0LH_0LX---_0LG0LC_1LG1LC".
Definition tm0' := TM'_from_str "0RN---_1LX---_0LH---_1LH---_0RI1LG_1RI1LC_0RQ0LX_0RN1LX_0RQ0RN_1RQ1RN_1LH1RQ_0RF1RJ_0LO0RJ_1RQ1RJ_0LO1RQ_1LO1RN_1LH0RF_---1RF_0LD1RI_1LD1LC_0RQ0LH_0LX---_0LG0LC_1LG1LC".
Definition tm1 := TM'_from_str "1RB1LH_0RC0RE_1LD0RA_0RE1LG_1RC1RF_1RC1RE_1LI1LH_0LD---_0RC0LG".
Definition tm2 := TM'_from_str "1RB1LH_0RC0RE_1LD0RA_0RE1LG_1RC1RF_1RC1RE_1LI1LH_0LD1RJ_0RC0LG_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;1;0]%N.
Definition mp := mp_from_str "FIQHNJXCG".
Definition mp' := mp_from_str "FIQHNJXCG".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM633.


Module TM634.
Definition tm := TM_from_str "1LB0LE_1LC1LF_1RD1LA_1RB1RD_1LA1RB_---0RE".
Definition tm' := TM_from_str "1LB0LE_1LC0LF_1RD1LA_1RB1RD_1LA1RB_---0RD".
Definition tm0 := TM'_from_str "1LL0LD_1LX1LD_0LH0LS_1LH1LS_1RN---_1LD0RF_0LL0LX_1LL1LX_0RN1LH_1RN1LS_1RF0LD_1RN1LD_0RF0RN_1RF1RN_1LD1RF_0RF1RN_1LH0RF_1LS1RF_0LD1LD_1LD0RF_---0RQ_---1RQ_---1LH_---0RF".
Definition tm0' := TM'_from_str "1LL0LD_1LW1LD_0LH0LS_1LH1LS_1RN---_1LD0RF_0LL0LW_1LL1LW_0RN1LH_1RN1LS_1RF0LD_1RN1LD_0RF0RN_1RF1RN_1LD1RF_0RF1RN_1LH0RF_1LS1RF_0LD1LD_1LD0RF_---0RM_---1RM_---0RF_---0RN".
Definition tm1 := TM'_from_str "1LB0RA_1LD1LC_0LB1LB_1LE1LG_1RF1LB_1RA1RF_---0RA".
Definition tm2 := TM'_from_str "1LB0RA_1LD1LC_0LB1LB_1LE1LG_1RF1LB_1RA1RF_1RH0RA_1RH1RH".
Definition l0 := [1;1;1;1;1;1;1;1;0;0;0;1;1;1;1;1]%N.
Definition mp := mp_from_str "FDSHLNX".
Definition mp' := mp_from_str "FDSHLNW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 62 62.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM634.


Module TM635.
Definition tm := TM_from_str "1LB0LF_1RC1LD_1RA1RC_1LA0LE_1LD1RA_---0RC".
Definition tm' := TM_from_str "1LB1LF_1RC1LD_1RA1RC_1LA0LE_1LD1RA_---0RE".
Definition tm0 := TM'_from_str "1RJ---_1LP0RB_0LH0LW_1LH1LW_0RJ1LD_1RJ1LS_1RB0LP_1RJ1LP_0RB0RJ_1RB1RJ_1LP1RB_0RB1RJ_1LH0LP_1LW1LP_0LD0LS_1LD1LS_1LD0RB_1LS1RB_0LP1LP_1LP0RB_---0RI_---1RI_---0RB_---0RJ".
Definition tm0' := TM'_from_str "1RJ---_1LP0RB_0LH0LX_1LH1LX_0RJ1LD_1RJ1LS_1RB0LP_1RJ1LP_0RB0RJ_1RB1RJ_1LP1RB_0RB1RJ_1LH0LP_1LX1LP_0LD0LS_1LD1LS_1LD0RB_1LS1RB_0LP1LP_1LP0RB_---0RQ_---1RQ_---1LD_---0RB".
Definition tm1 := TM'_from_str "1RB1RA_1LC0RB_1LE1LD_0LC1LC_1LF1LG_1RA1LC_---0RB".
Definition tm2 := TM'_from_str "1RB1RA_1LC0RB_1LE1LD_0LC1LC_1LF1LG_1RA1LC_1RH0RB_1RH1RH".
Definition l0 := [1;1;1;1;0;1;1;1;1;0;0;0;1;1;1;1]%N.
Definition mp := mp_from_str "JBPSDHW".
Definition mp' := mp_from_str "JBPSDHX".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 6%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM635.


Module TM636.
Definition tm := TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LB---".
Definition tm' := TM_from_str "1RB0RE_0LB1RC_1LD1RA_1LA0LE_0RC0RF_0LC---".
Definition tm0 := TM'_from_str "0RF0RM_1RF1RM_1LO0RQ_1RR0RU_1LD0RR_1LO1RR_0LL1LO_1LL1RB_1RR1LD_0RU0LL_0LD0LO_1LD1LO_0RQ0RU_1RQ1RU_1LD0LL_0RB---_1LD0RB_1LO1RB_0LL1RF_1LL1RM_0LL---_1LO---_0LG---_1LG---".
Definition tm0' := TM'_from_str "0RF0RQ_1RF1RQ_1LS0RI_1RJ0RU_0LG0RJ_1LS1RJ_0LG1LS_1LG1RB_1LD0RB_1LS1RB_0LP1RF_1LP1RQ_1RJ1LD_0RU0LP_0LD0LS_1LD1LS_0RI0RU_1RI1RU_1LD0LP_0RB---_0LP---_1RF---_0LK---_1LK---".
Definition tm1 := TM'_from_str "1LB1RE_1LD0LC_1LD1LB_1RA0RI_1RH1RF_0RG0RI_1LD0RE_1LB1RA_0LC---".
Definition tm2 := TM'_from_str "1LB1RE_1LD0LC_1LD1LB_1RA0RI_1RH1RF_0RG0RI_1LD0RE_1LB1RA_0LC1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "ROLDBMQFU".
Definition mp' := mp_from_str "JSPDBQIFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM636.


Module TM637.
Definition tm := TM_from_str "1RB0RE_0LB1RC_1LD1RA_1LA0LE_0RC0RF_0LC---".
Definition tm' := TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LE---".
Definition tm0 := TM'_from_str "0RF0RQ_1RF1RQ_1LS0RI_1RJ0RU_0LG0RJ_1LS1RJ_0LG1LS_1LG1RB_1LD0RB_1LS1RB_0LP1RF_1LP1RQ_1RJ1LD_0RU0LP_0LD0LS_1LD1LS_0RI0RU_1RI1RU_1LD0LP_0RB---_0LP---_1RF---_0LK---_1LK---".
Definition tm0' := TM'_from_str "0RF0RM_1RF1RM_1LO0RQ_1RR0RU_1LD0RR_1LO1RR_0LL1LO_1LL1RB_1RR1LD_0RU0LL_0LD0LO_1LD1LO_0RQ0RU_1RQ1RU_1LD0LL_0RB---_1LD0RB_1LO1RB_0LL1RF_1LL1RM_0LL---_1RF---_0LS---_1LS---".
Definition tm1 := TM'_from_str "1LB1RE_1LD0LC_1LD1LB_1RA0RI_1RH1RF_0RG0RI_1LD0RE_1LB1RA_0LC---".
Definition tm2 := TM'_from_str "1LB1RE_1LD0LC_1LD1LB_1RA0RI_1RH1RF_0RG0RI_1LD0RE_1LB1RA_0LC1RJ_1RJ1RJ".
Definition l0 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "JSPDBQIFU".
Definition mp' := mp_from_str "ROLDBMQFU".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 71 71.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM637.


Module TM638.
Definition tm := TM_from_str "1LB0LA_1RC1LE_1RD0RC_0RE0LF_1LA1RD_---1LD".
Definition tm' := TM_from_str "1LB0LA_1RC1LE_1LD0RC_0RE0LF_1LA1RD_---1LD".
Definition tm0 := TM'_from_str "1RI0LH_1LT0LC_0LH0LC_1LH1LC_0RJ1LD_1RJ0LP_1RN0LT_1RI1LT_0RN0RI_1RN1RI_1RQ0RN_0LP0RI_0RQ---_1RQ0LP_1LH0LW_0RN1LW_1LH0RN_1LC1RN_0LD1RQ_1LD0LP_---0RN_---1LW_---0LP_---1LP".
Definition tm0' := TM'_from_str "1RI0LH_1LT0LC_0LH0LC_1LH1LC_0RJ1LD_1RJ0LP_1LW0LT_1RI1LT_0RN0RI_1LW1RI_0LP0RN_1LP0RI_0RQ---_1RQ0LP_1LH0LW_0RN1LW_1LH0RN_1LC1RN_0LD1RQ_1LD0LP_---0RN_---1LW_---0LP_---1LP".
Definition tm1 := TM'_from_str "1LB0RF_1RE1LC_1LD0LG_1LB1LH_0RF0RE_1RA0LG_0RF1LI_0LB0LH_---0LG".
Definition tm2 := TM'_from_str "1LB0RF_1RE1LC_1LD0LG_1LB1LH_0RF0RE_1RA0LG_0RF1LI_0LB0LH_1RJ0LG_1RJ1RJ".
Definition l0 := [1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_str "QHTDINPCW".
Definition mp' := mp_from_str "QHTDINPCW".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 115 115.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM638.


Module TM639.
Definition tm := TM_from_str "1RB1LA_0RC1LE_1LC0RD_1LE1RD_1LF0LA_1LB---".
Definition tm' := TM_from_str "1LB0RE_1LC0LF_1LD---_0RA1LB_1LB1RE_1RD1LF".
Definition tm0 := TM'_from_str "0RF1LC_1RF1LD_1RI0LD_1LC1LD_0RI1LX_1RI1LC_1LL0LT_0RM1LT_1LL0RM_0RN1RM_0LL1LX_1LL0RN_1LX0RN_1LC1RN_0LT1LC_1LT1RN_1LH1RI_---0LD_0LX0LC_1LX1LC_0RM---_1LT---_0LH---_1LH---".
Definition tm0' := TM'_from_str "1LL0RQ_1LW1RQ_0LH1LL_1LH0RR_1LP1RA_---0LX_0LL0LW_1LL1LW_0RQ---_1LH---_0LP---_1LP---_0RA1LL_1RA1LW_1LL0LH_0RQ1LH_1LL0RR_1LW1RR_0LH1LW_1LH1RR_0RN1LW_1RN1LX_1RA0LX_1LW1LX".
Definition tm1 := TM'_from_str "1LB1RA_1RD0LC_1LB1LC_---0RE_1LF0RA_1LG---_0RE1LH_1LF1LB".
Definition tm2 := TM'_from_str "1LB1RA_1RD0LC_1LB1LC_---0RE_1LF0RA_1LG1RI_0RE1LH_1LF1LB_1RI1RI".
Definition l0 := [1;1;0;1;0;0;1;1;1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "NCDIMXHT".
Definition mp' := mp_from_str "RWXAQLPH".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 200 200.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM639.


Module TM640.
Definition tm := TM_from_str "1RB1LA_1RC0RE_1LD0LF_---1RA_1RF1RE_1LC0LA".
Definition tm' := TM_from_str "1RB1LA_1RC0RE_1LD0LF_---1LA_1RF1RE_1LC0LA".
Definition tm0 := TM'_from_str "0RF1RQ_1RF1LD_1RJ0LD_1RQ1LD_0RJ0RQ_1RJ1RQ_1LD0RV_0LC0RR_---0LL_1LD0LC_0LP0LW_1LP1LW_---0RB_---1RB_---1RF_---1LD_0RV0RR_1RV1RR_1LW1RV_0LD1RR_1LP1RJ_1LW0LD_0LL0LC_1LL1LC".
Definition tm0' := TM'_from_str "0RF1RQ_1RF1LD_1RJ0LD_1RQ1LD_0RJ0RQ_1RJ1RQ_1LD0RV_0LC0RR_---0LL_1LD0LC_0LP0LW_1LP1LW_---1RQ_---1LD_---0LD_---1LD_0RV0RR_1RV1RR_1LW1RV_0LD1RR_1LP1RJ_1LW0LD_0LL0LC_1LL1LC".
Definition tm1 := TM'_from_str "1LB0LD_0LG0LC_1RH0LD_1RE1LD_0RA0RF_1RA1RF_1LI1LB_1LD---".
Definition tm2 := TM'_from_str "1LB0LD_0LG0LC_1RH0LD_1RE1LD_0RA0RF_1RA1RF_1LI1LB_1LD---_1RJ---_1RJ1RJ".
Definition l0 := [1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_str "VWCDQRLJP".
Definition mp' := mp_from_str "VWCDQRLJP".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 201 201.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM640.


