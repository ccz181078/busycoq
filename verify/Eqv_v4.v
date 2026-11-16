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

Fixpoint nth_error_N{A}(x:list A)(n:N):option A :=
match x with
| [] => None
| x0::x1 =>
  match n with
  | N0 => Some x0
  | _ => nth_error_N x1 (N.pred n)
  end
end.

Definition TM'_from_str(x:string):TMinf.TM :=
  fun '(q,s)=>
  TM'_from_str_rec x (S (String.length x)) q s.

Definition TM'_from_list x:TMinf.TM :=
  fun '(q,s)=>
  match nth_error_N x q with
  | Some x0 =>
    match nth_error_N x0 s with
    | Some x1 => x1
    | _ => None
    end
  | _ => None
  end.

Definition mp_from_list (x:list BBinf.Q)(n:BBinf.Q):BBinf.Q :=
  match nth_error_N x n with
  | Some x0 => x0
  | _ => N0
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
    [ | solve_evstep 16 ];
    solve_cert cert
  | ];
  rewrite <-(TMinf.halts_evstep_iff _ TMinf.c0) in I2 by solve_evstep T.

Ltac solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' qn l0 cert T T' :=
  solve_v1 tm tm0 3;
  solve_v1 tm' tm0' 3;
  solve_v2 tm0 tm1 tm2 mp qn (const 0<*(rev l0),0,const 0)%N l0 cert T;
  solve_v2 tm0' tm1 tm2 mp' qn (const 0<*(rev l0),0,const 0)%N l0 cert T'.


Module TM1.
Definition tm := TM_from_str "1RB0LA_1RC0RE_0RD---_1LA0LE_1LD1RF_1RA1LB".
Definition tm' := TM_from_str "1RB0LA_1RC0RE_0RD---_1LA1LF_1LD1RF_1RA1LB".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,35)];[Some(0,R,19);Some(0,R,54)];[Some(0,R,21);Some(0,R,39)];[Some(0,R,23);Some(1,R,70)];[Some(1,R,17);Some(1,R,35)];[Some(1,R,19);Some(1,R,54)];[Some(1,R,21);Some(1,R,39)];[Some(1,R,23);Some(0,L,8)];[Some(1,R,70);Some(0,L,8)];[Some(0,L,14);Some(0,L,10)];[None;Some(0,L,12)];[Some(1,R,3);Some(0,L,14)];[Some(0,L,8);Some(1,L,8)];[Some(1,L,14);Some(1,L,10)];[None;Some(1,L,12)];[Some(1,R,81);Some(1,L,14)];[Some(0,R,33);Some(0,R,64)];[Some(0,R,35);Some(0,R,66)];[Some(0,R,37);Some(0,R,68)];[Some(0,R,39);Some(0,R,70)];[Some(1,R,33);Some(1,R,64)];[Some(1,R,35);Some(1,R,66)];[Some(1,R,37);Some(1,R,68)];[Some(1,R,39);Some(1,R,70)];[Some(1,L,12);Some(0,L,11)];[None;Some(0,R,23)];[Some(0,L,74);Some(0,L,15)];[None;Some(0,R,3)];[Some(1,R,85);Some(1,L,11)];[None;Some(1,R,70)];[Some(1,L,74);Some(1,L,15)];[None;Some(0,R,81)];[Some(0,R,48);None];[Some(0,R,50);None];[Some(0,R,52);None];[Some(0,R,54);None];[Some(1,R,48);None];[Some(1,R,50);None];[Some(1,R,52);None];[Some(1,R,54);None];[Some(0,L,14);None];[Some(0,L,57);None];[Some(1,R,3);None];[Some(0,L,61);None];[Some(1,L,14);None];[Some(1,L,57);None];[Some(1,R,81);None];[Some(1,L,61);None];[Some(0,R,66);Some(1,R,3)];[None;Some(0,R,3)];[Some(0,R,70);Some(0,L,61)];[Some(0,L,8);Some(0,R,7)];[Some(1,R,66);Some(0,L,14)];[None;Some(1,R,3)];[Some(1,R,70);Some(0,L,8)];[Some(1,L,8);Some(1,R,7)];[Some(0,L,9);Some(0,L,72)];[Some(0,L,11);Some(0,L,74)];[Some(0,L,13);Some(0,L,76)];[Some(0,L,15);Some(0,L,78)];[Some(1,L,9);Some(1,L,72)];[Some(1,L,11);Some(1,L,74)];[Some(1,L,13);Some(1,L,76)];[Some(1,L,15);Some(1,L,78)];[Some(0,R,85);Some(0,R,81)];[Some(1,L,11);Some(0,R,83)];[None;Some(0,R,85)];[Some(1,R,70);Some(0,R,87)];[Some(1,R,85);Some(1,R,81)];[Some(1,L,74);Some(1,R,83)];[Some(1,L,12);Some(1,R,85)];[Some(0,L,8);Some(1,R,87)];[Some(0,L,57);Some(1,R,39)];[Some(0,L,59);Some(0,R,23)];[Some(0,L,61);Some(0,L,8)];[Some(0,L,63);Some(0,R,3)];[Some(1,L,57);Some(1,R,70)];[Some(1,L,59);Some(1,R,70)];[Some(1,L,61);Some(1,L,8)];[Some(1,L,63);Some(0,R,81)];[Some(0,R,1);None];[Some(0,R,3);Some(0,R,81)];[Some(0,R,5);None];[Some(0,R,7);Some(0,R,85)];[Some(1,R,1);None];[Some(1,R,3);Some(1,R,81)];[Some(1,R,5);None];[Some(1,R,7);Some(1,R,85)];[Some(1,R,54);Some(0,L,25)];[Some(0,L,8);Some(0,L,27)];[Some(1,L,12);Some(0,L,29)];[Some(0,L,12);Some(0,L,31)];[None;Some(1,L,25)];[Some(1,L,8);Some(1,L,27)];[Some(1,R,85);Some(1,L,29)];[Some(1,L,12);Some(1,L,31)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,35)];[Some(0,R,19);Some(0,R,54)];[Some(0,R,21);Some(0,R,39)];[Some(0,R,23);Some(1,R,70)];[Some(1,R,17);Some(1,R,35)];[Some(1,R,19);Some(1,R,54)];[Some(1,R,21);Some(1,R,39)];[Some(1,R,23);Some(0,L,8)];[Some(1,R,70);Some(0,L,8)];[Some(0,L,14);Some(0,L,10)];[None;Some(0,L,12)];[Some(1,R,3);Some(0,L,14)];[Some(0,L,8);Some(1,L,8)];[Some(1,L,14);Some(1,L,10)];[None;Some(1,L,12)];[Some(1,R,81);Some(1,L,14)];[Some(0,R,33);Some(0,R,64)];[Some(0,R,35);Some(0,R,66)];[Some(0,R,37);Some(0,R,68)];[Some(0,R,39);Some(0,R,70)];[Some(1,R,33);Some(1,R,64)];[Some(1,R,35);Some(1,R,66)];[Some(1,R,37);Some(1,R,68)];[Some(1,R,39);Some(1,R,70)];[Some(1,L,12);Some(0,L,11)];[None;Some(0,R,23)];[Some(0,L,8);Some(0,L,15)];[None;Some(0,R,3)];[Some(1,R,85);Some(1,L,11)];[None;Some(1,R,70)];[Some(1,L,8);Some(1,L,15)];[None;Some(0,R,81)];[Some(0,R,48);None];[Some(0,R,50);None];[Some(0,R,52);None];[Some(0,R,54);None];[Some(1,R,48);None];[Some(1,R,50);None];[Some(1,R,52);None];[Some(1,R,54);None];[Some(0,L,14);None];[Some(0,L,8);None];[Some(1,R,3);None];[Some(0,L,12);None];[Some(1,L,14);None];[Some(1,L,8);None];[Some(1,R,81);None];[Some(1,L,12);None];[Some(0,R,66);Some(0,R,54)];[None;None];[Some(0,R,70);Some(1,R,70)];[Some(0,L,8);Some(0,R,81)];[Some(1,R,66);Some(1,R,54)];[None;None];[Some(1,R,70);Some(0,L,8)];[Some(1,L,8);Some(1,R,81)];[Some(0,L,9);Some(0,L,89)];[Some(0,L,11);Some(0,L,91)];[Some(0,L,13);Some(0,L,93)];[Some(0,L,15);Some(0,L,95)];[Some(1,L,9);Some(1,L,89)];[Some(1,L,11);Some(1,L,91)];[Some(1,L,13);Some(1,L,93)];[Some(1,L,15);Some(1,L,95)];[Some(0,R,85);Some(0,R,81)];[Some(0,L,8);Some(0,R,83)];[None;Some(0,R,85)];[None;Some(0,R,87)];[Some(1,R,85);Some(1,R,81)];[Some(1,L,8);Some(1,R,83)];[Some(1,L,12);Some(1,R,85)];[Some(0,R,81);Some(1,R,87)];[Some(0,L,57);Some(1,R,39)];[Some(0,L,59);Some(0,R,23)];[Some(0,L,61);Some(0,L,8)];[Some(0,L,63);Some(0,R,3)];[Some(1,L,57);Some(1,R,70)];[Some(1,L,59);Some(1,R,70)];[Some(1,L,61);Some(1,L,8)];[Some(1,L,63);Some(0,R,81)];[Some(0,R,1);None];[Some(0,R,3);Some(0,R,81)];[Some(0,R,5);None];[Some(0,R,7);Some(0,R,85)];[Some(1,R,1);None];[Some(1,R,3);Some(1,R,81)];[Some(1,R,5);None];[Some(1,R,7);Some(1,R,85)];[Some(1,R,54);Some(0,L,25)];[Some(0,L,8);Some(0,L,27)];[Some(1,L,12);Some(0,L,29)];[Some(0,L,12);Some(0,L,31)];[None;Some(1,L,25)];[Some(1,L,8);Some(1,L,27)];[Some(1,R,85);Some(1,L,29)];[Some(1,L,12);Some(1,L,31)]]%N.
Definition tm1 := TM'_from_str "1LB1RD_0LC1LC_1RA0LC_1RF1RE_0RF0RE_0RG1RA_1RH1RA_1RI---_1RA0LC".
Definition tm2 := TM'_from_str "1LB1RD_0LC1LC_1RA0LC_1RF1RE_0RF0RE_0RG1RA_1RH1RA_1RI1RJ_1RA0LC_1RJ1RJ".
Definition l0 := [0;0;1;1;1;1;1;1;0;1;1;1;0;1;1;1]%N.
Definition mp := mp_from_list [70;12;8;85;81;3;23;39;54]%N.
Definition mp' := mp_from_list [70;12;8;85;81;3;23;39;54]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 32 32.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM1.


Module TM2.
Definition tm := TM_from_str "1RB1LC_1RC0LB_1RD0RF_0RE---_1LB1LA_1LE1RA".
Definition tm' := TM_from_str "1RB1LC_1RC0LB_1RD0RF_0RE---_1LB0LF_1LE1RA".
Definition tm0 := TM'_from_list [[Some(0,R,17);None];[Some(0,R,19);Some(0,R,1)];[Some(0,R,21);None];[Some(0,R,23);Some(0,R,5)];[Some(1,R,17);None];[Some(1,R,19);Some(1,R,1)];[Some(1,R,21);None];[Some(1,R,23);Some(1,R,5)];[Some(1,R,70);Some(0,L,41)];[Some(0,L,24);Some(0,L,43)];[Some(1,L,28);Some(0,L,45)];[Some(0,L,28);Some(0,L,47)];[None;Some(1,L,41)];[Some(1,L,24);Some(1,L,43)];[Some(1,R,5);Some(1,L,45)];[Some(1,L,28);Some(1,L,47)];[Some(0,R,33);Some(0,R,51)];[Some(0,R,35);Some(0,R,70)];[Some(0,R,37);Some(0,R,55)];[Some(0,R,39);Some(1,R,86)];[Some(1,R,33);Some(1,R,51)];[Some(1,R,35);Some(1,R,70)];[Some(1,R,37);Some(1,R,55)];[Some(1,R,39);Some(0,L,24)];[Some(1,R,86);Some(0,L,24)];[Some(0,L,30);Some(0,L,26)];[None;Some(0,L,28)];[Some(1,R,19);Some(0,L,30)];[Some(0,L,24);Some(1,L,24)];[Some(1,L,30);Some(1,L,26)];[None;Some(1,L,28)];[Some(1,R,1);Some(1,L,30)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(1,L,28);Some(0,L,27)];[None;Some(0,R,39)];[Some(0,L,24);Some(0,L,31)];[None;Some(0,R,19)];[Some(1,R,5);Some(1,L,27)];[None;Some(1,R,86)];[Some(1,L,24);Some(1,L,31)];[None;Some(0,R,1)];[Some(0,R,64);None];[Some(0,R,66);None];[Some(0,R,68);None];[Some(0,R,70);None];[Some(1,R,64);None];[Some(1,R,66);None];[Some(1,R,68);None];[Some(1,R,70);None];[Some(0,L,30);None];[Some(0,L,24);None];[Some(1,R,19);None];[Some(0,L,28);None];[Some(1,L,30);None];[Some(1,L,24);None];[Some(1,R,1);None];[Some(1,L,28);None];[Some(0,R,82);Some(0,R,70)];[None;None];[Some(0,R,86);Some(1,R,86)];[Some(0,L,24);Some(0,R,1)];[Some(1,R,82);Some(1,R,70)];[None;None];[Some(1,R,86);Some(0,L,24)];[Some(1,L,24);Some(1,R,1)];[Some(0,L,25);Some(0,L,9)];[Some(0,L,27);Some(0,L,11)];[Some(0,L,29);Some(0,L,13)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,25);Some(1,L,9)];[Some(1,L,27);Some(1,L,11)];[Some(1,L,29);Some(1,L,13)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,5);Some(0,R,1)];[Some(0,L,24);Some(0,R,3)];[None;Some(0,R,5)];[None;Some(0,R,7)];[Some(1,R,5);Some(1,R,1)];[Some(1,L,24);Some(1,R,3)];[Some(1,L,28);Some(1,R,5)];[Some(0,R,1);Some(1,R,7)];[Some(0,L,73);Some(1,R,55)];[Some(0,L,75);Some(0,R,39)];[Some(0,L,77);Some(0,L,24)];[Some(0,L,79);Some(0,R,19)];[Some(1,L,73);Some(1,R,86)];[Some(1,L,75);Some(1,R,86)];[Some(1,L,77);Some(1,L,24)];[Some(1,L,79);Some(0,R,1)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);None];[Some(0,R,19);Some(0,R,1)];[Some(0,R,21);None];[Some(0,R,23);Some(0,R,5)];[Some(1,R,17);None];[Some(1,R,19);Some(1,R,1)];[Some(1,R,21);None];[Some(1,R,23);Some(1,R,5)];[Some(1,R,70);Some(0,L,41)];[Some(0,L,24);Some(0,L,43)];[Some(1,L,28);Some(0,L,45)];[Some(0,L,28);Some(0,L,47)];[None;Some(1,L,41)];[Some(1,L,24);Some(1,L,43)];[Some(1,R,5);Some(1,L,45)];[Some(1,L,28);Some(1,L,47)];[Some(0,R,33);Some(0,R,51)];[Some(0,R,35);Some(0,R,70)];[Some(0,R,37);Some(0,R,55)];[Some(0,R,39);Some(1,R,86)];[Some(1,R,33);Some(1,R,51)];[Some(1,R,35);Some(1,R,70)];[Some(1,R,37);Some(1,R,55)];[Some(1,R,39);Some(0,L,24)];[Some(1,R,86);Some(0,L,24)];[Some(0,L,30);Some(0,L,26)];[None;Some(0,L,28)];[Some(1,R,19);Some(0,L,30)];[Some(0,L,24);Some(1,L,24)];[Some(1,L,30);Some(1,L,26)];[None;Some(1,L,28)];[Some(1,R,1);Some(1,L,30)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(1,L,28);Some(0,L,27)];[None;Some(0,R,39)];[Some(0,L,90);Some(0,L,31)];[None;Some(0,R,19)];[Some(1,R,5);Some(1,L,27)];[None;Some(1,R,86)];[Some(1,L,90);Some(1,L,31)];[None;Some(0,R,1)];[Some(0,R,64);None];[Some(0,R,66);None];[Some(0,R,68);None];[Some(0,R,70);None];[Some(1,R,64);None];[Some(1,R,66);None];[Some(1,R,68);None];[Some(1,R,70);None];[Some(0,L,30);None];[Some(0,L,73);None];[Some(1,R,19);None];[Some(0,L,77);None];[Some(1,L,30);None];[Some(1,L,73);None];[Some(1,R,1);None];[Some(1,L,77);None];[Some(0,R,82);Some(1,R,19)];[None;Some(0,R,19)];[Some(0,R,86);Some(0,L,77)];[Some(0,L,24);Some(0,R,23)];[Some(1,R,82);Some(0,L,30)];[None;Some(1,R,19)];[Some(1,R,86);Some(0,L,24)];[Some(1,L,24);Some(1,R,23)];[Some(0,L,25);Some(0,L,88)];[Some(0,L,27);Some(0,L,90)];[Some(0,L,29);Some(0,L,92)];[Some(0,L,31);Some(0,L,94)];[Some(1,L,25);Some(1,L,88)];[Some(1,L,27);Some(1,L,90)];[Some(1,L,29);Some(1,L,92)];[Some(1,L,31);Some(1,L,94)];[Some(0,R,5);Some(0,R,1)];[Some(1,L,27);Some(0,R,3)];[None;Some(0,R,5)];[Some(1,R,86);Some(0,R,7)];[Some(1,R,5);Some(1,R,1)];[Some(1,L,90);Some(1,R,3)];[Some(1,L,28);Some(1,R,5)];[Some(0,L,24);Some(1,R,7)];[Some(0,L,73);Some(1,R,55)];[Some(0,L,75);Some(0,R,39)];[Some(0,L,77);Some(0,L,24)];[Some(0,L,79);Some(0,R,19)];[Some(1,L,73);Some(1,R,86)];[Some(1,L,75);Some(1,R,86)];[Some(1,L,77);Some(1,L,24)];[Some(1,L,79);Some(0,R,1)]]%N.
Definition tm1 := TM'_from_str "1RB0LD_1LC1RE_0LD1LD_1RB0LD_1RG1RF_0RG0RF_0RH1RB_1RI1RB_1RA---".
Definition tm2 := TM'_from_str "1RB0LD_1LC1RE_0LD1LD_1RB0LD_1RG1RF_0RG0RF_0RH1RB_1RI1RB_1RA1RJ_1RJ1RJ".
Definition l0 := [0;1;1;1;0;0;1;1;1;0;1;1;1;0;1;1]%N.
Definition mp := mp_from_list [70;86;28;24;5;1;19;39;55]%N.
Definition mp' := mp_from_list [70;86;28;24;5;1;19;39;55]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 38 38.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM2.


Module TM3.
Definition tm := TM_from_str "1RB0RD_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LE---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LE---".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,48)];[Some(0,R,19);Some(0,R,50)];[Some(0,R,21);Some(0,R,52)];[Some(0,R,23);Some(0,R,54)];[Some(1,R,17);Some(1,R,48)];[Some(1,R,19);Some(1,R,50)];[Some(1,R,21);Some(1,R,52)];[Some(1,R,23);Some(1,R,54)];[Some(0,L,58);Some(1,L,74)];[Some(1,L,74);Some(0,L,74)];[Some(0,L,62);Some(1,R,17)];[Some(1,R,17);Some(0,L,78)];[Some(1,L,58);Some(1,R,66)];[Some(1,R,66);Some(1,L,74)];[Some(1,L,62);Some(1,R,48)];[Some(1,R,48);Some(1,L,78)];[Some(0,R,48);Some(0,R,64)];[Some(1,R,66);Some(0,R,66)];[Some(0,R,52);Some(0,R,68)];[Some(1,L,74);Some(0,R,70)];[Some(1,R,48);Some(1,R,64)];[Some(1,L,74);Some(1,R,66)];[Some(1,R,52);Some(1,R,68)];[None;Some(1,R,70)];[Some(0,L,41);Some(0,L,13)];[Some(0,L,43);Some(1,R,66)];[Some(0,L,45);Some(0,R,21)];[Some(0,L,47);Some(0,R,66)];[Some(1,L,41);Some(1,L,13)];[Some(1,L,43);Some(0,R,66)];[Some(1,L,45);Some(0,R,4)];[Some(1,L,47);Some(1,L,13)];[Some(0,R,0);Some(0,R,21)];[Some(0,R,2);Some(0,L,44)];[Some(0,R,4);Some(0,L,44)];[Some(0,R,6);None];[Some(1,R,0);Some(1,R,21)];[Some(1,R,2);Some(0,R,21)];[Some(1,R,4);Some(0,R,21)];[Some(1,R,6);None];[Some(0,L,13);Some(0,L,56)];[Some(0,R,21);Some(0,L,58)];[Some(0,R,21);Some(0,L,60)];[Some(0,L,44);Some(0,L,62)];[Some(1,L,13);Some(1,L,56)];[Some(0,R,4);Some(1,L,58)];[Some(0,R,4);Some(1,L,60)];[Some(1,L,44);Some(1,L,62)];[Some(0,R,66);Some(1,L,13)];[Some(1,L,13);None];[Some(0,R,70);Some(0,R,66)];[Some(0,R,66);None];[Some(1,R,66);Some(1,L,56)];[Some(1,L,56);None];[Some(1,R,70);Some(1,R,66)];[Some(1,R,66);None];[Some(0,L,9);Some(0,L,89)];[Some(0,L,11);Some(0,L,91)];[Some(0,L,13);Some(0,L,93)];[Some(0,L,15);Some(0,L,95)];[Some(1,L,9);Some(1,L,89)];[Some(1,L,11);Some(1,L,91)];[Some(1,L,13);Some(1,L,93)];[Some(1,L,15);Some(1,L,95)];[Some(0,R,17);Some(0,R,0)];[Some(1,L,74);Some(0,R,2)];[Some(0,R,21);Some(0,R,4)];[Some(0,L,74);Some(0,R,6)];[Some(1,R,17);Some(1,R,0)];[Some(0,L,74);Some(1,R,2)];[Some(1,R,21);Some(1,R,4)];[None;Some(1,R,6)];[Some(0,L,40);Some(0,L,13)];[Some(0,L,42);Some(0,R,21)];[Some(0,L,44);Some(0,R,21)];[Some(0,L,46);Some(0,L,44)];[Some(1,L,40);Some(1,L,13)];[Some(1,L,42);Some(0,R,4)];[Some(1,L,44);Some(0,R,4)];[Some(1,L,46);Some(1,L,44)];[Some(1,R,66);None];[Some(0,R,17);None];[Some(0,L,9);None];[Some(0,R,21);None];[Some(1,L,74);None];[Some(1,R,17);None];[Some(0,L,89);None];[Some(1,R,21);None];[Some(0,L,72);None];[Some(0,L,74);None];[Some(0,L,76);None];[Some(0,L,78);None];[Some(1,L,72);None];[Some(1,L,74);None];[Some(1,L,76);None];[Some(1,L,78);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(1,R,66)];[Some(0,R,19);Some(0,R,17)];[Some(0,R,21);Some(0,L,9)];[Some(0,R,23);Some(0,R,21)];[Some(1,R,17);Some(1,L,74)];[Some(1,R,19);Some(1,R,17)];[Some(1,R,21);Some(0,L,89)];[Some(1,R,23);Some(1,R,21)];[Some(0,L,58);Some(0,L,72)];[Some(1,L,74);Some(0,L,74)];[Some(0,L,62);Some(0,L,76)];[Some(1,R,17);Some(0,L,78)];[Some(1,L,58);Some(1,L,72)];[Some(1,R,66);Some(1,L,74)];[Some(1,L,62);Some(1,L,76)];[Some(1,R,64);Some(1,L,78)];[Some(1,R,66);Some(0,R,64)];[Some(1,R,66);Some(0,R,66)];[Some(0,L,9);Some(0,R,68)];[Some(1,L,74);Some(0,R,70)];[Some(1,L,74);Some(1,R,64)];[Some(1,L,74);Some(1,R,66)];[Some(0,L,89);Some(1,R,68)];[None;Some(1,R,70)];[Some(0,L,41);Some(0,L,13)];[Some(0,L,43);Some(1,R,66)];[Some(0,L,45);Some(0,R,21)];[Some(0,L,47);Some(0,R,17)];[Some(1,L,41);Some(1,L,13)];[Some(1,L,43);Some(0,R,66)];[Some(1,L,45);Some(0,R,68)];[Some(1,L,47);Some(0,R,64)];[Some(0,R,0);Some(0,R,21)];[Some(0,R,2);Some(0,L,44)];[Some(0,R,4);Some(0,L,44)];[Some(0,R,6);None];[Some(1,R,0);Some(1,R,21)];[Some(1,R,2);Some(0,R,21)];[Some(1,R,4);Some(0,R,21)];[Some(1,R,6);None];[Some(0,L,13);Some(0,L,56)];[Some(0,L,40);Some(0,L,58)];[Some(0,R,21);Some(0,L,60)];[Some(0,L,44);Some(0,L,62)];[Some(1,L,13);Some(1,L,56)];[Some(1,L,40);Some(1,L,58)];[Some(0,R,68);Some(1,L,60)];[Some(1,L,44);Some(1,L,62)];[Some(0,R,66);Some(1,L,13)];[Some(1,L,13);None];[Some(0,R,70);Some(0,R,66)];[Some(0,R,66);None];[Some(1,R,66);Some(1,L,56)];[Some(1,L,56);None];[Some(1,R,70);Some(1,R,66)];[Some(1,R,66);None];[Some(0,L,9);Some(0,L,89)];[Some(0,L,11);Some(0,L,91)];[Some(0,L,13);Some(0,L,93)];[Some(0,L,15);Some(0,L,95)];[Some(1,L,9);Some(1,L,89)];[Some(1,L,11);Some(1,L,91)];[Some(1,L,13);Some(1,L,93)];[Some(1,L,15);Some(1,L,95)];[Some(0,R,17);Some(0,R,64)];[Some(1,L,74);Some(0,R,66)];[Some(0,R,21);Some(0,R,68)];[Some(0,L,74);Some(0,R,70)];[Some(1,R,17);Some(1,R,64)];[Some(0,L,74);Some(1,R,66)];[Some(1,R,21);Some(1,R,68)];[None;Some(1,R,70)];[Some(0,L,40);Some(0,L,13)];[Some(0,L,42);Some(1,R,66)];[Some(0,L,44);Some(0,R,21)];[Some(0,L,46);Some(0,R,17)];[Some(1,L,40);Some(1,L,13)];[Some(1,L,42);Some(0,R,66)];[Some(1,L,44);Some(0,R,68)];[Some(1,L,46);Some(0,R,64)];[Some(1,R,66);None];[Some(0,R,17);None];[Some(0,L,9);None];[Some(0,R,21);None];[Some(1,L,74);None];[Some(1,R,17);None];[Some(0,L,89);None];[Some(1,R,21);None];[Some(0,L,72);None];[Some(0,L,74);None];[Some(0,L,76);None];[Some(0,L,78);None];[Some(1,L,72);None];[Some(1,L,74);None];[Some(1,L,76);None];[Some(1,L,78);None]]%N.
Definition tm1 := TM'_from_str "1LB1RH_0LC0RA_1LG1LD_0LE0LF_1LB0LB_0LB---_1RH1LB_0RA0RI_1RJ---_1RH0RH".
Definition tm2 := TM'_from_str "1LB1RH_0LC0RA_1LG1LD_0LE0LF_1LB0LB_0LB1RK_1RH1LB_0RA0RI_1RJ---_1RH0RH_1RK1RK".
Definition l0 := [1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [21;74;44;56;9;89;13;66;4;17]%N.
Definition mp' := mp_from_list [21;74;44;56;9;89;13;66;68;17]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 true) 49 49.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM3.


Module TM4.
Definition tm := TM_from_str "1LB0LE_0LC---_1RD1RF_1LA0RD_1RC1LF_1LD1RA".
Definition tm' := TM_from_str "1LB0LE_0LC---_1RD0RE_1LA0RD_1RC1LF_1LD1RA".
Definition tm0 := TM'_from_list [[Some(1,R,52);Some(0,R,51)];[None;Some(0,L,15)];[Some(0,R,48);Some(0,R,55)];[None;Some(0,L,59)];[Some(1,L,93);Some(1,R,51)];[None;Some(1,L,78)];[Some(1,R,48);Some(1,R,55)];[None;Some(0,L,89)];[Some(0,L,25);Some(0,L,72)];[Some(0,L,27);Some(0,L,74)];[Some(0,L,29);Some(0,L,76)];[Some(0,L,31);Some(0,L,78)];[Some(1,L,25);Some(1,L,72)];[Some(1,L,27);Some(1,L,74)];[Some(1,L,29);Some(1,L,76)];[Some(1,L,31);Some(1,L,78)];[Some(0,R,54);None];[Some(0,R,48);None];[Some(1,L,59);None];[Some(0,R,52);None];[Some(1,R,54);None];[Some(1,R,48);None];[Some(1,L,89);None];[Some(1,R,52);None];[Some(0,L,40);None];[Some(0,L,42);None];[Some(0,L,44);None];[Some(0,L,46);None];[Some(1,L,40);None];[Some(1,L,42);None];[Some(1,L,44);None];[Some(1,L,46);None];[Some(0,R,49);Some(0,R,81)];[Some(0,R,51);Some(0,R,83)];[Some(0,R,53);Some(0,R,85)];[Some(0,R,55);Some(0,R,87)];[Some(1,R,49);Some(1,R,81)];[Some(1,R,51);Some(1,R,83)];[Some(1,R,53);Some(1,R,85)];[Some(1,R,55);Some(1,R,87)];[Some(0,L,74);Some(0,L,46)];[None;None];[Some(0,L,78);Some(1,L,78)];[Some(0,R,48);Some(0,L,89)];[Some(1,L,74);Some(1,L,46)];[None;None];[Some(1,L,78);Some(0,R,48)];[Some(1,R,48);Some(1,L,89)];[Some(1,L,78);Some(0,R,48)];[Some(0,R,54);Some(0,R,50)];[None;Some(0,R,52)];[Some(1,L,59);Some(0,R,54)];[Some(0,R,48);Some(1,R,48)];[Some(1,R,54);Some(1,R,50)];[None;Some(1,R,52)];[Some(1,L,89);Some(1,R,54)];[Some(0,L,9);Some(0,L,27)];[Some(0,L,11);Some(0,L,46)];[Some(0,L,13);Some(0,L,31)];[Some(0,L,15);Some(1,L,78)];[Some(1,L,9);Some(1,L,27)];[Some(1,L,11);Some(1,L,46)];[Some(1,L,13);Some(1,L,31)];[Some(1,L,15);Some(0,R,48)];[Some(0,R,33);Some(1,L,31)];[Some(0,R,35);Some(0,L,15)];[Some(0,R,37);Some(0,R,48)];[Some(0,R,39);Some(0,L,59)];[Some(1,R,33);Some(1,L,78)];[Some(1,R,35);Some(1,L,78)];[Some(1,R,37);Some(1,R,48)];[Some(1,R,39);Some(0,L,89)];[Some(0,L,93);Some(0,L,89)];[Some(0,R,48);Some(0,L,91)];[None;Some(0,L,93)];[None;Some(0,L,95)];[Some(1,L,93);Some(1,L,89)];[Some(1,R,48);Some(1,L,91)];[Some(1,R,52);Some(1,L,93)];[Some(0,L,89);Some(1,L,95)];[Some(1,L,46);Some(0,R,1)];[Some(0,R,48);Some(0,R,3)];[Some(1,R,52);Some(0,R,5)];[Some(0,R,52);Some(0,R,7)];[None;Some(1,R,1)];[Some(1,R,48);Some(1,R,3)];[Some(1,L,93);Some(1,R,5)];[Some(1,R,52);Some(1,R,7)];[Some(0,L,57);None];[Some(0,L,59);Some(0,L,89)];[Some(0,L,61);None];[Some(0,L,63);Some(0,L,93)];[Some(1,L,57);None];[Some(1,L,59);Some(1,L,89)];[Some(1,L,61);None];[Some(1,L,63);Some(1,L,93)]]%N.
Definition tm0' := TM'_from_list [[Some(1,R,52);Some(0,R,51)];[None;Some(0,L,15)];[Some(0,R,66);Some(0,R,55)];[None;Some(0,L,59)];[Some(1,L,93);Some(1,R,51)];[None;Some(1,L,78)];[Some(1,R,66);Some(1,R,55)];[None;Some(0,L,89)];[Some(0,L,25);Some(0,L,72)];[Some(0,L,27);Some(0,L,74)];[Some(0,L,29);Some(0,L,76)];[Some(0,L,31);Some(0,L,78)];[Some(1,L,25);Some(1,L,72)];[Some(1,L,27);Some(1,L,74)];[Some(1,L,29);Some(1,L,76)];[Some(1,L,31);Some(1,L,78)];[Some(0,R,54);None];[Some(0,R,33);None];[Some(1,L,59);None];[Some(0,R,37);None];[Some(1,R,54);None];[Some(1,R,33);None];[Some(1,L,89);None];[Some(1,R,37);None];[Some(0,L,40);None];[Some(0,L,42);None];[Some(0,L,44);None];[Some(0,L,46);None];[Some(1,L,40);None];[Some(1,L,42);None];[Some(1,L,44);None];[Some(1,L,46);None];[Some(0,R,49);Some(0,R,64)];[Some(0,R,51);Some(0,R,66)];[Some(0,R,53);Some(0,R,68)];[Some(0,R,55);Some(0,R,70)];[Some(1,R,49);Some(1,R,64)];[Some(1,R,51);Some(1,R,66)];[Some(1,R,53);Some(1,R,68)];[Some(1,R,55);Some(1,R,70)];[Some(0,L,74);Some(1,L,59)];[None;Some(0,L,59)];[Some(0,L,78);Some(0,R,37)];[Some(0,R,48);Some(0,L,63)];[Some(1,L,74);Some(0,R,54)];[None;Some(1,L,59)];[Some(1,L,78);Some(0,R,48)];[Some(1,R,48);Some(1,L,63)];[Some(1,L,78);Some(0,R,48)];[Some(0,R,54);Some(0,R,50)];[None;Some(0,R,52)];[Some(1,L,59);Some(0,R,54)];[Some(0,R,48);Some(1,R,48)];[Some(1,R,54);Some(1,R,50)];[None;Some(1,R,52)];[Some(1,L,89);Some(1,R,54)];[Some(0,L,9);Some(0,L,27)];[Some(0,L,11);Some(0,L,46)];[Some(0,L,13);Some(0,L,31)];[Some(0,L,15);Some(1,L,78)];[Some(1,L,9);Some(1,L,27)];[Some(1,L,11);Some(1,L,46)];[Some(1,L,13);Some(1,L,31)];[Some(1,L,15);Some(0,R,48)];[Some(0,R,33);Some(1,L,31)];[Some(0,R,35);Some(0,L,15)];[Some(0,R,37);Some(0,R,48)];[Some(0,R,39);Some(0,L,59)];[Some(1,R,33);Some(1,L,78)];[Some(1,R,35);Some(1,L,78)];[Some(1,R,37);Some(1,R,48)];[Some(1,R,39);Some(0,L,89)];[Some(0,L,93);Some(0,L,89)];[Some(1,R,51);Some(0,L,91)];[None;Some(0,L,93)];[Some(1,L,78);Some(0,L,95)];[Some(1,L,93);Some(1,L,89)];[Some(1,R,66);Some(1,L,91)];[Some(1,R,52);Some(1,L,93)];[Some(0,R,48);Some(1,L,95)];[Some(1,L,46);Some(0,R,1)];[Some(0,R,48);Some(0,R,3)];[Some(1,R,52);Some(0,R,5)];[Some(0,R,52);Some(0,R,7)];[None;Some(1,R,1)];[Some(1,R,48);Some(1,R,3)];[Some(1,L,93);Some(1,R,5)];[Some(1,R,52);Some(1,R,7)];[Some(0,L,57);None];[Some(0,L,59);Some(0,L,89)];[Some(0,L,61);None];[Some(0,L,63);Some(0,L,93)];[Some(1,L,57);None];[Some(1,L,59);Some(1,L,89)];[Some(1,L,61);None];[Some(1,L,63);Some(1,L,93)]]%N.
Definition tm1 := TM'_from_str "1LB0RA_1RC1LD_0RA1RA_1LF1LE_0LF0LE_0LG1LB_1LH1LB_1LI---_1LB0RA".
Definition tm2 := TM'_from_str "1LB0RA_1RC1LD_0RA1RA_1LF1LE_0LF0LE_0LG1LB_1LH1LB_1LI1RJ_1LB0RA_1RJ1RJ".
Definition l0 := [1;1;0;1;1;0;0;1;1;0;0;1;1;0;0;0]%N.
Definition mp := mp_from_list [48;78;52;93;89;59;15;31;46]%N.
Definition mp' := mp_from_list [48;78;52;93;89;59;15;31;46]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 54 54.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM4.


Module TM5.
Definition tm := TM_from_str "1LB1RE_1LC0LA_1RD0LC_1RF0RA_1RC1LD_0RB---".
Definition tm' := TM_from_str "1LB1RE_1LC1LE_1RD0LC_1RF0RA_1RC1LD_0RB---".
Definition tm0 := TM'_from_list [[Some(0,R,69);Some(0,R,65)];[Some(1,L,43);Some(0,R,67)];[None;Some(0,R,69)];[Some(1,R,6);Some(0,R,71)];[Some(1,R,69);Some(1,R,65)];[Some(1,L,10);Some(1,R,67)];[Some(1,L,44);Some(1,R,69)];[Some(0,L,40);Some(1,R,71)];[Some(0,L,25);Some(1,R,87)];[Some(0,L,27);Some(0,R,55)];[Some(0,L,29);Some(0,L,40)];[Some(0,L,31);Some(0,R,35)];[Some(1,L,25);Some(1,R,6)];[Some(1,L,27);Some(1,R,6)];[Some(1,L,29);Some(1,L,40)];[Some(1,L,31);Some(0,R,65)];[Some(0,R,2);Some(1,R,35)];[None;Some(0,R,35)];[Some(0,R,6);Some(0,L,29)];[Some(0,L,40);Some(0,R,39)];[Some(1,R,2);Some(0,L,46)];[None;Some(1,R,35)];[Some(1,R,6);Some(0,L,40)];[Some(1,L,40);Some(1,R,39)];[Some(0,L,41);Some(0,L,8)];[Some(0,L,43);Some(0,L,10)];[Some(0,L,45);Some(0,L,12)];[Some(0,L,47);Some(0,L,14)];[Some(1,L,41);Some(1,L,8)];[Some(1,L,43);Some(1,L,10)];[Some(1,L,45);Some(1,L,12)];[Some(1,L,47);Some(1,L,14)];[Some(0,R,49);Some(0,R,83)];[Some(0,R,51);Some(0,R,22)];[Some(0,R,53);Some(0,R,87)];[Some(0,R,55);Some(1,R,6)];[Some(1,R,49);Some(1,R,83)];[Some(1,R,51);Some(1,R,22)];[Some(1,R,53);Some(1,R,87)];[Some(1,R,55);Some(0,L,40)];[Some(1,R,6);Some(0,L,40)];[Some(0,L,46);Some(0,L,42)];[None;Some(0,L,44)];[Some(1,R,35);Some(0,L,46)];[Some(0,L,40);Some(1,L,40)];[Some(1,L,46);Some(1,L,42)];[None;Some(1,L,44)];[Some(1,R,65);Some(1,L,46)];[Some(0,R,81);Some(0,R,0)];[Some(0,R,83);Some(0,R,2)];[Some(0,R,85);Some(0,R,4)];[Some(0,R,87);Some(0,R,6)];[Some(1,R,81);Some(1,R,0)];[Some(1,R,83);Some(1,R,2)];[Some(1,R,85);Some(1,R,4)];[Some(1,R,87);Some(1,R,6)];[Some(1,L,44);Some(0,L,43)];[None;Some(0,R,55)];[Some(0,L,10);Some(0,L,47)];[None;Some(0,R,35)];[Some(1,R,69);Some(1,L,43)];[None;Some(1,R,6)];[Some(1,L,10);Some(1,L,47)];[None;Some(0,R,65)];[Some(0,R,33);None];[Some(0,R,35);Some(0,R,65)];[Some(0,R,37);None];[Some(0,R,39);Some(0,R,69)];[Some(1,R,33);None];[Some(1,R,35);Some(1,R,65)];[Some(1,R,37);None];[Some(1,R,39);Some(1,R,69)];[Some(1,R,22);Some(0,L,57)];[Some(0,L,40);Some(0,L,59)];[Some(1,L,44);Some(0,L,61)];[Some(0,L,44);Some(0,L,63)];[None;Some(1,L,57)];[Some(1,L,40);Some(1,L,59)];[Some(1,R,69);Some(1,L,61)];[Some(1,L,44);Some(1,L,63)];[Some(0,R,16);None];[Some(0,R,18);None];[Some(0,R,20);None];[Some(0,R,22);None];[Some(1,R,16);None];[Some(1,R,18);None];[Some(1,R,20);None];[Some(1,R,22);None];[Some(0,L,46);None];[Some(0,L,25);None];[Some(1,R,35);None];[Some(0,L,29);None];[Some(1,L,46);None];[Some(1,L,25);None];[Some(1,R,65);None];[Some(1,L,29);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,69);Some(0,R,65)];[Some(0,L,40);Some(0,R,67)];[None;Some(0,R,69)];[None;Some(0,R,71)];[Some(1,R,69);Some(1,R,65)];[Some(1,L,40);Some(1,R,67)];[Some(1,L,44);Some(1,R,69)];[Some(0,R,65);Some(1,R,71)];[Some(0,L,25);Some(1,R,87)];[Some(0,L,27);Some(0,R,55)];[Some(0,L,29);Some(0,L,40)];[Some(0,L,31);Some(0,R,35)];[Some(1,L,25);Some(1,R,6)];[Some(1,L,27);Some(1,R,6)];[Some(1,L,29);Some(1,L,40)];[Some(1,L,31);Some(0,R,65)];[Some(0,R,2);Some(0,R,22)];[None;None];[Some(0,R,6);Some(1,R,6)];[Some(0,L,40);Some(0,R,65)];[Some(1,R,2);Some(1,R,22)];[None;None];[Some(1,R,6);Some(0,L,40)];[Some(1,L,40);Some(1,R,65)];[Some(0,L,41);Some(0,L,73)];[Some(0,L,43);Some(0,L,75)];[Some(0,L,45);Some(0,L,77)];[Some(0,L,47);Some(0,L,79)];[Some(1,L,41);Some(1,L,73)];[Some(1,L,43);Some(1,L,75)];[Some(1,L,45);Some(1,L,77)];[Some(1,L,47);Some(1,L,79)];[Some(0,R,49);Some(0,R,83)];[Some(0,R,51);Some(0,R,22)];[Some(0,R,53);Some(0,R,87)];[Some(0,R,55);Some(1,R,6)];[Some(1,R,49);Some(1,R,83)];[Some(1,R,51);Some(1,R,22)];[Some(1,R,53);Some(1,R,87)];[Some(1,R,55);Some(0,L,40)];[Some(1,R,6);Some(0,L,40)];[Some(0,L,46);Some(0,L,42)];[None;Some(0,L,44)];[Some(1,R,35);Some(0,L,46)];[Some(0,L,40);Some(1,L,40)];[Some(1,L,46);Some(1,L,42)];[None;Some(1,L,44)];[Some(1,R,65);Some(1,L,46)];[Some(0,R,81);Some(0,R,0)];[Some(0,R,83);Some(0,R,2)];[Some(0,R,85);Some(0,R,4)];[Some(0,R,87);Some(0,R,6)];[Some(1,R,81);Some(1,R,0)];[Some(1,R,83);Some(1,R,2)];[Some(1,R,85);Some(1,R,4)];[Some(1,R,87);Some(1,R,6)];[Some(1,L,44);Some(0,L,43)];[None;Some(0,R,55)];[Some(0,L,40);Some(0,L,47)];[None;Some(0,R,35)];[Some(1,R,69);Some(1,L,43)];[None;Some(1,R,6)];[Some(1,L,40);Some(1,L,47)];[None;Some(0,R,65)];[Some(0,R,33);None];[Some(0,R,35);Some(0,R,65)];[Some(0,R,37);None];[Some(0,R,39);Some(0,R,69)];[Some(1,R,33);None];[Some(1,R,35);Some(1,R,65)];[Some(1,R,37);None];[Some(1,R,39);Some(1,R,69)];[Some(1,R,22);Some(0,L,57)];[Some(0,L,40);Some(0,L,59)];[Some(1,L,44);Some(0,L,61)];[Some(0,L,44);Some(0,L,63)];[None;Some(1,L,57)];[Some(1,L,40);Some(1,L,59)];[Some(1,R,69);Some(1,L,61)];[Some(1,L,44);Some(1,L,63)];[Some(0,R,16);None];[Some(0,R,18);None];[Some(0,R,20);None];[Some(0,R,22);None];[Some(1,R,16);None];[Some(1,R,18);None];[Some(1,R,20);None];[Some(1,R,22);None];[Some(0,L,46);None];[Some(0,L,40);None];[Some(1,R,35);None];[Some(0,L,44);None];[Some(1,L,46);None];[Some(1,L,40);None];[Some(1,R,65);None];[Some(1,L,44);None]]%N.
Definition tm1 := TM'_from_str "1RB1RD_1RC---_1RD0LF_1LE1RG_0LF1LF_1RD0LF_1RI1RH_0RI0RH_0RA1RD".
Definition tm2 := TM'_from_str "1RB1RD_1RC1RJ_1RD0LF_1LE1RG_0LF1LF_1RD0LF_1RI1RH_0RI0RH_0RA1RD_1RJ1RJ".
Definition l0 := [1;1;1;0;1;1;1;0;0;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_list [55;87;22;6;44;40;69;65;35]%N.
Definition mp' := mp_from_list [55;87;22;6;44;40;69;65;35]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 55 55.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM5.


Module TM6.
Definition tm := TM_from_str "1LB0LD_1RC---_1LE1RD_1RC0RF_1LA0LE_1RD0RE".
Definition tm' := TM_from_str "1LB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_1LA---".
Definition tm0 := TM'_from_list [[Some(0,R,51);Some(1,L,27)];[None;Some(0,R,49)];[Some(0,R,55);Some(1,L,9)];[None;Some(0,R,53)];[Some(1,R,51);Some(1,L,58)];[None;Some(1,R,49)];[Some(1,R,55);Some(1,L,72)];[None;Some(1,R,53)];[Some(0,L,25);Some(0,L,56)];[Some(0,L,27);Some(0,L,58)];[Some(0,L,29);Some(0,L,60)];[Some(0,L,31);Some(0,L,62)];[Some(1,L,25);Some(1,L,56)];[Some(1,L,27);Some(1,L,58)];[Some(1,L,29);Some(1,L,60)];[Some(1,L,31);Some(1,L,62)];[Some(0,R,33);None];[Some(0,R,35);None];[Some(0,R,37);None];[Some(0,R,39);None];[Some(1,R,33);None];[Some(1,R,35);None];[Some(1,R,37);None];[Some(1,R,39);None];[Some(0,L,74);None];[Some(1,L,72);None];[Some(0,L,78);None];[Some(1,R,53);None];[Some(1,L,74);None];[Some(1,R,55);None];[Some(1,L,78);None];[Some(1,R,68);None];[Some(1,R,68);Some(0,R,49)];[Some(1,L,27);Some(0,R,51)];[Some(1,L,78);Some(0,R,53)];[Some(1,L,9);Some(0,R,55)];[None;Some(1,R,49)];[Some(1,L,58);Some(1,R,51)];[Some(0,R,68);Some(1,R,53)];[Some(1,L,72);Some(1,R,55)];[Some(0,L,73);Some(0,L,76)];[Some(0,L,75);Some(1,R,35)];[Some(0,L,77);Some(1,R,39)];[Some(0,L,79);Some(1,R,86)];[Some(1,L,73);Some(1,L,76)];[Some(1,L,75);Some(1,R,82)];[Some(1,L,77);Some(1,R,86)];[Some(1,L,79);None];[Some(0,R,33);Some(0,R,80)];[Some(0,R,35);Some(0,R,82)];[Some(0,R,37);Some(0,R,84)];[Some(0,R,39);Some(0,R,86)];[Some(1,R,33);Some(1,R,80)];[Some(1,R,35);Some(1,R,82)];[Some(1,R,37);Some(1,R,84)];[Some(1,R,39);Some(1,R,86)];[Some(0,L,74);Some(1,L,9)];[Some(1,L,72);Some(1,R,53)];[Some(0,L,78);Some(0,R,53)];[Some(1,R,53);Some(0,L,27)];[Some(1,L,74);Some(0,R,55)];[Some(1,R,55);Some(1,R,68)];[Some(1,L,78);Some(0,R,68)];[Some(1,R,68);Some(1,L,27)];[Some(0,R,86);Some(1,R,53)];[Some(1,L,13);Some(0,L,27)];[None;Some(0,L,78)];[Some(0,R,82);Some(0,L,9)];[Some(1,R,86);None];[Some(1,L,76);Some(0,L,58)];[None;Some(0,R,53)];[Some(1,R,82);Some(0,L,72)];[Some(0,L,9);Some(0,L,72)];[Some(0,L,11);Some(0,L,74)];[Some(0,L,13);Some(0,L,76)];[Some(0,L,15);Some(0,L,78)];[Some(1,L,9);Some(1,L,72)];[Some(1,L,11);Some(1,L,74)];[Some(1,L,13);Some(1,L,76)];[Some(1,L,15);Some(1,L,78)];[Some(0,R,49);Some(0,R,64)];[Some(0,R,51);Some(0,R,66)];[Some(0,R,53);Some(0,R,68)];[Some(0,R,55);Some(0,R,70)];[Some(1,R,49);Some(1,R,64)];[Some(1,R,51);Some(1,R,66)];[Some(1,R,53);Some(1,R,68)];[Some(1,R,55);Some(1,R,70)];[Some(0,L,76);Some(0,L,27)];[Some(1,R,35);Some(0,L,9)];[Some(1,R,39);Some(0,L,31)];[Some(1,R,86);Some(0,L,13)];[Some(1,L,76);Some(1,L,27)];[Some(1,R,82);Some(1,L,9)];[Some(1,R,86);Some(1,L,31)];[None;Some(1,L,13)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,19);Some(1,L,27)];[Some(0,R,80);Some(0,R,17)];[Some(0,R,23);Some(1,L,9)];[Some(0,R,84);Some(0,R,21)];[Some(1,R,19);Some(1,L,26)];[Some(1,R,80);Some(1,R,17)];[Some(1,R,23);Some(1,L,56)];[Some(1,R,84);Some(1,R,21)];[Some(0,L,25);Some(0,L,24)];[Some(0,L,27);Some(0,L,26)];[Some(0,L,29);Some(0,L,28)];[Some(0,L,31);Some(0,L,30)];[Some(1,L,25);Some(1,L,24)];[Some(1,L,27);Some(1,L,26)];[Some(1,L,29);Some(1,L,28)];[Some(1,L,31);Some(1,L,30)];[Some(0,R,33);Some(0,R,64)];[Some(0,R,35);Some(0,R,66)];[Some(0,R,37);Some(0,R,68)];[Some(0,R,39);Some(0,R,70)];[Some(1,R,33);Some(1,R,64)];[Some(1,R,35);Some(1,R,66)];[Some(1,R,37);Some(1,R,68)];[Some(1,R,39);Some(1,R,70)];[Some(0,L,58);Some(1,L,9)];[Some(1,L,56);Some(1,R,21)];[Some(0,L,62);Some(0,R,21)];[Some(1,R,21);None];[Some(1,L,58);Some(0,R,23)];[Some(1,R,23);Some(1,R,84)];[Some(1,L,62);Some(0,R,84)];[Some(1,R,84);None];[Some(1,R,84);Some(0,R,17)];[Some(1,L,27);Some(0,R,19)];[Some(1,L,62);Some(0,R,21)];[Some(1,L,9);Some(0,R,23)];[None;Some(1,R,17)];[Some(1,L,26);Some(1,R,19)];[Some(0,R,84);Some(1,R,21)];[Some(1,L,56);Some(1,R,23)];[Some(0,L,57);Some(0,L,60)];[Some(0,L,59);Some(1,R,35)];[Some(0,L,61);Some(1,R,39)];[Some(0,L,63);Some(1,R,70)];[Some(1,L,57);Some(1,L,60)];[Some(1,L,59);Some(1,R,66)];[Some(1,L,61);Some(1,R,70)];[Some(1,L,63);None];[Some(0,R,70);Some(1,R,21)];[Some(1,L,13);Some(0,L,27)];[None;Some(0,L,62)];[Some(0,R,66);Some(0,L,9)];[Some(1,R,70);None];[Some(1,L,60);Some(0,L,26)];[None;Some(0,R,21)];[Some(1,R,66);Some(0,L,56)];[Some(0,L,9);Some(0,L,56)];[Some(0,L,11);Some(0,L,58)];[Some(0,L,13);Some(0,L,60)];[Some(0,L,15);Some(0,L,62)];[Some(1,L,9);Some(1,L,56)];[Some(1,L,11);Some(1,L,58)];[Some(1,L,13);Some(1,L,60)];[Some(1,L,15);Some(1,L,62)];[Some(0,R,17);Some(0,R,80)];[Some(0,R,19);Some(0,R,82)];[Some(0,R,21);Some(0,R,84)];[Some(0,R,23);Some(0,R,86)];[Some(1,R,17);Some(1,R,80)];[Some(1,R,19);Some(1,R,82)];[Some(1,R,21);Some(1,R,84)];[Some(1,R,23);Some(1,R,86)];[Some(0,L,60);Some(0,L,27)];[Some(1,R,35);None];[Some(1,R,39);Some(0,L,31)];[Some(1,R,70);None];[Some(1,L,60);Some(1,L,27)];[Some(1,R,66);None];[Some(1,R,70);Some(1,L,31)];[None;None];[Some(0,R,70);None];[Some(1,L,13);None];[None;None];[Some(0,R,66);None];[Some(1,R,70);None];[Some(1,L,60);None];[None;None];[Some(1,R,66);None];[Some(0,L,9);None];[Some(0,L,11);None];[Some(0,L,13);None];[Some(0,L,15);None];[Some(1,L,9);None];[Some(1,L,11);None];[Some(1,L,13);None];[Some(1,L,15);None]]%N.
Definition tm1 := TM'_from_str "1LB1RI_0LC0LB_0LL0LD_0LE0RG_1LK1LF_1LC1LB_1RH1RM_1LC0RI_1RA1RJ_1RG1RN_1LL1LD_1RG---_0RG0RN_1RJ---".
Definition tm2 := TM'_from_str "1LB1RI_0LC0LB_0LL0LD_0LE0RG_1LK1LF_1LC1LB_1RH1RM_1LC0RI_1RA1RJ_1RG1RN_1LL1LD_1RG1RO_0RG0RN_1RJ1RO_1RO1RO".
Definition l0 := [1;1;0;1;1;1;0;1;0;1;0;1;0;1;0;1]%N.
Definition mp := mp_from_list [39;72;9;58;78;76;53;35;55;86;13;27;82;68]%N.
Definition mp' := mp_from_list [39;56;9;26;62;60;21;35;23;70;13;27;66;84]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 56 56.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM6.


Module TM7.
Definition tm := TM_from_str "1LB0RD_1LC1LD_0RA1RF_0LF1LE_0RA---_1RE0LB".
Definition tm' := TM_from_str "1LB1LD_0RC1RE_1LA0RD_0LE1LF_1RB0LA_0RC---".
Definition tm0 := TM'_from_list [[Some(0,R,48);Some(0,R,48)];[Some(1,R,48);Some(0,R,50)];[Some(1,L,90);Some(0,R,52)];[Some(0,R,48);Some(0,R,54)];[Some(1,R,48);Some(1,R,48)];[Some(1,L,28);Some(1,R,50)];[Some(1,L,75);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,61)];[Some(0,L,27);Some(1,L,90)];[Some(0,L,29);Some(1,R,2)];[Some(0,L,31);Some(0,R,2)];[Some(1,L,25);Some(1,L,61)];[Some(1,L,27);Some(0,R,52)];[Some(1,L,29);Some(1,R,48)];[Some(1,L,31);Some(0,R,48)];[Some(0,R,48);Some(0,R,52)];[Some(1,R,2);Some(0,R,48)];[Some(0,R,52);Some(1,L,41)];[Some(0,R,2);None];[Some(1,R,48);Some(1,R,52)];[Some(0,L,28);Some(1,R,48)];[Some(1,R,52);Some(1,L,57)];[None;None];[Some(0,L,41);Some(0,L,57)];[Some(0,L,43);Some(0,L,59)];[Some(0,L,45);Some(0,L,61)];[Some(0,L,47);Some(0,L,63)];[Some(1,L,41);Some(1,L,57)];[Some(1,L,43);Some(1,L,59)];[Some(1,L,45);Some(1,L,61)];[Some(1,L,47);Some(1,L,63)];[Some(0,R,0);Some(0,R,81)];[Some(0,R,2);Some(0,R,83)];[Some(0,R,4);Some(0,R,85)];[Some(0,R,6);Some(0,R,87)];[Some(1,R,0);Some(1,R,81)];[Some(1,R,2);Some(1,R,83)];[Some(1,R,4);Some(1,R,85)];[Some(1,R,6);Some(1,R,87)];[Some(0,L,43);Some(1,L,75)];[Some(1,L,90);Some(0,L,57)];[Some(0,L,47);None];[Some(0,R,2);Some(0,L,61)];[Some(1,L,43);Some(1,R,52)];[Some(0,R,52);Some(1,L,57)];[Some(1,L,47);None];[Some(0,R,48);Some(1,L,61)];[Some(0,R,2);Some(0,R,48)];[Some(1,L,90);None];[Some(0,R,6);Some(0,R,52)];[Some(0,L,90);None];[Some(1,R,2);Some(1,R,48)];[Some(0,L,57);None];[Some(1,R,6);Some(1,R,52)];[Some(0,L,75);None];[Some(0,L,88);Some(0,L,73)];[Some(0,L,90);Some(0,L,75)];[Some(0,L,92);Some(0,L,77)];[Some(0,L,94);Some(0,L,79)];[Some(1,L,88);Some(1,L,73)];[Some(1,L,90);Some(1,L,75)];[Some(1,L,92);Some(1,L,77)];[Some(1,L,94);Some(1,L,79)];[Some(0,R,0);None];[Some(0,R,2);None];[Some(0,R,4);None];[Some(0,R,6);None];[Some(1,R,0);None];[Some(1,R,2);None];[Some(1,R,4);None];[Some(1,R,6);None];[Some(0,L,43);None];[Some(1,L,90);None];[Some(0,L,47);None];[Some(0,R,2);None];[Some(1,L,43);None];[Some(0,R,52);None];[Some(1,L,47);None];[Some(0,R,48);None];[Some(0,R,65);Some(0,R,2)];[Some(0,R,67);Some(1,R,2)];[Some(0,R,69);Some(0,L,90)];[Some(0,R,71);Some(0,R,2)];[Some(1,R,65);Some(1,R,2)];[Some(1,R,67);Some(0,L,28)];[Some(1,R,69);Some(0,L,75)];[Some(1,R,71);None];[Some(0,L,61);Some(0,L,24)];[None;Some(0,L,26)];[Some(1,R,2);Some(0,L,28)];[None;Some(0,L,30)];[Some(1,L,61);Some(1,L,24)];[None;Some(1,L,26)];[Some(1,R,48);Some(1,L,28)];[None;Some(1,L,30)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,48);Some(0,R,52)];[Some(1,R,34);Some(0,R,48)];[Some(0,R,52);Some(1,L,25)];[Some(0,R,34);None];[Some(1,R,48);Some(1,R,52)];[Some(0,L,12);Some(1,R,48)];[Some(1,R,52);Some(1,L,57)];[None;None];[Some(0,L,25);Some(0,L,57)];[Some(0,L,27);Some(0,L,59)];[Some(0,L,29);Some(0,L,61)];[Some(0,L,31);Some(0,L,63)];[Some(1,L,25);Some(1,L,57)];[Some(1,L,27);Some(1,L,59)];[Some(1,L,29);Some(1,L,61)];[Some(1,L,31);Some(1,L,63)];[Some(0,R,32);Some(0,R,65)];[Some(0,R,34);Some(0,R,67)];[Some(0,R,36);Some(0,R,69)];[Some(0,R,38);Some(0,R,71)];[Some(1,R,32);Some(1,R,65)];[Some(1,R,34);Some(1,R,67)];[Some(1,R,36);Some(1,R,69)];[Some(1,R,38);Some(1,R,71)];[Some(0,L,27);Some(1,L,91)];[Some(1,L,74);Some(0,L,57)];[Some(0,L,31);Some(1,R,23)];[Some(0,R,34);Some(0,L,61)];[Some(1,L,27);Some(1,R,52)];[Some(0,R,52);Some(1,L,57)];[Some(1,L,31);None];[Some(0,R,48);Some(1,L,61)];[Some(0,R,48);Some(0,R,48)];[Some(1,R,48);Some(0,R,50)];[Some(1,L,74);Some(0,R,52)];[Some(0,R,48);Some(0,R,54)];[Some(1,R,48);Some(1,R,48)];[Some(1,L,12);Some(1,R,50)];[Some(1,L,91);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,9);Some(0,L,61)];[Some(0,L,11);Some(1,L,74)];[Some(0,L,13);Some(1,R,34)];[Some(0,L,15);Some(0,R,34)];[Some(1,L,9);Some(1,L,61)];[Some(1,L,11);Some(0,R,52)];[Some(1,L,13);Some(1,R,48)];[Some(1,L,15);Some(0,R,48)];[Some(0,R,34);Some(0,R,48)];[Some(1,L,74);None];[Some(0,R,38);Some(0,R,52)];[Some(0,L,74);None];[Some(1,R,34);Some(1,R,48)];[Some(0,L,57);None];[Some(1,R,38);Some(1,R,52)];[Some(0,L,91);None];[Some(0,L,72);Some(0,L,89)];[Some(0,L,74);Some(0,L,91)];[Some(0,L,76);Some(0,L,93)];[Some(0,L,78);Some(0,L,95)];[Some(1,L,72);Some(1,L,89)];[Some(1,L,74);Some(1,L,91)];[Some(1,L,76);Some(1,L,93)];[Some(1,L,78);Some(1,L,95)];[Some(0,R,17);Some(0,R,34)];[Some(0,R,19);Some(1,R,34)];[Some(0,R,21);Some(0,L,74)];[Some(0,R,23);Some(0,R,34)];[Some(1,R,17);Some(1,R,34)];[Some(1,R,19);Some(0,L,12)];[Some(1,R,21);Some(0,L,91)];[Some(1,R,23);None];[Some(0,L,61);Some(0,L,8)];[Some(1,R,38);Some(0,L,10)];[Some(1,R,34);Some(0,L,12)];[Some(0,L,91);Some(0,L,14)];[Some(1,L,61);Some(1,L,8)];[Some(1,R,71);Some(1,L,10)];[Some(1,R,48);Some(1,L,12)];[Some(1,L,91);Some(1,L,14)];[Some(0,R,32);None];[Some(0,R,34);None];[Some(0,R,36);None];[Some(0,R,38);None];[Some(1,R,32);None];[Some(1,R,34);None];[Some(1,R,36);None];[Some(1,R,38);None];[Some(0,L,27);None];[Some(1,L,74);None];[Some(0,L,31);None];[Some(0,R,34);None];[Some(1,L,27);None];[Some(0,R,52);None];[Some(1,L,31);None];[Some(0,R,48);None]]%N.
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_1RB0LD_1LE1LF_1LC0LF_0LC0LG_0RB---_0RB0RH".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_1RB0LD_1LE1LF_1LC0LF_0LC0LG_0RB1RI_0RB0RH_1RI1RI".
Definition l0 := [1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [52;2;90;28;41;57;75;48]%N.
Definition mp' := mp_from_list [52;34;74;12;25;57;91;48]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 61 61.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM7.


Module TM8.
Definition tm := TM_from_str "1LB1LD_0RC1RE_1LA0RD_0LE1LF_1RB0LA_0RC---".
Definition tm' := TM_from_str "1RB0LD_0RC---_1LD0RF_0LE1RD_0RA1LF_0LA1LB".
Definition tm0 := TM'_from_list [[Some(0,R,48);Some(0,R,52)];[Some(1,R,34);Some(0,R,48)];[Some(0,R,52);Some(1,L,25)];[Some(0,R,34);None];[Some(1,R,48);Some(1,R,52)];[Some(0,L,12);Some(1,R,48)];[Some(1,R,52);Some(1,L,57)];[None;None];[Some(0,L,25);Some(0,L,57)];[Some(0,L,27);Some(0,L,59)];[Some(0,L,29);Some(0,L,61)];[Some(0,L,31);Some(0,L,63)];[Some(1,L,25);Some(1,L,57)];[Some(1,L,27);Some(1,L,59)];[Some(1,L,29);Some(1,L,61)];[Some(1,L,31);Some(1,L,63)];[Some(0,R,32);Some(0,R,65)];[Some(0,R,34);Some(0,R,67)];[Some(0,R,36);Some(0,R,69)];[Some(0,R,38);Some(0,R,71)];[Some(1,R,32);Some(1,R,65)];[Some(1,R,34);Some(1,R,67)];[Some(1,R,36);Some(1,R,69)];[Some(1,R,38);Some(1,R,71)];[Some(0,L,27);Some(1,L,91)];[Some(1,L,74);Some(0,L,57)];[Some(0,L,31);Some(1,R,23)];[Some(0,R,34);Some(0,L,61)];[Some(1,L,27);Some(1,R,52)];[Some(0,R,52);Some(1,L,57)];[Some(1,L,31);None];[Some(0,R,48);Some(1,L,61)];[Some(0,R,48);Some(0,R,48)];[Some(1,R,48);Some(0,R,50)];[Some(1,L,74);Some(0,R,52)];[Some(0,R,48);Some(0,R,54)];[Some(1,R,48);Some(1,R,48)];[Some(1,L,12);Some(1,R,50)];[Some(1,L,91);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,9);Some(0,L,61)];[Some(0,L,11);Some(1,L,74)];[Some(0,L,13);Some(1,R,34)];[Some(0,L,15);Some(0,R,34)];[Some(1,L,9);Some(1,L,61)];[Some(1,L,11);Some(0,R,52)];[Some(1,L,13);Some(1,R,48)];[Some(1,L,15);Some(0,R,48)];[Some(0,R,34);Some(0,R,48)];[Some(1,L,74);None];[Some(0,R,38);Some(0,R,52)];[Some(0,L,74);None];[Some(1,R,34);Some(1,R,48)];[Some(0,L,57);None];[Some(1,R,38);Some(1,R,52)];[Some(0,L,91);None];[Some(0,L,72);Some(0,L,89)];[Some(0,L,74);Some(0,L,91)];[Some(0,L,76);Some(0,L,93)];[Some(0,L,78);Some(0,L,95)];[Some(1,L,72);Some(1,L,89)];[Some(1,L,74);Some(1,L,91)];[Some(1,L,76);Some(1,L,93)];[Some(1,L,78);Some(1,L,95)];[Some(0,R,17);Some(0,R,34)];[Some(0,R,19);Some(1,R,34)];[Some(0,R,21);Some(0,L,74)];[Some(0,R,23);Some(0,R,34)];[Some(1,R,17);Some(1,R,34)];[Some(1,R,19);Some(0,L,12)];[Some(1,R,21);Some(0,L,91)];[Some(1,R,23);None];[Some(0,L,61);Some(0,L,8)];[Some(1,R,38);Some(0,L,10)];[Some(1,R,34);Some(0,L,12)];[Some(0,L,91);Some(0,L,14)];[Some(1,L,61);Some(1,L,8)];[Some(1,R,71);Some(1,L,10)];[Some(1,R,48);Some(1,L,12)];[Some(1,L,91);Some(1,L,14)];[Some(0,R,32);None];[Some(0,R,34);None];[Some(0,R,36);None];[Some(0,R,38);None];[Some(1,R,32);None];[Some(1,R,34);None];[Some(1,R,36);None];[Some(1,R,38);None];[Some(0,L,27);None];[Some(1,L,74);None];[Some(0,L,31);None];[Some(0,R,34);None];[Some(1,L,27);None];[Some(0,R,52);None];[Some(1,L,31);None];[Some(0,R,48);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,34)];[Some(0,R,19);Some(1,R,34)];[Some(0,R,21);Some(0,L,10)];[Some(0,R,23);Some(0,R,34)];[Some(1,R,17);Some(1,R,34)];[Some(1,R,19);Some(0,L,60)];[Some(1,R,21);Some(0,L,27)];[Some(1,R,23);None];[Some(0,L,93);Some(0,L,56)];[None;Some(0,L,58)];[Some(1,R,34);Some(0,L,60)];[None;Some(0,L,62)];[Some(1,L,93);Some(1,L,56)];[None;Some(1,L,58)];[Some(1,R,80);Some(1,L,60)];[None;Some(1,L,62)];[Some(0,R,32);None];[Some(0,R,34);None];[Some(0,R,36);None];[Some(0,R,38);None];[Some(1,R,32);None];[Some(1,R,34);None];[Some(1,R,36);None];[Some(1,R,38);None];[Some(0,L,74);None];[Some(1,L,10);None];[Some(0,L,78);None];[Some(0,R,34);None];[Some(1,L,74);None];[Some(0,R,84);None];[Some(1,L,78);None];[Some(0,R,80);None];[None;Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(1,L,10);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[None;Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,L,27);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(0,L,57);Some(0,L,93)];[Some(0,L,59);Some(1,L,10)];[Some(0,L,61);Some(1,R,34)];[Some(0,L,63);Some(0,R,34)];[Some(1,L,57);Some(1,L,93)];[Some(1,L,59);Some(0,R,84)];[Some(1,L,61);Some(1,R,80)];[Some(1,L,63);Some(0,R,80)];[Some(0,R,17);Some(0,R,49)];[Some(1,R,34);Some(0,R,51)];[Some(0,R,21);Some(0,R,53)];[Some(0,R,34);Some(0,R,55)];[Some(1,R,17);Some(1,R,49)];[Some(0,L,60);Some(1,R,51)];[Some(1,R,21);Some(1,R,53)];[None;Some(1,R,55)];[Some(0,L,72);Some(0,L,89)];[Some(0,L,74);Some(0,L,27)];[Some(0,L,76);Some(0,L,93)];[Some(0,L,78);None];[Some(1,L,72);Some(1,L,89)];[Some(1,L,74);Some(1,L,27)];[Some(1,L,76);Some(1,L,93)];[Some(1,L,78);Some(1,R,55)];[Some(0,R,0);Some(0,R,84)];[Some(0,R,2);Some(0,R,80)];[Some(0,R,4);Some(1,L,72)];[Some(0,R,6);None];[Some(1,R,0);Some(1,R,84)];[Some(1,R,2);Some(1,R,80)];[Some(1,R,4);Some(1,L,89)];[Some(1,R,6);None];[Some(1,L,10);Some(0,L,89)];[Some(0,L,72);Some(0,L,91)];[None;Some(0,L,93)];[Some(0,L,76);Some(0,L,95)];[Some(0,R,84);Some(1,L,89)];[Some(1,L,72);Some(1,L,91)];[None;Some(1,L,93)];[Some(1,L,76);Some(1,L,95)];[Some(0,R,34);Some(0,R,80)];[Some(1,L,10);None];[Some(0,R,38);Some(0,R,84)];[Some(0,L,10);None];[Some(1,R,34);Some(1,R,80)];[Some(0,L,89);None];[Some(1,R,38);Some(1,R,84)];[Some(0,L,27);None];[Some(0,L,8);Some(0,L,25)];[Some(0,L,10);Some(0,L,27)];[Some(0,L,12);Some(0,L,29)];[Some(0,L,14);Some(0,L,31)];[Some(1,L,8);Some(1,L,25)];[Some(1,L,10);Some(1,L,27)];[Some(1,L,12);Some(1,L,29)];[Some(1,L,14);Some(1,L,31)]]%N.
Definition tm1 := TM'_from_str "1RB1RH_1LC0RA_1RB0LD_1LE1LF_1LC0LF_0LC0LG_0RB---_0RB0RH".
Definition tm2 := TM'_from_str "1RB1RH_1LC0RA_1RB0LD_1LE1LF_1LC0LF_0LC0LG_0RB1RI_0RB0RH_1RI1RI".
Definition l0 := [1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [52;34;74;12;25;57;91;48]%N.
Definition mp' := mp_from_list [84;34;10;60;72;89;27;80]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 7%N l0 (NG 0 1000 1000 1 1 0 0 false) 61 61.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM8.


Module TM9.
Definition tm := TM_from_str "1RB1RD_1LC1LA_0RA0LB_1LB0RE_0RF1RA_---1LD".
Definition tm' := TM_from_str "1RB1RD_1LC1LA_1RA0LB_1LB0RE_0RF1RA_---1LD".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,49)];[Some(0,R,19);Some(0,R,51)];[Some(0,R,21);Some(0,R,53)];[Some(0,R,23);Some(0,R,55)];[Some(1,R,17);Some(1,R,49)];[Some(1,R,19);Some(1,R,51)];[Some(1,R,21);Some(1,R,53)];[Some(1,R,23);Some(1,R,55)];[Some(0,L,26);Some(0,L,11)];[None;None];[Some(0,L,30);Some(0,L,15)];[Some(1,R,19);Some(1,R,19)];[Some(1,L,26);Some(1,L,11)];[Some(1,L,30);Some(1,L,30)];[Some(1,L,30);Some(1,L,15)];[Some(1,R,51);Some(1,R,51)];[Some(0,R,49);Some(0,R,66)];[Some(1,R,51);Some(0,R,66)];[Some(0,R,53);Some(0,R,70)];[Some(1,L,30);Some(0,R,70)];[Some(1,R,49);Some(1,R,66)];[Some(1,L,26);Some(1,R,66)];[Some(1,R,53);Some(1,R,70)];[Some(1,L,30);Some(1,R,70)];[Some(0,L,41);Some(0,L,9)];[Some(0,L,43);Some(0,L,11)];[Some(0,L,45);Some(0,L,13)];[Some(0,L,47);Some(0,L,15)];[Some(1,L,41);Some(1,L,9)];[Some(1,L,43);Some(1,L,11)];[Some(1,L,45);Some(1,L,13)];[Some(1,L,47);Some(1,L,15)];[Some(0,R,0);Some(0,R,5)];[Some(0,R,2);Some(0,R,84)];[Some(0,R,4);Some(0,L,45)];[Some(0,R,6);Some(0,R,84)];[Some(1,R,0);Some(1,R,5)];[Some(1,R,2);Some(1,R,84)];[Some(1,R,4);Some(0,L,13)];[Some(1,R,6);Some(1,R,84)];[Some(0,L,45);Some(0,L,24)];[Some(1,R,19);Some(0,L,26)];[Some(0,R,84);Some(0,L,28)];[Some(0,R,84);Some(0,L,30)];[Some(1,L,45);Some(1,L,24)];[Some(1,R,51);Some(1,L,26)];[Some(0,R,5);Some(1,L,28)];[Some(0,R,5);Some(1,L,30)];[Some(0,R,66);Some(0,R,64)];[Some(0,R,5);Some(0,R,66)];[Some(1,L,45);Some(0,R,68)];[Some(0,R,5);Some(0,R,70)];[Some(1,R,66);Some(1,R,64)];[Some(1,R,5);Some(1,R,66)];[Some(1,L,13);Some(1,R,68)];[Some(1,R,5);Some(1,R,70)];[Some(0,L,25);None];[Some(0,L,27);Some(1,L,30)];[Some(0,L,29);Some(0,L,47)];[Some(0,L,31);Some(0,R,5)];[Some(1,L,25);None];[Some(1,L,27);Some(0,R,70)];[Some(1,L,29);Some(1,L,47)];[Some(1,L,31);Some(0,R,70)];[Some(0,R,80);Some(0,R,1)];[Some(0,R,82);Some(0,R,3)];[Some(0,R,84);Some(0,R,5)];[Some(0,R,86);Some(0,R,7)];[Some(1,R,80);Some(1,R,1)];[Some(1,R,82);Some(1,R,3)];[Some(1,R,84);Some(1,R,5)];[Some(1,R,86);Some(1,R,7)];[None;Some(0,L,13)];[Some(0,L,27);Some(1,R,19)];[None;Some(1,R,84)];[Some(0,L,31);Some(1,R,84)];[None;Some(1,L,13)];[Some(1,L,27);Some(1,R,51)];[None;Some(1,R,5)];[Some(1,L,31);Some(1,R,5)];[None;Some(0,R,5)];[None;Some(0,R,1)];[None;Some(1,R,51)];[None;Some(0,R,5)];[None;Some(1,L,30)];[None;Some(1,R,1)];[None;Some(1,R,51)];[None;Some(1,R,5)];[None;Some(0,L,57)];[None;Some(0,L,59)];[None;Some(0,L,61)];[None;Some(0,L,63)];[None;Some(1,L,57)];[None;Some(1,L,59)];[None;Some(1,L,61)];[None;Some(1,L,63)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,49)];[Some(0,R,19);Some(0,R,51)];[Some(0,R,21);Some(0,R,53)];[Some(0,R,23);Some(0,R,55)];[Some(1,R,17);Some(1,R,49)];[Some(1,R,19);Some(1,R,51)];[Some(1,R,21);Some(1,R,53)];[Some(1,R,23);Some(1,R,55)];[Some(0,L,26);Some(0,L,11)];[None;None];[Some(0,L,30);Some(0,L,15)];[Some(1,R,19);Some(1,R,19)];[Some(1,L,26);Some(1,L,11)];[Some(1,L,30);Some(1,L,30)];[Some(1,L,30);Some(1,L,15)];[Some(1,R,51);Some(1,R,51)];[Some(0,R,51);Some(0,R,66)];[Some(1,R,51);Some(0,R,66)];[Some(0,R,55);Some(0,R,70)];[Some(1,L,30);Some(0,R,70)];[Some(1,R,51);Some(1,R,66)];[Some(1,L,26);Some(1,R,66)];[Some(1,R,55);Some(1,R,70)];[Some(1,L,30);Some(1,R,70)];[Some(0,L,41);Some(0,L,9)];[Some(0,L,43);Some(0,L,11)];[Some(0,L,45);Some(0,L,13)];[Some(0,L,47);Some(0,L,15)];[Some(1,L,41);Some(1,L,9)];[Some(1,L,43);Some(1,L,11)];[Some(1,L,45);Some(1,L,13)];[Some(1,L,47);Some(1,L,15)];[Some(0,R,1);Some(0,R,5)];[Some(0,R,3);Some(0,R,84)];[Some(0,R,5);Some(0,L,45)];[Some(0,R,7);Some(0,R,84)];[Some(1,R,1);Some(1,R,5)];[Some(1,R,3);Some(1,R,84)];[Some(1,R,5);Some(0,L,13)];[Some(1,R,7);Some(1,R,84)];[Some(0,L,13);Some(0,L,24)];[Some(1,R,19);Some(0,L,26)];[Some(1,R,84);Some(0,L,28)];[Some(1,R,84);Some(0,L,30)];[Some(1,L,13);Some(1,L,24)];[Some(1,R,51);Some(1,L,26)];[Some(1,R,5);Some(1,L,28)];[Some(1,R,5);Some(1,L,30)];[Some(0,R,70);Some(0,R,64)];[Some(0,R,5);Some(0,R,66)];[Some(1,L,45);Some(0,R,68)];[Some(0,R,5);Some(0,R,70)];[Some(1,R,70);Some(1,R,64)];[Some(1,R,5);Some(1,R,66)];[Some(1,L,13);Some(1,R,68)];[Some(1,R,5);Some(1,R,70)];[Some(0,L,25);None];[Some(0,L,27);Some(1,L,30)];[Some(0,L,29);Some(0,L,47)];[Some(0,L,31);Some(0,R,5)];[Some(1,L,25);None];[Some(1,L,27);Some(0,R,70)];[Some(1,L,29);Some(1,L,47)];[Some(1,L,31);Some(0,R,70)];[Some(0,R,80);Some(0,R,1)];[Some(0,R,82);Some(0,R,3)];[Some(0,R,84);Some(0,R,5)];[Some(0,R,86);Some(0,R,7)];[Some(1,R,80);Some(1,R,1)];[Some(1,R,82);Some(1,R,3)];[Some(1,R,84);Some(1,R,5)];[Some(1,R,86);Some(1,R,7)];[None;Some(0,L,13)];[Some(0,L,27);Some(1,R,19)];[None;Some(1,R,84)];[Some(0,L,31);Some(1,R,84)];[None;Some(1,L,13)];[Some(1,L,27);Some(1,R,51)];[None;Some(1,R,5)];[Some(1,L,31);Some(1,R,5)];[None;Some(1,R,5)];[None;Some(0,R,1)];[None;Some(1,R,51)];[None;Some(0,R,5)];[None;Some(1,L,30)];[None;Some(1,R,1)];[None;Some(1,R,51)];[None;Some(1,R,5)];[None;Some(0,L,57)];[None;Some(0,L,59)];[None;Some(0,L,61)];[None;Some(0,L,63)];[None;Some(1,L,57)];[None;Some(1,L,59)];[None;Some(1,L,61)];[None;Some(1,L,63)]]%N.
Definition tm1 := TM'_from_str "1RB1RG_1LC0RH_1LE1LD_1LC1LC_1RG1LF_0LE0LD_0RA0RH_1RI1RA_---1LC".
Definition tm2 := TM'_from_str "1RB1RG_1LC0RH_1LE1LD_1LC1LC_1RG1LF_0LE0LD_0RA0RH_1RI1RA_1RJ1LC_1RJ1RJ".
Definition l0 := [1;0;1;0;1;1;0;1;1;0;1;1;0;1;1;0]%N.
Definition mp := mp_from_list [5;19;30;13;45;26;51;70;84]%N.
Definition mp' := mp_from_list [5;19;30;13;45;26;51;70;84]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 61 61.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM9.


Module TM10.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD0LF_1RC---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0RD0RF_1LE---_1LF0LB_1LA0LE".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,20)];[Some(0,R,19);Some(1,L,11)];[Some(0,R,21);Some(1,L,15)];[Some(0,R,23);Some(1,L,78)];[Some(1,R,17);Some(1,R,20)];[Some(1,R,19);Some(1,L,74)];[Some(1,R,21);Some(1,L,78)];[Some(1,R,23);None];[Some(1,L,92);Some(0,L,57)];[Some(1,R,51);Some(0,L,59)];[Some(1,R,22);Some(0,L,61)];[Some(1,R,33);Some(0,L,63)];[None;Some(1,L,57)];[Some(1,R,50);Some(1,L,59)];[Some(0,L,92);Some(1,L,61)];[Some(1,R,16);Some(1,L,63)];[Some(0,R,33);Some(0,R,16)];[Some(0,R,35);Some(0,R,18)];[Some(0,R,37);Some(0,R,20)];[Some(0,R,39);Some(0,R,22)];[Some(1,R,33);Some(1,R,16)];[Some(1,R,35);Some(1,R,18)];[Some(1,R,37);Some(1,R,20)];[Some(1,R,39);Some(1,R,22)];[Some(0,L,78);Some(1,L,61)];[Some(1,R,37);Some(0,R,51)];[None;Some(0,R,22)];[Some(0,L,74);Some(0,R,33)];[Some(1,L,78);None];[Some(1,R,20);Some(0,R,50)];[None;Some(0,L,61)];[Some(1,L,74);Some(0,R,16)];[Some(0,R,49);Some(0,R,48)];[Some(0,R,51);Some(0,R,50)];[Some(0,R,53);Some(0,R,52)];[Some(0,R,55);Some(0,R,54)];[Some(1,R,49);Some(1,R,48)];[Some(1,R,51);Some(1,R,50)];[Some(1,R,53);Some(1,R,52)];[Some(1,R,55);Some(1,R,54)];[Some(0,L,59);Some(1,R,51)];[Some(0,L,88);Some(0,L,57)];[Some(0,L,63);Some(1,R,33)];[Some(0,L,92);Some(0,L,61)];[Some(1,L,59);Some(1,R,50)];[Some(1,L,88);Some(1,L,57)];[Some(1,L,63);Some(1,R,16)];[Some(1,L,92);Some(1,L,61)];[Some(0,R,18);Some(1,R,33)];[Some(1,R,16);Some(1,L,61)];[Some(0,R,22);Some(0,L,61)];[Some(1,L,61);None];[Some(1,R,18);Some(0,L,63)];[Some(1,L,63);Some(1,L,92)];[Some(1,R,22);Some(0,L,92)];[Some(1,L,92);None];[Some(0,L,9);Some(0,L,72)];[Some(0,L,11);Some(0,L,74)];[Some(0,L,13);Some(0,L,76)];[Some(0,L,15);Some(0,L,78)];[Some(1,L,9);Some(1,L,72)];[Some(1,L,11);Some(1,L,74)];[Some(1,L,13);Some(1,L,76)];[Some(1,L,15);Some(1,L,78)];[Some(0,R,20);Some(0,R,51)];[Some(1,L,11);None];[Some(1,L,15);Some(0,R,55)];[Some(1,L,78);None];[Some(1,R,20);Some(1,R,51)];[Some(1,L,74);None];[Some(1,L,78);Some(1,R,55)];[None;None];[Some(0,L,57);Some(0,L,88)];[Some(0,L,59);Some(0,L,90)];[Some(0,L,61);Some(0,L,92)];[Some(0,L,63);Some(0,L,94)];[Some(1,L,57);Some(1,L,88)];[Some(1,L,59);Some(1,L,90)];[Some(1,L,61);Some(1,L,92)];[Some(1,L,63);Some(1,L,94)];[Some(0,R,33);None];[Some(0,R,35);None];[Some(0,R,37);None];[Some(0,R,39);None];[Some(1,R,33);None];[Some(1,R,35);None];[Some(1,R,37);None];[Some(1,R,39);None];[Some(0,L,78);None];[Some(1,R,37);None];[None;None];[Some(0,L,74);None];[Some(1,L,78);None];[Some(1,R,20);None];[None;None];[Some(1,L,74);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,20)];[Some(0,R,19);Some(1,L,11)];[Some(0,R,21);Some(1,L,15)];[Some(0,R,23);Some(1,L,78)];[Some(1,R,17);Some(1,R,20)];[Some(1,R,19);Some(1,L,74)];[Some(1,R,21);Some(1,L,78)];[Some(1,R,23);None];[Some(1,L,28);Some(0,L,89)];[Some(1,R,50);Some(0,L,91)];[Some(1,R,22);Some(0,L,93)];[Some(1,R,33);Some(0,L,95)];[None;Some(1,L,89)];[Some(1,R,82);Some(1,L,91)];[Some(0,L,28);Some(1,L,93)];[Some(1,R,16);Some(1,L,95)];[Some(0,R,33);Some(0,R,16)];[Some(0,R,35);Some(0,R,18)];[Some(0,R,37);Some(0,R,20)];[Some(0,R,39);Some(0,R,22)];[Some(1,R,33);Some(1,R,16)];[Some(1,R,35);Some(1,R,18)];[Some(1,R,37);Some(1,R,20)];[Some(1,R,39);Some(1,R,22)];[Some(0,L,78);Some(1,L,93)];[Some(1,R,37);Some(0,R,50)];[None;Some(0,R,22)];[Some(0,L,74);Some(0,R,33)];[Some(1,L,78);None];[Some(1,R,20);Some(0,R,82)];[None;Some(0,L,93)];[Some(1,L,74);Some(0,R,16)];[Some(0,R,48);Some(0,R,80)];[Some(0,R,50);Some(0,R,82)];[Some(0,R,52);Some(0,R,84)];[Some(0,R,54);Some(0,R,86)];[Some(1,R,48);Some(1,R,80)];[Some(1,R,50);Some(1,R,82)];[Some(1,R,52);Some(1,R,84)];[Some(1,R,54);Some(1,R,86)];[Some(0,L,91);Some(1,R,50)];[None;Some(0,L,89)];[Some(0,L,95);Some(1,R,33)];[None;Some(0,L,93)];[Some(1,L,91);Some(1,R,82)];[None;Some(1,L,89)];[Some(1,L,95);Some(1,R,16)];[None;Some(1,L,93)];[Some(1,R,16);None];[None;None];[Some(1,L,93);None];[Some(0,R,82);None];[Some(1,L,95);None];[None;None];[Some(1,L,28);None];[Some(1,R,82);None];[Some(0,L,73);None];[Some(0,L,75);None];[Some(0,L,77);None];[Some(0,L,79);None];[Some(1,L,73);None];[Some(1,L,75);None];[Some(1,L,77);None];[Some(1,L,79);None];[Some(0,R,20);Some(0,R,50)];[Some(1,L,11);Some(0,R,33)];[Some(1,L,15);Some(0,R,54)];[Some(1,L,78);Some(0,R,37)];[Some(1,R,20);Some(1,R,50)];[Some(1,L,74);Some(1,R,33)];[Some(1,L,78);Some(1,R,54)];[None;Some(1,R,37)];[Some(0,L,89);Some(0,L,24)];[Some(0,L,91);Some(0,L,26)];[Some(0,L,93);Some(0,L,28)];[Some(0,L,95);Some(0,L,30)];[Some(1,L,89);Some(1,L,24)];[Some(1,L,91);Some(1,L,26)];[Some(1,L,93);Some(1,L,28)];[Some(1,L,95);Some(1,L,30)];[Some(0,R,18);Some(1,R,33)];[Some(1,R,16);Some(1,L,93)];[Some(0,R,22);Some(0,L,93)];[Some(1,L,93);Some(0,R,50)];[Some(1,R,18);Some(0,L,95)];[Some(1,L,95);Some(1,L,28)];[Some(1,R,22);Some(0,L,28)];[Some(1,L,28);Some(1,R,50)];[Some(0,L,9);Some(0,L,72)];[Some(0,L,11);Some(0,L,74)];[Some(0,L,13);Some(0,L,76)];[Some(0,L,15);Some(0,L,78)];[Some(1,L,9);Some(1,L,72)];[Some(1,L,11);Some(1,L,74)];[Some(1,L,13);Some(1,L,76)];[Some(1,L,15);Some(1,L,78)]]%N.
Definition tm1 := TM'_from_str "1RB1RI_1LC---_1LG1LD_0LC0LE_1LF---_1LC1LE_1RH0LJ_0RB0RI_0RM0LC_1LK1LF_1RL1LJ_0RH0RL_1RA1RN_1RH1RL".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RO_1LG1LD_0LC0LE_1LF1RO_1LC1LE_1RH0LJ_0RB0RI_0RM0LC_1LK1LF_1RL1LJ_0RH0RL_1RA1RN_1RH1RL_1RO1RO".
Definition l0 := [1;0;0;0;0;1;1;0;0;1;1;0;0;0;0;1]%N.
Definition mp := mp_from_list [37;51;61;74;92;78;11;33;50;63;15;16;22;20]%N.
Definition mp' := mp_from_list [37;50;93;74;28;78;11;33;82;95;15;16;22;20]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 64 64.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM10.


Module TM11.
Definition tm := TM_from_str "1LB0RB_0LC0RE_1LD0LF_1RB1LB_0RA1LB_1LD---".
Definition tm' := TM_from_str "1LB0RB_0LC0RE_1LD0LF_1RB1LB_0RA1LB_1LE---".
Definition tm0 := TM'_from_list [[Some(1,R,16);Some(0,R,16)];[Some(1,R,16);Some(0,R,18)];[Some(1,L,57);Some(0,R,20)];[Some(1,L,57);Some(0,R,22)];[Some(1,L,27);Some(1,R,16)];[Some(1,L,27);Some(1,R,18)];[None;Some(1,R,20)];[None;Some(1,R,22)];[Some(0,L,25);Some(0,L,57)];[Some(0,L,27);Some(1,R,16)];[Some(0,L,29);Some(0,L,61)];[Some(0,L,31);Some(0,L,61)];[Some(1,L,25);Some(1,L,57)];[Some(1,L,27);Some(0,R,16)];[Some(1,L,29);Some(1,L,61)];[Some(1,L,31);Some(1,L,61)];[Some(0,R,4);Some(0,R,64)];[Some(1,L,27);Some(0,R,66)];[Some(0,L,46);Some(0,R,68)];[None;Some(0,R,70)];[Some(1,R,4);Some(1,R,64)];[Some(0,L,27);Some(1,R,66)];[Some(0,L,46);Some(1,R,68)];[None;Some(1,R,70)];[Some(0,L,40);Some(0,L,61)];[Some(0,L,42);Some(0,L,42)];[Some(0,L,44);Some(0,R,4)];[Some(0,L,46);Some(0,L,46)];[Some(1,L,40);Some(1,L,61)];[Some(1,L,42);Some(1,L,42)];[Some(1,L,44);Some(0,R,64)];[Some(1,L,46);Some(1,L,46)];[Some(0,R,66);Some(0,R,4)];[Some(1,L,61);None];[Some(0,R,70);Some(0,L,46)];[Some(1,L,61);None];[Some(1,R,66);Some(1,R,4)];[Some(1,L,92);None];[Some(1,R,70);Some(0,L,46)];[Some(1,L,92);None];[Some(0,L,57);Some(0,L,88)];[Some(0,L,59);Some(0,L,90)];[Some(0,L,61);Some(0,L,92)];[Some(0,L,63);Some(0,L,94)];[Some(1,L,57);Some(1,L,88)];[Some(1,L,59);Some(1,L,90)];[Some(1,L,61);Some(1,L,92)];[Some(1,L,63);Some(1,L,94)];[Some(0,R,17);Some(1,R,16)];[Some(0,R,19);Some(1,R,16)];[Some(0,R,21);Some(1,L,57)];[Some(0,R,23);Some(1,L,57)];[Some(1,R,17);Some(1,L,27)];[Some(1,R,19);Some(1,L,27)];[Some(1,R,21);None];[Some(1,R,23);None];[Some(0,L,88);Some(0,L,25)];[Some(1,L,27);Some(0,L,27)];[Some(0,L,92);Some(0,L,29)];[Some(0,L,92);Some(0,L,31)];[Some(1,L,88);Some(1,L,25)];[Some(1,R,16);Some(1,L,27)];[Some(1,L,92);Some(1,L,29)];[Some(1,L,92);Some(1,L,31)];[Some(0,R,0);Some(1,R,16)];[Some(0,R,2);Some(1,R,16)];[Some(0,R,4);Some(1,L,57)];[Some(0,R,6);Some(1,L,57)];[Some(1,R,0);Some(1,L,27)];[Some(1,R,2);Some(1,L,27)];[Some(1,R,4);None];[Some(1,R,6);None];[Some(0,L,42);Some(0,L,25)];[Some(1,L,27);Some(0,L,27)];[Some(0,L,46);Some(0,L,29)];[Some(0,R,0);Some(0,L,31)];[Some(1,L,42);Some(1,L,25)];[Some(1,R,16);Some(1,L,27)];[Some(1,L,46);Some(1,L,29)];[Some(1,R,16);Some(1,L,31)];[Some(0,R,66);None];[Some(1,L,61);None];[Some(0,R,70);None];[Some(1,L,61);None];[Some(1,R,66);None];[Some(1,L,92);None];[Some(1,R,70);None];[Some(1,L,92);None];[Some(0,L,57);None];[Some(0,L,59);None];[Some(0,L,61);None];[Some(0,L,63);None];[Some(1,L,57);None];[Some(1,L,59);None];[Some(1,L,61);None];[Some(1,L,63);None]]%N.
Definition tm0' := TM'_from_list [[Some(1,R,16);Some(0,R,16)];[Some(1,R,16);Some(0,R,18)];[Some(1,L,73);Some(0,R,20)];[Some(1,L,73);Some(0,R,22)];[Some(1,L,27);Some(1,R,16)];[Some(1,L,27);Some(1,R,18)];[None;Some(1,R,20)];[None;Some(1,R,22)];[Some(0,L,25);Some(0,L,57)];[Some(0,L,27);Some(1,R,16)];[Some(0,L,29);Some(0,L,61)];[Some(0,L,31);Some(0,L,61)];[Some(1,L,25);Some(1,L,57)];[Some(1,L,27);Some(0,R,16)];[Some(1,L,29);Some(1,L,61)];[Some(1,L,31);Some(1,L,61)];[Some(0,R,4);Some(0,R,64)];[Some(1,L,27);Some(0,R,66)];[Some(0,L,46);Some(0,R,68)];[None;Some(0,R,70)];[Some(1,R,4);Some(1,R,64)];[Some(0,L,27);Some(1,R,66)];[Some(0,L,46);Some(1,R,68)];[None;Some(1,R,70)];[Some(0,L,40);Some(0,L,61)];[Some(0,L,42);Some(0,L,42)];[Some(0,L,44);Some(0,R,4)];[Some(0,L,46);Some(0,L,46)];[Some(1,L,40);Some(1,L,61)];[Some(1,L,42);Some(1,L,42)];[Some(1,L,44);Some(0,R,64)];[Some(1,L,46);Some(1,L,46)];[Some(0,R,66);Some(0,R,4)];[Some(1,L,61);None];[Some(0,R,70);Some(0,L,46)];[Some(1,L,61);None];[Some(1,R,66);Some(1,R,4)];[Some(1,L,92);None];[Some(1,R,70);Some(0,L,46)];[Some(1,L,92);None];[Some(0,L,57);Some(0,L,88)];[Some(0,L,59);Some(0,L,90)];[Some(0,L,61);Some(0,L,92)];[Some(0,L,63);Some(0,L,94)];[Some(1,L,57);Some(1,L,88)];[Some(1,L,59);Some(1,L,90)];[Some(1,L,61);Some(1,L,92)];[Some(1,L,63);Some(1,L,94)];[Some(0,R,17);Some(1,R,16)];[Some(0,R,19);Some(1,R,16)];[Some(0,R,21);Some(1,L,73)];[Some(0,R,23);Some(1,L,73)];[Some(1,R,17);Some(1,L,27)];[Some(1,R,19);Some(1,L,27)];[Some(1,R,21);None];[Some(1,R,23);None];[Some(0,L,88);Some(0,L,25)];[Some(1,L,27);Some(0,L,27)];[Some(0,L,92);Some(0,L,29)];[Some(0,L,92);Some(0,L,31)];[Some(1,L,88);Some(1,L,25)];[Some(1,R,16);Some(1,L,27)];[Some(1,L,92);Some(1,L,29)];[Some(1,L,92);Some(1,L,31)];[Some(0,R,0);Some(1,R,16)];[Some(0,R,2);Some(1,R,16)];[Some(0,R,4);Some(1,L,73)];[Some(0,R,6);Some(1,L,73)];[Some(1,R,0);Some(1,L,27)];[Some(1,R,2);Some(1,L,27)];[Some(1,R,4);None];[Some(1,R,6);None];[Some(0,L,42);Some(0,L,25)];[Some(1,L,27);Some(0,L,27)];[Some(0,L,46);Some(0,L,29)];[Some(0,R,0);Some(0,L,31)];[Some(1,L,42);Some(1,L,25)];[Some(1,R,16);Some(1,L,27)];[Some(1,L,46);Some(1,L,29)];[Some(1,R,16);Some(1,L,31)];[Some(0,R,16);None];[Some(1,L,61);None];[Some(0,R,20);None];[Some(1,L,61);None];[Some(1,R,16);None];[Some(1,L,92);None];[Some(1,R,20);None];[Some(1,L,92);None];[Some(0,L,73);None];[Some(0,L,75);None];[Some(0,L,77);None];[Some(0,L,79);None];[Some(1,L,73);None];[Some(1,L,75);None];[Some(1,L,77);None];[Some(1,L,79);None]]%N.
Definition tm1 := TM'_from_str "1LB1RG_0LC0LC_1LF1LD_1LE---_1LB0LB_1RG1LB_0RA0RH_0RI1RG_1RG0RG".
Definition tm2 := TM'_from_str "1LB1RG_0LC0LC_1LF1LD_1LE1RJ_1LB0LB_1RG1LB_0RA0RH_0RI1RG_1RG0RG_1RJ1RJ".
Definition l0 := [1;0;0;1;0;0;0;0;1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [4;27;46;92;57;61;16;64;0]%N.
Definition mp' := mp_from_list [4;27;46;92;73;61;16;64;0]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 78 78.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM11.


Module TM12.
Definition tm := TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_1RD0LA_---0RB".
Definition tm' := TM_from_str "1LB0LF_1RC1LD_1RA1RC_1LA1LE_0LB0RD_---0RC".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(1,R,23)];[Some(0,R,19);Some(1,R,33)];[Some(0,R,21);None];[Some(0,R,23);Some(1,R,33)];[Some(1,R,17);Some(1,L,63)];[Some(1,R,19);Some(1,L,61)];[Some(1,R,21);Some(0,R,33)];[Some(1,R,23);Some(1,L,61)];[Some(0,L,79);Some(0,L,57)];[Some(1,L,14);Some(0,L,59)];[Some(1,L,94);Some(0,L,61)];[Some(1,R,39);Some(0,L,63)];[Some(1,L,79);Some(1,L,57)];[Some(1,R,37);Some(1,L,59)];[Some(1,R,33);Some(1,L,61)];[Some(1,R,23);Some(1,L,63)];[Some(0,R,33);Some(0,R,17)];[Some(0,R,35);Some(0,R,19)];[Some(0,R,37);Some(0,R,21)];[Some(0,R,39);Some(0,R,23)];[Some(1,R,33);Some(1,R,17)];[Some(1,R,35);Some(1,R,19)];[Some(1,R,37);Some(1,R,21)];[Some(1,R,39);Some(1,R,23)];[Some(0,L,59);Some(0,L,79)];[Some(0,L,47);Some(1,L,14)];[Some(0,L,63);Some(1,L,94)];[Some(1,L,15);Some(1,R,39)];[Some(1,L,59);Some(1,L,79)];[Some(1,L,47);Some(1,R,37)];[Some(1,L,63);Some(1,R,33)];[Some(0,R,33);Some(1,R,23)];[Some(0,R,19);None];[Some(1,L,15);Some(0,R,33)];[Some(0,R,23);None];[Some(1,L,14);Some(0,R,37)];[Some(1,R,19);None];[Some(1,L,94);Some(1,R,33)];[Some(1,R,23);None];[Some(1,L,14);Some(1,R,37)];[Some(0,L,9);Some(0,L,88)];[Some(0,L,11);Some(0,L,90)];[Some(0,L,13);Some(0,L,92)];[Some(0,L,15);Some(0,L,94)];[Some(1,L,9);Some(1,L,88)];[Some(1,L,11);Some(1,L,90)];[Some(1,L,13);Some(1,L,92)];[Some(1,L,15);Some(1,L,94)];[Some(0,R,23);Some(0,R,37)];[None;Some(0,R,37)];[Some(1,L,47);Some(1,L,43)];[Some(0,R,33);Some(1,L,43)];[Some(1,R,23);Some(1,R,37)];[None;Some(1,R,37)];[Some(1,L,79);Some(1,L,75)];[Some(1,R,33);Some(1,L,75)];[Some(0,L,41);Some(0,L,73)];[Some(0,L,43);Some(0,L,75)];[Some(0,L,45);Some(0,L,77)];[Some(0,L,47);Some(0,L,79)];[Some(1,L,41);Some(1,L,73)];[Some(1,L,43);Some(1,L,75)];[Some(1,L,45);Some(1,L,77)];[Some(1,L,47);Some(1,L,79)];[Some(0,R,49);Some(0,R,35)];[Some(0,R,51);Some(0,L,15)];[Some(0,R,53);Some(0,R,39)];[Some(0,R,55);Some(0,L,14)];[Some(1,R,49);Some(1,R,35)];[Some(1,R,51);Some(0,L,94)];[Some(1,R,53);Some(1,R,39)];[Some(1,R,55);Some(0,L,14)];[Some(0,L,90);Some(0,L,8)];[Some(0,L,10);Some(0,L,10)];[Some(0,L,94);Some(0,L,12)];[Some(0,L,14);Some(0,L,14)];[Some(1,L,90);Some(1,L,8)];[Some(1,L,10);Some(1,L,10)];[Some(1,L,94);Some(1,L,12)];[Some(1,L,14);Some(1,L,14)];[None;Some(0,R,16)];[None;Some(0,R,18)];[None;Some(0,R,20)];[None;Some(0,R,22)];[None;Some(1,R,16)];[None;Some(1,R,18)];[None;Some(1,R,20)];[None;Some(1,R,22)];[None;Some(0,L,47)];[None;Some(1,L,14)];[None;Some(1,L,15)];[None;Some(0,R,39)];[None;Some(1,L,47)];[None;Some(0,R,37)];[None;Some(0,R,33)];[None;Some(0,R,23)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,35);None];[Some(1,L,31);Some(0,R,1)];[Some(0,R,39);None];[Some(1,L,30);Some(0,R,5)];[Some(1,R,35);None];[Some(1,L,94);Some(1,R,1)];[Some(1,R,39);None];[Some(1,L,30);Some(1,R,5)];[Some(0,L,25);Some(0,L,88)];[Some(0,L,27);Some(0,L,90)];[Some(0,L,29);Some(0,L,92)];[Some(0,L,31);Some(0,L,94)];[Some(1,L,25);Some(1,L,88)];[Some(1,L,27);Some(1,L,90)];[Some(1,L,29);Some(1,L,92)];[Some(1,L,31);Some(1,L,94)];[Some(0,R,33);Some(1,R,39)];[Some(0,R,35);Some(1,R,1)];[Some(0,R,37);None];[Some(0,R,39);Some(1,R,1)];[Some(1,R,33);Some(1,L,63)];[Some(1,R,35);Some(1,L,61)];[Some(1,R,37);Some(0,R,1)];[Some(1,R,39);Some(1,L,61)];[Some(0,L,79);Some(0,L,57)];[Some(1,L,30);Some(0,L,59)];[Some(1,L,94);Some(0,L,61)];[Some(1,R,7);Some(0,L,63)];[Some(1,L,79);Some(1,L,57)];[Some(1,R,5);Some(1,L,59)];[Some(1,R,1);Some(1,L,61)];[Some(1,R,39);Some(1,L,63)];[Some(0,R,1);Some(0,R,33)];[Some(0,R,3);Some(0,R,35)];[Some(0,R,5);Some(0,R,37)];[Some(0,R,7);Some(0,R,39)];[Some(1,R,1);Some(1,R,33)];[Some(1,R,3);Some(1,R,35)];[Some(1,R,5);Some(1,R,37)];[Some(1,R,7);Some(1,R,39)];[Some(0,L,59);Some(0,L,79)];[Some(0,L,15);Some(1,L,30)];[Some(0,L,63);Some(1,L,94)];[Some(1,L,31);Some(1,R,7)];[Some(1,L,59);Some(1,L,79)];[Some(1,L,15);Some(1,R,5)];[Some(1,L,63);Some(1,R,1)];[Some(0,R,1);Some(1,R,39)];[Some(0,R,39);Some(0,R,5)];[None;Some(0,R,5)];[Some(1,L,15);Some(1,L,11)];[Some(0,R,1);Some(1,L,11)];[Some(1,R,39);Some(1,R,5)];[None;Some(1,R,5)];[Some(1,L,79);Some(1,L,75)];[Some(1,R,1);Some(1,L,75)];[Some(0,L,9);Some(0,L,73)];[Some(0,L,11);Some(0,L,75)];[Some(0,L,13);Some(0,L,77)];[Some(0,L,15);Some(0,L,79)];[Some(1,L,9);Some(1,L,73)];[Some(1,L,11);Some(1,L,75)];[Some(1,L,13);Some(1,L,77)];[Some(1,L,15);Some(1,L,79)];[Some(0,R,3);Some(0,R,48)];[Some(0,L,31);Some(0,R,50)];[Some(0,R,7);Some(0,R,52)];[Some(0,L,30);Some(0,R,54)];[Some(1,R,3);Some(1,R,48)];[Some(0,L,94);Some(1,R,50)];[Some(1,R,7);Some(1,R,52)];[Some(0,L,30);Some(1,R,54)];[Some(0,L,24);Some(0,L,27)];[Some(0,L,26);Some(0,L,26)];[Some(0,L,28);Some(0,L,31)];[Some(0,L,30);Some(0,L,30)];[Some(1,L,24);Some(1,L,27)];[Some(1,L,26);Some(1,L,26)];[Some(1,L,28);Some(1,L,31)];[Some(1,L,30);Some(1,L,30)];[None;Some(0,R,32)];[None;Some(0,R,34)];[None;Some(0,R,36)];[None;Some(0,R,38)];[None;Some(1,R,32)];[None;Some(1,R,34)];[None;Some(1,R,36)];[None;Some(1,R,38)];[None;Some(0,L,15)];[None;Some(1,L,30)];[None;Some(1,L,31)];[None;Some(0,R,7)];[None;Some(1,L,15)];[None;Some(0,R,5)];[None;Some(0,R,1)];[None;Some(0,R,39)]]%N.
Definition tm1 := TM'_from_str "1LB0RA_1RC1LJ_1RD1RC_1LE1RI_1RA1LF_1LH1LG_0LE0LE_0LB0LM_1LM1RA_1LL1LK_1LE1LE_1LB1LM_---0RA".
Definition tm2 := TM'_from_str "1LB0RA_1RC1LJ_1RD1RC_1LE1RI_1RA1LF_1LH1LG_0LE0LE_0LB0LM_1LM1RA_1LL1LK_1LE1LE_1LB1LM_1RN0RA_1RN1RN".
Definition l0 := [1;1;0;0;0;0;0;0;1;1;1;1;1;1;1;0]%N.
Definition mp := mp_from_list [33;15;23;39;14;61;75;43;37;63;79;47;94]%N.
Definition mp' := mp_from_list [1;31;39;7;30;61;75;11;5;63;79;15;94]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 12%N l0 (NG 0 1000 1000 1 1 0 0 false) 91 91.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM12.


Module TM13.
Definition tm := TM_from_str "1RB0RA_0RC0RE_1LD---_1LE0LA_1LF0LD_1RA1LE".
Definition tm' := TM_from_str "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_1RB---".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,0)];[Some(0,R,19);Some(0,R,2)];[Some(0,R,21);Some(0,R,4)];[Some(0,R,23);Some(0,R,6)];[Some(1,R,17);Some(1,R,0)];[Some(1,R,19);Some(1,R,2)];[Some(1,R,21);Some(1,R,4)];[Some(1,R,23);Some(1,R,6)];[Some(0,L,62);Some(1,L,77)];[Some(1,R,21);Some(0,R,34)];[None;Some(0,R,6)];[Some(0,L,58);Some(0,R,17)];[Some(1,L,62);None];[Some(1,R,4);Some(0,R,66)];[None;Some(0,L,77)];[Some(1,L,58);Some(0,R,0)];[Some(0,R,32);Some(0,R,64)];[Some(0,R,34);Some(0,R,66)];[Some(0,R,36);Some(0,R,68)];[Some(0,R,38);Some(0,R,70)];[Some(1,R,32);Some(1,R,64)];[Some(1,R,34);Some(1,R,66)];[Some(1,R,36);Some(1,R,68)];[Some(1,R,38);Some(1,R,70)];[Some(0,L,75);Some(1,R,34)];[None;Some(0,L,73)];[Some(0,L,79);Some(1,R,17)];[None;Some(0,L,77)];[Some(1,L,75);Some(1,R,66)];[None;Some(1,L,73)];[Some(1,L,79);Some(1,R,0)];[None;Some(1,L,77)];[Some(1,R,0);None];[None;None];[Some(1,L,77);None];[Some(0,R,66);None];[Some(1,L,79);None];[None;None];[Some(1,L,12);None];[Some(1,R,66);None];[Some(0,L,57);None];[Some(0,L,59);None];[Some(0,L,61);None];[Some(0,L,63);None];[Some(1,L,57);None];[Some(1,L,59);None];[Some(1,L,61);None];[Some(1,L,63);None];[Some(0,R,4);Some(0,R,34)];[Some(1,L,91);Some(0,R,17)];[Some(1,L,95);Some(0,R,38)];[Some(1,L,62);Some(0,R,21)];[Some(1,R,4);Some(1,R,34)];[Some(1,L,58);Some(1,R,17)];[Some(1,L,62);Some(1,R,38)];[None;Some(1,R,21)];[Some(0,L,73);Some(0,L,8)];[Some(0,L,75);Some(0,L,10)];[Some(0,L,77);Some(0,L,12)];[Some(0,L,79);Some(0,L,14)];[Some(1,L,73);Some(1,L,8)];[Some(1,L,75);Some(1,L,10)];[Some(1,L,77);Some(1,L,12)];[Some(1,L,79);Some(1,L,14)];[Some(0,R,2);Some(1,R,17)];[Some(1,R,0);Some(1,L,77)];[Some(0,R,6);Some(0,L,77)];[Some(1,L,77);Some(0,R,34)];[Some(1,R,2);Some(0,L,79)];[Some(1,L,79);Some(1,L,12)];[Some(1,R,6);Some(0,L,12)];[Some(1,L,12);Some(1,R,34)];[Some(0,L,89);Some(0,L,56)];[Some(0,L,91);Some(0,L,58)];[Some(0,L,93);Some(0,L,60)];[Some(0,L,95);Some(0,L,62)];[Some(1,L,89);Some(1,L,56)];[Some(1,L,91);Some(1,L,58)];[Some(1,L,93);Some(1,L,60)];[Some(1,L,95);Some(1,L,62)];[Some(0,R,1);Some(0,R,4)];[Some(0,R,3);Some(1,L,91)];[Some(0,R,5);Some(1,L,95)];[Some(0,R,7);Some(1,L,62)];[Some(1,R,1);Some(1,R,4)];[Some(1,R,3);Some(1,L,58)];[Some(1,R,5);Some(1,L,62)];[Some(1,R,7);None];[Some(1,L,12);Some(0,L,73)];[Some(1,R,34);Some(0,L,75)];[Some(1,R,6);Some(0,L,77)];[Some(1,R,17);Some(0,L,79)];[None;Some(1,L,73)];[Some(1,R,66);Some(1,L,75)];[Some(0,L,12);Some(1,L,77)];[Some(1,R,0);Some(1,L,79)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,0)];[Some(0,R,19);Some(0,R,2)];[Some(0,R,21);Some(0,R,4)];[Some(0,R,23);Some(0,R,6)];[Some(1,R,17);Some(1,R,0)];[Some(1,R,19);Some(1,R,2)];[Some(1,R,21);Some(1,R,4)];[Some(1,R,23);Some(1,R,6)];[Some(0,L,78);Some(1,L,45)];[Some(1,R,21);Some(0,R,35)];[None;Some(0,R,6)];[Some(0,L,74);Some(0,R,17)];[Some(1,L,78);None];[Some(1,R,4);Some(0,R,34)];[None;Some(0,L,45)];[Some(1,L,74);Some(0,R,0)];[Some(0,R,33);Some(0,R,32)];[Some(0,R,35);Some(0,R,34)];[Some(0,R,37);Some(0,R,36)];[Some(0,R,39);Some(0,R,38)];[Some(1,R,33);Some(1,R,32)];[Some(1,R,35);Some(1,R,34)];[Some(1,R,37);Some(1,R,36)];[Some(1,R,39);Some(1,R,38)];[Some(0,L,43);Some(1,R,35)];[Some(0,L,88);Some(0,L,41)];[Some(0,L,47);Some(1,R,17)];[Some(0,L,92);Some(0,L,45)];[Some(1,L,43);Some(1,R,34)];[Some(1,L,88);Some(1,L,41)];[Some(1,L,47);Some(1,R,0)];[Some(1,L,92);Some(1,L,45)];[Some(0,R,2);Some(1,R,17)];[Some(1,R,0);Some(1,L,45)];[Some(0,R,6);Some(0,L,45)];[Some(1,L,45);None];[Some(1,R,2);Some(0,L,47)];[Some(1,L,47);Some(1,L,92)];[Some(1,R,6);Some(0,L,92)];[Some(1,L,92);None];[Some(0,L,57);Some(0,L,72)];[Some(0,L,59);Some(0,L,74)];[Some(0,L,61);Some(0,L,76)];[Some(0,L,63);Some(0,L,78)];[Some(1,L,57);Some(1,L,72)];[Some(1,L,59);Some(1,L,74)];[Some(1,L,61);Some(1,L,76)];[Some(1,L,63);Some(1,L,78)];[Some(0,R,1);Some(0,R,4)];[Some(0,R,3);Some(1,L,59)];[Some(0,R,5);Some(1,L,63)];[Some(0,R,7);Some(1,L,78)];[Some(1,R,1);Some(1,R,4)];[Some(1,R,3);Some(1,L,74)];[Some(1,R,5);Some(1,L,78)];[Some(1,R,7);None];[Some(1,L,92);Some(0,L,41)];[Some(1,R,35);Some(0,L,43)];[Some(1,R,6);Some(0,L,45)];[Some(1,R,17);Some(0,L,47)];[None;Some(1,L,41)];[Some(1,R,34);Some(1,L,43)];[Some(0,L,92);Some(1,L,45)];[Some(1,R,0);Some(1,L,47)];[Some(0,R,4);Some(0,R,35)];[Some(1,L,59);None];[Some(1,L,63);Some(0,R,39)];[Some(1,L,78);None];[Some(1,R,4);Some(1,R,35)];[Some(1,L,74);None];[Some(1,L,78);Some(1,R,39)];[None;None];[Some(0,L,41);Some(0,L,88)];[Some(0,L,43);Some(0,L,90)];[Some(0,L,45);Some(0,L,92)];[Some(0,L,47);Some(0,L,94)];[Some(1,L,41);Some(1,L,88)];[Some(1,L,43);Some(1,L,90)];[Some(1,L,45);Some(1,L,92)];[Some(1,L,47);Some(1,L,94)];[Some(0,R,17);None];[Some(0,R,19);None];[Some(0,R,21);None];[Some(0,R,23);None];[Some(1,R,17);None];[Some(1,R,19);None];[Some(1,R,21);None];[Some(1,R,23);None];[Some(0,L,78);None];[Some(1,R,21);None];[None;None];[Some(0,L,74);None];[Some(1,L,78);None];[Some(1,R,4);None];[None;None];[Some(1,L,74);None]]%N.
Definition tm1 := TM'_from_str "1RB1RI_1LC---_1LG1LD_0LC0LE_1LF---_1LC1LE_1RH0LJ_0RB0RI_0RK0LC_1LN1LF_1RA1RL_1RH1RM_0RH0RM_1RM1LJ".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RO_1LG1LD_0LC0LE_1LF1RO_1LC1LE_1RH0LJ_0RB0RI_0RK0LC_1LN1LF_1RA1RL_1RH1RM_0RH0RM_1RM1LJ_1RO1RO".
Definition l0 := [1;0;1;0;0;0;0;1;1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_list [21;34;77;58;12;62;91;17;66;79;6;4;0;95]%N.
Definition mp' := mp_from_list [21;35;45;74;92;78;59;17;34;47;6;4;0;63]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 103 103.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM13.


Module TM14.
Definition tm := TM_from_str "1LB0LD_1LC0LA_1RD1LB_1RE0RD_0RF0RB_1LA---".
Definition tm' := TM_from_str "1LB0LF_1LC0LA_1RD1LB_1RE0RD_1RB0RB_1RE---".
Definition tm0 := TM'_from_list [[Some(0,R,52);Some(0,R,82)];[Some(1,L,43);Some(0,R,65)];[Some(1,L,47);Some(0,R,86)];[Some(1,L,14);Some(0,R,69)];[Some(1,R,52);Some(1,R,82)];[Some(1,L,10);Some(1,R,65)];[Some(1,L,14);Some(1,R,86)];[None;Some(1,R,69)];[Some(0,L,25);Some(0,L,56)];[Some(0,L,27);Some(0,L,58)];[Some(0,L,29);Some(0,L,60)];[Some(0,L,31);Some(0,L,62)];[Some(1,L,25);Some(1,L,56)];[Some(1,L,27);Some(1,L,58)];[Some(1,L,29);Some(1,L,60)];[Some(1,L,31);Some(1,L,62)];[Some(0,R,50);Some(1,R,65)];[Some(1,R,48);Some(1,L,29)];[Some(0,R,54);Some(0,L,29)];[Some(1,L,29);Some(0,R,82)];[Some(1,R,50);Some(0,L,31)];[Some(1,L,31);Some(1,L,60)];[Some(1,R,54);Some(0,L,60)];[Some(1,L,60);Some(1,R,82)];[Some(0,L,41);Some(0,L,8)];[Some(0,L,43);Some(0,L,10)];[Some(0,L,45);Some(0,L,12)];[Some(0,L,47);Some(0,L,14)];[Some(1,L,41);Some(1,L,8)];[Some(1,L,43);Some(1,L,10)];[Some(1,L,45);Some(1,L,12)];[Some(1,L,47);Some(1,L,14)];[Some(0,R,49);Some(0,R,52)];[Some(0,R,51);Some(1,L,43)];[Some(0,R,53);Some(1,L,47)];[Some(0,R,55);Some(1,L,14)];[Some(1,R,49);Some(1,R,52)];[Some(1,R,51);Some(1,L,10)];[Some(1,R,53);Some(1,L,14)];[Some(1,R,55);None];[Some(1,L,60);Some(0,L,25)];[Some(1,R,82);Some(0,L,27)];[Some(1,R,54);Some(0,L,29)];[Some(1,R,65);Some(0,L,31)];[None;Some(1,L,25)];[Some(1,R,18);Some(1,L,27)];[Some(0,L,60);Some(1,L,29)];[Some(1,R,48);Some(1,L,31)];[Some(0,R,65);Some(0,R,48)];[Some(0,R,67);Some(0,R,50)];[Some(0,R,69);Some(0,R,52)];[Some(0,R,71);Some(0,R,54)];[Some(1,R,65);Some(1,R,48)];[Some(1,R,67);Some(1,R,50)];[Some(1,R,69);Some(1,R,52)];[Some(1,R,71);Some(1,R,54)];[Some(0,L,14);Some(1,L,29)];[Some(1,R,69);Some(0,R,82)];[None;Some(0,R,54)];[Some(0,L,10);Some(0,R,65)];[Some(1,L,14);None];[Some(1,R,52);Some(0,R,18)];[None;Some(0,L,29)];[Some(1,L,10);Some(0,R,48)];[Some(0,R,80);Some(0,R,16)];[Some(0,R,82);Some(0,R,18)];[Some(0,R,84);Some(0,R,20)];[Some(0,R,86);Some(0,R,22)];[Some(1,R,80);Some(1,R,16)];[Some(1,R,82);Some(1,R,18)];[Some(1,R,84);Some(1,R,20)];[Some(1,R,86);Some(1,R,22)];[Some(0,L,27);Some(1,R,82)];[None;Some(0,L,25)];[Some(0,L,31);Some(1,R,65)];[None;Some(0,L,29)];[Some(1,L,27);Some(1,R,18)];[None;Some(1,L,25)];[Some(1,L,31);Some(1,R,48)];[None;Some(1,L,29)];[Some(1,R,48);None];[None;None];[Some(1,L,29);None];[Some(0,R,18);None];[Some(1,L,31);None];[None;None];[Some(1,L,60);None];[Some(1,R,18);None];[Some(0,L,9);None];[Some(0,L,11);None];[Some(0,L,13);None];[Some(0,L,15);None];[Some(1,L,9);None];[Some(1,L,11);None];[Some(1,L,13);None];[Some(1,L,15);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,52);Some(0,R,19)];[Some(1,L,43);None];[Some(1,L,47);Some(0,R,23)];[Some(1,L,14);None];[Some(1,R,52);Some(1,R,19)];[Some(1,L,10);None];[Some(1,L,14);Some(1,R,23)];[None;None];[Some(0,L,25);Some(0,L,88)];[Some(0,L,27);Some(0,L,90)];[Some(0,L,29);Some(0,L,92)];[Some(0,L,31);Some(0,L,94)];[Some(1,L,25);Some(1,L,88)];[Some(1,L,27);Some(1,L,90)];[Some(1,L,29);Some(1,L,92)];[Some(1,L,31);Some(1,L,94)];[Some(0,R,50);Some(1,R,65)];[Some(1,R,48);Some(1,L,29)];[Some(0,R,54);Some(0,L,29)];[Some(1,L,29);None];[Some(1,R,50);Some(0,L,31)];[Some(1,L,31);Some(1,L,92)];[Some(1,R,54);Some(0,L,92)];[Some(1,L,92);None];[Some(0,L,41);Some(0,L,8)];[Some(0,L,43);Some(0,L,10)];[Some(0,L,45);Some(0,L,12)];[Some(0,L,47);Some(0,L,14)];[Some(1,L,41);Some(1,L,8)];[Some(1,L,43);Some(1,L,10)];[Some(1,L,45);Some(1,L,12)];[Some(1,L,47);Some(1,L,14)];[Some(0,R,49);Some(0,R,52)];[Some(0,R,51);Some(1,L,43)];[Some(0,R,53);Some(1,L,47)];[Some(0,R,55);Some(1,L,14)];[Some(1,R,49);Some(1,R,52)];[Some(1,R,51);Some(1,L,10)];[Some(1,R,53);Some(1,L,14)];[Some(1,R,55);None];[Some(1,L,92);Some(0,L,25)];[Some(1,R,19);Some(0,L,27)];[Some(1,R,54);Some(0,L,29)];[Some(1,R,65);Some(0,L,31)];[None;Some(1,L,25)];[Some(1,R,18);Some(1,L,27)];[Some(0,L,92);Some(1,L,29)];[Some(1,R,48);Some(1,L,31)];[Some(0,R,65);Some(0,R,48)];[Some(0,R,67);Some(0,R,50)];[Some(0,R,69);Some(0,R,52)];[Some(0,R,71);Some(0,R,54)];[Some(1,R,65);Some(1,R,48)];[Some(1,R,67);Some(1,R,50)];[Some(1,R,69);Some(1,R,52)];[Some(1,R,71);Some(1,R,54)];[Some(0,L,14);Some(1,L,29)];[Some(1,R,69);Some(0,R,19)];[None;Some(0,R,54)];[Some(0,L,10);Some(0,R,65)];[Some(1,L,14);None];[Some(1,R,52);Some(0,R,18)];[None;Some(0,L,29)];[Some(1,L,10);Some(0,R,48)];[Some(0,R,17);Some(0,R,16)];[Some(0,R,19);Some(0,R,18)];[Some(0,R,21);Some(0,R,20)];[Some(0,R,23);Some(0,R,22)];[Some(1,R,17);Some(1,R,16)];[Some(1,R,19);Some(1,R,18)];[Some(1,R,21);Some(1,R,20)];[Some(1,R,23);Some(1,R,22)];[Some(0,L,27);Some(1,R,19)];[Some(0,L,88);Some(0,L,25)];[Some(0,L,31);Some(1,R,65)];[Some(0,L,92);Some(0,L,29)];[Some(1,L,27);Some(1,R,18)];[Some(1,L,88);Some(1,L,25)];[Some(1,L,31);Some(1,R,48)];[Some(1,L,92);Some(1,L,29)];[Some(0,R,65);None];[Some(0,R,67);None];[Some(0,R,69);None];[Some(0,R,71);None];[Some(1,R,65);None];[Some(1,R,67);None];[Some(1,R,69);None];[Some(1,R,71);None];[Some(0,L,14);None];[Some(1,R,69);None];[None;None];[Some(0,L,10);None];[Some(1,L,14);None];[Some(1,R,52);None];[None;None];[Some(1,L,10);None]]%N.
Definition tm1 := TM'_from_str "1RB1RI_1LC---_1LG1LD_0LC0LE_1LF---_1LC1LE_1RH0LM_0RB0RI_0RJ0LC_1RA1RK_1RH1RL_0RH0RL_1LN1LF_1RL1LM".
Definition tm2 := TM'_from_str "1RB1RI_1LC1RO_1LG1LD_0LC0LE_1LF1RO_1LC1LE_1RH0LM_0RB0RI_0RJ0LC_1RA1RK_1RH1RL_0RH0RL_1LN1LF_1RL1LM_1RO1RO".
Definition l0 := [1;0;1;0;1;0;0;1;1;0;0;1;1;0;0;1]%N.
Definition mp := mp_from_list [69;82;29;10;60;14;43;65;18;54;52;48;31;47]%N.
Definition mp' := mp_from_list [69;19;29;10;92;14;43;65;18;54;52;48;31;47]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 false) 112 112.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM14.


Module TM15.
Definition tm := TM_from_str "1LB0LF_1RC0LC_0LE0RD_1RC1RD_0RB1LA_1LB---".
Definition tm' := TM_from_str "1LB---_1RC0LC_0LE0RD_0LE1RB_0RB1LF_1LB0LA".
Definition tm0 := TM'_from_list [[Some(0,R,50);Some(0,R,37)];[Some(1,L,27);None];[Some(0,R,54);Some(0,L,76)];[Some(0,R,50);None];[Some(1,R,50);Some(1,R,37)];[Some(1,L,9);None];[Some(1,R,54);Some(0,R,37)];[Some(1,R,50);None];[Some(0,L,25);Some(0,L,88)];[Some(0,L,27);Some(0,L,90)];[Some(0,L,29);Some(0,L,92)];[Some(0,L,31);Some(0,L,94)];[Some(1,L,25);Some(1,L,88)];[Some(1,L,27);Some(1,L,90)];[Some(1,L,29);Some(1,L,92)];[Some(1,L,31);Some(1,L,94)];[Some(0,R,33);Some(1,R,35)];[Some(0,R,35);Some(0,R,33)];[Some(0,R,37);Some(0,L,27)];[Some(0,R,39);Some(0,R,37)];[Some(1,R,33);Some(0,L,46)];[Some(1,R,35);Some(1,R,33)];[Some(1,R,37);Some(0,L,90)];[Some(1,R,39);Some(1,R,37)];[Some(0,L,9);Some(0,L,40)];[Some(0,L,46);Some(0,L,42)];[Some(0,L,13);Some(0,L,44)];[Some(1,R,35);Some(0,L,46)];[Some(1,L,9);Some(1,L,40)];[Some(1,R,50);Some(1,L,42)];[Some(1,L,13);Some(1,L,44)];[Some(1,R,51);Some(1,L,46)];[Some(0,R,33);Some(0,R,48)];[Some(1,R,35);Some(0,R,50)];[Some(0,R,37);Some(0,R,52)];[Some(0,L,29);Some(0,R,54)];[Some(1,R,33);Some(1,R,48)];[Some(0,L,46);Some(1,R,50)];[Some(1,R,37);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,72);Some(0,L,27)];[Some(0,L,74);Some(0,L,29)];[Some(0,L,76);Some(0,R,37)];[Some(0,L,78);Some(0,R,39)];[Some(1,L,72);Some(1,L,27)];[Some(1,L,74);Some(0,R,54)];[Some(1,L,76);Some(0,R,53)];[Some(1,L,78);Some(0,R,55)];[Some(0,R,33);Some(0,R,49)];[Some(0,R,35);Some(0,R,51)];[Some(0,R,37);Some(0,R,53)];[Some(0,R,39);Some(0,R,55)];[Some(1,R,33);Some(1,R,49)];[Some(1,R,35);Some(1,R,51)];[Some(1,R,37);Some(1,R,53)];[Some(1,R,39);Some(1,R,55)];[Some(0,L,9);Some(0,L,90)];[Some(0,L,46);None];[Some(0,L,13);Some(1,R,37)];[Some(1,R,35);Some(1,R,39)];[Some(1,L,9);Some(1,L,90)];[Some(1,R,50);Some(1,R,54)];[Some(1,L,13);Some(1,R,53)];[Some(1,R,51);Some(1,R,55)];[Some(0,R,16);Some(0,R,53)];[Some(0,R,18);Some(1,R,50)];[Some(0,R,20);Some(1,L,76)];[Some(0,R,22);None];[Some(1,R,16);Some(1,R,53)];[Some(1,R,18);Some(1,L,42)];[Some(1,R,20);Some(0,R,53)];[Some(1,R,22);None];[Some(0,L,27);Some(0,L,9)];[Some(0,L,72);Some(0,L,11)];[Some(0,R,37);Some(0,L,13)];[Some(0,L,76);Some(0,L,15)];[Some(1,L,27);Some(1,L,9)];[Some(1,L,72);Some(1,L,11)];[Some(0,R,53);Some(1,L,13)];[Some(1,L,76);Some(1,L,15)];[Some(0,R,50);None];[Some(1,L,27);None];[Some(0,R,54);None];[Some(0,R,50);None];[Some(1,R,50);None];[Some(1,L,9);None];[Some(1,R,54);None];[Some(1,R,50);None];[Some(0,L,25);None];[Some(0,L,27);None];[Some(0,L,29);None];[Some(0,L,31);None];[Some(1,L,25);None];[Some(1,L,27);None];[Some(1,L,29);None];[Some(1,L,31);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,50);None];[Some(1,L,27);None];[Some(0,R,54);None];[Some(0,R,50);None];[Some(1,R,50);None];[Some(1,L,89);None];[Some(1,R,54);None];[Some(1,R,50);None];[Some(0,L,25);None];[Some(0,L,27);None];[Some(0,L,29);None];[Some(0,L,31);None];[Some(1,L,25);None];[Some(1,L,27);None];[Some(1,L,29);None];[Some(1,L,31);None];[Some(0,R,33);Some(1,R,35)];[Some(0,R,35);Some(0,R,33)];[Some(0,R,37);Some(0,L,27)];[Some(0,R,39);Some(0,R,37)];[Some(1,R,33);Some(0,L,46)];[Some(1,R,35);Some(1,R,33)];[Some(1,R,37);Some(0,L,10)];[Some(1,R,39);Some(1,R,37)];[Some(0,L,89);Some(0,L,40)];[Some(0,L,46);Some(0,L,42)];[Some(0,L,93);Some(0,L,44)];[Some(1,R,35);Some(0,L,46)];[Some(1,L,89);Some(1,L,40)];[Some(1,R,50);Some(1,L,42)];[Some(1,L,93);Some(1,L,44)];[Some(1,R,33);Some(1,L,46)];[Some(0,R,33);Some(0,R,48)];[Some(1,R,35);Some(0,R,50)];[Some(0,R,37);Some(0,R,52)];[Some(0,L,29);Some(0,R,54)];[Some(1,R,33);Some(1,R,48)];[Some(0,L,46);Some(1,R,50)];[Some(1,R,37);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,72);Some(0,L,27)];[Some(0,L,74);Some(0,L,29)];[Some(0,L,76);Some(0,R,37)];[Some(0,L,78);Some(1,R,35)];[Some(1,L,72);Some(1,L,27)];[Some(1,L,74);Some(0,R,54)];[Some(1,L,76);Some(0,R,21)];[Some(1,L,78);Some(0,R,50)];[Some(0,R,33);Some(0,R,17)];[Some(1,R,35);Some(0,R,19)];[Some(0,R,37);Some(0,R,21)];[Some(0,L,29);Some(0,R,23)];[Some(1,R,33);Some(1,R,17)];[Some(0,L,46);Some(1,R,19)];[Some(1,R,37);Some(1,R,21)];[None;Some(1,R,23)];[Some(0,L,72);Some(0,L,10)];[Some(0,L,74);Some(0,L,27)];[Some(0,L,76);Some(1,R,37)];[Some(0,L,78);Some(0,R,37)];[Some(1,L,72);Some(1,L,10)];[Some(1,L,74);Some(1,L,27)];[Some(1,L,76);Some(1,R,21)];[Some(1,L,78);Some(0,R,21)];[Some(0,R,16);Some(0,R,21)];[Some(0,R,18);Some(1,R,50)];[Some(0,R,20);Some(1,L,76)];[Some(0,R,22);None];[Some(1,R,16);Some(1,R,21)];[Some(1,R,18);Some(1,L,42)];[Some(1,R,20);Some(0,R,21)];[Some(1,R,22);None];[Some(0,L,27);Some(0,L,89)];[Some(0,L,72);Some(0,L,91)];[Some(0,R,37);Some(0,L,93)];[Some(0,L,76);Some(0,L,95)];[Some(1,L,27);Some(1,L,89)];[Some(1,L,72);Some(1,L,91)];[Some(0,R,21);Some(1,L,93)];[Some(1,L,76);Some(1,L,95)];[Some(0,R,50);Some(0,R,37)];[Some(1,L,27);None];[Some(0,R,54);Some(0,L,76)];[Some(0,R,50);None];[Some(1,R,50);Some(1,R,37)];[Some(1,L,89);None];[Some(1,R,54);Some(0,R,37)];[Some(1,R,50);None];[Some(0,L,25);Some(0,L,8)];[Some(0,L,27);Some(0,L,10)];[Some(0,L,29);Some(0,L,12)];[Some(0,L,31);Some(0,L,14)];[Some(1,L,25);Some(1,L,8)];[Some(1,L,27);Some(1,L,10)];[Some(1,L,29);Some(1,L,12)];[Some(1,L,31);Some(1,L,14)]]%N.
Definition tm1 := TM'_from_str "0LB1RI_1LC0RJ_1LE1LD_0LE0LL_1RF0LB_0LG0RK_1RI1LH_0LC0RA_0RA0RJ_1RF---_1RA1RJ_0LG---".
Definition tm2 := TM'_from_str "0LB1RI_1LC0RJ_1LE1LD_0LE0LL_1RF0LB_0LG0RK_1RI1LH_0LC0RA_0RA0RJ_1RF---_1RA1RJ_0LG1RM_1RM1RM".
Definition l0 := [1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [37;46;76;9;27;35;29;42;50;53;54;90]%N.
Definition mp' := mp_from_list [37;46;76;89;27;35;29;42;50;21;54;10]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 true) 146 146.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM15.


Module TM16.
Definition tm := TM_from_str "1RB0LD_0RC0RA_1LC0LA_---1LE_0LF0RE_0RA0LE".
Definition tm' := TM_from_str "1RB0LD_0RC0RE_1LC0LA_---1LE_0LF0RE_0RA0LE".
Definition tm0 := TM'_from_list [[Some(0,R,17);None];[Some(0,R,19);Some(0,R,21)];[Some(0,R,21);None];[Some(0,R,23);Some(0,R,17)];[Some(1,R,17);None];[Some(1,R,19);Some(0,L,76)];[Some(1,R,21);None];[Some(1,R,23);Some(1,R,17)];[Some(0,L,14);Some(0,L,56)];[Some(1,R,34);Some(0,L,58)];[Some(1,L,60);Some(0,L,60)];[None;Some(0,L,62)];[Some(1,L,14);Some(1,L,56)];[Some(1,R,2);Some(1,L,58)];[Some(1,R,38);Some(1,L,60)];[None;Some(1,L,62)];[Some(0,R,32);Some(0,R,0)];[Some(0,R,34);Some(0,R,2)];[Some(0,R,36);Some(0,R,4)];[Some(0,R,38);Some(0,R,6)];[Some(1,R,32);Some(1,R,0)];[Some(1,R,34);Some(1,R,2)];[Some(1,R,36);Some(1,R,4)];[Some(1,R,38);Some(1,R,6)];[Some(0,L,43);Some(1,R,38)];[Some(0,L,14);None];[Some(0,L,47);Some(0,R,21)];[Some(1,L,60);None];[Some(1,L,43);Some(0,R,38)];[Some(1,L,14);None];[Some(1,L,47);None];[Some(1,R,38);None];[Some(1,L,47);Some(0,R,34)];[Some(0,R,38);None];[Some(1,R,38);Some(0,R,38)];[None;Some(0,L,90)];[Some(1,L,14);Some(1,R,34)];[Some(1,R,38);None];[Some(1,L,60);Some(1,R,38)];[Some(1,L,73);Some(0,R,34)];[Some(0,L,41);Some(0,L,8)];[Some(0,L,43);Some(0,L,10)];[Some(0,L,45);Some(0,L,12)];[Some(0,L,47);Some(0,L,14)];[Some(1,L,41);Some(1,L,8)];[Some(1,L,43);Some(1,L,10)];[Some(1,L,45);Some(1,L,12)];[Some(1,L,47);Some(1,L,14)];[None;Some(0,R,2)];[None;Some(0,R,64)];[None;Some(1,L,88)];[None;Some(0,R,68)];[None;Some(1,R,2)];[None;Some(1,R,64)];[None;Some(0,R,38)];[None;Some(1,R,68)];[None;Some(0,L,73)];[None;Some(0,L,75)];[None;Some(0,L,77)];[None;Some(0,L,79)];[None;Some(1,L,73)];[None;Some(1,L,75)];[None;Some(1,L,77)];[None;Some(1,L,79)];[Some(0,R,17);Some(0,R,64)];[Some(1,R,38);Some(0,R,66)];[Some(0,R,21);Some(0,R,68)];[Some(0,R,34);Some(0,R,70)];[Some(1,R,17);Some(1,R,64)];[Some(0,L,72);Some(1,R,66)];[Some(1,R,21);Some(1,R,68)];[Some(1,R,34);Some(1,R,70)];[Some(0,L,88);Some(1,R,38)];[Some(0,L,90);Some(0,R,34)];[Some(0,L,92);Some(0,R,21)];[Some(0,L,94);Some(0,R,17)];[Some(1,L,88);Some(0,R,38)];[Some(1,L,90);Some(0,R,2)];[Some(1,L,92);None];[Some(1,L,94);Some(0,R,64)];[Some(0,R,0);Some(0,R,34)];[Some(0,R,2);Some(0,R,17)];[Some(0,R,4);Some(0,L,88)];[Some(0,R,6);Some(0,R,21)];[Some(1,R,0);Some(1,R,34)];[Some(1,R,2);Some(1,R,17)];[Some(1,R,4);Some(1,R,38)];[Some(1,R,6);Some(1,R,21)];[Some(1,R,38);Some(0,L,72)];[None;Some(0,L,74)];[Some(0,R,21);Some(0,L,76)];[None;Some(0,L,78)];[Some(0,R,38);Some(1,L,72)];[None;Some(1,L,74)];[None;Some(1,L,76)];[None;Some(1,L,78)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);None];[Some(0,R,19);Some(0,R,21)];[Some(0,R,21);None];[Some(0,R,23);Some(0,R,17)];[Some(1,R,17);None];[Some(1,R,19);Some(0,L,76)];[Some(1,R,21);None];[Some(1,R,23);Some(1,R,17)];[Some(0,L,14);Some(0,L,56)];[Some(1,R,34);Some(0,L,58)];[Some(1,L,60);Some(0,L,60)];[Some(1,R,17);Some(0,L,62)];[Some(1,L,14);Some(1,L,56)];[Some(1,R,66);Some(1,L,58)];[Some(1,R,38);Some(1,L,60)];[Some(1,R,64);Some(1,L,62)];[Some(0,R,32);Some(0,R,64)];[Some(0,R,34);Some(0,R,66)];[Some(0,R,36);Some(0,R,68)];[Some(0,R,38);Some(0,R,70)];[Some(1,R,32);Some(1,R,64)];[Some(1,R,34);Some(1,R,66)];[Some(1,R,36);Some(1,R,68)];[Some(1,R,38);Some(1,R,70)];[Some(0,L,43);Some(1,R,38)];[Some(0,L,14);Some(0,R,34)];[Some(0,L,47);Some(0,R,21)];[Some(1,L,60);Some(0,R,17)];[Some(1,L,43);Some(0,R,38)];[Some(1,L,14);Some(0,R,66)];[Some(1,L,47);Some(0,R,68)];[Some(1,R,38);Some(0,R,64)];[Some(1,L,47);Some(0,R,34)];[Some(0,R,38);None];[Some(1,R,38);Some(0,R,38)];[None;Some(0,L,90)];[Some(1,L,14);Some(1,R,34)];[Some(1,R,38);None];[Some(1,L,60);Some(1,R,38)];[Some(1,L,73);Some(0,R,34)];[Some(0,L,41);Some(0,L,8)];[Some(0,L,43);Some(0,L,10)];[Some(0,L,45);Some(0,L,12)];[Some(0,L,47);Some(0,L,14)];[Some(1,L,41);Some(1,L,8)];[Some(1,L,43);Some(1,L,10)];[Some(1,L,45);Some(1,L,12)];[Some(1,L,47);Some(1,L,14)];[None;Some(0,R,66)];[None;Some(0,R,64)];[None;Some(1,L,88)];[None;Some(0,R,68)];[None;Some(1,R,66)];[None;Some(1,R,64)];[None;Some(0,R,38)];[None;Some(1,R,68)];[None;Some(0,L,73)];[None;Some(0,L,75)];[None;Some(0,L,77)];[None;Some(0,L,79)];[None;Some(1,L,73)];[None;Some(1,L,75)];[None;Some(1,L,77)];[None;Some(1,L,79)];[Some(0,R,17);Some(0,R,64)];[Some(1,R,38);Some(0,R,66)];[Some(0,R,21);Some(0,R,68)];[Some(0,R,34);Some(0,R,70)];[Some(1,R,17);Some(1,R,64)];[Some(0,L,72);Some(1,R,66)];[Some(1,R,21);Some(1,R,68)];[Some(1,R,34);Some(1,R,70)];[Some(0,L,88);Some(1,R,38)];[Some(0,L,90);Some(0,R,34)];[Some(0,L,92);Some(0,R,21)];[Some(0,L,94);Some(0,R,17)];[Some(1,L,88);Some(0,R,38)];[Some(1,L,90);Some(0,R,66)];[Some(1,L,92);Some(0,R,68)];[Some(1,L,94);Some(0,R,64)];[Some(0,R,0);Some(0,R,34)];[Some(0,R,2);Some(0,R,17)];[Some(0,R,4);Some(0,L,88)];[Some(0,R,6);Some(0,R,21)];[Some(1,R,0);Some(1,R,34)];[Some(1,R,2);Some(1,R,17)];[Some(1,R,4);Some(1,R,38)];[Some(1,R,6);Some(1,R,21)];[Some(1,R,38);Some(0,L,72)];[None;Some(0,L,74)];[Some(0,R,21);Some(0,L,76)];[None;Some(0,L,78)];[Some(0,R,38);Some(1,L,72)];[None;Some(1,L,74)];[Some(0,R,68);Some(1,L,76)];[None;Some(1,L,78)]]%N.
Definition tm1 := TM'_from_str "1LB1RA_---1LC_0LE0RD_1RA0RA_0RF0LG_1RD---_1LH0RA_1RA0LI_0LH1RA".
Definition tm2 := TM'_from_str "1LB1RA_1RJ1LC_0LE0RD_1RA0RA_0RF0LG_1RD---_1LH0RA_1RA0LI_0LH1RA_1RJ1RJ".
Definition l0 := [0;1;0;1;0;1;0;1;0;0;0;1;0;1;1;1]%N.
Definition mp := mp_from_list [38;60;73;34;90;21;76;88;72]%N.
Definition mp' := mp_from_list [38;60;73;34;90;21;76;88;72]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 8%N l0 (NG 0 1000 1000 1 1 0 0 false) 183 183.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM16.


Module TM17.
Definition tm := TM_from_str "1RB1LA_0RC1LD_1LA0RE_1LF0LA_1LD1RE_1LB---".
Definition tm' := TM_from_str "1LB0RC_0RA1LD_1LD1RC_1LE0LF_1LB---_1RB1LF".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,68)];[Some(0,R,19);Some(1,R,65)];[Some(0,R,21);Some(1,L,10)];[Some(0,R,23);Some(1,L,14)];[Some(1,R,17);Some(1,R,68)];[Some(1,R,19);Some(1,L,13)];[Some(1,R,21);Some(1,L,11)];[Some(1,R,23);Some(1,L,15)];[Some(0,L,13);Some(0,L,9)];[Some(0,L,10);Some(0,L,11)];[Some(1,L,63);Some(0,L,13)];[Some(0,L,14);Some(0,L,15)];[Some(1,L,13);Some(1,L,9)];[Some(1,L,10);Some(1,L,11)];[Some(1,R,65);Some(1,L,13)];[Some(1,L,14);Some(1,L,15)];[Some(0,R,32);Some(0,R,67)];[Some(0,R,34);Some(0,R,68)];[Some(0,R,36);None];[Some(0,R,38);Some(1,L,10)];[Some(1,R,32);Some(1,L,63)];[Some(1,R,34);Some(1,R,68)];[Some(1,R,36);None];[Some(1,R,38);Some(1,L,11)];[Some(0,L,10);Some(0,L,57)];[Some(0,L,31);Some(0,L,59)];[Some(0,L,14);Some(0,L,61)];[Some(0,R,68);Some(0,L,63)];[Some(1,L,10);Some(1,L,57)];[Some(1,L,31);Some(1,L,59)];[Some(1,L,14);Some(1,L,61)];[Some(0,R,67);Some(1,L,63)];[Some(0,R,68);Some(0,R,64)];[Some(1,R,65);Some(0,R,66)];[Some(1,L,10);Some(0,R,68)];[Some(1,L,14);Some(0,R,70)];[Some(1,R,68);Some(1,R,64)];[Some(1,L,13);Some(1,R,66)];[Some(1,L,11);Some(1,R,68)];[Some(1,L,15);Some(1,R,70)];[Some(0,L,9);Some(0,L,91)];[Some(0,L,11);Some(1,L,63)];[Some(0,L,13);Some(0,L,95)];[Some(0,L,15);Some(1,L,10)];[Some(1,L,9);Some(1,L,91)];[Some(1,L,11);Some(1,R,65)];[Some(1,L,13);Some(1,L,95)];[Some(1,L,15);Some(0,R,71)];[Some(0,R,65);Some(0,R,34)];[None;Some(1,L,63)];[Some(1,L,95);Some(0,R,38)];[None;Some(0,L,14)];[Some(1,R,65);Some(1,R,34)];[None;Some(0,L,13)];[Some(1,L,14);Some(1,R,38)];[None;Some(0,L,15)];[Some(0,L,89);Some(0,L,8)];[Some(0,L,91);Some(0,L,10)];[Some(0,L,93);Some(0,L,12)];[Some(0,L,95);Some(0,L,14)];[Some(1,L,89);Some(1,L,8)];[Some(1,L,91);Some(1,L,10)];[Some(1,L,93);Some(1,L,12)];[Some(1,L,95);Some(1,L,14)];[Some(0,R,67);Some(0,R,65)];[Some(0,R,68);Some(0,R,67)];[None;Some(0,R,69)];[Some(1,L,10);Some(0,R,71)];[Some(1,L,63);Some(1,R,65)];[Some(1,R,68);Some(1,R,67)];[None;Some(1,R,69)];[Some(1,L,11);Some(1,R,71)];[Some(0,L,57);Some(0,L,10)];[Some(0,L,59);Some(0,L,13)];[Some(0,L,61);Some(0,L,14)];[Some(0,L,63);Some(1,L,11)];[Some(1,L,57);Some(1,L,10)];[Some(1,L,59);Some(1,L,13)];[Some(1,L,61);Some(1,L,14)];[Some(1,L,63);Some(1,R,71)];[Some(0,R,64);None];[Some(1,L,31);None];[Some(0,R,68);None];[Some(1,R,65);None];[Some(1,R,64);None];[None;None];[Some(1,R,68);None];[Some(1,L,13);None];[Some(0,L,25);None];[Some(0,L,27);None];[Some(0,L,29);None];[Some(0,L,31);None];[Some(1,L,25);None];[Some(1,L,27);None];[Some(1,L,29);None];[Some(1,L,31);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,32);Some(0,R,32)];[Some(1,L,31);Some(0,R,34)];[Some(0,R,36);Some(0,R,36)];[Some(1,R,33);Some(0,R,38)];[Some(1,R,32);Some(1,R,32)];[None;Some(1,R,34)];[Some(1,R,36);Some(1,R,36)];[Some(1,L,93);Some(1,R,38)];[Some(0,L,25);Some(0,L,75)];[Some(0,L,27);Some(1,L,63)];[Some(0,L,29);Some(0,L,79)];[Some(0,L,31);Some(1,L,90)];[Some(1,L,25);Some(1,L,75)];[Some(1,L,27);Some(1,R,33)];[Some(1,L,29);Some(1,L,79)];[Some(1,L,31);Some(0,R,39)];[Some(0,R,0);Some(0,R,35)];[Some(0,R,2);Some(0,R,36)];[Some(0,R,4);None];[Some(0,R,6);Some(1,L,90)];[Some(1,R,0);Some(1,L,63)];[Some(1,R,2);Some(1,R,36)];[Some(1,R,4);None];[Some(1,R,6);Some(1,L,91)];[Some(0,L,31);Some(0,L,57)];[Some(0,L,31);Some(0,L,59)];[Some(0,R,36);Some(0,L,61)];[Some(0,R,36);Some(0,L,63)];[Some(1,L,31);Some(1,L,57)];[Some(1,L,31);Some(1,L,59)];[Some(0,R,35);Some(1,L,61)];[Some(0,R,35);Some(1,L,63)];[Some(0,R,35);Some(0,R,33)];[Some(0,R,36);Some(0,R,35)];[None;Some(0,R,37)];[Some(1,L,90);Some(0,R,39)];[Some(1,L,63);Some(1,R,33)];[Some(1,R,36);Some(1,R,35)];[None;Some(1,R,37)];[Some(1,L,91);Some(1,R,39)];[Some(0,L,57);Some(0,L,90)];[Some(0,L,59);Some(0,L,93)];[Some(0,L,61);Some(0,L,94)];[Some(0,L,63);Some(1,L,91)];[Some(1,L,57);Some(1,L,90)];[Some(1,L,59);Some(1,L,93)];[Some(1,L,61);Some(1,L,94)];[Some(1,L,63);Some(1,R,39)];[Some(0,R,33);Some(0,R,2)];[None;Some(1,L,63)];[Some(1,L,79);Some(0,R,6)];[None;Some(0,L,94)];[Some(1,R,33);Some(1,R,2)];[None;Some(0,L,93)];[Some(1,L,94);Some(1,R,6)];[None;Some(0,L,95)];[Some(0,L,73);Some(0,L,88)];[Some(0,L,75);Some(0,L,90)];[Some(0,L,77);Some(0,L,92)];[Some(0,L,79);Some(0,L,94)];[Some(1,L,73);Some(1,L,88)];[Some(1,L,75);Some(1,L,90)];[Some(1,L,77);Some(1,L,92)];[Some(1,L,79);Some(1,L,94)];[Some(0,R,32);None];[Some(1,L,31);None];[Some(0,R,36);None];[Some(1,R,33);None];[Some(1,R,32);None];[None;None];[Some(1,R,36);None];[Some(1,L,93);None];[Some(0,L,25);None];[Some(0,L,27);None];[Some(0,L,29);None];[Some(0,L,31);None];[Some(1,L,25);None];[Some(1,L,27);None];[Some(1,L,29);None];[Some(1,L,31);None];[Some(0,R,17);Some(0,R,36)];[Some(0,R,19);Some(1,R,33)];[Some(0,R,21);Some(1,L,90)];[Some(0,R,23);Some(1,L,94)];[Some(1,R,17);Some(1,R,36)];[Some(1,R,19);Some(1,L,93)];[Some(1,R,21);Some(1,L,91)];[Some(1,R,23);Some(1,L,95)];[Some(1,L,63);Some(0,L,89)];[Some(0,L,90);Some(0,L,91)];[Some(1,L,63);Some(0,L,93)];[Some(0,L,94);Some(0,L,95)];[Some(1,R,33);Some(1,L,89)];[Some(1,L,90);Some(1,L,91)];[Some(1,R,33);Some(1,L,93)];[Some(1,L,94);Some(1,L,95)]]%N.
Definition tm1 := TM'_from_str "1LB0RF_1LC0LI_1LK1LD_1RE1LI_0RJ0RA_1LG1RF_0LD0LH_1LD1LH_1LB1LG_1LC1RE_1LL---_0RA1LC".
Definition tm2 := TM'_from_str "1LB0RF_1LC0LI_1LK1LD_1RE1LI_0RJ0RA_1LG1RF_0LD0LH_1LD1LH_1LB1LG_1LC1RE_1LL1RM_0RA1LC_1RM1RM".
Definition l0 := [1;1;0;1;1;1;1;1;1;0;1;1;1;0;1;0]%N.
Definition mp := mp_from_list [67;10;63;14;65;71;11;15;13;68;95;31]%N.
Definition mp' := mp_from_list [35;90;63;94;33;39;91;95;93;36;79;31]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 209 209.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM17.


Module TM18.
Definition tm := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA0RB_1RD0RF".
Definition tm' := TM_from_str "1LB1LA_0LC1LF_1RD---_0RE1RE_1LA1RD_1RD0RF".
Definition tm0 := TM'_from_list [[Some(0,R,20);Some(1,R,67)];[Some(0,R,22);Some(1,L,46)];[None;Some(1,R,71)];[Some(0,R,80);Some(1,L,31)];[Some(1,R,20);None];[Some(1,R,22);Some(1,L,95)];[None;Some(0,R,80)];[Some(1,R,80);Some(1,L,15)];[Some(0,L,25);Some(0,L,9)];[Some(0,L,27);Some(0,L,11)];[Some(0,L,29);Some(0,L,13)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,25);Some(1,L,9)];[Some(1,L,27);Some(1,L,11)];[Some(1,L,29);Some(1,L,13)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,66);Some(0,R,67)];[None;Some(0,R,80)];[Some(0,R,70);Some(0,R,71)];[None;Some(0,R,84)];[Some(1,R,66);Some(1,R,67)];[None;Some(1,R,80)];[Some(1,R,70);Some(1,R,71)];[None;Some(1,R,84)];[Some(0,L,40);Some(0,L,89)];[Some(0,L,42);Some(0,L,91)];[Some(0,L,44);Some(0,L,93)];[Some(0,L,46);Some(0,L,95)];[Some(1,L,40);Some(1,L,89)];[Some(1,L,42);Some(1,L,91)];[Some(1,L,44);Some(1,L,93)];[Some(1,L,46);Some(1,L,95)];[Some(0,R,49);None];[Some(0,R,51);None];[Some(0,R,53);None];[Some(0,R,55);None];[Some(1,R,49);None];[Some(1,R,51);None];[Some(1,R,53);None];[Some(1,R,55);None];[Some(0,L,95);None];[Some(0,L,15);None];[Some(1,R,66);None];[Some(1,R,70);None];[Some(1,L,95);None];[Some(1,L,15);None];[Some(1,R,67);None];[Some(1,R,71);None];[Some(0,R,64);Some(0,R,65)];[Some(0,R,66);Some(0,R,67)];[Some(0,R,68);Some(0,R,69)];[Some(0,R,70);Some(0,R,71)];[Some(1,R,64);Some(1,R,65)];[Some(1,R,66);Some(1,R,67)];[Some(1,R,68);Some(1,R,69)];[Some(1,R,70);Some(1,R,71)];[Some(0,L,27);Some(0,L,11)];[Some(1,R,71);Some(0,R,80)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,31);Some(1,L,15)];[Some(1,L,27);Some(1,L,11)];[Some(0,R,20);Some(1,R,20)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,22);Some(1,R,22)];[Some(1,R,67);Some(0,R,16)];[Some(1,L,46);Some(0,R,18)];[Some(1,R,71);Some(0,R,20)];[Some(1,L,31);Some(0,R,22)];[None;Some(1,R,16)];[Some(1,L,95);Some(1,R,18)];[Some(0,R,80);Some(1,R,20)];[Some(1,L,15);Some(1,R,22)];[Some(0,L,9);Some(0,L,95)];[Some(0,L,11);Some(0,L,15)];[Some(0,L,13);Some(1,R,66)];[Some(0,L,15);Some(1,R,70)];[Some(1,L,9);Some(1,L,95)];[Some(1,L,11);Some(1,L,15)];[Some(1,L,13);Some(1,R,67)];[Some(1,L,15);Some(1,R,71)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(0,L,95);Some(1,R,71)];[Some(0,L,15);Some(0,R,66)];[Some(1,R,66);Some(1,L,31)];[Some(1,R,70);Some(0,R,49)];[Some(1,L,95);Some(0,R,20)];[Some(1,L,15);Some(0,R,67)];[Some(1,R,67);Some(0,R,22)];[Some(1,R,71);Some(0,R,80)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,53);Some(1,R,67)];[Some(0,R,55);Some(1,L,46)];[None;Some(1,R,71)];[Some(0,R,80);Some(1,L,31)];[Some(1,R,53);None];[Some(1,R,55);Some(1,L,95)];[None;Some(0,R,80)];[Some(1,R,80);Some(1,L,15)];[Some(0,L,25);Some(0,L,9)];[Some(0,L,27);Some(0,L,11)];[Some(0,L,29);Some(0,L,13)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,25);Some(1,L,9)];[Some(1,L,27);Some(1,L,11)];[Some(1,L,29);Some(1,L,13)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,66);Some(0,R,67)];[None;Some(0,R,80)];[Some(0,R,70);Some(0,R,71)];[None;Some(0,R,84)];[Some(1,R,66);Some(1,R,67)];[None;Some(1,R,80)];[Some(1,R,70);Some(1,R,71)];[None;Some(1,R,84)];[Some(0,L,40);Some(0,L,89)];[Some(0,L,42);Some(0,L,91)];[Some(0,L,44);Some(0,L,93)];[Some(0,L,46);Some(0,L,95)];[Some(1,L,40);Some(1,L,89)];[Some(1,L,42);Some(1,L,91)];[Some(1,L,44);Some(1,L,93)];[Some(1,L,46);Some(1,L,95)];[Some(0,R,49);None];[Some(0,R,51);None];[Some(0,R,53);None];[Some(0,R,55);None];[Some(1,R,49);None];[Some(1,R,51);None];[Some(1,R,53);None];[Some(1,R,55);None];[Some(0,L,95);None];[Some(0,L,15);None];[Some(1,R,66);None];[Some(1,R,70);None];[Some(1,L,95);None];[Some(1,L,15);None];[Some(1,R,67);None];[Some(1,R,71);None];[Some(0,R,64);Some(0,R,65)];[Some(0,R,66);Some(0,R,67)];[Some(0,R,68);Some(0,R,69)];[Some(0,R,70);Some(0,R,71)];[Some(1,R,64);Some(1,R,65)];[Some(1,R,66);Some(1,R,67)];[Some(1,R,68);Some(1,R,69)];[Some(1,R,70);Some(1,R,71)];[Some(0,L,27);Some(0,L,11)];[Some(1,R,71);Some(0,R,80)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,31);Some(1,L,15)];[Some(1,L,27);Some(1,L,11)];[Some(0,R,53);Some(1,R,53)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,55);Some(1,R,55)];[Some(1,R,67);Some(0,R,49)];[Some(1,L,46);Some(0,R,51)];[Some(1,R,71);Some(0,R,53)];[Some(1,L,31);Some(0,R,55)];[None;Some(1,R,49)];[Some(1,L,95);Some(1,R,51)];[Some(0,R,80);Some(1,R,53)];[Some(1,L,15);Some(1,R,55)];[Some(0,L,9);Some(0,L,95)];[Some(0,L,11);Some(0,L,15)];[Some(0,L,13);Some(1,R,66)];[Some(0,L,15);Some(1,R,70)];[Some(1,L,9);Some(1,L,95)];[Some(1,L,11);Some(1,L,15)];[Some(1,L,13);Some(1,R,67)];[Some(1,L,15);Some(1,R,71)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(0,L,95);Some(1,R,71)];[Some(0,L,15);Some(0,R,66)];[Some(1,R,66);Some(1,L,31)];[Some(1,R,70);Some(0,R,49)];[Some(1,L,95);Some(0,R,53)];[Some(1,L,15);Some(0,R,67)];[Some(1,R,67);Some(0,R,55)];[Some(1,R,71);Some(0,R,80)]]%N.
Definition tm1 := TM'_from_str "1LB1RF_1LC1LB_1LD1LG_1RE---_---0RF_1RK1RA_1RA0RH_0RI0RH_0RJ---_1RA---_0RH---".
Definition tm2 := TM'_from_str "1LB1RF_1LC1LB_1LD1LG_1RE1RL_---0RF_1RK1RA_1RA0RH_0RI0RH_0RJ---_1RA---_0RH---_1RL1RL".
Definition l0 := [1;0;1;1;1;1;0;0;0;0;0;0;0;0;0;1]%N.
Definition mp := mp_from_list [71;15;31;46;67;22;95;80;49;66;70]%N.
Definition mp' := mp_from_list [71;15;31;46;67;55;95;80;49;66;70]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 10%N l0 (NG 0 1000 1000 1 1 0 0 false) 44 44.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM18.


Module TM19.
Definition tm := TM_from_str "1LB1LA_0LC1LC_1RD0RF_0RE1RE_1LA1RD_---0RC".
Definition tm' := TM_from_str "1LB1LA_0LC1LC_1RD0RF_0RE1RE_1LA0RB_---0RC".
Definition tm0 := TM'_from_list [[Some(0,R,53);Some(1,R,67)];[Some(0,R,55);Some(1,L,46)];[None;Some(1,R,71)];[Some(0,R,80);Some(1,L,31)];[Some(1,R,53);None];[Some(1,R,55);Some(1,L,47)];[None;Some(0,R,32)];[Some(1,R,80);Some(1,L,15)];[Some(0,L,25);Some(0,L,9)];[Some(0,L,27);Some(0,L,11)];[Some(0,L,29);Some(0,L,13)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,25);Some(1,L,9)];[Some(1,L,27);Some(1,L,11)];[Some(1,L,29);Some(1,L,13)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,66);Some(0,R,67)];[None;Some(0,R,32)];[Some(0,R,70);Some(0,R,71)];[None;Some(0,R,36)];[Some(1,R,66);Some(1,R,67)];[None;Some(1,R,32)];[Some(1,R,70);Some(1,R,71)];[None;Some(1,R,36)];[Some(0,L,40);Some(0,L,41)];[Some(0,L,42);Some(0,L,43)];[Some(0,L,44);Some(0,L,45)];[Some(0,L,46);Some(0,L,47)];[Some(1,L,40);Some(1,L,41)];[Some(1,L,42);Some(1,L,43)];[Some(1,L,44);Some(1,L,45)];[Some(1,L,46);Some(1,L,47)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(0,L,47);None];[Some(0,L,15);Some(0,R,66)];[Some(1,R,66);None];[Some(1,R,70);None];[Some(1,L,47);None];[Some(1,L,15);Some(0,R,67)];[Some(1,R,67);None];[Some(1,R,71);Some(0,R,32)];[Some(0,R,64);Some(0,R,65)];[Some(0,R,66);Some(0,R,67)];[Some(0,R,68);Some(0,R,69)];[Some(0,R,70);Some(0,R,71)];[Some(1,R,64);Some(1,R,65)];[Some(1,R,66);Some(1,R,67)];[Some(1,R,68);Some(1,R,69)];[Some(1,R,70);Some(1,R,71)];[Some(0,L,27);Some(0,L,11)];[Some(1,R,71);Some(0,R,32)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,31);Some(1,L,15)];[Some(1,L,27);Some(1,L,11)];[Some(0,R,53);Some(1,R,53)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,55);Some(1,R,55)];[Some(1,R,67);Some(0,R,49)];[Some(1,L,46);Some(0,R,51)];[Some(1,R,71);Some(0,R,53)];[Some(1,L,31);Some(0,R,55)];[None;Some(1,R,49)];[Some(1,L,47);Some(1,R,51)];[Some(0,R,32);Some(1,R,53)];[Some(1,L,15);Some(1,R,55)];[Some(0,L,9);Some(0,L,47)];[Some(0,L,11);Some(0,L,15)];[Some(0,L,13);Some(1,R,66)];[Some(0,L,15);Some(1,R,70)];[Some(1,L,9);Some(1,L,47)];[Some(1,L,11);Some(1,L,15)];[Some(1,L,13);Some(1,R,67)];[Some(1,L,15);Some(1,R,71)];[None;Some(0,R,32)];[None;Some(0,R,34)];[None;Some(0,R,36)];[None;Some(0,R,38)];[None;Some(1,R,32)];[None;Some(1,R,34)];[None;Some(1,R,36)];[None;Some(1,R,38)];[None;Some(1,R,71)];[None;None];[None;Some(1,L,31)];[None;Some(0,R,49)];[None;Some(0,R,53)];[None;None];[None;Some(0,R,55)];[None;Some(0,R,80)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,20);Some(1,R,67)];[Some(0,R,22);Some(1,L,46)];[None;Some(1,R,71)];[Some(0,R,80);Some(1,L,31)];[Some(1,R,20);None];[Some(1,R,22);Some(1,L,47)];[None;Some(0,R,32)];[Some(1,R,80);Some(1,L,15)];[Some(0,L,25);Some(0,L,9)];[Some(0,L,27);Some(0,L,11)];[Some(0,L,29);Some(0,L,13)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,25);Some(1,L,9)];[Some(1,L,27);Some(1,L,11)];[Some(1,L,29);Some(1,L,13)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,66);Some(0,R,67)];[None;Some(0,R,32)];[Some(0,R,70);Some(0,R,71)];[None;Some(0,R,36)];[Some(1,R,66);Some(1,R,67)];[None;Some(1,R,32)];[Some(1,R,70);Some(1,R,71)];[None;Some(1,R,36)];[Some(0,L,40);Some(0,L,41)];[Some(0,L,42);Some(0,L,43)];[Some(0,L,44);Some(0,L,45)];[Some(0,L,46);Some(0,L,47)];[Some(1,L,40);Some(1,L,41)];[Some(1,L,42);Some(1,L,43)];[Some(1,L,44);Some(1,L,45)];[Some(1,L,46);Some(1,L,47)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(0,L,47);None];[Some(0,L,15);Some(0,R,66)];[Some(1,R,66);None];[Some(1,R,70);None];[Some(1,L,47);None];[Some(1,L,15);Some(0,R,67)];[Some(1,R,67);None];[Some(1,R,71);Some(0,R,32)];[Some(0,R,64);Some(0,R,65)];[Some(0,R,66);Some(0,R,67)];[Some(0,R,68);Some(0,R,69)];[Some(0,R,70);Some(0,R,71)];[Some(1,R,64);Some(1,R,65)];[Some(1,R,66);Some(1,R,67)];[Some(1,R,68);Some(1,R,69)];[Some(1,R,70);Some(1,R,71)];[Some(0,L,27);Some(0,L,11)];[Some(1,R,71);Some(0,R,32)];[Some(0,L,31);Some(0,L,15)];[Some(1,L,31);Some(1,L,15)];[Some(1,L,27);Some(1,L,11)];[Some(0,R,20);Some(1,R,20)];[Some(1,L,31);Some(1,L,15)];[Some(0,R,22);Some(1,R,22)];[Some(1,R,67);Some(0,R,16)];[Some(1,L,46);Some(0,R,18)];[Some(1,R,71);Some(0,R,20)];[Some(1,L,31);Some(0,R,22)];[None;Some(1,R,16)];[Some(1,L,47);Some(1,R,18)];[Some(0,R,32);Some(1,R,20)];[Some(1,L,15);Some(1,R,22)];[Some(0,L,9);Some(0,L,47)];[Some(0,L,11);Some(0,L,15)];[Some(0,L,13);Some(1,R,66)];[Some(0,L,15);Some(1,R,70)];[Some(1,L,9);Some(1,L,47)];[Some(1,L,11);Some(1,L,15)];[Some(1,L,13);Some(1,R,67)];[Some(1,L,15);Some(1,R,71)];[None;Some(0,R,32)];[None;Some(0,R,34)];[None;Some(0,R,36)];[None;Some(0,R,38)];[None;Some(1,R,32)];[None;Some(1,R,34)];[None;Some(1,R,36)];[None;Some(1,R,38)];[None;Some(1,R,71)];[None;None];[None;Some(1,L,31)];[None;Some(0,R,49)];[None;Some(0,R,20)];[None;None];[None;Some(0,R,22)];[None;Some(0,R,80)]]%N.
Definition tm1 := TM'_from_str "1LB1RF_1LC1LB_1LD1LG_1RE---_---0RF_1RL1RA_1RA0RH_0RJ0RI_---0RH_0RK---_1RA---_0RH---".
Definition tm2 := TM'_from_str "1LB1RF_1LC1LB_1LD1LG_1RE1RM_---0RF_1RL1RA_1RA0RH_0RJ0RI_1RM0RH_0RK---_1RA---_0RH---_1RM1RM".
Definition l0 := [1;0;1;1;1;1;0;0;0;0;0;0;0;0;0;1]%N.
Definition mp := mp_from_list [71;15;31;46;67;55;47;32;80;49;66;70]%N.
Definition mp' := mp_from_list [71;15;31;46;67;22;47;32;80;49;66;70]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 44 44.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM19.


Module TM20.
Definition tm := TM_from_str "1RB1RE_0LC---_1LD1LC_0RE0LD_1RF0RA_1RC0LA".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LB---".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,65)];[Some(0,R,19);Some(0,R,67)];[Some(0,R,21);Some(0,R,69)];[Some(0,R,23);Some(0,R,71)];[Some(1,R,17);Some(1,R,65)];[Some(1,R,19);Some(1,R,67)];[Some(1,R,21);Some(1,R,69)];[Some(1,R,23);Some(1,R,71)];[Some(0,L,41);Some(1,L,56)];[None;Some(0,L,62)];[Some(0,L,45);Some(1,R,39)];[None;Some(1,R,83)];[Some(1,L,41);Some(1,L,47)];[None;None];[Some(1,L,45);Some(1,R,87)];[None;Some(1,R,2)];[Some(0,R,17);None];[Some(0,R,83);None];[Some(0,R,39);None];[Some(0,L,63);None];[Some(1,R,17);None];[Some(0,L,62);None];[Some(0,L,60);None];[Some(0,L,47);None];[Some(0,L,40);None];[Some(0,L,42);None];[Some(0,L,44);None];[Some(0,L,46);None];[Some(1,L,40);None];[Some(1,L,42);None];[Some(1,L,44);None];[Some(1,L,46);None];[Some(0,R,0);Some(0,R,65)];[Some(0,R,83);Some(0,R,2)];[Some(0,R,4);Some(0,R,87)];[Some(1,L,63);Some(1,L,63)];[Some(1,R,0);Some(1,R,65)];[Some(1,R,83);Some(1,L,62)];[Some(1,R,4);Some(1,L,60)];[Some(1,L,56);Some(1,L,47)];[Some(0,L,57);Some(0,L,41)];[Some(0,L,59);Some(0,L,43)];[Some(0,L,61);Some(0,L,45)];[Some(0,L,63);Some(0,L,47)];[Some(1,L,57);Some(1,L,41)];[Some(1,L,59);Some(1,L,43)];[Some(1,L,61);Some(1,L,45)];[Some(1,L,63);Some(1,L,47)];[Some(0,R,64);Some(0,R,81)];[Some(0,R,66);Some(0,R,35)];[Some(0,R,68);Some(0,R,85)];[Some(0,R,70);Some(1,L,63)];[Some(1,R,64);Some(1,R,81)];[Some(1,R,66);Some(1,R,35)];[Some(1,R,68);Some(1,R,85)];[Some(1,R,70);Some(0,L,56)];[Some(1,L,63);Some(0,L,56)];[Some(0,R,83);Some(0,L,58)];[Some(0,R,39);Some(0,L,60)];[Some(0,R,83);Some(0,L,62)];[Some(1,L,63);Some(1,L,56)];[None;Some(1,L,58)];[Some(0,R,87);Some(1,L,60)];[Some(0,R,2);Some(1,L,62)];[Some(0,R,81);Some(0,R,0)];[Some(0,R,83);Some(0,R,2)];[Some(0,R,85);Some(0,R,4)];[Some(0,R,87);Some(0,R,6)];[Some(1,R,81);Some(1,R,0)];[Some(1,R,83);Some(1,R,2)];[Some(1,R,85);Some(1,R,4)];[Some(1,R,87);Some(1,R,6)];[Some(0,L,60);Some(0,L,59)];[Some(1,L,56);Some(0,R,39)];[Some(0,L,47);None];[Some(1,R,39);Some(0,R,21)];[Some(1,L,60);Some(1,L,59)];[Some(1,L,47);Some(0,R,87)];[Some(1,L,47);None];[Some(1,R,87);Some(0,R,69)];[Some(0,R,33);Some(0,R,83)];[Some(0,R,35);Some(0,R,83)];[Some(0,R,37);Some(0,L,63)];[Some(0,R,39);Some(0,R,87)];[Some(1,R,33);Some(0,L,62)];[Some(1,R,35);Some(1,R,83)];[Some(1,R,37);Some(0,L,47)];[Some(1,R,39);Some(1,R,87)];[Some(0,L,58);Some(0,L,8)];[Some(0,L,43);Some(0,L,10)];[Some(0,L,62);Some(0,L,12)];[Some(0,L,47);Some(0,L,14)];[Some(1,L,58);Some(1,L,8)];[Some(1,L,43);Some(1,L,10)];[Some(1,L,62);Some(1,L,12)];[Some(1,L,47);Some(1,L,14)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,1)];[Some(0,R,19);Some(0,R,3)];[Some(0,R,21);Some(0,R,5)];[Some(0,R,23);Some(0,R,7)];[Some(1,R,17);Some(1,R,1)];[Some(1,R,19);Some(1,R,3)];[Some(1,R,21);Some(1,R,5)];[Some(1,R,23);Some(1,R,7)];[Some(0,L,42);Some(0,L,44)];[Some(0,L,27);Some(1,L,40)];[Some(0,L,46);Some(0,L,31)];[Some(0,L,31);Some(1,R,23)];[Some(1,L,42);Some(1,L,44)];[Some(1,L,27);Some(1,L,31)];[Some(1,L,46);Some(1,L,31)];[Some(1,L,31);Some(1,R,7)];[Some(0,R,64);Some(0,R,49)];[Some(0,R,3);Some(0,R,66)];[Some(0,R,68);Some(0,R,7)];[Some(1,L,47);Some(1,L,47)];[Some(1,R,64);Some(1,R,49)];[Some(1,R,3);Some(1,L,46)];[Some(1,R,68);Some(1,L,44)];[Some(1,L,40);Some(1,L,31)];[Some(0,L,41);Some(0,L,25)];[Some(0,L,43);Some(0,L,27)];[Some(0,L,45);Some(0,L,29)];[Some(0,L,47);Some(0,L,31)];[Some(1,L,41);Some(1,L,25)];[Some(1,L,43);Some(1,L,27)];[Some(1,L,45);Some(1,L,29)];[Some(1,L,47);Some(1,L,31)];[Some(0,R,48);Some(0,R,1)];[Some(0,R,50);Some(0,R,19)];[Some(0,R,52);Some(0,R,5)];[Some(0,R,54);Some(1,L,47)];[Some(1,R,48);Some(1,R,1)];[Some(1,R,50);Some(1,R,19)];[Some(1,R,52);Some(1,R,5)];[Some(1,R,54);Some(0,L,40)];[Some(1,L,47);Some(0,L,40)];[Some(0,R,3);Some(0,L,42)];[Some(0,R,23);Some(0,L,44)];[Some(0,R,3);Some(0,L,46)];[Some(1,L,47);Some(1,L,40)];[None;Some(1,L,42)];[Some(0,R,7);Some(1,L,44)];[Some(0,R,66);Some(1,L,46)];[Some(0,R,1);Some(0,R,64)];[Some(0,R,3);Some(0,R,66)];[Some(0,R,5);Some(0,R,68)];[Some(0,R,7);Some(0,R,70)];[Some(1,R,1);Some(1,R,64)];[Some(1,R,3);Some(1,R,66)];[Some(1,R,5);Some(1,R,68)];[Some(1,R,7);Some(1,R,70)];[Some(0,L,44);Some(0,L,43)];[Some(1,L,40);Some(0,R,23)];[Some(0,L,31);None];[Some(1,R,23);Some(0,R,85)];[Some(1,L,44);Some(1,L,43)];[Some(1,L,31);Some(0,R,7)];[Some(1,L,31);None];[Some(1,R,7);Some(0,R,53)];[Some(0,R,81);Some(0,R,49)];[Some(0,R,83);Some(0,R,51)];[Some(0,R,85);Some(0,R,53)];[Some(0,R,87);Some(0,R,55)];[Some(1,R,81);Some(1,R,49)];[Some(1,R,83);Some(1,R,51)];[Some(1,R,85);Some(1,R,53)];[Some(1,R,87);Some(1,R,55)];[Some(0,L,25);Some(1,L,40)];[None;Some(0,L,46)];[Some(0,L,29);Some(1,R,23)];[None;Some(1,R,3)];[Some(1,L,25);Some(1,L,31)];[None;None];[Some(1,L,29);Some(1,R,7)];[None;Some(1,R,66)];[Some(0,R,81);None];[Some(0,R,3);None];[Some(0,R,23);None];[Some(0,L,47);None];[Some(1,R,81);None];[Some(0,L,46);None];[Some(0,L,44);None];[Some(0,L,31);None];[Some(0,L,24);None];[Some(0,L,26);None];[Some(0,L,28);None];[Some(0,L,30);None];[Some(1,L,24);None];[Some(1,L,26);None];[Some(1,L,28);None];[Some(1,L,30);None]]%N.
Definition tm1 := TM'_from_str "1RB1RA_1LC1LI_1LD0LC_0RF1LE_0RA---_0RJ0RG_1RH1RF_0RB0RA_1LD1LI_0LE---".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LI_1LD0LC_0RF1LE_0RA---_0RJ0RG_1RH1RF_0RB0RA_1LD1LI_0LE1RK_1RK1RK".
Definition l0 := [0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_list [87;39;56;63;62;2;69;83;47;21]%N.
Definition mp' := mp_from_list [7;23;40;47;46;66;53;3;31;85]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 9%N l0 (NG 0 1000 1000 1 1 0 0 true) 376 376.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM20.


Module TM21.
Definition tm := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA0RE_1RE---".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB0RE_0LA0RE_1RD---".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,49)];[Some(0,R,19);Some(1,L,24)];[Some(0,R,21);Some(0,R,53)];[Some(0,R,23);Some(0,R,53)];[Some(1,R,17);Some(1,R,49)];[Some(1,R,19);Some(0,L,24)];[Some(1,R,21);Some(1,R,53)];[Some(1,R,23);Some(1,R,53)];[Some(1,L,24);Some(0,L,24)];[Some(1,L,24);Some(0,L,26)];[Some(1,R,65);Some(0,L,28)];[Some(1,R,65);Some(0,L,30)];[Some(1,R,66);Some(1,L,24)];[Some(1,R,66);Some(1,L,26)];[None;Some(1,L,28)];[None;Some(1,L,30)];[Some(0,R,32);Some(0,R,53)];[Some(0,R,34);Some(0,R,34)];[Some(0,R,36);Some(0,L,12)];[Some(0,R,38);Some(0,R,38)];[Some(1,R,32);Some(1,R,53)];[Some(1,R,34);Some(1,R,34)];[Some(1,R,36);Some(0,L,72)];[Some(1,R,38);Some(1,R,38)];[Some(0,L,12);Some(0,L,72)];[Some(1,R,66);Some(0,L,74)];[Some(0,R,38);Some(0,L,76)];[None;Some(0,L,78)];[Some(1,L,12);Some(1,L,72)];[Some(0,R,66);Some(1,L,74)];[Some(0,R,68);Some(1,L,76)];[None;Some(1,L,78)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(0,L,74);Some(0,L,12)];[Some(1,R,53);None];[Some(0,L,78);Some(0,R,38)];[Some(1,R,34);None];[Some(1,L,74);Some(1,L,12)];[Some(1,R,84);None];[Some(1,L,78);Some(0,R,68)];[Some(1,R,64);None];[Some(0,R,80);Some(0,R,64)];[Some(1,R,66);Some(0,R,66)];[Some(0,R,84);Some(0,R,68)];[Some(0,R,84);Some(0,R,70)];[Some(1,R,80);Some(1,R,64)];[Some(1,L,24);Some(1,R,66)];[Some(1,R,84);Some(1,R,68)];[Some(1,R,84);Some(1,R,70)];[Some(0,L,25);Some(1,L,24)];[Some(0,L,27);Some(0,R,53)];[Some(0,L,29);Some(1,R,65)];[Some(0,L,31);Some(0,R,34)];[Some(1,L,25);Some(1,R,66)];[Some(1,L,27);Some(0,R,84)];[Some(1,L,29);None];[Some(1,L,31);Some(0,R,64)];[Some(0,R,34);Some(0,R,64)];[Some(1,R,66);Some(0,R,66)];[Some(0,R,38);Some(0,R,68)];[Some(0,L,8);Some(0,R,70)];[Some(1,R,34);Some(1,R,64)];[Some(1,L,24);Some(1,R,66)];[Some(1,R,38);Some(1,R,68)];[Some(1,L,24);Some(1,R,70)];[Some(0,L,8);Some(1,L,24)];[Some(0,L,10);Some(0,R,53)];[Some(0,L,12);Some(1,R,65)];[Some(0,L,14);Some(0,R,34)];[Some(1,L,8);Some(1,R,66)];[Some(1,L,10);Some(0,R,84)];[Some(1,L,12);None];[Some(1,L,14);Some(0,R,64)];[Some(0,R,65);None];[Some(0,R,67);None];[Some(0,R,69);None];[Some(0,R,71);None];[Some(1,R,65);None];[Some(1,R,67);None];[Some(1,R,69);None];[Some(1,R,71);None];[Some(0,L,24);None];[Some(1,R,53);None];[Some(0,L,28);None];[Some(1,R,34);None];[Some(1,L,24);None];[Some(1,R,84);None];[Some(1,L,28);None];[Some(1,R,64);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,49)];[Some(0,R,19);Some(1,L,24)];[Some(0,R,21);Some(0,R,53)];[Some(0,R,23);Some(0,R,53)];[Some(1,R,17);Some(1,R,49)];[Some(1,R,19);Some(0,L,24)];[Some(1,R,21);Some(1,R,53)];[Some(1,R,23);Some(1,R,53)];[Some(1,L,24);Some(0,L,24)];[Some(1,L,24);Some(0,L,26)];[Some(1,R,49);Some(0,L,28)];[Some(1,R,49);Some(0,L,30)];[Some(1,R,66);Some(1,L,24)];[Some(1,R,66);Some(1,L,26)];[None;Some(1,L,28)];[None;Some(1,L,30)];[Some(0,R,32);Some(0,R,53)];[Some(0,R,34);Some(0,R,34)];[Some(0,R,36);Some(0,L,12)];[Some(0,R,38);Some(0,R,38)];[Some(1,R,32);Some(1,R,53)];[Some(1,R,34);Some(1,R,34)];[Some(1,R,36);Some(0,L,72)];[Some(1,R,38);Some(1,R,38)];[Some(0,L,12);Some(0,L,72)];[Some(1,R,66);Some(0,L,74)];[Some(0,R,38);Some(0,L,76)];[None;Some(0,L,78)];[Some(1,L,12);Some(1,L,72)];[Some(0,R,66);Some(1,L,74)];[Some(0,R,68);Some(1,L,76)];[None;Some(1,L,78)];[Some(0,R,49);Some(0,R,80)];[Some(0,R,51);Some(0,R,82)];[Some(0,R,53);Some(0,R,84)];[Some(0,R,55);Some(0,R,86)];[Some(1,R,49);Some(1,R,80)];[Some(1,R,51);Some(1,R,82)];[Some(1,R,53);Some(1,R,84)];[Some(1,R,55);Some(1,R,86)];[Some(0,L,74);Some(0,L,12)];[Some(1,R,53);None];[Some(0,L,78);Some(0,R,38)];[Some(1,R,34);None];[Some(1,L,74);Some(1,L,12)];[Some(1,R,84);None];[Some(1,L,78);Some(0,R,68)];[Some(1,R,64);None];[Some(0,R,80);Some(0,R,64)];[Some(1,R,66);Some(0,R,66)];[Some(0,R,84);Some(0,R,68)];[Some(0,R,84);Some(0,R,70)];[Some(1,R,80);Some(1,R,64)];[Some(1,L,24);Some(1,R,66)];[Some(1,R,84);Some(1,R,68)];[Some(1,R,84);Some(1,R,70)];[Some(0,L,25);Some(1,L,24)];[Some(0,L,27);Some(0,R,53)];[Some(0,L,29);Some(1,R,49)];[Some(0,L,31);Some(0,R,34)];[Some(1,L,25);Some(1,R,66)];[Some(1,L,27);Some(0,R,84)];[Some(1,L,29);None];[Some(1,L,31);Some(0,R,64)];[Some(0,R,34);Some(0,R,64)];[Some(1,R,66);Some(0,R,66)];[Some(0,R,38);Some(0,R,68)];[Some(0,L,8);Some(0,R,70)];[Some(1,R,34);Some(1,R,64)];[Some(1,L,24);Some(1,R,66)];[Some(1,R,38);Some(1,R,68)];[Some(1,L,24);Some(1,R,70)];[Some(0,L,8);Some(1,L,24)];[Some(0,L,10);Some(0,R,53)];[Some(0,L,12);Some(1,R,49)];[Some(0,L,14);Some(0,R,34)];[Some(1,L,8);Some(1,R,66)];[Some(1,L,10);Some(0,R,84)];[Some(1,L,12);None];[Some(1,L,14);Some(0,R,64)];[Some(0,R,49);None];[Some(0,R,51);None];[Some(0,R,53);None];[Some(0,R,55);None];[Some(1,R,49);None];[Some(1,R,51);None];[Some(1,R,53);None];[Some(1,R,55);None];[Some(0,L,74);None];[Some(1,R,53);None];[Some(0,L,78);None];[Some(1,R,34);None];[Some(1,L,74);None];[Some(1,R,84);None];[Some(1,L,78);None];[Some(1,R,64);None]]%N.
Definition tm1 := TM'_from_str "1LB1RE_0LD0LC_0LI1LB_1RE1LB_0RF0RJ_1RA1RG_1RH---_1RE0RE_1LB0LB_1RK1RL_0RA0RG_0RK0RL".
Definition tm2 := TM'_from_str "1LB1RE_0LD0LC_0LI1LB_1RE1LB_0RF0RJ_1RA1RG_1RH1RM_1RE0RE_1LB0LB_1RK1RL_0RA0RG_0RK0RL_1RM1RM".
Definition l0 := [1;0;1;1;0;0;1;1;1;0;1;0;1;1;0;1]%N.
Definition mp := mp_from_list [53;24;72;12;66;38;84;65;8;68;34;64]%N.
Definition mp' := mp_from_list [53;24;72;12;66;38;84;49;8;68;34;64]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 11%N l0 (NG 0 1000 1000 1 1 0 0 false) 53 53.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM21.


Module TM22.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_0LA---".
Definition tm' := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC1LF_0LA---".
Definition tm0 := TM'_from_list [[Some(1,R,50);Some(0,R,48)];[Some(1,R,50);Some(0,R,50)];[Some(0,L,41);Some(0,R,52)];[Some(1,L,10);Some(0,R,54)];[Some(1,L,58);Some(1,R,48)];[Some(1,L,58);Some(1,R,50)];[Some(0,L,89);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,45)];[Some(0,L,27);Some(1,R,50)];[Some(0,L,29);Some(0,R,5)];[Some(0,L,31);Some(0,R,1)];[Some(1,L,25);Some(1,L,45)];[Some(1,L,27);Some(0,R,50)];[Some(1,L,29);Some(0,R,52)];[Some(1,L,31);Some(0,R,48)];[Some(0,R,32);Some(0,R,5)];[Some(0,R,34);Some(0,L,29)];[Some(0,R,36);Some(0,L,28)];[Some(0,R,38);None];[Some(1,R,32);Some(1,R,5)];[Some(1,R,34);Some(0,R,5)];[Some(1,R,36);Some(0,R,5)];[Some(1,R,38);None];[Some(0,L,45);Some(0,L,72)];[Some(0,L,24);Some(0,L,74)];[Some(0,R,5);Some(0,L,76)];[Some(0,L,28);Some(0,L,78)];[Some(1,L,45);Some(1,L,72)];[Some(1,L,24);Some(1,L,74)];[Some(0,R,52);Some(1,L,76)];[Some(1,L,28);Some(1,L,78)];[Some(0,R,1);Some(1,R,50)];[Some(0,R,3);Some(0,R,1)];[Some(0,R,5);Some(0,L,41)];[Some(0,R,7);Some(0,R,5)];[Some(1,R,1);Some(1,L,58)];[Some(1,R,3);Some(1,R,1)];[Some(1,R,5);Some(0,L,89)];[Some(1,R,7);Some(1,R,5)];[Some(0,L,74);Some(0,L,56)];[Some(1,L,58);Some(0,L,58)];[Some(0,L,78);Some(0,L,60)];[Some(1,R,1);Some(0,L,62)];[Some(1,L,74);Some(1,L,56)];[Some(1,R,50);Some(1,L,58)];[Some(1,L,78);Some(1,L,60)];[Some(1,R,48);Some(1,L,62)];[Some(0,R,1);Some(0,R,48)];[Some(1,L,58);Some(0,R,50)];[Some(0,R,5);Some(0,R,52)];[Some(0,L,10);Some(0,R,54)];[Some(1,R,1);Some(1,R,48)];[Some(0,L,58);Some(1,R,50)];[Some(1,R,5);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,24);Some(0,L,45)];[Some(0,L,26);Some(1,R,50)];[Some(0,L,28);Some(0,R,5)];[Some(0,L,30);Some(0,R,1)];[Some(1,L,24);Some(1,L,45)];[Some(1,L,26);Some(0,R,50)];[Some(1,L,28);Some(0,R,52)];[Some(1,L,30);Some(0,R,48)];[Some(0,R,50);Some(1,L,24)];[Some(1,L,45);None];[Some(0,R,54);Some(0,R,50)];[Some(0,R,50);None];[Some(1,R,50);Some(1,L,74)];[Some(1,L,72);None];[Some(1,R,54);Some(1,R,50)];[Some(1,R,50);None];[Some(0,L,41);Some(0,L,89)];[Some(0,L,43);Some(0,L,91)];[Some(0,L,45);Some(0,L,93)];[Some(0,L,47);Some(0,L,95)];[Some(1,L,41);Some(1,L,89)];[Some(1,L,43);Some(1,L,91)];[Some(1,L,45);Some(1,L,93)];[Some(1,L,47);Some(1,L,95)];[Some(0,L,45);None];[Some(0,R,1);None];[Some(0,L,45);None];[Some(0,R,5);None];[Some(0,L,72);None];[Some(1,R,1);None];[Some(0,L,93);None];[Some(1,R,5);None];[Some(0,L,8);None];[Some(0,L,10);None];[Some(0,L,12);None];[Some(0,L,14);None];[Some(1,L,8);None];[Some(1,L,10);None];[Some(1,L,12);None];[Some(1,L,14);None]]%N.
Definition tm0' := TM'_from_list [[Some(1,R,50);Some(0,R,48)];[Some(1,R,50);Some(0,R,50)];[Some(0,L,41);Some(0,R,52)];[Some(1,L,10);Some(0,R,54)];[Some(1,L,58);Some(1,R,48)];[Some(1,L,58);Some(1,R,50)];[Some(0,L,89);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,45)];[Some(0,L,27);Some(1,R,50)];[Some(0,L,29);Some(0,R,5)];[Some(0,L,31);Some(0,L,45)];[Some(1,L,25);Some(1,L,45)];[Some(1,L,27);Some(0,R,50)];[Some(1,L,29);Some(0,R,36)];[Some(1,L,31);Some(1,L,45)];[Some(0,R,32);Some(0,R,5)];[Some(0,R,34);Some(0,L,29)];[Some(0,R,36);Some(0,L,28)];[Some(0,R,38);None];[Some(1,R,32);Some(1,R,5)];[Some(1,R,34);Some(0,R,5)];[Some(1,R,36);Some(0,R,5)];[Some(1,R,38);None];[Some(0,L,45);Some(0,L,72)];[Some(0,L,24);Some(0,L,74)];[Some(0,R,5);Some(0,L,76)];[Some(0,L,28);Some(0,L,78)];[Some(1,L,45);Some(1,L,72)];[Some(1,L,24);Some(1,L,74)];[Some(0,R,36);Some(1,L,76)];[Some(1,L,28);Some(1,L,78)];[Some(0,R,1);Some(1,R,50)];[Some(0,R,3);Some(0,R,1)];[Some(0,R,5);Some(0,L,41)];[Some(0,R,7);Some(0,R,5)];[Some(1,R,1);Some(1,L,58)];[Some(1,R,3);Some(1,R,1)];[Some(1,R,5);Some(0,L,89)];[Some(1,R,7);Some(1,R,5)];[Some(0,L,74);Some(0,L,56)];[Some(1,L,58);Some(0,L,58)];[Some(0,L,78);Some(0,L,60)];[Some(1,R,1);Some(0,L,62)];[Some(1,L,74);Some(1,L,56)];[Some(1,R,50);Some(1,L,58)];[Some(1,L,78);Some(1,L,60)];[Some(1,L,58);Some(1,L,62)];[Some(0,R,1);Some(0,R,32)];[Some(1,L,58);Some(0,R,34)];[Some(0,R,5);Some(0,R,36)];[Some(0,L,10);Some(0,R,38)];[Some(1,R,1);Some(1,R,32)];[Some(0,L,58);Some(1,R,34)];[Some(1,R,5);Some(1,R,36)];[None;Some(1,R,38)];[Some(0,L,24);Some(0,L,45)];[Some(0,L,26);Some(0,L,24)];[Some(0,L,28);Some(0,R,5)];[Some(0,L,30);Some(0,L,28)];[Some(1,L,24);Some(1,L,45)];[Some(1,L,26);Some(1,L,24)];[Some(1,L,28);Some(0,R,36)];[Some(1,L,30);Some(1,L,28)];[Some(0,R,50);Some(1,L,24)];[Some(1,L,45);None];[Some(0,R,54);Some(0,R,50)];[Some(0,R,50);None];[Some(1,R,50);Some(1,L,74)];[Some(1,L,72);None];[Some(1,R,54);Some(1,R,50)];[Some(1,R,50);None];[Some(0,L,41);Some(0,L,89)];[Some(0,L,43);Some(0,L,91)];[Some(0,L,45);Some(0,L,93)];[Some(0,L,47);Some(0,L,95)];[Some(1,L,41);Some(1,L,89)];[Some(1,L,43);Some(1,L,91)];[Some(1,L,45);Some(1,L,93)];[Some(1,L,47);Some(1,L,95)];[Some(0,L,45);None];[Some(0,R,1);None];[Some(0,L,45);None];[Some(0,R,5);None];[Some(0,L,72);None];[Some(1,R,1);None];[Some(0,L,93);None];[Some(1,R,5);None];[Some(0,L,8);None];[Some(0,L,10);None];[Some(0,L,12);None];[Some(0,L,14);None];[Some(1,L,8);None];[Some(1,L,10);None];[Some(1,L,12);None];[Some(1,L,14);None]]%N.
Definition tm1 := TM'_from_str "1LB1RE_0LC0RA_1LD1LH_1RE1LB_0RA0RF_1RG---_1RE0RE_0LI0LJ_1LB0LB_0LK---_0LL0RA_1LM1LN_0LD0LH_0LD0LO_1LK---".
Definition tm2 := TM'_from_str "1LB1RE_0LC0RA_1LD1LH_1RE1LB_0RA0RF_1RG---_1RE0RE_0LI0LJ_1LB0LB_0LK1RP_0LL0RA_1LM1LN_0LD0LH_0LD0LO_1LK1RP_1RP1RP".
Definition l0 := [1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [5;58;28;45;50;52;1;72;41;89;10;29;24;74;93]%N.
Definition mp' := mp_from_list [5;58;28;45;50;36;1;72;41;89;10;29;24;74;93]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 14%N l0 (NG 0 1000 1000 1 1 0 0 true) 48 48.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM22.


Module TM23.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC0LF_0LA---".
Definition tm' := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC0LF_0LA---".
Definition tm0 := TM'_from_list [[Some(1,R,50);Some(0,R,48)];[Some(1,R,50);Some(0,R,50)];[Some(0,L,41);Some(0,R,52)];[Some(1,L,8);Some(0,R,54)];[Some(1,L,58);Some(1,R,48)];[Some(1,L,58);Some(1,R,50)];[Some(0,L,88);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,45)];[Some(0,L,27);Some(1,R,50)];[Some(0,L,29);Some(0,R,5)];[Some(0,L,31);Some(0,L,45)];[Some(1,L,25);Some(1,L,45)];[Some(1,L,27);Some(0,R,50)];[Some(1,L,29);Some(0,R,36)];[Some(1,L,31);Some(1,L,45)];[Some(0,R,32);Some(0,R,5)];[Some(0,R,34);Some(0,L,25)];[Some(0,R,36);Some(0,L,28)];[Some(0,R,38);None];[Some(1,R,32);Some(1,R,5)];[Some(1,R,34);Some(0,L,45)];[Some(1,R,36);Some(0,R,5)];[Some(1,R,38);None];[Some(0,L,45);Some(0,L,72)];[Some(0,L,24);Some(0,L,74)];[Some(0,R,5);Some(0,L,76)];[Some(0,L,28);Some(0,L,78)];[Some(1,L,45);Some(1,L,72)];[Some(1,L,24);Some(1,L,74)];[Some(0,R,36);Some(1,L,76)];[Some(1,L,28);Some(1,L,78)];[Some(0,R,1);Some(1,R,50)];[Some(0,R,3);Some(0,R,1)];[Some(0,R,5);Some(0,L,41)];[Some(0,R,7);Some(0,R,5)];[Some(1,R,1);Some(1,L,58)];[Some(1,R,3);Some(1,R,1)];[Some(1,R,5);Some(0,L,88)];[Some(1,R,7);Some(1,R,5)];[Some(0,L,74);Some(0,L,56)];[Some(1,L,58);Some(0,L,58)];[Some(0,L,78);Some(0,L,60)];[Some(1,R,1);Some(0,L,62)];[Some(1,L,74);Some(1,L,56)];[Some(1,R,50);Some(1,L,58)];[Some(1,L,78);Some(1,L,60)];[Some(1,L,58);Some(1,L,62)];[Some(0,R,1);Some(0,R,32)];[Some(1,L,58);Some(0,R,34)];[Some(0,R,5);Some(0,R,36)];[Some(0,L,8);Some(0,R,38)];[Some(1,R,1);Some(1,R,32)];[Some(0,L,58);Some(1,R,34)];[Some(1,R,5);Some(1,R,36)];[None;Some(1,R,38)];[Some(0,L,24);Some(0,L,45)];[Some(0,L,26);Some(0,L,24)];[Some(0,L,28);Some(0,R,5)];[Some(0,L,30);Some(0,L,28)];[Some(1,L,24);Some(1,L,45)];[Some(1,L,26);Some(1,L,24)];[Some(1,L,28);Some(0,R,36)];[Some(1,L,30);Some(1,L,28)];[Some(0,R,50);Some(0,L,24)];[Some(1,L,45);None];[Some(0,R,54);Some(1,R,50)];[Some(0,R,50);None];[Some(1,R,50);Some(0,L,74)];[Some(1,L,72);None];[Some(1,R,54);Some(1,L,58)];[Some(1,R,50);None];[Some(0,L,41);Some(0,L,88)];[Some(0,L,43);Some(0,L,90)];[Some(0,L,45);Some(0,L,92)];[Some(0,L,47);Some(0,L,94)];[Some(1,L,41);Some(1,L,88)];[Some(1,L,43);Some(1,L,90)];[Some(1,L,45);Some(1,L,92)];[Some(1,L,47);Some(1,L,94)];[Some(0,L,45);None];[Some(0,R,1);None];[Some(0,L,45);None];[Some(0,R,5);None];[Some(0,L,72);None];[Some(1,R,1);None];[Some(0,L,92);None];[Some(1,R,5);None];[Some(0,L,8);None];[Some(0,L,10);None];[Some(0,L,12);None];[Some(0,L,14);None];[Some(1,L,8);None];[Some(1,L,10);None];[Some(1,L,12);None];[Some(1,L,14);None]]%N.
Definition tm0' := TM'_from_list [[Some(1,R,50);Some(0,R,48)];[Some(1,R,50);Some(0,R,50)];[Some(0,L,41);Some(0,R,52)];[Some(1,L,8);Some(0,R,54)];[Some(1,L,58);Some(1,R,48)];[Some(1,L,58);Some(1,R,50)];[Some(0,L,88);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,45)];[Some(0,L,27);Some(1,R,50)];[Some(0,L,29);Some(0,R,5)];[Some(0,L,31);Some(0,R,1)];[Some(1,L,25);Some(1,L,45)];[Some(1,L,27);Some(0,R,50)];[Some(1,L,29);Some(0,R,52)];[Some(1,L,31);Some(0,R,48)];[Some(0,R,32);Some(0,R,5)];[Some(0,R,34);Some(0,L,25)];[Some(0,R,36);Some(0,L,28)];[Some(0,R,38);None];[Some(1,R,32);Some(1,R,5)];[Some(1,R,34);Some(0,L,45)];[Some(1,R,36);Some(0,R,5)];[Some(1,R,38);None];[Some(0,L,45);Some(0,L,72)];[Some(0,L,24);Some(0,L,74)];[Some(0,R,5);Some(0,L,76)];[Some(0,L,28);Some(0,L,78)];[Some(1,L,45);Some(1,L,72)];[Some(1,L,24);Some(1,L,74)];[Some(0,R,52);Some(1,L,76)];[Some(1,L,28);Some(1,L,78)];[Some(0,R,1);Some(1,R,50)];[Some(0,R,3);Some(0,R,1)];[Some(0,R,5);Some(0,L,41)];[Some(0,R,7);Some(0,R,5)];[Some(1,R,1);Some(1,L,58)];[Some(1,R,3);Some(1,R,1)];[Some(1,R,5);Some(0,L,88)];[Some(1,R,7);Some(1,R,5)];[Some(0,L,74);Some(0,L,56)];[Some(1,L,58);Some(0,L,58)];[Some(0,L,78);Some(0,L,60)];[Some(1,R,1);Some(0,L,62)];[Some(1,L,74);Some(1,L,56)];[Some(1,R,50);Some(1,L,58)];[Some(1,L,78);Some(1,L,60)];[Some(1,R,48);Some(1,L,62)];[Some(0,R,1);Some(0,R,48)];[Some(1,L,58);Some(0,R,50)];[Some(0,R,5);Some(0,R,52)];[Some(0,L,8);Some(0,R,54)];[Some(1,R,1);Some(1,R,48)];[Some(0,L,58);Some(1,R,50)];[Some(1,R,5);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,24);Some(0,L,45)];[Some(0,L,26);Some(1,R,50)];[Some(0,L,28);Some(0,R,5)];[Some(0,L,30);Some(0,R,1)];[Some(1,L,24);Some(1,L,45)];[Some(1,L,26);Some(0,R,50)];[Some(1,L,28);Some(0,R,52)];[Some(1,L,30);Some(0,R,48)];[Some(0,R,50);Some(0,L,24)];[Some(1,L,45);None];[Some(0,R,54);Some(1,R,50)];[Some(0,R,50);None];[Some(1,R,50);Some(0,L,74)];[Some(1,L,72);None];[Some(1,R,54);Some(1,L,58)];[Some(1,R,50);None];[Some(0,L,41);Some(0,L,88)];[Some(0,L,43);Some(0,L,90)];[Some(0,L,45);Some(0,L,92)];[Some(0,L,47);Some(0,L,94)];[Some(1,L,41);Some(1,L,88)];[Some(1,L,43);Some(1,L,90)];[Some(1,L,45);Some(1,L,92)];[Some(1,L,47);Some(1,L,94)];[Some(0,L,45);None];[Some(0,R,1);None];[Some(0,L,45);None];[Some(0,R,5);None];[Some(0,L,72);None];[Some(1,R,1);None];[Some(0,L,92);None];[Some(1,R,5);None];[Some(0,L,8);None];[Some(0,L,10);None];[Some(0,L,12);None];[Some(0,L,14);None];[Some(1,L,8);None];[Some(1,L,10);None];[Some(1,L,12);None];[Some(1,L,14);None]]%N.
Definition tm1 := TM'_from_str "1LB1RE_0LC0RA_1LD1LH_1RE1LB_0RA0RF_1RG---_1RE0RE_0LI0LJ_1LB0LB_0LK---_0LL0LD_0LM0LN_0LD0LH_0LD0LO_1LK---".
Definition tm2 := TM'_from_str "1LB1RE_0LC0RA_1LD1LH_1RE1LB_0RA0RF_1RG---_1RE0RE_0LI0LJ_1LB0LB_0LK1RP_0LL0LD_0LM0LN_0LD0LH_0LD0LO_1LK1RP_1RP1RP".
Definition l0 := [1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [5;58;28;45;50;36;1;72;41;88;8;25;24;74;92]%N.
Definition mp' := mp_from_list [5;58;28;45;50;52;1;72;41;88;8;25;24;74;92]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 14%N l0 (NG 0 1000 1000 1 1 0 0 true) 48 48.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM23.


Module TM24.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC1LF_0LC---".
Definition tm' := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_0LC---".
Definition tm0 := TM'_from_list [[Some(1,R,50);Some(0,R,48)];[Some(1,R,50);Some(0,R,50)];[Some(0,L,41);Some(0,R,52)];[Some(1,L,42);Some(0,R,54)];[Some(1,L,58);Some(1,R,48)];[Some(1,L,58);Some(1,R,50)];[Some(0,L,89);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,45)];[Some(0,L,27);Some(1,R,50)];[Some(0,L,29);Some(0,R,5)];[Some(0,L,31);Some(0,L,45)];[Some(1,L,25);Some(1,L,45)];[Some(1,L,27);Some(0,R,50)];[Some(1,L,29);Some(0,R,36)];[Some(1,L,31);Some(1,L,45)];[Some(0,R,32);Some(0,R,5)];[Some(0,R,34);Some(0,L,78)];[Some(0,R,36);Some(0,L,28)];[Some(0,R,38);None];[Some(1,R,32);Some(1,R,5)];[Some(1,R,34);Some(0,L,60)];[Some(1,R,36);Some(0,R,5)];[Some(1,R,38);None];[Some(0,L,45);Some(0,L,72)];[Some(0,L,24);Some(0,L,74)];[Some(0,R,5);Some(0,L,76)];[Some(0,L,28);Some(0,L,78)];[Some(1,L,45);Some(1,L,72)];[Some(1,L,24);Some(1,L,74)];[Some(0,R,36);Some(1,L,76)];[Some(1,L,28);Some(1,L,78)];[Some(0,R,1);Some(1,R,50)];[Some(0,R,3);Some(0,R,1)];[Some(0,R,5);Some(0,L,41)];[Some(0,R,7);Some(0,R,5)];[Some(1,R,1);Some(1,L,58)];[Some(1,R,3);Some(1,R,1)];[Some(1,R,5);Some(0,L,89)];[Some(1,R,7);Some(1,R,5)];[Some(0,L,74);Some(0,L,56)];[Some(1,L,58);Some(0,L,58)];[Some(0,L,78);Some(0,L,60)];[Some(1,R,1);Some(0,L,62)];[Some(1,L,74);Some(1,L,56)];[Some(1,R,50);Some(1,L,58)];[Some(1,L,78);Some(1,L,60)];[Some(1,L,58);Some(1,L,62)];[Some(0,R,1);Some(0,R,32)];[Some(1,L,58);Some(0,R,34)];[Some(0,R,5);Some(0,R,36)];[Some(0,L,42);Some(0,R,38)];[Some(1,R,1);Some(1,R,32)];[Some(0,L,58);Some(1,R,34)];[Some(1,R,5);Some(1,R,36)];[None;Some(1,R,38)];[Some(0,L,24);Some(0,L,45)];[Some(0,L,26);Some(0,L,24)];[Some(0,L,28);Some(0,R,5)];[Some(0,L,30);Some(0,L,28)];[Some(1,L,24);Some(1,L,45)];[Some(1,L,26);Some(1,L,24)];[Some(1,L,28);Some(0,R,36)];[Some(1,L,30);Some(1,L,28)];[Some(0,R,50);Some(1,L,45)];[Some(1,L,45);None];[Some(0,R,54);Some(1,L,24)];[Some(0,R,50);None];[Some(1,R,50);Some(1,L,93)];[Some(1,L,72);None];[Some(1,R,54);Some(1,L,45)];[Some(1,R,50);None];[Some(0,L,41);Some(0,L,89)];[Some(0,L,43);Some(0,L,91)];[Some(0,L,45);Some(0,L,93)];[Some(0,L,47);Some(0,L,95)];[Some(1,L,41);Some(1,L,89)];[Some(1,L,43);Some(1,L,91)];[Some(1,L,45);Some(1,L,93)];[Some(1,L,47);Some(1,L,95)];[Some(1,R,50);None];[Some(0,L,45);None];[Some(1,L,42);None];[Some(1,R,50);None];[Some(1,L,58);None];[Some(0,L,72);None];[None;None];[Some(1,L,58);None];[Some(0,L,40);None];[Some(0,L,42);None];[Some(0,L,44);None];[Some(0,L,46);None];[Some(1,L,40);None];[Some(1,L,42);None];[Some(1,L,44);None];[Some(1,L,46);None]]%N.
Definition tm0' := TM'_from_list [[Some(1,R,50);Some(0,R,48)];[Some(1,R,50);Some(0,R,50)];[Some(0,L,41);Some(0,R,52)];[Some(1,L,42);Some(0,R,54)];[Some(1,L,58);Some(1,R,48)];[Some(1,L,58);Some(1,R,50)];[Some(0,L,89);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,45)];[Some(0,L,27);Some(1,R,50)];[Some(0,L,29);Some(0,R,5)];[Some(0,L,31);Some(0,R,1)];[Some(1,L,25);Some(1,L,45)];[Some(1,L,27);Some(0,R,50)];[Some(1,L,29);Some(0,R,52)];[Some(1,L,31);Some(0,R,48)];[Some(0,R,32);Some(0,R,5)];[Some(0,R,34);Some(0,L,78)];[Some(0,R,36);Some(0,L,28)];[Some(0,R,38);None];[Some(1,R,32);Some(1,R,5)];[Some(1,R,34);Some(0,L,60)];[Some(1,R,36);Some(0,R,5)];[Some(1,R,38);None];[Some(0,L,45);Some(0,L,72)];[Some(0,L,24);Some(0,L,74)];[Some(0,R,5);Some(0,L,76)];[Some(0,L,28);Some(0,L,78)];[Some(1,L,45);Some(1,L,72)];[Some(1,L,24);Some(1,L,74)];[Some(0,R,52);Some(1,L,76)];[Some(1,L,28);Some(1,L,78)];[Some(0,R,1);Some(1,R,50)];[Some(0,R,3);Some(0,R,1)];[Some(0,R,5);Some(0,L,41)];[Some(0,R,7);Some(0,R,5)];[Some(1,R,1);Some(1,L,58)];[Some(1,R,3);Some(1,R,1)];[Some(1,R,5);Some(0,L,89)];[Some(1,R,7);Some(1,R,5)];[Some(0,L,74);Some(0,L,56)];[Some(1,L,58);Some(0,L,58)];[Some(0,L,78);Some(0,L,60)];[Some(1,R,1);Some(0,L,62)];[Some(1,L,74);Some(1,L,56)];[Some(1,R,50);Some(1,L,58)];[Some(1,L,78);Some(1,L,60)];[Some(1,R,48);Some(1,L,62)];[Some(0,R,1);Some(0,R,48)];[Some(1,L,58);Some(0,R,50)];[Some(0,R,5);Some(0,R,52)];[Some(0,L,42);Some(0,R,54)];[Some(1,R,1);Some(1,R,48)];[Some(0,L,58);Some(1,R,50)];[Some(1,R,5);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,24);Some(0,L,45)];[Some(0,L,26);Some(1,R,50)];[Some(0,L,28);Some(0,R,5)];[Some(0,L,30);Some(0,R,1)];[Some(1,L,24);Some(1,L,45)];[Some(1,L,26);Some(0,R,50)];[Some(1,L,28);Some(0,R,52)];[Some(1,L,30);Some(0,R,48)];[Some(0,R,50);Some(1,L,45)];[Some(1,L,45);None];[Some(0,R,54);Some(1,L,24)];[Some(0,R,50);None];[Some(1,R,50);Some(1,L,93)];[Some(1,L,72);None];[Some(1,R,54);Some(1,L,45)];[Some(1,R,50);None];[Some(0,L,41);Some(0,L,89)];[Some(0,L,43);Some(0,L,91)];[Some(0,L,45);Some(0,L,93)];[Some(0,L,47);Some(0,L,95)];[Some(1,L,41);Some(1,L,89)];[Some(1,L,43);Some(1,L,91)];[Some(1,L,45);Some(1,L,93)];[Some(1,L,47);Some(1,L,95)];[Some(1,R,50);None];[Some(0,L,45);None];[Some(1,L,42);None];[Some(1,R,50);None];[Some(1,L,58);None];[Some(0,L,72);None];[None;None];[Some(1,L,58);None];[Some(0,L,40);None];[Some(0,L,42);None];[Some(0,L,44);None];[Some(0,L,46);None];[Some(1,L,40);None];[Some(1,L,42);None];[Some(1,L,44);None];[Some(1,L,46);None]]%N.
Definition tm1 := TM'_from_str "1LB1RE_0LC0RA_1LD1LH_1RE1LB_0RA0RF_1RG---_1RE0RE_0LI0LJ_1LB0LB_0LK---_0LL0LN_1LD1LM_1LK---_1LO1LD_0LD0LH".
Definition tm2 := TM'_from_str "1LB1RE_0LC0RA_1LD1LH_1RE1LB_0RA0RF_1RG---_1RE0RE_0LI0LJ_1LB0LB_0LK1RP_0LL0LN_1LD1LM_1LK1RP_1LO1LD_0LD0LH_1RP1RP".
Definition l0 := [1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [5;58;28;45;50;36;1;72;41;89;42;78;93;60;24]%N.
Definition mp' := mp_from_list [5;58;28;45;50;52;1;72;41;89;42;78;93;60;24]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 14%N l0 (NG 0 1000 1000 1 1 0 0 true) 48 48.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM24.


Module TM25.
Definition tm := TM_from_str "1LB0LB_0RC0RF_0RD1RB_1LE0LE_0LA---_0RB0LD".
Definition tm' := TM_from_str "1LB0RD_0RC0RF_0RD1RB_1LE0LE_0LA---_0RB0LD".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,48)];[Some(0,L,29);Some(0,R,16)];[Some(0,R,21);Some(0,R,52)];[None;Some(0,R,20)];[Some(1,R,17);Some(1,R,48)];[Some(0,L,28);Some(1,R,16)];[Some(1,R,21);Some(1,R,52)];[None;Some(1,R,20)];[Some(0,L,25);Some(0,L,24)];[Some(0,L,27);Some(0,L,26)];[Some(0,L,29);Some(0,L,28)];[Some(0,L,31);Some(0,L,30)];[Some(1,L,25);Some(1,L,24)];[Some(1,L,27);Some(1,L,26)];[Some(1,L,29);Some(1,L,28)];[Some(1,L,31);Some(1,L,30)];[Some(0,R,32);Some(0,R,80)];[Some(0,R,34);Some(0,R,82)];[Some(0,R,36);Some(0,R,84)];[Some(0,R,38);Some(0,R,86)];[Some(1,R,32);Some(1,R,80)];[Some(1,R,34);Some(1,R,82)];[Some(1,R,36);Some(1,R,84)];[Some(1,R,38);Some(1,R,86)];[Some(0,L,29);Some(0,R,48)];[Some(0,R,52);Some(0,L,73)];[Some(0,L,25);Some(0,R,16)];[Some(0,R,20);Some(0,L,77)];[Some(1,L,29);Some(0,R,17)];[Some(0,R,21);Some(1,L,73)];[Some(1,L,25);Some(0,L,29)];[None;Some(1,L,77)];[Some(0,R,48);Some(0,R,17)];[Some(0,R,50);Some(0,R,19)];[Some(0,R,52);Some(0,R,21)];[Some(0,R,54);Some(0,R,23)];[Some(1,R,48);Some(1,R,17)];[Some(1,R,50);Some(1,R,19)];[Some(1,R,52);Some(1,R,21)];[Some(1,R,54);Some(1,R,23)];[Some(0,L,10);Some(1,L,73)];[Some(0,L,8);Some(1,R,32)];[Some(0,L,14);Some(1,R,34)];[Some(0,L,12);None];[Some(1,L,10);Some(0,L,73)];[Some(1,L,8);Some(1,R,80)];[Some(1,L,14);Some(1,R,82)];[Some(1,L,12);None];[Some(0,R,21);Some(0,R,52)];[None;None];[Some(1,L,29);Some(0,L,29)];[None;None];[Some(1,L,73);Some(0,L,73)];[None;None];[Some(0,R,17);Some(0,R,48)];[None;None];[Some(0,L,73);Some(0,L,72)];[Some(0,L,75);Some(0,L,74)];[Some(0,L,77);Some(0,L,76)];[Some(0,L,79);Some(0,L,78)];[Some(1,L,73);Some(1,L,72)];[Some(1,L,75);Some(1,L,74)];[Some(1,L,77);Some(1,L,76)];[Some(1,L,79);Some(1,L,78)];[Some(0,R,34);None];[Some(0,R,21);None];[Some(0,L,10);None];[Some(0,R,32);None];[Some(1,R,34);None];[Some(1,L,73);None];[None;None];[Some(1,R,32);None];[Some(0,L,8);None];[Some(0,L,10);None];[Some(0,L,12);None];[Some(0,L,14);None];[Some(1,L,8);None];[Some(1,L,10);None];[Some(1,L,12);None];[Some(1,L,14);None];[Some(0,R,16);Some(0,L,29)];[Some(0,R,18);Some(0,L,25)];[Some(0,R,20);None];[Some(0,R,22);None];[Some(1,R,16);Some(0,L,28)];[Some(1,R,18);Some(0,L,24)];[Some(1,R,20);None];[Some(1,R,22);None];[Some(0,R,21);Some(0,L,56)];[Some(0,R,32);Some(0,L,58)];[Some(0,R,34);Some(0,L,60)];[Some(0,L,10);Some(0,L,62)];[Some(0,R,52);Some(1,L,56)];[Some(0,R,80);Some(1,L,58)];[Some(0,R,82);Some(1,L,60)];[Some(1,L,10);Some(1,L,62)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,48)];[Some(0,L,29);Some(0,R,50)];[Some(0,R,21);Some(0,R,52)];[None;Some(0,R,54)];[Some(1,R,17);Some(1,R,48)];[Some(0,L,14);Some(1,R,50)];[Some(1,R,21);Some(1,R,52)];[None;Some(1,R,54)];[Some(0,L,25);Some(0,L,10)];[Some(0,L,27);Some(0,L,8)];[Some(0,L,29);Some(0,L,14)];[Some(0,L,31);Some(0,L,12)];[Some(1,L,25);Some(1,L,10)];[Some(1,L,27);Some(1,L,8)];[Some(1,L,29);Some(1,L,14)];[Some(1,L,31);Some(1,L,12)];[Some(0,R,32);Some(0,R,80)];[Some(0,R,34);Some(0,R,82)];[Some(0,R,36);Some(0,R,84)];[Some(0,R,38);Some(0,R,86)];[Some(1,R,32);Some(1,R,80)];[Some(1,R,34);Some(1,R,82)];[Some(1,R,36);Some(1,R,84)];[Some(1,R,38);Some(1,R,86)];[Some(0,L,29);Some(0,R,48)];[Some(0,R,52);Some(0,L,73)];[Some(0,L,25);Some(0,R,16)];[Some(0,R,20);Some(0,L,77)];[Some(1,L,29);Some(0,R,17)];[Some(0,R,21);Some(1,L,73)];[Some(1,L,25);Some(0,L,29)];[None;Some(1,L,77)];[Some(0,R,48);Some(0,R,17)];[Some(0,R,50);Some(0,R,19)];[Some(0,R,52);Some(0,R,21)];[Some(0,R,54);Some(0,R,23)];[Some(1,R,48);Some(1,R,17)];[Some(1,R,50);Some(1,R,19)];[Some(1,R,52);Some(1,R,21)];[Some(1,R,54);Some(1,R,23)];[Some(0,L,10);Some(1,L,73)];[Some(0,L,8);Some(1,R,32)];[Some(0,L,14);Some(1,R,34)];[Some(0,L,12);None];[Some(1,L,10);Some(0,L,73)];[Some(1,L,8);Some(1,R,80)];[Some(1,L,14);Some(1,R,82)];[Some(1,L,12);None];[Some(0,R,21);Some(0,R,52)];[None;None];[Some(1,L,29);Some(0,L,29)];[None;None];[Some(1,L,73);Some(0,L,73)];[None;None];[Some(1,L,14);Some(0,L,14)];[None;None];[Some(0,L,73);Some(0,L,72)];[Some(0,L,75);Some(0,L,74)];[Some(0,L,77);Some(0,L,76)];[Some(0,L,79);Some(0,L,78)];[Some(1,L,73);Some(1,L,72)];[Some(1,L,75);Some(1,L,74)];[Some(1,L,77);Some(1,L,76)];[Some(1,L,79);Some(1,L,78)];[Some(0,R,34);None];[Some(0,R,21);None];[Some(0,L,10);None];[Some(1,L,29);None];[Some(1,R,34);None];[Some(1,L,73);None];[None;None];[Some(1,L,14);None];[Some(0,L,8);None];[Some(0,L,10);None];[Some(0,L,12);None];[Some(0,L,14);None];[Some(1,L,8);None];[Some(1,L,10);None];[Some(1,L,12);None];[Some(1,L,14);None];[Some(0,R,16);Some(0,L,29)];[Some(0,R,18);Some(0,L,25)];[Some(0,R,20);None];[Some(0,R,22);None];[Some(1,R,16);Some(0,L,14)];[Some(1,R,18);Some(0,L,10)];[Some(1,R,20);None];[Some(1,R,22);None];[Some(0,R,21);Some(0,L,56)];[Some(0,R,32);Some(0,L,58)];[Some(0,R,34);Some(0,L,60)];[Some(0,L,10);Some(0,L,62)];[Some(0,R,52);Some(1,L,56)];[Some(0,R,80);Some(1,L,58)];[Some(0,R,82);Some(1,L,60)];[Some(1,L,10);Some(1,L,62)]]%N.
Definition tm1 := TM'_from_str "1LB0LB_0LC---_0LD0LG_0RE1LB_1RF1RH_0RA0RE_1LD---_0RI---_1RJ1RM_0RK0RL_0RE0RA_0RF0RH_0RN0LD_0RJ0RM".
Definition tm2 := TM'_from_str "1LB0LB_0LC1RO_0LD0LG_0RE1LB_1RF1RH_0RA0RE_1LD---_0RI1RO_1RJ1RM_0RK0RL_0RE0RA_0RF0RH_0RN0LD_0RJ0RM_1RO1RO".
Definition l0 := [0;1;0;1;0;0;0;1;0;0;0;1;0;0;1;0]%N.
Definition mp := mp_from_list [52;73;10;29;21;34;28;82;20;32;48;17;80;16]%N.
Definition mp' := mp_from_list [52;73;10;29;21;34;14;82;20;32;48;17;80;16]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 true) 66 66.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM25.


Module TM26.
Definition tm := TM_from_str "1LB0LA_1LC1LD_1RD1RB_0LF1RE_1RB0RC_---1LA".
Definition tm' := TM_from_str "1LB0LA_1LC1LD_1RD1RB_0LF1RE_1RE0RC_---1LA".
Definition tm0 := TM'_from_list [[Some(0,R,38);Some(1,R,53)];[None;Some(0,L,43)];[Some(0,R,21);Some(0,L,94)];[Some(0,R,21);Some(0,L,25)];[Some(1,R,38);Some(1,R,34)];[Some(1,L,13);Some(0,L,59)];[Some(1,R,21);Some(1,R,34)];[Some(1,R,21);Some(0,L,8)];[Some(0,L,25);Some(0,L,8)];[Some(0,L,27);Some(0,L,10)];[Some(0,L,29);Some(0,L,12)];[Some(0,L,31);Some(0,L,14)];[Some(1,L,25);Some(1,L,8)];[Some(1,L,27);Some(1,L,10)];[Some(1,L,29);Some(1,L,12)];[Some(1,L,31);Some(1,L,14)];[Some(0,R,67);None];[Some(0,R,34);Some(0,R,34)];[Some(0,R,71);Some(1,L,27)];[Some(0,R,38);Some(0,R,38)];[Some(1,R,67);None];[Some(1,R,34);Some(1,R,34)];[Some(1,R,71);Some(1,L,10)];[Some(1,R,38);Some(1,R,38)];[Some(0,L,41);Some(0,L,57)];[Some(0,L,43);Some(0,L,59)];[Some(0,L,45);Some(0,L,61)];[Some(0,L,47);Some(0,L,63)];[Some(1,L,41);Some(1,L,57)];[Some(1,L,43);Some(1,L,59)];[Some(1,L,45);Some(1,L,61)];[Some(1,L,47);Some(1,L,63)];[Some(0,R,49);Some(0,R,17)];[Some(0,R,51);Some(0,R,19)];[Some(0,R,53);Some(0,R,21)];[Some(0,R,55);Some(0,R,23)];[Some(1,R,49);Some(1,R,17)];[Some(1,R,51);Some(1,R,19)];[Some(1,R,53);Some(1,R,21)];[Some(1,R,55);Some(1,R,23)];[Some(0,L,9);Some(0,L,63)];[Some(1,R,38);Some(0,L,63)];[Some(0,L,13);Some(1,R,34)];[Some(1,R,53);Some(1,R,34)];[Some(1,L,9);Some(1,R,67)];[Some(1,R,38);Some(1,R,67)];[Some(1,L,13);Some(1,R,34)];[Some(1,R,21);Some(1,R,34)];[None;Some(0,R,65)];[Some(0,L,47);Some(0,R,67)];[None;Some(0,R,69)];[Some(0,L,29);Some(0,R,71)];[None;Some(1,R,65)];[Some(0,L,63);Some(1,R,67)];[None;Some(1,R,69)];[Some(0,L,12);Some(1,R,71)];[Some(0,L,88);Some(1,R,53)];[Some(0,L,90);Some(0,L,63)];[Some(0,L,92);Some(1,R,53)];[Some(0,L,94);Some(1,R,34)];[Some(1,L,88);Some(1,R,21)];[Some(1,L,90);Some(1,R,67)];[Some(1,L,92);Some(1,R,21)];[Some(1,L,94);Some(1,R,34)];[Some(0,R,17);Some(0,R,32)];[Some(0,R,19);Some(0,R,34)];[Some(0,R,21);Some(0,R,36)];[Some(0,R,23);Some(0,R,38)];[Some(1,R,17);Some(1,R,32)];[Some(1,R,19);Some(1,R,34)];[Some(1,R,21);Some(1,R,36)];[Some(1,R,23);Some(1,R,38)];[Some(0,L,63);Some(0,L,27)];[Some(0,L,63);Some(0,R,53)];[Some(1,R,34);Some(0,R,23)];[Some(1,R,34);Some(0,R,53)];[Some(1,R,67);Some(1,L,27)];[Some(1,R,67);Some(0,R,21)];[Some(1,R,34);Some(0,R,38)];[Some(1,R,34);Some(0,R,21)];[None;Some(1,R,21)];[None;Some(1,L,43)];[None;Some(1,L,94)];[None;Some(1,L,25)];[None;Some(1,R,34)];[None;Some(1,L,59)];[None;Some(1,R,34)];[None;Some(1,L,8)];[None;Some(0,L,9)];[None;Some(0,L,11)];[None;Some(0,L,13)];[None;Some(0,L,15)];[None;Some(1,L,9)];[None;Some(1,L,11)];[None;Some(1,L,13)];[None;Some(1,L,15)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,38);Some(1,R,53)];[None;Some(0,L,43)];[Some(0,R,21);Some(0,L,94)];[Some(0,R,21);Some(0,L,25)];[Some(1,R,38);Some(1,R,34)];[Some(1,L,13);Some(0,L,59)];[Some(1,R,21);Some(1,R,34)];[Some(1,R,21);Some(0,L,8)];[Some(0,L,25);Some(0,L,8)];[Some(0,L,27);Some(0,L,10)];[Some(0,L,29);Some(0,L,12)];[Some(0,L,31);Some(0,L,14)];[Some(1,L,25);Some(1,L,8)];[Some(1,L,27);Some(1,L,10)];[Some(1,L,29);Some(1,L,12)];[Some(1,L,31);Some(1,L,14)];[Some(0,R,67);None];[Some(0,R,34);Some(0,R,34)];[Some(0,R,71);Some(1,L,27)];[Some(0,R,38);Some(0,R,38)];[Some(1,R,67);None];[Some(1,R,34);Some(1,R,34)];[Some(1,R,71);Some(1,L,10)];[Some(1,R,38);Some(1,R,38)];[Some(0,L,41);Some(0,L,57)];[Some(0,L,43);Some(0,L,59)];[Some(0,L,45);Some(0,L,61)];[Some(0,L,47);Some(0,L,63)];[Some(1,L,41);Some(1,L,57)];[Some(1,L,43);Some(1,L,59)];[Some(1,L,45);Some(1,L,61)];[Some(1,L,47);Some(1,L,63)];[Some(0,R,49);Some(0,R,17)];[Some(0,R,51);Some(0,R,19)];[Some(0,R,53);Some(0,R,21)];[Some(0,R,55);Some(0,R,23)];[Some(1,R,49);Some(1,R,17)];[Some(1,R,51);Some(1,R,19)];[Some(1,R,53);Some(1,R,21)];[Some(1,R,55);Some(1,R,23)];[Some(0,L,9);Some(0,L,63)];[Some(1,R,71);Some(0,L,63)];[Some(0,L,13);Some(1,R,34)];[Some(1,R,53);Some(1,R,34)];[Some(1,L,9);Some(1,R,67)];[Some(1,R,38);Some(1,R,67)];[Some(1,L,13);Some(1,R,34)];[Some(1,R,21);Some(1,R,34)];[None;Some(0,R,65)];[Some(0,L,47);Some(0,R,67)];[None;Some(0,R,69)];[Some(0,L,29);Some(0,R,71)];[None;Some(1,R,65)];[Some(0,L,63);Some(1,R,67)];[None;Some(1,R,69)];[Some(0,L,12);Some(1,R,71)];[Some(0,L,88);Some(1,R,71)];[Some(0,L,90);Some(0,L,63)];[Some(0,L,92);Some(1,R,53)];[Some(0,L,94);Some(1,R,34)];[Some(1,L,88);Some(1,R,38)];[Some(1,L,90);Some(1,R,67)];[Some(1,L,92);Some(1,R,21)];[Some(1,L,94);Some(1,R,34)];[Some(0,R,65);Some(0,R,32)];[Some(0,R,67);Some(0,R,34)];[Some(0,R,69);Some(0,R,36)];[Some(0,R,71);Some(0,R,38)];[Some(1,R,65);Some(1,R,32)];[Some(1,R,67);Some(1,R,34)];[Some(1,R,69);Some(1,R,36)];[Some(1,R,71);Some(1,R,38)];[Some(1,R,71);Some(0,L,27)];[Some(0,L,63);Some(0,R,53)];[Some(1,R,53);Some(0,R,71)];[Some(1,R,34);Some(0,R,53)];[Some(1,R,38);Some(1,L,27)];[Some(1,R,67);Some(0,R,21)];[Some(1,R,21);Some(0,R,38)];[Some(1,R,34);Some(0,R,21)];[None;Some(1,R,21)];[None;Some(1,L,43)];[None;Some(1,L,94)];[None;Some(1,L,25)];[None;Some(1,R,34)];[None;Some(1,L,59)];[None;Some(1,R,34)];[None;Some(1,L,8)];[None;Some(0,L,9)];[None;Some(0,L,11)];[None;Some(0,L,13)];[None;Some(0,L,15)];[None;Some(1,L,9)];[None;Some(1,L,11)];[None;Some(1,L,13)];[None;Some(1,L,15)]]%N.
Definition tm1 := TM'_from_str "0LB1RN_1LC1RJ_---1LD_1LQ1LE_0LL0LF_1LH1LG_0LH0LG_0LK0LI_0LC1RJ_0RA0RM_1RA---_1LK1LI_1RJ1RJ_0RO0RP_---1RP_1RA1RM_0LR0LB_1RM---".
Definition tm2 := TM'_from_str "0LB1RN_1LC1RJ_1RS1LD_1LQ1LE_0LL0LF_1LH1LG_0LH0LG_0LK0LI_0LC1RJ_0RA0RM_1RA---_1LK1LI_1RJ1RJ_0RO0RP_---1RP_1RA1RM_0LR0LB_1RM---_1RS1RS".
Definition l0 := [1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [53;63;94;13;10;12;8;25;59;34;43;29;21;67;23;38;27;47]%N.
Definition mp' := mp_from_list [53;63;94;13;10;12;8;25;59;34;43;29;21;67;71;38;27;47]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 17%N l0 (NG 0 1000 1000 1 1 0 0 true) 85 85.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM26.


Module TM27.
Definition tm := TM_from_str "1LB1LE_1RC1RB_1RE0RD_1LA1RC_0LF1LA_---1LA".
Definition tm' := TM_from_str "1LB1LE_1RC1RB_1RE0RD_1RE1RC_0LF1LA_---1LA".
Definition tm0 := TM'_from_list [[Some(0,R,50);None];[Some(0,R,19);Some(1,R,50)];[Some(0,R,54);Some(1,L,27)];[Some(0,R,23);Some(1,L,94)];[Some(1,R,50);None];[Some(1,R,19);Some(1,R,23)];[Some(1,R,54);Some(1,L,75)];[Some(1,R,23);Some(1,L,15)];[Some(0,L,25);Some(0,L,73)];[Some(0,L,27);Some(0,L,75)];[Some(0,L,29);Some(0,L,77)];[Some(0,L,31);Some(0,L,79)];[Some(1,L,25);Some(1,L,73)];[Some(1,L,27);Some(1,L,75)];[Some(1,L,29);Some(1,L,77)];[Some(1,L,31);Some(1,L,79)];[Some(0,R,33);Some(0,R,17)];[Some(0,R,35);Some(0,R,19)];[Some(0,R,37);Some(0,R,21)];[Some(0,R,39);Some(0,R,23)];[Some(1,R,33);Some(1,R,17)];[Some(1,R,35);Some(1,R,19)];[Some(1,R,37);Some(1,R,21)];[Some(1,R,39);Some(1,R,23)];[Some(0,L,75);Some(0,L,15)];[Some(1,R,39);Some(1,R,71)];[Some(0,L,15);Some(1,R,23)];[Some(1,R,67);Some(1,R,39)];[Some(1,L,75);Some(1,L,79)];[Some(1,R,23);Some(1,R,54)];[Some(1,L,15);Some(1,R,37)];[Some(1,R,50);Some(1,R,23)];[Some(0,R,65);Some(0,R,48)];[Some(0,R,67);Some(0,R,50)];[Some(0,R,69);Some(0,R,52)];[Some(0,R,71);Some(0,R,54)];[Some(1,R,65);Some(1,R,48)];[Some(1,R,67);Some(1,R,50)];[Some(1,R,69);Some(1,R,52)];[Some(1,R,71);Some(1,R,54)];[Some(0,L,9);Some(0,L,27)];[Some(0,L,75);Some(0,L,94)];[Some(0,L,13);Some(0,L,31)];[Some(0,L,79);Some(0,R,23)];[Some(1,L,9);Some(1,L,27)];[Some(1,L,75);Some(1,L,31)];[Some(1,L,13);Some(1,L,31)];[Some(1,L,79);Some(0,R,37)];[Some(0,R,37);Some(0,R,33)];[None;Some(0,R,35)];[Some(0,R,23);Some(0,R,37)];[Some(1,L,31);Some(0,R,39)];[Some(1,R,37);Some(1,R,33)];[Some(1,L,13);Some(1,R,35)];[Some(1,R,23);Some(1,R,37)];[Some(1,L,79);Some(1,R,39)];[Some(0,L,9);Some(0,L,75)];[Some(0,L,11);Some(1,R,39)];[Some(0,L,13);Some(0,L,15)];[Some(0,L,15);Some(1,R,67)];[Some(1,L,9);Some(1,L,75)];[Some(1,L,11);Some(1,R,23)];[Some(1,L,13);Some(1,L,15)];[Some(1,L,15);Some(1,R,50)];[None;Some(0,R,37)];[Some(1,R,67);None];[None;Some(0,R,23)];[Some(0,L,94);Some(1,L,31)];[None;Some(1,R,37)];[Some(1,R,39);Some(1,L,13)];[None;Some(1,R,23)];[Some(0,L,15);Some(1,L,79)];[Some(0,L,88);Some(0,L,9)];[Some(0,L,90);Some(0,L,11)];[Some(0,L,92);Some(0,L,13)];[Some(0,L,94);Some(0,L,15)];[Some(1,L,88);Some(1,L,9)];[Some(1,L,90);Some(1,L,11)];[Some(1,L,92);Some(1,L,13)];[Some(1,L,94);Some(1,L,15)];[None;Some(0,R,37)];[None;None];[None;Some(0,R,23)];[None;Some(1,L,31)];[None;Some(1,R,37)];[None;Some(1,L,13)];[None;Some(1,R,23)];[None;Some(1,L,79)];[None;Some(0,L,9)];[None;Some(0,L,11)];[None;Some(0,L,13)];[None;Some(0,L,15)];[None;Some(1,L,9)];[None;Some(1,L,11)];[None;Some(1,L,13)];[None;Some(1,L,15)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,50);None];[Some(0,R,19);Some(1,R,50)];[Some(0,R,54);Some(1,L,27)];[Some(0,R,23);Some(1,L,94)];[Some(1,R,50);None];[Some(1,R,19);Some(1,R,23)];[Some(1,R,54);Some(1,L,75)];[Some(1,R,23);Some(1,L,15)];[Some(0,L,25);Some(0,L,73)];[Some(0,L,27);Some(0,L,75)];[Some(0,L,29);Some(0,L,77)];[Some(0,L,31);Some(0,L,79)];[Some(1,L,25);Some(1,L,73)];[Some(1,L,27);Some(1,L,75)];[Some(1,L,29);Some(1,L,77)];[Some(1,L,31);Some(1,L,79)];[Some(0,R,33);Some(0,R,17)];[Some(0,R,35);Some(0,R,19)];[Some(0,R,37);Some(0,R,21)];[Some(0,R,39);Some(0,R,23)];[Some(1,R,33);Some(1,R,17)];[Some(1,R,35);Some(1,R,19)];[Some(1,R,37);Some(1,R,21)];[Some(1,R,39);Some(1,R,23)];[Some(0,L,75);Some(0,L,15)];[Some(1,R,39);Some(1,R,71)];[Some(0,L,15);Some(1,R,69)];[Some(1,R,67);Some(1,R,39)];[Some(1,L,75);Some(1,L,79)];[Some(1,L,13);Some(1,R,54)];[Some(1,L,15);Some(1,R,37)];[Some(1,R,50);Some(1,R,23)];[Some(0,R,65);Some(0,R,48)];[Some(0,R,67);Some(0,R,50)];[Some(0,R,69);Some(0,R,52)];[Some(0,R,71);Some(0,R,54)];[Some(1,R,65);Some(1,R,48)];[Some(1,R,67);Some(1,R,50)];[Some(1,R,69);Some(1,R,52)];[Some(1,R,71);Some(1,R,54)];[Some(0,L,9);Some(0,L,27)];[Some(0,L,75);Some(0,L,94)];[Some(0,L,13);Some(0,L,94)];[Some(0,L,79);Some(0,R,69)];[Some(1,L,9);Some(1,L,27)];[Some(1,L,75);Some(1,L,31)];[Some(1,L,13);Some(1,L,94)];[Some(1,L,79);Some(0,R,37)];[Some(0,R,65);Some(0,R,33)];[Some(0,R,67);Some(0,R,35)];[Some(0,R,69);Some(0,R,37)];[Some(0,R,71);Some(0,R,39)];[Some(1,R,65);Some(1,R,33)];[Some(1,R,67);Some(1,R,35)];[Some(1,R,69);Some(1,R,37)];[Some(1,R,71);Some(1,R,39)];[Some(0,L,9);Some(0,L,75)];[Some(0,L,75);Some(1,R,39)];[Some(0,L,13);Some(0,L,15)];[Some(0,L,79);Some(1,R,67)];[Some(1,L,9);Some(1,L,75)];[Some(1,L,75);Some(1,L,13)];[Some(1,L,13);Some(1,L,15)];[Some(1,L,79);Some(1,R,50)];[None;Some(0,R,37)];[Some(1,R,67);None];[None;Some(0,R,23)];[Some(0,L,94);Some(1,L,31)];[None;Some(1,R,37)];[Some(1,R,39);Some(1,L,13)];[None;Some(1,R,23)];[Some(0,L,15);Some(1,L,79)];[Some(0,L,88);Some(0,L,9)];[Some(0,L,90);Some(0,L,11)];[Some(0,L,92);Some(0,L,13)];[Some(0,L,94);Some(0,L,15)];[Some(1,L,88);Some(1,L,9)];[Some(1,L,90);Some(1,L,11)];[Some(1,L,92);Some(1,L,13)];[Some(1,L,94);Some(1,L,15)];[None;Some(0,R,37)];[None;None];[None;Some(0,R,23)];[None;Some(1,L,31)];[None;Some(1,R,37)];[None;Some(1,L,13)];[None;Some(1,R,23)];[None;Some(1,L,79)];[None;Some(0,L,9)];[None;Some(0,L,11)];[None;Some(0,L,13)];[None;Some(0,L,15)];[None;Some(1,L,9)];[None;Some(1,L,11)];[None;Some(1,L,13)];[None;Some(1,L,15)]]%N.
Definition tm1 := TM'_from_str "1RB1RJ_0LC---_1LH1LD_1LE1LC_---1LF_1LN1LG_0LE0LC_1RL1RI_1RA1RI_---1RK_1RM1RL_---0RK_0LE1LH_1RM1RA".
Definition tm2 := TM'_from_str "1RB1RJ_0LC---_1LH1LD_1LE1LC_1RO1LF_1LN1LG_0LE0LC_1RL1RI_1RA1RI_---1RK_1RM1RL_---0RK_0LE1LH_1RM1RA_1RO1RO".
Definition l0 := [1;0;1;0;1;1;1;1;1;1;1;0;1;1;1;1]%N.
Definition mp := mp_from_list [39;71;15;79;94;13;75;31;23;54;37;50;67;27]%N.
Definition mp' := mp_from_list [39;71;15;79;94;13;75;31;23;54;37;50;67;27]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 true) 110 110.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM27.


Module TM28.
Definition tm := TM_from_str "1RB0RF_1LC1LB_1LD1RC_1RE0LB_---0RA_1RC0RD".
Definition tm' := TM_from_str "1RB0RB_1RC0RD_1LD1RC_1RF0LE_1LC1LE_---0RA".
Definition tm0 := TM'_from_list [[Some(0,R,17);Some(0,R,80)];[Some(0,R,19);Some(0,R,82)];[Some(0,R,21);Some(0,R,84)];[Some(0,R,23);Some(0,R,86)];[Some(1,R,17);Some(1,R,80)];[Some(1,R,19);Some(1,R,82)];[Some(1,R,21);Some(1,R,84)];[Some(1,R,23);Some(1,R,86)];[Some(0,L,29);Some(0,L,45)];[Some(0,L,27);None];[Some(1,L,27);Some(1,L,43)];[Some(0,L,31);Some(0,L,59)];[Some(1,L,29);Some(1,L,45)];[Some(1,L,27);Some(0,R,2)];[Some(1,R,39);Some(0,R,39)];[Some(1,L,31);Some(1,L,59)];[Some(0,R,84);Some(1,R,48)];[Some(0,R,35);Some(1,L,63)];[Some(1,L,45);Some(0,R,39)];[Some(0,R,39);Some(1,L,47)];[Some(1,R,84);Some(1,L,30)];[Some(1,R,35);Some(1,R,39)];[Some(1,L,29);Some(1,R,39)];[Some(1,R,39);Some(1,L,31)];[Some(0,L,41);Some(0,L,25)];[Some(0,L,43);Some(0,L,27)];[Some(0,L,45);Some(0,L,29)];[Some(0,L,47);Some(0,L,31)];[Some(1,L,41);Some(1,L,25)];[Some(1,L,43);Some(1,L,27)];[Some(1,L,45);Some(1,L,29)];[Some(1,L,47);Some(1,L,31)];[Some(0,R,2);Some(0,R,33)];[Some(1,L,59);Some(0,R,35)];[Some(0,R,6);Some(0,R,37)];[Some(1,L,43);Some(0,R,39)];[Some(1,R,2);Some(1,R,33)];[Some(1,L,29);Some(1,R,35)];[Some(1,R,6);Some(1,R,37)];[Some(1,L,27);Some(1,R,39)];[Some(0,L,57);Some(0,L,26)];[Some(0,L,59);Some(0,L,29)];[Some(0,L,61);Some(0,L,30)];[Some(0,L,63);Some(1,L,27)];[Some(1,L,57);Some(1,L,26)];[Some(1,L,59);Some(1,L,29)];[Some(1,L,61);Some(1,L,30)];[Some(1,L,63);Some(1,R,39)];[Some(0,R,65);Some(1,R,33)];[Some(0,R,67);Some(0,L,63)];[Some(0,R,69);Some(1,L,43)];[Some(0,R,71);Some(0,L,47)];[Some(1,R,65);Some(0,L,30)];[Some(1,R,67);Some(1,L,27)];[Some(1,R,69);Some(1,L,27)];[Some(1,R,71);Some(0,L,31)];[None;Some(0,L,24)];[Some(1,R,35);Some(0,L,26)];[None;Some(0,L,28)];[Some(1,R,33);Some(0,L,30)];[None;Some(1,L,24)];[Some(1,R,39);Some(1,L,26)];[None;Some(1,L,28)];[Some(1,R,48);Some(1,L,30)];[None;Some(0,R,0)];[None;Some(0,R,2)];[None;Some(0,R,4)];[None;Some(0,R,6)];[None;Some(1,R,0)];[None;Some(1,R,2)];[None;Some(1,R,4)];[None;Some(1,R,6)];[None;Some(1,L,43)];[None;Some(1,L,59)];[None;Some(0,L,47)];[None;Some(0,R,65)];[None;Some(0,R,39)];[None;Some(0,R,35)];[None;Some(1,L,47)];[None;Some(1,R,33)];[Some(0,R,33);Some(0,R,48)];[Some(0,R,35);Some(0,R,50)];[Some(0,R,37);Some(0,R,52)];[Some(0,R,39);Some(0,R,54)];[Some(1,R,33);Some(1,R,48)];[Some(1,R,35);Some(1,R,50)];[Some(1,R,37);Some(1,R,52)];[Some(1,R,39);Some(1,R,54)];[Some(0,L,26);None];[Some(0,L,29);Some(0,L,41)];[Some(0,L,30);Some(0,R,21)];[Some(1,L,27);Some(0,L,45)];[Some(1,L,26);None];[Some(1,L,29);Some(1,L,41)];[Some(1,L,30);Some(0,R,84)];[Some(1,R,39);Some(1,L,45)]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,17);Some(0,R,16)];[Some(0,R,19);Some(0,R,18)];[Some(0,R,21);Some(0,R,20)];[Some(0,R,23);Some(0,R,22)];[Some(1,R,17);Some(1,R,16)];[Some(1,R,19);Some(1,R,18)];[Some(1,R,21);Some(1,R,20)];[Some(1,R,23);Some(1,R,22)];[Some(0,L,77);Some(0,L,45)];[None;None];[Some(1,L,75);Some(1,L,43)];[Some(0,L,77);Some(0,L,59)];[Some(1,L,77);Some(1,L,45)];[Some(1,R,2);Some(0,R,2)];[Some(1,R,39);Some(0,R,39)];[Some(1,L,77);Some(1,L,59)];[Some(0,R,33);Some(0,R,48)];[Some(0,R,35);Some(0,R,50)];[Some(0,R,37);Some(0,R,52)];[Some(0,R,39);Some(0,R,54)];[Some(1,R,33);Some(1,R,48)];[Some(1,R,35);Some(1,R,50)];[Some(1,R,37);Some(1,R,52)];[Some(1,R,39);Some(1,R,54)];[Some(0,L,74);None];[Some(0,L,77);Some(0,L,41)];[Some(0,L,78);Some(0,R,21)];[Some(1,L,75);Some(0,L,45)];[Some(1,L,74);None];[Some(1,L,77);Some(1,L,41)];[Some(1,L,78);Some(0,R,20)];[Some(1,R,39);Some(1,L,45)];[Some(0,R,2);Some(0,R,33)];[Some(1,L,59);Some(0,R,35)];[Some(0,R,6);Some(0,R,37)];[Some(1,L,43);Some(0,R,39)];[Some(1,R,2);Some(1,R,33)];[Some(1,L,77);Some(1,R,35)];[Some(1,R,6);Some(1,R,37)];[Some(1,L,75);Some(1,R,39)];[Some(0,L,57);Some(0,L,74)];[Some(0,L,59);Some(0,L,77)];[Some(0,L,61);Some(0,L,78)];[Some(0,L,63);Some(1,L,75)];[Some(1,L,57);Some(1,L,74)];[Some(1,L,59);Some(1,L,77)];[Some(1,L,61);Some(1,L,78)];[Some(1,L,63);Some(1,R,39)];[Some(0,R,81);Some(1,R,33)];[Some(0,R,83);Some(0,L,63)];[Some(0,R,85);Some(1,L,43)];[Some(0,R,87);Some(0,L,47)];[Some(1,R,81);Some(0,L,78)];[Some(1,R,83);Some(1,L,75)];[Some(1,R,85);Some(1,L,75)];[Some(1,R,87);Some(0,L,79)];[None;Some(0,L,72)];[Some(1,R,35);Some(0,L,74)];[None;Some(0,L,76)];[Some(1,R,33);Some(0,L,78)];[None;Some(1,L,72)];[Some(1,R,50);Some(1,L,74)];[None;Some(1,L,76)];[Some(1,R,48);Some(1,L,78)];[Some(0,R,20);Some(1,R,48)];[Some(0,R,35);Some(1,L,63)];[Some(1,L,45);Some(0,R,39)];[Some(0,R,39);Some(1,L,47)];[Some(1,R,20);Some(1,L,78)];[Some(1,R,35);Some(1,R,39)];[Some(1,L,77);Some(1,R,39)];[Some(1,R,39);Some(1,L,79)];[Some(0,L,41);Some(0,L,73)];[Some(0,L,43);Some(0,L,75)];[Some(0,L,45);Some(0,L,77)];[Some(0,L,47);Some(0,L,79)];[Some(1,L,41);Some(1,L,73)];[Some(1,L,43);Some(1,L,75)];[Some(1,L,45);Some(1,L,77)];[Some(1,L,47);Some(1,L,79)];[None;Some(0,R,0)];[None;Some(0,R,2)];[None;Some(0,R,4)];[None;Some(0,R,6)];[None;Some(1,R,0)];[None;Some(1,R,2)];[None;Some(1,R,4)];[None;Some(1,R,6)];[None;Some(1,L,43)];[None;Some(1,L,59)];[None;Some(0,R,85)];[None;Some(0,R,81)];[None;Some(0,R,39)];[None;Some(0,R,35)];[None;Some(1,L,43)];[None;Some(1,R,33)]]%N.
Definition tm1 := TM'_from_str "1RB1RM_1LC0RF_1RB0LD_1LE1LK_1LC1LK_1LL0RG_1LH1RG_0LI0LP_1LJ1RG_1RM1LD_1LL1LH_0LJ1LH_0RN1RB_---0RO_0RQ0RA_1LI1LP_1RF---".
Definition tm2 := TM'_from_str "1RB1RM_1LC0RF_1RB0LD_1LE1LK_1LC1LK_1LL0RG_1LH1RG_0LI0LP_1LJ1RG_1RM1LD_1LL1LH_0LJ1LH_0RN1RB_1RR0RO_0RQ0RA_1LI1LP_1RF---_1RR1RR".
Definition l0 := [1;1;1;0;0;0;1;1;1;0;0;0;1;0;0;0]%N.
Definition mp := mp_from_list [84;33;59;30;45;35;39;27;47;63;29;43;48;65;2;31;21]%N.
Definition mp' := mp_from_list [20;33;59;78;45;35;39;75;47;63;77;43;48;81;2;79;21]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 16%N l0 (NG 0 1000 1000 1 1 0 0 true) 131 131.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM28.


Ltac solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' qn l0 cert T T' ::=
  solve_v1 tm tm0 4;
  solve_v1 tm' tm0' 4;
  solve_v2 tm0 tm1 tm2 mp qn (const 0<*(rev l0),0,const 0)%N l0 cert T;
  solve_v2 tm0' tm1 tm2 mp' qn (const 0<*(rev l0),0,const 0)%N l0 cert T'.

Module TM29.
Definition tm := TM_from_str "1RB---_0LC1RF_0LD1LC_1RE1LB_1RD0RB_0RB0RA".
Definition tm' := TM_from_str "1RB---_0LC1RF_0LD1LC_1RE1LB_1RD0LD_0RB0RA".
Definition tm0 := TM'_from_list [[Some(0,R,33);None];[Some(0,R,35);None];[Some(0,R,37);None];[Some(0,R,39);None];[Some(0,R,41);None];[Some(0,R,43);None];[Some(0,R,45);None];[Some(0,R,47);None];[Some(1,R,33);None];[Some(1,R,35);None];[Some(1,R,37);None];[Some(1,R,39);None];[Some(1,R,41);None];[Some(1,R,43);None];[Some(1,R,45);None];[Some(1,R,47);None];[Some(0,L,81);None];[Some(0,L,53);None];[Some(0,L,85);None];[Some(1,R,38);None];[Some(0,L,89);None];[Some(1,R,42);None];[Some(0,L,93);None];[None;None];[Some(1,L,81);None];[Some(1,L,53);None];[Some(1,L,85);None];[Some(1,R,171);None];[Some(1,L,89);None];[Some(1,R,10);None];[Some(1,L,93);None];[None;None];[Some(0,R,135);Some(0,R,161)];[Some(0,R,45);Some(0,R,163)];[Some(0,L,116);Some(0,R,165)];[None;Some(0,R,167)];[Some(0,R,143);Some(0,R,169)];[Some(0,L,90);Some(0,R,171)];[Some(0,L,90);Some(0,R,173)];[Some(0,L,126);Some(0,R,175)];[Some(1,R,135);Some(1,R,161)];[Some(1,R,45);Some(1,R,163)];[Some(0,L,85);Some(1,R,165)];[Some(0,L,61);Some(1,R,167)];[Some(1,R,143);Some(1,R,169)];[Some(1,R,38);Some(1,R,171)];[Some(1,R,38);Some(1,R,173)];[Some(0,L,95);Some(1,R,175)];[Some(0,L,80);Some(0,L,49)];[Some(0,L,82);Some(0,L,53)];[Some(0,L,84);Some(0,L,85)];[Some(0,L,86);None];[Some(0,L,88);Some(0,L,57)];[Some(0,L,90);Some(1,R,38)];[Some(0,L,92);Some(1,R,37)];[Some(0,L,94);None];[Some(1,L,80);Some(1,L,49)];[Some(1,L,82);Some(1,L,53)];[Some(1,L,84);Some(1,R,165)];[Some(1,L,86);None];[Some(1,L,88);Some(1,L,57)];[Some(1,L,90);Some(1,R,6)];[Some(1,L,92);None];[Some(1,L,94);None];[Some(0,R,99);Some(0,R,6)];[Some(1,R,38);None];[Some(0,R,103);Some(1,L,116)];[Some(0,R,37);None];[Some(0,R,107);Some(0,R,14)];[Some(0,L,122);Some(1,L,90)];[Some(0,R,111);Some(0,R,171)];[Some(0,R,45);Some(1,L,126)];[Some(1,R,99);Some(1,R,6)];[Some(0,L,57);None];[Some(1,R,103);Some(1,L,85)];[Some(1,R,37);Some(1,L,61)];[Some(1,R,107);Some(1,R,14)];[Some(0,L,91);Some(1,R,6)];[Some(1,R,111);Some(1,R,171)];[Some(1,R,45);Some(1,L,95)];[Some(0,L,112);Some(0,L,81)];[Some(0,L,114);Some(0,L,83)];[Some(0,L,116);Some(0,L,85)];[Some(0,L,118);Some(0,L,87)];[Some(0,L,120);Some(0,L,89)];[Some(0,L,122);Some(0,L,91)];[Some(0,L,124);Some(0,L,93)];[Some(0,L,126);Some(0,L,95)];[Some(1,L,112);Some(1,L,81)];[Some(1,L,114);Some(1,L,83)];[Some(1,L,116);Some(1,L,85)];[Some(1,L,118);Some(1,L,87)];[Some(1,L,120);Some(1,L,89)];[Some(1,L,122);Some(1,L,91)];[Some(1,L,124);Some(1,L,93)];[Some(1,L,126);Some(1,L,95)];[Some(0,R,129);Some(0,R,46)];[Some(0,R,131);Some(0,R,2)];[Some(0,R,133);Some(1,R,171)];[Some(0,R,135);Some(0,R,6)];[Some(0,R,137);Some(1,L,82)];[Some(0,R,139);Some(0,R,10)];[Some(0,R,141);Some(1,L,118)];[Some(0,R,143);Some(0,R,14)];[Some(1,R,129);Some(1,R,46)];[Some(1,R,131);Some(1,R,2)];[Some(1,R,133);Some(1,L,53)];[Some(1,R,135);Some(1,R,6)];[Some(1,R,137);Some(1,L,53)];[Some(1,R,139);Some(1,R,10)];[Some(1,R,141);Some(1,L,87)];[Some(1,R,143);Some(1,R,14)];[Some(1,R,143);Some(0,L,49)];[Some(0,L,49);Some(0,L,51)];[Some(1,R,38);Some(0,L,53)];[Some(0,L,85);Some(0,L,55)];[Some(1,R,38);Some(0,L,57)];[Some(0,L,57);Some(0,L,59)];[None;Some(0,L,61)];[Some(1,R,37);Some(0,L,63)];[Some(1,R,14);Some(1,L,49)];[Some(1,L,49);Some(1,L,51)];[Some(1,R,171);Some(1,L,53)];[Some(1,R,165);Some(1,L,55)];[Some(1,R,173);Some(1,L,57)];[Some(1,L,57);Some(1,L,59)];[None;Some(1,L,61)];[None;Some(1,L,63)];[Some(0,R,97);Some(0,R,32)];[Some(0,R,99);Some(0,R,34)];[Some(0,R,101);Some(0,R,36)];[Some(0,R,103);Some(0,R,38)];[Some(0,R,105);Some(0,R,40)];[Some(0,R,107);Some(0,R,42)];[Some(0,R,109);Some(0,R,44)];[Some(0,R,111);Some(0,R,46)];[Some(1,R,97);Some(1,R,32)];[Some(1,R,99);Some(1,R,34)];[Some(1,R,101);Some(1,R,36)];[Some(1,R,103);Some(1,R,38)];[Some(1,R,105);Some(1,R,40)];[Some(1,R,107);Some(1,R,42)];[Some(1,R,109);Some(1,R,44)];[Some(1,R,111);Some(1,R,46)];[Some(1,R,111);Some(0,L,112)];[Some(0,L,53);Some(0,L,82)];[Some(0,L,53);Some(0,L,116)];[None;Some(0,L,90)];[Some(1,R,45);Some(0,L,120)];[Some(1,R,38);Some(0,R,42)];[Some(1,R,42);Some(0,L,124)];[None;None];[Some(1,R,46);Some(1,L,112)];[Some(1,L,53);Some(1,L,82)];[Some(1,L,53);Some(1,L,116)];[None;Some(0,R,171)];[None;Some(1,L,120)];[Some(1,R,6);Some(0,R,10)];[Some(1,R,10);Some(1,L,124)];[None;None];[Some(0,R,32);Some(0,R,0)];[Some(0,R,34);Some(0,R,2)];[Some(0,R,36);Some(0,R,4)];[Some(0,R,38);Some(0,R,6)];[Some(0,R,40);Some(0,R,8)];[Some(0,R,42);Some(0,R,10)];[Some(0,R,44);Some(0,R,12)];[Some(0,R,46);Some(0,R,14)];[Some(1,R,32);Some(1,R,0)];[Some(1,R,34);Some(1,R,2)];[Some(1,R,36);Some(1,R,4)];[Some(1,R,38);Some(1,R,6)];[Some(1,R,40);Some(1,R,8)];[Some(1,R,42);Some(1,R,10)];[Some(1,R,44);Some(1,R,12)];[Some(1,R,46);Some(1,R,14)];[Some(0,L,112);Some(0,L,114)];[Some(0,L,82);None];[Some(0,L,116);Some(0,L,90)];[Some(0,L,90);None];[Some(0,L,120);Some(0,L,122)];[Some(0,R,42);None];[Some(0,L,124);Some(0,R,45)];[None;None];[Some(1,L,112);Some(1,L,114)];[Some(1,L,82);None];[Some(1,L,116);Some(0,R,173)];[Some(0,R,171);None];[Some(1,L,120);Some(1,L,122)];[Some(0,R,10);None];[Some(1,L,124);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,33);None];[Some(0,R,35);None];[Some(0,R,37);None];[Some(0,R,39);None];[Some(0,R,41);None];[Some(0,R,43);None];[Some(0,R,45);None];[Some(0,R,47);None];[Some(1,R,33);None];[Some(1,R,35);None];[Some(1,R,37);None];[Some(1,R,39);None];[Some(1,R,41);None];[Some(1,R,43);None];[Some(1,R,45);None];[Some(1,R,47);None];[Some(0,L,81);None];[Some(0,L,53);None];[Some(0,L,85);None];[Some(1,R,38);None];[Some(0,L,89);None];[Some(1,R,42);None];[Some(0,L,93);None];[None;None];[Some(1,L,81);None];[Some(1,L,53);None];[Some(1,L,85);None];[Some(1,R,171);None];[Some(1,L,89);None];[Some(1,R,10);None];[Some(1,L,93);None];[None;None];[Some(0,R,135);Some(0,R,161)];[Some(0,R,45);Some(0,R,163)];[Some(0,L,116);Some(0,R,165)];[None;Some(0,R,167)];[Some(0,R,143);Some(0,R,169)];[Some(0,L,90);Some(0,R,171)];[Some(0,L,90);Some(0,R,173)];[Some(0,L,126);Some(0,R,175)];[Some(1,R,135);Some(1,R,161)];[Some(1,R,45);Some(1,R,163)];[Some(0,L,85);Some(1,R,165)];[Some(0,L,61);Some(1,R,167)];[Some(1,R,143);Some(1,R,169)];[Some(1,R,38);Some(1,R,171)];[Some(1,R,38);Some(1,R,173)];[Some(0,L,95);Some(1,R,175)];[Some(0,L,80);Some(0,L,49)];[Some(0,L,82);Some(0,L,53)];[Some(0,L,84);Some(0,L,85)];[Some(0,L,86);None];[Some(0,L,88);Some(0,L,57)];[Some(0,L,90);Some(1,R,38)];[Some(0,L,92);Some(1,R,37)];[Some(0,L,94);None];[Some(1,L,80);Some(1,L,49)];[Some(1,L,82);Some(1,L,53)];[Some(1,L,84);Some(1,R,165)];[Some(1,L,86);None];[Some(1,L,88);Some(1,L,57)];[Some(1,L,90);Some(1,R,6)];[Some(1,L,92);None];[Some(1,L,94);None];[Some(0,R,99);Some(0,R,6)];[Some(1,R,38);None];[Some(0,R,103);Some(1,L,116)];[Some(0,R,37);None];[Some(0,R,107);Some(0,R,14)];[Some(0,L,122);Some(1,L,90)];[Some(0,R,111);Some(0,R,171)];[Some(0,R,45);Some(1,L,126)];[Some(1,R,99);Some(1,R,6)];[Some(0,L,57);None];[Some(1,R,103);Some(1,L,85)];[Some(1,R,37);Some(1,L,61)];[Some(1,R,107);Some(1,R,14)];[Some(0,L,91);Some(1,R,6)];[Some(1,R,111);Some(1,R,171)];[Some(1,R,45);Some(1,L,95)];[Some(0,L,112);Some(0,L,81)];[Some(0,L,114);Some(0,L,83)];[Some(0,L,116);Some(0,L,85)];[Some(0,L,118);Some(0,L,87)];[Some(0,L,120);Some(0,L,89)];[Some(0,L,122);Some(0,L,91)];[Some(0,L,124);Some(0,L,93)];[Some(0,L,126);Some(0,L,95)];[Some(1,L,112);Some(1,L,81)];[Some(1,L,114);Some(1,L,83)];[Some(1,L,116);Some(1,L,85)];[Some(1,L,118);Some(1,L,87)];[Some(1,L,120);Some(1,L,89)];[Some(1,L,122);Some(1,L,91)];[Some(1,L,124);Some(1,L,93)];[Some(1,L,126);Some(1,L,95)];[Some(0,R,129);Some(0,R,45)];[Some(0,R,131);Some(0,R,2)];[Some(0,R,133);Some(1,R,171)];[Some(0,R,135);Some(0,R,6)];[Some(0,R,137);Some(1,L,82)];[Some(0,R,139);Some(0,R,10)];[Some(0,R,141);Some(1,L,118)];[Some(0,R,143);Some(0,R,14)];[Some(1,R,129);Some(1,R,45)];[Some(1,R,131);Some(1,R,2)];[Some(1,R,133);Some(1,L,53)];[Some(1,R,135);Some(1,R,6)];[Some(1,R,137);Some(1,L,53)];[Some(1,R,139);Some(1,R,10)];[Some(1,R,141);Some(1,L,87)];[Some(1,R,143);Some(1,R,14)];[Some(1,R,143);Some(0,L,49)];[Some(0,L,49);Some(0,L,51)];[Some(1,R,38);Some(0,L,53)];[Some(0,L,53);Some(0,L,55)];[Some(1,R,38);Some(0,L,57)];[Some(0,L,57);Some(0,L,59)];[None;Some(0,L,61)];[Some(0,L,61);Some(0,L,63)];[Some(1,R,14);Some(1,L,49)];[Some(1,L,49);Some(1,L,51)];[Some(1,R,171);Some(1,L,53)];[Some(1,L,53);Some(1,L,55)];[Some(1,R,171);Some(1,L,57)];[Some(1,L,57);Some(1,L,59)];[None;Some(1,L,61)];[Some(1,L,61);Some(1,L,63)];[Some(0,R,97);Some(0,R,99)];[Some(0,R,99);Some(1,R,38)];[Some(0,R,101);Some(0,R,103)];[Some(0,R,103);Some(0,R,37)];[Some(0,R,105);Some(0,R,107)];[Some(0,R,107);Some(0,L,122)];[Some(0,R,109);Some(0,R,111)];[Some(0,R,111);Some(0,R,45)];[Some(1,R,97);Some(1,R,99)];[Some(1,R,99);Some(0,L,57)];[Some(1,R,101);Some(1,R,103)];[Some(1,R,103);Some(1,R,37)];[Some(1,R,105);Some(1,R,107)];[Some(1,R,107);Some(0,L,91)];[Some(1,R,109);Some(1,R,111)];[Some(1,R,111);Some(1,R,45)];[Some(1,R,111);Some(0,L,112)];[Some(0,L,53);Some(0,L,114)];[Some(0,L,53);Some(0,L,116)];[None;Some(0,L,118)];[Some(1,R,45);Some(0,L,120)];[Some(1,R,38);Some(0,L,122)];[Some(1,R,38);Some(0,L,124)];[None;Some(0,L,126)];[Some(1,R,45);Some(1,L,112)];[Some(1,L,53);Some(1,L,114)];[Some(1,L,53);Some(1,L,116)];[None;Some(1,L,118)];[None;Some(1,L,120)];[Some(1,R,6);Some(1,L,122)];[Some(1,R,6);Some(1,L,124)];[None;Some(1,L,126)];[Some(0,R,32);Some(0,R,0)];[Some(0,R,34);Some(0,R,2)];[Some(0,R,36);Some(0,R,4)];[Some(0,R,38);Some(0,R,6)];[Some(0,R,40);Some(0,R,8)];[Some(0,R,42);Some(0,R,10)];[Some(0,R,44);Some(0,R,12)];[Some(0,R,46);Some(0,R,14)];[Some(1,R,32);Some(1,R,0)];[Some(1,R,34);Some(1,R,2)];[Some(1,R,36);Some(1,R,4)];[Some(1,R,38);Some(1,R,6)];[Some(1,R,40);Some(1,R,8)];[Some(1,R,42);Some(1,R,10)];[Some(1,R,44);Some(1,R,12)];[Some(1,R,46);Some(1,R,14)];[Some(0,L,112);Some(0,L,114)];[Some(0,L,82);None];[Some(0,L,116);Some(0,L,90)];[Some(0,L,90);None];[Some(0,L,120);Some(0,L,122)];[Some(0,R,42);None];[Some(0,L,124);Some(0,R,45)];[None;None];[Some(1,L,112);Some(1,L,114)];[Some(1,L,82);None];[Some(1,L,116);Some(0,R,173)];[Some(0,R,171);None];[Some(1,L,120);Some(1,L,122)];[Some(0,R,10);None];[Some(1,L,124);None]]%N.
Definition tm1 := TM'_from_str "0LB1RT_0LC0LG_1RL1LD_0LM1RE_0LM0RF_1RA1RR_1LH1LN_---0LI_1LM1RJ_0RK---_---1RL_1RE---_1LQ1LB_0LP0LO_1LP1LO_---1LI_1RE---_1RS---_---0RL_0RA0RR".
Definition tm2 := TM'_from_str "0LB1RT_0LC0LG_1RL1LD_0LM1RE_0LM0RF_1RA1RR_1LH1LN_1RU0LI_1LM1RJ_0RK1RU_---1RL_1RE---_1LQ1LB_0LP0LO_1LP1LO_1RU1LI_1RE---_1RS1RU_---0RL_0RA0RR_1RU1RU".
Definition l0 := [1;0;1;1;0;1;0;1;0;1;1;0;1;0;1;0]%N.
Definition mp := mp_from_list [42;85;122;53;38;173;91;118;61;6;45;171;90;87;95;126;116;10;37;165]%N.
Definition mp' := mp_from_list [42;85;122;53;38;173;91;118;61;6;45;171;90;87;95;126;116;10;37;165]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 19%N l0 (NG 0 1000 1000 1 1 0 0 true) 117 117.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM29.


Module TM30.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1LC---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1LB---".
Definition tm0 := TM'_from_list [[Some(0,R,33);Some(0,R,128)];[Some(0,R,35);Some(0,R,130)];[Some(0,R,37);Some(0,R,132)];[Some(0,R,39);Some(0,R,134)];[Some(0,R,41);Some(0,R,136)];[Some(0,R,43);Some(0,R,138)];[Some(0,R,45);Some(0,R,140)];[Some(0,R,47);Some(0,R,142)];[Some(1,R,33);Some(1,R,128)];[Some(1,R,35);Some(1,R,130)];[Some(1,R,37);Some(1,R,132)];[Some(1,R,39);Some(1,R,134)];[Some(1,R,41);Some(1,R,136)];[Some(1,R,43);Some(1,R,138)];[Some(1,R,45);Some(1,R,140)];[Some(1,R,47);Some(1,R,142)];[Some(0,L,116);Some(0,L,119)];[Some(0,L,120);Some(1,L,127)];[Some(0,L,87);None];[Some(1,L,112);Some(0,R,47)];[Some(0,L,124);Some(0,L,127)];[Some(0,L,95);Some(0,R,79)];[Some(0,L,95);None];[Some(1,R,79);Some(0,R,43)];[Some(1,L,116);Some(1,L,119)];[Some(1,L,120);Some(1,L,127)];[Some(1,L,87);None];[Some(1,L,95);None];[Some(1,L,124);Some(1,L,127)];[Some(1,L,95);Some(0,R,47)];[Some(1,L,95);None];[Some(1,R,47);Some(0,R,138)];[Some(0,R,65);Some(0,R,33)];[Some(0,R,67);Some(0,R,35)];[Some(0,R,69);Some(0,R,37)];[Some(0,R,71);Some(0,R,39)];[Some(0,R,73);Some(0,R,41)];[Some(0,R,75);Some(0,R,43)];[Some(0,R,77);Some(0,R,45)];[Some(0,R,79);Some(0,R,47)];[Some(1,R,65);Some(1,R,33)];[Some(1,R,67);Some(1,R,35)];[Some(1,R,69);Some(1,R,37)];[Some(1,R,71);Some(1,R,39)];[Some(1,R,73);Some(1,R,41)];[Some(1,R,75);Some(1,R,43)];[Some(1,R,77);Some(1,R,45)];[Some(1,R,79);Some(1,R,47)];[Some(0,L,114);Some(0,L,116)];[Some(0,L,83);Some(0,L,120)];[Some(0,L,118);Some(0,L,87)];[Some(0,L,87);Some(1,L,112)];[Some(0,L,122);Some(0,L,124)];[Some(0,L,91);Some(0,L,95)];[Some(0,L,126);Some(0,L,95)];[Some(0,L,95);Some(1,R,79)];[Some(1,L,114);Some(1,L,116)];[Some(1,L,83);Some(1,L,120)];[Some(1,L,118);Some(1,L,87)];[Some(1,L,87);Some(1,L,95)];[Some(1,L,122);Some(1,L,124)];[Some(1,L,91);Some(1,L,95)];[Some(1,L,126);Some(1,L,95)];[Some(1,L,95);Some(1,R,47)];[Some(0,R,128);Some(0,R,1)];[Some(0,R,35);Some(0,R,130)];[Some(0,R,132);Some(0,R,39)];[Some(0,R,5);Some(0,R,5)];[Some(0,R,136);Some(0,R,9)];[Some(0,R,43);Some(0,R,47)];[Some(0,R,140);Some(1,L,127)];[Some(1,L,127);Some(1,L,127)];[Some(1,R,128);Some(1,R,1)];[Some(1,R,35);Some(1,R,130)];[Some(1,R,132);Some(1,R,39)];[Some(1,L,126);Some(1,L,126)];[Some(1,R,136);Some(1,R,9)];[Some(1,R,43);Some(1,L,124)];[Some(1,R,140);Some(1,L,120)];[Some(1,L,112);Some(1,L,95)];[Some(0,L,113);Some(0,L,81)];[Some(0,L,115);Some(0,L,83)];[Some(0,L,117);Some(0,L,85)];[Some(0,L,119);Some(0,L,87)];[Some(0,L,121);Some(0,L,89)];[Some(0,L,123);Some(0,L,91)];[Some(0,L,125);Some(0,L,93)];[Some(0,L,127);Some(0,L,95)];[Some(1,L,113);Some(1,L,81)];[Some(1,L,115);Some(1,L,83)];[Some(1,L,117);Some(1,L,85)];[Some(1,L,119);Some(1,L,87)];[Some(1,L,121);Some(1,L,89)];[Some(1,L,123);Some(1,L,91)];[Some(1,L,125);Some(1,L,93)];[Some(1,L,127);Some(1,L,95)];[Some(0,R,0);Some(0,R,33)];[Some(0,R,2);Some(0,R,67)];[Some(0,R,4);Some(0,R,37)];[Some(0,R,6);Some(0,R,5)];[Some(0,R,8);Some(0,R,41)];[Some(0,R,10);Some(0,R,75)];[Some(0,R,12);Some(0,R,45)];[Some(0,R,14);Some(0,L,127)];[Some(1,R,0);Some(1,R,33)];[Some(1,R,2);Some(1,R,67)];[Some(1,R,4);Some(1,R,37)];[Some(1,R,6);Some(1,L,126)];[Some(1,R,8);Some(1,R,41)];[Some(1,R,10);Some(1,R,75)];[Some(1,R,12);Some(1,R,45)];[Some(1,R,14);Some(0,L,112)];[Some(0,L,127);Some(0,L,112)];[Some(0,R,165);Some(0,L,114)];[Some(1,L,127);Some(0,L,116)];[Some(0,R,71);Some(0,L,118)];[Some(0,L,127);Some(0,L,120)];[None;Some(0,L,122)];[Some(0,R,79);Some(0,L,124)];[Some(0,R,165);Some(0,L,126)];[Some(1,L,127);Some(1,L,112)];[Some(0,R,5);Some(1,L,114)];[Some(1,L,127);Some(1,L,116)];[Some(0,R,39);Some(1,L,118)];[Some(1,L,127);Some(1,L,120)];[None;Some(1,L,122)];[Some(0,R,47);Some(1,L,124)];[Some(0,R,5);Some(1,L,126)];[Some(0,R,161);Some(0,R,1)];[Some(0,R,163);Some(0,R,3)];[Some(0,R,165);Some(0,R,5)];[Some(0,R,167);Some(0,R,7)];[Some(0,R,169);Some(0,R,9)];[Some(0,R,171);Some(0,R,11)];[Some(0,R,173);Some(0,R,13)];[Some(0,R,175);Some(0,R,15)];[Some(1,R,161);Some(1,R,1)];[Some(1,R,163);Some(1,R,3)];[Some(1,R,165);Some(1,R,5)];[Some(1,R,167);Some(1,R,7)];[Some(1,R,169);Some(1,R,9)];[Some(1,R,171);Some(1,R,11)];[Some(1,R,173);Some(1,R,13)];[Some(1,R,175);Some(1,R,15)];[Some(0,L,83);Some(0,L,120)];[None;Some(0,L,126)];[Some(0,L,87);Some(1,L,112)];[None;Some(1,R,71)];[Some(0,L,91);Some(0,L,95)];[None;None];[Some(0,L,95);Some(1,R,79)];[None;Some(1,R,165)];[Some(1,L,83);Some(1,L,120)];[None;Some(1,L,126)];[Some(1,L,87);Some(1,L,95)];[None;Some(1,R,39)];[Some(1,L,91);Some(1,L,95)];[None;None];[Some(1,L,95);Some(1,R,47)];[None;Some(1,R,5)];[Some(0,R,1);None];[Some(0,R,130);None];[Some(0,R,39);None];[Some(0,R,5);None];[Some(0,R,9);None];[Some(0,R,47);None];[Some(1,L,127);None];[Some(1,L,127);None];[Some(1,R,1);None];[Some(1,R,130);None];[Some(1,R,39);None];[Some(1,L,126);None];[Some(1,R,9);None];[Some(1,L,124);None];[Some(1,L,120);None];[Some(1,L,95);None];[Some(0,L,81);None];[Some(0,L,83);None];[Some(0,L,85);None];[Some(0,L,87);None];[Some(0,L,89);None];[Some(0,L,91);None];[Some(0,L,93);None];[Some(0,L,95);None];[Some(1,L,81);None];[Some(1,L,83);None];[Some(1,L,85);None];[Some(1,L,87);None];[Some(1,L,89);None];[Some(1,L,91);None];[Some(1,L,93);None];[Some(1,L,95);None]]%N.
Definition tm0' := TM'_from_list [[Some(0,R,33);Some(0,R,128)];[Some(0,R,35);Some(0,R,130)];[Some(0,R,37);Some(0,R,132)];[Some(0,R,39);Some(0,R,134)];[Some(0,R,41);Some(0,R,136)];[Some(0,R,43);Some(0,R,138)];[Some(0,R,45);Some(0,R,140)];[Some(0,R,47);Some(0,R,142)];[Some(1,R,33);Some(1,R,128)];[Some(1,R,35);Some(1,R,130)];[Some(1,R,37);Some(1,R,132)];[Some(1,R,39);Some(1,R,134)];[Some(1,R,41);Some(1,R,136)];[Some(1,R,43);Some(1,R,138)];[Some(1,R,45);Some(1,R,140)];[Some(1,R,47);Some(1,R,142)];[Some(0,L,116);Some(0,L,150)];[Some(0,L,120);Some(1,L,127)];[Some(0,L,87);None];[Some(1,L,112);Some(0,R,47)];[Some(0,L,124);Some(0,L,158)];[Some(0,L,95);Some(0,R,79)];[Some(0,L,95);None];[Some(1,R,79);Some(0,R,43)];[Some(1,L,116);Some(1,L,150)];[Some(1,L,120);Some(1,L,127)];[Some(1,L,87);None];[Some(1,L,95);None];[Some(1,L,124);Some(1,L,158)];[Some(1,L,95);Some(0,R,47)];[Some(1,L,95);None];[Some(1,R,47);Some(0,R,138)];[Some(0,R,65);Some(1,L,158)];[Some(0,R,67);Some(0,R,35)];[Some(0,R,69);Some(0,R,39)];[Some(0,R,71);Some(0,R,39)];[Some(0,R,73);Some(0,R,47)];[Some(0,R,75);Some(0,R,43)];[Some(0,R,77);Some(0,R,47)];[Some(0,R,79);Some(0,R,47)];[Some(1,R,65);Some(1,R,47)];[Some(1,R,67);Some(1,R,35)];[Some(1,R,69);Some(1,R,39)];[Some(1,R,71);Some(1,R,39)];[Some(1,R,73);Some(1,R,47)];[Some(1,R,75);Some(1,R,43)];[Some(1,R,77);Some(1,R,47)];[Some(1,R,79);Some(1,R,47)];[Some(0,L,114);Some(0,L,144)];[Some(0,L,83);Some(0,L,146)];[Some(0,L,118);Some(0,L,148)];[Some(0,L,87);Some(0,L,150)];[Some(0,L,122);Some(0,L,152)];[Some(0,L,91);Some(0,L,154)];[Some(0,L,126);Some(0,L,156)];[Some(0,L,95);Some(0,L,158)];[Some(1,L,114);Some(1,L,144)];[Some(1,L,83);Some(1,L,146)];[Some(1,L,118);Some(1,L,148)];[Some(1,L,87);Some(1,L,150)];[Some(1,L,122);Some(1,L,152)];[Some(1,L,91);Some(1,L,154)];[Some(1,L,126);Some(1,L,156)];[Some(1,L,95);Some(1,L,158)];[Some(0,R,128);Some(0,R,1)];[Some(0,R,35);Some(0,R,130)];[Some(0,R,132);Some(0,R,39)];[Some(0,R,5);Some(0,R,5)];[Some(0,R,136);Some(0,R,9)];[Some(0,R,43);Some(0,R,47)];[Some(0,R,140);Some(1,L,127)];[Some(1,L,127);Some(1,L,127)];[Some(1,R,128);Some(1,R,1)];[Some(1,R,35);Some(1,R,130)];[Some(1,R,132);Some(1,R,39)];[Some(1,L,126);Some(1,L,126)];[Some(1,R,136);Some(1,R,9)];[Some(1,R,43);Some(1,L,124)];[Some(1,R,140);Some(1,L,120)];[Some(1,L,112);Some(1,L,95)];[Some(0,L,113);Some(0,L,81)];[Some(0,L,115);Some(0,L,83)];[Some(0,L,117);Some(0,L,85)];[Some(0,L,119);Some(0,L,87)];[Some(0,L,121);Some(0,L,89)];[Some(0,L,123);Some(0,L,91)];[Some(0,L,125);Some(0,L,93)];[Some(0,L,127);Some(0,L,95)];[Some(1,L,113);Some(1,L,81)];[Some(1,L,115);Some(1,L,83)];[Some(1,L,117);Some(1,L,85)];[Some(1,L,119);Some(1,L,87)];[Some(1,L,121);Some(1,L,89)];[Some(1,L,123);Some(1,L,91)];[Some(1,L,125);Some(1,L,93)];[Some(1,L,127);Some(1,L,95)];[Some(0,R,0);Some(0,R,33)];[Some(0,R,2);Some(0,R,67)];[Some(0,R,4);Some(0,R,37)];[Some(0,R,6);Some(0,R,5)];[Some(0,R,8);Some(0,R,41)];[Some(0,R,10);Some(0,R,75)];[Some(0,R,12);Some(0,R,45)];[Some(0,R,14);Some(0,L,127)];[Some(1,R,0);Some(1,R,33)];[Some(1,R,2);Some(1,R,67)];[Some(1,R,4);Some(1,R,37)];[Some(1,R,6);Some(1,L,126)];[Some(1,R,8);Some(1,R,41)];[Some(1,R,10);Some(1,R,75)];[Some(1,R,12);Some(1,R,45)];[Some(1,R,14);Some(0,L,112)];[Some(0,L,127);Some(0,L,112)];[Some(0,L,158);Some(0,L,114)];[Some(1,L,127);Some(0,L,116)];[Some(0,R,71);Some(0,L,118)];[Some(0,L,127);Some(0,L,120)];[None;Some(0,L,122)];[Some(0,R,79);Some(0,L,124)];[Some(0,R,165);Some(0,L,126)];[Some(1,L,127);Some(1,L,112)];[Some(1,L,158);Some(1,L,114)];[Some(1,L,127);Some(1,L,116)];[Some(0,R,39);Some(1,L,118)];[Some(1,L,127);Some(1,L,120)];[None;Some(1,L,122)];[Some(0,R,47);Some(1,L,124)];[Some(0,R,5);Some(1,L,126)];[Some(0,R,161);Some(0,R,1)];[Some(0,R,163);Some(0,R,3)];[Some(0,R,165);Some(0,R,5)];[Some(0,R,167);Some(0,R,7)];[Some(0,R,169);Some(0,R,9)];[Some(0,R,171);Some(0,R,11)];[Some(0,R,173);Some(0,R,13)];[Some(0,R,175);Some(0,R,15)];[Some(1,R,161);Some(1,R,1)];[Some(1,R,163);Some(1,R,3)];[Some(1,R,165);Some(1,R,5)];[Some(1,R,167);Some(1,R,7)];[Some(1,R,169);Some(1,R,9)];[Some(1,R,171);Some(1,R,11)];[Some(1,R,173);Some(1,R,13)];[Some(1,R,175);Some(1,R,15)];[Some(0,L,146);Some(0,L,120)];[None;Some(1,R,79)];[Some(0,L,150);Some(1,L,112)];[None;Some(1,R,71)];[Some(0,L,154);Some(0,L,95)];[None;None];[Some(0,L,158);Some(1,R,79)];[None;Some(1,R,165)];[Some(1,L,146);Some(1,L,120)];[None;Some(1,R,47)];[Some(1,L,150);Some(1,L,95)];[None;Some(1,R,39)];[Some(1,L,154);Some(1,L,95)];[None;None];[Some(1,L,158);Some(1,R,47)];[None;Some(1,R,5)];[Some(0,R,130);None];[Some(1,L,158);None];[Some(0,R,5);None];[Some(0,R,39);None];[Some(0,R,47);None];[Some(0,R,47);None];[Some(1,L,127);None];[Some(0,R,47);None];[Some(1,R,130);None];[Some(1,R,47);None];[Some(1,L,126);None];[Some(1,R,39);None];[Some(1,L,124);None];[Some(1,R,47);None];[Some(1,L,95);None];[Some(1,R,47);None];[Some(0,L,49);None];[Some(0,L,51);None];[Some(0,L,53);None];[Some(0,L,55);None];[Some(0,L,57);None];[Some(0,L,59);None];[Some(0,L,61);None];[Some(0,L,63);None];[Some(1,L,49);None];[Some(1,L,51);None];[Some(1,L,53);None];[Some(1,L,55);None];[Some(1,L,57);None];[Some(1,L,59);None];[Some(1,L,61);None];[Some(1,L,63);None]]%N.
Definition tm1 := TM'_from_str "1RB1RA_1LC1LK_0LD0LC_0RH1LE_0RA1LF_1LD1LG_1LD1LC_0RI0RL_1RN1RJ_0RB0RA_1LD1LK_1RM1RH_0RA---_1LD1LD".
Definition tm2 := TM'_from_str "1RB1RA_1LC1LK_0LD0LC_0RH1LE_0RA1LF_1LD1LG_1LD1LC_0RI0RL_1RN1RJ_0RB0RA_1LD1LK_1RM1RH_0RA1RO_1LD1LD_1RO1RO".
Definition l0 := [0;0;0;0;1;0;1;0;1;1;1;1;1;1;1;1]%N.
Definition mp := mp_from_list [47;79;112;127;126;124;120;5;43;39;95;138;165;71]%N.
Definition mp' := mp_from_list [47;79;112;127;126;124;120;5;43;39;95;138;165;71]%N.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' tm0 tm0' tm1 tm2 mp mp' 13%N l0 (NG 0 1000 1000 1 1 0 0 true) 368 368.
  rewrite I1',I1'0,I2',I2'0; reflexivity.
Time Qed.
End TM30.


