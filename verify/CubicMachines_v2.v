(* cubic.txt: TM6/TM7 grow forever; TM45 halts. Only BusyCoq dependencies. *)
From BusyCoq Require Import Individual62 ES_v3 Eqb Helper BigUint.
Require Import ZifyNat ZifyN Lia String List NArith.

Close Scope sym.
Module Common67.
Inductive phase := PS | PT | PU | PV.
Inductive frame := cfg (p:phase) (l:list nat) (a:nat) (r:list nat).
Fixpoint pad k (l:list nat) := match k,l with
| 0,_=>l | Datatypes.S k,[]=>0::pad k []
| Datatypes.S k,a::l=>a::pad k l end.
Definition prep x := match x with cfg p l a r=>cfg p (pad 2 l) a (pad 3 r) end.
Definition tick x := match x with cfg p (x0::x1::l) a (y0::y1::y2::r) =>
  let l0:=x0::x1::l in let r0:=y0::y1::y2::r in
  match p with
  | PS => match a with
    | Datatypes.S a1=>cfg PT l0 a r0
    | 0=>match x0 with
      | Datatypes.S b=>cfg PS (x1::l) b (0::(1+y0)::y1::y2::r)
      | 0=>cfg PU l x1 (0::(1+y0)::y1::y2::r) end end
  | PU => match a with
    | Datatypes.S a1=>cfg PS l0 a1 (0::r0)
    | 0=>match y0 with
      | 0=>cfg PT (x1::l) (2+x0) (y1::y2::r)
      | 1=>cfg PT ((2+x0)::x1::l) 0 (y1::y2::r)
      | _=>x end end
  | PT => match y0 with
    | Datatypes.S b=>cfg PV l0 (1+a) (b::y1::y2::r)
    | 0=>match y1 with
      | Datatypes.S b=>cfg PT (a::l0) 1 (b::y2::r)
      | 0=>cfg PU l0 a (0::(1+y2)::r) end end
  | PV => match y0 with
    | Datatypes.S b=>cfg PS l0 a (0::b::y1::y2::r)
    | 0=>match y1 with
      | 0=>cfg PT l0 (2+a) (y2::r)
      | 1=>cfg PT ((2+a)::l0) 0 (y2::r)
      | _=>x end end
  end
| _=>x end.
Definition next x:=tick (prep x).
Definition encode x := match x with cfg p l a r =>
  ((match p with PS=>0 | PT=>1 | PU=>2 | PV=>3 end),l,a,r) end.
Lemma encode_inj x y: encode x=encode y -> x=y.
Proof. destruct x as [p l a r],y as [q l' a' r']; destruct p,q;
  cbn; intro H; inversion H; reflexivity. Qed.
Definition target n := prep (cfg PT [] 2
  (([0;1;0;6]++repeat 1 (4+n*2)++[0;11+n*3])++[0])).
Definition check fuel a n :=
  Eqb.eqb (encode (N.iter fuel next (cfg PT [] a []))) (encode (target n)).
Section Abstract.
Variable tm: TM.
Variables S T U V: list nat -> nat -> list nat -> Q*tape.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Hypothesis Spos: forall l a r, S l (1+a) r -->* T l (1+a) r.
Hypothesis Szero: forall l a c r, S ((1+a)::l) 0 (c::r) -->* S l a (0::(1+c)::r).
Hypothesis Sedge: forall l a c r, S (0::a::l) 0 (c::r) -->* U l a (0::(1+c)::r).
Hypothesis Upos: forall l a r, U l (1+a) r -->* S l a (0::r).
Hypothesis Uzero0: forall l a r, U (a::l) 0 (0::r) -->* T l (2+a) r.
Hypothesis Uzero1: forall l a r, U (a::l) 0 (1::r) -->* T ((2+a)::l) 0 r.
Hypothesis Tzero: forall l a c r, T l a (0::0::c::r) -->* U l a (0::(1+c)::r).
Hypothesis Tmix: forall l a c r, T l a (0::(1+c)::r) -->* T (a::l) 1 (c::r).
Hypothesis Tpos: forall l a c r, T l a ((1+c)::r) -->* V l (1+a) (c::r).
Hypothesis Vpos: forall l a c r, V l a ((1+c)::r) -->* S l a (0::c::r).
Hypothesis Vzero0: forall l a r, V l a (0::0::r) -->* T l (2+a) r.
Hypothesis Vzero1: forall l a r, V l a (0::1::r) -->* T ((2+a)::l) 0 r.
Definition denote x := match x with cfg p l a r =>
  (match p with PS=>S | PT=>T | PU=>U | PV=>V end) l a r end.
Hypothesis prep_eq: forall x, denote (prep x)=denote x.
Lemma tick_spec x: denote x -->* denote (tick x).
Proof.
  destruct x as [p [|x0 [|x1 l]] a [|y0 [|y1 [|y2 r]]]];
    cbn [tick denote]; try solve [finish].
  destruct p; cbn [tick denote].
  - destruct a; [destruct x0; cbn [denote]; [apply Sedge|apply Szero]|apply Spos].
  - destruct y0; [destruct y1; cbn [denote]; [apply Tzero|apply Tmix]|apply Tpos].
  - destruct a; [destruct y0 as [|[|y0]]; cbn [denote];
      [apply Uzero0|apply Uzero1|finish]|apply Upos].
  - destruct y0; [destruct y1 as [|[|y1]]; cbn [denote];
      [apply Vzero0|apply Vzero1|finish]|apply Vpos].
Qed.
Lemma next_spec x: denote x -->* denote (next x).
Proof. unfold next. rewrite <- (prep_eq x) at 1. apply tick_spec. Qed.
Lemma run_spec n x: denote x -->* denote (N.iter n next x).
Proof. apply (N.iter_invariant n _ next (fun y=>denote x -->* denote y)).
  - intros y H. eapply evstep_trans; [exact H|apply next_spec].
  - finish. Qed.
Hypothesis Tmixs: forall n l a r, T l a (0::repeat 1 (1+n)++r) -->*
  T (repeat 1 n++a::l) 1 (0::r).
Hypothesis Szeros: forall n l c r, S (repeat 1 (1+n)++l) 0 (c::r) -->*
  S l 0 (0::repeat 1 n++(1+c)::r).
Hypothesis Triples: forall n l a c r, T l a (((1+n)*3+c)::r) -->*
  T (repeat 2 n++(1+a)::l) 1 (c::r).
Hypothesis Cycles: forall m n l c r, S (repeat 3 m++l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (1+n+m)++0::(m*2+c)::r).
Hypothesis Pairs: forall n l r, T l 0 (repeat 1 (n*2)++r) -->* T (repeat 3 n++l) 0 r.
Hypothesis Cycles2: forall m n l c r, S (repeat 2 m++l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (1+n+m)++0::(m+c)::r).
Hypothesis Spos_progress: forall l a r, S l (1+a) r -->+ T l (1+a) r.
Hypothesis Sblankl: forall l a r, S l a r = S (l++[0]) a r.
Hypothesis Ublankl: forall l a r, U l a r = U (l++[0]) a r.
Hypothesis Tblankr: forall l a r, T l a r = T l a (r++[0]).
Lemma rep_snoc (x n:nat) l: repeat x n++x::l = repeat x (1+n)++l.
Proof. induction n; cbn in *; congruence. Qed.
Lemma rep_join (x n m:nat) l: repeat x n++repeat x m++l = repeat x (n+m)++l.
Proof. rewrite repeat_app, app_assoc. reflexivity. Qed.
Lemma cons_rep (x n:nat) l: x::repeat x n++l = repeat x (1+n)++l.
Proof. reflexivity. Qed.
Ltac norm := repeat rewrite <- app_assoc; repeat rewrite rep_join;
  repeat rewrite rep_snoc; cbn [Nat.add Nat.mul app repeat].
Ltac follows H := follow_trans;
  [applys_eq H; norm; solve [repeat rewrite cons_rep; flia]|].
Definition cap n := T [] 2 ([0;1;0;6]++repeat 1 (4+n*2)++[0;11+n*3]).
Lemma cap_step n: cap n -->+ cap (1+n).
Proof.
  unfold cap.
  norm. follows (Tmixs (0) (([])) (2) (((0)::(6)::repeat (1) (4+n*2)++(0)::(11+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (0) (([])) (1) (((0)::(7)::repeat (1) (4+n*2)++(0)::(11+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (0) (([])) (0) (((0)::(8)::repeat (1) (4+n*2)++(0)::(11+n*3)::[]))).
  rewrite (Sblankl _ _ _).
  rewrite (Sblankl _ _ _).
  norm. follow (Sedge).
  rewrite (Ublankl _ _ _).
  norm. follow (Uzero0).
  norm. follow (Tpos).
  norm. follow (Vzero1).
  norm. follow (Tmix).
  norm. follows (Triples (1) (((0)::(5)::[])) (1) (1) ((repeat (1) (4+n*2)++(0)::(11+n*3)::[]))).
  norm. follow (Tpos).
  norm. follow (Vzero1).
  norm. follows (Pairs (1+n) (((4)::(2)::(2)::(0)::(5)::[])) (((1)::(0)::(11+n*3)::[]))).
  norm. follow (Tpos).
  norm. follow (Vzero0).
  norm. follows (Triples (2+n) ((repeat (3) (1+n)++(4)::(2)::(2)::(0)::(5)::[])) (3) (2) (([]))).
  norm. follow (Tpos).
  norm. follow (Vpos).
  norm. follow (Spos).
  rewrite (Tblankr _ _ _).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Spos).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Szero).
  norm. follows (Cycles2 (1+n) (0) (((4)::repeat (3) (1+n)++(4)::(2)::(2)::(0)::(5)::[])) (2) (([]))).
  norm. follow (Spos).
  norm. follows (Tmixs (1+n) (((4)::repeat (3) (1+n)++(4)::(2)::(2)::(0)::(5)::[])) (1) (((0)::(3+n)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (1+n) (((4)::repeat (3) (1+n)++(4)::(2)::(2)::(0)::(5)::[])) (0) (((0)::(4+n)::[]))).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (2+n) ((repeat (3) (1+n)++(4)::(2)::(2)::(0)::(5)::[])) (3) (((0)::(4+n)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (1+n) ((repeat (3) (2+n)++(4)::(2)::(2)::(0)::(5)::[])) (0) (((0)::(5+n)::[]))).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (2+n) ((repeat (3) (1+n)++(4)::(2)::(2)::(0)::(5)::[])) (2) (((0)::(5+n)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (1+n) (((2)::repeat (3) (1+n)++(4)::(2)::(2)::(0)::(5)::[])) (0) (((0)::(6+n)::[]))).
  norm. follow (Szero).
  norm. follows (Cycles (1+n) (2+n) (((4)::(2)::(2)::(0)::(5)::[])) (6+n) (([]))).
  norm. follow (Spos).
  norm. follows (Tmixs (3+n*2) (((4)::(2)::(2)::(0)::(5)::[])) (1) (((0)::(8+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (3+n*2) (((4)::(2)::(2)::(0)::(5)::[])) (0) (((0)::(9+n*3)::[]))).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (4+n*2) (((2)::(2)::(0)::(5)::[])) (3) (((0)::(9+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (3+n*2) (((3)::(2)::(2)::(0)::(5)::[])) (0) (((0)::(10+n*3)::[]))).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (4+n*2) (((2)::(2)::(0)::(5)::[])) (2) (((0)::(10+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (3+n*2) (((2)::(2)::(2)::(0)::(5)::[])) (0) (((0)::(11+n*3)::[]))).
  norm. follow (Szero).
  norm. follows (Cycles2 (2) (4+n*2) (((0)::(5)::[])) (11+n*3) (([]))).
  norm. follow (Spos).
  norm. follows (Tmixs (6+n*2) (((0)::(5)::[])) (1) (((0)::(13+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follows (Szeros (6+n*2) (((0)::(5)::[])) (0) (((0)::(14+n*3)::[]))).
  norm. follow (Sedge).
  norm. follow (Upos).
  norm. follow (Spos).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Spos).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Spos).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Spos).
  norm. follow (Tzero).
  norm. follow (Upos).
  rewrite (Sblankl _ _ _).
  rewrite (Sblankl _ _ _).
  norm. follow (Sedge).
  rewrite (Ublankl _ _ _).
  norm. follow (Uzero0).
  norm. follow (Tpos).
  norm. follow (Vzero0).
  norm. follows (Triples (0) (([])) (5) (2) ((repeat (1) (7+n*2)++(0)::(14+n*3)::[]))).
  norm. follow (Tpos).
  norm. follow (Vpos).
  norm. follow (Spos).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Spos).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (0) (([])) (5) (((0)::(3)::repeat (1) (6+n*2)++(0)::(14+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (0) (([])) (4) (((0)::(4)::repeat (1) (6+n*2)++(0)::(14+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Szero).
  norm. follow (Spos).
  norm. follows (Tmixs (0) (([])) (3) (((0)::(5)::repeat (1) (6+n*2)++(0)::(14+n*3)::[]))).
  norm. follow (Tzero).
  norm. follow (Upos).
  norm. follow (Szero).
  norm. apply Spos_progress.
Qed.
Lemma cap_nonhalt n: ~halts tm (cap n).
Proof. apply (progress_nonhalt_simple tm _ cap n).
  intro k. exists (1+k). apply cap_step. Qed.
Lemma check_spec fuel a n: c0 -->* T [] a [] -> check fuel a n=true -> ~halts tm c0.
Proof.
  intros I H. unfold check in H.
  destruct (Eqb.eqb_spec (encode (N.iter fuel next (cfg PT [] a [])))
    (encode (target n))) as [E|]; [|discriminate].
  apply encode_inj in E.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [exact I|apply (run_spec fuel (cfg PT [] a []))].
  - rewrite E. unfold target. rewrite prep_eq. cbn [denote].
    rewrite <- Tblankr. apply cap_nonhalt.
Qed.
End Abstract.
End Common67.

Module TM6.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0RC1RE_1LD1RB_0LE0LC_1RA0LC_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC l := match l with []=>0inf | a::l=>LC l <* [1]^^a <* [0] end.
Fixpoint RC r := match r with []=>0inf | a::r=>[1]^^a *> [0] *> RC r end.
Definition S l b r := LC l <* [1]^^b <{{C}} RC r.
Definition T l b r := LC l <* [1]^^b {{B}}> RC r.
Definition U l b r := LC l <* [1]^^b <{{E}} RC r.
Definition V l b r := LC l <* [1]^^b {{E}}> RC r.
Close Scope sym.
Lemma Rblank r: RC r = RC (r++[0]).
Proof. induction r; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHr]. Qed.
Lemma Spos l a r: S l (1+a) r -->* T l (1+a) r.
Proof. es. Qed.
Lemma Szero l a c r: S ((1+a)::l) 0 (c::r) -->* S l a (0::(1+c)::r).
Proof. es. Qed.
Lemma Sedge l a c r: S (0::a::l) 0 (c::r) -->* U l a (0::(1+c)::r).
Proof. es. Qed.
Lemma Upos l a r: U l (1+a) r -->* S l a (0::r).
Proof. es. Qed.
Lemma Uzero0 l a r: U (a::l) 0 (0::r) -->* T l (2+a) r.
Proof. es. Qed.
Lemma Uzero1 l a r: U (a::l) 0 (1::r) -->* T ((2+a)::l) 0 r.
Proof. es. Qed.
Lemma Tzero l a c r: T l a (0::0::c::r) -->* U l a (0::(1+c)::r).
Proof. es. Qed.
Lemma Tmix l a c r: T l a (0::(1+c)::r) -->* T (a::l) 1 (c::r).
Proof. es. Qed.
Lemma Tpos l a c r: T l a ((1+c)::r) -->* V l (1+a) (c::r).
Proof. es. Qed.
Lemma Vpos l a c r: V l a ((1+c)::r) -->* S l a (0::c::r).
Proof. es. Qed.
Lemma Vzero0 l a r: V l a (0::0::r) -->* T l (2+a) r.
Proof. es. Qed.
Lemma Vzero1 l a r: V l a (0::1::r) -->* T ((2+a)::l) 0 r.
Proof. es. Qed.
Lemma rep_snoc (x n:nat) l: repeat x n++x::l = repeat x (1+n)++l.
Proof. induction n; cbn in *; congruence. Qed.
Lemma Tmixs n l a r: T l a (0::repeat 1 (1+n)++r) -->*
  T (repeat 1 n++a::l) 1 (0::r).
Proof.
  gen l a. induction n; intros; [apply Tmix|].
  follow Tmix. follow (IHn (a::l) 1). rewrite rep_snoc. finish.
Qed.
Lemma Szeros n l c r: S (repeat 1 (1+n)++l) 0 (c::r) -->*
  S l 0 (0::repeat 1 n++(1+c)::r).
Proof.
  gen c r. induction n; intros; [apply Szero|].
  follow Szero. follow (IHn 0 ((1+c)::r)). rewrite rep_snoc. finish.
Qed.
Lemma Triple l a c r: T l a ((3+c)::r) -->* T ((1+a)::l) 1 (c::r).
Proof. follow Tpos. follow Vpos. follow Spos. follow Tmix. finish. Qed.
Lemma Triples n l a c r: T l a (((1+n)*3+c)::r) -->*
  T (repeat 2 n++(1+a)::l) 1 (c::r).
Proof.
  gen l a. induction n; intros; [apply Triple|].
  follow Triple. follow (IHn ((1+a)::l) 1). rewrite rep_snoc. finish.
Qed.
Lemma init: c0 -->* T [] 1 [].
Proof. unfold T; cbn [LC RC]. esx. Qed.
Lemma Cycle l n c r: S (3::l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (2+n)++0::(2+c)::r).
Proof.
  follow Spos. follow (Tmixs n (3::l) 1 (0::c::r)).
  rewrite rep_snoc. follow Tzero. follow Upos.
  follow (Szeros n (3::l) 0 (0::(1+c)::r)). rewrite rep_snoc.
  follow Szero. follow Spos.
  follow (Tmixs (1+n) l 2 (0::(1+c)::r)).
  follow Tzero. follow Upos.
  follow (Szeros n (2::l) 0 (0::(2+c)::r)). rewrite rep_snoc.
  follow Szero. finish.
Qed.
Lemma Cycles m n l c r: S (repeat 3 m++l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (1+n+m)++0::(m*2+c)::r).
Proof.
  gen n c. induction m; intros; [finish|].
  follow Cycle. follow (IHm (1+n) (2+c)). finish.
Qed.
Lemma Pairs n l r: T l 0 (repeat 1 (n*2)++r) -->* T (repeat 3 n++l) 0 r.
Proof.
  gen l. induction n; intros; [finish|].
  follow Tpos. follow Vzero1. follow (IHn (3::l)). rewrite rep_snoc. finish.
Qed.
Lemma Cycle2 l n c r: S (2::l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (2+n)++0::(1+c)::r).
Proof.
  follow Spos. follow (Tmixs n (2::l) 1 (0::c::r)).
  rewrite rep_snoc. follow Tzero. follow Upos.
  follow (Szeros n (2::l) 0 (0::(1+c)::r)). rewrite rep_snoc.
  follow Szero. finish.
Qed.
Lemma Cycles2 m n l c r: S (repeat 2 m++l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (1+n+m)++0::(m+c)::r).
Proof.
  gen n c. induction m; intros; [finish|].
  follow Cycle2. follow (IHm (1+n) (1+c)). finish.
Qed.
Lemma LC_pad k l: LC (Common67.pad k l)=LC l.
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [rewrite <- const_unfold|]; reflexivity. Qed.
Lemma RC_pad k l: RC (Common67.pad k l)=RC l.
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [rewrite <- const_unfold|]; reflexivity. Qed.
Lemma prep_eq x: Common67.denote S T U V (Common67.prep x)=Common67.denote S T U V x.
Proof. destruct x as [p l a r]; destruct p; cbn [Common67.prep Common67.denote];
  unfold S,T,U,V; rewrite LC_pad,RC_pad; reflexivity. Qed.
Lemma Lblanks l: LC l=LC (l++[0]).
Proof. induction l; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHl]. Qed.
Lemma Spos_progress l a r: S l (1+a) r -[tm]->+ T l (1+a) r.
Proof. es. Qed.
Lemma Sblankl l a r: S l a r=S (l++[0]) a r.
Proof. unfold S. now rewrite <- Lblanks. Qed.
Lemma Ublankl l a r: U l a r=U (l++[0]) a r.
Proof. unfold U. now rewrite <- Lblanks. Qed.
Lemma Tblankr l a r: T l a r=T l a (r++[0]).
Proof. unfold T. now rewrite <- Rblank. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (Common67.check_spec tm S T U V) with (a:=1) (n:=476) (fuel:=89885063%N);
    try solve [apply Spos|apply Szero|apply Sedge|apply Upos|apply Uzero0|apply Uzero1|
      apply Tzero|apply Tmix|apply Tpos|apply Vpos|apply Vzero0|apply Vzero1|
      apply prep_eq|apply Tmixs|apply Szeros|apply Triples|apply Cycles|apply Pairs|
      apply Cycles2|apply Spos_progress|apply Sblankl|apply Ublankl|apply Tblankr|apply init].
  native_check_eq.
Qed.
End TM6.
Module TM7.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RF_0RD1RA_1LE1RC_0LA0LD_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC l := match l with []=>0inf | a::l=>LC l <* [1]^^a <* [0] end.
Fixpoint RC r := match r with []=>0inf | a::r=>[1]^^a *> [0] *> RC r end.
Definition S l b r := LC l <* [1]^^b <{{D}} RC r.
Definition T l b r := LC l <* [1]^^b {{C}}> RC r.
Definition U l b r := LC l <* [1]^^b <{{A}} RC r.
Definition V l b r := LC l <* [1]^^b {{A}}> RC r.
Close Scope sym.
Lemma Rblank r: RC r = RC (r++[0]).
Proof. induction r; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHr]. Qed.
Lemma Spos l a r: S l (1+a) r -->* T l (1+a) r.
Proof. es. Qed.
Lemma Szero l a c r: S ((1+a)::l) 0 (c::r) -->* S l a (0::(1+c)::r).
Proof. es. Qed.
Lemma Sedge l a c r: S (0::a::l) 0 (c::r) -->* U l a (0::(1+c)::r).
Proof. es. Qed.
Lemma Upos l a r: U l (1+a) r -->* S l a (0::r).
Proof. es. Qed.
Lemma Uzero0 l a r: U (a::l) 0 (0::r) -->* T l (2+a) r.
Proof. es. Qed.
Lemma Uzero1 l a r: U (a::l) 0 (1::r) -->* T ((2+a)::l) 0 r.
Proof. es. Qed.
Lemma Tzero l a c r: T l a (0::0::c::r) -->* U l a (0::(1+c)::r).
Proof. es. Qed.
Lemma Tmix l a c r: T l a (0::(1+c)::r) -->* T (a::l) 1 (c::r).
Proof. es. Qed.
Lemma Tpos l a c r: T l a ((1+c)::r) -->* V l (1+a) (c::r).
Proof. es. Qed.
Lemma Vpos l a c r: V l a ((1+c)::r) -->* S l a (0::c::r).
Proof. es. Qed.
Lemma Vzero0 l a r: V l a (0::0::r) -->* T l (2+a) r.
Proof. es. Qed.
Lemma Vzero1 l a r: V l a (0::1::r) -->* T ((2+a)::l) 0 r.
Proof. es. Qed.
Lemma rep_snoc (x n:nat) l: repeat x n++x::l = repeat x (1+n)++l.
Proof. induction n; cbn in *; congruence. Qed.
Lemma Tmixs n l a r: T l a (0::repeat 1 (1+n)++r) -->*
  T (repeat 1 n++a::l) 1 (0::r).
Proof.
  gen l a. induction n; intros; [apply Tmix|].
  follow Tmix. follow (IHn (a::l) 1). rewrite rep_snoc. finish.
Qed.
Lemma Szeros n l c r: S (repeat 1 (1+n)++l) 0 (c::r) -->*
  S l 0 (0::repeat 1 n++(1+c)::r).
Proof.
  gen c r. induction n; intros; [apply Szero|].
  follow Szero. follow (IHn 0 ((1+c)::r)). rewrite rep_snoc. finish.
Qed.
Lemma Triple l a c r: T l a ((3+c)::r) -->* T ((1+a)::l) 1 (c::r).
Proof. follow Tpos. follow Vpos. follow Spos. follow Tmix. finish. Qed.
Lemma Triples n l a c r: T l a (((1+n)*3+c)::r) -->*
  T (repeat 2 n++(1+a)::l) 1 (c::r).
Proof.
  gen l a. induction n; intros; [apply Triple|].
  follow Triple. follow (IHn ((1+a)::l) 1). rewrite rep_snoc. finish.
Qed.
Lemma init: c0 -->* T [] 2 [].
Proof. unfold T; cbn [LC RC]. esx. Qed.
Lemma Cycle l n c r: S (3::l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (2+n)++0::(2+c)::r).
Proof.
  follow Spos. follow (Tmixs n (3::l) 1 (0::c::r)).
  rewrite rep_snoc. follow Tzero. follow Upos.
  follow (Szeros n (3::l) 0 (0::(1+c)::r)). rewrite rep_snoc.
  follow Szero. follow Spos.
  follow (Tmixs (1+n) l 2 (0::(1+c)::r)).
  follow Tzero. follow Upos.
  follow (Szeros n (2::l) 0 (0::(2+c)::r)). rewrite rep_snoc.
  follow Szero. finish.
Qed.
Lemma Cycles m n l c r: S (repeat 3 m++l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (1+n+m)++0::(m*2+c)::r).
Proof.
  gen n c. induction m; intros; [finish|].
  follow Cycle. follow (IHm (1+n) (2+c)). finish.
Qed.
Lemma Pairs n l r: T l 0 (repeat 1 (n*2)++r) -->* T (repeat 3 n++l) 0 r.
Proof.
  gen l. induction n; intros; [finish|].
  follow Tpos. follow Vzero1. follow (IHn (3::l)). rewrite rep_snoc. finish.
Qed.
Lemma Cycle2 l n c r: S (2::l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (2+n)++0::(1+c)::r).
Proof.
  follow Spos. follow (Tmixs n (2::l) 1 (0::c::r)).
  rewrite rep_snoc. follow Tzero. follow Upos.
  follow (Szeros n (2::l) 0 (0::(1+c)::r)). rewrite rep_snoc.
  follow Szero. finish.
Qed.
Lemma Cycles2 m n l c r: S (repeat 2 m++l) 1 (0::repeat 1 (1+n)++0::c::r) -->*
  S l 1 (0::repeat 1 (1+n+m)++0::(m+c)::r).
Proof.
  gen n c. induction m; intros; [finish|].
  follow Cycle2. follow (IHm (1+n) (1+c)). finish.
Qed.
Lemma LC_pad k l: LC (Common67.pad k l)=LC l.
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [rewrite <- const_unfold|]; reflexivity. Qed.
Lemma RC_pad k l: RC (Common67.pad k l)=RC l.
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [rewrite <- const_unfold|]; reflexivity. Qed.
Lemma prep_eq x: Common67.denote S T U V (Common67.prep x)=Common67.denote S T U V x.
Proof. destruct x as [p l a r]; destruct p; cbn [Common67.prep Common67.denote];
  unfold S,T,U,V; rewrite LC_pad,RC_pad; reflexivity. Qed.
Lemma Lblanks l: LC l=LC (l++[0]).
Proof. induction l; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHl]. Qed.
Lemma Spos_progress l a r: S l (1+a) r -[tm]->+ T l (1+a) r.
Proof. es. Qed.
Lemma Sblankl l a r: S l a r=S (l++[0]) a r.
Proof. unfold S. now rewrite <- Lblanks. Qed.
Lemma Ublankl l a r: U l a r=U (l++[0]) a r.
Proof. unfold U. now rewrite <- Lblanks. Qed.
Lemma Tblankr l a r: T l a r=T l a (r++[0]).
Proof. unfold T. now rewrite <- Rblank. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (Common67.check_spec tm S T U V) with (a:=2) (n:=339) (fuel:=38711955%N);
    try solve [apply Spos|apply Szero|apply Sedge|apply Upos|apply Uzero0|apply Uzero1|
      apply Tzero|apply Tmix|apply Tpos|apply Vpos|apply Vzero0|apply Vzero1|
      apply prep_eq|apply Tmixs|apply Szeros|apply Triples|apply Cycles|apply Pairs|
      apply Cycles2|apply Spos_progress|apply Sblankl|apply Ublankl|apply Tblankr|apply init].
  native_check_eq.
Qed.
End TM7.

Module TM45.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0LD_1LD0RF_0LB0LA_1LC1RE_---0RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC l := match l with []=>0inf | a::l=>LC l <* [1]^^a <* [0] end.
Fixpoint RC r := match r with []=>0inf | a::r=>[1]^^a *> [0] *> RC r end.
Definition S l b r := LC l <* [1]^^b <{{C}} RC r.
Definition T l b r := LC l <* [1]^^b {{E}}> RC r.
Definition U l b r := LC l <* [1]^^b <{{B}} RC r.
Close Scope sym.
Lemma Sstep l a c r: S ((2+a)::l) 0 (c::r) -->* S (a::l) 0 ((2+c)::r).
Proof. es. Qed.
Lemma Sshift n l a c r: S ((n*2+a)::l) 0 (c::r) -->*
  S (a::l) 0 ((n*2+c)::r).
Proof. gen a c. ind n Sstep. Qed.
Lemma Szero l a c r: S (0::a::l) 0 (c::r) -->* U l a (0::(1+c)::r).
Proof. es. Qed.
Lemma Sone l a c r: S (1::a::l) 0 ((1+c)::r) -->* T (0::(2+a)::l) 0 (c::r).
Proof. es. Qed.
Lemma HSone l r: halts tm (S (1::l) 0 (0::r)).
Proof. destruct l; unfold S; cbn [LC RC]; esx. Qed.
Lemma Spos l a c r: S l (1+a) ((1+c)::r) -->* T (0::a::l) 0 (c::r).
Proof. es. Qed.
Lemma HSpos l a r: halts tm (S l (1+a) (0::r)).
Proof. esx. Qed.
Lemma Tscan l a b c r: T l a (b::c::r) -->* S l (b+a) ((1+c)::r).
Proof. unfold S, T; cbn [LC RC]. es' a b c & (LC l) (RC r). Qed.
Lemma Ularge l a r: U l (3+a) r -->* S (a::l) 0 (1::r).
Proof. es. Qed.
Lemma Utwo l c r: U l 2 (c::r) -->* S l 0 ((2+c)::r).
Proof. destruct l; unfold U, S; cbn [LC RC]; es. Qed.
Lemma Uone l a r: U (a::l) 1 r -->* U l a (0::0::r).
Proof. es. Qed.
Lemma Upos l a c r: U (a::l) 0 ((2+c)::r) -->* T (0::(1+a)::l) 0 (c::r).
Proof. es. Qed.
Lemma HUone l r: halts tm (U l 0 (1::r)).
Proof. destruct l; unfold U; cbn [LC RC]; esx. Qed.
Lemma Uzero l a c r: U ((1+a)::l) 0 (0::c::r) -->* S (a::l) 0 ((2+c)::r).
Proof. es. Qed.
Lemma Uedge l a c r: U (0::a::l) 0 (0::(1+c)::r) -->* T (0::(2+a)::l) 0 (c::r).
Proof. es. Qed.
Lemma HUedge l r: halts tm (U (0::l) 0 (0::0::r)).
Proof. destruct l; unfold U; cbn [LC RC]; esx. Qed.
Lemma Inc l a b c r: S (0::a::l) (9+b*2) (1::c::r) -->*
  S (0::(2+a)::l) (3+b*2) (1::(4+c)::r).
Proof.
  follow Spos. follow Tscan. follow Szero. follow Ularge.
  fold Nat.add Nat.mul.
  follow (Sshift (2+b) (0::a::l) 1 1 (0::(2+c)::r)).
  follow Sone. follow Tscan. follow Spos. follow Tscan. follow Szero.
  fold Nat.add Nat.mul. follow (Ularge (0::2::a::l) (b*2) (0::(4+c)::r)).
  follow (Sshift b (0::2::a::l) 0 1 (0::(4+c)::r)).
  follow Szero. follow Uzero. follow Sone. follow Tscan. finish.
Qed.
Lemma Incs n k l a c r: S (0::a::l) (n*6+3+k*2) (1::c::r) -->*
  S (0::(n*2+a)::l) (3+k*2) (1::(n*4+c)::r).
Proof.
  gen a c. induction n; intros; [finish|].
  follow (Inc l a (n*3+k) c r). follow (IHn (2+a) (4+c)). finish.
Qed.
Lemma init: c0 -->* T [] 0 [0;1].
Proof. unfold T; cbn [LC RC]. esx. Qed.

Module Kernel.
Import BigUint.
Definition N2 := Eval compute in of_nat 2.
Definition N3 := Eval compute in of_nat 3.
Definition N4 := Eval compute in of_nat 4.
Definition N5 := Eval compute in of_nat 5.
Definition N6 := Eval compute in of_nat 6.
Definition N7 := Eval compute in of_nat 7.
Inductive phase := PS | PT | PU.
Inductive state := cfg (p:phase) (l:list N') (a:N') (r:list N').
Definition denote x := match x with cfg p l a r =>
  (match p with PS=>S | PT=>T | PU=>U end)
    (map to_nat l) (to_nat a) (map to_nat r) end.
Fixpoint pad k (l:list N') := match k,l with
| 0,_ => l | Datatypes.S k,[] => N0::pad k []
| Datatypes.S k,a::l => a::pad k l end.
Definition prep x := match x with cfg p l a r => cfg p (pad 2 l) a (pad 2 r) end.
Lemma LC_pad k l: LC (map to_nat (pad k l)) = LC (map to_nat l).
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [rewrite <- const_unfold|]; reflexivity. Qed.
Lemma RC_pad k l: RC (map to_nat (pad k l)) = RC (map to_nat l).
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [rewrite <- const_unfold|]; reflexivity. Qed.
Lemma prep_eq x: denote (prep x)=denote x.
Proof. destruct x as [p l a r]; destruct p; cbn [prep denote];
  unfold S,T,U; rewrite LC_pad,RC_pad; reflexivity. Qed.

Definition edge p x0 x1 l a y0 y1 r := (match p with
| PS => match pred a with
  | Some a1 => match pred y0 with
    | Some c => Some (cfg PT (N0::a1::x0::x1::l) N0 (c::y1::r)) | None=>None end
  | None => match pred x0 with
    | None => Some (cfg PU l x1 (N0::succ y0::y1::r))
    | Some v => match pred v with
      | None => match pred y0 with
        | Some c => Some (cfg PT (N0::(N2+x1)::l) N0 (c::y1::r)) | None=>None end
      | Some _ => match divmod_small x0 N2 with
        | Some (n,d) => Some (cfg PS (d::x1::l) N0 ((n+n+y0)::y1::r))
        | None => Some (cfg PS (x0::x1::l) a (y0::y1::r)) end end end end
| PT => Some (cfg PS (x0::x1::l) (a+y0) (succ y1::r))
| PU => match pred a with
  | Some a1 => match pred a1 with
    | Some a2 => match pred a2 with
      | Some a3 => Some (cfg PS (a3::x0::x1::l) N0 (N1::y0::y1::r))
      | None => Some (cfg PS (x0::x1::l) N0 ((N2+y0)::y1::r)) end
    | None => Some (cfg PU (x1::l) x0 (N0::N0::y0::y1::r)) end
  | None => match pred y0 with
    | Some c1 => match pred c1 with
      | Some c2 => Some (cfg PT (N0::succ x0::x1::l) N0 (c2::y1::r)) | None=>None end
    | None => match pred x0 with
      | Some v => Some (cfg PS (v::x1::l) N0 ((N2+y1)::r))
      | None => match pred y1 with
        | Some c => Some (cfg PT (N0::(N2+x1)::l) N0 (c::r)) | None=>None end end end end
end)%N'.

Definition loop_result l a c r n b :=
  cfg PS (N0::(n+n+a)%N'::l) b (N1::(n*N4+c)%N'::r).
Definition loops l a b c r := match divmod_small b N6 with
| Some (q,d) => match pred q with
  | None => None
  | Some q1 => match pred d with
    | None => None
    | Some d1 => match pred d1 with
      | None => match pred q1 with
        | None => None | Some _ => Some (loop_result l a c r q1 N7) end
      | Some d2 => match pred d2 with
        | None => None
        | Some d3 => match pred d3 with
          | None => Some (loop_result l a c r q N3)
          | Some d4 => match pred d4 with
            | None => None
            | Some d5 => match pred d5 with
              | None => Some (loop_result l a c r q N5) | Some _=>None end
            end end end end end end
| None=>None end.
Definition fast x := match x with
| cfg PS (x0::a::l) b (y0::c::r) =>
  if is0 x0 then match pred y0 with
  | Some y => if is0 y then loops l a b c r else None | None=>None end
  else None
| _=>None end.
Definition tick x := match fast x with
| Some y=>Some y
| None=>match x with
  | cfg p (x0::x1::l) a (y0::y1::r)=>edge p x0 x1 l a y0 y1 r
  | _=>Some x end end.
Definition next x := tick (prep x).

Ltac des_pred := match goal with
| |- context[match pred ?a with _ => _ end] =>
  let H:=fresh "H" in pose proof (inj_pred a) as H; destruct (pred a)
end.
Ltac nums := rw_N';
  change (to_nat N0) with 0 in *; change (to_nat N1) with 1 in *;
  change (to_nat N2) with 2 in *; change (to_nat N3) with 3 in *;
  change (to_nat N4) with 4 in *; change (to_nat N5) with 5 in *;
  change (to_nat N6) with 6 in *; change (to_nat N7) with 7 in *.
Ltac solve_rule rule := applys_eq rule; flia.

Lemma edge_spec p x0 x1 l a y0 y1 r:
match edge p x0 x1 l a y0 y1 r with
| Some y=>denote (cfg p (x0::x1::l) a (y0::y1::r)) -->* denote y
| None=>halts tm (denote (cfg p (x0::x1::l) a (y0::y1::r))) end.
Proof.
  destruct p; unfold edge; repeat des_pred; cbn [denote map]; nums.
  all: try (match goal with |-context[divmod_small ?v N2]=>
    destruct (divmod_small v N2) as [[n d]|] eqn:E;
    [pose proof (inj_divmod_small _ _ _ _ E)|]; cbn [denote map]; nums end).
  all: try first [solve [finish] | solve [solve_rule Spos] |
    solve [solve_rule Szero] | solve [solve_rule Sone] | solve [solve_rule HSone] |
    solve [solve_rule Tscan] |
    solve [solve_rule Ularge] | solve [solve_rule Utwo] | solve [solve_rule Uone] |
    solve [solve_rule Upos] | solve [solve_rule HUone] | solve [solve_rule Uzero] |
    solve [solve_rule Uedge] | solve [solve_rule HUedge]].
  - rewrite H,H0. apply HSpos.
  - (applys_eq (Sshift (to_nat n) (to_nat x1::map to_nat l)
      (to_nat d) (to_nat y0) (to_nat y1::map to_nat r)); flia).
Qed.
Lemma loops_spec l a b c r y: loops l a b c r = Some y ->
  S (0::to_nat a::map to_nat l) (to_nat b) (1::to_nat c::map to_nat r) -->* denote y.
Proof.
  unfold loops. destruct (divmod_small b N6) as [[q d]|] eqn:E; [|discriminate].
  pose proof (inj_divmod_small _ _ _ _ E) as Hq. nums.
  repeat des_pred; try discriminate; intro E1; inversion E1; subst y;
    cbn [loop_result denote map]; nums.
  all: first [solve [solve_rule (Incs (to_nat q-1) 2 (map to_nat l) (to_nat a) (to_nat c) (map to_nat r))] |
    solve [solve_rule (Incs (to_nat q) 0 (map to_nat l) (to_nat a) (to_nat c) (map to_nat r))] |
    solve [solve_rule (Incs (to_nat q) 1 (map to_nat l) (to_nat a) (to_nat c) (map to_nat r))]].
Qed.
Lemma fast_spec x y: fast x=Some y -> denote x -->* denote y.
Proof.
  destruct x as [p l b r]; destruct p; cbn [fast]; try discriminate.
  destruct l as [|x0 [|a l]],r as [|y0 [|c r]]; try discriminate.
  destruct (inj_is0 x0); [|discriminate].
  des_pred; [|discriminate]. destruct (inj_is0 b0); [|discriminate].
  intros E; cbn [denote map]; nums.
  applys_eq (loops_spec l a b c r y E); flia.
Qed.
Lemma tick_spec x: match tick x with
| Some y=>denote x -->* denote y | None=>halts tm (denote x) end.
Proof.
  unfold tick. destruct (fast x) eqn:E; [apply fast_spec,E|].
  destruct x as [p l a r]; destruct l as [|x0 [|x1 l]],r as [|y0 [|y1 r]];
    try solve [finish]; apply edge_spec.
Qed.
Lemma next_spec x: match next x with
| Some y=>denote x -->* denote y | None=>halts tm (denote x) end.
Proof. unfold next. pose proof (tick_spec (prep x)) as H.
  destruct (tick (prep x)); rewrite prep_eq in H; exact H. Qed.
Definition initial := cfg PT [] N0 [N0;N1].
Definition next' x := match next x with Some y=>inl y | None=>inr tt end.
Definition check fuel := match N_iter_until next' (inl initial) fuel with
| inr _=>true | _=>false end.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof.
  unfold check. intro H.
  assert (match N_iter_until next' (inl initial) fuel with
    | inl y=>c0 -->* denote y | inr _=>halts tm c0 end) as R.
  { apply N_iter_until_spec.
    - intros x Hx. unfold next'. pose proof (next_spec x) as E. destruct (next x).
      + eapply evstep_trans; eauto.
      + eapply halts_evstep; eauto.
    - apply init. }
  destruct (N_iter_until next' (inl initial) fuel); [discriminate|exact R].
Qed.
End Kernel.
Theorem halt: halts tm c0.
Proof. apply (Kernel.check_spec 205000000%N). native_check_eq. Qed.
End TM45.
