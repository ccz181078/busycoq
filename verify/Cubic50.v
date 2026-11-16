(* cubic.txt TM50: verified RLE execution and affine-return memoization.
   The final computation generates its own rules; no trajectory table is stored. *)
From BusyCoq Require Import Individual62 ES_v3 Eqb Helper.
Require Import ZifyNat ZifyN Lia String List NArith FMapPositive.
Open Scope sym.
Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RB_1LD0LD_1RA1LC_---1LF_1LA0LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC l := match l with []=>0inf | a::l=>LC l <* [1]^^a <* [0] end.
Fixpoint RC r := match r with []=>0inf | a::r=>[1]^^a *> [0] *> RC r end.
Definition S l b r := LC l <* [1]^^b <{{C}} RC r.
Definition T l b r := LC l <* [1]^^b {{B}}> RC r.
Definition U l b r := LC l <* [1]^^b <{{F}} RC r.
Definition V l b r := LC l <* [1]^^b <{{A}} RC r.
Close Scope sym.
Lemma Lblank: LC [] = LC [0].
Proof. cbn. rewrite <- const_unfold. reflexivity. Qed.
Lemma Rblank r: RC r = RC (r++[0]).
Proof. induction r; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHr]. Qed.
Lemma Szero l a r: S (0::a::l) 0 r -->* U l a (1::r).
Proof. es. Qed.
Lemma Sleft l a c r: S ((1+a)::l) 0 (c::r) -->* S l a ((2+c)::r).
Proof. es. Qed.
Lemma Sone l a r: S (a::l) 1 r -->* T l (2+a) r.
Proof. es. Qed.
Lemma Spos l a r: S l (2+a) r -->* S l a (1::r).
Proof. es. Qed.
Lemma Tzero l a r: T l a (0::0::r) -->* U l a (1::r).
Proof. es. Qed.
Lemma Tmix l a c r: T l a (0::(1+c)::r) -->* T l (2+a) (c::r).
Proof. es. Qed.
Lemma Tpos l a c r: T l a ((1+c)::r) -->* T (a::l) 0 (c::r).
Proof. es. Qed.
Lemma Uzero l a c r: U (a::l) 0 (c::r) -->* V l a ((1+c)::r).
Proof. es. Qed.
Lemma Upos l a r: U l (1+a) r -->* S l a (0::r).
Proof. es. Qed.
Lemma Vzero l a r: V (a::l) 0 r -->* T l (1+a) r.
Proof. es. Qed.
Lemma HV l r: halts tm (V l 1 r).
Proof. destruct l; unfold V; cbn [LC]; esx. Qed.
Lemma Vpos l a r: V l (2+a) r -->* U l a (1::r).
Proof. es. Qed.
Lemma rep_snoc (x n:nat) l: repeat x n++x::l = repeat x (1+n)++l.
Proof. induction n; cbn in *; congruence. Qed.
Lemma Slefts n l a r: S l (n*2+a) r -->* S l a (repeat 1 n++r).
Proof.
  gen r. induction n; intros; [finish|].
  follow Spos. follow (IHn (1::r)). rewrite rep_snoc. finish.
Qed.
Lemma Trights n l a r: T l a ((1+n)::r) -->* T (repeat 0 n++a::l) 0 (0::r).
Proof.
  gen l a. induction n; intros; [apply Tpos|].
  follow Tpos. follow (IHn (a::l) 0). rewrite rep_snoc. finish.
Qed.
Lemma Tmixs n l a r: T l a (0::repeat 1 n++r) -->* T l (n*2+a) (0::r).
Proof. gen a. ind n Tmix. Qed.
Lemma Inc l a b r: S (a::l) (5+b*2) (0::r) -->*
  S ((2+a)::l) (1+b*2) (0::1::r).
Proof.
  follow (Slefts (2+b) (a::l) 1 (0::r)). follow Sone. follow Tpos.
  follow (Tmixs (1+b) ((2+a)::l) 0 (0::r)). follow Tzero.
  fold Nat.add Nat.mul. follow (Upos ((2+a)::l) (1+b*2) (1::r)). finish.
Qed.
Lemma Incs n k l a r: S (a::l) (n*4+1+k*2) (0::r) -->*
  S ((n*2+a)::l) (1+k*2) (0::repeat 1 n++r).
Proof.
  gen a r. induction n; intros; [finish|].
  follow (Inc l a (n*2+k) r). follow (IHn (2+a) (1::r)). rewrite rep_snoc. finish.
Qed.
Lemma init: c0 -->* T [] 1 [].
Proof. unfold T; cbn [LC RC]. esx. Qed.

Module Kernel.
Local Notation "a && b" := (if a then b else false) (at level 40,left associativity).
Local Notation "a || b" := (if a then true else b) (at level 50,left associativity).
Record ops := Ops {
  num:Type; sample:num->N; con:N->num; add:num->num->num;
  sub:num->num->option num; div:num->N->option (num*N);
  eq:num->num->bool
}.
Arguments sample {_} _.
Arguments con {_} _.
Arguments add {_} _ _.
Arguments sub {_} _ _.
Arguments div {_} _ _.
Arguments eq {_} _ _.
Record laws (o:ops) (v:num o->nat) := Laws {
  con_ok: forall n, v (con n)=N.to_nat n;
  add_ok: forall x y, v (add x y)=v x+v y;
  sub_ok: forall x y z, sub x y=Some z -> v x=v y+v z;
  div_ok: forall x n q r, div x n=Some(q,r) ->
    v x=v q*N.to_nat n+N.to_nat r;
  eq_ok: forall x y, eq x y=true -> v x=v y
}.
Inductive phase:=PS|PT|PU|PV.
Inductive frame (A:Type):=cfg (p:phase) (l:list(A*A)) (a:A) (r:list(A*A)).
Arguments cfg {_} _ _ _ _.
Notation "'let?' x := a 'in' b" :=
  (match a with Some x=>b | None=>None end) (at level 200,x pattern,a at level 100,b at level 200).
Section Generic.
Context {o:ops}.
Definition push x n (l:list(num o*num o)) :=
  if eq n (con 0%N) then l else
  match l with (y,m)::l' => if eq x y then (y,add n m)::l' else (x,n)::l
  | []=>(x,n)::[] end.
Fixpoint pop (l:list(num o*num o)) := match l with
| []=>Some(con 0%N,[])
| (x,n)::l'=>if eq n (con 0%N) then pop l' else
    let? n' := sub n (con 1%N) in
    Some(x,if eq n' (con 0%N) then l' else (x,n')::l')
end.
Definition near (r:list(num o*num o)):=match r with []=>con 0%N | (x,_)::_=>x end.
Definition step x := match x with cfg p l a r => match p with
| PS =>
  if (5<=?sample a)%N && N.odd (sample a) && (sample (near r)=?0)%N then
    if eq (near r) (con 0%N) then
      let? b := sub a (con 1%N) in let? (n,d) := div b 4%N in
      if (d=?0)%N || (d=?2)%N then
        let? (x,l') := pop l in let? (c,r') := pop r in
        if eq c (con 0%N) then
        Some(Some(cfg PS (push (add x (add n n)) (con 1%N) l')
          (con (1+d)%N) (push (con 0%N) (con 1%N) (push (con 1%N) n r'))))
        else None
      else None
    else None
  else if (2<=?sample a)%N then
    let? (n,d) := div a 2%N in
    Some(Some(cfg PS l (con d) (push (con 1%N) n r)))
  else if (sample a=?1)%N then
    if eq a (con 1%N) then let? (x,l') := pop l in
      Some(Some(cfg PT l' (add (con 2%N) x) r)) else None
  else if eq a (con 0%N) then
    let? (x,l') := pop l in
    if (0<?sample x)%N then let? x' := sub x (con 1%N) in
      let? (c,r') := pop r in Some(Some(cfg PS l' x' (push (add (con 2%N) c) (con 1%N) r')))
    else if eq x (con 0%N) then let? (y,l'') := pop l' in
      Some(Some(cfg PU l'' y (push (con 1%N) (con 1%N) r))) else None
  else None
| PT => let? (c,r') := pop r in
  if (0<?sample c)%N then let? n := sub c (con 1%N) in
    Some(Some(cfg PT (push (con 0%N) n (push a (con 1%N) l)) (con 0%N)
      (push (con 0%N) (con 1%N) r')))
  else if eq c (con 0%N) then match r' with
    | (d,n)::r'' => if (sample d=?1)%N then
        if eq d (con 1%N) then
          Some(Some(cfg PT l (add a (add n n)) (push (con 0%N) (con 1%N) r''))) else None
      else let? (d,r'') := pop r' in
        if (sample d=?0)%N then if eq d (con 0%N) then
          Some(Some(cfg PU l a (push (con 1%N) (con 1%N) r''))) else None
        else let? d' := sub d (con 1%N) in
          Some(Some(cfg PT l (add (con 2%N) a) (push d' (con 1%N) r'')))
    | []=>Some(Some(cfg PU l a (push (con 1%N) (con 1%N) []))) end
  else None
| PU => if (0<?sample a)%N then let? a' := sub a (con 1%N) in
    Some(Some(cfg PS l a' (push (con 0%N) (con 1%N) r)))
  else if eq a (con 0%N) then let? (x,l') := pop l in let? (c,r') := pop r in
    Some(Some(cfg PV l' x (push (add (con 1%N) c) (con 1%N) r'))) else None
| PV => if (sample a=?0)%N then if eq a (con 0%N) then let? (x,l') := pop l in
    Some(Some(cfg PT l' (add (con 1%N) x) r)) else None
  else if (sample a=?1)%N then if eq a (con 1%N) then Some None else None
  else let? a' := sub a (con 2%N) in
    Some(Some(cfg PU l a' (push (con 1%N) (con 1%N) r)))
end end.
Variable v:num o->nat.
Hypothesis H:laws o v.
Fixpoint expand (l:list(num o*num o)) := match l with
| []=>[] | (x,n)::l'=>repeat (v x) (v n)++expand l' end.
Definition meaning x := match x with cfg p l a r =>
 (match p with PS=>S | PT=>T | PU=>U | PV=>V end) (expand l) (v a) (expand r) end.
Lemma push_ok x n l: expand (push x n l)=repeat (v x) (v n)++expand l.
Proof.
  unfold push. destruct (eq n (con 0%N)) eqn:E.
  - apply (eq_ok _ _ H) in E. rewrite (con_ok _ _ H) in E. rewrite E. reflexivity.
  - destruct l as [|[y m] l]; [reflexivity|].
    destruct (eq x y) eqn:F; [|reflexivity].
    apply (eq_ok _ _ H) in F. cbn [expand]. rewrite (add_ok _ _ H),repeat_app,F,app_assoc. reflexivity.
Qed.
Lemma pop_ok l x l': pop l=Some(x,l') ->
  LC (expand l)=LC (v x::expand l') /\ RC (expand l)=RC (v x::expand l').
Proof.
  gen x l'. induction l as [|[y n] l IH]; intros x l' E; cbn [pop] in E.
  - inversion E; subst. cbn [expand]. rewrite (con_ok _ _ H). split; [apply Lblank|apply (Rblank [])].
  - destruct (eq n (con 0%N)) eqn:F.
    + apply (eq_ok _ _ H) in F. rewrite (con_ok _ _ H) in F.
      cbn [expand]. rewrite F. apply IH,E.
    + destruct (sub n (con 1%N)) as [k|] eqn:G; [|discriminate].
      pose proof (sub_ok _ _ H _ _ _ G) as Hk. rewrite (con_ok _ _ H) in Hk.
      destruct (eq k (con 0%N)) eqn:J; inversion E; subst x l'; cbn [expand].
      * apply (eq_ok _ _ H) in J. rewrite (con_ok _ _ H) in J.
        rewrite Hk,J. cbn. auto.
      * rewrite Hk. cbn [repeat app]. auto.
Qed.
Ltac cases50 := repeat first [solve [exact I] |
  lazymatch goal with |- match ?z with _=>_ end => lazymatch z with
  | match sub ?x ?y with _=>_ end =>
    let E:=fresh "Es" in destruct (sub x y) eqn:E; [
      let Hs:=fresh "Hs" in pose proof (sub_ok _ _ H _ _ _ E) as Hs|]
  | match div ?x ?n with _=>_ end =>
    let E:=fresh "Ed" in let q:=fresh "q" in let d:=fresh "d" in
    destruct (div x n) as [[q d]|] eqn:E; [
      let Hd:=fresh "Hd" in pose proof (div_ok _ _ H _ _ _ _ E) as Hd|]
  | match pop ?l with _=>_ end =>
    let E:=fresh "Ep" in let x:=fresh "x" in let ls:=fresh "ls" in
    destruct (pop l) as [[x ls]|] eqn:E; [
      let Hl:=fresh "Hl" in let Hr:=fresh "Hr" in destruct (pop_ok _ _ _ E) as [Hl Hr]|]
  | if eq ?x ?y then _ else _ =>
    let E:=fresh "Ee" in destruct (eq x y) eqn:E; [
      let He:=fresh "He" in pose proof (eq_ok _ _ H _ _ E) as He|]
  | if ?b then _ else _ => let E:=fresh "Eb" in destruct b eqn:E
  | match ?l with []=>_ | _::_=>_ end =>
    let d:=fresh "d" in let n:=fresh "n" in let rs:=fresh "rs" in
    destruct l as [|[d n] rs]; cbn beta iota zeta
  end end; cbn beta iota zeta].
Ltac numeric := repeat first [rewrite (con_ok _ _ H) in * | rewrite (add_ok _ _ H) in *];
  change (Pos.to_nat 1) with 1 in *; change (Pos.to_nat 2) with 2 in *;
  change (Pos.to_nat 4) with 4 in *.
Ltac tapes := cbn [meaning]; repeat rewrite push_ok;
  cbn [repeat app]; unfold S,T,U,V;
  repeat first [rewrite (con_ok _ _ H) | rewrite (add_ok _ _ H) |
    match goal with
    | E:LC (expand _) = _ |- _ => rewrite E; clear E
    | E:RC (expand _) = _ |- _ => rewrite E; clear E
    end | progress cbn [LC RC repeat app N.to_nat Pos.to_nat Pos.iter_op] ]; fold S T U V.
Lemma step_spec x: match step x with
| Some(Some y)=>meaning x -->* meaning y
| Some None=>halts tm (meaning x) | None=>True end.
Proof.
  destruct x as [p l a r],p; cbn [step]; cases50.
  all: numeric; tapes.
  all: cbn [expand]; numeric; cbn [repeat app].
  all: repeat match goal with E:v ?a = ?b |- _=>rewrite E; clear E end.
  all: try first [solve [applys_eq Sone; flia] | solve [applys_eq Sleft; flia] |
    solve [applys_eq Szero; flia] | solve [applys_eq Tzero; flia] |
    solve [applys_eq Tmix; flia] | solve [applys_eq Upos; flia] |
    solve [applys_eq Uzero; flia] | solve [applys_eq Vzero; flia] |
    solve [applys_eq Vpos; flia] | solve [applys_eq HV; flia] |
    solve [applys_eq Slefts; flia] | solve [applys_eq Trights; flia] |
    solve [applys_eq Tmixs; flia]].
  all: try (match goal with E:(if (?d =? 0)%N then true else (?d =? 2)%N)=true |- _ =>
    destruct (d =? 0)%N eqn:F; [apply N.eqb_eq in F; subst d|apply N.eqb_eq in E; subst d] end).
  all: cbn [N.to_nat]; numeric.
  all: try solve [applys_eq (Incs (v q) 0 (expand ls) (v x) (expand ls0)); unfold S; cbn [LC RC]; flia].
  all: try solve [applys_eq (Incs (v q) 1 (expand ls) (v x) (expand ls0)); unfold S; cbn [LC RC]; flia].
  all: try solve [applys_eq (Tmixs (v n) (expand l) (v a) (expand rs)); unfold T; cbn [LC RC]; flia].
  all: try solve [rewrite (Rblank []); applys_eq Tzero; flia].
Qed.
End Generic.

Definition nsub (x y:N) := if (y<=?x)%N then Some (x-y)%N else None.
Definition ndiv (x n:N) := if (n=?0)%N then None else Some ((x/n)%N,(x mod n)%N).
Definition numbers := Ops N (fun x=>x) (fun x=>x) N.add nsub ndiv N.eqb.
Lemma number_laws: laws numbers N.to_nat.
Proof.
  constructor; cbn; intros; try reflexivity.
  - apply N2Nat.inj_add.
  - unfold nsub in H. destruct (y<=?x)%N eqn:E; inversion H; subst.
    apply N.leb_le in E. rewrite <- N2Nat.inj_add. f_equal. lia.
  - unfold ndiv in H. destruct (n=?0)%N eqn:E; inversion H; subst.
    apply N.eqb_neq in E. rewrite <- N2Nat.inj_mul,<-N2Nat.inj_add.
    f_equal. pose proof (N.div_mod x n E). nia.
  - apply N.eqb_eq in H. now subst.
Qed.
Definition affine := (N*N)%type.
Definition aval (t:N) (x:affine) := N.to_nat (fst x+snd x*t).
Definition aadd (x y:affine) := (fst x+fst y,snd x+snd y)%N.
Definition asub (x y:affine) :=
  if (fst y<=?fst x)%N && (snd y<=?snd x)%N then
    Some(fst x-fst y,snd x-snd y)%N else None.
Definition adiv (x:affine) (n:N) :=
  if negb (n=?0)%N && (snd x mod n=?0)%N then
    Some((fst x/n,snd x/n)%N,(fst x mod n)%N) else None.
Definition aeq (x y:affine) := (fst x=?fst y)%N && (snd x=?snd y)%N.
Definition affines := Ops affine fst (fun x=>(x,0%N)) aadd asub adiv aeq.
Lemma affine_laws t: laws affines (aval t).
Proof.
  constructor; cbn; intros.
  - unfold aval; cbn. f_equal. lia.
  - unfold aval,aadd; cbn. rewrite <-N2Nat.inj_add. f_equal. nia.
  - unfold asub in H. destruct (fst y<=?fst x)%N eqn:E; [|discriminate].
    destruct (snd y<=?snd x)%N eqn:F; inversion H; subst.
    apply N.leb_le in E,F. unfold aval; cbn. rewrite <-N2Nat.inj_add. f_equal. nia.
  - unfold adiv in H. destruct (n=?0)%N eqn:E; [discriminate|].
    cbn in H. destruct (snd x mod n=?0)%N eqn:F; inversion H; subst.
    apply N.eqb_neq in E. apply N.eqb_eq in F.
    unfold aval; cbn. rewrite <-N2Nat.inj_mul,<-N2Nat.inj_add. f_equal.
    pose proof (N.div_mod (fst x) n E). pose proof (N.div_mod (snd x) n E). nia.
  - unfold aeq in H. destruct (fst x=?fst y)%N eqn:E; [|discriminate].
    apply N.eqb_eq in E,H. unfold aval. now rewrite E,H.
Qed.
Definition den := @meaning numbers N.to_nat.
Definition aden t := @meaning affines (aval t).
Definition Cn (n:N) := S [] (N.to_nat n) [0;1].
Definition start (n:N) : frame affine := cfg PS [] (n,1%N) [((0,0),(1,0));((1,0),(1,0))]%N.
Definition cut {o:ops} (x:frame(num o)) := match x with
| cfg PS [] a [(z,n);(u,m)] =>
  if eq z (con 0%N) && eq n (con 1%N) && eq u (con 1%N) && eq m (con 1%N)
  then Some a else None
| _=>None end.
Lemma cut_spec {o:ops} v (H:laws o v) x a:
  cut x=Some a -> meaning v x=S [] (v a) [0;1].
Proof.
  destruct x as [p l b r],p; cbn [cut]; try discriminate.
  destruct l; [|discriminate]. destruct r as [|[z n] [|[u m] r]]; try discriminate.
  destruct r; [|discriminate].
  destruct (eq z (con 0%N)) eqn:E; [|discriminate].
  destruct (eq n (con 1%N)) eqn:F; [|discriminate].
  destruct (eq u (con 1%N)) eqn:G; [|discriminate].
  destruct (eq m (con 1%N)) eqn:J; intros K; inversion K; subst.
  apply (eq_ok _ _ H) in E,F,G,J.
  rewrite (con_ok _ _ H) in E,F,G,J.
  cbn [meaning expand]. rewrite E,F,G,J. reflexivity.
Qed.
Definition amap (f:affine->affine) x := match x with cfg p l a r=>
  cfg p (map (fun '(x,n)=>(f x,f n)) l) (f a) (map (fun '(x,n)=>(f x,f n)) r) end.
Definition twice (x:affine) := (fst x,2*snd x)%N.
Lemma aval_twice t x: aval t (twice x)=aval (2*t) x.
Proof. change (N.to_nat (fst x+(2*snd x)*t)=N.to_nat (fst x+snd x*(2*t)))%N.
  f_equal. nia. Qed.
Lemma expand_twice t l:
  @expand affines (aval t) (map (fun '(x,n)=>(twice x,twice n)) l)=
  @expand affines (aval (2*t)) l.
Proof.
  induction l as [|[x n] l IH]; cbn [map expand]; [reflexivity|]. now rewrite !aval_twice,IH.
Qed.
Lemma aden_twice t x: aden t (amap twice x)=aden (2*t) x.
Proof. destruct x as [p l a r],p; cbn [aden amap meaning]; now rewrite !expand_twice,aval_twice. Qed.
(* A failed symbolic division refines the input arithmetic progression. *)
Fixpoint trace (fuel retries:nat) (ready:bool) (x:frame affine) : option(N*frame affine) :=
  match fuel with O=>None | Datatypes.S fuel=>
    if ready && match cut (o:=affines) x with Some _=>true|None=>false end then Some(1%N,x) else
    match @step affines x with
    | Some(Some y)=>trace fuel retries true y
    | Some None=>None
    | None=>match retries with O=>None | Datatypes.S retries=>
      let? (k,y) := trace fuel retries ready (amap twice x) in Some((2*k)%N,y) end
    end end.
Lemma trace_spec fuel retries ready x k y:
  trace fuel retries ready x=Some(k,y) ->
  forall t,aden (k*t) x -->* aden t y.
Proof.
  gen retries ready x k y. induction fuel; intros; [discriminate|].
  cbn [trace] in H. destruct (ready && match cut (o:=affines) x with Some _=>true|None=>false end).
  - inversion H; subst. rewrite N.mul_1_l. finish.
  - pose proof (@step_spec affines (aval (k*t)) (affine_laws (k*t)) x) as E.
    destruct (@step affines x) as [[z|]|] eqn:F; [|discriminate|].
    + eapply evstep_trans; [exact E|eapply IHfuel; eauto].
    + destruct retries; [discriminate|].
      destruct (trace fuel retries ready (amap twice x)) as [[j z]|] eqn:G; [|discriminate].
      inversion H; subst. pose proof (IHfuel _ _ _ _ _ G t) as J.
      rewrite aden_twice in J. rewrite N.mul_assoc in J. exact J.
Qed.
Record rule := Rule { base:N; stride:N; delta:N }.
Definition valid (r:rule) := forall t,
  Cn (base r+stride r*t) -->* Cn (base r+delta r+stride r*t).
Definition compile (n:N) : option rule :=
  let? (k,y) := trace 2000 60 false (start n) in
  let? (b,m) := cut (o:=affines) y in
  if (m=?k)%N && (n<?b)%N then Some(Rule n k (b-n)) else None.
Lemma compile_spec n r: compile n=Some r -> valid r.
Proof.
  unfold compile. destruct (trace 2000 60 false (start n)) as [[k y]|] eqn:E; [|discriminate].
  destruct (cut (o:=affines) y) as [[b m]|] eqn:F; [|discriminate].
  destruct (m=?k)%N eqn:G; [|discriminate]. destruct (n<?b)%N eqn:J; [|discriminate].
  intros K. inversion K; subst. apply N.eqb_eq in G. apply N.ltb_lt in J.
  intros t. pose proof (trace_spec _ _ _ _ _ _ E t) as H.
  unfold aden in H. rewrite (cut_spec _ (affine_laws t) _ _ F) in H.
  cbn [start meaning expand] in H. unfold aval in H.
  cbn [fst snd] in H. rewrite !N.mul_1_l,!N.mul_0_l,!N.add_0_r in H.
  cbn [N.to_nat repeat app] in H. unfold Cn; cbn [base stride delta].
  replace (n+(b-n)+k*t)%N with (b+m*t)%N by nia. exact H.
Qed.
Definition applies (r:rule) (n:N) :=
  (base r<=?n)%N && negb (stride r=?0)%N && ((n-base r) mod stride r=?0)%N.
Lemma applies_spec r n: applies r n=true ->
  (base r<=n)%N /\ stride r<>0%N /\ ((n-base r) mod stride r=0)%N.
Proof.
  unfold applies. destruct (base r<=?n)%N eqn:E; [|discriminate].
  destruct (stride r=?0)%N eqn:F; [discriminate|]. cbn. intro H.
  apply N.leb_le in E. apply N.eqb_neq in F. apply N.eqb_eq in H. auto.
Qed.
Lemma apply_rule r n: valid r -> applies r n=true -> Cn n -->* Cn (n+delta r).
Proof.
  intros H E. apply applies_spec in E as [E [F G]].
  specialize (H ((n-base r)/stride r)%N).
  pose proof (N.div_mod (n-base r) (stride r) F) as J.
  replace (base r+stride r*((n-base r)/stride r))%N with n in H by nia.
  replace (base r+delta r+stride r*((n-base r)/stride r))%N with (n+delta r)%N in H by nia.
  exact H.
Qed.
Definition compatible r n m := applies r n && (m mod stride r=?0)%N.
Lemma lift_rule r n m: valid r -> compatible r n m=true -> valid (Rule n m (delta r)).
Proof.
  unfold compatible. destruct (applies r n) eqn:E; [|discriminate]. intros H F.
  apply N.eqb_eq in F. apply applies_spec in E as [E [G J]].
  pose proof (N.div_mod (n-base r) (stride r) G) as A.
  pose proof (N.div_mod m (stride r) G) as B.
  intros t. specialize (H (((n-base r)/stride r)+(m/stride r)*t)%N).
  cbn [base stride delta].
  replace (n+m*t)%N with (base r+stride r*((n-base r)/stride r+(m/stride r)*t))%N by nia.
  replace (n+delta r+m*t)%N with
    (base r+delta r+stride r*((n-base r)/stride r+(m/stride r)*t))%N by nia.
  exact H.
Qed.
Definition join n r s := let m:=N.max (stride r) (stride s) in
  if compatible r n m && compatible s (n+delta r)%N m then
    Some (Rule n m (delta r+delta s)) else None.
Lemma join_spec n r s u: valid r -> valid s -> join n r s=Some u -> valid u.
Proof.
  intros H J. unfold join.
  destruct (compatible r n (N.max (stride r) (stride s))) eqn:E; [|discriminate].
  destruct (compatible s (n+delta r) (N.max (stride r) (stride s))) eqn:F; [|discriminate].
  intro G; inversion G; subst. apply (lift_rule _ _ _ H) in E. apply (lift_rule _ _ _ J) in F.
  intro t. specialize (E t). specialize (F t). cbn [base stride delta] in *.
  replace (n+(delta r+delta s)+N.max (stride r) (stride s)*t)%N with
    (n+delta r+delta s+N.max (stride r) (stride s)*t)%N by lia.
  eapply evstep_trans; eauto.
Qed.
Definition cache := list(N*PositiveMap.t rule).
Definition key n m := N.succ_pos (n mod m).
Fixpoint lookup (n:N) (c:cache) := match c with
| []=>None | (m,t)::c=>match PositiveMap.find (key n m) t with
  | Some r=>if applies r n then Some r else lookup n c | None=>lookup n c end end.
Fixpoint store (r:rule) (c:cache) := match c with
| []=>[(stride r,PositiveMap.add (key (base r) (stride r)) r (PositiveMap.empty rule))]
| (m,t)::cs=>if (stride r=?m)%N then
  (m,PositiveMap.add (key (base r) m) r t)::cs
  else if (m<?stride r)%N then
    (stride r,PositiveMap.add (key (base r) (stride r)) r (PositiveMap.empty rule))::c
  else (m,t)::store r cs end.
Definition cache_ok (c:cache) := Forall (fun '(_,t)=>forall k r,
  PositiveMap.find k t=Some r -> valid r) c.
Lemma lookup_spec n c r: cache_ok c -> lookup n c=Some r -> valid r /\ applies r n=true.
Proof.
  intros H. induction H as [|[m t] c H Hc IH]; cbn [lookup]; [discriminate|].
  destruct (PositiveMap.find (key n m) t) as [s|] eqn:E; [|apply IH].
  destruct (applies s n) eqn:F; [|apply IH]. intro G; inversion G; subst. split; [eapply H; eauto|exact F].
Qed.
Lemma store_spec r c: valid r -> cache_ok c -> cache_ok (store r c).
Proof.
  intros H J. unfold cache_ok in *. induction J as [|[m t] c J Hc IH]; cbn [store].
  - constructor; [|constructor]. intros k s E.
    rewrite PositiveMapAdditionalFacts.gsspec in E. destruct (PositiveMap.E.eq_dec _ _);
      [inversion E; subst; exact H|rewrite PositiveMap.gempty in E; discriminate].
  - destruct (stride r=?m)%N; [|destruct (m<?stride r)%N].
    + constructor; [|exact Hc]. intros k s E.
      rewrite PositiveMapAdditionalFacts.gsspec in E. destruct (PositiveMap.E.eq_dec _ _);
        [inversion E; subst; exact H|eapply J; eauto].
    + constructor; [|constructor; assumption]. intros k s E.
      rewrite PositiveMapAdditionalFacts.gsspec in E. destruct (PositiveMap.E.eq_dec _ _);
        [inversion E; subst; exact H|rewrite PositiveMap.gempty in E; discriminate].
    + constructor; assumption.
Qed.
Fixpoint chain fuel c n r := match fuel with O=>r | Datatypes.S fuel=>
  match lookup (n+delta r)%N c with Some s=>
    match join n r s with Some u=>chain fuel c n u|None=>r end | None=>r end end.
Lemma chain_spec fuel c n r: cache_ok c -> valid r -> valid (chain fuel c n r).
Proof.
  intros H. gen r. induction fuel; intros; cbn [chain]; [assumption|].
  destruct (lookup (n+delta r) c) as [s|] eqn:E; [|assumption].
  destruct (join n r s) as [u|] eqn:F; [|assumption].
  apply IHfuel. apply (join_spec n r s u H0); [exact (proj1 (lookup_spec _ _ _ H E))|exact F].
Qed.
Definition get n c := match lookup n c with Some r=>Some r | None=>compile n end.
Definition advance limit n c := let? r := get n c in
  let s:=chain limit c n r in
  if applies s n then Some(s,store s c) else None.
Local Opaque chain compile.
Lemma advance_spec limit n c r d: cache_ok c -> advance limit n c=Some(r,d) ->
  cache_ok d /\ Cn n -->* Cn (n+delta r).
Proof.
  intros H. unfold advance,get. destruct (lookup n c) as [s|] eqn:E.
  - pose proof (proj1 (lookup_spec _ _ _ H E)) as J.
    destruct (applies (chain limit c n s) n) eqn:F; [|discriminate].
    intro G; inversion G; subst. pose proof (chain_spec limit c n s H J) as K.
    split; [apply store_spec; assumption|apply apply_rule; assumption].
  - destruct (compile n) as [s|] eqn:F; [|discriminate].
    pose proof (compile_spec _ _ F) as J.
    destruct (applies (chain limit c n s) n) eqn:G; [|discriminate].
    intro K; inversion K; subst. pose proof (chain_spec limit c n s H J) as L.
    split; [apply store_spec; assumption|apply apply_rule; assumption].
Qed.
Definition normal (n:N) : frame N := cfg PS [] n [(0,1);(1,1)]%N.
Definition fallback (x:frame N) c : (frame N*cache)+bool :=
  match @step numbers x with Some(Some y)=>inl(y,c) | Some None=>inr true | None=>inr false end.
Definition tick (s:frame N*cache) : (frame N*cache)+bool := let '(x,c):=s in
  match cut (o:=numbers) x with Some n=>
    match advance 4096 n c with Some(r,d)=>inl(normal (n+delta r)%N,d) | None=>fallback x c end
  | None=>fallback x c end.
Definition initial : frame N := cfg PT [] 1%N [].
Definition check fuel := match N_iter_until tick (inl(initial,[])) fuel with
  | inr b=>b | _=>false end.
Lemma tick_spec x c: cache_ok c ->
  match tick (x,c) with
  | inl(y,d)=>cache_ok d /\ den x -->* den y
  | inr b=>b=true -> halts tm (den x) end.
Proof.
  intro H. unfold tick. destruct (cut (o:=numbers) x) as [n|] eqn:E.
  - destruct (advance 4096 n c) as [[r d]|] eqn:F.
    + apply (advance_spec _ _ _ _ _ H) in F as [F G]. split; [exact F|].
      unfold den. rewrite (cut_spec _ number_laws _ _ E). exact G.
    + unfold fallback. pose proof (@step_spec numbers N.to_nat number_laws x) as J.
      destruct (@step numbers x) as [[y|]|]; cbn; auto; discriminate.
  - unfold fallback. pose proof (@step_spec numbers N.to_nat number_laws x) as J.
    destruct (@step numbers x) as [[y|]|]; cbn; auto; discriminate.
Qed.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof.
  unfold check. intro H.
  assert (match N_iter_until tick (inl(initial,[])) fuel with
    | inl(x,c)=>cache_ok c /\ c0 -->* den x | inr b=>b=true -> halts tm c0 end) as R.
  { apply N_iter_until_spec.
    - intros [x c] [J K]. pose proof (tick_spec x c J) as E.
      destruct (tick (x,c)) as [[y d]|b].
      + split; [exact (proj1 E)|eapply evstep_trans; [exact K|exact (proj2 E)]].
      + intro F. eapply halts_evstep; [apply E,F|exact K].
    - split; [constructor|apply init]. }
  destruct (N_iter_until tick (inl(initial,[])) fuel) as [[x c]|b]; [discriminate|apply R,H].
Qed.
Local Transparent chain compile.
End Kernel.
Theorem halt: halts tm c0.
Proof. apply (Kernel.check_spec 100000%N). native_check_eq. Qed.
End TM50.
