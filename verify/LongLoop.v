From BusyCoq Require Import Individual62.

Require Import ZifyN Lia.
Require Import ZArith.
Require Import List.
Import Eqb.

Open Scope N.

Definition Nsubge(a b:N) :=
if b <=? a then Some (a-b) else None.

Lemma Nsubge_spec a b c:
  Nsubge a b = Some c ->
  a=c+b.
Proof.
  unfold Nsubge.
  intros.
  destruct (N.leb_spec b a);
  inverts H; lia.
Qed.

Definition Ndiv(a b:N) :=
if a mod b =? 0 then Some (a/b) else None.

Lemma Ndiv_spec a b c:
  Ndiv a b = Some c ->
  a=c*b.
Proof.
  unfold Ndiv.
  intros.
  destruct (N.eqb_spec (a mod b) 0);
  inverts H.
  pose proof (N.div_mod a b); lia.
Qed.

Definition N_OS(n:N) :=
match n with
| N0 => None
| _ => Some (N.pred n)
end.

Lemma N_OS_spec n:
(match N_OS n with
| None => n=N0
| Some n0 => n=1+n0
end)%N.
Proof.
  unfold N_OS.
  destruct n; lia.
Qed.

Definition if_None {A} (a:option A) b :=
match a with
| None => b tt
| _ => a
end.

Notation "a ||| b" := (if_None a b) (at level 30, right associativity).

Definition b2o(b:bool) := if b then Some tt else None.

Notation seg := (list Sym).
Notation head := (DH0*DH0)%type.
Notation vseg := (list seg + list seg)%type.
Notation vside := (list vseg * seg)%type.

Ltac ec := econstructor.
Ltac eex := repeat eexists.

Ltac des_if H :=
  cbn[if_None] in H;
  cbn[if_Some] in H;
  let E:=fresh "E" in
  match type of H with
  | ?a ||| _ = _ =>
    destruct a eqn:E
  | ?a &&& _ = _ =>
    destruct a eqn:E
  end.

Ltac des_if' H := des_if H; [|inverts H].


Section sec.
Hypothesis f2:seg->head->option(N*N*head).
Hypothesis f1:seg->head->option((list seg)*(list head)).
Hypothesis f0:seg->head->option((list seg)*seg).
Hypothesis tm:TM.

Definition to_side '(ws,w) :=
  concat ws*>w*>0inf.

Hypothesis f2_spec:
  forall w h a0 a1 h',
  f2 w h = Some (a0,a1,h') ->
  segRLs tm ([h]^^(N.to_nat (2^a0))) ([h']^^(N.to_nat (2^a1))) w w.

Hypothesis f1_spec:
  forall w h ws hs,
  f1 w h = Some (ws,hs) ->
  segRLs tm [h] hs w (concat ws).

Hypothesis f0_spec:
  forall w h w',
  f0 w h = Some w' ->
  sideRLs tm [h] (w*>0inf) (to_side w').

Inductive Nmap :=
| Nmap_mk(a0 a1 b0 b1:N)
| Nmap_c(b0 b1:N).

Inductive Nmap_apply: Nmap->N->N->Prop :=
| Nmap_apply_mk(a0 a1 b0 b1 n:N): Nmap_apply (Nmap_mk a0 a1 b0 b1) (2^a0*n+b0) (2^a1*n+b1)
| Nmap_apply_c b0 b1: Nmap_apply (Nmap_c b0 b1) b0 b1.

Inductive vN :=
| vN_v(id:N)(mp:Nmap)
| vN_c(c:N).

Definition Nmap_add x k :=
match x with
| Nmap_mk a0 a1 b0 b1 => Nmap_mk a0 a1 b0 (b1+k)
| Nmap_c b0 b1 => Nmap_c b0 (b1+k)
end.

Definition vN_add a b :=
match a,b with
| vN_c a,vN_c b => Some (vN_c (a+b))
| vN_c a,vN_v id mp => Some (vN_v id (Nmap_add mp a))
| vN_v id mp,vN_c b => Some (vN_v id (Nmap_add mp b))
| _,_ => None
end.

Inductive vhead :=
| vhead_mk(h:head)(n:N)(n':vN)
.

Section vhead_sec.
Hypothesis ctx:N->N.
Inductive vN_eval: vN->N->Prop :=
| vN_eval_v id mp n:
  Nmap_apply mp (ctx id) n ->
  vN_eval (vN_v id mp) n
| vN_eval_c c:
  vN_eval (vN_c c) c.

Inductive vhead_eval: vhead -> list head -> Prop :=
| vhead_eval_mk h n n' n'0:
  vN_eval n' n'0 ->
  vhead_eval (vhead_mk h n n') ([h]^^(N.to_nat n'0)).

Inductive vheads_eval: list vhead -> list head -> Prop :=
| vheads_eval_O: vheads_eval [] []
| vheads_eval_S h t h' t':
  vhead_eval h h' ->
  vheads_eval t t' ->
  vheads_eval (h::t) (h'++t').

Inductive Nmap_applys: Nmap->N->N->N->Prop :=
| Nmap_applys_O mp n: Nmap_applys mp n n 0
| Nmap_applys_S mp n n0 n1 k:
  Nmap_apply mp n n0 ->
  Nmap_applys mp n0 n1 k ->
  Nmap_applys mp n n1 (1+k).

Inductive vN_evaln: vN->N->N->Prop :=
| vN_evaln_v id mp n i:
  Nmap_applys mp (ctx id) n i ->
  vN_evaln (vN_v id mp) n i
| vN_evaln_c c i:
  vN_evaln (vN_c c) c i.

Inductive vhead_evaln: vhead -> list head -> N -> Prop :=
| vhead_evaln_mk h n n' n'0 i:
  vN_evaln n' n'0 i ->
  vhead_evaln (vhead_mk h n n') ([h]^^(N.to_nat n'0)) i.

Inductive vheads_evaln: list vhead -> list head -> N -> Prop :=
| vheads_evaln_O n: vheads_evaln [] [] n
| vheads_evaln_S h t h' t' n:
  vhead_evaln h h' n ->
  vheads_evaln t t' n ->
  vheads_evaln (h::t) (h'++t') n.

Definition vhead_add a b :=
match a,b with
| vhead_mk h n n',vhead_mk h0 n0 n'0 =>
  b2o (eqb h h0) &&& (fun _ =>
  vN_add n' n'0 &&& (fun n'1 =>
  Some (vhead_mk h (n+n0) n'1)))
end.

Definition vN_is0' n :=
match n with
| vN_c c => b2o (c=?0)
| _ => None
end.

Definition vN_is0 n :=
match n with
| vN_c c => b2o (c=?0)
| vN_v _ (Nmap_c b0 b1) => b2o (b1=?0)
| _ => None
end.

Definition vhead_is0' x :=
match x with
| vhead_mk h n n' => vN_is0' n'
end.

Fixpoint vheads_simpl(ls ls0:list vhead) :=
match ls with
| h::t =>
  if vhead_is0' h then vheads_simpl t ls0 else
  match vheads_simpl t ls0 with
  | [] => [h]
  | h0::t0 =>
    match vhead_add h h0 with
    | Some h1 => h1::t0
    | None => h::h0::t0
    end
  end
| [] => ls0
end.

Definition Nmap_sub x k :=
match x with
| Nmap_mk a0 a1 b0 b1 =>
  let c:=(k-b1+(2^a1-1))/2^a1 in
  Some (Nmap_mk a0 a1 (b0+c*2^a0) (b1+c*2^a1-k))
| Nmap_c b0 b1 =>
  Nsubge b1 k &&& (fun b2 =>
  Some (Nmap_c b0 b2))
end.

Definition Nmap_divpow2 x k :=
match x with
| Nmap_mk a0 a1 b0 b1 =>
  let pk:=2^k in
  Ndiv b1 pk &&& (fun b1 => Some (Nmap_mk (a0+(k-a1)) (a1-k) b0 b1))
| Nmap_c b0 b1 =>
  Ndiv b1 (2^k) &&& (fun b1 => Some (Nmap_c b0 b1))
end.

Definition Nmap_mulpow2 x k :=
match x with
| Nmap_mk a0 a1 b0 b1 => Some (Nmap_mk a0 (a1+k) b0 (b1*2^k))
| Nmap_c b0 b1 => Some (Nmap_c b0 (b1*2^k))
end.

Definition Nmap_to_c x k :=
match x with
| Nmap_mk a0 a1 b0 b1 =>
  Nsubge k b1 &&& (fun k =>
  Ndiv k (2^a1) &&& (fun k =>
  Some (Nmap_c (2^a0*k+b0) (2^a1*k+b1))))
| Nmap_c b0 b1 =>
  if b1=?k then Some x else None
end.

Definition vN_to_c x k :=
match x with
| vN_v id mp => Nmap_to_c mp k &&& (fun mp => Some (vN_v id mp))
| vN_c c => if c=?k then Some x else None
end.

Definition vN_subdivmulpow2 x m a0 a1 :=
match x with
| vN_v id mp =>
  Nmap_sub mp m &&& (fun mp =>
  Nmap_divpow2 mp a0 &&& (fun mp =>
  Nmap_mulpow2 mp a1 &&& (fun mp =>
  Some (vN_v id mp))))
| vN_c c =>
  Nsubge c m &&& (fun c =>
  Ndiv c (2^a0) &&& (fun c =>
  Some (vN_c (c*2^a1))))
end.

Definition vhead_c h n := vhead_mk h n (vN_c n).

Lemma vN_is0'_spec n u:
  vN_is0' n = Some u ->
  vN_eval n 0.
Proof.
  unfold vN_is0'.
  intros.
  destruct n.
  1: inverts H.
  destruct (N.eqb_spec c 0).
  2: inverts H.
  subst.
  ec.
Qed.

Lemma vN_is0_spec n u:
  vN_is0 n = Some u ->
  forall nv,
  vN_eval n nv ->
  nv=0.
Proof.
  unfold vN_is0.
  intros.
  destruct n.
  1: {
    destruct mp.
    1: congruence.
    destruct (N.eqb_spec b1 0).
    2: inverts H.
    subst.
    inverts H0.
    inverts H4.
    ec.
  }
  destruct (N.eqb_spec c 0).
  2: inverts H.
  subst.
  inverts H0.
  ec.
Qed.

Definition vN_sub1 n n' :=
vN_subdivmulpow2 n' 1 0 0 &&& (fun n' =>
if n=?0 then vN_to_c n' 0 else Some n').

Fixpoint segRLs_rec(hs:list vhead)(ws:list seg)(flag:bool)(T:nat):option((list vhead)*(list seg)) :=
match T with
| O => None
| S T =>
match ws with
| [] => Some (hs,[])
| w::ws =>
match hs with
| [] => Some ([],w::ws)
| (vhead_mk h n n')::hs =>
  (b2o flag &&& (fun _ =>
  N_OS n &&& (fun _ =>
  f2 w h &&& (fun '(a0,a1,h') =>
  let pa0:=2^a0 in
  let n1:=(n/pa0)*2^a1 in
  let n2:=n mod pa0 in
  vN_subdivmulpow2 n' n2 a0 a1 &&& (fun n' =>
  segRLs_rec [vhead_mk h' n1 n'] ws true T &&& (fun '(hs',ws') =>
  segRLs_rec ((vhead_c h n2)::hs) (w::ws') false T &&& (fun '(hs'0,ws'0) =>
  Some (vheads_simpl hs' hs'0,ws'0)
  ))))))) ||| (fun _ =>
  match N_OS n with
  | Some n =>
    vN_sub1 n n' &&& (fun n' =>
    f1 w h &&& (fun '(w',h') =>
    segRLs_rec (vheads_simpl (map (fun h => vhead_c h 1) h') []) ws true T &&& (fun '(hs',ws') =>
    segRLs_rec ((vhead_mk h n n')::hs) (w'++ws') flag T &&& (fun '(hs'0,ws'0) =>
    Some (vheads_simpl hs' hs'0,ws'0)
    ))))
  | None =>
    vN_to_c n' 0 &&& (fun n' =>
    segRLs_rec hs (w::ws) true T &&& (fun '(hs',ws') =>
    Some (vheads_simpl [vhead_mk h 0 n'] hs',ws')
    ))
  end)
end
end
end.

Fixpoint segRLs_rec' hs ws T :=
match ws with
| [] => Some (hs,[])
| w::ws =>
  segRLs_rec hs [w] true T &&& (fun '(hs',ws') =>
  segRLs_rec' hs' ws T &&& (fun '(hs'0,ws'0) =>
  Some (hs'0,ws'++ws'0)))
end.

Fixpoint sideRLs_rec hs ws w T :=
match T with
| O => None
| S T =>
  segRLs_rec' hs ws T &&& (fun '(hs,ws0) =>
  match hs with
  | [] => Some (ws0,w)
  | vhead_mk h n n'::hs =>
    match N_OS n with
    | Some n =>
      vN_sub1 n n' &&& (fun n' =>
      f0 w h &&& (fun '(ws1,w') =>
      sideRLs_rec (vhead_mk h n n'::hs) ws1 w' T &&& (fun '(ws',w') =>
      Some (ws0++ws',w'))))
    | None =>
      vN_is0' n' &&& (fun _ =>
      sideRLs_rec hs [] w T &&& (fun '(ws',w') =>
      Some (ws0++ws',w')))
    end
  end)
end.

Lemma Nmap_sub_spec mp k mp':
  Nmap_sub mp k = Some mp' ->
  forall n n',
  Nmap_apply mp' n n' ->
  Nmap_apply mp n (n'+k).
Proof.
  unfold Nmap_sub.
  intros.
  destruct mp.
  - inverts H.
    inverts H0.
    remember ((k-b1+(2^a1-1))/2^a1) as c.
    applys_eq (Nmap_apply_mk a0 a1 b0 b1 (n0+c)); lia.
  - des_if' H.
    inverts H.
    apply Nsubge_spec in E.
    subst.
    inverts H0.
    ec.
Qed.

Lemma Nmap_divpow2_spec mp k mp':
  Nmap_divpow2 mp k = Some mp' ->
  forall n n',
  Nmap_apply mp' n n' ->
  Nmap_apply mp n (n'*2^k).
Proof.
  unfold Nmap_divpow2.
  intros.
  destruct mp.
  - des_if H; inverts H.
    apply Ndiv_spec in E.
    subst b1.
    inverts H0.
    applys_eq (Nmap_apply_mk a0 a1 b0 (n0*2^k) (2^(k-a1)*n1)).
    1: rewrite N.pow_add_r; lia.
    rewrite N.mul_add_distr_r.
    f_equal.
    rewrite N.mul_shuffle0.
    rewrite N.mul_assoc.
    f_equal.
    do 2 rewrite <-N.pow_add_r.
    f_equal.
    lia.
  - des_if H; inverts H.
    apply Ndiv_spec in E.
    subst b1.
    inverts H0.
    ec.
Qed.

Lemma Nmap_mulpow2_spec mp k mp':
  Nmap_mulpow2 mp k = Some mp' ->
  forall n n',
  Nmap_apply mp' n n' ->
  exists n'0,
  Nmap_apply mp n n'0 /\
  n'=n'0*2^k.
Proof.
  unfold Nmap_mulpow2.
  intros.
  destruct mp.
  - inverts H.
    inverts H0.
    eexists (2^a1*n0+b1); split.
    2: rewrite N.pow_add_r; lia.
    constructor.
  - inverts H.
    inverts H0.
    eexists; split; ec.
Qed.

Lemma vN_subdivmulpow2_spec x m a0 a1 x':
  vN_subdivmulpow2 x m a0 a1 = Some x' ->
  forall x'v,
  vN_eval x' x'v ->
  exists xv,
  vN_eval x xv /\
  exists v,
  xv = m+v*2^a0 /\
  x'v = v*2^a1.
Proof.
  unfold vN_subdivmulpow2.
  intros.
  destruct x.
  - do 3 des_if' H.
    inverts H.
    inverts H0.
    eapply Nmap_mulpow2_spec in E1.
    2: eauto 1.
    destruct E1 as [n'0 [E1 E1a]].
    subst x'v.
    eapply Nmap_divpow2_spec in E0.
    2: eauto 1.
    eapply Nmap_sub_spec in E.
    2: eauto 1.
    eexists; split.
    1: ec; eauto 1.
    eexists n'0; lia.
  - do 2 des_if' H.
    inverts H.
    apply Nsubge_spec in E.
    apply Ndiv_spec in E0.
    subst c n.
    inverts H0.
    eexists; split.
    1: ec.
    eexists n0; lia.
Qed.

Lemma Nmap_to_c_spec mp k mp':
  Nmap_to_c mp k = Some mp' ->
  forall n n',
  Nmap_apply mp' n n' ->
  Nmap_apply mp n k /\ k=n'.
Proof.
  unfold Nmap_to_c.
  intros.
  destruct mp.
  - do 2 des_if' H.
    inverts H.
    apply Nsubge_spec in E.
    apply Ndiv_spec in E0.
    subst.
    inverts H0.
    rewrite (N.mul_comm n1).
    ec; ec.
  - destruct (N.eqb_spec b1 k); [subst|congruence].
    inverts H.
    inverts H0.
    ec; ec.
Qed.

Lemma vN_to_c_spec x n x':
  vN_to_c x n = Some x' ->
  forall x'v,
  vN_eval x' x'v ->
  vN_eval x n /\ n=x'v.
Proof.
  unfold vN_to_c.
  intros.
  destruct x.
  - des_if' H; inverts H.
    inverts H0.
    eapply Nmap_to_c_spec in E.
    2: eauto 1.
    destruct E as [Ea Eb].
    subst.
    ec; ec; trivial.
  - destruct (N.eqb_spec c n); [subst|congruence].
    inverts H.
    inverts H0.
    repeat ec.
Qed.

Lemma vN_sub1_spec n x x':
  vN_sub1 n x = Some x' ->
  forall x'v,
  vN_eval x' x'v ->
  vN_eval x (1+x'v).
Proof.
  unfold vN_sub1.
  intros.
  des_if' H.
  destruct (N.eqb_spec n 0).
  - inverts H.
    subst.
    eapply vN_to_c_spec in H2.
    2: eauto 1.
    destruct H2 as [H2 H2a]; subst.
    eapply vN_subdivmulpow2_spec in E.
    2: eauto 1.
    destruct E as [xv [Ea [v0 [Eb Ec]]]].
    subst.
    applys_eq Ea; lia.
  - inverts H.
    eapply vN_subdivmulpow2_spec in E.
    2: eauto 1.
    destruct E as [xv [Ea [v [Eb Ec]]]].
    subst.
    eauto 1.
Qed.

Lemma Nmap_add_spec mp k:
  let mp':=Nmap_add mp k in
  forall n n',
  Nmap_apply mp' n n' ->
  exists n'0,
  Nmap_apply mp n n'0 /\
  n'=n'0+k.
Proof.
  unfold Nmap_add.
  intros.
  destruct mp.
  - inverts H.
    eexists (2^a1*n0+b1); split.
    1: ec.
    lia.
  - inverts H.
    eexists; split; ec.
Qed.

Lemma vN_add_spec a b c:
  vN_add a b = Some c ->
  forall cv,
  vN_eval c cv ->
  exists av bv,
  vN_eval a av /\
  vN_eval b bv /\
  cv=av+bv.
Proof.
  unfold vN_add.
  intros.
  destruct a,b; inverts H.
  - inverts H0.
    apply Nmap_add_spec in H3.
    destruct H3 as [n'0 [I1 I2]].
    subst cv.
    eex.
    + ec; eauto 1.
    + ec.
  - inverts H0.
    apply Nmap_add_spec in H3.
    destruct H3 as [n'0 [I1 I2]].
    subst cv.
    eexists c1,n'0.
    eex.
    + ec.
    + ec; eauto 1.
    + lia.
  - inverts H0.
    eex; ec.
Qed.

Lemma vhead_add_spec a b c:
  vhead_add a b = Some c ->
  forall cv,
  vhead_eval c cv ->
  exists av bv,
  vhead_eval a av /\
  vhead_eval b bv /\
  cv=av++bv.
Proof.
  unfold vhead_add.
  intros.
  destruct a,b.
  des_if' H.
  des_if' H.
  inverts H.
  destruct (eqb_spec h h0); inverts E; subst.
  inverts H0.
  eapply vN_add_spec in E0.
  2: eauto 1.
  destruct E0 as [av [bv [I1 [I2 I3]]]].
  subst n'2.
  eex.
  1,2: eauto 1.
  rewrite Nnat.N2Nat.inj_add,lpow_add.
  reflexivity.
Qed.

Lemma vheads_simpl_spec ls ls0 lsv:
  vheads_eval (vheads_simpl ls ls0) lsv ->
  vheads_eval (ls++ls0) lsv.
Proof.
  gen ls0 lsv.
  induction ls; cbn[vheads_simpl]; intros.
  - apply H.
  - destruct (vhead_is0' a) eqn:E'.
    1:{
      destruct a.
      inverts E'.
      eapply vN_is0'_spec in H1.
      eapply IHls in H.
      change lsv with ([]++lsv).
      ec.
      2: eauto 1.
      eapply vhead_eval_mk in H1.
      eauto 1.
    }
    destruct (vheads_simpl ls ls0) as [|h1 t1] eqn:E.
    + epose proof (IHls _ _) as IHls.
      rewrite E in IHls.
      unshelve epose proof (IHls _) as IHls.
      1: ec.
      inverts H.
      inverts H4.
      ec; eauto 1.
    + destruct (vhead_add a h1) eqn:E0.
      * inverts H.
        eapply vhead_add_spec in E0.
        2: eauto 1.
        destruct E0 as [av [bv [I1 [I2 I3]]]].
        subst h'.
        epose proof (IHls _ _) as IHls.
        rewrite E in IHls.
        unshelve epose proof (IHls _) as IHls.
        1: ec; eauto 1.
        rewrite <-app_assoc.
        ec; eauto 1.
      * inverts H.
        epose proof (IHls _ _) as IHls.
        rewrite E in IHls.
        unshelve epose proof (IHls _) as IHls.
        1: eauto 1.
        ec; eauto 1.
Qed.

Lemma vheads_eval_split a b cv:
  vheads_eval (a++b) cv ->
  exists av bv,
  vheads_eval a av /\
  vheads_eval b bv /\
  cv=av++bv.
Proof.
  gen b cv.
  induction a; intros.
  - eex.
    1: ec.
    1: eauto 1.
    1: eauto 1.
  - inverts H.
    eapply IHa in H4.
    destruct H4 as [av [bv [I1 [I2 I3]]]].
    subst.
    eexists _,_; split.
    1: ec; eauto 1.
    split.
    1: eauto 1.
    apply app_assoc.
Qed.

Lemma vheads_c_spec h hv:
  vheads_eval (map (fun h : head => vhead_c h 1) h) hv ->
  hv = h.
Proof.
  gen hv.
  induction h; intros.
  - inverts H; trivial.
  - inverts H.
    apply IHh in H4.
    inverts H2.
    inverts H5.
    subst; trivial.
Qed.

Local Opaque vheads_simpl.

Lemma segRLs_rec_spec hs ws flag T hs' ws':
  segRLs_rec hs ws flag T = Some (hs',ws') ->
  forall hs'v,
  vheads_eval hs' hs'v ->
  exists hsv,
  vheads_eval hs hsv /\
  segRLs tm hsv hs'v (concat ws) (concat ws').
Proof.
  gen hs ws flag hs' ws'.
  induction T; intros.
  1: inverts H.
  cbn[segRLs_rec] in H.
  destruct ws as [|w ws].
  { inverts H.
    eexists; split.
    1: apply H0.
    apply segRLs_nil. }
  destruct hs as [|[h n n'] hs].
  { inverts H.
    inverts H0.
    eexists; split; constructor. }
  des_if H.
  {
    inverts H.
    do 2 des_if' E.
    clear E1.
    des_if' E.
    destruct p as [[a0 a1] h'].
    do 2 des_if' E.
    destruct p as [hs'0 ws'0].
    des_if' E.
    destruct p as [hs'1 ws'1].
    inverts E.
    eapply f2_spec in E1.
    eapply vheads_simpl_spec in H0.
    eapply vheads_eval_split in H0.
    destruct H0 as [av [bv [I1 [I2 I3]]]].
    subst.
    eapply IHT in E4.
    2: eauto 1.
    destruct E4 as [hs'1v [E4a E4b]].
    eapply IHT in E3.
    2: eauto 1.
    destruct E3 as [hsv [E3a E3b]].
    inverts E4a.
    inverts E3a.
    inverts H5.
    inverts H2.
    eapply vN_subdivmulpow2_spec in E2.
    2: eauto 1.
    destruct E2 as [xv [E2a [v0 [E2b E2c]]]].
    subst.
    eexists; split.
    - ec.
      2: eauto 1.
      ec; eauto 1.
    - rewrite N.add_comm.
      rewrite Nnat.N2Nat.inj_add,lpow_add,<-app_assoc.
      rewrite app_nil_r in E3b.
      eapply segRLs_trans.
      + cbn[concat].
        eapply segRLs_concat.
        2: eauto 1.
        do 2 rewrite Nnat.N2Nat.inj_mul.
        do 2 rewrite lpow_mul.
        eapply segRLs_wall''.
        eauto 1.
      + inverts H1.
        inverts H5.
        eauto 1.
  }
  clear E.
  {
    cbn in H.
    epose proof (N_OS_spec n) as E.
    destruct (N_OS n) as [n0|]; subst n.
    { 
      do 2 des_if' H.
      destruct p as [w' h'].
      des_if' H.
      destruct p as [hs'0 ws'0].
      des_if' H.
      destruct p as [hs'1 ws'1].
      inverts H.
      eapply vheads_simpl_spec in H0.
      eapply vheads_eval_split in H0.
      destruct H0 as [av [bv [I1 [I2 I3]]]].
      subst.
      eapply IHT in E2.
      2: eauto 1.
      destruct E2 as [hsv [E2a E2b]].
      eapply IHT in E1.
      2: eauto 1.
      destruct E1 as [hsv0 [E1a E1b]].
      eapply f1_spec in E0.
      inverts E2a.
      inverts H1.
      eapply vN_sub1_spec in E.
      2: eauto 1.
      eapply vheads_simpl_spec in E1a.
      rewrite app_nil_r in E1a.
      apply vheads_c_spec in E1a.
      subst hsv0.
      eexists; split.
      - ec.
        2: eauto 1.
        ec; eauto 1.
      - rewrite Nnat.N2Nat.inj_add,lpow_add,<-app_assoc.
        eapply segRLs_trans.
        + cbn[concat].
          eapply segRLs_concat; eauto 1.
        + rewrite concat_app in E2b.
          eauto 1. }
    {
      des_if' H.
      des_if' H.
      destruct p as [hs'0 ws'0].
      inverts H.
      eapply vheads_simpl_spec in H0.
      inverts H0.
      inverts H2.
      eapply IHT in E0.
      2: eauto 1.
      destruct E0 as [hsv [I1 I2]].
      eapply vN_to_c_spec in E.
      2: eauto 1.
      destruct E as [E Ea]; subst.
      eexists; split.
      - ec.
        2: eauto 1.
        ec; eauto 1.
      - eauto 1.
    }
  }
Qed.

Lemma segRLs_rec'_spec hs ws T hs' ws':
  segRLs_rec' hs ws T = Some (hs',ws') ->
  forall hs'v,
  vheads_eval hs' hs'v ->
  exists hsv,
  vheads_eval hs hsv /\
  segRLs tm hsv hs'v (concat ws) (concat ws').
Proof.
  gen hs T hs' ws'.
  induction ws; intros.
  - inverts H.
    eexists; split.
    1: apply H0.
    apply segRLs_nil.
  - cbn[segRLs_rec'] in H.
    des_if' H.
    destruct p as [hs'0 ws'0].
    des_if' H.
    destruct p as [hs'1 ws'1].
    inverts H.
    eapply IHws in E0.
    2: eauto 1.
    destruct E0 as [hsv [E0a E0b]].
    eapply segRLs_rec_spec in E.
    2: eauto 1.
    destruct E as [hsv0 [Ea Eb]].
    eexists; split.
    + eauto 1.
    + cbn[concat] in *.
      rewrite app_nil_r in Eb.
      rewrite concat_app.
      eapply segRLs_concat; eauto 1.
Qed.

Lemma sideRLs_rec_spec hs ws w T ws':
  sideRLs_rec hs ws w T = Some ws' ->
  exists hs',
  vheads_eval hs hs' /\
  sideRLs tm hs' (to_side (ws,w)) (to_side ws').
Proof.
  gen hs ws w ws'.
  induction T; intros.
  1: inverts H.
  cbn[sideRLs_rec] in H.
  des_if' H.
  destruct p as [hs0 ws1].
  cbn in H.
  destruct hs0 as [|h hs0].
  - inverts H.
    eapply segRLs_rec'_spec in E.
    2: ec.
    destruct E as [hsv [Ea Eb]].
    unfold to_side.
    eex.
    1: eauto 1.
    eapply segRLs_sideRLs_concat.
    1: eauto 1.
    ec.
  - destruct h.
    pose proof (N_OS_spec n) as E0.
    destruct (N_OS n); subst n.
    + des_if' H.
      des_if' H.
      destruct p as [ws2 w'].
      des_if' H.
      destruct p as [ws'0 w'0].
      inverts H.
      eapply IHT in E2.
      destruct E2 as [hs' [E2a E2b]].
      eapply f0_spec in E1.
      inverts E2a.
      inverts H1.
      eapply vN_sub1_spec in E0.
      2: eauto 1.
      eapply segRLs_rec'_spec in E.
      2: ec.
      3: eauto 1.
      2: ec; eauto 1.
      destruct E as [hsv [Ea Eb]].
      eex.
      1: eauto 1.
      unfold to_side.
      rewrite concat_app,Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      1: eauto 1.
      rewrite Nnat.N2Nat.inj_add,lpow_add,<-app_assoc.
      eapply sideRLs_trans; eauto 1.
    + des_if' H.
      des_if' H.
      destruct p as [ws'0 w'].
      inverts H.
      eapply IHT in E1.
      destruct E1 as [hs' [E1a E1b]].
      eapply vN_is0'_spec in E0.
      eapply segRLs_rec'_spec in E.
      2: ec.
      3: eauto 1.
      2: ec; eauto 1.
      destruct E as [hsv [Ea Eb]].
      eex.
      1: eauto 1.
      unfold to_side.
      rewrite concat_app,Str_app_assoc.
      eapply segRLs_sideRLs_concat; eauto 1.
Qed.

End vhead_sec.

Fixpoint lcp(ls ls0:list seg):list seg :=
match ls,ls0 with
| h::t,h0::t0 => if eqb h h0 then h::lcp t t0 else []
| _,_ => []
end.

Fixpoint skip(ls ls0:list seg):option (list seg) :=
match ls,ls0 with
| h::t,h0::t0 => if eqb h h0 then skip t t0 else None
| _,[] => Some ls
| _,_ => None
end.

Fixpoint interpolate(ls ls0 ls1:list seg)(T:nat):option (list (list seg+list seg)) :=
match T with
| O => None
| S T =>
  if (eqb ls [] && eqb ls0 [] && eqb ls1 []) then Some [] else
  let ls0' := lcp ls0 ls1 in
  let ls' := lcp ls ls0' in
  match ls' with
  | [] =>
    skip ls0 ls0' &&& (fun ls0 =>
    skip ls1 ls0' &&& (fun ls1 =>
    skip ls1 ls0' &&& (fun ls1 =>
    interpolate ls ls0 ls1 T &&& (fun res =>
    Some (inr ls0' :: res)))))
  | _ =>
    skip ls ls' &&& (fun ls =>
    skip ls0 ls' &&& (fun ls0 =>
    skip ls1 ls' &&& (fun ls1 =>
    interpolate ls ls0 ls1 T &&& (fun res =>
    ((Some (inl ls' :: res))))
    )))
  end
end.

Definition interpolate'(x0 x1 x2:list seg * seg) T :=
match x0,x1,x2 with
| (ws0,w0),(ws1,w1),(ws2,w2) =>
  b2o (eqb w0 w1 && eqb w0 w2) &&& (fun _ =>
  interpolate ws0 ws1 ws2 T &&& (fun ws =>
  Some (ws,w0)))
end.

Fixpoint vheads_v hs id (f:N->bool) :=
match hs with
| vhead_mk h n _::hs =>
  vhead_mk h n (if f id then vN_c n else vN_v id (Nmap_mk 0 0 0 0))::vheads_v hs (id+1) f
| [] => []
end.

Fixpoint get_del_vars hs :=
match hs with
| vhead_mk h 0 (vN_v id _)::hs =>
  fun x => if x =? id then true else get_del_vars hs x
| _::hs => get_del_vars hs
| [] => fun _ => false
end.


Ltac rw_pa := repeat rewrite N.pow_add_r in *.

Lemma Nmap_applys_inc a0 a1 b0 b1 n k:
  a1<>0 ->
  Nmap_applys (Nmap_mk a0 (a0+a1) b0 (b0+2^a0*b1)) (2^a0*n+b0) (2^a0*2^(a1*k)*n+(b0+(2^(a1*k)-1)/(2^a1-1)*(2^a0*b1))) k.
Proof.
  gen a0 a1 b0 b1 n.
  induction k using N.peano_ind; intros.
  - applys_eq Nmap_applys_O.
    repeat rewrite N.mul_0_r.
    lia.
  - replace (N.succ k) with (1+k) by lia.
    eapply Nmap_applys_S.
    1: ec.
    replace (a1*(1+k)) with (a1+a1*k) by lia.
    rw_pa.
    applys_eq (IHk a0 a1 b0 b1 (2^a1*n+b1)).
    1,3: lia.
    remember (2^(a1*k)) as v2.
    remember (2^a1-1) as v1.
    assert (v1<>0). {
      replace a1 with (1+(a1-1)) in * by lia.
      rw_pa; lia.
    }
    replace (2^a1) with (v1+1) in * by lia.
    replace ((v1+1)*v2-1) with (v2-1+v2*v1) by lia.
    rewrite N.div_add by lia.
    lia.
Qed.

Lemma Nmap_applys_S' mp n0 n1 n2 k:
  Nmap_applys mp n0 n1 k ->
  Nmap_apply mp n1 n2 ->
  Nmap_applys mp n0 n2 (1+k).
Proof.
  intro H.
  induction H; intros.
  - ec.
    1: eauto 1.
    ec.
  - ec; eauto 2.
Qed.

Lemma Nmap_apply_rev a0 a1 b0 b1 n0 n1:
  Nmap_apply (Nmap_mk a0 a1 b0 b1) n0 n1 ->
  Nmap_apply (Nmap_mk a1 a0 b1 b0) n1 n0.
Proof.
  intros.
  inverts H.
  ec.
Qed.

Local Opaque N.add.

Lemma Nmap_applys_rev a0 a1 b0 b1 n0 n1 k:
  Nmap_applys (Nmap_mk a0 a1 b0 b1) n0 n1 k ->
  Nmap_applys (Nmap_mk a1 a0 b1 b0) n1 n0 k.
Proof.
  gen a0 a1 b0 b1 n0 n1.
  induction k using N.peano_ind; intros.
  - inverts H; [ec|lia].
  - replace (N.succ k) with (1+k) in * by lia.
    inverts H; [lia|].
    replace k0 with k in * by lia.
    eapply Nmap_applys_S'.
    + eauto 2.
    + eapply Nmap_apply_rev; eauto 1.
Qed.

Lemma Nmap_applys_dec a0 a1 b0 b1 n k:
  a1<>0 ->
  Nmap_applys (Nmap_mk (a0+a1) a0 (b0+2^a0*b1) b0) (2^a0*2^(a1*k)*n+(b0+(2^(a1*k)-1)/(2^a1-1)*(2^a0*b1))) (2^a0*n+b0) k.
Proof.
  intros.
  apply Nmap_applys_rev.
  apply Nmap_applys_inc; auto 1.
Qed.

Inductive N' :=
| N'_mk(a b c d:N)
| N'_c(a:N)
| N'_mk2(a b c a' c':N).

Definition toN(n:N)(x:N'):N :=
match x with
| N'_mk a b c d => ((2^(n*a)-1)*b+c)/d
| N'_c a => a
| N'_mk2 a b c a' c' => ((2^(n*a)-1)*b+c)*2^(n*a')+c'
end.

Definition N'_eq_c x k :=
match x with
| N'_c c => b2o (c =? k)
| N'_mk a b c d =>
  b2o (b =? 0) &&& (fun _ =>
  b2o (c/d =? k))
| _ => None
end.

Ltac des_N_op :=
repeat
match goal with
| [H: b2o (?a =? ?b) = Some _ |- _] =>
  destruct (N.eqb_spec a b); inverts H; subst
| [H: b2o (negb (?a =? ?b)) = Some _ |- _] =>
  destruct (N.eqb_spec a b); inverts H
| [H: b2o (eqb ?a ?b) = Some _ |- _] =>
  destruct (eqb_spec a b); inverts H; subst
| [H: Nsubge ?a ?b = Some _ |- _] =>
  apply Nsubge_spec in H; subst
| [H: Ndiv ?a ?b = Some _ |- _] =>
  apply Ndiv_spec in H; subst
end.

Lemma N'_eq_c_spec x k u n:
  N'_eq_c x k = Some u ->
  toN n x = k.
Proof.
  unfold N'_eq_c.
  intros.
  destruct x.
  - des_if' H.
    cbn in H.
    des_N_op.
    unfold toN.
    f_equal; lia.
  - des_N_op.
    trivial.
  - congruence.
Qed.

Definition N'_Nmap_apply mp x :=
match mp with
| Nmap_mk a0 a1 b0 b1 =>
  match x with
  | N'_c c =>
    Nsubge c b0 &&& (fun c =>
    Ndiv c (2^a0) &&& (fun c =>
    Some (N'_c (c*2^a1+b1))))
  | N'_mk a b c d =>
    Nsubge c (b0*d) &&& (fun c =>
    Ndiv b (2^a0*d) &&& (fun b =>
    Ndiv c (2^a0*d) &&& (fun c =>
    b2o (negb (d=?0)) &&& (fun _ =>
    Some (N'_mk a (b*2^a1*d) ((c*2^a1+b1)*d) d)))))
  | N'_mk2 a b c a' c' =>
    Nsubge c' b0 &&& (fun c' =>
    Ndiv b (2^a0) &&& (fun b =>
    Ndiv c (2^a0) &&& (fun c =>
    Ndiv c' (2^a0) &&& (fun c' =>
    Some (N'_mk2 a (b*2^a1) (c*2^a1) a' (c'*2^a1+b1))))))
  end
| Nmap_c b0 b1 =>
  N'_eq_c x b0 &&& (fun _ =>
  Some (N'_c b1))
end.

Lemma N'_Nmap_apply_spec mp x x' n:
  N'_Nmap_apply mp x = Some x' ->
  Nmap_apply mp (toN n x) (toN n x').
Proof.
  unfold N'_Nmap_apply.
  intros.
  destruct mp.
  - destruct x.
    + do 4 des_if' H.
      inverts H.
      des_N_op.
      unfold toN.
      repeat rewrite N.mul_assoc.
      repeat rewrite <-N.mul_add_distr_r.
      repeat rewrite N.div_mul by auto 1.
      applys_eq (Nmap_apply_mk a0 a1 b0 b1 ((2^(n*a)-1)*n1+n2)); lia.
    + do 2 des_if' H.
      inverts H.
      des_N_op.
      unfold toN.
      applys_eq (Nmap_apply_mk a0 a1 b0 b1 n1); lia.
    + do 4 des_if' H.
      inverts H.
      des_N_op.
      unfold toN.
      applys_eq (Nmap_apply_mk a0 a1 b0 b1 (((2^(n*a)-1)*n1+n2)*2^(n*a')+n3)); lia.
  - des_if' H.
    inverts H.
    eapply N'_eq_c_spec in E.
    rewrite E.
    ec.
Qed.

Definition N'_Nmap_applys_inc_0(a0 a1 b0 b1:N)(x:N'):option N' :=
match x with
| N'_c n =>
  b2o (negb (a1=?0)) &&& (fun _ =>
  Nsubge n b0 &&& (fun n =>
  Ndiv n (2^a0) &&& (fun n =>
  Some (N'_mk a1 (2^a0*(b1+n*(2^a1-1))) ((2^a0*n+b0)*(2^a1-1)) (2^a1-1)))))
| N'_mk a b c d =>
  b2o (d=?1) &&& (fun _ =>
  b2o (negb (a1=?0)) &&& (fun _ =>
  b2o (b1=?0) &&& (fun _ =>
  Nsubge c b0 &&& (fun c =>
  Ndiv c (2^a0) &&& (fun c =>
  Ndiv b (2^a0) &&& (fun b =>
  Some (N'_mk2 a (b*2^a0) (c*2^a0) a1 b0)))))))
| _ => None
end.

Definition N'_simpl_d x :=
match x with
| N'_mk a b c d =>
  let g:=N.gcd d (N.gcd b c) in
  b2o (negb (g=?0)) &&& (fun _ =>
  Ndiv b g &&& (fun b =>
  Ndiv c g &&& (fun c =>
  Ndiv d g &&& (fun d =>
  Some (N'_mk a b c d)))))
| _ => Some x
end.

Lemma N'_simpl_d_spec x x' n:
  N'_simpl_d x = Some x' ->
  toN n x = toN n x'.
Proof.
  unfold N'_simpl_d.
  intros.
  destruct x.
  2,3: inverts H; trivial.
  do 4 des_if' H.
  inverts H.
  des_N_op.
  remember (N.gcd d (N.gcd b c)) as v1.
  clear Heqv1.
  subst.
  unfold toN.
  rewrite N.mul_assoc.
  rewrite <-N.mul_add_distr_r.
  rewrite N.Div0.div_mul_cancel_r; trivial.
Qed.

Definition N'_Nmap_applys_inc(a0 a1 b0 b1:N)(x:N'):option N' :=
N'_Nmap_applys_inc_0 a0 a1 b0 b1 x &&& (fun x =>
N'_simpl_d x).

Lemma geosum_div a n:
  (2^(n*a)-1) mod (2^a-1) = 0.
Proof.
  intros.
  induction n using N.peano_ind.
  - rewrite N.mul_0_l; trivial.
  - rewrite N.mul_succ_l.
    rw_pa.
    remember (2^(n*a)-1) as v1. 
    replace (2^(n*a)) with (v1+1) in * by lia.
    remember (2^(a)-1) as v2. 
    replace (2^(a)) with (v2+1) in * by lia.
    replace ((v1+1)*(v2+1)-1) with (v1+(v1+1)*v2) by lia.
    rewrite N.Div0.mod_add; trivial.
Qed.

Lemma N'_Nmap_applys_inc_0_spec a0 a1 b0 b1 x x' n:
  N'_Nmap_applys_inc_0 a0 a1 b0 b1 x = Some x' ->
  Nmap_applys (Nmap_mk a0 (a0+a1) b0 (b0+2^a0*b1)) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_inc_0.
  intros.
  destruct x.
  3: inverts H.
  1:{
    do 6 des_if' H.
    inverts H.
    des_N_op.
    unfold toN.
    applys_eq (Nmap_applys_inc a0 a1 b0 0 ((2^(n*a)-1)*n2+n1)).
    1,3: lia.
    rewrite (N.mul_comm _ n).
    lia.
  }
  do 3 des_if' H.
  inverts H.
  des_N_op.
  unfold toN.
  pose proof (geosum_div a1 n) as I1.
  applys_eq (Nmap_applys_inc a0 a1 b0 b1 n1 n).
  1,3: lia.
  remember (2^a1-1) as v1.
  assert (v1<>0) by (pose proof (N.pow_le_mono_r 2 1 a1); lia).
  replace (2^a1) with (v1+1) in * by lia.
  rewrite (N.mul_comm a1 n).
  remember (2^(n*a1)-1) as v2.
  replace (2^(n*a1)) with (v2+1) in * by lia.
  repeat rewrite N.mul_assoc.
  repeat rewrite N.add_assoc.
  rewrite N.div_add by lia.
  rewrite <-N.mul_assoc,N.mul_comm.
  rewrite N.Lcm0.divide_div_mul_exact.
  2: apply N.Lcm0.mod_divide,I1.
  pose proof (N.div_mod v2 v1) as I2.
  rewrite I1 in I2.
  lia.
Qed.

Lemma N'_Nmap_applys_inc_spec a0 a1 b0 b1 x x' n:
  N'_Nmap_applys_inc a0 a1 b0 b1 x = Some x' ->
  Nmap_applys (Nmap_mk a0 (a0+a1) b0 (b0+2^a0*b1)) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_inc.
  intros.
  des_if' H.
  inverts H.
  eapply N'_Nmap_applys_inc_0_spec in E.
  eapply N'_simpl_d_spec in H1.
  rewrite H1 in E.
  apply E.
Qed.

Definition N'_set_d x k :=
match x with
| N'_mk a b c d =>
  Ndiv k d &&& (fun k =>
  b2o (negb (k =? 0)) &&& (fun _ =>
  Some (N'_mk a (b*k) (c*k) (d*k))))
| _ => None
end.

Lemma N'_set_d_spec x k x' n:
  N'_set_d x k = Some x' ->
  toN n x = toN n x'.
Proof.
  unfold N'_set_d.
  intros.
  destruct x.
  2,3: inverts H.
  do 2 des_if' H.
  inverts H.
  des_N_op.
  unfold toN.
  rewrite N.mul_assoc.
  rewrite <-N.mul_add_distr_r.
  rewrite N.Div0.div_mul_cancel_r; trivial.
Qed.

Definition N'_Nmap_applys_dec_v3(a0 a1 b0 b1:N)(x:N'):option N' :=
match x with
| N'_mk2 a b c a' c' =>
  b2o (negb (a1=?0)) &&& (fun _ =>
  b2o (b1=?0) &&& (fun _ =>
  b2o (a1=?a') &&& (fun _ =>
  b2o (b0=?c') &&& (fun _ =>
  Ndiv b (2^a0) &&& (fun b =>
  Ndiv c (2^a0) &&& (fun c =>
  Some (N'_mk a (b*2^a0) (c*2^a0+b0) 1)))))))
| _ => None
end.

Lemma N'_Nmap_applys_dec_v3_spec a0 a1 b0 b1 x x' n:
  N'_Nmap_applys_dec_v3 a0 a1 b0 b1 x = Some x' ->
  Nmap_applys (Nmap_mk (a0+a1) a0 (b0+2^a0*b1) b0) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_dec_v3.
  intros.
  destruct x.
  1,2: inverts H.
  do 6 des_if' H.
  inverts H.
  des_N_op.
  unfold toN.
  applys_eq (Nmap_applys_dec a0 a' c' 0 ((2^(n*a)-1)*n0+n1)).
  2,3: lia.
  rewrite (N.mul_comm _ n).
  lia.
Qed.


Definition N'_Nmap_applys_dec_v2(a0 a1 b0 b1:N)(x:N'):option N' :=
N'_set_d x (2^a1-1) &&& (fun x =>
match x with
| N'_mk a b c d =>
  b2o (negb (a1=?0)) &&& (fun _ =>
  b2o (a=?a1*2) &&& (fun _ =>
  b2o (d =? 2^a1-1) &&& (fun _ =>
  Ndiv b (2^a0*d) &&& (fun b' =>
  Nsubge c (b0*d) &&& (fun c =>
  Ndiv c (2^a0*d) &&& (fun c' =>
  b2o (b'*d=?b1+c'*d) &&& (fun _ =>
  Some (N'_mk a1 (b'*2^a0) (c'*2^a0+b0) 1))))))))
| _ => None
end).

Ltac Nmul_to_r d :=
  repeat rewrite <-N.mul_assoc;
  repeat rewrite (N.mul_comm d);
  repeat rewrite N.mul_assoc.

Lemma N'_Nmap_applys_dec_v2_spec a0 a1 b0 b1 x x' n:
  N'_Nmap_applys_dec_v2 a0 a1 b0 b1 x = Some x' ->
  Nmap_applys (Nmap_mk (a0+a1) a0 (b0+2^a0*b1) b0) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_dec_v2.
  intros.
  destruct x.
  2,3: inverts H.
  des_if' H.
  cbn in H.
  destruct n0.
  2,3: inverts H.
  do 7 des_if' H.
  inverts H.
  rename n2 into c'.
  rename n0 into b'.
  des_N_op.
  eapply N'_set_d_spec in E.
  rewrite E; clear E.
  unfold toN.
  pose proof (geosum_div a1 n) as I1.
  replace (n*(a1*2)) with (n*a1+n*a1) by lia.
  rewrite N.pow_add_r.
  remember (2^a1-1) as v1.
  assert (v1<>0) by (pose proof (N.pow_le_mono_r 2 1 a1); lia).
  Nmul_to_r (2^a1-1).
  repeat rewrite N.div_add_l by lia.
  repeat rewrite N.div_mul by lia.
  rewrite N.div_1_r.
  applys_eq (Nmap_applys_dec a0 a1 b0 b1 (((2^(n*a1)-1)*b'+c')) n).
  2,3: lia.
  rewrite (N.mul_comm a1 n).
  remember (2^(n*a1)-1) as v2.
  replace (2^(n*a1)) with (v2+1) in * by lia.
  replace (2^a1) with (v1+1) in * by lia.
  rewrite N.add_sub.
  remember (v2/v1) as v3.
  replace v2 with (v3*v1) in * by (apply N.Div0.div_exact in I1; lia).
  lia.
Qed.

Definition N'_Nmap_applys_dec_v1(a0 a1 b0 b1:N)(x:N'):option N' :=
N'_set_d x (2^a1-1) &&& (fun x =>
match x with
| N'_mk a b c d =>
  b2o (negb (a1=?0)) &&& (fun _ =>
  b2o (a=?a1) &&& (fun _ =>
  b2o (d =? 2^a1-1) &&& (fun _ =>
  Nsubge b (2^a0*b1) &&& (fun b =>
  Ndiv b (2^a0*d) &&& (fun n =>
  b2o (c =? ((2^a0*n+b0)*d)) &&& (fun _ =>
  Some (N'_c (n*2^a0+b0))))))))
| _ => None
end).

Lemma N'_Nmap_applys_dec_v1_spec a0 a1 b0 b1 x x' n:
  N'_Nmap_applys_dec_v1 a0 a1 b0 b1 x = Some x' ->
  Nmap_applys (Nmap_mk (a0+a1) a0 (b0+2^a0*b1) b0) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_dec_v1.
  intros.
  destruct x.
  2,3: inverts H.
  des_if' H.
  cbn in H.
  destruct n0.
  2,3: inverts H.
  do 6 des_if' H.
  inverts H.
  des_N_op.
  eapply N'_set_d_spec in E.
  rewrite E; clear E.
  unfold toN.
  pose proof (geosum_div a1 n) as I1.
  applys_eq (Nmap_applys_dec a0 a1 b0 b1 n1 n).
  2,3: lia.
  remember (2^a1-1) as v1.
  assert (v1<>0) by (pose proof (N.pow_le_mono_r 2 1 a1); lia).
  replace (2^a1) with (v1+1) in * by lia.
  rewrite (N.mul_comm a1 n).
  remember (2^(n*a1)-1) as v2.
  replace (2^(n*a1)) with (v2+1) in * by lia.
  repeat rewrite N.mul_assoc.
  repeat rewrite N.add_assoc.
  rewrite N.div_add by lia.
  rewrite <-N.mul_assoc,N.mul_comm.
  rewrite N.Lcm0.divide_div_mul_exact.
  2: apply N.Lcm0.mod_divide,I1.
  pose proof (N.div_mod v2 v1) as I2.
  rewrite I1 in I2.
  lia.
Qed.

Definition N'_Nmap_applys_dec(a0 a1 b0 b1:N)(x:N'):option N' :=
  N'_Nmap_applys_dec_v1 a0 a1 b0 b1 x ||| (fun _ =>
  N'_Nmap_applys_dec_v2 a0 a1 b0 b1 x ||| (fun _ =>
  N'_Nmap_applys_dec_v3 a0 a1 b0 b1 x)).

Lemma N'_Nmap_applys_dec_spec a0 a1 b0 b1 x x' n:
  N'_Nmap_applys_dec a0 a1 b0 b1 x = Some x' ->
  Nmap_applys (Nmap_mk (a0+a1) a0 (b0+2^a0*b1) b0) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_dec.
  intros.
  des_if' H.
  {
    inverts H.
    eapply N'_Nmap_applys_dec_v1_spec,E.
  }
  clear E; rename H1 into H.
  des_if' H.
  {
    inverts H.
    eapply N'_Nmap_applys_dec_v2_spec,E.
  }
  eapply N'_Nmap_applys_dec_v3_spec,H1.
Qed.

Definition N'_Nmap_applys_id(a0 b0:N)(x:N'):option N' :=
N'_Nmap_apply (Nmap_mk a0 a0 b0 b0) x.

Definition N'_Nmap_applys_id_c(b0:N)(x:N'):option N' :=
N'_Nmap_apply (Nmap_c b0 b0) x.

Definition N'_Nmap_applys mp x :=
match mp with
| Nmap_mk a0 a1 b0 b1 =>
  (b2o (a0=?a1) &&& (fun _ =>
  b2o (b0=?b1) &&& (fun _ =>
  N'_Nmap_applys_id a0 b0 x))) ||| (fun _ =>
  (Nsubge a1 a0 &&& (fun a1 =>
  Nsubge b1 b0 &&& (fun b1 =>
  Ndiv b1 (2^a0) &&& (fun b1 =>
  N'_Nmap_applys_inc a0 a1 b0 b1 x)))) ||| (fun _ =>
  (Nsubge a0 a1 &&& (fun a0 =>
  Nsubge b0 b1 &&& (fun b0 =>
  Ndiv b0 (2^a1) &&& (fun b0 =>
  N'_Nmap_applys_dec a1 a0 b1 b0 x))))))
| Nmap_c b0 b1 =>
  b2o (b0=?b1) &&& (fun _ =>
  N'_Nmap_applys_id_c b0 x)
end.

Lemma Nmap_applys_id a0 b0 x x' n:
  Nmap_apply (Nmap_mk a0 a0 b0 b0) x x' ->
  Nmap_applys (Nmap_mk a0 a0 b0 b0) x x' n.
Proof.
  intros.
  inverts H.
  induction n using N.peano_ind.
  1: ec.
  replace (N.succ n) with (1+n) by lia.
  ec.
  2: eauto 1.
  ec.
Qed.

Lemma N'_Nmap_applys_id_spec a0 b0 x x' n:
  N'_Nmap_applys_id a0 b0 x = Some x' ->
  Nmap_applys (Nmap_mk a0 a0 b0 b0) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_id.
  intros.
  eapply N'_Nmap_apply_spec in H.
  eapply Nmap_applys_id in H.
  apply H.
Qed.

Lemma Nmap_applys_id_c b0 x x' n:
  Nmap_apply (Nmap_c b0 b0) x x' ->
  Nmap_applys (Nmap_c b0 b0) x x' n.
Proof.
  intros H.
  inverts H.
  induction n using N.peano_ind.
  1: ec.
  replace (N.succ n) with (1+n) by lia.
  ec.
  2: eauto 1.
  ec.
Qed.

Lemma N'_Nmap_applys_id_c_spec b0 x x' n:
  N'_Nmap_applys_id_c b0 x = Some x' ->
  Nmap_applys (Nmap_c b0 b0) (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys_id_c.
  intros.
  eapply N'_Nmap_apply_spec in H.
  eapply Nmap_applys_id_c in H.
  apply H.
Qed.

Lemma N'_Nmap_applys_spec mp x x' n:
  N'_Nmap_applys mp x = Some x' ->
  Nmap_applys mp (toN n x) (toN n x') n.
Proof.
  unfold N'_Nmap_applys.
  intros.
  destruct mp.
  2:{
    des_if' H.
    inverts H.
    des_N_op.
    eapply N'_Nmap_applys_id_c_spec in H1.
    apply H1.
  }
  des_if' H.
  {
    inverts H.
    do 2 des_if' E.
    inverts E.
    des_N_op.
    eapply N'_Nmap_applys_id_spec in H0.
    apply H0.
  }
  clear E.
  rename H1 into H.
  des_if' H.
  {
    inverts H.
    do 3 des_if' E.
    inverts E.
    des_N_op.
    eapply N'_Nmap_applys_inc_spec in H0.
    applys_eq H0; flia.
  }
  {
    do 3 des_if' H1.
    inverts H1.
    des_N_op.
    eapply N'_Nmap_applys_dec_spec in H0.
    applys_eq H0; flia.
  }
Qed.

Inductive N'_head :=
| N'_head_mk(h0:head)(n:N').

Definition Nmap_is_id mp :=
match mp with
| Nmap_mk 0 0 0 0 => Some tt
| _ => None
end.

Fixpoint N'_match_vheads hs (hs':list (N'_head)) :=
match hs,hs' with
| vhead_mk h n n'::hs,(N'_head_mk h'0 h')::hs' =>
  b2o (eqb h h'0) &&& (fun _ =>
  N'_match_vheads hs hs' &&& (fun f =>
  match n' with
  | vN_v id mp =>
    Nmap_is_id mp &&& (fun _ =>
    Some (fun x => if x=?id then Some h' else f x))
  | vN_c c =>
    N'_eq_c h' c &&& (fun _ =>
    Some f)
  end))
| [],[] => Some (fun _ => None)
| _,_ => None
end.

Definition N'_eqb x x0 :=
match x,x0 with
| N'_mk a b c d,N'_mk a0 b0 c0 d0 => eqb a a0 && eqb b b0 && eqb c c0 && eqb d d0
| N'_c c,N'_c c0 => eqb c c0
| N'_mk2 a b c a' c',N'_mk2 a0 b0 c0 a'0 c'0 => eqb a a0 && eqb b b0 && eqb c c0 && eqb a' a'0 && eqb c' c'0
| _,_ => false
end.

Instance N'_Eqb: Eqb N'.
Proof with solve_Bool_reflect.
  apply Build_Eqb with (eqb:=N'_eqb).
  intros.
  unfold N'_eqb.
  destruct x,y...
  - destruct (eqb_spec a a0)...
    destruct (eqb_spec b b0)...
    destruct (eqb_spec c c1)...
    destruct (eqb_spec d d0)...
  - destruct (eqb_spec a a0)...
  - destruct (eqb_spec a a0)...
    destruct (eqb_spec b b0)...
    destruct (eqb_spec c c1)...
    destruct (eqb_spec a' a'0)...
    destruct (eqb_spec c' c'0)...
Defined.

Fixpoint N'_matched_vheads hs (hs':list (N'_head)) f {struct hs} :=
match hs,hs' with
| vhead_mk h n n'::hs,(N'_head_mk h'0 h')::hs' =>
  b2o (eqb h h'0) &&& (fun _ =>
  N'_matched_vheads hs hs' f &&& (fun _ =>
  match n' with
  | vN_v id mp =>
    Nmap_is_id mp &&& (fun _ =>
    f id &&& (fun x => b2o (eqb x h')))
  | vN_c c =>
    N'_eq_c h' c
  end))
| [],[] => Some tt 
| _,_ => None
end.

Fixpoint N'_apply_vheads hs f :=
match hs with
| vhead_mk h n n'::hs =>
  N'_apply_vheads hs f &&& (fun res =>
  match n' with
  | vN_v id mp =>
    f id &&& (fun x =>
    N'_Nmap_apply mp x &&& (fun x =>
    Some ((N'_head_mk h x)::res)))
  | vN_c c =>
    Some ((N'_head_mk h (N'_c c))::res)
  end)
| [] => Some []
end.

Fixpoint N'_applys_vheads hs f :=
match hs with
| vhead_mk h n n'::hs =>
  N'_applys_vheads hs f &&& (fun res =>
  match n' with
  | vN_v id mp =>
    f id &&& (fun x =>
    N'_Nmap_applys mp x &&& (fun x =>
    Some ((N'_head_mk h x)::res)))
  | vN_c c =>
    Some ((N'_head_mk h (N'_c c))::res)
  end)
| [] => Some []
end.

Fixpoint hs_match_rec hs hs' id0 :=
match hs,hs' with
| vhead_mk h n (vN_c c)::hs,vhead_mk h' n' (vN_c c')::hs' =>
  b2o (eqb h h') &&& (fun _ =>
  b2o (eqb c c') &&& (fun _ =>
  hs_match_rec hs hs' id0))
| vhead_mk h n (vN_v id mp)::hs,vhead_mk h' n' (vN_v id' mp')::hs' =>
  b2o (eqb h h') &&& (fun _ =>
  b2o (eqb id id') &&& (fun _ =>
  b2o (id0 <=? id) &&& (fun _ =>
  Nmap_is_id mp &&& (fun _ =>
  hs_match_rec hs hs' (1+id)))))
| [],[] => Some tt
| _,_ => None
end.

Definition N'_add (x x0:N') :=
match x,x0 with
| N'_mk a b c d,N'_mk a0 b0 c0 d0 =>
  b2o (eqb a a0) &&& (fun _ =>
  b2o (eqb d 1) &&& (fun _ =>
  b2o (eqb d0 1) &&& (fun _ =>
  Some (N'_mk a (b+b0) (c+c0) d))))
| _,_ => None
end.

Lemma N'_add_spec x x0 x1 n:
  N'_add x x0 = Some x1 ->
  toN n x + toN n x0 = toN n x1.
Proof.
  unfold N'_add.
  intros.
  destruct x,x0.
  all: try congruence.
  do 3 des_if' H.
  inverts H.
  des_N_op.
  unfold toN.
  lia.
Qed.

Definition N'_head_add (x x0:N'_head) :=
match x,x0 with
| N'_head_mk h n,N'_head_mk h0 n0 =>
  b2o (eqb h h0) &&& (fun _ =>
  N'_add n n0 &&& (fun n1 =>
  Some (N'_head_mk h n1)))
end.

Fixpoint merge_hs (hsN':list N'_head) (hs:list vhead) :=
match hsN',hs with
| h'::t',h::t =>
  merge_hs t' t &&& (fun '(t',t) =>
  match t',t with
  | h'0::t'0,h0::t0 =>
    (vhead_add h h0 &&& (fun h1 =>
    N'_head_add h' h'0 &&& (fun h'1 =>
    Some (h'1::t'0,h1::t0)
    ))) ||| (fun _ =>
    Some (h'::t',h::t))
  | [],[] => Some ([h'],[h])
  | _,_ => None
  end)
| [],[] => Some ([],[])
| _,_ => None
end.


Fixpoint segRLs_rec_v hsN' hs ws T :=
merge_hs hsN' (vheads_v hs 0 (fun _ => true)) &&& (fun '(hsN',hs) =>
let hs:=vheads_v hs 0 (fun _=>false) in
match ws with
| [] => Some (hsN',hs,[])
| inl ws::ws0 =>
  segRLs_rec' hs ws T &&& (fun '(hs',ws') =>
  let hs:=vheads_v hs 0 (get_del_vars hs') in
  segRLs_rec' hs ws T &&& (fun '(hs',ws') =>
  N'_match_vheads hs hsN' &&& (fun f =>
  N'_matched_vheads hs hsN' f &&& (fun _ =>
  N'_apply_vheads hs' f &&& (fun hsN' =>
  segRLs_rec_v hsN' hs' ws0 T &&& (fun '(res0,res) =>
  Some (res0,inl ws'::res)))))))
| inr ws::ws0 =>
  segRLs_rec' hs ws T &&& (fun '(hs',ws') =>
  let hs:=vheads_v hs 0 (get_del_vars hs') in
  segRLs_rec' hs ws T &&& (fun '(hs',ws') =>
  N'_match_vheads hs hsN' &&& (fun f =>
  N'_matched_vheads hs hsN' f &&& (fun _ =>
  N'_applys_vheads hs' f &&& (fun hsN' =>
  hs_match_rec hs hs' 0 &&& (fun _ =>
  segRLs_rec_v hsN' hs' ws0 T &&& (fun '(res0,res) =>
  Some (res0,inr ws'::res))))))))
end).

Definition sideRLs_rec_v hsN' hs '(ws,w) T :=
segRLs_rec_v hsN' hs ws T &&& (fun '(hsN',hs,ws0) =>
let hs:=vheads_v hs 0 (fun _=>true) in
N'_match_vheads hs hsN' &&& (fun f =>
N'_matched_vheads hs hsN' f &&& (fun _ =>
sideRLs_rec hs [] w T &&& (fun '(ws1,w0) =>
Some (ws0++[inl ws1],w0))))).

Definition vseg_eval n (w:vseg) :=
match w with
| inl w => concat w
| inr w => (concat w)^^n
end.

Definition vsegs_eval n ws :=
  flat_map (vseg_eval n) ws.

Definition vside_eval(n:nat)(x:vside) :=
let '(ws,w):=x in
(vsegs_eval n ws) *> w *> 0inf.

Definition vseg_O (w:vseg) :=
match w with
| inl w => w
| inr w => []
end.

Definition vseg_S (w:vseg) :=
match w with
| inl w => [inl w]
| inr w => [inl w;inr w]
end.

Definition vside_S (x:vside) :=
let '(ws,w):=x in
(flat_map vseg_S ws,w).

Definition vside_O (x:vside) :=
let '(ws,w):=x in
(flat_map vseg_O ws,w).

Fixpoint vsegs_rot0 (w:list seg) (ws:list vseg): list vseg :=
match ws,w with
| inl [w']::ws',w0::w1 =>
  if eqb w0 w' then
    inl [w0] :: vsegs_rot0 (w1++[w0]) ws'
  else
    inr w :: ws
| _,_ => inr w :: ws
end.

Fixpoint vsegs_rot(ws:list vseg) :=
match ws with
| w::ws =>
  let ws:=vsegs_rot ws in
  match w with
  | inl w => map (fun w => inl [w]) w ++ ws
  | inr w => vsegs_rot0 w ws
  end
| [] => []
end.

Definition vside_rot(x:vside) :=
let '(ws,w):=x in (vsegs_rot ws,w).

Ltac rw_app :=
  repeat (cbn in * ||
  rewrite app_nil_r in * ||
  rewrite concat_app in * ||
  rewrite flat_map_app in * ||
  rewrite <-app_assoc in *);
  trivial;
  try congruence.

Lemma vside_O_spec x:
  to_side (vside_O x) = vside_eval 0 x.
Proof.
  destruct x as [ws w].
  cbn.
  f_equal.
  clear.
  unfold vsegs_eval.
  induction ws; rw_app.
  f_equal.
  2: apply IHws.
  destruct a; rw_app.
Qed.

Lemma vside_S_spec x n:
  vside_eval n (vside_S x) = vside_eval (S n) x.
Proof.
  destruct x as [ws w].
  cbn.
  f_equal.
  clear.
  unfold vsegs_eval.
  induction ws; rw_app.
  rewrite IHws.
  destruct a; rw_app.
Qed.

Lemma vsegs_rot0_spec w ws n:
  vsegs_eval n (vsegs_rot0 w ws) = vsegs_eval n (inr w::ws).
Proof with trivial.
  gen w.
  induction ws; cbn[vsegs_rot0]; intros...
  destruct a...
  destruct l...
  destruct l0...
  destruct w...
  destruct (eqb_spec l0 l)...
  subst.
  unfold vsegs_eval in *.
  cbn[flat_map] in *.
  rewrite IHws.
  do 2 rewrite app_assoc.
  f_equal.
  unfold vseg_eval.
  clear.
  induction n; rw_app.
Qed.

Lemma vsegs_rot_spec x n:
  vsegs_eval n (vsegs_rot x) = vsegs_eval n x.
Proof.
  induction x; cbn[vsegs_rot].
  - trivial.
  - destruct a.
    + unfold vsegs_eval in *; cbn[flat_map] in *.
      rewrite flat_map_app.
      rewrite IHx.
      f_equal.
      clear.
      unfold vseg_eval.
      induction l; rw_app.
    + rewrite vsegs_rot0_spec.
      unfold vsegs_eval in *; rw_app.
Qed.

Lemma vside_rot_spec x n:
  vside_eval n (vside_rot x) = vside_eval n x.
Proof.
  destruct x as [ws w].
  cbn.
  rewrite vsegs_rot_spec.
  trivial.
Qed.

Fixpoint N'_heads_eval hs n :=
match hs with
| [] => []
| N'_head_mk h n'::hs => [h]^^(N.to_nat (toN n n')) ++ N'_heads_eval hs n
end.

Definition f_eval (f:N->option N') i n :=
match f n with
| Some n' => toN i n'
| None => 0
end.

Lemma N'_apply_vheads_spec hs f i hsN':
  N'_apply_vheads hs f = Some hsN' ->
  vheads_eval (f_eval f i) hs (N'_heads_eval hsN' i).
Proof.
  gen hsN'.
  induction hs; cbn[N'_apply_vheads]; intros.
  - inverts H.
    ec.
  - destruct a.
    des_if' H.
    cbn in H.
    destruct n'.
    + des_if' H.
      des_if' H.
      inverts H.
      cbn.
      ec.
      2: eauto 2.
      eapply N'_Nmap_apply_spec in E1.
      ec.
      ec.
      unfold f_eval.
      rewrite E0.
      eauto 1.
    + inverts H.
      cbn.
      ec.
      2: eauto 2.
      ec.
      ec.
Qed.

Lemma N'_applys_vheads_spec hs f i hsN':
  N'_applys_vheads hs f = Some hsN' ->
  vheads_evaln (f_eval f i) hs (N'_heads_eval hsN' i) i.
Proof.
  gen hsN'.
  induction hs; cbn[N'_applys_vheads]; intros.
  - inverts H.
    ec.
  - destruct a.
    des_if' H.
    cbn in H.
    destruct n'.
    + des_if' H.
      des_if' H.
      inverts H.
      cbn.
      ec.
      2: eauto 2.
      eapply N'_Nmap_applys_spec in E1.
      ec.
      ec.
      unfold f_eval.
      rewrite E0.
      eauto 1.
    + inverts H.
      cbn.
      ec.
      2: eauto 2.
      ec.
      ec.
Qed.

Local Opaque N'_Eqb.

Lemma Nmap_is_id_spec mp u:
  Nmap_is_id mp = Some u ->
  mp = Nmap_mk 0 0 0 0.
Proof.
  unfold Nmap_is_id.
  intros.
  destruct mp; [|inverts H].
  destruct a0; [|inverts H].
  destruct a1; [|inverts H].
  destruct b0; [|inverts H].
  destruct b1; [|inverts H].
  ec.
Qed.

Local Opaque N.add N.mul.

Lemma N'_matched_vheads_spec hs hsN' f n hsv:
  N'_matched_vheads hs hsN' f = Some tt ->
  vheads_eval (f_eval f n) hs hsv ->
  N'_heads_eval hsN' n = hsv.
Proof.
  gen hsN' hsv.
  induction hs; cbn[N'_matched_vheads]; intros.
  - destruct hsN'; inverts H.
    inverts H0.
    ec.
  - destruct a.
    destruct hsN' as [|[h'0 h'] hsN'].
    1: inverts H.
    des_if' H.
    des_if' H.
    cbn in H.
    destruct n'.
    + des_if' H.
      des_if' H.
      inverts H.
      des_N_op.
      inverts H0.
      destruct u0.
      cbn.
      f_equal.
      2: eauto 2.
      inverts H2.
      inverts H5.
      f_equal.
      f_equal.
      apply Nmap_is_id_spec in E1; subst.
      inverts H2.
      replace (1*n1+0) with n1 in H by lia.
      subst n1.
      unfold f_eval.
      rewrite E2.
      lia.
    + destruct u0.
      des_N_op.
      eapply N'_eq_c_spec in H.
      cbn.
      rewrite H.
      inverts H0.
      f_equal.
      2: eauto 2.
      inverts H3.
      inverts H6.
      trivial.
Qed.

Inductive hs_match: (list vhead)->(list vhead)->N->Prop :=
| hs_match_O id': hs_match [] [] id'
| hs_match_Sv h n n' hs hs' id mp id':
  hs_match hs hs' (1+id) ->
  id'<=id ->
  hs_match (vhead_mk h n (vN_v id (Nmap_mk 0 0 0 0))::hs) (vhead_mk h n' (vN_v id mp)::hs') id'
| hs_match_Sc h n n0 n' hs hs' id':
  hs_match hs hs' id' ->
  hs_match (vhead_mk h n (vN_c n0)::hs) (vhead_mk h n' (vN_c n0)::hs') id'.

Lemma hs_match_rec_spec hs hs' id0:
  hs_match_rec hs hs' id0 = Some tt ->
  hs_match hs hs' id0.
Proof with (try congruence).
  gen hs' id0.
  induction hs; cbn[hs_match_rec]; intros.
  - destruct hs'; inverts H.
    ec.
  - destruct a.
    destruct n'.
    + destruct hs' as [|h' hs']...
      destruct h'...
      destruct n'...
      do 4 des_if' H.
      cbn in H.
      apply IHhs in H.
      destruct (eqb_spec h h0); inverts E; subst.
      destruct (eqb_spec id id1); inverts E0; subst.
      destruct (N.leb_spec id0 id1); inverts E1; subst.
      eapply Nmap_is_id_spec in E2; subst.
      ec; eauto 1.
    + destruct hs' as [|h' hs']...
      destruct h'...
      destruct n'...
      do 2 des_if' H.
      cbn in H.
      apply IHhs in H.
      destruct (eqb_spec h h0); inverts E; subst.
      destruct (eqb_spec c c1); inverts E0; subst.
      ec; eauto 1.
Qed.

Lemma hs_match_hs'_ge hs hs' id' hs'v i ctx1 ctx2:
  hs_match hs hs' id' ->
  (forall i, id'<=i -> ctx1 i = ctx2 i) ->
  vheads_evaln ctx1 hs' hs'v i ->
  vheads_evaln ctx2 hs' hs'v i.
Proof.
  intro H.
  gen hs'v i ctx1 ctx2.
  induction H; intros.
  - inverts H0.
    ec.
  - inverts H2.
    inverts H5.
    inverts H9.
    ec.
    + ec.
      ec.
      rewrite H1 in H6; auto 1.
    + eapply IHhs_match.
      2: eauto 1.
      intros.
      apply H1; lia.
  - inverts H1.
    inverts H4.
    inverts H8.
    ec.
    + ec.
      ec.
    + eauto 2.
Qed.

Lemma hs_match_hs_ge hs hs' id' hsv ctx1 ctx2:
  hs_match hs hs' id' ->
  (forall i, id'<=i -> ctx1 i = ctx2 i) ->
  vheads_eval ctx1 hs hsv ->
  vheads_eval ctx2 hs hsv.
Proof.
  intro H.
  gen hsv ctx1 ctx2.
  induction H; intros.
  - inverts H0.
    ec.
  - inverts H2.
    inverts H5.
    inverts H8.
    ec.
    + ec.
      ec.
      rewrite H1 in H5; auto 1.
    + eapply IHhs_match.
      2: eauto 1.
      intros.
      apply H1; lia.
  - inverts H1.
    inverts H4.
    inverts H7.
    ec.
    + ec.
      ec.
    + eauto 2.
Qed.

Lemma hs_match_spec1 hs hs' id':
  hs_match hs hs' id' ->
  forall ctx hs'v i,
  vheads_evaln ctx hs' hs'v (N.succ i) ->
  exists ctx',
  (vheads_evaln ctx' hs' hs'v i /\
  (forall hsv, vheads_eval ctx' hs hsv -> vheads_eval ctx hs' hsv)).
Proof.
  intro H.
  induction H; intros.
  - inverts H.
    eexists ctx; split.
    1: ec.
    intros.
    inverts H.
    ec.
  - inverts H1.
    eapply IHhs_match in H7.
    destruct H7 as [ctx' [I1 I2]].
    inverts H4.
    inverts H7.
    inverts H5.
    1: lia.
    replace k with i in * by lia.
    exists (fun x => if x=?id then n1 else ctx' x); split.
    + ec.
      2: {
        eapply hs_match_hs'_ge; eauto 1.
        intros.
        destruct (N.eqb_spec i0 id); lia.
      }
      ec.
      ec.
      destruct (N.eqb_spec id id); [eauto 1|lia].
    + intros.
      inverts H3.
      inverts H6.
      inverts H10.
      inverts H6.
      destruct (N.eqb_spec id id); [|lia].
      subst.
      ec.
      * ec.
        ec.
        eauto 1.
      * eapply I2.
        eapply hs_match_hs_ge.
        3: apply H9.
        1: eauto 1.
        intros.
        cbn.
        destruct (N.eqb_spec i0 id); lia.
  - inverts H0.
    eapply IHhs_match in H6.
    destruct H6 as [ctx' [I1 I2]].
    inverts H3.
    inverts H6.
    exists ctx'; split.
    + ec.
      2: eauto 1.
      ec.
      ec.
    + intros.
      inverts H0.
      inverts H3.
      inverts H6.
      ec.
      2: eauto 2.
      ec.
      ec.
Qed.

Lemma hs_match_spec2 hs hs' id':
  hs_match hs hs' id' ->
  forall ctx hs'v,
  vheads_evaln ctx hs' hs'v 0 ->
  vheads_eval ctx hs hs'v.
Proof.
  intro H.
  induction H; intros.
  - inverts H.
    ec.
  - inverts H1.
    inverts H4.
    inverts H8.
    ec.
    2: eauto 2.
    ec.
    ec.
    inverts H5.
    + applys_eq (Nmap_apply_mk 0 0 0 0 (ctx id)); lia.
    + lia.
  - inverts H0.
    inverts H3.
    inverts H7.
    ec.
    2: eauto 2.
    ec.
    ec.
Qed.

Lemma segRLs_rec'_specn hs ws T hs' ws' i:
  segRLs_rec' hs ws T = Some (hs',ws') ->
  hs_match hs hs' 0 ->
  forall ctx hs'v,
  vheads_evaln ctx hs' hs'v i ->
  exists hsv,
  vheads_eval ctx hs hsv /\
  segRLs tm hsv hs'v ((concat ws)^^(N.to_nat i)) ((concat ws')^^(N.to_nat i)).
Proof.
  intros H H0.
  induction i using N.peano_ind; intros.
  - exists hs'v; split.
    + eapply hs_match_spec2 in H0; eauto 1.
    + apply segRLs_nil.
  - replace (N.to_nat (N.succ i)) with (S (N.to_nat i))%nat by lia.
    cbn[lpow].
    eapply hs_match_spec1 in H0.
    2: eauto 1.
    destruct H0 as [ctx' [X1 X2]].
    apply IHi in X1.
    destruct X1 as [hsv [X1a X1b]].
    specialize (X2 _ X1a).
    eapply segRLs_rec'_spec in X2.
    2: eauto 1.
    destruct X2 as [hsv0 [I1 I2]].
    eexists; split.
    1: eauto 1.
    eapply segRLs_concat; eauto 1.
Qed.

Lemma merge_hs_spec hsN' hs hsN'0 hs0 n:
  merge_hs hsN' hs = Some (hsN'0,hs0) ->
  N'_heads_eval hsN' n = N'_heads_eval hsN'0 n.
Proof.
  gen hs hsN'0 hs0.
  induction hsN' as [|h' t']; destruct hs as [|h t]; cbn[merge_hs]; intros.
  all: try congruence.
  des_if' H.
  destruct p as [[|h'0 t'0] [|h0 t0]];
  cbn in H.
  all: try congruence.
  - inverts H.
    cbn[N'_heads_eval].
    destruct h' as [h' n'].
    apply IHt' in E.
    rewrite E; reflexivity.
  - des_if' H.
    + inverts H.
      do 2 des_if' E0.
      inverts E0.
      apply IHt' in E.
      cbn[N'_heads_eval].
      unfold N'_head_add in E2.
      destruct h' as [h' n'].
      destruct h'0 as [h'0 n'0].
      do 2 des_if' E2.
      inverts E2.
      des_N_op.
      eapply N'_add_spec in E3.
      rewrite <-E3,E.
      cbn[N'_heads_eval].
      rewrite Nnat.N2Nat.inj_add,lpow_add,app_assoc; reflexivity.
    + clear E0.
      apply IHt' in E.
      destruct h' as [h' n'].
      destruct h'0 as [h'0 n'0].
      cbn[N'_heads_eval].
      rewrite E.
      reflexivity.
Qed.


Lemma segRLs_rec_v_spec hsN' hs ws T hsN'0 hs' ws' n:
  segRLs_rec_v hsN' hs ws T = Some (hsN'0,hs',ws') ->
  segRLs tm (N'_heads_eval hsN' n) (N'_heads_eval hsN'0 n) (vsegs_eval (N.to_nat n) ws) (vsegs_eval (N.to_nat n) ws').
Proof.
  gen hsN' hs hsN'0 hs' ws'.
  induction ws; cbn[segRLs_rec_v]; intros.
  - des_if' H.
    destruct p as [hsN'a hsa].
    inverts H.
    eapply merge_hs_spec in E.
    rewrite E.
    apply segRLs_nil.
  - des_if' H.
    destruct p as [hsN'a hsa].
    eapply merge_hs_spec in E.
    rewrite E.
    clear E.
    destruct a.
    + des_if' H.
      destruct p as [hs'0 ws'0].
      des_if' H.
      destruct p as [hs'1 ws'1].
      des_if' H.
      des_if' H.
      des_if' H.
      des_if' H.
      destruct p as [[res1 res0] res].
      inverts H.
      unfold vsegs_eval; cbn.
      eapply segRLs_concat.
      2: eapply IHws; eauto 1.
      eapply N'_apply_vheads_spec in E3.
      eapply segRLs_rec'_spec in E0.
      2: eauto 1.
      destruct E0 as [hsv [E0a E0b]].
      applys_eq E0b.
      destruct u.
      eapply N'_matched_vheads_spec in E2; eauto 1.
    + des_if' H.
      destruct p as [hs'0 ws'0].
      des_if' H.
      destruct p as [hs'1 ws'1].
      des_if' H.
      des_if' H.
      des_if' H.
      des_if' H.
      des_if' H.
      destruct u0.
      destruct p as [[res1 res0] res].
      inverts H.
      unfold vsegs_eval; cbn.
      eapply segRLs_concat.
      2: eapply IHws; eauto 1.
      eapply N'_applys_vheads_spec in E3.
      eapply hs_match_rec_spec in E4.
      eapply segRLs_rec'_specn in E0.
      2,3: eauto 1.
      destruct E0 as [hsv [E0a E0b]].
      applys_eq E0b.
      destruct u.
      eapply N'_matched_vheads_spec in E2; eauto 1.
Qed.

Lemma sideRLs_rec_v_spec hsN' hs ws T ws' n:
  sideRLs_rec_v hsN' hs ws T = Some (ws') ->
  sideRLs tm (N'_heads_eval hsN' n) (vside_eval (N.to_nat n) ws) (vside_eval (N.to_nat n) ws').
Proof.
  unfold sideRLs_rec_v.
  intros.
  destruct ws as [ws w].
  des_if' H.
  cbn in H.
  destruct p as [[hsN'0 hs0] ws0].
  des_if' H.
  des_if' H.
  des_if' H.
  cbn in H.
  destruct p as [ws1 w1].
  destruct u.
  inverts H.
  unfold vside_eval.
  eapply segRLs_rec_v_spec in E.
  unfold vsegs_eval in *.
  rewrite flat_map_app,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eauto 1.
  eapply sideRLs_rec_spec in E2.
  destruct E2 as [hs' [E1a E1b]].
  unfold to_side in *.
  eapply N'_matched_vheads_spec in E1.
  2: eauto.
  rewrite E1.
  rw_app.
Qed.

Section sim_sec.
Hypothesis hs_step: list head.
Hypothesis ws_init: (list seg)*seg.

Definition mstep '(ws,w) T :=
  sideRLs_rec (map (fun h => vhead_c h 1) hs_step) ws w T.

Fixpoint msteps n ws T :=
match n with
| O => Some ws
| S n => mstep ws T &&& (fun ws => msteps n ws T)
end.

Lemma mstep_spec ws T ws':
  mstep ws T = Some ws' ->
  sideRLs tm hs_step (to_side ws) (to_side ws').
Proof.
  unfold mstep.
  intros.
  destruct ws as [ws w].
  eapply sideRLs_rec_spec with (ctx:=fun _=>0) in H.
  destruct H as [hs' [I1 I2]].
  apply vheads_c_spec in I1.
  subst.
  apply I2.
Qed.

Definition hR: DH0 := fst (hd ((q0,[]),(q0,[])) hs_step).
Definition hs_step' := snd (rcons hs_step hR).
Hypothesis hs_step'_spec:
  lcons hR hs_step' = (hs_step,hR).
Hypothesis hs_step'_ne: hs_step' <> [].

Hypothesis lh: side.
Hypothesis lh_spec:
  sideRLs (flip tm) hs_step' lh lh.

Definition S' x :=
  lh {{{ (hR,R) }}} to_side x.

Definition S'' x :=
  lh {{{ (hR,R) }}} x.

Hypothesis init:
  c0 -[ tm ]->* S' ws_init.

Lemma BigStep ws ws':
  sideRLs tm hs_step (ws) (ws') ->
  S'' ws -[ tm ]->+ S'' ws'.
Proof.
  intros H.
  apply (sideRLs_concat_v2 hs_step'_spec hs_step'_ne lh_spec H).
Qed.

Definition decide_nonhalt pp T :=
  msteps pp ws_init T &&& (fun x0 =>
  mstep x0 T &&& (fun x1 =>
  mstep x1 T &&& (fun x2 =>
  interpolate' x0 x1 x2 T &&& (fun x =>
  sideRLs_rec_v (map (fun h => (N'_head_mk h (N'_c 1))) hs_step) (map (fun h => vhead_c h 1) hs_step) x T &&& (fun x' =>
  b2o (eqb (vside_O x) x0) &&& (fun _ =>
  b2o (eqb (vside_rot (vside_S x)) (vside_rot x')) &&& (fun _ =>
  Some tt
  ))))))).

Lemma msteps_spec n x T x':
  msteps n x T = Some x' ->
  S' x -[ tm ]->* S' x'.
Proof.
  gen x x'.
  induction n; cbn[msteps]; intros.
  - inverts H.
    finish.
  - des_if' H.
    inverts H.
    apply mstep_spec in E.
    apply BigStep in E.
    apply IHn in H1.
    follow100 E.
    apply H1.
Qed.

Lemma N'_heads_eval_c_spec hs i:
  hs = N'_heads_eval (map (fun h : head => N'_head_mk h (N'_c 1)) hs) i.
Proof.
  induction hs; intros.
  - trivial.
  - cbn.
    rewrite <-IHhs.
    reflexivity.
Qed.

Lemma decide_nonhalt_spec pp T:
  decide_nonhalt pp T = Some tt ->
  ~halts tm c0.
Proof.
  unfold decide_nonhalt.
  intros.
  do 7 des_if' H.
  inverts H.
  apply msteps_spec in E.
  destruct (eqb_spec (vside_O p2) p); inverts E4; subst.
  destruct (eqb_spec (vside_rot (vside_S p2)) (vside_rot p3)); inverts E5; subst.
  eapply multistep_nonhalt.
  1: follow init; apply E.
  change (S' (vside_O p2)) with (S'' (to_side (vside_O p2))).
  eapply progress_nonhalt_cond with (P:=fun x => exists i, x=vside_eval i p2).
  2: exists O; apply vside_O_spec.
  intros x [i0 HP].
  eexists; split.
  2: exists (S i0); reflexivity.
  apply BigStep.
  subst.
  eapply sideRLs_rec_v_spec with (n:=N.of_nat i0) in E3.
  rewrite Nnat.Nat2N.id in E3.
  rewrite <-vside_S_spec.
  rewrite <-(vside_rot_spec (vside_S _)).
  rewrite e.
  rewrite vside_rot_spec.
  applys_eq E3.
  apply N'_heads_eval_c_spec.
Qed.

End sim_sec.

End sec.

Require Import String.

Close Scope N.

Ltac des_all H :=
  repeat
  match type of H with
  | match ?a with _ => _ end = _ => destruct a
  | None = Some _ => inverts H
  | Some _ = Some _ => inverts H
  end.


