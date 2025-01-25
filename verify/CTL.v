From BusyCoq Require Import DHTM.
Require Import List.
Require Import Streams.
Require Import ZArith.
Require Import Lia.
From BusyCoq Require Import HashTable.
Require Uint63.

Module Type CTLCtx(K:HashableType)(Ctx:Ctx).
Export K.
Export Ctx.
Parameter config_t:Type.
Parameter global_state_t:Type.
Parameter global_state_init:config_t->global_state_t.
Parameter dfa_state_0:K.
Parameter dfa_trans:K->Sym->dir->global_state_t->(K*global_state_t).
End CTLCtx.


Definition int0 := Eval compute in (Uint63.of_Z Z0).
Definition int1 := Eval compute in (Uint63.of_Z (1%Z)).

Module CTL(K:HashableType)(Ctx:Ctx)(CTLCtx:CTLCtx K Ctx).

Module TM := DHTM Ctx. Export TM.
Export Ctx.
Export CTLCtx.

Module IdAllocK := IdAlloc K.

Module QHash := QHash Ctx.

Module SymHash := SymHash Ctx.

Module dfa_trans_V <: ValueType.
Definition V:Type := Uint63.int*Sym.
End dfa_trans_V.
Module dfa_trans_Hash := ProdHash Uint63_K SymHash.
Module dfa_trans_HashMap := HashMap dfa_trans_Hash Uint63_V.
Module dfa_trans_inv1_HashMap := HashMultimap dfa_trans_Hash Uint63_V.
Module dfa_trans_inv2_HashMap := HashMultimap Uint63_K dfa_trans_V.

Module DirHash <: HashableType.
Import HashConcat.
Definition K := dir.
Definition K_hash := fun x =>
match x with
| L => hv1
| R => hv2
end.
Definition K_eq a b :=
match a,b with
| L,L | R,R => true
| _,_ => false
end.
Lemma K_eq_spec a b: Bool.reflect (a=b) (K_eq a b).
Proof.
  destruct a,b; solve_Bool_reflect.
Qed.
End DirHash.

Module Unit_V <: ValueType.
Definition V := unit.
End Unit_V.

Record config := {
  l:Uint63.int;
  r:Uint63.int;
  s: Q;
  sgn: dir;
}.

Module config_Hash <: HashableType.
Import HashConcat.
Definition K := config.
Definition K_hash(a:K) :=
let (a0,a1,a2,a3):=a in
(a0 # a1,hash_P) ## (QHash.K_hash a2) ## (DirHash.K_hash a3).
Definition K_eq(a b:K) :=
let (a0,a1,a2,a3):=a in
let (b0,b1,b2,b3):=b in
(Uint63.eqb a0 b0) &&
(Uint63.eqb a1 b1) &&
(q_eqb a2 b2) &&
(DirHash.K_eq a3 b3).
Lemma K_eq_spec(a b:K):Bool.reflect (a=b) (K_eq a b).
Proof.
  destruct a as [a0 a1 a2 a3].
  destruct b as [b0 b1 b2 b3].
  cbn.
  destruct (Uint63_K.K_eq_spec a0 b0); solve_Bool_reflect.
  destruct (Uint63_K.K_eq_spec a1 b1); solve_Bool_reflect.
  destruct (q_eqb_spec a2 b2); solve_Bool_reflect.
  destruct (DirHash.K_eq_spec a3 b3); solve_Bool_reflect.
Qed.
End config_Hash.

Module config_HashSet := HashMap config_Hash Unit_V.

Module config_V <: ValueType.
Definition V := config.
End config_V.

Module config_Index := HashMultimap Uint63_K config_V.

Record dfa_t := {
  id_alloc: IdAllocK.id_alloc_t;
  trans: dfa_trans_HashMap.hmap_t;
  inv1_trans: dfa_trans_inv1_HashMap.hmap_t;
  inv2_trans: dfa_trans_inv2_HashMap.hmap_t;
  config_idx: config_Index.hmap_t;
}.

Record CTL_state_t := {
  ldfa: dfa_t;
  rdfa: dfa_t;
  config_set: config_HashSet.hmap_t;
  config_queue: list (Uint63.int*Sym*(Sym*dir*Q)*config);
  global_state: global_state_t;
  init_flag: bool;
}.

Inductive dfa_match(dfa:dfa_trans_HashMap.hmap_t): list Sym -> Uint63.int -> Prop :=
| dfa_match_O: dfa_match dfa [] int0
| dfa_match_S a ls x x':
  dfa_match dfa ls x ->
  dfa_trans_HashMap.hmap_get (x,a) dfa = Some x' ->
  dfa_match dfa (a::ls) x'
.

Inductive is_config(st:CTL_state_t): DH_config -> config -> Prop :=
| is_config_l l r l' r' s
  (Hlm: dfa_match st.(ldfa).(trans) l l')
  (Hrm: dfa_match st.(rdfa).(trans) r r'):
  is_config st (const s0 <* r, l *> const s0, s, L) {| l:=r'; r:=l'; s:=s; sgn:=L |}
| is_config_r l r l' r' s
  (Hlm: dfa_match st.(ldfa).(trans) l l')
  (Hrm: dfa_match st.(rdfa).(trans) r r'):
  is_config st (const s0 <* l, r *> const s0, s, R) {| l:=l'; r:=r'; s:=s; sgn:=R |}
.

Inductive is_config_in_mset(st:CTL_state_t): DH_config -> config -> Prop :=
| is_config'_intro c1 c1'
  (H_is_config: is_config st c1 c1')
  (H_in_mset: config_HashSet.hmap_get c1' st.(config_set) = Some tt):
  is_config_in_mset st c1 c1'
.

Section tm_ctx.
Hypothesis tm:TM.
Hypothesis DH_config_init:DH_cconfig.

Definition config_init:DH_config :=
DH_cconfig_to_config DH_config_init.

Inductive dfa_WF: dfa_t -> CTL_state_t -> dir -> Prop :=
| dfa_WF_intro dfa st dir

  (H_id_alloc_wf: IdAllocK.id_alloc_WF dfa.(id_alloc))
  (H_trans_wf: dfa_trans_HashMap.hmap_WF dfa.(trans))
  (H_inv1_trans_wf: dfa_trans_inv1_HashMap.hmap_WF dfa.(inv1_trans))
  (H_inv2_trans_wf: dfa_trans_inv2_HashMap.hmap_WF dfa.(inv2_trans))
  (H_config_idx_wf: config_Index.hmap_WF dfa.(config_idx))

  (H_dfa_state0: dfa_trans_HashMap.hmap_get (int0,s0) dfa.(trans) = Some int0)
  (H_inv1_trans:
    forall x y z,
    dfa_trans_HashMap.hmap_get (x,y) dfa.(trans) = Some z ->
    In x (dfa_trans_inv1_HashMap.hmap_get (z,y) dfa.(inv1_trans)))
  (H_inv2_trans:
    forall x y z,
    dfa_trans_HashMap.hmap_get (x,y) dfa.(trans) = Some z ->
    In (x,y) (dfa_trans_inv2_HashMap.hmap_get z dfa.(inv2_trans)))
  (H_config_idx:
    forall c,
    config_HashSet.hmap_get c st.(config_set) = Some tt ->
    c.(sgn) = dir ->
    In c (config_Index.hmap_get c.(r) dfa.(config_idx))):
  dfa_WF dfa st dir
.

Definition get_dfa(st:CTL_state_t)(sgn:dir) :=
match sgn with
| L => st.(ldfa)
| R => st.(rdfa)
end.

Definition next_config(cfg:(Uint63.int * Sym * (Sym * dir * Q) * config))(st:CTL_state_t):option config :=
let '(x,y,y',c1'):=cfg in
let (l0,r0,s0,sgn0):=c1' in
let '(y1,sgn1,s1):=y' in
if DirHash.K_eq sgn0 sgn1 then
  dfa_trans_HashMap.hmap_get (l0,y1) (get_dfa st (dir_rev sgn0)).(trans) &&& (fun l1 =>
    Some {| l:=l1; r:=x; s:=s1; sgn:=sgn1 |})
else
  dfa_trans_HashMap.hmap_get (x,y1) (get_dfa st sgn0).(trans) &&& (fun r1 =>
    Some {| l:=r1; r:=l0; s:=s1; sgn:=sgn1 |})
.

Inductive CTL_state_WF: CTL_state_t -> Prop :=
| CTL_state_WF_intro st
  (HO: st.(init_flag) = false \/
    exists c1',
    (is_config_in_mset st config_init c1'))
  (HS: forall c1',
    config_HashSet.hmap_get c1' st.(config_set) = Some tt ->
    (forall x y,
      let (l0,r0,s0,sgn0):=c1' in
      dfa_trans_HashMap.hmap_get (x,y) (get_dfa st sgn0).(trans) = Some r0 ->
      exists y',
      tm (s0,y) = Some y' /\
      (In (x,y,y',c1') st.(config_queue) \/
      (exists c2', next_config (x,y,y',c1') st = Some c2' /\ config_HashSet.hmap_get c2' st.(config_set) = Some tt)
      )))
  (HL: dfa_WF st.(ldfa) st L)
  (HR: dfa_WF st.(rdfa) st R)
  (H_config_set_wf: config_HashSet.hmap_WF st.(config_set)):
  CTL_state_WF st
.

Definition get_cs' (x:Uint63.int) (y:Sym) cs :=
List.fold_right (fun c cs0 => cs0 &&& (fun cs1 => tm (c.(s),y) &&& (fun y' => Some ((x,y,y',c)::cs1)))) (Some nil) cs.

Definition dfa_add_trans(st:CTL_state_t)(x:Uint63.int)(y:Sym)(sgn:dir):option CTL_state_t :=
let dfa := get_dfa st sgn in
IdAllocK.get_key x dfa.(id_alloc) &&& (fun x' =>
let (z',gs) := dfa_trans x' y sgn st.(global_state) in
IdAllocK.get_or_alloc_id z' dfa.(id_alloc) &&& (fun '(z,id_alloc') =>
let trans' := dfa_trans_HashMap.hmap_set (x,y) z dfa.(trans) in
let inv1_trans' := dfa_trans_inv1_HashMap.hmap_add (z,y) x dfa.(inv1_trans) in
let inv2_trans' := dfa_trans_inv2_HashMap.hmap_add z (x,y) dfa.(inv2_trans) in
let cs := config_Index.hmap_get z dfa.(config_idx) in
get_cs' x y cs &&& (fun cs' =>
let dfa' := {| id_alloc := id_alloc'; trans := trans'; inv1_trans := inv1_trans'; inv2_trans := inv2_trans'; config_idx := dfa.(config_idx) |} in
Some {|
  ldfa :=
  match sgn with
  | L => dfa'
  | R => st.(ldfa)
  end;
  rdfa :=
  match sgn with
  | L => st.(rdfa)
  | R => dfa'
  end;
  config_set := st.(config_set);
  config_queue := cs' ++ st.(config_queue);
  global_state := gs;
  init_flag := st.(init_flag);
|}
))).

Definition dfa_add_config(dfa:dfa_t)(sgn0:dir)(c1':config):dfa_t :=
if DirHash.K_eq c1'.(sgn) sgn0 then
{|
  id_alloc := dfa.(id_alloc);
  trans := dfa.(trans);
  inv1_trans := dfa.(inv1_trans);
  inv2_trans := dfa.(inv2_trans);
  config_idx := config_Index.hmap_add c1'.(r) c1' dfa.(config_idx)
|}
else dfa.

Definition get_cs'' c1' (xys:list (Uint63.int*Sym)) :=
  List.fold_right (fun '(x,y) cs0 => cs0 &&& (fun cs1 => tm (c1'.(s),y) &&& (fun y' => Some ((x,y,y',c1')::cs1)))) (Some nil) xys.

Definition config_push(st:CTL_state_t)(c1':config):option CTL_state_t :=
match config_HashSet.hmap_add c1' tt st.(config_set) with
| None =>
  Some {|
    ldfa := st.(ldfa);
    rdfa := st.(rdfa);
    config_set := st.(config_set);
    config_queue := List.tl st.(config_queue);
    global_state := st.(global_state);
    init_flag := st.(init_flag);
  |}
| Some config_set' =>
  let dfa := get_dfa st c1'.(sgn) in
  let xys := dfa_trans_inv2_HashMap.hmap_get c1'.(r) dfa.(inv2_trans) in
  get_cs'' c1' xys &&& (fun cs' =>
  Some {|
    ldfa := dfa_add_config st.(ldfa) L c1';
    rdfa := dfa_add_config st.(rdfa) R c1';
    config_set := config_set';
    config_queue := cs' ++ List.tl st.(config_queue);
    global_state := st.(global_state);
   init_flag := st.(init_flag);
  |})
end.

Definition CTL_step(st:CTL_state_t):option CTL_state_t :=
match st.(config_queue) with
| (x,y,y',c1')::q0 =>
  let (l0,r0,s0,sgn0):=c1' in
  let '(y1,sgn1,s1):=y' in
  if DirHash.K_eq sgn0 sgn1 then
    match dfa_trans_HashMap.hmap_get (l0,y1) (get_dfa st (dir_rev sgn0)).(trans) with
    | Some l1 => (config_push st {| l:=l1; r:=x; s:=s1; sgn:=sgn1 |})
    | None => dfa_add_trans st l0 y1 (dir_rev sgn0)
    end
  else
    match dfa_trans_HashMap.hmap_get (x,y1) (get_dfa st sgn0).(trans) with
    | Some r1 => (config_push st {| l:=r1; r:=l0; s:=s1; sgn:=sgn1 |})
    | None => dfa_add_trans st x y1 sgn0
    end
| _ => None
end.

Definition dfa_0 len := 
IdAllocK.get_or_alloc_id dfa_state_0 (IdAllocK.id_alloc_make len) &&& (fun '(z0,id_alloc') =>
Some {|
  id_alloc := id_alloc';
  trans := dfa_trans_HashMap.hmap_set (z0,s0) z0 (dfa_trans_HashMap.hmap_make len);
  inv1_trans := dfa_trans_inv1_HashMap.hmap_add (z0,s0) z0 (dfa_trans_inv1_HashMap.hmap_make len);
  inv2_trans := dfa_trans_inv2_HashMap.hmap_add z0 (z0,s0) (dfa_trans_inv2_HashMap.hmap_make len);
  config_idx := config_Index.hmap_make len;
|}).

Definition CTL_state_0 cfg len :=
dfa_0 len &&& (fun dfa01 =>
dfa_0 len &&& (fun dfa02 =>
Some {|
  ldfa := dfa01;
  rdfa := dfa02;
  config_set := config_HashSet.hmap_make len;
  config_queue := nil;
  global_state := global_state_init cfg;
  init_flag := false;
|})).

Definition dfa_get_trans st x y sgn0 :=
  dfa_trans_HashMap.hmap_get (x,y) (get_dfa st sgn0).(trans).

Definition CTL_add_side st sgn0 ls :=
List.fold_right (fun y st => st &&& (fun '(st,x) => 
  match dfa_get_trans st x y sgn0 with
  | Some z => Some (st,z)
  | None => dfa_add_trans st x y sgn0 &&&
    (fun st => dfa_get_trans st x y sgn0 &&& (fun z => Some (st,z)))
  end
)) (Some (st,int0)) ls.

Definition CTL_state_1 cfg len :=
let '(l0,r0,s2,sgn0):=DH_config_init in
CTL_state_0 cfg len &&& (fun st =>
CTL_add_side st (dir_rev sgn0) l0 &&& (fun '(st,_) =>
CTL_add_side st sgn0 r0 &&& (fun '(st,_) =>
Some st
))).

Definition CTL_match_side st sgn0 ls :=
List.fold_right (fun y x => x &&& (fun x => 
  dfa_get_trans st x y sgn0
)) (Some (int0)) ls.

Definition CTL_state_init cfg len :=
let '(l0,r0,s2,sgn0):=DH_config_init in
CTL_state_1 cfg len &&& (fun st =>
CTL_match_side st (dir_rev sgn0) l0 &&& (fun l1 =>
CTL_match_side st sgn0 r0 &&& (fun r1 =>
  let c1' := {| l:=l1; r:=r1; s:=s2; sgn:=sgn0 |} in
  let config_set' := config_HashSet.hmap_set c1' tt st.(config_set) in
  let dfa := get_dfa st c1'.(sgn) in
  let xys := dfa_trans_inv2_HashMap.hmap_get c1'.(r) dfa.(inv2_trans) in
  get_cs'' c1' xys &&& (fun cs' =>
  Some {|
    ldfa := dfa_add_config st.(ldfa) L c1';
    rdfa := dfa_add_config st.(rdfa) R c1';
    config_set := config_set';
    config_queue := cs' ++ st.(config_queue);
    global_state := st.(global_state);
    init_flag := true;
  |})
))).

Definition CTL_steps cfg len n :=
N_iter_until (fun st =>
match CTL_step st with
| Some st' => inl st'
| None => inr (Some st)
end)
(match CTL_state_init cfg len with
| Some st => inl st
| None => inr None
end) n.

Definition CTL_decide_nonhalt cfg len T :=
match CTL_steps cfg len T with
| inr (Some st) =>
  st.(init_flag) &&
  match st.(config_queue) with
  | nil => true
  | _ => false
  end
| _ => false
end.




Ltac cbn_proj :=
  cbn[ldfa]; cbn[rdfa]; cbn[config_set]; cbn[config_queue]; cbn[global_state]; cbn[init_flag];
  cbn[id_alloc]; cbn[config_idx]; cbn[trans]; cbn[inv1_trans]; cbn[inv2_trans].

Lemma CTL_state_0_WF cfg len:
  match CTL_state_0 cfg len with
  | Some st => CTL_state_WF st
  | None => True
  end.
Proof.
  unfold CTL_state_0,dfa_0.
  unfold dfa_add_trans,if_Some.
  destruct (IdAllocK.get_or_alloc_id dfa_state_0 (IdAllocK.id_alloc_make len)) as [[z id_alloc']|] eqn:E1; trivial.
  assert (z=int0). {
    unfold IdAllocK.get_or_alloc_id,IdAllocK.id_alloc_make in E1.
    rewrite IdAllocK.MapToId.hmap_get_make in E1.
    inverts E1.
    reflexivity.
  }
  subst z.
  constructor;
  cbn[get_dfa]; cbn_proj.
  - left. reflexivity.
  - intros c H.
    rewrite config_HashSet.hmap_get_make in H. congruence.
  - constructor; cbn_proj.
    + epose proof (IdAllocK.get_or_alloc_id_WF _ _ _) as H.
      rewrite E1 in H.
      apply H.
      Unshelve.
      apply IdAllocK.id_alloc_make_WF.
    + apply dfa_trans_HashMap.hmap_set_WF,dfa_trans_HashMap.hmap_make_WF.
    + apply dfa_trans_inv1_HashMap.hmap_add_WF,dfa_trans_inv1_HashMap.hmap_make_WF.
    + apply dfa_trans_inv2_HashMap.hmap_add_WF,dfa_trans_inv2_HashMap.hmap_make_WF. 
    + apply config_Index.hmap_make_WF.
    + apply dfa_trans_HashMap.hmap_get_set_same,dfa_trans_HashMap.hmap_make_WF.
    + intros x y z E.
      destruct (dfa_trans_Hash.K_eq_spec (x,y) (int0,s0)).
      * inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same in E.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        inverts E.
        rewrite dfa_trans_inv1_HashMap.hmap_get_add_same.
        2: apply dfa_trans_inv1_HashMap.hmap_make_WF.
        left; reflexivity.
      * rewrite dfa_trans_HashMap.hmap_get_set_other in E; auto 1.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        rewrite dfa_trans_HashMap.hmap_get_make in E; congruence.
    + intros x y z E.
      destruct (dfa_trans_Hash.K_eq_spec (x,y) (int0,s0)).
      * inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same in E.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        inverts E.
        rewrite dfa_trans_inv2_HashMap.hmap_get_add_same.
        2: apply dfa_trans_inv2_HashMap.hmap_make_WF.
        left; reflexivity.
      * rewrite dfa_trans_HashMap.hmap_get_set_other in E; auto 1.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        rewrite dfa_trans_HashMap.hmap_get_make in E; congruence.
    + intros c Hc Hs.
      rewrite config_HashSet.hmap_get_make in Hc. congruence.
  - constructor; cbn_proj.
    + epose proof (IdAllocK.get_or_alloc_id_WF _ _ _) as H.
      rewrite E1 in H.
      apply H.
      Unshelve.
      apply IdAllocK.id_alloc_make_WF.
    + apply dfa_trans_HashMap.hmap_set_WF,dfa_trans_HashMap.hmap_make_WF.
    + apply dfa_trans_inv1_HashMap.hmap_add_WF,dfa_trans_inv1_HashMap.hmap_make_WF.
    + apply dfa_trans_inv2_HashMap.hmap_add_WF,dfa_trans_inv2_HashMap.hmap_make_WF. 
    + apply config_Index.hmap_make_WF.
    + apply dfa_trans_HashMap.hmap_get_set_same,dfa_trans_HashMap.hmap_make_WF.
    + intros x y z E.
      destruct (dfa_trans_Hash.K_eq_spec (x,y) (int0,s0)).
      * inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same in E.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        inverts E.
        rewrite dfa_trans_inv1_HashMap.hmap_get_add_same.
        2: apply dfa_trans_inv1_HashMap.hmap_make_WF.
        left; reflexivity.
      * rewrite dfa_trans_HashMap.hmap_get_set_other in E; auto 1.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        rewrite dfa_trans_HashMap.hmap_get_make in E; congruence.
    + intros x y z E.
      destruct (dfa_trans_Hash.K_eq_spec (x,y) (int0,s0)).
      * inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same in E.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        inverts E.
        rewrite dfa_trans_inv2_HashMap.hmap_get_add_same.
        2: apply dfa_trans_inv2_HashMap.hmap_make_WF.
        left; reflexivity.
      * rewrite dfa_trans_HashMap.hmap_get_set_other in E; auto 1.
        2: apply dfa_trans_HashMap.hmap_make_WF.
        rewrite dfa_trans_HashMap.hmap_get_make in E; congruence.
    + intros c Hc Hs.
      rewrite config_HashSet.hmap_get_make in Hc. congruence.
  - apply config_HashSet.hmap_make_WF.
Qed.



Lemma dfa_add_trans_match x y z dfa l0 l':
  dfa_trans_HashMap.hmap_WF dfa ->
  dfa_trans_HashMap.hmap_get (x, y) dfa = None ->
  dfa_match dfa l0 l' ->
  dfa_match (dfa_trans_HashMap.hmap_set (x, y) z dfa) l0 l'.
Proof.
  intros Hwf Hn.
  gen l'.
  induction l0; intros l' H.
  - inverts H.
    apply dfa_match_O.
  - inversion H; subst.
    eapply dfa_match_S.
    + apply IHl0,H2.
    + destruct (dfa_trans_Hash.K_eq_spec (x0,a) (x,y)).
      * inverts e.
        unfold Uint63_K.K in Hn.
        congruence.
      * rewrite dfa_trans_HashMap.hmap_get_set_other; auto.
Qed.

Lemma get_cs'_spec x y c ls a0:
  In c ls ->
  get_cs' x y ls = Some a0 ->
  exists y',
    tm (c.(s), y) = Some y' /\
    In (x, y, y', c) a0.
Proof.
  gen a0.
  unfold get_cs'.
  induction ls; intros a0.
  1: cbn; tauto.
  intros [H|H].
  - subst a.
    cbn[fold_right].
    unfold if_Some.
    do 2 match goal with
    | |- (match ?a with _ => _ end = _ -> _) => destruct a; try congruence
    end.
    intros H. inverts H.
    eexists.
    split; cbn; auto.
  - cbn[fold_right].
    match goal with
    | |- ?a &&& _ = _ -> _ => destruct a eqn:E
    end.
    2: unfold if_Some; congruence.
    specialize (IHls l0 H (eq_refl _)).
    unfold if_Some.
    destruct (tm (s a, y)); try congruence.
    intros H0. inverts H0.
    destruct IHls as [y' [H1 H2]].
    exists y'.
    split.
    1: apply H1.
    right. apply H2.
Qed.


Lemma dfa_add_trans_WF st x y sgn:
dfa_trans_HashMap.hmap_get (x,y) (get_dfa st sgn).(trans) = None ->
  CTL_state_WF st ->
  match dfa_add_trans st x y sgn with
  | None => True
  | Some st' =>
    CTL_state_WF st'
  end.
Proof.
  intros Hn Hwf.
  unfold dfa_add_trans,if_Some.
  destruct (IdAllocK.get_key x (id_alloc (get_dfa st sgn))) eqn:Eia; trivial.
  destruct (dfa_trans k y sgn (global_state st)) as [z' gs] eqn:Edt.
  destruct (IdAllocK.get_or_alloc_id z' (id_alloc (get_dfa st sgn))) as [[z id_alloc']|] eqn:Eia2; trivial.
  destruct (get_cs' x y (config_Index.hmap_get z (config_idx (get_dfa st sgn)))) as [a0|] eqn:Ecs'; trivial.
  destruct Hwf.
  constructor.
  - destruct HO as [HO|[c1' HO]].
    1: tauto.
    right.
    exists c1'.
    destruct HO.
    constructor.
    + destruct H_is_config.
      * constructor.
        -- destruct sgn; cbn[ldfa]; cbn[trans]; cbn[get_dfa].
          ++ apply dfa_add_trans_match; try assumption.
            destruct HL; assumption.
          ++ assumption.
        -- destruct sgn; cbn[rdfa]; cbn[trans]; cbn[get_dfa].
          ++ assumption.
          ++ apply dfa_add_trans_match; try assumption.
            destruct HR; assumption.
      * constructor.
        -- destruct sgn; cbn[ldfa]; cbn[trans]; cbn[get_dfa].
          ++ apply dfa_add_trans_match; try assumption.
            destruct HL; assumption.
          ++ assumption.
        -- destruct sgn; cbn[rdfa]; cbn[trans]; cbn[get_dfa].
          ++ assumption.
          ++ apply dfa_add_trans_match; try assumption.
            destruct HR; assumption.
    + assumption.
  - cbn[config_set].
    intros c1' H x0 y0.
    specialize (HS c1' H x0 y0).
    destruct c1' as [l0 r0 s2 sgn0].
    cbn[trans]. cbn[config_queue].
    destruct sgn0; cbn[get_dfa].
    + cbn[ldfa].
      destruct sgn.
      * cbn[trans].
        destruct (dfa_trans_Hash.K_eq_spec (x0,y0) (x,y)).
        1: {
          inverts e.
          inverts HL.
          rewrite dfa_trans_HashMap.hmap_get_set_same; auto 1.
          intros E. inverts E.
          cbn[get_dfa] in Ecs'.
          specialize (H_config_idx _ H (eq_refl _)).
          cbn in H_config_idx.
          destruct (get_cs'_spec _ _ _ _ _ H_config_idx Ecs') as [y' [H2 H3]].
          exists y'.
          split. 1: apply H2.
          left. rewrite in_app_iff. left. apply H3.
        }
        rewrite dfa_trans_HashMap.hmap_get_set_other; auto 1.
        2: inverts HL; auto 1.
        intros H0.
        specialize (HS H0).
        cbn[config_queue].
        destruct HS as [y' [HS1 HS2]].
        exists y'.
        split. 1: apply HS1.
        destruct HS2 as [HS2|[c2' [HS2 HS3]]].
        1: left; rewrite in_app_iff; tauto.
        right.
        exists c2'.
        split. 2: apply HS3.
        gen HS2.
        unfold next_config.
        cbn[dir_rev]. cbn[get_dfa]. cbn[ldfa]. cbn[rdfa]. cbn[trans].
        destruct y' as [[y1 sgn1] s1].
        destruct sgn1; cbn[DirHash.K_eq]. 1: tauto.
        unfold if_Some.
        destruct (dfa_trans_HashMap.hmap_get (x0, y1) (trans (ldfa st))) eqn:E;
        unfold Uint63_K.K,Uint63_V.V in E;
        rewrite E.
        2: congruence.
        destruct (dfa_trans_Hash.K_eq_spec (x0,y1) (x,y)).
        -- inverts e. cbn in Hn. unfold Uint63_K.K,SymHash.K in Hn. congruence.
        -- destruct HL; rewrite dfa_trans_HashMap.hmap_get_set_other; auto 1.
          rewrite E. tauto.
      * intros H0.
        specialize (HS H0).
        cbn[config_queue].
        destruct HS as [y' [HS1 HS2]].
        exists y'.
        split. 1: apply HS1.
        destruct HS2 as [HS2|[c2' [HS2 HS3]]].
        1: left; rewrite in_app_iff; tauto.
        right.
        exists c2'.
        split. 2: apply HS3.
        gen HS2.
        unfold next_config.
        cbn[dir_rev]. cbn[get_dfa]. cbn[ldfa]. cbn[rdfa]. cbn[trans].
        destruct y' as [[y1 sgn1] s1].
        destruct sgn1; cbn[DirHash.K_eq]. 2: tauto.
        unfold if_Some.
        destruct (dfa_trans_HashMap.hmap_get (l0, y1) (trans (rdfa st))) eqn:E.
        2: congruence.
        destruct (dfa_trans_Hash.K_eq_spec (l0,y1) (x,y)).
        -- inverts e. cbn in Hn. unfold Uint63_K.K,SymHash.K in Hn. congruence.
        -- destruct HR; rewrite dfa_trans_HashMap.hmap_get_set_other; auto 1.
          rewrite E. tauto.
    + cbn[rdfa].
      destruct sgn.
      * intros H0.
        specialize (HS H0).
        cbn[config_queue].
        destruct HS as [y' [HS1 HS2]].
        exists y'.
        split. 1: apply HS1.
        destruct HS2 as [HS2|[c2' [HS2 HS3]]].
        1: left; rewrite in_app_iff; tauto.
        right.
        exists c2'.
        split. 2: apply HS3.
        gen HS2.
        unfold next_config.
        cbn[dir_rev]. cbn[get_dfa]. cbn[ldfa]. cbn[rdfa]. cbn[trans].
        destruct y' as [[y1 sgn1] s1].
        destruct sgn1; cbn[DirHash.K_eq]. 1: tauto.
        unfold if_Some.
        destruct (dfa_trans_HashMap.hmap_get (l0, y1) (trans (ldfa st))) eqn:E.
        2: congruence.
        destruct (dfa_trans_Hash.K_eq_spec (l0,y1) (x,y)).
        -- inverts e. cbn in Hn. unfold Uint63_K.K,SymHash.K in Hn. congruence.
        -- destruct HL; rewrite dfa_trans_HashMap.hmap_get_set_other; auto 1.
          rewrite E. tauto.
      * cbn[trans].
        destruct (dfa_trans_Hash.K_eq_spec (x0,y0) (x,y)).
        1: {
          inverts e.
          inverts HR.
          rewrite dfa_trans_HashMap.hmap_get_set_same; auto 1.
          intros E. inverts E.
          cbn[get_dfa] in Ecs'.
          specialize (H_config_idx _ H (eq_refl _)).
          cbn in H_config_idx.
          destruct (get_cs'_spec _ _ _ _ _ H_config_idx Ecs') as [y' [H2 H3]].
          exists y'.
          split. 1: apply H2.
          left. rewrite in_app_iff. left. apply H3.
        }
        rewrite dfa_trans_HashMap.hmap_get_set_other; auto 1.
        2: inverts HR; auto 1.
        intros H0.
        specialize (HS H0).
        cbn[config_queue].
        destruct HS as [y' [HS1 HS2]].
        exists y'.
        split. 1: apply HS1.
        destruct HS2 as [HS2|[c2' [HS2 HS3]]].
        1: left; rewrite in_app_iff; tauto.
        right.
        exists c2'.
        split. 2: apply HS3.
        gen HS2.
        unfold next_config.
        cbn[dir_rev]. cbn[get_dfa]. cbn[ldfa]. cbn[rdfa]. cbn[trans].
        destruct y' as [[y1 sgn1] s1].
        destruct sgn1; cbn[DirHash.K_eq]. 2: tauto.
        unfold if_Some.
        destruct (dfa_trans_HashMap.hmap_get (x0, y1) (trans (rdfa st))) eqn:E;
        unfold Uint63_K.K,Uint63_V.V in E;
        rewrite E.
        2: congruence.
        destruct (dfa_trans_Hash.K_eq_spec (x0,y1) (x,y)).
        -- inverts e. cbn in Hn. unfold Uint63_K.K,SymHash.K in Hn. congruence.
        -- destruct HR; rewrite dfa_trans_HashMap.hmap_get_set_other; auto 1.
          rewrite E. tauto.
  - cbn[ldfa].
    inverts HL.
    destruct sgn.
    2: constructor; assumption.
    constructor.
    * cbn[id_alloc].
      epose proof (IdAllocK.get_or_alloc_id_WF _ _ H_id_alloc_wf) as H.
      cbn[get_dfa] in Eia2.
      rewrite Eia2 in H.
      apply H.
    * cbn[trans].
      apply dfa_trans_HashMap.hmap_set_WF; assumption.
    * cbn[inv1_trans].
      apply dfa_trans_inv1_HashMap.hmap_add_WF; assumption.
    * cbn[inv2_trans].
      apply dfa_trans_inv2_HashMap.hmap_add_WF; assumption.
    * assumption.
    * cbn[trans].
      destruct (dfa_trans_Hash.K_eq_spec (int0,s0) (x,y)).
      -- rewrite <-e in Hn. cbn[get_dfa] in Hn.
        congruence.
      -- rewrite dfa_trans_HashMap.hmap_get_set_other; assumption.
    * cbn[trans]. cbn[inv1_trans].
      intros x0 y0 z0.
      destruct (dfa_trans_Hash.K_eq_spec (x0,y0) (x,y)).
      -- inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same; try assumption.
        intros Hz; inverts Hz.
        rewrite dfa_trans_inv1_HashMap.hmap_get_add_same; try assumption.
        left. reflexivity.
      -- rewrite dfa_trans_HashMap.hmap_get_set_other; try assumption.
        intros H.
        specialize (H_inv1_trans x0 y0 z0 H).
        apply dfa_trans_inv1_HashMap.hmap_get_add_mono; assumption.
    * cbn[trans]. cbn[inv2_trans].
      intros x0 y0 z0.
      destruct (dfa_trans_Hash.K_eq_spec (x0,y0) (x,y)).
      -- inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same; try assumption.
        intros Hz; inverts Hz.
        rewrite dfa_trans_inv2_HashMap.hmap_get_add_same; try assumption.
        left. reflexivity.
      -- rewrite dfa_trans_HashMap.hmap_get_set_other; try assumption.
        intros H.
        specialize (H_inv2_trans x0 y0 z0 H).
        apply dfa_trans_inv2_HashMap.hmap_get_add_mono; assumption.
    * assumption.
  - cbn[rdfa].
    inverts HR.
    destruct sgn.
    1: constructor; assumption.
    constructor.
    * cbn[id_alloc].
      epose proof (IdAllocK.get_or_alloc_id_WF _ _ H_id_alloc_wf) as H.
      cbn[get_dfa] in Eia2.
      rewrite Eia2 in H.
      apply H.
    * cbn[trans].
      apply dfa_trans_HashMap.hmap_set_WF; assumption.
    * cbn[inv1_trans].
      apply dfa_trans_inv1_HashMap.hmap_add_WF; assumption.
    * cbn[inv2_trans].
      apply dfa_trans_inv2_HashMap.hmap_add_WF; assumption.
    * assumption.
    * cbn[trans].
      destruct (dfa_trans_Hash.K_eq_spec (int0,s0) (x,y)).
      -- rewrite <-e in Hn. cbn[get_dfa] in Hn.
        congruence.
      -- rewrite dfa_trans_HashMap.hmap_get_set_other; assumption.
    * cbn[trans]. cbn[inv1_trans].
      intros x0 y0 z0.
      destruct (dfa_trans_Hash.K_eq_spec (x0,y0) (x,y)).
      -- inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same; try assumption.
        intros Hz; inverts Hz.
        rewrite dfa_trans_inv1_HashMap.hmap_get_add_same; try assumption.
        left. reflexivity.
      -- rewrite dfa_trans_HashMap.hmap_get_set_other; try assumption.
        intros H.
        specialize (H_inv1_trans x0 y0 z0 H).
        apply dfa_trans_inv1_HashMap.hmap_get_add_mono; assumption.
    * cbn[trans]. cbn[inv2_trans].
      intros x0 y0 z0.
      destruct (dfa_trans_Hash.K_eq_spec (x0,y0) (x,y)).
      -- inverts e.
        rewrite dfa_trans_HashMap.hmap_get_set_same; try assumption.
        intros Hz; inverts Hz.
        rewrite dfa_trans_inv2_HashMap.hmap_get_add_same; try assumption.
        left. reflexivity.
      -- rewrite dfa_trans_HashMap.hmap_get_set_other; try assumption.
        intros H.
        specialize (H_inv2_trans x0 y0 z0 H).
        apply dfa_trans_inv2_HashMap.hmap_get_add_mono; assumption.
    * assumption.
  - assumption.
Qed.

Lemma CTL_add_side_WF st sgn0 ls:
  CTL_state_WF st ->
  match CTL_add_side st sgn0 ls with
  | None => True
  | Some (st',_) => CTL_state_WF st'
  end.
Proof.
  intros H.
  unfold CTL_add_side.
  induction ls.
  1: apply H.
  cbn[fold_right].
  match goal with
  | |- match ?a &&& _ with _ => _ end => destruct a as [[st' z]|]; trivial
  end.
  unfold if_Some.
  destruct (dfa_get_trans st' z a sgn0) eqn:E; auto 1.
  pose proof (dfa_add_trans_WF st' z a sgn0 E IHls).
  destruct (dfa_add_trans st' z a sgn0); trivial.
  destruct (dfa_get_trans c z a sgn0); trivial.
Qed.

Lemma CTL_state_1_WF cfg len:
  match CTL_state_1 cfg len with
  | None => True
  | Some st => CTL_state_WF st
  end.
Proof.
  unfold CTL_state_1.
  destruct (DH_config_init) as [[[l0 r0] s2] sgn0].
  unfold if_Some.
  pose proof (CTL_state_0_WF cfg len).
  destruct (CTL_state_0 cfg len); trivial.
  pose proof (CTL_add_side_WF c (dir_rev sgn0) l0 H).
  destruct (CTL_add_side c (dir_rev sgn0) l0) as [[st _]|]; trivial.
  pose proof (CTL_add_side_WF st sgn0 r0 H0).
  destruct (CTL_add_side st sgn0 r0) as [[st0 _]|]; trivial.
Qed.

Lemma CTL_match_side_WF st sgn0 ls:
  CTL_state_WF st ->
  match CTL_match_side st sgn0 ls with
  | None => True
  | Some z => dfa_match (get_dfa st sgn0).(trans) ls z
  end.
Proof.
  intros H.
  unfold CTL_match_side.
  induction ls.
  1: constructor.
  cbn[fold_right].
  match goal with
  | |- match ?a &&& _ with _ => _ end => destruct a as [z|]; trivial
  end.
  unfold if_Some.
  destruct (dfa_get_trans st z a sgn0) eqn:E; auto 1.
  eapply dfa_match_S; eauto.
Qed.



Lemma dfa_add_config_trans dfa sgn0 c:
  ((dfa_add_config dfa sgn0 c).(trans)) = (dfa.(trans)).
Proof.
  unfold dfa_add_config.
  destruct (DirHash.K_eq (sgn c) sgn0); reflexivity.
Qed.
Lemma dfa_add_config_inv1_trans dfa sgn0 c:
  ((dfa_add_config dfa sgn0 c).(inv1_trans)) = (dfa.(inv1_trans)).
Proof.
  unfold dfa_add_config.
  destruct (DirHash.K_eq (sgn c) sgn0); reflexivity.
Qed.
Lemma dfa_add_config_inv2_trans dfa sgn0 c:
  ((dfa_add_config dfa sgn0 c).(inv2_trans)) = (dfa.(inv2_trans)).
Proof.
  unfold dfa_add_config.
  destruct (DirHash.K_eq (sgn c) sgn0); reflexivity.
Qed.

Lemma dfa_add_config_id_alloc dfa sgn0 c:
  ((dfa_add_config dfa sgn0 c).(id_alloc)) = (dfa.(id_alloc)).
Proof.
  unfold dfa_add_config.
  destruct (DirHash.K_eq (sgn c) sgn0); reflexivity.
Qed.

Lemma get_cs''_spec x y c ls l0:
In (x, y) ls ->
get_cs'' c ls = Some l0 ->
exists y' : Sym * dir * Q,
  tm (c.(s), y) = Some y' /\
  In (x, y, y', c) l0.
Proof.
  unfold get_cs''.
  gen l0.
  induction ls; intros l0.
  - cbn. tauto.
  - intros [H|H].
    + subst a.
      unfold if_Some.
      cbn.
      do 2 match goal with
      | |- (match ?a with _ => _ end = _ -> _) => destruct a; try congruence
      end.
      intros H. inverts H.
      eexists.
      split; cbn; auto.
    + destruct a as [x0 y0].
      cbn[fold_right].
      match goal with
      | |- ?a &&& _ = _ -> _ => destruct a eqn:E
      end.
      2: unfold if_Some; congruence.
      specialize (IHls l1 H (eq_refl _)).
      unfold if_Some.
      destruct (tm (s c, y0)); try congruence.
      intros H0. inverts H0.
      destruct IHls as [y' [H1 H2]].
      exists y'.
      split.
      1: apply H1.
      right. apply H2.
Qed.

Lemma CTL_state_init_WF cfg len:
  match CTL_state_init cfg len with
  | Some st' => CTL_state_WF st'
  | None => True
  end.
Proof.
  unfold CTL_state_init.
  destruct DH_config_init as [[[l0 r0] s2] sgn0] eqn:Edci.
  unfold if_Some.
  pose proof (CTL_state_1_WF cfg len) as H1.
  destruct (CTL_state_1 cfg len) as [st|]; trivial.
  pose proof (CTL_match_side_WF st (dir_rev sgn0) l0 H1) as H2.
  destruct (CTL_match_side st (dir_rev sgn0) l0) as [l1|]; trivial.
  pose proof (CTL_match_side_WF st sgn0 r0 H1) as H3.
  destruct (CTL_match_side st sgn0 r0) as [r1|]; trivial.
  cbn[r]. cbn[sgn].
  cbn[get_dfa].
  remember ((dfa_trans_inv2_HashMap.hmap_get r1 (inv2_trans (get_dfa st sgn0)))) as ls.
  destruct (get_cs'' {| l := l1; r := r1; s := s2; sgn := sgn0 |} ls) eqn:E1; trivial.
  destruct H1.
  constructor.
  - right.
    exists {| l := l1; r := r1; s := s2; sgn := sgn0 |}.
    unfold config_init.
    rewrite Edci.
    constructor.
    + destruct sgn0;
      constructor; assumption.
    + apply config_HashSet.hmap_get_set_same; assumption.
  - cbn_proj.
    intros c1' Hc1'.
    destruct (config_Hash.K_eq_spec c1' {| l := l1; r := r1; s := s2; sgn := sgn0 |}),sgn0.
    + subst c1'. cbn[get_dfa]. cbn_proj.
      rewrite dfa_add_config_trans.
      intros x y H.
      epose proof (get_cs''_spec _ _ _ _ _ _ E1) as H0.
      destruct H0 as [y' [H0 H1]].
      exists y'.
      split. 1: apply H0.
      left. rewrite in_app_iff. left. apply H1.
      Unshelve.
      subst ls.
      gen H.
      inverts HL.
      apply H_inv2_trans.
    + subst c1'. cbn[get_dfa]. cbn_proj.
      rewrite dfa_add_config_trans.
      intros x y H.
      epose proof (get_cs''_spec _ _ _ _ _ _ E1) as H0.
      destruct H0 as [y' [H0 H1]].
      exists y'.
      split. 1: apply H0.
      left. rewrite in_app_iff. left. apply H1.
      Unshelve.
      subst ls.
      gen H.
      inverts HR.
      apply H_inv2_trans.
    + rewrite config_HashSet.hmap_get_set_other in Hc1'; auto 1.
      intros x y.
      specialize (HS c1' Hc1' x y).
      destruct c1' as [l3 r2 s3 sgn0].
      intros H.
      unshelve epose proof (HS _) as HS.
      {
        gen H.
        destruct sgn0; cbn[get_dfa]; cbn_proj;
        rewrite dfa_add_config_trans; tauto.
      }
      destruct HS as [y' [HS1 HS2]].
      exists y'.
      split. 1: apply HS1.
      destruct HS2 as [HS2|HS2].
      * left. rewrite in_app_iff. tauto.
      * right. destruct HS2 as [c2' [HS2 HS3]].
        exists c2'. split.
        -- gen HS2.
          unfold next_config.
          destruct y' as [[y1 sgn1] s1].
          destruct (DirHash.K_eq_spec sgn0 sgn1);
          destruct sgn0;
          cbn[dir_rev]; cbn[get_dfa]; cbn[ldfa]; cbn[rdfa];
          rewrite dfa_add_config_trans;
          tauto.
        -- gen HS3.
          destruct (config_Hash.K_eq_spec c2' {| l := l1; r := r1; s := s2; sgn := L |}).
          ++ subst c2'.
            rewrite config_HashSet.hmap_get_set_same; auto 1.
          ++ rewrite config_HashSet.hmap_get_set_other; auto 1.
    + rewrite config_HashSet.hmap_get_set_other in Hc1'; auto 1.
      intros x y.
      specialize (HS c1' Hc1' x y).
      destruct c1' as [l3 r2 s3 sgn0].
      intros H.
      unshelve epose proof (HS _) as HS.
      {
        gen H.
        destruct sgn0; cbn[get_dfa]; cbn_proj;
        rewrite dfa_add_config_trans; tauto.
      }
      destruct HS as [y' [HS1 HS2]].
      exists y'.
      split. 1: apply HS1.
      destruct HS2 as [HS2|HS2].
      * left. rewrite in_app_iff. tauto.
      * right. destruct HS2 as [c2' [HS2 HS3]].
        exists c2'. split.
        -- gen HS2.
          unfold next_config.
          destruct y' as [[y1 sgn1] s1].
          destruct (DirHash.K_eq_spec sgn0 sgn1);
          destruct sgn0;
          cbn[dir_rev]; cbn[get_dfa]; cbn[ldfa]; cbn[rdfa];
          rewrite dfa_add_config_trans;
          tauto.
        -- gen HS3.
          destruct (config_Hash.K_eq_spec c2' {| l := l1; r := r1; s := s2; sgn := R |}).
          ++ subst c2'.
            rewrite config_HashSet.hmap_get_set_same; auto 1.
          ++ rewrite config_HashSet.hmap_get_set_other; auto 1.
  - destruct sgn0.
    -- cbn_proj.
      inverts HL.
      constructor; try assumption;
      cbn_proj.
      + unfold dfa_add_config.
        cbn[sgn]. cbn[DirHash.K_eq].
        cbn_proj.
        apply config_Index.hmap_add_WF; assumption.
      + unfold dfa_add_config.
        cbn[sgn]. cbn[DirHash.K_eq].
        cbn_proj.
        intros c Hc Hs.
        destruct (config_Hash.K_eq_spec c {| l := l1; r := r1; s := s2; sgn := L |}).
        * subst c.
          rewrite config_Index.hmap_get_add_same; cbn; auto 2.
        * rewrite config_HashSet.hmap_get_set_other in Hc; try assumption.
          apply config_Index.hmap_get_add_mono; auto 1.
          apply H_config_idx; auto 1.
    -- cbn_proj.
      inverts HL.
      constructor; try assumption.
      cbn_proj.
      intros c Hc Hs.
      rewrite config_HashSet.hmap_get_set_other in Hc; try assumption.
      2: destruct c; cbn in Hs; congruence.
      apply H_config_idx; auto 1.
  - destruct sgn0.
    -- cbn_proj.
      inverts HR.
      constructor; try assumption.
      cbn_proj.
      intros c Hc Hs.
      rewrite config_HashSet.hmap_get_set_other in Hc; try assumption.
      2: destruct c; cbn in Hs; congruence.
      apply H_config_idx; auto 1.
    -- cbn_proj.
      inverts HR.
      constructor; try assumption;
      cbn_proj.
      + unfold dfa_add_config.
        cbn[sgn]. cbn[DirHash.K_eq].
        cbn_proj.
        apply config_Index.hmap_add_WF; assumption.
      + unfold dfa_add_config.
        cbn[sgn]. cbn[DirHash.K_eq].
        cbn_proj.
        intros c Hc Hs.
        destruct (config_Hash.K_eq_spec c {| l := l1; r := r1; s := s2; sgn := R |}).
        * subst c.
          rewrite config_Index.hmap_get_add_same; cbn; auto 2.
        * rewrite config_HashSet.hmap_get_set_other in Hc; try assumption.
          apply config_Index.hmap_get_add_mono; auto 1.
          apply H_config_idx; auto 1.
  - cbn_proj.
    apply config_HashSet.hmap_set_WF; assumption.
Qed.

Lemma config_push_WF st c1':
  CTL_state_WF st ->
  (forall h t, st.(config_queue) = h::t ->
  next_config h st = Some c1' ->
  match config_push st c1' with
  | Some st' => CTL_state_WF st'
  | None => True
  end).
Proof.
  intros Hwf h t Hq Hnx.
  unfold config_push.
  rewrite config_HashSet.hmap_add_spec.
  destruct (config_HashSet.hmap_get c1' (config_set st)) eqn:E.
  - destruct Hwf.
    constructor.
    + destruct HO as [HO|[c' HO]].
      1: tauto.
      right.
      exists c'.
      destruct HO.
      constructor.
      * destruct H_is_config;
        constructor; assumption.
      * assumption.
    + intros c' H x y.
      specialize (HS c' H x y).
      destruct c' as [l0 r0 s0 sgn0].
      intros H0.
      specialize (HS H0).
      destruct HS as [y' [HS1 HS2]].
      exists y'.
      split. 1: apply HS1.
      destruct HS2 as [HS2|HS2].
      2: right; apply HS2.
      rewrite Hq in HS2.
      rewrite Hq.
      cbn in HS2.
      destruct HS2 as [HS2|HS2].
      2: left; apply HS2.
      right.
      exists c1'.
      subst h.
      split. 1: apply Hnx.
      destruct v.
      apply E.
    + cbn.
      destruct HL.
      constructor; try assumption.
    + cbn.
      destruct HR.
      constructor; try assumption.
    + assumption.
  - destruct Hwf.
    unfold if_Some.
    destruct (get_cs'' c1' (dfa_trans_inv2_HashMap.hmap_get (r c1') (inv2_trans (get_dfa st (sgn c1'))))) eqn:Ecs''; trivial.
    constructor.
    + destruct HO as [HO|[c' HO]].
      1: tauto.
      right.
      exists c'.
      destruct HO.
      constructor.
      * destruct H_is_config; constructor;
        cbn; rewrite dfa_add_config_trans; assumption.
      * cbn[config_set].
        destruct (config_Hash.K_eq_spec c1'0 c1').
        -- subst. apply config_HashSet.hmap_get_set_same; assumption.
        -- rewrite config_HashSet.hmap_get_set_other; assumption.
    + intros c' H x y.
      cbn[config_set] in H.
      destruct (config_Hash.K_eq_spec c' c1').
      1:{
        subst c'.
        destruct c1' as [l1 r0 s2 sgn0].
        cbn[config_queue].
        cbn in Ecs''.
        intros H0.
        assert (dfa_trans_HashMap.hmap_get (x, y) (get_dfa st sgn0).(trans) = Some r0) as H0'. {
          applys_eq H0.
          destruct sgn0; cbn[get_dfa]; cbn[ldfa]; cbn[rdfa];
          rewrite dfa_add_config_trans;
          reflexivity.
        }
        clear H0.
        remember (dfa_trans_inv2_HashMap.hmap_get r0 (inv2_trans (get_dfa st sgn0))) as ls.
        assert (In (x,y) ls) as H1'. {
          subst ls.
          gen H0'.
          destruct sgn0; cbn[get_dfa].
          - destruct HL.
            apply H_inv2_trans.
          - destruct HR.
            apply H_inv2_trans.
        }
        destruct (get_cs''_spec _ _ _ _ _ H1' Ecs'') as [y' [H2 H3]].
        exists y'.
        split. 1: apply H2.
        left.
        rewrite in_app_iff. tauto.
      }
      unshelve epose proof (HS c' _ x y) as HS.
      1: rewrite config_HashSet.hmap_get_set_other in H; assumption.
      destruct c' as [l1 r0 s2 sgn0] eqn:Ec'.
      intros H0.
      unshelve epose proof (HS _) as HS.
      1: destruct sgn0; cbn in H0; rewrite dfa_add_config_trans in H0; apply H0.
      destruct HS as [y' [HS1 HS2]].
      exists y'.
      split. 1: apply HS1.
      destruct HS2 as [HS2|HS2].
      2: {
        destruct HS2 as [c2' [HS2 HS3]].
        cbn[config_set].
        right.
        exists c2'.
        split. 2: {
          destruct (config_Hash.K_eq_spec c2' c1').
          - subst c2'.
            apply config_HashSet.hmap_get_set_same; assumption.
          - rewrite config_HashSet.hmap_get_set_other; assumption.
        }
        gen HS2.
        unfold next_config.
        destruct y' as [[y1 sgn1] s1].
        destruct (DirHash.K_eq_spec sgn0 sgn1);
        destruct sgn0;
        cbn[dir_rev]; cbn[get_dfa]; cbn[ldfa]; cbn[rdfa];
        rewrite dfa_add_config_trans;
        tauto.
      }
      rewrite Hq in HS2.
      rewrite Hq.
      cbn in HS2.
      cbn[config_queue].
      cbn[config_set].
      cbn[tl].
      destruct HS2 as [HS2|HS2].
      2: left; rewrite in_app_iff; right; apply HS2.
      right.
      exists c1'.
      subst h.
      split.
      2: apply config_HashSet.hmap_get_set_same; assumption.
      gen Hnx.
      unfold next_config.
      destruct y' as [[y1 sgn1] s1].
      destruct (DirHash.K_eq_spec sgn0 sgn1);
      destruct sgn0;
      cbn[dir_rev]; cbn[get_dfa]; cbn[ldfa]; cbn[rdfa];
      rewrite dfa_add_config_trans;
      tauto.
    + cbn[ldfa].
      inverts HL.
      constructor.
      all: repeat (
      rewrite dfa_add_config_id_alloc ||
      rewrite dfa_add_config_trans ||
      rewrite dfa_add_config_inv1_trans ||
      rewrite dfa_add_config_inv2_trans); try assumption.
      * unfold dfa_add_config.
        destruct (DirHash.K_eq (sgn c1') L).
        2: assumption.
        apply config_Index.hmap_add_WF; assumption.
      * cbn[config_set].
        intros c Hc Hs.
        unfold dfa_add_config.
        destruct (DirHash.K_eq_spec (sgn c1') L).
        -- cbn[config_idx].
          destruct (config_Hash.K_eq_spec c c1').
          ++ subst c.
            rewrite config_Index.hmap_get_add_same; auto 1.
            left; reflexivity.
          ++ destruct (Uint63_K.K_eq_spec (r c) (r c1')).
            ** rewrite <-e0.
              rewrite config_Index.hmap_get_add_same; auto 1.
              right.
              apply H_config_idx; auto 1.
              rewrite config_HashSet.hmap_get_set_other in Hc; assumption.
            ** rewrite config_Index.hmap_get_add_other; auto 1.
              apply H_config_idx; auto 1.
              rewrite config_HashSet.hmap_get_set_other in Hc; assumption.
        -- apply H_config_idx; auto.
          destruct (config_Hash.K_eq_spec c c1').
          1: congruence.
          rewrite config_HashSet.hmap_get_set_other in Hc; assumption.
    + cbn[rdfa].
      inverts HR.
      constructor.
      all: repeat (
      rewrite dfa_add_config_id_alloc ||
      rewrite dfa_add_config_trans ||
      rewrite dfa_add_config_inv1_trans ||
      rewrite dfa_add_config_inv2_trans); try assumption.
      * unfold dfa_add_config.
        destruct (DirHash.K_eq (sgn c1') R).
        2: assumption.
        apply config_Index.hmap_add_WF; assumption.
      * cbn[config_set].
        intros c Hc Hs.
        unfold dfa_add_config.
        destruct (DirHash.K_eq_spec (sgn c1') R).
        -- cbn[config_idx].
          destruct (config_Hash.K_eq_spec c c1').
          ++ subst c.
            rewrite config_Index.hmap_get_add_same; auto 1.
            left; reflexivity.
          ++ destruct (Uint63_K.K_eq_spec (r c) (r c1')).
            ** rewrite <-e0.
              rewrite config_Index.hmap_get_add_same; auto 1.
              right.
              apply H_config_idx; auto 1.
              rewrite config_HashSet.hmap_get_set_other in Hc; assumption.
            ** rewrite config_Index.hmap_get_add_other; auto 1.
              apply H_config_idx; auto 1.
              rewrite config_HashSet.hmap_get_set_other in Hc; assumption.
        -- apply H_config_idx; auto.
          destruct (config_Hash.K_eq_spec c c1').
          1: congruence.
          rewrite config_HashSet.hmap_get_set_other in Hc; assumption.
    + cbn[config_set].
      apply config_HashSet.hmap_set_WF; assumption.
Qed.

Lemma CTL_step_WF st:
CTL_state_WF st ->
match CTL_step st with
| None => True
| Some st' =>
  CTL_state_WF st'
end.
Proof.
unfold CTL_step.
destruct (config_queue st) as [|q1 q0] eqn:Eq; trivial.
destruct q1 as [[[x y] y'] c1'].
destruct c1' as [l0 r0 s0 sgn0].
destruct y' as [[y1 sgn1] s2].
destruct sgn0,sgn1; cbn.
- destruct (dfa_trans_HashMap.hmap_get (l0, y1) (trans (rdfa st))) eqn:E.
  + intros Hwf.
    eapply config_push_WF; eauto.
    cbn. unfold if_Some. rewrite E. reflexivity.
  + apply (dfa_add_trans_WF st _ _ R E).
- destruct (dfa_trans_HashMap.hmap_get (x, y1) (trans (ldfa st))) eqn:E.
  + intros Hwf.
    eapply config_push_WF; eauto.
    cbn. unfold if_Some. rewrite E. reflexivity.
  + apply (dfa_add_trans_WF st _ _ L E).
- destruct (dfa_trans_HashMap.hmap_get (x, y1) (trans (rdfa st))) eqn:E.
  + intros Hwf.
    eapply config_push_WF; eauto.
    cbn. unfold if_Some. rewrite E. reflexivity.
  + apply (dfa_add_trans_WF st _ _ R E).
- destruct (dfa_trans_HashMap.hmap_get (l0, y1) (trans (ldfa st))) eqn:E.
  + intros Hwf.
    eapply config_push_WF; eauto.
    cbn. unfold if_Some. rewrite E. reflexivity.
  + apply (dfa_add_trans_WF st _ _ L E).
Qed.

Lemma CTL_state_end st:
CTL_state_WF st ->
st.(config_queue) = nil ->
st.(init_flag) = true ->
~halts tm config_init.
Proof.
intros Hwf Hqnil Hinit.
destruct Hwf.
apply step_nonhalt with (P:=fun c1 => exists c1' : config, is_config_in_mset st c1 c1').
2: destruct HO as [HO|HO]; [congruence|apply HO].
intros c1 [c1' HP].
destruct HP.
specialize (HS c1' H_in_mset).
rewrite Hqnil in HS.
cbn[In] in HS.
destruct H_is_config.
- cbn in HS.
  destruct Hlm.
  + remember (ldfa st) as ldfa'.
    inverts HL.
    specialize (HS int0 s0 H_dfa_state0).
    destruct HS as [[[y1 sgn1] s2] [HS1 [HS2|[c2' [HS2 HS3]]]]]. 1: tauto.
    destruct sgn1.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (r', y1) (trans (rdfa st))) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        1: apply dfa_match_O.
        eapply dfa_match_S. 2: apply HS2'.  apply Hrm.
      -- cbn.
        applys_eq step_through.
        1: rewrite <-const_unfold; reflexivity.
        assumption.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (int0, y1) (trans ldfa')) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        2: apply Hrm.
        rewrite <-Heqldfa'.
        eapply dfa_match_S.
        2: apply HS2'.
        apply dfa_match_O.
      -- cbn.
        applys_eq step_back.
        1: rewrite <-const_unfold; reflexivity.
        1: reflexivity.
        assumption.
  + remember (ldfa st) as ldfa'.
    inverts HL.
    specialize (HS x a H).
    destruct HS as [[[y1 sgn1] s2] [HS1 [HS2|[c2' [HS2 HS3]]]]]. 1: tauto.
    destruct sgn1.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (r', y1) (trans (rdfa st))) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        1: rewrite <-Heqldfa'; apply Hlm.
        eapply dfa_match_S; eassumption.
      -- constructor. apply HS1.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (x, y1) (trans ldfa')) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        2: apply Hrm.
        rewrite <-Heqldfa'.
        eapply dfa_match_S; eassumption.
      -- constructor. apply HS1.
- cbn in HS.
  destruct Hrm.
  + remember (rdfa st) as rdfa'.
    inverts HR.
    specialize (HS int0 s0 H_dfa_state0).
    destruct HS as [[[y1 sgn1] s2] [HS1 [HS2|[c2' [HS2 HS3]]]]]. 1: tauto.
    destruct sgn1.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (int0, y1) (trans rdfa')) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        1: apply Hlm.
        rewrite <-Heqrdfa'.
        eapply dfa_match_S.
        2: apply HS2'.
        apply dfa_match_O.
      -- cbn.
        applys_eq step_back.
        1: rewrite <-const_unfold; reflexivity.
        1: reflexivity.
        assumption.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (l', y1) (trans (ldfa st))) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        2: apply dfa_match_O.
        eapply dfa_match_S; eassumption.
      -- cbn.
        applys_eq step_through.
        1: rewrite <-const_unfold; reflexivity.
        assumption.
  + remember (rdfa st) as rdfa'.
    inverts HR.
    specialize (HS x a H).
    destruct HS as [[[y1 sgn1] s2] [HS1 [HS2|[c2' [HS2 HS3]]]]]. 1: tauto.
    destruct sgn1.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (x, y1) (trans rdfa')) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        1: apply Hlm.
        rewrite <-Heqrdfa'.
        eapply dfa_match_S; eassumption.
      -- constructor. apply HS1.
    * unfold if_Some in HS2.
      destruct (dfa_trans_HashMap.hmap_get (l', y1) (trans (ldfa st))) eqn:HS2'.
      2: congruence.
      inverts HS2; eexists; split.
      -- eexists; constructor; [constructor | apply HS3].
        2: rewrite <-Heqrdfa'; apply Hrm.
        eapply dfa_match_S; eassumption.
      -- constructor. apply HS1.
Qed.

Lemma CTL_steps_spec cfg len T:
match CTL_steps cfg len T with
| inl st => CTL_state_WF st
| inr st =>
  match st with
  | Some st => CTL_state_WF st
  | None => True
  end
end.
Proof.
  unfold CTL_steps.
  apply N_iter_until_spec.
  - intros st Hwf.
    pose proof (CTL_step_WF st Hwf) as H.
    destruct (CTL_step st) as [st'|]; trivial.
  - pose proof (CTL_state_init_WF cfg len) as H.
    destruct (CTL_state_init cfg len); trivial.
Qed.

Lemma CTL_decide_nonhalt_spec cfg len T:
CTL_decide_nonhalt cfg len T = true ->
~halts tm config_init.
Proof.
  unfold CTL_decide_nonhalt.
  pose proof (CTL_steps_spec cfg len T).
  destruct (CTL_steps cfg len T) as [st|[st|]]; try congruence.
  rewrite and_true_iff.
  intros [H1 H2].
  destruct (config_queue st) eqn:E; try congruence.
  eapply CTL_state_end; eauto.
Qed.

End tm_ctx.

End CTL.






Module TMCtx(Ctx:TM.Ctx) <: Ctx.
Include Ctx.
End TMCtx.

Module DHTMFromTM(Ctx:TM.Ctx).
Module TMCtx := TMCtx Ctx.
Module DHTM := DHTM TMCtx.
Module TM := TM Ctx.

Definition map_config(x:DHTM.DH_config):Ctx.Q*TM.tape :=
match x with
| (l,r,s,L) => (s,(Streams.tl r,Streams.hd r,l))
| (l,r,s,R) => (s,(l,Streams.hd r,Streams.tl r))
end.

Ltac cbn_all :=
  repeat match goal with
  | H:_ |- _ => cbn in H || fail
  end;
  cbn.

Lemma map_step {tm c1 c2}:
  DHTM.step tm c1 c2 ->
  TM.step tm (map_config c1) (map_config c2).
Proof.
  destruct c1 as [[[l1 r1] s1] sgn1].
  destruct c2 as [[[l2 r2] s2] sgn2].
  intros; unfold map_config.
  destruct sgn1,sgn2;
  inverts H.
  1: destruct l1.
  all: constructor; auto 1.
Qed.

Lemma map_multistep {tm n c1 c2}:
  DHTM.multistep tm n c1 c2 ->
  TM.multistep tm n (map_config c1) (map_config c2).
Proof.
  gen c1 c2.
  induction n; intros c1 c2 H.
  - inverts H.
    constructor.
  - inverts H.
    pose proof (map_step H1).
    econstructor; eauto.
Qed.

Lemma map_halts {tm}:
  DHTM.halts' tm DHTM.c0 ->
  TM.halts' tm TM.c0.
Proof.
  rewrite <-DHTM.halts_halts'.
  rewrite <-TM.halts_halts'.
  intros [n [c [H H0]]].
  exists n.
  eexists.
  split.
  1: apply (map_multistep H).
  destruct c as [[[l r] s] sgn].
  gen H0. cbn.
  destruct r,sgn; cbn; tauto.
Qed.

Lemma map_nonhalt {tm}:
  ~DHTM.halts' tm DHTM.c0 ->
  ~TM.halts' tm TM.c0.
Proof.
  rewrite <-DHTM.halts_halts'.
  rewrite <-TM.halts_halts'.
  rewrite DHTM.nonhalt_iff.
  rewrite TM.nonhalt_iff.
  intros H n.
  specialize (H n).
  destruct H as [c' H].
  eexists.
  apply (map_multistep H).
Qed.

End DHTMFromTM.




Module BlockTMCtx(Ctx:Ctx)<: Ctx.
Definition Q:Type := Ctx.Q*dir.
Definition Sym:Type := list Ctx.Sym.
Definition q0 := (Ctx.q0,R).
Definition s0 := @nil Ctx.Sym.
Definition q_eqb := prod_eqb Ctx.q_eqb dir_eqb.
Definition sym_eqb := list_eqb Ctx.sym_eqb.
Lemma q_eqb_spec a b: Bool.reflect (a = b) (q_eqb a b).
Proof.
  intros.
  apply prod_eqb_spec.
  - apply Ctx.q_eqb_spec.
  - apply dir_eqb_spec.
Qed.
Lemma sym_eqb_spec a b: Bool.reflect (a = b) (sym_eqb a b).
Proof.
  intros.
  apply list_eqb_spec.
  apply Ctx.sym_eqb_spec.
Qed.
Import HashConcat.
Definition q_hash '(q,d) := Ctx.q_hash q ## dir_hash d.
Definition sym_hash ls := list_hash Ctx.sym_hash ls.
End BlockTMCtx.

Module BlockTMFromDHTM(Ctx:Ctx).
Module BlockTMCtx := BlockTMCtx Ctx.
Module BlockTM := DHTM BlockTMCtx.
Module DHTM := DHTM Ctx.

Lemma repeat_const {A} (a:A) n:
  repeat a n *> const a = const a.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    rewrite IHn,<-const_unfold.
    reflexivity.
Qed.

Lemma const_unfold' {A} (a:A) h t:
  h >> t = const a <->
  (h = a /\ t = const a).
Proof.
  split.
  - intros H.
    rewrite const_unfold in H.
    inverts H. tauto.
  - intros [H H0].
    subst.
    rewrite <-const_unfold.
    tauto.
Qed.

Section BlockSize.
Hypothesis block_size:nat.
Hypothesis block_time_limit:N.
Hypothesis block_size_nonzero: block_size <> O.
Hypothesis tm:DHTM.TM.

Definition map_TM:BlockTM.TM :=
fun '((s,sgn),ls) =>
let ls :=
match ls with
| nil => List.repeat Ctx.s0 block_size
| _ => ls
end in
match (DHTM.DH_cconfig_bounded_progress tm (nil,ls,s,sgn) block_time_limit) with
| None => None
| Some (l0,r0,s0,sgn0) =>
  match r0 with
  | nil => Some (l0,sgn0,(s0,sgn0))
  | _ => None
  end
end.

Inductive map_cconfig: BlockTM.DH_cconfig -> DHTM.DH_cconfig -> Prop :=
| map_cconfig_intro l r s sgn:
  Forall (fun x => length x = block_size) l ->
  Forall (fun x => length x = block_size) r ->
  map_cconfig (l,r,(s,sgn),sgn) (concat l,concat r,s,sgn)
.

Ltac simpl_Forall_hyp :=
  repeat
  (match goal with
  | H: _ |- _ => (rewrite Forall_cons_iff in H; cbn in H; try lia) || fail
  | H: _ /\ _ |- _ => destruct H
  end).

Lemma Str_app_inv {a1 a2}:
  a1 *> const BlockTMCtx.s0 = a2 *> const BlockTMCtx.s0 ->
  Forall (fun x => length x = block_size) a1 ->
  Forall (fun x => length x = block_size) a2 ->
  a1 = a2.
Proof.
  gen a2.
  induction a1; cbn; intros [|h2 t2] H H1 H2.
  - reflexivity.
  - cbn in H.
    symmetry in H.
    rewrite const_unfold' in H.
    destruct H as [H Ha].
    subst h2.
    simpl_Forall_hyp.
  - cbn in H.
    rewrite const_unfold' in H.
    destruct H as [H Ha].
    subst a.
    simpl_Forall_hyp.
  - inverts H. f_equal.
    simpl_Forall_hyp.
    eapply IHa1; eauto.
Qed.

Lemma map_step c1 c1' c2'':
  BlockTM.step map_TM (BlockTM.DH_cconfig_to_config c1) c2'' ->
  map_cconfig c1 c1' ->
  exists c2,
  c2'' = (BlockTM.DH_cconfig_to_config c2) /\
  exists c2',
  map_cconfig c2 c2' /\
  DHTM.progress tm (DHTM.DH_cconfig_to_config c1') (DHTM.DH_cconfig_to_config c2').
Proof.
  intros Hs C1.
  inverts C1.
  cbn in Hs.
  cbn.
  unfold map_TM in Hs.
  inverts Hs.
  - destruct m as [|m0 m1].
    + pose proof (DHTM.DH_cconfig_bounded_progress_spec tm ([], repeat Ctx.s0 block_size, s, sgn) block_time_limit).
      destruct (DHTM.DH_cconfig_bounded_progress tm ([], repeat Ctx.s0 block_size, s, sgn) block_time_limit) as [[[[l2 r2] s2] sgn2]|];
      try congruence.
      destruct r2 as [|r2 r3]; try congruence.
      inverts H6.

      destruct r as [|r4 r5].
      2: cbn in H3; inverts H3;
      rewrite Forall_cons_iff in H0; cbn in H0; lia.
      inverts H3.

      rewrite const_unfold' in H4.
      destruct H4 as [_ H4].
      subst r0.

      destruct H1 as [H1' H1].
      cbn in H1'.
      rewrite repeat_length in H1'.

      repeat rewrite <-const_unfold.
      eexists (m'::l0,nil,(s2,sgn),sgn).
      cbn.
      split. 1: reflexivity.
      eexists (_,_,_,_).
      split.
      * applys_eq map_cconfig_intro.
        -- apply Forall_cons; auto 1; lia.
        -- auto.
      * cbn. cbn in H1.
        repeat rewrite Str_app_assoc.
        destruct sgn.
        -- applys_eq H1.
          repeat f_equal.
          rewrite repeat_const; reflexivity.
        -- applys_eq H1.
          repeat f_equal.
          rewrite repeat_const; reflexivity.

    + pose proof (DHTM.DH_cconfig_bounded_progress_spec tm ([], m0 :: m1, s, sgn) block_time_limit).
      destruct (DHTM.DH_cconfig_bounded_progress tm ([], m0 :: m1, s, sgn) block_time_limit) as [[[[l2 r2] s2] sgn2]|];
      try congruence.
      destruct r2 as [|r2 r3]; try congruence.
      inverts H6.

      destruct H1 as [H1' H1].
      cbn in H1'.

      destruct r as [|r4 r5].
      1: { cbn in H3.
        rewrite const_unfold' in H3.
        unfold BlockTMCtx.s0 in H3.
        destruct H3.
        congruence.
      }
      inverts H3.

      simpl_Forall_hyp.
      eexists (m'::l0,r5,(s2,sgn),sgn).
      cbn.
      split. 1: reflexivity.
      eexists (_,_,_,_).
      split.
      * applys_eq map_cconfig_intro.
        -- apply Forall_cons; auto 1; lia.
        -- auto.
      * cbn. cbn in H1.
        repeat rewrite Str_app_assoc.
        destruct sgn; apply H1.

  - destruct m as [|m0 m1].
    + pose proof (DHTM.DH_cconfig_bounded_progress_spec tm ([], repeat Ctx.s0 block_size, s, sgn) block_time_limit).
      destruct (DHTM.DH_cconfig_bounded_progress tm  ([], repeat Ctx.s0 block_size, s, sgn) block_time_limit) as [[[[l2 r2] s2] sgn2]|];
      try congruence.

      destruct r2 as [|r2 r3]; try congruence.
      inverts H6.

      destruct H1 as [H1' H1].
      cbn in H1'.
      rewrite repeat_length in H1'.

      destruct r as [|r4 r5].
      2: cbn in H3; inverts H3; simpl_Forall_hyp.
      cbn in H3; inverts H3.

      rewrite const_unfold' in H4.
      destruct H4 as [_ H4].
      subst r0.

      repeat rewrite <-const_unfold.
      eexists (m'::nil,l0,(s2,dir_rev sgn),dir_rev sgn).
      cbn.
      split. 1: reflexivity.
      eexists (_,_,_,_).
      split.
      * applys_eq map_cconfig_intro.
        -- apply Forall_cons; auto 1; lia.
        -- auto.
      * cbn. cbn in H1.
        repeat rewrite Str_app_assoc.
        destruct sgn.
        -- applys_eq H1.
          repeat f_equal. cbn.
          rewrite repeat_const; reflexivity.
        -- applys_eq H1.
          repeat f_equal. cbn.
          rewrite repeat_const; reflexivity.

    + pose proof (DHTM.DH_cconfig_bounded_progress_spec tm ([], m0 :: m1, s, sgn) block_time_limit).
      destruct (DHTM.DH_cconfig_bounded_progress tm ([], m0 :: m1, s, sgn) block_time_limit) as [[[[l2 r2] s2] sgn2]|];
      try congruence.
      destruct r2 as [|r2 r3]; try congruence.
      inverts H6.
      destruct H1 as [H1' H1].
      cbn in H1'.

      destruct r as [|r4 r5].
      1: { cbn in H3.
        rewrite const_unfold' in H3.
        unfold BlockTMCtx.s0 in H3.
        destruct H3.
        congruence.
      }
      inverts H3.

      simpl_Forall_hyp.
      eexists (m'::r5,l0,(s2,dir_rev sgn),dir_rev sgn).
      cbn.
      split. 1: reflexivity.
      eexists (_,_,_,_).
      split.
      * applys_eq map_cconfig_intro.
        -- apply Forall_cons; auto 1; lia.
        -- auto.
      * cbn. cbn in H1.
        repeat rewrite Str_app_assoc.
        destruct sgn; apply H1.
Qed.

Definition P c1'' := exists c1 c1',
  map_cconfig c1 c1' /\
  c1'' = (DHTM.DH_cconfig_to_config c1') /\
  ~BlockTM.halts map_TM (BlockTM.DH_cconfig_to_config c1).

Lemma map_nonhalt c1 c1':
  ~BlockTM.halts' map_TM (BlockTM.DH_cconfig_to_config c1) ->
  map_cconfig c1 c1' ->
  ~DHTM.halts' tm (DHTM.DH_cconfig_to_config c1').
Proof.
  rewrite <-BlockTM.halts_halts'.
  rewrite <-DHTM.halts_halts'.
  intros H H0.
  apply DHTM.progress_nonhalt with (P:=P).
  - intros c'' Pc.
    unfold P in Pc.
    destruct Pc as [c [c' [H1 [H2 H3]]]].
    pose proof (BlockTM.DH_cconfig_step_spec map_TM c).
    destruct (BlockTM.DH_cconfig_step map_TM c) as [c2|] eqn:E.
    * epose proof (map_step _ _ _ H4 H1) as H5.
      destruct H5 as [c2_ [H5 [c2' [H6 H7]]]].
      exists (DHTM.DH_cconfig_to_config c2').
      subst c''.
      split; auto 1.
      unfold P.
      eexists _,_.
      split. 1: apply H6.
      split. 1: reflexivity.
      intros [n0 [c3 Hh]].
      apply H3.
      exists (S n0),c3.
      split. 2: tauto.
      econstructor; eauto.
      rewrite H5.
      apply Hh.
    * assert False. {
        apply H3.
        eexists _,_.
        split. 2: apply H4.
        constructor.
      }
      tauto.
  - unfold P.
    eexists _,_.
    split. 1: apply H0.
    split. 1: reflexivity.
    apply H.
Qed.

Fixpoint inv_map_cside(ls:list Ctx.Sym)(n:nat):(BlockTMCtx.Sym)*(list BlockTMCtx.Sym) :=
match ls with
| nil => (List.repeat Ctx.s0 n,nil)
| h::t =>
  match n with
  | O =>
    let (a,b):=inv_map_cside t (Nat.pred block_size) in (nil,(h::a)::b)
  | S n =>
    let (a,b):=inv_map_cside t n in (h::a,b)
  end
end.

Definition inv_map_cconfig(x:DHTM.DH_cconfig):BlockTM.DH_cconfig :=
let '(l,r,s,sgn):=x in
let (l0,l1):=inv_map_cside l block_size in
let (r0,r1):=inv_map_cside r block_size in
(l0::l1,r0::r1,(s,sgn),sgn).

Lemma inv_map_cside_spec' l n s0 l0:
  inv_map_cside l n = (s0, l0) ->
  (Forall (fun x : list Ctx.Sym => length x = block_size) l0 /\
  length s0 = n /\
  s0 *> concat l0 *> const Ctx.s0 = l *> const Ctx.s0).
Proof.
  gen n s0 l0.
  induction l; intros.
  - inverts H.
    repeat split. 1: auto.
    1: apply repeat_length.
    cbn.
    rewrite repeat_const.
    reflexivity.
  - cbn in H.
    destruct n as [|n].
    + destruct (inv_map_cside l (Nat.pred block_size)) eqn:E1.
      inverts H.
      specialize (IHl _ _ _ E1).
      cbn.
      repeat rewrite Str_app_assoc.
      repeat split.
      * apply Forall_cons.
        -- cbn. lia.
        -- apply IHl.
      * f_equal. apply IHl.
    + destruct (inv_map_cside l n) eqn:E1.
      inverts H.
      specialize (IHl _ _ _ E1).
      cbn.
      repeat split.
      * apply IHl.
      * lia.
      * f_equal. apply IHl.
Qed.

Lemma inv_map_cside_spec l s0 l0:
  inv_map_cside l block_size = (s0, l0) ->
  (Forall (fun x : list Ctx.Sym => length x = block_size) (s0 :: l0) /\
  s0 *> concat l0 *> const Ctx.s0 = l *> const Ctx.s0).
Proof.
  intros H.
  pose proof (inv_map_cside_spec' _ _ _ _ H).
  split.
  - apply Forall_cons; tauto.
  - tauto.
Qed.

Lemma inv_map_cconfig_spec x:
  exists x', map_cconfig (inv_map_cconfig x) x' /\ DHTM.DH_cconfig_to_config x' = DHTM.DH_cconfig_to_config x.
Proof.
  destruct x as [[[l r] s] sgn].
  cbn.
  destruct (inv_map_cside l block_size) eqn:El.
  destruct (inv_map_cside r block_size) eqn:Er.
  pose proof (inv_map_cside_spec _ _ _ El) as Hl.
  pose proof (inv_map_cside_spec _ _ _ Er) as Hr.
  cbn.
  eexists.
  split.
  - econstructor.
    + apply Hl.
    + apply Hr.
  - cbn.
    repeat rewrite Str_app_assoc.
    do 3 f_equal.
    + apply Hl.
    + apply Hr.
Qed.

Lemma inv_map_nonhalt c1':
  ~BlockTM.halts' map_TM (BlockTM.DH_cconfig_to_config (inv_map_cconfig c1')) ->
  ~DHTM.halts' tm (DHTM.DH_cconfig_to_config c1').
Proof.
  destruct (inv_map_cconfig_spec c1') as [c1 [H H0]].
  intros H1.
  rewrite <-H0.
  apply (map_nonhalt _ _ H1 H).
Qed.

End BlockSize.

End BlockTMFromDHTM.



Module Type NonEmptyHashableType(HT:HashableType).
Export HT.
Parameter k0: K.
End NonEmptyHashableType.

Module TapeHistoryTMCtx(Ctx:Ctx)(HT:HashableType)(th:NonEmptyHashableType HT) <: Ctx.
Export th.
Definition Q:Type := Ctx.Q.
Definition Sym:Type := Ctx.Sym*K.
Definition q0 := Ctx.q0.
Definition s0 := (Ctx.s0,k0).
Definition q_eqb := Ctx.q_eqb.
Definition sym_eqb := prod_eqb Ctx.sym_eqb K_eq.
Definition q_eqb_spec := Ctx.q_eqb_spec.
Lemma sym_eqb_spec a b: Bool.reflect (a = b) (sym_eqb a b).
Proof.
  intros.
  apply prod_eqb_spec.
  - apply Ctx.sym_eqb_spec.
  - apply K_eq_spec.
Qed.
Import HashConcat.
Definition q_hash := Ctx.q_hash.
Definition sym_hash '(s,h) := (Ctx.sym_hash s) ## (K_hash h).
End TapeHistoryTMCtx.


Module TapeHistoryTMFromDHTM(Ctx:Ctx)(HT:HashableType)(th:NonEmptyHashableType HT).

Module TapeHistoryTMCtx := TapeHistoryTMCtx Ctx HT th.
Module TapeHistoryTM := DHTM TapeHistoryTMCtx.
Module DHTM := DHTM Ctx.

Section map_ctx.

Hypothesis tm:DHTM.TM.
Hypothesis history_upd:Ctx.Q->Ctx.Sym->HT.K->HT.K.
Definition map_TM:TapeHistoryTM.TM :=
fun '(s,(m,k)) =>
match tm (s,m) with
| None => None
| Some (m',sgn',s') =>
  Some ((m',history_upd s m k),sgn',s')
end.

Definition map_cside(x:list TapeHistoryTMCtx.Sym):list Ctx.Sym :=
List.map fst x.

Definition inv_map_cside(x:list Ctx.Sym):list TapeHistoryTMCtx.Sym :=
List.map (fun a => (a,th.k0)) x.

Definition map_cconfig(x:TapeHistoryTM.DH_cconfig):DHTM.DH_cconfig :=
let '(l,r,s,sgn):=x in
(map_cside l,map_cside r,s,sgn).

Definition inv_map_cconfig(x:DHTM.DH_cconfig):TapeHistoryTM.DH_cconfig :=
let '(l,r,s,sgn):=x in
(inv_map_cside l,inv_map_cside r,s,sgn).

Lemma map_step c1 c2'':
  TapeHistoryTM.step map_TM (TapeHistoryTM.DH_cconfig_to_config c1) c2'' ->
  exists c2,
  c2'' = (TapeHistoryTM.DH_cconfig_to_config c2) /\
  DHTM.step tm (DHTM.DH_cconfig_to_config (map_cconfig c1)) (DHTM.DH_cconfig_to_config (map_cconfig c2)).
Proof.
  intros H.
  destruct c1 as [[[l1 r1] s1] sgn1]; cbn in H.
  inverts H.
  - unfold map_TM in H5.
    destruct m as [m k].
    destruct r1 as [|[m1 k1] r1].
    + cbn in H2.
      rewrite const_unfold in H2.
      inverts H2. cbn.
      eexists (m'::l1,nil,s',sgn1); cbn.
      split. 1: reflexivity.
      unfold map_cside.
      applys_eq DHTM.step_through.
      1: rewrite <-const_unfold; reflexivity.
      destruct (tm (s1, Ctx.s0)) as [[[m'' sgn'] s'']|] eqn:E; try congruence.
      unfold TapeHistoryTMCtx.Q in E.
      rewrite E.
      inverts H5. reflexivity.
    + cbn in H2.
      inverts H2. cbn.
      eexists (m'::l1,r1,_,_); cbn.
      split. 1: reflexivity.
      unfold map_cside.
      applys_eq DHTM.step_through.
      destruct (tm (s1, m1)) as [[[m'' sgn'] s'']|] eqn:E; try congruence.
      unfold TapeHistoryTMCtx.Q in E.
      rewrite E.
      inverts H5. reflexivity.
  - unfold map_TM in H5.
    destruct m as [m k].
    destruct r1 as [|[m1 k1] r1].
    + cbn in H2.
      rewrite const_unfold in H2.
      inverts H2. cbn.
      eexists (m'::nil,l1,_,_); cbn.
      split. 1: reflexivity.
      unfold map_cside.
      applys_eq DHTM.step_back.
      1: rewrite <-const_unfold; reflexivity.
      destruct (tm (s1, Ctx.s0)) as [[[m'' sgn'] s'']|] eqn:E; try congruence.
      unfold TapeHistoryTMCtx.Q in E.
      rewrite E.
      inverts H5. reflexivity.
    + cbn in H2.
      inverts H2. cbn.
      eexists (m'::r1,l1,_,_); cbn.
      split. 1: reflexivity.
      unfold map_cside.
      applys_eq DHTM.step_back.
      destruct (tm (s1, m1)) as [[[m'' sgn'] s'']|] eqn:E; try congruence.
      unfold TapeHistoryTMCtx.Q in E.
      rewrite E.
      inverts H5. reflexivity.
Qed.

Lemma map_multistep n c1 c2'':
  TapeHistoryTM.multistep map_TM n (TapeHistoryTM.DH_cconfig_to_config c1) c2'' ->
  exists c2,
  c2'' = (TapeHistoryTM.DH_cconfig_to_config c2) /\
  DHTM.multistep tm n (DHTM.DH_cconfig_to_config (map_cconfig c1)) (DHTM.DH_cconfig_to_config (map_cconfig c2)).
Proof.
  gen c1 c2''.
  induction n; intros.
  - exists c1.
    inverts H.
    split.
    1: reflexivity.
    constructor.
  - inverts H.
    destruct (map_step c1 c' H1) as [c [H3 H4]].
    subst c'.
    destruct (IHn c c2'' H2) as [c2 [H5 H6]].
    eexists.
    split. 1: apply H5.
    econstructor; eauto.
Qed.

Lemma map_nonhalt c1:
  ~TapeHistoryTM.halts map_TM (TapeHistoryTM.DH_cconfig_to_config c1) ->
  ~DHTM.halts tm (DHTM.DH_cconfig_to_config (map_cconfig c1)).
Proof.
  rewrite TapeHistoryTM.nonhalt_iff.
  rewrite DHTM.nonhalt_iff.
  intros H n.
  specialize (H n).
  destruct H as [c' H].
  destruct (map_multistep _ _ _ H) as [c2 [H0 H1]].
  eexists; eauto.
Qed.

Lemma inv_map_cside_spec ls:
  map_cside (inv_map_cside ls) = ls.
Proof.
  unfold map_cside,inv_map_cside.
  induction ls; cbn.
  1: reflexivity.
  rewrite IHls.
  reflexivity.
Qed.

Lemma inv_map_cconfig_spec c:
  map_cconfig (inv_map_cconfig c) = c.
Proof.
  destruct c as [[[l r] s] sgn]; cbn.
  do 2 rewrite inv_map_cside_spec.
  reflexivity.
Qed.

Lemma inv_map_nonhalt c1:
  ~TapeHistoryTM.halts' map_TM (TapeHistoryTM.DH_cconfig_to_config (inv_map_cconfig c1)) ->
  ~DHTM.halts' tm (DHTM.DH_cconfig_to_config c1).
Proof.
  rewrite <-TapeHistoryTM.halts_halts'.
  rewrite <-DHTM.halts_halts'.
  intros H.
  applys_eq (map_nonhalt _ H).
  rewrite inv_map_cconfig_spec.
  reflexivity.
Qed.

End map_ctx.

End TapeHistoryTMFromDHTM.

Fixpoint remove_nth{A}(f:A->bool)(n:nat)(ls:list A):list A :=
match ls with
| nil => nil
| h::t =>
  if f h then
    match n with
    | O => t
    | S n0 => h::remove_nth f n0 t
    end
  else h::remove_nth f n t
end.

Fixpoint upd_skipn{A}(n:nat)(f:list A->list A)(ls:list A) :=
match n with
| O => f ls
| S n0 =>
  match ls with
  | nil => nil
  | h::ls0 => h::upd_skipn n0 f ls0
  end
end.

Definition upd_LRU{A}(n LRU_n:nat)(A_eqb:A->A->bool)(ls:list A) :=
match ls with
| nil => nil
| h::ls0 => firstn n (h::(remove_nth (A_eqb h) LRU_n ls0))
end.

Definition upd_skipn_LRU{A}(n1 n2 LRU_n:nat)(A_eqb:A->A->bool)(ls:list A) :=
upd_skipn n1 (fun ls => upd_LRU n2 LRU_n A_eqb ls) ls.




Module RWL_mod(Ctx:Ctx).

Module SymHash := SymHash Ctx.
Module Int2Hash := ProdHash Uint63_K Uint63_K.
Module Int3Hash := ProdHash Int2Hash Uint63_K.
Module ListInt3Hash := ListHash Int3Hash.

Fixpoint limit_length{A}(len1 len2:nat)(ls:list A):list A :=
match len1 with
| O => if List.length ls <=? len2 then ls else (List.tl ls)
| S len1' =>
  match ls with
  | nil => nil
  | h::t => h::(limit_length len1' len2 t)
  end
end.

Module CTLCtx <: CTLCtx ListInt3Hash Ctx.
Module SymIdAlloc := IdAlloc SymHash.
Record config := {
  mnc: Uint63.int;
  mod_: Uint63.int;
  len1: nat;
  len2: nat;
  maxS: Uint63.int;
  is_s0: Ctx.Sym->bool;
}.
Definition config_t:Type := config.
Definition global_state_t:Type := config_t*SymIdAlloc.id_alloc_t.
Definition global_state_init cfg := (cfg,SymIdAlloc.id_alloc_make cfg.(maxS)).
Definition dfa_state_0 := @nil Int3Hash.K.

Definition dfa_trans(x:ListInt3Hash.K)(y0:Ctx.Sym)(d:dir)(gs:global_state_t):ListInt3Hash.K*global_state_t :=
let (cfg,gs):=gs in
match SymIdAlloc.get_or_alloc_id y0 gs with
| None => (nil,(cfg,gs))
| Some (y,gs) =>
  (match x with
  | nil => if cfg.(is_s0) y0 then nil else (y,int1,int1)::nil
  | (x0,n,m)::x1 =>
    let x' :=
    (if Uint63.eqb x0 y then
      (x0,
       if Uint63.ltb n cfg.(mnc) then Uint63.add n int1 else cfg.(mnc),
       Uint63.mod (Uint63.add m int1) cfg.(mod_))::
       x1
    else (y,int1,int1)::x)
    in limit_length cfg.(len1) cfg.(len2) x'
  end,(cfg,gs))
end.
End CTLCtx.

End RWL_mod.



Module CPS_LRU(Ctx:Ctx).

Module SymHash := SymHash Ctx.
Module ListIntHash := ListHash Uint63_K.
Module List2IntHash := ProdHash ListIntHash ListIntHash.

Module CTLCtx <: CTLCtx List2IntHash Ctx.
Module SymIdAlloc := IdAlloc SymHash.
Record config := {
  len1: nat;
  len2: nat;
  len3: nat;
  LRU_n: nat;
  maxS: Uint63.int;
  is_s0: Ctx.Sym->bool;
}.

Definition config_t:Type := config.
Definition global_state_t:Type := config_t*SymIdAlloc.id_alloc_t.
Definition global_state_init cfg := (cfg,SymIdAlloc.id_alloc_make cfg.(maxS)).
Definition dfa_state_0:List2IntHash.K := (nil,nil).

Definition is_nil{A}(ls:list A):bool :=
match ls with
| nil => true
| _ => false
end.

Definition dfa_trans(x:List2IntHash.K)(y0:Ctx.Sym)(d:dir)(gs:global_state_t):List2IntHash.K*global_state_t :=
let (cfg,gs):=gs in
match SymIdAlloc.get_or_alloc_id y0 gs with
| None => ((nil,nil),(cfg,gs))
| Some (y,gs) =>
  let '(x12,x3):=x in
  if is_nil x12 && is_nil x3 && cfg.(is_s0) y0 then ((nil,nil),(cfg,gs))
  else
  let x' :=
  (if length x3 <? cfg.(len3) then
    (x12,y::x3)
  else
    (upd_skipn_LRU cfg.(len1) cfg.(len2) cfg.(LRU_n) Uint63.eqb (y::x12),x3)
  ) in
  (x',(cfg,gs))
end.

End CTLCtx.
End CPS_LRU.


Module NGramCPS(Ctx:Ctx).

Module SymHash := SymHash Ctx.
Module ListIntHash := ListHash Uint63_K.

Module CTLCtx <: CTLCtx ListIntHash Ctx.
Module SymIdAlloc := IdAlloc SymHash.
Record config := {
  len: nat;
  maxS: Uint63.int;
}.

Definition config_t:Type := config.
Definition global_state_t:Type := config_t*SymIdAlloc.id_alloc_t.
Definition global_state_init cfg := (cfg,SymIdAlloc.id_alloc_make cfg.(maxS)).
Definition dfa_state_0:ListIntHash.K := (nil).

Definition dfa_trans(x:ListIntHash.K)(y:Ctx.Sym)(d:dir)(gs:global_state_t):ListIntHash.K*global_state_t :=
let (cfg,gs):=gs in
match SymIdAlloc.get_or_alloc_id y gs with
| None => ((nil),(cfg,gs))
| Some (y,gs) =>
  (firstn cfg.(len) (y::x),(cfg,gs))
end.

End CTLCtx.

End NGramCPS.


Module TapeHistoryImpl(Ctx:Ctx).
Module QHash := QHash Ctx.
Module SymHash := SymHash Ctx.
Module QSymHash := ProdHash QHash SymHash.
Module ListSymHash := ListHash SymHash.
Module ListQSymHash := ListHash QSymHash.

Module ListSymNonEmptyHash <: NonEmptyHashableType ListSymHash.
Definition k0 := @nil (Ctx.Sym).
End ListSymNonEmptyHash.

Module ListQSymNonEmptyHash <: NonEmptyHashableType ListQSymHash.
Definition k0 := @nil (Ctx.Q*Ctx.Sym).
End ListQSymNonEmptyHash.

Module ListSymTapeHistoryTMFromDHTM := TapeHistoryTMFromDHTM Ctx ListSymHash ListSymNonEmptyHash.
Module ListQSymTapeHistoryTMFromDHTM := TapeHistoryTMFromDHTM Ctx ListQSymHash ListQSymNonEmptyHash.

Definition Sym_history_upd(len1 len2 LRU_n:nat)(s:Ctx.Q)(m:Ctx.Sym)(ls:ListSymHash.K): ListSymHash.K :=
upd_skipn_LRU len1 len2 LRU_n SymHash.K_eq (m::ls).

Definition QSym_history_upd(len1 len2 LRU_n:nat)(s:Ctx.Q)(m:Ctx.Sym)(ls:ListQSymHash.K): ListQSymHash.K :=
upd_skipn_LRU len1 len2 LRU_n QSymHash.K_eq ((s,m)::ls).

End TapeHistoryImpl.

Definition N_to_int x := Uint63.of_Z (Z.of_N x).

Module CTLDecider(Ctx:TM.Ctx).

Module DHTMFromTM := DHTMFromTM Ctx.
Module BlockTMFromDHTM := BlockTMFromDHTM DHTMFromTM.TMCtx.
Module TapeHistoryImpl := TapeHistoryImpl DHTMFromTM.TMCtx.

Module Ctx_RWL_mod := RWL_mod BlockTMFromDHTM.BlockTMCtx.
Module CTL_RWL_mod := CTL Ctx_RWL_mod.ListInt3Hash BlockTMFromDHTM.BlockTMCtx Ctx_RWL_mod.CTLCtx.

Module Ctx_CPS_LRU := CPS_LRU BlockTMFromDHTM.BlockTMCtx.
Module CTL_CPS_LRU := CTL Ctx_CPS_LRU.List2IntHash BlockTMFromDHTM.BlockTMCtx Ctx_CPS_LRU.CTLCtx.

Module Ctx_NG_Sym := NGramCPS TapeHistoryImpl.ListSymTapeHistoryTMFromDHTM.TapeHistoryTMCtx.
Module Ctx_NG_QSym := NGramCPS TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTMCtx.
Module CTL_NG_Sym := CTL
  Ctx_NG_Sym.ListIntHash
  TapeHistoryImpl.ListSymTapeHistoryTMFromDHTM.TapeHistoryTMCtx
  Ctx_NG_Sym.CTLCtx.
Module CTL_NG_QSym := CTL
  Ctx_NG_QSym.ListIntHash
  TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTMCtx
  Ctx_NG_QSym.CTLCtx.

Inductive DeciderParameter :=
| RWL_mod(simT maxT maxS bsz bmaxT mnc mod_ len1 len2:N)
| CPS_LRU(simT maxT maxS bsz bmaxT len1 len2 len3 LRU_n:N)
| NG(simT maxT maxS NG_n len1 len2 LRU_n:N)(asth:bool)
.

Section tm_ctx.
Hypothesis tm:DHTMFromTM.TM.TM.
Hypothesis arg:DeciderParameter.
Definition decide_nonhalt:bool :=
match arg with
| RWL_mod simT maxT maxS bsz bmaxT mnc mod_ len1 len2 =>
  match DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT with
  | inl c =>
    let bsz := N.max 1 bsz in
    let tm1 := (BlockTMFromDHTM.map_TM (N.to_nat bsz) (bmaxT) tm) in
    let c1 := (BlockTMFromDHTM.inv_map_cconfig (N.to_nat bsz) c) in
    let cfg :=
      {|
        Ctx_RWL_mod.CTLCtx.mnc := N_to_int mnc;
        Ctx_RWL_mod.CTLCtx.mod_ := N_to_int mod_;
        Ctx_RWL_mod.CTLCtx.len1 := N.to_nat len1;
        Ctx_RWL_mod.CTLCtx.len2 := N.to_nat len2;
        Ctx_RWL_mod.CTLCtx.maxS := N_to_int maxS;
        Ctx_RWL_mod.CTLCtx.is_s0 := fun ls => forallb (DHTMFromTM.TMCtx.sym_eqb DHTMFromTM.TMCtx.s0) ls;
      |} in
    (CTL_RWL_mod.CTL_decide_nonhalt tm1 c1 cfg (N_to_int maxS) (maxT*100))
  | inr c => false
  end
| CPS_LRU simT maxT maxS bsz bmaxT len1 len2 len3 LRU_n =>
  match DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT with
  | inl c =>
    let bsz := N.max 1 bsz in
    let tm1 := (BlockTMFromDHTM.map_TM (N.to_nat bsz) (bmaxT) tm) in
    let c1 := (BlockTMFromDHTM.inv_map_cconfig (N.to_nat bsz) c) in
    let cfg := 
      {|
        Ctx_CPS_LRU.CTLCtx.len1 := N.to_nat len1;
        Ctx_CPS_LRU.CTLCtx.len2 := N.to_nat len2;
        Ctx_CPS_LRU.CTLCtx.len3 := N.to_nat len3;
        Ctx_CPS_LRU.CTLCtx.LRU_n := N.to_nat LRU_n;
        Ctx_CPS_LRU.CTLCtx.maxS := N_to_int maxS;
        Ctx_CPS_LRU.CTLCtx.is_s0 := fun ls => forallb (DHTMFromTM.TMCtx.sym_eqb DHTMFromTM.TMCtx.s0) ls;
      |} in
    (CTL_CPS_LRU.CTL_decide_nonhalt tm1 c1 cfg (N_to_int maxS) (maxT*100))
  | inr c => false
  end
| NG simT maxT maxS NG_n len1 len2 LRU_n asth =>
  match DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT with
  | inl c =>
    let '(len1,len2,LRU_n):=(N.to_nat len1,N.to_nat len2,N.to_nat LRU_n) in
    if asth then
      let upd := TapeHistoryImpl.QSym_history_upd len1 len2 LRU_n in
      let tm1 := TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.map_TM tm upd in
      let c1 := TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.inv_map_cconfig c in
      let cfg :=
        {|
          Ctx_NG_QSym.CTLCtx.len := N.to_nat NG_n;
          Ctx_NG_QSym.CTLCtx.maxS := N_to_int maxS;
        |} in
      (CTL_NG_QSym.CTL_decide_nonhalt tm1 c1 cfg (N_to_int maxS) (maxT*100))
    else
      let upd := TapeHistoryImpl.Sym_history_upd len1 len2 LRU_n in
      let tm1 := TapeHistoryImpl.ListSymTapeHistoryTMFromDHTM.map_TM tm upd in
      let c1 := TapeHistoryImpl.ListSymTapeHistoryTMFromDHTM.inv_map_cconfig c in
      let cfg :=
        {|
          Ctx_NG_Sym.CTLCtx.len := N.to_nat NG_n;
          Ctx_NG_Sym.CTLCtx.maxS := N_to_int maxS;
        |} in
      (CTL_NG_Sym.CTL_decide_nonhalt tm1 c1 cfg (N_to_int maxS) (maxT*100))
  | inr c => false
  end
end.

Lemma decide_nonhalt_spec:
  decide_nonhalt = true ->
  ~DHTMFromTM.TM.halts' tm DHTMFromTM.TM.c0.
Proof.
  unfold decide_nonhalt.
  intros H.
  destruct arg.
  - apply DHTMFromTM.map_nonhalt.
    pose proof (DHTMFromTM.DHTM.DH_cconfig_steps_spec tm DHTMFromTM.DHTM.cc0 simT) as H0.
    destruct (DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT); try congruence.
    rewrite <-DHTMFromTM.DHTM.halts_halts'.
    eapply DHTMFromTM.DHTM.evstep_nonhalt; eauto. clear H0.
    epose proof (CTL_RWL_mod.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
    rewrite DHTMFromTM.DHTM.halts_halts'.
    rewrite CTL_RWL_mod.TM.halts_halts' in H1.
    eapply BlockTMFromDHTM.inv_map_nonhalt.
    2: apply H1.
    lia.
  - apply DHTMFromTM.map_nonhalt.
    pose proof (DHTMFromTM.DHTM.DH_cconfig_steps_spec tm DHTMFromTM.DHTM.cc0 simT) as H0.
    destruct (DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT); try congruence.
    rewrite <-DHTMFromTM.DHTM.halts_halts'.
    eapply DHTMFromTM.DHTM.evstep_nonhalt; eauto. clear H0.
    epose proof (CTL_CPS_LRU.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
    rewrite DHTMFromTM.DHTM.halts_halts'.
    rewrite CTL_CPS_LRU.TM.halts_halts' in H1.
    eapply BlockTMFromDHTM.inv_map_nonhalt.
    2: apply H1.
    lia.
  - apply DHTMFromTM.map_nonhalt.
    pose proof (DHTMFromTM.DHTM.DH_cconfig_steps_spec tm DHTMFromTM.DHTM.cc0 simT) as H0.
    destruct (DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT); try congruence.
    rewrite <-DHTMFromTM.DHTM.halts_halts'.
    eapply DHTMFromTM.DHTM.evstep_nonhalt; eauto. clear H0.
    destruct asth.
    + epose proof (CTL_NG_QSym.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
      rewrite DHTMFromTM.DHTM.halts_halts'.
      rewrite CTL_NG_QSym.TM.halts_halts' in H1.
      eapply TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.inv_map_nonhalt.
      apply H1.
    + epose proof (CTL_NG_Sym.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
      rewrite DHTMFromTM.DHTM.halts_halts'.
      rewrite CTL_NG_Sym.TM.halts_halts' in H1.
      eapply TapeHistoryImpl.ListSymTapeHistoryTMFromDHTM.inv_map_nonhalt.
      apply H1.
Qed.

End tm_ctx.

End CTLDecider.



