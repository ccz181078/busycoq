From BusyCoq Require Import DHTM.
Require Import List.
Require Import Streams.
Require Import ZArith.
Require Import Lia.
From BusyCoq Require Import HashTable.
Require Uint63.
Require PArray.

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


Module FAR(K:HashableType)(Ctx:Ctx)(CTLCtx:CTLCtx K Ctx).

Module TM := DHTM Ctx. Export TM.
Export Ctx.
Export CTLCtx.

Definition h2:Type := Q*K.
Definition h2b:Type := Q*K.
Definition h3:Type := Sym*h2.
Definition Trans:Type := Sym*K.

Inductive Event :=
| h2s(a:h2)
| h3s(a:h3)
| ret2(a:h2)(b:h2b)
| ret3(a:h3)(b:h2b)
| retL(b:h2b)
| pre23(a:h2)(w:Sym)
| pre32(a:h3)(b:h2)
| pre33(a:h3)(b:h3)
| pre3L(a:h3)
| dfa_trans(a:K)(e:Trans)
.

Instance Q_Hash: HashConcat.Hash Q := (ltac: (esplit; apply q_hash)).
Instance Sym_Hash: HashConcat.Hash Sym := (ltac: (esplit; apply sym_hash)).
Instance K_Hash: HashConcat.Hash K := (ltac: (esplit; apply K_hash)).
Instance Q_Eqb: Eqb Q := (ltac: (esplit; apply q_eqb_spec)).
Instance Sym_Eqb: Eqb Sym := (ltac: (esplit; apply sym_eqb_spec)).
Instance K_Eqb: Eqb K := (ltac: (esplit; apply K_eq_spec)).

Module EventHash <: HashableType.
Import HashConcat.
Definition K := Event.
Definition K_hash := fun x =>
match x with
| h2s a => hv1 ## hash a
| h3s a => hv2 ## hash a
| ret2 a b => hv3 ## hash a ## hash b
| ret3 a b => hv4 ## hash a ## hash b
| retL b => hv5 ## hash b
| pre23 a w => hv6 ## hash a ## hash w
| pre32 a b => hv7 ## hash a ## hash b
| pre33 a b => hv8 ## hash a ## hash b
| pre3L a => hv9 ## hash a
| dfa_trans a e => hv10 ## hash a ## hash e
end.
Import Eqb.
Definition K_eq x y :=
match x,y with
| h2s a,h2s a0 => eqb a a0
| h3s a,h3s a0 => eqb a a0
| ret2 a b,ret2 a0 b0 => eqb a a0 && eqb b b0
| ret3 a b,ret3 a0 b0 => eqb a a0 && eqb b b0
| retL a,retL a0 => eqb a a0
| pre23 a b,pre23 a0 b0 => eqb a a0 && eqb b b0
| pre32 a b,pre32 a0 b0 => eqb a a0 && eqb b b0
| pre33 a b,pre33 a0 b0 => eqb a a0 && eqb b b0
| pre3L a,pre3L a0 => eqb a a0
| dfa_trans a b,dfa_trans a0 b0 => eqb a a0 && eqb b b0
| _,_ => false
end.
Lemma K_eq_spec a b: Bool.reflect (a=b) (K_eq a b).
Proof with solve_Bool_reflect.
  destruct a,b...
  all: cbn[K_eq].
  - destruct (eqb_spec a a0)...
  - destruct (eqb_spec a a0)...
  - destruct (eqb_spec a a0)...
    subst.
    destruct (eqb_spec b0 b)...
  - destruct (eqb_spec a a0)...
    subst.
    destruct (eqb_spec b0 b)...
  - destruct (eqb_spec b0 b)...
  - destruct (eqb_spec a a0)...
    subst.
    destruct (eqb_spec w w0)...
  - destruct (eqb_spec a a0)...
    subst.
    destruct (eqb_spec b0 b)...
  - destruct (eqb_spec a a0)...
    subst.
    destruct (eqb_spec b0 b)...
  - destruct (eqb_spec a a0)...
  - destruct (eqb_spec a a0)...
    subst.
    destruct (eqb_spec e e0)...
Qed.
End EventHash.

Module Bool_V <: ValueType.
Definition V := bool.
End Bool_V.

Module H2b_V <: ValueType.
Definition V := h2b.
End H2b_V.

Module H2_V <: ValueType.
Definition V := h2.
End H2_V.

Module H3_V <: ValueType.
Definition V := h3.
End H3_V.

Module K_V <: ValueType.
Definition V := K.
End K_V.

Module Q_V <: ValueType.
Definition V := Q.
End Q_V.

Module Sym_V <: ValueType.
Definition V := Sym.
End Sym_V.

Module Trans_V <: ValueType.
Definition V := Trans.
End Trans_V.

Module H2_K <: HashableType.
Import HashConcat.
Definition K := h2.
Definition K_hash := @hash K _.
Definition K_eq := @eqb K _.
Definition K_eq_spec := @eqb_spec K _.
End H2_K.

Module H3_K <: HashableType.
Import HashConcat.
Definition K := h3.
Definition K_hash := @hash K _.
Definition K_eq := @eqb K _.
Definition K_eq_spec := @eqb_spec K _.
End H3_K.

Module EventSet := HashMap EventHash Bool_V.
Module Ret2Map := HashMultimap H2_K H2b_V. 
Module Ret3Map := HashMultimap H3_K H2b_V. 
Module Pre23Map := HashMultimap H2_K Sym_V. 
Module Pre32Map := HashMultimap H3_K H2_V. 
Module Pre33Map := HashMultimap H3_K H3_V. 
Module DFATransMap := HashMultimap K Trans_V.
Module RSMap := HashMultimap K Q_V.

Section tm_sec.

Hypothesis tm: TM.

Section P_sec.
Hypothesis P:Event->Prop.

Inductive DFA_match: K->side->Prop :=
| DFA_match_O: DFA_match dfa_state_0 (const s0)
| DFA_match_S w r r0 r':
  DFA_match r r' ->
  P (dfa_trans r0 (w,r)) ->
  DFA_match r0 (w>>r')
.

Inductive Closed: Prop :=
| Closed_intro
    (Hinit: P (pre3L (s0,(q0,dfa_state_0))))
    (Hdfa_0: P (dfa_trans dfa_state_0 (s0,dfa_state_0)))
    (Hh2s_pre23: forall a b, P (pre23 a b) -> P (h2s a))
    (Hh3s_pre32: forall a b, P (pre32 a b) -> P (h3s a))
    (Hh3s_pre33: forall a b, P (pre33 a b) -> P (h3s a))
    (Hh3s_pre3L: forall a, P (pre3L a) -> P (h3s a))
    (Hh2s: forall q r w r0,
    P (h2s (q,r)) ->
    P (dfa_trans r (w,r0)) ->
    match tm (q,w) with
    | Some (w0,L,q0) =>
      exists r1,
      P (dfa_trans r1 (w0,r0)) /\
      P (ret2 (q,r) (q0,r1))
    | Some (w0,R,q0) =>
      P (pre32 (w0,(q0,r0)) (q,r))
    | None => False
    end)
    (Hh3s: forall q r w,
    P (h3s (w,(q,r))) ->
    P (pre23 (q,r) w))
    (Hpre23': forall a w r q,
    P (pre23 a w) ->
    P (ret2 a (q,r)) ->
    match tm (q,w) with
    | Some (w0,L,q0) =>
      exists r0,
      P (dfa_trans r0 (w0,r)) /\
      P (ret3 (w,a) (q0,r0))
    | Some (w0,R,q0) =>
      P (pre33 (w0,(q0,r)) (w,a))
    | None => False
    end)
    (HretL: forall r q,
    P (retL (q,r)) ->
    match tm (q,s0) with
    | Some (w0,L,q0) =>
      exists r0,
      P (dfa_trans r0 (w0,r)) /\
      P (retL (q0,r0))
    | Some (w0,R,q0) =>
      P (pre3L (w0,(q0,r)))
    | None => False
    end)
    (Hpre32': forall a a0 b, P (pre32 a a0) -> P (ret3 a b) -> P (ret2 a0 b))
    (Hpre33': forall a a0 b, P (pre33 a a0) -> P (ret3 a b) -> P (ret3 a0 b))
    (Hpre3L: forall a b, P (pre3L a) -> P (ret3 a b) -> P (retL b))
    :
  Closed
.

Lemma DFA_match_S'(HClosed:Closed) r r':
  DFA_match r r' ->
  exists w r0 r'0,
  DFA_match r0 r'0 /\
  r' = w>>r'0 /\
  P (dfa_trans r (w,r0)).
Proof.
  inverts HClosed.
  intros H.
  inverts H.
  - exists s0.
    repeat eexists.
    2: rewrite const_unfold; reflexivity.
    2: eauto 1.
    econstructor.
  - repeat eexists; eauto 1.
Qed.

Inductive coevstep: nat->DH_config->(DH_config->Prop)->Prop :=
| coevstep_1 n c p c':
  c -[ tm ]->> n / c' ->
  coevstep n c p
| coevstep_2 n n1 c p c':
  n1<=n ->
  c -[ tm ]->> n1 / c' ->
  p c' ->
  coevstep n c p.

Lemma coevstep_O c1 p:
  coevstep 0 c1 p.
Proof.
  eapply coevstep_1.
  eauto.
Qed.

Lemma coevstep_base n c p:
  p c ->
  coevstep n c p.
Proof.
  intros.
  eapply coevstep_2 with (n1:=O); eauto; lia.
Qed.

Lemma coevstep_step n c1 c2 p:
  coevstep n c2 p ->
  c1 -[ tm ]-> c2 ->
  coevstep (S n) c1 p.
Proof.
  intros.
  inverts H.
  - econstructor; eauto.
  - eapply coevstep_2 with (n1:=S n1); eauto; lia.
Qed.

Lemma multistep_split n1 n2 c1 c3:
  c1 -[ tm ]->> (n1+n2) / c3 ->
  exists c2,
  c1 -[ tm ]->> n1 / c2 /\
  c2 -[ tm ]->> n2 / c3.
Proof.
  gen n2 c1 c3.
  induction n1; intros.
  - eauto.
  - inverts H.
    apply IHn1 in H2.
    destruct H2 as [c2 [I1 I2]].
    eauto.
Qed.

Lemma coevstep_trans n c p p':
  coevstep n c p ->
  (forall c', p c' -> coevstep n c' p') ->
  coevstep n c p'.
Proof.
  intros.
  inverts H.
  1: econstructor; eauto.
  apply H0 in H3.
  inverts H3.
  - eassert (I4:_) by (eapply multistep_trans; [ apply H2 | apply H ]).
    rewrite Nat.add_comm in I4.
    apply multistep_split in I4.
    destruct I4 as [c2' [I4 _]].
    econstructor; eauto.
  - destruct (Nat.leb_spec (n1+n2) n) as [E|E].
    + econstructor 2; eauto using multistep_trans.
    + eassert (I5:_) by (eapply multistep_trans; [ apply H2 | apply H4 ]).
      replace (n1+n2) with (n+(n1+n2-n)) in I5 by lia.
      apply multistep_split in I5.
      destruct I5 as [c2' [I5 _]].
      econstructor; eauto.
Qed.


Section closed_sec.
Hypothesis HClosed:Closed.

Definition P2 n :=
  forall q r,
  P (h2s (q,r)) ->
  forall l r',
  DFA_match r r' ->
  coevstep n (l,r',q,R) (fun c => exists q0 r0 r0',
  P (ret2 (q,r) (q0,r0)) /\
  DFA_match r0 r0' /\
  c=(r0',l,q0,L)).

Definition P3 n :=
  forall w q r,
  P (h3s (w,(q,r))) ->
  forall l r',
  DFA_match r r' ->
  coevstep n (l<<w,r',q,R) (fun c => exists q0 r0 r0',
  P (ret3 (w,(q,r)) (q0,r0)) /\
  DFA_match r0 r0' /\
  c=(r0',l,q0,L)).

Lemma P23_n n:
  P2 n /\ P3 n.
Proof.
  unfold P2,P3.
  induction n.
  1: split; intros; apply coevstep_O.
  destruct IHn as [HP2 HP3].
  epose proof (DFA_match_S' HClosed) as HS'.
  epose proof (HClosed) as HClosed'.
  inversion HClosed'; subst.
  assert (HP2':P2 (S n)). {
    introv HP Hr.
    eapply HS' in Hr.
    destruct Hr as [w [r0 [r'0 [X1 [X2 X3]]]]].
    subst r'.
    epose proof (Hh2s _ _ _ _ HP X3) as I1.
    destruct (tm (q,w)) as [[[w0 []] q0]|] eqn:E.
    + destruct I1 as [r1 [I1 I2]].
      eapply coevstep_step.
      2: eapply step_back,E.
      eapply coevstep_base.
      repeat eexists.
      1: apply I2.
      eapply DFA_match_S; eauto 1.
    + eapply coevstep_step.
      2: eapply step_through,E.
      eapply coevstep_trans.
      1: eapply HP3; eauto 2.
      intros c' [q1 [r1 [r0' [P1 [P2 P3]]]]].
      eapply coevstep_base.
      repeat eexists; eauto 2.
    + tauto.
  }
  split.
  1: apply HP2'.
  {
    introv HP Hr.
    epose proof Hr as Hr0.
    eapply HS' in Hr0.
    destruct Hr0 as [w0 [r0 [r'0 [X1 [X2 X3]]]]].
    subst r'.
    eapply coevstep_trans.
    1: eapply HP2'; eauto 3.
    intros c' [q0' [r0' [r0'' [P1 [P2 P3]]]]].
    subst c'.
    epose proof (Hh3s _ _ _ HP) as HP1.
    epose proof (Hh2s_pre23 _ _ HP1) as HP2a.
    epose proof (Hpre23' _ _ _ _ HP1 P1) as HP3a.
    destruct (tm (q0',w)) as [[[w1' []] q1']|] eqn:E'.
    3: tauto.
    + destruct HP3a as [r1 [P4 P5]].
      eapply coevstep_step.
      2: eapply step_through,E'.
      eapply coevstep_base.
      repeat eexists; eauto 2 using DFA_match_S.
    + eapply coevstep_step.
      2: eapply step_back,E'.
      epose proof (Hh3s_pre33 _ _ HP3a) as HP4.
      eapply coevstep_trans.
      1: apply (HP3 _ _ _ HP4 l _ P2).
      intros c'0 [q2' [r1' [r1'' [P7 [P8 P9]]]]].
      eapply coevstep_base.
      repeat eexists; eauto 2.
    }
Qed.

Definition PR n :=
  forall w q r r',
  P (pre3L (w,(q,r))) ->
  DFA_match r r' ->
  exists c, (const s0<<w,r',q,R) -[ tm ]->> n / c.

Definition PL n :=
  forall q r r',
  P (retL (q,r)) ->
  DFA_match r r' ->
  exists c, (r',const s0,q,L) -[ tm ]->> n / c.

Lemma PLR_n n:
  PL n /\ PR n.
Proof.
  unfold PL,PR.
  induction n.
  1: eauto.
  destruct IHn as [HPL HPR].
  split.
  - introv HP Hr.
    inverts HClosed.
    eapply HretL in HP.
    destruct (tm (q,s0)) as [[[w0 []] q0]|] eqn:E.
    3: tauto.
    + destruct HP as [r0 [I1 I2]].
      eapply HPL in I2.
      2: econstructor; eauto.
      destruct I2 as [c I2].
      eexists.
      econstructor.
      * rewrite const_unfold.
        eapply step_through,E.
      * eauto 1.
    + eapply HPR in HP.
      2: eauto 1.
      destruct HP as [c I2].
      eexists.
      econstructor.
      * rewrite const_unfold.
        eapply step_back,E.
      * eauto 1.
  - introv HP Hr.
    epose proof (P23_n (S n)) as [_ HP3].
    inverts HClosed.
    eassert (I1:_). {
      eapply HP3 with (l:=const s0).
      - eapply Hh3s_pre3L,HP.
      - eauto 1.
    }
    inverts I1.
    1: eauto 2.
    destruct H1 as [q1 [r0 [r0' [I1 [I2 I3]]]]].
    subst c'.
    eapply Hpre3L in I1.
    eapply HretL in I1.
    2: eauto 1.
    destruct (tm (q1,s0)) as [[[w0 []] q2]|] eqn:E.
    3: tauto.
    * destruct I1 as [r1 [I1 I1a]].
      eapply HPL in I1a.
      2: econstructor; eauto.
      destruct I1a as [c I1a].
      eassert (I:_). {
        eapply multistep_trans.
        1: apply H0.
        econstructor 2.
        1: rewrite const_unfold; apply step_through,E.
        apply I1a.
      }
      rewrite Nat.add_comm in I.
      apply multistep_split in I.
      destruct I as [c2 [I I']].
      eauto.
    * eapply HPR in I1.
      2: eauto.
      destruct I1 as [c I1a].
      eassert (I:_). {
        eapply multistep_trans.
        1: apply H0.
        econstructor 2.
        1: rewrite const_unfold; apply step_back,E.
        apply I1a.
      }
      rewrite Nat.add_comm in I.
      apply multistep_split in I.
      destruct I as [c2 [I I']].
      eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  rewrite nonhalt_iff.
  intro n.
  epose proof (PLR_n n) as [_ HPR].
  inverts HClosed.
  eapply HPR in Hinit.
  epose proof Hinit as [c I1].
  1: constructor.
  rewrite <-const_unfold in I1.
  eauto.
Qed.

End closed_sec.
End P_sec.


Inductive Closed'(P P':Event->Prop): Prop :=
| Closed'_intro
    (HPP': forall e, P e -> P' e)
    (Hinit: P' (pre3L (s0,(q0,dfa_state_0))))
    (Hdfa_0: P' (dfa_trans dfa_state_0 (s0,dfa_state_0)))
    (Hh2s_pre23: forall a b, P (pre23 a b) -> P' (h2s a))
    (Hh3s_pre32: forall a b, P (pre32 a b) -> P' (h3s a))
    (Hh3s_pre33: forall a b, P (pre33 a b) -> P' (h3s a))
    (Hh3s_pre3L: forall a, P (pre3L a) -> P' (h3s a))
    (Hh2s: forall q r w r0,
    P (h2s (q,r)) ->
    P (dfa_trans r (w,r0)) ->
    match tm (q,w) with
    | Some (w0,L,q0) =>
      exists r1,
      P' (dfa_trans r1 (w0,r0)) /\
      P' (ret2 (q,r) (q0,r1))
    | Some (w0,R,q0) =>
      P' (pre32 (w0,(q0,r0)) (q,r))
    | None => False
    end)
    (Hh3s: forall q r w,
    P (h3s (w,(q,r))) ->
    P' (pre23 (q,r) w))
    (Hpre23': forall a w r q,
    P (pre23 a w) ->
    P (ret2 a (q,r)) ->
    match tm (q,w) with
    | Some (w0,L,q0) =>
      exists r0,
      P' (dfa_trans r0 (w0,r)) /\
      P' (ret3 (w,a) (q0,r0))
    | Some (w0,R,q0) =>
      P' (pre33 (w0,(q0,r)) (w,a))
    | None => False
    end)
    (HretL: forall r q,
    P (retL (q,r)) ->
    match tm (q,s0) with
    | Some (w0,L,q0) =>
      exists r0,
      P' (dfa_trans r0 (w0,r)) /\
      P' (retL (q0,r0))
    | Some (w0,R,q0) =>
      P' (pre3L (w0,(q0,r)))
    | None => False
    end)
    (Hpre32': forall a a0 b, P (pre32 a a0) -> P (ret3 a b) -> P' (ret2 a0 b))
    (Hpre33': forall a a0 b, P (pre33 a a0) -> P (ret3 a b) -> P' (ret3 a0 b))
    (Hpre3L: forall a b, P (pre3L a) -> P (ret3 a b) -> P' (retL b))
    :
  Closed' P P'
.


Lemma Closed'_Closed P P':
  Closed' P P' ->
  (forall x, P' x -> P x) ->
  Closed P.
Proof.
  intros H Heq.
  inverts H.
  assert (Heq':forall x, P' x <-> P x) by intuition.
  constructor; intros.
  all: eauto.
  - eassert (I:_) by (eapply Hh2s; eauto 1).
    destruct (tm (q,w)) as [[[w0 []] q0]|].
    1: destruct I as [r1 [I1 I2]].
    all: eauto.
  - eassert (I:_) by (eapply Hpre23'; eauto 2).
    destruct (tm (q,w)) as [[[w0 []] q0]|].
    1: destruct I as [r1 [I1 I2]].
    all: eauto.
  - eassert (I:_) by (eapply HretL; eauto 1).
    destruct (tm (q,s0)) as [[[w0 []] q0]|].
    1: destruct I as [r1 [I1 I2]].
    all: eauto.
Qed.

Inductive Ins :=
| ins_1(e:Event)
| ins_all{T}(p:T->Prop)(f:T->Event)
| ins_all'{T}(p:T->Prop)(f:T->global_state_t->option ((list Event)*global_state_t))
.

Definition on_H2_pop(a:h2)(e:Trans)(gs:global_state_t): option ((list Event)*global_state_t) :=
let '(q,r):=a in
let '(w,r0):=e in
match tm (q,w) with
| Some (w0,L,q0) =>
  let '(r1,gs):=CTLCtx.dfa_trans r0 w0 R gs in
  Some ([dfa_trans r1 (w0,r0);(ret2 (q,r) (q0,r1))],gs)
| Some (w0,R,q0) =>
  Some ([pre32 (w0,(q0,r0)) (q,r)],gs)
| None => None
end.

Definition on_H3_back(a':h3)(b:h2b)(gs:global_state_t): option ((list Event)*global_state_t) :=
let '(w,a):=a' in
let '(q,r):=b in
match tm (q,w) with
| Some (w0,L,q0) =>
  let '(r0,gs):=CTLCtx.dfa_trans r w0 R gs in
  Some ([(dfa_trans r0 (w0,r));
  (ret3 (w,a) (q0,r0))],gs)
| Some (w0,R,q0) =>
  Some ([(pre33 (w0,(q0,r)) (w,a))],gs)
| None => None
end.

Definition on_retL(b:h2b)(gs:global_state_t): option ((list Event)*global_state_t) :=
let '(q,r):=b in
match tm (q,s0) with
| Some (w0,L,q0) =>
  let '(r0,gs):=CTLCtx.dfa_trans r w0 R gs in
  Some ([(dfa_trans r0 (w0,r));
  (retL (q0,r0))],gs)
| Some (w0,R,q0) =>
  Some ([(pre3L (w0,(q0,r)))],gs)
| None => None
end.

Definition delta(P P':Event->Prop)(x:Event):list Ins :=
match x with
| h2s a =>
  [(ins_all' (fun e => P (dfa_trans (snd a) e)) (on_H2_pop a))]
| h3s a => 
  [(ins_1 (pre23 (snd a) (fst a)))]
| ret2 a b =>
  [(ins_all' (fun w => P (pre23 a w)) (fun w => on_H3_back (w,a) b))]
| ret3 a b =>
  [(ins_all' (fun (_:unit) => P (pre3L a)) (fun _ gs => Some ([retL b],gs)));
  (ins_all (fun a0 => P (pre33 a a0)) (fun a0 => ret3 a0 b));
  (ins_all (fun a0 => P (pre32 a a0)) (fun a0 => ret2 a0 b))]
| retL b =>
  [(ins_all' (fun (_:unit) => True) (fun _ => on_retL b))]
| pre23 a w =>
  [(ins_1 (h2s a));
  (ins_all' (fun b => P (ret2 a b)) (on_H3_back (w,a)))]
| pre32 a a0 =>
  [(ins_1 (h3s a));
  (ins_all (fun b => P (ret3 a b)) (ret2 a0))]
| pre33 a a0 =>
  [(ins_1 (h3s a));
  (ins_all (fun b => P (ret3 a b)) (ret3 a0))]
| pre3L a =>
  [(ins_1 (h3s a));
  (ins_all (fun b => P (ret3 a b)) (retL))]
| dfa_trans a e =>
  [(ins_all' (fun s => P (h2s (s,a))) (fun s => on_H2_pop (s,a) e))]
end.

Fixpoint ins_all'_rec {T}(f:T->global_state_t->option ((list Event)*_)) ls gs :=
match ls with
| [] => Some ([],gs)
| h::t =>
  ins_all'_rec f t gs &&& (fun '(res,gs) =>
  f h gs &&& (fun '(res0,gs) =>
  Some (res0++res,gs)))
end.

Lemma ins_all'_rec_spec {T} {f:T->_} {ls gs x res gs'}:
  ins_all'_rec f ls gs = Some (res,gs') ->
  In x ls ->
  exists gs'0 res' gs'1, f x gs'0 = Some (res',gs'1) /\ List.incl res' res.
Proof.
  gen gs res gs'.
  induction ls; intros.
  1: destruct H0.
  cbn in H.
  unfold if_Some in H.
  destruct (ins_all'_rec f ls gs) as [[res0 gs0]|] eqn:E.
  2: congruence.
  destruct (f a gs0) as [[res1 gs1]|] eqn:E0.
  2: congruence.
  inverts H.
  destruct H0.
  2:{
    epose proof (IHls _ _ _ E H) as [gs'0 [res' [I1 [I2 I3]]]].
    repeat eexists.
    1: apply I2.
    apply incl_appr,I3.
  }
  subst a.
  repeat eexists.
  1: apply E0.
  apply incl_appl,incl_refl.
Qed.

Inductive Ins_WF: (Ins)->(Event->Prop)->(Event->Prop)->Prop :=
| Ins_1_WF x P P0
  (Hins:P0 x)
  (Hmono:forall x0, P x0 -> P0 x0):
  Ins_WF (ins_1 x) P P0
| Ins_all_WF {T} (p:T->Prop) f ls P P0
  (Hls:forall x1, p x1 -> In x1 ls)
  (Hins:forall x0, In x0 (List.map f ls) -> P0 x0)
  (Hmono:forall x0, P x0 -> P0 x0):
  Ins_WF (ins_all p f) P P0
| Ins_all'_WF {T} (p:T->Prop) f ls gs res gs' P P0
  (Hls:forall x1, p x1 -> In x1 ls)
  (Hres:ins_all'_rec f ls gs = Some (res,gs'))
  (Hins:forall x0, In x0 res -> P0 x0)
  (Hmono:forall x0, P x0 -> P0 x0):
  Ins_WF (ins_all' p f) P P0
.

Inductive Inss_WF: (list Ins)->(Event->Prop)->(Event->Prop)->Prop :=
| Inss_WF_O P P' (Hincl: forall x, P x -> P' x): Inss_WF [] P P'
| Inss_WF_S h t P P0 P1: Inss_WF t P P0 -> Ins_WF h P0 P1 -> Inss_WF (h::t) P P1
.

Lemma Inss_mono ls P P0:
  Inss_WF ls P P0 ->
  forall x,
  P x -> P0 x.
Proof.
  intros H.
  induction H.
  1: eauto.
  inverts H0; eauto.
Qed.

Ltac inv :=
repeat
match goal with
| [H: Ins_WF _ _ _ |- _] => inverts H
| [H: Inss_WF _ _ _ |- _] => inverts H
end;
match goal with
| [H: Closed' _ _ |- _] => inverts H
end.

Ltac rw1 HIns P :=
repeat
match goal with
| [H: P _ |- _] => rewrite HIns in H; try (destruct H; [|congruence])
end.

Ltac des1 I0 x :=
  let w0:=fresh "w" in
  let q1:=fresh "q" in
  let r1:=fresh "r" in
  destruct (tm x) as [[[w0 []] q1]|];
  [ destruct I0 as [r1 [I1 I2]]; eauto 12 | eauto 12 | tauto].

Lemma delta_spec P P' x:
  Closed' P P' ->
  P' x ->
  let ls := delta P P' x in
  forall P0 P'0,
  (forall x0, P0 x0 <-> (P x0 \/ x0=x)) ->
  Inss_WF ls P' P'0 ->
  Closed' P0 P'0.
Proof.
  introv HC Hx HIns HInss.
  assert (X1:forall x, P0 x -> P'0 x). {
    epose proof (Inss_mono _ _ _ HInss).
    intros.
    apply H.
    rewrite HIns in H0.
    inverts HC.
    destruct H0; subst; eauto.
  }
  destruct x.
  - inv.
    unfold fst,snd in *.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + destruct H.
      * epose proof (Hh2s _ _ _ _ H H0) as I0.
        des1 I0 (q,w).
      * inverts H.
        apply Hls in H0.
        epose proof (ins_all'_rec_spec Hres H0) as [gs'0 [res' [gs'1 [I1 I2]]]].
        unfold on_H2_pop in I1.
        destruct (tm (q,w)) as [[[w' []] q']|].
        3: congruence.
        {
          destruct (CTLCtx.dfa_trans r0 w' R gs'0) as [r1 gs'2].
          inverts I1.
          unfold incl in I2; cbn in I2.
          exists r1; eauto 9.
        }
        {
          inverts I1.
          unfold incl in I2; cbn in I2.
          eauto.
        }
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
  - inv.
    destruct a.
    unfold fst,snd in *.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + destruct H0.
      * epose proof (Hpre23' _ _ _ _ H H0) as I0.
        des1 I0 (q,w).
      * inverts H0.
        apply Hls in H.
        epose proof (ins_all'_rec_spec Hres H) as [gs'0 [res' [gs'1 [I1 I2]]]].
        unfold on_H3_back in I1.
        destruct (tm (q,w)) as [[[w' []] q']|].
        3: congruence.
        {
          destruct (CTLCtx.dfa_trans r w' R gs'0) as [r1 gs'2].
          inverts I1.
          unfold incl in I2; cbn in I2.
          exists r1; eauto 9.
        }
        {
          inverts I1.
          unfold incl in I2; cbn in I2.
          eauto.
        }
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto 10.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
    + destruct H0.
      1: eauto 10.
      inverts H0.
      apply Hls1 in H.
      epose proof (Hins1 (_ a1) (in_map _ _ _ H)) as I1.
      cbn in I1.
      eauto.
    + destruct H0.
      1: eauto 10.
      inverts H0.
      apply Hls0 in H.
      epose proof (Hins0 (_ a1) (in_map _ _ _ H)) as I1.
      cbn in I1.
      eauto.
    + destruct H0.
      1: eauto 10.
      inverts H0.
      apply (Hls tt) in H.
      epose proof (ins_all'_rec_spec Hres H) as [gs'0 [res' [gs'1 [I1 I2]]]].
      inverts I1.
      unfold incl in I2; cbn in I2.
      eauto.
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + destruct H.
      * epose proof (HretL _ _ H) as I0.
        des1 I0 (q,s0).
      * inverts H.
        epose proof (Hls tt I) as H.
        epose proof (ins_all'_rec_spec Hres H) as [gs'0 [res' [gs'1 [I1 I2]]]].
        unfold on_retL in I1.
        destruct (tm (q,s0)) as [[[w' []] q']|].
        3: congruence.
        {
          destruct (CTLCtx.dfa_trans r w' R gs'0) as [r1 gs'2].
          inverts I1.
          unfold incl in I2; cbn in I2.
          exists r1; eauto 9.
        }
        {
          inverts I1.
          unfold incl in I2; cbn in I2.
          eauto.
        }
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w0).
    + destruct H.
      * epose proof (Hpre23' _ _ _ _ H H0) as I0.
        des1 I0 (q,w0).
      * inverts H.
        apply Hls in H0.
        epose proof (ins_all'_rec_spec Hres H0) as [gs'0 [res' [gs'1 [I1 I2]]]].
        unfold on_H3_back in I1.
        destruct (tm (q,w)) as [[[w' []] q']|].
        3: congruence.
        {
          destruct (CTLCtx.dfa_trans r w' R gs'0) as [r1 gs'2].
          inverts I1.
          unfold incl in I2; cbn in I2.
          exists r1; eauto 11.
        }
        {
          inverts I1.
          unfold incl in I2; cbn in I2.
          eauto.
        }
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
    + destruct H; eauto.
      inverts H.
      eapply Hls in H0.
      epose proof (Hins0 (_ b0) (in_map _ _ _ H0)) as I1.
      eauto.
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
    + destruct H; eauto.
      inverts H.
      eapply Hls in H0.
      epose proof (Hins0 (_ b0) (in_map _ _ _ H0)) as I1.
      eauto.
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + epose proof (Hh2s _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
    + destruct H; eauto.
      inverts H.
      eapply Hls in H0.
      epose proof (Hins0 (_ b) (in_map _ _ _ H0)) as I1.
      eauto.
  - inv.
    econstructor.
    1: exact X1.
    all: intros; rw1 HIns P0; eauto.
    + destruct H0.
      * epose proof (Hh2s _ _ _ _ H H0) as I0.
        des1 I0 (q,w).
      * inverts H0.
        apply Hls in H.
        epose proof (ins_all'_rec_spec Hres H) as [gs'0 [res' [gs'1 [I1 I2]]]].
        unfold on_H2_pop in I1.
        destruct (tm (q,w)) as [[[w' []] q']|].
        3: congruence.
        {
          destruct (CTLCtx.dfa_trans r0 w' R gs'0) as [r1 gs'2].
          inverts I1.
          unfold incl in I2; cbn in I2.
          exists r1; eauto 9.
        }
        {
          inverts I1.
          unfold incl in I2; cbn in I2.
          eauto.
        }
    + epose proof (Hpre23' _ _ _ _ H H0) as I0.
      des1 I0 (q,w).
    + epose proof (HretL _ _ H) as I0.
      des1 I0 (q,s0).
Qed.

Record FAR_state_t := {
  events: EventSet.hmap_t;
  events_todo: list Event;

  ret2': Ret2Map.hmap_t;
  ret3': Ret3Map.hmap_t;

  pre23': Pre23Map.hmap_t;
  pre32': Pre32Map.hmap_t;
  pre33': Pre33Map.hmap_t;

  dfa_trans': DFATransMap.hmap_t;
  rs': RSMap.hmap_t;

  rest_T: Uint63.int;
}.

Definition Px x k :=
  EventSet.hmap_get k x = Some true.

Definition Px' x k :=
  EventSet.hmap_get k x <> None.


Inductive FAR_state_WF: FAR_state_t->Prop :=
| FAR_state_WF_intro x
  (Hevents_WF: EventSet.hmap_WF x.(events))
  (Hret2'WF: Ret2Map.hmap_WF x.(ret2'))
  (Hret3'WF: Ret3Map.hmap_WF x.(ret3'))
  (Hpre23'WF: Pre23Map.hmap_WF x.(pre23'))
  (Hpre32'WF: Pre32Map.hmap_WF x.(pre32'))
  (Hpre33'WF: Pre33Map.hmap_WF x.(pre33'))
  (Hdfa_trans'WF: DFATransMap.hmap_WF x.(dfa_trans'))
  (Hrs'WF: RSMap.hmap_WF x.(rs'))
  (Hevents_todo:
  forall k, Px' x.(events) k -> (~Px x.(events) k) -> In k x.(events_todo))
  (Hret2': forall a b, Px x.(events) (ret2 a b) -> In b (Ret2Map.hmap_get a x.(ret2')))
  (Hret3': forall a b, Px x.(events) (ret3 a b) -> In b (Ret3Map.hmap_get a x.(ret3')))
  (Hpre23': forall a b, Px x.(events) (pre23 a b) -> In b (Pre23Map.hmap_get a x.(pre23')))
  (Hpre32': forall a b, Px x.(events) (pre32 a b) -> In b (Pre32Map.hmap_get a x.(pre32')))
  (Hpre33': forall a b, Px x.(events) (pre33 a b) -> In b (Pre33Map.hmap_get a x.(pre33')))
  (Hdfa_trans': forall a b, Px x.(events) (dfa_trans a b) -> In b (DFATransMap.hmap_get a x.(dfa_trans')))
  (Hrs': forall a b, Px x.(events) (h2s (b,a)) -> In b (RSMap.hmap_get a x.(rs')))
  (Hevents':Closed' (Px x.(events)) (Px' x.(events)))
    :
  FAR_state_WF x
.

Fixpoint batch_ins2 x ls :=
match ls with
| [] => (x,[])
| h::t =>
  let '(x',ls'):=batch_ins2 x t in
  EventSet.hmap_upd2 h
  (fun a =>
  match a with
  | None => (false,h::ls')
  | Some a0 => (a0,ls')
  end) x'
end.

Fixpoint batch_ins x ls :=
match ls with
| [] => x
| h::t => EventSet.hmap_upd h
  (fun a =>
  match a with
  | None => false
  | Some a0 => a0
  end) (batch_ins x t)
end.

Lemma batch_ins2_spec x ls:
  (fst (batch_ins2 x ls)) = batch_ins x ls.
Proof.
  unfold fst.
  induction ls; cbn[batch_ins2]; cbn[batch_ins].
  1: trivial.
  rewrite EventSet.hmap_upd_spec.
  destruct (batch_ins2 x ls) as [x' ls'].
  subst x'.
  rewrite EventSet.hmap_upd2_spec.
  destruct (EventSet.hmap_get a (batch_ins x ls)); trivial.
Qed.

Definition ins_all'_c{T}(ls:list T) f gs :=
  ins_all'_rec f ls gs.

Definition ins_1_c(e:Event)(gs:global_state_t):=
  Some ([e],gs).

Definition ins_all_c{T}(ls:list T)(f:T->Event)(gs:global_state_t):=
  Some (List.map f ls,gs).

Definition delta' x' (x:Event) gs :=
let P := Px x'.(events) in
match x with
| h2s a =>
  ins_all'_c (DFATransMap.hmap_get (snd a) x'.(dfa_trans')) (on_H2_pop a) gs
| h3s a =>
  ins_1_c (pre23 (snd a) (fst a)) gs
| ret2 a b =>
  ins_all'_c (Pre23Map.hmap_get a x'.(pre23')) (fun w => on_H3_back (w,a) b) gs
| ret3 a b =>
  ins_all'_c (match EventSet.hmap_get (pre3L a) x'.(events) with
             | Some true => [tt]
             | _ => []
             end) (fun _ gs => Some ([retL b],gs)) gs &&& (fun '(ls0,gs) =>
  ins_all_c (Pre33Map.hmap_get a x'.(pre33')) (fun a0 => ret3 a0 b) gs &&& (fun '(ls1,gs) =>
  ins_all_c (Pre32Map.hmap_get a x'.(pre32')) (fun a0 => ret2 a0 b) gs &&& (fun '(ls2,gs) =>
  Some (ls0++ls1++ls2,gs))))
| retL b =>
  ins_all'_c [tt] (fun _ => on_retL b) gs
| pre23 a w =>
  ins_1_c (h2s a) gs &&& (fun '(ls0,gs) =>
  ins_all'_c (Ret2Map.hmap_get a x'.(ret2')) (on_H3_back (w,a)) gs &&& (fun '(ls1,gs) =>
  Some (ls0++ls1,gs)))
| pre32 a a0 =>
  ins_1_c (h3s a) gs &&& (fun '(ls0,gs) =>
  ins_all_c (Ret3Map.hmap_get a x'.(ret3')) (ret2 a0) gs &&& (fun '(ls1,gs) =>
  Some (ls0++ls1,gs)))
| pre33 a a0 =>
  ins_1_c (h3s a) gs &&& (fun '(ls0,gs) =>
  ins_all_c (Ret3Map.hmap_get a x'.(ret3')) (ret3 a0) gs &&& (fun '(ls1,gs) =>
  Some (ls0++ls1,gs)))
| pre3L a =>
  ins_1_c (h3s a) gs &&& (fun '(ls0,gs) =>
  ins_all_c (Ret3Map.hmap_get a x'.(ret3')) (retL) gs &&& (fun '(ls1,gs) =>
  Some (ls0++ls1,gs)))
| dfa_trans a e =>
  ins_all'_c (RSMap.hmap_get a x'.(rs')) (fun s => on_H2_pop (s,a) e) gs
end.

Fixpoint len_int{T}(ls:list T)(s:Uint63.int):Uint63.int :=
match ls with
| [] => s
| h::t => len_int t (Uint63.succ s)
end.

Definition upd x gs :=
match x.(events_todo) with
| x0::t => delta' x x0 gs
&&& (fun '(dt,gs) =>
  let len:=len_int dt int0 in
  if Uint63.ltb x.(rest_T) len then None else
  let (w0,w1) := EventSet.hmap_upd2 x0 (fun v => (true,
  match v with
  | Some false => false
  | _ => true
  end)) x.(events) in
  if w1 then None else
  let w:=batch_ins2 w0 dt in
  Some (inl ({|
  events := fst w;
  events_todo := snd w++t;
  ret2' :=
    match x0 with
    | ret2 a b => Ret2Map.hmap_add a b x.(ret2')
    | _ => x.(ret2')
    end;
  ret3' :=
    match x0 with
    | ret3 a b => Ret3Map.hmap_add a b x.(ret3')
    | _ => x.(ret3')
    end;
  pre23' :=
    match x0 with
    | pre23 a b => Pre23Map.hmap_add a b x.(pre23')
    | _ => x.(pre23')
    end;
  pre32' := 
    match x0 with
    | pre32 a b => Pre32Map.hmap_add a b x.(pre32')
    | _ => x.(pre32')
    end;
  pre33' := 
    match x0 with
    | pre33 a b => Pre33Map.hmap_add a b x.(pre33')
    | _ => x.(pre33')
    end;
  dfa_trans' :=
    match x0 with
    | dfa_trans a b => DFATransMap.hmap_add a b x.(dfa_trans')
    | _ => x.(dfa_trans')
    end;
  rs' :=
    match x0 with
    | h2s (b,a) => RSMap.hmap_add a b x.(rs')
    | _ => x.(rs')
    end;
  rest_T := Uint63.sub x.(rest_T) len;
|},gs)))
| [] => Some (inr tt)
end.

Lemma batch_ins_WF x ls:
  EventSet.hmap_WF x ->
  EventSet.hmap_WF (batch_ins x ls).
Proof.
  intros HWF.
  induction ls.
  1: apply HWF.
  cbn[batch_ins].
  rewrite EventSet.hmap_upd_spec.
  apply EventSet.hmap_set_WF,IHls.
Qed.

Lemma Px_batch_ins x ls a:
  EventSet.hmap_WF x ->
  Px (batch_ins x ls) a <-> Px x a.
Proof.
  intros HWF.
  induction ls.
  1: reflexivity.
  rewrite <-IHls.
  cbn[batch_ins].
  unfold Px.
  rewrite EventSet.hmap_upd_spec.
  destruct (EventHash.K_eq_spec a a0).
  - subst.
    rewrite EventSet.hmap_get_set_same by (apply batch_ins_WF,HWF).
    destruct (EventSet.hmap_get a0 (batch_ins x ls)) as [[]|]; split; intro; solve[tauto|congruence].
  - rewrite EventSet.hmap_get_set_other.
    2: apply batch_ins_WF,HWF.
    2: auto 1.
    reflexivity.
Qed.

Lemma Px_ins x a a':
  EventSet.hmap_WF x ->
  Px (EventSet.hmap_set a true x) a' ->
  Px x a' /\ a'<>a \/ a'=a.
Proof.
  unfold Px.
  intros H.
  destruct (EventHash.K_eq_spec a' a).
  - subst.
    tauto.
  - left.
    split; auto 1.
    rewrite EventSet.hmap_get_set_other in H0; auto 1.
Qed.


Lemma Px'_batch_ins x res:
  EventSet.hmap_WF x ->
  (forall x0 : Event, (In x0 res \/ Px' x x0) -> Px' (batch_ins x res) x0).
Proof.
  intros.
  induction res; cbn[batch_ins].
  - destruct H0 as [[]|H0].
    tauto.
  - rewrite EventSet.hmap_upd_spec.
    unfold Px' in *.
    destruct (EventHash.K_eq_spec x0 a).
    + subst x0.
      rewrite EventSet.hmap_get_set_same.
      2: apply batch_ins_WF,H.
      congruence.
    + cbn[In] in H0.
      rewrite EventSet.hmap_get_set_other.
      2: apply batch_ins_WF,H.
      2: congruence.
      destruct H0 as [[H0|H0]|H0]; solve[tauto|congruence].
Qed.

Lemma Px'_set_true x x0 x1:
  EventSet.hmap_WF x ->
  Px' x x0 ->
  Px' (EventSet.hmap_set x1 true x) x0.
Proof.
  unfold Px'.
  intros.
  destruct (EventHash.K_eq_spec x0 x1).
  + subst x0.
    rewrite EventSet.hmap_get_set_same by auto 1.
    congruence.
  + cbn[In] in H0.
    rewrite EventSet.hmap_get_set_other; auto 1.
Qed.

Lemma ins_1_c_spec e gs x dt gs0:
  ins_1_c e gs = Some (dt,gs0) ->
  EventSet.hmap_WF x ->
  Ins_WF (ins_1 e) (Px' x) (Px' (batch_ins x dt)).
Proof.
  intros H HWF.
  inverts H.
  econstructor.
  - apply Px'_batch_ins; cbn[In]; tauto.
  - intros.
    apply Px'_batch_ins; tauto.
Qed.

Lemma ins_all_c_spec{T}(ls:list T) f gs p x dt gs0:
  (forall x1, p x1 -> In x1 ls) ->
  ins_all_c ls f gs = Some (dt,gs0) ->
  EventSet.hmap_WF x ->
  Ins_WF (ins_all p f) (Px' x) (Px' (batch_ins x dt)).
Proof.
  unfold ins_all_c.
  intros H H0 HWF.
  inverts H0.
  econstructor.
  - apply H.
  - intros.
    apply Px'_batch_ins; tauto.
  - intros.
    apply Px'_batch_ins; tauto.
Qed.

Lemma ins_all'_c_spec{T}(ls:list T) f gs p x dt gs0:
  (forall x1, p x1 -> In x1 ls) ->
  ins_all'_c ls f gs = Some (dt,gs0) ->
  EventSet.hmap_WF x ->
  Ins_WF (ins_all' p f) (Px' x) (Px' (batch_ins x dt)).
Proof.
  unfold ins_all'_c.
  intros H H0 HWF.
  gen p gs gs0 dt.
  induction ls; cbn[ins_all'_rec]; intros.
  - inverts H0.
    cbn[batch_ins].
    econstructor.
    + apply H.
    + reflexivity.
    + cbn[In]; tauto.
    + tauto.
  - pose proof H0 as H0'.
    unfold if_Some in H0.
    destruct (ins_all'_rec f ls gs) as [[res' gs']|] eqn:E.
    2: congruence.
    pose proof E as E'.
    destruct (f a gs') as [[res'0 gs'0]|] eqn:E0.
    2: congruence.
    inverts H0.
    eapply (IHls (fun x1 => In x1 ls) (fun x y => y)) in E.
    inverts E.
    econstructor.
    + apply H.
    + cbn[ins_all'_rec].
      rewrite E'.
      apply H0'.
    + intros.
      apply Px'_batch_ins; tauto.
    + intros.
      apply Px'_batch_ins; tauto.
  Unshelve.
  apply gs0.
Qed.

Lemma batch_ins_trans x ls ls0 :
  batch_ins x (ls++ls0) =
  batch_ins (batch_ins x ls0) ls.
Proof.
  induction ls; trivial.
  cbn[app].
  cbn[batch_ins].
  congruence.
Qed.

Ltac des2 H :=
  try (destruct H as [[H Hne]|H]; [auto 2|congruence]).

Ltac des3 H x0 :=
  rewrite Px_batch_ins in H;
  [| apply EventSet.hmap_set_WF; solve[auto 1]];
  apply Px_ins in H; [|solve[auto 1]];
  destruct x0; des2 H.

Ltac des4 H b b0 :=
  cbn[In];
  destruct (eqb_spec b b0);
  [ subst; tauto
  | right; des2 H ].

Ltac des5 H :=
  unfold if_Some in H;
  (repeat
  match type of H with
  | match ?e with _ => _ end = _ =>
    let ls:=fresh "dt" in
    let gs:=fresh "gs" in
    let E:=fresh "E" in
    destruct e as [[ls gs]|] eqn:E; [|congruence]
  end);
  inverts H;
  repeat rewrite batch_ins_trans.

Ltac solve_S :=
  econstructor; [|(eapply ins_1_c_spec || eapply ins_all_c_spec || eapply ins_all'_c_spec); eauto using EventSet.hmap_set_WF,batch_ins_WF].

Ltac solve_O :=
  econstructor;
  intro x0;
  apply Px'_set_true; auto 1.

Ltac ec_WF :=
  econstructor;
  cbn[events]; cbn[events_todo]; cbn[ret2']; cbn[ret3'];
  cbn[pre23']; cbn[pre32']; cbn[pre33']; cbn[dfa_trans']; cbn[rs'].

Lemma upd_spec x gs:
FAR_state_WF x ->
match upd x gs with
| Some (inl (x',gs')) => FAR_state_WF x'
| Some (inr tt) => ~halts tm c0
| _ => True
end.
Proof.
  intros HWF.
  unfold upd.
  destruct x.(events_todo) as [|x0 t] eqn:E.
  1:{
    inverts HWF.
    eapply nonhalt.
    eapply Closed'_Closed.
    1: eapply Hevents'.
    intros.
    epose proof (Hevents_todo _ H) as I.
    rewrite E in I.
    cbn in I.
    unfold Px.
    unfold Px in I.
    destruct (EventSet.hmap_get x0 x.(events)) as [[]|].
    - trivial.
    - destruct I; congruence.
    - destruct I; congruence.
  }
  unfold if_Some.
  destruct (delta' x x0 gs) as [[dt gs0]|] eqn:Edt.
  2: trivial.
  destruct (PrimInt63.ltb (rest_T x) (len_int dt int0)); trivial.
  rewrite EventSet.hmap_upd2_spec.
  destruct (EventSet.hmap_get x0 (events x)) as [[]|] eqn:E'; trivial.
  rewrite batch_ins2_spec.
  inverts HWF.
  ec_WF.
  - apply batch_ins_WF.
    apply EventSet.hmap_set_WF; auto 1.
  - destruct x0; auto 1.
    apply Ret2Map.hmap_add_WF; auto 1.
  - destruct x0; auto 1.
    apply Ret3Map.hmap_add_WF; auto 1.
  - destruct x0; auto 1.
    apply Pre23Map.hmap_add_WF; auto 1.
  - destruct x0; auto 1.
    apply Pre32Map.hmap_add_WF; auto 1.
  - destruct x0; auto 1.
    apply Pre33Map.hmap_add_WF; auto 1.
  - destruct x0; auto 1.
    apply DFATransMap.hmap_add_WF; auto 1.
  - destruct x0; auto 1.
    destruct a.
    apply RSMap.hmap_add_WF; auto 1.
  - intros k.
    epose proof (Hevents_todo k).
    clear Edt.
    induction dt; cbn[batch_ins]; cbn[batch_ins2].
    + unfold snd.
      rewrite E in H.
      cbn[In] in H.
      cbn[app].
      intros.
      unfold Px',Px in H,H0,H1.
      destruct (EventHash.K_eq_spec k x0).
      * subst.
        rewrite EventSet.hmap_get_set_same in H1 by auto 1.
        contradiction.
      * rewrite EventSet.hmap_get_set_other in H0,H1 by auto 1.
        destruct H; solve[tauto|congruence].
    + remember ((EventSet.hmap_set x0 true (events x))) as v1.
      destruct (batch_ins2 v1 dt) as [x' ls'] eqn:E0.
      assert (x'=fst (batch_ins2 v1 dt)) as E1 by (rewrite E0; trivial).
      rewrite batch_ins2_spec in E1.
      subst x'.
      clear E0.
      unfold snd in IHdt.
      remember (batch_ins v1 dt) as v2.
      assert (EventSet.hmap_WF v2) as HWFv2. {
        subst v2.
        apply batch_ins_WF.
        subst v1.
        apply EventSet.hmap_set_WF; auto 1.
      }
      rewrite EventSet.hmap_upd_spec.
      rewrite EventSet.hmap_upd2_spec.
      destruct (EventSet.hmap_get a v2) as [a0|] eqn:E0.
      { unfold snd.
        intros.
        unfold Px',Px in IHdt,H0,H1.
        destruct (EventHash.K_eq_spec k a).
        * subst k.
          rewrite EventSet.hmap_get_set_same in H0,H1 by auto 1.
          rewrite E0 in IHdt.
          apply IHdt; auto 1.
        * rewrite EventSet.hmap_get_set_other in H0,H1 by auto 1.
          apply IHdt; auto 1. }
      { unfold snd.
        intros.
        unfold Px',Px in IHdt,H0,H1.
        destruct (EventHash.K_eq_spec k a).
        * subst k.
          left; trivial.
        * rewrite EventSet.hmap_get_set_other in H0,H1 by auto 1.
          right.
          apply IHdt; auto 1.
      }
  - intros.
    des3 H x0.
    destruct (eqb_spec a a0).
    + subst.
      rewrite Ret2Map.hmap_get_add_same by auto 1.
      des4 H b b0.
    + rewrite Ret2Map.hmap_get_add_other by auto 1.
      des2 H.
  - intros.
    des3 H x0.
    destruct (eqb_spec a a0).
    + subst.
      rewrite Ret3Map.hmap_get_add_same by auto 1.
      des4 H b b0.
    + rewrite Ret3Map.hmap_get_add_other by auto 1.
      des2 H.
  - intros.
    des3 H x0.
    destruct (eqb_spec a a0).
    + subst.
      rewrite Pre23Map.hmap_get_add_same by auto 1.
      des4 H b w.
    + rewrite Pre23Map.hmap_get_add_other by auto 1.
      des2 H.
  - intros.
    des3 H x0.
    destruct (eqb_spec a a0).
    + subst.
      rewrite Pre32Map.hmap_get_add_same by auto 1.
      des4 H b b0.
    + rewrite Pre32Map.hmap_get_add_other by auto 1.
      des2 H.
  - intros.
    des3 H x0.
    destruct (eqb_spec a a0).
    + subst.
      rewrite Pre33Map.hmap_get_add_same by auto 1.
      des4 H b b0.
    + rewrite Pre33Map.hmap_get_add_other by auto 1.
      des2 H.
  - intros.
    des3 H x0.
    destruct (eqb_spec a a0).
    + subst.
      rewrite DFATransMap.hmap_get_add_same by auto 1.
      des4 H b e.
    + rewrite DFATransMap.hmap_get_add_other by auto 1.
      des2 H.
  - intros.
    des3 H x0.
    destruct a0 as [a0 a1].
    destruct (eqb_spec a a1).
    + subst.
      rewrite RSMap.hmap_get_add_same by auto 1.
      des4 H b a0.
    + rewrite RSMap.hmap_get_add_other by auto 1.
      des2 H.
  - eapply delta_spec with (x:=x0).
    + apply Hevents'.
    + unfold Px'.
      congruence.
    + intros.
      rewrite Px_batch_ins.
      2: apply EventSet.hmap_set_WF; auto 1.
      unfold Px.
      destruct (EventHash.K_eq_spec x0 x1).
      * subst x0.
        rewrite EventSet.hmap_get_set_same by auto 1.
        tauto.
      * rewrite EventSet.hmap_get_set_other by auto 1.
        split; intros.
        1: tauto.
        destruct H; solve[tauto|congruence].
    + unfold delta.
      unfold delta' in Edt.
      destruct x0.
      {
        solve_S.
        solve_O.
      }
      {
        solve_S.
        solve_O.
      }
      {
        solve_S.
        solve_O.
      }
      {
        des5 Edt.
        solve_S.
        2:{
          intros.
          unfold Px in H.
          rewrite H.
          destruct x1; cbn[In]; tauto.
        }
        solve_S.
        solve_S.
        solve_O.
      }
      {
        solve_S.
        2: intro X; destruct X; cbn; tauto.
        solve_O.
      }
      {
        des5 Edt.
        solve_S.
        solve_S.
        solve_O.
      }
      {
        des5 Edt.
        solve_S.
        solve_S.
        solve_O.
      }
      {
        des5 Edt.
        solve_S.
        solve_S.
        solve_O.
      }
      {
        des5 Edt.
        solve_S.
        solve_S.
        solve_O.
      }
      {
        solve_S.
        solve_O.
      }
Qed.

Definition init maxS maxT :=
let v1:=pre3L (s0,(q0,dfa_state_0)) in
let v2:=dfa_trans dfa_state_0 (s0,dfa_state_0) in
{| 
  events :=
  EventSet.hmap_set v2 false (EventSet.hmap_set v1 false (EventSet.hmap_make maxS));
  events_todo := [v2;v1];
  ret2' := Ret2Map.hmap_make maxS;
  ret3' := Ret3Map.hmap_make maxS;
  pre23' := Pre23Map.hmap_make maxS;
  pre32' := Pre32Map.hmap_make maxS;
  pre33' := Pre33Map.hmap_make maxS;
  dfa_trans' := DFATransMap.hmap_add dfa_state_0 (s0,dfa_state_0) (DFATransMap.hmap_make maxS);
  rs' := RSMap.hmap_make maxS;
  rest_T := maxT;
|}.

Ltac gso H :=
  (rewrite EventSet.hmap_get_set_other in H;
  [
  | auto using EventSet.hmap_set_WF,EventSet.hmap_make_WF
  | congruence]) ||
  (rewrite EventSet.hmap_get_set_same in H;
  [
  | auto using EventSet.hmap_set_WF,EventSet.hmap_make_WF]) ||
  rewrite EventSet.hmap_get_make in H.

Ltac gso' :=
  (rewrite EventSet.hmap_get_set_other;
  [
  | auto using EventSet.hmap_set_WF,EventSet.hmap_make_WF
  | congruence]) ||
  (rewrite EventSet.hmap_get_set_same;
  [
  | auto using EventSet.hmap_set_WF,EventSet.hmap_make_WF]) ||
  rewrite EventSet.hmap_get_make.

Ltac gso'' :=
repeat
(intros || congruence ||
match goal with
| [H:_ |- _] => gso H
end).

Lemma init_WF maxS maxT:
  FAR_state_WF (init maxS maxT).
Proof.
  unfold init.
  ec_WF;
  unfold Px,Px' in *.
  - auto using EventSet.hmap_set_WF,EventSet.hmap_make_WF.
  - apply Ret2Map.hmap_make_WF.
  - apply Ret3Map.hmap_make_WF.
  - apply Pre23Map.hmap_make_WF.
  - apply Pre32Map.hmap_make_WF.
  - apply Pre33Map.hmap_make_WF.
  - apply DFATransMap.hmap_add_WF.
    apply DFATransMap.hmap_make_WF.
  - apply RSMap.hmap_make_WF.
  - introv H H0.
    destruct k.
    all: try solve[gso''].
    + destruct (eqb_spec a (s0,(q0,dfa_state_0))).
      1: subst.
      all: gso''.
      cbn[In]; tauto.
    + destruct (eqb_spec a dfa_state_0).
      1: subst.
      1: destruct (eqb_spec e (s0,dfa_state_0)); subst.
      all: gso''.
      cbn[In]; tauto.
  - gso''.
  - gso''.
  - gso''.
  - gso''.
  - gso''.
  - introv H.
    destruct (eqb_spec a dfa_state_0).
    1: subst.
    1: destruct (eqb_spec b (s0,dfa_state_0)); subst.
    all: gso''.
  - gso''.
  - econstructor.
    + gso''.
    + do 2 gso'.
      congruence.
    + gso'.
      congruence.
    + gso''.
    + gso''.
    + gso''.
    + introv H.
      gso H.
      destruct (eqb_spec a (s0,(q0,dfa_state_0))).
      1: subst.
      all: gso''.
    + gso''.
    + gso''.
    + gso''.
    + gso''.
    + gso''.
    + gso''.
    + gso''.
Qed.

Definition FAR_step '(x,gs) :=
match upd x gs with
| Some (inl v) => inl v
| Some (inr tt) => inr true
| None => inr false
end.

Definition decide cfg maxS maxT T :=
N_iter_until FAR_step (inl (init (Uint63.of_Z (Z.of_N maxS)) (Uint63.of_Z (Z.of_N maxT)),global_state_init cfg)) T.

Lemma decide_spec cfg maxS maxT T:
match decide cfg maxS maxT T with
| inl (x,gs) => FAR_state_WF x
| inr true => ~halts tm c0
| inr false => True
end.
Proof.
  unfold decide.
  apply N_iter_until_spec.
  2: apply init_WF.
  intros [x gs] HWF.
  unfold FAR_step.
  epose proof (upd_spec _ gs HWF) as I1.
  destruct (upd x gs) as [[[x' gs']|[]]|]; trivial.
Qed.

Definition FAR_decide_nonhalt cfg maxS maxT T :=
match decide cfg maxS maxT T with
| inr true => true
| _ => false
end.

Lemma FAR_decide_nonhalt_spec cfg maxS maxT T:
FAR_decide_nonhalt cfg maxS maxT T = true ->
~halts tm c0.
Proof.
  unfold FAR_decide_nonhalt.
  pose proof (decide_spec cfg maxS maxT T).
  destruct (decide cfg maxS maxT T) as [|[]]; try congruence.
Qed.

End tm_sec.

End FAR.





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

Lemma inv_map_nonhalt_c0:
  ~BlockTM.halts' map_TM (BlockTM.c0) ->
  ~DHTM.halts' tm (DHTM.c0).
Proof.
  epose proof (map_nonhalt ([],[],BlockTMCtx.q0,R) ([],[],Ctx.q0,R)) as H.
  cbn in H.
  intros.
  apply H.
  1: apply H0.
  econstructor; eauto.
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


Module RNGS_mod(Ctx:Ctx).

Module SymHash := SymHash Ctx.
Module Int2Hash := ProdHash Uint63_K Uint63_K.
Module Int3Hash := ProdHash Int2Hash Uint63_K.
Module ListInt3Hash := ListHash Int3Hash.
Module ListIntHash := ListHash Uint63_K.
Module ListInt11Hash := ProdHash ListIntHash ListIntHash.
Module ListInt113Hash := ProdHash ListInt11Hash ListInt3Hash.

Fixpoint find_del{A}(f:A->bool)(ls:list A) :=
match ls with
| [] => None
| x::t => if f x then Some (x,t) else
  match find_del f t with
  | Some (x0,t0) => Some (x0,x::t0)
  | None => None
  end
end.

Definition is_nil{A}(ls:list A):bool :=
match ls with
| [] => true
| _ => false
end.

Module CTLCtx <: CTLCtx ListInt113Hash Ctx.
Module SymIdAlloc := IdAlloc SymHash.
Module ListIntIdAlloc := IdAlloc ListIntHash.
Record config := {
  mnc: Uint63.int;
  mod_: Uint63.int;
  NG_n: nat;
  len_h: nat;
  bs_n: nat;
  maxS: Uint63.int;
  is_s0: Ctx.Sym->bool;
}.
Definition config_t:Type := config.
Definition global_state_t:Type := config_t*SymIdAlloc.id_alloc_t*ListIntIdAlloc.id_alloc_t.
Definition global_state_init cfg := (cfg,SymIdAlloc.id_alloc_make cfg.(maxS),ListIntIdAlloc.id_alloc_make cfg.(maxS)).
Definition dfa_state_0:ListInt113Hash.K := ([],[],[]).

Definition dfa_trans(x:ListInt113Hash.K)(y0:Ctx.Sym)(d:dir)(gs:global_state_t):ListInt113Hash.K*global_state_t :=
let '(cfg,gs0,gs1):=gs in
let '(x0,x2,x1):=x in
if is_nil x0 && cfg.(is_s0) y0 then (x,gs) else
match SymIdAlloc.get_or_alloc_id y0 gs0 with
| None => (x,gs)
| Some (y',gs0) =>
  let x0:=firstn cfg.(NG_n) (y'::x0) in
  match ListIntIdAlloc.get_or_alloc_id x0 gs1 with
  | None => (x,gs)
  | Some (y,gs1) =>
    if length x2 =? cfg.(bs_n) then
    let '(x2,y) := (removelast (y::x2),last (y::x2) y) in
    let x1 :=
    match find_del (fun '(a,_,_) => Uint63.eqb y a) x1 with
    | Some ((w,n,m),x) =>
      (w,Uint63.min cfg.(mnc) (Uint63.succ n),if Uint63.eqb cfg.(mod_) int0 then m else Uint63.mod (Uint63.succ m) cfg.(mod_))::x
    | None => (y,int1,int1)::x1
    end
    in
    ((x0,x2,firstn cfg.(len_h) x1),(cfg,gs0,gs1))
    else ((x0,y::x2,x1),(cfg,gs0,gs1))
  end
end.
End CTLCtx.

End RNGS_mod.


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

Module MITMDFA(Ctx:Ctx).
Record config := {
  ldfa: PArray.array Uint63.int;
  rdfa: PArray.array Uint63.int;
  sym_id: Ctx.Sym->Uint63.int;
  n_sym: Uint63.int;
}.
Module SymHash := SymHash Ctx.
Module DFAStateHash := ProdHash Uint63_K SymHash.
Module CTLCtx <: CTLCtx DFAStateHash Ctx.
Definition config_t:Type := config.
Definition global_state_t:Type := config.
Definition global_state_init:config_t->global_state_t := fun x=>x.
Definition dfa_state_0:=(int0,Ctx.s0).
Definition dfa_trans(x:Uint63.int*Ctx.Sym)(y:Ctx.Sym)(d:dir)(gs:global_state_t):Uint63.int*Ctx.Sym*global_state_t :=
let dfa :=
match d with
| L => gs.(ldfa)
| R => gs.(rdfa)
end in
let z := PArray.get dfa (Uint63.add (Uint63.mul (fst x) (gs.(n_sym))) (gs.(sym_id) (snd x))) in
(z,y,gs).
End CTLCtx.

End MITMDFA.


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
Definition list_N_to_array_int(x:list N):PArray.array Uint63.int :=
let a:=PArray.make (N_to_int (N.of_nat (List.length x))) int0 in
fst (List.fold_left (fun '(a0,a1) b => (PArray.set a0 a1 (N_to_int b),Uint63.succ a1)) x (a,int0)).

Module CTLDecider(Ctx:TM.Ctx).

Module DHTMFromTM := DHTMFromTM Ctx.
Module BlockTMFromDHTM := BlockTMFromDHTM DHTMFromTM.TMCtx.
Module TapeHistoryImpl := TapeHistoryImpl DHTMFromTM.TMCtx.

Module Ctx_RNGS_mod := RNGS_mod BlockTMFromDHTM.BlockTMCtx.
Module CTL_RNGS_mod := CTL Ctx_RNGS_mod.ListInt113Hash BlockTMFromDHTM.BlockTMCtx Ctx_RNGS_mod.CTLCtx.
Module Ctx_RNGS_mod_QSym := RNGS_mod TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTMCtx.
Module CTL_RNGS_mod_QSym := CTL
  Ctx_RNGS_mod_QSym.ListInt113Hash
  TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTMCtx
  Ctx_RNGS_mod_QSym.CTLCtx.

Module Ctx_RWL_mod := RWL_mod BlockTMFromDHTM.BlockTMCtx.
Module CTL_RWL_mod := CTL Ctx_RWL_mod.ListInt3Hash BlockTMFromDHTM.BlockTMCtx Ctx_RWL_mod.CTLCtx.
Module FAR_RWL_mod := FAR Ctx_RWL_mod.ListInt3Hash BlockTMFromDHTM.BlockTMCtx Ctx_RWL_mod.CTLCtx.

Module Ctx_CPS_LRU := CPS_LRU BlockTMFromDHTM.BlockTMCtx.
Module CTL_CPS_LRU := CTL Ctx_CPS_LRU.List2IntHash BlockTMFromDHTM.BlockTMCtx Ctx_CPS_LRU.CTLCtx.
Module FAR_CPS_LRU := FAR Ctx_CPS_LRU.List2IntHash BlockTMFromDHTM.BlockTMCtx Ctx_CPS_LRU.CTLCtx.

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

Module Ctx_MITMDFA := MITMDFA Ctx.
Module CTL_MITMDFA := CTL Ctx_MITMDFA.DFAStateHash DHTMFromTM.TMCtx Ctx_MITMDFA.CTLCtx.

Inductive DeciderParameter :=
| RWL_mod_FAR(maxT maxS bsz bmaxT mnc mod_ len1 len2:N)
| CPS_LRU_FAR(maxT maxS bsz bmaxT len1 len2 len3 LRU_n:N)
| RWL_mod(simT maxT maxS bsz bmaxT mnc mod_ len1 len2:N)
| CPS_LRU(simT maxT maxS bsz bmaxT len1 len2 len3 LRU_n:N)
| NG(simT maxT maxS NG_n len1 len2 LRU_n:N)(asth:bool)
| MITMDFA(maxT maxS:N)(ldfa rdfa:list N)(sym_id:Ctx.Sym->Uint63.int)(n_sym:Uint63.int)
| RNGS_mod(simT maxT maxS bsz bmaxT mnc mod_ NG_n len_h bs_n:N)
| RNGS_mod_QSym(simT maxT maxS len1 len2 LRU_n mnc mod_ NG_n len_h bs_n:N)
.

Section tm_ctx.
Hypothesis tm:DHTMFromTM.TM.TM.
Hypothesis arg:DeciderParameter.
Definition decide_nonhalt:bool :=
match arg with
| RWL_mod_FAR maxT maxS bsz bmaxT mnc mod_ len1 len2 =>
  let c:=DHTMFromTM.DHTM.cc0 in
    let bsz := N.max 1 bsz in
    let tm1 := (BlockTMFromDHTM.map_TM (N.to_nat bsz) (bmaxT) tm) in
    let cfg :=
      {|
        Ctx_RWL_mod.CTLCtx.mnc := N_to_int mnc;
        Ctx_RWL_mod.CTLCtx.mod_ := N_to_int mod_;
        Ctx_RWL_mod.CTLCtx.len1 := N.to_nat len1;
        Ctx_RWL_mod.CTLCtx.len2 := N.to_nat len2;
        Ctx_RWL_mod.CTLCtx.maxS := N_to_int maxS;
        Ctx_RWL_mod.CTLCtx.is_s0 := fun ls => forallb (DHTMFromTM.TMCtx.sym_eqb DHTMFromTM.TMCtx.s0) ls;
      |} in
    (FAR_RWL_mod.FAR_decide_nonhalt tm1 cfg (maxS) (maxT) maxT)
| CPS_LRU_FAR maxT maxS bsz bmaxT len1 len2 len3 LRU_n =>
    let bsz := N.max 1 bsz in
    let tm1 := (BlockTMFromDHTM.map_TM (N.to_nat bsz) (bmaxT) tm) in
    let cfg := 
      {|
        Ctx_CPS_LRU.CTLCtx.len1 := N.to_nat len1;
        Ctx_CPS_LRU.CTLCtx.len2 := N.to_nat len2;
        Ctx_CPS_LRU.CTLCtx.len3 := N.to_nat len3;
        Ctx_CPS_LRU.CTLCtx.LRU_n := N.to_nat LRU_n;
        Ctx_CPS_LRU.CTLCtx.maxS := N_to_int maxS;
        Ctx_CPS_LRU.CTLCtx.is_s0 := fun ls => forallb (DHTMFromTM.TMCtx.sym_eqb DHTMFromTM.TMCtx.s0) ls;
      |} in
    (FAR_CPS_LRU.FAR_decide_nonhalt tm1 cfg (maxS) (maxT) maxT)
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
| MITMDFA maxT maxS ldfa rdfa sym_id n_sym =>
    let cfg :=
      {|
        Ctx_MITMDFA.ldfa := list_N_to_array_int ldfa;
        Ctx_MITMDFA.rdfa := list_N_to_array_int rdfa;
        Ctx_MITMDFA.sym_id := sym_id;
        Ctx_MITMDFA.n_sym := n_sym;
      |} in
    CTL_MITMDFA.CTL_decide_nonhalt tm DHTMFromTM.DHTM.cc0 cfg (N_to_int maxS) (maxT*100)
| RNGS_mod simT maxT maxS bsz bmaxT mnc mod_ NG_n len_h bs_n =>
  match DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT with
  | inl c =>
    let bsz := N.max 1 bsz in
    let tm1 := (BlockTMFromDHTM.map_TM (N.to_nat bsz) (bmaxT) tm) in
    let c1 := (BlockTMFromDHTM.inv_map_cconfig (N.to_nat bsz) c) in
    let cfg :=
      {|
        Ctx_RNGS_mod.CTLCtx.mnc := N_to_int mnc;
        Ctx_RNGS_mod.CTLCtx.mod_ := N_to_int mod_;
        Ctx_RNGS_mod.CTLCtx.NG_n := N.to_nat NG_n;
        Ctx_RNGS_mod.CTLCtx.len_h := N.to_nat len_h;
        Ctx_RNGS_mod.CTLCtx.bs_n := N.to_nat bs_n;
        Ctx_RNGS_mod.CTLCtx.maxS := N_to_int maxS;
        Ctx_RNGS_mod.CTLCtx.is_s0 := fun ls => forallb (DHTMFromTM.TMCtx.sym_eqb DHTMFromTM.TMCtx.s0) ls;
      |} in
    (CTL_RNGS_mod.CTL_decide_nonhalt tm1 c1 cfg (N_to_int maxS) (maxT*100))
  | inr c => false
  end
| RNGS_mod_QSym simT maxT maxS len1 len2 LRU_n mnc mod_ NG_n len_h bs_n =>
  match DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT with
  | inl c =>
    let '(len1,len2,LRU_n):=(N.to_nat len1,N.to_nat len2,N.to_nat LRU_n) in
      let upd := TapeHistoryImpl.QSym_history_upd len1 len2 LRU_n in
      let tm1 := TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.map_TM tm upd in
      let c1 := TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.inv_map_cconfig c in
      let cfg :=
        {|
          Ctx_RNGS_mod_QSym.CTLCtx.mnc := N_to_int mnc;
          Ctx_RNGS_mod_QSym.CTLCtx.mod_ := N_to_int mod_;
          Ctx_RNGS_mod_QSym.CTLCtx.NG_n := N.to_nat NG_n;
          Ctx_RNGS_mod_QSym.CTLCtx.len_h := N.to_nat len_h;
          Ctx_RNGS_mod_QSym.CTLCtx.bs_n := N.to_nat bs_n;
          Ctx_RNGS_mod_QSym.CTLCtx.maxS := N_to_int maxS;
          Ctx_RNGS_mod_QSym.CTLCtx.is_s0 := fun '(a,b) => (DHTMFromTM.TMCtx.sym_eqb DHTMFromTM.TMCtx.s0 a) && (Ctx_RNGS_mod_QSym.is_nil b);
        |} in
      (CTL_RNGS_mod_QSym.CTL_decide_nonhalt tm1 c1 cfg (N_to_int maxS) (maxT*100))
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
    rewrite <-DHTMFromTM.DHTM.halts_halts'.
    epose proof (FAR_RWL_mod.FAR_decide_nonhalt_spec _ _ _ _ _ H) as H1.
    rewrite DHTMFromTM.DHTM.halts_halts'.
    rewrite FAR_RWL_mod.TM.halts_halts' in H1.
    eapply BlockTMFromDHTM.inv_map_nonhalt_c0.
    2: apply H1.
    lia.
  - apply DHTMFromTM.map_nonhalt.
    rewrite <-DHTMFromTM.DHTM.halts_halts'.
    epose proof (FAR_CPS_LRU.FAR_decide_nonhalt_spec _ _ _ _ _ H) as H1.
    rewrite DHTMFromTM.DHTM.halts_halts'.
    rewrite FAR_CPS_LRU.TM.halts_halts' in H1.
    eapply BlockTMFromDHTM.inv_map_nonhalt_c0.
    2: apply H1.
    lia.
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
  - apply DHTMFromTM.map_nonhalt.
    rewrite <-CTL_MITMDFA.TM.halts_halts'.
    epose proof (CTL_MITMDFA.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
    apply H1.
  - apply DHTMFromTM.map_nonhalt.
    pose proof (DHTMFromTM.DHTM.DH_cconfig_steps_spec tm DHTMFromTM.DHTM.cc0 simT) as H0.
    destruct (DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT); try congruence.
    rewrite <-DHTMFromTM.DHTM.halts_halts'.
    eapply DHTMFromTM.DHTM.evstep_nonhalt; eauto. clear H0.
    epose proof (CTL_RNGS_mod.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
    rewrite DHTMFromTM.DHTM.halts_halts'.
    rewrite CTL_RNGS_mod.TM.halts_halts' in H1.
    eapply BlockTMFromDHTM.inv_map_nonhalt.
    2: apply H1.
    lia.
  - apply DHTMFromTM.map_nonhalt.
    pose proof (DHTMFromTM.DHTM.DH_cconfig_steps_spec tm DHTMFromTM.DHTM.cc0 simT) as H0.
    destruct (DHTMFromTM.DHTM.DH_cconfig_steps tm DHTMFromTM.DHTM.cc0 simT); try congruence.
    rewrite <-DHTMFromTM.DHTM.halts_halts'.
    eapply DHTMFromTM.DHTM.evstep_nonhalt; eauto. clear H0.
      epose proof (CTL_RNGS_mod_QSym.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
      rewrite DHTMFromTM.DHTM.halts_halts'.
      rewrite CTL_RNGS_mod_QSym.TM.halts_halts' in H1.
      eapply TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.inv_map_nonhalt.
      apply H1.
Qed.

End tm_ctx.

End CTLDecider.



